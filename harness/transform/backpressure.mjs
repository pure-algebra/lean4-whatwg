import assert from 'node:assert/strict';
import { setImmediate } from 'node:timers/promises';
import { TransformStream } from 'node:stream/web';

// Finite observations of this Node profile. The pinned text owns semantics.
// No Lean execution, WPT replay, reference implementation, or simulation runs here.
const authority = {
  streams: 'b9ba9f49d95b4280be0dc2372377a006c3a91c18',
  referenceImplementation: {
    tree: 'vendor/whatwg-streams-b9ba9f49/reference-implementation',
    commit: 'b9ba9f49d95b4280be0dc2372377a006c3a91c18', executed: false,
  },
  wpt: { commit: '480fdfcd85d043c23875665f464c35c0043dff52', executed: false },
};

function deferred() {
  let resolve;
  const promise = new Promise(yes => { resolve = yes; });
  return { promise, resolve };
}

function observe(promise) {
  return promise.then(
    value => ({ status: 'fulfilled', value }),
    reason => ({ status: 'rejected', reason }),
  );
}

async function readUnblocksButDoesNotSettleWrite() {
  const completion = deferred();
  const entered = deferred();
  const calls = [];
  const stream = new TransformStream({
    transform(chunk, controller) {
      calls.push(`transform:${chunk}`);
      controller.enqueue('output');
      entered.resolve();
      return completion.promise;
    },
  });
  const writer = stream.writable.getWriter();
  const reader = stream.readable.getReader();
  await writer.ready;
  let writeSettled = false;
  const write = observe(writer.write('input')).then(result => {
    writeSettled = true;
    return result;
  });
  // One host event-loop turn is a finite scheduling checkpoint, not a timing theorem.
  await setImmediate();
  assert.deepEqual(calls, []);
  assert.equal(writeSettled, false);
  const read = reader.read();
  await entered.promise;
  assert.deepEqual(await read, { value: 'output', done: false });
  assert.equal(writeSettled, false);
  completion.resolve();
  assert.equal((await write).status, 'fulfilled');
  await writer.ready;
  assert.deepEqual(calls, ['transform:input']);
  return {
    name: 'read-unblocks-transform-but-write-awaits-transform-result',
    counterexamples: ['WS-TRANS-CE-003', 'WS-TRANS-CE-004', 'WS-TRANS-CE-009'],
    tape: ['write input at readable HWM 0', 'read', 'enqueue output in transform',
      'return pending transform promise', 'fulfill transform promise'],
    observed: { calls, output: ['output'], writePendingAfterRead: true },
    assumption: 'default unit sizes; attached reader/writer; native deferred transform promise',
  };
}

async function activeErrorStillAllowsTransformReturn() {
  const reason = {};
  const calls = [];
  const stream = new TransformStream({
    transform(_chunk, controller) {
      calls.push('transform:enter');
      controller.error(reason);
      calls.push('controller:error');
      calls.push('transform:return');
    },
  });
  const writer = stream.writable.getWriter();
  const reader = stream.readable.getReader();
  const closed = observe(writer.closed);
  const readableClosed = observe(reader.closed);
  await writer.ready;
  const write = observe(writer.write('input'));
  const ready = observe(writer.ready);
  const read = observe(reader.read());
  assert.equal((await write).status, 'fulfilled');
  for (const result of await Promise.all([ready, closed, readableClosed, read])) {
    assert.equal(result.status, 'rejected');
    assert.equal(result.reason, reason);
  }
  assert.deepEqual(calls, ['transform:enter', 'controller:error', 'transform:return']);
  return {
    name: 'active-transform-errors-components-and-still-returns-successfully',
    counterexamples: ['WS-TRANS-CE-013'],
    tape: ['write input at readable HWM 0', 'read', 'controller.error with retained object',
      'transform returns undefined'],
    observed: { calls, writeFulfilled: true, componentQueriesRetainExactReason: true },
    assumption: 'same-realm reason; synchronous transform body; observers attached as above',
    limitation: 'installed algorithm clearing and internal reaction attachment are not directly visible',
  };
}

async function positiveCapacityStartsWithoutRead() {
  const calls = [];
  const stream = new TransformStream({
    transform(chunk, controller) {
      calls.push(`transform:${chunk}`);
      controller.enqueue('queued');
    },
  }, { highWaterMark: 1 }, { highWaterMark: 1 });
  const writer = stream.writable.getWriter();
  const reader = stream.readable.getReader();
  await writer.ready;
  await writer.write('input');
  assert.deepEqual(calls, ['transform:input']);
  const output = await reader.read();
  assert.deepEqual(output, { value: 'queued', done: false });
  return {
    name: 'positive-readable-capacity-services-transform-before-first-read',
    counterexamples: ['WS-TRANS-CE-014'],
    tape: ['successful start with readable/writable HWM 1', 'write input',
      'enqueue queued; transform returns undefined', 'await write, then first read'],
    observed: { calls, writeFulfilledBeforeRead: true, output },
    assumption: 'default unit sizes; positive readable HWM; synchronous transform body',
  };
}

async function zeroAndMultipleOutputsSurviveTermination() {
  const calls = [];
  const stream = new TransformStream({
    transform(chunk, controller) {
      calls.push(`transform:${chunk}`);
      if (chunk === 'skip') return;
      controller.enqueue('first');
      controller.enqueue('second');
      controller.terminate();
    },
  }, { highWaterMark: 1 }, { highWaterMark: 1 });
  const writer = stream.writable.getWriter();
  const reader = stream.readable.getReader();
  const closed = observe(writer.closed);
  await writer.ready;
  await writer.write('skip');
  const write = observe(writer.write('emit'));
  const ready = observe(writer.ready);
  assert.equal((await write).status, 'fulfilled');
  const closedResult = await closed;
  const readyResult = await ready;
  assert.equal(closedResult.status, 'rejected');
  assert.equal(readyResult.status, 'rejected');
  assert.ok(closedResult.reason instanceof TypeError);
  assert.equal(readyResult.reason, closedResult.reason);
  const outputs = [await reader.read(), await reader.read(), await reader.read()];
  assert.deepEqual(outputs, [
    { value: 'first', done: false }, { value: 'second', done: false },
    { value: undefined, done: true },
  ]);
  await reader.closed;
  assert.deepEqual(calls, ['transform:skip', 'transform:emit']);
  return {
    name: 'zero-and-multiple-outputs-retained-through-termination',
    counterexamples: ['WS-TRANS-CE-010', 'WS-TRANS-CE-011', 'WS-TRANS-CE-013'],
    tape: ['write skip with no output at readable HWM 1', 'write emit',
      'enqueue first; enqueue second; terminate; return undefined', 'read three times'],
    observed: { calls, outputs, writableQueriesShareTypeError: true, currentWriteFulfilled: true },
    assumption: 'count output profile; same-realm TypeError; queued output read after termination',
  };
}

async function withDeadline(probe) {
  let timer;
  const timeout = new Promise((_, reject) => {
    timer = setTimeout(() => reject(new Error(`Host probe timed out: ${probe.name}`)), 5000);
  });
  try { return await Promise.race([probe(), timeout]); }
  finally { clearTimeout(timer); }
}

const observations = [];
for (const probe of [readUnblocksButDoesNotSettleWrite, activeErrorStillAllowsTransformReturn,
  positiveCapacityStartsWithoutRead, zeroAndMultipleOutputsSurviveTermination]) {
  observations.push(await withDeadline(probe));
}
console.log(JSON.stringify({
  evidence: 'finite host observations only', authority,
  profile: { runtime: 'Node node:stream/web', version: process.version,
    platform: process.platform, architecture: process.arch },
  command: 'node harness/transform/backpressure.mjs',
  observationBoundary: 'API outcomes, object identity, delivered chunks, and callback order; '
    + 'no comparison to a Lean execution or global DB-04 M1/M2 mask',
  observations, result: 'PASS',
}, null, 2));
