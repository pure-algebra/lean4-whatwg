import assert from 'node:assert/strict';
import { ReadableStream } from 'node:stream/web';

// Finite host observations of the named sequences below. These do not run a Lean model,
// replay WPT, or establish a simulation theorem. The pinned specification owns the claims.
const authority = {
  streams: 'b9ba9f49d95b4280be0dc2372377a006c3a91c18',
  referenceImplementation: {
    tree: 'vendor/whatwg-streams-b9ba9f49/reference-implementation',
    commit: 'b9ba9f49d95b4280be0dc2372377a006c3a91c18',
    executed: false,
  },
  wpt: { commit: '480fdfcd85d043c23875665f464c35c0043dff52', executed: false },
};

async function pullErrorsBeforeQueuedReadSettles() {
  const reason = {};
  const calls = [];
  const settlements = [];
  const stream = new ReadableStream({
    start(controller) { controller.enqueue('a'); },
    pull(controller) {
      calls.push('pull');
      controller.error(reason);
    },
  }, { highWaterMark: 1 });
  const reader = stream.getReader();
  const closed = reader.closed.then(
    () => assert.fail('closed must reject'),
    error => {
      assert.equal(error, reason);
      settlements.push('closed:rejected');
    },
  );

  // Allow the successful start reaction to set started=true. The queued chunk fills HWM,
  // so this checkpoint cannot invoke pull before the consumer removes it.
  await Promise.resolve();
  assert.deepEqual(calls, []);
  calls.push('before-read');
  const result = reader.read();
  calls.push('after-read');
  assert.deepEqual(calls, ['before-read', 'pull', 'after-read']);
  const read = result.then(value => {
    assert.deepEqual(value, { value: 'a', done: false });
    settlements.push('read:chunk:a');
  });
  await Promise.all([closed, read]);
  assert.deepEqual(settlements, ['closed:rejected', 'read:chunk:a']);
  const laterRead = await reader.read().then(
    () => assert.fail('a subsequent read must reject'),
    error => error,
  );
  assert.equal(laterRead, reason);
  return {
    counterexample: 'WS-READ-CE-013',
    name: 'synchronous-pull-error-before-queued-read',
    tape: [
      'start enqueues a at HWM 1; start fulfills',
      'consumer reads; synchronous pull calls controller.error(reason); pull returns undefined',
      'consumer reads again after the registered promise reactions run',
    ],
    observed: { calls, settlements, laterReadRejectsWithSameReason: true },
    mask: 'finite settlement-order component of M2 and terminal-error component of M1',
    assumption: 'one default reader; native promises; the stated reaction-registration order',
  };
}

async function nestedInvalidSizesAllocateDistinctErrors() {
  let controller;
  let innerError;
  let outerError;
  const stream = new ReadableStream({ start(value) { controller = value; } }, {
    highWaterMark: 0,
    size(chunk) {
      if (chunk === 'outer') {
        try { controller.enqueue('inner'); } catch (error) { innerError = error; }
      }
      return Infinity;
    },
  });
  const reader = stream.getReader();
  const storedReason = reader.closed.then(
    () => assert.fail('closed must reject'),
    error => error,
  );
  try { controller.enqueue('outer'); } catch (error) { outerError = error; }
  assert.ok(innerError instanceof RangeError);
  assert.ok(outerError instanceof RangeError);
  assert.notEqual(innerError, outerError);
  assert.equal(await storedReason, innerError);
  return {
    counterexample: 'WS-READ-CE-016',
    name: 'nested-invalid-size-errors-have-distinct-identities',
    tape: [
      'construct at HWM 0 and acquire one default reader',
      'enqueue outer; its size enqueues inner; inner size returns Infinity',
      'outer size catches the inner RangeError, then returns Infinity',
    ],
    observed: { distinctRangeErrors: true, storedReasonIsInner: true, thrownReasonIsOuter: true },
    mask: 'M1 terminal reason identity, with the two synchronous thrown values as discriminators',
    assumption: 'same realm; ordinary RangeError identity; no asynchronous source callbacks',
  };
}

async function pullEnqueuesBeforeReadReturns() {
  let controller;
  let pulls = 0;
  const stream = new ReadableStream({
    start(value) { controller = value; controller.enqueue('a'); },
    pull(value) {
      pulls += 1;
      value.enqueue('b');
      return new Promise(() => {});
    },
  }, { highWaterMark: 1 });
  const reader = stream.getReader();
  await Promise.resolve();
  const first = reader.read();
  // This synchronous query occurs after pull enqueues b but before any promise reaction.
  const desiredSizeAtReturn = controller.desiredSize;
  assert.equal(desiredSizeAtReturn, 0);
  const second = reader.read();
  assert.deepEqual(await Promise.all([first, second]), [
    { value: 'a', done: false }, { value: 'b', done: false },
  ]);
  assert.equal(pulls, 1);
  return {
    counterexample: 'WS-READ-CE-014',
    name: 'synchronous-pull-enqueue-before-read-return',
    tape: [
      'start enqueues a at HWM 1; start fulfills',
      'consumer reads; synchronous pull enqueues b and returns a pending promise',
      'consumer queries desiredSize immediately, then reads again',
    ],
    observed: { desiredSizeAtReturn, chunks: ['a', 'b'], pulls },
    mask: 'M1 chunks and the desiredSize-read component of M2',
    assumption: 'one default reader; the pull promise remains unanswered, a live frontier',
  };
}

async function nestedReadSettlesBeforeOuterRead() {
  let reader;
  let inner;
  const order = [];
  const stream = new ReadableStream({
    start(controller) { controller.enqueue('a'); },
    pull(controller) {
      inner = reader.read().then(value => { order.push(1); return value; });
      controller.enqueue('b');
      return new Promise(() => {});
    },
  }, { highWaterMark: 1 });
  reader = stream.getReader();
  await Promise.resolve();
  const outer = reader.read().then(value => { order.push(0); return value; });
  assert.ok(inner instanceof Promise);
  assert.deepEqual(await Promise.all([outer, inner]), [
    { value: 'a', done: false }, { value: 'b', done: false },
  ]);
  assert.deepEqual(order, [1, 0]);
  return {
    counterexample: 'WS-READ-CE-015',
    name: 'nested-read-settles-before-outer-queued-read',
    tape: [
      'start enqueues a at HWM 1; start fulfills',
      'consumer reads; synchronous pull reads again, enqueues b, and returns a pending promise',
    ],
    observed: { readReactionOrder: order, outerChunk: 'a', innerChunk: 'b' },
    mask: 'finite read-settlement-order component of M2',
    assumption: 'native promises and stated reaction registration; the pull remains unanswered',
  };
}

const observations = [
  await pullErrorsBeforeQueuedReadSettles(),
  await pullEnqueuesBeforeReadReturns(),
  await nestedReadSettlesBeforeOuterRead(),
  await nestedInvalidSizesAllocateDistinctErrors(),
];
console.log(JSON.stringify({
  evidence: 'finite host observations only',
  authority,
  profile: { runtime: 'Node node:stream/web', version: process.version,
    platform: process.platform, architecture: process.arch },
  command: 'node harness/readable/reentrancy.mjs',
  observations,
  result: 'PASS',
}, null, 2));
