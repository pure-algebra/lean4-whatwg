import assert from 'node:assert/strict';
import { WritableStream } from 'node:stream/web';

// Finite observations of this Node host. The pinned specification owns the semantics.
// No Lean execution, WPT replay, reference implementation, or simulation is performed.
const authority = {
  streams: 'b9ba9f49d95b4280be0dc2372377a006c3a91c18',
  referenceImplementation: {
    tree: 'vendor/whatwg-streams-b9ba9f49/reference-implementation',
    commit: 'b9ba9f49d95b4280be0dc2372377a006c3a91c18',
    executed: false,
  },
  wpt: { commit: '480fdfcd85d043c23875665f464c35c0043dff52', executed: false },
};

function deferred() {
  let resolve;
  let reject;
  const promise = new Promise((yes, no) => { resolve = yes; reject = no; });
  return { promise, resolve, reject };
}

async function readyIdentityAndClose() {
  const sinkWrite = deferred();
  const calls = [];
  const writer = new WritableStream({
    write(chunk) { calls.push(`write:${chunk}`); return sinkWrite.promise; },
    close() { calls.push('close'); },
  }, { highWaterMark: 1 }).getWriter();
  const oldReady = writer.ready;
  await oldReady;
  const write = writer.write('a');
  const pressuredReady = writer.ready;
  assert.notEqual(pressuredReady, oldReady);
  assert.equal(writer.desiredSize, 0);
  let readyResolved = false;
  const watchedReady = pressuredReady.then(() => { readyResolved = true; });
  await Promise.resolve();
  assert.equal(readyResolved, false);
  assert.deepEqual(calls, ['write:a']);

  const close = writer.close();
  assert.equal(writer.ready, pressuredReady);
  await watchedReady;
  assert.equal(writer.desiredSize, 0);
  assert.deepEqual(calls, ['write:a']);
  sinkWrite.resolve();
  await Promise.all([write, close, writer.closed]);
  assert.deepEqual(calls, ['write:a', 'close']);
  return {
    counterexamples: ['WS-WRITE-CE-004', 'WS-WRITE-CE-005'],
    name: 'ready-replacement-and-close-while-write-pending',
    tape: [
      'successful start at HWM 1; retain fulfilled ready reference',
      'write a; sink returns a pending promise; retain replacement ready reference',
      'close while write remains pending; query desiredSize after ready resolves',
      'fulfill sink write; allow sink close to fulfill',
    ],
    observed: {
      oldAndNewReadyDistinct: true,
      closeRetainsCurrentReady: true,
      readyResolvesBeforeSinkWrite: true,
      desiredSizeWhileWritePending: 0,
      calls,
    },
    scope: 'finite promise identity, ready outcome, desiredSize, and sink-invocation observations',
    assumption: 'one attached writer; default unit sizes; native promises; sink write held pending',
    limitation: 'backpressure is an internal slot; this host probe observes desiredSize and ready only',
  };
}

async function sizeClosesBeforeAdmission() {
  const calls = [];
  let writer;
  let close;
  const stream = new WritableStream({
    write(chunk) { calls.push(`write:${chunk}`); },
    close() { calls.push('close'); },
  }, {
    highWaterMark: 1,
    size(chunk) {
      calls.push(`size:${chunk}`);
      close = writer.close();
      return 1;
    },
  });
  writer = stream.getWriter();
  await writer.ready;
  const reason = await writer.write('outer').then(
    () => assert.fail('reentrant close must prevent outer write admission'),
    error => error,
  );
  assert.ok(reason instanceof TypeError);
  await Promise.all([close, writer.closed]);
  assert.deepEqual(calls, ['size:outer', 'close']);
  return {
    counterexamples: ['WS-WRITE-CE-001'],
    name: 'size-callback-closes-before-outer-write-admission',
    tape: [
      'successful start at HWM 1; attach writer',
      'write outer; size callback calls writer.close and returns 1',
      'observe the outer write rejection and sink close completion',
    ],
    observed: { outerWriteRejectsTypeError: true, sinkReceivesOuterChunk: false, calls },
    scope: 'finite API outcome and ordered size/sink invocation observations',
    assumption: 'one attached writer; synchronous size callback; native same-realm TypeError',
  };
}

async function abortRetainsEarlierReason() {
  const abortReason = {};
  const writeReason = {};
  const laterAbortReason = {};
  const sinkWrite = deferred();
  const calls = [];
  const reactions = [];
  let signal;
  const writer = new WritableStream({
    start(controller) {
      signal = controller.signal;
      signal.addEventListener('abort', () => { calls.push('signal'); });
    },
    write(chunk) { calls.push(`write:${chunk}`); return sinkWrite.promise; },
    abort(reason) { assert.equal(reason, abortReason); calls.push('sink:abort'); },
  }, { highWaterMark: 1 }).getWriter();
  const closed = writer.closed.then(
    () => assert.fail('closed must reject'),
    reason => { assert.equal(reason, abortReason); reactions.push('closed:rejected'); },
  );
  await writer.ready;
  const first = writer.write('a').then(
    () => assert.fail('the in-flight write must reject'),
    reason => { assert.equal(reason, writeReason); reactions.push('first:rejected'); },
  );
  const queued = writer.write('b').then(
    () => assert.fail('the queued write must reject'),
    reason => { assert.equal(reason, abortReason); reactions.push('queued:rejected'); },
  );
  const ready = writer.ready.then(
    () => assert.fail('ready must reject during erroring'),
    reason => { assert.equal(reason, abortReason); reactions.push('ready:rejected'); },
  );
  const abort = writer.abort(abortReason);
  const repeated = writer.abort(laterAbortReason);
  assert.equal(repeated, abort);
  assert.equal(signal.reason, abortReason);
  assert.deepEqual(calls, ['write:a', 'signal']);
  const aborted = abort.then(() => { reactions.push('abort:fulfilled'); });
  await ready;
  assert.deepEqual(calls, ['write:a', 'signal']);
  sinkWrite.reject(writeReason);
  await Promise.all([first, queued, aborted, closed]);
  assert.deepEqual(calls, ['write:a', 'signal', 'sink:abort']);
  assert.deepEqual(reactions, [
    'ready:rejected', 'first:rejected', 'queued:rejected', 'abort:fulfilled', 'closed:rejected',
  ]);
  return {
    counterexamples: ['WS-WRITE-CE-009', 'WS-WRITE-CE-010', 'WS-WRITE-CE-013'],
    name: 'abort-waits-for-inflight-write-and-retains-stored-reason',
    tape: [
      'successful start; write a returns pending sink promise; queue write b',
      'abort with first reason; abort again with distinct reason while write is in flight',
      'reject sink write with a third reason; sink abort returns undefined',
    ],
    observed: {
      repeatedAbortAliasesPendingPromise: true,
      signalRetainsFirstReason: true,
      inFlightWriteRetainsItsRejectionReason: true,
      queuedWriteAndClosedRetainAbortReason: true,
      calls,
      reactions,
    },
    scope: 'finite reason/promise identity, callback order, and native promise-reaction order',
    assumption: 'same-realm reasons; one writer; all observer reactions registered as in this fixture',
    limitation: 'reaction order is host evidence; no access to pendingAbort or algorithm internal slots',
  };
}

async function successfulCloseWinsErroring() {
  const reason = {};
  const sinkClose = deferred();
  const calls = [];
  const reactions = [];
  const writer = new WritableStream({
    start(controller) {
      controller.signal.addEventListener('abort', () => { calls.push('signal'); });
    },
    close() { calls.push('sink:close'); return sinkClose.promise; },
    abort() { assert.fail('successful in-flight close must bypass sink abort'); },
  }).getWriter();
  const oldReady = writer.ready;
  await oldReady;
  const closed = writer.closed.then(() => { reactions.push('closed:fulfilled'); });
  const close = writer.close().then(() => { reactions.push('close:fulfilled'); });
  assert.deepEqual(calls, ['sink:close']);
  const abort = writer.abort(reason).then(() => { reactions.push('abort:fulfilled'); });
  const rejectedReady = writer.ready;
  assert.notEqual(rejectedReady, oldReady);
  const ready = rejectedReady.then(
    () => assert.fail('the ready replacement must reject'),
    error => { assert.equal(error, reason); reactions.push('ready:rejected'); },
  );
  await ready;
  assert.deepEqual(calls, ['sink:close', 'signal']);
  assert.deepEqual(reactions, ['ready:rejected']);
  sinkClose.resolve();
  await Promise.all([close, abort, closed]);
  assert.equal(writer.ready, rejectedReady);
  assert.deepEqual(reactions, [
    'ready:rejected', 'close:fulfilled', 'abort:fulfilled', 'closed:fulfilled',
  ]);
  return {
    counterexamples: ['WS-WRITE-CE-011'],
    name: 'successful-inflight-close-wins-erroring-without-repairing-ready',
    tape: [
      'successful start; retain fulfilled ready reference; close returns pending sink promise',
      'abort while close is in flight; retain and observe the rejected ready replacement',
      'fulfill sink close; observe close, abort, and closed fulfillment',
    ],
    observed: { sinkAbortCalled: false, rejectedReadyIdentityRetained: true, calls, reactions },
    scope: 'finite promise identity, callback order, and native promise-reaction order',
    assumption: 'one attached writer; close promise held pending; fixture reaction registration order',
  };
}

const observations = [];
for (const probe of [
  readyIdentityAndClose, sizeClosesBeforeAdmission,
  abortRetainsEarlierReason, successfulCloseWinsErroring,
]) {
  observations.push(await probe());
}
console.log(JSON.stringify({
  evidence: 'finite host observations only',
  authority,
  profile: {
    runtime: 'Node node:stream/web', version: process.version,
    platform: process.platform, architecture: process.arch,
  },
  command: 'node harness/writable/reentrancy.mjs',
  observationBoundary: 'API/callback/reaction observations relevant to P5a; DB-04 embeddings remain open',
  observations,
  result: 'PASS',
}, null, 2));
