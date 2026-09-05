# Default-writable proof graph (`WRITABLE-PG-DEFAULT`, P5a)

Status: frozen base packet, 2026-09-05. Contract:
`test/contracts/writable-default.contract.md`.
Base: `f4394d81d59739dd1410c6cc16df17ee147d6e1f`.

This graph owns the writable representative's exact anchor map, declaration
dispositions, dependency relationships, and assurance obligations. It does
not own any coverage count. Every algorithm below is a byte-span digest in
the sealed Streams census at `b9ba9f49d95b4280be0dc2372377a006c3a91c18`.

## Anchor map

| Alias | Census row | Span SHA-256 |
| --- | --- | --- |
| WRITE | `op.writable-stream-default-writer-write` | `d2b5ad5bcd6b399fef2ab19fba5e9aa683811ed082adaff7232e68ef5e3179c4` |
| SIZE | `op.writable-stream-default-controller-get-chunk-size` | `20517642266cd527180b239f5ea6cc1d3b694a632bae05296560c25f945f1872` |
| ENQUEUE | `op.writable-stream-default-controller-write` | `8d61c07286fd9969ce15072dadfb9df0d9421859aff11314496889f48dd72a84` |
| ADVANCE | `op.writable-stream-default-controller-advance-queue-if-needed` | `ee221518afc480ddbd35c6903d9a74f22f8f4182cb7f85a1504b29283d761cbe` |
| PROCESSWRITE | `op.writable-stream-default-controller-process-write` | `ca9fedd0d674c0ea84b8719cde61fa478c49d330335375443a18e15de996983a` |
| WRITEOK | `op.writable-stream-finish-in-flight-write` | `0154f894cbb72a0ccee1674c0ca04aa63fc6d6dee2594bfc0910bfba5cb67880` |
| WRITEFAIL | `op.writable-stream-finish-in-flight-write-with-error` | `edc3bf78aca1d3402553d575ba8972f9c9b21516df289f46543bbc40899aab2f` |
| CLOSE | `op.writable-stream-close` | `8b3fdd00054b774c9ea7b27323ab3512aba0987cbf40655c84e1fade1f5c62a0` |
| CLOSEQUEUE | `op.writable-stream-default-controller-close` | `6427bbdc4ffed135600ae10a1c8f8c1ed8ff2a2650a45a4d0c5c10872073f5b2` |
| PROCESSCLOSE | `op.writable-stream-default-controller-process-close` | `cafce64ee7515ad08efc6a01586757bde820184218425f0b2bf3fa816b1e21da` |
| CLOSEOK | `op.writable-stream-finish-in-flight-close` | `d19813563f15d1fe54dac8f4967aaaec84dbd75b8a1c2023fe492e487346438b` |
| CLOSEFAIL | `op.writable-stream-finish-in-flight-close-with-error` | `e3730d36ad8942b05bfe2d6f40017a575de1ba415d361d08747aa3807ed5cc34` |
| CLEAR | `op.writable-stream-default-controller-clear-algorithms` | `8c780c865fb8fd736334bee304c328c01322d14398b6e9b1d0464235ebdd7eec` |
| BACKPRESSURE | `op.writable-stream-update-backpressure` | `9d09e57a740c4c8b1c915b1b5383d35098200d53568e283b575b901bec70c7bf` |
| GETBACKPRESSURE | `op.writable-stream-default-controller-get-backpressure` | `3aa6da340e2a0844f96fc8eb81ad0e544f9bcac77ae298493e31aef0450d185e` |
| DESIRED | `op.writable-stream-default-writer-get-desired-size` | `e827502b6cd7ae1e78546fa98bc53db08b163b57c7e562aa40bbfc9f8b98498b` |
| READYERROR | `op.writable-stream-default-writer-ensure-ready-promise-rejected` | `e625a58639596b71bef95711924fe5c05af0e40e2096a7bc73f05cf16bc84669` |
| STARTERROR | `op.writable-stream-start-erroring` | `601a3534cfe044f49e5c3f06da61766c84944e3e31b8e408b4da15a6cac9ecbf` |
| FINISHERROR | `op.writable-stream-finish-erroring` | `53c60feb8cec7f05dfe0f0761bc2f2901129ceeb13df11c46f5ebeeb02de9e4b` |
| REJECTCLOSED | `op.writable-stream-reject-close-and-closed-promise-if-needed` | `1c36d91545fad304f004d31d235ff4ed0f337f682616b8aeacbbceef0dbb6cc9` |
| ABORT | `op.writable-stream-abort` | `208ceae72726689b2938b5b18b10305e17d8d5ee266bf08c5e4e6c8618cf0e3c` |
| ABORTSTEPS | `op.ws-default-controller-private-abort` | `ce6b44d6dd440ae7f6a8031a59ebc67580787b600ff77ce19558aafc6d08d921` |
| PUBLICCLOSE | `op.default-writer-close` | `c2263ad1e85c38420ccec4f941982a41a1fec3e5af342b7291f3a208e6e4bea7` |
| READYGET | `op.default-writer-ready` | `ee600b58b306e99190c61a86d476695f12089f14236840585bc695e2623ff781` |
| CLOSEDGET | `op.default-writer-closed` | `6f23788e0e9e09ca93336485a90f53ef62a2060bf1a316ea84f2c7bb95af795e` |
| PUBLICERROR | `op.ws-default-controller-error` | `d5d8554ea182577e20cdbb44341be47b10d35e9df263a15a482fee35a174a15a` |
| ERROR | `op.writable-stream-default-controller-error` | `ff606d4d6b68e895ad737a607ffbe0a443069b9309db04fafc7c739f73ceaa04` |
| ERRORIF | `op.writable-stream-default-controller-error-if-needed` | `4a14be045a1e6167846226c949f4da7fbe575648313131203b6a87d037840464` |
| DEAL | `op.writable-stream-deal-with-rejection` | `f4e79aca966aea1b5050c0745ef02207366dca38906573436f971a4794f6d9ee` |
| INFLIGHT | `op.writable-stream-has-operation-marked-in-flight` | `81d632b43a6f0d5bb686e32fcae3fef4ba95f5ed573730eca5b77e955e4da5e9` |
| WRITERSETUP | `op.set-up-writable-stream-default-writer` | `f410933085d1714301b8a0d46a359dfff2474b26be198e2e0cb45e54f4df04a4` |
| CONTROLLERDESIRED | `op.writable-stream-default-controller-get-desired-size` | `90759ffad823ac35b9386fd314a19bb83d2b806f2fb439659a1885943e51d0ee` |
| CLOSEPENDING | `op.writable-stream-close-queued-or-in-flight` | `83b13a394919c3c786e1e364ea06db06c31f5346ca121aab418c078d281e600b` |
| ERRORSTEPS | `op.ws-default-controller-private-error` | `97a86bdfd5332054e0b0ef925566f7ad58680e44a169a19eecfbaa6270459984` |
| SINKSETUP | `op.set-up-writable-stream-default-controller-from-underlying-sink` | `73c1fc5422ff7623809f041483b4c8cf19d46589b6fd61c4a238724a54d98f64` |

## Declaration dispositions

Stable names are under `Whatwg.Streams.Writable` unless explicitly qualified.
Every row contributes to this graph; a generated declaration snapshot must
eventually expand its constructors/projections/theorems individually.

| Family | Role and duplicate prevention | Disposition / anchors |
| --- | --- | --- |
| `Size`, `sizes`, strategy/size answers | named views of P3 owners; no new numeric representation | `owned` exact arithmetic, foreign rounding; SIZE, ENQUEUE |
| `UnitPromise`, `SinkAnswer`, `SinkReturn` | named views of the shared passive shapes first frozen under Readable; exact view/round-trip receipts required | `foreignBoundary` objects, owned first-order outcomes; PROCESSWRITE, PROCESSCLOSE, ABORTSTEPS |
| `Status`, `QueueItem`, `CloseState`, `PendingAbort` | distinct writable slot/calculus roles; close-request XOR, canonical Queue and shared Exception identities | `owned`; WRITE, CLOSE, STARTERROR, FINISHERROR, ABORT |
| `Algorithms`, `SinkAlgorithm` | present default/foreign algorithms distinct from cleared slots; size reuses P3 SizeAlgorithm | `foreignBoundary` callbacks; SIZE, SINKSETUP, CLEAR |
| `OperationPhase`, `SinkKind`, `SinkOperation`, `SinkJob`, `Control` | first-order operation IDs, arguments, phase tags and suspended administrative continuations; no callback bodies or second global runtime | `owned` protocol state, `foreignBoundary` invocation/return; SIZE, PROCESSWRITE, PROCESSCLOSE, ABORT, ABORTSTEPS |
| `Decision` | canonical first-order external call/answer alphabet; tick labels remain internal, not tape choices | `owned` calls, `foreignBoundary` answers; WRITE, CLOSE, ABORT, PROCESSWRITE |
| `State`, promise/identity slot views | one post-start writer/controller projection; seeded cursors are views of a future shared supply | `owned`; all anchors; global freshness embedding open |
| operation laws | named algorithm stages are deterministic internal work; external decisions enter only at empty-stack or foreign-marker frontiers | `owned`; exact per-declaration map below |
| `Event`, `VisibleEvent`, `SinkObservation`, `OrderedObservation`, observation helpers and query transitions | named foreign sink-input and ordered candidate views with DB-04 M1/M2 embeddings open; ordered view carries sink result and consumer events | `owned`; DESIRED, BACKPRESSURE, WRITEOK, CLOSEOK, REJECTCLOSED |

## Ten assurance edges

| Edge | Status | Required evidence |
| --- | --- | --- |
| identity | required-open | exact constructors/signatures, sentinel separation, shared reason/size/promise view receipts |
| construction | required-open | initial state and seeded supply laws, close-request XOR, promise identity retention and reachable cross-flight disjointness |
| semantics | required-open | explicit synchronous size/sink/signal returns, later settlements, deterministic FIFO jobs and relational finite composition |
| laws | required-closed | all 109 frozen local equations and two composed lifecycle statements pass; see the P5a landing receipt; whole-P5 and global obligations remain on their separate open edges |
| representation | required-open | P3 queue/size/answer reuse, shared exceptions, promise view dependency, first-order call stack, full-stream projection |
| counterexamples | required-closed | seventeen retained attack IDs and their linked production repair laws pass for this local projection; see the landing receipt |
| bridges | required-open | full writer/global scheduler/shared supply and host-profile embeddings; no host equivalence asserted by P5a |
| targets | not-applicable | this packet has no lowering; P11 owns target obligations |
| trust | required-closed | all 111 named theorem receipts, exhaustive root audit, narrow/full builds, executable gates and independent source review pass; see the landing receipt |
| coverage | required-open | full clause map and test-side frozen numerator witnesses; packet claims no changed coverage state |

## Exact declaration ownership map

Stable names are relative to `Whatwg.Streams.Writable`. The P5 builder owns
the listed production modules after freeze; this breaker owns the signatures.
Each constructor, projection and derived instance inherits the exact role,
existing-type disposition and duplicate-prevention relationship of its parent
family above. Every listed law inherits the operation it constrains. All rows
contribute to `WRITABLE-PG-DEFAULT`; no row creates another canonical queue,
number, error carrier or global promise runtime. The passive constructor and
projection entries contribute to identity/representation; operations and laws
contribute to semantics/laws. The future generated snapshot must expand every
derived export and join it to exactly one parent record.

New `Writable/Step.lean` is permitted to avoid cyclic imports. Module splits
may respect dependency direction without changing stable names or root
reachability. Stream owns passive shapes and table primitives; Backpressure
uses those shapes; DefaultController stages algorithms; DefaultWriter admits
external calls and returns; Step owns the relational face. The Stream views
depend on shared passive P4 shapes currently placed in Readable/State.lean.
Moving those shared shapes later requires exact adapter receipts for both APIs.

| Stable name | Intended module | Exact owner anchor(s) | Role |
| --- | --- | --- | --- |
| `Size` | `Writable/Stream.lean` | SIZE | surface; family disposition inherited |
| `sizes` | `Writable/Stream.lean` | SIZE | surface; family disposition inherited |
| `UnitPromise` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkAnswer` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkReturn` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `Status` | `Writable/Stream.lean` | STARTERROR | surface; family disposition inherited |
| `QueueItem` | `Writable/Stream.lean` | ENQUEUE | surface; family disposition inherited |
| `OperationPhase` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkKind` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkOperation` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `CloseState` | `Writable/Stream.lean` | CLOSE | surface; family disposition inherited |
| `PendingAbort` | `Writable/Stream.lean` | ABORT | surface; family disposition inherited |
| `Algorithms` | `Writable/Stream.lean` | CLEAR | surface; family disposition inherited |
| `Control` | `Writable/Stream.lean` | ADVANCE | surface; family disposition inherited |
| `SinkJob` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `Event` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `VisibleEvent` | `Writable/Stream.lean` | DESIRED | surface; family disposition inherited |
| `State` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `Decision` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `SinkObservation` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `OrderedObservation` | `Writable/Stream.lean` | DESIRED | surface; family disposition inherited |
| `unitPromiseToShared` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `unitPromiseFromShared` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `sinkAnswerToShared` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `sinkAnswerFromShared` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `sinkReturnToShared` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `sinkReturnFromShared` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `Status.writable` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `Status.erroring` | `Writable/Stream.lean` | STARTERROR | surface; family disposition inherited |
| `Status.errored` | `Writable/Stream.lean` | FINISHERROR | surface; family disposition inherited |
| `Status.closed` | `Writable/Stream.lean` | CLOSEOK | surface; family disposition inherited |
| `QueueItem.chunk` | `Writable/Stream.lean` | ENQUEUE | surface; family disposition inherited |
| `QueueItem.close` | `Writable/Stream.lean` | CLOSEQUEUE | surface; family disposition inherited |
| `OperationPhase.invoking` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `OperationPhase.awaiting` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `OperationPhase.queued` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkKind.write` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkKind.close` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkKind.abort` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkOperation.write` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkOperation.close` | `Writable/Stream.lean` | PROCESSCLOSE | surface; family disposition inherited |
| `SinkOperation.abort` | `Writable/Stream.lean` | ABORTSTEPS | surface; family disposition inherited |
| `CloseState.none` | `Writable/Stream.lean` | CLOSE | surface; family disposition inherited |
| `CloseState.queued` | `Writable/Stream.lean` | CLOSE | surface; family disposition inherited |
| `CloseState.inFlight` | `Writable/Stream.lean` | PROCESSCLOSE | surface; family disposition inherited |
| `PendingAbort.requested` | `Writable/Stream.lean` | ABORT | surface; family disposition inherited |
| `PendingAbort.alreadyErroring` | `Writable/Stream.lean` | ABORT | surface; family disposition inherited |
| `Algorithms.mk` | `Writable/Stream.lean` | CLEAR | surface; family disposition inherited |
| `Algorithms.size` | `Writable/Stream.lean` | CLEAR | surface; family disposition inherited |
| `Algorithms.write` | `Writable/Stream.lean` | CLEAR | surface; family disposition inherited |
| `Algorithms.close` | `Writable/Stream.lean` | CLEAR | surface; family disposition inherited |
| `Algorithms.abort` | `Writable/Stream.lean` | CLEAR | surface; family disposition inherited |
| `SinkJob.mk` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkJob.answer` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `Control.getSize` | `Writable/Stream.lean` | SIZE | surface; family disposition inherited |
| `Control.awaitSize` | `Writable/Stream.lean` | SIZE | surface; family disposition inherited |
| `Control.afterSize` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `Control.enqueueWrite` | `Writable/Stream.lean` | ENQUEUE | surface; family disposition inherited |
| `Control.advance` | `Writable/Stream.lean` | ADVANCE | surface; family disposition inherited |
| `Control.beginClose` | `Writable/Stream.lean` | CLOSE | surface; family disposition inherited |
| `Control.beginAbort` | `Writable/Stream.lean` | ABORT | surface; family disposition inherited |
| `Control.awaitSignal` | `Writable/Stream.lean` | ABORT | surface; family disposition inherited |
| `Control.afterSignal` | `Writable/Stream.lean` | ABORT | surface; family disposition inherited |
| `Control.awaitSink` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `Control.startErroring` | `Writable/Stream.lean` | STARTERROR | surface; family disposition inherited |
| `Control.finishErroring` | `Writable/Stream.lean` | FINISHERROR | surface; family disposition inherited |
| `Control.errorIfNeeded` | `Writable/Stream.lean` | ERRORIF | surface; family disposition inherited |
| `Control.controllerError` | `Writable/Stream.lean` | PUBLICERROR; ERROR | surface; family disposition inherited |
| `Control.dealRejection` | `Writable/Stream.lean` | DEAL | surface; family disposition inherited |
| `Control.rejectCloseClosed` | `Writable/Stream.lean` | REJECTCLOSED | surface; family disposition inherited |
| `Control.returnPromise` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `Control.react` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `Event.sizeCalled` | `Writable/Stream.lean` | SIZE | surface; family disposition inherited |
| `Event.sinkCalled` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `Event.signalCalled` | `Writable/Stream.lean` | ABORT | surface; family disposition inherited |
| `Event.settled` | `Writable/Stream.lean` | WRITEOK | surface; family disposition inherited |
| `Event.returned` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `Event.readyRead` | `Writable/Stream.lean` | BACKPRESSURE | surface; family disposition inherited |
| `Event.closedRead` | `Writable/Stream.lean` | REJECTCLOSED | surface; family disposition inherited |
| `Event.desiredSizeRead` | `Writable/Stream.lean` | DESIRED | surface; family disposition inherited |
| `VisibleEvent.settled` | `Writable/Stream.lean` | WRITEOK | surface; family disposition inherited |
| `VisibleEvent.returned` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `VisibleEvent.readyRead` | `Writable/Stream.lean` | BACKPRESSURE | surface; family disposition inherited |
| `VisibleEvent.closedRead` | `Writable/Stream.lean` | REJECTCLOSED | surface; family disposition inherited |
| `VisibleEvent.desiredSizeRead` | `Writable/Stream.lean` | DESIRED | surface; family disposition inherited |
| `State.mk` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.status` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.queue` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.highWaterMark` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.backpressure` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.algorithms` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.readyPromise` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.closedPromise` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.promises` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.handled` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.writeRequests` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.closeState` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.inFlightWrite` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.abortInFlight` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.pendingAbort` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.signalArgument` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.nextCall` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.nextPromise` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.nextError` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.control` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.jobs` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `State.trace` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `Decision.write` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `Decision.close` | `Writable/Stream.lean` | CLOSE | surface; family disposition inherited |
| `Decision.abort` | `Writable/Stream.lean` | ABORT | surface; family disposition inherited |
| `Decision.controllerError` | `Writable/Stream.lean` | PUBLICERROR | surface; family disposition inherited |
| `Decision.queryReady` | `Writable/Stream.lean` | READYGET | surface; family disposition inherited |
| `Decision.queryClosed` | `Writable/Stream.lean` | CLOSEDGET | surface; family disposition inherited |
| `Decision.queryDesiredSize` | `Writable/Stream.lean` | DESIRED | surface; family disposition inherited |
| `Decision.returnSize` | `Writable/Stream.lean` | SIZE | surface; family disposition inherited |
| `Decision.returnSink` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `Decision.returnSignal` | `Writable/Stream.lean` | ABORT | surface; family disposition inherited |
| `Decision.answer` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `initial` | `Writable/Stream.lean` | WRITERSETUP | surface; family disposition inherited |
| `lookupPromise` | `Writable/Stream.lean` | WRITEOK | surface; family disposition inherited |
| `freshPromise` | `Writable/Stream.lean` | WRITE | surface; family disposition inherited |
| `settle` | `Writable/Stream.lean` | WRITEOK | surface; family disposition inherited |
| `markHandled` | `Writable/Stream.lean` | READYERROR | surface; family disposition inherited |
| `ensureReadyRejected` | `Writable/Backpressure.lean` | READYERROR | surface; family disposition inherited |
| `updateBackpressure` | `Writable/Backpressure.lean` | BACKPRESSURE | surface; family disposition inherited |
| `desiredSize` | `Writable/Backpressure.lean` | DESIRED | surface; family disposition inherited |
| `getBackpressure` | `Writable/Backpressure.lean` | GETBACKPRESSURE; CONTROLLERDESIRED | surface; family disposition inherited |
| `clearAlgorithms` | `Writable/DefaultController.lean` | CLEAR | surface; family disposition inherited |
| `closeQueuedOrInFlight` | `Writable/Backpressure.lean` | CLOSEPENDING | surface; family disposition inherited |
| `hasInFlight` | `Writable/Backpressure.lean` | INFLIGHT | surface; family disposition inherited |
| `externalFrontier` | `Writable/DefaultWriter.lean` | PROCESSWRITE | surface; family disposition inherited |
| `operationPhase` | `Writable/DefaultController.lean` | PROCESSWRITE | surface; family disposition inherited |
| `setOperationPhase` | `Writable/DefaultController.lean` | PROCESSWRITE | surface; family disposition inherited |
| `invokeSink` | `Writable/DefaultController.lean` | PROCESSWRITE | surface; family disposition inherited |
| `attachSink` | `Writable/DefaultController.lean` | PROCESSWRITE | surface; family disposition inherited |
| `acceptAnswer` | `Writable/DefaultController.lean` | PROCESSWRITE | surface; family disposition inherited |
| `decide` | `Writable/DefaultWriter.lean` | WRITE | surface; family disposition inherited |
| `tick` | `Writable/DefaultController.lean` | ADVANCE | surface; family disposition inherited |
| `Step` | `Writable/Step.lean` | ADVANCE | surface; family disposition inherited |
| `Reaches` | `Writable/Step.lean` | ADVANCE | surface; family disposition inherited |
| `sinkInput` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `visibleEvents` | `Writable/Stream.lean` | DESIRED | surface; family disposition inherited |
| `settlementTrace` | `Writable/Stream.lean` | WRITEOK | surface; family disposition inherited |
| `observeSink` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `observeOrdered` | `Writable/Stream.lean` | DESIRED | surface; family disposition inherited |
| `SinkObservation.mk` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkObservation.chunks` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkObservation.status` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `OrderedObservation.mk` | `Writable/Stream.lean` | DESIRED | surface; family disposition inherited |
| `OrderedObservation.sink` | `Writable/Stream.lean` | DESIRED | surface; family disposition inherited |
| `OrderedObservation.events` | `Writable/Stream.lean` | DESIRED | surface; family disposition inherited |
| `SinkJob.kind` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkJob.request` | `Writable/Stream.lean` | PROCESSWRITE | surface; family disposition inherited |
| `operationKind` | `Writable/DefaultController.lean` | PROCESSWRITE | surface; family disposition inherited |
| `operationRequest` | `Writable/DefaultController.lean` | PROCESSWRITE | surface; family disposition inherited |
| `SinkAlgorithm` | `Writable/Stream.lean` | SINKSETUP | surface; family disposition inherited |
| `SinkAlgorithm.fulfilled` | `Writable/Stream.lean` | SINKSETUP | surface; family disposition inherited |
| `SinkAlgorithm.foreign` | `Writable/Stream.lean` | SINKSETUP | surface; family disposition inherited |
| `sizeNonPositive` | `Writable/Stream.lean` | GETBACKPRESSURE | surface; family disposition inherited |
| `Control.returnUnit` | `Writable/Stream.lean` | PUBLICERROR | surface; family disposition inherited |
| `Event.controllerReturned` | `Writable/Stream.lean` | PUBLICERROR | surface; family disposition inherited |
| `VisibleEvent.controllerReturned` | `Writable/Stream.lean` | PUBLICERROR | surface; family disposition inherited |
| `size_eq` | `Writable/Stream.lean` | SIZE | quantified stage/view law |
| `sizes_eq` | `Writable/Stream.lean` | SIZE | quantified stage/view law |
| `unitPromise_eq` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `unitPromiseToShared_eq` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `unitPromiseFromShared_eq` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `unitPromise_roundtrip` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `sinkAnswer_eq` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `sinkAnswerToShared_eq` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `sinkAnswerFromShared_eq` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `sinkAnswer_roundtrip` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `sinkReturn_eq` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `sinkReturnToShared_eq` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `sinkReturnFromShared_eq` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `sinkReturn_roundtrip` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `initial_eq` | `Writable/Stream.lean` | WRITERSETUP | quantified stage/view law |
| `lookupPromise_eq` | `Writable/Stream.lean` | WRITEOK | quantified stage/view law |
| `freshPromise_pending` | `Writable/Stream.lean` | WRITE | quantified stage/view law |
| `freshPromise_fulfilled` | `Writable/Stream.lean` | WRITE | quantified stage/view law |
| `freshPromise_rejected` | `Writable/Stream.lean` | WRITE | quantified stage/view law |
| `settle_pending` | `Writable/Stream.lean` | WRITEOK | quantified stage/view law |
| `settle_other` | `Writable/Stream.lean` | WRITEOK | quantified stage/view law |
| `markHandled_eq` | `Writable/Stream.lean` | READYERROR | quantified stage/view law |
| `ensureReadyRejected_pending` | `Writable/Backpressure.lean` | READYERROR | quantified stage/view law |
| `ensureReadyRejected_other` | `Writable/Backpressure.lean` | READYERROR | quantified stage/view law |
| `updateBackpressure_same` | `Writable/Backpressure.lean` | BACKPRESSURE | quantified stage/view law |
| `updateBackpressure_true` | `Writable/Backpressure.lean` | BACKPRESSURE | quantified stage/view law |
| `updateBackpressure_false` | `Writable/Backpressure.lean` | BACKPRESSURE | quantified stage/view law |
| `desiredSize_eq` | `Writable/Backpressure.lean` | DESIRED | quantified stage/view law |
| `getBackpressure_eq` | `Writable/Backpressure.lean` | GETBACKPRESSURE; CONTROLLERDESIRED | quantified stage/view law |
| `clearAlgorithms_eq` | `Writable/DefaultController.lean` | CLEAR | quantified stage/view law |
| `closeQueuedOrInFlight_eq` | `Writable/Backpressure.lean` | CLOSEPENDING | quantified stage/view law |
| `hasInFlight_eq` | `Writable/Backpressure.lean` | INFLIGHT | quantified stage/view law |
| `externalFrontier_eq` | `Writable/DefaultWriter.lean` | PROCESSWRITE | quantified stage/view law |
| `operationKind_eq` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `operationRequest_eq` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `operationPhase_eq` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `setOperationPhase_eq` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `attachSink_eq` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `invokeSink_eq` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `acceptAnswer_waiting` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `acceptAnswer_other` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `sizeNonPositive_eq` | `Writable/Stream.lean` | GETBACKPRESSURE | quantified stage/view law |
| `decide_blocked` | `Writable/DefaultWriter.lean` | WRITE | quantified stage/view law |
| `decide_write` | `Writable/DefaultWriter.lean` | WRITE | quantified stage/view law |
| `decide_close` | `Writable/DefaultWriter.lean` | CLOSE | quantified stage/view law |
| `decide_abort` | `Writable/DefaultWriter.lean` | ABORT | quantified stage/view law |
| `decide_controllerError` | `Writable/DefaultWriter.lean` | PUBLICERROR | quantified stage/view law |
| `decide_queryReady` | `Writable/DefaultWriter.lean` | READYGET | quantified stage/view law |
| `decide_queryClosed` | `Writable/DefaultWriter.lean` | CLOSEDGET | quantified stage/view law |
| `decide_queryDesiredSize` | `Writable/DefaultWriter.lean` | DESIRED | quantified stage/view law |
| `decide_answer` | `Writable/DefaultWriter.lean` | PROCESSWRITE | quantified stage/view law |
| `returnSize_value` | `Writable/DefaultWriter.lean` | SIZE | quantified stage/view law |
| `returnSize_thrown` | `Writable/DefaultWriter.lean` | SIZE | quantified stage/view law |
| `returnSize_unmatched` | `Writable/DefaultWriter.lean` | SIZE | quantified stage/view law |
| `returnSink_invoking` | `Writable/DefaultWriter.lean` | PROCESSWRITE | quantified stage/view law |
| `returnSink_unmatched` | `Writable/DefaultWriter.lean` | PROCESSWRITE | quantified stage/view law |
| `returnSignal_eq` | `Writable/DefaultWriter.lean` | ABORT | quantified stage/view law |
| `returnSignal_unmatched` | `Writable/DefaultWriter.lean` | ABORT | quantified stage/view law |
| `tick_foreign_marker` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `tick_no_job` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `tick_job_fifo` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `tick_returnPromise` | `Writable/DefaultController.lean` | WRITE | quantified stage/view law |
| `tick_returnUnit` | `Writable/DefaultController.lean` | PUBLICERROR | quantified stage/view law |
| `tick_getSize` | `Writable/DefaultController.lean` | SIZE | quantified stage/view law |
| `tick_afterSize_errored` | `Writable/DefaultController.lean` | WRITE | quantified stage/view law |
| `tick_afterSize_closing` | `Writable/DefaultController.lean` | WRITE | quantified stage/view law |
| `tick_afterSize_erroring` | `Writable/DefaultController.lean` | WRITE | quantified stage/view law |
| `tick_afterSize_writable` | `Writable/DefaultController.lean` | WRITE | quantified stage/view law |
| `tick_enqueueWrite_error` | `Writable/DefaultController.lean` | ENQUEUE | quantified stage/view law |
| `tick_enqueueWrite_ok` | `Writable/DefaultController.lean` | ENQUEUE | quantified stage/view law |
| `tick_advance_busy` | `Writable/DefaultController.lean` | ADVANCE | quantified stage/view law |
| `tick_advance_erroring` | `Writable/DefaultController.lean` | ADVANCE | quantified stage/view law |
| `tick_advance_empty` | `Writable/DefaultController.lean` | ADVANCE | quantified stage/view law |
| `tick_advance_write` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `tick_advance_close` | `Writable/DefaultController.lean` | PROCESSCLOSE | quantified stage/view law |
| `tick_beginClose_rejected` | `Writable/DefaultController.lean` | PUBLICCLOSE; CLOSE | quantified stage/view law |
| `tick_beginClose_admitted` | `Writable/DefaultController.lean` | CLOSE | quantified stage/view law |
| `tick_beginAbort_terminal` | `Writable/DefaultController.lean` | ABORT | quantified stage/view law |
| `tick_afterSignal_terminal` | `Writable/DefaultController.lean` | ABORT | quantified stage/view law |
| `tick_beginAbort_signal` | `Writable/DefaultController.lean` | ABORT | quantified stage/view law |
| `tick_beginAbort_signaled` | `Writable/DefaultController.lean` | ABORT | quantified stage/view law |
| `tick_afterSignal_existing` | `Writable/DefaultController.lean` | ABORT | quantified stage/view law |
| `tick_afterSignal_writable` | `Writable/DefaultController.lean` | ABORT | quantified stage/view law |
| `tick_afterSignal_erroring` | `Writable/DefaultController.lean` | ABORT | quantified stage/view law |
| `tick_errorIfNeeded` | `Writable/DefaultController.lean` | ERRORIF | quantified stage/view law |
| `tick_controllerError` | `Writable/DefaultController.lean` | PUBLICERROR; ERROR | quantified stage/view law |
| `tick_startErroring` | `Writable/DefaultController.lean` | STARTERROR | quantified stage/view law |
| `tick_dealRejection` | `Writable/DefaultController.lean` | DEAL | quantified stage/view law |
| `tick_finishErroring` | `Writable/DefaultController.lean` | FINISHERROR; ERRORSTEPS; ABORTSTEPS | quantified stage/view law |
| `tick_finishErroring_inFlight` | `Writable/DefaultController.lean` | FINISHERROR; INFLIGHT | quantified stage/view law |
| `tick_rejectCloseClosed` | `Writable/DefaultController.lean` | REJECTCLOSED | quantified stage/view law |
| `tick_react_unmatched` | `Writable/DefaultController.lean` | PROCESSWRITE | quantified stage/view law |
| `tick_write_fulfilled` | `Writable/DefaultController.lean` | WRITEOK | quantified stage/view law |
| `tick_write_rejected` | `Writable/DefaultController.lean` | WRITEFAIL | quantified stage/view law |
| `tick_close_fulfilled` | `Writable/DefaultController.lean` | CLOSEOK | quantified stage/view law |
| `tick_close_rejected` | `Writable/DefaultController.lean` | CLOSEFAIL | quantified stage/view law |
| `tick_abort_settled` | `Writable/DefaultController.lean` | ABORTSTEPS | quantified stage/view law |
| `step_iff` | `Writable/Step.lean` | ADVANCE | quantified stage/view law |
| `reaches_nil` | `Writable/Step.lean` | ADVANCE | quantified stage/view law |
| `reaches_cons` | `Writable/Step.lean` | ADVANCE | quantified stage/view law |
| `reaches_append_iff` | `Writable/Step.lean` | ADVANCE | quantified stage/view law |
| `step_deterministic` | `Writable/Step.lean` | ADVANCE | quantified stage/view law |
| `sinkInput_eq` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `visibleEvents_eq` | `Writable/Stream.lean` | DESIRED | quantified stage/view law |
| `settlementTrace_eq` | `Writable/Stream.lean` | WRITEOK | quantified stage/view law |
| `observeSink_eq` | `Writable/Stream.lean` | PROCESSWRITE | quantified stage/view law |
| `observeOrdered_eq` | `Writable/Stream.lean` | DESIRED | quantified stage/view law |
| `observeOrdered_toSink` | `Writable/Stream.lean` | DESIRED | quantified stage/view law |

## Clause map and remaining breadth obligations

| Local packet surface | Required later obligation |
| --- | --- |
| Seeded, empty post-start state and fixed attached writer | full setup/start outcomes, writer acquisition/release/reacquisition and valid initial projection |
| Canonical Queue plus zero-size close sentinel and separate in-flight slots | reachable assertions: queue/request correspondence, sentinel position, write-vs-close disjointness; no such invariant is asserted for arbitrary raw State |
| Shared exception identities and retained promise cells | global cross-stream supply freshness and ECMAScript promise/handled-state embedding |
| LIFO internal control and foreign size/sink/signal markers | global synchronous call stack, callback profile and scheduler embedding; DOM signal reason normalization |
| FIFO sink reaction jobs and typed pending/settled returns | arbitrary external promise reactions and deterministic global job registration order |
| Foreign sink-input and ordered candidate observations | DB-04 M1/M2 mapping, all consumer delivery/settlement observations of the whole writable calculus |
| Write/close/erroring/abort equations in the representative | every omitted writable clause before whole-P5 admission or a census row becomes green |

The abort algorithm's detailed supplied-reason behavior is the owner here.
The UnderlyingSink.abort prose's new-TypeError sentence does not override the
explicit WritableStreamAbort/FinishErroring steps. Source conflict resolution
must not erase the supplied reason or be replaced by a host observation.

## Freeze ledger

The base packet has 162 interface ascriptions, 108 exact quantified stage/view
laws, 108 axiom-report names, and 16 independent finite fixtures. The
independent reviewer checked all source equations and retained fixtures,
confirmed all receipt names occur in the battery, and rehashed all 35 source
spans against the sealed bytes and census. No semantic blocker remained.
The reviewer did no Lean builds or host runs. The breaker ran the sequential
narrow commands and recorded intended-red/green results in the contract and
attack receipt. Later source edits changed comments/anchors only.

| Artifact | SHA-256 at base freeze |
| --- | --- |
| `WhatwgTest/Streams/Writable/DefaultContract.lean` | `3bf8e2312bd7034aeeae6ce8a6740c653cb7ba8275c4f42cdef0f3c487b08e40` |
| `WhatwgTest/Streams/Writable/DefaultLaws.lean` | `3515f15a9a6b2383adc9219bb8387e4d3a53c9fd743ae5bd057c4b0a88e9f683` |
| `WhatwgTest/Streams/Writable/DefaultAxiomReport.lean` | `7c341a151bec5321eef3f2eef32187693cfde019a8ac929126b46b1930226c3f` |
| `WhatwgTest/Streams/Counterexamples/Writable/Default.lean` | `0ae8323ee2d494bbd3e40d45c7fe14d8720d19787d977be6f9f0f39d0fb62581` |

The base commit excludes `COORDINATION.md`, root imports, known-red entries
and the host fixture, which the coordinator owns. Before builder admission,
the coordinator declares the three base red modules named in the contract.
The two requested composed lifecycle regressions will land as a separately
reviewed theorem-only addendum before those production theorems are built.
They remain obligations of this same graph. No whole-P5 or coverage claim is
made by freezing or implementing only the base packet.

## Composed addendum freeze ledger

The separate theorem-only addendum is described in the contract's composed
lifecycle section. Base commit `68fc922e4efde615fc9aecb2f3433afa99514a02`
and its 162/108 frozen files are unchanged.
Stable names in the following addendum table are relative to `Whatwg.Streams`.

| Stable name | Intended module | Role, ownership and source anchors | Assurance |
| --- | --- | --- | --- |
| `Writable.lifecycle_write_close` | `Writable/Step.lean` | quantified fixed-initial two-part Reaches derivation under the exact local ordered view; WRITE, BACKPRESSURE, CLOSE, PROCESSWRITE, PROCESSCLOSE, CLOSEOK | this graph's construction, semantics and laws edges |
| `Writable.lifecycle_abort_rejection` | `Writable/Step.lean` | quantified fixed-initial in-flight/queued/abort/rejection derivation with distinct reasons; WRITE, ABORT, STARTERROR, WRITEFAIL, FINISHERROR, ABORTSTEPS, REJECTCLOSED | this graph's construction, semantics and laws edges |

These are derived laws of the existing writable calculus, disposition
`owned`. They introduce no carrier, program interpreter or host runtime,
and no new specification pin. The existing 35-anchor map remains their
authority. Independent review checked the explicit operational sequences
and exact observations; the contract records the two intended-red commands.
The coordinator owns their two known-red declarations and integration.

| Artifact | SHA-256 at addendum freeze |
| --- | --- |
| `WhatwgTest/Streams/Writable/LifecycleContract.lean` | `8ad3e4ffe65ad20bc3a57d5224d75c1f0067f78e1c1a6b741f77515dda6f2e54` |
| `WhatwgTest/Streams/Writable/LifecycleAxiomReport.lean` | `a19447a2677a6d5eff873c6049b3f6c1e9004b04ac8915f08348bed88f220f8b` |

The addendum commit is the immutable identity of these two statements.
No required-open graph edge is closed merely by their freeze. Full initial
projection, reachable assertions, global promise/supply/scheduler embeddings
and the DB-04 mask mappings remain open even once the two proofs are built.

## Exact in-flight equation freeze ledger

This additive correction leaves every earlier frozen Lean file intact. It
adds one quantified exact slot equation and retains `WS-WRITE-CE-017` as
the independent precedence counterexample. The same graph remains the
assurance owner.

| Stable name, relative to Whatwg.Streams | Intended module | Role / disposition / anchor | Required edge |
| --- | --- | --- | --- |
| `Writable.hasInFlight_exact` | `Writable/Laws.lean`, semantic owner `Writable/Backpressure.lean` | derived exact slot equation, `owned`; INFLIGHT, span `81d632b43a6f0d5bb686e32fcae3fef4ba95f5ed573730eca5b77e955e4da5e9` | construction and laws; supports local sink-input/ordered views |

The old `hasInFlight_eq` is retained as its actual weaker coerced predicate;
the new equation is the required exact receipt for the algorithm's complete
Boolean result. There is no new type/disposition or replacement of the
correct production operation. The existing global reachability, scheduler,
shared-supply and DB-04 embedding obligations remain open.

Independent review read the pinned Lean notation/coercion definitions and
the pinned Streams INFLIGHT algorithm, and confirmed the parenthesized exact
ascription. The contract and attack document record the one-name intended-red
checks and both axiom-free witness receipts.

| Artifact | SHA-256 at exact-equation freeze |
| --- | --- |
| `WhatwgTest/Streams/Writable/InFlightExactContract.lean` | `1062abbd71f34f4efff5802c333cc1c9d00874822921845c128e639f77fd9ee6` |
| `WhatwgTest/Streams/Writable/InFlightExactAxiomReport.lean` | `b3d02246ec505cceef4c5406c5861eb80da7a201bffe73e92cd7331ea73bf4eb` |
| `WhatwgTest/Streams/Counterexamples/Writable/InFlightPrecedence.lean` | `3f51d0eafcf0e6220704a55f7398231b9899e1bfb108488b63448fd50f4011fd` |

The commit carrying this record is the addendum identity. Known-red entries,
production proof, root integration and gate receipts remain coordinator
work. Freezing the correction closes no required-open graph edge.

## Builder module allocation (coordinator, 2026-09-05)

The stable names and frozen statements above are unchanged. `Writable/Step.lean`
owns `Step`, `Reaches`, and its finite-derivation constructors `Reaches.nil` and
`Reaches.cons`; these are the graph's existing semantics family, disposition
`owned`, under ADVANCE. `Writable/Laws.lean` houses the 108 frozen stage/view
proofs, including finite composition, plus `hasInFlight_exact` from the additive
packet. `Writable/Lifecycle.lean` houses the two
frozen composed proofs. This file split changes no judgment or declaration name.
All modules must be reachable from the audited root before landing. No assurance
edge closes until its recorded checks and independent review pass.

The slot helpers `clearAlgorithms`, `closeQueuedOrInFlight`, and `hasInFlight`
are implemented in `Writable/Backpressure.lean`; `externalFrontier` is in
`Writable/DefaultController.lean`. Their stable names and semantic owners above
are unchanged. Settlement updates only the promise table and trace, so unrelated
state projections reduce directly; the frozen pending/other equations check
both branches. No private semantic helper or duplicate promise carrier is added.

## P5a landing receipt (coordinator, 2026-09-05)

Base: `5f7cebef3c533c20ee1cc65558847fc1c1db5f46`, following the frozen
base/lifecycle/exact packets integrated as `5669062`, `47a86da`, and
`5f7cebe`. The verified P4a prerequisite is
`5121268d3c148678bfbe501b245881631524f2e5`. This receipt accompanies the
implementation commit; the coordinator handoff records its exact head.

The production fence is
`Whatwg/Streams/Writable/{Stream,Backpressure,DefaultController,DefaultWriter,Step,Laws,Lifecycle}.lean`.
The stable public declarations are exactly the families recorded above,
with the module allocation in the coordinator appendix. The seven modules
implement one post-successful-start stream with a fixed attached writer,
typed size/sink/signal returns, later sink answers, staged synchronous
continuations, retained identity-indexed promise cells, and deterministic
FIFO reaction jobs. `Reaches` composes actual external decisions and
internal ticks; unanswered callbacks remain live frontiers.

The remaining changed files are `Whatwg/Streams.lean`, `WhatwgTest.lean`,
`test/fixtures/trust-gate/known-red.txt`, `harness/writable/reentrancy.mjs`,
the seventeen writable status/repair cells in `test/counterexamples/REGISTER.md`,
this graph, `PLAN.md`, and `COORDINATION.md`. Authored dependency records in
`SPEC-MANIFEST.md`, `docs/PROVENANCE.md`, `docs/WHATWG-PACKAGE-PLAN.md`, and
the effects version comment in `lakefile.toml` are reconciled to the
existing lockfile and local Git objects. No dependency revision changes.
All nine frozen interface/law/receipt/witness file hashes match their
freeze ledgers. No frozen statement or witness body, generated projection,
vendored byte, or `lake-manifest.json` is edited.

### Verification

All Lean commands used Lean 4.33.1 with `LEAN_NUM_THREADS=1`:

```text
lake --log-level=warning build WhatwgTest.Streams.Writable.DefaultContract WhatwgTest.Streams.Writable.DefaultLaws WhatwgTest.Streams.Writable.DefaultAxiomReport WhatwgTest.Streams.Writable.LifecycleContract WhatwgTest.Streams.Writable.LifecycleAxiomReport WhatwgTest.Streams.Writable.InFlightExactContract WhatwgTest.Streams.Writable.InFlightExactAxiomReport WhatwgTest.Streams.Counterexamples.Writable.Default WhatwgTest.Streams.Counterexamples.Writable.InFlightPrecedence
lake --log-level=warning build
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest/Streams/Writable/DefaultAxiomReport.lean
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest/Streams/Writable/LifecycleAxiomReport.lean
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest/Streams/Writable/InFlightExactAxiomReport.lean
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest.lean
.lake/build/bin/vendorseal.exe
.lake/build/bin/citations.exe
.lake/build/bin/tyxmlschema.exe
.lake/build/bin/census.exe
.lake/build/bin/census.exe --report
.lake/build/bin/census.exe --standard infra
node harness/writable/reentrancy.mjs
git diff --check
```

The narrow build passes 72 jobs, including all 162 interface ascriptions,
109 local law signatures, the two composed signatures, and the two retained
witness modules. The full build passes 275 jobs. The 111 theorem receipts
comprise 23 axiom-free proofs, 34 at `[propext]`, 52 at
`[propext, Quot.sound]`, and the two lifecycle proofs at
`[propext, Classical.choice, Quot.sound]`. All are within R-11; none reaches
a forbidden axiom. The exhaustive root audit checks 133 modules and 9324
declarations, including 1595 in the Gates tooling tree. All seven now-green
battery modules have been removed from the known-red set.

The vendor seal checks 206 files in five pinned trees. The citation gate,
TyXML projection/emission drift checks, and Streams/Infra census gates pass.
The coverage report at the base above with this implementation working tree
prints the following unchanged numerator; these local proofs add no census
witness by themselves:

```text
WHATWG Streams (b9ba9f49) coverage: denominator 410; owned-with-green 12/410;
green 12, partial 6, absent 392; census 450 rows, 40 excluded
partial: op.blqs-size op.byte-length-queuing-strategy-size-function op.count-queuing-strategy-size-function op.cqs-size op.is-non-negative-number slot.queue-total-size
```

The Node fixture passes four finite observations under `node:stream/web`,
Node `v22.23.2`, Windows x64: ready replacement and close while a write is
pending; synchronous size-close reentrancy; pending-write abort reason and
settlement ordering; and successful in-flight close during erroring. The
fixture names its authority pins, tapes, reaction-registration assumptions,
and observable limits. It executes neither WPT nor the pinned reference
implementation. It establishes no general host relation or DB-04 embedding.

### Independent review and residual obligations

The separate reviewer checked the frozen equations against their source
anchors, the canonical carrier reuse, return/answer/reaction staging,
promise identity retention, and the final implementation/proof bodies.
The lifecycle proofs construct actual `Reaches.nil`/`Reaches.cons`
derivations and discharge each actual `Step` with ordinary `simp`/`rfl`;
their endpoints are inferred from those derivations. They quantify chunks
and reasons but fix the initial projection and the two tape shapes. They
are composed local regressions, not arbitrary-run invariants or host traces.

The review also checked the additive `hasInFlight_exact` correction. The
earlier unparenthesized equation remains unchanged; CE-017 demonstrates why
it cannot by itself exclude a write-only predicate. The parenthesized
whole-result equation now has its own exact checked signature and receipt.
The other sixteen retained attacks close through their linked production
equations. Independent source review found no remaining P5a landing blocker.

Only laws, counterexamples, and trust close here. Identity remains open for
generated public-declaration snapshot joins. Construction remains open for
valid initial/full-state projection, queue/request and close-sentinel
invariants, in-flight disjointness on reachable states, and shared fresh
allocation. Semantics, representation, and bridges remain open for global
call-stack/job order, ECMAScript promises and reaction registration,
full-stream/host embeddings, and DB-04 M1/M2 relations. Coverage remains open
for the clause map and test-side numerator witnesses. P11 owns targets.
Setup/start and writer acquire/release/reacquire are later full-P5 work.

The next breadth representative is the independently frozen P6a packet
`03547f1feb938d65898c47b4061faeb3f4bd9edf`, built on the P4/P5 canonical
states and shared P5 promise table. Its integration and implementation do
not close any of these remaining global obligations.
