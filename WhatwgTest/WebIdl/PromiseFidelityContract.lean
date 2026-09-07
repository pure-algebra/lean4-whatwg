import Whatwg.WebIdl

/-!
Breaker-owned Q3b exact-signature and law battery for the fidelity addendum's
`Whatwg.WebIdl.Promise` surface.
Addendum: `test/contracts/promise-first-packet-q3b.contract.md`.
Base packet: `test/contracts/promise-first-packet.contract.md`.
Graph: `PROMISE-PG-FIRST`, `docs/PROMISE-DAG.md`, "Q3b addendum".
Attacks: `test/counterexamples/promise/ATTACKS.md`, WS-PROM-CE-029..031 and
WS-PROM-CE-034..036.

Byte spans are 0-based, ends exclusive, into
`vendor/whatwg-webidl-a652053f/index.bs`
(SHA-256 `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83`).
Row ids are those of `generated/webidl-census.tsv`; per R-P17 the frozen
`op.dfn-perform-steps-once-promise-is-settled` and `op.waiting-for-all-promise`
spellings stand. Citing a row id here anchors a declaration and moves no
coverage state; the Web IDL census stays all-`absent`.

Masks (DB-04) under §7's rule: a law whose statement observes the order in
which settlements happen or in which reaction jobs enter the queue is **M2**.
Argument order is neither, which is why this addendum relabels the base
packet's `waitForAll_failure` and `waitForAll_success` M1 and why only the two
traced failure laws below are M2.

Every ascription names an inventory row with its reuse mode or a gap id
(R-P12).

The builder must not change a statement in this file.
-/

set_option autoImplicit false

/-! ## F6 — `wait for all` short-circuits on the first rejection **to settle**

`op.wait-for-all`, 353239..354879, digest
`518fae182417ff76e800ed67df039a512d35b6af29ee11251b684172e703d930`. Read the
pinned steps: the rejection handler is `1. If |rejected| is true, abort these
steps. 2. Set |rejected| to true. 3. Perform |failureSteps| given |arg|.` It
runs when a promise rejects, mentions neither `fullfilledCount` nor `total`,
and therefore fires with the other promises still pending. The success steps
run only from the fulfilment handler, and only when `fullfilledCount` equals
`total`.

The base packet's `waitForAll` guards the whole answer on `allSettled`, so a
rejection while a sibling is pending answers `pending` (WS-PROM-CE-029), and it
picks the reported reason with `List.findSome?` over the **argument** list
(WS-PROM-CE-030). Neither is expressible over the general table alone, which
records what settled and not when; `Whatwg.Ecma262.Promise.SettlementTrace` is
the order DB-04's M2 needs, and it is a trace over the one table, never a
second one (WS-PROM-CE-031).

`waitForAll` keeps its signature and its two law statements: eleven Streams
call sites reach the predicate half, and `E-55`/`E-56` own it. `G-06`;
`E-55`, `E-56` (generalize). `op.waiting-for-all-promise` (354881..356058) and
its `[=Queue a microtask=]` step stay out, so no ordering claim is made about
the returned promise. -/

#check (@Whatwg.WebIdl.Promise.waitForAllTraced :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason →
    Whatwg.Ecma262.Promise.SettlementTrace value reason → List Nat →
    Whatwg.WebIdl.Promise.WaitResult value reason)

/-! Mask M1: with no rejection settled and not every argument fulfilled, the
answer is the live frontier (DB-07), because `fullfilledCount` has not reached
`total` and no failure step has run. -/
#check (@Whatwg.WebIdl.Promise.waitForAllTraced_pending :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (tr : Whatwg.Ecma262.Promise.SettlementTrace value reason) (ids : List Nat),
    Whatwg.Ecma262.Promise.SettlementTrace.firstRejection tr ids = none →
    ¬ Whatwg.WebIdl.Promise.AllSettled t ids →
      Whatwg.WebIdl.Promise.waitForAllTraced t tr ids =
        Whatwg.WebIdl.Promise.WaitResult.pending)

/-! Mask M1: the fulfilment handler's `|result|[|promiseIndex|]` assignment
makes the result list argument-ordered, and the success steps run when the
count reaches the total. Argument order is not a settlement order, so this is
M1 under §7's rule. -/
#check (@Whatwg.WebIdl.Promise.waitForAllTraced_success :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (tr : Whatwg.Ecma262.Promise.SettlementTrace value reason) (ids : List Nat)
    (values : List value),
    Whatwg.Ecma262.Promise.SettlementTrace.firstRejection tr ids = none →
    ids.length = values.length →
    (∀ p ∈ ids.zip values, Whatwg.Ecma262.Promise.Table.get t p.1 =
        some (Whatwg.Ecma262.Promise.State.fulfilled p.2)) →
      Whatwg.WebIdl.Promise.waitForAllTraced t tr ids =
        Whatwg.WebIdl.Promise.WaitResult.success values)

/-! Mask M2: **the F6 law**. The statement quantifies over the settlement
trace, not the argument list: the reported reason is the one of the earliest
entry in settlement order that is a rejection of an argument identity. The
table does not appear in the hypotheses at all. -/
#check (@Whatwg.WebIdl.Promise.waitForAllTraced_failure :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (before after : Whatwg.Ecma262.Promise.SettlementTrace value reason)
    (id : Nat) (r : reason) (ids : List Nat),
    List.contains ids id = true →
    (∀ e ∈ before, List.contains ids e.1 = false ∨ ∃ v : value, e.2 = Except.ok v) →
      Whatwg.WebIdl.Promise.waitForAllTraced t
          (before ++ (id, Except.error r) :: after) ids =
        Whatwg.WebIdl.Promise.WaitResult.failure r)

/-! Mask M2: **the short-circuit**, which is what WS-PROM-CE-029 attacks. The
failure is reported even though a sibling argument promise is still pending, so
`AllSettled` is false and the base packet's `waitForAll` would answer
`pending`. The extra hypothesis is deliberately unused in the conclusion: that
is the content. -/
#check (@Whatwg.WebIdl.Promise.waitForAllTraced_failure_pending :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (before after : Whatwg.Ecma262.Promise.SettlementTrace value reason)
    (id other : Nat) (r : reason) (ids : List Nat),
    List.contains ids id = true →
    List.contains ids other = true →
    Whatwg.Ecma262.Promise.Table.get t other =
        some Whatwg.Ecma262.Promise.State.pending →
    (∀ e ∈ before, List.contains ids e.1 = false ∨ ∃ v : value, e.2 = Except.ok v) →
      Whatwg.WebIdl.Promise.waitForAllTraced t
          (before ++ (id, Except.error r) :: after) ids =
        Whatwg.WebIdl.Promise.WaitResult.failure r)

/-! Mask M1: where the two forms agree. With every argument fulfilled and no
rejection in the trace, the traced operation is the base packet's `waitForAll`,
so the eleven Streams call sites that reach the predicate half lose nothing. -/
#check (@Whatwg.WebIdl.Promise.waitForAll_traced_success_agree :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (tr : Whatwg.Ecma262.Promise.SettlementTrace value reason) (ids : List Nat),
    Whatwg.Ecma262.Promise.SettlementTrace.firstRejection tr ids = none →
    (∀ id : Nat, List.contains ids id = true →
      ∃ v : value, Whatwg.Ecma262.Promise.Table.get t id =
        some (Whatwg.Ecma262.Promise.State.fulfilled v)) →
      Whatwg.WebIdl.Promise.waitForAllTraced t tr ids =
        Whatwg.WebIdl.Promise.waitForAll t ids)

/-! ## Minor — "a new promise" returns a capability

`op.a-new-promise`, 347604..347946, digest
`a9c212f9448d6cfdaf262e33f33ed5104392aaec738b6e3ae22b285edc3751b3`. Step 2 is
`Return ? NewPromiseCapability(|constructor|)`: the operation's result is a
PromiseCapability Record, not a promise identity (WS-PROM-CE-034). `newPromise`
keeps its landed signature — eighteen `Whatwg/Streams/**` call sites use the
identity and `E-19` (generalize) is the row it serves — and this is the form
the pinned text returns. `G-03`. -/

#check (@Whatwg.WebIdl.Promise.newPromiseWithCapability :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.Table value reason → Nat →
    Whatwg.Ecma262.Promise.Table value reason × Whatwg.Ecma262.Promise.Capability)

/-! Mask M1. -/
#check (@Whatwg.WebIdl.Promise.newPromiseWithCapability_eq :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (functionSeed : Nat),
    Whatwg.WebIdl.Promise.newPromiseWithCapability t functionSeed =
      Whatwg.Ecma262.Promise.newPromiseCapability t functionSeed)

/-! Mask M1: the landed identity is exactly the capability's `[[Promise]]`, so
the base packet's `newPromise` is the capability form projected and not a
different operation. -/
#check (@Whatwg.WebIdl.Promise.newPromise_capability_promise :
  ∀ {value reason : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (functionSeed : Nat),
    (Whatwg.WebIdl.Promise.newPromise t).2 =
      (Whatwg.WebIdl.Promise.newPromiseWithCapability t functionSeed).2.promise)

/-! ## Minor — "resolve" and "reject" call the resolving functions

`op.resolve`, 349216..349783, digest
`071c11c45c5c1da04b86837e7911385b64880eaf3a013ff769676110af545cc3`, step 3:
`Perform ! Call(|p|.[[Resolve]], undefined, « |value| »)`. `op.reject`,
349785..350073, digest
`c2edaaba6c2c29a161365819f857be96eabcf9ee573580a4687e8eec72a900ea`, step 1 is
the same through `[[Reject]]`. Both therefore inherit the shared one-shot
marker of `op.createresolvingfunctions`, which a direct table settle does not
have (WS-PROM-CE-035). `resolve` and `reject` keep their landed signatures —
`E-20` (generalize) and 58 Streams invocations — and these two state the form
the pinned text uses, with the exact hypothesis under which the two agree.
`G-03`. -/

#check (@Whatwg.WebIdl.Promise.resolveThrough :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.ResolvingFunctions →
    Whatwg.Ecma262.Promise.Table value reason → value →
    Whatwg.Ecma262.Promise.ResolvingFunctions ×
      Whatwg.Ecma262.Promise.Table value reason)

#check (@Whatwg.WebIdl.Promise.rejectThrough :
  ∀ {value reason : Type}, Whatwg.Ecma262.Promise.ResolvingFunctions →
    Whatwg.Ecma262.Promise.Table value reason → reason →
    Whatwg.Ecma262.Promise.ResolvingFunctions ×
      Whatwg.Ecma262.Promise.Table value reason)

/-! Mask M1. -/
#check (@Whatwg.WebIdl.Promise.resolveThrough_eq :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (v : value),
    Whatwg.WebIdl.Promise.resolveThrough f t v =
      Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve f t v)

/-! Mask M1. -/
#check (@Whatwg.WebIdl.Promise.rejectThrough_eq :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason),
    Whatwg.WebIdl.Promise.rejectThrough f t r =
      Whatwg.Ecma262.Promise.ResolvingFunctions.callReject f t r)

/-! Mask M1: the exact hypothesis under which the landed direct form is the
pinned one — the resolving functions have not fired yet. Without it the two
differ, which is the whole of WS-PROM-CE-035. -/
#check (@Whatwg.WebIdl.Promise.resolveThrough_resolve :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (v : value),
    f.alreadyResolved = false →
      (Whatwg.WebIdl.Promise.resolveThrough f t v).2 =
        Whatwg.WebIdl.Promise.resolve t f.promise v)

/-! Mask M1. -/
#check (@Whatwg.WebIdl.Promise.rejectThrough_reject :
  ∀ {value reason : Type} (f : Whatwg.Ecma262.Promise.ResolvingFunctions)
    (t : Whatwg.Ecma262.Promise.Table value reason) (r : reason),
    f.alreadyResolved = false →
      (Whatwg.WebIdl.Promise.rejectThrough f t r).2 =
        Whatwg.WebIdl.Promise.reject t f.promise r)

/-! ## F1 and F2 at the Web IDL layer

`op.dfn-perform-steps-once-promise-is-settled`, 350075..352408, digest
`dd0e08ae5b8739280837b31e10f2ace6f1a7f9b20034124d7c748d450aaab383`. Step 7 is
`Perform PerformPromiseThen(|promise|.[[Promise]], |onFulfilled|, |onRejected|,
|newCapability|)`, so Web IDL `react` **is** `PerformPromiseThen` at this
surface and inherits both step 12 and the settled branches' "append nothing".
The base packet's `react` returned no table and so could not mark the promise
handled, and appended to both lists on the settled branches; both are repaired
by the amended `react` in `WhatwgTest/WebIdl/PromiseContract.lean`, and these
two laws state the inheritance directly.

Step 6's `newCapability` and step 8's `Return |newCapability|` stay out: the
derived promise is `G-11`'s remainder, as the base packet already records, so
`react` still takes no capability argument. `E-31`, `E-37` (generalize). -/

/-! Mask M1: `react` is `PerformPromiseThen` with the capability forgotten. -/
#check (@Whatwg.WebIdl.Promise.react_performPromiseThen :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body),
    Whatwg.WebIdl.Promise.react t rs q promise onFulfilled onRejected =
      (Whatwg.Ecma262.Promise.performPromiseThen t rs q promise onFulfilled onRejected
        none).map (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1)))

/-! Mask M1: step 12 through step 7. Every branch of `react` that returns at
all leaves the promise handled, the pending branch included. -/
#check (@Whatwg.WebIdl.Promise.react_handled :
  ∀ {value reason body : Type} (t : Whatwg.Ecma262.Promise.Table value reason)
    (rs : Whatwg.Ecma262.Promise.Reactions body)
    (q : Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body)
    (res : Whatwg.Ecma262.Promise.Table value reason ×
      Whatwg.Ecma262.Promise.Reactions body ×
      Whatwg.Ecma262.Jobs.Queue (Whatwg.Ecma262.Jobs.ReactionJob (Except reason value)) ×
      Option (Whatwg.Ecma262.Promise.Reaction body)),
    Whatwg.WebIdl.Promise.react t rs q promise onFulfilled onRejected = some res →
      (Whatwg.Ecma262.Promise.Table.getCell res.1 promise).map
        Whatwg.Ecma262.Promise.Cell.handled = some true)
