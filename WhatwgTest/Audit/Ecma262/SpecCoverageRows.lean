/-
GENERATED FILE. Do not edit.

Written by `lake exe census --standard ecma262 --write` (`Gates.Census`) from the pinned
`vendor/ecma262-0248456c/spec.html` (SHA-256 `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0`), the census projection
`generated/ecma262-census.tsv`, and the authored disposition inputs under `census/ecma262/`.
Format version 1. `lake exe census --standard ecma262` fails on any byte of drift.

This is an all-absent census scaffold, not a checked coverage numerator.
One entry per census row carries its id and joined disposition, with no
theorem witnesses. The census command checks projection drift; the Streams
numerator does not validate this module. `docs/SPEC-COVERAGE.md` owns the rules.
-/

import Gates

namespace WhatwgTest.Audit.Ecma262.SpecCoverageRows

open Gates.Census

/-- One entry per census row, sorted by kind then id, as the census is. -/
def rows : Array CoverageRow := #[
  ⟨"builtin.get-promise-%symbol.species%", .hostOnly, .absent, []⟩,
  ⟨"builtin.promise-executor", .owned, .absent, []⟩,
  ⟨"builtin.promise.all", .owned, .absent, []⟩,
  ⟨"builtin.promise.allsettled", .owned, .absent, []⟩,
  ⟨"builtin.promise.any", .owned, .absent, []⟩,
  ⟨"builtin.promise.prototype.catch", .owned, .absent, []⟩,
  ⟨"builtin.promise.prototype.finally", .owned, .absent, []⟩,
  ⟨"builtin.promise.prototype.then", .owned, .absent, []⟩,
  ⟨"builtin.promise.race", .owned, .absent, []⟩,
  ⟨"builtin.promise.reject", .owned, .absent, []⟩,
  ⟨"builtin.promise.resolve", .owned, .absent, []⟩,
  ⟨"builtin.promise.try", .owned, .absent, []⟩,
  ⟨"builtin.promise.withResolvers", .owned, .absent, []⟩,
  ⟨"clause.jobs", .requirement, .absent, []⟩,
  ⟨"clause.promise-abstract-operations", .evidenceOnly, .absent, []⟩,
  ⟨"clause.promise-constructor", .hostOnly, .absent, []⟩,
  ⟨"clause.promise-jobs", .evidenceOnly, .absent, []⟩,
  ⟨"clause.promise-objects", .owned, .absent, []⟩,
  ⟨"clause.properties-of-promise-instances", .owned, .absent, []⟩,
  ⟨"clause.properties-of-the-promise-constructor", .hostOnly, .absent, []⟩,
  ⟨"clause.properties-of-the-promise-prototype-object", .hostOnly, .absent, []⟩,
  ⟨"field.jobcallback-records.Callback", .owned, .absent, []⟩,
  ⟨"field.jobcallback-records.HostDefined", .foreignBoundary, .absent, []⟩,
  ⟨"field.promisecapability-records.Promise", .owned, .absent, []⟩,
  ⟨"field.promisecapability-records.Reject", .owned, .absent, []⟩,
  ⟨"field.promisecapability-records.Resolve", .owned, .absent, []⟩,
  ⟨"field.promisereaction-records.Capability", .owned, .absent, []⟩,
  ⟨"field.promisereaction-records.Handler", .owned, .absent, []⟩,
  ⟨"field.promisereaction-records.Type", .owned, .absent, []⟩,
  ⟨"hook.host-promise-rejection-tracker", .foreignBoundary, .absent, []⟩,
  ⟨"hook.hostcalljobcallback", .foreignBoundary, .absent, []⟩,
  ⟨"hook.hostenqueuegenericjob", .foreignBoundary, .absent, []⟩,
  ⟨"hook.hostenqueuepromisejob", .requirement, .absent, []⟩,
  ⟨"hook.hostenqueuetimeoutjob", .foreignBoundary, .absent, []⟩,
  ⟨"hook.hostmakejobcallback", .foreignBoundary, .absent, []⟩,
  ⟨"op.createresolvingfunctions", .owned, .absent, []⟩,
  ⟨"op.fulfillpromise", .owned, .absent, []⟩,
  ⟨"op.getpromiseresolve", .owned, .absent, []⟩,
  ⟨"op.ifabruptrejectpromise", .owned, .absent, []⟩,
  ⟨"op.ispromise", .owned, .absent, []⟩,
  ⟨"op.newpromisecapability", .owned, .absent, []⟩,
  ⟨"op.newpromisereactionjob", .owned, .absent, []⟩,
  ⟨"op.newpromiseresolvethenablejob", .owned, .absent, []⟩,
  ⟨"op.performpromiseall", .owned, .absent, []⟩,
  ⟨"op.performpromiseallsettled", .owned, .absent, []⟩,
  ⟨"op.performpromiseany", .owned, .absent, []⟩,
  ⟨"op.performpromiserace", .owned, .absent, []⟩,
  ⟨"op.performpromisethen", .owned, .absent, []⟩,
  ⟨"op.promise-resolve", .owned, .absent, []⟩,
  ⟨"op.rejectpromise", .owned, .absent, []⟩,
  ⟨"op.triggerpromisereactions", .owned, .absent, []⟩,
  ⟨"property.promise.prototype", .hostOnly, .absent, []⟩,
  ⟨"property.promise.prototype-%symbol.tostringtag%", .hostOnly, .absent, []⟩,
  ⟨"property.promise.prototype.constructor", .hostOnly, .absent, []⟩,
  ⟨"record.jobcallback-records", .foreignBoundary, .absent, []⟩,
  ⟨"record.promisecapability-records", .owned, .absent, []⟩,
  ⟨"record.promisereaction-records", .owned, .absent, []⟩,
  ⟨"requirement.hostcalljobcallback.1", .foreignBoundary, .absent, []⟩,
  ⟨"requirement.hostenqueuepromisejob.1", .foreignBoundary, .absent, []⟩,
  ⟨"requirement.hostenqueuepromisejob.2", .foreignBoundary, .absent, []⟩,
  ⟨"requirement.hostenqueuepromisejob.3", .requirement, .absent, []⟩,
  ⟨"requirement.hostmakejobcallback.1", .foreignBoundary, .absent, []⟩,
  ⟨"requirement.jobs.1", .requirement, .absent, []⟩,
  ⟨"requirement.jobs.2", .requirement, .absent, []⟩,
  ⟨"requirement.jobs.3", .requirement, .absent, []⟩,
  ⟨"requirement.jobs.4", .requirement, .absent, []⟩,
  ⟨"slot.PromiseFulfillReactions", .owned, .absent, []⟩,
  ⟨"slot.PromiseIsHandled", .owned, .absent, []⟩,
  ⟨"slot.PromiseRejectReactions", .owned, .absent, []⟩,
  ⟨"slot.PromiseResult", .owned, .absent, []⟩,
  ⟨"slot.PromiseState", .owned, .absent, []⟩,
  ⟨"term.%Promise%", .hostOnly, .absent, []⟩,
  ⟨"term.%Promise.prototype%", .hostOnly, .absent, []⟩,
  ⟨"term.Promise~20~prototype~20~object", .hostOnly, .absent, []⟩,
  ⟨"term.job", .owned, .absent, []⟩,
  ⟨"term.job-activescriptormodule", .foreignBoundary, .absent, []⟩,
  ⟨"term.job-preparedtoevaluatecode", .foreignBoundary, .absent, []⟩
]

/-- Total census rows. -/
def rowTotal : Nat := 77

/-- Rows inside the coverage denominator. -/
def denominator : Nat := 75

end WhatwgTest.Audit.Ecma262.SpecCoverageRows
