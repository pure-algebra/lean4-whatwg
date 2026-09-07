/-
GENERATED FILE. Do not edit.

Written by `lake exe census --standard webidl --write` (`Gates.Census`) from the pinned
`vendor/whatwg-webidl-a652053f/index.bs` (SHA-256 `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83`), the census projection
`generated/webidl-census.tsv`, and the authored disposition inputs under `census/webidl/`.
Format version 1. `lake exe census --standard webidl` fails on any byte of drift.

This is an all-absent census scaffold, not a checked coverage numerator.
One entry per census row carries its id and joined disposition, with no
theorem witnesses. The census command checks projection drift; the Streams
numerator does not validate this module. `docs/SPEC-COVERAGE.md` owns the rules.
-/

import Gates

namespace WhatwgTest.Audit.WebIdl.SpecCoverageRows

open Gates.Census

/-- One entry per census row, sorted by kind then id, as the census is. -/
def rows : Array CoverageRow := #[
  ⟨"idl.dom-exception", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-abort-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-code", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-constructor", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-data-clone-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-domstring-size-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-hierarchy-request-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-index-size-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-inuse-attribute-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-invalid-access-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-invalid-character-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-invalid-modification-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-invalid-node-type-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-invalid-state-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-message", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-name", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-namespace-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-network-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-no-data-allowed-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-no-modification-allowed-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-not-found-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-not-supported-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-quota-exceeded-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-security-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-syntax-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-timeout-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-type-mismatch-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-url-mismatch-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-validation-err", .hostOnly, .absent, []⟩,
  ⟨"idl.domexception-wrong-document-err", .hostOnly, .absent, []⟩,
  ⟨"idl.quota-exceeded-error", .hostOnly, .absent, []⟩,
  ⟨"idl.quota-exceeded-error-options", .hostOnly, .absent, []⟩,
  ⟨"idl.quotaexceedederror-constructor", .hostOnly, .absent, []⟩,
  ⟨"idl.quotaexceedederror-quota", .hostOnly, .absent, []⟩,
  ⟨"idl.quotaexceedederror-requested", .hostOnly, .absent, []⟩,
  ⟨"idl.quotaexceedederroroptions-quota", .hostOnly, .absent, []⟩,
  ⟨"idl.quotaexceedederroroptions-requested", .hostOnly, .absent, []⟩,
  ⟨"op.a-new-promise", .owned, .absent, []⟩,
  ⟨"op.a-promise-rejected-with", .owned, .absent, []⟩,
  ⟨"op.a-promise-resolved-with", .owned, .absent, []⟩,
  ⟨"op.add-bookmark", .evidenceOnly, .absent, []⟩,
  ⟨"op.add-delay", .evidenceOnly, .absent, []⟩,
  ⟨"op.an-exception-was-thrown", .hostOnly, .absent, []⟩,
  ⟨"op.batch-request", .evidenceOnly, .absent, []⟩,
  ⟨"op.delay", .evidenceOnly, .absent, []⟩,
  ⟨"op.dfn-create-exception", .owned, .absent, []⟩,
  ⟨"op.dfn-error-names-table", .owned, .absent, []⟩,
  ⟨"op.dfn-exception", .owned, .absent, []⟩,
  ⟨"op.dfn-perform-steps-once-promise-is-settled", .owned, .absent, []⟩,
  ⟨"op.dfn-promise-type", .hostOnly, .absent, []⟩,
  ⟨"op.dfn-simple-exception", .owned, .absent, []⟩,
  ⟨"op.dfn-throw", .owned, .absent, []⟩,
  ⟨"op.dom-exception-message", .owned, .absent, []⟩,
  ⟨"op.dom-exception-name", .owned, .absent, []⟩,
  ⟨"op.environment-create", .evidenceOnly, .absent, []⟩,
  ⟨"op.environment-ready", .evidenceOnly, .absent, []⟩,
  ⟨"op.environment-ready-promise", .evidenceOnly, .absent, []⟩,
  ⟨"op.js-exception-objects", .hostOnly, .absent, []⟩,
  ⟨"op.js-to-promise", .hostOnly, .absent, []⟩,
  ⟨"op.mark-a-promise-as-handled", .owned, .absent, []⟩,
  ⟨"op.quota-exceeded-error-deserialization-steps", .hostOnly, .absent, []⟩,
  ⟨"op.quota-exceeded-error-quota", .hostOnly, .absent, []⟩,
  ⟨"op.quota-exceeded-error-requested", .hostOnly, .absent, []⟩,
  ⟨"op.quota-exceeded-error-serialization-steps", .hostOnly, .absent, []⟩,
  ⟨"op.quotaexceedederror-quota-exceeded-error-message-options", .hostOnly, .absent, []⟩,
  ⟨"op.reject", .owned, .absent, []⟩,
  ⟨"op.resolve", .owned, .absent, []⟩,
  ⟨"op.throw-an-exception", .owned, .absent, []⟩,
  ⟨"op.to-create-a-dom-exception", .owned, .absent, []⟩,
  ⟨"op.to-create-a-dom-exception-derived-interface", .owned, .absent, []⟩,
  ⟨"op.to-create-a-simple-exception", .owned, .absent, []⟩,
  ⟨"op.upon-fulfillment", .owned, .absent, []⟩,
  ⟨"op.upon-rejection", .owned, .absent, []⟩,
  ⟨"op.validated-delay", .evidenceOnly, .absent, []⟩,
  ⟨"op.wait-for-all", .owned, .absent, []⟩,
  ⟨"op.waiting-for-all-promise", .owned, .absent, []⟩,
  ⟨"rule.domexception-derived-attributes", .requirement, .absent, []⟩,
  ⟨"rule.domexception-derived-constructor-message", .requirement, .absent, []⟩,
  ⟨"rule.domexception-derived-constructor-name", .requirement, .absent, []⟩,
  ⟨"rule.domexception-derived-constructor-options", .requirement, .absent, []⟩,
  ⟨"rule.domexception-derived-identifier", .requirement, .absent, []⟩,
  ⟨"rule.domexception-derived-serializable", .requirement, .absent, []⟩,
  ⟨"rule.domexception-deserialization-steps", .owned, .absent, []⟩,
  ⟨"rule.domexception-serialization-steps", .owned, .absent, []⟩,
  ⟨"rule.promise-to-js", .hostOnly, .absent, []⟩,
  ⟨"type.aborterror", .owned, .absent, []⟩,
  ⟨"type.constrainterror", .owned, .absent, []⟩,
  ⟨"type.datacloneerror", .owned, .absent, []⟩,
  ⟨"type.dataerror", .owned, .absent, []⟩,
  ⟨"type.encodingerror", .owned, .absent, []⟩,
  ⟨"type.eval-error", .owned, .absent, []⟩,
  ⟨"type.hierarchyrequesterror", .owned, .absent, []⟩,
  ⟨"type.idl-dom-exception", .hostOnly, .absent, []⟩,
  ⟨"type.idl-promise", .hostOnly, .absent, []⟩,
  ⟨"type.indexsizeerror", .owned, .absent, []⟩,
  ⟨"type.inuseattributeerror", .owned, .absent, []⟩,
  ⟨"type.invalidaccesserror", .owned, .absent, []⟩,
  ⟨"type.invalidcharactererror", .owned, .absent, []⟩,
  ⟨"type.invalidmodificationerror", .owned, .absent, []⟩,
  ⟨"type.invalidnodetypeerror", .owned, .absent, []⟩,
  ⟨"type.invalidstateerror", .owned, .absent, []⟩,
  ⟨"type.namespaceerror", .owned, .absent, []⟩,
  ⟨"type.networkerror", .owned, .absent, []⟩,
  ⟨"type.nomodificationallowederror", .owned, .absent, []⟩,
  ⟨"type.notallowederror", .owned, .absent, []⟩,
  ⟨"type.notfounderror", .owned, .absent, []⟩,
  ⟨"type.notreadableerror", .owned, .absent, []⟩,
  ⟨"type.notsupportederror", .owned, .absent, []⟩,
  ⟨"type.operationerror", .owned, .absent, []⟩,
  ⟨"type.optouterror", .owned, .absent, []⟩,
  ⟨"type.range-error", .owned, .absent, []⟩,
  ⟨"type.readonlyerror", .owned, .absent, []⟩,
  ⟨"type.reference-error", .owned, .absent, []⟩,
  ⟨"type.securityerror", .owned, .absent, []⟩,
  ⟨"type.syntaxerror", .owned, .absent, []⟩,
  ⟨"type.timeouterror", .owned, .absent, []⟩,
  ⟨"type.transactioninactiveerror", .owned, .absent, []⟩,
  ⟨"type.type-error", .owned, .absent, []⟩,
  ⟨"type.typemismatcherror", .owned, .absent, []⟩,
  ⟨"type.unknownerror", .owned, .absent, []⟩,
  ⟨"type.uri-error", .owned, .absent, []⟩,
  ⟨"type.urlmismatcherror", .owned, .absent, []⟩,
  ⟨"type.versionerror", .owned, .absent, []⟩,
  ⟨"type.wrongdocumenterror", .owned, .absent, []⟩
]

/-- Total census rows. -/
def rowTotal : Nat := 124

/-- Rows inside the coverage denominator. -/
def denominator : Nat := 116

end WhatwgTest.Audit.WebIdl.SpecCoverageRows
