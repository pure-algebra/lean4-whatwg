/-!
# Web IDL promise operations

Reserved for the Promises section of the pinned Web IDL source: "a new
promise", "a promise resolved with", "a promise rejected with", "resolve",
"reject", "react" ("upon fulfillment" / "upon rejection"), "wait for all",
"get a promise to wait for all", and "mark as handled", each stated as an
operation over `Whatwg.Ecma262.Promise` state. These are the verbs the
Streams source uses on every promise it creates; the survey at
`docs/research/2026-09-06-webidl-promise-census-survey.md` counts 197 direct
invocations, six operations carrying 168 of them.
Declaration-free; the P8 plan owns the first packet.
-/
