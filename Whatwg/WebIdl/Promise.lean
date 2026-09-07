/-!
# Web IDL promise operations

Reserved for the Promises section of the pinned Web IDL source: "a new
promise", "a promise resolved with", "a promise rejected with", "resolve",
"reject", "react" ("upon fulfillment" / "upon rejection"), "wait for all",
"get a promise to wait for all", and "mark as handled", each stated as an
operation over `Whatwg.Ecma262.Promise` state, plus the rule that a
rejected promise passed to an algorithm is a "handled" promise. These are
the verbs the Streams source uses on every promise it creates.
Declaration-free; the P8 plan owns the first packet.
-/
