# Web IDL promise and exception sections: source survey for a census lane

Read-only survey pass, 2026-09-06. Nothing under `vendor/` was touched and no
Lean build was run. Every number below was recomputed from the sealed bytes in
this pass with PowerShell (`[IO.File]::ReadAllBytes`, Latin-1 decode so that
character index equals byte offset, `SHA256.ComputeHash` over extracted byte
ranges). Offsets are 0-based byte offsets into the pinned file; ends are
exclusive. No line numbers are cited anywhere.

## 0. Pins, method, and what this document is for

| Item | Value |
| --- | --- |
| Surveyed source | `vendor/whatwg-webidl-a652053f/index.bs` |
| Upstream | `whatwg/webidl` commit `a652053f1e74e4aaf647528deb174012ed6c909f`, "Review Draft Publication: March 2026" |
| Size | 695,845 bytes |
| SHA-256 | `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83` (recomputed this pass, matches `SPEC-MANIFEST.md` and `docs/PROVENANCE.md`) |
| Encoding | UTF-8 with non-ASCII content: 695,845 bytes decode to 694,983 characters, so a character-indexed scanner is off by 862 on this file. Every offset here is a byte offset. |
| Cross-referenced source | `vendor/whatwg-streams-b9ba9f49/index.bs`, 417,076 bytes, read-only |

This is a source survey, not a census, not a denominator, and not a coverage
claim. It exists so that a later extension of `Gates/Census.lean` and the
breaker contract over it can be specified against exact bytes rather than
against a reading.

The five sections in scope hold **54,343 bytes, 7.81 % of the file**.

## 1. The structure in scope

### 1.1 Headings

`Gates.Census.scanHeadings` admits `<h2>`, `<h3>` and `<h4>` that open a line
and carry an `id`. The file has 236 headings at levels 2–6 that open a line;
239 byte occurrences of `<h`. A section's content ends at the next heading of
the same or higher level. The three `<h2>` rows are the ancestors the
disposition walk reaches, not themselves in scope.

| id | level | title | offset | content end | length | SHA-256 of span |
| --- | --- | --- | --- | --- | --- | --- |
| `idl` | h2 | Interface definition language | 8378 | 283469 | 275091 | `1f3dc31cb672a6efb9e9c7af807ff2e89fdd9199071cf9037c418eae5c7177ba` |
| `idl-exceptions` | h3 | Exceptions | 193957 | 217551 | 23594 | `b8c34eecb372c4cc76c476b3d1806fdd523c33112fc05c86c11bd6f59676ac0d` |
| `idl-DOMException-error-names` | h4 | Base `{{DOMException}}` error names | 198581 | 211138 | 12557 | `2baf51f7fd3f509a0e1b8ad3a1bb6be1353045df11e67782f9eb32a619771478` |
| `idl-DOMException-derived-interfaces` | h4 | `{{DOMException}}` derived interfaces | 211138 | 213283 | 2145 | `bea024c7146f0d2044eff5f77b8ec8f5d619e595e9d836ef0127ca0ccfda7c13` |
| `idl-DOMException-derived-predefineds` | h4 | Predefined `{{DOMException}}` derived interfaces | 213283 | 217551 | 4268 | `bcf40e666435f4aeb3bba2546ebcb008c214e6d820bbb1566b9ad534365a1f6f` |
| `idl-promise` | h4 | Promise types — Promise&lt;\|T\|&gt; | 252146 | 252819 | 673 | `c0f7dcec8c01af9f09faaf23c6d9aa8cb4fce16e55f788cc54018c63175369c7` |
| `javascript-binding` | h2 | JavaScript binding | 283469 | 671837 | 388368 | `a8547a4c796aca4d64f50c71b821ec004396d333e6f7e6c812c30bb12a89700b` |
| `js-promise` | h4 | Promise types — Promise&lt;\|T\|&gt; | 346519 | 364590 | 18071 | `784465713cb51539e5dc012d985c3129b10d90b10d8f213e245dbdff0f81f996` |
| `js-promise-manipulation` | **h5** | Creating and manipulating Promises | 347497 | 356716 | 9219 | `ae739fc5a23e72c2cbc1fd8fc0545cb186452b8db633a5e1fe514b3414281abb` |
| `js-promise-examples` | **h5** | Examples | 356716 | 364590 | 7874 | `691d8bdefbb9363b25cc578e098fbfd7c26fd353cfc951490f147174675030d5` |
| `js-exceptions` | h3 | Exceptions | 663547 | 671837 | 8290 | `0219395d3a2e97187ce2e6dbc62b8b81bc0527ae2b2cf1ae678f3cfb42fefc53` |
| `js-DOMException-specialness` | h4 | `{{DOMException}}` custom bindings | 663610 | 664320 | 710 | `923178c810fcff090e9c7d11a8d668aaca92d393d486535500a65ee20efa6357` |
| `js-exception-objects` | h4 | Exception objects | 664320 | 664612 | 292 | `ef1143597f76f45d3127c900bb225642cae5d637376e7c523f791c407a5c87b9` |
| `js-creating-throwing-exceptions` | h4 | Creating and throwing exceptions | 664612 | 669093 | 4481 | `fcb3f587bf2a39d1cdc58ceea453d0a75550e7d6dc304bd72b76f239daa4a19c` |
| `js-handling-exceptions` | h4 | Handling exceptions | 669093 | 671837 | 2744 | `6a96769d1fa4a7af507679f208a776c5465a2af0e1a73f4a0c29ebdaeae27491` |
| `common` | h2 | Common definitions | 671837 | 677688 | 5851 | `b2b30cc833af2a8cc9f7152786d93e3422ee91bbda2be3eb7041a8abc0008cfa` |
| `idl-DOMException` | h3 | DOMException | 673398 | 677113 | 3715 | `55a0c66acdc2eab5dc8cba0ebb6fc982d029350c0f2bf80ed89bcb284e07e515` |

Three sections in scope have their own content before their first child. Those
lead spans are what a section-keyed disposition line actually governs for the
rows that sit in them:

| Section | lead span | length | SHA-256 |
| --- | --- | --- | --- |
| `idl-exceptions` | 193957–198581 | 4624 | `4620512e385ee5314d440b5389ed932b97fd7ee83716ba2d557262ca01548004` |
| `js-promise` | 346519–347497 | 978 | `a710551eedb15814beca6800389880df8f9fad12875f6dd3f28e5e2f26f7aa70` |
| `js-exceptions` | 663547–663610 | 63 | `a0fdd35c9b901d982f1a30028ed67378682c40f018104817a3f2cacb28a9263d` |

Three facts about the heading tags themselves matter to the generator:

- `idl-promise` is written `<h4 oldids="dom-promise" id="idl-promise" interface lt="Promise|Promise&lt;T&gt;">`. The `id` is not the first attribute, and the tag also carries the Bikeshed *heading-is-a-definition* markers `interface` and `lt`. `attrValue?` reads the right value (`id=` inside `oldids=` is not preceded by whitespace, so it is not misread), but the heading is simultaneously the `<dfn>` for the `Promise` interface type and no `<dfn>` tag exists for it.
- `js-exception-objects` is written `<h4 id="js-exception-objects" oldids="…" dfn>`. The bare `dfn` attribute makes the heading itself the definition of "exception objects"; again there is no `<dfn>` tag.
- `idl-DOMException` is written `<h3 id="idl-DOMException" interface oldids="dfn-DOMException">`, so the `DOMException` interface's own definition is the heading. The `id` carries upper-case letters, which any authored `dispositions.tsv` line must reproduce exactly.

`js-promise-manipulation` and `js-promise-examples` are `<h5>`. `scanHeadings`
accepts levels 2–4 only, so both are invisible to the disposition walk and
every row inside them resolves against the `js-promise` `<h4>`. That single
fact is why the eleven real promise operations and the seven worked examples
would receive the same disposition today. Streams has 0 `<h5>` headings at
line start and Infra has 0, so raising the level ceiling is byte-neutral for
both existing censuses.

### 1.2 Algorithm blocks in scope

26 `<div>` elements in scope carry an `algorithm` attribute. 25 of them open
with the byte prefix `<div algorithm`; one does not and is invisible to the
present scanner (marked ✗). The `id` column is the derived row id the current
`scanOps` naming ladder would produce (verified by replaying the ladder).

| Section | derived `op` id | start | end | length | SHA-256 | seen? |
| --- | --- | --- | --- | --- | --- | --- |
| `idl-DOMException-derived-predefineds` | `op.quotaexceedederror-quota-exceeded-error-message-options` | 214573 | 215831 | 1258 | `058bb10014d24c4dcfb77050f02193ce07f8ef6dbba643d103df8c5977b83ffc` | ✓ |
| `idl-DOMException-derived-predefineds` | `op.quota-exceeded-error-serialization-steps` | 216470 | 216860 | 390 | `1bdcd05ecca0b4517b231b35aadfec823e7a0c3dc24d53945b5e4b370761edbe` | ✓ |
| `idl-DOMException-derived-predefineds` | `op.quota-exceeded-error-deserialization-steps` | 216862 | 217258 | 396 | `b595923cd7a3d7ea789812018fe48c8ba464eb3109215a72a4adbf632a691a7a` | ✓ |
| `js-promise` (lead) | *(no row today)* `<div id="js-to-promise" algorithm="convert a JavaScript value to promise">` | 346692 | 347209 | 517 | `c42584ffe744b7ecb64aee1920b52123a79024aa81ad1ed268f34351cc87158b` | ✗ |
| `js-promise-manipulation` | `op.a-new-promise` | 347604 | 347946 | 342 | `a9c212f9448d6cfdaf262e33f33ed5104392aaec738b6e3ae22b285edc3751b3` | ✓ |
| `js-promise-manipulation` | `op.a-promise-resolved-with` | 347948 | 348631 | 683 | `a5b86f19962066ef9844df3f2ee2494cb78c74bae6cf6690cc8ee1b6e0b60015` | ✓ |
| `js-promise-manipulation` | `op.a-promise-rejected-with` | 348633 | 349214 | 581 | `3f6d84e5da374f56e56aebba956939b54dbefb219a67137a37128ecce58f20f8` | ✓ |
| `js-promise-manipulation` | `op.resolve` | 349216 | 349783 | 567 | `071c11c45c5c1da04b86837e7911385b64880eaf3a013ff769676110af545cc3` | ✓ |
| `js-promise-manipulation` | `op.reject` | 349785 | 350073 | 288 | `c2edaaba6c2c29a161365819f857be96eabcf9ee573580a4687e8eec72a900ea` | ✓ |
| `js-promise-manipulation` | `op.dfn-perform-steps-once-promise-is-settled` | 350075 | 352408 | 2333 | `dd0e08ae5b8739280837b31e10f2ace6f1a7f9b20034124d7c748d450aaab383` | ✓ |
| `js-promise-manipulation` | `op.upon-fulfillment` | 352410 | 352816 | 406 | `81ccd0a141715f38ae30f05c97a994c4ea3fef748c6301da8f3b8e4c6c785b9d` | ✓ |
| `js-promise-manipulation` | `op.upon-rejection` | 352818 | 353237 | 419 | `f1e47b988febfd3652dac64ddb390db465d96a07f5b2d939cd8c62413221e7e9` | ✓ |
| `js-promise-manipulation` | `op.wait-for-all` | 353239 | 354879 | 1640 | `518fae182417ff76e800ed67df039a512d35b6af29ee11251b684172e703d930` | ✓ |
| `js-promise-manipulation` | `op.waiting-for-all-promise` | 354881 | 356058 | 1177 | `e8e29da9e357ce2532fe7acb9b978139f217f5dbc83db043cc2f7ffeacb605b3` | ✓ |
| `js-promise-manipulation` | `op.mark-a-promise-as-handled` | 356060 | 356713 | 653 | `644263e9155cf45d31167e53346f9d0e2431aedde301b440dbc92d9021b618bc` | ✓ |
| `js-promise-examples` | `op.delay` | 357180 | 357688 | 508 | `947b495ff64d4df797af63cc0252de4e696f7289b059114ae173f642737b9392` | ✓ |
| `js-promise-examples` | `op.validated-delay` | 358205 | 358816 | 611 | `520648ac6758cb1bfe8aaf7b54d209872c5e428255c266f01a32940cdc503b3d` | ✓ |
| `js-promise-examples` | `op.add-delay` | 359201 | 360103 | 902 | `c41832d6488f46c5e6e135f0a2118c1fef90c39180900ffff10d3898fc88e182` | ✓ |
| `js-promise-examples` | `op.environment-ready` | 360719 | 360874 | 155 | `b36bfad03aec0c8fddaa59eb6567d025b7a049e88b727b19fa8b86eacf451fa5` | ✓ |
| `js-promise-examples` | `op.environment-create` | 360876 | 361777 | 901 | `931feca212ae287d25ad348a8da9ff9c314c20cb6a3810963ea83bb0718e11e2` | ✓ |
| `js-promise-examples` | `op.add-bookmark` | 362329 | 363490 | 1161 | `c7999583a7b35262fcd27f7b4139b94ae17fd9ab73bdbed47131d590e3c4614c` | ✓ |
| `js-promise-examples` | `op.batch-request` | 364131 | 364580 | 449 | `13713a763dcfd6681cbac28d539dcbc0c003751446261d83c3b97f5f48d50482` | ✓ |
| `js-creating-throwing-exceptions` | `op.to-create-a-simple-exception` | 664734 | 665486 | 752 | `a685c4154d0f603eb41dfcc0b4cafcb2ffcfc201d1519963d63a1008d36351de` | ✓ |
| `js-creating-throwing-exceptions` | `op.to-create-a-dom-exception` | 665488 | 666331 | 843 | `9c9e8e3900f31454289e363c04d9cb3d534bc9723d7e4864788e2558acf1b54f` | ✓ |
| `js-creating-throwing-exceptions` | `op.to-create-a-dom-exception-derived-interface` | 666333 | 667324 | 991 | `ff0eedd3a45de5b085e69a570d46272ca1b9d60d1ca4b471f7561708bfc2f710` | ✓ |
| `js-creating-throwing-exceptions` | `op.throw-an-exception` | 667326 | 667543 | 217 | `eef218df5d89e680179c4fd287dc583ed2f32c627bb99c514f7e7b7c0e5b54b7` | ✓ |

Sections in scope with **no** algorithm block at all: `idl-exceptions` (lead),
`idl-DOMException-error-names`, `idl-DOMException-derived-interfaces`,
`idl-promise`, `js-DOMException-specialness`, `js-exception-objects`,
`js-handling-exceptions`, `idl-DOMException`. The last of these states the
`DOMException` constructor steps and its three getter steps as bare Bikeshed
markdown `1.` lists with no enclosing block, and states the serialization and
deserialization steps as `<ol>` lists with no enclosing block.

### 1.3 Definitions in scope

89 `<dfn>` tags open inside the five sections. 12 of them sit inside an
in-scope algorithm block (the eleven promise operations plus the
`QuotaExceededError` constructor); 77 stand alone. The `for` and `id` columns
are the literal attribute values; `–` means the attribute is absent, in which
case Bikeshed derives the anchor from the name.

| Section | name (`lt` head, else text) | `for` | `id` | span | Bikeshed dfn type |
| --- | --- | --- | --- | --- | --- |
| `idl-exceptions` | exception | – | `dfn-exception` | 194001–194047 | export |
| `idl-exceptions` | simple exception | – | `dfn-simple-exception` | 194435–194495 | export |
| `idl-exceptions` | EvalError | – | – | 194546–194576 | exception |
| `idl-exceptions` | RangeError | – | – | 194581–194612 | exception |
| `idl-exceptions` | ReferenceError | – | – | 194617–194652 | exception |
| `idl-exceptions` | TypeError | – | – | 194657–194687 | exception |
| `idl-exceptions` | URIError | – | – | 194692–194721 | exception |
| `idl-exceptions` | create | `exception` | `dfn-create-exception` | 195896–195975 | export |
| `idl-exceptions` | throw | `exception` | `dfn-throw` | 196146–196212 | export |
| `error-names` | DOMException names table | – | `dfn-error-names-table` | 198663–198745 | export |
| `error-names` | IndexSizeError | – | `indexsizeerror` | 200637–200712 | export, exception |
| `error-names` | INDEX_SIZE_ERR | `DOMException` | `dom-domexception-index_size_err` | 200813–200920 | export, const |
| `error-names` | HierarchyRequestError | – | `hierarchyrequesterror` | 200979–201068 | export, exception |
| `error-names` | HIERARCHY_REQUEST_ERR | `DOMException` | `dom-domexception-hierarchy_request_err` | 201174–201295 | export, const |
| `error-names` | WrongDocumentError | – | `wrongdocumenterror` | 201354–201437 | export, exception |
| `error-names` | WRONG_DOCUMENT_ERR | `DOMException` | `dom-domexception-wrong_document_err` | 201531–201646 | export, const |
| `error-names` | InvalidCharacterError | – | `invalidcharactererror` | 201705–201794 | export, exception |
| `error-names` | INVALID_CHARACTER_ERR | `DOMException` | `dom-domexception-invalid_character_err` | 201878–201999 | export, const |
| `error-names` | NoModificationAllowedError | – | `nomodificationallowederror` | 202058–202157 | export, exception |
| `error-names` | NO_MODIFICATION_ALLOWED_ERR | `DOMException` | `dom-domexception-no_modification_allowed_err` | 202233–202366 | export, const |
| `error-names` | NotFoundError | – | `notfounderror` | 202425–202498 | export, exception |
| `error-names` | NOT_FOUND_ERR | `DOMException` | `dom-domexception-not_found_err` | 202576–202681 | export, const |
| `error-names` | NotSupportedError | – | `notsupportederror` | 202740–202821 | export, exception |
| `error-names` | NOT_SUPPORTED_ERR | `DOMException` | `dom-domexception-not_supported_err` | 202897–203010 | export, const |
| `error-names` | InUseAttributeError | – | `inuseattributeerror` | 203069–203154 | export, exception |
| `error-names` | INUSE_ATTRIBUTE_ERR | `DOMException` | `dom-domexception-inuse_attribute_err` | 203255–203372 | export, const |
| `error-names` | InvalidStateError | – | `invalidstateerror` | 203432–203513 | export, exception |
| `error-names` | INVALID_STATE_ERR | `DOMException` | `dom-domexception-invalid_state_err` | 203592–203705 | export, const |
| `error-names` | SyntaxError | – | `syntaxerror` | 203765–203834 | export, exception |
| `error-names` | SYNTAX_ERR | `DOMException` | `dom-domexception-syntax_err` | 203925–204024 | export, const |
| `error-names` | InvalidModificationError | – | `invalidmodificationerror` | 204084–204179 | export, exception |
| `error-names` | INVALID_MODIFICATION_ERR | `DOMException` | `dom-domexception-invalid_modification_err` | 204267–204394 | export, const |
| `error-names` | NamespaceError | – | `namespaceerror` | 204454–204529 | export, exception |
| `error-names` | NAMESPACE_ERR | `DOMException` | `dom-domexception-namespace_err` | 204651–204756 | export, const |
| `error-names` | InvalidAccessError | – | `invalidaccesserror` | 204835–204918 | export, exception |
| `error-names` | INVALID_ACCESS_ERR | `DOMException` | `dom-domexception-invalid_access_err` | 205273–205381 | const (not exported) |
| `error-names` | TypeMismatchError | – | `typemismatcherror` | 205460–205541 | export, exception |
| `error-names` | TYPE_MISMATCH_ERR | `DOMException` | `dom-domexception-type_mismatch_err` | 205641–205747 | const (not exported) |
| `error-names` | SecurityError | – | `securityerror` | 205807–205880 | export, exception |
| `error-names` | SECURITY_ERR | `DOMException` | `dom-domexception-security_err` | 205951–206054 | export, const |
| `error-names` | NetworkError | – | `networkerror` | 206114–206185 | export, exception |
| `error-names` | NETWORK_ERR | `DOMException` | `dom-domexception-network_err` | 206255–206356 | export, const |
| `error-names` | AbortError | – | `aborterror` | 206416–206483 | export, exception |
| `error-names` | ABORT_ERR | `DOMException` | `dom-domexception-abort_err` | 206554–206651 | export, const |
| `error-names` | URLMismatchError | – | `urlmismatcherror` | 206730–206809 | export, exception |
| `error-names` | URL_MISMATCH_ERR | `DOMException` | `dom-domexception-url_mismatch_err` | 206882–206993 | export, const |
| `error-names` | QUOTA_EXCEEDED_ERR | `DOMException` | `dom-domexception-quota_exceeded_err` | 207251–207366 | export, const |
| `error-names` | TimeoutError | – | `timeouterror` | 207426–207497 | export, exception |
| `error-names` | TIMEOUT_ERR | `DOMException` | `dom-domexception-timeout_err` | 207566–207667 | export, const |
| `error-names` | InvalidNodeTypeError | – | `invalidnodetypeerror` | 207727–207814 | export, exception |
| `error-names` | INVALID_NODE_TYPE_ERR | `DOMException` | `dom-domexception-invalid_node_type_err` | 207950–208071 | export, const |
| `error-names` | DataCloneError | – | `datacloneerror` | 208131–208206 | export, exception |
| `error-names` | DATA_CLONE_ERR | `DOMException` | `dom-domexception-data_clone_err` | 208280–208387 | export, const |
| `error-names` | EncodingError | – | `encodingerror` | 208447–208520 | export, exception |
| `error-names` | NotReadableError | – | `notreadableerror` | 208677–208756 | export, exception |
| `error-names` | UnknownError | – | `unknownerror` | 208884–208955 | export, exception |
| `error-names` | ConstraintError | – | `constrainterror` | 209127–209204 | export, exception |
| `error-names` | DataError | – | `dataerror` | 209400–209465 | export, exception |
| `error-names` | TransactionInactiveError | – | `transactioninactiveerror` | 209591–209686 | export, exception |
| `error-names` | ReadOnlyError | – | `readonlyerror` | 209893–209966 | export, exception |
| `error-names` | VersionError | – | `versionerror` | 210143–210214 | export, exception |
| `error-names` | OperationError | – | `operationerror` | 210413–210488 | export, exception |
| `error-names` | NotAllowedError | – | `notallowederror` | 210640–210717 | export, exception |
| `error-names` | OptOutError | – | `optouterror` | 210944–211013 | export, exception |
| `derived-predefineds` | requested | `QuotaExceededError` | – | 214411–214463 | export |
| `derived-predefineds` | quota | `QuotaExceededError` | – | 214470–214518 | export |
| `derived-predefineds` | QuotaExceededError(message, options) | `QuotaExceededError` | – | 214597–214731 | constructor |
| `derived-predefineds` | quota | `QuotaExceededError` | – | 215837–215888 | attribute |
| `derived-predefineds` | requested | `QuotaExceededError` | – | 215962–216017 | attribute |
| `idl-promise` | promise type | – | `dfn-promise-type` | 252273–252325 | export |
| `js-promise-manipulation` | a new promise | – | – | 347628–347671 | export |
| `js-promise-manipulation` | a promise resolved with | – | – | 347981–348044 | export |
| `js-promise-manipulation` | a promise rejected with | – | – | 348666–348729 | export |
| `js-promise-manipulation` | resolve | – | – | 349240–349265 | export |
| `js-promise-manipulation` | reject | – | – | 349809–349833 | export |
| `js-promise-manipulation` | react | `promise` | `dfn-perform-steps-once-promise-is-settled` | 350099–350203 | export |
| `js-promise-manipulation` | upon fulfillment | – | – | 352453–352487 | export |
| `js-promise-manipulation` | upon rejection | – | – | 352861–352893 | export |
| `js-promise-manipulation` | wait for all | – | – | 353263–353327 | export |
| `js-promise-manipulation` | get a promise to wait for all | – | `waiting-for-all-promise` | 354909–355058 | export |
| `js-promise-manipulation` | mark a promise as handled | – | – | 356083–356163 | export |
| `js-promise-examples` | ready promise | `Environment` | – | 360589–360631 | *(none)* |
| `js-handling-exceptions` | an exception was thrown | – | – | 669580–669614 | *(none)* |
| `idl-DOMException` | name | `DOMException` | – | 675261–675302 | export |
| `idl-DOMException` | message | `DOMException` | – | 675307–675351 | export |
| `idl-DOMException` | DOMException(message, name) | `DOMException` | – | 675376–675499 | constructor |
| `idl-DOMException` | name | `DOMException` | – | 675637–675694 | attribute |
| `idl-DOMException` | message | `DOMException` | – | 675761–675821 | attribute |
| `idl-DOMException` | code | `DOMException` | – | 675891–675948 | attribute |

Three definitions in scope carry **no `<dfn>` tag at all**, because Bikeshed
lets a heading be the definition: `Promise` (the interface type, on the
`idl-promise` heading), "exception objects" (on the `js-exception-objects`
heading), and `DOMException` (the interface, on the `idl-DOMException`
heading). Any `<dfn`-keyed scanner misses all three.

### 1.4 IDL blocks and the error-names table

The Web IDL source uses **zero** `<xmp class="idl">` blocks. It writes IDL in
`<pre class="idl">` (11 occurrences) and `<pre class=idl>` (1, unquoted). Two
are in scope. Example IDL is written `<pre highlight="webidl">` (93 in the
file, 8 in scope) and must stay invisible.

| Structure | section | span | length | SHA-256 |
| --- | --- | --- | --- | --- |
| `<table id="error-names" class="vert data">` | `idl-DOMException-error-names` | 200422–211136 | 10714 | `19f118f10e7fd738b516afd4ded1e83cf17edda2a433a1eb281a7b615ff6fd49` |
| `<pre class=idl>` QuotaExceededError + QuotaExceededErrorOptions | `idl-DOMException-derived-predefineds` | 213511–213861 | 350 | `c261d7cb63c4c311acc3ef1d020dc30d041b64599fa9a3454510fca85419b669` |
| `<pre class="idl">` DOMException | `idl-DOMException` | 673570–675052 | 1482 | `8c1843c9c476d21a743b43d59dae846a6e877f22dd4413ebe39648dd34d8d494` |

The error-names table is not a source of rows by itself: every one of its 32
name cells and 22 legacy-code cells carries its own `<dfn>` (listed above), so
the table is the layout, not the definition carrier. Its span spills to within
two bytes of the next heading.

### 1.5 Element census of the five sections

| Section | `<dfn>` | of which `exception` | of which `const` | `<div algorithm` | `<div …algorithm=` | `<pre class=idl>` |
| --- | --- | --- | --- | --- | --- | --- |
| `idl-exceptions` (lead) | 9 | 5 | 0 | 0 | 0 | 0 |
| `idl-DOMException-error-names` | 55 | 32 | 22 | 0 | 0 | 0 |
| `idl-DOMException-derived-interfaces` | 0 | 0 | 0 | 0 | 0 | 0 |
| `idl-DOMException-derived-predefineds` | 5 | 0 | 0 | 3 | 3 | 1 |
| `idl-promise` | 1 | 0 | 0 | 0 | 0 | 0 |
| `js-promise` (lead) | 0 | 0 | 0 | 0 | **1** | 0 |
| `js-promise-manipulation` | 11 | 0 | 0 | 11 | 11 | 0 |
| `js-promise-examples` | 1 | 0 | 0 | 7 | 7 | 0 |
| `js-exceptions` (lead) | 0 | 0 | 0 | 0 | 0 | 0 |
| `js-DOMException-specialness` | 0 | 0 | 0 | 0 | 0 | 0 |
| `js-exception-objects` | 0 | 0 | 0 | 0 | 0 | 0 |
| `js-creating-throwing-exceptions` | 0 | 0 | 0 | 4 | 4 | 0 |
| `js-handling-exceptions` | 1 | 0 | 0 | 0 | 0 | 0 |
| `idl-DOMException` | 6 | 0 | 0 | 0 | 0 | 1 |

`idl-DOMException-derived-interfaces` has no `<dfn>`, no algorithm block and
no IDL block. Its whole content is a six-bullet list of `must`/`should`
constraints on how a specification derives an interface from `DOMException`,
plus one prose sentence about creating and throwing them. It is a
`requirement` section with no row source under either present mode. The six
top-level bullets begin at bytes 211607, 211775, 211922, 212162, 212319 and
212508.

Example and note containers in scope, all of which must be excluded from any
`owned` count: `<div class="example">` at 196439, 197424, 212974, 356789,
357697, 358825, 360112, 361786, 363499, 669667, and `<div class="note">` at
667545. All seven `js-promise-examples` algorithm blocks are nested inside
these example containers.

## 2. What `Gates/Census.lean` would do to these sections today

### 2.1 The Streams mode (`definitionKeyed := false`)

**Hard blocker.** `build` calls `scanRequirements bs ops` unconditionally in
the non-definition-keyed branch, and `scanRequirements` opens with a literal
search for the byte string `<div algorithm="ReadableStreamPipeTo">`. On any
other source that search fails and the whole run returns
`.error "census: the ReadableStreamPipeTo algorithm block was not found"`.
A Web IDL census cannot use this mode without changing that function.

Setting that aside and replaying the four scanners over the Web IDL bytes:

**`scanOps` — 156 rows file-wide, no errors, no duplicate ids, every anchor
unique.** I replayed the naming ladder and the `chooseAnchorLength` ladder in
full: all 156 rows resolve to a distinct id and every one finds a unique
prefix anchor within the admitted lengths. 25 of the 156 fall in scope.

Its defect here is the key: `scanOps` keys on the byte prefix `<div algorithm`.
The Web IDL source writes 201 `<div>` tags carrying an `algorithm` attribute,
of which **45 put `id=` first** (`<div id="js-to-promise" algorithm="convert a
JavaScript value to promise">` and the 44 sibling type conversions). Those 45
are dropped silently — exactly the failure mode that `SPEC-MANIFEST.md` records
for keying on the closing bracket, one level up. One of the 45 is in scope.
The same defect propagates to `algorithmBlocks`, which the definition mode uses
to find a definition's enclosing block.

Naming quality in scope is poor because the ladder prefers an explicit `id`
over the definition's name: `react` becomes
`op.dfn-perform-steps-once-promise-is-settled`, "get a promise to wait for all"
becomes `op.waiting-for-all-promise`, "mark as handled" becomes
`op.mark-a-promise-as-handled` (the first `lt` alternative rather than the
canonical spelling), and the `QuotaExceededError` constructor becomes
`op.quotaexceedederror-quota-exceeded-error-message-options`. These are stable
and unique, so they are usable, but they will not read back as the
specification's own verbs and the P8 packet will be citing them constantly.

**`scanSlots` — 47 rows file-wide, 9 anchored in scope, none of them a
definition.** The rule (a `[[Name]]` counts when some occurrence is preceded by
`\` or `/`) admits 47 of 53 candidates. Pass two, which prefers a defining
`<dfn>`, finds **none**: the file contains 0 `<dfn>` whose `lt` or immediate
text is a `[[…]]` slot. Every slot row therefore anchors at an incidental use
site. The 9 whose first qualified occurrence is in scope are `Quota` (216714),
`Requested` (216793), `Resolve` (347104), `Promise` (347417), `Intrinsics`
(347843), `Reject` (349110), `PromiseIsHandled` (356278), `Name` (676319) and
`Message` (676413) — every one of them an ECMA-262 or HTML-serialization
internal, not a Web IDL concept. The remaining 38 are the object-model
internals of the JavaScript binding (`[[Writable]]`, `[[Enumerable]]`,
`[[BackingList]]`, `[[Unforgeables]]`, and so on). `scanSlots` is the wrong
row source for this standard.

**`scanIdl` — 0 rows, and two distinct mis-parses once the tag is fixed.** The
opener it searches for, `<xmp class="idl">`, occurs 0 times. All twelve IDL
blocks are invisible, so the `DOMException` interface and its 30 members
produce nothing. I re-ran the statement machine against the two in-scope
blocks with the opener swapped for `<pre class=…idl…>`:

- **QuotaExceededError block (213511).** The accumulated header statement is
  `[Exposed=*, Serializable] interface QuotaExceededError : DOMException {`.
  After `stripExtendedAttribute` the word list is
  `["interface","QuotaExceededError",":","DOMException","{"]`, which matches
  none of the three admitted header shapes, so the run **aborts** with
  `census: unrecognised IDL header`. Interface inheritance is unsupported.
- **DOMException block (673570).** The header line ends with a trailing `//`
  comment (`interface DOMException { // but see below note about JavaScript
  binding`), so the accumulator never sees a terminating `{` and keeps
  swallowing lines until the constructor's `;`. The result is one unrecognised
  top-level statement; `owner` is never set; and every one of the following 29
  lines is then also treated as a top-level statement. **30 statements are
  silently counted as skipped and 0 rows are produced.** Even with `owner` set
  correctly, `const unsigned short INDEX_SIZE_ERR = 1;` would be named by
  `trailingIdent` as `1`, giving `idl.domexception-1` … `idl.domexception-25`:
  `const` members have no case in the member-naming ladder.

**`scanRequirements`** — fails as described. Even generalised, its naming
ladder (bullet's own `<dfn>` id, else the kebab of a `<strong>` lead-in) finds
neither on the six `idl-DOMException-derived-interfaces` bullets, which open
with `The [=identifier=] of the [=interface=] must …`. Those bullets need
authored names.

**`scanHeadings` / `sectionPath`** — work, with the h5 blindness described in
§1.1. `dispositions.tsv` keys would have to be exact-case (`idl-DOMException`,
`js-DOMException-specialness`).

**Net for the Streams mode, in scope:** 25 `op` rows, 9 `slot` rows, 0 `idl`
rows, a run-aborting `scanRequirements`, and **not one row for any of the 89
definitions**: no row for `exception`, `simple exception`, the five simple
exception types, `create`, `throw`, the `DOMException` names table, any of the
32 error names, `promise type`, or the `DOMException` associated name and
message.

### 2.2 The Infra mode (`definitionKeyed := true`)

I replayed `scanDefinitions` over the whole file. 384 `<dfn>` tags; 2 skipped
(`ignore`, or a `for` containing `/`); **382 candidate rows**.

**It aborts.** Four row ids collide, and all four collisions are inside the
sections in scope:

| colliding id | first dfn | second dfn |
| --- | --- | --- |
| `dom-exception-name` | 675261 (associated value) | 675637 (attribute getter) |
| `dom-exception-message` | 675307 (associated value) | 675761 (attribute getter) |
| `quota-exceeded-error-quota` | 214470 (associated value) | 215837 (attribute getter) |
| `quota-exceeded-error-requested` | 214411 (associated value) | 215962 (attribute getter) |

`build` fails with `census: duplicate row id(s)`. The naming ladder ignores
the Bikeshed dfn *type*, so the associated value and the IDL attribute that
exposes it become the same name.

**Its spans are meaningless on this source.** The Infra source is written with
explicit `<p>`, `<dt>` and `<li>` wrappers; the Web IDL source is written in
Bikeshed markdown and has only 99 paragraph openers (`<p>` 11, `<p ` 63,
`<dt>` 5, `<li>` 20) for 384 definitions. Of the 382 rows, only 89 land inside
an algorithm block. The other 293 fall through to "the last `<p>`/`<dt>`/`<li>`
anywhere before me", giving:

| statistic | value |
| --- | --- |
| rows whose span comes from an algorithm block | 89 |
| rows whose span comes from the paragraph fallback | 274 |
| …plus the fallback extended through a following `<ol>` | 19 |
| fallback rows whose span starts more than 2,000 bytes before the definition | 257 |
| median distance from span start to the definition, fallback rows | 9,671 bytes |
| worst case | `dom-exception-code` at 675891, span starts at 560241 — **115,650 bytes early** |

All six `idl-DOMException` definitions share a span start at byte 560241, in
an unrelated section of the JavaScript binding. Nineteen rows take the
`endsWith ':'` branch and reach for the next `<ol`, of which the file has only
four; those spans jump across sections. No error fires for any of this — the
generator would happily anchor and digest garbage.

**Net for the Infra mode, in scope:** 89 rows, an abort on four of them, and
spans that are not usable as anchors for any of the rest.

### 2.3 The minimal extension

The two existing modes are complements, not alternatives: Web IDL's promise
section is algorithm-keyed, its exception section is definition-keyed, and its
`DOMException` interface is IDL-block-keyed. The extension therefore replaces
the single `definitionKeyed : Bool` with independent row-source switches plus a
section scope, and repairs four parsers. Described as a diff against
`Gates/Census.lean`:

**(a) `structure Standard`** — replace `definitionKeyed : Bool` by four
booleans `algorithmRows`, `definitionRows`, `idlRows`, `slotRows`; add
`requirementMarker : Option String` (the algorithm-block locator that
`scanRequirements` keys on) and `sectionScope : Array String` (heading ids;
empty means the whole document). `streams` becomes
`{ algorithmRows := true, definitionRows := false, idlRows := true,
slotRows := true, requirementMarker := some "<div algorithm=\"ReadableStreamPipeTo\">",
sectionScope := #[] }` and `infra` becomes
`{ algorithmRows := false, definitionRows := true, idlRows := false,
slotRows := false, requirementMarker := none, sectionScope := #[] }`, both
byte-identical to today. A new `webidl` record turns on algorithm, definition
and IDL rows, turns off slot rows, sets `requirementMarker := none`, and lists
the five section ids.

**(b) `build`** — replace the `if std.definitionKeyed then … else …` split by
a union of the enabled scanners, then, when `sectionScope` is non-empty, drop
every row whose `sectionPath` triple contains none of the whitelisted ids.
Scope filtering must happen *before* the disposition join and before the
duplicate check, and the scanners must not raise on out-of-scope material, so
each scanner takes the scope predicate as a parameter rather than being
filtered after the fact.

**(c) `scanOps` and `algorithmBlocks`** — key on a `<div` tag that carries an
`algorithm` attribute anywhere in the tag, instead of on the byte prefix
`<div algorithm`. Concretely, iterate `occurrences bs "<div"`, find the tag
end, and accept when `attrText? bs i (tagE+1) "algorithm"` is `some` or
`hasBareAttr bs i (tagE+1) "algorithm"`. **Verified byte-neutral for both
existing censuses:** Streams has 248 tags under either rule and Infra has 18
under either rule, so the drift gate stays green while Web IDL gains its 45
missing blocks. Optionally move the `algorithm` attribute ahead of the block's
first `<dfn>` in the naming ladder for a standard that opts in, which turns
`op.dfn-perform-steps-once-promise-is-settled` into `op.react`; that is *not*
byte-neutral for Streams, so it must be a per-`Standard` flag.

**(d) `scanIdl`** — take the block opener from the `Standard` (a list of
openers with their closers: `<xmp class="idl">`/`</xmp>` for Streams,
`<pre class="idl">` and `<pre class=idl>`/`</pre>` for Web IDL). Then three
statement-level repairs, all needed by the two in-scope blocks: strip a
trailing `//…` comment from each line before the `;`/`{` terminator test;
accept `interface <Name> : <Base> {` in the header match (a five-word form with
`:` in third position); and give `const` members their declared name by taking
`trailingIdent` of the part before ` = ` rather than of the whole body.

**(e) `scanDefinitions`** — two repairs. First, the paragraph fallback must
respect blank-line chunking: when the last `<p>`/`<dt>`/`<li>` opener before the
definition lies *before* the definition's own blank-line-delimited chunk, start
the span at that chunk's start instead. On Infra the two agree (every
definition there is inside an explicit wrapper), so this is byte-neutral; on
Web IDL it turns 274 garbage spans into paragraph spans. Second, read the
Bikeshed dfn type from the tag and use it, both to choose the row kind
(`attribute`/`const`/`constructor` → `idl`, `exception` → `type`, everything
else → `op`) and to break the four id collisions. Infra uses none of those
attributes, so the kind mapping is byte-neutral there too.

**(f) `scanRequirements`** — gate it on `requirementMarker`, and when the
marker is `none` produce no requirement rows from it. Web IDL's six
`idl-DOMException-derived-interfaces` bullets then come in through the authored
`rules.tsv` route, which already exists and is empty at P1. Caveat: `scanRules`
runs a span from the locator to the next blank line, and the six bullets sit in
one blank-line-delimited paragraph, so six authored rule rows would all end at
the same offset with nested spans. Either accept nested spans, author a single
`rule` row for the whole list, or add an authored end locator. This is an open
decision (§6.4).

**(g) `scanHeadings` / `sectionPath`** — either raise the level ceiling from
`0x34` to `0x35` and widen `sectionPath` to a four-tuple, or leave the code
alone and author eight per-row overrides for the `js-promise-examples`
contents. Both existing sources have 0 `<h5>` at line start, so the code change
is byte-neutral; the override route needs no code change at all and is the
smaller diff.

**(h) `readPinnedInput` / `standards`** — the new `webidl` record with input
`vendor/whatwg-webidl-a652053f/index.bs`, digest
`3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83`, census
`generated/webidl-census.tsv`, authored dir `census/webidl`, and `emit? := none`
in `cli` (no numerator yet, exactly as Infra is handled).

**Expected row counts under (a)–(h), scoped to the five sections:**

| kind | count | source |
| --- | --- | --- |
| `op` | 26 | 25 `<div algorithm` blocks + `js-to-promise` |
| `idl` | 37 | DOMException 30 (header, constructor, 3 attributes, 25 consts) + QuotaExceededError 4 + QuotaExceededErrorOptions 3 |
| definitions (`op`/`type`) | 49 | 77 standalone `<dfn>` minus the 28 `const`/`attribute`/`constructor` dfns that the IDL block rows already carry |
| `requirement` | 6 | the derived-interfaces bullets, authored |
| `slot` | 0 | `slotRows := false`; would be 9 if left on |
| **total** | **118** | |

Leaving every standalone definition in raises the total to 146 and reintroduces
the four id collisions. Leaving `slotRows` on adds 9. Nothing in this table is
a denominator: dispositions in §4 put a substantial part of it outside one.

## 3. The promise operations, and how often Streams invokes them

Eleven operations are defined in `js-promise-manipulation`, one type in
`idl-promise`, and two conversions in the `js-promise` lead. Streams usage was
counted over all 2,188 `[=…=]` autolinks in `vendor/whatwg-streams-b9ba9f49/index.bs`,
normalising internal whitespace (Bikeshed lets an autolink wrap across lines —
`[=a promise rejected\n    with=]` occurs 8 times and a naive single-line count
loses 12 invocations of the two `a promise …with` operations), splitting the
display-text form on `|`, and matching case-insensitively (Streams writes
`[=Resolve=]`, `[=Reject=]`, `[=React=]`, `[=Upon fulfillment=]`,
`[=Upon rejection=]` at step starts).

| # | operation (canonical `lt`) | `for` | explicit `id` | dfn span | algorithm-block span | Streams invocations |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `a new promise` | – | *none* (Bikeshed anchor from the name) | 347628–347671 | 347604–347946 | **18** |
| 2 | `a promise resolved with` | – | *none* | 347981–348044 | 347948–348631 | **46** |
| 3 | `a promise rejected with` | – | *none* | 348666–348729 | 348633–349214 | **46** |
| 4 | `resolve` | – | *none* | 349240–349265 | 349216–349783 | **35** |
| 5 | `reject` | – | *none* | 349809–349833 | 349785–350073 | **23** |
| 6 | `react` \| `reacting` | `promise` | `dfn-perform-steps-once-promise-is-settled` | 350099–350203 | 350075–352408 | **8** (`React` 3, `reacting` 5) |
| 7 | `upon fulfillment` | – | *none* | 352453–352487 | 352410–352816 | **9** |
| 8 | `upon rejection` | – | *none* | 352861–352893 | 352818–353237 | **11** |
| 9 | `wait for all` \| `waiting for all` | – | *none* | 353263–353327 | 353239–354879 | **0** (reached only through #10) |
| 10 | `get a promise to wait for all` \| `getting a promise to wait for all` | – | `waiting-for-all-promise` | 354909–355058 | 354881–356058 | **1** |
| 11 | `mark a promise as handled` \| `mark as handled` | – | *none* | 356083–356163 | 356060–356713 | **0** |
| 12 | `promise type` (the IDL type) | – | `dfn-promise-type` | 252273–252325 | — | **0** by autolink; **21** `Promise<…>` IDL declarations |
| 13 | convert a JavaScript value to promise | — | div `js-to-promise` | — | 346692–347209 | reached implicitly by each of the 21 `Promise<…>` arguments |
| 14 | convert an IDL promise to a JavaScript value | — | `<p id="promise-to-js">`, no block | — | — | reached implicitly by each `Promise<…>` return |

**197 direct invocations** of Web IDL promise operations in the Streams source.

What the join says for the first packet:

- Six operations carry the whole load: `a promise resolved with` (46),
  `a promise rejected with` (46), `resolve` (35), `reject` (23), `a new promise`
  (18) and `upon rejection`/`upon fulfillment` (20 combined). Those six are
  168 of 197.
- `react` (8) is the primitive the two `upon …` operations are defined over, so
  it is on the critical path even though it is directly invoked eight times.
- `wait for all` is reachable from Streams only through
  `get a promise to wait for all`, used exactly once, in the pipe-to shutdown
  path. It can be deferred to a P7-facing packet.
- `mark as handled` is invoked **0** times by the Streams source. The Web IDL
  note beside it names `writableStreamWriter.closed` as its motivating case, but
  the pinned Streams text does not use the operation, and the string "handled"
  does not occur in the Streams source outside `{{unhandledrejection}}` in one
  example and two occurrences of ordinary prose. It carries no Streams
  obligation at this pin.
- `Whatwg/WebIdl/Promise.lean`'s docstring reserves "the rule that a rejected
  promise passed to an algorithm is a 'handled' promise". **No such rule exists
  in this pin.** The only mention of `[[PromiseIsHandled]]` in the whole file is
  step 1 of `mark as handled` at 356278. The stub's prose must be corrected or
  the rule sourced from ECMA-262 or HTML before it is cited.

The eleven operations reduce to a small ECMA-262 surface: `NewPromiseCapability`
(5 uses in scope), `PerformPromiseThen` (2), `Call` (5), `CreateBuiltinFunction`
(4), `Construct` (1), and the intrinsics `%Promise%` (5),
`%Promise.prototype.then%` (1, in a note) and `%Error.prototype%` (1). Nothing
else from ECMA-262 is touched by the promise operations.

## 4. Proposed dispositions

Vocabulary is `SPEC-MANIFEST.md`'s and nothing else. Rows outside the
denominator are `evidenceOnly`, `refused` and `targetOnly`. Applying DB-11
(the promise verbs and exception kinds live in `Whatwg.WebIdl` beneath Streams,
over `Whatwg.Ecma262`) and the standing manifest rule that the binding layer —
conversions, brand checks, overload resolution — is `hostOnly`.

### 4.1 Section defaults

| Section (or sub-scope) | kind | proposed | reason | ratify? |
| --- | --- | --- | --- | --- |
| `js-promise-manipulation` (h5, by override or h5 support) | `*` | `owned` | These eleven operations are the promise verbs DB-11 places in `Whatwg.WebIdl`; Streams invokes them 197 times. | no |
| `js-promise-examples` (h5) | `*` | `evidenceOnly` | Seven worked examples inside `<div class="example">` containers, defining `delay`, `Environment` and `addBookmark` for illustration only. | no |
| `js-promise` (h4 lead) | `*` | `hostOnly` | Its one algorithm is the JavaScript-value-to-`Promise<T>` conversion and its one paragraph is the reverse conversion; conversions are the binding layer the manifest already rules `hostOnly`. | no |
| `idl-promise` | `*` | `owned` | `promise type` is the carrier the eleven operations range over and the type of all 21 Streams `Promise<…>` declarations. | **yes** — it could equally be `hostOnly` as a pure type-system entry; see §6.2 |
| `idl-exceptions` (h3 lead) | `*` | `owned` | `exception`, `simple exception`, the five simple exception types, and the specification-level `create`/`throw` are the first-order exception universe `Whatwg.WebIdl.Exceptions` is reserved for. | no |
| `idl-DOMException-error-names` | `type` / `op` | `owned` | The 32 error names are the closed name universe every WHATWG algorithm draws from. | no |
| `idl-DOMException-error-names` | `idl` | `hostOnly` | The 22 legacy `const` rows are numeric compatibility constants exposed by the host's IDL layer. | no |
| `idl-DOMException-derived-interfaces` | `requirement` | `requirement` | Six `must`/`should` constraints on deriving an interface, stated as constraints with no algorithm — the definition of the `requirement` disposition. | no |
| `idl-DOMException-derived-predefineds` | `*` | `hostOnly` | `QuotaExceededError` is one predefined derived interface with a constructor, two attributes and structured-clone hooks; no Streams algorithm reaches it (0 occurrences of the name in the Streams source). | **yes** — `evidenceOnly` is arguable since it is the worked instance of the preceding requirements |
| `js-DOMException-specialness` | `*` | `hostOnly` | States what the JavaScript binding does to the `DOMException` prototype and `[[ErrorData]]`; pure binding. | no |
| `js-exception-objects` | `*` | `hostOnly` | Two sentences saying which host object represents each exception kind. Note it produces **no row** today (§1.3). | **yes** — needs a row before it can carry a disposition |
| `js-creating-throwing-exceptions` | `*` | `owned` | The four algorithms that give `create` and `throw` their meaning; these are what `Whatwg.WebIdl.Exceptions` must realize. | no |
| `js-handling-exceptions` | `*` | `evidenceOnly` | One propagation sentence plus a long JavaScript example; the propagation rule is ECMA-262's. | **yes** — the propagation sentence could be `requirement` |
| `idl-DOMException` | `idl` | `hostOnly` | The interface declaration and its 30 members are the host's IDL surface. | no |
| `idl-DOMException` | `op` | `owned` | The associated `name` and `message` and the constructor/getter steps are the first-order content `Whatwg.WebIdl.Exceptions` carries. | no |

### 4.2 Notable individual rows

| Row | proposed | reason | ratify? |
| --- | --- | --- | --- |
| `op.a-new-promise`, `op.a-promise-resolved-with`, `op.a-promise-rejected-with`, `op.resolve`, `op.reject` | `owned` | 168 of the 197 Streams invocations; the first packet's core. | no |
| `op.react` (today `op.dfn-perform-steps-once-promise-is-settled`) | `owned` | The primitive both `upon …` operations are defined over. | no |
| `op.upon-fulfillment`, `op.upon-rejection` | `owned` | 20 Streams invocations between them; thin wrappers over `react`. | no |
| `op.wait-for-all` | `owned` | Not invoked by Streams directly, but `get a promise to wait for all` is defined over it, so it cannot be excluded. | no |
| `op.waiting-for-all-promise` (`get a promise to wait for all`) | `owned` | One Streams invocation, in the pipe-to shutdown action; P7-facing. | no |
| `op.mark-a-promise-as-handled` | `owned` | Zero Streams invocations at this pin, but it is a promise verb DB-11 names explicitly and other standards use it. | **yes** — `evidenceOnly` would keep it out of the denominator until a consumer appears; `owned` with `absent` coverage is the honest alternative |
| `op.js-to-promise` (the conversion) | `hostOnly` | Binding-layer conversion; reached by all 21 Streams `Promise<…>` declarations but never by a Streams algorithm step. | no |
| the 9 `slot` rows, if `scanSlots` is left on | `foreignBoundary` | `[[Promise]]`, `[[Resolve]]`, `[[Reject]]`, `[[PromiseIsHandled]]`, `[[Intrinsics]]`, `[[Name]]`, `[[Message]]`, `[[Quota]]`, `[[Requested]]` are ECMA-262 and HTML internals, consistent with the P1 landing ruling that promise and completion-record internals are `foreignBoundary`. | **yes** — the survey recommends emitting no slot rows at all, since none of the 47 anchors at a definition |
| `idl.domexception-*` (25 legacy code constants) | `hostOnly` | Numeric compatibility constants with no semantic content; `code` is defined to read the names table. | no |
| the 6 `rule` rows of `idl-DOMException-derived-interfaces` | `requirement` | Stated as `must`/`should` constraints realized by `QuotaExceededError`, structurally identical to the piping requirements and their reference algorithm. | no |
| `type.evalerror`, `type.rangeerror`, `type.referenceerror`, `type.typeerror`, `type.urierror` | `owned` | The five simple exception kinds; Streams uses `{{TypeError}}` 64 times and `{{RangeError}}` 13 times. | no |
| the 32 `DOMException` name rows | `owned` | A closed enumeration; `Whatwg.WebIdl.Exceptions` reifies it as data. Streams names `DataCloneError` 6 times and `AbortError` twice. | **yes** — the 25 names no WHATWG standard in this repository reaches (`InUseAttributeError`, `URLMismatchError`, …) could be `owned` in one enumeration row rather than 32 rows |

### 4.3 Dispositions rejected, with reasons

- **`refused`** is used nowhere here. Nothing in these sections is a protocol
  the repository declines to model.
- **`foreignBoundary`** is used only for slot rows if they are emitted. The
  promise operations themselves are *not* a foreign boundary: DB-11 places them
  in a Lean library over `Whatwg.Ecma262`, so the boundary sits one layer below,
  at ECMA-262's job queue, which DB-03 already rules to be deterministic state.
- **`targetOnly`** is used nowhere; no row here exists only for the P11
  TypeScript profile.

## 5. Everything that escapes the scope

Extracted from the 78 distinct `[=…=]` autolinks, 5 distinct `[$…$]` ECMA-262
links and 31 distinct `{{…}}` type links that occur inside the five sections.

**Group A — ECMA-262 abstract operations and intrinsics.** `[$Call$]` (5),
`[$Construct$]` (1), `[$CreateBuiltinFunction$]` (4), `[$NewPromiseCapability$]`
(5), `[$PerformPromiseThen$]` (2), `{{%Promise%}}` (5),
`{{%Promise.prototype.then%}}` (1), `{{%Error.prototype%}}` (1),
`[=PromiseCapability=]` (1), `[=abrupt completions=]` (1),
`[=ECMAScript/error objects=]` (1), plus the completion shorthands `[=!=]` (5)
and `[=?=]` (6).
*Record as:* a **named boundary into `Whatwg.Ecma262`**, one row per operation
or intrinsic, in a `census/webidl/dependencies.tsv` shaped like
`census/url/dependencies.tsv`. This is the smallest closed set in the survey —
five operations and three intrinsics — and it is exactly the surface
`Whatwg/Ecma262/Promise.lean` and `Whatwg/Ecma262/Jobs.lean` must cover for the
promise packet. It is a proof edge, not an external: DB-11 puts ECMA-262 inside
the repository's own library stack.

**Group B — realm, global and task machinery.** `[=realm=]` (8),
`[=current realm=]` (4), `[=relevant realm=]` (3), `[=in parallel=]` (6),
`[=Queue a task=]` (8), `[=Queue a microtask=]` (1), `[=task source=]` (5),
`[=function object=]` (2), `[=platform object=]` (1), `[=new=]` (3),
`[=this=]` (19).
*Record as:* **externals** in `census/webidl/externals.tsv`
(`ext.html.queue-a-task`, `ext.webidl.realm`, …). All but `[=Queue a
microtask=]` occur only in the example subsection or in the exception-creation
algorithms' realm selection. `[=Queue a microtask=]` is the one that matters:
it is step 6.1 of `wait for all`, so the ordering claim about `wait for all`
depends on it. Flag it separately.

**Group C — Web IDL's own type system and binding, outside the five sections.**
`[=interface=]` (6), `[=interfaces=]` (2), `[=interface type=]`/`types` (3),
`[=interface/inherit(s|ing)=]` (3), `[=identifier=]` (4), `[=attribute(s)=]` (2),
`[=operation=]` (5), `[=constructor operation=]` (3), `[=dictionary=]` (1),
`[=optional argument=]` (1), `[=read only=]` (1), `[=return type=]` (1),
`[=sequence=]` (2), `[=IDL fragment=]` (1),
`[=converted to an IDL value=]` (3), `[=converted to a JavaScript value=]` (5),
`[=create an interface prototype object=]` (1),
`[=interface prototype object=]` (1), `{{any}}` (2), `{{DOMString}}` (1),
`{{undefined}}` (3).
*Record as:* **dependency rows onto out-of-scope sections of the same pinned
source**, with disposition `hostOnly`. They stay inside `vendor/whatwg-webidl-a652053f/index.bs`
but outside the census's section scope, so a `dependencies.tsv` entry naming
the target heading id is the honest record; promoting them to census rows would
open the whole 695 KB file.

**Group D — Infra.** `[=list=]` (4), `[=list/Append=]` (1),
`[=list/For each=]` (2), `[=list/size=]` (1), `[=strings=]` (1),
`[=implementation-defined=]` (3).
*Record as:* **dependency rows onto the existing Infra census**, by Infra row
id. Every one of these already has a row in `generated/infra-census.tsv`
(`op.implementation-defined` is there under that exact id), so this group needs
no new external identity — it is the first real cross-census join in the
repository and should be spelled as such.

**Group E — HTML.** `[=serializable objects=]` (3), `[=serialization steps=]`
(4), `[=deserialization steps=]` (4), `[=Queue a task=]`/`[=Queue a microtask=]`
(also Group B), `{{Window/unhandledrejection}}` (1),
`{{WindowOrWorkerGlobalScope/fetch()}}` (1), `{{Response}}` (1).
*Record as:* **externals** with an explicit note that the HTML pin exists in
`SPEC-MANIFEST.md` but has no census, so these cannot become dependency rows
yet. The structured-clone hooks appear only on `DOMException` and
`QuotaExceededError`, both `hostOnly`, so nothing `owned` depends on them.

**Group F — DOM.** `[=/document=]` (1), `[=/element=]` (1), `[=node=]` (1),
`[=node tree=]` (1). All four occur inside the error-names table's descriptive
prose (`HierarchyRequestError`, `WrongDocumentError`, `NotFoundError`).
*Record as:* **externals**; they are descriptions of when a name is used, not
operations the model invokes.

**Group G — a back-reference into Streams.**
`{{WritableStreamDefaultWriter/closed}}` (1), in the note beside
`mark as handled`.
*Record as:* nothing. It is a note naming a motivating case; recording it as a
dependency would invert the layering DB-11 fixes.

## 6. Risks and open decisions for the coordinator

**6.1 The Streams mode cannot be reused without touching a Streams-critical
function.** `scanRequirements` is hard-wired to the `ReadableStreamPipeTo`
marker and runs unconditionally in the non-definition-keyed branch. Gating it
on a new `requirementMarker` field is a two-line change, but it sits on the
path that produces the seven Streams `requirement` rows, and the P7 work
depends on those. The breaker contract should include a regression that the
Streams census is byte-identical after the change, not only that the Web IDL
census is produced.

**6.2 Is `idl-promise` `owned` or `hostOnly`?** `promise type` is a Web IDL
*type-system* entry, and the manifest's standing rule puts the type system and
its conversions in the binding layer. But it is also the carrier the eleven
`owned` operations range over, and 21 Streams IDL declarations use it. Ruling it
`hostOnly` would leave the eleven operations `owned` over a type with no row.
Recommendation: `owned`, with the conversions in the `js-promise` lead
`hostOnly`. Needs ratification.

**6.3 `mark as handled` has zero Streams consumers at this pin.** Ruling it
`owned` puts a row in the denominator that nothing in this repository will make
green for the foreseeable future; ruling it `evidenceOnly` keeps the
denominator honest but contradicts DB-11, which names the operation explicitly.
The same question applies with less force to `wait for all`, which at least has
one indirect consumer. Needs ratification.

**6.4 The six derived-interface requirement bullets have no separable span.**
They sit in one blank-line-delimited paragraph, so the existing `scanRules`
locator-to-blank-line rule gives six nested spans ending at the same offset.
Three options: accept the nesting; author one `rule` row for the whole list
(losing per-bullet granularity that the piping precedent has); or add an
authored end locator to the `rules.tsv` format, which changes an input format
two censuses already use. Decision needed before the breaker freezes the input
interface.

**6.5 The four duplicate ids are a naming-policy question, not a bug to patch
locally.** `DOMException`'s associated `name` and its `name` attribute getter
are genuinely two different things with the same Bikeshed name and the same
`for`. Whatever rule resolves them (this survey proposes keying the row kind off
the Bikeshed dfn type) also decides whether the attribute-getter *steps* get a
row of their own or are folded into the `idl` row from the `<pre class=idl>`
block. Under the folding option the getter steps in `idl-DOMException` have no
anchored span at all, which weakens any later claim about them. Under the
separate-row option, `idl.domexception-name` from the dfn collides with
`idl.domexception-name` from the IDL statement and a third rule is needed.
Decide before the extension is written.

**6.6 Three definitions in scope have no `<dfn>` tag.** `Promise` (the interface
type), "exception objects", and `DOMException` (the interface) are defined by
their headings' `interface`/`dfn` attributes. A `<dfn`-keyed scanner misses all
three. Either extend the definition scanner to read heading-borne definitions
(a real parser change, byte-neutral for Streams and Infra, which use neither
form) or accept that the census has no row for the `DOMException` interface
itself while having 30 rows for its members.

**6.7 `scanSlots` should be off, and that is a policy statement.** All 47 slot
rows it would produce anchor at incidental use sites, not definitions, and 38 of
them are JavaScript-binding object-model internals with no bearing on this lane.
Turning the scanner off for this standard means the census silently carries no
row for `[[PromiseIsHandled]]`, which is the single ECMA-262 slot the promise
operations write. Recommendation: turn `scanSlots` off and record
`[[PromiseIsHandled]]`, `[[Promise]]`, `[[Resolve]]` and `[[Reject]]` as
dependency rows into `Whatwg.Ecma262` instead, where they belong under DB-11.

**6.8 Scope filtering must be inside the scanners, not after them.** The
QuotaExceededError IDL block raises `unrecognised IDL header` and the
DOMException block silently skips 30 statements; both are *inside* the scope, so
they must be fixed. But the ten out-of-scope `<pre class="idl">` blocks would
also be parsed if the scanner runs file-wide and the filter is applied to rows,
and any error they raise aborts the run for reasons that have nothing to do with
this lane. The section scope has to be a predicate the scanners consult, which
makes the diff larger than a post-filter.

**6.9 Bikeshed autolinks wrap across lines.** A single-line regex undercounts
the two most-used operations by 12 invocations (`a promise resolved with` 45
→ 46, `a promise rejected with` 34 → 46) and gives 1,468 autolinks in the
Streams source where there are 2,188. Any later tooling that joins Streams
usage to Web IDL definitions must normalise whitespace inside `[=…=]`. This is
recorded so the number is not silently re-derived wrong.

**6.10 `Whatwg/WebIdl/Promise.lean`'s docstring is wrong at this pin.** It
reserves "the rule that a rejected promise passed to an algorithm is a
'handled' promise". No such rule exists in
`vendor/whatwg-webidl-a652053f/index.bs`; the only `[[PromiseIsHandled]]`
mention is inside `mark as handled`. Correct the stub or source the rule
elsewhere before the first packet cites it.

**6.11 Opening the lane has bookkeeping this pass deliberately did not do.**
`SPEC-MANIFEST.md` currently records the Web IDL pin with "no census or
dispositions yet"; `docs/SPEC-COVERAGE.md`'s scope note names Streams, Infra
and URL only; `census/README.md` describes three authored inputs for two
standards; `docs/research/README.md` asks that its index table be updated in
the same change as a new research document. Each is an authored router owned by
someone else, and none was touched. The coordinator must sequence those edits
with the generator change so that no two files claim the same fact.

**6.12 The scoped census is 118 rows against a 695,845-byte source, 7.81 % of
which is in scope.** The section whitelist is doing almost all of the work of
keeping this lane small. If the whitelist is ever widened — to the conversions,
say — the generator changes in §2.3(c) and (d) alone bring in 45 more algorithm
blocks and roughly 293 more definitions, and the Infra-mode span defect (§2.2)
becomes load-bearing rather than academic. The whitelist should be treated as
part of the frozen contract, not as a convenience.
