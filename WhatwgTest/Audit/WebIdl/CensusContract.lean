import Lean
import Gates

/-!
# Web IDL promise and exception census contract battery

Breaker-owned and frozen before implementation. Packet:
`test/contracts/webidl-census.contract.md`, which is the authority on every
number below and on the meaning of every name this file ascribes.

This battery is a tooling contract. It asserts no Web IDL semantics, no
observation mask, no coverage state and no denominator claim: a census row is
a byte span of the pinned source with a joined disposition, nothing more.

Two red causes are expected before the builder lands the lane, and no other
error class:

1. the names ascribed in sections 1 and 2 do not exist
   (`Gates.Census.Bikeshed` and its switches, `Gates.Census.Profile`,
   `Gates.Census.Standard.profile` and the three new authored-input paths,
   `Gates.Census.webidl`, `Gates.Census.RuleInput.endLocator`); and
2. `Gates.Census.Standard.ofKey? "webidl"` is `none`, so the projection gate
   in section 4 refuses before it can look at a file.

The frozen row table in section 3 was recomputed from the sealed bytes of
`vendor/whatwg-webidl-a652053f/index.bs` with PowerShell
(`[IO.File]::ReadAllBytes`, ISO-8859-1 decode so that character index equals
byte offset, `System.Security.Cryptography.SHA256`), independently of both
`Gates.Census` and the survey. The gate recomputes every digest with
`Gates.Sha256.hexDigest` over the pinned bytes.
-/

set_option autoImplicit false

namespace WhatwgTest.Audit.WebIdl.CensusContract

open Lean Elab Command

/-! ## 1. The source profile

Ruling R-P1 replaces `Gates.Census.Standard.definitionKeyed : Bool` with a
source profile. `Bikeshed` carries the per-scanner switches; `Profile` chooses
between the Bikeshed scanners and the ecmarkup scanner of `Gates/Ecmarkup.lean`.

- `algorithmRows`   emit one `op` row per `<div>` carrying an `algorithm`
                    attribute anywhere in its tag.
- `definitionRows`  emit one row per Bikeshed definition, `<dfn>` or
                    heading-borne.
- `idlRows`         emit one `idl` row per statement of an IDL block.
- `slotRows`        emit one `slot` row per qualified `[[Name]]`.
- `requirementMarker` the algorithm-block locator `scanRequirements` keys on;
                    `none` emits no requirement rows at all.
- `sectionScope`    restrict rows to the heading ids authored in
                    `<authoredDir>/sections.tsv`; `false` is the whole document.
- `headingLevels`   the inclusive heading-level range `scanHeadings` admits.
- `idlOpeners`      the (opening tag, closing tag) pairs of an IDL block.
-/

#check (@Gates.Census.Bikeshed : Type)
#check (@Gates.Census.Bikeshed.mk :
  Bool → Bool → Bool → Bool → Option String → Bool → Nat × Nat →
    Array (String × String) → Gates.Census.Bikeshed)
#check (@Gates.Census.Bikeshed.algorithmRows : Gates.Census.Bikeshed → Bool)
#check (@Gates.Census.Bikeshed.definitionRows : Gates.Census.Bikeshed → Bool)
#check (@Gates.Census.Bikeshed.idlRows : Gates.Census.Bikeshed → Bool)
#check (@Gates.Census.Bikeshed.slotRows : Gates.Census.Bikeshed → Bool)
#check (@Gates.Census.Bikeshed.requirementMarker : Gates.Census.Bikeshed → Option String)
#check (@Gates.Census.Bikeshed.sectionScope : Gates.Census.Bikeshed → Bool)
#check (@Gates.Census.Bikeshed.headingLevels : Gates.Census.Bikeshed → Nat × Nat)
#check (@Gates.Census.Bikeshed.idlOpeners : Gates.Census.Bikeshed → Array (String × String))

#check (@Gates.Census.Profile : Type)
#check (@Gates.Census.Profile.bikeshed : Gates.Census.Bikeshed → Gates.Census.Profile)
#check (Gates.Census.Profile.ecmarkup : Gates.Census.Profile)

#check (@Gates.Census.Standard.profile : Gates.Census.Standard → Gates.Census.Profile)
#check (@Gates.Census.Standard.sectionsRelativePath : Gates.Census.Standard → String)
#check (@Gates.Census.Standard.dependenciesRelativePath : Gates.Census.Standard → String)
#check (@Gates.Census.Standard.externalsRelativePath : Gates.Census.Standard → String)

/-! ### The optional end locator of `rules.tsv`

Ruling R-P4: `rules.tsv` gains a third, optional field. With two fields the
span runs from the locator to the next blank line, exactly as it does today;
with three, it runs to the first occurrence of the end locator at or after the
start locator, with trailing ASCII whitespace trimmed. Both `census/rules.tsv`
and `census/infra/rules.tsv` are entry-free at this pin and both projections
carry zero `rule` rows, so the extension is byte-neutral for them. -/

#check (@Gates.Census.RuleInput.mk : String → String → Option String → Gates.Census.RuleInput)
#check (@Gates.Census.RuleInput.name : Gates.Census.RuleInput → String)
#check (@Gates.Census.RuleInput.locator : Gates.Census.RuleInput → String)
#check (@Gates.Census.RuleInput.endLocator : Gates.Census.RuleInput → Option String)
#check (@Gates.Census.parseRules :
  String → String → Except String (Array Gates.Census.RuleInput))
#check (@Gates.Census.scanRules :
  ByteArray → Array Gates.Census.RuleInput → Except String (Array Gates.Census.Row))

private def parsedRules (text : String) : Option (Array Gates.Census.RuleInput) :=
  (Gates.Census.parseRules text "census/webidl/rules.tsv").toOption

-- WEBIDL-CEN-P01: two fields keep today's meaning; three carry the end locator.
#guard (match parsedRules "alpha\tSTART\n" with
        | some rules =>
          rules.size == 1 && (rules.getD 0 default).name == "alpha" &&
            (rules.getD 0 default).locator == "START" &&
            (rules.getD 0 default).endLocator == none
        | none => false)
#guard (match parsedRules "alpha\tSTART\tEND\n" with
        | some rules =>
          rules.size == 1 && (rules.getD 0 default).name == "alpha" &&
            (rules.getD 0 default).locator == "START" &&
            (rules.getD 0 default).endLocator == some "END"
        | none => false)
#guard (parsedRules "alpha\tSTART\tEND\tEXTRA\n").isNone
#guard (parsedRules "alpha\tSTART\t\n").isNone
#guard (parsedRules "\tSTART\tEND\n").isNone

-- WEBIDL-CEN-P02: the end locator bounds the span; trailing whitespace is trimmed.
private def ruleFixture : String := "AAA head\nmiddle\nBBB tail\n\nafter"

private def scannedRules (text : String) (rules : Array Gates.Census.RuleInput) :
    Option (Array Gates.Census.Row) :=
  (Gates.Census.scanRules text.toUTF8 rules).toOption

#guard (match scannedRules ruleFixture #[⟨"one", "AAA", some "BBB"⟩] with
        | some rows =>
          rows.size == 1 && (rows.getD 0 default).id == "rule.one" &&
            (rows.getD 0 default).spanB == 0 && (rows.getD 0 default).spanE == 15
        | none => false)
#guard (match scannedRules ruleFixture #[⟨"one", "AAA", none⟩] with
        | some rows =>
          rows.size == 1 && (rows.getD 0 default).spanB == 0 &&
            (rows.getD 0 default).spanE == 24
        | none => false)
-- An end locator that never occurs after the start locator is refused, never
-- silently widened to the blank-line rule.
#guard (scannedRules ruleFixture #[⟨"one", "BBB", some "AAA"⟩]).isNone
#guard (scannedRules ruleFixture #[⟨"one", "AAA", some "ZZZ"⟩]).isNone
-- A start locator that is not unique is refused, exactly as it is today.
#guard (scannedRules "AAA\nAAA\n\n" #[⟨"one", "AAA", none⟩]).isNone

/-! ## 2. The `webidl` standard -/

#check (@Gates.Census.webidl : Gates.Census.Standard)

#guard Gates.Census.webidl.key == "webidl"
#guard Gates.Census.webidl.label == "WHATWG Web IDL (a652053f)"
#guard Gates.Census.webidl.inputRelativePath == "vendor/whatwg-webidl-a652053f/index.bs"
#guard Gates.Census.webidl.inputDigest ==
  "3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83"
#guard Gates.Census.webidl.censusRelativePath == "generated/webidl-census.tsv"
#guard Gates.Census.webidl.rowsRelativePath == "WhatwgTest/Audit/WebIdl/SpecCoverageRows.lean"
#guard Gates.Census.webidl.rowsNamespace == "WhatwgTest.Audit.WebIdl.SpecCoverageRows"
#guard Gates.Census.webidl.authoredDir == "census/webidl"
#guard Gates.Census.webidl.regenerateCommand == "lake exe census --standard webidl --write"
#guard Gates.Census.webidl.sectionsRelativePath == "census/webidl/sections.tsv"
#guard Gates.Census.webidl.dependenciesRelativePath == "census/webidl/dependencies.tsv"
#guard Gates.Census.webidl.externalsRelativePath == "census/webidl/externals.tsv"
#guard (Gates.Census.Standard.ofKey? "webidl").isSome

#guard (match Gates.Census.webidl.profile with
        | .bikeshed switches =>
          switches.algorithmRows == true &&
            switches.definitionRows == true &&
            switches.idlRows == true &&
            switches.slotRows == false &&
            switches.requirementMarker == none &&
            switches.sectionScope == true &&
            switches.headingLevels == (2, 5) &&
            switches.idlOpeners ==
              #[("<pre class=\"idl\">", "</pre>"), ("<pre class=idl>", "</pre>")]
        | .ecmarkup => false)

/-! ## 3. The frozen census

Every row of `generated/webidl-census.tsv`: its kind, its id, the half-open
byte interval of its span in the pinned source, the byte length of the anchor
`Gates.Census.chooseAnchorLength` selects for that span, and the SHA-256 of
the span. -/

private structure Frozen where
  kind : String
  id : String
  spanB : Nat
  spanE : Nat
  anchorLen : Nat
  digest : String
  deriving Inhabited

private def frozenRows : Array Frozen := #[
  ⟨"idl", "idl.dom-exception", 673588, 673639, 24, "4e9332bb7e47cf957a9ff8fcfeb1fdd42d6a8a93b2b9227765d29e6c1f7f2e9e"⟩,
  ⟨"idl", "idl.domexception-abort-err", 674776, 674812, 24, "180a37fcd9ce24e6d0f515e38b8b3987ceed6d97e26869a3cb2212c1ac75f172"⟩,
  ⟨"idl", "idl.domexception-code", 673849, 673888, 48, "19315c8e4e4c657557461099d25f86f0a7ec9650d040b40d3b4581ae36d2739d"⟩,
  ⟨"idl", "idl.domexception-constructor", 673689, 673769, 64, "49d172735ba63a076fc928ac085343af36cdd1a6ac2a52c054de2d816e5aa8eb"⟩,
  ⟨"idl", "idl.domexception-data-clone-err", 675001, 675042, 24, "740e593d32f8901e25cdc3e6d978bb67272c65de1868a0396cd341c65db93872"⟩,
  ⟨"idl", "idl.domexception-domstring-size-err", 673935, 673979, 24, "98ccc4904605695d859a7cc591cb2bad479187313056884a0920a41b534f56ea"⟩,
  ⟨"idl", "idl.domexception-hierarchy-request-err", 673982, 674029, 24, "e2cbabfefeeafbe86b317692ed8687af27c48dd8844c32771a9d1d1d224199db"⟩,
  ⟨"idl", "idl.domexception-index-size-err", 673892, 673932, 24, "133bbbb3c421027af025736b6212d27076227710f988c9c5d7b0546d1ae9d32b"⟩,
  ⟨"idl", "idl.domexception-inuse-attribute-err", 674321, 674367, 24, "fb243755c7c3c3fcc11d888843c2256e30af6885596d46d4f2c3e79ccd655c19"⟩,
  ⟨"idl", "idl.domexception-invalid-access-err", 674554, 674599, 32, "21164016f5e04ec857f2b3b486fb23ef06b86fd86f90e612af1025673857f8d2"⟩,
  ⟨"idl", "idl.domexception-invalid-character-err", 674079, 674126, 32, "cea85d0cb5514da5e97e857c053cec173ec3aa9e50ebd033617f432700045b5d"⟩,
  ⟨"idl", "idl.domexception-invalid-modification-err", 674457, 674508, 32, "af7f4f553f8fce7279534ed78e365a89cbf2affecfd1e9ac1ba83b40e7379007"⟩,
  ⟨"idl", "idl.domexception-invalid-node-type-err", 674950, 674998, 32, "091646b6151b0dd2470323b442186140a17f2d809a388c805f937b5e97fa0686"⟩,
  ⟨"idl", "idl.domexception-invalid-state-err", 674370, 674414, 32, "cc06444ebabf8d34bf3c917f510cc92646b4e729bf2d8106f8140fb096184b3e"⟩,
  ⟨"idl", "idl.domexception-message", 673809, 673846, 32, "06bc68820b3b8af473c2c0d0bfe9328441f524ca261be6a85bebadece9f1de9b"⟩,
  ⟨"idl", "idl.domexception-name", 673772, 673806, 48, "cdf794c2d44a1dfe2a6821c33397454e0bb260c41490873433e4e40246e2d1b7"⟩,
  ⟨"idl", "idl.domexception-namespace-err", 674511, 674551, 24, "27e146b180ea0d8687b3d7516cd89eae8c844063d069f984b0a495f5ce2e4edc"⟩,
  ⟨"idl", "idl.domexception-network-err", 674735, 674773, 24, "e5e19c055273f8b6d4c1ba8558477b13d92ea22e8f2f567dce64a66ba9fd89b7"⟩,
  ⟨"idl", "idl.domexception-no-data-allowed-err", 674129, 674174, 32, "48bc28c5b781e86a43ec6ff8c184eb774a55a49bf73634967ab293c84ef4dbc1"⟩,
  ⟨"idl", "idl.domexception-no-modification-allowed-err", 674177, 674230, 32, "d6ff442ef60633d8420cb074a11bdc30c49b4adfe1fd1def8786699e276d14c4"⟩,
  ⟨"idl", "idl.domexception-not-found-err", 674233, 674272, 32, "be946dd8e85954ab10fde83cb01b079bd50dbf48ebc10c4c2c320f34e1e43067"⟩,
  ⟨"idl", "idl.domexception-not-supported-err", 674275, 674318, 32, "cc6b8d89ddb057b9c1500629748ba16769af4b2e2085738e211295611bd33d3b"⟩,
  ⟨"idl", "idl.domexception-quota-exceeded-err", 674861, 674906, 24, "b42e6d43c7b2f20d051499fb83849d71a4f1e6af3a6d1497b97490ea2aea5fcc"⟩,
  ⟨"idl", "idl.domexception-security-err", 674693, 674732, 24, "60d9210cc3fcd70c71edbe17c0a632b3bf7d088e42b5a394b94645bf14d4387d"⟩,
  ⟨"idl", "idl.domexception-syntax-err", 674417, 674454, 24, "a5c8a5c025e197f311f9c7f19d6b43b4427baba7aeb43ab4a04309e49ebcd0be"⟩,
  ⟨"idl", "idl.domexception-timeout-err", 674909, 674947, 24, "40d0c8ec21f4420c2e7c30db23f84fb313e811fc2f9660e72a72f8d4d124a2fa"⟩,
  ⟨"idl", "idl.domexception-type-mismatch-err", 674646, 674690, 24, "b0895a121349c365285cc3d9633d4b9baa561c696701506099f7c349fdd347f1"⟩,
  ⟨"idl", "idl.domexception-url-mismatch-err", 674815, 674858, 24, "b6cd3a45dbe17c39b6af91cea88620bcc411d566b180e54908047b7c5f1a42fb"⟩,
  ⟨"idl", "idl.domexception-validation-err", 674602, 674643, 24, "2f83b8cef33249cc3ba05e3e6a58abeb5fe440f63fbbef96686d5b84b4202ef0"⟩,
  ⟨"idl", "idl.domexception-wrong-document-err", 674032, 674076, 24, "a7ef7c9458a97fcee6e6787218799723e9f808d1fefff01db29411702f90e5e2"⟩,
  ⟨"idl", "idl.quota-exceeded-error", 213527, 213598, 24, "e27a117ef91d587eb017ada33f4c1a2e200be5272395d9890455355b90fbecd2"⟩,
  ⟨"idl", "idl.quota-exceeded-error-options", 213777, 213815, 24, "b641b4d494d106b025a3cd95eeb543a1d233588e5b7413645cf9e8af30d9c27d"⟩,
  ⟨"idl", "idl.quotaexceedederror-constructor", 213601, 213695, 64, "b09449cf5e0157f7876a617e91d67ca96e75c66d8cf6dd662c6c0d478d304ee2"⟩,
  ⟨"idl", "idl.quotaexceedederror-quota", 213699, 213732, 32, "971545ce535cf3c8a6dc69a5f292f0f49fb1030218fb0d1d7f7d2e61afaa2f2d"⟩,
  ⟨"idl", "idl.quotaexceedederror-requested", 213735, 213772, 32, "e590defe8544439fb751e5a92b0c8beedba417e7dbc1767163140deafb4c9911"⟩,
  ⟨"idl", "idl.quotaexceedederroroptions-quota", 213818, 213831, 24, "e5cada2860e8ecd3720a5c003e2607f96b89e8ccd1f4dc19c077c4bac266fef8"⟩,
  ⟨"idl", "idl.quotaexceedederroroptions-requested", 213834, 213851, 24, "c5a302d1c3172aacff4d8697b72f642c3849d26563eff76ce7ff27c970ffb743"⟩,
  ⟨"op", "op.a-new-promise", 347604, 347946, 48, "a9c212f9448d6cfdaf262e33f33ed5104392aaec738b6e3ae22b285edc3751b3"⟩,
  ⟨"op", "op.a-promise-rejected-with", 348633, 349214, 64, "3f6d84e5da374f56e56aebba956939b54dbefb219a67137a37128ecce58f20f8"⟩,
  ⟨"op", "op.a-promise-resolved-with", 347948, 348631, 64, "a5b86f19962066ef9844df3f2ee2494cb78c74bae6cf6690cc8ee1b6e0b60015"⟩,
  ⟨"op", "op.add-bookmark", 362329, 363490, 24, "c7999583a7b35262fcd27f7b4139b94ae17fd9ab73bdbed47131d590e3c4614c"⟩,
  ⟨"op", "op.add-delay", 359201, 360103, 24, "c41832d6488f46c5e6e135f0a2118c1fef90c39180900ffff10d3898fc88e182"⟩,
  ⟨"op", "op.an-exception-was-thrown", 669437, 669665, 24, "a705b8c63991bc538c2c97e6aa1a5ef66360e8e37f5e9a6bb1dc44544859efa6"⟩,
  ⟨"op", "op.batch-request", 364131, 364580, 24, "13713a763dcfd6681cbac28d539dcbc0c003751446261d83c3b97f5f48d50482"⟩,
  ⟨"op", "op.delay", 357180, 357688, 24, "947b495ff64d4df797af63cc0252de4e696f7289b059114ae173f642737b9392"⟩,
  ⟨"op", "op.dfn-create-exception", 195867, 196437, 24, "f532faf75bb38516470dfa36637d8c495ff494a8188ae96a5e55a3aa8181e041"⟩,
  ⟨"op", "op.dfn-error-names-table", 198659, 198938, 24, "41f19f926ee8be134bc10020ccd4f95b505991f165245143bb965fc9f44775bd"⟩,
  ⟨"op", "op.dfn-exception", 193998, 194431, 24, "a727aa273727aa630983e9f4f49a017ca2c9c421bdfacd3bea03a45fe964a980"⟩,
  ⟨"op", "op.dfn-perform-steps-once-promise-is-settled", 350075, 352408, 48, "dd0e08ae5b8739280837b31e10f2ace6f1a7f9b20034124d7c748d450aaab383"⟩,
  ⟨"op", "op.dfn-promise-type", 252271, 252705, 24, "517973beeca92afcddbb3ebc38522fd1f95c964706b3e0183dcbaa6e4835bfb5"⟩,
  ⟨"op", "op.dfn-simple-exception", 194433, 194721, 24, "23597069802c1cb8d6b73ddb94125c7fed97b65815cf8e7bf7b3cdd69e1041d3"⟩,
  ⟨"op", "op.dfn-throw", 195867, 196437, 24, "f532faf75bb38516470dfa36637d8c495ff494a8188ae96a5e55a3aa8181e041"⟩,
  ⟨"op", "op.dom-exception-message", 675214, 675370, 24, "5d36b1e822347566aae87eafaa4d0125413f13f8aaab8f2c05c28c163fb71de3"⟩,
  ⟨"op", "op.dom-exception-name", 675214, 675370, 24, "5d36b1e822347566aae87eafaa4d0125413f13f8aaab8f2c05c28c163fb71de3"⟩,
  ⟨"op", "op.environment-create", 360876, 361777, 32, "931feca212ae287d25ad348a8da9ff9c314c20cb6a3810963ea83bb0718e11e2"⟩,
  ⟨"op", "op.environment-ready", 360719, 360874, 32, "b36bfad03aec0c8fddaa59eb6567d025b7a049e88b727b19fa8b86eacf451fa5"⟩,
  ⟨"op", "op.environment-ready-promise", 360535, 360717, 24, "8f86f770f6d88675276f175fb5522403170a92290f8ee5449574ef36403a35d8"⟩,
  ⟨"op", "op.js-exception-objects", 664320, 664406, 24, "036d4e370d6f4dc68f7266889421e196ca709b894fc8ae9cfd293ae9eac124e4"⟩,
  ⟨"op", "op.js-to-promise", 346692, 347209, 24, "c42584ffe744b7ecb64aee1920b52123a79024aa81ad1ed268f34351cc87158b"⟩,
  ⟨"op", "op.mark-a-promise-as-handled", 356060, 356713, 48, "644263e9155cf45d31167e53346f9d0e2431aedde301b440dbc92d9021b618bc"⟩,
  ⟨"op", "op.quota-exceeded-error-deserialization-steps", 216862, 217258, 48, "b595923cd7a3d7ea789812018fe48c8ba464eb3109215a72a4adbf632a691a7a"⟩,
  ⟨"op", "op.quota-exceeded-error-quota", 214367, 214571, 24, "99018d0b0b70c2b17fc53c8caa1f7d47ee092af97989b516aab48f2aed681b3d"⟩,
  ⟨"op", "op.quota-exceeded-error-requested", 214367, 214571, 24, "99018d0b0b70c2b17fc53c8caa1f7d47ee092af97989b516aab48f2aed681b3d"⟩,
  ⟨"op", "op.quota-exceeded-error-serialization-steps", 216470, 216860, 48, "1bdcd05ecca0b4517b231b35aadfec823e7a0c3dc24d53945b5e4b370761edbe"⟩,
  ⟨"op", "op.quotaexceedederror-quota-exceeded-error-message-options", 214573, 215831, 32, "058bb10014d24c4dcfb77050f02193ce07f8ef6dbba643d103df8c5977b83ffc"⟩,
  ⟨"op", "op.reject", 349785, 350073, 48, "c2edaaba6c2c29a161365819f857be96eabcf9ee573580a4687e8eec72a900ea"⟩,
  ⟨"op", "op.resolve", 349216, 349783, 48, "071c11c45c5c1da04b86837e7911385b64880eaf3a013ff769676110af545cc3"⟩,
  ⟨"op", "op.throw-an-exception", 667326, 667543, 24, "eef218df5d89e680179c4fd287dc583ed2f32c627bb99c514f7e7b7c0e5b54b7"⟩,
  ⟨"op", "op.to-create-a-dom-exception", 665488, 666331, 48, "9c9e8e3900f31454289e363c04d9cb3d534bc9723d7e4864788e2558acf1b54f"⟩,
  ⟨"op", "op.to-create-a-dom-exception-derived-interface", 666333, 667324, 48, "ff0eedd3a45de5b085e69a570d46272ca1b9d60d1ca4b471f7561708bfc2f710"⟩,
  ⟨"op", "op.to-create-a-simple-exception", 664734, 665486, 32, "a685c4154d0f603eb41dfcc0b4cafcb2ffcfc201d1519963d63a1008d36351de"⟩,
  ⟨"op", "op.upon-fulfillment", 352410, 352816, 64, "81ccd0a141715f38ae30f05c97a994c4ea3fef748c6301da8f3b8e4c6c785b9d"⟩,
  ⟨"op", "op.upon-rejection", 352818, 353237, 64, "f1e47b988febfd3652dac64ddb390db465d96a07f5b2d939cd8c62413221e7e9"⟩,
  ⟨"op", "op.validated-delay", 358205, 358816, 24, "520648ac6758cb1bfe8aaf7b54d209872c5e428255c266f01a32940cdc503b3d"⟩,
  ⟨"op", "op.wait-for-all", 353239, 354879, 48, "518fae182417ff76e800ed67df039a512d35b6af29ee11251b684172e703d930"⟩,
  ⟨"op", "op.waiting-for-all-promise", 354881, 356058, 24, "e8e29da9e357ce2532fe7acb9b978139f217f5dbc83db043cc2f7ffeacb605b3"⟩,
  ⟨"rule", "rule.domexception-derived-attributes", 212319, 212507, 24, "b6f0959816c25a86e3190fa116bce101193b052dc473bfa9f5d6ef859101aedc"⟩,
  ⟨"rule", "rule.domexception-derived-constructor-message", 211922, 212161, 48, "8c76ad3f87e6e38bf899921555982b993526392959c49443fe804978f81d5496"⟩,
  ⟨"rule", "rule.domexception-derived-constructor-name", 211775, 211921, 24, "725cee27de08373b9d2f6a91a8e50ed462e030e2924bf2d858d7539fa006be16"⟩,
  ⟨"rule", "rule.domexception-derived-constructor-options", 212162, 212318, 48, "b22c520f07b64ef41cc104c1506b06f289461dc1abcf6b1f636f55780a610000"⟩,
  ⟨"rule", "rule.domexception-derived-identifier", 211607, 211774, 24, "f624781f6a7b62a5daa3deb6805a683e9fdd76d9d033ce6867726b8e0ee24564"⟩,
  ⟨"rule", "rule.domexception-derived-serializable", 212508, 212653, 24, "f29b16284e3c090804206588df17445b408eb0e821feb9b190b84acf4fcbbc84"⟩,
  ⟨"type", "type.aborterror", 206394, 206680, 32, "18920890af5a1bb435cd9d7215ef532f9c599e4400f56e012cf25da6b84ced66"⟩,
  ⟨"type", "type.constrainterror", 209105, 209369, 32, "2bbb3bd78064f6f703f29e3439dc75f4c25d15a9584a888621b890cc69c0ae7f"⟩,
  ⟨"type", "type.datacloneerror", 208109, 208416, 48, "f4989a2f14bed893723de1a9c1bcd2f037d933bf07a5811d7ae37beae18fe49b"⟩,
  ⟨"type", "type.dataerror", 209378, 209560, 48, "1250a40d36b944ce09519ab3baab26b848091322ec10d322f89ce6e62c25cbc9"⟩,
  ⟨"type", "type.encodingerror", 208425, 208646, 32, "09f5bb975f55e29abebae3e9d7d9ba514d815a0b707a0ee158e1252ceef52a47"⟩,
  ⟨"type", "type.eval-error", 194542, 194576, 24, "fe52f6d4a2d0a88af703f2350adddf91c27a6ee76cd229324b54724bed0c93d8"⟩,
  ⟨"type", "type.hierarchyrequesterror", 200957, 201323, 32, "47148ba23577331f23085583db568390eb676e1e5da0eb0dbf217cf232ab2403"⟩,
  ⟨"type", "type.idl-dom-exception", 673398, 673477, 24, "0d75c2304dcc564dd7e4199120d80adc2f23dc2b033b78ac174ec19dae5d82d6"⟩,
  ⟨"type", "type.idl-promise", 252146, 252269, 24, "fa4cada5568a7371132cec82e9632293dd79e663dbc121e0c6deb0639316e334"⟩,
  ⟨"type", "type.indexsizeerror", 200596, 200948, 64, "a78fab8f0aa76c8e861b409bfaedfecdfb45a4902dc41e9b0ea9dc7240a3b07c"⟩,
  ⟨"type", "type.inuseattributeerror", 203047, 203401, 48, "cdcb8259df8f08935d5de9972c8581d982824ce0b4f24c4e21366eb1eb587ad8"⟩,
  ⟨"type", "type.invalidaccesserror", 204794, 205410, 64, "36eb12e30a0a5172ff2e20ae8938f1857701721c16b3f5e6888c423dcbb5326a"⟩,
  ⟨"type", "type.invalidcharactererror", 201683, 202027, 48, "d6ee3a99130a2233697485719c8be7fee4206a6476e98643b7b93a496f0cbc48"⟩,
  ⟨"type", "type.invalidmodificationerror", 204062, 204423, 48, "39d4d1ebf79d34688ba197b09eba06ea7ce31202d870bcf887e333f6676fb800"⟩,
  ⟨"type", "type.invalidnodetypeerror", 207705, 208100, 48, "4f6c50936ec7d13da070d3b5d22443da1c1a12911d3c0b455ec06901be69f01c"⟩,
  ⟨"type", "type.invalidstateerror", 203410, 203734, 48, "37f9c581b7ef85e806642ab4359c5d2a8c178c985012e556c6899dd73a182110"⟩,
  ⟨"type", "type.namespaceerror", 204432, 204785, 48, "059c76bc893cbf7b23d449727a898649eadccfe1f68852c71a48c42a7b9bbec7"⟩,
  ⟨"type", "type.networkerror", 206092, 206385, 48, "5fd5052507c74a89ef7ada1bff51a85643377976b2b1c1a42cb5faf331170402"⟩,
  ⟨"type", "type.nomodificationallowederror", 202036, 202394, 48, "7caa02a5efd0af1a87df073e2efcda61958725d1c05581bde74dfb7d0c370783"⟩,
  ⟨"type", "type.notallowederror", 210618, 210913, 48, "f3382081f3f1551544d0eacad475a64b1c46eebd22c2eefbe7207f298022aa97"⟩,
  ⟨"type", "type.notfounderror", 202403, 202709, 48, "4c8d7c60abde59dba7d92a596a89935c0f34e6995706afdc7805354c9d1bed41"⟩,
  ⟨"type", "type.notreadableerror", 208655, 208853, 48, "cb8c86f88a824b41d9caffa5e0f4159a77b97757c710acd34fc0b2f7049ff2de"⟩,
  ⟨"type", "type.notsupportederror", 202718, 203038, 48, "7ef8b3a7417ef440e6cbb241c0a612d10fbad37ca6e276cdec84665a6fdba4eb"⟩,
  ⟨"type", "type.operationerror", 210391, 210609, 48, "63019aafdb8dd9cecc174c10c15e970a68e941b977868c4b4a851c9c4c037cca"⟩,
  ⟨"type", "type.optouterror", 210922, 211114, 48, "79525ead90cfbfd0d548f12b2d1abd9ddb13c0c6b9c053ba1a87e43f8d2b3eb5"⟩,
  ⟨"type", "type.range-error", 194577, 194612, 24, "d15db5c544b96a84193b54197019d13371c736db365c85dc348ad49e3a2b7311"⟩,
  ⟨"type", "type.readonlyerror", 209871, 210112, 32, "91d02708973dcf9c44bf5e4a8704880161e48e6705b0b57c2e2a8ff475b12a47"⟩,
  ⟨"type", "type.reference-error", 194613, 194652, 24, "25210a48ac8e4d513cb59d2f82798138187e0b03b2b89fc5091fa0e252ce5dc1"⟩,
  ⟨"type", "type.securityerror", 205785, 206083, 48, "59c3f7350f0655d8ae23f30ad8e7c00f16f241aa12fa2cc7dac8aa21c202305c"⟩,
  ⟨"type", "type.syntaxerror", 203743, 204053, 48, "a53db98ed19f851882b83ed576f99404c39648335b82da1e835a366753532e40"⟩,
  ⟨"type", "type.timeouterror", 207404, 207696, 48, "24af6447be4228aa7f4ab63f6d49380fdc1ca73399af82882cb91e0926e9ee6e"⟩,
  ⟨"type", "type.transactioninactiveerror", 209569, 209862, 48, "3e7b1fcf5ac3c2dfd5eb3d90b5ea49f9c9166db31fb9fec6219c24ea6ce0291d"⟩,
  ⟨"type", "type.type-error", 194653, 194687, 24, "d81310aea9f58cfc2aad57a69a92a8d6752ea011377684ff9859969ed5832c7f"⟩,
  ⟨"type", "type.typemismatcherror", 205419, 205776, 64, "0c1751de3cb145f9d78e5d1fffa55270a3a18456e32336b8db05f8aab7bc3999"⟩,
  ⟨"type", "type.unknownerror", 208862, 209096, 32, "b18781b2f65d78ec81babe2c219ebb8f4e965034333e33bf909f5665689eb2ab"⟩,
  ⟨"type", "type.uri-error", 194688, 194721, 24, "f7bf226ec77f3615c85f432c11ad4d0ae345c50a0dae119baa662f8a4a6ce0bf"⟩,
  ⟨"type", "type.urlmismatcherror", 206689, 207022, 64, "53910d07cfa4481ecde98f9aa78594b271e216a61c58e27a8a7ae7c9d127c3f5"⟩,
  ⟨"type", "type.versionerror", 210121, 210382, 32, "3457c1af6ec4f7e1eb224c85b8e3067cfe3469706bf9e5c5d014962e5ba0ef47"⟩,
  ⟨"type", "type.wrongdocumenterror", 201332, 201674, 32, "d590c3a636b3e789e16529a3e72f35e5a883eb2dca6b29260e93b513f01e503c"⟩
]

private def sourceRelativePath : String := "vendor/whatwg-webidl-a652053f/index.bs"

private def sourceDigest : String :=
  "3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83"

private def censusRelativePath : String := "generated/webidl-census.tsv"

private def rowsRelativePath : String := "WhatwgTest/Audit/WebIdl/SpecCoverageRows.lean"

private def regenerateCommand : String := "lake exe census --standard webidl --write"

-- Q2 amendment, `test/contracts/webidl-census-q2.contract.md`, 2026-09-07:
-- 121 -> 124. Debt D3 adds the two `rule` rows for DOMException's
-- serialization and deserialization steps, and debt D5 adds
-- `rule.promise-to-js`.
private def expectedRowTotal : Nat := 124

-- Q2 amendment, `test/contracts/webidl-census-q2.contract.md`, 2026-09-07:
-- 112 -> 116. The three new rows are all inside the denominator, and debt D4
-- moves `op.an-exception-was-thrown` into it.
private def expectedDenominator : Nat := 116

-- Q2 amendment, `test/contracts/webidl-census-q2.contract.md`, 2026-09-07:
-- `rows=121` -> `rows=124`, from the same three rows.
private def expectedHeader : String :=
  "#census format=1 generator=Gates.Census input=vendor/whatwg-webidl-a652053f/index.bs " ++
  "input-sha256=3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83 " ++
  "rows=124 regenerate=lake exe census --standard webidl --write"

-- Q2 amendment, `test/contracts/webidl-census-q2.contract.md`, 2026-09-07:
-- `rule` 6 -> 9. Every other kind is unchanged.
private def expectedKindCounts : List (String × Nat) :=
  [("idl", 37), ("op", 39), ("requirement", 0), ("rule", 9), ("slot", 0), ("type", 39),
   ("builtin", 0), ("hook", 0), ("property", 0), ("record", 0), ("field", 0),
   ("term", 0), ("clause", 0)]

-- Q2 amendment, `test/contracts/webidl-census-q2.contract.md`, 2026-09-07:
-- `owned` 59 -> 61 (the two D3 step rows, under a new `idl-DOMException rule
-- owned` line), `hostOnly` 47 -> 49 (`rule.promise-to-js` from D5 and
-- `op.an-exception-was-thrown` from D4), `evidenceOnly` 9 -> 8 (the same D4
-- row leaving). `requirement`, `foreignBoundary`, `refused` and `targetOnly`
-- are unchanged.
private def expectedDispositionCounts : List (String × Nat) :=
  [("owned", 61), ("hostOnly", 49), ("evidenceOnly", 8), ("requirement", 6),
   ("foreignBoundary", 0), ("refused", 0), ("targetOnly", 0)]

/-! ## 4. The projection gate -/

private def occurrencesOf (haystack needle : String) : Nat :=
  (haystack.splitOn needle).length - 1

open Elab Command in
elab "#webidl_census_contract_gate" : command => do
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "webidl census contract: source file has no parent directory"
  let projectRoot ← liftIO <| Gates.Common.findProjectRoot sourceDirectory
  let some standard := Gates.Census.Standard.ofKey? "webidl"
    | throwError "webidl census contract: no standard is registered under the key webidl; ruling R-P1 requires `lake exe census --standard webidl`"
  if standard.censusRelativePath != censusRelativePath then
    throwError "webidl census contract: the standard writes {standard.censusRelativePath}; the packet freezes {censusRelativePath}"
  let censusPath := projectRoot / censusRelativePath
  unless ← liftIO censusPath.pathExists do
    throwError "webidl census contract: missing {censusRelativePath}; run `{regenerateCommand}`"
  let sourcePath := projectRoot / sourceRelativePath
  unless ← liftIO sourcePath.pathExists do
    throwError "webidl census contract: missing the pinned source {sourceRelativePath}"
  let bytes ← liftIO <| IO.FS.readBinFile sourcePath
  let censusText ← liftIO <| IO.FS.readFile censusPath
  let allLines := Gates.Common.lines censusText
  let header := allLines.headD ""
  let dataLines := allLines.drop 1
  if header != expectedHeader then
    throwError "webidl census contract: the header line of {censusRelativePath} is not the frozen one"
  if dataLines.length != expectedRowTotal then
    throwError "webidl census contract: {censusRelativePath} carries {dataLines.length} rows; the packet freezes {expectedRowTotal}"
  let mut parsed : Array (Array String) := #[]
  let mut lineNumber : Nat := 1
  for line in dataLines do
    lineNumber := lineNumber + 1
    match Gates.Census.splitRow line with
    | .error message =>
      throwError "webidl census contract: line {lineNumber}: {message}"
    | .ok fields =>
      if fields.size != 7 then
        throwError "webidl census contract: line {lineNumber}: expected seven fields, found {fields.size}"
      let kindText := fields.getD 0 ""
      let rowId := fields.getD 1 ""
      match Gates.Census.Kind.ofString? kindText with
      | none => throwError "webidl census contract: line {lineNumber}: unknown kind {kindText}"
      | some kind =>
        unless rowId.startsWith (kind.name ++ ".") do
          throwError "webidl census contract: line {lineNumber}: row id {rowId} does not carry its own kind"
      parsed := parsed.push fields
  for i in [1:parsed.size] do
    let previous := (parsed.getD (i - 1) #[]).getD 0 "" ++ "|" ++ (parsed.getD (i - 1) #[]).getD 1 ""
    let current := (parsed.getD i #[]).getD 0 "" ++ "|" ++ (parsed.getD i #[]).getD 1 ""
    unless previous < current do
      throwError "webidl census contract: rows {i} and {i + 1} are not strictly increasing in kind then id ({previous}, {current})"
  for (kindName, expected) in expectedKindCounts do
    let observed := parsed.foldl (fun acc fields => if fields.getD 0 "" == kindName then acc + 1 else acc) 0
    unless observed == expected do
      throwError "webidl census contract: {censusRelativePath} holds {observed} {kindName} row(s); the packet freezes {expected}"
  for row in frozenRows do
    let some fields := parsed.find? (fun f => f.getD 0 "" == row.kind && f.getD 1 "" == row.id)
      | throwError "webidl census contract: {censusRelativePath} has no {row.kind} row {row.id}"
    let anchorField := fields.getD 2 ""
    let startField := fields.getD 3 ""
    let endField := fields.getD 4 ""
    let digestField := fields.getD 5 ""
    if startField != toString row.spanB then
      throwError "webidl census contract: {row.id} starts at {startField}; the packet freezes {row.spanB}"
    if endField != toString row.spanE then
      throwError "webidl census contract: {row.id} ends at {endField}; the packet freezes {row.spanE}"
    if digestField != row.digest then
      throwError "webidl census contract: {row.id} records span digest {digestField}; the packet freezes {row.digest}"
    let recomputed := Gates.Sha256.hexDigest (bytes.extract row.spanB row.spanE)
    if recomputed != row.digest then
      throwError "webidl census contract: the pinned bytes [{row.spanB}, {row.spanE}) hash to {recomputed}; the packet freezes {row.digest} for {row.id}"
    let some anchor := Gates.Census.sliceString? bytes row.spanB (row.spanB + row.anchorLen)
      | throwError "webidl census contract: the {row.anchorLen}-byte anchor of {row.id} is not valid UTF-8"
    if anchorField != anchor then
      throwError "webidl census contract: the anchor of {row.id} is not the first {row.anchorLen} bytes of its span"
  let rowsPath := projectRoot / rowsRelativePath
  unless ← liftIO rowsPath.pathExists do
    throwError "webidl census contract: missing {rowsRelativePath}; run `{regenerateCommand}`"
  let rowsText ← liftIO <| IO.FS.readFile rowsPath
  let rowsLines := Gates.Common.lines rowsText
  unless rowsLines.contains s!"def rowTotal : Nat := {expectedRowTotal}" do
    throwError "webidl census contract: {rowsRelativePath} does not record rowTotal {expectedRowTotal}"
  unless rowsLines.contains s!"def denominator : Nat := {expectedDenominator}" do
    throwError "webidl census contract: {rowsRelativePath} does not record denominator {expectedDenominator}"
  for (dispositionName, expected) in expectedDispositionCounts do
    let observed := occurrencesOf rowsText (", ." ++ dispositionName ++ ",")
    unless observed == expected do
      throwError "webidl census contract: {rowsRelativePath} carries {observed} {dispositionName} row(s); the packet freezes {expected}"
  logInfo
    m!"webidl census contract: {expectedRowTotal} rows, {frozenRows.size} frozen anchor rows verified against {sourceRelativePath} (SHA-256 {sourceDigest}), denominator {expectedDenominator}"

#webidl_census_contract_gate

end WhatwgTest.Audit.WebIdl.CensusContract
