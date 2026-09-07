import Lean
import Gates

/-!
# Census profile-identity battery

Breaker-owned and frozen before implementation. Packet:
`test/contracts/census-profile-identity.contract.md`.

Ruling R-P1 turns `Gates.Census.Standard.definitionKeyed : Bool` into a source
profile. This battery is the regression that the refactor is byte-neutral: the
Streams and Infra censuses and their two frozen coverage row lists must come
out of the new generator with the digests they have today, and their header
format and row-kind spellings must not move.

The red cause before the builder lands the refactor, and no other error class,
is that `Gates.Census.Bikeshed`, `Gates.Census.Profile` and
`Gates.Census.Standard.profile` do not exist. The four identity digests below
are checked against the working tree today and pass; the refactor must keep
them passing.

Every digest was recomputed from the working tree with .NET
`System.Security.Cryptography.SHA256.ComputeHash` over
`[IO.File]::ReadAllBytes`, and the gate recomputes each one with
`Gates.Sha256.hexDigest`, so the identity rests on two implementations of
SHA-256 rather than on one.
-/

set_option autoImplicit false

namespace WhatwgTest.Audit.CensusProfileIdentity

open Lean Elab Command

/-! ## 1. The profile, and what the two existing standards must say through it -/

#check (@Gates.Census.Bikeshed : Type)
#check (@Gates.Census.Profile : Type)
#check (@Gates.Census.Profile.bikeshed : Gates.Census.Bikeshed → Gates.Census.Profile)
#check (Gates.Census.Profile.ecmarkup : Gates.Census.Profile)
#check (@Gates.Census.Standard.profile : Gates.Census.Standard → Gates.Census.Profile)

#guard (match Gates.Census.streams.profile with
        | .bikeshed switches =>
          switches.algorithmRows == true &&
            switches.definitionRows == false &&
            switches.idlRows == true &&
            switches.slotRows == true &&
            switches.requirementMarker == some "<div algorithm=\"ReadableStreamPipeTo\">" &&
            switches.sectionScope == false &&
            switches.headingLevels == (2, 4) &&
            switches.idlOpeners == #[("<xmp class=\"idl\">", "</xmp>")]
        | .ecmarkup => false)

#guard (match Gates.Census.infra.profile with
        | .bikeshed switches =>
          switches.algorithmRows == false &&
            switches.definitionRows == true &&
            switches.idlRows == false &&
            switches.slotRows == false &&
            switches.requirementMarker == none &&
            switches.sectionScope == false &&
            switches.headingLevels == (2, 4) &&
            switches.idlOpeners == #[]
        | .ecmarkup => false)

/-! ## 2. The vocabulary that must not move

The six existing kinds keep their constructors, their external spellings and
their position at the head of `Kind.all`. Adding the seven ECMA-262 kinds
after them keeps the sort key of every Streams and Infra row unchanged. -/

#guard Gates.Census.Kind.idl.name == "idl"
#guard Gates.Census.Kind.op.name == "op"
#guard Gates.Census.Kind.requirement.name == "requirement"
#guard Gates.Census.Kind.rule.name == "rule"
#guard Gates.Census.Kind.slot.name == "slot"
#guard Gates.Census.Kind.type.name == "type"
#guard (Gates.Census.Kind.all.take 6).map (·.name) ==
  ["idl", "op", "requirement", "rule", "slot", "type"]
#guard Gates.Census.formatVersion == "1"
#guard Gates.Census.streams.regenerateCommand == "lake exe census --write"
#guard Gates.Census.infra.regenerateCommand == "lake exe census --standard infra --write"
#guard Gates.Census.streams.key == "streams"
#guard Gates.Census.infra.key == "infra"
#guard (Gates.Census.standards.take 2).map (·.key) == ["streams", "infra"]

/-! ## 3. The four frozen files -/

private structure Identity where
  path : String
  size : Nat
  digest : String
  deriving Inhabited

private def identities : Array Identity := #[
  ⟨"generated/spec-algorithm-census.tsv", 141352,
    "1a3672789fb62d3ae68eb528efb20a211727e9ed2b18c3e751c5acf67cd37e02"⟩,
  ⟨"generated/infra-census.tsv", 55766,
    "5041ef0035e087cb242a300a95398982351d766b39a4f24f28e94d9b853d5b18"⟩,
  ⟨"WhatwgTest/Audit/SpecCoverageRows.lean", 32032,
    "d0e47fdfefdf412b88a51cfcbfa2ec573d6a8092faaba3462f68468ecb377476"⟩,
  ⟨"WhatwgTest/Audit/Infra/SpecCoverageRows.lean", 10607,
    "94b04b5a9c23af20bc101be9504e2ccbd54b3e0002ccfb5ffd73c92ff7eef7b0"⟩]

private def streamsHeader : String :=
  "#census format=1 generator=Gates.Census input=vendor/whatwg-streams-b9ba9f49/index.bs " ++
  "input-sha256=24360b4f8446e6c80e185c5021fcca9b67a7e0bb62490a00109080ebc04c6440 " ++
  "rows=450 regenerate=lake exe census --write"

private def infraHeader : String :=
  "#census format=1 generator=Gates.Census input=vendor/whatwg-infra-3f984adc/infra.bs " ++
  "input-sha256=7c38e6e25ef21f536142cfc6d94954c41bc9889cd0b6fd67ab34571215acd8eb " ++
  "rows=176 regenerate=lake exe census --standard infra --write"

private def streamsKindCounts : List (String × Nat) :=
  [("idl", 133), ("op", 248), ("requirement", 7), ("slot", 62), ("rule", 0), ("type", 0)]

private def infraKindCounts : List (String × Nat) :=
  [("op", 150), ("type", 26), ("idl", 0), ("requirement", 0), ("rule", 0), ("slot", 0)]

/-! ## 4. The identity gate -/

private def kindCountsOf (dataLines : List String) : List (String × Nat) → Option (String × Nat × Nat)
  | [] => none
  | (kindName, expected) :: rest =>
    let observed :=
      dataLines.foldl
        (fun acc line => if line.startsWith (kindName ++ "|") then acc + 1 else acc) 0
    if observed == expected then kindCountsOf dataLines rest
    else some (kindName, expected, observed)

open Elab Command in
elab "#census_profile_identity_gate" : command => do
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "census profile identity: source file has no parent directory"
  let projectRoot ← liftIO <| Gates.Common.findProjectRoot sourceDirectory
  for identity in identities do
    let path := projectRoot / identity.path
    unless ← liftIO path.pathExists do
      throwError "census profile identity: missing {identity.path}"
    let bytes ← liftIO <| IO.FS.readBinFile path
    unless bytes.size == identity.size do
      throwError "census profile identity: {identity.path} is {bytes.size} bytes; the packet freezes {identity.size}"
    let observed := Gates.Sha256.hexDigest bytes
    unless observed == identity.digest do
      throwError "census profile identity: {identity.path} has SHA-256 {observed}; the packet freezes {identity.digest}. The R-P1 refactor must be byte-neutral for it"
  -- The header format and the row-kind spellings of the two existing censuses.
  let streamsText ← liftIO <| IO.FS.readFile (projectRoot / "generated/spec-algorithm-census.tsv")
  let infraText ← liftIO <| IO.FS.readFile (projectRoot / "generated/infra-census.tsv")
  let streamsLines := Gates.Common.lines streamsText
  let infraLines := Gates.Common.lines infraText
  unless streamsLines.headD "" == streamsHeader do
    throwError "census profile identity: the Streams census header line moved"
  unless infraLines.headD "" == infraHeader do
    throwError "census profile identity: the Infra census header line moved"
  unless (streamsLines.drop 1).length == 450 do
    throwError "census profile identity: the Streams census no longer holds 450 rows"
  unless (infraLines.drop 1).length == 176 do
    throwError "census profile identity: the Infra census no longer holds 176 rows"
  if let some (kindName, expected, observed) := kindCountsOf (streamsLines.drop 1) streamsKindCounts then
    throwError "census profile identity: the Streams census holds {observed} {kindName} row(s); the packet freezes {expected}"
  if let some (kindName, expected, observed) := kindCountsOf (infraLines.drop 1) infraKindCounts then
    throwError "census profile identity: the Infra census holds {observed} {kindName} row(s); the packet freezes {expected}"
  -- The two frozen coverage row lists the same two commands write.
  let streamsRows ← liftIO <| IO.FS.readFile (projectRoot / "WhatwgTest/Audit/SpecCoverageRows.lean")
  let infraRows ← liftIO <| IO.FS.readFile (projectRoot / "WhatwgTest/Audit/Infra/SpecCoverageRows.lean")
  for (label, text, total, denominator) in
      [("Streams", streamsRows, 450, 410), ("Infra", infraRows, 176, 165)] do
    let textLines := Gates.Common.lines text
    unless textLines.contains s!"def rowTotal : Nat := {total}" do
      throwError "census profile identity: the {label} row list no longer records rowTotal {total}"
    unless textLines.contains s!"def denominator : Nat := {denominator}" do
      throwError "census profile identity: the {label} row list no longer records denominator {denominator}"
  logInfo
    m!"census profile identity: 4 frozen files, Streams 450 rows / denominator 410, Infra 176 rows / denominator 165"

#census_profile_identity_gate

end WhatwgTest.Audit.CensusProfileIdentity
