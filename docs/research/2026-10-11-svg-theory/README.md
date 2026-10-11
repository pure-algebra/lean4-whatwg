# The SVG theory packet (2026-10-11)

The research partner of seat SVG wrote this packet. It serves the review
`docs/research/2026-10-11-svg-seat-review.md`: the model points T1 to T9 and the meta rules M1
to M8. The prompt is `docs/research/2026-10-11-svg-theory-prompt.md`.

The packet makes each cited source local. The seat then cites from the page, not from memory.

Four rules hold for every line below:

- Every text was fetched on 2026-10-11. Each hash is the SHA-256 of the fetched bytes.
- The texts are under `texts/`, which git ignores. Only this README is committed.
- A citation, a section number or a quotation stands here only if it was read on the named file.
  Where a file does not print its venue, the line says so.
- No Lean was run. A statement about the kernel is read from its source. It is not a
  measurement.

A sentence marked **my reading** is an inference of the research partner. It is not a statement
of a source.

## Read this first

The sources contradict or weaken the review at these points. Part 3 states each one.

| Point | What the sources say |
| --- | --- |
| T1, the name | The checker is not a "top-down deterministic" automaton in the sense of the two cited texts. It is a single-type grammar. |
| T1, fact 3 | The cited closure is under intersection, with a product of states. A sum of states is not a closure result. Union is not closed. |
| T1, fact 2 | The sources bound the number of states only exponentially. Enumeration by `decide` needs a measured count. |
| T3 | The paper's classes are DIME and DIMS. A DIMS is a local schema. Only the test at one node is a DIME. |
| T4 | `Nat.testBit` and `Nat.log2` are not kernel primitives. The docstring says "usually GMP". `Nat` has no complement. |
| T5 | The cited theorem is for ranked parse trees. "Paramorphism" alone carries no law. W1 needs equal transitions. |
| T8 | No cited paper proves the retraction for free. Every proved round trip has an unambiguity premise. Verbatim's lexer is not structural. |
| M1 | No source of the packet uses the name "de Bruijn criterion". |
| M4 | The kernel does unfold a well-founded definition. It has no notion of irreducibility. |
| M5 | Hygiene covers identifiers written in a syntax quotation. It does not cover a name built by `mkIdent`. |

## Part 1. The sources

One line per source. "Fetched" is the date of the fetch. The file is under `texts/`.

### 1.1 Trees

| Source, as read on the file | Address | Fetched | SHA-256 | File |
| --- | --- | --- | --- | --- |
| M. Murata, D. Lee, M. Mani, K. Kawaguchi, "Taxonomy of XML Schema Languages using Formal Language Theory". Authors' preprint. Its running head reads "ACM Journal Name, Vol. V, No. N, November 2004". The bibliography of TATA gives the place: ACM Transactions on Internet Technology 5(4):660–704, 2005. | `https://pike.psu.edu/publications/toit05.pdf` | 2026-10-11 | `76649738a77a119528d6aa4fe8301b25aa41d121e14e9b2ef8abf5af70eb9fcb` | `murata-lee-mani-kawaguchi-2005-taxonomy-toit.pdf` |
| G. J. Bex, W. Martens, F. Neven, T. Schwentick, "Expressiveness of XSDs: from Practice to Theory, There and Back Again", WWW 2005, May 10–14, 2005, Chiba. **Kept in place of the TODS 2006 article, which was not obtained (1.6).** | `https://archives.iw3c2.org/www2005/proceedings/docs/p712.pdf` | 2026-10-11 | `280007603559cf9bb5e69039fa273cb410b3835b6626bbc99b321d75957bf48f` | `martens-neven-schwentick-bex-2005-xsd-www.pdf` |
| H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison, M. Tommasi, *Tree Automata Techniques and Applications*. Page footer: "TATA — November 18, 2008". Kept: the title page, chapter 8 "Automata for Unranked Trees" (pages 199–244), and the bibliography and index (pages 245–262). The full book was fetched (SHA-256 `d28cb99fca83c7b8b216344b9bf64e255b4d704622f182369779e00bb1f456a6`) and cut with `pypdf`. | `https://florent-jacquemard.github.io/files/tata.pdf` | 2026-10-11 | `313553287a29b1f00d0ad8da7e794fff5b6bf31ad6aab0398b9e12960fce699c` | `tata-2008-chapter8-unranked-trees.pdf` |
| P. Kilpeläinen, D. Wood, "SGML and XML Document Grammars and Exceptions", HKUST Theoretical Computer Science Center Research Report HKUST-TCSC-99-01, January 25, 1999. **The technical report of the same authors. The journal article was not obtained (1.6).** | `https://cse.hkust.edu.hk/tcsc/RR/1999-01.ps.gz` | 2026-10-11 | `190cc6f1ece5ea2a90e994b026e7320a787edf517554a71ee9822d6ac601368b` | `kilpelainen-wood-1999-sgml-xml-exceptions-hkust-tcsc-1999-01.ps.gz` |
| I. Boneva, R. Ciucanu, S. Staworko, "Schemas for Unordered XML on a DIME", arXiv:1311.7307v4, 28 Oct 2014. The file does not print the journal. | `https://arxiv.org/pdf/1311.7307` | 2026-10-11 | `9a3966a54695b2adb22e3e74796ae14a163fb611f04c1d6a507ca31c71b0ec71` | `boneva-ciucanu-staworko-2015-dime-arxiv-1311.7307.pdf` |
| P. Caron, L. Mignot, C. Miklarz, "On the decidability of k-Block determinism", arXiv:1705.10625v1, 30 May 2017. **A closest open text for Brüggemann-Klein and Wood, which was not obtained (1.6).** | `https://arxiv.org/pdf/1705.10625` | 2026-10-11 | `13fecc8e3e1f6f7a13faf47898703219c9b5ab8b7866de4c757e00dbcb9fc200` | `caron-mignot-miklarz-2017-k-block-determinism-arxiv-1705.10625.pdf` |

### 1.2 Folds

| Source, as read on the file | Address | Fetched | SHA-256 | File |
| --- | --- | --- | --- | --- |
| D. E. Knuth, "Semantics of Context-Free Languages", Mathematical Systems Theory, Vol. 2, No. 2, pages 127–145, Springer-Verlag New York. The file does not print the year. It is a scan on a course site, not the author's or the publisher's copy. | `https://www.csee.umbc.edu/courses/331/fall16/01/resources/papers/Knuth67AG.pdf` | 2026-10-11 | `d31231696a5d00b48811cf736f7af1a212d18106bb4b93f8e91a08e218008ab6` | `knuth-1968-semantics-cfl-umbc-mirror.pdf` |
| M. Fokkinga, J. Jeuring, L. Meertens, E. Meijer, "A Translation from Attribute Grammars to Catamorphisms". The file reads "Version of November 9, 1990 — reformatted at March 10, 1994". The first author's index page gives the place: The Squiggolist, Vol 2, Nr 1, 1991, pages 20–26. | `https://maartenfokkinga.github.io/utwente/mmf91c.pdf` | 2026-10-11 | `254174861ed5abef38759b857d398245a17396576406762fa57cec6baf9f2adf` | `fokkinga-jeuring-meertens-meijer-1991-ag-to-cata-mmf91c.pdf` |
| E. Meijer, M. Fokkinga, R. Paterson, "Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire". The file prints no venue. The second author's index page gives it: FPCA91, LNCS 523, Springer, August 1991, pages 124–144. | `https://maartenfokkinga.github.io/utwente/mmf91m.pdf` | 2026-10-11 | `a37f101561101fc964448733ff3cda3714390da71be44d2713caeb5f5886c1e0` | `meijer-fokkinga-paterson-1991-bananas.pdf` |

### 1.3 Embeddings

| Source, as read on the file | Address | Fetched | SHA-256 | File |
| --- | --- | --- | --- | --- |
| J. N. Foster, M. B. Greenwald, J. T. Moore, B. C. Pierce, A. Schmitt, "Combinators for Bi-Directional Tree Transformations: A Linguistic Approach to the View Update Problem". Authors' final version, © 2007 ACM. Its head reads "ACM Transactions on Programming Languages and Systems, Vol. TBD". | `https://www.cis.upenn.edu/~bcpierce/papers/lenses-toplas-final.pdf` | 2026-10-11 | `f1c1ecc3c06a46ae6c12c68772ea6e8298d275c23776d517eb6febd32fdf20e7` | `foster-et-al-2007-lenses-toplas.pdf` |
| A. J. Kennedy, "Pickler Combinators" (Functional Pearl). Its head reads "Under consideration for publication in J. Functional Programming". The file prints no volume or year. | `https://www.microsoft.com/en-us/research/wp-content/uploads/2004/01/picklercombinators.pdf` | 2026-10-11 | `d17c976e86fc14094953a1c7e5937019ebd87811b8b1c940c4ffa7337409cdb4` | `kennedy-2004-pickler-combinators.pdf` |
| T. Rendel, K. Ostermann, "Invertible Syntax Descriptions: Unifying Parsing and Pretty Printing", Haskell'10, September 30, 2010, Baltimore. | `https://www.informatik.uni-marburg.de/~rendel/unparse/rendel10invertible.pdf` | 2026-10-11 | `65467791217ab45daf0979c7f560747df1a9ad400f1ee8a29522b83b0391b40f` | `rendel-ostermann-2010-invertible-syntax.pdf` |
| N. A. Danielsson, "Correct-by-Construction Pretty-Printing", DTP '13, September 24, 2013, Boston. | `https://www.cse.chalmers.se/~nad/publications/danielsson-correct-pretty.pdf` | 2026-10-11 | `2bbfaf03faea3d6743b77023be747c016f9cb703a04f2edd0154a2f7254f4f7d` | `danielsson-2013-correct-pretty.pdf` |

### 1.4 Regular

| Source, as read on the file | Address | Fetched | SHA-256 | File |
| --- | --- | --- | --- | --- |
| J. A. Brzozowski, "Derivatives of Regular Expressions", Journal of the Association for Computing Machinery, Vol. 11, No. 4 (October, 1964), pages 481–494. A scan on a third-party research repository. | `https://cflmark.nms.kcl.ac.uk/hg/regexp/raw-file/tip/Literature/p481-brzozowski.pdf` | 2026-10-11 | `f5d3772c0f521030cd75f1ff0c5fc1d7c94cc2befa04a8a128e0f5430ada9879` | `brzozowski-1964-derivatives-jacm.pdf` |
| S. Owens, J. Reppy, A. Turon, "Regular-expression derivatives reexamined". An author's copy. The file prints no venue. | `https://www.khoury.northeastern.edu/home/turon/re-deriv.pdf` | 2026-10-11 | `602df80d0b50789ac747a16e193eadaa4bef61019998be96d5e87998622ca631` | `owens-reppy-turon-2009-re-deriv.pdf` |
| D. Egolf, S. Lasser, K. Fisher, "Verbatim++: Verified, Optimized, and Semantically Rich Lexing with Derivatives", CPP '22, January 17–18, 2022, Philadelphia, DOI 10.1145/3497775.3503694, licence CC BY 4.0. Fetched from a third-party research repository. | `https://cflmark.nms.kcl.ac.uk/hg/lexing/raw-file/tip/Literature/VerbatimPP-Lexer.pdf` | 2026-10-11 | `138b5e867b9a0f36fa164c6426994cceea855af5531cc8fab8c99674296059e7` | `egolf-lasser-fisher-2022-verbatimpp-cpp.pdf` |
| D. Egolf, S. Lasser, K. Fisher, "Verbatim: A Verified Lexer Generator". The file prints no venue. Fetched from the same third-party repository. | `https://cflmark.nms.kcl.ac.uk/hg/lexing/raw-file/tip/Literature/Verbatim-2021-paper.pdf` | 2026-10-11 | `13761d7dae4b3bb4b41f4aee161fa69505c7e18862dd77b2822455019094c69b` | `egolf-lasser-fisher-2021-verbatim-spw.pdf` |
| G. Radanne, "Typed Parsing and Unparsing for Untyped Regular Expression Engines", PEPM '19, January 14–15, 2019, Cascais, DOI 10.1145/3294032.3294082. The author's version. | `https://gabriel.radanne.net/papers/tyre/tyre_paper.pdf` | 2026-10-11 | `9fa47a39e48af787edc3efa179c6f091e900f692d7e5cabf371616e75088b9d3` | `radanne-2019-tyre.pdf` |

### 1.5 Meta

| Source, as read on the file | Address | Fetched | SHA-256 | File |
| --- | --- | --- | --- | --- |
| The Coq Reference Manual 8.19.0, the page "ring and field: solvers for polynomial and rational equations". **The closest open text for Boutin, which was not obtained (1.6).** The page cites it as [Bou97]. | `https://coq.inria.fr/doc/V8.19.0/refman/addendum/ring.html` | 2026-10-11 | `626b3b0010e39dfabb721e4d4bc0466d9c131d0c562f00bbc171fa189cd1238c` | `coq-refman-8.19-ring-addendum.html` |
| G. Gonthier, A. Mahboubi, "An introduction to small scale reflection in Coq", Journal of Formalized Reasoning Vol. 3, No. 2, 2010, pages 95–152. | `https://jfr.unibo.it/article/download/1979/1358` | 2026-10-11 | `83cc7c36a24cefa567c3b85cb59f2a839cfaad685ab0e75d5848562b82b36b51` | `gonthier-mahboubi-2010-ssreflect-jfr.pdf` |
| B. Grégoire, X. Leroy, "A Compiled Implementation of Strong Reduction", ICFP'02, October 4–6, 2002, Pittsburgh. | `https://xavierleroy.org/publi/strong-reduction.pdf` | 2026-10-11 | `0d799e758d73d3a5138b08fb259d0b377e8aa340d62c792c0bdb44ee6bd65bcf` | `gregoire-leroy-2002-strong-reduction.pdf` |
| S. Ullrich, L. de Moura, "Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages", Logical Methods in Computer Science Volume 18, Issue 2, 2022, pages 1:1–1:21. | `https://arxiv.org/pdf/2001.10490` | 2026-10-11 | `3523fa896f71c836aa3bf895ba8d6384cc606533b82565439f87b6442b2e3e56` | `ullrich-demoura-2022-beyond-notations-arxiv-2001.10490.pdf` |
| L. de Moura, S. Ullrich, "The Lean 4 Theorem Prover and Programming Language", CADE 2021, LNAI 12699, pages 625–635, DOI 10.1007/978-3-030-79876-5_37, licence CC BY 4.0. | `https://link.springer.com/content/pdf/10.1007/978-3-030-79876-5_37.pdf` | 2026-10-11 | `e1fc635e3e6e84572240316d34275592cca99a871b45005456c4ac4690764f9b` | `demoura-ullrich-2021-lean4-cade-springer.pdf` |
| L. de Moura, J. Avigad, S. Kong, C. Roux, "Elaboration in Dependent Type Theory", arXiv:1505.04324v2, 17 Dec 2015. | `https://arxiv.org/pdf/1505.04324` | 2026-10-11 | `0d2efdb95704cdd3a5920adc955efcadab5f6aeb6548c81c1661140209f3ba0e` | `demoura-avigad-kong-roux-2015-elaboration-arxiv-1505.04324.pdf` |

### 1.6 Sources not obtained

| Source | What was tried | What stands in its place |
| --- | --- | --- |
| W. Martens, F. Neven, T. Schwentick, G. J. Bex, "Expressiveness and complexity of XML Schema". TATA's bibliography gives ACM Transactions on Database Systems 31(3):770–813, 2006. | `documentserver.uhasselt.be/bitstream/1942/1424/1/tods.pdf` answers "available only on campus and via VPN". `alpha.uhasselt.be/~lucg5503/tods2006.pdf` does not connect. `lrb.cs.uni-dortmund.de/~martens/data/tods06.pdf` does not resolve. | The WWW 2005 paper of the same four authors (1.1). TATA Section 8.7.2 states two of the results. |
| A. Brüggemann-Klein, D. Wood, "One-unambiguous regular languages". The WWW 2005 paper cites it as Information and Computation 142(2):182–206, 1998. TATA's bibliography gives 140(2):229–253, 1998. The two differ, and the paper was not seen. | The publisher's open archive (`sciencedirect.com`; CORE's record gives DOI 10.1006/inco.1997.2695) and the mirror `https://core.ac.uk/download/81993955.pdf` both answer with a bot check. The partner does not pass bot checks. A person can open either address in a browser. | TATA Section 8.7.1, Murata et al. Section 6.6, the WWW 2005 paper Section 5.1, and Caron et al. (1.1). |
| P. Kilpeläinen, D. Wood, the journal article. CORE's record gives Information and Computation 169, pages 230–251, 2001, DOI 10.1006/inco.2000.2964. The article was not seen. | The publisher's open archive answers with a bot check. | The technical report HKUST-TCSC-99-01 of the same authors (1.1). |
| S. Boutin, "Using reflection to build efficient and certified decision procedures", TACS 1997, DOI 10.1007/BFb0014565. | `link.springer.com/content/pdf/10.1007/BFb0014565.pdf` returns a sales page. Unpaywall lists no open copy. Semantic Scholar marks it closed. | The Coq Reference Manual page that cites it (1.5). Grégoire and Leroy, Section 1, and Gonthier and Mahboubi, Section 1, describe the method. |

Three more copies came from a mirror, because the publisher answers with a bot check: TATA (the
HAL record), Verbatim++ and Brzozowski (the ACM Digital Library).

### 1.7 The Lean 4 sources at tag `v4.33.1`

Each file was fetched from
`https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/<path>` on 2026-10-11. It is saved
under `texts/lean4-v4.33.1/` with `/` written as `-`. Each `.lean` file has the same hash as its
copy in the local toolchain `leanprover/lean4:v4.33.1`. The toolchain does not ship the kernel's
C++ files.

| Path at the tag | SHA-256 |
| --- | --- |
| `src/kernel/type_checker.cpp` | `5312a8f02318d6e3fe7eca68bf3525d5f3558fa98f5737612b52cac2e588c447` |
| `src/kernel/type_checker.h` | `251e5910586972445d0ebd317a056e27d8f124515f19ae7865560526fa7935b0` |
| `src/kernel/declaration.h` | `eb9c497bb19dab26550cbb5196a13e0a925896c6d357a8faa2f3794c1e798a51` |
| `src/Init/Prelude.lean` | `56de5780adc4358372fa9cfac270a70f2d03fd4f213a373aea4365483b31a544` |
| `src/Init/Core.lean` | `8537e234659a281a8f49cc91e2f48c17b6faeacb852d1c4ba3a09b6b5e45ab20` |
| `src/Init/WF.lean` | `fe7c0a49de4a9c4b4fac24493f40598a1374837b17a6c334fc1ed03e23646e01` |
| `src/Init/Data/Nat/Basic.lean` | `92edcd298633bc57f70cf6c9cea73a3b6f984b91b3c8cc8fcc72f57bada0ee36` |
| `src/Init/Data/Nat/Bitwise/Basic.lean` | `0196b9eabcb97bd41b9ace0cfb828d2f0f0215085d2eb8972d2c541539c94df3` |
| `src/Init/Data/Nat/Bitwise/Lemmas.lean` | `529687f061efb55560de711acb367184e86b2cc8c21a4894a6169460e337f430` |
| `src/Init/Data/Nat/Gcd.lean` | `672c96102205b59a47742be74c959ed780ba319713baaa8a2eeede2cdc46cbea` |
| `src/Init/Data/Nat/Log2.lean` | `afef53e5ebc17001038c5f4c9000e8e2856d3976bec23019266840f91743da6b` |
| `src/Lean/AutoDecl.lean` | `67b9553c36481666ed4bad819abe7edcd634a4863ce79eecf2ae7f2846628fde` |
| `src/Lean/MonadEnv.lean` | `1c168f46d68a62564d44a1996d856d19b41f0088f02f3f481be38580c907ef95` |
| `src/Lean/Elab/MutualInductive.lean` | `8a30233713df9a399c8a529511c6767668d9cfa82a46a8ae02b8c631231274d8` |
| `src/Lean/Elab/Deriving/DecEq.lean` | `690927433eebce75ae83ea8498f18b5b1b0684b22d00aa32e5c319ae8fdbfc07` |
| `src/Lean/Meta/NatTable.lean` | `377abb7c9a590d5f9871c2ae331fec24fe9b551cebef3679790f3689f425a98b` |
| `src/Lean/Meta/Constructions/CtorIdx.lean` | `0ee3af3884cf3a85325d06fde6eca551e29884def81124548297e1243f7ab019` |
| `src/Lean/Meta/Constructions/SparseCasesOn.lean` | `a0e49b27302adcb51cc357a36c24bd2b3e4b401a65de82ab8f6570b0221cec10` |

## Part 2. What the package takes

### 2.1 Trees

**Murata, Lee, Mani, Kawaguchi.** Against T1: the paper's closure result is for intersection, and
it does not call this pass a deterministic top-down automaton (Part 3, C1 and C2).

- A regular tree grammar has productions `X → a r`. `a` is a label, and `r` is a regular
  expression over nonterminals (Definition 2.1).
- Two nonterminals compete when their productions share a label (Definition 2.4). A grammar is
  single-type when no content model holds two competing nonterminals, and the start symbols do
  not compete (Definition 2.6).
- The package takes this as the class of T1. A nonterminal is a pair of a position and a name.
  `Pos.child` is a function, so the grammar is single-type by construction (my reading).
- A tree has at most one interpretation against a single-type grammar (Proposition 2).
  Algorithm 2 finds it in one depth-first pass (Section 4.3). The time is linear in the
  document (Section 4.6).
- Section 5.1 names HTML's ban on a nested `a` and SGML's exclusions. It says that a
  single-type grammar can hold them, with one nonterminal per combination. This supports the
  exclusion set as a component of the state (T3).
- Quotation: "deterministic top-down tree automata are almost useless for XML" (Section 6.5).

**Bex, Martens, Neven, Schwentick (WWW 2005), in place of the TODS article.**

- A single-type grammar is the paper's model of XML Schema under the rule "Element Declarations
  Consistent" (Section 2.3, Definition 1).
- Section 5.2 reports a characterisation: the type of a node depends only on the labels on the
  path from the root. The proof is in another paper, which this packet does not hold.
- The package takes this as the meaning of T1's first fact. A position is a function of the
  path. The rule for `a` under `switch` in T3 is such a function (my reading).
- Section 4.1 gives a test for the class: closure under an exchange of subtrees whose roots
  have the same path of labels. A constraint that fails the test is outside the class.
- Sections 5.2 and 5.3 name a wider class, where a type may also depend on left siblings. The
  count rules of T3 do not need it: they are tests at the parent (my reading).
- Quotation: "every single-type SDTD admits 1PPT" (Section 5.2). 1PPT is typing at the opening
  tag.

**TATA, chapter 8.** Against T1: Exercise 8.5 defines "top-down deterministic" for hedge
automata, and the checker does not fit it (Part 3, C1).

- A hedge automaton has rules `a(R) → q`. `R` is a regular language over states
  (Section 8.2.2). It runs bottom-up.
- The recognizable languages of unranked trees are closed under union, intersection and
  complement (Theorem 8.3.8). This is the wide class. It is not the single-type class.
- Section 8.7.2 defines the single-type extended DTD. The proof of Theorem 8.7.10 assigns types
  top-down, as `Pos.child` does. Inclusion of two deterministic single-type schemas is
  polynomial (Theorem 8.7.11).
- The package may use Theorem 8.7.11 later: two versions of a schema can be compared by a
  procedure. No slice plans this.
- Section 8.9 relates single-type schemas to top-down deterministic automata only loosely, and
  only in the sense of a paper by Cristau, Löding and Thomas. That paper is not in this packet.
- Quotation: "The single-type property of D allows a unique top-down assignment of types"
  (Section 8.7.2, proof of Theorem 8.7.10).

**Kilpeläinen and Wood (the technical report).** It supports T3.

- A DTD with exceptions is a grammar with productions `A → E + I − X`. `I` is the set of
  inclusions and `X` the set of exclusions (Section 3).
- A derivation step gives each new nonterminal the union of the sets in force and the sets of
  the production. So the exclusions only grow along a path. This is the first law of T3.
- An exclusion overrides an inclusion (Section 3).
- Algorithm I removes the exceptions. It makes one nonterminal per name, inclusion set and
  exclusion set, and the count can grow exponentially (Section 3). So the package keeps the set
  as data in the state (T3, T4). It does not expand the grammar.
- The report describes a parser that keeps the excluded names on a stack and asks it at each
  element (Section 3). `Ctx.child` with an exclusion mask is that parser.
- Quotation: "exceptions are propagated and cumulated by derivations" (Section 3). The text
  layer of the PostScript breaks words, so the seat should check the page.

**Boneva, Ciucanu, Staworko.** Against T3: the name and the class differ from the review's
(Part 3, C4).

- An unordered word is a multiset of labels (Section 2). The children of a node are read as
  one.
- A DIME is an unordered concatenation of clauses. A clause is a disjunction of atoms with
  intervals (Section 4.2). The multiplicities are intervals `[n, m]`, with `?`, `1`, `+` and `*`
  as short forms (Section 2).
- Membership and containment for DIMEs are in polynomial time (Theorem 4). Membership of a tree
  runs in one pass with a counter per label, and it rejects at the earliest point
  (Proposition 2).
- The three count rules of T3 are clauses: one of the three light sources with multiplicity
  `1`, and `mpath?` (my reading).
- Unrestricted unordered expressions are hard. Membership is NP-complete even with only `?` and
  unordered concatenation (Theorem 1). So the package keeps its model flat: disjoint groups,
  with one interval each.
- Quotation: "a symbol can occur at most once in a DIME" (Section 4.2).

**Brüggemann-Klein and Wood (not obtained).** The notes come from the texts that state its
results.

- TATA Section 8.7.1 defines a deterministic regular expression, and gives 1-unambiguous as
  its other name. Mark each letter of the expression with its position. No two marked words
  may then continue one prefix with two positions of the same letter.
- Murata et al., Section 6.6, and Caron et al., Section 2, give the same notion by an
  automaton: the Glushkov automaton of the expression is deterministic.
- A deterministic expression gives a deterministic automaton in polynomial time (TATA,
  Theorem 8.7.4). Some regular languages have no deterministic expression (TATA,
  Theorem 8.7.6). TATA Section 8.9 credits both to this paper.
- The package takes one thing for T1. If an ordered model is deterministic, `seqOk` can match
  it in one pass, with the next name as its only lookahead.
- No text of the packet says that the ordered models of the HTML Standard are deterministic.
  The seat checks that per model, or states it as a premise.

### 2.2 Folds

**Knuth.** It supports T5.

- Section 1 introduces the two kinds of attribute. Section 2 splits the attributes of each
  symbol into synthesized and inherited ones, and gives the start symbol no inherited
  attribute.
- The package's state `S` is one inherited attribute. The result `R` of an algebra is one
  synthesized attribute.
- Section 2 also shows that synthesized attributes alone suffice in principle. It adds that
  the rules are then harder to read. A fold into functions of the state is that encoding.
- Section 3 tests a grammar for circular rules. The walk needs no such test: a child's state
  depends only on its parent's state and name (my reading).
- Quotation: "inherited attributes are evaluated from the top down" (Section 1).

**Fokkinga, Jeuring, Meertens, Meijer.** Against T5, in scope only: the theorem is for ranked
parse trees, and its general case needs a fixed point (Part 3, C6).

- Theorem (8): to evaluate the attributes of a tree `t` with root value `x` is to apply a
  catamorphism to `t` and then to `x`. In the partner's notation:
  `eval A (t, x) = cata φ t x`, with `cata φ t : X → Y`.
- Assumption (2) tuples all inherited attributes of a node into one, and all synthesized
  attributes into one. This is why `S` and `R` are single types.
- In the general rule, a child's inherited value may depend on its siblings' results, and the
  note solves that by recursion. In the walk it depends on the parent's state and name only.
  So the walk is a plain structural recursion (my reading).
- The note's functor is a sum of finite products, one per production. `RawNode` has a list of
  children. The same induction works, but the seat proves it over the node and the list.

**Meijer, Fokkinga, Paterson.** Against T5, in wording only: the word "paramorphism" carries no
law (Part 3, C6).

- Section 4 gives the fusion law of catamorphisms (CataFusion): `f ∘ cata φ = cata ψ` when
  `f ∘ φ = ψ ∘ F f`. The paper works with partial values, so it adds that `f` is strict.
- A paramorphism also gives its algebra the substructure itself (ParaEval). Its fusion law
  (ParaFusion) has the same shape.
- W1 is the fusion law at the carrier `S → R`, with `f = (h ∘ ·)`. W2 is the same law with
  `f = (· ∘ g)` for the state map `g`. One proof shape serves both (my reading).
- Lean's functions are total, so the strictness premise has no counterpart (my reading).
- Quotation: "Any function f (of the right type of course!) is a paramorphism." (Section 4).

### 2.3 Embeddings

**Foster, Greenwald, Moore, Pierce, Schmitt.** It supports T6 and T7.

- A lens is a `get` and a `putback` (Definition 3.1). It is well behaved when it satisfies the
  laws GetPut and PutGet (Definition 3.2).
- A lens is oblivious when `putback` ignores the old concrete value (Definition 3.7). A total
  oblivious lens is a bijection (Lemma 3.9).
- A name table of T6 is an oblivious lens between the spellings and the tags. The retraction is
  PutGet. The exactness is GetPut. Totality is Definition 3.3 (my reading).
- For T7, `decode_render` is PutGet for the printer, and injectivity follows from it.
- The laws of the paper are exact. It has no law "modulo a normaliser". The packet holds no
  formal source for that form, which T6 uses for case restoration.
- Quotation: "every bijection between C and A induces a total oblivious lens" (Section 3, after
  Lemma 3.9).

**Kennedy.** Against T8: the paper states the round trip and does not prove it (Part 3, C7).

- One value of type `PU a` holds a pickler and an unpickler. The combinators are `pair`,
  `wrap` with two functions, `alt` with a tag function, and `sequ` (Sections 2 and 3).
- Section 5 states two properties. Unpickling after pickling is the identity. Pickling after a
  successful unpickling gives the same bytes. It adds that the first holds only for values in
  the intended domain.
- The library chooses its own byte format. A list, for one, is written after its length
  (Section 3). An SVG grammar is fixed by its specification. So the package's printer must
  write the separators that make the reading unique (my reading).
- `alt` takes a function from a value to the index of its alternative. A description that
  prints a sum needs the same.
- Quotation: "mostly correct by construction, with additional proof obligations generated by
  some combinators" (Section 1).

**Rendel and Ostermann.** Against T8: the paper proves no round trip, and its descriptions
cannot be erased to a regular expression (Part 3, C7).

- A partial isomorphism is a pair of partial functions, each of which undoes the other where
  it is defined (Section 3.1). In the partner's notation: `f a = some b ↔ g b = some a`.
- A description is built from five things: a map by a partial isomorphism, a product, a
  choice with an empty case, `pure` and `token` (Section 3.4). The printer of a choice tries
  the left side first (Section 3.3).
- Section 4.3 gives a description a meaning: a relation between values and strings. The
  package takes this relation as the specification of both directions.
- Section 3.1 lets the law of a partial isomorphism hold only up to an equivalence. Section
  6.3 uses that for white space. The package states the law strictly, as two proofs in a
  structure.
- Section 4.4 says that a parser with one token of lookahead may fail where the relation
  holds. So the reader's strategy matters to completeness (V3b).
- Quotation: "Both printing and parsing are under-specified here" (Section 4.3).

**Danielsson.** It supports T7, and it names the premise that T8 lacks.

- A document has the type `Doc g x`, indexed by a grammar `g` and a value `x` (Section 1).
  A printer for `g` gives each value `x` a document of that type.
- A renderer must satisfy one property, proved once: the string it writes for a `Doc g x`
  parses to `x` under `g` (Section 1).
- The round trip then follows for an unambiguous grammar, and only for one (Section 1).
- Section 2 says that regular expressions with semantic actions can replace the paper's
  general grammars. That is the shape of T8.
- For T7, `decode_render` is this pattern: a printer that is correct against the grammar, and
  a grammar that is unambiguous on well-formed trees (my reading).
- Quotation: "which for unambiguous grammars g implies the round-tripping property"
  (Section 1).

### 2.4 Regular

**Brzozowski.** It supports T8, V3a.

- The derivative of a set `R` by a sequence `s` is the set of `t` with `st` in `R`
  (Definition 3.1). Theorem 3.1 computes it by the structure of the expression, with a test
  for the empty sequence (Definition 3.2).
- Theorem 4.2: `s` is in `R` exactly when the empty sequence is in the derivative of `R` by
  `s`. The proof is two lines. In the partner's notation: `s ∈ L r ↔ nullable (D s r)`.
- Theorem 4.3 says that an expression has finitely many derivatives up to equality of
  languages. A matcher does not need it. An automaton does.
- The package takes Theorems 3.1 and 4.2 as the statement of `Regex.accepts_iff`. The matcher
  recurses on the input list, so it is structural (M4).
- The text layer of the scan is poor, so no quotation is given.

**Owens, Reppy, Turon.** It weakens the prompt's phrase "with its correctness": the paper states
the correctness of the matcher in one sentence, with no proof (Part 3, C7).

- Section 3.1 restates the derivative and the nullability function, for expressions with
  intersection and complement. Section 3.2 defines matching by repeated derivatives.
- Section 4.1 lists equations that keep a derivative small, and builds each expression through
  smart constructors that apply them. The package does the same, because the kernel pays for
  every node (M4).
- Section 4.2 takes a set of characters as an atom. The derivative of a set by a character is
  the empty word if the character is in the set, and nothing otherwise. A mask over the code
  point is such a set (T4, T8).
- The derivative classes of Section 4.2 serve the construction of an automaton. A matcher that
  takes one derivative per input character does not need them.
- The paper does not treat the longest match.
- Quotation: "It is straightforward to show" (Section 3.2). These are the words that stand
  for the proof.

**Egolf, Lasser, Fisher (both papers).** Against T8 and M4: the lexer is not structurally
recursive, and neither paper has a printer (Part 3, C7).

- The specification is the rule of the longest match. The first token is the longest prefix
  that matches a rule, and the earliest rule wins a tie (2021, Sections II.B and II.C;
  Verbatim++, Section 2.5).
- Three theorems are proved in Coq: soundness, uniqueness of the specified result, and
  completeness. Completeness follows from the other two (2021, Section V).
- The package takes this order for V3b: prove that the specification has one result, and
  completeness then follows from soundness. The step needs a specification that gives every
  input a result. Verbatim's does: a text with no first token is returned unprocessed
  (my reading).
- The lexer recurses on a suffix that a function returns. Coq does not accept that as
  structural, so the definition carries an accessibility proof (2021, Section IV). A reader
  that the Lean kernel evaluates should not have this shape (M4, with the reason of C9).
- Verbatim++ adds semantic actions: a function from a token's text to an optional typed value
  (Section 6). It does not ask for a proof that the action succeeds on every match.
- Quotation: "the first word of z is the maximal prefix of z with respect to R" (2021,
  Section II.C).

**Radanne.** It gives T8 its data type. It proves no law.

- A typed regular expression is a data type. A choice has a sum type, a sequence a pair, a
  repetition a list, and an untyped leaf a string. A converter changes the type by two
  functions, and `Ignore` gives a unit (Section 4).
- The untyped expression is derived from the typed one (Section 4). This is `Syn.erase`.
- Unparsing walks the typed expression. An ignored part is filled with some word of its
  language (Section 4.4).
- The library leaves matching to an outside engine. The paper states no round-trip law.
- Section 6 notes that a map with one direction would make unparsing impossible. So a
  converter of the package holds both directions.
- Quotation: "Unparsing can't fail but the result is not unique." (Section 2.1).

### 2.5 Meta

**Boutin (not obtained); the Coq Reference Manual in its place.** It supports M1, M3 and M4.

- The section "How does it work?" defines reflection: a part of a tactic is a function of the
  logic, with a proof of its correctness.
- The scheme has three steps. Meta code guesses a term of a data type and a map of variables.
  The goal must convert to the interpretation of that term. The proof then applies one
  correctness theorem.
- This is M1: the meta code proposes, and the kernel checks the conversion. The guess is the
  reification of M3.
- The section "History of ring" says that the proof terms are small, and that checking them
  costs time in the conversion rule. This is the cost of M4.
- The same section says that Boutin rewrote an earlier tactic by reflection, and cites
  [Bou97].
- Quotation: "the proof is only the application of the main correctness theorem to
  well-chosen arguments" (section "How does it work?").

**Gonthier and Mahboubi.** It supports M1 and M7.

- Section 1 defines small-scale reflection. Statements hold symbolic data, and a decidable
  predicate is a Boolean function. It contrasts this with the reflection of `ring`.
- The predicate `reflect P b` ties a proposition to a Boolean (Section 4.1.4).
- A finite type holds a Boolean equality and a list of its values (Section 6.1.1). The axiom
  says that each value occurs in the list exactly once. A second form asks for a list with no
  duplicates that holds every value.
- This is the class of M7. Its laws are stated once, for every finite type.
- The plan's class `Universe` asks that each value stands at its index. That gives "at least
  once". The paper's axiom gives "exactly once". The package needs the stronger form only where
  it counts values (my reading).
- Quotation: "a duplicate-free sequence containing all the elements of the carrier type"
  (Section 6.1.1).

**Grégoire and Leroy.** It supports M4 by contrast.

- Section 1 says that proof assistants of that time reduced a term by walking its tree. It
  names this as the bottleneck of proofs by reflection.
- The paper compiles a term to the code of an abstract machine and reads the result back. The
  correctness is checked in Coq (Section 5), because a wrong evaluator would break the logic.
- On its tests the compiled evaluator is one to two orders faster than the lazy interpreter
  (Section 6).
- The Lean kernel at `v4.33.1` is of the interpreted kind: `whnf` with a cache and lazy
  unfolding, as read in `type_checker.cpp`. Its compiled path is `Lean.reduceBool`, which this
  repository forbids. So M4's cost model is the interpreter's, with the `Nat` list of 2.6 as
  the one fast path (my reading).
- Quotation: "10 to 100 times faster than Coq's lazy call-by-name interpreter" (Section 6).

**Ullrich and de Moura.** Against M5, in scope only (Part 3, C10).

- Section 3 gives two rules. An identifier in a quotation that matches top-level symbols keeps
  them as its top-level scopes. Each expansion marks the identifiers that it introduces with a
  fresh macro scope.
- So a binder that a macro writes in a quotation cannot capture a user's name. A user's binder
  cannot capture the macro's name either.
- Section 4 says that `mkIdent` makes an identifier from a name, with no top-level scopes. It
  adds no macro scope. So a name made that way is outside hygiene (my reading).
- An element name of `html!` that stays a string literal is data. Hygiene does not concern it
  (my reading).
- The paper says nothing of the token table or of a trust gate.
- Quotation: "all identifiers freshly introduced by the expansion are annotated with a new
  macro scope" (Section 3).

**de Moura and Ullrich.** Weak for M1 and M4: the paper says almost nothing about the kernel.

- It is a system description. It covers the extensible parser and elaborator, the macro
  system, type class resolution and the code generator.
- Its one statement on the kernel is the quotation below. It does not name the `Nat`
  operations of the kernel, and it does not discuss the cost of evaluation in the kernel.
- Section 3 says that the code generator erases proofs and emits C. That is the path of
  compiled code. It is not the kernel's path (my reading).
- So the facts of M4 rest on the kernel's source (2.6), not on this paper.
- Quotation: "Lean has a relatively small trusted kernel" (Section 5).

**de Moura, Avigad, Kong, Roux.** It supports M1. With the kernel's source, it contradicts one
sentence of M4 (Part 3, C9).

- The paper describes the elaborator of Lean in 2015. Lean 4's elaborator is a new program, so
  the paper is background.
- The elaborator turns a partial expression into a fully specified, type-correct term
  (Section 2.1). The kernel then checks that term. This is the division of M1.
- The marks `irreducible`, `semireducible` and `reducible` guide the elaborator only. The
  kernel ignores them when it checks a term (Sections 2.3 and 3.3).
- Quotation: "These annotations are used only by the elaborator" (Section 2.3).

### 2.6 The two facts about the toolchain

**Fact 1. The `Nat` operations that the kernel evaluates.** The function is
`type_checker::reduce_nat` in `src/kernel/type_checker.cpp` at `v4.33.1`, lines 702–733:

```cpp
optional<expr> type_checker::reduce_nat(expr const & e) {
    unsigned nargs = get_app_num_args(e);
    if (nargs == 1) {
        expr const & f = app_fn(e);
        if (f == *g_nat_succ) {
            ...
        }
    } else if (nargs == 2) {
        expr const & f = app_fn(app_fn(e));
        if (!is_constant(f)) return none_expr();
        if (f == *g_nat_add) return reduce_bin_nat_op(nat_add, e, /* check_size */ true);
        if (f == *g_nat_sub) return reduce_bin_nat_op(nat_sub, e, /* check_size */ true);
        if (f == *g_nat_mul) return reduce_bin_nat_op(nat_mul, e, /* check_size */ true);
        if (f == *g_nat_pow) return reduce_pow(e);
        if (f == *g_nat_gcd) return reduce_bin_nat_op(nat_gcd, e);
        if (f == *g_nat_mod) return reduce_bin_nat_op(nat_mod, e);
        if (f == *g_nat_div) return reduce_bin_nat_op(nat_div, e);
        if (f == *g_nat_beq) return reduce_bin_nat_pred(nat_eq, e);
        if (f == *g_nat_ble) return reduce_bin_nat_pred(nat_le, e);
        if (f == *g_nat_land) return reduce_bin_nat_op(nat_land, e);
        if (f == *g_nat_lor)  return reduce_bin_nat_op(nat_lor, e);
        if (f == *g_nat_xor)  return reduce_bin_nat_op(nat_lxor, e);
        if (f == *g_nat_shiftLeft) return reduce_shiftLeft(e);
        if (f == *g_nat_shiftRight) return reduce_bin_nat_op(lean_nat_shiftr, e);
    }
    return none_expr();
}
```

Lines 1326–1341 bind these names to the constants `Nat.zero`, `Nat.succ`, `Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.pow`, `Nat.gcd`, `Nat.div`, `Nat.mod`, `Nat.beq`, `Nat.ble`, `Nat.land`,
`Nat.lor`, `Nat.xor`, `Nat.shiftLeft` and `Nat.shiftRight`.

- **On the list:** `Nat.succ`, and the fourteen binary operations above. `Nat.pow`, `Nat.gcd`,
  `Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft` and `Nat.shiftRight`
  are among them.
- **Not on the list:** `Nat.testBit` and `Nat.log2`.
- **`Nat.testBit` is an ordinary definition.** It is in
  `src/Init/Data/Nat/Bitwise/Basic.lean`, lines 147–149:

  ```lean
  @[expose, implicit_reducible] def testBit (m n : Nat) : Bool :=
    -- `1 &&& n` is faster than `n &&& 1` for big `n`.
    1 &&& (m >>> n) != 0
  ```

  The kernel unfolds it. It then meets `Nat.shiftRight`, `Nat.land` and a comparison. `!=` is
  `bne`, which is `!(a == b)` (`src/Init/Core.lean`, line 772). On `Nat`, `==` comes from
  `DecidableEq` (`src/Init/Prelude.lean`, line 1078), and `Nat.decEq` is a match on `Nat.beq`
  (lines 1869–1873). So each step ends in an operation of the list.
- **`Nat.log2` is an ordinary definition** by `Nat.rec` on a fuel argument
  (`src/Init/Data/Nat/Log2.lean`, lines 41–45). It has an `extern` name for compiled code only.
- **When the fast path applies.** Both arguments must reduce to literals
  (`reduce_bin_nat_op`, lines 644–658). In `lazy_delta_reduction` the kernel tries it only for
  terms with no free variable, or under `eagerReduce` (lines 1093–1099).
- **Limits.** A numeral may not pass `LEAN_NAT_MAX_SIZE`, 128 MB by default (lines 31–36).
  The second argument of `Nat.pow` and `Nat.shiftLeft` must fit 32 bits (lines 305–313).
- **The library behind it.** The docstring of `Nat` says "usually GMP"
  (`src/Init/Prelude.lean`, lines 1235–1236).
- **The lemmas of T4 exist.** `Nat.testBit_and`, `Nat.testBit_or` and `Nat.testBit_xor` are in
  `src/Init/Data/Nat/Bitwise/Lemmas.lean`, lines 496, 573 and 649. `Nat.eq_of_testBit_eq` is at
  line 189.
- **A precedent.** Lean itself keeps a set of constructor indices as a `Nat` mask.
  `Nat.hasNotBit` is "used by Lean internally for compact bitmaps" (`Bitwise/Basic.lean`, lines
  151–157), and `SparseCasesOn.lean` states `Nat.hasNotBit mask x.ctorIdx` (line 50).

**Fact 2. The index function of an inductive type.** Its name is `ctorIdx`. It is in
`src/Lean/Meta/Constructions/CtorIdx.lean`. The excerpt is lines 24–28 and 38–51, with two
lines left out at the second `...`:

```lean
public def mkToCtorIdxName (indName : Name) : Name :=
  Name.mkStr indName "toCtorIdx"

public def mkCtorIdxName (indName : Name) : Name :=
  Name.mkStr indName "ctorIdx"
...
/--
For an inductive type `T` with more than one function builds a function `T.ctorIdx : T → Nat` that
returns the constructor index of the given value.
Does nothing if `T` does not eliminate into `Type` or if `T` is unsafe.
Assumes `T.casesOn` to be defined already.
-/
public def mkCtorIdx (indName : Name) : MetaM Unit :=
  ...
    unless genCtorIdx.get (← getOptions) do return
    let declName := mkCtorIdxName indName
    if (← hasConst declName) then return
    let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
    if (← isPropFormerType info.type) then return
```

- **It is generated for every inductive type, not only for an enumeration.**
  `mkAuxConstructions` calls it for each declared type
  (`src/Lean/Elab/MutualInductive.lean`, line 1552: `if hasNat then mkCtorIdx n`).
- **The code returns early in three cases:** the option `genCtorIdx` is off, the type is a
  proposition, or its `casesOn` cannot eliminate into every universe (`CtorIdx.lean`, lines
  47–54). It also returns if a constant of that name exists.
- **Its value** is `casesOn` with one raw literal per constructor. For a type with one
  constructor it is the constant `0` (lines 65–82).
- **`toCtorIdx` is a deprecated alias.** It exists only for an enumeration, it unfolds to
  `ctorIdx`, and it is deprecated since 2025-08-25 (lines 101–117).
- **`ofNat` exists only under `deriving DecidableEq` on an enumeration.** The handler is
  `mkDecEqEnum` in `src/Lean/Elab/Deriving/DecEq.lean`, lines 264–286:

  ```lean
  def mkDecEqEnum (declName : Name) : CommandElabM Unit := do
    let cmd ← liftTermElabM do
      mkEnumOfNat declName
      mkEnumOfNatThm declName
      let ofNatIdent  := mkIdent (Name.mkStr declName "ofNat")
      let auxThmIdent := mkIdent (Name.mkStr declName "ofNat_ctorIdx")
  ...
  def mkDecEqInstance (declName : Name) : CommandElabM Bool := do
    withoutExposeFromCtors declName do
    if (← isEnumType declName) then
      mkDecEqEnum declName
      return true
    else
      mkDecEq declName
  ```

- **`T.ofNat : Nat → T` is total.** It is a tree of `cond (Nat.ble n k) low high`
  (`src/Lean/Meta/NatTable.lean`, lines 25–38). A number past the last index gives the last
  constructor.
- **One theorem comes with it:** `T.ofNat_ctorIdx : ∀ x, T.ofNat (T.ctorIdx x) = x`
  (`DecEq.lean`, lines 239–262). No theorem is generated for `T.ctorIdx (T.ofNat n) = n`.
- **No function is named `ofCtorIdx`.** A search of the toolchain's Lean sources finds none.
- **An enumeration** is a single inductive type that is not a proposition and not recursive.
  It has no parameter and no index, and no constructor has a field (`isEnumType`,
  `src/Lean/MonadEnv.lean`, lines 198–207).

## Part 3. Where a source contradicts or weakens the review

**C1. T1: "a top-down deterministic hedge automaton".** Two cited texts use the name for a
weaker device.

- Murata et al., Section 6.5: a deterministic top-down automaton gives a node its state
  without reading the node. The paper says that its Algorithms 1 and 2 read the element first.
- TATA, Exercise 8.5: in a top-down deterministic hedge automaton, the states of the children
  follow from the parent's rule and their number alone.
- The checker of T1 reads the children's names to accept. So it is neither device.
- TATA Section 8.9 says only that single-type schemas are near a third definition, in a paper
  outside this packet.
- **What to write:** "a single-type grammar, validated in one top-down pass". Cite Murata et
  al., Definition 2.6 and Algorithm 2.

**C2. T1, fact 3: "closed under product ... whose state is the sum of their states".**

- Murata et al., Theorem 2.4: the single-type class is closed under intersection. The proof
  pairs the nonterminals. That is a product of states, for the intersection of two languages.
- Theorem 2.2: the class is not closed under union. The union of two local languages need not
  be single-type.
- TATA, Theorem 8.3.8, gives all three closures, but for the wide recognizable class.
- The seam of T2 is neither an intersection nor a union. It is a new grammar over both sets of
  names. Its state is a sum.
- **What to write:** the composed grammar is single-type because `Pos.child` is a function.
  Cite no closure theorem for it. HTML and SVG share names, such as `a` and `title`. Their
  types compete, and the grammar stays single-type only because no position admits both
  (my reading).
- The product closure does serve T2 and T3. A state that holds a namespace, a model and an
  exclusion set is a product.

**C3. T1, fact 2: "A test can enumerate them".**

- The states are finite. No source disputes it.
- Murata et al., Section 5.1, say that a single-type grammar for HTML's exclusions needs one
  nonterminal per combination. Kilpeläinen and Wood bound the growth only exponentially
  (Section 3).
- **What to write:** state the reachable count as a measured number before a `decide` over
  all reachable positions is promised.

**C4. T3: "This is a disjunctive multiplicity schema".**

- The paper's classes are the disjunctive interval multiplicity expression (DIME) and schema
  (DIMS). The file says that an earlier workshop version exists. The review's name is not in
  the file.
- A DIMS gives each label one expression (Section 5, Definition 1). It is a local schema, with
  no context. The model of T3 has transparency and exclusions, so it is not a DIMS.
- Only the test at one node is a DIME.
- A DIME allows an interval on a disjunction only as `1`, `?`, `+` or `*`, and each label
  occurs once (Section 4.2). "A list of intervals, each over a set of labels" is wider.
- **What to write:** "the test at a node is a DIME (Boneva et al., Section 4.2)". Keep the
  groups disjoint and the intervals among the four forms. The three count rules of SVG fit.
- The paper's bounds are not needed for membership. The package's test counts labels.

**C5. T4: four details.**

- "The kernel evaluates `Nat` arithmetic and its bit operations natively": true for the
  sixteen constants of Fact 1. `Nat.testBit` and `Nat.log2` are not among them. `testBit`
  unfolds to operations that are.
- "by GMP": the docstring says "usually GMP".
- "A finite Boolean algebra" (T3) on `Nat` masks: the toolchain has no complement on `Nat`.
  The package needs a top mask per universe, and a rule that a mask has no bit past the
  universe. Without the rule, two masks with the same members can differ, and `a ||| b = b`
  is not inclusion (my reading).
- The fast path needs closed terms. A proof about a variable mask goes through the
  `testBit` lemmas.

**C6. T5: three details.**

- Fokkinga et al. prove their theorem for ranked parse trees. Their general case solves a
  recursion between siblings. The walk is the special case with no such recursion, over a tree
  with a list of children. The citation supports the carrier `S → R`. The proof is the seat's.
- Meijer et al., Section 4: every function is a paramorphism. So "the walk is a paramorphism"
  states a shape. The law is the fusion law.
- W1, as the review writes it, lacks a premise: the two walks have the same transition. The
  fusion premise `f ∘ φ = ψ ∘ F f` covers the whole algebra, and the transition is part of it
  (my reading). The plan's Section 3.1 already has this premise.

**C7. T8: six details.**

- "Three laws are proved once, over the description": no cited paper proves V1. Rendel and
  Ostermann give a relation and call both directions under-specified (Section 4.3). Kennedy
  states the property with a caveat (Section 5). Radanne states none.
- Danielsson proves the round trip, for unambiguous grammars only (Section 1). So V1 has a
  premise per grammar. "Each grammar then costs its transcription and nothing more" is too
  strong. The plan's `Syn.ok` is this premise.
- V1 is not independent of V3b. `read (print v) = some v` needs the reader to find the printed
  parse. That is completeness on the image of the printer (my reading).
- "Its erasure is that expression (Rendel and Ostermann; Kennedy)": both libraries are
  functions of the host language, with the host's recursion. They cannot be erased. Radanne's
  data type can (Section 4).
- "Through a derivative matcher (Brzozowski; Owens, Reppy and Turon)": Owens et al. state the
  matcher's correctness without proof. Brzozowski's Theorem 4.2 has the proof.
- "Verbatim's longest-match lexer is the model to read": its definition recurses by an
  accessibility proof (2021, Section IV). M4 rules that shape out. Take the specification and
  the order of the theorems, not the definition. Neither paper has a printer.

**C8. M1: the name.** No text of this packet uses "de Bruijn criterion". The content is
supported: the Coq manual's scheme, de Moura et al. 2015, Sections 2.1 and 2.3, and de Moura
and Ullrich, Section 5. **What to write:** cite a source for the name, or state the rule
without the name.

**C9. M4: "The kernel does not unfold a well-founded definition".** The kernel's source says
otherwise.

- `is_delta` unfolds any constant that has a value (`type_checker.cpp`, lines 555–563).
  `has_value` is true for a definition and for a theorem (`declaration.h`, lines 466–468).
- The kernel has no notion of irreducibility. de Moura et al. 2015 say the same of the Lean of
  that year (Section 2.3).
- Well-founded recursion is built on `WellFounded.fix`, which is `fixF` on a proof of
  accessibility (`src/Init/WF.lean`, lines 98–100 and 135–136). `fixF` recurses on that proof.
- So the kernel unfolds such a function. Each step must then reduce the proof to its
  constructor (my reading). The partner did not measure how far that goes or what it costs.
- A comment in the kernel names a "function defined using well-founded recursion" as an
  expensive term to unfold (`type_checker.cpp`, lines 1010–1011).
- **What to write:** "Recurse structurally. The kernel reduces a well-founded definition only
  through its accessibility proof." The rule stands. Its reason changes. The seat should
  measure one case before it states the cost.

**C10. M5: the scope of hygiene.** Hygiene marks the identifiers of a syntax quotation
(Ullrich and de Moura, Section 3). `mkIdent` gives an identifier no scope of its own
(Section 4). So the sentence of M5 holds for names written in a quotation, and not for names
computed from text.

**Smaller notes.**

- T6 and T7: Foster et al. give exact laws only. "A retraction modulo a named normaliser" has
  no formal source in this packet.
- T1, the ordered models: the packet does not show that the HTML Standard's ordered models
  are deterministic expressions.
- M1 and M4 cite de Moura and Ullrich. That paper has one sentence on the kernel.
- T2 and T9 cite no source of the table, so the packet has nothing on them.

## Part 4. A reading order for the seat

Five sources, in this order, before the plan revision. The sections are the ones to read.

1. **Murata, Lee, Mani, Kawaguchi.** Section 2 to the end of 2.6: Definitions 2.4 to 2.6,
   Propositions 1 and 2, Theorems 2.2 to 2.4. Then Section 4.3 (Algorithm 2), Section 5.1 and
   Section 6.5. This fixes the name of the class and what closure it has (C1, C2).
2. **Boneva, Ciucanu, Staworko.** Section 2 (unordered words and intervals), Sections 4.1 and
   4.2, Definition 1 of Section 5, and Proposition 2 of Section 6. This fixes the count model
   of T3 (C4).
3. **Fokkinga, Jeuring, Meertens, Meijer**, all seven pages. Then **Meijer, Fokkinga,
   Paterson**, Section 4: CataFusion, ParaEval and ParaFusion. This fixes W1 and W2 as one law
   (C6).
4. **Rendel and Ostermann.** Sections 3.1, 3.3, 3.4, 4.3 and 4.4. Read Section 4.3 as the
   specification of `Syn`, and Section 4.4 as the warning for V3b (C7).
5. **Owens, Reppy, Turon.** Sections 3.1 and 3.2, then 4.1 and 4.2. This is `Regex.accepts`
   and `CharSet` (C7).

If time allows, four short passages close the open points:

- Danielsson, Section 1, for the premise of V1.
- TATA, Section 8.7.2 and Exercise 8.5, for the name in T1.
- Kilpeläinen and Wood, Section 3, for the law of the exclusions.
- Egolf, Lasser and Fisher (2021), Sections II.B, II.C and IV, for the longest match and for
  the recursion that M4 forbids.
