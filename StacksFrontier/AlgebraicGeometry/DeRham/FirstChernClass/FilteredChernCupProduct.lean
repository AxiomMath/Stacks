module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.BrutalPresentations
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.GradedPieceMultiplicativity

/-!
# Cup products of Hodge-filtered first Chern classes, for an arbitrary natural pairing

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` whose
stalks are local rings, let `Ω^•_{𝒪_X/A}` be the relative de Rham complex, and let
`γ₁ : Pic(X) ⟶ H²(X, σ^{≥1}Ω^•_{𝒪_X/A})` be the Hodge-filtered first Chern class of
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredFirstChernClass`.

This file develops the multiplicative theory of the Hodge filtration — the cup products of
Section 50.7 (Tag 0FM7), its two commutative diagrams, the multiplicativity of the filtration, and
the `a`-fold products of first Chern classes of Remark 50.9.2 (Tag 0FME) together with their two
images — for **every natural pairing**

`H^i(X, K) × H^j(X, L) ⟶ H^{i + j}(X, M)`

attached to multiplications `m : Tot(K ⊗_A L) ⟶ M` of complexes of sheaves of `A`-modules, that
is, for every term of `AlgebraicGeometry.SheafOfModules.TruncationCupProduct`. Everything here is
proved from naturality alone. The cup product of the source is the term
`AlgebraicGeometry.SheafOfModules.truncationCupProduct` of
`StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProduct`, built from the
canonical global cup product of Cohomology, Section 0FKU; the statements of Section 50.7 and of
Remark 50.9.2 for *that* cup product, with no parameter, are in that file and in
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.CanonicalChernCupProduct`, and they carry the
tags. Nothing in this file is registered: a statement quantified over all natural pairings —
the zero pairing among them — is a lemma about the source's cup product only once it is
specialised to it.

## What is proved for an arbitrary pairing

The multiplication of complexes displayed in Section 50.7,

`Tot(σ^{≥i}Ω^•_{𝒪_X/A} ⊗_A σ^{≥j}Ω^•_{𝒪_X/A}) ⟶ σ^{≥(i + j)}Ω^•_{𝒪_X/A}`,

is `AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge`
(`StacksFrontier/AlgebraicGeometry/DeRham/HodgeFiltration/Multiplicativity.lean`), and
`hodgeFiltrationWedge_ιBrutal` says it is the wedge product of Tag 0FM2 restricted. Pairing those
two facts with a natural pairing gives
`AlgebraicGeometry.SheafOfModules.TruncationCupProduct.cup` and
`AlgebraicGeometry.SheafOfModules.TruncationCupProduct.cupDeRham` as *definitions*, and the
commutative diagram `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.truncationMap_cup` as a
*theorem*: the inclusion of the truncation is multiplicative because the multiplication of the
filtration lies over the wedge product and the pairing is natural.

The second diagram, for the projections `σ^{≥k}Ω^• ⟶ Ω^k[-k]` onto the bottom graded pieces, is a
theorem in the same way. Its complex-level input is
`AlgebraicGeometry.SheafOfModules.gradedPieceWedge_comm`
(`StacksFrontier/AlgebraicGeometry/DeRham/HodgeFiltration/GradedPieceMultiplicativity.lean`): the
multiplication `Tot(Ω^p[-p] ⊗_A Ω^q[-q]) ⟶ Ω^{p + q}[-(p + q)]` of the graded pieces and the
square it satisfies with the projections. The projection is the same map in the two presentations
of a brutal truncation by
`AlgebraicGeometry.SheafOfModules.brutalTruncationCohomologyMap_gradedPieceProjection`, so the
naturality of the pairing turns that square into
`AlgebraicGeometry.SheafOfModules.TruncationCupProduct.gradedPieceMap_cup`, the cup product on the
graded pieces being the definition
`AlgebraicGeometry.SheafOfModules.TruncationCupProduct.cupGradedPiece`.

Both diagrams are about products of *two* classes. The `a`-fold statements are deduced from them
by induction on the number of factors, starting from the `a = 1` clauses `C` and `E` of the
imported file; that induction is the mathematical content of the last part of this file.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.singleComplexPlus` and
  `AlgebraicGeometry.SheafOfModules.singleComplexCohomology`: an abelian sheaf placed in an
  arbitrary cohomological degree `p`, and the hypercohomology `H^n(X, F[-p])` of that complex.
* `AlgebraicGeometry.SheafOfModules.sheafCohomologyIsoShiftedCohomology`: **`H^a(X, F) ≅
  H^{2a}(X, F[-a])`**, the identification
  `AlgebraicGeometry.SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo` in an arbitrary
  degree.
* `AlgebraicGeometry.SheafOfModules.gradedPieceProjection`: **the projection
  `σ^{≥p}Ω^•_{𝒪_X/A} ⟶ Ω^p_{𝒪_X/A}[-p]`** onto the bottom graded piece, in an arbitrary degree.
* `AlgebraicGeometry.SheafOfModules.gradedPieceCohomology` and
  `AlgebraicGeometry.SheafOfModules.gradedPieceProjectionCohomologyMap`: the group
  `H^n(X, Ω^p[-p])` and the map induced by that projection.
* `AlgebraicGeometry.SheafOfModules.gradedPieceCohomologyIsoHodgeCohomology`: **the group
  `H^{2a}(X, Ω^a[-a])` is the Hodge cohomology group `H^a(X, Ω^a_{𝒪_X/A})`** of the source.
* `AlgebraicGeometry.SheafOfModules.HypercohomologyPairing` and
  `AlgebraicGeometry.SheafOfModules.TruncationCupProduct`: a pairing of hypercohomology groups
  along multiplications of complexes, and such a pairing with its naturality.
* `AlgebraicGeometry.SheafOfModules.moduleHypercohomology`: `H^n(X, K)` for an `ℕ`-indexed
  complex of sheaves of `A`-modules read in abelian sheaves, the groups the pairing pairs.
* `AlgebraicGeometry.SheafOfModules.brutalTruncationCohomologyIso`: **`H^n(X, σ^{≥p}Ω^•)` is the
  hypercohomology of the brutal truncation of Section 0FM7**.
* `AlgebraicGeometry.SheafOfModules.cupOfPair`,
  `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.cup`,
  `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.cupDeRham` and
  `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.cupGradedPiece`: the products on
  `H^*(X, σ^{≥p}Ω^•)`, on `H^*_{dR}` and on the graded pieces `H^*(X, Ω^p[-p])` attached to a
  natural pairing.
* `AlgebraicGeometry.SheafOfModules.gradedPiecePlusIso` and
  `AlgebraicGeometry.SheafOfModules.gradedPieceCohomologyIso`: the bottom graded piece
  `Ω^k_{𝒪_X/A}[-k]`, and its hypercohomology, in the two presentations.
* `AlgebraicGeometry.SheafOfModules.cupLength` and
  `AlgebraicGeometry.SheafOfModules.cupDegree`: the filtration index `a` and the cohomological
  degree `2a` of a product of `a = k + 1` first Chern classes, in the shape the recursion builds
  them; `cupLength_eq` and `cupDegree_eq` identify them with `a` and `2a`.
* `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.filteredChernProduct`,
  `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.deRhamChernProduct` and
  `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.hodgeChernProduct`: the `a`-fold
  products `γ₁(L₁) ∪ … ∪ γ₁(L_a)`, `c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a)` and
  `c₁^{Hodge}(L₁) ∪ … ∪ c₁^{Hodge}(L_a)` for a natural pairing.
* `AlgebraicGeometry.SheafOfModules.hodgeFirstChernClassGraded`: `c₁^{Hodge}(L)` read in the
  group `H²(X, (Ω^•)¹[-1])` that the projection of `γ₁(L)` lands in.

## Main results

* `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.truncationMap_cup` and
  `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.gradedPieceMap_cup`: the inclusions
  `σ^{≥p}Ω^• ⟶ Ω^•` and the projections `σ^{≥p}Ω^• ⟶ Ω^p[-p]` are multiplicative.
* `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.cupDeRham_mem_hodgeFiltrationAbelian`:
  the Hodge filtration is multiplicative,
  `F^iH^n_{dR} ∪ F^jH^m_{dR} ⊆ F^{i + j}H^{n + m}_{dR}`, using
  `AlgebraicGeometry.SheafOfModules.exists_eq_truncatedDeRhamCohomologyAbelianMap` and
  `truncatedDeRhamCohomologyAbelianMap_mem_hodgeFiltrationAbelian`,
  which say that a class lies in a step of the filtration exactly when it comes from the
  hypercohomology of the corresponding brutal truncation.
* `AlgebraicGeometry.SheafOfModules.brutalTruncationPlus_gradedPieceProjectionPlus` and
  `AlgebraicGeometry.SheafOfModules.brutalTruncationCohomologyMap_gradedPieceProjection`:
  the projection onto the bottom graded piece is the same map in the two presentations, on
  complexes and on hypercohomology.
* `TruncationCupProduct.truncatedDeRhamCohomologyAbelianMap_filteredChernProduct`,
  `TruncationCupProduct.deRhamChernProduct_mem_hodgeFiltrationAbelian`
  and
  `TruncationCupProduct.gradedPieceProjectionCohomologyMap_filteredChernProduct`:
  the images of the `a`-fold product `γ₁(L₁) ∪ … ∪ γ₁(L_a)`, for a natural pairing.
* `AlgebraicGeometry.SheafOfModules.gradedPieceProjectionCohomologyMap_filteredFirstChernClass`:
  the `a = 1` case of the last of these, which is clause `E` of the imported file with `Ω¹`
  relabelled as the degree-one term of the extended de Rham complex.

## Implementation notes

**Indexing, and why there are no transports.** A product of `a` classes is indexed by `k = a - 1`
and a family `L : ℕ → Pic(X)`, the factors being `L 0, …, L k` in that order; this keeps the
recursion on `ℕ` while leaving the number of factors at least one, which is where the source
states the remark. The filtration index and cohomological degree are the functions `cupLength` and
`cupDegree`, defined by the *same* recursion as the product itself, so that the degree of the
value built at `k + 1` from the one at `k` is syntactically the degree the type asks for. In
consequence no `cast` and no reindexing transport appears anywhere below, and the two inductions
are plain rewrites. The price is the two lemmas `cupLength_eq` and `cupDegree_eq`, which say that
these are `a` and `2a`.

**The graded pieces.** The projection `σ^{≥p}Ω^• ⟶ Ω^p[-p]` is written with target the degree-`p`
term of the de Rham complex *extended by zero to negative degrees*, rather than `Ω^p` itself,
because the extended complex is what the brutal truncation is taken of and its term is available
for every `p : ℤ`; for `p` a natural number
`AlgebraicGeometry.SheafOfModules.deRhamAbelianIntXIsoNat` identifies it with `Ω^p`, and
`gradedPieceCohomologyIsoHodgeCohomology` turns that into the identification of
`H^{2a}(X, Ω^a[-a])` with `H^a(X, Ω^a)`. The `p = 1` case differs from
`AlgebraicGeometry.SheafOfModules.degreeOneProjection` by exactly that relabelling, which is
`AlgebraicGeometry.SheafOfModules.gradedPieceProjectionPlus_relabel`.

As in the imported file, everything is in the abelian-sheaf realization of de Rham cohomology,
because `d log` is additive but not `𝒪_X`-linear; the package `B` of the three algebras of Stacks
Section 17.21 and the de Rham differential `D` on it are hypotheses, and by
`AlgebraicGeometry.SheafOfModules.deRhamDifferential_unique` the differential is unique.

## References

* [Stacks Project, Tag 0FME](https://stacks.math.columbia.edu/tag/0FME)
* [Stacks Project, Tag 0FM7](https://stacks.math.columbia.edu/tag/0FM7)
* [Stacks Project, Tag 0FM8](https://stacks.math.columbia.edu/tag/0FM8)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Tag 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
-- `abelianModules`, `hasSheafifyOpens` and `wEqualsLocallyBijectiveOpens` are `local instance`s
-- of `WedgeFiltration`, and `local` scopes the attribute rather than the name, so the three are
-- re-enabled here instead of being declared again. The last two are what let
-- `SheafOfModules.instAbelian` be found at `Stacks.SheafOfModules.Tensor.ringSheaf A`.
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

/-! ### An abelian sheaf placed in an arbitrary cohomological degree -/

section Shift

variable (Y : TopCat.{u}) (p : ℤ) (F : AbelianSheaf Y)

/-- An abelian sheaf placed in cohomological degree `p`, `F[-p]`, as a bounded-below complex. -/
def singleComplexPlus : CochainComplex.Plus (AbelianSheaf Y) :=
  ⟨(CochainComplex.singleFunctor _ p).obj F, p, inferInstance⟩

/-- At `p = 1` this is `AlgebraicGeometry.SheafOfModules.singleOneComplexPlus`. -/
theorem singleComplexPlus_one : singleComplexPlus Y 1 F = singleOneComplexPlus Y F := rfl

/-- `H^n(X, F[-p])`, the degree-`n` hypercohomology of an abelian sheaf placed in degree `p`. -/
abbrev singleComplexCohomology (n : ℤ) : AddCommGrpCat.{u} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
    ((sectionsFunctor Y ⊤).rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj (singleComplexPlus Y p F)))

end Shift

section ShiftIso

variable (Y : TopCat.{u}) (a : ℕ) (p n : ℤ) (hp : (a : ℤ) = p) (hn : p + p = n) (F : AbelianSheaf Y)

/-- **`H^a(X, F) ≅ H^{2a}(X, F[-a])`**: the degree-`a` cohomology of an abelian sheaf is the
degree-`2a` hypercohomology of that sheaf placed in cohomological degree `a`.

This is `AlgebraicGeometry.SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo` for an
arbitrary degree, assembled from the same two inputs: the comparison
`Stacks.DerivedIndexing.rightDerivedIso` of the two indexings of the right derived functors, and
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`, which moves the degree of a
single complex across the shift-commuting functor `RΓ(X, -)`.

Both degrees are parameters constrained by `hp` and `hn` rather than the literals `a` and `a + a`,
so that a caller at a numeral obtains the identification in the degrees it is reading, with no
transport. -/
def sheafCohomologyIsoShiftedCohomology :
    ((sectionsFunctor Y ⊤).rightDerived a).obj F ≅ singleComplexCohomology Y p F n := by
  subst hp
  subst hn
  exact (Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y ⊤) a).app F ≪≫
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
      (sectionsFunctor Y ⊤).rightDerivedFunctorPlus (a : ℤ) (a : ℤ)).app F).symm

end ShiftIso

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The graded pieces of the Hodge filtration -/

/-- The degree-`a` term of the de Rham complex of abelian sheaves extended by zero to negative
degrees is `Ω^a`, for every natural number `a`. This is
`AlgebraicGeometry.SheafOfModules.deRhamAbelianIntXIsoOne` in an arbitrary degree. -/
abbrev deRhamAbelianIntXIsoNat (a : ℕ) :
    (deRhamAbelianComplexInt B D).X (a : ℤ) ≅ (deRhamAbelianComplex B D).X a :=
  (deRhamAbelianComplex B D).extendXIso embeddingUpNat (i := a) (i' := (a : ℤ)) rfl

/-- **The projection `σ^{≥p}Ω^•_{𝒪_X/A} ⟶ Ω^p_{𝒪_X/A}[-p]`** of the `p`-th step of the Hodge
filtration onto its bottom graded piece. This is
`AlgebraicGeometry.SheafOfModules.degreeOneProjection` in an arbitrary degree, with the target
written as the degree-`p` term of the extended complex; for `p` a natural number
`AlgebraicGeometry.SheafOfModules.deRhamAbelianIntXIsoNat` identifies that term with `Ω^p`. -/
abbrev gradedPieceProjection (p : ℤ) :
    (deRhamAbelianComplexInt B D).stupidTrunc (embeddingUpIntGE p) ⟶
      (CochainComplex.singleFunctor (AbelianSheaf X.carrier) p).obj
        ((deRhamAbelianComplexInt B D).X p) :=
  StacksDraft.StupidTruncation.stupidTruncGEπ (deRhamAbelianComplexInt B D) p

/-- `Ω^p_{𝒪_X/A}[-p]`: the degree-`p` term of the de Rham complex placed in cohomological degree
`p`, as a bounded-below complex. -/
abbrev gradedPieceComplexPlus (p : ℤ) : CochainComplex.Plus (AbelianSheaf X.carrier) :=
  singleComplexPlus X.carrier p ((deRhamAbelianComplexInt B D).X p)

/-- The projection `σ^{≥p}Ω^• ⟶ Ω^p[-p]` as a morphism of bounded-below complexes. -/
abbrev gradedPieceProjectionPlus (p : ℤ) :
    deRhamAbelianTruncationPlus B D p ⟶ gradedPieceComplexPlus B D p :=
  ⟨gradedPieceProjection B D p⟩

/-- **The hypercohomology `H^n(X, Ω^p_{𝒪_X/A}[-p])` of a graded piece of the Hodge filtration.**
For `n = 2p` it is the Hodge cohomology group `H^p(X, Ω^p)` of the source, by
`AlgebraicGeometry.SheafOfModules.sheafCohomologyIsoShiftedCohomology`. -/
abbrev gradedPieceCohomology (p n : ℤ) : AddCommGrpCat.{u} :=
  singleComplexCohomology X.carrier p ((deRhamAbelianComplexInt B D).X p) n

/-- **The group `H^{2a}(X, Ω^a_{𝒪_X/A}[-a])` in which the `a`-fold Hodge product of first Chern
classes lives is the Hodge cohomology group `H^a(X, Ω^a_{𝒪_X/A})` of the source.**

Both degrees are parameters constrained by `hp` and `hn`, so that a caller reading the degrees off
`AlgebraicGeometry.SheafOfModules.cupLength` and `AlgebraicGeometry.SheafOfModules.cupDegree`
obtains the identification in exactly those degrees. -/
def gradedPieceCohomologyIsoHodgeCohomology (a : ℕ) (p n : ℤ) (hp : (a : ℤ) = p)
    (hn : p + p = n) :
    ((sectionsFunctor X.carrier ⊤).rightDerived a).obj ((deRhamAbelianComplex B D).X a) ≅
      gradedPieceCohomology B D p n := by
  subst hp
  exact ((sectionsFunctor X.carrier ⊤).rightDerived a).mapIso
      (deRhamAbelianIntXIsoNat B D a).symm ≪≫
    sheafCohomologyIsoShiftedCohomology X.carrier a (a : ℤ) n rfl hn
      ((deRhamAbelianComplexInt B D).X (a : ℤ))

/-- The map `H^n(X, σ^{≥p}Ω^•) ⟶ H^n(X, Ω^p[-p])` induced by the projection onto the bottom
graded piece. -/
abbrev gradedPieceProjectionCohomologyMap (p n : ℤ) :
    truncatedDeRhamCohomologyAbelian B D p n ⟶ gradedPieceCohomology B D p n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (gradedPieceProjectionPlus B D p)))

/-! ### Hypercohomology of a complex of sheaves of modules -/

/-- An `ℕ`-indexed complex of sheaves of `A`-modules, read in abelian sheaves and extended by
zero to negative degrees, as a bounded-below complex. For the de Rham complex itself this is
`AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus`. -/
abbrev modulePlus (K : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ) :
    CochainComplex.Plus (AbelianSheaf X.carrier) :=
  ⟨((abelianisationFunctor (A := A)).obj K).extend embeddingUpNat, 0, inferInstance⟩

/-- A morphism of `ℕ`-indexed complexes of sheaves of `A`-modules, read in abelian sheaves and
extended by zero. -/
abbrev modulePlusMap {K L : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}
    (f : K ⟶ L) : modulePlus (A := A) K ⟶ modulePlus (A := A) L :=
  ⟨HomologicalComplex.extendMap ((abelianisationFunctor (A := A)).map f) embeddingUpNat⟩

/-- **`H^n(X, K)`**, the degree-`n` hypercohomology of an `ℕ`-indexed complex of sheaves of
`A`-modules, read in abelian sheaves. For the de Rham complex it is
`AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelian` and for its brutal truncations it is
`AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelian`, by
`AlgebraicGeometry.SheafOfModules.brutalTruncationCohomologyIso`. -/
abbrev moduleHypercohomology (K : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ) (n : ℤ) :
    AddCommGrpCat.{u} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj (modulePlus (A := A) K)))

/-- The map on hypercohomology induced by a morphism of complexes of sheaves of modules. -/
abbrev moduleHypercohomologyMap {K L : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ} (f : K ⟶ L)
    (n : ℤ) : moduleHypercohomology (A := A) K n ⟶ moduleHypercohomology (A := A) L n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (modulePlusMap (A := A) f)))

/-! ### The brutal truncation read as a step of the Hodge filtration -/

/-- The morphism `σ^{≥k}Ω^• ⟶ σ^{≥p}Ω^•` from the brutal truncation at a natural number `k`,
read in abelian sheaves and extended by zero, to the step of the Hodge filtration at any `p ≤ k`:
the identification `AlgebraicGeometry.SheafOfModules.deRhamBrutalAbelianIso` of the two
presentations, followed by the comparison of the tower of stupid truncations. -/
abbrev brutalTruncationPlus (k : ℕ) (p : ℤ) (hp : p ≤ (k : ℤ)) :
    modulePlus (A := A) (deRhamBrutal B D k) ⟶ deRhamAbelianTruncationPlus B D p :=
  ⟨(deRhamBrutalAbelianIso B D k).hom ≫
    StacksDraft.StupidTruncation.stupidTruncGEMapLE (deRhamAbelianComplexInt B D) hp⟩

/-- **The comparison lies over the inclusions into the de Rham complex**: composing it with
`σ^{≥p}Ω^• ⟶ Ω^•` returns the abelianised, extended inclusion of the brutal truncation. -/
theorem brutalTruncationPlus_ι (k : ℕ) (p : ℤ) (hp : p ≤ (k : ℤ)) :
    brutalTruncationPlus B D k p hp ≫ ιDeRhamAbelianTruncationPlus B D p =
      modulePlusMap (A := A) (CochainComplex.ιBrutal (deRhamComplex B D) k) := by
  apply (CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map_injective
  show ((deRhamBrutalAbelianIso B D k).hom ≫
      StacksDraft.StupidTruncation.stupidTruncGEMapLE (deRhamAbelianComplexInt B D) hp) ≫
      HomologicalComplex.ιStupidTrunc (deRhamAbelianComplexInt B D) (embeddingUpIntGE p) = _
  rw [Category.assoc, StacksDraft.StupidTruncation.stupidTruncGEMapLE_ι]
  exact deRhamBrutalAbelianIso_hom_ι B D k

/-- **The brutal truncation at `p.toNat` is the `p`-th step of the Hodge filtration**, for every
`p : ℤ`. For `0 ≤ p` the two indices agree; for `p < 0` both truncations are the whole de Rham
complex, which has no terms in negative degrees. -/
def brutalTruncationPlusIso (p : ℤ) :
    modulePlus (A := A) (deRhamBrutal B D p.toNat) ≅ deRhamAbelianTruncationPlus B D p := by
  have hp : p ≤ ((p.toNat : ℕ) : ℤ) := by omega
  haveI : IsIso (StacksDraft.StupidTruncation.stupidTruncGEMapLE
      (deRhamAbelianComplexInt B D) hp) :=
    StacksDraft.StupidTruncation.isIso_stupidTruncGEMapLE _ hp fun n _ _ =>
      CochainComplex.isZero_of_isStrictlyGE (deRhamAbelianComplexInt B D) 0 n (by omega)
  haveI : IsIso ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map
      (brutalTruncationPlus B D p.toNat p hp)) := by
    change IsIso ((deRhamBrutalAbelianIso B D p.toNat).hom ≫ _)
    infer_instance
  haveI := isIso_of_fully_faithful (CochainComplex.Plus.ι (AbelianSheaf X.carrier))
    (brutalTruncationPlus B D p.toNat p hp)
  exact asIso (brutalTruncationPlus B D p.toNat p hp)

/-- The map `H^n(X, σ^{≥k}Ω^•) ⟶ H^n(X, σ^{≥p}Ω^•)` induced by that comparison. -/
abbrev brutalTruncationCohomologyMap (k : ℕ) (p : ℤ) (hp : p ≤ (k : ℤ)) (n : ℤ) :
    moduleHypercohomology (A := A) (deRhamBrutal B D k) n ⟶
      truncatedDeRhamCohomologyAbelian B D p n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (brutalTruncationPlus B D k p hp)))

/-- **The hypercohomology of the brutal truncation at `p.toNat` is the group
`H^n(X, σ^{≥p}Ω^•)`** in which the Hodge-filtered first Chern class and its cup products live. -/
def brutalTruncationCohomologyIso (p n : ℤ) :
    moduleHypercohomology (A := A) (deRhamBrutal B D p.toNat) n ≅
      truncatedDeRhamCohomologyAbelian B D p n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).mapIso
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.mapIso
      (DerivedCategory.Plus.Q.mapIso (brutalTruncationPlusIso B D p)))

/-- The isomorphism is the comparison map at `k = p.toNat`. -/
theorem brutalTruncationCohomologyIso_hom (p n : ℤ) (hp : p ≤ ((p.toNat : ℕ) : ℤ)) :
    (brutalTruncationCohomologyIso B D p n).hom =
      brutalTruncationCohomologyMap B D p.toNat p hp n := rfl

/-- The comparison map at `p.toNat` is a retraction of the inverse of the isomorphism. -/
private theorem brutalTruncationCohomologyMap_apply_inv (p n : ℤ) (hp : p ≤ ((p.toNat : ℕ) : ℤ))
    (z : truncatedDeRhamCohomologyAbelian B D p n) :
    (brutalTruncationCohomologyMap B D p.toNat p hp n).hom
      ((brutalTruncationCohomologyIso B D p n).inv.hom z) = z := by
  rw [← brutalTruncationCohomologyIso_hom B D p n hp]
  simp

/-- **The map `H^n(X, σ^{≥k}Ω^•) ⟶ H^n_{dR}` of the brutal presentation factors through the
`p`-th step of the Hodge filtration**, for every `p ≤ k`. -/
theorem moduleHypercohomologyMap_ιBrutal (k : ℕ) (p : ℤ) (hp : p ≤ (k : ℤ)) (n : ℤ) :
    moduleHypercohomologyMap (A := A) (CochainComplex.ιBrutal (deRhamComplex B D) k) n =
      brutalTruncationCohomologyMap B D k p hp n ≫
        truncatedDeRhamCohomologyAbelianMap B D p n := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, brutalTruncationPlus_ι]
  rfl

/-! ### The bottom graded piece in the two presentations -/

/-- **`Ω^k_{𝒪_X/A}[-k]`, read in abelian sheaves and extended by zero, vanishes outside degree
`k`.** In a degree `(m : ℤ)` retained by the extension the term is the degree-`m` term of the
single complex, which vanishes for `m ≠ k`; in a negative degree the extension vanishes. -/
lemma isZero_gradedPieceAbelian_X (k : ℕ) (n : ℤ) (hn : n ≠ (k : ℤ)) :
    IsZero ((((abelianisationFunctor (A := A)).obj (deRhamGradedPiece B D k)).extend
      embeddingUpNat).X n) := by
  by_cases hm : ∃ m : ℕ, (m : ℤ) = n
  · obtain ⟨m, rfl⟩ := hm
    refine IsZero.of_iso ?_ (((abelianisationFunctor (A := A)).obj
      (deRhamGradedPiece B D k)).extendXIso embeddingUpNat (i := m) (i' := (m : ℤ)) rfl)
    have h0 : IsZero ((deRhamGradedPiece B D k).X m) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) k _ m (by omega)
    exact (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map_isZero h0
  · exact HomologicalComplex.isZero_extend_X _ _ n fun m hm' => hm ⟨m, hm'⟩

/-- **The comparison `Ω^k[-k] ⟶ Ω^k[-k]` of the two presentations of the bottom graded piece** of
the `k`-th step of the Hodge filtration: the graded piece
`AlgebraicGeometry.SheafOfModules.deRhamGradedPiece` that carries the multiplication of Section
50.7, read in abelian sheaves and extended by zero, compared with the single complex
`AlgebraicGeometry.SheafOfModules.gradedPieceComplexPlus` that the Hodge filtration on
hypercohomology projects onto.

The target is concentrated in degree `k`, so the comparison is given by its degree-`k` component
alone, and that is the identification of the degree-`k` term of the extension with `Ω^k` read in
abelian sheaves. -/
def gradedPieceComplexHom (k : ℕ) :
    ((abelianisationFunctor (A := A)).obj (deRhamGradedPiece B D k)).extend embeddingUpNat ⟶
      (CochainComplex.singleFunctor (AbelianSheaf X.carrier) (k : ℤ)).obj
        ((deRhamAbelianComplexInt B D).X (k : ℤ)) :=
  HomologicalComplex.mkHomToSingle
    ((((abelianisationFunctor (A := A)).obj (deRhamGradedPiece B D k)).extendXIso
          embeddingUpNat (i := k) (i' := (k : ℤ)) rfl).hom ≫
      (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) k
            ((deRhamComplex B D).X k)).hom ≫
        (deRhamAbelianIntXIsoNat B D k).inv)
    fun i hi => (isZero_gradedPieceAbelian_X B D k i
      (by change i + 1 = (k : ℤ) at hi; omega)).eq_of_src _ _

/-- The degree-`k` component of the comparison of the two presentations of the bottom graded
piece. -/
@[simp]
theorem gradedPieceComplexHom_f (k : ℕ) :
    (gradedPieceComplexHom B D k).f (k : ℤ) =
      (((abelianisationFunctor (A := A)).obj (deRhamGradedPiece B D k)).extendXIso
            embeddingUpNat (i := k) (i' := (k : ℤ)) rfl).hom ≫
        (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) k
              ((deRhamComplex B D).X k)).hom ≫
          (deRhamAbelianIntXIsoNat B D k).inv ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (k : ℤ)
              ((deRhamAbelianComplexInt B D).X (k : ℤ))).inv := by
  rw [gradedPieceComplexHom, HomologicalComplex.mkHomToSingle_f]
  simp only [Category.assoc]

/-- **The two presentations of the bottom graded piece agree**, as bounded-below complexes of
abelian sheaves: the comparison is an isomorphism, being one in degree `k` and a morphism between
zero objects in every other degree. -/
def gradedPiecePlusIso (k : ℕ) :
    modulePlus (A := A) (deRhamGradedPiece B D k) ≅ gradedPieceComplexPlus B D (k : ℤ) := by
  haveI hcomp : ∀ n : ℤ, IsIso ((gradedPieceComplexHom B D k).f n) := by
    intro n
    by_cases hn : n = (k : ℤ)
    · subst hn
      rw [gradedPieceComplexHom_f]
      have h1 : IsIso ((((abelianisationFunctor (A := A)).obj
          (deRhamGradedPiece B D k)).extendXIso
            embeddingUpNat (i := k) (i' := (k : ℤ)) rfl).hom) := inferInstance
      -- The image of an isomorphism under a functor is one, but only `Functor.mapIso` says so
      -- in a form instance search can use: there is no instance matching `IsIso (F.map f)`.
      have h2 : IsIso ((_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) k
            ((deRhamComplex B D).X k)).hom) :=
        ((_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) k
            ((deRhamComplex B D).X k))).isIso_hom
      have h3 : IsIso (deRhamAbelianIntXIsoNat B D k).inv := inferInstance
      have h4 : IsIso ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (k : ℤ)
          ((deRhamAbelianComplexInt B D).X (k : ℤ))).inv) := inferInstance
      infer_instance
    · refine ⟨(HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (k : ℤ) _ n hn).to_
        _, ?_, ?_⟩
      · exact (isZero_gradedPieceAbelian_X B D k n hn).eq_of_src _ _
      · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (k : ℤ) _ n
          hn).eq_of_src _ _
  haveI : IsIso ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map
      (⟨gradedPieceComplexHom B D k⟩ :
        modulePlus (A := A) (deRhamGradedPiece B D k) ⟶
          gradedPieceComplexPlus B D (k : ℤ))) := by
    change IsIso (gradedPieceComplexHom B D k)
    exact HomologicalComplex.Hom.isIso_of_components _
  haveI := isIso_of_fully_faithful (CochainComplex.Plus.ι (AbelianSheaf X.carrier))
    (⟨gradedPieceComplexHom B D k⟩ :
      modulePlus (A := A) (deRhamGradedPiece B D k) ⟶ gradedPieceComplexPlus B D (k : ℤ))
  exact asIso (⟨gradedPieceComplexHom B D k⟩ :
    modulePlus (A := A) (deRhamGradedPiece B D k) ⟶ gradedPieceComplexPlus B D (k : ℤ))

/-- The projection onto the bottom graded piece, read in abelian sheaves and followed back into
`Ω^k`, is the inclusion `(σ^{≥k}Ω^•)^k ⟶ Ω^k`. Stated with the trailing morphism explicit, so
that it applies where a reassociation cannot be rewritten. -/
private lemma toSheaf_map_brutalπ_comp (k : ℕ) {Z : AbelianSheaf X.carrier}
    (g : (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).obj
      ((deRhamComplex B D).X k) ⟶ Z) :
    (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map
          ((deRhamBrutalπ B D k).f k) ≫
        (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) k
              ((deRhamComplex B D).X k)).hom ≫ g =
      (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map
          ((CochainComplex.ιBrutal (deRhamComplex B D) k).f k) ≫ g :=
  ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g)
          ((_root_.SheafOfModules.toSheaf.{u, u, u, u}
            (underlyingRingSheaf A)).map_comp _ _).symm)).trans
    (congrArg
      (fun z => (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map z ≫ g)
      (CochainComplex.brutalπ_f_comp_singleObjXSelf (deRhamComplex B D) k))

/-- **The projection onto the bottom graded piece agrees in the two presentations.** The
comparison `AlgebraicGeometry.SheafOfModules.brutalTruncationPlus` of the two presentations of
`σ^{≥k}Ω^•`, followed by the projection
`AlgebraicGeometry.SheafOfModules.gradedPieceProjectionPlus` of the step of the Hodge filtration
onto its bottom graded piece, is the projection
`AlgebraicGeometry.SheafOfModules.deRhamBrutalπ` of the brutal presentation followed by the
comparison `AlgebraicGeometry.SheafOfModules.gradedPiecePlusIso` of the two presentations of that
graded piece.

Both sides are morphisms into a complex concentrated in degree `k`, so they agree as soon as
their degree-`k` components do, and there both are the inclusion `(σ^{≥k}Ω^•)^k ⟶ Ω^k` read in
abelian sheaves. -/
theorem brutalTruncationPlus_gradedPieceProjectionPlus (k : ℕ) :
    brutalTruncationPlus B D k (k : ℤ) le_rfl ≫ gradedPieceProjectionPlus B D (k : ℤ) =
      modulePlusMap (A := A) (deRhamBrutalπ B D k) ≫ (gradedPiecePlusIso B D k).hom := by
  apply (CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map_injective
  show ((deRhamBrutalAbelianIso B D k).hom ≫
      StacksDraft.StupidTruncation.stupidTruncGEMapLE (deRhamAbelianComplexInt B D)
        (le_refl (k : ℤ))) ≫
      StacksDraft.StupidTruncation.stupidTruncGEπ (deRhamAbelianComplexInt B D) (k : ℤ) =
    HomologicalComplex.extendMap
        ((abelianisationFunctor (A := A)).map (deRhamBrutalπ B D k)) embeddingUpNat ≫
      gradedPieceComplexHom B D k
  apply HomologicalComplex.to_single_hom_ext
  -- `abelianisationFunctor` is an elaboration boundary, so
  -- `Functor.mapHomologicalComplex_map_f` no longer matches its components: the lemma is stated
  -- with the category read off the functor's body, at `underlyingRingSheaf A`, and here it is
  -- the declared one, at `Stacks.SheafOfModules.Tensor.ringSheaf A`. The identity itself is
  -- `rfl`, so it is taken here rather than from the simp set.
  have hf : ∀ {K L : CochainComplex
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}
      (ψ : K ⟶ L) (i : ℕ), ((abelianisationFunctor (A := A)).map ψ).f i =
        (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).map (ψ.f i) :=
    fun _ _ => rfl
  have hmap : (StacksDraft.StupidTruncation.stupidTruncGEMapLE (deRhamAbelianComplexInt B D)
      (le_refl (k : ℤ))).f (k : ℤ) = 𝟙 _ := by
    rw [StacksDraft.StupidTruncation.stupidTruncGEMapLE_f _ (le_refl (k : ℤ)) (k : ℤ) le_rfl,
      Iso.hom_inv_id]
  have hι : (deRhamBrutalAbelianIso B D k).hom.f (k : ℤ) ≫
      (StacksDraft.StupidTruncation.stupidTruncGEXIso (deRhamAbelianComplexInt B D) (k : ℤ)
        (k : ℤ) le_rfl).hom =
      (HomologicalComplex.extendMap ((abelianisationFunctor (A := A)).map
        (CochainComplex.ιBrutal (deRhamComplex B D) k)) embeddingUpNat).f (k : ℤ) := by
    rw [← StacksDraft.StupidTruncation.ιStupidTruncGE_f (deRhamAbelianComplexInt B D) (k : ℤ)
        (k : ℤ) le_rfl, ← HomologicalComplex.comp_f, deRhamBrutalAbelianIso_hom_ι]
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hmap, Category.comp_id,
    StacksDraft.StupidTruncation.stupidTruncGEπ_f, ← Category.assoc, hι,
    HomologicalComplex.comp_f, gradedPieceComplexHom_f,
    HomologicalComplex.extendMap_f _ embeddingUpNat (i := k) (i' := (k : ℤ)) rfl,
    HomologicalComplex.extendMap_f _ embeddingUpNat (i := k) (i' := (k : ℤ)) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hf]
  rw [toSheaf_map_brutalπ_comp]

/-- **`H^n(X, Ω^k_{𝒪_X/A}[-k])` in the two presentations of the bottom graded piece.** -/
def gradedPieceCohomologyIso (k : ℕ) (n : ℤ) :
    moduleHypercohomology (A := A) (deRhamGradedPiece B D k) n ≅
      gradedPieceCohomology B D (k : ℤ) n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).mapIso
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.mapIso
      (DerivedCategory.Plus.Q.mapIso (gradedPiecePlusIso B D k)))

/-- **The projection onto the bottom graded piece on hypercohomology, in the two
presentations**: the map `H^n(X, σ^{≥k}Ω^•) ⟶ H^n(X, Ω^k[-k])` of the brutal presentation is the
one of the Hodge filtration, read through the two comparisons. -/
theorem brutalTruncationCohomologyMap_gradedPieceProjection (k : ℕ) (n : ℤ) :
    brutalTruncationCohomologyMap B D k (k : ℤ) le_rfl n ≫
        gradedPieceProjectionCohomologyMap B D (k : ℤ) n =
      moduleHypercohomologyMap (A := A) (deRhamBrutalπ B D k) n ≫
        (gradedPieceCohomologyIso B D k n).hom := by
  simp only [gradedPieceCohomologyIso, CategoryTheory.Functor.mapIso_hom,
    ← CategoryTheory.Functor.map_comp, brutalTruncationPlus_gradedPieceProjectionPlus]

/-! ### The cup products and commutative diagrams of Section 50.7 -/

/-- **Pairings of the hypercohomology of complexes of sheaves of `A`-modules along their
multiplications**, the shape of the cup product of Cohomology, Section 0FKU: for every
multiplication `m : Tot(K ⊗_A L) ⟶ M` of `ℕ`-indexed complexes of
sheaves of `A`-modules, a pairing

`∪ : H^i(X, K) × H^j(X, L) ⟶ H^{i + j}(X, M)`

of the hypercohomology groups of their abelianisations.

The multiplications are taken between complexes of *modules* because that is where the ones of
Section 50.7 live — the wedge product of Tag 0FM2 is `A`-bilinear — while the groups are the
abelian-sheaf ones, because that is where the Hodge-filtered first Chern class lives. The cup
product of Section 0FKU is the pairing
`AlgebraicGeometry.SheafOfModules.canonicalPairing` of this shape. -/
def HypercohomologyPairing :=
  ∀ {K L M : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}
    (_m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M) (i j : ℤ),
      moduleHypercohomology (A := A) K i → moduleHypercohomology (A := A) L j →
        moduleHypercohomology (A := A) M (i + j)

/-- The hypercohomology of the de Rham complex of modules is de Rham cohomology in the
abelian-sheaf realization. -/
theorem moduleHypercohomology_deRhamComplex (n : ℤ) :
    moduleHypercohomology (A := A) (deRhamComplex B D) n = deRhamCohomologyAbelian B D n := rfl

/-- **The cup product `H^i(X, σ^{≥p}Ω^•) × H^j(X, σ^{≥q}Ω^•) ⟶ H^{i + j}(X, σ^{≥(p + q)}Ω^•)`
built from a pairing**: the multiplication of the Hodge filtration of Section 0FM7,
`AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge`, paired by it and read through the
identification `AlgebraicGeometry.SheafOfModules.brutalTruncationCohomologyIso` of the two
presentations of a brutal truncation.

The multiplication of Section 0FM7 is indexed by natural numbers while the steps of the Hodge
filtration are indexed by `ℤ`, so the pairing is formed at `p.toNat` and `q.toNat` and its value
pushed down to the step `p + q`, which `p.toNat + q.toNat` is always at least. For `p` and `q`
nonnegative — the only case in which the classes below are formed — that push is the identity. -/
def cupOfPair (c : HypercohomologyPairing (A := A)) (p q i j : ℤ) :
    truncatedDeRhamCohomologyAbelian B D p i → truncatedDeRhamCohomologyAbelian B D q j →
      truncatedDeRhamCohomologyAbelian B D (p + q) (i + j) := fun x y =>
  (brutalTruncationCohomologyMap B D (p.toNat + q.toNat) (p + q) (by omega) (i + j)).hom
    (c (hodgeFiltrationWedge B D p.toNat q.toNat) i j
      ((brutalTruncationCohomologyIso B D p i).inv.hom x)
      ((brutalTruncationCohomologyIso B D q j).inv.hom y))

/-- **A natural pairing of hypercohomology groups along multiplications of complexes.**

A term of this structure provides, for every multiplication `m : Tot(K ⊗_A L) ⟶ M` of
`ℕ`-indexed complexes of sheaves of `A`-modules, a pairing
`H^i(X, K) × H^j(X, L) ⟶ H^{i + j}(X, M)`, natural in the three complexes. From it the products
of Section 50.7 (Tag 0FM7) on the hypercohomology of the brutal truncations, on de Rham cohomology
and on the graded pieces are *defined* below, the multiplications being
`AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge`, the wedge product of Tag 0FM2 and
`AlgebraicGeometry.SheafOfModules.gradedPieceWedge`, and both commutative diagrams are *proved*,
in `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.truncationMap_cup` and
`AlgebraicGeometry.SheafOfModules.TruncationCupProduct.gradedPieceMap_cup`.

The cup product of the source, Cohomology, Section 0FKU, is the term
`AlgebraicGeometry.SheafOfModules.truncationCupProduct` of
`StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProduct`, built from the
canonical global cup product of the ringed space `(X, A)`.

**This structure is also inhabited by the zero pairing.** Taking `pair m i j x y = 0` satisfies
`pair_naturality`, since every map on hypercohomology is a homomorphism of abelian groups. So a
statement proved below for an arbitrary term says something about the cup product of the source
only once it is specialised to `truncationCupProduct`, which is why the statements of Section
50.7 and of Remark 50.9.2 are registered on those specialisations and not here. -/
structure TruncationCupProduct where
  /-- The pairing of hypercohomology groups attached to a multiplication of complexes. -/
  pair : HypercohomologyPairing (A := A)
  /-- **The pairing is natural**: restricting the two factors along `f` and `g` and the product
  along `h` are compatible whenever the multiplications are. It is what the commutative diagrams
  of Section 50.7 are deduced from. -/
  pair_naturality {K K' L L' M M' : CochainComplex
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}
      (f : K ⟶ K') (g : L ⟶ L')
      (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
      (m' : ((tensorBifunctorNat (A := A)).obj K').obj L' ⟶ M') (h : M ⟶ M')
      (hm : m ≫ h = ((tensorBifunctorNat (A := A)).obj K).map g ≫
        ((tensorBifunctorNat (A := A)).map f).app L' ≫ m')
      (i j : ℤ) (x : moduleHypercohomology (A := A) K i)
      (y : moduleHypercohomology (A := A) L j) :
    (moduleHypercohomologyMap (A := A) h (i + j)).hom (pair m i j x y) =
      pair m' i j ((moduleHypercohomologyMap (A := A) f i).hom x)
        ((moduleHypercohomologyMap (A := A) g j).hom y)

/-- The cup product `H^i(X, σ^{≥p}Ω^•) × H^j(X, σ^{≥q}Ω^•) ⟶ H^{i + j}(X, σ^{≥(p + q)}Ω^•)`
induced by the multiplication of brutal truncations. -/
def TruncationCupProduct.cup (s : TruncationCupProduct (A := A)) (p q i j : ℤ) :
    truncatedDeRhamCohomologyAbelian B D p i →
    truncatedDeRhamCohomologyAbelian B D q j →
      truncatedDeRhamCohomologyAbelian B D (p + q) (i + j) :=
  cupOfPair B D s.pair p q i j

/-- The cup product `H^i_{dR} × H^j_{dR} ⟶ H^{i + j}_{dR}` on de Rham cohomology, in the
abelian-sheaf realization in which the Hodge-filtered first Chern class lives: the pairing along
the wedge product of Tag 0FM2. -/
def TruncationCupProduct.cupDeRham (s : TruncationCupProduct (A := A)) (i j : ℤ) :
    deRhamCohomologyAbelian B D i → deRhamCohomologyAbelian B D j →
    deRhamCohomologyAbelian B D (i + j) := fun x y => s.pair (wedgeProduct B D) i j x y

/-- **The inclusions of the brutal truncations into the de Rham complex are multiplicative**, for
every natural pairing: the commutative diagram of Section 50.7, which for the cup product of the
source is
`AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelianMap_hodgeFiltrationCup`. -/
theorem TruncationCupProduct.truncationMap_cup (s : TruncationCupProduct (A := A)) (p q i j : ℤ)
    (x : truncatedDeRhamCohomologyAbelian B D p i)
    (y : truncatedDeRhamCohomologyAbelian B D q j) :
    (truncatedDeRhamCohomologyAbelianMap B D (p + q) (i + j)).hom
        (TruncationCupProduct.cup B D s p q i j x y) =
      TruncationCupProduct.cupDeRham B D s i j
        ((truncatedDeRhamCohomologyAbelianMap B D p i).hom x)
        ((truncatedDeRhamCohomologyAbelianMap B D q j).hom y) := by
  have hp : p ≤ ((p.toNat : ℕ) : ℤ) := by omega
  have hq : q ≤ ((q.toNat : ℕ) : ℤ) := by omega
  have hpq : p + q ≤ ((p.toNat + q.toNat : ℕ) : ℤ) := by omega
  have hcomm : hodgeFiltrationWedge B D p.toNat q.toNat ≫
      CochainComplex.ιBrutal (deRhamComplex B D) (p.toNat + q.toNat) =
      ((tensorBifunctorNat (A := A)).obj (deRhamBrutal B D p.toNat)).map
          (CochainComplex.ιBrutal (deRhamComplex B D) q.toNat) ≫
        ((tensorBifunctorNat (A := A)).map
          (CochainComplex.ιBrutal (deRhamComplex B D) p.toNat)).app (deRhamComplex B D) ≫
            wedgeProduct B D := by
    rw [hodgeFiltrationWedge_ιBrutal]
    rfl
  have hfac : ∀ (r n : ℤ) (hr : r ≤ ((r.toNat : ℕ) : ℤ))
      (z : truncatedDeRhamCohomologyAbelian B D r n),
      (moduleHypercohomologyMap (A := A)
          (CochainComplex.ιBrutal (deRhamComplex B D) r.toNat) n).hom
        ((brutalTruncationCohomologyIso B D r n).inv.hom z) =
        (truncatedDeRhamCohomologyAbelianMap B D r n).hom z := by
    intro r n hr z
    rw [moduleHypercohomologyMap_ιBrutal B D r.toNat r hr n]
    show (truncatedDeRhamCohomologyAbelianMap B D r n).hom
      ((brutalTruncationCohomologyMap B D r.toNat r hr n).hom
        ((brutalTruncationCohomologyIso B D r n).inv.hom z)) = _
    rw [brutalTruncationCohomologyMap_apply_inv B D r n hr z]
  have htop : ∀ z : moduleHypercohomology (A := A)
        (deRhamBrutal B D (p.toNat + q.toNat)) (i + j),
      (truncatedDeRhamCohomologyAbelianMap B D (p + q) (i + j)).hom
          ((brutalTruncationCohomologyMap B D (p.toNat + q.toNat) (p + q) hpq (i + j)).hom z) =
        (moduleHypercohomologyMap (A := A)
          (CochainComplex.ιBrutal (deRhamComplex B D) (p.toNat + q.toNat)) (i + j)).hom z := by
    intro z
    rw [moduleHypercohomologyMap_ιBrutal B D (p.toNat + q.toNat) (p + q) hpq (i + j)]
    rfl
  show (truncatedDeRhamCohomologyAbelianMap B D (p + q) (i + j)).hom
      ((brutalTruncationCohomologyMap B D (p.toNat + q.toNat) (p + q) hpq (i + j)).hom
        (s.pair (hodgeFiltrationWedge B D p.toNat q.toNat) i j
          ((brutalTruncationCohomologyIso B D p i).inv.hom x)
          ((brutalTruncationCohomologyIso B D q j).inv.hom y))) =
    s.pair (wedgeProduct B D) i j ((truncatedDeRhamCohomologyAbelianMap B D p i).hom x)
      ((truncatedDeRhamCohomologyAbelianMap B D q j).hom y)
  rw [htop, s.pair_naturality _ _ _ (wedgeProduct B D) _ hcomm, hfac p i hp, hfac q j hq]

/-- **The cup product
`H^i(X, Ω^p[-p]) × H^j(X, Ω^q[-q]) ⟶ H^{i + j}(X, Ω^{p + q}[-(p + q)])` on the bottom graded
pieces of the Hodge filtration**, at natural-number filtration indices: the multiplication
`AlgebraicGeometry.SheafOfModules.gradedPieceWedge` of the graded pieces, paired by the pairing
and read through the identification
`AlgebraicGeometry.SheafOfModules.gradedPieceCohomologyIso` of the two presentations of a graded
piece.

The filtration indices are natural numbers, read into `ℤ` through the parameters `p` and `q`
constrained by `hp` and `hq`, so that a caller reading them off
`AlgebraicGeometry.SheafOfModules.cupLength` obtains the product in exactly the groups it is
holding, with no transport. -/
def TruncationCupProduct.cupGradedPiece (s : TruncationCupProduct (A := A)) (a b : ℕ) (p q : ℤ)
    (hp : (a : ℤ) = p) (hq : (b : ℤ) = q) (i j : ℤ) :
    gradedPieceCohomology B D p i → gradedPieceCohomology B D q j →
      gradedPieceCohomology B D (p + q) (i + j) := by
  subst hp
  subst hq
  exact fun x y =>
    (gradedPieceCohomologyIso B D (a + b) (i + j)).hom.hom
      (s.pair (gradedPieceWedge B D a b) i j
        ((gradedPieceCohomologyIso B D a i).inv.hom x)
        ((gradedPieceCohomologyIso B D b j).inv.hom y))

/-- The cup product on the graded pieces at the indices it is built at. -/
theorem TruncationCupProduct.cupGradedPiece_natCast (s : TruncationCupProduct (A := A)) (a b : ℕ)
    (i j : ℤ) (x : gradedPieceCohomology B D (a : ℤ) i)
    (y : gradedPieceCohomology B D (b : ℤ) j) :
    TruncationCupProduct.cupGradedPiece B D s a b (a : ℤ) (b : ℤ) rfl rfl i j x y =
      (gradedPieceCohomologyIso B D (a + b) (i + j)).hom.hom
        (s.pair (gradedPieceWedge B D a b) i j
          ((gradedPieceCohomologyIso B D a i).inv.hom x)
          ((gradedPieceCohomologyIso B D b j).inv.hom y)) :=
  rfl

/-- **The projections of the brutal truncations onto their bottom graded pieces are
multiplicative**, for every natural pairing.

The multiplication of Section 0FM7 composed with the projection onto the
bottom graded piece is the two projections tensored followed by the multiplication of the graded
pieces (`AlgebraicGeometry.SheafOfModules.gradedPieceWedge_comm`), so the naturality of the
pairing turns that identity of complexes into this identity of classes; the
projection onto the bottom graded piece is the same map in the two presentations by
`AlgebraicGeometry.SheafOfModules.brutalTruncationCohomologyMap_gradedPieceProjection`. -/
theorem TruncationCupProduct.gradedPieceMap_cup (s : TruncationCupProduct (A := A)) (a b : ℕ)
    (p q : ℤ) (hp : (a : ℤ) = p) (hq : (b : ℤ) = q) (i j : ℤ)
    (x : truncatedDeRhamCohomologyAbelian B D p i)
    (y : truncatedDeRhamCohomologyAbelian B D q j) :
    (gradedPieceProjectionCohomologyMap B D (p + q) (i + j)).hom
        (cupOfPair B D s.pair p q i j x y) =
      TruncationCupProduct.cupGradedPiece B D s a b p q hp hq i j
        ((gradedPieceProjectionCohomologyMap B D p i).hom x)
        ((gradedPieceProjectionCohomologyMap B D q j).hom y) := by
  subst hp
  subst hq
  have hfac : ∀ (k : ℕ) (n : ℤ) (z : truncatedDeRhamCohomologyAbelian B D (k : ℤ) n),
      (moduleHypercohomologyMap (A := A) (deRhamBrutalπ B D k) n).hom
          ((brutalTruncationCohomologyIso B D (k : ℤ) n).inv.hom z) =
        (gradedPieceCohomologyIso B D k n).inv.hom
          ((gradedPieceProjectionCohomologyMap B D (k : ℤ) n).hom z) := by
    intro k n z
    have hz : (brutalTruncationCohomologyMap B D k (k : ℤ) le_rfl n).hom
        ((brutalTruncationCohomologyIso B D (k : ℤ) n).inv.hom z) = z :=
      brutalTruncationCohomologyMap_apply_inv B D (k : ℤ) n le_rfl z
    have key : (gradedPieceCohomologyIso B D k n).hom.hom
        ((moduleHypercohomologyMap (A := A) (deRhamBrutalπ B D k) n).hom
          ((brutalTruncationCohomologyIso B D (k : ℤ) n).inv.hom z)) =
        (gradedPieceProjectionCohomologyMap B D (k : ℤ) n).hom z := by
      have h := ConcreteCategory.congr_hom
        (brutalTruncationCohomologyMap_gradedPieceProjection B D k n)
        ((brutalTruncationCohomologyIso B D (k : ℤ) n).inv.hom z)
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hz] at h
      exact h.symm
    rw [← key]
    simp
  rw [TruncationCupProduct.cupGradedPiece_natCast]
  show (gradedPieceProjectionCohomologyMap B D ((a + b : ℕ) : ℤ) (i + j)).hom
      ((brutalTruncationCohomologyMap B D (a + b) ((a + b : ℕ) : ℤ) le_rfl (i + j)).hom
        (s.pair (hodgeFiltrationWedge B D a b) i j
          ((brutalTruncationCohomologyIso B D (a : ℤ) i).inv.hom x)
          ((brutalTruncationCohomologyIso B D (b : ℤ) j).inv.hom y))) =
    (gradedPieceCohomologyIso B D (a + b) (i + j)).hom.hom
      (s.pair (gradedPieceWedge B D a b) i j
        ((gradedPieceCohomologyIso B D a i).inv.hom
          ((gradedPieceProjectionCohomologyMap B D (a : ℤ) i).hom x))
        ((gradedPieceCohomologyIso B D b j).inv.hom
          ((gradedPieceProjectionCohomologyMap B D (b : ℤ) j).hom y)))
  rw [← hfac a i x, ← hfac b j y, ← s.pair_naturality (deRhamBrutalπ B D a)
    (deRhamBrutalπ B D b) (hodgeFiltrationWedge B D a b) (gradedPieceWedge B D a b)
    (deRhamBrutalπ B D (a + b)) (gradedPieceWedge_comm B D a b) i j]
  simpa using ConcreteCategory.congr_hom
    (brutalTruncationCohomologyMap_gradedPieceProjection B D (a + b) (i + j))
    (s.pair (hodgeFiltrationWedge B D a b) i j
      ((brutalTruncationCohomologyIso B D (a : ℤ) i).inv.hom x)
      ((brutalTruncationCohomologyIso B D (b : ℤ) j).inv.hom y))

/-! ### The Hodge filtration is multiplicative on de Rham cohomology -/

/-- **Every element of the `p`-th step `F^pH^n_{dR}(X/S)` of the Hodge filtration is the image of
a class on the brutal truncation.** The step is by definition the image of
`H^n(X, σ^{≥p}Ω^•) ⟶ H^n_{dR}`, and the factorisation of a morphism through its image is an
epimorphism, hence a surjection of abelian groups. -/
theorem exists_eq_truncatedDeRhamCohomologyAbelianMap (p n : ℤ)
    (z : (hodgeFiltrationAbelian B D p n : AddCommGrpCat.{u})) :
    ∃ x : truncatedDeRhamCohomologyAbelian B D p n,
      (truncatedDeRhamCohomologyAbelianMap B D p n).hom x =
        ((hodgeFiltrationAbelian B D p n).arrow).hom z := by
  obtain ⟨x, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
    (factorThruImageSubobject (truncatedDeRhamCohomologyAbelianMap B D p n))).mp
      inferInstance z
  exact ⟨x, (ConcreteCategory.congr_hom
    (imageSubobject_arrow_comp (truncatedDeRhamCohomologyAbelianMap B D p n)) x).symm⟩

/-- **The image of a class on the brutal truncation lies in the `p`-th step `F^pH^n_{dR}(X/S)` of
the Hodge filtration**, that step being the image of `H^n(X, σ^{≥p}Ω^•) ⟶ H^n_{dR}`: the witness
is the class pushed into the image. -/
theorem truncatedDeRhamCohomologyAbelianMap_mem_hodgeFiltrationAbelian (p n : ℤ)
    (z : truncatedDeRhamCohomologyAbelian B D p n) :
    ∃ w : (hodgeFiltrationAbelian B D p n : AddCommGrpCat.{u}),
      ((hodgeFiltrationAbelian B D p n).arrow).hom w =
        (truncatedDeRhamCohomologyAbelianMap B D p n).hom z :=
  ⟨(factorThruImageSubobject (truncatedDeRhamCohomologyAbelianMap B D p n)).hom z,
    ConcreteCategory.congr_hom
      (imageSubobject_arrow_comp (truncatedDeRhamCohomologyAbelianMap B D p n)) z⟩

/-- **The Hodge filtration on de Rham cohomology is multiplicative** for the product attached to
every natural pairing,

`F^iH^n_{dR}(X/S) ∪ F^jH^m_{dR}(X/S) ⊆ F^{i + j}H^{n + m}_{dR}(X/S)`.

This is what the source draws from the commutative diagram
`AlgebraicGeometry.SheafOfModules.TruncationCupProduct.truncationMap_cup`, and it is proved from
it here. The two factors are classes on the brutal truncations by
`AlgebraicGeometry.SheafOfModules.exists_eq_truncatedDeRhamCohomologyAbelianMap`, the diagram
rewrites the cup product of their images as the image of their cup product on
`σ^{≥(i + j)}Ω^•_{𝒪_X/A}`, and the step `F^{i + j}` contains that image by
`AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelianMap_mem_hodgeFiltrationAbelian`.

Membership in a step is written as in
`AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian_mem_hodgeFiltrationAbelian`, the
step `AlgebraicGeometry.SheafOfModules.hodgeFiltrationAbelian` of Tag 0FM8 being a subobject of
`H^n_{dR}` and a class lying in it meaning that it is the image of an element of that
subobject. -/
theorem TruncationCupProduct.cupDeRham_mem_hodgeFiltrationAbelian
    (s : TruncationCupProduct (A := A)) (p q i j : ℤ)
    (x : deRhamCohomologyAbelian B D i) (y : deRhamCohomologyAbelian B D j)
    (hx : ∃ u : (hodgeFiltrationAbelian B D p i : AddCommGrpCat.{u}),
      ((hodgeFiltrationAbelian B D p i).arrow).hom u = x)
    (hy : ∃ v : (hodgeFiltrationAbelian B D q j : AddCommGrpCat.{u}),
      ((hodgeFiltrationAbelian B D q j).arrow).hom v = y) :
    ∃ w : (hodgeFiltrationAbelian B D (p + q) (i + j) : AddCommGrpCat.{u}),
      ((hodgeFiltrationAbelian B D (p + q) (i + j)).arrow).hom w =
        TruncationCupProduct.cupDeRham B D s i j x y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  obtain ⟨x', hx'⟩ := exists_eq_truncatedDeRhamCohomologyAbelianMap B D p i u
  obtain ⟨y', hy'⟩ := exists_eq_truncatedDeRhamCohomologyAbelianMap B D q j v
  rw [← hx', ← hy', ← TruncationCupProduct.truncationMap_cup B D s]
  exact truncatedDeRhamCohomologyAbelianMap_mem_hodgeFiltrationAbelian B D (p + q) (i + j)
    (TruncationCupProduct.cup B D s p q i j x' y')

/-! ### The degrees of an `a`-fold product -/

/-- The filtration index of a product of `k + 1` first Chern classes, namely `k + 1`, written in
the shape in which the recursion of
`AlgebraicGeometry.SheafOfModules.filteredChernProduct` builds it. -/
def cupLength : ℕ → ℤ
  | 0 => 1
  | (k + 1) => 1 + cupLength k

/-- The cohomological degree of a product of `k + 1` first Chern classes, namely `2(k + 1)`,
written in the shape in which the recursion of
`AlgebraicGeometry.SheafOfModules.filteredChernProduct` builds it. -/
def cupDegree : ℕ → ℤ
  | 0 => 2
  | (k + 1) => 2 + cupDegree k

/-- The filtration index of a product of `a = k + 1` first Chern classes is `a`. -/
theorem cupLength_eq (k : ℕ) : cupLength k = (k : ℤ) + 1 := by
  induction k with
  | zero => simp [cupLength]
  | succ k ih => rw [cupLength, ih]; push_cast; ring

/-- The cohomological degree of a product of `a = k + 1` first Chern classes is `2a`. -/
theorem cupDegree_eq (k : ℕ) : cupDegree k = 2 * ((k : ℤ) + 1) := by
  induction k with
  | zero => simp [cupDegree]
  | succ k ih => rw [cupDegree, ih]; push_cast; ring

/-- The filtration index of a product of `a = k + 1` first Chern classes is the number of
factors, in the form in which
`AlgebraicGeometry.SheafOfModules.gradedPieceCohomologyIsoHodgeCohomology` asks for it. -/
theorem cast_eq_cupLength (k : ℕ) : ((k + 1 : ℕ) : ℤ) = cupLength k := by
  rw [cupLength_eq]; push_cast; ring

/-- The cohomological degree of a product of `a = k + 1` first Chern classes is twice its
filtration index, in the form in which
`AlgebraicGeometry.SheafOfModules.gradedPieceCohomologyIsoHodgeCohomology` asks for it. -/
theorem cupLength_add_cupLength (k : ℕ) : cupLength k + cupLength k = cupDegree k := by
  rw [cupLength_eq, cupDegree_eq]; ring

/-! ### Relabelling the bottom graded piece in degree one -/

/-- The relabelling `(Ω^•)¹[-1] ⟶ Ω¹[-1]` of the bottom graded piece in degree one: the
identification of the degree-one term of the extended complex with `Ω¹`, placed in cohomological
degree one. -/
abbrev gradedPieceOneRelabel :
    gradedPieceComplexPlus B D 1 ⟶ degreeOneComplexPlus B D :=
  ⟨(CochainComplex.singleFunctor (AbelianSheaf X.carrier) 1).map
    (deRhamAbelianIntXIsoOne B D).hom⟩

/-- The inverse relabelling `Ω¹[-1] ⟶ (Ω^•)¹[-1]`. -/
abbrev gradedPieceOneRelabelInv :
    degreeOneComplexPlus B D ⟶ gradedPieceComplexPlus B D 1 :=
  ⟨(CochainComplex.singleFunctor (AbelianSheaf X.carrier) 1).map
    (deRhamAbelianIntXIsoOne B D).inv⟩

/-- The two relabellings are mutually inverse. -/
theorem gradedPieceOneRelabel_comp :
    gradedPieceOneRelabel B D ≫ gradedPieceOneRelabelInv B D = 𝟙 _ := by
  apply (CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map_injective
  have h : (CochainComplex.singleFunctor (AbelianSheaf X.carrier) 1).map
        (deRhamAbelianIntXIsoOne B D).hom ≫
      (CochainComplex.singleFunctor (AbelianSheaf X.carrier) 1).map
        (deRhamAbelianIntXIsoOne B D).inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id]
    exact (CochainComplex.singleFunctor (AbelianSheaf X.carrier) 1).map_id _
  exact h

/-- The relabelling of the degree-one graded piece, on degree-two hypercohomology. -/
abbrev gradedPieceOneRelabelCohomologyMap :
    gradedPieceCohomology B D 1 2 ⟶ degreeOneShiftedCohomologyTwo B D :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (gradedPieceOneRelabel B D)))

/-- The inverse relabelling of the degree-one graded piece, on degree-two hypercohomology. -/
abbrev gradedPieceOneRelabelInvCohomologyMap :
    degreeOneShiftedCohomologyTwo B D ⟶ gradedPieceCohomology B D 1 2 :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (gradedPieceOneRelabelInv B D)))

/-- The two relabellings are mutually inverse on hypercohomology, being so on complexes. -/
theorem gradedPieceOneRelabelCohomologyMap_comp :
    gradedPieceOneRelabelCohomologyMap B D ≫ gradedPieceOneRelabelInvCohomologyMap B D = 𝟙 _ := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, gradedPieceOneRelabel_comp,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

/-- **The projection onto the bottom graded piece in degree one is the one of
`AlgebraicGeometry.SheafOfModules.degreeOneProjection`**, up to the relabelling of the degree-one
term of the extended complex as `Ω¹`. The `p = 1` case of
`AlgebraicGeometry.SheafOfModules.gradedPieceProjection` is by construction the brutal projection
`StacksDraft.StupidTruncation.stupidTruncGEπ` that `degreeOneProjection` is built from. -/
theorem gradedPieceProjectionPlus_relabel :
    gradedPieceProjectionPlus B D 1 ≫ gradedPieceOneRelabel B D = degreeOneProjectionPlus B D :=
  rfl

/-- The map on degree-two hypercohomology induced by `degreeOneProjection` factors through the one
induced by the `p = 1` case of `gradedPieceProjection`. -/
theorem degreeOneProjectionCohomologyMap_eq :
    degreeOneProjectionCohomologyMap B D =
      gradedPieceProjectionCohomologyMap B D 1 2 ≫ gradedPieceOneRelabelCohomologyMap B D := by
  have h : DerivedCategory.Plus.Q.map (gradedPieceProjectionPlus B D 1) ≫
      DerivedCategory.Plus.Q.map (gradedPieceOneRelabel B D) =
      DerivedCategory.Plus.Q.map (degreeOneProjectionPlus B D) := by
    rw [← Functor.map_comp, gradedPieceProjectionPlus_relabel]
  calc degreeOneProjectionCohomologyMap B D
      = (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
          ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map (gradedPieceProjectionPlus B D 1) ≫
              DerivedCategory.Plus.Q.map (gradedPieceOneRelabel B D))) := by rw [h]
    _ = _ := by rw [Functor.map_comp, Functor.map_comp]

/-! ### The `a`-fold products -/

section Classes

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-- **`c₁^{Hodge}(L) ∈ H¹(X, Ω¹_{𝒪_X/A})` read in `H²(X, (Ω^•)¹[-1])`**, the group that the
projection of `γ₁(L)` onto the bottom graded piece lands in: the relabelling of `Ω¹` as the
degree-one term of the extended complex, followed by the identification
`H¹(X, F) ≅ H²(X, F[-1])` of
`AlgebraicGeometry.SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo`.

It *is* the projection of `γ₁(L)`, by
`AlgebraicGeometry.SheafOfModules.gradedPieceProjectionCohomologyMap_filteredFirstChernClass`;
this spelling is the one in which the `a`-fold Hodge product below is formed. -/
def hodgeFirstChernClassGraded
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    gradedPieceCohomology B D 1 2 :=
  (sheafCohomologyOneIsoShiftedCohomologyTwo X.carrier
      ((deRhamAbelianComplexInt B D).X 1)).hom.hom
    ((((sectionsFunctor X.carrier ⊤).rightDerived 1).map
      (deRhamAbelianIntXIsoOne B D).inv).hom (hodgeFirstChernClassAbelian B D c))

/-- **The image of `γ₁(L)` under the projection `σ^{≥1}Ω^• ⟶ (Ω^•)¹[-1]` is `c₁^{Hodge}(L)`**,
read in the relabelled group of
`AlgebraicGeometry.SheafOfModules.hodgeFirstChernClassGraded`. This is the `a = 1` clause
`AlgebraicGeometry.SheafOfModules.hodgeFirstChernClassAbelian_eq` with `Ω¹` relabelled as the
degree-one term of the extended de Rham complex: the projection differs from
`degreeOneProjection` by that relabelling, and the identification `H¹(X, F) ≅ H²(X, F[-1])` is
natural in `F`, so the relabelling passes across it. -/
theorem gradedPieceProjectionCohomologyMap_filteredFirstChernClass
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    (gradedPieceProjectionCohomologyMap B D 1 2).hom (filteredFirstChernClass B D c) =
      hodgeFirstChernClassGraded B D c := by
  have step : ∀ x y : degreeOneShiftedCohomologyTwo B D, x = y →
      (gradedPieceOneRelabelInvCohomologyMap B D).hom x =
        (gradedPieceOneRelabelInvCohomologyMap B D).hom y := fun _ _ h => by rw [h]
  have hnat := ConcreteCategory.congr_hom
    (sheafCohomologyOneIsoShiftedCohomologyTwo_hom_naturality
      (deRhamAbelianIntXIsoOne B D).inv) (hodgeFirstChernClassAbelian B D c)
  have hfac := ConcreteCategory.congr_hom (degreeOneProjectionCohomologyMap_eq B D)
    (filteredFirstChernClass B D c)
  have hid := ConcreteCategory.congr_hom (gradedPieceOneRelabelCohomologyMap_comp B D)
    ((gradedPieceProjectionCohomologyMap B D 1 2).hom (filteredFirstChernClass B D c))
  exact Eq.symm (hnat.trans
    ((step _ _ ((hodgeFirstChernClassAbelian_eq B D c).symm.trans hfac)).trans hid))

variable (s : TruncationCupProduct (A := A))

/-- **The `a`-fold product `γ₁(L₁) ∪ … ∪ γ₁(L_a) ∈ H^{2a}(X, σ^{≥a}Ω^•_{𝒪_X/A})`** of
Hodge-filtered first Chern classes for a natural pairing `s`, for `a = k + 1` invertible modules
with Picard classes `L 0, …, L k`.

The filtration index and the cohomological degree are `AlgebraicGeometry.SheafOfModules.cupLength`
and `AlgebraicGeometry.SheafOfModules.cupDegree`, which `cupLength_eq` and `cupDegree_eq` identify
with `a` and `2a`. For the cup product of the source this is
`AlgebraicGeometry.SheafOfModules.filteredChernProduct`. -/
def TruncationCupProduct.filteredChernProduct : (k : ℕ) →
    (ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) →
      truncatedDeRhamCohomologyAbelian B D (cupLength k) (cupDegree k)
  | 0, L => filteredFirstChernClass B D (L 0)
  | (k + 1), L => TruncationCupProduct.cup B D s 1 (cupLength k) 2 (cupDegree k)
      (filteredFirstChernClass B D (L 0))
      (TruncationCupProduct.filteredChernProduct k (fun i => L (i + 1)))

/-- The `a`-fold product `c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a) ∈ H^{2a}_{dR}(X/S)` of de Rham first
Chern classes for a natural pairing `s`. -/
def TruncationCupProduct.deRhamChernProduct : (k : ℕ) →
    (ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) →
      deRhamCohomologyAbelian B D (cupDegree k)
  | 0, L => deRhamFirstChernClassAbelian B D (L 0)
  | (k + 1), L => TruncationCupProduct.cupDeRham B D s 2 (cupDegree k)
      (deRhamFirstChernClassAbelian B D (L 0))
      (TruncationCupProduct.deRhamChernProduct k (fun i => L (i + 1)))

/-- The `a`-fold product `c₁^{Hodge}(L₁) ∪ … ∪ c₁^{Hodge}(L_a)` of Hodge first Chern classes for a
natural pairing `s`, formed in `H^{2a}(X, Ω^a[-a])`, which is `H^a(X, Ω^a)` by
`gradedPieceCohomologyIsoHodgeCohomology B D (k + 1) (cupLength k) (cupDegree k)
  (cast_eq_cupLength k) (cupLength_add_cupLength k)`. -/
def TruncationCupProduct.hodgeChernProduct : (k : ℕ) →
    (ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) →
      gradedPieceCohomology B D (cupLength k) (cupDegree k)
  | 0, L => hodgeFirstChernClassGraded B D (L 0)
  | (k + 1), L => TruncationCupProduct.cupGradedPiece B D s 1 (k + 1) 1 (cupLength k) rfl
      (cast_eq_cupLength k) 2 (cupDegree k)
      (hodgeFirstChernClassGraded B D (L 0))
      (TruncationCupProduct.hodgeChernProduct k (fun i => L (i + 1)))

/-! ### The images of the `a`-fold product -/

/-- **The image of `γ₁(L₁) ∪ … ∪ γ₁(L_a)` under `σ^{≥a}Ω^• ⟶ Ω^•` is
`c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a)`**, for a natural pairing.

The induction is on the number of factors. For one factor this is
`AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian_eq`; the inductive step is the
commutative diagram `AlgebraicGeometry.SheafOfModules.TruncationCupProduct.truncationMap_cup`,
which says that the inclusion of the truncation is multiplicative. -/
theorem TruncationCupProduct.truncatedDeRhamCohomologyAbelianMap_filteredChernProduct (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    (truncatedDeRhamCohomologyAbelianMap B D (cupLength k) (cupDegree k)).hom
        (TruncationCupProduct.filteredChernProduct B D s k L) =
      TruncationCupProduct.deRhamChernProduct B D s k L := by
  induction k generalizing L with
  | zero => exact (deRhamFirstChernClassAbelian_eq B D (L 0)).symm
  | succ k ih =>
    show (truncatedDeRhamCohomologyAbelianMap B D (1 + cupLength k) (2 + cupDegree k)).hom
        (TruncationCupProduct.cup B D s 1 (cupLength k) 2 (cupDegree k)
          (filteredFirstChernClass B D (L 0))
          (TruncationCupProduct.filteredChernProduct B D s k (fun i => L (i + 1)))) =
      TruncationCupProduct.cupDeRham B D s 2 (cupDegree k) (deRhamFirstChernClassAbelian B D (L 0))
        (TruncationCupProduct.deRhamChernProduct B D s k (fun i => L (i + 1)))
    rw [TruncationCupProduct.truncationMap_cup B D s, ← deRhamFirstChernClassAbelian_eq, ih]

/-- **`c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a)` lies in `F^a H^{2a}_{dR}(X/S)`**, for a natural pairing:
the step `F^a H^{2a}_{dR}` is the image of `H^{2a}(X, σ^{≥a}Ω^•) ⟶ H^{2a}_{dR}`, and
`TruncationCupProduct.truncatedDeRhamCohomologyAbelianMap_filteredChernProduct`
exhibits the product as the image of `γ₁(L₁) ∪ … ∪ γ₁(L_a)` under exactly that map. -/
theorem TruncationCupProduct.deRhamChernProduct_mem_hodgeFiltrationAbelian (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    ∃ y : (hodgeFiltrationAbelian B D (cupLength k) (cupDegree k) : AddCommGrpCat.{u}),
      ((hodgeFiltrationAbelian B D (cupLength k) (cupDegree k)).arrow).hom y =
        TruncationCupProduct.deRhamChernProduct B D s k L := by
  rw [← TruncationCupProduct.truncatedDeRhamCohomologyAbelianMap_filteredChernProduct B D s k L]
  exact truncatedDeRhamCohomologyAbelianMap_mem_hodgeFiltrationAbelian B D _ _ _

/-- **The image of `γ₁(L₁) ∪ … ∪ γ₁(L_a)` under `σ^{≥a}Ω^• ⟶ Ω^a_{𝒪_X/A}[-a]` is
`c₁^{Hodge}(L₁) ∪ … ∪ c₁^{Hodge}(L_a)`**, for a natural pairing.

The induction is on the number of factors. For one factor this is
`AlgebraicGeometry.SheafOfModules.gradedPieceProjectionCohomologyMap_filteredFirstChernClass`;
the inductive step is the commutative diagram
`AlgebraicGeometry.SheafOfModules.TruncationCupProduct.gradedPieceMap_cup`, which says that the
projection onto the bottom graded piece is multiplicative. -/
theorem TruncationCupProduct.gradedPieceProjectionCohomologyMap_filteredChernProduct (k : ℕ)
    (L : ℕ → Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    (gradedPieceProjectionCohomologyMap B D (cupLength k) (cupDegree k)).hom
        (TruncationCupProduct.filteredChernProduct B D s k L) =
      TruncationCupProduct.hodgeChernProduct B D s k L := by
  induction k generalizing L with
  | zero => exact gradedPieceProjectionCohomologyMap_filteredFirstChernClass B D (L 0)
  | succ k ih =>
    show (gradedPieceProjectionCohomologyMap B D (1 + cupLength k) (2 + cupDegree k)).hom
        (cupOfPair B D s.pair 1 (cupLength k) 2 (cupDegree k)
          (filteredFirstChernClass B D (L 0))
          (TruncationCupProduct.filteredChernProduct B D s k (fun i => L (i + 1)))) =
      TruncationCupProduct.cupGradedPiece B D s 1 (k + 1) 1 (cupLength k) rfl
        (cast_eq_cupLength k) 2 (cupDegree k) (hodgeFirstChernClassGraded B D (L 0))
        (TruncationCupProduct.hodgeChernProduct B D s k (fun i => L (i + 1)))
    rw [TruncationCupProduct.gradedPieceMap_cup B D s 1 (k + 1) 1 (cupLength k) rfl
      (cast_eq_cupLength k) 2 (cupDegree k),
      gradedPieceProjectionCohomologyMap_filteredFirstChernClass, ih]

end Classes

end AlgebraicGeometry.SheafOfModules

end
