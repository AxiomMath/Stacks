module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.LogarithmicDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.PicardGroupAndFirstCohomology

/-!
# The first Chern class in Hodge-filtered de Rham cohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a topological space, with
`𝒪_X` the structure sheaf of a ringed space `X` whose stalks are local rings, and let
`Ω^•_{𝒪_X/A}` be the relative de Rham complex. Logarithmic differentiation
`d log u = u⁻¹ · d u` kills the differential, so it is a morphism of complexes of abelian
sheaves

`𝒪_X^*[-1] ⟶ σ^{≥1}Ω^•_{𝒪_X/A}`

from the sheaf of units placed in cohomological degree one into the first step of the Hodge
filtration — the brutal truncation of the de Rham complex in degrees `≥ 1`. Composing the
induced map on degree-two hypercohomology with the identification `Pic(X) = H¹(X, 𝒪_X^*)` of
Stacks Tag 09NU gives the **Hodge-filtered first Chern class**

`γ₁ : Pic(X) ⟶ H²(X, σ^{≥1}Ω^•_{𝒪_X/A})`.

Its image under the inclusion `σ^{≥1}Ω^• ⟶ Ω^•` is the de Rham first Chern class, so
`c₁^{dR}(L)` lies in the first step `F¹H²_{dR}` of the Hodge filtration.

Its image under the projection `σ^{≥1}Ω^• ⟶ Ω¹_{𝒪_X/A}[-1]` onto the bottom graded piece is the
Hodge first Chern class `c₁^{Hodge}(L) ∈ H¹(X, Ω¹_{𝒪_X/A})`.

That is the whole of Tag 0FME for a single invertible module, and it is the whole of what this
file covers.

## What of Tag 0FME is covered here, and where the rest is

Remark 50.9.2 is a list of nine clauses, A–I. **The covering set here is the `a = 1` case,
clauses A–E**; each registration below says in its attribute string or in its docstring
which clause it is. Written
out, the five that are covered are

* **(A)** `d log`, viewed as a map `𝒪_X^*[-1] ⟶ σ^{≥1}Ω^•` — on
  `AlgebraicGeometry.SheafOfModules.filteredLogarithmicDifferentialComplexMap`, which constructs
  it, jointly with
  `AlgebraicGeometry.SheafOfModules.filteredLogarithmicDifferentialComplexMap_ι`, which pins it
  down to `d log`;
* **(B)** the class `γ₁(L) ∈ H²(X, σ^{≥1}Ω^•)` — on
  `AlgebraicGeometry.SheafOfModules.filteredFirstChernClass`;
* **(C)** the image of `γ₁(L)` under `σ^{≥1}Ω^• ⟶ Ω^•` is `c₁^{dR}(L)` — on
  `AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian_eq`;
* **(D)** `c₁^{dR}(L) ∈ F¹H²_{dR}` — on
  `AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian_mem_hodgeFiltrationAbelian`;
* **(E)** the image of `γ₁(L)` under `σ^{≥1}Ω^• ⟶ Ω¹[-1]` is `c₁^{Hodge}(L)` — on
  `AlgebraicGeometry.SheafOfModules.hodgeFirstChernClassAbelian_eq`.

The four `a ≥ 2` cup-product clauses are the subject of the file
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.CanonicalChernCupProduct`, which imports this
one and proves them there for every `a`. They are

* **(F)** `ξ = γ₁(L₁) ∪ … ∪ γ₁(L_a) ∈ H^{2a}(X, σ^{≥a}Ω^•)` —
  `AlgebraicGeometry.SheafOfModules.filteredChernProduct`;
* **(G)** the image of `ξ` under `σ^{≥a}Ω^• ⟶ Ω^•` is `c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a)` in
  `H^{2a}_{dR}` —
  `AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelianMap_filteredChernProduct`;
* **(H)** consequently `c₁^{dR}(L₁) ∪ … ∪ c₁^{dR}(L_a) ∈ F^a H^{2a}_{dR}` —
  `AlgebraicGeometry.SheafOfModules.deRhamChernProduct_mem_hodgeFiltrationAbelian`;
* **(I)** the image of `ξ` under `σ^{≥a}Ω^• ⟶ Ω^a[-a]`, read in `H^a(X, Ω^a)`, is
  `(-1)^{a(a - 1)/2} · c₁^{Hodge}(L₁) ∪ … ∪ c₁^{Hodge}(L_a)` for the Hodge cup product of
  Tag 0FM4, the sign (absent from the source) being the one the identifications force —
  `AlgebraicGeometry.SheafOfModules.hodgeGradedIso_inv_gradedPieceProjection_filteredChernProduct`.

`AlgebraicGeometry.SheafOfModules.remark_filteredFirstChernClass`, in that file, states all nine
clauses at once for every `a`.

What those four clauses need beyond this file is what the source itself cites from its Section
50.7, Tag 0FM7: the cup product on the hypercohomology of the brutal truncations, together with
the two commutative diagrams saying that the inclusion `σ^{≥p}Ω^• ⟶ Ω^•` and the projection
`σ^{≥p}Ω^• ⟶ Ω^p[-p]` are multiplicative. The cup product is
`AlgebraicGeometry.SheafOfModules.hodgeFiltrationCup` of
`StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProduct`, the cup product of
Cohomology, Section 0FKU built from the canonical global cup product, along the multiplication
`AlgebraicGeometry.SheafOfModules.hodgeFiltrationWedge` of the brutal truncations; the cup
products on de Rham cohomology and on the graded pieces are the same construction along the wedge
products. The `a`-fold clauses are proved from the two-factor diagrams by induction on the number
of factors, starting from clauses C and E below.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.unitsComplex`: the sheaf of units placed in cohomological
  degree one, `𝒪_X^*[-1]`.
* `AlgebraicGeometry.SheafOfModules.logarithmicDifferentialComplexMap` and
  `AlgebraicGeometry.SheafOfModules.filteredLogarithmicDifferentialComplexMap`: **logarithmic
  differentiation as a morphism of complexes** `𝒪_X^*[-1] ⟶ Ω^•_{𝒪_X/A}`, and its canonical
  factorization through the brutal truncation `σ^{≥1}Ω^•_{𝒪_X/A}`.
* `AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelian`: the hypercohomology
  `H^n(X, σ^{≥p}Ω^•_{𝒪_X/A})` of a brutal truncation of the de Rham complex of abelian sheaves,
  the group the Hodge filtration of
  `AlgebraicGeometry.SheafOfModules.hodgeFiltrationAbelian` is the image of.
* `AlgebraicGeometry.SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo`: the canonical
  identification `H¹(X, F) ≅ H²(X, F[-1])` of the first cohomology of an abelian sheaf with the
  degree-two hypercohomology of that sheaf placed in degree one.
* `AlgebraicGeometry.SheafOfModules.filteredFirstChernClass`: **the Hodge-filtered first Chern
  class** `γ₁ : Pic(X) ⟶ H²(X, σ^{≥1}Ω^•_{𝒪_X/A})`.
* `AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian`: the de Rham first Chern class
  `c₁^{dR} : Pic(X) ⟶ H²_{dR}`, in the abelian-sheaf realization.
* `AlgebraicGeometry.SheafOfModules.degreeOneProjection`: **the projection
  `σ^{≥1}Ω^•_{𝒪_X/A} ⟶ Ω¹_{𝒪_X/A}[-1]`** of the first step of the Hodge filtration onto its
  bottom graded piece.
* `AlgebraicGeometry.SheafOfModules.hodgeFirstChernClassAbelian`: **the Hodge first Chern class**
  `c₁^{Hodge} : Pic(X) ⟶ H¹(X, Ω¹_{𝒪_X/A})`, in the abelian-sheaf realization.
* `AlgebraicGeometry.SheafOfModules.sheafCohomologyOneNatIsoShiftedCohomologyTwo`: the
  identification `H¹(X, F) ≅ H²(X, F[-1])` before evaluation at a sheaf, which is what makes its
  naturality available.

## Main results

* `AlgebraicGeometry.SheafOfModules.d_logarithmicDifferentialAbelian`: the logarithmic
  differential of a unit is a closed form, read as a morphism of abelian sheaves.
* `AlgebraicGeometry.SheafOfModules.filteredLogarithmicDifferentialComplexMap_ι`: the
  factorization through the truncation composes with the inclusion of the truncation to give
  back the unfiltered logarithmic differential.
* `AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian_eq`: **the de Rham first Chern
  class is the image of the Hodge-filtered one** under the inclusion
  `σ^{≥1}Ω^• ⟶ Ω^•`; in particular `c₁^{dR}(L) ∈ F¹H²_{dR}`, the first step of the Hodge
  filtration being by definition the image of that inclusion on hypercohomology.
* `AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian_mem_hodgeFiltrationAbelian`:
  **`c₁^{dR}(L) ∈ F¹H²_{dR}`**, the first step of the Hodge filtration being by definition the
  image of that inclusion on hypercohomology.
* `AlgebraicGeometry.SheafOfModules.filteredLogarithmicDifferentialComplexMap_degreeOneProjection`:
  the projection onto the bottom graded piece composed with the filtered `d log` is
  `d log : 𝒪_X^*[-1] ⟶ Ω¹_{𝒪_X/A}[-1]`.
* `AlgebraicGeometry.SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo_hom_naturality`:
  the identification `H¹(X, F) ≅ H²(X, F[-1])` is natural in `F`.
* `AlgebraicGeometry.SheafOfModules.hodgeFirstChernClassAbelian_eq`: **the image of `γ₁(L)`
  under `σ^{≥1}Ω^• ⟶ Ω¹_{𝒪_X/A}[-1]` is the Hodge first Chern class `c₁^{Hodge}(L)`.**

## Implementation notes

The construction is carried out in the abelian-sheaf realization of de Rham cohomology of
`StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic`, because `d log` is only a morphism
of sheaves of *abelian groups*: it is additive in the unit but not linear over `𝒪_X`.

Two spellings of the category of sheaves of abelian groups on `X` are in play — `TopCat.Sheaf`,
in which the sheaf of units `Stacks.Cohomology.Generators.unitsSheaf` is stated, and
`Stacks.Cohomology.Leray.AbelianSheaf`, in which the de Rham complex of abelian sheaves is. They
are definitionally equal but carry separate category instances, so the sheaf of units is
relabelled once, as `AlgebraicGeometry.SheafOfModules.unitsAbelianSheaf`, and every morphism out
of it below is formed in the second spelling.

The identification `H¹(X, F) ≅ H²(X, F[-1])` is not constructed here: it is
`Stacks.DerivedIndexing.rightDerivedIso`, which compares Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived` — the one `Pic(X) = H¹(X, 𝒪_X^*)` is stated with — to the
derived-category `CategoryTheory.Functor.rightDerivedPlus`, followed by
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`, which moves the degree of a
single complex across the shift-commuting functor `RΓ(X, -)`.

As everywhere in this group of files, the package `B` of the three algebras of Stacks Section
17.21 and the de Rham differential `D` on it are hypotheses; by
`AlgebraicGeometry.SheafOfModules.deRhamDifferential_unique` the differential is unique, so
nothing below depends on the choice.

## References

* [Stacks Project, Tag 0FME](https://stacks.math.columbia.edu/tag/0FME)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 0FM8](https://stacks.math.columbia.edu/tag/0FM8)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

/-! ### First cohomology of an abelian sheaf as hypercohomology of its shift -/

section Shift

variable (Y : TopCat.{u}) (F : AbelianSheaf Y)

/-- An abelian sheaf placed in cohomological degree one, `F[-1]`, as a bounded-below complex. -/
def singleOneComplexPlus : CochainComplex.Plus (AbelianSheaf Y) :=
  ⟨(CochainComplex.singleFunctor _ 1).obj F, 1, inferInstance⟩

/-- **The first cohomology of an abelian sheaf is the degree-two hypercohomology of that sheaf
placed in cohomological degree one**: `H¹(X, F) ≅ H²(X, F[-1])`.

Both sides are read off the same injective resolution: the left-hand side is Mathlib's
`ℕ`-indexed right derived functor of global sections, which
`Stacks.DerivedIndexing.rightDerivedIso` identifies with the derived-category one, and the
remaining degree shift is `DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso` for
the shift-commuting functor `RΓ(X, -)`. -/
def sheafCohomologyOneIsoShiftedCohomologyTwo :
    ((sectionsFunctor Y ⊤).rightDerived 1).obj F ≅
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).obj
        ((sectionsFunctor Y ⊤).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj (singleOneComplexPlus Y F))) :=
  (Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y ⊤) 1).app F ≪≫
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
      (sectionsFunctor Y ⊤).rightDerivedFunctorPlus 1 1).app F).symm

end Shift

section ShiftNaturality

variable (Y : TopCat.{u})

/-- **`H¹(X, -) ≅ H²(X, (-)[-1])` as an isomorphism of functors.** This is
`AlgebraicGeometry.SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo` assembled from the
two natural isomorphisms it is the composite of, before evaluating at a sheaf; its only purpose
is to make the naturality of that identification available. -/
def sheafCohomologyOneNatIsoShiftedCohomologyTwo :
    (sectionsFunctor Y ⊤).rightDerived 1 ≅
      DerivedCategory.Plus.singleFunctor (AbelianSheaf Y) 1 ⋙
        (sectionsFunctor Y ⊤).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2 :=
  Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y ⊤) 1 ≪≫
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
      (sectionsFunctor Y ⊤).rightDerivedFunctorPlus 1 1).symm

variable {Y}

/-- The functorial identification evaluates to the one used to define the first Chern
classes. -/
theorem sheafCohomologyOneNatIsoShiftedCohomologyTwo_app (F : AbelianSheaf Y) :
    (sheafCohomologyOneNatIsoShiftedCohomologyTwo Y).app F =
      sheafCohomologyOneIsoShiftedCohomologyTwo Y F := rfl

/-- **The identification `H¹(X, F) ≅ H²(X, F[-1])` is natural in the abelian sheaf `F`.** Both
of its two halves are components of natural isomorphisms, so this is their naturality. -/
theorem sheafCohomologyOneIsoShiftedCohomologyTwo_hom_naturality
    {F₁ F₂ : AbelianSheaf Y} (f : F₁ ⟶ F₂) :
    ((sectionsFunctor Y ⊤).rightDerived 1).map f ≫
        (sheafCohomologyOneIsoShiftedCohomologyTwo Y F₂).hom =
      (sheafCohomologyOneIsoShiftedCohomologyTwo Y F₁).hom ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
          ((sectionsFunctor Y ⊤).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf Y) 1).map f)) :=
  (sheafCohomologyOneNatIsoShiftedCohomologyTwo Y).hom.naturality f

end ShiftNaturality

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The logarithmic differential as a morphism of complexes -/

/-- The sheaf of units of a ringed space, written additively and read in the spelling
`Stacks.Cohomology.Leray.AbelianSheaf` of the category of sheaves of abelian groups in which the
de Rham complex of abelian sheaves lives. -/
abbrev unitsAbelianSheaf (X : RingedSpace.{u, u}) : AbelianSheaf X.carrier :=
  Stacks.Cohomology.Generators.unitsSheaf X

/-- `𝒪_X^*[-1]`: the sheaf of units placed in cohomological degree one. -/
abbrev unitsComplex (X : RingedSpace.{u, u}) : CochainComplex (AbelianSheaf X.carrier) ℤ :=
  (CochainComplex.singleFunctor _ 1).obj (unitsAbelianSheaf X)

/-- `𝒪_X^*[-1]` as a bounded-below complex: it is concentrated in degree one. -/
abbrev unitsComplexPlus (X : RingedSpace.{u, u}) : CochainComplex.Plus (AbelianSheaf X.carrier) :=
  singleOneComplexPlus X.carrier (unitsAbelianSheaf X)

/-- The degree-one term of the de Rham complex of abelian sheaves extended by zero to negative
degrees is `Ω¹`, the degree-one term of the complex it is extended from. -/
abbrev deRhamAbelianIntXIsoOne :
    (deRhamAbelianComplexInt B D).X 1 ≅ (deRhamAbelianComplex B D).X 1 :=
  (deRhamAbelianComplex B D).extendXIso embeddingUpNat (i := 1) (i' := 1) rfl

/-- **Logarithmic differentiation as a morphism of sheaves of abelian groups**
`𝒪_X^* ⟶ Ω¹_{𝒪_X/A}`, read in the category of abelian sheaves the de Rham complex of abelian
sheaves lives in. -/
abbrev logarithmicDifferentialAbelianSheafHom :
    unitsAbelianSheaf X ⟶ (deRhamAbelianComplex B D).X 1 :=
  logarithmicDifferentialSheafHom B

/-- **The logarithmic differential of a unit is a closed form**, read as an identity of
morphisms of sheaves of abelian groups: `d log` composed with the de Rham differential out of
degree one vanishes. On local sections this is
`AlgebraicGeometry.SheafOfModules.d_logarithmicDifferential`. -/
theorem d_logarithmicDifferentialAbelian :
    logarithmicDifferentialAbelianSheafHom B D ≫ (deRhamAbelianComplex B D).d 1 2 = 0 := by
  ext U g
  exact d_logarithmicDifferential B D U (Additive.toMul g)

/-- Logarithmic differentiation into the degree-one term of the de Rham complex of abelian
sheaves extended by zero to negative degrees. -/
abbrev logarithmicDifferentialAbelian :
    unitsAbelianSheaf X ⟶ (deRhamAbelianComplexInt B D).X 1 :=
  logarithmicDifferentialAbelianSheafHom B D ≫ (deRhamAbelianIntXIsoOne B D).inv

/-- Closedness of the logarithmic differential, read in the extended complex. -/
theorem logarithmicDifferentialAbelian_comp_d :
    logarithmicDifferentialAbelian B D ≫ (deRhamAbelianComplexInt B D).d 1 2 = 0 := by
  rw [logarithmicDifferentialAbelian, (deRhamAbelianComplex B D).extend_d_eq embeddingUpNat
      (i := 1) (j := 2) (i' := 1) (j' := 2) rfl rfl, Category.assoc,
    ← Category.assoc (deRhamAbelianIntXIsoOne B D).inv, Iso.inv_hom_id, Category.id_comp,
    ← Category.assoc, d_logarithmicDifferentialAbelian, Limits.zero_comp]

/-- **Stacks Project, Tag 0FLE.** **Logarithmic differentiation as a morphism of complexes of
abelian sheaves** `𝒪_X^*[-1] ⟶ Ω^•_{𝒪_X/A}`. There is a single condition to check, that
`d log u` is closed, and it is
`AlgebraicGeometry.SheafOfModules.d_logarithmicDifferentialAbelian`. -/
@[stacks 0FLE "d log as a map of complexes"]
def logarithmicDifferentialComplexMap : unitsComplex X ⟶ deRhamAbelianComplexInt B D :=
  HomologicalComplex.mkHomFromSingle (logarithmicDifferentialAbelian B D) fun k hk ↦ by
    have hk' : (1 : ℤ) + 1 = k := hk
    obtain rfl : k = 2 := by omega
    exact logarithmicDifferentialAbelian_comp_d B D

/-- **Stacks Project, Tag 0FME.** **Logarithmic differentiation as a morphism of complexes into
the first step of the Hodge filtration**, `d log : 𝒪_X^*[-1] ⟶ σ^{≥1}Ω^•_{𝒪_X/A}`.

The source is concentrated in degree one, hence strictly supported in degrees `≥ 1`, so the
morphism `AlgebraicGeometry.SheafOfModules.logarithmicDifferentialComplexMap` into the de Rham
complex factors uniquely through the brutal truncation. -/
@[stacks 0FME "d log as a map to the first step of the Hodge filtration"]
def filteredLogarithmicDifferentialComplexMap :
    unitsComplex X ⟶ (deRhamAbelianComplexInt B D).stupidTrunc (embeddingUpIntGE 1) :=
  StacksDraft.StupidTruncation.liftStupidTrunc (deRhamAbelianComplexInt B D)
    (embeddingUpIntGE 1) (logarithmicDifferentialComplexMap B D)

/-- The factorization of `d log` through the brutal truncation is one: composing it with the
inclusion of the truncation returns the unfiltered logarithmic differential. -/
@[stacks 0FME "Remark 50.9.2, clause A of A-I, the theorem half: the factorization of d log \
through σ^{≥1}Ω^• IS d log, composing with σ^{≥1}Ω^• ⟶ Ω^• back to the unfiltered one. This is \
what pins `filteredLogarithmicDifferentialComplexMap` down to the source's map rather than to \
some morphism into the truncation. The covering set here is the a = 1 case, clauses A-E; \
the a ≥ 2 clauses F-I are proved for every a in \
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.CanonicalChernCupProduct`"]
theorem filteredLogarithmicDifferentialComplexMap_ι :
    filteredLogarithmicDifferentialComplexMap B D ≫
        HomologicalComplex.ιStupidTrunc (deRhamAbelianComplexInt B D)
          (embeddingUpIntGE 1) =
      logarithmicDifferentialComplexMap B D :=
  StacksDraft.StupidTruncation.liftStupidTrunc_ι _ _ _

/-- `d log : 𝒪_X^*[-1] ⟶ σ^{≥1}Ω^•_{𝒪_X/A}` as a morphism of bounded-below complexes. -/
abbrev filteredLogarithmicDifferentialComplexMapPlus :
    unitsComplexPlus X ⟶ deRhamAbelianTruncationPlus B D 1 :=
  ⟨filteredLogarithmicDifferentialComplexMap B D⟩

/-- `d log : 𝒪_X^*[-1] ⟶ Ω^•_{𝒪_X/A}` as a morphism of bounded-below complexes. -/
abbrev logarithmicDifferentialComplexMapPlus :
    unitsComplexPlus X ⟶ deRhamAbelianComplexPlus B D :=
  ⟨logarithmicDifferentialComplexMap B D⟩

/-- The factorization of `d log` through the brutal truncation is one, read on bounded-below
complexes: morphisms of bounded-below complexes are morphisms of the underlying complexes, so
this is `AlgebraicGeometry.SheafOfModules.filteredLogarithmicDifferentialComplexMap_ι`. -/
theorem filteredLogarithmicDifferentialComplexMapPlus_ι :
    filteredLogarithmicDifferentialComplexMapPlus B D ≫ ιDeRhamAbelianTruncationPlus B D 1 =
      logarithmicDifferentialComplexMapPlus B D :=
  CochainComplex.Plus.ι _ |>.map_injective (filteredLogarithmicDifferentialComplexMap_ι B D)

/-! ### Hypercohomology of the filtered de Rham complex -/

/-- **The hypercohomology `H^n(X, σ^{≥p}Ω^•_{𝒪_X/A})` of a brutal truncation of the relative de
Rham complex** of abelian sheaves. The `p`-th step
`AlgebraicGeometry.SheafOfModules.hodgeFiltrationAbelian` of the Hodge filtration is the image
of this group in `H^n_{dR}`. -/
abbrev truncatedDeRhamCohomologyAbelian (p n : ℤ) : AddCommGrpCat.{u} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj (deRhamAbelianTruncationPlus B D p)))

/-- The map `H^n(X, σ^{≥p}Ω^•) ⟶ H^n_{dR}` induced by the inclusion of the brutal truncation.
The Hodge filtration is its image. -/
abbrev truncatedDeRhamCohomologyAbelianMap (p n : ℤ) :
    truncatedDeRhamCohomologyAbelian B D p n ⟶ deRhamCohomologyAbelian B D n :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (ιDeRhamAbelianTruncationPlus B D p)))

/-- The degree-two hypercohomology `H²(X, 𝒪_X^*[-1])` of the sheaf of units placed in degree
one. -/
abbrev shiftedUnitsCohomologyTwo (X : RingedSpace.{u, u}) : AddCommGrpCat.{u} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).obj
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj (unitsComplexPlus X)))

/-- The map `H²(X, 𝒪_X^*[-1]) ⟶ H²(X, σ^{≥1}Ω^•_{𝒪_X/A})` induced by `d log`. -/
abbrev filteredLogarithmicDifferentialCohomologyMap :
    shiftedUnitsCohomologyTwo X ⟶ truncatedDeRhamCohomologyAbelian B D 1 2 :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (filteredLogarithmicDifferentialComplexMapPlus B D)))

/-- The map `H²(X, 𝒪_X^*[-1]) ⟶ H²_{dR}` induced by `d log`. -/
abbrev logarithmicDifferentialCohomologyMap :
    shiftedUnitsCohomologyTwo X ⟶ deRhamCohomologyAbelian B D 2 :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (logarithmicDifferentialComplexMapPlus B D)))

/-- Degree-`n` hypercohomology maps induced by composable morphisms of bounded-below complexes
compose. -/
private theorem map_comp_hypercohomology {Y : TopCat.{u}}
    {P Q R : CochainComplex.Plus (AbelianSheaf Y)} (f : P ⟶ Q) (g : Q ⟶ R) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
        ((sectionsFunctor Y ⊤).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
        ((sectionsFunctor Y ⊤).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g)) =
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
        ((sectionsFunctor Y ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (f ≫ g))) := by
  simp only [← Functor.map_comp]

/-- On degree-two hypercohomology, `d log` into the de Rham complex is `d log` into its first
filtered step followed by the inclusion of that step. -/
theorem logarithmicDifferentialCohomologyMap_eq :
    logarithmicDifferentialCohomologyMap B D =
      filteredLogarithmicDifferentialCohomologyMap B D ≫
        truncatedDeRhamCohomologyAbelianMap B D 1 2 := by
  rw [truncatedDeRhamCohomologyAbelianMap, filteredLogarithmicDifferentialCohomologyMap,
    map_comp_hypercohomology, filteredLogarithmicDifferentialComplexMapPlus_ι]

/-! ### The projection onto the degree-one graded piece -/

/-- **The projection `σ^{≥1}Ω^•_{𝒪_X/A} ⟶ Ω¹_{𝒪_X/A}[-1]`** of the first step of the Hodge
filtration onto its bottom graded piece: `StacksDraft.StupidTruncation.stupidTruncGEπ` followed
by the identification of the degree-one term of the extended complex with `Ω¹`. -/
def degreeOneProjection :
    (deRhamAbelianComplexInt B D).stupidTrunc (embeddingUpIntGE 1) ⟶
      (CochainComplex.singleFunctor (AbelianSheaf X.carrier) 1).obj
        ((deRhamAbelianComplex B D).X 1) :=
  StacksDraft.StupidTruncation.stupidTruncGEπ (deRhamAbelianComplexInt B D) 1 ≫
    (CochainComplex.singleFunctor (AbelianSheaf X.carrier) 1).map
      (deRhamAbelianIntXIsoOne B D).hom

/-- **The projection recovers `d log`**: composing
`AlgebraicGeometry.SheafOfModules.filteredLogarithmicDifferentialComplexMap` with the projection
onto the bottom graded piece gives logarithmic differentiation `𝒪_X^*[-1] ⟶ Ω¹_{𝒪_X/A}[-1]`
between the two sheaves placed in cohomological degree one.

Both sides are morphisms out of a complex concentrated in degree one, so only the degree-one
component is at issue, and there the factorisation through the truncation and the projection off
it compose to the identification of `(σ^{≥1}Ω^•)¹` with `Ω¹`. -/
theorem filteredLogarithmicDifferentialComplexMap_degreeOneProjection :
    filteredLogarithmicDifferentialComplexMap B D ≫ degreeOneProjection B D =
      (CochainComplex.singleFunctor (AbelianSheaf X.carrier) 1).map
        (logarithmicDifferentialAbelianSheafHom B D) := by
  apply HomologicalComplex.to_single_hom_ext
  have hι : (filteredLogarithmicDifferentialComplexMap B D).f 1 ≫
      (StacksDraft.StupidTruncation.stupidTruncGEXIso
        (deRhamAbelianComplexInt B D) 1 1 le_rfl).hom =
      (logarithmicDifferentialComplexMap B D).f 1 := by
    have h := congrArg (fun g => HomologicalComplex.Hom.f g 1)
      (filteredLogarithmicDifferentialComplexMap_ι B D)
    simpa [StacksDraft.StupidTruncation.ιStupidTruncGE_f] using h
  rw [HomologicalComplex.comp_f, degreeOneProjection, HomologicalComplex.comp_f,
    StacksDraft.StupidTruncation.stupidTruncGEπ_f, ← Category.assoc, ← Category.assoc, hι,
    logarithmicDifferentialComplexMap, HomologicalComplex.mkHomFromSingle_f,
    logarithmicDifferentialAbelian]
  simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]

/-- `Ω¹_{𝒪_X/A}[-1]`: the sheaf of relative differentials placed in cohomological degree one, as
a bounded-below complex. -/
abbrev degreeOneComplexPlus : CochainComplex.Plus (AbelianSheaf X.carrier) :=
  singleOneComplexPlus X.carrier ((deRhamAbelianComplex B D).X 1)

/-- The projection `σ^{≥1}Ω^• ⟶ Ω¹[-1]` as a morphism of bounded-below complexes. -/
abbrev degreeOneProjectionPlus :
    deRhamAbelianTruncationPlus B D 1 ⟶ degreeOneComplexPlus B D :=
  ⟨degreeOneProjection B D⟩

/-- `d log : 𝒪_X^*[-1] ⟶ Ω¹_{𝒪_X/A}[-1]` as a morphism of bounded-below complexes. -/
abbrev logarithmicDifferentialSingleMapPlus :
    unitsComplexPlus X ⟶ degreeOneComplexPlus B D :=
  ⟨(CochainComplex.singleFunctor (AbelianSheaf X.carrier) 1).map
    (logarithmicDifferentialAbelianSheafHom B D)⟩

/-- The projection recovers `d log`, read on bounded-below complexes: morphisms of bounded-below
complexes are morphisms of the underlying complexes, so this is
`AlgebraicGeometry.SheafOfModules.filteredLogarithmicDifferentialComplexMap_degreeOneProjection`.
-/
theorem filteredLogarithmicDifferentialComplexMapPlus_degreeOneProjectionPlus :
    filteredLogarithmicDifferentialComplexMapPlus B D ≫ degreeOneProjectionPlus B D =
      logarithmicDifferentialSingleMapPlus B D :=
  CochainComplex.Plus.ι _ |>.map_injective
    (filteredLogarithmicDifferentialComplexMap_degreeOneProjection B D)

/-- The degree-two hypercohomology `H²(X, Ω¹_{𝒪_X/A}[-1])` of the sheaf of relative
differentials placed in degree one. -/
abbrev degreeOneShiftedCohomologyTwo : AddCommGrpCat.{u} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).obj
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj (degreeOneComplexPlus B D)))

/-- The map `H²(X, σ^{≥1}Ω^•) ⟶ H²(X, Ω¹[-1])` induced by the projection onto the bottom
graded piece. -/
abbrev degreeOneProjectionCohomologyMap :
    truncatedDeRhamCohomologyAbelian B D 1 2 ⟶ degreeOneShiftedCohomologyTwo B D :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
    ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (degreeOneProjectionPlus B D)))

/-- **The Hodge cohomology group `H¹(X, Ω¹_{𝒪_X/A})`**, in the abelian-sheaf realization. -/
abbrev hodgeCohomologyOneAbelian : AddCommGrpCat.{u} :=
  ((sectionsFunctor X.carrier ⊤).rightDerived 1).obj ((deRhamAbelianComplex B D).X 1)

/-! ### The first Chern classes -/

section Classes

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-! The abelian group structure on the Picard group of a ringed space, named for the same reason
as `Stacks.Cohomology.Generators.picardGroupAddCommGroup` in
`StacksFrontier.Topology.Sheaves.Cohomology.Torsors.PicardGroupAndFirstCohomology`, that instance
search does not find it through the universe constraints of a ringed space: it is that same
instance, re-seated here. -/

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-- The identification `Pic(X) = H¹(X, 𝒪_X^*) = H²(X, 𝒪_X^*[-1])` of the Picard group with the
degree-two hypercohomology of the sheaf of units placed in degree one, as a homomorphism of
abelian groups: Tag 09NU followed by the degree shift
`AlgebraicGeometry.SheafOfModules.sheafCohomologyOneIsoShiftedCohomologyTwo`. Both steps are
isomorphisms. -/
def picardGroupToShiftedUnitsCohomologyTwo :
    Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj (structureSheaf X.sheaf).property →+
      shiftedUnitsCohomologyTwo X :=
  ((sheafCohomologyOneIsoShiftedCohomologyTwo X.carrier (unitsAbelianSheaf X)).hom).hom.comp
    (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup X).symm.toAddMonoidHom

/-- **Stacks Project, Tag 0FME.** **The first Chern class in Hodge-filtered de Rham
cohomology.** Logarithmic differentiation is a morphism of complexes of abelian sheaves
`𝒪_X^*[-1] ⟶ σ^{≥1}Ω^•_{𝒪_X/A}`, and `Pic(X) = H¹(X, 𝒪_X^*) = H²(X, 𝒪_X^*[-1])`; the class
`γ₁(L) ∈ H²(X, σ^{≥1}Ω^•_{𝒪_X/A})` of an invertible module is the image of its Picard class
under the composite. -/
@[stacks 0FME "the filtered first Chern class"]
def filteredFirstChernClass :
    Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj (structureSheaf X.sheaf).property →+
      truncatedDeRhamCohomologyAbelian B D 1 2 :=
  (filteredLogarithmicDifferentialCohomologyMap B D).hom.comp
    (picardGroupToShiftedUnitsCohomologyTwo (X := X))

/-- **Stacks Project, Tag 0FLE.** **The first Chern class in relative de Rham cohomology**, in
the abelian-sheaf realization: the image of a Picard class under the map on degree-two
hypercohomology induced by logarithmic differentiation `𝒪_X^*[-1] ⟶ Ω^•_{𝒪_X/A}`. -/
@[stacks 0FLE "the de Rham first Chern class"]
def deRhamFirstChernClassAbelian :
    Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj (structureSheaf X.sheaf).property →+
      deRhamCohomologyAbelian B D 2 :=
  (logarithmicDifferentialCohomologyMap B D).hom.comp
    (picardGroupToShiftedUnitsCohomologyTwo (X := X))

/-- **The de Rham first Chern class is the image of the Hodge-filtered one** under the map
`H²(X, σ^{≥1}Ω^•) ⟶ H²_{dR}` induced by the inclusion of the first filtered step. In
particular `c₁^{dR}(L)` lies in the first step of the Hodge filtration,
`AlgebraicGeometry.SheafOfModules.hodgeFiltrationAbelian`, that step being by definition the
image of that map. -/
@[stacks 0FME "Remark 50.9.2, clause C of A-I: the image of γ₁(L) under σ^{≥1}Ω^• ⟶ Ω^• is the \
de Rham first Chern class c₁^dR(L). The a = 1 case; the a ≥ 2 analogue, clause G, is \
`truncatedDeRhamCohomologyAbelianMap_filteredChernProduct` in \
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.CanonicalChernCupProduct`, which this is the \
base case of"]
theorem deRhamFirstChernClassAbelian_eq
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    deRhamFirstChernClassAbelian B D c =
      (truncatedDeRhamCohomologyAbelianMap B D 1 2).hom (filteredFirstChernClass B D c) := by
  rw [deRhamFirstChernClassAbelian, filteredFirstChernClass, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, logarithmicDifferentialCohomologyMap_eq]
  rfl

/-- **Stacks Project, Tag 0FME.** **`c₁^{dR}(L)` lies in `F¹H²_{dR}(X/S)`**, the first step of
the Hodge filtration of Tag 0FM8.

The step `F¹H²_{dR}` is the image of `H²(X, σ^{≥1}Ω^•) ⟶ H²_{dR}`, and
`AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian_eq` exhibits `c₁^{dR}(L)` as the
image of `γ₁(L)` under exactly that map; the witness is therefore `γ₁(L)` pushed into the
image. -/
@[stacks 0FME "Remark 50.9.2, clause D of A-I: c₁^dR(L) lies in the first step F¹H²_dR of the \
Hodge filtration. The a = 1 case; the a ≥ 2 analogue, clause H, that the a-fold product \
c₁^dR(L₁) ∪ … ∪ c₁^dR(L_a) lies in F^a H^{2a}_dR, is \
`deRhamChernProduct_mem_hodgeFiltrationAbelian` in \
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.CanonicalChernCupProduct`"]
theorem deRhamFirstChernClassAbelian_mem_hodgeFiltrationAbelian
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    ∃ y : (hodgeFiltrationAbelian B D 1 2 : AddCommGrpCat.{u}),
      ((hodgeFiltrationAbelian B D 1 2).arrow).hom y =
        deRhamFirstChernClassAbelian B D c := by
  refine ⟨(factorThruImageSubobject
    (truncatedDeRhamCohomologyAbelianMap B D 1 2)).hom (filteredFirstChernClass B D c), ?_⟩
  rw [deRhamFirstChernClassAbelian_eq]
  exact ConcreteCategory.congr_hom
    (imageSubobject_arrow_comp (truncatedDeRhamCohomologyAbelianMap B D 1 2))
    (filteredFirstChernClass B D c)

/-- **Stacks Project, Tag 0FLE.** **The first Chern class in Hodge cohomology**
`c₁^{Hodge} : Pic(X) ⟶ H¹(X, Ω¹_{𝒪_X/A})`, in the abelian-sheaf realization: the identification
`Pic(X) = H¹(X, 𝒪_X^*)` of Stacks Tag 09NU followed by the map on first cohomology induced by
logarithmic differentiation `𝒪_X^* ⟶ Ω¹_{𝒪_X/A}`.

The construction is the one of `AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass`, carried out
for a ringed space over a base ring sheaf rather than for a morphism of schemes — the two use
the same functor `(Γ(X, -)).rightDerived 1` and the same `d log`, but different spellings of the
identification of Tag 09NU, and no comparison between them is proved here. This realization is
the one the first step of the Hodge filtration projects onto, in
`AlgebraicGeometry.SheafOfModules.hodgeFirstChernClassAbelian_eq`. -/
@[stacks 0FLE "the Hodge first Chern class, for a ringed space over a base ring sheaf"]
def hodgeFirstChernClassAbelian :
    Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj (structureSheaf X.sheaf).property →+
      hodgeCohomologyOneAbelian B D :=
  (((sectionsFunctor X.carrier ⊤).rightDerived 1).map
      (logarithmicDifferentialAbelianSheafHom B D)).hom.comp
    (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup X).symm.toAddMonoidHom

/-- **Stacks Project, Tag 0FME.** **The image of `γ₁(L)` under `σ^{≥1}Ω^• ⟶ Ω¹_{𝒪_X/A}[-1]`
recovers `c₁^{Hodge}(L)`**, read through the identification `H¹(X, Ω¹) ≅ H²(X, Ω¹[-1])` of
`sheafCohomologyOneIsoShiftedCohomologyTwo`.

Both sides are the image of the Picard class under a map on degree-two hypercohomology induced
by `d log : 𝒪_X^*[-1] ⟶ Ω¹[-1]`: on the left because the projection composed with the filtered
`d log` is that map (`filteredLogarithmicDifferentialComplexMapPlus_degreeOneProjectionPlus`), on
the right because the identification is natural in the sheaf
(`sheafCohomologyOneIsoShiftedCohomologyTwo_hom_naturality`). -/
@[stacks 0FME "Remark 50.9.2, clause E of A-I: the image of γ₁(L) under σ^{≥1}Ω^• ⟶ Ω¹[-1] is \
the Hodge first Chern class c₁^Hodge(L) ∈ H¹(X, Ω¹). The a = 1 case; the a ≥ 2 analogue, clause \
I, is `hodgeGradedIso_inv_gradedPieceProjection_filteredChernProduct` in \
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.CanonicalChernCupProduct`, which this is the \
base case of"]
theorem hodgeFirstChernClassAbelian_eq
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    (degreeOneProjectionCohomologyMap B D).hom (filteredFirstChernClass B D c) =
      (sheafCohomologyOneIsoShiftedCohomologyTwo X.carrier
          ((deRhamAbelianComplex B D).X 1)).hom.hom
        (hodgeFirstChernClassAbelian B D c) := by
  have hbridge : DerivedCategory.Plus.Q.map (logarithmicDifferentialSingleMapPlus B D) =
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf X.carrier) 1).map
        (logarithmicDifferentialAbelianSheafHom B D) := rfl
  have hcomp : filteredLogarithmicDifferentialCohomologyMap B D ≫
        degreeOneProjectionCohomologyMap B D =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
        ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (logarithmicDifferentialSingleMapPlus B D))) := by
    rw [degreeOneProjectionCohomologyMap, filteredLogarithmicDifferentialCohomologyMap,
      map_comp_hypercohomology,
      filteredLogarithmicDifferentialComplexMapPlus_degreeOneProjectionPlus]
  have h₁ := ConcreteCategory.congr_hom hcomp
    (picardGroupToShiftedUnitsCohomologyTwo (X := X) c)
  have h₂ := ConcreteCategory.congr_hom
    (sheafCohomologyOneIsoShiftedCohomologyTwo_hom_naturality
      (logarithmicDifferentialAbelianSheafHom B D))
    ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup X).symm c)
  rw [← hbridge] at h₂
  simp only [ConcreteCategory.comp_apply] at h₁ h₂
  rw [filteredFirstChernClass, AddMonoidHom.comp_apply, h₁]
  exact h₂.symm

/-- The de Rham first Chern class of an invertible module. -/
abbrev deRhamFirstChernClassAbelianOf (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L) :
    deRhamCohomologyAbelian B D 2 :=
  deRhamFirstChernClassAbelian B D
    (Stacks.SheafOfModules.Picard.classOf X.sheaf.obj (structureSheaf X.sheaf).property L hL)

/-- **Stacks Project, Tag 0FME.** The Hodge-filtered first Chern class of an invertible
module. -/
@[stacks 0FME "the filtered first Chern class of an invertible module"]
abbrev filteredFirstChernClassOf (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L) :
    truncatedDeRhamCohomologyAbelian B D 1 2 :=
  filteredFirstChernClass B D
    (Stacks.SheafOfModules.Picard.classOf X.sheaf.obj (structureSheaf X.sheaf).property L hL)

end Classes

end AlgebraicGeometry.SheafOfModules

end
