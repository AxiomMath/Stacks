module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.AbelianClassMapNaturality
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianCechDerivedSquare
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechSupportTransport

/-!
# The degree-`c` passage: the square of Stacks 0G85 above the Čech cokernel

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global equations with `c = n + 1`, let `Z` be
their common zero locus and let `ℱ`, `𝒢` be quasi-coherent `𝒪_X`-modules.  Step (ii) of the proof
of [Stacks, Tag 0G85] is proved in this library **in the unbounded derived category**, by
`Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare`: for an arbitrary morphism `ψ`
of the underlying abelian sheaves of the coefficient modules — in particular for a relative de
Rham differential, which is only `f⁻¹𝒪_S`-linear — the comparison of [Stacks, Tag 0G7L],
forgotten, carries the abelian Čech derived map to `i_* R𝓗_Z^{ab}` applied to `ψ` in degree `0`.

That identity lives in `D(Ab(X))`.  This file brings it down to the cokernel level, which is
where the class map of [Stacks, Tag 0G7Q] and the Gysin map of [Stacks, Tag 0G83] live.  Its
module-level analogue is
`Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport`, which is "`Hᶜ` of
`Stacks.Perfect.SupportedFraction.cechToDerivedSupport` read through
`Stacks.Perfect.SupportedFraction.cokernelLastDifIsoHomology`"; the chain here mirrors that one,
with the forgetful functor to abelian sheaves threaded through it.

Two identifications are needed and both are supplied:

* **(1)** the abelian functoriality `Stacks.Perfect.AbelianFraction.cokernelLastDifAb` of the Čech
  cokernel is the degree-`c` cohomology of
  `Stacks.Perfect.AbelianCechDerivedSquare.derivedCechAb`, through the Čech-cokernel comparison and
  `HomologicalComplex.extendHomologyIso`.  This is
  `cokernelLastDifAb_eq_homologyFunctor_derivedCechAb`.
* **(2)** the degree-`c` cohomology of the forgetful image of the comparison of
  [Stacks, Tag 0G7L] is the forgetful image of its degree-`c` cohomology.  This is
  `homologyFunctor_map_forget_cechToSupport`, the naturality of the comparison
  `forgetDerivedHomology`.

With the derived square these assemble into `map_cokernelLastDifToSupport_abelian_square`, the
square of step (ii) between the Čech cokernel and `i_*ℋ ᶜ_Z`, in the spelling
`Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport` lands in.  Transporting that into the
spelling the Gysin map is built in — by
`Stacks.Perfect.CechSupportTransport.cokernelLastDifToPushforward_eq` — then gives
`Stacks.Perfect.AbelianClassMap.CokernelLastDifToPushforwardAbelianNatural`, **modulo one
hypothesis**; see the implementation notes.

## Main definitions

* `forgetDerivedHomologyIso` and `forgetDerivedHomology`: **forgetting the module structure
  commutes with the cohomology of the derived category**, `Hᵖ(Φ K) ≅ Φ(Hᵖ K)`, and its value at an
  object.
* `forgetHomologyIso` and `forgetCyclesIso`: the same comparison at the level of cochain complexes,
  on homology and on cycles.
* `cokernelLastDifIsoExtendHomology` and `cokernelLastDifIsoDerivedHomology`: **the Čech cokernel
  of [Stacks, Tag 0G7Q] as the degree-`c` cohomology of the extended alternating Čech complex**, in
  the `ℤ`-graded complex and in the derived category.
* `cechCokernelToForgetDerived`: the forgetful image of that identification, written so that the
  comparison `forgetDerivedHomology` is never inverted.
* `forgetSupportPushAbMap` and `supportCohomologyForgetAbMap`: the right-hand vertical arrow of the
  derived square in conjugated form, and **the action of `i_*ℋ ᶜ_Z` on a morphism of the underlying
  abelian sheaves** obtained from it by taking degree-`c` cohomology.

## Main results

* `cokernelLastDifAb_eq_homologyFunctor_derivedCechAb`: **clause (1)**.
* `homologyFunctor_map_forget_cechToSupport`: **clause (2)**.
* `map_cokernelLastDifToSupport_abelian_square`: **the square of step (ii) of [Stacks, Tag 0G85]
  above the Čech cokernel**, in the spelling of [Stacks, Tag 0G7S].  This is the result the file
  exists for, and it carries no hypothesis beyond quasi-coherence of the two coefficient modules.
* `cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoSquare` and
  `topCechClassAbelianNatural_of_forgetIsoSquare`: the same square in the spelling the Gysin map is
  built in, and the naturality of the class map of [Stacks, Tag 0G7Q], **given** the identity
  relating the two readings of [Stacks, Tag 0G74] part (2).
* `map_extendXIso_inv_comp_cplxAbExtend_f`: the degree-`c` component of the extended abelian Čech
  chain map is the induced map on the top-degree Čech term.  This is the only step at which the
  formula for the induced map is used; everything else is formal.
* `forgetIsoSquare_id`, `supportCohomologyForgetAbMap_id`, `forgetSupportPushAbMap_id`: nonvacuity
  checks, at the identity morphism.

## Implementation notes

**Carried hypotheses.**  Everything up to and including
`map_cokernelLastDifToSupport_abelian_square` carries exactly a nonempty family of global
equations `f : Fin (n + 1) → Γ(X, 𝒪_X)`, a closed subset `T` containing their common zero
locus, and quasi-coherence of both coefficient modules
(`[F.IsQuasicoherent]`, `[G.IsQuasicoherent]`) — which is where [Stacks, Tag 0G7M] enters, exactly
as it does in `Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport` and in
`Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare`.  No hypothesis is placed on
`ψ`: the whole point is that none may be.  The declarations of the last section specialise `T` to
the common zero locus of the equations, which is a specialisation and not a hypothesis.

**The one input this file does not supply.**  The two final declarations carry the hypothesis
`hforget`, which says that the comparison
`Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward` between the two places at
which the degree-`c` cohomology sheaf is taken carries `supportCohomologyForgetAbMap` to
`Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap`.  Both are the action of `i_*ℋ ᶜ_Z` on a
morphism of the underlying abelian sheaves, but they are built from *different* constructions of
[Stacks, Tag 0G74] part (2): `supportCohomologyForgetAbMap` from
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison`, which is
what the derived square is stated with, and `gysinTargetAbelianMap` from
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexForgetIso`, which is what the
Gysin map is built with.  That identity is the *only* thing between this file and
`Stacks.Perfect.AbelianClassMap.CokernelLastDifToPushforwardAbelianNatural` for a general `ψ`;
`forgetIsoSquare_id` checks it is satisfiable.  Nothing here weakens that statement — it is reached
through the *iff*
`Stacks.Perfect.AbelianClassMap.topCechClassAbelianNatural_iff_abelianSquare`, so the conclusion is
exactly as strong as the naturality of the class map of [Stacks, Tag 0G7Q] itself.

**Why three comparisons are re-spelled.**  `forgetHomologyIso`, `forgetQIso`,
`derivedQHomologyIsoAb` and `forgetDerivedHomology` are the four natural isomorphisms of this file
evaluated at an object.  Naming them is not cosmetic: a term whose type is stated through a
composite functor — `(Hᵖ ⋙ Φ).obj L` rather than `Φ.obj (Hᵖ.obj L)` — is type-correct only up to
unfolding `Functor.comp`, and in a goal containing one, `rw`, `simp` and `reassoc_of%` all report
that they have nothing to do rather than failing usefully.  With the four values named, every
rewrite below happens in a goal whose every subterm is type-correct at `implicit` transparency.

**Why `assoc_formal` and `id_conj_formal` are stated at an abstract category.**  The two spellings
`X.carrier` and `X.toRingedSpace` of the site of a scheme carry different
`Preorder.smallCategory` instance terms, and
`Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare_conj` is elaborated at the second
while this file works at the first.  `Category.assoc` therefore rewrites nothing in that
statement.  At a variable category the reassociation is immediate, and `exact` — which works up to
default transparency — instantiates it.  This is the device of
`Stacks.Perfect.AbelianCechDerivedSquare.square_formal` and
`Stacks.Perfect.CechSupportTransport.assembly_formal`, for the same reason.

**Which comparison of "an exact functor commutes with derived homology" is used.**  There are three
mutually non-`rfl` copies in the project: `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`,
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` and
`Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso`.  Everything here stays
inside the first, so that no bridge between two of them is needed.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.SupportedFraction
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AbelianCechCokernelPassage

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### Forgetting the module structure commutes with cohomology -/

/-- **Forgetting the module structure commutes with the homology of a cochain complex**, in the
spelling with the two ends written as `Functor.obj` applied to a complex rather than as the value
of a composite functor.  This is
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso` evaluated at `L`; the point of naming it
is the spelling, because a term whose type is stated through a composite functor is type-correct
only up to unfolding `Functor.comp` and then neither `rw` nor `simp` will touch the goal it sits
in. -/
def forgetHomologyIso (L : CochainComplex X.Modules ℤ) (p : ℤ) :
    (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology p ≅
      (abelianSheaf X).obj (L.homology p) :=
  ((abelianSheaf X).mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) p).app L

/-- **Forgetting the module structure commutes with the cycles of a cochain complex.**  The
forgetful functor is exact, so it preserves the kernel that cuts out the cycles. -/
def forgetCyclesIso (L : CochainComplex X.Modules ℤ) (p : ℤ) :
    (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).cycles p ≅
      (abelianSheaf X).obj (L.cycles p) :=
  (L.sc p).mapCyclesIso (abelianSheaf X)

/-- The identification of the cycles is compatible with their inclusion into the term of the
complex. -/
lemma forgetCyclesIso_inv_iCycles (L : CochainComplex X.Modules ℤ) (p : ℤ) :
    (forgetCyclesIso L p).inv ≫
        (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).iCycles p =
      (abelianSheaf X).map (L.iCycles p) :=
  ShortComplex.mapCyclesIso_inv_comp_iCycles (L.sc p) (abelianSheaf X)

/-- **The identification of the homology is compatible with the projection from the cycles**:
`Stacks.Perfect.AbelianCechCokernelPassage.forgetCyclesIso` on the source and
`forgetHomologyIso` on the target.  This is
`CategoryTheory.ShortComplex.homologyπ_comp_mapHomologyIso_hom` read on the short complex that
computes the degree-`p` homology of `L`. -/
lemma homologyπ_comp_forgetHomologyIso_hom (L : CochainComplex X.Modules ℤ) (p : ℤ) :
    (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homologyπ p ≫
        (forgetHomologyIso L p).hom =
      (forgetCyclesIso L p).hom ≫ (abelianSheaf X).map (L.homologyπ p) :=
  ShortComplex.homologyπ_comp_mapHomologyIso_hom (L.sc p) (abelianSheaf X)

/-- The inverted form of `homologyπ_comp_forgetHomologyIso_hom`. -/
lemma map_homologyπ_comp_forgetHomologyIso_inv (L : CochainComplex X.Modules ℤ) (p : ℤ) :
    (abelianSheaf X).map (L.homologyπ p) ≫
        (forgetHomologyIso L p).inv =
      (forgetCyclesIso L p).inv ≫
        (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homologyπ p :=
  ShortComplex.π_comp_mapHomologyIso_inv (L.sc p) (abelianSheaf X)

/-- **Forgetting the module structure commutes with the cohomology of the derived category**:
`Hᵖ(Φ K) ≅ Φ(Hᵖ K)` naturally in `K`, where `Φ` is the forgetful functor on derived categories.
This is `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at the forgetful functor of a
scheme.

Of the three copies of this comparison in the project — this one,
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` and
`Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso` — no two are `rfl`-equal, so
everything below stays inside this one. -/
def forgetDerivedHomologyIso (X : Scheme.{u}) (p : ℤ) :
    (abelianSheaf X).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) p ≅
      DerivedCategory.homologyFunctor X.Modules p ⋙ abelianSheaf X :=
  (abelianSheaf X).mapDerivedCategoryHomologyIso p

/-- The comparison identifying the forgetful functor on derived categories with the forgetful
functor applied degreewise, at a complex, with both ends spelled as `Functor.obj` applied to an
object.  Mathlib's `Functor.mapDerivedCategoryFactors`, re-spelled for the reason recorded at
`forgetHomologyIso`. -/
def forgetQIso (L : CochainComplex X.Modules ℤ) :
    (abelianSheaf X).mapDerivedCategory.obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj
        (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
  (abelianSheaf X).mapDerivedCategoryFactors.app L

/-- The cohomology of a complex of abelian sheaves read in the derived category is its
cohomology.  This is the abelian-sheaf counterpart of
`Stacks.Perfect.SupportedFraction.derivedQHomologyIso`. -/
def derivedQHomologyIsoAb
    (L : CochainComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ℤ)
    (p : ℤ) :
    (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) p).obj
        (DerivedCategory.Q.obj L) ≅
      L.homology p :=
  (DerivedCategory.homologyFunctorFactors
    (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) p).app L

/-- `derivedQHomologyIsoAb` is natural in the complex. -/
lemma derivedQHomologyIsoAb_hom_naturality
    {L L' : CochainComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ℤ}
    (α : L ⟶ L') (p : ℤ) :
    (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) p).map
          (DerivedCategory.Q.map α) ≫
        (derivedQHomologyIsoAb L' p).hom =
      (derivedQHomologyIsoAb L p).hom ≫ HomologicalComplex.homologyMap α p :=
  DerivedCategory.homologyFunctorFactors_hom_naturality α p

/-- `derivedQHomologyIsoAb` is natural in the complex, inverted. -/
lemma derivedQHomologyIsoAb_inv_naturality
    {L L' : CochainComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ℤ}
    (α : L ⟶ L') (p : ℤ) :
    (derivedQHomologyIsoAb L p).inv ≫
        (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) p).map
          (DerivedCategory.Q.map α) =
      HomologicalComplex.homologyMap α p ≫ (derivedQHomologyIsoAb L' p).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← derivedQHomologyIsoAb_hom_naturality α p,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `forgetDerivedHomologyIso` at an object, with both ends spelled as `Functor.obj` applied to
an object. -/
def forgetDerivedHomology (K : DerivedCategory X.Modules) (p : ℤ) :
    (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) p).obj
        ((abelianSheaf X).mapDerivedCategory.obj K) ≅
      (abelianSheaf X).obj ((DerivedCategory.homologyFunctor X.Modules p).obj K) :=
  (forgetDerivedHomologyIso X p).app K

/-- **`forgetDerivedHomology` is natural**: the degree-`p` cohomology of the forgetful image of a
morphism of `D(𝒪_X)` is the forgetful image of its degree-`p` cohomology.  This is the second of
the two identifications the degree-`c` passage needs, and it is nothing but the naturality of the
comparison. -/
lemma forgetDerivedHomology_hom_naturality {K L : DerivedCategory X.Modules} (g : K ⟶ L)
    (p : ℤ) :
    (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) p).map
          ((abelianSheaf X).mapDerivedCategory.map g) ≫
        (forgetDerivedHomology L p).hom =
      (forgetDerivedHomology K p).hom ≫
        (abelianSheaf X).map ((DerivedCategory.homologyFunctor X.Modules p).map g) :=
  (forgetDerivedHomologyIso X p).hom.naturality g

/-- **The value of `forgetDerivedHomology` at a localized complex**, in terms of the chain-level
comparisons: the forgetful comparison of the localizations, the two identifications of the
cohomology of a complex with its cohomology in the derived category, and the chain-level
comparison `forgetHomologyIso`.

This is `CategoryTheory.Localization.liftNatTrans_app` for the lift along `DerivedCategory.Q`
that defines `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, with the two
`CategoryTheory.Localization.Lifting` instances evaluated: the source one is
`Functor.mapDerivedCategoryFactors` composed on the right with `Hᵖ`, and the target one is the
identity. -/
lemma forgetDerivedHomology_hom_Q (L : CochainComplex X.Modules ℤ) (p : ℤ) :
    (forgetDerivedHomology (DerivedCategory.Q.obj L) p).hom =
      (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) p).map
          (forgetQIso L).hom ≫
        (derivedQHomologyIsoAb
          (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) p).hom ≫
        (forgetHomologyIso L p).hom ≫
        (abelianSheaf X).map (derivedQHomologyIso L p).inv := by
  rw [forgetDerivedHomology, forgetQIso, derivedQHomologyIsoAb, CategoryTheory.Iso.app_hom,
    CategoryTheory.Iso.app_hom, CategoryTheory.Iso.app_hom, forgetDerivedHomologyIso,
    CategoryTheory.Functor.mapDerivedCategoryHomologyIso,
    Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp [CategoryTheory.Functor.mapDerivedCategoryHomologyIsoAux]
  rfl

/-! ### The Čech cokernel is the degree-`c` cohomology of the extended Čech complex -/

section Cokernel

variable {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) (F : X.Modules)

/-- **The Čech cokernel is the degree-`c` cohomology of the extended alternating Čech complex.**
`Stacks.Perfect.SupportedFraction.cokernelLastDifIsoHomology` identifies the cokernel of the last
differential with the degree-`c` homology of the `ℕ`-graded complex, and
`HomologicalComplex.extendHomologyIso` carries that to the degree-`c` homology of the `ℤ`-graded
extension, which is the complex the comparison of [Stacks, Tag 0G7L] is stated at. -/
def cokernelLastDifIsoExtendHomology :
    cokernel (lastDif f F) ≅
      ((cplx f F).extend ComplexShape.embeddingUpNat).homology ((n + 1 : ℕ) : ℤ) :=
  cokernelLastDifIsoHomology f F ≪≫
    ((cplx f F).extendHomologyIso ComplexShape.embeddingUpNat
      (embeddingUpNat_f (n + 1))).symm

/-- **A top-degree Čech cochain is a cycle of the extended complex**: there is nothing above
degree `c`, so the top-degree term is its own cycles
(`Stacks.Perfect.SupportedFraction.topCyclesIso`), and extending the grading does not change the
cycles (`HomologicalComplex.extendCyclesIso`). -/
def topExtendCycles :
    prodTerm f F n ⟶
      ((cplx f F).extend ComplexShape.embeddingUpNat).cycles ((n + 1 : ℕ) : ℤ) :=
  (topCyclesIso f F).hom ≫
    ((cplx f F).extendCyclesIso ComplexShape.embeddingUpNat
      (embeddingUpNat_f (n + 1))).inv

/-- The inclusion of the cycles carries `topExtendCycles` to the canonical identification of the
degree-`c` term of the extension with the top-degree Čech term. -/
lemma topExtendCycles_comp_iCycles :
    topExtendCycles f F ≫
        ((cplx f F).extend ComplexShape.embeddingUpNat).iCycles ((n + 1 : ℕ) : ℤ) =
      ((cplx f F).extendXIso ComplexShape.embeddingUpNat (embeddingUpNat_f (n + 1))).inv := by
  rw [topExtendCycles, Category.assoc,
    HomologicalComplex.extendCyclesIso_inv_iCycles, ← Category.assoc,
    topCyclesIso_hom_iCycles]
  exact Category.id_comp _

/-- **The characteristic property of `cokernelLastDifIsoExtendHomology`**: it carries the class of
a top-degree Čech cochain to its degree-`c` cohomology class on the extended complex. -/
lemma cokernelπ_comp_cokernelLastDifIsoExtendHomology :
    cokernel.π (lastDif f F) ≫ (cokernelLastDifIsoExtendHomology f F).hom =
      topExtendCycles f F ≫
        ((cplx f F).extend ComplexShape.embeddingUpNat).homologyπ ((n + 1 : ℕ) : ℤ) := by
  rw [cokernelLastDifIsoExtendHomology, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    cokernelπ_comp_cokernelLastDifIsoHomology, Category.assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_inv, topExtendCycles, Category.assoc]

/-- **The Čech cokernel is the degree-`c` cohomology of the extended alternating Čech complex,
read in the derived category.**  This is the whole of the module-level identification
`Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport` except for its last factor, the
comparison of [Stacks, Tag 0G7L]; see `cokernelLastDifToSupport_eq`. -/
def cokernelLastDifIsoDerivedHomology :
    cokernel (lastDif f F) ≅
      (DerivedCategory.homologyFunctor X.Modules ((n + 1 : ℕ) : ℤ)).obj
        (DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat)) :=
  cokernelLastDifIsoExtendHomology f F ≪≫
    (derivedQHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat)
      ((n + 1 : ℕ) : ℤ)).symm

/-- **The identification of [Stacks, Tag 0G7M] factors through the derived-category cohomology of
the extended Čech complex.**  The first factor is the isomorphism
`cokernelLastDifIsoDerivedHomology`, which involves no local cohomology; the second is the
degree-`c` cohomology of the comparison of [Stacks, Tag 0G7L]. -/
lemma cokernelLastDifToSupport_eq [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) :
    cokernelLastDifToSupport f F hT hTf =
      (cokernelLastDifIsoDerivedHomology f F).hom ≫
        (DerivedCategory.homologyFunctor X.Modules ((n + 1 : ℕ) : ℤ)).map
          (cechToSupport f F hT hTf) := by
  rw [cokernelLastDifToSupport, cechHomologyToSupport, extendHomologyToSupport,
    cokernelLastDifIsoDerivedHomology, cokernelLastDifIsoExtendHomology]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]

end Cokernel

/-! ### The abelian Čech chain map on the top-degree cokernel -/

section Abelian

open Stacks.Perfect.AbelianCechDerivedSquare (cplxAbExtend derivedCechAb)
open Stacks.Perfect.AbelianFraction (cplxAb cokernelLastDifAb prodTermAb)

variable {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) {F G : X.Modules}
  (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)

/-- The map induced on the top Čech term by a morphism of the underlying abelian sheaves is the
map induced on the top-degree product of Čech terms: the two are the same construction, the
degree-`c` term of the complex being that product. -/
lemma termAb_succ : AbelianFraction.termAb f ψ (n + 1) = prodTermAb f ψ n := rfl

/-- **The degree-`c` component of the extended abelian Čech chain map is the induced map on the
top-degree Čech term**, read through the canonical identifications of the degree-`c` terms of the
two extensions with the top-degree terms of the `ℕ`-graded complexes.

This is the only place where the abelian Čech chain map
`Stacks.Perfect.AbelianFraction.cplxAb` is opened up, and it is where the whole degree-`c`
passage touches the actual formula for the induced map: everything else is formal. -/
lemma map_extendXIso_inv_comp_cplxAbExtend_f :
    (abelianSheaf X).map ((cplx f F).extendXIso ComplexShape.embeddingUpNat
          (embeddingUpNat_f (n + 1))).inv ≫
        (cplxAbExtend f ψ).f ((n + 1 : ℕ) : ℤ) =
      prodTermAb f ψ n ≫
        (abelianSheaf X).map ((cplx f G).extendXIso ComplexShape.embeddingUpNat
          (embeddingUpNat_f (n + 1))).inv := by
  have hsq : (HomologicalComplex.mapHomologicalComplexExtendIso (abelianSheaf X) (cplx f F)
          ComplexShape.embeddingUpNat).hom ≫ cplxAbExtend f ψ =
      HomologicalComplex.extendMap (cplxAb f ψ) ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso (abelianSheaf X) (cplx f G)
          ComplexShape.embeddingUpNat).hom := by
    rw [cplxAbExtend, Iso.hom_inv_id_assoc]
  have hsqf := congrArg (fun α => HomologicalComplex.Hom.f α ((n + 1 : ℕ) : ℤ)) hsq
  have hRHS := HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f (abelianSheaf X)
    (cplx f G) (cplxAb f ψ) ComplexShape.embeddingUpNat (embeddingUpNat_f (n + 1))
  rw [HomologicalComplex.comp_f] at hRHS
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _
      (embeddingUpNat_f (n + 1)), hRHS] at hsqf
  refine (cancel_epi ((((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (cplx f F)).extendXIso ComplexShape.embeddingUpNat
      (embeddingUpNat_f (n + 1))).hom).mp ?_
  rw [← Category.assoc, hsqf, Stacks.Perfect.AbelianFraction.cplxAb_f, termAb_succ]
  rfl

/-- **The abelian Čech chain map carries a top-degree cocycle to the image of that cocycle**,
read on the cycles of the two extended complexes.  Both sides are checked after composing with
the inclusion of the cycles, which is a monomorphism; what is left is
`map_extendXIso_inv_comp_cplxAbExtend_f`. -/
lemma topExtendCycles_comp_cyclesMap_cplxAbExtend :
    (abelianSheaf X).map (topExtendCycles f F) ≫
        (forgetCyclesIso ((cplx f F).extend ComplexShape.embeddingUpNat)
          ((n + 1 : ℕ) : ℤ)).inv ≫
        HomologicalComplex.cyclesMap (cplxAbExtend f ψ) ((n + 1 : ℕ) : ℤ) =
      prodTermAb f ψ n ≫
        (abelianSheaf X).map (topExtendCycles f G) ≫
          (forgetCyclesIso ((cplx f G).extend ComplexShape.embeddingUpNat)
            ((n + 1 : ℕ) : ℤ)).inv := by
  refine (cancel_mono ((((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((cplx f G).extend ComplexShape.embeddingUpNat)).iCycles ((n + 1 : ℕ) : ℤ))).mp ?_
  simp only [Category.assoc]
  rw [HomologicalComplex.cyclesMap_i,
    reassoc_of% (forgetCyclesIso_inv_iCycles
      ((cplx f F).extend ComplexShape.embeddingUpNat) ((n + 1 : ℕ) : ℤ)),
    forgetCyclesIso_inv_iCycles, ← CategoryTheory.Functor.map_comp_assoc,
    ← CategoryTheory.Functor.map_comp, topExtendCycles_comp_iCycles,
    topExtendCycles_comp_iCycles]
  exact map_extendXIso_inv_comp_cplxAbExtend_f f ψ

/-- **The abelian functoriality of the Čech cokernel is the degree-`c` cohomology of the abelian
Čech chain map**, at the level of the `ℤ`-graded extensions and before passing to the derived
category.  Both sides are checked after composing with the canonical epimorphism onto the
cokernel, which stays epimorphic after forgetting the module structure
(`Stacks.Perfect.AbelianFraction.epi_map_cokernelπ_lastDif`); what is left is the statement on
cycles, `topExtendCycles_comp_cyclesMap_cplxAbExtend`. -/
lemma map_cokernelLastDifIsoExtendHomology_comp :
    (abelianSheaf X).map (cokernelLastDifIsoExtendHomology f F).hom ≫
        (forgetHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat)
            ((n + 1 : ℕ) : ℤ)).inv ≫
        HomologicalComplex.homologyMap (cplxAbExtend f ψ) ((n + 1 : ℕ) : ℤ) ≫
        (forgetHomologyIso ((cplx f G).extend ComplexShape.embeddingUpNat)
          ((n + 1 : ℕ) : ℤ)).hom =
      cokernelLastDifAb f ψ ≫
        (abelianSheaf X).map (cokernelLastDifIsoExtendHomology f G).hom := by
  refine (cancel_epi ((abelianSheaf X).map (cokernel.π (lastDif f F)))).mp ?_
  rw [← CategoryTheory.Functor.map_comp_assoc,
    cokernelπ_comp_cokernelLastDifIsoExtendHomology,
    CategoryTheory.Functor.map_comp_assoc,
    reassoc_of% (map_homologyπ_comp_forgetHomologyIso_inv
      ((cplx f F).extend ComplexShape.embeddingUpNat) ((n + 1 : ℕ) : ℤ)),
    reassoc_of% (HomologicalComplex.homologyπ_naturality (cplxAbExtend f ψ)
      ((n + 1 : ℕ) : ℤ)),
    homologyπ_comp_forgetHomologyIso_hom,
    reassoc_of% (topExtendCycles_comp_cyclesMap_cplxAbExtend f ψ),
    Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp,
    ← cokernelπ_comp_cokernelLastDifIsoExtendHomology, CategoryTheory.Functor.map_comp,
    reassoc_of% (Stacks.Perfect.AbelianFraction.map_cokernelπ_comp_cokernelLastDifAb f ψ)]

end Abelian

/-! ### The Čech cokernel in the forgetful image of the derived category -/

section Derived

open Stacks.Perfect.AbelianCechDerivedSquare (cplxAbExtend derivedCechAb)
open Stacks.Perfect.AbelianFraction (cplxAb cokernelLastDifAb prodTermAb)

variable {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) {F G : X.Modules}
  (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)

/-- **The Čech cokernel, after forgetting the module structure, mapped to the degree-`c`
cohomology of the forgetful image of the extended Čech complex in the derived category of abelian
sheaves.**  This is `cokernelLastDifIsoDerivedHomology` conjugated past the comparison
`forgetDerivedHomology`, written out so that the conjugation is never inverted; see
`cechCokernelToForgetDerived_comp_forgetDerivedHomology_hom`. -/
def cechCokernelToForgetDerived (F : X.Modules) :
    (abelianSheaf X).obj (cokernel (lastDif f F)) ⟶
      (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
          ((n + 1 : ℕ) : ℤ)).obj
        ((abelianSheaf X).mapDerivedCategory.obj
          (DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat))) :=
  (abelianSheaf X).map (cokernelLastDifIsoExtendHomology f F).hom ≫
    (forgetHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat)
      ((n + 1 : ℕ) : ℤ)).inv ≫
    (derivedQHomologyIsoAb (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((cplx f F).extend ComplexShape.embeddingUpNat)) ((n + 1 : ℕ) : ℤ)).inv ≫
    (DerivedCategory.homologyFunctor
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        ((n + 1 : ℕ) : ℤ)).map
      (forgetQIso ((cplx f F).extend ComplexShape.embeddingUpNat)).inv

/-- Reading `cechCokernelToForgetDerived` through the comparison `forgetDerivedHomology` gives
the forgetful image of `cokernelLastDifIsoDerivedHomology`. -/
lemma cechCokernelToForgetDerived_comp_forgetDerivedHomology_hom (F : X.Modules) :
    cechCokernelToForgetDerived f F ≫
        (forgetDerivedHomology
          (DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat))
          ((n + 1 : ℕ) : ℤ)).hom =
      (abelianSheaf X).map (cokernelLastDifIsoDerivedHomology f F).hom := by
  rw [cechCokernelToForgetDerived, forgetDerivedHomology_hom_Q,
    cokernelLastDifIsoDerivedHomology, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_assoc]

/-- `map_cokernelLastDifIsoExtendHomology_comp` with the homology comparison of the target moved
to the other side. -/
lemma map_cokernelLastDifIsoExtendHomology_comp_homologyMap :
    (abelianSheaf X).map (cokernelLastDifIsoExtendHomology f F).hom ≫
        (forgetHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat)
          ((n + 1 : ℕ) : ℤ)).inv ≫
        HomologicalComplex.homologyMap (cplxAbExtend f ψ) ((n + 1 : ℕ) : ℤ) =
      cokernelLastDifAb f ψ ≫
        (abelianSheaf X).map (cokernelLastDifIsoExtendHomology f G).hom ≫
          (forgetHomologyIso ((cplx f G).extend ComplexShape.embeddingUpNat)
            ((n + 1 : ℕ) : ℤ)).inv := by
  rw [← Category.assoc (cokernelLastDifAb f ψ), Iso.eq_comp_inv, Category.assoc,
    Category.assoc]
  exact map_cokernelLastDifIsoExtendHomology_comp f ψ

/-- The abelian Čech derived map of [Stacks, Tag 0G85] step (2), written through the comparison
`forgetQIso` of the two localizations. -/
lemma derivedCechAb_eq :
    derivedCechAb f ψ =
      (forgetQIso ((cplx f F).extend ComplexShape.embeddingUpNat)).hom ≫
        DerivedCategory.Q.map (cplxAbExtend f ψ) ≫
        (forgetQIso ((cplx f G).extend ComplexShape.embeddingUpNat)).inv := rfl

/-- **The first of the two identifications the degree-`c` passage needs: the abelian
functoriality of the Čech cokernel *is* the degree-`c` cohomology of the abelian Čech derived
map.**  Read through `cechCokernelToForgetDerived`, the map
`Stacks.Perfect.AbelianFraction.cokernelLastDifAb` of [Stacks, Tag 0G7Q] is carried to
`Hᶜ` of `Stacks.Perfect.AbelianCechDerivedSquare.derivedCechAb`.

This is the passage from the derived square of [Stacks, Tag 0G85] step (ii) down to the cokernel
level, on the left-hand vertical arrow. -/
theorem cokernelLastDifAb_eq_homologyFunctor_derivedCechAb :
    cechCokernelToForgetDerived f F ≫
        (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
            ((n + 1 : ℕ) : ℤ)).map (derivedCechAb f ψ) =
      cokernelLastDifAb f ψ ≫ cechCokernelToForgetDerived f G := by
  rw [cechCokernelToForgetDerived, cechCokernelToForgetDerived, derivedCechAb_eq,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% (derivedQHomologyIsoAb_inv_naturality (cplxAbExtend f ψ) ((n + 1 : ℕ) : ℤ)),
    reassoc_of% (map_cokernelLastDifIsoExtendHomology_comp_homologyMap f ψ)]

end Derived

/-! ### The square above the Čech cokernel -/

section Square

open Stacks.Cohomology.AbelianSupportedCounit (derivedAbelianSupportedPushforward)
open Stacks.Perfect.AbelianCechDerivedSquare (derivedCechAb derivedSingleAb forgetComparison
  forgetComparisonIso)
open Stacks.Perfect.AbelianFraction (cokernelLastDifAb)
open Stacks.Perfect.CechDerivedSupport (isClosed_equationsClosedSet)
open Stacks.Perfect.CechSupportTransport (supportCohomologyToPushforward
  cokernelLastDifToPushforward_eq)

variable {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) {F G : X.Modules}

/-- **The right-hand vertical arrow of the derived square of [Stacks, Tag 0G85] step (ii), in
conjugated form**: the comparison of [Stacks, Tag 0G74] part (2), then `i_* R𝓗_T^{ab}` applied to
`ψ` in degree `0`, then the inverse of that comparison.  With this reading the square is a square
of maps `Φ(𝓕^•) ⟶ Φ(i_* R𝓗_T(𝒢))`. -/
def forgetSupportPushAbMap {T : Set X} (hT : IsClosed T)
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).mapDerivedCategory.obj (supportPushSingle hT F) ⟶
      (abelianSheaf X).mapDerivedCategory.obj (supportPushSingle hT G) :=
  (forgetComparison hT).app ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
    (derivedAbelianSupportedPushforward X.toRingedSpace T hT).map (derivedSingleAb ψ) ≫
    (forgetComparisonIso hT ((DerivedCategory.singleFunctor X.Modules 0).obj G)).inv

/-- Reassociating a four-fold composite, at an abstract category.  The reason this is not done
by `Category.assoc` in place is that the two spellings `X.carrier` and `X.toRingedSpace` of the
site of a scheme carry different `Preorder.smallCategory` instance terms, and
`Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare_conj` is elaborated at the
second one, so neither `rw [Category.assoc]` nor `simp [Category.assoc]` finds anything to do in
its statement.  At a variable category the rewrite is immediate, and the result is instantiated
afterwards by `exact`, which works up to default transparency. -/
private lemma assoc_formal {C₀ : Type*} [Category* C₀] {A B₁ B₂ B₃ Z : C₀} (a : A ⟶ B₁)
    (b : B₁ ⟶ B₂) (c : B₂ ⟶ B₃) (d : B₃ ⟶ Z) (w : A ⟶ Z) (h : (a ≫ b ≫ c) ≫ d = w) :
    a ≫ b ≫ c ≫ d = w := by
  rw [← h, Category.assoc, Category.assoc]

/-- **The derived square of [Stacks, Tag 0G85] step (ii)**, which is
`Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare_conj` with the right-hand
vertical arrow named. -/
lemma cechToSupport_comp_forgetSupportPushAbMap [F.IsQuasicoherent] [G.IsQuasicoherent]
    {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T)
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).mapDerivedCategory.map (cechToSupport f F hT hTf) ≫
        forgetSupportPushAbMap hT ψ =
      derivedCechAb f ψ ≫
        (abelianSheaf X).mapDerivedCategory.map (cechToSupport f G hT hTf) := by
  rw [forgetSupportPushAbMap]
  exact assoc_formal _ _ _ _ _
    (Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare_conj f hT hTf ψ)

/-- **The action of `i_*ℋ ᶜ_T` on a morphism of the underlying abelian sheaves, as the degree-`c`
cohomology of the derived square's right-hand vertical arrow.**  This is the middle vertical of
the degree-`c` passage: it is what the square `map_cokernelLastDifToSupport_abelian_square` below
relates to `Stacks.Perfect.AbelianFraction.cokernelLastDifAb`, and what the carried hypothesis of
`cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoSquare` relates to
`Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap`.

It is *not* identified here with
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap`, which is the same action
built from `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexForgetIso` instead
of from `Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison`;
that identification is the one input this file does not supply. -/
def supportCohomologyForgetAbMap {T : Set X} (hT : IsClosed T) (p : ℤ)
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).obj (supportCohomologySheaf hT F p) ⟶
      (abelianSheaf X).obj (supportCohomologySheaf hT G p) :=
  (forgetDerivedHomology (supportPushSingle hT F) p).inv ≫
    (DerivedCategory.homologyFunctor
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) p).map
      (forgetSupportPushAbMap hT ψ) ≫
    (forgetDerivedHomology (supportPushSingle hT G) p).hom

/-- **The second of the two identifications the degree-`c` passage needs: the degree-`c`
cohomology of the forgetful image of the comparison of [Stacks, Tag 0G7L] is the forgetful image
of its degree-`c` cohomology.**  This is the naturality of `forgetDerivedHomology` at
`Stacks.Perfect.SupportedFraction.cechToSupport` and nothing else; it is recorded separately
because it is one of the two clauses of the passage. -/
lemma homologyFunctor_map_forget_cechToSupport [F.IsQuasicoherent] {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) (p : ℤ) :
    (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) p).map
          ((abelianSheaf X).mapDerivedCategory.map (cechToSupport f F hT hTf)) ≫
        (forgetDerivedHomology (supportPushSingle hT F) p).hom =
      (forgetDerivedHomology
          (DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat)) p).hom ≫
        (abelianSheaf X).map
          ((DerivedCategory.homologyFunctor X.Modules p).map (cechToSupport f F hT hTf)) :=
  forgetDerivedHomology_hom_naturality (cechToSupport f F hT hTf) p

/-- **The square of [Stacks, Tag 0G85] step (ii), between the Čech cokernel and `i_*ℋ ᶜ_T`.**
For a morphism `ψ` of the underlying abelian sheaves of two quasi-coherent coefficient modules —
not required to be `𝒪_X`-linear — the forgetful image of the identification
`Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport` of [Stacks, Tag 0G7M] carries the
abelian functoriality `Stacks.Perfect.AbelianFraction.cokernelLastDifAb` of the Čech cokernel to
the action `supportCohomologyForgetAbMap`.

This is the degree-`c` passage: the derived square
`Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare_conj` read on the degree-`c`
cohomology sheaves, brought down to the cokernel level by
`cokernelLastDifAb_eq_homologyFunctor_derivedCechAb` on the left and by
`homologyFunctor_map_forget_cechToSupport` on the horizontal arrows. -/
theorem map_cokernelLastDifToSupport_abelian_square [F.IsQuasicoherent] [G.IsQuasicoherent]
    {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T)
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).map (cokernelLastDifToSupport f F hT hTf) ≫
        supportCohomologyForgetAbMap hT ((n + 1 : ℕ) : ℤ) ψ =
      cokernelLastDifAb f ψ ≫
        (abelianSheaf X).map (cokernelLastDifToSupport f G hT hTf) := by
  rw [cokernelLastDifToSupport_eq, cokernelLastDifToSupport_eq,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    supportCohomologyForgetAbMap,
    ← cechCokernelToForgetDerived_comp_forgetDerivedHomology_hom f F,
    ← cechCokernelToForgetDerived_comp_forgetDerivedHomology_hom f G]
  simp only [Category.assoc]
  rw [← reassoc_of% (homologyFunctor_map_forget_cechToSupport f (F := F) hT hTf
      ((n + 1 : ℕ) : ℤ)),
    Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    cechToSupport_comp_forgetSupportPushAbMap f hT hTf ψ,
    CategoryTheory.Functor.map_comp_assoc,
    reassoc_of% (cokernelLastDifAb_eq_homologyFunctor_derivedCechAb f ψ),
    homologyFunctor_map_forget_cechToSupport f hT hTf ((n + 1 : ℕ) : ℤ)]

/-- Conjugating the identity by an isomorphism, at an abstract category; stated at a variable
category for the reason recorded at `assoc_formal`. -/
private lemma id_conj_formal {C₀ : Type*} [Category* C₀] {A B : C₀} (e : A ≅ B) (u : B ⟶ B)
    (hu : u = 𝟙 B) : e.hom ≫ u ≫ e.inv = 𝟙 A := by
  rw [hu, Category.id_comp, Iso.hom_inv_id]

/-- The underlying abelian sheaf map of the identity of a module is the identity. -/
private lemma abHom_mapPresheaf_id (F : X.Modules) :
    abHom (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) = 𝟙 ((abelianSheaf X).obj F) := by
  rw [← Stacks.Perfect.AbelianFraction.abelianSheaf_map, CategoryTheory.Functor.map_id]

/-- **A nonvacuity check**: the derived square's right-hand vertical arrow is the identity at the
identity morphism. -/
lemma forgetSupportPushAbMap_id {T : Set X} (hT : IsClosed T) (F : X.Modules) :
    forgetSupportPushAbMap hT (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) = 𝟙 _ := by
  have hs : Stacks.Perfect.AbelianCechDerivedSquare.singleCplxAb
      (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) = 𝟙 _ := by
    rw [Stacks.Perfect.AbelianCechDerivedSquare.singleCplxAb]
    exact id_conj_formal
      ((HomologicalComplex.singleMapHomologicalComplex (abelianSheaf X)
        (ComplexShape.up ℤ) 0).app F) _
      (by rw [abHom_mapPresheaf_id]; exact CategoryTheory.Functor.map_id _ _)
  have hd : derivedSingleAb (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) = 𝟙 _ := by
    rw [Stacks.Perfect.AbelianCechDerivedSquare.derivedSingleAb]
    exact id_conj_formal
      ((abelianSheaf X).mapDerivedCategoryFactors.app
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F)) _
      (by rw [hs]; exact CategoryTheory.Functor.map_id _ _)
  rw [forgetSupportPushAbMap, hd]
  exact id_conj_formal
    (forgetComparisonIso hT ((DerivedCategory.singleFunctor X.Modules 0).obj F)) _
    (CategoryTheory.Functor.map_id _ _)

/-- **A nonvacuity check**: the action of `i_*ℋ ᶜ_T` on the identity morphism of abelian sheaves
is the identity. -/
lemma supportCohomologyForgetAbMap_id {T : Set X} (hT : IsClosed T) (p : ℤ) (F : X.Modules) :
    supportCohomologyForgetAbMap hT p (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) = 𝟙 _ := by
  rw [supportCohomologyForgetAbMap, forgetSupportPushAbMap_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

end Square

/-! ### The square above the Čech cokernel in the Gysin map's spelling -/

section Assembly

open Stacks.Perfect.AbelianFraction (cokernelLastDifAb)
open Stacks.Perfect.CechDerivedSupport (isClosed_equationsClosedSet)
open Stacks.Perfect.CechSupportTransport (supportCohomologyToPushforward
  cokernelLastDifToPushforward_eq)

variable {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) {F G : X.Modules}

/-- **The square of step (ii) of [Stacks, Tag 0G85] above the Čech cokernel, in the spelling the
Gysin map of [Stacks, Tag 0G83] is built in**, given the identity relating the two readings of
[Stacks, Tag 0G74] part (2).

The carried hypothesis `hforget` is exactly that identity: that the comparison
`Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward` between the two places at
which the degree-`c` cohomology sheaf is taken carries the action `supportCohomologyForgetAbMap`
of this file — built from
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison` — to the
action `Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap` on the target of the Gysin map —
built from `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexForgetIso`.
`forgetIsoSquare_id` checks that it is not vacuous.

Everything else is discharged: the two identifications of the degree-`c` passage
(`cokernelLastDifAb_eq_homologyFunctor_derivedCechAb` and
`homologyFunctor_map_forget_cechToSupport`), the square they assemble into
(`map_cokernelLastDifToSupport_abelian_square`), and the identification
`Stacks.Perfect.CechSupportTransport.cokernelLastDifToPushforward_eq` of the two constructions of
the comparison of [Stacks, Tag 0G7M]. -/
theorem cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoSquare
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (hforget : (abelianSheaf X).map (supportCohomologyToPushforward f F).hom ≫
        Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap f (abHom ψ) =
      supportCohomologyForgetAbMap (isClosed_equationsClosedSet f) ((n + 1 : ℕ) : ℤ) ψ ≫
        (abelianSheaf X).map (supportCohomologyToPushforward f G).hom) :
    Stacks.Perfect.AbelianClassMap.CokernelLastDifToPushforwardAbelianNatural f ψ := by
  simp only [Stacks.Perfect.AbelianClassMap.CokernelLastDifToPushforwardAbelianNatural,
    cokernelLastDifToPushforward_eq, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hforget, ← Category.assoc,
    map_cokernelLastDifToSupport_abelian_square f (isClosed_equationsClosedSet f) subset_rfl ψ,
    Category.assoc]

/-- **The naturality of the class map of [Stacks, Tag 0G7Q] in a morphism of the underlying
abelian sheaves follows**, given the same identity.  This chains
`cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoSquare` with the equivalence
`Stacks.Perfect.AbelianClassMap.topCechClassAbelianNatural_iff_abelianSquare`. -/
theorem topCechClassAbelianNatural_of_forgetIsoSquare
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (hforget : (abelianSheaf X).map (supportCohomologyToPushforward f F).hom ≫
        Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap f (abHom ψ) =
      supportCohomologyForgetAbMap (isClosed_equationsClosedSet f) ((n + 1 : ℕ) : ℤ) ψ ≫
        (abelianSheaf X).map (supportCohomologyToPushforward f G).hom) :
    Stacks.Perfect.GysinFractionDeRham.TopCechClassAbelianNatural f ψ :=
  Stacks.Perfect.AbelianClassMap.topCechClassAbelianNatural_of_abelianSquare f ψ
    (cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoSquare f ψ hforget)

/-- **A nonvacuity check for the carried hypothesis**: the identity relating the two readings of
[Stacks, Tag 0G74] part (2) holds for the identity morphism.  Both actions send the identity to
the identity, so both composites are the comparison itself.  This says nothing about a morphism
that is not `𝒪_X`-linear; what it rules out is that the hypothesis of
`cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoSquare` is unsatisfiable. -/
lemma forgetIsoSquare_id (F : X.Modules) :
    (abelianSheaf X).map (supportCohomologyToPushforward f F).hom ≫
        Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap f
          (abHom (Scheme.Modules.Hom.mapPresheaf (𝟙 F))) =
      supportCohomologyForgetAbMap (isClosed_equationsClosedSet f) ((n + 1 : ℕ) : ℤ)
          (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) ≫
        (abelianSheaf X).map (supportCohomologyToPushforward f F).hom := by
  rw [supportCohomologyForgetAbMap_id, Category.id_comp,
    Stacks.Perfect.GysinAbelianSquare.gysinTargetAbelianMap, abHom_mapPresheaf_id,
    Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyAbelianMap_id]
  exact Category.comp_id _

end Assembly

end Stacks.Perfect.AbelianCechCokernelPassage

/-! ### Step (ii) of Stacks 0G85

The square between the Čech cokernel and `i_*ℋ ᶜ_T` is step (ii) of the argument of Stacks 0G85.
It is proved with no hypothesis beyond quasi-coherence of the two modules and the two conditions on
the closed set.
-/

add_to_stacks 0G85 "STEP (ii) ONLY. This is the square between the Cech cokernel and i_*H^c_T,
carrying nothing beyond quasi-coherence of F and G and the two closed-set conditions. Steps (i)
and (iii) are proved elsewhere in this development, and the tag itself is now proved and
registered unsuffixed on AlgebraicGeometry.Scheme.Hom.gysinMapCommutesWithDeRham of
StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinMapDeRham.lean. The identity this suffix used to
name as outstanding, forgetIsoApp of
AbelianSupportedEndoModelBridge.cokernelLastDifToPushforwardAbelianNatural_of_forgetIsoApp, is
discharged by Stacks.Perfect.SupportedEndoForgetDegreewise.forgetIsoApp."
  Stacks.Perfect.AbelianCechCokernelPassage.map_cokernelLastDifToSupport_abelian_square

end
