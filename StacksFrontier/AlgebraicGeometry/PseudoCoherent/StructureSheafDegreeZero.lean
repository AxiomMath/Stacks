module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.RingedSpaceComorphism
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectLocalRep
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TrivialRange

/-!
# The structure sheaf is relatively `0`-pseudo-coherent

Let `f : X ⟶ S` be a morphism of schemes locally of finite type. This file proves that `𝒪_X` is
relatively `0`-pseudo-coherent over `S` in the sense of Stacks 09UI, and deduces that the
comparison of Stacks 09VF and Stacks 09UJ at the structure sheaf —
`AlgebraicGeometry.RelativeStructureSheafComparison`, the comparison from which
`AlgebraicGeometry.pseudoCoherent_tfae_of_relativeComparison` derives the three-condition form of
Stacks 067Y — follows from its restriction to the *strictly negative* degrees, where
`AlgebraicGeometry.relativeStructureSheafComparison_of_nonpos` needs the degrees `m ≤ 0`.

That comparison is itself proved, with no hypotheses, in
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafComparison`, so Stacks 067Y is
unconditional and the reductions below locate the content of the comparison rather than reducing
an open problem.

The argument is local on the base and on the source, as the definition of Stacks 09UI is: over a
compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V` one chooses a closed immersion `i : U ⟶ 𝔸ⁿ_V`, and
what has to be seen is that `Ri_*𝒪_U` is `0`-pseudo-coherent on `𝔸ⁿ_V`. Since `i` is a closed
immersion, `i_*` is exact, so `Ri_*𝒪_U` is the sheaf `i_*𝒪_U` placed in degree zero; and the
comorphism `𝒪_{𝔸ⁿ_V} ⟶ i_*𝒪_U` of a closed immersion is surjective, so that sheaf receives an
epimorphism from `𝒪_{𝔸ⁿ_V}` itself. A module which receives an epimorphism from a direct summand
of a finite free module is `0`-pseudo-coherent, the approximating strictly perfect complex being
the source of that epimorphism in degree zero.

## Main results

* `HomologicalComplex.epi_homologyMap_single_map`: the degree-`j` homology of the map of complexes
  concentrated in degree `j` induced by an epimorphism is an epimorphism.
* `StrictlyPerfect.isStrictlyPerfect_single`: a direct summand of a finite free module, placed in
  a single degree, is a strictly perfect complex.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_zero_of_exists_epi`: a sheaf
  of `𝒪_X`-modules which, locally on `X`, receives an epimorphism from a direct summand of a
  finite free module is `0`-pseudo-coherent as an object of the derived category.
* `AlgebraicGeometry.Scheme.Modules.epi_unitToPushforwardObjUnit`: for a closed immersion of
  schemes `i : Z ⟶ Y` the comorphism `𝒪_Y ⟶ i_*𝒪_Z` is an epimorphism of sheaves of modules.
* `AlgebraicGeometry.Scheme.Hom.isModulePseudoCoherentFrom_unit_zero`: for a morphism locally of
  finite type, `𝒪_X` is relatively `0`-pseudo-coherent (Stacks 09UI).
* `AlgebraicGeometry.relativeStructureSheafComparison_of_neg`: the comparison of Stacks 09VF and
  Stacks 09UJ at the structure sheaf follows from its restriction to the degrees `m < 0`.
* `AlgebraicGeometry.pseudoCoherent_iff_isModulePseudoCoherent_of_neg`: the equivalence of
  conditions (2) and (3) of Stacks 067Y, conditionally on that comparison in the degrees `m < 0`
  only.

## Implementation notes

The approximating complex required by Stacks 08CB lives on the open subspace produced by the
local condition, so the epimorphism it is built from is asked for on that subspace as well: the
hypothesis of
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_single_zero_of_exists_epi` quantifies
over points of `X` and produces, near each, a direct summand of a finite free module on the
restricted ringed space together with an epimorphism onto the restriction of the given module.
The comparison between "the complex concentrated in degree zero, restricted" and "the restriction,
placed in degree zero" is `HomologicalComplex.singleMapHomologicalComplex`; it is introduced
through a `have` carrying the reduced type, because the natural isomorphism's own type is phrased
with composites of functors and a goal mentioning it is then not type-correct at `implicit`
transparency, which makes `rw` fail.

Epimorphy of the comorphism of a closed immersion is not reproved here. Local surjectivity of the
comorphism as a map of sheaves of commutative rings is
`Stacks.ClosedImmersion.isLocallySurjective_c_toShHom`, and what is added is the passage to the
category of sheaves of modules: `SheafOfModules.unitToPushforwardObjUnit_val_app_apply` makes the
map on sections of `SheafOfModules.unitToPushforwardObjUnit` literally the map on sections of the
comorphism, so the two image sieves of `CategoryTheory.Presheaf.imageSieve` coincide and the
covering condition transfers unchanged; `Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective`
then gives the epimorphism.

All the ringed-space statements are at the `StrictlyPerfect.OXMod` spelling of the category of
modules, and `AlgebraicGeometry.Scheme.Modules.pushforward i` is definitionally
`SheafOfModules.pushforward i.toRingCatSheafHom`, so the structure-sheaf comorphism can be handed
directly to them. Writing the binders at that spelling, rather than at
`AlgebraicGeometry.Scheme.Modules`, is what lets instance synthesis for `HasDerivedCategory`
succeed here.

What the comparison asserts is exactly its negative range. In the degrees `m ≥ 0` both sides of
the comparison hold outright — the right-hand side by
`AlgebraicGeometry.isModuleRelativelyPseudoCoherentFrom_appLE_of_nonneg` and the left-hand side by
`AlgebraicGeometry.Scheme.Hom.isModulePseudoCoherentFrom_of_pos` together with
`AlgebraicGeometry.Scheme.Hom.isModulePseudoCoherentFrom_unit_zero` below — so the equivalence
there has no content, and each of the two implications between conditions (2) and (3) of
Stacks 067Y uses the comparison only in the degrees `m < 0`. No declaration here carries a
`stacks` tag: the statements about Stacks 067Y below are conditional, and the `067Y` tag sits on
the unconditional `AlgebraicGeometry.pseudoCoherent_tfae_three`.

## References

* [The Stacks Project, Lemma 36.60.1 (067Y)](https://stacks.math.columbia.edu/tag/067Y)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 36.61.8 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Definition 20.46.1 (08C4)](https://stacks.math.columbia.edu/tag/08C4)
* [The Stacks Project, Lemma 36.37.3 (0E2K)](https://stacks.math.columbia.edu/tag/0E2K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe v u d

namespace HomologicalComplex

/-- The map on degree-`j` homology induced by `g` placed in degree `j` is an epimorphism whenever
`g` is: the composite of `HomologicalComplex.single` with homology in degree `j` is isomorphic to
the identity functor, by `HomologicalComplex.homologyFunctorSingleIso`, and a functor isomorphic
to one preserving epimorphisms preserves them. -/
public theorem epi_homologyMap_single_map {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] [CategoryWithHomology C] {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)
    (j : ι) {A B : C} (g : A ⟶ B) [Epi g] :
    Epi (homologyMap ((single C c j).map g) j) :=
  have : (single C c j ⋙ homologyFunctor C c j).PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso (homologyFunctorSingleIso C c j).symm
  Functor.map_epi (single C c j ⋙ homologyFunctor C c j) g

end HomologicalComplex

namespace StrictlyPerfect

/-- A direct summand of a finite free `𝒪_X`-module, placed in a single degree, is a strictly
perfect complex: its only possibly nonzero term is in that degree, and that term is the given
module. -/
public theorem isStrictlyPerfect_single {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {D : OXMod.{u, u} X} (hD : IsDirectSummandOfFiniteFree D) (j : ℤ) :
    IsStrictlyPerfect
      ((HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) j).obj D) where
  bounded := Set.Finite.subset (Set.finite_singleton j) fun i hi =>
    Classical.byContradiction fun h => hi (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  directSummand i := by
    by_cases h : i = j
    · subst h
      exact isDirectSummandOfFiniteFree_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i D) hD
    · exact isDirectSummandOfFiniteFree_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)

/-- The structure sheaf, as a module over itself, is a direct summand of a finite free module: it
is a retract of `𝒪_X^{⊕1}` through the inclusion of and the projection onto the single summand. -/
public theorem isDirectSummandOfFiniteFree_structureModule
    (X : AlgebraicGeometry.RingedSpace.{u, u}) : IsDirectSummandOfFiniteFree (structureModule X) :=
  (isDirectSummandOfFiniteFree_iff_retract _).mpr
    ⟨1, ⟨⟨biproduct.ι (fun _ : Fin 1 => structureModule X) 0,
      biproduct.π (fun _ : Fin 1 => structureModule X) 0,
      biproduct.ι_π_self (fun _ : Fin 1 => structureModule X) 0⟩⟩⟩

end StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

open StrictlyPerfect

/-- A sheaf of `𝒪_X`-modules which, locally on `X`, receives an epimorphism from a direct summand
of a finite free module is `0`-pseudo-coherent in degree zero: as a complex concentrated in degree
zero it satisfies the local condition of Stacks 08CB for `m = 0`.

Near a point, the source of the given epimorphism placed in degree zero is the strictly perfect
approximation. Above degree zero both complexes vanish, so the map on homology there is an
isomorphism between zero objects; in degree zero the map on homology is the given epimorphism, by
`HomologicalComplex.epi_homologyMap_single_map`, followed by the identification of the restriction
of a complex concentrated in degree zero with the restriction placed in degree zero. -/
public theorem isPseudoCoherentComplexFrom_single_zero_of_exists_epi
    {X : RingedSpace.{u, u}} (B : OXMod.{u, u} X)
    (h : ∀ x : X.carrier, ∃ W : Opens X.carrier, x ∈ W ∧
      ∃ A : OXMod.{u, u} (X.restrict W.isOpenEmbedding), IsDirectSummandOfFiniteFree A ∧
        ∃ q : A ⟶ (restrictModules X W).obj B, Epi q) :
    IsPseudoCoherentComplexFrom
      ((HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj B) 0 := by
  intro x
  obtain ⟨W, hxW, A, hA, q, hq⟩ := h x
  have hiso : (HomologicalComplex.single (OXMod.{u, u} (X.restrict W.isOpenEmbedding))
        (ComplexShape.up ℤ) 0).obj ((restrictModules X W).obj B) ≅
      restrictComplex
        ((HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj B) W :=
    ((HomologicalComplex.singleMapHomologicalComplex (restrictModules X W)
      (ComplexShape.up ℤ) 0).app B).symm
  refine ⟨W, hxW, (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A,
    isStrictlyPerfect_single hA 0,
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map q ≫ hiso.hom, ?_, ?_⟩
  · intro j hj
    refine (HomologicalComplex.isZero_single_obj_homology _ _ _ _ (by lia)).isIso ?_ _
    exact HomologicalComplex.isZero_homology_of_isZero_X _ _
      ((restrictModules X W).isZero_obj
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)))
  · rw [HomologicalComplex.homologyMap_comp]
    have := HomologicalComplex.epi_homologyMap_single_map (ComplexShape.up ℤ) 0 q
    exact epi_comp _ _

/-- An object of the derived category of `𝒪_X`-modules concentrated in degree zero is
`0`-pseudo-coherent as soon as the sheaf it is concentrated at receives, locally on `X`, an
epimorphism from a direct summand of a finite free module.

The representing complex is the sheaf placed in degree zero, which
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_single_zero_of_exists_epi` shows is
`0`-pseudo-coherent as a complex. -/
public theorem isPseudoCoherentFrom_singleFunctor_zero_of_exists_epi
    {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)] (B : OXMod.{u, u} X)
    (h : ∀ x : X.carrier, ∃ W : Opens X.carrier, x ∈ W ∧
      ∃ A : OXMod.{u, u} (X.restrict W.isOpenEmbedding), IsDirectSummandOfFiniteFree A ∧
        ∃ q : A ⟶ (restrictModules X W).obj B, Epi q) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj B) 0 :=
  ⟨(HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj B,
    isPseudoCoherentComplexFrom_single_zero_of_exists_epi B h,
    ⟨eqToIso (DerivedCategory.Q_obj_single_obj (OXMod.{u, u} X) 0 B)⟩⟩

/-- An object of the derived category of `𝒪_X`-modules concentrated in degree zero is
`0`-pseudo-coherent as soon as the sheaf it is concentrated at receives a *global* epimorphism
from a direct summand of a finite free module: the whole space serves as the open neighbourhood of
every point, and restriction to it preserves both being a direct summand of a finite free module
and epimorphy. -/
public theorem isPseudoCoherentFrom_singleFunctor_zero_of_epi {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] {A B : OXMod.{u, u} X}
    (hA : IsDirectSummandOfFiniteFree A) (q : A ⟶ B) (hq : Epi q) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj B) 0 := by
  -- The module universe of `restrictModules` is not determined by its explicit arguments, so it
  -- is written out here: otherwise this instance is searched for with an unsolved universe.
  have hpe : (restrictModules.{u, u} X ⊤).PreservesEpimorphisms := inferInstance
  exact isPseudoCoherentFrom_singleFunctor_zero_of_exists_epi B fun _ =>
    ⟨⊤, trivial, (restrictModules X ⊤).obj A,
      isDirectSummandOfFiniteFree_restrictModules ⊤ hA, (restrictModules X ⊤).map q,
      hpe.preserves q⟩

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] HasDerivedCategory.standard

/-- **The comorphism of a closed immersion of schemes is surjective, in the category of sheaves of
modules.** For a closed immersion `i : Z ⟶ Y` the canonical map `𝒪_Y ⟶ i_*𝒪_Z` is an
epimorphism of `𝒪_Y`-modules.

An epimorphism of sheaves of modules is a locally surjective morphism of the underlying presheaves
of abelian groups, and the map on sections of `SheafOfModules.unitToPushforwardObjUnit` is the map
on sections of the comorphism, whose local surjectivity is
`Stacks.ClosedImmersion.isLocallySurjective_c_toShHom`; the image sieves of
`CategoryTheory.Presheaf.imageSieve` are therefore the same sieves and the covering condition
transfers. -/
public theorem epi_unitToPushforwardObjUnit {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] :
    Epi (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    ⟨fun {V} s ↦ (Stacks.ClosedImmersion.isLocallySurjective_c_toShHom i).imageSieve_mem (U := V) s⟩

/-- For a closed immersion `i : U ⟶ Y` of schemes, the local condition of Stacks 09UI holds for
`𝒪_U` in degree zero: the derived pushforward of `𝒪_U` along `i` is `0`-pseudo-coherent on `Y`.

Pushforward along a closed immersion is exact, so by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff` the condition is
`0`-pseudo-coherence of `i_*𝒪_U`, which is concentrated in degree zero
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`) and receives an epimorphism from `𝒪_Y`
by `AlgebraicGeometry.Scheme.Modules.epi_unitToPushforwardObjUnit`. -/
public theorem isPseudoCoherentFromAfterPushforward_singleFunctor_unit_zero {U Y : Scheme.{u}}
    (i : U ⟶ Y) [IsClosedImmersion i] :
    IsPseudoCoherentFromAfterPushforward i
      ((DerivedCategory.singleFunctor U.Modules 0).obj
        (SheafOfModules.unit U.ringCatSheaf)) 0 := by
  rw [isPseudoCoherentFromAfterPushforward_iff]
  exact RingedSpace.IsPseudoCoherentFrom.of_iso.{u, u + 1}
    (RingedSpace.isPseudoCoherentFrom_singleFunctor_zero_of_epi.{u, u + 1}
      (StrictlyPerfect.isDirectSummandOfFiniteFree_structureModule Y.toRingedSpace)
      (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
      (epi_unitToPushforwardObjUnit i))
    ((Functor.mapDerivedCategorySingleFunctor (pushforward i) 0).app
      (SheafOfModules.unit U.ringCatSheaf)).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

/-- **The degree-zero case of Stacks 09UI for the structure sheaf.** For a morphism of schemes
locally of finite type, `𝒪_X` is relatively `0`-pseudo-coherent over `S`.

The affine open covering of the base is the family of all affine opens, and over each member the
covering of its inverse image is the family of all affine opens of `X` contained in it; the closed
immersions into affine space are the ones produced by
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`, and the local condition at each of
them is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_unit_zero`,
transported along `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`, which identifies the
restriction of `𝒪_X` to an open subscheme with the structure sheaf of that subscheme. -/
public theorem isModulePseudoCoherentFrom_unit_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    IsModulePseudoCoherentFrom f (SheafOfModules.unit X.ringCatSheaf) 0 := by
  refine ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun V ↦ ?_⟩
  refine ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ (V : S.affineOpens).1}, fun u ↦ u.1, ?_, fun u ↦ ?_⟩
  · refine le_antisymm (iSup_le fun u ↦ u.2) fun x hx ↦ ?_
    obtain ⟨W, hW, hxW, hWle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
    exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hxW⟩
  · obtain ⟨n, i, hi, hover⟩ := exists_isClosedImmersion_affineSpace_resLE f V u.1 u.2
    have := hi
    refine ⟨u.2, n, i, hi, hover,
      Scheme.Modules.IsPseudoCoherentFromAfterPushforward.of_iso i ?_
        ((Functor.mapDerivedCategorySingleFunctor
          (Scheme.Modules.restrictFunctor (u.1).1.ι) 0).app
            (SheafOfModules.unit X.ringCatSheaf)).symm⟩
    exact Scheme.Modules.IsPseudoCoherentFromAfterPushforward.of_iso i
      (Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_unit_zero i)
      ((DerivedCategory.singleFunctor _ 0).mapIso
        (Scheme.Modules.restrictUnitIso (u.1).1.ι)).symm

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The comparison of Stacks 09VF and Stacks 09UJ at the structure sheaf holds in degree
zero.** Both sides of `AlgebraicGeometry.RelativeStructureSheafComparisonAt f hft 0` hold
outright: the left-hand side is
`AlgebraicGeometry.Scheme.Hom.isModulePseudoCoherentFrom_unit_zero` and the right-hand side is
`AlgebraicGeometry.isModuleRelativelyPseudoCoherentFrom_appLE_of_nonneg` at `m = 0`. -/
public theorem relativeStructureSheafComparisonAt_zero (hft : LocallyOfFiniteType f) :
    RelativeStructureSheafComparisonAt f hft 0 := by
  have := hft
  exact iff_of_true (Scheme.Hom.isModulePseudoCoherentFrom_unit_zero f)
    fun U hU V hV e ↦ isModuleRelativelyPseudoCoherentFrom_appLE_of_nonneg f U hU V hV e le_rfl

/-- **The comparison of Stacks 09VF and Stacks 09UJ at the structure sheaf has no content outside
the strictly negative degrees.** `AlgebraicGeometry.RelativeStructureSheafComparison f`, the
hypothesis of `AlgebraicGeometry.pseudoCoherent_tfae_of_relativeComparison`, follows from its
restriction to the degrees `m < 0`.

This sharpens `AlgebraicGeometry.relativeStructureSheafComparison_of_nonpos` by one degree, the
new case `m = 0` being `AlgebraicGeometry.relativeStructureSheafComparisonAt_zero`. The remaining
degrees are the whole content of the comparison, and they are proved in
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafComparison`, by
`AlgebraicGeometry.relativeStructureSheafComparison`. -/
public theorem relativeStructureSheafComparison_of_neg
    (h : ∀ (hft : LocallyOfFiniteType f) (m : ℤ), m < 0 →
      RelativeStructureSheafComparisonAt f hft m) :
    RelativeStructureSheafComparison f := by
  refine relativeStructureSheafComparison_of_nonpos f fun hft m hm ↦ ?_
  obtain hm' | rfl := hm.lt_or_eq
  · exact h hft m hm'
  · exact relativeStructureSheafComparisonAt_zero f hft

/-- **Stacks 067Y, the equivalence of (2) and (3), conditionally on Stacks 09VF and Stacks 09UJ in
the strictly negative degrees only.** This is
`AlgebraicGeometry.pseudoCoherent_iff_isModulePseudoCoherent_of_relativeComparison` with its
hypothesis reduced by `AlgebraicGeometry.relativeStructureSheafComparison_of_neg`; it records
the degrees in which the comparison is actually used. The unconditional form is
`AlgebraicGeometry.pseudoCoherent_iff_isModulePseudoCoherent`. -/
public theorem pseudoCoherent_iff_isModulePseudoCoherent_of_neg
    (h : ∀ (hft : LocallyOfFiniteType f) (m : ℤ), m < 0 →
      RelativeStructureSheafComparisonAt f hft m) :
    PseudoCoherent f ↔
      ∃ hft : LocallyOfFiniteType f,
        letI := hft
        Scheme.Hom.IsModulePseudoCoherent f (SheafOfModules.unit X.ringCatSheaf) :=
  pseudoCoherent_iff_isModulePseudoCoherent_of_relativeComparison f
    (relativeStructureSheafComparison_of_neg f h)

end AlgebraicGeometry

end
