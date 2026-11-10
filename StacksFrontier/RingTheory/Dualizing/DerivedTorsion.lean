module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.Algebra.Module.IPowerTorsion.SerreClass
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived torsion for a finitely generated ideal (Stacks chapter Dualizing Complexes)

Let `I` be a finitely generated ideal of a commutative ring `A`. The modules that are
`I`-power torsion — every element is annihilated by some positive power of `I` — form a Serre
subcategory of `A`-modules, so they are an abelian category with an exact inclusion into
`Mod(A)`. This file assembles the derived picture.

First, the inclusion induces a canonical comparison functor from the derived category of
`I`-power-torsion modules to the full subcategory of `D(A)` cut out by the objects all of
whose cohomology modules are `I`-power torsion. That comparison is an isomorphism on `Hom`
and on `Ext¹` between modules placed in degree zero: an extension of two `I`-power-torsion
modules is again `I`-power torsion, so the two categories compute the same `Ext¹`. These are
parts (1) and (2) of Stacks 0A6P.

In degree `2` the comparison is no longer surjective, which is part (3) of Stacks 0A6P, and the
comparison functor is therefore not an equivalence, which is part (4). The counterexample is in
`StacksFrontier.RingTheory.Dualizing.TorsionExtCounterexample`; what this file contributes to it is
the implication between the two parts, `Extⁿ` being bijective in every degree whenever the
comparison functor is an equivalence.

Second, the `I`-power-torsion submodule functor `Γ_I` (Mathlib's `Ideal.primaryComponent`) is
right adjoint to the inclusion, and this adjunction derives: the total right derived functor
`RΓ_I`, which is local cohomology, is right adjoint to the derived inclusion.

## Main definitions

* `Dualizing.powerTorsionModuleProperty` — the property of an `A`-module of being `I`-power
  torsion, indexed by a finite-generation witness so that the Serre structure is canonical.
* `Dualizing.PowerTorsionModule` — the abelian category of `I`-power-torsion `A`-modules.
* `Dualizing.derivedPowerTorsionProperty` — the property that every cohomology module of an
  object of `D(A)` is `I`-power torsion.
* `Dualizing.PowerTorsionDerivedCategory` — the corresponding full subcategory of `D(A)`.
* `Dualizing.powerTorsionComparison` — the comparison functor
  `D(I^∞-torsion) ⥤ D_{I^∞-torsion}(A)`.
* `Dualizing.IPowerTorsionModule`, `Dualizing.powerTorsionFunctor` — the torsion category and
  the torsion-submodule functor in the universe required by the construction of enough
  injectives.
* `Dualizing.derivedPowerTorsion` — local cohomology `RΓ_I`, the total right derived functor
  of `Dualizing.powerTorsionFunctor`.
* `Dualizing.powerTorsionCounit`, `Dualizing.powerTorsionHomotopyInclusion` — the inclusion of
  the `I`-power-torsion submodule, on modules and degreewise on the homotopy category.
* `Dualizing.powerTorsionAdjunction` — the underived adjunction between that inclusion and
  `Γ_I`.
* `Dualizing.derivedPowerTorsionUnit` — the total right derived unit of `RΓ_I`.
* `Dualizing.IsCanonicalDerivedPowerTorsionCounit` — the normalization condition on a derived
  map `RΓ_I ⋙ ι ⟶ 𝟭`: its composite with the derived unit is the degreewise torsion inclusion.
The normalized derived adjunction itself, and the canonical derived map `RΓ_I → id` it supplies,
are `Dualizing.derivedPowerTorsionAdjunction` and `Dualizing.derivedPowerTorsionCounit` in
`StacksFrontier.RingTheory.Dualizing.DerivedTorsionCounit`.

## Main results

* `Dualizing.bijective_derivedInclusion_map_singleFunctor` — the degree-zero `Hom` comparison
  is bijective.
* `Dualizing.bijective_mapExt_one_powerTorsionModule` — the `Ext¹` comparison is bijective.
* `Dualizing.bijective_mapExtAddHom_of_fullyFaithful_mapDerivedCategory` — an exact functor which
  is fully faithful on derived categories is bijective on `Extⁿ` in every degree.
* `Dualizing.bijective_mapExt_powerTorsionModule_of_isEquivalence` and
  `Dualizing.not_isEquivalence_powerTorsionComparison_of_not_surjective_mapExt` — if the
  comparison functor is an equivalence then the `Extⁿ` comparison is bijective in every degree,
  so a single failure of surjectivity shows the comparison functor is not an equivalence.
* `Dualizing.derivedInclusion_adj_derivedPowerTorsion` — the derived inclusion is left adjoint
  to `RΓ_I`, by an adjunction whose counit is normalized by the torsion-submodule inclusion.
  That the counit of the chosen adjunction is so normalized is
  `Dualizing.derivedPowerTorsionCounit_isCanonical`, in
  `StacksFrontier.RingTheory.Dualizing.DerivedTorsionCounit`.

## Implementation notes

The finite-generation witness is an argument of `powerTorsionModuleProperty` and
`derivedPowerTorsionProperty`. Their values do not depend on it, but retaining it in the type
lets Lean infer the Serre structure that the source derived category needs; proof irrelevance
makes the choice immaterial.

`powerTorsionComparison` is the lift of the derived functor of the Serre inclusion, so its
composite with the inclusion of the target full subcategory is definitionally the usual
derived functor; `powerTorsionComparisonCompInclusionIso` records that factorization. The
`Hom` comparison is phrased as the map on morphisms of that derived functor, which records its
canonical, natural character.

For `RΓ_I` the module universe is enlarged to `max u v`, as required by the available
construction of enough injectives, and the existence of the total right derived functor comes
from K-injective resolutions of unbounded complexes.

## References

* [Stacks Project, Tag 0A6L](https://stacks.math.columbia.edu/tag/0A6L)
* [Stacks Project, Tag 0A6N](https://stacks.math.columbia.edu/tag/0A6N)
* [Stacks Project, Tag 0A6P](https://stacks.math.columbia.edu/tag/0A6P)
* [Stacks Project, Tag 06UR](https://stacks.math.columbia.edu/tag/06UR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w w' t t'

namespace Dualizing

/-- An exact functor read on derived categories commutes with cohomology degree by degree. -/
noncomputable def mapDerivedCategoryHomologyIso
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] (i : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D i ≅
      DerivedCategory.homologyFunctor C i ⋙ F := by
  let e : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i ⋙ F :=
    NatIso.ofComponents (fun P ↦ (P.sc i).mapHomologyIso F) (fun φ ↦
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map φ) F)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D i))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C i ⋙ F)) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor D i) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors D i) ≪≫ e ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C i).symm F)

section Comparison

open Limits ZeroObject

/-- The object property on `A`-modules of being `I`-power torsion. The finite-generation
hypothesis is retained as an index so that the associated Serre structure is canonical. -/
def powerTorsionModuleProperty (A : Type u) [CommRing A] (I : Ideal A) (_hI : I.FG) :
    ObjectProperty (ModuleCat.{v} A) :=
  fun M ↦ IsIPowerTorsion A M I

/-- For a finitely generated ideal `I`, the `I`-power-torsion modules form a Serre subcategory. -/
instance powerTorsionModuleProperty_isSerreClass
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (powerTorsionModuleProperty A I hI).IsSerreClass where
  exists_zero := ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _, by
      intro m
      exact ⟨1, Nat.zero_lt_one, fun _ _ ↦ Subsingleton.elim _ _⟩⟩
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [powerTorsionModuleProperty,
      isIPowerTorsion_iff_support_subset A S.X₂ I hI]
    rw [Module.support_of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
      hS.moduleCat_injective_f hS.moduleCat_surjective_g]
    exact Set.union_subset
      ((isIPowerTorsion_iff_support_subset A S.X₁ I hI).mp h₁)
      ((isIPowerTorsion_iff_support_subset A S.X₃ I hI).mp h₃)
  prop_of_mono {X Y} f _ hY := by
    rw [powerTorsionModuleProperty,
      isIPowerTorsion_iff_support_subset A X I hI]
    exact (Module.support_subset_of_injective f.hom
      ((ModuleCat.mono_iff_injective f).mp inferInstance)).trans
      ((isIPowerTorsion_iff_support_subset A Y I hI).mp hY)
  prop_of_epi {X Y} f _ hX := by
    rw [powerTorsionModuleProperty,
      isIPowerTorsion_iff_support_subset A Y I hI]
    exact (Module.support_subset_of_surjective f.hom
      ((ModuleCat.epi_iff_surjective f).mp inferInstance)).trans
      ((isIPowerTorsion_iff_support_subset A X I hI).mp hX)

/-- The inclusion of `I`-power-torsion `A`-modules into all `A`-modules preserves finite limits. -/
instance powerTorsionModuleProperty_preservesFiniteLimits
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    PreservesFiniteLimits (powerTorsionModuleProperty A I hI).ι :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion of `I`-power-torsion `A`-modules into all `A`-modules preserves finite colimits.
-/
instance powerTorsionModuleProperty_preservesFiniteColimits
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    PreservesFiniteColimits (powerTorsionModuleProperty A I hI).ι :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

/-- The category of `I`-power-torsion `A`-modules. -/
abbrev PowerTorsionModule (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :=
  (powerTorsionModuleProperty A I hI).FullSubcategory

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The property on `D(A)` that every cohomology module is `I`-power torsion. -/
def derivedPowerTorsionProperty (A : Type u) [CommRing A] (I : Ideal A) (_hI : I.FG) :
    ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
  fun K ↦ ∀ i : ℤ,
    IsIPowerTorsion A ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K) I

/-- The full subcategory of `D(A)` whose objects have `I`-power-torsion cohomology. -/
abbrev PowerTorsionDerivedCategory
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :=
  (derivedPowerTorsionProperty A I hI).FullSubcategory

/-- **Stacks 0A6N.** The canonical functor from the derived category of `I`-power-torsion
`A`-modules to the full subcategory of `D(A)` on the objects with `I`-power-torsion cohomology. -/
@[stacks 0A6N]
noncomputable def powerTorsionComparison
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    DerivedCategory (PowerTorsionModule A I hI) ⥤
      PowerTorsionDerivedCategory A I hI :=
  (derivedPowerTorsionProperty A I hI).lift
    (powerTorsionModuleProperty A I hI).ι.mapDerivedCategory (fun K ↦ by
      intro i
      exact (powerTorsionModuleProperty A I hI).prop_of_iso
        ((mapDerivedCategoryHomologyIso
          (powerTorsionModuleProperty A I hI).ι i).app K).symm
        ((powerTorsionModuleProperty A I hI).prop_ι_obj
          ((DerivedCategory.homologyFunctor (PowerTorsionModule A I hI) i).obj K)))

/-- Composing the comparison functor with the inclusion into `D(A)` gives the derived functor
of the inclusion of `I`-power-torsion modules. -/
noncomputable def powerTorsionComparisonCompInclusionIso
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    powerTorsionComparison A I hI ⋙ (derivedPowerTorsionProperty A I hI).ι ≅
      (powerTorsionModuleProperty A I hI).ι.mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

/-- The inclusion of power-torsion modules induces a bijection on derived
morphisms between modules concentrated in degree zero. -/
@[stacks 0A6P "part (1), the Hom comparison"]
theorem bijective_derivedInclusion_map_singleFunctor
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M N : PowerTorsionModule.{u, v} A I hI) :
    let F := (powerTorsionModuleProperty A I hI).ι.mapDerivedCategory
    let X := (DerivedCategory.singleFunctor
      (PowerTorsionModule.{u, v} A I hI) 0).obj M
    let Y := (DerivedCategory.singleFunctor
      (PowerTorsionModule.{u, v} A I hI) 0).obj N
    Function.Bijective (fun f : X ⟶ Y ↦ F.map f) := by
  dsimp
  let G := (powerTorsionModuleProperty A I hI).ι
  let s := DerivedCategory.singleFunctor (PowerTorsionModule.{u, v} A I hI) 0
  let t := DerivedCategory.singleFunctor (ModuleCat.{v} A) 0
  let e := Functor.mapDerivedCategorySingleFunctor G 0
  apply (Function.Bijective.of_comp_iff
    (fun f : s.obj M ⟶ s.obj N ↦ G.mapDerivedCategory.map f)
    ((Functor.FullyFaithful.ofFullyFaithful s).homEquiv.bijective)).mp
  have h : Function.Bijective (fun g : M ⟶ N ↦
      e.hom.app M ≫ t.map (G.map g) ≫ e.inv.app N) :=
    ((asIso (e.hom.app M)).symm.homCongr (asIso (e.inv.app N))).bijective.comp
      ((Functor.FullyFaithful.ofFullyFaithful t).homEquiv.bijective.comp
        (ObjectProperty.fullyFaithfulι _).homEquiv.bijective)
  convert h using 1
  funext g
  simpa [Functor.comp_map, Category.assoc] using
    congrArg (fun k => k ≫ e.inv.app N) (e.hom.naturality g)

end Derived

end Comparison

section Ext

attribute [local instance] CategoryTheory.HasExt.standard

private lemma mapExtClass_fullSubcategory
    {C : Type u} [Category.{v} C] [Abelian C]
    (P : ObjectProperty C) [P.IsSerreClass] [Limits.PreservesFiniteLimits P.ι]
    [Limits.PreservesFiniteColimits P.ι]
    (S : ShortComplex P.FullSubcategory) (hS : S.ShortExact) :
    (P.ι).mapExtAddHom S.X₃ S.X₁ 1 hS.extClass =
      (hS.map_of_exact P.ι).extClass := by
  rw [Functor.mapExtAddHom_apply]
  exact Abelian.Ext.mapExactFunctor_extClass P.ι hS

/-- The exact inclusion of the category of `I`-power-torsion modules into all `A`-modules is
injective on Ext¹: two extensions with the same image are isomorphic as extensions of
`I`-power-torsion modules. -/
private theorem injective_mapExt_one_powerTorsionModule
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M N : PowerTorsionModule.{u, v} A I hI) :
    Function.Injective
      ((powerTorsionModuleProperty A I hI).ι.mapExtAddHom M N 1) := by
  let P := powerTorsionModuleProperty A I hI
  let F := P.ι
  let eP := Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum P.FullSubcategory M N
  let eA := Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
    (ModuleCat A) (F.obj M) (F.obj N)
  intro x y hxy
  obtain ⟨E, i, p, w, hE, hx⟩ := eP.1 x
  obtain ⟨E', i', p', w', hE', hy⟩ := eP.1 y
  let S : ShortComplex P.FullSubcategory := ShortComplex.mk i p w
  let S' : ShortComplex P.FullSubcategory := ShortComplex.mk i' p' w'
  have hS : S.ShortExact := hE
  have hS' : S'.ShortExact := hE'
  let T := S.map F
  let T' := S'.map F
  have hT : T.ShortExact := hS.map_of_exact F
  have hT' : T'.ShortExact := hS'.map_of_exact F
  have hmap : hT.extClass = hT'.extClass := by
    calc
      hT.extClass = F.mapExtAddHom M N 1 hS.extClass :=
        (mapExtClass_fullSubcategory P S hS).symm
      _ = F.mapExtAddHom M N 1 x := congrArg (F.mapExtAddHom M N 1) hx
      _ = F.mapExtAddHom M N 1 y := hxy
      _ = F.mapExtAddHom M N 1 hS'.extClass :=
        congrArg (F.mapExtAddHom M N 1) hy.symm
      _ = hT'.extClass := mapExtClass_fullSubcategory P S' hS'
  obtain ⟨φ, hφ₁, hφ₂⟩ := (eA.2.1 T.X₂ T'.X₂ T.f T.g T.zero
    T'.f T'.g T'.zero hT hT').1 hmap
  have hsource : hS.extClass = hS'.extClass := by
    apply (eP.2.1 S.X₂ S'.X₂ i p w i' p' w' hS hS').2
    refine ⟨P.isoMk φ, ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      change i.hom ≫ φ.hom = i'.hom
      simpa [T, T', S, S', ShortComplex.map, F] using hφ₁
    · apply ObjectProperty.hom_ext
      change φ.hom ≫ p'.hom = p.hom
      simpa [T, T', S, S', ShortComplex.map, F] using hφ₂
  exact hx.symm.trans (hsource.trans hy)

/-- The exact inclusion of the category of `I`-power-torsion modules into all `A`-modules is
surjective on Ext¹: an extension of `I`-power-torsion modules is again `I`-power torsion. -/
private theorem surjective_mapExt_one_powerTorsionModule
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M N : PowerTorsionModule.{u, v} A I hI) :
    Function.Surjective
      ((powerTorsionModuleProperty A I hI).ι.mapExtAddHom M N 1) := by
  let P := powerTorsionModuleProperty A I hI
  let F := P.ι
  intro x
  obtain ⟨E, i, p, w, hE, hx⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (ModuleCat A) (F.obj M) (F.obj N)).1 x
  let E' : P.FullSubcategory := ⟨E, P.prop_X₂_of_exact hE.exact N.property M.property⟩
  let i' : N ⟶ E' := ObjectProperty.homMk i
  let p' : E' ⟶ M := ObjectProperty.homMk p
  let S : ShortComplex P.FullSubcategory :=
    ShortComplex.mk i' p' (ObjectProperty.hom_ext _ w)
  have hS : S.ShortExact := (CategoryTheory.ShortExact.shortExact_map_iff F).1 hE
  exact ⟨hS.extClass, (mapExtClass_fullSubcategory P S hS).trans hx⟩

/-- **Stacks 0A6P, Ext¹ comparison.** The exact inclusion of the category of
`I`-power-torsion modules into all `A`-modules induces a bijection on Ext¹. -/
@[stacks 0A6P "part (2), the Ext¹ comparison"]
theorem bijective_mapExt_one_powerTorsionModule
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M N : PowerTorsionModule.{u, v} A I hI) :
    Function.Bijective
      ((powerTorsionModuleProperty A I hI).ι.mapExtAddHom M N 1) :=
  ⟨injective_mapExt_one_powerTorsionModule A I hI M N,
    surjective_mapExt_one_powerTorsionModule A I hI M N⟩

end Ext

section ExtCriterion

attribute [local instance] HasDerivedCategory.standard CategoryTheory.HasExt.standard

/-- An exact functor which is fully faithful on derived categories induces a bijection on
`Extⁿ` for every `n`. Indeed the map on `Extⁿ` is, conjugated by the canonical comparison of
the derived functor with the degree-zero inclusions, the map on shifted morphisms of the induced
functor on derived categories, and that map is a composite of the bijection on morphisms of a
fully faithful functor with composition by isomorphisms. -/
@[sga "6 II 2.1.3" "special case"]
theorem bijective_mapExtAddHom_of_fullyFaithful_mapDerivedCategory
    {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F]
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    [HasExt.{w} C] [HasExt.{w'} D]
    [F.mapDerivedCategory.Full] [F.mapDerivedCategory.Faithful]
    (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapExtAddHom.{w, w'} X Y n) := by
  let Φ := F.mapDerivedCategory
  let e := F.mapDerivedCategorySingleFunctor (0 : ℤ)
  let sX := (DerivedCategory.singleFunctor C 0).obj X
  let sY := (DerivedCategory.singleFunctor C 0).obj Y
  let iso₂ : Φ.obj (sY⟦(n : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor D 0).obj (F.obj Y))⟦(n : ℤ)⟧ :=
    (Φ.commShiftIso (n : ℤ)).app sY ≪≫
      (shiftFunctor (DerivedCategory D) (n : ℤ)).mapIso (asIso (e.hom.app Y))
  have hff : Function.Bijective (fun α : (sX ⟶ sY⟦(n : ℤ)⟧) ↦ Φ.map α) :=
    (Functor.FullyFaithful.ofFullyFaithful Φ).homEquiv.bijective
  let Ψ : ShiftedHom sX sY (n : ℤ) → ShiftedHom ((DerivedCategory.singleFunctor D 0).obj (F.obj X))
      ((DerivedCategory.singleFunctor D 0).obj (F.obj Y)) (n : ℤ) := fun α ↦
    e.inv.app X ≫ ShiftedHom.map α Φ ≫
      (shiftFunctor (DerivedCategory D) (n : ℤ)).map (e.hom.app Y)
  have hΨ : Function.Bijective Ψ := by
    have heq : Ψ =
        ((asIso (e.hom.app X)).homCongr iso₂) ∘ (fun α : (sX ⟶ sY⟦(n : ℤ)⟧) ↦ Φ.map α) := by
      funext α
      simp [Ψ, ShiftedHom.map, Iso.homCongr, iso₂, Category.assoc]
    rw [heq]
    exact (Iso.homCongr (asIso (e.hom.app X)) iso₂).bijective.comp hff
  have hcomp : (Abelian.Ext.homEquiv (C := D) (X := F.obj X) (Y := F.obj Y) (n := n)) ∘
      (F.mapExtAddHom.{w, w'} X Y n) =
      Ψ ∘ (Abelian.Ext.homEquiv (C := C) (X := X) (Y := Y) (n := n)) := by
    funext a
    exact Abelian.Ext.mapExactFunctor_hom F a
  refine ((Abelian.Ext.homEquiv (C := D) (X := F.obj X) (Y := F.obj Y)
    (n := n)).bijective.of_comp_iff' ⇑(F.mapExtAddHom.{w, w'} X Y n)).mp ?_
  rw [hcomp]
  exact hΨ.comp (Abelian.Ext.homEquiv (C := C) (X := X) (Y := Y) (n := n)).bijective

/-- If the comparison functor of Stacks 0A6N is fully faithful then so is the derived functor of
the inclusion of `I`-power-torsion modules, the comparison functor being its factorization
through a full subcategory of `D(A)`. -/
noncomputable def fullyFaithful_mapDerivedCategory_inclusion_of_powerTorsionComparison
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (hff : (powerTorsionComparison A I hI).FullyFaithful) :
    ((powerTorsionModuleProperty A I hI).ι.mapDerivedCategory).FullyFaithful := by
  have h : (powerTorsionComparison A I hI ⋙
      (derivedPowerTorsionProperty A I hI).ι).FullyFaithful :=
    hff.comp (ObjectProperty.fullyFaithfulι _)
  haveI := h.full
  haveI := h.faithful
  haveI := Functor.Full.of_iso (powerTorsionComparisonCompInclusionIso A I hI)
  haveI := Functor.Faithful.of_iso (powerTorsionComparisonCompInclusionIso A I hI)
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- **Stacks 0A6P, part (4) from part (3).** If the comparison functor of Stacks 0A6N is an
equivalence, then the inclusion of `I`-power-torsion modules induces a bijection on `Extⁿ`
between torsion modules, in every degree `n`.

Parts (1) and (2) of Stacks 0A6P are the cases `n = 0` and `n = 1`, which hold unconditionally;
in degree `2` the conclusion fails for some ring and ideal, which is part (3), and this is how
part (4) — that the comparison functor is not an equivalence in general — is deduced from it.
See `Dualizing.not_isEquivalence_powerTorsionComparison_of_not_surjective_mapExt`. -/
theorem bijective_mapExt_powerTorsionModule_of_isEquivalence
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    [(powerTorsionComparison.{u, v} A I hI).IsEquivalence]
    (M N : PowerTorsionModule.{u, v} A I hI) (n : ℕ) :
    Function.Bijective ((powerTorsionModuleProperty A I hI).ι.mapExtAddHom M N n) := by
  have hff := fullyFaithful_mapDerivedCategory_inclusion_of_powerTorsionComparison.{u, v}
    A I hI (Functor.FullyFaithful.ofFullyFaithful (powerTorsionComparison.{u, v} A I hI))
  have := hff.full
  have := hff.faithful
  exact bijective_mapExtAddHom_of_fullyFaithful_mapDerivedCategory
    (powerTorsionModuleProperty A I hI).ι M N n

/-- **Stacks 0A6P, part (4) from part (3).** The comparison functor of Stacks 0A6N is not an
equivalence as soon as the `Extⁿ` comparison of Stacks 0A6P fails to be surjective for a single
pair of `I`-power-torsion modules. The source deduces part (4) from part (3) in exactly this
way, part (3) being the failure of surjectivity in degree `n = 2`, which is
`Dualizing.exists_not_surjective_mapExt_two_powerTorsionModule`. -/
theorem not_isEquivalence_powerTorsionComparison_of_not_surjective_mapExt
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M N : PowerTorsionModule.{u, v} A I hI) (n : ℕ)
    (h : ¬ Function.Surjective ((powerTorsionModuleProperty A I hI).ι.mapExtAddHom M N n)) :
    ¬ (powerTorsionComparison.{u, v} A I hI).IsEquivalence := by
  intro hequiv
  exact h (bijective_mapExt_powerTorsionModule_of_isEquivalence.{u, v} A I hI M N n).2

end ExtCriterion

section LocalCohomology

open CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

private noncomputable def mapHomotopyCategoryAdjunction
    {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : G ⊣ F)
    (c : ComplexShape ℤ) : G.mapHomotopyCategory c ⊣ F.mapHomotopyCategory c := by
  let adjC : G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c := {
    unit :=
      { app := fun X => { f := fun n => adj.unit.app (X.X n), comm' := fun _ _ _ => by simp }
        naturality := fun X Y f => by ext n; simp }
    counit :=
      { app := fun Y => { f := fun n => adj.counit.app (Y.X n), comm' := fun _ _ _ => by simp }
        naturality := fun X Y f => by ext n; simp }
    left_triangle_components := by intro X; ext n; simp
    right_triangle_components := by intro Y; ext n; simp }
  refine {
    unit := Quotient.natTransLift _
      (Functor.whiskerRight adjC.unit (HomotopyCategory.quotient D c))
    counit := Quotient.natTransLift _
      (Functor.whiskerRight adjC.counit (HomotopyCategory.quotient C c))
    left_triangle_components := ?_
    right_triangle_components := ?_ }
  · rintro ⟨X⟩
    exact ((HomotopyCategory.quotient C c).map_comp _ _).symm.trans
      ((congrArg _ (adjC.left_triangle_components X)).trans
        ((HomotopyCategory.quotient C c).map_id _))
  · rintro ⟨Y⟩
    exact ((HomotopyCategory.quotient D c).map_comp _ _).symm.trans
      ((congrArg _ (adjC.right_triangle_components Y)).trans
        ((HomotopyCategory.quotient D c).map_id _))

/-- The abelian category of modules which are elementwise annihilated by positive powers of
`I`. -/
abbrev IPowerTorsionModule (A : Type u) [CommRing A] (I : Ideal A) :=
  ObjectProperty.FullSubcategory
    ((fun M : ModuleCat.{max u v} A => IsIPowerTorsion A M I) :
      ObjectProperty (ModuleCat.{max u v} A))

/-- The functor taking an `A`-module to its `I`-power-torsion submodule. -/
def powerTorsionFunctor (A : Type u) [CommRing A] (I : Ideal A) :
    ModuleCat.{max u v} A ⥤ IPowerTorsionModule.{u, v} A I where
  obj M := ⟨ModuleCat.of A (Ideal.primaryComponent M I), fun x => by
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp x.property
    refine ⟨n + 1, Nat.succ_pos n, fun a ha => ?_⟩
    rw [Submodule.mem_torsionBySet_iff] at hn
    exact Subtype.ext (hn ⟨a, Ideal.pow_le_pow_right n.le_succ ha⟩)⟩
  map {M N} f := ⟨ModuleCat.ofHom (Ideal.primaryComponent.map I f.hom)⟩
  map_id M := by
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    rfl
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    rfl

/-- The `I`-power-torsion-submodule functor is additive. -/
instance powerTorsionFunctor_additive (A : Type u) [CommRing A] (I : Ideal A) :
    (powerTorsionFunctor.{u, v} A I).Additive where
  map_add := by
    intro M N f g
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    rfl

/-- The total right derived functor of the `I`-power-torsion-submodule functor. This is
local cohomology `RΓ_I`, valued in the derived category of `I`-power-torsion modules. -/
@[implicit_reducible]
noncomputable def derivedPowerTorsion (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) :
    let P : ObjectProperty (ModuleCat.{max u v} A) :=
      fun M => IsIPowerTorsion A M I
    letI : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
    DerivedCategory (ModuleCat.{max u v} A) ⥤ DerivedCategory P.FullSubcategory := by
  let P : ObjectProperty (ModuleCat.{max u v} A) :=
    fun M => IsIPowerTorsion A M I
  let : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
  let : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  let F : ModuleCat.{max u v} A ⥤ ObjectProperty.FullSubcategory P :=
    powerTorsionFunctor.{u, v} A I
  let : HasPointwiseRightDerivedFunctor
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := ObjectProperty.FullSubcategory P))
        (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) :=
    (hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
        max u v, max (u + 1) (v + 1), max (u + 1) (v + 1),
        max (u + 1) (v + 1), max (u + 1) (v + 1), max (u + 1) (v + 1)}
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := ObjectProperty.FullSubcategory P))
      (fun K ↦ by
        obtain ⟨J, q, hq, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective K
        exact ⟨J, q, hJ, hq⟩)).1
  exact (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh (C := ObjectProperty.FullSubcategory P)).totalRightDerived
    DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))

/-- The inclusion of the `I`-power-torsion modules into `Mod(A)` is left adjoint to the
`I`-power-torsion-submodule functor `Γ_I`. This is the underived adjunction whose derived form
is `Dualizing.derivedInclusion_adj_derivedPowerTorsion`. -/
@[no_expose] noncomputable def powerTorsionAdjunction
    (A : Type u) [CommRing A] (I : Ideal A) :
    let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
    P.ι ⊣ powerTorsionFunctor.{u, v} A I := by
  let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
  refine Adjunction.mkOfHomEquiv ⟨fun X Y => {
    toFun := fun f => ⟨ModuleCat.ofHom (f.hom.codRestrict
      (Ideal.primaryComponent Y I) (fun x => ?_))⟩
    invFun := fun g => (P.ι.map g) ≫
      ModuleCat.ofHom (Ideal.primaryComponent Y I).subtype
    left_inv := ?_
    right_inv := ?_ }, by cat_disch, by cat_disch⟩
  · rw [Ideal.primaryComponent_mem]
    obtain ⟨n, hn, hkill⟩ := X.property x
    refine ⟨n, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    simpa using congrArg f.hom (hkill a a.property)
  · intro f
    apply ModuleCat.hom_ext
    ext x
    rfl
  · intro g
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    rfl

/-- The underived counit is the inclusion of the torsion submodule. -/
def powerTorsionCounit (A : Type u) [CommRing A] (I : Ideal A) :
    let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
    powerTorsionFunctor.{u, v} A I ⋙ P.ι ⟶ 𝟭 _ where
  app M := ModuleCat.ofHom (Ideal.primaryComponent M I).subtype
  naturality _ _ _ := by ext x; rfl

/-- The torsion adjunction uses the actual submodule inclusion as its counit. -/
theorem powerTorsionAdjunction_counit (A : Type u) [CommRing A] (I : Ideal A) :
    (powerTorsionAdjunction.{u, v} A I).counit = powerTorsionCounit.{u, v} A I := by
  ext M x
  rfl

/-- The degreewise torsion-submodule inclusion on the homotopy category. -/
noncomputable def powerTorsionHomotopyInclusion
    (A : Type u) [CommRing A] (I : Ideal A) :
    let P : ObjectProperty (ModuleCat.{max u v} A) :=
      fun M ↦ IsIPowerTorsion A M I
    (powerTorsionFunctor.{u, v} A I).mapHomotopyCategory (.up ℤ) ⋙
      P.ι.mapHomotopyCategory (.up ℤ) ⟶ 𝟭 _ := by
  let P : ObjectProperty (ModuleCat.{max u v} A) :=
    fun M ↦ IsIPowerTorsion A M I
  let ε : (powerTorsionFunctor.{u, v} A I).mapHomologicalComplex (.up ℤ) ⋙
      P.ι.mapHomologicalComplex (.up ℤ) ⟶ 𝟭 _ :=
    { app := fun K ↦
        { f := fun n ↦ (powerTorsionCounit.{u, v} A I).app (K.X n)
          comm' := fun _ _ _ ↦ by ext x; rfl }
      naturality := fun K L f ↦ by ext n x; rfl }
  exact Quotient.natTransLift _
    (Functor.whiskerRight ε (HomotopyCategory.quotient _ (.up ℤ)))

/-- The canonical unit used to construct the total right derived torsion functor. -/
noncomputable def derivedPowerTorsionUnit
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    let P : ObjectProperty (ModuleCat.{max u v} A) :=
      fun M ↦ IsIPowerTorsion A M I
    letI : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
    (powerTorsionFunctor.{u, v} A I).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedPowerTorsion.{u, v} A I hI := by
  let P : ObjectProperty (ModuleCat.{max u v} A) :=
    fun M ↦ IsIPowerTorsion A M I
  letI : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
  letI : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  let F := powerTorsionFunctor.{u, v} A I
  let H := F.mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh (C := P.FullSubcategory)
  letI : H.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ)) :=
    (hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
        max u v, max (u + 1) (v + 1), max (u + 1) (v + 1),
        max (u + 1) (v + 1), max (u + 1) (v + 1), max (u + 1) (v + 1)} H
      (fun K ↦ by
        obtain ⟨J, q, hq, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective K
        exact ⟨J, q, hJ, hq⟩)).1
  exact H.totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (.up ℤ))

/-- A derived map `RΓ_I → id` is canonical if its composite with the derived functor's unit is
the degreewise torsion-submodule inclusion. On a K-injective resolution the unit is invertible,
so this condition pins the map completely. -/
def IsCanonicalDerivedPowerTorsionCounit
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
    letI : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
    letI : PreservesFiniteLimits P.ι :=
      ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
    letI : PreservesFiniteColimits P.ι :=
      ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
    (derivedPowerTorsion.{u, v} A I hI ⋙ P.ι.mapDerivedCategory ⟶ 𝟭 _) →
      Prop := by
  let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
  letI : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
  letI : PreservesFiniteLimits P.ι :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
  letI : PreservesFiniteColimits P.ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
  exact fun ε ↦ ∀ K,
    P.ι.mapDerivedCategory.map
        ((derivedPowerTorsionUnit.{u, v} A I hI).app K) ≫
        ε.app (DerivedCategory.Qh.obj K) =
      P.ι.mapDerivedCategoryFactorsh.hom.app
          (((powerTorsionFunctor.{u, v} A I).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((powerTorsionHomotopyInclusion.{u, v} A I).app K)

/-- For `β : H ⟶ L ⋙ RF` with `L` inverting `W`, the cocone on the `W`-morphisms out of `K`
with vertex `RF (L K)` whose coprojection at `s` is `β` followed by the inverse of `RF (L s)`. -/
private noncomputable def coconeOfUnit {D D' E : Type*} [Category D] [Category D'] [Category E]
    (H : D ⥤ E) (W : MorphismProperty D) (L : D ⥤ D') (hL : W.IsInvertedBy L) (RF : D' ⥤ E)
    (β : H ⟶ L ⋙ RF) (K : D) :
    Cocone (MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙ H) where
  pt := RF.obj (L.obj K)
  ι :=
    { app := fun s => by
        letI : IsIso (L.map s.hom) := hL s.hom s.prop
        exact β.app s.right ≫ inv (RF.map (L.map s.hom))
      naturality := by
        intro s t f
        dsimp
        have : IsIso (L.map s.hom) := hL s.hom s.prop
        have : IsIso (L.map t.hom) := hL t.hom t.prop
        have hmap : RF.map (L.map f.right) ≫ inv (RF.map (L.map t.hom)) =
            inv (RF.map (L.map s.hom)) := by
          rw [IsIso.comp_inv_eq, IsIso.eq_inv_comp]
          simp only [← Functor.map_comp, MorphismProperty.Under.w f]
        simpa only [Functor.comp_map, Category.assoc, Category.comp_id, hmap] using
          β.naturality f.right =≫ inv (RF.map (L.map t.hom)) }

/-- Let `β : H ⟶ Qh ⋙ RF` be invertible at K-injective complexes, in a category where every
complex has a K-injective resolution. If `β` is invertible at the target of a
quasi-isomorphism `s₀` out of `K`, then every transition morphism of the cocone
`coconeOfUnit` factors through the section `RF (Qh s₀) ≫ β⁻¹` after enlarging the index. -/
private theorem exists_transition_factor_coconeOfUnit
    {C E : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Category E]
    (H : HomotopyCategory C (ComplexShape.up ℤ) ⥤ E) (RF : DerivedCategory C ⥤ E)
    (β : H ⟶ DerivedCategory.Qh ⋙ RF)
    (hK : ∀ K : CochainComplex C ℤ, ∃ (J : CochainComplex C ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (hβ : ∀ J : CochainComplex C ℤ, J.IsKInjective →
      IsIso (β.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J)))
    {K : HomotopyCategory C (ComplexShape.up ℤ)}
    (s₀ s : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).Under ⊤ K)
    [IsIso (β.app s₀.right)] :
    ∃ (t : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).Under ⊤ K) (u : s ⟶ t)
      (v : s₀ ⟶ t),
      H.map u.right = (coconeOfUnit H (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
          DerivedCategory.Qh (Localization.inverts DerivedCategory.Qh
            (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))) RF β K).ι.app s ≫
        (RF.map (DerivedCategory.Qh.map s₀.hom) ≫ inv (β.app s₀.right)) ≫ H.map v.right := by
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := C)
  let z : W.RightFraction s₀.right s.right := ⟨s₀.hom, s₀.prop, s.hom⟩
  obtain ⟨w, hw⟩ := z.exists_leftFraction
  obtain ⟨Yc, eY⟩ := HomotopyCategory.quotient_obj_surjective w.Y'
  obtain ⟨Jc', p, hpJ, hp⟩ := hK Yc
  let p' := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map p
  let eYh : w.Y' ⟶ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Yc :=
    eqToHom eY.symm
  let umap := w.s ≫ eYh ≫ p'
  have humap : W umap := W.comp_mem _ _ w.hs (W.comp_mem _ _ (W.of_isIso eYh)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp))
  let t : W.Under ⊤ K :=
    MorphismProperty.Under.mk ⊤ (s.hom ≫ umap) (W.comp_mem _ _ s.prop humap)
  let u : s ⟶ t := MorphismProperty.Under.homMk umap rfl
  let v : s₀ ⟶ t := MorphismProperty.Under.homMk (w.f ≫ eYh ≫ p') (by
    simpa [t, umap, z, Category.assoc, MorphismProperty.Under.mk_hom] using
      congrArg (fun k => k ≫ eYh ≫ p') hw.symm)
  refine ⟨t, u, v, ?_⟩
  have := hβ Jc' hpJ
  apply (cancel_mono (β.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Jc'))).1
  have : IsIso (Q.map s.hom) := Localization.inverts Q W s.hom s.prop
  change H.map u.right ≫ β.app t.right =
    ((β.app s.right ≫ inv (RF.map (Q.map s.hom))) ≫
      (RF.map (Q.map s₀.hom) ≫ inv (β.app s₀.right)) ≫ H.map v.right) ≫ β.app t.right
  have hvβ : H.map v.right ≫ β.app t.right = β.app s₀.right ≫ RF.map (Q.map v.right) := by
    simpa only [Functor.comp_map] using β.naturality v.right
  have hX : RF.map (Q.map u.right) =
      inv (RF.map (Q.map s.hom)) ≫ RF.map (Q.map s₀.hom) ≫ RF.map (Q.map v.right) := by
    rw [IsIso.eq_inv_comp]
    simp only [← Functor.map_comp, MorphismProperty.Under.w u, MorphismProperty.Under.w v]
  rw [β.naturality u.right]
  simp only [Functor.comp_map, Category.assoc, hvβ, IsIso.inv_hom_id_assoc]
  exact congrArg (β.app s.right ≫ ·) hX

/-- Let `H` be a functor on `K(C)`, in a category where every complex has a K-injective
resolution, and let `β : H ⟶ Qh ⋙ RF` be invertible at K-injective complexes. Then at every
object `K` the cocone `coconeOfUnit` computes the right derived value of `H`, with vertex
`RF (Qh K)` and coprojections induced by `β`. -/
private theorem exists_isRightDerivedValueAt_of_isIso_app_isKInjective
    {C E : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Category E]
    (H : HomotopyCategory C (ComplexShape.up ℤ) ⥤ E) (RF : DerivedCategory C ⥤ E)
    (β : H ⟶ DerivedCategory.Qh ⋙ RF)
    (hK : ∀ K : CochainComplex C ℤ, ∃ (J : CochainComplex C ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (hβ : ∀ J : CochainComplex C ℤ, J.IsKInjective →
      IsIso (β.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J)))
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    ∃ (c : Cocone (MorphismProperty.Under.forget
          (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ⊤ K ⋙ Under.forget K ⋙ H))
      (_ : H.IsRightDerivedValueAt (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) K c)
      (e : c.pt ≅ RF.obj (DerivedCategory.Qh.obj K)),
      ∀ s : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).Under ⊤ K,
        c.ι.app s ≫ e.hom ≫ RF.map (DerivedCategory.Qh.map s.hom) = β.app s.right := by
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  obtain ⟨Kc, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨J, q, hJ, hq⟩ := hK Kc
  let s₀ : W.Under ⊤ ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Kc) :=
    MorphismProperty.Under.mk ⊤ _ ((HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq)
  have : IsIso (β.app s₀.right) := hβ J hJ
  have : IsIso (DerivedCategory.Qh.map s₀.hom) :=
    Localization.inverts DerivedCategory.Qh W s₀.hom s₀.prop
  refine ⟨coconeOfUnit H W DerivedCategory.Qh (Localization.inverts DerivedCategory.Qh W) RF β _,
    ⟨s₀, RF.map (DerivedCategory.Qh.map s₀.hom) ≫ inv (β.app s₀.right), by simp [coconeOfUnit],
      fun s => exists_transition_factor_coconeOfUnit H RF β hK hβ s₀ s⟩,
    Iso.refl _, fun s => by simp [coconeOfUnit]⟩

/-- The derived functor of an exact functor `G`, compared with `G` on homotopy categories
through `Functor.mapDerivedCategoryFactorsh`, is a left derived value of `G` at every object:
the pro-object of the quasi-isomorphisms into `M` is essentially constant. -/
private theorem exists_isLeftDerivedValueAt_mapDerivedCategory
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (M : HomotopyCategory C (ComplexShape.up ℤ)) :
    ∃ (d : Cone (MorphismProperty.Over.forget
          (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ⊤ M ⋙
          Over.forget M ⋙ G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
      (_ : (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsLeftDerivedValueAt
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) M d)
      (e : G.mapDerivedCategory.obj (DerivedCategory.Qh.obj M) ≅ d.pt),
      ∀ t : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).Over ⊤ M,
        G.mapDerivedCategory.map (DerivedCategory.Qh.map t.hom) ≫ e.hom ≫ d.π.app t =
          G.mapDerivedCategoryFactorsh.hom.app t.left := by
  let W' := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := D)
  let Q' := DerivedCategory.Qh (C := C)
  let Gh := G.mapHomotopyCategory (ComplexShape.up ℤ)
  let LG := G.mapDerivedCategory
  let α : Q' ⋙ LG ⟶ Gh ⋙ Q := G.mapDerivedCategoryFactorsh.hom
  have hG : W'.IsInvertedBy (Gh ⋙ Q) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso W' G.mapDerivedCategoryFactorsh).1
      (MorphismProperty.IsInvertedBy.of_comp W' Q' (Localization.inverts Q' W') LG)
  let d : Cone (MorphismProperty.Over.forget W' ⊤ M ⋙ Over.forget M ⋙ Gh ⋙ Q) := {
    pt := Q.obj (Gh.obj M)
    π := {
      app := fun t => by
        have : IsIso ((Gh ⋙ Q).map t.hom) := hG t.hom t.prop
        exact (asIso ((Gh ⋙ Q).map t.hom)).inv
      naturality := by
        intro t t' f
        dsimp
        have : IsIso ((Gh ⋙ Q).map t.hom) := hG t.hom t.prop
        have : IsIso ((Gh ⋙ Q).map t'.hom) := hG t'.hom t'.prop
        have hcalc : (asIso ((Gh ⋙ Q).map t.hom)).inv ≫ (Gh ⋙ Q).map f.left =
            (asIso ((Gh ⋙ Q).map t'.hom)).inv := by
          rw [asIso_inv, asIso_inv, IsIso.inv_comp_eq, IsIso.eq_comp_inv]
          simp only [← Functor.map_comp, MorphismProperty.Over.w f]
        rw [Category.id_comp]
        exact hcalc.symm } }
  refine ⟨d, ⟨MorphismProperty.Over.mk ⊤ (𝟙 M) (W'.id_mem M), 𝟙 _, ?_, fun s => ?_⟩,
    asIso (α.app M), fun t => ?_⟩
  · dsimp [d, MorphismProperty.Over.mk]
    have : IsIso (Q.map (Gh.map (𝟙 M))) := hG (𝟙 M) (W'.id_mem M)
    simp
  · cases s.right
    refine ⟨s, MorphismProperty.Over.homMk (𝟙 s.left) (by simp),
      MorphismProperty.Over.homMk s.hom (Category.comp_id _), ?_⟩
    dsimp [d, MorphismProperty.Over.homMk, MorphismProperty.Over.mk,
      CategoryTheory.Over.homMk]
    have : IsIso (Q.map (Gh.map s.hom)) := hG s.hom s.prop
    simp only [map_id, Category.id_comp, IsIso.eq_comp_inv]
    rfl
  · dsimp [d]
    have : IsIso ((Gh ⋙ Q).map t.hom) := hG t.hom t.prop
    have hnat : LG.map (Q'.map t.hom) ≫ α.app M =
        α.app t.left ≫ (Gh ⋙ Q).map t.hom := α.naturality t.hom
    calc
      LG.map (Q'.map t.hom) ≫ α.app M ≫ (asIso ((Gh ⋙ Q).map t.hom)).inv =
          (α.app t.left ≫ (Gh ⋙ Q).map t.hom) ≫ (asIso ((Gh ⋙ Q).map t.hom)).inv := by
        rw [← Category.assoc, hnat]
      _ = α.app t.left := by simp

/-- **Stacks 0A6L.** Local cohomology `RΓ_I`, as the named total right derived functor of
the `I`-power-torsion-submodule functor, is right adjoint to the derived inclusion of the
category of `I`-power-torsion modules into `D(A)`. Its counit is induced by the underived
torsion-submodule inclusion, compatibly with the total right derived unit. -/
@[stacks 0A6L]
theorem derivedInclusion_adj_derivedPowerTorsion
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
    letI : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
    letI : PreservesFiniteLimits P.ι :=
      ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
    letI : PreservesFiniteColimits P.ι :=
      ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
    ∃ adj : P.ι.mapDerivedCategory ⊣ derivedPowerTorsion.{u, v} A I hI,
      IsCanonicalDerivedPowerTorsionCounit.{u, v} A I hI adj.counit := by
  let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
  let : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
  let : PreservesFiniteLimits P.ι :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
  let : PreservesFiniteColimits P.ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
  let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)
  let W' := HomotopyCategory.quasiIso P.FullSubcategory (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := ModuleCat.{max u v} A)
  let Q' := DerivedCategory.Qh (C := P.FullSubcategory)
  let H := (powerTorsionFunctor.{u, v} A I).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Q'
  have hK : ∀ K : CochainComplex (ModuleCat.{max u v} A) ℤ,
      ∃ (J : CochainComplex (ModuleCat.{max u v} A) ℤ) (q : K ⟶ J),
        J.IsKInjective ∧ QuasiIso q := fun K =>
    (CochainComplex.exists_quasiIso_isKInjective K).imp fun _ ⟨q, hq, hJ⟩ => ⟨q, hJ, hq⟩
  have hDerived :=
    H.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective hK
  have : H.HasPointwiseRightDerivedFunctor W := hDerived.1
  let RF := H.totalRightDerived Q W
  let β : H ⟶ Q ⋙ RF := H.totalRightDerivedUnit Q W
  let adjh := mapHomotopyCategoryAdjunction (powerTorsionAdjunction.{u, v} A I)
    (ComplexShape.up ℤ)
  obtain ⟨adjDerived, _, hCounit⟩ :=
    Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt
      adjh W W' Q Q' RF β P.ι.mapDerivedCategory P.ι.mapDerivedCategoryFactorsh.hom
      (exists_isRightDerivedValueAt_of_isIso_app_isKInjective H RF β hK
        (hDerived.2 Q RF β))
      (exists_isLeftDerivedValueAt_mapDerivedCategory P.ι)
  have hc : adjh.counit = powerTorsionHomotopyInclusion.{u, v} A I := by
    ext K
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    apply (HomotopyCategory.quotient _ _).congr_map
    ext n x
    rfl
  exact ⟨adjDerived, fun K => by simpa only [hc, derivedPowerTorsionUnit] using hCounit K⟩

end LocalCohomology

end Dualizing
