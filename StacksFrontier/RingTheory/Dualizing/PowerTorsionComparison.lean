module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison.LocalCohomologyFunctor

/-!
# The comparison between `D(I^∞-torsion)` and `D_{I^∞-torsion}(A)`

Let `I` be a finitely generated ideal of a commutative ring `A`. The inclusion of the Serre
subcategory of `I`-power-torsion modules into all `A`-modules induces a comparison functor
`Dualizing.powerTorsionComparison` from the derived category of `I`-power-torsion modules to the
full subcategory `D_{I^∞-torsion}(A) ⊆ D(A)` of objects with `I`-power-torsion cohomology. For a
Noetherian ring this comparison is an equivalence; for a general ring it is not (Stacks Tag
0A6P).

This file contains the formal half of that statement, the half that holds over any ring: the
comparison is an equivalence as soon as the counit of the derived adjunction
`ι ⊣ RΓ_I` is an isomorphism on the objects with `I`-power-torsion cohomology. That reduction is
the "formal argument, which we omit" of the Stacks proof of Tag 0955. It rests on the fact that
the derived functor of an exact fully faithful functor is conservative, which is proved here
first.

## Main results

* `Dualizing.isIso_of_isIso_mapDerivedCategory_map` — an exact fully faithful functor is
  conservative on derived categories.
* `Dualizing.isEquivalence_powerTorsionComparison_of_isIso_counit` — if the counit of a derived
  adjunction `ι ⊣ RΓ_I` is invertible on `D_{I^∞-torsion}(A)`, the comparison functor is an
  equivalence. This is part (1) ⟹ part (2) of Stacks Tag 0955.
* `Dualizing.isIso_localCohomologyAdjunction_counit` — the counit `RΓ_Z(K) → K` of the
  adjunction of Stacks Tag 0A6R is an isomorphism for every `K` with `I`-power-torsion
  cohomology. This is the analogue for `RΓ_Z` of part (1) of Stacks Tag 0955, and unlike that
  statement it holds over any ring, because the inclusion of `D_{I^∞-torsion}(A)` is fully
  faithful by construction.

## References

* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 0A6N](https://stacks.math.columbia.edu/tag/0A6N)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

/-- An exact fully faithful functor is conservative on derived categories: a morphism of
`D(C)` whose image in `D(D)` is invertible is itself invertible. Indeed an exact functor
commutes with cohomology degree by degree, and a fully faithful functor reflects
isomorphisms. -/
lemma isIso_of_isIso_mapDerivedCategory_map {C D : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] {X Y : DerivedCategory C} (f : X ⟶ Y)
    (hf : IsIso (F.mapDerivedCategory.map f)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (F.map ((DerivedCategory.homologyFunctor C n).map f)) :=
    (NatIso.isIso_map_iff (mapDerivedCategoryHomologyIso F n) f).1
      (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor D n).map
        (F.mapDerivedCategory.map f))))
  exact isIso_of_fully_faithful F _

/-- Whether the counit of an adjunction is invertible at an object depends only on the pair of
adjoint functors, not on the chosen adjunction: two adjunctions between the same functors have
counits that differ by the automorphism of the right adjoint relating them. -/
lemma isIso_counit_app_iff_of_adjunctions {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj₁ adj₂ : F ⊣ G) (X : D) :
    IsIso (adj₁.counit.app X) ↔ IsIso (adj₂.counit.app X) := by
  rw [← Adjunction.rightAdjointUniq_hom_app_counit adj₁ adj₂ X]
  exact isIso_comp_left_iff _ _

/-- A morphism with an invertible right inverse is invertible. -/
private lemma isIso_of_comp_eq_id {C : Type*} [Category C] {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X)
    (hb : IsIso b) (h : a ≫ b = 𝟙 X) : IsIso a := by
  rw [IsIso.eq_inv_of_inv_hom_id h]
  infer_instance

section Comparison

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

/-- The derived functor of the inclusion of the `I`-power-torsion modules is conservative. -/
lemma isIso_of_isIso_derivedInclusion_map
    {X Y : DerivedCategory (PowerTorsionModule.{u, v} A I hI)} (f : X ⟶ Y)
    (hf : IsIso ((powerTorsionModuleProperty A I hI).ι.mapDerivedCategory.map f)) : IsIso f :=
  isIso_of_isIso_mapDerivedCategory_map (powerTorsionModuleProperty A I hI).ι f hf

/-- **Stacks 0955, part (1) implies part (2).** Let `RΓ_I` be right adjoint to the derived
inclusion of the `I`-power-torsion modules into `D(A)`. If the counit `RΓ_I(K) → K` of that
adjunction is an isomorphism for every `K` whose cohomology modules are `I`-power torsion, then
the comparison functor `D(I^∞-torsion) ⥤ D_{I^∞-torsion}(A)` is an equivalence.

This is the formal argument that the Stacks proof of Tag 0955 omits. The two ingredients are
that the derived inclusion is conservative, and that the inclusion of a full subcategory of
`D(A)` is fully faithful. -/
theorem isEquivalence_powerTorsionComparison_of_isIso_counit
    {derivedTorsion : DerivedCategory (ModuleCat.{v} A) ⥤
      DerivedCategory (PowerTorsionModule.{u, v} A I hI)}
    (adj : (powerTorsionModuleProperty A I hI).ι.mapDerivedCategory ⊣ derivedTorsion)
    (hcounit : ∀ K : PowerTorsionDerivedCategory.{u, v} A I hI,
      IsIso (adj.counit.app K.obj)) :
    (powerTorsionComparison.{u, v} A I hI).IsEquivalence := by
  have hunitapp (L) : IsIso (adj.unit.app L) :=
    isIso_of_isIso_derivedInclusion_map A I hI _ <| isIso_of_comp_eq_id _ _
      (hcounit ((powerTorsionComparison.{u, v} A I hI).obj L)) (adj.left_triangle_components L)
  have hunit : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  have := hff.full
  have := hff.faithful
  have : (powerTorsionComparison.{u, v} A I hI).Faithful :=
    Functor.Faithful.of_comp_iso (powerTorsionComparisonCompInclusionIso A I hI)
  have : (powerTorsionComparison.{u, v} A I hI).Full :=
    Functor.Full.of_comp_faithful_iso (powerTorsionComparisonCompInclusionIso A I hI)
  have hess : ∀ K : PowerTorsionDerivedCategory.{u, v} A I hI,
      Nonempty ((powerTorsionComparison.{u, v} A I hI).obj
        (derivedTorsion.obj K.obj) ≅ K) := by
    intro K
    have e : (derivedPowerTorsionProperty A I hI).ι.obj
        ((powerTorsionComparison.{u, v} A I hI).obj (derivedTorsion.obj K.obj)) ≅
        (derivedPowerTorsionProperty A I hI).ι.obj K :=
      @asIso _ _ _ _ (adj.counit.app K.obj) (hcounit K)
    exact ⟨(derivedPowerTorsionProperty A I hI).fullyFaithfulι.preimageIso e⟩
  have : (powerTorsionComparison.{u, v} A I hI).EssSurj :=
    ⟨fun K => ⟨derivedTorsion.obj K.obj, hess K⟩⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The counit `RΓ_Z(K) → K` of the adjunction of Stacks Tag 0A6R is an isomorphism whenever the
cohomology modules of `K` are `I`-power torsion. This holds over an arbitrary ring: the
inclusion of `D_{I^∞-torsion}(A)` into `D(A)` is fully faithful because it is the inclusion of a
full subcategory, so the counit of its right adjoint is invertible on the subcategory. -/
lemma isIso_localCohomologyAdjunction_counit
    (K : PowerTorsionDerivedCategory.{u, v} A I hI) :
    IsIso ((localCohomologyAdjunction A I hI).counit.app K.obj) :=
  inferInstanceAs
    (IsIso ((localCohomologyAdjunction A I hI).counit.app
      ((derivedPowerTorsionProperty A I hI).ι.obj K)))

end Comparison

end Dualizing
