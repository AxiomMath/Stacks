module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison

/-!
# Perfectness and compactness in a module universe above the ring

The perfect objects of `D(R)` are the compact ones ([Stacks, Tag 07LT]), here for `R`-modules in
a universe `max u v` above the universe `u` of `R`. Over such modules the localization
`Q : C(Mod R) ⥤ D(Mod R)` preserves coproducts indexed by any type in the universe `max u v`.

## Main results

* `StacksDraft.Perfect.isPerfect_of_iso`: perfectness is invariant under isomorphism.
* `StacksDraft.Perfect.isPerfect_restrictScalars_ringEquiv`: perfectness is invariant under
  restriction of scalars along a ring isomorphism.
* `StacksDraft.Perfect.isPerfect_iff_isCompactObject_max`: [Stacks, Tag 07LT] for modules in a
  universe above the universe of the ring.
* `StacksDraft.Perfect.moduleCat_hasExactLimitsOfShape_discrete_nat`: countable products are
  exact in `Mod_{max u v}(R)`.
* `StacksDraft.Perfect.preservesColimitsOfShape_discrete_Q_moduleCat`: `Q` preserves coproducts
  of every shape in the universe `max u v`.

## Implementation notes

Both perfectness and the exactness of countable products are transported along the equivalence
`StacksDraft.TorAmplitude.scalarLift : Mod_{max u v}(R) ≌ Mod_{max u v}(ULift.{v} R)`, restriction
of scalars along `ULift.ringEquiv`, whose target ring lives in the universe of its own modules.

## References

* [The Stacks Project, Tag 07LT](https://stacks.math.columbia.edu/tag/07LT)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.Perfect

/-- Perfectness is invariant under isomorphism in the derived category. -/
theorem isPerfect_of_iso {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    {K L : DerivedCategory (ModuleCat.{v} R)} (e : K ≅ L) (hL : IsPerfect L) : IsPerfect K := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨eP⟩⟩ := hL
  exact ⟨P, a, b, ha, hb, hf, hp, ⟨e ≪≫ eP⟩⟩

section

attribute [local instance] HasDerivedCategory.standard

/-- Perfectness is invariant under restriction of scalars along an isomorphism of rings. -/
theorem isPerfect_restrictScalars_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Small.{w} R] [Small.{w} S] (e : S ≃+* R)
    (K : DerivedCategory (ModuleCat.{w} R)) (hK : IsPerfect K) :
    IsPerfect ((ModuleCat.restrictScalars.{w} e.toRingHom).mapDerivedCategory.obj K) := by
  let F := ModuleCat.restrictScalars.{w} e.toRingHom
  have : F.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨ei⟩⟩ := hK
  have := ha
  have := hb
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, a, b, inferInstance, inferInstance,
    ?_, ?_, ⟨F.mapDerivedCategory.mapIso ei ≪≫ F.mapDerivedCategoryFactors.app P⟩⟩
  · intro i
    have := hf i
    let f : P.X i →ₛₗ[e.symm.toRingHom] F.obj (P.X i) :=
      { toFun := fun x => x
        map_add' := fun _ _ => rfl
        map_smul' := by intro r x; change r • x = e (e.symm r) • x; rw [e.apply_symm_apply] }
    exact Module.Finite.of_surjective f (fun x => ⟨x, rfl⟩)
  · intro i
    have : Module.Projective R (P.X i) := hp i
    have : Projective (F.obj (P.X i)) := inferInstance
    show Module.Projective S (F.obj (P.X i))
    exact ModuleCat.projective_of_module_projective _

/-- Countable products are exact in the category of `R`-modules in a universe above that of `R`.
-/
theorem moduleCat_hasExactLimitsOfShape_discrete_nat {R : Type u} [CommRing R] :
    HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} R) :=
  HasExactLimitsOfShape.domain_of_functor (Discrete ℕ)
    (StacksDraft.TorAmplitude.scalarLift.{u, v} (R := R))

attribute [local instance] moduleCat_hasExactLimitsOfShape_discrete_nat

/-- The localization `Q : C(Mod R) ⥤ D(Mod R)` preserves coproducts of every shape indexed in
the universe `max u v` of the modules. -/
theorem preservesColimitsOfShape_discrete_Q_moduleCat {R : Type u} [CommRing R]
    (ι : Type (max u v)) :
    PreservesColimitsOfShape (Discrete ι) (DerivedCategory.Q (C := ModuleCat.{max u v} R)) :=
  derivedCategory_Q_preservesCoproductsOfShape_of_enoughInjectives _ ι

/-- **[Stacks, Tag 07LT]** in a module universe above the universe of the ring: an object of the
derived category of `R`-modules is perfect if and only if it is compact. -/
theorem isPerfect_iff_isCompactObject_max {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) :
    IsPerfect K ↔ IsCompactObject.{max u v} K := by
  let F := StacksDraft.TorAmplitude.scalarLift.{u, v} (R := R)
  have he : IsCompactObject.{max u v} K ↔
      IsCompactObject.{max u v} (F.mapDerivedCategory.obj K) :=
    isCompactObject_iff_isCompactObject_obj F.mapDerivedCategory K
  have hp := isPerfect_iff_isCompactObject (F.mapDerivedCategory.obj K)
  refine ⟨fun h => he.mpr (hp.mp (isPerfect_restrictScalars_ringEquiv
    (ULift.ringEquiv : ULift.{v} R ≃+* R) K h)), fun h => ?_⟩
  let G := ModuleCat.restrictScalars.{max u v}
    (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom
  have hP : IsPerfect (G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K)) :=
    isPerfect_restrictScalars_ringEquiv (ULift.ringEquiv.symm : R ≃+* ULift.{v} R) _
      (hp.mpr (he.mp h))
  let P := DerivedCategory.Q.objPreimage K
  let ei := DerivedCategory.Q.objObjPreimageIso K
  let e₀ : F ⋙ G ≅ 𝟭 (ModuleCat.{max u v} R) :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{v} R ≃+* R)).unitIso.symm
  let eP := (Functor.mapHomologicalComplexCompIso e₀ (ComplexShape.up ℤ)).app P ≪≫
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).app P
  exact isPerfect_of_iso (ei.symm ≪≫ (DerivedCategory.Q.mapIso eP).symm ≪≫
    (G.mapDerivedCategoryFactors.app _).symm ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P).symm ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso ei)) hP

end

end StacksDraft.Perfect

end
