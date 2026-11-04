module

public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts
public import StacksFrontier.Homology.Perfect.CompactObjectAnyModel
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
public import StacksFrontier.RingTheory.Dualizing.DerivedHomAnyModel
import all StacksFrontier.Homology.Perfect.Characterizing

/-!
# Derived Hom along a ring map preserves direct sums, in a module universe above the rings

For a homomorphism of commutative rings `f : R →+* A` whose target is perfect as a module over
its source, the functor `RHom_R(A, -) : D(R) ⥤ D(A)` preserves direct sums indexed by types of
the module universe. Both derived categories are at *arbitrary* chosen models with independent
morphism universes, and the modules live in a universe `max v u` above the universe `u` of the
two rings.

The coproduct criterion used is
`CategoryTheory.Pretriangulated.preservesColimitsOfShape_discrete_of_isCompactObject_map`, whose
index universe is free of both morphism universes, so its hypotheses can be met at every model,
including the standard one.

The two generators change with the module universe: in `Mod_{max v u}(A)` the compact projective
separator is `ULift.{v} A`, not `A`, and the perfectness hypothesis has to be read for
`ULift.{v} A` over `R` rather than for `A`. Raising it is the content of `isPerfect_uliftFunctor`:
perfectness is preserved by `ModuleCat.uliftFunctor`, because that functor is exact and carries
a bounded complex of finite projective modules to one of the same kind.

## Main results

* `StacksDraft.Perfect.isPerfect_uliftFunctor` — perfectness is preserved by raising the module
  universe along `ModuleCat.uliftFunctor`.
* `StacksDraft.Perfect.isPerfectModule_ulift` — a perfect module stays perfect after `ULift`.
* `StacksDraft.Perfect.isCompactObject_uliftRegularModule`,
  `StacksDraft.Perfect.isSeparator_uliftRegularModule` — `ULift.{v} A` is a compact separator of
  `Mod_{max v u}(A)`.
* `StacksDraft.Perfect.isWeakTriangulatedGenerator_uliftRegularModule` — it is a weak generator
  of `D(Mod_{max v u}(A))`, at every chosen model.
* `StacksDraft.CompactDevissage.preservesColimitsOfShape_discrete_derivedHom_largeUniverse` —
  `RHom_R(A, -)` preserves direct sums, at arbitrary models and in the large module universe.
* `StacksDraft.CompactDevissage.preservesColimitsOfShape_discrete_derivedHom_standard` — the same
  for `Dualizing.derivedHom`, i.e. at the standard model.

## References

* [The Stacks Project, Tag 07LT](https://stacks.math.columbia.edu/tag/07LT)
* [The Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [The Stacks Project, Tag 0BZD](https://stacks.math.columbia.edu/tag/0BZD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor CategoryTheory.ObjectProperty

universe u v w w' w₀ u'

namespace StacksDraft.Perfect

/-! ### Raising the module universe -/

/-- **Perfectness survives raising the module universe.** The image of a perfect complex `K`
under the functor induced by `ModuleCat.uliftFunctor` is perfect. -/
theorem isPerfect_uliftFunctor {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u'} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u' v} R)]
    {K : DerivedCategory (ModuleCat.{u'} R)} (hK : IsPerfect K) :
    IsPerfect ((ModuleCat.uliftFunctor.{v, u'} R).mapDerivedCategory.obj K) := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨ei⟩⟩ := hK
  set F := ModuleCat.uliftFunctor.{v, u'} R with hF
  have := ha
  have := hb
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, a, b, inferInstance, inferInstance,
    ?_, ?_, ⟨F.mapDerivedCategory.mapIso ei ≪≫ F.mapDerivedCategoryFactors.app P⟩⟩
  · intro i
    have := hf i
    exact Module.Finite.equiv (ULift.moduleEquiv (R := R) (M := P.X i)).symm
  · intro i
    have := hp i
    exact Module.Projective.of_equiv (ULift.moduleEquiv (R := R) (M := P.X i)).symm

/-- **A perfect module stays perfect after `ULift`.** -/
theorem isPerfectModule_ulift {R : Type u} [CommRing R] (M : Type u')
    [AddCommGroup M] [Module R M]
    [HasDerivedCategory.{w} (ModuleCat.{u'} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u' v} R)]
    (hM : IsPerfectModule (R := R) M) :
    IsPerfectModule (R := R) (ULift.{v} M) :=
  isPerfect_of_iso
    (((ModuleCat.uliftFunctor.{v, u'} R).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of R M)).symm
    (isPerfect_uliftFunctor.{u, v} hM)

/-! ### The compact projective separator of the large module category -/

/-- `ULift.{v} A` is a separator of `Mod_{max v u}(A)`. -/
theorem isSeparator_uliftRegularModule {A : Type u} [Ring A] :
    IsSeparator (ModuleCat.of A (ULift.{v} A)) := by
  intro X Y f g h
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff, ModuleCat.hom_comp,
    LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply, forall_eq'] at h
  ext x
  simpa using h (ModuleCat.ofHom
    ((LinearMap.toSpanSingleton A X x).comp ULift.moduleEquiv.toLinearMap)) (ULift.up 1)

/-- `ULift.{v} A` is a compact object of `Mod_{max v u}(A)`. -/
theorem isCompactObject_uliftRegularModule {A : Type u} [CommRing A] :
    IsCompactObject.{max v u} (ModuleCat.of A (ULift.{v} A)) := by
  rw [isCompactObject_iff_isCompactObject_obj
    (StacksDraft.TorAmplitude.scalarLift.{u, v} (R := A))]
  exact isCompactObject_regularModule

/-- Countable products are exact in `Mod_{max v u}(A)`. -/
private instance hasExactLimitsOfShape_discrete_nat_moduleCat {A : Type u} [CommRing A] :
    HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max v u} A) :=
  moduleCat_hasExactLimitsOfShape_discrete_nat.{u, v}

/-- `ULift.{v} A` placed in degree zero is a compact object of `D(Mod_{max v u}(A))`, at every
chosen model. -/
theorem isCompactObject_derived_single_ulift {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max v u} A)] :
    IsCompactObject.{max v u}
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (ULift.{v} A))) := by
  have : IsCompactObject.{max v u} (ModuleCat.of A (ULift.{v} A)) :=
    isCompactObject_uliftRegularModule.{u, v}
  exact isCompactObject_derived_single _ 0

/-- `ULift.{v} A` placed in degree zero is a weak generator of `D(Mod_{max v u}(A))`, at every
chosen model. -/
theorem isWeakTriangulatedGenerator_uliftRegularModule {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max v u} A)] :
    (ObjectProperty.singleton
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (ULift.{v} A)))).IsWeakTriangulatedGenerator :=
  isWeakTriangulatedGenerator_single_of_projective_separator _ isSeparator_uliftRegularModule.{u, v}

/-- `D(Mod_{max v u}(A))` has coproducts indexed by the module universe, at every chosen model. -/
theorem hasCoproducts_derivedCategory_moduleCat {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max v u} A)] :
    HasCoproducts.{max v u} (DerivedCategory (ModuleCat.{max v u} A)) := by
  exact fun J => hasCoproductsOfShape_derivedCategory J

end StacksDraft.Perfect

namespace StacksDraft.CompactDevissage

/-- **`RHom_R(A, -)` preserves direct sums when `A` is perfect as an `R`-module**, for arbitrary
chosen models of `D(R)` and `D(A)` with independent morphism universes, and for modules in a
universe `max v u` above the universe `u` of the two rings. In particular the standard model is
allowed. -/
theorem preservesColimitsOfShape_discrete_derivedHom_largeUniverse
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{w₀} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{max v u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max v u} A)]
    (hperfect : letI := f.toAlgebra; StacksDraft.Perfect.IsPerfectModule (R := R) A)
    (J : Type (max v u)) :
    PreservesColimitsOfShape (Discrete J)
      (Dualizing.AnyModel.derivedHom.{u, v, u, w, w'} f) := by
  let := f.toAlgebra
  have : Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{max v u} f) :=
    ⟨fun _ _ _ => ⟨inferInstance⟩⟩
  have : Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{max v u} f) :=
    ⟨fun _ _ _ => ⟨inferInstance⟩⟩
  obtain ⟨adj⟩ := Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom.{u, v, u, w, w'} f
  have : (Dualizing.AnyModel.derivedHom.{u, v, u, w, w'} f).Additive :=
    adj.right_adjoint_additive
  have : HasCoproducts.{max v u} (DerivedCategory (ModuleCat.{max v u} A)) :=
    StacksDraft.Perfect.hasCoproducts_derivedCategory_moduleCat.{u, v}
  have : HasCoproducts.{max v u} (DerivedCategory (ModuleCat.{max v u} R)) :=
    StacksDraft.Perfect.hasCoproducts_derivedCategory_moduleCat.{u, v}
  set W : DerivedCategory (ModuleCat.{max v u} A) :=
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
      (ModuleCat.of A (ULift.{v} A)) with hW
  have hLW0 : (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.obj W ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
        ((ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of A (ULift.{v} A))) :=
    ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of A (ULift.{v} A))
  have hperfectUlift : StacksDraft.Perfect.IsPerfectModule (R := R) (ULift.{v} A) :=
    StacksDraft.Perfect.isPerfectModule_ulift.{u, v} A hperfect
  have hLWc : IsCompactObject.{max v u}
      ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.obj W) :=
    isCompactObject_of_iso hLW0
      ((StacksDraft.Perfect.AnyModel.isPerfect_iff_isCompactObject_max.{u, v} _).mp hperfectUlift)
  exact Pretriangulated.preservesColimitsOfShape_discrete_of_isCompactObject_map adj W
    StacksDraft.Perfect.isWeakTriangulatedGenerator_uliftRegularModule.{u, v}
    StacksDraft.Perfect.isCompactObject_derived_single_ulift.{u, v} hLWc J

/-- **`Dualizing.derivedHom` preserves direct sums when `A` is perfect as an `R`-module.** This is
the standard-model form of `preservesColimitsOfShape_discrete_derivedHom_largeUniverse`. -/
theorem preservesColimitsOfShape_discrete_derivedHom_standard
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (hperfect : letI := HasDerivedCategory.standard (ModuleCat.{u} R)
      letI := f.toAlgebra; StacksDraft.Perfect.IsPerfectModule (R := R) A)
    (J : Type (max v u)) :
    letI := HasDerivedCategory.standard (ModuleCat.{max v u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{max v u} A)
    PreservesColimitsOfShape (Discrete J) (Dualizing.derivedHom.{u, v, u} f) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{max v u} R)
  let := HasDerivedCategory.standard (ModuleCat.{max v u} A)
  rw [← Dualizing.AnyModel.derivedHom_eq_standard.{u, v, u} f]
  exact preservesColimitsOfShape_discrete_derivedHom_largeUniverse.{u, v} f hperfect J

end StacksDraft.CompactDevissage

end
