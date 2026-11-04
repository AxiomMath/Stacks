module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomChart
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomothety
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomothetySiteEquivalence

/-!
# The homothety map `𝒪_X ⟶ R𝓗om(K, K)` on an algebraic space

For an object `K` of `D(𝒪_X)` the homothety map `𝒪_X ⟶ R𝓗om(K, K)` is the morphism
corresponding to the unit constraint `𝒪_X ⊗^L K ≅ K` under the tensor–Hom adjunction of
Stacks 08J8.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedHomothety`: the map `𝒪_X ⟶ R𝓗om(K, K)` on an
  algebraic space.

## Main results

* `AlgebraicGeometry.Space.isIso_map_smallEtaleDerivedHomothety_chartToSpace_iff`: for an étale
  chart `φ : U ⟶ X`, `Lφ^*` of the homothety map of `K` is invertible exactly when the homothety
  map of `Lφ^* K` is.

## Implementation notes

The derived internal Hom of an algebraic space is that of the equi-universe model of its small
étale ringed site, read through the derived equivalence with the model
(`AlgebraicGeometry.Space.smallEtaleDerivedSheafHom`); the homothety map is defined in the same
way.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The total tensor complexes of sheaves of modules on a slice of the small étale model site
exist, read at the universes of the model site. -/
theorem hasMapBifunctor_sheafTensor_smallEtaleModelOver
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    (V : (smallEtaleModelRingedSite B S hS F hF).C)
    (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      ((smallEtaleModelRingedSite B S hS F hF).O.over V))) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((smallEtaleModelRingedSite B S hS F hF).O.over V)) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u, u, u, u, u} _ K₁ K₂

/-- **The homothety map** `𝒪_X ⟶ R𝓗om(K, K)` on an algebraic space: the homothety map of the
equi-universe model of the small étale ringed site, read through the derived equivalence with
the model. -/
def smallEtaleDerivedHomothety
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) ⟶
      ((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj K :=
  (smallEtaleModelDerivedEquivalence B S hS X).unitIso.hom.app _ ≫
    (smallEtaleModelDerivedEquivalence B S hS X).inverse.map
      (((smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategorySingleFunctor
          0).hom.app (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) ≫
        RingedSite.derivedHomothety (smallEtaleModelRingedSite B S hS X.1 X.2)
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj K))

/-- The homothety map of `K` is the unit of the derived equivalence with the model, followed by
the inverse equivalence applied to the comparison of the unit objects and the homothety map of the
model of `K`. -/
lemma smallEtaleDerivedHomothety_def
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    smallEtaleDerivedHomothety B S hS X K =
      (smallEtaleModelDerivedEquivalence B S hS X).unitIso.hom.app _ ≫
        (smallEtaleModelDerivedEquivalence B S hS X).inverse.map
          (((smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategorySingleFunctor
              0).hom.app (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) ≫
            RingedSite.derivedHomothety (smallEtaleModelRingedSite B S hS X.1 X.2)
              ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj K)) := rfl

section Generic

variable {C D E : Type*} [Category C] [Category D] [Category E] (e : C ≌ D)

omit hS in
/-- For an equivalence `e : C ≌ D`, isomorphisms `v : a ≅ e⁻¹ b` and `w : b ≅ c`, and a morphism
`h : c ⟶ d`, the composite `v ≫ e⁻¹ (w ≫ h)` is an isomorphism if and only if `h` is. -/
lemma isIso_comp_inverse_map_comp_iff {a : C} {b c d : D} (v : a ≅ e.inverse.obj b)
    (w : b ≅ c) (h : c ⟶ d) :
    IsIso (v.hom ≫ e.inverse.map (w.hom ≫ h)) ↔ IsIso h := by
  rw [isIso_comp_left_iff, isIso_iff_of_reflects_iso _ e.inverse, isIso_comp_left_iff]

omit hS in
/-- For an equivalence `e : C ≌ D`, a functor `G : D ⥤ E`, isomorphisms `v : a ≅ e⁻¹ b` and
`w : b ≅ c`, and a morphism `h : c ⟶ d`, the morphism `G (e (v ≫ e⁻¹ (w ≫ h)))` is an isomorphism
if and only if `G h` is. -/
lemma isIso_map_functor_map_comp_inverse_map_comp_iff (G : D ⥤ E) {a : C} {b c d : D}
    (v : a ≅ e.inverse.obj b) (w : b ≅ c) (h : c ⟶ d) :
    IsIso (G.map (e.functor.map (v.hom ≫ e.inverse.map (w.hom ≫ h)))) ↔ IsIso (G.map h) := by
  rw [Functor.map_comp, Functor.map_comp, isIso_comp_left_iff, e.fun_inv_map, Functor.map_comp,
    Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff, Functor.map_comp,
    isIso_comp_left_iff]

end Generic

/-- The homothety map of `K` is invertible exactly when the homothety map of the model of `K`
is. -/
theorem isIso_smallEtaleDerivedHomothety_iff
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    IsIso (smallEtaleDerivedHomothety B S hS X K) ↔
      IsIso (RingedSite.derivedHomothety (smallEtaleModelRingedSite B S hS X.1 X.2)
        ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj K)) :=
  isIso_comp_inverse_map_comp_iff _
    ((smallEtaleModelDerivedEquivalence B S hS X).unitIso.app _)
    (((smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategorySingleFunctor
      0).app _) _

/-- `G ∘ e_X` of the homothety map of `K` is invertible exactly when `G` of the homothety map of
the model of `K` is, for any functor `G` out of the derived category of the model. -/
theorem isIso_map_functor_map_smallEtaleDerivedHomothety_iff {D : Type*} [Category D]
    (G : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O)) ⥤ D)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    IsIso (G.map ((smallEtaleModelDerivedEquivalence B S hS X).functor.map
        (smallEtaleDerivedHomothety B S hS X K))) ↔
      IsIso (G.map (RingedSite.derivedHomothety (smallEtaleModelRingedSite B S hS X.1 X.2)
        ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj K))) :=
  isIso_map_functor_map_comp_inverse_map_comp_iff _ G
    ((smallEtaleModelDerivedEquivalence B S hS X).unitIso.app _)
    (((smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategorySingleFunctor
      0).app _) _

/-- **The homothety map and étale charts.** For an étale chart `φ : U ⟶ X` and `K` in
`D(𝒪_X)`, `Lφ^*` of the homothety map `𝒪_X ⟶ R𝓗om(K, K)` is invertible exactly when the
homothety map `𝒪_U ⟶ R𝓗om(Lφ^* K, Lφ^* K)` is. -/
theorem isIso_map_smallEtaleDerivedHomothety_chartToSpace_iff (A : SmallEtale B S hS X.1)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    IsIso ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X A)).map
        (smallEtaleDerivedHomothety B S hS X K)) ↔
      IsIso (smallEtaleDerivedHomothety B S hS (chartSpace B S hS X A)
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X A)).obj K)) := by
  let P := smallEtaleDerivedModulePullbackIsoEtale B S hS (chartToSpace B S hS X A)
    (isEtale_chartToSpace B S hS X A)
  let eU := smallEtaleModelDerivedEquivalence B S hS (chartSpace B S hS X A)
  let eX := smallEtaleModelDerivedEquivalence B S hS X
  let D := chartModelDerivedIso B S hS X A
  let T := (chartModelTransport B S hS X A).mapDerivedCategory
  let U : (smallEtaleModelRingedSite B S hS X.1 X.2).C :=
    (smallEtaleModelEquivalence B S hS X.1).inverse.obj A
  have : ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        ((smallEtaleModelRingedSite B S hS X.1 X.2).O.over U))) (ComplexShape.up ℤ)),
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((smallEtaleModelRingedSite B S hS X.1 X.2).O.over U)) (ComplexShape.up ℤ) :=
    fun K₁ K₂ => hasMapBifunctor_sheafTensor_smallEtaleModelOver B S hS U K₁ K₂
  exact (NatIso.isIso_map_iff P _).trans <|
    (isIso_iff_of_reflects_iso _ eU.functor).symm.trans <|
    (NatIso.isIso_map_iff D _).trans <|
    (isIso_map_functor_map_smallEtaleDerivedHomothety_iff B S hS X T K).trans <|
    (RingedSite.isIso_map_derivedHomothety_sliceEquivTransport_iff
      (X := smallEtaleModelRingedSite B S hS X.1 X.2)
      (Y := smallEtaleModelRingedSite B S hS (chartSpace B S hS X A).1 (chartSpace B S hS X A).2)
      U
      (chartModelSliceEquivalence B S hS X A) (chartModelSliceRingMap B S hS X A)
      (hl := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits _)
      (hc := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits _)
      (eX.functor.obj K)).trans <|
    (RingedSite.isIso_derivedHomothety_iff_of_iso _
      (eU.functor.mapIso (P.app K) ≪≫ D.app K).symm).trans <|
    (isIso_smallEtaleDerivedHomothety_iff B S hS (chartSpace B S hS X A) _).symm

end AlgebraicGeometry.Space

end
