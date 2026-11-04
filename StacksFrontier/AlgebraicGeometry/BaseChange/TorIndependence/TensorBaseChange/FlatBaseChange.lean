module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.FlatModel
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.DerivedTensor
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.StalkComplexCriterion
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingBridge

/-!
# The map of Stacks 0DJ7 at the derived pullback, for a flat base change

For a cartesian square of schemes with `g : S' ⟶ S` flat, the map of Stacks 0DJ7 at
`(M, L(g')^*M, id)` is an isomorphism at every point of `X'` and in every degree, for every
`M ∈ D(𝒪_X)`: on stalks it is
`H^n(M_x ⊗^L_{𝒪_{S,s}} 𝒪_{S',s'}) ⊗ 𝒪_{X',x'} ⟶ H^n(M_x ⊗^L 𝒪_{X',x'})`, and `𝒪_{X',x'}` is a
localization of `𝒪_{X,x} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}`.

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_id_of_flat`
* `AlgebraicGeometry.isIso_of_isIso_baseChangeCohomologyMap_of_flat`: for `g` flat, condition (1)
  of Stacks 0DJ8 for `(K, K', φ)` says exactly that `φ` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
open RingTheory.TorIndependence

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedPullbackTensor Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- For `g` flat, the ring map `𝒪_{S,s} ⟶ 𝒪_{S',s'}` of Stacks 0DJ7 is flat. -/
theorem flat_baseStalkMap (w : g' ≫ f = f' ≫ g) [Flat g] (x' : X') :
    (baseStalkMap f g f' g' w x').Flat :=
  RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso
      (S.presheaf.stalkCongr (.of_eq (congrArg (fun h : X' ⟶ S ↦ h x') w))).hom))
    (Flat.stalkMap g (f' x'))

private theorem id_chase {C : Type*} [Category C] {X Y Z : C} (m : X ⟶ Y) (p : X ⟶ Z)
    (hp : IsIso p) (i : Z ⟶ Z) (hi : i = 𝟙 Z) : m ≫ 𝟙 Y = (p ≫ i) ≫ @inv _ _ _ _ p hp ≫ m := by
  subst hi
  simp

/-- **Flat base change for the map of Stacks 0DJ7.**  For a cartesian square of schemes with
`g` flat, the map of Stacks 0DJ7 at `(M, L(g')^*M, id)` is an isomorphism at every point of `X'`
and in every degree. -/
theorem isIso_baseChangeCohomologyMap_id_of_flat (hpb : IsPullback g' f' f g) [Flat g]
    (M : DerivedCategory X.Modules) (x' : X') (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' hpb.w M ((derivedPullback g'.toLRSHom.toShHom).obj M)
      (𝟙 _) x' n) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_kFlat_iso M
  have hpc : IsIso (pullbackComparisonOnComplex g' N) :=
    isIso_derivedPullbackNatTrans_app g'.toLRSHom.toShHom N hN
  have key : IsIso (baseChangeCohomologyMap f g f' g' hpb.w (DerivedCategory.Q.obj N)
      (DerivedCategory.Q.obj (((Scheme.Modules.pullback g').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N))
      (pullbackComparisonOnComplex g' N ≫ DerivedCategory.Q.map (𝟙 _)) x' n) := by
    let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
      ((f.stalkMap (g' x')).hom).toAlgebra
    let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
      (baseStalkMap f g f' g' hpb.w x').toAlgebra
    let : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
      (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
    let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
      ((g'.stalkMap x').hom).toAlgebra
    let : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
      ((f'.stalkMap x').hom).toAlgebra
    let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
        (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
        (X'.presheaf.stalk x') :=
      IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' hpb.w x')
    have : Module.Flat (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
      flat_baseStalkMap hpb.w x'
    obtain ⟨T, hT⟩ := exists_isLocalization_stalk hpb x'
    have : IsIso ((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso g' x')
        (ComplexShape.up ℤ)).hom.app N ≫
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X' x').mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (𝟙 (((Scheme.Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj N))) :=
      IsIso.comp_isIso' (Iso.isIso_hom ((NatIso.mapHomologicalComplex
        (Stacks.ModuleSkyscraper.pullbackStalkIso g' x') (ComplexShape.up ℤ)).app N))
        (Functor.map_isIso _ _)
    exact (isIso_baseChangeCohomologyMap_complex_iff f g f' g' hpb.w N _ (𝟙 _) x' n).2
      (isIso_ringBaseChangeCohomologyMap_of_flat T hT _ _ _ n)
  let τ := @inv _ _ _ _ (pullbackComparisonOnComplex g' N) hpc ≫
    ((derivedPullback g'.toLRSHom.toShHom).mapIso e).hom
  have h1 := (isIso_baseChangeCohomologyMap_iff_of_isIso_target f g f' g' hpb.w _ _ _ _ τ
    (IsIso.comp_isIso' (@IsIso.inv_isIso _ _ _ _ _ hpc) (Iso.isIso_hom _)) x' n).2 key
  have heq : (derivedPullback g'.toLRSHom.toShHom).map e.hom ≫ 𝟙 _ =
      (pullbackComparisonOnComplex g' N ≫ DerivedCategory.Q.map (𝟙 _)) ≫ τ :=
    id_chase _ _ hpc _ (CategoryTheory.Functor.map_id _ _)
  have h2 := isIso_baseChangeCohomologyMap_of_eq hpb.w _ _ _ _ heq x' n h1
  exact (isIso_baseChangeCohomologyMap_iff_of_isIso_source f g f' g' hpb.w _ _ _ e.hom
    (Iso.isIso_hom e) (𝟙 _) x' n).1 h2

/-- **For a flat base change, condition (1) of Stacks 0DJ8 forces `φ` to be an isomorphism.**
For a cartesian square of schemes with `g` flat, if the map of Stacks 0DJ7 at `(K, K', φ)` is an
isomorphism at every point of `X'` and in every degree, then `φ : L(g')^*K ⟶ K'` is an
isomorphism. -/
theorem isIso_of_isIso_baseChangeCohomologyMap_of_flat (hpb : IsPullback g' f' f g) [Flat g]
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' hpb.w K K' φ x' n)) :
    IsIso φ := by
  have hst : ∀ x' : X', IsIso ((derivedStalkFunctor x').map φ) := fun x' => by
    refine (DerivedCategory.isIso_iff _ _).2 fun n => ?_
    have h1 := isIso_baseChangeCohomologyMap_of_eq hpb.w K K' (𝟙 _ ≫ φ) φ (Category.id_comp φ) x'
      n (h x' n)
    have h2 := baseChangeCohomologyMap_comp f g f' g' hpb.w K _ K' (𝟙 _) φ x' n
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
      (isIso_baseChangeCohomologyMap_id_of_flat hpb K x' n) (h2 ▸ h1)
  exact (Stacks.Cohomology.StalkwiseIso.isIso_iff_forall_derivedStalk_isIso
    X'.ringCatSheaf φ).2 fun x' => (isIso_derivedStalkFunctor_map_iff x' φ).1 (hst x')

end AlgebraicGeometry
