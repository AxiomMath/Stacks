module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.CompositeChartData
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompactQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.StrictlyPerfectTensorBound
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackSingleUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceShiftedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactnessGeneral

/-!
# A uniform lower bound for `(E ⊗^L 𝒢^•) ⊗^L Lf^*ℱ`

Let `f : X ⟶ Y` be a morphism of algebraic spaces with `X` quasi-compact, `E` a perfect object of
`D(𝒪_X)` and `𝒢^•` a bounded complex of `𝒪_X`-modules flat over `Y`. Then there is an integer
`m` with `(E ⊗^L 𝒢^•) ⊗^L Lf^*ℱ ∈ D^{≥ m}` for every `𝒪_Y`-module `ℱ`.

`X` has a surjective étale chart `w : W ⟶ X` with `W` an affine scheme. Vanishing of a module is
detected after `w^*`, and `w^*` commutes with the derived tensor products and pullbacks. On the
affine `W` the perfect object `Lw^*E` has a strictly perfect model, vanishing below some `c`,
and `(P ⊗^L w^*𝒢^•) ⊗^L L(f ∘ w)^*ℱ ∈ D^{≥ c + a}`.

## Main results

* `AlgebraicGeometry.Space.exists_isGE_smallEtaleDerivedTensor_tensor_pullback`
* `AlgebraicGeometry.Space.exists_isLE_smallEtaleDerivedTensor_of_isPerfect`: `E ⊗^L 𝒢^•` is
  bounded above for `𝒢^•` bounded above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **A uniform lower bound for `(E ⊗^L 𝒢^•) ⊗^L Lf^*ℱ`** with `X` quasi-compact, `E` perfect
and `𝒢^•` a bounded complex of modules flat over `Y` vanishing below `a`. -/
theorem exists_isGE_smallEtaleDerivedTensor_tensor_pullback (f : X ⟶ Y)
    (hX : IsQuasiCompactSpace B S hS X.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (a : ℤ) (hGa : ∀ i, i < a → IsZero (G.X i))
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x) :
    ∃ m : ℤ, ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      (((smallEtaleDerivedTensor B S hS X).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))).obj
          ((smallEtaleDerivedModulePullback B S hS f).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))).IsGE m := by
  obtain ⟨U, φ, hUa, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUa
  let w : schemeSpace U ⟶ X := ObjectProperty.homMk φ
  have hw : IsEtale B S hS w.hom := het
  have := faithful_modulePullback B S hS U w hw hsurj
  -- a strictly perfect model of `Lw^*E`
  have hEW := isPerfect_smallEtaleDerivedModulePullback w E hE
  obtain ⟨P, hP, ⟨c, d, hc, hd⟩, ⟨eP⟩⟩ := hasStrictlyPerfectModel_of_isCompactObject_yoneda U
    ⟨_, qcohDerived_of_isPerfect_derivedCategoryB (schemeSpace U) _ hEW⟩
    (isCompactObject_of_isPerfect_yoneda U _ hEW)
  have hPb : {i : ℤ | ¬ IsZero (P.X i)}.Finite :=
    (Set.finite_Icc c d).subset fun i hi => ⟨not_lt.1 fun h => hi (P.isZero_of_isStrictlyGE c i h),
      not_lt.1 fun h => hi (P.isZero_of_isStrictlyLE d i h)⟩
  let G' := ((modulePullback B S hS w).mapHomologicalComplex (ComplexShape.up ℤ)).obj G
  have hG'b : {i : ℤ | ¬ IsZero (G'.X i)}.Finite :=
    hGb.subset fun i hi h => hi ((modulePullback B S hS w).map_isZero h)
  have hG'a : ∀ i, i < a → IsZero (G'.X i) := fun i hi =>
    (modulePullback B S hS w).map_isZero (hGa i hi)
  have hG' : ∀ n x, IsFlatOverAtGeometricPoint B S hS (w ≫ f) (G'.X n) x := fun n x =>
    (isFlatOverAtGeometricPoint_modulePullback_iff_of_isFlatAt B S hS w f (G.X n) x
      (isFlatAt_of_isFlat B S hS _ (isFlat_of_isEtale B S hS hw) x.image)).1 (hG n _)
  refine ⟨c + a, fun F => ?_⟩
  let L' := (smallEtaleDerivedModulePullback B S hS (w ≫ f)).obj
    ((DerivedCategory.singleFunctor _ 0).obj F)
  have hW := isGE_smallEtaleDerivedTensor_tensor_of_strictlyPerfect P hP hPb c
    (fun i hi => P.isZero_of_isStrictlyGE c i hi) (DerivedCategory.Q.obj G') L' a
    (isGE_smallEtaleDerivedTensor_pullback_of_isFlatOver (w ≫ f) G' hG'b a hG'a hG' F)
  let M := ((smallEtaleDerivedTensor B S hS X).obj
    (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))).obj
      ((smallEtaleDerivedModulePullback B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F))
  let e₁ : (smallEtaleDerivedModulePullback B S hS w).obj
      (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)) ≅
      ((smallEtaleDerivedTensor B S hS (schemeSpace U)).obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj G') :=
    (smallEtaleDerivedPullbackTensorIso w).app (E, DerivedCategory.Q.obj G) ≪≫
      ((smallEtaleDerivedTensor B S hS (schemeSpace U)).mapIso eP).app _ ≪≫
      ((smallEtaleDerivedTensor B S hS (schemeSpace U)).obj _).mapIso
        (smallEtaleDerivedModulePullbackObjQIsoOfIsEtale w hw G)
  let e : (smallEtaleDerivedModulePullback B S hS w).obj M ≅
      ((smallEtaleDerivedTensor B S hS (schemeSpace U)).obj
        (((smallEtaleDerivedTensor B S hS (schemeSpace U)).obj (DerivedCategory.Q.obj P)).obj
          (DerivedCategory.Q.obj G'))).obj L' :=
    (smallEtaleDerivedPullbackTensorIso w).app (_, _) ≪≫
      ((smallEtaleDerivedTensor B S hS (schemeSpace U)).mapIso e₁).app _ ≪≫
      ((smallEtaleDerivedTensor B S hS (schemeSpace U)).obj _).mapIso
        ((smallEtaleDerivedModulePullbackCompIso B S hS w f).app _)
  rw [DerivedCategory.isGE_iff] at hW ⊢
  exact fun k hk => (IsZero.iff_id_eq_zero _).2 ((modulePullback B S hS w).map_injective
    ((((hW k hk).of_iso ((DerivedCategory.homologyFunctor _ k).mapIso e)).of_iso
      (smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale w hw M k).symm).eq_of_src _ _))

/-- **`E ⊗^L 𝒢^•` is bounded above** for `X` quasi-compact, `E` perfect and `𝒢^•` a complex
vanishing above `b`. -/
theorem exists_isLE_smallEtaleDerivedTensor_of_isPerfect (hX : IsQuasiCompactSpace B S hS X.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (b : ℤ) (hGb : ∀ i, b < i → IsZero (G.X i)) :
    ∃ m : ℤ, (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)).IsLE m := by
  obtain ⟨U, φ, hUa, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUa
  let w : schemeSpace U ⟶ X := ObjectProperty.homMk φ
  have hw : IsEtale B S hS w.hom := het
  have := faithful_modulePullback B S hS U w hw hsurj
  have hEW := isPerfect_smallEtaleDerivedModulePullback w E hE
  obtain ⟨P, hP, ⟨_, d, _, hd⟩, ⟨eP⟩⟩ := hasStrictlyPerfectModel_of_isCompactObject_yoneda U
    ⟨_, qcohDerived_of_isPerfect_derivedCategoryB (schemeSpace U) _ hEW⟩
    (isCompactObject_of_isPerfect_yoneda U _ hEW)
  let G' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (schemeSpace U))) ℤ :=
    ((modulePullback B S hS w).mapHomologicalComplex (ComplexShape.up ℤ)).obj G
  have : CochainComplex.IsStrictlyLE G' b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => (modulePullback B S hS w).map_isZero (hGb i hi)
  have hPd : (DerivedCategory.Q.obj P).IsLE d := by
    rw [DerivedCategory.isLE_Q_obj_iff]
    have := hd
    infer_instance
  have hG'd : (DerivedCategory.Q.obj G').IsLE b := by
    rw [DerivedCategory.isLE_Q_obj_iff]
    infer_instance
  have hW := Stacks.SheafOfModules.DerivedTensorProduct.isBoundedAboveBy_tensor_general
    (smallEtaleDerivedTensorProduct B S hS (schemeSpace U))
    ((Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE _ d).2 hPd)
    ((Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE _ b).2 hG'd)
  refine ⟨d + b, ?_⟩
  let M := ((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)
  let e : (smallEtaleDerivedModulePullback B S hS w).obj M ≅
      ((smallEtaleDerivedTensor B S hS (schemeSpace U)).obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj G') :=
    (smallEtaleDerivedPullbackTensorIso w).app (E, DerivedCategory.Q.obj G) ≪≫
      ((smallEtaleDerivedTensor B S hS (schemeSpace U)).mapIso eP).app _ ≪≫
      ((smallEtaleDerivedTensor B S hS (schemeSpace U)).obj _).mapIso
        (smallEtaleDerivedModulePullbackObjQIsoOfIsEtale w hw G)
  rw [DerivedCategory.isLE_iff]
  exact fun k hk => (IsZero.iff_id_eq_zero _).2 ((modulePullback B S hS w).map_injective
    ((((hW k hk).of_iso ((DerivedCategory.homologyFunctor _ k).mapIso e)).of_iso
      (smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale w hw M k).symm).eq_of_src _ _))

/-- **`E ⊗^L 𝒢^•` is bounded below** for `X` quasi-compact, `E` perfect and `𝒢^•` a bounded
complex of modules flat over `Y`: it is `(E ⊗^L 𝒢^•) ⊗^L Lf^*𝒪_Y`. -/
theorem exists_isGE_smallEtaleDerivedTensor_of_isFlatOver (f : X ⟶ Y)
    (hX : IsQuasiCompactSpace B S hS X.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (a : ℤ) (hGa : ∀ i, i < a → IsZero (G.X i))
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x) :
    ∃ m : ℤ, (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)).IsGE m := by
  obtain ⟨m, hm⟩ := exists_isGE_smallEtaleDerivedTensor_tensor_pullback f hX E hE G hGb a hGa hG
  refine ⟨m, ?_⟩
  let M := ((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)
  let OY := SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)
  let e₁ : (smallEtaleDerivedModulePullback B S hS f).obj
      ((DerivedCategory.singleFunctor _ 0).obj OY) ≅
      DerivedCategory.Q.obj (Stacks.SheafOfModules.singleUnitComplex
        (smallEtaleRingedTopos B S hS X).O 0) :=
    (smallEtaleDerivedModulePullback B S hS f).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app OY) ≪≫
      Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackSingleUnitIso
        (smallEtaleRingedToposHom B S hS f) 0
  let e : ((smallEtaleDerivedTensor B S hS X).obj M).obj
      ((smallEtaleDerivedModulePullback B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj OY)) ≅
      M :=
    ((smallEtaleDerivedTensor B S hS X).obj M).mapIso e₁ ≪≫
      ((smallEtaleDerivedTensorProduct B S hS X).rightSingleUnitNatIso 0).app M ≪≫
      (shiftFunctorZero' _ (-0 : ℤ) (by simp)).app M
  have h := hm OY
  rw [DerivedCategory.isGE_iff] at h ⊢
  exact fun k hk => (h k hk).of_iso ((DerivedCategory.homologyFunctor _ k).mapIso e.symm)

end AlgebraicGeometry.Space

end
