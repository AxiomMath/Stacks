module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorFlatPullbackBound
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso
public import StacksFrontier.AlgebraicGeometry.Spaces.TorAmplitudeQuasiCoherentDetection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactnessGeneral

/-!
# A lower bound for `Rf_*(E ⊗^L 𝒢^•) ⊗^L ℱ`

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces, `E` perfect
on `X` and `𝒢^•` a bounded complex of `𝒪_X`-modules flat over `Y`, with `E ⊗^L 𝒢^•` in
`D_QCoh(𝒪_X)`. Then there is an integer `m` such that `Rf_*(E ⊗^L 𝒢^•) ⊗^L ℱ ∈ D^{≥ m}` for every
quasi-coherent `𝒪_Y`-module `ℱ`. By the projection formula (Stacks 08IN) this object is
`Rf_*((E ⊗^L 𝒢^•) ⊗^L Lf^*ℱ)`, the inner object has no cohomology below a uniform bound, and
`Rf_*` is left t-exact.

## Main results

* `AlgebraicGeometry.Space.exists_isGE_smallEtaleDerivedTensor_pushforward_tensor`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **A uniform lower bound for `Rf_*(E ⊗^L 𝒢^•) ⊗^L ℱ`** over the quasi-coherent
`𝒪_Y`-modules `ℱ`, for `f` quasi-compact and quasi-separated, `X` quasi-compact, `E` perfect and
`𝒢^•` a bounded complex of modules flat over `Y`. -/
theorem exists_isGE_smallEtaleDerivedTensor_pushforward_tensor (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hX : IsQuasiCompactSpace B S hS X.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (a : ℤ) (hGa : ∀ i, i < a → IsZero (G.X i))
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    (hM : QcohDerived B S hS X
      (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) :
    ∃ m : ℤ, ∀ F : Modules.{u, u} B S hS Y.1 Y.2, F.IsQuasicoherentOnSite →
      (((smallEtaleDerivedTensor B S hS Y).obj ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)))).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)).IsGE m := by
  obtain ⟨m, hm⟩ := exists_isGE_smallEtaleDerivedTensor_tensor_pullback f hX E hE G hGb a hGa hG
  refine ⟨m, fun F hF => ?_⟩
  have hFq : QcohDerived B S hS Y ((DerivedCategory.singleFunctor _ 0).obj F) :=
    (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _) F hF).2
  have hiso := isIso_smallEtaleProjectionFormulaMap B S hS f hfqc hfqs _ hM _ hFq
  have hR := isGE_rightDerived_modulePushforward_obj B S hS f _
    (derivedModulePushforwardUnit B S hS f) _ m (hm F)
  rw [DerivedCategory.isGE_iff] at hR ⊢
  intro k hk
  exact (hR k hk).of_iso ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) k).mapIso
      (@asIso _ _ _ _ (smallEtaleProjectionFormulaMap B S hS f _
        ((DerivedCategory.singleFunctor _ 0).obj F)) hiso))

/-- **`Rf_*(E ⊗^L 𝒢^•)` has finite Tor amplitude** when `Y` is quasi-separated, `f` quasi-compact
and quasi-separated, `X` quasi-compact, `E` perfect, `𝒢^•` a bounded complex of modules flat over
`Y` with `E ⊗^L 𝒢^•` in `D_QCoh(𝒪_X)`, and `Rf_*(E ⊗^L 𝒢^•)` has no cohomology above `b`. -/
theorem exists_hasTorAmplitude_derivedModulePushforward_tensor (hZ : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hX : IsQuasiCompactSpace B S hS X.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (a : ℤ) (hGa : ∀ i, i < a → IsZero (G.X i))
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    (hM : QcohDerived B S hS X
      (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)))
    (b : ℤ) (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS Y.1 Y.2) i).obj ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))))) :
    ∃ m : ℤ, Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude
      (smallEtaleDerivedTensorProduct B S hS Y) ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) m b := by
  obtain ⟨m, hm⟩ := exists_isGE_smallEtaleDerivedTensor_pushforward_tensor f hfqc hfqs hX E hE G
    hGb a hGa hG hM
  have hK := qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs _ hM
  refine ⟨m, (hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent_standardModel
    hZ Y hYqs _ _ hK m b).2
    fun F hF i hi => ?_⟩
  have hi' : i < m ∨ b < i := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hi
    exact hi
  rcases hi' with h | h
  · exact (DerivedCategory.isGE_iff _ m).1 (hm F hF) i h
  · have hKb : ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))).IsLE b :=
      (DerivedCategory.isLE_iff _ b).2 hb
    have hF0 : ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F).IsLE 0 :=
      inferInstance
    have := Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor_general
      (smallEtaleDerivedTensorProduct B S hS Y) ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G)))
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F) b 0
    exact (DerivedCategory.isLE_iff _ (b + 0)).1 this i (by omega)

end AlgebraicGeometry.Space

end
