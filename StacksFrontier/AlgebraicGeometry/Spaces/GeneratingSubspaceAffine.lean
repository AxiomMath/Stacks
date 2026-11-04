module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariantsTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineFromTwistedVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GeneratingSubspaceAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionMultiplication
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistStepMultiples
public import StacksFrontier.CategoryTheory.Functor.Iterate

/-!
# The generating subspace of a section of a power of an ample-like invertible module is affine

Let `X` be a Noetherian algebraic space over a scheme `S` and `𝓛` an invertible `𝒪_X`-module such
that every coherent `𝓕` has some `n ≥ 1` with `H¹(X, 𝓕 ⊗ 𝓛^{⊗ n}) = 0`.  Let `s` be a global
section of `𝓛^{⊗ d}`, `d ≥ 1`, and `U_s ⊆ X` the open subspace over which `s` generates
`𝓛^{⊗ d}`.  The claim in the proof of Stacks 0D2W is that `U_s` is affine.

Multiplication by `s` is a natural transformation `μ : 𝟭 ⟶ - ⊗ 𝓛^{⊗ d}`
(`AlgebraicGeometry.Space.sectionMulNatTrans`); its iterates `μ^a : 𝓕 ⟶ 𝓕 ⊗ 𝓛^{⊗ ad}` become
invertible on `U_s`, and every coherent `𝓕` has some `a` with `H¹(X, 𝓕 ⊗ 𝓛^{⊗ ad}) = 0`
(`AlgebraicGeometry.Space.exists_isZero_obj_twistStep_mul`).  The inclusion `U_s ⟶ X` is affine
(`AlgebraicGeometry.Space.isAffineHom_ι_generatingSubspace`), so
`AlgebraicGeometry.Space.isAffineSpace_of_isAffineHom_of_twist` shows that `U_s` is affine.

## Main definitions

* `AlgebraicGeometry.Space.sectionMulNatTrans`: multiplication by a global section of `𝓜`, as a
  natural transformation `𝟭 ⟶ - ⊗ 𝓜`.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_generatingSubspace`: the generating subspace of a
  section of `𝓛^{⊗ d}` is affine.

## References

* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Multiplication by a global section `s` of `𝓜`, as a natural transformation from the identity
to tensoring on the right by `𝓜`. -/
noncomputable def sectionMulNatTrans (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (s : M.sections) :
    𝟭 _ ⟶ (Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS X.1 X.2).O).flip.obj
      M where
  app F := sectionMul X F M s
  naturality _ _ a := sectionMul_naturality X a M s

/-- The component of `sectionMulNatTrans` at `F` is multiplication by `s` on `F`. -/
@[simp]
theorem sectionMulNatTrans_app (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (s : M.sections) (F : Modules.{u, u} B S hS X.1 X.2) :
    (sectionMulNatTrans X M s).app F = sectionMul X F M s := rfl

/-- Twisting by equal integers gives isomorphic modules. -/
private noncomputable def twistStepEqIso (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    {m n : ℤ} (h : m = n) (K : Modules.{u, u} B S hS X.1 X.2) :
    twistStep B S hS X.1 X.2 L m K ≅ twistStep B S hS X.1 X.2 L n K :=
  eqToIso (congrArg (fun n : ℤ => twistStep B S hS X.1 X.2 L n K) h)

/-- **The iterated twist by `𝓛^{⊗ d}` is the twist by `𝓛^{⊗ ad}`**, for `a ≥ 1`. -/
theorem nonempty_iterate_tensorRightFunctor_obj_iso_twistStep (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (d a : ℕ) (K : Modules.{u, u} B S hS X.1 X.2) :
    Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS X.1 X.2).O).flip.obj
      (invertibleTensorPower B S hS X.1 X.2 L d)).iterate (a + 1)).obj K ≅
        twistStep B S hS X.1 X.2 L (((a + 1) * d : ℕ) : ℤ) K) := by
  induction a with
  | zero =>
    exact ⟨twistStepEqIso X L (by simp) K⟩
  | succ a ih =>
    obtain ⟨e⟩ := ih
    have e' : (((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS X.1 X.2).O).flip.obj
          (invertibleTensorPower B S hS X.1 X.2 L d)).iterate (a + 1 + 1)).obj K ≅
        twistStep B S hS X.1 X.2 L d (twistStep B S hS X.1 X.2 L (((a + 1) * d : ℕ) : ℤ) K) :=
      ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).mapIso
        e).app (invertibleTensorPower B S hS X.1 X.2 L d)
    exact ⟨e' ≪≫
        twistStepAddIso X L d (((a + 1) * d : ℕ) : ℤ) K ≪≫
        twistStepEqIso X L (by push_cast; ring) K⟩

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard

/-- **The claim in the proof of Stacks 0D2W: the generating subspace of a section of `𝓛^{⊗ d}`
is affine**, for an invertible `𝓛` on a Noetherian algebraic space every coherent module of
which has a twist `𝓕 ⊗ 𝓛^{⊗ n}`, `n ≥ 1`, with vanishing `H¹`.  See the module docstring. -/
theorem isAffineSpace_generatingSubspace (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (h : have := enoughInjectives_modules B S hS X.1 X.2
      ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
        ∃ n : ℕ, 1 ≤ n ∧ IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj
            (twistStep B S hS X.1 X.2 L n F)))
    (d : ℕ) (hd : 0 < d) (s : (invertibleTensorPower B S hS X.1 X.2 L d).sections) :
    IsAffineSpace B S hS
      (generatingSubspace B S hS X.2 (invertibleTensorPower B S hS X.1 X.2 L d) s).toFunctor := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have hXN : Fact (HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  let M := invertibleTensorPower B S hS X.1 X.2 L d
  have hMinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property M :=
    @Stacks.SheafOfModules.Invertible.tensorPower_isInvertible.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ L hL d
  have hMft : SheafOfModules.IsFiniteTypeOnSite M :=
    have := isCoherentOnSite_of_isInvertible M hMinv
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS X M
  let G := generatingSubspace B S hS X.2 M s
  have hj : IsAffineHom B S hS G.ι := isAffineHom_ι_generatingSubspace B S hS X M hMinv hMft s
  have hGo : IsOpenSubspace B S hS G := isOpenSubspace_generatingSubspace B S hS M s hMft
  let U : AlgebraicSpaces B S hS := ⟨G.toFunctor, hGo.1⟩
  let j : U ⟶ X := ObjectProperty.homMk G.ι
  have hjet : IsEtale B S hS j.hom := isEtale_ι_of_isOpenSubspace hGo
  have hqc : IsQuasiCompactSpace B S hS U.1 :=
    isQuasiCompactSpace_of_isImmersion_of_isNoetherian B S hS hZ X.2 hGo.1 hN G.ι
      (isImmersion_of_isOpenImmersion B S hS hGo.2)
  have hqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hGo.1 hN.2.1
      (isQuasiSeparated_of_isAffineHom B S hS G.ι hGo.1 X.2 hj)
  have hMinv' : AlgebraicGeometry.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property M :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ M hMinv
  let T₁ := (Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS X.1 X.2).O).flip.obj
    M
  have hT₁ : T₁.IsEquivalence :=
    @Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible _ _
      (smallEtaleRingedSite B S hS X.1 X.2).J (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ M hMinv'
  have : ∀ a, (T₁.iterate a).IsEquivalence := fun a => Functor.isEquivalence_iterate T₁ a
  let μ₁ := sectionMulNatTrans X M s
  have hμ₁ : ∀ F, IsIso ((modulePullback B S hS j).map (μ₁.app F)) := fun F =>
    (NatIso.isIso_map_iff (modulePullbackIsoEtaleModulePullback B S hS j hjet) _).2
      (isIso_etaleModulePullback_map_sectionMul j hjet F M hMinv s
        (range_pointsMap_ι_generatingSubspace B S hS M s).le)
  refine @isAffineSpace_of_isAffineHom_of_twist B S hS hZ X U hN j hj hqc hqs T₁.iterate this
    (Functor.iterateNatTrans μ₁) (fun K hK => ?_) (fun a => ?_)
  · have hK' : IsCoherent B S hS X.1 X.2 (twistStep B S hS X.1 X.2 L d K) :=
      have := isCoherentOnSite_twistStep B S hS X.1 X.2 L d K hK.toIsCoherentOnSite
      isCoherent_of_isCoherentOnSite B S hS X.1 X.2 _
    obtain ⟨a, ha⟩ := exists_isZero_obj_twistStep_mul X L _ h d hd _ hK'
    obtain ⟨e⟩ := nonempty_iterate_tensorRightFunctor_obj_iso_twistStep X L d a K
    refine ⟨a + 1, (ha.of_iso (Functor.mapIso _ ?_))⟩
    exact e ≪≫ twistStepEqIso X L (by push_cast; ring) K ≪≫
      (twistStepAddIso X L (a * d) d K).symm
  · induction a with
    | zero => exact fun F => (congrArg IsIso ((modulePullback B S hS j).map_id _)).mpr (IsIso.id _)
    | succ a ih =>
      intro F
      have h₁ : IsIso ((modulePullback B S hS j).map
          ((Functor.iterateNatTrans μ₁ a).app F ≫ μ₁.app ((T₁.iterate a).obj F))) :=
        (congrArg IsIso ((modulePullback B S hS j).map_comp _ _)).mpr
          (@IsIso.comp_isIso _ _ _ _ _ _ _ (ih F) (hμ₁ _))
      exact (congrArg (fun f => IsIso ((modulePullback B S hS j).map f))
        (Functor.iterateNatTrans_app_succ μ₁ a F)).mpr h₁

end AlgebraicGeometry.Space

end
