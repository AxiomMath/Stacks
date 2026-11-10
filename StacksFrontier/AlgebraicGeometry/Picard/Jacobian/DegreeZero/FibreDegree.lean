module

public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZeroSubfunctor
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZero.FibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.DegreeIso

/-!
# The degree of a family of invertible modules on the fibres of a curve is locally constant

Let `X` be a proper flat scheme of finite presentation and of dimension at most one over a field
`k`, and let `ℒ` be an invertible module on a base change `X_T = X ×_k T`. For a point `t ∈ T` the
restriction of `ℒ` to the fibre `X_{κ(t)} = X ×_k κ(t)` has a degree `deg(ℒ_t)`
([Stacks, Tag 0AYR]). The function `t ↦ deg(ℒ_t)` on `T` is locally constant: it is
`χ(X_t, ℒ_t) - χ(X_t, 𝒪)`, and each of the two terms is locally constant by [Stacks, Tag 0B9T]
(`isLocallyConstant_fibreCoherentEulerCharacteristic_and_baseChange`).

This is the input of the proof of [Stacks, Tag 0BA0] that the degree-zero part `Pic⁰_{X/k}` of
the Picard functor is an open and closed subfunctor.

## Main definitions

* `Stacks.PicardFunctor.residueFibreDegree`: the degree `deg(ℒ_t)` of the restriction of a class of
  `Pic(X_T)` to the fibre over a point `t ∈ T`.

## Main results

* `Stacks.PicardFunctor.residueFibreDegree_picardClass_eq_fibreEulerCharacteristic_sub`:
  `deg(ℒ_t)` is `χ(X_t, ℒ_t) - χ(X_t, 𝒪_{X_t})`.
* `Stacks.PicardFunctor.isLocallyConstant_residueFibreDegree`: `t ↦ deg(ℒ_t)` is locally constant.

## References

* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {k : Type u} [Field k] {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)

/-- **The degree on the fibre over a point.** For a class `c ∈ Pic(X_T)` and a point `t` of the
test scheme `T`, the degree over `κ(t)` of the restriction of `c` to the fibre
`X_{κ(t)} = X ×_k κ(t)`. -/
def residueFibreDegree [IsProper (B.inclusion.map f)] (hdim : topologicalKrullDim X ≤ 1)
    (T : BigFppfOver B (Spec (.of k)) hk) (c : picardAt B hX hk f T)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) : ℤ :=
  Stacks.Picard.ofSchemeDegree
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)
    (pullback.snd (B.inclusion.map f) (B.inclusion.map (residueTest B hk T t).hom))
    (topologicalKrullDim_baseChange_residueTest B hX hk f hdim T t)
    (picardMap B hX hk f (residueTestι B hk T t) c)

/-- The restriction of a class to the fibre over `t` has degree zero exactly when the fibre degree
vanishes. -/
theorem picardMap_mem_fibreDegreeZero_iff [IsProper (B.inclusion.map f)]
    (hdim : topologicalKrullDim X ≤ 1) (T : BigFppfOver B (Spec (.of k)) hk)
    (c : picardAt B hX hk f T) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    picardMap B hX hk f (residueTestι B hk T t) c ∈ fibreDegreeZero B hX hk f hdim T t ↔
      residueFibreDegree B hX hk f hdim T c t = 0 :=
  AddMonoidHom.mem_ker

/-- The fibre degree is additive in the class. -/
theorem residueFibreDegree_add [IsProper (B.inclusion.map f)] (hdim : topologicalKrullDim X ≤ 1)
    (T : BigFppfOver B (Spec (.of k)) hk) (c d : picardAt B hX hk f T)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    residueFibreDegree B hX hk f hdim T (c + d) t =
      residueFibreDegree B hX hk f hdim T c t + residueFibreDegree B hX hk f hdim T d t := by
  unfold residueFibreDegree
  rw [picardMap_add, map_add]

/-- The projection `X_T ⟶ T` of the base change. -/
abbrev baseChangeSnd (T : BigFppfOver B (Spec (.of k)) hk) :
    baseChange B hX hk f T ⟶ (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T :=
  pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)

/-- The scheme-theoretic fibre of `X_T ⟶ T` over `t` maps to the base change of `X` to the
residue test scheme at `t`. -/
def fiberToResidueBaseChange (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    (baseChangeSnd B hX hk f T).fiber t ⟶ baseChange B hX hk f (residueTest B hk T t) :=
  pullback.lift ((baseChangeSnd B hX hk f T).fiberι t ≫ pullback.fst _ _)
    ((baseChangeSnd B hX hk f T).fiberToSpecResidueField t) (by
      change ((baseChangeSnd B hX hk f T).fiberι t ≫ pullback.fst _ _) ≫ B.inclusion.map f =
        (baseChangeSnd B hX hk f T).fiberToSpecResidueField t ≫
          (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).fromSpecResidueField t ≫
            B.inclusion.map T.hom)
      rw [Category.assoc, pullback.condition, ← Category.assoc, Scheme.Hom.fiber_fac,
        Category.assoc]
      rfl)

/-- The comparison map from the fibre of `X_T ⟶ T` over `t`, followed by the base change map to
`X_T`, is the inclusion of the fibre. -/
theorem fiberToResidueBaseChange_baseChangeMap (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    fiberToResidueBaseChange B hX hk f T t ≫ baseChangeMap B hX hk f (residueTestι B hk T t) =
      (baseChangeSnd B hX hk f T).fiberι t := by
  apply pullback.hom_ext
  · simp only [fiberToResidueBaseChange, baseChangeMap, Category.assoc, pullback.lift_fst,
      Category.comp_id]
  · simp only [fiberToResidueBaseChange, baseChangeMap, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc]
    exact (Scheme.Hom.fiber_fac _ t).symm

/-- The fibre of `X_T ⟶ T` over `t` is the base change of `X` to the residue test scheme at `t`:
the comparison map sits in a cartesian square over the identity of `Spec κ(t)`. -/
theorem isPullback_fiberToResidueBaseChange (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    IsPullback (fiberToResidueBaseChange B hX hk f T t)
      ((baseChangeSnd B hX hk f T).fiberToSpecResidueField t)
      (pullback.snd (B.inclusion.map f) (B.inclusion.map (residueTest B hk T t).hom))
      (𝟙 _) := by
  have h := (IsPullback.of_hasPullback (baseChangeSnd B hX hk f T)
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).fromSpecResidueField t)).paste_horiz
    (IsPullback.of_hasPullback (B.inclusion.map f) (B.inclusion.map T.hom))
  refine IsPullback.of_right (h₁₂ := pullback.fst (B.inclusion.map f)
      (B.inclusion.map (residueTest B hk T t).hom)) (v₁₃ := B.inclusion.map f)
    (h₂₂ := B.inclusion.map (residueTest B hk T t).hom) ?_ ?_ (IsPullback.of_hasPullback _ _)
  · rw [Category.id_comp, show fiberToResidueBaseChange B hX hk f T t ≫ pullback.fst _ _ =
      (baseChangeSnd B hX hk f T).fiberι t ≫ pullback.fst _ _ from pullback.lift_fst _ _ _]
    exact h
  · rw [Category.comp_id]
    exact pullback.lift_snd _ _ _

/-- The degree does not see which equal structure morphism is used. -/
theorem _root_.Stacks.Picard.ofSchemeDegree_congr_structureMap (K : Type u) [Field K]
    {Y : Scheme.{u}} {p q : Y ⟶ Spec (.of K)} [IsProper p] [IsProper q] (h : p = q)
    (hdim : topologicalKrullDim Y ≤ 1) (c : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.ofSchemeDegree K p hdim c = Stacks.Picard.ofSchemeDegree K q hdim c := by
  subst h
  rfl

/-- The projection `X_T ⟶ T` is proper when `X ⟶ Spec k` is. -/
instance isProper_baseChangeSnd [IsProper (B.inclusion.map f)]
    (T : BigFppfOver B (Spec (.of k)) hk) : IsProper (baseChangeSnd B hX hk f T) :=
  inferInstanceAs (IsProper (pullback.snd _ _))

/-- The fibre of `X_T ⟶ T` over `t` is proper over `Spec κ(t)` when `X ⟶ Spec k` is. -/
instance isProper_fiberToSpecResidueField [IsProper (B.inclusion.map f)]
    (T : BigFppfOver B (Spec (.of k)) hk) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    IsProper ((baseChangeSnd B hX hk f T).fiberToSpecResidueField t) :=
  inferInstanceAs (IsProper (pullback.snd _ _))

/-- The comparison map from the fibre of `X_T ⟶ T` over `t` to the base change of `X` to the
residue test scheme at `t` is an isomorphism. -/
instance isIso_fiberToResidueBaseChange (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    IsIso (fiberToResidueBaseChange B hX hk f T t) :=
  (isPullback_fiberToResidueBaseChange B hX hk f T t).isIso_fst_of_isIso

/-- The comparison map from the fibre of `X_T ⟶ T` over `t` commutes with the projections to
`Spec κ(t)`. -/
theorem fiberToResidueBaseChange_snd (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    fiberToResidueBaseChange B hX hk f T t ≫
        pullback.snd (B.inclusion.map f) (B.inclusion.map (residueTest B hk T t).hom) =
      (baseChangeSnd B hX hk f T).fiberToSpecResidueField t :=
  pullback.lift_snd _ _ _

/-- The fibre of `X_T ⟶ T` over `t` has dimension at most one when `X` does. -/
theorem topologicalKrullDim_fiber_baseChangeSnd [IsProper (B.inclusion.map f)]
    (hdim : topologicalKrullDim X ≤ 1) (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    topologicalKrullDim ((baseChangeSnd B hX hk f T).fiber t) ≤ 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _ (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
    (asIso (fiberToResidueBaseChange B hX hk f T t)))).isHomeomorph).trans_le
    (topologicalKrullDim_baseChange_residueTest B hX hk f hdim T t)

/-- **The fibre degree read on the scheme-theoretic fibre.** The degree of `c` on `X_{κ(t)}` is
the degree over `κ(t)` of the pullback of `c` to the fibre of `X_T ⟶ T` over `t`. -/
theorem residueFibreDegree_eq_ofSchemeDegree_fiber [IsProper (B.inclusion.map f)]
    (hdim : topologicalKrullDim X ≤ 1) (T : BigFppfOver B (Spec (.of k)) hk)
    (c : picardAt B hX hk f T) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    residueFibreDegree B hX hk f hdim T c t =
      Stacks.Picard.ofSchemeDegree
        (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)
        ((baseChangeSnd B hX hk f T).fiberToSpecResidueField t)
        (topologicalKrullDim_fiber_baseChangeSnd B hX hk f hdim T t)
        (Stacks.Picard.schemePullbackClass ((baseChangeSnd B hX hk f T).fiberι t) c) := by
  have h1 := Stacks.Picard.ofSchemeDegree_schemePullbackClass_of_isIso
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)
    (pullback.snd (B.inclusion.map f) (B.inclusion.map (residueTest B hk T t).hom))
    (fiberToResidueBaseChange B hX hk f T t)
    (topologicalKrullDim_baseChange_residueTest B hX hk f hdim T t)
    (topologicalKrullDim_fiber_baseChangeSnd B hX hk f hdim T t)
    (picardMap B hX hk f (residueTestι B hk T t) c)
  have h2 := Stacks.Picard.ofSchemeDegree_congr_structureMap
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)
    (fiberToResidueBaseChange_snd B hX hk f T t)
    (topologicalKrullDim_fiber_baseChangeSnd B hX hk f hdim T t)
    (Stacks.Picard.schemePullbackClass (fiberToResidueBaseChange B hX hk f T t)
      (picardMap B hX hk f (residueTestι B hk T t) c))
  have h3 : Stacks.Picard.schemePullbackClass (fiberToResidueBaseChange B hX hk f T t)
      (picardMap B hX hk f (residueTestι B hk T t) c) =
      Stacks.Picard.schemePullbackClass ((baseChangeSnd B hX hk f T).fiberι t) c := by
    change Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _ c) = _
    rw [Stacks.Picard.schemePullbackClass_comp, fiberToResidueBaseChange_baseChangeMap]
  rw [← h3, ← h2]
  exact h1.symm

open ProperFlatFibreEulerCharacteristic in
/-- **The fibre degree is `χ(X_t, ℒ_t) - χ(X_t, 𝒪)`.** -/
theorem residueFibreDegree_picardClass_eq_fibreEulerCharacteristic_sub
    [IsProper (B.inclusion.map f)] (hdim : topologicalKrullDim X ≤ 1)
    (T : BigFppfOver B (Spec (.of k)) hk)
    (L : (baseChange B hX hk f T).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (baseChange B hX hk f T).presheaf
      (Stacks.RingedSpace.structureIsSheaf (baseChange B hX hk f T).toRingedSpace) L)
    [L.IsFinitePresentation] (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    residueFibreDegree B hX hk f hdim T (Stacks.SheafOfModules.picardClass _ _ L hL) t =
      fibreCoherentEulerCharacteristic (baseChangeSnd B hX hk f T) L t -
        @fibreCoherentEulerCharacteristic _ _ (baseChangeSnd B hX hk f T) _
          (SheafOfModules.unit (baseChange B hX hk f T).ringCatSheaf)
          (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit _) t := by
  rw [residueFibreDegree_eq_ofSchemeDegree_fiber]
  change Stacks.Picard.ofSchemeDegree _ _ _ (Stacks.Picard.pullbackClass _ _) = _
  rw [Stacks.Picard.pullbackClass_classOf
    ((baseChangeSnd B hX hk f T).fiberι t).toLRSHom.toShHom L hL]
  refine (Stacks.Picard.ofSchemeDegree_picardClass _ _ _ _ _).trans ?_
  unfold invertibleCurveDegree fibreCoherentEulerCharacteristic
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum]
  congr 1
  exact finsum_congr fun n =>
    (congrArg (fun m : ℕ => (-1 : ℤ) ^ n * (m : ℤ)) (finrank_cohomologyOverField_eq_of_iso _ _
      (Scheme.Modules.pullbackUnitIso ((baseChangeSnd B hX hk f T).fiberι t)) n)).symm

open ProperFlatFibreEulerCharacteristic in
/-- **The degree on the fibres of a family of invertible modules is locally constant.** For a
proper flat morphism `X ⟶ Spec k` locally of finite presentation, with `X` of dimension at most
one, and a class `c ∈ Pic(X_T)`, the function `t ↦ deg(c_t)` on `T` is locally constant: it is
`χ(X_t, ℒ_t) - χ(X_t, 𝒪)` (`residueFibreDegree_picardClass_eq_fibreEulerCharacteristic_sub`),
and both terms are locally constant by [Stacks, Tag 0B9T]. -/
theorem isLocallyConstant_residueFibreDegree [IsProper (B.inclusion.map f)]
    [Flat (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
    (hdim : topologicalKrullDim X ≤ 1) (T : BigFppfOver B (Spec (.of k)) hk)
    (c : picardAt B hX hk f T) :
    IsLocallyConstant (residueFibreDegree B hX hk f hdim T c) := by
  obtain ⟨L, hL, rfl⟩ : ∃ (L : (baseChange B hX hk f T).Modules)
      (hL : Stacks.SheafOfModules.IsInvertible (baseChange B hX hk f T).presheaf
        (Stacks.RingedSpace.structureIsSheaf (baseChange B hX hk f T).toRingedSpace) L),
      Stacks.SheafOfModules.picardClass (baseChange B hX hk f T).presheaf
        (Stacks.RingedSpace.structureIsSheaf (baseChange B hX hk f T).toRingedSpace) L hL = c :=
    ⟨_, _, Stacks.Picard.classOf_picardRepresentative (baseChange B hX hk f T).toRingedSpace c⟩
  have : L.IsFinitePresentation :=
    Stacks.ModuleDescent.isFinitePresentation_of_isInvertible _ L
      (Stacks.Picard.isInvertible_ringCatSheaf_of_isInvertible L hL)
  let O := SheafOfModules.unit (baseChange B hX hk f T).ringCatSheaf
  have : O.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit _
  have hfp : FinitePresentation (baseChangeSnd B hX hk f T) :=
    FinitePresentation.mk inferInstance inferInstance inferInstance
  have key : ∀ (M : (baseChange B hX hk f T).Modules) [M.IsFinitePresentation],
      SheafOfModules.IsInvertible (baseChange B hX hk f T).presheaf
        (baseChange B hX hk f T).ringCatSheaf.2 M →
      IsLocallyConstant (fibreCoherentEulerCharacteristic (baseChangeSnd B hX hk f T) M) := by
    intro M _ hM
    have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M 1
    have : M.IsQuasicoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M
    exact (isLocallyConstant_fibreCoherentEulerCharacteristic_and_baseChange _ hfp M
      (VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree _ M)).1
  have hfun : residueFibreDegree B hX hk f hdim T
      (Stacks.SheafOfModules.picardClass _ _ L hL) =
      fun t => fibreCoherentEulerCharacteristic (baseChangeSnd B hX hk f T) L t -
        fibreCoherentEulerCharacteristic (baseChangeSnd B hX hk f T) O t :=
    funext fun t =>
      residueFibreDegree_picardClass_eq_fibreEulerCharacteristic_sub B hX hk f hdim T L hL t
  rw [hfun]
  exact (key L (Stacks.Picard.isInvertible_ringCatSheaf_of_isInvertible L hL)).comp₂
    (key O (Stacks.AlgebraicGeometry.Tag09NY.isInvertible_unit _)) (· - ·)

end Stacks.PicardFunctor

end
