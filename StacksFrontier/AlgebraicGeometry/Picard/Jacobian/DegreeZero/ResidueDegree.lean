module

public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZero.FibreDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Normalized
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeBaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.PicardFunctorPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange

/-!
# The degree of a section of the Picard functor of a curve at a point

Let `X` be a smooth projective curve over an algebraically closed field `k`, and `Pic_{X/k}` its
Picard functor on a big fppf site ([Stacks, Tag 0B9L]). For a test scheme `T`, a section
`ξ ∈ Pic_{X/k}(T)` and a point `t ∈ T`, the restriction `ξ_t ∈ Pic_{X/k}(κ(t))` is the class of a
unique invertible module on `X_{κ(t)}`, because `X` has a rational point and `Pic(κ(t)) = 0`
([Stacks, Tag 0B9N]). Its degree is the *degree of `ξ` at `t`*.

This degree is additive in `ξ`, compatible with restriction along morphisms of test schemes,
and locally constant in `t`: by [Stacks, Tag 0B9N] the section `ξ` is the class of an invertible
module `ℒ` on `X_T`, and then the degree at `t` is `deg(ℒ_t)`, locally constant by
`Stacks.PicardFunctor.isLocallyConstant_residueFibreDegree`. The degree-zero part `Pic⁰_{X/k}`
(`Stacks.PicardFunctor.degreeZeroSubfunctor`) is the subfunctor where it vanishes identically.

## Main definitions

* `Stacks.PicardFunctor.residueDegree`: the degree of `ξ ∈ Pic_{X/k}(T)` at `t ∈ T`.

## Main results

* `Stacks.PicardFunctor.residueDegree_add`, `residueDegree_zero`, `residueDegree_neg`.
* `Stacks.PicardFunctor.residueDegree_map`: compatibility with restriction.
* `Stacks.PicardFunctor.isLocallyConstant_residueDegree`: local constancy in `t`.
* `Stacks.PicardFunctor.mem_degreeZeroSubfunctor_iff_residueDegree`: `ξ ∈ Pic⁰_{X/k}(T)` if and
  only if its degree vanishes at every point of `T`.
* `Stacks.PicardFunctor.residueDegree_ofSchemeAddEquivPicardFunctorOfCurve`: at the test scheme
  `Spec k`, the degree is the degree of the corresponding class of `Pic(X)`.

## References

* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-- Restriction of sections of the Picard functor, as a homomorphism of groups. -/
def picardFunctorMapHom {T U : BigFppfOver B S hS} (φ : T ⟶ U) :
    (picardFunctor B hX hS f).obj (op U) →+ (picardFunctor B hX hS f).obj (op T) :=
  AddMonoidHom.mk' ((picardFunctor B hX hS f).map φ.op) (picardFunctor_map_add B hX hS f φ)

/-- **The degree over an isomorphic ground field, in `Spec` form.** For an isomorphism of fields
`φ : k ⟶ κ` and `p : Y ⟶ Spec κ`, the degree over `k` along `p ≫ Spec φ` is the degree over `κ`
along `p`. -/
theorem _root_.Stacks.Picard.ofSchemeDegree_comp_SpecMap_of_isIso (k κ : Type u) [Field k]
    [Field κ] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of κ)) (φ : CommRingCat.of k ⟶ CommRingCat.of κ)
    [IsIso φ] [IsProper p] [IsProper (p ≫ Spec.map φ)] (hdim : topologicalKrullDim Y ≤ 1)
    (c : Stacks.Picard.ofScheme Y) :
    Stacks.Picard.ofSchemeDegree k (p ≫ Spec.map φ) hdim c =
      Stacks.Picard.ofSchemeDegree κ p hdim c := by
  let : Algebra k κ := φ.hom.toAlgebra
  obtain ⟨L, hL, rfl⟩ : ∃ (L : Y.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L),
      Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L hL = c :=
    ⟨_, _, Stacks.Picard.classOf_picardRepresentative Y.toRingedSpace c⟩
  rw [Stacks.Picard.ofSchemeDegree_picardClass, Stacks.Picard.ofSchemeDegree_picardClass]
  let := Stacks.Picard.isInvertible_ringCatSheaf_of_isInvertible L hL
  have hc : (Scheme.ΓSpecIso (.of k)).inv ≫ (p ≫ Spec.map φ).appTop =
      φ ≫ (Scheme.ΓSpecIso (.of κ)).inv ≫ p.appTop := by
    show (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map φ).appTop ≫ p.appTop = _
    rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  exact invertibleCurveDegree_eq_of_bijective_algebraMap k κ
    (ConcreteCategory.bijective_of_isIso φ) (p ≫ Spec.map φ) p
    ((congrArg CommRingCat.Hom.hom hc).trans rfl) hdim L

section Curve

variable (k : Type u) [Field k] [IsAlgClosed k] {hk : B.Contains (Spec (.of k))}
  (g : B.obj hX ⟶ B.obj hk) [IsCurve k (B.inclusion.map g)]
  [IsProjectiveVariety k (B.inclusion.map g)] [Smooth (B.inclusion.map g)]

include g in
omit [IsAlgClosed k] [IsProjectiveVariety k (B.inclusion.map g)] [Smooth (B.inclusion.map g)] in
/-- A smooth projective curve has dimension at most one. -/
theorem topologicalKrullDim_le_one_of_curve : topologicalKrullDim X ≤ 1 :=
  (IsCurve.topologicalKrullDim_eq_one (k := k) (f := B.inclusion.map g)).le

/-- The isomorphism condition of [Stacks, Tag 0B9N] for a smooth projective curve over an
algebraically closed field, with the rational point of
`Stacks.PicardFunctor.exists_section_of_isAlgClosed`. -/
theorem isIso_c_baseChangeProj_of_curve (U : BigFppfOver B (Spec (.of k)) hk) :
    IsIso (baseChangeProj B hX hk g U).toLRSHom.toHom.c :=
  have : CompactSpace (B.inclusion.obj (B.obj hk)) :=
    (inferInstance : CompactSpace (Spec (.of k)))
  have : CompactSpace (B.inclusion.obj (B.obj hX)) :=
    QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map g)
  isIso_c_baseChange_of_isCurve_of_section (B.inclusion.map g)
    (exists_section_of_isAlgClosed k (B.inclusion.map g)).choose
    (exists_section_of_isAlgClosed k (B.inclusion.map g)).choose_spec
    (B.inclusion.map U.hom)

/-- **[Stacks, Tag 0B9N] for a smooth projective curve**: every section of the Picard functor is
the class of an invertible module on the base change. -/
theorem surjective_toPicardFunctorHom_of_curve (T : BigFppfOver B (Spec (.of k)) hk) :
    Function.Surjective (toPicardFunctorHom B hX hk g T) :=
  have : CompactSpace (B.inclusion.obj (B.obj hk)) :=
    (inferInstance : CompactSpace (Spec (.of k)))
  have : CompactSpace (B.inclusion.obj (B.obj hX)) :=
    QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map g)
  surjective_toPicardFunctorHom B hX hk g
    (exists_section_of_isAlgClosed k (B.inclusion.map g)).choose
    (exists_section_of_isAlgClosed k (B.inclusion.map g)).choose_spec
    (isIso_c_baseChangeProj_of_curve B hX k g) T

/-- **`Pic(X_{κ(t)}) ≃+ Pic_{X/k}(κ(t))`** at the residue test scheme of a point. -/
def residuePicardAddEquiv (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    picardAt B hX hk g (residueTest B hk T t) ≃+
      (picardFunctor B hX hk g).obj (op (residueTest B hk T t)) :=
  haveI : CompactSpace (B.inclusion.obj (B.obj hk)) :=
    (inferInstance : CompactSpace (Spec (.of k)))
  haveI : CompactSpace (B.inclusion.obj (B.obj hX)) :=
    QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map g)
  haveI : Nonempty (B.inclusion.obj (B.obj hX)) :=
    (inferInstance : IsIntegral (B.inclusion.obj (B.obj hX))).nonempty
  haveI : Subsingleton (Stacks.Picard.ofScheme
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (residueTest B hk T t))) :=
    Stacks.Picard.subsingleton_ofScheme_of_discreteTopology
      (Spec (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t))
  picardAtAddEquivOfSubsingleton B hX hk g
    (exists_section_of_isAlgClosed k (B.inclusion.map g)).choose
    (exists_section_of_isAlgClosed k (B.inclusion.map g)).choose_spec
    (isIso_c_baseChangeProj_of_curve B hX k g) (residueTest B hk T t)

/-- `Stacks.PicardFunctor.residuePicardAddEquiv` sends a class of `Pic(X_{κ(t)})` to its image
under `Stacks.PicardFunctor.toPicardFunctor`. -/
theorem residuePicardAddEquiv_apply (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T)
    (c : picardAt B hX hk g (residueTest B hk T t)) :
    residuePicardAddEquiv B hX k g T t c =
      (toPicardFunctor B hX hk g).app (op (residueTest B hk T t)) c :=
  rfl

/-- **The degree of a section of the Picard functor at a point.** For `ξ ∈ Pic_{X/k}(T)` and
`t ∈ T`, the degree over `κ(t)` of the invertible module on `X_{κ(t)}` whose class is the
restriction of `ξ` to `Spec κ(t)`. -/
def residueDegree (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk g).obj (op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) : ℤ :=
  Stacks.Picard.ofSchemeDegree
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)
    (pullback.snd (B.inclusion.map g) (B.inclusion.map (residueTest B hk T t).hom))
    (topologicalKrullDim_baseChange_residueTest B hX hk g
      (topologicalKrullDim_le_one_of_curve B hX k g) T t)
    ((residuePicardAddEquiv B hX k g T t).symm
      ((picardFunctor B hX hk g).map (residueTestι B hk T t).op ξ))

/-- The degree at a point of the class of an invertible module on `X_T` is the degree of its
restriction to the fibre over that point. -/
theorem residueDegree_toPicardFunctor (T : BigFppfOver B (Spec (.of k)) hk)
    (c : picardAt B hX hk g T) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    residueDegree B hX k g T ((toPicardFunctor B hX hk g).app (op T) c) t =
      residueFibreDegree B hX hk g (topologicalKrullDim_le_one_of_curve B hX k g) T c t := by
  have h := toPicardFunctor_app_naturality B hX hk g (residueTestι B hk T t) c
  unfold residueDegree residueFibreDegree
  refine congrArg _ ?_
  refine (congrArg (residuePicardAddEquiv B hX k g T t).symm h.symm).trans ?_
  exact AddEquiv.symm_apply_apply _ _

/-- The degree at a point is additive in the section. -/
theorem residueDegree_add (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ η : (picardFunctor B hX hk g).obj (op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    residueDegree B hX k g T (ξ + η) t =
      residueDegree B hX k g T ξ t + residueDegree B hX k g T η t := by
  unfold residueDegree
  rw [picardFunctor_map_add, map_add, map_add]

/-- The degree at a point, as a homomorphism of groups. -/
def residueDegreeHom (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    (picardFunctor B hX hk g).obj (op T) →+ ℤ :=
  AddMonoidHom.mk' (fun ξ => residueDegree B hX k g T ξ t)
    (fun ξ η => residueDegree_add B hX k g T ξ η t)

/-- The degree at a point of the zero section is zero. -/
@[simp] theorem residueDegree_zero (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    residueDegree B hX k g T 0 t = 0 :=
  map_zero (residueDegreeHom B hX k g T t)

/-- The degree at a point of `-ξ` is minus the degree of `ξ`. -/
@[simp] theorem residueDegree_neg (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk g).obj (op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    residueDegree B hX k g T (-ξ) t = -residueDegree B hX k g T ξ t :=
  map_neg (residueDegreeHom B hX k g T t) ξ

/-- **The degree at a point is compatible with restriction**: the degree of the restriction of
`ξ` along `φ : T ⟶ U` at `t` is the degree of `ξ` at `φ(t)`, the degree being unchanged by the
extension of residue fields `κ(φ t) ⟶ κ(t)` ([Stacks, Tag 0B59]). -/
theorem residueDegree_map {T U : BigFppfOver B (Spec (.of k)) hk} (φ : T ⟶ U)
    (ξ : (picardFunctor B hX hk g).obj (op U))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    residueDegree B hX k g T ((picardFunctor B hX hk g).map φ.op ξ) t =
      residueDegree B hX k g U ξ ((BigFppfOver.toScheme B (Spec (.of k)) hk).map φ t) := by
  set u := (BigFppfOver.toScheme B (Spec (.of k)) hk).map φ t
  set M := (residuePicardAddEquiv B hX k g U u).symm
    ((picardFunctor B hX hk g).map (residueTestι B hk U u).op ξ) with hM
  have hMξ : (toPicardFunctor B hX hk g).app (op (residueTest B hk U u)) M =
      (picardFunctor B hX hk g).map (residueTestι B hk U u).op ξ := by
    rw [← residuePicardAddEquiv_apply, hM, AddEquiv.apply_symm_apply]
  have hres : (picardFunctor B hX hk g).map (residueTestι B hk T t).op
      ((picardFunctor B hX hk g).map φ.op ξ) =
      (toPicardFunctor B hX hk g).app (op (residueTest B hk T t))
        (picardMap B hX hk g (residueTestMap B hk φ t) M) := by
    rw [toPicardFunctor_app_naturality, hMξ, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply]
    exact congrArg (fun ψ => (picardFunctor B hX hk g).map ψ ξ)
      (Quiver.Hom.unop_inj (residueTestMap_comp_residueTestι B hk φ t)).symm
  unfold residueDegree
  rw [hres, ← residuePicardAddEquiv_apply, AddEquiv.symm_apply_apply, ← hM]
  let : Algebra (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).residueField u)
      (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t) :=
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).map φ).residueFieldMap t).hom.toAlgebra
  have hsq := isPullback_baseChangeMap_residueTestMap B hX hk g φ t
  have e : B.inclusion.map (residueTestMap B hk φ t).left =
      Spec.map (CommRingCat.ofHom (algebraMap
        (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).residueField u)
        (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t))) := rfl
  rw [e] at hsq
  exact Stacks.Picard.ofSchemeDegree_schemePullbackClass_of_isPullback
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).residueField u)
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t) _ _ _ hsq _ _ M

/-- **The degree at a point is locally constant.** By [Stacks, Tag 0B9N] the section is the class
of an invertible module on `X_T`, whose fibre degree is locally constant
(`Stacks.PicardFunctor.isLocallyConstant_residueFibreDegree`). -/
theorem isLocallyConstant_residueDegree (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk g).obj (op T)) :
    IsLocallyConstant (residueDegree B hX k g T ξ) := by
  obtain ⟨c, rfl⟩ := surjective_toPicardFunctorHom_of_curve B hX k g T ξ
  have h : residueDegree B hX k g T (toPicardFunctorHom B hX hk g T c) =
      residueFibreDegree B hX hk g (topologicalKrullDim_le_one_of_curve B hX k g) T c :=
    funext fun t => residueDegree_toPicardFunctor B hX k g T c t
  rw [h]
  exact isLocallyConstant_residueFibreDegree B hX hk g _ T c

/-- **`ξ ∈ Pic⁰_{X/k}(T)` exactly when its degree vanishes at every point of `T`.** -/
theorem mem_degreeZeroSubfunctor_iff_residueDegree (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk g).obj (op T)) :
    ξ ∈ (degreeZeroSubfunctor B hX hk g (topologicalKrullDim_le_one_of_curve B hX k g)).obj
        (op T) ↔ ∀ t, residueDegree B hX k g T ξ t = 0 := by
  rw [mem_degreeZeroSubfunctor_iff]
  refine forall_congr' fun t => ⟨fun ⟨L, hL, hLξ⟩ => ?_, fun h => ⟨_, h, ?_⟩⟩
  · unfold residueDegree
    rw [← hLξ, ← residuePicardAddEquiv_apply, AddEquiv.symm_apply_apply]
    exact hL
  · rw [← residuePicardAddEquiv_apply, AddEquiv.apply_symm_apply]

/-- **At the test scheme `Spec k`, the degree is the degree on `X`.** Under
`Stacks.PicardFunctor.ofSchemeAddEquivPicardFunctorOfCurve`, `Pic(X) ≃+ Pic_{X/k}(Spec k)`, the
degree at the point of `Spec k` of the image of a class is its degree. -/
theorem residueDegree_ofSchemeAddEquivPicardFunctorOfCurve (hdim : topologicalKrullDim X ≤ 1)
    (c : Stacks.Picard.ofScheme X)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (terminalTest B hk)) :
    residueDegree B hX k g (terminalTest B hk) (ofSchemeAddEquivPicardFunctorOfCurve B hX k g c) t =
      Stacks.Picard.ofSchemeDegree k (B.inclusion.map g) hdim c := by
  have h1 : ofSchemeAddEquivPicardFunctorOfCurve B hX k g c =
      (toPicardFunctor B hX hk g).app (op (terminalTest B hk))
        (Stacks.Picard.schemePullbackClass (baseChangeTerminalIso B hX hk g).hom c) := rfl
  rw [h1, residueDegree_toPicardFunctor]
  unfold residueFibreDegree
  set ψ := B.inclusion.map (residueTest B hk (terminalTest B hk) t).hom
  set φ := pullback.fst (B.inclusion.map g) ψ
  have hφ : baseChangeMap B hX hk g (residueTestι B hk (terminalTest B hk) t) ≫
      (baseChangeTerminalIso B hX hk g).hom = φ := by
    simp only [baseChangeTerminalIso, asIso_hom, baseChangeMap, φ, pullback.lift_fst,
      Category.comp_id]
    rfl
  have h2 : picardMap B hX hk g (residueTestι B hk (terminalTest B hk) t)
      (Stacks.Picard.schemePullbackClass (baseChangeTerminalIso B hX hk g).hom c) =
      Stacks.Picard.schemePullbackClass φ c := by
    show Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _ c) = _
    rw [Stacks.Picard.schemePullbackClass_comp, hφ]
  rw [h2]
  have : Subsingleton ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (terminalTest B hk)) :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  have hψ : IsIso ψ := by
    have : IsIso ((Spec (.of k)).fromSpecResidueField (IsLocalRing.closedPoint k)) :=
      isIso_fromSpecResidueField_closedPoint k
    obtain rfl : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    show IsIso ((Spec (.of k)).fromSpecResidueField (IsLocalRing.closedPoint k) ≫
      B.inclusion.map (𝟙 (B.obj hk)))
    have : IsIso (B.inclusion.map (𝟙 (B.obj hk))) := Functor.map_isIso _ _
    infer_instance
  have : IsIso φ := (IsPullback.of_hasPullback (B.inclusion.map g) ψ).isIso_fst_of_isIso
  have : IsIso (Spec.preimage ψ) :=
    ⟨Spec.preimage (inv ψ), Spec.map_injective (by simp [Spec.map_comp]),
      Spec.map_injective (by simp [Spec.map_comp])⟩
  have hsq : pullback.snd (B.inclusion.map g) ψ ≫ Spec.map (Spec.preimage ψ) =
      φ ≫ B.inclusion.map g := by
    rw [Spec.map_preimage]
    exact pullback.condition.symm
  have : IsProper (pullback.snd (B.inclusion.map g) ψ ≫ Spec.map (Spec.preimage ψ)) := by
    rw [hsq]; infer_instance
  have hY := topologicalKrullDim_baseChange_residueTest B hX hk g
    (topologicalKrullDim_le_one_of_curve B hX k g) (terminalTest B hk) t
  calc _ = Stacks.Picard.ofSchemeDegree k
        (pullback.snd (B.inclusion.map g) ψ ≫ Spec.map (Spec.preimage ψ)) hY
        (Stacks.Picard.schemePullbackClass φ c) :=
      (Stacks.Picard.ofSchemeDegree_comp_SpecMap_of_isIso k _ _ (Spec.preimage ψ) hY _).symm
    _ = Stacks.Picard.ofSchemeDegree k (φ ≫ B.inclusion.map g) hY
        (Stacks.Picard.schemePullbackClass φ c) :=
      Stacks.Picard.ofSchemeDegree_congr_structureMap k hsq hY _
    _ = _ := Stacks.Picard.ofSchemeDegree_schemePullbackClass_of_isIso k (B.inclusion.map g) φ
        hdim hY c

end Curve

end Stacks.PicardFunctor

end
