module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianPointGroup
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeZeroDivisibility

/-!
# The endomorphism of the Jacobian induced by an endomorphism of a curve

Let `X` be a smooth projective curve over a field `k` and `Ψ : X ⟶ X` a morphism over `k`
(`Ψ ≫ f = f`). For every `k`-scheme `T` the base change `Θ_T = Ψ ×_k 𝟙_T : X_T ⟶ X_T` is natural
in `T`, so pulling back along `Θ_T` is an endomorphism of the presheaf `T ↦ Pic(X_T)`, hence of
the Picard functor `Pic_{X/k}`, its fppf sheafification. By Yoneda it is an endomorphism of the
Picard scheme, which carries the connected component `Pic^0_{X/k}` of the identity into itself
since `Pic^0_{X/k}` is open and closed; and since it respects the group laws of the values of the
Picard functor, the induced endomorphism `Ψ^*` of the Jacobian `J = Pic^0_{X/k}` is a
homomorphism of group objects. On rational points it is the pullback `Ψ^*` on `Pic^0(X)`.

This is the map `φ^* : J → J` of [Stacks, Tag 03U1]. The construction is that of
`Stacks.PicardFunctor.jacobianFrobenius` (for a morphism lying over a power of the
Frobenius of `Spec k`), for a morphism over `k` and in every characteristic.

## Main definitions

* `Stacks.PicardFunctor.endoBaseChangeMap`: `Θ_T : X_T ⟶ X_T`.
* `Stacks.PicardFunctor.endoPicardPresheafMap`, `Stacks.PicardFunctor.endoPicardMap`: `Θ^*` on
  the presheaf `T ↦ Pic(X_T)` and on the Picard functor.
* `Stacks.PicardFunctor.endoPicardSchemeHom`: the induced endomorphism of the Picard scheme.
* `Stacks.PicardFunctor.endoJacobianHom`, `Stacks.PicardFunctor.jacobianPullback`: the
  endomorphism `Ψ^*` of `Pic^0_{X/k}`, in the site and as a scheme over `k`.

## Main results

* `Stacks.PicardFunctor.isMonHom_jacobianPullback`: `Ψ^*` is a homomorphism.
* `Stacks.PicardFunctor.jacobianPointsAddEquiv_comp_jacobianPullback`: on `J(k) = Pic^0(X)`,
  it is the pullback of line bundles along `Ψ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.PicardFunctor

section Presheaf

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (Ψ : X ⟶ X)
  (hΨ : Ψ ≫ B.inclusion.map f = B.inclusion.map f)

/-- **The base change of `Ψ`**, `Θ_T = Ψ ×_k 𝟙_T : X ×_k T ⟶ X ×_k T`. -/
def endoBaseChangeMap (T : BigFppfOver B (Spec (.of k)) hk) :
    baseChange B hX hk f T ⟶ baseChange B hX hk f T :=
  pullback.map (B.inclusion.map f) (B.inclusion.map T.hom) (B.inclusion.map f)
    (B.inclusion.map T.hom) Ψ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hΨ])
    (by rw [Category.comp_id, Category.id_comp])

/-- `Θ_T` followed by the first projection is the first projection followed by `Ψ`. -/
@[reassoc (attr := simp)]
theorem endoBaseChangeMap_fst (T : BigFppfOver B (Spec (.of k)) hk) :
    endoBaseChangeMap B hX hk f Ψ hΨ T ≫
        pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom) =
      pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom) ≫ Ψ :=
  pullback.lift_fst _ _ _

/-- `Θ_T` commutes with the second projection `X_T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem endoBaseChangeMap_snd (T : BigFppfOver B (Spec (.of k)) hk) :
    endoBaseChangeMap B hX hk f Ψ hΨ T ≫
        pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom) =
      pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom) := by
  simp [endoBaseChangeMap]

/-- `Θ` is natural in the test scheme. -/
theorem baseChangeMap_endoBaseChangeMap {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U) :
    baseChangeMap B hX hk f g ≫ endoBaseChangeMap B hX hk f Ψ hΨ U =
      endoBaseChangeMap B hX hk f Ψ hΨ T ≫ baseChangeMap B hX hk f g := by
  apply pullback.hom_ext
  · simp only [baseChangeMap, Category.assoc, endoBaseChangeMap_fst, pullback.lift_fst_assoc,
      pullback.lift_fst, Category.comp_id]
  · simp only [baseChangeMap, Category.assoc, endoBaseChangeMap_snd, pullback.lift_snd,
      endoBaseChangeMap_snd_assoc]

/-- `Θ^*` commutes with pullback along a morphism of test schemes. -/
theorem schemePullbackClass_endoBaseChangeMap_picardMap {T U : BigFppfOver B (Spec (.of k)) hk}
    (g : T ⟶ U) (x : picardAt B hX hk f U) :
    Stacks.Picard.schemePullbackClass (endoBaseChangeMap B hX hk f Ψ hΨ T)
        (picardMap B hX hk f g x) =
      picardMap B hX hk f g
        (Stacks.Picard.schemePullbackClass (endoBaseChangeMap B hX hk f Ψ hΨ U) x) := by
  change Stacks.Picard.schemePullbackClass (endoBaseChangeMap B hX hk f Ψ hΨ T)
      (Stacks.Picard.schemePullbackClass (baseChangeMap B hX hk f g) x) =
    Stacks.Picard.schemePullbackClass (baseChangeMap B hX hk f g)
      (Stacks.Picard.schemePullbackClass (endoBaseChangeMap B hX hk f Ψ hΨ U) x)
  rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
    baseChangeMap_endoBaseChangeMap]

/-- **`Θ^*` on the presheaf `T ↦ Pic(X_T)`.** -/
def endoPicardPresheafMap : picardPresheaf B hX hk f ⟶ picardPresheaf B hX hk f where
  app T := TypeCat.ofHom
    (Stacks.Picard.schemePullbackClass (endoBaseChangeMap B hX hk f Ψ hΨ T.unop))
  naturality {T U} g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact schemePullbackClass_endoBaseChangeMap_picardMap B hX hk f Ψ hΨ g.unop x

/-- **`Θ^*` on the Picard functor**: the sheafification of `endoPicardPresheafMap`. -/
def endoPicardMap : picardFunctor B hX hk f ⟶ picardFunctor B hX hk f :=
  sheafifyMap (BigFppfOver.topology B (Spec (.of k)) hk)
    (endoPicardPresheafMap B hX hk f Ψ hΨ)

/-- `Θ^*` on the Picard functor extends `Θ^*` on Picard groups of base changes. -/
theorem endoPicardMap_toPicardFunctor (T : BigFppfOver B (Spec (.of k)) hk)
    (x : picardAt B hX hk f T) :
    (endoPicardMap B hX hk f Ψ hΨ).app (op T)
        ((toPicardFunctor B hX hk f).app (op T) x) =
      (toPicardFunctor B hX hk f).app (op T)
        (Stacks.Picard.schemePullbackClass (endoBaseChangeMap B hX hk f Ψ hΨ T) x) :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality
    (BigFppfOver.topology B (Spec (.of k)) hk)
    (endoPicardPresheafMap B hX hk f Ψ hΨ)) (op T)) x).symm

end Presheaf

section Curve

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (Ψ : X ⟶ X)
  (hΨ : Ψ ≫ B.inclusion.map f = B.inclusion.map f)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)]

include σ hσ in
/-- `Θ^*` on the Picard functor of a smooth projective curve with a rational point is additive:
every point is the class of an invertible module on the base change ([Stacks, Tag 0B9N]). -/
theorem endoPicardMap_add (T : BigFppfOver B (Spec (.of k)) hk)
    (a b : (picardFunctor B hX hk f).obj (op T)) :
    (endoPicardMap B hX hk f Ψ hΨ).app (op T) (a + b) =
      (endoPicardMap B hX hk f Ψ hΨ).app (op T) a +
        (endoPicardMap B hX hk f Ψ hΨ).app (op T) b := by
  have hsurj := surjective_toPicardFunctorHom B hX hk f σ hσ
    (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) T
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  rw [← map_add, toPicardFunctorHom_apply, toPicardFunctorHom_apply, toPicardFunctorHom_apply,
    endoPicardMap_toPicardFunctor, endoPicardMap_toPicardFunctor,
    endoPicardMap_toPicardFunctor, Stacks.Picard.schemePullbackClass_add,
    toPicardFunctor_app_add]

include σ hσ in
/-- `Θ^*` on the Picard functor of a smooth projective curve with a rational point maps `0` to
`0`. -/
theorem endoPicardMap_zero (T : BigFppfOver B (Spec (.of k)) hk) :
    (endoPicardMap B hX hk f Ψ hΨ).app (op T) 0 = 0 := by
  have h := endoPicardMap_add B hX hk f Ψ hΨ σ hσ T 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

variable [(picardFunctor B hX hk f).IsRepresentable]

/-- **`Θ^*` on the Picard scheme**, by Yoneda. -/
def endoPicardSchemeHom : picardSchemeOver B hX hk f ⟶ picardSchemeOver B hX hk f :=
  (picardHomEquiv B hX hk f).symm
    ((endoPicardMap B hX hk f Ψ hΨ).app _ (universalPoint B hX hk f))

omit [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] in
/-- The endomorphism of the Picard scheme classifies `Θ^*` of the classified point. -/
theorem picardHomEquiv_comp_endoPicardSchemeHom {T : BigFppfOver B (Spec (.of k)) hk}
    (x : T ⟶ picardSchemeOver B hX hk f) :
    picardHomEquiv B hX hk f (x ≫ endoPicardSchemeHom B hX hk f Ψ hΨ) =
      (endoPicardMap B hX hk f Ψ hΨ).app (op T) (picardHomEquiv B hX hk f x) := by
  have hx : picardHomEquiv B hX hk f x =
      (picardFunctor B hX hk f).map x.op (universalPoint B hX hk f) := by
    rw [← (picardFunctor B hX hk f).representableBy.homEquiv_comp x (𝟙 _), Category.comp_id]
  rw [(picardFunctor B hX hk f).representableBy.homEquiv_comp, endoPicardSchemeHom,
    Equiv.apply_symm_apply, hx]
  exact (NatTrans.naturality_apply (endoPicardMap B hX hk f Ψ hΨ) x.op
    (universalPoint B hX hk f)).symm

end Curve

section Jacobian

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (Ψ : X ⟶ X)
  (hΨ : Ψ ≫ B.inclusion.map f = B.inclusion.map f)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [(picardFunctor B hX hk f).IsRepresentable] [IsSepClosed k]

/-- **`Θ^*` maps `Pic^0_{X/k}` into itself.** The image of the connected `Pic^0_{X/k}` under the
endomorphism of the Picard scheme is connected and contains the zero point, and `Pic^0_{X/k}` is
open and closed. -/
theorem exists_endoJacobianHom :
    ∃ F : picardSchemeDegreeComponent B hX hk f σ hσ 0 ⟶
        picardSchemeDegreeComponent B hX hk f σ hσ 0,
      F ≫ picardSchemeDegreeComponentι B hX hk f σ hσ 0 =
        picardSchemeDegreeComponentι B hX hk f σ hσ 0 ≫ endoPicardSchemeHom B hX hk f Ψ hΨ := by
  set ιJ := picardSchemeDegreeComponentι B hX hk f σ hσ 0
  set ν := endoPicardSchemeHom B hX hk f Ψ hΨ
  refine (exists_comp_picardSchemeDegreeComponentι_iff B hX hk f σ hσ (ιJ ≫ ν) 0).mpr
    ((range_subset_picardDegreeLocus_iff B hX hk f σ hσ (ιJ ≫ ν) 0).mp ?_)
  obtain ⟨-, -, hirr⟩ := universallyClosed_picardSchemeDegreeComponent_zero B hX hk f σ hσ
  have hconn : _root_.IsPreconnected (Set.range (B.inclusion.map (ιJ ≫ ν).left)) := by
    have h := (IsPreirreducible.isPreconnected
      (@IrreducibleSpace.isIrreducible_univ _ _ hirr).2).image
      (B.inclusion.map (ιJ ≫ ν).left) (B.inclusion.map (ιJ ≫ ν).left).continuous.continuousOn
    rwa [Set.image_univ] at h
  refine hconn.subset_isClopen (isClopen_picardDegreeLocus B hX hk f σ hσ 0) ?_
  let T₀ : BigFppfOver B (Spec (.of k)) hk := fieldObj B hk k hk
  let φ₀ : T₀ ⟶ picardSchemeOver B hX hk f := (picardHomEquiv B hX hk f).symm 0
  have hφ₀ : ∀ t, curveFibreDegree B hX hk f σ hσ T₀ (picardHomEquiv B hX hk f φ₀) t = 0 := by
    rw [Equiv.apply_symm_apply]
    exact (degreeZeroAddSubgroup B hX hk f σ hσ T₀).zero_mem
  obtain ⟨ψ₀, hψ₀⟩ := (exists_comp_picardSchemeDegreeComponentι_iff B hX hk f σ hσ φ₀ 0).mpr hφ₀
  have hfix : ψ₀ ≫ ιJ ≫ ν = φ₀ := by
    apply (picardHomEquiv B hX hk f).injective
    rw [← Category.assoc, picardHomEquiv_comp_endoPicardSchemeHom, hψ₀,
      Equiv.apply_symm_apply, endoPicardMap_zero B hX hk f Ψ hΨ σ hσ]
  obtain ⟨t₀⟩ : Nonempty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T₀) :=
    inferInstanceAs (Nonempty (Spec (.of k)))
  refine ⟨B.inclusion.map φ₀.left t₀, ⟨B.inclusion.map ψ₀.left t₀, ?_⟩, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Over.comp_left, hfix]
  · exact (range_subset_picardDegreeLocus_iff B hX hk f σ hσ φ₀ 0).mpr hφ₀ ⟨t₀, rfl⟩

/-- **The endomorphism of `Pic^0_{X/k}` induced by `Ψ`**, in the site. -/
def endoJacobianHom :
    picardSchemeDegreeComponent B hX hk f σ hσ 0 ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0 :=
  (exists_endoJacobianHom B hX hk f Ψ hΨ σ hσ).choose

/-- The endomorphism of `Pic^0_{X/k}` induced by `Ψ` is the restriction of the endomorphism
`endoPicardSchemeHom` of the Picard scheme. -/
theorem endoJacobianHom_comp_ι :
    endoJacobianHom B hX hk f Ψ hΨ σ hσ ≫ picardSchemeDegreeComponentι B hX hk f σ hσ 0 =
      picardSchemeDegreeComponentι B hX hk f σ hσ 0 ≫ endoPicardSchemeHom B hX hk f Ψ hΨ :=
  (exists_endoJacobianHom B hX hk f Ψ hΨ σ hσ).choose_spec

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- On `T`-points the endomorphism of `Pic^0_{X/k}` induced by `Ψ` is `Θ^*`. -/
theorem degreeZeroHomAddEquiv_comp_endoJacobianHom {T : BigFppfOver B (Spec (.of k)) hk}
    (x : T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0) :
    letI := jacobianGrpObj B hX hk f σ hσ
    (degreeZeroHomAddEquiv B hX hk f σ hσ T
        (Additive.ofMul (x ≫ endoJacobianHom B hX hk f Ψ hΨ σ hσ)) :
          (picardFunctor B hX hk f).obj (op T)) =
      (endoPicardMap B hX hk f Ψ hΨ).app (op T)
        (degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul x)) := by
  change picardHomEquiv B hX hk f ((x ≫ endoJacobianHom B hX hk f Ψ hΨ σ hσ) ≫
      picardSchemeDegreeComponentι B hX hk f σ hσ 0) =
    (endoPicardMap B hX hk f Ψ hΨ).app (op T)
      (picardHomEquiv B hX hk f (x ≫ picardSchemeDegreeComponentι B hX hk f σ hσ 0))
  rw [Category.assoc, endoJacobianHom_comp_ι, ← Category.assoc,
    picardHomEquiv_comp_endoPicardSchemeHom]

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- The endomorphism of `Pic^0_{X/k}` induced by `Ψ` is a homomorphism of group objects: on
points it is `Θ^*`, which is additive. -/
theorem isMonHom_endoJacobianHom :
    letI := jacobianGrpObj B hX hk f σ hσ
    IsMonHom (endoJacobianHom B hX hk f Ψ hΨ σ hσ) := by
  let := jacobianGrpObj B hX hk f σ hσ
  set F := endoJacobianHom B hX hk f Ψ hΨ σ hσ
  set N := endoPicardMap B hX hk f Ψ hΨ
  have key : ∀ {T : BigFppfOver B (Spec (.of k)) hk}
      (x y : T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0)
      (h : (N.app (op T) (degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul x)) :
          (picardFunctor B hX hk f).obj (op T)) =
        degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul y)), x ≫ F = y := by
    intro T x y h
    apply Additive.ofMul.injective
    apply (degreeZeroHomAddEquiv B hX hk f σ hσ T).injective
    apply Subtype.ext
    rwa [degreeZeroHomAddEquiv_comp_endoJacobianHom]
  constructor
  · refine key _ _ ?_
    have h1 : (η[picardSchemeDegreeComponent B hX hk f σ hσ 0] :
        𝟙_ (BigFppfOver B (Spec (.of k)) hk) ⟶ _) = 1 := by
      rw [CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [h1, ofMul_one, map_zero, ZeroMemClass.coe_zero, endoPicardMap_zero B hX hk f Ψ hΨ σ hσ]
  · have hμ : (μ[picardSchemeDegreeComponent B hX hk f σ hσ 0]) =
        fst _ _ * snd _ _ := by
      rw [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp]
    have hFF : (F ⊗ₘ F) ≫ μ[picardSchemeDegreeComponent B hX hk f σ hσ 0] =
        (fst _ _ ≫ F) * (snd _ _ ≫ F) := by
      rw [CategoryTheory.Hom.mul_def]
      congr 1
    rw [hFF]
    refine key _ _ ?_
    rw [hμ, ofMul_mul, ofMul_mul, map_add, map_add, AddSubgroup.coe_add, AddSubgroup.coe_add,
      endoPicardMap_add B hX hk f Ψ hΨ σ hσ, ← degreeZeroHomAddEquiv_comp_endoJacobianHom,
      ← degreeZeroHomAddEquiv_comp_endoJacobianHom]

/-- **The endomorphism `Ψ^*` of the Jacobian** `J = Pic^0_{X/k}` over `k` induced by pullback
along `Ψ`. -/
def jacobianPullback :
    (jacobianGrp B hX hk f σ hσ).X ⟶ (jacobianGrp B hX hk f σ hσ).X :=
  (Over.post (X := B.obj hk) B.inclusion).map (endoJacobianHom B hX hk f Ψ hΨ σ hσ)

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- The endomorphism `Ψ^*` of the Jacobian is a homomorphism. -/
instance isMonHom_jacobianPullback :
    IsMonHom (jacobianPullback B hX hk f Ψ hΨ σ hσ) := by
  have := preservesFiniteProducts_overPost_bigFppfInclusion B (Spec (.of k)) hk
  let := jacobianGrpObj B hX hk f σ hσ
  have := isMonHom_endoJacobianHom B hX hk f Ψ hΨ σ hσ
  exact Functor.map.instIsMonHom (F := Over.post (X := B.obj hk) B.inclusion)
    (f := endoJacobianHom B hX hk f Ψ hΨ σ hσ)

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- On morphisms from a test scheme, `Ψ^*` on the Jacobian is `Θ^*`. -/
theorem jacobianHomAddEquiv_comp_jacobianPullback (T : BigFppfOver B (Spec (.of k)) hk)
    (z : (Over.post (X := B.obj hk) B.inclusion).obj T ⟶
      (Over.post (X := B.obj hk) B.inclusion).obj (picardSchemeDegreeComponent B hX hk f σ hσ 0)) :
    (jacobianHomAddEquiv B hX hk f σ hσ T
        (Additive.ofMul (z ≫ (Over.post (X := B.obj hk) B.inclusion).map
          (endoJacobianHom B hX hk f Ψ hΨ σ hσ))) :
          (picardFunctor B hX hk f).obj (op T)) =
      (endoPicardMap B hX hk f Ψ hΨ).app (op T)
        (jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul z)) := by
  let hF := fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk
  have hpre : hF.preimage (z ≫ (Over.post (X := B.obj hk) B.inclusion).map
        (endoJacobianHom B hX hk f Ψ hΨ σ hσ)) =
      hF.preimage z ≫ endoJacobianHom B hX hk f Ψ hΨ σ hσ :=
    hF.map_injective (by rw [hF.map_preimage, Functor.map_comp, hF.map_preimage])
  change (degreeZeroHomAddEquiv B hX hk f σ hσ T
      (Additive.ofMul (hF.preimage (z ≫ (Over.post (X := B.obj hk) B.inclusion).map
        (endoJacobianHom B hX hk f Ψ hΨ σ hσ)))) :
        (picardFunctor B hX hk f).obj (op T)) =
    (endoPicardMap B hX hk f Ψ hΨ).app (op T)
      (degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul (hF.preimage z)))
  rw [hpre, degreeZeroHomAddEquiv_comp_endoJacobianHom]

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] [IsSepClosed k] in
/-- At `Spec k` the invertible module representing `Θ^*` of a point is `Θ^*` of the invertible
module representing it. -/
theorem picardAddEquivOfSubsingleton_symm_endoPicardMap
    (ξ : (picardFunctor B hX hk f).obj (op (fieldObj B hk k hk))) :
    (picardAddEquivOfSubsingleton B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)
        (fieldObj B hk k hk)).symm ((endoPicardMap B hX hk f Ψ hΨ).app _ ξ) =
      Stacks.Picard.schemePullbackClass
        (endoBaseChangeMap B hX hk f Ψ hΨ (fieldObj B hk k hk))
        ((picardAddEquivOfSubsingleton B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)
          (fieldObj B hk k hk)).symm ξ) := by
  set e := picardAddEquivOfSubsingleton B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)
    (fieldObj B hk k hk)
  obtain ⟨L, rfl⟩ := e.surjective ξ
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_eq]
  exact endoPicardMap_toPicardFunctor B hX hk f Ψ hΨ _ L

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- **On rational points, `Ψ^*` on the Jacobian is the pullback `Ψ^*` on `Pic^0(X)`**, read in
the model `Stacks.Picard.ofScheme` of the Picard group. -/
theorem jacobianPointsAddEquiv_comp_jacobianPullback (hdim : topologicalKrullDim X ≤ 1)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm
        (jacobianPointsAddEquiv B hX hk f σ hσ hdim
          (Additive.ofMul (x ≫ jacobianPullback B hX hk f Ψ hΨ σ hσ))).1 =
      Stacks.Picard.schemePullbackClass Ψ
        ((Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm
          (jacobianPointsAddEquiv B hX hk f σ hσ hdim (Additive.ofMul x)).1) := by
  set T₀ := fieldObj B hk k hk
  set eT := picardAddEquivOfSubsingleton B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ) T₀
  set E := jacobianPointsAddEquiv B hX hk f σ hσ hdim
  set E1 := jacobianPointsAddEquivFieldSelf B hX hk f σ hσ
  set E2 := picardDegreeZeroFieldSelfAddEquiv B hX hk f hdim
  set mX := Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
  set mK := Stacks.GluePicard.picardModelAddEquiv (baseChange B hX hk f T₀).toRingedSpace
  set fst₀ := pullback.fst (B.inclusion.map f) (B.inclusion.map T₀.hom)
  have hE2 : ∀ c, (E2 c : schemePicard _) = mK (Stacks.Picard.schemePullbackClass fst₀
      (mX.symm c.1)) := fun c => rfl
  have hE1 : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ (jacobianGrp B hX hk f σ hσ).X,
      (E1 (Additive.ofMul y) : schemePicard _) =
        mK (eT.symm (jacobianHomAddEquiv B hX hk f σ hσ T₀
          (Additive.ofMul (Stacks.Groupoids.fieldStructureHom k ≫ y)))) := fun y => rfl
  have hEE : ∀ y, E2 (E y) = E1 y := fun y => E2.apply_symm_apply (E1 y)
  have hfield : (E1 (Additive.ofMul (x ≫ jacobianPullback B hX hk f Ψ hΨ σ hσ)) :
        schemePicard _) =
      mK (Stacks.Picard.schemePullbackClass
        (endoBaseChangeMap B hX hk f Ψ hΨ T₀)
        (eT.symm (jacobianHomAddEquiv B hX hk f σ hσ T₀
          (Additive.ofMul (Stacks.Groupoids.fieldStructureHom k ≫ x))))) := by
    rw [hE1, ← picardAddEquivOfSubsingleton_symm_endoPicardMap B hX hk f Ψ hΨ σ hσ]
    congr 2
    exact jacobianHomAddEquiv_comp_jacobianPullback B hX hk f Ψ hΨ σ hσ T₀
      (Stacks.Groupoids.fieldStructureHom k ≫ x)
  have h1 := congrArg Subtype.val
    (hEE (Additive.ofMul (x ≫ jacobianPullback B hX hk f Ψ hΨ σ hσ)))
  have h2 := congrArg Subtype.val (hEE (Additive.ofMul x))
  rw [hE2, hfield] at h1
  rw [hE2, hE1] at h2
  have h3 := mK.injective h1
  have h4 := mK.injective h2
  rw [← h4, Stacks.Picard.schemePullbackClass_comp, endoBaseChangeMap_fst,
    ← Stacks.Picard.schemePullbackClass_comp] at h3
  exact (Stacks.Picard.schemePullbackClassAddEquiv (fieldSelfIso B hX hk f)).injective h3

end Jacobian

end Stacks.PicardFunctor

end
