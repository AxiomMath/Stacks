module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeZeroSubgroup
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicardBasePoints
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement

/-!
# The rational points of the degree components of the Picard scheme of a curve

Let `X` be a smooth projective geometrically irreducible curve over a field `k` with a rational
point, whose Picard functor is representable. A `k`-point `p` of `Pic_{X/k}` corresponds to a
class `L ∈ Pic(X)` (`Stacks.PicardFunctor.picardPointsEquiv`), and the fibre degree of the point
of `Pic_{X/k}(Spec k)` classified by `p` is the degree of `L`
(`Stacks.PicardFunctor.curveFibreDegree_picardHomEquiv_eq_picardDegree`). Hence `p` lands in
`Pic^d_{X/k}` exactly when `deg L = d`: this discharges the hypothesis `hdeg` of
`Stacks.PicardFunctor.degreePointsEquiv` for the degree components `Pic^d_{X/k}`
(`Stacks.PicardFunctor.exists_comp_picardDegreeComponentι_iff_picardDegree`).

For the degree-zero component, the group of `k`-points of the group scheme `Pic⁰_{X/k}` is
isomorphic, as a group, to `Pic⁰(X)`: `Stacks.PicardFunctor.picardDegreeZeroPointsMulEquiv`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u

namespace Stacks.PicardCurve

/-- **The fibre rank of a Picard class of a scheme over a field** is the dimension of the
cohomology of its representative. -/
theorem classFibreRank_eq_finrank {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (L : Stacks.Picard.ofScheme X) (t : Spec (.of k)) (n : ℕ) :
    classFibreRank f L t n = Module.finrank k (cohomologyOverField k f (rep L) n) := by
  obtain rfl : t = (𝟙 (Spec (.of k)) : Spec (.of k) ⟶ Spec (.of k)) (IsLocalRing.closedPoint k) :=
    Subsingleton.elim _ _
  have hφ := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k (Spec (.of k))
    (𝟙 (Spec (.of k)))
  have hsq : IsPullback (𝟙 X) f f (Spec.map (Scheme.descResidueField
      (Scheme.stalkClosedPointTo (𝟙 (Spec (.of k))))) ≫ (Spec (.of k)).fromSpecResidueField
        ((𝟙 (Spec (.of k)) : Spec (.of k) ⟶ Spec (.of k)) (IsLocalRing.closedPoint k))) := by
    rw [hφ]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact (Stacks.FibreCohomology.finrank_eq_of_isPullback f (rep L) _ _ (𝟙 X) f hsq (rep L)
    ((Scheme.Modules.pullbackId X).app (rep L)).symm n).symm

end Stacks.PicardCurve

namespace Stacks.PicardFunctor

open Stacks.PicardCurve

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]

omit [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)] in
/-- The base change of `X` along the base object is identified with `X` compatibly with the
projections. -/
theorem isPullback_baseChangeBaseOverIso :
    IsPullback (baseChangeBaseOverIso B hX hk f).hom (B.inclusion.map f)
      (baseChangeProj B hX hk f (baseOver B hk)) (𝟙 _) :=
  IsPullback.of_horiz_isIso ⟨by
    simp [baseChangeBaseOverIso, pullbackRightIdIso, baseChangeProj]⟩

/-- **The fibre degree of a point of `Pic_{X/k}(Spec k)` is the degree of the corresponding
invertible module.** -/
theorem curveFibreDegree_picardBaseAddEquiv_eq_picardDegree (L : Stacks.Picard.ofScheme X)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (baseOver B hk)) :
    curveFibreDegree B hX hk f σ hσ (baseOver B hk)
        (picardBaseAddEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) L) t =
      picardDegree k (B.inclusion.map f) (topologicalKrullDim_le_one_of_isCurve B hX hk f)
        (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace L) := by
  show fibreDegree B hX hk f σ hσ _ _ (toPicardFunctorHom B hX hk f (baseOver B hk)
    (picardAtBaseOverAddEquiv B hX hk f L)) t = _
  rw [fibreDegree_toPicardFunctorHom, fibreClassDegree_eq]
  have hq := isPullback_baseChangeBaseOverIso B hX hk f
  have hL : Stacks.Picard.schemePullbackClass (baseChangeBaseOverIso B hX hk f).hom
      (picardAtBaseOverAddEquiv B hX hk f L) = L := by
    show Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _ L) = L
    rw [Stacks.Picard.schemePullbackClass_comp, Iso.hom_inv_id,
      Stacks.Picard.schemePullbackClass_id]
  have h0 : Stacks.Picard.schemePullbackClass (baseChangeBaseOverIso B hX hk f).hom
      (0 : picardAt B hX hk f (baseOver B hk)) = 0 :=
    map_zero (Stacks.Picard.schemePullbackClassHom _)
  have e : ∀ (x : picardAt B hX hk f (baseOver B hk)) (n : ℕ),
      classFibreRank (B.inclusion.map f)
          (Stacks.Picard.schemePullbackClass (baseChangeBaseOverIso B hX hk f).hom x) t n =
        classFibreRank (baseChangeProj B hX hk f (baseOver B hk)) x t n := fun x n =>
    classFibreRank_schemePullbackClass (baseChangeProj B hX hk f (baseOver B hk))
      _ (B.inclusion.map f) (𝟙 _) hq x t n
  simp only [← e, hL, h0, classFibreRank_eq_finrank]
  exact (classDegree_eq_euler_sub k (B.inclusion.map f) L).symm

section Representable

variable [(picardFunctor B hX hk f).IsRepresentable]

/-- **The fibre degree of the point classified by a `k`-point `p` of the Picard scheme is the
degree of the invertible module corresponding to `p`.** -/
theorem curveFibreDegree_picardHomEquiv_eq_picardDegree
    (p : baseOver B hk ⟶ picardSchemeOver B hX hk f)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (baseOver B hk)) :
    curveFibreDegree B hX hk f σ hσ (baseOver B hk) (picardHomEquiv B hX hk f p) t =
      picardDegree k (B.inclusion.map f) (topologicalKrullDim_le_one_of_isCurve B hX hk f)
        (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
          (picardPointsEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
            p)) := by
  rw [← curveFibreDegree_picardBaseAddEquiv_eq_picardDegree B hX hk f σ hσ _ t]
  congr 1
  exact ((picardBaseAddEquiv B hX hk f σ hσ _).apply_symm_apply _).symm

/-- **The hypothesis `hdeg` of `Stacks.PicardFunctor.degreePointsEquiv`, discharged**: a `k`-point
of the Picard scheme factors through `Pic^d_{X/k}` exactly when the corresponding invertible
module has degree `d`. -/
theorem exists_comp_picardDegreeComponentι_iff_picardDegree (d : ℤ)
    (p : baseOver B hk ⟶ picardSchemeOver B hX hk f) :
    (∃ q : baseOver B hk ⟶ picardSchemeDegreeComponent B hX hk f σ hσ d,
        q ≫ picardSchemeDegreeComponentι B hX hk f σ hσ d = p) ↔
      picardDegree k (B.inclusion.map f) (topologicalKrullDim_le_one_of_isCurve B hX hk f)
        (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
          (picardPointsEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) p)) =
        d := by
  rw [exists_comp_picardSchemeDegreeComponentι_iff]
  simp only [curveFibreDegree_picardHomEquiv_eq_picardDegree]
  exact ⟨fun h => h (IsLocalRing.closedPoint k), fun h _ => h⟩

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- The fibre degree of a point of `Pic_{X/k}(Spec k)` is the degree of the corresponding class
of `Pic(X)`. -/
theorem curveFibreDegree_baseOver_eq (ξ : (picardFunctor B hX hk f).obj (op (baseOver B hk)))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (baseOver B hk)) :
    curveFibreDegree B hX hk f σ hσ (baseOver B hk) ξ t =
      picardDegree k (B.inclusion.map f) (topologicalKrullDim_le_one_of_isCurve B hX hk f)
        (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
          ((picardBaseAddEquiv B hX hk f σ hσ
            (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)).symm ξ)) := by
  rw [← curveFibreDegree_picardBaseAddEquiv_eq_picardDegree B hX hk f σ hσ _ t,
    AddEquiv.apply_symm_apply]

/-- **The degree-zero points of `Pic_{X/k}(Spec k)` are `Pic⁰(X)`.** -/
def degreeZeroBaseAddEquiv :
    fibreDegreeZeroAddSubgroup B hX hk f σ hσ (baseOver B hk) ≃+
      picardDegreeZero k (B.inclusion.map f) (topologicalKrullDim_le_one_of_isCurve B hX hk f) where
  toFun ξ := ⟨Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
      ((picardBaseAddEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)).symm
        ξ.1), by
    rw [mem_picardDegreeZero_iff, ← curveFibreDegree_baseOver_eq B hX hk f σ hσ ξ.1
      (IsLocalRing.closedPoint k)]
    exact ξ.2 _⟩
  invFun y := ⟨picardBaseAddEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
      ((Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm y.1), fun t => by
    rw [curveFibreDegree_baseOver_eq, AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv ξ := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_add' ξ ζ := Subtype.ext
    (((Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).toAddMonoidHom.comp
      (picardBaseAddEquiv B hX hk f σ hσ
        (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)).symm.toAddMonoidHom).map_add ξ.1 ζ.1)

/-- The isomorphism of the terminal object of schemes over `k` with the image of the base
object of the site. -/
def tensorUnitIsoOverPostBaseOver :
    (Over.post (X := B.obj hk) B.inclusion).obj (baseOver B hk) ≅
      𝟙_ (Over (B.inclusion.obj (B.obj hk))) :=
  haveI := preservesTerminal_overPost_bigFppfInclusion B (Spec (.of k)) hk
  ((isTerminalBaseOver B hk).isTerminalObj (Over.post (X := B.obj hk) B.inclusion)).uniqueUpToIso
    isTerminalTensorUnit

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- The group of `k`-points of `Pic⁰_{X/k}` in the big fppf site is the group of degree-zero
points of `Pic_{X/k}(Spec k)`. -/
def degreeZeroSitePointsMulEquiv :
    letI := degreeZeroGrpObj B hX hk f σ hσ
    (baseOver B hk ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0) ≃*
      Multiplicative (fibreDegreeZeroAddSubgroup B hX hk f σ hσ (baseOver B hk)) :=
  letI := degreeZeroGrpObj B hX hk f σ hσ
  { toFun := (degreeZeroRepresentableBy B hX hk f σ hσ).homEquiv'
    invFun := (degreeZeroRepresentableBy B hX hk f σ hσ).homEquiv'.symm
    left_inv := (degreeZeroRepresentableBy B hX hk f σ hσ).homEquiv'.left_inv
    right_inv := (degreeZeroRepresentableBy B hX hk f σ hσ).homEquiv'.right_inv
    map_mul' a b := homEquiv'_mul_ofRepresentableBy _ _ a b }

/-- The underlying scheme over `k` of `Pic⁰_{X/k}` is the image of the degree-zero component. -/
theorem picardDegreeZeroSubgroup_carrier_X :
    (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X =
      (Over.post (X := B.obj hk) B.inclusion).obj (picardSchemeDegreeComponent B hX hk f σ hσ 0) :=
  rfl

/-- **The group of `k`-points of the group scheme `Pic⁰_{X/k}` is `Pic⁰(X)`**: the `k`-points of
`Pic⁰_{X/k}` over `k` are its `k`-points in the big fppf site, which are the degree-zero points of
`Pic_{X/k}(Spec k)`, which are the classes of degree zero in `Pic(X)`. -/
def picardDegreeZeroPointsMulEquiv :
    (𝟙_ (Over (B.inclusion.obj (B.obj hk))) ⟶
        (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X) ≃*
      Multiplicative
        (picardDegreeZero k (B.inclusion.map f)
          (topologicalKrullDim_le_one_of_isCurve B hX hk f)) := by
  letI : CartesianMonoidalCategory (BigFppfOver B (Spec (.of k)) hk) := .ofHasFiniteProducts
  haveI := preservesFiniteProducts_overPost_bigFppfInclusion B (Spec (.of k)) hk
  letI : (Over.post (X := B.obj hk) B.inclusion).Monoidal := .ofChosenFiniteProducts _
  letI := degreeZeroGrpObj B hX hk f σ hσ
  let i := tensorUnitIsoOverPostBaseOver B hk
  let e₁ : (𝟙_ (Over (B.inclusion.obj (B.obj hk))) ⟶
      (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X) ≃*
      ((Over.post (X := B.obj hk) B.inclusion).obj (baseOver B hk) ⟶
        (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X) :=
    { toFun := fun a => i.hom ≫ a
      invFun := fun b => i.inv ≫ b
      left_inv := fun a => by simp
      right_inv := fun b => by simp
      map_mul' := fun a b => MonObj.comp_mul _ _ _ }
  let e₂ := ((fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).homMulEquiv
    (X := baseOver B hk) (M := picardSchemeDegreeComponent B hX hk f σ hσ 0)).symm
  exact e₁.trans (e₂.trans ((degreeZeroSitePointsMulEquiv B hX hk f σ hσ).trans
    (degreeZeroBaseAddEquiv B hX hk f σ hσ).toMultiplicative))

/-- **The `k`-points of `Pic⁰_{X/k}` are the classes of degree zero in `Pic(X)`**, as the map
`φ` that the consumers of [Stacks, Tag 0BA0] in [Stacks, Tag 03RQ] and [Stacks, Tag 03RR]
take. -/
def picardDegreeZeroPoints
    (a : 𝟙_ (Over (B.inclusion.obj (B.obj hk))) ⟶
      (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X) :
    picardDegreeZero k (B.inclusion.map f) (topologicalKrullDim_le_one_of_isCurve B hX hk f) :=
  Multiplicative.toAdd (picardDegreeZeroPointsMulEquiv B hX hk f σ hσ a)

/-- The identification of the `k`-points of `Pic⁰_{X/k}` with `Pic⁰(X)` turns the group law of
the group scheme into addition of classes. -/
theorem picardDegreeZeroPoints_mul
    (a b : 𝟙_ (Over (B.inclusion.obj (B.obj hk))) ⟶
      (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X) :
    picardDegreeZeroPoints B hX hk f σ hσ (a * b) =
      picardDegreeZeroPoints B hX hk f σ hσ a + picardDegreeZeroPoints B hX hk f σ hσ b := by
  simp only [picardDegreeZeroPoints, map_mul, toAdd_mul]

/-- **The identification of the `k`-points of `Pic⁰_{X/k}` with `Pic⁰(X)` is bijective.** -/
theorem bijective_picardDegreeZeroPoints :
    Function.Bijective (picardDegreeZeroPoints B hX hk f σ hσ) :=
  Multiplicative.toAdd.bijective.comp (picardDegreeZeroPointsMulEquiv B hX hk f σ hσ).bijective

end Representable

end Stacks.PicardFunctor
