module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicardBasePoints
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.FibreDegreeAdd

/-!
# The Picard functor of a curve at a test scheme with trivial Picard group

Let `X` be a proper scheme over a field `k` with a rational point, satisfying the hypothesis of
[Stacks, Tag 0B9N]. At every test scheme `T` with `Pic(T) = 0` — for instance the spectrum of a
field ([Stacks, Tag 03QV]) — the fppf sheafification unit `Pic(X_T) ⟶ Pic_{X/k}(T)` is bijective:
it is surjective by [Stacks, Tag 0B9N], and its kernel is the image of `Pic(T)` by exactness in
the middle of the same sequence. This generalizes
`Stacks.PicardFunctor.bijective_toPicardFunctorHom_baseOver` from the base to every such `T`.

## Main results

* `Stacks.PicardFunctor.bijective_toPicardFunctorHom_of_subsingleton`: if `Pic(T) = 0`, then
  `Pic(X_T) ⟶ Pic_{X/k}(T)` is bijective.
* `Stacks.PicardFunctor.picardAddEquivOfSubsingleton`: `Pic(X_T) ≅ Pic_{X/k}(T)`.
* `Stacks.PicardFunctor.fibreDegree_fieldObj`: for a field extension `K/k`, the fibre degree of a
  class on `X_K` is its degree on the curve `X_K` over `K`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
    IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c)
  (T : BigFppfOver B (Spec (.of k)) hk)
  [Subsingleton (Stacks.Picard.ofScheme ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T))]

include σ hσ hOiso in
/-- **At a test scheme with trivial Picard group the sheafification unit of the relative Picard
presheaf is bijective.** -/
theorem bijective_toPicardFunctorHom_of_subsingleton :
    Function.Bijective (toPicardFunctorHom B hX hk f T) := by
  refine ⟨fun a b hab => ?_, surjective_toPicardFunctorHom B hX hk f σ hσ hOiso T⟩
  have hz : toPicardFunctorHom B hX hk f T (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨N, hN⟩ := (exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom
    B hX hk f σ hσ hOiso T (a - b)).1 hz
  rw [Subsingleton.elim N 0] at hN
  rw [← sub_eq_zero, ← hN]
  exact map_zero (Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hk f T))

include σ hσ hOiso in
/-- **`Pic(X_T) ≅ Pic_{X/k}(T)` at a test scheme `T` with trivial Picard group.** -/
def picardAddEquivOfSubsingleton :
    picardAt B hX hk f T ≃+ (picardFunctor B hX hk f).obj (op T) :=
  { Equiv.ofBijective _ (bijective_toPicardFunctorHom_of_subsingleton B hX hk f σ hσ hOiso T) with
    map_add' := map_add (toPicardFunctorHom B hX hk f T) }

/-! ### Points over a field: the fibre degree is the degree on `X_K` -/

section Field

omit [Subsingleton (Stacks.Picard.ofScheme ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T))]

variable [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  (K : Type u) [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K)))

/-- **The test scheme `Spec K`** of the site, for a field extension `K/k`. -/
abbrev fieldObj : BigFppfOver B (Spec (.of k)) hk :=
  Over.mk (ObjectProperty.homMk (X := B.obj hK) (Y := B.obj hk)
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))

/-- The base change `X_K ⟶ Spec K`. -/
abbrev fieldCurve : baseChange B hX hk f (fieldObj B hk K hK) ⟶ Spec (.of K) :=
  baseChangeProj B hX hk f (fieldObj B hk K hK)

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)] in
/-- `X_K` is the pullback of `X ⟶ Spec k` along `Spec K ⟶ Spec k`. -/
theorem isPullback_fieldCurve : IsPullback
    (pullback.fst (B.inclusion.map f) (B.inclusion.map (fieldObj B hk K hK).hom))
    (fieldCurve B hX hk f K hK) (B.inclusion.map f)
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  IsPullback.of_hasPullback _ _

/-- **`X_K` is a proper curve over `K`.** -/
theorem isCurve_fieldCurve : IsProper (fieldCurve B hX hk f K hK) ∧
    IsCurve K (fieldCurve B hX hk f K hK) := by
  have hZ := isPullback_fieldCurve B hX hk f K hK
  have hP : IsProper (fieldCurve B hX hk f K hK) := Stacks.AbelMap.isProper_of_isPullback _ _ _ hZ
  have hI := Stacks.AbelMap.isIntegral_of_isPullback _ _ _ hZ
  have hd := Stacks.AbelMap.topologicalKrullDim_eq_one_of_isPullback _ _ _ hZ
  exact ⟨hP, { toIsIntegral := hI, topologicalKrullDim_eq_one := hd }⟩

/-- `X_K ⟶ Spec K` is proper. -/
instance isProper_fieldCurve : IsProper (fieldCurve B hX hk f K hK) :=
  (isCurve_fieldCurve B hX hk f K hK).1

/-- `X_K` is a curve over `K`. -/
instance isCurve_fieldCurve' : IsCurve K (fieldCurve B hX hk f K hK) :=
  (isCurve_fieldCurve B hX hk f K hK).2

/-- The topological Krull dimension of `X_K` is at most `1`. -/
theorem topologicalKrullDim_fieldCurve_le :
    topologicalKrullDim (baseChange B hX hk f (fieldObj B hk K hK)) ≤ 1 := by
  rw [(isCurve_fieldCurve B hX hk f K hK).2.topologicalKrullDim_eq_one]

/-- **The fibre degree of a class on `X_K` at the point of `Spec K` is its degree on the curve
`X_K` over `K`.** -/
theorem fibreDegree_fieldObj (x : picardAt B hX hk f (fieldObj B hk K hK))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (fieldObj B hk K hK)) :
    fibreDegree B hX hk f σ hσ hOiso (fieldObj B hk K hK)
        (toPicardFunctorHom B hX hk f (fieldObj B hk K hK) x) t =
      picardDegree K (fieldCurve B hX hk f K hK) (topologicalKrullDim_fieldCurve_le B hX hk f K hK)
        (Stacks.GluePicard.picardModelAddEquiv
          (baseChange B hX hk f (fieldObj B hk K hK)).toRingedSpace x) := by
  obtain ⟨hP, hC⟩ := isCurve_fieldCurve B hX hk f K hK
  have he : ∀ y : picardAt B hX hk f (fieldObj B hk K hK),
      fibreEuler B hX hk f σ hσ hOiso (fieldObj B hk K hK)
        (toPicardFunctorHom B hX hk f (fieldObj B hk K hK) y) t =
      Stacks.PicardCurve.classEuler (fieldCurve B hX hk f K hK) y := fun y => by
    rw [fibreEuler, fibreRank_toPicardFunctorHom, fibreRank_toPicardFunctorHom]
    exact congrArg₂ (fun a b : ℕ => (a : ℤ) - b)
      (@Stacks.AbelMap.finrank_cohomologyOverField_eq_fibreCohomology _ _ _ _ hP _ _ t 0).symm
      (@Stacks.AbelMap.finrank_cohomologyOverField_eq_fibreCohomology _ _ _ _ hP _ _ t 1).symm
  have hd := @Stacks.PicardCurve.classEuler_sub_eq_picardDegree _ _ _ _ hP hC
    (topologicalKrullDim_fieldCurve_le B hX hk f K hK)
  have h1 := hd x
  have h0 := hd 0
  rw [map_zero, map_zero] at h0
  rw [fibreDegree, ← (toPicardFunctorHom B hX hk f (fieldObj B hk K hK)).map_zero, he, he]
  omega

end Field

end Stacks.PicardFunctor

end
