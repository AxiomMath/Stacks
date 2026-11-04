module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Jacobian
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.FieldPoints

/-!
# Degree-zero points of the Picard functor over a field

For a field extension `K/k` with `Spec K` in the site, the degree-zero points of the Picard
functor of a pointed smooth projective curve `X` at `Spec K` are the degree-zero Picard group
`Pic^0(X_K)` (`AlgebraicGeometry.picardDegreeZero`) of the base change `X_K`: the
sheafification unit is bijective at `Spec K` (`Pic(Spec K) = 0`), and the fibre degree at the
point of `Spec K` is the degree on `X_K`.

## Main results

* `Stacks.PicardFunctor.degreeZeroFieldAddEquiv`: the degree-zero points of the Picard functor
  at `Spec K` are additively equivalent to `Pic^0(X_K)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  [(picardFunctor B hX hk f).IsRepresentable]
  (K : Type u) [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K)))

/-- The Picard group of `Spec K`, regarded as an object of the site over `Spec k`, is trivial. -/
instance subsingleton_picardAt_fieldObj :
    Subsingleton (Stacks.Picard.ofScheme
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (fieldObj B hk K hK))) :=
  AlgebraicGeometry.subsingleton_picardGroup_spec_field K

/-- `Pic_{X/k}(Spec K) ≅ Pic(X_K)`, in the spelling of `AlgebraicGeometry.picardDegree`. -/
def picardFieldAddEquiv :
    (picardFunctor B hX hk f).obj (op (fieldObj B hk K hK)) ≃+
      schemePicard (baseChange B hX hk f (fieldObj B hk K hK)) :=
  (picardAddEquivOfSubsingleton B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)
    (fieldObj B hk K hK)).symm.trans
    (Stacks.GluePicard.picardModelAddEquiv
      (baseChange B hX hk f (fieldObj B hk K hK)).toRingedSpace)

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- The fibre degree of a point `ξ` of the Picard functor at `Spec K` equals the degree on `X_K` of
the corresponding line bundle under `picardFieldAddEquiv`. -/
theorem curveFibreDegree_fieldObj (ξ : (picardFunctor B hX hk f).obj (op (fieldObj B hk K hK)))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (fieldObj B hk K hK)) :
    curveFibreDegree B hX hk f σ hσ (fieldObj B hk K hK) ξ t =
      picardDegree K (fieldCurve B hX hk f K hK) (topologicalKrullDim_fieldCurve_le B hX hk f K hK)
        (picardFieldAddEquiv B hX hk f σ hσ K hK ξ) := by
  obtain ⟨x, rfl⟩ := (bijective_toPicardFunctorHom_of_subsingleton B hX hk f σ hσ
    (isIso_c_of_isCurve B hX hk f σ hσ) (fieldObj B hk K hK)).2 ξ
  have hx : (picardAddEquivOfSubsingleton B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)
      (fieldObj B hk K hK)).symm (toPicardFunctorHom B hX hk f (fieldObj B hk K hK) x) = x :=
    (picardAddEquivOfSubsingleton B hX hk f σ hσ _ (fieldObj B hk K hK)).symm_apply_apply x
  simp only [picardFieldAddEquiv, AddEquiv.trans_apply, hx]
  exact fibreDegree_fieldObj B hX hk f σ hσ _ K hK x t

/-- **The degree-zero points of the Picard functor at `Spec K` are `Pic^0(X_K)`.** -/
def degreeZeroFieldAddEquiv :
    degreeZeroAddSubgroup B hX hk f σ hσ (fieldObj B hk K hK) ≃+
      picardDegreeZero K (fieldCurve B hX hk f K hK)
        (topologicalKrullDim_fieldCurve_le B hX hk f K hK) where
  toFun ξ := ⟨picardFieldAddEquiv B hX hk f σ hσ K hK ξ.1, by
    have hne : Nonempty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (fieldObj B hk K hK)) :=
      inferInstanceAs (Nonempty (Spec (.of K)))
    exact (curveFibreDegree_fieldObj B hX hk f σ hσ K hK ξ.1 hne.some).symm.trans
      (ξ.2 hne.some)⟩
  invFun y := ⟨(picardFieldAddEquiv B hX hk f σ hσ K hK).symm y.1, fun t => by
    change curveFibreDegree B hX hk f σ hσ (fieldObj B hk K hK)
      ((picardFieldAddEquiv B hX hk f σ hσ K hK).symm y.1) t = 0
    rw [curveFibreDegree_fieldObj, AddEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv ξ := Subtype.ext (AddEquiv.symm_apply_apply _ _)
  right_inv y := Subtype.ext (AddEquiv.apply_symm_apply _ _)
  map_add' ξ η := Subtype.ext (map_add (picardFieldAddEquiv B hX hk f σ hσ K hK) ξ.1 η.1)

end Stacks.PicardFunctor

end
