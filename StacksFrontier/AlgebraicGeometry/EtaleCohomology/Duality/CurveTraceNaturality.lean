module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PicardDegreeZeroDivisible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityPullbackDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.MultiplicativeFirstCohomologyNaturality

/-!
# The trace map `H²(X, μ_n) ≅ ℤ/n` of a curve under pullback

Let `X` be a smooth proper curve over an algebraically closed field `k` and `n` invertible in
`k`. The trace map `tr_X : H²(X, μ_n) ≅ ℤ/n` is the Kummer isomorphism `H²(X, μ_n) ≅ Pic(X)/n`
followed by the degree mod `n` (`Stacks.Kummer.smoothProperCurveTrace`).

For a morphism `π : X ⟶ Y` of such curves (over possibly different fields, and not necessarily
over a common base) whose pullback on line bundles multiplies degrees by `c`,
`tr_X(π^* y) = c · tr_Y(y)` for `y ∈ H²(Y, μ_n)`
(`Stacks.Kummer.smoothProperCurveTrace_rootsOfUnityPullbackMap`).

## Main definitions

* `Stacks.Kummer.smoothProperCurveTrace`: `tr_X : H²(X, μ_n) ≃+ ℤ/n`.

## Main results

* `Stacks.Kummer.smoothProperCurveTrace_kummerδ`: `tr_X(δ x) = deg [x] mod n`.
* `Stacks.Kummer.smoothProperCurveTrace_rootsOfUnityPullbackMap`: the pullback formula.

## References

* [Stacks Project, Tag 0AMB](https://stacks.math.columbia.edu/tag/0AMB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Kummer

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

section General

variable (X : Scheme.{u}) {n : ℕ} (hn0 : n ≠ 0) (hX : IsUnit ((n : ℕ) : Γ(X, ⊤)))
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **`H²(X, μ_n) ≅ Pic(X)/n` sends a Kummer coboundary `δ x` to the class of `[x]`.** -/
theorem h2RootsOfUnityAddEquivPicardQuotient_kummerδ
    (h2 : Subsingleton (Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} X) 2))
    (x : Sheaf.H.{u + 1} (multiplicativeSheaf.{u, u + 1} X) 1) :
    h2RootsOfUnityAddEquivPicardQuotient.{u + 1, u + 1, u} X hn0 hX h2 (kummerδ X hn0 hX 1 x) =
      QuotientAddGroup.mk (etaleH1MultiplicativeAddEquivPicard.{u + 1, u + 1, u} X x) := by
  unfold h2RootsOfUnityAddEquivPicardQuotient
  rw [AddEquiv.trans_apply]
  have hq : (QuotientAddGroup.quotientKerEquivOfSurjective (kummerδ X hn0 hX 1)
      (surjective_kummerδ_one X hn0 hX h2)).symm (kummerδ X hn0 hX 1 x) =
      QuotientAddGroup.mk x := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  rw [hq]
  rfl

end General

section Trace

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f] {n : ℕ} (hn : IsUnit (n : k))

/-- **The trace map `H²(X, μ_n) ≅ ℤ/n` of a smooth proper curve** over an algebraically closed
field, `n` invertible in the field: the Kummer isomorphism `H²(X, μ_n) ≅ Pic(X)/n` followed by
the degree mod `n`. -/
def smoothProperCurveTrace :
    Sheaf.H.{u + 1, u + 1} (rootsOfUnitySheaf.{u, u + 1} X n) 2 ≃+ ZMod n :=
  curveTrace f hn _ (Picard.picardDegree_surjective f)
    (fun L hL => Picard.exists_nsmul_eq_of_picardDegree_eq_zero f _ hn L hL)

include hn in
omit [IsAlgClosed k] in
/-- A natural number invertible in a field is nonzero. -/
theorem neZero_of_isUnit : n ≠ 0 := by
  rintro rfl
  simp at hn

include f hn in
omit [IsAlgClosed k] [IsCurve k f] [Smooth f] [IsProper f] in
/-- A natural number invertible in `k` is invertible in the global sections of a `k`-scheme. -/
theorem isUnit_globalSections : IsUnit ((n : ℕ) : Γ(X, ⊤)) :=
  isUnit_natCast_globalSections X n f hn

/-- **The trace of a Kummer coboundary is the degree**: `tr_X(δ x) = deg [x] mod n` for
`x ∈ H¹(X, 𝐆_m)`, with `[x] ∈ Pic(X)` its class by Tag 03P8. -/
theorem smoothProperCurveTrace_kummerδ
    (x : Sheaf.H.{u + 1, u + 1} (multiplicativeSheaf.{u, u + 1} X) 1) :
    smoothProperCurveTrace f hn
        (kummerδ.{u + 1, u, u + 1} X (neZero_of_isUnit hn) (isUnit_globalSections f hn) 1 x) =
      (Picard.picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
        (etaleH1MultiplicativeAddEquivPicard.{u + 1, u + 1, u} X x) : ZMod n) := by
  unfold smoothProperCurveTrace curveTrace h2RootsOfUnityAddEquivPicardQuotient_of_smoothCurve
  rw [AddEquiv.trans_apply, h2RootsOfUnityAddEquivPicardQuotient_kummerδ,
    quotientNsmulAddEquivZModOfSurjective_mk]

end Trace

section Pullback

variable {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] {X Y : Scheme.{u}}
  (fX : X ⟶ Spec (.of k)) [IsCurve k fX] [Smooth fX] [IsProper fX]
  (fY : Y ⟶ Spec (.of k')) [IsCurve k' fY] [Smooth fY] [IsProper fY] {n : ℕ}
  (hnX : IsUnit (n : k)) (hnY : IsUnit (n : k'))

/-- **The trace under pullback.** For a morphism `π : X ⟶ Y` of smooth proper curves over
algebraically closed fields whose pullback on line bundles multiplies degrees by `c`,
`tr_X(π^* y) = c · tr_Y(y)` for `y ∈ H²(Y, μ_n)`. -/
theorem smoothProperCurveTrace_rootsOfUnityPullbackMap (π : X ⟶ Y) (c : ℤ)
    (hdeg : ∀ L : Picard.ofScheme Y,
      Picard.picardDegree fX (IsCurve.topologicalKrullDim_eq_one (f := fX)).le
          (Picard.schemePullbackClassHom π L) =
        c * Picard.picardDegree fY (IsCurve.topologicalKrullDim_eq_one (f := fY)).le L)
    (y : Sheaf.H.{u + 1, u + 1} (rootsOfUnitySheaf.{u, u + 1} Y n) 2) :
    smoothProperCurveTrace fX hnX
        (Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} π n 2 y) =
      c • smoothProperCurveTrace fY hnY y := by
  obtain ⟨x, rfl⟩ := surjective_kummerδ_one Y (neZero_of_isUnit hnY) (isUnit_globalSections fY hnY)
    (Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve fY 2 le_rfl) y
  have hX := isUnit_globalSections fX hnX
  have hsq := Stacks.Kummer.etaleCohomologyRestrictionMap_kummerExtClass.{u, u + 1, u + 1} π
    (neZero_of_isUnit hnY) (isUnit_globalSections fY hnY) 1 2 rfl x
  have h1 : Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} π n 2
      (kummerδ.{u + 1, u, u + 1} Y (neZero_of_isUnit hnY) (isUnit_globalSections fY hnY) 1 x) =
      kummerδ.{u + 1, u, u + 1} X (neZero_of_isUnit hnX) hX 1
        (Sheaf.H.map (multiplicativeInverseImageComparison.{u, u + 1} π) 1
          (Stacks.EtaleCohomology.etaleCohomologyRestrictionMap.{u, u + 1, u + 1} π _ 1 x)) :=
    hsq
  rw [h1, smoothProperCurveTrace_kummerδ, smoothProperCurveTrace_kummerδ,
    etaleH1MultiplicativeAddEquivPicard_naturality, hdeg, zsmul_eq_mul]
  push_cast
  ring

end Pullback

end Stacks.Kummer

end
