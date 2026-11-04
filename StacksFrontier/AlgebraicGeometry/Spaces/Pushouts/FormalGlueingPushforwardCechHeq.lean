module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspacePushforwardCech
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingLocalGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingStalkQuotient

/-!
# Chartwise Čech properties of a direct image along an inclusion known up to definitional equality

The chartwise separation and glueing of `j_*ℋ` along an open subspace `W`
(`AlgebraicGeometry.Space.eq_zero_of_forall_pow_smul_eq_zero_modulePushforward_openSubspace`,
`AlgebraicGeometry.Space.cechGlueingElementary_modulePushforward_openSubspace`) are stated for the
inclusion `ObjectProperty.homMk W.ι`.  The named inclusions of a formal glueing situation
(`openImmersion`, `openImmersionOver`) are that inclusion only definitionally, and the
definitional check through the module categories exceeds the heartbeat budget; the two theorems
here take the inclusion with an equation of spaces and a `HEq`, which are discharged by `rfl` and
`HEq.rfl`, and substitute.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_forall_pow_smul_eq_zero_modulePushforward_of_heq`.
* `AlgebraicGeometry.Space.cechGlueingElementary_modulePushforward_of_heq`.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `eq_zero_of_forall_pow_smul_eq_zero_modulePushforward_openSubspace` for an inclusion known
only up to the definitional identification with the inclusion of `W`. -/
theorem eq_zero_of_forall_pow_smul_eq_zero_modulePushforward_of_heq {X : AlgebraicSpaces B S hS}
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W) {U : AlgebraicSpaces B S hS} (j : U ⟶ X)
    (hU : U = ⟨W.toFunctor, hW.1⟩)
    (hj : HEq j (ObjectProperty.homMk W.ι : (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X))
    (H : Modules.{u, u} B S hS U.1 U.2)
    (M : SmallEtale B S hS X.1) (hM : IsAffine (chartScheme M))
    {r : ℕ} (g : Fin r → chartRing B S hS X.1 X.2 M)
    (hcov : ∀ x : chartScheme M, chartPointsMap M x ∈
      Set.range (pointsMap B S hS W.toFunctor W.ι) → ∃ i, x ∈ (chartScheme M).basicOpen (g i))
    (s : ((modulePushforward B S hS j).obj H).val.obj (op M))
    (hs : ∀ i, ∃ k : ℕ, g i ^ k • s = 0) : s = 0 := by
  subst hU
  cases eq_of_heq hj
  exact eq_zero_of_forall_pow_smul_eq_zero_modulePushforward_openSubspace X W hW H M hM g
    hcov s hs

/-- `cechGlueingElementary_modulePushforward_openSubspace` for an inclusion known only up to the
definitional identification with the inclusion of `W`. -/
theorem cechGlueingElementary_modulePushforward_of_heq {X : AlgebraicSpaces B S hS}
    (W : Subfunctor X.1) (hW : IsOpenSubspace B S hS W) {U : AlgebraicSpaces B S hS} (j : U ⟶ X)
    (hU : U = ⟨W.toFunctor, hW.1⟩)
    (hj : HEq j (ObjectProperty.homMk W.ι : (⟨W.toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶ X))
    (H : Modules.{u, u} B S hS U.1 U.2)
    (hF : ((modulePushforward B S hS j).obj H).IsQuasicoherentOnSite)
    (M : SmallEtale B S hS X.1) (hM : IsAffine (chartScheme M))
    {r : ℕ} (g : Fin r → chartRing B S hS X.1 X.2 M)
    (hcov : ∀ x : chartScheme M, chartPointsMap M x ∈
      Set.range (pointsMap B S hS W.toFunctor W.ι) → ∃ i, x ∈ (chartScheme M).basicOpen (g i)) :
    FormalGlueing.CechGlueingElementary g
      (((modulePushforward B S hS j).obj H).val.obj (op M)) := by
  subst hU
  cases eq_of_heq hj
  exact cechGlueingElementary_modulePushforward_openSubspace X W hW H hF M hM g hcov

end AlgebraicGeometry.Space

end
