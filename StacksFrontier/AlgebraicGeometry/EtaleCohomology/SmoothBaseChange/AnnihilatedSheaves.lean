module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AffineLineVanishing

/-!
# Smooth base change for sheaves annihilated by an invertible integer

The smooth base change theorem (Stacks, Theorem 0EYU) for an abelian sheaf annihilated by an
integer `n` invertible on the base: in a cartesian square with `f` smooth and `g` quasi-compact
and quasi-separated, the base change map `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism. This
is the condition `BC(f, n, q)` of Stacks, Remark 0F02 at the trivial base change of `S`.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.isIso_higherBaseChangeMapAb_of_smooth_of_zsmul_eq_zero`

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

/-- **Smooth base change for a sheaf annihilated by an invertible integer.** In a cartesian square
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
with `f` smooth and `g` quasi-compact and quasi-separated, and an abelian sheaf `F` on `T_étale`
annihilated by an integer `n` invertible on `S`, the base change map
`f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism for every `q`. -/
theorem isIso_higherBaseChangeMapAb_of_smooth_of_zsmul_eq_zero
    (h0EYS : FlatReducedFibresBaseChange.{u}) (h0EZR : EtaleLocalHigherBaseChange.{u})
    (h0EZS : HigherBaseChangePaste.{u}) (h0F08 : FirstFailureNormalization.{u})
    (h03SC2 : AffineCurveCohomologyVanishing.{u}) (h03SC6 : CurveCohomologyAlgClosedInvariance.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) [Smooth f] [QuasiCompact g] [QuasiSeparated g] {n : ℤ}
    (hn : IsUnit (n : Γ(S, ⊤))) (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : ∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMapAb f g h e sq.w q).app F) :=
  (baseChangeAllDegrees_of_smooth' h0EYS h0EZR h0EZS h0F08 h03SC2 h03SC6 h0EYD f
      hn).isIso
    (𝟙 S) (𝟙 X) f (IsPullback.id_horiz f) g h e sq F hF q

end Stacks.EtaleCohomology.SmoothBaseChange

end
