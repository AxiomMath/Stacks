module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullback
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison

/-!
# Nonvanishing opens and ratios of pulled-back sections

Let `g : X ⟶ Y` be a morphism of schemes, `M` an invertible `𝒪_Y`-module and `s` a global
section of `M`. The pullback of `s` is the global section
`AlgebraicGeometry.pullbackGlobalSections g M s` of `g ^* M`, which is again invertible. This
file records the two facts about it that a comparison of linear systems on an open subscheme
needs: its nonvanishing open is the preimage of the nonvanishing open, and the ratio of two
pulled-back sections is the pullback of the ratio.

Both are proved for `Stacks.AlgebraicGeometry.ProjChartCocycle.ratioOf` at the left-iterated
tensor powers `Stacks.TensorPowers.natTensorPow`
(`Stacks.AlgebraicGeometry.ProjChartRatioPullback.ratioOf_pullback`); what is proved here is the
same statement for `Stacks.ProjectiveFromSections.div`, the ratio of the ampleness theory, with
no tensor power in sight. The proof is the same: the ratio is characterized by
`(t/s) · s = t` and nothing else, so pushing that identity along the unit of the
pullback–pushforward adjunction — semilinear over `AlgebraicGeometry.Scheme.Hom.appLE` — proves
the pulled-back ratio is the ratio of the pullbacks.

## Main results

* `Stacks.RatioPullback.nvOpen_pullbackGlobalSections`: **the nonvanishing open of a pulled-back
  global section is the preimage of the nonvanishing open.**
* `Stacks.RatioPullback.div_pullbackGlobalSections`: **the ratio commutes with pullback.**
* `Stacks.RatioPullback.resO_ratio_pullbackGlobalSections`: the same for the coordinate ratios of
  a family.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.ProjectiveFromSections

universe u

namespace Stacks.RatioPullback

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) [IsInvertibleModule Y M]

/-- **The nonvanishing open of a pulled-back global section is the preimage of the nonvanishing
open.** This is `Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections`
read as an equality of opens. -/
theorem nvOpen_pullbackGlobalSections (s : Γ(M, ⊤)) :
    nvOpen ((Scheme.Modules.pullback g).obj M) (pullbackGlobalSections g M s) =
      g ⁻¹ᵁ nvOpen M s :=
  TopologicalSpace.Opens.ext
    (Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections g M s).symm

/-- **The ratio of two global sections commutes with pullback.** If `t` does not vanish on `V`
and `W` is an open of `X` inside `g⁻¹(V)` on which the pullback of `t` does not vanish, the ratio
`(g^* a)/(g^* t)` over `W` is the pullback of the ratio `a/t` over `V`.

The ratio is the unique section with `(a/t) · t = a`, so the identity is that identity pushed
along the unit of the pullback–pushforward adjunction, which is semilinear
(`Stacks.TwistPullbackPinned.pullbackSectionOn_smul`) and commutes with restriction
(`Stacks.TwistPullbackPinned.pullbackGlobalSections_res`). -/
theorem div_pullbackGlobalSections (t a : Γ(M, ⊤)) {V : Y.Opens} (hV : V ≤ nvOpen M t)
    {W : X.Opens}
    (hW : W ≤ nvOpen ((Scheme.Modules.pullback g).obj M) (pullbackGlobalSections g M t))
    (hWV : W ≤ g ⁻¹ᵁ V) :
    div (pullbackGlobalSections g M t) hW (resT W (pullbackGlobalSections g M a)) =
      g.appLE V W hWV (div t hV (resT V a)) := by
  refine (eq_div (pullbackGlobalSections g M t) hW ?_).symm
  have h0 : div t hV (resT V a) • resT V t = resT V a := div_smul t hV _
  have h1 := congrArg (Stacks.TwistPullbackPinned.pullbackSectionOn g M V) h0
  rw [Stacks.TwistPullbackPinned.pullbackSectionOn_smul,
    Stacks.TwistPullbackPinned.pullbackGlobalSections_res,
    Stacks.TwistPullbackPinned.pullbackGlobalSections_res] at h1
  have h2 := congrArg (resM (L := (Scheme.Modules.pullback g).obj M) hWV) h1
  rw [resM_smul, resM_resT, resM_resT] at h2
  refine Eq.trans ?_ h2
  refine congrArg (fun z => z • resT W (pullbackGlobalSections g M t)) ?_
  have happ : ∀ d : Γ(Y, V), resO hWV (g.app V d) = g.appLE V W hWV d := by
    intro d
    rw [Scheme.Hom.app_eq_appLE]
    exact CategoryTheory.ConcreteCategory.congr_hom
      (Scheme.Hom.appLE_map g (le_refl (g ⁻¹ᵁ V)) (homOfLE hWV).op) d
  exact (happ (div t hV (resT V a))).symm

/-- **The coordinate ratios of a pulled-back family are the pullbacks of the coordinate
ratios.** -/
theorem resO_ratio_pullbackGlobalSections {ι : Type*} (s : ι → Γ(M, ⊤)) (i k : ι)
    {W : X.Opens}
    (hW : W ≤ nvCover (fun l => pullbackGlobalSections g M (s l)) i)
    (hWV : W ≤ g ⁻¹ᵁ nvCover s i) :
    resO hW (ratio (fun l => pullbackGlobalSections g M (s l)) i k) =
      g.appLE (nvCover s i) W hWV (ratio s i k) := by
  rw [ratio, Stacks.TwistPullbackPinned.resO_div, resM_resT,
    div_pullbackGlobalSections g M (s i) (s k) le_rfl hW hWV, ratio]

end Stacks.RatioPullback

end
