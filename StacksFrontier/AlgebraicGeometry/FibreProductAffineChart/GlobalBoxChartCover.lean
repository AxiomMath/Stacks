module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.GlobalBoxSectionChart

/-!
# The chart of a pair of affine opens, and the unit maps of a chart

Two pieces of geometry for a Künneth argument on `X ×_S Y`, both independent of any module.

First, when the base `S` is affine every pair of affine opens `U` of `X` and `V` of `Y` is a chart
— take `⊤` for the chart's base open — and the image of that chart is exactly
`pr₁⁻¹U ⊓ pr₂⁻¹V`. So a pair of open coverings of `X` and of `Y` by affine opens gives a covering
of `X ×_S Y` by charts *indexed by the full grid of pairs*. The grid matters: a family of charts
covering `X ×_S Y` need not contain the chart of a mixed pair, and it is exactly the mixed pairs
that a tensor product has to be tested against.

Second, the comparison `Γ(X, U) ⟶ Γ(Spec Γ(X, U), p^*F)` attached to a chart's structure map is
**bijective**, not merely surjective: it is an isomorphism of modules followed by a restriction
between two opens which are equal.

## Main definitions

* `Stacks.FibreProductAffineChart.Chart.ofAffineOpens`: the chart of a pair of affine opens over
  an affine base.

## Main results

* `AlgebraicGeometry.Scheme.Modules.homApp_injective_of_iso`: an isomorphism of modules is
  injective on sections over any open.
* `Stacks.Tag01VSPullbackTensor.injective_modulesPullbackUnitTop`: the unit comparison over an
  open whose image is the whole source is injective.
* `Stacks.FibreProductAffineChart.Chart.opensRange_ofAffineOpens`: the image of the chart of a
  pair of affine opens is the intersection of the two preimages.
* `Stacks.FibreProductAffineChart.Chart.iSup_opensRange_ofAffineOpens`: **the charts of the pairs
  of two affine coverings cover the fibre product.**

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.homApp_injective_of_iso` is `Iso.hom_inv_id` read through
`congrArg`, exactly as
`Stacks.FibreProductAffineChart.Chart.restrictFunctorIsoPullback_app_inv_hom` is; the composite
`Scheme.Modules.Hom.app (φ ≫ ψ) U` is definitionally the composite of the two apps, and the app
of an identity is the identity, so no further lemma is needed.

Injectivity of the unit comparison is read off
`Stacks.Tag01VSPullbackTensor.modulesPullbackUnitTop_restrictFunctorIsoPullback`, which factors
it as a restriction `Γ(M, U) ⟶ Γ(M, j ''ᵁ ⊤)` followed by the comparison isomorphism. When the
two opens agree the restriction has
`Stacks.Tag01VSPullbackTensor.presheaf_map_map_self` for a left inverse, so the hypotheses are
stated as the two inclusions rather than as an equality of opens — that is how a consumer has
them, from `Stacks.FibreProductAffineChart.Chart.image_fromSpecLeft_top`.

## References

* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **An isomorphism of modules is injective on sections over any open.** -/
theorem homApp_injective_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app e.hom U) :=
  Function.LeftInverse.injective (g := Scheme.Modules.Hom.app e.inv U) fun x =>
    congrArg (fun φ : M ⟶ M ↦ Scheme.Modules.Hom.app φ U x) e.hom_inv_id

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Tag01VSPullbackTensor

/-- **The unit comparison over an open whose preimage is the whole source, and whose image is
that open, is injective.** -/
theorem injective_modulesPullbackUnitTop {Z W : Scheme.{u}} (j : Z ⟶ W) [IsOpenImmersion j]
    (M : W.Modules) (U : W.Opens) (hU : j ⁻¹ᵁ U = ⊤) (hle : j ''ᵁ (⊤ : Z.Opens) ≤ U)
    (hge : U ≤ j ''ᵁ (⊤ : Z.Opens)) :
    Function.Injective (modulesPullbackUnitTop j M U hU) := fun s s' hss => by
  have key : ∀ t : Γ(M, U), modulesPullbackUnitTop j M U hU t =
      Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback j).app M).hom ⊤
        (M.presheaf.map (homOfLE hle).op t) :=
    fun t => modulesPullbackUnitTop_restrictFunctorIsoPullback j M U hU t hle
  have hres : M.presheaf.map (homOfLE hle).op s = M.presheaf.map (homOfLE hle).op s' :=
    Scheme.Modules.homApp_injective_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback j).app M) ⊤
      (((key s).symm.trans hss).trans (key s'))
  exact (presheaf_map_map_self M (homOfLE hle) (homOfLE hge) s).symm.trans
    ((congrArg (fun y ↦ M.presheaf.map (homOfLE hge).op y) hres).trans
      (presheaf_map_map_self M (homOfLE hle) (homOfLE hge) s'))

end Stacks.Tag01VSPullbackTensor

namespace Stacks.FibreProductAffineChart.Chart

open Stacks.Tag01VSPullbackTensor

universe v

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}

/-- **The chart of a pair of affine opens over an affine base.** -/
def ofAffineOpens [IsAffine S] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) : Chart a b where
  base := ⊤
  left := U
  right := V
  isAffineOpen_base := isAffineOpen_top S
  isAffineOpen_left := hU
  isAffineOpen_right := hV
  le_left := le_top
  le_right := le_top

/-- The image of the chart of a pair of affine opens is the intersection of the two preimages. -/
theorem opensRange_ofAffineOpens [IsAffine S] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) :
    (ofAffineOpens (a := a) (b := b) hU hV).ι.opensRange
      = pullback.fst a b ⁻¹ᵁ U ⊓ pullback.snd a b ⁻¹ᵁ V :=
  opensRange_ι _

/-- **The charts of the pairs of two affine coverings cover the fibre product.** -/
theorem iSup_opensRange_ofAffineOpens [IsAffine S] {I J : Type v}
    {U : I → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hUcov : ⨆ i, U i = ⊤)
    {V : J → Y.Opens} (hV : ∀ j, IsAffineOpen (V j)) (hVcov : ⨆ j, V j = ⊤) :
    ⨆ p : I × J, (ofAffineOpens (a := a) (b := b) (hU p.1) (hV p.2)).ι.opensRange = ⊤ := by
  refine eq_top_iff.2 fun z _ => Opens.mem_iSup.2 ?_
  have cover : ∀ {T : Scheme.{u}} {K : Type v} {W : K → T.Opens}, ⨆ k, W k = ⊤ →
      ∀ t, ∃ k, t ∈ W k := fun h t => Opens.mem_iSup.1 (h ▸ trivial)
  obtain ⟨i, hi⟩ := cover hUcov ((pullback.fst a b).base z)
  obtain ⟨j, hj⟩ := cover hVcov ((pullback.snd a b).base z)
  exact ⟨(i, j), (opensRange_ofAffineOpens (a := a) (b := b) (hU i) (hV j)) ▸ ⟨hi, hj⟩⟩

end Stacks.FibreProductAffineChart.Chart

end
