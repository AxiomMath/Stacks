module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.StageChart
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# Étale charts of bounded size

Let `G` be an fppf sheaf on the big fppf site of a scheme `S` and let `c : h_W ⟶ G` be a
morphism out of the representable sheaf of an object `W` of the site which is representable by
objects of the site and étale. Then the base change of `c` along any point `h_{T₀} ⟶ G` is an
étale object `L₀` over `T₀` of size at most `2 ^ 2 ^ max (size T₀) (size W)`: the representing
object maps monomorphically to `T₀ ×_S W`.

This is the bound `AlgebraicGeometry.FormalSpace.DependentProduct.IsEtaleChartBounded` asks of an
étale chart before its dependent product along a thickening is formed.

## Main results

* `AlgebraicGeometry.FormalSpace.DependentProduct.isEtaleChartBounded_of_relative`: the bound.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The bound function of an étale chart out of `W`. -/
noncomputable def chartBound (W : BigFppfOver B S hS) (κ : Cardinal.{u}) : Cardinal.{u} :=
  (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max κ ((BigFppfOver.toScheme B S hS).obj W).size

/-- `chartBound W` is monotone in `κ`. -/
theorem chartBound_monotone (W : BigFppfOver B S hS) : Monotone (chartBound W) :=
  fun _ _ h ↦ power_le_power_left two_ne_zero
    (power_le_power_left two_ne_zero (max_le_max h le_rfl))

/-- If `κ` is below the cutoff cardinal of the site, then so is `chartBound W κ`. -/
theorem chartBound_lt (W : BigFppfOver B S hS) {κ : Cardinal.{u}} (hκ : κ < B.cutoff) :
    chartBound W κ < B.cutoff :=
  B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit (max_lt hκ W.left.property))

/-- **The base changes of an étale chart representable by objects of the site have bounded
size.** -/
theorem isEtaleChartBounded_of_relative {G : FppfSheaf B S hS} {W : BigFppfOver B S hS}
    (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ G)
    (hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} c.hom) :
    IsEtaleChartBounded c (chartBound W) := by
  intro T₀ x
  set F := BigFppfOver.toScheme B S hS with hF
  set J := BigFppfOver.topology B S hS with hJ
  set L₀ := hc.1.pullback x.hom
  set q₀ : L₀ ⟶ T₀ := hc.1.snd x.hom
  set f₀ := hc.1.fst x.hom
  have hpre : IsPullback f₀ (uliftYoneda.{u + 1}.map q₀) c.hom x.hom := hc.1.isPullback x.hom
  set r₀ : J.uliftYoneda.{u + 1}.obj L₀ ⟶ J.uliftYoneda.{u + 1}.obj W := ⟨f₀⟩
  have hsq : IsPullback (J.uliftYoneda.{u + 1}.map q₀) r₀ x c := by
    refine IsPullback.of_map_of_faithful (sheafToPresheaf J (Type (u + 1))) ?_
    exact hpre.flip
  refine ⟨L₀, q₀, r₀, hsq, hc.2 x.hom f₀ q₀ hpre, ?_⟩
  -- `L₀` maps monomorphically to `T₀ ×_S W`
  have ht := isTerminal_mkId_bigFppfOver B S hS
  have := hasPullbacks_bigFppfOver B S hS
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  set w₀ : L₀ ⟶ W := (J.uliftYoneda.{u + 1}).preimage r₀
  have hw₀ : J.uliftYoneda.{u + 1}.map w₀ = r₀ := (J.uliftYoneda.{u + 1}).map_preimage r₀
  set m : L₀ ⟶ pullback (ht.from T₀) (ht.from W) :=
    pullback.lift q₀ w₀ (ht.hom_ext _ _)
  have : Mono m := by
    refine ⟨fun a b hab ↦ (J.uliftYoneda.{u + 1}).map_injective ?_⟩
    have h1 := congrArg (· ≫ pullback.fst (ht.from T₀) (ht.from W)) hab
    have h2 := congrArg (· ≫ pullback.snd (ht.from T₀) (ht.from W)) hab
    simp only [Category.assoc, m, pullback.lift_fst, pullback.lift_snd] at h1 h2
    refine hsq.hom_ext ?_ ?_
    · rw [← Functor.map_comp, ← Functor.map_comp, h1]
    · rw [← hw₀, ← Functor.map_comp, ← Functor.map_comp, h2]
  set e := PreservesPullback.iso F (ht.from T₀) (ht.from W)
  have hsize : (F.obj (pullback (ht.from T₀) (ht.from W))).size ≤
      max (F.obj T₀).size (F.obj W).size := by
    rw [Scheme.size_congr e]
    exact Scheme.size_pullback_le _ _
  have hle := Scheme.size_le_of_mono (F.map m)
  have hc₀ : max (F.obj T₀).size (F.obj W).size ≤ chartBound W (F.obj T₀).size :=
    ((cantor _).le.trans (power_le_power_left two_ne_zero (cantor _).le))
  refine hle.trans (max_le ?_ (hsize.trans hc₀))
  refine power_le_power_left two_ne_zero ?_
  exact (Scheme.mk_le_two_pow_size _).trans
    (power_le_power_left two_ne_zero hsize)

end AlgebraicGeometry.FormalSpace.DependentProduct

end
