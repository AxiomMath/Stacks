module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChart
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute

/-!
# Further results

Results complementing `StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChart`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'}
  {g' : X' ⟶ X}

end BaseChangeChart

/-- **The `U'` of the chart on given affine opens contains every point over them.** A point `x'`
of `X'` with `g' x' ∈ U` and `f' x' ∈ V'` lies in the `U' = V' ×_V U` of
`BaseChangeChart.ofAffineOpens`, because `x'` corresponds to a point of `U ×_V V'` under the
cartesian square. -/
public theorem BaseChangeChart.exists_incU'_ofAffineOpens_eq {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (U : X.Opens) (V : S.Opens) (V' : S'.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hUV : U ≤ f ⁻¹ᵁ V) (hV'V : V' ≤ g ⁻¹ᵁ V) (x' : X') (hxU : g' x' ∈ U)
    (hs'V' : f' x' ∈ V') :
    ∃ y : Spec (BaseChangeChart.ofAffineOpens sq U V V' hU hV hV' hUV hV'V).A',
      (BaseChangeChart.ofAffineOpens sq U V V' hU hV hV' hUV hV'V).incU' y = x' := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let _ : Algebra Γ(S, V) Γ(S', V') := (g.appLE V V' hV'V).hom.toAlgebra
  let incU : Spec (CommRingCat.of Γ(X, U)) ⟶ X := hU.fromSpec
  let incV : Spec (CommRingCat.of Γ(S, V)) ⟶ S := hV.fromSpec
  let incV' : Spec (CommRingCat.of Γ(S', V')) ⟶ S' := hV'.fromSpec
  let e := AlgebraicGeometry.pullbackSpecIso (Γ(S, V) : Type u)
    (Γ(X, U) : Type u) (Γ(S', V') : Type u)
  have hwU : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U))) ≫ incV =
      incU ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV
  have hwV' : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(S', V'))) ≫ incV =
      incV' ≫ g :=
    IsAffineOpen.SpecMap_appLE_fromSpec g hV hV' hV'V
  let q := pullback.map
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U))))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(S', V')))) f g
    incU incV' incV hwU hwV'
  let ch := BaseChangeChart.ofAffineOpens sq U V V' hU hV hV' hUV hV'V
  have : IsOpenImmersion ch.incU := ch.isOpenImmersion_incU
  have : IsOpenImmersion ch.incV' := ch.isOpenImmersion_incV'
  have hz : ∀ {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W) {p : pullback f g ⟶ Y}
      {a : X' ⟶ Y}, sq.isoPullback.hom ≫ p = a → a x' ∈ W →
      p (sq.isoPullback.hom x') ∈ Set.range hW.fromSpec := fun hW _ _ h hx => by
    rwa [← Scheme.Hom.comp_apply, h, ← Scheme.Hom.coe_opensRange, hW.opensRange_fromSpec]
  obtain ⟨w, hw⟩ : sq.isoPullback.hom x' ∈ Set.range q := by
    rw [Scheme.Pullback.range_map _ _ f g incU incV' incV hwU hwV']
    exact ⟨hz hU sq.isoPullback_hom_fst hxU, hz hV' sq.isoPullback_hom_snd hs'V'⟩
  refine ⟨e.hom w, ?_⟩
  change sq.isoPullback.inv (q (e.inv (e.hom w))) = x'
  simp [hw]

end AlgebraicGeometry

end
