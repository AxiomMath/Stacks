module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The axioms of Weil data in coordinates

The cycle class map `γ : CH^i(X) → H^{2i}(X)(i)` and the trace map `∫_X : H^{2d}(X)(d) → F` of
the data (D2), (D3) of Section 0FHA (Tag 0FHA) take values in, respectively are defined on, Tate
twists. The coordinate of the one-dimensional space `F(1)` with which the twisted cup products
are defined identifies a twist `H^n(X)(m)` with `H^n(X)`
(`Stacks.WeilCohomology.WeilData.twCoord`), and the twisted cup products and pullbacks with the
untwisted ones (`WeilData.twCoord_cupTw`, `WeilData.twCoord_pullTw`). Read in these coordinates,
`γ` becomes a map `CH^i(X) → H^{2i}(X)` (`WeilData.cycleClassCoord`) and `∫_X` a map
`H^{2d}(X) → F` (`WeilData.traceCoord`).

This file proves that each of the axioms (A)(b), (B)(b) and (C) follows from its form in these
coordinates, in which no Tate twist appears. This is how a cohomology theory produced by a
realization of motives (Stacks 0FHK) is checked: there the twist by `F(m)` is the tensor product
with `G(𝟏(m))`, and a generator of each `G(𝟏(m))` is fixed once and for all.

## Main definitions

* `Stacks.WeilCohomology.WeilData.cycleClassCoord`: `γ` in coordinates.
* `Stacks.WeilCohomology.WeilData.traceCoord`: `∫_X` in coordinates.

## Main results

* `Stacks.WeilCohomology.WeilData.perfectPairing_of_coord`: axiom (A)(b).
* `Stacks.WeilCohomology.WeilData.kunnethTrace_of_coord`: axiom (B)(b).
* `Stacks.WeilCohomology.WeilData.cycleClassPullback_of_coord`,
  `...cycleClassPushforward_of_coord`, `...cycleClassMul_of_coord`,
  `...cycleClassPoint_of_coord`: axiom (C).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

namespace WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] (W : WeilData k F)

/-- The cycle class map `γ : CH^i(X) → H^{2i}(X)(i)` read in coordinates, `CH^i(X) → H^{2i}(X)`. -/
def cycleClassCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ) :
    codimensionChowGroup k X.obj.hom i →+ W.grade X (2 * i) :=
  (W.twCoord X (2 * i) i).toLinearMap.toAddMonoidHom.comp (W.cycleClass X i)

/-- The trace map `∫_X : H^{2d}(X)(d) → F` read in coordinates, `H^{2d}(X) → F`. -/
def traceCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) :
    W.grade X (2 * (d : ℤ)) →ₗ[F] F :=
  W.trace X d hX ∘ₗ (W.twCoord X (2 * (d : ℤ)) d).symm.toLinearMap

/-- `cycleClassCoord X i α` is the coordinate of the cycle class `γ(α) ∈ H^{2i}(X)(i)`. -/
theorem cycleClassCoord_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :
    W.cycleClassCoord X i α = W.twCoord X (2 * i) i (W.cycleClass X i α) :=
  rfl

/-- The trace of `x ∈ H^{2d}(X)(d)` is the coordinate trace of the coordinate of `x`. -/
theorem trace_eq_traceCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (x : W.Tw X (2 * (d : ℤ)) d) :
    W.trace X d hX x = W.traceCoord X d hX (W.twCoord X _ _ x) := by
  simp [traceCoord]

/-- In coordinates, the pairing is the trace of the cup product. -/
theorem pairingTw_eq_traceCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (i j : ℤ) (h : i + j = 2 * d) (s t : ℤ)
    (h' : s + t = d) (a : W.Tw X i s) (b : W.Tw X j t) :
    W.pairingTw X d hX i j h s t h' a b =
      W.traceCoord X d hX (W.cup X i j _ h (W.twCoord X i s a) (W.twCoord X j t b)) := by
  rw [pairingTw_apply, trace_eq_traceCoord, twCoord_cupTw]

/-- **Axiom (A)(b) in coordinates**: the pairings `(a, b) ↦ tr(a ∪ b)` are perfect. -/
theorem perfectPairing_of_coord
    (h : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
      (hX : IsNonemptyEquidimensional X d) (i j : ℤ) (h : i + j = 2 * d),
      ((W.cup X i j _ h).compr₂ (W.traceCoord X d hX)).IsPerfPair) :
    W.PerfectPairing := by
  intro X d hX i j hij
  have := h X d hX i j hij
  have heq : W.pairing X d hX i j hij =
      ((W.cup X i j _ hij).compr₂ (W.traceCoord X d hX)).compl₁₂
        (LinearEquiv.refl F _).toLinearMap (W.twCoord X j d).toLinearMap := by
    refine LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
    show W.trace X d hX (tateCupLeft (W.cup X i j _ hij) d a b) =
      W.traceCoord X d hX (W.cup X i j _ hij a (W.twCoord X j d b))
    rw [trace_eq_traceCoord]
    exact congrArg (W.traceCoord X d hX)
      (tateTwistCoordinates_map (F := F) (tateLineCoordinate W.finrank_tate) (d : ℤ)
        (W.cup X i j _ hij a) b)
  rw [heq]
  exact LinearMap.IsPerfPair.compl₁₂ _ _ _

/-- **Axiom (B)(b) in coordinates**: `tr_{X×Y}(pr₁^*a ∪ pr₂^*b) = tr_X a · tr_Y b` for
`a ∈ H^{2d}(X)`, `b ∈ H^{2e}(Y)`, and `tr_{X×Y}(pr₁^*a ∪ pr₂^*b) = 0` on the other Künneth
components of `H^{2(d+e)}(X × Y)`. -/
theorem kunnethTrace_of_coord
    (h : ∀ (X Y : (SmoothProjectiveScheme k).FullSubcategory) (d e : ℕ)
      (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
      (hXY : IsNonemptyEquidimensional (SmoothProjectiveScheme.prod X Y) (d + e)),
      (∀ (a : W.grade X (2 * d)) (b : W.grade Y (2 * e)),
        W.traceCoord _ (d + e) hXY (W.cup _ (2 * d) (2 * e) _ (by push_cast; ring)
          (W.pullDeg (SmoothProjectiveScheme.fst X Y) _ a)
          (W.pullDeg (SmoothProjectiveScheme.snd X Y) _ b)) =
          W.traceCoord X d hX a * W.traceCoord Y e hY b) ∧
      ∀ (i j : ℤ) (h : i + j = 2 * ((d + e : ℕ) : ℤ)), i ≠ 2 * d →
        ∀ (a : W.grade X i) (b : W.grade Y j),
          W.traceCoord _ (d + e) hXY (W.cup _ i j _ h
            (W.pullDeg (SmoothProjectiveScheme.fst X Y) _ a)
            (W.pullDeg (SmoothProjectiveScheme.snd X Y) _ b)) = 0) :
    W.KunnethTrace := by
  intro X Y d e hX hY hXY
  refine ⟨fun a b ↦ ?_, fun i j hij hi a b ↦ ?_⟩
  · rw [trace_eq_traceCoord, trace_eq_traceCoord, trace_eq_traceCoord, twCoord_cupTw,
      twCoord_pullTw, twCoord_pullTw]
    exact (h X Y d e hX hY hXY).1 _ _
  · rw [trace_eq_traceCoord, twCoord_cupTw, twCoord_pullTw, twCoord_pullTw]
    exact (h X Y d e hX hY hXY).2 i j hij hi _ _

/-- **Axiom (C)(a) in coordinates**: `γ(f^!β) = f^*γ(β)`. -/
theorem cycleClassPullback_of_coord
    (h : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (i : ℤ)
      (β : codimensionChowGroup k Y.obj.hom i),
      W.cycleClassCoord X i (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) i β) =
        W.pullDeg f _ (W.cycleClassCoord Y i β)) :
    W.CycleClassPullback := by
  intro X Y f i β
  apply (W.twCoord X (2 * i) i).injective
  rw [twCoord_pullTw]
  exact h f i β

/-- **Axiom (C)(c) in coordinates**: `γ(α · β) = γ(α) ∪ γ(β)`. -/
theorem cycleClassMul_of_coord
    (h : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
      (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j),
      W.cycleClassCoord X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β) =
        W.cup X (2 * i) (2 * j) _ (by ring) (W.cycleClassCoord X i α)
          (W.cycleClassCoord X j β)) :
    W.CycleClassMul := by
  intro X i j α β
  apply (W.twCoord X (2 * (i + j)) (i + j)).injective
  rw [twCoord_cupTw]
  exact h X i j α β

/-- **Axiom (C)(d) in coordinates**: `tr_{Spec k} γ([Spec k]) = 1`. -/
theorem cycleClassPoint_of_coord
    (h : W.traceCoord (SmoothProjectiveScheme.point k) 0 isNonemptyEquidimensional_point
      (W.cycleClassCoord (SmoothProjectiveScheme.point k) 0
        (fundamentalClass (SmoothProjectiveScheme.point k))) = 1) :
    W.CycleClassPoint := by
  rwa [CycleClassPoint, trace_eq_traceCoord]

/-- **Axiom (C)(b) in coordinates**: for `f : X ⟶ Y` of nonempty equidimensional schemes of
dimensions `d` and `e` and `α ∈ CH^p(X)`, `tr_X(f^*b ∪ γ(α)) = tr_Y(b ∪ γ(f_*α))` for all `b` of
complementary degree. By Poincaré duality on `Y` this says `γ(f_*α) = f_*γ(α)`. -/
theorem cycleClassPushforward_of_coord (hA : W.PerfectPairing)
    (h : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (d e : ℕ)
      (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (p q : ℤ)
      (hpq : q = p + e - d) (α : codimensionChowGroup k X.obj.hom p) (i : ℤ)
      (hi : i + 2 * p = 2 * d) (hi' : i + 2 * q = 2 * e) (b : W.grade Y i),
      W.traceCoord X d hX (W.cup X i (2 * p) _ hi (W.pullDeg f i b) (W.cycleClassCoord X p α)) =
        W.traceCoord Y e hY (W.cup Y i (2 * q) _ hi' b
          (W.cycleClassCoord Y q (equidimensionalPushforward f d e p q hpq α)))) :
    W.CycleClassPushforward hA := by
  intro X Y f d e hX hY p q hpq α
  have hi : (2 * e - 2 * q) + 2 * p = 2 * (d : ℤ) := by omega
  have hi' : (2 * e - 2 * q) + 2 * q = 2 * (e : ℤ) := by omega
  have hs : (e - q) + p = (d : ℤ) := by omega
  have hs' : (e - q) + q = (e : ℤ) := by omega
  refine W.eq_of_pairingTw_eq hA hY _ _ hi' _ _ hs' fun b ↦ ?_
  rw [← pushforward_trace' hA f hX hY _ _ _ _ _ _ _ _ hi hs hi' hs', pairingTw_eq_traceCoord,
    pairingTw_eq_traceCoord, twCoord_pullTw]
  exact (h f d e hX hY p q hpq α _ hi hi' _).symm

end WeilData

end Stacks.WeilCohomology

end
