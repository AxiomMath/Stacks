module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData

/-!
# The projection formula for the pushforward of a Weil cohomology theory

Let `H^*` be data (D0), (D1), (D3) of Section 45.9 (Tag 0FHA) over the actual category of smooth
projective schemes over `k`, satisfying axiom (A)(b). For a morphism `f : X ⟶ Y` of nonempty
equidimensional smooth projective schemes the pushforward `f_*` on cohomology is the contragredient
of the pullback `f^*` with respect to the cup-product trace pairings. Stacks 0FHB says

* `f_*(f^*b ∪ a) = b ∪ f_*a` (the projection formula), and
* `g_* ∘ f_* = (g ∘ f)_*` for a second morphism `g : Y ⟶ Z`.

Both are proved as in the source, by pairing against an arbitrary class and using that the
pairing on the target is perfect.

## Main results

* `Stacks.WeilCohomology.WeilData.pushforward_cupTw_pullTw`: the projection formula.
* `Stacks.WeilCohomology.WeilData.pushforward_comp`: functoriality of the pushforward.

## Implementation notes

The twisted cohomology groups `H^n(X)(m) = H^n(X) ⊗ F(m)` are compared with `H^n(X)` through the
coordinate of the one-dimensional line `F(1)` that defines the twisted cup products
(`Stacks.WeilCohomology.tateLineCoordinate`); in that coordinate the twisted cup product is the
cup product and the twisted pullback is the pullback (`WeilData.twCoord_cupTw`,
`WeilData.twCoord_pullTw`), so associativity of the twisted cup product and its compatibility
with pullback come from the ring `H^*(X)` and the algebra homomorphism `f^*`.

## References

* [Stacks Project, Tag 0FHB](https://stacks.math.columbia.edu/tag/0FHB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u w

namespace Stacks.WeilCohomology

namespace WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] (W : WeilData k F)

/-! ### Coordinates on the twists -/

/-- The coordinate `H^n(X)(m) ≃ H^n(X)` given by the coordinate of `F(1)` with which the twisted
cup products are defined. -/
def twCoord (X : (SmoothProjectiveScheme k).FullSubcategory)
    (n m : ℤ) : W.Tw X n m ≃ₗ[F] W.grade X n :=
  tateTwistCoordinates (tateLineCoordinate W.finrank_tate) m

/-- In coordinates the twisted cup product is the cup product. -/
theorem twCoord_cupTw (X : (SmoothProjectiveScheme k).FullSubcategory) (i j n : ℤ) (h : i + j = n)
    (s t m : ℤ)
    (h' : s + t = m) (a : W.Tw X i s) (b : W.Tw X j t) :
    W.twCoord X n m (W.cupTw X i j n h s t m h' a b) =
      W.cup X i j n h (W.twCoord X i s a) (W.twCoord X j t b) := by
  simp only [cupTw, tateCup, tateCupWith, twCoord, LinearMap.compl₁₂_apply,
    LinearMap.compr₂_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- In coordinates the twisted pullback is the pullback. -/
theorem twCoord_pullTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n m : ℤ)
    (a : W.Tw Y n m) :
    W.twCoord X n m (W.pullTw f n m a) = W.pullDeg f n (W.twCoord Y n m a) :=
  tateTwistCoordinates_map _ _ _ _

/-- The value of the pullback in degree `n` is the pullback of the total cohomology. -/
@[simp]
theorem coe_pullDeg {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ)
    (a : W.grade Y n) :
    (W.pullDeg f n a : W.H X) = W.pull f a :=
  rfl

/-- Twisted classes are equal once their coordinates are equal in the total cohomology. -/
private theorem eq_of_coe_twCoord_eq {X : (SmoothProjectiveScheme k).FullSubcategory} {n m : ℤ}
    {a a' : W.Tw X n m} (h : (W.twCoord X n m a : W.H X) = W.twCoord X n m a') : a = a' :=
  (W.twCoord X n m).injective (Subtype.ext h)

/-- **Associativity of the twisted cup product.** -/
theorem cupTw_assoc (X : (SmoothProjectiveScheme k).FullSubcategory) (i₁ i₂ i₃ i₁₂ i₂₃ n : ℤ)
    (h₁₂ : i₁ + i₂ = i₁₂) (h₂₃ : i₂ + i₃ = i₂₃) (h : i₁₂ + i₃ = n) (h' : i₁ + i₂₃ = n)
    (s₁ s₂ s₃ s₁₂ s₂₃ m : ℤ) (g₁₂ : s₁ + s₂ = s₁₂) (g₂₃ : s₂ + s₃ = s₂₃) (g : s₁₂ + s₃ = m)
    (g' : s₁ + s₂₃ = m) (a : W.Tw X i₁ s₁) (b : W.Tw X i₂ s₂) (c : W.Tw X i₃ s₃) :
    W.cupTw X i₁₂ i₃ n h s₁₂ s₃ m g (W.cupTw X i₁ i₂ i₁₂ h₁₂ s₁ s₂ s₁₂ g₁₂ a b) c =
      W.cupTw X i₁ i₂₃ n h' s₁ s₂₃ m g' a (W.cupTw X i₂ i₃ i₂₃ h₂₃ s₂ s₃ s₂₃ g₂₃ b c) := by
  apply eq_of_coe_twCoord_eq
  rw [twCoord_cupTw, twCoord_cupTw, twCoord_cupTw, twCoord_cupTw]
  simp only [coe_cup, mul_assoc]

/-- **The twisted pullback is multiplicative.** -/
theorem pullTw_cupTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (i j n : ℤ)
    (h : i + j = n)
    (s t m : ℤ) (h' : s + t = m) (a : W.Tw Y i s) (b : W.Tw Y j t) :
    W.pullTw f n m (W.cupTw Y i j n h s t m h' a b) =
      W.cupTw X i j n h s t m h' (W.pullTw f i s a) (W.pullTw f j t b) := by
  apply eq_of_coe_twCoord_eq
  rw [twCoord_pullTw, twCoord_cupTw, twCoord_cupTw, twCoord_pullTw, twCoord_pullTw]
  simp only [coe_cup, coe_pullDeg, map_mul]

/-- The pullback along the composite is the composite of the pullbacks. -/
theorem pullTw_comp {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n m : ℤ)
    (a : W.Tw Z n m) :
    W.pullTw (f ≫ g) n m a = W.pullTw f n m (W.pullTw g n m a) := by
  apply eq_of_coe_twCoord_eq
  rw [twCoord_pullTw, twCoord_pullTw, twCoord_pullTw]
  simp only [coe_pullDeg, W.pull_comp, AlgHom.comp_apply]

/-! ### The trace equation at arbitrary complementary indices -/

variable {W}

/-- The pairing is `∫_X` of the twisted cup product. -/
theorem pairingTw_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (i j : ℤ) (h : i + j = 2 * d) (s t : ℤ) (h' : s + t = d)
    (a : W.Tw X i s) (b : W.Tw X j t) :
    W.pairingTw X d hX i j h s t h' a b = W.trace X d hX (W.cupTw X i j _ h s t d h' a b) :=
  rfl

/-- **The trace equation `∫_X f^*b ∪ a = ∫_Y b ∪ f_*a`**, for a test class `b` in any degree and
twist complementary to those of `a`. -/
theorem pushforward_trace' (hA : W.PerfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (j t j' t' : ℤ) (hj : j' + 2 * d = j + 2 * e) (ht : t' + d = t + e) (i s : ℤ)
    (hi : i + j = 2 * d) (hs : s + t = d) (hi' : i + j' = 2 * e) (hs' : s + t' = e)
    (b : W.Tw Y i s) (a : W.Tw X j t) :
    W.pairingTw X d hX i j hi s t hs (W.pullTw f i s b) a =
      W.pairingTw Y e hY i j' hi' s t' hs' b (W.pushforward hA f hX hY j t j' t' hj ht a) := by
  obtain rfl : i = 2 * d - j := by omega
  obtain rfl : s = d - t := by omega
  exact W.pushforward_trace hA f hX hY j t j' t' hj ht b a

/-- A class in `H^j(Y)(t)` of a nonempty equidimensional `Y` is determined by its pairings with
the classes of one complementary degree and twist: axiom (A)(b). -/
theorem eq_of_pairingTw_eq (hA : W.PerfectPairing) {Y : (SmoothProjectiveScheme k).FullSubcategory}
    {e : ℕ}
    (hY : IsNonemptyEquidimensional Y e) (i j : ℤ) (hi : i + j = 2 * e) (s t : ℤ)
    (hs : s + t = e) {a a' : W.Tw Y j t}
    (h : ∀ b : W.Tw Y i s, W.pairingTw Y e hY i j hi s t hs b a =
      W.pairingTw Y e hY i j hi s t hs b a') : a = a' := by
  have := hA.pairingTw Y e hY i j hi s t hs
  exact (LinearMap.IsPerfPair.bijective_right (W.pairingTw Y e hY i j hi s t hs)).injective
    (LinearMap.ext h)

/-! ### Stacks 0FHB -/

/-- **Stacks 0FHB, the projection formula.** For a morphism `f : X ⟶ Y` of nonempty
equidimensional smooth projective schemes over `k`, of dimensions `d` and `e`, and classes
`a ∈ H^j(X)(t)`, `b ∈ H^m(Y)(s)`,

`f_*(f^*b ∪ a) = b ∪ f_*a` in `H^{m+j'}(Y)(s+t')`,

where `f_* : H^j(X)(t) → H^{j'}(Y)(t')` with `j' = j + 2(e - d)`, `t' = t + (e - d)`.
The proof uses only axiom (A)(b). -/
@[stacks 0FHB "the projection formula f_*(f^*b ∪ a) = b ∪ f_*a, over the actual category of \
  smooth projective schemes over k, in every degree and Tate twist"]
theorem pushforward_cupTw_pullTw (hA : W.PerfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (m s j t j' t' : ℤ) (hj : j' + 2 * d = j + 2 * e)
    (ht : t' + d = t + e) (b : W.Tw Y m s) (a : W.Tw X j t) :
    W.pushforward hA f hX hY (m + j) (s + t) (m + j') (s + t') (by omega) (by omega)
        (W.cupTw X m j _ rfl s t _ rfl (W.pullTw f m s b) a) =
      W.cupTw Y m j' _ rfl s t' _ rfl b (W.pushforward hA f hX hY j t j' t' hj ht a) := by
  refine eq_of_pairingTw_eq hA hY (2 * d - (m + j)) (m + j') (by omega) (d - (s + t)) (s + t')
    (by omega) fun c ↦ ?_
  rw [← pushforward_trace' hA f hX hY (m + j) (s + t) (m + j') (s + t') (by omega) (by omega)
      (2 * d - (m + j)) (d - (s + t)) (by omega) (by omega) (by omega) (by omega),
    pairingTw_apply, pairingTw_apply,
    ← W.cupTw_assoc X (2 * d - (m + j)) m j (2 * d - j) (m + j) _ (by omega) (by omega)
      (by omega) (by omega) (d - (s + t)) s t (d - t) (s + t) _ (by omega) (by omega) (by omega)
      (by omega),
    ← W.cupTw_assoc Y (2 * d - (m + j)) m j' (2 * d - j) (m + j') _ (by omega) (by omega)
      (by omega) (by omega) (d - (s + t)) s t' (d - t) (s + t') _ (by omega) (by omega)
      (by omega) (by omega),
    ← W.pullTw_cupTw f _ m (2 * d - j) (by omega) _ s (d - t) (by omega)]
  exact pushforward_trace' hA f hX hY j t j' t' hj ht (2 * d - j) (d - t) (by omega) (by omega)
    (by omega) (by omega) _ a

/-- **Stacks 0FHB, functoriality of the pushforward.** For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`
of nonempty equidimensional smooth projective schemes over `k`, `g_* ∘ f_* = (g ∘ f)_*`.
The proof uses only axiom (A)(b). -/
@[stacks 0FHB "functoriality g_* ∘ f_* = (g ∘ f)_* of the pushforward, over the actual category \
  of smooth projective schemes over k, in every degree and Tate twist"]
theorem pushforward_comp (hA : W.PerfectPairing)
    {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (g : Y ⟶ Z) {d e c : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (hZ : IsNonemptyEquidimensional Z c)
    (j t j' t' j'' t'' : ℤ) (hj : j' + 2 * d = j + 2 * e) (ht : t' + d = t + e)
    (hj' : j'' + 2 * e = j' + 2 * c) (ht' : t'' + e = t' + c) (a : W.Tw X j t) :
    W.pushforward hA g hY hZ j' t' j'' t'' hj' ht' (W.pushforward hA f hX hY j t j' t' hj ht a) =
      W.pushforward hA (f ≫ g) hX hZ j t j'' t'' (by omega) (by omega) a := by
  refine eq_of_pairingTw_eq hA hZ (2 * d - j) j'' (by omega) (d - t) t'' (by omega) fun b ↦ ?_
  rw [← pushforward_trace' hA (f ≫ g) hX hZ j t j'' t'' (by omega) (by omega) (2 * d - j)
      (d - t) (by omega) (by omega) (by omega) (by omega),
    ← pushforward_trace' hA g hY hZ j' t' j'' t'' hj' ht' (2 * d - j) (d - t) (by omega)
      (by omega) (by omega) (by omega),
    ← pushforward_trace' hA f hX hY j t j' t' hj ht (2 * d - j) (d - t) (by omega) (by omega)
      (by omega) (by omega), W.pullTw_comp]

end WeilData

end Stacks.WeilCohomology

end
