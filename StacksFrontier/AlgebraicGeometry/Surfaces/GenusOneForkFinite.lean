module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkPattern

/-!
# The exceptional affine extensions

Of the seven possibilities for the shape, the attachment vertex and the level left open by
`AlgebraicGeometry.NumericalType.exists_affine_extension_of_three_le_neighborCount`, those on a
bounded number of vertices are settled here: each produces one of the exceptional affine
coefficient tables of `AlgebraicGeometry.NumericalType.GenusOne.finitePatterns`. Concretely the
shapes `E₆`, `E₇` and `E₈` and the chains of type `A` give cases (32), (33) and (34), and the
smallest member of each remaining family — a `D₄`, a `B₄` or a `C₄` with one component attached,
and a `D₈` with one component attached at a short arm — gives case (22), (23) or (24) for five
components and case (34) for nine.

Where the level is `2` the weight of the attached component is not determined: it is either
twice or half the weight at the attachment vertex, and the two options give the two tables (23)
and (24), which differ exactly by halving the scale. That dichotomy is
`AlgebraicGeometry.NumericalType.pendant_of_affine_system`, and it is resolved inside each
affected branch.

## Main results

One lemma per branch, named after the shape and the attachment vertex; each concludes
`AlgebraicGeometry.NumericalType.IsGenusOneConfiguration`.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

/-! ### Matching one of the exceptional tables -/

/-- A numerical type which is a Dynkin configuration with one component attached is a genus-one
configuration as soon as an ordering of its components realises one of the exceptional affine
coefficient tables; the conditions are those of
`AlgebraicGeometry.NumericalType.matchesCoefficients_of_erase_leaf` read off the lists. -/
private lemma isGenusOneConfiguration_of_finitePattern {t N : ℕ} (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (d : DynkinShape) (w : ℤ) (hcfg : IsDynkinConfiguration T v d w)
    (r₀ : Fin t) (hr₀ : v r₀ = x)
    (ι : Fin N → Option (Fin t)) (hιinj : Function.Injective ι)
    (E : Fin t → Fin t → Prop) (hE : ∀ r s, d.Edge r s ↔ E r s)
    (mv wv : Fin t → ℤ) (mcl wcl m W : ℤ) (hm : 0 < m) (hW : 0 < W)
    (hmv : ∀ r, T.multiplicity (v r) = mv r * m) (hml : T.multiplicity l = mcl * m)
    (hwv : ∀ r, T.weight (v r) = wv r * W) (hwl : T.weight l = wcl * W)
    (p : List ℤ × List ℤ × List (List ℤ)) (hp : p ∈ GenusOne.finitePatterns)
    (hlen : p.1.length = N) (hcard : N = T.componentCount)
    (hmc : ∀ a : Fin N, (ι a).elim mcl mv = p.1.getD a.val 0)
    (hwc : ∀ a : Fin N, (ι a).elim wcl wv = p.2.1.getD a.val 0)
    (hdiag : ∀ a : Fin N, (p.2.2.getD a.val []).getD a.val 0 = -2 * p.2.1.getD a.val 0)
    (hedge : ∀ a b : Fin N, a ≠ b → AttachAdj ι E r₀ a b →
      (p.2.2.getD a.val []).getD b.val 0 = max (p.2.1.getD a.val 0) (p.2.1.getD b.val 0))
    (hzero : ∀ a b : Fin N, a ≠ b → ¬ AttachAdj ι E r₀ a b →
      (p.2.2.getD a.val []).getD b.val 0 = 0) :
    IsGenusOneConfiguration T := by
  subst hlen
  exact Or.inr (Or.inl ⟨p, hp,
    matchesCoefficients_of_erase_leaf T hn hminus l x hlx hleaf v hvinj hvl d w hcfg r₀ hr₀
      hcard ι hιinj E hE mv wv mcl wcl m W hm hW hmv hml hwv hwl _ _ _ hmc hwc hdiag
      hedge hzero⟩)

/-- At an attachment of level one the weight and the multiplicity of the attached component are
read off from those at the attachment vertex. -/
private lemma pendant_values_of_level_one {t : ℕ} (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (d : DynkinShape) (w : ℤ) (hcfg : IsDynkinConfiguration T v d w)
    (r₀ : Fin t) (hr₀ : v r₀ = x)
    (hmain : 2 * ∑ s, d.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * d.weightFactor r₀ * T.multiplicity (v r₀))
    (a mcl wcl : ℤ) (mv : Fin t → ℤ) (hmv : ∀ r, T.multiplicity (v r) = mv r * a)
    (hmc : 2 * mcl = mv r₀) (hwf : d.weightFactor r₀ = wcl) :
    T.multiplicity l = mcl * a ∧ T.weight l = wcl * w := by
  obtain ⟨hwl, hml⟩ := pendant_level_one (pendant_of_affine_system T hn hminus l x hlx hleaf
    v hvinj hvl hvsurj d w hcfg r₀ hr₀ 1 hmain)
  rw [← hr₀, hcfg.2.2.1 r₀, hwf] at hwl
  rw [← hr₀, hmv r₀, ← hmc] at hml
  exact ⟨by linarith, hwl⟩

/-! ### The completed `E₆`, `E₇` and `E₈` -/

/-- The affine extension of `E₆` at the tip of its short branch is case (32). -/
public lemma isGenusOneConfiguration_of_affine_E6 (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 6 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .E6 w) (hcard : 7 = T.componentCount)
    (r₀ : Fin 6) (hr₀ : v r₀ = x) (hr0 : r₀.val = 5)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.E6.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.E6.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.E6.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 5 := Fin.ext (by simpa using hr0)
  obtain ⟨-, -, a, hapos, hm⟩ := affine_system_solved_E6 (fun r => T.multiplicity (v r))
    (fun r => T.multiplicity_pos _) _ 1 hrest hmain
  obtain ⟨hml, hwl⟩ := pendant_values_of_level_one T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .E6 w hcfg _ hr₀ hmain a 1 1 _ hm (by norm_num) rfl
  exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.E6 w hcfg 5 hr₀
    (fun b => [some 0, some 1, some 2, some 4, some 3, none, some 5].getD b.val none) (by decide)
    (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 5 ∧ s.val < 5) ∨
      (r.val = 2 ∧ s.val = 5) ∨ (s.val = 2 ∧ r.val = 5)) (fun _ _ => Iff.rfl)
    _ DynkinShape.E6.weightFactor 1 1 a w hapos hcfg.2.1 hm hml hcfg.2.2.1 hwl
    ([1, 2, 3, 1, 2, 1, 2], [1, 1, 1, 1, 1, 1, 1],
      [[-2, 1, 0, 0, 0, 0, 0], [1, -2, 1, 0, 0, 0, 0], [0, 1, -2, 0, 1, 0, 1],
       [0, 0, 0, -2, 1, 0, 0], [0, 0, 1, 1, -2, 0, 0], [0, 0, 0, 0, 0, -2, 1],
       [0, 0, 1, 0, 0, 1, -2]]) (by decide) rfl hcard
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The affine extension of `E₇` at the far end of its two-vertex branch is case (33). -/
public lemma isGenusOneConfiguration_of_affine_E7 (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 7 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .E7 w) (hcard : 8 = T.componentCount)
    (r₀ : Fin 7) (hr₀ : v r₀ = x) (hr0 : r₀.val = 5)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.E7.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.E7.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.E7.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 5 := Fin.ext (by simpa using hr0)
  obtain ⟨-, -, a, hapos, hm⟩ := affine_system_solved_E7 (fun r => T.multiplicity (v r))
    (fun r => T.multiplicity_pos _) _ 1 hrest hmain
  obtain ⟨hml, hwl⟩ := pendant_values_of_level_one T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .E7 w hcfg _ hr₀ hmain a 1 1 _ hm (by norm_num) rfl
  exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.E7 w hcfg 5 hr₀
    (fun b => [some 0, some 1, some 2, some 3, some 4, some 5, none,
      some 6].getD b.val none) (by decide)
    (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 6 ∧ s.val < 6) ∨
      (r.val = 3 ∧ s.val = 6) ∨ (s.val = 3 ∧ r.val = 6)) (fun _ _ => Iff.rfl)
    _ DynkinShape.E7.weightFactor 1 1 a w hapos hcfg.2.1 hm hml hcfg.2.2.1 hwl
    ([1, 2, 3, 4, 3, 2, 1, 2], [1, 1, 1, 1, 1, 1, 1, 1],
      [[-2, 1, 0, 0, 0, 0, 0, 0], [1, -2, 1, 0, 0, 0, 0, 0], [0, 1, -2, 1, 0, 0, 0, 0],
       [0, 0, 1, -2, 1, 0, 0, 1], [0, 0, 0, 1, -2, 1, 0, 0], [0, 0, 0, 0, 1, -2, 1, 0],
       [0, 0, 0, 0, 0, 1, -2, 0], [0, 0, 0, 1, 0, 0, 0, -2]]) (by decide) rfl hcard
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The affine extension of `E₈` at the far end of its long arm is case (34). -/
public lemma isGenusOneConfiguration_of_affine_E8 (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 8 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .E8 w) (hcard : 9 = T.componentCount)
    (r₀ : Fin 8) (hr₀ : v r₀ = x) (hr0 : r₀.val = 0)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.E8.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.E8.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.E8.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 0 := Fin.ext (by simpa using hr0)
  obtain ⟨-, -, a, hapos, hm⟩ := affine_system_solved_E8 (fun r => T.multiplicity (v r))
    (fun r => T.multiplicity_pos _) _ 1 hrest hmain
  obtain ⟨hml, hwl⟩ := pendant_values_of_level_one T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .E8 w hcfg _ hr₀ hmain a 1 1 _ hm (by norm_num) rfl
  exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.E8 w hcfg 0 hr₀
    (fun b => [none, some 0, some 1, some 2, some 3, some 4, some 5, some 6,
      some 7].getD b.val none) (by decide)
    (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 7 ∧ s.val < 7) ∨
      (r.val = 4 ∧ s.val = 7) ∨ (s.val = 4 ∧ r.val = 7)) (fun _ _ => Iff.rfl)
    _ DynkinShape.E8.weightFactor 1 1 a w hapos hcfg.2.1 hm hml hcfg.2.2.1 hwl
    ([1, 2, 3, 4, 5, 6, 4, 2, 3], [1, 1, 1, 1, 1, 1, 1, 1, 1],
      [[-2, 1, 0, 0, 0, 0, 0, 0, 0], [1, -2, 1, 0, 0, 0, 0, 0, 0],
       [0, 1, -2, 1, 0, 0, 0, 0, 0], [0, 0, 1, -2, 1, 0, 0, 0, 0],
       [0, 0, 0, 1, -2, 1, 0, 0, 0], [0, 0, 0, 0, 1, -2, 1, 0, 1],
       [0, 0, 0, 0, 0, 1, -2, 1, 0], [0, 0, 0, 0, 0, 0, 1, -2, 0],
       [0, 0, 0, 0, 0, 1, 0, 0, -2]]) (by decide) rfl hcard
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### Chains of type `A` -/

/-- The affine extension of a chain of type `A` on seven vertices at its middle vertex is
case (33): the multiplicities rise from each end to the attachment vertex, so they are
`(1, 2, 3, 4, 3, 2, 1)` there and `2` at the attached component. -/
public lemma isGenusOneConfiguration_of_affine_A7 (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 7 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .A w) (hcard : 8 = T.componentCount)
    (r₀ : Fin 7) (hr₀ : v r₀ = x) (hr0 : r₀.val = 3)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.A.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.A.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.A.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 3 := Fin.ext (by simpa using hr0)
  obtain ⟨-, a, b, hapos, hbpos, hlo, hhi⟩ := affine_system_solved_A (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) _ 1 hrest hmain
  have hab : b = a := by
    have h1 := hlo 3 (by norm_num)
    have h2 := hhi 3 (by norm_num)
    norm_num at h1 h2
    omega
  have hmv : ∀ r : Fin 7,
      T.multiplicity (v r) = (if r.val ≤ 3 then (r.val : ℤ) + 1 else 7 - r.val) * a := by
    intro r
    have hr := r.isLt
    by_cases h : r.val ≤ 3
    · rw [ite_eq_left h]
      linear_combination hlo r (by omega)
    · rw [ite_eq_right h]
      linear_combination hhi r (by omega) + ((7 : ℤ) - (r.val : ℤ)) * hab
  obtain ⟨hml, hwl⟩ := pendant_values_of_level_one T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .A w hcfg _ hr₀ hmain a 2 1 _ hmv (by norm_num) rfl
  exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.A w hcfg 3 hr₀
    (fun c => [some 0, some 1, some 2, some 3, some 4, some 5, some 6,
      none].getD c.val none) (by decide)
    (fun r s => r.val + 1 = s.val ∨ s.val + 1 = r.val) (fun _ _ => Iff.rfl)
    _ DynkinShape.A.weightFactor 2 1 a w hapos hcfg.2.1 hmv hml hcfg.2.2.1 hwl
    ([1, 2, 3, 4, 3, 2, 1, 2], [1, 1, 1, 1, 1, 1, 1, 1],
      [[-2, 1, 0, 0, 0, 0, 0, 0], [1, -2, 1, 0, 0, 0, 0, 0], [0, 1, -2, 1, 0, 0, 0, 0],
       [0, 0, 1, -2, 1, 0, 0, 1], [0, 0, 0, 1, -2, 1, 0, 0], [0, 0, 0, 0, 1, -2, 1, 0],
       [0, 0, 0, 0, 0, 1, -2, 0], [0, 0, 0, 1, 0, 0, 0, -2]]) (by decide) rfl hcard
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The affine extension of a chain of type `A` on eight vertices at its third vertex is
case (34). -/
public lemma isGenusOneConfiguration_of_affine_A8_two (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 8 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .A w) (hcard : 9 = T.componentCount)
    (r₀ : Fin 8) (hr₀ : v r₀ = x) (hr0 : r₀.val = 2)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.A.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.A.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.A.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 2 := Fin.ext (by simpa using hr0)
  obtain ⟨-, a, b, hapos, hbpos, hlo, hhi⟩ := affine_system_solved_A (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) _ 1 hrest hmain
  have hab : a = 2 * b := by
    have h1 := hlo 2 (by norm_num)
    have h2 := hhi 2 (by norm_num)
    norm_num at h1 h2
    omega
  have hmv : ∀ r : Fin 8,
      T.multiplicity (v r)
        = (if r.val ≤ 2 then 2 * ((r.val : ℤ) + 1) else 8 - r.val) * b := by
    intro r
    have hr := r.isLt
    by_cases h : r.val ≤ 2
    · rw [ite_eq_left h]
      linear_combination hlo r (by omega) + ((r.val : ℤ) + 1) * hab
    · rw [ite_eq_right h]
      linear_combination hhi r (by omega)
  obtain ⟨hml, hwl⟩ := pendant_values_of_level_one T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .A w hcfg _ hr₀ hmain b 3 1 _ hmv (by norm_num) rfl
  exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.A w hcfg 2 hr₀
    (fun c => [some 7, some 6, some 5, some 4, some 3, some 2, some 1, some 0,
      none].getD c.val none) (by decide)
    (fun r s => r.val + 1 = s.val ∨ s.val + 1 = r.val) (fun _ _ => Iff.rfl)
    _ DynkinShape.A.weightFactor 3 1 b w hbpos hcfg.2.1 hmv hml hcfg.2.2.1 hwl
    ([1, 2, 3, 4, 5, 6, 4, 2, 3], [1, 1, 1, 1, 1, 1, 1, 1, 1],
      [[-2, 1, 0, 0, 0, 0, 0, 0, 0], [1, -2, 1, 0, 0, 0, 0, 0, 0],
       [0, 1, -2, 1, 0, 0, 0, 0, 0], [0, 0, 1, -2, 1, 0, 0, 0, 0],
       [0, 0, 0, 1, -2, 1, 0, 0, 0], [0, 0, 0, 0, 1, -2, 1, 0, 1],
       [0, 0, 0, 0, 0, 1, -2, 1, 0], [0, 0, 0, 0, 0, 0, 1, -2, 0],
       [0, 0, 0, 0, 0, 1, 0, 0, -2]]) (by decide) rfl hcard
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The affine extension of a chain of type `A` on eight vertices at its sixth vertex is
case (34). -/
public lemma isGenusOneConfiguration_of_affine_A8_five (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 8 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .A w) (hcard : 9 = T.componentCount)
    (r₀ : Fin 8) (hr₀ : v r₀ = x) (hr0 : r₀.val = 5)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.A.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.A.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.A.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 5 := Fin.ext (by simpa using hr0)
  obtain ⟨-, a, b, hapos, hbpos, hlo, hhi⟩ := affine_system_solved_A (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) _ 1 hrest hmain
  have hab : b = 2 * a := by
    have h1 := hlo 5 (by norm_num)
    have h2 := hhi 5 (by norm_num)
    norm_num at h1 h2
    omega
  have hmv : ∀ r : Fin 8,
      T.multiplicity (v r)
        = (if r.val ≤ 5 then (r.val : ℤ) + 1 else 2 * (8 - r.val)) * a := by
    intro r
    have hr := r.isLt
    by_cases h : r.val ≤ 5
    · rw [ite_eq_left h]
      linear_combination hlo r (by omega)
    · rw [ite_eq_right h]
      linear_combination hhi r (by omega) + ((8 : ℤ) - (r.val : ℤ)) * hab
  obtain ⟨hml, hwl⟩ := pendant_values_of_level_one T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .A w hcfg _ hr₀ hmain a 3 1 _ hmv (by norm_num) rfl
  exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.A w hcfg 5 hr₀
    (fun c => [some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7,
      none].getD c.val none) (by decide)
    (fun r s => r.val + 1 = s.val ∨ s.val + 1 = r.val) (fun _ _ => Iff.rfl)
    _ DynkinShape.A.weightFactor 3 1 a w hapos hcfg.2.1 hmv hml hcfg.2.2.1 hwl
    ([1, 2, 3, 4, 5, 6, 4, 2, 3], [1, 1, 1, 1, 1, 1, 1, 1, 1],
      [[-2, 1, 0, 0, 0, 0, 0, 0, 0], [1, -2, 1, 0, 0, 0, 0, 0, 0],
       [0, 1, -2, 1, 0, 0, 0, 0, 0], [0, 0, 1, -2, 1, 0, 0, 0, 0],
       [0, 0, 0, 1, -2, 1, 0, 0, 0], [0, 0, 0, 0, 1, -2, 1, 0, 1],
       [0, 0, 0, 0, 0, 1, -2, 1, 0], [0, 0, 0, 0, 0, 0, 1, -2, 0],
       [0, 0, 0, 0, 0, 1, 0, 0, -2]]) (by decide) rfl hcard
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### The smallest chains of type `B` and `C` -/

/-- The affine extension of a chain of type `B` on four vertices at its second vertex is
case (24). -/
public lemma isGenusOneConfiguration_of_affine_B4 (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 4 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .B w) (hcard : 5 = T.componentCount)
    (r₀ : Fin 4) (hr₀ : v r₀ = x) (hr0 : r₀.val = 1)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.B.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.B.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.B.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 1 := Fin.ext (by simpa using hr0)
  obtain ⟨-, -, a, hapos, hb0, hb1⟩ := affine_system_solved_B (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) _ 1 (by omega) (by omega)
    hrest hmain
  have hmv : ∀ r : Fin 4,
      T.multiplicity (v r) = (if r.val = 0 then (1 : ℤ) else 2) * a := by
    intro r
    by_cases h : r.val = 0
    · rw [ite_eq_left h]
      linear_combination hb0 r h
    · rw [ite_eq_right h]
      linear_combination hb1 r (by omega)
  obtain ⟨hml, hwl⟩ := pendant_values_of_level_one T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .B w hcfg _ hr₀ hmain a 1 2 _ hmv (by norm_num) (by norm_num [DynkinShape.weightFactor])
  exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.B w hcfg 1 hr₀
    (fun b => [some 3, some 2, some 1, some 0, none].getD b.val none) (by decide)
    (fun r s => r.val + 1 = s.val ∨ s.val + 1 = r.val) (fun _ _ => Iff.rfl)
    _ DynkinShape.B.weightFactor 1 2 a w hapos hcfg.2.1 hmv hml
    hcfg.2.2.1 hwl
    ([2, 2, 2, 1, 1], [1, 2, 2, 2, 2],
      [[-2, 2, 0, 0, 0], [2, -4, 2, 0, 0], [0, 2, -4, 2, 2], [0, 0, 2, -4, 0],
       [0, 0, 2, 0, -4]]) (by decide) rfl hcard
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The affine extension of a chain of type `C` on four vertices at its second vertex is
case (23). -/
public lemma isGenusOneConfiguration_of_affine_C4 (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 4 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .C w) (hcard : 5 = T.componentCount)
    (r₀ : Fin 4) (hr₀ : v r₀ = x) (hr0 : r₀.val = 1)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.C.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.C.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.C.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 1 := Fin.ext (by simpa using hr0)
  obtain ⟨-, -, a, hapos, hc0, hc1, hc2⟩ := affine_system_solved_C (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) _ 1 (by omega) (by omega)
    hrest hmain
  have hmv : ∀ r : Fin 4,
      T.multiplicity (v r) = (if r.val = 0 ∨ r.val + 1 = 4 then (1 : ℤ) else 2) * a := by
    intro r
    have hr := r.isLt
    by_cases h : r.val = 0 ∨ r.val + 1 = 4
    · rw [ite_eq_left h]
      rcases h with h | h
      · linear_combination hc0 r h
      · linear_combination hc2 r h
    · rw [ite_eq_right h]
      linear_combination hc1 r (by omega) (by omega)
  obtain ⟨hml, hwl⟩ := pendant_values_of_level_one T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .C w hcfg _ hr₀ hmain a 1 1 _ hmv (by norm_num) (by norm_num [DynkinShape.weightFactor])
  exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.C w hcfg 1 hr₀
    (fun b => [some 3, some 2, some 1, some 0, none].getD b.val none) (by decide)
    (fun r s => r.val + 1 = s.val ∨ s.val + 1 = r.val) (fun _ _ => Iff.rfl)
    _ DynkinShape.C.weightFactor 1 1 a w hapos hcfg.2.1 hmv hml
    hcfg.2.2.1 hwl
    ([1, 2, 2, 1, 1], [2, 1, 1, 1, 1],
      [[-4, 2, 0, 0, 0], [2, -2, 1, 0, 0], [0, 1, -2, 1, 1], [0, 0, 1, -2, 0],
       [0, 0, 1, 0, -2]]) (by decide) rfl hcard
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### The smallest diagram of type `D` -/

/-- The affine extension of `D₄` at its central vertex is case (22), the star with four legs. -/
public lemma isGenusOneConfiguration_of_affine_D4_centre (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 4 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .D w) (hcard : 5 = T.componentCount)
    (r₀ : Fin 4) (hr₀ : v r₀ = x) (hr0 : r₀.val = 1)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.D.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 1 := Fin.ext (by simpa using hr0)
  obtain ⟨a, hapos, hcases⟩ := affine_system_solved_D (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) _ 1 hrest hmain
  rcases hcases with h | h | h | h <;> try omega
  obtain ⟨-, -, hd0, hd1, hd2⟩ := h
  have hmv : ∀ r : Fin 4,
      T.multiplicity (v r) = (if r.val = 1 then (2 : ℤ) else 1) * a := by
    intro r
    have hr := r.isLt
    by_cases h : r.val = 1
    · rw [ite_eq_left h]
      linear_combination hd1 r (by omega) (by omega)
    · rw [ite_eq_right h]
      rcases Nat.eq_zero_or_pos r.val with h0 | h0
      · linear_combination hd0 r h0
      · linear_combination hd2 r (by omega)
  obtain ⟨hml, hwl⟩ := pendant_values_of_level_one T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .D w hcfg _ hr₀ hmain a 1 1 _ hmv (by norm_num) (by norm_num [DynkinShape.weightFactor])
  exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.D w hcfg 1 hr₀
    (fun b => [some 1, some 0, some 2, some 3, none].getD b.val none) (by decide)
    (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 3 ∧ s.val < 3) ∨
      (r.val = 1 ∧ s.val = 3) ∨ (s.val = 1 ∧ r.val = 3)) (fun _ _ => Iff.rfl)
    _ DynkinShape.D.weightFactor 1 1 a w hapos hcfg.2.1 hmv hml
    hcfg.2.2.1 hwl
    ([2, 1, 1, 1, 1], [1, 1, 1, 1, 1],
      [[-2, 1, 1, 1, 1], [1, -2, 0, 0, 0], [1, 0, -2, 0, 0], [1, 0, 0, -2, 0],
       [1, 0, 0, 0, -2]]) (by decide) rfl hcard
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The affine extension of `D₄` at one of its three leg tips is case (23) or case (24),
according to which of the two weights at the attachment is the larger. The ordering `ι` lists
the attached component, the attachment vertex, the central vertex and the two remaining legs,
in that order. -/
private lemma isGenusOneConfiguration_of_affine_D4_leg (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 4 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .D w) (hcard : 5 = T.componentCount)
    (r₀ : Fin 4) (hr₀ : v r₀ = x)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * T.multiplicity (v s)
      = 2 * DynkinShape.D.weightFactor r₀ * T.multiplicity (v r₀))
    (a : ℤ) (hapos : 0 < a) (mv : Fin 4 → ℤ)
    (hmv : ∀ r, T.multiplicity (v r) = mv r * a) (hmx : mv r₀ = 2)
    (ι : Fin 5 → Option (Fin 4)) (hιinj : Function.Injective ι)
    (hmc23 : ∀ b : Fin 5, (ι b).elim 1 mv = [1, 2, 2, 1, 1].getD b.val 0)
    (hmc24 : ∀ b : Fin 5, (ι b).elim 2 mv = [2, 2, 2, 1, 1].getD b.val 0)
    (hwc23 : ∀ b : Fin 5, (ι b).elim 2 DynkinShape.D.weightFactor
      = [2, 1, 1, 1, 1].getD b.val 0)
    (hwc24 : ∀ b : Fin 5, (ι b).elim 1 (fun _ : Fin 4 => (2 : ℤ))
      = [1, 2, 2, 2, 2].getD b.val 0)
    (hedge23 : ∀ b c : Fin 5, b ≠ c →
      AttachAdj ι (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 3 ∧ s.val < 3) ∨
        (r.val = 1 ∧ s.val = 3) ∨ (s.val = 1 ∧ r.val = 3)) r₀ b c →
      ([[-4, 2, 0, 0, 0], [2, -2, 1, 0, 0], [0, 1, -2, 1, 1], [0, 0, 1, -2, 0],
        [0, 0, 1, 0, -2]].getD b.val []).getD c.val 0
        = max ([2, 1, 1, 1, 1].getD b.val 0) ([2, 1, 1, 1, 1].getD c.val 0))
    (hzero23 : ∀ b c : Fin 5, b ≠ c →
      ¬ AttachAdj ι (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 3 ∧ s.val < 3)
        ∨ (r.val = 1 ∧ s.val = 3) ∨ (s.val = 1 ∧ r.val = 3)) r₀ b c →
      ([[-4, 2, 0, 0, 0], [2, -2, 1, 0, 0], [0, 1, -2, 1, 1], [0, 0, 1, -2, 0],
        [0, 0, 1, 0, -2]].getD b.val []).getD c.val 0 = 0)
    (hedge24 : ∀ b c : Fin 5, b ≠ c →
      AttachAdj ι (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 3 ∧ s.val < 3) ∨
        (r.val = 1 ∧ s.val = 3) ∨ (s.val = 1 ∧ r.val = 3)) r₀ b c →
      ([[-2, 2, 0, 0, 0], [2, -4, 2, 0, 0], [0, 2, -4, 2, 2], [0, 0, 2, -4, 0],
        [0, 0, 2, 0, -4]].getD b.val []).getD c.val 0
        = max ([1, 2, 2, 2, 2].getD b.val 0) ([1, 2, 2, 2, 2].getD c.val 0))
    (hzero24 : ∀ b c : Fin 5, b ≠ c →
      ¬ AttachAdj ι (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 3 ∧ s.val < 3)
        ∨ (r.val = 1 ∧ s.val = 3) ∨ (s.val = 1 ∧ r.val = 3)) r₀ b c →
      ([[-2, 2, 0, 0, 0], [2, -4, 2, 0, 0], [0, 2, -4, 2, 2], [0, 0, 2, -4, 0],
        [0, 0, 2, 0, -4]].getD b.val []).getD c.val 0 = 0) :
    IsGenusOneConfiguration T := by
  have hpend := pendant_of_affine_system T hn hminus l x hlx hleaf v hvinj hvl hvsurj .D w hcfg
    r₀ hr₀ 2 hmain
  rw [← hr₀] at hpend
  have hmxv : T.multiplicity (v r₀) = 2 * a := by rw [hmv r₀, hmx]
  rcases pendant_level_two T l (v r₀) v w a (fun r => hcfg.2.2.1 r) (hcfg.2.2.1 r₀) hmxv
    hpend with ⟨W, hWpos, hwv, hwl, hml⟩ | ⟨hwl, hml⟩
  · exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
      DynkinShape.D w hcfg r₀ hr₀ ι hιinj _ (fun _ _ => Iff.rfl)
      mv (fun _ => 2) 2 1 a W hapos hWpos hmv hml hwv hwl
      ([2, 2, 2, 1, 1], [1, 2, 2, 2, 2],
        [[-2, 2, 0, 0, 0], [2, -4, 2, 0, 0], [0, 2, -4, 2, 2], [0, 0, 2, -4, 0],
         [0, 0, 2, 0, -4]]) (by decide) rfl hcard
      hmc24 hwc24 (by decide) hedge24 hzero24
  · exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
      DynkinShape.D w hcfg r₀ hr₀ ι hιinj _ (fun _ _ => Iff.rfl)
      mv DynkinShape.D.weightFactor 1 2 a w hapos hcfg.2.1 hmv hml hcfg.2.2.1 hwl
      ([1, 2, 2, 1, 1], [2, 1, 1, 1, 1],
        [[-4, 2, 0, 0, 0], [2, -2, 1, 0, 0], [0, 1, -2, 1, 1], [0, 0, 1, -2, 0],
         [0, 0, 1, 0, -2]]) (by decide) rfl hcard
      hmc23 hwc23 (by decide) hedge23 hzero23

/-- The affine extension of `D₄` at the far end of its long arm is case (23) or case (24). -/
public lemma isGenusOneConfiguration_of_affine_D4_zero (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 4 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .D w) (hcard : 5 = T.componentCount)
    (r₀ : Fin 4) (hr₀ : v r₀ = x) (hr0 : r₀.val = 0)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * T.multiplicity (v s)
      = 2 * DynkinShape.D.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 0 := Fin.ext (by simpa using hr0)
  obtain ⟨a, hapos, hcases⟩ := affine_system_solved_D (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) _ 2 hrest hmain
  rcases hcases with h | h | h | h <;> try omega
  obtain ⟨-, -, hlo, hhi⟩ := h
  have hmv : ∀ r : Fin 4,
      T.multiplicity (v r) = (if r.val + 3 ≤ 4 then (2 : ℤ) else 1) * a := by
    intro r
    have hr := r.isLt
    by_cases hc : r.val + 3 ≤ 4
    · rw [ite_eq_left hc]
      linear_combination hlo r hc
    · rw [ite_eq_right hc]
      linear_combination hhi r (by omega)
  exact isGenusOneConfiguration_of_affine_D4_leg T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    w hcfg hcard 0 hr₀ hmain a hapos _ hmv (by decide)
    (fun b => [none, some 0, some 1, some 2, some 3].getD b.val none) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- On the long arm of a diagram of type `D` the multiplicities rise linearly, then halve onto
the two short arms. -/
private lemma multiplicity_eq_of_affine_D_tail {t : ℕ} (m : Fin t → ℤ) (a c₁ c₂ : ℤ) {e₁ e₂ : ℤ}
    (hlo : ∀ r : Fin t, r.val + 3 ≤ t → m r = ((r.val : ℤ) + 1) * a)
    (hmid : ∀ r : Fin t, r.val + 2 = t → 2 * m r = e₁ * a)
    (hend : ∀ r : Fin t, r.val + 1 = t → 2 * m r = e₂ * a) (h₁ : e₁ = 2 * c₁) (h₂ : e₂ = 2 * c₂) :
    ∀ r : Fin t, m r
      = (if r.val + 3 ≤ t then (r.val : ℤ) + 1 else if r.val + 2 = t then c₁ else c₂) * a := by
  subst h₁ h₂
  intro r
  have hr := r.isLt
  split_ifs with hc hc2
  · exact hlo r hc
  · linarith [hmid r hc2]
  · linarith [hend r (by omega)]

/-- The affine extension of `D₄` at the last of its three leg tips is case (23) or case (24). -/
public lemma isGenusOneConfiguration_of_affine_D4_last (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 4 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .D w) (hcard : 5 = T.componentCount)
    (r₀ : Fin 4) (hr₀ : v r₀ = x) (hr0 : r₀.val = 3)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * T.multiplicity (v s)
      = 2 * DynkinShape.D.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 3 := Fin.ext (by simpa using hr0)
  obtain ⟨a, hapos, hcases⟩ := affine_system_solved_D (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) _ 2 hrest hmain
  rcases hcases with h | h | h | h <;> try omega
  obtain ⟨-, -, hlo, hmid, hend⟩ := h
  have hmv := multiplicity_eq_of_affine_D_tail _ a 1 2 hlo hmid hend (by norm_num)
    (by norm_num)
  exact isGenusOneConfiguration_of_affine_D4_leg T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    w hcfg hcard 3 hr₀ hmain a hapos _ hmv (by decide)
    (fun b => [none, some 3, some 1, some 0, some 2].getD b.val none) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- The affine extension of `D₄` at the middle of its three leg tips is case (23) or
case (24). -/
public lemma isGenusOneConfiguration_of_affine_D4_mid (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 4 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .D w) (hcard : 5 = T.componentCount)
    (r₀ : Fin 4) (hr₀ : v r₀ = x) (hr0 : r₀.val = 2)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * T.multiplicity (v s)
      = 2 * DynkinShape.D.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 2 := Fin.ext (by simpa using hr0)
  obtain ⟨a, hapos, hcases⟩ := affine_system_solved_D (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) _ 2 hrest hmain
  rcases hcases with h | h | h | h <;> try omega
  obtain ⟨-, -, hlo, hmid, hend⟩ := h
  have hmv := multiplicity_eq_of_affine_D_tail _ a 2 1 hlo hmid hend (by norm_num)
    (by norm_num)
  exact isGenusOneConfiguration_of_affine_D4_leg T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    w hcfg hcard 2 hr₀ hmain a hapos _ hmv (by decide)
    (fun b => [none, some 2, some 1, some 0, some 3].getD b.val none) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-! ### `D₈` with a component attached at a short arm -/

/-- The affine extension of `D₈` at the second of its two short arms is case (34). -/
public lemma isGenusOneConfiguration_of_affine_D8_last (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 8 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .D w) (hcard : 9 = T.componentCount)
    (r₀ : Fin 8) (hr₀ : v r₀ = x) (hr0 : r₀.val = 7)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.D.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 7 := Fin.ext (by simpa using hr0)
  obtain ⟨a, hapos, hcases⟩ := affine_system_solved_D (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) _ 1 hrest hmain
  rcases hcases with h | h | h | h <;> try omega
  obtain ⟨-, -, hlo, hmid, hend⟩ := h
  have hmv := multiplicity_eq_of_affine_D_tail _ a 3 4 hlo hmid hend (by norm_num)
    (by norm_num)
  obtain ⟨hml, hwl⟩ := pendant_values_of_level_one T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .D w hcfg _ hr₀ hmain a 2 1 _ hmv (by norm_num) (by norm_num [DynkinShape.weightFactor])
  exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.D w hcfg 7 hr₀
    (fun b => [some 0, some 1, some 2, some 3, some 4, some 5, some 7, none,
      some 6].getD b.val none) (by decide)
    (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 7 ∧ s.val < 7) ∨
      (r.val = 5 ∧ s.val = 7) ∨ (s.val = 5 ∧ r.val = 7)) (fun _ _ => Iff.rfl)
    _ DynkinShape.D.weightFactor 2 1 a w hapos hcfg.2.1 hmv hml
    hcfg.2.2.1 hwl
    ([1, 2, 3, 4, 5, 6, 4, 2, 3], [1, 1, 1, 1, 1, 1, 1, 1, 1],
      [[-2, 1, 0, 0, 0, 0, 0, 0, 0], [1, -2, 1, 0, 0, 0, 0, 0, 0],
       [0, 1, -2, 1, 0, 0, 0, 0, 0], [0, 0, 1, -2, 1, 0, 0, 0, 0],
       [0, 0, 0, 1, -2, 1, 0, 0, 0], [0, 0, 0, 0, 1, -2, 1, 0, 1],
       [0, 0, 0, 0, 0, 1, -2, 1, 0], [0, 0, 0, 0, 0, 0, 1, -2, 0],
       [0, 0, 0, 0, 0, 1, 0, 0, -2]]) (by decide) rfl hcard
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The affine extension of `D₈` at the first of its two short arms is case (34). -/
public lemma isGenusOneConfiguration_of_affine_D8_mid (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin 8 → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .D w) (hcard : 9 = T.componentCount)
    (r₀ : Fin 8) (hr₀ : v r₀ = x) (hr0 : r₀.val = 6)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.D.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain rfl : r₀ = 6 := Fin.ext (by simpa using hr0)
  obtain ⟨a, hapos, hcases⟩ := affine_system_solved_D (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) _ 1 hrest hmain
  rcases hcases with h | h | h | h <;> try omega
  obtain ⟨-, -, hlo, hmid, hend⟩ := h
  have hmv := multiplicity_eq_of_affine_D_tail _ a 4 3 hlo hmid hend (by norm_num)
    (by norm_num)
  obtain ⟨hml, hwl⟩ := pendant_values_of_level_one T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .D w hcfg _ hr₀ hmain a 2 1 _ hmv (by norm_num) (by norm_num [DynkinShape.weightFactor])
  exact isGenusOneConfiguration_of_finitePattern T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.D w hcfg 6 hr₀
    (fun b => [some 0, some 1, some 2, some 3, some 4, some 5, some 6, none,
      some 7].getD b.val none) (by decide)
    (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 7 ∧ s.val < 7) ∨
      (r.val = 5 ∧ s.val = 7) ∨ (s.val = 5 ∧ r.val = 7)) (fun _ _ => Iff.rfl)
    _ DynkinShape.D.weightFactor 2 1 a w hapos hcfg.2.1 hmv hml
    hcfg.2.2.1 hwl
    ([1, 2, 3, 4, 5, 6, 4, 2, 3], [1, 1, 1, 1, 1, 1, 1, 1, 1],
      [[-2, 1, 0, 0, 0, 0, 0, 0, 0], [1, -2, 1, 0, 0, 0, 0, 0, 0],
       [0, 1, -2, 1, 0, 0, 0, 0, 0], [0, 0, 1, -2, 1, 0, 0, 0, 0],
       [0, 0, 0, 1, -2, 1, 0, 0, 0], [0, 0, 0, 0, 1, -2, 1, 0, 1],
       [0, 0, 0, 0, 0, 1, -2, 1, 0], [0, 0, 0, 0, 0, 0, 1, -2, 0],
       [0, 0, 0, 0, 0, 1, 0, 0, -2]]) (by decide) rfl hcard
    (by decide) (by decide) (by decide) (by decide) (by decide)

end AlgebraicGeometry.NumericalType
