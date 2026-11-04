module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Order.Directed

/-!
# Comparing directed systems of long exact sequences along a tower

Let `0 → Z_{p+1} → Q_p → Z_p → 0` (`p ≥ 0`) be a tower of short exact sequences, as produced by
the opcycles of a resolution of `Z_0`, and suppose given, for every index `i` of a directed set,
a contravariant cohomology theory `h_i^•` with its long exact sequences

`0 → h_i^0(Z_p) → h_i^0(Q_p) → h_i^0(Z_{p+1}) → h_i^1(Z_p) → h_i^1(Q_p) → ⋯`

compatible with transition maps `h_i ⟶ h_{i'}` (`i ≤ i'`), together with a theory `h_∞^•` and
compatible maps `h_i ⟶ h_∞`. This file proves the dévissage underlying the Čech step of Stacks
09YQ: **if `colim_i h_i^m(Q_p) → h_∞^m(Q_p)` is an isomorphism for all `m` and `p`, then so is
`colim_i h_i^m(Z_p) → h_∞^m(Z_p)`**, in particular for `Z_0`.

The colimits are never formed: that the comparison is an isomorphism is expressed elementwise,
as surjectivity (every element of `h_∞` comes from some stage, `DirectedSurj`) and eventual
injectivity (an element of a stage which vanishes in `h_∞` vanishes at a later stage,
`DirectedEvInj`). This is exactly what the consumers need, and it lets the theories be arbitrary
families of abelian groups.

The proof is an induction on the degree `m`, for all `p` at once: eventual injectivity in degree
`m` follows from the statement in degree `m - 1` by the four lemma, and surjectivity in degree `m`
from eventual injectivity in degree `m` at `p + 1` and surjectivity in degree `m - 1` by the
five lemma. The base case uses the injectivity of `h^0(Z_p) → h^0(Q_p)`.

## Main results

* `Stacks.Homology.DirectedTower.surj_and_evInj`: the dévissage.
* `Stacks.Homology.DirectedTower.surj_and_evInj_of_shortExact`: the five lemma for a single short
  exact sequence `0 → A → B → C → 0`: if the comparison is an isomorphism on `A` and on `B` in
  every degree, it is one on `C` in every degree. This is the form the Mayer–Vietoris step of
  Stacks 09YQ uses.
-/

@[expose] public section

namespace Stacks.Homology.DirectedTower

variable {J : Type*} [Preorder J]

/-- Every element of the target comes from some stage. -/
def DirectedSurj {A : J → Type*} {L : Type*} (ℓ : ∀ i, A i → L) : Prop :=
  ∀ y : L, ∃ i, ∃ x : A i, ℓ i x = y

/-- An element of a stage which vanishes in the target vanishes at a later stage. -/
def DirectedEvInj {A : J → Type*} [∀ i, Zero (A i)] {L : Type*} [Zero L] (ℓ : ∀ i, A i → L)
    (t : ∀ {i i' : J}, i ≤ i' → A i → A i') : Prop :=
  ∀ i (x : A i), ℓ i x = 0 → ∃ i', ∃ h : i ≤ i', t h x = 0

variable [IsDirected J (· ≤ ·)]
  -- the theories at the stages, on the `Z_p` and on the `Q_p`: degree `m`, tower position `p`
  (E Q : J → ℕ → ℕ → Type*) [∀ i m p, AddCommGroup (E i m p)] [∀ i m p, AddCommGroup (Q i m p)]
  -- the theory at the limit
  (e q : ℕ → ℕ → Type*) [∀ m p, AddCommGroup (e m p)] [∀ m p, AddCommGroup (q m p)]
  -- transition maps and their composition law
  (tE : ∀ {i i' : J}, i ≤ i' → ∀ m p, E i m p →+ E i' m p)
  (tQ : ∀ {i i' : J}, i ≤ i' → ∀ m p, Q i m p →+ Q i' m p)
  (htE : ∀ {i i' i'' : J} (h : i ≤ i') (h' : i' ≤ i'') m p x,
    tE h' m p (tE h m p x) = tE (h.trans h') m p x)
  -- maps to the limit
  (lE : ∀ i m p, E i m p →+ e m p) (lQ : ∀ i m p, Q i m p →+ q m p)
  (hlE : ∀ {i i' : J} (h : i ≤ i') m p x, lE i' m p (tE h m p x) = lE i m p x)
  (hlQ : ∀ {i i' : J} (h : i ≤ i') m p x, lQ i' m p (tQ h m p x) = lQ i m p x)
  -- the long exact sequences at the stages ...
  (α : ∀ i m p, E i m p →+ Q i m p) (β : ∀ i m p, Q i m p →+ E i m (p + 1))
  (δ : ∀ i m p, E i m (p + 1) →+ E i (m + 1) p)
  -- ... and at the limit
  (α' : ∀ m p, e m p →+ q m p) (β' : ∀ m p, q m p →+ e m (p + 1))
  (δ' : ∀ m p, e m (p + 1) →+ e (m + 1) p)
  -- compatibility with the transitions
  (htα : ∀ {i i' : J} (h : i ≤ i') m p x, α i' m p (tE h m p x) = tQ h m p (α i m p x))
  (htβ : ∀ {i i' : J} (h : i ≤ i') m p x, β i' m p (tQ h m p x) = tE h m (p + 1) (β i m p x))
  (htδ : ∀ {i i' : J} (h : i ≤ i') m p x,
    δ i' m p (tE h m (p + 1) x) = tE h (m + 1) p (δ i m p x))
  -- compatibility with the maps to the limit
  (hlα : ∀ i m p x, lQ i m p (α i m p x) = α' m p (lE i m p x))
  (hlβ : ∀ i m p x, lE i m (p + 1) (β i m p x) = β' m p (lQ i m p x))
  (hlδ : ∀ i m p x, lE i (m + 1) p (δ i m p x) = δ' m p (lE i m (p + 1) x))
  -- exactness at the stages
  (hα₀ : ∀ i p x, α i 0 p x = 0 → x = 0)
  (hβα : ∀ i m p y, β i m p y = 0 → ∃ x, α i m p x = y)
  (hαδ : ∀ i m p x, α i (m + 1) p x = 0 → ∃ y, δ i m p y = x)
  (hδβ : ∀ i m p y, δ i m p (β i m p y) = 0)
  -- exactness at the limit
  (hα₀' : ∀ p x, α' 0 p x = 0 → x = 0)
  (hβα' : ∀ m p y, β' m p (α' m p y) = 0)
  (hδβ' : ∀ m p x, δ' m p x = 0 → ∃ y, β' m p y = x)
  (hαδ' : ∀ m p x, α' (m + 1) p x = 0 → ∃ y, δ' m p y = x)
  -- the comparison is an isomorphism on the `Q_p`
  (hQs : ∀ m p, DirectedSurj (fun i => lQ i m p))
  (hQi : ∀ m p, DirectedEvInj (fun i => lQ i m p) (fun h => tQ h m p))

include htE hlE hlQ htα htβ htδ hlα hlβ hlδ hα₀ hβα hαδ hδβ hα₀' hβα' hδβ' hαδ' hQs hQi in
/-- **The dévissage.** If the comparison of the colimit of the stages with the limit is an
isomorphism on every `Q_p` in every degree, it is an isomorphism on every `Z_p` in every degree:
every element of the limit comes from a stage, and an element of a stage vanishing in the limit
vanishes at a later stage. -/
theorem surj_and_evInj (m : ℕ) :
    ∀ p, DirectedSurj (fun i => lE i m p) ∧
      DirectedEvInj (fun i => lE i m p) (fun h => tE h m p) := by
  -- eventual injectivity in degree `m`, for all `p`, from the statement in lower degrees
  have hinj : ∀ m, (∀ m' < m, ∀ p, DirectedSurj (fun i => lE i m' p) ∧
      DirectedEvInj (fun i => lE i m' p) (fun h => tE h m' p)) →
      ∀ p, DirectedEvInj (fun i => lE i m p) (fun h => tE h m p) := by
    intro m ih p i x hx
    dsimp only at hx
    -- `α x` vanishes in the limit, hence at a later stage
    obtain ⟨i₁, h₁, h₁x⟩ := hQi m p i (α i m p x) (by
      show lQ i m p (α i m p x) = 0
      rw [hlα, hx, map_zero])
    dsimp only at h₁x
    rw [← htα] at h₁x
    cases m with
    | zero => exact ⟨i₁, h₁, hα₀ _ _ _ h₁x⟩
    | succ m =>
      obtain ⟨y, hy⟩ := hαδ i₁ m p _ h₁x
      have hly : δ' m p (lE i₁ m (p + 1) y) = 0 := by
        rw [← hlδ, hy, hlE, hx]
      obtain ⟨z, hz⟩ := hδβ' m p _ hly
      obtain ⟨i₂, w, hw⟩ := hQs m p z
      dsimp only at hw
      obtain ⟨i₃, h₁₃, h₂₃⟩ := directed_of (· ≤ ·) i₁ i₂
      have hd : lE i₃ m (p + 1) (tE h₁₃ m (p + 1) y - β i₃ m p (tQ h₂₃ m p w)) = 0 := by
        rw [map_sub, hlE, hlβ, hlQ]
        show lE i₁ m (p + 1) y - β' m p (lQ i₂ m p w) = 0
        rw [hw, hz, sub_self]
      obtain ⟨i₄, h₃₄, h₄⟩ := (ih m (Nat.lt_succ_self m) (p + 1)).2 i₃ _ hd
      dsimp only at h₄
      refine ⟨i₄, (h₁.trans h₁₃).trans h₃₄, ?_⟩
      rw [map_sub, sub_eq_zero, htE] at h₄
      have h5 : tE (h₁₃.trans h₃₄) (m + 1) p (δ i₁ m p y) = 0 := by
        rw [← htδ, h₄, htδ, hδβ, map_zero]
      rw [hy, htE] at h5
      exact h5
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hm := hinj m ih
    refine fun p => ⟨fun y => ?_, hm p⟩
    obtain ⟨i, w, hw⟩ := hQs m p (α' m p y)
    dsimp only at hw
    obtain ⟨i₁, h₁, h₁w⟩ := hinj m ih (p + 1) i (β i m p w) (by
      show lE i m (p + 1) (β i m p w) = 0
      rw [hlβ, hw, hβα'])
    dsimp only at h₁w
    rw [← htβ] at h₁w
    obtain ⟨x', hx'⟩ := hβα i₁ m p _ h₁w
    have hd : α' m p (y - lE i₁ m p x') = 0 := by
      rw [map_sub, ← hlα, hx', hlQ, hw, sub_self]
    cases m with
    | zero => exact ⟨i₁, x', (sub_eq_zero.1 (hα₀' p _ hd)).symm⟩
    | succ m =>
      obtain ⟨v, hv⟩ := hαδ' m p _ hd
      obtain ⟨i₂, v', hv'⟩ := (ih m (Nat.lt_succ_self m) (p + 1)).1 v
      dsimp only at hv'
      obtain ⟨i₃, h₁₃, h₂₃⟩ := directed_of (· ≤ ·) i₁ i₂
      refine ⟨i₃, tE h₁₃ (m + 1) p x' + δ i₃ m p (tE h₂₃ m (p + 1) v'), ?_⟩
      show lE i₃ (m + 1) p _ = y
      rw [map_add, hlE, hlδ, hlE, hv', hv, add_sub_cancel]

section ShortExact

variable
  -- the theories at the stages on `C`, `B`, `A`, for `0 → A → B → C → 0`, in degree `m`
  (EC EB EA : J → ℕ → Type*) [∀ i m, AddCommGroup (EC i m)] [∀ i m, AddCommGroup (EB i m)]
  [∀ i m, AddCommGroup (EA i m)]
  (eC eB eA : ℕ → Type*) [∀ m, AddCommGroup (eC m)] [∀ m, AddCommGroup (eB m)]
  [∀ m, AddCommGroup (eA m)]
  (tC : ∀ {i i' : J}, i ≤ i' → ∀ m, EC i m →+ EC i' m)
  (tB : ∀ {i i' : J}, i ≤ i' → ∀ m, EB i m →+ EB i' m)
  (tA : ∀ {i i' : J}, i ≤ i' → ∀ m, EA i m →+ EA i' m)
  (htC : ∀ {i i' i'' : J} (h : i ≤ i') (h' : i' ≤ i'') m x,
    tC h' m (tC h m x) = tC (h.trans h') m x)
  (htA : ∀ {i i' i'' : J} (h : i ≤ i') (h' : i' ≤ i'') m x,
    tA h' m (tA h m x) = tA (h.trans h') m x)
  (lC : ∀ i m, EC i m →+ eC m) (lB : ∀ i m, EB i m →+ eB m) (lA : ∀ i m, EA i m →+ eA m)
  (hlC : ∀ {i i' : J} (h : i ≤ i') m x, lC i' m (tC h m x) = lC i m x)
  (hlB : ∀ {i i' : J} (h : i ≤ i') m x, lB i' m (tB h m x) = lB i m x)
  (hlA : ∀ {i i' : J} (h : i ≤ i') m x, lA i' m (tA h m x) = lA i m x)
  (a : ∀ i m, EC i m →+ EB i m) (b : ∀ i m, EB i m →+ EA i m)
  (d : ∀ i m, EA i m →+ EC i (m + 1))
  (a' : ∀ m, eC m →+ eB m) (b' : ∀ m, eB m →+ eA m) (d' : ∀ m, eA m →+ eC (m + 1))
  (hta : ∀ {i i' : J} (h : i ≤ i') m x, a i' m (tC h m x) = tB h m (a i m x))
  (htb : ∀ {i i' : J} (h : i ≤ i') m x, b i' m (tB h m x) = tA h m (b i m x))
  (htd : ∀ {i i' : J} (h : i ≤ i') m x, d i' m (tA h m x) = tC h (m + 1) (d i m x))
  (hla : ∀ i m x, lB i m (a i m x) = a' m (lC i m x))
  (hlb : ∀ i m x, lA i m (b i m x) = b' m (lB i m x))
  (hld : ∀ i m x, lC i (m + 1) (d i m x) = d' m (lA i m x))
  (ha₀ : ∀ i x, a i 0 x = 0 → x = 0)
  (hba : ∀ i m y, b i m y = 0 → ∃ x, a i m x = y)
  (had : ∀ i m x, a i (m + 1) x = 0 → ∃ y, d i m y = x)
  (hdb : ∀ i m y, d i m (b i m y) = 0)
  (ha₀' : ∀ x, a' 0 x = 0 → x = 0)
  (hba' : ∀ m y, b' m (a' m y) = 0)
  (hdb' : ∀ m x, d' m x = 0 → ∃ y, b' m y = x)
  (had' : ∀ m x, a' (m + 1) x = 0 → ∃ y, d' m y = x)
  (hBs : ∀ m, DirectedSurj (fun i => lB i m))
  (hBi : ∀ m, DirectedEvInj (fun i => lB i m) (fun h => tB h m))
  (hAs : ∀ m, DirectedSurj (fun i => lA i m))
  (hAi : ∀ m, DirectedEvInj (fun i => lA i m) (fun h => tA h m))

include htC htA hlC hlB hlA hta htb htd hla hlb hld ha₀ hba had hdb ha₀' hba' hdb' had' hBs hBi
  hAs hAi in
/-- **The five lemma along a directed system.** For a short exact sequence `0 → A → B → C → 0`
whose comparison of the colimit of the stages with the limit is an isomorphism on `A` and on `B`
in every degree, the comparison is an isomorphism on `C` in every degree. -/
theorem surj_and_evInj_of_shortExact (m : ℕ) :
    DirectedSurj (fun i => lC i m) ∧ DirectedEvInj (fun i => lC i m) (fun h => tC h m) := by
  have hinj : ∀ m, DirectedEvInj (fun i => lC i m) (fun h => tC h m) := by
    intro m i x hx
    dsimp only at hx
    obtain ⟨i₁, h₁, h₁x⟩ := hBi m i (a i m x) (by
      show lB i m (a i m x) = 0
      rw [hla, hx, map_zero])
    dsimp only at h₁x
    rw [← hta] at h₁x
    cases m with
    | zero => exact ⟨i₁, h₁, ha₀ _ _ h₁x⟩
    | succ m =>
      obtain ⟨y, hy⟩ := had i₁ m _ h₁x
      have hly : d' m (lA i₁ m y) = 0 := by
        rw [← hld, hy, hlC, hx]
      obtain ⟨z, hz⟩ := hdb' m _ hly
      obtain ⟨i₂, w, hw⟩ := hBs m z
      dsimp only at hw
      obtain ⟨i₃, h₁₃, h₂₃⟩ := directed_of (· ≤ ·) i₁ i₂
      have hd : lA i₃ m (tA h₁₃ m y - b i₃ m (tB h₂₃ m w)) = 0 := by
        rw [map_sub, hlA, hlb, hlB, hw, hz, sub_self]
      obtain ⟨i₄, h₃₄, h₄⟩ := hAi m i₃ _ hd
      dsimp only at h₄
      refine ⟨i₄, (h₁.trans h₁₃).trans h₃₄, ?_⟩
      rw [map_sub, sub_eq_zero, htA] at h₄
      have h5 : tC (h₁₃.trans h₃₄) (m + 1) (d i₁ m y) = 0 := by
        rw [← htd, h₄, htd, hdb, map_zero]
      rw [hy, htC] at h5
      exact h5
  refine ⟨fun y => ?_, hinj m⟩
  obtain ⟨i, w, hw⟩ := hBs m (a' m y)
  dsimp only at hw
  obtain ⟨i₁, h₁, h₁w⟩ := hAi m i (b i m w) (by
    show lA i m (b i m w) = 0
    rw [hlb, hw, hba'])
  dsimp only at h₁w
  rw [← htb] at h₁w
  obtain ⟨x', hx'⟩ := hba i₁ m _ h₁w
  have hd : a' m (y - lC i₁ m x') = 0 := by
    rw [map_sub, ← hla, hx', hlB, hw, sub_self]
  cases m with
  | zero => exact ⟨i₁, x', (sub_eq_zero.1 (ha₀' _ hd)).symm⟩
  | succ m =>
    obtain ⟨v, hv⟩ := had' m _ hd
    obtain ⟨i₂, v', hv'⟩ := hAs m v
    dsimp only at hv'
    obtain ⟨i₃, h₁₃, h₂₃⟩ := directed_of (· ≤ ·) i₁ i₂
    refine ⟨i₃, tC h₁₃ (m + 1) x' + d i₃ m (tA h₂₃ m v'), ?_⟩
    show lC i₃ (m + 1) _ = y
    rw [map_add, hlC, hld, hlA, hv', hv, add_sub_cancel]

end ShortExact

section Transfer

omit [IsDirected J (· ≤ ·)] in
/-- **Transfer along compatible bijections.** If `ψ_i : B_i → A_i` are bijections and
`ψ' : b → a` is injective, compatibly with the transition maps and the maps to the limits, then
the comparison for `B` is an isomorphism as soon as the one for `A` is. -/
theorem surj_evInj_of_bijective {A B : J → Type*} [∀ i, AddCommGroup (A i)]
    [∀ i, AddCommGroup (B i)] {a b : Type*} [AddCommGroup a] [AddCommGroup b]
    (tA : ∀ {i i' : J}, i ≤ i' → A i →+ A i') (tB : ∀ {i i' : J}, i ≤ i' → B i →+ B i')
    (lA : ∀ i, A i →+ a) (lB : ∀ i, B i →+ b) (ψ : ∀ i, B i →+ A i) (ψ' : b →+ a)
    (hψ : ∀ i, Function.Bijective (ψ i)) (hψ' : Function.Injective ψ')
    (ht : ∀ {i i' : J} (h : i ≤ i') x, ψ i' (tB h x) = tA h (ψ i x))
    (hl : ∀ i x, ψ' (lB i x) = lA i (ψ i x)) :
    (DirectedSurj (fun i => lA i) → DirectedSurj (fun i => lB i)) ∧
      (DirectedEvInj (fun i => lA i) (fun h => tA h) →
        DirectedEvInj (fun i => lB i) (fun h => tB h)) := by
  refine ⟨fun hs y => ?_, fun hi i x hx => ?_⟩
  · obtain ⟨i, z, hz⟩ := hs (ψ' y)
    obtain ⟨x, rfl⟩ := (hψ i).2 z
    exact ⟨i, x, hψ' (by rw [hl]; exact hz)⟩
  · obtain ⟨i', h, h'⟩ := hi i (ψ i x) (by simp only at hx ⊢; rw [← hl, hx, map_zero])
    refine ⟨i', h, (hψ i').1 ?_⟩
    simp only at h' ⊢
    rw [ht, h', map_zero]

/-- **A direct sum of two theories.** If a theory is the direct sum of two others, compatibly
with the transition maps and the maps to the limit, and the comparison is an isomorphism for
both summands, it is one for the sum. -/
theorem surj_evInj_of_sum {B B₁ B₂ : J → Type*}
    [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (B₁ i)] [∀ i, AddCommGroup (B₂ i)]
    {b b₁ b₂ : Type*} [AddCommGroup b] [AddCommGroup b₁] [AddCommGroup b₂]
    (t : ∀ {i i' : J}, i ≤ i' → B i →+ B i') (t₁ : ∀ {i i' : J}, i ≤ i' → B₁ i →+ B₁ i')
    (t₂ : ∀ {i i' : J}, i ≤ i' → B₂ i →+ B₂ i')
    (ht₁ : ∀ {i i' i'' : J} (h : i ≤ i') (h' : i' ≤ i'') x, t₁ h' (t₁ h x) = t₁ (h.trans h') x)
    (ht₂ : ∀ {i i' i'' : J} (h : i ≤ i') (h' : i' ≤ i'') x, t₂ h' (t₂ h x) = t₂ (h.trans h') x)
    (l : ∀ i, B i →+ b) (l₁ : ∀ i, B₁ i →+ b₁) (l₂ : ∀ i, B₂ i →+ b₂)
    (hl₁ : ∀ {i i' : J} (h : i ≤ i') x, l₁ i' (t₁ h x) = l₁ i x)
    (hl₂ : ∀ {i i' : J} (h : i ≤ i') x, l₂ i' (t₂ h x) = l₂ i x)
    (p₁ : ∀ i, B i →+ B₁ i) (p₂ : ∀ i, B i →+ B₂ i) (s₁ : ∀ i, B₁ i →+ B i)
    (s₂ : ∀ i, B₂ i →+ B i) (hps : ∀ i x, s₁ i (p₁ i x) + s₂ i (p₂ i x) = x)
    (p₁' : b →+ b₁) (p₂' : b →+ b₂) (s₁' : b₁ →+ b) (s₂' : b₂ →+ b)
    (hps' : ∀ y, s₁' (p₁' y) + s₂' (p₂' y) = y)
    (htp₁ : ∀ {i i' : J} (h : i ≤ i') x, p₁ i' (t h x) = t₁ h (p₁ i x))
    (htp₂ : ∀ {i i' : J} (h : i ≤ i') x, p₂ i' (t h x) = t₂ h (p₂ i x))
    (_hts₁ : ∀ {i i' : J} (h : i ≤ i') x, s₁ i' (t₁ h x) = t h (s₁ i x))
    (_hts₂ : ∀ {i i' : J} (h : i ≤ i') x, s₂ i' (t₂ h x) = t h (s₂ i x))
    (hlp₁ : ∀ i x, l₁ i (p₁ i x) = p₁' (l i x)) (hlp₂ : ∀ i x, l₂ i (p₂ i x) = p₂' (l i x))
    (hls₁ : ∀ i x, l i (s₁ i x) = s₁' (l₁ i x)) (hls₂ : ∀ i x, l i (s₂ i x) = s₂' (l₂ i x))
    (hs₁ : DirectedSurj (fun i => l₁ i)) (hs₂ : DirectedSurj (fun i => l₂ i))
    (hi₁ : DirectedEvInj (fun i => l₁ i) (fun h => t₁ h))
    (hi₂ : DirectedEvInj (fun i => l₂ i) (fun h => t₂ h)) :
    DirectedSurj (fun i => l i) ∧ DirectedEvInj (fun i => l i) (fun h => t h) := by
  refine ⟨fun y => ?_, fun i x hx => ?_⟩
  · obtain ⟨i₁, z₁, hz₁⟩ := hs₁ (p₁' y)
    obtain ⟨i₂, z₂, hz₂⟩ := hs₂ (p₂' y)
    obtain ⟨i₃, h₁, h₂⟩ := directed_of (· ≤ ·) i₁ i₂
    refine ⟨i₃, s₁ i₃ (t₁ h₁ z₁) + s₂ i₃ (t₂ h₂ z₂), ?_⟩
    simp only at hz₁ hz₂ ⊢
    rw [map_add, hls₁, hls₂, hl₁, hl₂, hz₁, hz₂, hps']
  · simp only at hx
    obtain ⟨i₁, h₁, e₁⟩ := hi₁ i (p₁ i x) (by simp only; rw [hlp₁, hx, map_zero])
    obtain ⟨i₂, h₂, e₂⟩ := hi₂ i (p₂ i x) (by simp only; rw [hlp₂, hx, map_zero])
    obtain ⟨i₃, h₁₃, h₂₃⟩ := directed_of (· ≤ ·) i₁ i₂
    refine ⟨i₃, h₁.trans h₁₃, ?_⟩
    simp only at e₁ e₂ ⊢
    rw [← hps i₃ (t _ x), htp₁, htp₂, ← ht₁ h₁ h₁₃, ← ht₂ h₂ h₂₃, e₁, e₂, map_zero, map_zero,
      map_zero, map_zero, add_zero]

end Transfer

end Stacks.Homology.DirectedTower
