module

public import Mathlib.Algebra.Exact.Basic

/-!
# Dévissage of a morphism of long exact sequences

Let `S` and `T` be two families of abelian groups `S X n`, `T X n` indexed by objects `X` and
degrees `n : ℕ`, with maps `ψ : S X n ⟶ T X n`. Suppose every `X` sits in a "short exact
sequence" `X ⟶ X' ⟶ X''` along which both `S` and `T` have long exact sequences starting with an
injection in degree `0`, compatible with `ψ`, and such that `ψ` is bijective at `X'` in every
degree. Then `ψ` is bijective at every `X` in every degree.

This is the four-lemma induction on the degree underlying the effaceability argument in the proof
of the Künneth formula [Stacks, Tag 0BED]: one first proves injectivity in degree `n` for every
`X` (using the result in degree `n - 1`), and then surjectivity in degree `n` (using injectivity
in degree `n` at `X''`).

## Main definitions

* `Stacks.CechKunneth.LESMorphism`: the long exact sequences of `S` and `T` along a triple
  `X, X', X''` and the compatibility of `ψ` with them.

## Main results

* `Stacks.CechKunneth.LESMorphism.bijective`: the dévissage.
-/

@[expose] public section

namespace Stacks.CechKunneth

variable {Obj : Type*} {S T : Obj → ℕ → Type*} [∀ X n, AddCommGroup (S X n)]
  [∀ X n, AddCommGroup (T X n)]

/-- **A morphism of long exact sequences** along a triple `X, X', X''`: maps `f, g, δ` for `S` and
for `T`, the exactness of both long sequences together with the injectivity of `f` in degree `0`,
and the compatibility of `ψ` with all three maps. -/
structure LESMorphism (ψ : ∀ X n, S X n →+ T X n) (X X' X'' : Obj) where
  /-- The map `S X n ⟶ S X' n`. -/
  fS : ∀ n, S X n →+ S X' n
  /-- The map `S X' n ⟶ S X'' n`. -/
  gS : ∀ n, S X' n →+ S X'' n
  /-- The connecting map `S X'' n ⟶ S X (n + 1)`. -/
  δS : ∀ n, S X'' n →+ S X (n + 1)
  /-- The map `T X n ⟶ T X' n`. -/
  fT : ∀ n, T X n →+ T X' n
  /-- The map `T X' n ⟶ T X'' n`. -/
  gT : ∀ n, T X' n →+ T X'' n
  /-- The connecting map `T X'' n ⟶ T X (n + 1)`. -/
  δT : ∀ n, T X'' n →+ T X (n + 1)
  /-- Exactness of `S X n ⟶ S X' n ⟶ S X'' n`. -/
  exactS₁ : ∀ n, Function.Exact (fS n) (gS n)
  /-- Exactness of `S X' n ⟶ S X'' n ⟶ S X (n + 1)`. -/
  exactS₂ : ∀ n, Function.Exact (gS n) (δS n)
  /-- Exactness of `S X'' n ⟶ S X (n + 1) ⟶ S X' (n + 1)`. -/
  exactS₃ : ∀ n, Function.Exact (δS n) (fS (n + 1))
  /-- The map `S X 0 ⟶ S X' 0` is injective. -/
  injS : Function.Injective (fS 0)
  /-- Exactness of `T X n ⟶ T X' n ⟶ T X'' n`. -/
  exactT₁ : ∀ n, Function.Exact (fT n) (gT n)
  /-- Exactness of `T X' n ⟶ T X'' n ⟶ T X (n + 1)`. -/
  exactT₂ : ∀ n, Function.Exact (gT n) (δT n)
  /-- Exactness of `T X'' n ⟶ T X (n + 1) ⟶ T X' (n + 1)`. -/
  exactT₃ : ∀ n, Function.Exact (δT n) (fT (n + 1))
  /-- The map `T X 0 ⟶ T X' 0` is injective. -/
  injT : Function.Injective (fT 0)
  /-- `ψ` commutes with the maps `fS` and `fT`. -/
  comm_f : ∀ n x, ψ X' n (fS n x) = fT n (ψ X n x)
  /-- `ψ` commutes with the maps `gS` and `gT`. -/
  comm_g : ∀ n x, ψ X'' n (gS n x) = gT n (ψ X' n x)
  /-- `ψ` commutes with the connecting maps `δS` and `δT`. -/
  comm_δ : ∀ n x, ψ X (n + 1) (δS n x) = δT n (ψ X'' n x)

namespace LESMorphism

variable {ψ : ∀ X n, S X n →+ T X n}

/-- **Injectivity in degree `n`** at `X`, from bijectivity at `X'` in degree `n`, and in degree
`n - 1` at `X'` and `X''`. -/
theorem injective {X X' X'' : Obj} (D : LESMorphism ψ X X' X'') (n : ℕ)
    (h' : Function.Bijective (ψ X' n))
    (hprev : ∀ m, n = m + 1 → Function.Bijective (ψ X' m) ∧ Function.Bijective (ψ X'' m)) :
    Function.Injective (ψ X n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hf : D.fS n x = 0 := h'.1 (by rw [D.comm_f, hx, map_zero, map_zero])
  cases n with
  | zero => exact D.injS (hf.trans (map_zero _).symm)
  | succ m =>
    obtain ⟨hX', hX''⟩ := hprev m rfl
    obtain ⟨y, rfl⟩ := ((D.exactS₃ m) x).1 hf
    have hy : D.δT m (ψ X'' m y) = 0 := by rw [← D.comm_δ, hx]
    obtain ⟨t, ht⟩ := ((D.exactT₂ m) _).1 hy
    obtain ⟨t', rfl⟩ := hX'.2 t
    have : y = D.gS m t' := hX''.1 (by rw [D.comm_g, ht])
    rw [this]
    exact ((D.exactS₂ m) _).2 ⟨t', rfl⟩

/-- **Surjectivity in degree `n`** at `X`, from bijectivity at `X'` in degree `n`, injectivity at
`X''` in degree `n`, and bijectivity in degree `n - 1` at `X''`. -/
theorem surjective {X X' X'' : Obj} (D : LESMorphism ψ X X' X'') (n : ℕ)
    (h' : Function.Bijective (ψ X' n)) (h'' : Function.Injective (ψ X'' n))
    (hprev : ∀ m, n = m + 1 → Function.Bijective (ψ X'' m)) :
    Function.Surjective (ψ X n) := by
  intro t
  obtain ⟨s', hs'⟩ := h'.2 (D.fT n t)
  have hg : D.gS n s' = 0 := h'' (by rw [D.comm_g, hs', map_zero, ((D.exactT₁ n) _).2 ⟨t, rfl⟩])
  obtain ⟨s, rfl⟩ := ((D.exactS₁ n) s').1 hg
  have hd : D.fT n (t - ψ X n s) = 0 := by rw [map_sub, ← D.comm_f, hs', sub_self]
  cases n with
  | zero =>
    exact ⟨s, (sub_eq_zero.1 (D.injT (hd.trans (map_zero _).symm))).symm⟩
  | succ m =>
    obtain ⟨u, hu⟩ := ((D.exactT₃ m) _).1 hd
    obtain ⟨v, rfl⟩ := (hprev m rfl).2 u
    refine ⟨s + D.δS m v, ?_⟩
    rw [map_add, D.comm_δ, hu, add_sub_cancel]

end LESMorphism

/-- **The dévissage.** If every `X` sits in a triple `X, E X, C X` carrying a morphism of long
exact sequences, and `ψ` is bijective at every `E X` in every degree, then `ψ` is bijective at
every `X` in every degree. -/
theorem LESMorphism.bijective {ψ : ∀ X n, S X n →+ T X n} (E C : Obj → Obj)
    (D : ∀ X, LESMorphism ψ X (E X) (C X)) (hE : ∀ X n, Function.Bijective (ψ (E X) n))
    (X : Obj) (n : ℕ) : Function.Bijective (ψ X n) := by
  induction n generalizing X with
  | zero =>
    have hinj : ∀ Y, Function.Injective (ψ Y 0) := fun Y =>
      (D Y).injective 0 (hE Y 0) (fun m h => absurd h (by omega))
    exact ⟨hinj X, (D X).surjective 0 (hE X 0) (hinj (C X)) (fun m h => absurd h (by omega))⟩
  | succ m ih =>
    have hinj : ∀ Y, Function.Injective (ψ Y (m + 1)) := fun Y =>
      (D Y).injective (m + 1) (hE Y (m + 1)) (fun m' h => by
        obtain rfl : m = m' := by omega
        exact ⟨hE Y m, ih (C Y)⟩)
    exact ⟨hinj X, (D X).surjective (m + 1) (hE X (m + 1)) (hinj (C X)) (fun m' h => by
      obtain rfl : m = m' := by omega
      exact ih (C X))⟩

end Stacks.CechKunneth

end
