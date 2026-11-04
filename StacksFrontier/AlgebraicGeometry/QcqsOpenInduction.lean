module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Order.CompleteLattice.Finset

/-!
# The Mayer–Vietoris induction principle on quasi-compact opens

Let `X` be a scheme and `P` a property of open subschemes of `X` which holds for every affine
open and passes from `U`, `V` and `U ⊓ V` to `U ⊔ V`. Then `P` holds for every quasi-compact open
contained in an affine open, and, if `X` is quasi-separated, for every quasi-compact open.

This is the induction by which a statement about the cohomology of affine schemes is carried to
quasi-compact quasi-separated schemes through Mayer–Vietoris sequences: first over a separated,
here affine, ambient scheme, where finite intersections of basic opens are basic opens, then in
general, where the intersection of a finite union of affines with one further affine is a
quasi-compact open of that affine.

## Main results

* `AlgebraicGeometry.Scheme.Opens.mayerVietoris_induction_of_le_affine` — the affine-ambient
  case.
* `AlgebraicGeometry.Scheme.Opens.mayerVietoris_induction` — the quasi-separated case.
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Opens

variable {X : Scheme.{u}} (P : X.Opens → Prop)
  (haff : ∀ W : X.Opens, IsAffineOpen W → P W)
  (hmv : ∀ U V : X.Opens, P U → P V → P (U ⊓ V) → P (U ⊔ V))

include haff hmv in
/-- Finite unions of basic opens of an affine open satisfy `P`. -/
theorem mayerVietoris_induction_basicOpen {V : X.Opens} (hV : IsAffineOpen V) :
    ∀ (n : ℕ) (s : Finset Γ(X, V)), s.card ≤ n → P (⨆ f ∈ s, X.basicOpen f) := by
  intro n
  induction n with
  | zero =>
    intro s hs
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hs)]
    simpa using haff ⊥ (isAffineOpen_bot X)
  | succ n ih =>
    intro s hs
    classical
    induction s using Finset.induction_on with
    | empty => simpa using haff ⊥ (isAffineOpen_bot X)
    | insert g t hg _ =>
      have ht : t.card ≤ n := by
        rw [Finset.card_insert_of_notMem hg] at hs
        omega
      have hunion :
          (⨆ f ∈ insert g t, X.basicOpen f) = (⨆ f ∈ t, X.basicOpen f) ⊔ X.basicOpen g := by
        rw [Finset.iSup_insert, sup_comm]
      have hinter : (⨆ f ∈ t, X.basicOpen f) ⊓ X.basicOpen g =
          ⨆ h ∈ t.image (· * g), X.basicOpen h := by
        rw [Finset.iSup_finset_image, iSup₂_inf_eq]
        simp only [Scheme.basicOpen_mul]
      rw [hunion]
      refine hmv _ _ (ih t ht) (haff _ (hV.basicOpen g)) ?_
      rw [hinter]
      exact ih _ (Finset.card_image_le.trans ht)

include haff hmv in
/-- **The Mayer–Vietoris induction principle over an affine open.** If `P` holds for affine opens
and passes from `U`, `V`, `U ⊓ V` to `U ⊔ V`, then it holds for every quasi-compact open `W`
contained in an affine open. -/
theorem mayerVietoris_induction_of_le_affine {V W : X.Opens} (hV : IsAffineOpen V) (hWV : W ≤ V)
    (hW : IsCompact (W : Set X)) : P W := by
  classical
  have hcov : ∀ x ∈ (W : Set X), ∃ f : Γ(X, V), X.basicOpen f ≤ W ∧ x ∈ X.basicOpen f :=
    fun x hx => hV.exists_basicOpen_le ⟨x, hx⟩ (hWV hx)
  choose! g hgW hxg using hcov
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun x : W => (X.basicOpen (g x) : Set X))
    (fun x => (X.basicOpen (g x)).isOpen) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxg x hx⟩)
  have heq : W = ⨆ f ∈ t.image (fun x : W => g x), X.basicOpen f := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
      simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.mem_mk, Set.mem_iUnion,
        Finset.mem_image]
      exact ⟨_, ⟨y, hy, rfl⟩, hxy⟩
    · simp only [iSup_le_iff, Finset.mem_image]
      rintro _ ⟨y, -, rfl⟩
      exact hgW y y.2
  rw [heq]
  exact mayerVietoris_induction_basicOpen P haff hmv hV _ _ le_rfl

include haff hmv in
/-- **The Mayer–Vietoris induction principle.** On a quasi-separated scheme, a property of opens
which holds for affine opens and passes from `U`, `V`, `U ⊓ V` to `U ⊔ V` holds for every
quasi-compact open. -/
theorem mayerVietoris_induction [QuasiSeparatedSpace X] {W : X.Opens}
    (hW : IsCompact (W : Set X)) : P W := by
  classical
  obtain ⟨s, hs, rfl⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
  lift s to Finset X.affineOpens using hs
  induction s using Finset.induction_on with
  | empty => simpa using haff ⊥ (isAffineOpen_bot X)
  | insert V t _ ih =>
    have hunion : (⨆ i ∈ (↑(insert V t) : Set X.affineOpens), (i : X.Opens)) =
        (⨆ i ∈ (↑t : Set X.affineOpens), (i : X.Opens)) ⊔ V := by
      rw [Finset.coe_insert, iSup_insert, sup_comm]
    have htc : IsCompact ((⨆ i ∈ (↑t : Set X.affineOpens), (i : X.Opens) : X.Opens) : Set X) := by
      simp only [Opens.iSup_def, Opens.coe_mk]
      exact t.finite_toSet.isCompact_biUnion fun i _ => i.2.isCompact
    rw [hunion]
    refine hmv _ _ (ih htc) (haff _ V.2) ?_
    exact mayerVietoris_induction_of_le_affine P haff hmv V.2 inf_le_right
      (htc.inter_of_isOpen V.2.isCompact (Opens.isOpen _) (Opens.isOpen _))

end AlgebraicGeometry.Scheme.Opens
