module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Counting eigenvectors of an endomorphism through exact sequences

Let `σ` be an endomorphism of an abelian group `A` and `q` an integer. This file bounds the set
`E(A) = {a | σ a = q • a}` of `q`-eigenvectors through maps to and from other groups carrying
compatible endomorphisms. The bounds are in `ℕ∞`, so that no finiteness is needed.

* Through a sequence `U → A → P`, exact at `A`: `#E(A) ≤ #δ(W) · #ι(E(A))`, where `W` is the set
  of `u` with `σ u - q • u ∈ ker δ`.
* Through a surjection `r : P̄ → P` whose kernel is fixed by `σ̄`: the `N`-torsion
  `q`-eigenvectors of `P` are at most `#P[q - 1]` times those of `P̄`.

These are the two steps that reduce the Frobenius eigenvectors in `H¹(Y_k̄, μ_n)` of an open
curve `Y` to those of the Picard group of its compactification, via the Kummer sequence and the
restriction `Pic(Ȳ) → Pic(Y)`.

## Main results

* `Set.encard_le_mul_of_sub_mem`: the fibre bound.
* `Stacks.EigenvectorCount.encard_eigen_le_mul_of_exact`: the bound through an exact sequence.
* `Stacks.EigenvectorCount.encard_torsion_eigen_le_mul_of_surjective`: the bound through a
  surjection with fixed kernel.
-/

@[expose] public section

/-- **The fibre bound.** If any two elements of `E` with the same image under `h` differ by an
element of `F`, then `#E ≤ #h(E) · #F`. -/
theorem Set.encard_le_mul_of_sub_mem {A P : Type*} [AddGroup A] {E F : Set A} (h : A → P)
    (hEF : ∀ a₁ ∈ E, ∀ a₂ ∈ E, h a₁ = h a₂ → a₁ - a₂ ∈ F) :
    E.encard ≤ (h '' E).encard * F.encard := by
  classical
  let rep : P → A := fun p => if hp : ∃ a ∈ E, h a = p then hp.choose else 0
  have hrep : ∀ a ∈ E, rep (h a) ∈ E ∧ h (rep (h a)) = h a := fun a ha => by
    have hp : ∃ a' ∈ E, h a' = h a := ⟨a, ha, rfl⟩
    simp only [rep, dif_pos hp]
    exact hp.choose_spec
  let g : A → P × A := fun a => (h a, a - rep (h a))
  have hinj : Set.InjOn g E := by
    intro a₁ _ a₂ _ h12
    have e1 : h a₁ = h a₂ := congrArg Prod.fst h12
    have e2 : a₁ - rep (h a₁) = a₂ - rep (h a₂) := congrArg Prod.snd h12
    rw [e1] at e2
    exact sub_left_injective e2
  have hsub : g '' E ⊆ (h '' E) ×ˢ F := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, hEF a ha _ (hrep a ha).1 (hrep a ha).2.symm⟩
  calc E.encard = (g '' E).encard := hinj.encard_image.symm
    _ ≤ ((h '' E) ×ˢ F).encard := Set.encard_le_encard hsub
    _ = (h '' E).encard * F.encard := Set.encard_prod

namespace Stacks.EigenvectorCount

variable {U A P : Type*} [AddCommGroup U] [AddCommGroup A] [AddCommGroup P]

/-- **Eigenvectors through an exact sequence.** Let `U →δ A →ι P` be exact at `A`, with
compatible endomorphisms `σ`. The `q`-eigenvectors of `A` are at most `#δ(W) · #ι(E(A))`, where
`W = {u | δ (σ u - q • u) = 0}`. -/
theorem encard_eigen_le_mul_of_exact (σU : U →+ U) (σA : A →+ A) (_σP : P →+ P) (δ : U →+ A)
    (ι : A →+ P) (hδ : ∀ u, δ (σU u) = σA (δ u)) (hexact : ∀ a, ι a = 0 → ∃ u, δ u = a)
    (q : ℤ) :
    {a : A | σA a = q • a}.encard ≤
      (ι '' {a : A | σA a = q • a}).encard *
        (δ '' {u : U | δ (σU u - q • u) = 0}).encard := by
  refine Set.encard_le_mul_of_sub_mem ι fun a₁ h₁ a₂ h₂ h12 => ?_
  obtain ⟨u, hu⟩ := hexact (a₁ - a₂) (by rw [map_sub, h12, sub_self])
  refine ⟨u, ?_, hu⟩
  show δ (σU u - q • u) = 0
  rw [map_sub, map_zsmul, hδ, hu, map_sub, (h₁ : σA a₁ = q • a₁), (h₂ : σA a₂ = q • a₂),
    ← zsmul_sub, sub_self]

variable {P' : Type*} [AddCommGroup P']

/-- **Torsion eigenvectors through a surjection with fixed kernel.** Let `r : P' → P` be
surjective, compatible with endomorphisms `σ'` and `σ`, with `σ'` fixing the kernel of `r`
pointwise. Then the `N`-torsion `Q`-eigenvectors of `P` are at most `#P[Q - 1]` times the
`N`-torsion `Q`-eigenvectors of `P'`: for `z = r w`, the class `(1 - Q) • w - (σ' w - Q • w)` is
an `N`-torsion `Q`-eigenvector over `(1 - Q) • z`. -/
theorem encard_torsion_eigen_le_mul_of_surjective (σ' : P' →+ P') (σ : P →+ P) (r : P' →+ P)
    (hr : Function.Surjective r) (hσ : ∀ w, r (σ' w) = σ (r w))
    (hfix : ∀ l, r l = 0 → σ' l = l) (N Q : ℤ) :
    {z : P | N • z = 0 ∧ σ z = Q • z}.encard ≤
      {w : P' | N • w = 0 ∧ σ' w = Q • w}.encard * {z : P | (Q - 1) • z = 0}.encard := by
  refine (Set.encard_le_mul_of_sub_mem (fun z : P => (1 - Q) • z) fun z₁ _ z₂ _ h12 => ?_).trans
    (mul_le_mul_left ?_ _)
  · show (Q - 1) • (z₁ - z₂) = 0
    have h : (1 - Q) • (z₁ - z₂) = 0 := by rw [zsmul_sub, h12, sub_self]
    rw [show Q - 1 = -(1 - Q) by ring, neg_zsmul, h, neg_zero]
  · refine le_trans (Set.encard_le_encard ?_) (Set.encard_image_le r _)
    rintro _ ⟨z, ⟨hNz, hσz⟩, rfl⟩
    obtain ⟨w, rfl⟩ := hr z
    set l := σ' w - Q • w
    have hl : r l = 0 := by
      simp only [l, map_sub, map_zsmul, hσ, hσz, sub_self]
    have hNw : r (N • w) = 0 := by rw [map_zsmul, hNz]
    have hw : σ' w = l + Q • w := by simp [l]
    have hNl : N • l = (1 - Q) • (N • w) := by
      have e := hfix _ hNw
      rw [map_zsmul, hw] at e
      linear_combination (norm := module) e
    refine ⟨(1 - Q) • w - l, ⟨?_, ?_⟩, ?_⟩
    · linear_combination (norm := module) (-1 : ℤ) • hNl
    · rw [map_sub, map_zsmul, hfix l hl, hw]
      linear_combination (norm := module) (0 : ℤ) • hNl
    · rw [map_sub, map_zsmul, hl, sub_zero]

/-- For `u` with `δ (σ u - q • u) = 0`, where `ker δ ⊆ n • U` and `φ ∘ σ = φ`, the element
`gcd(n, q - 1) • φ u` is `n` times an element of `φ(U)`. -/
private theorem exists_gcd_zsmul_eq_of_eigen {F : Type*} [AddCommGroup F] (δ : U →+ A) {n : ℕ}
    (hδ : ∀ u, δ u = 0 → ∃ v, n • v = u) (φ : U →+ F) (σ : U →+ U) (hσ : ∀ u, φ (σ u) = φ u)
    (q : ℤ) {u : U} (hu : δ (σ u - q • u) = 0) :
    ∃ z : φ.range, (Int.gcd (n : ℤ) (q - 1) : ℤ) • φ u = (n : ℤ) • (z : F) := by
  obtain ⟨v, hv⟩ := hδ _ hu
  have hφv : (n : ℤ) • φ v = -((q - 1) • φ u) := by
    have := congrArg φ hv
    rw [map_nsmul, map_sub, map_zsmul, hσ] at this
    rw [natCast_zsmul, this, sub_zsmul, one_zsmul]
    abel
  refine ⟨⟨Int.gcdA n (q - 1) • φ u - Int.gcdB n (q - 1) • φ v,
    sub_mem (zsmul_mem (AddMonoidHom.mem_range.2 ⟨u, rfl⟩) _)
      (zsmul_mem (AddMonoidHom.mem_range.2 ⟨v, rfl⟩) _)⟩, ?_⟩
  show (Int.gcd (n : ℤ) (q - 1) : ℤ) • φ u =
    (n : ℤ) • (Int.gcdA n (q - 1) • φ u - Int.gcdB n (q - 1) • φ v)
  rw [Int.gcd_eq_gcd_ab (n : ℤ) (q - 1)]
  linear_combination (norm := module) (Int.gcdB n (q - 1)) • hφv

/-- If `a ∣ b`, then `G / a G` is a quotient of `G / b G`, so it has at most as many elements. -/
private theorem encard_univ_quotient_zsmul_le_of_dvd {G : Type*} [AddCommGroup G] {a b : ℤ}
    (hab : a ∣ b) :
    (Set.univ : Set (G ⧸ (zsmulAddGroupHom (α := G) a).range)).encard ≤
      (Set.univ : Set (G ⧸ (zsmulAddGroupHom (α := G) b).range)).encard := by
  obtain ⟨c, hc⟩ := hab
  have hle : (zsmulAddGroupHom (α := G) b).range ≤ (zsmulAddGroupHom (α := G) a).range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨c • x, by simp [hc, smul_smul]⟩
  have hsurj : Function.Surjective (QuotientAddGroup.map
      (zsmulAddGroupHom (α := G) b).range (zsmulAddGroupHom (α := G) a).range
      (AddMonoidHom.id G) (fun x hx => hle hx)) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact ⟨QuotientAddGroup.mk y, rfl⟩
  rw [← Set.image_univ_of_surjective hsurj]
  exact Set.encard_image_le _ _

/-- Two elements with the same class modulo `d G` differ by `d` times an element of `G`. -/
private theorem exists_sub_eq_zsmul_of_mk_eq {G : Type*} [AddCommGroup G] {d : ℤ} {x y : G}
    (h : (QuotientAddGroup.mk x : G ⧸ (zsmulAddGroupHom (α := G) d).range) =
      QuotientAddGroup.mk y) : ∃ t : G, x - y = d • t := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.eq_iff_sub_mem.1 h
  exact ⟨t, ht.symm⟩

/-- **Eigenvectors coming from a group with a divisor map.** Let `δ : U → A` have kernel `n • U`
and let `φ : U → F` into a torsion-free group have kernel inside `n • U`, with `φ ∘ σ = φ`. Then
the image under `δ` of `W = {u | δ (σ u - q • u) = 0}` has at most as many elements as
`φ(U) / (q - 1) φ(U)`. For `u ∈ W`, `(1 - q) φ u ∈ n φ(U)`; writing `g = gcd(n, q - 1)` this forces
`φ u = (n / g) z` with `z ∈ φ(U)`, and the class of `z` modulo `g φ(U)` determines `δ u`. -/
theorem encard_image_eigen_le_of_ker_le {F : Type*} [AddCommGroup F] [IsAddTorsionFree F]
    (δ : U →+ A) {n : ℕ} (hn : n ≠ 0) (hδn : ∀ u, δ (n • u) = 0)
    (hδ : ∀ u, δ u = 0 → ∃ v, n • v = u) (φ : U →+ F) (hφ : ∀ u, φ u = 0 → ∃ v, n • v = u)
    (σ : U →+ U) (hσ : ∀ u, φ (σ u) = φ u) (q : ℤ) :
    (δ '' {u : U | δ (σ u - q • u) = 0}).encard ≤
      (Set.univ : Set (φ.range ⧸ (zsmulAddGroupHom (α := φ.range) (q - 1)).range)).encard := by
  classical
  set d : ℤ := q - 1
  set g : ℕ := Int.gcd (n : ℤ) d
  have hg0 : g ≠ 0 := Int.gcd_ne_zero_left (by exact_mod_cast hn)
  obtain ⟨n', hn'⟩ : (g : ℤ) ∣ (n : ℤ) := Int.gcd_dvd_left _ _
  -- every `u ∈ W` has `g • φ u = n • z` for some `z ∈ φ(U)`
  have hz : ∀ u, δ (σ u - q • u) = 0 → ∃ z : φ.range, (g : ℤ) • φ u = (n : ℤ) • (z : F) :=
    fun u hu => exists_gcd_zsmul_eq_of_eigen δ hδ φ σ hσ q hu
  choose! z hzu using hz
  set Q := φ.range ⧸ (zsmulAddGroupHom (α := φ.range) (g : ℤ)).range
  -- `φ u = n' • z u`
  have hφz : ∀ u, δ (σ u - q • u) = 0 → φ u = n' • (z u : F) := by
    intro u hu
    have h := hzu u hu
    rw [hn', ← smul_smul] at h
    refine IsAddTorsionFree.nsmul_right_injective (M := F) hg0 ?_
    simpa only [← natCast_zsmul] using h
  -- the class of `z u` determines `δ u`
  let h : A → Q := fun a => if ha : ∃ u, δ (σ u - q • u) = 0 ∧ δ u = a then
    QuotientAddGroup.mk (z ha.choose) else 0
  have hEF : ∀ a₁ ∈ δ '' {u : U | δ (σ u - q • u) = 0}, ∀ a₂ ∈ δ '' {u : U | δ (σ u - q • u) = 0},
      h a₁ = h a₂ → a₁ - a₂ ∈ ({0} : Set A) := by
    rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ h12
    have e₁ : ∃ u, δ (σ u - q • u) = 0 ∧ δ u = δ u₁ := ⟨u₁, hu₁, rfl⟩
    have e₂ : ∃ u, δ (σ u - q • u) = 0 ∧ δ u = δ u₂ := ⟨u₂, hu₂, rfl⟩
    simp only [h, dif_pos e₁, dif_pos e₂] at h12
    obtain ⟨hw₁, hw₁'⟩ := e₁.choose_spec
    obtain ⟨hw₂, hw₂'⟩ := e₂.choose_spec
    obtain ⟨⟨t, ⟨y, rfl⟩⟩, ht⟩ := exists_sub_eq_zsmul_of_mk_eq h12
    have ht' : (z e₁.choose : F) - z e₂.choose = (g : ℤ) • φ y := congrArg Subtype.val ht
    have hφ12 : φ (e₁.choose - e₂.choose - n • y) = 0 := by
      rw [map_sub, map_sub, map_nsmul, hφz _ hw₁, hφz _ hw₂, ← zsmul_sub, ht', smul_smul,
        ← natCast_zsmul, hn', mul_comm, sub_self]
    obtain ⟨v, hv⟩ := hφ _ hφ12
    have : δ e₁.choose - δ e₂.choose = 0 := by
      rw [← map_sub, show e₁.choose - e₂.choose = n • (v + y) by rw [nsmul_add, hv]; abel, hδn]
    rw [← hw₁', ← hw₂', this, Set.mem_singleton_iff]
  refine (Set.encard_le_mul_of_sub_mem h hEF).trans ?_
  rw [Set.encard_singleton, mul_one]
  have hgd : (g : ℤ) ∣ d := Int.gcd_dvd_right _ _
  exact (Set.encard_le_encard (Set.subset_univ _)).trans
    (encard_univ_quotient_zsmul_le_of_dvd hgd)

/-- A finitely generated abelian group modulo `d` times itself is finite, for `d ≠ 0`. -/
theorem finite_quotient_range_zsmulAddGroupHom {G : Type*} [AddCommGroup G] [AddGroup.FG G]
    {d : ℤ} (hd : d ≠ 0) : Finite (G ⧸ (zsmulAddGroupHom (α := G) d).range) := by
  set Q := G ⧸ (zsmulAddGroupHom (α := G) d).range
  have : Module.Finite ℤ G := Module.Finite.iff_addGroup_fg.2 inferInstance
  have : Module.Finite ℤ Q := Module.Finite.of_surjective
    (QuotientAddGroup.mk' (zsmulAddGroupHom (α := G) d).range).toIntLinearMap
    (QuotientAddGroup.mk'_surjective _)
  refine Module.finite_of_fg_torsion Q fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  refine ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩, ?_⟩
  show d • (QuotientAddGroup.mk y : Q) = 0
  rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
  exact ⟨y, rfl⟩

/-- A subgroup of a finitely generated abelian group is finitely generated. -/
theorem addGroupFG_addSubgroup {G : Type*} [AddCommGroup G] [AddGroup.FG G]
    (H : AddSubgroup G) : AddGroup.FG H := by
  have : Module.Finite ℤ G := Module.Finite.iff_addGroup_fg.2 inferInstance
  have hfg : (AddSubgroup.toIntSubmodule H).FG := IsNoetherian.noetherian _
  have hfg' : H.FG := (Submodule.fg_iff_addSubgroup_fg _).1 hfg
  exact (AddGroup.fg_iff_addSubgroup_fg H).2 hfg'

/-- **Torsion through a surjection whose kernel is the image of a given group.** For
`r : P' ↠ P` with kernel `ψ(G)`, the `d`-torsion of `P` has at most `#(G / d G) · #P'[d]`
elements: `z = r w` gives `d • w = ψ(g)`, and the class of `g` modulo `d G` determines `z` up to
`r(P'[d])`. -/
theorem encard_torsion_le_mul_of_surjective {G : Type*} [AddCommGroup G] (r : P' →+ P)
    (hr : Function.Surjective r) (ψ : G →+ P') (hrψ : ∀ g, r (ψ g) = 0)
    (hψ : ∀ l, r l = 0 → ∃ g, ψ g = l) (d : ℤ) :
    {z : P | d • z = 0}.encard ≤ (Set.univ : Set (G ⧸
        (zsmulAddGroupHom (α := G) d).range)).encard * {w : P' | d • w = 0}.encard := by
  classical
  choose s hs using hr
  have hmem : ∀ z : P, d • z = 0 → ∃ g, ψ g = d • s z := fun z hz =>
    hψ _ (by rw [map_zsmul, hs, hz])
  let h : P → G ⧸ (zsmulAddGroupHom (α := G) d).range := fun z =>
    if hz : d • z = 0 then QuotientAddGroup.mk (hmem z hz).choose else 0
  refine (Set.encard_le_mul_of_sub_mem (F := r '' {w : P' | d • w = 0}) h ?_).trans ?_
  · intro z₁ hz₁ z₂ hz₂ h12
    simp only [h, dif_pos (show d • z₁ = 0 from hz₁), dif_pos (show d • z₂ = 0 from hz₂)] at h12
    have e₁ := (hmem z₁ hz₁).choose_spec
    have e₂ := (hmem z₂ hz₂).choose_spec
    obtain ⟨t, ht⟩ := exists_sub_eq_zsmul_of_mk_eq h12
    refine ⟨s z₁ - s z₂ - ψ t, ?_, ?_⟩
    · show d • (s z₁ - s z₂ - ψ t) = 0
      rw [zsmul_sub, zsmul_sub, ← map_zsmul, ← ht, map_sub, e₁, e₂]
      abel
    · rw [map_sub, map_sub, hs, hs, hrψ, sub_zero]
  · exact mul_le_mul' (Set.encard_le_encard (Set.subset_univ _)) (Set.encard_image_le _ _)

end Stacks.EigenvectorCount
