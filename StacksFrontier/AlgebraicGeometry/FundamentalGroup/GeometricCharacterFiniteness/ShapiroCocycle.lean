module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The Shapiro cocycle of a character

Let `φ : G → Γ` be a homomorphism of groups, `H` a normal subgroup of `Γ` and `N = φ⁻¹(H)`.
The group `G` acts on the functions `Γ ⧸ H → A` by `(g • F)(x) = F(φ(g)⁻¹ • x)`, and `N` acts
trivially. A homomorphism `χ : N → A` gives a crossed homomorphism `C_χ : G → (Γ ⧸ H → A)`: on the
`G`-orbit of the trivial coset, choose for every coset `x` an element `s(x)` of `G` with
`φ(s(x)) H = x` and `s(H) = 1`, and put `C_χ(g)(x) = χ(s(x)⁻¹ g s(φ(g)⁻¹ • x))`; off the orbit put
`C_χ(g)(x) = 0`. Its value at the trivial coset recovers `χ` on `N`, and it is locally constant
when `G` is a topological group, `Γ ⧸ H` is finite and the kernel of `χ` is open in `G`. This is
the cocycle-level form of the map `H¹(N, A) → H¹(G, Coind A)` of Shapiro's lemma.

## Main definitions

* `Stacks.GroupCohomology.shapiroCocycle` — the crossed homomorphism `C_χ`.

## Main results

* `Stacks.GroupCohomology.shapiroCocycle_mul` — the crossed homomorphism identity.
* `Stacks.GroupCohomology.shapiroCocycle_apply_one` — `C_χ(n)(H) = χ(n)` for `n ∈ N`.
* `Stacks.GroupCohomology.isLocallyConstant_shapiroCocycle` — local constancy.
-/

@[expose] public noncomputable section

namespace Stacks.GroupCohomology

open scoped Pointwise

variable {G Γ : Type*} [Group G] [Group Γ] (φ : G →* Γ) (H : Subgroup Γ) [H.Normal]
  {A : Type*} [AddCommGroup A]

/-- An element of `H` fixes every coset of the normal subgroup `H`. -/
lemma smul_quotient_eq_of_mem_normal {h : Γ} (hh : h ∈ H) (x : Γ ⧸ H) : h • x = x := by
  induction x using QuotientGroup.induction_on with
  | H γ =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    have := (inferInstance : H.Normal).conj_mem _ (H.inv_mem hh) γ⁻¹
    simpa [mul_assoc] using this

/-- The cosets in the `G`-orbit of the trivial coset: those of the form `φ(t) H`. -/
def InImageOrbit (x : Γ ⧸ H) : Prop := ∃ t : G, ((φ t : Γ) : Γ ⧸ H) = x

omit [H.Normal] in
/-- The image orbit is stable under the action of `G`. -/
lemma inImageOrbit_smul_iff (g : G) (x : Γ ⧸ H) :
    InImageOrbit φ H ((φ g)⁻¹ • x) ↔ InImageOrbit φ H x := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨g * t, ?_⟩
    rw [map_mul, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, ht, smul_inv_smul]
  · rintro ⟨t, rfl⟩
    refine ⟨g⁻¹ * t, ?_⟩
    rw [map_mul, map_inv, ← smul_eq_mul, ← MulAction.Quotient.smul_mk]

/-- A section of `g ↦ φ(g) H` over the image orbit, taking the trivial coset to `1`. -/
def orbitSection (x : Γ ⧸ H) : G := by
  classical
  exact if x = ((1 : Γ) : Γ ⧸ H) then 1 else if h : InImageOrbit φ H x then h.choose else 1

lemma orbitSection_one : orbitSection φ H ((1 : Γ) : Γ ⧸ H) = 1 := by
  simp [orbitSection]

omit [H.Normal] in
lemma mk_orbitSection {x : Γ ⧸ H} (hx : InImageOrbit φ H x) :
    ((φ (orbitSection φ H x) : Γ) : Γ ⧸ H) = x := by
  classical
  unfold orbitSection
  split_ifs with h1
  · rw [h1, map_one]
  · exact hx.choose_spec

/-- `χ : N → A` extended by zero to `G`. -/
def charExt (χ : H.comap φ → A) (g : G) : A := by
  classical
  exact if h : g ∈ H.comap φ then χ ⟨g, h⟩ else 0

omit [H.Normal] in
lemma charExt_of_mem (χ : H.comap φ → A) {g : G} (hg : g ∈ H.comap φ) :
    charExt φ H χ g = χ ⟨g, hg⟩ := by
  simp [charExt, hg]

omit [H.Normal] in
lemma charExt_mul (χ : H.comap φ → A) (hχ : ∀ a b, χ (a * b) = χ a + χ b) {a b : G}
    (ha : a ∈ H.comap φ) (hb : b ∈ H.comap φ) :
    charExt φ H χ (a * b) = charExt φ H χ a + charExt φ H χ b := by
  rw [charExt_of_mem φ H χ ha, charExt_of_mem φ H χ hb, charExt_of_mem φ H χ (mul_mem ha hb)]
  exact hχ ⟨a, ha⟩ ⟨b, hb⟩

omit [H.Normal] in
/-- The element `s(x)⁻¹ g s(φ(g)⁻¹ • x)` lies in `N` for `x` in the image orbit. -/
lemma orbitSection_mul_mem {x : Γ ⧸ H} (hx : InImageOrbit φ H x) (g : G) :
    (orbitSection φ H x)⁻¹ * g * orbitSection φ H ((φ g)⁻¹ • x) ∈ H.comap φ := by
  have h1 := mk_orbitSection φ H ((inImageOrbit_smul_iff φ H g x).2 hx)
  have h2 := mk_orbitSection φ H hx
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, mul_assoc, ← QuotientGroup.eq, h2,
    ← smul_eq_mul, ← MulAction.Quotient.smul_mk, h1, smul_inv_smul]

/-- **The Shapiro cocycle** `C_χ(g)(x) = χ(s(x)⁻¹ g s(φ(g)⁻¹ • x))` on the image orbit, `0` off
it. -/
def shapiroCocycle (χ : H.comap φ → A) (g : G) (x : Γ ⧸ H) : A := by
  classical
  exact if InImageOrbit φ H x then
    charExt φ H χ ((orbitSection φ H x)⁻¹ * g * orbitSection φ H ((φ g)⁻¹ • x)) else 0

omit [H.Normal] in
/-- **The crossed homomorphism identity** `C(gh)(x) = C(h)(φ(g)⁻¹ • x) + C(g)(x)`. -/
theorem shapiroCocycle_mul (χ : H.comap φ → A) (hχ : ∀ a b, χ (a * b) = χ a + χ b)
    (g h : G) (x : Γ ⧸ H) :
    shapiroCocycle φ H χ (g * h) x =
      shapiroCocycle φ H χ h ((φ g)⁻¹ • x) + shapiroCocycle φ H χ g x := by
  classical
  by_cases hx : InImageOrbit φ H x
  · have hy := (inImageOrbit_smul_iff φ H g x).2 hx
    simp only [shapiroCocycle, hx, hy, ↓reduceIte]
    rw [add_comm, ← charExt_mul φ H χ hχ (orbitSection_mul_mem φ H hx g)
        (orbitSection_mul_mem φ H hy h)]
    congr 1
    rw [map_mul, mul_inv_rev, mul_smul]
    simp only [mul_assoc, mul_inv_cancel_left]
  · have hy : ¬ InImageOrbit φ H ((φ g)⁻¹ • x) := fun h' ↦ hx ((inImageOrbit_smul_iff φ H g x).1 h')
    unfold shapiroCocycle
    simp only [hx, hy, ↓reduceIte, add_zero]

/-- **The Shapiro cocycle recovers the character**: `C_χ(n)(H) = χ(n)` for `n ∈ N`. -/
theorem shapiroCocycle_apply_one (χ : H.comap φ → A) {n : G} (hn : n ∈ H.comap φ) :
    shapiroCocycle φ H χ n ((1 : Γ) : Γ ⧸ H) = χ ⟨n, hn⟩ := by
  classical
  have h1 : InImageOrbit φ H ((1 : Γ) : Γ ⧸ H) := ⟨1, by rw [map_one]⟩
  have h2 : (φ n)⁻¹ • ((1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H) :=
    smul_quotient_eq_of_mem_normal H (H.inv_mem hn) _
  simp only [shapiroCocycle, h1, ↓reduceIte, h2, orbitSection_one, inv_one, one_mul, mul_one]
  exact charExt_of_mem φ H χ hn

/-- **The Shapiro cocycle is locally constant** when `G` is a topological group, `Γ ⧸ H` is
finite and the kernel `{n ∈ N | χ(n) = 0}` is open in `G`. -/
theorem isLocallyConstant_shapiroCocycle [TopologicalSpace G] [IsTopologicalGroup G]
    [Finite (Γ ⧸ H)] (χ : H.comap φ → A) (hχ : ∀ a b, χ (a * b) = χ a + χ b)
    (hker : IsOpen {g : G | ∃ h : g ∈ H.comap φ, χ ⟨g, h⟩ = 0}) :
    IsLocallyConstant (shapiroCocycle φ H χ) := by
  classical
  set K : Set G := {g : G | ∃ h : g ∈ H.comap φ, χ ⟨g, h⟩ = 0}
  let U : Set G := ⋂ x : Γ ⧸ H,
    (fun m ↦ (orbitSection φ H x)⁻¹ * m * orbitSection φ H x) ⁻¹' K
  have hU : IsOpen U := isOpen_iInter_of_finite fun x ↦ hker.preimage (by fun_prop)
  have h1U : (1 : G) ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_preimage, mul_one, inv_mul_cancel]
    intro _
    refine ⟨Subgroup.one_mem _, ?_⟩
    have h11 := hχ 1 1
    rw [mul_one, left_eq_add] at h11
    exact h11
  have hzero : ∀ m ∈ U, shapiroCocycle φ H χ m = 0 := by
    intro m hm
    have hmK : m ∈ K := by
      have := Set.mem_iInter.1 hm ((1 : Γ) : Γ ⧸ H)
      rw [Set.mem_preimage, orbitSection_one, inv_one, one_mul, mul_one] at this
      exact this
    obtain ⟨hmN, -⟩ := hmK
    funext y
    by_cases hy : InImageOrbit φ H y
    · simp only [shapiroCocycle, hy, ↓reduceIte, Pi.zero_apply]
      rw [smul_quotient_eq_of_mem_normal H (H.inv_mem hmN)]
      obtain ⟨hN, h0⟩ := Set.mem_iInter.1 hm y
      rw [charExt_of_mem φ H χ hN]
      exact h0
    · simp [shapiroCocycle, hy]
  have hmul : ∀ g, ∀ m ∈ U, shapiroCocycle φ H χ (g * m) = shapiroCocycle φ H χ g := by
    intro g m hm
    funext x
    rw [shapiroCocycle_mul φ H χ hχ, hzero m hm, Pi.zero_apply, zero_add]
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun y ↦ g⁻¹ * y) ⁻¹' U, hU.preimage (by fun_prop), by simpa using h1U, ?_⟩
  intro y hy
  have := hmul g (g⁻¹ * y) hy
  rwa [mul_inv_cancel_left] at this

omit [AddCommGroup A] in
/-- `N` acts trivially on the functions `Γ ⧸ H → A`. -/
lemma comp_smul_eq_of_mem (F : Γ ⧸ H → A) {n : G} (hn : n ∈ H.comap φ) :
    (fun x ↦ F ((φ n)⁻¹ • x)) = F := by
  funext x
  rw [smul_quotient_eq_of_mem_normal H (H.inv_mem hn)]

end Stacks.GroupCohomology
