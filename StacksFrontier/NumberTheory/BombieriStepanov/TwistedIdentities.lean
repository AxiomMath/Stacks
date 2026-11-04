module

public import StacksFrontier.NumberTheory.BombieriStepanov.HomCount
public import StacksFrontier.NumberTheory.BombieriStepanov.HomExtension
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The counting identities of the lower bound, for points with values in a field

Let `B` be a ring containing a finite field `E` of constants, let `G` be a finite group of ring
automorphisms of `B`, and let `ι : E → Ω` be an embedding into an algebraically closed field of
characteristic `p`. The points of `B` over `ι` are the ring homomorphisms `φ : B → Ω` restricting
to `ι` on `E`. For `Q = p ^ n` a power of `#E` and `σ ∈ G`, a point is *`σ`-twisted* when
`φ ∘ σ = Frob_Q ∘ φ`; their number is the twisted count `N_σ`.

Two identities hold, for the group `G'` of elements of `G` fixing `E` and a subgroup `H`:

* if `B` is integral over the polynomial ring `E[x] ⊆ B` and `G` is transitive on the points
  with a given restriction to `k[x]`, then `∑_{σ ∈ G'} N_σ = |G'| · Q`
  (`Stacks.BombieriStepanov.sum_twistedCount_eq`);
* if `G` restricted to `H` is transitive on the points with a given restriction to a subring
  `B_H` fixed by `H`, then `∑_{σ ∈ H ∩ G'} N_σ ≤ |H ∩ G'| · #{ψ : B_H → Ω | Frob_Q ∘ ψ = ψ}`
  (`Stacks.BombieriStepanov.sum_twistedCount_le`).

Both are `Stacks.BombieriStepanov.sum_ncard_twisted_eq` for the action `σ • φ = φ ∘ σ⁻¹` of
`G'`, which preserves the points because elements of `G'` fix `E`. The hypothesis `hE`, that the
elements `b` of `B` with `b ^ #E = b` are constants, makes every element of `G` carrying one
point to another fix `E`: such an element permutes the constants, and `ι` is injective.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.BombieriStepanov

variable (B : Type*) {Ω E : Type*} [CommRing B] [Field Ω] [Field E] [Algebra E B] (ι : E →+* Ω)

/-- The points of `B` with values in `Ω` over the embedding `ι` of the constants. -/
abbrev PointsOver : Type _ := {φ : B →+* Ω // φ.comp (algebraMap E B) = ι}

variable (E) (G : Type*) [Group G] [MulSemiringAction G B]

/-- The elements of `G` fixing the constants `E ⊆ B`. -/
def constantFixing : Subgroup G where
  carrier := {g | ∀ e : E, g • algebraMap E B e = algebraMap E B e}
  mul_mem' {a b} ha hb e := by
    rw [mul_smul, hb e, ha e]
  one_mem' e := one_smul G _
  inv_mem' {a} ha e := by
    rw [inv_smul_eq_iff, ha e]

variable {E G}

/-- The twisted count `N_σ`: the points `φ` over `ι` with `φ ∘ σ = Frob_Q ∘ φ`. -/
def twistedCount (Q : ℕ) (σ : G) : ℕ :=
  {φ : PointsOver B ι | ∀ b : B, φ.1 (σ • b) = φ.1 b ^ Q}.ncard

variable {B ι}

/-- An element carrying a point over `ι` to another one fixes the constants, when the constants
are exactly the solutions of `b ^ qE = b`. -/
theorem mem_constantFixing_of_comp {qE : ℕ} (hqE : ∀ e : E, e ^ qE = e)
    (hE : ∀ b : B, b ^ qE = b → ∃ e : E, algebraMap E B e = b) {φ φ' : PointsOver B ι} {g : G}
    (hg : ∀ b, φ'.1 b = φ.1 (g • b)) : g ∈ constantFixing B E G := by
  intro e
  obtain ⟨e', he'⟩ := hE (g • algebraMap E B e) (by rw [← smul_pow', ← map_pow, hqE])
  have h1 : ι e' = ι e := by
    have h := hg (algebraMap E B e)
    rw [← he'] at h
    have h2 := congrArg (fun f : E →+* Ω => f e') φ.2
    have h3 := congrArg (fun f : E →+* Ω => f e) φ'.2
    simp only [RingHom.comp_apply] at h2 h3
    rw [← h2, ← h3, h]
  rw [← he', ι.injective h1]

/-- The action `σ • φ = φ ∘ σ⁻¹` of a group of automorphisms fixing the constants on the points
over `ι`. -/
@[reducible] def pointsAction (S : Subgroup G) (hS : S ≤ constantFixing B E G) :
    MulAction S (PointsOver B ι) where
  smul σ φ := ⟨φ.1.comp (MulSemiringAction.toRingHom G B ((σ⁻¹ : S) : G)), by
    ext e
    simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
    rw [hS (σ⁻¹ : S).2 e]
    exact congrArg (fun f : E →+* Ω => f e) φ.2⟩
  one_smul φ := Subtype.ext <| RingHom.ext fun b =>
    show φ.1 ((((1 : S)⁻¹ : S) : G) • b) = φ.1 b by simp
  mul_smul σ τ φ := Subtype.ext <| RingHom.ext fun b =>
    show φ.1 ((((σ * τ)⁻¹ : S) : G) • b) = φ.1 (((τ⁻¹ : S) : G) • (((σ⁻¹ : S) : G) • b)) by
      simp only [mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]

/-- If `g ∈ S` carries a point `w` to `w'`, then some element of `S` carries `w` to `w'`. -/
private theorem exists_smul_eq_of_comp (S : Subgroup G) (hS : S ≤ constantFixing B E G)
    {w w' : PointsOver B ι} {g : G} (hgS : g ∈ S) (hg : ∀ b, w'.1 b = w.1 (g • b)) :
    letI := pointsAction (ι := ι) S hS
    ∃ σ : S, σ • w = w' := by
  let := pointsAction (ι := ι) S hS
  refine ⟨(⟨g, hgS⟩ : S)⁻¹, Subtype.ext <| RingHom.ext fun b => ?_⟩
  change w.1 ((((⟨g, hgS⟩ : S)⁻¹⁻¹ : S) : G) • b) = w'.1 b
  rw [inv_inv, hg]

section Action

variable (p n : ℕ) [Fact p.Prime] [CharP Ω p]

/-- The `Q`-Frobenius `φ ↦ Frob_Q ∘ φ` on the points over `ι`, for `Q = p ^ n` a power of `#E`. -/
def pointsFrobenius (hQE : ∀ e : E, e ^ (p ^ n) = e) (φ : PointsOver B ι) : PointsOver B ι :=
  ⟨(iterateFrobenius Ω p n).comp φ.1, by
    ext e
    have h := congrArg (fun f : E →+* Ω => f e) φ.2
    simp only [RingHom.comp_apply] at h ⊢
    rw [h, iterateFrobenius_def, ← map_pow, hQE]⟩

/-- A point is fixed by the `Q`-Frobenius if and only if all its values satisfy `a ^ Q = a`. -/
theorem pointsFrobenius_eq_self_iff (hQE : ∀ e : E, e ^ (p ^ n) = e) (φ : PointsOver B ι) :
    pointsFrobenius p n hQE φ = φ ↔ ∀ b, φ.1 b ^ (p ^ n) = φ.1 b :=
  ⟨fun h b => by
    simpa [pointsFrobenius, iterateFrobenius_def] using
      congrArg (fun χ : PointsOver B ι => χ.1 b) h,
  fun h => Subtype.ext <| RingHom.ext fun b => by
    simpa [pointsFrobenius, iterateFrobenius_def] using h b⟩

/-- For `σ` in a group of automorphisms fixing the constants, the `Q`-Frobenius of a point `φ`
equals `σ • φ` if and only if `φ (σ⁻¹ • b) = φ b ^ Q` for every `b : B`. -/
theorem pointsFrobenius_eq_smul_iff (hQE : ∀ e : E, e ^ (p ^ n) = e) (S : Subgroup G)
    (hS : S ≤ constantFixing B E G) (σ : S) (φ : PointsOver B ι) :
    letI := pointsAction (ι := ι) S hS
    pointsFrobenius p n hQE φ = σ • φ ↔ ∀ b : B, φ.1 (((σ⁻¹ : S) : G) • b) = φ.1 b ^ (p ^ n) := by
  let := pointsAction (ι := ι) S hS
  refine ⟨fun h b => ?_, fun h => ?_⟩
  · have := congrArg (fun ψ : PointsOver B ι => ψ.1 b) h
    simp only [pointsFrobenius, RingHom.comp_apply, iterateFrobenius_def] at this
    exact this.symm
  · ext b
    simp only [pointsFrobenius, RingHom.comp_apply, iterateFrobenius_def]
    exact (h b).symm

/-- The twisted counts summed over a group of automorphisms fixing the constants are the counts
of `Stacks.BombieriStepanov.sum_ncard_twisted_eq` for the action `σ • φ = φ ∘ σ⁻¹`. -/
theorem sum_twistedCount_eq_sum_ncard (hQE : ∀ e : E, e ^ (p ^ n) = e) (S : Subgroup G)
    (hS : S ≤ constantFixing B E G) [Fintype S] :
    letI := pointsAction (ι := ι) S hS
    ∑ σ : S, twistedCount B ι (p ^ n) (σ : G) =
      ∑ σ : S, {φ : PointsOver B ι | pointsFrobenius p n hQE φ = σ • φ}.ncard := by
  let := pointsAction (ι := ι) S hS
  refine Fintype.sum_equiv (Equiv.inv S) _ _ (fun σ => ?_)
  unfold twistedCount
  congr 1
  ext φ
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, pointsFrobenius_eq_smul_iff]
  simp

/-- A homomorphism into a field with finite image has maximal kernel. -/
theorem isMaximal_ker_of_finite_range {R : Type*} [CommRing R] (f : R →+* Ω)
    (hf : (Set.range f).Finite) : (RingHom.ker f).IsMaximal := by
  have : Finite f.range := hf
  exact Ideal.Quotient.maximal_of_isField _
    ((RingHom.quotientKerEquivRange f).toMulEquiv.isField (Finite.isField_of_domain _))

/-- A point of `E[x]` over `ι` is determined by its value at `x`. -/
theorem pointsOver_polynomial_ext {ψ ψ' : PointsOver E[X] ι} (h : ψ.1 X = ψ'.1 X) : ψ = ψ' := by
  refine Subtype.ext (Polynomial.ringHom_ext (fun e => ?_) h)
  have he := congrArg (fun f : E →+* Ω => f e) ψ.2
  have he' := congrArg (fun f : E →+* Ω => f e) ψ'.2
  simp only [RingHom.comp_apply, Polynomial.algebraMap_eq] at he he'
  rw [he, he']

/-- A point of `E[x]` over `ι` is fixed by the `Q`-Frobenius if and only if its value `a` at `x`
satisfies `a ^ Q = a`. -/
theorem pointsFrobenius_eq_self_iff_pow_X (hQE : ∀ e : E, e ^ (p ^ n) = e)
    (ψ : PointsOver E[X] ι) : pointsFrobenius p n hQE ψ = ψ ↔ ψ.1 X ^ (p ^ n) = ψ.1 X :=
  ⟨fun h => (pointsFrobenius_eq_self_iff p n hQE ψ).1 h X, fun h =>
    pointsOver_polynomial_ext (by simpa [pointsFrobenius, iterateFrobenius_def] using h)⟩

/-- The points of `E[x]` over `ι` fixed by the `Q`-Frobenius are finite in number. -/
theorem finite_setOf_pointsFrobenius_eq_self (hn : n ≠ 0) (hQE : ∀ e : E, e ^ (p ^ n) = e) :
    {ψ : PointsOver E[X] ι | pointsFrobenius p n hQE ψ = ψ}.Finite := by
  have hp1 : 1 < p ^ n := Nat.one_lt_pow hn (Fact.out : p.Prime).one_lt
  refine Set.Finite.of_finite_image
    ((setOf_pow_eq_self_finite_ncard_le (Ω := Ω) hp1).1.subset ?_)
    (fun _ _ _ _ h => pointsOver_polynomial_ext h)
  rintro _ ⟨ψ, hψ, rfl⟩
  exact (pointsFrobenius_eq_self_iff_pow_X p n hQE ψ).1 hψ

/-- There are exactly `Q` points of `E[x]` over `ι` fixed by the `Q`-Frobenius. -/
theorem ncard_setOf_pointsFrobenius_eq_self [IsAlgClosed Ω] (hn : n ≠ 0)
    (hQE : ∀ e : E, e ^ (p ^ n) = e) :
    {ψ : PointsOver E[X] ι | pointsFrobenius p n hQE ψ = ψ}.ncard = p ^ n := by
  rw [← ncard_setOf_pow_eq_self (Ω := Ω) p hn]
  refine Set.ncard_congr (fun ψ _ => ψ.1 X)
    (fun ψ hψ => (pointsFrobenius_eq_self_iff_pow_X p n hQE ψ).1 hψ)
    (fun _ _ _ _ h => pointsOver_polynomial_ext h) (fun a ha => ?_)
  refine ⟨⟨Polynomial.eval₂RingHom ι a, ?_⟩,
    (pointsFrobenius_eq_self_iff_pow_X p n hQE _).2 (by simpa using ha), by simp⟩
  ext e
  simp [Polynomial.algebraMap_eq]

/-- A point of `E[x]` over `ι` fixed by the `Q`-Frobenius extends to a point of a ring `B`
integral over `E[x]`. -/
theorem exists_comp_eq_of_pointsFrobenius_eq_self [IsAlgClosed Ω] (hn : n ≠ 0)
    (hQE : ∀ e : E, e ^ (p ^ n) = e) [Algebra E[X] B] [IsScalarTower E E[X] B]
    [Algebra.IsIntegral E[X] B] (hinj : Function.Injective (algebraMap E[X] B))
    {ψ : PointsOver E[X] ι} (hψ : pointsFrobenius p n hQE ψ = ψ) :
    ∃ φ : PointsOver B ι, φ.1.comp (algebraMap E[X] B) = ψ.1 := by
  have hp1 : 1 < p ^ n := Nat.one_lt_pow hn (Fact.out : p.Prime).one_lt
  have : (RingHom.ker ψ.1).IsMaximal := isMaximal_ker_of_finite_range ψ.1
    ((setOf_pow_eq_self_finite_ncard_le (Ω := Ω) hp1).1.subset (by
      rintro _ ⟨r, rfl⟩
      exact (pointsFrobenius_eq_self_iff p n hQE ψ).1 hψ r))
  obtain ⟨φ₀, hφ₀⟩ := exists_comp_algebraMap_eq hinj ψ.1
  refine ⟨⟨φ₀, ?_⟩, hφ₀⟩
  rw [IsScalarTower.algebraMap_eq E E[X] B, ← RingHom.comp_assoc, hφ₀]
  exact ψ.2

/-- **The first counting identity.** Let `B` contain the polynomial ring `E[x]` (through an
injective map) and be integral over it, let `G` fix `x`, and let `G` be transitive on the points
with a given restriction to `E[x]` that is fixed by `Frob_Q`. Then the twisted counts of the
elements of `G` fixing the constants add up to `|G'| · Q`. -/
theorem sum_twistedCount_eq [IsAlgClosed Ω] (hn : n ≠ 0) (hQE : ∀ e : E, e ^ (p ^ n) = e)
    {qE : ℕ} (hqE : ∀ e : E, e ^ qE = e)
    (hE : ∀ b : B, b ^ qE = b → ∃ e : E, algebraMap E B e = b)
    [Algebra E[X] B] [IsScalarTower E E[X] B] [Algebra.IsIntegral E[X] B]
    (hinj : Function.Injective (algebraMap E[X] B))
    (hGx : ∀ g : G, g • algebraMap E[X] B X = algebraMap E[X] B X)
    (htr : ∀ φ φ' : B →+* Ω,
      (∀ r : E[X], φ (algebraMap E[X] B r) ^ (p ^ n) = φ (algebraMap E[X] B r)) →
      φ.comp (algebraMap E[X] B) = φ'.comp (algebraMap E[X] B) →
        ∃ g : G, ∀ b, φ' b = φ (g • b))
    [Fintype (constantFixing B E G)] :
    ∑ σ : constantFixing B E G, twistedCount B ι (p ^ n) (σ : G) =
      Fintype.card (constantFixing B E G) * p ^ n := by
  let := pointsAction (ι := ι) (constantFixing B E G) le_rfl
  have hfixP : ∀ σ ∈ (constantFixing B E G), ∀ r : E[X],
      σ • algebraMap E[X] B r = algebraMap E[X] B r := by
    intro σ hσ r
    have h := Polynomial.ringHom_ext (f := (MulSemiringAction.toRingHom G B σ).comp
      (algebraMap E[X] B)) (g := algebraMap E[X] B) (fun e => by
        simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
        rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact hσ e) (by simpa using hGx σ)
    exact congrArg (fun f : E[X] →+* B => f r) h
  let ρ : PointsOver B ι → PointsOver E[X] ι := fun φ =>
    ⟨φ.1.comp (algebraMap E[X] B), by
      rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
      exact φ.2⟩
  have key := sum_ncard_twisted_eq (H := (constantFixing B E G)) ρ (pointsFrobenius p n hQE)
    (pointsFrobenius p n hQE) (fun φ => rfl)
    (fun σ φ => Subtype.ext <| RingHom.ext fun r => by
      show φ.1 (((σ⁻¹ : (constantFixing B E G)) : G) • algebraMap E[X] B r) =
        φ.1 (algebraMap E[X] B r)
      rw [hfixP _ (σ⁻¹ : (constantFixing B E G)).2])
    (fun w w' hw hww' => by
      obtain ⟨g, hg⟩ := htr w.1 w'.1 ((pointsFrobenius_eq_self_iff p n hQE (ρ w)).1 hw)
        (congrArg Subtype.val hww')
      exact exists_smul_eq_of_comp _ le_rfl (mem_constantFixing_of_comp hqE hE hg) hg)
    (finite_setOf_pointsFrobenius_eq_self p n hn hQE)
  refine (sum_twistedCount_eq_sum_ncard (ι := ι) p n hQE (constantFixing B E G) le_rfl).trans ?_
  have hD : {ψ | pointsFrobenius p n hQE ψ = ψ} ∩ Set.range ρ =
      {ψ | pointsFrobenius p n hQE ψ = ψ} :=
    Set.inter_eq_left.2 fun ψ hψ =>
      (exists_comp_eq_of_pointsFrobenius_eq_self p n hn hQE hinj hψ).imp fun _ => Subtype.ext
  rw [key, hD, ncard_setOf_pointsFrobenius_eq_self p n hn hQE]

/-- **The second counting identity.** Let `B_H` be a ring over a subfield `k ⊆ E` mapping to `B`
into the invariants of a subgroup `H`, and let `H` be transitive on the points of `B` with a given
Frobenius-fixed restriction to `B_H`. Then the twisted counts of the elements of `H` fixing the
constants add up to at most `|H ∩ G'|` times the number of Frobenius-fixed points of `B_H` over
`k`. -/
theorem sum_twistedCount_le {k BH : Type*} [Field k] [CommRing BH] [Algebra k E] [Algebra k BH]
    [Algebra k B] [Algebra BH B] [IsScalarTower k E B] [IsScalarTower k BH B]
    (hQE : ∀ e : E, e ^ (p ^ n) = e) {qE : ℕ} (hqE : ∀ e : E, e ^ qE = e)
    (hE : ∀ b : B, b ^ qE = b → ∃ e : E, algebraMap E B e = b) (H : Subgroup G)
    (hH : ∀ h ∈ H, ∀ c : BH, h • algebraMap BH B c = algebraMap BH B c)
    (htr : ∀ φ φ' : B →+* Ω,
      (∀ c : BH, φ (algebraMap BH B c) ^ (p ^ n) = φ (algebraMap BH B c)) →
      φ.comp (algebraMap BH B) = φ'.comp (algebraMap BH B) →
        ∃ g ∈ H, ∀ b, φ' b = φ (g • b))
    (hD : {ψ : PointsOver BH (ι.comp (algebraMap k E)) |
      ∀ c, ψ.1 c ^ (p ^ n) = ψ.1 c}.Finite)
    [Fintype (H ⊓ constantFixing B E G : Subgroup G)] :
    ∑ σ : (H ⊓ constantFixing B E G : Subgroup G), twistedCount B ι (p ^ n) (σ : G) ≤
      Fintype.card (H ⊓ constantFixing B E G : Subgroup G) *
        {ψ : PointsOver BH (ι.comp (algebraMap k E)) | ∀ c, ψ.1 c ^ (p ^ n) = ψ.1 c}.ncard := by
  let := pointsAction (ι := ι) (H ⊓ constantFixing B E G) inf_le_right
  let ρ : PointsOver B ι → PointsOver BH (ι.comp (algebraMap k E)) := fun φ =>
    ⟨φ.1.comp (algebraMap BH B), by
      rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq k E B,
        ← RingHom.comp_assoc, φ.2]⟩
  have hQk : ∀ c : k, c ^ (p ^ n) = c := fun c =>
    (algebraMap k E).injective (by rw [map_pow, hQE])
  have hset : {ψ | pointsFrobenius p n hQk ψ = ψ} = {ψ : PointsOver BH (ι.comp (algebraMap k E)) |
      ∀ c, ψ.1 c ^ (p ^ n) = ψ.1 c} := Set.ext (pointsFrobenius_eq_self_iff p n hQk)
  have key := sum_ncard_twisted_eq (H := (H ⊓ constantFixing B E G : Subgroup G)) ρ
    (pointsFrobenius p n hQE) (pointsFrobenius p n hQk) (fun φ => rfl)
    (fun σ φ => Subtype.ext <| RingHom.ext fun c => by
      show φ.1 ((((σ⁻¹ : (H ⊓ constantFixing B E G : Subgroup G)) : G)) •
        algebraMap BH B c) = φ.1 (algebraMap BH B c)
      rw [hH _ (σ⁻¹ : (H ⊓ constantFixing B E G : Subgroup G)).2.1])
    (fun w w' hw hww' => by
      have hfix := (pointsFrobenius_eq_self_iff p n hQk (ρ w)).1 hw
      obtain ⟨g, hgH, hg⟩ := htr w.1 w'.1 hfix (congrArg Subtype.val hww')
      exact exists_smul_eq_of_comp _ inf_le_right ⟨hgH, mem_constantFixing_of_comp hqE hE hg⟩ hg)
    (hset ▸ hD)
  refine (sum_twistedCount_eq_sum_ncard (ι := ι) p n hQE (H ⊓ constantFixing B E G)
    inf_le_right).trans_le ?_
  rw [key, ← hset]
  exact Nat.mul_le_mul_left _ (Set.ncard_le_ncard Set.inter_subset_left (hset ▸ hD))

end Action

end Stacks.BombieriStepanov

end
