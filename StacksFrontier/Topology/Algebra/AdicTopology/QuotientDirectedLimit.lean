module

public import StacksFrontier.Topology.Algebra.AdicTopology.DirectedLimit

/-!
# The weakly admissible completion of a ring surjecting onto a directed system

Let `Λ` be a commutative ring, let `(R i)_{i ∈ I}` be a directed inverse system of commutative
rings whose transition maps have locally nilpotent kernels, and let `ρ i : Λ →+* R i` be a
compatible family of **surjections**. Then the inverse limit of the system is realized by a
commutative ring `A` *in the same universe as `Λ`*, namely the inverse limit of the quotients of
`Λ` by the kernels of the `ρ i`, and that ring is weakly admissible with the kernels of its
projections to the `R i` as a fundamental system of weak ideals of definition.

The point of taking the limit over the kernels rather than over `I` is size: `I` may live in a
larger universe than the rings, as it does for a presentation of a formal algebraic space, while
the kernels are ideals of `Λ` and so form a type in the universe of `Λ`. The two limits agree
because `i ↦ RingHom.ker (ρ i)` is antitone with directed image.

Surjectivity of the `ρ i` is what makes the projections out of the limit surjective — the
projections of an inverse limit of a directed system with surjective transition maps need not be
surjective, see `StacksFrontier/AlgebraicGeometry/FormalSpace/McQuillanSectionProjections.lean` —
and it is also what identifies the stage `R i` with the quotient `Λ ⧸ RingHom.ker (ρ i)`.

## Main definitions

* `TopologicalRing.StageIdeal`: the kernel of one of the given surjections, as an index ordered
  by reverse inclusion.

## Main results

* `TopologicalRing.exists_isWeaklyAdmissible_proj_of_surjective_family`: the inverse limit is a
  weakly admissible topological ring in the universe of `Λ`, with surjective projections to the
  stages whose kernels are weak ideals of definition basing the topology.
-/

@[expose] public noncomputable section

namespace TopologicalRing

open Filter

universe u v

variable {Λ : Type u} [CommRing Λ] {I : Type v} {R : I → Type u} [∀ i, CommRing (R i)]

/-- An ideal of `Λ` which is the kernel of one of a given family of homomorphisms out of `Λ`,
ordered by **reverse** inclusion so that the quotients form a directed diagram. This is the index
of the inverse limit of those quotients; it lives in the universe of `Λ`, whatever the universe
of the family's index. -/
structure StageIdeal (ρ : ∀ i : I, Λ →+* R i) : Type u where
  /-- The ideal. -/
  ideal : Ideal Λ
  /-- It is the kernel of one of the given homomorphisms. -/
  exists_ker_eq : ∃ i : I, RingHom.ker (ρ i) = ideal

namespace StageIdeal

variable {ρ : ∀ i : I, Λ →+* R i}

/-- Two indices are equal when their underlying ideals are equal. -/
@[ext]
theorem ext {x y : StageIdeal ρ} (h : x.ideal = y.ideal) : x = y := by
  cases x
  cases y
  subst h
  rfl

/-- Reverse inclusion of the underlying ideals. -/
instance instPreorder : Preorder (StageIdeal ρ) where
  le x y := y.ideal ≤ x.ideal
  le_refl _ := le_rfl
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁

/-- `x ≤ y` exactly when the ideal of `y` is contained in the ideal of `x`. -/
theorem le_def {x y : StageIdeal ρ} : x ≤ y ↔ y.ideal ≤ x.ideal := Iff.rfl

/-- The index attached to a member of the family. -/
def of (ρ : ∀ i : I, Λ →+* R i) (i : I) : StageIdeal ρ :=
  ⟨RingHom.ker (ρ i), ⟨i, rfl⟩⟩

/-- The ideal of the index attached to `i` is the kernel of `ρ i`. -/
@[simp]
theorem of_ideal (i : I) : (StageIdeal.of ρ i).ideal = RingHom.ker (ρ i) := rfl

/-- The transition homomorphisms of the diagram of quotients. -/
def factor {x y : StageIdeal ρ} (h : x ≤ y) : (Λ ⧸ y.ideal) →+* (Λ ⧸ x.ideal) :=
  Ideal.Quotient.factor (le_def.mp h)

/-- The transition homomorphism sends the class of `a` to the class of `a`. -/
@[simp]
theorem factor_mk {x y : StageIdeal ρ} (h : x ≤ y) (a : Λ) :
    factor h (Ideal.Quotient.mk y.ideal a) = Ideal.Quotient.mk x.ideal a :=
  Ideal.Quotient.factor_mk _ a

end StageIdeal

variable [Preorder I] {τ : ∀ ⦃i j : I⦄, i ≤ j → R j →+* R i} {ρ : ∀ i : I, Λ →+* R i}

/-- A compatible family of homomorphisms out of `Λ` has antitone kernels. -/
theorem ker_antitone_of_compat
    (hcompat : ∀ ⦃i j : I⦄ (h : i ≤ j) (x : Λ), τ h (ρ j x) = ρ i x) :
    Antitone fun i : I ↦ RingHom.ker (ρ i) := by
  intro i j h a ha
  refine RingHom.mem_ker.mpr ?_
  rw [← hcompat h a, RingHom.mem_ker.mp ha, map_zero]

/-- **The weakly admissible completion of a ring along a directed system of surjections.** Let a
commutative ring `Λ` surject compatibly onto a nonempty directed inverse system of commutative
rings whose transition maps have locally nilpotent kernels. Then the inverse limit of the system
is a commutative ring in the universe of `Λ`, weakly admissible for the limit topology, with
surjective projections onto the stages whose kernels are weak ideals of definition forming a
fundamental system of neighbourhoods of `0`. -/
theorem exists_isWeaklyAdmissible_proj_of_surjective_family [Nonempty I]
    [IsDirected I (· ≤ ·)]
    (hτnil : ∀ ⦃i j : I⦄ (h : i ≤ j), (RingHom.ker (τ h)).LocallyNilpotent)
    (hρ : ∀ i, Function.Surjective (ρ i))
    (hcompat : ∀ ⦃i j : I⦄ (h : i ≤ j) (x : Λ), τ h (ρ j x) = ρ i x) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A) (π : ∀ i : I, A →+* R i),
      TopologicalRing.IsWeaklyAdmissible A ∧
        (∀ i, Function.Surjective (π i)) ∧
        (∀ ⦃i j : I⦄ (h : i ≤ j) (a : A), τ h (π j a) = π i a) ∧
        (∀ i, TopologicalRing.IsWeakIdealOfDefinition (RingHom.ker (π i))) ∧
        (nhds (0 : A)).HasBasis (fun _ : I ↦ True)
          (fun i ↦ (RingHom.ker (π i) : Set A)) := by
  classical
  have hanti : Antitone fun i : I ↦ RingHom.ker (ρ i) := ker_antitone_of_compat hcompat
  have hne : Nonempty (StageIdeal ρ) := ⟨StageIdeal.of ρ (Classical.arbitrary I)⟩
  -- The index of the limit: the kernels, ordered by reverse inclusion.
  have hdir : IsDirected (StageIdeal ρ) (· ≤ ·) := by
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨i, hi⟩ := x.exists_ker_eq
    obtain ⟨j, hj⟩ := y.exists_ker_eq
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨StageIdeal.of ρ k, StageIdeal.le_def.mpr ((hanti hik).trans hi.le),
      StageIdeal.le_def.mpr ((hanti hjk).trans hj.le)⟩
  -- The transition maps of the diagram of quotients have locally nilpotent kernels.
  have hnil : ∀ ⦃x y : StageIdeal ρ⦄ (h : x ≤ y),
      (RingHom.ker (StageIdeal.factor (ρ := ρ) h)).LocallyNilpotent := by
    intro x y h z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨i, hi⟩ := x.exists_ker_eq
    obtain ⟨j, hj⟩ := y.exists_ker_eq
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    rw [RingHom.mem_ker, StageIdeal.factor_mk, Ideal.Quotient.eq_zero_iff_mem, ← hi,
      RingHom.mem_ker, ← hcompat hik a] at hz
    obtain ⟨n, hn⟩ := hτnil hik (ρ k a) (RingHom.mem_ker.mpr hz)
    refine ⟨n, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hj.le (hanti hjk (RingHom.mem_ker.mpr (by rwa [map_pow]))))
  let t : ∀ ⦃x y : StageIdeal ρ⦄, x ≤ y → (Λ ⧸ y.ideal) →+* (Λ ⧸ x.ideal) :=
    fun {_ _} h ↦ StageIdeal.factor (ρ := ρ) h
  let A := TopologicalRing.DirectedLimit t
  let κ : Λ →+* A := (RingHom.pi fun x : StageIdeal ρ ↦ Ideal.Quotient.mk x.ideal).codRestrict
    (DirectedLimit.subring t) fun a _ _ h ↦ StageIdeal.factor_mk h a
  let ε := fun i ↦ RingHom.quotientKerEquivOfSurjective (hρ i)
  have hε : ∀ (i : I) (a : Λ), ε i (Ideal.Quotient.mk (RingHom.ker (ρ i)) a) = ρ i a :=
    fun i a ↦ RingHom.quotientKerEquivOfSurjective_apply_mk (hρ i) a
  let π : ∀ i : I, A →+* R i := fun i ↦ (ε i).toRingHom.comp
    (DirectedLimit.proj t (StageIdeal.of ρ i))
  have hπ_surj : ∀ i, Function.Surjective (π i) := fun i y ↦
    let ⟨a, ha⟩ := hρ i y; ⟨κ a, (hε i a).trans ha⟩
  have hπ_ker : ∀ i : I,
      RingHom.ker (π i) = RingHom.ker (DirectedLimit.proj t (StageIdeal.of ρ i)) :=
    fun i ↦ RingHom.ker_comp_of_injective _ (ε i).injective
  have hπ_compat : ∀ ⦃i j : I⦄ (h : i ≤ j) (a : A), τ h (π j a) = π i a := by
    intro i j h a
    have hle : StageIdeal.of ρ i ≤ StageIdeal.of ρ j := StageIdeal.le_def.mpr (hanti h)
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (DirectedLimit.proj t (StageIdeal.of ρ j) a)
    change τ h (ε j (DirectedLimit.proj t (StageIdeal.of ρ j) a)) =
      ε i (DirectedLimit.proj t (StageIdeal.of ρ i) a)
    rw [← DirectedLimit.t_proj t hle a, ← hb, StageIdeal.factor_mk hle b]
    change τ h (ε j (Ideal.Quotient.mk (RingHom.ker (ρ j)) b)) =
      ε i (Ideal.Quotient.mk (RingHom.ker (ρ i)) b)
    rw [hε j b, hε i b, hcompat h b]
  refine ⟨A, inferInstanceAs (CommRing (TopologicalRing.DirectedLimit t)),
    inferInstanceAs (TopologicalSpace (TopologicalRing.DirectedLimit t)),
    inferInstanceAs (IsTopologicalRing (TopologicalRing.DirectedLimit t)),
    inferInstanceAs (IsLinearTopology (TopologicalRing.DirectedLimit t)
      (TopologicalRing.DirectedLimit t)), π,
    DirectedLimit.isWeaklyAdmissible t hnil, hπ_surj, hπ_compat, ?_, ?_⟩
  · intro i
    rw [hπ_ker i]
    exact DirectedLimit.isWeakIdealOfDefinition_ker t hnil (StageIdeal.of ρ i)
  · refine (DirectedLimit.hasBasis_nhds_zero t).to_hasBasis ?_ ?_
    · intro x _
      obtain ⟨i, hi⟩ := x.exists_ker_eq
      have hxi : StageIdeal.of ρ i = x := StageIdeal.ext (by rw [StageIdeal.of_ideal, hi])
      exact ⟨i, trivial, fun z hz ↦ by rwa [hπ_ker i, hxi] at hz⟩
    · exact fun i _ ↦ ⟨StageIdeal.of ρ i, trivial, fun z hz ↦ by rwa [hπ_ker i]⟩

end TopologicalRing

end
