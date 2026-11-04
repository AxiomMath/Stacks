module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.RingTheory.Nilpotent.Ideal
public import StacksFrontier.SetTheory.Cardinal.SizeBound
import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes

/-!
# Countably indexed affine formal algebraic spaces as formal spectra (Stacks 0AN1)

Let `S` be a scheme contained in a big fppf site `B` and let `X` be an fppf sheaf over `S`.
**Stacks 0AN1** lists five equivalent descriptions of `X`:

1. `X` is a countably indexed affine formal algebraic space;
2. `X = Spf A` for a weakly admissible topological `S`-algebra `A` having a countable
   fundamental system of neighbourhoods of `0`;
3. `X = Spf A` for a weakly admissible topological `S`-algebra `A` having a fundamental system
   of neighbourhoods of `0` consisting of a descending chain `A ⊇ I₁ ⊇ I₂ ⊇ ⋯` of weak ideals
   of definition;
4. `X = Spf A` for a complete topological `S`-algebra `A` whose topology comes from a descending
   chain `A ⊇ I₁ ⊇ I₂ ⊇ ⋯` of ideals with `Iₙ/Iₙ₊₁` locally nilpotent;
5. `X = Spf A` for `A = lim R/Jₙ` with the limit topology, where `R ⊇ J₁ ⊇ J₂ ⊇ ⋯` are ideals
   of an `S`-algebra `R` with `Jₙ/Jₙ₊₁` locally nilpotent.

## Main definitions

* `AlgebraicGeometry.FormalSpace.SpfPresentation`: a topological ring over `S` together with an
  identification of `X` with its formal spectrum; the datum common to conditions (2)–(5).
* `AlgebraicGeometry.FormalSpace.IsCountablyIndexedAffine`: condition (1).
* `AlgebraicGeometry.FormalSpace.HasCountableWeakPresentation`: condition (2).
* `AlgebraicGeometry.FormalSpace.HasWeakIdealChain`: condition (3).
* `AlgebraicGeometry.FormalSpace.HasNilpotentIdealChain`: condition (4).
* `AlgebraicGeometry.FormalSpace.IsLimitOfNilpotentQuotients`: condition (5).

## Main results

* `AlgebraicGeometry.FormalSpace.hasCountableWeakPresentation_iff_hasWeakIdealChain`:
  conditions (2) and (3) are equivalent.
* `AlgebraicGeometry.FormalSpace.hasWeakIdealChain_iff_hasNilpotentIdealChain`:
  conditions (3) and (4) are equivalent.
* `AlgebraicGeometry.FormalSpace.isLimitOfNilpotentQuotients_of_hasWeakIdealChain`:
  condition (3) implies condition (5).
* `AlgebraicGeometry.FormalSpace.hasCountableWeakPresentation_of_isLimitOfNilpotentQuotients`:
  condition (5) implies condition (2).
* `AlgebraicGeometry.FormalSpace.isCountablyIndexedAffine_of_hasCountableWeakPresentation`:
  condition (2) implies condition (1).
* `AlgebraicGeometry.FormalSpace.hasCountableWeakPresentation_of_isCountablyIndexedAffine`:
  condition (1) implies condition (2).
* `AlgebraicGeometry.FormalSpace.isCountablyIndexedAffine_tfae`: all five conditions are
  equivalent.

## Implementation notes

The implication (1) ⇒ (2) is the one step of the source's proof that appeals to the
equivalence of the five conditions of **Stacks 0AIC**, in the direction (4) ⇒ (1): a
countably indexed `X` is the formal spectrum of the limit of the section rings of a sequential
presentation, which is
`AlgebraicGeometry.FormalSpace.exists_quotientSystem_of_isCountablyIndexed` (**Stacks 0AIK**,
item (6)). Together with the cycle (2) ⇒ (1) and the chain (2) ⇔ (3) ⇔ (4) ⇒ (5) ⇒ (2) proved
here, all five conditions are equivalent.

The source writes `X = Spf A`; here that equality is an isomorphism of fppf sheaves, recorded
together with the ring and its `AlgebraicGeometry.FormalSpace.QuotientSystem` in
`SpfPresentation`. As in `StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum`, a
topological ring over a possibly non-affine `S` carries structure morphisms on its quotient
spectra rather than a single morphism from `Spec A`, so "topological `S`-algebra" unfolds to a
`QuotientSystem`; for the untopologized ring `R` of condition (5) the same device gives a
compatible family `Spec (R/Jₙ) ⟶ S`.

Natural numbers index the chains of the source starting at its `I₁`, and "fundamental system of
neighbourhoods of `0`" is `Filter.HasBasis` for `nhds 0`; for condition (2) only countable
generation of `nhds 0` is asked, which is what `Filter.HasBasis.exists_antitone_subbasis` turns
into a chain. Completeness in condition (4) is for the canonical uniformity of the additive
group, as in `TopologicalRing.IsWeaklyAdmissible`, and is accompanied by separatedness: the
source's "complete" includes separated, and without it the inverse limit description fails. That
the ideals of condition (4) are open is recorded explicitly although it follows from their being
a fundamental system of neighbourhoods of `0`, since that is how the source reads the condition.

Condition (5) spells out `A = lim R/Jₙ` by the universal property instead of choosing a limit
cone: the quotient maps `A → R/Jₙ` are compatible, and every compatible family of elements of
the `R/Jₙ` is hit by exactly one element of `A`. "With the limit topology" is the statement that
the kernels of those maps are a fundamental system of neighbourhoods of `0`. The last clause
says that the `S`-structure of `Spf A` is the one induced from `R`: each structure morphism
`Spec (A/K) ⟶ S` of the quotient system factors `Spec (R/Jₙ) ⟶ S` through the induced map.

## References

* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presentation of an fppf sheaf `X` over `S` as the formal spectrum of a topological ring:
a linearly topologized ring, a quotient system making it a ring over `S` in the sense of
**Stacks 0AIF**, and an isomorphism of `X` with the resulting formal spectrum. This is the
datum behind the source's `X = Spf A`. -/
structure SpfPresentation (X : FppfSheaf B S hS) where
  /-- The presenting ring. -/
  ring : Type u
  [commRing : CommRing ring]
  [topology : TopologicalSpace ring]
  [topologicalRing : IsTopologicalRing ring]
  [linearTopology : IsLinearTopology ring ring]
  /-- The structure morphisms making the ring a ring over `S`. -/
  system : QuotientSystem B S hS ring
  /-- The identification of `X` with the formal spectrum of the ring. -/
  iso : Nonempty (X ≅ formalSpectrum system)

attribute [instance] SpfPresentation.commRing SpfPresentation.topology
  SpfPresentation.topologicalRing SpfPresentation.linearTopology

/-- Condition (1) of **Stacks 0AN1**: `X` is a countably indexed affine formal algebraic
space, that is, an affine formal algebraic space (**Stacks 0AI7**) admitting a presentation
indexed by `ℕ` (**Stacks 0AIJ**). -/
abbrev IsCountablyIndexedAffine (X : FppfSheaf B S hS) : Prop :=
  IsAffineFormalAlgebraicSpace B S hS X ∧ IsCountablyIndexed B S hS X

/-- Condition (2) of **Stacks 0AN1**: `X = Spf A` for a weakly admissible topological
`S`-algebra `A` which has a countable fundamental system of neighbourhoods of `0`. -/
abbrev HasCountableWeakPresentation (X : FppfSheaf B S hS) : Prop :=
  ∃ P : SpfPresentation B S hS X,
    TopologicalRing.IsWeaklyAdmissible P.ring ∧ (nhds (0 : P.ring)).IsCountablyGenerated

/-- Condition (3) of **Stacks 0AN1**: `X = Spf A` for a weakly admissible topological
`S`-algebra `A` having a fundamental system of neighbourhoods of `0` which is a descending
chain `A ⊇ I₁ ⊇ I₂ ⊇ ⋯` of weak ideals of definition. -/
abbrev HasWeakIdealChain (X : FppfSheaf B S hS) : Prop :=
  ∃ P : SpfPresentation B S hS X,
    TopologicalRing.IsWeaklyAdmissible P.ring ∧
      ∃ I : ℕ → Ideal P.ring, Antitone I ∧
        (∀ n, TopologicalRing.IsWeakIdealOfDefinition (I n)) ∧
        (nhds (0 : P.ring)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set P.ring))

/-- Condition (4) of **Stacks 0AN1**: `X = Spf A` for a complete and separated topological
`S`-algebra `A` whose neighbourhoods of `0` come from a descending chain `A ⊇ I₁ ⊇ I₂ ⊇ ⋯` of
open ideals with `Iₙ/Iₙ₊₁` locally nilpotent. -/
abbrev HasNilpotentIdealChain (X : FppfSheaf B S hS) : Prop :=
  ∃ P : SpfPresentation B S hS X,
    (@CompleteSpace P.ring (IsTopologicalAddGroup.rightUniformSpace P.ring)) ∧
      T2Space P.ring ∧
      ∃ I : ℕ → Ideal P.ring, Antitone I ∧ (∀ n, IsOpen (I n : Set P.ring)) ∧
        (nhds (0 : P.ring)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set P.ring)) ∧
        (∀ n, ((I n).map (Ideal.Quotient.mk (I (n + 1)))).LocallyNilpotent)

/-- Condition (5) of **Stacks 0AN1**: `X = Spf A` where `A = lim R/Jₙ` carries the limit
topology, for a descending chain `R ⊇ J₁ ⊇ J₂ ⊇ ⋯` of ideals of an `S`-algebra `R` whose
successive quotients `Jₙ/Jₙ₊₁` are locally nilpotent. The limit is expressed by its universal
property, the limit topology by the kernels of the projections, and the `S`-structure of `R` by
compatible morphisms `Spec (R/Jₙ) ⟶ S` inducing the structure morphisms of `Spf A`. -/
abbrev IsLimitOfNilpotentQuotients (X : FppfSheaf B S hS) : Prop :=
  ∃ P : SpfPresentation B S hS X, ∃ (R : Type u) (inst : CommRing R),
    letI : CommRing R := inst
    ∃ (J : ℕ → Ideal R) (hJ : Antitone J)
      (g : ∀ n, Spec (.of (R ⧸ J n)) ⟶ S) (π : ∀ n, P.ring →+* R ⧸ J n),
      (∀ n, ((J n).map (Ideal.Quotient.mk (J (n + 1)))).LocallyNilpotent) ∧
      (∀ n, Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (hJ (Nat.le_succ n)))) ≫ g (n + 1) = g n) ∧
      (∀ n, (Ideal.Quotient.factor (hJ (Nat.le_succ n))).comp (π (n + 1)) = π n) ∧
      (∀ x : ∀ n, R ⧸ J n,
        (∀ n, Ideal.Quotient.factor (hJ (Nat.le_succ n)) (x (n + 1)) = x n) →
          ∃! a : P.ring, ∀ n, π n a = x n) ∧
      (nhds (0 : P.ring)).HasBasis (fun _ : ℕ ↦ True)
        (fun n ↦ (RingHom.ker (π n) : Set P.ring)) ∧
      (∀ K : { I : Ideal P.ring // TopologicalRing.IsWeakIdealOfDefinition I },
        ∃ (n : ℕ) (q : R ⧸ J n →+* P.ring ⧸ K.1),
          Ideal.Quotient.mk K.1 = q.comp (π n) ∧
          Spec.map (CommRingCat.ofHom q) ≫ g n = P.system.overS K)

/-! ### Conditions (2), (3) and (4) -/

/-- A weakly admissible ring whose zero neighbourhood filter is countably generated has a
descending sequence of weak ideals of definition as a fundamental system of neighbourhoods of
`0`: the weak ideals of definition already are such a system (**Stacks 0AI3**), and a countably
generated filter with a basis has an antitone subbasis drawn from it. -/
private theorem exists_antitone_weakIdeal_basis {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hc : (nhds (0 : A)).IsCountablyGenerated) :
    ∃ I : ℕ → Ideal A, Antitone I ∧
      (∀ n, TopologicalRing.IsWeakIdealOfDefinition (I n)) ∧
      (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)) := by
  let _ : (nhds (0 : A)).IsCountablyGenerated := hc
  obtain ⟨I, hweak, hanti⟩ :=
    (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hA).exists_antitone_subbasis
  exact ⟨I, hanti.antitone, hweak, hanti.toHasBasis⟩

/-- If a descending sequence of ideals is a fundamental system of neighbourhoods of `0` and each
successive quotient `Iₙ/Iₙ₊₁` is locally nilpotent, then every element of `I₀` is topologically
nilpotent: a power of it lies in `I₁`, a power of that in `I₂`, and so on, so some power lies in
any prescribed member of the system. -/
private theorem isTopologicallyNilpotent_of_locallyNilpotent_chain {A : Type*} [CommRing A]
    [TopologicalSpace A] {I : ℕ → Ideal A}
    (hbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)))
    (hnil : ∀ n, ((I n).map (Ideal.Quotient.mk (I (n + 1)))).LocallyNilpotent)
    {x : A} (hx : x ∈ I 0) : IsTopologicallyNilpotent x := by
  have hstep (n p : ℕ) (hp : x ^ p ∈ I n) : ∃ q, x ^ q ∈ I (n + 1) := by
    obtain ⟨q, hq⟩ := hnil n (Ideal.Quotient.mk (I (n + 1)) (x ^ p))
      (Ideal.mem_map_of_mem (Ideal.Quotient.mk (I (n + 1))) hp)
    refine ⟨p * q, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    simpa [pow_mul] using hq
  have hpow (n : ℕ) : ∃ p, x ^ p ∈ I n := by
    induction n with
    | zero => exact ⟨1, by simpa using hx⟩
    | succ n ih => exact ih.elim (hstep n)
  rw [IsTopologicallyNilpotent, Filter.tendsto_def]
  intro U hU
  obtain ⟨n, -, hsub⟩ := hbasis.mem_iff.mp hU
  obtain ⟨p, hp⟩ := hpow n
  filter_upwards [Filter.eventually_ge_atTop p] with k hk
  refine hsub ?_
  show x ^ k ∈ (I n : Set A)
  rw [← pow_sub_mul_pow x hk]
  exact (I n).mul_mem_left _ hp

/-- A weak ideal of definition has locally nilpotent image in the quotient by any smaller open
ideal: an element of the first is topologically nilpotent, so some power of it lies in the
second. -/
private theorem locallyNilpotent_map_of_isWeakIdealOfDefinition {A : Type*} [CommRing A]
    [TopologicalSpace A] {I J : Ideal A} (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    (hJ : IsOpen (J : Set A)) : (I.map (Ideal.Quotient.mk J)).LocallyNilpotent := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
  obtain ⟨k, hk⟩ := ((hI.2 x hx).eventually (hJ.mem_nhds (Ideal.zero_mem J))).exists
  exact ⟨k, by simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hk⟩

/-- **Stacks 0AN1**, conditions (2) and (3) are equivalent. A countably generated filter of
neighbourhoods of `0` in a weakly admissible ring is based on a descending chain of weak ideals
of definition, and such a chain is in particular a countable fundamental system. -/
@[stacks 0AN1 "conditions (2) and (3)"]
theorem hasCountableWeakPresentation_iff_hasWeakIdealChain (X : FppfSheaf B S hS) :
    HasCountableWeakPresentation B S hS X ↔ HasWeakIdealChain B S hS X := by
  constructor
  · rintro ⟨P, hA, hc⟩
    obtain ⟨I, hanti, hweak, hbasis⟩ := exists_antitone_weakIdeal_basis hA hc
    exact ⟨P, hA, I, hanti, hweak, hbasis⟩
  · rintro ⟨P, hA, I, hanti, hweak, hbasis⟩
    exact ⟨P, hA, hbasis.isCountablyGenerated⟩

/-- **Stacks 0AN1**, conditions (3) and (4) are equivalent. A chain of weak ideals of definition
has locally nilpotent successive quotients because its members consist of topologically
nilpotent elements; conversely, if the successive quotients are locally nilpotent then every
element of a member of the chain is topologically nilpotent, so each member is a weak ideal of
definition and the ring is weakly pre-admissible. -/
@[stacks 0AN1 "conditions (3) and (4)"]
theorem hasWeakIdealChain_iff_hasNilpotentIdealChain (X : FppfSheaf B S hS) :
    HasWeakIdealChain B S hS X ↔ HasNilpotentIdealChain B S hS X := by
  constructor
  · rintro ⟨P, ⟨-, hcomplete, hT2⟩, I, hanti, hweak, hbasis⟩
    exact ⟨P, hcomplete, hT2, I, hanti, fun n ↦ (hweak n).1, hbasis,
      fun n ↦ locallyNilpotent_map_of_isWeakIdealOfDefinition (hweak n) (hweak (n + 1)).1⟩
  · rintro ⟨P, hcomplete, hT2, I, hanti, hopen, hbasis, hnil⟩
    have hweak (n : ℕ) : TopologicalRing.IsWeakIdealOfDefinition (I n) :=
      ⟨hopen n, fun _ hx ↦ isTopologicallyNilpotent_of_locallyNilpotent_chain hbasis hnil
        (hanti (Nat.zero_le n) hx)⟩
    exact ⟨P, ⟨⟨I 0, hweak 0⟩, hcomplete, hT2⟩, I, hanti, hweak, hbasis⟩

/-! ### Conditions (3) and (5): the inverse limit description -/

/-- A weak ideal of definition contains some member of a chain of ideals basing the topology. -/
private theorem exists_le_of_isWeakIdealOfDefinition {A : Type*} [CommRing A]
    [TopologicalSpace A] {I : ℕ → Ideal A}
    (hbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)))
    {K : Ideal A} (hK : TopologicalRing.IsWeakIdealOfDefinition K) : ∃ n, I n ≤ K := by
  obtain ⟨n, -, hsub⟩ := hbasis.mem_iff.mp (hK.1.mem_nhds (Ideal.zero_mem K))
  exact ⟨n, hsub⟩

/-- An element of a separated topological ring which lies in every member of a fundamental
system of neighbourhoods of `0` is `0`: the constant sequence with that value converges both to
it and to `0`. -/
private theorem eq_of_forall_sub_mem {A : Type*} [CommRing A] [TopologicalSpace A]
    (hT2 : T2Space A) {I : ℕ → Ideal A}
    (hbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)))
    {a b : A} (h : ∀ n, a - b ∈ I n) : a = b := by
  let _ : T2Space A := hT2
  have hzero : Tendsto (fun _ : ℕ ↦ a - b) atTop (nhds (0 : A)) :=
    hbasis.tendsto_right_iff.mpr fun n _ ↦ Filter.Eventually.of_forall fun _ ↦ h n
  exact sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hzero)

/-- Compatibility of the projections to successive quotients, stated pointwise. -/
private theorem factor_apply_of_comp_eq {A R : Type*} [CommRing A] [CommRing R]
    {J : ℕ → Ideal R} (hJ : Antitone J) (π : ∀ n, A →+* R ⧸ J n)
    (hπ : ∀ n, (Ideal.Quotient.factor (hJ (Nat.le_succ n))).comp (π (n + 1)) = π n)
    (n : ℕ) (a : A) : Ideal.Quotient.factor (hJ (Nat.le_succ n)) (π (n + 1) a) = π n a := by
  simpa using RingHom.congr_fun (hπ n) a

section Limit

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- A complete separated topological ring whose topology is given by a descending sequence of
ideals is the inverse limit of the corresponding quotients: every compatible family of elements
of the `A/Iₙ` is the image of exactly one element of `A`.

Uniqueness is separatedness. For existence one lifts the family to a sequence of elements of
`A`; compatibility makes the differences of its terms lie in ever smaller members of the chain,
so the sequence is Cauchy and its limit is the required element. -/
@[ega "0 7.2.1" "partial"]
private theorem existsUnique_mk_eq_of_compatible (hT2 : T2Space A)
    (hcomplete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    {I : ℕ → Ideal A} (hanti : Antitone I)
    (hbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)))
    (x : ∀ n, A ⧸ I n)
    (hx : ∀ n, Ideal.Quotient.factor (hanti (Nat.le_succ n)) (x (n + 1)) = x n) :
    ∃! a : A, ∀ n, Ideal.Quotient.mk (I n) a = x n := by
  classical
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let _ : CompleteSpace A := hcomplete
  let _ : T2Space A := hT2
  -- the compatibility of the family propagates from successors to all pairs `m ≤ n`
  have hxle : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factor (hanti h) (x n) = x m := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base =>
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (x m)
      rw [← hr, Ideal.Quotient.factor_mk]
    | succ n h ih =>
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (x (n + 1))
      rw [← ih, ← hx n, ← hr]
      simp only [Ideal.Quotient.factor_mk]
  choose a ha using fun n ↦ Ideal.Quotient.mk_surjective (x n)
  have hmk : ∀ {m n : ℕ}, m ≤ n → Ideal.Quotient.mk (I m) (a n) = x m := fun {_ n} h ↦ by
    rw [← hxle h, ← ha n, Ideal.Quotient.factor_mk]
  have hCauchy : CauchySeq a := by
    rw [cauchySeq_iff]
    intro V hV
    rw [uniformity_eq_comap_nhds_zero] at hV
    obtain ⟨U, hU, hUV⟩ := Filter.mem_comap.mp hV
    obtain ⟨n, -, hIU⟩ := hbasis.mem_iff.mp hU
    refine ⟨n, fun i hi j hj ↦ hUV (hIU ?_)⟩
    exact Ideal.Quotient.eq.mp ((hmk hj).trans (hmk hi).symm)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hzval (n : ℕ) : Ideal.Quotient.mk (I n) z = x n := by
    have hev : ∀ᶠ k : ℕ in atTop, a k - z ∈ I n := by
      have hmem : (I n : Set A) ∈ nhds (z - z) := by
        simpa using hbasis.mem_of_mem (i := n) trivial
      exact (hz.sub_const z).eventually hmem
    obtain ⟨k, hk, hkn⟩ := (hev.and (Filter.eventually_ge_atTop n)).exists
    exact (Ideal.Quotient.eq.mpr hk).symm.trans (hmk hkn)
  refine ⟨z, hzval, fun b hb ↦ eq_of_forall_sub_mem hT2 hbasis fun n ↦ ?_⟩
  exact Ideal.Quotient.eq.mp ((hb n).trans (hzval n).symm)

/-- **Stacks 0AN1**, condition (3) implies condition (5). A chain of weak ideals of definition
basing the topology of a weakly admissible `A` exhibits `A` itself as the inverse limit
`lim A/Iₙ` with the limit topology, and the `S`-algebra of condition (5) can be taken to be `A`:
the successive quotients `Iₙ/Iₙ₊₁` are locally nilpotent, the kernels of the quotient maps are
the `Iₙ`, and the structure morphisms of the quotient system are already indexed by weak ideals
of definition, each of which contains some `Iₙ`. -/
@[stacks 0AN1 "condition (3) implies condition (5)"]
theorem isLimitOfNilpotentQuotients_of_hasWeakIdealChain (X : FppfSheaf B S hS)
    (hX : HasWeakIdealChain B S hS X) : IsLimitOfNilpotentQuotients B S hS X := by
  obtain ⟨P, ⟨-, hcomplete, hT2⟩, I, hanti, hweak, hbasis⟩ := hX
  refine ⟨P, P.ring, inferInstance, I, hanti,
    fun n ↦ P.system.overS ⟨I n, hweak n⟩, fun n ↦ Ideal.Quotient.mk (I n),
    fun n ↦ locallyNilpotent_map_of_isWeakIdealOfDefinition (hweak n) (hweak (n + 1)).1,
    fun n ↦ P.system.compatible ⟨I (n + 1), hweak (n + 1)⟩ ⟨I n, hweak n⟩
      (hanti (Nat.le_succ n)),
    fun n ↦ Ideal.Quotient.factor_comp_mk (hanti (Nat.le_succ n)),
    fun x hx ↦ existsUnique_mk_eq_of_compatible hT2 hcomplete hanti hbasis x hx, ?_, ?_⟩
  · simpa only [Ideal.mk_ker] using hbasis
  · intro K
    obtain ⟨n, hsub⟩ := exists_le_of_isWeakIdealOfDefinition hbasis K.2
    exact ⟨n, Ideal.Quotient.factor hsub, (Ideal.Quotient.factor_comp_mk hsub).symm,
      P.system.compatible ⟨I n, hweak n⟩ K hsub⟩

variable {R : Type*} [CommRing R] {J : ℕ → Ideal R}

/-- A topological ring which is the inverse limit of a sequence of rings and is topologized by
the kernels of the projections is complete and separated.

Separatedness: an element killed by every projection is `0`, because `0` is the unique element
inducing the zero family. Completeness: a Cauchy sequence is eventually constant modulo each
kernel, so its projections stabilise to a compatible family; the element of the limit inducing
that family is the limit of the sequence. -/
private theorem complete_and_t2Space_of_limit (hJ : Antitone J) (π : ∀ n, A →+* R ⧸ J n)
    (hπ : ∀ n, (Ideal.Quotient.factor (hJ (Nat.le_succ n))).comp (π (n + 1)) = π n)
    (hlim : ∀ x : ∀ n, R ⧸ J n,
      (∀ n, Ideal.Quotient.factor (hJ (Nat.le_succ n)) (x (n + 1)) = x n) →
        ∃! a : A, ∀ n, π n a = x n)
    (hbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (RingHom.ker (π n) : Set A))) :
    (@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)) ∧ T2Space A := by
  classical
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have hπ' := factor_apply_of_comp_eq hJ π hπ
  have hker (n : ℕ) : (RingHom.ker (π n) : Set A) ∈ nhds (0 : A) :=
    hbasis.mem_of_mem trivial
  refine ⟨?_, ?_⟩
  · have _ : (nhds (0 : A)).IsCountablyGenerated := hbasis.isCountablyGenerated
    have _ : (uniformity A).IsCountablyGenerated := by
      rw [uniformity_eq_comap_nhds_zero]
      exact Filter.comap.isCountablyGenerated _ _
    apply UniformSpace.complete_of_cauchySeq_tendsto
    intro u hu
    have heq (n : ℕ) : ∃ N, ∀ k ≥ N, ∀ l ≥ N, π n (u k) = π n (u l) := by
      refine (cauchySeq_iff.mp hu) {z : A × A | π n z.1 = π n z.2} ?_
      rw [uniformity_eq_comap_nhds_zero]
      refine Filter.mem_comap.mpr ⟨RingHom.ker (π n), hker n, fun z hz ↦ ?_⟩
      have hz' : π n (z.2 - z.1) = 0 := RingHom.mem_ker.mp hz
      rw [map_sub] at hz'
      exact (sub_eq_zero.mp hz').symm
    choose N hN using heq
    have hxcompat (n : ℕ) : Ideal.Quotient.factor (hJ (Nat.le_succ n))
        (π (n + 1) (u (N (n + 1)))) = π n (u (N n)) := by
      rw [hN (n + 1) (N (n + 1)) le_rfl (max (N n) (N (n + 1))) (le_max_right _ _), hπ']
      exact hN n _ (le_max_left _ _) (N n) le_rfl
    obtain ⟨z, hz, -⟩ := hlim (fun n ↦ π n (u (N n))) hxcompat
    refine ⟨z, ?_⟩
    have hsub : Tendsto (fun k : ℕ ↦ u k - z) atTop (nhds (0 : A)) := by
      refine hbasis.tendsto_right_iff.mpr fun n _ ↦ ?_
      filter_upwards [Filter.eventually_ge_atTop (N n)] with k hk
      exact RingHom.mem_ker.mpr (by rw [map_sub, hz n, hN n k hk (N n) le_rfl, sub_self])
    simpa using hsub.add_const z
  · refine IsTopologicalAddGroup.t2Space_of_zero_sep fun a ha ↦ ?_
    obtain ⟨b, -, huniq⟩ := hlim (fun _ ↦ 0) fun n ↦ map_zero _
    obtain ⟨n, hn⟩ : ∃ n, π n a ≠ 0 := by
      by_contra! h
      exact ha ((huniq a h).trans (huniq 0 fun _ ↦ map_zero _).symm)
    exact ⟨RingHom.ker (π n), hker n, fun hz ↦ hn (RingHom.mem_ker.mp hz)⟩

/-- A topological ring presented as the inverse limit of a sequence of quotients of another ring
with locally nilpotent successive quotients, and topologized by the kernels of the projections,
is weakly admissible.

The kernels `Kₙ` of the projections form a descending chain of open ideals basing the topology,
and `Kₙ/Kₙ₊₁` is locally nilpotent because an element of `Kₙ` has its image in `R/Jₙ₊₁` in
`Jₙ/Jₙ₊₁`. Hence every element of `K₀` is topologically nilpotent, so `K₀` is a weak ideal of
definition; completeness and separatedness come from the limit presentation. -/
private theorem isWeaklyAdmissible_of_limit [IsLinearTopology A A] (hJ : Antitone J)
    (hnil : ∀ n, ((J n).map (Ideal.Quotient.mk (J (n + 1)))).LocallyNilpotent)
    (π : ∀ n, A →+* R ⧸ J n)
    (hπ : ∀ n, (Ideal.Quotient.factor (hJ (Nat.le_succ n))).comp (π (n + 1)) = π n)
    (hlim : ∀ x : ∀ n, R ⧸ J n,
      (∀ n, Ideal.Quotient.factor (hJ (Nat.le_succ n)) (x (n + 1)) = x n) →
        ∃! a : A, ∀ n, π n a = x n)
    (hbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (RingHom.ker (π n) : Set A))) :
    TopologicalRing.IsWeaklyAdmissible A := by
  have hπ' := factor_apply_of_comp_eq hJ π hπ
  have hKanti : Antitone (fun n ↦ RingHom.ker (π n)) :=
    antitone_nat_of_succ_le fun n a ha ↦ by
      refine RingHom.mem_ker.mpr ?_
      rw [← hπ' n a, RingHom.mem_ker.mp ha, map_zero]
  have hnilK (n : ℕ) : ((RingHom.ker (π n)).map
      (Ideal.Quotient.mk (RingHom.ker (π (n + 1))))).LocallyNilpotent := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
    have hmem : π (n + 1) x ∈ (J n).map (Ideal.Quotient.mk (J (n + 1))) := by
      rw [← Ideal.Quotient.factor_ker (hJ (Nat.le_succ n))]
      exact RingHom.mem_ker.mpr (by rw [hπ' n x, RingHom.mem_ker.mp hx])
    obtain ⟨k, hk⟩ := hnil n (π (n + 1) x) hmem
    refine ⟨k, Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr ?_)⟩
    rw [map_pow, hk]
  obtain ⟨hcomplete, hT2⟩ := complete_and_t2Space_of_limit hJ π hπ hlim hbasis
  refine ⟨⟨RingHom.ker (π 0), ?_, ?_⟩, hcomplete, hT2⟩
  · exact (RingHom.ker (π 0)).toAddSubgroup.isOpen_of_mem_nhds (g := 0)
      (hbasis.mem_of_mem trivial)
  · exact fun x hx ↦ isTopologicallyNilpotent_of_locallyNilpotent_chain
      (I := fun n ↦ RingHom.ker (π n)) hbasis hnilK hx

end Limit

/-- **Stacks 0AN1**, condition (5) implies condition (2). The presenting ring of an inverse
limit presentation is weakly admissible, and the kernels of the projections are a countable
fundamental system of neighbourhoods of `0`. -/
@[stacks 0AN1 "condition (5) implies condition (2)"]
theorem hasCountableWeakPresentation_of_isLimitOfNilpotentQuotients (X : FppfSheaf B S hS)
    (hX : IsLimitOfNilpotentQuotients B S hS X) : HasCountableWeakPresentation B S hS X := by
  obtain ⟨P, R, inst, J, hJ, -, π, hnil, -, hπ, hlim, hbasis, -⟩ := hX
  exact ⟨P, isWeaklyAdmissible_of_limit hJ hnil π hπ hlim hbasis,
    hbasis.isCountablyGenerated⟩

/-! ### Conditions (2) and (1) -/

/-- The spectrum of a quotient map between quotients by nested weak ideals of definition is a
thickening: the map is surjective with locally nilpotent kernel, so its spectrum is a closed
immersion, and it is surjective on points because a prime of the source contains the kernel and
is therefore the contraction of its extension. -/
private theorem isThickening_spec_quotient_factor {A : Type u} [CommRing A]
    [TopologicalSpace A] {I K : Ideal A} (hKI : K ≤ I)
    (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    (hK : TopologicalRing.IsWeakIdealOfDefinition K) :
    Stacks.Thickenings.IsThickening
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKI))) := by
  have hsurj : Function.Surjective (Ideal.Quotient.factor hKI) :=
    Ideal.Quotient.factor_surjective hKI
  have hnil (x : A ⧸ K) (hx : x ∈ RingHom.ker (Ideal.Quotient.factor hKI)) :
      IsNilpotent x :=
    locallyNilpotent_map_of_isWeakIdealOfDefinition hI hK.1 x
      (by rwa [← Ideal.Quotient.factor_ker hKI])
  have hspec : Function.Surjective
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKI))) := by
    intro p
    let _ : p.asIdeal.IsPrime := p.2
    have hkerle : RingHom.ker (Ideal.Quotient.factor hKI) ≤ p.asIdeal := by
      intro x hx
      obtain ⟨n, hn⟩ := hnil x hx
      exact p.2.mem_of_pow_mem n (hn ▸ Ideal.zero_mem _)
    refine ⟨⟨p.asIdeal.map (Ideal.Quotient.factor hKI),
      Ideal.map_isPrime_of_surjective hsurj hkerle⟩, PrimeSpectrum.ext ?_⟩
    show Ideal.comap (Ideal.Quotient.factor hKI)
      (p.asIdeal.map (Ideal.Quotient.factor hKI)) = p.asIdeal
    rw [Ideal.comap_map_of_surjective _ hsurj, sup_eq_left]
    exact hkerle
  exact ⟨IsClosedImmersion.spec_of_surjective _ hsurj, hspec⟩

attribute [local instance] sheaf_hasColimits

/-- The formal spectrum of a weakly admissible ring with countably generated zero
neighbourhoods is countably indexed: a descending chain of weak ideals of definition basing the
topology is cofinal in the index of the canonical diagram, and a cofinal reindexing does not
change the colimit. -/
private theorem isCountablyIndexed_of_countableWeakPresentation {X : FppfSheaf B S hS}
    (P : SpfPresentation B S hS X) (hA : TopologicalRing.IsWeaklyAdmissible P.ring)
    (hc : (nhds (0 : P.ring)).IsCountablyGenerated) : IsCountablyIndexed B S hS X := by
  obtain ⟨I, hanti, hweak, hbasis⟩ := exists_antitone_weakIdeal_basis hA hc
  have hmono : Monotone (fun n : ℕ ↦
      OrderDual.toDual (⟨I n, hweak n⟩ :
        { K : Ideal P.ring // TopologicalRing.IsWeakIdealOfDefinition K })) :=
    fun _ _ h ↦ hanti h
  let e := hmono.functor
  let _ : Functor.Final e := hmono.final_functor_iff.mpr fun K ↦ by
    exact exists_le_of_isWeakIdealOfDefinition hbasis K.2
  let H := BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  refine ⟨e ⋙ P.system.diagram, fun {i j} f ↦ ?_, ?_⟩
  · show Stacks.Thickenings.IsThickening (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (show I j ≤ I i from hanti (leOfHom f)))))
    exact isThickening_spec_quotient_factor (hanti (leOfHom f)) (hweak i) (hweak j)
  · exact P.iso.map fun hX ↦
      hX ≪≫ (Functor.Final.colimitIso e (P.system.diagram ⋙ H)).symm

/-- A quotient system on a weakly admissible ring with countably generated zero neighbourhoods
lives in a site large enough to contain the coproduct of all its quotient spectra, which is what
**Stacks 0AIF** needs in order to recognise the formal spectrum as an affine formal algebraic
space.

A chain `Iₙ` of weak ideals of definition basing the topology embeds `A` into `∏ₙ A/Iₙ`, by
separatedness. Each `#(A/Iₙ)` is below the cutoff because the quotient spectrum lies in the
site, hence so is their supremum `μ`, the cutoff having uncountable cofinality; the cutoff being
a strong prelimit then keeps `μ ^ ℵ₀`, and therefore `#A`, below it. Every quotient of `A` and
the set of weak ideals of definition are of size at most `2 ^ #A`, which bounds the size of the
coproduct. -/
theorem QuotientSystem.hasLargeSite_of_isCountablyGenerated {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (D : QuotientSystem B S hS A) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hc : (nhds (0 : A)).IsCountablyGenerated) : D.HasLargeSite := by
  obtain ⟨I, hanti, hweak, hbasis⟩ := exists_antitone_weakIdeal_basis hA hc
  -- each quotient by a member of the chain is small, hence so is their supremum
  have hquot (n : ℕ) : Cardinal.mk (A ⧸ I n) < B.cutoff := by
    have hsite : (Spec (.of (A ⧸ I n))).size < B.cutoff := D.inSite ⟨I n, hweak n⟩
    rw [Scheme.size_Spec] at hsite
    exact (le_max_right _ _).trans_lt hsite
  have hsup : (⨆ n : ULift.{u} ℕ, Cardinal.mk (A ⧸ I n.down)) < B.cutoff :=
    Cardinal.iSup_lt_of_lt_cof_ord (α := ULift.{u} ℕ)
      ((Cardinal.mk_le_aleph0 :
        Cardinal.mk (ULift.{u} ℕ) ≤ Cardinal.aleph0).trans_lt B.aleph0_lt_cutoff_cof)
      fun n ↦ hquot n.down
  -- separatedness embeds `A` into the product of the quotients
  have hinj : Function.Injective (fun a : A ↦ fun n : ℕ ↦ Ideal.Quotient.mk (I n) a) :=
    fun _ _ hab ↦ eq_of_forall_sub_mem hA.2.2 hbasis fun n ↦ Ideal.Quotient.eq.mp (congrFun hab n)
  have hA_lt : Cardinal.mk A < B.cutoff := by
    refine lt_of_le_of_lt ?_ (Cardinal.power_aleph0_lt_of_isStrongPrelimit
      B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hsup)
    calc Cardinal.mk A ≤ Cardinal.mk ((n : ℕ) → A ⧸ I n) := Cardinal.mk_le_of_injective hinj
      _ ≤ (⨆ n : ULift.{u} ℕ, Cardinal.mk (A ⧸ I n.down)) ^ Cardinal.aleph0 := by
          rw [Cardinal.mk_pi]
          calc Cardinal.prod (fun n : ℕ ↦ Cardinal.mk (A ⧸ I n))
              ≤ Cardinal.prod (fun _ : ℕ ↦
                  ⨆ n : ULift.{u} ℕ, Cardinal.mk (A ⧸ I n.down)) :=
                Cardinal.prod_le_prod _ _ fun n ↦ le_ciSup
                  (f := fun k : ULift.{u} ℕ ↦ Cardinal.mk (A ⧸ I k.down))
                  Cardinal.bddAbove_of_small (ULift.up n)
            _ = (⨆ n : ULift.{u} ℕ, Cardinal.mk (A ⧸ I n.down)) ^ Cardinal.aleph0 := by
                simp
  -- both the index and the fibres of the coproduct are bounded by `2 ^ #A`
  have hpow : Cardinal.mk A ≤ 2 ^ Cardinal.mk A :=
    (Cardinal.mk_le_of_injective (f := fun a : A ↦ ({a} : Set A)) fun a b h ↦ by
      simpa using congrArg (fun T : Set A ↦ a ∈ T) h).trans_eq Cardinal.mk_set
  have hidx : Cardinal.mk { K : Ideal A // TopologicalRing.IsWeakIdealOfDefinition K } ≤
      2 ^ Cardinal.mk A :=
    (Cardinal.mk_subtype_le _).trans
      ((Cardinal.mk_le_of_injective (f := fun K : Ideal A ↦ (K : Set A)) fun K L h ↦
        Ideal.ext fun x ↦ Iff.of_eq (congrArg (fun T : Set A ↦ x ∈ T) h)).trans_eq
          Cardinal.mk_set)
  refine lt_of_le_of_lt (schemeSize_coproduct_le _ (max Cardinal.aleph0 (2 ^ Cardinal.mk A))
    (le_max_left _ _) (hidx.trans (le_max_right _ _)) fun K ↦ ?_)
    (max_lt B.aleph0_lt_cutoff (B.cutoff_isStrongPrelimit hA_lt))
  rw [Scheme.size_Spec]
  exact max_le (le_max_left _ _)
    (((Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans hpow).trans
      (le_max_right _ _))

/-- `AlgebraicGeometry.FormalSpace.QuotientSystem.hasLargeSite_of_isCountablyGenerated`, under
the name the rest of this file uses. -/
private alias hasLargeSite_of_isCountablyGenerated := QuotientSystem.hasLargeSite_of_isCountablyGenerated

/-- **Stacks 0AN1**, condition (2) implies condition (1). The formal spectrum of a weakly
admissible ring over `S` is an affine formal algebraic space (**Stacks 0AIF**) once the site is
large enough, which a countable fundamental system of neighbourhoods of `0` guarantees, and it
is countably indexed because such a system is cofinal in the weak ideals of definition. -/
@[stacks 0AN1 "condition (2) implies condition (1)"]
theorem isCountablyIndexedAffine_of_hasCountableWeakPresentation (X : FppfSheaf B S hS)
    (hX : HasCountableWeakPresentation B S hS X) : IsCountablyIndexedAffine B S hS X := by
  obtain ⟨P, hA, hc⟩ := hX
  obtain ⟨hset, I, pre, hne, hdir, D, hD, hcolim⟩ :=
    isAffineFormalAlgebraicSpace_formalSpectrum hA P.system
      (hasLargeSite_of_isCountablyGenerated B S hS P.system hA hc)
  obtain ⟨eX⟩ := P.iso
  exact ⟨⟨satisfiesSetTheoreticCondition_of_iso B S hS eX.symm hset, I, pre, hne, hdir, D, hD,
      hcolim.map fun e ↦ eX ≪≫ e⟩,
    isCountablyIndexed_of_countableWeakPresentation B S hS P hA hc⟩

/-- **Stacks 0AN1**, condition (1) implies condition (2). A countably indexed affine formal
algebraic space is the formal spectrum of the limit of the section rings of a sequential
presentation (**Stacks 0AIK**, item (6)); that ring is weakly admissible and the kernels of
its projections are a countable fundamental system of neighbourhoods of `0`. -/
@[stacks 0AN1 "condition (1) implies condition (2)"]
theorem hasCountableWeakPresentation_of_isCountablyIndexedAffine (X : FppfSheaf B S hS)
    (hX : IsCountablyIndexedAffine B S hS X) : HasCountableWeakPresentation B S hS X := by
  obtain ⟨A, hCR, hTS, hTR, hLT, Q, hWA, hcount, ⟨e⟩⟩ :=
    exists_quotientSystem_of_isCountablyIndexed B S hS hX.2
  exact ⟨{ ring := A, system := Q, iso := ⟨e⟩ }, hWA, hcount⟩

/-- **Stacks 0AN1.** For an fppf sheaf `X` on the big fppf site of `S` the following are
equivalent:

1. `X` is a countably indexed affine formal algebraic space;
2. `X = Spf A` for a weakly admissible topological `S`-algebra `A` with a countable
   fundamental system of neighbourhoods of `0`;
3. `X = Spf A` for a weakly admissible `A` with a descending chain of weak ideals of
   definition as a fundamental system of neighbourhoods of `0`;
4. `X = Spf A` for a complete and separated `A` with a descending chain of open ideals with
   locally nilpotent successive quotients as a fundamental system of neighbourhoods of `0`;
5. `X = Spf A` for `A` the inverse limit of a sequence of quotients of a ring with locally
   nilpotent successive quotients, with the limit topology. -/
@[stacks 0AN1]
theorem isCountablyIndexedAffine_tfae (X : FppfSheaf B S hS) :
    List.TFAE
      [IsCountablyIndexedAffine B S hS X,
        HasCountableWeakPresentation B S hS X,
        HasWeakIdealChain B S hS X,
        HasNilpotentIdealChain B S hS X,
        IsLimitOfNilpotentQuotients B S hS X] := by
  tfae_have 1 → 2 := hasCountableWeakPresentation_of_isCountablyIndexedAffine B S hS X
  tfae_have 2 → 1 := isCountablyIndexedAffine_of_hasCountableWeakPresentation B S hS X
  tfae_have 2 ↔ 3 := hasCountableWeakPresentation_iff_hasWeakIdealChain B S hS X
  tfae_have 3 ↔ 4 := hasWeakIdealChain_iff_hasNilpotentIdealChain B S hS X
  tfae_have 3 → 5 := isLimitOfNilpotentQuotients_of_hasWeakIdealChain B S hS X
  tfae_have 5 → 2 := hasCountableWeakPresentation_of_isLimitOfNilpotentQuotients B S hS X
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
