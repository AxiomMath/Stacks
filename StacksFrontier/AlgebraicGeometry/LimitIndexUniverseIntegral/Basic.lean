module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Basic.Countable.Small
public import Mathlib.Logic.Small.Set
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic

/-!
# The algebra of Stacks 09ZN at an index universe independent of the scheme universe

[Stacks, Tag 09ZN] says that in a directed inverse system of quasi-compact quasi-separated
schemes over a quasi-compact quasi-separated base, with finite transition morphisms and
structure morphisms locally of finite type, an integral morphism from the limit forces the
structure morphisms to be finite at all sufficiently large indices.  Its proof reduces, after an
affine cover of the base and the reduction of
[Stacks, Tag 09ZM], to the following statement of commutative algebra (Step 3 of the source
proof): given a ring `R`, a directed system of `R`-algebras `A i` with module-finite transition
maps and `R → A i` of finite type, and `A = colim A i` with `R → A` integral, some `A i` is
integral — hence finite — over `R`.

The source proof of that algebra step uses the colimit twice, and the second use is the whole
difficulty at a large index.  It chooses `R`-algebra generators `x` of `A i`, finds monic
`P ∈ R[X]` with `P(x) = 0` *in the colimit* because `A` is integral over `R`, and then says that
the relation `P(x) = 0` already holds at a finite stage *because `A` is the colimit*.  When the
index type lives in a universe larger than the rings, the set-theoretic filtered colimit
`A∞ = Ring.DirectLimit` need not be a ring in the rings' universe at all, and all that a limit
cone of schemes supplies is a ring `L` in the small universe which is universal among small
rings — a *reflection* of `A∞`.  The canonical map `A∞ → L` could a priori kill elements that no
finite stage kills, and then the descent step fails.

**It cannot, and that is the content of this file.**  The kernel of `A∞ → L` consists of
nilpotents, with no smallness hypothesis on the index whatsoever
(`isNilpotent_of_lift_eq_zero`).  The reason is that the transition maps are *finite*, which the
ambient Tag 09ZM situation does not assume: every element of `A∞` is then integral over any
fixed stage `A i₀`, so for a prime `q` of `A∞` the domain `A∞ ⧸ q` is integral over the small
ring `A i₀`, hence small itself (`small_of_isIntegral_isDomain`: a domain integral over a
`u`-small ring is covered by the root sets of the monic polynomials over that ring, a `u`-small
family of finite sets).  So each quotient of `A∞` by a prime is a legitimate test ring, the
universal property of `L` factors the quotient map through `L`, and an element killed by
`A∞ → L` lies in every prime of `A∞`, i.e. is nilpotent.

Nilpotency is enough for the descent step, which is why the whole argument goes through: if
`P(x)` dies in `L` then `P(x) ^ n = 0` at some finite stage, and `P ^ n` is monic, so `x` is
integral over `R` at that stage after all.

What is proved here is therefore the algebra of Tag 09ZN with the index universe free and **no
smallness hypothesis**, in the form the scheme-level proof consumes: `exists_isIntegral`.  The
hypothesis that replaces the colimit is `IsSmallColimit`, the bare *existence* half of the
universal property among rings in the small universe — not uniqueness, and not the existence of
the colimit as a `CategoryTheory` object.  At the scheme level that hypothesis is supplied by a
limit cone of schemes with affine stages, through the `Spec`/`Γ` equivalence of affine schemes,
with no smallness used; assembling that is not done in this file.

Nothing here carries the Tag 09ZN attribute: Tag 09ZN is a single unqualified assertion about
schemes, this file proves a lemma of commutative algebra, and the remaining input at a free
index universe is [Stacks, Tag 09ZM] (eventual affineness of the structure morphisms), which is
a separate tag and is open at a free index universe.

## Main results

* `small_of_isIntegral_isDomain`: a domain integral over a `u`-small commutative ring is
  `u`-small, in any universe.
* `isIntegral_of_directLimit`: with module-finite transition maps, the direct limit of a directed
  system of rings is integral over any one stage.
* `IsSmallColimit`: the existence half of the universal property of a cocone among rings in
  `Type u`.
* `exists_hom_of_small`: a compatible family of ring maps into a `u`-small ring factors through
  such a cocone.
* `isNilpotent_of_lift_eq_zero`: **the kernel of the reflection consists of nilpotents.**
* `exists_pow_eq_zero`: a stage element dying in the reflection has a power dying at a finite
  stage.
* `exists_isIntegral`: the algebra of Tag 09ZN at a free index universe.
* `isSmallColimit_directLimit`: at a small index the honest direct limit satisfies
  `IsSmallColimit`, so the hypothesis is not vacuous and `exists_isIntegral` contains the
  source's own Step 3.

## References

* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
* [The Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
-/

@[expose] public section

noncomputable section

universe w v u

namespace Stacks.IntegralLimitAlgebra

/-! ### Smallness of a domain integral over a small ring -/

/-- **A domain integral over a `u`-small commutative ring is `u`-small**, whatever universe it
lives in.  Each element is a root of a monic polynomial over the base; a monic polynomial maps to
a nonzero polynomial over a nontrivial ring, whose root set in a domain is finite; and the monic
polynomials over a ring in `Type u` form a family indexed by `Type u`. -/
theorem small_of_isIntegral_isDomain (R : Type u) [CommRing R] (B : Type w) [CommRing B]
    [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] : Small.{u} B := by
  classical
  have hsmall : ∀ p : Polynomial R,
      Small.{u} {b : B | p.Monic ∧ Polynomial.eval₂ (algebraMap R B) b p = 0} := by
    intro p
    have hfin : Set.Finite {b : B | p.Monic ∧ Polynomial.eval₂ (algebraMap R B) b p = 0} := by
      by_cases hp : p.Monic
      · have hne : p.map (algebraMap R B) ≠ 0 := (hp.map (algebraMap R B)).ne_zero
        refine (Polynomial.finite_setOfPred_isRoot hne).subset fun b hb ↦ ?_
        simpa [Polynomial.IsRoot, Polynomial.eval₂_eq_eval_map] using hb.2
      · exact Set.Finite.subset Set.finite_empty fun b hb ↦ absurd hb.1 hp
    have := hfin.to_subtype
    infer_instance
  have hcover : (Set.univ : Set B) =
      ⋃ p : Polynomial R, {b : B | p.Monic ∧ Polynomial.eval₂ (algebraMap R B) b p = 0} := by
    ext b
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    exact Algebra.IsIntegral.isIntegral b
  have : Small.{u} (Set.univ : Set B) := by rw [hcover]; infer_instance
  exact small_of_injective (f := fun b : B ↦ (⟨b, Set.mem_univ b⟩ : (Set.univ : Set B)))
    fun a b hab ↦ by simpa using hab

/-- Integrality of a ring map is preserved by a surjection on the target. -/
theorem isIntegral_comp_surjective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {φ : R →+* S} (hφ : φ.IsIntegral) (π : S →+* T) (hπ : Function.Surjective π) :
    (π.comp φ).IsIntegral := by
  intro t
  obtain ⟨s, rfl⟩ := hπ t
  obtain ⟨p, hp, hps⟩ := hφ s
  exact ⟨p, hp, by rw [← Polynomial.hom_eval₂, hps, map_zero]⟩

/-! ### The direct limit of a directed system with finite transition maps -/

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {A : I → Type u} [∀ i, CommRing (A i)] (ψ : ∀ i j, i ≤ j → A i →+* A j)
  [DirectedSystem A fun i j h ↦ ψ i j h]

omit [DirectedSystem A fun i j h ↦ ψ i j h] in
/-- **With module-finite transition maps the direct limit is integral over any one stage.**  Every
element of the direct limit comes from some stage, which is module-finite, hence integral, over a
common refinement with the fixed stage. -/
theorem isIntegral_of_directLimit (hfin : ∀ i j (h : i ≤ j), (ψ i j h).Finite) (i₀ : I) :
    (Ring.DirectLimit.of A (ψ · · ·) i₀).IsIntegral := by
  intro z
  obtain ⟨j, x, rfl⟩ := Ring.DirectLimit.exists_of z
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i₀ j
  obtain ⟨p, hp, hpx⟩ := (hfin i₀ k hik).to_isIntegral (ψ j k hjk x)
  refine ⟨p, hp, ?_⟩
  have h1 : Ring.DirectLimit.of A (ψ · · ·) j x
      = Ring.DirectLimit.of A (ψ · · ·) k (ψ j k hjk x) :=
    (Ring.DirectLimit.of_f hjk x).symm
  have h2 : (Ring.DirectLimit.of A (ψ · · ·) k).comp (ψ i₀ k hik)
      = Ring.DirectLimit.of A (ψ · · ·) i₀ :=
    RingHom.ext fun y ↦ Ring.DirectLimit.of_f hik y
  rw [h1, ← h2, ← Polynomial.hom_eval₂, hpx, map_zero]

/-! ### The reflection of the direct limit into the small universe -/

/-- `IsSmallColimit ψ ιL` is the *existence* half of the universal property of the cocone `ιL`
among commutative rings in `Type u`: every compatible family of ring maps from the stages to a
ring in `Type u` factors through `L`.  Uniqueness is not required, and neither is the existence
of a colimit in the sense of `CategoryTheory`. -/
def IsSmallColimit {L : Type u} [CommRing L] (ιL : ∀ i, A i →+* L) : Prop :=
  ∀ (C : Type u) [CommRing C] (g : ∀ i, A i →+* C),
    (∀ i j (h : i ≤ j) (x : A i), g j (ψ i j h x) = g i x) →
      ∃ G : L →+* C, ∀ i x, G (ιL i x) = g i x

omit [IsDirectedOrder I] [Nonempty I] [DirectedSystem A fun i j h ↦ ψ i j h] in
/-- A compatible family of ring maps into a `u`-small ring, in any universe, factors through a
cocone with the universal property among rings in `Type u`. -/
theorem exists_hom_of_small {L : Type u} [CommRing L] {ιL : ∀ i, A i →+* L}
    (huniv : IsSmallColimit ψ ιL) (C : Type v) [CommRing C] [Small.{u} C] (g : ∀ i, A i →+* C)
    (hg : ∀ i j (h : i ≤ j) (x : A i), g j (ψ i j h x) = g i x) :
    ∃ G : L →+* C, ∀ i x, G (ιL i x) = g i x := by
  obtain ⟨G, hG⟩ := huniv (Shrink.{u} C)
    (fun i ↦ ((Shrink.ringEquiv C).symm.toRingHom.comp (g i)))
    (fun i j h x ↦ by simp [hg i j h x])
  refine ⟨(Shrink.ringEquiv C).toRingHom.comp G, fun i x ↦ ?_⟩
  have h := congrArg (Shrink.ringEquiv C) (hG i x)
  simpa using h

omit [DirectedSystem A fun i j h ↦ ψ i j h] in
/-- **The kernel of the reflection consists of nilpotents.**

Let `A∞` be the direct limit of a directed system of rings in `Type u` with module-finite
transition maps, indexed by a directed preorder in an arbitrary universe, and let `L` be a ring
in `Type u` carrying a cocone that is universal among rings in `Type u`.  Then any element of
`A∞` whose image in `L` vanishes is nilpotent.

No smallness hypothesis on the index is used.  The proof tests `A∞` against its own quotients by
primes: those are domains integral over a fixed stage, hence `u`-small, hence legitimate test
rings for the universal property, so an element killed in `L` is killed in every such quotient,
i.e. lies in every prime. -/
theorem isNilpotent_of_lift_eq_zero (hfin : ∀ i j (h : i ≤ j), (ψ i j h).Finite) (i₀ : I)
    {L : Type u} [CommRing L] {ιL : ∀ i, A i →+* L}
    (hιL : ∀ i j (h : i ≤ j) (x : A i), ιL j (ψ i j h x) = ιL i x)
    (huniv : IsSmallColimit ψ ιL) (z : Ring.DirectLimit A (ψ · · ·))
    (hz : Ring.DirectLimit.lift A (ψ · · ·) L ιL (fun i j h x ↦ hιL i j h x) z = 0) :
    IsNilpotent z := by
  rw [nilpotent_iff_mem_prime]
  intro q hq
  have : q.IsPrime := hq
  let _ : Algebra (A i₀) (Ring.DirectLimit A (ψ · · ·) ⧸ q) :=
    ((Ideal.Quotient.mk q).comp (Ring.DirectLimit.of A (ψ · · ·) i₀)).toAlgebra
  have : Algebra.IsIntegral (A i₀) (Ring.DirectLimit A (ψ · · ·) ⧸ q) :=
    ⟨fun b ↦ isIntegral_comp_surjective (isIntegral_of_directLimit ψ hfin i₀)
      (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective b⟩
  have : Small.{u} (Ring.DirectLimit A (ψ · · ·) ⧸ q) :=
    small_of_isIntegral_isDomain (A i₀) _
  obtain ⟨G, hG⟩ := exists_hom_of_small ψ huniv (Ring.DirectLimit A (ψ · · ·) ⧸ q)
    (fun i ↦ (Ideal.Quotient.mk q).comp (Ring.DirectLimit.of A (ψ · · ·) i))
    (fun i j h x ↦ by simp [Ring.DirectLimit.of_f])
  have hcomp : G.comp (Ring.DirectLimit.lift A (ψ · · ·) L ιL (fun i j h x ↦ hιL i j h x))
      = Ideal.Quotient.mk q := by
    refine Ring.DirectLimit.hom_ext _ fun i ↦ RingHom.ext fun x ↦ ?_
    simpa using hG i x
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hcomp]
  simpa using congrArg G hz

/-- **A stage element dying in the reflection has a power dying at a finite stage.**  This is the
descent step of [Stacks, Tag 09ZN] at a free index universe: it is weaker than the source's
"the relation already holds at a finite stage", and it is enough, because a power of a monic
polynomial is monic. -/
theorem exists_pow_eq_zero (hfin : ∀ i j (h : i ≤ j), (ψ i j h).Finite)
    {L : Type u} [CommRing L] {ιL : ∀ i, A i →+* L}
    (hιL : ∀ i j (h : i ≤ j) (x : A i), ιL j (ψ i j h x) = ιL i x)
    (huniv : IsSmallColimit ψ ιL) (i : I) (a : A i) (ha : ιL i a = 0) :
    ∃ (j : I) (h : i ≤ j) (n : ℕ), 0 < n ∧ ψ i j h (a ^ n) = 0 := by
  have hz : Ring.DirectLimit.lift A (ψ · · ·) L ιL (fun i j h x ↦ hιL i j h x)
      (Ring.DirectLimit.of A (ψ · · ·) i a) = 0 := by
    rw [Ring.DirectLimit.lift_of]; exact ha
  obtain ⟨n, hn⟩ := isNilpotent_of_lift_eq_zero ψ hfin i hιL huniv _ hz
  have hn' : Ring.DirectLimit.of A (ψ · · ·) i (a ^ (n + 1)) = 0 := by
    rw [map_pow, pow_succ, hn, zero_mul]
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact hn'
  exact ⟨j, hij, n + 1, Nat.succ_pos n, hj⟩

/-! ### The algebra of Tag 09ZN at a free index universe -/

/-- **The algebra of [Stacks, Tag 09ZN] at an index universe independent of the ring universe,
with no smallness hypothesis.**

Let `A` be a directed system of commutative rings in `Type u`, indexed by a nonempty directed
preorder `I` in an arbitrary universe, with module-finite transition maps.  Let `R` be a ring in
`Type u` mapping compatibly to every stage, of finite type at one stage `i₀`.  Let `L` be a ring
in `Type u` carrying a cocone on the system that is universal among rings in `Type u`, and
suppose `R → L` is integral.  Then `R → A j` is integral for some `j ≥ i₀`.

This is Steps 3–5 of the source proof.  Together with `RingHom.FiniteType` at the stage reached,
integrality gives module-finiteness, which is the conclusion the scheme-level argument needs over
an affine open of the base. -/
theorem exists_isIntegral (hfin : ∀ i j (h : i ≤ j), (ψ i j h).Finite)
    {R : Type u} [CommRing R] (r : ∀ i, R →+* A i)
    (hr : ∀ i j (h : i ≤ j) (x : R), ψ i j h (r i x) = r j x)
    {L : Type u} [CommRing L] {ιL : ∀ i, A i →+* L}
    (hιL : ∀ i j (h : i ≤ j) (x : A i), ιL j (ψ i j h x) = ιL i x)
    (huniv : IsSmallColimit ψ ιL) (i₀ : I) (hft : (r i₀).FiniteType)
    (hint : ((ιL i₀).comp (r i₀)).IsIntegral) :
    ∃ (j : I) (_ : i₀ ≤ j), (r j).IsIntegral := by
  classical
  have hrc : ∀ (a b : I) (h : a ≤ b), (ψ a b h).comp (r a) = r b :=
    fun a b h ↦ RingHom.ext (hr a b h)
  obtain ⟨s, hs⟩ := Stacks.RingTheory.EventualFiniteness.exists_finset_gens (r i₀) hft
  have key : ∀ x : A i₀, ∃ (j : I) (h : i₀ ≤ j) (P : Polynomial R), P.Monic ∧
      Polynomial.eval₂ (r j) (ψ i₀ j h x) P = 0 := by
    intro x
    obtain ⟨P, hP, hPx⟩ := hint (ιL i₀ x)
    have h0 : ιL i₀ (Polynomial.eval₂ (r i₀) x P) = 0 := by
      rw [Polynomial.hom_eval₂]; exact hPx
    obtain ⟨j, hij, n, _, hz⟩ := exists_pow_eq_zero ψ hfin hιL huniv i₀ _ h0
    refine ⟨j, hij, P ^ n, hP.pow n, ?_⟩
    rw [← hrc i₀ j hij, ← Polynomial.hom_eval₂, Polynomial.eval₂_pow]
    exact hz
  choose jx hjx Px hPxmonic hPxzero using key
  obtain ⟨j, hj⟩ := (insert i₀ (s.image jx)).exists_le
  have hij : i₀ ≤ j := hj i₀ (Finset.mem_insert_self _ _)
  have hgens : ∀ x ∈ (s : Set (A i₀)),
      ((ψ i₀ j hij).comp (r i₀)).IsIntegralElem (ψ i₀ j hij x) := by
    intro x hx
    have hxj : jx x ≤ j := hj _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))
    refine ⟨Px x, hPxmonic x, ?_⟩
    have hmap : ψ (jx x) j hxj (ψ i₀ (jx x) (hjx x) x) = ψ i₀ j hij x :=
      DirectedSystem.map_map (f := fun i j h ↦ ψ i j h) _ _ _
    rw [hrc i₀ j hij, ← hmap, ← hrc (jx x) j hxj, ← Polynomial.hom_eval₂, hPxzero x, map_zero]
  refine ⟨j, hij, ?_⟩
  rw [← hrc i₀ j hij]
  exact Stacks.RingTheory.EventualFiniteness.isIntegral_comp_of_isIntegralElem_image (r i₀)
    (ψ i₀ j hij) (hfin i₀ j hij).to_isIntegral
    (Stacks.RingTheory.EventualFiniteness.isIntegralElem_image_of_gens (r i₀) (ψ i₀ j hij)
      (s : Set (A i₀)) hs hgens)

/-! ### `IsSmallColimit` is satisfiable: the honest colimit at a small index -/

/-- **The hypothesis `IsSmallColimit` is not vacuous.**  When the index type lives in the same
universe as the rings, the direct limit itself lies in `Type u` and its own universal property is
exactly `IsSmallColimit`.  So `exists_isIntegral` specialises to the source's Step 3 verbatim,
and the free-index-universe statement is a genuine generalisation of it rather than a vacuous
one. -/
theorem isSmallColimit_directLimit {J : Type u} [Preorder J] {B : J → Type u}
    [∀ i, CommRing (B i)] (χ : ∀ i j, i ≤ j → B i →+* B j) :
    IsSmallColimit χ (Ring.DirectLimit.of B (χ · · ·)) := by
  intro C _ g hg
  exact ⟨Ring.DirectLimit.lift B (χ · · ·) C g fun i j h x ↦ hg i j h x,
    fun i x ↦ by rw [Ring.DirectLimit.lift_of]⟩

end Stacks.IntegralLimitAlgebra

end

end
