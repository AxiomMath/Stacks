module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace

/-!
# Finite fibre products of relative projective spaces

The Stacks proof of Chow's lemma over a Noetherian base (Tag 0200) immerses the common dense
open `U` of a finite affine cover into the fibre product
`ℙ^{n₁}_S ×_S … ×_S ℙ^{n_m}_S` of the projective spaces receiving the individual charts, and uses
that this fibre product is again projective over `S` — iterated Segre embeddings, Stacks 01WD.

This file produces that data for an arbitrary finite nonempty family of charts, reducing it to a
single named hypothesis: `AlgebraicGeometry.HasSegreEmbedding`.

## Main definitions

* `AlgebraicGeometry.HasSegreEmbedding` is **Stacks 01WD** for the base `S`: the fibre product
  of two projective spaces over `S` closed-immerses into a projective space over `S`, over `S`.

## Main results

* `AlgebraicGeometry.exists_chartEnvelope`: granted `HasSegreEmbedding S`, a nonempty list of
  immersions of `X` into projective spaces over `S` factors through a single scheme `P`,
  projective over `S`, into which `X` immerses and which carries a projection over `S` onto
  each of the given projective spaces compatibly with the charts.
* `AlgebraicGeometry.exists_chartEnvelope_of_finite`: the same for a finite nonempty index
  type, which is the form the proof of Chow's lemma uses.

## Implementation notes

`HasSegreEmbedding` is deliberately stated with the target dimension existentially quantified,
which is *weaker* than Stacks 01WD — 01WD produces the explicit `n * m + n + m` — so every
result below is correspondingly more general than one assuming the explicit dimension. It is a
hypothesis here because nothing in this repository and nothing in Mathlib constructs a Segre
embedding: the token `Segre` does not occur in any `.lean` file of either Lean tree or of
vendored Mathlib.

The envelope is produced as a flat existential rather than as a recursively defined fibre
product indexed by the list. A recursive definition makes the *type* of the projections depend
on the list, so every commutativity in the induction step has to be checked across an unfolding
of that recursion, which in practice needs transparency-override options. With the fibre product
hidden inside an existential the dependency disappears, and so does the need for any such option.

The induction is over `List I` with a one-element base case, so the empty list never enters the
inductive step, where it would contribute a spurious factor of `S`.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v

variable {X S : Scheme.{u}}

/-- **Stacks 01WD for the base `S`, the Segre embedding.** The fibre product over `S` of two
projective spaces over `S` admits a closed immersion into a projective space over `S`, over `S`.

Stated with the target dimension existential, so that assuming it is weaker than assuming
Stacks 01WD itself, which produces `n * m + n + m`. -/
def HasSegreEmbedding (S : Scheme.{u}) : Prop :=
  ∀ n m : ℕ, ∃ (N : ℕ)
      (e : pullback (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ⟶ ProjectiveSpace N S),
      IsClosedImmersion e ∧ e ≫ (ProjectiveSpace N S ↘ S) =
        pullback.fst (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ≫
          (ProjectiveSpace n S ↘ S)

/-- **A nonempty list of projective charts of `X` over `S` factors through a single scheme
projective over `S`.** Granted the Segre embedding for `S`, there are a scheme `P`, a closed
immersion of `P` into a projective space over `S` over `S`, an immersion `X ⟶ P` over `S`, and
a projection of `P` over `S` onto each chart's projective space through which that chart
factors.

This is the fibre product `ℙ^{n₁}_S ×_S … ×_S ℙ^{n_m}_S` of the Stacks proof of Chow's lemma
over a Noetherian base, presented as an existential so that the projections do not have a type
depending on the list. -/
theorem exists_chartEnvelope (hsegre : HasSegreEmbedding S) {f : X ⟶ S} {I : Type v} (n : I → ℕ)
    (j : ∀ i, X ⟶ ProjectiveSpace (n i) S) (hj : ∀ i, IsImmersion (j i))
    (hcomm : ∀ i, j i ≫ (ProjectiveSpace (n i) S ↘ S) = f) :
    ∀ l : List I, l ≠ [] →
      ∃ (P : Scheme.{u}) (q : P ⟶ S) (N : ℕ) (c : P ⟶ ProjectiveSpace N S) (a : X ⟶ P),
        IsClosedImmersion c ∧ c ≫ (ProjectiveSpace N S ↘ S) = q ∧
          IsImmersion a ∧ a ≫ q = f ∧
          ∀ i ∈ l, ∃ ri : P ⟶ ProjectiveSpace (n i) S,
            ri ≫ (ProjectiveSpace (n i) S ↘ S) = q ∧ a ≫ ri = j i := by
  intro l
  induction l with
  | nil => simp
  | cons i₀ rest ih =>
      intro _
      cases rest with
      | nil =>
          refine ⟨ProjectiveSpace (n i₀) S, ProjectiveSpace (n i₀) S ↘ S, n i₀, 𝟙 _, j i₀,
            inferInstance, Category.id_comp _, hj i₀, hcomm i₀, fun i hi => ?_⟩
          obtain rfl : i = i₀ := by simpa using hi
          exact ⟨𝟙 _, Category.id_comp _, Category.comp_id _⟩
      | cons i₁ tail =>
          obtain ⟨P, q, N, c, a, hc, hcq, -, haq, hr⟩ := ih (List.cons_ne_nil _ _)
          -- the fibre product of `ℙ^{n i₀}_S` with the envelope of the tail
          let p : ProjectiveSpace (n i₀) S ⟶ S := ProjectiveSpace (n i₀) S ↘ S
          let d : ProjectiveSpace N S ⟶ S := ProjectiveSpace N S ↘ S
          let a' : X ⟶ pullback p q := pullback.lift (j i₀) a ((hcomm i₀).trans haq.symm)
          have ha'fst : a' ≫ pullback.fst p q = j i₀ := pullback.lift_fst _ _ _
          have ha'snd : a' ≫ pullback.snd p q = a := pullback.lift_snd _ _ _
          -- `pullback p q` closed-immerses into `pullback p d`, being a base change of `c`
          let k : pullback p q ⟶ pullback p d := pullback.lift (pullback.fst p q)
            (pullback.snd p q ≫ c) (by rw [Category.assoc, hcq, pullback.condition])
          have hkfst : k ≫ pullback.fst p d = pullback.fst p q := pullback.lift_fst _ _ _
          have hksnd : k ≫ pullback.snd p d = pullback.snd p q ≫ c := pullback.lift_snd _ _ _
          have hbig : IsPullback (pullback.snd p q) (k ≫ pullback.fst p d) (c ≫ d) p := by
            rw [hkfst, hcq]
            exact (IsPullback.of_hasPullback p q).flip
          have : IsClosedImmersion k := MorphismProperty.IsStableUnderBaseChange.of_isPullback
            (hbig.of_bot hksnd.symm (IsPullback.of_hasPullback p d).flip) hc
          -- and `pullback p d` closed-immerses into a single projective space, by Segre
          obtain ⟨M, e, he, hebase⟩ := hsegre (n i₀) N
          have : IsClosedImmersion e := he
          refine ⟨pullback p q, pullback.fst p q ≫ p, M, k ≫ e, a',
            inferInstance, ?_, ?_, ?_, ?_⟩
          · rw [Category.assoc, hebase, ← Category.assoc, hkfst]
          · have : IsImmersion (a' ≫ pullback.fst p q) := ha'fst ▸ hj i₀
            exact IsImmersion.of_comp a' (pullback.fst p q)
          · rw [← Category.assoc, ha'fst, hcomm i₀]
          · intro i hi
            obtain rfl | h := List.mem_cons.mp hi
            · exact ⟨pullback.fst p q, rfl, ha'fst⟩
            · obtain ⟨ri, hri, hari⟩ := hr i h
              exact ⟨pullback.snd p q ≫ ri, by rw [Category.assoc, hri, pullback.condition],
                by rw [← Category.assoc, ha'snd, hari]⟩

/-- **A finite nonempty family of projective charts of `X` over `S` factors through a single
scheme projective over `S`.** The form of `AlgebraicGeometry.exists_chartEnvelope` used in the
proof of Chow's lemma over a Noetherian base. -/
theorem exists_chartEnvelope_of_finite (hsegre : HasSegreEmbedding S) {f : X ⟶ S} {I : Type v}
    [Finite I] [Nonempty I] (n : I → ℕ) (j : ∀ i, X ⟶ ProjectiveSpace (n i) S)
    (hj : ∀ i, IsImmersion (j i)) (hcomm : ∀ i, j i ≫ (ProjectiveSpace (n i) S ↘ S) = f) :
    ∃ (P : Scheme.{u}) (q : P ⟶ S) (N : ℕ) (c : P ⟶ ProjectiveSpace N S) (a : X ⟶ P),
      IsClosedImmersion c ∧ c ≫ (ProjectiveSpace N S ↘ S) = q ∧
        IsImmersion a ∧ a ≫ q = f ∧
        ∀ i, ∃ ri : P ⟶ ProjectiveSpace (n i) S,
          ri ≫ (ProjectiveSpace (n i) S ↘ S) = q ∧ a ≫ ri = j i := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hne : (Finset.univ : Finset I).toList ≠ [] := by
    simp [Finset.toList_eq_nil, Finset.univ_nonempty.ne_empty]
  obtain ⟨P, q, N, c, a, hc, hcq, ha, haq, hr⟩ := exists_chartEnvelope hsegre n j hj hcomm _ hne
  exact ⟨P, q, N, c, a, hc, hcq, ha, haq, fun i => hr i (by simp)⟩

end AlgebraicGeometry
