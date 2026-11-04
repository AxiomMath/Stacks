module

public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence

/-!
# Comparing the equivalences on families of morphisms with fixed target

Stacks tag 00VV, for families of morphisms with fixed target — Mathlib's
`CategoryTheory.PreZeroHypercover`:

1. combinatorially equivalent families are tautologically equivalent;
2. tautologically equivalent families refine each other;
3. combinatorial equivalence is an equivalence relation;
4. tautological equivalence is an equivalence relation;
5. mutual refinement is an equivalence relation.

## Refinement here is Mathlib's `PreZeroHypercover.Hom`

Stacks 00VT (2) defines a refinement of `𝒱` by `𝒰` as a morphism of families over the identity
of the common target, and `ZeroOver` records that these are exactly Mathlib's
`PreZeroHypercover.Hom`. So "`𝒰` refines `𝒱`" is `Nonempty (E.Hom F)`, and parts (2) and (5)
are stated that way rather than over a separate refinement predicate. Part (5) then costs
almost nothing: reflexivity is `Hom.id` and transitivity is `Hom.comp`.

## The `Equivalence` bundlings are single-universe

Parts (3), (4) and (5) are given twice: as `refl`/`symm`/`trans` lemmas, which allow the three
families to be indexed in three different universes, and as a bundled `Equivalence`, which is
what the source literally asserts and which forces one universe since `Equivalence` is a
relation on a single type.
-/

@[expose] public section

namespace CategoryTheory.PreZeroHypercover

universe w w' w'' v u

variable {C : Type u} [Category.{v} C] {U : C}

/-! ### (1) and (2): the two implications -/

/-- **Stacks 00VV (1).** Combinatorially equivalent families are tautologically equivalent: an
equality of sources gives an isomorphism between them, via `eqToIso`. -/
@[stacks 00VV "(1)"]
theorem tautologicallyEquivalent_of_combinatoriallyEquivalent
    (E : PreZeroHypercover.{w} U) (F : PreZeroHypercover.{w'} U) :
    CombinatoriallyEquivalent E F → TautologicallyEquivalent E F := by
  rintro ⟨⟨α, h, heq⟩, β, h', heq'⟩
  exact ⟨⟨α, fun i => ⟨eqToIso (h i), by simpa using (heq i).symm⟩⟩,
    ⟨β, fun j => ⟨eqToIso (h' j), by simpa using (heq' j).symm⟩⟩⟩

/-- **Stacks 00VV (2).** Tautologically equivalent families refine each other: the horizontal
isomorphism of each triangle is in particular a morphism over the common target, so the
triangles assemble into a `PreZeroHypercover.Hom` in each direction. -/
@[stacks 00VV "(2)"]
theorem nonempty_hom_and_nonempty_hom_of_tautologicallyEquivalent
    (E : PreZeroHypercover.{w} U) (F : PreZeroHypercover.{w'} U) :
    TautologicallyEquivalent E F → Nonempty (E.Hom F) ∧ Nonempty (F.Hom E) := by
  rintro ⟨⟨α, hα⟩, β, hβ⟩
  choose e he using hα
  choose e' he' using hβ
  exact ⟨⟨⟨α, fun i => (e i).hom, he⟩⟩, ⟨⟨β, fun j => (e' j).hom, he'⟩⟩⟩

/-! ### Consequences for the generated sieve

Combinatorially equivalent families generate the same *presieve*
(`presieve₀_eq_of_combinatoriallyEquivalent`). Tautologically equivalent families need not:
their sources are only isomorphic, so the two sets of arrows differ. What survives is the
generated *sieve*, which is what every sheaf condition depends on. -/

/-- A refinement makes the generated sieve smaller: each `E.f i` factors through
`F.f (φ.s₀ i)`.

Mathlib's `Hom.sieve₀_le_sieve₀` says this for two families indexed in the *same* universe;
this version allows the two index universes to differ, which is what the relations of 00VU
need. -/
lemma generate_presieve₀_le_of_hom {E : PreZeroHypercover.{w} U} {F : PreZeroHypercover.{w'} U}
    (φ : E.Hom F) : Sieve.generate E.presieve₀ ≤ Sieve.generate F.presieve₀ := by
  rw [Sieve.generate_le_iff]
  rintro Y g ⟨i⟩
  exact ⟨F.X (φ.s₀ i), φ.h₀ i, F.f (φ.s₀ i), ⟨φ.s₀ i⟩, φ.w₀ i⟩

/-- Tautologically equivalent families generate the same sieve. This is the form in which
00VV (2) is consumed: it is exactly what makes the sheaf conditions agree (00VW), and it
follows from mutual refinement. -/
lemma generate_presieve₀_eq_of_tautologicallyEquivalent (E : PreZeroHypercover.{w} U)
    (F : PreZeroHypercover.{w'} U) (h : TautologicallyEquivalent E F) :
    Sieve.generate E.presieve₀ = Sieve.generate F.presieve₀ := by
  obtain ⟨⟨φ⟩, ⟨ψ⟩⟩ := nonempty_hom_and_nonempty_hom_of_tautologicallyEquivalent E F h
  exact le_antisymm (generate_presieve₀_le_of_hom φ) (generate_presieve₀_le_of_hom ψ)

/-! ### (3) Combinatorial equivalence is an equivalence relation -/

/-- **Stacks 00VV (3).** Combinatorial equivalence is reflexive. -/
@[stacks 00VV "(3)"]
theorem combinatoriallyEquivalent_refl (E : PreZeroHypercover.{w} U) :
    CombinatoriallyEquivalent E E :=
  ⟨⟨id, fun _ => rfl, fun _ => by simp⟩, ⟨id, fun _ => rfl, fun _ => by simp⟩⟩

/-- **Stacks 00VV (3).** Combinatorial equivalence is transitive: compose the index maps and
the source equalities, and `eqToHom_trans` composes the transports. -/
@[stacks 00VV "(3)"]
theorem combinatoriallyEquivalent_trans (E : PreZeroHypercover.{w} U)
    (F : PreZeroHypercover.{w'} U) (G : PreZeroHypercover.{w''} U) :
    CombinatoriallyEquivalent E F → CombinatoriallyEquivalent F G →
      CombinatoriallyEquivalent E G := by
  rintro ⟨⟨α₁, h₁, e₁⟩, β₁, h₁', e₁'⟩ ⟨⟨α₂, h₂, e₂⟩, β₂, h₂', e₂'⟩
  refine ⟨⟨fun i => α₂ (α₁ i), fun i => (h₁ i).trans (h₂ (α₁ i)), fun i => ?_⟩,
    fun j => β₁ (β₂ j), fun j => (h₂' j).trans (h₁' (β₂ j)), fun j => ?_⟩
  · rw [e₁ i, e₂ (α₁ i), ← Category.assoc, eqToHom_trans]
  · rw [e₂' j, e₁' (β₂ j), ← Category.assoc, eqToHom_trans]

/-- **Stacks 00VV (3)** as stated there: combinatorial equivalence *is* an equivalence relation
on the families of morphisms with fixed target `U`. -/
@[stacks 00VV "(3)"]
theorem combinatoriallyEquivalent_equivalence :
    _root_.Equivalence (fun E F : PreZeroHypercover.{w} U => CombinatoriallyEquivalent E F) where
  refl := combinatoriallyEquivalent_refl
  symm h := h.symm
  trans := combinatoriallyEquivalent_trans _ _ _

/-! ### (4) Tautological equivalence is an equivalence relation -/

/-- **Stacks 00VV (4).** Tautological equivalence is reflexive. -/
@[stacks 00VV "(4)"]
theorem tautologicallyEquivalent_refl (E : PreZeroHypercover.{w} U) :
    TautologicallyEquivalent E E :=
  ⟨⟨id, fun _ => ⟨Iso.refl _, by simp⟩⟩, ⟨id, fun _ => ⟨Iso.refl _, by simp⟩⟩⟩

/-- **Stacks 00VV (4).** Tautological equivalence is transitive: compose the index maps, and
compose the triangles' horizontal isomorphisms with `Iso.trans`. -/
@[stacks 00VV "(4)"]
theorem tautologicallyEquivalent_trans (E : PreZeroHypercover.{w} U)
    (F : PreZeroHypercover.{w'} U) (G : PreZeroHypercover.{w''} U) :
    TautologicallyEquivalent E F → TautologicallyEquivalent F G →
      TautologicallyEquivalent E G := by
  rintro ⟨⟨α₁, h₁⟩, β₁, h₁'⟩ ⟨⟨α₂, h₂⟩, β₂, h₂'⟩
  refine ⟨⟨fun i => α₂ (α₁ i), fun i => ?_⟩, fun j => β₁ (β₂ j), fun j => ?_⟩
  · obtain ⟨e₁, he₁⟩ := h₁ i
    obtain ⟨e₂, he₂⟩ := h₂ (α₁ i)
    exact ⟨e₁ ≪≫ e₂, by rw [Iso.trans_hom, Category.assoc, he₂, he₁]⟩
  · obtain ⟨e₂, he₂⟩ := h₂' j
    obtain ⟨e₁, he₁⟩ := h₁' (β₂ j)
    exact ⟨e₂ ≪≫ e₁, by rw [Iso.trans_hom, Category.assoc, he₁, he₂]⟩

/-- **Stacks 00VV (4)** as stated there: tautological equivalence *is* an equivalence relation
on the families of morphisms with fixed target `U`. -/
@[stacks 00VV "(4)"]
theorem tautologicallyEquivalent_equivalence :
    _root_.Equivalence (fun E F : PreZeroHypercover.{w} U => TautologicallyEquivalent E F) where
  refl := tautologicallyEquivalent_refl
  symm h := h.symm
  trans := tautologicallyEquivalent_trans _ _ _

/-! ### (5) Mutual refinement is an equivalence relation -/

/-- **Stacks 00VV (5).** Every family refines itself, by the identity refinement. -/
@[stacks 00VV "(5)"]
theorem nonempty_hom_refl (E : PreZeroHypercover.{w} U) :
    Nonempty (E.Hom E) ∧ Nonempty (E.Hom E) :=
  ⟨⟨Hom.id E⟩, ⟨Hom.id E⟩⟩

/-- **Stacks 00VV (5).** Mutual refinement is transitive, by composing refinements. -/
@[stacks 00VV "(5)"]
theorem nonempty_hom_trans (E : PreZeroHypercover.{w} U) (F : PreZeroHypercover.{w'} U)
    (G : PreZeroHypercover.{w''} U) :
    (Nonempty (E.Hom F) ∧ Nonempty (F.Hom E)) → (Nonempty (F.Hom G) ∧ Nonempty (G.Hom F)) →
      (Nonempty (E.Hom G) ∧ Nonempty (G.Hom E)) :=
  fun ⟨⟨f⟩, ⟨f'⟩⟩ ⟨⟨g⟩, ⟨g'⟩⟩ => ⟨⟨f.comp g⟩, ⟨g'.comp f'⟩⟩

/-- **Stacks 00VV (5)** as stated there: mutual refinement *is* an equivalence relation on the
families of morphisms with fixed target `U`. Symmetry is the swap. -/
@[stacks 00VV "(5)"]
theorem nonempty_hom_equivalence :
    _root_.Equivalence
      (fun E F : PreZeroHypercover.{w} U => Nonempty (E.Hom F) ∧ Nonempty (F.Hom E)) where
  refl := nonempty_hom_refl
  symm h := ⟨h.2, h.1⟩
  trans := nonempty_hom_trans _ _ _

end CategoryTheory.PreZeroHypercover
