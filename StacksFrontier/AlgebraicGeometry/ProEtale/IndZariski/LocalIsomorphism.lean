module

public import StacksFrontier.RingTheory.LocalIso.IdentifiesLocalRings
public import Mathlib.RingTheory.LocalIso
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Local isomorphisms and the identification of local rings

A ring map is a *local isomorphism* if, near each prime of its target, it induces an open
immersion on spectra. It *identifies local rings* if the induced map between the localizations
at every prime of the target and at its contraction is an isomorphism. For a local isomorphism
finitely many principal opens cover the target spectrum, and each of the corresponding
localizations is a principal localization of the source as well.

## Main definitions

* `AlgebraicGeometry.ProEtale.IdentifiesLocalRings`: all canonical maps on local rings are
  isomorphisms.

## Main results

* `AlgebraicGeometry.ProEtale.exists_fin_localization_away`: a local isomorphism admits a finite
  cover by principal localizations which are principal localizations of the source.

## Implementation notes

Being a local isomorphism is `Algebra.IsLocalIso`, the first of the two notions defined here,
formulated using standard open immersions on principal localizations. Identifying local rings is
expressed by bijectivity of `Localization.localRingHom`, which for a ring map is equivalent to
being a ring isomorphism.

In the finite cover, the equation saying that the chosen elements of the target generate the unit
ideal expresses that their principal opens cover the target spectrum. `IsLocalization.Away`
expresses that the canonical map from the source to each of these localizations is a localization
away from the corresponding source element, hence identifies the two principal localizations as
algebras over the source.

## References

* [Stacks Project, Tag 096E](https://stacks.math.columbia.edu/tag/096E)
* [Stacks Project, Tag 096J](https://stacks.math.columbia.edu/tag/096J)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u v

/-- A local isomorphism admits a finite cover by principal localizations that
are principal localizations of the source. -/
@[stacks 096J]
theorem exists_fin_localization_away
    (A : Type u) (B : Type v) [CommSemiring A] [CommSemiring B]
    [Algebra A B] [Algebra.IsLocalIso A B] :
    ∃ (n : ℕ) (g : Fin n → B) (f : Fin n → A),
      Ideal.span (Set.range g) = ⊤ ∧
        ∀ i, IsLocalization.Away (f i) (Localization.Away (g i)) := by
  classical
  obtain ⟨t, ht, hspan⟩ := (Ideal.span_eq_top_iff_finite _).mp
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top A B)
  let g : Fin t.card → B := fun j => (t.equivFin.symm j).1
  have hspan' : Ideal.span (Set.range g) = ⊤ := by
    change Ideal.span (Set.range ((Subtype.val : t → B) ∘ t.equivFin.symm)) = ⊤
    simpa [Set.range_comp] using hspan
  have hexists (j : Fin t.card) : ∃ f : A, IsLocalization.Away f (Localization.Away (g j)) := by
    let : Algebra.IsStandardOpenImmersion A (Localization.Away (g j)) := ht (by simp [g])
    exact Algebra.IsStandardOpenImmersion.exists_away A (Localization.Away (g j))
  exact ⟨t.card, g, fun j => Classical.choose (hexists j), hspan',
    fun j => Classical.choose_spec (hexists j)⟩

end AlgebraicGeometry.ProEtale

end
