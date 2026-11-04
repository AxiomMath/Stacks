module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Noetherian.Retrocompact
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticImage

/-!
# Extending a rational map after a proper modification

Let `S` be a scheme, `X` a Noetherian scheme over `S` and `Y` a scheme proper over `S`. An
`S`-rational map `X ⇢ Y` extends to an honest `S`-morphism after replacing `X` by a proper
modification `X' ⟶ X` which changes nothing over the domain of definition of the rational map.
This is Tag 0C4V, and `exists_proper_modification_resolving_partialMap` is its statement here.

The modification is the scheme-theoretic image of the graph: a rational map defined on a dense
open `U ⊆ X` with underlying morphism `h : U ⟶ Y` gives a morphism
`q : U ⟶ Y ×_S X` whose two components are `h` and the inclusion of `U`, and `X'` is taken to be
the scheme-theoretic image of `q`, with `p : X' ⟶ X` the second projection and `f' : X' ⟶ Y` the
first. Properness of `p` comes from properness of `Y ⟶ S` (the projection `Y ×_S X ⟶ X` is
proper, and a closed immersion followed by a proper morphism is proper). That `p` is an
isomorphism over `U` is the scheme-theoretic-image statement for a section over a retrocompact
open: `U` is retrocompact in `X` because `X` is Noetherian, and over `U` the morphism `q` is a
section of `Y ×_S X ⟶ X`, so the image agrees with `U` there.

## Main results

* `Stacks.Divisors.exists_proper_modification_resolving_partialMap`: Tag 0C4V, a partial map to
  a scheme proper over the base extends across a proper modification of its source.

## Implementation notes

A rational map together with the open set on which it is displayed is
`AlgebraicGeometry.Scheme.PartialMap`. The inverse image of its domain under the modification is
presented as the pullback `X' ×_X U`, so "the modification is an isomorphism over the domain" is
the canonical assertion `IsIso (pullback.snd p f.domain.ι)`, and "the extension agrees with the
rational map there" is an equality of two morphisms out of that same pullback. Stating both on
the pullback avoids having to transport along an isomorphism of schemes.

Agreement of the two morphisms is checked after cancelling the isomorphism
`pullback.snd p f.domain.ι`, whose inverse is the lift of the factorization `q.toImage` through
the pullback; that lift exists because `q.toImage ≫ q.imageι` is `q`.

## References

* [Stacks Project, Tag 0C4V](https://stacks.math.columbia.edu/tag/0C4V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Stacks.Divisors

/-- **Stacks Project, Tag 0C4V.** An `S`-rational map from a Noetherian scheme to a scheme
proper over `S` extends to an `S`-morphism after a proper modification which is unchanged over
the rational map's domain. -/
@[stacks 0C4V]
theorem exists_proper_modification_resolving_partialMap
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S] [IsNoetherian X]
    [IsProper (Y ↘ S)] (f : X.PartialMap Y) [f.IsOver S] :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ X) (f' : X' ⟶ Y),
      IsProper p ∧
        f' ≫ (Y ↘ S) = p ≫ (X ↘ S) ∧
        IsIso (pullback.snd p f.domain.ι) ∧
        pullback.fst p f.domain.ι ≫ f' = pullback.snd p f.domain.ι ≫ f.hom := by
  have hcompat : f.hom ≫ (Y ↘ S) = f.domain.ι ≫ (X ↘ S) := by
    simp [(Scheme.Hom.isOver_iff (f := f.hom) (S := S)).mp (inferInstance : f.hom.IsOver S)]
  let q : f.domain.toScheme ⟶ pullback (Y ↘ S) (X ↘ S) := pullback.lift f.hom f.domain.ι hcompat
  let i := q.imageι
  let p : q.image ⟶ X := i ≫ pullback.snd (Y ↘ S) (X ↘ S)
  let f' : q.image ⟶ Y := i ≫ pullback.fst (Y ↘ S) (X ↘ S)
  have hq : q ≫ pullback.snd (Y ↘ S) (X ↘ S) = f.domain.ι := pullback.lift_snd _ _ _
  have hIso : IsIso (pullback.snd p f.domain.ι) := by
    simpa [p, i, Category.assoc] using
      (AlgebraicGeometry.isIso_pullback_snd_imageι_comp_of_section
        (pullback.snd (Y ↘ S) (X ↘ S)) f.domain
        (noetherianSpace_isRetrocompact X (f.domain : Set X)) q hq)
  refine ⟨q.image, p, f', by dsimp [p, i]; infer_instance, ?_, hIso, ?_⟩
  · dsimp [f', p]; simp only [Category.assoc, pullback.condition]
  · have hfactor : q.toImage ≫ i = q := Scheme.Hom.toImage_imageι q
    let t : f.domain.toScheme ⟶ pullback p f.domain.ι :=
      pullback.lift q.toImage (𝟙 _) (by
        simpa only [p, i, Category.id_comp, ← Category.assoc, hfactor] using hq)
    have ht : t ≫ pullback.snd p f.domain.ι = 𝟙 _ := pullback.lift_snd _ _ _
    have hte : t = (asIso (pullback.snd p f.domain.ι)).inv := by
      apply (cancel_mono (pullback.snd p f.domain.ι)).1; simp [ht]
    apply (cancel_epi (asIso (pullback.snd p f.domain.ι)).inv).1
    rw [← hte]
    simp only [t, pullback.lift_fst, pullback.lift_snd, Category.id_comp,
      f', ← Category.assoc, hfactor, q]

end Stacks.Divisors

end
