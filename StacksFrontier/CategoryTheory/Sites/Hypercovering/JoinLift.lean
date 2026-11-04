module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.JoinCovering

/-!
# Lifting a pair of simplices of a hypercovering

Let `(C, J)` be a site with fibre products and let `K` be a hypercovering, either of the final
presheaf in the sense of Stacks 09VU or of an object `X` in the sense of Stacks 01G5. For
`m n : ℕ` write `N = m + n + 1` and let `⦋m⦌ ⟶ ⦋N⦌ ⟵ ⦋n⦌` be the two complementary face
inclusions. This file proves that a pair consisting of an `m`-simplex and an `n`-simplex of `K`
over an object `A` is, locally on `A`, the pair of complementary faces of a single `N`-simplex
of `K`.

This is the degree-`N` clause of the definition of a hypercovering, read through the join
`Δ[m] ⋆ Δ[n] = Δ[N]`: it is Tag 01GN for the inclusion of the two ends of that join, which
`Stacks.CategoryTheory.Hypercovering.isCoveringOver_joinProdLift` supplies for a hypercovering of
an *object*. For a hypercovering of the final presheaf it is transported there along the Yoneda
embedding into the slice over the final presheaf; for a hypercovering of an object it is read off
directly, over the localized site `C/X`.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.joinLiftSieve`: the sieve of arrows along which a pair of
  simplices lifts to a single simplex of degree `m + n + 1`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.joinLiftSieve_mem`: that sieve is covering, for a
  hypercovering of the final presheaf.
* `Stacks.CategoryTheory.Hypercovering.homLifts_mem_over`: a section of a semi-representable
  object over `X` lifts, locally on the site `C/X`, through a covering morphism of
  semi-representable objects over `X`.
* `Stacks.CategoryTheory.Hypercovering.joinLiftSieve_mem_over`: the join-lift sieve is covering
  for the localized topology of `C/X`, for a hypercovering of the object `X`.

## Implementation notes

A simplex of `K` over `A` is a morphism out of the one-summand formal coproduct on `A`, which is
how the statement avoids naming an index and a morphism separately; `FormalCoproduct.incl` is
that one-summand formal coproduct, and `sectionEquiv` relates such morphisms to sections of the
associated presheaf where that is wanted.

The transport for a hypercovering of the final presheaf is the one of
`Stacks.CategoryTheory.Hypercovering.isHypercovering_yonedaFormal`: a hypercovering of the final
presheaf becomes, under `yonedaFormal`, a hypercovering of the terminal object of the category of
presheaves for `localPretopology`, where the covering-permanence chain and hence Tag 01GN apply.
A covering morphism there is locally surjective on maps out of the test objects
(`homLocallySurjective_of_covering'`), and `yonedaFormal` is fully faithful, so the local lifts it
produces descend to `C`.

For a hypercovering of an object no transport is needed, because `isCoveringOver_joinProdLift` is
stated there; what the Yoneda detour supplies in that case is only the instance
`Precoverage.IsStableUnderComposition`, the indexed-family composition axiom of Tag 00VH (2),
which Mathlib's presieve-level `Pretopology` does not carry. It is obtained instead from
`GrothendieckTopology.toPretopology`: the largest pretopology generating `J` has that instance,
and a covering morphism for `J` is one for it by `isCoveringOver_toPretopology`, which is why
`joinLiftSieve_mem_over` concludes in the Grothendieck topology `J.over X` and not in a
pretopology.

## References

* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 01GN](https://stacks.math.columbia.edu/tag/01GN)
* [Stacks Project, Tag 0DAX](https://stacks.math.columbia.edu/tag/0DAX)
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SSet.stdSimplex

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]

/-- The sieve on `A` of the arrows along which a pair consisting of an `m`-simplex and an
`n`-simplex of `K` over `A` lifts to a single `(m + n + 1)`-simplex having them as its two
complementary faces. -/
def joinLiftSieve (K : SimplicialObject (FormalCoproduct.{w} C)) (m n : ℕ) {A : C}
    (s₁ : (FormalCoproduct.incl C).obj A ⟶ K.obj (op ⦋m⦌))
    (s₂ : (FormalCoproduct.incl C).obj A ⟶ K.obj (op ⦋n⦌)) : Sieve A where
  arrows _ g := ∃ t : (FormalCoproduct.incl C).obj _ ⟶ K.obj (op ⦋m + n + 1⦌),
    t ≫ K.map (joinFst m n).op = (FormalCoproduct.incl C).map g ≫ s₁ ∧
      t ≫ K.map (joinSnd m n).op = (FormalCoproduct.incl C).map g ≫ s₂
  downward_closed := by
    rintro A' A'' g ⟨t, h₁, h₂⟩ h
    refine ⟨(FormalCoproduct.incl C).map h ≫ t, ?_, ?_⟩
    · rw [Category.assoc, h₁, ← Category.assoc, ← Functor.map_comp]
    · rw [Category.assoc, h₂, ← Category.assoc, ← Functor.map_comp]

/-- **A pair of simplices of a hypercovering of the final presheaf is locally a pair of
complementary faces.** For a hypercovering `K` of the final presheaf, `m n : ℕ` and a pair
consisting of an `m`-simplex and an `n`-simplex of `K` over `A`, the arrows `A' ⟶ A` along which
the pair lifts to a single `(m + n + 1)`-simplex of `K` form a covering sieve of `A`.

This is Tag 01GN for the inclusion of the two ends of the join `Δ[m] ⋆ Δ[n] = Δ[m + n + 1]`,
applied to the hypercovering of the terminal presheaf which `isHypercovering_yonedaFormal`
produces, and brought back to `C` by full faithfulness of `yonedaFormal`. -/
theorem joinLiftSieve_mem (J : Pretopology C) (H : HypercoveringOfTerminal.{max w u v} J)
    (m n : ℕ) {A : C}
    (s₁ : (FormalCoproduct.incl C).obj A ⟶ H.toSimplicialObject.obj (op ⦋m⦌))
    (s₂ : (FormalCoproduct.incl C).obj A ⟶ H.toSimplicialObject.obj (op ⦋n⦌)) :
    joinLiftSieve H.toSimplicialObject m n s₁ s₂ ∈ J.toGrothendieck A := by
  have hFF : (yonedaFormal : FormalCoproduct.{max w u v} C ⥤ _).FullyFaithful :=
    yonedaFormalFullyFaithful
  have hLhyp : IsHypercovering (localPretopology.{v, u, max w u v} J)
      (H.toSimplicialObject ⋙ yonedaFormal) := isHypercovering_yonedaFormal J H
  have hcov := isCoveringOver_joinProdLift (localPretopology.{v, u, max w u v} J)
    (H.toSimplicialObject ⋙ yonedaFormal) m n hLhyp
  have hhls := homLocallySurjective_of_covering' J _ hcov
  refine J.toGrothendieck.superset_covering ?_
    (hhls A (prod.lift (yonedaFormal.map s₁) (yonedaFormal.map s₂)))
  rintro A' g ⟨t, ht⟩
  refine ⟨hFF.preimage t, ?_, ?_⟩
  · refine hFF.map_injective ?_
    rw [Functor.map_comp, hFF.map_preimage, Functor.map_comp]
    have h := congrArg (fun z => z ≫ (prod.fst :
      (H.toSimplicialObject ⋙ yonedaFormal).obj (op ⦋m⦌) ⨯
        (H.toSimplicialObject ⋙ yonedaFormal).obj (op ⦋n⦌) ⟶ _)) ht
    simp only [Category.assoc, prod.lift_fst, Functor.comp_map] at h
    exact h
  · refine hFF.map_injective ?_
    rw [Functor.map_comp, hFF.map_preimage, Functor.map_comp]
    have h := congrArg (fun z => z ≫ (prod.snd :
      (H.toSimplicialObject ⋙ yonedaFormal).obj (op ⦋m⦌) ⨯
        (H.toSimplicialObject ⋙ yonedaFormal).obj (op ⦋n⦌) ⟶ _)) ht
    simp only [Category.assoc, prod.lift_snd, Functor.comp_map] at h
    exact h

/-! ### The same for a hypercovering of an object -/

section Over

omit [HasEqualizers C]

/-- **A covering morphism of semi-representable objects over `X` admits local lifts of
sections.** Let `p : Y ⟶ Z` be a covering morphism of `SR(C, X)` — covering for the largest
pretopology generating `J`, which is what `isCoveringOver_toPretopology` supplies from a covering
morphism for any pretopology generating `J` — and let `s` be a section of `Z` over an object `A`
of `C/X`, that is a morphism out of the one-summand object on `A`. Then the arrows `A' ⟶ A` of
`C/X` along which `s` lifts through `p` form a covering sieve of `A` for the localized topology
`J.over X`.

A section of `Z` over `A` is an index `j` of `Z` together with a morphism `A ⟶ Z.obj j` over `X`;
the components of `p` over `j` cover `Z.obj j`, so pulling that covering sieve back along the
underlying morphism of `A ⟶ Z.obj j` gives the required arrows, and each of them is a morphism
over `X` because the defining square of `Over X` makes it one. -/
theorem homLifts_mem_over (J : GrothendieckTopology C) {X : C}
    {Y Z : FormalCoproduct.{w} (Over X)} (p : Y ⟶ Z)
    (hp : IsCoveringOver J.toPretopology p) {A : Over X}
    (s : (FormalCoproduct.incl (Over X)).obj A ⟶ Z) :
    homLifts (FormalCoproduct.incl (Over X)) p s ∈ (J.over X) A := by
  obtain ⟨j, w, rfl⟩ : ∃ (j : Z.I) (w : A ⟶ Z.obj j),
      s = FormalCoproduct.Hom.fromIncl j w :=
    ⟨_, _, (FormalCoproduct.Hom.fromIncl_asSigma s).symm⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (J.overEquiv_symm_mem_over A _ (J.pullback_stable w.left (hp j)))
  intro A' g hg
  rw [Sieve.overEquiv_symm_iff, Sieve.pullback_apply] at hg
  obtain ⟨W, q, r, hr, hcomm⟩ := hg
  cases hr with
  | mk i =>
    obtain ⟨i, hi⟩ := i
    subst hi
    simp only [eqToHom_refl, Category.comp_id] at hcomm
    have hq : q ≫ (Y.obj i).hom = A'.hom := by
      rw [← Over.w (p.φ i), ← Category.assoc, hcomm, Category.assoc, Over.w w, Over.w g]
    refine ⟨FormalCoproduct.Hom.fromIncl i (Over.homMk q hq), ?_⟩
    refine (FormalCoproduct.inclHomEquiv A' Z).injective ?_
    exact congrArg (Sigma.mk (p.f i)) (Over.OverMorphism.ext hcomm)

/-- A covering morphism of semi-representable objects over `X` for a pretopology is covering for
the largest pretopology generating the same Grothendieck topology: the covering family it gives
over each index generates the sieve asked for there. -/
theorem isCoveringOver_toPretopology (P : Pretopology C) {X : C}
    {U V : FormalCoproduct.{w} (Over X)} {f : U ⟶ V} (hf : IsCoveringOver P f) :
    IsCoveringOver P.toGrothendieck.toPretopology f :=
  fun j ↦ ⟨_, hf j, Sieve.le_generate _⟩

/-- **A pair of simplices of a hypercovering of an object is locally a pair of complementary
faces.** For a hypercovering `K` of `X` in the sense of Stacks 01G5, `m n : ℕ` and a pair
consisting of an `m`-simplex and an `n`-simplex of `K` over an object `A` of `C/X`, the arrows
`A' ⟶ A` of `C/X` along which the pair lifts to a single `(m + n + 1)`-simplex of `K` form a
covering sieve of `A` for the localized topology.

This is Tag 01GN for the inclusion of the two ends of the join `Δ[m] ⋆ Δ[n] = Δ[m + n + 1]`,
which `isCoveringOver_joinProdLift` states for a hypercovering of an object: a lift of the pair
is a lift of the single section `prod.lift s₁ s₂` through the covering morphism
`K_{m + n + 1} ⟶ K_m ⨯ K_n` of the two complementary faces, so `homLifts_mem_over` applies. -/
theorem joinLiftSieve_mem_over (P : Pretopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (hK : IsHypercovering P K)
    (m n : ℕ) {A : Over X}
    (s₁ : (FormalCoproduct.incl (Over X)).obj A ⟶ K.obj (op ⦋m⦌))
    (s₂ : (FormalCoproduct.incl (Over X)).obj A ⟶ K.obj (op ⦋n⦌)) :
    joinLiftSieve K m n s₁ s₂ ∈ (P.toGrothendieck.over X) A := by
  have : Precoverage.IsStableUnderComposition P.toGrothendieck.toPretopology.toPrecoverage :=
    inferInstanceAs (Precoverage.IsStableUnderComposition P.toGrothendieck.toPrecoverage)
  have hQ : IsHypercovering P.toGrothendieck.toPretopology K :=
    ⟨isCoveringOver_toPretopology P hK.1, fun r ↦ isCoveringOver_toPretopology P (hK.2 r)⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (homLifts_mem_over P.toGrothendieck (joinProdLift K m n)
      (isCoveringOver_joinProdLift P.toGrothendieck.toPretopology K m n hQ) (prod.lift s₁ s₂))
  rintro A' g ⟨t, ht⟩
  refine ⟨t, ?_, ?_⟩
  · rw [show K.map (joinFst m n).op = joinProdLift K m n ≫ prod.fst from
      (prod.lift_fst _ _).symm, ← Category.assoc, ht, Category.assoc, prod.lift_fst]
  · rw [show K.map (joinSnd m n).op = joinProdLift K m n ≫ prod.snd from
      (prod.lift_snd _ _).symm, ← Category.assoc, ht, Category.assoc, prod.lift_snd]

end Over

end Stacks.CategoryTheory.Hypercovering

end
