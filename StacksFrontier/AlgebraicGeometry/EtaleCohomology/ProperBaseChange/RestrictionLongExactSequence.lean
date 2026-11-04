module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction

/-!
# Restriction on étale cohomology is a morphism of long exact sequences

Let `i : Y ⟶ X` be a morphism of schemes and let `0 → F₁ → F₂ → F₃ → 0` be a short exact
sequence of abelian sheaves on the small étale site of `X`. Inverse image along `i` is exact,
so it carries the sequence to a short exact sequence of abelian sheaves on the small étale site
of `Y`, and both sequences have a long exact sequence of étale cohomology. This file shows that
the restriction maps `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` form a morphism
between those two long exact sequences: they commute with the maps induced by `F₁ → F₂ → F₃`
and with the connecting maps.

The first consequence recorded here is a dévissage step: surjectivity of restriction in a fixed
degree passes from the two outer terms of a short exact sequence to the middle one, as soon as
the cohomology of the subsheaf vanishes one degree higher. This is the surjectivity statement of
Stacks Project Tag 0A5C, and unlike the bijectivity statement it needs the vanishing hypothesis:
without it the element of the middle cohomology one wants to hit need not come from the middle
term upstairs at all.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comp_mk₀`: restriction commutes with the
  map on cohomology induced by a morphism of sheaves.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comp_extClass`: restriction commutes with
  the connecting map of a short exact sequence.
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact`: surjectivity
  of restriction in degree `q` passes to the middle term of a short exact sequence when the
  degree-`q + 1` cohomology of the subsheaf vanishes.

## Implementation notes

Both commutation statements are proved from the defining formula
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_apply`, which exhibits restriction as the
action of the exact inverse-image functor on an `Ext` class followed by precomposition with the
constant-sheaf comparison. Precomposition commutes with postcomposition by associativity of the
`Ext` composition, and the action of an exact functor commutes with `Abelian.Ext.mk₀` and with
the extension class of a short exact sequence; these are the three Mathlib lemmas
`Abelian.Ext.mapExactFunctor_comp`, `Abelian.Ext.mapExactFunctor_mk₀` and
`Abelian.Ext.mapExactFunctor_extClass`.

The degree in the surjectivity statement is left free, and the two cohomology degrees appearing
in it are related by an equation `q + 1 = r` rather than by the literal successor, so that the
statement applies without rewriting at the degrees `2` and `3` in which Tag 0A5C uses it.

No `@[stacks]` tag is attached. Tag 0A5C asserts the closure under extensions of all eight
statements of Situation 0A52 at once, and two of them — the finiteness statements 0A56 and
0A57 — are conditional on the sheaf being constructible, so for the middle term of a short
exact sequence they require the sub and the quotient of a constructible abelian sheaf to be
constructible again. That is Proposition 09BH (2), the *strong* Serre property of the
constructible abelian sheaves on a Noetherian scheme, and it is what Tag 0A5C cites; closure
under extensions alone, which is the weak Serre property of Tag 03RZ (2), does not give it.
Neither is available in this library.

## References

* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

section RestrictionNaturality

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- Restriction on étale cohomology commutes with composing with an `Ext` class, the class
downstairs being its image under the inverse image functor. -/
private theorem etaleCohomologyRestrictionMap_comp_mapExactFunctor
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (q m r : ℕ) (hqr : q + m = r)
    (x : Sheaf.H.{w} F q) (β : Ext F G m) :
    etaleCohomologyRestrictionMap.{u, v, w} i G r (x.comp β hqr) =
      (etaleCohomologyRestrictionMap.{u, v, w} i F q x).comp
        (β.mapExactFunctor (etaleAbelianInverseImage.{u, v} i)) hqr := by
  rw [etaleCohomologyRestrictionMap_apply.{u, v, w},
    etaleCohomologyRestrictionMap_apply.{u, v, w}, Ext.mapExactFunctor_comp,
    ← Ext.comp_assoc _ _ _ (zero_add q) hqr (by omega)]

/-- Restriction on étale cohomology is natural in the sheaf: restricting the image of a
cohomology class under a morphism of sheaves gives the image of its restriction under the
inverse image of that morphism. -/
theorem etaleCohomologyRestrictionMap_comp_mk₀
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (φ : F ⟶ G) (q : ℕ)
    (x : Sheaf.H.{w} F q) :
    etaleCohomologyRestrictionMap.{u, v, w} i G q (x.comp (Ext.mk₀ φ) (add_zero q)) =
      (etaleCohomologyRestrictionMap.{u, v, w} i F q x).comp
        (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map φ)) (add_zero q) := by
  rw [etaleCohomologyRestrictionMap_comp_mapExactFunctor.{u, v, w} i q 0 q (add_zero q),
    Ext.mapExactFunctor_mk₀]

/-- Restriction on étale cohomology commutes with the connecting map of a short exact sequence
of abelian étale sheaves, the connecting map downstairs being that of the inverse-image
sequence. -/
theorem etaleCohomologyRestrictionMap_comp_extClass
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (q r : ℕ) (hqr : q + 1 = r) (x : Sheaf.H.{w} S.X₃ q) :
    etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ r (x.comp hS.extClass hqr) =
      (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q x).comp
        (hS.map_of_exact (etaleAbelianInverseImage.{u, v} i)).extClass hqr := by
  rw [etaleCohomologyRestrictionMap_comp_mapExactFunctor.{u, v, w} i q 1 r hqr,
    Ext.mapExactFunctor_extClass]

/-- **Dévissage for the restriction map: closure under extensions, surjectivity only.** Let
`0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of abelian sheaves on the small étale site of
`X` whose subsheaf has vanishing cohomology in degree `r = q + 1`. If restriction along
`i : Y ⟶ X` is surjective in degree `q` for `F₁` and for `F₃`, then it is surjective in degree
`q` for `F₂`.

This is the surjectivity statement of Stacks Project Tag 0A5C, used there with `q = 2` and
`r = 3`. It holds for an arbitrary morphism of schemes; the properness, dimension and torsion
hypotheses of Situation 0A52 play no role in this step. -/
theorem surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (q r : ℕ) (hqr : q + 1 = r)
    (hvanishing : Subsingleton (Sheaf.H.{w} S.X₁ r))
    (h₁ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ q))
    (h₃ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q) := by
  have hS' := hS.map_of_exact (etaleAbelianInverseImage.{u, v} i)
  intro y
  obtain ⟨x₃, hx₃⟩ := h₃ (y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.g))
    (add_zero q))
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS x₃ hqr (hvanishing.elim _ _)
  have hz : (Ext.postcomp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.g)) _
      (add_zero q)) (y - etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q x₂) = 0 := by
    rw [map_sub, sub_eq_zero]
    change Ext.comp _ _ (add_zero q) = Ext.comp _ _ (add_zero q)
    rw [← etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.g q x₂, hx₂, hx₃]
  obtain ⟨y₁, hy₁⟩ := Ext.covariant_sequence_exact₂ _ hS' _ hz
  have hy₁' : y₁.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.f)) (add_zero q) =
      y - etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q x₂ := hy₁
  obtain ⟨x₁, hx₁⟩ := h₁ y₁
  refine ⟨x₂ + x₁.comp (Ext.mk₀ S.f) (add_zero q), ?_⟩
  rw [map_add, etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.f q x₁, hx₁, hy₁']
  abel

end RestrictionNaturality

end Stacks.EtaleCohomology

end
