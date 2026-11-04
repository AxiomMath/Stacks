module

public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.ArrowDescentDatum
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic

/-!
# The arrow scheme descends along a finite locally free quotient of the object scheme

Let `G = (U, R, s, t, c)` be a groupoid scheme over `S` with `j = (t, s) : R ⟶ U ×_S U`
separated, locally quasi-finite and locally of finite type, and let `q : U ⟶ Ū` be a surjective
finite locally free morphism with a system of quotient arrows, i.e. with the kernel pair
`U ×_Ū U` identified with a subgroupoid of `R`.  Then the descent datum the arrow scheme carries
relative to `q × q : U ×_S U ⟶ Ū ×_S Ū` is effective: there is a scheme `R̄` over `Ū ×_S Ū`
together with a morphism `R ⟶ R̄` exhibiting `R` as `R̄ ×_{Ū ×_S Ū} (U ×_S U)`.

This is the descent step of the fourth conclusion of Tag 04S4, and it is Tag 02W8 at exactly the
hypotheses that tag supplies; the proof of Tag 04S4 takes the same step through
`AlgebraicGeometry.exists_effectiveTransport`, with the datum given on generalized points over
`S`.

## Main results

* `AlgebraicGeometry.surjective_pairCover`, `AlgebraicGeometry.flat_pairCover` and
  `AlgebraicGeometry.quasiCompact_pairCover`: the covering morphism `U ×_S U ⟶ Ū ×_S Ū` of the
  descent inherits surjectivity, flatness and quasi-compactness from `q`.
* `AlgebraicGeometry.GroupoidQuotientArrows.isEffective_arrowsDescentDatum`: **the descent datum
  carried by the arrow scheme is effective.**
* `AlgebraicGeometry.GroupoidQuotientArrows.nonempty_descended_arrows`: the descended scheme
  exists.

## Implementation notes

The covering morphism is the map on underlying schemes of `prod.map q q` formed in `Over S`.
That it inherits a property stable under base change and composition from `q` is
`AlgebraicGeometry.prodMap_left_mem`, obtained by conjugating it with
`CategoryTheory.Over.prodLeftIsoPullback` into the literal `CategoryTheory.Limits.pullback.map`
to which `CategoryTheory.MorphismProperty.pullbackMap` applies.

Flatness and quasi-compactness of `q` are not hypotheses: they come from finite local freeness,
through `Stacks.Morphisms.IsFiniteLocallyFree.flat` and
`Stacks.Morphisms.IsFiniteLocallyFree.isFinite`.

## References

* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The map on underlying schemes of a product of two morphisms in `Over S`, conjugated into
the literal fibre products. -/
lemma prodMap_left_eq_pullbackMap {A B C D : Over S} (p : A ⟶ C) (r : B ⟶ D) :
    (Over.prodLeftIsoPullback A B).inv ≫ (prod.map p r).left ≫
        (Over.prodLeftIsoPullback C D).hom =
      pullback.map A.hom B.hom C.hom D.hom p.left r.left (𝟙 S) (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst, pullback.lift_fst]
    rw [← Over.comp_left, prod.map_fst, Over.comp_left]
    simp
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd, pullback.lift_snd]
    rw [← Over.comp_left, prod.map_snd, Over.comp_left]
    simp

/-- A property of morphisms of schemes stable under base change and composition holds of the
map on underlying schemes of a product of two morphisms of `Over S` as soon as it holds of
both. -/
lemma prodMap_left_mem {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] {A B C D : Over S} (p : A ⟶ C) (r : B ⟶ D)
    (hp : P p.left) (hr : P r.left) : P (prod.map p r).left := by
  have hmap : P (pullback.map A.hom B.hom C.hom D.hom p.left r.left (𝟙 S)
      ((Category.comp_id _).trans (Over.w p).symm)
      ((Category.comp_id _).trans (Over.w r).symm)) :=
    MorphismProperty.pullbackMap hp hr (Over.w p).symm (Over.w r).symm
  have hconj := prodMap_left_eq_pullbackMap p r
  have hiso : (prod.map p r).left =
      (Over.prodLeftIsoPullback A B).hom ≫
        pullback.map A.hom B.hom C.hom D.hom p.left r.left (𝟙 S) (by simp) (by simp) ≫
        (Over.prodLeftIsoPullback C D).inv := by
    rw [← hconj]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [hiso, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact hmap

variable {G : GroupoidScheme S} {Ub : Over S} (q : G.objects ⟶ Ub)

/-- The morphism `U ×_S U ⟶ Ū ×_S Ū` induced by a surjective `q` is surjective. -/
instance surjective_pairCover [Surjective q.left] : Surjective (pairCover q) :=
  have : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    ⟨fun _ _ hf hg ↦ by letI := hf; letI := hg; infer_instance⟩
  prodMap_left_mem (P := @Surjective.{u}) q q inferInstance inferInstance

/-- The morphism `U ×_S U ⟶ Ū ×_S Ū` induced by a finite locally free `q` is flat. -/
instance flat_pairCover [IsFiniteLocallyFree q.left] : Flat (pairCover q) :=
  have : Flat q.left := IsFiniteLocallyFree.flat q.left
  prodMap_left_mem (P := @Flat.{u}) q q inferInstance inferInstance

/-- The morphism `U ×_S U ⟶ Ū ×_S Ū` induced by a finite locally free `q` is quasi-compact. -/
instance quasiCompact_pairCover [IsFiniteLocallyFree q.left] : QuasiCompact (pairCover q) :=
  have : IsFinite q.left := IsFiniteLocallyFree.isFinite q.left
  prodMap_left_mem (P := @QuasiCompact.{u}) q q inferInstance inferInstance

namespace GroupoidQuotientArrows

variable (K : GroupoidQuotientArrows G q)

/-- **The descent datum carried by the arrow scheme is effective.**  This is Tag 02W8 at the
hypotheses of Tag 04S4: the covering `U ×_S U ⟶ Ū ×_S Ū` is surjective, flat and quasi-compact
because `q` is surjective and finite locally free, and the structure morphism of the datum is
`j = (t, s)`, which the tag assumes separated, locally quasi-finite and locally of finite
type. -/
theorem isEffective_arrowsDescentDatum [Surjective q.left] [IsFiniteLocallyFree q.left]
    (hsep : IsSeparated (groupoidPreRelation G).left)
    (hqf : LocallyQuasiFinite (groupoidPreRelation G).left)
    (hft : LocallyOfFiniteType (groupoidPreRelation G).left) :
    DescentData.IsEffective (K.arrowsDescentDatum q) :=
  DescentDatum.isEffective_of_isSeparated_of_locallyQuasiFinite (K.arrowsDescentDatum q)
    hsep hqf hft

/-- **The arrow scheme descends.** -/
theorem nonempty_descended_arrows [Surjective q.left] [IsFiniteLocallyFree q.left]
    (hsep : IsSeparated (groupoidPreRelation G).left)
    (hqf : LocallyQuasiFinite (groupoidPreRelation G).left)
    (hft : LocallyOfFiniteType (groupoidPreRelation G).left) :
    Nonempty (K.arrowsDescentDatum q).Descended :=
  DescentDatum.nonempty_descended_of_isEffective
    (K.isEffective_arrowsDescentDatum q hsep hqf hft)

end GroupoidQuotientArrows

end AlgebraicGeometry

end

end
