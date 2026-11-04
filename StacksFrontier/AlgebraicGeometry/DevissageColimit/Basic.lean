module

public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.Descending
public import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Descending dévissage against two classes, and the colimit reduction between them

`StacksFrontier/AlgebraicGeometry/HighTwistDevissage/Descending.lean` runs the descending
dévissage induction over a *single* class `P` of objects: every object of `P` must be the quotient
term of a short exact sequence with acyclic middle term and with first term again in `P`. That
shape does not fit the cohomological arguments of Chapter 30, and the reason is sharp rather than
technical. The sequence comes from global generation after an ample twist ([Stacks, Tag 01Q3],
clause (8)), which holds only for modules **of finite type**, while the first term of the sequence
— the kernel of a surjection onto a finite-type module — is quasi-coherent and nothing more. So
the class producing the sequence and the class the induction descends over are different classes,
and the source closes the gap at the level of cohomology, not inside the generation statement:
[Stacks, Tag 01PG] writes an arbitrary quasi-coherent module as the directed colimit of its
finite-type quasi-coherent submodules and Cohomology, Lemma 20.19.1 commutes cohomology with that
colimit.

This file supplies the two pieces that shape needs.

* The **two-class descending dévissage**: the dévissage sequence is required only for the smaller
  class `Q`, the induction descends over the larger class `P`, and a *reduction* hypothesis carries
  degreewise vanishing from `Q` to `P`. That hypothesis is where 01PG and 20.19.1 enter.
* The **reduction from a colimit presentation**: if `Dⁿ(X)` is the colimit of `Dⁿ` along a diagram
  of objects on which `Dⁿ` vanishes, then `Dⁿ(X)` vanishes. This is proved here, not assumed.

## Main results

* `Stacks.DevissageColimit.isZero_of_isColimit`: a colimit of zero objects is a zero object.
* `Stacks.DevissageColimit.isZero_obj_of_colimitPresentation`: **the colimit reduction.** If `X`
  is presented as a colimit of objects satisfying `Q`, if `H` sends that presentation to a colimit,
  and if `H` kills every object of `Q`, then `H` kills `X`.
* `Stacks.DevissageColimit.isZero_obj_of_descending_devissage_of_reduction`: **the two-class
  descending dévissage**, the engine [Stacks, Tag 0EBD] actually needs.

## Implementation notes

**A colimit of zero objects is zero for an arbitrary index category**, with no filteredness, no
connectedness and no nonemptiness: the identity of the colimit agrees with the zero map after
composing with every leg, because each leg has a zero object as source, so the two maps are equal
by `CategoryTheory.Limits.IsColimit.hom_ext` and `CategoryTheory.Limits.IsZero.iff_id_eq_zero`
finishes. The empty case is the statement that an initial object of a category with zero
morphisms is a zero object, and it is covered by the same two lines.

**Filteredness is not a hypothesis of the reduction.** [Stacks, Tag 01PG] produces a *directed*
system and Cohomology, Lemma 20.19.1 needs filteredness to commute cohomology with the colimit,
but neither fact is used below: once the commutation is handed over as the hypothesis that `H`
sends the presentation to a colimit, the vanishing argument is insensitive to the shape of the
index category. Omitting `CategoryTheory.IsFiltered` therefore makes the results strictly more
applicable and loses nothing, since any instance of 01PG plus 20.19.1 supplies the stronger input.

**The presentation is `CategoryTheory.Limits.ColimitPresentation`.** Its `pt` is the presented
object on the nose, so `(H.mapCocone pres.cocone).pt` is `H.obj X` by definition and the
conclusion needs no transport along an isomorphism.

**Why the reduction is a separate hypothesis rather than a `P`-indexed dévissage.** Folding the
reduction into the dévissage hypothesis — demanding the short exact sequence for every object of
`P` — produces a hypothesis with *no instances*: on a nonempty scheme no quasi-coherent module of
infinite type is a quotient of a finite direct sum of invertible modules. That failure is visible
on `Stacks.HighTwistDevissage.isAffine_of_isZero_cohomology_negative_tensorPower`, whose `hgen` had
exactly that shape; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/HighTwistDevissage/AffineFromNegativeTwists.lean` (the reduction
of [Stacks, Tag 0EBD]) and the module documentation of
`StacksFrontier/AlgebraicGeometry/AmpleGlobalGeneration/Basic.lean`.

No tag attribute is attached: this is an engine for the cohomological tags of Chapter 30 and the
statement of none of them. In particular neither 01PG nor Cohomology, Lemma 20.19.1 is proved
here; both remain inputs of the consumers.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 0EBD](https://stacks.math.columbia.edu/tag/0EBD)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public section

universe v v' w w' u u'

namespace Stacks.DevissageColimit

open CategoryTheory CategoryTheory.Limits

section Colimit

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B] [HasZeroMorphisms B]

/-- **A colimit of zero objects is a zero object.** No hypothesis on the index category: each leg
of the cocone has a zero object as source and is therefore the zero map, so the identity of the
colimit and the zero map agree after composing with every leg. -/
theorem isZero_of_isColimit {J : Type w} [Category.{w'} J] {G : J ⥤ B}
    (hG : ∀ j, IsZero (G.obj j)) {c : Cocone G} (hc : IsColimit c) : IsZero c.pt := by
  rw [IsZero.iff_id_eq_zero]
  refine hc.hom_ext fun j => ?_
  rw [Category.comp_id, comp_zero]
  exact (hG j).eq_zero_of_src _

/-- **Vanishing propagates along a colimit presentation.** Let `X` be presented as the colimit of
a diagram whose objects all satisfy `Q`, let the functor `H` send that presentation to a colimit,
and let `H` send every object satisfying `Q` to a zero object. Then `H.obj X` is a zero object.

In the application `H` is `Hᵖ(X, -)`, `Q` is "quasi-coherent of finite type", the presentation is
[Stacks, Tag 01PG] and the commutation hypothesis is Cohomology, Lemma 20.19.1. -/
theorem isZero_obj_of_colimitPresentation (H : A ⥤ B) (Q : A → Prop)
    (hQ : ∀ Y : A, Q Y → IsZero (H.obj Y)) {J : Type w} [Category.{w'} J] {X : A}
    (pres : ColimitPresentation J X) (hdiag : ∀ j, Q (pres.diag.obj j))
    (hH : IsColimit (H.mapCocone pres.cocone)) : IsZero (H.obj X) :=
  isZero_of_isColimit (G := pres.diag ⋙ H) (fun j => hQ _ (hdiag j)) hH

end Colimit

section Devissage

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B]
  [Preadditive B]

/-- **The two-class descending dévissage induction**, with the parameter `k` that drives it
exposed. See
`Stacks.DevissageColimit.isZero_obj_of_descending_devissage_of_reduction` for the statement. -/
theorem isZero_obj_of_descending_devissage_of_reduction_of_lt (D : DeltaFunctor A B)
    (P Q : A → Prop) (e : ℕ)
    (hbound : ∀ p : ℕ, e < p → ∀ X : A, P X → IsZero ((D.functor p).obj X))
    (hred : ∀ p : ℕ, 0 < p → (∀ Y : A, Q Y → IsZero ((D.functor p).obj Y)) →
      ∀ X : A, P X → IsZero ((D.functor p).obj X))
    (step : ∀ Y : A, Q Y → ∃ S : ShortComplex A, S.ShortExact ∧ S.X₃ = Y ∧ P S.X₁ ∧
      ∀ m : ℕ, 0 < m → IsZero ((D.functor m).obj S.X₂)) :
    ∀ k p : ℕ, 0 < p → e < p + k → ∀ X : A, P X → IsZero ((D.functor p).obj X) := by
  intro k
  induction k with
  | zero =>
    intro p _ hlt X hX
    exact hbound p (by omega) X hX
  | succ k ih =>
    intro p hp hlt X hX
    by_cases hep : e < p
    · exact hbound p hep X hX
    · refine hred p hp (fun Y hY => ?_) X hX
      obtain ⟨S, hS, hX₃, hP₁, hacyc⟩ := step Y hY
      subst hX₃
      exact Stacks.HighTwistDevissage.isZero_obj_of_shortExact_of_isZero D hS p (hacyc p hp)
        (ih (p + 1) (by omega) (by omega) S.X₁ hP₁)

/-- **Descending dévissage over two classes.** Let `Q ⊆ P` be classes of objects — in the
application, the quasi-coherent modules of finite type inside all quasi-coherent modules — and
suppose

* `D` vanishes on `P` above the degree `e`;
* in each positive degree, vanishing of `D` on all of `Q` implies vanishing on all of `P` (the
  *reduction*, supplied by [Stacks, Tag 01PG] and Cohomology, Lemma 20.19.1 through
  `Stacks.DevissageColimit.isZero_obj_of_colimitPresentation`); and
* every object of `Q` is the quotient term of a short exact sequence whose middle term is
  `D`-acyclic in positive degrees and whose first term satisfies `P` — only `P`, which is what the
  kernel of a surjection onto a finite-type module actually satisfies.

Then `D` vanishes on `P` in every positive degree. The inclusion `Q ⊆ P` is never used and is not
assumed.

This is the shape of the claim inside the proof of [Stacks, Tag 0EBD]; the single-class form
`Stacks.HighTwistDevissage.isZero_obj_of_descending_devissage` cannot be instantiated there,
because its dévissage hypothesis at a module of infinite type has no instances. -/
theorem isZero_obj_of_descending_devissage_of_reduction (D : DeltaFunctor A B) (P Q : A → Prop)
    (e : ℕ)
    (hbound : ∀ p : ℕ, e < p → ∀ X : A, P X → IsZero ((D.functor p).obj X))
    (hred : ∀ p : ℕ, 0 < p → (∀ Y : A, Q Y → IsZero ((D.functor p).obj Y)) →
      ∀ X : A, P X → IsZero ((D.functor p).obj X))
    (step : ∀ Y : A, Q Y → ∃ S : ShortComplex A, S.ShortExact ∧ S.X₃ = Y ∧ P S.X₁ ∧
      ∀ m : ℕ, 0 < m → IsZero ((D.functor m).obj S.X₂))
    (p : ℕ) (hp : 0 < p) (X : A) (hX : P X) : IsZero ((D.functor p).obj X) :=
  isZero_obj_of_descending_devissage_of_reduction_of_lt D P Q e hbound hred step (e + 1) p hp
    (by omega) X hX

end Devissage

end Stacks.DevissageColimit

end
