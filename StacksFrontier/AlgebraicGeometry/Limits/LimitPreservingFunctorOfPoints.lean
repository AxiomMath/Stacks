module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.SurjectiveFinitePresentationCriterion

/-!
# Limit preserving functors on schemes over a base

A functor on schemes over a base scheme `S` is *limit preserving* when it turns every cofiltered
inverse limit of affine `S`-schemes into a filtered colimit of sets. For a scheme `X` over `S`
the functor of points `h_X = Mor_S(-, X)` is limit preserving exactly when `X` is locally of
finite presentation over `S`.

## Main definitions

* `AlgebraicGeometry.Scheme.IsLimitPreserving`: a functor on `(Over S)ᵒᵖ` sends cofiltered
  inverse limits of affine `S`-schemes to filtered colimits of sets.
* `AlgebraicGeometry.Scheme.IsLimitPreservingOnAffineTransitions`: the same condition for the
  cofiltered inverse limits of quasi-compact quasi-separated `S`-schemes whose transition
  morphisms are affine.

## Main results

* `AlgebraicGeometry.Scheme.locallyOfFinitePresentation_iff_isLimitPreserving_yoneda`: a scheme
  is locally of finite presentation over `S` if and only if its functor of points is limit
  preserving.
* `AlgebraicGeometry.Scheme.locallyOfFinitePresentation_iff_isLimitPreservingOnAffineTransitions`:
  the same equivalence for inverse systems of quasi-compact quasi-separated schemes with affine
  transition morphisms.
* `AlgebraicGeometry.Scheme.locallyOfFinitePresentation_tfae_directed`: Stacks 01ZC as stated,
  with the inverse systems indexed by directed sets.
* `AlgebraicGeometry.Scheme.exists_comp_eq_of_isLimitPreserving`: a limit preserving functor of
  points factors a morphism out of a cofiltered limit of affine `S`-schemes through a member of
  the inverse system.

## Implementation notes

The colimit condition is Mathlib's `CategoryTheory.Limits.PreservesColimit` for the opposite
diagram, which is the assertion that the canonical map `colim_i F(T_i) → F(lim_i T_i)` is
bijective. The inverse systems tested are the cofiltered ones rather than those indexed by a
directed poset; the two readings agree, because the equivalence below identifies each of them
with local finite presentation.

Index categories are taken at the size of the schemes, `I : Type u` with `Category.{u} I`, which
is the size at which the inverse-limit API for schemes with affine transition morphisms is
stated.

The implication from local finite presentation is Mathlib's
`AlgebraicGeometry.Scheme.preservesColimit_yoneda`, applied after noting that a morphism between
affine schemes is affine and that an affine scheme is quasi-compact and quasi-separated. For the
converse, only the surjectivity half of the colimit condition is needed: a filtered colimit of
sets is the union of the images of its legs, so a morphism out of the limit already factors
through one stage of the system, which is the hypothesis of the criterion
`AlgebraicGeometry.locallyOfFinitePresentation_of_affineLimit_surjective`.

## References

* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 0CM0](https://stacks.math.columbia.edu/tag/0CM0)
* [Stacks Project, Tag 05LX](https://stacks.math.columbia.edu/tag/05LX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Scheme

/-- **Stacks 05LX.** A functor on schemes over `S` is *limit preserving* when for every
cofiltered inverse system `{T_i}` of affine schemes over `S` with limit `T` the canonical map
`colim_i F(T_i) → F(T)` is bijective. -/
@[stacks 05LX "limit preserving functors", sga "3 XI 3.2" "definition of (*)"]
def IsLimitPreserving (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ (I : Type u) [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over S),
    (∀ i, IsAffine (D.obj i).left) → PreservesColimit D.op F

/-- The functor of points of a scheme locally of finite presentation over `S` is limit
preserving. -/
theorem isLimitPreserving_yoneda_of_locallyOfFinitePresentation {S : Scheme.{u}} (X : Over S)
    [LocallyOfFinitePresentation X.hom] : IsLimitPreserving S (yoneda.obj X) := by
  intro I _ _ D hD
  have : ∀ i, IsAffine (D.obj i).left := hD
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left := fun _ => inferInstance
  have : ∀ i : I, CompactSpace (D.obj i).left := fun _ => inferInstance
  have : ∀ i : I, QuasiSeparatedSpace (D.obj i).left := fun _ => inferInstance
  infer_instance

/-- A morphism to `X` out of the limit of a cofiltered inverse system of affine schemes over `S`
factors through some member of the system, as soon as the functor of points of `X` is limit
preserving: a filtered colimit of sets is the union of the images of its legs. -/
theorem exists_comp_eq_of_isLimitPreserving {S : Scheme.{u}} {X : Over S}
    (H : IsLimitPreserving S (yoneda.obj X)) {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Over S) (c : Cone D) (hc : IsLimit c) (hD : ∀ i, IsAffine (D.obj i).left)
    (g : c.pt ⟶ X) : ∃ (i : I) (gᵢ : D.obj i ⟶ X), c.π.app i ≫ gᵢ = g := by
  obtain ⟨hcol⟩ := (H I D hD).preserves hc.op
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcol g
  exact ⟨j.unop, y, hy⟩

/-- **Stacks 01ZC in the terminology of limit preserving functors.** A scheme `X` over `S` is
locally of finite presentation over `S` if and only if its functor of points
`h_X = Mor_S(-, X)` is limit preserving. -/
@[stacks 05LX "locally of finite presentation iff the functor of points is limit preserving",
  sga "3 XI 3.2" "representable case"]
theorem locallyOfFinitePresentation_iff_isLimitPreserving_yoneda {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔ IsLimitPreserving S (yoneda.obj (Over.mk f)) := by
  refine ⟨fun hf => ?_, fun H => locallyOfFinitePresentation_of_affineLimit_surjective f
    fun _ _ _ D c hc hD g => exists_comp_eq_of_isLimitPreserving H D c hc hD g⟩
  have : LocallyOfFinitePresentation (Over.mk f).hom := hf
  exact isLimitPreserving_yoneda_of_locallyOfFinitePresentation (Over.mk f)

add_to_stacks 01ZC "parts (1) and (2), with the inverse systems indexed by cofiltered categories
rather than by directed sets"
  locallyOfFinitePresentation_iff_isLimitPreserving_yoneda

/-- A functor on schemes over `S` *preserves limits along affine transitions* when for every
cofiltered inverse system `{T_i}` of quasi-compact and quasi-separated schemes over `S` whose
transition morphisms are affine, with limit `T`, the canonical map `colim_i F(T_i) → F(T)` is
bijective. -/
def IsLimitPreservingOnAffineTransitions (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ (I : Type u) [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over S),
    (∀ (i j : I) (g : i ⟶ j), IsAffineHom (D.map g).left) →
    (∀ i, CompactSpace (D.obj i).left) →
    (∀ i, QuasiSeparatedSpace (D.obj i).left) →
      PreservesColimit D.op F

/-- A scheme `X` over `S` is locally of finite presentation over `S` if and only if its functor
of points `h_X = Mor_S(-, X)` turns every cofiltered inverse limit of quasi-compact and
quasi-separated `S`-schemes with affine transition morphisms into a filtered colimit.

The same characterization with the inverse systems restricted to affine schemes is
`locallyOfFinitePresentation_iff_isLimitPreserving_yoneda`. -/
@[stacks 01ZC "parts (1) and (3), with the inverse systems indexed by cofiltered categories
rather than by directed sets", ega "IV 8.14.2" "a ⇔ b"]
theorem locallyOfFinitePresentation_iff_isLimitPreservingOnAffineTransitions
    {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFinitePresentation f ↔
      IsLimitPreservingOnAffineTransitions S (yoneda.obj (Over.mk f)) := by
  constructor
  · intro hf I _ _ D hAff hQC hQS
    have : LocallyOfFinitePresentation (Over.mk f).hom := hf
    have : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g).left := fun g => hAff _ _ g
    have : ∀ i : I, CompactSpace (D.obj i).left := hQC
    have : ∀ i : I, QuasiSeparatedSpace (D.obj i).left := hQS
    infer_instance
  · intro H
    refine (locallyOfFinitePresentation_iff_isLimitPreserving_yoneda f).2 ?_
    intro I _ _ D hD
    have : ∀ i, IsAffine (D.obj i).left := hD
    exact H I D (fun _ _ _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)

/-- **Stacks 01ZC.** For a morphism of schemes `f : X ⟶ S` the following are equivalent:

1. `f` is locally of finite presentation;
2. for every directed set `Λ` and every inverse system `(T_i)` of affine `S`-schemes over `Λ`,
   the canonical map `colim_i Mor_S(T_i, X) → Mor_S(lim_i T_i, X)` is bijective;
3. for every directed set `Λ` and every inverse system `(T_i)` of `S`-schemes over `Λ` whose
   transition morphisms are affine and whose members are quasi-compact and quasi-separated, the
   canonical map `colim_i Mor_S(T_i, X) → Mor_S(lim_i T_i, X)` is bijective.

A directed set is a nonempty preordered type in which any two elements have an upper bound, as in
the source, taken in the universe of the schemes; an inverse system over it is a functor out of
`Λᵒᵖ`. Bijectivity of the canonical map is `PreservesColimit` of the functor of points
`Mor_S(-, X)` for the opposite diagram.

The cofiltered readings of conditions (2) and (3) are
`locallyOfFinitePresentation_iff_isLimitPreserving_yoneda` and
`locallyOfFinitePresentation_iff_isLimitPreservingOnAffineTransitions`; condition (1) implies
the directed forms by specializing them along `Λᵒᵖ`, and the directed form of condition (2)
implies condition (1) by the directed criterion
`AlgebraicGeometry.locallyOfFinitePresentation_of_directedAffineLimit_surjective`. -/
@[stacks 01ZC, ega "IV 17.3.2" "more general", sga "3 XI 3.2" "partial"]
theorem locallyOfFinitePresentation_tfae_directed {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE
      [ LocallyOfFinitePresentation f,
        ∀ (Λ : Type u) [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ] (D : Λᵒᵖ ⥤ Over S),
          (∀ i, IsAffine (D.obj i).left) → PreservesColimit D.op (yoneda.obj (Over.mk f)),
        ∀ (Λ : Type u) [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ] (D : Λᵒᵖ ⥤ Over S),
          (∀ (i j : Λᵒᵖ) (g : i ⟶ j), IsAffineHom (D.map g).left) →
          (∀ i, CompactSpace (D.obj i).left) →
          (∀ i, QuasiSeparatedSpace (D.obj i).left) →
            PreservesColimit D.op (yoneda.obj (Over.mk f)) ] := by
  tfae_have 1 → 3 := fun hf Λ _ _ _ D hAff hQC hQS =>
    (locallyOfFinitePresentation_iff_isLimitPreservingOnAffineTransitions f).1 hf Λᵒᵖ D
      hAff hQC hQS
  tfae_have 3 → 2 := by
    intro H Λ _ _ _ D hD
    have : ∀ i, IsAffine (D.obj i).left := hD
    exact H Λ D (fun _ _ _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
  tfae_have 2 → 1 := fun H =>
    locallyOfFinitePresentation_of_directedAffineLimit_surjective f fun Λ _ _ _ D c hc hD g => by
      obtain ⟨hcol⟩ := (H Λ D hD).preserves hc.op
      obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcol g
      exact ⟨j.unop, y, hy⟩
  tfae_finish

end AlgebraicGeometry.Scheme

end
