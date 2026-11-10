module

public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Composition
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksCore.Tactic.StacksAttribute

/-!
# A filtered colimit of ind-Zariski algebras is ind-Zariski

An `A`-algebra is ind-Zariski when it is a filtered colimit of `A`-algebras whose structure maps
are local isomorphisms (Tag 096N). This file shows that the class of ind-Zariski `A`-algebras is
itself closed under filtered colimits.

## Main results

* `AlgebraicGeometry.ProEtale.localIso_isFinitelyPresentable`: a local isomorphism is a finitely
  presentable object of the category of algebras over its source.
* `AlgebraicGeometry.ProEtale.ind_ind_localIso`: the class of ind-Zariski `A`-algebras is
  idempotent for the ind-construction.
* `AlgebraicGeometry.ProEtale.isIndZariski_of_colimitPresentation`: Tag 096S, a filtered colimit
  of ind-Zariski `A`-algebras is ind-Zariski over `A`.

## Implementation notes

The closure under filtered colimits is Mathlib's general idempotence of the ind-construction,
`CategoryTheory.ObjectProperty.ind_ind`, which holds for any object property implying finite
presentability. The content specific to ind-Zariski algebras is therefore the hypothesis of that
theorem: a local isomorphism `A → B` is a finitely presentable object of the category of
`A`-algebras.

That hypothesis is proved in two steps. First, `A → B` is of finite presentation, which is
`RingHom.IsLocalIso.finitePresentation`. Second, finite presentation of an algebra is finite
presentability of the corresponding object of the category of algebras over the source
(`CommRingCat.isFinitelyPresentable_under`, Lemma 00QO).

The second step is Mathlib's only for a base and an algebra in one universe, because
`commAlgCatEquivUnder` identifies `CommAlgCat.{w} R` with `Under R` only for `R : CommRingCat.{w}`.
For `A : Type u` and the ambient category `CommAlgCat.{max u v} A` of `Algebra.IsIndZariski`, the
base is first moved into the universe `max u v` with `StacksDraft.commAlgChangeScalarsEquivalence`
along `ULift.ringEquiv`; finite presentation of the structure map is unchanged by precomposition
with that ring equivalence, and finite presentability is invariant under an equivalence of
categories.

## References

* [Stacks Project, Tag 096S](https://stacks.math.columbia.edu/tag/096S)
* [Stacks Project, Tag 096N](https://stacks.math.columbia.edu/tag/096N)
* [Stacks Project, Tag 00QO](https://stacks.math.columbia.edu/tag/00QO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.ProEtale

/-- A local isomorphism is a finitely presentable object of the category of algebras over its
source, with the source and the algebra in independent universes: it is of finite presentation,
and finite presentation of an algebra is finite presentability of the corresponding object under
the source ring (Lemma 00QO), checked after moving the source into the universe of the algebra. -/
theorem localIso_isFinitelyPresentable (A : Type u) [CommRing A] :
    CommAlgCat.localIso.{u, max u v} A ≤
      ObjectProperty.isFinitelyPresentable.{max u v} (CommAlgCat.{max u v} A) := by
  intro X hX
  have hA : (algebraMap A (X : Type max u v)).FinitePresentation :=
    RingHom.IsLocalIso.finitePresentation (RingHom.isLocalIso_algebraMap.mpr
      (hX : Algebra.IsLocalIso A (X : Type max u v)))
  let E := StacksDraft.commAlgChangeScalarsEquivalence.{u, max u v, max u v}
    (ULift.ringEquiv : ULift.{v} A ≃+* A).symm
  let E' := E.trans (commAlgCatEquivUnder (CommRingCat.of (ULift.{v} A)))
  have hfp : ((E'.functor.obj X).hom.hom).FinitePresentation :=
    hA.comp (.of_bijective (ULift.ringEquiv : ULift.{v} A ≃+* A).bijective)
  have := Cardinal.fact_isRegular_aleph0.{max u v}
  change IsFinitelyPresentable.{max u v} X
  rw [IsFinitelyPresentable, ← isCardinalPresentable_iff_of_isEquivalence X _ E'.functor]
  exact CommRingCat.isFinitelyPresentable_under (CommRingCat.of (ULift.{v} A)) _ hfp

/-- The ind-Zariski `A`-algebras are closed under filtered colimits: a filtered colimit of
filtered colimits of local isomorphisms is again a filtered colimit of local isomorphisms. This
is the idempotence of the ind-construction for the property of being a local isomorphism, which
applies because a local isomorphism is finitely presentable. -/
theorem ind_ind_localIso (A : Type u) [CommRing A] :
    ((CommAlgCat.localIso.{u, max u v} A).ind.{max u v}).ind.{max u v}
      = (CommAlgCat.localIso.{u, max u v} A).ind.{max u v} :=
  ObjectProperty.ind_ind (localIso_isFinitelyPresentable.{u, v} A)

/-- **Stacks 096S.** A filtered colimit of ind-Zariski `A`-algebras is ind-Zariski over `A`: if
`B` is presented as the colimit of a filtered diagram of `A`-algebras each of which is ind-Zariski
over `A`, then `B` is ind-Zariski over `A`. -/
@[stacks 096S]
theorem isIndZariski_of_colimitPresentation {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{max u v} J]
    (pres : ColimitPresentation J (CommAlgCat.of A (ULift.{u} B)))
    (hpres : ∀ j, Algebra.IsIndZariski A (pres.diag.obj j)) :
    Algebra.IsIndZariski A B := by
  have key : ((CommAlgCat.localIso.{u, max u v} A).ind.{max u v}).ind.{max u v}
      (CommAlgCat.of A (ULift.{u} B)) :=
    ObjectProperty.of_essentiallySmall_index pres fun j =>
      ((CommAlgCat.localIso.{u, max u v} A).ind.{max u v}).prop_of_iso
        (CommAlgCat.isoMk ULift.algEquiv) (hpres j)
  rwa [ind_ind_localIso.{u, v}] at key

end AlgebraicGeometry.ProEtale

end
