module

public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.NoetherianSystem
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Induction

/-!
# Absolute Noetherian approximation, from the single-affine step

**Absolute Noetherian approximation** (Stacks 01ZA) says that a quasi-compact quasi-separated
scheme `S` is the limit of a directed inverse system of schemes of finite type over the
integers with affine transition morphisms. The Stacks proof deduces it from the stronger
relative statement (Stacks 07RN), approximation relative to a quasi-compact open `U ⊆ S`, by
taking `U = ∅`.

`AlgebraicGeometry.Scheme.FiniteTypeApproximation.exists_of_isOneAffineOpenStep` reduces that
relative statement to its single-affine case, the predicate
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`. This file performs the
`U = ∅` specialization, so that absolute Noetherian approximation too rests on that one
predicate and on nothing else.

The output is packaged as an `AlgebraicGeometry.LimitNoetherianSituation`, which is the form
the consumers of 01ZA want: a scheme of finite type over the integers is Noetherian
(`AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminal_from`), and both Chow's lemma
(Stacks 0202, whose proof opens "write `S = lim S_i` as a directed limit of Noetherian
schemes") and the descent results of Stacks 32.26 are stated over such a situation.

That packaging loses information, and the statement below therefore carries the lost field
beside it. `LimitNoetherianSituation`'s only condition on a stage is that it be Noetherian, and
*Noetherian does not imply finite type over the integers* — the spectrum of a field of infinite
transcendence degree over `ℚ` is Noetherian and not of finite type over `ℤ`. Finite type is what
01ZA asserts and what its consumers in the theory of limits spend, so the conclusion below
asserts it too, as a second conjunct ranging over the stages of the situation's system.

## Main results

* `Scheme.FiniteTypeApproximation.exists_limitNoetherianSituation_of_isOneAffineOpenStep`,
  in the `AlgebraicGeometry` namespace: absolute Noetherian approximation, granted the
  single-affine step, with the stages asserted to be of finite type over the integers.

## Implementation notes

The empty open subscheme of `S` is exhibited as the limit of the inverse system constant at
itself over the one-object index preorder `PUnit`: that system is
`AlgebraicGeometry.Scheme.botDiagram` and the limiting cone of identities is
`AlgebraicGeometry.Scheme.isLimitConstConePUnit`, both in
`StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Basic`. Its transition morphisms
are identities, hence affine, and it is of finite type over the terminal scheme by
`AlgebraicGeometry.locallyOfFiniteType_terminal_from_of_isEmpty` and
`AlgebraicGeometry.quasiCompact_terminal_from_of_isEmpty` in
`StacksFrontier.AlgebraicGeometry.Limits.ChowLemma`, an empty scheme being affine with the zero
ring as its ring of global functions. That system is the input the relative statement consumes,
and it is the same input the unconditional
`AlgebraicGeometry.Scheme.exists_isLimit_affine_locallyOfFiniteType` consumes.

The approximating system produced by `FiniteTypeApproximation` is indexed by the *order dual*
`Jᵒᵈ` of its index preorder, whereas `LimitNoetherianSituation` is indexed by the categorical
opposite `Jᵒᵖ`. The two are transported into one another along Mathlib's
`CategoryTheory.orderDualEquivalence`, and the limiting cone is carried across by
`CategoryTheory.Limits.IsLimit.whiskerEquivalence`; whiskering does not move the vertex, so the
resulting situation has `S` itself as its limit scheme, not merely a scheme isomorphic to it.

No `@[stacks 01ZA]` attribute is attached: the result below carries `IsOneAffineOpenStep` as a
hypothesis, whereas the tag asserts the conclusion unconditionally.

## References

* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Scheme.FiniteTypeApproximation

attribute [local instance] indexPreorder indexNonempty indexDirected

/-- **Absolute Noetherian approximation, Stacks 01ZA**, granted the single-affine step
`IsOneAffineOpenStep` of Noetherian approximation relative to a quasi-compact open
(Stacks 07RN).

A quasi-compact quasi-separated scheme `S` is the limit of a directed inverse system of
Noetherian schemes with affine transition morphisms, with `S` itself as the vertex of the
limiting cone. This is the Stacks deduction of 01ZA from 07RN, specializing the relative
statement to the empty open subscheme; the stages are Noetherian because they are quasi-compact
and of finite type over the integers.

`IsOneAffineOpenStep` is the only hypothesis, so proving that one predicate makes absolute
Noetherian approximation unconditional.

The stages are asserted to be of finite type over the integers as well as Noetherian.  That is
the form the source states and it is strictly more than `LimitNoetherianSituation` records:
Noetherian does not imply finite type over `ℤ`, as the spectrum of a field of infinite
transcendence degree over `ℚ` shows.  Consumers that descend a finitely presented object to a
stage need the finite-type hypothesis and cannot recover it from Noetherianity, so it is carried
alongside the situation rather than dropped. -/
theorem exists_limitNoetherianSituation_of_isOneAffineOpenStep
    (hstep : IsOneAffineOpenStep.{u}) (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (D : LimitNoetherianSituation.{u, u} J), D.limitScheme = S ∧
        ∀ i : J, LocallyOfFiniteType (terminal.from (D.system.obj (op i))) := by
  have : IsEmpty ((⊥ : S.Opens) : Scheme.{u}) := inferInstanceAs (IsEmpty (∅ : Set S))
  have : CompactSpace ((⊥ : S.Opens) : Scheme.{u}) := inferInstance
  have hAff : ∀ {i j : (PUnit.{u + 1})ᵒᵈ} (f : i ⟶ j),
      IsAffineHom ((Scheme.botDiagram S).map f) :=
    fun _ ↦ inferInstanceAs (IsAffineHom (𝟙 ((⊥ : S.Opens) : Scheme.{u})))
  have hFT : ∀ i, LocallyOfFiniteType (terminal.from ((Scheme.botDiagram S).obj i)) :=
    fun _ ↦ locallyOfFiniteType_terminal_from_of_isEmpty ((⊥ : S.Opens) : Scheme.{u})
  have hQC : ∀ i, QuasiCompact (terminal.from ((Scheme.botDiagram S).obj i)) :=
    fun _ ↦ quasiCompact_terminal_from_of_isEmpty ((⊥ : S.Opens) : Scheme.{u})
  obtain ⟨Q⟩ := exists_of_isOneAffineOpenStep (Scheme.botDiagram S) hstep S (⊥ : S.Opens)
    (𝟙 _) (Scheme.isLimitConstConePUnit ((⊥ : S.Opens) : Scheme.{u}))
  let e : (Q.indexType)ᵒᵖ ≌ (Q.indexType)ᵒᵈ := (orderDualEquivalence Q.indexType).symm
  have hFT' : ∀ i : Q.indexType,
      LocallyOfFiniteType (terminal.from (Q.ambient.obj (e.functor.obj (op i)))) :=
    fun i ↦ Q.locallyOfFiniteType _
  refine ⟨Q.indexType, inferInstance, inferInstance, inferInstance,
    { system := e.functor ⋙ Q.ambient
      noetherian := fun i ↦ ?_
      transition_affine := fun f ↦ Q.transition_affine (e.functor.map f)
      limitCone := Cone.whisker e.functor (Cone.mk S Q.ambientCone)
      isLimit := Q.ambientCone_isLimit.whiskerEquivalence e }, rfl, hFT'⟩
  have := hFT' i
  have := Q.quasiCompact (e.functor.obj (op i))
  exact isNoetherian_of_locallyOfFiniteType_terminal_from
    (Q.ambient.obj (e.functor.obj (op i)))

end Scheme.FiniteTypeApproximation

end AlgebraicGeometry

end
