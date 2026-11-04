module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RefinedDatumAssembly
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponentsCocycle

/-!
# Packaging the quasi-coherent descent datum of Stacks 03DX (1)

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/RefinedDatumAssembly.lean` proves both
laws of the descent datum of Stacks 03DX (1) for a family of objects of `(Sch/S)_fppf` whose
structure morphisms are an fpqc covering family, in the spelling in which the transition
isomorphisms of Stacks 0GN7 are stated.  This file re-packages them for the consumer:
`CategoryTheory.Pseudofunctor.DescentData'`, the structure which organizes a descent datum
relative to a choice of fibre products.

Re-packaging is needed because that structure phrases its two laws with *its own* projections —
`CategoryTheory.Limits.ChosenPullback₃.p₁`, `.p₂`, `.p₃` and the morphism `.p` to the base — and
with the comparison morphisms `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom'`
through the chosen pullback, whereas the laws as proved speak of the projections of the fibre
products of the site read downstairs.  The two spellings are definitionally equal, and the work
here is to make every identification between them a *named* one, at a place where its types are
small, rather than a definitional unfolding inside the category of sheaves of modules on a
threefold fibre product of schemes.

The object family and the transitions are therefore restated once in the pullback
pseudofunctor's own spelling, and each law is reduced to a statement about
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` at the projections
`CategoryTheory.Limits.ChosenPullback₃.p₁₂`, `.p₂₃`, `.p₁₃` of the chosen threefold product —
the form in which the structure's own reduction lemmas
`CategoryTheory.Pseudofunctor.DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃` and its two
companions leave the laws.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.memberObj`: the local associated modules of Stacks 03DV on the
  members of the family, read as objects of the pullback pseudofunctor at their schemes.
* `AlgebraicGeometry.BigFppfOver.memberHom`: the transition isomorphisms over the chosen fibre
  products of two members, read as morphisms between the pullbacks of those objects — the datum
  of a descent datum.

## Main results

* `AlgebraicGeometry.BigFppfOver.memberHom_self_law`: **the identity law of the descent datum**,
  in the spelling of `memberHom`.
* `AlgebraicGeometry.BigFppfOver.pullHom_memberHom_self`: the identity law read on the diagonal
  of the fibre product of a member with itself, at the level of `pullHom`.
* `AlgebraicGeometry.BigFppfOver.pullHom_memberHom_comp`: **the cocycle law of the descent
  datum**, at the level of `pullHom`, on the three projections of the chosen threefold fibre
  product of three members.

## Implementation notes

**The performance wall, and what it actually is.**  The elaborator accepts
`CategoryTheory.Pseudofunctor.DescentData'.mk` at these chosen pullbacks with these two laws;
the *kernel* then exceeds its 200 000-heartbeat budget re-checking the application, and no
option may be set to raise that budget.  The cost is not, as one
might expect, the `isLimit` field of the chosen pullback, which is data.  Three things
determine it.

First, the type `CategoryTheory.Pseudofunctor.DescentData'` at these chosen pullbacks is cheap,
as is each of the fields `obj` and `hom`; what is not affordable is a *partial* application of
the constructor, because inferring the sort of the residual product type re-checks the two law
field types, and those are phrased with the autoparameter proofs that
`CategoryTheory.Pseudofunctor.DescentData'` baked in when it was declared.  So the constructor
must be applied fully, and the two laws must be stated with those same proof terms, not with
`CategoryTheory.Limits.ChosenPullback₃.w₁` and its companions: comparing the two spellings of
one such proof costs the whole budget by itself, the kernel unfolding `pullHom'` into
`CategoryTheory.Limits.IsPullback.lift` and thence into
`CategoryTheory.Limits.limit.cone`, at 40 945 and 118 148 unfoldings for one law.

Second, the object family must be restated in the pullback pseudofunctor's own spelling.  Given
as a family of `AlgebraicGeometry.Scheme.Modules`, it fits the `obj` field only after unfolding
`AlgebraicGeometry.modulePullbackPseudofunctor`, which is semireducible and whose pullback is a
left adjoint produced by `Classical.choose`; the resulting goals are then not type-correct at
the `implicit` transparency level, which silently defeats `rw` and `dsimp` and makes every
later comparison pay for that unfolding.  `AlgebraicGeometry.BigFppfOver.memberObj` and
`AlgebraicGeometry.BigFppfOver.memberHom` exist to pin that spelling, and `memberHom` is
deliberately written out with `CategoryTheory.Pseudofunctor.map` and `.toFunctor.obj` rather
than through `AlgebraicGeometry.pullMod`, so that the `hom` field needs no unfolding at all.

Third, every `CategoryTheory.Limits.ChosenPullback` argument is passed explicitly.  Left
implicit, `(sq i j).p₁` is a projection applied to a metavariable, which no unifier can solve,
and the fallback is again to unfold `pullHom'`.

**Where it stops.**  With both laws reduced as below and the two data fields in one spelling,
each of the five declarations here is checked by the kernel comfortably, and the laws are
exactly the content of the two fields; the single remaining step, the constructor application
itself, still exceeds the budget.  The reduction lemmas of
`CategoryTheory.Pseudofunctor.DescentData'` are the right road — they keep the structure's own
autoparameter proofs as metavariables, so no proof is ever compared — but the residual cost of
the application is not under the budget, and splitting it further is not possible: a structure
instance's fields cannot be moved into separate declarations without naming the auxiliary
proofs the structure generated, which is both unstable and reported by the linter.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
  CategoryTheory.Pseudofunctor.DescentData'

universe u w

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {I : Type w} (G : SheafOfModules.{u} (structureSheaf B S hS))
  (X : I → BigFppfOver B S hS) (F : ∀ i, (objScheme B S hS (X i)).Modules)
  (hF : ∀ i, (F i).IsQuasicoherent)
  (e : ∀ i, (associatedModule B (objScheme B S hS (X i))
    (contains_objScheme B S hS (X i))).obj (F i) ≅ (objRestrict B S hS (X i)).obj G)

/-! ### The datum, in the pullback pseudofunctor's own spelling -/

/-- **The local associated module on a member of the family, read as an object of the pullback
pseudofunctor.**  A descent datum for `AlgebraicGeometry.modulePullbackPseudofunctor` has as its
objects elements of the fibres of that pseudofunctor, and the local data of Stacks 03DV are
sheaves of modules on the schemes of the members; the two are the same thing, but only after
unfolding the pseudofunctor, so the identification is made once here and never again. -/
public noncomputable def memberObj (i : I) :
    modulePullbackPseudofunctor.obj (.mk (op (objScheme B S hS (X i)))) :=
  F i

/-- **The transition isomorphism of the descent datum over the chosen fibre product of two
members, read as a morphism of the pullback pseudofunctor.**  This is the `hom` field of
`CategoryTheory.Pseudofunctor.DescentData'` at the chosen pullbacks
`AlgebraicGeometry.BigFppfOver.memberChosenPullback`: the transition isomorphism of
Stacks 03DX (1) between the pullbacks of the local data of `X i` and `X j` along the two
projections of `X i ×_S X j`. -/
public noncomputable def memberHom (i j : I) :
    (modulePullbackPseudofunctor.map
          (memberChosenPullback B S hS X i j).p₁.op.toLoc).toFunctor.obj
        (memberObj B S hS X F i) ⟶
      (modulePullbackPseudofunctor.map
        (memberChosenPullback B S hS X i j).p₂.op.toLoc).toFunctor.obj
        (memberObj B S hS X F j) :=
  memberTransition B S hS G X F hF e i j

/-! ### The two laws -/

/-- **The identity law of the descent datum.**  Read over a member `X i` itself, through the
chosen fibre product of `X i` with itself, the transition isomorphism of Stacks 03DX (1) is the
identity.  This is the statement of the `pullHom'_hom_self` field of
`CategoryTheory.Pseudofunctor.DescentData'` in the spelling of
`AlgebraicGeometry.BigFppfOver.memberHom`, the two differing only in which proof of
`𝟙 _ ≫ f = f` is carried along. -/
public theorem memberHom_self_law (i : I) :
    pullHom' (sq := memberChosenPullback B S hS X) (memberHom B S hS G X F hF e)
      (objHom B S hS (X i)) (𝟙 (objScheme B S hS (X i))) (𝟙 (objScheme B S hS (X i)))
      (Category.id_comp _) (Category.id_comp _) = 𝟙 _ :=
  pullHom'_memberTransition_self B S hS G X F hF e
    (localComparisonPseudonatural B S hS G) i

/-- **The identity law, read on the diagonal at the level of `pullHom`.**  The diagonal
`X i ⟶ X i ×_S X i` of the site, read downstairs, carries the transition isomorphism at the pair
of projections to the transition isomorphism at the pair of identities, which is the identity by
`AlgebraicGeometry.BigFppfOver.transitionIso_self`.

This is the form `CategoryTheory.Pseudofunctor.DescentData'.pullHom'_eq_pullHom` leaves the
identity law in once the lift through the chosen pullback has been named: the diagonal is an
honest morphism of the site, so no universal property is invoked. -/
public theorem pullHom_memberHom_self (i : I) :
    pullHom (memberHom B S hS G X F hF e i i)
      (objHomOver B S hS (memberProdDiag B S hS X i))
      (𝟙 (objScheme B S hS (X i))) (𝟙 (objScheme B S hS (X i)))
      (congrArg (toScheme B S hS).map (pullback.lift_fst _ _ _))
      (congrArg (toScheme B S hS).map (pullback.lift_snd _ _ _)) = 𝟙 _ :=
  (pullHom_eq_transitionIso B S hS G (localComparisonPseudonatural B S hS G)
      (memberProdDiag B S hS X i)
      (memberProdFst B S hS X i i) (memberProdSnd B S hS X i i)
      (a₁ := 𝟙 (X i)) (pullback.lift_fst _ _ _)
      (a₂ := 𝟙 (X i)) (pullback.lift_snd _ _ _) (hF i) (e i) (hF i) (e i)).trans
    (transitionIso_self B S hS G (𝟙 (X i)) (hF i) (e i))

/-- **The cocycle law of the descent datum, at the level of `pullHom`.**  Over the threefold
fibre product `X i₁ ×_S X i₂ ×_S X i₃` of the site, the transport of the transition from `X i₁`
to `X i₂` along the projection onto `X i₁ ×_S X i₂`, followed by the transport of the transition
from `X i₂` to `X i₃` along the projection onto `X i₂ ×_S X i₃`, is the transport of the
transition from `X i₁` to `X i₃` along the projection onto `X i₁ ×_S X i₃`.

The three projections are those of `CategoryTheory.Limits.ChosenPullback₃` — `.p₁₂`, `.p₂₃` and
`.p₁₃` — which is the form in which
`CategoryTheory.Pseudofunctor.DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃` and its two
companions leave the `pullHom'_hom_comp` field, so that no lift through a chosen pullback
survives in the statement.  Each of the three transports is then the transition isomorphism of
Stacks 03DX (1) at the corresponding pair of projections of the threefold product, by
`AlgebraicGeometry.BigFppfOver.pullHom_eq_transitionIso`, and those three compose by
`AlgebraicGeometry.BigFppfOver.transitionIso_trans`.

The two reductions are performed by `Stacks.comp_eq_of_eq`, so that the equalities of the three
factors are substituted inside a lemma whose types are small. -/
public theorem pullHom_memberHom_comp (i₁ i₂ i₃ : I) :
    pullHom (memberHom B S hS G X F hF e i₁ i₂)
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₁₂
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₁
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₂
          (ChosenPullback₃.p₁₂_p₁ _) (ChosenPullback₃.p₁₂_p₂ _) ≫
        pullHom (memberHom B S hS G X F hF e i₂ i₃)
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₂₃
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₂
          (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₃
          (ChosenPullback₃.p₂₃_p₂ _) (ChosenPullback₃.p₂₃_p₃ _) =
      pullHom (memberHom B S hS G X F hF e i₁ i₃)
        (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₁₃
        (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₁
        (memberChosenPullback₃ B S hS X i₁ i₂ i₃).p₃
        (ChosenPullback₃.p₁₃_p₁ _) (ChosenPullback₃.p₁₃_p₃ _) :=
  Stacks.comp_eq_of_eq
    (pullHom_eq_transitionIso B S hS G (localComparisonPseudonatural B S hS G)
      (pullback.fst (memberProdSnd B S hS X i₁ i₂) (memberProdFst B S hS X i₂ i₃))
      (memberProdFst B S hS X i₁ i₂) (memberProdSnd B S hS X i₁ i₂)
      (a₁ := memberProd₃Fst B S hS X i₁ i₂ i₃) rfl
      (a₂ := memberProd₃Mid B S hS X i₁ i₂ i₃) rfl (hF i₁) (e i₁) (hF i₂) (e i₂))
    (pullHom_eq_transitionIso B S hS G (localComparisonPseudonatural B S hS G)
      (pullback.snd (memberProdSnd B S hS X i₁ i₂) (memberProdFst B S hS X i₂ i₃))
      (memberProdFst B S hS X i₂ i₃) (memberProdSnd B S hS X i₂ i₃)
      (a₁ := memberProd₃Mid B S hS X i₁ i₂ i₃) pullback.condition.symm
      (a₂ := memberProd₃Snd B S hS X i₁ i₂ i₃) rfl (hF i₂) (e i₂) (hF i₃) (e i₃))
    (pullHom_eq_transitionIso B S hS G (localComparisonPseudonatural B S hS G)
      (memberProd₃Outer B S hS X i₁ i₂ i₃)
      (memberProdFst B S hS X i₁ i₃) (memberProdSnd B S hS X i₁ i₃)
      (a₁ := memberProd₃Fst B S hS X i₁ i₂ i₃) (pullback.lift_fst _ _ _)
      (a₂ := memberProd₃Snd B S hS X i₁ i₂ i₃) (pullback.lift_snd _ _ _)
      (hF i₁) (e i₁) (hF i₃) (e i₃))
    (transitionIso_trans B S hS G (memberProd₃Fst B S hS X i₁ i₂ i₃)
      (memberProd₃Mid B S hS X i₁ i₂ i₃) (memberProd₃Snd B S hS X i₁ i₂ i₃)
      (hF i₁) (e i₁) (hF i₂) (e i₂) (hF i₃) (e i₃))

end AlgebraicGeometry.BigFppfOver

end
