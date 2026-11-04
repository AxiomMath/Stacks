module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# The composition transformation of right derived functors commutes with the shift

Let `P : 𝒜 ⥤ ℬ` and `Q : ℬ ⥤ 𝒞` be additive functors between abelian categories, with `𝒜` and
`ℬ` having enough injectives. The canonical transformation

`t : R(Q ∘ P) ⟶ RQ ∘ RP`

of [Stacks, Tag 05T2] (`Stacks.DerivedIndexing.rightDerivedPlusCompTrans`) is produced by the
universal property of right derivation and therefore has no componentwise formula. This file
shows that it nevertheless commutes with the shift by `ℤ`, which is what allows a statement
about it to be moved between cohomological degrees: an abelian sheaf placed in cohomological
degree `q` is one placed in degree `0` shifted by `-q`, so a comparison of derived functors
proved at degree `0` reaches degree `q` only through the shift.

## Main results

* `Stacks.DerivedIndexing.natTransCommShift_rightDerivedPlusCompUnit`: the transformation
  `Q(P(K)) ⟶ RQ(P(K)) ⟶ RQ(RP(K))` out of which `t` is factored commutes with the shift.
* `Stacks.DerivedIndexing.natTransCommShift_rightDerivedPlusCompTrans`: **the canonical
  transformation `t : R(Q ∘ P) ⟶ RQ ∘ RP` commutes with the shift by `ℤ`.**

## Implementation notes

`Stacks.DerivedIndexing.rightDerivedPlusCompUnit` is a composite of three transformations, each
shift-compatible for a reason of its own: the comparison of the functor induced on bounded below
homotopy categories by `Q ∘ P` with the composite of the induced functors, by
`CategoryTheory.commShift_mapHomotopyCategoryPlusCompIso`; and the units of `RQ` and of `RP`, by
`Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit`. Whiskerings and
composites of shift-compatible transformations are shift-compatible, so that half is instance
search — but only after the composite is rebracketed. The three transformations do not compose
on the nose: their sources and targets are the same functors written with different bracketings,
and while the bracketings are definitionally equal, asking instance search to see that costs
more than the heartbeat budget allows. The proof therefore writes the composite out *with* the
intervening associators, which are themselves shift-compatible, and identifies it with
`rightDerivedPlusCompUnit` by `CategoryTheory.NatTrans.commShift_of_eq`; the resulting equation
has identity components wherever an associator occurs.

For `t` itself there is nothing to compute. The commutation is an equality of two
transformations out of `shiftFunctor D⁺(𝒜) a ⋙ R(Q ∘ P)`, and that functor is *again* a right
derived functor — of `shiftFunctor K⁺(𝒜) a ⋙ (Q ∘ P)` along `Qh`, with unit
`CategoryTheory.Functor.IsRightDerivedFunctor.precomposeShiftNatTrans`, an instance of Mathlib's
`Mathlib/CategoryTheory/Functor/Derived/RightDerivedCommShift.lean`. So
`CategoryTheory.Functor.rightDerived_ext` reduces the equality to an equality after composing
with that unit, and there both sides collapse onto the shift-compatibility of
`rightDerivedPlusCompUnit`: Mathlib's
`CategoryTheory.Functor.IsRightDerivedFunctor.comp_map_commShiftIso_hom_app` turns the unit of
`R(Q ∘ P)` followed by the commutation isomorphism of `R(Q ∘ P)` into the commutation
isomorphism of the underlying functor followed by the shift of the unit, the factorization
`Stacks.DerivedIndexing.rightDerivedPlusCompTrans_fac_app` replaces the unit followed by `t` by
`rightDerivedPlusCompUnit` on both sides, and `CategoryTheory.Functor.commShiftIso_comp_hom_app`
reads the commutation isomorphism of the composite `Qh ⋙ RP ⋙ RQ` as the two factors the right
hand side carries.

That first step is taken through a typed `have` rather than by `rw` or `simp`: the commutation
isomorphism named in the goal is the one of
`Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus`, which is *defined* to be Mathlib's
`CategoryTheory.Functor.IsRightDerivedFunctor.commShift` but is marked `instance_reducible`, so
the rewriting tactics do not see the two as the same instance while elaboration at default
transparency does.

Instance search for `Functor.rightDerivedFunctorPlus` is given the cheap pointwise-derivability
instance at raised priority, as in
`StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective`: without it the
search sets out to prove termwise injectivity of an unknown complex and exhausts its budget.

## References

* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits DerivedCategory

universe w w' w'' v v' v'' u u' u''

namespace Stacks.DerivedIndexing

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [HasDerivedCategory.{w''} E]
  [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive]

/-- **The transformation `Q(P(K)) ⟶ RQ(RP(K))` that pins the canonical map of a composite
commutes with the shift.** It is the composite of the comparison of the functor induced on
bounded below homotopy categories by `Q ∘ P` with the composite of the induced functors, of the
unit of `RQ` and of the unit of `RP`, each of which commutes with the shift; the composite is
rebracketed by associators so that instance search can put the three together. -/
lemma natTransCommShift_rightDerivedPlusCompUnit :
    NatTrans.CommShift (rightDerivedPlusCompUnit P Q) ℤ := by
  refine NatTrans.commShift_of_eq (θ :=
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ Q))).inv
        DerivedCategory.Plus.Qh ≫
      (Functor.associator P.mapHomotopyCategoryPlus Q.mapHomotopyCategoryPlus
        DerivedCategory.Plus.Qh).hom ≫
      Functor.whiskerLeft P.mapHomotopyCategoryPlus Q.rightDerivedFunctorPlusUnit ≫
      (Functor.associator P.mapHomotopyCategoryPlus DerivedCategory.Plus.Qh
        Q.rightDerivedFunctorPlus).inv ≫
      Functor.whiskerRight P.rightDerivedFunctorPlusUnit Q.rightDerivedFunctorPlus ≫
      (Functor.associator DerivedCategory.Plus.Qh P.rightDerivedFunctorPlus
        Q.rightDerivedFunctorPlus).hom) ?_
  refine NatTrans.ext (funext fun K => ?_)
  simp only [NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp, Category.comp_id]
  rfl

attribute [local instance] natTransCommShift_rightDerivedPlusCompUnit

/-- **The canonical transformation `t : R(Q ∘ P) ⟶ RQ ∘ RP` of [Stacks, Tag 05T2] commutes with
the shift by `ℤ`.** For each `a` the equation is an equality of transformations out of
`shiftFunctor D⁺(𝒜) a ⋙ R(Q ∘ P)`, which is itself a right derived functor, so it is enough to
check it after composing with that functor's unit; there both sides reduce to the
shift-compatibility of `Stacks.DerivedIndexing.rightDerivedPlusCompUnit`. -/
lemma natTransCommShift_rightDerivedPlusCompTrans :
    NatTrans.CommShift (rightDerivedPlusCompTrans P Q) ℤ := by
  refine ⟨fun a => ?_⟩
  refine Functor.rightDerived_ext _
    (Functor.IsRightDerivedFunctor.precomposeShiftNatTrans
      (P ⋙ Q).rightDerivedFunctorPlus (P ⋙ Q).rightDerivedFunctorPlusUnit a)
    (HomotopyCategory.Plus.quasiIso C) _ _ _ (NatTrans.ext (funext fun K => ?_))
  have key :
      (P ⋙ Q).rightDerivedFunctorPlusUnit.app
            ((shiftFunctor (HomotopyCategory.Plus C) a).obj K) ≫
          (P ⋙ Q).rightDerivedFunctorPlus.map
            ((Functor.commShiftIso DerivedCategory.Plus.Qh a).hom.app K) ≫
          (Functor.commShiftIso (P ⋙ Q).rightDerivedFunctorPlus a).hom.app
            (DerivedCategory.Plus.Qh.obj K) =
        (Functor.commShiftIso
            ((P ⋙ Q).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) a).hom.app K ≫
          (shiftFunctor (DerivedCategory.Plus E) a).map
            ((P ⋙ Q).rightDerivedFunctorPlusUnit.app K) :=
    Functor.IsRightDerivedFunctor.comp_map_commShiftIso_hom_app _ _
      (HomotopyCategory.Plus.quasiIso C) ℤ a K
  have hnat := (rightDerivedPlusCompTrans P Q).naturality
    ((Functor.commShiftIso DerivedCategory.Plus.Qh a).hom.app K)
  have hβ := NatTrans.shift_app_comm (rightDerivedPlusCompUnit P Q) a K
  have hcomp := Functor.commShiftIso_comp_hom_app DerivedCategory.Plus.Qh
    (P.rightDerivedFunctorPlus ⋙ Q.rightDerivedFunctorPlus) a K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Functor.IsRightDerivedFunctor.precomposeShiftNatTrans_app]
  rw [reassoc_of% key, ← Functor.map_comp, rightDerivedPlusCompTrans_fac_app, hβ, hcomp,
    reassoc_of% hnat, reassoc_of% rightDerivedPlusCompTrans_fac_app]
  rfl

end Stacks.DerivedIndexing

end
