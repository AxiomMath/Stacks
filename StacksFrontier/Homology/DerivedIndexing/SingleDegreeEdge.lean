module

public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# The degreewise comparison of a composite, read on complexes

Let `P : 𝒜 ⥤ ℬ` and `Q : ℬ ⥤ 𝒞` be additive functors between abelian categories, with `𝒜` and
`ℬ` having enough injectives and `P` preserving injective objects. The degreewise comparison

`R ⁱQ(Pℱ) ⟶ R ⁱ(Q ∘ P)(ℱ)`

of `Stacks.DerivedIndexing.rightDerivedPlusEdge` is built from the canonical map
`(Pℱ)[0] ⟶ RP(ℱ[0])` of `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle`, which lives in the
bounded-below homotopy category. This file rewrites it as the degree-`i` homology of a *pullback
map on derived global sections of complexes*: the map obtained by applying `RQ` to the canonical
map `(Pℱ)[-q] ⟶ RP(ℱ[-q])` of `Stacks.DerivedIndexing.singleDerivedUnit` and transporting along
the composition isomorphism `R(Q ∘ P) ≅ RQ ∘ RP` of [Stacks, Tag 015M].

For `P = f_*` and `Q = Γ(Y, -)` the right-hand side at `q = 1` is the pullback on the degree-two
hypercohomology of the sheaf of units placed in degree one, which is where the de Rham first
Chern class of [Stacks, Tag 0FLE] is taken; the left-hand side at `q = 0` is the pullback of
first cohomology classes that [Stacks, Tag 09NU] is natural for. So this is the step of
[Stacks, Tag 0FMD] that puts the two pullbacks in the same language, before the degree shift.

## Main definitions

* `Stacks.DerivedIndexing.singleDerivedPullback`: the pullback
  `RQ((Pℱ)[-q]) ⟶ R(Q ∘ P)(ℱ[-q])` attached to a complex concentrated in degree `q`.

## Main results

* `Stacks.DerivedIndexing.rightDerivedPlusEdge_app_eq`: **the degreewise comparison of a
  composite is the degree-`i` homology of the degree-zero pullback.**

## Implementation notes

The variables are declared exactly as in the `EdgeIdentification` section of
`StacksFrontier.Homology.DerivedIndexing.Composite`, with a single universe for the derived
categories of `𝒜` and `ℬ`: `Stacks.DerivedIndexing.rightDerivedPlusEdge_app` is stated there
with that constraint, so a declaration giving the two separate universes cannot apply it.

## References

* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w w'' v v' v'' u u' u''

namespace Stacks.DerivedIndexing

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D] [HasDerivedCategory.{w''} E]
  [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ D) (Q : D ⥤ E) [P.Additive] [Q.Additive] [P.PreservesInjectiveObjects]

/-- **The pullback `RQ((Pℱ)[-q]) ⟶ R(Q ∘ P)(ℱ[-q])` attached to a complex concentrated in one
degree**: `RQ` applied to the canonical map `(Pℱ)[-q] ⟶ RP(ℱ[-q])` of
`Stacks.DerivedIndexing.singleDerivedUnit`, followed by the inverse of the composition
isomorphism `R(Q ∘ P) ≅ RQ ∘ RP` of [Stacks, Tag 015M].

For `P = f_*` and `Q = Γ(Y, -)` this is the pullback on derived global sections
`AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback` along the comparison of complexes
`(f_*ℱ)[-q] ⟶ f_*(ℱ[-q])`. -/
def singleDerivedPullback (q : ℤ) (X : C) :
    Q.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D q).obj (P.obj X)) ⟶
      (P ⋙ Q).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor C q).obj X) :=
  Q.rightDerivedFunctorPlus.map (singleDerivedUnit P q X) ≫
    (rightDerivedPlusCompIso P Q).inv.app ((DerivedCategory.Plus.singleFunctor C q).obj X)

/-- **The degreewise comparison of a composite of right derived functors is the degree-`i`
homology of the degree-zero pullback attached to the single complex.** This is the identity that
carries `Stacks.DerivedIndexing.rightDerivedPlusEdge` — hence, through
`Stacks.DerivedIndexing.map_comp_edge_comp_rightDerivedIso`, [Stacks, Tag 09NU]'s pullback of
first cohomology classes — to a pullback map on derived global sections of complexes. It is
`Stacks.DerivedIndexing.singleDerivedUnit_zero` together with the functoriality of the homology
functor. -/
theorem rightDerivedPlusEdge_app_eq (i : ℤ) (X : C) :
    (rightDerivedPlusEdge P Q i).app X =
      (DerivedCategory.Plus.homologyFunctor E i).map (singleDerivedPullback P Q 0 X) := by
  refine (rightDerivedPlusEdge_app P Q i X).trans ?_
  refine Eq.trans ?_ (congrArg (DerivedCategory.Plus.homologyFunctor E i).map
    (congrArg (fun z => Q.rightDerivedFunctorPlus.map z ≫
      (rightDerivedPlusCompIso P Q).inv.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X))
      (singleDerivedUnit_zero P X))).symm
  exact ((DerivedCategory.Plus.homologyFunctor E i).map_comp _ _).symm

end Stacks.DerivedIndexing

end
