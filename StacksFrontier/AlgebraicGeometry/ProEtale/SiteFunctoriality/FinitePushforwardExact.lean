module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.SmallWeaklyContractible
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleFinite
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ExactPushforward

/-!
# Exactness of direct image along a finite morphism

For a finite morphism of schemes which is locally of finite presentation, direct image of
abelian sheaves on the small pro-étale sites is exact.

Exactness is tested on the affine objects of the small pro-étale site of the target whose rings
of global sections are w-contractible, which cover every object. Base change of such an object
along the morphism is again finite and locally of finite presentation over it, hence affine with
a ring of global sections that is a finite, finitely presented algebra over a w-contractible
ring, and so again w-contractible. Over a w-contractible object a locally surjective morphism of
sheaves is surjective on sections, and direct image evaluates on an object of the source site at
its base change.

## Main results

* `AlgebraicGeometry.ProEtale.SmallProetale.isWContractibleObject_baseChange`: base change of an
  affine object with w-contractible global sections along a finite, locally finitely presented
  morphism is again one.
* `AlgebraicGeometry.ProEtale.exact_smallProetalePushforward`: direct image of abelian sheaves is
  exact.

## Implementation notes

Abelian sheaves are taken in `AddCommGrpCat.{u + 1}`: the small pro-étale site of a scheme in a
chosen big pro-étale site has its objects one universe above its morphisms, and sheafification of
abelian presheaves on it needs colimits of that larger size.

## References

* [Stacks Project, Tag 09A8](https://stacks.math.columbia.edu/tag/09A8)
* [Stacks Project, Tag 0983](https://stacks.math.columbia.edu/tag/0983)
* [Stacks Project, Tag 0986](https://stacks.math.columbia.edu/tag/0986)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) {Z X : B.Scheme} (f : Z ⟶ X)

/-- **Stacks 0986 on the small pro-étale site.** Base change along a finite morphism which is
locally of finite presentation carries an affine object with w-contractible ring of global
sections to another: the base change is finite and locally of finite presentation over the
object, so its ring of global sections is a finite, finitely presented algebra over a
w-contractible ring. -/
theorem SmallProetale.isWContractibleObject_baseChange
    [IsFinite (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
    (U : SmallProetale B X.obj X.property)
    (hU : SmallProetale.IsWContractibleObject B X.obj X.property U) :
    SmallProetale.IsWContractibleObject B Z.obj Z.property
      ((smallProetaleBaseChange B Z X f).obj U) := by
  obtain ⟨haff, hwc⟩ := hU
  have haffU : IsAffine (B.inclusion.obj U.obj.left) := haff
  have hpb : IsPullback (B.inclusion.map (pullback.fst U.obj.hom f))
      (B.inclusion.map (pullback.snd U.obj.hom f))
      (B.inclusion.map U.obj.hom) (B.inclusion.map f) :=
    (IsPullback.of_hasPullback U.obj.hom f).map B.inclusion
  have hfin : IsFinite (B.inclusion.map (pullback.fst U.obj.hom f)) :=
    MorphismProperty.of_isPullback hpb.flip inferInstance
  have hfp : LocallyOfFinitePresentation (B.inclusion.map (pullback.fst U.obj.hom f)) :=
    MorphismProperty.of_isPullback hpb.flip inferInstance
  have haff' : IsAffine (B.inclusion.obj (pullback U.obj.hom f)) :=
    isAffine_of_isAffineHom (B.inclusion.map (pullback.fst U.obj.hom f))
  refine ⟨haff', ?_⟩
  show IsWContractible.{u, u} Γ(B.inclusion.obj (pullback U.obj.hom f), ⊤)
  let p := B.inclusion.map (pullback.fst U.obj.hom f)
  exact @isWContractible_of_finite_of_finitePresentation
    Γ(B.inclusion.obj U.obj.left, ⊤) Γ(B.inclusion.obj (pullback U.obj.hom f), ⊤) _ _
    p.appTop.hom.toAlgebra (IsFinite.finite_app p ⊤ (isAffineOpen_top _))
    p.finitePresentation_appTop hwc

/-- **Stacks 09A8.** For a finite morphism of schemes which is locally of finite presentation,
direct image of abelian sheaves along the induced morphism of small pro-étale sites is exact. -/
@[stacks 09A8]
theorem exact_smallProetalePushforward
    [IsFinite (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)] :
    exactFunctor
      (Sheaf (SmallProetale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1})
      (Sheaf (SmallProetale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      ((smallProetaleBaseChange B Z X f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property)) := by
  let _ : (smallProetaleBaseChange B Z X f).IsContinuous
      (SmallProetale.topology B X.obj X.property)
      (SmallProetale.topology B Z.obj Z.property) :=
    (smallProetaleBaseChange_isMorphismOfSites B Z X f).toIsContinuous
  refine Stacks.WeaklyContractible.exact_sheafPushforwardContinuous _ _ _
    (SmallProetale.IsWContractibleObject B X.obj X.property)
    (SmallProetale.hasEnoughObjects_isWContractible B X) ?_
  intro U hU F G φ hφ
  obtain ⟨haff, hwc⟩ := SmallProetale.isWContractibleObject_baseChange B f U hU
  exact SmallProetale.surjective_sections_of_isWContractible B Z.obj Z.property _ hwc F G φ hφ

end AlgebraicGeometry.ProEtale

end
