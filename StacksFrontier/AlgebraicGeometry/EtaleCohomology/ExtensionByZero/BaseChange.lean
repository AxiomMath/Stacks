module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation

/-!
# Extension by zero commutes with inverse image

Let `f : Y ⟶ X` be an arbitrary morphism of schemes and let `j : U ⟶ X` be étale. Writing
`U' = U ×_X Y` and taking `f' : U' ⟶ U` and `j' : U' ⟶ Y` for the two projections, the square

```
U' --j'--> Y
|          |
f'         f
v          v
U ---j---> X
```

is cartesian with `j'` again étale, and `f^{-1} ∘ j_! ≅ j'_! ∘ (f')^{-1}`. This is Stacks
Project Tag 03S6 for abelian sheaves, and it is the step of Tag 03SC part (7) that identifies
the restriction to `X_{k'}` of a sheaf extended by zero from a dense open with a sheaf extended
by zero from the corresponding dense open of `X_{k'}`.

The argument is formal, and is the argument the source gives. Both sides are left adjoints:
`f^{-1} ∘ j_!` is left adjoint to `j^{-1} ∘ f_*` and `j'_! ∘ (f')^{-1}` is left adjoint to
`(f')_* ∘ (j')^{-1}`, and the two right adjoints agree because each of them is the direct image
along one of the two composite site functors `U.Etale ⥤ Y.Etale`, and those two site functors
are identified by the canonical comparison of the two ways of forming `V ×_X Y` for `V` étale
over `U`: once in one step, and once as `V ×_U (U ×_X Y)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Etale.smallEtaleComposeBaseChangeIso` — the comparison of site
  functors `j_{post} ∘ f^* ≅ (f')^* ∘ j'_{post}` underlying everything else.
* `Stacks.EtaleCohomology.smallEtaleRestrictionPushforwardBaseChangeIso` — the resulting
  identification of `(j')^{-1}` followed by `(f')_*` with `f_*` followed by `j^{-1}`, for
  sheaves valued in an arbitrary category.

## Main results

* `Stacks.EtaleCohomology.extensionByZeroBaseChangeIso` — **Stacks Project Tag 03S6** for
  abelian sheaves: `j'_! ∘ (f')^{-1} ≅ f^{-1} ∘ j_!`, naturally in the sheaf.

## Implementation notes

The source states Tag 03S6 as an equality of functors; it is recorded here as an isomorphism,
which retains naturality in the sheaf. The isomorphism is the mate, under the three adjunctions
involved, of the identification of right adjoints, so it is the unique comparison compatible
with the units and counits rather than an arbitrary isomorphism.

The site square is proved by cancelling the fully faithful forgetful functor
`AlgebraicGeometry.Scheme.Etale.forget` to the category of schemes over the base: after that
cancellation the two sides are the two sides of
`CategoryTheory.overPullbackBaseChangeIso` for the cartesian square above, and both
cancellation steps are definitional equalities, because composition with an étale morphism and
base change along an arbitrary morphism are the restrictions to the small étale site of
`CategoryTheory.Over.map` and `CategoryTheory.Over.pullback`.

This library carries a second, independent model of the small étale site, built on
`AlgebraicGeometry.BigEtaleSite` rather than on Mathlib's `AlgebraicGeometry.Scheme.Etale`, and
Tag 03S6 is already available there as
`AlgebraicGeometry.abelianExtensionByZeroBaseChangeIso`. The two models are not identified in
this library, and the dévissage of Tag 03SC part (7) is carried out on Mathlib's site — that is
where `Stacks.EtaleCohomology.etaleAbelianInverseImage` and
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` live — so the statement is needed in this
model too. The clause on the tag names the model.

## References

* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v u₀ v₀

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
  AlgebraicGeometry.Etale.instIsMultiplicativeScheme

namespace AlgebraicGeometry.Scheme.Etale

variable {U X Y : Scheme.{u}} (j : U ⟶ X) [Etale j] (f : Y ⟶ X)

/-- The two ways of forming `V ×_X Y` for `V` étale over `U` agree: composing with `j : U ⟶ X`
and then base changing along `f : Y ⟶ X` is isomorphic to base changing along the projection
`U ×_X Y ⟶ U` and then composing with the projection `U ×_X Y ⟶ Y`, as functors from the small
étale site of `U` to the small étale site of `Y`.

On an object `V` of the small étale site of `U` the two sides are `V ×_X Y` and
`V ×_U (U ×_X Y)`, and the comparison is the canonical isomorphism of the two cartesian
squares. -/
def smallEtaleComposeBaseChangeIso :
    smallEtaleCompose j ⋙ Stacks.EtaleCohomology.smallEtaleBaseChange f ≅
      Stacks.EtaleCohomology.smallEtaleBaseChange (pullback.fst j f) ⋙
        smallEtaleCompose (pullback.snd j f) := by
  apply Functor.fullyFaithfulCancelRight (Scheme.Etale.forget Y)
  calc (smallEtaleCompose j ⋙ Stacks.EtaleCohomology.smallEtaleBaseChange f) ⋙
        Scheme.Etale.forget Y
      = Scheme.Etale.forget U ⋙
          (CategoryTheory.Over.map j ⋙ CategoryTheory.Over.pullback f) := rfl
    _ ≅ Scheme.Etale.forget U ⋙
          (CategoryTheory.Over.pullback (pullback.fst j f) ⋙
            CategoryTheory.Over.map (pullback.snd j f)) :=
        Functor.isoWhiskerLeft _
          (overPullbackBaseChangeIso (pullback.snd j f) (pullback.fst j f) f j
            (IsPullback.of_hasPullback j f).flip)
    _ = (Stacks.EtaleCohomology.smallEtaleBaseChange (pullback.fst j f) ⋙
          smallEtaleCompose (pullback.snd j f)) ⋙ Scheme.Etale.forget Y := rfl

end AlgebraicGeometry.Scheme.Etale

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.Scheme.Etale

variable {U X Y : Scheme.{u}} (j : U ⟶ X) [Etale j] (f : Y ⟶ X)

/-- Restriction to the small étale site of `U ×_X Y` followed by direct image along the
projection `U ×_X Y ⟶ U` agrees with direct image along `f : Y ⟶ X` followed by restriction to
the small étale site of `U`.

This is the identification of right adjoints from which the base-change isomorphism for
extension by zero is obtained. It holds for sheaves valued in an arbitrary category, because
both sides are the direct image along a composite of continuous site functors and the two
composites are identified by
`AlgebraicGeometry.Scheme.Etale.smallEtaleComposeBaseChangeIso`. -/
def smallEtaleRestrictionPushforwardBaseChangeIso (A : Type u₀) [Category.{v₀} A] :
    (smallEtaleCompose (pullback.snd j f)).sheafPushforwardContinuous A
        (smallEtaleTopology (pullback j f)) (smallEtaleTopology Y) ⋙
      (smallEtaleBaseChange (pullback.fst j f)).sheafPushforwardContinuous A
        (smallEtaleTopology U) (smallEtaleTopology (pullback j f)) ≅
    (smallEtaleBaseChange f).sheafPushforwardContinuous A
        (smallEtaleTopology X) (smallEtaleTopology Y) ⋙
      (smallEtaleCompose j).sheafPushforwardContinuous A
        (smallEtaleTopology U) (smallEtaleTopology X) := by
  have := Functor.isContinuous_comp (smallEtaleCompose j) (smallEtaleBaseChange f)
    (smallEtaleTopology U) (smallEtaleTopology X) (smallEtaleTopology Y)
  exact Functor.sheafPushforwardContinuousComp'
      (smallEtaleComposeBaseChangeIso j f).symm A
      (smallEtaleTopology U) (smallEtaleTopology (pullback j f)) (smallEtaleTopology Y) ≪≫
    (Functor.sheafPushforwardContinuousComp (smallEtaleCompose j) (smallEtaleBaseChange f) A
      (smallEtaleTopology U) (smallEtaleTopology X) (smallEtaleTopology Y)).symm

/-- **Stacks Project, Tag 03S6** for abelian sheaves. Extension by zero of abelian étale
sheaves commutes with inverse image: for an arbitrary morphism `f : Y ⟶ X` and an étale
`j : U ⟶ X`, writing `f' : U ×_X Y ⟶ U` and `j' : U ×_X Y ⟶ Y` for the two projections, one has
`j'_! ∘ (f')^{-1} ≅ f^{-1} ∘ j_!`, naturally in the sheaf.

Both sides are left adjoints, of `(f')_* ∘ (j')^{-1}` and of `j^{-1} ∘ f_*` respectively, and
those two right adjoints agree by
`Stacks.EtaleCohomology.smallEtaleRestrictionPushforwardBaseChangeIso`; the isomorphism is the
mate of that agreement. -/
def extensionByZeroBaseChangeIso :
    etaleAbelianInverseImage.{u, v} (pullback.fst j f) ⋙
        extensionByZero.{u, v} (pullback.snd j f) ≅
      extensionByZero.{u, v} j ⋙ etaleAbelianInverseImage.{u, v} f :=
  Adjunction.leftAdjointCompIso
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtaleBaseChange (pullback.fst j f)) AddCommGrpCat.{max (u + 1) v}
      (smallEtaleTopology U) (smallEtaleTopology (pullback j f)))
    (extensionByZeroAdj.{u, v} (pullback.snd j f))
    ((extensionByZeroAdj.{u, v} j).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange f) AddCommGrpCat.{max (u + 1) v}
        (smallEtaleTopology X) (smallEtaleTopology Y)))
    (smallEtaleRestrictionPushforwardBaseChangeIso.{u, _, _} j f
      AddCommGrpCat.{max (u + 1) v})

end Stacks.EtaleCohomology

end
