module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompProperSupportBaseChange
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompProperSupportOpen
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompProperSupportSeparated

import StacksCore.Tactic.StacksAttribute

/-!
# Parts (b) and (c) of Stacks 0F79

Let `f' : X ⟶ Y'` and `g : Y' ⟶ Y` be morphisms of a big étale site with `f'` and `f = g ∘ f'`
locally quasi-finite and `g` separated and locally of finite type, and let
`(g ∘ f')_! ≅ g_! ∘ f'_!` be the isomorphism of Stacks 0F79
(`AlgebraicGeometry.SmallEtale.fShriekCompProperIso`). This file registers its compatibility with
base change (part (b)) and its agreement with the isomorphism of Stacks 0F50 when `f'` is
separated (part (c)); part (a) is
`AlgebraicGeometry.SmallEtale.sepCompShriekMap_openCovariance`. In the Lean names the morphism
`f'` of the source is `f`.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekCompProperIso_baseChange` — **Stacks 0F79, part (b)**.
* `AlgebraicGeometry.SmallEtale.fShriekCompProperIso_eq_of_isSeparated` — **Stacks 0F79,
  part (c)**.

## Implementation notes

The base-change isomorphism `b⁻¹ g_! ≅ g₁_! b'⁻¹` of Stacks 0F55 enters part (b) through the
base-change map `AlgebraicGeometry.SmallEtale.properSupportBaseChange`, whose being an isomorphism
is the content of Stacks 0F55: the compatibility of part (b) is an identity of maps and does not
depend on it. The base-change isomorphism of Stacks 0F5J is available for abelian sheaves with
values in `AddCommGrpCat.{u + 1}`, so part (b) is stated there.

## References

* [Stacks Project, Tag 0F79](https://stacks.math.columbia.edu/tag/0F79)
* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 0F55](https://stacks.math.columbia.edu/tag/0F55)
* [Stacks Project, Tag 0F50](https://stacks.math.columbia.edu/tag/0F50)
* [Stacks Project, Tag 0F6N](https://stacks.math.columbia.edu/tag/0F6N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section PartB

variable (B : BigEtaleSite.{u}) {X Y Z X₁ Y₁ Z₁ : B.Scheme}
  (f : X ⟶ Y) (g : Y ⟶ Z) (a : X₁ ⟶ X) (f₁ : X₁ ⟶ Y₁) (b' : Y₁ ⟶ Y) (g₁ : Y₁ ⟶ Z₁)
  (b : Z₁ ⟶ Z) (sq₁ : IsPullback a f₁ f b') (sq₂ : IsPullback b' g₁ g b)
  [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map (f ≫ g))]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})

/-- **Stacks 0F79, part (b).** For a base change `b : Z₁ ⟶ Z`, with cartesian squares
`X₁ = X ×_Y Y₁` and `Y₁ = Y ×_Z Z₁`, the isomorphism `(g ∘ f)_! ≅ g_! ∘ f_!` of Stacks 0F79 is
compatible with the base-change isomorphisms of Stacks 0F5J and 0F55: the base-change
isomorphism `b⁻¹ (g ∘ f)_! F ≅ (g₁ ∘ f₁)_! a⁻¹ F` of Stacks 0F5J followed by the isomorphism for
`f₁` and `g₁` equals `b⁻¹` of the isomorphism for `f` and `g`, followed by the base change
`b⁻¹ g_! ⟶ g₁_! b'⁻¹` of Stacks 0F55 and `g₁_!` of the base-change isomorphism
`b'⁻¹ f_! F ≅ f₁_! a⁻¹ F` of Stacks 0F5J. -/
@[stacks 0F79 "part (b), compatibility with the base change isomorphisms of 0F5J and 0F55"]
public theorem fShriekCompProperIso_baseChange :
    letI := locallyOfFiniteType_of_isPullback B a f₁ f b' sq₁
    letI := locallyQuasiFinite_of_isPullback B a f₁ f b' sq₁
    letI := locallyOfFiniteType_of_isPullback B b' g₁ g b sq₂
    letI : IsSeparated (B.inclusion.map g₁) :=
      MorphismProperty.of_isPullback (sq₂.map B.inclusion) inferInstance
    letI : LocallyQuasiFinite (B.inclusion.map (f₁ ≫ g₁)) :=
      MorphismProperty.of_isPullback ((sq₁.paste_vert sq₂).map B.inclusion) inferInstance
    (fShriekBaseChangeNatIso.{u} B a (f₁ ≫ g₁) (f ≫ g) b (sq₁.paste_vert sq₂)).hom.app F ≫
        (fShriekCompProperIso.{u, u + 1} B f₁ g₁).hom.app ((abPullback.{u, u + 1} B a).obj F) =
      (abPullback.{u, u + 1} B b).map ((fShriekCompProperIso.{u, u + 1} B f g).hom.app F) ≫
        properSupportBaseChange.{u, u + 1} B b' g₁ g b sq₂
          ((fShriekFunctor.{u, u + 1} B f).obj F) ≫
        (properSupportFunctor.{u, u + 1} B g₁).map
          ((fShriekBaseChangeNatIso.{u} B a f₁ f b' sq₁).hom.app F) := by
  have := locallyOfFiniteType_of_isPullback B a f₁ f b' sq₁
  have := locallyQuasiFinite_of_isPullback B a f₁ f b' sq₁
  have := locallyOfFiniteType_of_isPullback B b' g₁ g b sq₂
  have : IsSeparated (B.inclusion.map g₁) :=
    MorphismProperty.of_isPullback (sq₂.map B.inclusion) inferInstance
  have : LocallyQuasiFinite (B.inclusion.map (f₁ ≫ g₁)) :=
    MorphismProperty.of_isPullback ((sq₁.paste_vert sq₂).map B.inclusion) inferInstance
  exact sepCompShriekMap_baseChange B f g a f₁ b' g₁ b sq₁ sq₂ F

end PartB

section PartC

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map (f ≫ g))]

/-- **Stacks 0F79, part (c).** If `f` is separated as well, the isomorphism
`(g ∘ f)_! ≅ g_! ∘ f_!` of Stacks 0F79 is the isomorphism `(g ∘ f)_! = g_! ∘ f_!` of
proper-support direct images of Stacks 0F50, read through the identifications of Stacks 0F6N of
`(g ∘ f)_!` and `f_!` with their proper-support models. -/
@[stacks 0F79 "part (c), the isomorphism of 0F50 via the identifications of 0F6N for f' separated"]
public theorem fShriekCompProperIso_eq_of_isSeparated [IsSeparated (B.inclusion.map f)] :
    letI := isSeparated_map_comp B f g
    fShriekCompProperIso.{u, v} B f g =
      fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g) ≪≫
        (properSupportFunctor_compIso B f g).val.symm ≪≫
        Functor.isoWhiskerRight (fShriekFunctorIsoProperSupport.{u, v} B f).symm
          (properSupportFunctor.{u, max (u + 1) v} B g) := by
  let := isSeparated_map_comp B f g
  exact Iso.ext (NatTrans.ext (funext fun F => sepCompShriekMap_eq_of_isSeparated B f g F))

end PartC

end AlgebraicGeometry.SmallEtale

end
