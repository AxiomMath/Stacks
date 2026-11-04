module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

/-!
# The direct image of an injective abelian étale sheaf is injective

Let `f : X ⟶ Y` be a morphism in a big étale site. Inverse image along `f` is exact on abelian
sheaves on the small étale sites, so its right adjoint — direct image — carries injective
objects to injective objects. The same holds one level down, for the underlying presheaves:
the underlying presheaf of a direct image is a restriction along a representably flat functor,
and restriction along such a functor is right adjoint to an exact left Kan extension.

## Main results

* `AlgebraicGeometry.injective_smallEtalePushforward_obj` — the underlying presheaf of the
  direct image of an injective abelian étale sheaf is injective.
* `AlgebraicGeometry.injective_smallEtalePushforward` — the direct image of an injective
  abelian étale sheaf is injective.

## Implementation notes

Mathlib's left Kan extension along a flat functor is exact only for *small* categories,
whereas the small étale categories have their objects and their morphisms in different
universes. The argument is therefore transported along `CategoryTheory.ULiftHom.equiv` in each
variable: injectivity of a presheaf is invariant under the induced equivalence of presheaf
categories, so it can be checked after transport and read back. Injectivity of the sheaf then
follows from injectivity of its underlying presheaf because the inclusion of sheaves into
presheaves is fully faithful and right adjoint to sheafification.

## References

* [Stacks Project, Tag 03QB](https://stacks.math.columbia.edu/tag/03QB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (I : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})

/-- The underlying presheaf of the direct image of an injective abelian sheaf on the small
étale site of `X` is an injective presheaf on the small étale site of `Y`. -/
public theorem injective_smallEtalePushforward_obj [Injective I] :
    Injective (((smallEtaleBaseChange B f).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).obj I).obj := by
  let F := smallEtaleBaseChange B f
  let J := SmallEtale.topology B Y.obj Y.property
  let K := SmallEtale.topology B X.obj X.property
  let P := (F.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).obj I
  let Cₓ := SmallEtale B X.obj X.property
  let Cᵧ := SmallEtale B Y.obj Y.property
  let eₓ : Cₓ ≌ ULiftHom.{u + 1} Cₓ := ULiftHom.equiv
  let eᵧ : Cᵧ ≌ ULiftHom.{u + 1} Cᵧ := ULiftHom.equiv
  let F' : ULiftHom.{u + 1} Cᵧ ⥤ ULiftHom.{u + 1} Cₓ := eᵧ.inverse ⋙ F ⋙ eₓ.functor
  let preₓ : (Cₓᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      ((ULiftHom.{u + 1} Cₓ)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    (Functor.whiskeringLeft (ULiftHom.{u + 1} Cₓ)ᵒᵖ Cₓᵒᵖ AddCommGrpCat.{u + 1}).obj eₓ.inverse.op
  let preᵧ : (Cᵧᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      ((ULiftHom.{u + 1} Cᵧ)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    (Functor.whiskeringLeft (ULiftHom.{u + 1} Cᵧ)ᵒᵖ Cᵧᵒᵖ AddCommGrpCat.{u + 1}).obj eᵧ.inverse.op
  have : Injective I.obj :=
    (sheafificationAdjunction K AddCommGrpCat.{u + 1}).map_injective I inferInstance
  have : Injective (preₓ.obj I.obj) :=
    (preₓ.asEquivalence.map_injective_iff I.obj).2 inferInstance
  have : PreservesFiniteLimits
      (F'.op.lan : ((ULiftHom.{u + 1} Cᵧ)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        ((ULiftHom.{u + 1} Cₓ)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})) :=
    lan_preservesFiniteLimits_of_flat AddCommGrpCat.{u + 1} F'
  have hP' : F'.op ⋙ preₓ.obj I.obj = preᵧ.obj P.obj := rfl
  exact (preᵧ.asEquivalence.map_injective_iff P.obj).1
    (hP' ▸ (F'.op.lanAdjunction AddCommGrpCat.{u + 1}).map_injective
      (preₓ.obj I.obj) inferInstance)

/-- **Stacks 03QB.** The direct image of an injective abelian sheaf on the small étale site of
`X` is an injective abelian sheaf on the small étale site of `Y`. -/
public theorem injective_smallEtalePushforward [Injective I] :
    Injective (((smallEtaleBaseChange B f).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).obj I) :=
  (sheafificationAdjunction (SmallEtale.topology B Y.obj Y.property)
      AddCommGrpCat.{u + 1}).injective_of_map_injective _
    (injective_smallEtalePushforward_obj B f I)

end AlgebraicGeometry
