module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafForgetAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose

/-!
# Extension by zero of a constant module sheaf underlies extension by zero of a constant
abelian sheaf

Let `U ⟶ X` be an étale object of the small étale site of a scheme `X` in a big étale site `B`,
and let `Λ` be a ring. This file identifies the abelian sheaf underlying
`AlgebraicGeometry.moduleShriekConstant`, the extension by zero from `U` of the constant sheaf of
free rank-one `Λ`-modules, with the extension by zero from `U` of the constant abelian sheaf on
the additive group `ULift Λ`; and, at `Λ = ULift (ℤ/nℤ)`, with
`AlgebraicGeometry.abelianShriekZMod`.

## Main definitions

* `AlgebraicGeometry.moduleShriekConstantForget₂Iso` — the comparison at a general ring `Λ`,
  natural in the étale object only through the two functors it is built from.
* `AlgebraicGeometry.abelianShriekZModIsoForget₂ModuleShriekConstant` — the same at the finite
  cyclic rings, where the right-hand side is `AlgebraicGeometry.abelianShriekZMod`.

## Implementation notes

Both constructions are the *same* sheaf pullback — Mathlib's
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` along the continuous site functor
`AlgebraicGeometry.smallEtalePostcompose` — read at two coefficient categories, and passing to
the underlying abelian sheaf is `CategoryTheory.sheafCompose` at
`forget₂ (ModuleCat Λ) AddCommGrpCat`. So the comparison is an instance of
`CategoryTheory.Functor.sheafPullbackSheafComposeIso`, together with
`Stacks.ModuleCatLift.constantSheafForget₂Iso` for the constant sheaf being extended.

Three inputs of that isomorphism are supplied by hand, as in
`AlgebraicGeometry.smallEtaleUnderlyingSetCommutes`, which is the same argument for the forgetful
functor to sets along small étale base change. The pointwise left Kan extensions exist at both
coefficient categories because the comma categories `CostructuredArrow Φ.op Y` are essentially
small in `Type (u + 1)`, where both categories have their colimits. The forgetful functor of
`Λ`-modules preserves *all* colimits of that size, by `ModuleCat.forget₂PreservesColimitsOfSize`,
so no filteredness of the comma categories is needed here — unlike for the forgetful functor to
sets.

**This is not the counterexample `Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`.** That
one says the lower shriek of a sheaf of modules over a *sheaf of rings* may differ, as an abelian
sheaf, from the lower shriek of the underlying abelian sheaf: it compares
`SheafOfModules.toSheaf ⋙ Functor.sheafPullback` with `SheafOfModules.pullback ⋙
SheafOfModules.toSheaf`, and the discrepancy is created by the change of the *ring sheaf* along
the site functor, which postcomposition by a fixed `forget₂` cannot see. Here the coefficients
are a single ring `Λ` in the model `Sheaf J (ModuleCat Λ)`, both functors being sheaf pullbacks
of one and the same site functor; so the comparison of this file is unobstructed by it.

Nothing here carries a `stacks` attribute: a comparison between two constructions each of which
is tagged at its own definition is infrastructure, not a tag.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 00YT](https://stacks.math.columbia.edu/tag/00YT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **The abelian sheaf underlying `j_{U!}\underline{Λ}_U` is `j_{U!}\underline{ULift Λ}_U`.**
Extension by zero from an étale object `U` of `X` commutes with passing from sheaves of
`Λ`-modules to the underlying sheaves of abelian groups, when applied to the constant sheaf of
free rank-one `Λ`-modules.

Both extensions by zero are sheaf pullbacks along the same continuous site functor
`AlgebraicGeometry.smallEtalePostcompose`, so this is
`CategoryTheory.Functor.sheafPullbackSheafComposeIso` composed with
`Stacks.ModuleCatLift.constantSheafForget₂Iso`. -/
public def moduleShriekConstantForget₂Iso (Λ : Type (u + 1)) [Ring Λ]
    (U : SmallEtale B X.obj X.property) :
    (sheafCompose (SmallEtale.topology B X.obj X.property)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (moduleShriekConstant.{u, u + 1, u + 1} B X Λ U) ≅
      (abelianExtensionByZero B X.obj X.property U).obj
        ((constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} Λ))) := by
  letI := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X Λ
  letI := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B U.obj.left Λ
  letI : (SmallEtale.topology B U.obj.left.obj U.obj.left.property).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ _
  letI : (SmallEtale.topology B X.obj X.property).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ _
  letI : (SmallEtale.topology B X.obj X.property).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ _
  letI : ∀ P : (SmallEtale B U.obj.left.obj U.obj.left.property)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePostcompose B X.obj X.property U).op.HasPointwiseLeftKanExtension P :=
    fun _ Y => by
      let := hasColimitsOfShape_of_essentiallySmall.{u + 1}
        (CostructuredArrow (smallEtalePostcompose B X.obj X.property U).op Y)
        (ModuleCat.{u + 1} Λ)
      infer_instance
  letI : ∀ P : (SmallEtale B U.obj.left.obj U.obj.left.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePostcompose B X.obj X.property U).op.HasPointwiseLeftKanExtension P :=
    fun _ Y => by
      let := hasColimitsOfShape_of_essentiallySmall.{u + 1}
        (CostructuredArrow (smallEtalePostcompose B X.obj X.property U).op Y)
        AddCommGrpCat.{u + 1}
      infer_instance
  letI : ∀ Y : (SmallEtale B X.obj X.property)ᵒᵖ,
      PreservesColimitsOfShape
        (CostructuredArrow (smallEtalePostcompose B X.obj X.property U).op Y)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := fun Y => by
    let := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow (smallEtalePostcompose B X.obj X.property U).op Y)
      AddCommGrpCat.{u + 1}
    infer_instance
  refine ((sheafCompose (SmallEtale.topology B X.obj X.property)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso
      ((Functor.sheafPullbackConstruction.sheafPullbackIso
        (smallEtalePostcompose B X.obj X.property U) (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
        (SmallEtale.topology B X.obj X.property)).app _).symm) ≪≫ ?_
  refine ((smallEtalePostcompose B X.obj X.property U).sheafPullbackSheafComposeIso
    (ModuleCat.{u + 1} Λ) (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (SmallEtale.topology B X.obj X.property)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    ((constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ (ULift.{u + 1} Λ)))).symm ≪≫ ?_
  refine ((smallEtalePostcompose B X.obj X.property U).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      (SmallEtale.topology B X.obj X.property)).mapIso
    ((Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1, u + 1, u + 1, u} Λ
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property)).app
        (ModuleCat.of Λ (ULift.{u + 1} Λ))) ≪≫ ?_
  exact (Functor.sheafPullbackConstruction.sheafPullbackIso
    (smallEtalePostcompose B X.obj X.property U) AddCommGrpCat.{u + 1}
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (SmallEtale.topology B X.obj X.property)).app _

/-- **`AlgebraicGeometry.abelianShriekZMod` is the abelian sheaf underlying
`AlgebraicGeometry.moduleShriekConstant` at `ℤ/nℤ`.** The sheaf `j_{U!}(ℤ/nℤ)` of abelian groups
is the abelian sheaf underlying the extension by zero from `U` of the constant sheaf of free
rank-one `ULift (ℤ/nℤ)`-modules.

This is `AlgebraicGeometry.moduleShriekConstantForget₂Iso` at `Λ = ULift (ℤ/nℤ)`, followed by
collapsing the iterated universe lift `ULift (ULift (ℤ/nℤ))` of the value of the constant sheaf.
The ring has to be lifted to `Type (u + 1)` because that is the universe at which the shriek
presentations of `AlgebraicGeometry.HasFiniteShriekPresentation`, and hence the library's
Stacks 093C for sheaves of modules, are stated. -/
public def abelianShriekZModIsoForget₂ModuleShriekConstant (n : ℕ)
    (U : SmallEtale B X.obj X.property) :
    abelianShriekZMod B X n U ≅
      (sheafCompose (SmallEtale.topology B X.obj X.property)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})).obj
        (moduleShriekConstant.{u, u + 1, u + 1} B X (ULift.{u + 1} (ZMod n)) U) :=
  ((abelianExtensionByZero B X.obj X.property U).mapIso
      ((constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
        AddCommGrpCat.{u + 1}).mapIso
          (AddEquiv.ulift (α := ULift.{u + 1} (ZMod n))).symm.toAddCommGrpIso)) ≪≫
    (moduleShriekConstantForget₂Iso B X (ULift.{u + 1} (ZMod n)) U).symm

end AlgebraicGeometry

end
