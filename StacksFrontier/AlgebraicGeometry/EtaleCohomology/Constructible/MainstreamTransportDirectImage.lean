module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.MainstreamTransport

/-!
# The transport of sheaves of modules to Mathlib's small étale site commutes with direct image

The functor `AlgebraicGeometry.SmallEtale.moduleSheafToEtale` carries a sheaf of `Λ`-modules on
the small étale site of Stacks 021B of a scheme `X` of a big étale site `B` to the underlying
abelian sheaf on Mathlib's small étale site `X.smallEtaleTopology`. This file shows that it
commutes with direct image along any morphism `f : T ⟶ S` of `B`: transporting and then taking
the direct image on Mathlib's small étale sites is taking the direct image on the sites of
Stacks 021B and then transporting. Combined with
`AlgebraicGeometry.SmallEtale.moduleSheafToEtaleConstantIso`, the transport of the direct image
of a constant sheaf is the direct image of a constant sheaf, which is what is needed to carry an
embedding into a finite sum of sheaves `f_* M` (Stacks 09Z7) from one site to the other.

## Main results

* `AlgebraicGeometry.SmallEtale.moduleSheafToEtaleDirectImageIso` — the transport commutes with
  direct image.
* `AlgebraicGeometry.SmallEtale.moduleSheafToEtaleDirectImageConstantIso` — the transport of the
  direct image of a constant sheaf of modules is the direct image of the constant abelian sheaf
  on the underlying group.

## References

* [Stacks Project, Tag 09Z7](https://stacks.math.columbia.edu/tag/09Z7)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [Ring Λ] {S T : B.Scheme} (f : T ⟶ S)

/-- Composition with forgetting the module structure commutes with direct image along base
change of the sites of Stacks 021B, on the nose. -/
def sheafComposeForgetPushforwardIso :
    (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} Λ) (topology B S.obj S.property) (topology B T.obj T.property) ⋙
      sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
    sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
      (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (topology B S.obj S.property) (topology B T.obj T.property) :=
  Iso.refl _

/-- **The transport functor commutes with direct image.** For a morphism `f : T ⟶ S` of a big
étale site, transporting a sheaf of `Λ`-modules from the site of Stacks 021B of `T` and then
taking its direct image along `f` on Mathlib's small étale sites is taking the direct image on
the sites of Stacks 021B and then transporting. The two presentations of the small étale site
have the same direct image along base change
(`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`), and composition with
forgetting the module structure commutes with direct image on the nose. -/
def moduleSheafToEtaleDirectImageIso :
    moduleSheafToEtale B T Λ ⋙
        Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, 0} (B.inclusion.map f) ≅
      (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          (ModuleCat.{u + 1} Λ) (topology B S.obj S.property) (topology B T.obj T.property) ⋙
        moduleSheafToEtale B S Λ :=
  let ES := sheafEquiv B S.obj S.property AddCommGrpCat.{u + 1}
  let ET := sheafEquiv B T.obj T.property AddCommGrpCat.{u + 1}
  let D := Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, 0} (B.inclusion.map f)
  let DB := (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (topology B S.obj S.property) (topology B T.obj T.property)
  let F := sheafCompose (topology B T.obj T.property)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  -- `ET.functor ⋙ D ≅ DB ⋙ ES.functor`
  let e₁ : ET.functor ⋙ D ≅ DB ⋙ ES.functor :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft (ET.functor ⋙ D) ES.counitIso.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft ET.functor (toEtaleSitePushforwardBaseChangeIso B f
          AddCommGrpCat.{u + 1}) ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ET.unitIso.symm DB ≪≫ Functor.leftUnitor _) ES.functor
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafComposeForgetPushforwardIso B Λ f).symm ES.functor ≪≫
    Functor.associator _ _ _

/-- **The transport of the direct image of a constant sheaf of modules** along `f : T ⟶ S` is the
direct image along `f`, on Mathlib's small étale sites, of the constant abelian sheaf on the
underlying group. -/
def moduleSheafToEtaleDirectImageConstantIso (M : ModuleCat.{u + 1} Λ) :
    (moduleSheafToEtale B S Λ).obj
        ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          (ModuleCat.{u + 1} Λ) (topology B S.obj S.property) (topology B T.obj T.property) |>.obj
          ((constantSheaf (topology B T.obj T.property) (ModuleCat.{u + 1} Λ)).obj M)) ≅
      (Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, 0} (B.inclusion.map f)).obj
        ((constantSheaf T.obj.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M)) :=
  ((moduleSheafToEtaleDirectImageIso B Λ f).app _).symm ≪≫
    (Stacks.EtaleCohomology.etaleAbelianDirectImage.{u, 0} (B.inclusion.map f)).mapIso
      ((moduleSheafToEtaleConstantIso B T Λ).app M)

end AlgebraicGeometry.SmallEtale

end
