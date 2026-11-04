module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensor
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportModuleLift

/-!
# The direct image with compact support of sheaves of `Λ`-modules is a sheafification

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site and let `Λ` be a
commutative ring. The `f_!` of Stacks 0F6R on abelian sheaves is by definition the
sheafification of the finite-support direct image presheaf `f_{p!}` of Stacks 0F6M; this file
proves the same of the `Λ`-linear `f_!`, namely that
`AlgebraicGeometry.SmallEtale.fShriekMod` is the sheafification, *in sheaves of `Λ`-modules*, of
`AlgebraicGeometry.SmallEtale.modFiniteSupportPresheaf`.

This is what makes the presheaf-level construction of [Stacks, Tag 0GKF] usable: the source
builds its comparison map `can` as a map of presheaves out of `f_{p!}`, and a map of presheaves
of `Λ`-modules out of `f_{p!}F` induces one out of `f_!F` only through this identification.

## Main definitions

* `Stacks.ModuleCatLift.homOfScalarEnd` and `Stacks.ModuleCatLift.isoOfScalarEnd` — a morphism
  of the abelian sheaves underlying two sheaves of `Λ`-modules which commutes with
  multiplication by every scalar is a morphism of sheaves of `Λ`-modules.
* `Stacks.ModuleCatLift.sheafifyForgetIso` — sheafification commutes with forgetting the module
  structure. This is `CategoryTheory.sheafComposeNatIso` for `forget₂ (ModuleCat Λ)
  AddCommGrpCat`.

## Main results

* `Stacks.ModuleCatLift.presheafToSheaf_map_presheafModuleSmul` — **sheafifying multiplication
  by a scalar gives multiplication by that scalar.** This is the `Λ`-linearity of
  `sheafifyForgetIso`.
* `AlgebraicGeometry.SmallEtale.fShriekModSheafifyIso` — **`f_!` with coefficients in `Λ` is the
  sheafification of `f_{p!}` with coefficients in `Λ`.**

## Implementation notes

The underlying abelian sheaf of `fShriekMod F` is, on the nose, the abelian sheafification of
the abelian presheaf underlying `modFiniteSupportPresheaf F`: both lifts to `Λ`-modules of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift` leave the underlying abelian
object untouched. So the comparison of the two sheaves of `Λ`-modules is exactly the comparison
of *sheafification with the forgetful functor*, `CategoryTheory.sheafComposeNatIso`, together
with the verification that it is `Λ`-linear. That verification is the naturality of that
isomorphism applied to multiplication by a scalar on the presheaf of `Λ`-modules, which exists
as a morphism of presheaves of `Λ`-modules because `Λ` is commutative — the same point as in
`Stacks.ModuleCatLift.valueLiftSheafFiberIso`.

Nothing here carries a `stacks` attribute: Stacks 0F6R is attributed to
`AlgebraicGeometry.SmallEtale.fShriekFunctor`, and this is the comparison of two descriptions of
its `Λ`-linear lift.

## References

* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModuleCatLift

universe w r u₁ v₁ u₂ v₂

section Hom

variable (Λ : Type r) [Ring Λ] {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- **A morphism of the underlying abelian sheaves commuting with the scalar actions is a
morphism of sheaves of `Λ`-modules.** -/
public def homOfScalarEnd {F G : Sheaf J (ModuleCat.{w} Λ)}
    (α : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G)
    (h : ∀ (a : Λ) (V : Cᵒᵖ), α.hom.app V ≫ (G.obj.obj V).smul a =
      (F.obj.obj V).smul a ≫ α.hom.app V) :
    F ⟶ G :=
  ObjectProperty.homMk
    { app := fun V => ModuleCat.homMk (α.hom.app V) fun a => h a V
      naturality := fun _ _ g =>
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map_injective (α.hom.naturality g) }

/-- The morphism of abelian sheaves underlying `homOfScalarEnd Λ J α h` is `α`. -/
@[simp]
public lemma sheafCompose_map_homOfScalarEnd {F G : Sheaf J (ModuleCat.{w} Λ)}
    (α : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G)
    (h : ∀ (a : Λ) (V : Cᵒᵖ), α.hom.app V ≫ (G.obj.obj V).smul a =
      (F.obj.obj V).smul a ≫ α.hom.app V) :
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
      (homOfScalarEnd.{w} Λ J α h) = α :=
  rfl

/-- **An isomorphism of the underlying abelian sheaves commuting with the scalar actions is an
isomorphism of sheaves of `Λ`-modules.** -/
public def isoOfScalarEnd {F G : Sheaf J (ModuleCat.{w} Λ)}
    (α : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G)
    (h : ∀ (a : Λ) (V : Cᵒᵖ), α.hom.hom.app V ≫ (G.obj.obj V).smul a =
      (F.obj.obj V).smul a ≫ α.hom.hom.app V) :
    F ≅ G :=
  haveI : IsIso ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
      (homOfScalarEnd.{w} Λ J α.hom h)) := by
    rw [sheafCompose_map_homOfScalarEnd]
    infer_instance
  haveI := isIso_of_reflects_iso (homOfScalarEnd.{w} Λ J α.hom h)
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))
  asIso (homOfScalarEnd.{w} Λ J α.hom h)

/-- The morphism of abelian sheaves underlying `(isoOfScalarEnd Λ J α h).hom` is `α.hom`. -/
@[simp]
public lemma sheafCompose_map_isoOfScalarEnd_hom {F G : Sheaf J (ModuleCat.{w} Λ)}
    (α : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj G)
    (h : ∀ (a : Λ) (V : Cᵒᵖ), α.hom.hom.app V ≫ (G.obj.obj V).smul a =
      (F.obj.obj V).smul a ≫ α.hom.hom.app V) :
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
      (isoOfScalarEnd.{w} Λ J α h).hom = α.hom :=
  rfl

end Hom

section Sheafify

variable (Λ : Type r) [CommRing Λ]

/-- Multiplication by a scalar on a presheaf of `Λ`-modules is natural in the presheaf. -/
public lemma presheafModuleSmul_naturality {K : Type u₂} [Category.{v₂} K]
    {P Q : K ⥤ ModuleCat.{w} Λ} (g : P ⟶ Q) (a : Λ) :
    g ≫ presheafModuleSmul.{w} Λ Q a = presheafModuleSmul.{w} Λ P a ≫ g :=
  NatTrans.ext (funext fun U => moduleSmulHom_naturality.{w} Λ (g.app U) a)

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J (ModuleCat.{w} Λ)]

/-- **Sheafifying multiplication by a scalar gives multiplication by that scalar.** -/
public lemma presheafToSheaf_map_presheafModuleSmul (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) (a : Λ) :
    (presheafToSheaf J (ModuleCat.{w} Λ)).map (presheafModuleSmul.{w} Λ P a) =
      moduleSheafSmul.{w} Λ J ((presheafToSheaf J (ModuleCat.{w} Λ)).obj P) a := by
  refine ((sheafificationAdjunction J (ModuleCat.{w} Λ)).homEquiv P _).injective ?_
  have hnat := (sheafificationAdjunction J (ModuleCat.{w} Λ)).unit.naturality
    (presheafModuleSmul.{w} Λ P a)
  simp only [Functor.comp_map, Functor.id_map] at hnat
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← hnat]
  exact (presheafModuleSmul_naturality.{w} Λ
    ((sheafificationAdjunction J (ModuleCat.{w} Λ)).unit.app P) a).symm

variable [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- **Sheafification commutes with forgetting the module structure.** -/
public def sheafifyForgetIso (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) :
    (presheafToSheaf J AddCommGrpCat.{w}).obj
        (P ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj
        ((presheafToSheaf J (ModuleCat.{w} Λ)).obj P) :=
  (sheafComposeNatIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
    (sheafificationAdjunction J (ModuleCat.{w} Λ))
    (sheafificationAdjunction J AddCommGrpCat.{w})).app P

/-- **The comparison of sheafification with the forgetful functor is `Λ`-linear.** On the left
the scalar action is the sheafification of multiplication by the scalar on the abelian presheaf;
on the right it is multiplication by the scalar on the sheafification. -/
public lemma sheafifyForgetIso_smul (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) (a : Λ) :
    (presheafToSheaf J AddCommGrpCat.{w}).map
          (Functor.whiskerRight (presheafModuleSmul.{w} Λ P a)
            (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})) ≫
        (sheafifyForgetIso.{w} Λ J P).hom =
      (sheafifyForgetIso.{w} Λ J P).hom ≫
        sheafScalarEnd.{w} Λ J ((presheafToSheaf J (ModuleCat.{w} Λ)).obj P) a := by
  have hnat := (sheafComposeNatIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
    (sheafificationAdjunction J (ModuleCat.{w} Λ))
    (sheafificationAdjunction J AddCommGrpCat.{w})).hom.naturality
      (presheafModuleSmul.{w} Λ P a)
  simp only [Functor.comp_map, Functor.whiskeringRight_obj_map] at hnat
  rw [presheafToSheaf_map_presheafModuleSmul.{w} Λ J P a,
    sheafCompose_map_moduleSheafSmul.{w} Λ J _ a] at hnat
  exact hnat

end Sheafify

end Stacks.ModuleCatLift

namespace AlgebraicGeometry.SmallEtale

universe u v r

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The scalar action on the `Λ`-linear finite-support direct image, read on the underlying
abelian presheaf, is the action of `f_{p!}` on multiplication by that scalar. -/
public theorem whiskerRight_presheafModuleSmul_modFiniteSupportPresheaf
    (F : ModuleSheaf.{u, v, r} B X Λ) (a : Λ) :
    Functor.whiskerRight
        (Stacks.ModuleCatLift.presheafModuleSmul.{max (u + 1) v r} Λ
          ((modFiniteSupportPresheaf.{u, v, r} B Λ f).obj F) a)
        (forget₂ (ModuleCat.{max (u + 1) v r} Λ) AddCommGrpCat.{max (u + 1) v r}) =
      (finiteSupportPushforward.{u, max (u + 1) v r} B f (fun _ => inferInstance)).1.map
        (Stacks.ModuleCatLift.sheafScalarEnd Λ
          (SmallEtale.topology B X.obj X.property) F a) :=
  NatTrans.ext (funext fun V => by
    exact (modFiniteSupportPresheaf_obj_smul.{u, v, r} B Λ f F V a).symm)

/-- **The direct image with compact support of sheaves of `Λ`-modules is the sheafification of
the finite-support direct image of sheaves of `Λ`-modules.** The `f_!` of Stacks 0F6R is the
sheafification of the `f_{p!}` of Stacks 0F6M by definition, and the same holds after lifting
both to sheaves of `Λ`-modules: the underlying abelian sheaves agree on the nose, and the
comparison of sheafification with the forgetful functor is `Λ`-linear. -/
public def fShriekModSheafifyIso (F : ModuleSheaf.{u, v, r} B X Λ) :
    (fShriekMod.{u, v, r} B Λ f).obj F ≅
      (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
          (ModuleCat.{max (u + 1) v r} Λ)).obj
        ((modFiniteSupportPresheaf.{u, v, r} B Λ f).obj F) := by
  letI := preservesSheafification_forgetModuleCat.{u, v, r} B Y Λ
  refine Stacks.ModuleCatLift.isoOfScalarEnd.{max (u + 1) v r} Λ
    (SmallEtale.topology B Y.obj Y.property)
    (F := (fShriekMod.{u, v, r} B Λ f).obj F)
    (G := (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
      (ModuleCat.{max (u + 1) v r} Λ)).obj ((modFiniteSupportPresheaf.{u, v, r} B Λ f).obj F))
    (Stacks.ModuleCatLift.sheafifyForgetIso.{max (u + 1) v r} Λ
      (SmallEtale.topology B Y.obj Y.property)
      ((modFiniteSupportPresheaf.{u, v, r} B Λ f).obj F)) ?_
  intro a V
  have h := Stacks.ModuleCatLift.sheafifyForgetIso_smul.{max (u + 1) v r} Λ
    (SmallEtale.topology B Y.obj Y.property)
    ((modFiniteSupportPresheaf.{u, v, r} B Λ f).obj F) a
  rw [whiskerRight_presheafModuleSmul_modFiniteSupportPresheaf.{u, v, r} B Λ f F a] at h
  exact (congrArg (fun m => m.hom.app V) h).symm

end AlgebraicGeometry.SmallEtale

end
