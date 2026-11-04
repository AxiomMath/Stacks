module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSheaves
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Higher direct image of abelian sheaves is the sheafification of a derived presheaf

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` contained in a big fppf
site `B`, and let `τ` be one of the five topologies Zariski, étale, smooth, syntomic, fppf. The
higher direct image `Rⁱf_*` of abelian sheaves along `f`, for the associated sites of
Stacks 06TP, is the sheafification of the derived *presheaf* direct image.

## Main definitions

* `AlgebraicGeometry.Stack.abelianFibreCohomologyPresheaf`: the derived presheaf direct image,
  the right derived functors of sheaves-to-presheaves followed by right Kan extension along the
  functor underlying `f`.

## Main results

* `AlgebraicGeometry.Stack.abelianHigherDirectImage_iso_sheafify_fibreCohomology`: the higher
  direct image on abelian sheaves is the derived presheaf direct image followed by
  sheafification.
-/


@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules

universe u w a

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Presheaf

variable {X Y : Type (u + 1)} [Category.{u} X] [Category.{u} Y]
  (pX : X ⥤ BigFppfOver B S hS) (f : X ⥤ Y) (τ : SiteKind)

/-- The derived presheaf direct image along `f` of abelian sheaves on the site associated with
`pX` for the topology `τ`: the right derived functors of the inclusion of sheaves into
presheaves followed by right Kan extension along `f.op`. -/
abbrev abelianFibreCohomologyPresheaf
    [HasSheafify (BigFppfOver.associatedTopology B S hS pX τ) AddCommGrpCat.{max (u + 1) a}]
    [HasInjectiveResolutions (Sheaf (BigFppfOver.associatedTopology B S hS pX τ)
      AddCommGrpCat.{max (u + 1) a})] (n : ℕ) :
    Sheaf (BigFppfOver.associatedTopology B S hS pX τ) AddCommGrpCat.{max (u + 1) a} ⥤
      Yᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a} :=
  letI := (f.op.ranAdjunction AddCommGrpCat.{max (u + 1) a}).right_adjoint_additive
  letI := (sheafificationAdjunction (BigFppfOver.associatedTopology B S hS pX τ)
    AddCommGrpCat.{max (u + 1) a}).right_adjoint_additive
  (sheafToPresheaf (BigFppfOver.associatedTopology B S hS pX τ)
    AddCommGrpCat.{max (u + 1) a} ⋙ f.op.ran).rightDerived n

end Presheaf

section AlgebraicStacks

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (τ : SiteKind)

local notation "g" => CatFiberedInGroupoids.homFunctor f.hom
local notation "JX" => BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ
local notation "JY" => BigFppfOver.associatedTopology B S hS 𝒴.val.val.p τ

/-- The functor underlying a 1-morphism of algebraic stacks is cocontinuous for the associated
topologies of Stacks 06TP. -/
instance isCocontinuous_homFunctor_associatedTopology :
    (g).IsCocontinuous JX JY :=
  (BigFppfOver.isContinuous_and_isCocontinuous_associatedTopology B S hS f.hom τ).2

/-- Direct image of abelian sheaves along a 1-morphism of algebraic stacks is additive. -/
instance abelianDirectImageAdditive
    [HasSheafify JX AddCommGrpCat.{max (u + 1) a}]
    [HasSheafify JY AddCommGrpCat.{max (u + 1) a}] :
    ((g).sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a} JX JY).Additive := by
  have := ((g).op.ranAdjunction AddCommGrpCat.{max (u + 1) a}).right_adjoint_additive
  have := (sheafificationAdjunction JX AddCommGrpCat.{max (u + 1) a}).right_adjoint_additive
  have := (sheafificationAdjunction JY AddCommGrpCat.{max (u + 1) a}).right_adjoint_additive
  have := Functor.additive_of_iso
    ((g).sheafPushforwardCocontinuousCompSheafToPresheafIso
      AddCommGrpCat.{max (u + 1) a} JX JY).symm
  apply Functor.additive_of_comp_faithful _ (sheafToPresheaf JY AddCommGrpCat.{max (u + 1) a})

/-- The `n`-th higher direct image of abelian sheaves along a 1-morphism of algebraic stacks is
the sheafification of the `n`-th derived presheaf direct image. -/
def abelianHigherDirectImage_iso_sheafify_fibreCohomology (n : ℕ) :
    letI := site_hasSheafify_addCommGrp.{u + 1, u, a} (J := JX)
    letI := site_hasSheafify_addCommGrp.{u + 1, u, a} (J := JY)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max (u + 1) a}
      JX AddCommGrpCat.{max (u + 1) a}
    letI := IsGrothendieckAbelian.enoughInjectives
      (C := Sheaf JX AddCommGrpCat.{max (u + 1) a})
    letI := abelianDirectImageAdditive.{u, w, a} B S hS f τ
    ((g).sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a} JX JY).rightDerived n ≅
      abelianFibreCohomologyPresheaf.{u, a} B S hS 𝒳.val.val.p (g) τ n ⋙
        presheafToSheaf JY AddCommGrpCat.{max (u + 1) a} := by
  letI := site_hasSheafify_addCommGrp.{u + 1, u, a} (J := JX)
  letI := site_hasSheafify_addCommGrp.{u + 1, u, a} (J := JY)
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max (u + 1) a}
    JX AddCommGrpCat.{max (u + 1) a}
  letI := IsGrothendieckAbelian.enoughInjectives
    (C := Sheaf JX AddCommGrpCat.{max (u + 1) a})
  letI := abelianDirectImageAdditive.{u, w, a} B S hS f τ
  let P := (g).sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a} JX JY
  let G := sheafToPresheaf JX AddCommGrpCat.{max (u + 1) a} ⋙ (g).op.ran
  let T := presheafToSheaf JY AddCommGrpCat.{max (u + 1) a}
  have : G.Additive := by
    have := ((g).op.ranAdjunction AddCommGrpCat.{max (u + 1) a}).right_adjoint_additive
    infer_instance
  have hcomp : P ≅ G ⋙ T :=
    calc
      P ≅ P ⋙ sheafToPresheaf JY AddCommGrpCat.{max (u + 1) a} ⋙ T :=
        (Functor.rightUnitor P).symm ≪≫
          Functor.isoWhiskerLeft P
            (sheafificationNatIso JY AddCommGrpCat.{max (u + 1) a}) ≪≫
          (Functor.associator P (sheafToPresheaf JY AddCommGrpCat.{max (u + 1) a}) T).symm
      _ ≅ G ⋙ T :=
        Functor.isoWhiskerRight
          ((g).sheafPushforwardCocontinuousCompSheafToPresheafIso
            AddCommGrpCat.{max (u + 1) a} JX JY) T
  have hT : T.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels T
  exact CategoryTheory.Functor.rightDerivedIsoOfNatIso hcomp n ≪≫
    CategoryTheory.Functor.rightDerivedCompIso G T n

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
