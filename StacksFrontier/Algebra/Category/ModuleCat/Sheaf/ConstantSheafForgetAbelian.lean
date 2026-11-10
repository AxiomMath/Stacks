module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions

/-!
# The constant sheaf of `Λ`-modules underlies the constant sheaf of abelian groups

Let `Λ` be a ring and let `(C, J)` be a site. The abelian sheaf underlying the constant sheaf of
`Λ`-modules on a module `E` is the constant sheaf of abelian groups on the abelian group underlying
`E`, and the comparison is equivariant for the action of `Λ`: it carries multiplication by `a : Λ`,
the endomorphism `Stacks.ModuleCatLift.sheafScalarEnd` of the underlying abelian sheaf, to the
constant sheaf of multiplication by `a` on `E`.

## Main definitions

* `Stacks.ModuleCatLift.constantSheafForget₂Iso` — the abelian sheaf underlying the constant sheaf
  of `Λ`-modules on `E` is the constant sheaf of abelian groups on the abelian group underlying
  `E`, naturally in `E`.

## Main results

* `Stacks.ModuleCatLift.constantSheafForget₂Iso_hom_app_scalar` — the comparison is
  `Λ`-equivariant: it carries multiplication by `a : Λ` on the sections of the constant sheaf on
  `E` to the constant sheaf of the morphism of abelian groups `a • · : E ⟶ E`.

## Implementation notes

The isomorphism is `CategoryTheory.constantCommuteCompose` for the forgetful functor
`forget₂ (ModuleCat Λ) AddCommGrpCat`. The coefficient ring `Λ` need not be commutative:
multiplication by `a : Λ` is used only as an endomorphism of an underlying abelian sheaf, never as
a morphism of `Λ`-modules.

The side conditions, `HasSheafify` for presheaves of `Λ`-modules and of abelian groups and
`J.HasSheafCompose` and `J.PreservesSheafification` for `forget₂ (ModuleCat Λ) AddCommGrpCat`, are
file-local instances derived from the universe inequality `UnivLE.{max u v, w}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w r u v

namespace Stacks.ModuleCatLift

variable (Λ : Type r) [Ring Λ] {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable [UnivLE.{max u v, w}]

/-- Postcomposition with `forget₂ (ModuleCat Λ) AddCommGrpCat` carries sheaves to sheaves. -/
local instance hasSheafCompose_forget₂ :
    J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
  ModuleSheaf.hasSheafCompose_forget₂.{w} Λ J

/-- Presheaves of `Λ`-modules admit sheafification. -/
local instance hasSheafify_moduleCat : HasSheafify J (ModuleCat.{w} Λ) :=
  ModuleSheaf.hasSheafify_moduleCat.{w} Λ J

/-- Presheaves of abelian groups admit sheafification. -/
local instance hasSheafify_addCommGrpCat : HasSheafify J AddCommGrpCat.{w} := by
  have h : ∀ Y : C, PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget AddCommGrpCat.{w}) :=
    fun Y => ModuleSheaf.preservesColimitsOfShape_forget_addCommGrp.{w} J Y
  exact HasSheafify.mk' J AddCommGrpCat.{w} (plusPlusAdjunction J AddCommGrpCat.{w})

/-- Postcomposition with `forget₂ (ModuleCat Λ) AddCommGrpCat` commutes with sheafification. -/
local instance preservesSheafification_forget₂ :
    J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
  ModuleSheaf.preservesSheafification_forget₂.{w} Λ J

section Const

omit [UnivLE.{max u v, w}] in
/-- Multiplication by `a : Λ` on the constant presheaf of `Λ`-modules on `E` is, on underlying
abelian groups, the constant presheaf of multiplication by `a` on `E`. -/
public lemma whiskerLeft_smulNatTrans_constComp (E : ModuleCat.{w} Λ) (a : Λ) :
    Functor.whiskerLeft ((Functor.const Cᵒᵖ).obj E) (ModuleCat.smulNatTrans Λ a).asHom ≫
        (Functor.constComp Cᵒᵖ E (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).hom =
      (Functor.constComp Cᵒᵖ E (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).hom ≫
        (Functor.const Cᵒᵖ).map ((ModuleCat.smulNatTrans Λ a).asHom.app E) := by
  ext V
  simp

end Const

section Sheafify

/-- The sheafification of `whiskerLeft_smulNatTrans_constComp`. -/
public lemma sheafifyMap_whiskerLeft_smulNatTrans_constComp (E : ModuleCat.{w} Λ) (a : Λ) :
    sheafifyMap J (Functor.whiskerLeft ((Functor.const Cᵒᵖ).obj E)
          (ModuleCat.smulNatTrans Λ a).asHom) ≫
        sheafifyMap J (Functor.constComp Cᵒᵖ E
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).hom =
      sheafifyMap J (Functor.constComp Cᵒᵖ E
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).hom ≫
        sheafifyMap J ((Functor.const Cᵒᵖ).map ((ModuleCat.smulNatTrans Λ a).asHom.app E)) := by
  rw [← sheafifyMap_comp, ← sheafifyMap_comp, whiskerLeft_smulNatTrans_constComp]

end Sheafify

section Compare

/-- The comparison between sheafifying a presheaf of `Λ`-modules and sheafifying the underlying
presheaf of abelian groups commutes with multiplication by a scalar. -/
public lemma sheafifyComposeIso_hom_whiskerLeft_smulNatTrans (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) (a : Λ) :
    (sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom ≫
        Functor.whiskerLeft (sheafify J P) (ModuleCat.smulNatTrans Λ a).asHom =
      sheafifyMap J (Functor.whiskerLeft P (ModuleCat.smulNatTrans Λ a).asHom) ≫
        (sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom := by
  refine sheafify_hom_ext J _ _ ((sheafCompose J
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj
      ((presheafToSheaf J (ModuleCat.{w} Λ)).obj P)).property ?_
  rw [sheafComposeIso_hom_fac_assoc, ← toSheafify_naturality_assoc, sheafComposeIso_hom_fac]
  exact (Functor.whiskerLeft_comp_whiskerRight (toSheafify J P)
    (ModuleCat.smulNatTrans Λ a).asHom).symm

/-- `sheafifyComposeIso_hom_whiskerLeft_smulNatTrans` read through the inverse of the
comparison. -/
@[reassoc]
public lemma whiskerLeft_smulNatTrans_sheafifyComposeIso_inv (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) (a : Λ) :
    Functor.whiskerLeft (sheafify J P) (ModuleCat.smulNatTrans Λ a).asHom ≫
        (sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).inv =
      (sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).inv ≫
        sheafifyMap J (Functor.whiskerLeft P (ModuleCat.smulNatTrans Λ a).asHom) := by
  rw [Iso.comp_inv_eq, Category.assoc,
    ← sheafifyComposeIso_hom_whiskerLeft_smulNatTrans, Iso.inv_hom_id_assoc]

/-- **The abelian sheaf underlying the constant sheaf of `Λ`-modules is the constant abelian
sheaf.** This is `CategoryTheory.constantCommuteCompose` for the forgetful functor
`forget₂ (ModuleCat Λ) AddCommGrpCat`. -/
public def constantSheafForget₂Iso :
    constantSheaf J (ModuleCat.{w} Λ) ⋙ sheafCompose J (forget₂ (ModuleCat.{w} Λ)
        AddCommGrpCat.{w}) ≅
      forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} ⋙ constantSheaf J AddCommGrpCat.{w} :=
  constantCommuteCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})

/-- The presheaf morphism underlying `constantSheafForget₂Iso`: compare the two sheafifications,
then sheafify the comparison of constant presheaves. -/
public lemma constantSheafForget₂Iso_hom_app_hom (E : ModuleCat.{w} Λ) :
    ((constantSheafForget₂Iso Λ J).hom.app E).hom =
      (sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
          ((Functor.const Cᵒᵖ).obj E)).inv ≫
        sheafifyMap J (Functor.constComp Cᵒᵖ E
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).hom :=
  constantCommuteCompose_hom_app_hom J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) E

/-- Multiplication by `a : Λ` on the abelian sheaf underlying the constant sheaf of `Λ`-modules on
`E` is, at the level of presheaves, multiplication by `a` on the sheafified constant presheaf. -/
public lemma sheafScalarEnd_constantSheaf_hom (E : ModuleCat.{w} Λ) (a : Λ) :
    (sheafScalarEnd Λ J ((constantSheaf J (ModuleCat.{w} Λ)).obj E) a).asHom.hom =
      Functor.whiskerLeft (sheafify J ((Functor.const Cᵒᵖ).obj E))
        (ModuleCat.smulNatTrans Λ a).asHom :=
  rfl

/-- The presheaf morphism underlying the constant abelian sheaf of a morphism of abelian groups. -/
public lemma constantSheaf_map_hom {E₁ E₂ : AddCommGrpCat.{w}} (g : E₁ ⟶ E₂) :
    ((constantSheaf J AddCommGrpCat.{w}).map g).hom =
      sheafifyMap J ((Functor.const Cᵒᵖ).map g) :=
  rfl

/-- The equivariance of `constantSheafForget₂Iso` at the level of presheaves, with both the
comparison and the constant abelian sheaf spelled out as in `constantSheafForget₂Iso_hom_app_hom`,
`sheafScalarEnd_constantSheaf_hom` and `constantSheaf_map_hom`. -/
public lemma whiskerLeft_smulNatTrans_comp_constantComparison (E : ModuleCat.{w} Λ) (a : Λ) :
    Functor.whiskerLeft (sheafify J ((Functor.const Cᵒᵖ).obj E))
          (ModuleCat.smulNatTrans Λ a).asHom ≫
        ((sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
            ((Functor.const Cᵒᵖ).obj E)).inv ≫
          sheafifyMap J (Functor.constComp Cᵒᵖ E
            (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).hom) =
      ((sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
            ((Functor.const Cᵒᵖ).obj E)).inv ≫
          sheafifyMap J (Functor.constComp Cᵒᵖ E
            (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).hom) ≫
        sheafifyMap J ((Functor.const Cᵒᵖ).map ((ModuleCat.smulNatTrans Λ a).asHom.app E)) := by
  simp only [Category.assoc]
  rw [whiskerLeft_smulNatTrans_sheafifyComposeIso_inv_assoc,
    sheafifyMap_whiskerLeft_smulNatTrans_constComp]

/-- **The comparison is `Λ`-equivariant.** It carries multiplication by `a : Λ` on the sections of
the constant sheaf of `Λ`-modules on `E` to the constant abelian sheaf of the morphism of abelian
groups `a • · : E ⟶ E`. -/
public lemma constantSheafForget₂Iso_hom_app_scalar (E : ModuleCat.{w} Λ) (a : Λ) :
    (sheafScalarEnd Λ J ((constantSheaf J (ModuleCat.{w} Λ)).obj E) a).asHom ≫
        (constantSheafForget₂Iso Λ J).hom.app E =
      (constantSheafForget₂Iso Λ J).hom.app E ≫
        (constantSheaf J AddCommGrpCat.{w}).map ((ModuleCat.smulNatTrans Λ a).asHom.app E) :=
  Sheaf.hom_ext (whiskerLeft_smulNatTrans_comp_constantComparison Λ J E a)

end Compare

end Stacks.ModuleCatLift

end
