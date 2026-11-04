module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Category.Grp.Preadditive
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantSheafGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact

/-!
# Global sections of abelian sheaves along a morphism of topoi

Let `f : Sh(C) → Sh(D)` be a morphism of topoi of small sites. Global sections are unchanged by
the direct image: `Γ(D, f_* F) = Γ(C, F)` for every abelian sheaf `F` on `C`. This is the
underived identity on which the factorisation `RΓ(C, -) = RΓ(D, -) ∘ Rf_*` of Cohomology on Sites,
Remark 08J6, rests.

For sheaves of sets the identification is
`Stacks.ConstantSheaf.globalSectionsIsoOfAdjunction`. Global sections of an abelian sheaf are, as
a set, the global sections of its underlying sheaf of sets (`CategoryTheory.Sheaf.ΓForgetIso`), and
a natural bijection between the underlying sets of two additive functors to abelian groups is a
natural isomorphism of abelian groups (`AddCommGrpCat.natIsoOfForget`): the sum of two elements is
the image along the codiagonal of an element of the value at a biproduct, which the bijection
respects by naturality.

## Main definitions

* `AddCommGrpCat.natIsoOfForget`: a natural isomorphism of the underlying-set functors of two
  additive functors to abelian groups is a natural isomorphism of the functors.
* `CategoryTheory.Sheaf.ΓForgetIso`: global sections commute with forgetting the group structure.
* `Stacks.Topos.AbelianPushforward.abelianPushforwardΓIso`: `Γ(D, f_* -) ≅ Γ(C, -)` on abelian
  sheaves.

## References

* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace AddCommGrpCat

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]
  (G₁ G₂ : 𝒜 ⥤ AddCommGrpCat.{w}) [G₁.Additive] [G₂.Additive]
  (β : G₁ ⋙ forget AddCommGrpCat ≅ G₂ ⋙ forget AddCommGrpCat)

/-- The component of `β`, as a map of the underlying sets. -/
abbrev natIsoOfForgetFun (F : 𝒜) : G₁.obj F → G₂.obj F := fun t ↦ β.hom.app F t

omit [Preadditive 𝒜] [HasBinaryBiproducts 𝒜] [G₁.Additive] [G₂.Additive] in
/-- The components of `β` are natural. -/
theorem natIsoOfForgetFun_naturality {X Y : 𝒜} (g : X ⟶ Y) (t : G₁.obj X) :
    natIsoOfForgetFun G₁ G₂ β Y (G₁.map g t) = G₂.map g (natIsoOfForgetFun G₁ G₂ β X t) :=
  ConcreteCategory.congr_hom (β.hom.naturality g) t

/-- **A natural bijection between the underlying sets of two additive functors to abelian groups
is additive.** -/
theorem map_add_of_natIso (F : 𝒜) (x y : G₁.obj F) :
    natIsoOfForgetFun G₁ G₂ β F (x + y) =
      natIsoOfForgetFun G₁ G₂ β F x + natIsoOfForgetFun G₁ G₂ β F y := by
  let z : G₁.obj (F ⊞ F) := G₁.map biprod.inl x + G₁.map biprod.inr y
  have key : ∀ p : F ⊞ F ⟶ F,
      G₁.map p z = G₁.map (biprod.inl ≫ p) x + G₁.map (biprod.inr ≫ p) y := by
    intro p
    simp only [z, map_add, Functor.map_comp, ConcreteCategory.comp_apply]
  have hfst : G₁.map biprod.fst z = x := by simp [key]
  have hsnd : G₁.map biprod.snd z = y := by simp [key]
  have h₁ : x + y = G₁.map (biprod.fst + biprod.snd) z := by
    rw [CategoryTheory.Functor.map_add, hom_add_apply, hfst, hsnd]
  rw [h₁, natIsoOfForgetFun_naturality, CategoryTheory.Functor.map_add, hom_add_apply,
    ← natIsoOfForgetFun_naturality, ← natIsoOfForgetFun_naturality, hfst, hsnd]

/-- **A natural bijection between the underlying sets of two additive functors to abelian groups
is a natural isomorphism of the functors.** -/
def natIsoOfForget : G₁ ≅ G₂ :=
  NatIso.ofComponents (fun F ↦ AddEquiv.toAddCommGrpIso
    { toFun := natIsoOfForgetFun G₁ G₂ β F
      invFun := fun t ↦ β.inv.app F t
      left_inv := fun t ↦ ConcreteCategory.congr_hom (β.hom_inv_id_app F) t
      right_inv := fun t ↦ ConcreteCategory.congr_hom (β.inv_hom_id_app F) t
      map_add' := map_add_of_natIso G₁ G₂ β F })
    (fun g ↦ by ext t; exact natIsoOfForgetFun_naturality G₁ G₂ β g t)

end AddCommGrpCat

namespace CategoryTheory.Sheaf

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)

/-- Global sections of abelian sheaves are additive, preserving binary products. -/
instance Γ_additive : (Sheaf.Γ J AddCommGrpCat.{w}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Global sections of abelian sheaves are left exact, being a right adjoint. -/
instance Γ_preservesFiniteLimits : PreservesFiniteLimits (Sheaf.Γ J AddCommGrpCat.{w}) :=
  haveI : PreservesLimitsOfSize.{0, 0} (Sheaf.Γ J AddCommGrpCat.{w}) :=
    (constantSheafΓAdj J AddCommGrpCat.{w}).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- **Global sections of an abelian sheaf, as a set, are the global sections of its underlying
sheaf of sets**: both are limits of the underlying presheaves, and forgetting the group structure
preserves limits. -/
def ΓForgetIso :
    Sheaf.Γ J AddCommGrpCat.{w} ⋙ forget AddCommGrpCat ≅
      sheafCompose J (forget AddCommGrpCat.{w}) ⋙ Sheaf.Γ J (Type w) :=
  Functor.isoWhiskerRight (Sheaf.ΓNatIsoLim J AddCommGrpCat.{w}) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (preservesLimitNatIso (forget AddCommGrpCat.{w})) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl _) _ ≪≫
    (Functor.isoWhiskerLeft (sheafCompose J (forget AddCommGrpCat.{w}))
      (Sheaf.ΓNatIsoLim J (Type w))).symm

end CategoryTheory.Sheaf

namespace Stacks.Topos.AbelianPushforward

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  {D : Type w} [SmallCategory D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

/-- **Global sections are unchanged by the direct image of abelian sheaves** along a morphism of
topoi of small sites: `Γ(D, f_* F) ≅ Γ(C, F)`, naturally in the abelian sheaf `F` (Cohomology on
Sites, Remark 08J6, underived). On underlying sets this is
`Stacks.ConstantSheaf.globalSectionsIsoOfAdjunction`, and a natural bijection between additive
functors to abelian groups is additive. -/
def abelianPushforwardΓIso :
    abelianPushforward J f ⋙ Sheaf.Γ K AddCommGrpCat.{w} ≅ Sheaf.Γ J AddCommGrpCat.{w} :=
  haveI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  AddCommGrpCat.natIsoOfForget _ _
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Sheaf.ΓForgetIso K) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (abelianPushforward_forgetIso J f) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Stacks.ConstantSheaf.globalSectionsIsoOfAdjunction f.adj) ≪≫
      (Sheaf.ΓForgetIso J).symm)

end Stacks.Topos.AbelianPushforward

end
