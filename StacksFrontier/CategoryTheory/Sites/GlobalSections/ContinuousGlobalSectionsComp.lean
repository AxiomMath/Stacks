module

public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ContinuousGlobalSections

/-!
# The restriction of global sections along a chain of two continuous functors

For a continuous functor of sites `u : (C, J) ⟶ (D, K)`,
`Stacks.Sites.globalSectionsAlongContinuousApp` is the restriction map on global sections
`Γ(D, F) ⟶ Γ(C, u⁻¹F)`.  These maps **compose**: for

`u : (C, J) ⟶ (D, K)`, `v : (D, K) ⟶ (E, L)` and `w : (C, J) ⟶ (E, L)` with `u ⋙ v ≅ w`,

restricting a global section of a sheaf on `(E, L)` first along `v` and then along `u` is
restricting it along `w`, once the two restriction functors are identified by Mathlib's
`CategoryTheory.Functor.sheafPushforwardContinuousComp'`.

## Main results

* `CategoryTheory.Sheaf.hom_ext_of_ΓRes` — two maps into the global sections of a sheaf agree
  when they agree after every restriction map.
* `Stacks.Sites.globalSectionsAlongContinuousApp_comp` — the composition law, at a single sheaf.
* `Stacks.Sites.globalSectionsAlongContinuous_comp` — the same as an equality of natural
  transformations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₄ u₄ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Sheaf

/-- **Two maps into the global sections of a sheaf agree as soon as they agree after every
restriction map** `CategoryTheory.Sheaf.ΓRes`. -/
theorem hom_ext_of_ΓRes {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {A : Type u₄} [Category.{v₄} A] [HasWeakSheafify J A] [HasGlobalSectionsFunctor J A]
    {F : Sheaf J A} {X : A} {f g : X ⟶ (Sheaf.Γ J A).obj F}
    (h : ∀ U : Cᵒᵖ, f ≫ F.ΓRes U = g ≫ F.ΓRes U) : f = g :=
  F.isLimitConeΓ.hom_ext h

end CategoryTheory.Sheaf

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {u : C ⥤ D} {v : D ⥤ E} {w : C ⥤ E} (e : u ⋙ v ≅ w)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (A : Type u₄) [Category.{v₄} A]
  [u.IsContinuous J K] [v.IsContinuous K L] [w.IsContinuous J L]
  [HasWeakSheafify J A] [HasWeakSheafify K A] [HasWeakSheafify L A]
  [HasGlobalSectionsFunctor J A] [HasGlobalSectionsFunctor K A] [HasGlobalSectionsFunctor L A]

/-- **The restriction maps on global sections compose.**  Restricting a global section of a sheaf
`F` on `(E, L)` along `v` and then along `u`, and finally transporting along the identification
`u⁻¹v⁻¹F ≅ w⁻¹F` induced by `e : u ⋙ v ≅ w`, is restricting it along `w`. -/
theorem globalSectionsAlongContinuousApp_comp (F : Sheaf L A) :
    globalSectionsAlongContinuousApp v K L A F ≫
        globalSectionsAlongContinuousApp u J K A
          ((v.sheafPushforwardContinuous A K L).obj F) ≫
        (Sheaf.Γ J A).map ((Functor.sheafPushforwardContinuousComp' e A J K L).hom.app F) =
      globalSectionsAlongContinuousApp w J L A F := by
  have : (u ⋙ v).IsContinuous J L := Functor.isContinuous_comp u v J K L
  refine Sheaf.hom_ext_of_ΓRes fun U => ?_
  have hc : (Functor.sheafPushforwardContinuousComp' e A J K L).hom.app F =
      (Functor.sheafPushforwardContinuousNatTrans e.inv A J L).app F := Category.id_comp _
  have h1 : (Sheaf.Γ J A).map ((Functor.sheafPushforwardContinuousNatTrans e.inv A J L).app F) ≫
      ((w.sheafPushforwardContinuous A J L).obj F).ΓRes U =
      ((u.sheafPushforwardContinuous A J K).obj
        ((v.sheafPushforwardContinuous A K L).obj F)).ΓRes U ≫
        F.obj.map ((e.inv.app U.unop).op) :=
    Sheaf.ΓRes_naturality _ U
  rw [globalSectionsAlongContinuousApp_comp_ΓRes, hc, Category.assoc, Category.assoc]
  have h2 := globalSectionsAlongContinuousApp v K L A F ≫=
    globalSectionsAlongContinuousApp u J K A ((v.sheafPushforwardContinuous A K L).obj F) ≫= h1
  have h4 := globalSectionsAlongContinuousApp v K L A F ≫=
    globalSectionsAlongContinuousApp_comp_ΓRes_assoc u J K A
      ((v.sheafPushforwardContinuous A K L).obj F) U (F.obj.map ((e.inv.app U.unop).op))
  have h5 := globalSectionsAlongContinuousApp_comp_ΓRes_assoc v K L A F (u.op.obj U)
    (F.obj.map ((e.inv.app U.unop).op))
  exact h2.trans (h4.trans (h5.trans (F.ΓRes_map ((e.inv.app U.unop).op))))

/-- **The restriction maps on global sections compose**, as an equality of natural
transformations `Γ(E, -) ⟶ w⁻¹ ⋙ Γ(C, -)`. -/
theorem globalSectionsAlongContinuous_comp :
    globalSectionsAlongContinuous v K L A ≫
        (Functor.whiskerLeft (v.sheafPushforwardContinuous A K L)
          (globalSectionsAlongContinuous u J K A)) ≫
        (Functor.whiskerRight (Functor.sheafPushforwardContinuousComp' e A J K L).hom
          (Sheaf.Γ J A)) =
      globalSectionsAlongContinuous w J L A := by
  ext F
  simpa using globalSectionsAlongContinuousApp_comp e J K L A F

end Stacks.Sites

end
