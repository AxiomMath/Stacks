module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.InverseImageRepresentedSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTwistStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapTwistRestriction
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.RestrictionOfGlobalSections

/-!
# The self-map twist on pulled back sections

Let `g : X' ⟶ X` be a morphism of schemes, `ψ` an endomorphism of `X'` over `X` (`ψ ≫ g = g`) and
`G` a sheaf of `Λ`-modules on the small étale site of `X`. The twist
`Stacks.EtaleCohomology.selfMapTwist : g⁻¹G ⟶ ψ_* g⁻¹G` induces an action of `ψ` on `Γ(X', g⁻¹G)`.
This file computes it on a global section which, over the final object, is the restriction along a
morphism `t : X' ⟶ g⁻¹U` of the pulled back section `u(a)` of some `a ∈ G(U)`: the result is the
restriction of `u(a)` along any `t'` whose projection to `U` is that of `t` precomposed with `ψ`.

## Main results

* `Stacks.EtaleCohomology.ΓRes_selfMapTwistAction_of_moduleUnitSection` — the computation above.

## Implementation notes

The twist is characterized by `Stacks.EtaleCohomology.unit_comp_map_selfMapTwist`: on pulled back
sections it is restriction along the comparison of the base change along `ψ ≫ g = g` with the
iterated base change. Global sections are read through `CategoryTheory.Sheaf.ΓRes` at the final
object and at the terminal objects used by
`Stacks.EtaleCohomology.etaleModuleGlobalSectionsDirectImageIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {X X' : Scheme.{u}} (g : X' ⟶ X) (ψ : X' ⟶ X') (w : ψ ≫ g = g)

/-- The inverse of the comparison of base change along `ψ ≫ g = g` with the iterated base change,
on first projections. -/
lemma smallEtaleBaseChangeComp'_inv_app_left_fst_fst (U : X.Etale) :
    ((smallEtaleBaseChangeComp' ψ g g w.symm).inv.app U).left ≫ pullback.fst U.hom g =
      pullback.fst ((smallEtaleBaseChange g).obj U).hom ψ ≫ pullback.fst U.hom g := by
  have h := smallEtaleBaseChangeComp'_fst_fst ψ g g w.symm U
  have hi : ((smallEtaleBaseChangeComp' ψ g g w.symm).inv.app U ≫
      (smallEtaleBaseChangeComp' ψ g g w.symm).hom.app U).left = 𝟙 _ := by
    rw [Iso.inv_hom_id_app]
    rfl
  calc ((smallEtaleBaseChangeComp' ψ g g w.symm).inv.app U).left ≫ pullback.fst U.hom g
      = ((smallEtaleBaseChangeComp' ψ g g w.symm).inv.app U).left ≫
          ((smallEtaleBaseChangeComp' ψ g g w.symm).hom.app U).left ≫
            pullback.fst ((smallEtaleBaseChange g).obj U).hom ψ ≫ pullback.fst U.hom g := by
        rw [h]
    _ = ((smallEtaleBaseChangeComp' ψ g g w.symm).inv.app U ≫
          (smallEtaleBaseChangeComp' ψ g g w.symm).hom.app U).left ≫
            pullback.fst ((smallEtaleBaseChange g).obj U).hom ψ ≫ pullback.fst U.hom g :=
        (Category.assoc _ _ _).symm
    _ = _ := by
        rw [hi, Category.id_comp]
        rfl

/-- The first projection of a composite through an iterated base change and the comparison
`(smallEtaleBaseChangeComp' ψ g g _).inv`. -/
lemma smallEtaleBaseChange_comp_inv_left_fst {A B : X'.Etale} (U : X.Etale)
    (m : A ⟶ (smallEtaleBaseChange ψ).obj B) (p : B ⟶ (smallEtaleBaseChange g).obj U) :
    ((m ≫ (smallEtaleBaseChange ψ).map p) ≫
        (smallEtaleBaseChangeComp' ψ g g w.symm).inv.app U).left ≫ pullback.fst U.hom g =
      m.left ≫ pullback.fst B.hom ψ ≫ p.left ≫ pullback.fst U.hom g := by
  have h1 := smallEtaleBaseChangeComp'_inv_app_left_fst_fst g ψ w U
  have h2 := smallEtaleBaseChange_map_left_fst ψ p
  calc ((m ≫ (smallEtaleBaseChange ψ).map p) ≫
        (smallEtaleBaseChangeComp' ψ g g w.symm).inv.app U).left ≫ pullback.fst U.hom g
      = m.left ≫ ((smallEtaleBaseChange ψ).map p).left ≫
          (((smallEtaleBaseChangeComp' ψ g g w.symm).inv.app U).left ≫
            pullback.fst U.hom g) := by
        simp only [Category.assoc]
        rfl
    _ = m.left ≫ (((smallEtaleBaseChange ψ).map p).left ≫
          pullback.fst ((smallEtaleBaseChange g).obj U).hom ψ) ≫ pullback.fst U.hom g :=
        congrArg (m.left ≫ ·) ((congrArg (((smallEtaleBaseChange ψ).map p).left ≫ ·) h1).trans
          (Category.assoc _ _ _).symm)
    _ = m.left ≫ pullback.fst B.hom ψ ≫ p.left ≫ pullback.fst U.hom g :=
        congrArg (m.left ≫ ·) ((congrArg (· ≫ pullback.fst U.hom g) h2).trans
          (Category.assoc _ _ _))

/-- Restricting a section along a composite, elementwise. -/
lemma moduleSheaf_map_comp_op_apply {Y : Scheme.{u}} (H : EtaleModules.{u, 0} Λ Y)
    {A B C : Y.Etale} (a : A ⟶ B) (b : B ⟶ C) (x : H.obj.obj (op C)) :
    H.obj.map (a ≫ b).op x = H.obj.map a.op (H.obj.map b.op x) := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- **The self-map twist on a pulled back section.** Let `ψ` be an endomorphism of `X'` over `X`
(`ψ ≫ g = g`) and let `z` be a global section of `g⁻¹G` whose restriction to the final object is
the restriction of a pulled back section `u(a)`, `a ∈ G(U)`, along `t : X' ⟶ g⁻¹U`. Then the
action of `ψ` on `Γ(X', g⁻¹G)` (global sections of the twist `g⁻¹G ⟶ ψ_* g⁻¹G`, followed by
`Γ(X', ψ_* -) = Γ(X', -)`) carries `z` to the section restricting `u(a)` along any `t'` whose
projection to `U` is that of `t` precomposed with `ψ`. -/
theorem ΓRes_selfMapTwistAction_of_moduleUnitSection (G : EtaleModules.{u, 0} Λ X)
    {U : X.Etale} (a : G.obj.obj (op U))
    (z : (etaleModuleGlobalSections.{u, 0} Λ X').obj ((etaleModuleInverseImage.{u, 0} Λ g).obj G))
    (t t' : Scheme.Etale.mk (𝟙 X') ⟶ (smallEtaleBaseChange g).obj U)
    (hz : ((etaleModuleInverseImage.{u, 0} Λ g).obj G).ΓRes (op (Scheme.Etale.mk (𝟙 X'))) z =
      ((etaleModuleInverseImage.{u, 0} Λ g).obj G).obj.map t.op (moduleUnitSection Λ g G a))
    (ht' : t'.left ≫ pullback.fst U.hom g = ψ ≫ t.left ≫ pullback.fst U.hom g) :
    ((etaleModuleInverseImage.{u, 0} Λ g).obj G).ΓRes (op (Scheme.Etale.mk (𝟙 X')))
        (((etaleModuleGlobalSections.{u, 0} Λ X').map ((selfMapTwist.{u, 0} Λ g ψ w).app G) ≫
          (etaleModuleGlobalSectionsDirectImageIso ψ Λ).hom.app
            ((etaleModuleInverseImage.{u, 0} Λ g).obj G)) z) =
      ((etaleModuleInverseImage.{u, 0} Λ g).obj G).obj.map t'.op (moduleUnitSection Λ g G a) := by
  let H := (etaleModuleInverseImage.{u, 0} Λ g).obj G
  let hT : IsTerminal ((smallEtaleBaseChange ψ).obj (⊤_ X'.Etale)) :=
    IsTerminal.isTerminalObj (smallEtaleBaseChange ψ) _ terminalIsTerminal
  let ΓS := Sheaf.ΓNatIsoSheafSections X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (terminalIsTerminal (C := X'.Etale))
  let ΓY := Sheaf.ΓNatIsoSheafSections X'.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT
  have he : (etaleModuleGlobalSectionsDirectImageIso ψ Λ).hom.app H =
      ΓS.hom.app ((etaleModuleDirectImage.{u, 0} Λ ψ).obj H) ≫ ΓY.inv.app H := rfl
  have hY : ΓY.hom.app H = H.ΓRes (op ((smallEtaleBaseChange ψ).obj (⊤_ X'.Etale))) :=
    Sheaf.ΓNatIsoSheafSections_hom_app_general hT H
  have hS : ΓS.hom.app ((etaleModuleDirectImage.{u, 0} Λ ψ).obj H) =
      ((etaleModuleDirectImage.{u, 0} Λ ψ).obj H).ΓRes (op (⊤_ X'.Etale)) :=
    Sheaf.ΓNatIsoSheafSections_hom_app_general _ _
  let E : X'.Etale := Scheme.Etale.mk (𝟙 X')
  let k : ⊤_ X'.Etale ⟶ E := (isTerminalEtaleMkId X').from _
  let m : E ⟶ (smallEtaleBaseChange ψ).obj (⊤_ X'.Etale) := hT.from E
  have hinv : ∀ x, ΓY.hom.app H (ΓY.inv.app H x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app]
    rfl
  have step1 : ∀ y, H.ΓRes (op ((smallEtaleBaseChange ψ).obj (⊤_ X'.Etale)))
      ((etaleModuleGlobalSectionsDirectImageIso ψ Λ).hom.app H y) =
      ΓS.hom.app ((etaleModuleDirectImage.{u, 0} Λ ψ).obj H) y := fun y => by
    rw [ConcreteCategory.congr_hom he y, ← hY]
    exact hinv _
  have h1 : H.ΓRes (op ((smallEtaleBaseChange ψ).obj (⊤_ X'.Etale)))
      (((etaleModuleGlobalSections.{u, 0} Λ X').map ((selfMapTwist.{u, 0} Λ g ψ w).app G) ≫
          (etaleModuleGlobalSectionsDirectImageIso ψ Λ).hom.app H) z) =
      ((selfMapTwist.{u, 0} Λ g ψ w).app G).hom.app (op (⊤_ X'.Etale))
        (H.ΓRes (op (⊤_ X'.Etale)) z) :=
    (step1 _).trans (by
      rw [hS]
      exact ConcreteCategory.congr_hom
        (Sheaf.ΓRes_naturality ((selfMapTwist.{u, 0} Λ g ψ w).app G) (op (⊤_ X'.Etale))) z)
  have hres : ∀ {A B : X'.Etale} (f : A ⟶ B) (y : (etaleModuleGlobalSections.{u, 0} Λ X').obj H),
      H.ΓRes (op A) y = H.obj.map f.op (H.ΓRes (op B) y) := fun f y =>
    (ConcreteCategory.congr_hom (Sheaf.ΓRes_map H f.op) y).symm
  have h4 := ConcreteCategory.congr_hom
    (((selfMapTwist.{u, 0} Λ g ψ w).app G).hom.naturality (k ≫ t).op)
    (moduleUnitSection Λ g G a)
  have h5 := congrArg (fun φ => φ.hom.app (op U) a)
    (unit_comp_map_selfMapTwist Λ g ψ w G)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h5
  let c := (smallEtaleBaseChangeComp' ψ g g w.symm).inv.app U
  have h5' : ((selfMapTwist.{u, 0} Λ g ψ w).app G).hom.app (op ((smallEtaleBaseChange g).obj U))
      (moduleUnitSection Λ g G a) = H.obj.map c.op (moduleUnitSection Λ g G a) := by
    rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      etaleModuleDirectImageComp_inv_app_hom_app] at h5
  have e1 : ((selfMapTwist.{u, 0} Λ g ψ w).app G).hom.app (op (⊤_ X'.Etale))
      (H.ΓRes (op (⊤_ X'.Etale)) z) =
      H.obj.map ((smallEtaleBaseChange ψ).map (k ≫ t)).op
        (H.obj.map c.op (moduleUnitSection Λ g G a)) := by
    rw [hres k, hz, ← moduleSheaf_map_comp_op_apply, ← h5', ← ConcreteCategory.comp_apply, h4,
      ConcreteCategory.comp_apply]
    rfl
  have hk : k.left = (⊤_ X'.Etale).hom :=
    (Category.comp_id k.left).symm.trans (MorphismProperty.Over.w k)
  have hm : m.left ≫ pullback.snd (⊤_ X'.Etale).hom ψ = 𝟙 X' := smallEtaleBaseChange_w ψ m
  have hmψ : m.left ≫ pullback.fst (⊤_ X'.Etale).hom ψ ≫ k.left = ψ :=
    (congrArg (fun x => m.left ≫ pullback.fst (⊤_ X'.Etale).hom ψ ≫ x) hk).trans
      ((congrArg (m.left ≫ ·) pullback.condition).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ ψ) hm).trans (Category.id_comp ψ))))
  have ht : (m ≫ (smallEtaleBaseChange ψ).map (k ≫ t)) ≫ c = t' := by
    refine smallEtaleBaseChange_hom_ext g ?_
    have e : m.left ≫ pullback.fst (⊤_ X'.Etale).hom ψ ≫ (k ≫ t).left ≫ pullback.fst U.hom g =
        (m.left ≫ pullback.fst (⊤_ X'.Etale).hom ψ ≫ k.left) ≫ t.left ≫ pullback.fst U.hom g := by
      simp only [Category.assoc]
      rfl
    exact (smallEtaleBaseChange_comp_inv_left_fst g ψ w U m (k ≫ t)).trans
      (e.trans ((congrArg (· ≫ t.left ≫ pullback.fst U.hom g) hmψ).trans ht'.symm))
  rw [hres m, h1, e1, ← moduleSheaf_map_comp_op_apply, ← moduleSheaf_map_comp_op_apply, ht]

end Stacks.EtaleCohomology

end
