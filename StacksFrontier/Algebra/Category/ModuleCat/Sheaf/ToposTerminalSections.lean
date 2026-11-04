module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback

/-!
# Global sections as morphisms out of the terminal sheaf

A global section of a sheaf of types `E` on a site is a compatible family of sections over all
objects of the site, i.e. an element of `E.obj.sections`. Equivalently it is a morphism of
sheaves `1 ⟶ E` out of the terminal sheaf, because the terminal sheaf is the presheaf whose
sections over every object form a singleton. This file records that bijection, transports it to
the free sheaf of modules of rank one through Mathlib's `SheafOfModules.unitHomEquiv`, and uses
it to show that global sections are preserved by the direct image along a morphism of topoi:
the inverse image of a morphism of topoi preserves finite limits by definition, hence carries
the terminal sheaf to the terminal sheaf, so `Hom(1, f_*E) ≃ Hom(f⁻¹1, E) ≃ Hom(1, E)`.

## Main definitions

* `CategoryTheory.Sheaf.terminalHomEquivSections`: global sections of a sheaf of types are the
  morphisms out of the terminal sheaf.
* `CategoryTheory.Sheaf.unitTerminalHomEquiv`: morphisms out of the free sheaf of modules of
  rank one are the morphisms out of the terminal sheaf into the underlying sheaf of sets.
* `MorphismOfTopoi.inverseImageTerminalIso`: the inverse image of a morphism of topoi carries
  the terminal sheaf to the terminal sheaf.

## Main results

* `MorphismOfTopoi.pushforwardTerminalHomEquiv`: global sections are preserved by the direct
  image along a morphism of topoi, naturally in the sheaf
  (`MorphismOfTopoi.pushforwardTerminalHomEquiv_comp`).

## Implementation notes

Each bijection comes with a single naturality lemma stating its compatibility with composition
on the right.
-/

@[expose] public section

open CategoryTheory Limits

universe w w' v u v' u'

namespace CategoryTheory.Sheaf

section Terminal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The unique section of the terminal sheaf of types over an object of the site. -/
noncomputable def terminalSheafSection (J : GrothendieckTopology C) (X : Cᵒᵖ) :
    (⊤_ (Sheaf J (Type w))).obj.obj X :=
  (default : (sectionsFunctor J X).obj (⊤_ (Sheaf J (Type w))))

/-- Every section of the terminal sheaf of types over `X` is `terminalSheafSection J X`. -/
lemma eq_terminalSheafSection {X : Cᵒᵖ} (p : (⊤_ (Sheaf J (Type w))).obj.obj X) :
    p = terminalSheafSection J X :=
  Subsingleton.elim (α := (sectionsFunctor J X).obj (⊤_ (Sheaf J (Type w)))) p _

/-- The sections of a morphism out of the terminal sheaf are a compatible family. -/
lemma map_terminalSheafSection_app {E : Sheaf J (Type w)} (α : ⊤_ (Sheaf J (Type w)) ⟶ E)
    {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    E.obj.map g (α.hom.app X (terminalSheafSection J X)) =
      α.hom.app Y (terminalSheafSection J Y) := by
  rw [← NatTrans.naturality_apply α.hom g (terminalSheafSection J X)]
  exact congrArg _ (eq_terminalSheafSection _)

/-- Global sections of a sheaf of types are the morphisms out of the terminal sheaf. -/
noncomputable def terminalHomEquivSections (E : Sheaf J (Type w)) :
    (⊤_ (Sheaf J (Type w)) ⟶ E) ≃ E.obj.sections where
  toFun α :=
    ⟨fun X ↦ α.hom.app X (terminalSheafSection J X), fun g ↦ map_terminalSheafSection_app α g⟩
  invFun s := constHom s.1 (fun g ↦ s.2 g)
  left_inv α := hom_ext_sections fun X p ↦ by
    rw [sectionsFunctor_map_constHom]
    exact congrArg _ (eq_terminalSheafSection p).symm
  right_inv _ := rfl

/-- The morphism out of the terminal sheaf attached to a global section `s` is the constant
morphism with components `s`. -/
lemma terminalHomEquivSections_symm_apply (E : Sheaf J (Type w)) (s : E.obj.sections) :
    (terminalHomEquivSections E).symm s = constHom s.1 (fun g ↦ s.2 g) :=
  rfl

/-- `terminalHomEquivSections` is natural: postcomposing a global section with a morphism of
sheaves is the induced map on compatible families. -/
lemma terminalHomEquivSections_symm_comp {E E' : Sheaf J (Type w)} (s : E.obj.sections)
    (m : E ⟶ E') :
    (terminalHomEquivSections E).symm s ≫ m =
      (terminalHomEquivSections E').symm ((Functor.sectionsFunctor Cᵒᵖ).map m.hom s) :=
  rfl

end Terminal

section Unit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w})

/-- Morphisms from the free sheaf of modules of rank one to `M` are the global sections of the
underlying sheaf of sets of `M`, i.e. the morphisms into it from the terminal sheaf. -/
noncomputable def unitTerminalHomEquiv (M : SheafOfModules.{w} R) :
    (SheafOfModules.unit R ⟶ M) ≃ (⊤_ (Sheaf J (Type w)) ⟶ moduleSheaf R M) :=
  (SheafOfModules.unitHomEquiv M).trans (terminalHomEquivSections (moduleSheaf R M)).symm

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- `unitTerminalHomEquiv` is natural in the sheaf of modules. -/
lemma unitTerminalHomEquiv_comp {M N : SheafOfModules.{w} R} (a : SheafOfModules.unit R ⟶ M)
    (p : M ⟶ N) :
    unitTerminalHomEquiv R N (a ≫ p) =
      unitTerminalHomEquiv R M a ≫ (moduleSheafFunctor R).map p := by
  have h : SheafOfModules.unitHomEquiv N (a ≫ p) =
      (Functor.sectionsFunctor Cᵒᵖ).map ((moduleSheafFunctor R).map p).hom
        (SheafOfModules.unitHomEquiv M a) :=
    SheafOfModules.unitHomEquiv_comp_apply a p
  exact (congrArg (terminalHomEquivSections (moduleSheaf R N)).symm h).trans
    (terminalHomEquivSections_symm_comp _ _).symm

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- `unitTerminalHomEquiv` is natural in the sheaf of modules, inverse form. -/
lemma unitTerminalHomEquiv_symm_comp {M N : SheafOfModules.{w} R}
    (c : ⊤_ (Sheaf J (Type w)) ⟶ moduleSheaf R M) (p : M ⟶ N) :
    (unitTerminalHomEquiv R N).symm (c ≫ (moduleSheafFunctor R).map p) =
      (unitTerminalHomEquiv R M).symm c ≫ p :=
  (unitTerminalHomEquiv R N).injective (by
    rw [Equiv.apply_symm_apply, unitTerminalHomEquiv_comp, Equiv.apply_symm_apply])

end Unit

end CategoryTheory.Sheaf

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- The inverse image of a morphism of topoi carries the terminal sheaf to the terminal sheaf. -/
noncomputable def inverseImageTerminalIso :
    g.inverseImage.obj (⊤_ (Sheaf K (Type w'))) ≅ ⊤_ (Sheaf J (Type w)) :=
  haveI := g.preservesFiniteLimits
  PreservesTerminal.iso g.inverseImage

/-- Global sections are preserved by the direct image along a morphism of topoi: morphisms from
the terminal sheaf to `f_*E` correspond, across the adjunction and `inverseImageTerminalIso`, to
morphisms from the terminal sheaf to `E`. -/
noncomputable def pushforwardTerminalHomEquiv (E : Sheaf J (Type w)) :
    (⊤_ (Sheaf K (Type w')) ⟶ g.pushforward.obj E) ≃ (⊤_ (Sheaf J (Type w)) ⟶ E) :=
  (g.adj.homEquiv _ E).symm.trans (inverseImageTerminalIso g).homFromEquiv

/-- `pushforwardTerminalHomEquiv` is natural in the sheaf. -/
lemma pushforwardTerminalHomEquiv_comp {E E' : Sheaf J (Type w)} (m : E ⟶ E')
    (c : ⊤_ (Sheaf K (Type w')) ⟶ g.pushforward.obj E) :
    pushforwardTerminalHomEquiv g E' (c ≫ g.pushforward.map m) =
      pushforwardTerminalHomEquiv g E c ≫ m := by
  dsimp [pushforwardTerminalHomEquiv, Iso.homFromEquiv]
  rw [g.adj.homEquiv_naturality_right_symm, Category.assoc]

end MorphismOfTopoi

end
