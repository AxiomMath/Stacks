module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsMate

/-!
# The restriction map on sections of a sheaf pullback, read at terminal objects

Global sections of a sheaf of types are written as morphisms out of a terminal sheaf, and the
restriction map `CategoryTheory.sheafPullbackSectionsRestriction` is computed in those terms: it
is inverse image along `b` followed by the canonical comparison `b⁻¹a⁻¹ ≅ c⁻¹` of left
adjoints.

## Main definitions

* `CategoryTheory.Sheaf.terminalHomEquivObj` — morphisms out of a terminal sheaf of types as
  the sections at a terminal object of the site.

## Main results

* `CategoryTheory.sheafPullbackRestrictionAdjunct_eq_leftAdjointCompIso` — the adjunct of
  `CategoryTheory.sheafPullbackRestriction` is `CategoryTheory.Adjunction.leftAdjointCompIso` of
  the comparison of direct images.
* `CategoryTheory.sheafPullbackSectionsRestriction_ΓEquivHomTerminal_symm` — on global sections
  written as morphisms out of a terminal sheaf, the restriction map is inverse image along `b`
  followed by that comparison.

## References

* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

section TerminalHom

variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)
  [HasSheafify K (Type w)] [HasTerminal D] [HasTerminal (Sheaf K (Type w))]

/-- Morphisms out of a terminal sheaf of types are the sections at a terminal object. -/
public def Sheaf.terminalHomEquivObj {T : D} (hT : IsTerminal T) (H : Sheaf K (Type w)) :
    ((⊤_ Sheaf K (Type w)) ⟶ H) ≃ H.obj.obj (op T) :=
  (Sheaf.ΓEquivHomTerminal K H).symm.trans
    ((Sheaf.ΓNatIsoSheafSections K (Type w) hT).app H).toEquiv

/-- `CategoryTheory.Sheaf.terminalHomEquivObj` is natural: postcomposition with a morphism of
sheaves becomes that morphism at the terminal object. -/
public lemma Sheaf.terminalHomEquivObj_comp {T : D} (hT : IsTerminal T)
    {H H' : Sheaf K (Type w)} (φ : (⊤_ Sheaf K (Type w)) ⟶ H) (ρ : H ⟶ H') :
    Sheaf.terminalHomEquivObj K hT H' (φ ≫ ρ) =
      ρ.hom.app (op T) (Sheaf.terminalHomEquivObj K hT H φ) := by
  have h1 : (Sheaf.ΓEquivHomTerminal K H').symm (φ ≫ ρ) =
      (Sheaf.Γ K (Type w)).map ρ ((Sheaf.ΓEquivHomTerminal K H).symm φ) := by
    apply (Sheaf.ΓEquivHomTerminal K H').injective
    rw [Equiv.apply_symm_apply, Sheaf.ΓEquivHomTerminal_naturality, Equiv.apply_symm_apply]
  have h2 := ConcreteCategory.congr_hom
    ((Sheaf.ΓNatIsoSheafSections K (Type w) hT).hom.naturality ρ)
    ((Sheaf.ΓEquivHomTerminal K H).symm φ)
  simp only [Sheaf.terminalHomEquivObj, Equiv.trans_apply, h1]
  exact h2

/-- `CategoryTheory.Sheaf.terminalHomEquivObj` followed back to global sections is the
identification of global sections with morphisms out of a terminal sheaf, whichever terminal
object is used. -/
public lemma Sheaf.ΓNatIsoSheafSections_inv_terminalHomEquivObj {T : D} (hT : IsTerminal T)
    (H : Sheaf K (Type w)) (φ : (⊤_ Sheaf K (Type w)) ⟶ H) :
    (Sheaf.ΓNatIsoSheafSections K (Type w) hT).inv.app H
        (Sheaf.terminalHomEquivObj K hT H φ) = (Sheaf.ΓEquivHomTerminal K H).symm φ := by
  simp [Sheaf.terminalHomEquivObj]

end TerminalHom

section TerminalAdjunct

variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
  (K : GrothendieckTopology D) (L : GrothendieckTopology E) (b : D ⥤ E)
  [b.IsContinuous K L] [(b.sheafPushforwardContinuous (Type w) K L).IsRightAdjoint]
  [HasSheafify K (Type w)] [HasSheafify L (Type w)] [HasTerminal D] [HasTerminal E]
  [HasTerminal (Sheaf K (Type w))] [HasTerminal (Sheaf L (Type w))]

/-- Read at terminal objects, the adjunct of a morphism `⊤ ⟶ b_* H` is that morphism, provided
`b` preserves the terminal object and so does its inverse image. -/
public lemma Sheaf.terminalHomEquivObj_homEquiv_symm {T : D} (hT : IsTerminal T)
    (hbT : IsTerminal (b.obj T))
    (hsub : IsTerminal ((b.sheafPullback (Type w) K L).obj (⊤_ Sheaf K (Type w))))
    {H : Sheaf L (Type w)}
    (k : (⊤_ Sheaf K (Type w)) ⟶ (b.sheafPushforwardContinuous (Type w) K L).obj H)
    (u : (⊤_ Sheaf L (Type w)) ⟶ (b.sheafPullback (Type w) K L).obj (⊤_ Sheaf K (Type w))) :
    Sheaf.terminalHomEquivObj L hbT H
        (u ≫ ((b.sheafAdjunctionContinuous (Type w) K L).homEquiv _ _).symm k) =
      Sheaf.terminalHomEquivObj K hT _ k := by
  set m := ((b.sheafAdjunctionContinuous (Type w) K L).homEquiv _ _).symm k
  have hk : k = (b.sheafAdjunctionContinuous (Type w) K L).unit.app _ ≫
      (b.sheafPushforwardContinuous (Type w) K L).map m :=
    (Equiv.apply_symm_apply _ k).symm.trans
      ((b.sheafAdjunctionContinuous (Type w) K L).homEquiv_unit _ _ m)
  rw [hk, Sheaf.terminalHomEquivObj_comp, Sheaf.terminalHomEquivObj_comp]
  change m.hom.app _ _ = m.hom.app _ _
  congr 1
  exact (Sheaf.terminalHomEquivObj L hbT _).symm.injective (hsub.hom_ext _ _)

end TerminalAdjunct

section TerminalRestriction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (a : C ⥤ D) (b : D ⥤ E) (c : C ⥤ E)
  [a.IsContinuous J K] [b.IsContinuous K L] [c.IsContinuous J L]
  [(a.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [(b.sheafPushforwardContinuous (Type w) K L).IsRightAdjoint]
  [(c.sheafPushforwardContinuous (Type w) J L).IsRightAdjoint]

/-- The adjunct of `CategoryTheory.sheafPullbackRestriction` is the canonical comparison
`b⁻¹a⁻¹ ≅ c⁻¹` of left adjoints, obtained from the comparison of direct images. -/
public lemma sheafPullbackRestrictionAdjunct_eq_leftAdjointCompIso (e : a ⋙ b ≅ c)
    (F : Sheaf J (Type w)) :
    sheafPullbackRestrictionAdjunct J K L a b c e F =
      (Adjunction.leftAdjointCompIso (a.sheafAdjunctionContinuous (Type w) J K)
        (b.sheafAdjunctionContinuous (Type w) K L) (c.sheafAdjunctionContinuous (Type w) J L)
        (Functor.sheafPushforwardContinuousComp' e (Type w) J K L)).hom.app F := by
  apply ((b.sheafAdjunctionContinuous (Type w) K L).homEquiv _ _).injective
  apply ((a.sheafAdjunctionContinuous (Type w) J K).homEquiv _ _).injective
  simp only [sheafPullbackRestrictionAdjunct, Equiv.apply_symm_apply, sheafPullbackRestriction]
  simp [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_unit]

variable [HasSheafify K (Type w)] [HasSheafify L (Type w)] [HasTerminal D] [HasTerminal E]
  [HasTerminal (Sheaf K (Type w))] [HasTerminal (Sheaf L (Type w))]

/-- Read at terminal objects, pulling a global section of `a⁻¹F` back along `b` and comparing
`b⁻¹a⁻¹F` with `c⁻¹F` is `CategoryTheory.sheafPullbackRestriction`. -/
public lemma Sheaf.terminalHomEquivObj_sheafPullbackRestriction (e : a ⋙ b ≅ c)
    (F : Sheaf J (Type w)) {T : D} (hT : IsTerminal T) (hbT : IsTerminal (b.obj T))
    (hsub : IsTerminal ((b.sheafPullback (Type w) K L).obj (⊤_ Sheaf K (Type w))))
    (s : (⊤_ Sheaf K (Type w)) ⟶ (a.sheafPullback (Type w) J K).obj F)
    (u : (⊤_ Sheaf L (Type w)) ⟶ (b.sheafPullback (Type w) K L).obj (⊤_ Sheaf K (Type w))) :
    Sheaf.terminalHomEquivObj L hbT _
        (u ≫ (b.sheafPullback (Type w) K L).map s ≫
          (Adjunction.leftAdjointCompIso (a.sheafAdjunctionContinuous (Type w) J K)
            (b.sheafAdjunctionContinuous (Type w) K L) (c.sheafAdjunctionContinuous (Type w) J L)
            (Functor.sheafPushforwardContinuousComp' e (Type w) J K L)).hom.app F) =
      (sheafPullbackRestriction J K L a b c e F).hom.app (op T)
        (Sheaf.terminalHomEquivObj K hT _ s) := by
  have hadj : (b.sheafPullback (Type w) K L).map s ≫
      (Adjunction.leftAdjointCompIso (a.sheafAdjunctionContinuous (Type w) J K)
        (b.sheafAdjunctionContinuous (Type w) K L) (c.sheafAdjunctionContinuous (Type w) J L)
        (Functor.sheafPushforwardContinuousComp' e (Type w) J K L)).hom.app F =
      ((b.sheafAdjunctionContinuous (Type w) K L).homEquiv _ _).symm
        (s ≫ sheafPullbackRestriction J K L a b c e F) := by
    rw [← sheafPullbackRestrictionAdjunct_eq_leftAdjointCompIso,
      Adjunction.homEquiv_naturality_left_symm]
    rfl
  rw [hadj, Sheaf.terminalHomEquivObj_homEquiv_symm K L b hT hbT hsub,
    Sheaf.terminalHomEquivObj_comp]

/-- `CategoryTheory.sheafPullbackSectionsRestriction`, on global sections written as morphisms
out of a terminal sheaf: pull back along `b` and compare `b⁻¹a⁻¹F` with `c⁻¹F`. -/
public lemma sheafPullbackSectionsRestriction_ΓEquivHomTerminal_symm (e : a ⋙ b ≅ c)
    (F : Sheaf J (Type w)) {T : D} (hT : IsTerminal T) (hbT : IsTerminal (b.obj T))
    (hsub : IsTerminal ((b.sheafPullback (Type w) K L).obj (⊤_ Sheaf K (Type w))))
    (s : (⊤_ Sheaf K (Type w)) ⟶ (a.sheafPullback (Type w) J K).obj F)
    (u : (⊤_ Sheaf L (Type w)) ⟶ (b.sheafPullback (Type w) K L).obj (⊤_ Sheaf K (Type w))) :
    sheafPullbackSectionsRestriction J K L a b c e hT hbT F
        ((Sheaf.ΓEquivHomTerminal K _).symm s) =
      (Sheaf.ΓEquivHomTerminal L _).symm
        (u ≫ (b.sheafPullback (Type w) K L).map s ≫
          (Adjunction.leftAdjointCompIso (a.sheafAdjunctionContinuous (Type w) J K)
            (b.sheafAdjunctionContinuous (Type w) K L) (c.sheafAdjunctionContinuous (Type w) J L)
            (Functor.sheafPushforwardContinuousComp' e (Type w) J K L)).hom.app F) := by
  rw [← Sheaf.ΓNatIsoSheafSections_inv_terminalHomEquivObj K hT,
    ← Sheaf.ΓNatIsoSheafSections_inv_terminalHomEquivObj L hbT,
    Sheaf.terminalHomEquivObj_sheafPullbackRestriction J K L a b c e F hT hbT hsub s u]
  simp only [sheafPullbackSectionsRestriction, ConcreteCategory.comp_apply,
    Iso.inv_hom_id_app_apply]
  rfl

end TerminalRestriction

end CategoryTheory
