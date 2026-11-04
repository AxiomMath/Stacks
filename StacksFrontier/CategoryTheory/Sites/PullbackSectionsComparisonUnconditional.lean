module
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparisonValued
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison
import all StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# PullbackSectionsComparisonUnconditional

Stronger forms of declarations of `StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparison`,
stated as separate declarations beside the ones there: over more general coefficient universes, or
with inputs that are carried there as hypotheses discharged, together with the new results built
on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅ w

namespace CategoryTheory

section Restriction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (a : C ⥤ D) (b : D ⥤ E) (c : C ⥤ E)
  [a.IsContinuous J K] [b.IsContinuous K L] [c.IsContinuous J L]
  [(a.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [(c.sheafPushforwardContinuous (Type w) J L).IsRightAdjoint]

variable [HasTerminal D] [HasTerminal E]
  [HasWeakSheafify K (Type w)] [HasWeakSheafify L (Type w)]

end Restriction

section GlobalSections

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasTerminal C] {A : Type u₅} [Category.{v₅} A] [HasWeakSheafify J A]

end GlobalSections

section Canonical

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {A : Type u₅} [Category.{v₅} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  (a : C ⥤ D) (i : D ⥤ E) (j : C ⥤ E)
  [a.IsContinuous J K] [i.IsContinuous K L] [j.IsContinuous J L]
  [i.IsCocontinuous K L]
  [∀ F : Dᵒᵖ ⥤ A, i.op.HasPointwiseRightKanExtension F]
  (ε : a ⋙ i ⟶ j)

omit [i.IsContinuous K L] in
/-- If each comparison arrow `ε.app U` is initial among the structured arrows over `i.op`, then
the Kan extension comparison is an isomorphism: it is then one of the components of the
pointwise right Kan extension at an initial object. -/
public lemma sheafPushforwardRanComparison_isIso_general
    (hε : ∀ U : C, IsInitial (StructuredArrow.mk (T := i.op) ((ε.app U).op))) :
    IsIso (_root_.CategoryTheory.sheafPushforwardRanComparisonValued (A := A) J K L a i j ε) := by
  have hG (G : Sheaf K A) :
      IsIso ((_root_.CategoryTheory.sheafPushforwardRanComparisonValued (A := A)
        J K L a i j ε).app G) := by
    have hU (U : Cᵒᵖ) :
        IsIso (((_root_.CategoryTheory.sheafPushforwardRanComparisonValued (A := A)
          J K L a i j ε).app G).hom.app U) :=
      (i.op.isPointwiseRightKanExtensionRanCounit G.obj
          (j.op.obj U)).isIso_π_app_of_isInitial
        (StructuredArrow.mk (T := i.op) ((ε.app U.unop).op)) (hε U.unop)
    have : IsIso ((sheafToPresheaf J A).map
        ((_root_.CategoryTheory.sheafPushforwardRanComparisonValued (A := A)
          J K L a i j ε).app G)) :=
      NatIso.isIso_of_isIso_app
        ((_root_.CategoryTheory.sheafPushforwardRanComparisonValued (A := A)
          J K L a i j ε).app G).hom
    exact isIso_of_reflects_iso
      ((_root_.CategoryTheory.sheafPushforwardRanComparisonValued (A := A) J K L a i j ε).app G)
      (sheafToPresheaf J A)
  exact NatIso.isIso_of_isIso_app _

variable (P : Sheaf J A ⥤ Sheaf L A)
  (adjP : P ⊣ j.sheafPushforwardContinuous A J L)
  [(a.sheafPushforwardContinuous A J K).IsRightAdjoint]
  (hε : ∀ U : C, IsInitial (StructuredArrow.mk (T := i.op) ((ε.app U).op)))

/-- Under the initiality hypothesis of `sheafPushforwardRanComparison_isIso_general`, the sheaf
pullback along `a` is the pullback along `j` followed by the direct image along `i`. -/
public def sheafPullbackIsoOfInitialUnconditional :
    a.sheafPullback A J K ≅ P ⋙ i.sheafPushforwardContinuous A K L := by
  let := sheafPushforwardRanComparison_isIso_general (A := A) J K L a i j ε hε
  exact Adjunction.leftAdjointUniq (a.sheafAdjunctionContinuous A J K)
    ((adjP.comp (i.sheafAdjunctionCocontinuous A K L)).ofNatIsoRight
      (asIso (_root_.CategoryTheory.sheafPushforwardRanComparisonValued (A := A) J K L a i j ε)))

end Canonical

section Compatibility

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {H : Type u₄} [Category.{v₄} H]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : GrothendieckTopology E) (M : GrothendieckTopology H)
  (a : C ⥤ D) (b : D ⥤ E) (c : C ⥤ E)
  (i : D ⥤ H) (i' : E ⥤ H) (j : C ⥤ H)
  [a.IsContinuous J K] [b.IsContinuous K L] [c.IsContinuous J L]
  [i.IsContinuous K M] [i'.IsContinuous L M] [j.IsContinuous J M]
  [(a.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [(c.sheafPushforwardContinuous (Type w) J L).IsRightAdjoint]

variable (P : Sheaf J (Type w) ⥤ Sheaf M (Type w))
  (η : 𝟭 (Sheaf J (Type w)) ⟶ P ⋙ j.sheafPushforwardContinuous (Type w) J M)
  (ε : a ⋙ i ⟶ j) (ε' : c ⋙ i' ⟶ j)
  (m : a.sheafPullback (Type w) J K ⟶ P ⋙ i.sheafPushforwardContinuous (Type w) K M)
  (m' : c.sheafPullback (Type w) J L ⟶ P ⋙ i'.sheafPushforwardContinuous (Type w) L M)
  (hm : ∀ F U, ((a.sheafAdjunctionContinuous (Type w) J K).unit.app F).hom.app U ≫
    (m.app F).hom.app (a.op.obj U) = (η.app F).hom.app U ≫
      (P.obj F).obj.map (ε.app U.unop).op)
  (hm' : ∀ F U, ((c.sheafAdjunctionContinuous (Type w) J L).unit.app F).hom.app U ≫
    (m'.app F).hom.app (c.op.obj U) = (η.app F).hom.app U ≫
      (P.obj F).obj.map (ε'.app U.unop).op)

end Compatibility

section SectionsComparison

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {H : Type u₄} [Category.{v₄} H]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : GrothendieckTopology E) (M : GrothendieckTopology H)
  [HasTerminal D] [HasTerminal E]
  [HasWeakSheafify K (Type w)] [HasWeakSheafify L (Type w)]
  (a : C ⥤ D) (b : D ⥤ E) (c : C ⥤ E) (i : D ⥤ H) (i' : E ⥤ H)
  [a.IsContinuous J K] [b.IsContinuous K L] [c.IsContinuous J L]
  [i.IsContinuous K M] [i'.IsContinuous L M]
  [(a.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint]
  [(c.sheafPushforwardContinuous (Type w) J L).IsRightAdjoint]
  (P : Sheaf J (Type w) ⥤ Sheaf M (Type w))

end SectionsComparison

end CategoryTheory
