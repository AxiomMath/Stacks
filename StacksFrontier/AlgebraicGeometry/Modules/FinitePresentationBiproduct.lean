module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationBiproduct

/-!
# A biproduct of finitely presented modules on a scheme is finitely presented

Let `X` be a scheme and let `A` and `B` be `𝒪_X`-modules of finite presentation. Then `A ⊞ B`
is of finite presentation.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.presentationOfLE`: the restriction of a presentation of
  `M|_U` to a smaller open `V ≤ U`.
* `AlgebraicGeometry.Scheme.Modules.overBiprodIso`: the restriction of a biproduct is the
  biproduct of the restrictions.

## Main results

* `AlgebraicGeometry.isFinitePresentation_biprod`: a biproduct of two finitely presented
  modules on a scheme is finitely presented.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits SheafOfModules
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

/-- The restriction of a presentation of `M|_U` to a smaller open `V ≤ U`. -/
noncomputable def presentationOfLE {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (M : X.Modules)
    (P : (M.over U).Presentation) : (M.over V).Presentation := by
  let f : V ⟶ U := homOfLE h
  let F := SheafOfModules.overMap X.ringCatSheaf f
  haveI : PreservesColimitsOfSize.{u, u} F :=
    (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits
  let P' := P.map F (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) f).symm
  let e : F.obj (M.over U) ≅ M.over V :=
    (SheafOfModules.overFunctorMap X.ringCatSheaf f).app M
  exact P'.ofIsIso e.hom

/-- The restriction of a finite presentation to a smaller open is finite. -/
theorem isFinite_presentationOfLE {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (M : X.Modules)
    (P : (M.over U).Presentation) [P.IsFinite] :
    (presentationOfLE h M P).IsFinite := by
  unfold presentationOfLE
  dsimp
  let F := SheafOfModules.overMap X.ringCatSheaf (homOfLE h)
  let P' := P.map F (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) (homOfLE h)).symm
  have : P'.IsFinite :=
    { isFiniteType_generators := by
        change (P.generators.map F
          (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) (homOfLE h)).symm).IsFiniteType
        infer_instance
      isFiniteType_relations := ⟨by
        rw [show P'.relations.I = P.relations.I by simp [P']]
        exact (Presentation.IsFinite.isFiniteType_relations (p := P)).finite⟩ }
  infer_instance

/-- The restriction of a biproduct of two modules to an open is the biproduct of their
restrictions. -/
noncomputable def overBiprodIso {X : Scheme.{u}} (A B : X.Modules) [HasBinaryBiproduct A B]
    (U : X.Opens) : (A ⊞ B).over U ≅ (A.over U) ⊞ (B.over U) := by
  letI : Abelian (SheafOfModules (X.ringCatSheaf.over U)) := inferInstance
  letI : HasBinaryBiproducts (SheafOfModules (X.ringCatSheaf.over U)) :=
    Abelian.hasBinaryBiproducts
  let F := SheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over U))
  have hpc : PreservesColimitsOfSize.{0, 0} F :=
    (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits
  haveI : PreservesColimit (pair A B) F := hpc.preservesColimitsOfShape.preservesColimit
  exact (F.mapIso (biprod.isoCoprod A B)) ≪≫ (PreservesColimitPair.iso F A B).symm ≪≫
    (biprod.isoCoprod (F.obj A) (F.obj B)).symm

end Scheme.Modules

/-- **A biproduct of two finitely presented modules on a scheme is finitely presented.** -/
theorem isFinitePresentation_biprod {X : Scheme.{u}} (A B : X.Modules)
    [A.IsFinitePresentation] [B.IsFinitePresentation] :
    (A ⊞ B).IsFinitePresentation := by
  classical
  obtain ⟨qA, hqA⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData A
  obtain ⟨qB, hqB⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData B
  have hPA (i) : (qA.presentation i).IsFinite := hqA.isFinite_presentation i
  have hPB (i) : (qB.presentation i).IsFinite := hqB.isFinite_presentation i
  let U (ij : qA.I × qB.I) := qA.X ij.1 ⊓ qB.X ij.2
  let P (ij : qA.I × qB.I) :=
    Scheme.Modules.presentationOfLE (inf_le_left : U ij ≤ qA.X ij.1) A (qA.presentation ij.1)
  let Q (ij : qA.I × qB.I) :=
    Scheme.Modules.presentationOfLE (inf_le_right : U ij ≤ qB.X ij.2) B (qB.presentation ij.2)
  have hP (ij) : (P ij).IsFinite := Scheme.Modules.isFinite_presentationOfLE _ _ _
  have hQ (ij) : (Q ij).IsFinite := Scheme.Modules.isFinite_presentationOfLE _ _ _
  let T (ij) := (P ij).biprod (Q ij)
  have hT (ij) : (T ij).IsFinite := Presentation.isFinite_biprod _ _
  let q : (A ⊞ B).QuasicoherentData.{u} :=
    { I := qA.I × qB.I
      X := U
      coversTop := by
        have hA := qA.coversTop
        have hB := qB.coversTop
        rw [Opens.coversTop_iff] at hA hB ⊢
        change (⨆ i, qA.X i) = ⊤ at hA
        change (⨆ i, qB.X i) = ⊤ at hB
        change (⨆ ij : qA.I × qB.I, qA.X ij.1 ⊓ qB.X ij.2) = ⊤
        rw [← iSup_inf_iSup, hA, hB, inf_top_eq]
      presentation ij := (T ij).ofIsIso (Scheme.Modules.overBiprodIso A B (U ij)).inv }
  refine { exists_quasicoherentData := ⟨q, ?_⟩ }
  constructor
  intro ij
  change ((T ij).ofIsIso (Scheme.Modules.overBiprodIso A B (U ij)).inv).IsFinite
  infer_instance

end AlgebraicGeometry

end
