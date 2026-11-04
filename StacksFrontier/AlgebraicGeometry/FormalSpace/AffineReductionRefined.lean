module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageThickening
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
import all StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction

/-!
# Affineness of the reduction of an affine formal algebraic space

The reduction of an object of the big fppf site of `S` with affine underlying scheme is again
affine, and an affine formal algebraic space over `S` has a reduction which is the sheaf
represented by an affine object of the site.

## Main results

* `isAffine_toScheme_obj_siteReduction`: the reduction of an object of the site with affine
  underlying scheme has affine underlying scheme.
* `exists_isReduction_isAffine_of_isAffineFormalAlgebraicSpace`: an affine formal algebraic
  space has a reduction represented by an affine object of the site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The reduction of an object of the site -/

/-- The reduction of an object of the big fppf site of `S` whose underlying scheme is affine has
affine underlying scheme itself. -/
theorem isAffine_toScheme_obj_siteReduction (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (siteReduction B S hS T)) := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  have _ : IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (siteReductionMap B S hS T)) :=
    (isThickening_toScheme_map_siteReductionMap B S hS T).1
  exact isAffine_of_isAffineHom
    ((BigFppfOver.toScheme B S hS).map (siteReductionMap B S hS T))

/-! ### The reduction of an affine formal algebraic space -/

/-- An affine formal algebraic space `X` over `S` has a reduction `Xred ⟶ X` such that `Xred` is
the sheaf represented by an object `T` of the site whose underlying scheme is affine.

This is the step of the proof of Stacks 0AIN in the affine case which reads "since the transition
morphisms are thickenings, the affine schemes `X_λ` all have isomorphic reductions `X_red`".
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isAffineFormalAlgebraicSpace` is the
statement of Stacks 0AIN in the affine case and follows from this. -/
theorem exists_isReduction_isAffine_of_isAffineFormalAlgebraicSpace
    (X : FppfSheaf B S hS) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    ∃ (Xred : FppfSheaf B S hS) (i : Xred ⟶ X) (T : BigFppfOver B S hS),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty ((uliftYoneda.{u + 1}).obj T ≅ Xred.obj) ∧
      IsReduction B S hS X Xred i := by
  classical
  obtain ⟨I, pre, hne, hdir, D, hD, ⟨e⟩⟩ := hX.2
  let _ : Preorder I := pre
  let _ : Nonempty I := hne
  let _ : IsDirected I (· ≤ ·) := hdir
  let JT := BigFppfOver.topology B S hS
  let _ : JT.Subcanonical := bigFppfOver_subcanonical B S hS
  let F := Sheaf.sheafifiedYoneda JT
  let P := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let _ : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let _ : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  let _ : F.Full := inferInstance
  let _ : F.Faithful := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan F := by
    dsimp [F, Sheaf.sheafifiedYoneda]
    infer_instance
  let i₀ : I := Classical.arbitrary I
  let T₀ : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (D.obj i₀)
  have hstage : MorphismProperty.relative F P
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i₀ ≫ e.symm.hom) :=
    isThickening_colimitι B S hS D hD X e.symm i₀
  let Tred : BigFppfOver B S hS := siteReduction B S hS T₀
  let r : F.obj Tred ⟶ X :=
    F.map (siteReductionMap B S hS T₀) ≫
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i₀ ≫ e.symm.hom)
  have hr : MorphismProperty.relative F P r :=
    MorphismProperty.comp_mem _ _ _
      (MorphismProperty.relative_map
        (isThickening_toScheme_map_siteReductionMap B S hS T₀)) hstage
  have hrU : Space.IsRepresentableThickeningULift.{u + 1} B S hS r.hom :=
    relative_uliftYoneda_of_sheafifiedYoneda B S hS P hr
  let ε : F ⋙ sheafToPresheaf JT (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
    Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' JT)
        (sheafToPresheaf JT (Type (u + 1))) ≪≫ JT.uliftYonedaCompSheafToPresheaf
  have hatlas : (uliftYoneda.{u + 1}).obj Tred ≅ (F.obj Tred).obj := (ε.app Tred).symm
  refine ⟨F.obj Tred, r, Tred,
    isAffine_toScheme_obj_siteReduction B S hS T₀
      (BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj i₀)),
    ⟨hatlas⟩, isReduction_of_isRepresentableThickening B S hS r ?_ ?_ hrU⟩
  · exact Space.isAlgebraicSpaceULift_of_iso B S hS hatlas
      (Space.isAlgebraicSpaceULift_uliftYoneda B S hS Tred)
  · refine ⟨Tred, hatlas.hom, ?_, ?_, isReduced_toScheme_obj_siteReduction B S hS T₀⟩
    · exact hasSchemePropertyULift_of_isoSource B S hS _
        (fun _ _ f hf ↦ by have := hf; infer_instance) hatlas
    · exact hasSchemePropertyULift_of_isoSource B S hS _
        (fun _ _ f hf ↦ by have := hf; infer_instance) hatlas

end AlgebraicGeometry.FormalSpace

end
