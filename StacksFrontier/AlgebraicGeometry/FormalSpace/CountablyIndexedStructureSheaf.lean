module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReductionSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSiteCanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningTowerStructureSheafCohomology
import all StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction

/-!
# The structure sheaf of a countably indexed affine formal algebraic space

Let `X = colim Xₙ` be a countably indexed affine formal algebraic space over `S`, presented by a
sequence `X₀ ⟶ X₁ ⟶ ⋯` of affine schemes of the site along thickenings, and let `X_red` be a
reduction of `X`. The reduction of the first stage `X₀` is a reduction of `X` (Stacks 0AIN), so
`X_red` is the affine scheme `V = (X₀)_red`, and `V ⟶ X₀ ⟶ X₁ ⟶ ⋯` is a tower of thickenings.
An affine object `W` of `X_étale` is then an affine scheme étale over `V`, with an étale lift
`Wₙ` to every stage, and the structure sheaf of Stacks 0DEJ is `𝒪_X(W) = lim Γ(Wₙ, 𝒪)`: if
`U ⟶ X` is the affine formal algebraic space étale over `X` with `U_red = W`, then `Wₙ` is
`U ×_X Xₙ` and `U = colim Wₙ` is a presentation of `U`.

This file records that identification of `X_red` with a scheme, and defines the structure sheaf
of `X` on `X_étale` from it.

## Main definitions

* `AlgebraicGeometry.FormalSpace.CountablePresentation`: a presentation of `X` as a sequential
  colimit of affine schemes along thickenings, the datum of Stacks 0AIJ.
* `AlgebraicGeometry.FormalSpace.CountablePresentation.stageReduction`: the reduction of `X₀`,
  as a bundled reduction of `X`.
* `AlgebraicGeometry.FormalSpace.CountablePresentation.reductionIso`: an arbitrary reduction of
  `X` is the presheaf represented by the reduction of `X₀`.
* `AlgebraicGeometry.FormalSpace.CountablePresentation.tower`: the tower of thickenings
  `(X₀)_red ⟶ X₀ ⟶ X₁ ⟶ ⋯`.
* `AlgebraicGeometry.FormalSpace.CountablePresentation.structureSheaf`: the structure sheaf of
  `X`, a sheaf of topological rings on `X_étale`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A presentation of a sheaf on the big fppf site of `S` as the colimit of a sequence of sheaves
represented by affine schemes along thickenings: the datum whose existence is Stacks 0AIJ's
definition of a countably indexed affine formal algebraic space. -/
structure CountablePresentation (X : FppfSheaf B S hS) where
  /-- The sequence of affine stages. -/
  diagram : ℕ ⥤ BigAffineFppf B S hS
  /-- The transition morphisms are thickenings. -/
  isThickening : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
    Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (diagram.map f))
  /-- The sheaf is the colimit of the stages. -/
  iso : X ≅ colimit (diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))

/-- A countably indexed sheaf has a sequential presentation. -/
theorem nonempty_countablePresentation {X : FppfSheaf B S hS}
    (hc : IsCountablyIndexed B S hS X) : Nonempty (CountablePresentation X) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := hc
  exact ⟨⟨D, hD, e⟩⟩

namespace CountablePresentation

variable {X : FppfSheaf B S hS} (P : CountablePresentation X)

/-- The stage `Xₙ` as an object of the big fppf site of `S`. -/
noncomputable abbrev stage (n : ℕ) : BigFppfOver B S hS :=
  (BigAffineFppf.inclusion B S hS).obj (P.diagram.obj n)

/-- The colimit injection `Xₙ ⟶ X`. -/
noncomputable abbrev stageι (n : ℕ) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (P.stage n) ⟶ X :=
  colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) n ≫ P.iso.inv

/-- The reduction `V = (X₀)_red` of the first stage, as an object of the site. -/
noncomputable abbrev reductionObj : BigFppfOver B S hS :=
  siteReduction B S hS (P.stage 0)

/-- The inclusion of `V = (X₀)_red` into `X`. -/
noncomputable abbrev reductionInclusion :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj P.reductionObj ⟶ X :=
  (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
    (siteReductionMap B S hS (P.stage 0)) ≫ P.stageι 0

/-- **Each stage maps to `X` by a representable thickening** (Stacks 0AI9). The presentation is
reindexed by `ULift ℕ`, which lives in the universe of the objects of the site, to apply the
statement there; the reindexing is final, so it does not change the colimit. -/
theorem isThickening_stageι (n : ℕ) :
    MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (P.stageι n) := by
  have hc : Monotone (ULift.down : ULift.{u + 1, 0} ℕ → ℕ) := fun _ _ h ↦ h
  let e := hc.functor
  have : Functor.Final e := hc.final_functor_iff.mpr fun n ↦ ⟨ULift.up n, le_rfl⟩
  let G := P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let iso' : X ≅ colimit ((e ⋙ P.diagram) ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) :=
    P.iso ≪≫ (Functor.Final.colimitIso e G).symm
  have key : colimit.ι ((e ⋙ P.diagram) ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (ULift.up n) ≫ iso'.symm.hom =
      P.stageι n := by
    show colimit.ι (e ⋙ G) (ULift.up n) ≫ (Functor.Final.colimitIso e G).hom ≫ P.iso.inv = _
    rw [← Category.assoc, Functor.Final.ι_colimitIso_hom]
    rfl
  exact key ▸ isThickening_colimitι B S hS (e ⋙ P.diagram)
    (fun ⦃_ _⦄ f ↦ P.isThickening (e.map f)) X iso'.symm (ULift.up n)

/-- **Stacks 0AIN at the first stage.** The reduction of the first stage of a sequential
presentation by thickenings is a reduction of the presented sheaf. -/
theorem isReduction_reductionInclusion :
    IsReduction B S hS X _ P.reductionInclusion := by
  classical
  let JT := BigFppfOver.topology B S hS
  let _ : JT.Subcanonical := bigFppfOver_subcanonical B S hS
  let F := Sheaf.sheafifiedYoneda JT
  let Pr := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have _ : Pr.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have _ : Pr.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  let _ : PreservesLimitsOfShape WalkingCospan F := by
    dsimp [F, Sheaf.sheafifiedYoneda]
    infer_instance
  have hr : MorphismProperty.relative F Pr P.reductionInclusion :=
    MorphismProperty.comp_mem _ _ _
      (MorphismProperty.relative_map
        (isThickening_toScheme_map_siteReductionMap B S hS (P.stage 0))) (P.isThickening_stageι 0)
  have hrU : Space.IsRepresentableThickeningULift.{u + 1} B S hS P.reductionInclusion.hom :=
    relative_uliftYoneda_of_sheafifiedYoneda B S hS Pr hr
  let ε : F ⋙ sheafToPresheaf JT (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
    Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' JT)
        (sheafToPresheaf JT (Type (u + 1))) ≪≫ JT.uliftYonedaCompSheafToPresheaf
  have hatlas : (uliftYoneda.{u + 1}).obj P.reductionObj ≅ (F.obj P.reductionObj).obj :=
    (ε.app P.reductionObj).symm
  refine isReduction_of_isRepresentableThickening B S hS P.reductionInclusion ?_ ?_ hrU
  · exact Space.isAlgebraicSpaceULift_of_iso B S hS hatlas
      (Space.isAlgebraicSpaceULift_uliftYoneda B S hS P.reductionObj)
  · refine ⟨P.reductionObj, hatlas.hom, ?_, ?_,
      isReduced_toScheme_obj_siteReduction B S hS (P.stage 0)⟩ <;>
    exact hasSchemePropertyULift_of_isoSource B S hS _
      (fun _ _ f hf ↦ by have := hf; infer_instance) hatlas

/-- The reduction of the first stage, as a bundled reduction of `X`. -/
noncomputable def stageReduction : Reduction B S hS X where
  space := schemeSpace P.reductionObj
  inclusion := (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS P.reductionObj).hom ≫
    P.reductionInclusion
  isReduction := P.isReduction_reductionInclusion.precomp_iso _

/-- **An arbitrary reduction of `X` is represented by `V = (X₀)_red`.** Two reductions of `X`
are canonically isomorphic, and the reduction of the first stage is the presheaf represented by
`V`. -/
noncomputable def reductionIso (R : Reduction B S hS X) :
    R.space.obj ≅ yoneda.obj P.reductionObj :=
  (ObjectProperty.ι _).mapIso (R.iso P.stageReduction)

/-- The reduction `V = (X₀)_red` of `X` is an affine scheme. -/
theorem isAffine_reductionObj :
    IsAffine ((BigFppfOver.toScheme B S hS).obj P.reductionObj) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (P.stage 0)) :=
    BigAffineFppf.isAffine_toScheme_obj B S hS (P.diagram.obj 0)
  exact isAffine_toScheme_obj_siteReduction B S hS (P.stage 0)

/-- **The tower of thickenings `V = (X₀)_red ⟶ X₀ ⟶ X₁ ⟶ ⋯` of a sequential presentation.** -/
noncomputable def tower : ThickeningTower ((BigFppfOver.toScheme B S hS).obj P.reductionObj) where
  stage := P.diagram ⋙ BigAffineFppf.toScheme B S hS
  ι := (BigFppfOver.toScheme B S hS).map (siteReductionMap B S hS (P.stage 0))
  isThickening_ι := isThickening_toScheme_map_siteReductionMap B S hS (P.stage 0)
  isThickening_succ n := P.isThickening (homOfLE (Nat.le_succ n))

/-- **The structure sheaf of a countably indexed affine formal algebraic space** (Stacks 0DEJ),
on the small étale site `X_étale` of Stacks 0DEA read at a reduction `R` of `X`. On an affine
object `W` of `X_étale` its sections are `lim Γ(Wₙ, 𝒪)`, where `Wₙ` is the étale lift of `W` to
the stage `Xₙ` of the presentation, with the inverse-limit topology of the discrete rings
`Γ(Wₙ, 𝒪)`. -/
noncomputable def structureSheaf (R : Reduction B S hS X) :
    Sheaf R.smallEtaleTopology TopCommRingCat.{u + 1} :=
  Space.towerStructureSheaf (P.reductionIso R) P.tower R.space.property

/-- The structure sheaf of `X` restricted to the affine objects of `X_étale`. -/
noncomputable def structureSheafAffine (R : Reduction B S hS X) :
    Sheaf R.affineEtaleTopology TopCommRingCat.{u + 1} :=
  Space.towerStructureSheafAffine (P.reductionIso R) P.tower R.space.property

/-- **Stacks 0DEL**, for a presented countably indexed affine formal algebraic space: the
structure sheaf `𝒪_X` of `X` has no higher cohomology on `X_étale`,
`Hⁿ(X_étale, 𝒪_X) = 0` for `n > 0`, the cohomology being that of the abelian sheaf underlying
`𝒪_X`. -/
theorem subsingleton_sheafH_structureSheaf.{x} (R : Reduction B S hS X)
    [HasExt.{x} (Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})] (n : ℕ) (hn : 0 < n) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ Space.topCommRingToAddCommGrp).obj (P.structureSheaf R)) n) :=
  Space.subsingleton_sheafH_towerStructureSheaf (P.reductionIso R) P.tower R.space.property
    P.isAffine_reductionObj n hn

end CountablePresentation

end AlgebraicGeometry.FormalSpace

end
