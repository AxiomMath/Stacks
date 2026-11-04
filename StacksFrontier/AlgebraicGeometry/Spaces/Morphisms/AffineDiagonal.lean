module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affineness of a morphism of algebraic spaces from an affine diagonal

Let `X ⟶ Y ⟶ T` be morphisms of algebraic spaces over a scheme `S`. If `X` is affine over `T`
and the diagonal of `Y ⟶ T` is affine, then `X ⟶ Y` is affine; the same conclusion holds when
`Y` is separated over `T`. In particular a morphism from an affine scheme to an algebraic space
whose absolute diagonal is affine — or which is separated in the absolute sense of Stacks
03BS — is affine.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_isAffineHom_comp_of_isAffineHom_diagonal` and
  `AlgebraicGeometry.Space.isAffineHom_of_isAffineHom_comp_of_isSeparated`: **Stacks 08GB**,
  parts (1) and (2).
* `AlgebraicGeometry.Space.isAffineHom_of_affine_source_of_isAffineHom_diag` and
  `AlgebraicGeometry.Space.isAffineHom_of_affine_source_of_isAbsolutelySeparated`:
  **Stacks 08GB**, parts (3) and (4).
* `AlgebraicGeometry.Space.isAffineHom_of_isAffineHom_relocalizeChart`: affineness of a
  morphism out of a representable presheaf descends along the lower-shriek extension of
  Stacks 03I5 (2).
* `AlgebraicGeometry.Space.isAffineHom_yoneda_map_terminal_from`: over an affine base, the
  structure morphism of an affine object of the site is affine.

## Implementation notes

Parts (1) and (2) are formal. The morphism `f : X ⟶ Y` factors as the graph
`X ⟶ X ×_T Y` followed by the projection `X ×_T Y ⟶ Y`; the projection is a base change of
`X ⟶ T` and the graph is a base change of the diagonal of `Y ⟶ T`, by Mathlib's
`CategoryTheory.Limits.pullback_lift_diagonal_isPullback`, so both are affine by Stacks 03WI
and their composite is affine by Stacks 03WH. Part (2) is part (1) with the diagonal shown
affine by Stacks 07U2, a closed immersion of algebraic spaces being affine. Neither statement
uses the algebraic-space conditions on the three presheaves, so both are stated for arbitrary
morphisms of presheaves on the big fppf site of `S`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Affine.lean`.

Parts (3) and (4) are parts (1) and (2) applied over the terminal scheme `Spec ℤ`, where the
intervening object `T` is a terminal presheaf: over an affine base every affine object of the
site is affine over the base, which is what makes the hypothesis of part (1) available, and
the relative diagonal over a terminal presheaf is the absolute diagonal read through
`CategoryTheory.Limits.prodIsoPullback`.

Passing between the two bases is the lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor` of Stacks 03I5 (2), which is how
`AlgebraicGeometry.Space.viewOverIntegers` and hence the absolute separation axioms of Stacks
03BS are defined. What has to be checked is that affineness comes back down, and that is
`AlgebraicGeometry.Space.isAffineHom_of_isAffineHom_relocalizeChart`: a test object of the
larger base whose structure morphism factors through the smaller one is the extension of a
test object of the smaller base with the *same underlying scheme*
(`AlgebraicGeometry.relocalizeBaseHom`), the representing object produced upstairs therefore
descends with its affineness intact, and the extension reflects Cartesian squares
(`AlgebraicGeometry.isPullback_of_isPullback_relocalizeChart`). This is the same bookkeeping
as in `AlgebraicGeometry.presheaf_relocalizeChart_iff`, of which it is the affine analogue;
it is stated for a morphism out of a representable presheaf, which is all parts (3) and (4)
need and is what lets the two factorizations of the square be compared through the structural
morphism `CategoryTheory.OverShriek.relocalizeToYoneda`.

This file sits downstream of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Affine.lean`, where affineness is defined and
Stacks 03WH is proved, because Stacks 03WI, Stacks 07U2 and the lower-shriek extension are all
downstream of that module.

## References

* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03WH](https://stacks.math.columbia.edu/tag/03WH)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 07U2](https://stacks.math.columbia.edu/tag/07U2)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Parts (1) and (2): an affine diagonal on the intermediate space -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `X ⟶ Y ⟶ T` be morphisms of presheaves on the big fppf site of `S`. If the composite
`X ⟶ T` is affine and the relative diagonal of `Y ⟶ T` is affine, then `X ⟶ Y` is affine. -/
@[stacks 08GB "part (1)"]
theorem isAffineHom_of_isAffineHom_comp_of_isAffineHom_diagonal
    {X Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Y ⟶ T)
    (hfg : IsAffineHom B S hS (f ≫ g))
    (hΔ : IsAffineHom B S hS (pullback.diagonal g)) :
    IsAffineHom B S hS f := by
  have hsnd : IsAffineHom B S hS (pullback.snd (f ≫ g) g) :=
    IsAffineHom.of_isPullback (IsPullback.of_hasPullback (f ≫ g) g) hfg
  have hgraph := IsAffineHom.of_isPullback (pullback_lift_diagonal_isPullback f g) hΔ
  have hcomp := isAffineHom_comp B S hS _ _ hgraph hsnd
  rwa [pullback.lift_snd] at hcomp

/-- Let `X ⟶ Y ⟶ T` be morphisms of presheaves on the big fppf site of `S`. If the composite
`X ⟶ T` is affine and `Y ⟶ T` is separated, then `X ⟶ Y` is affine. -/
@[stacks 08GB "part (2)"]
theorem isAffineHom_of_isAffineHom_comp_of_isSeparated
    {X Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Y ⟶ T)
    (hfg : IsAffineHom B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    IsAffineHom B S hS f :=
  isAffineHom_of_isAffineHom_comp_of_isAffineHom_diagonal B S hS f g hfg
    (isAffineHom_of_isClosedImmersion B S hS _ hg)

/-! ### Affineness over an affine base -/

/-- The Yoneda image of the terminal object is terminal. -/
private noncomputable def isTerminal_yoneda_obj_terminal (C : Type*) [Category C] [HasTerminal C] :
    IsTerminal (yoneda.obj (⊤_ C)) :=
  terminalIsTerminal.isTerminalObj yoneda _

/-- **Over an affine base, the structure morphism of an affine object of the site is affine.**
The base change of `V ⟶ S` along `Z ⟶ S` is the fibre product in the site, whose underlying
scheme is affine because `V`, `Z` and the base are. -/
theorem isAffineHom_yoneda_map_terminal_from
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj (⊤_ (BigFppfOver B S hS))))
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    IsAffineHom B S hS (yoneda.map (terminal.from V)) := by
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  intro Z g
  have hg : g = yoneda.map (terminal.from ((BigAffineFppf.inclusion B S hS).obj Z)) :=
    (isTerminal_yoneda_obj_terminal _).hom_ext _ _
  have hsq : IsPullback
      (pullback.fst (terminal.from V)
        (terminal.from ((BigAffineFppf.inclusion B S hS).obj Z)))
      (pullback.snd (terminal.from V)
        (terminal.from ((BigAffineFppf.inclusion B S hS).obj Z)))
      (terminal.from V)
      (terminal.from ((BigAffineFppf.inclusion B S hS).obj Z)) :=
    IsPullback.of_hasPullback _ _
  have hP : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (Limits.pullback (terminal.from V)
        (terminal.from ((BigAffineFppf.inclusion B S hS).obj Z)))) := by
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hV
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj Z)) := Z.property
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (⊤_ (BigFppfOver B S hS))) := hT
    have _ : _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B S hS).map
          (terminal.from ((BigAffineFppf.inclusion B S hS).obj Z))) :=
      _root_.AlgebraicGeometry.isAffineHom_of_isAffine _
    exact _root_.AlgebraicGeometry.IsAffine.of_isPullback
      (hsq.map (BigFppfOver.toScheme B S hS))
  refine ⟨⟨_, hP⟩, yoneda.map (pullback.fst (terminal.from V) _),
    pullback.snd (terminal.from V) _, ?_⟩
  rw [hg]
  exact hsq.map yoneda

/-! ### Descent of affineness along the lower-shriek extension -/

/-- **Affineness of a morphism out of a representable presheaf descends along the lower-shriek
extension of Stacks 03I5 (2).** A test object over the larger base whose structure morphism
factors through the smaller one has the same underlying scheme as a test object over the
smaller base, so the affine object representing the base change upstairs represents it
downstairs too; the extension reflects Cartesian squares. -/
theorem isAffineHom_of_isAffineHom_relocalizeChart
    (W S' : Scheme.{u}) (hW : B.Contains W) (hS' : B.Contains S')
    (h : B.obj hW ⟶ B.obj hS')
    {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} {U : BigFppfOver B W hW} (a : yoneda.obj U ⟶ F)
    (ha : IsAffineHom B S' hS' (relocalizeChart B W S' hW hS' h a)) :
    IsAffineHom B W hW a := by
  intro Z g
  obtain ⟨W', p', q', hpb⟩ :=
    ha ⟨(Over.map h).obj ((BigAffineFppf.inclusion B W hW).obj Z), Z.property⟩
      (relocalizeChart B W S' hW hS' h g)
  have hp₀ : yoneda.map (yoneda.preimage p') = p' := yoneda.map_preimage p'
  rw [← hp₀] at hpb
  set p₀ := yoneda.preimage p' with hp₀def
  have hbase : p₀ ≫ relocalizeOverHom B W S' hW hS' h U
      = q' ≫ relocalizeOverHom B W S' hW hS' h
        ((BigAffineFppf.inclusion B W hW).obj Z) := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp,
      ← relocalizeChart_comp_relocalizeToYoneda B W S' hW hS' h a,
      ← relocalizeChart_comp_relocalizeToYoneda B W S' hW hS' h g,
      ← Category.assoc, ← Category.assoc, hpb.w]
  have hleft : p₀.left ≫ U.hom
      = q'.left ≫ ((BigAffineFppf.inclusion B W hW).obj Z).hom :=
    congrArg Over.Hom.left hbase
  have hτ : (q'.left ≫ ((BigAffineFppf.inclusion B W hW).obj Z).hom) ≫ h
      = ((BigAffineFppf.inclusion B S' hS').obj W').hom := by
    rw [Category.assoc]
    exact Over.w q'
  set V : BigFppfOver B W hW :=
    Over.mk (q'.left ≫ ((BigAffineFppf.inclusion B W hW).obj Z).hom) with hVdef
  set pV : V ⟶ U := Over.homMk p₀.left hleft with hpVdef
  set qV : V ⟶ (BigAffineFppf.inclusion B W hW).obj Z := Over.homMk q'.left rfl with hqVdef
  set ι := relocalizeBaseHom B W S' hW hS' h hτ with hιdef
  have h1 : ι ≫ (Over.map h).map pV = p₀ := Over.OverMorphism.ext (Category.id_comp _)
  have h2 : ι ≫ (Over.map h).map qV = q' := Over.OverMorphism.ext (Category.id_comp _)
  have hpullS : IsPullback (yoneda.map ((Over.map h).map pV))
      (yoneda.map ((Over.map h).map qV))
      (relocalizeChart B W S' hW hS' h a) (relocalizeChart B W S' hW hS' h g) := by
    refine hpb.of_iso (yoneda.mapIso (asIso ι)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    all_goals simp [← yoneda.map_comp, h1, h2]
  exact ⟨⟨V, W'.property⟩, yoneda.map pV, qV,
    isPullback_of_isPullback_relocalizeChart B W S' hW hS' h hpullS⟩

/-! ### Parts (3) and (4): a morphism from an affine scheme -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A morphism from an affine object of the big fppf site of `S` to a presheaf whose absolute
diagonal, in the sense of Stacks 03BS, is affine is affine. -/
@[stacks 08GB "part (3)", ega "II 1.6.3"]
theorem isAffineHom_of_affine_source_of_isAffineHom_diag
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (X : BigAffineFppf B S hS)
    (f : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj X) ⟶ Y)
    (hΔ : IsAffineHom B (⊤_ Scheme.{u}) hZ (diag (viewOverIntegers B S hS hZ Y))) :
    IsAffineHom B S hS f := by
  set m : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩ with hmdef
  set F := viewOverIntegers B S hS hZ Y with hFdef
  set VZ : BigFppfOver B (⊤_ Scheme.{u}) hZ :=
    (Over.map m).obj ((BigAffineFppf.inclusion B S hS).obj X) with hVZdef
  refine isAffineHom_of_isAffineHom_relocalizeChart B S (⊤_ Scheme.{u}) hS hZ m f ?_
  have hTaff : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      (⊤_ (BigFppfOver B (⊤_ Scheme.{u}) hZ))) := by
    have h0 : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
        (Over.mk (𝟙 (B.obj hZ)))) := by
      show IsAffine (⊤_ Scheme.{u})
      infer_instance
    exact _root_.AlgebraicGeometry.IsAffine.of_isIso
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
        (terminalIsTerminal.uniqueUpToIso Over.mkIdTerminal).hom)
  have hΔ' : IsAffineHom B (⊤_ Scheme.{u}) hZ (pullback.diagonal (terminal.from F)) := by
    have hd : diag F = pullback.diagonal (terminal.from F) ≫ (prodIsoPullback F F).inv := by
      refine prod.hom_ext ?_ ?_ <;> simp
    have hd' : pullback.diagonal (terminal.from F)
        = diag F ≫ (prodIsoPullback F F).hom := by
      rw [hd, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hd']
    exact isAffineHom_comp_iso _ hΔ
  have hXT : IsAffineHom B (⊤_ Scheme.{u}) hZ
      (relocalizeChart B S (⊤_ Scheme.{u}) hS hZ m f ≫ terminal.from F) := by
    have hstruct : relocalizeChart B S (⊤_ Scheme.{u}) hS hZ m f ≫ terminal.from F
        = yoneda.map (terminal.from VZ)
          ≫ (terminalIsTerminal.uniqueUpToIso (isTerminal_yoneda_obj_terminal _)).inv :=
      terminal.hom_ext _ _
    rw [hstruct]
    exact isAffineHom_comp_iso _
      (isAffineHom_yoneda_map_terminal_from B (⊤_ Scheme.{u}) hZ hTaff VZ X.property)
  exact isAffineHom_of_isAffineHom_comp_of_isAffineHom_diagonal B (⊤_ Scheme.{u}) hZ
    (relocalizeChart B S (⊤_ Scheme.{u}) hS hZ m f) (terminal.from F) hXT hΔ'

/-- A morphism from an affine object of the big fppf site of `S` to a separated algebraic space,
in the absolute sense of Stacks 03BS, is affine: its absolute diagonal is a closed immersion,
hence affine by Stacks 07U2. -/
@[stacks 08GB "part (4)", ega "II 1.6.3"]
theorem isAffineHom_of_affine_source_of_isAbsolutelySeparated
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (X : BigAffineFppf B S hS)
    (f : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj X) ⟶ Y)
    (hsep : IsAbsolutelySeparated B S hS hZ Y) :
    IsAffineHom B S hS f :=
  isAffineHom_of_affine_source_of_isAffineHom_diag B S hS hZ X f
    (isAffineHom_of_isClosedImmersion B (⊤_ Scheme.{u}) hZ _ hsep)

end AlgebraicGeometry.Space

end
