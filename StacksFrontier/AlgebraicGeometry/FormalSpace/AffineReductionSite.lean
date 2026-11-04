module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
import all StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction

/-!
# The reduction of an affine formal algebraic space, as an object of the site

Let `S` be a scheme contained in a big fppf site `B` and let `X` be an affine formal algebraic
space over `S`. `StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction` proves **Stacks
0AIN** for `X`: the reduction of any stage of a presentation of `X` is a reduction of `X`. This
file states the same construction with the object of the site retained: the reduction of `X` is
the sheaf of an *affine* object of the big fppf site of `S` with *reduced* underlying scheme,
mapping to `X` by a representable thickening.

## Main results

* `AlgebraicGeometry.FormalSpace.isAffine_toScheme_obj_siteReduction`: the reduction of an
  affine object of the site is affine.
* `AlgebraicGeometry.FormalSpace.exists_siteReduction_of_isAffineFormalAlgebraicSpace`: the
  reduction of an affine formal algebraic space is an affine reduced object of the site.

## Implementation notes

The proof is that of
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isAffineFormalAlgebraicSpace`, stopped
before the object of the site is forgotten. It uses the private helpers of
`StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction` (the stability instances of
thickenings and the transfer of a relative property from the sheafified to the universe-lifted
Yoneda embedding), reached by `import all` rather than duplicated.

## References

* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The reduction of an object of the big fppf site of `S` with affine underlying scheme is
again affine: it is cut out by a closed immersion, and a closed immersion is affine. -/
theorem isAffine_toScheme_obj_siteReduction (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (siteReduction B S hS T)) := by
  have h : IsAffine ((BigFppfOver.toScheme B S hS).obj T).nilradical.subscheme :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).obj T).nilradical.subschemeι
  exact h

/-- **The reduction of an affine formal algebraic space is an affine reduced object of the
site.** Let `X` be an affine formal algebraic space over `S`. Some affine object `T` of the big
fppf site of `S` with reduced underlying scheme maps to `X` by a representable thickening. -/
theorem exists_siteReduction_of_isAffineFormalAlgebraicSpace
    (X : FppfSheaf B S hS) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    ∃ (T : BigFppfOver B S hS)
      (r : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      IsReduced ((BigFppfOver.toScheme B S hS).obj T) ∧
      Space.IsRepresentableThickeningULift.{u + 1} B S hS r.hom := by
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
  -- the stage of the presentation at `i₀` maps to `X` by a representable thickening
  have hstage : MorphismProperty.relative F P
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i₀ ≫ e.symm.hom) :=
    isThickening_colimitι B S hS D hD X e.symm i₀
  -- compose it with the inclusion of the reduction of that stage
  let Tred : BigFppfOver B S hS := siteReduction B S hS T₀
  let r : F.obj Tred ⟶ X :=
    F.map (siteReductionMap B S hS T₀) ≫
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i₀ ≫ e.symm.hom)
  have hr : MorphismProperty.relative F P r :=
    MorphismProperty.comp_mem _ _ _
      (MorphismProperty.relative_map
        (isThickening_toScheme_map_siteReductionMap B S hS T₀)) hstage
  refine ⟨Tred, r, ?_, isReduced_toScheme_obj_siteReduction B S hS T₀,
    relative_uliftYoneda_of_sheafifiedYoneda B S hS P hr⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) :=
    BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj i₀)
  exact isAffine_toScheme_obj_siteReduction B S hS T₀

end AlgebraicGeometry.FormalSpace

end
