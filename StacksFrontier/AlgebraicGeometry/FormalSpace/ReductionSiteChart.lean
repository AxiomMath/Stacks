module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReductionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReductionSite

/-!
# The reduction of an affine formal algebraic space, as an object of the site

Let `S` be a scheme contained in a big fppf site `B`. The reduction of an *affine* formal
algebraic space `X` over `S` is already available as
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isAffineFormalAlgebraicSpace`, which is
**Stacks 0AIN** in the affine case. The general case needs that reduction in a more explicit
shape: the reduction is the reduced closed subscheme of a *stage* of the presentation, so it is
an object `T` of the big fppf site of `S` whose underlying scheme is both reduced and affine,
and the inclusion is a representable thickening out of `h_T`. The affine statement reports
neither the reducedness nor the affineness of that object, and both are needed — the first to
recognize an étale chart of the glued reduction as reduced, the second to bound its size.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_reduced_affine_thickening_of_isAffineFormal`: a stage
  of the presentation of an affine formal algebraic space, reduced and affine, included by a
  representable thickening.
* `AlgebraicGeometry.FormalSpace.isReduction_yonedaSheaf_of_isRepresentableThickening`: a
  representable thickening out of the sheaf of a *reduced* object of the site exhibits that
  sheaf as a reduction.
* `AlgebraicGeometry.FormalSpace.exists_isReduction_reduced_affine_siteObject_of_isAffineFormal`:
  the two combined — **Stacks 0AIN** in the affine case with the reduction exhibited as a
  reduced affine object of the site.

## Implementation notes

The stage and its thickening into `X` are Stacks 0AI9
(`AlgebraicGeometry.FormalSpace.isThickening_colimitι`), and the reduced closed subscheme of an
object of the site, with its thickening, is
`AlgebraicGeometry.FormalSpace.siteReduction` with
`AlgebraicGeometry.FormalSpace.isThickening_toScheme_map_siteReductionMap`; both are already in
the library, the first in `StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage` and
the second in `StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction`. What is added here
is only the bookkeeping: the two thickenings are composed, the result is transported from the
sheafified Yoneda embedding to the universe-lifted one by
`AlgebraicGeometry.FormalSpace.relative_sheafifiedYoneda_iff_uliftYoneda`, and the reducedness
and affineness of the reduced stage are read off.

That a representable thickening by a reduced algebraic space is a reduction is
`AlgebraicGeometry.FormalSpace.isReduction_of_isRepresentableThickening`; the only thing to
supply is that the sheaf of an object of the site with reduced underlying scheme is a reduced
algebraic space, for which the identity of that object is a surjective étale atlas.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A stage of the presentation of an affine formal algebraic space, reduced and affine,
including into it by a representable thickening.** Let `X` be an affine formal algebraic space
over `S`. There is an object `T` of the big fppf site of `S` with reduced affine underlying
scheme and a morphism `h_T ⟶ X` of fppf sheaves which is a representable thickening.

The object is the reduced closed subscheme of an arbitrary stage of a presentation of `X` by
affine schemes with thickening transition morphisms: the stage includes into `X` by a
representable thickening, by Stacks 0AI9, and the reduced closed subscheme includes into the
stage by a thickening of schemes. -/
theorem exists_reduced_affine_thickening_of_isAffineFormal
    (X : FppfSheaf B S hS) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    ∃ (T : BigFppfOver B S hS) (g : yonedaSheaf B S hS T ⟶ X),
      IsReduced ((BigFppfOver.toScheme B S hS).obj T) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
          Space.IsRepresentableThickeningULift.{u + 1} B S hS g.hom := by
  classical
  obtain ⟨I, pre, hne, hdir, D, hD, ⟨e⟩⟩ := hX.2
  let _ : Preorder I := pre
  let _ : Nonempty I := hne
  let _ : IsDirected I (· ≤ ·) := hdir
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let F := Sheaf.sheafifiedYoneda J
  let P := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let _ : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let _ : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  let _ : PreservesLimitsOfShape WalkingCospan F := by
    dsimp [F, Sheaf.sheafifiedYoneda]
    infer_instance
  let i₀ : I := Classical.arbitrary I
  let T₀ : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (D.obj i₀)
  have hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) :=
    BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj i₀)
  let Tred : BigFppfOver B S hS := siteReduction B S hS T₀
  let r : F.obj Tred ⟶ X :=
    F.map (siteReductionMap B S hS T₀) ≫
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i₀ ≫ e.symm.hom)
  have hr : P.relative F r :=
    MorphismProperty.comp_mem _ _ _
      (MorphismProperty.relative_map
        (isThickening_toScheme_map_siteReductionMap B S hS T₀))
      (isThickening_colimitι B S hS D hD X e.symm i₀)
  exact ⟨Tred, (yonedaSheafIsoSheafifiedYoneda B S hS Tred).hom ≫ r,
    isReduced_toScheme_obj_siteReduction B S hS T₀,
    isAffine_toScheme_obj_siteReduction B S hS T₀,
    (relative_sheafifiedYoneda_iff_uliftYoneda' B S hS P _).mp
      (MorphismProperty.RespectsIso.precomp (P.relative F)
        (yonedaSheafIsoSheafifiedYoneda B S hS Tred).hom r hr)⟩

/-- **An algebraic space étale over an object of the site with reduced underlying scheme is
reduced.** Any atlas of the space is étale over that object, hence has reduced source by Stacks
033B, so it witnesses the étale-local reducedness condition. -/
theorem hasEtaleLocalPropertyULift_isReduced_of_isEtaleULift
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hF : Space.IsAlgebraicSpaceULift.{u + 1} B S hS F) (T : BigFppfOver B S hS)
    (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (f : F ⟶ (uliftYoneda.{u + 1}).obj T)
    (hf : Space.IsEtaleULift.{u + 1} B S hS f) :
    Space.HasEtaleLocalPropertyULift.{u + 1} B S hS F (fun V : Scheme.{u} ↦ IsReduced V) := by
  obtain ⟨V, p, hps, hpe⟩ := hF.exists_atlas
  refine ⟨V, p, hps, hpe, ?_⟩
  let a : V ⟶ T := (uliftYoneda.{u + 1}).preimage (p ≫ f)
  have ha : (uliftYoneda.{u + 1}).map a = p ≫ f := (uliftYoneda.{u + 1}).map_preimage _
  have : Etale ((BigFppfOver.toScheme B S hS).map a) := by
    refine (hf V p hpe).property (𝟙 _) (𝟙 _) a ?_
    simpa only [ha] using IsPullback.of_id_fst (f := p ≫ f)
  exact isReduced_of_smooth ((BigFppfOver.toScheme B S hS).map a)

/-- **A representable thickening out of the sheaf of a reduced object of the site exhibits that
sheaf as a reduction.** The source is an algebraic space, being representable, and it is reduced
because its underlying scheme is; the unique factorization clause is then
`AlgebraicGeometry.FormalSpace.isReduction_of_isRepresentableThickening`. -/
theorem isReduction_yonedaSheaf_of_isRepresentableThickening {X : FppfSheaf B S hS}
    (T : BigFppfOver B S hS) (g : yonedaSheaf B S hS T ⟶ X)
    (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (hg : Space.IsRepresentableThickeningULift.{u + 1} B S hS g.hom) :
    IsReduction B S hS X (yonedaSheaf B S hS T) g :=
  isReduction_of_isRepresentableThickening B S hS g
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T)
    (hasEtaleLocalPropertyULift_isReduced_uliftYoneda B S hS T hT) hg

/-- **Stacks 0AIN for an affine formal algebraic space, with the reduction exhibited as a
reduced affine object of the site.** Let `X` be an affine formal algebraic space over `S`. There
is an object `T` of the big fppf site of `S` whose underlying scheme is reduced and affine and a
morphism `h_T ⟶ X` which is a representable thickening and exhibits `h_T` as a reduction of
`X`. -/
theorem exists_isReduction_reduced_affine_siteObject_of_isAffineFormal
    (X : FppfSheaf B S hS) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    ∃ (T : BigFppfOver B S hS) (g : yonedaSheaf B S hS T ⟶ X),
      IsReduced ((BigFppfOver.toScheme B S hS).obj T) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
          Space.IsRepresentableThickeningULift.{u + 1} B S hS g.hom ∧
            IsReduction B S hS X (yonedaSheaf B S hS T) g := by
  obtain ⟨T, g, hTred, hTaff, hg⟩ :=
    exists_reduced_affine_thickening_of_isAffineFormal B S hS X hX
  exact ⟨T, g, hTred, hTaff, hg,
    isReduction_yonedaSheaf_of_isRepresentableThickening B S hS T g hTred hg⟩

end AlgebraicGeometry.FormalSpace

end
