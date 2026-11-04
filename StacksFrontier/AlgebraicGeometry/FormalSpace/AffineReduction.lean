module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageThickening
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# The reduction of an affine formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`. An affine formal algebraic space `X` over
`S` is the colimit of a directed diagram of affine objects of the site whose transition
morphisms are thickenings. Each stage maps to `X` by a representable thickening, and a
thickening does not change the reduction, so a reduction of `X` is the reduction of any one
stage: the closed subscheme of that stage cut out by the nilradical, which is reduced and whose
inclusion into the stage is a surjective closed immersion. Composing the two thickenings
exhibits that reduced object of the site as a reduction of `X` in the sense of
`AlgebraicGeometry.FormalSpace.IsReduction`, which is the assertion of **Stacks 0AIN** for an
affine formal algebraic space.

## Main definitions

* `AlgebraicGeometry.FormalSpace.siteReduction` is the reduction of an object of the big fppf
  site of `S`, and `AlgebraicGeometry.FormalSpace.siteReductionMap` is its inclusion.

## Main results

* `AlgebraicGeometry.FormalSpace.isThickening_nilradical_subschemeι`: the reduction of a scheme
  includes into it by a thickening.
* `AlgebraicGeometry.FormalSpace.isThickening_toScheme_map_siteReductionMap`: the same for an
  object of the site.
* `AlgebraicGeometry.FormalSpace.exists_isReduction_of_isAffineFormalAlgebraicSpace`:
  **Stacks 0AIN** for an affine formal algebraic space.

## What is assumed

Nothing. The restriction to the affine case is a restriction of the statement, not a hypothesis
left unproved: for a general formal algebraic space the reductions of the members of an étale
covering by affine formal algebraic spaces have to be glued, and the resulting subsheaf of the
space has to be shown to be an algebraic space and to include by a representable thickening.
That gluing is carried out on top of the affine case proved here, in
`StacksFrontier/AlgebraicGeometry/FormalSpace/GeneralReduction.lean`, which proves Stacks 0AIN for
a general formal algebraic space.

## Implementation notes

The reduction is delivered as an existence statement, as in the source, rather than as a
construction: `AlgebraicGeometry.FormalSpace.IsReduction` is the predicate naming the defining
properties of a reduction and the conclusion is that some morphism has them, so no reduction is
chosen. The stage used is an arbitrary member of the presentation, picked inside the proof of a
proposition.

That the inclusion of a reduced algebraic space by a representable thickening already forces
the unique factorization clause is
`AlgebraicGeometry.FormalSpace.isReduction_of_isRepresentableThickening`; what is supplied here
is that the composite stage morphism is representable and a thickening after every represented
base change, and that its source is a reduced algebraic space.

Two universe levels of representability occur. The stage statements for an affine formal
algebraic space are relative to the sheafified Yoneda embedding, whereas the properties of a
morphism of formal algebraic spaces are relative to the universe-lifted Yoneda embedding into
presheaves, because a formal algebraic space is a sheaf of `Type (u + 1)`. On a subcanonical
site the two embeddings agree after composing with the inclusion of sheaves into presheaves,
and the private helper moving a relative property across that identification duplicates, at
file scope, the one `StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumReduction`
declares privately; it is private there, hence not importable.

The reduction of an object of the site is the closed subscheme cut out by the nilradical ideal
sheaf of its underlying scheme. It is again an object of the site because a closed immersion
does not increase the size of a scheme, Stacks 000R (4), and it carries the structure morphism
obtained by composing that closed immersion with the one of the ambient object.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stability properties of thickenings -/

/-- Thickenings of schemes respect isomorphisms of arrows, being the conjunction of two
properties that do. -/
private instance respectsIso_isThickening : MorphismProperty.RespectsIso
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) := by
  rw [isThickening_eq_inf]
  exact MorphismProperty.RespectsIso.inf _ _

/-- Thickenings of schemes are stable under composition, closed immersions and surjective
morphisms both being so. -/
private instance isStableUnderComposition_isThickening :
    MorphismProperty.IsStableUnderComposition
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) := by
  rw [isThickening_eq_inf]
  let _ : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let _ : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact MorphismProperty.IsStableUnderComposition.inf

/-- Thickenings of schemes are stable under base change along a morphism of the big fppf site
of `S`, since that site's structure functor to schemes preserves fibre products. -/
private instance isStableUnderBaseChange_inverseImage_isThickening :
    (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
  refine ⟨?_⟩
  intro X₁ X₂ Y₂ X₃ f g f' g' hs hg
  exact isThickening_isStableUnderBaseChange.of_isPullback
    (hs.map (BigFppfOver.toScheme B S hS)) hg

/-! ### The reduction of an object of the site -/

/-- The reduction of a scheme includes into it by a thickening: the closed immersion cut out by
the nilradical ideal sheaf is surjective, that ideal sheaf being supported everywhere. -/
theorem isThickening_nilradical_subschemeι (T : Scheme.{u}) :
    Stacks.Thickenings.IsThickening T.nilradical.subschemeι := by
  refine ⟨inferInstance, ?_⟩
  rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
    Scheme.support_nilradical, TopologicalSpace.Closeds.coe_top]

/-- **Stacks 000R (4)** for the reduction: the reduction of the underlying scheme of an object
of the big fppf site of `S` is again contained in that site, being a closed subscheme of a
contained scheme. -/
theorem contains_nilradical_subscheme_toScheme_obj (T : BigFppfOver B S hS) :
    B.Contains ((BigFppfOver.toScheme B S hS).obj T).nilradical.subscheme :=
  Scheme.size_lt_of_isClosedImmersion
    ((BigFppfOver.toScheme B S hS).obj T).nilradical.subschemeι T.left.property

/-- The closed immersion cutting out the reduction of the underlying scheme of an object of the
big fppf site of `S`, read in that site's category of schemes. -/
noncomputable def siteReductionHom (T : BigFppfOver B S hS) :
    B.obj (contains_nilradical_subscheme_toScheme_obj B S hS T) ⟶ T.left :=
  B.inclusion.preimage
    (show B.inclusion.obj (B.obj (contains_nilradical_subscheme_toScheme_obj B S hS T)) ⟶
      B.inclusion.obj T.left from
      ((BigFppfOver.toScheme B S hS).obj T).nilradical.subschemeι)

/-- The reduction of an object of the big fppf site of `S`: the closed subscheme of its
underlying scheme cut out by the nilradical, with the induced structure morphism to `S`. -/
noncomputable def siteReduction (T : BigFppfOver B S hS) : BigFppfOver B S hS :=
  Over.mk (siteReductionHom B S hS T ≫ T.hom)

/-- The inclusion of the reduction of an object of the big fppf site of `S`. -/
noncomputable def siteReductionMap (T : BigFppfOver B S hS) :
    siteReduction B S hS T ⟶ T :=
  Over.homMk (siteReductionHom B S hS T)

/-- The underlying scheme of the reduction of an object of the big fppf site of `S` is
reduced. -/
theorem isReduced_toScheme_obj_siteReduction (T : BigFppfOver B S hS) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj (siteReduction B S hS T)) :=
  isReduced_nilradical_subscheme ((BigFppfOver.toScheme B S hS).obj T)

/-- The inclusion of the reduction of an object of the big fppf site of `S` is a thickening of
the underlying schemes. -/
theorem isThickening_toScheme_map_siteReductionMap (T : BigFppfOver B S hS) :
    Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (siteReductionMap B S hS T)) := by
  have hmap : (BigFppfOver.toScheme B S hS).map (siteReductionMap B S hS T)
      = ((BigFppfOver.toScheme B S hS).obj T).nilradical.subschemeι :=
    B.inclusion.map_preimage _
  rw [hmap]
  exact isThickening_nilradical_subschemeι _

/-! ### Two transfers of a relative morphism property -/

/-- An isomorphism of presheaves out of a universe-lifted Yoneda presheaf has every relative
property of morphisms of schemes which holds for isomorphisms: a base change of an isomorphism
is an isomorphism, and the Yoneda embedding reflects them. -/
private theorem hasSchemePropertyULift_of_isoSource
    (Q : MorphismProperty Scheme.{u})
    (hQ : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), IsIso f → Q f)
    {T : BigFppfOver B S hS} {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (e : (uliftYoneda.{u + 1}).obj T ≅ G) :
    Space.HasSchemePropertyULift.{u + 1} B S hS Q e.hom := by
  refine ⟨Functor.relativelyRepresentable.of_isIso (uliftYoneda.{u + 1}) e.hom, ?_⟩
  intro a b g fst snd hpb
  have : IsIso ((uliftYoneda.{u + 1}).map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd :=
    Functor.FullyFaithful.isIso_of_isIso_map (ULiftYoneda.fullyFaithful _) snd
  show Q ((BigFppfOver.toScheme B S hS).map snd)
  exact hQ _ (Functor.map_isIso _ snd)

/-- On the subcanonical big fppf site, the sheafified Yoneda embedding agrees with the
universe-lifted Yoneda embedding after including sheaves into presheaves. -/
private noncomputable def sheafifiedYonedaCompSheafToPresheafIso :
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) ⋙
        sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS))
      (sheafToPresheaf _ (Type (u + 1))) ≪≫
    (BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf

/-- A relative property of a morphism of fppf sheaves relative to the sheafified Yoneda
embedding holds relative to the universe-lifted Yoneda embedding of presheaves: the site being
subcanonical the two embeddings agree after including sheaves into presheaves, a scheme-valued
point of the target lifts to the sheaf level along that identification, and the inclusion of
sheaves into presheaves carries the resulting cartesian square to a cartesian square of
presheaves. -/
private theorem relative_uliftYoneda_of_sheafifiedYoneda
    (P : MorphismProperty (BigFppfOver B S hS)) [P.RespectsIso]
    {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) P f) :
    MorphismProperty.relative (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)) P f.hom := by
  let JT := BigFppfOver.topology B S hS
  let _ : JT.Subcanonical := bigFppfOver_subcanonical B S hS
  let ε := sheafifiedYonedaCompSheafToPresheafIso B S hS
  apply MorphismProperty.relative.of_exists
  intro a g
  let g' : (Sheaf.sheafifiedYoneda JT).obj a ⟶ Y := ⟨(ε.app a).hom ≫ g⟩
  obtain ⟨b, snd, fst, sq⟩ := h.rep g'
  refine ⟨b, (ε.app b).inv ≫ fst.hom, snd, ?_, h.property g' fst snd sq⟩
  exact (sq.map (sheafToPresheaf JT (Type (u + 1)))).of_iso
    (ε.app b) (Iso.refl _) (ε.app a) (Iso.refl _)
    (by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Iso.refl_hom,
      Category.comp_id]; rfl)
    (ε.hom.naturality snd) (by simp) (by simp [g'])

/-! ### The reduction of an affine formal algebraic space -/

/-- **Stacks 0AIN** for an affine formal algebraic space, with the reduction exhibited as an
object of the site. Let `X` be an affine formal algebraic space over `S`. There is an object
`T` of the big fppf site of `S` with quasi-compact underlying scheme, a reduced algebraic space
`Xred` isomorphic to the universe-lifted Yoneda presheaf of `T`, and a representable morphism
`Xred ⟶ X` which is a thickening and through which every morphism to `X` from a reduced
algebraic space factors uniquely.

The object `T` is the reduction of a stage of the presentation of `X`, a closed subscheme of an
affine scheme, hence quasi-compact. Recording it is what makes a reduction of an affine formal
algebraic space a quasi-compact algebraic space. -/
theorem exists_isReduction_uliftYoneda_of_isAffineFormalAlgebraicSpace
    (X : FppfSheaf B S hS) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    ∃ (T : BigFppfOver B S hS) (Xred : FppfSheaf B S hS) (i : Xred ⟶ X),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj T : Type u) ∧
        Nonempty ((uliftYoneda.{u + 1}).obj T ≅ Xred.obj) ∧
          IsReduction B S hS X Xred i := by
  classical
  obtain ⟨I, _, _, _, D, hD, ⟨e⟩⟩ := hX.2
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
  have hrU : Space.IsRepresentableThickeningULift.{u + 1} B S hS r.hom :=
    relative_uliftYoneda_of_sheafifiedYoneda B S hS P hr
  -- the reduced stage is the sheaf of a reduced object of the site, hence is a reduced
  -- algebraic space
  have hatlas : (uliftYoneda.{u + 1}).obj Tred ≅ (F.obj Tred).obj :=
    ((sheafifiedYonedaCompSheafToPresheafIso B S hS).app Tred).symm
  -- the stage is affine, hence quasi-compact, and a closed immersion into a quasi-compact
  -- scheme has quasi-compact source
  have hcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj Tred : Type u) := by
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) := (D.obj i₀).property
    have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj T₀ : Type u) :=
      Scheme.compactSpace_of_isAffine _
    have := (isThickening_toScheme_map_siteReductionMap B S hS T₀).1
    exact QuasiCompact.compactSpace_of_compactSpace
      ((BigFppfOver.toScheme B S hS).map (siteReductionMap B S hS T₀))
  refine ⟨Tred, F.obj Tred, r, hcompact, ⟨hatlas⟩,
    isReduction_of_isRepresentableThickening B S hS r ?_ ?_ hrU⟩
  · exact Space.isAlgebraicSpaceULift_of_iso B S hS hatlas
      (Space.isAlgebraicSpaceULift_uliftYoneda B S hS Tred)
  · refine ⟨Tred, hatlas.hom, ?_, ?_, isReduced_toScheme_obj_siteReduction B S hS T₀⟩ <;>
      exact hasSchemePropertyULift_of_isoSource B S hS _
        (fun _ _ f hf ↦ by have := hf; infer_instance) hatlas

/-- **Stacks 0AIN** for an affine formal algebraic space. Let `X` be an affine formal algebraic
space over `S`. There is a reduced algebraic space `Xred` and a representable morphism
`Xred ⟶ X` which is a thickening and through which every morphism to `X` from a reduced
algebraic space factors uniquely. -/
@[stacks 0AIN "affine formal algebraic spaces"]
theorem exists_isReduction_of_isAffineFormalAlgebraicSpace
    (X : FppfSheaf B S hS) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    ∃ (Xred : FppfSheaf B S hS) (i : Xred ⟶ X), IsReduction B S hS X Xred i := by
  obtain ⟨-, Xred, i, -, -, hi⟩ :=
    exists_isReduction_uliftYoneda_of_isAffineFormalAlgebraicSpace B S hS X hX
  exact ⟨Xred, i, hi⟩

end AlgebraicGeometry.FormalSpace

end
