module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanCriterion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanCriterionPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSetTheoretic

/-!
# A closed subscheme of the completion of an affine scheme is a closed subscheme of it

Let `S` be a scheme contained in a big fppf site `B`, let `Spec A` be an affine scheme of that
site over `S` and let `T` be a closed set of points of `Spec A`. The completion `Spec A_{/T}`
is an affine formal algebraic space (**Stacks 0AIY**) presented by the quotients `Spec (A ⧸ J)`
over the ideals `J` with `V(J) = T`. Each of those quotient stages is a *closed subscheme* of
`Spec A`, so a scheme of the site closed-immersed in `Spec A_{/T}` is closed-immersed in
`Spec A`.

This is the affine core of clause (2) of **Stacks 0GVV**: the source's step writing a McQuillan
`X` as `Spf(A)` and observing that `X_{/T} ⟶ X ⟶ Spec(A)` satisfies condition (2) of
Stacks 0AIC rests on exactly this, since condition (2) quantifies over the closed immersions of
affine schemes into `X_{/T}`.

## Main results

* `AlgebraicGeometry.FormalSpace.isClosedImmersionInto_comp_completionSheafInclusion_affineOver`:
  a closed immersion of an object of the site into `Spec A_{/T}`, followed by the inclusion of
  `Spec A_{/T}` into `Spec A`, is a closed immersion.

## Implementation notes

The quotient stage `Spec (A ⧸ J)` maps into the completion by
`AlgebraicGeometry.FormalSpace.supportStageToCompletion`, defined through Yoneda's lemma for
sheaves from the section of the completion given by the quotient morphism
`Spec (A ⧸ J) ⟶ Spec A`. That the triangle *stage → completion → `Spec A`* commutes is the
private `sectionEquiv_supportStageToCompletion_comp_inclusion`, proved on sections exactly as
`AlgebraicGeometry.FormalSpace.completionComparison_overAffine` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum` is.

The ambient object of the triangle is the fppf sheafification
`AlgebraicGeometry.Space.sheafifiedULift` of the universe lift of the represented presheaf,
which is the target of `AlgebraicGeometry.Space.completionSheafInclusion`, whereas the stages
map in through `CategoryTheory.Sheaf.sheafifiedYoneda`. Those two sheafifications of one
presheaf are compared by `CategoryTheory.plusPlusSheafIsoPresheafToSheaf`; the comparison is
needed because `CategoryTheory.presheafToSheaf` is an arbitrary chosen left adjoint and does
not unfold to the `plusPlus` construction that `AlgebraicGeometry.Space.sheafifiedULift` uses.

Closedness of `T` enters once, to replace the set of points by the points supported on the
zero locus of an ideal, which is the shape Stacks 0AIY presents the completion in.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIY](https://stacks.math.columbia.edu/tag/0AIY)
* [Stacks Project, Tag 0GVV](https://stacks.math.columbia.edu/tag/0GVV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private theorem sectionEquiv_eq_toSheafify {X : BigFppfOver B S hS} {F : FppfSheaf B S hS}
    (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj X ⟶ F) :
    Sheaf.sectionEquiv (BigFppfOver.topology B S hS) α =
      (toSheafify (BigFppfOver.topology B S hS) (yoneda.obj X ⋙ uliftFunctor.{u + 1}) ≫
        α.hom).app (op X) ⟨𝟙 X⟩ := rfl

/-- The fppf sheafification of the universe lift of the presheaf represented by an object `V`
of the site is the fppf sheaf represented by `V`: both are sheafifications of one presheaf,
compared by `CategoryTheory.plusPlusSheafIsoPresheafToSheaf`. -/
private def sheafifiedULiftIsoRepresented (V : BigFppfOver B S hS) :
    Space.sheafifiedULift B S hS (yoneda.obj V) ≅
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V :=
  (plusPlusSheafIsoPresheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).app
    (yoneda.obj V ⋙ uliftFunctor.{u + 1})

private theorem toSheafify_comp_sheafifiedULiftIsoRepresented_inv (V : BigFppfOver B S hS) :
    toSheafify (BigFppfOver.topology B S hS) (yoneda.obj V ⋙ uliftFunctor.{u + 1}) ≫
        (sheafifiedULiftIsoRepresented B S hS V).inv.hom =
      (BigFppfOver.topology B S hS).toSheafify (yoneda.obj V ⋙ uliftFunctor.{u + 1}) :=
  (Iso.comp_inv_eq ((sheafToPresheaf (BigFppfOver.topology B S hS)
    (Type (u + 1))).mapIso (sheafifiedULiftIsoRepresented B S hS V))).mpr
      (toSheafify_plusPlusIsoSheafify_hom (BigFppfOver.topology B S hS) (Type (u + 1))
        (yoneda.obj V ⋙ uliftFunctor.{u + 1})).symm

private theorem sectionEquiv_sheafifiedULiftIsoRepresented_inv (V : BigFppfOver B S hS) :
    Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (sheafifiedULiftIsoRepresented B S hS V).inv =
      ((BigFppfOver.topology B S hS).toSheafify
        (yoneda.obj V ⋙ uliftFunctor.{u + 1})).app (op V) ⟨𝟙 V⟩ := by
  rw [sectionEquiv_eq_toSheafify B S hS,
    toSheafify_comp_sheafifiedULiftIsoRepresented_inv B S hS V]
  rfl

section Affine

variable {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S)
  (I : Ideal A)

/-- On each quotient stage of the completion of `Spec A` along `V(I)`, the morphism into the
completion followed by the inclusion of the completion into `Spec A` is the section given by
the morphism `Spec (A ⧸ K) ⟶ Spec A`. -/
private theorem sectionEquiv_supportStageToCompletion_comp_inclusion (K : SupportIdeal I) :
    Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      (supportStageToCompletion B S hS hA f I K ≫
        Space.completionSheafInclusion B S hS (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I)) =
      ((BigFppfOver.topology B S hS).toSheafify
        (yoneda.obj (affineOver B S hS hA f) ⋙ uliftFunctor.{u + 1})).app
          (op ((BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I K)))
          ⟨supportStageToAffine B S hS hA f I K⟩ := by
  have hsec : Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (supportStageToCompletion B S hS hA f I K) =
      supportStageSection B S hS hA f I K :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (X := (BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I K))
        (F := Space.completionSheaf B S hS
          (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I))).apply_symm_apply
      (supportStageSection B S hS hA f I K)
  refine Eq.trans ((Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS)
      (supportStageToCompletion B S hS hA f I K)
      (Space.completionSheafInclusion B S hS (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I))).trans
    (congrArg (fun s => (Space.completionSheafInclusion B S hS
        (yoneda.obj (affineOver B S hS hA f))
        (zeroLocusPoints B S hS hA f I)).hom.app
      (op ((BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I K))) s) hsec)) ?_
  let C := Space.completionSubfunctor B S hS
    (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I)
  let U := (BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I K)
  let x : C.toFunctor.obj (op U) :=
    ⟨ULift.up (supportStageToAffine B S hS hA f I K),
      supportStage_hasImageIn B S hS hA f I K⟩
  show ((BigFppfOver.topology B S hS).sheafifyMap C.ι).app (op U)
      ((GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS) C.toFunctor).app
        (op U) x) =
    (GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
      (yoneda.obj (affineOver B S hS hA f) ⋙ uliftFunctor.{u + 1})).app
        (op U) (ULift.up (supportStageToAffine B S hS hA f I K))
  let ηC := GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS) C.toFunctor
  let ηX := GrothendieckTopology.toSheafify (BigFppfOver.topology B S hS)
    (yoneda.obj (affineOver B S hS hA f) ⋙ uliftFunctor.{u + 1})
  let φ := (BigFppfOver.topology B S hS).sheafifyMap C.ι
  calc
    _ = ((ηC ≫ φ).app (op U)) x := by simp [ηC, φ]
    _ = ((C.ι ≫ ηX).app (op U)) x := by
      have hη := congrArg (fun η => η.app (op U))
        (GrothendieckTopology.toSheafify_naturality (BigFppfOver.topology B S hS) C.ι).symm
      simpa [ηC, ηX, φ, C, x] using congrArg (fun g => g x) hη
    _ = _ := by rfl

/-- The morphism `Spec (A ⧸ K) ⟶ Spec A` of a quotient stage of the completion of `Spec A`
along `V(I)` is a closed immersion of schemes. -/
private theorem isClosedImmersion_supportStageToAffine (K : SupportIdeal I) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (supportStageToAffine B S hS hA f I K)) := by
  show _root_.AlgebraicGeometry.IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)))
  exact _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    Ideal.Quotient.mk_surjective

/-- **The quotient stages of the completion of `Spec A` along `V(I)` sit inside `Spec A`.** -/
private theorem supportStageToCompletion_comp_inclusion (K : SupportIdeal I) :
    supportStageToCompletion B S hS hA f I K ≫
        Space.completionSheafInclusion B S hS (yoneda.obj (affineOver B S hS hA f))
          (zeroLocusPoints B S hS hA f I) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (supportStageToAffine B S hS hA f I K) ≫
        (sheafifiedULiftIsoRepresented B S hS (affineOver B S hS hA f)).inv := by
  apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
  refine (sectionEquiv_supportStageToCompletion_comp_inclusion B S hS hA f I K).trans ?_
  refine Eq.trans ?_ (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS)
    (supportStageToAffine B S hS hA f I K)
    (sheafifiedULiftIsoRepresented B S hS (affineOver B S hS hA f)).inv).symm
  have hnat := NatTrans.naturality_apply
    ((BigFppfOver.topology B S hS).toSheafify
      (yoneda.obj (affineOver B S hS hA f) ⋙ uliftFunctor.{u + 1}))
    (supportStageToAffine B S hS hA f I K).op ⟨𝟙 (affineOver B S hS hA f)⟩
  rw [sectionEquiv_sheafifiedULiftIsoRepresented_inv]
  refine Eq.trans ?_ hnat
  congr 1

/-- A morphism of the big fppf site over `S` whose morphism of schemes is a closed immersion
induces a closed immersion of the represented fppf sheaves. -/
theorem isClosedImmersionInto_sheafifiedYoneda_map {a b : BigFppfOver B S hS} (g : a ⟶ b)
    (hg : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map g)) :
    IsClosedImmersionInto B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g) := by
  let _ := preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let ff := Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)
  let _ := ff.full
  let _ := ff.faithful
  let _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  exact MorphismProperty.relative_map hg

/-- **The affine case of the key step of clause (2) of Stacks 0GVV, for a zero locus.** A closed
immersion of an object of the site into the completion of `Spec A` along `V(I)` composes with
the inclusion of that completion into `Spec A` to a closed immersion. -/
private theorem isClosedImmersionInto_comp_inclusion_zeroLocus (Z : BigFppfOver B S hS)
    (c : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Z ⟶
      zeroLocusCompletion B S hS hA f I)
    (hc : IsClosedImmersionInto B S hS c) :
    IsClosedImmersionInto B S hS (c ≫ Space.completionSheafInclusion B S hS
      (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I)) := by
  have := isIso_supportComparison B S hS hA f I
  let e : zeroLocusCompletion B S hS hA f I ≅ colimit (supportSheafDiagram B S hS hA f I) :=
    (asIso (supportComparison B S hS hA f I)).symm
  obtain ⟨K, h, hci, hfac⟩ := exists_stage_isClosedImmersion_of_isClosedImmersionInto
    B S hS (supportDiagram B S hS hA f I)
    (fun {_ _} g ↦ isThickening_supportDiagram_map B S hS hA f I g) e c hc
  let L : SupportIdeal I := K.down
  have heK : colimit.ι (supportDiagram B S hS hA f I ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) K ≫ e.inv =
      supportStageToCompletion B S hS hA f I L :=
    supportComparison_stage B S hS hA f I L
  have hstage : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (supportStageToAffine B S hS hA f I L)) :=
    isClosedImmersion_supportStageToAffine B S hS hA f I L
  have hcomp : c ≫ Space.completionSheafInclusion B S hS
        (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map h ≫
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
            (supportStageToAffine B S hS hA f I L) ≫
          (sheafifiedULiftIsoRepresented B S hS (affineOver B S hS hA f)).inv) := by
    calc c ≫ Space.completionSheafInclusion B S hS
            (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I)
        = ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map h ≫
            (colimit.ι (supportDiagram B S hS hA f I ⋙ BigAffineFppf.inclusion B S hS ⋙
              Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) K ≫ e.inv)) ≫
            Space.completionSheafInclusion B S hS
              (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I) := by
          rw [hfac]
      _ = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map h ≫
            (supportStageToCompletion B S hS hA f I L ≫
              Space.completionSheafInclusion B S hS
                (yoneda.obj (affineOver B S hS hA f)) (zeroLocusPoints B S hS hA f I)) := by
          rw [Category.assoc, heK]
      _ = _ := by
          rw [supportStageToCompletion_comp_inclusion B S hS hA f I L]
          rfl
  rw [hcomp]
  exact isClosedImmersionInto_comp' _ _
    (isClosedImmersionInto_sheafifiedYoneda_map B S hS h hci)
    (MorphismProperty.RespectsIso.postcomp _
      (sheafifiedULiftIsoRepresented B S hS (affineOver B S hS hA f)).inv _
      (isClosedImmersionInto_sheafifiedYoneda_map B S hS
        (supportStageToAffine B S hS hA f I L) hstage))

/-- **The affine case of the key step of clause (2) of Stacks 0GVV.** A closed immersion of an
object of the site into the completion of an affine scheme `Spec A` of the site along a closed
set of its points composes with the inclusion of that completion into `Spec A` to a closed
immersion: a closed subscheme of the formal completion is a closed subscheme of `Spec A`.

The closed set of points is the set of points supported on a closed subset of the scheme
(`exists_isClosed_supportedPoints_eq`), and a closed subset of an affine scheme is the zero
locus of its vanishing ideal, so the statement reduces to
`isClosedImmersionInto_comp_inclusion_zeroLocus`. -/
theorem isClosedImmersionInto_comp_completionSheafInclusion_affineOver
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hA f))))
    (hT : @IsClosed _ (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS hA f))) T)
    (Z : BigFppfOver B S hS)
    (c : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Z ⟶
      Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA f)) T)
    (hc : IsClosedImmersionInto B S hS c) :
    IsClosedImmersionInto B S hS (c ≫ Space.completionSheafInclusion B S hS
      (yoneda.obj (affineOver B S hS hA f)) T) := by
  obtain ⟨Ti, hTi, hpts⟩ := exists_isClosed_supportedPoints_eq B S hS
    (affineOver B S hS hA f) (𝟙 (yoneda.obj (affineOver B S hS hA f))) T hT
  rw [Space.pointsMap_id, Set.preimage_id] at hpts
  have hTz : Ti = PrimeSpectrum.zeroLocus
      (PrimeSpectrum.vanishingIdeal Ti : Set A) :=
    hTi.closure_eq.symm.trans
      (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Ti).symm
  have hzl : T = zeroLocusPoints B S hS hA f (PrimeSpectrum.vanishingIdeal Ti) :=
    hpts.trans ((congrArg (supportedPoints B S hS (affineOver B S hS hA f)) hTz).trans
      (supportedPoints_zeroLocus B S hS hA f (PrimeSpectrum.vanishingIdeal Ti)))
  revert c hc
  rw [hzl]
  exact isClosedImmersionInto_comp_inclusion_zeroLocus B S hS hA f
    (PrimeSpectrum.vanishingIdeal Ti) Z

end Affine

end AlgebraicGeometry.FormalSpace

end
