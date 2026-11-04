module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Assembly.Relativize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitChartLocality
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactQuasiSeparatedPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSiteChart
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SurjectiveClosedImmersionAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfSchemeThickenings
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReductionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaSupplement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReductionSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersionSupplement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSupplement

/-!
# A formal algebraic space with affine reduction

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0DE8** says that a formal
algebraic space `X` over `S` is an *affine* formal algebraic space exactly when its reduction
`X_red` of Stacks 0AIN is affine.

## Main results

* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_iff_isAffine_reduction`:
  **Stacks 0DE8**.

## The proof

One direction is the affine case of Stacks 0AIN: an affine formal algebraic space is a
directed colimit of affine schemes along thickenings, and a thickening does not change the
reduction, so the reduction is the reduced closed subscheme of any one stage
(`AlgebraicGeometry.FormalSpace.exists_isReduction_reduced_affine_siteObject_of_isAffineFormal`).
Two reductions of one sheaf are isomorphic, by the universal property of either.

For the other direction let `X_red` be the sheaf of an affine object `T` of the site. Then

1. `X` is quasi-compact: `T` is quasi-compact, which is condition (1) of Stacks 0AJ9, and that
   tag gives condition (3);
2. `X` is quasi-separated: this is clause (3) of Stacks 0AJ5 for `X`, which
   `AlgebraicGeometry.FormalSpace.hasQuasiCompactIntersectionsULift_of_isReduction` deduces
   from the same clause for `X_red`, and for `X_red = h_T` with `T` affine it is the affineness
   of a fibre product of two affine schemes over an affine scheme;
3. so Stacks 0AJE presents `X = colim_λ W_λ` by algebraic spaces along thickenings;
4. each stage has `h_T` for a reduction: `T` is quasi-compact, so the reduction `h_T ⟶ X`
   factors through some stage, the colimit injections are monomorphisms, and a cartesian square
   over a stage is a cartesian square over the colimit, so the factorization is again a
   representable thickening and is universal because the colimit injection is a monomorphism;
5. hence each stage is an algebraic space receiving a thickening from an affine scheme, that is,
   a surjective closed immersion, so the stage is an affine scheme by the closed-immersion case
   of **Stacks 07VS** — the source's route through Stacks 07VU appeals to Stacks 07VT here, but
   only this special case is needed, and it is proved (see below);
6. and Stacks 0GVM assembles the colimit of those affine stages into an affine formal algebraic
   space, the set-theoretic condition of Stacks 0AIS coming from `X` being a formal algebraic
   space.

## The input from Stacks 07VS

Step 5 applies Stacks 07VS to a surjective closed immersion from an affine scheme of the site, a
thickening. The inner results below take that statement as the argument
`haff : AlgebraicGeometry.FormalSpace.IsAffineOfSurjectiveClosedImmersion B S hS`, and **Stacks
0DE8 supplies it**: `AlgebraicGeometry.FormalSpace.isAffineOfSurjectiveClosedImmersion` proves it
with nothing granted, through
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace`.
That proof does not follow the source's route through Stacks 07VR, 07SQ and the
finite-presentation case, which this library cannot yet take; it approximates the thickening from
above by finite-order thickenings and uses the topological invariance of the étale site,
Stacks 05ZH. So the registered statement carries no granted hypothesis. Neither Stacks 05ZR nor
Stacks 06AD for algebraic spaces is used in the form the source cites.

## References

* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ5](https://stacks.math.columbia.edu/tag/0AJ5)
* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AJE](https://stacks.math.columbia.edu/tag/0AJE)
* [Stacks Project, Tag 0DE8](https://stacks.math.columbia.edu/tag/0DE8)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-compactness and quasi-separatedness from the reduction -/

/-- **A formal algebraic space whose reduction is the sheaf of a quasi-compact object of the
site is quasi-compact.** This is the implication (1) ⇒ (3) of Stacks 0AJ9 at a reduction of that
shape. -/
theorem isQuasiCompactSpace_of_isReduction_uliftYoneda
    {X Xred : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {i : Xred ⟶ X} (hi : IsReduction B S hS X Xred i)
    {T : BigFppfOver B S hS} (eT : (uliftYoneda.{u + 1}).obj T ≅ Xred.obj)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    IsQuasiCompactSpace B S hS X :=
  HasFiniteFormalAtlas.isQuasiCompactSpace' B S hS
    (hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_of_isReduction B S hS hX hi
      (Space.isQuasiCompactSpaceULift_of_iso B S hS eT
        (Space.isQuasiCompactSpaceULift_uliftYoneda.{u + 1} B S hS T hT)))

/-- **The intersection condition of Stacks 0AJ5 with affine test objects holds for the sheaf of
an affine object of the site.** A fibre product of two affine schemes over an affine scheme is
affine, hence quasi-compact; the universe-lifted Yoneda embedding is fully faithful and the
underlying-scheme functor preserves fibre products, so the cartesian square of presheaves the
condition quantifies over is the image of a cartesian square of schemes. -/
theorem hasQuasiCompactIntersectionsULift_uliftYoneda_of_isAffine
    (T : BigFppfOver B S hS) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    HasQuasiCompactIntersectionsULift B S hS (fun Z : Scheme.{u} ↦ IsAffine Z)
      ((uliftYoneda.{u + 1}).obj T) := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  intro U V Q a b p q hU hV sq
  obtain ⟨a₀, ha₀⟩ := (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).map_surjective a
  obtain ⟨b₀, hb₀⟩ := (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).map_surjective b
  subst ha₀ hb₀
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj Q) := IsAffine.of_isPullback
    ((sq.of_map_of_faithful (uliftYoneda.{u + 1} (C := BigFppfOver B S hS))).map
      (BigFppfOver.toScheme B S hS))
  infer_instance

/-- **A formal algebraic space whose reduction is the sheaf of an affine object of the site is
quasi-separated.** The intersection condition of Stacks 0AJ5 with affine test objects passes
from the reduction to the space, and for the sheaf of an affine object it is the affineness of a
fibre product of affines. -/
theorem isQuasiSeparated_of_isReduction_uliftYoneda_of_isAffine
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X} (hi : IsReduction B S hS X Xred i)
    {T : BigFppfOver B S hS} (eT : (uliftYoneda.{u + 1}).obj T ≅ Xred.obj)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsQuasiSeparated B S hS X := by
  have hXred : HasQuasiCompactIntersectionsULift B S hS (fun Z : Scheme.{u} ↦ IsAffine Z)
      Xred.obj :=
    hasQuasiCompactIntersectionsULift_of_mono B S hS _ eT.inv
      (hasQuasiCompactIntersectionsULift_uliftYoneda_of_isAffine B S hS T hT)
  have hXsp : HasQuasiCompactIntersectionsULift B S hS (fun Z : Scheme.{u} ↦ IsAffine Z)
      X.obj :=
    hasQuasiCompactIntersectionsULift_of_isReduction B S hS _
      (fun W hW ↦ @isAffine_toScheme_obj_siteReduction B S hS W hW) hi hXred
  intro U V P f g p q hU hV sq
  set η := fppfYonedaCompSheafToPresheaf' B S hS
  refine hXsp U V P ((η.app U).inv ≫ f.hom) ((η.app V).inv ≫ g.hom) p q hU hV ?_
  refine (sq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).of_iso
    (η.app P) (η.app U) (η.app V) (Iso.refl X.obj) (η.hom.naturality p) (η.hom.naturality q) ?_ ?_
  · exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc (η.app U) f.hom).symm
  · exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc (η.app V) g.hom).symm

/-! ### The reduction of a subobject through which the reduction factors -/

/-- **A representable thickening which factors through a monomorphism factors by a representable
thickening.** A cartesian square over the intermediate sheaf is a cartesian square over the
ambient one, the comparison being a monomorphism, so both clauses transfer. -/
theorem isRepresentableThickeningULift_of_comp_mono
    {X W Y : FppfSheaf B S hS} (ι : W ⟶ X) [Mono ι] (s : Y ⟶ W)
    (h : Space.IsRepresentableThickeningULift.{u + 1} B S hS (s ≫ ι).hom) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS s.hom := by
  have : Mono ι.hom :=
    (Sheaf.Hom.mono_iff_presheaf_mono (BigFppfOver.topology B S hS) (Type (u + 1)) ι).1
      inferInstance
  rw [show (s ≫ ι).hom = s.hom ≫ ι.hom from rfl] at h
  refine ⟨fun A g ↦ ?_, fun a b g fst snd hpb ↦
    h.property (g ≫ ι.hom) fst snd ((isPullback_comp_mono_iff ι.hom).2 hpb)⟩
  obtain ⟨b, snd, fst, hpb⟩ := h.rep (g ≫ ι.hom)
  exact ⟨b, snd, fst, (isPullback_comp_mono_iff ι.hom).1 hpb⟩

/-- **A reduction of a sheaf is a reduction of any subobject of it through which the reduction
factors.** If `ι : W ⟶ X` is a monomorphism and the inclusion `i : X_red ⟶ X` of a reduction
factors as `s ≫ ι`, then `s` exhibits `X_red` as a reduction of `W`: a cartesian square over `W`
is a cartesian square over `X`, which gives the representability and thickening clauses, and the
universal property transfers because `ι` is a monomorphism. -/
theorem isReduction_of_factor_through_mono
    {X W Xred : FppfSheaf B S hS} (ι : W ⟶ X) [Mono ι] {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i) (s : Xred ⟶ W) (hs : s ≫ ι = i) :
    IsReduction B S hS W Xred s := by
  have hth : Space.IsRepresentableThickeningULift.{u + 1} B S hS s.hom := by
    refine isRepresentableThickeningULift_of_comp_mono B S hS ι s ?_
    rw [hs]
    exact hi.isRepresentableThickening
  refine ⟨hi.algebraic, hi.reduced, hth.rep, hth.property, fun U hU hUred f ↦ ?_⟩
  obtain ⟨g, hg, hgu⟩ := hi.universal U hU hUred (f ≫ ι)
  refine ⟨g, (cancel_mono ι).1 (by rw [Category.assoc, hs, hg]), fun g' hg' ↦ hgu g' ?_⟩
  show g' ≫ i = f ≫ ι
  rw [← hs, ← Category.assoc, hg']

/-! ### The universe lift of a thickening of algebraic spaces -/

/-- **The universe lift of a thickening of algebraic spaces over `S` is a representable
thickening.** A thickening is a closed immersion, hence representable, and it is surjective by
Stacks 03MD, so each of its represented base changes is a surjective closed immersion of
schemes. This is the converse of
`AlgebraicGeometry.FormalSpace.isThickeningHom_of_isRepresentableThickeningULift`. -/
theorem isRepresentableThickeningULift_liftSheafMap_of_isThickeningHom
    {W W' : AlgebraicSpaces B S hS} {f : W ⟶ W'} (hf : Space.IsThickeningHom B S hS f) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS
      ((liftSheafFunctor B S hS).map f).hom := by
  have hci : Space.IsClosedImmersion B S hS f.hom := hf.isClosedImmersion
  have hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom :=
    (Space.surjective_iff_pointsMap_surjective B S hS W.property W'.property f.hom
      hci.rep).2 hf.surjective_pointsMap
  refine (Space.relative_uliftYoneda_whiskerRight_iff' B S hS
    (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f.hom).mpr ⟨hci.rep, ?_⟩
  intro a b g fst snd hpb
  exact ⟨hci.property g fst snd hpb, (hsurj.property g fst snd hpb).1⟩

/-! ### An algebraic space whose reduction is an affine scheme -/

/-- **An algebraic space over `S` receiving a representable thickening from the sheaf of an
affine object of the site is an affine formal algebraic space**, indeed the sheaf of an affine
object of the site.

The thickening is a thickening of algebraic spaces with affine source, so it is a surjective
closed immersion, and the closed-immersion case of Stacks 07VS, the argument `haff`, makes the
ambient space an affine scheme of the site in one step. This is the application of Stacks 07VT
that the source's Stacks 07VU makes; only the closed-immersion case is needed, and
`AlgebraicGeometry.FormalSpace.isAffineOfSurjectiveClosedImmersion` proves it. -/
theorem isAffineFormalAlgebraicSpace_liftSheaf_of_isRepresentableThickening_uliftYoneda
    {W : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {s : yonedaSheaf B S hS T ⟶ liftSheaf B S hS W}
    (hs : Space.IsRepresentableThickeningULift.{u + 1} B S hS s.hom)
    (haff : IsAffineOfSurjectiveClosedImmersion B S hS) :
    IsAffineFormalAlgebraicSpace B S hS (liftSheaf B S hS W) := by
  classical
  -- the thickening comes from a morphism of algebraic spaces
  set eTS : (liftSheafFunctor B S hS).obj ((schemeSpaceFunctor B S hS).obj T) ≅
      yonedaSheaf B S hS T :=
    liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS T ≪≫
      (yonedaSheafIsoSheafifiedYoneda B S hS T).symm
  set c : (schemeSpaceFunctor B S hS).obj T ⟶ W :=
    (liftSheafFunctorFullyFaithful B S hS).preimage (eTS.hom ≫ s)
  have hcmap : (liftSheafFunctor B S hS).map c = eTS.hom ≫ s :=
    (liftSheafFunctorFullyFaithful B S hS).map_preimage (eTS.hom ≫ s)
  have hcth : Space.IsThickeningHom B S hS c :=
    isThickeningHom_of_isRepresentableThickeningULift B S hS c eTS (Iso.refl _) s
      (by rw [hcmap]; simp) hs
      (bijective_pointsMapULift_of_isRepresentableThickeningULift hs).2
  -- the thickening is a surjective finite morphism from an affine scheme
  have hcci : Space.IsClosedImmersion B S hS c.hom := hcth.isClosedImmersion
  have hcsurj : Space.IsSurjective B S hS c.hom :=
    Space.isSurjective_of_presheafSurjective B S hS c.hom
      ((Space.surjective_iff_pointsMap_surjective B S hS
        (isAlgebraicSpace_yoneda B S hS T) W.property c.hom hcci.rep).2
        hcth.surjective_pointsMap)
  -- so the ambient space is an affine scheme of the site, by Stacks 07VS for thickenings
  obtain ⟨V, hVaff, ⟨eV⟩⟩ := haff c.hom W.property hT hcsurj hcci
  -- and its universe lift is the sheaf of an affine object of the site
  have eW : W ≅ (schemeSpaceFunctor B S hS).obj V :=
    (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u ↦
      IsAlgebraicSpace B S hS F)).preimageIso eV
  refine isAffineFormalAlgebraicSpace_of_iso B S hS
    (((liftSheafFunctor B S hS).mapIso eW).trans
      (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS V)).symm ?_
  exact isAffineFormalAlgebraicSpace_sheafifiedYoneda' B S hS V hVaff

/-- **An algebraic space over `S` is an affine formal algebraic space if a thickening of it into
a second algebraic space has a base change along a representable thickening from the sheaf of an
affine object of the site.** The base change is a closed subscheme of that affine object, hence
affine, and it is a representable thickening of the first space. -/
private theorem isAffineFormalAlgebraicSpace_liftSheaf_of_isRepresentableThickening_baseChange
    {W W' : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (q : W ⟶ W')
    (hq : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      ((liftSheafFunctor B S hS).map q).hom)
    {t : yonedaSheaf B S hS T ⟶ liftSheaf B S hS W'}
    (ht : Space.IsRepresentableThickeningULift.{u + 1} B S hS t.hom)
    (haff : IsAffineOfSurjectiveClosedImmersion B S hS) :
    IsAffineFormalAlgebraicSpace B S hS (liftSheaf B S hS W) := by
  have hsq := hq.rep.isPullback t.hom
  have _ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (hq.rep.snd t.hom)) := (hq.property _ _ _ hsq).1
  have hPaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (hq.rep.pullback t.hom)) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hq.rep.snd t.hom))
  exact isAffineFormalAlgebraicSpace_liftSheaf_of_isRepresentableThickening_uliftYoneda
    B S hS hPaff (s := ⟨hq.rep.fst t.hom⟩)
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq.flip ht) haff

/-! ### Stacks 0DE8 -/

attribute [local instance] Sheaf.instHasColimitsOfSize

/-- **Two reductions of one fppf sheaf are isomorphic.** Each factors through the other by the
universal property of the other, and the two composites are the identities, again by the
uniqueness in that property. -/
theorem nonempty_iso_of_isReduction {X R R' : FppfSheaf B S hS} {r : R ⟶ X} {r' : R' ⟶ X}
    (h : IsReduction B S hS X R r) (h' : IsReduction B S hS X R' r') : Nonempty (R ≅ R') := by
  exact h.nonempty_iso h'

/-- **The substantial half of Stacks 0DE8.** A formal algebraic space over `S` whose reduction
is the sheaf of an affine object of the big fppf site of `S` is an affine formal algebraic space.

The space is quasi-compact and quasi-separated, so Stacks 0AJE presents it as a directed colimit
of algebraic spaces along thickenings. The reduction is quasi-compact, so it factors through one
stage, and that factorization is again a representable thickening because the colimit injection
is a monomorphism. The base change of a transition morphism along it exhibits *every* stage as
receiving a representable thickening from an affine object of the site, so every stage is an
affine formal algebraic space, and Stacks 0GVM assembles the colimit.

The argument `haff` is the closed-immersion case of Stacks 07VS, which
`AlgebraicGeometry.FormalSpace.isAffineOfSurjectiveClosedImmersion` proves; see the module
documentation. -/
theorem isAffineFormalAlgebraicSpace_of_isReduction_uliftYoneda_of_isAffine
    {X Xred : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {i : Xred ⟶ X} (hi : IsReduction B S hS X Xred i)
    {T : BigFppfOver B S hS} (eT : (uliftYoneda.{u + 1}).obj T ≅ Xred.obj)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (haff : IsAffineOfSurjectiveClosedImmersion B S hS) :
    IsAffineFormalAlgebraicSpace B S hS X := by
  classical
  have hTqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) := inferInstance
  obtain ⟨Λ, pre, hne, hdir, D, hD, ⟨eX⟩⟩ :=
    exists_colimit_presentation_of_quasiCompact_quasiSeparated B S hS X hX
      (isQuasiCompactSpace_of_isReduction_uliftYoneda B S hS hX hi eT hTqc)
      (isQuasiSeparated_of_isReduction_uliftYoneda_of_isAffine B S hS hi eT hT)
  let : Preorder Λ := pre
  let : Nonempty Λ := hne
  let : IsDirected Λ (· ≤ ·) := hdir
  set E : Λ ⥤ FppfSheaf B S hS := D ⋙ liftSheafFunctor B S hS
  have hEthick : ∀ ⦃a b : Λ⦄ (g : a ⟶ b),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom := fun a b g ↦
    isRepresentableThickeningULift_liftSheafMap_of_isThickeningHom B S hS (hD g)
  have hEmono : ∀ (a b : Λ) (g : a ⟶ b), Mono (E.map g) := fun a b g ↦
    mono_of_isRepresentableThickening B S hS (E.map g) (hEthick g)
  -- the reduction of `X`, with the sheaf of `T` for its source
  set iT : yonedaSheaf B S hS T ⟶ X := ⟨eT.hom ≫ i.hom⟩
  -- it factors through a stage, `T` being quasi-compact
  obtain ⟨l₀, g₀, hg₀⟩ := compact_map_factors_through_filtered_colimit E
    (fun _ _ g ↦ hEmono _ _ g) T (BigFppfOver.isQuasiCompactObject_of_compactSpace B S hS T hTqc)
    ((yonedaSheafIsoSheafifiedYoneda B S hS T).inv ≫ iT ≫ eX.hom)
  have : Mono (colimit.ι E l₀) := Sheaf.mono_colimit_ι_of_mono_transition E hEmono l₀
  set s₀ : yonedaSheaf B S hS T ⟶ E.obj l₀ :=
    (yonedaSheafIsoSheafifiedYoneda B S hS T).hom ≫ g₀ with hs₀
  have hs₀eq : s₀ ≫ (colimit.ι E l₀ ≫ eX.inv) = iT := by
    rw [hs₀, Category.assoc, ← Category.assoc g₀, hg₀, Category.assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hs₀th : Space.IsRepresentableThickeningULift.{u + 1} B S hS s₀.hom := by
    refine isRepresentableThickeningULift_of_comp_mono B S hS (colimit.ι E l₀ ≫ eX.inv) s₀ ?_
    rw [hs₀eq]
    exact MorphismProperty.RespectsIso.precomp _ eT.hom i.hom hi.isRepresentableThickening
  -- every stage receives a representable thickening from an affine object of the site
  have hstage : ∀ μ : Λ, IsAffineFormalAlgebraicSpace B S hS (E.obj μ) := fun μ ↦ by
    obtain ⟨ν, hlν, hμν⟩ := directed_of (· ≤ ·) l₀ μ
    exact isAffineFormalAlgebraicSpace_liftSheaf_of_isRepresentableThickening_baseChange B S hS
      hT (D.map (homOfLE hμν)) (hEthick (homOfLE hμν))
      (isRepresentableThickeningULift_comp B S hS hs₀th (hEthick (homOfLE hlν))) haff
  exact isAffineFormalAlgebraicSpace_colimit B S hS E hstage
    (fun a b g ↦ (relative_sheafifiedYoneda_iff_uliftYoneda' B S hS _ (E.map g)).mpr (hEthick g))
    X eX hX.1

/-- **The easy half of Stacks 0DE8.** The reduction of an affine formal algebraic space over `S`
is the sheaf of an affine object of the big fppf site of `S`: that is the affine case of
Stacks 0AIN, and two reductions of one sheaf are isomorphic. -/
theorem exists_isAffine_uliftYoneda_iso_of_isAffineFormalAlgebraicSpace
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X} (hi : IsReduction B S hS X Xred i)
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    ∃ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty ((uliftYoneda.{u + 1}).obj T ≅ Xred.obj) := by
  obtain ⟨T, g, -, hTaff, -, hgred⟩ :=
    exists_isReduction_reduced_affine_siteObject_of_isAffineFormal B S hS X hX
  obtain ⟨e⟩ := nonempty_iso_of_isReduction B S hS hgred hi
  exact ⟨T, hTaff, ⟨(sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso e⟩⟩

/-- **Stacks 0DE8.** Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal
algebraic space over `S` with reduction `i : X_red ⟶ X` as in Stacks 0AIN. Then `X` is an affine
formal algebraic space over `S` if and only if `X_red` is affine, that is, if and only if it is
the sheaf of an object of the site with affine underlying scheme.

Nothing is granted. The converse direction uses, for one stage of the presentation of Stacks 0AJE,
that an algebraic space receiving a surjective closed immersion from an affine scheme of the site is
affine: `AlgebraicGeometry.FormalSpace.isAffineOfSurjectiveClosedImmersion`, the closed-immersion
case of Stacks 07VS, proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineThickening`. -/
@[stacks 0DE8 "affineness of the reduction rendered as its being the sheaf of an object of the site \
with affine underlying scheme, the shape Stacks 0AIN delivers in the affine case; stated for an \
arbitrary reduction i : X_red -> X, which generalizes the source's canonical one"]
theorem isAffineFormalAlgebraicSpace_iff_isAffine_reduction
    {X Xred : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {i : Xred ⟶ X} (hi : IsReduction B S hS X Xred i) :
    IsAffineFormalAlgebraicSpace B S hS X ↔
      ∃ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
        Nonempty ((uliftYoneda.{u + 1}).obj T ≅ Xred.obj) := by
  refine ⟨exists_isAffine_uliftYoneda_iso_of_isAffineFormalAlgebraicSpace B S hS hi, ?_⟩
  rintro ⟨T, hTaff, ⟨eT⟩⟩
  exact isAffineFormalAlgebraicSpace_of_isReduction_uliftYoneda_of_isAffine B S hS hX hi eT
    hTaff (isAffineOfSurjectiveClosedImmersion B S hS)

end AlgebraicGeometry.FormalSpace

end
