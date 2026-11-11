module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSourceRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfSchemeThickenings
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine

/-!
# Sheaves representable by objects of the site over an affine formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `Y` be an affine formal algebraic
space over `S` and let `f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf site of `S`.
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_affineFormal` —
the source's reduction of **Stacks 0AJH** — concludes that `X` is a formal algebraic space from
`f` being representable by *algebraic spaces*, given the argument `h0AIU`: the stages of the
colimit presenting `X` are then algebraic spaces, and that a directed colimit of algebraic
spaces along thickenings is a formal algebraic space is **Stacks 0AIU**, proved in its corrected
form by
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_isRepresentableThickeningULift`
(not imported here). The registered unconditional Stacks 0AJH is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_isAffineFormal`.

This file does without that argument under the stronger assumption that `f` is representable **by
objects of the site**. The stages are then schemes, and
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_siteThickenings` — the
scheme-stage case of Stacks 0AIU, with its chart system constructed rather than assumed —
applies in place of `h0AIU`. The set-theoretic condition of **Stacks 0AIS** is not assumed
either: it passes to the source of a relatively representable morphism,
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_relativelyRepresentable`.

## Main results

* `isFormalAlgebraicSpace_of_relativelyRepresentable_over_affineFormal`:
  a sheaf carrying a morphism to an affine formal algebraic space which is representable by
  objects of the site is a formal algebraic space. Nothing is assumed beyond that.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isEtale_of_isAffineFormal`:
  the fibre product `U ×_Z V` of two affine formal algebraic spaces over an **arbitrary** fppf
  sheaf `Z` is a formal algebraic space as soon as one of the two legs is representable by
  algebraic spaces and étale. No hypothesis is placed on `Z`.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_pullback_of_isAffineFormal`:
  the second, iterated fibre product of the proof of **Stacks 0ANG** is a formal algebraic space
  as well, by the previous result and this library's Stacks 0AJ3.

## Why the base may be arbitrary

The second result is the form in which the refinement constructed by the proof of **Stacks
0ANG** needs the fibre products `Yᵢ ×_Y V₀` and `Xᵢ ×_X U₀`, and it is stated asking nothing
whatever of the base. That is more than that refinement needs —
`AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'` carries the standing hypothesis
of Stacks 0ANG, that `X` and `Y` are locally countably indexed, hence in particular formal
algebraic spaces, so
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`,
this library's **Stacks 0AJ3**, does apply to them — but it is worth recording, because the
statements below also cover a base about which nothing at all is known.

Nothing about the base is needed. **Stacks 0AIG** in the form
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_isEtale_of_isAffineFormal` makes a
representable étale morphism out of an affine formal algebraic space representable by objects of
the site, a property of the morphism alone; relative representability is stable under base
change, so the projection of the fibre product to the other affine formal leg is representable
by objects of the site too, and the first result applies to it. In particular the fibre products
of the proof of Stacks 0ANG do **not** need Stacks 0AJ2, which depends on Stacks 05ZH at
arbitrary order.

## What this does not supply

`AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'` names three inputs in its own
docstring. These results settle the first of them — the fibre products — and nothing more. Of
the other two, the second is now available elsewhere in the library and the third is not:

* **the extraction of a finite subfamily** is
  `exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace`.
  The refinement must be indexed by a `Finite` type, so an arbitrary covering as in Definition
  0AIM of the affine formal algebraic space `U₀` has to be cut down to a finite jointly
  surjective *subfamily* — the members keep their maps to the given covering, so a finite atlas
  obtained some other way will not do. That statement takes the covering as an argument and
  returns a finite reindexing `k : K → I` of it, so every datum the given covering carries
  restricts to the subfamily; its two inputs are quasi-compactness of an affine formal
  algebraic space, `AlgebraicGeometry.FormalSpace.affineReductionsQuasiCompact`, and the
  prescribed-covering form of the compact-point extraction,
  `AlgebraicGeometry.FormalSpace.exists_finite_subfamily_pullback_cover_of_compactSpace`, which
  is what the implication (1) ⇒ (2) of **Stacks 0AJ9** now routes through as well. Nothing in
  it assumes `AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`.
* **the presentation of the refinement by completed étale ring maps.** Nothing in the library
  concludes `AlgebraicGeometry.FormalSpace.IsCompletedEtaleLocalizationOfChartMap` or
  `AlgebraicGeometry.FormalSpace.IsCompletedEtaleFiniteCoverOfChartMap`: both ask for étale ring
  maps out of the chart rings whose completions present the members of the refinement, which is
  the essential-surjectivity clause of **Stacks 0AN8**,
  `AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf`, together with **Stacks 0AN9** for
  the faithfully flat covering. Both of those are now available —
  `AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf` and
  `AlgebraicGeometry.FormalSpace.etaleFormalSpectrumMap_surjective_tfae` — but neither of the
  two statements above follows from them alone: each asks for the étale ring map against an
  *arbitrary* prescribed presentation of the chart, so the completion produced by the clause has
  to be identified bicontinuously with that presentation (Stacks 0AN0, in the bicontinuous form
  `AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_of_formalSpectrum_iso`), and
  `IsCompletedEtaleLocalizationOfChartMap` asks in addition for a
  `TopologicalRing.LocalizationDiagram` relating the two charts, which the clause does not
  produce.

  The first of the two is now concluded, by
  `AlgebraicGeometry.FormalSpace.isCompletedEtaleLocalizationOfChartMap_of_presentation` and its
  geometric form `isCompletedEtaleLocalizationOfChartMap_of_isCountablyIndexedAffine`,
  and assembled over the whole refinement by
  `exists_finite_affineEtaleRefinement_completedEtaleLocalization_of_sourceCover`.
  Both of the first two ask the *lower* chart map for a presentation by rings of the class,
  resp. its two ends to be countably indexed, so the assembled form asks the members of the
  covering being refined to be countably indexed. What remains between that and
  `AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'`, whose hypothesis is the
  source's own — `X` and `Y` locally countably indexed — is the implication (2) ⟹ (1) of
  **Stacks 0AKX**, which the library does not carry. The second clause is concluded by
  nothing; it needs finite-product infrastructure that the library does not have.

NO TAG IS ATTACHED to any of the three statements. Stacks 0AJH asks only that the morphism be
representable by algebraic spaces, and Stacks 0AJ2 asks only that the diagonal of the base be
representable by algebraic spaces; the statements below assume representability by objects of
the site instead, which is strictly stronger, so they are special cases of those tags rather
than the tags.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AJH](https://stacks.math.columbia.edu/tag/0AJH)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN9](https://stacks.math.columbia.edu/tag/0AN9)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism `f : X ⟶ Y` to a directed colimit `Y` of fppf sheaves exhibits `X` as the colimit
of the fibre products of `f` with the stages, along an equifibered transformation to the stages. -/
theorem exists_isColimit_pullback_of_isDirected {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)] (G : Λ ⥤ FppfSheaf B S hS) [HasColimit G] {X Y : FppfSheaf B S hS}
    (eY : Y ≅ colimit G) (f : X ⟶ Y) :
    ∃ (E : Λ ⥤ FppfSheaf B S hS) (α : E ⟶ G) (ι : E ⟶ (Functor.const Λ).obj X),
      Nonempty (IsColimit (Cocone.mk X ι)) ∧ NatTrans.Equifibered α ∧
        ∀ i, IsPullback (ι.app i) (α.app i) f (colimit.ι G i ≫ eY.inv) := by
  let gi (i : Λ) : G.obj i ⟶ Y := colimit.ι G i ≫ eY.inv
  have hgi {i j : Λ} (g : i ⟶ j) : G.map g ≫ gi j = gi i := by
    simp [gi]
  let E : Λ ⥤ FppfSheaf B S hS :=
    { obj := fun i ↦ pullback (gi i) f
      map := fun {i j} g ↦ pullback.lift (pullback.fst (gi i) f ≫ G.map g)
        (pullback.snd (gi i) f) (by rw [Category.assoc, hgi g, pullback.condition])
      map_id := fun _ ↦ pullback.hom_ext (by simp) (by simp)
      map_comp := fun _ _ ↦ pullback.hom_ext
        (by simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          CategoryTheory.Functor.map_comp])
        (by simp only [Category.assoc, pullback.lift_snd]) }
  have hEfst {i j : Λ} (g : i ⟶ j) :
      E.map g ≫ pullback.fst (gi j) f = pullback.fst (gi i) f ≫ G.map g :=
    pullback.lift_fst _ _ _
  have hEsnd {i j : Λ} (g : i ⟶ j) :
      E.map g ≫ pullback.snd (gi j) f = pullback.snd (gi i) f :=
    pullback.lift_snd _ _ _
  let α : E ⟶ G := { app := fun i ↦ pullback.fst (gi i) f, naturality := fun _ _ g ↦ hEfst g }
  let ι : E ⟶ (Functor.const Λ).obj X :=
    { app := fun i ↦ pullback.snd (gi i) f, naturality := fun _ _ g ↦ by simpa using hEsnd g }
  let cY : Cocone G :=
    { pt := Y
      ι := { app := gi, naturality := fun _ _ g ↦ by simpa using hgi g } }
  have hpb (i : Λ) : IsPullback (ι.app i) (α.app i) f (gi i) :=
    (IsPullback.of_hasPullback (gi i) f).flip
  have hα : NatTrans.Equifibered α := by
    intro i j g
    refine IsPullback.of_right ?_ (hEfst g) (hpb j)
    rw [hEsnd g, hgi g]
    exact hpb i
  exact ⟨E, α, ι, (sheaf_filteredColimit_isUniversalColimit _ G).of_iso
    (Cocone.ext (c' := cY) eY.symm fun _ ↦ rfl) (Cocone.mk X ι) α f
    (NatTrans.ext (funext fun _ ↦ pullback.condition)) hα hpb, hα, hpb⟩

/-- **A sheaf representable by objects of the site over an affine formal algebraic space is a
formal algebraic space.** This is the special case of **Stacks 0AJH** in which the morphism to
the affine formal algebraic space is representable by objects of the big fppf site of `S` rather
than merely by algebraic spaces, and it carries nothing.

Write `Y` as the directed colimit of its affine stages, which is what being an affine formal
algebraic space provides (**Stacks 0AI7**). A filtered colimit of fppf sheaves is a universal
colimit, so `X` is the colimit of the fibre products of `f` with those stages. Each of those is
represented by an object of the site, by the hypothesis, so the diagram of stages lifts along
the fully faithful sheafified Yoneda embedding to a diagram in the site; each of its transitions
is a base change of a transition of the presentation of `Y`, hence a thickening of schemes
(**Stacks 09ZU**). So
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_siteThickenings` applies, in
place of the argument `h0AIU` that
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_affineFormal` takes
for stages which are only algebraic spaces.

The set-theoretic condition of **Stacks 0AIS** is proved rather than assumed: it passes from `Y`
to `X` along `f` by
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_relativelyRepresentable`, which
uses relative representability and nothing else.

NO TAG IS ATTACHED. Stacks 0AJH assumes only representability by algebraic spaces, which is
strictly weaker, so this is a special case of that tag and not the tag. -/
theorem isFormalAlgebraicSpace_of_relativelyRepresentable_over_affineFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable f) :
    IsFormalAlgebraicSpace B S hS X := by
  classical
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let F := Sheaf.sheafifiedYoneda J
  have : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  have : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  have : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  obtain ⟨hYset, Λ, pre, hne, hdir, D, hthickD, ⟨eY⟩⟩ := hY
  let : Preorder Λ := pre
  have : Nonempty Λ := hne
  have : IsDirected Λ (· ≤ ·) := hdir
  let G : Λ ⥤ FppfSheaf B S hS := D ⋙ BigAffineFppf.inclusion B S hS ⋙ F
  obtain ⟨E, α, ι, ⟨hX⟩, hα, hpb⟩ := exists_isColimit_pullback_of_isDirected B S hS G eY f
  have hess : ∀ i : Λ, F.essImage (E.obj i) := fun i ↦ by
    obtain ⟨P, _, _, hsq⟩ := hf (colimit.ι G i ≫ eY.inv)
    exact ⟨P, ⟨hsq.flip.isoPullback ≪≫ (hpb i).flip.isoPullback.symm⟩⟩
  let Dsite := Functor.essImage.liftFunctor E F hess
  have eD : Dsite ⋙ F ≅ E := Functor.essImage.liftFunctorCompIso E F hess
  let PT : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  have : PT.IsStableUnderBaseChange := inverseImage_isThickening_isStableUnderBaseChange B S hS
  have : (PT.relative F).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange PT
  have hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      IsThickening ((BigFppfOver.toScheme B S hS).map (Dsite.map g)) := by
    intro i j g
    have hE : PT.relative F (E.map g) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (hα g).flip
        (MorphismProperty.relative_map (hthickD g))
    have harr : Arrow.mk (F.map (Dsite.map g)) ≅ Arrow.mk (E.map g) :=
      Arrow.isoMk (eD.app i) (eD.app j) (eD.hom.naturality g).symm
    change PT (Dsite.map g)
    exact MorphismProperty.of_relative_map
      ((MorphismProperty.arrow_mk_iso_iff (P := PT.relative F) harr).mpr hE)
  exact isFormalAlgebraicSpace_of_colimit_siteThickenings B S hS Dsite hthick X
    (satisfiesSetTheoreticCondition_of_relativelyRepresentable B S hS f hf hYset)
    ⟨hX.coconePointUniqueUpToIso (colimit.isColimit E) ≪≫ (HasColimit.isoOfNatIso eD).symm⟩

/-- **The fibre product of two affine formal algebraic spaces over an arbitrary fppf sheaf is a
formal algebraic space, as soon as one leg is representable by algebraic spaces and étale.**
Nothing whatsoever is assumed about the base `Z`.

The leg `p` is representable by objects of the site by **Stacks 0AIG**, in the form
`AlgebraicGeometry.FormalSpace.exists_isPullback_etale_isSeparated_of_chart`, which asks only
that the source of `p` be an affine formal algebraic space and that `p` be representable by
algebraic spaces and étale. Relative representability is stable under base change, so the
second projection `U ×_Z V ⟶ V` is representable by objects of the site as well, and
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_relativelyRepresentable_over_affineFormal`
applies to it over the affine formal algebraic space `V`.

The two hypotheses `hrep` and `het` are the two components of
`AlgebraicGeometry.FormalSpace.IsRepresentableEtale`, taken separately so that this statement
does not depend on the module declaring that abbreviation.

NO TAG IS ATTACHED. **Stacks 0AJ2** concludes this for a base whose diagonal is representable by
algebraic spaces and asks nothing of the legs; here the base is arbitrary and one leg is asked
for representability and étaleness, so neither statement implies the other and this is not the
tag. -/
theorem isFormalAlgebraicSpace_pullback_of_isEtale_of_isAffineFormal
    {U V Z : FppfSheaf B S hS} (p : U ⟶ Z) (q : V ⟶ Z)
    (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) p.hom hrep)
    (hV : IsAffineFormalAlgebraicSpace B S hS V) :
    IsFormalAlgebraicSpace B S hS (pullback p q) := by
  have hp : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable p := by
    intro _ c
    obtain ⟨W, pr, s, hsq, -, -⟩ :=
      exists_isPullback_etale_isSeparated_of_chart B S hS p hU hrep het c
    exact ⟨W, pr, s, hsq⟩
  exact isFormalAlgebraicSpace_of_relativelyRepresentable_over_affineFormal B S hS
    (pullback.snd p q) hV
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback p q) hp)

/-- **The second fibre product of the proof of Stacks 0ANG is a formal algebraic space.** In the
notation of that proof, `Z = Yᵢⱼ` is an affine formal algebraic space over the affine formal
algebraic space `V = Yᵢ`, and the other leg is `Xᵢ ×_X U₀ ⟶ Xᵢ ⟶ Yᵢ`, the fibre product of the
member `u : U = Xᵢ ⟶ X` of the covering of condition (3) with the chart `a : U₀ ⟶ X` of
condition (1), followed by the factorization `t : Xᵢ ⟶ Yᵢ`.

The inner fibre product is a formal algebraic space by
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isEtale_of_isAffineFormal`,
which needs nothing of the base `X`. The outer one is then this library's **Stacks 0AJ3**,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace`: its
base `V` is an affine formal algebraic space, hence a formal algebraic space, and so are both
legs. So neither fibre product of that proof needs Stacks 0AJ2.

NO TAG IS ATTACHED, for the reason given on
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isEtale_of_isAffineFormal`. -/
theorem isFormalAlgebraicSpace_pullback_pullback_of_isAffineFormal
    {U U₀ X V Z : FppfSheaf B S hS} (u : U ⟶ X) (a : U₀ ⟶ X) (t : U ⟶ V) (r : Z ⟶ V)
    (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS u.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) u.hom hrep)
    (hU₀ : IsAffineFormalAlgebraicSpace B S hS U₀)
    (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hZ : IsAffineFormalAlgebraicSpace B S hS Z) :
    IsFormalAlgebraicSpace B S hS (pullback r (pullback.fst u a ≫ t)) :=
  isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS r (pullback.fst u a ≫ t)
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV)
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hZ)
    (isFormalAlgebraicSpace_pullback_of_isEtale_of_isAffineFormal B S hS u a hU hrep het hU₀)

end AlgebraicGeometry.FormalSpace

end
