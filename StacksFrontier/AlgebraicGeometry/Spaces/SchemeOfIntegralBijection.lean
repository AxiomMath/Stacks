module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism

/-!
# Schemes under an integral bijection of algebraic spaces (Stacks 07VV, 07VU)

An integral morphism of algebraic spaces over `S` which is a bijection on points has a scheme
source exactly when it has a scheme target (Stacks 07VV), and an algebraic space whose reduction
is a scheme is a scheme (Stacks 07VU). Being a scheme is `CategoryTheory.Functor.IsRepresentable`
for the presheaf underlying the space.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_surjective_pointsMap_schematicLocus`: an algebraic
  space whose schematic locus of Stacks 03JH carries every point is a scheme.
* `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom`: **Stacks 07VV, the implication from
  the target**, which needs no bijectivity: an integral morphism with scheme target has scheme
  source.
* `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective`: **Stacks 07VV, the
  implication from the source.**
* `AlgebraicGeometry.Space.isRepresentable_iff_of_isIntegralHom_of_bijective`: **Stacks 07VV.**
* `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_reduction`: **Stacks 07VU.**

## Implementation notes

The source glues the affine opens produced for the target into a scheme by Tag 01JJ, which on
the big fppf site of `S` carries a cardinal hypothesis on the index of the covering. No such
hypothesis is needed here, and no covering family is formed: each point of the target is placed
in the *schematic locus* of Stacks 03JH, which is an open subspace and is representable with no
hypotheses by `isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace`, so an
inclusion of the locus that is surjective on points is an isomorphism and the whole space is the
locus. This is `AlgebraicGeometry.Space.isRepresentable_of_surjective_pointsMap_schematicLocus`,
and both implications of Stacks 07VV run through it.

For the implication from the source, the affine open `V ⊆ Y` attached to an affine open
`U ⊆ X` is the open subspace cut out by the point set `|f|(|U|)`, which is open because an
integral morphism is universally closed by Stacks 0415, hence closed on points, and `|f|` is
bijective. The base change `X ×_Y V` has the same point set as `U`, so the two agree as open
subspaces by part (1) of Tag 03BZ, and the projection to `V` is integral and surjective; Stacks
07VT then makes `V` affine.

Stacks 07VU reduces to Stacks 07VV applied to the inclusion of
`AlgebraicGeometry.Space.reduction`: that inclusion is injective on points because it is a
monomorphism, surjective on points by `surjective_pointsMap_ι_reduction`, and integral because
it is a closed immersion by Stacks 081Y. The last of those is unconditional:
`isClosedSubspace_reducedClosedSubspace` is the form of Stacks 03IQ whose effective-descent
hypothesis is already discharged.

The three hypotheses `h09YA`, `h07SQ` and `hFinitePresentation` are carried unchanged from
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`, so the results
below are conditional on precisely what Stacks 07VT is conditional on and on nothing else. None
is the universally quantified form of any conclusion here: the first two conclude about inverse
systems and the third about affineness of a target.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two general lemmas -/

/-- A closed map which is bijective is open. -/
private theorem isOpen_image_of_bijective_of_isClosedMap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {g : α → β} (hg : Function.Bijective g) (hclosed : IsClosedMap g)
    {V : Set α} (hV : IsOpen V) : IsOpen (g '' V) := by
  rw [← isClosed_compl_iff, ← Set.image_compl_eq hg]
  exact hclosed Vᶜ hV.isClosed_compl

/-- **An algebraic space whose schematic locus carries every point is a scheme.**

The schematic locus of Stacks 03JH is an open subspace and is representable, so an inclusion of
it which is surjective on points is an open immersion surjective after every represented base
change, hence an isomorphism. -/
theorem isRepresentable_of_surjective_pointsMap_schematicLocus
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hsurj : Function.Surjective (pointsMap B S hS (schematicLocus B S hS F).toFunctor
      (schematicLocus B S hS F).ι)) :
    F.IsRepresentable := by
  obtain ⟨hopen, hrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF
  have _ : IsIso (schematicLocus B S hS F).ι :=
    isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS _ hopen.2
      (presheafSurjective_of_isSurjective B S hS _ hopen.2.rep hsurj)
  let _ : (schematicLocus B S hS F).toFunctor.IsRepresentable := hrep
  exact isRepresentable_of_natIso _ (asIso (schematicLocus B S hS F).ι)

/-- An affine open neighbourhood of a point of a representable presheaf: a member of the
standard affine cover of the representing object through which the point factors. -/
private theorem exists_affineChart_isOpenImmersion_mem_range
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : BigFppfOver B S hS) (e : yoneda.obj U ≅ F)
    (x : points B S hS F) :
    ∃ (V : BigFppfOver B S hS) (α : yoneda.obj V ⟶ F),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ IsOpenImmersion B S hS α ∧
        x ∈ Set.range (pointsMap B S hS (yoneda.obj V) α) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  obtain ⟨i, q, hq⟩ := exists_affineChart_pointsMap_eq B S hS U e p
  refine ⟨affineChart B S hS U i, yoneda.map (affineChartι B S hS U i) ≫ e.hom,
    isAffine_affineChart B S hS U i, ?_, ⟨_, hq⟩⟩
  refine MorphismProperty.RespectsIso.postcomp _ e.hom _ ?_
  exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@AlgebraicGeometry.IsOpenImmersion.{u}) _).2
    (isOpenImmersion_toScheme_map_affineChartι B S hS U i)

/-! ### Stacks 07VV -/

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 07VV, the implication from the target.** If the target of an integral morphism of
algebraic spaces over `S` is a scheme, then so is its source. Bijectivity on points is not
needed.

An integral morphism is representable, so the base change of the morphism along an affine open
of the target is an affine open subspace of the source; the affine opens of the target cover it,
so every point of the source lies in a representable open subspace, hence in the schematic
locus of Stacks 03JH. -/
@[stacks 07VV "the implication from the target, with no bijectivity hypothesis"]
theorem isRepresentable_of_isIntegralHom (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G)
    (hf : IsIntegralHom B S hS f) (hGrep : G.IsRepresentable) :
    F.IsRepresentable := by
  classical
  let _ : G.IsRepresentable := hGrep
  refine isRepresentable_of_surjective_pointsMap_schematicLocus B S hS hF fun x => ?_
  obtain ⟨V, α, hVaff, hαopen, v, hv⟩ := exists_affineChart_isOpenImmersion_mem_range B S hS
    (Functor.reprX G) (Functor.reprW G) (pointsMap B S hS F f x)
  obtain ⟨W, pW, qW, hpb, -, -⟩ := hf V hVaff α
  have hqopen : IsOpenImmersion B S hS qW :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb.flip hαopen
  have _ : Mono qW := mono_of_presheaf_isOpenImmersion hqopen
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS hpb x v hv.symm
  refine (mem_range_pointsMap_schematicLocus_iff B S hS F x).2
    ⟨Subfunctor.range qW, isOpenSubspace_range_of_isOpenImmersion W qW hqopen,
      isRepresentable_range_of_isOpenImmersion W qW hqopen, ?_⟩
  rw [range_pointsMap_ι_range B S hS qW]
  exact ⟨w, hw⟩

/-- **Stacks 07VV, the implication from the source.** If the source of an integral morphism of
algebraic spaces over `S` which is bijective on points is a scheme, then so is its target.

Let `α : h_V ⟶ X` be an affine open of the source through a given point. The morphism is
universally closed by Stacks 0415, hence closed on points, so the image of `|V|` is open and
cuts out an open subspace `W` of the target by part (1) of Tag 03BZ. Bijectivity identifies the
point set of `X ×_Y W` with `|V|`, so the two open subspaces of `X` agree and `X ×_Y W` is
affine; its projection to `W` is integral and surjective, so `W` is affine by Stacks 07VT and
the given point lies in the schematic locus of Stacks 03JH. -/
@[stacks 07VV "the implication from the source, granted the three hypotheses of Stacks 07VT: \
`h09YA`, the conclusion of Stacks 09YA that an integral morphism over a quasi-compact \
quasi-separated algebraic space is a directed limit of finite morphisms of finite presentation; \
`h07SQ`, the conclusion of Stacks 07SQ that a directed system with affine transition morphisms \
whose limit is affine has an affine stage; and `hFinitePresentation`, the case of Stacks 07VT \
in which the morphism is finite and of finite presentation. None is the universally quantified \
form of this conclusion: the first two conclude about inverse systems and the third about \
affineness of a target"]
theorem isRepresentable_of_isIntegralHom_of_bijective (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsIntegralHom B S hS f)
    (hbij : Function.Bijective (pointsMap B S hS F f)) (hFrep : F.IsRepresentable)
    (h09YA : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    G.IsRepresentable := by
  classical
  let _ : F.IsRepresentable := hFrep
  have hclosedmap : IsClosedMap (pointsMap B S hS F f) :=
    isClosed_of_universallyClosed B S hS hG f
      ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hF hG f).1 hf).2
  refine isRepresentable_of_surjective_pointsMap_schematicLocus B S hS hG fun y => ?_
  obtain ⟨x, hx⟩ := hbij.2 y
  obtain ⟨V, α, hVaff, hαopen, v, hv⟩ := exists_affineChart_isOpenImmersion_mem_range B S hS
    (Functor.reprX F) (Functor.reprW F) x
  have _ : Mono α := mono_of_presheaf_isOpenImmersion hαopen
  -- The open subspace of the target cut out by the image of the point set of `V`.
  have hVopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj V) α)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS α hαopen
  have himage : IsOpen (pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α)) :=
    isOpen_image_of_bijective_of_isClosedMap hbij hclosedmap hVopen
  set W : Subfunctor G := openSubspaceOfPoints B S hS G
    (pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α)) with hWdef
  have hW : IsOpenSubspace B S hS W :=
    isOpenSubspace_openSubspaceOfPoints B S hS hG _ himage
  have hWpts : Set.range (pointsMap B S hS W.toFunctor W.ι) =
      pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hWmem := Set.ext_iff.1 hWpts
  have hyW : y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) :=
    (hWmem y).2 ⟨x, ⟨v, hv⟩, hx⟩
  -- The base change of the morphism along that open subspace.
  have hQalg : IsAlgebraicSpace B S hS (pullback f W.ι) :=
    isAlgebraicSpace_pullback B S hS f W.ι hF hW.1 hG
  have hfstopen : IsOpenImmersion B S hS (pullback.fst f W.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback f W.ι).flip hW.2
  have _ : Mono (pullback.fst f W.ι) := mono_of_presheaf_isOpenImmersion hfstopen
  have hfstpts : Set.range (pointsMap B S hS (pullback f W.ι) (pullback.fst f W.ι)) =
      Set.range (pointsMap B S hS (yoneda.obj V) α) := by
    refine subset_antisymm ?_ ?_
    · rintro z ⟨w, rfl⟩
      obtain ⟨z', hz', hfz'⟩ := (hWmem _).1 (pointsMap_apply_comm B S hS pullback.condition w ▸
        ⟨_, rfl⟩ : pointsMap B S hS F f (pointsMap B S hS (pullback f W.ι)
          (pullback.fst f W.ι) w) ∈ Set.range (pointsMap B S hS W.toFunctor W.ι))
      exact hbij.1 hfz' ▸ hz'
    · rintro z ⟨w, rfl⟩
      obtain ⟨b, hb⟩ := (hWmem _).2 ⟨_, ⟨w, rfl⟩, rfl⟩
      obtain ⟨c, hc, -⟩ := exists_points_of_isPullback B S hS
        (IsPullback.of_hasPullback f W.ι) _ b hb.symm
      exact ⟨c, hc⟩
  have hrange : Subfunctor.range (pullback.fst f W.ι) = Subfunctor.range α := by
    have hP := range_pointsMap_ι_range B S hS (pullback.fst f W.ι)
    have hA := range_pointsMap_ι_range B S hS α
    refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_range_of_isOpenImmersion V α hαopen) ?_)
      (le_of_range_pointsMap_ι_subset B S hS
        (isOpenSubspace_range_of_isAlgebraicSpace B S hS hQalg _ hfstopen) ?_)
    · rw [hP, hA, hfstpts]
    · rw [hP, hA, hfstpts]
  have hQaff : IsAffineSpace B S hS (pullback f W.ι) := by
    refine ⟨V, hVaff, ⟨?_⟩⟩
    refine rangeIsoOfMono B S hS (pullback.fst f W.ι) ≪≫ ?_
    rw [hrange]
    exact (rangeIsoOfMono B S hS α).symm
  -- The projection to the open subspace is integral and surjective, so the subspace is affine.
  have hsndint : IsIntegralHom B S hS (pullback.snd f W.ι) :=
    isIntegralHom_pullback_snd B S hS f W.ι hf
  have hsndsurj : IsSurjective B S hS (pullback.snd f W.ι) := by
    intro b
    obtain ⟨z, -, hfz⟩ := (hWmem _).1 ⟨b, rfl⟩
    obtain ⟨c, -, hc⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback f W.ι) z b hfz
    exact ⟨c, hc⟩
  have hWaff : IsAffineSpace B S hS W.toFunctor :=
    isAffineSpace_of_isSurjective_of_universallyClosed B S hS (pullback.snd f W.ι) hQalg hW.1
      hsndsurj ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hQalg hW.1
        (pullback.snd f W.ι)).1 hsndint).2 hQaff h09YA h07SQ hFinitePresentation
  obtain ⟨T, -, ⟨eT⟩⟩ := hWaff
  exact (mem_range_pointsMap_schematicLocus_iff B S hS G y).2
    ⟨W, hW, isRepresentable_of_natIso _ eT.symm, hyW⟩

/-- **Stacks 07VV.** Let `f : X ⟶ Y` be an integral morphism of algebraic spaces over `S` which
induces a bijection `|X| → |Y|` on points. Then `X` is a scheme if and only if `Y` is a scheme.

The two implications are
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective` and
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom`; only the first uses bijectivity, and
only the first uses the three hypotheses of Stacks 07VT. -/
@[stacks 07VV "granted the three hypotheses of Stacks 07VT: `h09YA`, the conclusion of Stacks \
09YA that an integral morphism over a quasi-compact quasi-separated algebraic space is a \
directed limit of finite morphisms of finite presentation; `h07SQ`, the conclusion of Stacks \
07SQ that a directed system with affine transition morphisms whose limit is affine has an \
affine stage; and `hFinitePresentation`, the case of Stacks 07VT in which the morphism is \
finite and of finite presentation. None is the universally quantified form of this conclusion: \
the first two conclude about inverse systems and the third about affineness of a target"]
theorem isRepresentable_iff_of_isIntegralHom_of_bijective (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsIntegralHom B S hS f)
    (hbij : Function.Bijective (pointsMap B S hS F f))
    (h09YA : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    F.IsRepresentable ↔ G.IsRepresentable :=
  ⟨fun hFrep => isRepresentable_of_isIntegralHom_of_bijective B S hS hF hG f hf hbij hFrep
      h09YA h07SQ hFinitePresentation,
    fun hGrep => isRepresentable_of_isIntegralHom B S hS hF f hf hGrep⟩

/-! ### Stacks 07VU -/

/-- **Stacks 07VU**, due to Conrad–Lieblich–Olsson 3.1.12. If the reduction of an algebraic
space over `S` is a scheme, then the space itself is a scheme.

The inclusion of `AlgebraicGeometry.Space.reduction` is a closed immersion, hence integral by
Stacks 081Y, it is injective on points because it is a monomorphism, and it is surjective on
points by `AlgebraicGeometry.Space.surjective_pointsMap_ι_reduction`; Stacks 07VV applies. -/
@[stacks 07VU "granted the three hypotheses of Stacks 07VT: `h09YA`, the conclusion of Stacks \
09YA that an integral morphism over a quasi-compact quasi-separated algebraic space is a \
directed limit of finite morphisms of finite presentation; `h07SQ`, the conclusion of Stacks \
07SQ that a directed system with affine transition morphisms whose limit is affine has an \
affine stage; and `hFinitePresentation`, the case of Stacks 07VT in which the morphism is \
finite and of finite presentation. None is the universally quantified form of this conclusion: \
the first two conclude about inverse systems and the third about affineness of a target"]
theorem isRepresentable_of_isRepresentable_reduction {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hred : (reduction B S hS X hX).toFunctor.IsRepresentable)
    (h09YA : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X' →
      IsAffineSpace B S hS Y') :
    X.IsRepresentable := by
  have hclosed : IsClosedSubspace B S hS (reduction B S hS X hX) :=
    isClosedSubspace_reducedClosedSubspace B S hS X hX Set.univ isClosed_univ
  exact (isRepresentable_iff_of_isIntegralHom_of_bijective B S hS hclosed.1 hX
    (reduction B S hS X hX).ι (isIntegralHom_of_isClosedImmersion B S hS _ hclosed.2)
    ⟨pointsMap_injective_of_mono B S hS _, surjective_pointsMap_ι_reduction B S hS X hX⟩
    h09YA h07SQ hFinitePresentation).1 hred

end AlgebraicGeometry.Space

add_to_stacks 049D "an algebraic space whose reduction is a scheme is a scheme, granted the
  same three hypotheses `h09YA`, `h07SQ` and `hFinitePresentation` that the Stacks 07VU
  attribute of this declaration records."
  AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_reduction

end
