module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusBoundedChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# The schematic locus of a reasonable algebraic space is dense

Stacks 03JI says that a *reasonable* algebraic space over a scheme `S` has a dense open subspace
which is a scheme. This file passes from the hypothesis of the tag to the hypothesis of the
corollary already proved in
`StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusBoundedChart`, namely the existence of
*one* surjective étale chart by an affine scheme whose fibres are universally bounded, and
concludes the tag.

A reasonable space need not have a single such chart. What Stacks 03JT supplies — in the form
`AlgebraicGeometry.Space.exists_boundedEtaleCover_of_isReasonableSpace`, the implication
(2) ⇒ (1) — is a *jointly surjective family* `φ i : h_{U i} ⟶ X` of étale charts by affine
schemes with universally bounded fibres, and no member of it is surjective. The passage is
therefore in four steps.

* Replace `X` by the open subspace `X i` swept out by `φ i`, which is Stacks 06NF in the form
  `AlgebraicGeometry.Space.exists_isOpenSubspace_etaleImage`: the induced chart
  `ψ i : h_{U i} ⟶ X i` is *surjective* étale, by the same affine scheme.
* Carry the bound on the fibres from `φ i` to `ψ i`. The condition of Stacks 03JL quantifies
  over the field-valued points of the target, and `(X i).ι` is a monomorphism, so a field-valued
  point of `X i` is one of `X` with the same fibre; this is
  `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_factorsThrough`.
* Apply the corollary to each `X i`: its schematic locus contains a representable open subspace
  `L i` with dense point set.
* Glue by the same reduction of Stacks 03JH that the corollary itself uses,
  `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace`,
  which asks only for a nonempty representable open subspace inside every nonempty open subspace
  of `X`. Joint surjectivity makes the point sets of the `X i` cover `|X|`, so a nonempty open
  subspace `G` meets some `X i`; density of `L i` in `|X i|` then puts a point of `L i` over
  `|G|`, and the open subspace of `X` cut out by `|G| ∩ |L i|` is nonempty, contained in `G`, and
  representable because it is contained in the representable `L i`.

No new density argument is needed, and in particular neither the closed filtration of
Stacks 07S8 nor the induction on the degree bound that the source's proof runs: both are already
absent from the corollary, for the reason recorded in its implementation notes.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_factorsThrough`: a morphism to a
  subfunctor has universally bounded fibres as soon as its composite with the inclusion does.
* `AlgebraicGeometry.Space.isOpenSubspace_range_ι_comp_ι` and
  `AlgebraicGeometry.Space.isRepresentable_range_ι_comp_ι`: an open subspace of an open subspace
  of `X`, read as a subfunctor of `X`.
* `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isReasonableSpace`:
  **Stacks 03JI**.

## Implementation notes

Pushing an open subspace `L` of an open subspace `Y` of `X` back to a subfunctor of `X` is the
upward counterpart of Stacks 02YX, which goes downward, and is not an instance of it. It is done
here as the range of `L.ι ≫ Y.ι`: that composite is a monomorphism, so
`CategoryTheory.Subfunctor.toRange` is an isomorphism and both algebraicity and representability
transport along it, while the inclusion of the range is the composite read through that
isomorphism, hence an open immersion by
`AlgebraicGeometry.Space.isOpenImmersion_comp`.

The point sets of the `X i` cover `|X|` by
`AlgebraicGeometry.Space.points_cover_of_isLocallySurjective_sigma_desc`, applied to the family
of subfunctors `X i`; local surjectivity of the induced morphism out of their coproduct follows
from that of `Sigma.desc φ` because the latter factors through it, each `φ i` factoring as
`ψ i ≫ (X i).ι`.

## References

* [Stacks Project, Tag 02YX](https://stacks.math.columbia.edu/tag/02YX)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transporting a bound on the fibres to a subfunctor of the target -/

/-- **The bound of Stacks 03JL along a morphism factored through a subfunctor.** If a morphism
`φ : h_U ⟶ X` from an object of the site factors as `ψ ≫ Y.ι` through a subfunctor `Y` of `X`,
and the fibres of `φ` are universally bounded, then so are the fibres of `ψ`.

The condition of Stacks 03JL quantifies over the field-valued points of the target, and `Y.ι` is
a monomorphism. So a field-valued point `ξ` of `Y` gives the field-valued point `ξ ≫ Y.ι` of `X`
over the same object of the site, the fibre of `φ` above it is a fibre of `ψ` above `ξ` by
`CategoryTheory.isPullback_of_comp_mono`, and the bound and the degree are unchanged. -/
theorem hasUniversallyBoundedFibers_of_factorsThrough
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y : Subfunctor X} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X} {ψ : yoneda.obj U ⟶ Y.toFunctor} (hfac : ψ ≫ Y.ι = φ)
    (hφ : HasUniversallyBoundedFibers B S hS U φ) :
    HasUniversallyBoundedFibers B S hS U ψ := by
  subst hfac
  obtain ⟨n, hn⟩ := hφ
  refine ⟨n, fun k _ T e ξ => ?_⟩
  obtain ⟨V, p, i, r, hrn, hrank, hsq⟩ := hn k T e (ξ ≫ Y.ι)
  exact ⟨V, p, i, r, hrn, hrank, _root_.CategoryTheory.isPullback_of_comp_mono Y.ι hsq⟩

/-! ### An open subspace of an open subspace, read inside the ambient presheaf -/

section Upward

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y : Subfunctor X} {L : Subfunctor Y.toFunctor}

/-- The composite inclusion of an iterated subfunctor is a monomorphism. -/
private theorem mono_ι_comp_ι : Mono (L.ι ≫ Y.ι) := mono_comp _ _

/-- A subfunctor of a subfunctor of `X`, read as a subfunctor of `X`, has the same underlying
presheaf: the range of the composite inclusion is isomorphic to it. -/
private noncomputable def rangeIsoOfIotaCompIota :
    L.toFunctor ≅ (Subfunctor.range (L.ι ≫ Y.ι)).toFunctor :=
  have _ : Mono (L.ι ≫ Y.ι) := mono_ι_comp_ι B S hS
  asIso (Subfunctor.toRange (L.ι ≫ Y.ι))

/-- The inclusion of the range of the composite inclusion, read through
`AlgebraicGeometry.Space.rangeIsoOfIotaCompIota`, is that composite. -/
private theorem rangeIsoOfIotaCompIota_inv_comp :
    (rangeIsoOfIotaCompIota B S hS (Y := Y) (L := L)).inv ≫ (L.ι ≫ Y.ι) =
      (Subfunctor.range (L.ι ≫ Y.ι)).ι :=
  (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι (L.ι ≫ Y.ι)).symm

/-- **An open subspace of an open subspace of `X` is an open subspace of `X`.** Its underlying
subfunctor of `X` is the range of the composite of the two inclusions.

This is the upward counterpart of Stacks 02YX. The range is an algebraic space because it is
isomorphic to `L.toFunctor`, and its inclusion into `X` is, through that isomorphism, the
composite `L.ι ≫ Y.ι`, which is an open immersion of presheaves by
`AlgebraicGeometry.Space.isOpenImmersion_comp`. -/
theorem isOpenSubspace_range_ι_comp_ι (hY : IsOpenSubspace B S hS Y)
    (hL : IsOpenSubspace B S hS L) :
    IsOpenSubspace B S hS (Subfunctor.range (L.ι ≫ Y.ι)) := by
  refine ⟨isAlgebraicSpace_of_iso B S hS
    (rangeIsoOfIotaCompIota B S hS (Y := Y) (L := L)) hL.1, ?_⟩
  have hpre := MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
    (rangeIsoOfIotaCompIota B S hS (Y := Y) (L := L)).inv (L.ι ≫ Y.ι)
    (isOpenImmersion_comp B S hS L.ι Y.ι hL.2 hY.2)
  rwa [rangeIsoOfIotaCompIota_inv_comp] at hpre

/-- A representable subfunctor of a subfunctor of `X` stays representable when read as a
subfunctor of `X`. -/
theorem isRepresentable_range_ι_comp_ι (hL : L.toFunctor.IsRepresentable) :
    (Subfunctor.range (L.ι ≫ Y.ι)).toFunctor.IsRepresentable :=
  have _ := hL
  isRepresentable_of_natIso _ (rangeIsoOfIotaCompIota B S hS (Y := Y) (L := L))

/-- The point set of an iterated open subspace, read inside `X`, is the image of the point set
of the inner one. -/
theorem range_pointsMap_ι_range_ι_comp_ι :
    Set.range (pointsMap B S hS (Subfunctor.range (L.ι ≫ Y.ι)).toFunctor
        (Subfunctor.range (L.ι ≫ Y.ι)).ι) =
      Set.range (pointsMap B S hS L.toFunctor (L.ι ≫ Y.ι)) := by
  have : Mono (L.ι ≫ Y.ι) := mono_ι_comp_ι B S hS
  exact range_pointsMap_ι_range B S hS (L.ι ≫ Y.ι)

end Upward

/-! ### The dense schematic locus of a reasonable algebraic space -/

/-- **Stacks 03JI.** The schematic locus of a reasonable algebraic space is dense: a reasonable
algebraic space `X` over a scheme `S` has a representable open subspace whose point set is dense
in `|X|`.

Reasonableness is condition (2) of Stacks 03JT, so Stacks 03JT in the form
`AlgebraicGeometry.Space.exists_boundedEtaleCover_of_isReasonableSpace` gives a jointly
surjective family of étale charts `φ i` by affine schemes with universally bounded fibres. No
member of the family is surjective, so the corollary does not apply to `X` directly. Replacing
`X` by the open subspace `X i` swept out by `φ i` — Stacks 06NF — makes the induced chart
`ψ i : h_{U i} ⟶ X i` surjective, and the bound passes from `φ i` to `ψ i` because `(X i).ι` is
a monomorphism. The corollary then gives in each `X i` a representable open subspace `L i` with
dense point set.

Stacks 03JH, in the form
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace`,
reduces the conclusion to finding a nonempty representable open subspace inside every nonempty
open subspace `G` of `X`. The point sets of the `X i` cover `|X|`, so some `|X i|` meets `|G|`;
the preimage of `|G|` in `|X i|` is then a nonempty open set, which by density meets `|L i|`. So
`|G| ∩ |L i|` is nonempty, and the open subspace of `X` it cuts out is contained in `G` and
contained in `L i`, hence representable by
`AlgebraicGeometry.Space.isRepresentable_of_le_of_isRepresentable`. -/
@[stacks 03JI]
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_isReasonableSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hreasonable : IsReasonableSpace B S hS X) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) := by
  classical
  -- Stacks 03JT, (2) ⇒ (1): a jointly surjective family of bounded affine étale charts.
  obtain ⟨I, U, φ, hloc, hdata⟩ :=
    exists_boundedEtaleCover_of_isReasonableSpace B S hS X hX hreasonable
  -- Stacks 06NF: the open subspace swept out by each chart, with a surjective chart of its own.
  choose Y ψ hYopen hψfac hψsurj hψetale _hYpts using fun i =>
    exists_isOpenSubspace_etaleImage B S hS hX (U i) (φ i) (hdata i).2.1
  -- The corollary of Stacks 03JI at each of the open subspaces.
  choose L hLopen hLrep hLdense using fun i =>
    exists_denseRange_isRepresentable_isOpenSubspace_of_boundedAffineChart B S hS
      (hYopen i).1 (hdata i).1 (ψ i) (hψsurj i) (hψetale i)
      (hasUniversallyBoundedFibers_of_factorsThrough B S hS (hψfac i) (hdata i).2.2)
  -- Each `L i`, read as a subfunctor of `X`.
  set M : I → Subfunctor X := fun i => Subfunctor.range ((L i).ι ≫ (Y i).ι)
  have hMopen : ∀ i, IsOpenSubspace B S hS (M i) := fun i =>
    isOpenSubspace_range_ι_comp_ι B S hS (hYopen i) (hLopen i)
  have hMrep : ∀ i, (M i).toFunctor.IsRepresentable := fun i =>
    isRepresentable_range_ι_comp_ι B S hS (hLrep i)
  -- Joint surjectivity makes the point sets of the open subspaces cover `|X|`.
  have hcover : (⋃ i, Set.range (pointsMap B S hS (Y i).toFunctor (Y i).ι)) = Set.univ := by
    have hfac : (Limits.Sigma.map fun i => ψ i) ≫ (Sigma.desc fun i => (Y i).ι) =
        Sigma.desc φ := by
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Sigma.ι_comp_desc,
        Sigma.ι_comp_desc, hψfac i]
    have _ := hloc
    exact points_cover_of_isLocallySurjective_sigma_desc B S hS X I Y
      (Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hfac)
  -- Stacks 03JH reduces the conclusion to local nonemptiness.
  refine exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace B S hS hX ?_
  rintro G hG ⟨x, hxG⟩
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.1 (Set.eq_univ_iff_forall.1 hcover x)
  -- Density of `L i` inside `X i` puts a point of `L i` over `|G|`.
  have hGopen : IsOpen (Set.range (pointsMap B S hS G.toFunctor G.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS G.ι hG.2
  have hpre : IsOpen (pointsMap B S hS (Y i).toFunctor (Y i).ι ⁻¹'
      Set.range (pointsMap B S hS G.toFunctor G.ι)) :=
    hGopen.preimage (continuous_pointsMap B S hS (Y i).ι)
  have hyG : y ∈ pointsMap B S hS (Y i).toFunctor (Y i).ι ⁻¹'
      Set.range (pointsMap B S hS G.toFunctor G.ι) := by
    rwa [Set.mem_preimage, hy]
  obtain ⟨z, hzG, l, hzl⟩ := dense_iff_inter_open.1 (hLdense i) _ hpre ⟨y, hyG⟩
  have hmeet : (Set.range (pointsMap B S hS G.toFunctor G.ι) ∩
      Set.range (pointsMap B S hS (M i).toFunctor (M i).ι)).Nonempty := by
    refine ⟨pointsMap B S hS (Y i).toFunctor (Y i).ι z, hzG, ?_⟩
    exact (range_pointsMap_ι_range_ι_comp_ι B S hS (Y := Y i) (L := L i)).ge
      ⟨l, by rw [pointsMap_comp, Function.comp_apply, hzl]⟩
  -- The open subspace of `X` cut out by the intersection.
  set W := Set.range (pointsMap B S hS G.toFunctor G.ι) ∩
    Set.range (pointsMap B S hS (M i).toFunctor (M i).ι)
  have hWopen : IsOpen W :=
    hGopen.inter (isOpen_range_pointsMap_of_isOpenImmersion B S hS (M i).ι (hMopen i).2)
  have hWsub := isOpenSubspace_openSubspaceOfPoints B S hS hX W hWopen
  have hrange := range_pointsMap_ι_openSubspaceOfPoints B S hS W
  refine ⟨openSubspaceOfPoints B S hS X W,
    le_of_range_pointsMap_ι_subset B S hS hG (hrange.subset.trans Set.inter_subset_left),
    hWsub, isRepresentable_of_le_of_isRepresentable B S hS hWsub
      (le_of_range_pointsMap_ι_subset B S hS (hMopen i)
        (hrange.subset.trans Set.inter_subset_right)) (hMrep i), ?_⟩
  rwa [hrange]

end AlgebraicGeometry.Space

end
