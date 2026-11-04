module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianApproximationInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeApproximationOfSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeFinitePresentationApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints

/-!
# Approximation by spaces of finite presentation, for spaces with small atlases

Stacks 09NS writes a quasi-compact quasi-separated algebraic space `X` over a quasi-separated
algebraic space `Y` as a directed limit of algebraic spaces of finite presentation over `Y` with
affine transition morphisms. This file proves it when `X` and `Y` have étale atlases smaller than
the cofinality of the size cutoff of the site, which is what absolute Noetherian approximation
(`AlgebraicGeometry.Space.hasSmallNoetherianApproximation_of_etaleAtlas`) needs.

The proof is the one of the Stacks project: the image of `X` lies in a quasi-compact open subspace
`V` of `Y` (viewed over `Spec ℤ`); `X ⟶ V` is a limit of morphisms of quasi-separated algebraic
spaces of finite type over `Spec ℤ` (Stacks 0GS3, from the small approximations of `X` and `V`);
base changing the stages back to `Y` concludes
(`AlgebraicGeometry.Space.exists_isLimit_finitePresentation_of_hasRelativeApproximation`).

## Main results

* `AlgebraicGeometry.Space.exists_quasiCompact_openSubspace_factor`: a morphism from a
  quasi-compact algebraic space factors through a quasi-compact open subspace of the target.
* `AlgebraicGeometry.Space.exists_isLimit_finitePresentation_of_small`.

## References

* [Stacks Project, Tag 09NS](https://stacks.math.columbia.edu/tag/09NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism from a quasi-compact algebraic space factors through a quasi-compact open
subspace of the target.** The image of `|X|` in `|Y|` is compact; it is covered by finitely many
open compact subsets of `|Y|` (Stacks 03E4 and the local compactness of `|Y|`), whose union is
the point set of a quasi-compact open subspace (Stacks 03BZ), through which `f` factors by Stacks
03IE. -/
theorem exists_quasiCompact_openSubspace_factor {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXqc : IsQuasiCompactSpace B S hS X) (f : X ⟶ Y) :
    ∃ V : Subfunctor Y, IsOpenSubspace B S hS V ∧ (∃ fV : X ⟶ V.toFunctor, fV ≫ V.ι = f) ∧
      IsQuasiCompactSpace B S hS V.toFunctor := by
  classical
  let := pointTopology B S hS X
  let := pointTopology B S hS Y
  have _ : CompactSpace (points B S hS X) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS X hX).mp hXqc
  have hK : IsCompact (Set.range (pointsMap B S hS X f)) :=
    Set.image_univ ▸ isCompact_univ.image (continuous_pointsMap B S hS f)
  choose N hNo hNc hNy using fun y : points B S hS Y =>
    ((hasBasis_nhds_isOpen_isCompact B S hS Y hY y).mem_iff.mp Filter.univ_mem).imp fun _ h => h.1
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover N hNo
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hNy y⟩)
  let W : Set (points B S hS Y) := ⋃ i ∈ t, N i
  have hWo : IsOpen W := isOpen_biUnion fun i _ => hNo i
  have hWc : IsCompact W := t.finite_toSet.isCompact_biUnion fun i _ => hNc i
  let V := openSubspaceOfPoints B S hS Y W
  have hV : IsOpenSubspace B S hS V := isOpenSubspace_openSubspaceOfPoints B S hS hY W hWo
  have hrange : Set.range (pointsMap B S hS V.toFunctor V.ι) = W :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS W
  exact ⟨V, hV, (factorsThrough_openSubspace_iff_points B S hS hY hX V hV f).mpr (hrange ▸ ht),
    isQuasiCompactSpace_of_isCompact_range B S hS hY hV (hrange ▸ hWc)⟩

/-- **A surjective étale atlas of an algebraic space over `S` gives one of its view over
`Spec ℤ`, by the same scheme.** -/
theorem exists_atlas_viewOverIntegers {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ X)
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    ∃ (U' : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)
      (q' : yoneda.obj U' ⟶ viewOverIntegers B S hS B.contains_terminal X),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal)).presheaf q' ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal)).presheaf q' ∧
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal).obj U' =
        (BigFppfOver.toScheme B S hS).obj U := by
  let k : B.obj hS ⟶ B.obj B.contains_terminal := ⟨terminal.from S⟩
  have := MorphismProperty.RespectsIso.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) B.contains_terminal)
  exact ⟨(Over.map k).obj U, ((OverShriek.relocalizeYonedaIso k).app U).inv ≫
    (OverShriek.relocalizePresheafFunctor k).map q,
    MorphismProperty.RespectsIso.precomp _ _ _
      (OverShriek.presheaf_map_relocalize k (fun _ hj => hj) hqs),
    MorphismProperty.RespectsIso.precomp _ _ _
      (OverShriek.presheaf_map_relocalize k (fun _ hj => hj) hqe), rfl⟩

/-- **Stacks 09NS, for spaces with small étale atlases.** Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` with `X` quasi-compact and quasi-separated and `Y` quasi-separated, and
suppose `X` and `Y` have surjective étale atlases by schemes smaller than the cofinality of the
size cutoff of the site. Then `X` is the limit of a directed inverse system of algebraic spaces of
finite presentation over `Y` with affine transition morphisms over `Y`. -/
theorem exists_isLimit_finitePresentation_of_small {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (hXsmall : ∃ (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ X),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      ((BigFppfOver.toScheme B S hS).obj U).size < B.cutoff.ord.cof)
    (hYsmall : ∃ (W : BigFppfOver B S hS) (b : yoneda.obj W ⟶ Y),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      ((BigFppfOver.toScheme B S hS).obj W).size < B.cutoff.ord.cof) :
    ∃ (I : Type (u + 1)) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (D : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      (t : D ⟶ (Functor.const Iᵒᵖ).obj Y) (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X p)),
      (p ≫ t = (Functor.const Iᵒᵖ).map f) ∧
        (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
        (∀ i, IsFinitePresentation B S hS (t.app i)) ∧
        (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B S hS (D.map g)) := by
  classical
  let hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let k : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let L := OverShriek.relocalizePresheafFunctor k
  have hXZ := isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ k X hX
  have hYZ := isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ k Y hY
  have hXZqc := isQuasiCompactSpace_relocalize B S hS hZ k hXqc
  have hXZqs := isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ X hXqs
  have hYZqs := isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ Y hYqs
  obtain ⟨V, hV, ⟨fV, hfV⟩, hVqc⟩ :=
    exists_quasiCompact_openSubspace_factor B (⊤_ Scheme.{u}) hZ hXZ hYZ hXZqc (L.map f)
  obtain ⟨U, q, hqs, hqe, hU⟩ := hXsmall
  obtain ⟨UX, qX, hqXs, hqXe, hUX⟩ := exists_atlas_viewOverIntegers B S hS q hqs hqe
  obtain ⟨W, b, hbs, hbe, hW⟩ := hYsmall
  obtain ⟨WY, bY, hbYs, hbYe, hWY⟩ := exists_atlas_viewOverIntegers B S hS b hbs hbe
  -- an atlas of `V`: the open subscheme of the atlas of `Y` over `V`
  have hO := hV.2
  have hsq := hO.rep.isPullback bY
  have _ : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (hO.rep.snd bY)) := hO.property_snd bY
  have hVqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ V.toFunctor :=
    isAbsolutelyQuasiSeparated_of_mono _ _ _ _ hV.1 V.ι inferInstance hYZqs
  have hAX := hasSmallNoetherianApproximation_of_etaleAtlas hXZ hXZqc hXZqs UX qX hqXs
    ((isEtale_iff_presheaf_of_yoneda B (⊤_ Scheme.{u}) hZ qX).mpr hqXe) (hUX ▸ hU)
  have hAV := hasSmallNoetherianApproximation_of_etaleAtlas hV.1 hVqc hVqs _ (hO.rep.fst bY)
    (presheaf_of_isPullback B (⊤_ Scheme.{u}) hZ hsq.flip hbYs)
    ((isEtale_iff_presheaf_of_yoneda B (⊤_ Scheme.{u}) hZ _).mpr
      (presheaf_of_isPullback B (⊤_ Scheme.{u}) hZ hsq.flip hbYe))
    ((Scheme.size_le_of_isOpenImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (hO.rep.snd bY))).trans_lt (hWY ▸ hW))
  exact exists_isLimit_finitePresentation_of_hasRelativeApproximation B S hS f hX hY hYqs V hV
    hVqc fV hfV (hasRelativeApproximation_of_hasSmallNoetherianApproximation B hZ fV hXZ hAX hAV)

end AlgebraicGeometry.Space

end
