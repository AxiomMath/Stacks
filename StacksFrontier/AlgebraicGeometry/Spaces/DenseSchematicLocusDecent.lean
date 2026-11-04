module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingAffineOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusBoundedChart

/-!
# A decent algebraic space has a dense schematic open subspace

Stacks 086U, Rydh's theorem: a decent algebraic space over a scheme has a dense open subspace
which is a scheme. This file proves it, by the source's own route.

By Stacks 03JH the question is local, in the precise sense that it suffices to find, inside
every nonempty open subspace `G` of `X`, a nonempty representable open subspace. Inside `G`
there is an affine étale chart of `X`: the base change of an étale atlas of `X` along the
inclusion of `G` is an open subscheme of the atlas, and a nonempty affine open `V` of it gives
an étale chart `φ : h_V ⟶ X` whose image lies in `G`.

Stacks 086R, applied to the relation of `φ`, now stratifies `V` by the degree of the fibre of
`φ`: there are opens `V = Z₀ ⊇ Z₁ ⊇ Z₂ ⊇ …` with a field-valued point of `V` lying in `Zᵈ`
exactly when the fibre of `φ` above the point of `X` it carries has degree at least `d`. One of
two things happens.

* Some nonempty affine open `W` of `V` misses `Zₙ`. Then above every point of the open subspace
  swept out by `W` the fibre of `φ` has degree below `n`, so that chart has universally bounded
  fibres in the sense of Stacks 03JL, and the corollary of Stacks 03JI for a single bounded
  affine chart gives a dense representable open subspace of it — in particular a nonempty one,
  which transports to a representable open subspace of `X` inside `G`.
* Otherwise there is a descending chain of nonempty affine opens `V₀ ⊇ V₁ ⊇ …` with `Vₙ ⊆ Zₙ`.
  The limit of such a chain is nonempty, which is Stacks 01Z2, so some point of `V` lies in
  every `Zₙ`, and the fibre of `φ` above the point of `X` it carries has degree at least every
  `n`. That contradicts decency, which bounds that degree.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_nonempty_of_isDecentSpace`:
  every nonempty open subspace of a decent algebraic space over `S` contains a nonempty
  representable open subspace. This is the local nonemptiness statement which the reduction of
  `StacksFrontier/AlgebraicGeometry/Spaces/DenseSchematicLocus.lean` carried as a hypothesis.
* `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace`
  is **Stacks 086U**.

## Implementation notes

The dichotomy is `AlgebraicGeometry.exists_isAffineOpen_disjoint_or_exists_antitone_isAffineOpen`
and does not need the family of opens to be antitone; what it needs is that the zeroth member
be everything, which the chain of Stacks 086R satisfies.

Two shapes of a field-valued point occur and have to be reconciled. Stacks 03JL, and with it
the conclusion the corollary of Stacks 03JI consumes, quantifies over an object of the site
together with an *isomorphism* to the spectrum of a field; Stacks 03BU, and with it the
stratification, asks for the spectrum on the nose. The comparison is
`AlgebraicGeometry.Space.exists_fieldValuedPoint_degreeGe_iff`.

The corollary of Stacks 03JI returns a representable open subspace of the auxiliary space swept
out by the chart, and the statement being proved asks for one of `X`; the passage is
`AlgebraicGeometry.Space.exists_isOpenSubspace_isRepresentable_of_isOpenSubspace`.

Decency enters at exactly one point, through
`AlgebraicGeometry.Space.exists_not_fibre_degree_ge_of_isDecentSpace`, and only to rule out the
second alternative of the dichotomy. It is not used anywhere else, which is why the chart may
be chosen before decency is invoked.

## References

* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 086R](https://stacks.math.columbia.edu/tag/086R)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 01Z2](https://stacks.math.columbia.edu/tag/01Z2)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Precomposing an étale morphism out of a represented presheaf with the inclusion of a Zariski
open of the source gives an étale morphism. -/
private theorem presheaf_etale_yoneda_map_opensObjectι_comp {U : BigFppfOver B S hS}
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {φ : yoneda.obj U ⟶ X}
    (hφ : (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf φ) :
    (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (opensObjectι B S hS U V) ≫ φ) := by
  have hEcomp : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun f g hf hg => by
      have : Etale f := hf
      have : Etale g := hg
      exact Etale.etale_comp f g⟩
  refine MorphismProperty.IsStableUnderComposition.comp_mem
    (P := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf) _ _ ?_ hφ
  refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS (@Etale.{u}) _).2 ?_
  have : _root_.AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B S hS).map (opensObjectι B S hS U V)) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion V.ι)
  infer_instance

/-- **The local nonemptiness statement of Stacks 086U.** Every nonempty open subspace of a
decent algebraic space over `S` contains a nonempty representable open subspace.

This is the hypothesis `hnonempty` which the reduction of
`StacksFrontier/AlgebraicGeometry/Spaces/DenseSchematicLocus.lean` carries, and it is the whole
geometric content of Stacks 086U; see the module documentation for the argument. -/
theorem exists_isRepresentable_isOpenSubspace_nonempty_of_isDecentSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (G : Subfunctor X) (hG : IsOpenSubspace B S hS G)
    (hGne : (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty) :
    ∃ H : Subfunctor X, H ≤ G ∧ IsOpenSubspace B S hS H ∧
      H.toFunctor.IsRepresentable ∧
      (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
  classical
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hEcomp : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun f g hf hg => by
      have : Etale f := hf
      have : Etale g := hg
      exact Etale.etale_comp f g⟩
  have hPcomp : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have hPbc : P.IsStableUnderBaseChange := by
    refine ⟨?_⟩
    intro A C C' T f g f' g' sq hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale.{u}) (sq.map (BigFppfOver.toScheme B S hS)) hg
  have hPpcomp : P.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition P
  obtain ⟨U, atl, hatlsurj, hatletale⟩ := hX.exists_atlas
  -- The base change of the atlas along the inclusion of `G`: an open subscheme of the atlas.
  have hGrep := hG.2.rep
  have hsqG := hGrep.isPullback atl
  have hprOpen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hGrep.snd atl)) := hG.2.property_snd atl
  -- The chart `φ : h_P ⟶ X` through `G`.
  have hφetale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (hGrep.snd atl) ≫ atl) := by
    have hpr : (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (hGrep.snd atl)) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS (@Etale.{u})
        (hGrep.snd atl)).2 (by
          have := hprOpen
          infer_instance)
    exact MorphismProperty.IsStableUnderComposition.comp_mem (P := P.presheaf) _ _
      hpr hatletale
  have hφfac : yoneda.map (hGrep.snd atl) ≫ atl = hGrep.fst atl ≫ G.ι := (hsqG.w).symm
  -- `|h_P|` is nonempty, because the base change of a surjective chart is surjective.
  have hfstsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hGrep.fst atl) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@Surjective.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback hsqG.flip hatlsurj
  have hPne : Nonempty ((BigFppfOver.toScheme B S hS).obj (hGrep.pullback atl)) := by
    obtain ⟨x, hx⟩ := hGne
    obtain ⟨y, -⟩ := hx
    obtain ⟨z, -⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS G.toFunctor hG.1 _
      (hGrep.fst atl)).1 hfstsurj y
    exact ⟨pointsToScheme B S hS _ z⟩
  -- A nonempty affine open `V` of it, and the affine étale chart it carries.
  obtain ⟨V, hVaff, hVmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := hPne.some) (U := ⊤) trivial
  have hVne : ((V : Set ((BigFppfOver.toScheme B S hS).obj (hGrep.pullback atl)))).Nonempty :=
    ⟨hPne.some, hVmem⟩
  have hVaffine : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (opensObject B S hS (hGrep.pullback atl) V)) := hVaff
  have hVnonempty : Nonempty ((BigFppfOver.toScheme B S hS).obj
      (opensObject B S hS (hGrep.pullback atl) V)) := ⟨⟨hPne.some, hVmem⟩⟩
  set φ := yoneda.map (opensObjectι B S hS (hGrep.pullback atl) V) ≫
    (yoneda.map (hGrep.snd atl) ≫ atl) with hφdef
  have hφ₁etale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ :=
    presheaf_etale_yoneda_map_opensObjectι_comp B S hS V hφetale
  -- The image of `φ` lies in `G`.
  have hφrange : Set.range (pointsMap B S hS
      (yoneda.obj (opensObject B S hS (hGrep.pullback atl) V)) φ) ⊆
      Set.range (pointsMap B S hS G.toFunctor G.ι) := by
    rw [hφdef, hφfac, ← Category.assoc, pointsMap_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  -- Stacks 086R on the relation of `φ`.
  obtain ⟨Z, hZ0, -, hZdeg⟩ := exists_antitone_opens_of_etale_chart B S hS φ hX hφ₁etale
    (isFlat_of_presheafEtale B S hS hφ₁etale)
    (isLocallyOfFinitePresentation_of_presheafEtale B S hS hφ₁etale)
    (isSeparated_of_scheme_isSeparated B S hS inferInstance φ)
    (isLocallyQuasiFinite_of_presheafEtale B S hS hφ₁etale)
  -- A field-valued point of the chart at a given point of its underlying scheme.
  have hrep (x : (BigFppfOver.toScheme B S hS).obj
      (opensObject B S hS (hGrep.pullback atl) V)) :
      ∃ q : FieldValuedPoint B S hS
        (yoneda.obj (opensObject B S hS (hGrep.pullback atl) V)),
        schemePoint B S hS (opensObject B S hS (hGrep.pullback atl) V) q = x := by
    obtain ⟨y, hy⟩ := surjective_pointsToScheme B S hS
      (opensObject B S hS (hGrep.pullback atl) V) x
    obtain ⟨q, rfl⟩ := Quot.exists_rep y
    exact ⟨q, hy⟩
  rcases exists_isAffineOpen_disjoint_or_exists_antitone_isAffineOpen Z hZ0 with
    ⟨n, W, hWaff, hWne, hWZ⟩ | ⟨Vc, hVcanti, hVcaff, hVcne, hVcZ⟩
  · -- The bounded case: the open subspace swept out by `W` has bounded fibres.
    have hWetale := presheaf_etale_yoneda_map_opensObjectι_comp B S hS W hφ₁etale
    obtain ⟨X₂, ψ₂, hX₂open, hψ₂fac, hψ₂surj, hψ₂etale, hX₂image⟩ :=
      exists_isOpenSubspace_etaleImage B S hS hX
        (opensObject B S hS (opensObject B S hS (hGrep.pullback atl) V) W) _ hWetale
    -- Above every field-valued point of `X₂` the fibre of `φ` has degree below `n`.
    have hbound : ∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
        ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) →
        ∀ ξ : yoneda.obj T ⟶ X₂.toFunctor, ∃ r : ℕ, r < n ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map
            ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd (ξ ≫ X₂.ι))) r := by
      intro k _ T e ξ
      obtain ⟨p, hpmem, hpiff⟩ :=
        exists_fieldValuedPoint_degreeGe_iff B S hS hX φ k T e (ξ ≫ X₂.ι)
      -- The point of `p` lies in the image of `W`.
      have hpW : p.class B S hS X ∈ Set.range (pointsMap B S hS
          (yoneda.obj (opensObject B S hS (opensObject B S hS (hGrep.pullback atl) V) W))
          (yoneda.map (opensObjectι B S hS
            (opensObject B S hS (hGrep.pullback atl) V) W) ≫ φ)) := by
        rw [← hX₂image]
        obtain ⟨z, hz⟩ := hpmem
        refine ⟨pointsMap B S hS (yoneda.obj T) ξ z, ?_⟩
        rw [← hz, pointsMap_comp]
        rfl
      obtain ⟨y, hy⟩ := hpW
      obtain ⟨q₂, rfl⟩ := Quot.exists_rep y
      set q := FieldValuedPoint.map B S hS
        (yoneda.obj (opensObject B S hS (opensObject B S hS (hGrep.pullback atl) V) W))
        (yoneda.map (opensObjectι B S hS
          (opensObject B S hS (hGrep.pullback atl) V) W)) q₂ with hqdef
      have hqclass : pointsMap B S hS
          (yoneda.obj (opensObject B S hS (hGrep.pullback atl) V)) φ
          (q.class B S hS (yoneda.obj (opensObject B S hS (hGrep.pullback atl) V))) =
          p.class B S hS X := by
        rw [← hy, pointsMap_comp]
        rfl
      have hqW : schemePoint B S hS (opensObject B S hS (hGrep.pullback atl) V) q ∈ W := by
        rw [hqdef, schemePoint_map_yoneda]
        exact (schemePoint B S hS
          (opensObject B S hS (opensObject B S hS (hGrep.pullback atl) V) W) q₂).property
      have hdeg0 : DegreeGe ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
            (yonedaEquiv.symm p.value))) 0 :=
        (degreeGe_iff_mem_of_etale_chart B S hS φ hX (Z 0) 0 (hZdeg 0) q p hqclass).1
          (by rw [hZ0]; trivial)
      have hdegn : ¬ DegreeGe ((BigFppfOver.toScheme B S hS).map
          ((relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ).snd
            (yonedaEquiv.symm p.value))) n := fun hcon =>
        hWZ _ hqW ((degreeGe_iff_mem_of_etale_chart B S hS φ hX (Z n) n (hZdeg n) q p
          hqclass).2 hcon)
      exact exists_rank_lt_of_degree_ge_zero_of_not_degree_ge _ n
        ((degreeGe_iff _ 0).1 ((hpiff 0).2 hdeg0))
        (fun hcon => hdegn ((hpiff n).1 ((degreeGe_iff _ n).2 hcon)))
    have hbdd := hasUniversallyBoundedFibers_of_rank_lt B S hS hX φ W ψ₂ hψ₂fac n hbound
    have hWaffine : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (opensObject B S hS (opensObject B S hS (hGrep.pullback atl) V) W)) := hWaff
    obtain ⟨H, hHopen, hHrep, hHdense⟩ :=
      exists_denseRange_isRepresentable_isOpenSubspace_of_boundedAffineChart B S hS
        hX₂open.1 hWaffine ψ₂ hψ₂surj hψ₂etale hbdd
    -- `|X₂|` is nonempty, so the dense point set of `H` is nonempty.
    have hX₂ne : Nonempty (points B S hS X₂.toFunctor) := by
      obtain ⟨w, hw⟩ := hWne
      exact ⟨pointsMap B S hS _ ψ₂
        ((pointsEquivScheme B S hS (opensObject B S hS
          (opensObject B S hS (hGrep.pullback atl) V) W)).symm ⟨w, hw⟩)⟩
    have hHne : (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty := by
      obtain ⟨h⟩ := hHdense.nonempty
      exact ⟨pointsMap B S hS H.toFunctor H.ι h, h, rfl⟩
    obtain ⟨K, hKopen, hKrep, hKimage⟩ :=
      exists_isOpenSubspace_isRepresentable_of_isOpenSubspace B S hS hX hX₂open hHopen hHrep
    refine ⟨K, ?_, hKopen, hKrep, ?_⟩
    · refine le_of_range_pointsMap_ι_subset B S hS hG ?_
      rw [hKimage, pointsMap_comp, Set.range_comp]
      refine Set.Subset.trans (Set.image_subset_range _ _) ?_
      rw [hX₂image, pointsMap_comp, Set.range_comp]
      exact Set.Subset.trans (Set.image_subset_range _ _) hφrange
    · rw [hKimage, pointsMap_comp, Set.range_comp]
      exact hHne.image _
  · -- The unbounded case: a point of the chart with fibre of every degree, against decency.
    obtain ⟨x, hx⟩ := AlgebraicGeometry.Scheme.exists_mem_iInter_of_antitone_isAffineOpen
      Vc hVcanti hVcaff hVcne
    obtain ⟨q, hq⟩ := hrep x
    set p := FieldValuedPoint.map B S hS
      (yoneda.obj (opensObject B S hS (hGrep.pullback atl) V)) φ q with hpdef
    have hqclass : pointsMap B S hS
        (yoneda.obj (opensObject B S hS (hGrep.pullback atl) V)) φ
        (q.class B S hS (yoneda.obj (opensObject B S hS (hGrep.pullback atl) V))) =
        p.class B S hS X := rfl
    obtain ⟨d, hd⟩ := exists_not_fibre_degree_ge_of_isDecentSpace B S hS hdec
      inferInstance φ hφ₁etale p
    refine absurd ?_ hd
    refine (degreeGe_iff_presheaf B S hS
      (relativelyRepresentable_of_isAlgebraicSpace B S hS hX φ)
      (yonedaEquiv.symm p.value) d).1 ?_
    refine (degreeGe_iff_mem_of_etale_chart B S hS φ hX (Z d) d (hZdeg d) q p hqclass).1 ?_
    rw [hq]
    exact hVcZ d (hx d)

/-- **Stacks 086U (David Rydh).** A decent algebraic space over a scheme has a dense open
subspace which is a scheme: its schematic locus of Stacks 03JH is a representable open subspace
whose set of points is dense.

The reduction to the local statement
`AlgebraicGeometry.Space.exists_isRepresentable_isOpenSubspace_nonempty_of_isDecentSpace` is
`AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace`,
which is Stacks 03JH together with the reduction of
`StacksFrontier/AlgebraicGeometry/Spaces/DenseSchematicLocus.lean`. -/
@[stacks 086U]
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) :=
  exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace B S hS hX
    (exists_isRepresentable_isOpenSubspace_nonempty_of_isDecentSpace B S hS hX hdec)

end AlgebraicGeometry.Space

end
