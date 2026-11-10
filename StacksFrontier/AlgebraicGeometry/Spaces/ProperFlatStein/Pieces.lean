module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.StructureMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Pieces of a morphism cut out by an open and closed subscheme

Let `f : X ⟶ Z` be a morphism of algebraic spaces over a scheme `S`, let `ψ : X ⟶ h_T` be a
morphism to the presheaf represented by an object `T` of the big fppf site, and let
`ι : V ⟶ T` be a morphism of the site. The base change `X₁ = X ×_{h_T} h_V` of `X` along
`h_ι` comes with a morphism `j : X₁ ⟶ X`, and this file records which properties of `f` the
composite `j ≫ f` inherits when `ι` is an open immersion, a closed immersion, or both — that
is, when `V` is an open and closed subscheme of `T`, so that `X₁` is an open and closed piece
of `X`.

All declarations are in the namespace `AlgebraicGeometry.Space.ProperFlatStein`.

## Main results

* `presheaf_inverseImage_of_isPullback_yoneda_map`: `j` has, relatively, every base-change
  stable property of morphisms of schemes that the scheme morphism underlying `ι` has; in
  particular it is a closed immersion, an open immersion or relatively étale when `ι` is.
* `isAlgebraicSpace_of_isPullback_yoneda_map`: `X₁` is an algebraic space.
* `isProper_comp_of_isPullback_isClosedImmersion`,
  `isFlat_comp_of_isPullback_isOpenImmersion` and
  `isFinitePresentation_comp_of_isPullback_isOpenImmersion_isClosedImmersion` say that `j ≫ f`
  is proper, flat, or of finite presentation when `f` is and `ι` is a closed immersion, an open
  immersion, or both.
* `isGeometricallyReducedFibreAt_comp_of_etale`: precomposing a morphism with geometrically
  reduced fibres (Stacks 0E08) with a relatively étale morphism of algebraic spaces gives a
  morphism with geometrically reduced fibres; and
  `isGeometricallyReducedFibreAt_comp_of_isPullback_isOpenImmersion` is the case of `j ≫ f`
  for an open immersion `ι`.

## Implementation notes

A closed immersion `j` is proper (Stacks 04XZ) and is quasi-compact and quasi-separated; an open
immersion is étale, hence flat (Stacks 0467) and locally of finite presentation (Stacks 06CN).
Each of the three properties is then stable under composition (Stacks 04XY, 03MN, 03XQ).

For the fibres: by Stacks 0E07 geometric reducedness of the fibre at a point of `|Y|` is
reducedness of the fibre over every field-valued representative `p`, read on étale scheme
charts (Stacks 03E6, 03E8). The fibre of `j ≫ f` over `p` maps to the fibre of `f` over `p` by
the base change of the restriction of `j`, which is relatively étale since restriction along
the structure morphism of the field spectrum preserves relative properties of morphisms; so an
étale chart of the first fibre followed by that map is an étale chart of the second fibre, and
is therefore reduced.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.ProperFlatStein

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is slow
/-- Pullbacks of presheaves on a big fppf site over a scheme (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_ProperFlatSteinPieces {B : BigFppfSite.{u}} {S' : Scheme.{u}}
    {hS' : B.Contains S'} : HasPullbacks ((BigFppfOver B S' hS')ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ProperFlatSteinPieces {B : BigFppfSite.{u}}
    {S' : Scheme.{u}} {hS' : B.Contains S'} {X Y Z : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The base change of a represented morphism -/

section Piece

variable {X X₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T V : BigFppfOver B S hS}
  {ψ : X ⟶ yoneda.obj T} {ι : V ⟶ T} {j : X₁ ⟶ X} {r : X₁ ⟶ yoneda.obj V}

/-- The base change `j : X₁ ⟶ X` of `h_ι : h_V ⟶ h_T` along `ψ : X ⟶ h_T` has, relatively, every
base-change stable property of morphisms of schemes which the scheme morphism underlying `ι`
has. -/
theorem presheaf_inverseImage_of_isPullback_yoneda_map (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (sq : IsPullback j r ψ (yoneda.map ι))
    (hι : P ((BigFppfOver.toScheme B S hS).map ι)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf j :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq.flip
    (presheaf_yoneda_map_of_inverseImage B S hS inferInstance ι hι)

/-- The base change `X₁ = X ×_{h_T} h_V` of an algebraic space `X` along a morphism of
representable presheaves is an algebraic space. -/
theorem isAlgebraicSpace_of_isPullback_yoneda_map (hX : IsAlgebraicSpace B S hS X)
    (sq : IsPullback j r ψ (yoneda.map ι)) : IsAlgebraicSpace B S hS X₁ :=
  isAlgebraicSpace_of_iso B S hS sq.isoPullback.symm
    (isAlgebraicSpace_pullback B S hS ψ (yoneda.map ι) hX (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS T))

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If `ι : V ⟶ T` is a closed immersion and `f : X ⟶ Z` is proper, then so is the composite of
`f` with the base change `j : X ×_{h_T} h_V ⟶ X` of `h_ι` along `ψ : X ⟶ h_T`: `j` is a closed
immersion, hence proper (Stacks 04XZ), and proper morphisms compose (Stacks 04XY). -/
theorem isProper_comp_of_isPullback_isClosedImmersion (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Z) (sq : IsPullback j r ψ (yoneda.map ι))
    (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hf : IsProper B S hS f) : IsProper B S hS (j ≫ f) := by
  have hX₁ := isAlgebraicSpace_of_isPullback_yoneda_map B S hS hX sq
  exact isProper_comp B S hS hX₁ hX hZ j f
    (isProper_of_isClosedImmersion B S hS hX₁ hX j
      (presheaf_inverseImage_of_isPullback_yoneda_map B S hS _ sq hι)) hf

/-- If `ι : V ⟶ T` is an open immersion and `f : X ⟶ Z` is flat, then so is the composite of `f`
with the base change `j : X ×_{h_T} h_V ⟶ X` of `h_ι` along `ψ : X ⟶ h_T`: `j` is an open
immersion, hence étale and so flat (Stacks 0467), and flat morphisms compose (Stacks 03MN). -/
theorem isFlat_comp_of_isPullback_isOpenImmersion (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Z) (sq : IsPullback j r ψ (yoneda.map ι))
    (hι : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hf : IsFlat B S hS f) : IsFlat B S hS (j ≫ f) :=
  isFlat_comp B S hS (isAlgebraicSpace_of_isPullback_yoneda_map B S hS hX sq) hX hZ j f
    (isFlat_of_isEtale B S hS (isEtale_of_isOpenImmersion B S hS
      (presheaf_inverseImage_of_isPullback_yoneda_map B S hS _ sq hι))) hf

/-- If `ι : V ⟶ T` is both an open and a closed immersion and `f : X ⟶ Z` is of finite
presentation, then so is the composite of `f` with the base change `j : X ×_{h_T} h_V ⟶ X` of
`h_ι` along `ψ : X ⟶ h_T`: `j` is an open immersion, hence locally of finite presentation
(Stacks 06CN), and a closed immersion, hence quasi-compact (Stacks 04CG) and quasi-separated;
morphisms of finite presentation compose (Stacks 03XQ). -/
theorem isFinitePresentation_comp_of_isPullback_isOpenImmersion_isClosedImmersion
    (hX : IsAlgebraicSpace B S hS X) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Z)
    (sq : IsPullback j r ψ (yoneda.map ι))
    (hιo : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hιc : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hf : IsFinitePresentation B S hS f) : IsFinitePresentation B S hS (j ≫ f) := by
  have hjc : IsClosedImmersion B S hS j :=
    presheaf_inverseImage_of_isPullback_yoneda_map B S hS _ sq hιc
  exact isFinitePresentation_comp B S hS (isAlgebraicSpace_of_isPullback_yoneda_map B S hS hX sq)
    hX hZ j f
    ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS
      (presheaf_inverseImage_of_isPullback_yoneda_map B S hS _ sq hιo),
      isQuasiCompact_of_isClosedImmersion' B S hS hjc,
      isQuasiSeparated_of_isClosedImmersion B S hS hjc⟩ hf

end Piece

/-! ### Geometrically reduced fibres -/

section Fibres

variable {X X₁ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The fibre of `j ≫ f` over a field-valued point `p` maps to the fibre of `f` over `p` by a
relatively étale morphism when `j` is relatively étale: that map is the base change of the
restriction of `j` along the structure morphism of the field spectrum. -/
theorem exists_presheaf_etale_fibreOverFieldValuedPoint_comp (f : X ⟶ Y) (j : X₁ ⟶ X)
    (hj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j)
    (p : FieldValuedPoint B S hS Y) :
    ∃ φ : fibreOverFieldValuedPoint B S hS (j ≫ f) p ⟶ fibreOverFieldValuedPoint B S hS f p,
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of p.carrier)) p.contained)).presheaf φ := by
  let g : B.obj p.contained ⟶ B.obj hS := ⟨p.toBase⟩
  let R : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤
      ((BigFppfOver B (Spec (.of p.carrier)) p.contained)ᵒᵖ ⥤ Type u) :=
    OverShriek.relocalizeRestrict g
  let σ := restrictedSection B S hS Y p.contained g p.value
  have hR : R.map (j ≫ f) = R.map j ≫ R.map f := R.map_comp j f
  let φ : pullback (R.map (j ≫ f)) σ ⟶ pullback (R.map f) σ :=
    pullback.map _ _ _ _ (R.map j) (𝟙 _) (𝟙 _) (by rw [hR, Category.comp_id]) (by simp)
  have hs : IsPullback (pullback.fst (R.map (j ≫ f)) σ) (φ ≫ pullback.snd (R.map f) σ)
      (R.map j ≫ R.map f) σ := by
    have hφ : φ ≫ pullback.snd (R.map f) σ = pullback.snd (R.map (j ≫ f)) σ := by
      simp [φ]
    rw [hφ, ← hR]
    exact IsPullback.of_hasPullback _ _
  have hsq : IsPullback (pullback.fst (R.map (j ≫ f)) σ) φ (R.map j)
      (pullback.fst (R.map f) σ) :=
    IsPullback.of_bot hs (by simp [φ]) (IsPullback.of_hasPullback _ _)
  exact ⟨φ, (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq
    (presheaf_inverseImage_relocalizeRestrict_map B (Spec (.of p.carrier)) S
      p.contained hS g (@AlgebraicGeometry.Etale.{u}) inferInstance hj)⟩

/-- **Geometrically reduced fibres pass along a relatively étale morphism of the source.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S` all of whose fibres are geometrically
reduced (Stacks 0E08), and let `j : X₁ ⟶ X` be a morphism from an algebraic space which is
étale after every representable base change. Then all fibres of `j ≫ f` are geometrically
reduced: by Stacks 0E07 it suffices that the fibre over every field-valued point be reduced on
its étale charts, and an étale chart of the fibre of `j ≫ f` followed by the étale comparison
map is an étale chart of the fibre of `f`. -/
theorem isGeometricallyReducedFibreAt_comp_of_etale (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (j : X₁ ⟶ X)
    (hX₁ : IsAlgebraicSpace B S hS X₁)
    (hj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j)
    (h : ∀ y, IsGeometricallyReducedFibreAt B S hS f hX hY y) :
    ∀ y, IsGeometricallyReducedFibreAt B S hS (j ≫ f) hX₁ hY y := by
  intro y
  rw [isGeometricallyReducedFibreAt_iff_forall_isReduced]
  intro p hp
  have hred := (isGeometricallyReducedFibreAt_iff_forall_isReduced B S hS f hX hY y).1 (h y) p hp
  obtain ⟨φ, hφ⟩ := exists_presheaf_etale_fibreOverFieldValuedPoint_comp B S hS f j hj p
  have := isMultiplicative_presheaf_etale B (Spec (.of p.carrier)) p.contained
  refine (exists_atlas_iff_forall_etale B (Spec (.of p.carrier)) p.contained _
    (fun T : Scheme.{u} => IsReduced T)
    (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS (j ≫ f) hX₁ hY p)).2 fun W g hg => ?_
  exact (exists_atlas_iff_forall_etale B (Spec (.of p.carrier)) p.contained _
    (fun T : Scheme.{u} => IsReduced T)
    (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY p)).1 hred W (g ≫ φ)
    (MorphismProperty.comp_mem _ g φ hg hφ)

/-- **Geometrically reduced fibres of an open piece.** Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` all of whose fibres are geometrically reduced, let `ψ : X ⟶ h_T` and
let `ι : V ⟶ T` be a morphism of the site whose underlying morphism of schemes is an open
immersion. Then the composite of `f` with the base change `j : X ×_{h_T} h_V ⟶ X` of `h_ι` has
geometrically reduced fibres: `j` is relatively an open immersion, hence relatively étale. -/
theorem isGeometricallyReducedFibreAt_comp_of_isPullback_isOpenImmersion
    {T V : BigFppfOver B S hS} {ψ : X ⟶ yoneda.obj T} {ι : V ⟶ T} {j : X₁ ⟶ X}
    {r : X₁ ⟶ yoneda.obj V} (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hX₁ : IsAlgebraicSpace B S hS X₁)
    (sq : IsPullback j r ψ (yoneda.map ι))
    (hι : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (h : ∀ y, IsGeometricallyReducedFibreAt B S hS f hX hY y) :
    ∀ y, IsGeometricallyReducedFibreAt B S hS (j ≫ f) hX₁ hY y :=
  isGeometricallyReducedFibreAt_comp_of_etale B S hS f hX hY j hX₁
    (presheaf_etale_of_isOpenImmersion B S hS
      (presheaf_inverseImage_of_isPullback_yoneda_map B S hS _ sq hι))
    h

end Fibres

end AlgebraicGeometry.Space.ProperFlatStein

end
