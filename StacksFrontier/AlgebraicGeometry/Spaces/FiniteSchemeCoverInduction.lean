module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteHullOfIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty

/-!
# Finite surjective scheme covers of quasi-compact quasi-separated algebraic spaces

A quasi-compact and quasi-separated algebraic space `X` over a scheme `S` has a finite
surjective morphism `Y ⟶ X` from a scheme `Y`. This is the first part of [Stacks, Tag 09YC]
without the assertion that `Y ⟶ X` is of finite presentation.

The proof is the induction of [Stacks, Tag 09YB] on the degrees of the fibres of a separated
surjective étale chart `p : h_U ⟶ X`, with every integral morphism it produces replaced by a
finite one through `AlgebraicGeometry.Space.exists_isFinite_isOpenImmersion_comp_of_isIntegralHom`:

* Tag 0ABS factors `p` as a quasi-compact open immersion `h_U ⟶ Y₀` followed by an integral
  `Y₀ ⟶ X`; since `p` is locally of finite type, `Y₀` may be replaced by a space `Y₁` finite over
  `X` in which `h_U` is still open, and then by the scheme-theoretic closure `Y` of `h_U` in
  `Y₁`, which is again finite over `X`;
* the fibre-degree drop of Tag 09YB produces an open subspace `V ⊆ Y` with `Y ∖ V ⊆ h_U` and a
  chart of `V` of smaller fibre degree, so `V` has a finite surjective scheme cover `Z ⟶ V` by
  induction;
* Tag 0G2D extends `Z ⟶ V` to an integral `Y' ⟶ Y`, which is replaced by a finite `Y'' ⟶ Y` in
  which `Z` is still open; `Y''` is a scheme, being covered by the open subspaces `Z` and
  `Y'' ×_Y h_U`, the latter finite over the scheme `U`;
* `Y'' ⨿ (Y ∖ V)_{red} ⟶ Y ⟶ X` is finite and surjective.

## Main definitions

* `AlgebraicGeometry.Space.ExistsFiniteSurjectiveSchemeCover`: an algebraic space receives a
  finite surjective morphism from (the presheaf represented by) an object of the site.

## Main results

* `AlgebraicGeometry.Space.exists_isFinite_factorization_of_isIntegralHom`: an integral morphism
  to a quasi-compact quasi-separated algebraic space factors through a finite one, by a
  surjection which keeps a given quasi-compact open of finite type open.
* `AlgebraicGeometry.Space.existsFiniteSurjectiveSchemeCover_of_chart_fibre_le`: the induction.
* `AlgebraicGeometry.Space.existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace`: every
  quasi-compact quasi-separated algebraic space has a finite surjective scheme cover.

## Implementation notes

The source deduces the first part of Tag 09YC from Tag 09YB by writing the integral algebra of
an integral scheme cover as a filtered colimit of finite subalgebras and descending the property
of being a scheme to one of the finite stages by limit arguments. Here the finite replacement is
instead made at each stage of the induction, where the open `h_U`, respectively `Z`, witnesses
that the finite replacement is still a scheme; no limit of algebraic spaces is formed.

## References

* [Stacks, Tag 09YC], [Stacks, Tag 09YB], [Stacks, Tag 0ABS], [Stacks, Tag 0G2D]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space `X` over `S` has a *finite surjective scheme cover* when some object of
the big fppf site maps to it by a finite surjective morphism of its representable presheaf. -/
def ExistsFiniteSurjectiveSchemeCover (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ X),
    IsSurjective B S hS g ∧ IsFinite B S hS g

/-- A finite surjective scheme cover is an integral surjective scheme cover. -/
theorem ExistsFiniteSurjectiveSchemeCover.existsIntegralSurjectiveSchemeCover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : ExistsFiniteSurjectiveSchemeCover B S hS X) :
    ExistsIntegralSurjectiveSchemeCover B S hS X := by
  obtain ⟨W, g, hs, hf⟩ := h
  exact ⟨W, g, hs, IsFinite.isIntegralHom B S hS hf⟩

/-- **A finite surjective scheme cover descends along a finite surjective morphism.** -/
theorem existsFiniteSurjectiveSchemeCover_comp
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : Y ⟶ X)
    (hπ : IsFinite B S hS π) (hπsurj : IsSurjective B S hS π)
    (h : ExistsFiniteSurjectiveSchemeCover B S hS Y) :
    ExistsFiniteSurjectiveSchemeCover B S hS X := by
  obtain ⟨W, g, hgsurj, hgfin⟩ := h
  exact ⟨W, g ≫ π, isSurjective_comp B S hS hgsurj hπsurj, isFinite_comp B S hS hgfin hπ⟩

/-- **Two objects of the site finite over an algebraic space whose point sets cover it assemble
into one finite surjective cover**, their coproduct. -/
theorem existsFiniteSurjectiveSchemeCover_of_isFinite_pair
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (X₁ X₂ : BigFppfOver B S hS) (p₁ : yoneda.obj X₁ ⟶ X) (p₂ : yoneda.obj X₂ ⟶ X)
    (hp₁ : IsFinite B S hS p₁) (hp₂ : IsFinite B S hS p₂)
    (hcov : ∀ x : points B S hS X,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj X₁) p₁) ∪
        Set.range (pointsMap B S hS (yoneda.obj X₂) p₂)) :
    ExistsFiniteSurjectiveSchemeCover B S hS X := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let Xs : Sheaf J (Type u) := ⟨X, hX.isSheaf⟩
  have hV : IsColimit (Cofan.mk (X₁ ⨿ X₂) (coprodPairIncl B S hS X₁ X₂)) :=
    isColimit_cofan_coprodPair B S hS X₁ X₂
  have hY : IsColimit (Cofan.mk (J.yoneda.obj (X₁ ⨿ X₂))
      fun b => J.yoneda.map (coprodPairIncl B S hS X₁ X₂ b)) :=
    BigFppfOver.isColimit_yoneda_cofan B S hS (coprodPairObj B S hS X₁ X₂)
      (coprodPairIncl B S hS X₁ X₂) hV
  let tgt : ∀ b, J.yoneda.obj (coprodPairObj B S hS X₁ X₂ b) ⟶ Xs := fun b =>
    match b with
    | ⟨false⟩ => ⟨p₁⟩
    | ⟨true⟩ => ⟨p₂⟩
  let h : J.yoneda.obj (X₁ ⨿ X₂) ⟶ Xs := Cofan.IsColimit.desc hY tgt
  have hfac₁ : yoneda.map (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ≫ h.hom = p₁ :=
    congrArg (fun k : J.yoneda.obj (coprodPairObj B S hS X₁ X₂ ⟨false⟩) ⟶ Xs => k.hom)
      (Cofan.IsColimit.fac hY tgt ⟨false⟩)
  have hfac₂ : yoneda.map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫ h.hom = p₂ :=
    congrArg (fun k : J.yoneda.obj (coprodPairObj B S hS X₁ X₂ ⟨true⟩) ⟶ Xs => k.hom)
      (Cofan.IsColimit.fac hY tgt ⟨true⟩)
  let fam : ∀ b : ULift.{u} Bool, yoneda.obj (coprodPairObj B S hS X₁ X₂ b) ⟶ X := fun b =>
    match b with
    | ⟨false⟩ => p₁
    | ⟨true⟩ => p₂
  have hfac : ∀ b, yoneda.map (coprodPairIncl B S hS X₁ X₂ b) ≫ h.hom = fam b := by
    intro b
    rcases b with ⟨_ | _⟩
    · exact hfac₁
    · exact hfac₂
  refine ⟨X₁ ⨿ X₂, h.hom, ?_, ?_⟩
  · refine isSurjective_of_iUnion_range_pointsMap_eq_univ B S hS
      (fun b => yoneda.map (coprodPairIncl B S hS X₁ X₂ b)) h.hom fam hfac ?_
    refine Set.eq_univ_of_forall fun x => ?_
    rcases hcov x with hx | hx
    · exact Set.mem_iUnion.2 ⟨⟨false⟩, hx⟩
    · exact Set.mem_iUnion.2 ⟨⟨true⟩, hx⟩
  · refine isFinite_coproduct B S hS
      (fun b => yoneda.obj (coprodPairObj B S hS X₁ X₂ b))
      (fun b => isAlgebraicSpace_yoneda B S hS (coprodPairObj B S hS X₁ X₂ b)) hX
      (J.yoneda.obj (X₁ ⨿ X₂))
      (fun b => J.yoneda.map (coprodPairIncl B S hS X₁ X₂ b)) hY fam h.hom hfac ?_
    intro b
    rcases b with ⟨_ | _⟩
    · exact hp₁
    · exact hp₂

/-- **An integral morphism to a quasi-compact quasi-separated algebraic space factors through a
finite one.** Let `π : Y ⟶ X` be integral, with `X` quasi-compact and quasi-separated, and let
`w : W ⟶ Y` be an open immersion from a quasi-compact algebraic space with `w ≫ π` locally of
finite type. Then `π = h ≫ π'` with `π'` finite, `h` surjective and `w ≫ h` an open immersion.

This is `AlgebraicGeometry.Space.exists_isFinite_isOpenImmersion_comp_of_isIntegralHom` for a
morphism of presheaves rather than an object affine over `X`. -/
theorem exists_isFinite_factorization_of_isIntegralHom
    {X Y W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hW : IsAlgebraicSpace B S hS W)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (π : Y ⟶ X) (hπ : IsIntegralHom B S hS π) (w : W ⟶ Y) (hw : IsOpenImmersion B S hS w)
    (hWqc : IsQuasiCompactSpace B S hS W)
    (hWlft : IsLocallyOfFiniteType B S hS (w ≫ π)) :
    ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (h : Y ⟶ Y') (π' : Y' ⟶ X),
      IsAlgebraicSpace B S hS Y' ∧ h ≫ π' = π ∧ IsFinite B S hS π' ∧
        IsOpenImmersion B S hS (w ≫ h) ∧ IsSurjective B S hS h := by
  let Xa : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let N : AffineOver B S hS Xa :=
    ⟨Over.mk (ObjectProperty.homMk π : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ Xa),
      isAffineHom_of_isIntegralHom π hπ⟩
  obtain ⟨N', h, h1, h2, h3⟩ :=
    exists_isFinite_isOpenImmersion_comp_of_isIntegralHom B S hS Xa hXqc hXqs N hπ hW w hw hWqc
      hWlft
  refine ⟨N'.obj.left.1, h.left.hom, N'.obj.hom.hom, N'.obj.left.2, ?_, h1, h2, h3⟩
  exact congrArg (fun k => k.hom) (Over.w h)

/-- **The dense finite relative compactification.** Let `j : U ⟶ Y` be a quasi-compact open
immersion of algebraic spaces and let `π : Y ⟶ X` be finite. Then `j ≫ π` factors as a
quasi-compact open immersion `j' : U ⟶ Y'` followed by a finite `π' : Y' ⟶ X`, the range of `j'`
being a quasi-compact, scheme-theoretically dense open subspace of `Y'`. `Y'` is the
scheme-theoretic closure of `j(U)` in `Y`. -/
theorem exists_isSchemeTheoreticallyDense_isFinite_factorization
    {U X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hY : IsAlgebraicSpace B S hS Y) (j : U ⟶ Y)
    (hj : IsOpenImmersion B S hS j) (hjqc : IsQuasiCompact B S hS j) (π : Y ⟶ X)
    (hπ : IsFinite B S hS π) :
    ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j' : U ⟶ Y') (π' : Y' ⟶ X),
      IsAlgebraicSpace B S hS Y' ∧ IsOpenImmersion B S hS j' ∧
        IsQuasiCompact B S hS j' ∧ IsFinite B S hS π' ∧ j' ≫ π' = j ≫ π ∧
        IsOpenSubspace B S hS (Subfunctor.range j') ∧
        IsQuasiCompact B S hS (Subfunctor.range j').ι ∧
        IsSchemeTheoreticallyDense B S hS (Subfunctor.range j') ∧
        DenseRange (pointsMap B S hS U j') := by
  have hjim : IsImmersion B S hS j := isImmersion_of_isOpenImmersion B S hS hj
  have hclosed : IsClosedSubspace B S hS (schemeTheoreticImageSubfunctor B S hS j) :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS j hY
  obtain ⟨hopen, hqc⟩ :=
    isOpenSubspace_isQuasiCompact_range_toSchemeTheoreticImage B S hS hU hY j hjim hjqc
  refine ⟨(schemeTheoreticImageSubfunctor B S hS j).toFunctor,
    toSchemeTheoreticImage B S hS j,
    (schemeTheoreticImageSubfunctor B S hS j).ι ≫ π, hclosed.1,
    isOpenImmersion_toSchemeTheoreticImage B S hS hY j hjim hjqc,
    isQuasiCompact_toSchemeTheoreticImage B S hS j hjqc,
    isFinite_comp B S hS (isFinite_of_isClosedImmersion B S hS _ hclosed.2) hπ, ?_, hopen, hqc,
    isSchemeTheoreticallyDense_range_toSchemeTheoreticImage B S hS hU hY j hjim hjqc,
    denseRange_pointsMap_toSchemeTheoreticImage_of_isQuasiCompact B S hS j hU hY hjqc⟩
  rw [← Category.assoc, toSchemeTheoreticImage_ι]

/-- Precomposing a finite morphism with an isomorphism gives a finite morphism. -/
private theorem isFinite_comp_of_isIso {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : Y ⟶ Z)
    [IsIso e] (f : Z ⟶ X) (hf : IsFinite B S hS f) : IsFinite B S hS (e ≫ f) :=
  isFinite_comp B S hS
    (isFinite_of_isClosedImmersion B S hS _ (isClosedImmersion_of_isIso B S hS e)) hf

/-- Precomposing with an isomorphism does not change the range on points. -/
private theorem range_pointsMap_comp_of_isIso {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : Y ⟶ Z) [IsIso e] (f : Z ⟶ X) :
    Set.range (pointsMap B S hS Y (e ≫ f)) = Set.range (pointsMap B S hS Z f) := by
  rw [pointsMap_comp]
  exact (pointsMap_surjective_of_isIso B S hS e).range_comp _

/-- The source of a finite morphism to a quasi-compact algebraic space is quasi-compact. -/
private theorem isQuasiCompactSpace_of_isFinite {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXqc : IsQuasiCompactSpace B S hS X) (π : Y ⟶ X) (hπ : IsFinite B S hS π) :
    IsQuasiCompactSpace B S hS Y :=
  isQuasiCompactSpace_source_of_isQuasiCompact B S hS hX hXqc
    (isQuasiCompact_of_isAffineHom' B S hS π hY hX (IsFinite.isAffineHom hπ))

/-- The source of an integral morphism to an absolutely quasi-separated algebraic space is
absolutely quasi-separated. -/
private theorem isAbsolutelyQuasiSeparated_of_isIntegralHom'
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) (π : Y ⟶ X) (hπ : IsIntegralHom B S hS π) :
    IsAbsolutelyQuasiSeparated B S hS hZ Y :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hY hXqs
    (isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isIntegralHom B S hS π hY hX hπ))

/-- **The last step of the finite inductive step.** Let `Y` be a quasi-compact quasi-separated
algebraic space over `S`, let `j : h_U ⟶ Y` be an open immersion from an object of the site and
let `V ⊆ Y` be a quasi-compact open subspace whose points together with those of `j` cover
`|Y|`. If `V` has a finite surjective scheme cover then so does `Y`.

Tag 0G2D extends the cover `Z ⟶ V` to an integral `Y' ⟶ Y` with `Y' ×_Y V = Z`;
`AlgebraicGeometry.Space.exists_isFinite_factorization_of_isIntegralHom` replaces it by a finite
`Y'' ⟶ Y` in which `Z` is still open. `Y''` is a scheme: it is covered by `Z` and by
`Y'' ×_Y h_U`, which is finite over the scheme `U`, since every point of `Y''` comes from `Y'`.
The reduced induced structure on `|Y| ∖ |V|` is a scheme lying inside `j(U)`, and the two are
glued by `AlgebraicGeometry.Space.existsFiniteSurjectiveSchemeCover_of_isFinite_pair`. -/
theorem existsFiniteSurjectiveSchemeCover_of_openSubspace_cover
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (U : BigFppfOver B S hS) (j : yoneda.obj U ⟶ Y) (hj : IsOpenImmersion B S hS j)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor)
    (hcov : Set.range (pointsMap B S hS (yoneda.obj U) j) ∪
      Set.range (pointsMap B S hS V.toFunctor V.ι) = Set.univ)
    (hVcover : ExistsFiniteSurjectiveSchemeCover B S hS V.toFunctor) :
    ExistsFiniteSurjectiveSchemeCover B S hS Y := by
  classical
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  obtain ⟨Zc, ζ, hζsurj, hζfin⟩ := hVcover
  have hζint : IsIntegralHom B S hS ζ := IsFinite.isIntegralHom B S hS hζfin
  have hZcalg : IsAlgebraicSpace B S hS (yoneda.obj Zc) := isAlgebraicSpace_yoneda B S hS Zc
  have hViqc : IsQuasiCompact B S hS V.ι :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hY hYqs hVqc V.ι
  -- Tag 0G2D
  obtain ⟨Y', ν, f', hY', hνint, hsq⟩ :=
    exists_isIntegralHom_isPullback_of_isOpenImmersion hZcalg hV.1 hY V.ι hV.2 hViqc ζ hζint
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hf'oi : IsOpenImmersion B S hS f' :=
    MorphismProperty.of_isPullback hsq.flip hV.2
  -- the finite replacement of `Y'`
  have hZcqc : IsQuasiCompactSpace B S hS (yoneda.obj Zc) :=
    isQuasiCompactSpace_of_isFinite B S hS hV.1 hZcalg hVqc ζ hζfin
  have hlft : IsLocallyOfFiniteType B S hS (f' ≫ ν) := by
    rw [hsq.w]
    exact isLocallyOfFiniteType_comp B S hS hZcalg hV.1 hY ζ V.ι
      (isLocallyOfFiniteType_of_isFinite B S hS hZcalg hV.1 hζfin)
      (isLocallyOfFiniteType_of_isImmersion B S hS V.ι (isImmersion_of_isOpenImmersion B S hS hV.2))
  obtain ⟨Y'', h, ν'', hY'', hfac, hν''fin, hfhoi, hhsurj⟩ :=
    exists_isFinite_factorization_of_isIntegralHom B S hS hY hY' hZcalg hYqc hYqs ν hνint f'
      hf'oi hZcqc hlft
  -- the two charts of `Y''`
  have hPalg : IsAlgebraicSpace B S hS (pullback ν'' j) :=
    isAlgebraicSpace_pullback B S hS ν'' j hY'' hUalg hY
  have hfstoi : IsOpenImmersion B S hS (pullback.fst ν'' j) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback ν'' j).flip hj
  have hsndfin : IsFinite B S hS (pullback.snd ν'' j) :=
    isFinite_of_isPullback B S hS (IsPullback.of_hasPullback ν'' j) hν''fin
  have hPrep : (pullback ν'' j).IsRepresentable := by
    obtain ⟨hrep, -⟩ :=
      (isFinite_iff_representable B S hS (pullback.snd ν'' j) hPalg hUalg).1 hsndfin
    exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _ hrep
  have _ := hPrep
  set eP : yoneda.obj (pullback ν'' j).reprX ≅ pullback ν'' j := (pullback ν'' j).reprW
    with hePdef
  set Wfam : ULift.{u} Bool → BigFppfOver B S hS := fun b =>
    match b with
    | ⟨false⟩ => Zc
    | ⟨true⟩ => (pullback ν'' j).reprX
  set kfam : ∀ b, yoneda.obj (Wfam b) ⟶ Y'' := fun b =>
    match b with
    | ⟨false⟩ => f' ≫ h
    | ⟨true⟩ => eP.hom ≫ pullback.fst ν'' j
  have hkoi : ∀ b, IsOpenImmersion B S hS (kfam b) := by
    intro b
    rcases b with ⟨_ | _⟩
    · exact hfhoi
    · exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS eP.hom) hfstoi
  have hkcov : (⋃ b, Set.range (pointsMap B S hS (yoneda.obj (Wfam b)) (kfam b))) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun y'' => ?_
    obtain ⟨y', rfl⟩ := hhsurj y''
    rcases Set.eq_univ_iff_forall.1 hcov (pointsMap B S hS Y' ν y') with ⟨uu, hu⟩ | ⟨vv, hv⟩
    · have hu' : pointsMap B S hS Y'' ν'' (pointsMap B S hS Y' h y') =
          pointsMap B S hS (yoneda.obj U) j uu := by
        rw [← pointsMap_comp_apply, hfac, hu]
      obtain ⟨w, hw, -⟩ :=
        exists_points_of_isPullback B S hS (IsPullback.of_hasPullback ν'' j) _ uu hu'
      refine Set.mem_iUnion.2 ⟨⟨true⟩,
        pointsMap B S hS (pullback ν'' j) eP.inv w, ?_⟩
      show pointsMap B S hS (yoneda.obj (pullback ν'' j).reprX) (eP.hom ≫ pullback.fst ν'' j)
        (pointsMap B S hS (pullback ν'' j) eP.inv w) = _
      rw [← pointsMap_comp_apply, eP.inv_hom_id_assoc]
      exact hw
    · obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS hsq y' vv hv.symm
      refine Set.mem_iUnion.2 ⟨⟨false⟩, w, ?_⟩
      show pointsMap B S hS (yoneda.obj Zc) (f' ≫ h) w = _
      rw [pointsMap_comp_apply, hw]
  have hY''rep : Y''.IsRepresentable := by
    refine isRepresentable_of_isOpenImmersion_cover B S hS hY''.isSheaf
      (ι := ULift.{u} Bool) ((Cardinal.lt_aleph0_of_finite _).trans B.aleph0_lt_cutoff)
      (μ := max ((BigFppfOver.toScheme B S hS).obj Zc).size
        ((BigFppfOver.toScheme B S hS).obj (pullback ν'' j).reprX).size)
      (max_lt Zc.left.property (pullback ν'' j).reprX.left.property)
      (W := Wfam) ?_ kfam hkoi hkcov
    intro b
    rcases b with ⟨_ | _⟩
    · exact le_max_left _ _
    · exact le_max_right _ _
  have _ := hY''rep
  set eY : yoneda.obj Y''.reprX ≅ Y'' := Y''.reprW with heYdef
  -- the reduced closed complement of `V`, a scheme because it lies inside `j(U)`
  have hVopenPts : IsOpen (Set.range (pointsMap B S hS V.toFunctor V.ι)) :=
    isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY V hV
  set Tset : Set (points B S hS Y) := (Set.range (pointsMap B S hS V.toFunctor V.ι))ᶜ
    with hTsetdef
  have hTcl : _root_.IsClosed Tset := hVopenPts.isClosed_compl
  set T : Subfunctor Y := reducedClosedSubspace B S hS Y hY Tset hTcl with hTdef
  have hTrange : Set.range (pointsMap B S hS T.toFunctor T.ι) = Tset :=
    range_pointsMap_ι_reducedClosedSubspace B S hS Y hY Tset hTcl
  have hTcs : IsClosedSubspace B S hS T :=
    isClosedSubspace_reducedClosedSubspace' B S hS hY Tset hTcl
  have hjopen : IsOpenSubspace B S hS (Subfunctor.range j) :=
    isOpenSubspace_range_of_isOpenImmersion U j hj
  have _ : Mono j := mono_of_isOpenImmersion B S hS j hj
  have hjrange : Set.range (pointsMap B S hS (Subfunctor.range j).toFunctor
      (Subfunctor.range j).ι) = Set.range (pointsMap B S hS (yoneda.obj U) j) :=
    range_pointsMap_ι_range B S hS j
  have hle : T ≤ Subfunctor.range j := by
    refine le_of_range_pointsMap_ι_subset B S hS hjopen ?_
    rw [hTrange, hjrange]
    intro y hy
    exact (Set.eq_univ_iff_forall.1 hcov y).resolve_right hy
  have hTrep : T.toFunctor.IsRepresentable :=
    isRepresentable_of_le_of_isClosedSubspace B S hS hTcs hle
      (isRepresentable_range_of_isOpenImmersion U j hj)
  have _ := hTrep
  set eT : yoneda.obj T.toFunctor.reprX ≅ T.toFunctor := T.toFunctor.reprW with heTdef
  -- glue the two finite covers
  refine existsFiniteSurjectiveSchemeCover_of_isFinite_pair B S hS hY
    Y''.reprX T.toFunctor.reprX (eY.hom ≫ ν'') (eT.hom ≫ T.ι) ?_ ?_ ?_
  · exact isFinite_comp_of_isIso B S hS eY.hom ν'' hν''fin
  · exact isFinite_comp_of_isIso B S hS eT.hom T.ι (isFinite_of_isClosedImmersion B S hS _ hTcs.2)
  · intro y
    rw [range_pointsMap_comp_of_isIso B S hS eY.hom, range_pointsMap_comp_of_isIso B S hS eT.hom]
    by_cases hy : y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι)
    · obtain ⟨v, hv⟩ := hy
      obtain ⟨z, hz⟩ := hζsurj v
      refine Or.inl ⟨pointsMap B S hS (yoneda.obj Zc) (f' ≫ h) z, ?_⟩
      rw [← pointsMap_comp_apply, Category.assoc, hfac, hsq.w, pointsMap_comp_apply, hz, hv]
    · refine Or.inr ?_
      rw [hTrange]
      exact hy

/-- **An algebraic space with no points has a finite surjective scheme cover: its own étale
chart**, which is then an isomorphism by Stacks 05W5. -/
theorem existsFiniteSurjectiveSchemeCover_of_isEmpty_points
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (c : yoneda.obj U ⟶ X) (hc : IsEtale B S hS c)
    (hcs : IsSurjective B S hS c) (hempty : IsEmpty (points B S hS X)) :
    ExistsFiniteSurjectiveSchemeCover B S hS X := by
  have hUempty : IsEmpty (points B S hS (yoneda.obj U)) :=
    ⟨fun w ↦ hempty.elim (pointsMap B S hS (yoneda.obj U) c w)⟩
  have hui : UniversallyInjective B S hS c := by
    intro Y' _ g a _ _
    exact hUempty.elim (pointsMap B S hS (pullback g c) (pullback.snd g c) a)
  have hiso : IsIso c :=
    isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS
      (isAlgebraicSpace_yoneda B S hS U) hX c hc hui hcs
  exact ⟨U, c, hcs, isFinite_of_isClosedImmersion B S hS c (isClosedImmersion_of_isIso B S hS c)⟩

/-- **The induction of [Stacks, Tag 09YB] on the fibre degree of a chart, with finite covers.**

Let `X` be a quasi-separated algebraic space over `S` and let `p : h_U ⟶ X` be a separated
surjective étale chart whose source is quasi-compact and every field-valued fibre of which is
finite locally free of degree at most `d`. Then `X` has a finite surjective scheme cover.

The step is that of
`AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_chart_fibre_le`, with the integral
compactification `h_U ⟶ Y₀ ⟶ X` of Tag 0ABS first replaced by a finite one
(`AlgebraicGeometry.Space.exists_isFinite_factorization_of_isIntegralHom`, `p` being locally of
finite type) and the cover of the open `V` carried to `Y` by
`AlgebraicGeometry.Space.existsFiniteSurjectiveSchemeCover_of_openSubspace_cover`. -/
theorem existsFiniteSurjectiveSchemeCover_of_chart_fibre_le
    (hZ : B.Contains (⊤_ Scheme.{u})) (d : ℕ) :
    ∀ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS X →
      IsAbsolutelyQuasiSeparated B S hS hZ X →
      ∀ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsEtale B S hS p → IsSurjective B S hS p → IsSeparated B S hS p →
        IsQuasiCompactSpace B S hS (yoneda.obj U) →
        (∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
          (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
          (ζ : yoneda.obj T ⟶ X) (Q : BigFppfOver B S hS) (q : Q ⟶ T)
          (c : yoneda.obj Q ⟶ yoneda.obj U),
          IsPullback c (yoneda.map q) p ζ →
            ∃ r : ℕ, r ≤ d ∧
              Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r) →
        ExistsFiniteSurjectiveSchemeCover B S hS X := by
  classical
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro X hX hXqs U p hpet hpsurj hpsep hUqc hd
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_of_isSurjective B S hS hUalg hX p hpsurj hUqc
  -- the chart is a quasi-compact morphism, hence quasi-finite
  have hpqc : IsQuasiCompact B S hS p :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hX hXqs hUqc p
  have hpqf : IsQuasiFinite B S hS p :=
    ⟨isLocallyQuasiFinite_of_isEtale' B S hS hpet, hpqc⟩
  -- Tag 0ABS
  obtain ⟨-, N₀, hfac₀, hj₀, -, hπ₀⟩ := zariskiMainTheorem B S hS p hUalg hX hpqf hpsep
  have hY₀ := N₀.isAlgebraicSpace
  set j₀ := N₀.toNorm
  set π₀ := N₀.fromNorm
  -- the finite replacement
  obtain ⟨Y₁, h₁, π₁, hY₁, hfac₁, hπ₁, hj₁, -⟩ :=
    exists_isFinite_factorization_of_isIntegralHom B S hS hX hY₀ hUalg hXqc hXqs π₀ hπ₀ j₀ hj₀
      hUqc (by rw [hfac₀]; exact isLocallyOfFiniteType_of_isEtale' B S hS p hpet)
  have hY₁qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₁ :=
    isAbsolutelyQuasiSeparated_of_isIntegralHom' B S hS hZ hX hY₁ hXqs π₁
      (IsFinite.isIntegralHom B S hS hπ₁)
  have hj₁qc : IsQuasiCompact B S hS (j₀ ≫ h₁) :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hY₁ hY₁qs hUqc _
  -- the dense replacement
  obtain ⟨Y, j, π, hY, hj, hjqc, hπ, hfac, -, -, -, hdense⟩ :=
    exists_isSchemeTheoreticallyDense_isFinite_factorization B S hS hUalg hY₁ (j₀ ≫ h₁) hj₁
      hj₁qc π₁ hπ₁
  have hjπ : j ≫ π = p := by rw [hfac, Category.assoc, hfac₁]; exact hfac₀
  have hπint : IsIntegralHom B S hS π := IsFinite.isIntegralHom B S hS hπ
  -- the fibre-degree drop
  obtain ⟨Wc, V, g', φ, hVopen, hg'et, hg'surj, hφint, hgfac, hcov, hdrop⟩ :=
    exists_isOpenSubspace_chart_isFiniteLocallyFreeOfRank_lt B S hS hX hY U j π hj hπint
      (by rw [hjπ]; exact hpet) (by rw [hjπ]; exact hpsep) (by rw [hjπ]; exact hpsurj)
      hdense d (by rw [hjπ]; exact hd)
  have hWcalg : IsAlgebraicSpace B S hS (yoneda.obj Wc) := isAlgebraicSpace_yoneda B S hS Wc
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- the base: no fibre can have degree below zero, so `V` has no points and `j` is an iso
    subst hd0
    have hVempty : IsEmpty (points B S hS V.toFunctor) := by
      refine ⟨fun x => ?_⟩
      obtain ⟨pt, -⟩ := Quot.exists_rep x
      have hg'p := (isEtale_iff_presheaf_of_yoneda B S hS g').1 hg'et
      obtain ⟨r, hr, -⟩ := hdrop pt.carrier pt.field pt.siteObject (Iso.refl _)
        (yonedaEquiv.symm pt.value) (hg'p.rep.pullback (yonedaEquiv.symm pt.value))
        (hg'p.rep.snd (yonedaEquiv.symm pt.value))
        (yoneda.map (hg'p.rep.fst' (yonedaEquiv.symm pt.value)))
        (hg'p.rep.isPullback' (yonedaEquiv.symm pt.value))
      exact absurd hr (Nat.not_lt_zero r)
    have hVrange : Set.range (pointsMap B S hS V.toFunctor V.ι) = ∅ := Set.range_eq_empty _
    have hjsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) j) := by
      intro y
      have hmem : y ∈ Set.range (pointsMap B S hS (yoneda.obj U) j) ∪
          Set.range (pointsMap B S hS V.toFunctor V.ι) := hcov ▸ Set.mem_univ y
      rcases hmem with h | h
      · exact h
      · rw [hVrange] at h; exact absurd h (Set.notMem_empty y)
    have _ : IsIso j := isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS j hj hjsurj
    exact ⟨U, p, hpsurj, hjπ ▸ isFinite_comp_of_isIso B S hS j π hπ⟩
  · -- the step: recurse into `V` at the strictly smaller bound
    have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y :=
      isAbsolutelyQuasiSeparated_of_isIntegralHom' B S hS hZ hX hY hXqs π hπint
    have hYqc : IsQuasiCompactSpace B S hS Y :=
      isQuasiCompactSpace_of_isFinite B S hS hX hY hXqc π hπ
    have hφqc : IsQuasiCompact B S hS φ :=
      isQuasiCompact_of_isAffineHom' B S hS φ hWcalg hUalg
        (isAffineHom_of_isIntegralHom φ hφint)
    have hWcqc : IsQuasiCompactSpace B S hS (yoneda.obj Wc) :=
      isQuasiCompactSpace_source_of_isQuasiCompact B S hS hUalg hUqc hφqc
    have hVqc : IsQuasiCompactSpace B S hS V.toFunctor :=
      isQuasiCompactSpace_of_isSurjective B S hS hWcalg hVopen.1 g' hg'surj hWcqc
    have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V.toFunctor :=
      isAbsolutelyQuasiSeparated_subfunctor B S hS hZ hYqs V hVopen.1
    have hg'sep : IsSeparated B S hS g' := by
      refine isSeparated_of_comp B S hS g' (V.ι ≫ π) ?_
      have hcomp : g' ≫ V.ι ≫ π = φ ≫ p := by rw [← Category.assoc, hgfac, hjπ]
      rw [hcomp]
      exact isSeparated_comp B S hS φ p
        (isSeparated_of_isIntegralHom B S hS φ hWcalg hUalg hφint) hpsep
    have hVcover : ExistsFiniteSurjectiveSchemeCover B S hS V.toFunctor :=
      ih (d - 1) (by omega) V.toFunctor hVopen.1 hVqs Wc g' hg'et hg'surj hg'sep hWcqc
        (fun K hK T eT ξ Q q c hsqc => by
          obtain ⟨r, hlt, hrank⟩ := hdrop K hK T eT ξ Q q c hsqc
          exact ⟨r, by omega, hrank⟩)
    refine existsFiniteSurjectiveSchemeCover_comp B S hS π hπ ?_ ?_
    · intro y
      obtain ⟨x, hx⟩ := hpsurj y
      exact ⟨pointsMap B S hS (yoneda.obj U) j x, by rw [← pointsMap_comp_apply, hjπ]; exact hx⟩
    · exact existsFiniteSurjectiveSchemeCover_of_openSubspace_cover B S hS hZ hY hYqc hYqs U j
        hj V hVopen hVqc hcov hVcover

/-- **A quasi-compact quasi-separated algebraic space has a finite surjective scheme cover.**
This is part (1) of [Stacks, Tag 09YC] without the assertion that the cover is of finite
presentation.

An affine surjective étale chart exists because the space is quasi-compact; its fibre degrees
are bounded because a quasi-separated algebraic space is reasonable (Stacks 03JX, 07S8); and
`AlgebraicGeometry.Space.existsFiniteSurjectiveSchemeCover_of_chart_fibre_le` performs the
induction on that bound. -/
theorem existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    ExistsFiniteSurjectiveSchemeCover B S hS X := by
  classical
  obtain ⟨U, c, hUaff, hcsurj, hcet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1 hXqc
  have hcs : IsSurjective B S hS c := isSurjective_of_presheafSurjective B S hS c hcsurj
  rcases isEmpty_or_nonempty (points B S hS X) with hemp | hne
  · exact existsFiniteSurjectiveSchemeCover_of_isEmpty_points B S hS hX U c hcet hcs hemp
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUaff
  have hUsep : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
  have hUqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    isQuasiCompact_yoneda_of_compact B S hS U inferInstance
  have hcsep : IsSeparated B S hS c :=
    isSeparated_of_isEtale_of_scheme_isSeparated B S hS X hX U hUsep c hcet
  have hR : IsReasonableSpace B S hS X :=
    isReasonableSpace_of_isAbsolutelyQuasiSeparated B S hS hZ X hX hXqs
  obtain ⟨d, -, -, -, -, -, hbd⟩ :=
    exists_minimalDegreeOpen_and_fibre_le_degree B S hS X U c hX hR hUaff hcet hcsep hne
  exact existsFiniteSurjectiveSchemeCover_of_chart_fibre_le B S hS hZ d X hX hXqs U c hcet
    hcs hcsep hUqc hbd

end AlgebraicGeometry.Space

end
