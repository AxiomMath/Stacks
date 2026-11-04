module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity.OpenSubspaceCharts

/-!
# Scheme-theoretic density of an open subspace of an algebraic space

The scheme-theoretic closure and scheme-theoretic density of an open subspace of an algebraic
space (Stacks 0834), the criterion by injectivity of the structure-sheaf map of the inclusion
(Stacks 0836), intersections of dense open subspaces (Stacks 0837), and the part of Stacks 0833
that holds for the bare equality of the scheme-theoretic closure with the chart. See
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity` for an overview.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Scheme-theoretic density of an open subspace -/

section Density

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0834, part (1).** The *scheme-theoretic closure* of a subspace `U` of an algebraic
space `X` over `S` is the scheme-theoretic image of Stacks 082X of its inclusion. -/
@[stacks 0834 "part (1): the scheme-theoretic closure of an open subspace"]
abbrev schemeTheoreticClosure (U : Subfunctor X) : Subfunctor X :=
  schemeTheoreticImageSubfunctor B S hS U.ι

/-- **Stacks 0834, part (2).** An open subspace `U` of an algebraic space `X` over `S` is
*scheme-theoretically dense in `X`* when, for every étale morphism `φ : V ⟶ X` of algebraic
spaces over `S`, the scheme-theoretic closure of `U ×_X V` in `V` is all of `V`.

This is the first of the equivalent conditions of Stacks 0833, and is in general strictly
stronger than the scheme-theoretic closure of `U` itself being all of `X`. -/
@[stacks 0834 "part (2): scheme-theoretic density of an open subspace",
  ega "IV 11.10.2" "single open subspace"]
def IsSchemeTheoreticallyDense (U : Subfunctor X) : Prop :=
  ∀ {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS V → ∀ φ : V ⟶ X,
    IsEtale B S hS φ → schemeTheoreticClosure B S hS (U.preimage φ) = ⊤

/-- If the scheme-theoretic image of the inverse image of `U` along a surjective étale
morphism `ψ` from a representable presheaf is all of the source, then the scheme-theoretic image
of `U` is all of `X`. -/
private lemma schemeTheoreticImageSubfunctor_eq_top_of_preimage_eq_top
    (hX : IsAlgebraicSpace B S hS X) (U : Subfunctor X) (V : BigFppfOver B S hS)
    (ψ : yoneda.obj V ⟶ X)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hclosure : schemeTheoreticImageSubfunctor B S hS (U.preimage ψ).ι = ⊤) :
    schemeTheoreticImageSubfunctor B S hS U.ι = ⊤ := by
  have hsq : (U.preimage ψ).ι ≫ ψ = U.fromPreimage ψ ≫ U.ι :=
    (Subfunctor.isPullback_preimage ψ U).w.symm
  have hle := schemeTheoreticImageSubfunctor_le_preimage B S hS
    (isAlgebraicSpace_yoneda B S hS V) hX hsq
  rw [hclosure] at hle
  exact subfunctor_eq_top_of_isSurjective_isEtale_preimage B S hS hX _
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS U.ι hX).1.isSheaf V ψ hsurj
    hetale (le_antisymm le_top hle)

/-- Scheme-theoretic density of an open subspace may be tested on the étale scheme charts
alone: the scheme-theoretic closure of `U ×_X V` is all of `V` for every étale morphism
`V ⟶ X` of algebraic spaces as soon as it is so for every étale scheme chart of `X`.

Every étale morphism from an algebraic space admits a surjective étale scheme chart, whose
composite with it is again an étale scheme chart of `X`; the scheme-theoretic closure of the
inverse image in that chart is contained in the inverse image of the scheme-theoretic closure
downstairs, by Stacks 0CP2, so the latter has everything as inverse image and
`AlgebraicGeometry.Space.subfunctor_eq_top_of_isSurjective_isEtale_preimage` identifies it
with `⊤`. -/
lemma isSchemeTheoreticallyDense_iff_forall_chart (U : Subfunctor X) :
    IsSchemeTheoreticallyDense B S hS U ↔
      ∀ V : SmallEtale B S hS X,
        schemeTheoreticImageSubfunctor B S hS (U.preimage V.1.hom).ι = ⊤ := by
  constructor
  · intro h V
    exact h (isAlgebraicSpace_yoneda B S hS V.1.left) V.1.hom
      (isEtale_of_presheafEtale B S hS V.1.hom V.2)
  · intro h W hW φ hφ
    obtain ⟨V, ψ, hsurj, hetale⟩ := hW.exists_atlas
    have hcomp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (ψ ≫ φ) := hφ V ψ hetale
    have hchart0 := h ⟨CostructuredArrow.mk (ψ ≫ φ), hcomp⟩
    refine schemeTheoreticImageSubfunctor_eq_top_of_preimage_eq_top B S hS hW _ V ψ hsurj hetale ?_
    rw [← Subfunctor.preimage_comp U ψ φ]
    exact hchart0

/-- **Stacks 0836.** Let `j : U ⟶ X` be an open immersion of algebraic spaces over a scheme
`S` contained in a big fppf site `B`. Then `U` is scheme-theoretically dense in `X` if and only
if the canonical homomorphism `𝒪_X ⟶ j_* 𝒪_U` of sheaves of commutative rings on the small
étale site of `X` is injective, that is, a monomorphism.

Both sides are tested on the étale scheme charts of `X`. On the one hand the structure map of
the morphism of ringed topoi of Stacks 03G8 is a monomorphism exactly when, over every étale
scheme chart `V` of `X`, pullback of regular functions along the open immersion of schemes
representing `U ×_X V` is injective; the sections of the direct image over `V` are a limit over
the étale charts of `U` above `U ×_X V`, which for a representable morphism is attained at the
single chart `U ×_X V`. On the other hand the scheme-theoretic closure of `U ×_X V` is all of
`V` exactly when that open immersion of schemes is scheme-theoretically dominant, and -- since
the charts of `X` include every open subscheme of every chart -- dominance over all charts is
the same as injectivity on global sections over all charts. Finally density may be tested on
the charts alone, by
`AlgebraicGeometry.Space.isSchemeTheoreticallyDense_iff_forall_chart`. -/
@[stacks 0836]
theorem isSchemeTheoreticallyDense_iff_mono_fSharp (hX : IsAlgebraicSpace B S hS X)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U) :
    IsSchemeTheoreticallyDense B S hS U ↔
      Mono (smallEtaleRingedToposHom B S hS
        (ObjectProperty.homMk U.ι :
          (⟨U.toFunctor, hU.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨X, hX⟩ : AlgebraicSpaces B S hS))).fSharp := by
  rw [mono_fSharp_iff_injective_structureMapApp,
    isSchemeTheoreticallyDense_iff_forall_chart]
  have hchart : ∀ V : SmallEtale B S hS X,
      (Function.Injective (structureMapApp B S hS
          (ObjectProperty.homMk U.ι :
            (⟨U.toFunctor, hU.1⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨X, hX⟩ : AlgebraicSpaces B S hS)) V) ↔
        Function.Injective ((BigFppfOver.toScheme B S hS).map
          (hU.2.rep.snd V.1.hom)).appTop.hom) := by
    intro V
    exact injective_structureMapApp_iff_appTop B S hS
      (X := (⟨U.toFunctor, hU.1⟩ : AlgebraicSpaces B S hS))
      (Y := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) (ObjectProperty.homMk U.ι) hU.2.rep V
  calc
    (∀ V : SmallEtale B S hS X,
          schemeTheoreticImageSubfunctor B S hS (U.preimage V.1.hom).ι = ⊤) ↔
        ∀ V : SmallEtale B S hS X, IsSchemeTheoreticallyDominant
          ((BigFppfOver.toScheme B S hS).map (hU.2.rep.snd V.1.hom)) :=
      forall_congr' fun V =>
        schemeTheoreticImageSubfunctor_preimage_eq_top_iff B S hS hU.2 V.1.hom
    _ ↔ ∀ V : SmallEtale B S hS X,
        Mono ((BigFppfOver.toScheme B S hS).map (hU.2.rep.snd V.1.hom)).c :=
      (forall_mono_c_iff_forall_isSchemeTheoreticallyDominant B S hS hU.2).symm
    _ ↔ ∀ V : SmallEtale B S hS X, Function.Injective
        ((BigFppfOver.toScheme B S hS).map (hU.2.rep.snd V.1.hom)).appTop.hom :=
      (forall_injective_appTop_iff_forall_mono_c B S hS hU.2).symm
    _ ↔ _ := forall_congr' fun V => (hchart V).symm

/-- **Scheme-theoretic density of an open subspace, read on the étale scheme charts.** An open
subspace `U ⊆ X` is scheme-theoretically dense in `X` exactly when, for every étale scheme
chart `V` of `X`, the structure-sheaf map of the morphism of schemes representing `U ×_X V` is
a monomorphism.

This is Stacks 0836 read chartwise: density may be tested on the charts alone by
`AlgebraicGeometry.Space.isSchemeTheoreticallyDense_iff_forall_chart`, where it says that the
morphism of schemes representing `U ×_X V` is scheme-theoretically dominant for every chart,
and over all the charts that is the same as its structure-sheaf map being a monomorphism. For
an open immersion of schemes the latter is scheme-theoretic density of its image, by Stacks
01RE, `AlgebraicGeometry.isSchemeTheoreticallyDense_opensRange_iff_mono`. -/
theorem isSchemeTheoreticallyDense_iff_forall_chart_mono_c (U : Subfunctor X)
    (hU : IsOpenImmersion B S hS U.ι) :
    IsSchemeTheoreticallyDense B S hS U ↔
      ∀ V : SmallEtale B S hS X,
        Mono ((BigFppfOver.toScheme B S hS).map (hU.rep.snd V.1.hom)).c := by
  rw [isSchemeTheoreticallyDense_iff_forall_chart,
    forall_mono_c_iff_forall_isSchemeTheoreticallyDominant B S hS hU]
  exact forall_congr' fun V =>
    schemeTheoreticImageSubfunctor_preimage_eq_top_iff B S hS hU V.1.hom

/-! ### Intersections of scheme-theoretically dense open subspaces -/

/-- A closed subspace `Z` of an algebraic space `W` étale over `X` which contains the inverse
image of `U ⊓ V` is all of `W`, when `U` and `V` are scheme-theoretically dense in `X` and `V`
is open.

Indeed `V ×_X W` is an open subspace of `W`, so it is étale over `X`, and the inverse image of
`U` in it lands in the inverse image of `Z`, a closed subspace of `V ×_X W`; density of `U`
makes that inverse image all of `V ×_X W`, which says that `Z` contains `V ×_X W`, and density
of `V` then makes `Z` all of `W`. -/
private lemma eq_top_of_preimage_inf_le (hX : IsAlgebraicSpace B S hS X) (U V : Subfunctor X)
    (hV : IsOpenSubspace B S hS V)
    (hUdense : IsSchemeTheoreticallyDense B S hS U)
    (hVdense : IsSchemeTheoreticallyDense B S hS V)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W) (φ : W ⟶ X)
    (hφ : IsEtale B S hS φ) (Z : Subfunctor W) (hZ : IsClosedSubspace B S hS Z)
    (hle : (U ⊓ V).preimage φ ≤ Z) :
    Z = ⊤ := by
  have hVW : IsOpenSubspace B S hS (V.preimage φ) :=
    isOpenSubspace_preimage B S hS φ V hX hW hV
  have hιetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (V.preimage φ).ι :=
    MorphismProperty.relative_monotone (F := yoneda)
      (fun _ _ _ hk => @AlgebraicGeometry.Etale.instOfIsOpenImmersion _ _ _ hk) _ hVW.2
  have hψ : IsEtale B S hS ((V.preimage φ).ι ≫ φ) :=
    isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hιetale) hφ
  have hsub : Subfunctor.range (U.preimage ((V.preimage φ).ι ≫ φ)).ι ≤
      Z.preimage (V.preimage φ).ι := by
    rw [Subfunctor.range_ι]
    intro T z hz
    exact hle T ⟨hz, z.2⟩
  have hZVtop : Z.preimage (V.preimage φ).ι = ⊤ := by
    refine le_antisymm le_top ?_
    calc (⊤ : Subfunctor (V.preimage φ).toFunctor)
        = schemeTheoreticClosure B S hS (U.preimage ((V.preimage φ).ι ≫ φ)) :=
          (hUdense hVW.1 ((V.preimage φ).ι ≫ φ) hψ).symm
      _ ≤ Z.preimage (V.preimage φ).ι :=
          schemeTheoreticImageSubfunctor_le B S hS _
            (isClosedSubspace_preimage B S hS (V.preimage φ).ι Z hW hVW.1 hZ) hsub
  refine le_antisymm le_top ?_
  calc (⊤ : Subfunctor W) = schemeTheoreticClosure B S hS (V.preimage φ) :=
        (hVdense hW φ hφ).symm
    _ ≤ Z := schemeTheoreticImageSubfunctor_le B S hS _ hZ
        ((Subfunctor.preimage_eq_top_iff Z (V.preimage φ).ι).1 hZVtop)

/-- **Stacks 0837.** If `U` and `V` are scheme-theoretically dense open subspaces of an
algebraic space `X` over a scheme `S` contained in a big fppf site `B`, then so is `U ∩ V`.

Let `φ : W ⟶ X` be an étale morphism of algebraic spaces over `S`. The scheme-theoretic
closure of `(U ∩ V) ×_X W` in `W` is a closed subspace containing the inverse image of
`U ∩ V`, hence is all of `W` by
`AlgebraicGeometry.Space.eq_top_of_preimage_inf_le`: the density of `U` along the étale
morphism `V ×_X W ⟶ X` and the density of `V` along `φ` are used in turn. -/
@[stacks 0837]
theorem isSchemeTheoreticallyDense_inf (hX : IsAlgebraicSpace B S hS X) (U V : Subfunctor X)
    (hU : IsOpenSubspace B S hS U) (hV : IsOpenSubspace B S hS V)
    (hUdense : IsSchemeTheoreticallyDense B S hS U)
    (hVdense : IsSchemeTheoreticallyDense B S hS V) :
    IsOpenSubspace B S hS (U ⊓ V) ∧ IsSchemeTheoreticallyDense B S hS (U ⊓ V) := by
  refine ⟨isOpenSubspace_inf B S hS hX U V hU hV, ?_⟩
  intro W hW φ hφ
  refine eq_top_of_preimage_inf_le B S hS hX U V hV hUdense hVdense hW φ hφ _
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS ((U ⊓ V).preimage φ).ι hW) ?_
  have h := range_le_schemeTheoreticImageSubfunctor B S hS ((U ⊓ V).preimage φ).ι
  rwa [Subfunctor.range_ι] at h

/-- **Stacks 0833, condition (1) implies condition (2).** If an open subspace `U` of an
algebraic space `X` over a scheme `S` contained in a big fppf site `B` is scheme-theoretically
dense in `X`, then there is a scheme `V` and a surjective étale morphism `φ : V ⟶ X` such that
the scheme-theoretic closure of `U ×_X V` in `V` is all of `V`.

Take for `φ` any étale scheme atlas of `X`, which is surjective and étale after every
representable base change, hence surjective and étale as a morphism of algebraic spaces; the
density hypothesis applied to it is exactly the required equality. -/
theorem exists_surjective_etale_chart_schemeTheoreticClosure_eq_top
    (hX : IsAlgebraicSpace B S hS X) (U : Subfunctor X)
    (hU : IsSchemeTheoreticallyDense B S hS U) :
    ∃ (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ X),
      IsSurjective B S hS φ ∧ IsEtale B S hS φ ∧
        schemeTheoreticClosure B S hS (U.preimage φ) = ⊤ := by
  obtain ⟨V, φ, hsurj, hetale⟩ := hX.exists_atlas
  have hφ : IsEtale B S hS φ := isEtale_of_presheafEtale B S hS φ hetale
  exact ⟨V, φ, (presheafSurjective_iff_isSurjective_yoneda B S hS X hX V φ).1 hsurj, hφ,
    hU (isAlgebraicSpace_yoneda B S hS V) φ hφ⟩

/-- An étale morphism from a representable presheaf to an algebraic space is étale in the
relatively representable sense: apply the definition of Stacks 03FR to the identity chart of
the source. -/
lemma presheafEtale_of_isEtale_chart {V : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ X)
    (hφ : IsEtale B S hS φ) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ := by
  have hidE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj V)) := by
    have h := presheaf_yoneda_map_of_property B S hS (@Etale.{u}) (𝟙 V)
      (by rw [(BigFppfOver.toScheme B S hS).map_id V]; infer_instance)
    rwa [yoneda.map_id] at h
  have h := hφ V (𝟙 (yoneda.obj V)) hidE
  rwa [Category.id_comp] at h

/-- **The descent step in the proof of Stacks 0833.** Let `U` be a subspace of an algebraic
space `X` over a scheme `S` contained in a big fppf site `B` and let `φ : V ⟶ X` be a
surjective étale morphism from a scheme. If the scheme-theoretic closure of `U ×_X V` in `V` is
all of `V`, then the scheme-theoretic closure of `U` in `X` is all of `X`.

This is the first paragraph of the proof of Stacks 0833, read with `V' = X`: the
scheme-theoretic closure of `U ×_X V` in `V` is contained in the inverse image along `φ` of the
scheme-theoretic closure of `U` in `X`, by Stacks 0CP2, so that inverse image is everything,
and `AlgebraicGeometry.Space.subfunctor_eq_top_of_isSurjective_isEtale_preimage` descends this
to the closed subspace itself.

Unlike the converse step, this direction needs no hypothesis beyond the bare equality of the
closure with `V`; see
`AlgebraicGeometry.Space.isSchemeTheoreticallyDense_iff_exists_surjective_etale_chart` for why
the converse needs scheme-theoretic density of `U ×_X V` in `V` instead. -/
theorem schemeTheoreticClosure_eq_top_of_isSurjective_isEtale (hX : IsAlgebraicSpace B S hS X)
    (U : Subfunctor X) {V : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ X)
    (hsurj : IsSurjective B S hS φ) (hφ : IsEtale B S hS φ)
    (hclosure : schemeTheoreticClosure B S hS (U.preimage φ) = ⊤) :
    schemeTheoreticClosure B S hS U = ⊤ := by
  exact schemeTheoreticImageSubfunctor_eq_top_of_preimage_eq_top B S hS hX U V φ
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX V φ).2 hsurj)
    (presheafEtale_of_isEtale_chart B S hS φ hφ) hclosure

end Density

end Space

end AlgebraicGeometry

end
