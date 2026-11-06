module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactLocal

/-!
# Quasi-separatedness and quasi-compactness of an affine étale atlas

Let `F` be an algebraic space over a scheme `S` with a surjective étale atlas
`q : h_U ⟶ F` whose source is affine, and suppose that the product `U ⨯ U` formed in the big
fppf category over `S` is affine as well. Then `F` is quasi-separated over `S` exactly when
`q` is a quasi-compact morphism of algebraic spaces. Both directions compare the kernel pair
`R = U ×_F U` of the atlas with the diagonal of `F`, using that `R ⟶ U ⨯ U` is the base change
of the diagonal along the induced chart `h_{U ⨯ U} ⟶ F ⨯ F` of
`AlgebraicGeometry.Space.atlasProd`.

The hypothesis that `U ⨯ U` is affine is automatic when the structure morphism of `U` maps
into an affine open of `S`, which is how the atlases produced by Stacks 03FY arrive; that
implication is `AlgebraicGeometry.Space.isAffine_prod_of_mapsTo_isAffineOpen`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isQuasiSeparatedOver_of_mono`: quasi-separatedness over `S` passes
  to a subobject.
* `AlgebraicGeometry.Space.isAffine_prod_of_mapsTo_isAffineOpen`: an affine object of the site
  whose structure morphism lands in an affine open of `S` has affine self-product.
* `AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiSeparatedOver_affineEtaleAtlas` and
  `AlgebraicGeometry.Space.isQuasiSeparatedOver_of_isQuasiCompact_affineEtaleAtlas`: the two
  directions of the comparison above.
* `AlgebraicGeometry.Space.presheafQuasiCompact_of_isQuasiCompact_affineEtaleAtlas`: an
  affine quasi-compact atlas is quasi-compact after every represented base change.
* `AlgebraicGeometry.Space.isQuasiCompact_of_isAffine_of_isQuasiCompact_atlas`: once one
  affine surjective étale atlas of `F` is quasi-compact, every morphism to `F` from a
  representable presheaf with affine source is quasi-compact.
* `AlgebraicGeometry.Space.IsQuasiCompact.of_comp_mono`: quasi-compactness of a morphism is
  inherited by a factor through a monomorphism.

## Implementation notes

Quasi-separatedness over `S` is quasi-compactness of the absolute diagonal after every
represented base change, so it transports along the cartesian squares of
`StacksFrontier/AlgebraicGeometry/Spaces/Diagonal.lean` by stability of a relative morphism
property under base change. Passing between that reading and quasi-compactness in the sense
of Stacks 03HE is `AlgebraicGeometry.Space.isQuasiCompact_of_presheaf_quasiCompact` and
Stacks 02WZ, `AlgebraicGeometry.presheaf_inverseImage_iff_atlas_snd`.

The factorization of the structure morphism of `U` through an affine open `V` of `S` is
`AlgebraicGeometry.IsOpenImmersion.lift`; the self-product of `U` is then the fibre product
of that factorization with itself over `V`, which is affine because `V` and the underlying
scheme of `U` are.

## References

* [Stacks Project, Tag 03W7](https://stacks.math.columbia.edu/tag/03W7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two permanence properties of quasi-compactness of a morphism -/

/-- A morphism which factors through a monomorphism inherits quasi-compactness in the sense of
Stacks 03HE from the composite: the square with the identity on the source is cartesian. -/
theorem IsQuasiCompact.of_comp_mono {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (i : G ⟶ H) [Mono i] (h : IsQuasiCompact B S hS (f ≫ i)) :
    IsQuasiCompact B S hS f :=
  IsQuasiCompact.of_isPullback B S hS
    (IsPullback.of_horiz_isIso_mono (fst := 𝟙 F) (snd := f) (f := f ≫ i) (g := i)
      ⟨by simp⟩) h

/-! ### Quasi-separatedness over the base passes to a subobject -/

/-- Quasi-separatedness over `S` passes to a subobject: for a monomorphism `f : F ⟶ G` the
diagonal of `F` is the base change of the diagonal of `G` along `f ⨯ f`, since `(1, 1)` is a
kernel pair of a monomorphism. -/
theorem isQuasiSeparatedOver_of_mono {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    [Mono f] (hG : IsQuasiSeparatedOver B S hS G) : IsQuasiSeparatedOver B S hS F := by
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_diag_prodLift (IsKernelPair.id_of_mono f)) hG

/-- Quasi-separatedness over `S` passes to a subfunctor. -/
theorem isQuasiSeparatedOver_subfunctor {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsQuasiSeparatedOver B S hS F) (G : Subfunctor F) :
    IsQuasiSeparatedOver B S hS G.toFunctor :=
  isQuasiSeparatedOver_of_mono B S hS G.ι hF

/-! ### Affineness of the self-product of an object lying over an affine open -/

/-- An object of the big fppf category over `S` with affine underlying scheme whose structure
morphism maps into an affine open `V` of `S` has affine self-product `U ⨯ U`: the structure
morphism factors through the open immersion of `V`, and the self-product is the fibre product
of that factorization with itself, formed over the affine scheme `V`. -/
theorem isAffine_prod_of_mapsTo_isAffineOpen (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (V : S.Opens) (hV : IsAffineOpen V)
    (himage : ∀ t : (BigFppfOver.toScheme B S hS).obj U, (B.inclusion.map U.hom) t ∈ V) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (U ⨯ U)) := by
  have hrange : Set.range (B.inclusion.map U.hom).base ⊆ Set.range V.ι := by
    rintro y ⟨t, rfl⟩
    exact ⟨⟨_, himage t⟩, rfl⟩
  let a : (BigFppfOver.toScheme B S hS).obj U ⟶ V.toScheme :=
    IsOpenImmersion.lift V.ι (B.inclusion.map U.hom) hrange
  have _ : IsAffine V.toScheme := hV
  -- the fibre product of `V.ι` with `a ≫ V.ι` is the source of `a`, since `V.ι` is a
  -- monomorphism and the square with the identity on that source commutes
  have hinner : IsPullback a (𝟙 ((BigFppfOver.toScheme B S hS).obj U)) V.ι (a ≫ V.ι) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have _ : IsAffine (pullback V.ι (a ≫ V.ι)) :=
    .of_isIso (hinner.isoIsPullback _ _ (IsPullback.of_hasPullback V.ι (a ≫ V.ι))).inv
  -- the self-product in the slice is the fibre product of the structure morphisms
  have _ : IsAffine (pullback (B.inclusion.map U.hom) (B.inclusion.map U.hom)) := by
    rw [← IsOpenImmersion.lift_fac V.ι (B.inclusion.map U.hom) hrange]
    exact .of_isIso (pullbackRightPullbackFstIso V.ι (a ≫ V.ι) a).inv
  exact IsAffine.of_isIso
    (B.inclusion.mapIso (Over.prodLeftIsoPullback U U) ≪≫
      (Functor.map_isPullback B.inclusion (IsPullback.of_hasPullback U.hom U.hom)).isoIsPullback
        _ _ (IsPullback.of_hasPullback (B.inclusion.map U.hom)
          (B.inclusion.map U.hom))).hom

/-! ### Quasi-separatedness over the base and a quasi-compact affine étale atlas -/

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
/-- If `q' : h_{U'} ⟶ F` is quasi-compact and `U` is affine, then the scheme representing the
fibre product of `q'` with a morphism `q : h_U ⟶ F` has compact underlying space. -/
private theorem compactSpace_pullback_of_isQuasiCompact {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U U' : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F)
    (q' : yoneda.obj U' ⟶ F) (hrel : yoneda.relativelyRepresentable q)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) (hq' : IsQuasiCompact B S hS q') :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (hrel.pullback q')) :=
  compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
    ((hq' (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) q).of_iso B S hS
        ((hrel.isPullback' q').isoIsPullback _ _ (IsPullback.of_hasPullback q q')).symm)

/-- **A quasi-separated algebraic space has quasi-compact affine étale atlases.** If `F` is
quasi-separated over `S` then every surjective étale atlas `q : h_U ⟶ F` with `U` and `U ⨯ U`
affine is a quasi-compact morphism: the kernel pair of `q` is the base change of the diagonal
along the induced chart of `F ⨯ F`, hence quasi-compact over the affine `U ⨯ U`, so it is
quasi-compact over `U`, and Stacks 02WZ transfers that to `q`. -/
theorem isQuasiCompact_of_isQuasiSeparatedOver_affineEtaleAtlas
    (hF : IsAlgebraicSpace B S hS F) (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hUU : IsAffine ((BigFppfOver.toScheme B S hS).obj (U ⨯ U)))
    (hQS : IsQuasiSeparatedOver B S hS F)
    (hqSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    IsQuasiCompact B S hS q := by
  have hrel : yoneda.relativelyRepresentable q := hF.diagonal_representable.of_diag q
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  -- the kernel pair is quasi-compact over `U ⨯ U`
  have hker : AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hrel)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).1
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_kernelPairToProd B S hS hrel) hQS)
  have hRcompact : CompactSpace
      ((BigFppfOver.toScheme B S hS).obj (hrel.pullback q)) := by
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (U ⨯ U)) := hUU
    exact AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hrel))
  -- hence quasi-compact over the affine `U`
  have hproj : AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (hrel.snd q)) :=
    quasiCompact_of_compactSpace_of_isAffine _ hU hRcompact
  exact isQuasiCompact_of_presheaf_quasiCompact B S hS
    ((presheaf_inverseImage_iff_atlas_snd B S hS
      (@AlgebraicGeometry.QuasiCompact.{u}) q hrel U q hqSurj hqEtale).2 hproj)

/-- **An affine quasi-compact atlas is quasi-compact after every represented base change.**
This is Stacks 03HD for an atlas whose source is affine, proved from the definition of
Stacks 03HE rather than from representability of the atlas. -/
theorem presheafQuasiCompact_of_isQuasiCompact_affineEtaleAtlas
    (hF : IsAlgebraicSpace B S hS F) (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hq : IsQuasiCompact B S hS q)
    (hqSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hrel : yoneda.relativelyRepresentable q := hF.diagonal_representable.of_diag q
  have hRcompact := compactSpace_pullback_of_isQuasiCompact B S hS U U q q hrel hU hq
  exact (presheaf_inverseImage_iff_atlas_snd B S hS
    (@AlgebraicGeometry.QuasiCompact.{u}) q hrel U q hqSurj hqEtale).2
      (quasiCompact_of_compactSpace_of_isAffine _ hU hRcompact)

/-- **An algebraic space with a quasi-compact affine étale atlas is quasi-separated.** The
kernel pair of the atlas is quasi-compact, hence has compact underlying scheme, hence is
quasi-compact over the affine `U ⨯ U`; it represents the base change of the diagonal of `F`
along the induced chart of `F ⨯ F`, which is again surjective and étale, so Stacks 02WZ
transfers quasi-compactness to the diagonal. -/
theorem isQuasiSeparatedOver_of_isQuasiCompact_affineEtaleAtlas
    (hF : IsAlgebraicSpace B S hS F) (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hUU : IsAffine ((BigFppfOver.toScheme B S hS).obj (U ⨯ U)))
    (hq : IsQuasiCompact B S hS q)
    (hqSurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    IsQuasiSeparatedOver B S hS F := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.IsStableUnderComposition
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have _ : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have hdiag : yoneda.relativelyRepresentable (diag F) := hF.diagonal_representable
  have hrel : yoneda.relativelyRepresentable q := hdiag.of_diag q
  -- the kernel pair of the atlas has compact underlying scheme
  have hRcompact := compactSpace_pullback_of_isQuasiCompact B S hS U U q q hrel hU hq
  -- so `R ⟶ U ⨯ U` is quasi-compact, the target being affine
  have hqcJ : AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hrel)) :=
    quasiCompact_of_compactSpace_of_isAffine _ hUU hRcompact
  -- and it represents the base change of the diagonal along the induced chart
  have hqcSnd : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (hdiag.snd (atlasProd B S hS q))) :=
    property_of_isPullback_of_isPullback B S hS
      (hdiag.isPullback (atlasProd B S hS q))
      (isPullback_kernelPairToProd B S hS hrel) hqcJ
  exact (presheaf_inverseImage_iff_atlas_snd B S hS
    (@AlgebraicGeometry.QuasiCompact.{u}) (diag F) hdiag (U ⨯ U) (atlasProd B S hS q)
      (presheaf_atlasProd B S hS _ q hqSurj) (presheaf_atlasProd B S hS _ q hqEtale)).2
        hqcSnd

/-- **One quasi-compact affine atlas makes every affine chart quasi-compact.** If `F` has a
quasi-compact surjective étale atlas with affine source, then every morphism to `F` from a
representable presheaf with affine source is quasi-compact: the fibre product of the chart
with the given atlas is quasi-compact, hence has compact underlying scheme, so it is
quasi-compact over the affine source of the atlas, and Stacks 02WZ transfers that to the
chart. -/
theorem isQuasiCompact_of_isAffine_of_isQuasiCompact_atlas
    (hF : IsAlgebraicSpace B S hS F)
    (U₀ : BigFppfOver B S hS) (q₀ : yoneda.obj U₀ ⟶ F)
    (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (hq₀ : IsQuasiCompact B S hS q₀)
    (hq₀surj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q₀)
    (hq₀etale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q₀)
    (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    IsQuasiCompact B S hS q := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hrel : yoneda.relativelyRepresentable q := hF.diagonal_representable.of_diag q
  have hcompact := compactSpace_pullback_of_isQuasiCompact B S hS U U₀ q q₀ hrel hU hq₀
  exact isQuasiCompact_of_presheaf_quasiCompact B S hS
    ((presheaf_inverseImage_iff_atlas_snd B S hS
      (@AlgebraicGeometry.QuasiCompact.{u}) q hrel U₀ q₀ hq₀surj hq₀etale).2
        (quasiCompact_of_compactSpace_of_isAffine _ hU₀ hcompact))

end AlgebraicGeometry.Space

end
