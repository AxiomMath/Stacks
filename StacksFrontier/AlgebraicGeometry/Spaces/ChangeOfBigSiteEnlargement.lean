module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteSmoothEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.BigFppfSiteCofinality
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CommonBigSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.EnlargementAboveCardinal

/-!
# Enlarging the big fppf site, and what survives it

The descent results for an inverse system of algebraic spaces indexed by a set `I` (Stacks 07SQ,
07SR, 0827, 0CP4, ...) are available in this library for a big fppf site whose cutoff has
cofinality above `#I`: below that bound the limit of the system is computed on the objects of
the site. A big fppf site can always be enlarged to one of arbitrarily large cofinality, and the
inverse image along the inclusion (Stacks 03FP, 04W1, `AlgebraicGeometry.changeBigSite`)
preserves and reflects everything such an argument needs to carry across. This file provides
both, so that a statement about algebraic spaces on an arbitrary big fppf site can be proved on
an enlargement where the index sets in play are small.

## Main results

* `AlgebraicGeometry.BigFppfSite.exists_isContained_lt_cof`: every big fppf site is contained in
  one whose cutoff has cofinality above a prescribed cardinal.
* `AlgebraicGeometry.changeBigSite_atlas`: a given surjective étale atlas transports, with the
  same source object and the same kernel pair.
* `AlgebraicGeometry.changeBigSite_isQuasiCompactSpace` and
  `AlgebraicGeometry.changeBigSite_isAbsolutelyQuasiSeparated`: quasi-compactness, and
  quasi-separatedness of a quasi-compact space, survive the enlargement.
* `AlgebraicGeometry.isRepresentable_changeBigSite_of_isRepresentable` and
  `AlgebraicGeometry.isRepresentable_of_isRepresentable_changeBigSite`: an algebraic space is a
  scheme exactly when its inverse image is.
* `AlgebraicGeometry.changeBigSiteProdYonedaIso` and
  `AlgebraicGeometry.isRepresentable_prod_yoneda_iff_changeBigSite`: the inverse image of
  `X ⨯ h_T` is `X' ⨯ h_{T}`, so representability of a base change `X_T` transports both ways.

## Implementation notes

Reflection of representability uses the size of the representing object: it receives a
surjection of sheaves from the image of an object of the smaller site, namely the transported
atlas, so it is no larger than that object
(`AlgebraicGeometry.Space.size_le_of_isLocallySurjective`) and lies in the smaller site; full
faithfulness of the inverse image (Stacks 04W1) then identifies the given space with the scheme it
represents.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 022J](https://stacks.math.columbia.edu/tag/022J)
* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **A big fppf site is contained in one of arbitrarily large cofinality.** -/
theorem BigFppfSite.exists_isContained_lt_cof (B : BigFppfSite.{u}) (lam : Cardinal.{u}) :
    ∃ (C : BigFppfSite.{u}) (_ : IsContained (τ := .fppf) B C), lam < C.cutoff.ord.cof := by
  obtain ⟨C, hcut, hcov, hlam⟩ := exists_bigFppfSite_le_of_lt_cof B lam
  exact ⟨C, isContained_of_le hcut hcov, hlam⟩

/-! ### Transport along the inverse image -/

section Transport

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **A surjective étale atlas transports to the enlarged site.** The inverse image of an
algebraic space `X` receives, from the sheaf represented by the same object `U` read in the
larger site, a surjective étale morphism whose kernel pair is represented by the same object
`R` with the same two projections, `R` being the kernel pair of the given atlas. -/
theorem changeBigSite_atlas (X : AlgebraicSpaces B S hS) {U : BigFppfOver B S hS}
    (q : yoneda.obj U ⟶ X.obj)
    (hqs : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqe : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U)
      (q' : yoneda.obj ((inclusionOver h S hS).obj U) ⟶ ((changeBigSite B B' h S hS).obj X).obj),
      (MorphismProperty.inverseImage (@Surjective.{u})
        (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf q' ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B' S (largerContains h hS))).presheaf q' ∧
      IsPullback (yoneda.map ((inclusionOver h S hS).map s))
        (yoneda.map ((inclusionOver h S hS).map t)) q' q' ∧
      IsPullback (yoneda.map s) (yoneda.map t) q q := by
  have _h₁ :=
    Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  have _h₂ :=
    Space.surjective_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  have _h₃ : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  have : HasFiniteLimits (siteCategory (τ := .fppf) B') :=
    hasFiniteLimits_siteCategory (τ := .fppf) B'
  have : HasFiniteLimits (Over (base (τ := .fppf) B' S (largerContains h hS))) := inferInstance
  have : HasBinaryProducts (BigFppfOver B' S (largerContains h hS)) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  obtain ⟨R, s, t, f, hls, hker, hsurj, hetale, hR⟩ :=
    sheafPullback_atlas B B' h S hS X.obj X.property q hqs hqe
  refine ⟨R, s, t, f, ?_, ?_, hker, hR⟩ <;>
    exact Space.presheaf_of_isLocallySurjective_of_kernelPair _ hls
      (((changeBigSite B B' h S hS).obj X).property.diagonal_representable.of_diag f) hker ‹_›

/-- **Quasi-compactness survives enlarging the big fppf site.** -/
theorem changeBigSite_isQuasiCompactSpace (X : AlgebraicSpaces B S hS)
    (hX : Space.IsQuasiCompactSpace B S hS X.obj) :
    Space.IsQuasiCompactSpace B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj := by
  obtain ⟨U, q, hU, hqs, hqe⟩ := hX
  obtain ⟨R, s, t, q', hqs', hqe', -, -⟩ := changeBigSite_atlas B B' h S hS X q hqs
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS q).1 hqe)
  exact ⟨(inclusionOver h S hS).obj U, q', hU, hqs',
    (Space.isEtale_iff_presheaf_of_yoneda B' S (largerContains h hS) q').2 hqe'⟩

/-- **Absolute quasi-separatedness of a quasi-compact algebraic space survives enlarging the big
fppf site.** An affine atlas of `X` has a kernel pair with quasi-compact projections, because `X`
is quasi-separated; the transported atlas has the same kernel pair, so Stacks 07S4 applies on the
larger site. -/
theorem changeBigSite_isAbsolutelyQuasiSeparated (X : AlgebraicSpaces B S hS)
    (hqc : Space.IsQuasiCompactSpace B S hS X.obj)
    (hqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.obj) :
    Space.IsAbsolutelyQuasiSeparated B' S (largerContains h hS) B'.contains_terminal
      ((changeBigSite B B' h S hS).obj X).obj := by
  obtain ⟨U, q, hU, hqsurj, hqe⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.obj
      X.property).1 hqc
  obtain ⟨R, s, t, q', hqs', hqe', hker', hker⟩ := changeBigSite_atlas B B' h S hS X q hqsurj
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS q).1 hqe)
  have hUc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
  have hRc : CompactSpace ((BigFppfOver.toScheme B S hS).obj R) :=
    Space.compactSpace_of_isAbsolutelyQuasiSeparated B S hS B.contains_terminal hqs hker hUc hUc
  have ht : QuasiCompact ((BigFppfOver.toScheme B S hS).map t) :=
    quasiCompact_of_compactSpace_of_isAffine _ hU hRc
  have hUqs : QuasiSeparated (B'.inclusion.map ((inclusionOver h S hS).obj U).hom ≫
      terminal.from S) := by
    have hq := (quasiSeparatedSpace_iff_quasiSeparated
      ((BigFppfOver.toScheme B S hS).obj U)).mp inferInstance
    rwa [terminal.hom_ext (terminal.from ((BigFppfOver.toScheme B S hS).obj U))
      (B'.inclusion.map ((inclusionOver h S hS).obj U).hom ≫ terminal.from S)] at hq
  exact Space.isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection B' S
    (largerContains h hS) B'.contains_terminal ((changeBigSite B B' h S hS).obj X).property
    hqs' hqe' hUqs hker' ht

/-- **A representable algebraic space stays representable after enlarging the big fppf site**,
by the image of its representing object (Stacks 03FP, part (1)). -/
theorem isRepresentable_changeBigSite_of_isRepresentable (X : AlgebraicSpaces B S hS)
    (hX : X.obj.IsRepresentable) : ((changeBigSite B B' h S hS).obj X).obj.IsRepresentable := by
  let eX : (schemeSpaceFunctor B S hS).obj X.obj.reprX ≅ X := ObjectProperty.isoMk _ X.obj.reprW
  exact Functor.IsRepresentable.mk' (changeBigSiteYonedaIso B B' h S hS X.obj.reprX ≪≫
    (ObjectProperty.ι (fun F => IsAlgebraicSpace B' S (largerContains h hS) F)).mapIso
      ((changeBigSite B B' h S hS).mapIso eX))

/-- **An algebraic space is representable as soon as it is after enlarging the big fppf site.**
A representing object of the inverse image receives a surjection from the image of an object of
the smaller site — the transported atlas — so it is no larger than that object and lies in the
smaller site; the inverse image is fully faithful (Stacks 04W1), so the given space is
represented by it. -/
theorem isRepresentable_of_isRepresentable_changeBigSite (X : AlgebraicSpaces B S hS)
    (hX : ((changeBigSite B B' h S hS).obj X).obj.IsRepresentable) : X.obj.IsRepresentable := by
  let Y := ((changeBigSite B B' h S hS).obj X).obj
  let T' := Y.reprX
  let eY : yoneda.obj T' ≅ Y := Y.reprW
  obtain ⟨U, -, -, -, f, hls, -⟩ := exists_sheafPullback_atlas B B' h S hS X.obj X.property
  let g : (inclusionOver h S hS).obj U ⟶ T' := yoneda.preimage (f ≫ eY.inv)
  have hg : Presheaf.IsLocallySurjective (BigFppfOver.topology B' S (largerContains h hS))
      (yoneda.map g) :=
    Presheaf.isLocallySurjective_yoneda_map_preimage_comp_iso _ f hls eY.symm
  have hsize : T'.left.obj.size < B.cutoff :=
    (Space.size_le_of_isLocallySurjective B' S (largerContains h hS) g hg).trans_lt
      U.left.property
  let T : BigFppfOver B S hS :=
    Over.mk (Y := (⟨T'.left.obj, hsize⟩ : B.Schemes)) (ObjectProperty.homMk T'.hom.hom)
  let eT : (inclusionOver h S hS).obj T ≅ T' := Over.isoMk (Iso.refl _) rfl
  let e : (changeBigSite B B' h S hS).obj ((schemeSpaceFunctor B S hS).obj T) ≅
      (changeBigSite B B' h S hS).obj X :=
    ObjectProperty.isoMk _ ((changeBigSiteYonedaIso B B' h S hS T).symm ≪≫
      yoneda.mapIso eT ≪≫ eY)
  let e' := (changeBigSite_fullyFaithful B B' h S hS).some.preimageIso e
  exact Functor.IsRepresentable.mk'
    ((ObjectProperty.ι (fun F => IsAlgebraicSpace B S hS F)).mapIso e')

/-- **The inverse image preserves binary products of algebraic spaces.** If the product of two
algebraic spaces over `S` is an algebraic space, the images of its two projections exhibit the
inverse image of the product as the product of the inverse images: the inverse image is left
exact on sheaves (Stacks 00X5), and a product of sheaves is computed on presheaves. -/
def isLimitChangeBigSiteBinaryFan (X Y : AlgebraicSpaces B S hS)
    (hXY : IsAlgebraicSpace B S hS (X.obj ⨯ Y.obj)) :
    IsLimit (BinaryFan.mk
      ((changeBigSite B B' h S hS).map (ObjectProperty.homMk
        (prod.fst : X.obj ⨯ Y.obj ⟶ X.obj) :
          (⟨X.obj ⨯ Y.obj, hXY⟩ : AlgebraicSpaces B S hS) ⟶ X)).hom
      ((changeBigSite B B' h S hS).map (ObjectProperty.homMk
        (prod.snd : X.obj ⨯ Y.obj ⟶ Y.obj) :
          (⟨X.obj ⨯ Y.obj, hXY⟩ : AlgebraicSpaces B S hS) ⟶ Y)).hom) := by
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S (largerContains h hS)
  let i := inclusionOver h S hS
  have : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  have : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let L := i.sheafPullback (Type u) J K
  have : PreservesFiniteLimits L :=
    inclusionOver_preservesFiniteLimits_sheafPullback B B' h S hS
  let A : Sheaf J (Type u) := ⟨X.obj, X.property.isSheaf⟩
  let A' : Sheaf J (Type u) := ⟨Y.obj, Y.property.isSheaf⟩
  let P : Sheaf J (Type u) := ⟨X.obj ⨯ Y.obj, hXY.isSheaf⟩
  let c : BinaryFan A A' := BinaryFan.mk (⟨prod.fst⟩ : P ⟶ A) (⟨prod.snd⟩ : P ⟶ A')
  have hc : IsLimit c := isLimitOfReflects (sheafToPresheaf J (Type u))
    ((isLimitMapConeBinaryFanEquiv (sheafToPresheaf J (Type u)) _ _).symm
      (prodIsProd X.obj Y.obj))
  exact (isLimitMapConeBinaryFanEquiv (L ⋙ sheafToPresheaf K (Type u)) _ _)
    (isLimitOfPreserves (L ⋙ sheafToPresheaf K (Type u)) hc)

/-- **The inverse image of a product with a represented sheaf** is the product of the inverse
image with the sheaf represented by the image of the representing object. -/
def changeBigSiteProdYonedaIso (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (hXT : IsAlgebraicSpace B S hS (X.obj ⨯ yoneda.obj T)) :
    ((changeBigSite B B' h S hS).obj ⟨X.obj ⨯ yoneda.obj T, hXT⟩).obj ≅
      ((changeBigSite B B' h S hS).obj X).obj ⨯ yoneda.obj ((inclusionOver h S hS).obj T) :=
  (isLimitChangeBigSiteBinaryFan B B' h S hS X ((schemeSpaceFunctor B S hS).obj T)
      hXT).conePointUniqueUpToIso (prodIsProd _ _) ≪≫
    prod.mapIso (Iso.refl _) (changeBigSiteYonedaIso B B' h S hS T).symm

/-- **Representability of a product with a represented sheaf is unchanged by enlarging the big
fppf site.** This is the form in which representability of a base change `X_T` transports: `X_T`
is representable exactly when `X ⨯ h_T` is. -/
theorem isRepresentable_prod_yoneda_iff_changeBigSite (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) (hXT : IsAlgebraicSpace B S hS (X.obj ⨯ yoneda.obj T)) :
    (((changeBigSite B B' h S hS).obj X).obj ⨯
        yoneda.obj ((inclusionOver h S hS).obj T)).IsRepresentable ↔
      (X.obj ⨯ yoneda.obj T).IsRepresentable := by
  let e := changeBigSiteProdYonedaIso B B' h S hS X T hXT
  exact ⟨fun _ => isRepresentable_of_isRepresentable_changeBigSite B B' h S hS ⟨_, hXT⟩
      (Functor.IsRepresentable.mk' (Functor.reprW _ ≪≫ e.symm)),
    fun hrep => have := isRepresentable_changeBigSite_of_isRepresentable B B' h S hS ⟨_, hXT⟩ hrep
      Functor.IsRepresentable.mk' (Functor.reprW _ ≪≫ e)⟩

end Transport

end AlgebraicGeometry

end
