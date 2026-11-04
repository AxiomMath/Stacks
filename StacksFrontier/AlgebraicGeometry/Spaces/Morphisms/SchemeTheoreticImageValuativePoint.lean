module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageValuativeDiagram
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImmersionFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion

/-!
# Reaching a point of the scheme-theoretic image by a valuation ring

Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, let `Z` be its scheme-theoretic image and let `z` be a point of `|Z|`.
Then there are a valuation ring `A` with fraction field `K` and a commutative diagram whose top
edge is `Spec K ⟶ X`, whose bottom edge is `Spec A ⟶ Z`, whose left edge is the inclusion of
`A` in `K` and whose right edge is the canonical morphism `X ⟶ Z`, and whose bottom edge
carries the closed point of `Spec A` to `z`. As a consequence, a quasi-compact morphism reaches
every point of codimension zero of its scheme-theoretic image.

## Main results

The names below live in the namespace `AlgebraicGeometry.Space`.

* `exists_valuativeSquare_toSchemeTheoreticImage`: every point of the scheme-theoretic image of
  a quasi-compact morphism is the image of the closed point of a valuative square over the
  canonical morphism to the image.
* `exists_fieldValuedPoint_of_localRingDimension_eq_zero`: a quasi-compact morphism whose
  scheme-theoretic image is everything reaches every point of codimension zero of its target.
* `exists_fieldValuedPoint_toSchemeTheoreticImage_of_localRingDimension_eq_zero`: the same for
  an arbitrary quasi-compact morphism and its scheme-theoretic image.

## References

* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 089B](https://stacks.math.columbia.edu/tag/089B)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace Cardinal

universe u

namespace AlgebraicGeometry.Space

/-! ### Valuation rings inside a residue field -/

/-- **A specialization in a scheme is witnessed by a valuation subring of a residue field.**
If `m w` specializes to `v`, then the local homomorphism `𝒪_{V, v} → 𝒪_{V, m w} → κ(m w) → κ(w)`
factors through a valuation subring `A` of `κ(w)`, and the resulting `Spec A ⟶ V` carries the
closed point to `v`, restricts over `κ(w)` to the composite `Spec κ(w) ⟶ W ⟶ V`, and has image
inside the closure of the image of `m`. -/
private theorem exists_valuationSubring_of_specializes {V W : Scheme.{u}} (m : W ⟶ V) (w : W)
    {v : V} (hsp : m w ⤳ v) :
    ∃ (A : ValuationSubring (W.residueField w)) (vA : Spec (.of A) ⟶ V),
      Spec.map (CommRingCat.ofHom (algebraMap A (W.residueField w))) ≫ vA =
          W.fromSpecResidueField w ≫ m ∧
        vA (closedPoint A) = v ∧
        Set.range (vA : Spec (.of A) → V) ⊆ closure (Set.range (m : W → V)) := by
  let φ : V.presheaf.stalk v ⟶ CommRingCat.of (W.residueField w) :=
    V.presheaf.stalkSpecializes hsp ≫ V.residue (m w) ≫ m.residueFieldMap w
  obtain ⟨A, hA, hAlocal⟩ := IsLocalRing.exists_factor_valuationRing φ.hom
  let localMap : CommRingCat.of (V.presheaf.stalk v) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (φ.hom.codRestrict A.toSubring hA)
  let _ : IsLocalHom localMap.hom := hAlocal
  set vA : Spec (.of A) ⟶ V := Spec.map localMap ≫ V.fromSpecStalk v with hvAdef
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap A (W.residueField w))) ≫ vA =
      W.fromSpecResidueField w ≫ m := by
    have hring : CommRingCat.ofHom ((algebraMap A (W.residueField w)).comp localMap.hom) = φ :=
      CommRingCat.hom_ext (by ext a; rfl)
    calc Spec.map (CommRingCat.ofHom (algebraMap A (W.residueField w))) ≫ vA
        = Spec.map (localMap ≫ CommRingCat.ofHom (algebraMap A (W.residueField w))) ≫
            V.fromSpecStalk v := by rw [hvAdef, ← Spec.map_comp_assoc]
      _ = Spec.map φ ≫ V.fromSpecStalk v := by rw [← CommRingCat.ofHom_comp, hring]
      _ = W.fromSpecResidueField w ≫ m := by
            show Spec.map (V.presheaf.stalkSpecializes hsp ≫
              V.residue (m w) ≫ m.residueFieldMap w) ≫ V.fromSpecStalk v = _
            rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
              Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp]
            exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField m w
  refine ⟨A, vA, hfac, ?_, ?_⟩
  · rw [hvAdef]
    show V.fromSpecStalk v (Spec.map localMap (closedPoint A)) = v
    rw [show Spec.map localMap (closedPoint A) = closedPoint (V.presheaf.stalk v) from
      IsLocalRing.comap_closedPoint localMap.hom]
    exact Scheme.fromSpecStalk_closedPoint
  · obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of (W.residueField w))) :=
      ⟨closedPoint (W.residueField w)⟩
    have ht : Spec.map (CommRingCat.ofHom (algebraMap A (W.residueField w))) t =
        genericPoint (Spec (CommRingCat.of A)) := by
      have : t.asIdeal.IsPrime := t.isPrime
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap A (W.residueField w)) t.asIdeal = _
      rw [genericPoint_eq_bot_of_affine, Ideal.eq_bot_of_prime t.asIdeal]
      ext x
      simp
    have hgen : vA (genericPoint (Spec (CommRingCat.of A))) = m w := by
      rw [← ht, ← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply,
        Scheme.fromSpecResidueField_apply]
    rintro _ ⟨p, rfl⟩
    have hspec : vA (genericPoint (Spec (CommRingCat.of A))) ⤳ vA p :=
      (genericPoint_specializes p).map vA.base.hom.continuous
    rw [hgen] at hspec
    exact closure_mono
      (Set.singleton_subset_iff.2 (Set.mem_range.2 ⟨w, rfl⟩)) hspec.mem_closure

/-- A point of the closure of the image of a quasi-compact morphism of schemes is the image of
a point of its scheme-theoretic image. -/
private theorem exists_image_point_of_mem_closure {T U : Scheme.{u}} (m : T ⟶ U)
    [QuasiCompact m] {x : U} (hx : x ∈ closure (Set.range (m : T → U))) :
    ∃ p : m.image, m.imageι p = x := by
  have hrange : Set.range (m.imageι : m.image → U) = closure (Set.range (m : T → U)) := by
    show Set.range (m.ker.subschemeι : _ → U) = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
  exact Set.mem_range.mp (hrange ▸ hx)

/-! ### Transfer of closures between a represented space and its scheme -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- The comparison map from the points of a represented presheaf to the points of the
representing scheme identifies closures. -/
private theorem pointsToScheme_mem_closure_iff {U : BigFppfOver B S hS}
    (C : Set (points B S hS (yoneda.obj U))) (x : points B S hS (yoneda.obj U)) :
    pointsToScheme B S hS U x ∈ closure (pointsToScheme B S hS U '' C) ↔ x ∈ closure C := by
  constructor
  · intro hx
    have hclosed : IsClosed (pointsToScheme B S hS U '' closure C) :=
      (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS U _).1 isClosed_closure
    obtain ⟨p, hp, hxp⟩ :=
      closure_minimal (Set.image_mono subset_closure) hclosed hx
    rwa [(injective_pointsToScheme B S hS U) hxp] at hp
  · intro hx
    have hclosed : IsClosed (pointsToScheme B S hS U ⁻¹'
        closure (pointsToScheme B S hS U '' C)) := by
      rw [isClosed_pointTopology_yoneda_iff_isClosed_image,
        Set.image_preimage_eq _ (surjective_pointsToScheme B S hS U)]
      exact isClosed_closure
    refine closure_minimal (fun c hc => Set.mem_preimage.2 (subset_closure ?_)) hclosed hx
    exact Set.mem_image_of_mem _ hc

/-- The comparison maps turn the image on points of a morphism of the site into the image of
the underlying morphism of schemes. -/
theorem image_pointsToScheme_range {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    pointsToScheme B S hS V '' Set.range (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) =
      Set.range ((BigFppfOver.toScheme B S hS).map h) := by
  rw [← Set.image_univ, image_pointsToScheme_image_pointsMap, Set.image_univ,
    Set.range_eq_univ.2 (surjective_pointsToScheme B S hS U), Set.image_univ]

/-- Membership in the closure of the image of a morphism of the site can be checked on points of
the represented presheaf or on the underlying schemes. -/
private theorem pointsToScheme_mem_closure_range_iff {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (p : points B S hS (yoneda.obj V)) :
    pointsToScheme B S hS V p ∈ closure (Set.range ((BigFppfOver.toScheme B S hS).map h)) ↔
      p ∈ closure (Set.range (pointsMap B S hS (yoneda.obj U) (yoneda.map h))) := by
  rw [← image_pointsToScheme_range B S hS h]
  exact pointsToScheme_mem_closure_iff B S hS _ p

/-! ### Stacks 089B -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over `S`,
let `Z` be its scheme-theoretic image and let `z` be a point of `|Z|`. There is a valuation
ring `A` with fraction field `K`, a morphism `Spec K ⟶ X` and a morphism `Spec A ⟶ Z` making
the square over the canonical morphism `X ⟶ Z` commute, such that the closed point of
`Spec A` maps to `z`. -/
@[stacks 089B]
theorem exists_valuativeSquare_toSchemeTheoreticImage (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsQuasiCompact B S hS f)
    (z : points B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor) :
    ∃ (q : ValuativeSquare (toSchemeTheoreticImage B S hS f))
      (w : points B S hS (yoneda.obj (siteObject B S hS q.ring_mem q.base))),
      pointsToScheme B S hS (siteObject B S hS q.ring_mem q.base) w = closedPoint q.R ∧
        pointsMap B S hS (yoneda.obj (siteObject B S hS q.ring_mem q.base)) q.special w = z := by
  classical
  set G := BigFppfOver.toScheme B S hS
  have hZc : IsClosedSubspace B S hS (schemeTheoreticImageSubfunctor B S hS f) :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hY
  have hZrange :
      Set.range (pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor
          (schemeTheoreticImageSubfunctor B S hS f).ι) =
        closure (Set.range (pointsMap B S hS X f)) :=
    range_pointsMap_ι_schemeTheoreticImage_eq_closure_of_isQuasiCompact B S hS f hX hY hf
  set y := pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor
    (schemeTheoreticImageSubfunctor B S hS f).ι z with hydef
  have hy : y ∈ closure (Set.range (pointsMap B S hS X f)) := hZrange ▸ ⟨z, rfl⟩
  obtain ⟨V, g, hVaff, hgPre, v, hv⟩ := exists_affine_etale_chart_at_point B S hS Y hY y
  have hgEt : IsEtale B S hS g := (isEtale_iff_presheaf_of_yoneda B S hS g).2 hgPre
  have hVsp : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have _ : IsAffine (G.obj V) := hVaff
  have _ : CompactSpace (G.obj V) := Scheme.compactSpace_of_isAffine _
  have hVqc : IsQuasiCompactSpace B S hS (yoneda.obj V) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS (yoneda.obj V) hVsp).2
      (compactSpace_points_yoneda B S hS V)
  have hPqc : IsQuasiCompactSpace B S hS (pullback g f) := hf (yoneda.obj V) hVsp hVqc g
  have hP : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hVsp hX hY
  obtain ⟨W, a, hWaff, haSurj, haEt⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (pullback g f) hP).1
      hPqc
  have _ : IsAffine (G.obj W) := hWaff
  have _ : CompactSpace (G.obj W) := Scheme.compactSpace_of_isAffine _
  set jW : W ⟶ V := yoneda.preimage (a ≫ pullback.fst g f)
  have hjW : yoneda.map jW = a ≫ pullback.fst g f := yoneda.map_preimage _
  set mW : G.obj W ⟶ G.obj V := G.map jW with hmWdef
  have _ : QuasiCompact mW := (quasiCompact_iff_compactSpace (f := mW)).mpr inferInstance
  have hsq : IsPullback (pullback.snd g f) (pullback.fst g f) f g :=
    (IsPullback.of_hasPullback g f).flip
  have hrangeW : Set.range (pointsMap B S hS (yoneda.obj W) (yoneda.map jW)) =
      Set.range (pointsMap B S hS (pullback g f) (pullback.fst g f)) := by
    rw [hjW, pointsMap_comp, Set.range_comp,
      Set.range_eq_univ.2 ((presheafSurjective_iff_isSurjective_yoneda B S hS
        (pullback g f) hP W a).mp haSurj), Set.image_univ]
  have hvcl : v ∈ closure (Set.range (pointsMap B S hS (yoneda.obj W) (yoneda.map jW))) := by
    rw [hrangeW, ← Set.image_univ (f := pointsMap B S hS (pullback g f) (pullback.fst g f)),
      ← Set.preimage_univ (f := pointsMap B S hS (pullback g f) (pullback.snd g f)),
      ← preimage_image_pointsMap_of_isPullback B S hS hsq Set.univ, Set.image_univ,
      ← (isOpenMap_pointsMap_of_isEtale B S hS g hVsp hY
          hgEt).preimage_closure_eq_closure_preimage (continuous_pointsMap B S hS g)]
    exact Set.mem_preimage.2 (hv ▸ hy)
  have hvscheme : pointsToScheme B S hS V v ∈ closure (Set.range (mW : G.obj W → G.obj V)) := by
    exact (pointsToScheme_mem_closure_range_iff B S hS jW v).2 hvcl
  obtain ⟨zimg, hzimg⟩ := exists_image_point_of_mem_closure mW hvscheme
  obtain ⟨w₀, hw₀⟩ := exists_specializes_of_image_point mW zimg
  rw [hzimg] at hw₀
  obtain ⟨A, vA, hfac, hclosedA, hrangeA⟩ := exists_valuationSubring_of_specializes mW w₀ hw₀
  have hKmem : B.Contains (Spec (.of ((G.obj W).residueField w₀))) :=
    B.residueField_spec_contains W.left.property w₀
  have hAmem : B.Contains (Spec (.of A)) := by
    show (Spec (.of A)).size < B.cutoff
    rw [Scheme.size_Spec]
    refine max_lt B.aleph0_lt_cutoff ?_
    have hK : Cardinal.mk ((G.obj W).residueField w₀) < B.cutoff := by
      have hcon := hKmem
      change (Spec (.of ((G.obj W).residueField w₀))).size < B.cutoff at hcon
      rw [Scheme.size_Spec] at hcon
      exact (le_max_right _ _).trans_lt hcon
    exact (Cardinal.mk_le_of_injective Subtype.val_injective).trans_lt hK
  set baseA : Spec (.of A) ⟶ S := vA ≫ B.inclusion.map V.hom with hbaseAdef
  set baseK : Spec (.of ((G.obj W).residueField w₀)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap A ((G.obj W).residueField w₀))) ≫ baseA with hbaseK
  set OA := siteObject B S hS hAmem baseA with hOAdef
  set OK := siteObject B S hS hKmem baseK with hOKdef
  set vV : B.obj hAmem ⟶ V.left := B.inclusion.preimage vA with hvVdef
  have hvV : B.inclusion.map vV = vA :=
    B.inclusion.map_preimage (X := B.obj hAmem) (Y := V.left) vA
  set specialV : OA ⟶ V := Over.homMk vV (by
    apply ObjectProperty.hom_ext
    show B.inclusion.map vV ≫ B.inclusion.map V.hom = baseA
    rw [hvV]) with hspecialVdef
  have hGspecialV : G.map specialV = vA := hvV
  set vK : B.obj hKmem ⟶ W.left :=
    B.inclusion.preimage ((G.obj W).fromSpecResidueField w₀) with hvKdef
  have hvK : B.inclusion.map vK = (G.obj W).fromSpecResidueField w₀ :=
    B.inclusion.map_preimage (X := B.obj hKmem) (Y := W.left)
      ((G.obj W).fromSpecResidueField w₀)
  have hjWbase : mW ≫ B.inclusion.map V.hom = B.inclusion.map W.hom := by
    rw [hmWdef]
    show B.inclusion.map jW.left ≫ B.inclusion.map V.hom = B.inclusion.map W.hom
    rw [← B.inclusion.map_comp]
    exact congrArg (fun t => B.inclusion.map t) (Over.w jW)
  set cK : OK ⟶ W := Over.homMk vK (by
    apply ObjectProperty.hom_ext
    show B.inclusion.map vK ≫ B.inclusion.map W.hom = baseK
    calc B.inclusion.map vK ≫ B.inclusion.map W.hom
        = (G.obj W).fromSpecResidueField w₀ ≫ mW ≫ B.inclusion.map V.hom := by
            rw [hvK, hjWbase]
      _ = ((G.obj W).fromSpecResidueField w₀ ≫ mW) ≫ B.inclusion.map V.hom :=
            (Category.assoc _ _ _).symm
      _ = (Spec.map (CommRingCat.ofHom (algebraMap A ((G.obj W).residueField w₀))) ≫ vA) ≫
            B.inclusion.map V.hom := by rw [hfac]
      _ = baseK := by rw [hbaseK, hbaseAdef, Category.assoc]) with hcKdef
  set fracHom : OK ⟶ OA := Over.homMk
    (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap A ((G.obj W).residueField w₀)))) :
      B.obj hKmem ⟶ B.obj hAmem) with hfracdef
  set specialY : yoneda.obj OA ⟶ Y := yoneda.map specialV ≫ g with hspecialYdef
  have hOAredScheme : IsReduced ((BigFppfOver.toScheme B S hS).obj OA) :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of A)))
  have hOAred : HasEtaleLocalProperty B S hS (yoneda.obj OA)
      (fun T : Scheme.{u} => IsReduced T) :=
    hasEtaleLocalProperty_of_representable B S hS (yoneda.obj OA)
      (fun T : Scheme.{u} => IsReduced T) OA (Iso.refl _) hOAredScheme
  have hsubV : Set.range (pointsMap B S hS (yoneda.obj OA) (yoneda.map specialV)) ⊆
      closure (Set.range (pointsMap B S hS (yoneda.obj W) (yoneda.map jW))) := by
    intro p hp
    refine (pointsToScheme_mem_closure_range_iff B S hS jW p).1 (hrangeA ?_)
    rw [← hGspecialV, ← image_pointsToScheme_range B S hS specialV]
    exact Set.mem_image_of_mem _ hp
  have hsub : Set.range (pointsMap B S hS (yoneda.obj OA) specialY) ⊆
      Set.range (pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor
        (schemeTheoreticImageSubfunctor B S hS f).ι) := by
    rw [hZrange, hspecialYdef, pointsMap_comp, Set.range_comp]
    refine (Set.image_mono hsubV).trans ?_
    refine (image_closure_subset_closure_image (continuous_pointsMap B S hS g)).trans
      (closure_mono ?_)
    rw [← Set.range_comp, ← pointsMap_comp, hjW]
    rintro _ ⟨t, rfl⟩
    refine ⟨pointsMap B S hS (yoneda.obj W) (a ≫ pullback.snd g f) t, ?_⟩
    rw [← Function.comp_apply (f := pointsMap B S hS X f), ← pointsMap_comp,
      Category.assoc, Category.assoc, hsq.w]
  obtain ⟨h, hh⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hY
    (isAlgebraicSpace_yoneda B S hS OA) (schemeTheoreticImageSubfunctor B S hS f) hZc hOAred
    specialY).2 hsub
  set wA := (pointsEquivScheme B S hS OA).symm (closedPoint A) with hwAdef
  have hptA : pointsToScheme B S hS OA wA = closedPoint A :=
    (pointsEquivScheme B S hS OA).apply_symm_apply (closedPoint A)
  have hspecialVpt : pointsMap B S hS (yoneda.obj OA) (yoneda.map specialV) wA = v := by
    refine (injective_pointsToScheme B S hS V) ?_
    rw [pointsToScheme_pointsMap_yoneda, hGspecialV, hptA]
    exact hclosedA
  have hfinal :
      pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor
          (schemeTheoreticImageSubfunctor B S hS f).ι
          (pointsMap B S hS (yoneda.obj OA) h wA) =
        pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor
          (schemeTheoreticImageSubfunctor B S hS f).ι z :=
    calc pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor
          (schemeTheoreticImageSubfunctor B S hS f).ι
          (pointsMap B S hS (yoneda.obj OA) h wA)
        = pointsMap B S hS (yoneda.obj OA)
            (h ≫ (schemeTheoreticImageSubfunctor B S hS f).ι) wA :=
          (congrFun (pointsMap_comp B S hS (yoneda.obj OA) h
            (schemeTheoreticImageSubfunctor B S hS f).ι) wA).symm
      _ = pointsMap B S hS (yoneda.obj OA) specialY wA :=
          congrArg (fun k : yoneda.obj OA ⟶ Y => pointsMap B S hS (yoneda.obj OA) k wA) hh
      _ = pointsMap B S hS (yoneda.obj V) g
            (pointsMap B S hS (yoneda.obj OA) (yoneda.map specialV) wA) := by
          rw [hspecialYdef]
          exact congrFun (pointsMap_comp B S hS (yoneda.obj OA) (yoneda.map specialV) g) wA
      _ = pointsMap B S hS (yoneda.obj V) g v :=
          congrArg (pointsMap B S hS (yoneda.obj V) g) hspecialVpt
      _ = pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor
            (schemeTheoreticImageSubfunctor B S hS f).ι z := hv.trans hydef
  refine ⟨{ R := A, K := (G.obj W).residueField w₀, ring_mem := hAmem, field_mem := hKmem
            base := baseA
            generic := yoneda.map cK ≫ a ≫ pullback.snd g f
            special := h
            comm := ?_ }, wA, ?_, ?_⟩
  · have hsite : cK ≫ jW = fracHom ≫ specialV := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      show B.inclusion.map vK ≫ B.inclusion.map jW.left =
        Spec.map (CommRingCat.ofHom (algebraMap A ((G.obj W).residueField w₀))) ≫
          B.inclusion.map vV
      rw [hvK, hvV]
      have hfac' : (G.obj W).fromSpecResidueField w₀ ≫ G.map jW =
          Spec.map (CommRingCat.ofHom (algebraMap A ((G.obj W).residueField w₀))) ≫ vA := by
        rw [← hmWdef]
        exact hfac.symm
      exact hfac'
    have hkey : (yoneda.map cK ≫ a ≫ pullback.snd g f) ≫ f =
        yoneda.map fracHom ≫ specialY := by
      rw [hspecialYdef]
      calc (yoneda.map cK ≫ a ≫ pullback.snd g f) ≫ f
          = yoneda.map cK ≫ a ≫ pullback.fst g f ≫ g := by
              simp only [Category.assoc, hsq.w]
        _ = yoneda.map (cK ≫ jW) ≫ g := by
              rw [Functor.map_comp, hjW]
              simp only [Category.assoc]
        _ = yoneda.map fracHom ≫ yoneda.map specialV ≫ g := by
              rw [hsite, Functor.map_comp, Category.assoc]
    refine (cancel_mono (schemeTheoreticImageSubfunctor B S hS f).ι).1 ?_
    simp only [Category.assoc]
    rw [toSchemeTheoreticImage_ι, hh]
    simpa only [Category.assoc] using hkey
  · exact hptA
  · exact pointsMap_injective_of_mono B S hS
      (schemeTheoreticImageSubfunctor B S hS f).ι hfinal

/-! ### Codimension-zero points of a scheme-theoretic image -/

/-- A generic point of an irreducible component admits no generization but itself. -/
private theorem eq_of_specializes_of_mem_genericPoints {α : Type*} [TopologicalSpace α]
    [T0Space α] {x y : α} (hy : y ∈ genericPoints α) (h : x ⤳ y) : x = y := by
  have h2 : y ⤳ x := specializes_iff_mem_closure.mpr
    (hy.2 isIrreducible_singleton.closure (specializes_iff_closure_subset.mp h)
      (subset_closure rfl))
  exact (h.antisymm h2).eq

/-- **A quasi-compact schematically dominant morphism onto a representable target reaches
every generic point of an irreducible component.** Let `f : X ⟶ h_T` be quasi-compact with
scheme-theoretic image all of `h_T`, and let `p` be a field-valued point of `h_T` whose point
of `T` is a generic point of an irreducible component. Then `p` is the image of a field-valued
point of `X`. -/
private theorem exists_fieldValuedPoint_of_mem_genericPoints {T : BigFppfOver B S hS}
    (f : X ⟶ yoneda.obj T) (hX : IsAlgebraicSpace B S hS X)
    (hf : IsQuasiCompact B S hS f)
    (htop : schemeTheoreticImageSubfunctor B S hS f = ⊤)
    (p : FieldValuedPoint B S hS (yoneda.obj T))
    (hp : schemePoint B S hS T p ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj T)) :
    ∃ r : FieldValuedPoint B S hS X,
      pointsMap B S hS X f (r.class B S hS X) = p.class B S hS (yoneda.obj T) := by
  classical
  set Z := schemeTheoreticImageSubfunctor B S hS f with hZdef
  let pZ : FieldValuedPoint B S hS Z.toFunctor :=
    { carrier := p.carrier
      contained := p.contained
      toBase := p.toBase
      value := ⟨p.value, by rw [htop]; trivial⟩ }
  have hpZ : pointsMap B S hS Z.toFunctor Z.ι (pZ.class B S hS Z.toFunctor) =
      p.class B S hS (yoneda.obj T) := rfl
  obtain ⟨q, w, hw1, hw2⟩ := exists_valuativeSquare_toSchemeTheoreticImage B S hS f hX
    (isAlgebraicSpace_yoneda B S hS T) hf (pZ.class B S hS Z.toFunctor)
  let qX : FieldValuedPoint B S hS X :=
    { carrier := q.K
      contained := q.field_mem
      toBase := Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base
      value := yonedaEquiv q.generic }
  let g : qX.siteObject B S hS X ⟶ siteObject B S hS q.ring_mem q.base :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))))
  have hgen : fieldMorphism B S hS X qX = q.generic := Equiv.symm_apply_apply _ _
  set s := yoneda.preimage (q.special ≫ Z.ι) with hsdef
  have hs : yoneda.map s = q.special ≫ Z.ι := yoneda.map_preimage _
  refine ⟨qX, ?_⟩
  have hfac : fieldMorphism B S hS X qX ≫ f = yoneda.map (g ≫ s) := by
    rw [hgen, Functor.map_comp, hs, ← Category.assoc, ← q.comm, Category.assoc,
      toSchemeTheoreticImage_ι]
  have hleft : pointsMap B S hS X f (qX.class B S hS X) =
      pointsMap B S hS (yoneda.obj (qX.siteObject B S hS X)) (yoneda.map (g ≫ s))
        ((qX.tautologicalPoint B S hS X).class B S hS (yoneda.obj (qX.siteObject B S hS X))) := by
    rw [← hfac, pointsMap_comp_apply, pointsMap_fieldMorphism_tautologicalPoint]
  have hright : p.class B S hS (yoneda.obj T) =
      pointsMap B S hS (yoneda.obj (siteObject B S hS q.ring_mem q.base)) (yoneda.map s) w := by
    rw [hs, pointsMap_comp_apply, hw2, hpZ]
  apply injective_pointsToScheme B S hS T
  have hL : pointsToScheme B S hS T (pointsMap B S hS X f (qX.class B S hS X)) =
      (BigFppfOver.toScheme B S hS).map s
        ((BigFppfOver.toScheme B S hS).map g
          (pointsToScheme B S hS (qX.siteObject B S hS X)
            ((qX.tautologicalPoint B S hS X).class B S hS
              (yoneda.obj (qX.siteObject B S hS X))))) := by
    rw [hleft, pointsToScheme_pointsMap_yoneda, Functor.map_comp, Scheme.Hom.comp_apply]
  have hR : pointsToScheme B S hS T (p.class B S hS (yoneda.obj T)) =
      (BigFppfOver.toScheme B S hS).map s (closedPoint q.R) := by
    rw [hright, pointsToScheme_pointsMap_yoneda, hw1]
  rw [hL, hR]
  refine eq_of_specializes_of_mem_genericPoints ?_
    ((IsLocalRing.specializes_closedPoint _).map
      ((BigFppfOver.toScheme B S hS).map s).continuous)
  rw [← hR, pointsToScheme_class]
  exact hp

/-- **A quasi-compact schematically dominant morphism of algebraic spaces over `S` reaches
every point of codimension zero of its target.** If `f : X ⟶ Y` is quasi-compact and the
scheme-theoretic image of `f` is all of `Y`, then every point of `|Y|` whose local ring has
dimension zero is the image of a field-valued point of `X`. -/
theorem exists_fieldValuedPoint_of_localRingDimension_eq_zero (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsQuasiCompact B S hS f)
    (htop : schemeTheoreticImageSubfunctor B S hS f = ⊤)
    (x : points B S hS Y) (hx : localRingDimension B S hS x = 0) :
    ∃ p : FieldValuedPoint B S hS X, pointsMap B S hS X f (p.class B S hS X) = x := by
  obtain ⟨T, a, u, ha, ⟨p, hpu, hpx⟩, hgen⟩ :=
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hY x).1 hx
  have hP : IsAlgebraicSpace B S hS (pullback f a) :=
    isAlgebraicSpace_pullback B S hS f a hX (isAlgebraicSpace_yoneda B S hS T) hY
  have hf' : IsQuasiCompact B S hS (pullback.snd f a) :=
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback f a) hf
  have htop' : schemeTheoreticImageSubfunctor B S hS (pullback.snd f a) = ⊤ := by
    rw [schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS f a
      hX hY (isAlgebraicSpace_yoneda B S hS T) hf ha, htop]
    exact (Subfunctor.preimage_eq_top_iff _ _).2 le_top
  obtain ⟨r, hr⟩ := exists_fieldValuedPoint_of_mem_genericPoints B S hS (pullback.snd f a) hP
    hf' htop' p (hpu ▸ hgen)
  refine ⟨FieldValuedPoint.map B S hS _ (pullback.fst f a) r, ?_⟩
  rw [← pointsMap_class, ← pointsMap_comp_apply, pullback.condition, pointsMap_comp_apply, hr,
    hpx]

/-- **A quasi-compact morphism of algebraic spaces over `S` reaches every point of codimension
zero of its scheme-theoretic image.** If `f : X ⟶ Y` is quasi-compact, then every point of the
scheme-theoretic image of `f` whose local ring has dimension zero is the image of a field-valued
point of `X` under the canonical morphism to the image. -/
theorem exists_fieldValuedPoint_toSchemeTheoreticImage_of_localRingDimension_eq_zero
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsQuasiCompact B S hS f)
    (z : points B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor)
    (hz : localRingDimension B S hS z = 0) :
    ∃ p : FieldValuedPoint B S hS X,
      pointsMap B S hS X (toSchemeTheoreticImage B S hS f) (p.class B S hS X) = z :=
  exists_fieldValuedPoint_of_localRingDimension_eq_zero B S hS (toSchemeTheoreticImage B S hS f)
    hX (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hY).1
    (isQuasiCompact_of_comp_mono B S hS (toSchemeTheoreticImage B S hS f)
      (schemeTheoreticImageSubfunctor B S hS f).ι (by rwa [toSchemeTheoreticImage_ι]))
    (schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top B S hS f hY) z hz

end AlgebraicGeometry.Space

end
