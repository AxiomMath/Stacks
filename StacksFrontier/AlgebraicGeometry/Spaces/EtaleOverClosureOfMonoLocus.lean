module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointLiftQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.EtaleAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ImmersionSchemeTheoreticallyDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal

/-!
# Étaleness over the closure of a locus where a flat morphism is a monomorphism

Let `F : E ⟶ Y` be a flat and separated morphism of algebraic spaces over a scheme `S`, locally
of finite presentation, and let `h : W ⟶ Y` be a quasi-compact immersion such that the base
change `E ×_Y W ⟶ W` is a monomorphism.  Then `F` is étale at every point of `E` whose image in
`|Y|` lies in the closure of the image of `|W|`.

Indeed let `Z ⊆ Y` be the scheme-theoretic image of `h`; then `W` is a scheme-theoretically
dense open subspace of `Z` (Stacks 088G).  The base change `F_Z : E_Z = E ×_Y Z ⟶ Z` is flat,
separated and locally of finite presentation, so `P = E_Z ×_Z E_Z` is flat over `Z`, the inverse
image of `W` in `P` is scheme-theoretically dense in `P`, and that inverse image lies in the
diagonal, `F_Z` being a monomorphism over `W`.  The diagonal is a closed immersion containing a
scheme-theoretically dense open subspace, hence an isomorphism, so `F_Z` is unramified.  Since
the unramified locus is compatible with base change, `F` is unramified, and hence étale, at the
points over `|Z|`, which contains the closure of the image of `|W|`.

## Main results

* `AlgebraicGeometry.Space.isEtaleAt_of_mono_pullback_snd`: the statement above.
* `AlgebraicGeometry.Space.bijective_etaleLocalRingMap_of_isEtaleAt`: at a geometric point over
  a point where a morphism is étale, its homomorphism of étale local rings is bijective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site times out at the default
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this). -/
local instance hasPullbacks_presheaf_EtaleOverClosureOfMonoLocus :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for limits of cospans of presheaves on the big fppf site. -/
local instance (priority := high) hasPullback_presheaf_EtaleOverClosureOfMonoLocus
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **A closed subspace containing a scheme-theoretically dense subspace is everything.** -/
theorem eq_top_of_isSchemeTheoreticallyDense_le {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {U C : Subfunctor X}
    (hU : IsSchemeTheoreticallyDense B S hS U) (hC : IsClosedSubspace B S hS C) (hUC : U ≤ C) :
    C = ⊤ := by
  have h := hU hX (𝟙 X) (isEtale_of_isIso B S hS (𝟙 X))
  rw [Subfunctor.preimage_id] at h
  refine top_le_iff.1 ?_
  rw [← h]
  exact schemeTheoreticImageSubfunctor_le B S hS U.ι hC (by rwa [Subfunctor.range_ι])

/-- Flatness together with local finite presentation is stable under base change. -/
private theorem isFlat_and_isLocallyOfFinitePresentation_of_isPullback
    {X Y Z T : AlgebraicSpaces B S hS} {p : T ⟶ Y} {q : T ⟶ X} {g : Y ⟶ Z} {f : X ⟶ Z}
    (sq : IsPullback p q g f)
    (hg : IsFlat B S hS g.hom ∧ IsLocallyOfFinitePresentation B S hS g.hom) :
    IsFlat B S hS q.hom ∧ IsLocallyOfFinitePresentation B S hS q.hom :=
  ⟨(isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hg.1,
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hg.2⟩

/-- Flatness together with local finite presentation is stable under composition. -/
private theorem isFlat_and_isLocallyOfFinitePresentation_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hH : IsAlgebraicSpace B S hS H) {f : F ⟶ G} {g : G ⟶ H}
    (hf : IsFlat B S hS f ∧ IsLocallyOfFinitePresentation B S hS f)
    (hg : IsFlat B S hS g ∧ IsLocallyOfFinitePresentation B S hS g) :
    IsFlat B S hS (f ≫ g) ∧ IsLocallyOfFinitePresentation B S hS (f ≫ g) :=
  ⟨isFlat_comp B S hS hF hG hH _ _ hf.1 hg.1,
    isLocallyOfFinitePresentation_comp B S hS hF hG hH _ _ hf.2 hg.2⟩

set_option synthInstance.maxHeartbeats 400000 in
-- instance searches over presheaves on the big fppf site in this proof exceed the default
/-- **A flat separated morphism locally of finite presentation which is a monomorphism over a
quasi-compact immersion is étale over the closure of its image.** Let `F : E ⟶ Y` be flat,
separated and locally of finite presentation and let `h : W ⟶ Y` be a quasi-compact immersion
such that `E ×_Y W ⟶ W` is a monomorphism.  Then `F` is étale at every point of `E` lying over
the closure of the image of `|W|` in `|Y|`. -/
theorem isEtaleAt_of_mono_pullback_snd {E Y W : AlgebraicSpaces B S hS} (F : E ⟶ Y)
    (h : W ⟶ Y) (hflat : IsFlat B S hS F.hom) (hlfp : IsLocallyOfFinitePresentation B S hS F.hom)
    (hsep : IsSeparated B S hS F.hom) (hh : IsImmersion B S hS h.hom)
    (hqc : IsQuasiCompact B S hS h.hom) (hmono : Mono (pullback.snd F.hom h.hom))
    (e : points B S hS E.1)
    (he : pointsMap B S hS _ F.hom e ∈ closure (Set.range (pointsMap B S hS _ h.hom))) :
    IsEtaleAt B S hS F.hom e := by
  classical
  -- the scheme-theoretic image `Z` of `h`, in which `W` is a dense open subspace
  set C := schemeTheoreticImageSubfunctor B S hS h.hom
  have hC : IsClosedSubspace B S hS C :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS h.hom Y.2
  let Z : AlgebraicSpaces B S hS := ⟨C.toFunctor, hC.1⟩
  let ι : Z ⟶ Y := ObjectProperty.homMk C.ι
  set h₀ := toSchemeTheoreticImage B S hS h.hom
  have hh₀ι : h₀ ≫ C.ι = h.hom := toSchemeTheoreticImage_ι B S hS h.hom
  have hW₀ : IsOpenSubspace B S hS (Subfunctor.range h₀) :=
    isOpenSubspace_range_toSchemeTheoreticImage_of_qc_or_reduced B S hS W.2 Y.2 h.hom hh
      (Or.inl hqc)
  have hW₀d : IsSchemeTheoreticallyDense B S hS (Subfunctor.range h₀) :=
    isSchemeTheoreticallyDense_range_toSchemeTheoreticImage_of_qc_or_reduced B S hS W.2 Y.2
      h.hom hh (Or.inl hqc)
  have : Mono h₀ := mono_of_isOpenImmersion B S hS _
    (isOpenImmersion_toSchemeTheoreticImage_of_qc_or_reduced B S hS W.2 Y.2 h.hom hh (Or.inl hqc))
  -- the base change `F_Z : E_Z ⟶ Z`
  let EZ := AlgebraicSpaces.fiberProduct B S hS ι F
  have sq₁ := AlgebraicSpaces.isPullback_fiberProduct B S hS ι F
  set FZ : EZ ⟶ Z := ObjectProperty.homMk (pullback.fst ι.hom F.hom)
  have hEZ : IsAlgebraicSpace B S hS (pullback C.ι F.hom) := EZ.2
  have hFZ := isFlat_and_isLocallyOfFinitePresentation_of_isPullback sq₁.flip
    ⟨hflat, hlfp⟩
  have hFZsep : IsSeparated B S hS (pullback.fst C.ι F.hom) :=
    isSeparated_pullbackFst B S hS C.ι hsep
  -- the square `P = E_Z ×_Z E_Z` and its map to `Z`
  have sq₂ := AlgebraicSpaces.isPullback_fiberProduct B S hS FZ FZ
  set f₀ := pullback.fst C.ι F.hom
  have hP : IsAlgebraicSpace B S hS (pullback f₀ f₀) :=
    isAlgebraicSpace_pullback B S hS f₀ f₀ hEZ hEZ hC.1
  have hp₂ := isFlat_and_isLocallyOfFinitePresentation_of_isPullback sq₂ hFZ
  set q := pullback.snd f₀ f₀ ≫ f₀ with hq
  have hq' := isFlat_and_isLocallyOfFinitePresentation_comp hP hEZ hC.1 hp₂ hFZ
  -- over `W` the two projections of `P` agree
  set D := (Subfunctor.range h₀).preimage q
  have hdense : IsSchemeTheoreticallyDense B S hS D :=
    isSchemeTheoreticallyDense_preimage_of_isFlat B S hS hP hC.1 q hq'.1 hq'.2
      (Subfunctor.range h₀) hW₀ @hW₀d
  have hL : Subfunctor.range (D.ι ≫ q) ≤ Subfunctor.range h₀ := by
    rintro T _ ⟨x, rfl⟩
    exact x.2
  obtain ⟨w, hw⟩ : ∃ w : D.toFunctor ⟶ W.1, D.ι ≫ q = w ≫ h₀ := by
    refine ⟨Subfunctor.lift (D.ι ≫ q) hL ≫ inv (Subfunctor.toRange h₀), ?_⟩
    calc D.ι ≫ q = Subfunctor.lift (D.ι ≫ q) hL ≫ (Subfunctor.range h₀).ι :=
          (Subfunctor.lift_ι _ _).symm
      _ = Subfunctor.lift (D.ι ≫ q) hL ≫ inv (Subfunctor.toRange h₀) ≫
            Subfunctor.toRange h₀ ≫ (Subfunctor.range h₀).ι := by
          rw [IsIso.inv_hom_id_assoc]
      _ = (Subfunctor.lift (D.ι ≫ q) hL ≫ inv (Subfunctor.toRange h₀)) ≫ h₀ := by
          rw [Subfunctor.toRange_ι h₀, Category.assoc]
  have hfst : pullback.fst f₀ f₀ ≫ f₀ = pullback.snd f₀ f₀ ≫ f₀ := pullback.condition
  have hc : ∀ k : D.toFunctor ⟶ pullback C.ι F.hom, k ≫ f₀ = w ≫ h₀ →
      (k ≫ pullback.snd C.ι F.hom) ≫ F.hom = w ≫ h.hom := by
    intro k hk
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hk, Category.assoc, hh₀ι]
  have h1 : (D.ι ≫ pullback.fst f₀ f₀) ≫ f₀ = w ≫ h₀ := by
    rw [Category.assoc, hfst, ← hw, hq]
  have h2 : (D.ι ≫ pullback.snd f₀ f₀) ≫ f₀ = w ≫ h₀ := by
    rw [← hw, hq, Category.assoc]
  have key : (D.ι ≫ pullback.fst f₀ f₀) ≫ pullback.snd C.ι F.hom =
      (D.ι ≫ pullback.snd f₀ f₀) ≫ pullback.snd C.ι F.hom := by
    have hm := hmono.right_cancellation
      (pullback.lift _ w (hc _ h1)) (pullback.lift _ w (hc _ h2))
      (by rw [pullback.lift_snd, pullback.lift_snd])
    simpa only [pullback.lift_fst] using congrArg (fun k => k ≫ pullback.fst F.hom h.hom) hm
  have hsame : D.ι ≫ pullback.fst f₀ f₀ = D.ι ≫ pullback.snd f₀ f₀ :=
    pullback.hom_ext (h1.trans h2.symm) key
  -- so the dense open lies in the diagonal, which is therefore everything
  have hDΔ : D.ι = (D.ι ≫ pullback.fst f₀ f₀) ≫ pullback.diagonal f₀ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hsame]
  have hle : D ≤ Subfunctor.range (pullback.diagonal f₀) := by
    rw [← Subfunctor.range_ι D, hDΔ]
    exact Subfunctor.range_comp_le _ _
  have : Epi (pullback.diagonal f₀) := (Subfunctor.epi_iff_range_eq_top _).2
    (eq_top_of_isSchemeTheoreticallyDense_le hP hdense
      (isClosedSubspace_range_of_isClosedImmersion B S hS _ hEZ hFZsep) hle)
  have : IsIso (pullback.diagonal f₀) := isIso_of_mono_of_epi _
  have hFZunr : IsUnramified B S hS FZ.hom :=
    isUnramified_of_isOpenImmersion_pullbackDiagonal B S hS hEZ hC.1 f₀
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hFZ.2)
      (isOpenImmersion_of_isIso B S hS _)
  -- a point of `E_Z` over `e`
  obtain ⟨z, hz⟩ :=
    closure_range_pointsMap_subset_range_pointsMap_schemeTheoreticImage B S hS h.hom Y.2 he
  have sq₁' := AlgebraicSpaces.isPullback_hom B S hS sq₁
  obtain ⟨e', -, he'⟩ := exists_points_of_isPullback B S hS sq₁' z e hz
  have hunr : IsUnramifiedAt B S hS F.hom e := by
    have := isUnramifiedAt_of_isUnramified_baseChange B S hS E.2 EZ.2 Y.2 Z.2 sq₁'.flip
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hlfp) hFZunr e'
    rwa [he'] at this
  obtain ⟨U, hU, x', hx', hUunr⟩ := hunr
  have hUe := isEtale_ι_of_isOpenSubspace hU
  have hUfl := isFlat_and_isLocallyOfFinitePresentation_comp hU.1 E.2 Y.2
    ⟨isFlat_of_isEtale B S hS hUe, isLocallyOfFinitePresentation_of_isEtale B S hS hUe⟩
    ⟨hflat, hlfp⟩
  exact ⟨U, hU, x', hx', isEtale_of_isFlat_of_isUnramified B S hS hU.1 Y.2 _ hUfl.2 hUfl.1 hUunr⟩

/-- **At a point where a morphism is étale its map of étale local rings is bijective.** If
`f : X ⟶ Y` is étale at the image of a geometric point `x̄` of `X`, the homomorphism
`𝒪_{Y, f(x̄)} ⟶ 𝒪_{X, x̄}` is bijective: on an open neighbourhood `U` of the point on which `f`
is étale, both `U ⟶ X` and `U ⟶ Y` are étale, so both induce bijections of étale local rings,
and the homomorphism of `f` is the quotient of the two. -/
theorem bijective_etaleLocalRingMap_of_isEtaleAt {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (x : GeometricPoint B S hS X.1) (hf : IsEtaleAt B S hS f.hom x.image) :
    Function.Bijective (etaleLocalRingMap X.2 f.hom x) := by
  obtain ⟨U, hU, u, hu, het⟩ := hf
  have hιe := isEtale_ι_of_isOpenSubspace hU
  obtain ⟨ubar, -, rfl⟩ := exists_geometricPoint_lift_of_isQuasiFiniteAt hU.1 X.2 U.ι
    (isLocallyOfFiniteType_of_isEtale B S hS X.2 hιe) x u hu
    (isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS hU.1
      (isLocallyQuasiFinite_of_isEtale B S hS X.2 hιe) u)
  have hb : ∀ {P Q : AlgebraicSpaces B S hS} (φ : P ⟶ Q) (hφ : IsEtale B S hS φ.hom)
      (p : GeometricPoint B S hS P.1), Function.Bijective (etaleLocalRingMap P.2 φ.hom p) := by
    intro P Q φ hφ p
    rw [← eq_etaleLocalRingMap P.2 φ.hom p
      (isEtaleLocalRingMap_etaleLocalRingIsoOfIsEtale_inv B S hS φ hφ p)]
    exact ConcreteCategory.bijective_of_isIso (etaleLocalRingIsoOfIsEtale B S hS φ hφ p).inv
  let Ub : AlgebraicSpaces B S hS := ⟨U.toFunctor, hU.1⟩
  have h₂ : Function.Bijective (etaleLocalRingMap hU.1 (U.ι ≫ f.hom) ubar) :=
    hb (ObjectProperty.homMk (U.ι ≫ f.hom) : Ub ⟶ Y) het ubar
  rw [← etaleLocalRingMap_comp hU.1 X.2 U.ι f.hom ubar] at h₂
  exact (Function.Bijective.of_comp_iff' (hb (ObjectProperty.homMk U.ι : Ub ⟶ X) hιe ubar) _).mp h₂

end AlgebraicGeometry.Space
