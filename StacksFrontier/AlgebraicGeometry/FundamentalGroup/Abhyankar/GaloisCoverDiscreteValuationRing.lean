module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularComplementFacts
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendUnramifiedRegularBoundary
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberCartier
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameCovers.DiscreteValuationRingPoints
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchLocallyIrreducible
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.RegularDivisorExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.BaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverTorsor
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOneIso
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.GaloisCoverTame
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# Extending a Galois cover of the generic fibre over a discrete valuation ring

Let `R` be a discrete valuation ring and `f : X ⟶ Spec R` smooth with geometrically connected
fibres and a section `σ`. A finite étale Galois cover of the generic fibre `X_η` with group of
order invertible in `R`, having a `κ(η)`-point over `σ(η)`, extends to a finite étale Galois
cover of `X`. This is the first paragraph of the proof of [Stacks, Tag 0EYJ].

## Main results

* `Abhyankar.exists_finiteEtaleGaloisCover_extending_genericFiber_of_isDiscreteValuationRing`:
  the statement above, granted purity (`h0BMA`) and the tame half of [Stacks, Tag 0EYD]
  (`h0EYD`), through [Stacks, Tag 0EYG]. Tameness of the generic cover is
  `AlgebraicGeometry.isTamelyRamifiedInCodimensionOne_of_finiteEtaleGaloisCover` and the Galois
  structure is extended by `AlgebraicGeometry.exists_finiteEtaleGaloisCover_of_fullyFaithful`.
* `AlgebraicGeometry.Abhyankar.exists_isPullback_finiteEtale_of_genericFiber`: the underlying
  finite étale extension.
* `AlgebraicGeometry.Abhyankar.isEffectiveCartierDivisor_closedFibre`,
  `AlgebraicGeometry.Abhyankar.isRegularLocalRing_stalk_closedFibre`: the closed fibre `X_s` is
  a regular effective Cartier divisor; `AlgebraicGeometry.Abhyankar.genericFiberIsoCompl`: its
  complement is `X_η`.
* `AlgebraicGeometry.Abhyankar.irreducibleSpace_of_smooth_of_connectedSpace`: a connected scheme
  smooth over a field is irreducible;
  `AlgebraicGeometry.Abhyankar.isIrreducible_preimage_of_smooth`: so are the fibres of a smooth
  morphism with geometrically connected fibres.

## Implementation notes

The source extends `Z` by [Stacks, Tag 0EYH], shows the extension is étale near `σ(s)` by
[Stacks, Tag 0EYI], and concludes with [Stacks, Tag 0EYE]. Here the normalization `Y'` of `X` in
`Z` is finite étale over `X_η` and over the neighbourhood `V` of `σ(s)` given by Tag 0EYI. Since
`X_s` is irreducible, every codimension-one point of `X` lies in `X_η ∪ V`, so [Stacks, Tag 0H2W]
applies with no ramification condition left to check; this replaces the passage through 0EYE.

## References

* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe v u

namespace AlgebraicGeometry.Abhyankar

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The closed fibre `X_s ⊆ X` of a flat scheme over a discrete valuation ring is an effective
Cartier divisor. -/
theorem isEffectiveCartierDivisor_closedFibre [Flat f] :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))))).ker :=
  Stacks.Models.isEffectiveCartierDivisor_specialFiber AlgEquiv.refl f

/-- `Spec κ ⟶ Spec R` for the residue field `κ` of `R` is a closed immersion. -/
private instance isClosedImmersion_specMap_algebraMap_residueField :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- A point of `Spec R` is the generic point iff it is not the closed point. -/
private lemma eq_genericPoint_iff_ne_closedPoint (y : Spec (.of R)) :
    y = genericPoint (Spec (.of R)) ↔ y ≠ closedPoint R := by
  rw [genericPoint_eq_bot_of_affine (.of R)]
  have hm : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  constructor
  · exact fun h h' ↦ hm (congrArg PrimeSpectrum.asIdeal (h.symm.trans h')).symm
  · refine fun h ↦ PrimeSpectrum.ext (not_not.mp fun hne ↦ h (PrimeSpectrum.ext ?_))
    exact IsLocalRing.eq_maximalIdeal ((y).isPrime.isMaximal hne)

/-- The closed fibre of a smooth scheme over a discrete valuation ring is regular. -/
theorem isRegularLocalRing_stalk_closedFibre [Smooth f]
    (z : (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap R (ResidueField R))))).ker.subscheme) :
    IsRegularLocalRing ((pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap R (ResidueField R))))).ker.subscheme.presheaf.stalk z) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))
  let i := pullback.fst f g
  let e : pullback f g ≅ i.image := asIso i.toImage
  have hreg : IsRegular (pullback f g) := isRegular_of_smooth_over_field (pullback.snd f g)
  have h := ((isRegular_iff_regular_stalks _).mp hreg).2 (e.inv z)
  have h' := (isRegularLocalRing_stalk_iff_of_isOpenImmersion e.hom (e.inv z)).mp h
  have hz : e.hom (e.inv z) = z := by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  rwa [hz] at h'

/-- The closed point of `Spec R` is the image of `Spec κ ⟶ Spec R`. -/
private lemma range_SpecMap_algebraMap_residueField :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))) =
      {closedPoint R} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact IsLocalRing.PrimeSpectrum.comap_residue R z
  · rintro rfl
    exact ⟨closedPoint _, IsLocalRing.PrimeSpectrum.comap_residue R _⟩

/-- The support of the closed fibre is `f⁻¹(s)`. -/
lemma coe_support_closedFibre :
    ((pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap R (ResidueField R))))).ker.support : Set X) = f ⁻¹' {closedPoint R} := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))
  rw [Scheme.Hom.support_ker, (pullback.fst f g).isClosedEmbedding.isClosed_range.closure_eq,
    Scheme.Pullback.range_fst, range_SpecMap_algebraMap_residueField]

/-- The complement of the closed fibre is the generic fibre. -/
theorem range_fiberι_genericPoint :
    Set.range (f.fiberι (genericPoint (Spec (.of R)))) =
      Set.range (Scheme.Opens.ι ((pullback.fst f (Spec.map (CommRingCat.ofHom
        (algebraMap R (ResidueField R))))).ker.support.compl : X.Opens)) := by
  rw [Scheme.Hom.range_fiberι, Scheme.Opens.range_ι]
  ext x
  show f x = _ ↔ x ∉ ((pullback.fst f (Spec.map (CommRingCat.ofHom
    (algebraMap R (ResidueField R))))).ker.support : Set X)
  rw [coe_support_closedFibre]
  exact eq_genericPoint_iff_ne_closedPoint (f x)

/-- The generic fibre `X_η` is the complement `X ∖ X_s` of the closed fibre. -/
def genericFiberIsoCompl :
    f.fiber (genericPoint (Spec (.of R))) ≅
      ((pullback.fst f (Spec.map (CommRingCat.ofHom
        (algebraMap R (ResidueField R))))).ker.support.compl : X.Opens) :=
  haveI := Stacks.Chow.isOpenImmersion_fiberι_genericPoint f
  IsOpenImmersion.isoOfRangeEq _ _ (range_fiberι_genericPoint f)

/-- The identification `X_η ≅ X ∖ X_s` is compatible with the inclusions into `X`. -/
@[reassoc (attr := simp)]
lemma genericFiberIsoCompl_hom_ι :
    (genericFiberIsoCompl f).hom ≫ Scheme.Opens.ι _ = f.fiberι (genericPoint (Spec (.of R))) :=
  have := Stacks.Chow.isOpenImmersion_fiberι_genericPoint f
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The closed point of `Spec R` is cut out by the kernel of `Spec κ ⟶ Spec R`. -/
lemma ker_SpecMap_residue_eq_vanishingIdeal :
    (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))).ker =
      Scheme.IdealSheafData.vanishingIdeal ⟨({closedPoint R} : Set (Spec (.of R))),
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (maximalIdeal.isMaximal R)⟩ := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))
  refine Scheme.IdealSheafData.eq_of_isReduced_subscheme_of_support_eq _ _ ?_ inferInstance ?_
  · exact isReduced_of_isOpenImmersion (inv g.toImage)
  · apply SetLike.coe_injective
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Hom.support_ker,
      g.isClosedEmbedding.isClosed_range.closure_eq, range_SpecMap_algebraMap_residueField]
    rfl

/-- A section of `X ⟶ Spec R` meets the closed fibre exactly in the closed point. -/
theorem comap_closedFibre_section [Flat f] (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))))).ker.comap σ =
      Scheme.IdealSheafData.vanishingIdeal ⟨({closedPoint R} : Set (Spec (.of R))),
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (maximalIdeal.isMaximal R)⟩ := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))
  let i := pullback.fst f g
  let t : Spec (.of (ResidueField R)) ⟶ pullback f g :=
    pullback.lift (g ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hP : IsPullback t g i σ := by
    have hs : IsPullback (t ≫ pullback.snd f g) g g (σ ≫ f) := by
      rw [pullback.lift_snd, hσ]
      exact IsPullback.id_horiz g
    exact IsPullback.of_right hs (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f g).flip
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i σ,
    ← ker_SpecMap_residue_eq_vanishingIdeal]
  have he : pullback.fst σ i = hP.flip.isoPullback.inv ≫ g := by
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_fst]
  rw [he, Scheme.Hom.ker_comp_of_isIso]

/-- The complement of the closed fibre of a flat scheme of finite type over a discrete valuation
ring is dense. -/
private lemma dense_compl_support_closedFibre [Flat f] [LocallyOfFiniteType f] :
    Dense ((((pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap R (ResidueField R))))).ker.support.compl : X.Opens)) : Set X) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  dense_of_isSchemeTheoreticallyDense _
    (Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor _
      (isEffectiveCartierDivisor_closedFibre f))

/-- A smooth scheme over a discrete valuation ring has regular local stalks. -/
private lemma isRegularLocalRing_stalk_of_smooth [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  ((isRegular_iff_regular_stalks X).mp (isRegular_of_smooth_over_regular f)).2 x

/-- **A connected scheme smooth over a field is irreducible**: every point has an irreducible open
neighbourhood, namely an integral piece of the decomposition of a normal Noetherian affine open
neighbourhood into integral schemes. -/
theorem irreducibleSpace_of_smooth_of_connectedSpace {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [Smooth g] [ConnectedSpace Y] : IrreducibleSpace Y := by
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  refine Topology.irreducibleSpace_of_connectedSpace_of_forall_exists_isIrreducible fun z ↦ ?_
  obtain ⟨V, hzV⟩ : ∃ V : Y.affineOpens, z ∈ V.1 := by
    rw [← TopologicalSpace.Opens.mem_iSup, iSup_affineOpens_eq_top]
    trivial
  have : IsAffine V.1.toScheme := V.2
  have : IsNoetherian V.1.toScheme := ⟨⟩
  have : IsNormal V.1.toScheme := isNormal_of_smooth (V.1.ι ≫ g)
  obtain ⟨ι, _, W, _, hint, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_finite_coproduct_integral_normal V.1.toScheme).mp inferInstance
  obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk W).surjective (e.hom ⟨z, hzV⟩)
  rw [sigmaMk_mk] at hw
  let j : W i ⟶ Y := Sigma.ι W i ≫ e.inv ≫ V.1.ι
  have := hint i
  refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, ⟨w, ?_⟩, ?_⟩
  · show V.1.ι (e.inv (Sigma.ι W i w)) = z
    rw [hw]
    show (e.hom ≫ e.inv ≫ V.1.ι) ⟨z, hzV⟩ = z
    rw [e.hom_inv_id_assoc]
    rfl
  · rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ (W i)).image j j.continuous.continuousOn).2

/-- The fibres of a smooth morphism with geometrically connected fibres are irreducible. -/
theorem isIrreducible_preimage_of_smooth {Y T : Scheme.{u}} (g : Y ⟶ T) [Smooth g]
    [GeometricallyConnected g] (t : T) : IsIrreducible (g ⁻¹' {t}) := by
  have hsm : Smooth (g.fiberToSpecResidueField t) := inferInstanceAs (Smooth (pullback.snd _ _))
  have := irreducibleSpace_of_smooth_of_connectedSpace (k := T.residueField t)
    (g.fiberToSpecResidueField t)
  have h := (IrreducibleSpace.isIrreducible_univ (g.fiber t)).image
    (g.fiberι t) (Scheme.Hom.continuous _).continuousOn
  rw [Set.image_univ] at h
  convert h using 1
  exact (Scheme.Hom.range_fiberι g _).symm

/-- **Every boundary prime divisor is the generic point of the closed fibre.** If `f` is smooth
with geometrically connected fibres, every prime divisor of `X` whose generic point lies in the
closed fibre has its generic point in every open meeting the closed fibre. -/
theorem genericPoint_mem_of_mem_closedFibre [Smooth f] [GeometricallyConnected f] (V : X.Opens)
    (hV : ∃ x ∈ V, f x = closedPoint R)
    (Z : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor X)
    (hZ : f Z.genericPoint = closedPoint R) : Z.genericPoint ∈ V := by
  have hirr := isIrreducible_preimage_of_smooth f (closedPoint R : Spec (.of R))
  have hcl : IsClosed (f ⁻¹' {closedPoint R}) :=
    (isClosed_singleton_closedPoint R).preimage f.continuous
  obtain ⟨ξs, hξs⟩ := QuasiSober.sober hirr hcl
  obtain ⟨x, hxV, hx⟩ := hV
  have hξsV : ξs ∈ V := (hξs.mem_open_set_iff V.isOpen).mpr ⟨x, hx, hxV⟩
  have hξsf : f ξs = closedPoint R := hξs.mem
  let ξ := Z.genericPoint
  have hspec : ξs ⤳ ξ := hξs.specializes hZ
  by_contra hξV
  have hne : ξ ≠ ξs := fun h ↦ hξV (by rw [show Z.genericPoint = ξs from h]; exact hξsV)
  -- a generization of `ξs` in the generic fibre
  have hη : genericPoint (Spec (.of R)) ⤳ f ξs := by
    rw [hξsf]
    exact genericPoint_specializes _
  obtain ⟨x', hx'ξs, hx'⟩ := (Flat.generalizingMap f) hη
  have hne' : x' ≠ ξs := fun h ↦
    (eq_genericPoint_iff_ne_closedPoint _).mp hx' (h ▸ hξsf)
  have hlt1 : ξ < ξs := lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr hspec,
    fun h ↦ hne (hspec.antisymm (Scheme.le_iff_specializes.mp h)).eq.symm⟩
  have hlt2 : ξs < x' := lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr hx'ξs,
    fun h ↦ hne' (hx'ξs.antisymm (Scheme.le_iff_specializes.mp h)).eq⟩
  have hco : Order.coheight ξ = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint
      (⟨Z.idealSheaf, Z.integral, Z.codimension_one⟩ : AlgebraicGeometry.PrimeDivisor X)
  have h1 : Order.coheight ξs + 1 ≤ Order.coheight ξ := Order.coheight_add_one_le hlt1
  have h2 : Order.coheight x' + 1 ≤ Order.coheight ξs := Order.coheight_add_one_le hlt2
  have h3 : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight x' + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight ξs + 1 := by gcongr
      _ ≤ 1 := h1.trans hco.le
  exact absurd h3 (by norm_num)

/-- A property local on the target holds over `U ⊔ V` once it holds over `U` and over `V`. -/
lemma morphismRestrict_sup (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {N Y : Scheme.{u}} (ν : N ⟶ Y) (U V : Y.Opens) (hU : P (ν ∣_ U)) (hV : P (ν ∣_ V)) :
    P (ν ∣_ (U ⊔ V)) := by
  have himage (W : Y.Opens) (hW : W ≤ U ⊔ V) : (U ⊔ V).ι ''ᵁ ((U ⊔ V).ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hW
  have hres (W : Y.Opens) (hW : W ≤ U ⊔ V) (h : P (ν ∣_ W)) :
      P (ν ∣_ (U ⊔ V).ι ''ᵁ ((U ⊔ V).ι ⁻¹ᵁ W)) := by
    rw [P.arrow_mk_iso_iff (morphismRestrictEq ν (himage W hW))]
    exact h
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun b : Bool ↦ (U ⊔ V).ι ⁻¹ᵁ (if b then U else V)) ?_ fun b ↦ ?_
  · apply (U ⊔ V).ι.image_injective
    dsimp only
    rw [Scheme.Hom.image_iSup, Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
    apply le_antisymm
    · exact iSup_le fun b ↦ by cases b <;> simp [himage]
    · refine sup_le ?_ ?_
      · exact (himage U le_sup_left).symm.le.trans (le_iSup (fun b : Bool ↦ (U ⊔ V).ι ''ᵁ
          ((U ⊔ V).ι ⁻¹ᵁ (if b then U else V))) true)
      · exact (himage V le_sup_right).symm.le.trans (le_iSup (fun b : Bool ↦ (U ⊔ V).ι ''ᵁ
          ((U ⊔ V).ι ⁻¹ᵁ (if b then U else V))) false)
  · rw [P.arrow_mk_iso_iff (morphismRestrictRestrict ν (U ⊔ V) _)]
    cases b
    · exact hres V le_sup_right hV
    · exact hres U le_sup_left hU

/-- A natural number invertible in every residue field of the target is invertible in every
residue field of the source. -/
lemma isUnit_natCast_residueField_of_hom {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (h : ∀ s : S, IsUnit (n : S.residueField s)) (x : X) : IsUnit (n : X.residueField x) := by
  have := (h (f x)).map (f.residueFieldMap x).hom
  rwa [map_natCast] at this

open Stacks.FundamentalGroup in
/-- **Galois covers with group of order invertible are tame**, transported to a cover of an open
`U ⊆ X` presented through an isomorphism `T ≅ U`. -/
theorem isTamelyRamifiedInCodimensionOne_of_galoisCover
    {X T : Scheme.{u}} (U : X.Opens) (e : T ≅ U) (G : Type v) [Group G] [Finite G]
    (hG : ∀ x : X, IsUnit (Nat.card G : X.residueField x)) (Z : FiniteEtaleGaloisCover T G) :
    IsTamelyRamifiedInCodimensionOne U.ι (Z.obj.hom ≫ e.hom) := by
  have : IsIso (pullback.fst Z.obj.hom e.inv) := inferInstance
  have : ConnectedSpace ((𝟭 Scheme).obj Z.obj.left) := Z.connected
  have hconn : ConnectedSpace ((finiteEtaleBaseChange e.inv).obj Z.obj).left :=
    (asIso (pullback.fst Z.obj.hom e.inv)).hom.homeomorph.symm.surjective.connectedSpace
      (asIso (pullback.fst Z.obj.hom e.inv)).hom.homeomorph.symm.continuous
  refine IsTamelyRamifiedInCodimensionOne.of_iso (Iso.refl _) (asIso (pullback.fst Z.obj.hom e.inv))
    (Category.id_comp _) ?_
    (isTamelyRamifiedInCodimensionOne_of_finiteEtaleGaloisCover U G hG (Z.baseChange e.inv hconn))
  show pullback.fst Z.obj.hom e.inv ≫ Z.obj.hom ≫ e.hom = pullback.snd Z.obj.hom e.inv ≫ 𝟙 _
  rw [reassoc_of% pullback.condition, Iso.inv_hom_id, Category.comp_id]

/-- `Spec K ⟶ Spec R` for the fraction field `K` factors through `Spec κ(η)`. -/
lemma exists_SpecMap_fractionRing_eq :
    ∃ t : Spec (.of (FractionRing R)) ⟶
        Spec ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))),
      t ≫ (Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have h : genericPoint (Spec (.of R)) = g (closedPoint (FractionRing R)) := by
    rw [genericPoint_eq_bot_of_affine (.of R)]
    apply PrimeSpectrum.ext
    show ⊥ = Ideal.comap (algebraMap R (FractionRing R)) (closedPoint (FractionRing R)).asIdeal
    rw [show (closedPoint (FractionRing R)).asIdeal = ⊥ from
      (IsLocalRing.maximalIdeal_eq_bot : maximalIdeal (FractionRing R) = ⊥)]
    exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))).symm
  refine ⟨Spec.map ((Spec (.of R)).descResidueField (Scheme.stalkClosedPointTo g)) ≫
    Spec.map ((Spec (.of R)).residueFieldCongr h).hom, ?_⟩
  rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]

/-- **The fibre of the generic Galois cover at `σ(η)` splits completely**: for `K` the fraction
field of `R`, the base change of `Z ⟶ X` along `σ ∘ (Spec K ⟶ Spec R)` is a disjoint union of
copies of `Spec K` over `Spec K`. -/
theorem exists_iso_sigma_genericFiber (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    {G : Type v} [Group G] [Finite G]
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint (Spec (.of R)))) G)
    (z : Spec ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ) :
    ∃ (J : Type u) (eJ : pullback (Spec.map (CommRingCat.ofHom
        (algebraMap R (FractionRing R))) ≫ σ)
        ((Z.obj.hom ≫ (genericFiberIsoCompl f).hom) ≫ Scheme.Opens.ι _) ≅
          ∐ fun _ : J ↦ Spec (.of (FractionRing R))),
      eJ.hom ≫ Limits.Sigma.desc (fun _ ↦ 𝟙 _) = pullback.fst _ _ := by
  obtain ⟨t, ht⟩ := exists_SpecMap_fractionRing_eq (R := R)
  let s := t ≫ z
  have hs : s ≫ Z.obj.hom ≫ f.fiberι (genericPoint (Spec (.of R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ σ := by
    simp only [s, Category.assoc]
    rw [reassoc_of% hz, genericFiberSection_fiberι, ← Category.assoc, ht]
  have := Stacks.Chow.isOpenImmersion_fiberι_genericPoint f
  obtain ⟨J, eJ, heJ⟩ := exists_iso_sigma_of_lift Z.obj.hom
    (((MorphismProperty.Over.forget _ ⊤ _).mapAut Z.obj).comp Z.action) s
    (f.fiberι (genericPoint (Spec (.of R)))) _ hs
  have hc : (Z.obj.hom ≫ (genericFiberIsoCompl f).hom) ≫ Scheme.Opens.ι _ =
      Z.obj.hom ≫ f.fiberι (genericPoint (Spec (.of R))) := by
    rw [Category.assoc, genericFiberIsoCompl_hom_ι]
  refine ⟨J, pullback.congrHom rfl hc ≪≫ eJ, ?_⟩
  refine (Category.assoc _ _ _).trans ?_
  rw [heJ]
  simp only [pullback.congrHom, pullback.map, asIso_hom, pullback.lift_fst, Category.comp_id]

open Stacks.FundamentalGroup in
/-- **The generic Galois cover extends to a finite étale cover** (first paragraph of the proof of
[Stacks, Tag 0EYJ], up to the Galois structure). Over a discrete valuation ring, the cover
`Z ⟶ X_η = X ∖ X_s` is the restriction of a finite étale `p : Y' ⟶ X`. The arguments are purity
`h0BMA` ([Stacks, Tag 0BMA] (1)) and `h0EYD` (the tame half of [Stacks, Tag 0EYD]), through
Tag 0EYG (via `AlgebraicGeometry.TameCovers.exists_opens_etale_fromNormalization`, i.e.
[Stacks, Tag 0EYI]). -/
theorem exists_isPullback_finiteEtale_of_genericFiber (h0BMA : PurityAtRegularLocalRings.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    [Smooth f] [GeometricallyConnected f] (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    {G : Type v} [Group G] [Finite G]
    (hG : ∀ s : Spec (.of R), IsUnit (Nat.card G : (Spec (.of R)).residueField s))
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint (Spec (.of R)))) G)
    (z : Spec ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ) :
    ∃ (Y' : Scheme.{u}) (p : Y' ⟶ X) (_ : IsFinite p) (_ : Etale p) (a : Z.obj.left ⟶ Y'),
      IsPullback (Z.obj.hom ≫ (genericFiberIsoCompl f).hom) a (Scheme.Opens.ι _) p := by
  let g0 := Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))
  let D := (pullback.fst f g0).ker
  let U : X.Opens := D.support.compl
  let fc : Z.obj.left ⟶ U := Z.obj.hom ≫ (genericFiberIsoCompl f).hom
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsFinite Z.obj.hom := Z.obj.prop.1
  have : Etale Z.obj.hom := Z.obj.prop.2
  have hD := isEffectiveCartierDivisor_closedFibre f
  have hDreg := isRegularLocalRing_stalk_closedFibre f
  have htame : IsTamelyRamifiedInCodimensionOne U.ι fc :=
    isTamelyRamifiedInCodimensionOne_of_galoisCover U (genericFiberIsoCompl f) G
      (isUnit_natCast_residueField_of_hom f _ hG) Z
  obtain ⟨J, eJ, heJ⟩ := exists_iso_sigma_genericFiber f σ hσ Z z hz
  obtain ⟨V, hσV, hVfin, hVet⟩ :=
    TameCovers.exists_opens_etale_fromNormalization h0BMA h0EYD D hD hDreg fc htame R
      (FractionRing R) σ (comap_closedFibre_section f σ hσ) J eJ heJ
  let ν := (fc ≫ U.ι).fromNormalization
  have hpbU := TameCovers.isPullback_toNormalization_ι D fc
  let j : Z.obj.left ≅ (ν ⁻¹ᵁ U).toScheme := hpbU.isoPullback ≪≫ pullbackRestrictIsoRestrict ν U
  have hj : j.hom ≫ ν ∣_ U = fc := by
    simp only [j, Iso.trans_hom, Category.assoc, pullbackRestrictIsoRestrict_hom_morphismRestrict]
    exact hpbU.isoPullback_hom_snd
  have eArr : Arrow.mk (ν ∣_ U) ≅ Arrow.mk fc :=
    Arrow.isoMk j.symm (Iso.refl _) (by simp [← hj])
  let hlf : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  let hle : IsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  have hUfin : IsFinite (ν ∣_ U) :=
    (@MorphismProperty.arrow_mk_iso_iff _ _ @IsFinite hlf.1 _ _ _ _ _ _ eArr).mpr inferInstance
  have hUet : Etale (ν ∣_ U) :=
    (@MorphismProperty.arrow_mk_iso_iff _ _ @Etale hle.1 _ _ _ _ _ _ eArr).mpr inferInstance
  let W : X.Opens := U ⊔ V
  have hWfin : IsFinite (ν ∣_ W) := morphismRestrict_sup @IsFinite ν U V hUfin hVfin
  have hWet : Etale (ν ∣_ W) := morphismRestrict_sup @Etale ν U V hUet hVet
  have hUdense : Dense (U : Set X) := dense_compl_support_closedFibre f
  have hdense : DenseRange W.ι.base := by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact hUdense.mono (le_sup_left : U ≤ W)
  have hsupp : (D.support : Set X) = f ⁻¹' {closedPoint R} := coe_support_closedFibre f
  have hunr : IsUnramifiedInCodimensionOne W.ι (ν ∣_ W) := by
    intro Zd hZd
    exfalso
    apply hZd
    rw [Scheme.Opens.range_ι]
    by_cases hU : Zd.genericPoint ∈ U
    · exact Or.inl hU
    · right
      have hfx : f Zd.genericPoint = closedPoint R := by
        have : Zd.genericPoint ∈ (D.support : Set X) := not_not.mp hU
        rwa [hsupp] at this
      refine genericPoint_mem_of_mem_closedFibre f V ⟨σ (closedPoint R), hσV _, ?_⟩ Zd hfx
      show (σ ≫ f) (closedPoint R) = _
      rw [hσ]
      rfl
  obtain ⟨Y', p, hpfin, hpet, e, he⟩ :=
    exists_finiteEtale_extension_of_isUnramifiedInCodimensionOne W hdense (ν ∣_ W) hunr fun x _ ↦
      isRegularLocalRing_stalk_of_smooth f x
  -- the two squares over `U ⊆ W ⊆ X`
  have hUW : U ≤ W := le_sup_left
  have hpre : ν ⁻¹ᵁ U ≤ ν ⁻¹ᵁ W := fun x hx ↦ hUW hx
  let i : (ν ⁻¹ᵁ U).toScheme ⟶ (ν ⁻¹ᵁ W).toScheme := Scheme.homOfLE _ hpre
  have hS2 : IsPullback (ν ∣_ U) i (X.homOfLE hUW) (ν ∣_ W) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_morphismRestrict ν W)
    · rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
      exact isPullback_morphismRestrict ν U
    · rw [← cancel_mono W.ι, Category.assoc (ν ∣_ U), Scheme.homOfLE_ι, morphismRestrict_ι,
        Category.assoc i, morphismRestrict_ι, ← Category.assoc i, Scheme.homOfLE_ι]
  have hS1 : IsPullback (ν ∣_ W) (e.inv ≫ pullback.fst p W.ι) W.ι p := by
    refine (IsPullback.of_hasPullback p W.ι).flip.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, he]
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · simp
    · simp
  have hS := hS2.paste_vert hS1
  rw [Scheme.homOfLE_ι] at hS
  refine ⟨Y', p, hpfin, hpet, j.hom ≫ i ≫ e.inv ≫ pullback.fst p W.ι, ?_⟩
  refine hS.of_iso j.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp]
    exact hj
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc]
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **Restriction to the generic fibre is fully faithful** for a smooth scheme over a discrete
valuation ring: `X` is regular and `X_η` is dense. -/
theorem nonempty_fullyFaithful_finiteEtaleBaseChange_fiberι [Smooth f] :
    Nonempty (finiteEtaleBaseChange (f.fiberι (genericPoint (Spec (.of R))))).FullyFaithful := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hU⟩ := fullyFaithful_finiteEtaleBaseChange_of_isRegularLocalRing _
    (dense_compl_support_closedFibre f) fun x _ ↦ isRegularLocalRing_stalk_of_smooth f x
  let e := genericFiberIsoCompl f
  have : (finiteEtaleBaseChange e.hom).IsEquivalence :=
    (CategoryTheory.Equivalence.mk (finiteEtaleBaseChange e.hom) (finiteEtaleBaseChange e.inv)
      (finiteEtaleBaseChangeId.symm ≪≫
        finiteEtaleBaseChangeComp e.inv e.hom (𝟙 _) e.inv_hom_id.symm)
      ((finiteEtaleBaseChangeComp e.hom e.inv (𝟙 _) e.hom_inv_id.symm).symm ≪≫
        finiteEtaleBaseChangeId)).isEquivalence_functor
  exact ⟨(hU.comp (Functor.FullyFaithful.ofFullyFaithful (finiteEtaleBaseChange e.hom))).ofIso
    (finiteEtaleBaseChangeComp e.hom (Scheme.Opens.ι _) _ (genericFiberIsoCompl_hom_ι f).symm).symm⟩

omit [IsDiscreteValuationRing R] in
/-- **A flat scheme over `Spec R` with connected generic fibre is connected**: every point
generizes into the generic fibre, which is therefore dense. -/
theorem connectedSpace_of_isPullback_fiberι {Y W : Scheme.{u}} (p : Y ⟶ X) [Flat p] [Flat f]
    (h : W ⟶ f.fiber (genericPoint (Spec (.of R)))) (a : W ⟶ Y)
    (H : IsPullback h a (f.fiberι (genericPoint (Spec (.of R)))) p) [ConnectedSpace W] :
    ConnectedSpace Y := by
  have hrange : Set.range a = (p ≫ f) ⁻¹' {genericPoint (Spec (.of R))} := by
    have hs : Function.Surjective H.flip.isoPullback.hom := fun y ↦
      ⟨H.flip.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
    have h1 : Set.range a = p ⁻¹' Set.range (f.fiberι (genericPoint (Spec (.of R)))) := by
      rw [← H.flip.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        hs.range_eq, Set.image_univ, Scheme.Pullback.range_fst]
    rw [h1, Scheme.Hom.range_fiberι]
    rfl
  have hdense : Dense (Set.range a) := by
    intro y
    have hη : genericPoint (Spec (.of R)) ⤳ (p ≫ f) y := genericPoint_specializes _
    obtain ⟨y', hy', hy'η⟩ := (Flat.generalizingMap (p ≫ f)) hη
    exact hy'.mem_closed isClosed_closure (subset_closure (hrange ▸ hy'η))
  have hconn : _root_.IsConnected (Set.range a) := isConnected_range a.continuous
  have := hconn.closure
  rw [hdense.closure_eq] at this
  exact connectedSpace_iff_univ.mpr this

open Stacks.FundamentalGroup in
/-- **Stacks Project, Tag 0EYJ, over a discrete valuation ring** (the first paragraph of the
proof), granted purity `h0BMA` ([Stacks, Tag 0BMA] (1)) and `h0EYD` (the tame half of
[Stacks, Tag 0EYD]), through Tag 0EYG. Let `R` be a discrete valuation ring, `f : X ⟶ Spec R`
smooth with geometrically connected fibres and a section `σ`, and `Z ⟶ X_η` a finite étale Galois
cover with group `G` of order invertible on `Spec R` having a `κ(η)`-point over `σ(η)`. Then `Z`
extends to a finite étale Galois cover of `X` with group `G`. -/
theorem exists_finiteEtaleGaloisCover_extending_genericFiber_of_isDiscreteValuationRing
    (h0BMA : PurityAtRegularLocalRings.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    [Smooth f] [GeometricallyConnected f] (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (G : Type v) [Group G] [Finite G]
    (hG : ∀ s : Spec (.of R), IsUnit (Nat.card G : (Spec (.of R)).residueField s))
    (Z : FiniteEtaleGaloisCover (f.fiber (genericPoint (Spec (.of R)))) G)
    (z : Spec ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom = genericFiberSection f σ hσ) :
    ∃ (Y : FiniteEtaleGaloisCover X G)
      (e : (finiteEtaleBaseChange (f.fiberι (genericPoint (Spec (.of R))))).obj Y.obj ≅ Z.obj),
      ∀ g : Gᵐᵒᵖ, (finiteEtaleBaseChange (f.fiberι (genericPoint (Spec (.of R))))).map
        (Y.action g).hom ≫ e.hom = e.hom ≫ (Z.action g).hom := by
  obtain ⟨Y', p, hpf, hpe, a, H⟩ :=
    exists_isPullback_finiteEtale_of_genericFiber f h0BMA h0EYD σ hσ hG Z z hz
  have H' : IsPullback Z.obj.hom a (f.fiberι (genericPoint (Spec (.of R)))) p := by
    refine H.of_iso (Iso.refl _) (genericFiberIsoCompl f).symm (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · rw [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.refl_hom,
        Category.id_comp]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.eq_inv_comp, genericFiberIsoCompl_hom_ι]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  let Yobj : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ p ⟨hpf, hpe⟩
  let e : (finiteEtaleBaseChange (f.fiberι (genericPoint (Spec (.of R))))).obj Yobj ≅ Z.obj :=
    MorphismProperty.Over.isoMk H'.flip.isoPullback.symm H'.flip.isoPullback_inv_snd
  have : ConnectedSpace Z.obj.left := Z.connected
  have := hpe
  have : Flat p := inferInstance
  have hconn' : ConnectedSpace Y' := connectedSpace_of_isPullback_fiberι f p _ a H'
  have hconn : ConnectedSpace Yobj.left := hconn'
  exact exists_finiteEtaleGaloisCover_of_fullyFaithful _
    (nonempty_fullyFaithful_finiteEtaleBaseChange_fiberι f).some G Yobj hconn Z e

end AlgebraicGeometry.Abhyankar
