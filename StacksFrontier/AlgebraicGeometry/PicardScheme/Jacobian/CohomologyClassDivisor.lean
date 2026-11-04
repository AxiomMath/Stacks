module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassTwist
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBaseChangeDegree
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMapDegree
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.LocallyPrincipalFibre
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFlatFamily
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeUnits
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveFibreDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.ProjectiveJacobian

/-!
# The claim in the proof of Stacks 0B9X: invertible direct image gives a unique divisor

Let `X` be a smooth proper geometrically irreducible curve of genus `g` over a field `k`, `T` a
`k`-scheme and `π : X_T ⟶ T` the base change. The proof of [Stacks, Tag 0B9X] rests on the
following claim. If `ℳ` is an invertible `𝒪_{X_T}`-module such that `Rπ_*ℳ` is an invertible
`𝒪_T`-module `𝒩` placed in degree zero, then the section of `ℳ ⊗ π^*𝒩^{⊗ -1}` corresponding to
the adjunction map `π^*𝒩 ⟶ ℳ` has as zero scheme a relative effective Cartier divisor `D`,
finite locally free of degree `g` over `T`. This file proves that claim, as existence of a
degree-`g` Hilbert family of class `[ℳ] - π^*[𝒩]`, together with the uniqueness of such a family
that the source leaves to the reader ("we omit the verification ... defines an inverse").

## The argument

* **The twist.** With `n = -[𝒩]` and `ℒ` the representative of `[ℳ] + π^*n`, the projection
  formula for an invertible module ([Stacks, Tag 01E8]) gives `π_*ℒ ≅ π_*ℳ ⊗ 𝒩^{-1} ≅ 𝒪_T`
  (`AlgebraicGeometry.exists_iso_unit_pushforward_picardRepresentative`). Let `s = e(1)`.
* **The fibres.** Over an affine open `V` of `T` on which `n` is trivial, `ℒ` has no higher
  cohomology on `π⁻¹(V)` (`AlgebraicGeometry.subsingleton_rightDerived_pullback_ι`); so by
  cohomology and base change the restriction of `s` to every fibre is a generator of the
  one-dimensional `H⁰(X_t, ℒ_t)`, and `ℒ_t` has no higher cohomology. In particular `s_t ≠ 0`.
* **The divisor.** The fibres `X_t` are integral, so the zero scheme `D = Z(s)` meets them in
  effective Cartier divisors; being locally principal, `D` is a relative effective Cartier divisor
  ([Stacks, Tag 062Y]), hence finite locally free over `T` since `π` is proper
  ([Stacks, Tag 0B9D]). Its degree at `t` is `deg ℒ_t = χ(ℒ_t) - χ(𝒪_{X_t}) = 1 - (1 - g) = g`.
* **Uniqueness.** A divisor `D'` of class `[ℒ] + π^*m`, containing no fibre, is `Z(s)`: over an
  affine open `V` on which `m` is trivial, `𝒪(D')|_{π⁻¹(V)} ≅ ℒ|_{π⁻¹(V)}`, whose sections are
  free of rank one on `s`; the canonical section of `D'` is `a · s` with `a ∈ Γ(T, V)` nonzero at
  every point, hence a unit, and multiplying by a unit does not change the zero scheme.

Neither half uses the two halves of [Stacks, Tag 0B91]: the base change needed is in degree zero
along the fibres, with the canonical map, and it comes from the vanishing of higher cohomology over
affine opens through the Čech complex
(`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.cohomologyBaseChange_of_vanishing`).

## Main results

* `Stacks.RigidifiedPicard.exists_hilbertFamily_abelClass_eq` — existence.
* `Stacks.RigidifiedPicard.eq_of_abelClass_eq` — uniqueness.
* `Stacks.WeilCohomology.cohomologyLocusDivisorExistence` and
  `Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness` — the two propositions
  `Stacks.WeilCohomology.CohomologyLocusDivisorExistence` and
  `Stacks.WeilCohomology.CohomologyLocusDivisorUniqueness`, for every field.

No Stacks tag is attached: the claim is part of the proof of [Stacks, Tag 0B9X], not a tag.

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

attribute [local instance 10000] HasDerivedCategory.standard




namespace AlgebraicGeometry

variable {Y T : Scheme.{u}} (π : Y ⟶ T)

/-- Invertibility in the sense of Stacks, transported to the `AlgebraicGeometry` notion. -/
private theorem isInvertible_sheaf_of_stacks {Z : Scheme.{u}} {L : Z.Modules}
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L) :
    SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp hL

/-- The base change of a smooth morphism of relative dimension one is again one. -/
private theorem smoothOfRelativeDimension_one_pullback_snd {X Z W : Scheme.{u}} (f : X ⟶ Z)
    (g : W ⟶ Z) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 (pullback.snd f g) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback f g) inferInstance

/-- **Rank of a finite locally free closed subscheme, read on the fibres.** -/
theorem isFiniteLocallyFreeOfRank_of_fiber (D : Y.IdealSheafData)
    [hD : Stacks.Morphisms.IsFiniteLocallyFree (D.subschemeι ≫ π)] (t : T) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((D.comap (π.fiberι t)).subschemeι ≫ π.fiberToSpecResidueField t)
      ((D.subschemeι ≫ π).finrank t) := by
  obtain ⟨hfin, hflat, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).1 hD
  obtain ⟨a, ha⟩ := exists_isPullback_subschemeι_baseChange
    (IsPullback.of_hasPullback π (T.fromSpecResidueField t)) D
  change IsPullback a ((D.comap (π.fiberι t)).subschemeι ≫ π.fiberToSpecResidueField t)
    (D.subschemeι ≫ π) (T.fromSpecResidueField t) at ha
  have : IsFinite ((D.comap (π.fiberι t)).subschemeι ≫ π.fiberToSpecResidueField t) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback ha hfin
  have : Flat ((D.comap (π.fiberι t)).subschemeι ≫ π.fiberToSpecResidueField t) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback ha hflat
  have := hfin
  have := hflat
  refine (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).2 fun y => ?_
  have h := Scheme.Hom.finrank_of_isPullback a _ _ _ ha y
  rwa [Scheme.fromSpecResidueField_apply] at h

/-- **The class of the zero scheme of a regular section is the class of the module.** -/
theorem picardClass_zeroScheme {Z : Scheme.{u}} (L : Z.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L)
    [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] (s : Γ(L, ⊤))
    [Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme Z L s)] :
    Stacks.Divisors.picardClass (Stacks.Divisors.zeroScheme Z L s) =
      Stacks.SheafOfModules.picardClass Z.presheaf
        (Stacks.RingedSpace.structureIsSheaf Z.toRingedSpace) L hL := by
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.Divisors.zeroScheme Z L ((Stacks.Divisors.sectionsOfTop L s).eval (op ⊤))) := by
    rw [Stacks.Divisors.sectionsOfTop_eval_top]
    infer_instance
  have hreg := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Z L _).1 hE
  have hinj := injective_smul_res_of_isRegularSection L _ hreg
  rw [Stacks.Divisors.sectionsOfTop_eval_top] at hinj
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ hL).2
    ⟨(invertibleSheafIsoZeroScheme L s hinj).symm⟩

open Stacks.Picard in
/-- **The core claim of [Stacks, Tag 0B9X], existence.** Let `X` be a smooth proper geometrically
irreducible curve of genus `g` over a field `k`, `T` a `k`-scheme and `c` a Picard class of
`X_T` whose representative `ℳ` has `Rπ_*ℳ` an invertible module placed in degree zero. Then there
is a relative effective Cartier divisor `D ⊂ X_T`, finite locally free of degree `g` over `T`,
whose class is `c + π^*n` for some class `n` of `T`. -/
theorem exists_relativeEffectiveCartierDivisor_picardClass_eq {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIrreducible f] (T : Over (Spec (.of k)))
    (c : ofScheme (pullback f T.hom))
    (hc : HasDerivedPushforwardRank (pullback.snd f T.hom)
      (Stacks.Picard.picardRepresentative _ c).obj 0 1) :
    ∃ (D : (pullback f T.hom).IdealSheafData) (n : ofScheme T.left)
      (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor (pullback.snd f T.hom) D),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ pullback.snd f T.hom) (genus f) ∧
      @Stacks.Divisors.picardClass _ D hD.1 = c + schemePullbackClass (pullback.snd f T.hom) n := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  set π := pullback.snd f T.hom
  have hfp : FinitePresentation π := Stacks.RigidifiedPicard.finitePresentation_bcProj f T
  have : SmoothOfRelativeDimension 1 π := smoothOfRelativeDimension_one_pullback_snd f T.hom
  obtain ⟨n, ⟨e⟩⟩ := exists_iso_unit_pushforward_picardRepresentative π c hc
  set L : (pullback f T.hom).Modules :=
    (Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace
      (c + schemePullbackClass π n)).obj
  have hL : Stacks.SheafOfModules.IsInvertible (pullback f T.hom).presheaf
      (pullback f T.hom).ringCatSheaf.2 L :=
    (Stacks.Picard.picardRepresentative (pullback f T.hom).toRingedSpace
      (c + schemePullbackClass π n)).property
  have hvan : ∀ t : T.left, ∃ V : T.left.Opens, IsAffineOpen V ∧ t ∈ V ∧ ∀ p : ℕ, 0 < p →
      Subsingleton (((AlgebraicGeometry.moduleGlobalSections (π ⁻¹ᵁ V)).rightDerived p).obj
        ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)) := fun t => by
    obtain ⟨V, hV, htV, hn⟩ := exists_isAffineOpen_schemePullbackClass_eq_zero n t
    exact ⟨V, hV, htV, subsingleton_rightDerived_pullback_ι π hfp c hc n hV hn⟩
  set s := Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T.left, ⊤))
  have hL' := isInvertible_sheaf_of_stacks hL
  set D := Stacks.Divisors.zeroScheme (pullback f T.hom) L s
  have hfibD : ∀ t : T.left, Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (π.fiberι t)) :=
    fun t =>
      have := Stacks.RigidifiedPicard.isIntegral_curveFibre f T t
      isEffectiveCartierDivisor_comap_zeroScheme_of_ne_zero (π.fiberι t) L s
        (pullbackGlobalSections_fiberι_ne_zero_of_iso π L hL e hvan t)
  have hRel : Stacks.Divisors.IsRelativeEffectiveCartierDivisor π D :=
    Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres π D
      (isLocallyPrincipal_zeroScheme _ L s) hfibD
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hRel.1
  have hclD : Stacks.Divisors.picardClass D = c + schemePullbackClass π n :=
    (picardClass_zeroScheme L hL s).trans (classOf_picardRepresentative _ _)
  have hflf : Stacks.Morphisms.IsFiniteLocallyFree (D.subschemeι ≫ π) :=
    (isFiniteLocallyFree_iff_isRelativeEffectiveCartierDivisor_of_isProper π D).2 hRel
  obtain ⟨hfin, hflat, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).1 hflf
  refine ⟨D, n, hRel, ?_, hclD⟩
  refine (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).2 fun t => ?_
  have hsm : SmoothOfRelativeDimension 1 (pullback.snd π (T.left.fromSpecResidueField t)) :=
    smoothOfRelativeDimension_one_pullback_snd π _
  have : SmoothOfRelativeDimension 1 (π.fiberToSpecResidueField t) := hsm
  have hdim : topologicalKrullDim (π.fiber t) ≤ 1 :=
    @topologicalKrullDim_le_one_of_smoothOfRelativeDimension _ _ _
      (π.fiberToSpecResidueField t) hsm
  have := hfibD t
  have hr := isFiniteLocallyFreeOfRank_of_fiber π D t
  have hdeg := invertibleCurveDegreeHom_picardClass_of_isFiniteLocallyFreeOfRank
    (T.left.residueField t) (π.fiberToSpecResidueField t) hdim (D.comap (π.fiberι t))
    ((D.subschemeι ≫ π).finrank t)
  have : Stacks.Divisors.IsPullbackDefined (π.fiberι t) D := hfibD t
  have hLt := Stacks.RingedSpace.modulePullback_isInvertible_of (π.fiberι t).toLRSHom.toShHom L hL
  have hclt : Stacks.Divisors.picardClass (D.comap (π.fiberι t)) =
      Stacks.SheafOfModules.picardClass (π.fiber t).presheaf
        (Stacks.RingedSpace.structureIsSheaf (π.fiber t).toRingedSpace)
        ((Scheme.Modules.pullback (π.fiberι t)).obj L) hLt := by
    rw [← Stacks.Divisors.schemePullbackClass_picardClass, hclD,
      ← classOf_picardRepresentative (pullback f T.hom).toRingedSpace
        (c + schemePullbackClass π n)]
    exact pullbackClass_classOf (π.fiberι t).toLRSHom.toShHom L hL
  rw [hclt] at hdeg
  have hdeg' := (invertibleCurveDegreeHom_picardClass (T.left.residueField t)
    (π.fiberToSpecResidueField t) hdim _ hLt).symm.trans hdeg
  let := overResidueFieldAlgebra T t
  obtain ⟨hpos, h0⟩ := cohomologyOverField_fiber_of_iso π L hL e hvan t
  have hg := @invertibleCurveDegree_eq_genus_of_cohomology k _ X f _ _ _
    (T.left.residueField t) _ (overResidueFieldAlgebra T t) _ _
    (π.fiberToSpecResidueField t)
    (isPullback_fiberι_fst f T t (spec_map_algebraMap_overResidueFieldAlgebra T t)) _ hdim
    ((Scheme.Modules.pullback (π.fiberι t)).obj L) hLt h0 hpos
  exact_mod_cast hdeg'.symm.trans hg

end AlgebraicGeometry


namespace AlgebraicGeometry

variable {Y T : Scheme.{u}} (π : Y ⟶ T)

/-- **A section is nonzero on a fibre as soon as its pullback to `π⁻¹(V)`, transported along an
isomorphism, is.** The bookkeeping between the three pullbacks to the fibre. -/
theorem pullbackGlobalSections_fiberιOfMem_ne_zero {V : T.Opens} (t : T) (ht : t ∈ V)
    {M L : Y.Modules} (φ : (Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj M ≅
      (Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L) (σ : Γ(M, ⊤))
    (hσ : pullbackGlobalSections (π.fiberι t) M σ ≠ 0) :
    pullbackGlobalSections (fiberιOfMem π t ht) _
      (Scheme.Modules.Hom.app φ.hom ⊤ (pullbackGlobalSections (π ⁻¹ᵁ V).ι M σ)) ≠ 0 := by
  intro h
  apply hσ
  have h1 := Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
    (fiberιOfMem π t ht) φ.hom (pullbackGlobalSections (π ⁻¹ᵁ V).ι M σ)
  rw [h1] at h
  have h2 : pullbackGlobalSections (fiberιOfMem π t ht) _
      (pullbackGlobalSections (π ⁻¹ᵁ V).ι M σ) = 0 := by
    have := congrArg (Scheme.Modules.Hom.app ((Scheme.Modules.pullback (fiberιOfMem π t ht)).map
      φ.inv) ⊤) h
    rw [map_zero] at this
    refine Eq.trans ?_ this
    exact (congrArg (fun k => Scheme.Modules.Hom.app k ⊤ _)
      ((Scheme.Modules.pullback (fiberιOfMem π t ht)).mapIso φ).hom_inv_id).symm
  rw [← fiberιOfMem_ι π t ht, ← SectionsEqualizer.pullbackGlobalSections_comp, h2, map_zero]

/-- **The linear form attached to `𝒪_T ≅ π_*ℒ` over an affine open**, sending the restriction of
`e(1)` to `1`, is bijective. -/
theorem exists_linearMap_of_iso (L : Y.Modules)
    (e : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ≅ (Scheme.Modules.pushforward π).obj L)
    {V : T.Opens} (hV : IsAffineOpen V) :
    letI := Stacks.Cech.sectionsModule ((π ∣_ V) ≫ hV.isoSpec.hom)
      ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L) ⊤
    ∃ ℓ : Γ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L, ⊤) →ₗ[Γ(T, V)] Γ(T, V),
      ℓ (pullbackGlobalSections (π ⁻¹ᵁ V).ι L (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T, ⊤)))) = 1 ∧
        Function.Bijective ℓ := by
  have hs : (Scheme.Modules.Hom.app e.inv V).hom
      (L.presheaf.map (homOfLE (le_top : π ⁻¹ᵁ V ≤ ⊤)).op
        (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T, ⊤)))) = (1 : Γ(T, V)) := by
    have hnat := PresheafOfModules.naturality_apply e.hom.val (homOfLE (le_top : V ≤ ⊤)).op
      (1 : Γ(T, ⊤))
    show Scheme.Modules.Hom.app e.inv V
      (((Scheme.Modules.pushforward π).obj L).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T, ⊤)))) = (1 : Γ(T, V))
    have h1 : ((Scheme.Modules.pushforward π).obj L).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T, ⊤))) =
        Scheme.Modules.Hom.app e.hom V (T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op 1) :=
      hnat.symm
    rw [h1, map_one]
    exact congr(Scheme.Modules.Hom.app $(Iso.hom_inv_id e) V (1 : Γ(T, V)))
  obtain ⟨ℓ, hℓ, hb⟩ := exists_linearMap_pullbackGlobalSections_eq_one π hV L _
    (Scheme.Modules.Hom.app e.inv V).hom (fun a z => Scheme.Modules.Hom.app_smul e.inv a z) hs
  exact ⟨ℓ, hℓ, hb (Function.bijective_iff_has_inverse.2 ⟨Scheme.Modules.Hom.app e.hom V,
      fun y => congr(Scheme.Modules.Hom.app $(Iso.inv_hom_id e) V y),
      fun x => congr(Scheme.Modules.Hom.app $(Iso.hom_inv_id e) V x)⟩)⟩

open Stacks.Picard in
/-- **Over an affine open on which a class `m` of the base is trivial, a divisor of class
`[ℒ] + π^*m` is the zero scheme of `e(1)`**, for `𝒪_T ≅ π_*ℒ`, as soon as it does not contain any
fibre. -/
theorem comap_eq_comap_zeroScheme [IsProper π] [Flat π] (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (e : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ≅ (Scheme.Modules.pushforward π).obj L)
    {V : T.Opens} (hV : IsAffineOpen V) (hne : ∀ t ∈ V, Nonempty (π.fiber t))
    (Z : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor Z]
    (hfibZ : ∀ t ∈ V, Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (π.fiberι t)))
    (m : ofScheme T) (hm : schemePullbackClass V.ι m = 0)
    (hZ : Stacks.Divisors.picardClass Z = Stacks.SheafOfModules.picardClass Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L hL + schemePullbackClass π m) :
    Z.comap (π ⁻¹ᵁ V).ι = (Stacks.Divisors.zeroScheme Y L
      (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T, ⊤)))).comap (π ⁻¹ᵁ V).ι := by
  set ι := (π ⁻¹ᵁ V).ι
  set s := Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T, ⊤))
  set MZ : Y.Modules :=
    (Stacks.Picard.picardRepresentative Y.toRingedSpace (Stacks.Divisors.picardClass Z)).obj
  have hMZ : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 MZ :=
    (Stacks.Picard.picardRepresentative Y.toRingedSpace (Stacks.Divisors.picardClass Z)).property
  have := isInvertible_sheaf_of_stacks hMZ
  obtain ⟨eZ⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard Z) hMZ).1
    (classOf_picardRepresentative _ _).symm
  obtain ⟨σ, -, hσZ⟩ := exists_isRegularSection_zeroScheme_eq Z MZ eZ
  have hcl : schemePullbackClass ι (Stacks.Divisors.picardClass Z) =
      schemePullbackClass ι (Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L hL) := by
    rw [hZ, schemePullbackClass_add, schemePullbackClass_comp, ← morphismRestrict_ι,
      ← schemePullbackClass_comp, hm]
    exact add_eq_left.2 (map_zero (schemePullbackClassHom (π ∣_ V)))
  have hιL := Stacks.RingedSpace.modulePullback_isInvertible_of ι.toLRSHom.toShHom L hL
  have hιM := Stacks.RingedSpace.modulePullback_isInvertible_of ι.toLRSHom.toShHom MZ hMZ
  have hcl' : Stacks.SheafOfModules.picardClass _ _ _ hιM =
      Stacks.SheafOfModules.picardClass _ _ _ hιL := by
    refine (pullbackClass_classOf ι.toLRSHom.toShHom MZ hMZ).symm.trans (Eq.trans ?_
      (pullbackClass_classOf ι.toLRSHom.toShHom L hL))
    refine Eq.trans ?_ hcl
    show schemePullbackClass ι _ = schemePullbackClass ι _
    rw [classOf_picardRepresentative]
  obtain ⟨φ⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ hιM hιL).1 hcl'
  set F := (Scheme.Modules.pullback ι).obj L
  set fV := (π ∣_ V) ≫ hV.isoSpec.hom
  let := Stacks.Cech.sectionsModule fV F ⊤
  obtain ⟨ℓ, hℓ, hbij⟩ := exists_linearMap_of_iso π L e hV
  set τ : Γ(F, ⊤) := Scheme.Modules.Hom.app φ.hom ⊤
    (pullbackGlobalSections ι MZ (σ.eval (op ⊤)))
  have hτ : τ = ℓ τ • pullbackGlobalSections ι L s :=
    hbij.1 (by rw [map_smul, hℓ, smul_eq_mul, mul_one])
  have hunit : IsUnit (ℓ τ) := by
    refine RingedSpace.isUnit_of_isUnit_germ T.toRingedSpace V _ fun t ht => ?_
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    have hσt : pullbackGlobalSections (π.fiberι t) MZ (σ.eval (op ⊤)) ≠ 0 := by
      have := hne t ht
      have hMt := Stacks.RingedSpace.modulePullback_isInvertible_of
        (π.fiberι t).toLRSHom.toShHom MZ hMZ
      have := isInvertible_sheaf_of_stacks hMt
      refine Stacks.Divisors.ne_zero_of_isEffectiveCartierDivisor_zeroScheme _ _ ?_
      rw [Stacks.Divisors.zeroScheme_pullback (π.fiberι t) MZ (σ.eval (op ⊤))]
      convert hfibZ t ht using 2
    have hτt := pullbackGlobalSections_fiberιOfMem_ne_zero π t ht φ (σ.eval (op ⊤)) hσt
    have hsq := isPullback_fiberιOfMem π hV t ht
    let : Module (T.residueField t)
        Γ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj F, (fiberιOfMem π t ht) ⁻¹ᵁ ⊤) :=
      Stacks.Cech.sectionsModule (π.fiberToSpecResidueField t)
        ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj F) ((fiberιOfMem π t ht) ⁻¹ᵁ ⊤)
    let : Module Γ(T, V)
        Γ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj F, (fiberιOfMem π t ht) ⁻¹ᵁ ⊤) :=
      Stacks.Cech.baseSectionsModule (fiberιOfMem π t ht) F (residueOfMem t ht).hom
        (π.fiberToSpecResidueField t) ((fiberιOfMem π t ht) ⁻¹ᵁ ⊤)
    have h1 := LinearMap.map_smul (Stacks.Cech.pullbackSectionsBaseₗ (fiberιOfMem π t ht) F
      (residueOfMem t ht).hom fV (π.fiberToSpecResidueField t)
      (fun W => Stacks.Cech.baseRingHom_comp_app _ fV _ _ hsq W) ⊤) (ℓ τ)
      (pullbackGlobalSections ι L s)
    rw [← hτ] at h1
    apply hτt
    refine (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.pullbackSectionsBaseₗ_top_apply
      _ fV _ _ F _ τ).symm.trans (h1.trans ?_)
    show ((residueOfMem t ht).hom (ℓ τ) • (Stacks.Cech.pullbackSectionsBaseₗ
      (fiberιOfMem π t ht) F (residueOfMem t ht).hom fV (π.fiberToSpecResidueField t)
      (fun W => Stacks.Cech.baseRingHom_comp_app _ fV _ _ hsq W) ⊤)
        (pullbackGlobalSections ι L s) : Γ((Scheme.Modules.pullback (fiberιOfMem π t ht)).obj F,
          (fiberιOfMem π t ht) ⁻¹ᵁ ⊤)) = 0
    rw [show (residueOfMem t ht).hom (ℓ τ) = 0 from h0, zero_smul]
  have hua : IsUnit ((Stacks.Cech.baseRingHom fV ⊤).hom (ℓ τ)) := hunit.map _
  have i1 : SheafOfModules.IsInvertible _ _ ((Scheme.Modules.pullback ι).obj MZ) :=
    isInvertible_sheaf_of_stacks hιM
  have i2 : SheafOfModules.IsInvertible _ _ F := isInvertible_sheaf_of_stacks hιL
  have hZV : Z.comap ι = Stacks.Divisors.zeroScheme _ F τ := by
    refine Eq.trans ?_ (@Stacks.Divisors.zeroScheme_congr_iso _ _ _ i1 i2 φ _).symm
    rw [Stacks.Divisors.zeroScheme_pullback ι MZ (σ.eval (op ⊤))]
    exact congrArg (fun I => I.comap ι) hσZ.symm
  rw [hZV, ← Stacks.Divisors.zeroScheme_pullback ι L s, hτ]
  exact Stacks.Divisors.zeroScheme_smul_of_isUnit F _ hua

open Stacks.Picard in
/-- **A divisor of class `[ℒ] + π^*m` containing no fibre is the zero scheme of `e(1)`**, for
`𝒪_T ≅ π_*ℒ` and `π` proper and flat with nonempty fibres. -/
theorem eq_zeroScheme_of_picardClass_eq [IsProper π] [Flat π] (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (e : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ≅ (Scheme.Modules.pushforward π).obj L)
    (hne : ∀ t : T, Nonempty (π.fiber t))
    (Z : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor Z]
    (hfibZ : ∀ t : T, Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (π.fiberι t)))
    (m : ofScheme T)
    (hZ : Stacks.Divisors.picardClass Z = Stacks.SheafOfModules.picardClass Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L hL + schemePullbackClass π m) :
    Z = Stacks.Divisors.zeroScheme Y L (Scheme.Modules.Hom.app e.hom ⊤ (1 : Γ(T, ⊤))) := by
  choose V hV hyV hm using fun y : Y => exists_isAffineOpen_schemePullbackClass_eq_zero m (π y)
  refine Stacks.Divisors.IdealSheafData.ext_of_comap_eq (fun y => π ⁻¹ᵁ V y) ?_ fun y => ?_
  · exact top_unique fun y _ => Opens.mem_iSup.2 ⟨y, hyV y⟩
  · exact comap_eq_comap_zeroScheme π L hL e (hV y) (fun t _ => hne t) Z (fun t _ => hfibZ t) m
      (hm y) hZ

end AlgebraicGeometry

namespace Stacks.RigidifiedPicard

open AlgebraicGeometry AlgebraicGeometry.ProperFlatFibreEulerCharacteristic Stacks.Picard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]

/-- **The core claim in the proof of [Stacks, Tag 0B9X], existence.** Let `X` be a smooth proper
geometrically irreducible curve of genus `g` over a field `k`, `T` a `k`-scheme, and `c` a Picard
class of `X_T` whose representative `ℳ` has `Rπ_*ℳ` an invertible module placed in degree zero.
Then there is a degree-`g` Hilbert family `D` of `X` over `T` whose class `[𝒪(D)]` is `c + π^*n`
for some class `n` of `T`. -/
theorem exists_hilbertFamily_abelClass_eq (T : Over (Spec (.of k))) (c : ofScheme (bc f T))
    (hc : HasInvertibleDirectImage f T c) :
    ∃ (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f)) (n : ofScheme T.left),
      abelClass f Z = c + schemePullbackClass (bcProj f T) n := by
  obtain ⟨D, n, hD, hrank, hcl⟩ := exists_relativeEffectiveCartierDivisor_picardClass_eq f T c hc
  exact ⟨⟨D, hrank⟩, n, hcl⟩

/-- **The core claim in the proof of [Stacks, Tag 0B9X], uniqueness.** Two degree-`g` Hilbert
families `D`, `D'` of `X` over `T` such that `Rπ_*𝒪(D)` is an invertible module placed in degree
zero and `[𝒪(D')] - [𝒪(D)]` comes from `T` are equal. -/
theorem eq_of_abelClass_eq (T : Over (Spec (.of k)))
    (Z Z' : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f))
    (hZ : HasInvertibleDirectImage f T (abelClass f Z))
    (hZZ' : ∃ n : ofScheme T.left, abelClass f Z' = abelClass f Z +
      schemePullbackClass (bcProj f T) n) :
    Z = Z' := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  set π := bcProj f T
  have : SmoothOfRelativeDimension 1 π := smoothOfRelativeDimension_one_pullback_snd f T.hom
  obtain ⟨n', hn'⟩ := hZZ'
  obtain ⟨n, ⟨e⟩⟩ := exists_iso_unit_pushforward_picardRepresentative π (abelClass f Z) hZ
  have hL : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf (bc f T).ringCatSheaf.2
      (Stacks.Picard.picardRepresentative (bc f T).toRingedSpace
        (abelClass f Z + schemePullbackClass π n)).obj :=
    (Stacks.Picard.picardRepresentative (bc f T).toRingedSpace
      (abelClass f Z + schemePullbackClass π n)).property
  have := isInvertible_sheaf_of_stacks hL
  have hclL : Stacks.SheafOfModules.picardClass (bc f T).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f T).toRingedSpace) _ hL =
      abelClass f Z + schemePullbackClass π n := classOf_picardRepresentative _ _
  have hne : ∀ t : T.left, Nonempty (π.fiber t) := fun t =>
    have := Stacks.RigidifiedPicard.isIntegral_curveFibre f T t
    inferInstance
  have hfib : ∀ (W : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f)) (t : T.left),
      Stacks.Divisors.IsEffectiveCartierDivisor (W.ideal.comap (π.fiberι t)) := fun W t => by
    have hW := W.isRelativeEffectiveCartierDivisor
    have : Flat (W.ideal.subschemeι ≫ π) := hW.2
    exact isEffectiveCartierDivisor_comap_of_isPullback π (T.left.fromSpecResidueField t)
      (IsPullback.of_hasPullback π (T.left.fromSpecResidueField t)).flip W.ideal hW.1
  let I : (bc f T).IdealSheafData := Z.ideal
  let I' : (bc f T).IdealSheafData := Z'.ideal
  have : Stacks.Divisors.IsEffectiveCartierDivisor I := Z.isRelativeEffectiveCartierDivisor.1
  have : Stacks.Divisors.IsEffectiveCartierDivisor I' := Z'.isRelativeEffectiveCartierDivisor.1
  have h1 := eq_zeroScheme_of_picardClass_eq π _ hL e hne I (hfib Z) (-n) (by
    show abelClass f Z = _
    rw [hclL, add_assoc, ← schemePullbackClass_add, add_neg_cancel]
    exact (add_zero _).symm.trans (congrArg _ (map_zero (schemePullbackClassHom π)).symm))
  have h2 := eq_zeroScheme_of_picardClass_eq π _ hL e hne I' (hfib Z') (n' - n) (by
    show abelClass f Z' = _
    rw [hn', hclL, add_assoc, ← schemePullbackClass_add, add_sub_cancel])
  exact Stacks.Hilbert.HilbertFamily.ext (h1.trans h2.symm)

end Stacks.RigidifiedPicard


namespace Stacks.WeilCohomology

/-- **The claim in the proof of [Stacks, Tag 0B9X], existence half, over every field.** -/
theorem cohomologyLocusDivisorExistence (K : Type u) [Field K] :
    CohomologyLocusDivisorExistence K :=
  fun f _ _ _ T c hc => Stacks.RigidifiedPicard.exists_hilbertFamily_abelClass_eq f T c hc

/-- **The claim in the proof of [Stacks, Tag 0B9X], uniqueness half, over every field.** -/
theorem cohomologyLocusDivisorUniqueness (K : Type u) [Field K] :
    CohomologyLocusDivisorUniqueness K :=
  fun f _ _ _ T Z Z' hZ hZZ' => Stacks.RigidifiedPicard.eq_of_abelClass_eq f T Z Z' hZ hZZ'

end Stacks.WeilCohomology

end
