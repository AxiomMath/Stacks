module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionTfae
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartRigEtaleDiagonalEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveRigEtaleDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite

/-!
# Fibre products of charts of a flat formal space with rig-étale rig-surjective diagonal

For `q : X' ⟶ Spf A` as in Stacks 0GD9 and charts `a : U ⟶ X'`, `b : V ⟶ X'`, the comparison
`U ×_{X'} V ⟶ U ×_{Spf A} V` is an isomorphism: it is a representable étale monomorphism,
rig-surjective as a base change of the diagonal, and every point of the formal spectrum of a flat
Noetherian adic ring is the closed point of an adic point out of a complete discrete valuation
ring, so it is surjective on points and hence a surjection of sheaves (Stacks 03Y8).

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallySurjective_of_isSurjective_of_isRepresentableEtale`
* `AlgebraicGeometry.FormalSpace.FieldValuedPointULift.class_eq_of_ker_eq`
* `AlgebraicGeometry.FormalSpace.exists_adic_completeDvr_point_of_pointsULift`
* `AlgebraicGeometry.FormalSpace.isSurjective_of_isRigSurjective`
* `AlgebraicGeometry.FormalSpace.isIso_pullback_map_of_isRigEtale_of_isRigSurjective_diagonal`

## References

* [Stacks Project, Tag 0GD9](https://stacks.math.columbia.edu/tag/0GD9)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of presheaves which is étale and whose target is a universe-lifted Yoneda
presheaf is locally of finite presentation on every étale chart: in a commuting square of étale
charts over a morphism `h` of the site, `h` is étale on schemes by Stacks 02GW, hence locally of
finite presentation. -/
theorem holdsOnEveryEtaleChartULift_locallyOfFinitePresentation_of_isEtaleULift_of_uliftYoneda
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {T : BigFppfOver B S hS}
    (g : F ⟶ (uliftYoneda.{w}).obj T) (hg : IsEtaleULift.{w} B S hS g) :
    HoldsOnEveryEtaleChartULift.{w} B S hS
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) g := by
  intro U V a b h ha hb hsq
  obtain ⟨β, rfl⟩ : ∃ β : V ⟶ T, (uliftYoneda.{w}).map β = b :=
    ⟨(uliftYoneda.{w}).preimage b, by simp⟩
  have key : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})
        ((uliftYoneda.{w}).map (h ≫ β)) := by
    rw [Functor.map_comp, hsq]
    exact hg U a ha
  have hcomp : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (h ≫ β)) :=
    (relative_etale_uliftYoneda_map_iff B S hS (h ≫ β)).mp key
  rw [Functor.map_comp] at hcomp
  have : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h) :=
    MorphismProperty.of_postcomp (@AlgebraicGeometry.Etale.{u}) _ _
      ((relative_etale_uliftYoneda_map_iff B S hS β).mp hb) hcomp
  infer_instance

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A representable étale morphism surjective on points is a surjection of sheaves.** It is
flat and locally of finite presentation on every étale chart after every represented base change,
so Stacks 03Y8 in the form `isLocallySurjective_of_isSurjective_of_flat` applies. -/
theorem isLocallySurjective_of_isSurjective_of_isRepresentableEtale {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsRepresentableEtale B S hS f) (hsurj : IsSurjective B S hS f) :
    Sheaf.IsLocallySurjective f := by
  obtain ⟨hrep, hflat⟩ := IsRepresentableFlat.of_isRepresentableEtale B S hS f hf
  refine isLocallySurjective_of_isSurjective_of_flat B S hS hrep hsurj hflat fun U ξ => ?_
  change Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (pullback.fst ξ f.hom)
  exact Space.holdsOnEveryEtaleChartULift_locallyOfFinitePresentation_of_isEtaleULift_of_uliftYoneda
    B S hS (pullback.fst ξ f.hom) (hf.2 U ξ)

section Points

variable {R : Type u} [CommRing R] [TopologicalSpace R] (E : QuotientSystem B S hS R)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Two stage points of a formal spectrum with the same kernel are the same point.** Let `p₁`
and `p₂` be field-valued points of `Spf R` given by morphisms `tᵢ : Spec Ωᵢ ⟶ Spec (R ⧸ I)` into
one quotient stage, with ring maps `φᵢ : R ⧸ I → Ωᵢ`. If `φ₁` and `φ₂` have the same kernel `𝔭`,
then `p₁` and `p₂` define the same point: both dominate the point of the residue field of `𝔭`,
through which `φ₁` and `φ₂` factor. -/
theorem FieldValuedPointULift.class_eq_of_ker_eq
    (I : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (p₁ p₂ : Space.FieldValuedPointULift.{u + 1} B S hS (formalSpectrum E).obj)
    (t₁ : p₁.siteObject B S hS _ ⟶ (BigAffineFppf.inclusion B S hS).obj (E.stage I))
    (t₂ : p₂.siteObject B S hS _ ⟶ (BigAffineFppf.inclusion B S hS).obj (E.stage I))
    (h₁ : p₁.value = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t₁ ≫
        formalSpectrumInclusion E (OrderDual.toDual I)))
    (h₂ : p₂.value = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t₂ ≫
        formalSpectrumInclusion E (OrderDual.toDual I)))
    (φ₁ : R ⧸ I.1 →+* p₁.carrier) (φ₂ : R ⧸ I.1 →+* p₂.carrier)
    (hφ₁ : t₁.left.hom = Spec.map (CommRingCat.ofHom φ₁))
    (hφ₂ : t₂.left.hom = Spec.map (CommRingCat.ofHom φ₂))
    (hker : RingHom.ker φ₁ = RingHom.ker φ₂) :
    p₁.class B S hS _ = p₂.class B S hS _ := by
  classical
  set 𝔭 := RingHom.ker φ₁
  have _ : 𝔭.IsPrime := RingHom.ker_isPrime φ₁
  let κ := 𝔭.ResidueField
  have hκ : B.Contains (Spec (.of κ)) := BigFppfSite.contains_spec_residueField_atPrime B
    (E.inSite I) 𝔭
  let α : R ⧸ I.1 →+* κ := algebraMap _ _
  -- the point of the residue field of `𝔭`
  let t₀ : (Over.mk (⟨Spec.map (CommRingCat.ofHom α) ≫ E.overS I⟩ : B.obj hκ ⟶ B.obj hS) :
      BigFppfOver B S hS) ⟶ (BigAffineFppf.inclusion B S hS).obj (E.stage I) :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom α))) rfl
  let p₀ : Space.FieldValuedPointULift.{u + 1} B S hS (formalSpectrum E).obj :=
    { carrier := κ
      contained := hκ
      toBase := Spec.map (CommRingCat.ofHom α) ≫ E.overS I
      value := Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t₀ ≫
          formalSpectrumInclusion E (OrderDual.toDual I)) }
  have hdom : ∀ (p : Space.FieldValuedPointULift.{u + 1} B S hS (formalSpectrum E).obj)
      (t : p.siteObject B S hS _ ⟶ (BigAffineFppf.inclusion B S hS).obj (E.stage I))
      (φ : R ⧸ I.1 →+* p.carrier),
      p.value = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t ≫
          formalSpectrumInclusion E (OrderDual.toDual I)) →
      t.left.hom = Spec.map (CommRingCat.ofHom φ) → RingHom.ker φ = 𝔭 →
      Space.FieldValuedPointULift.Dominates B S hS _ p p₀ := by
    intro p t φ hp ht hk
    have h₁ : 𝔭 ≤ RingHom.ker φ := hk.ge
    have h₂ : 𝔭.primeCompl ≤ (IsUnit.submonoid p.carrier).comap φ := fun x hx =>
      isUnit_iff_ne_zero.mpr fun h0 => hx (hk ▸ RingHom.mem_ker.mpr h0)
    let L : κ →+* p.carrier := Ideal.ResidueField.lift 𝔭 φ h₁ h₂
    have hLα : L.comp α = φ := RingHom.ext (Ideal.ResidueField.lift_algebraMap 𝔭 φ h₁ h₂)
    have hspec : Spec.map (CommRingCat.ofHom L) ≫ Spec.map (CommRingCat.ofHom α) =
        Spec.map (CommRingCat.ofHom φ) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hLα]
    let f : p.siteObject B S hS _ ⟶ p₀.siteObject B S hS _ :=
      Over.homMk (⟨Spec.map (CommRingCat.ofHom L)⟩ : B.obj p.contained ⟶ B.obj hκ) (by
        ext
        change Spec.map (CommRingCat.ofHom L) ≫ Spec.map (CommRingCat.ofHom α) ≫ E.overS I =
          p.toBase
        rw [← Category.assoc, hspec, ← ht]
        exact congrArg (fun k => k.hom) (Over.w t))
    have hft : f ≫ t₀ = t := by
      ext
      change Spec.map (CommRingCat.ofHom L) ≫ Spec.map (CommRingCat.ofHom α) = t.left.hom
      rw [hspec, ht]
    refine ⟨f, (Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) f
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t₀ ≫
        formalSpectrumInclusion E (OrderDual.toDual I))).symm.trans ?_⟩
    rw [hp]
    exact congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS))
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ formalSpectrumInclusion E (OrderDual.toDual I))
          (((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp f t₀).symm.trans
            (congrArg _ hft))))
  exact (Space.FieldValuedPointULift.class_eq_class_of_hasCommonExtension B S hS _
    ⟨p₁, Space.FieldValuedPointULift.dominates_refl B S hS _ p₁, hdom p₁ t₁ φ₁ h₁ hφ₁ rfl⟩).trans
    (Space.FieldValuedPointULift.class_eq_class_of_hasCommonExtension B S hS _
    ⟨p₂, Space.FieldValuedPointULift.dominates_refl B S hS _ p₂,
      hdom p₂ t₂ φ₂ h₂ hφ₂ hker.symm⟩).symm

end Points

section DvrPoints

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R] [IsNoetherianRing R] (E : QuotientSystem B S hS R)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Every point of the formal spectrum of a flat Noetherian adic ring is the closed point of an
adic point out of a complete discrete valuation ring.** Let `R` be a Noetherian adic ring and
`π ∈ R` a nonzerodivisor some power of which lies in every open ideal. Then every point of
`Spf R` is the image of the closed point of `Spf W` under an adic morphism `Spf W ⟶ Spf R`,
for a complete discrete valuation ring `W`.

A point is given by a ring map `R → Ω` into a field killing an open ideal; its kernel `𝔪` is an
open prime, it contains a minimal prime `𝔮`, which avoids `π`, and
`exists_adic_completeDvr_point_of_le_isPrime` gives an adic point with kernel `𝔮` and closed point
`𝔪`; its closed point has kernel `𝔪` too, so it is the given point
(`FieldValuedPointULift.class_eq_of_ker_eq`). -/
theorem exists_adic_completeDvr_point_of_pointsULift (hR : TopologicalRing.IsAdic R) {π : R}
    (hπ : π ∈ nonZeroDivisors R) (hπpow : ∀ I : Ideal R, IsOpen (I : Set R) → ∃ N, π ^ N ∈ I)
    (z : Space.pointsULift.{u + 1} B S hS (formalSpectrum E).obj) :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : TopologicalSpace W) (_ : IsTopologicalRing W) (_ : IsLinearTopology W W)
      (hWadic : _root_.IsAdic (IsLocalRing.maximalIdeal W)),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
        ∃ (_ : TopologicalRing.IsWeaklyAdmissible W) (DW : QuotientSystem B S hS W)
          (χ : ContinuousHom E DW),
          Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
            (formalSpectrumMap (Rig.weaklyAdmissible_of_isAdicRing hR) χ).hom ∧
          Space.pointsMapULift.{u + 1} B S hS (formalSpectrum DW).obj
            (formalSpectrumMap (Rig.weaklyAdmissible_of_isAdicRing hR) χ).hom
            ((residuePoint hWadic DW).class B S hS _) = z := by
  classical
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  have hcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS _)) :=
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of p.carrier)))
  obtain ⟨I, t, ht⟩ := exists_factorsThroughStage_of_compactSpace
    (Rig.weaklyAdmissible_of_isAdicRing hR).1 E _ hcpt
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm p.value)
  have h₁ : p.value = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t ≫
        formalSpectrumInclusion E (OrderDual.toDual I)) :=
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).apply_symm_apply p.value).symm.trans
      (congrArg _ ht.symm)
  let f : Spec (CommRingCat.of p.carrier) ⟶ Spec (CommRingCat.of (R ⧸ I.1)) := t.left.hom
  let φ : R ⧸ I.1 →+* p.carrier := (Spec.preimage f).hom
  have hφ : t.left.hom = Spec.map (CommRingCat.ofHom φ) := (Spec.map_preimage f).symm
  -- the kernel of the point and a minimal prime below it
  set 𝔪 := RingHom.ker (φ.comp (Ideal.Quotient.mk I.1))
  have _ : 𝔪.IsPrime := RingHom.ker_isPrime _
  have hI𝔪 : I.1 ≤ 𝔪 := fun x hx => by
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  obtain ⟨𝔮, h𝔮, h𝔮𝔪⟩ := Ideal.exists_minimalPrimes_le (J := 𝔪) bot_le
  have h𝔮' : 𝔮 ∈ minimalPrimes R := by simpa [minimalPrimes] using h𝔮
  have _ : 𝔮.IsPrime := h𝔮'.1.1
  have hπ𝔮 : π ∉ 𝔮 := fun h => notMem_nonZeroDivisors_of_mem_mem_minimalPrimes h h𝔮' hπ
  obtain ⟨J, hJ, -, -⟩ := exists_idealOfDefinition_isAdicComplete hR
  have hJ𝔪 : J ≤ 𝔪 := by
    obtain ⟨n, hn⟩ := hJ.2 (I.1 : Set R) (I.2.1.mem_nhds I.1.zero_mem)
    intro x hx
    exact (inferInstance : 𝔪.IsPrime).mem_of_pow_mem n
      (hI𝔪 (hn (Ideal.pow_mem_pow hx n)))
  have h𝔮J : ¬ J ≤ 𝔮 := by
    intro hle
    obtain ⟨N, hN⟩ := hπpow J hJ.1
    exact hπ𝔮 ((inferInstance : 𝔮.IsPrime).mem_of_pow_mem N (hle hN))
  obtain ⟨W, _, _, _, _, _, _, hWadic, hWc, hWw, DW, χ, hker, hcomap, hrep⟩ :=
    exists_adic_completeDvr_point_of_le_isPrime B S hS hR E h𝔮𝔪 hJ hJ𝔪 h𝔮J
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hWadic, hWc, hWw, DW, χ, hrep, ?_⟩
  have hIm : I.1 ≤ Ideal.comap χ.toRingHom (residueStage hWadic).1 := by
    change I.1 ≤ (IsLocalRing.maximalIdeal W).comap χ.toRingHom
    rwa [hcomap]
  let p₂ := Space.FieldValuedPointULift.map B S hS _
    (formalSpectrumMap (Rig.weaklyAdmissible_of_isAdicRing hR) χ).hom (residuePoint hWadic DW)
  let t₂ : p₂.siteObject B S hS _ ⟶ (BigAffineFppf.inclusion B S hS).obj (E.stage I) :=
    (BigAffineFppf.inclusion B S hS).map (χ.stageMap I (residueStage hWadic) hIm)
  let φ₂ : R ⧸ I.1 →+* W ⧸ (residueStage hWadic).1 :=
    Ideal.quotientMap (residueStage hWadic).1 χ.toRingHom hIm
  have h₂ : p₂.value =
      Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t₂ ≫
          formalSpectrumInclusion E (OrderDual.toDual I)) := by
    exact (Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS) _ _).symm.trans
      (congrArg _ (formalSpectrumMap_spec _ χ I (residueStage hWadic) hIm))
  rw [Space.pointsMapULift_class.{u + 1}]
  refine (FieldValuedPointULift.class_eq_of_ker_eq B S hS E I p p₂ t t₂ h₁ h₂ φ φ₂ hφ rfl ?_).symm
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change φ (Ideal.Quotient.mk I.1 r) = 0 ↔ Ideal.Quotient.mk _ (χ.toRingHom r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change r ∈ 𝔪 ↔ r ∈ (IsLocalRing.maximalIdeal W).comap χ.toRingHom
  rw [hcomap]

end DvrPoints

section RigSurjectivePoints

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The closed point of the formal spectrum of a complete discrete valuation ring maps to the
closed point under the formal spectrum of an extension. -/
theorem pointsMapULift_residuePoint_of_isExtension {W W' : Type u} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [TopologicalSpace W] [IsTopologicalRing W] [IsLinearTopology W W]
    [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] [TopologicalSpace W']
    [IsTopologicalRing W'] [Algebra W W'] [IsDiscreteValuationRing.IsExtension W W']
    (hWadic : _root_.IsAdic (IsLocalRing.maximalIdeal W))
    (hWw : TopologicalRing.IsWeaklyAdmissible W)
    (hW'adic : _root_.IsAdic (IsLocalRing.maximalIdeal W')) (DW : QuotientSystem B S hS W)
    (DW' : QuotientSystem B S hS W') (e : ContinuousHom DW DW')
    (he : e.toRingHom = algebraMap W W') :
    Space.pointsMapULift.{u + 1} B S hS (formalSpectrum DW').obj (formalSpectrumMap hWw e).hom
        ((residuePoint hW'adic DW').class B S hS _) = (residuePoint hWadic DW).class B S hS _ := by
  classical
  have hcomap : (IsLocalRing.maximalIdeal W').comap e.toRingHom = IsLocalRing.maximalIdeal W := by
    rw [he, IsLocalRing.maximalIdeal_comap]
  have hm : (residueStage hWadic).1 ≤ Ideal.comap e.toRingHom (residueStage hW'adic).1 :=
    hcomap.ge
  have hm' : ∀ {r : W}, e.toRingHom r ∈ (residueStage hW'adic).1 → r ∈ (residueStage hWadic).1 :=
    fun {r} h => by
      change r ∈ IsLocalRing.maximalIdeal W
      rw [← hcomap]
      exact h
  let p₂ := Space.FieldValuedPointULift.map B S hS _ (formalSpectrumMap hWw e).hom
    (residuePoint hW'adic DW')
  let t₂ : p₂.siteObject B S hS _ ⟶
      (BigAffineFppf.inclusion B S hS).obj (DW.stage (residueStage hWadic)) :=
    (BigAffineFppf.inclusion B S hS).map
      (e.stageMap (residueStage hWadic) (residueStage hW'adic) hm)
  have h₂ : p₂.value = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t₂ ≫
        formalSpectrumInclusion DW (OrderDual.toDual (residueStage hWadic))) := by
    exact (Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS) _ _).symm.trans
      (congrArg _ (formalSpectrumMap_spec _ e (residueStage hWadic) (residueStage hW'adic) hm))
  let p₁ := residuePoint hWadic DW
  have h₁ : p₁.value = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (𝟙 _) ≫
        formalSpectrumInclusion DW (OrderDual.toDual (residueStage hWadic))) := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  let f₁ : Spec (CommRingCat.of p₁.carrier) ⟶ Spec (CommRingCat.of (W ⧸ (residueStage hWadic).1)) :=
    (𝟙 (p₁.siteObject B S hS _) : p₁.siteObject B S hS _ ⟶
      (BigAffineFppf.inclusion B S hS).obj (DW.stage (residueStage hWadic))).left.hom
  let φ₁ : W ⧸ (residueStage hWadic).1 →+* p₁.carrier := (Spec.preimage f₁).hom
  have hφ₁ : (𝟙 (p₁.siteObject B S hS _) : p₁.siteObject B S hS _ ⟶
      (BigAffineFppf.inclusion B S hS).obj (DW.stage (residueStage hWadic))).left.hom =
      Spec.map (CommRingCat.ofHom φ₁) := (Spec.map_preimage f₁).symm
  let : Field (W ⧸ (residueStage hWadic).1) := Ideal.Quotient.field _
  rw [Space.pointsMapULift_class.{u + 1}]
  refine (FieldValuedPointULift.class_eq_of_ker_eq B S hS DW (residueStage hWadic) p₁ p₂ (𝟙 _) t₂
    h₁ h₂ φ₁ (Ideal.quotientMap _ e.toRingHom hm) hφ₁ rfl ?_).symm
  rw [(RingHom.injective_iff_ker_eq_bot φ₁).mp φ₁.injective]
  refine le_antisymm bot_le fun x hx => ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h0 : Ideal.Quotient.mk (residueStage hW'adic).1 (e.toRingHom r) = 0 := hx
  rw [Ideal.Quotient.eq_zero_iff_mem] at h0
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  exact hm' h0

/-- **A rig-surjective morphism onto the formal spectrum of a flat Noetherian adic ring is
surjective on points.** Every point of `Spf R` is the closed point of an adic point out of a
complete discrete valuation ring (`exists_adic_completeDvr_point_of_pointsULift`); rig-surjectivity
lifts that adic point after an extension of complete discrete valuation rings, and the closed
point of the extension maps to the closed point. -/
theorem isSurjective_of_isRigSurjective {W P : FppfSheaf B S hS} (g : W ⟶ P)
    (hg : IsRigSurjective B S hS g) {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] [IsNoetherianRing R]
    (hR : TopologicalRing.IsAdic R) (EP : QuotientSystem B S hS R) (eP : P ≅ formalSpectrum EP)
    {π : R} (hπ : π ∈ nonZeroDivisors R)
    (hπpow : ∀ I : Ideal R, IsOpen (I : Set R) → ∃ N, π ^ N ∈ I) :
    IsSurjective B S hS g := by
  classical
  intro y
  obtain ⟨W₀, _, _, _, _, _, _, hW₀adic, hW₀c, hW₀w, DW, χ, hrep, hz⟩ :=
    exists_adic_completeDvr_point_of_pointsULift B S hS EP hR hπ hπpow
      (Space.pointsMapULift.{u + 1} B S hS P.obj eP.hom.hom y)
  have hRw := Rig.weaklyAdmissible_of_isAdicRing hR
  have hptrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hRw χ ≫ eP.inv).hom :=
    Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _ hrep
      (isAdicMorphism_of_isIso B S hS eP.inv)
  obtain ⟨W₁, _, _, _, _, _, _, _, _, hW₁adic, -, D₁, e, w, he, hw⟩ :=
    hg W₀ hW₀adic hW₀c hW₀w DW (formalSpectrumMap hRw χ ≫ eP.inv) hptrep
  refine ⟨Space.pointsMapULift.{u + 1} B S hS _ w.hom ((residuePoint hW₁adic D₁).class B S hS _),
    ?_⟩
  have hcomp : w.hom ≫ g.hom = (formalSpectrumMap hW₀w e).hom ≫ (formalSpectrumMap hRw χ).hom ≫
      eP.inv.hom := congrArg (fun k => k.hom) hw
  have hinv : eP.hom.hom ≫ eP.inv.hom = 𝟙 _ := congrArg (fun k => k.hom) eP.hom_inv_id
  calc Space.pointsMapULift.{u + 1} B S hS _ g.hom
        (Space.pointsMapULift.{u + 1} B S hS _ w.hom ((residuePoint hW₁adic D₁).class B S hS _))
      = Space.pointsMapULift.{u + 1} B S hS _ (w.hom ≫ g.hom)
          ((residuePoint hW₁adic D₁).class B S hS _) := by
        rw [Space.pointsMapULift_comp]
        rfl
    _ = Space.pointsMapULift.{u + 1} B S hS _ eP.inv.hom
          (Space.pointsMapULift.{u + 1} B S hS _ (formalSpectrumMap hRw χ).hom
            (Space.pointsMapULift.{u + 1} B S hS _ (formalSpectrumMap hW₀w e).hom
              ((residuePoint hW₁adic D₁).class B S hS _))) := by
        rw [hcomp, Space.pointsMapULift_comp, Space.pointsMapULift_comp]
        rfl
    _ = Space.pointsMapULift.{u + 1} B S hS _ eP.inv.hom
          (Space.pointsMapULift.{u + 1} B S hS P.obj eP.hom.hom y) := by
        rw [pointsMapULift_residuePoint_of_isExtension B S hS hW₀adic hW₀w hW₁adic DW D₁ e he, hz]
    _ = y := by
        rw [← Function.comp_apply (f := Space.pointsMapULift.{u + 1} B S hS _ eP.inv.hom),
          ← Space.pointsMapULift_comp, hinv, Space.pointsMapULift_id]
        rfl

end RigSurjectivePoints

section ChartPairs

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A] (D : QuotientSystem B S hS A)

omit [IsLinearTopology A A] in
/-- **A uniformizer is a nonzerodivisor of a flat topological algebra and is topologically
nilpotent there.** For a flat continuous homomorphism `c : A → R` out of a discrete valuation ring
with its maximal-adic topology, the image `π` of a uniformizer is a nonzerodivisor of `R` and
some power of it lies in every open ideal of `R`. -/
theorem exists_nonZeroDivisor_pow_mem_of_flat
    (hAadic : _root_.IsAdic (IsLocalRing.maximalIdeal A)) {R : Type u} [CommRing R]
    [TopologicalSpace R] (c : A →+* R) (hc : Continuous c) (hflat : c.Flat) :
    ∃ π : R, π ∈ nonZeroDivisors R ∧ ∀ I : Ideal R, IsOpen (I : Set R) → ∃ N, π ^ N ∈ I := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine ⟨c ϖ, ?_, fun I hI => ?_⟩
  · let _ : Algebra A R := c.toAlgebra
    have _ : Module.Flat A R := hflat
    have hreg : IsSMulRegular R ϖ :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx => hreg ?_
    change ϖ • x = ϖ • 0
    rw [smul_zero, Algebra.smul_def]
    exact (mul_comm _ _).trans hx
  · have hopen : IsOpen (c ⁻¹' (I : Set R)) := hI.preimage hc
    obtain ⟨N, hN⟩ := (isAdic_iff.mp hAadic).2 _ (hopen.mem_nhds (by simp))
    refine ⟨N, ?_⟩
    have hmem : ϖ ^ N ∈ IsLocalRing.maximalIdeal A ^ N :=
      Ideal.pow_mem_pow ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ ▸
        Ideal.mem_span_singleton_self ϖ) N
    simpa [map_pow] using hN hmem

/-- **The fibre product of two charts over `X'` is their fibre product over the base.** Let `A`
be a complete discrete valuation ring with its maximal-adic topology and let `q : X' ⟶ Spf A` be
flat and locally of finite type, with `X'` locally Noetherian and relative diagonal rig-étale and
rig-surjective. Then for affine representable étale charts `a : U ⟶ X'` and `b : V ⟶ X'` the
canonical `U ×_{X'} V ⟶ U ×_{Spf A} V` is an isomorphism.

It is a base change of the diagonal of `X'`, so a monomorphism and rig-surjective (Stacks 0AQS);
it is representable étale, `U ×_{Spf A} V ⟶ U` being étale by
`isRepresentableEtale_comp_of_isRigEtale_of_isRigSurjective_diagonal`; the target is the formal
spectrum of a Noetherian adic ring flat over `A`, so rig-surjectivity makes it surjective on
points (`isSurjective_of_isRigSurjective`), hence a surjection of sheaves. -/
theorem isIso_pullback_map_of_isRigEtale_of_isRigSurjective_diagonal
    (hAadic : _root_.IsAdic (IsLocalRing.maximalIdeal A))
    (hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A) {X' U V : FppfSheaf B S hS}
    (q : X' ⟶ formalSpectrum D) (hX' : IsLocallyNoetherian B S hS X')
    (hq : IsLocallyOfFiniteType B S hS q) (hqflat : IsFlat B S hS q)
    (hdiagE : IsRigEtale B S hS (pullback.diagonal q))
    (hdiagS : IsRigSurjective B S hS (pullback.diagonal q)) (a : U ⟶ X') (b : V ⟶ X')
    (hU : IsAffineFormalAlgebraicSpace B S hS U) (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b) :
    IsIso (pullback.map a b (a ≫ q) (b ≫ q) (𝟙 U) (𝟙 V) q (by simp) (by simp)) := by
  classical
  set g := pullback.map a b (a ≫ q) (b ≫ q) (𝟙 U) (𝟙 V) q (by simp) (by simp)
  have hAN : TopologicalRing.IsAdic A :=
    topologicalRingIsAdic_of_isAdic_of_isAdicComplete hAadic hAc
  -- `g` is representable étale
  have hbq := isRepresentableEtale_comp_of_isRigEtale_of_isRigSurjective_diagonal B S hS D hAadic
    hAc q hX' hq hqflat hdiagE hdiagS b hV hb
  have hfst : IsRepresentableEtale B S hS (pullback.fst (a ≫ q) (b ≫ q)) :=
    isRepresentableEtale_of_isPullback B S hS (IsPullback.of_hasPullback (a ≫ q) (b ≫ q)).flip hbq
  have hgfst : g ≫ pullback.fst (a ≫ q) (b ≫ q) = pullback.fst a b := by
    simp [g]
  have hfstab : IsRepresentableEtale B S hS (pullback.fst a b) :=
    isRepresentableEtale_of_isPullback B S hS (IsPullback.of_hasPullback a b).flip hb
  have hget : IsRepresentableEtale B S hS g :=
    isRepresentableEtale_of_comp' B S hS g _ hfst (hgfst ▸ hfstab)
  -- `g` is a monomorphism
  have hmono : Mono g := by
    refine ⟨fun x y hxy => pullback.hom_ext ?_ ?_⟩
    · simpa [g] using congrArg (· ≫ pullback.fst (a ≫ q) (b ≫ q)) hxy
    · simpa [g] using congrArg (· ≫ pullback.snd (a ≫ q) (b ≫ q)) hxy
  -- `g` is rig-surjective, being a base change of the diagonal of `X'`
  have hgs : IsRigSurjective B S hS g :=
    IsRigSurjective.of_isPullback_of_representable B S hS
      (pullback_map_diagonal_isPullback a b q).flip
      (isRepresentableEtale_pullback_map B S hS q q ha hb).1 hdiagS
  -- the target is the formal spectrum of a flat Noetherian adic ring
  obtain ⟨-, -, hPn⟩ := isAffine_and_isNoetherian_pullback_charts B S hS D hAN q hX' hq hU hV
    ha hb
  obtain ⟨R, _, _, _, _, EP, hR, ⟨eP⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS hPn
  have _ : IsNoetherianRing R := hR.2
  obtain ⟨c, hc, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hAN.isWeaklyAdmissible
    hR.1.isWeaklyAdmissible (eP.inv ≫ pullback.snd (a ≫ q) (b ≫ q) ≫ b ≫ q)
  have hcflat := flat_of_isPullback_charts B S hS D hAN q hX' hq hqflat hU hV ha hb hR.1 EP eP c
    hc
  obtain ⟨π, hπ, hπpow⟩ := exists_nonZeroDivisor_pow_mem_of_flat hAadic c.toRingHom c.continuous
    hcflat
  have : Epi g := (Sheaf.isLocallySurjective_iff_epi g).mp
    (isLocallySurjective_of_isSurjective_of_isRepresentableEtale B S hS g hget
      (isSurjective_of_isRigSurjective B S hS g hgs hR.1 EP eP hπ hπpow))
  exact isIso_of_mono_of_epi g

end ChartPairs

end AlgebraicGeometry.FormalSpace

end
