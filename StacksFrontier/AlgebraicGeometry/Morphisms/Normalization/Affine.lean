module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.RingTheory.Branches.MinimalPrimes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine opens in the normalization of a reduced scheme

Let `X` be a reduced scheme whose quasi-compact opens have finitely many irreducible
components. Over an affine open `Spec A` of `X`, the normalization of `X` is the spectrum of
the integral closure of `A` in its total ring of fractions.

## Main definitions

* `AlgebraicGeometry.preimageNormalizationIsoSpecIntegralClosure`: the identification of the
  normalization over an affine open `Spec A` with the spectrum of the integral closure of `A`
  in its total ring of fractions.

## Main results

* `AlgebraicGeometry.preimageNormalizationIsoSpecIntegralClosure_hom_comp`: under that
  identification, the restriction of the normalization morphism is the spectrum map induced by
  the inclusion of `A` into its integral closure.

## Implementation notes

The affine open is presented by an isomorphism `Spec A ≅ U` rather than by an equality of
rings, so a ring presenting it is only determined up to isomorphism; the identification is
therefore stated for an arbitrary such presentation.

## References

* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The map on sections induced by `X.fromSpecStalk x`, followed by the canonical identification
of the global sections of a spectrum, is the germ map at `x`. -/
lemma fromSpecStalk_appLE_germ
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∈ U)
    (hle : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U) :
    (X.fromSpecStalk x).appLE U ⊤ hle ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom = X.presheaf.germ U x hx := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  have hc :
      (homOfLE (show X.fromSpecStalk x ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫
          (homOfLE hle).op =
        𝟙 (Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens)) := Subsingleton.elim _ _
  rw [hc]
  simp

/-- The map on sections over `⊤` induced by a morphism is its map on global sections. -/
private lemma appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ h = f.appTop := by
  convert Scheme.Hom.appLE_eq_app f (U := ⊤) using 1 <;> simp
  rfl

/-- The map on sections induced by `X.fromSpecResidueField x`, followed by the canonical
identification of the global sections of a spectrum, is evaluation at `x`. -/
lemma fromSpecResidueField_appLE_eval
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∈ U)
    (hle : ⊤ ≤ (X.fromSpecResidueField x) ⁻¹ᵁ U) :
    (X.fromSpecResidueField x).appLE U ⊤ hle ≫
      (Scheme.ΓSpecIso (X.residueField x)).hom = X.evaluation U x hx := by
  have h1 : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun y _ ↦ by
    have hs : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hs
    exact hs.mem_open U.isOpen hx
  have h2 : ⊤ ≤ Spec.map (X.residue x) ⁻¹ᵁ (⊤ : (Spec (X.presheaf.stalk x)).Opens) := by
    simp
  show (Spec.map (X.residue x) ≫ X.fromSpecStalk x).appLE U ⊤ hle ≫
      (Scheme.ΓSpecIso (X.residueField x)).hom = _
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (X.residue x)) (X.fromSpecStalk x)
    U ⊤ ⊤ h1 h2]
  rw [appLE_top_top, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc,
    fromSpecStalk_appLE_germ X U x hx h1]
  rfl

/-- The identification of the sections of `X` over an open `U` with the global sections of the
corresponding open subscheme is the map on sections induced by the inclusion of `U`. -/
lemma opensTopIso_inv_eq_ι_appLE (X : Scheme.{u}) (U : X.Opens) :
    U.topIso.inv = U.ι.appLE U ⊤ U.ι_preimage_self.ge := by
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
  congr 1

/-- Pulling sections over `U` back along `f`, viewing the result as global sections of `f ⁻¹ᵁ U`
and then pulling back along a morphism into that open subscheme, is the map on sections
induced by the composite morphism. -/
lemma app_comp_preimage_topIso_inv_appTop
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (m : Z ⟶ (f ⁻¹ᵁ U).toScheme)
    (hle : ⊤ ≤ (m ≫ (f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U) :
    f.app U ≫ (f ⁻¹ᵁ U).topIso.inv ≫ m.appTop =
      (m ≫ (f ⁻¹ᵁ U).ι ≫ f).appLE U ⊤ hle := by
  let W := f ⁻¹ᵁ U
  have hTop : ⊤ ≤ m ⁻¹ᵁ (⊤ : W.toScheme.Opens) := by simp
  rw [opensTopIso_inv_eq_ι_appLE Y W]
  have hcomp : ⊤ ≤ (W.ι ≫ f) ⁻¹ᵁ U := fun y _ ↦ y.2
  have h12 : f.app U ≫ W.topIso.inv = (W.ι ≫ f).appLE U ⊤ hcomp := by
    rw [opensTopIso_inv_eq_ι_appLE Y W]
    convert Scheme.Hom.appLE_comp_appLE W.ι f U W ⊤ le_rfl W.ι_preimage_self.ge using 1
    simp [W, Scheme.Hom.app_eq_appLE]
  rw [← opensTopIso_inv_eq_ι_appLE Y W, ← Category.assoc, h12]
  rw [← appLE_top_top m hTop, Scheme.Hom.appLE_comp_appLE m (W.ι ≫ f) U ⊤ ⊤ hcomp hTop]

/-- The irreducible components of `Spec R` correspond to the minimal primes of `R`, a component
going to its vanishing ideal. -/
@[ega "I 1.1.14"]
noncomputable def componentsEquivMinimalPrimes (R : Type u) [CommRing R] :
    irreducibleComponents (PrimeSpectrum R) ≃ minimalPrimes R := by
  classical
  let g : irreducibleComponents (PrimeSpectrum R) → minimalPrimes R := fun C =>
    ⟨PrimeSpectrum.vanishingIdeal (C : Set (PrimeSpectrum R)), by
      rw [← PrimeSpectrum.vanishingIdeal_irreducibleComponents R]
      exact ⟨C, C.property, rfl⟩⟩
  have hinj : Function.Injective g := fun C D h ↦ Subtype.ext <| by
    have hval := congrArg (fun I : Ideal R => PrimeSpectrum.zeroLocus (I : Set R))
      (congrArg Subtype.val h)
    simp only [g, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure] at hval
    rwa [(isClosed_of_mem_irreducibleComponents _ C.2).closure_eq,
      (isClosed_of_mem_irreducibleComponents _ D.2).closure_eq] at hval
  have hsurj : Function.Surjective g := fun p ↦ by
    obtain ⟨C, hC, hEq⟩ : (p : Ideal R) ∈ PrimeSpectrum.vanishingIdeal ''
        irreducibleComponents (PrimeSpectrum R) := by
      rw [PrimeSpectrum.vanishingIdeal_irreducibleComponents]
      exact p.property
    exact ⟨⟨C, hC⟩, Subtype.ext hEq⟩
  exact Equiv.ofBijective g ⟨hinj, hsurj⟩

/-- The generic points of an affine open correspond to the minimal primes of its ring of
sections. -/
noncomputable def genericPointsAffineOpenEquiv {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) :
    genericPoints (U : Set X) ≃ minimalPrimes Γ(X, U) := by
  let f : U.toScheme ≃ₜ Spec Γ(X, U) := hU.isoSpec.hom.homeomorph
  letI : QuasiSober (U : Set X) := f.isOpenEmbedding.quasiSober
  let ce := irreducibleComponentsEquivOfIsPreirreducibleFiber f f.continuous f.isOpenMap
    (fun x => (Set.subsingleton_singleton.preimage f.injective).isPreirreducible) f.surjective
  let e1 : genericPoints (U : Set X) ≃ irreducibleComponents (U : Set X) := genericPoints.equiv
  let e2 : irreducibleComponents (U : Set X) ≃ irreducibleComponents (PrimeSpectrum Γ(X, U)) :=
    ce.symm.toEquiv
  let e3 : irreducibleComponents (PrimeSpectrum Γ(X, U)) ≃ minimalPrimes Γ(X, U) :=
    componentsEquivMinimalPrimes (Γ(X, U))
  exact e1.trans (e2.trans e3)

/-- Under the correspondence between the generic points of an affine open and the minimal primes
of its ring of sections, a generic point goes to the prime ideal that it is. -/
lemma genericPointsAffineOpenEquiv_asIdeal {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (η : genericPoints (U : Set X)) :
    ((genericPointsAffineOpenEquiv hU η : minimalPrimes Γ(X, U)) : Ideal Γ(X, U)) =
      (hU.isoSpec.hom η.1).asIdeal := by
  classical
  let f : U.toScheme ≃ₜ Spec Γ(X, U) := hU.isoSpec.hom.homeomorph
  let : QuasiSober (U : Set X) := f.isOpenEmbedding.quasiSober
  let ce := irreducibleComponentsEquivOfIsPreirreducibleFiber f f.continuous f.isOpenMap
    (fun x => (Set.subsingleton_singleton.preimage f.injective).isPreirreducible) f.surjective
  let x : U.toScheme := ⟨η.1.1, η.1.2⟩
  have hx : x = η.1 := rfl
  have hcl : f '' closure {x} = closure {f x} := by
    rw [← f.isClosedMap.closure_image_eq_of_continuous f.continuous, Set.image_singleton]
  let η' : genericPoints (PrimeSpectrum Γ(X, U)) :=
    ⟨f x, by
      show closure {f x} ∈ irreducibleComponents (PrimeSpectrum Γ(X, U))
      rw [← hcl]
      show f '' (genericPoints.component η).1 ∈ irreducibleComponents _
      exact (ce.symm (genericPoints.component η)).property⟩
  have hcomp : genericPoints.component η' = ce.symm (genericPoints.component η) :=
    Subtype.ext hcl.symm
  show PrimeSpectrum.vanishingIdeal
      (ce.symm (genericPoints.component η)).1 = _
  rw [← hcomp]
  show PrimeSpectrum.vanishingIdeal (closure ({f x} : Set (PrimeSpectrum Γ(X, U)))) = _
  rw [PrimeSpectrum.vanishingIdeal_closure]
  exact PrimeSpectrum.vanishingIdeal_singleton (f x)

/-- The generic points of `X` lying in an affine open `U` correspond to the minimal primes of the
ring of sections of `U`. -/
noncomputable def genericPointsInOpenEquivMinimalPrimes
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    {η : genericPoints X // η.1 ∈ U} ≃ minimalPrimes Γ(X, U) :=
  (Scheme.genericPointsInOpenEquiv X U).trans (genericPointsAffineOpenEquiv hU)

/-- Under the correspondence between the generic points of `X` lying in an affine open and the
minimal primes of its ring of sections, a generic point goes to the prime ideal that it is. -/
lemma genericPointsInOpenEquivMinimalPrimes_asIdeal
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (η : {η : genericPoints X // η.1 ∈ U}) :
    ((genericPointsInOpenEquivMinimalPrimes hU η : minimalPrimes Γ(X, U)) :
        Ideal Γ(X, U)) =
      (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal := by
  classical
  have hη : (Scheme.genericPointsInOpenEquiv X U η).1 =
      (⟨η.1.1, η.2⟩ : U.toScheme) :=
    Subtype.ext rfl
  show ((genericPointsAffineOpenEquiv hU (Scheme.genericPointsInOpenEquiv X U η) :
      minimalPrimes Γ(X, U)) : Ideal Γ(X, U)) = _
  simpa only [IsAffineOpen.primeIdealOf, hη] using
    genericPointsAffineOpenEquiv_asIdeal hU (Scheme.genericPointsInOpenEquiv X U η)

/-- At a generic point of a reduced scheme the local ring is a field, so the residue map to the
residue field is an isomorphism. -/
@[sga "3 VIB 3.11" "partial"]
lemma residue_isIso_of_genericPoint
    (X : Scheme.{u}) [IsReduced X] (η : genericPoints X) :
    IsIso (X.residue η.1) := by
  let : Field (X.presheaf.stalk η.1) :=
    (isField_stalk_of_closure_mem_irreducibleComponents X η.1 η.2).toField
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨RingHom.injective (X.residue η.1).hom, X.residue_surjective η.1⟩

/-- At a generic point of a reduced scheme lying in an affine open, the residue field is the
localization of the ring of sections of that open at the corresponding prime. -/
lemma residueField_isLocalizationAtPrime
    {X : Scheme.{u}} [IsReduced X] {U : X.Opens} (hU : IsAffineOpen U)
    (η : {η : genericPoints X // η.1 ∈ U}) :
    letI : Algebra Γ(X, U) (X.residueField η.1.1) :=
      (X.evaluation U η.1.1 η.2).hom.toAlgebra
    IsLocalization.AtPrime (X.residueField η.1.1)
      (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal := by
  let x : U := ⟨η.1.1, η.2⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
    X.presheaf.algebra_section_stalk x
  let : IsLocalization.AtPrime (X.presheaf.stalk η.1.1)
      (hU.primeIdealOf x).asIdeal := hU.isLocalization_stalk x
  let : Algebra Γ(X, U) (X.residueField η.1.1) :=
    (X.evaluation U η.1.1 η.2).hom.toAlgebra
  let : IsIso (X.residue η.1.1) := residue_isIso_of_genericPoint X η.1
  let hres : (X.presheaf.stalk η.1.1) ≃+* (X.residueField η.1.1) :=
    (asIso (X.residue η.1.1)).commRingCatIsoToRingEquiv
  let hAlg : (X.presheaf.stalk η.1.1) ≃ₐ[Γ(X, U)] (X.residueField η.1.1) :=
    AlgEquiv.ofRingEquiv (f := hres) fun _ ↦ rfl
  exact IsLocalization.isLocalization_of_algEquiv
    (hU.primeIdealOf x).asIdeal.primeCompl hAlg

/-- The part of the generic-point residue spectrum lying over an open `U` is the coproduct of the
residue-field spectra at the generic points of `X` lying in `U`. -/
noncomputable def genericPreimageIsoSigma (X : Scheme.{u}) (U : X.Opens) :
    (∐ fun η : {η : genericPoints X // η.1 ∈ U} =>
      Spec (.of (X.residueField η.1.1))) ≅
        (Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U).toScheme := by
  classical
  let I := {η : genericPoints X // η.1 ∈ U}
  let C : genericPoints X → Scheme := fun η => Spec (.of (X.residueField η.1))
  let B : I → Scheme := fun η => Spec (.of (X.residueField η.1.1))
  let f := Scheme.fromGenericPointResidueFields X
  let W := f ⁻¹ᵁ U
  let g : (∐ B) ⟶ Scheme.genericPointResidueSpectrum X :=
    Sigma.desc fun η : I => Sigma.ι C η.1
  have hpair : Pairwise (Function.onFun Disjoint fun η : I => Set.range (Sigma.ι C η.1)) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have hz : Sigma.ι C i.1 x ∈
        (Sigma.ι C i.1).opensRange ⊓ (Sigma.ι C j.1).opensRange := ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    rwa [disjoint_iff.mp (disjoint_opensRange_sigmaι C i.1 j.1 fun h ↦ hij (Subtype.ext h))] at hz
  have (η : I) : IsOpenImmersion (Sigma.ι C η.1) := inferInstance
  have (η : I) : IsOpenImmersion (Sigma.ι B η) := inferInstance
  have : IsOpenImmersion g :=
    isOpenImmersion_sigmaDesc B (fun η => Sigma.ι C η.1) hpair
  have hg (η : I) : Sigma.ι B η ≫ g = Sigma.ι C η.1 := Sigma.ι_desc _ η
  have hfcomp (η : genericPoints X) : Sigma.ι C η ≫ f = X.fromSpecResidueField η.1 := by
    simp [C, f]
  have hrange : Set.range g = Set.range W.ι := by
    ext z
    constructor
    · rintro ⟨z, rfl⟩
      let q := (sigmaMk B).symm z
      have hz : z = Sigma.ι B q.1 q.2 := by
        calc
          z = (sigmaMk B) q := (sigmaMk B).apply_symm_apply z |>.symm
          _ = Sigma.ι B q.1 q.2 := by cases q; simp
      have hη : f (g z) ∈ U := by
        rw [hz]
        dsimp only [B]
        change ((Sigma.ι B q.1 ≫ g) ≫ f) q.2 ∈ U
        have hgb := hg q.1
        dsimp only [B] at hgb
        rw [hgb]
        change (Sigma.ι C q.1.1 ≫ f) q.2 ∈ U
        rw [hfcomp q.1.1, Scheme.fromSpecResidueField_apply]
        exact q.1.2
      exact ⟨⟨g z, hη⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      let z : Scheme.genericPointResidueSpectrum X := w.1
      let q := (sigmaMk (fun η : genericPoints X =>
        Spec (.of (X.residueField η.1)))).symm z
      have hz : (sigmaMk C) q = z := (sigmaMk C).apply_symm_apply z
      have hq : q.1.1 ∈ U := by
        have hw : f z ∈ U := w.2
        have hmap : f ((sigmaMk C) q) = q.1.1 := by
          cases q with
          | mk η x =>
            rw [show (sigmaMk C) ⟨η, x⟩ = Sigma.ι C η x by simp]
            change (Sigma.ι C η ≫ f) x = η.1
            rw [Scheme.genericPointResidueSpectrum_ι_fromGenericPointResidueFields,
              Scheme.fromSpecResidueField_apply]
        rw [← hz] at hw
        simpa [hmap] using hw
      refine ⟨(sigmaMk B) ⟨⟨q.1, hq⟩, q.2⟩, ?_⟩
      change g ((sigmaMk B) ⟨⟨q.1, hq⟩, q.2⟩) = z
      have hsrc : (sigmaMk B) ⟨⟨q.1, hq⟩, q.2⟩ = Sigma.ι B ⟨q.1, hq⟩ q.2 :=
        sigmaMk_mk B ⟨q.1, hq⟩ q.2
      rw [hsrc]
      change (Sigma.ι B ⟨q.1, hq⟩ ≫ g) q.2 = z
      rw [hg ⟨q.1, hq⟩]
      change Sigma.ι C q.1 q.2 = z
      have hmk : (sigmaMk C) q = Sigma.ι C q.1 q.2 := by
        simpa using (sigmaMk_mk C q.1 q.2)
      exact hmk.symm.trans hz
  exact IsOpenImmersion.isoOfRangeEq g W.ι hrange

/-- Under `AlgebraicGeometry.genericPreimageIsoSigma`, each summand of the coproduct maps to `X`
by the residue-field morphism at the corresponding generic point. -/
lemma genericPreimageIsoSigma_ι_comp (X : Scheme.{u}) (U : X.Opens)
    (η : {η : genericPoints X // η.1 ∈ U}) :
    Sigma.ι (fun η : {η : genericPoints X // η.1 ∈ U} =>
      Spec (.of (X.residueField η.1.1))) η ≫
        (genericPreimageIsoSigma X U).hom ≫
          (Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U).ι ≫
            Scheme.fromGenericPointResidueFields X =
      X.fromSpecResidueField η.1.1 := by
  classical
  let I := {η : genericPoints X // η.1 ∈ U}
  let C : genericPoints X → Scheme := fun η => Spec (.of (X.residueField η.1))
  let B : I → Scheme := fun η => Spec (.of (X.residueField η.1.1))
  let f := Scheme.fromGenericPointResidueFields X
  let W := f ⁻¹ᵁ U
  let g : (∐ B) ⟶ Scheme.genericPointResidueSpectrum X :=
    Sigma.desc fun η : I => Sigma.ι C η.1
  have hfac : (genericPreimageIsoSigma X U).hom ≫ W.ι = g := by
    have hpair : Pairwise (Function.onFun Disjoint fun ξ : I =>
        Set.range (Sigma.ι C ξ.1)) := by
      intro i j hij
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
      have hz : Sigma.ι C i.1 x ∈
          (Sigma.ι C i.1).opensRange ⊓ (Sigma.ι C j.1).opensRange := ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
      rwa [disjoint_iff.mp (disjoint_opensRange_sigmaι C i.1 j.1 fun h ↦ hij (Subtype.ext h))]
        at hz
    have (ξ : I) : IsOpenImmersion (Sigma.ι C ξ.1) := inferInstance
    have (ξ : I) : IsOpenImmersion (Sigma.ι B ξ) := inferInstance
    have : IsOpenImmersion g :=
      isOpenImmersion_sigmaDesc B (fun ξ => Sigma.ι C ξ.1) hpair
    unfold genericPreimageIsoSigma
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  calc
    _ = (Sigma.ι B η ≫ ((genericPreimageIsoSigma X U).hom ≫ W.ι)) ≫ f := by
      simp only [B, W, f, Category.assoc]
      rfl
    _ = (Sigma.ι B η ≫ g) ≫ f := by rw [hfac]
    _ = (Sigma.ι C η.1) ≫ f := by
      show (Sigma.ι B η ≫ Sigma.desc (fun ξ : I => Sigma.ι C ξ.1)) ≫ f = _
      rw [Sigma.ι_desc]
    _ = X.fromSpecResidueField η.1.1 := by
      simp [C, f]

/-- The sections of the generic-point residue spectrum over the preimage of `U` form the product
of the residue fields at the generic points lying in `U`. -/
noncomputable def genericPreimageSectionsRingEquiv (X : Scheme.{u}) (U : X.Opens)
    [Finite {η : genericPoints X // η.1 ∈ U}] :
    Γ(Scheme.genericPointResidueSpectrum X,
      Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) ≃+*
      (∀ η : {η : genericPoints X // η.1 ∈ U}, X.residueField η.1.1) := by
  classical
  let I := {η : genericPoints X // η.1 ∈ U}
  let R : I → CommRingCat := fun η => .of (X.residueField η.1.1)
  let σ := sigmaSpec R
  letI : IsIso σ := inferInstance
  let eSigma : (∐ fun η : I => Spec (R η)) ≅ Spec (.of (∀ η : I, X.residueField η.1.1)) :=
    asIso σ
  let W := Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U
  let eW : W.toScheme ≅ Spec (.of (∀ η : I, X.residueField η.1.1)) :=
    (genericPreimageIsoSigma X U).symm ≪≫ eSigma
  haveI : IsIso eW.inv.appTop := by
    change IsIso (eW.inv.app ⊤)
    infer_instance
  exact ((W.topIso).symm ≪≫ asIso eW.inv.appTop ≪≫
    Scheme.ΓSpecIso (.of (∀ η : I, X.residueField η.1.1))).commRingCatIsoToRingEquiv

/-- Projecting the product decomposition `AlgebraicGeometry.genericPreimageSectionsRingEquiv`
onto one factor is the map on sections induced by the corresponding summand of the coproduct. -/
lemma genericPreimageSectionsRingEquiv_eval_component
    (X : Scheme.{u}) (U : X.Opens)
    [Finite {η : genericPoints X // η.1 ∈ U}]
    (η : {η : genericPoints X // η.1 ∈ U}) :
    CommRingCat.ofHom (genericPreimageSectionsRingEquiv X U).toRingHom ≫
        CommRingCat.ofHom
          (Pi.evalRingHom (fun η : {η : genericPoints X // η.1 ∈ U} =>
            X.residueField η.1.1) η) =
      (Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U).topIso.inv ≫
        (Sigma.ι (fun η : {η : genericPoints X // η.1 ∈ U} =>
          Spec (.of (X.residueField η.1.1))) η ≫
            (genericPreimageIsoSigma X U).hom).appTop ≫
              (Scheme.ΓSpecIso (X.residueField η.1.1)).hom := by
  classical
  let I := {η : genericPoints X // η.1 ∈ U}
  let R : I → CommRingCat := fun η => .of (X.residueField η.1.1)
  let σ := sigmaSpec R
  let eSigma := asIso σ
  let W := Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U
  let eW : W.toScheme ≅ Spec (.of (∀ η : I, X.residueField η.1.1)) :=
    (genericPreimageIsoSigma X U).symm ≪≫ eSigma
  have : IsIso eW.inv.appTop := by
    show IsIso (eW.inv.app ⊤)
    infer_instance
  show (W.topIso.symm ≪≫ asIso eW.inv.appTop ≪≫
      Scheme.ΓSpecIso (.of (∀ η : I, X.residueField η.1.1))).hom ≫
        CommRingCat.ofHom (Pi.evalRingHom _ η) = _
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    ← Scheme.ΓSpecIso_naturality]
  have hgeom :
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom
          (fun η : I => X.residueField η.1.1) η)) ≫ eW.inv =
        Sigma.ι (fun η : I => Spec (.of (X.residueField η.1.1))) η ≫
          (genericPreimageIsoSigma X U).hom := by
    show Spec.map (CommRingCat.ofHom (Pi.evalRingHom
        (fun η : I => X.residueField η.1.1) η)) ≫
      eSigma.inv ≫ (genericPreimageIsoSigma X U).hom = _
    rw [← ι_sigmaSpec R η]
    have hcancel : sigmaSpec R ≫ eSigma.inv = 𝟙 _ := IsIso.hom_inv_id σ
    calc
      _ = Sigma.ι (fun i : I => Spec (R i)) η ≫
          (sigmaSpec R ≫ eSigma.inv) ≫
            (genericPreimageIsoSigma X U).hom := by
        simp only [Category.assoc]
        rfl
      _ = _ := by
        rw [hcancel]
        simp only [Category.id_comp, R]
  calc
    _ = W.topIso.inv ≫
        (Spec.map (CommRingCat.ofHom (Pi.evalRingHom
          (fun η : I => X.residueField η.1.1) η)) ≫ eW.inv).appTop ≫
            (Scheme.ΓSpecIso (X.residueField η.1.1)).hom := by
      rw [Scheme.Hom.comp_appTop]
      simp only [Category.assoc]
      rfl
    _ = _ := by rw [hgeom]

/-- Pulling sections over `U` back along the generic-point morphism and projecting onto one factor
is evaluation at the corresponding generic point. -/
lemma genericPreimageSectionsRingEquiv_comp_app
    (X : Scheme.{u}) (U : X.Opens)
    [Finite {η : genericPoints X // η.1 ∈ U}]
    (η : {η : genericPoints X // η.1 ∈ U}) :
    (Scheme.fromGenericPointResidueFields X).app U ≫
        CommRingCat.ofHom (genericPreimageSectionsRingEquiv X U).toRingHom ≫
          CommRingCat.ofHom
            (Pi.evalRingHom (fun η : {η : genericPoints X // η.1 ∈ U} =>
              X.residueField η.1.1) η) =
      X.evaluation U η.1.1 η.2 := by
  classical
  let f := Scheme.fromGenericPointResidueFields X
  let W := f ⁻¹ᵁ U
  let m : Spec (.of (X.residueField η.1.1)) ⟶ W.toScheme :=
    Sigma.ι (fun η : {η : genericPoints X // η.1 ∈ U} =>
      Spec (.of (X.residueField η.1.1))) η ≫ (genericPreimageIsoSigma X U).hom
  have hm : m ≫ W.ι ≫ f = X.fromSpecResidueField η.1.1 :=
    genericPreimageIsoSigma_ι_comp X U η
  have hle : ⊤ ≤ (m ≫ W.ι ≫ f) ⁻¹ᵁ U := by
    rw [hm]
    intro y _
    show X.fromSpecResidueField η.1.1 y ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    exact η.2
  rw [genericPreimageSectionsRingEquiv_eval_component X U η]
  show f.app U ≫ W.topIso.inv ≫ m.appTop ≫
      (Scheme.ΓSpecIso (X.residueField η.1.1)).hom = _
  have hle' : ⊤ ≤ (X.fromSpecResidueField η.1.1) ⁻¹ᵁ U := by
    simpa only [hm] using hle
  calc
    _ = (f.app U ≫ W.topIso.inv ≫ m.appTop) ≫
        (Scheme.ΓSpecIso (X.residueField η.1.1)).hom := by rfl
    _ = (m ≫ W.ι ≫ f).appLE U ⊤ hle ≫
        (Scheme.ΓSpecIso (X.residueField η.1.1)).hom := by
      rw [app_comp_preimage_topIso_inv_appTop f U m hle]
    _ = X.evaluation U η.1.1 η.2 := by
      simpa only [hm] using fromSpecResidueField_appLE_eval X U η.1.1 η.2 hle'

/-- For a reduced scheme, the sections of the generic-point residue spectrum over the preimage of
an affine open form the total ring of fractions of the ring of sections of that open. -/
noncomputable def genericPreimageSectionsAlgEquivFractionRing
    {X : Scheme.{u}} [IsReduced X] (U : X.Opens) (hU : IsAffineOpen U)
    [Finite {η : genericPoints X // η.1 ∈ U}] :
    letI := (Scheme.fromGenericPointResidueFields X).app U |>.hom.toAlgebra
    Γ(Scheme.genericPointResidueSpectrum X,
      Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
        FractionRing Γ(X, U) := by
  classical
  let I := {η : genericPoints X // η.1 ∈ U}
  let R := Γ(X, U)
  let S := Γ(Scheme.genericPointResidueSpectrum X,
    Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U)
  letI : _root_.IsReduced R := IsReduced.component_reduced U
  letI : Algebra R S :=
    (Scheme.fromGenericPointResidueFields X).app U |>.hom.toAlgebra
  let eI := genericPointsInOpenEquivMinimalPrimes hU
  let q : I → Ideal R := fun η => (eI η : Ideal R)
  letI (η : I) : (q η).IsPrime := (eI η).property.left.left
  letI (η : I) : Algebra R (X.residueField η.1.1) :=
    (X.evaluation U η.1.1 η.2).hom.toAlgebra
  letI (η : I) : IsLocalization.AtPrime (X.residueField η.1.1) (q η) := by
    simpa only [q, eI, genericPointsInOpenEquivMinimalPrimes_asIdeal hU η] using
      residueField_isLocalizationAtPrime hU η
  let eS : S ≃+* (∀ η : I, X.residueField η.1.1) :=
    genericPreimageSectionsRingEquiv X U
  let eSA : S ≃ₐ[R] (∀ η : I, X.residueField η.1.1) :=
    AlgEquiv.ofRingEquiv (f := eS) fun r ↦ funext fun η ↦
      congrArg (fun k : Γ(X, U) ⟶ X.residueField η.1.1 => k r)
        (genericPreimageSectionsRingEquiv_comp_app X U η)
  let eL : (∀ η : I, X.residueField η.1.1) ≃ₐ[R]
      (∀ η : I, Localization.AtPrime (q η)) :=
    AlgEquiv.piCongrRight (fun η =>
      IsLocalization.algEquiv (q η).primeCompl (X.residueField η.1.1)
        (Localization.AtPrime (q η)))
  letI : IsLocalization (nonZeroDivisors R)
      (∀ η : I, Localization.AtPrime (q η)) :=
    isLocalization_pi_localization_atPrime q
      (fun η => (eI η).property)
      (fun η ξ h => eI.injective (Subtype.ext h))
      (fun p hp ↦ (eI.surjective ⟨p, hp⟩).imp fun _ hη ↦ congrArg Subtype.val hη)
  let eQ : FractionRing R ≃ₐ[R] (∀ η : I, Localization.AtPrime (q η)) :=
    IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R)
      (∀ η : I, Localization.AtPrime (q η))
  exact (eQ.trans (eSA.trans eL).symm).symm

/-- Transport of the integral closure in an algebra along an isomorphism of the base ring. -/
noncomputable def integralClosureRingEquivOfBaseRingEquiv
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A S] [Algebra R S] (e : A ≃+* R)
    (h : (algebraMap R S).comp e.toRingHom = algebraMap A S) :
    integralClosure R S ≃+* integralClosure A S :=
  { toFun := fun x => ⟨x.1, (RingEquiv.isIntegral_iff e h x.1).mpr x.2⟩
    invFun := fun x => ⟨x.1, (RingEquiv.isIntegral_iff e h x.1).mp x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- A ring presenting an affine open, through a chosen isomorphism from its spectrum, is the ring
of sections of that open. -/
noncomputable def affineOpenCoordinateRingEquiv
    {X : Scheme.{u}} {A : Type u} [CommRing A]
    (U : X.Opens) (e : Spec (.of A) ≅ U.toScheme) :
    A ≃+* Γ(X, U) := by
  haveI : IsIso e.inv.appTop := by
    change IsIso (e.inv.app ⊤)
    infer_instance
  exact ((Scheme.ΓSpecIso (.of A)).symm ≪≫ asIso e.inv.appTop ≪≫
    U.topIso).commRingCatIsoToRingEquiv

/-- The spectrum map of `AlgebraicGeometry.affineOpenCoordinateRingEquiv` is the chosen
isomorphism composed with the canonical one of the affine open. -/
lemma affineOpenCoordinateRingEquiv_specMap
    {X : Scheme.{u}} {A : Type u} [CommRing A]
    (U : X.Opens) (hU : IsAffineOpen U)
    (e : Spec (.of A) ≅ U.toScheme) :
    Spec.map (CommRingCat.ofHom (affineOpenCoordinateRingEquiv U e).toRingHom) =
      hU.isoSpec.inv ≫ e.inv := by
  rw [← cancel_epi hU.isoSpec.hom]
  simp only [Iso.hom_inv_id_assoc]
  have heR : CommRingCat.ofHom (affineOpenCoordinateRingEquiv U e).toRingHom =
      (Scheme.ΓSpecIso (.of A)).inv ≫ e.inv.appTop ≫ U.topIso.hom := by
    rfl
  rw [heR]
  have : IsAffine U.toScheme := hU
  show (U.toScheme.isoSpec.hom ≫ Spec.map U.topIso.inv) ≫
    Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ e.inv.appTop ≫ U.topIso.hom) = e.inv
  simp only [Spec.map_comp, Category.assoc]
  simp only [← Spec.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Spec.map_comp]
  rw [← Category.assoc, Scheme.isoSpec_hom_naturality e.inv]
  simp [Scheme.isoSpec_Spec_hom]

/-- For a reduced scheme, the sections of the generic-point residue spectrum over the preimage of
an affine open form the total ring of fractions of a ring presenting that open. -/
noncomputable def genericPreimageSectionsRingEquivFractionRingAffine
    {X : Scheme.{u}} [IsReduced X] {A : Type u} [CommRing A]
    (U : X.Opens) (hU : IsAffineOpen U)
    (e : Spec (.of A) ≅ U.toScheme)
    [Finite {η : genericPoints X // η.1 ∈ U}] :
    Γ(Scheme.genericPointResidueSpectrum X,
      Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) ≃+* FractionRing A := by
  letI : Algebra Γ(X, U)
      Γ(Scheme.genericPointResidueSpectrum X,
        Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) :=
    (Scheme.fromGenericPointResidueFields X).app U |>.hom.toAlgebra
  let eR := affineOpenCoordinateRingEquiv U e
  let eS := genericPreimageSectionsAlgEquivFractionRing U hU
  let eQ : FractionRing Γ(X, U) ≃+* FractionRing A :=
    IsFractionRing.ringEquivOfRingEquiv eR.symm
  exact eS.toRingEquiv.trans eQ

/-- The identification `AlgebraicGeometry.genericPreimageSectionsRingEquivFractionRingAffine`
is one of algebras over the ring presenting the affine open. -/
lemma genericPreimageSectionsRingEquivFractionRingAffine_commutes
    {X : Scheme.{u}} [IsReduced X] {A : Type u} [CommRing A]
    (U : X.Opens) (hU : IsAffineOpen U)
    (e : Spec (.of A) ≅ U.toScheme)
    [Finite {η : genericPoints X // η.1 ∈ U}] (a : A) :
    (genericPreimageSectionsRingEquivFractionRingAffine U hU e)
        ((Scheme.fromGenericPointResidueFields X).app U
          ((affineOpenCoordinateRingEquiv U e) a)) =
      algebraMap A (FractionRing A) a := by
  let eR := affineOpenCoordinateRingEquiv U e
  let : Algebra Γ(X, U)
      Γ(Scheme.genericPointResidueSpectrum X,
        Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) :=
    (Scheme.fromGenericPointResidueFields X).app U |>.hom.toAlgebra
  let eS := genericPreimageSectionsAlgEquivFractionRing U hU
  let eQ : FractionRing Γ(X, U) ≃+* FractionRing A :=
    IsFractionRing.ringEquivOfRingEquiv eR.symm
  unfold genericPreimageSectionsRingEquivFractionRingAffine
  show eQ (eS ((Scheme.fromGenericPointResidueFields X).app U (eR a))) = _
  show eQ (eS (algebraMap Γ(X, U)
    Γ(Scheme.genericPointResidueSpectrum X,
      Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) (eR a))) = _
  rw [eS.commutes]
  simp [eQ]

/-- The relative normalization of a quasi-compact, quasi-separated morphism over an affine open is
the spectrum of the integral closure of the ring of sections of that open in the ring of
sections of its preimage. -/
noncomputable def relativeNormalizationPreimageIso
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    (f.fromNormalization ⁻¹ᵁ U).toScheme ≅
      Spec (.of (integralClosure Γ(X, U) Γ(Y, f ⁻¹ᵁ U))) := by
  letI : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  exact (hU.preimage f.fromNormalization).isoSpec ≪≫
    Scheme.Spec.mapIso (f.normalizationObjIso hU).symm.op

/-- Under `AlgebraicGeometry.relativeNormalizationPreimageIso`, the structural morphism of the
relative normalization is the spectrum map of the inclusion into the integral closure. -/
lemma relativeNormalizationPreimageIso_comp
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    (relativeNormalizationPreimageIso f U hU).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, U) (integralClosure Γ(X, U) Γ(Y, f ⁻¹ᵁ U)))) =
      (f.fromNormalization ∣_ U) ≫ hU.isoSpec.hom := by
  let : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  dsimp [relativeNormalizationPreimageIso]
  simp only [IsAffineOpen.isoSpec_hom]
  rw [← Scheme.Opens.toSpecΓ_naturality f.fromNormalization U, f.fromNormalization_app hU,
    Spec.map_comp]
  rfl

/-- The identification of the normalization over an affine open with the spectrum of the
integral closure of its coordinate ring in its total ring of fractions. -/
noncomputable def preimageNormalizationIsoSpecIntegralClosure
    {X : Scheme.{u}} [IsReduced X]
    (hX : ∀ V : X.Opens,
      IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {A : Type u} [CommRing A] (U : X.Opens)
    (e : Spec (.of A) ≅ U.toScheme) :
    (Scheme.normalization X hX ⁻¹ᵁ U).toScheme ≅
      Spec (.of (integralClosure A (FractionRing A))) := by
  classical
  let f := Scheme.fromGenericPointResidueFields X
  letI : QuasiCompact f := Scheme.quasiCompactFromGenericPointResidueFields X hX
  letI : QuasiSeparated f := Scheme.quasiSeparatedFromGenericPointResidueFields X
  have hU : IsAffineOpen U := IsAffine.of_isIso e.inv
  haveI : Finite (genericPoints (U : Set X)) :=
    (genericPoints.finite (hX U hU.isCompact)).to_subtype
  letI : Finite {η : genericPoints X // η.1 ∈ U} :=
    Finite.of_injective (Scheme.genericPointsInOpenEquiv X U)
      (Scheme.genericPointsInOpenEquiv X U).injective
  let R := Γ(X, U)
  let S := Γ(Scheme.genericPointResidueSpectrum X, f ⁻¹ᵁ U)
  let eR : A ≃+* R := affineOpenCoordinateRingEquiv U e
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : Algebra A S := ((f.app U).hom.comp eR.toRingHom).toAlgebra
  let eBase : integralClosure R S ≃+* integralClosure A S :=
    integralClosureRingEquivOfBaseRingEquiv eR rfl
  let eS : S ≃+* FractionRing A :=
    genericPreimageSectionsRingEquivFractionRingAffine U hU e
  let eSA : S ≃ₐ[A] FractionRing A :=
    AlgEquiv.ofRingEquiv (f := eS)
      (genericPreimageSectionsRingEquivFractionRingAffine_commutes U hU e)
  let eIntegral : integralClosure R S ≃+* integralClosure A (FractionRing A) :=
    eBase.trans eSA.mapIntegralClosure.toRingEquiv
  change (f.fromNormalization ⁻¹ᵁ U).toScheme ≅
    Spec (.of (integralClosure A (FractionRing A)))
  exact relativeNormalizationPreimageIso f U hU ≪≫
    Scheme.Spec.mapIso eIntegral.toCommRingCatIso.symm.op

/-- Under `AlgebraicGeometry.preimageNormalizationIsoSpecIntegralClosure`, the restriction of the
normalization morphism is the spectrum map induced by the inclusion into the integral closure. -/
@[stacks 035P "affine_normalization"]
theorem preimageNormalizationIsoSpecIntegralClosure_hom_comp
    {X : Scheme.{u}} [IsReduced X]
    (hX : ∀ V : X.Opens,
      IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {A : Type u} [CommRing A] (U : X.Opens)
    (e : Spec (.of A) ≅ U.toScheme) :
    (preimageNormalizationIsoSpecIntegralClosure hX U e).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap A (integralClosure A (FractionRing A)))) =
      (Scheme.normalization X hX ∣_ U) ≫ e.inv := by
  classical
  let f := Scheme.fromGenericPointResidueFields X
  let : QuasiCompact f := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let : QuasiSeparated f := Scheme.quasiSeparatedFromGenericPointResidueFields X
  have hU : IsAffineOpen U := IsAffine.of_isIso e.inv
  have : Finite (genericPoints (U : Set X)) :=
    (genericPoints.finite (hX U hU.isCompact)).to_subtype
  let : Finite {η : genericPoints X // η.1 ∈ U} :=
    Finite.of_injective (Scheme.genericPointsInOpenEquiv X U)
      (Scheme.genericPointsInOpenEquiv X U).injective
  let R := Γ(X, U)
  let S := Γ(Scheme.genericPointResidueSpectrum X, f ⁻¹ᵁ U)
  let eR : A ≃+* R := affineOpenCoordinateRingEquiv U e
  let : Algebra R S := (f.app U).hom.toAlgebra
  let : Algebra A S := ((f.app U).hom.comp eR.toRingHom).toAlgebra
  let eBase : integralClosure R S ≃+* integralClosure A S :=
    integralClosureRingEquivOfBaseRingEquiv eR rfl
  let eS : S ≃+* FractionRing A :=
    genericPreimageSectionsRingEquivFractionRingAffine U hU e
  let eSA : S ≃ₐ[A] FractionRing A :=
    AlgEquiv.ofRingEquiv (f := eS)
      (genericPreimageSectionsRingEquivFractionRingAffine_commutes U hU e)
  let eIntegral : integralClosure R S ≃+* integralClosure A (FractionRing A) :=
    eBase.trans eSA.mapIntegralClosure.toRingEquiv
  have he :
      CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))) ≫
        eIntegral.symm.toCommRingCatIso.hom =
      eR.toCommRingCatIso.hom ≫
        CommRingCat.ofHom (algebraMap R (integralClosure R S)) := by
    ext a
    have hEq : eIntegral.symm
        (algebraMap A (integralClosure A (FractionRing A)) a) =
          algebraMap R (integralClosure R S) (eR a) := eIntegral.injective <| by
      rw [eIntegral.apply_symm_apply]
      exact Subtype.ext (eSA.commutes a).symm
    exact congrArg Subtype.val hEq
  show (relativeNormalizationPreimageIso f U hU ≪≫
      Scheme.Spec.mapIso eIntegral.toCommRingCatIso.symm.op).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap A (integralClosure A (FractionRing A)))) =
      (f.fromNormalization ∣_ U) ≫ e.inv
  show ((relativeNormalizationPreimageIso f U hU).hom ≫
      Spec.map eIntegral.symm.toCommRingCatIso.hom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap A (integralClosure A (FractionRing A)))) =
      (f.fromNormalization ∣_ U) ≫ e.inv
  rw [Category.assoc, ← Spec.map_comp, he, Spec.map_comp, ← Category.assoc,
    relativeNormalizationPreimageIso_comp f U hU]
  show (f.fromNormalization ∣_ U ≫ hU.isoSpec.hom) ≫
    Spec.map (CommRingCat.ofHom (affineOpenCoordinateRingEquiv U e).toRingHom) =
      (f.fromNormalization ∣_ U) ≫ e.inv
  rw [affineOpenCoordinateRingEquiv_specMap U hU e]
  simp

end AlgebraicGeometry
