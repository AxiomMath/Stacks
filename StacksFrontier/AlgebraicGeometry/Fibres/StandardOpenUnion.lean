module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksCore.Tactic.StacksAttribute

/-!
# Scheme-theoretic closure of a finite union of standard opens

For a finite union of standard opens in an affine scheme, its scheme-theoretic closure is the
closed subscheme cut out by the kernel of the map to the product of the corresponding
localizations. The union is quasi-compact, and it is scheme-theoretically dense exactly when
that kernel vanishes.

The last of these is the dictionary that turns scheme-theoretic density of a finite union of
standard opens into an injectivity statement about rings, which is the form in which Stacks
0573 and Stacks 05KP use it.

## Main definitions

* `Stacks.Morphisms.standardOpenUnion` is the union of the standard opens determined by a
  finite family.
* `Stacks.Morphisms.localizationKernel` is the kernel of the map to the product of
  localizations.

## Main results

* `Stacks.Morphisms.schemeTheoreticImage_iso_quotient` identifies the closure as a closed
  subscheme over the original affine scheme.
* `Stacks.Morphisms.quasiCompact_standardOpenUnion` gives quasi-compactness of the inclusion.
* `Stacks.Morphisms.schemeTheoreticallyDense_iff_localizationKernel_eq_bot` is the density
  criterion.

## Implementation notes

The scheme-theoretic closure is the scheme-theoretic image of the canonical open immersion.
Its identification with the quotient spectrum is expressed by an isomorphism commuting with
both canonical maps to `Spec A`.

Scheme-theoretic density is the library's
`AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense` of Stacks 01RB, part (2).

The family is indexed by an arbitrary type, finite only where finiteness is used; the source
states the example for a finite list of elements.

## References

* [Stacks Project, Tag 056C](https://stacks.math.columbia.edu/tag/056C)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Morphisms

variable {A : Type u} [CommRing A] {ι : Type*}

/-- The union of the standard opens `D(fᵢ)` in `Spec A`. -/
public def standardOpenUnion (f : ι → A) : (Spec (.of A)).Opens :=
  ⨆ i, PrimeSpectrum.basicOpen (f i)

/-- The kernel of `A → ∏ i, A_{fᵢ}`. -/
public def localizationKernel (f : ι → A) : Ideal A :=
  RingHom.ker (RingHom.pi (fun i => algebraMap A (Localization.Away (f i))))

private lemma standardOpenUnion_eq_affineBasicOpen {f : ι → A} :
    standardOpenUnion f = ⨆ i, (Spec (.of A)).basicOpen
      ((Scheme.ΓSpecIso (.of A)).inv (f i)) := by
  ext x
  simp [standardOpenUnion]

private lemma restriction_map_from_standardOpenUnion {f : ι → A} (i : ι) :
    (Scheme.ΓSpecIso (.of A)).inv ≫ (standardOpenUnion f).ι.appTop ≫
        (standardOpenUnion f).toScheme.presheaf.map
          (homOfLE (show ((standardOpenUnion f).ι ⁻¹ᵁ
            (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv (f i))) ≤ ⊤ from le_top)).op =
      (Scheme.ΓSpecIso (.of A)).inv ≫ (Spec (.of A)).presheaf.map
        (homOfLE (show (standardOpenUnion f).ι ''ᵁ
          ((standardOpenUnion f).ι ⁻¹ᵁ
            (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv (f i))) ≤ ⊤
              from le_top)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.toScheme_presheaf_map]
  congr 2

private lemma sections_ext_of_restrictions {f : ι → A}
    {s t : Γ(standardOpenUnion f, ⊤)}
    (h : ∀ i, (standardOpenUnion f).toScheme.presheaf.map
      (homOfLE (show ((standardOpenUnion f).ι ⁻¹ᵁ
        (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv (f i))) ≤ ⊤ from le_top)).op s =
        (standardOpenUnion f).toScheme.presheaf.map
      (homOfLE (show ((standardOpenUnion f).ι ⁻¹ᵁ
        (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv (f i))) ≤ ⊤ from le_top)).op t) :
    s = t := by
  let U : (Spec (.of A)).Opens := standardOpenUnion f
  apply U.toScheme.IsSheaf.section_ext
  intro x hx
  have hxU : x.1 ∈ standardOpenUnion f := x.2
  rw [standardOpenUnion_eq_affineBasicOpen, TopologicalSpace.Opens.mem_iSup] at hxU
  obtain ⟨i, hi⟩ := hxU
  have hxV : x ∈ U.ι ⁻¹ᵁ
      (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv (f i)) := hi
  exact ⟨_, le_top, hxV, h i⟩

private def standardOpenUnionBasicOpenImage (f : ι → A) (i : ι) :
    (Spec (.of A)).Opens :=
  (standardOpenUnion f).ι ''ᵁ ((standardOpenUnion f).ι ⁻¹ᵁ
    (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv (f i)))

private lemma kernel_restriction_basicOpen {f : ι → A} (i : ι) :
    RingHom.ker (((Scheme.ΓSpecIso (.of A)).inv ≫
      (Spec (.of A)).presheaf.map
        (homOfLE (show standardOpenUnionBasicOpenImage f i ≤ ⊤ from le_top)).op).hom) =
      RingHom.ker (algebraMap A (Localization.Away (f i))) := by
  let X : Scheme := Spec (.of A)
  let hA : A ≃+* Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  have hA_map : (hA : A →+* Γ(X, ⊤)) = (Scheme.ΓSpecIso (.of A)).inv.hom := rfl
  let r : Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv).hom (f i)
  have hAr : hA (f i) = r := congrArg (fun φ : A →+* Γ(X, ⊤) => φ (f i)) hA_map
  have hDU : X.basicOpen r ≤ standardOpenUnion f := by
    rw [standardOpenUnion_eq_affineBasicOpen]
    exact le_iSup (fun j => X.basicOpen ((Scheme.ΓSpecIso (.of A)).inv (f j))) i
  have hW : standardOpenUnionBasicOpenImage f i = X.basicOpen r := by
    dsimp [standardOpenUnionBasicOpenImage]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hDU
  let : Algebra Γ(X, ⊤) Γ(X, standardOpenUnionBasicOpenImage f i) :=
    (X.presheaf.map (homOfLE
      (show standardOpenUnionBasicOpenImage f i ≤ ⊤ from le_top)).op).hom.toAlgebra
  let : IsLocalization.Away r Γ(X, standardOpenUnionBasicOpenImage f i) :=
    (isAffineOpen_top X).isLocalization_of_eq_basicOpen r
      (homOfLE (show standardOpenUnionBasicOpenImage f i ≤ ⊤ from le_top)) hW
  have H : Submonoid.map hA.toMonoidHom (Submonoid.powers (f i)) =
      Submonoid.powers r := by
    rw [Submonoid.map_powers]
    simp [hAr]
  let e : Localization.Away (f i) ≃+* Γ(X, standardOpenUnionBasicOpenImage f i) :=
    IsLocalization.ringEquivOfRingEquiv (Localization.Away (f i))
      (Γ(X, standardOpenUnionBasicOpenImage f i)) hA H
  ext a
  simp only [RingHom.mem_ker]
  have heq : e (algebraMap A (Localization.Away (f i)) a) =
      (((Scheme.ΓSpecIso (.of A)).inv ≫
        X.presheaf.map
          (homOfLE (show standardOpenUnionBasicOpenImage f i ≤ ⊤ from le_top)).op).hom a) := by
    rw [IsLocalization.ringEquivOfRingEquiv_eq H a, CommRingCat.hom_comp]
    exact congrArg (fun b => (X.presheaf.map
      (homOfLE (show standardOpenUnionBasicOpenImage f i ≤ ⊤ from le_top)).op).hom b)
      (congrArg (fun φ : A →+* Γ(X, ⊤) => φ a) hA_map)
  rw [← heq]
  simp

/-- Restricting the image of `a` in the global sections of the union to `D(fᵢ)` gives zero
exactly when `a` vanishes in `A_{fᵢ}`. -/
private lemma restriction_eq_zero_iff {f : ι → A} (i : ι) (a : A) :
    (standardOpenUnion f).toScheme.presheaf.map
      (homOfLE (show ((standardOpenUnion f).ι ⁻¹ᵁ
        (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv (f i))) ≤ ⊤ from le_top)).op
      (((Scheme.ΓSpecIso (.of A)).inv ≫ (standardOpenUnion f).ι.appTop).hom a) = 0 ↔
    algebraMap A (Localization.Away (f i)) a = 0 := by
  rw [← RingHom.mem_ker (f := algebraMap A (Localization.Away (f i))),
    ← kernel_restriction_basicOpen i, RingHom.mem_ker]
  exact iff_of_eq (congrArg (· = 0)
    (congrArg (fun φ => φ.hom a) (restriction_map_from_standardOpenUnion (f := f) i)))

private lemma kernel_restriction_standardOpenUnion {f : ι → A} :
    RingHom.ker (((Scheme.ΓSpecIso (.of A)).inv ≫
      (standardOpenUnion f).ι.appTop).hom) = localizationKernel f := by
  ext a
  simp only [RingHom.mem_ker, localizationKernel]
  constructor
  · intro ha
    funext i
    exact (restriction_eq_zero_iff i a).1 (by rw [ha, map_zero])
  · intro hpi
    apply sections_ext_of_restrictions (f := f)
    intro i
    rw [map_zero]
    exact (restriction_eq_zero_iff i a).2 (congrFun hpi i)

/-- The scheme-theoretic closure of the finite union of standard opens is the
closed subscheme `Spec (A/I)`, with its canonical map to `Spec A`. -/
@[stacks 056C "scheme-theoretic closure"]
public theorem schemeTheoreticImage_iso_quotient [Finite ι] (f : ι → A) :
    ∃ e : (standardOpenUnion f).ι.image ≅ Spec (.of (A ⧸ localizationKernel f)),
      (standardOpenUnion f).ι.imageι =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (localizationKernel f))) := by
  let X : Scheme := Spec (.of A)
  let j : (standardOpenUnion f).toScheme ⟶ X := (standardOpenUnion f).ι
  let I : Ideal A := localizationKernel f
  let q : Spec (.of (A ⧸ I)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let eA : A ≃+* Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  let eQ : A ⧸ I ≃+* Γ(Spec (.of (A ⧸ I)), ⊤) :=
    (Scheme.ΓSpecIso (.of (A ⧸ I))).commRingCatIsoToRingEquiv.symm
  have hqker : RingHom.ker (((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop).hom) = I := by
    show RingHom.ker (((Scheme.ΓSpecIso (.of A)).inv ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop).hom) = I
    rw [← Scheme.ΓSpecIso_inv_naturality]
    show RingHom.ker (eQ.toRingHom.comp (Ideal.Quotient.mk I)) = I
    rw [RingHom.ker_equiv_comp, Ideal.mk_ker]
  have hcompKer : RingHom.ker (j.appTop.hom.comp eA.toRingHom) =
      RingHom.ker (q.appTop.hom.comp eA.toRingHom) := by
    show RingHom.ker (((Scheme.ΓSpecIso (.of A)).inv ≫ j.appTop).hom) =
      RingHom.ker (((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop).hom)
    rw [kernel_restriction_standardOpenUnion (f := f), hqker]
  have htopKer : RingHom.ker j.appTop.hom = RingHom.ker q.appTop.hom := by
    apply Ideal.comap_injective_of_surjective eA.toRingHom eA.surjective
    simpa only [RingHom.comap_ker] using hcompKer
  have hker : j.ker = q.ker := by
    rw [Scheme.ker_of_isAffine j, Scheme.ker_of_isAffine q, htopKer]
  let e₀ : j.image ≅ q.image := {
    hom := Scheme.IdealSheafData.inclusion hker.ge
    inv := Scheme.IdealSheafData.inclusion hker.le
    hom_inv_id := by
      rw [Scheme.IdealSheafData.inclusion_comp hker.le hker.ge]
      simp
    inv_hom_id := by
      rw [Scheme.IdealSheafData.inclusion_comp hker.ge hker.le]
      simp }
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let e₁ : q.image ≅ Spec (.of (A ⧸ I)) := (asIso q.toImage).symm
  have hqfactor : e₁.hom ≫ q = q.imageι := by
    calc
      e₁.hom ≫ q = e₁.hom ≫ (q.toImage ≫ q.imageι) := by
        rw [q.toImage_imageι]
      _ = q.imageι := by simp [e₁]
  refine ⟨e₀ ≪≫ e₁, ?_⟩
  calc
    j.imageι = e₀.hom ≫ q.imageι := (Scheme.IdealSheafData.inclusion_subschemeι hker.ge).symm
    _ = e₀.hom ≫ e₁.hom ≫ q := by rw [← hqfactor]
    _ = (e₀ ≪≫ e₁).hom ≫ q := by simp [Category.assoc]

/-- The inclusion of a finite union of standard opens is quasi-compact. -/
@[stacks 056C "quasi-compactness"]
public theorem quasiCompact_standardOpenUnion [Finite ι] (f : ι → A) :
    QuasiCompact (standardOpenUnion f).ι := by
  apply quasiCompact_iff_isSpectralMap.mpr
  show IsSpectralMap (Subtype.val :
    ↥(standardOpenUnion f : Set (Spec (.of A))) → Spec (.of A))
  apply IsRetrocompact_iff_isSpectralMap_subtypeVal.mp
  have hcompact : IsCompact (standardOpenUnion f : Set (Spec (.of A))) := by
    rw [standardOpenUnion_eq_affineBasicOpen, TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun i => by
      rw [basicOpen_eq_of_affine]
      exact PrimeSpectrum.isCompact_basicOpen (f i)
  exact hcompact.isRetrocompact (standardOpenUnion f).isOpen

/-- A finite union of standard opens is scheme-theoretically dense precisely
when the canonical map to the product of localizations is injective. -/
@[stacks 056C "scheme-theoretic density"]
public theorem schemeTheoreticallyDense_iff_localizationKernel_eq_bot [Finite ι]
    (f : ι → A) :
    AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense (standardOpenUnion f) ↔
      localizationKernel f = ⊥ := by
  have := quasiCompact_standardOpenUnion f
  let eA : A ≃+* Γ(Spec (.of A), ⊤) :=
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  have hcomp : RingHom.ker (((Scheme.ΓSpecIso (.of A)).inv ≫
        (standardOpenUnion f).ι.appTop).hom) = ⊥ ↔
      RingHom.ker (standardOpenUnion f).ι.appTop.hom = ⊥ := by
    rw [← RingHom.injective_iff_ker_eq_bot, ← RingHom.injective_iff_ker_eq_bot]
    refine ⟨fun h x y hxy => ?_, fun h => h.comp eA.injective⟩
    have hxy' : (standardOpenUnion f).ι.appTop.hom (eA (eA.symm x)) =
        (standardOpenUnion f).ι.appTop.hom (eA (eA.symm y)) := by simpa using hxy
    simpa using congrArg eA (h hxy')
  have hdom : IsSchemeTheoreticallyDominant (standardOpenUnion f).ι ↔
      RingHom.ker (standardOpenUnion f).ι.appTop.hom = ⊥ := by
    rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine (standardOpenUnion f).ι]
    refine ⟨fun h => ?_, fun h => Scheme.IdealSheafData.ext_of_isAffine (by simpa using h)⟩
    simpa using congrArg (fun J : Scheme.IdealSheafData (Spec (.of A)) =>
      J.ideal ⟨⊤, isAffineOpen_top _⟩) h
  rw [Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant, hdom, ← hcomp,
    kernel_restriction_standardOpenUnion]

end Stacks.Morphisms
