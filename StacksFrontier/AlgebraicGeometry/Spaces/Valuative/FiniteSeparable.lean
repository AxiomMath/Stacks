module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Finite separable extensions in the existence valuative criterion

For a morphism of algebraic spaces over a scheme, the existence half of the valuative
criterion may be tested using only dominating extensions whose extension of fraction fields
is finite separable.

In one direction this is a restriction of the quantifier and so is immediate. The other
direction is the content: given an arbitrary dominating extension with a lift, one pulls
the lift back to an etale atlas of the source, picks a point of the atlas above the closed
point of the valuation ring and a generalization of it above the generic point, and takes
the residue field there. That residue field is finite separable over the original fraction
field because the atlas is etale, and a valuation ring of it dominating the stalk of the
pullback supplies the required dominating extension.

## Main definitions

* `AlgebraicGeometry.Space.ExistenceFiniteSeparable` is the existence half of the valuative
  criterion with the dominating extension of fraction fields required to be finite
  separable.

## Main results

* `AlgebraicGeometry.Space.valuativeCriterion_existence_iff_finiteSeparable` identifies the
  unrestricted and the finite separable forms of the existence criterion.

## Implementation notes

The finite separable extension is the homomorphism of fraction fields belonging to the
dominating extension of a valuative square; its finiteness and separability are measured
using the algebra structure that homomorphism induces. Both source and target are assumed
to be algebraic spaces on the same site.

## References

* [Stacks Project, Tag 03KH](https://stacks.math.columbia.edu/tag/03KH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The fraction field of a domain `R` is the function field of `Spec R`. -/
private noncomputable def fractionRingEquivSpecFunctionField
    (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : K ≃+* (Spec (.of R)).functionField := by
  let A := CommRingCat.of R
  letI : Algebra A (Spec A).functionField := RingHom.toAlgebra <| by
    apply CommRingCat.Hom.hom
    apply StructureSheaf.toStalk
  letI : IsFractionRing A (Spec A).functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine A
  let f : K →+* (Spec A).functionField :=
    IsFractionRing.lift (IsFractionRing.injective A (Spec A).functionField)
  let g : (Spec A).functionField →+* K :=
    IsFractionRing.lift (IsFractionRing.injective A K)
  have hgf : g.comp f = RingHom.id K := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro r
    simp [f, g]
  have hfg : f.comp g = RingHom.id (Spec A).functionField := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro r
    simp [f, g]
  exact RingEquiv.ofRingHom f g hfg hgf

/-- A field is its own residue field as a local ring. -/
private noncomputable def fieldEquivResidueField (K : Type u) [Field K] :
    K ≃+* IsLocalRing.ResidueField K :=
  RingEquiv.ofBijective (IsLocalRing.residue K)
    ⟨(IsLocalRing.residue K).injective, Ideal.Quotient.mk_surjective⟩

/-- A field is the residue field of `Spec` of itself at the closed point. -/
private noncomputable def specClosedResidueFieldEquiv (K : Type u) [Field K] :
    K ≃+* (Spec (.of K)).residueField (IsLocalRing.closedPoint K) := by
  let c : Spec (.of K) := IsLocalRing.closedPoint K
  letI : c.asIdeal.IsPrime := c.isPrime
  exact c.asIdeal.algEquivResidueFieldOfField.toRingEquiv.trans
    (Scheme.Spec.residueFieldIso (.of K) c).commRingCatIsoToRingEquiv.symm

/-- The canonical morphism from the spectrum of a residue field is quasi-compact, its
source being a one-point scheme. -/
@[ega "IV 3.2.9" "partial"]
private instance fromSpecResidueField_quasiCompact
    {X : Scheme.{u}} (x : X) : QuasiCompact (X.fromSpecResidueField x) :=
  quasiCompact_iff_forall_isAffineOpen.mpr fun V _ =>
    (Set.toFinite (X.fromSpecResidueField x ⁻¹' (V : Set X))).isCompact

/-- The existence valuative criterion with a finite separable extension of
the original fraction field. -/
public def ExistenceFiniteSeparable
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∀ q : ValuativeSquare f,
    ∃ e : q.DominatingExtension,
      (letI := e.fieldMap.toAlgebra
       Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
      Nonempty e.square.Lift

/-- A point over the generic point of `Spec R` has a residue field receiving the fraction field
of `R`, compatibly with the canonical morphisms. -/
private theorem exists_fromSpecResidueField_comp_eq (R K : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] {Z : Scheme.{u}} (φ : Z ⟶ Spec (.of R))
    {z : Z} (hz : φ z = genericPoint (Spec (.of R))) :
    ∃ k : K →+* Z.residueField z, Z.fromSpecResidueField z ≫ φ =
      Spec.map (CommRingCat.ofHom k) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  let A := CommRingCat.of R
  let : Algebra A (Spec A).functionField := RingHom.toAlgebra <| by
    apply CommRingCat.Hom.hom
    apply StructureSheaf.toStalk
  let : IsFractionRing A (Spec A).functionField := functionField_isFractionRing_of_affine A
  let k₀ : K →+* (Spec (.of R)).residueField (genericPoint (Spec (.of R))) :=
    (fieldEquivResidueField ((Spec (.of R)).functionField)).toRingHom.comp
      (fractionRingEquivSpecFunctionField R K).toRingHom
  have hk₀ : Spec.map (CommRingCat.ofHom k₀) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) =
      (Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Scheme.fromSpecResidueField,
      Spec.fromSpecStalk_eq']
    refine Eq.trans ?_ (Spec.map_comp _ _)
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext r
    change IsLocalRing.residue ((Spec (.of R)).functionField)
        ((fractionRingEquivSpecFunctionField R K).toRingHom (algebraMap R K r)) =
      IsLocalRing.residue ((Spec (.of R)).functionField)
        (algebraMap R ((Spec (.of R)).functionField) r)
    congr 1
    dsimp [fractionRingEquivSpecFunctionField]
    exact IsFractionRing.lift_algebraMap (IsFractionRing.injective A (Spec A).functionField) r
  refine ⟨(φ.residueFieldMap z).hom.comp
    (((Spec (.of R)).residueFieldCongr hz).inv.hom.comp k₀), ?_⟩
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := φ) z,
    ← Scheme.residueFieldCongr_fromSpecResidueField (X := Spec (.of R)) hz.symm, ← hk₀]
  repeat rw [← Spec.map_comp]
  repeat rw [← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext r
  simp [RingHom.comp_assoc]

/-- A generalizing surjective morphism to the spectrum of a local domain has a point over the
closed point specialized from a point over the generic point. -/
private theorem exists_specializes_closedPoint_genericPoint {R : Type u} [CommRing R]
    [IsDomain R] [IsLocalRing R] {Z : Scheme.{u}} (φ : Z ⟶ Spec (.of R))
    (hφ : GeneralizingMap φ) (hφs : Function.Surjective φ) :
    ∃ p p' : Z, p' ⤳ p ∧ φ p = IsLocalRing.closedPoint R ∧
      φ p' = genericPoint (Spec (.of R)) := by
  obtain ⟨p, hp⟩ := hφs (IsLocalRing.closedPoint R)
  obtain ⟨p', hp'p, hpgen⟩ := hφ (by rw [hp]; exact genericPoint_specializes _)
  exact ⟨p, p', hp'p, hp, hpgen⟩

/-- The residue field extensions of an étale morphism are finite separable. -/
private theorem finite_separable_residueFieldMap {Z V : Scheme.{u}} (φ : Z ⟶ V) [Etale φ]
    (z : Z) :
    letI := (φ.residueFieldMap z).hom.toAlgebra
    Module.Finite (V.residueField (φ z)) (Z.residueField z) ∧
      Algebra.IsSeparable (V.residueField (φ z)) (Z.residueField z) := by
  let := (φ.residueFieldMap z).hom.toAlgebra
  have hres : (φ.residueFieldMap z).hom.EssFiniteType := by
    change (IsLocalRing.ResidueField.map (φ.stalkMap z).hom).EssFiniteType
    exact RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap φ z)
  have : Algebra.EssFiniteType (V.residueField (φ z)) (Z.residueField z) :=
    RingHom.essFiniteType_algebraMap.mp hres
  have : Algebra.IsSeparable (V.residueField (φ z)) (Z.residueField z) := inferInstance
  exact ⟨Algebra.finite_of_essFiniteType_of_isAlgebraic, this⟩

/-- The identification of a field with its residue field at the closed point is the canonical
morphism from the spectrum of the residue field. -/
private theorem SpecMap_specClosedResidueFieldEquiv (K : Type u) [Field K] :
    Spec.map (CommRingCat.ofHom (specClosedResidueFieldEquiv K).toRingHom) =
      (Spec (.of K)).fromSpecResidueField (IsLocalRing.closedPoint K) := by
  have hK : CommRingCat.ofHom
      ((IsLocalRing.closedPoint K).asIdeal.algEquivResidueFieldOfField :
        K →+* (IsLocalRing.closedPoint K).asIdeal.ResidueField) =
      CommRingCat.ofHom (algebraMap K (IsLocalRing.closedPoint K).asIdeal.ResidueField) := by
    ext z
    simp [Ideal.algEquivResidueFieldOfField_apply]
  dsimp [specClosedResidueFieldEquiv]
  rw [Spec.map_comp, hK]
  exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
    (R := CommRingCat.of K) (x := IsLocalRing.closedPoint K)

/-- A residue field of a scheme étale over a field `K` is a finite separable extension of `K`,
compatibly with the canonical morphisms. -/
private theorem exists_finite_separable_residueField_of_etale {K : Type u} [Field K]
    {Z : Scheme.{u}} (φ : Z ⟶ Spec (.of K)) [Etale φ] (z : Z) :
    ∃ k : K →+* Z.residueField z, (letI := k.toAlgebra
      Module.Finite K (Z.residueField z) ∧ Algebra.IsSeparable K (Z.residueField z)) ∧
      Spec.map (CommRingCat.ofHom k) = Z.fromSpecResidueField z ≫ φ := by
  have hz : φ z = IsLocalRing.closedPoint K := by
    have hK : IsField ↑(CommRingCat.of K) := Field.toIsField K
    have : Subsingleton (Spec (.of K)) :=
      PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr hK
    exact Subsingleton.elim _ _
  let e : K ≃+* (Spec (.of K)).residueField (φ z) := (specClosedResidueFieldEquiv K).trans
    (Scheme.residueFieldCongr hz).symm.commRingCatIsoToRingEquiv
  have he : Spec.map (CommRingCat.ofHom e.toRingHom) =
      (Spec (.of K)).fromSpecResidueField (φ z) := by
    dsimp [e]
    rw [Spec.map_comp]
    change Spec.map (Scheme.residueFieldCongr hz.symm).hom ≫
      Spec.map (CommRingCat.ofHom (specClosedResidueFieldEquiv K).toRingHom) = _
    exact (congrArg (fun t => Spec.map (Scheme.residueFieldCongr hz.symm).hom ≫ t)
      (SpecMap_specClosedResidueFieldEquiv K)).trans
        (Scheme.residueFieldCongr_fromSpecResidueField hz.symm)
  let := (φ.residueFieldMap z).hom.toAlgebra
  let := ((φ.residueFieldMap z).hom.comp e.toRingHom).toAlgebra
  have hc : (algebraMap K (Z.residueField z)).comp e.symm.toRingHom =
      algebraMap ((Spec (.of K)).residueField (φ z)) (Z.residueField z) := by
    ext w
    change (φ.residueFieldMap z).hom (e (e.symm w)) = _
    rw [RingHom.algebraMap_toAlgebra]
    simp
  obtain ⟨hfin, hsep⟩ := finite_separable_residueFieldMap φ z
  refine ⟨(φ.residueFieldMap z).hom.comp e.toRingHom,
    ⟨Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl _) hc,
      Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl _) hc⟩, ?_⟩
  rw [CommRingCat.ofHom_comp, Spec.map_comp, he]
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField φ z

/-- A morphism to the spectrum of a local ring, with a point over the closed point specialized
from the image of a point `z`, factors through a valuation ring of the residue field at `z`
dominating the local ring. -/
private theorem exists_valuationSubring_factor {R : Type u} [CommRing R] [IsLocalRing R]
    {Z V : Scheme.{u}} (h : Z ⟶ V) (ψ : V ⟶ Spec (.of R)) {z : Z} {y : V} (hzy : h z ⤳ y)
    (hy : ψ y = IsLocalRing.closedPoint R) (ρ : R →+* Z.residueField z)
    (hρ : Spec.map (CommRingCat.ofHom ρ) = Z.fromSpecResidueField z ≫ h ≫ ψ) :
    ∃ (W : ValuationSubring (Z.residueField z)) (φ : R →+* W) (w : Spec (.of W) ⟶ V),
      IsLocalHom φ ∧ (algebraMap W (Z.residueField z)).comp φ = ρ ∧
      Spec.map (CommRingCat.ofHom φ) = w ≫ ψ ∧
      Spec.map (CommRingCat.ofHom (algebraMap W (Z.residueField z))) ≫ w =
        Z.fromSpecResidueField z ≫ h := by
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (V.fromSpecStalk y ≫ ψ)
  have : IsLocalHom σ.hom := by
    apply (IsLocalRing.isLocalHom_iff_comap_closedPoint σ.hom).mpr
    have h₁ := congrArg (fun g : Spec (V.presheaf.stalk y) ⟶ Spec (.of R) =>
      g (IsLocalRing.closedPoint (V.presheaf.stalk y))) hσ
    change PrimeSpectrum.comap σ.hom (IsLocalRing.closedPoint _) =
      ψ (V.fromSpecStalk y (IsLocalRing.closedPoint _)) at h₁
    rwa [Scheme.fromSpecStalk_closedPoint, hy] at h₁
  let ℓ := V.presheaf.stalkSpecializes hzy ≫ V.residue (h z) ≫ h.residueFieldMap z
  have hℓ : Spec.map ℓ ≫ V.fromSpecStalk y = Z.fromSpecResidueField z ≫ h := by
    simp only [ℓ, Spec.map_comp, Category.assoc]
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk hzy, ← Scheme.fromSpecResidueField]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField h z
  obtain ⟨W, hW, hWloc⟩ := IsLocalRing.exists_factor_valuationRing ℓ.hom
  let τ : V.presheaf.stalk y →+* W := ℓ.hom.codRestrict W hW
  have : IsLocalHom τ := hWloc
  have hτ : (algebraMap W (Z.residueField z)).comp τ = ℓ.hom := by
    ext
    rfl
  have hw : Spec.map (CommRingCat.ofHom (algebraMap W (Z.residueField z))) ≫
      Spec.map (CommRingCat.ofHom τ) ≫ V.fromSpecStalk y = Z.fromSpecResidueField z ≫ h := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ,
      CommRingCat.ofHom_hom, hℓ]
  have hφ : Spec.map (CommRingCat.ofHom (τ.comp σ.hom)) =
      Spec.map (CommRingCat.ofHom τ) ≫ V.fromSpecStalk y ≫ ψ := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hσ]
  refine ⟨W, τ.comp σ.hom, Spec.map (CommRingCat.ofHom τ) ≫ V.fromSpecStalk y,
    RingHom.isLocalHom_comp τ σ.hom, ?_, hφ.trans (Category.assoc _ _ _).symm, hw⟩
  have hcat : CommRingCat.ofHom ((algebraMap W (Z.residueField z)).comp (τ.comp σ.hom)) =
      CommRingCat.ofHom ρ := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, hφ, hρ, ← reassoc_of% hw]
  exact congrArg CommRingCat.Hom.hom hcat

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- The morphism of site objects induced by the inclusion of a ring into a field. -/
private noncomputable abbrev fracSiteHom (hS : B.Contains S) {R K : Type u} [CommRing R]
    [Field K] [Algebra R K] (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (base : Spec (.of R) ⟶ S) :
    siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
      siteObject B S hS hR base :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    B.obj hK ⟶ B.obj hR)

/-- A morphism of the big fppf category over `S` is compatible with the structure morphisms. -/
private theorem toScheme_map_comp_hom {A A' : BigFppfOver B S hS} (u : A ⟶ A') :
    (BigFppfOver.toScheme B S hS).map u ≫ B.inclusion.map A'.hom = B.inclusion.map A.hom := by
  change B.inclusion.map u.left ≫ _ = _
  rw [← B.inclusion.map_comp, Over.w]

/-- A morphism of schemes compatible with the structure morphisms comes from the big fppf
category over `S`. -/
private theorem exists_hom_of_comp_eq {A A' : BigFppfOver B S hS}
    (g : (BigFppfOver.toScheme B S hS).obj A ⟶ (BigFppfOver.toScheme B S hS).obj A')
    (hg : g ≫ B.inclusion.map A'.hom = B.inclusion.map A.hom) :
    ∃ g' : A ⟶ A', (BigFppfOver.toScheme B S hS).map g' = g :=
  ⟨Over.homMk (B.inclusion.preimage (X := A.left) (Y := A'.left) g) (B.inclusion.map_injective
    (by rw [B.inclusion.map_comp, B.inclusion.map_preimage]; exact hg)),
    B.inclusion.map_preimage _⟩

/-- The square of site objects formed by a dominating extension and the two inclusions into the
fraction fields commutes. -/
private theorem ValuativeSquare.DominatingExtension.fracSiteHom_comp_specialOver
    {q : ValuativeSquare f} (e : q.DominatingExtension) :
    fracSiteHom hS e.square.ring_mem e.square.field_mem e.square.base ≫ e.specialOver =
      e.genericOver ≫ fracSiteHom hS q.ring_mem q.field_mem q.base := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  change B.inclusion.map
      (fracSiteHom hS e.square.ring_mem e.square.field_mem e.square.base).left ≫
      B.inclusion.map e.specialOver.left =
    B.inclusion.map e.genericOver.left ≫
      B.inclusion.map (fracSiteHom hS q.ring_mem q.field_mem q.base).left
  rw [e.specialOver_left, e.genericOver_left]
  change Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) ≫
      Spec.map (CommRingCat.ofHom e.ringMap) =
    Spec.map (CommRingCat.ofHom e.fieldMap) ≫ Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    e.fraction_comm]

/-- A point of an object over the spectrum of a domain lying over the generic point is the image
of the closed point of an object mapping to the spectrum of the fraction field. -/
private theorem exists_hom_fracSiteHom_of_eq_genericPoint {R K : Type u} [CommRing R]
    [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {hR : B.Contains (Spec (.of R))}
    (hK : B.Contains (Spec (.of K))) {base : Spec (.of R) ⟶ S} {P : BigFppfOver B S hS}
    (b : P ⟶ siteObject B S hS hR base) {p : (BigFppfOver.toScheme B S hS).obj P}
    (hp : (BigFppfOver.toScheme B S hS).map b p = genericPoint (Spec (.of R))) :
    ∃ (V : BigFppfOver B S hS) (u : V ⟶ P)
      (v : V ⟶ siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base))
      (t : (BigFppfOver.toScheme B S hS).obj V),
      u ≫ b = v ≫ fracSiteHom hS hR hK base ∧ (BigFppfOver.toScheme B S hS).map u t = p := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨k, hk⟩ := exists_fromSpecResidueField_comp_eq R K (T.map b) hp
  have hk' : (T.obj P).fromSpecResidueField p ≫ T.map b =
      Spec.map (CommRingCat.ofHom k) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := hk
  let V := siteObject B S hS (BigFppfSite.residueField_spec_contains B P.left.property p)
    ((T.obj P).fromSpecResidueField p ≫ B.inclusion.map P.hom)
  obtain ⟨u, hu⟩ := exists_hom_of_comp_eq (A := V) (A' := P)
    ((T.obj P).fromSpecResidueField p) rfl
  obtain ⟨v, hv⟩ := exists_hom_of_comp_eq (A := V)
    (A' := siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base))
    (Spec.map (CommRingCat.ofHom k)) (by
      change _ = (T.obj P).fromSpecResidueField p ≫ B.inclusion.map P.hom
      rw [← toScheme_map_comp_hom b, ← Category.assoc ((T.obj P).fromSpecResidueField p), hk']
      exact (Category.assoc _ _ _).symm)
  refine ⟨V, u, v, IsLocalRing.closedPoint _,
    T.map_injective (by rw [Functor.map_comp, Functor.map_comp, hu, hv]; exact hk'), ?_⟩
  rw [hu]
  exact Scheme.fromSpecResidueField_apply p _

/-- A pair of compatible morphisms into a relatively representable morphism and its base gives a
lift to the pullback. -/
private theorem exists_lift_pullback {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U a c : BigFppfOver B S hS} {η : yoneda.obj U ⟶ Z} (hη : yoneda.relativelyRepresentable η)
    {g : yoneda.obj a ⟶ Z} (i : yoneda.obj c ⟶ yoneda.obj U) (h : c ⟶ a)
    (hi : i ≫ η = yoneda.map h ≫ g) :
    ∃ l : c ⟶ hη.pullback g, yoneda.map l ≫ hη.fst g = i ∧ l ≫ hη.snd g = h :=
  ⟨_, hη.lift_fst _ _ hi, hη.lift_snd _ _ hi⟩

/-- **Pulling a lift back to the atlas.** Given a lift `x` over a dominating extension and an
atlas `η`, some point of the pullback of `η` to the generic point of `q` maps to a generalization
of a point of the pullback of `η ≫ f` to the special point of `q` lying over the closed point. -/
private theorem exists_specializes_of_lift (q : ValuativeSquare f) (e₀ : q.DominatingExtension)
    (x : e₀.square.Lift) {U : BigFppfOver B S hS} {η : yoneda.obj U ⟶ X}
    (hηrep : yoneda.relativelyRepresentable η) (hηYrep : yoneda.relativelyRepresentable (η ≫ f))
    {p p' : (BigFppfOver.toScheme B S hS).obj (hηrep.pullback x.map)} (hp'p : p' ⤳ p)
    (hp : (BigFppfOver.toScheme B S hS).map (hηrep.snd x.map) p =
      IsLocalRing.closedPoint e₀.square.R)
    (hp' : (BigFppfOver.toScheme B S hS).map (hηrep.snd x.map) p' =
      genericPoint (Spec (.of e₀.square.R)))
    {g : hηrep.pullback q.generic ⟶ hηYrep.pullback q.special}
    (hgfst : yoneda.map g ≫ hηYrep.fst q.special = hηrep.fst q.generic)
    (hgsnd : g ≫ hηYrep.snd q.special =
      hηrep.snd q.generic ≫ fracSiteHom hS q.ring_mem q.field_mem q.base) :
    ∃ z y, (BigFppfOver.toScheme B S hS).map g z ⤳ y ∧
      (BigFppfOver.toScheme B S hS).map (hηYrep.snd q.special) y =
        IsLocalRing.closedPoint q.R := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨V, u, v, t, huv, ht⟩ :=
    exists_hom_fracSiteHom_of_eq_genericPoint e₀.square.field_mem (hηrep.snd x.map) hp'
  have hPc : hηrep.fst x.map ≫ η ≫ f =
      yoneda.map (hηrep.snd x.map ≫ e₀.specialOver) ≫ q.special := by
    rw [← Category.assoc, (hηrep.isPullback x.map).w, Category.assoc, x.special_comm,
      e₀.special_comm, Functor.map_comp, Category.assoc]
  obtain ⟨c, hc₁, hc₂⟩ := exists_lift_pullback hηYrep _ _ hPc
  have hcompat : (yoneda.map u ≫ hηrep.fst x.map) ≫ η =
      yoneda.map (v ≫ e₀.genericOver) ≫ q.generic := by
    simp only [Category.assoc, Functor.map_comp, (hηrep.isPullback x.map).w]
    rw [← yoneda.map_comp_assoc u (hηrep.snd x.map), huv, yoneda.map_comp_assoc,
      x.generic_comm, e₀.generic_comm]
  obtain ⟨d, hd₁, hd₂⟩ := exists_lift_pullback hηrep _ _ hcompat
  have hud : u ≫ c = d ≫ g := hηYrep.hom_ext (by simp [hc₁, hd₁, hgfst])
    (by simp only [Category.assoc, hc₂, hgsnd, reassoc_of% huv,
      e₀.fracSiteHom_comp_specialOver, reassoc_of% hd₂])
  refine ⟨T.map d t, T.map c p, ?_, ?_⟩
  · have h := congrArg (fun φ : T.obj V ⟶ T.obj (hηYrep.pullback q.special) => φ t)
      (congrArg T.map hud)
    change T.map c (T.map u t) = T.map g (T.map d t) at h
    rw [← h, ht]
    exact hp'p.map (T.map c).continuous
  · have h := congrArg (fun φ : T.obj (hηrep.pullback x.map) ⟶
      T.obj (siteObject B S hS q.ring_mem q.base) => φ p) (congrArg T.map hc₂)
    change T.map (hηYrep.snd q.special) (T.map c p) =
      T.map e₀.specialOver (T.map (hηrep.snd x.map) p) at h
    rw [h, hp]
    change B.inclusion.map e₀.specialOver.left (IsLocalRing.closedPoint e₀.square.R) = _
    rw [e₀.specialOver_left]
    exact (IsLocalRing.isLocalHom_iff_comap_closedPoint e₀.ringMap).mp e₀.isLocalHom

/-- A lift over a dominating valuation ring gives a dominating extension with a lift. -/
private theorem exists_dominatingExtension_of_lift (q : ValuativeSquare f)
    {W L : Type u} [CommRing W] [IsDomain W] [ValuationRing W] [Field L] [Algebra W L]
    [IsFractionRing W L] (hW : B.Contains (Spec (.of W))) (hL : B.Contains (Spec (.of L)))
    (φ : q.R →+* W) [IsLocalHom φ] (k : q.K →+* L)
    (hk : letI := k.toAlgebra; Module.Finite q.K L ∧ Algebra.IsSeparable q.K L)
    (hφk : (algebraMap W L).comp φ = k.comp (algebraMap q.R q.K))
    (sO : siteObject B S hS hW (Spec.map (CommRingCat.ofHom φ) ≫ q.base) ⟶
      siteObject B S hS q.ring_mem q.base)
    (hsO : B.inclusion.map sO.left = Spec.map (CommRingCat.ofHom φ))
    (gO : siteObject B S hS hL (Spec.map (CommRingCat.ofHom (algebraMap W L)) ≫
        Spec.map (CommRingCat.ofHom φ) ≫ q.base) ⟶
      siteObject B S hS q.field_mem (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))
    (hgO : B.inclusion.map gO.left = Spec.map (CommRingCat.ofHom k))
    (m : yoneda.obj (siteObject B S hS hW (Spec.map (CommRingCat.ofHom φ) ≫ q.base)) ⟶ X)
    (hm : m ≫ f = yoneda.map sO ≫ q.special)
    (hm' : yoneda.map (fracSiteHom hS hW hL (Spec.map (CommRingCat.ofHom φ) ≫ q.base)) ≫ m =
      yoneda.map gO ≫ q.generic) :
    ∃ e : q.DominatingExtension, (letI := e.fieldMap.toAlgebra
      Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
      Nonempty e.square.Lift := by
  let q' : ValuativeSquare f :=
    { R := W, K := L, ring_mem := hW, field_mem := hL
      base := Spec.map (CommRingCat.ofHom φ) ≫ q.base
      generic := yoneda.map (fracSiteHom hS hW hL _) ≫ m
      special := yoneda.map sO ≫ q.special
      comm := by rw [Category.assoc, hm] }
  let e : q.DominatingExtension :=
    { square := q'
      ringMap := φ
      fieldMap := k
      isLocalHom := inferInstance
      fraction_comm := hφk
      base_comm := rfl
      genericOver := gO
      genericOver_left := hgO
      specialOver := sO
      specialOver_left := hsO
      generic_comm := hm'
      special_comm := rfl }
  exact ⟨e, hk, ⟨{ map := m, generic_comm := rfl, special_comm := hm }⟩⟩

/-- **Assembling the dominating extension.** A valuation ring `W` of the residue field at a
point `z` of the pullback of `η` to the generic point of `q`, through which the pullback of
`η ≫ f` to the special point of `q` is reached, gives a dominating extension with a lift. -/
private theorem exists_finiteSeparable_lift_of_valuationSubring (q : ValuativeSquare f)
    {U : BigFppfOver B S hS} {η : yoneda.obj U ⟶ X} (hηrep : yoneda.relativelyRepresentable η)
    (hηYrep : yoneda.relativelyRepresentable (η ≫ f))
    {g : hηrep.pullback q.generic ⟶ hηYrep.pullback q.special}
    (hgfst : yoneda.map g ≫ hηYrep.fst q.special = hηrep.fst q.generic)
    {z : (BigFppfOver.toScheme B S hS).obj (hηrep.pullback q.generic)}
    {W : ValuationSubring
      (((BigFppfOver.toScheme B S hS).obj (hηrep.pullback q.generic)).residueField z)}
    (φ : q.R →+* W) [IsLocalHom φ]
    (k : q.K →+* ((BigFppfOver.toScheme B S hS).obj (hηrep.pullback q.generic)).residueField z)
    (hk : letI := k.toAlgebra
      Module.Finite q.K
        (((BigFppfOver.toScheme B S hS).obj (hηrep.pullback q.generic)).residueField z) ∧
      Algebra.IsSeparable q.K
        (((BigFppfOver.toScheme B S hS).obj (hηrep.pullback q.generic)).residueField z))
    (hφk : (algebraMap W
      (((BigFppfOver.toScheme B S hS).obj (hηrep.pullback q.generic)).residueField z)).comp φ =
        k.comp (algebraMap q.R q.K))
    (w : Spec (.of W) ⟶ (BigFppfOver.toScheme B S hS).obj (hηYrep.pullback q.special))
    (hwT : w ≫ (BigFppfOver.toScheme B S hS).map (hηYrep.snd q.special) =
      Spec.map (CommRingCat.ofHom φ))
    (hw : Spec.map (CommRingCat.ofHom
        (algebraMap W
          (((BigFppfOver.toScheme B S hS).obj (hηrep.pullback q.generic)).residueField z))) ≫ w =
      ((BigFppfOver.toScheme B S hS).obj (hηrep.pullback q.generic)).fromSpecResidueField z ≫
        (BigFppfOver.toScheme B S hS).map g)
    (hkT : ((BigFppfOver.toScheme B S hS).obj (hηrep.pullback q.generic)).fromSpecResidueField z ≫
        (BigFppfOver.toScheme B S hS).map (hηrep.snd q.generic) =
      Spec.map (CommRingCat.ofHom k)) :
    ∃ e : q.DominatingExtension, (letI := e.fieldMap.toAlgebra
      Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
      Nonempty e.square.Lift := by
  let T := BigFppfOver.toScheme B S hS
  have hL : B.Contains (Spec (.of ((T.obj (hηrep.pullback q.generic)).residueField z))) :=
    BigFppfSite.residueField_spec_contains B (hηrep.pullback q.generic).left.property z
  have hW : B.Contains (Spec (.of W)) := Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit hL ((Cardinal.mk_le_of_injective
      (f := fun w : W => (w : (T.obj (hηrep.pullback q.generic)).residueField z))
      Subtype.val_injective).trans (le_max_right _ _))
  obtain ⟨sO, hsO⟩ := exists_hom_of_comp_eq
    (A := siteObject B S hS hW (Spec.map (CommRingCat.ofHom φ) ≫ q.base))
    (A' := siteObject B S hS q.ring_mem q.base) (Spec.map (CommRingCat.ofHom φ)) rfl
  have hkφ : Spec.map (CommRingCat.ofHom k) ≫ Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap W ((T.obj (hηrep.pullback q.generic)).residueField z))) ≫
        Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hφk]
  obtain ⟨gO, hgO⟩ := exists_hom_of_comp_eq
    (A := siteObject B S hS hL (Spec.map (CommRingCat.ofHom
      (algebraMap W ((T.obj (hηrep.pullback q.generic)).residueField z))) ≫
        Spec.map (CommRingCat.ofHom φ) ≫ q.base))
    (A' := siteObject B S hS q.field_mem (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫
      q.base)) (Spec.map (CommRingCat.ofHom k)) ((reassoc_of% hkφ) q.base)
  obtain ⟨wP, hwP⟩ := exists_hom_of_comp_eq
    (A := siteObject B S hS hW (Spec.map (CommRingCat.ofHom φ) ≫ q.base)) w (by
      rw [← toScheme_map_comp_hom (hηYrep.snd q.special), ← Category.assoc, hwT]
      rfl)
  obtain ⟨gG, hgG⟩ := exists_hom_of_comp_eq (A := siteObject B S hS hL
    (Spec.map (CommRingCat.ofHom
      (algebraMap W ((T.obj (hηrep.pullback q.generic)).residueField z))) ≫
        Spec.map (CommRingCat.ofHom φ) ≫ q.base))
    ((T.obj _).fromSpecResidueField z) (by
      rw [← toScheme_map_comp_hom (hηrep.snd q.generic)]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) hkT).trans ((reassoc_of% hkφ) q.base)))
  have hwsnd : wP ≫ hηYrep.snd q.special = sO :=
    T.map_injective (by rw [Functor.map_comp, hwP, hsO]; exact hwT)
  have hgGO : gG ≫ hηrep.snd q.generic = gO :=
    T.map_injective (by rw [Functor.map_comp, hgG, hgO]; exact hkT)
  have hfrac : fracSiteHom hS hW hL (Spec.map (CommRingCat.ofHom φ) ≫ q.base) ≫ wP = gG ≫ g :=
    T.map_injective (by rw [Functor.map_comp, Functor.map_comp, hwP, hgG]; exact hw)
  refine exists_dominatingExtension_of_lift q hW hL φ k hk hφk sO hsO gO hgO
    (yoneda.map wP ≫ hηYrep.fst q.special ≫ η) ?_ ?_
  · rw [Category.assoc, Category.assoc, (hηYrep.isPullback q.special).w, ← hwsnd,
      Functor.map_comp, Category.assoc]
  · rw [← Functor.map_comp_assoc, hfrac, Functor.map_comp_assoc, reassoc_of% hgfst,
      (hηrep.isPullback q.generic).w, ← Functor.map_comp_assoc, hgGO]

/-- **The finite separable dominating extension.** A point `z` of the pullback of an étale atlas
`η` to the generic point of `q`, mapping to a generalization of a point over the closed point,
gives a dominating extension with fraction field the residue field at `z`, and a lift. -/
private theorem exists_finiteSeparable_lift_of_specializes (q : ValuativeSquare f)
    {U : BigFppfOver B S hS} {η : yoneda.obj U ⟶ X} (hηrep : yoneda.relativelyRepresentable η)
    (hηYrep : yoneda.relativelyRepresentable (η ≫ f))
    [Etale ((BigFppfOver.toScheme B S hS).map (hηrep.snd q.generic))]
    {g : hηrep.pullback q.generic ⟶ hηYrep.pullback q.special}
    (hgfst : yoneda.map g ≫ hηYrep.fst q.special = hηrep.fst q.generic)
    (hgsnd : g ≫ hηYrep.snd q.special =
      hηrep.snd q.generic ≫ fracSiteHom hS q.ring_mem q.field_mem q.base)
    (z : (BigFppfOver.toScheme B S hS).obj (hηrep.pullback q.generic))
    (y : (BigFppfOver.toScheme B S hS).obj (hηYrep.pullback q.special))
    (hzy : (BigFppfOver.toScheme B S hS).map g z ⤳ y)
    (hy : (BigFppfOver.toScheme B S hS).map (hηYrep.snd q.special) y =
      IsLocalRing.closedPoint q.R) :
    ∃ e : q.DominatingExtension, (letI := e.fieldMap.toAlgebra
      Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
      Nonempty e.square.Lift := by
  let T := BigFppfOver.toScheme B S hS
  have : @Etale (T.obj (hηrep.pullback q.generic)) (Spec (.of q.K))
      (T.map (hηrep.snd q.generic)) := ‹_›
  obtain ⟨k, hk, hkSpec⟩ :=
    exists_finite_separable_residueField_of_etale (K := q.K)
      (Z := T.obj (hηrep.pullback q.generic)) (T.map (hηrep.snd q.generic)) z
  have hkT : (T.obj _).fromSpecResidueField z ≫ T.map (hηrep.snd q.generic) =
      Spec.map (CommRingCat.ofHom k) := hkSpec.symm
  have hρ : Spec.map (CommRingCat.ofHom (k.comp (algebraMap q.R q.K))) =
      (T.obj _).fromSpecResidueField z ≫ T.map g ≫ T.map (hηYrep.snd q.special) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← hkT, Category.assoc, ← Functor.map_comp, hgsnd]
    rfl
  obtain ⟨W, φ, w, hφ, hφk, hφw, hw⟩ := exists_valuationSubring_factor (R := q.R)
    (Z := T.obj (hηrep.pullback q.generic)) (T.map g)
    (T.map (hηYrep.snd q.special)) hzy hy _ hρ
  exact exists_finiteSeparable_lift_of_valuationSubring q hηrep hηYrep hgfst φ k hk hφk w
    hφw.symm hw hkT

/-- The existence part of the valuative criterion implies its finite separable form. -/
public theorem existenceFiniteSeparable_of_existence (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (h : ValuativeCriterion.Existence f) :
    ExistenceFiniteSeparable f := by
  intro q
  obtain ⟨e₀, ⟨x⟩⟩ := h q
  obtain ⟨U, η, hsurj, hetale⟩ := hX.exists_atlas
  have hηrep : yoneda.relativelyRepresentable η :=
    Functor.relativelyRepresentable.diag_iff.mp hX.diagonal_representable η
  have hηYrep : yoneda.relativelyRepresentable (η ≫ f) :=
    Functor.relativelyRepresentable.diag_iff.mp hY.diagonal_representable (η ≫ f)
  have hb : Surjective ((BigFppfOver.toScheme B S hS).map (hηrep.snd x.map)) :=
    hsurj.property x.map _ _ (hηrep.isPullback x.map)
  have : Etale ((BigFppfOver.toScheme B S hS).map (hηrep.snd x.map)) :=
    hetale.property x.map _ _ (hηrep.isPullback x.map)
  have : Etale ((BigFppfOver.toScheme B S hS).map (hηrep.snd q.generic)) :=
    hetale.property q.generic _ _ (hηrep.isPullback q.generic)
  obtain ⟨p, p', hp'p, hp, hp'⟩ := exists_specializes_closedPoint_genericPoint
    (R := e₀.square.R) ((BigFppfOver.toScheme B S hS).map (hηrep.snd x.map))
    (Flat.generalizingMap _) hb.surj
  have hgc : hηrep.fst q.generic ≫ η ≫ f =
      yoneda.map (hηrep.snd q.generic ≫ fracSiteHom hS q.ring_mem q.field_mem q.base) ≫
        q.special := by
    rw [← Category.assoc, (hηrep.isPullback q.generic).w, Category.assoc, q.comm,
      Functor.map_comp, Category.assoc]
  obtain ⟨g, hgfst, hgsnd⟩ := exists_lift_pullback hηYrep _ _ hgc
  obtain ⟨z, y, hzy, hy⟩ := exists_specializes_of_lift q e₀ x hηrep hηYrep hp'p hp hp' hgfst hgsnd
  exact exists_finiteSeparable_lift_of_specializes q hηrep hηYrep hgfst hgsnd z y hzy hy

end Site

/-- Allowing arbitrary field extensions in the existence valuative criterion
is equivalent to allowing only finite separable ones. -/
@[stacks 03KH]
public theorem valuativeCriterion_existence_iff_finiteSeparable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    ValuativeCriterion.Existence f ↔ ExistenceFiniteSeparable f :=
  ⟨existenceFiniteSeparable_of_existence hX hY, fun h q => (h q).imp fun _ hfs => hfs.2⟩

end AlgebraicGeometry.Space

end
