module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SpecOver
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeCriterionCounterexample
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfCompletedLocalRing

/-!
# Morphisms from spectra of local rings into the local ring of a scheme

This file collects the dictionary used to read morphisms `Spec L ⟶ V` of the big fppf site, with
`L` a local ring, as maps of local rings out of the local ring `𝒪_{V,v}`, together with the facts
about the truncations `L ⧸ 𝔪ⁿ⁺¹` and about residue fields of schemes étale over an algebraically
closed field which the flatness of the contraction in Stacks 0D5E needs.

## Main results

* `AlgebraicGeometry.exists_eq_SpecMap_comp_fromSpecStalk` and
  `AlgebraicGeometry.SpecMap_comp_fromSpecStalk_injective`: a morphism from the spectrum of a
  local ring sending the closed point to `v` is `Spec` of exactly one local map out of `𝒪_{V,v}`.
* `AlgebraicGeometry.surjective_of_etale_of_isAlgClosed`: a field map `k → L` with `k`
  algebraically closed whose spectrum factors through a scheme étale over `Spec k`, by a
  morphism surjective on the local ring, is surjective.
* `AlgebraicGeometry.Space.fromSpecStalk_comp_str`: over an affine base, the composite
  `Spec 𝒪_{V,v} ⟶ V ⟶ S` is `Spec` of the structure map `Γ(S) ⟶ 𝒪_{V,v}`.
* `AlgebraicGeometry.Space.exists_specOverHom_eq`: every morphism of the site between spectra of
  `Γ(S)`-algebras is `Spec` of a map of `Γ(S)`-algebras.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Truncations of a local ring -/

section Truncation

variable {L : Type u} [CommRing L] [IsLocalRing L]

/-- The quotient of a local ring by a power `𝔪ⁿ⁺¹` of its maximal ideal is local. -/
instance isLocalRing_quotient_maximalIdeal_pow (n : ℕ) :
    IsLocalRing (L ⧸ maximalIdeal L ^ (n + 1)) :=
  have : Nontrivial (L ⧸ maximalIdeal L ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal L).ne_top (Ideal.pow_le_self (by omega)))
  .of_surjective' _ Ideal.Quotient.mk_surjective

/-- A prime ideal of `L ⧸ 𝔪ⁿ⁺¹` pulls back to the maximal ideal of `L`. -/
theorem comap_mk_eq_maximalIdeal_of_isPrime (n : ℕ) (p : Ideal (L ⧸ maximalIdeal L ^ (n + 1)))
    [hp : p.IsPrime] : p.comap (Ideal.Quotient.mk _) = maximalIdeal L := by
  have hle : maximalIdeal L ≤ p.comap (Ideal.Quotient.mk _) := by
    intro x hx
    refine (hp.comap (Ideal.Quotient.mk _)).mem_of_pow_mem (n + 1) ?_
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hx _)]
    exact p.zero_mem
  exact ((maximalIdeal.isMaximal L).eq_of_le (hp.comap (Ideal.Quotient.mk _)).ne_top hle).symm

/-- Every point of `Spec (L ⧸ 𝔪ⁿ⁺¹)` maps to the closed point of `Spec L`. -/
theorem SpecMap_quotient_mk_apply (n : ℕ) (y : Spec (.of (L ⧸ maximalIdeal L ^ (n + 1)))) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal L ^ (n + 1)))) y =
      closedPoint L :=
  PrimeSpectrum.ext (comap_mk_eq_maximalIdeal_of_isPrime n y.asIdeal (hp := y.isPrime))

/-- `Spec (L ⧸ 𝔪ⁿ⁺¹)` has a single point. -/
theorem eq_of_mem_Spec_quotient_pow (n : ℕ) (y y' : Spec (.of (L ⧸ maximalIdeal L ^ (n + 1)))) :
    y = y' := by
  refine PrimeSpectrum.ext ?_
  rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective y.asIdeal,
    ← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective y'.asIdeal,
    comap_mk_eq_maximalIdeal_of_isPrime n y.asIdeal (hp := y.isPrime),
    comap_mk_eq_maximalIdeal_of_isPrime n y'.asIdeal (hp := y'.isPrime)]

/-- Every ring map from `L ⧸ 𝔪ⁿ⁺¹` to a nontrivial ring is local: a non-unit of `L ⧸ 𝔪ⁿ⁺¹` is
nilpotent. -/
theorem isLocalHom_of_quotient_pow (n : ℕ) {M : Type*} [CommRing M] [Nontrivial M]
    (f : L ⧸ maximalIdeal L ^ (n + 1) →+* M) : IsLocalHom f := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  by_contra hb
  have hbm : b ∈ maximalIdeal L := fun hu => hb (hu.map _)
  have h0 : (Ideal.Quotient.mk (maximalIdeal L ^ (n + 1)) b) ^ (n + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hbm _
  have := ha.pow (n + 1)
  rw [← map_pow, h0, map_zero] at this
  exact not_isUnit_zero this

/-- The maximal ideal of `L ⧸ 𝔪ⁿ⁺¹` has vanishing `(n + 1)`-st power. -/
theorem maximalIdeal_quotient_pow_pow_eq_bot (n : ℕ) :
    maximalIdeal (L ⧸ maximalIdeal L ^ (n + 1)) ^ (n + 1) = ⊥ := by
  have hle : maximalIdeal (L ⧸ maximalIdeal L ^ (n + 1)) ≤
      (maximalIdeal L).map (Ideal.Quotient.mk (maximalIdeal L ^ (n + 1))) := by
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Ideal.mem_map_of_mem _ fun hb => hx (hb.map _)
  rw [eq_bot_iff, ← Ideal.map_quotient_self (maximalIdeal L ^ (n + 1)), Ideal.map_pow]
  exact Ideal.pow_right_mono hle _

/-- A local ring map from a local ring `A` to `L ⧸ 𝔪ⁿ⁺¹` kills `𝔪_Aⁿ⁺¹`. -/
theorem map_eq_zero_of_mem_maximalIdeal_pow {A : Type*} [CommRing A] [IsLocalRing A] (n : ℕ)
    (f : A →+* L ⧸ maximalIdeal L ^ (n + 1)) [IsLocalHom f] {a : A}
    (ha : a ∈ maximalIdeal A ^ (n + 1)) : f a = 0 := by
  have h : (maximalIdeal A ^ (n + 1)).map f = ⊥ := by
    rw [Ideal.map_pow, eq_bot_iff, ← maximalIdeal_quotient_pow_pow_eq_bot n]
    exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le f) _
  exact (Ideal.mem_bot).1 (h ▸ Ideal.mem_map_of_mem f ha)

end Truncation

/-! ### Morphisms from the spectrum of a local ring -/

section LocalRing

variable {X : Scheme.{u}}

/-- A morphism from the spectrum of a local ring sending the closed point to `x` is `Spec` of a
local map `𝒪_{X,x} ⟶ L` followed by `Spec 𝒪_{X,x} ⟶ X`. -/
theorem exists_eq_SpecMap_comp_fromSpecStalk {L : CommRingCat.{u}} [IsLocalRing L]
    (f : Spec L ⟶ X) {x : X} (hx : f (closedPoint L) = x) :
    ∃ φ : X.presheaf.stalk x ⟶ L, IsLocalHom φ.hom ∧ Spec.map φ ≫ X.fromSpecStalk x = f := by
  subst hx
  exact ⟨Scheme.stalkClosedPointTo f, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

/-- Two local maps `𝒪_{X,x} ⟶ L` inducing the same morphism `Spec L ⟶ X` agree. -/
theorem SpecMap_comp_fromSpecStalk_injective {L : CommRingCat.{u}} [IsLocalRing L] {x : X}
    (φ φ' : X.presheaf.stalk x ⟶ L) [IsLocalHom φ.hom] [IsLocalHom φ'.hom]
    (h : Spec.map φ ≫ X.fromSpecStalk x = Spec.map φ' ≫ X.fromSpecStalk x) : φ = φ' := by
  have h' := (SpecToEquivOfLocalRing X L).symm.injective
    (show (SpecToEquivOfLocalRing X L).symm ⟨x, φ, inferInstance⟩ =
      (SpecToEquivOfLocalRing X L).symm ⟨x, φ', inferInstance⟩ from h)
  have := eq_of_heq (Sigma.mk.inj h').2
  exact congrArg Subtype.val this

/-- If `φ : 𝒪_{X,x} ⟶ L` is surjective, so is the map of local rings induced at the closed point
by `Spec φ` followed by `Spec 𝒪_{X,x} ⟶ X`. -/
theorem surjective_stalkClosedPointTo_SpecMap_comp {L : CommRingCat.{u}} [IsLocalRing L] {x : X}
    (φ : X.presheaf.stalk x ⟶ L) [IsLocalHom φ.hom] (hφ : Function.Surjective φ) :
    Function.Surjective (Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x)) := by
  have h := (SpecToEquivOfLocalRing X L).apply_symm_apply ⟨x, φ, inferInstance⟩
  obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.1 h
  change Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = _ at h₂
  have key : ∀ {A B : CommRingCat.{u}} (i : A ≅ B) (ψ : B ⟶ L), Function.Surjective ψ →
      Function.Surjective (i.hom ≫ ψ) := by
    intro A B i ψ hψ z
    obtain ⟨w, rfl⟩ := hψ z
    exact ⟨i.inv w, by simp⟩
  rw [h₂]
  exact key _ _ hφ

/-- **A field map out of an algebraically closed field factoring through an étale scheme is
surjective.** Let `θ : k → L` be a map of fields with `k` algebraically closed, and suppose that
`Spec θ` factors as `Spec L ⟶ E ⟶ Spec k` with `E ⟶ Spec k` étale, the first factor inducing
a surjection on the local ring at the image of the closed point. Then `θ` is surjective: the
residue field of `E` there is `k`, since it is a separable algebraic extension of `k`. -/
theorem surjective_of_etale_of_isAlgClosed {k L : Type u} [Field k] [IsAlgClosed k] [Field L]
    (θ : k →+* L) {E : Scheme.{u}} (q : E ⟶ Spec (.of k)) [Etale q]
    (ℓ : Spec (.of L) ⟶ E) (hℓ : ℓ ≫ q = Spec.map (CommRingCat.ofHom θ))
    (hsurj : Function.Surjective (Scheme.stalkClosedPointTo ℓ)) : Function.Surjective θ := by
  set e := ℓ (closedPoint L) with he
  have : (q e).asIdeal.IsPrime := (q e).isPrime
  have : IsAlgClosed ((Spec (.of k)).residueField (q e)) :=
    isAlgClosed_residueField_of_etale (𝟙 _) (q e)
  let : Algebra ((Spec (.of k)).residueField (q e)) (E.residueField e) :=
    (q.residueFieldMap e).hom.toAlgebra
  have hbij : Function.Bijective (q.residueFieldMap e) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := (Spec (.of k)).residueField (q e)) (K := E.residueField e)
  -- the residue field of `Spec k` at its point is reached by global sections
  have hev : Function.Surjective
      ((Spec (.of k)).presheaf.germ ⊤ (q e) trivial ≫ (Spec (.of k)).residue (q e)) := by
    have hp : (q e).asIdeal.IsMaximal := by
      simpa [(q e).asIdeal.eq_bot_of_prime] using Ideal.bot_isMaximal
    have h := Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) (q e)
    intro w
    obtain ⟨c, hc⟩ := (q e).asIdeal.algebraMap_residueField_surjective
      ((Scheme.Spec.residueFieldIso (.of k) (q e)).hom w)
    refine ⟨(Scheme.ΓSpecIso (.of k)).inv c, ?_⟩
    have h' := congrArg (fun g => g c) h
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at h'
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [← h', hc]
    exact (Scheme.Spec.residueFieldIso (.of k) (q e)).hom_inv_id_apply w
  -- the composite through `q` is `θ` on global sections
  have hθ : ∀ f : Spec (.of L) ⟶ Spec (.of k), f = Spec.map (CommRingCat.ofHom θ) →
      (Spec (.of k)).presheaf.germ ⊤ (f (closedPoint L)) trivial ≫
        Scheme.stalkClosedPointTo f = (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom θ := by
    rintro f rfl
    exact Scheme.germ_stalkClosedPointTo_Spec _
  intro y
  obtain ⟨z, rfl⟩ := hsurj y
  obtain ⟨w, hw⟩ := hbij.2 (E.residue e z)
  obtain ⟨c, rfl⟩ := hev w
  refine ⟨(Scheme.ΓSpecIso (.of k)).hom c, ?_⟩
  have hcomp := Scheme.stalkClosedPointTo_comp ℓ q
  have h1 := congrArg (fun g => g c) (hθ (ℓ ≫ q) hℓ)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at h1
  rw [← h1, hcomp]
  dsimp only
  -- `z` and the image of `c` agree modulo the maximal ideal of `𝒪_{E,e}`
  have hres := congrArg (fun g => g ((Spec (.of k)).presheaf.germ ⊤ (q e) trivial c))
    (Scheme.residue_residueFieldMap (f := q) e)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hres hw
  rw [hw] at hres
  have hmem : q.stalkMap e ((Spec (.of k)).presheaf.germ ⊤ (q e) trivial c) - z ∈
      maximalIdeal (E.presheaf.stalk e) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hres.symm
  have hd : Scheme.stalkClosedPointTo ℓ
      (q.stalkMap e ((Spec (.of k)).presheaf.germ ⊤ (q e) trivial c) - z) = 0 := by
    by_contra hne
    exact (mem_maximalIdeal _).1 hmem
      (isUnit_of_map_unit (Scheme.stalkClosedPointTo ℓ).hom _ (isUnit_iff_ne_zero.2 hne))
  rw [map_sub, sub_eq_zero] at hd
  exact hd

end LocalRing

/-! ### Spectra of `Γ(S)`-algebras as objects of the site over an affine `S` -/

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsAffine S]

/-- The spectrum of a quotient of a ring whose spectrum lies in the site lies in the site. -/
theorem contains_spec_quotient {L : Type u} [CommRing L] (hL : B.Contains (Spec (.of L)))
    (J : Ideal L) : B.Contains (Spec (.of (L ⧸ J))) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hL
    ((Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (le_max_right _ _))

/-- The structure map `Γ(S) ⟶ 𝒪_{V,v}` of the local ring of an object `V` of the site at a
point. -/
def chartStalkStructureMap (V : BigFppfOver B S hS) (v : (BigFppfOver.toScheme B S hS).obj V) :
    Γ(S, ⊤) ⟶ ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v :=
  (B.inclusion.map V.hom).appTop ≫
    ((BigFppfOver.toScheme B S hS).obj V).presheaf.germ ⊤ v trivial

/-- Over an affine base, `Spec 𝒪_{V,v} ⟶ V ⟶ S` is `Spec` of the structure map
`Γ(S) ⟶ 𝒪_{V,v}` followed by `Spec Γ(S) ≅ S`. -/
theorem fromSpecStalk_comp_str (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    ((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v ≫ B.inclusion.map V.hom =
      Spec.map (chartStalkStructureMap V v) ≫ S.isoSpec.inv := by
  rw [← cancel_mono S.isoSpec.hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  change _ ≫ _ ≫ S.toSpecΓ = _
  rw [Scheme.toSpecΓ_naturality, Scheme.fromSpecStalk_toSpecΓ_assoc, chartStalkStructureMap,
    Spec.map_comp]

/-- A morphism of schemes from the spectrum of a `Γ(S)`-algebra to an object `V` of the site,
lying over `S`, as a morphism of the site. -/
def homOfSpec (V : BigFppfOver B S hS) {L : Type u} [CommRing L] [Algebra Γ(S, ⊤) L]
    (hL : B.Contains (Spec (.of L))) (g : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (hg : g ≫ B.inclusion.map V.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) L)) ≫ S.isoSpec.inv) :
    specOver B S hS S.isoSpec.inv L hL ⟶ V :=
  Over.homMk (ObjectProperty.homMk g) (ObjectProperty.hom_ext _ hg)

/-- The underlying morphism of schemes of `homOfSpec`. -/
@[simp]
theorem toScheme_map_homOfSpec (V : BigFppfOver B S hS) {L : Type u} [CommRing L]
    [Algebra Γ(S, ⊤) L] (hL : B.Contains (Spec (.of L)))
    (g : Spec (.of L) ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (hg : g ≫ B.inclusion.map V.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) L)) ≫ S.isoSpec.inv) :
    (BigFppfOver.toScheme B S hS).map (homOfSpec V hL g hg) = g := rfl

/-- A morphism of the site from the spectrum of a `Γ(S)`-algebra `L` lies over `S`. -/
theorem toScheme_map_comp_str {V : BigFppfOver B S hS} {L : Type u} [CommRing L]
    [Algebra Γ(S, ⊤) L] {hL : B.Contains (Spec (.of L))}
    (w : specOver B S hS S.isoSpec.inv L hL ⟶ V) :
    (BigFppfOver.toScheme B S hS).map w ≫ B.inclusion.map V.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) L)) ≫ S.isoSpec.inv :=
  congrArg (fun k => k.hom) (Over.w w)

/-- Every morphism of the site between spectra of `Γ(S)`-algebras is `Spec` of a map of
`Γ(S)`-algebras. -/
theorem exists_specOverHom_eq {R R' : Type u} [CommRing R] [CommRing R'] [Algebra Γ(S, ⊤) R]
    [Algebra Γ(S, ⊤) R'] {hR : B.Contains (Spec (.of R))} {hR' : B.Contains (Spec (.of R'))}
    (w : specOver B S hS S.isoSpec.inv R' hR' ⟶ specOver B S hS S.isoSpec.inv R hR) :
    ∃ q : R →ₐ[Γ(S, ⊤)] R', specOverHom B S hS S.isoSpec.inv hR hR' q = w := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of R' :=
    Spec.preimage ((BigFppfOver.toScheme B S hS).map w)
  have hφ : Spec.map φ = (BigFppfOver.toScheme B S hS).map w := Spec.map_preimage _
  have h := toScheme_map_comp_str w
  change _ ≫ Spec.map _ ≫ S.isoSpec.inv = _ at h
  rw [← Category.assoc, cancel_mono, ← hφ, ← Spec.map_comp] at h
  have hcomm : φ.hom.comp (algebraMap Γ(S, ⊤) R) = algebraMap Γ(S, ⊤) R' :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  refine ⟨{ φ.hom with commutes' := fun a => RingHom.congr_fun hcomm a }, ?_⟩
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [toScheme_map_specOverHom, ← hφ]
  rfl

/-- A map `φ : 𝒪_{V,v} ⟶ L` whose spectrum, followed by `Spec 𝒪_{V,v} ⟶ V`, lies over `S`
through the structure map of `L`, is a map of `Γ(S)`-algebras. -/
theorem chartStalkStructureMap_comp_eq {V : BigFppfOver B S hS}
    {v : (BigFppfOver.toScheme B S hS).obj V} {L : Type u} [CommRing L] [Algebra Γ(S, ⊤) L]
    (φ : ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v ⟶ CommRingCat.of L)
    (h : Spec.map φ ≫ ((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v ≫
        B.inclusion.map V.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) L)) ≫ S.isoSpec.inv) :
    chartStalkStructureMap V v ≫ φ = CommRingCat.ofHom (algebraMap Γ(S, ⊤) L) := by
  rw [fromSpecStalk_comp_str, ← Category.assoc, ← Spec.map_comp, cancel_mono] at h
  exact Spec.map_injective h

end Space

end AlgebraicGeometry

end
