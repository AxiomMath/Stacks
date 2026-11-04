module

public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.Extraction

/-!
# Versality at a point of the category of Stacks Example 98.12.8 implies smoothness

Let `𝒳 = 𝒮_F` be the category fibred in sets of Stacks Example 98.12.8 over `S = Spec Λ`, let
`x` be an object of `𝒳` over a scheme `U` locally of finite type over `S`, and let `u₀ ∈ U` be a
point over the closed point `𝔪` with `Λ → κ(u₀)` surjective. For an affine open `Spec A ∋ u₀`
of `U`, with `𝔪_A` the kernel of `A → κ(u₀)`, versality of `x` at `u₀` gives condition (4) of
Stacks 02HT for `Λ → A` at `𝔪_A`, so `Λ → A` is smooth at `𝔪_A`.

## Main definitions

* `Deformation.Artin.GRingNecessity.testAlgebra`: the algebra structure over the local ring
  `𝒪_{S,s}` at the image `s` of `u₀` of a local `Λ`-algebra lying over `𝔪`.
* `Deformation.Artin.GRingNecessity.testObject`, `Deformation.Artin.GRingNecessity.testHom`: the
  Artinian test algebras of condition (4) of Stacks 02HT and their surjection, as objects and
  morphisms of the category of Artinian local `𝒪_{S,s}`-algebras with residue field `κ(u₀)`.
* `Deformation.Artin.GRingNecessity.testSiteObj`, `Deformation.Artin.GRingNecessity.testFibObj`:
  the spectrum of a test algebra in the site, and the object of `𝒳` over it.

## Main results

* `Deformation.Artin.GRingNecessity.lift_smallExtension_of_isVersalAt`: versality of `x` at `u₀`
  gives condition (4) of Stacks 02HT for `Λ → A` at `𝔪_A`.
* `Deformation.Artin.GRingNecessity.isSmoothAt_of_isVersalAt`: versality of `x` at `u₀` implies
  smoothness of `Λ → A` at `𝔪_A`.

## Implementation notes

Given a small extension `B' → B` of Artinian local `Λ`-algebras and `A → B` inducing an
isomorphism of residue fields, both are local over `𝔪` with residue field `Λ / 𝔪`, hence of
finite type over `Λ`, so their spectra lie in the site. They become Artinian local algebras over
the local ring `𝒪_{S,s}` with residue field identified with `κ(u₀)`, objects of `𝒳` exist over
their spectra since `Λ_𝔪^∧` maps to them, and the morphism `Spec B → U` given by `A → B` lifts
to `Spec B' → U` by versality. That lift lands in `Spec A` because `Spec B'` is local, which gives
the required `A → B'`.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 02HT](https://stacks.math.columbia.edu/tag/02HT)
-/

@[expose] public noncomputable section

namespace Deformation.Artin.GRingNecessity

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

/-! ### Test rings of condition (4) of Stacks 02HT -/

section TestRings

variable {Λ : Type u} [CommRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal] {A : Type u} [CommRing A]
  [Algebra Λ A] {K : Type u} [Field K] (ψ : A →+* K)
  (hsurj : Function.Surjective (ψ.comp (algebraMap Λ A)))
  (hker : RingHom.ker (ψ.comp (algebraMap Λ A)) = 𝔪)
  {T : Type u} [CommRing T] [IsLocalRing T] [Algebra Λ T] (g : A →ₐ[Λ] T)
  (hq : (maximalIdeal T).comap (g : A →+* T) = RingHom.ker ψ)

omit [𝔪.IsMaximal] in
include hker hq in
/-- A local `Λ`-algebra receiving `A → T` with `𝔪_T ∩ A = 𝔪_A` lies over `𝔪`. -/
theorem comap_maximalIdeal_of_comap_eq_ker :
    (maximalIdeal T).comap (algebraMap Λ T) = 𝔪 := by
  rw [← g.comp_algebraMap, ← Ideal.comap_comap, hq]
  exact (eq_comap_ker 𝔪 ψ hker).symm

/-- If `a ≡ l` modulo `𝔪_A` for `l ∈ Λ`, then `g a ≡ l` modulo `𝔪_T`. -/
private theorem sub_algebraMap_mem_maximalIdeal_of_sub_mem_ker
    (hq : (maximalIdeal T).comap (g : A →+* T) = RingHom.ker ψ) (a : A) (l : Λ)
    (hl : a - algebraMap Λ A l ∈ RingHom.ker ψ) : g a - algebraMap Λ T l ∈ maximalIdeal T := by
  rw [← g.commutes, ← map_sub]
  exact (hq ▸ hl : a - algebraMap Λ A l ∈ (maximalIdeal T).comap (g : A →+* T))

include hsurj hq in
/-- A local `Λ`-algebra receiving `A → T` with `𝔪_T ∩ A = 𝔪_A` and `κ(𝔪_A) → κ(𝔪_T)` surjective
has residue field a quotient of `Λ`. -/
theorem exists_sub_mem_maximalIdeal_of_residueField_surjective
    [(RingHom.ker ψ).IsMaximal]
    (hres : Function.Surjective (Ideal.ResidueField.mapₐ (RingHom.ker ψ) (maximalIdeal T) g
      hq.symm)) (t : T) :
    ∃ l : Λ, t - algebraMap Λ T l ∈ maximalIdeal T := by
  obtain ⟨z, hz⟩ := hres (algebraMap T (maximalIdeal T).ResidueField t)
  obtain ⟨a, rfl⟩ := Ideal.algebraMap_residueField_surjective (RingHom.ker ψ) z
  obtain ⟨l, hl⟩ := exists_sub_mem_ker ψ hsurj a
  refine ⟨l, ?_⟩
  have hz' : algebraMap T (maximalIdeal T).ResidueField (g a) =
      algebraMap T (maximalIdeal T).ResidueField t :=
    (Ideal.ResidueField.map_algebraMap (RingHom.ker ψ) (maximalIdeal T) (g : A →+* T) hq.symm
      a).symm.trans hz
  have h1 : t - g a ∈ maximalIdeal T := by
    rwa [eq_comm, ← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero] at hz'
  exact sub_add_sub_cancel t (g a) (algebraMap Λ T l) ▸
    add_mem h1 (sub_algebraMap_mem_maximalIdeal_of_sub_mem_ker ψ g hq a l hl)

end TestRings

section TestRingsExtension

variable {Λ : Type u} [CommRing Λ] (𝔪 : Ideal Λ) {T₁ T₂ : Type u} [CommRing T₁] [IsLocalRing T₁]
  [Algebra Λ T₁] [CommRing T₂] [IsLocalRing T₂] [Algebra Λ T₂] (f : T₂ →ₐ[Λ] T₁)
  (hf : Function.Surjective f)

include hf in
/-- A surjection of local rings identifies the maximal ideal of the source with the preimage of
that of the target. -/
theorem comap_maximalIdeal_of_surjective :
    (maximalIdeal T₁).comap (f : T₂ →+* T₁) = maximalIdeal T₂ := by
  have : IsLocalHom (f : T₂ →+* T₁) := IsLocalHom.of_surjective _ hf
  exact IsLocalRing.maximalIdeal_comap _

include hf in
/-- A local `Λ`-algebra surjecting onto one lying over `𝔪` lies over `𝔪`. -/
theorem comap_maximalIdeal_of_surjective_of_comap
    (h₁ : (maximalIdeal T₁).comap (algebraMap Λ T₁) = 𝔪) :
    (maximalIdeal T₂).comap (algebraMap Λ T₂) = 𝔪 := by
  rw [← comap_maximalIdeal_of_surjective f hf, Ideal.comap_comap, f.comp_algebraMap, h₁]

include hf in
/-- A local `Λ`-algebra surjecting onto one with residue field a quotient of `Λ` has residue field
a quotient of `Λ`. -/
theorem exists_sub_mem_maximalIdeal_of_surjective
    (h₁ : ∀ t : T₁, ∃ l : Λ, t - algebraMap Λ T₁ l ∈ maximalIdeal T₁) (t : T₂) :
    ∃ l : Λ, t - algebraMap Λ T₂ l ∈ maximalIdeal T₂ := by
  obtain ⟨l, hl⟩ := h₁ (f t)
  refine ⟨l, ?_⟩
  rw [← comap_maximalIdeal_of_surjective f hf, Ideal.mem_comap]
  change f (t - algebraMap Λ T₂ l) ∈ maximalIdeal T₁
  rwa [map_sub, f.commutes]

end TestRingsExtension

/-- An Artinian local `Λ`-algebra whose residue field is a quotient of `Λ` has its spectrum in
every big fppf site containing `Spec Λ`. -/
theorem contains_spec_of_artinian {Λ : Type u} [CommRing Λ] (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of Λ))) (T : Type u) [CommRing T] [IsLocalRing T]
    [IsArtinianRing T] [Algebra Λ T]
    (hs : ∀ t : T, ∃ l : Λ, t - algebraMap Λ T l ∈ maximalIdeal T) :
    B.Contains (Spec (.of T)) := by
  have : Algebra.FiniteType Λ T := finiteType_of_residue_surjective (fun z => by
    obtain ⟨t, rfl⟩ := residue_surjective z
    obtain ⟨l, hl⟩ := hs t
    refine ⟨l, ?_⟩
    rwa [RingHom.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff])
  exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit Λ T hS

/-! ### Artinian test algebras over the local ring of `S` at the image of `u₀` -/

section TestObjects

variable {Λ : Type u} [CommRing Λ] (𝔪 : Ideal Λ) (U : Over (Spec (.of Λ)))
  (u₀ : U.left) (hsurjU : Function.Surjective (residueAlgebraMap U.hom u₀))
  (hkerU : RingHom.ker (residueAlgebraMap U.hom u₀) = 𝔪)

/-- The point of `S` at which the deformation base is localized is the image of `u₀`. -/
theorem basePoint_eq : basePoint U u₀ = U.hom u₀ :=
  (Scheme.Hom.comp_apply _ _ _).trans (congrArg U.hom (Scheme.fromSpecResidueField_apply u₀ _))

include hkerU in
/-- The prime of `Λ` under `u₀` is `𝔪`. -/
theorem basePoint_asIdeal : PrimeSpectrum.asIdeal (basePoint U u₀) = 𝔪 :=
  (congrArg PrimeSpectrum.asIdeal (basePoint_eq U u₀)).trans
    ((ker_residueAlgebraMap U.hom u₀).symm.trans hkerU)

variable {T : Type u} [CommRing T] [IsLocalRing T] [Algebra Λ T]
  (hT : (maximalIdeal T).comap (algebraMap Λ T) = 𝔪)

include hkerU hT in
/-- The elements of `Λ` outside the prime under `u₀` become units in a local `Λ`-algebra whose
maximal ideal lies over `𝔪`. -/
theorem isUnit_of_notMem_basePoint (y : Λ) (hy : y ∉ PrimeSpectrum.asIdeal (basePoint U u₀)) :
    IsUnit (algebraMap Λ T y) := by
  rw [basePoint_asIdeal 𝔪 U u₀ hkerU, ← hT] at hy
  exact IsLocalRing.notMem_maximalIdeal.mp hy

/-- The algebra structure of the local ring `𝒪_{S,s}` at the image of `u₀` on a local
`Λ`-algebra lying over `𝔪`. -/
@[instance_reducible]
def testAlgebra : Algebra ((Spec (.of Λ)).presheaf.stalk (basePoint U u₀)) T :=
  (stalkLift (basePoint U u₀) (isUnit_of_notMem_basePoint 𝔪 U u₀ hkerU hT)).toAlgebra

/-- The algebra structure `testAlgebra` extends `Λ → T`. -/
theorem testAlgebra_comp :
    letI := testAlgebra 𝔪 U u₀ hkerU hT
    (algebraMap ((Spec (.of Λ)).presheaf.stalk (basePoint U u₀)) T).comp
      (toStalkHom (basePoint U u₀)) = algebraMap Λ T :=
  stalkLift_comp_toStalkHom _ _

/-- The residue field algebra of `u₀` restricts on `Λ` to `Λ → κ(u₀)`. -/
theorem residueFieldAlgebra_comp :
    letI := residueFieldAlgebra U u₀
    (algebraMap ((Spec (.of Λ)).presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀)).comp
      (toStalkHom (basePoint U u₀)) = residueAlgebraMap U.hom u₀ :=
  stalkClosedPointTo_comp_toStalkHom _

variable [𝔪.IsMaximal] (hs : ∀ t : T, ∃ l : Λ, t - algebraMap Λ T l ∈ maximalIdeal T)

/-- The identification of the residue field of a test algebra with `κ(u₀)`, through `Λ / 𝔪`. -/
def testResidueRingEquiv : ResidueField T ≃+* U.left.residueField u₀ :=
  (quotientEquivResidueField 𝔪 T hT hs).symm.trans
    (quotientEquivResidueFieldOfPoint 𝔪 U.hom u₀ hkerU hsurjU)

/-- `testResidueRingEquiv` sends the residue of the image of `l ∈ Λ` to the image of `l` in
`κ(u₀)`. -/
theorem testResidueRingEquiv_residue (l : Λ) :
    testResidueRingEquiv 𝔪 U u₀ hsurjU hkerU hT hs (residue T (algebraMap Λ T l)) =
      residueAlgebraMap U.hom u₀ l := by
  rw [testResidueRingEquiv, RingEquiv.trans_apply, ← quotientEquivResidueField_mk 𝔪 T hT hs,
    RingEquiv.symm_apply_apply, quotientEquivResidueFieldOfPoint_mk]

/-- `testResidueRingEquiv` sends the residue of `t ≡ l` to the image of `l ∈ Λ` in `κ(u₀)`. -/
theorem testResidueRingEquiv_residue_of_sub_mem (t : T) (l : Λ)
    (hl : t - algebraMap Λ T l ∈ maximalIdeal T) :
    testResidueRingEquiv 𝔪 U u₀ hsurjU hkerU hT hs (residue T t) =
      residueAlgebraMap U.hom u₀ l := by
  rw [show residue T t = residue T (algebraMap Λ T l) by
    rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff], testResidueRingEquiv_residue]

/-- The identification of the residue field of a test algebra with `κ(u₀)`, as an algebra
isomorphism over the local ring of `S` at the image of `u₀`. -/
def testResidueEquiv :
    letI := residueFieldAlgebra U u₀
    letI := testAlgebra 𝔪 U u₀ hkerU hT
    ResidueField T ≃ₐ[(Spec (.of Λ)).presheaf.stalk (basePoint U u₀)] U.left.residueField u₀ :=
  letI := residueFieldAlgebra U u₀
  letI := testAlgebra 𝔪 U u₀ hkerU hT
  AlgEquiv.ofRingEquiv (f := testResidueRingEquiv 𝔪 U u₀ hsurjU hkerU hT hs) (fun o => by
    have h : (testResidueRingEquiv 𝔪 U u₀ hsurjU hkerU hT hs : ResidueField T →+*
        U.left.residueField u₀).comp
        (algebraMap ((Spec (.of Λ)).presheaf.stalk (basePoint U u₀)) (ResidueField T)) =
        algebraMap ((Spec (.of Λ)).presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀) := by
      apply stalk_ringHom_ext (basePoint U u₀)
      rw [residueFieldAlgebra_comp]
      ext l
      have h1 : algebraMap ((Spec (.of Λ)).presheaf.stalk (basePoint U u₀)) (ResidueField T)
          (toStalkHom (basePoint U u₀) l) = residue T (algebraMap Λ T l) := by
        rw [← testAlgebra_comp 𝔪 U u₀ hkerU hT]
        rfl
      rw [RingHom.comp_apply, RingHom.comp_apply, h1, RingHom.coe_coe,
        testResidueRingEquiv_residue]
    exact RingHom.congr_fun h o)

/-- An Artinian local test algebra, as an object of the category of Artinian local algebras over
the local ring of `S` at the image of `u₀` with residue field `κ(u₀)`. -/
def testObject [IsArtinianRing T] :
    letI := residueFieldAlgebra U u₀
    ArtinianLocalAlgCat.{u, u, u} ((Spec (.of Λ)).presheaf.stalk (basePoint U u₀))
      (U.left.residueField u₀) :=
  letI := residueFieldAlgebra U u₀
  letI := testAlgebra 𝔪 U u₀ hkerU hT
  { carrier := T
    residueEquiv := testResidueEquiv 𝔪 U u₀ hsurjU hkerU hT hs }

variable {T₂ : Type u} [CommRing T₂] [IsLocalRing T₂] [Algebra Λ T₂]
  (hT₂ : (maximalIdeal T₂).comap (algebraMap Λ T₂) = 𝔪)
  (hs₂ : ∀ t : T₂, ∃ l : Λ, t - algebraMap Λ T₂ l ∈ maximalIdeal T₂)

/-- A surjection of test algebras, as a morphism of Artinian local algebras over the local ring of
`S` at the image of `u₀`. -/
def testHom [IsArtinianRing T] [IsArtinianRing T₂] (e : T₂ →ₐ[Λ] T)
    (he : Function.Surjective e) :
    letI := residueFieldAlgebra U u₀
    testObject 𝔪 U u₀ hsurjU hkerU hT₂ hs₂ ⟶ testObject 𝔪 U u₀ hsurjU hkerU hT hs :=
  letI := residueFieldAlgebra U u₀
  letI := testAlgebra 𝔪 U u₀ hkerU hT
  letI := testAlgebra 𝔪 U u₀ hkerU hT₂
  have hcomm : (e : T₂ →+* T).comp
      (algebraMap ((Spec (.of Λ)).presheaf.stalk (basePoint U u₀)) T₂) =
      algebraMap ((Spec (.of Λ)).presheaf.stalk (basePoint U u₀)) T := by
    apply stalk_ringHom_ext (basePoint U u₀)
    rw [RingHom.comp_assoc, testAlgebra_comp 𝔪 U u₀ hkerU hT₂, testAlgebra_comp 𝔪 U u₀ hkerU hT,
      e.comp_algebraMap]
  have hloc : IsLocalHom (e : T₂ →+* T) := IsLocalHom.of_surjective _ he
  have key : ∀ t : T₂, testResidueRingEquiv 𝔪 U u₀ hsurjU hkerU hT hs (residue T (e t)) =
      testResidueRingEquiv 𝔪 U u₀ hsurjU hkerU hT₂ hs₂ (residue T₂ t) := fun t => by
    obtain ⟨l, hl⟩ := hs₂ t
    have hl' : e t - algebraMap Λ T l ∈ maximalIdeal T := by
      have h := IsLocalRing.map_maximalIdeal_le (e : T₂ →+* T) (Ideal.mem_map_of_mem _ hl)
      rwa [RingHom.coe_coe, map_sub, e.commutes] at h
    rw [testResidueRingEquiv_residue_of_sub_mem 𝔪 U u₀ hsurjU hkerU hT hs _ l hl',
      testResidueRingEquiv_residue_of_sub_mem 𝔪 U u₀ hsurjU hkerU hT₂ hs₂ _ l hl]
  { hom := { (e : T₂ →+* T) with commutes' := fun o => RingHom.congr_fun hcomm o }
    isLocal := hloc
    residue_comm := key }

end TestObjects

/-! ### Objects of `𝒳` over the spectra of test algebras -/

section TestSchemes

variable {Λ : Type u} [CommRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal] (C : Type u) [CommRing C]
  [Algebra Λ C] (φ : C →ₐ[Λ] Completion 𝔪) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of Λ))) (U : Over (Spec (.of Λ))) (u₀ : U.left)
  (hkerU : RingHom.ker (residueAlgebraMap U.hom u₀) = 𝔪)
  {T : Type u} [CommRing T] [IsLocalRing T] [Algebra Λ T]
  (hT : (maximalIdeal T).comap (algebraMap Λ T) = 𝔪) (hc : B.Contains (Spec (.of T)))

/-- The spectrum of a test algebra as an object of the big fppf site of `S`, with its structure
morphism through the local ring of `S` at the image of `u₀`. -/
def testSiteObj : BigFppfOver B (Spec (.of Λ)) hS :=
  letI := testAlgebra 𝔪 U u₀ hkerU hT
  Over.mk (ObjectProperty.homMk (X := B.obj hc) (Y := B.obj hS)
    (Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of Λ)).presheaf.stalk (basePoint U u₀)) T)) ≫
      (Spec (.of Λ)).fromSpecStalk (basePoint U u₀)))

omit [𝔪.IsMaximal] in
/-- The structure morphism of `testSiteObj` is the spectrum of `Λ → T`. -/
theorem structureHom_testSiteObj :
    structureHom B hS (testSiteObj 𝔪 B hS U u₀ hkerU hT hc) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ T)) := by
  let := testAlgebra 𝔪 U u₀ hkerU hT
  change Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of Λ)).presheaf.stalk (basePoint U u₀))
      T)) ≫ (Spec (.of Λ)).fromSpecStalk (basePoint U u₀) = _
  rw [fromSpecStalk_eq_toStalkHom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    testAlgebra_comp 𝔪 U u₀ hkerU hT]

variable [IsArtinianRing T]

/-- The object of `𝒳` over the spectrum of an Artinian test algebra, given by
`Spec T → Spec Λ_𝔪^∧ → Spec C → S'`. -/
def testFibObj : (factorizationCategory 𝔪 C B hS).val.obj :=
  mkObj 𝔪 C B hS (testSiteObj 𝔪 B hS U u₀ hkerU hT hc) (by
    obtain ⟨N, hN⟩ := exists_pow_maximalIdeal_eq_bot (X := T)
    rw [structureHom_testSiteObj]
    exact factorsThrough_of_algHom 𝔪 C ((completionLift 𝔪 hT N hN).comp φ))

end TestSchemes

/-! ### Versality at `u₀` gives condition (4) of Stacks 02HT -/

section Smooth

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal]
  (C : Type u) [CommRing C] [Algebra Λ C] (φ : C →ₐ[Λ] Completion 𝔪) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of Λ)))

/-- A morphism in schemes between the underlying schemes of two objects of the big fppf site of
`S`, compatible with the structure morphisms, is a morphism of the site. -/
def siteHomOfScheme {T T' : BigFppfOver B (Spec (.of Λ)) hS}
    (m : (BigFppfOver.toScheme B (Spec (.of Λ)) hS).obj T ⟶
      (BigFppfOver.toScheme B (Spec (.of Λ)) hS).obj T')
    (hm : m ≫ structureHom B hS T' = structureHom B hS T) : T ⟶ T' :=
  Over.homMk (ObjectProperty.homMk m) (ObjectProperty.hom_ext _ hm)

/-- The scheme over `S` underlying an object of `𝒳`. -/
abbrev objScheme (x : (factorizationCategory 𝔪 C B hS).val.obj) : Over (Spec (.of Λ)) :=
  (factorizationFunctor 𝔪 C B hS).obj x

omit [IsNoetherianRing Λ] in
include φ in
/-- **Versality at `u₀` gives condition (4) of Stacks 02HT.** Let `x` be an object of `𝒳` over
`U`, versal at a point `u₀` over `𝔪` with `Λ → κ(u₀)` surjective, and let `V ∋ u₀` be an affine
open of `U` with `A = Γ(U, V)` and `𝔪_A` the kernel of `A → κ(u₀)`. Then `Λ → A` and `𝔪_A`
satisfy condition (4) of Stacks 02HT (the last condition of `Algebra.isSmoothAt_tfae`): for every
small extension `e : T₂ → T₁` of Artinian local `Λ`-algebras, every `Λ`-algebra map `g : A → T₁`
with `𝔪_A = g⁻¹(𝔪_{T₁})` such that `κ(𝔪_A) → κ(𝔪_{T₁})` is surjective lifts to `A → T₂`. -/
theorem lift_smallExtension_of_isVersalAt (x : (factorizationCategory 𝔪 C B hS).val.obj)
    (u₀ : (objScheme 𝔪 C B hS x).left)
    (hvers : IsVersalAt (objScheme 𝔪 C B hS x) (factorizationFunctor 𝔪 C B hS)
      u₀ x rfl)
    (hsurjU : Function.Surjective
      (residueAlgebraMap (objScheme 𝔪 C B hS x).hom u₀))
    (hkerU : RingHom.ker (residueAlgebraMap (objScheme 𝔪 C B hS x).hom u₀) = 𝔪)
    {V : (objScheme 𝔪 C B hS x).left.Opens} (hV : IsAffineOpen V)
    (hu₀ : u₀ ∈ V) :
    letI := chartAlgebra (objScheme 𝔪 C B hS x).hom hV
    ∀ [(RingHom.ker (chartResidue hV hu₀)).IsPrime]
      (T₂ T₁ : Type u) [CommRing T₂] [CommRing T₁] [IsLocalRing T₂] [IsLocalRing T₁]
      [IsArtinianRing T₂] [IsArtinianRing T₁] [Algebra Λ T₂] [Algebra Λ T₁]
      (e : T₂ →ₐ[Λ] T₁), Function.Surjective e →
      IsSimpleModule T₂ (RingHom.ker (e : T₂ →+* T₁)) →
      ∀ (g : Γ((objScheme 𝔪 C B hS x).left, V) →ₐ[Λ] T₁)
        (hq : (maximalIdeal T₁).comap (g : Γ((objScheme 𝔪 C B hS x).left, V) →+* T₁) =
          RingHom.ker (chartResidue hV hu₀)),
        Function.Surjective (Ideal.ResidueField.mapₐ (RingHom.ker (chartResidue hV hu₀))
          (maximalIdeal T₁) g hq.symm) →
        ∃ g' : Γ((objScheme 𝔪 C B hS x).left, V) →ₐ[Λ] T₂, e.comp g' = g := by
  let := chartAlgebra (objScheme 𝔪 C B hS x).hom hV
  intro _
  have hψ₀ : (chartResidue hV hu₀).comp
      (algebraMap Λ Γ((objScheme 𝔪 C B hS x).left, V)) =
      residueAlgebraMap (objScheme 𝔪 C B hS x).hom u₀ :=
    chartResidue_comp_algebraMap (objScheme 𝔪 C B hS x).hom hV hu₀
  have hsurj : Function.Surjective ((chartResidue hV hu₀).comp
      (algebraMap Λ Γ((objScheme 𝔪 C B hS x).left, V))) := hψ₀ ▸ hsurjU
  have hker : RingHom.ker ((chartResidue hV hu₀).comp
      (algebraMap Λ Γ((objScheme 𝔪 C B hS x).left, V))) = 𝔪 := hψ₀ ▸ hkerU
  have hmax : (RingHom.ker (chartResidue hV hu₀)).IsMaximal :=
    ker_isMaximal_of_surjective_comp (chartResidue hV hu₀) hsurj
  intro T₂ T₁ _ _ _ _ _ _ _ _ e he _ g hq hres
  have hT₁ := comap_maximalIdeal_of_comap_eq_ker 𝔪 (chartResidue hV hu₀) hker g hq
  have hs₁ := exists_sub_mem_maximalIdeal_of_residueField_surjective (chartResidue hV hu₀)
    hsurj g hq hres
  have hT₂ := comap_maximalIdeal_of_surjective_of_comap 𝔪 e he hT₁
  have hs₂ := exists_sub_mem_maximalIdeal_of_surjective e he hs₁
  have hc₁ := contains_spec_of_artinian B hS T₁ hs₁
  have hc₂ := contains_spec_of_artinian B hS T₂ hs₂
  let y := testFibObj 𝔪 C φ B hS (objScheme 𝔪 C B hS x) u₀ hkerU hT₁ hc₁
  let z := testFibObj 𝔪 C φ B hS (objScheme 𝔪 C B hS x) u₀ hkerU hT₂ hc₂
  -- the arrow `Spec T₁ → Spec T₂`
  have hwi : Spec.map (CommRingCat.ofHom (e : T₂ →+* T₁)) ≫
      structureHom B hS (testSiteObj 𝔪 B hS (objScheme 𝔪 C B hS x) u₀ hkerU hT₂ hc₂) =
      structureHom B hS (testSiteObj 𝔪 B hS (objScheme 𝔪 C B hS x) u₀ hkerU hT₁ hc₁) := by
    rw [structureHom_testSiteObj, structureHom_testSiteObj, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, e.comp_algebraMap]
  let i : y ⟶ z := homOfBase (siteHomOfScheme B hS _ hwi)
  -- the arrow `Spec T₁ → U`
  have hwa : (Spec.map (CommRingCat.ofHom (g : Γ((objScheme 𝔪 C B hS x).left, V) →+* T₁)) ≫
      hV.fromSpec) ≫ structureHom B hS ((factorizationCategory 𝔪 C B hS).val.p.obj x) =
      structureHom B hS (testSiteObj 𝔪 B hS (objScheme 𝔪 C B hS x) u₀ hkerU hT₁ hc₁) := by
    rw [structureHom_testSiteObj]
    change (Spec.map (CommRingCat.ofHom (g : Γ((objScheme 𝔪 C B hS x).left, V) →+* T₁)) ≫
      hV.fromSpec) ≫ (objScheme 𝔪 C B hS x).hom = _
    rw [Category.assoc, ← specMap_chartAlgebra (objScheme 𝔪 C B hS x).hom hV, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, g.comp_algebraMap]
  let a : y ⟶ x := homOfBase (siteHomOfScheme B hS _ hwa)
  -- the residue condition for `a`
  have hkey : ((testResidueRingEquiv 𝔪 (objScheme 𝔪 C B hS x) u₀ hsurjU hkerU hT₁ hs₁ :
      ResidueField T₁ →+* (objScheme 𝔪 C B hS x).left.residueField u₀).comp
        (residue T₁)).comp (g : Γ((objScheme 𝔪 C B hS x).left, V) →+* T₁) =
      chartResidue hV hu₀ := by
    ext t
    obtain ⟨l, hl⟩ := exists_sub_mem_ker (chartResidue hV hu₀) hsurj t
    have h1 := sub_algebraMap_mem_maximalIdeal_of_sub_mem_ker (chartResidue hV hu₀) g hq t l hl
    have h2 : chartResidue hV hu₀ t = residueAlgebraMap (objScheme 𝔪 C B hS x).hom u₀ l := by
      rwa [← hψ₀, RingHom.comp_apply, ← sub_eq_zero, ← map_sub]
    change testResidueRingEquiv 𝔪 (objScheme 𝔪 C B hS x) u₀ hsurjU hkerU hT₁ hs₁
      (residue T₁ (g t)) = chartResidue hV hu₀ t
    rw [testResidueRingEquiv_residue_of_sub_mem 𝔪 (objScheme 𝔪 C B hS x) u₀ hsurjU hkerU hT₁ hs₁
        (g t) l h1, h2]
  have hcondA : Spec.map (CommRingCat.ofHom ((testResidueRingEquiv 𝔪 (objScheme 𝔪 C B hS x) u₀
      hsurjU hkerU hT₁ hs₁ : ResidueField T₁ →+* (objScheme 𝔪 C B hS x).left.residueField u₀).comp
        (residue T₁))) ≫ 𝟙 (Spec (.of T₁)) ≫
      (Spec.map (CommRingCat.ofHom (g : Γ((objScheme 𝔪 C B hS x).left, V) →+* T₁)) ≫
        hV.fromSpec) ≫ 𝟙 (objScheme 𝔪 C B hS x).left =
      (objScheme 𝔪 C B hS x).left.fromSpecResidueField u₀ := by
    rw [Category.id_comp, Category.comp_id, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hkey, specMap_chartResidue]
  obtain ⟨b, hb⟩ := hvers (testObject 𝔪 (objScheme 𝔪 C B hS x) u₀ hsurjU hkerU hT₁ hs₁)
    (testObject 𝔪 (objScheme 𝔪 C B hS x) u₀ hsurjU hkerU hT₂ hs₂)
    (testHom 𝔪 (objScheme 𝔪 C B hS x) u₀ hsurjU hkerU hT₁ hs₁ hT₂ hs₂ e he) he y z rfl rfl i
    ((Category.id_comp _).trans (Category.comp_id _)) a hcondA
  -- the lift `Spec T₂ → U`
  let b' : Spec (.of T₂) ⟶ (objScheme 𝔪 C B hS x).left :=
    ((factorizationFunctor 𝔪 C B hS).map b).left
  have hb' : Spec.map (CommRingCat.ofHom (e : T₂ →+* T₁)) ≫ b' =
      Spec.map (CommRingCat.ofHom (g : Γ((objScheme 𝔪 C B hS x).left, V) →+* T₁)) ≫
        hV.fromSpec := by
    have h := congrArg (fun m => ((factorizationFunctor 𝔪 C B hS).map m).left) hb
    simp only [Functor.map_comp, Over.comp_left] at h
    exact h
  have hbS : b' ≫ (objScheme 𝔪 C B hS x).hom =
      Spec.map (CommRingCat.ofHom (algebraMap Λ T₂)) :=
    (Over.w ((factorizationFunctor 𝔪 C B hS).map b)).trans
      (structureHom_testSiteObj 𝔪 B hS (objScheme 𝔪 C B hS x) u₀ hkerU hT₂ hc₂)
  have hloc : IsLocalHom (e : T₂ →+* T₁) := IsLocalHom.of_surjective _ he
  have hmemV : b' (closedPoint T₂) ∈ V := by
    have h1 : (Spec.map (CommRingCat.ofHom (e : T₂ →+* T₁))) (closedPoint T₁) =
        closedPoint T₂ := Spec_closedPoint
    have h2 : b' (closedPoint T₂) = hV.fromSpec
        ((Spec.map (CommRingCat.ofHom (g : Γ((objScheme 𝔪 C B hS x).left, V) →+* T₁)))
          (closedPoint T₁)) :=
      (congrArg b' h1.symm).trans ((Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun m => m (closedPoint T₁)) hb').trans (Scheme.Hom.comp_apply _ _ _)))
    rw [h2]
    exact (show _ ∈ (V : Set (objScheme 𝔪 C B hS x).left) from
      hV.range_fromSpec ▸ Set.mem_range_self _)
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem b' hmemV
  have hrange : Set.range b' ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨w, rfl⟩
    exact hV.range_fromSpec ▸ (htop ▸ trivial : w ∈ b' ⁻¹ᵁ V)
  let b'' := IsOpenImmersion.lift hV.fromSpec b' hrange
  have hb'' : b'' ≫ hV.fromSpec = b' := IsOpenImmersion.lift_fac _ _ _
  have hcomm : CommRingCat.ofHom (algebraMap Λ Γ((objScheme 𝔪 C B hS x).left, V)) ≫
      Spec.preimage b'' = CommRingCat.ofHom (algebraMap Λ T₂) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, specMap_chartAlgebra, ← Category.assoc, hb'', hbS]
  let g' : Γ((objScheme 𝔪 C B hS x).left, V) →ₐ[Λ] T₂ :=
    { (Spec.preimage b'').hom with commutes' := fun l => congrArg (fun m => m.hom l) hcomm }
  refine ⟨g', ?_⟩
  have h3 : Spec.preimage b'' ≫ CommRingCat.ofHom (e : T₂ →+* T₁) =
      CommRingCat.ofHom (g : Γ((objScheme 𝔪 C B hS x).left, V) →+* T₁) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← cancel_mono hV.fromSpec, Category.assoc, hb'', hb']
  ext t
  exact congrArg (fun m => m.hom t) h3

include φ in
/-- **Versality at `u₀` implies smoothness at `𝔪_A`.** Let `x` be an object of `𝒳` over `U`,
locally of finite type over `S`, versal at a point `u₀` over `𝔪` with `Λ → κ(u₀)` surjective, and
let `V ∋ u₀` be an affine open of `U` with `A = Γ(U, V)`. Then `Λ → A` is smooth at the kernel of
`A → κ(u₀)`, by condition (4) of Stacks 02HT (`lift_smallExtension_of_isVersalAt`). -/
theorem isSmoothAt_of_isVersalAt (x : (factorizationCategory 𝔪 C B hS).val.obj)
    (u₀ : (objScheme 𝔪 C B hS x).left)
    (hvers : IsVersalAt (objScheme 𝔪 C B hS x) (factorizationFunctor 𝔪 C B hS)
      u₀ x rfl)
    [LocallyOfFiniteType (objScheme 𝔪 C B hS x).hom]
    (hsurjU : Function.Surjective
      (residueAlgebraMap (objScheme 𝔪 C B hS x).hom u₀))
    (hkerU : RingHom.ker (residueAlgebraMap (objScheme 𝔪 C B hS x).hom u₀) = 𝔪)
    {V : (objScheme 𝔪 C B hS x).left.Opens} (hV : IsAffineOpen V)
    (hu₀ : u₀ ∈ V) :
    letI := chartAlgebra (objScheme 𝔪 C B hS x).hom hV
    ∀ [(RingHom.ker (chartResidue hV hu₀)).IsPrime],
      Algebra.IsSmoothAt Λ (RingHom.ker (chartResidue hV hu₀)) := by
  let := chartAlgebra (objScheme 𝔪 C B hS x).hom hV
  intro _
  have : Algebra.FiniteType Λ Γ((objScheme 𝔪 C B hS x).left, V) :=
    finiteType_chartAlgebra (objScheme 𝔪 C B hS x).hom hV
  exact ((Algebra.isSmoothAt_tfae (RingHom.ker (chartResidue hV hu₀))).out 4 1).mp
    (lift_smallExtension_of_isVersalAt 𝔪 C φ B hS x u₀ hvers hsurjU hkerU hV hu₀)

end Smooth

end Deformation.Artin.GRingNecessity

end
