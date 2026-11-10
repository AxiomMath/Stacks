module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFirstOrder
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap
public import StacksFrontier.AlgebraicGeometry.Thickenings.OpenRestriction
public import StacksFrontier.RingTheory.Unramified.Thickening

/-!
# Differentials of a universal first-order thickening

Let `h : Z ⟶ X` be a formally unramified morphism of schemes over `S`, and let `Z ⊂ Z'` be a
universal first-order thickening of `Z` over `X` with structure morphism `h' : Z' ⟶ X`. The
canonical map `c_{h'} : (h')^* Ω_{X/S} ⟶ Ω_{Z'/S}` restricts along `Z ⟶ Z'` to an isomorphism
`h^* Ω_{X/S} ⟶ Ω_{Z'/S} ⊗ 𝒪_Z`.

## Main results

* `Stacks.Thickenings.isIso_thickeningRelativeDifferentialsMap`: the restriction along the
  inclusion of a universal first-order thickening of the canonical map on relative differentials
  is an isomorphism.

## References

* [Stacks Project, Tag 04FB](https://stacks.math.columbia.edu/tag/04FB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
open AlgebraicGeometry.Scheme.Modules (sectionsLinearMap)

universe u

namespace Stacks.Thickenings

/-! ### Spectra of surjections with square-zero kernel -/

/-- The spectrum of the comorphism of a first-order thickening on an affine open of the ambient
scheme is a first-order thickening. -/
private lemma isFirstOrderThickening_specMap_appLE
    {Z Z' : Scheme.{u}} (i : Z ⟶ Z') (hi : IsFirstOrderThickening i)
    (U : Z.Opens) (V : Z'.Opens) (hV : IsAffineOpen V) (hUV : U = i ⁻¹ᵁ V) :
    IsFirstOrderThickening (Spec.map (i.appLE V U hUV.le)) := by
  have : IsClosedImmersion i := hi.1
  subst hUV
  have hker : RingHom.ker (i.app V).hom ^ 2 = ⊥ := by
    have he := congrArg (fun J : Z'.IdealSheafData => J.ideal ⟨V, hV⟩) hi.2
    have he' : (i.ker.ideal ⟨V, hV⟩) ^ 2 = ⊥ := he
    rwa [Scheme.Hom.ker_apply] at he'
  simpa only [Scheme.Hom.appLE_eq_app] using
    isFirstOrderThickening_specMap (i.app V) (i.app_surjective V hV) hker

/-! ### Transport of the universal property along isomorphisms -/

/-- The universal first-order thickening property transports along isomorphisms of the closed
subscheme, the ambient scheme and the base. -/
private lemma isUniversalFirstOrderThickening_transport
    {Z X Z' A B C : Scheme.{u}}
    {h : Z ⟶ X} {i : Z ⟶ Z'} {h' : Z' ⟶ X}
    (hi : IsUniversalFirstOrderThickening h i h')
    (eZ : Z ≅ A) (eX : X ≅ B) (eZ' : Z' ≅ C)
    (k : A ⟶ B) (j : A ⟶ C) (k' : C ⟶ B)
    (hk : eZ.hom ≫ k = h ≫ eX.hom)
    (hj : eZ.hom ≫ j = i ≫ eZ'.hom)
    (hk' : eZ'.hom ≫ k' = h' ≫ eX.hom)
    (hj₀ : IsFirstOrderThickening j) :
    IsUniversalFirstOrderThickening k j k' := by
  have hkInv : k ≫ eX.inv = eZ.inv ≫ h := by
    rw [← cancel_epi eZ.hom, ← Category.assoc, hk, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hjInv : j ≫ eZ'.inv = eZ.inv ≫ i := by
    rw [← cancel_epi eZ.hom, ← Category.assoc, hj, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hk'Inv : k' ≫ eX.inv = eZ'.inv ≫ h' := by
    rw [← cancel_epi eZ'.hom, ← Category.assoc, hk', Category.assoc, Iso.hom_inv_id,
      Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  refine ⟨hj₀, ?_, ?_⟩
  · rw [← cancel_epi eZ.hom, ← Category.assoc, hj, Category.assoc, hk',
      ← Category.assoc, hi.inclusion_toBase, hk]
  · intro T T' l hl a b hab
    obtain ⟨g, hg, hgu⟩ := hi.existsUnique_lift l hl (a ≫ eZ.inv) (b ≫ eX.inv)
      (by simpa only [Category.assoc, hkInv] using congrArg (fun q => q ≫ eX.inv) hab)
    refine ⟨g ≫ eZ'.hom, ⟨?_, ?_⟩, ?_⟩
    · rw [← Category.assoc, hg.1, Category.assoc, ← hj]
      simp
    · rw [Category.assoc, hk', ← Category.assoc, hg.2]
      simp
    · intro q hq
      have he := hgu (q ≫ eZ'.inv) ⟨?_, ?_⟩
      · rw [← Category.comp_id q, ← Iso.inv_hom_id eZ', ← Category.assoc, he]
      · simpa only [Category.assoc, hjInv] using congrArg (fun w => w ≫ eZ'.inv) hq.1
      · simpa only [Category.assoc, hk'Inv] using congrArg (fun w => w ≫ eX.inv) hq.2

/-- **The universal first-order thickening on an affine chart, read on spectra.** Let
`i : Z ⟶ Z'` with structure morphism `h' : Z' ⟶ X` be a universal first-order thickening of
`h : Z ⟶ X`, let `U ⊆ Z` and `V ⊆ X` be affine opens with `h(U) ⊆ V`, and let `O ⊆ Z'` be an
affine open with `Z ∩ O = U` and `h'(O) ⊆ V`. Then the spectra of the three comorphisms form a
universal first-order thickening. -/
private lemma isUniversalFirstOrderThickening_specMap_appLE
    {Z X Z' : Scheme.{u}} {h : Z ⟶ X} {i : Z ⟶ Z'} {h' : Z' ⟶ X}
    (hi : IsUniversalFirstOrderThickening h i h')
    (U : Z.affineOpens) (V : X.affineOpens) {O : Z'.Opens} (hO : IsAffineOpen O)
    (hUO : i ⁻¹ᵁ O = U.1) (hOV : O ≤ h' ⁻¹ᵁ V.1) (hUV : U.1 ≤ h ⁻¹ᵁ V.1) :
    IsUniversalFirstOrderThickening (Spec.map (h.appLE V.1 U.1 hUV))
      (Spec.map (i.appLE O U.1 hUO.ge)) (Spec.map (h'.appLE V.1 O hOV)) := by
  have := U.2
  exact isUniversalFirstOrderThickening_transport
    (isUniversalFirstOrderThickening_resLE hi hUO hOV hUV)
    U.2.isoSpec V.2.isoSpec hO.isoSpec _ _ _
    (Scheme.Opens.toSpecΓ_SpecMap_appLE h V.1 U.1 hUV)
    (Scheme.Opens.toSpecΓ_SpecMap_appLE i O U.1 hUO.ge)
    (Scheme.Opens.toSpecΓ_SpecMap_appLE h' V.1 O hOV)
    (isFirstOrderThickening_specMap_appLE i hi.isFirstOrderThickening U.1 O hO hUO.symm)

/-! ### From the scheme-theoretic universal property to the ring-theoretic one -/

/-- **A universal first-order thickening of affine schemes is one of rings.** If the spectra of a
surjection `q : B →ₐ[R] A` and of `algebraMap R B` are a universal first-order thickening of
`Spec A` over `Spec R`, then `q` is a universal first order thickening of `A` over `R` in the
sense of `Algebra.Extension.IsUniversalFirstOrderThickening`. -/
private theorem isUniversalFirstOrderThickening_extension
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra B A] [IsScalarTower R B A]
    (q : B →ₐ[R] A) (hq : Function.Surjective q)
    (hi : IsUniversalFirstOrderThickening
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom q.toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :
    (Algebra.Extension.ofSurjective q hq).IsUniversalFirstOrderThickening := by
  have hkerSq : RingHom.ker q.toRingHom ^ 2 = ⊥ := by
    set j := Spec.map (CommRingCat.ofHom q.toRingHom) with hj
    have htop : (j.ker.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of B))⟩) ^ 2 = ⊥ :=
      congrArg (fun J : (Spec (CommRingCat.of B)).IdealSheafData =>
        J.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of B))⟩)
        hi.isFirstOrderThickening.2
    rw [Scheme.Hom.ker_apply] at htop
    change (RingHom.ker j.appTop.hom) ^ 2 = ⊥ at htop
    have hkerApp : RingHom.ker j.appTop.hom =
        (RingHom.ker q.toRingHom).comap
          (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom := by
      ext x
      simp only [RingHom.mem_ker, Ideal.mem_comap]
      have hn := congrArg (fun k : CommRingCat.Hom _ _ => k.hom x)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom q.toRingHom))
      change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (j.appTop.hom x) =
        q.toRingHom ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom x) at hn
      constructor
      · intro hx
        rw [← hn, hx]
        simp
      · intro hx
        apply (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
        rw [map_zero, hn, hx]
    rw [hkerApp] at htop
    have hγ : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom :=
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom).2
    have hmap := congrArg
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom) htop
    rwa [Ideal.map_pow, Ideal.map_comap_of_surjective _ hγ, Ideal.map_bot] at hmap
  set P := Algebra.Extension.ofSurjective q hq with hP
  have hker : P.ker ^ 2 = ⊥ := hkerSq
  refine ⟨hker, ?_⟩
  intro C _ _ I hI a
  set jQ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ R I).toRingHom) with hjQ
  set aSpec := Spec.map (CommRingCat.ofHom a.toRingHom) with haSpec
  set bSpec := Spec.map (CommRingCat.ofHom (algebraMap R C)) with hbSpec
  set hA := Spec.map (CommRingCat.ofHom (algebraMap R A)) with hhA
  set iAB := Spec.map (CommRingCat.ofHom (algebraMap P.Ring A)) with hiAB
  set hB := Spec.map (CommRingCat.ofHom (algebraMap R P.Ring)) with hhB
  have hcomm : jQ ≫ bSpec = aSpec ≫ hA := by
    apply Spec.homEquiv.injective
    have hleft : Spec.homEquiv (jQ ≫ bSpec) =
        (CommRingCat.ofHom (algebraMap R C)) ≫
          CommRingCat.ofHom (Ideal.Quotient.mkₐ R I).toRingHom := by
      simp [hjQ, hbSpec]
    have hright : Spec.homEquiv (aSpec ≫ hA) =
        (CommRingCat.ofHom (algebraMap R A)) ≫ CommRingCat.ofHom a.toRingHom := by
      simp [haSpec, hhA]
    rw [hleft, hright]
    ext r
    simp
  have hkerQ : RingHom.ker (Ideal.Quotient.mkₐ R I).toRingHom ^ 2 = ⊥ := by
    change RingHom.ker (Ideal.Quotient.mk I) ^ 2 = ⊥
    rw [Ideal.mk_ker, hI]
  have hjThick := isFirstOrderThickening_specMap
    (CommRingCat.ofHom (Ideal.Quotient.mkₐ R I).toRingHom)
    Ideal.Quotient.mk_surjective hkerQ
  obtain ⟨g, hg, hgu⟩ := hi.existsUnique_lift jQ hjThick aSpec bSpec hcomm
  set φ : P.Ring →+* C := (Spec.homEquiv g).hom with hφdef
  have hφ : Spec.map (CommRingCat.ofHom φ) = g :=
    (congrArg Spec.map (rfl : CommRingCat.ofHom φ = Spec.homEquiv g)).trans
      (Spec.map_preimage g)
  have hlift : (CommRingCat.ofHom (algebraMap R P.Ring)) ≫ CommRingCat.ofHom φ =
      CommRingCat.ofHom (algebraMap R C) := by
    have hb : Spec.map (CommRingCat.ofHom φ) ≫ hB = bSpec := by
      rw [hφ]; exact hg.2
    have hh := congrArg Spec.homEquiv hb
    simpa [hhB, hbSpec, Spec.preimage_comp] using hh
  set lift : P.Ring →ₐ[R] C :=
    { toRingHom := φ
      commutes' := fun r => congrArg (fun k : CommRingCat.Hom _ _ => k.hom r) hlift }
    with hliftdef
  refine ⟨lift, ?_, ?_⟩
  · apply AlgHom.ext
    intro x
    have hsq : jQ ≫ Spec.map (CommRingCat.ofHom φ) = aSpec ≫ iAB := by
      rw [hφ]; exact hg.1
    have hr : (CommRingCat.ofHom φ) ≫ CommRingCat.ofHom
          (Ideal.Quotient.mkₐ R I).toRingHom =
        (CommRingCat.ofHom (algebraMap P.Ring A)) ≫ CommRingCat.ofHom a.toRingHom := by
      have hh := congrArg Spec.homEquiv hsq
      simpa [hjQ, haSpec, hiAB, Spec.preimage_comp] using hh
    exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom x) hr
  · intro k hk
    apply AlgHom.ext
    intro x
    have hk1 : jQ ≫ Spec.map (CommRingCat.ofHom k.toRingHom) = aSpec ≫ iAB := by
      apply Spec.homEquiv.injective
      have hleft : Spec.homEquiv (jQ ≫ Spec.map (CommRingCat.ofHom k.toRingHom)) =
          (CommRingCat.ofHom k.toRingHom) ≫
            CommRingCat.ofHom (Ideal.Quotient.mkₐ R I).toRingHom := by
        simp [hjQ, Spec.preimage_comp]
      have hright : Spec.homEquiv (aSpec ≫ iAB) =
          (CommRingCat.ofHom (algebraMap P.Ring A)) ≫ CommRingCat.ofHom a.toRingHom := by
        simp [haSpec, hiAB, Spec.preimage_comp]
      rw [hleft, hright]
      ext y
      exact congrArg (fun F : P.Ring →ₐ[R] C ⧸ I => F y) hk
    have hk2 : Spec.map (CommRingCat.ofHom k.toRingHom) ≫ hB = bSpec := by
      apply Spec.homEquiv.injective
      have hleft : Spec.homEquiv
          (Spec.map (CommRingCat.ofHom k.toRingHom) ≫ hB) =
            (CommRingCat.ofHom (algebraMap R P.Ring)) ≫
              CommRingCat.ofHom k.toRingHom := by
        change Spec.preimage
          (Spec.map (CommRingCat.ofHom k.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R P.Ring))) = _
        rw [Spec.preimage_comp]
        simp
      have hright : Spec.homEquiv bSpec = CommRingCat.ofHom (algebraMap R C) := by
        simp [hbSpec]
      rw [hleft, hright]
      ext r
      exact k.commutes r
    have hring : CommRingCat.ofHom k.toRingHom = Spec.homEquiv g := by
      have hh := congrArg Spec.homEquiv (hgu _ ⟨hk1, hk2⟩)
      change Spec.preimage (Spec.map (CommRingCat.ofHom k.toRingHom)) =
        Spec.preimage g at hh
      rwa [Spec.preimage_map] at hh
    exact congrArg (fun F : CommRingCat.Hom _ _ => F.hom x) hring

/-- The canonical map `B ⊗_R Ω_{R/T} ⟶ Ω_{B/T}` of
`KaehlerDifferential.mapBaseChange` is the base-change lift of `KaehlerDifferential.map`. -/
private lemma liftBaseChange_map_eq_mapBaseChange (T R B : Type*) [CommRing T] [CommRing R]
    [CommRing B] [Algebra T R] [Algebra R B] [Algebra T B] [IsScalarTower T R B] :
    (KaehlerDifferential.map T T R B).liftBaseChange B =
      KaehlerDifferential.mapBaseChange T R B := by
  refine LinearMap.restrictScalars_injective R ?_
  refine TensorProduct.ext' (fun b y => ?_)
  simp only [LinearMap.coe_restrictScalars, LinearMap.liftBaseChange_tmul,
    KaehlerDifferential.mapBaseChange_tmul]

/-- The bijection of Tag 04EF rewritten as a base change of the canonical map
`Ω_{R/T} ⊗_R B ⟶ Ω_{B/T}` along `B ⟶ A`. -/
private lemma bijective_baseChange_of_bijective_liftBaseChange
    {T R A B : Type*} [CommRing T] [CommRing R] [CommRing A] [CommRing B]
    [Algebra T R] [Algebra R B] [Algebra R A] [Algebra T B]
    [Algebra B A] [IsScalarTower T R B] [IsScalarTower R B A]
    (hbij : Function.Bijective
      ((((TensorProduct.mk B A Ω[B⁄T] 1).restrictScalars R).comp
        (KaehlerDifferential.map T T R B)).liftBaseChange A)) :
    Function.Bijective (LinearMap.baseChange A
      ((KaehlerDifferential.map T T R B).liftBaseChange B)) := by
  set e := TensorProduct.AlgebraTensorModule.cancelBaseChange R B A A Ω[R⁄T] with he'
  have he : (LinearMap.baseChange A
      ((KaehlerDifferential.map T T R B).liftBaseChange B)).comp e.symm.toLinearMap =
      (((TensorProduct.mk B A Ω[B⁄T] 1).restrictScalars R).comp
        (KaehlerDifferential.map T T R B)).liftBaseChange A := by
    ext x
    simp [he', LinearMap.liftBaseChange_tmul]
  have hb : Function.Bijective ((LinearMap.baseChange A
      ((KaehlerDifferential.map T T R B).liftBaseChange B)) ∘ e.symm) := by
    change Function.Bijective ((LinearMap.baseChange A
      ((KaehlerDifferential.map T T R B).liftBaseChange B)).comp e.symm.toLinearMap)
    rw [he]
    exact hbij
  exact (EquivLike.bijective_comp e.symm _).mp hb

/-- **A form of Stacks Project, Tag 04EF.** Let
`T → R → B → A` be ring maps with `q : B →ₐ[R] A` a surjection whose spectrum, together with the
spectrum of `algebraMap R B`, is a universal first-order thickening of `Spec A` over `Spec R`.
Then the base change along `B → A` of the canonical map `B ⊗_R Ω_{R/T} ⟶ Ω_{B/T}` is bijective.
-/
private theorem bijective_baseChange_mapBaseChange
    {T R A B : Type u} [CommRing T] [CommRing R] [CommRing A] [CommRing B]
    [Algebra T R] [Algebra R A] [Algebra R B] [Algebra T A]
    [iBA : Algebra B A] [iTB : Algebra T B]
    [IsScalarTower T R A] [IsScalarTower R B A] [IsScalarTower T R B]
    (q : B →ₐ[R] A) (hq : Function.Surjective q)
    (hBA : algebraMap B A = q.toRingHom)
    (hTB : algebraMap T B = (algebraMap R B).comp (algebraMap T R))
    (hi : IsUniversalFirstOrderThickening
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom q.toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :
    Function.Bijective
      (LinearMap.baseChange A (KaehlerDifferential.mapBaseChange T R B)) := by
  have h2 : iBA = q.toAlgebra :=
    Algebra.algebra_ext _ _ (fun b => congrArg (fun g : B →+* A => g b) hBA)
  have h1 : iTB = Algebra.compHom B (algebraMap T R) :=
    Algebra.algebra_ext _ _ (fun r => congrArg (fun g : T →+* B => g r) hTB)
  subst h1
  subst h2
  let : Algebra B A := q.toAlgebra
  let : Algebra T B := Algebra.compHom B (algebraMap T R)
  have hP := isUniversalFirstOrderThickening_extension q hq hi
  have hbij := (hP.formallyUnramified_ring_and_bijective_map T).2
  have hb := bijective_baseChange_of_bijective_liftBaseChange hbij
  rwa [liftBaseChange_map_eq_mapBaseChange] at hb


/-! ### Isomorphy of a morphism of modules tested on a basis of opens -/

/-- **A morphism of sheaves of modules on a scheme is an isomorphism as soon as it is one on
sections over the members of a basis of the topology.** -/
private lemma isIso_of_isIso_app_basis {Z : Scheme.{u}} {ι : Type*} (B : ι → Z.Opens)
    (hB : Opens.IsBasis (Set.range B)) {M N : SheafOfModules.{u} Z.ringCatSheaf} (f : M ⟶ N)
    (h : ∀ j, IsIso (((SheafOfModules.toSheaf.{u} Z.ringCatSheaf).map f).hom.app (op (B j)))) :
    IsIso f := by
  have hsheaf : IsIso ((SheafOfModules.toSheaf.{u} Z.ringCatSheaf).map f) :=
    TopCat.Sheaf.isIso_iff_isIso_basis hB h
  have : (SheafOfModules.toSheaf.{u} Z.ringCatSheaf ⋙
      sheafToPresheaf (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf _).ReflectsIsomorphisms
  have : (SheafOfModules.toSheaf.{u} Z.ringCatSheaf).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_comp _ (sheafToPresheaf _ _)
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf.{u} Z.ringCatSheaf)

/-- An affine open of the source of a morphism of schemes over a base, together with affine opens
of the target and of the base containing its images, is a member of a basis of the topology. -/
private lemma isBasis_compatibleAffineOpens {Z X S : Scheme.{u}} (h : Z ⟶ X) (p : X ⟶ S) :
    Opens.IsBasis (Set.range (fun U : { U : Z.affineOpens //
      ∃ (V : X.affineOpens) (W : S.affineOpens), U.1 ≤ h ⁻¹ᵁ V.1 ∧ V.1 ≤ p ⁻¹ᵁ W.1 } =>
      U.1.1)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro O z hz
  obtain ⟨W, hW, hzW, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (U := ⊤) (x := p (h z)) (by trivial)
  obtain ⟨V, hV, hzV, hVW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (U := p ⁻¹ᵁ W) (x := h z) hzW
  obtain ⟨U, hU, hzU, hUO⟩ := Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
    (U := O ⊓ h ⁻¹ᵁ V) (x := z) ⟨hz, hzV⟩
  exact ⟨U, ⟨⟨⟨U, hU⟩, ⟨⟨V, hV⟩, ⟨W, hW⟩, hUO.trans inf_le_right, hVW⟩⟩, rfl⟩,
    hzU, hUO.trans inf_le_left⟩

/-- **Pulling a section back exhibits the sections of the pullback over an affine open as a base
change.** -/
private lemma isBaseChange_pullbackSection {Y X : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) [inst : Algebra Γ(X, U) Γ(Y, V)]
    (halg : inst = (f.appLE U V hVU).hom.toAlgebra)
    [Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj F, V)]
    [IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V)]
    (ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ((Scheme.Modules.pullback f).obj F, V))
    (hρ : ∀ a, ρ a = Scheme.Modules.pullbackSection f F U V hVU a) :
    IsBaseChange Γ(Y, V) ρ :=
  ModuleCat.isBaseChange_of_extendScalarsIso (f.appLE U V hVU).hom halg
    (affinePullbackSectionsBaseChangeIso f F hU hV hVU) ρ
    (fun m => (affinePullbackSectionsBaseChangeIso_one_tmul f F hU hV hVU m).trans (hρ m).symm)

/-! ### The canonical map on an affine chart -/

/-- **Stacks Project, Tag 04FB on an affine chart.** With `i : Z ⟶ Z'` and `h' : Z' ⟶ X` a
universal first-order thickening of `h : Z ⟶ X`, affine opens `U ⊆ Z`, `V ⊆ X`, `W ⊆ S` with
`h(U) ⊆ V` and `p(V) ⊆ W`, and `O ⊆ Z'` an affine open with `Z ∩ O = U` and `h'(O) ⊆ V`, the
restriction along `i` of the canonical map `(h')^* Ω_{X/S} ⟶ Ω_{Z'/S}` is bijective on
sections over `U`. -/
private lemma bijective_app_pullback_relativeDifferentialsMap
    {Z X Z' S : Scheme.{u}} {h : Z ⟶ X} {i : Z ⟶ Z'} {h' : Z' ⟶ X}
    (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S)
    (U : Z.affineOpens) (V : X.affineOpens) (W : S.affineOpens)
    {O : Z'.Opens} (hO : IsAffineOpen O) (hUO : i ⁻¹ᵁ O = U.1) (hOV : O ≤ h' ⁻¹ᵁ V.1)
    (hUV : U.1 ≤ h ⁻¹ᵁ V.1) (hVW : V.1 ≤ p ⁻¹ᵁ W.1) :
    Function.Bijective (((Scheme.Modules.pullback i).map
      (Scheme.Hom.relativeDifferentialsMap h' p (h' ≫ p) (𝟙 S) (by simp))).app U.1) := by
  have hcomm : h' ≫ p = (h' ≫ p) ≫ 𝟙 S := by simp
  have hcommi : i ≫ h' = h ≫ 𝟙 X := by rw [hi.inclusion_toBase, Category.comp_id]
  have hcommh : h ≫ p = (h ≫ p) ≫ 𝟙 S := by simp
  have hOW : O ≤ (h' ≫ p) ⁻¹ᵁ W.1 := hOV.trans (Scheme.Hom.preimage_mono h' hVW)
  have hUW : U.1 ≤ (h ≫ p) ⁻¹ᵁ W.1 := hUV.trans (Scheme.Hom.preimage_mono h hVW)
  let : Algebra Γ(S, W.1) Γ(X, V.1) := (p.appLE W.1 V.1 hVW).hom.toAlgebra
  let : Algebra Γ(X, V.1) Γ(Z', O) := (h'.appLE V.1 O hOV).hom.toAlgebra
  let : Algebra Γ(S, W.1) Γ(Z', O) := ((h' ≫ p).appLE W.1 O hOW).hom.toAlgebra
  let : Algebra Γ(X, V.1) Γ(Z, U.1) := (h.appLE V.1 U.1 hUV).hom.toAlgebra
  let : Algebra Γ(Z', O) Γ(Z, U.1) := (i.appLE O U.1 hUO.ge).hom.toAlgebra
  let : Algebra Γ(S, W.1) Γ(Z, U.1) := ((h ≫ p).appLE W.1 U.1 hUW).hom.toAlgebra
  have : IsScalarTower Γ(S, W.1) Γ(X, V.1) Γ(Z', O) :=
    AffineDifferentials.isScalarTower_appLE h' p (h' ≫ p) hcomm W.1 V.1 O hVW hOV hOW
  have : IsScalarTower Γ(S, W.1) Γ(X, V.1) Γ(Z, U.1) :=
    AffineDifferentials.isScalarTower_appLE h p (h ≫ p) hcommh W.1 V.1 U.1 hVW hUV hUW
  have : IsScalarTower Γ(X, V.1) Γ(Z', O) Γ(Z, U.1) :=
    AffineDifferentials.isScalarTower_appLE i h' h hcommi V.1 O U.1 hOV hUO.ge hUV
  let q : Γ(Z', O) →ₐ[Γ(X, V.1)] Γ(Z, U.1) :=
    { toRingHom := (i.appLE O U.1 hUO.ge).hom
      commutes' := fun r =>
        (congrArg (fun g : Γ(X, V.1) →+* Γ(Z, U.1) => g r)
          (AffineDifferentials.appLE_eq_comp_appLE i h' h hcommi V.1 O U.1
            hOV hUO.ge hUV)).symm }
  have hq : Function.Surjective q := by
    have : IsClosedImmersion i := hi.isFirstOrderThickening.1
    have : IsIso (homOfLE hUO.ge : U.1 ⟶ i ⁻¹ᵁ O) := by
      rw [show (homOfLE hUO.ge : U.1 ⟶ i ⁻¹ᵁ O) = eqToHom hUO.symm from
        Subsingleton.elim _ _]
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso (Z.presheaf.map (homOfLE hUO.ge).op)).2.comp
      (i.app_surjective O hO)
  have hbase : Function.Bijective (LinearMap.baseChange Γ(Z, U.1)
      (KaehlerDifferential.mapBaseChange Γ(S, W.1) Γ(X, V.1) Γ(Z', O))) :=
    bijective_baseChange_mapBaseChange q hq rfl
      (AffineDifferentials.appLE_eq_comp_appLE h' p (h' ≫ p) hcomm W.1 V.1 O hVW hOV hOW)
      (isUniversalFirstOrderThickening_specMap_appLE hi U V hO hUO hOV hUV)
  have hMqc : (Scheme.Hom.relativeDifferentials p).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentials p
  have hNqc : (Scheme.Hom.relativeDifferentials (h' ≫ p)).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentials (h' ≫ p)
  have hPMqc : ((Scheme.Modules.pullback h').obj
      (Scheme.Hom.relativeDifferentials p)).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback h' (Scheme.Hom.relativeDifferentials p)
  have hkO : Function.Bijective
      (AffineDifferentials.kaehlerToSections (h' ≫ p) W.1 O hOW).hom := by
    have := AffineDifferentialsIso.isIso_kaehlerToSections (h' ≫ p) hO hOW W.2
    exact ConcreteCategory.bijective_of_isIso _
  have hkV : Function.Bijective
      (AffineDifferentials.kaehlerToSections p W.1 V.1 hVW).hom := by
    have := AffineDifferentialsIso.isIso_kaehlerToSections p V.2 hVW W.2
    exact ConcreteCategory.bijective_of_isIso _
  let kOeq : Ω[Γ(Z', O)⁄Γ(S, W.1)] ≃ₗ[Γ(Z', O)]
      Γ(Scheme.Hom.relativeDifferentials (h' ≫ p), O) :=
    LinearEquiv.ofBijective
      (AffineDifferentials.kaehlerToSections (h' ≫ p) W.1 O hOW).hom hkO
  let kVeq : Ω[Γ(X, V.1)⁄Γ(S, W.1)] ≃ₗ[Γ(X, V.1)]
      Γ(Scheme.Hom.relativeDifferentials p, V.1) :=
    LinearEquiv.ofBijective
      (AffineDifferentials.kaehlerToSections p W.1 V.1 hVW).hom hkV
  let : Module Γ(X, V.1) Γ((Scheme.Modules.pullback h').obj
      (Scheme.Hom.relativeDifferentials p), O) :=
    Module.compHom _ (algebraMap Γ(X, V.1) Γ(Z', O))
  have : IsScalarTower Γ(X, V.1) Γ(Z', O) Γ((Scheme.Modules.pullback h').obj
      (Scheme.Hom.relativeDifferentials p), O) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let ρ : Γ(Scheme.Hom.relativeDifferentials p, V.1) →ₗ[Γ(X, V.1)]
      Γ((Scheme.Modules.pullback h').obj (Scheme.Hom.relativeDifferentials p), O) :=
    { toFun := pullbackSectionHom h' (Scheme.Hom.relativeDifferentials p) V.1 O hOV
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a =>
        pullbackSectionHom_smul h' (Scheme.Hom.relativeDifferentials p) V.1 O hOV r a }
  have hbc : IsBaseChange Γ(Z', O) ρ :=
    ModuleCat.isBaseChange_of_extendScalarsIso (h'.appLE V.1 O hOV).hom rfl
      (affinePullbackSectionsBaseChangeIso h' (Scheme.Hom.relativeDifferentials p) V.2 hO hOV)
      ρ (fun m => affinePullbackSectionsBaseChangeIso_one_tmul h'
        (Scheme.Hom.relativeDifferentials p) V.2 hO hOV m)
  let Teq := (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl Γ(Z', O) Γ(Z', O)) kVeq).trans hbc.equiv
  have hTeq : ∀ x : Ω[Γ(X, V.1)⁄Γ(S, W.1)],
      Teq ((1 : Γ(Z', O)) ⊗ₜ x) = ρ (kVeq x) := by
    intro x
    change hbc.equiv ((1 : Γ(Z', O)) ⊗ₜ kVeq x) = ρ (kVeq x)
    rw [hbc.equiv_tmul, one_smul]
  have hmatrix := AffineDifferentials.relativeDifferentialsMap_app_eq_mapBaseChange
    h' p (h' ≫ p) hcomm W.1 V.1 O hVW hOV hOW Teq.toLinearMap kOeq.toLinearMap
    (fun a => (hTeq (KaehlerDifferential.D Γ(S, W.1) Γ(X, V.1) a)).trans
      (congrArg ρ (AffineDifferentials.kaehlerToSections_d p W.1 V.1 hVW a)))
    (fun c => AffineDifferentials.kaehlerToSections_d (h' ≫ p) W.1 O hOW c)
  set c := Scheme.Hom.relativeDifferentialsMap h' p (h' ≫ p) (𝟙 S) hcomm with hc
  let Φ := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl Γ(Z, U.1) Γ(Z, U.1)) Teq
  let Ψ := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl Γ(Z, U.1) Γ(Z, U.1)) kOeq
  have hsq : ∀ z, LinearMap.baseChange Γ(Z, U.1) (sectionsLinearMap c O) (Φ z) =
      Ψ (LinearMap.baseChange Γ(Z, U.1)
        (KaehlerDifferential.mapBaseChange Γ(S, W.1) Γ(X, V.1) Γ(Z', O)) z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a t =>
        change LinearMap.baseChange Γ(Z, U.1) (sectionsLinearMap c O) (a ⊗ₜ Teq t) = _
        rw [LinearMap.baseChange_tmul, show sectionsLinearMap c O (Teq t) = kOeq
          (KaehlerDifferential.mapBaseChange Γ(S, W.1) Γ(X, V.1) Γ(Z', O) t) from hmatrix t]
        rfl
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  have hbij : Function.Bijective (LinearMap.baseChange Γ(Z, U.1) (sectionsLinearMap c O)) := by
    have hcomp : Function.Bijective
        ((LinearMap.baseChange Γ(Z, U.1) (sectionsLinearMap c O)) ∘ Φ) := by
      have hfe : ((LinearMap.baseChange Γ(Z, U.1) (sectionsLinearMap c O)) ∘ Φ) =
          Ψ ∘ (LinearMap.baseChange Γ(Z, U.1)
            (KaehlerDifferential.mapBaseChange Γ(S, W.1) Γ(X, V.1) Γ(Z', O))) :=
        funext hsq
      rw [hfe]
      exact Ψ.bijective.comp hbase
    exact (EquivLike.bijective_comp Φ _).mp hcomp
  let : Module Γ(Z', O) Γ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback h').obj
      (Scheme.Hom.relativeDifferentials p)), U.1) :=
    Module.compHom _ (algebraMap Γ(Z', O) Γ(Z, U.1))
  have : IsScalarTower Γ(Z', O) Γ(Z, U.1) Γ((Scheme.Modules.pullback i).obj
      ((Scheme.Modules.pullback h').obj (Scheme.Hom.relativeDifferentials p)), U.1) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Module Γ(Z', O) Γ((Scheme.Modules.pullback i).obj
      (Scheme.Hom.relativeDifferentials (h' ≫ p)), U.1) :=
    Module.compHom _ (algebraMap Γ(Z', O) Γ(Z, U.1))
  have : IsScalarTower Γ(Z', O) Γ(Z, U.1) Γ((Scheme.Modules.pullback i).obj
      (Scheme.Hom.relativeDifferentials (h' ≫ p)), U.1) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let ρ₂ : Γ((Scheme.Modules.pullback h').obj (Scheme.Hom.relativeDifferentials p), O)
      →ₗ[Γ(Z', O)] Γ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback h').obj
        (Scheme.Hom.relativeDifferentials p)), U.1) :=
    { toFun := pullbackSectionHom i ((Scheme.Modules.pullback h').obj
        (Scheme.Hom.relativeDifferentials p)) O U.1 hUO.ge
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => pullbackSectionHom_smul i ((Scheme.Modules.pullback h').obj
        (Scheme.Hom.relativeDifferentials p)) O U.1 hUO.ge r a }
  let ρ₃ : Γ(Scheme.Hom.relativeDifferentials (h' ≫ p), O) →ₗ[Γ(Z', O)]
      Γ((Scheme.Modules.pullback i).obj
        (Scheme.Hom.relativeDifferentials (h' ≫ p)), U.1) :=
    { toFun := pullbackSectionHom i (Scheme.Hom.relativeDifferentials (h' ≫ p)) O U.1 hUO.ge
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => pullbackSectionHom_smul i
        (Scheme.Hom.relativeDifferentials (h' ≫ p)) O U.1 hUO.ge r a }
  have hbc₂ : IsBaseChange Γ(Z, U.1) ρ₂ :=
    isBaseChange_pullbackSection i ((Scheme.Modules.pullback h').obj
      (Scheme.Hom.relativeDifferentials p)) hO U.2 hUO.ge rfl ρ₂ (fun _ => rfl)
  have hbc₃ : IsBaseChange Γ(Z, U.1) ρ₃ :=
    isBaseChange_pullbackSection i (Scheme.Hom.relativeDifferentials (h' ≫ p)) hO U.2
      hUO.ge rfl ρ₃ (fun _ => rfl)
  have hkey : ∀ z, sectionsLinearMap ((Scheme.Modules.pullback i).map c) U.1 (hbc₂.equiv z) =
      hbc₃.equiv (LinearMap.baseChange Γ(Z, U.1) (sectionsLinearMap c O) z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a m =>
        rw [hbc₂.equiv_tmul, LinearMap.baseChange_tmul, hbc₃.equiv_tmul, map_smul]
        exact congrArg (fun y => a • y)
          (Scheme.Modules.pullbackSection_naturality i c O U.1 hUO.ge m)
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  refine (EquivLike.bijective_comp hbc₂.equiv
    (sectionsLinearMap ((Scheme.Modules.pullback i).map c) U.1)).mp ?_
  rw [show (sectionsLinearMap ((Scheme.Modules.pullback i).map c) U.1) ∘ hbc₂.equiv =
      hbc₃.equiv ∘ (LinearMap.baseChange Γ(Z, U.1) (sectionsLinearMap c O)) from funext hkey]
  exact hbc₃.equiv.bijective.comp hbij

/-! ### The main result -/

/-- Let `h : Z ⟶ X` be a morphism of schemes over `S` and let `i : Z ⟶ Z'` with structure
morphism `h' : Z' ⟶ X` be a universal first-order thickening of `Z` over `X`. The canonical map
`c_{h'} : (h')^* Ω_{X/S} ⟶ Ω_{Z'/S}` induces an isomorphism `h^* Ω_{X/S} ⟶ Ω_{Z'/S} ⊗ 𝒪_Z`,
namely its restriction along `i`.

Formal unramifiedness of `h`, a hypothesis of the source, is not needed here: it is what makes a
universal first-order thickening exist, and one is given. -/
@[stacks 04FB "the restriction along the inclusion of a universal first-order thickening of the
canonical map on relative differentials is an isomorphism; formal unramifiedness of `h` is not
assumed, a universal first-order thickening being given"]
public theorem isIso_thickeningRelativeDifferentialsMap {Z X Z' S : Scheme.{u}} {h : Z ⟶ X}
    {i : Z ⟶ Z'} {h' : Z' ⟶ X} (hi : IsUniversalFirstOrderThickening h i h') (p : X ⟶ S) :
    IsIso (Scheme.Hom.thickeningRelativeDifferentialsMap i h' p) := by
  refine isIso_of_isIso_app_basis _ (isBasis_compatibleAffineOpens h p) _ (fun U => ?_)
  obtain ⟨V, W, hUV, hVW⟩ := U.2
  let t : UniversalFirstOrderThickening h := ⟨Z', i, h', hi⟩
  have hUO : i ⁻¹ᵁ t.ambientOpens U.1.1 = U.1.1 := t.preimage_ambientOpens U.1.1
  have hOV : t.ambientOpens U.1.1 ≤ h' ⁻¹ᵁ V.1 := t.ambientOpens_le_preimage hUV
  have : IsAffine U.1.1.toScheme := U.1.2
  have hO : IsAffineOpen (t.ambientOpens U.1.1) :=
    isAffine_of_isFirstOrderThickening
      (isUniversalFirstOrderThickening_resLE hi hUO hOV hUV).isFirstOrderThickening
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_app_pullback_relativeDifferentialsMap hi p U.1 V W hO hUO hOV hUV hVW)

/-! ### The ring-level universal property on global sections -/

/-- **A universal first-order thickening of affine schemes is one of rings, on global
sections.**  Let `i : Z ⟶ Z'` with structure morphism `h' : Z' ⟶ X` be a universal first-order
thickening of `h : Z ⟶ X`, all three schemes being affine, and give `Γ(Z')`, `Γ(Z)` the algebra
structures of the comorphisms of `h'`, `h` and `i` on global sections.  Then the surjection
`Γ(Z') → Γ(Z)` is a universal first order thickening of `Γ(Z)` over `Γ(X)`, in the sense of
`Algebra.Extension.IsUniversalFirstOrderThickening`. -/
public theorem isUniversalFirstOrderThickening_ofSurjective_appTop {Z X Z' : Scheme.{u}}
    {h : Z ⟶ X} {i : Z ⟶ Z'} {h' : Z' ⟶ X} (hi : IsUniversalFirstOrderThickening h i h')
    [IsAffine Z] [IsAffine X] [IsAffine Z'] [Algebra Γ(X, ⊤) Γ(Z', ⊤)] [Algebra Γ(X, ⊤) Γ(Z, ⊤)]
    [Algebra Γ(Z', ⊤) Γ(Z, ⊤)] [IsScalarTower Γ(X, ⊤) Γ(Z', ⊤) Γ(Z, ⊤)]
    (hh' : algebraMap Γ(X, ⊤) Γ(Z', ⊤) = h'.appTop.hom)
    (hh : algebraMap Γ(X, ⊤) Γ(Z, ⊤) = h.appTop.hom)
    (hii : algebraMap Γ(Z', ⊤) Γ(Z, ⊤) = i.appTop.hom)
    (hsurj : Function.Surjective (algebraMap Γ(Z', ⊤) Γ(Z, ⊤))) :
    (Algebra.Extension.ofSurjective (IsScalarTower.toAlgHom Γ(X, ⊤) Γ(Z', ⊤) Γ(Z, ⊤))
      hsurj).IsUniversalFirstOrderThickening := by
  have hspec := isUniversalFirstOrderThickening_specMap_appLE hi ⟨⊤, isAffineOpen_top Z⟩
    ⟨⊤, isAffineOpen_top X⟩ (isAffineOpen_top Z') (Scheme.Hom.preimage_top i) le_top le_top
  have e : ∀ {A C : Scheme.{u}} (f : A ⟶ C) (hle : (⊤ : A.Opens) ≤ f ⁻¹ᵁ ⊤),
      f.appLE ⊤ ⊤ hle = f.appTop := fun f _ => by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  change IsUniversalFirstOrderThickening (Spec.map (h.appLE ⊤ ⊤ le_top))
    (Spec.map (i.appLE ⊤ ⊤ le_top)) (Spec.map (h'.appLE ⊤ ⊤ le_top)) at hspec
  rw [e h le_top, e i le_top, e h' le_top] at hspec
  refine isUniversalFirstOrderThickening_extension _ hsurj ?_
  have hq : (IsScalarTower.toAlgHom Γ(X, ⊤) Γ(Z', ⊤) Γ(Z, ⊤)).toRingHom = i.appTop.hom := hii
  rwa [hq, hh, hh']

end Stacks.Thickenings

end
