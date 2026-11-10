module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureRestriction
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.Quasicoherent
public import StacksFrontier.RingTheory.GradedAlgebra.ULiftGrading
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.ULift
public import StacksCore.Tactic.StacksAttribute

/-!
# The projective spectrum is a scheme

For a nonnegatively graded ring, its projective spectrum is a scheme, its positive-degree
homogeneous standard opens are affine, and the sheaf associated to a graded module is
quasi-coherent.

## Main results

* `AlgebraicGeometry.Proj` is the scheme structure on the projective spectrum.
* `AlgebraicGeometry.Proj.basicOpenIsoSpec` identifies a homogeneous standard open with the
  spectrum of the degree-zero homogeneous localization.
* `AlgebraicGeometry.Proj.isAffineOpen_basicOpen` says that these standard opens are affine.
* `AlgebraicGeometry.associatedModuleSheaf_isQuasicoherent` is quasi-coherence of the sheaf
  associated to a graded module when the ring and module lie in the same universe.
* `AlgebraicGeometry.associatedModuleSheafULift_isQuasicoherent` gives the assertion for a ring
  and module in independent universes, using their canonical universe lifts.

## Implementation notes

The scheme and standard-open assertions, including the canonical identification with the
spectrum of a degree-zero localization, are Mathlib's. The associated graded-module sheaf is
the sheaf of degree-zero local homogeneous fractions,
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf`.

Mathlib's quasi-coherence predicate requires the structure ring and the module sheaf to have
the same universe of sections. The instance `associatedModuleSheaf_isQuasicoherent` supplies
that case, and `associatedModuleSheafULift_isQuasicoherent` reduces the general case to it by
placing a ring and a module of independent sizes in their maximum universe with
`Stacks.GradedModule.uliftGrading`, whose gradings are transported along the canonical additive
equivalences.

`AlgebraicGeometry.Scheme.Modules` is a def-copy of `SheafOfModules` over the structure
sheaf, and the two spellings carry different `Category` instance paths: a local instance
stated at one of them is not found by instance search at the other. The helper
`presentationOfIso` therefore names the module and the morphism it transports at the
`SheafOfModules` spelling before calling `SheafOfModules.Presentation.ofIsIso`, which is
what lets its instance arguments be synthesised.

The direct-sum decomposition of the module is an explicit argument of the instance: it is
part of being a graded module, even though the local-fraction sheaf can be constructed
without it.

## References

* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry DirectSum
open CategoryTheory
open Stacks.GradedModule

attribute [local instance] ProjectiveSpectrum.isPrime

universe u v w t r

add_to_stacks 01MB "the projective spectrum is a scheme" AlgebraicGeometry.Proj
add_to_ega "II 2.4.1" "(f)" AlgebraicGeometry.Proj
add_to_ega "II 3.1.1" AlgebraicGeometry.Proj
add_to_ega "II 3.1.3" "special case" AlgebraicGeometry.Proj
add_to_ega "II 7.4.14" "more general" AlgebraicGeometry.Proj
add_to_ega "II 8.3.1" "special case" AlgebraicGeometry.Proj
add_to_ega "III 3.3.1" "special case" AlgebraicGeometry.Proj
add_to_ega "III 4.3.13" AlgebraicGeometry.Proj
add_to_ega "IV 18.12.17" AlgebraicGeometry.Proj
add_to_stacks 01MB "canonical standard-open identification" AlgebraicGeometry.Proj.basicOpenIsoSpec
add_to_sga "6 VI 2.3.2" "(f), special case" AlgebraicGeometry.Proj.basicOpenIsoSpec
add_to_ega "II 2.3.5" AlgebraicGeometry.Proj.basicOpenIsoSpec
add_to_ega "II 2.3.6" "more general" AlgebraicGeometry.Proj.basicOpenIsoSpec
add_to_ega "II 2.4.1" AlgebraicGeometry.Proj.basicOpenIsoSpec
add_to_ega "II 3.1.4" "special case" AlgebraicGeometry.Proj.basicOpenIsoSpec
add_to_ega "II 7.4.14" "partial" AlgebraicGeometry.Proj.basicOpenIsoSpec
add_to_stacks 01MB "standard opens are affine" AlgebraicGeometry.Proj.isAffineOpen_basicOpen
add_to_sga "6 VI 2.3.2" "affineness of D₊(f)" AlgebraicGeometry.Proj.isAffineOpen_basicOpen
add_to_ega "II 2.4.1" "(f)" AlgebraicGeometry.Proj.isAffineOpen_basicOpen
add_to_ega "II 3.1.4" "affineness of X_f over Y" AlgebraicGeometry.Proj.isAffineOpen_basicOpen
add_to_ega "II 5.5.7" "special case" AlgebraicGeometry.Proj.isAffineOpen_basicOpen

local instance : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

private lemma isLocalizedModule_away_of_pow {R P Q : Type*} [CommSemiring R]
    [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q]
    {r : R} (n : ℕ) (hn : 0 < n) (φ : P →ₗ[R] Q)
    (h : IsLocalizedModule.Away (r ^ n) φ) : IsLocalizedModule.Away r φ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let : IsLocalizedModule.Away (r ^ (k + 1)) φ := h
  have hunit : IsUnit (algebraMap R (Module.End R Q) (r ^ (k + 1))) :=
    IsLocalizedModule.map_units (S := Submonoid.powers (r ^ (k + 1))) φ ⟨r ^ (k + 1), 1, by simp⟩
  have hbij : Function.Bijective (fun x : Q => (r ^ (k + 1)) • x) := by
    rwa [Module.End.isUnit_iff] at hunit
  have hpow : r * r ^ k = r ^ (k + 1) := (pow_succ' r k).symm
  have hpow' : r ^ k * r = r ^ (k + 1) := (pow_succ r k).symm
  refine IsLocalizedModule.Away.mk ?_ ?_ ?_
  · rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      apply hbij.1
      simpa [smul_smul, hpow'] using congrArg (fun z : Q => r ^ k • z) hxy
    · intro y
      obtain ⟨x, hx⟩ := hbij.2 y
      exact ⟨r ^ k • x, by change r • r ^ k • x = y; rwa [smul_smul, hpow]⟩
  · intro y
    obtain ⟨l, x, hx⟩ := IsLocalizedModule.Away.surj φ (r ^ (k + 1)) y
    refine ⟨(k + 1) * l, x, ?_⟩
    simpa [pow_mul] using hx
  · intro x y hxy
    obtain ⟨l, hl⟩ := IsLocalizedModule.Away.exists_of_eq (f := φ)
      (r := r ^ (k + 1)) hxy
    refine ⟨(k + 1) * l, ?_⟩
    simpa [pow_mul] using hl

variable {S M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ)
  [SetLike.GradedSMul 𝒮 𝒨]

/-- Multiplying a degree-`n • d` element by a degree-`d` element lands in degree `(n + 1) * d`. -/
private lemma mul_mem_graded_succ_mul {f a : S} {d n : ℕ} (hf : f ∈ 𝒮 d) (ha : a ∈ 𝒮 (n • d)) :
    a * f ∈ 𝒮 ((n + 1) * d) := by
  have h := SetLike.mul_mem_graded ha hf
  simpa [smul_eq_mul, Nat.mul_add, Nat.add_mul, Nat.add_comm,
    Nat.mul_comm, Nat.mul_left_comm] using h

/-- The localization element of `a * f` over `f` is the `d`-th power of `a / f ^ n`. -/
private lemma isLocalizationElem_eq_mk_pow {f a : S} {d n : ℕ} (hf : f ∈ 𝒮 d)
    (ha : a ∈ 𝒮 (n • d)) (hg : a * f ∈ 𝒮 ((n + 1) * d)) :
    HomogeneousLocalization.Away.isLocalizationElem hf hg =
      (HomogeneousLocalization.Away.mk 𝒮 hf n a ha) ^ d := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  simp only [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, pow_mul, mul_pow]
  rw [HomogeneousLocalization.val_pow, HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp [pow_add, mul_pow, mul_assoc, mul_comm, mul_left_comm]

section

variable [Decomposition 𝒨]

private lemma degreeZeroRestriction_isLocalizedModule_away_repr
    {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (n : ℕ) (a : S) (ha : a ∈ 𝒮 (n • d)) :
    let q := HomogeneousLocalization.Away.mk 𝒮 hf n a ha
    let g := a * f
    let e := (n + 1) * d
    let hg : g ∈ 𝒮 e := mul_mem_graded_succ_mul 𝒮 hf ha
    let he : 0 < e := by dsimp [e]; positivity
    let hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f :=
      Proj.basicOpen_mono 𝒮 f g ⟨a, by dsimp [g]; ring⟩
    let φ₀ := ProjectiveSpectrum.degreeZeroRingMap 𝒮 f g
      ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
    let maps := ProjectiveSpectrum.moduleRestrictionMaps 𝒮 𝒨 f g
      ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
    let : Algebra (HomogeneousLocalization.Away 𝒮 f)
        (HomogeneousLocalization.Away 𝒮 g) := φ₀.toRingHom.toAlgebra
    let := Module.compHom (R := HomogeneousLocalization.Away 𝒮 g)
      (GradedModuleDegreeZeroLocalization 𝒮 𝒨 g) φ₀.toRingHom
    IsLocalizedModule.Away q maps.degreeZeroMap := by
  classical
  let q := HomogeneousLocalization.Away.mk 𝒮 hf n a ha
  let g := a * f
  let e := (n + 1) * d
  have hg : g ∈ 𝒮 e := mul_mem_graded_succ_mul 𝒮 hf ha
  have he : 0 < e := by dsimp [e]; positivity
  have hfg : AlgebraicGeometry.Proj.basicOpen 𝒮 g ≤
      AlgebraicGeometry.Proj.basicOpen 𝒮 f :=
    AlgebraicGeometry.Proj.basicOpen_mono 𝒮 f g ⟨a, by dsimp [g]; ring⟩
  let φ₀ := ProjectiveSpectrum.degreeZeroRingMap 𝒮 f g
    ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
  let maps := ProjectiveSpectrum.moduleRestrictionMaps 𝒮 𝒨 f g
    ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
  let : Algebra (HomogeneousLocalization.Away 𝒮 f)
      (HomogeneousLocalization.Away 𝒮 g) := φ₀.toRingHom.toAlgebra
  let := Module.compHom (R := HomogeneousLocalization.Away 𝒮 g)
    (GradedModuleDegreeZeroLocalization 𝒮 𝒨 g) φ₀.toRingHom
  have hloc := ProjectiveSpectrum.isLocalizedModule_degreeZeroMap
    𝒮 𝒨 f g d e hd he hf hg hfg
  have hqpow : HomogeneousLocalization.Away.isLocalizationElem hf hg =
      (HomogeneousLocalization.Away.mk 𝒮 hf n a ha) ^ d :=
    isLocalizationElem_eq_mk_pow 𝒮 hf ha hg
  have hlocalizer :
      HomogeneousLocalization.Away.mk 𝒮 hf e (g ^ d) (by
        simpa [mul_comm] using SetLike.pow_mem_graded d hg) = q ^ d := by
    simpa only [HomogeneousLocalization.Away.isLocalizationElem] using hqpow
  have hlocPow : IsLocalizedModule.Away (q ^ d) maps.degreeZeroMap := by
    rw [← hlocalizer]
    exact hloc
  exact isLocalizedModule_away_of_pow d hd _ hlocPow

private lemma awayι_scalar_top {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d) :
    (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒮 f))).inv ≫
      ((Proj.awayι 𝒮 f hf hd).appIso ⊤).inv ≫
      (AlgebraicGeometry.Proj 𝒮).presheaf.map (eqToHom (show Proj.basicOpen 𝒮 f =
        (Proj.awayι 𝒮 f hf hd) ''ᵁ ⊤ by
        rw [Scheme.Hom.image_top_eq_opensRange, Proj.opensRange_awayι])).op =
      Proj.awayToSection 𝒮 f := by
  let i := Proj.awayι 𝒮 f hf hd
  let e := Proj.basicOpenIsoSpec 𝒮 f hf hd
  have h : e.hom ≫ i = (Proj.basicOpen 𝒮 f).ι := by simp [i, Proj.awayι, e]
  have hi : (⊤ : (Spec (.of (HomogeneousLocalization.Away 𝒮 f))).Opens) ≤
      i ⁻¹ᵁ Proj.basicOpen 𝒮 f := by
    simp [i, ← Proj.opensRange_awayι 𝒮 f hf hd]
  have hh : i.appLE (Proj.basicOpen 𝒮 f) ⊤ hi ≫ e.hom.appTop =
      (Proj.basicOpen 𝒮 f).topIso.inv := by
    have hTop := congrArg (fun z : Γ(Spec (.of (HomogeneousLocalization.Away 𝒮 f)), ⊤) ⟶
        Γ((Proj.basicOpen 𝒮 f).toScheme, e.hom ⁻¹ᵁ ⊤) =>
      i.appLE (Proj.basicOpen 𝒮 f) ⊤ hi ≫ z) (Scheme.Hom.app_eq_appLE e.hom)
    have hAssoc := Scheme.Hom.appLE_comp_appLE e.hom i (Proj.basicOpen 𝒮 f) ⊤
      (e.hom ⁻¹ᵁ ⊤) hi le_rfl
    refine (hTop.trans hAssoc).trans ?_
    simp only [h, Scheme.Opens.ι_appLE]
    rfl
  rw [show e.hom.appTop = (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒮 f ≫
      (Proj.basicOpen 𝒮 f).topIso.inv from Proj.basicOpenToSpec_app_top 𝒮 f] at hh
  simp only [← Category.assoc, Iso.comp_inv_eq, Iso.inv_hom_id] at hh
  have hi_iso : IsIso (i.appLE (Proj.basicOpen 𝒮 f) ⊤ hi) := by
    have htop : i ''ᵁ ⊤ = Proj.basicOpen 𝒮 f := by
      simp [i, Scheme.Hom.image_top_eq_opensRange, Proj.opensRange_awayι]
    have hmap : i.appLE (Proj.basicOpen 𝒮 f) ⊤ hi =
        (AlgebraicGeometry.Proj 𝒮).presheaf.map (eqToHom htop).op ≫ (i.appIso ⊤).hom := by
      simp [Scheme.Hom.appIso_hom']
    rw [hmap]
    infer_instance
  apply (cancel_epi (i.appLE (Proj.basicOpen 𝒮 f) ⊤ hi ≫
    (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒮 f))).hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [Scheme.Hom.appLE_appIso_inv_assoc, ← Functor.map_comp]
  simpa [← Category.assoc] using hh.symm

private noncomputable def imageSectionsIso {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsOpenImmersion i] (N : Y.Modules) (V : X.Opens) (W : Y.Opens)
    (hW : i ''ᵁ V = W) : Γ(N.restrict i, V) ≅ Γ(N, W) :=
  N.restrictAppIso i V ≪≫ N.presheaf.mapIso (eqToIso hW.symm).op

private lemma imageSectionsIso_smul {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsOpenImmersion i] (N : Y.Modules) (V : X.Opens) (W : Y.Opens)
    (hW : i ''ᵁ V = W) (s : Γ(X, V)) (x : Γ(N.restrict i, V)) :
    (imageSectionsIso i N V W hW).hom (s • x) =
      (Y.presheaf.map (eqToHom hW.symm).op ((i.appIso V).inv s)) •
        (imageSectionsIso i N V W hW).hom x := by
  dsimp [imageSectionsIso]
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
  exact N.map_smul _ _ _

private lemma imageSectionsIso_naturality {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsOpenImmersion i] (N : Y.Modules) (V₁ V₂ : X.Opens) (W₁ W₂ : Y.Opens)
    (h₁ : i ''ᵁ V₁ = W₁) (h₂ : i ''ᵁ V₂ = W₂) (hV : V₂ ≤ V₁) (hW : W₂ ≤ W₁) :
    (N.restrict i).presheaf.map (homOfLE hV).op ≫
        (imageSectionsIso i N V₂ W₂ h₂).hom =
      (imageSectionsIso i N V₁ W₁ h₁).hom ≫ N.presheaf.map (homOfLE hW).op := by
  simp only [imageSectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    Category.assoc, Scheme.Modules.map_restrictAppIso_hom_assoc,
    ← Functor.map_comp]
  congr 2

private lemma awayι_scalar {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (V : (Spec (.of (HomogeneousLocalization.Away 𝒮 f))).Opens)
    (W : (AlgebraicGeometry.Proj 𝒮).Opens)
    (hW : (Proj.awayι 𝒮 f hf hd) ''ᵁ V = W) (hWU : W ≤ Proj.basicOpen 𝒮 f) :
    (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒮 f))).inv ≫
      (Spec (.of (HomogeneousLocalization.Away 𝒮 f))).presheaf.map V.leTop.op ≫
      ((Proj.awayι 𝒮 f hf hd).appIso V).inv ≫
      (AlgebraicGeometry.Proj 𝒮).presheaf.map (eqToHom hW.symm).op =
      Proj.awayToSection 𝒮 f ≫
        (AlgebraicGeometry.Proj 𝒮).presheaf.map (homOfLE hWU).op := by
  rw [Scheme.Hom.appIso_inv_naturality_assoc, ← awayι_scalar_top 𝒮 hf hd]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2

private noncomputable def chartDegreeZeroEquiv
    {f g : S} {d e : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (hg : g ∈ 𝒮 e) (he : 0 < e)
    (hfg : Proj.basicOpen 𝒮 g ≤ Proj.basicOpen 𝒮 f)
    (V : (Spec (.of (HomogeneousLocalization.Away 𝒮 f))).Opens)
    (hV : (Proj.awayι 𝒮 f hf hd) ''ᵁ V = Proj.basicOpen 𝒮 g)
    (α : HomogeneousLocalization.Away 𝒮 f →+* HomogeneousLocalization.Away 𝒮 g)
    (hα : CommRingCat.ofHom α ≫ Proj.awayToSection 𝒮 g =
      Proj.awayToSection 𝒮 f ≫ (AlgebraicGeometry.Proj 𝒮).presheaf.map (homOfLE hfg).op) :
    letI := Module.compHom (GradedModuleDegreeZeroLocalization 𝒮 𝒨 g) α
    ((modulesSpecToSheaf.obj ((show (AlgebraicGeometry.Proj 𝒮).Modules from
      ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).restrict
        (Proj.awayι 𝒮 f hf hd))).obj.obj (.op V))
      ≃ₗ[HomogeneousLocalization.Away 𝒮 f] GradedModuleDegreeZeroLocalization 𝒮 𝒨 g := by
  letI := Module.compHom (GradedModuleDegreeZeroLocalization 𝒮 𝒨 g) α
  let N : (AlgebraicGeometry.Proj 𝒮).Modules := ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨
  let i := Proj.awayι 𝒮 f hf hd
  let E := ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hg he
  let I := imageSectionsIso i N V (Proj.basicOpen 𝒮 g) hV
  let A := (AddEquiv.ofBijective I.hom.hom (ConcreteCategory.bijective_of_isIso I.hom)).trans
    E.toAddEquiv
  refine { A with map_smul' := ?_ }
  intro r x
  change E (I.hom (r • x)) = α r • E (I.hom x)
  change E (I.hom (((Spec (.of (HomogeneousLocalization.Away 𝒮 f))).presheaf.map
    V.leTop.op ((Scheme.ΓSpecIso _).inv r)) • (show Γ(N.restrict i, V) from x))) = _
  rw [imageSectionsIso_smul]
  have hscalar := congrArg (fun φ => φ.hom r) (awayι_scalar 𝒮 hf hd V _ hV hfg)
  change (AlgebraicGeometry.Proj 𝒮).presheaf.map _
      ((i.appIso V).inv ((Spec _).presheaf.map _ ((Scheme.ΓSpecIso _).inv r))) =
      (AlgebraicGeometry.Proj 𝒮).presheaf.map _ (Proj.awayToSection 𝒮 f r) at hscalar
  rw [hscalar]
  have hscalar' := congrArg (fun φ => φ.hom r) hα
  change Proj.awayToSection 𝒮 g (α r) =
    (AlgebraicGeometry.Proj 𝒮).presheaf.map _ (Proj.awayToSection 𝒮 f r) at hscalar'
  rw [← hscalar']
  exact E.map_smul (α r) _

private lemma standardOpenEquiv_restrict
    {f g : S} {d e : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (hg : g ∈ 𝒮 e) (he : 0 < e)
    (hfg : Proj.basicOpen 𝒮 g ≤ Proj.basicOpen 𝒮 f)
    (x : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (.op (Proj.basicOpen 𝒮 f))) :
    ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hg he
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.map (homOfLE hfg).op x) =
      (ProjectiveSpectrum.moduleRestrictionMaps 𝒮 𝒨 f g
        ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).degreeZeroMap
        (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd x) := by
  obtain ⟨a, rfl⟩ :=
    (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd).symm.surjective x
  have key : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.map (homOfLE hfg).op
        ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd).symm a) =
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hg he).symm
        ((ProjectiveSpectrum.moduleRestrictionMaps 𝒮 𝒨 f g
          ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).degreeZeroMap a) :=
    ProjectiveSpectrum.Proj.degreeZeroToSection_restriction 𝒮 𝒨 f g
      ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg a
  rw [key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

private lemma associatedModuleSheaf_chart_isLocalized
    {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (hd : 0 < d)
    (q : HomogeneousLocalization.Away 𝒮 f) :
    IsLocalizedModule.Away q ((modulesSpecToSheaf.obj
      ((show (AlgebraicGeometry.Proj 𝒮).Modules from
        ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).restrict
        (Proj.awayι 𝒮 f hf hd))).obj.map (PrimeSpectrum.basicOpen q).leTop.op).hom := by
  classical
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒮 hf q
  let g := a * f
  let e := (n + 1) * d
  have hg : g ∈ 𝒮 e := mul_mem_graded_succ_mul 𝒮 hf ha
  have he : 0 < e := by dsimp [e]; positivity
  have hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f :=
    Proj.basicOpen_mono 𝒮 f g ⟨a, by dsimp [g]; ring⟩
  let φ₀ := ProjectiveSpectrum.degreeZeroRingMap 𝒮 f g
    ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
  let maps := ProjectiveSpectrum.moduleRestrictionMaps 𝒮 𝒨 f g
    ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
  let : Algebra (HomogeneousLocalization.Away 𝒮 f)
      (HomogeneousLocalization.Away 𝒮 g) := φ₀.toRingHom.toAlgebra
  let := Module.compHom (R := HomogeneousLocalization.Away 𝒮 g)
    (GradedModuleDegreeZeroLocalization 𝒮 𝒨 g) φ₀.toRingHom
  have hloc : IsLocalizedModule.Away ((HomogeneousLocalization.Away.mk 𝒮 hf n a ha))
      maps.degreeZeroMap :=
    degreeZeroRestriction_isLocalizedModule_away_repr 𝒮 𝒨 hf hd n a ha
  have hqpow : HomogeneousLocalization.Away.isLocalizationElem hf hg =
      (HomogeneousLocalization.Away.mk 𝒮 hf n a ha) ^ d :=
    isLocalizationElem_eq_mk_pow 𝒮 hf ha hg
  let V : (Spec (.of (HomogeneousLocalization.Away 𝒮 f))).Opens :=
    PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.mk 𝒮 hf n a ha)
  have hV : V = (Proj.awayι 𝒮 f hf hd) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen 𝒮 g := by
    rw [AlgebraicGeometry.Proj.awayι_preimage_basicOpen 𝒮 hf hd hg he]
    change PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.mk 𝒮 hf n a ha) =
      PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem hf hg)
    rw [hqpow, PrimeSpectrum.basicOpen_pow _ d hd]
  have himage :
      (Proj.awayι 𝒮 f hf hd) ''ᵁ V =
        AlgebraicGeometry.Proj.basicOpen 𝒮 g := by
    calc
      _ = (Proj.awayι 𝒮 f hf hd) ''ᵁ
          (Proj.awayι 𝒮 f hf hd) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 g := by rw [hV]
      _ = (Proj.awayι 𝒮 f hf hd).opensRange ⊓ AlgebraicGeometry.Proj.basicOpen 𝒮 g :=
            Scheme.Hom.image_preimage_eq_opensRange_inf _ _
      _ = AlgebraicGeometry.Proj.basicOpen 𝒮 g := by
            rw [AlgebraicGeometry.Proj.opensRange_awayι]
            exact inf_eq_right.mpr hfg
  let N : (AlgebraicGeometry.Proj 𝒮).Modules := ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨
  let i := Proj.awayι 𝒮 f hf hd
  have htop : i ''ᵁ ⊤ = Proj.basicOpen 𝒮 f := by
    rw [Scheme.Hom.image_top_eq_opensRange, Proj.opensRange_awayι]
  let Etop := chartDegreeZeroEquiv 𝒮 𝒨 hf hd hf hd le_rfl ⊤ htop (RingHom.id _) (by simp)
  let EV := chartDegreeZeroEquiv 𝒮 𝒨 hf hd hg he hfg V himage φ₀.toRingHom
    (ProjectiveSpectrum.basicOpenIsoAway_restrict 𝒮 f g d e hf hd hg he hfg)
  let Q := modulesSpecToSheaf.obj (N.restrict i)
  let ψ := (Q.obj.map V.leTop.op).hom
  have hψ : ψ = EV.symm.toLinearMap ∘ₗ maps.degreeZeroMap ∘ₗ Etop.toLinearMap := by
    ext x
    apply EV.injective
    change EV (ψ x) = EV (EV.symm (maps.degreeZeroMap (Etop x)))
    rw [EV.apply_symm_apply]
    change (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hg he)
        ((imageSectionsIso i N V (Proj.basicOpen 𝒮 g) himage).hom
          ((N.restrict i).presheaf.map V.leTop.op x)) =
      maps.degreeZeroMap ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd)
        ((imageSectionsIso i N ⊤ (Proj.basicOpen 𝒮 f) htop).hom x))
    have hn := congrArg (fun k => k.hom x)
      (imageSectionsIso_naturality i N ⊤ V (Proj.basicOpen 𝒮 f)
        (Proj.basicOpen 𝒮 g) htop himage le_top hfg)
    change (imageSectionsIso i N V (Proj.basicOpen 𝒮 g) himage).hom
        ((N.restrict i).presheaf.map V.leTop.op x) =
      N.presheaf.map (homOfLE hfg).op
        ((imageSectionsIso i N ⊤ (Proj.basicOpen 𝒮 f) htop).hom x) at hn
    rw [hn]
    exact standardOpenEquiv_restrict 𝒮 𝒨 hf hd hg he hfg _
  change IsLocalizedModule.Away (HomogeneousLocalization.Away.mk 𝒮 hf n a ha) ψ
  rw [hψ]
  let := hloc
  exact IsLocalizedModule.of_linearEquiv _ _ EV.symm

private noncomputable def presentationOver {X : Scheme.{u}} (N : X.Modules) (U : X.Opens)
    (P : (N.restrict U.ι).Presentation) : (N.over U).Presentation :=
  ProjectiveSpectrum.Proj.presentationOver N U P

/-- Transport a presentation of a sheaf of modules on a scheme along an isomorphism. -/
private noncomputable def presentationOfIso {X : Scheme.{u}} {M N : X.Modules} (α : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let A : SheafOfModules.{u} X.ringCatSheaf := M
  let B : SheafOfModules.{u} X.ringCatSheaf := N
  let φ : A ⟶ B := α.hom
  haveI : IsIso φ := ⟨⟨α.inv, α.hom_inv_id, α.inv_hom_id⟩⟩
  exact SheafOfModules.Presentation.ofIsIso φ P

private noncomputable def presentationOfIsLocalizing {R : CommRingCat.{u}}
    (N : (Spec R).Modules) (h : IsLocalizing (modulesSpecToSheaf.obj N)) : N.Presentation :=
  ProjectiveSpectrum.Proj.presentationOfIsLocalizing N h

end

/-- The sheaf of degree-zero local homogeneous fractions of a graded module on its projective
spectrum is quasi-coherent. -/
@[stacks 01MB "associated graded-module sheaves are quasi-coherent",
  ega "II 3.2.1" "affine base",
  ega "II 3.2.2" "affine base Y"]
instance associatedModuleSheaf_isQuasicoherent [Decomposition 𝒨] :
    SheafOfModules.IsQuasicoherent.{u, u, u}
      (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨) := by
  classical
  let N : (AlgebraicGeometry.Proj 𝒮).Modules := ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨
  have : ∀ j : Σ n : PNat, 𝒮 n,
      IsOpenImmersion (Proj.awayι 𝒮 (j.2 : S) j.2.2 j.1.2) :=
    fun j => Proj.instIsOpenImmersionAwayι 𝒮 (j.2 : S) j.2.2 j.1.2
  apply SheafOfModules.QuasicoherentData.isQuasicoherent
  refine { I := Σ n : PNat, 𝒮 n
           X := fun j => Proj.basicOpen 𝒮 (j.2 : S)
           coversTop := ?_
           presentation := ?_ }
  · refine (_root_.Opens.coversTop_iff _ _).mpr ?_
    change (⨆ j : Σ n : PNat, 𝒮 n, Proj.basicOpen 𝒮 (j.2 : S)) =
      (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)
    have h : (⨆ j : Σ n : PNat, 𝒮 n,
        (Proj.awayι 𝒮 (j.2 : S) j.2.2 j.1.2).opensRange) =
          (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) :=
      (Proj.affineOpenCover 𝒮).openCover.iSup_opensRange
    exact Eq.trans (iSup_congr fun j =>
      (Proj.opensRange_awayι 𝒮 (j.2 : S) j.2.2 j.1.2).symm) h
  · intro j
    let U := Proj.basicOpen 𝒮 (j.2 : S)
    let i := Proj.awayι 𝒮 (j.2 : S) j.2.2 j.1.2
    haveI : IsOpenImmersion i := Proj.instIsOpenImmersionAwayι 𝒮 (j.2 : S) j.2.2 j.1.2
    let e := Proj.basicOpenIsoSpec 𝒮 (j.2 : S) j.2.2 j.1.2
    let P := presentationOfIsLocalizing (N.restrict i)
      (fun q => associatedModuleSheaf_chart_isLocalized 𝒮 𝒨 j.2.2 j.1.2 q)
    let iso : (N.restrict i).restrict e.hom ≅ N.restrict U.ι :=
      ((Scheme.Modules.restrictFunctorComp e.hom i).app N).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (by simp [i, e, U, Proj.awayι])).app N
    exact presentationOver N U (presentationOfIso iso
      (Scheme.Modules.presentationRestrict e.hom P))

/-- For a graded ring and graded module in independent universes, the associated sheaf
is quasi-coherent after canonically lifting both to their maximum universe. -/
theorem associatedModuleSheafULift_isQuasicoherent
    {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
    [CommRing S] [AddCommGroup M] [Module S M]
    [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
    [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
    [SetLike.GradedSMul 𝒮 𝒨] :
    SheafOfModules.IsQuasicoherent.{max u v, max u v, max u v}
      (ProjectiveSpectrum.Proj.associatedModuleSheaf
        (uliftGrading.{u, v} 𝒮) (uliftGrading.{v, u} 𝒨)) :=
  associatedModuleSheaf_isQuasicoherent _ _

end AlgebraicGeometry
