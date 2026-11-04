module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence

/-!
# The affine-local characterization of an effective Cartier divisor

Let `X` be a scheme and `I` a quasi-coherent sheaf of ideals, presented as
`AlgebraicGeometry.Scheme.IdealSheafData`.  The closed subscheme it cuts out is an effective
Cartier divisor exactly when, around every point of its support, there is an affine open
`U = Spec A` on which the subscheme is `Spec (A / fA)` for a nonzerodivisor `f ∈ A`.

## Main definitions

* `Stacks.Divisors.kernelIdealSheaf`: the sheaf of ideals of a closed subscheme presented
  *sectionwise*, as the submodule sheaf `V ↦ ker (𝒪_X(V) ⟶ 𝒪_Z(i⁻¹V))` of the structure sheaf.
* `Stacks.Divisors.kernelIdealSheafIso`: its identification with the categorical kernel
  `Stacks.ClosedImmersion.idealSheaf` that `Stacks.Divisors.IsEffectiveCartierDivisor` is about.

## Main results

* `Stacks.Divisors.ker_app_eq_span_res`: if `I(U) = (f)` on an affine open `U` with `f` a
  nonzerodivisor, then `I(V) = (f|_V)` on *every* open `V ≤ U`, affine or not.
* `Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal`: the closed subscheme is an
  effective Cartier divisor if and only if, around every point of its support, it is the zero
  scheme of a nonzerodivisor on an affine open.

## Implementation notes

On an affine open `U`, the sections of the ideal sheaf are `ker (i.app U) = I(U)`
(`Scheme.IdealSheafData.ker_subschemeι_app`), and a trivialization of the ideal sheaf over `U`
is a nonzerodivisor generating `I(U)`. Since `Stacks.SheafOfModules.isoUnitOver` asks for a
generator over every smaller open, `ker_app_eq_span_res` is proved for an arbitrary open
`V ≤ U`: injectivity of multiplication by `f|_V` is checked on stalks, which are localizations
of `𝒪_X(U)`, and surjectivity by gluing over basic opens.

## References

* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The ideal sheaf, sectionwise -/

/-- The structure-sheaf map `𝒪_X ⟶ i_* 𝒪_Z` of the closed subscheme cut out by `I`, as a
morphism of sheaves of `𝒪_X`-modules. -/
def structureSheafHomOfIdealSheafData :=
  SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom I.subschemeι.toLRSHom.toShHom)

/-- **The sheaf of ideals of a closed subscheme, presented sectionwise.**  Over an open `V` its
sections are the kernel of `𝒪_X(V) ⟶ 𝒪_Z(i⁻¹V)`, as a submodule of `𝒪_X(V)`. -/
def kernelIdealSheaf : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  SheafOfModules.kerObj (structureSheafHomOfIdealSheafData I)

/-- **The sectionwise ideal sheaf is the categorical kernel**
`Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom`. -/
def kernelIdealSheafIso :
    Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom ≅ kernelIdealSheaf I :=
  IsLimit.conePointUniqueUpToIso
    (kernelIsKernel (structureSheafHomOfIdealSheafData I))
    (SheafOfModules.kerIsLimit (structureSheafHomOfIdealSheafData I))

/-- The section of the structure sheaf underlying a section of the sectionwise ideal sheaf. -/
def kernelSection {V : X.Opens} (z : (kernelIdealSheaf I).val.obj (op V)) : Γ(X, V) := z.1

/-- The underlying section of a section of the sectionwise ideal sheaf is killed by `i.app`. -/
theorem kernelSection_mem {V : X.Opens} (z : (kernelIdealSheaf I).val.obj (op V)) :
    kernelSection I z ∈ RingHom.ker (I.subschemeι.app V).hom := z.2

/-- A section of the sectionwise ideal sheaf is determined by its underlying section. -/
theorem kernelSection_injective {V : X.Opens} :
    Function.Injective (kernelSection I (V := V)) := fun _ _ h => Subtype.ext h

/-- Taking the underlying section commutes with scalar multiplication. -/
theorem kernelSection_smul {V : X.Opens} (c : Γ(X, V))
    (z : (kernelIdealSheaf I).val.obj (op V)) :
    kernelSection I (c • z) = c * kernelSection I z := rfl

/-- Taking the underlying section commutes with restriction. -/
theorem kernelSection_res {V W : X.Opens} (h : W ≤ V)
    (z : (kernelIdealSheaf I).val.obj (op V)) :
    kernelSection I (((kernelIdealSheaf I).val.map (homOfLE h).op).hom z)
      = (X.presheaf.map (homOfLE h).op).hom (kernelSection I z) := rfl

/-- A section of the structure sheaf killed by `i.app` is a section of the sectionwise ideal
sheaf. -/
def mkKernelSection {V : X.Opens} (s : Γ(X, V))
    (hs : s ∈ RingHom.ker (I.subschemeι.app V).hom) :
    (kernelIdealSheaf I).val.obj (op V) := ⟨s, hs⟩

/-- The underlying section of `mkKernelSection I s hs` is `s`. -/
@[simp]
theorem kernelSection_mkKernelSection {V : X.Opens} (s : Γ(X, V))
    (hs : s ∈ RingHom.ker (I.subschemeι.app V).hom) :
    kernelSection I (mkKernelSection I s hs) = s := rfl

/-! ### The ideal on the rings of sections -/

/-- Restriction carries a section of the ideal sheaf to a section of the ideal sheaf. -/
theorem mem_ker_app_res {V W : X.Opens} (h : W ≤ V) {s : Γ(X, V)}
    (hs : s ∈ RingHom.ker (I.subschemeι.app V).hom) :
    (X.presheaf.map (homOfLE h).op).hom s ∈ RingHom.ker (I.subschemeι.app W).hom := by
  have hnat := I.subschemeι.naturality (U := W) (U' := V) (homOfLE h).op
  have h2 := congrArg (fun φ : Γ(X, V) ⟶ _ => φ.hom s) hnat
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [RingHom.mem_ker] at hs ⊢
  rw [h2, hs, map_zero]

/-- **A nonzerodivisor on an affine open has nonzerodivisor germs.** -/
theorem germ_mem_nonZeroDivisors {U : X.Opens} (hU : IsAffineOpen U) {f : Γ(X, U)}
    (hf : IsRegular f) (y : X) (hy : y ∈ U) :
    (X.presheaf.germ U y hy).hom f ∈ nonZeroDivisors (X.presheaf.stalk y) := by
  let _ := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  have _ := hU.isLocalization_stalk (⟨y, hy⟩ : U)
  have hg : (algebraMap Γ(X, U) (X.presheaf.stalk y)) f
      = (X.presheaf.germ U y hy).hom f := rfl
  rw [← hg]
  exact IsLocalization.map_nonZeroDivisors_le
    (hU.primeIdealOf (⟨y, hy⟩ : U)).asIdeal.primeCompl (X.presheaf.stalk y)
    ⟨f, isRegular_iff_mem_nonZeroDivisors.mp hf, rfl⟩

/-- **Multiplication by a nonzerodivisor on an affine open is injective on every smaller
open.** -/
theorem injective_mul_res {U : X.Opens} (hU : IsAffineOpen U) {f : Γ(X, U)}
    (hf : IsRegular f) (V : X.Opens) (hVU : V ≤ U) :
    Function.Injective
      (fun c : Γ(X, V) => c * (X.presheaf.map (homOfLE hVU).op).hom f) := by
  intro c c' hc
  refine TopCat.Presheaf.section_ext X.sheaf V c c' fun y hy => ?_
  have hreg := germ_mem_nonZeroDivisors hU hf y (hVU hy)
  have hgerm : (X.presheaf.germ V y hy).hom ((X.presheaf.map (homOfLE hVU).op).hom f)
      = (X.presheaf.germ U y (hVU hy)).hom f :=
    X.presheaf.germ_res_apply (homOfLE hVU) y hy f
  have h2 := congrArg (fun z => (X.presheaf.germ V y hy).hom z) hc
  simp only [map_mul, hgerm] at h2
  exact (mul_cancel_right_mem_nonZeroDivisors hreg).mp h2

/-- On a basic open of an affine open, a principal ideal sheaf is generated by the restriction
of its generator. -/
theorem ker_app_basicOpen_eq_span {U : X.affineOpens} {f : Γ(X, U.1)}
    (hgen : I.ideal U = Ideal.span {f}) (g : Γ(X, U.1)) :
    RingHom.ker (I.subschemeι.app (X.basicOpen g)).hom
      = Ideal.span {(X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom f} := by
  have h1 := I.ker_subschemeι_app (X.affineBasicOpen g)
  have h2 := I.map_ideal (X.affineBasicOpen_le g)
  rw [hgen, Ideal.map_span, Set.image_singleton] at h2
  exact h1.trans h2.symm

/-- **A principal ideal sheaf on an affine open is principal on every smaller open.**  If
`I(U) = (f)` with `f` a nonzerodivisor then `I(V) = (f|_V)` for every open `V ≤ U`, affine or
not. -/
theorem ker_app_eq_span_res {U : X.Opens} (hU : IsAffineOpen U) {f : Γ(X, U)}
    (hf : IsRegular f) (hgen : I.ideal ⟨U, hU⟩ = Ideal.span {f})
    (V : X.Opens) (hVU : V ≤ U) :
    RingHom.ker (I.subschemeι.app V).hom
      = Ideal.span {(X.presheaf.map (homOfLE hVU).op).hom f} := by
  classical
  have hfU : f ∈ RingHom.ker (I.subschemeι.app U).hom := by
    rw [I.ker_subschemeι_app ⟨U, hU⟩, hgen]
    exact Ideal.mem_span_singleton_self f
  refine le_antisymm ?_ ?_
  · intro s hs
    choose g hgle hgmem using fun y : V => hU.exists_basicOpen_le y (hVU y.2)
    set W : V → X.Opens := fun y => X.basicOpen (g y) with hWdef
    have hWU : ∀ y, W y ≤ U := fun y => X.basicOpen_le (g y)
    have hcover : V ≤ iSup W := fun y hy =>
      TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hgmem ⟨y, hy⟩⟩
    have hloc : ∀ y : V, ∃ c : Γ(X, W y),
        (X.presheaf.map (homOfLE (hgle y)).op).hom s
          = (X.presheaf.map (homOfLE (hWU y)).op).hom f * c := by
      intro y
      have hmem := mem_ker_app_res I (hgle y) hs
      rw [ker_app_basicOpen_eq_span I hgen (g y)] at hmem
      exact Ideal.mem_span_singleton.mp hmem
    choose c hc using hloc
    have hcompat : TopCat.Presheaf.IsCompatible X.presheaf W c := by
      intro y y'
      have hle : W y ⊓ W y' ≤ U := le_trans inf_le_left (hWU y)
      apply injective_mul_res hU hf (W y ⊓ W y') hle
      have e1 : (X.presheaf.map (TopologicalSpace.Opens.infLELeft (W y) (W y')).op).hom
            ((X.presheaf.map (homOfLE (hWU y)).op).hom f)
          = (X.presheaf.map (homOfLE hle).op).hom f := by
        rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]; congr 2
      have e2 : (X.presheaf.map (TopologicalSpace.Opens.infLERight (W y) (W y')).op).hom
            ((X.presheaf.map (homOfLE (hWU y')).op).hom f)
          = (X.presheaf.map (homOfLE hle).op).hom f := by
        rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]; congr 2
      have k1 := congrArg
        (fun z => (X.presheaf.map (TopologicalSpace.Opens.infLELeft (W y) (W y')).op).hom z)
        (hc y)
      have k2 := congrArg
        (fun z => (X.presheaf.map (TopologicalSpace.Opens.infLERight (W y) (W y')).op).hom z)
        (hc y')
      simp only [map_mul, e1, e2] at k1 k2
      have hres : (X.presheaf.map (TopologicalSpace.Opens.infLELeft (W y) (W y')).op).hom
            ((X.presheaf.map (homOfLE (hgle y)).op).hom s)
          = (X.presheaf.map (TopologicalSpace.Opens.infLERight (W y) (W y')).op).hom
            ((X.presheaf.map (homOfLE (hgle y')).op).hom s) := by
        rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp,
          ← CommRingCat.comp_apply, ← X.presheaf.map_comp]; congr 3
      rw [hres, k2] at k1
      exact (mul_comm _ _).trans (k1.symm.trans (mul_comm _ _))
    have key : ∀ d : Γ(X, V),
        (∀ y : V, (X.presheaf.map (homOfLE (hgle y)).op).hom d = c y) →
        s = (X.presheaf.map (homOfLE hVU).op).hom f * d := by
      intro d hd
      refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf W V (fun y => homOfLE (hgle y)) hcover
        s _ fun y => ?_
      have hfres : (X.presheaf.map (homOfLE (hgle y)).op).hom
            ((X.presheaf.map (homOfLE hVU).op).hom f)
          = (X.presheaf.map (homOfLE (hWU y)).op).hom f := by
        rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]; congr 2
      show (X.presheaf.map (homOfLE (hgle y)).op).hom s
          = (X.presheaf.map (homOfLE (hgle y)).op).hom
            ((X.presheaf.map (homOfLE hVU).op).hom f * d)
      rw [map_mul, hfres, hd y]
      exact hc y
    obtain ⟨c₀, hc₀, -⟩ :=
      X.sheaf.existsUnique_gluing' W V (fun y => homOfLE (hgle y)) hcover c hcompat
    exact Ideal.mem_span_singleton.mpr ⟨c₀, key c₀ hc₀⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact mem_ker_app_res I hVU hfU

/-! ### Trivializing the ideal sheaf over an affine open -/

/-- **A nonzerodivisor generating the ideal trivializes the ideal sheaf**: multiplication by
the restriction of `f` is a bijection from `𝒪_X(V)` to the sections of the sectionwise ideal
sheaf over every open `V ≤ U`. -/
theorem bijective_smul_mkKernelSection {U : X.Opens} (hU : IsAffineOpen U) {f : Γ(X, U)}
    (hf : IsRegular f) (hgen : I.ideal ⟨U, hU⟩ = Ideal.span {f})
    (hfU : f ∈ RingHom.ker (I.subschemeι.app U).hom)
    (V : X.Opens) (hVU : V ≤ U) :
    Function.Bijective (fun c : Γ(X, V) =>
      c • ((kernelIdealSheaf I).val.map (homOfLE hVU).op).hom (mkKernelSection I f hfU)) := by
  refine ⟨fun c c' hcc => ?_, fun z => ?_⟩
  · exact injective_mul_res hU hf V hVU (congrArg (kernelSection I) hcc)
  · have hz := kernelSection_mem I z
    rw [ker_app_eq_span_res I hU hf hgen V hVU] at hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hz
    exact ⟨c, kernelSection_injective I ((mul_comm _ _).trans hc.symm)⟩

/-- The sectionwise ideal sheaf is trivial over an affine open on which the ideal is generated
by a nonzerodivisor. -/
def kernelIdealSheafOverIsoUnit {U : X.Opens} (hU : IsAffineOpen U) {f : Γ(X, U)}
    (hf : IsRegular f) (hgen : I.ideal ⟨U, hU⟩ = Ideal.span {f})
    (hfU : f ∈ RingHom.ker (I.subschemeι.app U).hom) :
    (kernelIdealSheaf I).over U
      ≅ SheafOfModules.unit ((structureSheafRing X.toRingedSpace).over U) :=
  Stacks.SheafOfModules.isoUnitOver (kernelIdealSheaf I) U (mkKernelSection I f hfU)
    (bijective_smul_mkKernelSection I hU hf hgen hfU)

/-- The ideal sheaf itself — the categorical kernel — is trivial over such an affine open. -/
def idealSheafOverIsoUnit {U : X.Opens} (hU : IsAffineOpen U) {f : Γ(X, U)}
    (hf : IsRegular f) (hgen : I.ideal ⟨U, hU⟩ = Ideal.span {f})
    (hfU : f ∈ RingHom.ker (I.subschemeι.app U).hom) :
    (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom).over U
      ≅ SheafOfModules.unit ((structureSheafRing X.toRingedSpace).over U) :=
  (SheafOfModules.overFunctor (structureSheafRing X.toRingedSpace) U).mapIso
      (kernelIdealSheafIso I) ≪≫
    kernelIdealSheafOverIsoUnit I hU hf hgen hfU

/-- A generator of the ideal on an affine open is killed by `i.app`. -/
theorem mem_ker_app_of_ideal_eq_span {U : X.Opens} (hU : IsAffineOpen U) {f : Γ(X, U)}
    (hgen : I.ideal ⟨U, hU⟩ = Ideal.span {f}) :
    f ∈ RingHom.ker (I.subschemeι.app U).hom := by
  rw [I.ker_subschemeι_app ⟨U, hU⟩, hgen]
  exact Ideal.mem_span_singleton_self f

/-- Around a point off the support, the ideal is the unit ideal on a basic open. -/
theorem exists_basicOpen_ideal_eq_top (U : X.affineOpens) (x : X) (hxU : x ∈ U.1)
    (hxI : x ∉ I.supportSet) :
    ∃ g : Γ(X, U.1), x ∈ X.basicOpen g ∧ I.ideal (X.affineBasicOpen g) = ⊤ := by
  have hz : x ∉ X.zeroLocus (U := U.1) (I.ideal U) := fun hzero =>
    hxI ((I.mem_supportSet_iff_of_mem hxU).2 hzero)
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe] at hz
  obtain ⟨g, hg⟩ := not_forall.mp hz
  obtain ⟨hgj, hgb⟩ := not_imp.mp hg
  have hxg : x ∈ X.basicOpen g := by simpa using hgb
  have hWU : X.affineBasicOpen g ≤ U := X.affineBasicOpen_le g
  let rho : Γ(X, U.1) →+* Γ(X, (X.affineBasicOpen g).1) :=
    (X.presheaf.map (homOfLE hWU).op).hom
  let _ : Algebra Γ(X, U.1) Γ(X, (X.affineBasicOpen g).1) := rho.toAlgebra
  have _ : IsLocalization.Away g Γ(X, (X.affineBasicOpen g).1) :=
    U.2.isLocalization_of_eq_basicOpen g (homOfLE hWU) rfl
  have hunit : IsUnit (rho g) := IsLocalization.Away.algebraMap_isUnit g
  refine ⟨g, hxg, ?_⟩
  calc I.ideal (X.affineBasicOpen g) = Ideal.map rho (I.ideal U) := (I.map_ideal hWU).symm
    _ = ⊤ := Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem rho hgj) hunit

/-- Around a point off the support, the ideal is generated on an affine open by `1`. -/
theorem exists_affineOpen_ideal_eq_span_of_notMem_support (x : X) (hx : x ∉ I.supportSet) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      ∃ f : Γ(X, U), IsRegular f ∧ I.ideal ⟨U, hU⟩ = Ideal.span {f} := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨g, hxg, htop⟩ := exists_basicOpen_ideal_eq_top I ⟨V, hV⟩ x hxV hx
  refine ⟨(X.affineBasicOpen (U := ⟨V, hV⟩) g).1, (X.affineBasicOpen (U := ⟨V, hV⟩) g).2,
    hxg, 1, isRegular_one, ?_⟩
  exact htop.trans Ideal.span_singleton_one.symm

/-- The ideal of an effective Cartier divisor is, around every point, generated on an affine
open by a nonzerodivisor. -/
theorem exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
    (h : IsEffectiveCartierDivisor I) (x : X) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      ∃ f : Γ(X, U), IsRegular f ∧ I.ideal ⟨U, hU⟩ = Ideal.span {f} := by
  have hlocal : ∀ z : X.toRingedSpace.carrier,
      IsLocalRing (ringStalk X.toRingedSpace z) := fun z => X.isLocalRing z
  have hinv : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2 h
  have hinv' : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (kernelIdealSheaf I) :=
    Stacks.SheafOfModules.isInvertible_of_iso _ _ (kernelIdealSheafIso I)
  obtain ⟨W, hxW, a, ha⟩ :=
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible
      (X := X.toRingedSpace) (kernelIdealSheaf I) x
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  have hbij := ha U hUW
  set aU := ((kernelIdealSheaf I).val.map (homOfLE hUW).op).hom a with haU
  refine ⟨U, hU, hxU, kernelSection I aU, ?_, ?_⟩
  · have hinj : ∀ y : Γ(X, U), y * kernelSection I aU = 0 → y = 0 :=
      fun y hy => hbij.1 (kernelSection_injective I
        (hy.trans (zero_mul _).symm))
    exact isRegular_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff.mpr
      ⟨fun y hy => hinj y ((mul_comm _ _).trans hy), hinj⟩)
  · rw [← I.ker_subschemeι_app ⟨U, hU⟩]
    refine le_antisymm (fun t ht => ?_) ?_
    · obtain ⟨c, hcs⟩ := hbij.2 (mkKernelSection I t ht)
      exact Ideal.mem_span_singleton'.mpr ⟨c, congrArg (kernelSection I) hcs⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact kernelSection_mem I aU

/-! ### The chart -/

/-- The ideals of `I` on equal affine opens are heterogeneously equal. -/
theorem ideal_heq {U V : X.affineOpens} (h : U = V) : HEq (I.ideal U) (I.ideal V) := by
  cases h; rfl

/-- The ideal of the pullback of `I` to an affine open `U`, on the whole of `U`, is the ideal of
`I` on `U`. -/
theorem ideal_comap_top_heq (U : X.affineOpens) :
    HEq ((I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1⟩) (I.ideal U) := by
  have hU : (⟨(Scheme.Hom.opensFunctor U.1.ι).obj ⊤,
      (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩ : X.affineOpens) = U :=
    Subtype.ext (Scheme.Opens.ι_image_top U.1)
  have h1 : HEq ((I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1⟩)
      (I.ideal ⟨(Scheme.Hom.opensFunctor U.1.ι).obj ⊤,
        (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩) := by
    have h := I.ideal_comap_of_isOpenImmersion U.1.ι ⟨⊤, isAffineOpen_top U.1⟩
    rw [Scheme.Opens.ι_appIso] at h
    exact heq_of_eq h
  exact h1.trans (ideal_heq I hU)

/-- Heterogeneously equal ring maps and ideals have heterogeneously equal preimages. -/
theorem comap_ideal_heq {A A' B B' : CommRingCat.{u}}
    {f : A ⟶ B} {g : A' ⟶ B'} {J : Ideal B} {K : Ideal B'}
    (hA : A = A') (hB : B = B') (hf : HEq f.hom g.hom) (hJ : HEq J K) :
    HEq (Ideal.comap f.hom J) (Ideal.comap g.hom K) := by
  cases hA; cases hB
  obtain rfl : f = g := CommRingCat.hom_ext (eq_of_heq hf)
  obtain rfl : J = K := eq_of_heq hJ
  rfl

/-- Heterogeneously equal morphisms of commutative rings have heterogeneously equal underlying
ring maps. -/
theorem commRingCatHom_heq {A A' B B' : CommRingCat.{u}}
    {f : A ⟶ B} {g : A' ⟶ B'} (hA : A = A') (hB : B = B') (h : f ≍ g) :
    HEq f.hom g.hom := by
  cases hA; cases hB; cases h; rfl

/-- **A chart detects the ideal.**  If the intersection of the closed subscheme with an affine
open `U` is, compatibly with the closed immersion, `Spec (Γ(X, U) / K)`, then `I(U) = K`. -/
theorem ideal_eq_quotient_of_chart (U : X.Opens) (hU : IsAffineOpen U) (K : Ideal Γ(X, U))
    (e : pullback I.subschemeι U.ι ≅ Spec (.of (Γ(X, U) ⧸ K)))
    (he : pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) :
    I.ideal ⟨U, hU⟩ = K := by
  let U' : X.affineOpens := ⟨U, hU⟩
  let j : U'.1.toScheme ⟶ X := U.ι
  let I' : U'.1.toScheme.IdealSheafData := I.comap j
  let e' : I'.subscheme ≅ Spec (.of (Γ(X, U) ⧸ K)) :=
    I.comapIso j ≪≫ pullbackSymmetry j I.subschemeι ≪≫ e
  have hcomm : I'.subschemeι ≫ hU.isoSpec.hom =
      e'.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) := by
    dsimp [e', I']
    rw [← Scheme.IdealSheafData.comapIso_hom_fst]
    show (I.comapIso j).hom ≫ (pullback.fst j I.subschemeι ≫ hU.isoSpec.hom) =
      (I.comapIso j).hom ≫ ((pullbackSymmetry j I.subschemeι).hom ≫ e.hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))
    apply (cancel_epi (I.comapIso j).hom).2
    simp only [← pullbackSymmetry_hom_comp_snd, Category.assoc]
    exact congrArg (fun k => (pullbackSymmetry j I.subschemeι).hom ≫ k) he
  have hm : I'.map hU.isoSpec.hom =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).ker := by
    show (I'.subschemeι ≫ hU.isoSpec.hom).ker = _
    rw [hcomm, Scheme.Hom.ker_comp_of_isIso e'.hom]
  let _ : IsAffine U'.1.toScheme := hU
  have hleft : (I'.map hU.isoSpec.hom).ideal ⟨⊤, isAffineOpen_top _⟩ =
      ((I'.ideal ⟨⊤, isAffineOpen_top _⟩).comap
        (CommRingCat.Hom.hom (Scheme.Hom.appTop hU.isoSpec.hom))) :=
    Scheme.IdealSheafData.ideal_map_of_isAffineHom I' hU.isoSpec.hom ⟨⊤, isAffineOpen_top _⟩
  let q : CommRingCat.of (Γ(X, U)) ⟶ CommRingCat.of (Γ(X, U) ⧸ K) :=
    CommRingCat.ofHom (Ideal.Quotient.mk K)
  let gammaA := Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U)))
  let gammaQ := Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ K))
  have hnat : (Spec.map q).appTop ≫ gammaQ.hom = gammaA.hom ≫ q := by
    simp [q, gammaA, gammaQ]
  have hnat' : gammaQ.hom.hom.comp (CommRingCat.Hom.hom ((Spec.map q).appTop)) =
      q.hom.comp gammaA.hom.hom := congrArg CommRingCat.Hom.hom hnat
  have hker : RingHom.ker (CommRingCat.Hom.hom ((Spec.map q).appTop)) =
      Ideal.comap gammaA.hom.hom K := by
    calc
      RingHom.ker (CommRingCat.Hom.hom ((Spec.map q).appTop)) =
          RingHom.ker (gammaQ.hom.hom.comp (CommRingCat.Hom.hom ((Spec.map q).appTop))) :=
            (RingHom.ker_equiv_comp _ gammaQ.commRingCatIsoToRingEquiv).symm
      _ = RingHom.ker (q.hom.comp gammaA.hom.hom) := by rw [hnat']
      _ = Ideal.comap gammaA.hom.hom K := by
        show Ideal.comap gammaA.hom.hom (RingHom.ker q.hom) = _
        simp [q]
  have htop : (I'.map hU.isoSpec.hom).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.comap gammaA.hom.hom K := by
    rw [hm, Scheme.Hom.ker_apply]
    exact hker
  have htop' : (I'.ideal ⟨⊤, isAffineOpen_top _⟩).comap
        (CommRingCat.Hom.hom (Scheme.Hom.appTop hU.isoSpec.hom)) =
      Ideal.comap gammaA.hom.hom K :=
    hleft.symm.trans htop
  have hA : Γ(U'.1, ⊤) = Γ(X, U'.1) := by
    show Γ(X, U'.1.ι ''ᵁ (⊤ : U'.1.toScheme.Opens)) = Γ(X, U'.1)
    rw [Scheme.Opens.ι_image_top]
  have hbase := ideal_comap_top_heq I U'
  have hB : Γ(X, U'.1.ι ''ᵁ (⊤ : U'.1.toScheme.Opens)) = Γ(X, U'.1) := by
    rw [Scheme.Opens.ι_image_top]
  have hcomp : HEq (CommRingCat.Hom.hom (Scheme.Hom.appTop hU.isoSpec.hom))
      (CommRingCat.Hom.hom gammaA.hom) := by
    have htopIso : U'.1.topIso.inv = eqToHom hB.symm := by
      show X.presheaf.map (eqToHom U'.1.ι_image_top).op = eqToHom hB.symm
      rw [eqToHom_op, eqToHom_map]
    apply commRingCatHom_heq rfl hB
    rw [IsAffineOpen.isoSpec_hom_appTop, htopIso]
    exact CategoryTheory.comp_eqToHom_heq gammaA.hom hB.symm
  have htransport := comap_ideal_heq (A := Γ(Spec (.of (Γ(X, U))), ⊤))
    (A' := Γ(Spec (.of (Γ(X, U))), ⊤)) (B := Γ(U'.1, ⊤)) (B' := Γ(X, U'.1))
    (f := Scheme.Hom.appTop hU.isoSpec.hom) (g := gammaA.hom)
    (J := I'.ideal ⟨⊤, isAffineOpen_top _⟩) (K := I.ideal U') rfl hA hcomp hbase
  apply Ideal.comap_injective_of_surjective gammaA.hom.hom
    gammaA.commRingCatIsoToRingEquiv.surjective
  exact eq_of_heq (htransport.symm.trans (heq_of_eq htop'))

/-- **A principal ideal produces a chart.**  If `I(U) = (f)` on an affine open `U`, then the
intersection of the closed subscheme with `U` is, compatibly with the closed immersion,
`Spec (Γ(X, U) / (f))`. -/
theorem exists_quotient_chart_of_ideal_span (U : X.Opens) (hU : IsAffineOpen U) (f : Γ(X, U))
    (hgen : I.ideal ⟨U, hU⟩ = Ideal.span {f}) :
    ∃ e : pullback I.subschemeι U.ι ≅ Spec (.of (Γ(X, U) ⧸ Ideal.span {f})),
      pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) := by
  let g := pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom
  have hg : IsClosedImmersion g := by dsimp [g]; infer_instance
  obtain ⟨K, e0, he0⟩ := (IsClosedImmersion.Spec_iff (f := g)).mp hg
  have hKS : K = Ideal.span {f} :=
    (ideal_eq_quotient_of_chart I U hU K e0 he0).symm.trans hgen
  let qEquiv : (Γ(X, U) ⧸ K) ≃+* (Γ(X, U) ⧸ Ideal.span {f}) :=
    (Ideal.quotientEquivAlgOfEq ℤ hKS).toRingEquiv
  let qIso : CommRingCat.of (Γ(X, U) ⧸ K) ≅ CommRingCat.of (Γ(X, U) ⧸ Ideal.span {f}) :=
    qEquiv.toCommRingCatIso
  have hquot : CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})) ≫ qIso.inv =
      CommRingCat.ofHom (Ideal.Quotient.mk K) := by
    apply CommRingCat.hom_ext
    ext a
    apply qEquiv.injective
    simp [qEquiv, qIso, Ideal.quotientEquivAlgOfEq_mk]
  refine ⟨e0 ≪≫ asIso (Spec.map qIso.inv), ?_⟩
  show g = (e0.hom ≫ Spec.map qIso.inv) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
  rw [Category.assoc, ← Spec.map_comp, hquot]
  exact he0

/-! ### The characterization -/

/-- A sheaf of ideals that is generated by a nonzerodivisor on an affine open around every
point of the scheme cuts out an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_of_forall_exists_affineOpen
    (h : ∀ x : X, ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      ∃ f : Γ(X, U), IsRegular f ∧ I.ideal ⟨U, hU⟩ = Ideal.span {f}) :
    IsEffectiveCartierDivisor I := by
  classical
  choose U hU hxU f hf hgen using h
  refine (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1 ?_
  refine Stacks.SheafOfModules.isInvertible_of_coversTop_nonempty_iso_unit
    X.presheaf (structureSheafRing X.toRingedSpace).property _ (X := U) ?_ ?_
  · refine (Opens.coversTop_iff (X : Type u) U).2 (TopologicalSpace.IsOpenCover.mk ?_)
    exact eq_top_iff.2 fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hxU z⟩
  · exact fun x => ⟨idealSheafOverIsoUnit I (hU x) (hf x) (hgen x)
      (mem_ker_app_of_ideal_eq_span I (hU x) (hgen x))⟩

/-- A closed subscheme is an effective Cartier divisor if and only if it is locally, on affine
neighbourhoods of its support, the zero scheme of a nonzerodivisor. -/
@[stacks 01WS]
theorem isEffectiveCartierDivisor_iff_affineLocal :
    IsEffectiveCartierDivisor I ↔
      ∀ x ∈ I.supportSet,
        ∃ (U : X.Opens) (hU : IsAffineOpen U),
          x ∈ (U : Set X) ∧
            ∃ f : Γ(X, U), IsRegular f ∧
              ∃ e : pullback I.subschemeι U.ι ≅
                  Spec (.of (Γ(X, U) ⧸ Ideal.span {f})),
                pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom =
                  e.hom ≫ Spec.map
                    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) := by
  classical
  refine ⟨fun hC x _ => ?_, fun hlocal => ?_⟩
  · obtain ⟨U, hU, hxU, f, hf, hgen⟩ :=
      exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor I hC x
    obtain ⟨e, he⟩ := exists_quotient_chart_of_ideal_span I U hU f hgen
    exact ⟨U, hU, hxU, f, hf, e, he⟩
  · refine isEffectiveCartierDivisor_of_forall_exists_affineOpen I fun x => ?_
    by_cases hx : x ∈ I.supportSet
    · obtain ⟨U, hU, hxU, f, hf, e, he⟩ := hlocal x hx
      exact ⟨U, hU, hxU, f, hf, ideal_eq_quotient_of_chart I U hU _ e he⟩
    · exact exists_affineOpen_ideal_eq_span_of_notMem_support I x hx

end Stacks.Divisors

end
