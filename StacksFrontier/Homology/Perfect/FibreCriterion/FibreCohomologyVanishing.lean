module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.PseudoCoherent.Locality
import Mathlib
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Splitting from vanishing of a fibre cohomology module

The derived fibre `K ⊗_R^L κ(p)` of a pseudo-coherent object `K` of `D(R)` at a prime `p`, the
fibrewise conditions `FibreCohomologyVanishes` and `CohomologyBaseChangeSurjective`, projective
amplitude and the splitting lemma for distinguished triangles, derived localization of
cohomology, spreading out from the fibre, bounded finite projective representatives of the upper
truncation, and the splitting criterion [stacks 068U]
(`StacksDraft.Perfect.exists_localization_iso_biprod_truncGE_truncLE`).

Part of `StacksFrontier.Homology.Perfect.FibreCriterion`; see that module for the overview.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

-- The truncation and base-change identifications below read instances through iterated
-- `mapHomologicalComplex` and `opcycles` isomorphisms; this needs the pre-4.x defeq transparency.
set_option backward.isDefEq.respectTransparency false

namespace StacksDraft.Perfect

universe u v

/-! ### The derived fibre of a pseudo-coherent complex -/

/-- Termwise extension of scalars of a cochain complex of `R`-modules to the residue field at a
prime `p`. When the complex is bounded above with finite free terms this computes the derived
base change `- ⊗_R^L κ(p)`. -/
noncomputable def residueFieldComplex {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    CochainComplex (ModuleCat.{max u v} p.ResidueField) ℤ :=
  ((ModuleCat.extendScalars (algebraMap R p.ResidueField)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P

/-- The degree-`i` cohomology of the derived fibre `K ⊗_R^L κ(p)` vanishes.

The derived fibre is computed on a bounded-above finite free representative of `K`, whose
termwise extension of scalars to `κ(p)` represents `K ⊗_R^L κ(p)`. -/
def FibreCohomologyVanishes {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (i : ℤ) : Prop :=
  ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
    StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
      IsZero ((residueFieldComplex.{u, v} p P).homology i)

/-- The canonical map `H^i(K) ⊗_R κ(p) → H^i(K ⊗_R^L κ(p))` is surjective.

The derived fibre is computed on a bounded-above finite free representative `P` of `K`.
Surjectivity is spelled out by requiring every degree-`i` cohomology class of
`residueFieldComplex p P` to be represented by a cocycle in the image of the extension of scalars
of the cocycles of `P`; by right exactness of extension of scalars this is exactly surjectivity of
the displayed map. -/
def CohomologyBaseChangeSurjective {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (i : ℤ) : Prop :=
  ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
    StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
      (let F := ModuleCat.extendScalars (algebraMap R p.ResidueField)
      let Pκ := residueFieldComplex.{u, v} p P
      ∀ x : Pκ.cycles i, ∃ y : F.obj (P.cycles i),
        ∃ hy : Pκ.d i (i + 1) (F.map (P.iCycles i) y) = 0,
          Pκ.homologyπ i (Pκ.cyclesMk (F.map (P.iCycles i) y) (i + 1) (by simp) hy) =
            Pκ.homologyπ i x)

/-! ### Projective amplitude and the splitting lemma -/

/-- An object of `D(R)` has projective amplitude in `[a, b]` when it is represented by a complex
of projective modules concentrated in degrees `a` through `b` ([stacks 0A5N]). -/
@[sga "6 I 4.12.1" "special case"]
def HasProjectiveAmplitude {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ) : Prop :=
  ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
    Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
      (∀ i : ℤ, Module.Projective R (P.X i)) ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b

/-- An object of projective amplitude in `[a, b]` admits no nonzero morphism to an object
supported in degrees `≤ a - 1`. -/
private lemma hom_eq_zero_of_hasProjectiveAmplitude_of_isLE
    {R : Type u} [Ring R] (K L : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ)
    (hL : HasProjectiveAmplitude.{u, v} L a b) [K.IsLE (a - 1)] :
    ∀ f : L ⟶ K, f = 0 := by
  rintro f
  obtain ⟨P, ⟨eP⟩, hPproj, hPge, hPle⟩ := hL
  obtain ⟨X, hXle, ⟨eX⟩⟩ := K.exists_iso_Q_obj_of_isLE (a - 1)
  let (i : ℤ) : Module.Projective R (P.X i) := hPproj i
  let : P.IsStrictlyGE a := hPge
  let : P.IsStrictlyLE b := hPle
  let : X.IsStrictlyLE (a - 1) := hXle
  let : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  let qf := (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).hom.app P ≫
    eP.hom ≫ f ≫ eX.hom ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).inv.app X
  obtain ⟨q, hq⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).obj X)).surjective qf
  obtain ⟨φ, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).map_surjective q
  have hφ : φ = 0 := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : a ≤ i
    · apply (X.isZero_of_isStrictlyLE (a - 1) i (by omega)).eq_of_tgt
    · apply (P.isZero_of_isStrictlyGE a i (by omega)).eq_of_src
  subst φ
  dsimp [qf] at hq
  simp only [Functor.map_zero] at hq
  have hq' := congrArg (fun z ↦
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).inv.app P ≫ z ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).hom.app X) hq
  have hf' : eP.hom ≫ f ≫ eX.hom = 0 := by simpa using hq'.symm
  rw [← cancel_epi eP.hom, ← cancel_mono eX.hom]
  simpa only [Category.assoc, comp_zero, zero_comp] using hf'

/-- Vanishing of cohomology in all degrees `≥ a` places an object in degrees `≤ a - 1`. -/
private lemma isLE_of_homology_isZero
    {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat.{max u v} R)) (a : ℤ)
    (hK : ∀ i : ℤ, a ≤ i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K)) :
    K.IsLE (a - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact hK i (by omega)

/-- Two splittings of the same distinguished triangle compatible with its maps agree. -/
lemma compatible_iso_unique
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (K M L : C) (f : K ⟶ M) (g : M ⟶ L) (h : L ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang C) (hzero : ∀ q : L ⟶ K, q = 0)
    (e₁ e₂ : M ≅ K ⊞ L)
    (he₁ : f ≫ e₁.hom = biprod.inl ∧ g = e₁.hom ≫ biprod.snd)
    (he₂ : f ≫ e₂.hom = biprod.inl ∧ g = e₂.hom ≫ biprod.snd) : e₁ = e₂ := by
  apply Iso.ext
  apply biprod.hom_ext
  · have hz : f ≫ (e₁.hom ≫ biprod.fst - e₂.hom ≫ biprod.fst) = 0 := by
      simp only [Preadditive.comp_sub, ← Category.assoc, he₁.1, he₂.1,
        biprod.inl_fst, sub_self]
    obtain ⟨q, hq⟩ := (Triangle.mk f g h).yoneda_exact₂ hT
      (e₁.hom ≫ biprod.fst - e₂.hom ≫ biprod.fst) hz
    have hd : e₁.hom ≫ biprod.fst - e₂.hom ≫ biprod.fst = 0 := by
      rw [hq, hzero q, comp_zero]
    exact sub_eq_zero.mp hd
  · exact he₁.2.symm.trans he₂.2

/-- If `L` has projective amplitude in `[a, b]` then morphisms from `L` into an object with
vanishing cohomology in degrees `≥ a` are zero, and a distinguished triangle
`K ⟶ M ⟶ L ⟶ K⟦1⟧` with `H^j(K) = 0` for `j ≥ a + 1` splits, uniquely so when `H^j(K) = 0` for
`j ≥ a` ([stacks 0BCG]). -/
theorem hom_eq_zero_and_existsUnique_iso_biprod
    {R : Type u} [Ring R] (K L : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ)
    (hL : HasProjectiveAmplitude.{u, v} L a b) :
    ((∀ i : ℤ, a ≤ i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K)) →
        ∀ f : L ⟶ K, f = 0) ∧
      ((∀ i : ℤ, a + 1 ≤ i →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K)) →
        ∀ (M : DerivedCategory (ModuleCat.{max u v} R)) (f : K ⟶ M) (g : M ⟶ L)
          (h : L ⟶ K⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang _ →
            ∃ e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ g = e.hom ≫ biprod.snd) ∧
      ((∀ i : ℤ, a ≤ i →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K)) →
        ∀ (M : DerivedCategory (ModuleCat.{max u v} R)) (f : K ⟶ M) (g : M ⟶ L)
          (h : L ⟶ K⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang _ →
            ∃! e : M ≅ K ⊞ L, f ≫ e.hom = biprod.inl ∧ g = e.hom ≫ biprod.snd) := by
  have vanish (K' : DerivedCategory (ModuleCat.{max u v} R)) [K'.IsLE (a - 1)] :
      ∀ q : L ⟶ K', q = 0 :=
    hom_eq_zero_of_hasProjectiveAmplitude_of_isLE K' L a b hL
  have hh0 (K' : DerivedCategory (ModuleCat.{max u v} R)) [K'.IsLE a]
      (h : L ⟶ K'⟦(1 : ℤ)⟧) : h = 0 := by
    have : (K'⟦(1 : ℤ)⟧).IsLE (a - 1) :=
      DerivedCategory.TStructure.t.isLE_shift K' a 1 (a - 1) (by omega)
    exact vanish _ h
  refine ⟨fun hK ↦ @vanish K (isLE_of_homology_isZero K a hK), ?_, ?_⟩
  · intro hK M f g h hT
    have : K.IsLE a := by simpa using isLE_of_homology_isZero K (a + 1) hK
    exact exists_iso_binaryBiproduct_of_distTriang (Triangle.mk f g h) hT (hh0 K h)
  · intro hK M f g h hT
    have : K.IsLE (a - 1) := isLE_of_homology_isZero K a hK
    have : K.IsLE a := DerivedCategory.TStructure.t.isLE_of_le K (a - 1) a (by omega)
    obtain ⟨e, he⟩ :=
      exists_iso_binaryBiproduct_of_distTriang (Triangle.mk f g h) hT (hh0 K h)
    exact ⟨e, he, fun e' he' ↦ compatible_iso_unique K M L f g h hT (vanish K) e' e he' he⟩

/-! ### Derived localization and cohomology -/

/-- The canonical natural isomorphism `H^i(K ⊗_R R_f) ≅ H^i(K) ⊗_R R_f`: derived localization is
exact, so it commutes with the cohomology functors of the derived category. -/
noncomputable def localizationAwayHomologyFunctorIso {R : Type u} [CommRing R] (f : R) (i : ℤ) :
    PseudoCoherence.localizationAwayFunctorAux.{u, v} f ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{max u v} (Localization.Away f)) i ≅
      DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i ⋙
        ModuleCat.extendScalars (algebraMap R (Localization.Away f)) := by
  let F := ModuleCat.extendScalars.{u, u, max v u} (algebraMap R (Localization.Away f))
  letI : F.Additive := extendScalars_additive.{u, u, max v u} _
  letI : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away f) (Submonoid.powers f)))
  letI : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u}
      (algebraMap R (Localization.Away f))).leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  exact PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i

/-! ### Spreading out from the fibre

If the differential out of the degree-`i` opcycles stays injective after passing to the residue
field at `p`, then on a principal neighbourhood of `p` the degree-`i + 1` opcycles become
projective and the degree-`i` cohomology vanishes. -/

/-- Injectivity after base change of a map induced on a quotient, from exactness of the tensored
two-step complex it comes from. -/
private lemma lTensor_injective_of_exact_lTensor
    {R : Type u} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    {X₀ X₁ X₂ Z : Type*} [AddCommGroup X₀] [Module R X₀] [AddCommGroup X₁] [Module R X₁]
    [AddCommGroup X₂] [Module R X₂] [AddCommGroup Z] [Module R Z]
    (d₀ : X₀ →ₗ[R] X₁) (d₁ : X₁ →ₗ[R] X₂) (π : X₁ →ₗ[R] Z) (d : Z →ₗ[R] X₂)
    (hπ : Function.Surjective π) (hex : Function.Exact d₀ π) (hd : d ∘ₗ π = d₁)
    (hS : ∀ x, d₁.lTensor S x = 0 → ∃ y, d₀.lTensor S y = x) :
    Function.Injective (d.lTensor S) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective S hπ y
  have hx : d₁.lTensor S x = 0 := by
    rwa [← hd, LinearMap.lTensor_comp, LinearMap.comp_apply]
  obtain ⟨y, rfl⟩ := hS x hx
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hex.linearMap_comp_eq_zero,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- Injectivity after base change to `κ(p)` is inherited by the localization at `p`. -/
lemma lTensor_residueField_localization_injective
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (d : M →ₗ[R] N) (hinj : Function.Injective (d.lTensor p.ResidueField)) :
    Function.Injective ((LinearMap.baseChange (Localization.AtPrime p) d).lTensor
      (IsLocalRing.ResidueField (Localization.AtPrime p))) := by
  let A := Localization.AtPrime p
  rw [← LinearMap.baseChange_eq_lTensor]
  have hfib : Function.Injective (LinearMap.baseChange p.ResidueField d) := by
    rwa [LinearMap.baseChange_eq_lTensor]
  change Function.Injective
    (LinearMap.baseChange p.ResidueField (LinearMap.baseChange A d))
  rw [LinearMap.baseChange_baseChange]
  exact ((TensorProduct.AlgebraTensorModule.cancelBaseChange R A p.ResidueField
    p.ResidueField N).symm.injective.comp hfib).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A p.ResidueField
      p.ResidueField M).injective

/-- If `d` stays injective after base change to `κ(p)`, some element outside `p` annihilates the
kernel of `d`. -/
private lemma exists_smul_eq_zero_of_lTensor_residueField_injective
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {Z X : Type*} [AddCommGroup Z] [Module R Z] [AddCommGroup X] [Module R X]
    [Module.Finite R Z] [Module.Finite R X] [Module.Free R X]
    (d : Z →ₗ[R] X) (hinj : Function.Injective (d.lTensor p.ResidueField)) :
    ∃ r ∉ p, ∀ z, d z = 0 → r • z = 0 := by
  let A := Localization.AtPrime p
  obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (LinearMap.baseChange A d)).mpr (lTensor_residueField_localization_injective p d hinj)
  let fZ := TensorProduct.mk R A Z 1
  let fX := TensorProduct.mk R A X 1
  have : Module.FinitePresentation R X := Module.finitePresentation_of_projective R X
  obtain ⟨h, s, hh⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    p.primeCompl fZ ((l'.restrictScalars R) ∘ₗ fX)
  have hcomp : fZ ∘ₗ (h ∘ₗ d) = fZ ∘ₗ ((s : R) • LinearMap.id) := by
    ext z
    have h1 := congrArg (fun φ : X →ₗ[R] A ⊗[R] Z => φ (d z)) hh
    simp only [LinearMap.comp_apply] at h1 ⊢
    rw [h1]
    have h2 := congrArg (fun φ : A ⊗[R] Z →ₗ[A] A ⊗[R] Z => φ (1 ⊗ₜ z)) hl'
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.id_apply] at h2
    simp [fX, fZ, h2, Submonoid.smul_def, TensorProduct.smul_tmul']
  obtain ⟨t, ht⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    p.primeCompl fZ _ _ hcomp
  refine ⟨(t : R) * s, fun hmem => ((inferInstance : p.IsPrime).mem_or_mem hmem).elim t.2 s.2,
    fun z hz => ?_⟩
  have := congrArg (fun φ : Z →ₗ[R] Z => φ z) ht
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, hz, map_zero, smul_zero,
    LinearMap.id_apply] at this
  rw [mul_smul]
  exact this.symm

/-- If `δ` stays injective after base change to `κ(p)`, then its cokernel is free in a
neighbourhood of `p`. -/
private lemma mem_freeLocus_of_lTensor_residueField_injective
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {Z X W : Type*} [AddCommGroup Z] [Module R Z] [AddCommGroup X] [Module R X]
    [AddCommGroup W] [Module R W]
    [Module.Finite R Z] [Module.Finite R X] [Module.Free R X]
    (δ : Z →ₗ[R] X) (q : X →ₗ[R] W) (hq : Function.Surjective q)
    (hex : ∀ x, q x = 0 ↔ x ∈ LinearMap.range δ)
    (hinj : Function.Injective (δ.lTensor p.ResidueField)) :
    (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ Module.freeLocus R W := by
  let A := Localization.AtPrime p
  let ι := (LinearMap.range δ).subtype
  have hιinj : Function.Injective (ι.lTensor p.ResidueField) := by
    have hρ := LinearMap.lTensor_surjective p.ResidueField δ.surjective_rangeRestrict
    have hcomp : ι ∘ₗ δ.rangeRestrict = δ := LinearMap.subtype_comp_codRestrict _ _ _
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    obtain ⟨z, rfl⟩ := hρ w
    have : δ.lTensor p.ResidueField z = 0 := by
      rwa [← hcomp, LinearMap.lTensor_comp, LinearMap.comp_apply]
    rw [hinj (this.trans (map_zero _).symm), map_zero]
  have hexι : Function.Exact ι q := fun x =>
    (hex x).trans ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩
  have hqA : Function.Surjective (LinearMap.baseChange A q) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective A hq
  have hexA : Function.Exact (LinearMap.baseChange A ι) (LinearMap.baseChange A q) := by
    simpa only [LinearMap.baseChange_eq_lTensor] using lTensor_exact A hexι hq
  have : Module.Free A (A ⊗[R] W) :=
    Module.free_of_lTensor_residueField_injective
      (LinearMap.baseChange A ι) (LinearMap.baseChange A q) hqA hexA
      (lTensor_residueField_localization_injective p ι hιinj)
  exact (Module.mem_freeLocus_iff_tensor _ A).mpr this

/-- The differential into degree `j` is exact with the projection onto the degree-`j` opcycles. -/
lemma exact_d_pOpcycles {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (i j : ℤ) (hij : i + 1 = j) :
    Function.Exact (P.d i j).hom (P.pOpcycles j).hom := by
  intro x
  have h := (P.sc j).moduleCat_pOpcycles_eq_zero_iff x
  change (P.pOpcycles j).hom x = 0 ↔ ∃ y : P.X ((ComplexShape.up ℤ).prev j),
    (P.d ((ComplexShape.up ℤ).prev j) j).hom y = x at h
  rwa [(ComplexShape.up ℤ).prev_eq' hij] at h

/-- A module annihilated by an element that becomes a unit after base change dies after that
base change. -/
private lemma subsingleton_tensor_of_smul_eq_zero
    {R : Type u} [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {H : Type*} [AddCommGroup H] [Module R H] (r : R) (hr : IsUnit (algebraMap R A r))
    (hH : ∀ h : H, r • h = 0) : Subsingleton (A ⊗[R] H) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul a h =>
    obtain ⟨w, hw⟩ := hr
    have ha : a = r • ((↑w⁻¹ : A) * a) := by
      rw [Algebra.smul_def, ← hw, ← mul_assoc, Units.mul_inv, one_mul]
    rw [ha, TensorProduct.smul_tmul, hH, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- Vanishing of the degree-`i` cohomology of `residueFieldComplex p P` says that the tensored
differentials of `P` are exact at degree `i`. -/
private lemma exists_lTensor_residueField_eq_of_isZero_homology
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ)
    (hz : IsZero ((residueFieldComplex.{u, v} p P).homology i)) :
    ∀ x : p.ResidueField ⊗[R] P.X i, (P.d i (i + 1)).hom.lTensor p.ResidueField x = 0 →
      ∃ y, (P.d (i - 1) i).hom.lTensor p.ResidueField y = x := by
  let κ := p.ResidueField
  let Pκ := residueFieldComplex.{u, v} p P
  have hex := (Pκ.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).mp
    ((Pκ.exactAt_iff_isZero_homology i).mpr hz)
  have hexf : Function.Exact (Pκ.d (i - 1) i).hom (Pκ.d i (i + 1)).hom := by
    intro x
    constructor
    · intro hx
      exact (ShortComplex.moduleCat_exact_iff _).mp hex x hx
    · rintro ⟨y, rfl⟩
      change (Pκ.d (i - 1) i ≫ Pκ.d i (i + 1)).hom y = 0
      rw [Pκ.d_comp_d]
      rfl
  change (let := (algebraMap R κ).toAlgebra;
    Function.Exact (LinearMap.baseChange κ (P.d (i - 1) i).hom)
      (LinearMap.baseChange κ (P.d i (i + 1)).hom)) at hexf
  rw [toAlgebra_algebraMap] at hexf
  simp only [LinearMap.baseChange_eq_lTensor] at hexf
  exact fun x hx => (hexf x).mp hx

/-- An element `r` with `D(f) ⊆ D(r)` becomes a unit in `R_f`. -/
private lemma isUnit_algebraMap_away_of_basicOpen_le {R : Type u} [CommRing R] {f r : R}
    (h : PrimeSpectrum.basicOpen f ≤ PrimeSpectrum.basicOpen r) :
    IsUnit (algebraMap R (Localization.Away f) r) := by
  obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff f r).mp h
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hn
  have hfn : IsUnit (algebraMap R (Localization.Away f) (f ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit f).pow n
  rw [← hs, map_mul] at hfn
  exact isUnit_of_mul_isUnit_right hfn

/-- If `P` is a complex of finite free modules and `residueFieldComplex p P` has vanishing
degree-`i` cohomology, then there is `f ∉ p` such that the degree-`i + 1` opcycles of `P` become
projective over `R_f` and the degree-`i` cohomology of `P` vanishes after base change to `R_f`. -/
private lemma exists_away_projective_opcycles_and_subsingleton_homology
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ)
    (hP : ∀ j : ℤ, Module.Finite R (P.X j) ∧ Module.Free R (P.X j))
    (hz : IsZero ((residueFieldComplex.{u, v} p P).homology i)) :
    ∃ f : R, f ∉ p ∧
      Module.Projective (Localization.Away f) (Localization.Away f ⊗[R] P.opcycles (i + 1)) ∧
      Subsingleton (Localization.Away f ⊗[R] P.homology i) := by
  have hFin (j : ℤ) : Module.Finite R (P.X j) := (hP j).1
  have hFree (j : ℤ) : Module.Free R (P.X j) := (hP j).2
  let κ := p.ResidueField
  let π := (P.pOpcycles i).hom
  let dbar := (P.fromOpcycles i (i + 1)).hom
  have hπ : Function.Surjective π :=
    (ModuleCat.epi_iff_surjective (P.pOpcycles i)).mp inferInstance
  have hexπ : Function.Exact (P.d (i - 1) i).hom π := exact_d_pOpcycles P (i - 1) i (by simp)
  have hd : dbar ∘ₗ π = (P.d i (i + 1)).hom := by
    change (P.pOpcycles i ≫ P.fromOpcycles i (i + 1)).hom = _
    rw [P.p_fromOpcycles]
  have hinj : Function.Injective (dbar.lTensor κ) :=
    lTensor_injective_of_exact_lTensor κ _ _ π dbar hπ hexπ hd
      (exists_lTensor_residueField_eq_of_isZero_homology p P i hz)
  have : Module.Finite R (P.opcycles i) := Module.Finite.of_surjective π hπ
  obtain ⟨r, hr, hker⟩ := exists_smul_eq_zero_of_lTensor_residueField_injective p dbar hinj
  let q := (P.pOpcycles (i + 1)).hom
  have hq : Function.Surjective q :=
    (ModuleCat.epi_iff_surjective (P.pOpcycles (i + 1))).mp inferInstance
  have hdq : Function.Exact (P.d i (i + 1)).hom q := exact_d_pOpcycles P i (i + 1) rfl
  have hrange : LinearMap.range dbar = LinearMap.range (P.d i (i + 1)).hom := by
    rw [← hd, LinearMap.range_comp, LinearMap.range_eq_top.mpr hπ, Submodule.map_top]
  have hfree := mem_freeLocus_of_lTensor_residueField_injective p dbar q hq
    (fun x => by rw [hrange]; exact hdq x) hinj
  have : Module.FinitePresentation R (P.opcycles (i + 1)) :=
    Module.finitePresentation_of_free_of_surjective q hq
      (by
        rw [hdq.linearMap_ker_eq, LinearMap.range_eq_map]
        exact Module.Finite.fg_top.map _)
  let x : PrimeSpectrum R := ⟨p, inferInstance⟩
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := x) (u := Module.freeLocus R (P.opcycles (i + 1)) ∩ PrimeSpectrum.basicOpen r)
      ⟨hfree, hr⟩ ((Module.isOpen_freeLocus).inter (PrimeSpectrum.basicOpen r).isOpen)
  refine ⟨f, hxf, ?_, ?_⟩
  · have hproj := (Module.basicOpen_subset_freeLocus_iff (M := P.opcycles (i + 1))).mp
      (hfU.trans Set.inter_subset_left)
    exact Module.Projective.of_equiv
      (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)
        (IsLocalizedModule.iso (Submonoid.powers f)
          ((TensorProduct.mk R (Localization.Away f) (P.opcycles (i + 1))) 1)))
  · have hle : PrimeSpectrum.basicOpen f ≤ PrimeSpectrum.basicOpen r :=
      fun y hy => (hfU hy).2
    refine subsingleton_tensor_of_smul_eq_zero _ r
      (isUnit_algebraMap_away_of_basicOpen_le hle) fun h => ?_
    apply (ModuleCat.mono_iff_injective (P.homologyι i)).mp inferInstance
    rw [map_smul, map_zero]
    apply hker
    change (P.homologyι i ≫ P.fromOpcycles i (i + 1)).hom h = 0
    rw [P.homologyι_comp_fromOpcycles]
    rfl

/-! ### Bounded finite projective representatives of the upper truncation -/

/-- Tensoring with a module cannot create cohomology below a strict lower bound. -/
lemma isZero_tensorComplex_homology_of_isStrictlyGE
    {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (a : ℤ)
    (hP : P.IsStrictlyGE a) (M : ModuleCat.{max u v} A) (j : ℤ) (hj : j < a) :
    IsZero ((TorAmplitude.tensorComplex P M).homology j) := by
  let F := TorAmplitude.tensorRightMixed (R := A) M
  have hQ : (TorAmplitude.tensorComplex P M).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro k hk
    exact F.map_isZero ((P.isStrictlyGE_iff a).mp hP k hk)
  let : (TorAmplitude.tensorComplex P M).IsStrictlyGE a := hQ
  exact ((TorAmplitude.tensorComplex P M).exactAt_of_isGE a j hj).isZero_homology

/-- The truncation of a bounded complex of finite projectives with projective degree-`n` opcycles
is a bounded complex of finite projectives in degrees `≥ n`. -/
@[ega "III 7.7.12" "partial"]
private lemma truncGE_bounded_finite_projective
    {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (n b : ℤ)
    (hLE : P.IsStrictlyLE b)
    (hFinite : ∀ j : ℤ, Module.Finite A (P.X j))
    (hProjective : ∀ j : ℤ, Module.Projective A (P.X j))
    (hOpFinite : Module.Finite A (P.opcycles n))
    (hOpProjective : Module.Projective A (P.opcycles n)) :
    (P.truncGE n).IsStrictlyGE n ∧
      (P.truncGE n).IsStrictlyLE (max n b) ∧
      (∀ j : ℤ, Module.Finite A ((P.truncGE n).X j)) ∧
      (∀ j : ℤ, Module.Projective A ((P.truncGE n).X j)) := by
  let Q := P.truncGE n
  have hQGE : Q.IsStrictlyGE n := inferInstance
  have hQLE : Q.IsStrictlyLE (max n b) := by
    rw [Q.isStrictlyLE_iff]
    intro j hj
    have hnj : n < j := lt_of_le_of_lt (le_max_left n b) hj
    have hbj : b < j := lt_of_le_of_lt (le_max_right n b) hj
    have hzero : IsZero (P.X j) := (P.isStrictlyLE_iff b).mp hLE j hbj
    exact hzero.of_iso (P.truncGEXIso n j hnj)
  have hQ : ∀ j : ℤ, Module.Finite A (Q.X j) ∧ Module.Projective A (Q.X j) := by
    intro j
    by_cases hj : j < n
    · let : Subsingleton (Q.X j) := ModuleCat.subsingleton_of_isZero
        ((Q.isStrictlyGE_iff n).mp hQGE j hj)
      exact ⟨inferInstance, inferInstance⟩
    · by_cases heq : j = n
      · subst j
        exact ⟨Module.Finite.equiv (P.truncGEXIsoOpcycles n).toLinearEquiv.symm,
          Module.Projective.of_equiv' (P.truncGEXIsoOpcycles n).toLinearEquiv.symm⟩
      · have hnj : n < j := by omega
        exact ⟨Module.Finite.equiv (P.truncGEXIso n j hnj).toLinearEquiv.symm,
          Module.Projective.of_equiv' (P.truncGEXIso n j hnj).toLinearEquiv.symm⟩
  exact ⟨hQGE, hQLE, fun j ↦ (hQ j).1, fun j ↦ (hQ j).2⟩

/-- The canonical truncation of the derived-category image of a complex is the image of the
truncated complex. -/
private lemma truncGE_Q_obj_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    (P : CochainComplex C ℤ) (n : ℤ) :
    Nonempty ((DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (P.truncGE n)) := by
  let h := P.shortComplexTruncLE_shortExact (n - 1)
  let T := DerivedCategory.triangleOfSES h
  let e₃ : T.obj₃ ≅ DerivedCategory.Q.obj (P.truncGE n) :=
    asIso (DerivedCategory.Q.map (P.shortComplexTruncLEX₃ToTruncGE (n - 1) n (by omega)))
  have h₃ : T.obj₃.IsGE n := DerivedCategory.TStructure.t.isGE_of_iso e₃.symm n
  obtain ⟨e, -⟩ := DerivedCategory.TStructure.t.triangle_iso_exists
    (DerivedCategory.TStructure.t.triangleLTGE_distinguished n (DerivedCategory.Q.obj P))
    (DerivedCategory.triangleOfSES_distinguished h) (Iso.refl _) (n - 1) n
    (by infer_instance) (by infer_instance)
    (by
      change (DerivedCategory.Q.obj (P.truncLE (n - 1))).IsLE (n - 1)
      infer_instance) h₃
  exact ⟨Triangle.π₃.mapIso e ≪≫ e₃⟩

/-- Once the degree-`n` opcycles become projective after localizing away from `f`, the upper
truncation of the localization of a bounded-above finite free complex is represented by a bounded
complex of finite projective `R_f`-modules in degrees `≥ n`. -/
lemma localized_upper_representative
    {R : Type u} [CommRing R] (f : R)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (n b : ℤ)
    (hLE : P.IsStrictlyLE b)
    (hFinite : ∀ j : ℤ, Module.Finite R (P.X j))
    (hFree : ∀ j : ℤ, Module.Free R (P.X j))
    (hOpProjective : Module.Projective (Localization.Away f)
      (Localization.Away f ⊗[R] (P.opcycles n))) :
    ∃ Q : CochainComplex (ModuleCat.{max u v} (Localization.Away f)) ℤ,
      Q.IsStrictlyGE n ∧ Q.IsStrictlyLE (max n b) ∧
      (∀ j : ℤ, Module.Finite (Localization.Away f) (Q.X j)) ∧
      (∀ j : ℤ, Module.Projective (Localization.Away f) (Q.X j)) ∧
      Nonempty ((DerivedCategory.TStructure.t.truncGE n).obj
        ((PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj (DerivedCategory.Q.obj P)) ≅
        DerivedCategory.Q.obj Q) := by
  let A := Localization.Away f
  let F := ModuleCat.extendScalars (algebraMap R A)
  let : F.Additive := extendScalars_additive.{u, u, max v u} _
  let : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' _
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A (Submonoid.powers f)))
  let : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u} (algebraMap R A)).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  let Pf : CochainComplex (ModuleCat.{max u v} A) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hPfLE : Pf.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact F.map_isZero ((P.isStrictlyLE_iff b).mp hLE j hj)
  have hPfFinite (j : ℤ) : Module.Finite A (Pf.X j) :=
    Module.Finite.equiv
      (PseudoCoherence.extendScalarsTensorIso (S := A) (P.X j)).toLinearEquiv.symm
  have hPfProjective (j : ℤ) : Module.Projective A (Pf.X j) :=
    Module.Projective.of_equiv
      (PseudoCoherence.extendScalarsTensorIso (S := A) (P.X j)).toLinearEquiv.symm
  let eOp : Pf.opcycles n ≅ ModuleCat.of A (A ⊗[R] (P.opcycles n)) :=
    (P.sc n).mapOpcyclesIso F ≪≫ PseudoCoherence.extendScalarsTensorIso (S := A) (P.opcycles n)
  have hOpFinite : Module.Finite A (Pf.opcycles n) :=
    Module.Finite.of_surjective (Pf.pOpcycles n).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have : Module.Projective A (ModuleCat.of A (A ⊗[R] (P.opcycles n))) := hOpProjective
  have hOpProjective' : Module.Projective A (Pf.opcycles n) :=
    Module.Projective.of_equiv eOp.toLinearEquiv.symm
  obtain ⟨hge, hle, hfin, hproj⟩ := truncGE_bounded_finite_projective Pf n b
    hPfLE hPfFinite hPfProjective hOpFinite hOpProjective'
  refine ⟨Pf.truncGE n, hge, hle, hfin, hproj, ?_⟩
  obtain ⟨e⟩ := truncGE_Q_obj_iso Pf n
  exact ⟨(DerivedCategory.TStructure.t.truncGE n).mapIso
    (F.mapDerivedCategoryFactors.app P) ≪≫ e⟩

/-- Derived localization kills a cohomology module whose base change to `R_f` is trivial. -/
private lemma isZero_homology_localizationAway_of_subsingleton
    {R : Type u} [CommRing R] (f : R)
    (K : DerivedCategory (ModuleCat.{max u v} R)) (i : ℤ)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (eP : DerivedCategory.Q.obj P ≅ K)
    (hH : Subsingleton (Localization.Away f ⊗[R] P.homology i)) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (Localization.Away f)) i).obj
        ((PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K)) := by
  let F := ModuleCat.extendScalars (algebraMap R (Localization.Away f))
  have h0 : IsZero (F.obj (P.homology i)) :=
    (ModuleCat.isZero_of_subsingleton _).of_iso
      (PseudoCoherence.extendScalarsTensorIso (S := Localization.Away f) (P.homology i))
  have h1 : IsZero (F.obj ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} R) i).obj K)) :=
    h0.of_iso (F.mapIso ((DerivedCategory.homologyFunctor _ i).mapIso eP.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P))
  exact h1.of_iso ((localizationAwayHomologyFunctorIso.{u, v} f i).app K)

/-- The comparison `τ_{≤ i-1} K ⟶ τ_{≤ i} K` is an isomorphism when `H^i(K) = 0`. -/
private lemma isIso_natTransTruncLEOfLE_app_pred
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (X : DerivedCategory C) (i : ℤ)
    (hX : IsZero ((DerivedCategory.homologyFunctor C i).obj X)) :
    IsIso ((DerivedCategory.TStructure.t.natTransTruncLEOfLE (i - 1) i (by omega)).app X) := by
  have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished i (i + 1) rfl X
  have hLE : ((DerivedCategory.TStructure.t.truncLE i).obj X).IsLE (i - 1) := by
    rw [DerivedCategory.isLE_iff]
    intro j hj
    rcases (show j = i ∨ i < j by omega) with rfl | hj'
    · have hex := DerivedCategory.HomologySequence.exact₁ _ hT (j - 1) j (by omega)
      refine hex.isZero_X₂ ?_ ?_
      · have : ((DerivedCategory.TStructure.t.truncGE (j + 1)).obj X).IsGE (j + 1) :=
          DerivedCategory.TStructure.t.isGE_truncGE_obj X (j + 1) (j + 1)
        exact (DerivedCategory.isZero_of_isGE
          ((DerivedCategory.TStructure.t.truncGE (j + 1)).obj X) (j + 1) (j - 1)
            (by omega)).eq_of_src _ _
      · exact hX.eq_of_tgt _ _
    · exact DerivedCategory.isZero_of_isLE _ i j hj'
  refine ⟨DerivedCategory.TStructure.t.liftTruncLE
    ((DerivedCategory.TStructure.t.truncLEι i).app X) (i - 1), ?_, ?_⟩
  · exact DerivedCategory.TStructure.t.to_truncLE_obj_ext (by simp)
  · exact DerivedCategory.TStructure.t.to_truncLE_obj_ext (by simp)

/-- When `H^i(X) = 0`, the truncations `τ_{≤ i-1} X ⟶ X ⟶ τ_{≥ i+1} X` extend to a
distinguished triangle. -/
private lemma exists_distinguished_triangle_truncLE_pred_truncGE_succ
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (X : DerivedCategory C) (i : ℤ)
    (hX : IsZero ((DerivedCategory.homologyFunctor C i).obj X)) :
    ∃ δ, Triangle.mk ((DerivedCategory.TStructure.t.truncLEι (i - 1)).app X)
      ((DerivedCategory.TStructure.t.truncGEπ (i + 1)).app X) δ ∈ distTriang _ := by
  have := isIso_natTransTruncLEOfLE_app_pred X i hX
  have hle : i - 1 ≤ i := by omega
  let φ : (DerivedCategory.TStructure.t.truncLE (i - 1)).obj X ≅
      (DerivedCategory.TStructure.t.truncLE i).obj X :=
    asIso ((DerivedCategory.TStructure.t.natTransTruncLEOfLE (i - 1) i hle).app X)
  refine ⟨(DerivedCategory.TStructure.t.truncGEδLE i (i + 1) rfl).app X ≫
    (shiftFunctor _ (1 : ℤ)).map φ.inv, isomorphic_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished i (i + 1) rfl X) _ ?_⟩
  refine Triangle.isoMk _ _ φ (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · dsimp [φ]
    exact (Category.comp_id _).trans
      (DerivedCategory.TStructure.t.natTransTruncLEOfLE_ι_app _ _ _ _).symm
  · dsimp
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · dsimp
    rw [Category.assoc, ← Functor.map_comp, φ.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp]
    rfl

/-- A splitting `X ≅ B ⊞ A` adapted to `ι : B ⟶ X` and `π : X ⟶ A` gives, through the braiding,
a splitting `X ≅ A ⊞ B` adapted to the same maps, unique if the first one is. -/
private lemma existsUnique_iso_biprod_swap
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    {X A B : C} {ι : B ⟶ X} {π : X ⟶ A}
    (h : ∃! e : X ≅ B ⊞ A, ι ≫ e.hom = biprod.inl ∧ π = e.hom ≫ biprod.snd) :
    ∃! e : X ≅ A ⊞ B, π = e.hom ≫ biprod.fst ∧ ι ≫ e.hom = biprod.inr := by
  obtain ⟨e, he, huniq⟩ := h
  refine ⟨e ≪≫ biprod.braiding B A, ⟨?_, ?_⟩, ?_⟩
  · simp [he.2]
  · simp only [Iso.trans_hom, reassoc_of% he.1, biprod.braiding_hom]
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst]
      exact biprod.inl_snd.trans biprod.inr_fst.symm
    · rw [Category.assoc, biprod.lift_snd]
      exact biprod.inl_fst.trans biprod.inr_snd.symm
  · intro e' he'
    have hbr := huniq (e' ≪≫ biprod.braiding A B)
      ⟨by
        simp only [Iso.trans_hom, reassoc_of% he'.2, biprod.braiding_hom]
        apply biprod.hom_ext
        · rw [Category.assoc, biprod.lift_fst]
          exact biprod.inr_snd.trans biprod.inl_fst.symm
        · rw [Category.assoc, biprod.lift_snd]
          exact biprod.inr_fst.trans biprod.inl_snd.symm, by simp [he'.1]⟩
    rw [← hbr]
    ext <;> simp

/-! ### Splitting from vanishing of fibre cohomology -/

/-- Let `R` be a ring, `p ⊂ R` a prime, `i ∈ ℤ` and let `K` be a pseudo-coherent
object of `D(R)` with `H^i(K ⊗_R^L κ(p)) = 0`. Then there is `f ∈ R`, `f ∉ p`, and a canonical
direct sum decomposition
`K ⊗_R R_f = τ_{≥ i+1}(K ⊗_R R_f) ⊕ τ_{≤ i-1}(K ⊗_R R_f)` in `D(R_f)`, in which
`τ_{≥ i+1}(K ⊗_R R_f)` is a perfect complex with Tor amplitude in `[i + 1, ∞]`. -/
@[stacks 068U]
theorem exists_localization_iso_biprod_truncGE_truncLE
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (_hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (hfibre : FibreCohomologyVanishes.{u, v} p K i) :
    ∃ f : R, f ∉ p ∧
      let Kf := (PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K
      let upper := (DerivedCategory.TStructure.t.truncGE (i + 1)).obj Kf
      let lower := (DerivedCategory.TStructure.t.truncLE (i - 1)).obj Kf
      IsPerfect upper ∧
        (∃ (P : CochainComplex (ModuleCat.{max u v} (Localization.Away f)) ℤ) (b : ℤ),
          P.IsStrictlyGE (i + 1) ∧ P.IsStrictlyLE b ∧
            (∀ j : ℤ, Module.Finite (Localization.Away f) (P.X j)) ∧
            (∀ j : ℤ, Module.Projective (Localization.Away f) (P.X j)) ∧
            Nonempty (upper ≅ DerivedCategory.Q.obj P) ∧
            ∀ (M : ModuleCat.{max u v} (Localization.Away f)) (j : ℤ), j < i + 1 →
              IsZero ((TorAmplitude.tensorComplex P M).homology j)) ∧
        ∃! e : Kf ≅ upper ⊞ lower,
          (DerivedCategory.TStructure.t.truncGEπ (i + 1)).app Kf = e.hom ≫ biprod.fst ∧
            (DerivedCategory.TStructure.t.truncLEι (i - 1)).app Kf ≫ e.hom = biprod.inr := by
  obtain ⟨P, hP, ⟨eP⟩, hz⟩ := hfibre
  obtain ⟨b, hb⟩ := hP.upperBound
  have hFinite (j : ℤ) : Module.Finite R (P.X j) := (hP.finiteFree j).1
  have hFree (j : ℤ) : Module.Free R (P.X j) := (hP.finiteFree j).2
  obtain ⟨f, hf, hOp, hH⟩ :=
    exists_away_projective_opcycles_and_subsingleton_homology p P i hP.finiteFree hz
  obtain ⟨Q, hGE, hLE, hFin, hProj, ⟨eQ⟩⟩ :=
    localized_upper_representative f P (i + 1) b hb hFinite hFree hOp
  have hHi := isZero_homology_localizationAway_of_subsingleton f K i P eP hH
  refine ⟨f, hf, ?_⟩
  intro Kf upper lower
  have eU : upper ≅ DerivedCategory.Q.obj Q :=
    (DerivedCategory.TStructure.t.truncGE (i + 1)).mapIso
      ((PseudoCoherence.localizationAwayFunctorAux.{u, v} f).mapIso eP.symm) ≪≫ eQ
  refine ⟨⟨Q, i + 1, max (i + 1) b, hGE, hLE, hFin, hProj, ⟨eU⟩⟩,
    ⟨Q, max (i + 1) b, hGE, hLE, hFin, hProj, ⟨eU⟩,
      isZero_tensorComplex_homology_of_isStrictlyGE Q (i + 1) hGE⟩, ?_⟩
  have hAmp : HasProjectiveAmplitude.{u, v} upper (i + 1) (max (i + 1) b) :=
    ⟨Q, ⟨eU.symm⟩, hProj, hGE, hLE⟩
  have hLower : ∀ j : ℤ, i + 1 ≤ j →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} (Localization.Away f)) j).obj lower) := fun j hj =>
    DerivedCategory.isZero_of_isLE lower (i - 1) j (by omega)
  obtain ⟨δ, hT⟩ := exists_distinguished_triangle_truncLE_pred_truncGE_succ Kf i hHi
  exact existsUnique_iso_biprod_swap ((hom_eq_zero_and_existsUnique_iso_biprod
    lower upper (i + 1) (max (i + 1) b) hAmp).2.2 hLower Kf _ _ δ hT)

end StacksDraft.Perfect

end
