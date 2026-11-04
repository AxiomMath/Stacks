module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.TwoTermComplex.BaseChange
public import StacksFrontier.RingTheory.NaiveCotangent.Defs

@[expose] public section

/-!
# Base change of the naive cotangent complex

Let `R → S` be a ring map. This file records how the naive cotangent complex behaves under
changing the base ring `R → R'` and under changing `S → S'`.

## Main results

* `NaiveCotangent.naiveCotangentComplex_baseChange_homology` (Stacks 0FUZ): for arbitrary
  `R → R'`, base change of a presentation is a presentation of `S' = R' ⊗[R] S`, and the
  canonical map `NL(α) ⊗_S S' → NL(α')` is an isomorphism on `H⁰` and surjective on `H⁻¹`. The
  same holds for the canonical presentation, hence for `NL_{S/R} ⊗_S S' → NL_{S'/R'}`.
* `NaiveCotangent.naiveCotangent_baseChange_truncGE_comparison_isIso` (Stacks 0FUY): for
  `R → S → S'`, the canonical map `NL_{S/R} ⊗_S^L S' → NL_{S/R} ⊗_S S'` induces an isomorphism
  `τ_{≥ -1}(NL_{S/R} ⊗_S^L S') → NL_{S/R} ⊗_S S'`, and likewise for every polynomial
  presentation.

## Implementation notes

A two-term naive cotangent complex is handled through its differential from the conormal module
to the cotangent space (`NaiveCotangent.TwoTerm`). In Stacks 0FUZ "isomorphism on `H⁰`" is
recorded as bijectivity of the induced map on cokernels and "surjective on `H⁻¹`" as
surjectivity on kernels, stated elementwise so that no choice of homology model is needed.

Stacks 0FUY is an instance of the general base-change statement for two-term complexes with flat
degree-zero term, `StacksDraft.Homology.TwoTermComplex.twoTermBaseChange_iso_truncGE`: the
degree-zero term of the naive cotangent complex is a cotangent space, hence flat. Accordingly
derived base change is quantified over via its universal property as a total left derived
functor, and the complex is presented as the mapping cone of the differential placed in degrees
`-1` and `0`. The two terms are transported along their universe-lift equivalences so that
presentations whose generators live in an arbitrary universe sit in one module category.

The canonical presentation is written `NaiveCotangent.NL (NaiveCotangent.canonicalGenerators R S)`
rather than through a separate abbreviation, since the abbreviation belongs to the Chapter 10
development of `NL` and is not needed here.

## References

* [The Stacks Project, Lemma 15.87.1 (0FUY)](https://stacks.math.columbia.edu/tag/0FUY)
* [The Stacks Project, Lemma 15.87.2 (0FUZ)](https://stacks.math.columbia.edu/tag/0FUZ)
-/

open CategoryTheory Limits TensorProduct

namespace NaiveCotangent

universe t u uR uS uS' v w

attribute [local instance] HasDerivedCategory.standard

private lemma twoTerm_baseChange_bridge
    {A M N M' N' : Type*} [CommRing A]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module A M] [Module A N] [Module A M'] [Module A N']
    (d : M →ₗ[A] N) (d' : M' →ₗ[A] N') (f₁ : M →ₗ[A] M') (f₀ : N →ₗ[A] N')
    (hsq : d' ∘ₗ f₁ = f₀ ∘ₗ d) (hf₀ : Function.Bijective f₀)
    (hf₁ : Function.Surjective f₁) :
    d' ∘ₗ f₁ = f₀ ∘ₗ d ∧
      (∀ y, ∃ x, y - f₀ x ∈ LinearMap.range d') ∧
      (∀ x, f₀ x ∈ LinearMap.range d' ↔ x ∈ LinearMap.range d) ∧
      ∀ y, d' y = 0 → ∃ x, d x = 0 ∧ f₁ x = y := by
  have key (z : M) : d' (f₁ z) = f₀ (d z) := LinearMap.congr_fun hsq z
  refine ⟨hsq, fun y ↦ ?_, fun x ↦ ⟨?_, ?_⟩, fun y hy ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := hf₀.2 y
    exact ⟨x, by simp⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := hf₁ y
    exact ⟨z, hf₀.1 ((key z).symm.trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨f₁ y, key y⟩
  · obtain ⟨x, rfl⟩ := hf₁ y
    exact ⟨x, hf₀.1 (((key x).symm.trans hy).trans (map_zero f₀).symm), rfl⟩

set_option backward.isDefEq.respectTransparency false in
private lemma cotangent_baseChange_surjective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (P : Algebra.Extension R S) :
    letI : Algebra S (T ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    Function.Surjective
      ((Algebra.Extension.Cotangent.map (P.toBaseChange T)).liftBaseChange (T ⊗[R] S)) := by
  let : Algebra S (T ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  intro x
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  have hx : x.1 ∈ P.ker.map
      (Algebra.TensorProduct.includeRight : P.Ring →ₐ[R] T ⊗[R] P.Ring).toRingHom := by
    rw [← P.ker_baseChange T]
    exact x.2
  obtain ⟨y, hy⟩ := P.ker.map_includeRight_eq.le hx
  induction y using TensorProduct.induction_on generalizing x with
  | zero =>
      obtain rfl : x = 0 := Subtype.ext hy.symm
      exact ⟨0, by simp⟩
  | add y z iy iz =>
      let xy : (P.baseChange (T := T)).ker :=
        ⟨(LinearMap.lTensor T (P.ker.restrictScalars R).subtype) y, by
          rw [P.ker_baseChange T]
          exact P.ker.map_includeRight_eq.ge ⟨y, rfl⟩⟩
      let xz : (P.baseChange (T := T)).ker :=
        ⟨(LinearMap.lTensor T (P.ker.restrictScalars R).subtype) z, by
          rw [P.ker_baseChange T]
          exact P.ker.map_includeRight_eq.ge ⟨z, rfl⟩⟩
      obtain ⟨a, ha⟩ := iy xy (by rw [← P.ker_baseChange T]; exact xy.2) rfl
      obtain ⟨b, hb⟩ := iz xz (by rw [← P.ker_baseChange T]; exact xz.2) rfl
      refine ⟨a + b, ?_⟩
      rw [map_add, ha, hb, ← map_add]
      congr 1
      apply Subtype.ext
      show (LinearMap.lTensor T (P.ker.restrictScalars R).subtype) y +
        (LinearMap.lTensor T (P.ker.restrictScalars R).subtype) z = x.1
      simpa using hy
  | tmul t z =>
      let z' : P.ker := ⟨z.1, z.2⟩
      let xt : (P.baseChange (T := T)).ker :=
        ⟨(LinearMap.lTensor T (P.ker.restrictScalars R).subtype) (t ⊗ₜ[R] z), by
          rw [P.ker_baseChange T]
          exact P.ker.map_includeRight_eq.ge ⟨t ⊗ₜ[R] z, rfl⟩⟩
      obtain rfl : x = xt := Subtype.ext hy.symm
      refine ⟨(t ⊗ₜ[R] (1 : S)) ⊗ₜ[S] Algebra.Extension.Cotangent.mk z', ?_⟩
      rw [LinearMap.liftBaseChange_tmul, Algebra.Extension.Cotangent.map_mk]
      apply Algebra.Extension.Cotangent.ext
      rw [Algebra.Extension.Cotangent.val_smul, Algebra.Extension.Cotangent.val_mk,
        Algebra.Extension.Cotangent.val_mk, ← (P.baseChange.ker.toCotangent).map_smul,
        Ideal.toCotangent_eq]
      simp only [SetLike.val_smul_of_tower, z', xt,
        Algebra.Extension.Hom.toAlgHom_apply]
      simp only [Algebra.smul_def, LinearMap.lTensor_tmul]
      let r : P.baseChange.Ring := t ⊗ₜ[R] (1 : P.Ring)
      have hmul :
          (LinearMap.lTensor T (P.ker.restrictScalars R).subtype) (t ⊗ₜ[R] z) =
            r * (P.toBaseChange T).toRingHom z.1 := by
        simp only [LinearMap.lTensor_tmul]
        show (t ⊗ₜ[R] (z : P.Ring)) =
          (t ⊗ₜ[R] (1 : P.Ring)) * (1 ⊗ₜ[R] (z : P.Ring))
        simp
      rw [LinearMap.lTensor_tmul] at hmul
      rw [hmul]
      show (P.baseChange.σ (t ⊗ₜ[R] (1 : S)) *
        (P.toBaseChange T).toRingHom z.1 -
        r * (P.toBaseChange T).toRingHom z.1) ∈ P.baseChange.ker ^ 2
      rw [← sub_mul, pow_two]
      apply Ideal.mul_mem_mul
      · show algebraMap P.baseChange.Ring (T ⊗[R] S)
          (P.baseChange.σ (t ⊗ₜ[R] (1 : S)) - r) = 0
        rw [map_sub, P.baseChange.algebraMap_σ]
        show (t ⊗ₜ[R] (1 : S)) -
          (Algebra.TensorProduct.map (AlgHom.id T T)
            (IsScalarTower.toAlgHom R P.Ring S)) (t ⊗ₜ[R] (1 : P.Ring)) = 0
        simp
      · rw [P.ker_baseChange T]
        exact Ideal.mem_map_of_mem _ z.2

private lemma cotangent_map_surjective_of_ring_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P Q : Algebra.Extension R S} (f : P.Hom Q)
    (hf : Function.Surjective f.toRingHom) :
    Function.Surjective (Algebra.Extension.Cotangent.map f) := by
  intro x
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  obtain ⟨y, hy⟩ := hf x.1
  have hyker : y ∈ P.ker := by
    show algebraMap P.Ring S y = 0
    have h := f.algebraMap_toRingHom y
    have hx : algebraMap Q.Ring S x.1 = 0 := x.2
    rw [hy] at h
    simpa using h.symm.trans hx
  refine ⟨Algebra.Extension.Cotangent.mk ⟨y, hyker⟩, ?_⟩
  simp only [Algebra.Extension.Cotangent.map_mk]
  congr 1
  exact Subtype.ext hy

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Base change of a presentation is bijective on cotangent spaces: both sides are free on the
generators, compatibly. -/
lemma cotangentSpace_baseChange_bijective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] {ι : Type*} (P : Algebra.Generators R S ι) :
    let S' := T ⊗[R] S
    letI : Algebra S S' := Algebra.TensorProduct.rightAlgebra
    let h := (P.baseChangeFromBaseChange T).comp (P.toExtension.toBaseChange T)
    Function.Bijective ((Algebra.Extension.CotangentSpace.map h).liftBaseChange S') := by
  let S' := T ⊗[R] S
  let : Algebra S S' := Algebra.TensorProduct.rightAlgebra
  let P' := P.baseChange T
  let h := (P.baseChangeFromBaseChange T).comp (P.toExtension.toBaseChange T)
  let b := P.cotangentSpaceBasis.baseChange S'
  let b' := P'.cotangentSpaceBasis
  let f := (Algebra.Extension.CotangentSpace.map h).liftBaseChange S'
  have hb (i : ι) : f (b i) = b' i := by
    simp only [f, b, b', Module.Basis.baseChange_apply,
      LinearMap.liftBaseChange_tmul, one_smul]
    rw [P.cotangentSpaceBasis_apply, P'.cotangentSpaceBasis_apply]
    show (Algebra.Extension.CotangentSpace.map h)
      ((1 : S) ⊗ₜ[P.toExtension.Ring]
        KaehlerDifferential.D R P.toExtension.Ring (MvPolynomial.X i)) = _
    rw [Algebra.Extension.CotangentSpace.map_tmul]
    have hXi : h.toAlgHom (MvPolynomial.X i) = (MvPolynomial.X i : P'.Ring) := by
      show (MvPolynomial.algebraTensorAlgEquiv R T)
        (1 ⊗ₜ[R] (MvPolynomial.X i)) = _
      simp [MvPolynomial.algebraTensorAlgEquiv_tmul]
    rw [hXi]
    simp
  have hf : f = b'.repr.symm.toLinearMap ∘ₗ b.repr.toLinearMap := by
    refine b.ext fun i ↦ ?_
    show f (b i) = b'.repr.symm (b.repr (b i))
    rw [b.repr_self, b'.repr_symm_single_one]
    exact hb i
  show Function.Bijective f
  rw [hf]
  exact (b.repr.trans b'.repr.symm).bijective

private lemma cotangent_generators_baseChange_surjective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] {ι : Type*} (P : Algebra.Generators R S ι) :
    let S' := T ⊗[R] S
    letI : Algebra S S' := Algebra.TensorProduct.rightAlgebra
    let h := (P.baseChangeFromBaseChange T).comp (P.toExtension.toBaseChange T)
    Function.Surjective ((Algebra.Extension.Cotangent.map h).liftBaseChange S') := by
  let S' := T ⊗[R] S
  let : Algebra S S' := Algebra.TensorProduct.rightAlgebra
  let g := P.baseChangeFromBaseChange T
  let h := g.comp (P.toExtension.toBaseChange T)
  have heq : (Algebra.Extension.Cotangent.map h).liftBaseChange S' =
      Algebra.Extension.Cotangent.map g ∘ₗ
        (Algebra.Extension.Cotangent.map (P.toExtension.toBaseChange T)).liftBaseChange S' := by
    rw [LinearMap.liftBaseChange_comp, ← Algebra.Extension.Cotangent.map_comp]
  show Function.Surjective ((Algebra.Extension.Cotangent.map h).liftBaseChange S')
  rw [heq]
  exact (cotangent_map_surjective_of_ring_surjective g
    (MvPolynomial.algebraTensorAlgEquiv R T).surjective).comp
    (cotangent_baseChange_surjective P.toExtension)

/-- The cotangent complex differential commutes with the base-change maps of an extension
homomorphism. -/
private lemma cotangentComplex_comp_liftBaseChange
    {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra T U] [Algebra R T] [Algebra S U] [Algebra R U]
    [IsScalarTower R T U] [IsScalarTower R S U]
    {P : Algebra.Extension R S} {Q : Algebra.Extension T U} (f : P.Hom Q) :
    Q.cotangentComplex ∘ₗ (Algebra.Extension.Cotangent.map f).liftBaseChange U =
      (Algebra.Extension.CotangentSpace.map f).liftBaseChange U ∘ₗ
        AlgebraTensorModule.lTensor U U P.cotangentComplex := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [LinearMap.comp_apply, map_add, hx, hy]
  | tmul s x =>
    simp only [LinearMap.comp_apply, LinearMap.liftBaseChange_tmul,
      AlgebraTensorModule.lTensor_tmul, map_smul,
      Algebra.Extension.CotangentSpace.map_cotangentComplex]

/-- The base-change comparison maps commute with the differential of the naive cotangent
complex: the square of a presentation and its base change along `R → T` commutes. -/
lemma cotangent_generators_baseChange_square
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] {ι : Type*} (P : Algebra.Generators R S ι) :
    let S' := T ⊗[R] S
    letI : Algebra S S' := Algebra.TensorProduct.rightAlgebra
    let P' := P.baseChange T
    let h := (P.baseChangeFromBaseChange T).comp (P.toExtension.toBaseChange T)
    let d := AlgebraTensorModule.lTensor S' S' P.toExtension.cotangentComplex
    let f₁ := (Algebra.Extension.Cotangent.map h).liftBaseChange S'
    let f₀ := (Algebra.Extension.CotangentSpace.map h).liftBaseChange S'
    P'.toExtension.cotangentComplex ∘ₗ f₁ = f₀ ∘ₗ d := by
  let : Algebra S (T ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  exact cotangentComplex_comp_liftBaseChange _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma intrinsic_toKaehler_baseChange
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    let S' := T ⊗[R] S
    letI : Algebra S S' := Algebra.TensorProduct.rightAlgebra
    let Pc := Algebra.Generators.self R S
    let Pc' := Algebra.Generators.self T S'
    let hc := (Pc.defaultHom Pc').toExtensionHom
    let fc₀ := (Algebra.Extension.CotangentSpace.map hc).liftBaseChange S'
    Pc'.toExtension.toKaehler ∘ₗ fc₀ =
      (KaehlerDifferential.tensorKaehlerEquiv R T S S').toLinearMap ∘ₗ
        AlgebraTensorModule.lTensor S' S' Pc.toExtension.toKaehler := by
  let S' := T ⊗[R] S
  let : Algebra S S' := Algebra.TensorProduct.rightAlgebra
  let Pc := Algebra.Generators.self R S
  let Pc' := Algebra.Generators.self T S'
  let hc := (Pc.defaultHom Pc').toExtensionHom
  let fc₀ := (Algebra.Extension.CotangentSpace.map hc).liftBaseChange S'
  let b := Pc.cotangentSpaceBasis.baseChange S'
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply, b, Module.Basis.baseChange_apply]
  show Pc'.toExtension.toKaehler
      (fc₀ (1 ⊗ₜ[S] Pc.cotangentSpaceBasis i)) =
    (KaehlerDifferential.tensorKaehlerEquiv R T S S')
      (1 ⊗ₜ[S] Pc.toExtension.toKaehler (Pc.cotangentSpaceBasis i))
  rw [LinearMap.liftBaseChange_tmul, one_smul, Pc.toKaehler_cotangentSpaceBasis,
    KaehlerDifferential.tensorKaehlerEquiv_tmul_D, Pc.cotangentSpaceBasis_apply]
  show Pc'.toExtension.toKaehler
    ((Algebra.Extension.CotangentSpace.map hc)
      ((1 : S) ⊗ₜ[Pc.toExtension.Ring]
        KaehlerDifferential.D R Pc.toExtension.Ring (MvPolynomial.X i))) = _
  rw [Algebra.Extension.CotangentSpace.map_tmul]
  have hh : hc.toAlgHom (MvPolynomial.X i) =
      MvPolynomial.X (algebraMap S S' i) := by
    show (Pc.defaultHom Pc').toAlgHom (MvPolynomial.X i) = _
    rw [Algebra.Generators.Hom.toAlgHom_X]
    show Pc'.σ (algebraMap S S' (Pc.val i)) = _
    simp [Pc, Pc']
  rw [hh]
  simpa [Pc, Pc'] using Pc'.toKaehler_tmul_D (algebraMap S S' i)

private lemma cokernel_comparison_of_exact
    {A M M' N N' K K' : Type*} [CommRing A]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
    [AddCommGroup K] [AddCommGroup K']
    [Module A M] [Module A M'] [Module A N] [Module A N']
    [Module A K] [Module A K']
    (d : M →ₗ[A] N) (d' : M' →ₗ[A] N')
    (e : N →ₗ[A] K) (e' : N' →ₗ[A] K')
    (f : N →ₗ[A] N') (g : K ≃ₗ[A] K')
    (he : Function.Exact d e) (he' : Function.Exact d' e')
    (hes : Function.Surjective e) (_hes' : Function.Surjective e')
    (hsq : e' ∘ₗ f = g.toLinearMap ∘ₗ e) :
    (∀ y, ∃ x, y - f x ∈ LinearMap.range d') ∧
      ∀ x, f x ∈ LinearMap.range d' ↔ x ∈ LinearMap.range d := by
  have hk' := he'.linearMap_ker_eq
  have key (x : N) : e' (f x) = g (e x) := LinearMap.congr_fun hsq x
  refine ⟨fun y ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hes (g.symm (e' y))
    refine ⟨x, ?_⟩
    rw [← hk', LinearMap.mem_ker]
    rw [map_sub, key x, hx, g.apply_symm_apply, sub_self]
  · rw [← hk', ← he.linearMap_ker_eq, LinearMap.mem_ker, LinearMap.mem_ker]
    rw [key x, ← map_zero g]
    exact g.injective.eq_iff

/-- The two maps out of the tensored cycles of the naive cotangent complex agree. -/
public lemma cotangent_maps_agree_on_tensored_cycles
    {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra T U] [Algebra R T] [Algebra S U] [Algebra R U]
    [IsScalarTower R T U] [IsScalarTower R S U]
    {P : Algebra.Extension R S} {Q : Algebra.Extension T U}
    (f g : P.Hom Q) (x : U ⊗[S] P.Cotangent)
    (hx : AlgebraTensorModule.lTensor U U P.cotangentComplex x = 0) :
    (Algebra.Extension.Cotangent.map f).liftBaseChange U x =
      (Algebra.Extension.Cotangent.map g).liftBaseChange U x := by
  have hmap :
      (Algebra.Extension.Cotangent.map f).liftBaseChange U -
        (Algebra.Extension.Cotangent.map g).liftBaseChange U =
      (f.sub g).liftBaseChange U ∘ₗ
        AlgebraTensorModule.lTensor U U P.cotangentComplex := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [LinearMap.comp_apply, map_add, hx, hy]
    | tmul u z =>
        have hz := DFunLike.congr_fun (Algebra.Extension.Cotangent.map_sub_map f g) z
        simp only [LinearMap.sub_apply, LinearMap.comp_apply] at hz
        simp only [LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.liftBaseChange_tmul, AlgebraTensorModule.lTensor_tmul,
          ← smul_sub, hz]
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, hx, map_zero, sub_eq_zero] using
    DFunLike.congr_fun hmap x

set_option backward.isDefEq.respectTransparency false in
private lemma intrinsic_cycle_surjective
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    let S' := T ⊗[R] S
    letI : Algebra S S' := Algebra.TensorProduct.rightAlgebra
    let Pc := Algebra.Generators.self R S
    let Pc' := Algebra.Generators.self T S'
    let hc := (Pc.defaultHom Pc').toExtensionHom
    let dc := AlgebraTensorModule.lTensor S' S' Pc.toExtension.cotangentComplex
    let fc₁ := (Algebra.Extension.Cotangent.map hc).liftBaseChange S'
    ∀ y, Pc'.toExtension.cotangentComplex y = 0 →
      ∃ x, dc x = 0 ∧ fc₁ x = y := by
  let S' := T ⊗[R] S
  let : Algebra S S' := Algebra.TensorProduct.rightAlgebra
  let Pc := Algebra.Generators.self R S
  let Pc' := Algebra.Generators.self T S'
  let G := Pc.baseChange T
  let h := (Pc.baseChangeFromBaseChange T).comp (Pc.toExtension.toBaseChange T)
  let q := (G.defaultHom Pc').toExtensionHom
  let hc := (Pc.defaultHom Pc').toExtensionHom
  let dc := AlgebraTensorModule.lTensor S' S' Pc.toExtension.cotangentComplex
  let f₁ := (Algebra.Extension.Cotangent.map h).liftBaseChange S'
  let f₀ := (Algebra.Extension.CotangentSpace.map h).liftBaseChange S'
  let fc₁ := (Algebra.Extension.Cotangent.map hc).liftBaseChange S'
  have hp := twoTerm_baseChange_bridge dc G.toExtension.cotangentComplex f₁ f₀
    (cotangent_generators_baseChange_square Pc)
    (cotangentSpace_baseChange_bijective Pc)
    (cotangent_generators_baseChange_surjective Pc)
  show ∀ y : Pc'.toExtension.Cotangent,
    Pc'.toExtension.cotangentComplex y = 0 → ∃ x, dc x = 0 ∧ fc₁ x = y
  intro y hy
  let yy : Pc'.toExtension.H1Cotangent := ⟨y, hy⟩
  let ee := Algebra.Generators.H1Cotangent.equiv G Pc'
  let zz := ee.symm yy
  obtain ⟨x, hx, hfx⟩ := hp.2.2.2 zz.1 zz.2
  have heq : (Algebra.Extension.H1Cotangent.map q) zz = yy :=
    ee.apply_symm_apply yy
  have hyq : (Algebra.Extension.Cotangent.map q) zz.1 = y :=
    congrArg Subtype.val heq
  refine ⟨x, hx, ?_⟩
  calc
    fc₁ x = (Algebra.Extension.Cotangent.map (q.comp h)).liftBaseChange S' x :=
      cotangent_maps_agree_on_tensored_cycles hc (q.comp h) x hx
    _ = (Algebra.Extension.Cotangent.map q) (f₁ x) := by
      rw [Algebra.Extension.Cotangent.map_comp, ← LinearMap.liftBaseChange_comp]
      rfl
    _ = y := by rw [hfx, hyq]

private lemma intrinsic_square
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    let S' := T ⊗[R] S
    letI : Algebra S S' := Algebra.TensorProduct.rightAlgebra
    let Pc := Algebra.Generators.self R S
    let Pc' := Algebra.Generators.self T S'
    let hc := (Pc.defaultHom Pc').toExtensionHom
    let dc := AlgebraTensorModule.lTensor S' S' Pc.toExtension.cotangentComplex
    let fc₁ := (Algebra.Extension.Cotangent.map hc).liftBaseChange S'
    let fc₀ := (Algebra.Extension.CotangentSpace.map hc).liftBaseChange S'
    Pc'.toExtension.cotangentComplex ∘ₗ fc₁ = fc₀ ∘ₗ dc := by
  let : Algebra S (T ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  exact cotangentComplex_comp_liftBaseChange _

private lemma intrinsic_cokernel_comparison
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    let S' := T ⊗[R] S
    letI : Algebra S S' := Algebra.TensorProduct.rightAlgebra
    let Pc := Algebra.Generators.self R S
    let Pc' := Algebra.Generators.self T S'
    let hc := (Pc.defaultHom Pc').toExtensionHom
    let dc := AlgebraTensorModule.lTensor S' S' Pc.toExtension.cotangentComplex
    let fc₀ := (Algebra.Extension.CotangentSpace.map hc).liftBaseChange S'
    (∀ y, ∃ x, y - fc₀ x ∈ LinearMap.range Pc'.toExtension.cotangentComplex) ∧
      ∀ x, fc₀ x ∈ LinearMap.range Pc'.toExtension.cotangentComplex ↔
        x ∈ LinearMap.range dc := by
  let S' := T ⊗[R] S
  let : Algebra S S' := Algebra.TensorProduct.rightAlgebra
  let Pc := Algebra.Generators.self R S
  let Pc' := Algebra.Generators.self T S'
  let hc := (Pc.defaultHom Pc').toExtensionHom
  let dc := AlgebraTensorModule.lTensor S' S' Pc.toExtension.cotangentComplex
  let fc₀ := (Algebra.Extension.CotangentSpace.map hc).liftBaseChange S'
  exact cokernel_comparison_of_exact dc Pc'.toExtension.cotangentComplex
    (AlgebraTensorModule.lTensor S' S' Pc.toExtension.toKaehler)
    Pc'.toExtension.toKaehler fc₀
    (KaehlerDifferential.tensorKaehlerEquiv R T S S')
    (lTensor_exact _ Pc.toExtension.exact_cotangentComplex_toKaehler
        Pc.toExtension.toKaehler_surjective)
    Pc'.toExtension.exact_cotangentComplex_toKaehler
    (LinearMap.lTensor_surjective S' Pc.toExtension.toKaehler_surjective)
    Pc'.toExtension.toKaehler_surjective
    intrinsic_toKaehler_baseChange

/-- **Stacks 0FUZ.** Formation of the naive cotangent complex commutes with arbitrary base change
on `H⁰` and is surjective on `H⁻¹`, both for a chosen polynomial presentation and for the
canonical one. -/
@[stacks 0FUZ]
public theorem naiveCotangentComplex_baseChange_homology
    {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] {ι : Type t} (P : Algebra.Generators R S ι) :
    let S' := T ⊗[R] S
    letI : Algebra S S' := Algebra.TensorProduct.rightAlgebra
    let P' := P.baseChange T
    let h := (P.baseChangeFromBaseChange T).comp (P.toExtension.toBaseChange T)
    let d := AlgebraTensorModule.lTensor S' S' P.toExtension.cotangentComplex
    let f₁ := (Algebra.Extension.Cotangent.map h).liftBaseChange S'
    let f₀ := (Algebra.Extension.CotangentSpace.map h).liftBaseChange S'
    P'.toExtension.cotangentComplex ∘ₗ f₁ = f₀ ∘ₗ d ∧
      (∀ y, ∃ x, y - f₀ x ∈ LinearMap.range P'.toExtension.cotangentComplex) ∧
      (∀ x, f₀ x ∈ LinearMap.range P'.toExtension.cotangentComplex ↔
        x ∈ LinearMap.range d) ∧
      (∀ y, P'.toExtension.cotangentComplex y = 0 →
        ∃ x, d x = 0 ∧ f₁ x = y) ∧
      let Pc := Algebra.Generators.self R S
      let Pc' := Algebra.Generators.self T S'
      let hc := (Pc.defaultHom Pc').toExtensionHom
      let dc := AlgebraTensorModule.lTensor S' S' Pc.toExtension.cotangentComplex
      let fc₁ := (Algebra.Extension.Cotangent.map hc).liftBaseChange S'
      let fc₀ := (Algebra.Extension.CotangentSpace.map hc).liftBaseChange S'
      Pc'.toExtension.cotangentComplex ∘ₗ fc₁ = fc₀ ∘ₗ dc ∧
        (∀ y, ∃ x, y - fc₀ x ∈ LinearMap.range Pc'.toExtension.cotangentComplex) ∧
        (∀ x, fc₀ x ∈ LinearMap.range Pc'.toExtension.cotangentComplex ↔
          x ∈ LinearMap.range dc) ∧
        ∀ y, Pc'.toExtension.cotangentComplex y = 0 →
          ∃ x, dc x = 0 ∧ fc₁ x = y := by
  let S' := T ⊗[R] S
  let : Algebra S S' := Algebra.TensorProduct.rightAlgebra
  let P' := P.baseChange T
  let h := (P.baseChangeFromBaseChange T).comp (P.toExtension.toBaseChange T)
  let d := AlgebraTensorModule.lTensor S' S' P.toExtension.cotangentComplex
  let f₁ := (Algebra.Extension.Cotangent.map h).liftBaseChange S'
  let f₀ := (Algebra.Extension.CotangentSpace.map h).liftBaseChange S'
  have hp := twoTerm_baseChange_bridge d P'.toExtension.cotangentComplex f₁ f₀
    (cotangent_generators_baseChange_square P)
    (cotangentSpace_baseChange_bijective P)
    (cotangent_generators_baseChange_surjective P)
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2,
    intrinsic_square, (intrinsic_cokernel_comparison).1,
    (intrinsic_cokernel_comparison).2, intrinsic_cycle_surjective⟩

private lemma isZero_mappingCone_single_X
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    {M N : C} (d : M ⟶ N) (i : ℤ) (h₁ : i ≠ -1) (h₀ : i ≠ 0) :
    IsZero ((CochainComplex.mappingCone ((CochainComplex.singleFunctor C 0).map d)).X i) := by
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
    HomologicalComplex.isZero_single_obj_X _ _ _ _ h₀⟩

private lemma flat_mappingCone_single_X_zero
    {S : Type u} [CommRing S] {M N : ModuleCat.{v} S} (d : M ⟶ N)
    [Module.Flat S N] :
    Module.Flat S
      ((CochainComplex.mappingCone ((CochainComplex.singleFunctor _ 0).map d)).X 0) := by
  let e := HomologicalComplex.homotopyCofiber.XIsoBiprod
    ((CochainComplex.singleFunctor _ 0).map d) 0 1 rfl ≪≫
      (isoZeroBiprod (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 0 M 1 (by decide))).symm ≪≫
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

private lemma isZero_homology_Q_of_isZero_X
    {C : Type*} [Category C] [Abelian C]
    (L : CochainComplex C ℤ) (i : ℤ) (hi : IsZero (L.X i)) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj (DerivedCategory.Q.obj L)) :=
  (HomologicalComplex.ExactAt.of_isZero hi).isZero_homology.of_iso
    ((DerivedCategory.homologyFunctorFactors C i).app L)

/-- **Stacks 0FUY.** For `R → S → S'`, the canonical comparison from derived to termwise base
change of the naive cotangent complex induces an isomorphism after truncation in degrees at
least `-1`. This holds for the canonical presentation and for every polynomial presentation of
`S` over `R`. -/
@[stacks 0FUY]
public theorem naiveCotangent_baseChange_truncGE_comparison_isIso
    {R : Type uR} {S : Type uS} {S' : Type uS'}
    [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra S S'] :
    letI : Functor.IsLeftAdjoint
        (ModuleCat.extendScalars.{uS, uS', max uS' (max uR uS w)} (algebraMap S S')) :=
      ModuleCat.instIsLeftAdjointExtendScalars.{uS, uS', max uR uS w} (algebraMap S S')
    ∀ (derivedBaseChange : DerivedCategory (ModuleCat.{max uS' (max uR uS w)} S) ⥤
        DerivedCategory (ModuleCat.{max uS' (max uR uS w)} S'))
      (comparison : DerivedCategory.Q ⋙ derivedBaseChange ⟶
        (ModuleCat.extendScalars.{uS, uS', max uS' (max uR uS w)}
          (algebraMap S S')).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      [derivedBaseChange.IsLeftDerivedFunctor comparison
        (HomologicalComplex.quasiIso (ModuleCat.{max uS' (max uR uS w)} S)
          (ComplexShape.up ℤ))],
    let canonicalMapInducesIso
        (L : CochainComplex (ModuleCat.{max uS' (max uR uS w)} S) ℤ) : Prop :=
      ∃ f : ((DerivedCategory.TStructure.t
                (C := ModuleCat.{max uS' (max uR uS w)} S')).truncGE (-1)).obj
              (derivedBaseChange.obj (DerivedCategory.Q.obj L)) ⟶
            DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{uS, uS', max uS' (max uR uS w)}
                  (algebraMap S S')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj L),
        comparison.app L =
          ((DerivedCategory.TStructure.t
              (C := ModuleCat.{max uS' (max uR uS w)} S')).truncGEπ (-1)).app
            (derivedBaseChange.obj (DerivedCategory.Q.obj L)) ≫ f ∧
          IsIso f
    canonicalMapInducesIso
        (CochainComplex.mappingCone
          ((CochainComplex.singleFunctor (ModuleCat.{max uS' (max uR uS w)} S) 0).map
            (ModuleCat.ofHom
              (ULift.moduleEquiv.{uS, max uR uS,
                  max uS' (max uR uS w)}.symm.toLinearMap.comp
                ((NaiveCotangent.NL (NaiveCotangent.canonicalGenerators R S)).d.comp
                  ULift.moduleEquiv.{uS, max uR uS,
                    max uS' (max uR uS w)}.toLinearMap))))) ∧
      ∀ (ι : Type w) (P : Algebra.Generators R S ι),
        canonicalMapInducesIso
          (CochainComplex.mappingCone
            ((CochainComplex.singleFunctor (ModuleCat.{max uS' (max uR uS w)} S) 0).map
              (ModuleCat.ofHom
                (ULift.moduleEquiv.{uS, max (max uR uS) w,
                    max uS' (max uR uS w)}.symm.toLinearMap.comp
                  ((NaiveCotangent.NL P).d.comp
                    ULift.moduleEquiv.{uS, max uR w,
                      max uS' (max uR uS w)}.toLinearMap))))) := by
  intro derivedBaseChange comparison hderived
  extract_lets canonicalMapInducesIso
  have h (M N : ModuleCat.{max uS' (max uR uS w)} S) (d : M ⟶ N)
      (hflat : Module.Flat S N) :
      canonicalMapInducesIso
        (CochainComplex.mappingCone ((CochainComplex.singleFunctor _ 0).map d)) := by
    let L := CochainComplex.mappingCone ((CochainComplex.singleFunctor _ 0).map d)
    have hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i) :=
      isZero_mappingCone_single_X d
    obtain ⟨f, hf, hi⟩ := TwoTermComplex.twoTermBaseChange_iso_truncGE.{uS, uS', max uR w}
      (algebraMap S S') (DerivedCategory.Q.obj L) L (Iso.refl _)
      (fun i h₁ h₀ ↦ isZero_homology_Q_of_isZero_X L i (hL i h₁ h₀)) hL
      (flat_mappingCone_single_X_zero d) derivedBaseChange comparison
    exact ⟨f, by simpa using hf.symm, hi⟩
  refine ⟨h _ _ _ ?_, fun ι P ↦ h _ _ _ ?_⟩
  · exact inferInstanceAs
      (Module.Flat S (ULift (Algebra.Generators.self R S).toExtension.CotangentSpace))
  · exact inferInstanceAs (Module.Flat S (ULift P.toExtension.CotangentSpace))

end NaiveCotangent
