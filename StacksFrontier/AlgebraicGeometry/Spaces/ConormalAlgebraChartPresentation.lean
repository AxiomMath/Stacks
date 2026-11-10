module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartSectionMul
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.GradedBasis

/-!
# The conormal algebra of a closed immersion over an affine étale chart

Let `k : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, with kernel ideal sheaf `𝓘 ⊆ 𝒪_X` and conormal algebra `𝒞_{Z/X,*} = k^*(⨁ 𝓘ⁿ)`
of Stacks 09RN.  Let `V` be an étale scheme chart of `X` whose scheme is affine, with ring of
functions `A = 𝒪_X(V)`, and let `Z_V = Z ×_X V` be the base-changed chart of `Z`, with ring of
functions `𝒪_Z(Z_V)`.  This file computes the conormal algebra over `Z_V`:

`𝒞_{Z/X,n}(Z_V) = Iⁿ/Iⁿ⁺¹`, for `I = 𝓘(V) = Ker(A ⟶ 𝒪_Z(Z_V))`,

through the class map `Iⁿ ⟶ 𝒞_{Z/X,n}(Z_V)`, the chart section of Stacks 03D7 of the inverse
image.  The class map is surjective, its kernel is `Iⁿ⁺¹`, it is semilinear over the surjection
`A ⟶ 𝒪_Z(Z_V)` and it is multiplicative; in the language of
`Stacks.RingTheory.QuasiRegular.GradedPresentation` it is a graded presentation of the degree-`n`
piece, which is the form in which the commutative algebra of quasi-regular sequences
(Stacks 061M, 063G) applies to it.

## Main definitions

* `AlgebraicGeometry.Space.conormalChartClass`: the class map `Iⁿ ⟶ 𝒞_{Z/X,n}(Z_V)`.
* `AlgebraicGeometry.Space.conormalChartPresentation`: the class map as a graded presentation.

## Main results

* `AlgebraicGeometry.Space.ker_chartDiagramRestrict_baseChangeChartDiagram`: the kernel of
  `A ⟶ 𝒪_Z(Z_V)` is `𝓘(V)`, for the diagram `AlgebraicGeometry.Space.baseChangeChartDiagram` of
  a chart and its base change.
* `AlgebraicGeometry.Space.sectionIdeal_kernelIdealSheafZPow_eq_pow`: over an affine chart the
  sections of `𝓘ⁿ` are `𝓘(V)ⁿ`.
* `AlgebraicGeometry.Space.surjective_conormalChartClass` and
  `AlgebraicGeometry.Space.conormalChartClass_eq_zero_iff`: the class map is surjective with
  kernel `Iⁿ⁺¹`.
* `AlgebraicGeometry.Space.modulePullbackChartSection_kernel_mul`: the class maps are
  multiplicative.

## Implementation notes

The computation is the base change comparison of Stacks 083K,
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`: the
sections of `k^*(𝓘ⁿ)` over `Z_V` are `𝒪_Z(Z_V) ⊗_A 𝓘ⁿ(V)`, and as `𝒪_Z(Z_V) = A/I` that is
`𝓘ⁿ(V)/I·𝓘ⁿ(V) = Iⁿ/Iⁿ⁺¹`, by `TensorProduct.quotTensorEquivQuotSMul`.

## References

* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped TensorProduct

universe u

/-- **Over a surjective algebra map with kernel `J`, a pure tensor `1 ⊗ m` vanishes exactly when
`m ∈ J • ⊤`.**  The base change along `R ⟶ R/J` is the quotient by `J • ⊤`. -/
theorem TensorProduct.one_tmul_eq_zero_iff_of_surjective {R A M : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    (hψ : Function.Surjective (algebraMap R A)) (m : M) :
    (1 : A) ⊗ₜ[R] m = 0 ↔ m ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R M) := by
  let e : A ≃ₐ[R] R ⧸ RingHom.ker (algebraMap R A) :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R A) hψ).symm
  let φ : A ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker (algebraMap R A) • (⊤ : Submodule R M)) :=
    (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker (algebraMap R A)))
  have hφ : φ ((1 : A) ⊗ₜ[R] m) = Submodule.Quotient.mk m := by
    simp only [φ, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      AlgEquiv.toLinearEquiv_apply, map_one]
    have h := TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := M)
      (RingHom.ker (algebraMap R A)) 1 m
    rwa [one_smul, map_one] at h
  rw [← Submodule.Quotient.mk_eq_zero, ← hφ, LinearEquiv.map_eq_zero_iff]

/-- **Over a surjective algebra map every element of a base change is a pure tensor `1 ⊗ m`.** -/
theorem TensorProduct.exists_one_tmul_eq_of_surjective {R A M : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    (hψ : Function.Surjective (algebraMap R A)) (z : A ⊗[R] M) :
    ∃ m : M, (1 : A) ⊗ₜ[R] m = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
    obtain ⟨r, rfl⟩ := hψ a
    refine ⟨r • m, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨m', rfl⟩ := hy
    exact ⟨m + m', TensorProduct.tmul_add _ _ _⟩

/-- If a module `M` embeds in `R` with image `Jⁿ`, then `J • ⊤` consists of the elements of `M`
mapping into `Jⁿ⁺¹`. -/
private theorem mem_smul_top_iff_of_injective_range_eq_pow {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (J : Ideal R) (n : ℕ) (φ : M →ₗ[R] R)
    (hφ : Function.Injective φ) (hrange : LinearMap.range φ = J ^ n) (m : M) :
    m ∈ J • (⊤ : Submodule R M) ↔ φ m ∈ J ^ (n + 1) := by
  have hmap : Submodule.map φ (J • (⊤ : Submodule R M)) = J ^ (n + 1) := by
    rw [Submodule.map_smul'', Submodule.map_top, hrange, pow_succ', Ideal.smul_eq_mul]
  rw [← hmap, ← Submodule.mem_comap, Submodule.comap_map_eq_of_injective hφ]

/-- In the `J`-module `Jⁿ`, the submodule `J • ⊤` consists of the elements of `Jⁿ⁺¹`. -/
theorem Ideal.mem_smul_top_pow_iff {R : Type*} [CommRing R] (J : Ideal R) (n : ℕ)
    (x : ↥(J ^ n)) :
    x ∈ J • (⊤ : Submodule R ↥(J ^ n)) ↔ (x : R) ∈ J ^ (n + 1) :=
  mem_smul_top_iff_of_injective_range_eq_pow J n (J ^ n).subtype (Submodule.injective_subtype _)
    (Submodule.range_subtype _) x

namespace Stacks.RingTheory.QuasiRegular.GradedPresentation

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N]
  [Module S N] {c' : ℕ}

/-- **Lifting a basis of the degree-one piece to generators modulo the square.**  If the
degree-one piece `J/J²` presented by `P` is free over `S = R/J` with a basis indexed by `Fin c`,
then `c` elements of `J` lifting the basis generate `J` modulo `J²`.

The class of `x ∈ J` is a combination of the basis with coefficients in `S`; lifting the
coefficients along the surjection `R ⟶ S` gives a combination of the lifts with the same class,
so `x` minus it lies in the kernel `J²` of the presentation. -/
theorem exists_mem_le_span_sup_sq (P : GradedPresentation R S c' 1 N) {c : ℕ}
    (b : Module.Basis (Fin c) S N) :
    ∃ f : Fin c → R, (∀ k, f k ∈ P.J) ∧ P.J ≤ Ideal.span (Set.range f) ⊔ P.J ^ 2 := by
  classical
  choose a ha using fun k : Fin c => P.surjective_g (b k)
  refine ⟨fun k => (a k : R), fun k => by simpa using (a k).2, fun x hx => ?_⟩
  have hx1 : x ∈ P.J ^ 1 := by rwa [pow_one]
  set t := P.g ⟨x, hx1⟩ with ht
  choose r hr using fun k : Fin c => P.surjective_ψ (b.repr t k)
  have hsum : P.g (∑ k, r k • a k) = t := by
    rw [map_sum]
    calc ∑ k, P.g (r k • a k) = ∑ k, b.repr t k • b k :=
          Finset.sum_congr rfl fun k _ => by rw [P.smul_g, ha k, hr k]
      _ = t := b.sum_repr t
  have hmem2 : x - ∑ k, r k * (a k : R) ∈ P.J ^ 2 := by
    have h0 : P.g (⟨x, hx1⟩ - ∑ k, r k • a k) = 0 := by rw [map_sub, hsum, sub_self]
    have h1 := (P.ker_g _).mp h0
    have hcoe : ((⟨x, hx1⟩ - ∑ k, r k • a k : ↥(P.J ^ 1)) : R) =
        x - ∑ k, r k * (a k : R) := by
      rw [Submodule.coe_sub, Submodule.coe_sum]
      simp [smul_eq_mul]
    rwa [hcoe] at h1
  refine Submodule.mem_sup.mpr ⟨∑ k, r k * (a k : R), ?_, x - ∑ k, r k * (a k : R), hmem2,
    by ring⟩
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

end Stacks.RingTheory.QuasiRegular.GradedPresentation

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : AlgebraicSpaces B S hS}

/-! ### The base-changed chart -/

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

/-- **The kernel of pullback of regular functions to the base-changed chart is the kernel ideal
sheaf.** -/
theorem ker_chartDiagramRestrict_baseChangeChartDiagram (k : Z ⟶ X)
    (hk : yoneda.relativelyRepresentable k.hom) (V : SmallEtale B S hS X.1) :
    RingHom.ker (chartDiagramRestrict B S hS k (baseChangeChartDiagram B S hS k hk V)) =
      (kernelIdealSheaf B S hS k).obj (op V) := by
  rw [kernelIdealSheaf_obj, ker_structureSharp_eq B S hS k hk V,
    chartPullbackRingHom_chartBaseChangeArrow]
  rfl

/-- The base change of a chart along a closed immersion is a closed immersion of schemes. -/
theorem isClosedImmersion_baseChangeChartDiagram_g (k : Z ⟶ X)
    (hk : IsClosedImmersion B S hS k.hom) (V : SmallEtale B S hS X.1) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (baseChangeChartDiagram B S hS k hk.1 V).g) :=
  hk.2 V.1.hom (hk.1.fst V.1.hom) (hk.1.snd V.1.hom) (hk.1.isPullback V.1.hom)

/-- **The base change of an affine chart along a closed immersion is affine, and pullback of
regular functions onto it is surjective.** -/
theorem isAffine_and_surjective_baseChangeChartDiagram (k : Z ⟶ X)
    (hk : IsClosedImmersion B S hS k.hom) (V : SmallEtale B S hS X.1)
    (hV : IsAffine (chartScheme V)) :
    IsAffine (chartScheme (baseChangeChartDiagram B S hS k hk.1 V).U) ∧
      Function.Surjective
        (chartDiagramRestrict B S hS k (baseChangeChartDiagram B S hS k hk.1 V)) := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hk.1.snd V.1.hom)) :=
    isClosedImmersion_baseChangeChartDiagram_g B S hS k hk V
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := hV
  exact _root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map (hk.1.snd V.1.hom))

/-! ### The sections of the powers of the kernel ideal sheaf over an affine chart -/

/-- **Over an affine chart the sections of `𝓘ⁿ` are `𝓘(V)ⁿ`**, for the kernel ideal sheaf `𝓘` of
a closed immersion. -/
theorem sectionIdeal_kernelIdealSheafZPow_eq_pow (k : Z ⟶ X)
    (hk : IsClosedImmersion B S hS k.hom) (V : SmallEtale B S hS X.1)
    (hV : IsAffine (chartScheme V)) (n : ℕ) :
    Stacks.Sites.sectionIdeal (O := (smallEtaleRingedSite B S hS X.1 X.2).O)
        (kernelIdealSheafZPow B S hS k (n : ℤ)) (op V) =
      Stacks.Sites.sectionIdeal (O := (smallEtaleRingedSite B S hS X.1 X.2).O)
        (kernelIdealSheaf B S hS k) (op V) ^ n := by
  have hpow : kernelIdealSheafZPow B S hS k (n : ℤ) =
      idealPowSubmodule (kernelIdealSheaf B S hS k) n (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) := by
    have h := SheafOfModules.idealSheafZPow_of_nonneg (kernelIdealSheaf B S hS k)
      (Int.natCast_nonneg n)
    rw [Int.toNat_natCast] at h
    exact h.trans (idealSheafPow_eq_idealPowSubmodule_ringSheaf B S hS X _ n)
  rw [hpow]
  exact (chartSubmodule_idealPowSubmodule_eq_of_isAffine B S hS X.1 X.2
    (kernelIdealSheaf B S hS k) _ isCartesianOnAffineCharts_unit
    (isCartesianOnAffineCharts_kernelIdealSheaf B S hS k
      (isQuasiCompact_of_isClosedImmersion' B S hS hk)) n hV).trans (Ideal.mul_top _)

/-! ### The class map -/

section ClassMap

variable (k : Z ⟶ X) (hk : IsClosedImmersion B S hS k.hom) (V : SmallEtale B S hS X.1)
  (hV : IsAffine (chartScheme V))

/-- The ideal `I = 𝓘(V)` of functions on the chart `V` vanishing on `Z_V`. -/
noncomputable abbrev conormalChartIdeal : Ideal (chartRing B S hS X.1 X.2 V) :=
  chartSectionIdeal B S hS X.1 X.2 (kernelIdealSheaf B S hS k) V

include hk hV in
/-- Over an affine chart, every element of `Iⁿ` is a section of `𝓘ⁿ` over `V`. -/
theorem mem_kernelIdealSheafZPow_of_mem_pow (n : ℕ) {x : chartRing B S hS X.1 X.2 V}
    (hx : x ∈ conormalChartIdeal B S hS k V ^ n) :
    x ∈ (kernelIdealSheafZPow B S hS k (n : ℤ)).obj (op V) := by
  change x ∈ Stacks.Sites.sectionIdeal (O := (smallEtaleRingedSite B S hS X.1 X.2).O)
    (kernelIdealSheafZPow B S hS k (n : ℤ)) (op V)
  rwa [sectionIdeal_kernelIdealSheafZPow_eq_pow B S hS k hk V hV n]

/-- The `n`-th power of the kernel ideal sheaf, as an `𝒪_X`-module in the spelling whose sections
are modules over `AlgebraicGeometry.Space.chartRing`. -/
noncomputable abbrev kernelPowModule (n : ℤ) : Modules.{u, u} B S hS X.1 X.2 :=
  (kernelIdealSheafZPow B S hS k n).toSheafOfModules

/-- The section of `𝓘ⁿ` over `V` determined by an element of `Iⁿ`. -/
noncomputable def kernelIdealSheafZPowSection (n : ℕ)
    (x : ↥(conormalChartIdeal B S hS k V ^ n)) :
    (kernelPowModule B S hS k (n : ℤ)).val.obj (op V) :=
  ⟨x.1, mem_kernelIdealSheafZPow_of_mem_pow B S hS k hk V hV n x.2⟩

/-- The section of `𝓘ⁿ` determined by an element of `Iⁿ` is additive in that element. -/
theorem kernelIdealSheafZPowSection_add (n : ℕ) (x y : ↥(conormalChartIdeal B S hS k V ^ n)) :
    kernelIdealSheafZPowSection B S hS k hk V hV n (x + y) =
      kernelIdealSheafZPowSection B S hS k hk V hV n x +
        kernelIdealSheafZPowSection B S hS k hk V hV n y :=
  SheafOfModules.reesPiece_ext (kernelIdealSheaf B S hS k) rfl

/-- **The class map `Iⁿ ⟶ 𝒞_{Z/X,n}(Z_V)`**: the chart section of Stacks 03D7 of the inverse
image `k^*(𝓘ⁿ)` over the base-changed chart. -/
noncomputable def conormalChartClass (n : ℕ) :
    ↥(conormalChartIdeal B S hS k V ^ n) →+
      ((modulePullback B S hS k).obj (kernelPowModule B S hS k (n : ℤ))).val.obj
        (op (baseChangeChartDiagram B S hS k hk.1 V).U) :=
  AddMonoidHom.mk' (fun x => modulePullbackChartSection B S hS k
    (kernelPowModule B S hS k (n : ℤ))
    (baseChangeChartDiagram B S hS k hk.1 V) (kernelIdealSheafZPowSection B S hS k hk V hV n x))
    (fun x y => by
      rw [kernelIdealSheafZPowSection_add]
      exact modulePullbackChartSection_add B S hS k _ _ _ _)

/-- The class of `x ∈ Iⁿ` is the chart section of the inverse image of the section of `𝓘ⁿ`
determined by `x`. -/
theorem conormalChartClass_apply (n : ℕ) (x : ↥(conormalChartIdeal B S hS k V ^ n)) :
    conormalChartClass B S hS k hk V hV n x = modulePullbackChartSection B S hS k
      (kernelPowModule B S hS k (n : ℤ))
      (baseChangeChartDiagram B S hS k hk.1 V)
      (kernelIdealSheafZPowSection B S hS k hk V hV n x) :=
  rfl

/-- **The class map is semilinear over pullback of regular functions.** -/
theorem conormalChartClass_smul (n : ℕ) (r : chartRing B S hS X.1 X.2 V)
    (x : ↥(conormalChartIdeal B S hS k V ^ n)) :
    conormalChartClass B S hS k hk V hV n (r • x) =
      chartDiagramRestrict B S hS k (baseChangeChartDiagram B S hS k hk.1 V) r •
        conormalChartClass B S hS k hk V hV n x := by
  rw [conormalChartClass_apply, conormalChartClass_apply]
  have h : kernelIdealSheafZPowSection B S hS k hk V hV n (r • x) =
      r • kernelIdealSheafZPowSection B S hS k hk V hV n x :=
    Subtype.ext rfl
  rw [h]
  exact modulePullbackChartSection_smul B S hS k (kernelPowModule B S hS k (n : ℤ))
    (baseChangeChartDiagram B S hS k hk.1 V) r (kernelIdealSheafZPowSection B S hS k hk V hV n x)

include hV in
/-- The base change comparison at the `n`-th power of the kernel ideal sheaf over the
base-changed chart is bijective. -/
theorem bijective_modulePullbackChartBaseChange_kernelPowModule (n : ℕ) :
    letI := chartDiagramAlgebra B S hS k (baseChangeChartDiagram B S hS k hk.1 V)
    Function.Bijective (modulePullbackChartBaseChange B S hS k
      (kernelPowModule B S hS k (n : ℤ)) (baseChangeChartDiagram B S hS k hk.1 V)) :=
  bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS k
    (kernelPowModule B S hS k (n : ℤ))
    (isQuasicoherentOnSite_kernelIdealSheafZPow_natCast B S hS k
      (isQuasicoherentOnSite_kernelIdealSheaf B S hS k
        (isQuasiCompact_of_isClosedImmersion' B S hS hk)) n)
    (baseChangeChartDiagram B S hS k hk.1 V)
    (isAffine_and_surjective_baseChangeChartDiagram B S hS k hk V hV).1 hV

/-- Every section of `𝓘ⁿ` over the affine chart comes from an element of `Iⁿ`. -/
theorem exists_kernelIdealSheafZPowSection_eq (n : ℕ)
    (m : (kernelPowModule B S hS k (n : ℤ)).val.obj (op V)) :
    ∃ x : ↥(conormalChartIdeal B S hS k V ^ n),
      kernelIdealSheafZPowSection B S hS k hk V hV n x = m := by
  have hm : (m.1 : chartRing B S hS X.1 X.2 V) ∈ conormalChartIdeal B S hS k V ^ n := by
    have hm' : m.1 ∈ Stacks.Sites.sectionIdeal (O := (smallEtaleRingedSite B S hS X.1 X.2).O)
        (kernelIdealSheafZPow B S hS k (n : ℤ)) (op V) := m.2
    rwa [sectionIdeal_kernelIdealSheafZPow_eq_pow B S hS k hk V hV n] at hm'
  exact ⟨⟨m.1, hm⟩, Subtype.ext rfl⟩

/-- The base change comparison on a pure tensor `1 ⊗ s` is the chart section of `s`. -/
theorem modulePullbackChartBaseChange_one_tmul_kernelPowModule (n : ℕ)
    (s : (kernelPowModule B S hS k (n : ℤ)).val.obj (op V)) :
    letI := chartDiagramAlgebra B S hS k (baseChangeChartDiagram B S hS k hk.1 V)
    modulePullbackChartBaseChange B S hS k (kernelPowModule B S hS k (n : ℤ))
        (baseChangeChartDiagram B S hS k hk.1 V)
        ((1 : chartRing B S hS Z.1 Z.2 (baseChangeChartDiagram B S hS k hk.1 V).U) ⊗ₜ[
          chartRing B S hS X.1 X.2 (baseChangeChartDiagram B S hS k hk.1 V).V] s) =
      modulePullbackChartSection B S hS k (kernelPowModule B S hS k (n : ℤ))
        (baseChangeChartDiagram B S hS k hk.1 V) s :=
  let := chartDiagramAlgebra B S hS k (baseChangeChartDiagram B S hS k hk.1 V)
  (modulePullbackChartBaseChange_tmul B S hS k (kernelPowModule B S hS k (n : ℤ))
    (baseChangeChartDiagram B S hS k hk.1 V) 1 s).trans (one_smul _ _)

/-- **The class map is surjective.** -/
theorem surjective_conormalChartClass (n : ℕ) :
    Function.Surjective (conormalChartClass B S hS k hk V hV n) := by
  let := chartDiagramAlgebra B S hS k (baseChangeChartDiagram B S hS k hk.1 V)
  intro y
  obtain ⟨z, rfl⟩ :=
    (bijective_modulePullbackChartBaseChange_kernelPowModule B S hS k hk V hV n).2 y
  obtain ⟨m, rfl⟩ := TensorProduct.exists_one_tmul_eq_of_surjective
    (isAffine_and_surjective_baseChangeChartDiagram B S hS k hk V hV).2 z
  obtain ⟨x, rfl⟩ := exists_kernelIdealSheafZPowSection_eq B S hS k hk V hV n m
  exact ⟨x, (modulePullbackChartBaseChange_one_tmul_kernelPowModule B S hS k hk V n _).symm⟩

/-- In the sections of `𝓘ⁿ` over the affine chart, `I • ⊤` consists of the sections lying in
`Iⁿ⁺¹`. -/
theorem kernelIdealSheafZPowSection_mem_smul_top_iff (n : ℕ)
    (x : ↥(conormalChartIdeal B S hS k V ^ n)) :
    kernelIdealSheafZPowSection B S hS k hk V hV n x ∈
        conormalChartIdeal B S hS k V •
          (⊤ : Submodule (chartRing B S hS X.1 X.2 V)
            ((kernelPowModule B S hS k (n : ℤ)).val.obj (op V))) ↔
      (x : chartRing B S hS X.1 X.2 V) ∈ conormalChartIdeal B S hS k V ^ (n + 1) := by
  let φ : (kernelPowModule B S hS k (n : ℤ)).val.obj (op V) →ₗ[chartRing B S hS X.1 X.2 V]
      chartRing B S hS X.1 X.2 V :=
    { toFun := fun m => m.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrange : LinearMap.range φ = conormalChartIdeal B S hS k V ^ n := by
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨m, rfl⟩
      obtain ⟨x, rfl⟩ := exists_kernelIdealSheafZPowSection_eq B S hS k hk V hV n m
      exact x.2
    · exact ⟨kernelIdealSheafZPowSection B S hS k hk V hV n ⟨y, hy⟩, rfl⟩
  exact mem_smul_top_iff_of_injective_range_eq_pow _ n φ (fun _ _ h => Subtype.ext h) hrange _

/-- **The kernel of the class map is `Iⁿ⁺¹`.** -/
theorem conormalChartClass_eq_zero_iff (n : ℕ) (x : ↥(conormalChartIdeal B S hS k V ^ n)) :
    conormalChartClass B S hS k hk V hV n x = 0 ↔
      (x : chartRing B S hS X.1 X.2 V) ∈ conormalChartIdeal B S hS k V ^ (n + 1) := by
  let := chartDiagramAlgebra B S hS k (baseChangeChartDiagram B S hS k hk.1 V)
  have h1 : conormalChartClass B S hS k hk V hV n x =
      modulePullbackChartBaseChange B S hS k (kernelPowModule B S hS k (n : ℤ))
        (baseChangeChartDiagram B S hS k hk.1 V)
        ((1 : chartRing B S hS Z.1 Z.2 (baseChangeChartDiagram B S hS k hk.1 V).U) ⊗ₜ[
          chartRing B S hS X.1 X.2 (baseChangeChartDiagram B S hS k hk.1 V).V]
          kernelIdealSheafZPowSection B S hS k hk V hV n x) :=
    (modulePullbackChartBaseChange_one_tmul_kernelPowModule B S hS k hk V n _).symm
  have h2 := TensorProduct.one_tmul_eq_zero_iff_of_surjective
    (R := chartRing B S hS X.1 X.2 (baseChangeChartDiagram B S hS k hk.1 V).V)
    (A := chartRing B S hS Z.1 Z.2 (baseChangeChartDiagram B S hS k hk.1 V).U)
    (M := (kernelPowModule B S hS k (n : ℤ)).val.obj
      (op (baseChangeChartDiagram B S hS k hk.1 V).V))
    (isAffine_and_surjective_baseChangeChartDiagram B S hS k hk V hV).2
    (kernelIdealSheafZPowSection B S hS k hk V hV n x)
  rw [h1, ← map_zero (modulePullbackChartBaseChange B S hS k (kernelPowModule B S hS k (n : ℤ))
    (baseChangeChartDiagram B S hS k hk.1 V)),
    (bijective_modulePullbackChartBaseChange_kernelPowModule B S hS k hk V hV n).1.eq_iff]
  have hker : RingHom.ker (algebraMap
      (chartRing B S hS X.1 X.2 (baseChangeChartDiagram B S hS k hk.1 V).V)
      (chartRing B S hS Z.1 Z.2 (baseChangeChartDiagram B S hS k hk.1 V).U)) =
      conormalChartIdeal B S hS k V :=
    ker_chartDiagramRestrict_baseChangeChartDiagram B S hS k hk.1 V
  rw [h2, hker]
  exact kernelIdealSheafZPowSection_mem_smul_top_iff B S hS k hk V hV n x

/-- **The graded presentation of `𝒞_{Z/X,n}(Z_V)` by the `n`-th power of `I = 𝓘(V)`**, for a
finite generating sequence `f` of `I`: the class map `Iⁿ ⟶ 𝒞_{Z/X,n}(Z_V)` is surjective, has
kernel `Iⁿ⁺¹` and is semilinear over the surjection `𝒪_X(V) ⟶ 𝒪_Z(Z_V)` with kernel `I`. -/
noncomputable def conormalChartPresentation {c : ℕ} (f : Fin c → chartRing B S hS X.1 X.2 V)
    (hf : conormalChartIdeal B S hS k V = Ideal.span (Set.range f)) (n : ℕ) :
    Stacks.RingTheory.QuasiRegular.GradedPresentation (chartRing B S hS X.1 X.2 V)
      (chartRing B S hS Z.1 Z.2 (baseChangeChartDiagram B S hS k hk.1 V).U) c n
      (((modulePullback B S hS k).obj (kernelPowModule B S hS k (n : ℤ))).val.obj
        (op (baseChangeChartDiagram B S hS k hk.1 V).U)) where
  f := f
  ψ := chartDiagramRestrict B S hS k (baseChangeChartDiagram B S hS k hk.1 V)
  surjective_ψ := (isAffine_and_surjective_baseChangeChartDiagram B S hS k hk V hV).2
  J := conormalChartIdeal B S hS k V
  span_J := hf
  ker_ψ := ker_chartDiagramRestrict_baseChangeChartDiagram B S hS k hk.1 V
  g := conormalChartClass B S hS k hk V hV n
  smul_g := conormalChartClass_smul B S hS k hk V hV n
  surjective_g := surjective_conormalChartClass B S hS k hk V hV n
  ker_g := conormalChartClass_eq_zero_iff B S hS k hk V hV n

end ClassMap

/-! ### Multiplicativity -/

section Mul

variable (k : Z ⟶ X) (hk : yoneda.relativelyRepresentable k.hom) (V : SmallEtale B S hS X.1)

/-- **The chart sections of the conormal algebra multiply as the sections of the powers of the
kernel ideal sheaf do**, read through an equality of degrees: over the base-changed chart, the
chart section of a product `st` of a section of `𝓘ⁱ` and a section of `𝓘ʲ` is the product, in the
conormal algebra, of the chart sections of `s` and `t`. -/
theorem modulePullbackChartSection_kernel_mul {i j l : ℤ} (h : i + j = l)
    (s : (kernelPowModule B S hS k i).val.obj (op V))
    (t : (kernelPowModule B S hS k j).val.obj (op V))
    (st : (kernelPowModule B S hS k l).val.obj (op V))
    (hst : SheafOfModules.reesVal (kernelIdealSheaf B S hS k) (n := l) st =
      SheafOfModules.reesVal (kernelIdealSheaf B S hS k) (n := i) s *
        SheafOfModules.reesVal (kernelIdealSheaf B S hS k) (n := j) t) :
    modulePullbackChartSection B S hS k (kernelPowModule B S hS k l)
        (baseChangeChartDiagram B S hS k hk V) st =
      (eqToHom (congrArg (conormalAlgebra B S hS k).piece h)).val.app
        (op (baseChangeChartDiagram B S hS k hk V).U)
        (((conormalAlgebra B S hS k).mul i j).app (op (baseChangeChartDiagram B S hS k hk V).U)
          (modulePullbackChartSection B S hS k (kernelPowModule B S hS k i)
            (baseChangeChartDiagram B S hS k hk V) s)
          (modulePullbackChartSection B S hS k (kernelPowModule B S hS k j)
            (baseChangeChartDiagram B S hS k hk V) t)) := by
  subst h
  have hst' : st = ((kernelIdealGradedAlgebra B S hS k).mul i j).app (op V) s t :=
    SheafOfModules.reesPiece_ext (kernelIdealSheaf B S hS k)
      (hst.trans (SheafOfModules.reesVal_reesMul_app _ _ i j (op V) s t).symm)
  rw [hst', eqToHom_refl]
  exact modulePullbackChartSection_mul B S hS k (kernelIdealGradedAlgebra B S hS k)
    (baseChangeChartDiagram B S hS k hk V) i j s t

end Mul

/-! ### Generation in degree one -/

section Generation

variable (k : Z ⟶ X) (hk : IsClosedImmersion B S hS k.hom) (V : SmallEtale B S hS X.1)
  (hV : IsAffine (chartScheme V))
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Z))
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom A (conormalAlgebra B S hS k))

/-- The degree-`m` component of a homomorphism into the conormal algebra, with target spelled as
the inverse image of the `m`-th power of the kernel ideal sheaf. -/
noncomputable def toKernelPowPullback (m : ℤ) :
    A.piece m ⟶ (modulePullback B S hS k).obj (kernelPowModule B S hS k m) :=
  Φ.app m

/-- The multiplication of the conormal algebra, with source and target spelled as inverse images
of powers of the kernel ideal sheaf. -/
noncomputable def kernelPowPullbackMul (i j : ℤ) (W : (SmallEtale B S hS Z.1)ᵒᵖ) :
    ((modulePullback B S hS k).obj (kernelPowModule B S hS k i)).val.obj W →
      ((modulePullback B S hS k).obj (kernelPowModule B S hS k j)).val.obj W →
        ((modulePullback B S hS k).obj (kernelPowModule B S hS k (i + j))).val.obj W :=
  fun x y => ((conormalAlgebra B S hS k).mul i j).app W x y

/-- The degreewise components of a homomorphism into the conormal algebra are multiplicative. -/
theorem toKernelPowPullback_map_mul (i j : ℤ) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (x : (A.piece i).val.obj W) (y : (A.piece j).val.obj W) :
    (toKernelPowPullback B S hS k A Φ (i + j)).val.app W ((A.mul i j).app W x y) =
      kernelPowPullbackMul B S hS k i j W ((toKernelPowPullback B S hS k A Φ i).val.app W x)
        ((toKernelPowPullback B S hS k A Φ j).val.app W y) :=
  Φ.map_mul i j W x y

/-- The degreewise components commute with transport along an equality of degrees. -/
theorem toKernelPowPullback_eqToHom {i j : ℤ} (h : i = j) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (y : (A.piece i).val.obj W) :
    (eqToHom (congrArg (fun m => (modulePullback B S hS k).obj (kernelPowModule B S hS k m))
        h)).val.app W ((toKernelPowPullback B S hS k A Φ i).val.app W y) =
      (toKernelPowPullback B S hS k A Φ j).val.app W
        ((eqToHom (congrArg A.piece h)).val.app W y) := by
  subst h
  rfl

/-- **The chart sections multiply**, in the spelling of inverse images of powers of the kernel
ideal sheaf. -/
theorem modulePullbackChartSection_kernelPowPullbackMul {i j l : ℤ} (h : i + j = l)
    (s : (kernelPowModule B S hS k i).val.obj (op V))
    (t : (kernelPowModule B S hS k j).val.obj (op V))
    (st : (kernelPowModule B S hS k l).val.obj (op V))
    (hst : SheafOfModules.reesVal (kernelIdealSheaf B S hS k) (n := l) st =
      SheafOfModules.reesVal (kernelIdealSheaf B S hS k) (n := i) s *
        SheafOfModules.reesVal (kernelIdealSheaf B S hS k) (n := j) t) :
    modulePullbackChartSection B S hS k (kernelPowModule B S hS k l)
        (baseChangeChartDiagram B S hS k hk.1 V) st =
      (eqToHom (congrArg (fun m => (modulePullback B S hS k).obj (kernelPowModule B S hS k m))
        h)).val.app (op (baseChangeChartDiagram B S hS k hk.1 V).U)
        (kernelPowPullbackMul B S hS k i j (op (baseChangeChartDiagram B S hS k hk.1 V).U)
          (modulePullbackChartSection B S hS k (kernelPowModule B S hS k i)
            (baseChangeChartDiagram B S hS k hk.1 V) s)
          (modulePullbackChartSection B S hS k (kernelPowModule B S hS k j)
            (baseChangeChartDiagram B S hS k hk.1 V) t)) := by
  subst h
  exact modulePullbackChartSection_kernel_mul B S hS k hk.1 V rfl s t st hst

/-- **Every class of degree at least one is in the image of a unital homomorphism into the
conormal algebra which is the identity in degree one**: over the base-changed chart, the
classes of `Iⁿ` are generated by products of classes of `I`, and the homomorphism is
multiplicative. -/
theorem exists_toKernelPowPullback_eq_conormalChartClass
    (ι : (conormalAlgebra B S hS k).piece 1 ⟶ A.piece 1) (hι : ι ≫ Φ.app 1 = 𝟙 _)
    (n : ℕ) (hn : 1 ≤ n) (x : ↥(conormalChartIdeal B S hS k V ^ n)) :
    ∃ a : (A.piece (n : ℤ)).val.obj (op (baseChangeChartDiagram B S hS k hk.1 V).U),
      (toKernelPowPullback B S hS k A Φ (n : ℤ)).val.app _ a =
        conormalChartClass B S hS k hk V hV n x := by
  have hι' : ∀ y : ((modulePullback B S hS k).obj
      (kernelPowModule B S hS k ((1 : ℕ) : ℤ))).val.obj
        (op (baseChangeChartDiagram B S hS k hk.1 V).U),
      (toKernelPowPullback B S hS k A Φ ((1 : ℕ) : ℤ)).val.app
      (op (baseChangeChartDiagram B S hS k hk.1 V).U) (ι.val.app _ y) = y := fun y =>
    congrArg (fun m => m.val.app (op (baseChangeChartDiagram B S hS k hk.1 V).U) y) hι
  induction n, hn using Nat.le_induction with
  | base => exact ⟨_, hι' _⟩
  | succ n hn ih =>
    have hdeg : ((n : ℤ) + ((1 : ℕ) : ℤ)) = ((n + 1 : ℕ) : ℤ) :=
      (Nat.cast_add n 1).symm
    obtain ⟨z, hz⟩ := x
    have hz' : z ∈ conormalChartIdeal B S hS k V ^ n * conormalChartIdeal B S hS k V := by
      rwa [← pow_succ]
    induction hz' using Submodule.mul_induction_on' with
    | mem_mul_mem p hp q hq =>
      obtain ⟨a₁, ha₁⟩ := ih ⟨p, hp⟩
      have hq1 : q ∈ conormalChartIdeal B S hS k V ^ 1 := by rwa [pow_one]
      refine ⟨(eqToHom (congrArg A.piece hdeg)).val.app _
        ((A.mul (n : ℤ) ((1 : ℕ) : ℤ)).app _ a₁
          (ι.val.app _ (conormalChartClass B S hS k hk V hV 1 ⟨q, hq1⟩))), ?_⟩
      rw [← toKernelPowPullback_eqToHom B S hS k A Φ hdeg, toKernelPowPullback_map_mul, ha₁,
        hι', conormalChartClass_apply, conormalChartClass_apply, conormalChartClass_apply]
      exact (modulePullbackChartSection_kernelPowPullbackMul B S hS k hk V hdeg
        (kernelIdealSheafZPowSection B S hS k hk V hV n ⟨p, hp⟩)
        (kernelIdealSheafZPowSection B S hS k hk V hV 1 ⟨q, hq1⟩)
        (kernelIdealSheafZPowSection B S hS k hk V hV (n + 1) ⟨p * q, hz⟩) rfl).symm
    | add z₁ hz₁ z₂ hz₂ h₁ h₂ =>
      have hz₁' : z₁ ∈ conormalChartIdeal B S hS k V ^ (n + 1) := by
        rwa [pow_succ]
      have hz₂' : z₂ ∈ conormalChartIdeal B S hS k V ^ (n + 1) := by
        rwa [pow_succ]
      obtain ⟨b₁, hb₁⟩ := h₁ hz₁'
      obtain ⟨b₂, hb₂⟩ := h₂ hz₂'
      refine ⟨b₁ + b₂, ?_⟩
      rw [map_add, hb₁, hb₂]
      exact ((conormalChartClass B S hS k hk V hV (n + 1)).map_add ⟨z₁, hz₁'⟩ ⟨z₂, hz₂'⟩).symm

include hV in
/-- **A unital homomorphism into the conormal algebra which is the identity in degree one is
surjective on the sections over the base-changed chart in every degree at least one.** -/
theorem surjective_toKernelPowPullback_app
    (ι : (conormalAlgebra B S hS k).piece 1 ⟶ A.piece 1) (hι : ι ≫ Φ.app 1 = 𝟙 _)
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective ((toKernelPowPullback B S hS k A Φ (n : ℤ)).val.app
      (op (baseChangeChartDiagram B S hS k hk.1 V).U)) := by
  intro y
  obtain ⟨x, rfl⟩ := surjective_conormalChartClass B S hS k hk V hV n y
  exact exists_toKernelPowPullback_eq_conormalChartClass B S hS k hk V hV A Φ ι hι n hn x

/-- The function `1` lies in `I⁰`. -/
theorem one_mem_conormalChartIdeal_pow_zero :
    (1 : chartRing B S hS X.1 X.2 V) ∈ conormalChartIdeal B S hS k V ^ 0 := by
  simp

/-- **The class of `1` in degree zero is the unit of the conormal algebra.**  The unit `u` of the
conormal algebra over the base-changed chart is the class of some `s`, and the class `e` of `1`
satisfies `e = e·u = e·(class of s) = class of s = u`, by the unit law and multiplicativity. -/
theorem conormalChartClass_zero_one :
    conormalChartClass B S hS k hk V hV 0 ⟨1, one_mem_conormalChartIdeal_pow_zero B S hS k V⟩ =
      (conormalAlgebra B S hS k).one.eval (op (baseChangeChartDiagram B S hS k hk.1 V).U) := by
  set T := op (baseChangeChartDiagram B S hS k hk.1 V).U
  set e := conormalChartClass B S hS k hk V hV 0
    ⟨1, one_mem_conormalChartIdeal_pow_zero B S hS k V⟩
  obtain ⟨⟨s, hs⟩, hes⟩ := surjective_conormalChartClass B S hS k hk V hV 0
    ((conormalAlgebra B S hS k).one.eval T)
  have h1 : kernelPowPullbackMul B S hS k ((0 : ℕ) : ℤ) 0 T e
      ((conormalAlgebra B S hS k).one.eval T) = e :=
    eq_of_heq ((conormalAlgebra B S hS k).mul_one ((0 : ℕ) : ℤ) T e)
  have h2 := modulePullbackChartSection_kernelPowPullbackMul B S hS k hk V
    (i := ((0 : ℕ) : ℤ)) (j := ((0 : ℕ) : ℤ)) (l := ((0 : ℕ) : ℤ)) rfl
    (kernelIdealSheafZPowSection B S hS k hk V hV 0
      ⟨1, one_mem_conormalChartIdeal_pow_zero B S hS k V⟩)
    (kernelIdealSheafZPowSection B S hS k hk V hV 0 ⟨s, hs⟩)
    (kernelIdealSheafZPowSection B S hS k hk V hV 0 ⟨s, hs⟩) (one_mul _).symm
  rw [eqToHom_refl] at h2
  have h3 : kernelPowPullbackMul B S hS k ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) T e
      (conormalChartClass B S hS k hk V hV 0 ⟨s, hs⟩) =
      conormalChartClass B S hS k hk V hV 0 ⟨s, hs⟩ := h2.symm
  rw [hes] at h3
  exact h1.symm.trans h3

include hV in
/-- **A unital homomorphism into the conormal algebra is surjective on the sections over the
base-changed chart in degree zero.**  Degree zero is generated by the class of `1`, which is
the unit, and the unit is in the image. -/
theorem surjective_toKernelPowPullback_app_zero :
    Function.Surjective ((toKernelPowPullback B S hS k A Φ ((0 : ℕ) : ℤ)).val.app
      (op (baseChangeChartDiagram B S hS k hk.1 V).U)) := by
  intro y
  obtain ⟨⟨r, hr⟩, rfl⟩ := surjective_conormalChartClass B S hS k hk V hV 0 y
  have hr' : (⟨r, hr⟩ : ↥(conormalChartIdeal B S hS k V ^ 0)) =
      r • ⟨1, one_mem_conormalChartIdeal_pow_zero B S hS k V⟩ :=
    Subtype.ext (mul_one r).symm
  refine ⟨(show (structureRingSheaf B S hS Z).obj.obj
      (op (baseChangeChartDiagram B S hS k hk.1 V).U) from
      chartDiagramRestrict B S hS k (baseChangeChartDiagram B S hS k hk.1 V) r) •
    A.one.eval (op (baseChangeChartDiagram B S hS k hk.1 V).U), ?_⟩
  rw [hr', conormalChartClass_smul, conormalChartClass_zero_one]
  refine ((toKernelPowPullback B S hS k A Φ ((0 : ℕ) : ℤ)).val.app
    (op (baseChangeChartDiagram B S hS k hk.1 V).U)).hom.map_smul _ _ |>.trans ?_
  exact congrArg _ (Φ.map_one (op (baseChangeChartDiagram B S hS k hk.1 V).U))

end Generation

end AlgebraicGeometry.Space

end
