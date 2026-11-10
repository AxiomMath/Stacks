module

public import StacksFrontier.CategoryTheory.Limits.FunctorCategory.ShortExactColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationPowVanishing
public import StacksFrontier.Cotangent.SurjectionSiteAugmentationSections
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded pieces of the augmentation filtration are the symmetric powers of `Ω`

We identify the graded pieces of the filtration `… ⊆ 𝒦² ⊆ 𝒦 ⊆ Ō` of the presheaf `Ō = 𝒪 ⊗_A B̲`
on the small model of the polynomial site `C_{B/A}` with the symmetric powers of
`Ω = i^*Ω_{𝒪/A}`:

`𝒦ⁿ/𝒦ⁿ⁺¹ ≅ Sym^n_{B̲}(Ω)`

as presheaves of `B`-modules, and packages the resulting short exact sequence
`0 → 𝒦ⁿ⁺¹ → 𝒦ⁿ → Sym^n_{B̲}(Ω) → 0`.

## Main definitions

* `Stacks.augDiff`: the conormal map `p ↦ 1 ⊗ p - α(p) ⊗ 1` of an `A`-algebra `P` augmented to
  `R`, with values in `R ⊗_A P`.
* `Stacks.symPowDiagramMap` and `Stacks.symPowDiagramMapIso`: the `n`-th symmetric power of a
  map, respectively of an isomorphism, of diagrams of modules over a constant coefficient ring.
* `CommAlgCat.smallPolynomialAugmentationSymProd`: multiplication in `Ō(U)`, as the `B`-algebra
  map out of `Sym_B(𝒦(U))` extending the inclusion of `𝒦(U)`.
* `CommAlgCat.smallPolynomialAugmentationSymMul`: the map of presheaves
  `Sym^n_{B̲}(𝒦/𝒦²) ⟶ 𝒦ⁿ/𝒦ⁿ⁺¹` induced by multiplication in `Ō`.
* `CommAlgCat.smallPolynomialCotangentToGraded`: the conormal map `Ω ⟶ 𝒦/𝒦²`, the map of
  presheaves sending the pure differential `1 ⊗ d p` to the class of `1 ⊗ p - α(p)`.
* `CommAlgCat.smallPolynomialAugmentationGradedSectionsEquiv` and
  `CommAlgCat.smallPolynomialAugmentationGradedOneSectionsEquiv`: the sections of `𝒦ⁿ/𝒦ⁿ⁺¹` and
  of `𝒦/𝒦²` over an object, in the coordinates of the polynomial ring `B[S]`.
* `CommAlgCat.smallPolynomialCotangentBasis`,
  `CommAlgCat.smallPolynomialAugmentationGradedOneBasis` and
  `CommAlgCat.smallPolynomialAugmentationGradedBasis`: the bases of `Ω(U)`, of `𝒦(U)/𝒦²(U)` and
  of `𝒦ⁿ(U)/𝒦ⁿ⁺¹(U)` on the variables, respectively on the degree-`n` monomials in the
  generators `X s - g(s)`.
* `CommAlgCat.smallPolynomialAugmentationSymmetricPowerShortComplex`: the short complex
  `𝒦ⁿ⁺¹ → 𝒦ⁿ → Sym^n_{B̲}(Ω)` of presheaves.

## Main results

* `CommAlgCat.smallPolynomialCotangentGradedIso`: **`Ω ≅ 𝒦/𝒦²`** as presheaves of `B`-modules.
* `CommAlgCat.smallPolynomialAugmentationSymMulIso`: **`Sym^n_{B̲}(𝒦/𝒦²) ≅ 𝒦ⁿ/𝒦ⁿ⁺¹`**,
  multiplication in `Ō` being an isomorphism.
* `CommAlgCat.smallPolynomialAugmentationGradedSymmetricPowerIso`: **the main result**,
  `𝒦ⁿ/𝒦ⁿ⁺¹ ≅ Sym^n_{B̲}(Ω)` as presheaves of `B`-modules.
* `CommAlgCat.smallPolynomialAugmentationSymmetricPowerShortComplex_shortExact`: the short exact
  sequence `0 → 𝒦ⁿ⁺¹ → 𝒦ⁿ → Sym^n_{B̲}(Ω) → 0` of presheaves of `B`-modules.

## Implementation notes

Both maps are the canonical ones of the source, so that naturality is a computation with ring
maps rather than with coordinates, and only their bijectivity is checked in coordinates.

The map `Sym^n_{B̲}(𝒦/𝒦²) ⟶ 𝒦ⁿ/𝒦ⁿ⁺¹` is multiplication: over an object `U` the `B`-algebra map
`Sym_B(𝒦(U)) → Ō(U)` extending the inclusion of `𝒦(U)` carries the degree-`n` part into `𝒦ⁿ(U)`,
and the resulting map `Sym^n_B(𝒦(U)) → 𝒦ⁿ(U)/𝒦ⁿ⁺¹(U)` factors through `Sym^n_B(𝒦(U)/𝒦²(U))`
because a product of `n` elements of `𝒦(U)` one of which lies in `𝒦²(U)` lies in `𝒦ⁿ⁺¹(U)`. The
factorization uses the right-exactness of `Sym^n`, `symmetric_ker_le_im_alpha`, to know the
kernel of `Sym^n(𝒦(U)) → Sym^n(𝒦(U)/𝒦²(U))`; in degree `0` that statement does not apply and the
kernel is instead computed to be zero, the degree-`0` symmetric power of any module being `B`
itself.

The map `Ω ⟶ 𝒦/𝒦²` is the conormal map `1 ⊗ d p ↦ [1 ⊗ p - α(p)]`, obtained from the
`A`-derivation `p ↦ [1 ⊗ p - α(p)]` of `P` into `𝒦(U)/𝒦²(U)` read as a `P`-module through the
augmentation; it is a derivation because the defect of the Leibniz rule is the product of two
elements of `𝒦(U)` (`Stacks.augDiff_mul`). The `P`-module and `A`-module structures on
`𝒦(U)/𝒦²(U)` that the derivation needs are not instances, so they are supplied as `local
instance`s in the section where the derivation is built, and nowhere else.

Bijectivity of both maps is read off from the coordinate description of the sections:
`MvPolynomial.augmentationGradedOneEquiv` makes `𝒦(U)/𝒦²(U)` free on the variables, matching the
basis of `Ω(U) = B ⊗_P Ω[P⁄A]` given by the differentials of the variables, and
`MvPolynomial.symmetricPowerEquivAugmentationGraded` identifies `Sym^n_B` of that free module
with `𝒦ⁿ(U)/𝒦ⁿ⁺¹(U)` by a map which, by its characterising equation
`MvPolynomial.symmetricPowerEquivAugmentationGraded_prod_ι`, is exactly multiplication on the
products of `n` generators. Since those products are the monomial basis of the symmetric power
(`SymPow.exists_prod_ι_eq_coe_basisSymmetricPower_uniform`, which is why the otherwise unrelated
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify` is imported), the two maps agree
on a basis and multiplication is bijective.

Exactness of the sequence of presheaves is objectwise, `ShortComplex.shortExact_of_app`.

**Two spellings of the same type.** The polynomial algebra `((smallSiteToOver A B κ).obj X).left`
of an object is only *definitionally* `MvPolynomial ↥(X.unop.unop.1) A`, and the index type
`↥(X.unop.unop.1)` mentions `Cardinal.out κ`, which is not type-correct at `implicit`
transparency. A goal mixing the two spellings therefore defeats `rw` and `simp` with a
`Quotient.out κ` application-type-mismatch that is not a real type error. Every piece of tensor
algebra below is consequently factored through the generic `Stacks.augDiff` section, where the
augmented algebra is a variable and no such mixing can arise, and every site-level term is
wrapped in a `def` with a declared type so that the mixed spelling never enters a goal.

Nothing here needs `A → B` to be surjective.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08RD](https://stacks.math.columbia.edu/tag/08RD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace Stacks

section AugmentedTensor

variable {A : Type*} [CommRing A] {R : Type*} [CommRing R] [Algebra A R]
  {P : Type*} [CommRing P] [Algebra A P] (α : P →ₐ[A] R)

/-- **The conormal map of an augmented algebra**: for an `A`-algebra `P` with an augmentation
`α : P → R`, the map `p ↦ 1 ⊗ p - α(p) ⊗ 1` from `P` to `R ⊗_A P`. Its values lie in the kernel
of the augmentation `R ⊗_A P → R`, and the defect of the Leibniz rule is a product of two such
values (`Stacks.augDiff_mul`), which is what makes it a derivation modulo the square of that
kernel. -/
def augDiff (p : P) : R ⊗[A] P :=
  (1 : R) ⊗ₜ[A] p - (α p) ⊗ₜ[A] (1 : P)

/-- The conormal map sends `p` to `1 ⊗ p - α(p) ⊗ 1`. -/
lemma augDiff_def (p : P) :
    augDiff α p = (1 : R) ⊗ₜ[A] p - (α p) ⊗ₜ[A] (1 : P) :=
  rfl

/-- The structure map of `R ⊗_A P` over `R` is `r ↦ r ⊗ 1`. -/
lemma algebraMap_tensor (r : R) :
    algebraMap R (R ⊗[A] P) r = r ⊗ₜ[A] (1 : P) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

/-- The conormal map is additive. -/
lemma augDiff_add (p q : P) : augDiff α (p + q) = augDiff α p + augDiff α q := by
  simp only [augDiff_def, map_add, TensorProduct.tmul_add, TensorProduct.add_tmul]
  abel

/-- The conormal map is `A`-linear, `A` acting on `R ⊗_A P` through `R`. -/
lemma augDiff_smul (a : A) (p : P) :
    augDiff α (a • p) = (algebraMap A R a) • augDiff α p := by
  rw [algebraMap_smul]
  simp only [augDiff_def, map_smul, smul_sub, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- **The Leibniz defect of the conormal map** is the product of two of its values. -/
lemma augDiff_mul (p q : P) :
    augDiff α (p * q) =
      α p • augDiff α q + α q • augDiff α p + augDiff α p * augDiff α q := by
  have hu : ((1 : R) ⊗ₜ[A] p) * ((1 : R) ⊗ₜ[A] q) = (1 : R) ⊗ₜ[A] (p * q) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  simp only [augDiff_def, ← algebraMap_tensor, map_mul, Algebra.smul_def]
  rw [← hu]
  ring

/-- The conormal map lands in the kernel of the augmentation of `R ⊗_A P`. -/
lemma augDiff_mem_ker (ε : (R ⊗[A] P) →ₐ[R] R)
    (hε : ∀ (r : R) (p : P), ε (r ⊗ₜ[A] p) = r • α p) (p : P) :
    augDiff α p ∈ RingHom.ker (ε : (R ⊗[A] P) →+* R) := by
  rw [RingHom.mem_ker]
  change ε (augDiff α p) = 0
  rw [augDiff_def, map_sub, hε, hε, map_one, one_smul, smul_eq_mul, mul_one, sub_self]

/-- **The conormal map is natural** in the augmented algebra: a map `g : P → Q` over the
augmentations carries `1 ⊗ p - α(p) ⊗ 1` to `1 ⊗ g(p) - α'(g(p)) ⊗ 1`. -/
lemma augDiff_map {Q : Type*} [CommRing Q] [Algebra A Q] (α' : Q →ₐ[A] R) (g : P →ₐ[A] Q)
    (φ : (R ⊗[A] P) →ₐ[R] (R ⊗[A] Q))
    (hφ : ∀ (r : R) (q : P), φ (r ⊗ₜ[A] q) = r ⊗ₜ[A] g q)
    (hg : ∀ q : P, α' (g q) = α q) (p : P) :
    φ (augDiff α p) = augDiff α' (g p) := by
  rw [augDiff_def, map_sub, hφ, hφ, map_one, augDiff_def, hg]

/-- **The conormal map of a polynomial algebra at a variable, in coordinates**: the
identification `R ⊗_A A[σ] = R[σ]` carries `1 ⊗ X s - ε(X s) ⊗ 1` to `X s - C (g s)`, the
standard generator of the augmentation ideal of `R[σ]` at `g`. -/
lemma algebraTensorAlgEquiv_augDiff_X {σ : Type*} (g : σ → R) (s : σ) :
    MvPolynomial.algebraTensorAlgEquiv A R
        (augDiff (MvPolynomial.aeval g : MvPolynomial σ A →ₐ[A] R) (MvPolynomial.X s)) =
      MvPolynomial.X s - MvPolynomial.C (g s) := by
  rw [augDiff_def, map_sub, MvPolynomial.algebraTensorAlgEquiv_tmul,
    MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul, MvPolynomial.map_X, map_one,
    MvPolynomial.aeval_X, Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq]

end AugmentedTensor

section BasisHelpers

/-- **A linear map carrying one basis to another, index for index, is bijective.** -/
lemma bijective_of_basis_eq {R : Type*} [CommRing R] {ι : Type*} {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (f : M →ₗ[R] N)
    (h : ∀ i, f (b i) = b' i) : Function.Bijective f := by
  have hf : f = (b.equiv b' (Equiv.refl ι)).toLinearMap :=
    b.ext fun i => by
      simp only [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
      exact h i
  rw [hf]
  exact (b.equiv b' (Equiv.refl ι)).bijective

/-- The basis transported from `ι →₀ R` along the inverse of an isomorphism, read on an index
whose basis vector is known. -/
lemma basisSingleOne_map_symm_apply {R : Type*} [CommRing R] {ι : Type*} {M : Type*}
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] (ι →₀ R)) (i : ι) (m : M)
    (h : e m = Finsupp.single i 1) :
    (Finsupp.basisSingleOne.map e.symm : Module.Basis ι R M) i = m := by
  rw [Module.Basis.map_apply, congrFun Finsupp.coe_basisSingleOne i, ← h,
    LinearEquiv.symm_apply_apply]

/-- The base change of the monomial basis of the differentials of a polynomial algebra, read on a
variable. -/
@[ega "0 20.4.13" "more general"]
lemma baseChange_basisOfMvPolynomialAlgEquiv_apply {A : Type*} [CommRing A]
    {P : Type*} [CommRing P] [Algebra A P] (R : Type*) [CommRing R] [Algebra P R]
    {ι : Type*} (E : P ≃ₐ[A] MvPolynomial ι A) (i : ι) :
    (KaehlerDifferential.basisOfMvPolynomialAlgEquiv E).baseChange R i =
      (1 : R) ⊗ₜ[P] KaehlerDifferential.D A P (E.symm (MvPolynomial.X i)) := by
  rw [Module.Basis.baseChange_apply, KaehlerDifferential.basisOfMvPolynomialAlgEquiv_apply]

/-- `Sym^n` of the identity is the identity. -/
lemma symMap_id_apply {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (n : ℕ)
    (z : ↥(SymPow.symmetricPower n R M)) :
    SymPow.symMap n (LinearMap.id : M →ₗ[R] M) z = z :=
  Subtype.ext (by rw [SymPow.symMap_coe, Stacks.ChaoticSite.symAlgMap_id]; rfl)

/-- A product of `n` elements of an ideal lies in its `n`-th power. -/
lemma prod_mem_pow {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) (v : Fin n → R)
    (h : ∀ i, v i ∈ I) : ∏ i, v i ∈ I ^ n := by
  induction n with
  | zero =>
    rw [Finset.univ_eq_empty, Finset.prod_empty, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ k ih =>
    rw [Fin.prod_univ_castSucc, pow_succ]
    exact Ideal.mul_mem_mul (ih (fun i => v i.castSucc) fun i => h _) (h _)

end BasisHelpers

section SymmetricPowerDiagram

open Stacks.ChaoticSite

universe v' w'

variable {C : Type u} [Category.{v'} C] {R : Type w'} [CommRing R]
  {F G : Cᵒᵖ ⥤ ModuleCat.{max u v' w'} R}

/-- **`Sym^n` of a map of diagrams of modules** over a constant coefficient ring. -/
def symPowDiagramMap (η : F ⟶ G) (n : ℕ) :
    symmetricPowerDiagram C R F n ⟶ symmetricPowerDiagram C R G n where
  app X := ModuleCat.ofHom (SymPow.symMap n (η.app X).hom)
  naturality X Y f := ModuleCat.hom_ext (LinearMap.ext fun z => by
    have h : ((η.app Y).hom).comp ((F.map f).hom) = ((G.map f).hom).comp ((η.app X).hom) :=
      congrArg ModuleCat.Hom.hom (η.naturality f)
    exact ((symMap_comp_apply n (F.map f).hom (η.app Y).hom z).trans
      (congrArg (fun φ => SymPow.symMap n φ z) h)).trans
      (symMap_comp_apply n (η.app X).hom (G.map f).hom z).symm)

/-- The component of `Sym^n` of a map of diagrams at an object is `Sym^n` of its component. -/
lemma symPowDiagramMap_app (η : F ⟶ G) (n : ℕ) (X : Cᵒᵖ) :
    (symPowDiagramMap η n).app X = ModuleCat.ofHom (SymPow.symMap n (η.app X).hom) :=
  rfl

/-- **`Sym^n` of an isomorphism of diagrams of modules** is an isomorphism. -/
def symPowDiagramMapIso (e : F ≅ G) (n : ℕ) :
    symmetricPowerDiagram C R F n ≅ symmetricPowerDiagram C R G n where
  hom := symPowDiagramMap e.hom n
  inv := symPowDiagramMap e.inv n
  hom_inv_id := by
    refine NatTrans.ext (funext fun X => ModuleCat.hom_ext (LinearMap.ext fun z => ?_))
    have h : ((e.inv.app X).hom).comp ((e.hom.app X).hom) = LinearMap.id :=
      congrArg ModuleCat.Hom.hom (e.hom_inv_id_app X)
    exact ((symMap_comp_apply n (e.hom.app X).hom (e.inv.app X).hom z).trans
      (congrArg (fun φ => SymPow.symMap n φ z) h)).trans (Stacks.symMap_id_apply n z)
  inv_hom_id := by
    refine NatTrans.ext (funext fun X => ModuleCat.hom_ext (LinearMap.ext fun z => ?_))
    have h : ((e.hom.app X).hom).comp ((e.inv.app X).hom) = LinearMap.id :=
      congrArg ModuleCat.Hom.hom (e.inv_hom_id_app X)
    exact ((symMap_comp_apply n (e.inv.app X).hom (e.hom.app X).hom z).trans
      (congrArg (fun φ => SymPow.symMap n φ z) h)).trans (Stacks.symMap_id_apply n z)

end SymmetricPowerDiagram

end Stacks

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-! ### Multiplication from the symmetric powers of `𝒦` to the powers of `𝒦` -/

/-- **Multiplication in `Ō(U)`**, as a `B`-algebra map `Sym_B(𝒦(U)) → Ō(U)`: the algebra map
extending the inclusion of the sections of `𝒦` into those of `Ō`. On a product of `n` degree-one
generators it is the product of the corresponding `n` elements of `𝒦(U)`. -/
def smallPolynomialAugmentationSymProd (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    SymmetricAlgebra (B : Type u)
        ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X) →ₐ[(B : Type u)]
      ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u) :=
  SymmetricAlgebra.lift (smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X).subtype

/-- Multiplication sends a degree-one generator of `Sym_B(𝒦(U))` to the corresponding element of
`𝒦(U)`. -/
@[simp]
lemma smallPolynomialAugmentationSymProd_ι (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (y : ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)) :
    smallPolynomialAugmentationSymProd A B κ X
        (SymmetricAlgebra.ι (B : Type u) _ y) = (y : _) :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- Multiplication carries the degree-`n` part of `Sym_B(𝒦(U))` into `𝒦ⁿ(U)`: a product of `n`
elements of the ideal lies in its `n`-th power. -/
lemma smallPolynomialAugmentationSymProd_mem_pow
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) (n : ℕ)
    {x : SymmetricAlgebra (B : Type u)
      ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)}
    (hx : x ∈ SymPow.symmetricPower n (B : Type u)
      ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)) :
    smallPolynomialAugmentationSymProd A B κ X x ∈
      smallPolynomialAugmentationIdeal A B κ X ^ n := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | add x y i hx hy ihx ihy =>
    rw [map_add]
    exact Ideal.add_mem _ ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨y, rfl⟩ := hm
    have hy : (y : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) ∈
        smallPolynomialAugmentationIdeal A B κ X := by
      have : (y : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) ∈
          smallPolynomialAugmentationIdeal A B κ X ^ 1 := y.2
      rwa [pow_one] at this
    rw [map_mul, pow_succ']
    refine Ideal.mul_mem_mul ?_ ih
    rw [smallPolynomialAugmentationSymProd_ι]
    exact hy

/-- **Multiplication as a map of sections `Sym^n_B(𝒦(U)) → 𝒦ⁿ(U)`.** -/
def smallPolynomialAugmentationSymPowToPow (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    ↥(SymPow.symmetricPower n (B : Type u)
        ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)) →ₗ[(B : Type u)]
      ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n X) :=
  LinearMap.restrict (smallPolynomialAugmentationSymProd A B κ X).toLinearMap
    (fun _ hx => smallPolynomialAugmentationSymProd_mem_pow A B κ X n hx)

/-- The map `Sym^n_B(𝒦(U)) → 𝒦ⁿ(U)`, read in `Ō(U)`, is multiplication. -/
@[simp]
lemma coe_smallPolynomialAugmentationSymPowToPow (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (x : ↥(SymPow.symmetricPower n (B : Type u)
      ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X))) :
    (smallPolynomialAugmentationSymPowToPow A B κ n X x :
        ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) =
      smallPolynomialAugmentationSymProd A B κ X x :=
  rfl

/-- **The sections of the graded piece `𝒦ⁿ/𝒦ⁿ⁺¹`** over an object of the site: the quotient of
the sections of `𝒦ⁿ` by those of `𝒦ⁿ⁺¹`, read off the presheaf.

This is a name for the value of `CommAlgCat.smallPolynomialAugmentationGraded`, not a second
spelling of it: the module structure of the presheaf's value is the one carried by the
`ModuleCat` object, and writing the quotient out instead makes every elaboration below rederive
it. -/
abbrev smallPolynomialAugmentationGradedSections (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) : Type u :=
  ↥((smallPolynomialAugmentationGraded A B κ n).obj X)

/-- The projection `𝒦(U) → 𝒦(U)/𝒦²(U)` onto the sections of the first graded piece. -/
abbrev smallPolynomialAugmentationGradedOneπ
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X) →ₗ[(B : Type u)]
      smallPolynomialAugmentationGradedSections A B κ 1 X :=
  (Submodule.comap (smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X).subtype
    (smallPolynomialAugmentationIdealPowSubmodule A B κ 2 X)).mkQ

/-- **Multiplication as a map of sections `Sym^n_B(𝒦(U)) → 𝒦ⁿ(U)/𝒦ⁿ⁺¹(U)`.** -/
def smallPolynomialAugmentationSymPowToGraded (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    ↥(SymPow.symmetricPower n (B : Type u)
        ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)) →ₗ[(B : Type u)]
      smallPolynomialAugmentationGradedSections A B κ n X :=
  (Submodule.comap (smallPolynomialAugmentationIdealPowSubmodule A B κ n X).subtype
      (smallPolynomialAugmentationIdealPowSubmodule A B κ (n + 1) X)).mkQ ∘ₗ
    smallPolynomialAugmentationSymPowToPow A B κ n X

/-! ### The factorization through the symmetric powers of `𝒦/𝒦²` -/

/-- Taking `n`-th symmetric powers of the projection `𝒦(U) → 𝒦(U)/𝒦²(U)` is surjective. -/
lemma surjective_symMap_smallPolynomialAugmentationGradedOneπ (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Function.Surjective
      (SymPow.symMap n (smallPolynomialAugmentationGradedOneπ A B κ X)) :=
  SymPow.symMap_surjective n _ (Submodule.mkQ_surjective _)

/-- `𝒦²(U)`, as a `B`-submodule of `𝒦(U)`: the kernel of the projection onto `𝒦(U)/𝒦²(U)`. -/
abbrev smallPolynomialAugmentationIdealSqSubmodule
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Submodule (B : Type u) ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X) :=
  Submodule.comap (smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X).subtype
    (smallPolynomialAugmentationIdealPowSubmodule A B κ 2 X)

/-- The kernel of the projection `𝒦(U) → 𝒦(U)/𝒦²(U)` is `𝒦²(U)`. -/
lemma ker_smallPolynomialAugmentationGradedOneπ
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    LinearMap.ker (smallPolynomialAugmentationGradedOneπ A B κ X) =
      smallPolynomialAugmentationIdealSqSubmodule A B κ X :=
  Submodule.ker_mkQ _

/-- A product of `n + 1` elements of `𝒦(U)` one of which lies in `𝒦²(U)` lies in `𝒦ⁿ⁺²(U)`, so
multiplication kills the image of `𝒦²(U) ⊗ Sym^n_B(𝒦(U))`. This is the vanishing which lets
multiplication factor through the symmetric powers of `𝒦(U)/𝒦²(U)`. -/
lemma smallPolynomialAugmentationSymPowToGraded_symMulMap (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (t : ↥(smallPolynomialAugmentationIdealSqSubmodule A B κ X) ⊗[(B : Type u)]
      ↥(SymPow.symmetricPower n (B : Type u)
        ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X))) :
    smallPolynomialAugmentationSymPowToGraded A B κ (n + 1) X
        (SymPow.symMulMap n
          (smallPolynomialAugmentationIdealSqSubmodule A B κ X).subtype t) = 0 := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | tmul m y =>
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    have hm : ((m : ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)) :
        ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) ∈
        smallPolynomialAugmentationIdeal A B κ X ^ 2 := m.2
    have hy : smallPolynomialAugmentationSymProd A B κ X y ∈
        smallPolynomialAugmentationIdeal A B κ X ^ n :=
      smallPolynomialAugmentationSymProd_mem_pow A B κ X n y.2
    change smallPolynomialAugmentationSymProd A B κ X
        (SymmetricAlgebra.ι (B : Type u) _
          ((smallPolynomialAugmentationIdealSqSubmodule A B κ X).subtype m) *
          (y : SymmetricAlgebra (B : Type u) _)) ∈
      smallPolynomialAugmentationIdeal A B κ X ^ (n + 1 + 1)
    rw [map_mul, smallPolynomialAugmentationSymProd_ι,
      show n + 1 + 1 = 2 + n from by omega, pow_add]
    exact Ideal.mul_mem_mul hm hy

/-- Multiplication kills the kernel of `Sym^n_B(𝒦(U)) → Sym^n_B(𝒦(U)/𝒦²(U))`.

For `n ≥ 1` this is the right-exactness of `Sym^n`, `SymPow.symmetric_ker_le_im_alpha`, which
identifies that kernel with the image of `𝒦²(U) ⊗ Sym^{n-1}_B(𝒦(U))`. For `n = 0` the kernel is
zero: the degree-zero symmetric power of any module is the image of `B`, on which the map is the
identity, and `B` injects into the symmetric algebra because the zero linear map lifts to an
algebra map splitting the structure map. -/
lemma ker_symMap_le_ker_smallPolynomialAugmentationSymPowToGraded (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    LinearMap.ker (SymPow.symMap n (smallPolynomialAugmentationGradedOneπ A B κ X)) ≤
      LinearMap.ker (smallPolynomialAugmentationSymPowToGraded A B κ n X) := by
  cases n with
  | zero =>
    intro x hx
    have hx1 : (x : SymmetricAlgebra (B : Type u)
        ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)) ∈
        (1 : Submodule (B : Type u) (SymmetricAlgebra (B : Type u)
          ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X))) := by
      have hle : SymPow.symmetricPower 0 (B : Type u)
          ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X) ≤ 1 := le_of_eq (pow_zero _)
      exact hle x.2
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hx1
    have hzero : (algebraMap (B : Type u) (SymmetricAlgebra (B : Type u)
        (smallPolynomialAugmentationGradedSections A B κ 1 X))) r = 0 := by
      have h := Subtype.ext_iff.mp (LinearMap.mem_ker.mp hx)
      rw [SymPow.symMap_coe, ← hr, AlgHom.commutes] at h
      exact h
    have hr0 : r = 0 := by
      have h := congrArg (SymmetricAlgebra.lift
        (0 : smallPolynomialAugmentationGradedSections A B κ 1 X →ₗ[(B : Type u)]
          (B : Type u))) hzero
      simpa using h
    have hx0 : x = 0 := Subtype.ext (by rw [← hr, hr0, map_zero]; rfl)
    rw [hx0]
    exact Submodule.zero_mem _
  | succ k =>
    intro x hx
    obtain ⟨t, rfl⟩ := symmetric_ker_le_im_alpha
      (smallPolynomialAugmentationIdealSqSubmodule A B κ X).subtype
      (smallPolynomialAugmentationGradedOneπ A B κ X) (Submodule.mkQ_surjective _)
      (by rw [ker_smallPolynomialAugmentationGradedOneπ, Submodule.range_subtype]) k hx
    exact smallPolynomialAugmentationSymPowToGraded_symMulMap A B κ k X t

/-- **Multiplication from the symmetric power of `𝒦/𝒦²`**: the map of sections
`Sym^n_B(𝒦(U)/𝒦²(U)) → 𝒦ⁿ(U)/𝒦ⁿ⁺¹(U)` induced by multiplication in `Ō(U)`. -/
def smallPolynomialAugmentationSymMulApp (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    ↥(SymPow.symmetricPower n (B : Type u)
        (smallPolynomialAugmentationGradedSections A B κ 1 X)) →ₗ[(B : Type u)]
      smallPolynomialAugmentationGradedSections A B κ n X :=
  (Submodule.liftQ _ (smallPolynomialAugmentationSymPowToGraded A B κ n X)
      (ker_symMap_le_ker_smallPolynomialAugmentationSymPowToGraded A B κ n X)).comp
    (LinearMap.quotKerEquivOfSurjective _
      (surjective_symMap_smallPolynomialAugmentationGradedOneπ A B κ n X)).symm.toLinearMap

/-- **The characterising equation of `CommAlgCat.smallPolynomialAugmentationSymMulApp`**: it is
multiplication, read on the classes of `n` elements of `𝒦(U)`. -/
lemma smallPolynomialAugmentationSymMulApp_symMap (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (x : ↥(SymPow.symmetricPower n (B : Type u)
      ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X))) :
    smallPolynomialAugmentationSymMulApp A B κ n X
        (SymPow.symMap n (smallPolynomialAugmentationGradedOneπ A B κ X) x) =
      smallPolynomialAugmentationSymPowToGraded A B κ n X x := by
  have h : (LinearMap.quotKerEquivOfSurjective
        (SymPow.symMap n (smallPolynomialAugmentationGradedOneπ A B κ X))
        (surjective_symMap_smallPolynomialAugmentationGradedOneπ A B κ n X)).symm
        (SymPow.symMap n (smallPolynomialAugmentationGradedOneπ A B κ X) x) =
      Submodule.Quotient.mk x :=
    LinearMap.quotKerEquivOfSurjective_symm_apply _ _ x
  exact (congrArg (fun z => Submodule.liftQ (LinearMap.ker (SymPow.symMap n
      (smallPolynomialAugmentationGradedOneπ A B κ X)))
      (smallPolynomialAugmentationSymPowToGraded A B κ n X)
      (ker_symMap_le_ker_smallPolynomialAugmentationSymPowToGraded A B κ n X) z) h).trans
    (Submodule.liftQ_apply _ _ x)

/-! ### Naturality of multiplication -/

/-- The transition map of the filtration step `𝒦ⁿ`, read as a map between the submodules of
sections rather than between the values of the presheaf. -/
def smallPolynomialAugmentationIdealPowRestrict (n : ℕ)
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y) :
    ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n X) →ₗ[(B : Type u)]
      ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n Y) :=
  LinearMap.restrict ((smallPolynomialQuotientAlgebra A B κ).map f).hom.toLinearMap
    (fun x hx => smallPolynomialAugmentationIdealPow_map_mem A B κ n f x hx)

/-- The transition map of the presheaf `𝒦ⁿ` is the restriction of that of `Ō` to the submodules
of sections. -/
lemma hom_smallPolynomialAugmentationIdealPow_map (n : ℕ)
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y) :
    ((smallPolynomialAugmentationIdealPow A B κ n).map f).hom =
      smallPolynomialAugmentationIdealPowRestrict A B κ n f :=
  rfl

/-- **Multiplication is natural**: the transition maps of `Ō` are ring maps, so they commute with
the `n`-fold products of sections of `𝒦`. -/
lemma smallPolynomialAugmentationSymProd_naturality
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y) :
    (((smallPolynomialQuotientAlgebra A B κ).map f).hom).comp
        (smallPolynomialAugmentationSymProd A B κ X) =
      (smallPolynomialAugmentationSymProd A B κ Y).comp
        (SymPow.symAlgMap (smallPolynomialAugmentationIdealPowRestrict A B κ 1 f)) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun y => ?_)
  change ((smallPolynomialQuotientAlgebra A B κ).map f).hom
      (smallPolynomialAugmentationSymProd A B κ X (SymmetricAlgebra.ι (B : Type u) _ y)) =
    smallPolynomialAugmentationSymProd A B κ Y
      (SymPow.symAlgMap (smallPolynomialAugmentationIdealPowRestrict A B κ 1 f)
        (SymmetricAlgebra.ι (B : Type u) _ y))
  rw [SymPow.symAlgMap_ι, smallPolynomialAugmentationSymProd_ι,
    smallPolynomialAugmentationSymProd_ι]
  rfl

/-- Naturality of multiplication, read on the sections of `𝒦ⁿ`. -/
lemma smallPolynomialAugmentationSymPowToPow_naturality (n : ℕ)
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y)
    (x : ↥(SymPow.symmetricPower n (B : Type u)
      ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X))) :
    smallPolynomialAugmentationSymPowToPow A B κ n Y
        (SymPow.symMap n (smallPolynomialAugmentationIdealPowRestrict A B κ 1 f) x) =
      smallPolynomialAugmentationIdealPowRestrict A B κ n f
        (smallPolynomialAugmentationSymPowToPow A B κ n X x) := by
  refine Subtype.ext ?_
  change smallPolynomialAugmentationSymProd A B κ Y
      (SymPow.symAlgMap (smallPolynomialAugmentationIdealPowRestrict A B κ 1 f)
        (x : SymmetricAlgebra (B : Type u) _)) =
    ((smallPolynomialQuotientAlgebra A B κ).map f).hom
      (smallPolynomialAugmentationSymProd A B κ X (x : SymmetricAlgebra (B : Type u) _))
  exact (DFunLike.congr_fun (smallPolynomialAugmentationSymProd_naturality A B κ f)
    (x : SymmetricAlgebra (B : Type u) _)).symm

/-- Naturality of multiplication, read on the sections of the graded piece `𝒦ⁿ/𝒦ⁿ⁺¹`. -/
lemma smallPolynomialAugmentationSymPowToGraded_naturality (n : ℕ)
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y)
    (x : ↥(SymPow.symmetricPower n (B : Type u)
      ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X))) :
    smallPolynomialAugmentationSymPowToGraded A B κ n Y
        (SymPow.symMap n (smallPolynomialAugmentationIdealPowRestrict A B κ 1 f) x) =
      ((smallPolynomialAugmentationGraded A B κ n).map f).hom
        (smallPolynomialAugmentationSymPowToGraded A B κ n X x) :=
  congrArg (Submodule.Quotient.mk (p := Submodule.comap
      (smallPolynomialAugmentationIdealPowSubmodule A B κ n Y).subtype
      (smallPolynomialAugmentationIdealPowSubmodule A B κ (n + 1) Y)))
    (smallPolynomialAugmentationSymPowToPow_naturality A B κ n f x)

/-- The projection `𝒦 ⟶ 𝒦/𝒦²` is natural, read on sections. -/
lemma smallPolynomialAugmentationGradedOneπ_naturality
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y) :
    (((smallPolynomialAugmentationGraded A B κ 1).map f).hom).comp
        (smallPolynomialAugmentationGradedOneπ A B κ X) =
      (smallPolynomialAugmentationGradedOneπ A B κ Y).comp
        (smallPolynomialAugmentationIdealPowRestrict A B κ 1 f) :=
  LinearMap.ext fun _ => rfl

/-- **Multiplication from the symmetric power of `𝒦/𝒦²` is natural.** Every section of
`Sym^n_B(𝒦(U)/𝒦²(U))` is the image of one of `Sym^n_B(𝒦(U))`, where the statement is the
naturality of multiplication, `CommAlgCat.smallPolynomialAugmentationSymPowToGraded_naturality`. -/
lemma smallPolynomialAugmentationSymMulApp_naturality (n : ℕ)
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y)
    (z : ↥(SymPow.symmetricPower n (B : Type u)
      (smallPolynomialAugmentationGradedSections A B κ 1 X))) :
    smallPolynomialAugmentationSymMulApp A B κ n Y
        (SymPow.symMap n ((smallPolynomialAugmentationGraded A B κ 1).map f).hom z) =
      ((smallPolynomialAugmentationGraded A B κ n).map f).hom
        (smallPolynomialAugmentationSymMulApp A B κ n X z) := by
  obtain ⟨x, rfl⟩ := surjective_symMap_smallPolynomialAugmentationGradedOneπ A B κ n X z
  rw [Stacks.ChaoticSite.symMap_comp_apply, smallPolynomialAugmentationGradedOneπ_naturality,
    ← Stacks.ChaoticSite.symMap_comp_apply, smallPolynomialAugmentationSymMulApp_symMap,
    smallPolynomialAugmentationSymMulApp_symMap]
  exact smallPolynomialAugmentationSymPowToGraded_naturality A B κ n f x

/-- **Multiplication in `Ō`, as a map of presheaves `Sym^n_{B̲}(𝒦/𝒦²) ⟶ 𝒦ⁿ/𝒦ⁿ⁺¹`.** -/
def smallPolynomialAugmentationSymMul (n : ℕ) :
    Stacks.ChaoticSite.symmetricPowerDiagram (smallBoundedPolynomialSite A B κ) (B : Type u)
        (smallPolynomialAugmentationGraded A B κ 1) n ⟶
      smallPolynomialAugmentationGraded A B κ n where
  app X := ModuleCat.ofHom (smallPolynomialAugmentationSymMulApp A B κ n X)
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun z =>
    smallPolynomialAugmentationSymMulApp_naturality A B κ n f z)

/-! ### The conormal map `Ω ⟶ 𝒦/𝒦²` -/

/-- **The conormal map `P → Ō(U)`**, `p ↦ 1 ⊗ p - α(p) ⊗ 1`: the conormal map of the augmented
algebra naming the object, read as a map into the sections of `Ō`. -/
def smallPolynomialAugmentationDiff (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u) :=
  Stacks.augDiff (smallSiteAug A B κ X) p

/-- The conormal map `P → Ō(U)` is additive. -/
lemma smallPolynomialAugmentationDiff_add (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p q : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    smallPolynomialAugmentationDiff A B κ X (p + q) =
      smallPolynomialAugmentationDiff A B κ X p +
        smallPolynomialAugmentationDiff A B κ X q :=
  Stacks.augDiff_add (smallSiteAug A B κ X) p q

/-- The conormal map `P → Ō(U)` is `A`-linear, `A` acting on `Ō(U)` through `B`. -/
lemma smallPolynomialAugmentationDiff_smul (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) (a : A)
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    smallPolynomialAugmentationDiff A B κ X (a • p) =
      (algebraMap A (B : Type u) a) • smallPolynomialAugmentationDiff A B κ X p :=
  Stacks.augDiff_smul (smallSiteAug A B κ X) a p

/-- **The Leibniz defect of the conormal map** over an object is the product of two of its
values, which is why the conormal class map becomes a derivation modulo `𝒦²`. -/
lemma smallPolynomialAugmentationDiff_mul (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p q : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    smallPolynomialAugmentationDiff A B κ X (p * q) =
      smallSiteAug A B κ X p • smallPolynomialAugmentationDiff A B κ X q +
        smallSiteAug A B κ X q • smallPolynomialAugmentationDiff A B κ X p +
        smallPolynomialAugmentationDiff A B κ X p *
          smallPolynomialAugmentationDiff A B κ X q :=
  Stacks.augDiff_mul (smallSiteAug A B κ X) p q

/-- The conormal map lands in the augmentation ideal. -/
lemma smallPolynomialAugmentationDiff_mem (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    smallPolynomialAugmentationDiff A B κ X p ∈
      smallPolynomialAugmentationIdeal A B κ X :=
  Stacks.augDiff_mem_ker (smallSiteAug A B κ X) (smallPolynomialQuotientAug A B κ X)
    (smallPolynomialQuotientAug_tmul A B κ X) p

/-- The conormal map is natural: the transition maps of `Ō` are ring maps over the
augmentations. -/
lemma smallPolynomialAugmentationDiff_naturality
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y)
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    ((smallPolynomialQuotientAlgebra A B κ).map f).hom
        (smallPolynomialAugmentationDiff A B κ X p) =
      smallPolynomialAugmentationDiff A B κ Y
        (((smallSiteToOver A B κ).map f).left.hom p) :=
  Stacks.augDiff_map (smallSiteAug A B κ X) (smallSiteAug A B κ Y)
    (((smallSiteToOver A B κ).map f).left.hom)
    (((smallPolynomialQuotientAlgebra A B κ).map f).hom) (fun _ _ => rfl)
    (fun q => smallSiteAug_naturality A B κ f q) p

/-- The conormal map, read as a map into the sections of `𝒦`. -/
def smallPolynomialAugmentationDiffSection (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X) :=
  ⟨smallPolynomialAugmentationDiff A B κ X p, by
    change smallPolynomialAugmentationDiff A B κ X p ∈
      smallPolynomialAugmentationIdeal A B κ X ^ 1
    rw [pow_one]
    exact smallPolynomialAugmentationDiff_mem A B κ X p⟩

/-- The conormal section of `𝒦`, read in `Ō(U)`, is the conormal map. -/
@[simp]
lemma coe_smallPolynomialAugmentationDiffSection
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    (smallPolynomialAugmentationDiffSection A B κ X p :
        ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) =
      smallPolynomialAugmentationDiff A B κ X p :=
  rfl

/-- The conormal map into the sections of `𝒦` is additive. -/
lemma smallPolynomialAugmentationDiffSection_add
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p q : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    smallPolynomialAugmentationDiffSection A B κ X (p + q) =
      smallPolynomialAugmentationDiffSection A B κ X p +
        smallPolynomialAugmentationDiffSection A B κ X q :=
  Subtype.ext (by
    rw [AddMemClass.coe_add, coe_smallPolynomialAugmentationDiffSection,
      coe_smallPolynomialAugmentationDiffSection,
      coe_smallPolynomialAugmentationDiffSection,
      smallPolynomialAugmentationDiff_add])

/-- The conormal map into the sections of `𝒦` is `A`-linear, `A` acting through `B`. -/
lemma smallPolynomialAugmentationDiffSection_smul
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) (a : A)
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    smallPolynomialAugmentationDiffSection A B κ X (a • p) =
      (algebraMap A (B : Type u) a) • smallPolynomialAugmentationDiffSection A B κ X p :=
  Subtype.ext (by
    rw [SetLike.val_smul, coe_smallPolynomialAugmentationDiffSection,
      coe_smallPolynomialAugmentationDiffSection, smallPolynomialAugmentationDiff_smul])

/-- The coercion of the Leibniz defect of the conormal class map to a section of `Ō`. -/
lemma coe_smallPolynomialConormalDefect (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p q : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    ((smallPolynomialAugmentationDiffSection A B κ X (p * q) -
        (smallSiteAug A B κ X p • smallPolynomialAugmentationDiffSection A B κ X q +
          smallSiteAug A B κ X q • smallPolynomialAugmentationDiffSection A B κ X p) :
        ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)) :
        ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) =
      smallPolynomialAugmentationDiff A B κ X p *
        smallPolynomialAugmentationDiff A B κ X q := by
  rw [AddSubgroupClass.coe_sub, AddMemClass.coe_add, SetLike.val_smul, SetLike.val_smul,
    coe_smallPolynomialAugmentationDiffSection, coe_smallPolynomialAugmentationDiffSection,
    coe_smallPolynomialAugmentationDiffSection, smallPolynomialAugmentationDiff_mul,
    add_sub_cancel_left]

/-- **The conormal class map modulo `𝒦²` satisfies the Leibniz rule**: the defect of the conormal
map is a product of two elements of `𝒦(U)`, hence lies in `𝒦²(U)`. -/
lemma smallPolynomialConormalClass_mul (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p q : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    smallPolynomialAugmentationGradedOneπ A B κ X
        (smallPolynomialAugmentationDiffSection A B κ X (p * q)) =
      smallSiteAug A B κ X p • smallPolynomialAugmentationGradedOneπ A B κ X
          (smallPolynomialAugmentationDiffSection A B κ X q) +
        smallSiteAug A B κ X q • smallPolynomialAugmentationGradedOneπ A B κ X
          (smallPolynomialAugmentationDiffSection A B κ X p) := by
  rw [← map_smul, ← map_smul, ← map_add]
  refine (Submodule.Quotient.eq _).2 (Submodule.mem_comap.2 ?_)
  rw [Submodule.subtype_apply, coe_smallPolynomialConormalDefect]
  change smallPolynomialAugmentationDiff A B κ X p *
      smallPolynomialAugmentationDiff A B κ X q ∈
    smallPolynomialAugmentationIdeal A B κ X ^ 2
  rw [pow_two]
  exact Ideal.mul_mem_mul (smallPolynomialAugmentationDiff_mem A B κ X p)
    (smallPolynomialAugmentationDiff_mem A B κ X q)

/-- The conormal map into the sections of `𝒦` is natural: the transition map of `𝒦` carries the
conormal section of `p` to that of its image. -/
lemma smallPolynomialAugmentationDiffSection_naturality
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y)
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    smallPolynomialAugmentationIdealPowRestrict A B κ 1 f
        (smallPolynomialAugmentationDiffSection A B κ X p) =
      smallPolynomialAugmentationDiffSection A B κ Y
        (((smallSiteToOver A B κ).map f).left.hom p) :=
  Subtype.ext (smallPolynomialAugmentationDiff_naturality A B κ f p)

section Conormal

/-- The augmentation makes the sections of `𝒦/𝒦²` over an object a module over the polynomial
algebra naming that object: the module structure restricted along `α : P → B`. -/
local instance moduleSiteOfAugmentation (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Module (((smallSiteToOver A B κ).obj X).left : Type u)
      (smallPolynomialAugmentationGradedSections A B κ 1 X) :=
  Module.compHom _ (augmentationRingHom ((smallSiteToOver A B κ).obj X))

/-- The `A`-module structure on the sections of `𝒦/𝒦²` obtained from the previous one by
restriction along `A → P`. -/
local instance moduleBaseOfAugmentation (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Module A (smallPolynomialAugmentationGradedSections A B κ 1 X) :=
  Module.compHom _ (algebraMap A (((smallSiteToOver A B κ).obj X).left : Type u))

/-- The actions of `A` and of the polynomial algebra on the sections of `𝒦/𝒦²` form a scalar
tower. -/
local instance isScalarTowerOfAugmentation (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    IsScalarTower A (((smallSiteToOver A B κ).obj X).left : Type u)
      (smallPolynomialAugmentationGradedSections A B κ 1 X) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The conormal class map `p ↦ [1 ⊗ p - α(p)]`, as an `A`-linear map `P → 𝒦(U)/𝒦²(U)`. -/
def smallPolynomialConormalLinearMap (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    (((smallSiteToOver A B κ).obj X).left : Type u) →ₗ[A]
      smallPolynomialAugmentationGradedSections A B κ 1 X where
  toFun p := smallPolynomialAugmentationGradedOneπ A B κ X
    (smallPolynomialAugmentationDiffSection A B κ X p)
  map_add' p q := by
    rw [smallPolynomialAugmentationDiffSection_add, map_add]
  map_smul' a p := by
    change smallPolynomialAugmentationGradedOneπ A B κ X
        (smallPolynomialAugmentationDiffSection A B κ X (a • p)) =
      (smallSiteAug A B κ X
          (algebraMap A (((smallSiteToOver A B κ).obj X).left : Type u) a)) •
        smallPolynomialAugmentationGradedOneπ A B κ X
          (smallPolynomialAugmentationDiffSection A B κ X p)
    rw [AlgHom.commutes, smallPolynomialAugmentationDiffSection_smul, map_smul]

/-- **The conormal derivation** `p ↦ [1 ⊗ p - α(p)]` of `P` into `𝒦(U)/𝒦²(U)`, the latter read as
a `P`-module through the augmentation. The Leibniz rule holds because its defect is a product of
two elements of `𝒦(U)`, hence lies in `𝒦²(U)`
(`CommAlgCat.smallPolynomialConormalClass_mul`). -/
def smallPolynomialConormalDerivation (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Derivation A (((smallSiteToOver A B κ).obj X).left : Type u)
      (smallPolynomialAugmentationGradedSections A B κ 1 X) :=
  Derivation.mk' (smallPolynomialConormalLinearMap A B κ X)
    fun p q => smallPolynomialConormalClass_mul A B κ X p q

/-- The `P`-linear map `Ω[P⁄A] → 𝒦(U)/𝒦²(U)` the conormal derivation lifts to, which is the
adjoint of the conormal map `Ω(U) → 𝒦(U)/𝒦²(U)`. -/
def smallPolynomialConormalAdjoint (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    ModuleCat.of (((smallSiteToOver A B κ).obj X).left : Type u)
        (KaehlerDifferential A (((smallSiteToOver A B κ).obj X).left : Type u)) ⟶
      (ModuleCat.restrictScalars
          (augmentationRingHom ((smallSiteToOver A B κ).obj X))).obj
        ((smallPolynomialAugmentationGraded A B κ 1).obj X) :=
  ModuleCat.ofHom
    (Derivation.liftKaehlerDifferential (smallPolynomialConormalDerivation A B κ X))

/-- The adjoint of the conormal map sends `d p` to the class of `1 ⊗ p - α(p)`. -/
lemma smallPolynomialConormalAdjoint_D (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    (smallPolynomialConormalAdjoint A B κ X).hom
        (KaehlerDifferential.D A (((smallSiteToOver A B κ).obj X).left : Type u) p) =
      smallPolynomialAugmentationGradedOneπ A B κ X
        (smallPolynomialAugmentationDiffSection A B κ X p) :=
  Derivation.liftKaehlerDifferential_comp_D (smallPolynomialConormalDerivation A B κ X) p

end Conormal

/-- **The pure differential `1 ⊗ d p`** as a section of `Ω` over an object of the site. -/
def smallPolynomialCotangentMk (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    ((smallPolynomialCotangentModulePresheaf A B κ).obj X : Type u) :=
  overDifferentialsMk ((smallSiteToOver A B κ).obj X) p

/-- Two maps out of `Ω(U)` agreeing on the pure differentials are equal. -/
lemma smallPolynomialCotangent_hom_ext {X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)}
    {N : ModuleCat.{u} (B : Type u)}
    (a b : (smallPolynomialCotangentModulePresheaf A B κ).obj X ⟶ N)
    (h : ∀ p, a (smallPolynomialCotangentMk A B κ X p) =
      b (smallPolynomialCotangentMk A B κ X p)) : a = b :=
  overDifferentials_hom_ext a b h

/-- The transition maps of `Ω` on the pure differentials: `1 ⊗ d p ↦ 1 ⊗ d (g p)`. -/
lemma smallPolynomialCotangentModulePresheaf_map_mk
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y)
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    (smallPolynomialCotangentModulePresheaf A B κ).map f
        (smallPolynomialCotangentMk A B κ X p) =
      smallPolynomialCotangentMk A B κ Y (((smallSiteToOver A B κ).map f).left.hom p) :=
  overDifferentialsPush_mk _
    (augmentationRingHom_comp ((smallSiteToOver A B κ).map f)) p

/-- **The conormal map `Ω(U) → 𝒦(U)/𝒦²(U)`** over an object of the site: the `B`-linear map
sending the pure differential `1 ⊗ d p` to the class of `1 ⊗ p - α(p)`. -/
def smallPolynomialCotangentToGradedApp (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    (smallPolynomialCotangentModulePresheaf A B κ).obj X ⟶
      (smallPolynomialAugmentationGraded A B κ 1).obj X :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (augmentationRingHom ((smallSiteToOver A B κ).obj X))
    (smallPolynomialConormalAdjoint A B κ X)

/-- **The characterising equation of the conormal map**: it sends the pure differential
`1 ⊗ d p` to the class of `1 ⊗ p - α(p)`. -/
lemma smallPolynomialCotangentToGradedApp_mk
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (p : (((smallSiteToOver A B κ).obj X).left : Type u)) :
    smallPolynomialCotangentToGradedApp A B κ X (smallPolynomialCotangentMk A B κ X p) =
      smallPolynomialAugmentationGradedOneπ A B κ X
        (smallPolynomialAugmentationDiffSection A B κ X p) := by
  refine Eq.trans (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
    (augmentationRingHom ((smallSiteToOver A B κ).obj X))
    (smallPolynomialConormalAdjoint A B κ X) (1 : (B : Type u))
    (KaehlerDifferential.D A (((smallSiteToOver A B κ).obj X).left : Type u) p)) ?_
  rw [one_smul]
  exact smallPolynomialConormalAdjoint_D A B κ X p

/-- **The conormal map is natural.** Both sides send the pure differential `1 ⊗ d p` to the class
of `1 ⊗ g(p) - α(g(p))`, by `CommAlgCat.smallPolynomialAugmentationDiff_naturality`, and a map
out of `Ω(U)` is determined by its values on the pure differentials. -/
lemma smallPolynomialCotangentToGradedApp_naturality
    {X Y : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)} (f : X ⟶ Y) :
    (smallPolynomialCotangentModulePresheaf A B κ).map f ≫
        smallPolynomialCotangentToGradedApp A B κ Y =
      smallPolynomialCotangentToGradedApp A B κ X ≫
        (smallPolynomialAugmentationGraded A B κ 1).map f := by
  refine smallPolynomialCotangent_hom_ext A B κ _ _ fun p => ?_
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    smallPolynomialCotangentModulePresheaf_map_mk,
    smallPolynomialCotangentToGradedApp_mk, smallPolynomialCotangentToGradedApp_mk,
    ← smallPolynomialAugmentationDiffSection_naturality]
  exact (DFunLike.congr_fun (smallPolynomialAugmentationGradedOneπ_naturality A B κ f)
    (smallPolynomialAugmentationDiffSection A B κ X p)).symm

/-- **The conormal map `Ω ⟶ 𝒦/𝒦²`** of presheaves of `B`-modules on the small model of the
polynomial site. -/
def smallPolynomialCotangentToGraded :
    smallPolynomialCotangentModulePresheaf A B κ ⟶
      smallPolynomialAugmentationGraded A B κ 1 where
  app X := smallPolynomialCotangentToGradedApp A B κ X
  naturality _ _ f := smallPolynomialCotangentToGradedApp_naturality A B κ f

/-! ### The sections in coordinates, and bijectivity of the conormal map -/

/-- The `s`-th variable of the polynomial algebra naming an object of the small model. -/
def smallSiteVar (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) (s : ↥(X.unop.unop.1)) :
    (((smallSiteToOver A B κ).obj X).left : Type u) :=
  MvPolynomial.X s

/-- **The conormal map at a variable, in coordinates**: under `Ō(U) = B[S]` the section
`1 ⊗ X s - α(X s)` is the standard generator `X s - C (g s)` of the augmentation ideal. -/
lemma smallPolynomialQuotientAlgEquiv_smallPolynomialAugmentationDiff_var
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) (s : ↥(X.unop.unop.1)) :
    smallPolynomialQuotientAlgEquiv A B κ X
        (smallPolynomialAugmentationDiff A B κ X (smallSiteVar A B κ X s)) =
      MvPolynomial.X s - MvPolynomial.C (smallSitePoint A B κ X s) :=
  Stacks.algebraTensorAlgEquiv_augDiff_X (smallSitePoint A B κ X) s

/-- The identification of the sections of `𝒦ⁿ` with the `n`-th power of the augmentation ideal
of `B[S]` is the restriction of the identification `Ō(U) = B[S]`. -/
lemma coe_smallPolynomialAugmentationIdealPowLinearEquiv (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (x : ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n X)) :
    (smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X x :
        MvPolynomial ↥(X.unop.unop.1) (B : Type u)) =
      smallPolynomialQuotientAlgEquiv A B κ X
        (x : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) :=
  rfl

/-- The identification `Ō(U) = B[S]` carries the section of `𝒦ⁿ` corresponding to an element of
the `n`-th power of the augmentation ideal back to that element. -/
lemma smallPolynomialQuotientAlgEquiv_coe_symm (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (z : ↥(Submodule.restrictScalars (B : Type u)
      (MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n))) :
    smallPolynomialQuotientAlgEquiv A B κ X
        (((smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X).symm z :
          ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u))) =
      (z : MvPolynomial ↥(X.unop.unop.1) (B : Type u)) := by
  rw [← coe_smallPolynomialAugmentationIdealPowLinearEquiv, LinearEquiv.apply_symm_apply]

/-- The identification of the sections of `𝒦ⁿ` with the `n`-th power of the augmentation ideal of
`B[S]` carries the sections of `𝒦ⁿ⁺¹` onto the next step of that filtration. -/
lemma map_smallPolynomialAugmentationIdealPowLinearEquiv_step (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Submodule.map (smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X).toLinearMap
        (Submodule.comap (smallPolynomialAugmentationIdealPowSubmodule A B κ n X).subtype
          (smallPolynomialAugmentationIdealPowSubmodule A B κ (n + 1) X)) =
      MvPolynomial.augmentationFiltrationStep (smallSitePoint A B κ X) n := by
  refine le_antisymm ?_ fun z hz => ?_
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_comap.2 ?_
    rw [Submodule.subtype_apply]
    change (smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X x :
        MvPolynomial ↥(X.unop.unop.1) (B : Type u)) ∈
      MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ (n + 1)
    rw [coe_smallPolynomialAugmentationIdealPowLinearEquiv]
    have hx' : (x : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) ∈
        smallPolynomialAugmentationIdeal A B κ X ^ (n + 1) := hx
    rw [smallPolynomialAugmentationIdeal_pow_eq_comap] at hx'
    exact hx'
  · refine ⟨(smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X).symm z, ?_,
      (smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X).apply_symm_apply z⟩
    refine Submodule.mem_comap.2 ?_
    rw [Submodule.subtype_apply]
    change ((smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X).symm z :
        ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) ∈
      smallPolynomialAugmentationIdeal A B κ X ^ (n + 1)
    rw [smallPolynomialAugmentationIdeal_pow_eq_comap, Ideal.mem_comap,
      smallPolynomialQuotientAlgEquiv_coe_symm]
    exact hz

/-- **The sections of `𝒦ⁿ/𝒦ⁿ⁺¹` in coordinates**: the `n`-th graded piece of the augmentation
filtration of the polynomial ring `B[S]` at the point naming the object. -/
def smallPolynomialAugmentationGradedSectionsEquiv (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    smallPolynomialAugmentationGradedSections A B κ n X ≃ₗ[(B : Type u)]
      MvPolynomial.augmentationGraded (smallSitePoint A B κ X) n :=
  Submodule.Quotient.equiv _ _ (smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X)
    (map_smallPolynomialAugmentationIdealPowLinearEquiv_step A B κ n X)

/-- In coordinates, the class of a section of `𝒦ⁿ` is the class of the corresponding element of
the `n`-th power of the augmentation ideal of `B[S]`. -/
lemma smallPolynomialAugmentationGradedSectionsEquiv_mk (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (x : ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n X)) :
    smallPolynomialAugmentationGradedSectionsEquiv A B κ n X (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X x) :=
  rfl

/-- **The sections of `𝒦/𝒦²` are free on the variables**: the conormal module of the polynomial
ring `B[S]` at the point naming the object. -/
def smallPolynomialAugmentationGradedOneSectionsEquiv
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    smallPolynomialAugmentationGradedSections A B κ 1 X ≃ₗ[(B : Type u)]
      (↥(X.unop.unop.1) →₀ (B : Type u)) :=
  (smallPolynomialAugmentationGradedSectionsEquiv A B κ 1 X).trans
    (MvPolynomial.augmentationGradedOneEquiv (smallSitePoint A B κ X))

/-- The class of the conormal section at a variable corresponds to the basis vector of that
variable. -/
lemma smallPolynomialAugmentationGradedOneSectionsEquiv_diff_var
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) (s : ↥(X.unop.unop.1)) :
    smallPolynomialAugmentationGradedOneSectionsEquiv A B κ X
        (smallPolynomialAugmentationGradedOneπ A B κ X
          (smallPolynomialAugmentationDiffSection A B κ X (smallSiteVar A B κ X s))) =
      Finsupp.single s 1 := by
  have hgen : (MvPolynomial.X s - MvPolynomial.C (smallSitePoint A B κ X s) :
      MvPolynomial ↥(X.unop.unop.1) (B : Type u)) ∈
      MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ 1 :=
    (pow_one (MvPolynomial.augmentationIdeal (smallSitePoint A B κ X))).ge
      ((MvPolynomial.mem_augmentationIdeal (smallSitePoint A B κ X)).2 (by simp))
  have hstep : smallPolynomialAugmentationIdealPowLinearEquiv A B κ 1 X
      (smallPolynomialAugmentationDiffSection A B κ X (smallSiteVar A B κ X s)) =
      ⟨MvPolynomial.X s - MvPolynomial.C (smallSitePoint A B κ X s), hgen⟩ :=
    Subtype.ext ((coe_smallPolynomialAugmentationIdealPowLinearEquiv A B κ 1 X
        (smallPolynomialAugmentationDiffSection A B κ X (smallSiteVar A B κ X s))).trans
      (smallPolynomialQuotientAlgEquiv_smallPolynomialAugmentationDiff_var A B κ X s))
  exact (congrArg (fun z => MvPolynomial.augmentationGradedOneEquiv
        (smallSitePoint A B κ X) z) (congrArg Submodule.Quotient.mk hstep)).trans
    (MvPolynomial.augmentationGradedOneEquiv_mk (smallSitePoint A B κ X) s hgen)

/-- The basis of `𝒦(U)/𝒦²(U)` given by the classes of the conormal sections of the variables. -/
def smallPolynomialAugmentationGradedOneBasis
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Module.Basis ↥(X.unop.unop.1) (B : Type u)
      (smallPolynomialAugmentationGradedSections A B κ 1 X) :=
  Finsupp.basisSingleOne.map (smallPolynomialAugmentationGradedOneSectionsEquiv A B κ X).symm

/-- The basis vector of `𝒦(U)/𝒦²(U)` at a variable is the class of its conormal section. -/
lemma smallPolynomialAugmentationGradedOneBasis_apply
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) (s : ↥(X.unop.unop.1)) :
    smallPolynomialAugmentationGradedOneBasis A B κ X s =
      smallPolynomialAugmentationGradedOneπ A B κ X
        (smallPolynomialAugmentationDiffSection A B κ X (smallSiteVar A B κ X s)) :=
  Stacks.basisSingleOne_map_symm_apply
    (smallPolynomialAugmentationGradedOneSectionsEquiv A B κ X) s _
    (smallPolynomialAugmentationGradedOneSectionsEquiv_diff_var A B κ X s)

/-- The basis of `Ω(U) = B ⊗_P Ω[P⁄A]` given by the differentials of the variables. -/
def smallPolynomialCotangentBasis (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Module.Basis ↥(X.unop.unop.1) (B : Type u)
      ↥((smallPolynomialCotangentModulePresheaf A B κ).obj X) := by
  letI : Algebra (((smallSiteToOver A B κ).obj X).left : Type u) (B : Type u) :=
    (augmentationRingHom ((smallSiteToOver A B κ).obj X)).toAlgebra
  exact (KaehlerDifferential.basisOfMvPolynomialAlgEquiv (A := A)
    (AlgEquiv.refl : (((smallSiteToOver A B κ).obj X).left : Type u) ≃ₐ[A]
      MvPolynomial ↥(X.unop.unop.1) A)).baseChange (B : Type u)

/-- The basis vector of `Ω(U)` at a variable is the pure differential `1 ⊗ d (X s)`. -/
lemma smallPolynomialCotangentBasis_apply (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (s : ↥(X.unop.unop.1)) :
    smallPolynomialCotangentBasis A B κ X s =
      smallPolynomialCotangentMk A B κ X (smallSiteVar A B κ X s) := by
  let : Algebra (((smallSiteToOver A B κ).obj X).left : Type u) (B : Type u) :=
    (augmentationRingHom ((smallSiteToOver A B κ).obj X)).toAlgebra
  exact Stacks.baseChange_basisOfMvPolynomialAlgEquiv_apply (B : Type u)
    (AlgEquiv.refl : (((smallSiteToOver A B κ).obj X).left : Type u) ≃ₐ[A]
      MvPolynomial ↥(X.unop.unop.1) A) s

/-- **The conormal map is bijective over every object.** It carries the basis of `Ω(U)` given by
the differentials of the variables to the basis of `𝒦(U)/𝒦²(U)` given by the classes of the
generators `X s - g(s)` of the augmentation ideal. -/
lemma bijective_smallPolynomialCotangentToGradedApp
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Function.Bijective (smallPolynomialCotangentToGradedApp A B κ X).hom :=
  Stacks.bijective_of_basis_eq (smallPolynomialCotangentBasis A B κ X)
    (smallPolynomialAugmentationGradedOneBasis A B κ X)
    (smallPolynomialCotangentToGradedApp A B κ X).hom fun s =>
      ((congrArg (fun z => (smallPolynomialCotangentToGradedApp A B κ X).hom z)
            (smallPolynomialCotangentBasis_apply A B κ X s)).trans
          (smallPolynomialCotangentToGradedApp_mk A B κ X (smallSiteVar A B κ X s))).trans
        (smallPolynomialAugmentationGradedOneBasis_apply A B κ X s).symm

/-- **`Ω ≅ 𝒦/𝒦²`.** The conormal map `CommAlgCat.smallPolynomialCotangentToGraded` is an
isomorphism of presheaves of `B`-modules: it is natural, being the canonical conormal map, and
bijective over each object, both sides being free on the variables of that object. -/
def smallPolynomialCotangentGradedIso :
    smallPolynomialCotangentModulePresheaf A B κ ≅
      smallPolynomialAugmentationGraded A B κ 1 :=
  NatIso.ofComponents
    (fun X => (LinearEquiv.ofBijective _
      (bijective_smallPolynomialCotangentToGradedApp A B κ X)).toModuleIso)
    (fun f => smallPolynomialCotangentToGradedApp_naturality A B κ f)

/-- The component of the isomorphism `Ω ≅ 𝒦/𝒦²` at an object is the conormal map. -/
@[simp]
lemma smallPolynomialCotangentGradedIso_hom_app
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    (smallPolynomialCotangentGradedIso A B κ).hom.app X =
      smallPolynomialCotangentToGradedApp A B κ X :=
  rfl

/-! ### Multiplication is an isomorphism -/

/-- The map `Sym^n_B(𝒦(U)) → 𝒦ⁿ(U)` sends a product of `n` degree-one generators to the
product of the corresponding elements of `𝒦(U)`. -/
@[simp]
lemma coe_smallPolynomialAugmentationSymPowToPow_prod_ι (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (y : Fin n → ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)) :
    (smallPolynomialAugmentationSymPowToPow A B κ n X
        ⟨∏ i, SymmetricAlgebra.ι (B : Type u) _ (y i),
          MvPolynomial.prod_ι_mem_symmetricPower n y⟩ :
        ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) =
      ∏ i, (y i : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) := by
  rw [coe_smallPolynomialAugmentationSymPowToPow]
  change smallPolynomialAugmentationSymProd A B κ X
      (∏ i, SymmetricAlgebra.ι (B : Type u) _ (y i)) = _
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => smallPolynomialAugmentationSymProd_ι A B κ X (y i)

/-- **Multiplication on a product of `n` classes** is the class of the product of `n` lifts. -/
lemma smallPolynomialAugmentationSymMulApp_prod_ι (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (y : Fin n → ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)) :
    smallPolynomialAugmentationSymMulApp A B κ n X
        ⟨∏ i, SymmetricAlgebra.ι (B : Type u)
            (smallPolynomialAugmentationGradedSections A B κ 1 X)
            (smallPolynomialAugmentationGradedOneπ A B κ X (y i)),
          MvPolynomial.prod_ι_mem_symmetricPower n fun i =>
            smallPolynomialAugmentationGradedOneπ A B κ X (y i)⟩ =
      smallPolynomialAugmentationSymPowToGraded A B κ n X
        ⟨∏ i, SymmetricAlgebra.ι (B : Type u) _ (y i),
          MvPolynomial.prod_ι_mem_symmetricPower n y⟩ := by
  have hstep : (⟨∏ i, SymmetricAlgebra.ι (B : Type u)
        (smallPolynomialAugmentationGradedSections A B κ 1 X)
        (smallPolynomialAugmentationGradedOneπ A B κ X (y i)),
      MvPolynomial.prod_ι_mem_symmetricPower n fun i =>
        smallPolynomialAugmentationGradedOneπ A B κ X (y i)⟩ :
      ↥(SymPow.symmetricPower n (B : Type u)
        (smallPolynomialAugmentationGradedSections A B κ 1 X))) =
      SymPow.symMap n (smallPolynomialAugmentationGradedOneπ A B κ X)
        ⟨∏ i, SymmetricAlgebra.ι (B : Type u) _ (y i),
          MvPolynomial.prod_ι_mem_symmetricPower n y⟩ := by
    refine Subtype.ext ?_
    rw [SymPow.symMap_coe]
    change ∏ i, SymmetricAlgebra.ι (B : Type u)
          (smallPolynomialAugmentationGradedSections A B κ 1 X)
          (smallPolynomialAugmentationGradedOneπ A B κ X (y i)) =
        SymPow.symAlgMap (smallPolynomialAugmentationGradedOneπ A B κ X)
          (∏ i, SymmetricAlgebra.ι (B : Type u)
            ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X) (y i))
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ =>
      (SymPow.symAlgMap_ι (smallPolynomialAugmentationGradedOneπ A B κ X) (y i)).symm
  rw [hstep, smallPolynomialAugmentationSymMulApp_symMap]

/-- A product of `n` sections of `𝒦`, read in `B[S]`, lies in the `n`-th power of the
augmentation ideal. -/
lemma prod_mem_augmentationIdeal_pow (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (y : Fin n → ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)) :
    ∏ i, smallPolynomialQuotientAlgEquiv A B κ X
        ((y i : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u))) ∈
      MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n := by
  refine Stacks.prod_mem_pow _ n _ fun i => ?_
  have h : (y i : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u)) ∈
      smallPolynomialAugmentationIdeal A B κ X ^ 1 := (y i).2
  rw [pow_one, smallPolynomialAugmentationIdeal_eq_comap, Ideal.mem_comap] at h
  exact h

/-- **Multiplication in coordinates**: the product of the classes of `n` sections of `𝒦` is the
class of the product of those sections, read in the polynomial ring `B[S]`. -/
lemma smallPolynomialAugmentationGradedSectionsEquiv_symMul_prod_ι (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (y : Fin n → ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ 1 X)) :
    smallPolynomialAugmentationGradedSectionsEquiv A B κ n X
        (smallPolynomialAugmentationSymMulApp A B κ n X
          ⟨∏ i, SymmetricAlgebra.ι (B : Type u)
              (smallPolynomialAugmentationGradedSections A B κ 1 X)
              (smallPolynomialAugmentationGradedOneπ A B κ X (y i)),
            MvPolynomial.prod_ι_mem_symmetricPower n fun i =>
              smallPolynomialAugmentationGradedOneπ A B κ X (y i)⟩) =
      Submodule.Quotient.mk ⟨∏ i, smallPolynomialQuotientAlgEquiv A B κ X
        ((y i : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u))),
        prod_mem_augmentationIdeal_pow A B κ n X y⟩ := by
  rw [smallPolynomialAugmentationSymMulApp_prod_ι]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  refine (coe_smallPolynomialAugmentationIdealPowLinearEquiv A B κ n X
    (smallPolynomialAugmentationSymPowToPow A B κ n X
      ⟨∏ i, SymmetricAlgebra.ι (B : Type u) _ (y i),
        MvPolynomial.prod_ι_mem_symmetricPower n y⟩)).trans ?_
  refine (congrArg (fun z => smallPolynomialQuotientAlgEquiv A B κ X z)
    (coe_smallPolynomialAugmentationSymPowToPow_prod_ι A B κ n X y)).trans ?_
  exact map_prod (smallPolynomialQuotientAlgEquiv A B κ X)
    (fun i => (y i : ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u))) Finset.univ

/-- **Multiplication on the product of the classes of `n` variables**, in coordinates: the class
of the product of the corresponding generators `X s - g(s)` of the augmentation ideal. -/
lemma smallPolynomialAugmentationSymMul_prod_var (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) (σ : Fin n → ↑(X.unop.unop.1))
    (hprod : ∏ i, (MvPolynomial.X (σ i) -
        MvPolynomial.C (smallSitePoint A B κ X (σ i)) :
        MvPolynomial ↑(X.unop.unop.1) (B : Type u)) ∈
      MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n) :
    smallPolynomialAugmentationGradedSectionsEquiv A B κ n X
        (smallPolynomialAugmentationSymMulApp A B κ n X
          ⟨∏ i, SymmetricAlgebra.ι (B : Type u)
              (smallPolynomialAugmentationGradedSections A B κ 1 X)
              (smallPolynomialAugmentationGradedOneπ A B κ X
                (smallPolynomialAugmentationDiffSection A B κ X
                  (smallSiteVar A B κ X (σ i)))),
            MvPolynomial.prod_ι_mem_symmetricPower n fun i =>
              smallPolynomialAugmentationGradedOneπ A B κ X
                (smallPolynomialAugmentationDiffSection A B κ X
                  (smallSiteVar A B κ X (σ i)))⟩) =
      Submodule.Quotient.mk ⟨∏ i, (MvPolynomial.X (σ i) -
        MvPolynomial.C (smallSitePoint A B κ X (σ i))), hprod⟩ :=
  (smallPolynomialAugmentationGradedSectionsEquiv_symMul_prod_ι A B κ n X
      fun i => smallPolynomialAugmentationDiffSection A B κ X
        (smallSiteVar A B κ X (σ i))).trans
    (congrArg Submodule.Quotient.mk (Subtype.ext
      (show ∏ i, smallPolynomialQuotientAlgEquiv A B κ X
            ((smallPolynomialAugmentationDiffSection A B κ X
              (smallSiteVar A B κ X (σ i)) :
              ((smallPolynomialQuotientAlgebra A B κ).obj X : Type u))) =
          ∏ i, (MvPolynomial.X (σ i) -
            MvPolynomial.C (smallSitePoint A B κ X (σ i)) :
            MvPolynomial ↑(X.unop.unop.1) (B : Type u)) from
        Finset.prod_congr rfl fun i _ =>
          smallPolynomialQuotientAlgEquiv_smallPolynomialAugmentationDiff_var A B κ X (σ i))))

/-- The monomial basis of `𝒦ⁿ(U)/𝒦ⁿ⁺¹(U)`: the classes of the monomials of degree `n` in the
generators `X s - g(s)` of the augmentation ideal of `B[S]`. -/
def smallPolynomialAugmentationGradedBasis (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Module.Basis {d : ↥(X.unop.unop.1) →₀ ℕ | d.degree = n} (B : Type u)
      (smallPolynomialAugmentationGradedSections A B κ n X) :=
  (SymPow.basisSymmetricPower
    (Finsupp.basisSingleOne : Module.Basis ↥(X.unop.unop.1) (B : Type u)
      (↥(X.unop.unop.1) →₀ (B : Type u))) n).map
    ((MvPolynomial.symmetricPowerEquivAugmentationGraded (smallSitePoint A B κ X) n).trans
      (smallPolynomialAugmentationGradedSectionsEquiv A B κ n X).symm)

/-- The monomial basis of `𝒦ⁿ(U)/𝒦ⁿ⁺¹(U)`, read on a basis vector whose multidegree has been
enumerated by a tuple of variables. -/
lemma smallPolynomialAugmentationGradedBasis_apply_of_prod (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (d : {d : ↑(X.unop.unop.1) →₀ ℕ | d.degree = n}) (σ : Fin n → ↑(X.unop.unop.1))
    (hsym : ∏ i, SymmetricAlgebra.ι (B : Type u) (↑(X.unop.unop.1) →₀ (B : Type u))
        (Finsupp.single (σ i) 1) ∈
      SymPow.symmetricPower n (B : Type u) (↑(X.unop.unop.1) →₀ (B : Type u)))
    (hprod : ∏ i, (MvPolynomial.X (σ i) -
        MvPolynomial.C (smallSitePoint A B κ X (σ i)) :
        MvPolynomial ↑(X.unop.unop.1) (B : Type u)) ∈
      MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n)
    (hb : ((SymPow.basisSymmetricPower
          (Finsupp.basisSingleOne : Module.Basis ↑(X.unop.unop.1) (B : Type u)
            (↑(X.unop.unop.1) →₀ (B : Type u))) n) d :
        SymmetricAlgebra (B : Type u) (↑(X.unop.unop.1) →₀ (B : Type u))) =
      ∏ i, SymmetricAlgebra.ι (B : Type u) (↑(X.unop.unop.1) →₀ (B : Type u))
        (Finsupp.single (σ i) 1)) :
    smallPolynomialAugmentationGradedBasis A B κ n X d =
      (smallPolynomialAugmentationGradedSectionsEquiv A B κ n X).symm
        (Submodule.Quotient.mk ⟨∏ i, (MvPolynomial.X (σ i) -
          MvPolynomial.C (smallSitePoint A B κ X (σ i))), hprod⟩) :=
  congrArg (fun z => (smallPolynomialAugmentationGradedSectionsEquiv A B κ n X).symm z)
    ((congrArg (fun z => MvPolynomial.symmetricPowerEquivAugmentationGraded
          (smallSitePoint A B κ X) n z)
        (Subtype.ext hb : _ = (⟨_, hsym⟩ : ↥(SymPow.symmetricPower n (B : Type u)
          (↑(X.unop.unop.1) →₀ (B : Type u)))))).trans
      (MvPolynomial.symmetricPowerEquivAugmentationGraded_prod_ι
        (smallSitePoint A B κ X) n σ hsym hprod))

/-- Multiplication, read on a basis vector of `Sym^n_B(𝒦(U)/𝒦²(U))` whose multidegree has been
enumerated by a tuple of variables. -/
lemma smallPolynomialAugmentationSymMulApp_basis_of_prod (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (d : {d : ↑(X.unop.unop.1) →₀ ℕ | d.degree = n}) (σ : Fin n → ↑(X.unop.unop.1))
    (hprod : ∏ i, (MvPolynomial.X (σ i) -
        MvPolynomial.C (smallSitePoint A B κ X (σ i)) :
        MvPolynomial ↑(X.unop.unop.1) (B : Type u)) ∈
      MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n)
    (hb : ((SymPow.basisSymmetricPower
          (smallPolynomialAugmentationGradedOneBasis A B κ X) n) d :
        SymmetricAlgebra (B : Type u)
          (smallPolynomialAugmentationGradedSections A B κ 1 X)) =
      ∏ i, SymmetricAlgebra.ι (B : Type u)
        (smallPolynomialAugmentationGradedSections A B κ 1 X)
        (smallPolynomialAugmentationGradedOneπ A B κ X
          (smallPolynomialAugmentationDiffSection A B κ X
            (smallSiteVar A B κ X (σ i))))) :
    smallPolynomialAugmentationGradedSectionsEquiv A B κ n X
        (smallPolynomialAugmentationSymMulApp A B κ n X
          ((SymPow.basisSymmetricPower
            (smallPolynomialAugmentationGradedOneBasis A B κ X) n) d)) =
      Submodule.Quotient.mk ⟨∏ i, (MvPolynomial.X (σ i) -
        MvPolynomial.C (smallSitePoint A B κ X (σ i))), hprod⟩ :=
  (congrArg (fun z => smallPolynomialAugmentationGradedSectionsEquiv A B κ n X
        (smallPolynomialAugmentationSymMulApp A B κ n X z))
      (Subtype.ext hb : _ = (⟨_, MvPolynomial.prod_ι_mem_symmetricPower n fun i =>
        smallPolynomialAugmentationGradedOneπ A B κ X
          (smallPolynomialAugmentationDiffSection A B κ X
            (smallSiteVar A B κ X (σ i)))⟩ : ↥(SymPow.symmetricPower n (B : Type u)
        (smallPolynomialAugmentationGradedSections A B κ 1 X))))).trans
    (smallPolynomialAugmentationSymMul_prod_var A B κ n X σ hprod)

/-- The generator `X s - g(s)` of the augmentation ideal of `B[S]`. -/
lemma smallSiteGen_mem_augmentationIdeal (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (s : ↑(X.unop.unop.1)) :
    (MvPolynomial.X s - MvPolynomial.C (smallSitePoint A B κ X s) :
      MvPolynomial ↑(X.unop.unop.1) (B : Type u)) ∈
      MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) :=
  (MvPolynomial.mem_augmentationIdeal (smallSitePoint A B κ X)).2 (by simp)

/-- **Multiplication carries the monomial basis of `Sym^n_B(𝒦(U)/𝒦²(U))` to the monomial basis
of `𝒦ⁿ(U)/𝒦ⁿ⁺¹(U)`**, given an enumeration of the multidegree by a tuple of variables which
computes the two basis vectors. -/
lemma smallPolynomialAugmentationSymMulApp_basis_aux (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (d : {d : ↑(X.unop.unop.1) →₀ ℕ | d.degree = n}) (σ : Fin n → ↑(X.unop.unop.1))
    (h₁ : ((SymPow.basisSymmetricPower
          (smallPolynomialAugmentationGradedOneBasis A B κ X) n) d :
        SymmetricAlgebra (B : Type u)
          (smallPolynomialAugmentationGradedSections A B κ 1 X)) =
      ∏ i, SymmetricAlgebra.ι (B : Type u)
        (smallPolynomialAugmentationGradedSections A B κ 1 X)
        (smallPolynomialAugmentationGradedOneπ A B κ X
          (smallPolynomialAugmentationDiffSection A B κ X
            (smallSiteVar A B κ X (σ i)))))
    (h₂ : ((SymPow.basisSymmetricPower
          (Finsupp.basisSingleOne : Module.Basis ↑(X.unop.unop.1) (B : Type u)
            (↑(X.unop.unop.1) →₀ (B : Type u))) n) d :
        SymmetricAlgebra (B : Type u) (↑(X.unop.unop.1) →₀ (B : Type u))) =
      ∏ i, SymmetricAlgebra.ι (B : Type u) (↑(X.unop.unop.1) →₀ (B : Type u))
        (Finsupp.single (σ i) 1)) :
    smallPolynomialAugmentationSymMulApp A B κ n X
        ((SymPow.basisSymmetricPower
          (smallPolynomialAugmentationGradedOneBasis A B κ X) n) d) =
      smallPolynomialAugmentationGradedBasis A B κ n X d := by
  have hprod : ∏ i, (MvPolynomial.X (σ i) -
      MvPolynomial.C (smallSitePoint A B κ X (σ i)) :
      MvPolynomial ↑(X.unop.unop.1) (B : Type u)) ∈
      MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n :=
    Stacks.prod_mem_pow _ n _ fun i => smallSiteGen_mem_augmentationIdeal A B κ X (σ i)
  have hsym : ∏ i, SymmetricAlgebra.ι (B : Type u) (↑(X.unop.unop.1) →₀ (B : Type u))
      (Finsupp.single (σ i) 1) ∈
      SymPow.symmetricPower n (B : Type u) (↑(X.unop.unop.1) →₀ (B : Type u)) :=
    MvPolynomial.prod_ι_mem_symmetricPower n _
  have hlhs := smallPolynomialAugmentationSymMulApp_basis_of_prod A B κ n X d σ hprod h₁
  have hrhs := smallPolynomialAugmentationGradedBasis_apply_of_prod A B κ n X d σ hsym hprod h₂
  refine (smallPolynomialAugmentationGradedSectionsEquiv A B κ n X).injective ?_
  refine hlhs.trans (Eq.symm ?_)
  exact (congrArg (fun z => smallPolynomialAugmentationGradedSectionsEquiv A B κ n X z)
    hrhs).trans
    ((smallPolynomialAugmentationGradedSectionsEquiv A B κ n X).apply_symm_apply _)

/-- **Multiplication carries the monomial basis of `Sym^n_B(𝒦(U)/𝒦²(U))` to the monomial basis
of `𝒦ⁿ(U)/𝒦ⁿ⁺¹(U)`.** -/
lemma smallPolynomialAugmentationSymMulApp_basis (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ))
    (d : {d : ↑(X.unop.unop.1) →₀ ℕ | d.degree = n}) :
    smallPolynomialAugmentationSymMulApp A B κ n X
        ((SymPow.basisSymmetricPower
          (smallPolynomialAugmentationGradedOneBasis A B κ X) n) d) =
      smallPolynomialAugmentationGradedBasis A B κ n X d := by
  obtain ⟨σ, hσ⟩ := SymPow.exists_prod_ι_eq_coe_basisSymmetricPower_uniform n d
  have key : ∀ {M : Type u} [AddCommGroup M] [Module (B : Type u) M]
      (b : Module.Basis ↑(X.unop.unop.1) (B : Type u) M) (m : ↑(X.unop.unop.1) → M),
      (∀ s, b s = m s) →
      ((SymPow.basisSymmetricPower b n d : SymPow.symmetricPower n (B : Type u) M) :
        SymmetricAlgebra (B : Type u) M) =
      ∏ i, SymmetricAlgebra.ι (B : Type u) M (m (σ i)) := fun b m hm =>
    (hσ b).symm.trans (Finset.prod_congr rfl fun i _ => by rw [hm])
  exact smallPolynomialAugmentationSymMulApp_basis_aux A B κ n X d σ
    (key _ (fun s => smallPolynomialAugmentationGradedOneπ A B κ X
      (smallPolynomialAugmentationDiffSection A B κ X (smallSiteVar A B κ X s)))
      (smallPolynomialAugmentationGradedOneBasis_apply A B κ X))
    (key Finsupp.basisSingleOne (fun s => Finsupp.single s 1)
      fun s => congrFun Finsupp.coe_basisSingleOne s)

/-- **Multiplication is bijective over every object.** -/
lemma bijective_smallPolynomialAugmentationSymMulApp (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Function.Bijective (smallPolynomialAugmentationSymMulApp A B κ n X) :=
  Stacks.bijective_of_basis_eq
    (SymPow.basisSymmetricPower (smallPolynomialAugmentationGradedOneBasis A B κ X) n)
    (smallPolynomialAugmentationGradedBasis A B κ n X)
    (smallPolynomialAugmentationSymMulApp A B κ n X)
    (smallPolynomialAugmentationSymMulApp_basis A B κ n X)

/-- **`Sym^n_{B̲}(𝒦/𝒦²) ≅ 𝒦ⁿ/𝒦ⁿ⁺¹`**: multiplication in `Ō` is an isomorphism of presheaves of
`B`-modules. -/
def smallPolynomialAugmentationSymMulIso (n : ℕ) :
    Stacks.ChaoticSite.symmetricPowerDiagram (smallBoundedPolynomialSite A B κ) (B : Type u)
        (smallPolynomialAugmentationGraded A B κ 1) n ≅
      smallPolynomialAugmentationGraded A B κ n :=
  NatIso.ofComponents
    (fun X => (LinearEquiv.ofBijective _
      (bijective_smallPolynomialAugmentationSymMulApp A B κ n X)).toModuleIso)
    (fun f => (smallPolynomialAugmentationSymMul A B κ n).naturality f)

/-- **`𝒦ⁿ/𝒦ⁿ⁺¹ ≅ Sym^n_{B̲}(Ω)`.** The graded pieces of the augmentation filtration of
`Ō = 𝒪 ⊗_A B̲` are the symmetric powers of `Ω = i^*Ω_{𝒪/A}`, as presheaves of `B`-modules on the
small model of the polynomial site. This is the identification the `E₁`-page of Quillen's
spectral sequence rests on in the proof of [Stacks, Tag 08RF].

No hypothesis on `A → B` is needed. -/
def smallPolynomialAugmentationGradedSymmetricPowerIso (n : ℕ) :
    smallPolynomialAugmentationGraded A B κ n ≅
      Stacks.ChaoticSite.symmetricPowerDiagram (smallBoundedPolynomialSite A B κ) (B : Type u)
        (smallPolynomialCotangentModulePresheaf A B κ) n :=
  (smallPolynomialAugmentationSymMulIso A B κ n).symm ≪≫
    (Stacks.symPowDiagramMapIso (smallPolynomialCotangentGradedIso A B κ) n).symm

/-! ### The short exact sequence `0 → 𝒦ⁿ⁺¹ → 𝒦ⁿ → Sym^n_{B̲}(Ω) → 0` -/


/-- **The short complex `𝒦ⁿ⁺¹ → 𝒦ⁿ → Sym^n_{B̲}(Ω)`** of presheaves of `B`-modules: the inclusion
of the next step of the augmentation filtration, followed by the projection onto the graded piece
read through `CommAlgCat.smallPolynomialAugmentationGradedSymmetricPowerIso`. -/
def smallPolynomialAugmentationSymmetricPowerShortComplex (n : ℕ) :
    ShortComplex ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u)) :=
  ShortComplex.mk (smallPolynomialAugmentationIdealPowIncl A B κ n)
    (smallPolynomialAugmentationGradedπ A B κ n ≫
      (smallPolynomialAugmentationGradedSymmetricPowerIso A B κ n).hom)
    (by rw [← Category.assoc, smallPolynomialAugmentationIdealPowIncl_comp_gradedπ, zero_comp])

/-- **`0 → 𝒦ⁿ⁺¹ → 𝒦ⁿ → Sym^n_{B̲}(Ω) → 0` is exact.** Exactness of a sequence of presheaves of
modules is objectwise; over an object the first map is the inclusion of one submodule of the
sections of `Ō` into another, and the second is the projection onto the quotient, whose kernel is
exactly the first submodule (`CommAlgCat.ker_smallPolynomialAugmentationGradedπ`), composed with
an isomorphism. -/
lemma smallPolynomialAugmentationSymmetricPowerShortComplex_shortExact (n : ℕ) :
    (smallPolynomialAugmentationSymmetricPowerShortComplex A B κ n).ShortExact :=
  ShortComplex.shortExact_of_app _ fun X => by
    have hbij : Function.Bijective
        (((smallPolynomialAugmentationGradedSymmetricPowerIso A B κ n).app X).hom) :=
      (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
    refine ShortComplex.ShortExact.mk' ((ShortComplex.moduleCat_exact_iff _).2 ?_) ?_ ?_
    · intro x₂ hx₂
      have h1 : (smallPolynomialAugmentationGradedπ A B κ n).app X x₂ = 0 :=
        hbij.1 (hx₂.trans (map_zero _).symm)
      have hker : x₂ ∈ LinearMap.ker
          ((smallPolynomialAugmentationGradedπ A B κ n).app X).hom := h1
      rw [ker_smallPolynomialAugmentationGradedπ] at hker
      exact ⟨⟨(smallPolynomialAugmentationIdealPowSubmodule A B κ n X).subtype x₂,
        Submodule.mem_comap.1 hker⟩, rfl⟩
    · rw [ModuleCat.mono_iff_injective]
      exact Submodule.inclusion_injective
        (smallPolynomialAugmentationIdealPowSubmodule_antitone A B κ (Nat.le_succ n) X)
    · rw [ModuleCat.epi_iff_surjective]
      exact hbij.2.comp (surjective_smallPolynomialAugmentationGradedπ A B κ n X)

end CommAlgCat

end
