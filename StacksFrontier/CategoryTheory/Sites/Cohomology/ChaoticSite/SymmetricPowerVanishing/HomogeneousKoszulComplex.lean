module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.AlgebraicTopology.SimplicialTensorConnectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolutionOfModules
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.LinearAlgebra.SymmetricPower.Free
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import StacksFrontier.RingTheory.Flat.Lazard
public import StacksFrontier.RingTheory.Koszul.DifferentialGradedAlgebra
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.TensorAlgebra.Colimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing.SymmetricPowerDiagram
import StacksCore.Tactic.StacksAttribute

/-!
# The homogeneous Koszul complex

Koszul differentials of a bilinear map, the homogeneous Koszul complex `∧^p M ⊗ Sym^{k-p} M`,
and the exactness of the Koszul complex `∧^• M ⊗ Sym(M)` for a finite free module `M`.

This file is one part of `SymmetricPowerVanishing`, which imports all of them.
-/

@[expose] public noncomputable section

open scoped DirectSum TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Stacks.ChaoticSite

universe u v w

attribute [local instance] HasDerivedCategory.standard

section Koszul

open scoped TensorProduct

variable {B M P Q T : Type*} [CommRing B] [AddCommGroup M] [Module B M]
  [AddCommGroup P] [Module B P] [AddCommGroup Q] [Module B Q]
  [AddCommGroup T] [Module B T]

/-- The additive group structure on the exterior power `∧^p M`. -/
local instance (p : ℕ) : AddCommGroup (⋀[B]^p M) := inferInstance

/-- For a bilinear map `a : M → P → Q`, the map sending `x : M` to the alternating map
`(v, z) ↦ (v₁ ∧ ⋯ ∧ v_p) ⊗ a x z`. -/
def koszulAlternating (a : M →ₗ[B] P →ₗ[B] Q) (p : ℕ) :
    M →ₗ[B] M [⋀^Fin p]→ₗ[B] (P →ₗ[B] (⋀[B]^p M) ⊗[B] Q) where
  toFun x := ((TensorProduct.mk B (⋀[B]^p M) Q).compl₂
    (a x)).compAlternatingMap (exteriorPower.ιMulti B p)
  map_add' x y := by
    ext v z
    simp [TensorProduct.tmul_add]
  map_smul' r x := by
    ext v z
    simp

/-- The Koszul differential `∧^{p+1} M ⊗ P → ∧^p M ⊗ Q` of a bilinear map `a : M → P → Q`,
given on generators by `koszulDifferential_tmul`. -/
def koszulDifferential (a : M →ₗ[B] P →ₗ[B] Q) (p : ℕ) :
    (⋀[B]^(p + 1) M) ⊗[B] P →ₗ[B] (⋀[B]^p M) ⊗[B] Q :=
  TensorProduct.lift ((exteriorPower.alternatingMapLinearEquiv
    (R := B) (M := M) (N := P →ₗ[B] ((⋀[B]^p M) ⊗[B] Q)))
      (AlternatingMap.alternatizeUncurryFin (R := B) (M := M)
        (N := P →ₗ[B] ((⋀[B]^p M) ⊗[B] Q)) (koszulAlternating a p)))

/-- The Koszul differential sends `(v₀ ∧ ⋯ ∧ v_p) ⊗ z` to
`∑ᵢ (-1)ⁱ (v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ v_p) ⊗ a vᵢ z`. -/
lemma koszulDifferential_tmul (a : M →ₗ[B] P →ₗ[B] Q) (p : ℕ)
    (v : Fin (p + 1) → M) (z : P) :
    koszulDifferential a p (exteriorPower.ιMulti B (p + 1) v ⊗ₜ[B] z) =
      ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) •
        (exteriorPower.ιMulti B p (i.removeNth v) ⊗ₜ[B] a (v i) z) := by
  simp [koszulDifferential, AlternatingMap.alternatizeUncurryFin_apply,
    koszulAlternating]

/-- Linear maps out of `∧^n M ⊗ P` are equal if they agree on all `(v₁ ∧ ⋯ ∧ v_n) ⊗ z`. -/
private theorem exteriorPower_tensor_ext {n : ℕ} {f g : (⋀[B]^n M) ⊗[B] P →ₗ[B] Q}
    (h : ∀ (v : Fin n → M) (z : P),
      f (exteriorPower.ιMulti B n v ⊗ₜ[B] z) = g (exteriorPower.ιMulti B n v ⊗ₜ[B] z)) :
    f = g := by
  apply TensorProduct.ext
  apply exteriorPower.linearMap_ext (R := B) (M := M) (N := P →ₗ[B] Q)
  ext v z
  exact h v z

/-- For bilinear maps `a : M → P → Q` and `b : M → Q → T`, the map sending `x, y : M` to the
alternating map `(v, z) ↦ (v₁ ∧ ⋯ ∧ v_p) ⊗ b y (a x z)`. -/
def koszulBialternating (a : M →ₗ[B] P →ₗ[B] Q)
    (b : M →ₗ[B] Q →ₗ[B] T) (p : ℕ) :
    M →ₗ[B] M →ₗ[B] M [⋀^Fin p]→ₗ[B]
      (P →ₗ[B] (⋀[B]^p M) ⊗[B] T) where
  toFun x := {
    toFun y := ((TensorProduct.mk B (⋀[B]^p M) T).compl₂
      ((b y).comp (a x))).compAlternatingMap (exteriorPower.ιMulti B p)
    map_add' y z := by
      ext v t
      simp [TensorProduct.tmul_add]
    map_smul' r y := by
      ext v t
      simp }
  map_add' x y := by
    ext z v t
    simp [TensorProduct.tmul_add]
  map_smul' r x := by
    ext z v t
    simp

/-- If `b y (a x z) = b x (a y z)` for all `x y z`, then the composite of two Koszul
differentials, for `a` followed by `b`, is zero. -/
lemma koszulDifferential_comp
    (a : M →ₗ[B] P →ₗ[B] Q) (b : M →ₗ[B] Q →ₗ[B] T)
    (h : ∀ x y z, b y (a x z) = b x (a y z)) (p : ℕ) :
    (koszulDifferential b p).comp (koszulDifferential a (p + 1)) = 0 := by
  have hs : ∀ x y, koszulBialternating a b p x y =
      koszulBialternating a b p y x := by
    intro x y
    ext v z
    exact congrArg (fun t => exteriorPower.ιMulti B p v ⊗ₜ[B] t) (h x y z)
  have hz := AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
    (R := B) (M := M) (N := P →ₗ[B] ((⋀[B]^p M) ⊗[B] T))
    (f := koszulBialternating a b p) hs
  refine exteriorPower_tensor_ext fun v z => ?_
  change koszulDifferential b p
    (koszulDifferential a (p + 1) (exteriorPower.ιMulti B (p + 2) v ⊗ₜ[B] z)) = 0
  have he := congrArg (fun f => f v z) hz
  simpa [koszulDifferential_tmul, map_sum, map_zsmul,
    AlternatingMap.alternatizeUncurryFin_apply, LinearMap.comp_apply,
    AlternatingMap.alternatizeUncurryFinLM_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.smul_sum, AlternatingMap.zero_apply,
    LinearMap.zero_apply, koszulBialternating, LinearMap.compAlternatingMap_apply,
    LinearMap.compl₂_apply, TensorProduct.mk_apply] using he

/-- The Koszul differential is natural: linear maps `f`, `g`, `h` intertwining the bilinear maps
`a` and `b` commute with the Koszul differentials of `a` and `b`. -/
lemma koszulDifferential_naturality
    {N P' Q' : Type*} [AddCommGroup N] [Module B N]
    [AddCommGroup P'] [Module B P'] [AddCommGroup Q'] [Module B Q']
    (a : M →ₗ[B] P →ₗ[B] Q) (b : N →ₗ[B] P' →ₗ[B] Q')
    (f : M →ₗ[B] N) (g : P →ₗ[B] P') (h : Q →ₗ[B] Q')
    (hab : ∀ x z, h (a x z) = b (f x) (g z)) (p : ℕ) :
    (TensorProduct.map (exteriorPower.map p f) h).comp (koszulDifferential a p) =
      (koszulDifferential b p).comp
        (TensorProduct.map (exteriorPower.map (p + 1) f) g) := by
  refine exteriorPower_tensor_ext fun v z => ?_
  change TensorProduct.map (exteriorPower.map p f) h
      (koszulDifferential a p (exteriorPower.ιMulti B (p + 1) v ⊗ₜ[B] z)) =
    koszulDifferential b p
      (TensorProduct.map (exteriorPower.map (p + 1) f) g
        (exteriorPower.ιMulti B (p + 1) v ⊗ₜ[B] z))
  simp only [koszulDifferential_tmul, map_sum, map_zsmul,
    TensorProduct.map_tmul, exteriorPower.map_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hab]
  rfl

/-- The homogeneous Koszul differential `∧^{p+1} M ⊗ Sym^q M → ∧^p M ⊗ Sym^{q+1} M`, the
Koszul differential of multiplication `M ⊗ Sym^q M → Sym^{q+1} M`. -/
def homogeneousKoszulDifferential (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (p q : ℕ) :
    (⋀[B]^(p + 1) M) ⊗[B] SymPow.symmetricPower q B M →ₗ[B]
      (⋀[B]^p M) ⊗[B] SymPow.symmetricPower (q + 1) B M :=
  koszulDifferential (SymPow.symMulMapBil q (LinearMap.id : M →ₗ[B] M)) p

/-- Two consecutive homogeneous Koszul differentials compose to zero. -/
lemma homogeneousKoszulDifferential_comp (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (p q : ℕ) :
    (homogeneousKoszulDifferential B M p (q + 1)).comp
      (homogeneousKoszulDifferential B M (p + 1) q) = 0 := by
  apply koszulDifferential_comp
  intro x y z
  apply Subtype.ext
  change SymmetricAlgebra.ι B M y * (SymmetricAlgebra.ι B M x * z) =
    SymmetricAlgebra.ι B M x * (SymmetricAlgebra.ι B M y * z)
  exact mul_left_comm _ _ _

/-- The homogeneous Koszul differential is natural in the module `M`. -/
lemma homogeneousKoszulDifferential_naturality
    {N : Type*} [AddCommGroup N] [Module B N] (f : M →ₗ[B] N) (p q : ℕ) :
    (TensorProduct.map (exteriorPower.map p f) (SymPow.symMap (q + 1) f)).comp
        (homogeneousKoszulDifferential B M p q) =
      (homogeneousKoszulDifferential B N p q).comp
        (TensorProduct.map (exteriorPower.map (p + 1) f) (SymPow.symMap q f)) := by
  apply koszulDifferential_naturality
  intro x z
  apply Subtype.ext
  change SymPow.symAlgMap f (SymmetricAlgebra.ι B M x * z) =
    SymmetricAlgebra.ι B N (f x) * SymPow.symAlgMap f z
  rw [map_mul, SymPow.symAlgMap_ι]

/-- The isomorphism `∧^0 M ⊗ Sym^q M ≃ Sym^q M`. -/
def homogeneousKoszulZeroIso (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (q : ℕ) :
    ((⋀[B]^0 M) ⊗[B] SymPow.symmetricPower q B M) ≃ₗ[B]
      SymPow.symmetricPower q B M :=
  (TensorProduct.congr (exteriorPower.zeroEquiv B M) (LinearEquiv.refl B _)).trans
    (TensorProduct.lid B _)

/-- Under `∧^1 M ≃ M` and `∧^0 M ⊗ Sym^{q+1} M ≃ Sym^{q+1} M`, the homogeneous Koszul
differential out of degree `1` is multiplication `M ⊗ Sym^q M → Sym^{q+1} M`. -/
lemma homogeneousKoszulZeroIso_differential (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (q : ℕ) :
    (homogeneousKoszulZeroIso B M (q + 1)).toLinearMap.comp
      ((homogeneousKoszulDifferential B M 0 q).comp
        (TensorProduct.map (exteriorPower.oneEquiv B M).symm.toLinearMap LinearMap.id)) =
      SymPow.symMulMap q (LinearMap.id : M →ₗ[B] M) := by
  apply TensorProduct.ext
  ext x y
  have hx : (exteriorPower.oneEquiv B M).symm x =
      exteriorPower.ιMulti B 1 (fun _ => x) := by
    apply (exteriorPower.oneEquiv B M).injective
    simp [exteriorPower.oneEquiv_ιMulti]
  simp only [LinearMap.compr₂ₛₗ_apply, LinearMap.comp_apply,
    TensorProduct.mk_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    LinearMap.id_apply, hx]
  rw [homogeneousKoszulDifferential, koszulDifferential_tmul]
  simp [homogeneousKoszulZeroIso, exteriorPower.zeroEquiv_ιMulti,
    SymPow.symMulMap, SymPow.symMulMapBil]

/-- The homogeneous Koszul differential `∧^1 M ⊗ Sym^q M → ∧^0 M ⊗ Sym^{q+1} M` is
surjective. -/
lemma homogeneousKoszulDifferential_zero_surjective
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M] (q : ℕ) :
    Function.Surjective (homogeneousKoszulDifferential B M 0 q) := by
  intro z
  obtain ⟨x, hx⟩ := symmetricPower_multiplication_surjective q
    (homogeneousKoszulZeroIso B M (q + 1) z)
  refine ⟨TensorProduct.map (exteriorPower.oneEquiv B M).symm.toLinearMap LinearMap.id x, ?_⟩
  apply (homogeneousKoszulZeroIso B M (q + 1)).injective
  exact (LinearMap.congr_fun (homogeneousKoszulZeroIso_differential B M q) x).trans hx

/-- The differential `∧^{p+1} M ⊗ Sym^{k-p-1} M → ∧^p M ⊗ Sym^{k-p} M` of the homogeneous Koszul
complex in total degree `k`: the homogeneous Koszul differential for `p < k`, and zero
otherwise. -/
@[sga "6 IX 1.8" "partial"]
def homogeneousKoszulComplexDifferential (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (k p : ℕ) :
    ModuleCat.of B ((⋀[B]^(p + 1) M) ⊗[B] SymPow.symmetricPower (k - (p + 1)) B M) ⟶
      ModuleCat.of B ((⋀[B]^p M) ⊗[B] SymPow.symmetricPower (k - p) B M) :=
  if h : p < k then
    ModuleCat.ofHom (homogeneousKoszulDifferential B M p (k - (p + 1))) ≫
      eqToHom (by rw [show k - p = k - (p + 1) + 1 from by omega])
  else 0

/-- Two consecutive homogeneous Koszul differentials, composed with the identifications of
symmetric powers along `q + 1 = r` and `r + 1 = s`, compose to zero. -/
lemma homogeneousKoszulDifferential_comp_cast (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (p q r s : ℕ) (hqr : q + 1 = r) (hrs : r + 1 = s) :
    (ModuleCat.ofHom (homogeneousKoszulDifferential B M (p + 1) q) ≫
      eqToHom (congrArg
        (fun n => ModuleCat.of B ((⋀[B]^(p + 1) M) ⊗[B] SymPow.symmetricPower n B M)) hqr)) ≫
      ModuleCat.ofHom (homogeneousKoszulDifferential B M p r) ≫
        eqToHom (congrArg
          (fun n => ModuleCat.of B ((⋀[B]^p M) ⊗[B] SymPow.symmetricPower n B M)) hrs) = 0 := by
  subst r
  subst s
  simp only [eqToHom_refl, Category.comp_id]
  apply ModuleCat.hom_ext
  exact homogeneousKoszulDifferential_comp B M p q

/-- Two consecutive differentials of the homogeneous Koszul complex compose to zero. -/
lemma homogeneousKoszulComplexDifferential_comp (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (k p : ℕ) :
    homogeneousKoszulComplexDifferential B M k (p + 1) ≫
      homogeneousKoszulComplexDifferential B M k p = 0 := by
  by_cases hp : p + 1 < k
  · have hp' : p < k := by omega
    simp only [homogeneousKoszulComplexDifferential, dite_eq_left hp, dite_eq_left hp']
    exact homogeneousKoszulDifferential_comp_cast B M p
      (k - (p + 1 + 1)) (k - (p + 1)) (k - p) (by omega) (by omega)
  · simp [homogeneousKoszulComplexDifferential, hp]

/-- The homogeneous Koszul complex in total degree `k`, with `∧^p M ⊗ Sym^{k-p} M` in degree
`p`. -/
def homogeneousKoszulComplex (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (k : ℕ) :
    ChainComplex (ModuleCat B) ℕ :=
  ChainComplex.of
    (fun p => ModuleCat.of B ((⋀[B]^p M) ⊗[B] SymPow.symmetricPower (k - p) B M))
    (homogeneousKoszulComplexDifferential B M k)
    (homogeneousKoszulComplexDifferential_comp B M k)

/-- The differential of the homogeneous Koszul complex from degree `p + 1` to degree `p` is
`homogeneousKoszulComplexDifferential`. -/
lemma homogeneousKoszulComplex_d (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (k p : ℕ) :
    (homogeneousKoszulComplex B M k).d (p + 1) p =
      homogeneousKoszulComplexDifferential B M k p :=
  ChainComplex.of_d
    (fun p => ModuleCat.of B ((⋀[B]^p M) ⊗[B] SymPow.symmetricPower (k - p) B M))
    (homogeneousKoszulComplexDifferential B M k) p

/-- For `k > 0`, the homogeneous Koszul complex in total degree `k` is exact in degree `0`. -/
lemma homogeneousKoszulComplex_exactAt_zero
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M]
    (k : ℕ) (hk : 0 < k) :
    (homogeneousKoszulComplex B M k).ExactAt 0 := by
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)]
  apply (ShortComplex.exact_iff_epi _ (by
    change (homogeneousKoszulComplex B M k).d 0 0 = 0
    apply HomologicalComplex.shape; simp)).mpr
  rw [ModuleCat.epi_iff_surjective]
  change Function.Surjective ((homogeneousKoszulComplex B M k).d 1 0).hom
  rw [homogeneousKoszulComplex_d]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have h := homogeneousKoszulDifferential_zero_surjective B M q
  simp only [homogeneousKoszulComplex, ChainComplex.of,
    homogeneousKoszulComplexDifferential, dite_eq_left (Nat.succ_pos q), Nat.sub_zero,
    eqToHom_refl, Category.comp_id, ModuleCat.hom_ofHom]
  with_unfolding_all exact h

/-- The action of `M` on `Sym_B(M)` by left multiplication: `x ↦ (z ↦ x · z)`. -/
def symmetricKoszulAction (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] :
    M →ₗ[B] SymmetricAlgebra B M →ₗ[B] SymmetricAlgebra B M :=
  (LinearMap.mul B (SymmetricAlgebra B M)).comp (SymmetricAlgebra.ι B M)

/-- The Koszul differential `∧^{p+1} M ⊗ Sym_B(M) → ∧^p M ⊗ Sym_B(M)` of the multiplication
action of `M` on its symmetric algebra. -/
def symmetricKoszulDifferential (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (p : ℕ) :
    ((⋀[B]^(p + 1) M) ⊗[B] SymmetricAlgebra B M) →ₗ[B]
      ((⋀[B]^p M) ⊗[B] SymmetricAlgebra B M) :=
  koszulDifferential (symmetricKoszulAction B M) p

/-- The degree `q + 1` component of `x · z` is `x` times the degree `q` component of `z`. -/
lemma symmetricPowerProjection_mul_ι (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (q : ℕ) (x : M) (z : SymmetricAlgebra B M) :
    symmetricPowerProjection B M (q + 1) (SymmetricAlgebra.ι B M x * z) =
      SymPow.symMulMapBil q (LinearMap.id : M →ₗ[B] M) x
        (symmetricPowerProjection B M q z) := by
  apply Subtype.ext
  change (SymPow.degreeMap (SymmetricAlgebra.ι B M x * z)).coeff (q + 1) =
    SymmetricAlgebra.ι B M x * (SymPow.degreeMap z).coeff q
  rw [map_mul, SymPow.degreeMap_ι, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul]

/-- The inclusions `Sym^q M ⊆ Sym_B(M)` intertwine the homogeneous Koszul differential with the
Koszul differential on `Sym_B(M)`. -/
lemma symmetricKoszulDifferential_subtype (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (p q : ℕ) :
    (TensorProduct.map LinearMap.id (SymPow.symmetricPower (q + 1) B M).subtype).comp
        (homogeneousKoszulDifferential B M p q) =
      (symmetricKoszulDifferential B M p).comp
        (TensorProduct.map LinearMap.id (SymPow.symmetricPower q B M).subtype) := by
  simpa only [exteriorPower.map_id, homogeneousKoszulDifferential,
    symmetricKoszulDifferential] using
    koszulDifferential_naturality
      (SymPow.symMulMapBil q (LinearMap.id : M →ₗ[B] M))
      (symmetricKoszulAction B M) LinearMap.id
      (SymPow.symmetricPower q B M).subtype
      (SymPow.symmetricPower (q + 1) B M).subtype (fun _ _ => rfl) p

/-- The projections `Sym_B(M) → Sym^q M` intertwine the Koszul differential on `Sym_B(M)` with
the homogeneous Koszul differential. -/
lemma symmetricKoszulDifferential_projection (B M : Type*) [CommRing B]
    [AddCommGroup M] [Module B M] (p q : ℕ) :
    (TensorProduct.map LinearMap.id (symmetricPowerProjection B M (q + 1))).comp
        (symmetricKoszulDifferential B M p) =
      (homogeneousKoszulDifferential B M p q).comp
        (TensorProduct.map LinearMap.id (symmetricPowerProjection B M q)) := by
  simpa only [exteriorPower.map_id, homogeneousKoszulDifferential,
    symmetricKoszulDifferential] using
    koszulDifferential_naturality (symmetricKoszulAction B M)
      (SymPow.symMulMapBil q (LinearMap.id : M →ₗ[B] M)) LinearMap.id
      (symmetricPowerProjection B M q) (symmetricPowerProjection B M (q + 1))
      (symmetricPowerProjection_mul_ι B M q) p

/-- Exactness of the Koszul complex on `Sym_B(M)` at `∧^{p+1} M ⊗ Sym_B(M)` implies exactness of
each homogeneous Koszul complex at `∧^{p+1} M ⊗ Sym^{q+1} M`. -/
lemma homogeneousKoszul_exact_of_symmetricKoszul_exact
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M] (p q : ℕ)
    (h : Function.Exact (symmetricKoszulDifferential B M (p + 1))
      (symmetricKoszulDifferential B M p)) :
    Function.Exact (homogeneousKoszulDifferential B M (p + 1) q)
      (homogeneousKoszulDifferential B M p (q + 1)) := by
  intro x
  constructor
  · intro hx
    let i (n d : ℕ) := TensorProduct.map
      (LinearMap.id : (⋀[B]^n M) →ₗ[B] ⋀[B]^n M) (SymPow.symmetricPower d B M).subtype
    have hz : symmetricKoszulDifferential B M p (i (p + 1) (q + 1) x) = 0 := by
      rw [← LinearMap.comp_apply, ← symmetricKoszulDifferential_subtype]
      rw [LinearMap.comp_apply, hx, map_zero]
    obtain ⟨y, hy⟩ := (h _).mp hz
    refine ⟨TensorProduct.map LinearMap.id (symmetricPowerProjection B M q) y, ?_⟩
    change ((homogeneousKoszulDifferential B M (p + 1) q).comp
      (TensorProduct.map LinearMap.id (symmetricPowerProjection B M q))) y = x
    rw [← symmetricKoszulDifferential_projection, LinearMap.comp_apply, hy]
    change ((TensorProduct.map LinearMap.id (symmetricPowerProjection B M (q + 1))).comp
      (TensorProduct.map LinearMap.id (SymPow.symmetricPower (q + 1) B M).subtype)) x = x
    rw [← TensorProduct.map_comp, symmetricPowerProjection_subtype, LinearMap.id_comp,
      TensorProduct.map_id, LinearMap.id_apply]
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (homogeneousKoszulDifferential_comp B M p q) y

open MvPolynomial in
/-- If `i ∉ s`, then `Xᵢ · p` lies in the ideal generated by the variables indexed by `s` if and
only if `p` does. -/
lemma mul_X_mem_span_iff {R : Type u} [CommRing R] {σ : Type v}
    (s : Set σ) (i : σ) (hi : i ∉ s) (p : MvPolynomial σ R) :
    X i * p ∈ Ideal.span (X '' s) ↔ p ∈ Ideal.span (X '' s) := by
  classical
  constructor
  · intro hp
    rw [mem_ideal_span_X_image] at hp ⊢
    intro m hm
    have hmm : Finsupp.single i 1 + m ∈ (X i * p).support := by
      simpa only [mem_support_iff, coeff_X_mul] using (mem_support_iff.mp hm)
    obtain ⟨j, hj, hmj⟩ := hp _ hmm
    refine ⟨j, hj, ?_⟩
    have hji : i ≠ j := by rintro rfl; exact hi hj
    simpa [Finsupp.add_apply, Finsupp.single_eq_of_ne hji.symm] using hmj
  · exact fun hp => Ideal.mul_mem_left _ _ hp

open MvPolynomial in
/-- A finite sequence of distinct variables of a polynomial ring is weakly regular. -/
lemma variables_isWeaklyRegular (R : Type u) [CommRing R]
    (σ : Type v) (n : ℕ) (f : Fin n → σ) (hf : Function.Injective f) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ R)
      (List.ofFn (fun j => (X (f j) : MvPolynomial σ R))) := by
  classical
  constructor
  intro j hj
  have hjn : j < n := by simpa using hj
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  have hs : Ideal.ofList ((List.ofFn (fun j => (X (f j) : MvPolynomial σ R))).take j) =
      Ideal.span (X '' {i | ∃ a : Fin n, a.val < j ∧ f a = i}) := by
    apply congrArg Ideal.span
    ext p
    change p ∈ (List.ofFn (fun j => (X (f j) : MvPolynomial σ R))).take j ↔ _
    simp only [List.mem_take_iff_getElem, List.length_ofFn, List.getElem_ofFn,
      Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk, he⟩
      exact ⟨f ⟨k, lt_of_lt_of_le hk (Nat.min_le_right _ _)⟩,
        ⟨⟨k, lt_of_lt_of_le hk (Nat.min_le_right _ _)⟩,
          lt_of_lt_of_le hk (Nat.min_le_left _ _), rfl⟩, he⟩
    · rintro ⟨i, ⟨a, ha, rfl⟩, he⟩
      exact ⟨a.val, lt_min ha a.isLt, he⟩
  rw [hs, Ideal.smul_eq_mul, Ideal.mul_top]
  simp only [List.getElem_ofFn]
  intro p hp
  exact (mul_X_mem_span_iff _ (f ⟨j, hjn⟩) (by
    rintro ⟨a, ha, he⟩
    have hh := congrArg Fin.val (hf he)
    exact (Nat.ne_of_lt ha) hh) p).mp hp

open MvPolynomial in
/-- A finite sequence of distinct variables of a polynomial ring is Koszul-regular. -/
lemma variables_isKoszulRegular (R : Type u) [CommRing R]
    (σ : Type v) (n : ℕ) (f : Fin n → σ) (hf : Function.Injective f) :
    Koszul.IsKoszulRegular (fun j => (X (f j) : MvPolynomial σ R)) := by
  apply (Koszul.isKoszulRegularOn_self_iff _).mp
  apply Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular.1
  exact variables_isWeaklyRegular R σ n f hf

/-- For `M = Bⁿ`, the identification `∧^p_B M ⊗_B Sym_B(M) ≃ ∧^p_{B[X₁,…,Xₙ]}(B[X₁,…,Xₙ]ⁿ)`. -/
def finiteFreeKoszulTermEquiv (B : Type*) [CommRing B] (n p : ℕ) :
    ((⋀[B]^p (Fin n → B)) ⊗[B] SymmetricAlgebra B (Fin n → B)) ≃ₗ[B]
      (⋀[MvPolynomial (Fin n) B]^p (Fin n → MvPolynomial (Fin n) B)) :=
  (TensorProduct.congr (LinearEquiv.refl B _)
    (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun B (Fin n))).toLinearEquiv).trans
      ((TensorProduct.comm B _ _).trans
        ((Classical.choose (KoszulC.extPow_baseChange_natEquiv
          (R := B) (S := MvPolynomial (Fin n) B) (r := n) p)).restrictScalars B))

/-- `finiteFreeKoszulTermEquiv` sends `(v₁ ∧ ⋯ ∧ v_p) ⊗ z` to `z · (v₁ ∧ ⋯ ∧ v_p)`, with `z`
read as a polynomial and the `vᵢ` as constant vectors. -/
lemma finiteFreeKoszulTermEquiv_tmul (B : Type*) [CommRing B] (n p : ℕ)
    (v : Fin p → (Fin n → B)) (z : SymmetricAlgebra B (Fin n → B)) :
    finiteFreeKoszulTermEquiv B n p (exteriorPower.ιMulti B p v ⊗ₜ[B] z) =
      SymmetricAlgebra.equivMvPolynomial (Pi.basisFun B (Fin n)) z •
        exteriorPower.ιMulti (MvPolynomial (Fin n) B) p
          (fun i j => algebraMap B (MvPolynomial (Fin n) B) (v i j)) := by
  let β := Classical.choose (KoszulC.extPow_baseChange_natEquiv
    (R := B) (S := MvPolynomial (Fin n) B) (r := n) p)
  change β (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun B (Fin n)) z ⊗ₜ[B]
    exteriorPower.ιMulti B p v) = _
  rw [show (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun B (Fin n)) z ⊗ₜ[B]
      exteriorPower.ιMulti B p v) =
    SymmetricAlgebra.equivMvPolynomial (Pi.basisFun B (Fin n)) z •
      (1 ⊗ₜ[B] exteriorPower.ιMulti B p v) by simp [TensorProduct.smul_tmul']]
  rw [map_smul, Classical.choose_spec (KoszulC.extPow_baseChange_natEquiv
    (R := B) (S := MvPolynomial (Fin n) B) (r := n) p)]

/-- `finiteFreeKoszulTermEquiv` commutes with multiplication by an integer. -/
lemma finiteFreeKoszulTermEquiv_zsmul (B : Type*) [CommRing B] (n p : ℕ) (m : ℤ)
    (x : (⋀[B]^p (Fin n → B)) ⊗[B] SymmetricAlgebra B (Fin n → B)) :
    finiteFreeKoszulTermEquiv B n p (m • x) = m • finiteFreeKoszulTermEquiv B n p x :=
  map_zsmul (finiteFreeKoszulTermEquiv B n p) m x

set_option synthInstance.maxHeartbeats 200000 in
/-- `finiteFreeKoszulTermEquiv` commutes with finite sums. -/
lemma finiteFreeKoszulTermEquiv_sum {ι : Type*} (B : Type*) [CommRing B] (n p : ℕ)
    (s : Finset ι) (x : ι → (⋀[B]^p (Fin n → B)) ⊗[B] SymmetricAlgebra B (Fin n → B)) :
    finiteFreeKoszulTermEquiv B n p (∑ i ∈ s, x i) =
      ∑ i ∈ s, finiteFreeKoszulTermEquiv B n p (x i) :=
  map_sum (finiteFreeKoszulTermEquiv B n p) x s

/-- The linear form on `B[X₁,…,Xₙ]ⁿ` dual to the sequence of variables, evaluated at a constant
vector `v`, is the polynomial `∑ᵢ vᵢ Xᵢ`, the image of `v` in `Sym_B(Bⁿ) ≃ B[X₁,…,Xₙ]`. -/
lemma finiteFreeKoszulDual (B : Type*) [CommRing B] (n : ℕ) (v : Fin n → B) :
    Koszul.seqDual (MvPolynomial.X : Fin n → MvPolynomial (Fin n) B)
      (fun i => algebraMap B (MvPolynomial (Fin n) B) (v i)) =
      SymmetricAlgebra.equivMvPolynomial (Pi.basisFun B (Fin n))
        (SymmetricAlgebra.ι B (Fin n → B) v) := by
  classical
  conv_rhs => rw [← (Pi.basisFun B (Fin n)).sum_repr v]
  simp only [map_sum, map_smul, SymmetricAlgebra.equivMvPolynomial_ι_apply]
  simp [Koszul.seqDual_apply, Algebra.smul_def]

/-- The Koszul differential of a linear form `φ` sends `w₀ ∧ ⋯ ∧ w_q` to
`∑ₖ (-1)ᵏ φ(wₖ) (w₀ ∧ ⋯ ∧ ŵₖ ∧ ⋯ ∧ w_q)`. -/
lemma koszul_d_ιMulti {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : Module.Dual R M)
    (q : ℕ) (w : Fin (q + 1) → M) :
    Koszul.d φ q (exteriorPower.ιMulti R (q + 1) w) =
      ∑ k : Fin (q + 1), ((-1 : R) ^ k.val * φ (w k)) •
        exteriorPower.ιMulti R q (w ∘ k.succAbove) := by
  apply Subtype.ext
  simpa only [Koszul.d_apply_coe, exteriorPower.ιMulti_apply_coe,
    Submodule.coe_sum, Submodule.coe_smul_of_tower] using
    Koszul.contraction_ιMulti φ q w

/-- Under `finiteFreeKoszulTermEquiv`, the Koszul differential on `∧^• Bⁿ ⊗ Sym_B(Bⁿ)` becomes
the Koszul differential of the sequence of variables `X₁, …, Xₙ` of `B[X₁,…,Xₙ]`. -/
lemma finiteFreeKoszulTermEquiv_d (B : Type*) [CommRing B] (n p : ℕ) :
    (finiteFreeKoszulTermEquiv B n p).toLinearMap.comp
      (symmetricKoszulDifferential B (Fin n → B) p) =
    ((Koszul.d (Koszul.seqDual (MvPolynomial.X : Fin n → MvPolynomial (Fin n) B))
      p).restrictScalars B).comp (finiteFreeKoszulTermEquiv B n (p + 1)).toLinearMap := by
  refine exteriorPower_tensor_ext fun v z => ?_
  change finiteFreeKoszulTermEquiv B n p
    (koszulDifferential (symmetricKoszulAction B (Fin n → B)) p
      (exteriorPower.ιMulti B (p + 1) v ⊗ₜ[B] z)) =
    Koszul.d (Koszul.seqDual (MvPolynomial.X : Fin n → MvPolynomial (Fin n) B)) p
      (finiteFreeKoszulTermEquiv B n (p + 1)
        (exteriorPower.ιMulti B (p + 1) v ⊗ₜ[B] z))
  rw [koszulDifferential_tmul, finiteFreeKoszulTermEquiv_tmul, map_smul,
    koszul_d_ιMulti, Finset.smul_sum]
  simp only [finiteFreeKoszulTermEquiv_sum, finiteFreeKoszulTermEquiv_zsmul,
    finiteFreeKoszulTermEquiv_tmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteFreeKoszulDual]
  change (-1 : ℤ) ^ (i : ℕ) •
    (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun B (Fin n))
      (SymmetricAlgebra.ι B (Fin n → B) (v i) * z) • _) = _
  rw [map_mul]
  simp only [← Int.cast_smul_eq_zsmul (R := MvPolynomial (Fin n) B),
    Int.cast_pow, Int.cast_neg, Int.cast_one, smul_smul]
  congr 1
  ring

/-- The Koszul complex `∧^• Bⁿ ⊗ Sym_B(Bⁿ)` is exact in every positive degree. -/
lemma symmetricKoszul_exact_pi (B : Type*) [CommRing B] (n p : ℕ) :
    Function.Exact (symmetricKoszulDifferential B (Fin n → B) (p + 1))
      (symmetricKoszulDifferential B (Fin n → B) p) := by
  let S := MvPolynomial (Fin n) B
  have hreg := variables_isKoszulRegular B (Fin n) n id Function.injective_id
  have hs : (Koszul.seqComplex (MvPolynomial.X : Fin n → S)).ExactAt (p + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (hreg (p + 1) (by omega))
  rw [HomologicalComplex.exactAt_iff' _ (p + 1 + 1) (p + 1) p (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hs
  change Function.Exact
    ((Koszul.seqComplex (MvPolynomial.X : Fin n → S)).d (p + 1 + 1) (p + 1)).hom
    ((Koszul.seqComplex (MvPolynomial.X : Fin n → S)).d (p + 1) p).hom at hs
  rw [Koszul.seqComplex_d, Koszul.seqComplex_d] at hs
  apply (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := finiteFreeKoszulTermEquiv B n (p + 1 + 1))
    (e₂ := finiteFreeKoszulTermEquiv B n (p + 1))
    (e₃ := finiteFreeKoszulTermEquiv B n p)
    (f₁₂ := symmetricKoszulDifferential B (Fin n → B) (p + 1))
    (f₂₃ := symmetricKoszulDifferential B (Fin n → B) p)
    (g₁₂ := (Koszul.d (Koszul.seqDual (MvPolynomial.X : Fin n → S)) (p + 1)).restrictScalars B)
    (g₂₃ := (Koszul.d (Koszul.seqDual (MvPolynomial.X : Fin n → S)) p).restrictScalars B)
    (finiteFreeKoszulTermEquiv_d B n (p + 1)).symm
    (finiteFreeKoszulTermEquiv_d B n p).symm).mp
  exact hs

/-- A linear isomorphism `M ≃ N` induces a linear isomorphism `∧^p M ≃ ∧^p N`. -/
def exteriorPowerCongr {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (p : ℕ) : (⋀[R]^p M) ≃ₗ[R] (⋀[R]^p N) :=
  LinearEquiv.ofLinearMap (exteriorPower.map p e.toLinearMap)
    (exteriorPower.map p e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp, e.comp_symm, exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp, e.symm_comp, exteriorPower.map_id])

/-- The Koszul differential on `∧^• M ⊗ Sym_R(M)` is natural in `M`. -/
lemma symmetricKoszulDifferential_naturality
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (p : ℕ) :
    (TensorProduct.map (exteriorPower.map p f) (symmetricAlgebraMap f).toLinearMap).comp
        (symmetricKoszulDifferential R M p) =
      (symmetricKoszulDifferential R N p).comp
        (TensorProduct.map (exteriorPower.map (p + 1) f) (symmetricAlgebraMap f).toLinearMap) := by
  apply koszulDifferential_naturality
  intro x z
  change symmetricAlgebraMap f (SymmetricAlgebra.ι R M x * z) =
    SymmetricAlgebra.ι R N (f x) * symmetricAlgebraMap f z
  rw [map_mul, symmetricAlgebraMap_ι]

/-- Exactness of the Koszul complex `∧^• N ⊗ Sym_R(N)` at a given degree transfers along a linear
isomorphism `M ≃ N`. -/
lemma symmetricKoszul_exact_of_equiv
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (p : ℕ)
    (h : Function.Exact (symmetricKoszulDifferential R N (p + 1))
      (symmetricKoszulDifferential R N p)) :
    Function.Exact (symmetricKoszulDifferential R M (p + 1))
      (symmetricKoszulDifferential R M p) := by
  let E (q : ℕ) := TensorProduct.congr (exteriorPowerCongr e q)
    (symmetricAlgebraEquiv e).toLinearEquiv
  apply (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := E (p + 1 + 1)) (e₂ := E (p + 1)) (e₃ := E p)
    (f₁₂ := symmetricKoszulDifferential R M (p + 1))
    (f₂₃ := symmetricKoszulDifferential R M p)
    (g₁₂ := symmetricKoszulDifferential R N (p + 1))
    (g₂₃ := symmetricKoszulDifferential R N p) ?_ ?_).mp h
  · exact (symmetricKoszulDifferential_naturality e.toLinearMap (p + 1)).symm
  · exact (symmetricKoszulDifferential_naturality e.toLinearMap p).symm

/-- For a finite free module `M`, the Koszul complex `∧^• M ⊗ Sym_R(M)` is exact in every
positive degree. -/
lemma symmetricKoszul_exact_of_finite_free
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (p : ℕ) :
    Function.Exact (symmetricKoszulDifferential R M (p + 1))
      (symmetricKoszulDifferential R M p) := by
  classical
  let b := (Module.Free.chooseBasis R M).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex R M))
  exact symmetricKoszul_exact_of_equiv b.equivFun p (symmetricKoszul_exact_pi R _ p)

end Koszul

end Stacks.ChaoticSite

end
