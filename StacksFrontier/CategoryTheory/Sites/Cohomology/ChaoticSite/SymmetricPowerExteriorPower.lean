module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.AcyclicDimensionShift
public import StacksFrontier.AlgebraicTopology.SimplicialObject.DecalageShortExact
public import StacksFrontier.AlgebraicTopology.SimplicialObject.FunctorNullHomotopy
public import StacksFrontier.AlgebraicTopology.SimplicialObject.PowerZerothHomology
public import StacksFrontier.LinearAlgebra.SymmetricPower.RelativeKoszul

/-!
# The décalage identity for symmetric powers of a simplicial module

Let `B` be a commutative ring — no hypothesis whatsoever on `B`, in particular `2` need not be
invertible — and let `Y` be a simplicial `B`-module which is degreewise flat and whose Moore
complex has vanishing homology in degree zero. Write `N = H₁(Y)`. Then

`H_k(Symᵏ Y) ≅ ⋀ᵏ_B N`

for every `k`. This is the simplicial-module core of Remark 08SG of the Stacks project.

## Main results

* `Stacks.ChaoticSite.nonempty_linearEquiv_homology_symPow`: the displayed isomorphism.

## Implementation notes

The proof is Illusie's and Quillen's décalage. Let `D = decRed Y` be the reduced décalage: it is
degreewise flat, it is simplicially null-homotopic, and `decRedδ₀ : D ⟶ Y` is degreewise
surjective because `H₀(Y) = 0`. Let `W = ker(D → Y)`, which is degreewise flat as well; the long
exact sequence of `0 → W → D → Y → 0` gives `H₀(W) ≅ H₁(Y) = N`.

The relative Koszul complex of `W ⊆ D` in total degree `k`,

`0 → ⋀ᵏW → ⋀ᵏ⁻¹W ⊗ Sym¹D → ⋯ → ⋀¹W ⊗ Symᵏ⁻¹D → ⋀⁰W ⊗ SymᵏD → SymᵏY → 0`,

is degreewise exact. Every term but the two ends carries a factor `SymᵠD` with `q ≥ 1`, and
`SymᵠD` inherits the null homotopy of `D` because `Symᵠ` is a functor which preserves the zero
morphism in positive degree; tensoring keeps a null homotopy. So all those terms have acyclic
Moore complexes, and dimension shifting `k` times along the resulting short exact sequences gives
`H_k(SymᵏY) ≅ H₀(⋀ᵏW) ≅ ⋀ᵏ(H₀ W) ≅ ⋀ᵏ N`.

The bookkeeping is organised around the simplicial modules `koszulTerm B W D p q = ⋀ᵖW ⊗ SymᵠD`
and the cycles `simpKer (koszulTermd B ι p q)`; the chain of dimension shifts is
`Stacks.ChaoticSite.homologyIsoKoszulCycles`, an induction on the remaining symmetric degree,
which therefore never meets a natural-number subtraction.

The case `k = 0` is separate: there the Koszul complex degenerates and the content is that both
sides are the base ring, which is `Stacks.ChaoticSite.symPowZeroIsoExtPowZero` together with the
`k = 0` case of `nonempty_linearEquiv_homologyZero_extPowFunctor`.

## References

* [Stacks Project, Tag 08SG](https://stacks.math.columbia.edu/tag/08SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open MonoidalCategory StacksDraft.SimplicialTensor

open scoped TensorProduct Simplicial

namespace Stacks.ChaoticSite

universe u

/-! ### The degree-zero symmetric power is the base ring -/

/-- The augmentation of the symmetric algebra: the algebra homomorphism `Sym_B(M) → B` induced by
the zero map `M → B`. It retracts the structure map `B → Sym_B(M)`, which is what makes the
degree-zero symmetric power a free module of rank one. -/
public def symAlgAug (B : Type u) [CommRing B] (M : Type u) [AddCommGroup M] [Module B M] :
    SymmetricAlgebra B M →ₐ[B] B :=
  SymmetricAlgebra.lift (0 : M →ₗ[B] B)

/-- The augmentation of the symmetric algebra retracts the structure map. -/
public lemma symAlgAug_algebraMap (B : Type u) [CommRing B] (M : Type u) [AddCommGroup M]
    [Module B M] (r : B) :
    symAlgAug B M (algebraMap B (SymmetricAlgebra B M) r) = r := by
  rw [AlgHom.commutes, Algebra.algebraMap_self_apply]

/-- The degree-zero symmetric power consists exactly of the scalars: it is the unit submodule of
the symmetric algebra, the zeroth power of the degree-one part. -/
public lemma mem_symmetricPower_zero_iff (B : Type u) [CommRing B] (M : Type u) [AddCommGroup M]
    [Module B M] {x : SymmetricAlgebra B M} :
    x ∈ SymPow.symmetricPower 0 B M ↔ ∃ r : B, algebraMap B (SymmetricAlgebra B M) r = x := by
  rw [show SymPow.symmetricPower 0 B M = 1 from pow_zero _]
  exact Submodule.mem_one

/-- The comparison of the degree-zero symmetric power with the base ring: the restriction of the
augmentation of the symmetric algebra. -/
public def symPowZeroMap (B : Type u) [CommRing B] (M : Type u) [AddCommGroup M] [Module B M] :
    SymPow.symmetricPower 0 B M →ₗ[B] B :=
  (symAlgAug B M).toLinearMap.comp (SymPow.symmetricPower 0 B M).subtype

/-- The comparison of the degree-zero symmetric power with the base ring is the augmentation. -/
public lemma symPowZeroMap_apply (B : Type u) [CommRing B] (M : Type u) [AddCommGroup M]
    [Module B M] (x : SymPow.symmetricPower 0 B M) :
    symPowZeroMap B M x = symAlgAug B M (x : SymmetricAlgebra B M) := rfl

/-- The comparison of the degree-zero symmetric power with the base ring is bijective. -/
public lemma symPowZeroMap_bijective (B : Type u) [CommRing B] (M : Type u) [AddCommGroup M]
    [Module B M] : Function.Bijective (symPowZeroMap B M) := by
  refine ⟨fun x y hxy => ?_, fun r => ?_⟩
  · obtain ⟨a, ha⟩ := (mem_symmetricPower_zero_iff B M).mp x.2
    obtain ⟨b, hb⟩ := (mem_symmetricPower_zero_iff B M).mp y.2
    simp only [symPowZeroMap_apply, ← ha, ← hb, symAlgAug_algebraMap] at hxy
    exact Subtype.ext (by rw [← ha, ← hb, hxy])
  · exact ⟨⟨algebraMap B (SymmetricAlgebra B M) r,
      (mem_symmetricPower_zero_iff B M).mpr ⟨r, rfl⟩⟩, symAlgAug_algebraMap B M r⟩

/-- **The degree-zero symmetric power of a module is the base ring.** -/
public def symPowZeroEquiv (B : Type u) [CommRing B] (M : Type u) [AddCommGroup M]
    [Module B M] : SymPow.symmetricPower 0 B M ≃ₗ[B] B :=
  LinearEquiv.ofBijective (symPowZeroMap B M) (symPowZeroMap_bijective B M)

/-- The comparison of the degree-zero symmetric power with the base ring is natural: the
degree-zero symmetric power of a linear map is the identity of the base ring. -/
public lemma symPowZeroMap_comp_symMap (B : Type u) [CommRing B] {M N : Type u}
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] (f : M →ₗ[B] N) :
    (symPowZeroMap B N).comp (SymPow.symMap 0 f) = symPowZeroMap B M := by
  have h : (symAlgAug B N).comp (SymPow.symAlgMap f) = symAlgAug B M := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
    simp [symAlgAug, SymPow.symAlgMap_ι]
  exact LinearMap.ext fun x => DFunLike.congr_fun h (x : SymmetricAlgebra B M)

/-! ### The degree-zero exterior factor of a relative Koszul term -/

-- The value of `SymPow.relKoszulZeroIso` on a pure tensor is `SymPow.relKoszulZeroIso_tmul`,
-- stated for arbitrary universes in
-- `StacksFrontier/LinearAlgebra/SymmetricPower/RelativeKoszul.lean`, which this module already
-- imports.

/-- Naturality of `SymPow.relKoszulZeroIso` in both variables. -/
public lemma relKoszulZeroIso_naturality (B : Type u) [CommRing B] {A A' M M' : Type u}
    [AddCommGroup A] [Module B A] [AddCommGroup A'] [Module B A']
    [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B M']
    (a : A →ₗ[B] A') (m : M →ₗ[B] M') (q : ℕ) :
    (SymPow.relKoszulZeroIso B A' M' q).toLinearMap.comp
        (TensorProduct.map (exteriorPower.map 0 a) (SymPow.symMap q m)) =
      (SymPow.symMap q m).comp (SymPow.relKoszulZeroIso B A M q).toLinearMap := by
  refine TensorProduct.ext' fun x y => ?_
  have h := LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality a) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  change SymPow.relKoszulZeroIso B A' M' q
      (TensorProduct.map (exteriorPower.map 0 a) (SymPow.symMap q m) (x ⊗ₜ[B] y)) =
    SymPow.symMap q m (SymPow.relKoszulZeroIso B A M q (x ⊗ₜ[B] y))
  rw [TensorProduct.map_tmul, SymPow.relKoszulZeroIso_tmul, SymPow.relKoszulZeroIso_tmul, h,
    LinearMap.map_smul]

/-- The degree-zero symmetric power factor of a relative Koszul term is a scalar:
`⋀ᵏA ⊗ Sym⁰M ≅ ⋀ᵏA`. -/
public def extPowRidEquiv (B : Type u) [CommRing B] (A M : Type u) [AddCommGroup A]
    [Module B A] [AddCommGroup M] [Module B M] (k : ℕ) :
    ((⋀[B]^k A) ⊗[B] SymPow.symmetricPower 0 B M) ≃ₗ[B] ⋀[B]^k A :=
  (TensorProduct.congr (LinearEquiv.refl B (⋀[B]^k A)) (symPowZeroEquiv B M)).trans
    (TensorProduct.rid B (⋀[B]^k A))

/-- Naturality of `Stacks.ChaoticSite.extPowRidEquiv` in both variables. -/
public lemma extPowRidEquiv_naturality (B : Type u) [CommRing B] {A A' M M' : Type u}
    [AddCommGroup A] [Module B A] [AddCommGroup A'] [Module B A']
    [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B M']
    (a : A →ₗ[B] A') (m : M →ₗ[B] M') (k : ℕ) :
    (extPowRidEquiv B A' M' k).toLinearMap.comp
        (TensorProduct.map (exteriorPower.map k a) (SymPow.symMap 0 m)) =
      (exteriorPower.map k a).comp (extPowRidEquiv B A M k).toLinearMap := by
  refine TensorProduct.ext' fun x y => ?_
  have h := LinearMap.congr_fun (symPowZeroMap_comp_symMap B m) y
  simp only [LinearMap.comp_apply] at h
  change symPowZeroMap B M' (SymPow.symMap 0 m y) • exteriorPower.map k a x =
    exteriorPower.map k a (symPowZeroMap B M y • x)
  rw [h, LinearMap.map_smul]

/-- The degree-zero symmetric power and the degree-zero exterior power of a module are both the
base ring, hence agree. -/
public def symPowZeroExtPowZeroEquiv (B : Type u) [CommRing B] (M : Type u) [AddCommGroup M]
    [Module B M] : SymPow.symmetricPower 0 B M ≃ₗ[B] ⋀[B]^0 M :=
  (symPowZeroEquiv B M).trans (exteriorPower.zeroEquiv B M).symm

/-- Naturality of `Stacks.ChaoticSite.symPowZeroExtPowZeroEquiv`. -/
public lemma symPowZeroExtPowZeroEquiv_naturality (B : Type u) [CommRing B] {M N : Type u}
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] (f : M →ₗ[B] N) :
    (symPowZeroExtPowZeroEquiv B N).toLinearMap.comp (SymPow.symMap 0 f) =
      (exteriorPower.map 0 f).comp (symPowZeroExtPowZeroEquiv B M).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  have h := LinearMap.congr_fun (symPowZeroMap_comp_symMap B f) x
  simp only [LinearMap.comp_apply] at h
  change (exteriorPower.zeroEquiv B N).symm (symPowZeroMap B N (SymPow.symMap 0 f x)) =
    exteriorPower.map 0 f ((exteriorPower.zeroEquiv B M).symm (symPowZeroMap B M x))
  rw [h]
  refine (exteriorPower.zeroEquiv B N).injective ?_
  have h2 := LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality f)
    ((exteriorPower.zeroEquiv B M).symm (symPowZeroMap B M x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h2
  rw [LinearEquiv.apply_symm_apply, h2, LinearEquiv.apply_symm_apply]

/-! ### The relative Koszul differential of a linear map -/

/-- Two consecutive relative Koszul differentials of a linear map compose to zero: the
multiplication of the symmetric algebra is commutative. -/
public lemma relKoszulDifferential_comp {B A M : Type u} [CommRing B] [AddCommGroup A]
    [Module B A] [AddCommGroup M] [Module B M] (f : A →ₗ[B] M) (p q : ℕ) :
    (koszulDifferential (SymPow.symMulMapBil (q + 1) f) p).comp
        (koszulDifferential (SymPow.symMulMapBil q f) (p + 1)) = 0 := by
  apply koszulDifferential_comp
  intro x y z
  apply Subtype.ext
  change SymmetricAlgebra.ι B M (f y) * (SymmetricAlgebra.ι B M (f x) * z) =
    SymmetricAlgebra.ι B M (f x) * (SymmetricAlgebra.ι B M (f y) * z)
  exact mul_left_comm _ _ _

/-- Naturality of the relative Koszul differential in a commutative square of linear maps. -/
public lemma relKoszulDifferential_naturality {B A A' M M' : Type u} [CommRing B]
    [AddCommGroup A] [Module B A] [AddCommGroup A'] [Module B A']
    [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B M']
    (f : A →ₗ[B] M) (f' : A' →ₗ[B] M') (a : A →ₗ[B] A') (m : M →ₗ[B] M')
    (hcomm : ∀ x, f' (a x) = m (f x)) (p q : ℕ) :
    (TensorProduct.map (exteriorPower.map p a) (SymPow.symMap (q + 1) m)).comp
        (koszulDifferential (SymPow.symMulMapBil q f) p) =
      (koszulDifferential (SymPow.symMulMapBil q f') p).comp
        (TensorProduct.map (exteriorPower.map (p + 1) a) (SymPow.symMap q m)) := by
  apply koszulDifferential_naturality
  intro x z
  apply Subtype.ext
  change SymPow.symAlgMap m (SymmetricAlgebra.ι B M (f x) * z) =
    SymmetricAlgebra.ι B M' (f' (a x)) * SymPow.symAlgMap m z
  rw [map_mul, SymPow.symAlgMap_ι, hcomm]

/-! ### Kernel sequences of simplicial modules and dimension shifting -/

/-- A morphism of simplicial modules whose composite with `v` vanishes, corestricted to the
degreewise kernel of `v`. -/
public def simpKerLiftExact {B : Type u} [CommRing B]
    {X₁ X₂ X₃ : SimplicialObject (ModuleCat.{u} B)} (u : X₁ ⟶ X₂) (v : X₂ ⟶ X₃)
    (huv : u ≫ v = 0) : X₁ ⟶ simpKer v where
  app n := ModuleCat.ofHom (((u.app n).hom).codRestrict _ (fun x =>
    LinearMap.mem_ker.mpr
      (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (NatTrans.congr_app huv n)) x)))
  naturality n m θ := by
    ext x : 2
    exact Subtype.ext (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (u.naturality θ)) x)

/-- The degreewise kernel of `u` is killed by the corestriction of `u` to the degreewise kernel
of `v`. -/
public lemma simpKerι_comp_simpKerLiftExact {B : Type u} [CommRing B]
    {X₁ X₂ X₃ : SimplicialObject (ModuleCat.{u} B)} (u : X₁ ⟶ X₂) (v : X₂ ⟶ X₃)
    (huv : u ≫ v = 0) : simpKerι u ≫ simpKerLiftExact u v huv = 0 := by
  ext n : 2
  exact LinearMap.ext fun x => Subtype.ext (LinearMap.mem_ker.mp x.2)

/-- **Dimension shifting along the kernel sequence of a degreewise exact pair.** If
`u : X₁ ⟶ X₂` and `v : X₂ ⟶ X₃` are degreewise exact and the Moore complex of `X₁` is acyclic,
then `0 → ker u → X₁ → ker v → 0` is a degreewise short exact sequence with acyclic middle term,
so homology is shifted by one degree. -/
public def homologyIsoKerPair {B : Type u} [CommRing B]
    {X₁ X₂ X₃ : SimplicialObject (ModuleCat.{u} B)} (u : X₁ ⟶ X₂) (v : X₂ ⟶ X₃)
    (huv : u ≫ v = 0)
    (hex : ∀ n : SimplexCategoryᵒᵖ, Function.Exact (u.app n).hom (v.app n).hom)
    (hX : ∀ n : ℕ, IsZero (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj X₁).homology n))
    (n : ℕ) :
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj (simpKer v)).homology (n + 1) ≅
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj (simpKer u)).homology n := by
  refine homologyIsoOfDegreewiseShortExactOfAcyclic (simpKerι u) (simpKerLiftExact u v huv)
    (simpKerι_comp_simpKerLiftExact u v huv) (fun Δ => ?_) hX n
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro y
    refine ⟨fun hy => ⟨⟨y, LinearMap.mem_ker.mpr (congrArg Subtype.val hy)⟩, rfl⟩, ?_⟩
    rintro ⟨⟨x, hx⟩, rfl⟩
    exact Subtype.ext (LinearMap.mem_ker.mp hx)
  · exact (LinearMap.ker (u.app Δ).hom).injective_subtype
  · intro y
    obtain ⟨x, hx⟩ := (hex Δ _).mp (LinearMap.mem_ker.mp y.2)
    exact ⟨x, Subtype.ext hx⟩

/-- **Dimension shifting along the kernel sequence of a degreewise surjection.** If
`f : X₂ ⟶ X₃` is degreewise surjective and the Moore complex of `X₂` is acyclic, homology is
shifted by one degree from `X₃` to the degreewise kernel of `f`. -/
public def homologyIsoKerSurj {B : Type u} [CommRing B]
    {X₂ X₃ : SimplicialObject (ModuleCat.{u} B)} (f : X₂ ⟶ X₃)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom)
    (hX : ∀ n : ℕ, IsZero (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj X₂).homology n))
    (n : ℕ) :
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj X₃).homology (n + 1) ≅
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj (simpKer f)).homology n :=
  homologyIsoOfDegreewiseShortExactOfAcyclic (simpKerι f) f (simpKerι_comp f)
    (fun Δ => ModuleCat.shortComplex_shortExact _
      (LinearMap.exact_subtype_ker_map (f.app Δ).hom)
      (LinearMap.ker (f.app Δ).hom).injective_subtype (hf Δ)) hX n

/-- If moreover `u` is degreewise injective, the corestriction of `u` to the degreewise kernel of
`v` is an isomorphism: the kernel sequence of the pair has a zero left-hand term. -/
public def simpKerLiftIso {B : Type u} [CommRing B]
    {X₁ X₂ X₃ : SimplicialObject (ModuleCat.{u} B)} (u : X₁ ⟶ X₂) (v : X₂ ⟶ X₃)
    (huv : u ≫ v = 0)
    (hex : ∀ n : SimplexCategoryᵒᵖ, Function.Exact (u.app n).hom (v.app n).hom)
    (hinj : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (u.app n).hom) :
    X₁ ≅ simpKer v :=
  NatIso.ofComponents
    (fun n => (LinearEquiv.ofBijective ((simpKerLiftExact u v huv).app n).hom
      ⟨fun x y hxy => hinj n (congrArg Subtype.val hxy), fun y => by
        obtain ⟨x, hx⟩ := (hex n _).mp (LinearMap.mem_ker.mp y.2)
        exact ⟨x, Subtype.ext hx⟩⟩).toModuleIso)
    (fun θ => (simpKerLiftExact u v huv).naturality θ)

/-! ### The relative Koszul complex of simplicial modules -/

/-- The term `⋀ᵖW ⊗ SymᵠD` of the relative Koszul complex of a morphism `W ⟶ D` of simplicial
modules, as a simplicial module: the degreewise tensor product of the degreewise `p`-th exterior
power of `W` and the degreewise `q`-th symmetric power of `D`. -/
public def koszulTerm (B : Type u) [CommRing B] (W D : SimplicialObject (ModuleCat.{u} B))
    (p q : ℕ) : SimplicialObject (ModuleCat.{u} B) :=
  (W ⋙ Stacks.ModuleCat.extPowFunctor B p) ⊗ (D ⋙ Stacks.ModuleCat.symPowFunctor B q)

/-- The relative Koszul differential `⋀ᵖ⁺¹W ⊗ SymᵠD ⟶ ⋀ᵖW ⊗ Symᵠ⁺¹D` of a morphism `ι : W ⟶ D`
of simplicial modules, applied degreewise. -/
public def koszulTermd (B : Type u) [CommRing B] {W D : SimplicialObject (ModuleCat.{u} B)}
    (ι : W ⟶ D) (p q : ℕ) : koszulTerm B W D (p + 1) q ⟶ koszulTerm B W D p (q + 1) where
  app n := ModuleCat.ofHom (koszulDifferential (SymPow.symMulMapBil q (ι.app n).hom) p)
  naturality n m θ := by
    have hcomm : ∀ x : W.obj n, (ι.app m).hom ((W.map θ).hom x) =
        (D.map θ).hom ((ι.app n).hom x) :=
      fun x => LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ι.naturality θ)) x
    exact ModuleCat.hom_ext (LinearMap.ext fun t => (LinearMap.congr_fun
      (relKoszulDifferential_naturality _ _ _ _ hcomm p q) t).symm)

/-- Two consecutive relative Koszul differentials of simplicial modules compose to zero. -/
public lemma koszulTermd_comp (B : Type u) [CommRing B]
    {W D : SimplicialObject (ModuleCat.{u} B)} (ι : W ⟶ D) (p q : ℕ) :
    koszulTermd B ι (p + 1) q ≫ koszulTermd B ι p (q + 1) = 0 := by
  ext n : 2
  exact relKoszulDifferential_comp ((ι.app n).hom) p q

/-- The augmentation `⋀⁰W ⊗ SymᵏD ⟶ SymᵏY` of the relative Koszul complex attached to a morphism
`π : D ⟶ Y` of simplicial modules. -/
public def koszulAug (B : Type u) [CommRing B] (W : SimplicialObject (ModuleCat.{u} B))
    {D Y : SimplicialObject (ModuleCat.{u} B)} (π : D ⟶ Y) (k : ℕ) :
    koszulTerm B W D 0 k ⟶ Y ⋙ Stacks.ModuleCat.symPowFunctor B k where
  app n := ModuleCat.ofHom ((SymPow.symMap k (π.app n).hom).comp
    (SymPow.relKoszulZeroIso B (W.obj n) (D.obj n) k).toLinearMap)
  naturality n m θ := by
    have hfg : ((π.app m).hom).comp ((D.map θ).hom) =
        ((Y.map θ).hom).comp ((π.app n).hom) :=
      congrArg ModuleCat.Hom.hom (π.naturality θ)
    have key := relKoszulZeroIso_naturality B ((W.map θ).hom) ((D.map θ).hom) k
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun t => ?_
    change SymPow.symMap k ((π.app m).hom)
        (SymPow.relKoszulZeroIso B (W.obj m) (D.obj m) k
          (TensorProduct.map (exteriorPower.map 0 ((W.map θ).hom))
            (SymPow.symMap k ((D.map θ).hom)) t)) =
      SymPow.symMap k ((Y.map θ).hom) (SymPow.symMap k ((π.app n).hom)
        (SymPow.relKoszulZeroIso B (W.obj n) (D.obj n) k t))
    rw [show SymPow.relKoszulZeroIso B (W.obj m) (D.obj m) k
        (TensorProduct.map (exteriorPower.map 0 ((W.map θ).hom))
          (SymPow.symMap k ((D.map θ).hom)) t) =
        SymPow.symMap k ((D.map θ).hom)
          (SymPow.relKoszulZeroIso B (W.obj n) (D.obj n) k t) from
      LinearMap.congr_fun key t]
    rw [symMap_comp_apply, symMap_comp_apply, hfg]

/-- **The relative Koszul terms of positive symmetric degree are acyclic.** If `D` is
simplicially null-homotopic then so is `SymᵠD` for `q ≥ 1`, because the symmetric power functor
of positive degree preserves the zero morphism, and a null homotopy survives tensoring. -/
public lemma isZero_homology_koszulTerm (B : Type u) [CommRing B]
    (W : SimplicialObject (ModuleCat.{u} B)) {D : SimplicialObject (ModuleCat.{u} B)}
    (hD : SimplicialObject.Homotopy (0 : D ⟶ D) (𝟙 D)) (p q n : ℕ) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
      (koszulTerm B W D p (q + 1))).homology n) :=
  SimplicialObject.Homotopy.isZero_homology_of_nullHomotopy
    (SimplicialObject.Homotopy.whiskerLeftNullHomotopy
      (W ⋙ Stacks.ModuleCat.extPowFunctor B p)
      (hD.nullHomotopyWhiskerRight (Stacks.ModuleCat.symPowFunctor B (q + 1))
        (fun Z Z' => Stacks.ModuleCat.symPowFunctor_map_eq_zero (Nat.succ_pos q) Z Z'))) n

/-- The top term of the relative Koszul complex is the exterior power alone: the degree-zero
symmetric power factor is the base ring. -/
public def koszulTermTopIso (B : Type u) [CommRing B]
    (W D : SimplicialObject (ModuleCat.{u} B)) (k : ℕ) :
    koszulTerm B W D k 0 ≅ W ⋙ Stacks.ModuleCat.extPowFunctor B k :=
  NatIso.ofComponents
    (fun n => (extPowRidEquiv B (W.obj n) (D.obj n) k).toModuleIso)
    (fun θ => ModuleCat.hom_ext (LinearMap.ext fun t => LinearMap.congr_fun
      (extPowRidEquiv_naturality B ((W.map θ).hom) ((D.map θ).hom) k) t))

/-- The degree-zero symmetric power and the degree-zero exterior power of a simplicial module
agree: both are the constant simplicial module at the base ring. -/
public def symPowZeroIsoExtPowZero (B : Type u) [CommRing B]
    (X : SimplicialObject (ModuleCat.{u} B)) :
    X ⋙ Stacks.ModuleCat.symPowFunctor B 0 ≅ X ⋙ Stacks.ModuleCat.extPowFunctor B 0 :=
  NatIso.ofComponents
    (fun n => (symPowZeroExtPowZeroEquiv B (X.obj n)).toModuleIso)
    (fun θ => ModuleCat.hom_ext (LinearMap.ext fun t => LinearMap.congr_fun
      (symPowZeroExtPowZeroEquiv_naturality B ((X.map θ).hom)) t))

/-! ### Degreewise exactness of the simplicial relative Koszul complex -/

/-- **The simplicial relative Koszul complex is degreewise exact in the interior.** This is
`SymPow.relativeKoszul_exact` applied in each simplicial degree to the short exact sequence
`0 → W → D → Y → 0` of degreewise flat simplicial modules. -/
public lemma koszulTermd_exact_app (B : Type u) [CommRing B]
    {W D Y : SimplicialObject (ModuleCat.{u} B)} (ι : W ⟶ D) (π : D ⟶ Y)
    (hW : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (W.obj n))
    (hD : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (D.obj n))
    (hYf : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (Y.obj n))
    (hmono : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (ι.app n).hom)
    (hexact : ∀ n : SimplexCategoryᵒᵖ, Function.Exact (ι.app n).hom (π.app n).hom)
    (hepi : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (π.app n).hom)
    (p q : ℕ) (n : SimplexCategoryᵒᵖ) :
    Function.Exact ((koszulTermd B ι (p + 1) q).app n).hom
      ((koszulTermd B ι p (q + 1)).app n).hom := by
  have := hW n
  have := hD n
  have := hYf n
  exact SymPow.relativeKoszul_exact ((ι.app n).hom) ((π.app n).hom) (hmono n) (hexact n)
    (hepi n) p q

/-- **The top map of the simplicial relative Koszul complex is degreewise injective.** This is
`SymPow.relativeKoszul_injective` applied in each simplicial degree. -/
public lemma koszulTermd_injective_app (B : Type u) [CommRing B]
    {W D Y : SimplicialObject (ModuleCat.{u} B)} (ι : W ⟶ D) (π : D ⟶ Y)
    (hW : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (W.obj n))
    (hD : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (D.obj n))
    (hYf : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (Y.obj n))
    (hmono : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (ι.app n).hom)
    (hexact : ∀ n : SimplexCategoryᵒᵖ, Function.Exact (ι.app n).hom (π.app n).hom)
    (hepi : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (π.app n).hom)
    (p : ℕ) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((koszulTermd B ι p 0).app n).hom := by
  have := hW n
  have := hD n
  have := hYf n
  exact SymPow.relativeKoszul_injective ((ι.app n).hom) ((π.app n).hom) (hmono n) (hexact n)
    (hepi n) p

/-- **The simplicial relative Koszul complex is degreewise exact at the augmentation.** This is
`SymPow.relativeKoszul_exact_zero` applied in each simplicial degree. -/
public lemma koszulAug_exact_app (B : Type u) [CommRing B]
    {W D Y : SimplicialObject (ModuleCat.{u} B)} (ι : W ⟶ D) (π : D ⟶ Y)
    (hW : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (W.obj n))
    (hD : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (D.obj n))
    (hYf : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (Y.obj n))
    (hexact : ∀ n : SimplexCategoryᵒᵖ, Function.Exact (ι.app n).hom (π.app n).hom)
    (hepi : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (π.app n).hom)
    (q : ℕ) (n : SimplexCategoryᵒᵖ) :
    Function.Exact ((koszulTermd B ι 0 q).app n).hom
      ((koszulAug B W π (q + 1)).app n).hom := by
  have := hW n
  have := hD n
  have := hYf n
  exact SymPow.relativeKoszul_exact_zero ((ι.app n).hom) ((π.app n).hom) (hexact n)
    (hepi n) q

/-- **The augmentation of the simplicial relative Koszul complex is degreewise surjective.** It
is a symmetric power of a degreewise surjection composed with an isomorphism. -/
public lemma koszulAug_surjective_app (B : Type u) [CommRing B]
    (W : SimplicialObject (ModuleCat.{u} B)) {D Y : SimplicialObject (ModuleCat.{u} B)}
    (π : D ⟶ Y) (hepi : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (π.app n).hom)
    (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((koszulAug B W π k).app n).hom := by
  intro y
  obtain ⟨z, hz⟩ := SymPow.symMap_surjective k ((π.app n).hom) (hepi n) y
  refine ⟨(SymPow.relKoszulZeroIso B (W.obj n) (D.obj n) k).symm z, ?_⟩
  change SymPow.symMap k ((π.app n).hom)
      (SymPow.relKoszulZeroIso B (W.obj n) (D.obj n) k
        ((SymPow.relKoszulZeroIso B (W.obj n) (D.obj n) k).symm z)) = y
  rwa [LinearEquiv.apply_symm_apply]

/-! ### The chain of dimension shifts -/

/-- **The dimension shifts along the relative Koszul complex.** Starting from the cycles of the
differential out of `⋀ᵖ⁺¹W ⊗ Symᵠ⁺¹D` and shifting once for each remaining symmetric degree, the
homology in degree `n + q` is the homology in degree `n` of the top term `⋀ᵗW ⊗ Sym⁰D` with
`t = p + q + 2`. The induction is on `q`, so no natural-number subtraction occurs; the degrees
`m` and `t` are parameters constrained by equations, so that the statement can be applied at any
spelling of them. -/
public def homologyIsoKoszulCycles (B : Type u) [CommRing B]
    {W D : SimplicialObject (ModuleCat.{u} B)} (ι : W ⟶ D)
    (hex : ∀ p q : ℕ, ∀ n : SimplexCategoryᵒᵖ,
      Function.Exact ((koszulTermd B ι (p + 1) q).app n).hom
        ((koszulTermd B ι p (q + 1)).app n).hom)
    (hinj : ∀ p : ℕ, ∀ n : SimplexCategoryᵒᵖ,
      Function.Injective ((koszulTermd B ι p 0).app n).hom)
    (hac : ∀ p q n : ℕ, IsZero (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
      (koszulTerm B W D p (q + 1))).homology n))
    (q p n m t : ℕ) (hm : m = n + q) (ht : t = p + q + 2) :
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (simpKer (koszulTermd B ι p (q + 1)))).homology m ≅
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (koszulTerm B W D t 0)).homology n := by
  induction q generalizing p n m t with
  | zero =>
    rw [hm, ht]
    exact ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) _ n).mapIso
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).mapIso
        (simpKerLiftIso (koszulTermd B ι (p + 1) 0) (koszulTermd B ι p 1)
          (koszulTermd_comp B ι p 0) (hex p 0) (hinj (p + 1))))).symm
  | succ q ih =>
    rw [hm]
    exact (homologyIsoKerPair (koszulTermd B ι (p + 1) (q + 1))
      (koszulTermd B ι p (q + 2)) (koszulTermd_comp B ι p (q + 1)) (hex p (q + 1))
      (hac (p + 2) q) (n + q)).trans (ih (p + 1) n (n + q) t rfl (by omega))

/-- **The homology of a symmetric power, shifted onto the top Koszul term.** For `k = q + 1` the
degree-`k` homology of the Moore complex of `SymᵏY` is the degree-zero homology of the top term
`⋀ᵏW ⊗ Sym⁰D` of the relative Koszul complex. -/
public def homologyIsoSymPowKoszul (B : Type u) [CommRing B]
    {W D Y : SimplicialObject (ModuleCat.{u} B)} (ι : W ⟶ D) (π : D ⟶ Y)
    (hex : ∀ p q : ℕ, ∀ n : SimplexCategoryᵒᵖ,
      Function.Exact ((koszulTermd B ι (p + 1) q).app n).hom
        ((koszulTermd B ι p (q + 1)).app n).hom)
    (hinj : ∀ p : ℕ, ∀ n : SimplexCategoryᵒᵖ,
      Function.Injective ((koszulTermd B ι p 0).app n).hom)
    (haugex : ∀ q : ℕ, ∀ n : SimplexCategoryᵒᵖ,
      Function.Exact ((koszulTermd B ι 0 q).app n).hom
        ((koszulAug B W π (q + 1)).app n).hom)
    (haugsurj : ∀ k : ℕ, ∀ n : SimplexCategoryᵒᵖ,
      Function.Surjective ((koszulAug B W π k).app n).hom)
    (hac : ∀ p q n : ℕ, IsZero (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
      (koszulTerm B W D p (q + 1))).homology n))
    (q : ℕ) :
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (Y ⋙ Stacks.ModuleCat.symPowFunctor B (q + 1))).homology (q + 1) ≅
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (koszulTerm B W D (q + 1) 0)).homology 0 := by
  have hzero : ∀ j : ℕ, koszulTermd B ι 0 j ≫ koszulAug B W π (j + 1) = 0 := by
    intro j
    ext n : 2
    exact (haugex j n).linearMap_comp_eq_zero
  rcases q with _ | q
  · exact (homologyIsoKerSurj (koszulAug B W π 1) (haugsurj 1) (hac 0 0) 0).trans
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) _ 0).mapIso
        ((alternatingFaceMapComplex (ModuleCat.{u} B)).mapIso
          (simpKerLiftIso (koszulTermd B ι 0 0) (koszulAug B W π 1) (hzero 0)
            (haugex 0) (hinj 0)))).symm
  · exact (homologyIsoKerSurj (koszulAug B W π (q + 2)) (haugsurj (q + 2))
      (hac 0 (q + 1)) (q + 1)).trans
      ((homologyIsoKerPair (koszulTermd B ι 0 (q + 1)) (koszulAug B W π (q + 2))
        (hzero (q + 1)) (haugex (q + 1)) (hac 1 q) q).trans
        (homologyIsoKoszulCycles B ι hex hinj hac q 0 0 q (q + 2) (by omega) (by omega)))

/-- **The décalage shift for an abstract covering.** Let `0 → W → D → Y → 0` be a degreewise
short exact sequence of degreewise flat simplicial modules with `D` simplicially
null-homotopic. Then `H_{k+1}(Symᵏ⁺¹Y) ≅ H₀(⋀ᵏ⁺¹W)`: the relative Koszul complex of `W ⊆ D`
resolves `Symᵏ⁺¹Y` by terms that are acyclic except for the top one `⋀ᵏ⁺¹W ⊗ Sym⁰D`, and `k + 1`
dimension shifts land on it. -/
public def homologyIsoSymPowOfCovering (B : Type u) [CommRing B]
    {W D Y : SimplicialObject (ModuleCat.{u} B)} (ι : W ⟶ D) (π : D ⟶ Y)
    (hW : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (W.obj n))
    (hD : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (D.obj n))
    (hYf : ∀ n : SimplexCategoryᵒᵖ, Module.Flat B (Y.obj n))
    (hmono : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (ι.app n).hom)
    (hpair : ∀ n : SimplexCategoryᵒᵖ, Function.Exact (ι.app n).hom (π.app n).hom)
    (hepi : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (π.app n).hom)
    (hDnull : SimplicialObject.Homotopy (0 : D ⟶ D) (𝟙 D)) (k : ℕ) :
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (Y ⋙ Stacks.ModuleCat.symPowFunctor B (k + 1))).homology (k + 1) ≅
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (W ⋙ Stacks.ModuleCat.extPowFunctor B (k + 1))).homology 0 :=
  (homologyIsoSymPowKoszul B ι π
      (koszulTermd_exact_app B ι π hW hD hYf hmono hpair hepi)
      (koszulTermd_injective_app B ι π hW hD hYf hmono hpair hepi)
      (koszulAug_exact_app B ι π hW hD hYf hpair hepi)
      (koszulAug_surjective_app B W π hepi)
      (fun p q n => isZero_homology_koszulTerm B W hDnull p q n) k).trans
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) _ 0).mapIso
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).mapIso (koszulTermTopIso B W D (k + 1))))

/-! ### The décalage identity -/

/-- **The décalage identity for symmetric powers.** Let `B` be a commutative ring — with no
hypothesis at all, in particular `2` need not be invertible — and let `Y` be a simplicial
`B`-module which is degreewise flat and whose Moore complex has vanishing homology in degree
zero. Then for every `k` the degree-`k` homology of the Moore complex of the degreewise `k`-th
symmetric power of `Y` is the `k`-th exterior power of the degree-one homology of `Y`:

`H_k(Symᵏ Y) ≅ ⋀ᵏ_B (H₁ Y)`.

The proof is Illusie's and Quillen's décalage, run over the relative Koszul resolution of
`Symᵏ Y` by the terms `⋀ᵖ W ⊗ Symᵏ⁻ᵖ D` attached to the reduced décalage `D = decRed Y` and
`W = ker(D → Y)`; see the module docstring. Taking `k > l` in the same argument reproves the
vanishing `H_l(Symᵏ Y) = 0` of Tag 08RD. -/
public theorem nonempty_linearEquiv_homology_symPow
    (B : Type u) [CommRing B] (Y : CategoryTheory.SimplicialObject (ModuleCat.{u} B))
    (hY : ∀ n, Module.Flat B (Y.obj n))
    (h₀ : CategoryTheory.Limits.IsZero
      (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} B)).obj Y).homology 0))
    (k : ℕ) :
    Nonempty ((((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (Y ⋙ Stacks.ModuleCat.symPowFunctor B k)).homology k : ModuleCat.{u} B) ≃ₗ[B]
      ⋀[B]^k (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        Y).homology 1 : ModuleCat.{u} B)) := by
  rcases k with _ | k
  · obtain ⟨e⟩ := nonempty_linearEquiv_homologyZero_extPowFunctor B Y 0
    exact ⟨(((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) _ 0).mapIso
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).mapIso
        (symPowZeroIsoExtPowZero B Y))).toLinearEquiv.trans e).trans
      ((exteriorPower.zeroEquiv B _).trans (exteriorPower.zeroEquiv B _).symm)⟩
  · have hWY : ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj Y).homology 1 ≅
        ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
          (simpKer (decRedδ₀ Y))).homology 0 :=
      homologyIsoOfShortExactOfAcyclic (decRedShortComplex Y)
        (decRedShortComplex_shortExact Y h₀) (isZero_homology_decRed' Y) 0
    obtain ⟨e⟩ := nonempty_linearEquiv_homologyZero_extPowFunctor B
      (simpKer (decRedδ₀ Y)) (k + 1)
    have hmain := homologyIsoSymPowOfCovering B (simpKerι (decRedδ₀ Y)) (decRedδ₀ Y)
      (flat_decRedKer Y hY h₀) (flat_decRed Y hY) hY
      (fun n => (LinearMap.ker ((decRedδ₀ Y).app n).hom).injective_subtype)
      (fun n => LinearMap.exact_subtype_ker_map ((decRedδ₀ Y).app n).hom)
      (fun n => decRedδ₀_app_surjective Y h₀ n.unop.len)
      (decRedNullHomotopy Y) k
    exact ⟨(hmain.toLinearEquiv.trans e).trans
      (exteriorPowerCongr hWY.toLinearEquiv.symm (k + 1))⟩

end Stacks.ChaoticSite

end
