module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorizationGlue
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison
public import StacksFrontier.RingTheory.SymmetricAlgebra.AugmentationIdeal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sheaf of the zero section of an affine bundle

Let `A` be a commutative ring, let `K` be an `A`-module and write `C = Sym_A(K)`. The augmentation
`aug = SymmetricAlgebra.algebraMapInv : C →ₐ[A] A` is a retraction of `algebraMap A C`, hence
surjective, and its kernel is the augmentation ideal `I = SymmetricAlgebra.augIdeal A K`.
Geometrically `Spec C` is the affine bundle `𝐀(K)` over `Spec A` and `σ = Spec aug` is its zero
section, a closed immersion. This file identifies the conormal sheaf of `σ` with the
quasi-coherent sheaf `K^~` attached to `K`.

The statement is proved in two steps.

* An affine model for an arbitrary surjection `φ : R ⟶ S` of commutative rings: the ideal sheaf
  of `Spec φ` is `(ker φ)^~` and its conormal sheaf is the sheaf associated to `S ⊗_R ker φ`. This
  is the case of `Spec (R ⧸ J) ⟶ Spec R`, transported along the isomorphism square that factors
  `Spec φ` through the quotient.
* The algebraic computation `A ⊗_C I ≅ K`, the base-change form of
  `SymmetricAlgebra.augCotangentEquiv`: the two maps are the derivative at the origin
  `SymmetricAlgebra.augDeriv` and `k ↦ 1 ⊗ ι_A K k`.

This is the affine local model of the conormal sheaf of a section of a projective bundle.

## Main definitions

* `SymmetricAlgebra.augIdeal_quotientEquiv`: the quotient of `Sym_R(M)` by its augmentation ideal
  is `R`, through the augmentation.
* `Stacks.ProjectiveBundleConormal.augExtendScalarsIso`: the base change `A ⊗_C I ≅ K`.
* `Stacks.ClosedImmersion.AffineConormal.surjIdealSheafIso` and
  `Stacks.ClosedImmersion.AffineConormal.surjConormalBaseChangeIso`: the ideal sheaf and the
  conormal sheaf of `Spec φ` for a surjection `φ`.
* `Stacks.ProjectiveBundleConormal.zeroSection`: the zero section of the affine bundle.
* `Stacks.ProjectiveBundleConormal.conormalZeroSectionTildeIso` and
  `Stacks.ProjectiveBundleConormal.conormalZeroSectionIso`: the conormal sheaf of the zero
  section is `K^~`, for the ringed-space conormal sheaf and for `Stacks.Conormal.conormalSheaf`
  respectively.

## Main results

* `SymmetricAlgebra.augDeriv_mul_of_mem`: the Leibniz rule for the derivative at the origin on the
  augmentation ideal.
* `SymmetricAlgebra.sub_ι_augDeriv_mem_sq`: every element of the augmentation ideal is `ι` of its
  derivative modulo `I²`.
* `SymmetricAlgebra.augIdeal_quotientEquiv_symm_smul`: the `Sym_R(M) ⧸ I`-action on the cotangent
  module, read through the identification of `Sym_R(M) ⧸ I` with `R`, is its `R`-action.
* `Stacks.ClosedImmersion.AffineConormal.surjIdealSheafIso_hom_comp_idealSheafι` and
  `Stacks.ProjectiveBundleConormal.zeroSectionIdealSheafIso_hom_comp_idealSheafι`: the ideal
  sheaf identifications are compatible with the inclusions into the structure sheaf.
* `Stacks.ProjectiveBundleConormal.isClosedImmersion_zeroSection`: the zero section is a closed
  immersion.
* `Stacks.ProjectiveBundleConormal.conormalSheafIsoPullbackSelf_symm_trans_conormalZeroSectionIso`:
  `conormalZeroSectionIso` preceded by the inverse of
  `Stacks.CartierConormal.conormalSheafIsoPullbackSelf` is `conormalZeroSectionTildeIso`.

## Implementation notes

The module-level computation `A ⊗_C I ≅ K` is done inside `ModuleCat.extendScalars`, whose objects
carry a `Module` instance that type-class search cannot rediscover on the bare tensor product. The
forward map is the transpose of `Stacks.ProjectiveBundleConormal.augDerivRestrict` under
`ModuleCat.extendRestrictScalarsAdj`; the backward map is built with
`CategoryTheory.ConcreteCategory.ofHom`, which takes the two objects rather than two carrier
types; and the `Sym_A(K)`-module structure on `A` is reintroduced locally inside the proofs that
move a scalar across the tensor product.

`Stacks.ClosedImmersion.AffineConormal.surjIdealSheafIso` is defined as the `Exists.choose` of
`Stacks.ClosedImmersion.AffineConormal.exists_surjIdealSheafIso`, which asserts its compatibility
with the inclusion of the ideal sheaf into the structure sheaf. Stated about the explicit composite
`tildeIdealSheafIso R (ker φ) ≪≫ idealSheafQuotIso φ hφ`, that compatibility is a kernel
deterministic timeout. Since `idealSheafι` is a monomorphism, the compatibility determines the
isomorphism.

The affine model is stated for a surjection `φ : R ⟶ S` with `R`, `S` and `φ` variables, so that
its instantiation at the augmentation is a single application and never unfolds `Sym_A(K)`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine

universe u v

namespace SymmetricAlgebra

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- **The augmentation is surjective**: it is a retraction of `algebraMap R (Sym_R M)`. -/
theorem algebraMapInv_surjective :
    Function.Surjective (algebraMapInv (R := R) (M := M)) :=
  (algebraMap_leftInverse M).surjective

/-- **The quotient of `Sym_R(M)` by its augmentation ideal is `R`**, through the augmentation. -/
def augIdeal_quotientEquiv : (SymmetricAlgebra R M ⧸ augIdeal R M) ≃ₐ[R] R :=
  Ideal.quotientKerAlgEquivOfSurjective (algebraMapInv_surjective R M)

variable {R M}

/-- `SymmetricAlgebra.augIdeal_quotientEquiv` is the augmentation on classes of elements. -/
theorem augIdeal_quotientEquiv_mk (x : SymmetricAlgebra R M) :
    augIdeal_quotientEquiv R M (Ideal.Quotient.mk (augIdeal R M) x) = algebraMapInv x := rfl

/-- The inverse of `SymmetricAlgebra.augIdeal_quotientEquiv` is the class of the structure
map. -/
theorem augIdeal_quotientEquiv_symm_apply (r : R) :
    (augIdeal_quotientEquiv R M).symm r
      = Ideal.Quotient.mk (augIdeal R M) (algebraMap R (SymmetricAlgebra R M) r) :=
  (((augIdeal_quotientEquiv R M).eq_symm_apply).2
    ((augIdeal_quotientEquiv_mk _).trans (algebraMap_leftInverse M r))).symm

/-- **The `R`-module structure on the cotangent module read through
`SymmetricAlgebra.augIdeal_quotientEquiv`.** The cotangent module `I/I²` of the augmentation
ideal is a module over `Sym_R(M) ⧸ I`, and that action, transported along the identification of
`Sym_R(M) ⧸ I` with `R`, is the `R`-action it already carries. -/
theorem augIdeal_quotientEquiv_symm_smul (r : R) (c : (augIdeal R M).Cotangent) :
    (augIdeal_quotientEquiv R M).symm r • c = r • c := by
  have h1 : Ideal.Quotient.mk (augIdeal R M) (algebraMap R (SymmetricAlgebra R M) r) • c
      = algebraMap R (SymmetricAlgebra R M) r • c :=
    algebraMap_smul (SymmetricAlgebra R M ⧸ augIdeal R M) _ c
  rw [augIdeal_quotientEquiv_symm_apply, h1, algebraMap_smul]

/-- **The Leibniz rule for the derivative at the origin, on the augmentation ideal.** For `y` in
the augmentation ideal the derivative of `c * y` is the derivative of `y` scaled by the value of
the augmentation at `c`. -/
theorem augDeriv_mul_of_mem (c : SymmetricAlgebra R M) {y : SymmetricAlgebra R M}
    (hy : y ∈ augIdeal R M) : augDeriv (c * y) = algebraMapInv c • augDeriv y := by
  let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  set ψ : SymmetricAlgebra R M →ₐ[R] TrivSqZeroExt R M :=
    SymmetricAlgebra.lift (TrivSqZeroExt.inrHom R M) with hψ
  have hsnd : ∀ z : SymmetricAlgebra R M, augDeriv z = (ψ z).snd := fun _ => rfl
  have hfst : ∀ z : SymmetricAlgebra R M, (ψ z).fst = algebraMapInv z := by
    have key : (TrivSqZeroExt.fstHom R R M).comp ψ = algebraMapInv := by
      refine algHom_ext (LinearMap.ext fun m => ?_)
      simp [hψ, algebraMapInv_ι]
    exact fun z => congr($key z)
  rw [hsnd, map_mul, TrivSqZeroExt.snd_mul, hfst c, hfst y, mem_augIdeal_iff.mp hy, ← hsnd y]
  simp

/-- **Every element of the augmentation ideal is `ι` of its derivative, modulo `I²`.** -/
theorem sub_ι_augDeriv_mem_sq {y : SymmetricAlgebra R M} (hy : y ∈ augIdeal R M) :
    y - ι R M (augDeriv y) ∈ augIdeal R M ^ 2 := by
  obtain ⟨m, hm⟩ :=
    augToCotangent_surjective (R := R) (M := M) ((augIdeal R M).toCotangent ⟨y, hy⟩)
  have h2 : (ι R M m - y : SymmetricAlgebra R M) ∈ augIdeal R M ^ 2 := by
    simpa using (Ideal.toCotangent_eq (augIdeal R M)).mp
      ((augToCotangent_apply (R := R) (M := M) m).symm.trans hm)
  have h3 : augDeriv (R := R) (M := M) y = m := by
    have h4 := augDeriv_eq_zero_of_mem_sq h2
    rw [map_sub, augDeriv_ι, sub_eq_zero] at h4
    exact h4.symm
  rw [h3, ← neg_sub (ι R M m) y]
  exact neg_mem h2

end SymmetricAlgebra

namespace Stacks.ClosedImmersion.AffineConormal

open scoped ChangeOfRings

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : Function.Surjective φ.hom)

/-- **The first isomorphism theorem in `CommRingCat`**: for a surjection `φ : R ⟶ S` the quotient
of `R` by the kernel of `φ` is `S`. -/
def quotKerRingIso : quotRing (RingHom.ker φ.hom) ≅ S :=
  (RingHom.quotientKerEquivOfSurjective hφ).toCommRingCatIso

/-- The factorization of a surjection through its kernel quotient. -/
theorem quotHom_comp_quotKerRingIso :
    quotHom (RingHom.ker φ.hom) ≫ (quotKerRingIso φ hφ).hom = φ :=
  CommRingCat.hom_ext (RingHom.ext fun x =>
    RingHom.quotientKerEquivOfSurjective_apply_mk hφ x)

/-- **`Spec S ≅ Spec (R ⧸ ker φ)`** for a surjection `φ : R ⟶ S`, the image under `Spec` of
`Stacks.ClosedImmersion.AffineConormal.quotKerRingIso`. -/
def specQuotKerIso : Spec S ≅ Spec (quotRing (RingHom.ker φ.hom)) where
  hom := Spec.map (quotKerRingIso φ hφ).hom
  inv := Spec.map (quotKerRingIso φ hφ).inv
  hom_inv_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  inv_hom_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]

/-- **`Spec φ` factors through the quotient immersion**, through the isomorphism
`Stacks.ClosedImmersion.AffineConormal.specQuotKerIso`. -/
theorem specMap_eq_specQuotKerIso_comp :
    Spec.map φ = (specQuotKerIso φ hφ).hom ≫ quotImmersion R (RingHom.ker φ.hom) := by
  show Spec.map φ
    = Spec.map (quotKerRingIso φ hφ).hom ≫ Spec.map (quotHom (RingHom.ker φ.hom))
  rw [← Spec.map_comp]
  exact (congrArg (fun f : R ⟶ S => Spec.map f) (quotHom_comp_quotKerRingIso φ hφ)).symm

/-- `Stacks.ClosedImmersion.AffineConormal.specMap_eq_specQuotKerIso_comp` on the underlying
ringed spaces. -/
theorem specMap_toShHom_eq :
    (Spec.map φ).toLRSHom.toShHom
      = (RingedSpace.ringedSpaceIso (specQuotKerIso φ hφ)).hom ≫
        (quotImmersion R (RingHom.ker φ.hom)).toLRSHom.toShHom :=
  congrArg (fun g : Spec S ⟶ Spec R => g.toLRSHom.toShHom)
    (specMap_eq_specQuotKerIso_comp φ hφ)

/-- **The ideal sheaf of `Spec (R ⧸ ker φ) ⟶ Spec R` is the ideal sheaf of `Spec φ`.** -/
def idealSheafQuotIso :
    idealSheaf (quotImmersion R (RingHom.ker φ.hom)).toLRSHom.toShHom ≅
      idealSheaf (Spec.map φ).toLRSHom.toShHom :=
  (idealSheafCompIsoOfIso (RingedSpace.ringedSpaceIso (specQuotKerIso φ hφ))
      (quotImmersion R (RingHom.ker φ.hom)).toLRSHom.toShHom).symm ≪≫
    (eqToIso (congrArg idealSheaf (specMap_toShHom_eq φ hφ))).symm

include hφ in
/-- **The ideal sheaf of `Spec φ` is `(ker φ)^~`, compatibly with the two inclusions into
`𝒪_{Spec R}`**, for a surjection `φ : R ⟶ S` of rings. -/
theorem exists_surjIdealSheafIso :
    ∃ Φ : tilde (ModuleCat.of R (RingHom.ker φ.hom)) ≅
        idealSheaf (Spec.map φ).toLRSHom.toShHom,
      Φ.hom ≫ idealSheafι (Spec.map φ).toLRSHom.toShHom =
        tilde.map (ModuleCat.ofHom (RingHom.ker φ.hom).subtype) ≫ tildeSelf.hom := by
  obtain ⟨Φ, hΦ⟩ := Stacks.ClosedImmersion.exists_idealSheafIso_hom_comp_ι
    (RingedSpace.ringedSpaceIso (specQuotKerIso φ hφ))
    (quotImmersion R (RingHom.ker φ.hom)).toLRSHom.toShHom
    (Spec.map φ).toLRSHom.toShHom (specMap_toShHom_eq φ hφ)
  refine ⟨tildeIdealSheafIso R (RingHom.ker φ.hom) ≪≫ Φ, ?_⟩
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun z => (tildeIdealSheafIso R (RingHom.ker φ.hom)).hom ≫ z) hΦ) ?_
  exact tildeIdealSheafIso_hom_comp_idealSheafι R (RingHom.ker φ.hom)

/-- **The ideal sheaf of `Spec φ` is `(ker φ)^~`**, for a surjection `φ : R ⟶ S` of rings: an
isomorphism compatible with the inclusions into `𝒪_{Spec R}`, by
`Stacks.ClosedImmersion.AffineConormal.surjIdealSheafIso_hom_comp_idealSheafι`. -/
def surjIdealSheafIso :
    tilde (ModuleCat.of R (RingHom.ker φ.hom)) ≅ idealSheaf (Spec.map φ).toLRSHom.toShHom :=
  (exists_surjIdealSheafIso φ hφ).choose

/-- **The normalisation of `Stacks.ClosedImmersion.AffineConormal.surjIdealSheafIso` against the
inclusion of the ideal sheaf into the structure sheaf**: it carries that inclusion to the
sheafification of the inclusion `ker φ ⟶ R`. -/
theorem surjIdealSheafIso_hom_comp_idealSheafι :
    (surjIdealSheafIso φ hφ).hom ≫ idealSheafι (Spec.map φ).toLRSHom.toShHom =
      tilde.map (ModuleCat.ofHom (RingHom.ker φ.hom).subtype) ≫ tildeSelf.hom :=
  (exists_surjIdealSheafIso φ hφ).choose_spec

/-- **The conormal sheaf of `Spec φ` for a surjection `φ : R ⟶ S`.** It is the sheaf on `Spec S`
associated to the `S`-module `S ⊗_R ker φ`. -/
def surjConormalBaseChangeIso :
    conormalSheaf (Spec.map φ).toLRSHom.toShHom ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj (ModuleCat.of R (RingHom.ker φ.hom))) :=
  (Scheme.Modules.pullback (Spec.map φ)).mapIso (surjIdealSheafIso φ hφ).symm ≪≫
    (pullbackTildeIso R S φ).app (ModuleCat.of R (RingHom.ker φ.hom))

end Stacks.ClosedImmersion.AffineConormal

namespace Stacks.ProjectiveBundleConormal

open SymmetricAlgebra
open scoped ChangeOfRings

variable (A K : Type u) [CommRing A] [AddCommGroup K] [Module A K]

/-- The symmetric algebra `Sym_A(K)`, whose spectrum is the affine bundle `𝐀(K)`, as an object of
`CommRingCat`. -/
abbrev symRing : CommRingCat.{u} := CommRingCat.of (SymmetricAlgebra A K)

/-- The augmentation `Sym_A(K) ⟶ A` as a morphism of `CommRingCat`. Its spectrum is the zero
section of the affine bundle. -/
abbrev augRingHom : symRing A K ⟶ CommRingCat.of A :=
  CommRingCat.ofHom (algebraMapInv (R := A) (M := K)).toRingHom

/-- The augmentation ideal, as an ideal of `Stacks.ProjectiveBundleConormal.symRing`. -/
abbrev augIdealOf : Ideal (symRing A K) := augIdeal A K

/-- The augmentation ideal as a `Sym_A(K)`-module. -/
abbrev augIdealModule : ModuleCat.{u} (symRing A K) :=
  ModuleCat.of (symRing A K) (augIdealOf A K)

/-- **The derivative at the origin, restricted to the augmentation ideal**, as a `Sym_A(K)`-linear
map into `K` with its scalars restricted along the augmentation. -/
def augDerivRestrict :
    augIdealModule A K ⟶
      (ModuleCat.restrictScalars (augRingHom A K).hom).obj (ModuleCat.of (CommRingCat.of A) K) :=
  ModuleCat.ofHom (X := augIdealModule A K)
    (Y := (ModuleCat.restrictScalars (augRingHom A K).hom).obj (ModuleCat.of (CommRingCat.of A) K))
    { toFun := fun x => augDeriv (x : SymmetricAlgebra A K)
      map_add' := fun _ _ => map_add augDeriv _ _
      map_smul' := fun c x => augDeriv_mul_of_mem c x.2 }

/-- **The `A`-linear map `K ⟶ A ⊗_{Sym_A(K)} I` sending `k` to `1 ⊗ ι k`.** -/
def augTmul :
    ModuleCat.of (CommRingCat.of A) K ⟶
      (ModuleCat.extendScalars (augRingHom A K).hom).obj (augIdealModule A K) :=
  ConcreteCategory.ofHom (C := ModuleCat.{u} (CommRingCat.of A))
    { toFun := fun k => (1 : A) ⊗ₜ[SymmetricAlgebra A K, (augRingHom A K).hom]
        (⟨ι A K k, ι_mem_augIdeal k⟩ : augIdealOf A K)
      map_add' := fun k k' => by
        rw [show (⟨ι A K (k + k'), ι_mem_augIdeal _⟩ : augIdealOf A K)
            = ⟨ι A K k, ι_mem_augIdeal k⟩ + ⟨ι A K k', ι_mem_augIdeal k'⟩ from
          Subtype.ext (map_add (ι A K) k k')]
        exact TensorProduct.tmul_add _ _ _
      map_smul' := fun a k => by
        let : Module (SymmetricAlgebra A K) A := Module.compHom A (augRingHom A K).hom
        have h : (⟨ι A K (a • k), ι_mem_augIdeal _⟩ : augIdealOf A K)
            = algebraMap A (SymmetricAlgebra A K) a • ⟨ι A K k, ι_mem_augIdeal k⟩ :=
          Subtype.ext (by simp [Algebra.smul_def])
        have hscal : (algebraMap A (SymmetricAlgebra A K) a) • (1 : A) = a * 1 := by
          change algebraMapInv (algebraMap A (SymmetricAlgebra A K) a) * (1 : A) = a * 1
          rw [algebraMap_leftInverse]
        exact ((congrArg (fun z : augIdealOf A K =>
              (1 : A) ⊗ₜ[SymmetricAlgebra A K, (augRingHom A K).hom] z) h).trans
            (TensorProduct.smul_tmul _ _ _).symm).trans
          (congrArg (fun s : A => s ⊗ₜ[SymmetricAlgebra A K, (augRingHom A K).hom]
            (⟨ι A K k, ι_mem_augIdeal k⟩ : augIdealOf A K)) hscal) }

/-- **The `A`-linear map `A ⊗_{Sym_A(K)} I ⟶ K` extending the derivative at the origin**, the
transpose of `Stacks.ProjectiveBundleConormal.augDerivRestrict` under extension-restriction of
scalars. -/
def augExtendHom :
    (ModuleCat.extendScalars (augRingHom A K).hom).obj (augIdealModule A K) ⟶
      ModuleCat.of (CommRingCat.of A) K :=
  ((ModuleCat.extendRestrictScalarsAdj (augRingHom A K).hom).homEquiv
    (augIdealModule A K) (ModuleCat.of (CommRingCat.of A) K)).symm (augDerivRestrict A K)

/-- `Stacks.ProjectiveBundleConormal.augExtendHom` sends the generator `1 ⊗ z` to the derivative
of `z` at the origin. -/
theorem augExtendHom_one_tmul (z : augIdealOf A K) :
    (augExtendHom A K).hom ((1 : A) ⊗ₜ[SymmetricAlgebra A K, (augRingHom A K).hom] z)
      = augDeriv (z : SymmetricAlgebra A K) := by
  have h := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply (augExtendHom A K) z
  rw [augExtendHom, Equiv.apply_symm_apply] at h
  exact h.symm

/-- **The base change kills `I²`**: `1 ⊗ z = 0` for `z` in the augmentation ideal lying in
`I²`. -/
theorem one_tmul_eq_zero_of_mem_sq (z : augIdealOf A K)
    (hz : (z : SymmetricAlgebra A K) ∈ augIdeal A K ^ 2) :
    (1 : A) ⊗ₜ[SymmetricAlgebra A K, (augRingHom A K).hom] z = 0 := by
  let : Module (SymmetricAlgebra A K) A := Module.compHom A (augRingHom A K).hom
  have hz' : z ∈ (augIdealOf A K) • (⊤ : Submodule (symRing A K) (augIdealOf A K)) :=
    (Submodule.Quotient.mk_eq_zero _).mp
      ((Ideal.toCotangent_eq_zero (augIdealOf A K) z).mpr hz)
  refine Submodule.smul_induction_on hz' (fun c hc x _ => ?_) (fun x y hx hy => ?_)
  · have hc0 : c • (1 : A) = 0 := by
      show algebraMapInv c * (1 : A) = 0
      rw [mem_augIdeal_iff.mp hc, zero_mul]
    exact ((TensorProduct.smul_tmul c (1 : A) x).symm.trans
        (congrArg (fun s : A => s ⊗ₜ[SymmetricAlgebra A K, (augRingHom A K).hom] x) hc0)).trans
      (TensorProduct.zero_tmul _ _)
  · exact (TensorProduct.tmul_add _ _ _).trans (by rw [hx, hy, add_zero])

/-- Every generator `1 ⊗ z` of the base change is `1 ⊗ ι (augDeriv z)`. -/
theorem one_tmul_ι_augDeriv (z : augIdealOf A K) :
    (1 : A) ⊗ₜ[SymmetricAlgebra A K, (augRingHom A K).hom]
        (⟨ι A K (augDeriv (z : SymmetricAlgebra A K)), ι_mem_augIdeal _⟩ : augIdealOf A K)
      = (1 : A) ⊗ₜ[SymmetricAlgebra A K, (augRingHom A K).hom] z := by
  let : Module (SymmetricAlgebra A K) A := Module.compHom A (augRingHom A K).hom
  have hsq : (((⟨ι A K (augDeriv (z : SymmetricAlgebra A K)), ι_mem_augIdeal _⟩ :
      augIdealOf A K) - z : augIdealOf A K) : SymmetricAlgebra A K) ∈ augIdeal A K ^ 2 := by
    simpa using neg_mem (sub_ι_augDeriv_mem_sq (R := A) (M := K) z.2)
  have h0 := one_tmul_eq_zero_of_mem_sq A K _ hsq
  exact sub_eq_zero.mp ((TensorProduct.tmul_sub _ _ _).symm.trans h0)

/-- **`A ⊗_{Sym_A(K)} I ≅ K`**: the base change of the augmentation ideal along the augmentation
is `K` itself, through the derivative at the origin and `k ↦ 1 ⊗ ι k`. -/
def augExtendScalarsIso :
    (ModuleCat.extendScalars (augRingHom A K).hom).obj (augIdealModule A K)
      ≅ ModuleCat.of (CommRingCat.of A) K where
  hom := augExtendHom A K
  inv := augTmul A K
  hom_inv_id := ModuleCat.ExtendScalars.hom_ext fun z =>
    (congrArg (fun k : K => (augTmul A K).hom k) (augExtendHom_one_tmul A K z)).trans
      (one_tmul_ι_augDeriv A K z)
  inv_hom_id := ModuleCat.hom_ext (LinearMap.ext fun k =>
    (augExtendHom_one_tmul A K _).trans (augDeriv_ι k))

/-! ### The zero section of the affine bundle -/

/-- **The zero section** `Spec A ⟶ Spec (Sym_A K)` of the affine bundle `𝐀(K) = Spec (Sym_A K)`:
the spectrum of the augmentation. -/
abbrev zeroSection : Spec (CommRingCat.of A) ⟶ Spec (symRing A K) := Spec.map (augRingHom A K)

/-- **The zero section is a closed immersion.** -/
instance isClosedImmersion_zeroSection : IsClosedImmersion (zeroSection A K) :=
  IsClosedImmersion.spec_of_surjective _ (algebraMapInv_surjective A K)

/-- The kernel of the augmentation is the augmentation ideal, on the nose. -/
theorem ker_augRingHom : RingHom.ker (augRingHom A K).hom = augIdealOf A K := rfl

/-- **`I^~` is the ideal sheaf of the zero section.** -/
@[ega "II 8.9.3" "affine case"]
def zeroSectionIdealSheafIso :
    tilde (augIdealModule A K) ≅ idealSheaf (zeroSection A K).toLRSHom.toShHom :=
  surjIdealSheafIso (augRingHom A K) (algebraMapInv_surjective A K)

/-- **The normalisation of `Stacks.ProjectiveBundleConormal.zeroSectionIdealSheafIso` against the
inclusion of the ideal sheaf into the structure sheaf of `𝐀(K)`**: it carries that inclusion to
the sheafification of the inclusion `I ⟶ Sym_A(K)` of the augmentation ideal. -/
@[ega "II 8.9.3" "affine case"]
theorem zeroSectionIdealSheafIso_hom_comp_idealSheafι :
    (zeroSectionIdealSheafIso A K).hom ≫ idealSheafι (zeroSection A K).toLRSHom.toShHom =
      tilde.map (ModuleCat.ofHom (augIdealOf A K).subtype) ≫ tildeSelf.hom :=
  surjIdealSheafIso_hom_comp_idealSheafι (augRingHom A K) (algebraMapInv_surjective A K)

/-- **The conormal sheaf of the zero section, in base-change form**: the sheaf on `Spec A`
associated to `A ⊗_{Sym_A K} I`. -/
def conormalZeroSectionBaseChangeIso :
    conormalSheaf (zeroSection A K).toLRSHom.toShHom ≅
      tilde ((ModuleCat.extendScalars (augRingHom A K).hom).obj (augIdealModule A K)) :=
  surjConormalBaseChangeIso (augRingHom A K) (algebraMapInv_surjective A K)

/-- **The conormal sheaf of the zero section of the affine bundle `𝐀(K)` is `K`**, stated for the
ringed-space conormal sheaf of the zero section. -/
@[ega "II 8.9.3" "special case"]
def conormalZeroSectionTildeIso :
    conormalSheaf (zeroSection A K).toLRSHom.toShHom ≅
      tilde (ModuleCat.of (CommRingCat.of A) K) :=
  conormalZeroSectionBaseChangeIso A K ≪≫
    (tilde.functor (CommRingCat.of A)).mapIso (augExtendScalarsIso A K)

/-- **The conormal sheaf of the zero section of the affine bundle `𝐀(K)` is `K`.** -/
@[ega "II 8.9.3" "special case"]
def conormalZeroSectionIso :
    Stacks.Conormal.conormalSheaf (zeroSection A K) ≅
      tilde (ModuleCat.of (CommRingCat.of A) K) :=
  (Stacks.Immersion.conormalSheafSelfIso (zeroSection A K)).symm ≪≫
    conormalZeroSectionTildeIso A K

/-- `Stacks.ProjectiveBundleConormal.conormalZeroSectionIso` preceded by the inverse of
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf` is
`Stacks.ProjectiveBundleConormal.conormalZeroSectionTildeIso`. -/
theorem conormalSheafIsoPullbackSelf_symm_trans_conormalZeroSectionIso :
    (Stacks.CartierConormal.conormalSheafIsoPullbackSelf (zeroSection A K)).symm ≪≫
        conormalZeroSectionIso A K =
      conormalZeroSectionTildeIso A K :=
  Stacks.Immersion.conormalSheafIsoPullbackSelf_symm_trans_conormalSheafSelfIso_symm_trans
    (zeroSection A K) (conormalZeroSectionTildeIso A K)

end Stacks.ProjectiveBundleConormal

end
