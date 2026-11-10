module

public import StacksFrontier.Algebra.Module.Projective.Determinant.BaseChange
public import Mathlib.RingTheory.IsTensorProduct

/-!
# The determinant line along a base change

Let `R → S` be a homomorphism of commutative rings, `M` a finite projective `R`-module and `N` a
finite projective `S`-module. An `R`-linear map `φ : M → N` whose image spans `N` over `S`
induces an `R`-algebra map of exterior algebras `⋀_R M → ⋀_S N`, and this map carries the
determinant line of `M` into the determinant line of `N`. When `φ` exhibits `N` as the base change
`S ⊗_R M`, the induced map of determinant lines exhibits `det N` as the base change
`S ⊗_R det M`.

## Main definitions

* `ProjectiveDeterminant.exteriorMap`: the map of exterior algebras induced by `φ`.
* `ProjectiveDeterminant.detMap`: the induced map `det M → det N`.

## Main results

* `ProjectiveDeterminant.isBaseChange_detMap`: if `φ` is a base change, so is `detMap φ`.
* `ProjectiveDeterminant.detMap_comp`: the construction is compatible with composition along a
  tower `R → S → T`.
* `ProjectiveDeterminant.rankAtStalk_of_isBaseChange`: a base change has the rank of its source
  at the prime below.
-/

@[expose] public noncomputable section

universe u v w x

open TensorProduct

namespace ProjectiveDeterminant

section ExteriorMap

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- The `R`-algebra map of exterior algebras `⋀_R M → ⋀_S N` induced by an `R`-linear map
`φ : M → N` into an `S`-module. -/
def exteriorMap (φ : M →ₗ[R] N) : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra S N :=
  ExteriorAlgebra.lift R
    ⟨((ExteriorAlgebra.ι S : N →ₗ[S] ExteriorAlgebra S N).restrictScalars R).comp φ,
    fun m => ExteriorAlgebra.ι_sq_zero (φ m)⟩

/-- On a degree-one element, the induced map of exterior algebras is `φ`. -/
@[simp]
theorem exteriorMap_ι (φ : M →ₗ[R] N) (m : M) :
    exteriorMap (S := S) φ (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι S (φ m) :=
  ExteriorAlgebra.lift_ι_apply R _ _ m

/-- Precomposing with the exterior algebra map of an `R`-linear map. -/
theorem exteriorMap_map {M₂ : Type x} [AddCommGroup M₂] [Module R M₂] (φ : M →ₗ[R] N)
    (h : M₂ →ₗ[R] M) (y : ExteriorAlgebra R M₂) :
    exteriorMap (S := S) φ (ExteriorAlgebra.map h y) = exteriorMap (S := S) (φ.comp h) y := by
  have : (exteriorMap (S := S) φ).comp (ExteriorAlgebra.map h) = exteriorMap (S := S) (φ.comp h) :=
    ExteriorAlgebra.hom_ext (LinearMap.ext fun m => by simp)
  exact congrArg (fun F : ExteriorAlgebra R M₂ →ₐ[R] ExteriorAlgebra S N => F y) this

/-- Postcomposing with the exterior algebra map of an `S`-linear map. -/
theorem map_exteriorMap {N₂ : Type x} [AddCommGroup N₂] [Module R N₂] [Module S N₂]
    [IsScalarTower R S N₂] (φ : M →ₗ[R] N) (g : N →ₗ[S] N₂) (y : ExteriorAlgebra R M) :
    ExteriorAlgebra.map g (exteriorMap (S := S) φ y) =
      exteriorMap (S := S) ((g.restrictScalars R).comp φ) y := by
  have : ((ExteriorAlgebra.map g).restrictScalars R).comp (exteriorMap (S := S) φ) =
      exteriorMap (S := S) ((g.restrictScalars R).comp φ) :=
    ExteriorAlgebra.hom_ext (LinearMap.ext fun m => by simp)
  exact congrArg (fun F : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra S N₂ => F y) this

variable [Module.Finite R M] [Module.Projective R M] [Module.Finite S N] [Module.Projective S N]

/-- The exterior algebra map induced by a map whose image spans carries the determinant line into
the determinant line: the determinant line is the annihilator of the degree-one elements, and the
degree-one elements of `⋀_S N` are `S`-combinations of images of degree-one elements of
`⋀_R M`. -/
theorem exteriorMap_mem_submodule (φ : M →ₗ[R] N)
    (hφ : Submodule.span S (Set.range φ) = ⊤) (x : module (R := R) (M := M)) :
    exteriorMap (S := S) φ (x : ExteriorAlgebra R M) ∈ submodule (R := S) (M := N) := by
  have hx : ∀ m : M, ExteriorAlgebra.ι R m * (x : ExteriorAlgebra R M) = 0 := by
    have h : (x : ExteriorAlgebra R M) ∈
        ⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m)) :=
      determinant_submodule_eq_annihilator R M ▸ x.2
    simpa only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.mulLeft_apply] using h
  rw [determinant_submodule_eq_annihilator S N]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.mulLeft_apply]
  intro n
  have hn : n ∈ Submodule.span S (Set.range φ) := hφ ▸ Submodule.mem_top
  induction hn using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      rw [← exteriorMap_ι, ← map_mul, hx, map_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, add_mul, ha, hb, zero_add]
  | smul s a _ ha => rw [map_smul, smul_mul_assoc, ha, smul_zero]

/-- The map of determinant lines `det M → det N` induced by an `R`-linear map `φ : M → N` whose
image spans `N` over `S`. -/
def detMap (φ : M →ₗ[R] N) (hφ : Submodule.span S (Set.range φ) = ⊤) :
    module (R := R) (M := M) →ₗ[R] module (R := S) (M := N) where
  toFun x := ⟨exteriorMap (S := S) φ x, exteriorMap_mem_submodule φ hφ x⟩
  map_add' x y := Subtype.ext (map_add (exteriorMap (S := S) φ) x.1 y.1)
  map_smul' r x := Subtype.ext (map_smul (exteriorMap (S := S) φ) r x.1)

/-- The map of determinant lines is the induced map of exterior algebras on underlying
elements. -/
@[simp]
theorem coe_detMap (φ : M →ₗ[R] N) (hφ : Submodule.span S (Set.range φ) = ⊤)
    (x : module (R := R) (M := M)) :
    (detMap φ hφ x : ExteriorAlgebra S N) = exteriorMap (S := S) φ (x : ExteriorAlgebra R M) :=
  rfl

end ExteriorMap

section BaseChange

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- The image of a base change spans. -/
theorem span_range_eq_top_of_isBaseChange {φ : M →ₗ[R] N} (h : IsBaseChange S φ) :
    Submodule.span S (Set.range φ) = ⊤ := by
  rw [eq_top_iff]
  rintro n -
  induction n using h.inductionOn with
  | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
  | smul s n hn => exact Submodule.smul_mem _ s hn
  | add a b ha hb => exact Submodule.add_mem _ ha hb

/-- On the canonical base change `m ↦ 1 ⊗ m`, the induced map of exterior algebras is the inverse
of the base-change comparison applied to `1 ⊗ -`. -/
theorem exteriorMap_mk_one (y : ExteriorAlgebra R M) :
    exteriorMap (S := S) (TensorProduct.mk R S M 1) y =
      (exteriorAlgebraBaseChange R S M).symm ((1 : S) ⊗ₜ[R] y) := by
  let F : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra S (S ⊗[R] M) :=
    ((exteriorAlgebraBaseChange R S M).symm.toAlgHom.restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  have h : exteriorMap (S := S) (TensorProduct.mk R S M 1) = F := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun m => ?_)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, exteriorMap_ι,
      TensorProduct.mk_apply, F, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      AlgHom.restrictScalars_apply]
    rw [← exteriorAlgebraBaseChange_ι R S M m]
    exact ((exteriorAlgebraBaseChange R S M).symm_apply_apply _).symm
  rw [h]
  rfl

variable [Module.Finite R M] [Module.Projective R M] [Module.Finite S N] [Module.Projective S N]

/-- **The determinant line commutes with base change, along any base change.** If `φ : M → N`
exhibits `N` as `S ⊗_R M`, then `detMap φ` exhibits `det N` as `S ⊗_R det M`. -/
theorem isBaseChange_detMap {φ : M →ₗ[R] N} (h : IsBaseChange S φ) :
    IsBaseChange S (detMap φ (span_range_eq_top_of_isBaseChange h)) := by
  have : Module.Finite S (S ⊗[R] M) := inferInstance
  let E : S ⊗[R] module (R := R) (M := M) ≃ₗ[S] module (R := S) (M := N) :=
    (baseChangeEquiv (R := R) (A := S) (M := M)).trans (mapEquiv h.equiv)
  refine IsBaseChange.of_equiv E fun x => ?_
  apply Subtype.ext
  change ExteriorAlgebra.map h.equiv.toLinearMap
      ((baseChangeEquiv (R := R) (A := S) (M := M) (1 ⊗ₜ[R] x) :
        ExteriorAlgebra S (S ⊗[R] M))) = exteriorMap (S := S) φ (x : ExteriorAlgebra R M)
  rw [coe_baseChangeEquiv_tmul, ← exteriorMap_mk_one]
  rw [map_exteriorMap]
  congr 2
  exact LinearMap.ext fun m => by simp

omit [Module.Finite S N] [Module.Projective S N] in
/-- A base change has, at a prime of `S`, the rank of its source at the prime below. -/
theorem rankAtStalk_of_isBaseChange {φ : M →ₗ[R] N} (h : IsBaseChange S φ)
    (q : PrimeSpectrum S) :
    Module.rankAtStalk N q = Module.rankAtStalk M (PrimeSpectrum.comap (algebraMap R S) q) :=
  (congrFun (Module.rankAtStalk_eq_of_equiv h.equiv.symm) q).trans
    (Module.rankAtStalk_baseChange q)

end BaseChange

section Comp

variable {R : Type u} {S : Type u} {T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable {P : Type x} [AddCommGroup P] [Module R P] [Module S P] [Module T P]
  [IsScalarTower R S P] [IsScalarTower S T P] [IsScalarTower R T P]

/-- The maps of exterior algebras compose along a tower `R → S → T`. -/
theorem exteriorMap_comp (φ : M →ₗ[R] N) (ψ : N →ₗ[S] P) (y : ExteriorAlgebra R M) :
    exteriorMap (S := T) ((ψ.restrictScalars R).comp φ) y =
      exteriorMap (S := T) ψ (exteriorMap (S := S) φ y) := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap r =>
      rw [AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply R S
        (ExteriorAlgebra S N), AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  | ι m => simp
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

variable [Module.Finite R M] [Module.Projective R M] [Module.Finite S N] [Module.Projective S N]
  [Module.Finite T P] [Module.Projective T P]

/-- The induced maps of determinant lines compose along a tower `R → S → T`. -/
theorem detMap_comp (φ : M →ₗ[R] N) (hφ : Submodule.span S (Set.range φ) = ⊤)
    (ψ : N →ₗ[S] P) (hψ : Submodule.span T (Set.range ψ) = ⊤)
    (hψφ : Submodule.span T (Set.range ((ψ.restrictScalars R).comp φ)) = ⊤)
    (x : module (R := R) (M := M)) :
    detMap ((ψ.restrictScalars R).comp φ) hψφ x = detMap ψ hψ (detMap φ hφ x) :=
  Subtype.ext (exteriorMap_comp φ ψ x.1)

end Comp

end ProjectiveDeterminant

end
