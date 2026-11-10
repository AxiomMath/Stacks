module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.HomExtOfSectionRing
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedTangentFiniteDimensional
public import StacksFrontier.RingTheory.BaseChangeAlongSurjection
public import StacksFrontier.RingTheory.GradedAlgebra.GradedDerivationFunctor

/-!
# The infinitesimal automorphisms of the stack of polarized schemes at a point over a field

Let `k` be a field and `x₀ = (X ⟶ Spec k, ℒ)` an object of `𝒫olarized` over `Spec k`. Following
the proof of [Stacks, Tag 0D4S], the trivial deformation `x'_V` of `x₀` over `Spec k[V]` has graded
algebra `Q(x'_V) = k[V] ⊗_k P` (Stacks 0D4F, through the base change of Stacks 0D3L), for
`P = k ⊕ ⨁_{d ≥ d₀} H^0(X, ℒ^{⊗ d})`. An infinitesimal automorphism of `x'_V` acts on it by a
graded `k[V]`-algebra automorphism reducing to the identity, that is by `1 + D` for a
degree-preserving derivation `D : P → P ⊗_k V`. This map is natural in `V`, hence linear, and
injective because a morphism of deformations over a one-point base is determined by its map of
section rings. The degree-preserving derivations of the finitely generated graded algebra `P` with
finite-dimensional pieces form a finite-dimensional space, so `Inf_{x₀}(k)` is finite dimensional.

## Main definitions

* `AlgebraicGeometry.PolarizedDeformation.tensorRetract`: `k[V] ⊗_k P ≅ Q(x'_V)`.
* `AlgebraicGeometry.PolarizedDeformation.infTarget`: `V ↦ Der⁰_k(P, P ⊗ V)`.
* `AlgebraicGeometry.PolarizedDeformation.infDerivation`: the derivation of an infinitesimal
  automorphism.

## Main results

* `AlgebraicGeometry.PolarizedDeformation.infDerivation_injective`,
  `AlgebraicGeometry.PolarizedDeformation.infDerivation_naturality`
* `AlgebraicGeometry.PolarizedDeformation.finiteDimensional_infinitesimalAutomorphismFunctor_obj`:
  **Stacks 0D4S (2)** for the infinitesimal automorphisms.

## References

* [Stacks Project, Tag 0D4S](https://stacks.math.columbia.edu/tag/0D4S)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.BasedCategory.ofFunctor

@[expose] public noncomputable section

/-- **A base change does not depend on how its scalar structures are spelled**: the property is
transported along equalities of the algebra structure `R → S`, of the `R`-module structure of the
target, and of the linear map. -/
theorem IsBaseChange.of_instances_eq {R S M N : Type*} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module S N] {i₁ i₂ : Algebra R S} (hi : i₁ = i₂)
    {m₁ m₂ : Module R N} (hm : m₁ = m₂)
    {t₁ : letI := i₁; letI := m₁; IsScalarTower R S N}
    {t₂ : letI := i₂; letI := m₂; IsScalarTower R S N}
    {f₁ : letI := m₁; M →ₗ[R] N} {f₂ : letI := m₂; M →ₗ[R] N} (hf : ∀ x, f₁ x = f₂ x)
    (h : letI := i₁; letI := m₁; letI := t₁; IsBaseChange S f₁) :
    letI := i₂; letI := m₂; letI := t₂; IsBaseChange S f₂ := by
  subst hi hm
  obtain rfl : f₁ = f₂ := LinearMap.ext hf
  exact h

/-- An additive map between internally graded modules sending each piece into the corresponding
piece commutes with taking homogeneous components. -/
theorem DirectSum.decompose_map_of_mapsTo {ι A B σ τ : Type*} [DecidableEq ι]
    [AddCommMonoid A] [AddCommMonoid B] [SetLike σ A] [AddSubmonoidClass σ A]
    [SetLike τ B] [AddSubmonoidClass τ B]
    {𝒜 : ι → σ} {ℬ : ι → τ} [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ]
    (f : A →+ B) (hf : ∀ i a, a ∈ 𝒜 i → f a ∈ ℬ i) (a : A) (i : ι) :
    (DirectSum.decompose ℬ (f a) i : B) = f (DirectSum.decompose 𝒜 a i) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  rw [Finset.sum_eq_single i]
  · exact DirectSum.decompose_of_mem_same ℬ (hf i _ (SetLike.coe_mem _))
  · intro j _ hj
    exact DirectSum.decompose_of_mem_ne ℬ (hf j _ (SetLike.coe_mem _)) hj
  · intro hi
    rw [DFinsupp.notMem_support_iff.mp hi, ZeroMemClass.coe_zero, map_zero,
      DirectSum.decompose_zero]
    rfl

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily.AdmissibleDeformation.Hom

variable {P : PolarizedFamily.{u}} {D : P.AdmissibleDeformation}

/-- **An idempotent endomorphism of an affine deformation over the identity of its base algebra
acts trivially on global sections**: its section ring map is surjective, being a base change along
the identity, and idempotent. -/
theorem sectionRingHom_apply_eq_self [IsAffine D.S'] {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] {R : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} {ρ : R →+* Γ(D.S', ⊤)}
    (hρ : Function.Bijective ρ) (φ : Hom D D) (hb : ∀ r, φ.base.appLE ⊤ ⊤ le_rfl (ρ r) = ρ r)
    (hφ : φ.comp φ = φ) (y : D.sectionAlgebra.sectionRing ⊤) : sectionRingHom φ y = y := by
  have hbc := isBaseChange_sectionRingHom φ hρ hρ (𝟙 R) hb
  have hsurj : Function.Surjective (sectionRingHom φ) :=
    let i₁ := sectionRingAlgebraOver D ρ
    @IsBaseChange.surjective_of_surjective_algebraMap R R _ _ _ _ ((𝟙 R : R ⟶ R).hom.toAlgebra) _
      i₁.toModule _ (Module.compHom _ (𝟙 R : R ⟶ R).hom.toRingHom) i₁.toModule
      (@IsScalarTower.mk R R _ ((𝟙 R : R ⟶ R).hom.toAlgebra.toSMul) i₁.toSMul
        (Module.compHom _ (𝟙 R : R ⟶ R).hom.toRingHom).toSMul
        fun x y z =>
          @mul_smul R _ _ i₁.toModule.toDistribMulAction.toMulAction.toSemigroupAction x y z) _ hbc
      (fun r => ⟨r, rfl⟩)
  obtain ⟨z, rfl⟩ := hsurj y
  have h := DFunLike.congr_fun (sectionRingHom_comp φ φ) z
  rw [hφ] at h
  exact h.symm

end Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily.AdmissibleDeformation.Hom

namespace AlgebraicGeometry.PolarizedDeformation

open PolarizedFamily Deformation Deformation.Artin
open Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  (hT : Limits.IsTerminal (B.obj hS))
  {k : Type u} [Field k] (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  (x₀ : PolarizedFamily B)
  (hx : (polarizedSliceProjection B hS hT).obj x₀ = algebraOver k B S hS toS hk)

/-- `𝒫olarized`, read over the big fppf site of a terminal base, is fibred in groupoids. -/
theorem isFiberedInGroupoids_polarizedSliceProjection :
    (polarizedSliceProjection B hS hT).IsFiberedInGroupoids :=
  polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT

/-- The trivial deformation of `x₀` over `k[V]`, the pullback of `x₀` along
`Spec k[V] ⟶ Spec k`. -/
abbrev trivialLift (V : FGModuleCat.{u} k) : LiftFiber B hS hT toS hk x₀ hx V :=
  trivialDeformation k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx
    (isFiberedInGroupoids_polarizedSliceProjection B hS hT) ((fgSiteModule B hk).obj V)

/-- The identity of `x₀`, as an endomorphism of the trivial admissible deformation. -/
def deformationIdHom :
    AdmissibleDeformation.Hom (deformation₀ B hS hT toS hk x₀ hx)
      (deformation₀ B hS hT toS hk x₀ hx) :=
  liftHom (compactSpace₀ B hS hT toS hk x₀ hx) (isThickening_id_baseMap B x₀)
    (isThickening_id_baseMap B x₀) (𝟙 x₀) (Category.id_comp _)

/-- The identity of `x₀` acts trivially on the graded algebra of the special fibre. -/
theorem sectionRingHom_deformationIdHom
    (y : (deformation₀ B hS hT toS hk x₀ hx).sectionAlgebra.sectionRing ⊤) :
    AdmissibleDeformation.sectionRingHom (deformationIdHom B hS hT toS hk x₀ hx) y = y := by
  have : IsAffine (deformation₀ B hS hT toS hk x₀ hx).S' :=
    isAffine_of_baseEq (baseEq₀ B hS hT toS hk x₀ hx)
  refine AdmissibleDeformation.Hom.sectionRingHom_apply_eq_self
    (R := Deformation.Examples.residueFieldBase k k)
    (bijective_ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)) _ (fun r => ?_) ?_ y
  · refine (appLE_ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx) (baseEq₀ B hS hT toS hk x₀ hx)
      (B.inclusion.map (𝟙 x₀ : x₀ ⟶ x₀).baseMap) (𝟙 _) ?_ r).trans rfl
    change B.inclusion.map (𝟙 x₀.base) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Spec.map_id, Category.id_comp, Category.comp_id]
  · exact (liftHom_comp (compactSpace₀ B hS hT toS hk x₀ hx) (isThickening_id_baseMap B x₀)
      (isThickening_id_baseMap B x₀) (isThickening_id_baseMap B x₀) (𝟙 x₀) (𝟙 x₀)
      (Category.id_comp _) (Category.id_comp _)).symm.trans
      (liftHom_congr _ _ _ (Category.id_comp _) _ _)

variable {B hS hT toS hk x₀ hx} in
/-- The retraction of the trivial deformation onto `x₀`, as a morphism of admissible
deformations. -/
def retractHom (V : FGModuleCat.{u} k) :
    AdmissibleDeformation.Hom (liftDef B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
      (deformation₀ B hS hT toS hk x₀ hx) :=
  liftHom (compactSpace₀ B hS hT toS hk x₀ hx)
    (isThickening_liftBaseMap B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
    (isThickening_id_baseMap B x₀)
    (trivialRetract k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx
      (isFiberedInGroupoids_polarizedSliceProjection B hS hT) ((fgSiteModule B hk).obj V))
    (trivialRetract_fac k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx
      (isFiberedInGroupoids_polarizedSliceProjection B hS hT) ((fgSiteModule B hk).obj V))

/-- The structure morphism `k ⟶ k[V]` of `𝒞_k`. -/
def residueToSquareZero (V : FGModuleCat.{u} k) :
    Deformation.Examples.residueFieldBase k k ⟶ (artinianSquareZeroExtensionFunctor k k).obj V :=
  ⟨Algebra.ofId k _, ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst
      (x := (algebraMap k (TrivSqZeroExt k ((V : Type u)))) a)).mp ha⟩,
    fun a => by
      refine (squareZeroExtensionArtinian_residue k k V _).trans ?_
      exact (Deformation.Examples.residueFieldBase_residueEquiv_residue (Λ := k) (k := k) a).symm⟩

/-- **The retraction of the trivial deformation, on graded algebras**: the morphism
`P ⟶ Q(x'_V)` of the category of Stacks 0D3L over `k ⟶ k[V]`. -/
def retractAlgebraHom (V : FGModuleCat.{u} k) :
    specialFiberAlgebra B hS hT toS hk x₀ hx ⟶
      liftAlgebra B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V) :=
  haveI : IsAffine (deformation₀ B hS hT toS hk x₀ hx).S' :=
    isAffine_of_baseEq (baseEq₀ B hS hT toS hk x₀ hx)
  haveI : IsAffine (liftDef B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)).S' :=
    isAffine_of_baseEq (liftBaseEq B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
  AdmissibleDeformation.toProjectiveGradedAlgebraHom (retractHom V) _ _ _ _ _ _
    (residueToSquareZero V) (fun r => by
      have hp := isFiberedInGroupoids_polarizedSliceProjection B hS hT
      have := trivialRetract_isHomLift k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
        ((fgSiteModule B hk).obj V)
      have hfac := IsHomLift.fac' (polarizedSliceProjection B hS hT)
        (squareZeroRetraction k B S hS toS hk ((fgSiteModule B hk).obj V))
        (trivialRetract k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
          ((fgSiteModule B hk).obj V))
      have hb := baseMap_eq_of_map_eq B hS hT
        (trivialRetract k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
          ((fgSiteModule B hk).obj V))
        (squareZeroRetraction k B S hS toS hk ((fgSiteModule B hk).obj V))
        (liftRightEq B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)) hx hfac
      exact appLE_ringOfBaseEq
        (liftBaseEq B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
        (baseEq₀ B hS hT toS hk x₀ hx) _
        (CommRingCat.ofHom (TrivSqZeroExt.inlHom k ((fgSiteModule B hk).obj V).obj)) hb r)

/-- The retraction followed by the reduction to the special fibre is the identity of `P`. -/
theorem toSpecialFiber_retractAlgebraHom (V : FGModuleCat.{u} k)
    (y : (specialFiberAlgebra B hS hT toS hk x₀ hx).carrier) :
    (toSpecialFiber B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)).map
      ((retractAlgebraHom B hS hT toS hk x₀ hx V).map y) = y := by
  have hp := isFiberedInGroupoids_polarizedSliceProjection B hS hT
  have h := DFunLike.congr_fun (AdmissibleDeformation.sectionRingHom_comp
    (liftHom₀ B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)) (retractHom V)) y
  refine h.symm.trans ?_
  have hcomp := (liftHom_comp (compactSpace₀ B hS hT toS hk x₀ hx) (isThickening_id_baseMap B x₀)
    (isThickening_liftBaseMap B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
    (isThickening_id_baseMap B x₀) (trivialLift B hS hT toS hk x₀ hx V).1.hom
    (trivialRetract k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).obj V)) (Category.id_comp _)
    (trivialRetract_fac k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).obj V))).symm.trans
    (liftHom_congr _ _ _ (trivialRetract_fac k B S hS toS hk (polarizedSliceProjection B hS hT) x₀
      hx hp ((fgSiteModule B hk).obj V)) _ (Category.id_comp _))
  exact (congrArg (fun φ => AdmissibleDeformation.sectionRingHom φ y) hcomp).trans
    (sectionRingHom_deformationIdHom B hS hT toS hk x₀ hx y)

/-- The opposite scalar action on a finite-dimensional vector space, the one the square-zero
extensions `k[V]` of `𝒞_k` are built with. -/
local instance squareZeroModuleMulOpposite (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The two scalar actions on a finite-dimensional vector space agree. -/
local instance squareZeroIsCentralScalar (V : FGModuleCat.{u} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

/-- The graded ring `P` of the special fibre. -/
abbrev specialFiberRing : Type u := (deformation₀ B hS hT toS hk x₀ hx).sectionAlgebra.sectionRing ⊤

/-- The graded ring `Q(x'_V)` of the trivial deformation over `k[V]`. -/
abbrev trivialLiftRing (V : FGModuleCat.{u} k) : Type u :=
  (liftDef B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)).sectionAlgebra.sectionRing ⊤

/-- `P` as a `k`-algebra. -/
@[instance_reducible]
def specialFiberRingAlgebra : Algebra k (specialFiberRing B hS hT toS hk x₀ hx) :=
  AdmissibleDeformation.sectionRingAlgebraOver (R := k) (deformation₀ B hS hT toS hk x₀ hx)
    (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))

/-- `Q(x'_V)` as a `k[V]`-algebra. -/
@[instance_reducible]
def trivialLiftRingAlgebra (V : FGModuleCat.{u} k) :
    Algebra (TrivSqZeroExt k V) (trivialLiftRing B hS hT toS hk x₀ hx V) :=
  AdmissibleDeformation.sectionRingAlgebraOver (R := TrivSqZeroExt k V)
    (liftDef B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
    (ringOfBaseEq (liftBaseEq B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)))

/-- `Q(x'_V)` as a `k`-algebra, through `k ⟶ k[V]`. -/
@[instance_reducible]
def trivialLiftRingAlgebraBase (V : FGModuleCat.{u} k) :
    Algebra k (trivialLiftRing B hS hT toS hk x₀ hx V) :=
  letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  ((algebraMap (TrivSqZeroExt k V) (trivialLiftRing B hS hT toS hk x₀ hx V)).comp
    (algebraMap k (TrivSqZeroExt k V))).toAlgebra

/-- The scalar tower `k → k[V] → Q(x'_V)`. -/
theorem trivialLiftRing_isScalarTower (V : FGModuleCat.{u} k) :
    letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
    letI := trivialLiftRingAlgebraBase B hS hT toS hk x₀ hx V
    IsScalarTower k (TrivSqZeroExt k V) (trivialLiftRing B hS hT toS hk x₀ hx V) :=
  letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  letI := trivialLiftRingAlgebraBase B hS hT toS hk x₀ hx V
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The retraction `P → Q(x'_V)`, as a homomorphism of `k`-algebras. -/
def retractAlgHom (V : FGModuleCat.{u} k) :
    letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
    letI := trivialLiftRingAlgebraBase B hS hT toS hk x₀ hx V
    specialFiberRing B hS hT toS hk x₀ hx →ₐ[k] trivialLiftRing B hS hT toS hk x₀ hx V :=
  letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  letI := trivialLiftRingAlgebraBase B hS hT toS hk x₀ hx V
  { (retractAlgebraHom B hS hT toS hk x₀ hx V).map with
    commutes' := fun r => by
      have h := (retractAlgebraHom B hS hT toS hk x₀ hx V).map_smul r 1
      rw [map_one] at h
      change (retractAlgebraHom B hS hT toS hk x₀ hx V).map
        (algebraMap k (specialFiberRing B hS hT toS hk x₀ hx) r) = _
      rw [Algebra.algebraMap_eq_smul_one]
      refine h.trans ?_
      exact (Algebra.algebraMap_eq_smul_one _).symm }

/-- The retraction `P → Q(x'_V)`, as a ring map. -/
def retractRingHom (V : FGModuleCat.{u} k) :
    specialFiberRing B hS hT toS hk x₀ hx →+* trivialLiftRing B hS hT toS hk x₀ hx V :=
  (retractAlgebraHom B hS hT toS hk x₀ hx V).map

/-- **The trivial deformation is `k[V] ⊗ P` on graded algebras**: the `k[V]`-algebra map
`k[V] ⊗_k P → Q(x'_V)`, `r ⊗ x ↦ r · c(x)`, for the retraction `c : P → Q(x'_V)`. -/
def tensorRetract (V : FGModuleCat.{u} k) :
    letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
    letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
    TrivSqZeroExt k V ⊗[k] specialFiberRing B hS hT toS hk x₀ hx →ₐ[TrivSqZeroExt k V]
      trivialLiftRing B hS hT toS hk x₀ hx V :=
  letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  letI := trivialLiftRingAlgebraBase B hS hT toS hk x₀ hx V
  haveI := trivialLiftRing_isScalarTower B hS hT toS hk x₀ hx V
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (retractAlgHom B hS hT toS hk x₀ hx V)
    (fun _ _ => Commute.all _ _)

/-- `k[V] ⊗_k P → Q(x'_V)` on pure tensors. -/
theorem tensorRetract_tmul (V : FGModuleCat.{u} k) (r : TrivSqZeroExt k V)
    (x : specialFiberRing B hS hT toS hk x₀ hx) :
    letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
    letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
    tensorRetract B hS hT toS hk x₀ hx V (r ⊗ₜ x) =
      algebraMap (TrivSqZeroExt k V) (trivialLiftRing B hS hT toS hk x₀ hx V) r *
        retractRingHom B hS hT toS hk x₀ hx V x :=
  rfl

/-- The structure map `k ⟶ k[V]` of `𝒞_k` induces the standard `k`-algebra structure of `k[V]`. -/
theorem residueToSquareZero_toAlgebra (V : FGModuleCat.{u} k) :
    (residueToSquareZero V).hom.toRingHom.toAlgebra =
      (inferInstance : Algebra k (TrivSqZeroExt k V)) :=
  Algebra.algebra_ext _ _ fun _ => rfl

/-- The two `k`-module structures of `Q(x'_V)` agree. -/
theorem compHom_residueToSquareZero (V : FGModuleCat.{u} k) :
    letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
    (Module.compHom (trivialLiftRing B hS hT toS hk x₀ hx V)
      (show k →+* TrivSqZeroExt k V from (residueToSquareZero V).hom.toRingHom)) =
      (trivialLiftRingAlgebraBase B hS hT toS hk x₀ hx V).toModule :=
  Module.ext' _ _ fun _ _ => rfl

/-- **`Q(x'_V)` is the base change of `P` along `k ⟶ k[V]`** (Stacks 0D4F, through 0D3L), for the
standard `k`-algebra structure of `k[V]`. -/
theorem isBaseChange_retractAlgHom (V : FGModuleCat.{u} k) :
    letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
    letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
    letI := trivialLiftRingAlgebraBase B hS hT toS hk x₀ hx V
    letI := trivialLiftRing_isScalarTower B hS hT toS hk x₀ hx V
    IsBaseChange (TrivSqZeroExt k V) (retractAlgHom B hS hT toS hk x₀ hx V).toLinearMap := by
  let := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  let := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  let := trivialLiftRingAlgebraBase B hS hT toS hk x₀ hx V
  let := trivialLiftRing_isScalarTower B hS hT toS hk x₀ hx V
  have hbc := (retractAlgebraHom B hS hT toS hk x₀ hx V).isBaseChange
  let : Algebra ((artinianSquareZeroExtensionFunctor k k).obj V)
      (trivialLiftRing B hS hT toS hk x₀ hx V) := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  exact IsBaseChange.of_instances_eq (residueToSquareZero_toAlgebra V)
    (compHom_residueToSquareZero B hS hT toS hk x₀ hx V) (fun _ => rfl) hbc

/-- `k[V] ⊗_k P → Q(x'_V)` is bijective. -/
theorem bijective_tensorRetract (V : FGModuleCat.{u} k) :
    Function.Bijective (tensorRetract B hS hT toS hk x₀ hx V) := by
  let := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  let := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  let := trivialLiftRingAlgebraBase B hS hT toS hk x₀ hx V
  let := trivialLiftRing_isScalarTower B hS hT toS hk x₀ hx V
  have h2 := isBaseChange_retractAlgHom B hS hT toS hk x₀ hx V
  have he : ∀ z, tensorRetract B hS hT toS hk x₀ hx V z = h2.equiv z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
      rw [IsBaseChange.equiv_tmul, tensorRetract_tmul, Algebra.smul_def]
      rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hfun : ⇑(tensorRetract B hS hT toS hk x₀ hx V) = ⇑h2.equiv := funext he
  rw [hfun]
  exact h2.equiv.bijective

variable {V : FGModuleCat.{u} k}

/-- An infinitesimal automorphism of the trivial deformation, on its graded algebra. -/
def infAlgebraHom (θ : trivialLift B hS hT toS hk x₀ hx V ⟶ trivialLift B hS hT toS hk x₀ hx V) :
    liftAlgebra B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V) ⟶
      liftAlgebra B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V) :=
  liftAlgebraHom B hS hT toS hk x₀ hx (𝟙 V) _ _ θ.1.right
    (map_right_eq_of_fiberHom B hS hT toS hk x₀ hx _ _ θ) (Under.w θ.1)

/-- An infinitesimal automorphism of the trivial deformation, as an endomorphism of the
`k[V]`-algebra `Q(x'_V)`. -/
def infAlgHom (θ : trivialLift B hS hT toS hk x₀ hx V ⟶ trivialLift B hS hT toS hk x₀ hx V) :
    letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
    trivialLiftRing B hS hT toS hk x₀ hx V →ₐ[TrivSqZeroExt k V]
      trivialLiftRing B hS hT toS hk x₀ hx V :=
  letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  { (infAlgebraHom B hS hT toS hk x₀ hx θ).map with
    commutes' := fun r => by
      have h := (infAlgebraHom B hS hT toS hk x₀ hx θ).map_smul r 1
      rw [map_one] at h
      change (infAlgebraHom B hS hT toS hk x₀ hx θ).map
        (algebraMap (TrivSqZeroExt k V) (trivialLiftRing B hS hT toS hk x₀ hx V) r) = _
      rw [Algebra.algebraMap_eq_smul_one]
      refine h.trans ?_
      have hb : (infAlgebraHom B hS hT toS hk x₀ hx θ).base.hom r = r := by
        change ((artinianSquareZeroExtensionFunctor k k).map (𝟙 V)).hom r = r
        rw [CategoryTheory.Functor.map_id]
        rfl
      exact congrArg (fun s => s • (1 : (liftAlgebra B hS hT toS hk x₀ hx V
        (trivialLift B hS hT toS hk x₀ hx V)).carrier)) hb }

/-- An infinitesimal automorphism of the trivial deformation, read on `k[V] ⊗_k P`. -/
def infTensorAlgHom (θ : trivialLift B hS hT toS hk x₀ hx V ⟶ trivialLift B hS hT toS hk x₀ hx V) :
    letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
    TrivSqZeroExt k V ⊗[k] specialFiberRing B hS hT toS hk x₀ hx →ₐ[TrivSqZeroExt k V]
      TrivSqZeroExt k V ⊗[k] specialFiberRing B hS hT toS hk x₀ hx :=
  letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  (AlgEquiv.ofBijective (tensorRetract B hS hT toS hk x₀ hx V)
    (bijective_tensorRetract B hS hT toS hk x₀ hx V)).symm.toAlgHom.comp
      ((infAlgHom B hS hT toS hk x₀ hx θ).comp (tensorRetract B hS hT toS hk x₀ hx V))

/-- `tensorRetract` intertwines the two readings of an infinitesimal automorphism. -/
private theorem tensorRetract_infTensorAlgHom_aux
    (θ : trivialLift B hS hT toS hk x₀ hx V ⟶ trivialLift B hS hT toS hk x₀ hx V) :
    letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
    ∀ q : TrivSqZeroExt k V ⊗[k] specialFiberRing B hS hT toS hk x₀ hx,
      tensorRetract B hS hT toS hk x₀ hx V (infTensorAlgHom B hS hT toS hk x₀ hx θ q) =
        infAlgHom B hS hT toS hk x₀ hx θ (tensorRetract B hS hT toS hk x₀ hx V q) := by
  let := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  let := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  intro q
  exact (AlgEquiv.ofBijective (tensorRetract B hS hT toS hk x₀ hx V)
    (bijective_tensorRetract B hS hT toS hk x₀ hx V)).apply_symm_apply _

variable (V) in
/-- The reduction `Q(x'_V) → P` to the special fibre, as a ring map. -/
def reductionHom :
    trivialLiftRing B hS hT toS hk x₀ hx V →+* specialFiberRing B hS hT toS hk x₀ hx :=
  (toSpecialFiber B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)).map

variable (V) in
/-- The first coordinate of `k[V] ⊗_k P` is the reduction of `Q(x'_V)` to the special fibre. -/
theorem trivSqZeroExtTensorFst_eq :
    letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
    ∀ z : TrivSqZeroExt k V ⊗[k] specialFiberRing B hS hT toS hk x₀ hx,
      GradedAlgebra.trivSqZeroExtTensorFst k (specialFiberRing B hS hT toS hk x₀ hx) V z =
        reductionHom B hS hT toS hk x₀ hx V (tensorRetract B hS hT toS hk x₀ hx V z) := by
  let := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  let := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  intro z
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul r y =>
    rw [GradedAlgebra.trivSqZeroExtTensorFst_tmul, tensorRetract_tmul, map_mul]
    have h1 : reductionHom B hS hT toS hk x₀ hx V
        (retractRingHom B hS hT toS hk x₀ hx V y) = y :=
      toSpecialFiber_retractAlgebraHom B hS hT toS hk x₀ hx V y
    have h := (toSpecialFiber B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)).map_smul
      r 1
    have h2 : reductionHom B hS hT toS hk x₀ hx V
        (algebraMap (TrivSqZeroExt k V) (trivialLiftRing B hS hT toS hk x₀ hx V) r) =
          r.fst • (1 : specialFiberRing B hS hT toS hk x₀ hx) :=
      (congrArg (reductionHom B hS hT toS hk x₀ hx V)
        (Algebra.algebraMap_eq_smul_one (A := trivialLiftRing B hS hT toS hk x₀ hx V) r)).trans
        ((h.trans (congrArg (fun t : (specialFiberAlgebra B hS hT toS hk x₀ hx).base =>
          t • ((toSpecialFiber B hS hT toS hk x₀ hx V
            (trivialLift B hS hT toS hk x₀ hx V)).map 1)) (terminal_from_hom_apply V r))).trans
          (congrArg (fun t : (specialFiberAlgebra B hS hT toS hk x₀ hx).carrier =>
            (show (specialFiberAlgebra B hS hT toS hk x₀ hx).base from r.fst) • t) (map_one _)))
    rw [h1, h2, smul_mul_assoc, one_mul]

/-- The reduction of `Q(x'_V)` to the special fibre is invariant under an infinitesimal
automorphism. -/
theorem toSpecialFiber_infAlgebraHom
    (θ : trivialLift B hS hT toS hk x₀ hx V ⟶ trivialLift B hS hT toS hk x₀ hx V)
    (q : trivialLiftRing B hS hT toS hk x₀ hx V) :
    reductionHom B hS hT toS hk x₀ hx V (infAlgHom B hS hT toS hk x₀ hx θ q) =
      reductionHom B hS hT toS hk x₀ hx V q :=
  DFunLike.congr_fun (congrArg (fun f => f.map)
    (liftAlgebraHom_comp_toSpecialFiber B hS hT toS hk x₀ hx (𝟙 V) _ _ θ.1.right
      (map_right_eq_of_fiberHom B hS hT toS hk x₀ hx _ _ θ) (Under.w θ.1))) q

/-- An infinitesimal automorphism, read on `k[V] ⊗_k P`, reduces to the identity. -/
theorem infTensorAlgHom_reduction
    (θ : trivialLift B hS hT toS hk x₀ hx V ⟶ trivialLift B hS hT toS hk x₀ hx V)
    (x : specialFiberRing B hS hT toS hk x₀ hx) :
    letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
    GradedAlgebra.trivSqZeroExtTensorReduction k (specialFiberRing B hS hT toS hk x₀ hx) V
      (infTensorAlgHom B hS hT toS hk x₀ hx θ (1 ⊗ₜ x)) = 1 ⊗ₜ x := by
  let := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  let := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  apply (TensorProduct.lid k (specialFiberRing B hS hT toS hk x₀ hx)).injective
  change GradedAlgebra.trivSqZeroExtTensorFst k (specialFiberRing B hS hT toS hk x₀ hx) V
      (infTensorAlgHom B hS hT toS hk x₀ hx θ (1 ⊗ₜ x)) =
    GradedAlgebra.trivSqZeroExtTensorFst k (specialFiberRing B hS hT toS hk x₀ hx) V (1 ⊗ₜ x)
  rw [trivSqZeroExtTensorFst_eq, trivSqZeroExtTensorFst_eq]
  rw [tensorRetract_infTensorAlgHom_aux, toSpecialFiber_infAlgebraHom]

/-- An infinitesimal automorphism, read on `k[V] ⊗_k P`, preserves the grading: it sends `1 ⊗ x`
for `x ∈ P_d` into `k[V] ⊗ P_d`. -/
theorem infTensorAlgHom_mem
    (θ : trivialLift B hS hT toS hk x₀ hx V ⟶ trivialLift B hS hT toS hk x₀ hx V) :
    letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
    ∀ (d : ℕ) (x : specialFiberRing B hS hT toS hk x₀ hx),
      x ∈ AdmissibleDeformation.sectionGrading (R := k) (deformation₀ B hS hT toS hk x₀ hx)
          (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)) d →
        infTensorAlgHom B hS hT toS hk x₀ hx θ (1 ⊗ₜ x) ∈ LinearMap.range
          (TensorProduct.map (LinearMap.id : TrivSqZeroExt k V →ₗ[k] TrivSqZeroExt k V)
            (AdmissibleDeformation.sectionGrading (R := k) (deformation₀ B hS hT toS hk x₀ hx)
              (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)) d).subtype) := by
  let := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  let := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  let gP := AdmissibleDeformation.sectionGrading (R := k) (deformation₀ B hS hT toS hk x₀ hx)
    (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
  let gQ := AdmissibleDeformation.sectionGrading (R := TrivSqZeroExt k V)
    (liftDef B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
    (ringOfBaseEq (liftBaseEq B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)))
  let : GradedAlgebra gP := AdmissibleDeformation.sectionGradedAlgebra (R := k)
    (deformation₀ B hS hT toS hk x₀ hx) (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
  let : GradedAlgebra gQ := AdmissibleDeformation.sectionGradedAlgebra (R := TrivSqZeroExt k V)
    (liftDef B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
    (ringOfBaseEq (liftBaseEq B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)))
  intro d x hxd
  let e := tensorRetract B hS hT toS hk x₀ hx V
  let c : specialFiberRing B hS hT toS hk x₀ hx →+* trivialLiftRing B hS hT toS hk x₀ hx V :=
    (retractAlgebraHom B hS hT toS hk x₀ hx V).map
  have hc : ∀ i y, y ∈ gP i → c y ∈ gQ i := fun i y hy =>
    (retractAlgebraHom B hS hT toS hk x₀ hx V).map_mem i y hy
  let z := infTensorAlgHom B hS hT toS hk x₀ hx θ (1 ⊗ₜ x)
  have hez : e z = infAlgHom B hS hT toS hk x₀ hx θ (e (1 ⊗ₜ x)) :=
    tensorRetract_infTensorAlgHom_aux B hS hT toS hk x₀ hx θ _
  have he1 : e (1 ⊗ₜ x) = c x := by
    refine (tensorRetract_tmul B hS hT toS hk x₀ hx V 1 x).trans ?_
    rw [map_one, one_mul]
    rfl
  have hw : e z ∈ gQ d := by
    rw [hez, he1]
    exact (infAlgebraHom B hS hT toS hk x₀ hx θ).map_mem d _ (hc d x hxd)
  let g : specialFiberRing B hS hT toS hk x₀ hx →ₗ[k] gP d :=
    (DirectSum.component k ℕ (fun i => gP i) d).comp
      (DirectSum.decomposeLinearEquiv gP).toLinearMap
  let πQ : trivialLiftRing B hS hT toS hk x₀ hx V →ₗ[TrivSqZeroExt k V]
      trivialLiftRing B hS hT toS hk x₀ hx V :=
    (gQ d).subtype.comp ((DirectSum.component (TrivSqZeroExt k V) ℕ (fun i => gQ i) d).comp
      (DirectSum.decomposeLinearEquiv gQ).toLinearMap)
  have hπQ : ∀ q, πQ q = (DirectSum.decompose gQ q d : trivialLiftRing B hS hT toS hk x₀ hx V) :=
    fun _ => rfl
  have hcomm : ∀ w, e (TensorProduct.map LinearMap.id ((gP d).subtype.comp g) w) = πQ (e w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
    | tmul r y =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
      refine (tensorRetract_tmul B hS hT toS hk x₀ hx V r _).trans ?_
      refine Eq.trans ?_ (congrArg πQ (tensorRetract_tmul B hS hT toS hk x₀ hx V r y)).symm
      change algebraMap _ _ r * c _ = πQ (algebraMap _ _ r * c y)
      rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul, hπQ]
      congr 1
      exact (DirectSum.decompose_map_of_mapsTo c.toAddMonoidHom hc y d).symm
  have hz : TensorProduct.map LinearMap.id ((gP d).subtype.comp g) z = z := by
    apply (bijective_tensorRetract B hS hT toS hk x₀ hx V).1
    refine (hcomm z).trans ?_
    rw [hπQ]
    exact DirectSum.decompose_of_mem_same gQ hw
  refine ⟨TensorProduct.map LinearMap.id g z, ?_⟩
  refine Eq.trans ?_ hz
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]

variable (V) in
/-- **The target of the infinitesimal automorphisms**: the degree-preserving derivations
`P → P ⊗_k V` of the graded algebra of the special fibre, as an additive `k`-linear functor of
`V`. -/
def infTarget : FGModuleCat.{u} k ⥤ ModuleCat.{u} k :=
  letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  GradedAlgebra.gradedDerivationFunctor (P := specialFiberRing B hS hT toS hk x₀ hx)
    (AdmissibleDeformation.sectionGrading (R := k) (deformation₀ B hS hT toS hk x₀ hx)
      (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)))

/-- `infTarget` is additive. -/
instance infTarget_additive : (infTarget B hS hT toS hk x₀ hx).Additive :=
  letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  inferInstanceAs
    (GradedAlgebra.gradedDerivationFunctor (P := specialFiberRing B hS hT toS hk x₀ hx)
      (AdmissibleDeformation.sectionGrading (R := k) (deformation₀ B hS hT toS hk x₀ hx)
        (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)))).Additive

/-- `infTarget` is `k`-linear. -/
instance infTarget_linear : (infTarget B hS hT toS hk x₀ hx).Linear k :=
  letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  inferInstanceAs
    ((GradedAlgebra.gradedDerivationFunctor (P := specialFiberRing B hS hT toS hk x₀ hx)
      (AdmissibleDeformation.sectionGrading (R := k) (deformation₀ B hS hT toS hk x₀ hx)
        (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)))).Linear k)

/-- **The derivation of an infinitesimal automorphism of the trivial deformation**: on
`k[V] ⊗_k P` it is `1 ⊗ x ↦ 1 ⊗ x + D(x)` for a degree-preserving derivation `D : P → P ⊗ V`. -/
def infDerivation (θ : trivialLift B hS hT toS hk x₀ hx V ⟶ trivialLift B hS hT toS hk x₀ hx V) :
    (infTarget B hS hT toS hk x₀ hx).obj V :=
  letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  GradedAlgebra.derivationOfAlgHom
    (AdmissibleDeformation.sectionGrading (R := k) (deformation₀ B hS hT toS hk x₀ hx)
      (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))) V
    (infTensorAlgHom B hS hT toS hk x₀ hx θ) (infTensorAlgHom_mem B hS hT toS hk x₀ hx θ)
    (infTensorAlgHom_reduction B hS hT toS hk x₀ hx θ)

/-- **An infinitesimal automorphism of the trivial deformation is determined by its
derivation.** -/
theorem infDerivation_injective :
    Function.Injective (infDerivation B hS hT toS hk x₀ hx (V := V)) := by
  let := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  let := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  intro θ θ' h
  have hσ := GradedAlgebra.derivationOfAlgHom_injective _ V h
  have hQ : ∀ q, infAlgHom B hS hT toS hk x₀ hx θ q = infAlgHom B hS hT toS hk x₀ hx θ' q := by
    intro q
    obtain ⟨z, rfl⟩ := (bijective_tensorRetract B hS hT toS hk x₀ hx V).2 q
    rw [← tensorRetract_infTensorAlgHom_aux, ← tensorRetract_infTensorAlgHom_aux, hσ]
  have hbase : θ.1.right.baseMap = θ'.1.right.baseMap := by
    have e1 := map_right_eq_of_fiberHom B hS hT toS hk x₀ hx _ _ θ
    have e2 := map_right_eq_of_fiberHom B hS hT toS hk x₀ hx _ _ θ'
    exact congrArg (fun φ => φ.left) (e1.trans e2.symm)
  have : Subsingleton (liftDef B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)).S' :=
    subsingleton_of_baseEq
      (liftBaseEq B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
  have hhom := AdmissibleDeformation.Hom.ext_of_sectionRingHom
    (liftHom (compactSpace₀ B hS hT toS hk x₀ hx)
      (isThickening_liftBaseMap B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
      (isThickening_liftBaseMap B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
      θ.1.right (Under.w θ.1))
    (liftHom (compactSpace₀ B hS hT toS hk x₀ hx)
      (isThickening_liftBaseMap B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
      (isThickening_liftBaseMap B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
      θ'.1.right (Under.w θ'.1))
    (congrArg B.inclusion.map hbase) (RingHom.ext hQ)
  have htot := congrArg AdmissibleDeformation.Hom.total hhom
  have hpol := congr_arg_heq AdmissibleDeformation.Hom.polarization hhom
  apply Functor.Fiber.hom_ext
  apply Under.UnderMorphism.ext
  exact PolarizedFamily.Hom.ext hbase htot hpol

variable {W : FGModuleCat.{u} k}

/-- The transition `Q(x'_V) → Q(x'_W)` of the trivial deformations along `f : V ⟶ W`. -/
def transAlgebraHom (f : V ⟶ W) :
    liftAlgebra B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V) ⟶
      liftAlgebra B hS hT toS hk x₀ hx W (trivialLift B hS hT toS hk x₀ hx W) :=
  have hp := isFiberedInGroupoids_polarizedSliceProjection B hS hT
  haveI := trivialTransition_isHomLift k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
    ((fgSiteModule B hk).map f)
  liftAlgebraHom B hS hT toS hk x₀ hx f _ _
    (trivialTransition k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).map f))
    (IsHomLift.fac' (polarizedSliceProjection B hS hT)
      (squareZeroOverMap k B S hS toS ((fgSiteModule B hk).map f)) _)
    (Under.w (trivialTransitionUnder k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).map f)))

/-- The transition `Q(x'_V) → Q(x'_W)`, as a ring map. -/
def transRingHom (f : V ⟶ W) :
    trivialLiftRing B hS hT toS hk x₀ hx V →+* trivialLiftRing B hS hT toS hk x₀ hx W :=
  (transAlgebraHom B hS hT toS hk x₀ hx f).map

/-- The transitions are compatible with the retractions. -/
theorem transAlgebraHom_retract (f : V ⟶ W) (y : specialFiberRing B hS hT toS hk x₀ hx) :
    transRingHom B hS hT toS hk x₀ hx f (retractRingHom B hS hT toS hk x₀ hx V y) =
      retractRingHom B hS hT toS hk x₀ hx W y := by
  have hp := isFiberedInGroupoids_polarizedSliceProjection B hS hT
  have h := DFunLike.congr_fun (AdmissibleDeformation.sectionRingHom_comp
    (liftHom (compactSpace₀ B hS hT toS hk x₀ hx)
      (isThickening_liftBaseMap B hS hT toS hk x₀ hx W (trivialLift B hS hT toS hk x₀ hx W))
      (isThickening_liftBaseMap B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
      (trivialTransition k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
        ((fgSiteModule B hk).map f))
      (Under.w (trivialTransitionUnder k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
        ((fgSiteModule B hk).map f))))
    (retractHom V)) y
  refine h.symm.trans ?_
  have hcomp := (liftHom_comp (compactSpace₀ B hS hT toS hk x₀ hx)
    (isThickening_liftBaseMap B hS hT toS hk x₀ hx W (trivialLift B hS hT toS hk x₀ hx W))
    (isThickening_liftBaseMap B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V))
    (isThickening_id_baseMap B x₀)
    (trivialTransition k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).map f))
    (trivialRetract k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).obj V))
    (Under.w (trivialTransitionUnder k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
        ((fgSiteModule B hk).map f)))
    (trivialRetract_fac k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).obj V))).symm.trans
    (liftHom_congr _ _ _ (trivialTransition_comp_retract k B S hS toS hk
      (polarizedSliceProjection B hS hT) x₀ hx hp ((fgSiteModule B hk).map f)) _
      (trivialRetract_fac k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
        ((fgSiteModule B hk).obj W)))
  exact congrArg (fun φ => AdmissibleDeformation.sectionRingHom φ y) hcomp

/-- The identification `k[V] ⊗_k P = Q(x'_V)` is natural in `V`. -/
theorem tensorRetract_naturality (f : V ⟶ W) :
    letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
    ∀ q : TrivSqZeroExt k V ⊗[k] specialFiberRing B hS hT toS hk x₀ hx,
      tensorRetract B hS hT toS hk x₀ hx W
          (GradedAlgebra.trivSqZeroExtTensorMap (specialFiberRing B hS hT toS hk x₀ hx)
            f.hom.hom q) =
        transRingHom B hS hT toS hk x₀ hx f (tensorRetract B hS hT toS hk x₀ hx V q) := by
  let := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  let := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  let := trivialLiftRingAlgebra B hS hT toS hk x₀ hx W
  intro q
  induction q using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r y =>
    rw [GradedAlgebra.trivSqZeroExtTensorMap_tmul, tensorRetract_tmul, tensorRetract_tmul, map_mul]
    have h := (transAlgebraHom B hS hT toS hk x₀ hx f).map_smul r 1
    rw [map_one] at h
    have hτ : transRingHom B hS hT toS hk x₀ hx f
        (algebraMap (TrivSqZeroExt k V) (trivialLiftRing B hS hT toS hk x₀ hx V) r) =
        algebraMap (TrivSqZeroExt k W) (trivialLiftRing B hS hT toS hk x₀ hx W)
          (TrivSqZeroExt.map f.hom.hom r) :=
      (congrArg (transRingHom B hS hT toS hk x₀ hx f)
        (Algebra.algebraMap_eq_smul_one (A := trivialLiftRing B hS hT toS hk x₀ hx V) r)).trans
        (h.trans (Algebra.algebraMap_eq_smul_one (A := trivialLiftRing B hS hT toS hk x₀ hx W)
          (TrivSqZeroExt.map f.hom.hom r)).symm)
    rw [hτ, transAlgebraHom_retract]

/-- The transitions intertwine an infinitesimal automorphism and its restriction. -/
theorem transAlgebraHom_infAlgHom (f : V ⟶ W)
    (θ : trivialLift B hS hT toS hk x₀ hx V ⟶ trivialLift B hS hT toS hk x₀ hx V)
    (q : trivialLiftRing B hS hT toS hk x₀ hx V) :
    letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
    letI := trivialLiftRingAlgebra B hS hT toS hk x₀ hx W
    transRingHom B hS hT toS hk x₀ hx f (infAlgHom B hS hT toS hk x₀ hx θ q) =
      infAlgHom B hS hT toS hk x₀ hx
        (fiberEndRestrict (Under.post (polarizedSliceProjection B hS hT))
          (underPost_isFiberedInGroupoids _
            (isFiberedInGroupoids_polarizedSliceProjection B hS hT) x₀)
          (trivialTransitionUnder k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx
            (isFiberedInGroupoids_polarizedSliceProjection B hS hT) ((fgSiteModule B hk).map f))
          (trivialTransitionUnder_isHomLift k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx
            (isFiberedInGroupoids_polarizedSliceProjection B hS hT) ((fgSiteModule B hk).map f)) θ)
        (transRingHom B hS hT toS hk x₀ hx f q) := by
  have hp := isFiberedInGroupoids_polarizedSliceProjection B hS hT
  let θW := fiberEndRestrict (Under.post (polarizedSliceProjection B hS hT))
    (underPost_isFiberedInGroupoids _ hp x₀)
    (trivialTransitionUnder k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).map f))
    (trivialTransitionUnder_isHomLift k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).map f)) θ
  have hfac := congrArg (fun φ => φ.right) (fiberEndRestrict_fac (Under.post
    (polarizedSliceProjection B hS hT)) (underPost_isFiberedInGroupoids _ hp x₀)
    (trivialTransitionUnder k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).map f))
    (trivialTransitionUnder_isHomLift k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).map f)) θ)
  simp only [Under.comp_right] at hfac
  let thW := isThickening_liftBaseMap B hS hT toS hk x₀ hx W (trivialLift B hS hT toS hk x₀ hx W)
  let thV := isThickening_liftBaseMap B hS hT toS hk x₀ hx V (trivialLift B hS hT toS hk x₀ hx V)
  let tr := trivialTransition k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
    ((fgSiteModule B hk).map f)
  have htr : (trivialLift B hS hT toS hk x₀ hx W).1.hom ≫ tr =
      (trivialLift B hS hT toS hk x₀ hx V).1.hom :=
    Under.w (trivialTransitionUnder k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx hp
      ((fgSiteModule B hk).map f))
  have h1 := DFunLike.congr_fun (AdmissibleDeformation.sectionRingHom_comp
    (liftHom (compactSpace₀ B hS hT toS hk x₀ hx) thW thV tr htr)
    (liftHom (compactSpace₀ B hS hT toS hk x₀ hx) thV thV θ.1.right (Under.w θ.1))) q
  have h2 := DFunLike.congr_fun (AdmissibleDeformation.sectionRingHom_comp
    (liftHom (compactSpace₀ B hS hT toS hk x₀ hx) thW thW θW.1.right (Under.w θW.1))
    (liftHom (compactSpace₀ B hS hT toS hk x₀ hx) thW thV tr htr)) q
  refine h1.symm.trans (Eq.trans ?_ h2)
  rw [← liftHom_comp, ← liftHom_comp]
  exact congrArg (fun φ => AdmissibleDeformation.sectionRingHom φ q)
    (liftHom_congr _ _ _ hfac.symm _ _)

/-- `tensorRetract` intertwines the two readings of an infinitesimal automorphism. -/
theorem tensorRetract_infTensorAlgHom
    (θ : trivialLift B hS hT toS hk x₀ hx V ⟶ trivialLift B hS hT toS hk x₀ hx V) :
    letI := specialFiberRingAlgebra B hS hT toS hk x₀ hx
    ∀ q : TrivSqZeroExt k V ⊗[k] specialFiberRing B hS hT toS hk x₀ hx,
      tensorRetract B hS hT toS hk x₀ hx V (infTensorAlgHom B hS hT toS hk x₀ hx θ q) =
        infAlgHom B hS hT toS hk x₀ hx θ (tensorRetract B hS hT toS hk x₀ hx V q) := by
  exact tensorRetract_infTensorAlgHom_aux B hS hT toS hk x₀ hx θ

/-- **The derivation of an infinitesimal automorphism is natural in `V`**: restricting an
infinitesimal automorphism along `f : V ⟶ W` pushes its derivation forward along `P ⊗ f`. -/
theorem infDerivation_naturality (f : V ⟶ W)
    (θ : trivialLift B hS hT toS hk x₀ hx V ⟶ trivialLift B hS hT toS hk x₀ hx V) :
    infDerivation B hS hT toS hk x₀ hx
        (fiberEndRestrict (Under.post (polarizedSliceProjection B hS hT))
          (underPost_isFiberedInGroupoids _
            (isFiberedInGroupoids_polarizedSliceProjection B hS hT) x₀)
          (trivialTransitionUnder k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx
            (isFiberedInGroupoids_polarizedSliceProjection B hS hT) ((fgSiteModule B hk).map f))
          (trivialTransitionUnder_isHomLift k B S hS toS hk (polarizedSliceProjection B hS hT) x₀ hx
            (isFiberedInGroupoids_polarizedSliceProjection B hS hT) ((fgSiteModule B hk).map f))
          θ) =
      ((infTarget B hS hT toS hk x₀ hx).map f) (infDerivation B hS hT toS hk x₀ hx θ) := by
  let := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  let := trivialLiftRingAlgebra B hS hT toS hk x₀ hx V
  let := trivialLiftRingAlgebra B hS hT toS hk x₀ hx W
  refine GradedAlgebra.derivationOfAlgHom_naturality _ f _ _ _ _ _ _ fun q => ?_
  apply (bijective_tensorRetract B hS hT toS hk x₀ hx W).1
  rw [tensorRetract_naturality, tensorRetract_infTensorAlgHom, tensorRetract_infTensorAlgHom,
    tensorRetract_naturality, transAlgebraHom_infAlgHom]

/-- The degree-preserving derivations of `P` with values in `P ⊗ k` form a finite-dimensional
space: `P` is of finite type with finite-dimensional graded pieces. -/
theorem finiteDimensional_infTarget_obj (V : FGModuleCat.{u} k) :
    FiniteDimensional k ((infTarget B hS hT toS hk x₀ hx).obj V) := by
  let := specialFiberRingAlgebra B hS hT toS hk x₀ hx
  let := AdmissibleDeformation.sectionGradedAlgebra (R := k) (deformation₀ B hS hT toS hk x₀ hx)
    (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx))
  have : ∀ d, Module.Finite k (AdmissibleDeformation.sectionGrading (R := k)
      (deformation₀ B hS hT toS hk x₀ hx) (ringOfBaseEq (baseEq₀ B hS hT toS hk x₀ hx)) d) :=
    (specialFiberAlgebra B hS hT toS hk x₀ hx).finite
  have : Algebra.FiniteType k (specialFiberRing B hS hT toS hk x₀ hx) :=
    finiteType_specialFiberAlgebra B hS hT toS hk x₀ hx
  exact GradedAlgebra.finiteDimensional_gradedDerivationFunctor_obj _ V

/-- **Stacks 0D4S (2), infinitesimal automorphisms.** For a field `k` and a polarized proper
scheme `x₀` over `Spec k`, the value `Inf_{x₀}(k)` of the functor of infinitesimal automorphisms
of Stacks 07Y9 is finite dimensional. The statement holds for every such functor datum. -/
theorem finiteDimensional_infinitesimalAutomorphismFunctor_obj
    (I : InfinitesimalAutomorphismFunctorData k B S hS toS hk (polarizedSliceProjection B hS hT) x₀
      hx (isFiberedInGroupoids_polarizedSliceProjection B hS hT)) :
    FiniteDimensional k (I.functor.obj ((fgSiteModule B hk).obj (FGModuleCat.of k k))) := by
  have : (fgSiteModule B hk).Additive := ⟨rfl⟩
  have : (fgSiteModule B hk).Linear k := ⟨by intros; rfl⟩
  let F := fgSiteModule B hk ⋙ I.functor
  let t : ∀ V : FGModuleCat.{u} k, F.obj V → (infTarget B hS hT toS hk x₀ hx).obj V :=
    fun V a => infDerivation B hS hT toS hk x₀ hx (I.autEquiv _ a)
  have ht : ∀ {V W : FGModuleCat.{u} k} (f : V ⟶ W) (a : F.obj V),
      t W ((F.map f) a) = ((infTarget B hS hT toS hk x₀ hx).map f) (t V a) := by
    intro V W f a
    change infDerivation B hS hT toS hk x₀ hx
      (I.autEquiv _ (I.functor.map ((fgSiteModule B hk).map f) a)) = _
    rw [I.autEquiv_natural, infAutSetFunctor_map_eq]
    exact infDerivation_naturality B hS hT toS hk x₀ hx f _
  have hlin := isLinearMap_of_natural_on_fgModules k F (infTarget B hS hT toS hk x₀ hx) t ht
  have hinj : Function.Injective (t (FGModuleCat.of k k)) := fun a b hab =>
    (I.autEquiv _).injective (infDerivation_injective B hS hT toS hk x₀ hx hab)
  have := finiteDimensional_infTarget_obj B hS hT toS hk x₀ hx (FGModuleCat.of k k)
  exact FiniteDimensional.of_injective (IsLinearMap.mk' _ hlin) hinj

end AlgebraicGeometry.PolarizedDeformation

end
