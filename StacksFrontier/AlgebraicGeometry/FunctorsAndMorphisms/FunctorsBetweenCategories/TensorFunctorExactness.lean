module

public import Mathlib.RingTheory.Flat.CategoryTheory
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.TensorFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensoring with a bimodule is exact exactly when the bimodule is flat

Let `A` and `B` be algebras over a commutative ring `R`. A module `K` over `A ⊗[R] B` determines
the `R`-linear right exact functor `ModuleCat.tensorFunctor R A B K` from `A`-modules to
`B`-modules which preserves arbitrary direct sums, and every such functor arises this way. This
file records when that functor is exact: exactly when `K` is flat as an `A`-module, the
`A`-module structure being restriction of scalars along `a ↦ a ⊗ₜ 1`.

## Main results

* `ModuleCat.tensorFunctor_preservesFiniteLimits_iff_flat`: the tensor functor is left exact if
  and only if `K` is flat over `A`.
* `ModuleCat.tensorFunctor_exact_iff_flat`: the tensor functor is exact if and only if `K` is
  flat over `A`. Right exactness is unconditional, so this is the previous statement together
  with `ModuleCat.tensorFunctor_preservesFiniteColimits`.

## References

* [Stacks Project, Tag 0GNX](https://stacks.math.columbia.edu/tag/0GNX)
-/

@[expose] public section

namespace ModuleCat

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

section Raw

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
  (K : Type u) [AddCommGroup K] [Module C K] [Module A K] [IsScalarTower A C K]

/-- Base change of an `A`-module to `C` followed by tensoring over `C` with a `C`-module `K` is,
additively, tensoring over `A` with `K`. -/
private noncomputable def rawBaseChangeAddEquiv
    (M : Type u) [AddCommGroup M] [Module A M] :
    ((C ⊗[A] M) ⊗[C] K) ≃+ (M ⊗[A] K) :=
  (TensorProduct.comm C _ K).toAddEquiv.trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A C C K M).toAddEquiv.trans
      (TensorProduct.comm A K M).toAddEquiv)

variable {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

private lemma rawBaseChangeAddEquiv_naturality (h : M →ₗ[A] N) (z : (C ⊗[A] M) ⊗[C] K) :
    rawBaseChangeAddEquiv A C K N (LinearMap.rTensor K (LinearMap.baseChange C h) z) =
      LinearMap.rTensor K h (rawBaseChangeAddEquiv A C K M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul t k =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [TensorProduct.add_tmul]; simp only [map_add, hx, hy]
    | tmul s m => rfl

end Raw

/-- Extension of scalars along `f` followed by tensoring over `C` with a `C`-module `K` and
restriction of scalars along `g` is, in additive groups, tensoring over `A` with the `A`-module
underlying `K`. -/
private noncomputable def extendScalarsTensorForgetIso
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (f : A →+* C) (g : B →+* C)
    (K : ModuleCat.{u} C) :
    (extendScalars f ⋙ (MonoidalCategory.tensoringRight (ModuleCat.{u} C)).obj K ⋙
        restrictScalars g) ⋙ forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u} ≅
      MonoidalCategory.tensorRight ((restrictScalars f).obj K) ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} := by
  letI : Algebra A C := f.toAlgebra
  letI : Module A (K : Type u) := ((restrictScalars f).obj K).isModule
  letI : IsScalarTower A C (K : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine NatIso.ofComponents
    (fun M => (rawBaseChangeAddEquiv A C (K : Type u) (M : Type u)).toAddCommGrpIso) ?_
  intro M N h
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z =>
    rawBaseChangeAddEquiv_naturality A C (K : Type u) h.hom z)

/-- The `A`-module underlying an `A ⊗[R] B`-module, by restriction of scalars along `a ↦ a ⊗ₜ 1`.
-/
private noncomputable abbrev tensorFunctorLeftRestrict
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (K : ModuleCat.{u} (A ⊗[R] B)) : ModuleCat.{u} A :=
  (restrictScalars
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).obj K

/-- Tensoring with an `A ⊗[R] B`-module `K`, read in additive groups, is tensoring over `A` with
`K` viewed as an `A`-module. -/
private noncomputable def tensorFunctorForgetTensorRightIso
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (K : ModuleCat.{u} (A ⊗[R] B)) :
    tensorFunctor R A B K ⋙ forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u} ≅
      MonoidalCategory.tensorRight (tensorFunctorLeftRestrict R A B K) ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} := by
  unfold tensorFunctor
  exact extendScalarsTensorForgetIso _ _ K

/-- Finite limit preservation transfers along an isomorphism of the functors composed with the
forgetful functors to abelian groups. -/
private theorem preservesFiniteLimits_of_forget₂_iso {A B B' : Type u} [CommRing A] [CommRing B]
    [CommRing B'] {F : ModuleCat.{u} A ⥤ ModuleCat.{u} B} {G : ModuleCat.{u} A ⥤ ModuleCat.{u} B'}
    (e : F ⋙ forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u} ≅
      G ⋙ forget₂ (ModuleCat.{u} B') AddCommGrpCat.{u}) [PreservesFiniteLimits F] :
    PreservesFiniteLimits G := by
  let : PreservesFiniteLimits (F ⋙ forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}) :=
    comp_preservesFiniteLimits _ _
  let : PreservesFiniteLimits (G ⋙ forget₂ (ModuleCat.{u} B') AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso e
  exact preservesFiniteLimits_of_reflects_of_preserves G
    (forget₂ (ModuleCat.{u} B') AddCommGrpCat.{u})

/-- Tensoring with an `A ⊗[R] B`-module `K` is a left exact functor from `A`-modules to `B`-modules
if and only if `K` is flat as an `A`-module. -/
@[ega "0 6.1.1" "more general"]
public theorem tensorFunctor_preservesFiniteLimits_iff_flat
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (K : ModuleCat.{u} (A ⊗[R] B)) :
    PreservesFiniteLimits (tensorFunctor R A B K) ↔
      Module.Flat A ((restrictScalars
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).obj K) := by
  rw [Module.Flat.iff_preservesFiniteLimits_tensorRight]
  constructor
  · intro _
    exact preservesFiniteLimits_of_forget₂_iso (tensorFunctorForgetTensorRightIso R A B K)
  · intro _
    exact preservesFiniteLimits_of_forget₂_iso (tensorFunctorForgetTensorRightIso R A B K).symm

/-- Tensoring with an `A ⊗[R] B`-module `K` is an exact functor from `A`-modules to `B`-modules if
and only if `K` is flat as an `A`-module. -/
@[stacks 0GNX, ega "0 6.1.1" "more general"]
public theorem tensorFunctor_exact_iff_flat
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (K : ModuleCat.{u} (A ⊗[R] B)) :
    exactFunctor (ModuleCat.{u} A) (ModuleCat.{u} B) (tensorFunctor R A B K) ↔
      Module.Flat A ((restrictScalars
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))).obj K) := by
  rw [exactFunctor_iff]
  exact ⟨fun h => (tensorFunctor_preservesFiniteLimits_iff_flat R A B K).mp h.1, fun h =>
    ⟨(tensorFunctor_preservesFiniteLimits_iff_flat R A B K).mpr h,
      tensorFunctor_preservesFiniteColimits R A B K⟩⟩

end ModuleCat
