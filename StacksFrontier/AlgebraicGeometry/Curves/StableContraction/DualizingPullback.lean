module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafTrace
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.TrivialDirectImage
public import StacksFrontier.AlgebraicGeometry.FreeStalkBasis.LocalRank
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.ZeroDimensionalSupport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularityGlobalGeneration
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pulling back the dualizing sheaf along a contraction

Let `k` be a field and `c : X ⟶ Y` a morphism of proper `k`-schemes of dimension at most one
with `𝒪_Y = c_*𝒪_X` and `R^1 c_*𝒪_X = 0`, `X` reduced. This file carries out the argument of
[Stacks, Tag 0E7P] for the dualizing sheaves `ω_X`, `ω_Y` of [Stacks, Tag 0BS2], under the
assumption that both are finite locally free of rank one with `χ(ω) = -χ(𝒪)`:

1. the trace of `Rc_* ⊣ c^×` splits `c_*(b)` for a map `b : c^*ω_Y ⟶ ω_X`
   (`Stacks.Duality.exists_pushforward_map_comp_eq_id_of_isZero`);
2. on a reduced scheme a section killed by `b^{⊗ (n+1)}` is killed by `b ⊗ 𝟙`, and `b ⊗ 𝟙` is
   injective on global sections by the projection formula, so `b^{⊗ m}` is injective on global
   sections (`injective_app_top_tensorSheafNPowMap`);
3. Leray and the multiplicativity of the degree give `χ((c^*ω_Y)^{⊗ m}) = χ(ω_X^{⊗ m})`, so with
   `H^1(X, ω_X^{⊗ m}) = 0` the map `b^{⊗ m}` is bijective on global sections, hence surjective
   when `ω_X^{⊗ m}` is globally generated, hence `b` is an isomorphism
   (`isIso_of_epi_tensorSheafNPowMap`).

## Main results

* `Stacks.Curves.DualizingPullback.injective_app_top_tensorSheafNPowMap`.
* `Stacks.Curves.DualizingPullback.eulerCharacteristic_tensorSheafNPow`:
  `χ(ℒ^{⊗ n}) = n (χ(ℒ) - χ(𝒪_X)) + χ(𝒪_X)`.
* `Stacks.Curves.DualizingPullback.eulerCharacteristic_eq_of_derivedPushforwardIso`: Leray for a
  module with `Rc_*(ℱ[0]) = 𝒢[0]`.
* `Stacks.Curves.DualizingPullback.nonempty_pullback_iso_of_isFiniteLocallyFreeOfRank`: the
  argument of [Stacks, Tag 0E7P] for invertible dualizing sheaves with `χ(ω) = -χ(𝒪)`.

## Implementation notes

Tensor powers are `AlgebraicGeometry.tensorSheafNPow`, whose stalks are tensor powers of stalks
([Stacks, Tag 01CB]); all local computations are made on stalks, where a morphism between
modules free of rank one is a scalar multiple of an isomorphism.

## References

* [Stacks Project, Tag 0E7P](https://stacks.math.columbia.edu/tag/0E7P)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.Curves.DualizingPullback

section Algebra

variable {R : Type*} [CommRing R] {A B C D : Type*} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

/-- A linear map between modules free of rank one is a scalar multiple of a linear
isomorphism. -/
theorem exists_eq_smul_linearEquiv (bA : Module.Basis (Fin 1) R A) (bB : Module.Basis (Fin 1) R B)
    (φ : A →ₗ[R] B) : ∃ e : A ≃ₗ[R] B, φ = (bB.repr (φ (bA 0)) 0) • e.toLinearMap := by
  refine ⟨bA.equiv bB (Equiv.refl _), bA.ext fun i => ?_⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
    Equiv.refl_apply]
  conv_lhs => rw [← bB.sum_repr (φ (bA 0))]
  simp

/-- **In a module free of rank one over a reduced ring, `g^{k+1} z = 0` forces `g z = 0`.** -/
theorem smul_eq_zero_of_pow_smul_eq_zero [IsReduced R] (bA : Module.Basis (Fin 1) R A) (g : R)
    (z : A) (k : ℕ) (h : g ^ (k + 1) • z = 0) : g • z = 0 := by
  have hz : z = bA.repr z 0 • bA 0 := by
    conv_lhs => rw [← bA.sum_repr z]
    simp
  have hb : ∀ r : R, r • bA 0 = 0 → r = 0 := fun r hr => by
    simpa using congrArg (fun v => bA.repr v 0) hr
  have h1 : g ^ (k + 1) * bA.repr z 0 = 0 := by
    apply hb
    rw [mul_smul, ← hz, h]
  have h2 : (g * bA.repr z 0) ^ (k + 1) = 0 := by
    rw [mul_pow, pow_succ (bA.repr z 0), ← mul_assoc, mul_comm _ (bA.repr z 0 ^ k), mul_assoc,
      h1, mul_zero]
  rw [hz, smul_smul, IsReduced.eq_zero _ ⟨_, h2⟩, zero_smul]

/-- The tensor product of two scalar multiples of linear isomorphisms is the product scalar
times their tensor product. -/
theorem map_smul_smul_linearEquiv (g h : R) (e : A ≃ₗ[R] B) (e' : C ≃ₗ[R] D) :
    TensorProduct.map (g • e.toLinearMap) (h • e'.toLinearMap) =
      (g * h) • (TensorProduct.congr e e').toLinearMap := by
  rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul]
  rfl

/-- A scalar multiple `g^{k+1}·E` of a linear isomorphism out of a module free of rank one which is
surjective forces `g` to be a unit. -/
theorem isUnit_of_surjective_pow_smul (bA : Module.Basis (Fin 1) R A) (g : R) (k : ℕ)
    (E : A ≃ₗ[R] B) (h : Function.Surjective (g ^ (k + 1) • E.toLinearMap)) : IsUnit g := by
  obtain ⟨a, ha⟩ := h (E (bA 0))
  simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, ← map_smul] at ha
  have ha' := congrArg (fun v => bA.repr v 0) (E.injective ha)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
    Finsupp.single_eq_same] at ha'
  exact (isUnit_pow_iff (Nat.succ_ne_zero k)).mp (isUnit_iff_exists_inv.mpr ⟨_, ha'⟩)

/-- A unit multiple of a linear isomorphism is bijective. -/
theorem bijective_smul_linearEquiv {g : R} (hg : IsUnit g) (e : A ≃ₗ[R] B) :
    Function.Bijective (g • e.toLinearMap) := by
  obtain ⟨u, rfl⟩ := hg
  have : (u : R) • e.toLinearMap = (e.trans (LinearEquiv.smulOfUnit u)).toLinearMap := by
    ext a
    simp [LinearEquiv.smulOfUnit, Units.smul_def]
  rw [this]
  exact LinearEquiv.bijective _

end Algebra

section Stalks

variable {X : Scheme.{u}}

local notation "𝒪" => structureSheafRing X.toRingedSpace

/-- The germ of the image of a section is the image of its germ. -/
theorem stalkMapL_grpGerm {F F' : SheafOfModules.{u} 𝒪} (φ : F ⟶ F') (x : X) (U : X.Opens)
    (hx : x ∈ U) (s : F.val.obj (op U)) :
    stalkMapL X.toRingedSpace F.val F'.val φ.val x (grpGerm X.toRingedSpace F.val x U hx s) =
      grpGerm X.toRingedSpace F'.val x U hx ((φ.val.app (op U)).hom s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
    ((PresheafOfModules.toPresheaf (O X.toRingedSpace)).map φ.val) s

/-- A section of a sheaf of modules all of whose germs vanish is zero. -/
theorem eq_zero_of_grpGerm_eq_zero (F : SheafOfModules.{u} 𝒪) (U : X.Opens) (s : F.val.obj (op U))
    (h : ∀ x (hx : x ∈ U), grpGerm X.toRingedSpace F.val x U hx s = 0) : s = 0 :=
  TopCat.Presheaf.section_ext (C := AddCommGrpCat.{u})
    ⟨(F : X.Modules).val.presheaf, (F : X.Modules).isSheaf⟩ U s 0
    fun x hx => (h x hx).trans (map_zero _).symm

/-- **A reducedness criterion for vanishing on sections.** Let `𝒜` be finite locally free of rank
one on a reduced scheme and let `β : 𝒜 ⟶ ℬ`, `ε : 𝒜 ⟶ 𝒞` be such that at every point `x`
there is `g ∈ 𝒪_{X,x}` with `β_x = g^{k+1}·Φ` and `ε_x = g·Ψ` for linear isomorphisms `Φ`, `Ψ`.
Then every section killed by `β` is killed by `ε`. -/
theorem app_eq_zero_of_app_eq_zero [IsReduced X] {A B C : SheafOfModules.{u} 𝒪}
    (hA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := 𝒪) A 1) (β : A ⟶ B)
    (ε : A ⟶ C) (k : ℕ)
    (h : ∀ x : X, ∃ (g : ringStalk X.toRingedSpace x)
      (Φ : grpStalk X.toRingedSpace A.val x ≃ₗ[ringStalk X.toRingedSpace x]
        grpStalk X.toRingedSpace B.val x)
      (Ψ : grpStalk X.toRingedSpace A.val x ≃ₗ[ringStalk X.toRingedSpace x]
        grpStalk X.toRingedSpace C.val x),
      stalkMapL X.toRingedSpace A.val B.val β.val x = g ^ (k + 1) • Φ.toLinearMap ∧
        stalkMapL X.toRingedSpace A.val C.val ε.val x = g • Ψ.toLinearMap)
    (U : X.Opens) (s : A.val.obj (op U)) (hs : (β.val.app (op U)).hom s = 0) :
    (ε.val.app (op U)).hom s = 0 := by
  refine eq_zero_of_grpGerm_eq_zero C U _ fun x hx => ?_
  obtain ⟨g, Φ, Ψ, hβ, hε⟩ := h x
  have : IsReduced (ringStalk X.toRingedSpace x) :=
    inferInstanceAs (IsReduced (X.presheaf.stalk x))
  obtain ⟨bA⟩ := AlgebraicGeometry.nonempty_stalkBasis_of_isFiniteLocallyFreeOfRank A 1 hA x
  set z := grpGerm X.toRingedSpace A.val x U hx s
  have h1 : g ^ (k + 1) • z = 0 := by
    have h2 := stalkMapL_grpGerm β x U hx s
    rw [hs, map_zero, hβ] at h2
    simp only [LinearMap.smul_apply, LinearEquiv.coe_coe] at h2
    rw [← map_smul] at h2
    exact (LinearEquiv.map_eq_zero_iff Φ).mp h2
  have h3 := smul_eq_zero_of_pow_smul_eq_zero bA g z k h1
  rw [← stalkMapL_grpGerm ε x U hx s, hε]
  simp only [LinearMap.smul_apply, LinearEquiv.coe_coe]
  rw [← map_smul, h3, map_zero]

/-- The stalk of the tensor product of two morphisms is the tensor product of their stalks,
through the identifications `(ℱ ⊗ 𝒢)_x = ℱ_x ⊗ 𝒢_x` ([Stacks, Tag 01CB]). -/
theorem stalkMapL_tensorSheafMap {F F' G G' : SheafOfModules.{u} 𝒪} (φ : F ⟶ F') (ψ : G ⟶ G')
    (x : X) :
    letI := stalkModule X.toRingedSpace (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G).val x
    letI := stalkModule X.toRingedSpace (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F').obj G').val x
    stalkMapL X.toRingedSpace _ _
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          ((φ, ψ) : (_, _) ⟶ (_, _))).val x =
      (tensorStalkIso X.toRingedSpace x F' G').symm.toLinearMap ∘ₗ
        TensorProduct.map (stalkMapL X.toRingedSpace F.val F'.val φ.val x)
          (stalkMapL X.toRingedSpace G.val G'.val ψ.val x) ∘ₗ
        (tensorStalkIso X.toRingedSpace x F G).toLinearMap := by
  let := stalkModule X.toRingedSpace (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G).val x
  let := stalkModule X.toRingedSpace (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F').obj G').val x
  have h := tensorStalkIso_natural X.toRingedSpace x F G F' G' φ ψ
  let := stalkModule X.toRingedSpace ((Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj (F, G)).val x
  let := stalkModule X.toRingedSpace ((Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj (F', G')).val x
  refine LinearMap.ext fun m => (tensorStalkIso X.toRingedSpace x F' G').injective ?_
  have hm := LinearMap.congr_fun h m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hm ⊢
  rw [LinearEquiv.apply_symm_apply]
  exact hm.symm

/-- If the stalk maps of `φ` and `ψ` are scalar multiples `c·e`, `d·e'` of linear isomorphisms,
the stalk map of `φ ⊗ ψ` is `(cd)·E` for a linear isomorphism `E`. -/
theorem exists_stalkMapL_tensorSheafMap_eq_smul {F F' G G' : SheafOfModules.{u} 𝒪}
    (φ : F ⟶ F') (ψ : G ⟶ G') (x : X) (c d : ringStalk X.toRingedSpace x)
    (e : grpStalk X.toRingedSpace F.val x ≃ₗ[ringStalk X.toRingedSpace x]
      grpStalk X.toRingedSpace F'.val x)
    (e' : grpStalk X.toRingedSpace G.val x ≃ₗ[ringStalk X.toRingedSpace x]
      grpStalk X.toRingedSpace G'.val x)
    (hφ : stalkMapL X.toRingedSpace F.val F'.val φ.val x = c • e.toLinearMap)
    (hψ : stalkMapL X.toRingedSpace G.val G'.val ψ.val x = d • e'.toLinearMap) :
    letI := stalkModule X.toRingedSpace (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G).val x
    letI := stalkModule X.toRingedSpace (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F').obj G').val x
    ∃ E : grpStalk X.toRingedSpace (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G).val x
        ≃ₗ[ringStalk X.toRingedSpace x]
        grpStalk X.toRingedSpace (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F').obj G').val x,
      stalkMapL X.toRingedSpace _ _
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
            ((φ, ψ) : (_, _) ⟶ (_, _))).val x =
        (c * d) • E.toLinearMap := by
  let := stalkModule X.toRingedSpace (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G).val x
  let := stalkModule X.toRingedSpace (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F').obj G').val x
  refine ⟨(tensorStalkIso X.toRingedSpace x F G).trans ((TensorProduct.congr e e').trans
    (tensorStalkIso X.toRingedSpace x F' G').symm), ?_⟩
  rw [stalkMapL_tensorSheafMap, hφ, hψ, map_smul_smul_linearEquiv, LinearMap.smul_comp,
    LinearMap.comp_smul]
  rfl

/-- The stalk map of a composite is the composite of the stalk maps. -/
theorem stalkMapL_comp {F G H : SheafOfModules.{u} 𝒪} (φ : F ⟶ G) (ψ : G ⟶ H) (x : X) :
    stalkMapL X.toRingedSpace F.val H.val (φ ≫ ψ).val x =
      stalkMapL X.toRingedSpace G.val H.val ψ.val x ∘ₗ
        stalkMapL X.toRingedSpace F.val G.val φ.val x := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨U, hU, t, rfl⟩ := Stacks.SheafOfModules.exists_grpGerm_eq X.toRingedSpace F.val x m
  rw [LinearMap.comp_apply, Stacks.SheafOfModules.stalkMapL_germ,
    Stacks.SheafOfModules.stalkMapL_germ, Stacks.SheafOfModules.stalkMapL_germ]
  rfl

/-- The stalk map of the identity is the identity. -/
theorem stalkMapL_id (F : SheafOfModules.{u} 𝒪) (x : X) :
    stalkMapL X.toRingedSpace F.val F.val (SheafOfModules.Hom.val (𝟙 F)) x = LinearMap.id := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨U, hU, t, rfl⟩ := Stacks.SheafOfModules.exists_grpGerm_eq X.toRingedSpace F.val x m
  rw [Stacks.SheafOfModules.stalkMapL_germ]
  rfl

/-- **The `n`-th tensor power of a morphism**, `b^{⊗ n} : ℒ^{⊗ n} ⟶ ℳ^{⊗ n}`, for the tensor
powers `AlgebraicGeometry.tensorSheafNPow`. -/
def tensorSheafNPowMap {L M : SheafOfModules.{u} 𝒪} (b : L ⟶ M) :
    (n : ℕ) → (tensorSheafNPow X.toRingedSpace L n ⟶ tensorSheafNPow X.toRingedSpace M n)
  | 0 => 𝟙 (SheafOfModules.unit 𝒪)
  | n + 1 =>
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).map
        (tensorSheafNPowMap b n)).app L ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
        (tensorSheafNPow X.toRingedSpace M n)).map b

/-- If the stalk map of `b` is `g·e` for a linear isomorphism `e`, the stalk map of `b^{⊗ n}` is
`g^n·E` for a linear isomorphism `E`. -/
theorem exists_stalkMapL_tensorSheafNPowMap_eq_smul {L M : SheafOfModules.{u} 𝒪} (b : L ⟶ M)
    (x : X) (g : ringStalk X.toRingedSpace x)
    (e : grpStalk X.toRingedSpace L.val x ≃ₗ[ringStalk X.toRingedSpace x]
      grpStalk X.toRingedSpace M.val x)
    (hb : stalkMapL X.toRingedSpace L.val M.val b.val x = g • e.toLinearMap) (n : ℕ) :
    ∃ E : grpStalk X.toRingedSpace (tensorSheafNPow X.toRingedSpace L n).val x ≃ₗ[ringStalk
        X.toRingedSpace x] grpStalk X.toRingedSpace (tensorSheafNPow X.toRingedSpace M n).val x,
      stalkMapL X.toRingedSpace _ _ (tensorSheafNPowMap b n).val x = g ^ n • E.toLinearMap := by
  induction n with
  | zero =>
    refine ⟨LinearEquiv.refl _ _, ?_⟩
    rw [pow_zero, one_smul]
    exact stalkMapL_id _ x
  | succ n ih =>
    obtain ⟨E, hE⟩ := ih
    obtain ⟨E', hE'⟩ := exists_stalkMapL_tensorSheafMap_eq_smul (tensorSheafNPowMap b n) b x _ _
      E e hE hb
    exact ⟨E', by rwa [pow_succ]⟩

/-- The stalk map of a morphism between modules free of rank one at a point is a scalar multiple
of a linear isomorphism. -/
theorem exists_stalkMapL_eq_smul {L M : SheafOfModules.{u} 𝒪}
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := 𝒪) L 1)
    (hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := 𝒪) M 1) (b : L ⟶ M) (x : X) :
    ∃ (g : ringStalk X.toRingedSpace x)
      (e : grpStalk X.toRingedSpace L.val x ≃ₗ[ringStalk X.toRingedSpace x]
        grpStalk X.toRingedSpace M.val x),
      stalkMapL X.toRingedSpace L.val M.val b.val x = g • e.toLinearMap := by
  obtain ⟨bL⟩ := AlgebraicGeometry.nonempty_stalkBasis_of_isFiniteLocallyFreeOfRank L 1 hL x
  obtain ⟨bM⟩ := AlgebraicGeometry.nonempty_stalkBasis_of_isFiniteLocallyFreeOfRank M 1 hM x
  obtain ⟨e, he⟩ := exists_eq_smul_linearEquiv bL bM (stalkMapL X.toRingedSpace L.val M.val b.val x)
  exact ⟨_, e, he⟩

/-- `ℒ^{⊗ (n+1)} ≅ ℒ ⊗ ℒ^{⊗ n}`, by the unit and associativity constraints. -/
def tensorSheafNPowSuccIso (L : SheafOfModules.{u} 𝒪) :
    (n : ℕ) → (tensorSheafNPow X.toRingedSpace L (n + 1) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
        L).obj (tensorSheafNPow X.toRingedSpace L n))
  | 0 => tensorSheafUnitLeft X.toRingedSpace L ≪≫ (tensorSheafUnitRight X.toRingedSpace L).symm
  | n + 1 => tensorSheafMapIso X.toRingedSpace (tensorSheafNPowSuccIso L n) (Iso.refl L) ≪≫
    tensorSheafAssoc X.toRingedSpace L (tensorSheafNPow X.toRingedSpace L n) L

/-- The component of `sheafTensor.map b` at `P` is the tensor of `b` with `𝟙 P`. -/
private theorem sheafTensor_map_app_eq_uncurry_map {L M : SheafOfModules.{u} 𝒪} (b : L ⟶ M)
    (P : SheafOfModules.{u} 𝒪) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).map b).app P =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        ((b, 𝟙 P) : (_, _) ⟶ (_, _)) :=
  (Category.comp_id _).symm.trans
    (congrArg (fun t => ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).map b).app P ≫ t)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj M).map_id _).symm)

/-- **A section killed by `b^{⊗ (n+1)}` is killed by `b ⊗ 𝟙`**, on a reduced scheme, for a
morphism `b : ℒ ⟶ ℳ` of modules finite locally free of rank one. At a point `b` is `g·e`, so
`b^{⊗ (n+1)}` is `g^{n+1}` times an isomorphism and `b ⊗ 𝟙` is `g` times one, and `g^{n+1} z = 0`
forces `g z = 0` in a free module of rank one over a reduced ring. -/
theorem app_tensorSheafMap_eq_zero [IsReduced X] {L M : SheafOfModules.{u} 𝒪} {n : ℕ}
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := 𝒪) L 1)
    (hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := 𝒪) M 1)
    (hLn : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := 𝒪)
      (tensorSheafNPow X.toRingedSpace L (n + 1)) 1)
    (b : L ⟶ M) (U : X.Opens) (s : (tensorSheafNPow X.toRingedSpace L (n + 1)).val.obj (op U))
    (hs : ((tensorSheafNPowMap b (n + 1)).val.app (op U)).hom s = 0) :
    (((tensorSheafNPowSuccIso L n).hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).map b).app
        (tensorSheafNPow X.toRingedSpace L n)).val.app
        (op U)).hom s = 0 := by
  refine app_eq_zero_of_app_eq_zero hLn _ _ n (fun x => ?_) U s hs
  let := stalkModule X.toRingedSpace
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
      (tensorSheafNPow X.toRingedSpace L n)).val x
  let := stalkModule X.toRingedSpace
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj M).obj
      (tensorSheafNPow X.toRingedSpace L n)).val x
  let := stalkModule X.toRingedSpace
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj
      (L, tensorSheafNPow X.toRingedSpace L n)).val x
  let := stalkModule X.toRingedSpace
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj
      (M, tensorSheafNPow X.toRingedSpace L n)).val x
  obtain ⟨g, e, he⟩ := exists_stalkMapL_eq_smul hL hM b x
  obtain ⟨E, hE⟩ := exists_stalkMapL_tensorSheafNPowMap_eq_smul b x g e he (n + 1)
  obtain ⟨E', hE'⟩ := exists_stalkMapL_tensorSheafMap_eq_smul b
    (𝟙 (tensorSheafNPow X.toRingedSpace L n)) x g 1 e (LinearEquiv.refl _ _) he
    (by rw [one_smul]; exact stalkMapL_id _ x)
  refine ⟨g, E, (Stacks.SheafOfModules.stalkLinearEquiv X.toRingedSpace
    (tensorSheafNPowSuccIso L n) x).trans E', hE, ?_⟩
  refine (stalkMapL_comp _ _ x).trans ?_
  rw [sheafTensor_map_app_eq_uncurry_map]
  refine (congrArg (fun t => t ∘ₗ _) hE').trans ?_
  rw [mul_one, LinearMap.smul_comp]
  rfl

end Stalks

section Pullback

variable {X Y : Scheme.{u}}

/-- A tensor power of a module finite locally free of rank one is finite locally free of rank
one. -/
theorem isFiniteLocallyFreeOfRank_tensorSheafNPow (L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] (n : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (tensorSheafNPow X.toRingedSpace L n : X.Modules) 1 := by
  induction n with
  | zero => exact AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit X
  | succ n ih =>
    have := @AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X
      (tensorSheafNPow X.toRingedSpace L n : X.Modules) L 1 1 ih ‹_›
    rwa [mul_one] at this

/-- Pullback commutes with tensor powers: `c^*(𝒩^{⊗ n}) ≅ (c^*𝒩)^{⊗ n}`. -/
def pullbackTensorSheafNPowIso (c : X ⟶ Y) (N : Y.Modules) :
    (n : ℕ) → ((Scheme.Modules.pullback c).obj (tensorSheafNPow Y.toRingedSpace N n : Y.Modules) ≅
      (tensorSheafNPow X.toRingedSpace ((Scheme.Modules.pullback c).obj N) n : X.Modules))
  | 0 => Scheme.Modules.pullbackUnitIso c
  | n + 1 => Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso c
      (tensorSheafNPow Y.toRingedSpace N n : Y.Modules) N ≪≫
    tensorSheafMapIso X.toRingedSpace (pullbackTensorSheafNPowIso c N n) (Iso.refl _)

/-- A module finite locally free of rank one is invertible ([Stacks, Tag 0B8M]), in the spelling
the projection formula of [Stacks, Tag 01E8] takes. -/
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one (Z : Scheme.{u}) (M : Z.Modules)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1] :
    Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
    (Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one Z M h)

/-- `b ⊗ 𝟙_P` is `b ⊗ 𝟙_Q` conjugated by an isomorphism `P ≅ Q` in the second factor. -/
theorem tensorSheafMap_id_eq_conj
    {L M P Q : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (b : L ⟶ M) (e : P ≅ Q) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).map b).app P =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).map e.hom ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).map b).app Q ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj M).map e.inv := by
  have h := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).map b).naturality e.hom
  rw [reassoc_of% h]
  exact (Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (Functor.mapIso _ e).hom_inv_id.symm)

/-- A morphism of modules with a left inverse is injective on sections. -/
theorem injective_app_of_comp_eq_id {Z : Scheme.{u}} {A B : Z.Modules} (f : A ⟶ B) (g : B ⟶ A)
    (hfg : f ≫ g = 𝟙 A) (U : Z.Opensᵒᵖ) : Function.Injective (f.val.app U).hom :=
  Function.LeftInverse.injective (g := (g.val.app U).hom) fun x =>
    congrArg (fun φ : A ⟶ A => (φ.val.app U).hom x) hfg

/-- An isomorphism of modules is injective on sections. -/
private theorem injective_app_of_iso {Z : Scheme.{u}} {A B : Z.Modules} (e : A ≅ B)
    (U : Z.Opensᵒᵖ) : Function.Injective (e.hom.val.app U).hom :=
  injective_app_of_comp_eq_id e.hom e.inv e.hom_inv_id U

/-- **`b ⊗ 𝟙` is injective on global sections when `c_*(b)` is split mono**, for a tensor factor
isomorphic to a pullback `c^*𝒩` of a module finite locally free of rank one: the projection
formula ([Stacks, Tag 01E8]) identifies `c_*(b ⊗ 𝟙_{c^*𝒩})` with `c_*(b) ⊗ 𝟙_{𝒩}`, which is again
split mono. -/
theorem injective_app_top_tensorSheafMap (c : X ⟶ Y) {L M : X.Modules} (b : L ⟶ M)
    (r : (Scheme.Modules.pushforward c).obj M ⟶ (Scheme.Modules.pushforward c).obj L)
    (hr : (Scheme.Modules.pushforward c).map b ≫ r = 𝟙 _) (N : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1] (P : X.Modules)
    (e : P ≅ (Scheme.Modules.pullback c).obj N) :
    Function.Injective ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).map b).app P).val.app (op ⊤)).hom := by
  have := isInvertible_of_isFiniteLocallyFreeOfRank_one Y N
  let F := Scheme.Modules.pushforward c
  let T := Stacks.ProjectionFormula.tensorRightInvertible Y N
  let π := Stacks.ProjectionFormula.pushforwardTensorRightNatIso c N
  let b' := (Stacks.ProjectionFormula.tensorRightInvertible X
    ((Scheme.Modules.pullback c).obj N)).map b
  have hnat : F.map b' ≫ π.hom.app M = π.hom.app L ≫ T.map (F.map b) :=
    π.hom.naturality b
  have hT : Function.Injective ((T.map (F.map b)).val.app (op ⊤)).hom :=
    injective_app_of_comp_eq_id _ (T.map r) (by rw [← T.map_comp, hr, T.map_id]) (op ⊤)
  have hπ : Function.Injective ((π.hom.app L).val.app (op ⊤)).hom :=
    injective_app_of_iso (π.app L) (op ⊤)
  have hcomp : Function.Injective (((F.map b' ≫ π.hom.app M)).val.app (op ⊤)).hom := by
    rw [hnat]
    exact hT.comp hπ
  have hb' : Function.Injective (b'.val.app (op ⊤)).hom :=
    Function.Injective.of_comp (f := ((π.hom.app M).val.app (op ⊤)).hom) hcomp
  rw [show b' = _ from (sheafTensor_map_app_eq_uncurry_map b _).symm] at hb'
  have hfac := congrArg (fun φ => (φ.val.app (op ⊤)).hom) (tensorSheafMap_id_eq_conj b e)
  have h1 := injective_app_of_iso (Z := X)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).mapIso e) (op ⊤)
  have h2 := injective_app_of_iso (Z := X)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj M).mapIso e).symm (op ⊤)
  exact hfac ▸ h2.comp (hb'.comp h1)

/-- **`b^{⊗ m}` is injective on global sections** for `m ≥ 1`, on a reduced scheme, when
`b : c^*𝒩 ⟶ ℳ` is a morphism of modules finite locally free of rank one with `c_*(b)` split mono.
A global section killed by `b^{⊗ (n+1)}` is killed by `b ⊗ 𝟙_{(c^*𝒩)^{⊗ n}}`
(`app_tensorSheafMap_eq_zero`, which is where reducedness enters), and `b ⊗ 𝟙` is injective on
global sections by the projection formula (`injective_app_top_tensorSheafMap`). -/
theorem injective_app_top_tensorSheafNPowMap [IsReduced X] (c : X ⟶ Y) (N : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1] (M : X.Modules)
    [hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1]
    (b : (Scheme.Modules.pullback c).obj N ⟶ M)
    (r : (Scheme.Modules.pushforward c).obj M ⟶
      (Scheme.Modules.pushforward c).obj ((Scheme.Modules.pullback c).obj N))
    (hr : (Scheme.Modules.pushforward c).map b ≫ r = 𝟙 _) (n : ℕ) :
    Function.Injective ((tensorSheafNPowMap b (n + 1)).val.app (op ⊤)).hom := by
  have hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback c).obj N) 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback c N 1
  have hLn := isFiniteLocallyFreeOfRank_tensorSheafNPow ((Scheme.Modules.pullback c).obj N) (n + 1)
  have hNn := isFiniteLocallyFreeOfRank_tensorSheafNPow N n
  let σ := tensorSheafNPowSuccIso ((Scheme.Modules.pullback c).obj N : SheafOfModules.{u}
    (structureSheafRing X.toRingedSpace)) n
  have hσ := injective_app_of_iso (Z := X) σ (op ⊤)
  have hε := @injective_app_top_tensorSheafMap X Y c _ _ b r hr
    (tensorSheafNPow Y.toRingedSpace N n) hNn
    (tensorSheafNPow X.toRingedSpace ((Scheme.Modules.pullback c).obj N) n)
    (pullbackTensorSheafNPowIso c N n).symm
  rw [injective_iff_map_eq_zero]
  intro s hs
  have h := app_tensorSheafMap_eq_zero hL hM hLn b ⊤ s hs
  exact hσ ((hε (h.trans (map_zero _).symm)).trans (map_zero _).symm)

end Pullback

section Generation

variable {X : Scheme.{u}}

/-- **A morphism onto a module generated by a family of sections which is surjective on sections
is an epimorphism.** Every member of the generating family lifts. -/
theorem epi_of_surjective_sectionsMap {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {M N : SheafOfModules.{u} R}
    (σ : N.GeneratingSections) (φ : M ⟶ N)
    (h : Function.Surjective (SheafOfModules.sectionsMap φ)) :
    Epi φ := by
  choose t ht using fun i => h (σ.s i)
  have hfac : M.freeHomEquiv.symm t ≫ φ = N.freeHomEquiv.symm σ.s := by
    rw [SheafOfModules.freeHomEquiv_symm_comp]
    exact congrArg N.freeHomEquiv.symm (funext ht)
  have : Epi (M.freeHomEquiv.symm t ≫ φ) := by
    rw [hfac]
    exact σ.epi
  exact epi_of_epi (M.freeHomEquiv.symm t) φ

/-- **If `b^{⊗ (n+1)}` is an epimorphism then `b` is an isomorphism**, for a morphism of modules
finite locally free of rank one: at a point `b` is `g·e` and `b^{⊗ (n+1)}` is `g^{n+1}` times an
isomorphism, so surjectivity makes `g` a unit. -/
theorem isIso_of_epi_tensorSheafNPowMap {L M : X.Modules}
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1)
    (hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1) (b : L ⟶ M) (n : ℕ)
    (h' : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _ (tensorSheafNPowMap b (n + 1))) :
    IsIso b := by
  have hLn := isFiniteLocallyFreeOfRank_tensorSheafNPow L (n + 1)
  have hsurj := (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap _).1 h'
  have key : ∀ x : X, Function.Bijective
      (stalkMapL X.toRingedSpace L.val M.val b.val x) := by
    intro x
    obtain ⟨g, e, he⟩ := exists_stalkMapL_eq_smul hL hM b x
    obtain ⟨E, hE⟩ := exists_stalkMapL_tensorSheafNPowMap_eq_smul b x g e he (n + 1)
    obtain ⟨bA⟩ := AlgebraicGeometry.nonempty_stalkBasis_of_isFiniteLocallyFreeOfRank _ 1 hLn x
    have hs : Function.Surjective (g ^ (n + 1) • E.toLinearMap) := by
      rw [← hE]
      exact hsurj x
    rw [he]
    exact bijective_smul_linearEquiv (isUnit_of_surjective_pow_smul bA g n E hs) e
  have : @IsIso (SheafOfModules.{u} X.ringCatSheaf) _ _ _ b :=
    (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap b).2 key
  exact ⟨⟨this.out.choose, this.out.choose_spec⟩⟩

end Generation

section Leray

open Stacks.Duality

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (c : X ⟶ Y) (g : Y ⟶ Spec (.of k))

/-- **Leray for a morphism with `Rc_*(ℱ[0]) = 𝒢[0]`**: `Hⁱ(X, ℱ) ≅ Hⁱ(Y, 𝒢)` over `k`, through
`RΓ(X, -) = RΓ(Spec k, R(c ≫ g)_* -)` and `R(c ≫ g)_* = Rg_* ∘ Rc_*`. -/
def cohomologyOverFieldIsoOfDerivedPushforwardIso (F : X.Modules) (G : Y.Modules)
    (θ : (derivedPushforward c).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.singleFunctor Y.Modules 0).obj G) (n : ℕ) :
    cohomologyOverField k (c ≫ g) F n ≅ cohomologyOverField k g G n :=
  cohomologyOverFieldIsoDerivedCohomologyOverField k (c ≫ g) F n ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n : ℤ)).mapIso
      ((derivedGlobalSectionsOverIsoDerivedPushforwardOfField k (c ≫ g)).app _ ≪≫
        (derivedGlobalSectionsOver (𝟙 (Spec (.of k)))).mapIso
          ((derivedPushforwardCompIso c g).symm.app _ ≪≫ (derivedPushforward g).mapIso θ) ≪≫
        ((derivedGlobalSectionsOverIsoDerivedPushforwardOfField k g).app _).symm) ≪≫
    (cohomologyOverFieldIsoDerivedCohomologyOverField k g G n).symm

/-- **The Euler characteristic is preserved** when `Rc_*(ℱ[0]) = 𝒢[0]`. -/
theorem eulerCharacteristic_eq_of_derivedPushforwardIso [IsProper (c ≫ g)] [IsProper g]
    (F : X.Modules) [F.IsCoherent] (G : Y.Modules) [G.IsCoherent]
    (θ : (derivedPushforward c).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
      (DerivedCategory.singleFunctor Y.Modules 0).obj G) :
    eulerCharacteristic k (c ≫ g) F = eulerCharacteristic k g G := by
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum]
  congr 1
  funext n
  rw [(cohomologyOverFieldIsoOfDerivedPushforwardIso c g F G θ n).toLinearEquiv.finrank_eq]

end Leray

section EulerCharacteristic

open Stacks.AlgebraicGeometry.CurveEulerBridge

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **The Euler characteristic of a tensor power of an invertible module is affine in the
exponent**: `χ(ℒ^{⊗ n}) = n (χ(ℒ) - χ(𝒪_X)) + χ(𝒪_X)` on a proper scheme of dimension at most
one over `k`. This is the multiplicativity `deg(ℒ^{⊗ n}) = n deg(ℒ)` of the degree
([Stacks, Tag 0AYX]). -/
@[sga "6 XIII 3.7" "m = 0"]
theorem eulerCharacteristic_tensorSheafNPow (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] (n : ℕ) :
    @eulerCharacteristic k _ X f _ (tensorSheafNPow X.toRingedSpace L n : X.Modules)
        (@isCoherent_of_isFiniteLocallyFreeOfRank k _ X f _ _ 1
          (isFiniteLocallyFreeOfRank_tensorSheafNPow L n)) =
      n * (@eulerCharacteristic k _ X f _ L (isCoherent_of_isFiniteLocallyFreeOfRank k f L 1) -
        @eulerCharacteristic k _ X f _ _ (isCoherent_unit k f)) +
        @eulerCharacteristic k _ X f _ _ (isCoherent_unit k f) := by
  have key : ∀ n : ℕ, @curveDegree k _ X f _ hdim (tensorSheafNPow X.toRingedSpace L n : X.Modules)
      1 (isFiniteLocallyFreeOfRank_tensorSheafNPow L n) = n * curveDegree k f hdim L 1 := by
    intro n
    induction n with
    | zero =>
      simp only [curveDegree, Nat.cast_one, one_mul, Nat.cast_zero, zero_mul]
      exact sub_self _
    | succ n ih =>
      have h := @curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one k _ X f _ hdim
        (tensorSheafNPow X.toRingedSpace L n : X.Modules) L 1 1
        (isFiniteLocallyFreeOfRank_tensorSheafNPow L n) ‹_›
      simp only [one_mul, Nat.cast_one] at h
      push_cast
      rw [add_mul, one_mul, ← ih, ← h]
      rfl
  have k1 : @eulerCharacteristic k _ X f _ (tensorSheafNPow X.toRingedSpace L n : X.Modules)
        (@isCoherent_of_isFiniteLocallyFreeOfRank k _ X f _ _ 1
          (isFiniteLocallyFreeOfRank_tensorSheafNPow L n)) -
        ((1 : ℕ) : ℤ) * @eulerCharacteristic k _ X f _ _ (isCoherent_unit k f) =
      n * (@eulerCharacteristic k _ X f _ L (isCoherent_of_isFiniteLocallyFreeOfRank k f L 1) -
        ((1 : ℕ) : ℤ) * @eulerCharacteristic k _ X f _ _ (isCoherent_unit k f)) := key n
  push_cast at k1
  linarith

end EulerCharacteristic

section DualizingEuler

open Stacks.Duality Stacks.AlgebraicGeometry.CurveEulerBridge

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`χ(X, ω_X) = -χ(X, 𝒪_X)`** for an invertible dualizing sheaf on a proper scheme of
dimension at most one over `k`: by clause (5) of [Stacks, Tag 0BS2], `H^0(X, ω_X) = Hom(𝒪_X, ω_X)`
is dual to `H^1(X, 𝒪_X)` and `H^1(X, ω_X)` is dual to `End(ω_X)`, which is `End(𝒪_X) = H^0(X, 𝒪_X)`
because tensoring with `ω_X` is a `k`-linear autoequivalence ([Stacks, Tag 01CS]). -/
theorem eulerCharacteristic_dualizingSheafOverField [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualizingSheafOverField f) 1] :
    @eulerCharacteristic k _ X f _ (dualizingSheafOverField f)
        (isCoherent_of_isFiniteLocallyFreeOfRank k f _ 1) =
      -@eulerCharacteristic k _ X f _ _ (isCoherent_unit k f) := by
  let := modulesLinearOverField k f
  have hc := isCoherent_unit k f
  have hωc := isCoherent_of_isFiniteLocallyFreeOfRank k f (dualizingSheafOverField f) 1
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (dualizingSheafOverField f) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (isInvertible_of_isFiniteLocallyFreeOfRank_one X _)
  have := forall_finiteDimensional_cohomologyOverField_of_isProper k f _ hωc 1
  have := forall_finiteDimensional_cohomologyOverField_of_isProper k f _ hc 0
  let e : (Scheme.Modules.tensorLeft (dualizingSheafOverField f)).obj (structureSheafModule X) ≅
      dualizingSheafOverField f :=
    (Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight X.presheaf X.ringCatSheaf.2
      _).app _ ≪≫ Stacks.SheafOfModules.TensorPower.tensorPowerOneIso X.presheaf
        X.ringCatSheaf.2 _
  let E : (dualizingSheafOverField f ⟶ dualizingSheafOverField f) ≃ₗ[k]
      (structureSheafModule X ⟶ structureSheafModule X) :=
    ((tensorLeftHomLinearEquiv k f (dualizingSheafOverField f) (structureSheafModule X)
      (structureSheafModule X)).trans (Linear.homCongr k e e)).symm
  have h1 : Module.finrank k (cohomologyOverField k f (dualizingSheafOverField f) 1) =
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) := by
    rw [← Subspace.dual_finrank_eq,
      ← (homDualizingSheafLinearEquiv f hdim (dualizingSheafOverField f)
        (isQuasicoherent_of_isCoherent _)).finrank_eq,
      E.finrank_eq,
      (unitHomLinearEquivCohomologyZero k f (structureSheafModule X)).finrank_eq]
  have h0 : Module.finrank k (cohomologyOverField k f (dualizingSheafOverField f) 0) =
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) := by
    rw [finrank_cohomologyOverField_zero_dualizingSheafOverField f hdim,
      finrank_cohomologyOverField_one_unit_eq_genus]
  have eω := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f
    (dualizingSheafOverField f) (isZero_cohomologyOverField_two_le k f hdim _)
  have eO := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f
    (SheafOfModules.unit X.ringCatSheaf) (isZero_cohomologyOverField_two_le k f hdim _)
  unfold eulerCharacteristic
  rw [h0, h1] at eω
  linarith

end DualizingEuler

section Core

open Stacks.Duality Stacks.AlgebraicGeometry.CurveEulerBridge

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (c : X ⟶ Y) (g : Y ⟶ Spec (.of k))

/-- The higher direct images of `𝒪_X` along `c` vanish when `R^1 c_* 𝒪_X = 0` and `X` has dimension
at most one. -/
theorem isZero_rightDerived_unit [IsProper (c ≫ g)] [IsProper g] (hdimX : topologicalKrullDim X ≤ 1)
    (hR1 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward c).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (c ≫ g)
  have : IsProper c := IsProper.of_comp c g
  rcases Nat.lt_or_ge i 2 with h | h
  · obtain rfl : i = 1 := by omega
    exact hR1
  · open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
    exact isZero_rightDerived_pushforward_of_topologicalKrullDim_le
      c (d := 1) (by exact_mod_cast hdimX) _ i (by omega)

/-- The higher direct images of `c^*ω_Y` along `c` vanish when those of `𝒪_X` do. -/
private theorem isZero_rightDerived_pullback_dualizingSheafOverField [IsProper (c ≫ g)]
    [IsProper g] (hdimX : topologicalKrullDim X ≤ 1)
    (hR1 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualizingSheafOverField g) 1]
    (i : ℕ) (hi : 0 < i) : IsZero (((Scheme.Modules.pushforward c).rightDerived i).obj
      ((Scheme.Modules.pullback c).obj (dualizingSheafOverField g))) :=
  have := isInvertible_of_isFiniteLocallyFreeOfRank_one Y (dualizingSheafOverField g)
  Stacks.ProjectionFormula.isZero_rightDerived_pullback_of_isZero_rightDerived_unit
    c (dualizingSheafOverField g) i (isZero_rightDerived_unit c g hdimX hR1 i hi)

/-- A morphism of coherent modules on a proper `k`-scheme which is injective on global sections,
with `dim H^0` of the target at most that of the source, is surjective on global sections. -/
private theorem surjective_app_top_of_injective_of_finrank_le (f : X ⟶ Spec (.of k)) [IsProper f]
    {A B : X.Modules} (hA : A.IsCoherent) (hB : B.IsCoherent) (φ : A ⟶ B)
    (hinj : Function.Injective (φ.val.app (op ⊤)).hom)
    (hdim : Module.finrank k (cohomologyOverField k f B 0) ≤
      Module.finrank k (cohomologyOverField k f A 0)) :
    Function.Surjective (φ.app ⊤) := by
  have hH0inj : Function.Injective (cohomologyOverFieldMap k f φ 0) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 := cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f φ a
    rw [ha, map_zero] at h1
    have h2 : (cohomologyOverFieldZeroLinearIso k f A).hom a = 0 :=
      hinj (h1.symm.trans (map_zero _).symm)
    exact (cohomologyOverFieldZeroLinearIso k f A).toLinearEquiv.injective
      (h2.trans (map_zero _).symm)
  have := forall_finiteDimensional_cohomologyOverField_of_isProper k f A hA 0
  have := forall_finiteDimensional_cohomologyOverField_of_isProper k f B hB 0
  have hH0surj : Function.Surjective (cohomologyOverFieldMap k f φ 0) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm
      (LinearMap.finrank_le_finrank_of_injective
        (f := (cohomologyOverFieldMap k f φ 0).hom) hH0inj) hdim)).mp hH0inj
  intro y
  obtain ⟨z, rfl⟩ := (cohomologyOverFieldZeroLinearIso k f B).toLinearEquiv.surjective y
  obtain ⟨a, rfl⟩ := hH0surj z
  exact ⟨_, (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f φ a).symm⟩

/-- **The Euler characteristic step of [Stacks, Tag 0E7P]**: with `ℒ = c^*ω_Y`, the equality
`χ(ℒ^{⊗ m}) = χ(ω_X^{⊗ m})` (Leray and [Stacks, Tag 0AYX]) and `H^1(X, ω_X^{⊗ m}) = 0` give
`dim H^0(X, ω_X^{⊗ m}) ≤ dim H^0(X, ℒ^{⊗ m})`. -/
private theorem finrank_cohomologyOverField_zero_tensorSheafNPow_le [IsProper (c ≫ g)] [IsProper g]
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hR1 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualizingSheafOverField (c ≫ g)) 1]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualizingSheafOverField g) 1]
    (n : ℕ)
    (hH1 : IsZero (cohomologyOverField k (c ≫ g)
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) (n + 1)) 1)) :
    Module.finrank k (cohomologyOverField k (c ≫ g)
        (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) (n + 1)) 0) ≤
      Module.finrank k (cohomologyOverField k (c ≫ g) (tensorSheafNPow X.toRingedSpace
        ((Scheme.Modules.pullback c).obj (dualizingSheafOverField g)) (n + 1)) 0) := by
  have : IsProper c := IsProper.of_comp c g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have hχX := eulerCharacteristic_dualizingSheafOverField k (c ≫ g) hdimX
  have hχY := eulerCharacteristic_dualizingSheafOverField k g hdimY
  set L := (Scheme.Modules.pullback c).obj (dualizingSheafOverField g)
  have hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback c (dualizingSheafOverField g) 1
  have hRL := isZero_rightDerived_pullback_dualizingSheafOverField c g hdimX hR1
  have hRO := isZero_rightDerived_unit c g hdimX hR1
  let eL := Stacks.ProjectionFormula.pushforwardPullbackIsoOfIsIso c (dualizingSheafOverField g) hO
  have hLc : L.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank k (c ≫ g) L 1
  -- Euler characteristics
  have θL := (nonempty_derivedPushforward_iso_of_isZero c L (dualizingSheafOverField g) hRL eL).some
  have θO := (nonempty_derivedPushforward_iso_of_isZero c (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit Y.ringCatSheaf) hRO
    (asIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)).symm).some
  have χL := @eulerCharacteristic_eq_of_derivedPushforwardIso k _ X Y c g _ _ L hLc
    (dualizingSheafOverField g) (isCoherent_of_isFiniteLocallyFreeOfRank k g _ 1) θL
  have χO := @eulerCharacteristic_eq_of_derivedPushforwardIso k _ X Y c g _ _ _
    (isCoherent_unit k (c ≫ g)) _ (isCoherent_unit k g) θO
  have hLm := eulerCharacteristic_tensorSheafNPow k (c ≫ g) hdimX L (n + 1)
  have hMm := eulerCharacteristic_tensorSheafNPow k (c ≫ g) hdimX
    (dualizingSheafOverField (c ≫ g)) (n + 1)
  let Lm : X.Modules := tensorSheafNPow X.toRingedSpace L (n + 1)
  let Mm : X.Modules := tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) (n + 1)
  unfold eulerCharacteristic at hLm hMm χL χO hχX hχY
  have hL' := (finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k (c ≫ g) Lm
    (isZero_cohomologyOverField_two_le k (c ≫ g) hdimX Lm)).symm.trans hLm
  have hM' := (finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k (c ≫ g) Mm
    (isZero_cohomologyOverField_two_le k (c ≫ g) hdimX Mm)).symm.trans hMm
  have hM1 : Module.finrank k (cohomologyOverField k (c ≫ g) Mm 1) = 0 := by
    have := ModuleCat.subsingleton_of_isZero hH1
    exact Module.finrank_zero_of_subsingleton
  rw [hM1, Nat.cast_zero, sub_zero] at hM'
  have e : (Module.finrank k (cohomologyOverField k (c ≫ g) Lm 0) : ℤ) -
      Module.finrank k (cohomologyOverField k (c ≫ g) Lm 1) =
      Module.finrank k (cohomologyOverField k (c ≫ g) Mm 0) := by
    rw [hL', hM', χL, hχY, ← χO, hχX]
  have hpos : (0 : ℤ) ≤ Module.finrank k (cohomologyOverField k (c ≫ g) Lm 1) :=
    Nat.cast_nonneg _
  have : (Module.finrank k (cohomologyOverField k (c ≫ g) Mm 0) : ℤ) ≤
      Module.finrank k (cohomologyOverField k (c ≫ g) Lm 0) := by
    linarith
  exact_mod_cast this

/-- **The core of [Stacks, Tag 0E7P]**, for `X` and `Y` whose dualizing sheaves are finite locally
free of rank one, so that `χ(ω) = -χ(𝒪)` on both
(`eulerCharacteristic_dualizingSheafOverField`). With `ℒ = c^*ω_Y` and `b : ℒ ⟶ ω_X` the map whose
direct image is split by the trace, `b^{⊗ m}` is injective on global sections (reducedness of `X`),
`χ(ℒ^{⊗ m}) = χ(ω_X^{⊗ m})` (Leray and [Stacks, Tag 0AYX]) and `H^1(X, ω_X^{⊗ m}) = 0`, so
`b^{⊗ m}` is bijective on global sections, hence surjective as `ω_X^{⊗ m}` is globally generated,
hence `b` is an isomorphism. -/
theorem nonempty_pullback_iso_of_isFiniteLocallyFreeOfRank [IsProper (c ≫ g)] [IsProper g]
    [IsReduced X] (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hR1 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    [hωX : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualizingSheafOverField (c ≫ g)) 1]
    [hωY : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualizingSheafOverField g) 1]
    (n : ℕ)
    (hH1 : IsZero (cohomologyOverField k (c ≫ g)
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) (n + 1)) 1))
    (σ : SheafOfModules.GeneratingSections
      (tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) (n + 1) : X.Modules)) :
    Nonempty ((Scheme.Modules.pullback c).obj (dualizingSheafOverField g) ≅
      dualizingSheafOverField (c ≫ g)) := by
  have : IsProper c := IsProper.of_comp c g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  set L := (Scheme.Modules.pullback c).obj (dualizingSheafOverField g)
  have hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback c (dualizingSheafOverField g) 1
  have hRL := isZero_rightDerived_pullback_dualizingSheafOverField c g hdimX hR1
  let eL := Stacks.ProjectionFormula.pushforwardPullbackIsoOfIsIso c (dualizingSheafOverField g) hO
  have hLc : L.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank k (c ≫ g) L 1
  have hLq : L.IsQuasicoherent := isQuasicoherent_of_isCoherent L
  obtain ⟨b, t, hbt⟩ := exists_pushforward_map_comp_eq_id_of_isZero c g hdimX hdimY L hLq hRL eL
  have hinj := injective_app_top_tensorSheafNPowMap c (dualizingSheafOverField g)
    (dualizingSheafOverField (c ≫ g)) b t hbt n
  -- the map on `H^0`
  let φ : (tensorSheafNPow X.toRingedSpace L (n + 1) : X.Modules) ⟶
      tensorSheafNPow X.toRingedSpace (dualizingSheafOverField (c ≫ g)) (n + 1) :=
    tensorSheafNPowMap b (n + 1)
  have hsurj := surjective_app_top_of_injective_of_finrank_le (c ≫ g)
    (@isCoherent_of_isFiniteLocallyFreeOfRank k _ X (c ≫ g) _ _ 1
      (isFiniteLocallyFreeOfRank_tensorSheafNPow L (n + 1)))
    (@isCoherent_of_isFiniteLocallyFreeOfRank k _ X (c ≫ g) _ _ 1
      (isFiniteLocallyFreeOfRank_tensorSheafNPow (dualizingSheafOverField (c ≫ g)) (n + 1)))
    φ hinj (finrank_cohomologyOverField_zero_tensorSheafNPow_le c g hdimX hdimY hO hR1 n hH1)
  have hepi := epi_of_surjective_sectionsMap σ φ
    (AlgebraicGeometry.surjective_sectionsMap_of_surjective_app_top φ hsurj)
  have := isIso_of_epi_tensorSheafNPowMap hL hωX b n hepi
  exact ⟨asIso b⟩

end Core

end Stacks.Curves.DualizingPullback
