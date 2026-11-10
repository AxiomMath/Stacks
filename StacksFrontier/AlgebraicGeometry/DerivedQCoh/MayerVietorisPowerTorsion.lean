module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.RestrictionBaseRingLinear
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ExtSequenceRestrictions
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Mayer--Vietoris for a morphism killed by a power of a scalar

Let `(X, 𝒪)` be a ringed space covered by two opens `U` and `V`, let `A` be a commutative ring
acting on the category of sheaves of `𝒪`-modules and on the categories of sheaves of modules on
the three opens -- compatibly, in the sense that the three restriction functors are `A`-linear
-- and let `a ∈ A`. If a morphism `α : E ⟶ F⟦n⟧` of `D(𝒪)` restricts to something killed by a
power of `a` on `U` and on `V`, and if *every* morphism `E|_{U ∩ V} ⟶ F|_{U ∩ V}⟦n - 1⟧` is
killed by a power of `a`, then `α` itself is killed by a power of `a`.

This is the Mayer--Vietoris induction step of [Stacks, Tag 08EJ].

## Main results

* `Stacks.PowerTorsion.exists_pow_smul_eq_zero_of_cover`: the step itself.
* `Stacks.PowerTorsion.extensionRestrictionShiftedHomEquiv_smul`: the identification of
  Stacks 08BT is `A`-linear as soon as restriction is.
* `Stacks.PowerTorsion.mvCounitApp_comp_pow_smul_eq_zero`: a morphism whose restriction to
  an open is killed by a power of `a` is killed, after that power of `a`, by precomposition
  with the counit of that open.
* `Stacks.PowerTorsion.biprodTriangleShiftedHomδ_smul`: the connecting map of the contravariant
  sequence of a distinguished triangle with biproduct middle term is `A`-linear.

## References

* [Stacks Project, Tag 08EJ](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Pretriangulated
open ExtensionByZeroModules

universe u

variable {A : Type u} [CommRing A]

namespace Stacks.PowerTorsion

/-- A power of `a` killing an element is a lower bound: every larger power kills it too. -/
public theorem pow_smul_eq_zero_of_le {M : Type*} [AddCommGroup M] [Module A M] {a : A} {m : M}
    {k l : ℕ} (hk : a ^ k • m = 0) (hkl : k ≤ l) : a ^ l • m = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [pow_add, mul_comm, mul_smul, hk, smul_zero]

variable {B C : Type*} [Category* B] [Category* C] [Preadditive B] [Preadditive C]
  [HasShift B ℤ] [HasShift C ℤ] [Linear A B] [Linear A C]

/-- **The identification of shifted morphism groups across an adjunction is `A`-linear**, as
soon as the right adjoint is. -/
public theorem adjShiftedHomEquiv_smul (L : B ⥤ C) (R : C ⥤ B) (adj : L ⊣ R)
    [L.Additive] [R.CommShift ℤ] [R.Linear A] (E F : C) (n : ℤ) (r : A)
    (x : L.obj (R.obj E) ⟶ F⟦n⟧) :
    Stacks.ExtensionByZero.adjShiftedHomEquiv L R adj E F n (r • x) =
      r • Stacks.ExtensionByZero.adjShiftedHomEquiv L R adj E F n x := by
  change (adj.unit.app (R.obj E) ≫ R.map (r • x)) ≫ (R.commShiftIso n).hom.app F =
    r • ((adj.unit.app (R.obj E) ≫ R.map x) ≫ (R.commShiftIso n).hom.app F)
  rw [R.map_smul, Linear.comp_smul, Linear.smul_comp]

/-- **The connecting map of the contravariant sequence of a distinguished triangle with
biproduct middle term is `A`-linear.** -/
public theorem biprodTriangleShiftedHomδ_smul [∀ m : ℤ, (shiftFunctor C m).Additive]
    [∀ m : ℤ, (shiftFunctor C m).Linear A]
    {P Q Z W : C} [HasBinaryBiproduct P Q] (p : Z ⟶ P) (q : Z ⟶ Q) (r : P ⟶ W) (s : Q ⟶ W)
    (d : W ⟶ Z⟦(1 : ℤ)⟧) (F : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (c : A) (y : Z ⟶ F⟦n₀⟧) :
    biprodTriangleShiftedHomδ p q r s d F n₀ n₁ h (c • y) =
      c • biprodTriangleShiftedHomδ p q r s d F n₀ n₁ h y := by
  rw [biprodTriangleShiftedHomδ_apply, biprodTriangleShiftedHomδ_apply, Functor.map_smul,
    Linear.smul_comp, Linear.comp_smul]

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] jShriek_additive

open Stacks.ExtensionByZero

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [Linear A (SheafOfModules.{u} O)]

/-- Extension by zero `j_!` from an open `U` preserves finite limits. -/
local instance jShriekPFL (U : Opens X) : PreservesFiniteLimits (jShriek U O) :=
  (jShriek_additive_and_exact O U).2.1

/-- Extension by zero `j_!` from an open `U` preserves finite colimits. -/
local instance jShriekPFC (U : Opens X) : PreservesFiniteColimits (jShriek U O) :=
  (jShriek_additive_and_exact O U).2.2

/-- Restriction `j^*` to an open `U` preserves finite limits. -/
local instance jStarPFL (U : Opens X) : PreservesFiniteLimits (jStar U O) :=
  inferInstance

/-- Restriction `j^*` to an open `U` preserves finite colimits. -/
local instance jStarPFC (U : Opens X) : PreservesFiniteColimits (jStar U O) :=
  inferInstance

/-- **The identification of Stacks 08BT is `A`-linear**, as soon as restriction to the open
subspace is. -/
public theorem extensionRestrictionShiftedHomEquiv_smul (U : Opens X)
    [Linear A (SheafOfModules.{u} (resRing U O))] [(derivedRestriction O U).Linear A]
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) (r : A)
    (x : (derivedExtensionRestriction O U).obj E ⟶ F⟦n⟧) :
    extensionRestrictionShiftedHomEquiv O U E F n (r • x) =
      r • extensionRestrictionShiftedHomEquiv O U E F n x :=
  adjShiftedHomEquiv_smul _ _ (derivedJShriekRestrictionAdjunction O U) E F n r x

/-- **A morphism whose restriction to `U` is killed by `a ^ k` is killed by `a ^ k` after
precomposition with the counit of `U`.** -/
public theorem mvCounitApp_comp_pow_smul_eq_zero (U : Opens X)
    [Linear A (SheafOfModules.{u} (resRing U O))] [(derivedRestriction O U).Linear A]
    (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) (a : A) (k : ℕ)
    (α : E ⟶ F⟦n⟧)
    (h : a ^ k • (ShiftedHom.map α (derivedRestriction O U)) = 0) :
    mvCounitApp O U E ≫ (a ^ k • α) = 0 := by
  refine (extensionRestrictionShiftedHomEquiv O U E F n).injective ?_
  rw [map_zero, extensionRestrictionShiftedHomEquiv_mvCounitApp, ShiftedHom.map_smul, h]

/-- **The Mayer--Vietoris step of [Stacks, Tag 08EJ].** Let `(X, 𝒪)` be a ringed space covered
by two opens `U` and `V`, let `A` be a commutative ring acting `A`-linearly on the sheaves of
modules of `X` and of the three opens, with `A`-linear restriction functors, and let `a ∈ A`.
If `α : E ⟶ F⟦n⟧` restricts on `U` and on `V` to morphisms killed by a power of `a`, and if
every morphism `E|_{U ∩ V} ⟶ F|_{U ∩ V}⟦n - 1⟧` is killed by a power of `a`, then `α` is killed
by a power of `a`. -/
public theorem exists_pow_smul_eq_zero_of_cover (U V : Opens X) (hUV : U ⊔ V = ⊤)
    [Linear A (SheafOfModules.{u} (resRing U O))]
    [Linear A (SheafOfModules.{u} (resRing V O))]
    [Linear A (SheafOfModules.{u} (resRing (U ⊓ V) O))]
    [(derivedRestriction O U).Linear A] [(derivedRestriction O V).Linear A]
    [(derivedRestriction O (U ⊓ V)).Linear A]
    (a : A) (E F : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) (α : E ⟶ F⟦n⟧)
    (hU : ∃ k : ℕ, a ^ k • ShiftedHom.map α (derivedRestriction O U) = 0)
    (hV : ∃ k : ℕ, a ^ k • ShiftedHom.map α (derivedRestriction O V) = 0)
    (hW : ∀ y : ShiftedHom ((derivedRestriction O (U ⊓ V)).obj E)
        ((derivedRestriction O (U ⊓ V)).obj F) (n - 1), ∃ k : ℕ, a ^ k • y = 0) :
    ∃ k : ℕ, a ^ k • α = 0 := by
  obtain ⟨kU, hkU⟩ := hU
  obtain ⟨kV, hkV⟩ := hV
  have hn : n - 1 + 1 = n := by lia
  have h1 := mvCounitApp_comp_pow_smul_eq_zero O U E F n a _ α
    (pow_smul_eq_zero_of_le hkU (le_max_left kU kV))
  have h2 := mvCounitApp_comp_pow_smul_eq_zero O V E F n a _ α
    (pow_smul_eq_zero_of_le hkV (le_max_right kU kV))
  obtain ⟨iU, iV, δ, hiU, hiV, htri⟩ := distinguished_extensionRestriction_triangle O U V hUV
    (derivedExtensionRestriction O U) (derivedExtensionRestriction O V)
    (derivedExtensionRestriction O (U ⊓ V))
    (derivedExtensionRestrictionFactorsh O U).inv
    (derivedExtensionRestrictionFactorsh O V).inv
    (derivedExtensionRestrictionFactorsh O (U ⊓ V)).inv
  have hex := exact_biprodTriangleShiftedHomδ_shiftedHomRestriction
    (iU.app E) (iV.app E) (mvCounitApp O U E) (mvCounitApp O V E) (δ.app E) (htri E) F
    (n - 1) n hn
  obtain ⟨y, hy⟩ := (hex (a ^ (max kU kV) • α)).1 (Prod.ext h1 h2)
  obtain ⟨k, hk⟩ := hW (extensionRestrictionShiftedHomEquiv O (U ⊓ V) E F (n - 1) y)
  have hky : a ^ k • y = 0 :=
    (extensionRestrictionShiftedHomEquiv O (U ⊓ V) E F (n - 1)).injective
      (((extensionRestrictionShiftedHomEquiv_smul O (U ⊓ V) E F (n - 1) (a ^ k) y).trans
        hk).trans (map_zero _).symm)
  refine ⟨k + max kU kV, ?_⟩
  have hlin := biprodTriangleShiftedHomδ_smul (A := A) (iU.app E) (iV.app E)
    (mvCounitApp O U E) (mvCounitApp O V E) (δ.app E) F (n - 1) n hn (a ^ k) y
  rw [pow_add, mul_smul, ← hy, ← hlin, hky, map_zero]

end Stacks.PowerTorsion

end
