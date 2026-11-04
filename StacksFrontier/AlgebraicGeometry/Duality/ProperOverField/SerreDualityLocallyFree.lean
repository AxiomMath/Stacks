module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.RingedSpaceTrace
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupBaseShiftPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorWithDualizableSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PullbackSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualRingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Duality.CohomologyHypercohomology
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreTensorInstance
import StacksCore.Tactic.StacksAttribute

/-!
# Serre duality for finite locally free modules on a proper Cohen--Macaulay scheme

Let `X` be a proper Cohen--Macaulay scheme over a field `k`, equidimensional of dimension `d`,
with dualizing complex `ω_X^• = ω_X[d]` ([Stacks, Tag 0FVV], [Stacks, Tag 0FVZ]) and trace
`t : Hᵈ(X, ω_X) ⟶ k` ([Stacks, Tag 0FVW]). For a finite locally free `𝒪_X`-module `ℰ` with dual
`ℰ^∨`, [Stacks, Tag 0FW0] asserts that the pairings

`Hⁱ(X, ω_X ⊗ ℰ^∨) × Hᵈ⁻ⁱ(X, ℰ) ⟶ k,  (ξ, η) ↦ t((1 ⊗ ε)(ξ ∪ η))`

are perfect, `∪` being the cup product and `ε : ℰ^∨ ⊗ ℰ ⟶ 𝒪_X` the evaluation map.

## Main definitions

* `Stacks.Duality.sheafCohomology f ℱ n`: `Hⁿ(X, ℱ)` as a `k`-vector space, the cohomology at which
  the cup product of Cohomology, Section 0FKU is stated.
* `Stacks.Duality.dualContraction`: `1 ⊗ ε : (ℳ ⊗ ℰ^∨) ⊗ ℰ ⟶ ℳ`.
* `Stacks.Duality.serrePairing`: the pairing `(ξ, η) ↦ t((1 ⊗ ε)(ξ ∪ η))`.

## Main results

* `Stacks.Duality.serrePairing_isPerfPair`: **[Stacks, Tag 0FW0]**.

## Implementation notes

standard model: uses `Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing`, which exists only
there.

The proof is the source's ("a special case of [Stacks, Tag 0FVY]") carried out directly in
degree `i`, without the reduction to degree `0` by shifting `ℰ`, which would need a compatibility
of the cup product with shifts that the library does not provide. Write a class `ξ ∈ Hⁱ(X, K)` as a
morphism `ξ̃ : L(A[-i]) ⟶ K` out of `L(A[-i]) = 𝒪_X[-i]`, `L ⊣ RΓ(X, -)` being the adjunction of
the cup product. Then `ξ = Hⁱ(ξ̃)(gᵢ)` for the class `gᵢ` of the identity, and by naturality of the
cup product `t((1 ⊗ ε)(ξ ∪ η)) = t(Hᵈ(Ψ(ξ̃))(gᵢ ∪ η))` with `Ψ(ξ̃) = (1 ⊗ ε) ∘ (ξ̃ ⊗ ℰ[0])`. Now
* `ξ̃ ↦ Ψ(ξ̃)` is a bijection `Hom(L(A[-i]), (ω_X ⊗ ℰ^∨)[0]) ≃ Hom(L(A[-i]) ⊗^𝐋 ℰ[0], ω_X[0])`,
  since `- ⊗ ℰ ⊣ - ⊗ ℰ^∨` (`bijective_tensorRightSingle_comp_counit`);
* `β ↦ t ∘ Hᵈ(β)` is a bijection `Hom(Z, ω_X[0]) ≃ Hᵈ(X, Z)^∨` for `Z = L(A[-i]) ⊗^𝐋 ℰ[0]`, by
  [Stacks, Tag 0FVV] (`bijective_map_comp_topTrace`);
* `η ↦ gᵢ ∪ η` is a linear bijection `Hᵈ⁻ⁱ(X, ℰ) ≃ Hᵈ(X, Z)`: the cup product of the two
  generating classes names an isomorphism (`classAdjunct_cupPairing`, `isIso_pinnedSplitting`) and
  tensoring with `L(A[-i]) = 𝒪_X[-i]` is fully faithful (`bijective_map_tensorPullbackBaseShift`).
So the pairing is perfect on the left; on the right it is then perfect because `Hᵈ⁻ⁱ(X, ℰ)` is
finite dimensional ([Stacks, Tag 02O6]).

## References

* [Stacks Project, Tag 0FW0](https://stacks.math.columbia.edu/tag/0FW0)
* [Stacks Project, Tag 0FVY](https://stacks.math.columbia.edu/tag/0FVY)
* [Stacks Project, Tag 0FVZ](https://stacks.math.columbia.edu/tag/0FVZ)
* [Stacks Project, Tag 0FVW](https://stacks.math.columbia.edu/tag/0FVW)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections onePointComparisonCanonical
  globalCupProductCanonical)
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Duality

/-! ### The dual of a finite locally free module -/

section Dual

variable {X : Scheme.{u}}

/-- The dual `ℰ^∨ = 𝓗om(ℰ, 𝒪_X)` of a sheaf of `𝒪_X`-modules. -/
@[ega "IV 18.5.1", sga "3 III 0.6"]
abbrev dualModule (E : X.Modules) : X.Modules :=
  Stacks.SheafOfModules.dualSheaf X.presheaf X.ringCatSheaf.property E

/-- `ℳ ⊗ 𝒩`, the tensor product of [Stacks, Tag 01CA]. -/
abbrev tensorModule (M N : X.Modules) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N

/-- **`1 ⊗ ε : (ℳ ⊗ ℰ^∨) ⊗ ℰ ⟶ ℳ`**: the associativity constraint, the evaluation map
`ε : ℰ^∨ ⊗ ℰ ⟶ 𝒪_X` on the last two factors, and the unit constraint. -/
def dualContraction (M E : X.Modules) : tensorModule (tensorModule M (dualModule E)) E ⟶ M :=
  (@MonoidalCategoryStruct.associator (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) _
      (SheafOfModules.monoidalCategorySheafTensor X.sheaf).toMonoidalCategoryStruct M
      (dualModule E) E).hom ≫
    @MonoidalCategoryStruct.whiskerLeft (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) _
      (SheafOfModules.monoidalCategorySheafTensor X.sheaf).toMonoidalCategoryStruct M _ _
      (Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.property E) ≫
    (@MonoidalCategoryStruct.rightUnitor (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) _
      (SheafOfModules.monoidalCategorySheafTensor X.sheaf).toMonoidalCategoryStruct M).hom

/-- **A finite locally free module has `ℰ^∨` as a left dual** for the tensor product of
[Stacks, Tag 01CA] ([Stacks, Tag 0FNY]), read at the monoidal structure whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor`. -/
@[instance_reducible]
def hasRightDualOfFiniteLocallyFree (E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    @HasRightDual (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) _
      (SheafOfModules.monoidalCategorySheafTensor X.sheaf) E :=
  @HasRightDual.mk _ _ (SheafOfModules.monoidalCategorySheafTensor X.sheaf) E (dualModule E)
    (@ExactPairing.map _ _ _ _
      (Stacks.SheafOfModules.Strict.monoidalCategory X.sheaf.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf))
      (SheafOfModules.monoidalCategorySheafTensor X.sheaf) (𝟭 _)
      (SheafOfModules.idMonoidalStrictToSheafTensor X.sheaf) E _
      (Stacks.SheafOfModules.exactPairingDualSheafOfLocalSummand X.presheaf
        X.ringCatSheaf.property E
        (Stacks.Algebraization.isLocallyDirectSummandOfFiniteFree_of_isFiniteLocallyFree E hE)))

/-- The evaluation of the pairing `hasRightDualOfFiniteLocallyFree` is the evaluation map. -/
theorem evaluation_hasRightDualOfFiniteLocallyFree (E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    @ExactPairing.evaluation (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) _
        (SheafOfModules.monoidalCategorySheafTensor X.sheaf) E (dualModule E)
        (@HasRightDual.exact _ _ (SheafOfModules.monoidalCategorySheafTensor X.sheaf) E
          (hasRightDualOfFiniteLocallyFree E hE)) =
      Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.property E := by
  refine (@ExactPairing.map_evaluation _ _ _ _
    (Stacks.SheafOfModules.Strict.monoidalCategory X.sheaf.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf))
    (SheafOfModules.monoidalCategorySheafTensor X.sheaf) (𝟭 _)
    (SheafOfModules.idMonoidalStrictToSheafTensor X.sheaf) E _
    (Stacks.SheafOfModules.exactPairingDualSheafOfLocalSummand X.presheaf
      X.ringCatSheaf.property E
      (Stacks.Algebraization.isLocallyDirectSummandOfFiniteFree_of_isFiniteLocallyFree E
        hE))).trans ?_
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- `1 ⊗ ε` is the counit of the adjunction `- ⊗ ℰ ⊣ - ⊗ ℰ^∨`. -/
theorem dualContraction_eq_counit (M E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    dualContraction M E =
      (@tensorRightAdjunction (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) _
        (SheafOfModules.monoidalCategorySheafTensor X.sheaf) E (dualModule E)
        (@HasRightDual.exact _ _ (SheafOfModules.monoidalCategorySheafTensor X.sheaf) E
          (hasRightDualOfFiniteLocallyFree E hE))).counit.app M := by
  rw [dualContraction, ← evaluation_hasRightDualOfFiniteLocallyFree E hE]
  exact ((congrArg (fun g => g ≫ _) (@MonoidalCategory.id_whiskerRight
    (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) _
    (SheafOfModules.monoidalCategorySheafTensor X.sheaf) (tensorModule M (dualModule E)) E)).trans
    (Category.id_comp _)).symm

end Dual

/-! ### Classes as morphisms out of `L(A[-i])`, on elements -/

section Classes

attribute [local instance 100000] HasDerivedCategory.standard

variable {S : RingedSpace.{u, u}} (c : OnePointComparison S)

/-- A morphism out of `A` is the morphism attached to its value at `1`. -/
theorem ofHom_toSpanSingleton_apply_one {M : ModuleCat.{u} (baseRing S)}
    (φ : ModuleCat.of (baseRing S) (baseRing S) ⟶ M) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) M (φ.hom 1)) = φ := by
  ext
  simp

/-- A class `ξ ∈ Hⁱ(S, K)` as the morphism `ξ̃ : L(A[-i]) ⟶ K` (`classAdjunct`), on elements. -/
def elementAdjunct (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i : ℤ)
    (x : cohomologyModule K i) : c.pullback.obj (baseShift S i) ⟶ K :=
  classAdjunct c K i (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) _ x))

/-- Every morphism `L(A[-i]) ⟶ K` is `ξ̃` for exactly one class `ξ ∈ Hⁱ(S, K)`. -/
theorem bijective_elementAdjunct (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (i : ℤ) : Function.Bijective (elementAdjunct c K i) := by
  have h₁ : Function.Bijective (fun x : cohomologyModule K i =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) (cohomologyModule K i) x)) :=
    ⟨fun x y h => by simpa using congrArg (fun φ => φ.hom (1 : baseRing S)) h,
      fun φ => ⟨φ.hom 1, ofHom_toSpanSingleton_apply_one φ⟩⟩
  exact (classAdjunctEquiv c K i).bijective.comp h₁

/-- **The generating class** `gᵢ ∈ Hⁱ(S, L(A[-i]))`, the class named by the identity of
`L(A[-i])`. -/
def generatingClass (i : ℤ) : cohomologyModule (c.pullback.obj (baseShift S i)) i :=
  ((classAdjunctEquiv c _ i).symm (𝟙 _)).hom (1 : baseRing S)

/-- The morphism named by the generating class `gᵢ` is the identity of `L(A[-i])`. -/
theorem elementAdjunct_generatingClass (i : ℤ) :
    elementAdjunct c _ i (generatingClass c i) = 𝟙 (c.pullback.obj (baseShift S i)) := by
  exact (congrArg (classAdjunct c _ i) (ofHom_toSpanSingleton_apply_one _)).trans
    ((classAdjunctEquiv c _ i).apply_symm_apply _)

/-- **A class is the image of the generating class under the morphism it names**:
`ξ = Hⁱ(ξ̃)(gᵢ)`. -/
theorem map_elementAdjunct_generatingClass
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i : ℤ)
    (x : cohomologyModule K i) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
      ((baseSections S).map (elementAdjunct c K i x))).hom (generatingClass c i) = x := by
  have h : (classAdjunctEquiv c _ i).symm (𝟙 _) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
        ((baseSections S).map (elementAdjunct c K i x)) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) _ x) := by
    apply (classAdjunctEquiv c K i).injective
    rw [classAdjunctEquiv_apply, classAdjunct_comp, classAdjunctEquiv_apply,
      ← classAdjunctEquiv_apply, Equiv.apply_symm_apply, Category.id_comp]
    rfl
  have := congrArg (fun φ => φ.hom (1 : baseRing S)) h
  simpa [generatingClass] using this

/-- A composite out of `A ⊗ A` read at `1`. -/
private lemma leftUnitor_inv_tensorHom_comp_apply_one' {R : CommRingCat.{u}}
    {P Q T : ModuleCat.{u} R} (f : ModuleCat.of R R ⟶ P) (g : ModuleCat.of R R ⟶ Q)
    (h : P ⊗ Q ⟶ T) :
    ((λ_ (ModuleCat.of R R)).inv ≫ (f ⊗ₘ g) ≫ h).hom (1 : R) =
      h.hom (f.hom (1 : R) ⊗ₜ g.hom (1 : R)) := by
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply, ModuleCat.MonoidalCategory.tensorHom_tmul]

/-- **The cup product with the generating class, as a morphism**: the morphism named by
`gᵢ ∪ η` is `L(χ)` followed by the comparison `α` and `L(A[-i]) ⊗^𝐋 η̃`. -/
theorem elementAdjunct_cupPairing_generatingClass
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ)
    (y : cohomologyModule M j) :
    elementAdjunct c (((derivedTensorProductFunctor S.sheaf).obj
        (c.pullback.obj (baseShift S i))).obj M) (i + j)
        ((cupPairing (globalCupProduct c) _ M i j).hom (generatingClass c i ⊗ₜ y)) =
      c.pullback.map (pinnedSplitting S i j) ≫
        c.tensorComparison.app (baseShift S i, baseShift S j) ≫
          ((derivedTensorProductFunctor S.sheaf).obj (c.pullback.obj (baseShift S i))).map
            (elementAdjunct c M j y) := by
  have key := classAdjunct_cupPairing c (c.pullback.obj (baseShift S i)) M i j
    ((classAdjunctEquiv c _ i).symm (𝟙 _))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) _ y))
  have hgen : classAdjunct c (c.pullback.obj (baseShift S i)) i
      ((classAdjunctEquiv c _ i).symm (𝟙 _)) = 𝟙 _ :=
    (classAdjunctEquiv c _ i).apply_symm_apply _
  refine Eq.trans ?_ (key.trans ?_)
  · refine congrArg (classAdjunct c _ (i + j)) ?_
    refine Eq.trans ?_ (ofHom_toSpanSingleton_apply_one _)
    congr 2
    rw [leftUnitor_inv_tensorHom_comp_apply_one']
    simp [generatingClass]
  · have h₁ : ((derivedTensorProductFunctor S.sheaf).map
        (classAdjunct c (c.pullback.obj (baseShift S i)) i
          ((classAdjunctEquiv c _ i).symm (𝟙 _)))).app (c.pullback.obj (baseShift S j)) = 𝟙 _ := by
      rw [hgen]
      exact congrArg (fun φ => NatTrans.app φ (c.pullback.obj (baseShift S j)))
        ((derivedTensorProductFunctor S.sheaf).map_id _)
    refine congrArg (c.pullback.map (pinnedSplitting S i j) ≫ ·)
      (congrArg (c.tensorComparison.app (baseShift S i, baseShift S j) ≫ ·) ?_)
    exact (congrArg (· ≫ _) h₁).trans (Category.id_comp _)

end Classes

/-! ### The pairing -/

section Pairing

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `ℱ[0]`, in the standard model of `D(𝒪_X)`. -/
abbrev singleModule (F : X.Modules) : DerivedCategory X.Modules :=
  (DerivedCategory.singleFunctor X.Modules 0).obj F

/-- **`Hⁿ(X, ℱ)` as a `k`-vector space**: the cohomology `Hⁿ(RΓ(X, ℱ[0]))` of Cohomology,
Section 0FKU, a module over `Γ(X, 𝒪_X)`, read over `k` through `k ⟶ Γ(X, 𝒪_X)`. -/
abbrev sheafCohomology (F : X.Modules) (n : ℤ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj (cohomologyModule (singleModule F) n)

/-- `(ℳ ⊗ ℰ^∨)[0] ⊗^𝐋 ℰ[0] ⟶ ((ℳ ⊗ ℰ^∨) ⊗ ℰ)[0] ⟶ ℳ[0]`: the canonical map to the tensor product
in degree zero, followed by `1 ⊗ ε`. -/
def contractionMap (M E : X.Modules) :
    ((derivedTensorProductFunctor X.sheaf).obj (singleModule (tensorModule M (dualModule E)))).obj
        (singleModule E) ⟶ singleModule M :=
  derivedTensorSingleToTensor (tensorModule M (dualModule E)) E ≫
    DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map (dualContraction M E))

/-- **`ξ ⊗ η ↦ (1 ⊗ ε)(ξ ∪ η)`**, `Hⁱ(X, ℳ ⊗ ℰ^∨) ⊗ Hʲ(X, ℰ) ⟶ Hⁿ(X, ℳ)` for `i + j = n`: the cup
product of Section 0FKU, `Hⁱ⁺ʲ` of `contractionMap`, and `Hⁱ⁺ʲ = Hⁿ`. -/
def contractedCupProduct (M E : X.Modules) (i j n : ℤ) (h : i + j = n) :
    cohomologyModule (singleModule (tensorModule M (dualModule E))) i ⊗
        cohomologyModule (singleModule E) j ⟶ cohomologyModule (singleModule M) n :=
  cupPairing (globalCupProductCanonical X.toRingedSpace) _ _ i j ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) (i + j)).map
      ((baseSections X.toRingedSpace).map (contractionMap M E)) ≫
    eqToHom (by rw [h])

variable [IsProper f]

/-- **The pairing of [Stacks, Tag 0FW0]**,

`Hⁱ(X, ω_X ⊗ ℰ^∨) × Hʲ(X, ℰ) ⟶ k,  (ξ, η) ↦ t((1 ⊗ ε)(ξ ∪ η))`,

for `i + j = d`: the cup product of Section 0FKU, `1 ⊗ ε` with `ε : ℰ^∨ ⊗ ℰ ⟶ 𝒪_X` the evaluation,
and the trace `t : Hᵈ(X, ω_X) ⟶ k` of [Stacks, Tag 0FVW] read through `ω_X^• = ω_X[d]`
([Stacks, Tag 0FVZ]), as a `k`-bilinear map. -/
def serrePairing (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (E : X.Modules) (i j : ℤ) (hij : i + j = d) :
    sheafCohomology f (tensorModule (dualizingModule f) (dualModule E)) i →ₗ[k]
      sheafCohomology f E j →ₗ[k] k :=
  let T := (topTrace f hCM hequi d hd).hom
  let B := (TensorProduct.mk ↑(baseRing X.toRingedSpace)
      ↑(cohomologyModule (singleModule (tensorModule (dualizingModule f) (dualModule E))) i)
      ↑(cohomologyModule (singleModule E) j)).compr₂
    (contractedCupProduct (dualizingModule f) E i j d hij).hom
  LinearMap.mk₂ k (fun ξ η => T (B ξ η))
    (fun ξ₁ ξ₂ η => (congrArg T (B.map_add₂ ξ₁ ξ₂ η)).trans (map_add T _ _))
    (fun c ξ η => (congrArg T (B.map_smul₂ (globalRingHom f c) ξ η)).trans (map_smul T c _))
    (fun ξ η₁ η₂ => (congrArg T ((B ξ).map_add η₁ η₂)).trans (map_add T _ _))
    (fun c ξ η => (congrArg T ((B ξ).map_smul (globalRingHom f c) η)).trans (map_smul T c _))

/-- The value of the pairing. -/
theorem serrePairing_apply (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (E : X.Modules) (i j : ℤ) (hij : i + j = d)
    (ξ : sheafCohomology f (tensorModule (dualizingModule f) (dualModule E)) i)
    (η : sheafCohomology f E j) :
    serrePairing f hCM hequi d hd E i j hij ξ η =
      (topTrace f hCM hequi d hd).hom
        ((contractedCupProduct (dualizingModule f) E i j d hij).hom (ξ ⊗ₜ η)) :=
  rfl

end Pairing

/-! ### Perfectness -/

section Perfect

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The identification `Hⁿ = Hᵐ` for `n = m` is natural. -/
theorem eqToHom_comp_homologyFunctor_map {K L : DerivedCategory X.Modules} (φ : K ⟶ L) {n m : ℤ}
    (h : n = m) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) n).map
        ((baseSections X.toRingedSpace).map φ) ≫
      eqToHom (show cohomologyModule L n = cohomologyModule L m by rw [h]) =
    eqToHom (show cohomologyModule K n = cohomologyModule K m by rw [h]) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) m).map
        ((baseSections X.toRingedSpace).map φ) := by
  subst h
  simp

/-- A finite locally free `𝒪_X`-module is quasi-coherent, being of finite presentation. -/
private theorem isQuasicoherent_of_isFiniteLocallyFree (E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    E.IsQuasicoherent :=
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.isFinitePresentation E hE
  _root_.isQuasicoherent_of_isFinitePresentation E

/-- **The pairing is perfect on the left**: every linear form on `Hʲ(X, ℰ)` is `η ↦ ⟨ξ, η⟩` for
exactly one `ξ ∈ Hⁱ(X, ω_X ⊗ ℰ^∨)`. -/
theorem bijective_serrePairing (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (E : X.Modules) (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (i j : ℤ) (hij : i + j = d) :
    Function.Bijective (serrePairing f hCM hequi d hd E i j hij) := by
  let c := onePointComparisonCanonical X.toRingedSpace
  let P := c.pullback.obj (baseShift X.toRingedSpace i)
  let T := derivedTensorProductFunctor X.toRingedSpace.sheaf
  let ω := dualizingModule f
  let G0 := singleModule (tensorModule ω (dualModule E))
  let E0 := singleModule E
  let Z := (T.obj P).obj E0
  -- `ξ̃ ↦ (1 ⊗ ε) ∘ (ξ̃ ⊗ ℰ[0])` is bijective
  let Ψ : (P ⟶ G0) → (Z ⟶ singleModule ω) := fun ψ => (T.map ψ).app E0 ≫ contractionMap ω E
  have hΨ : Function.Bijective Ψ := by
    let := hasRightDualOfFiniteLocallyFree E hE
    have h := bijective_tensorRightSingle_comp_counit (R := X.toRingedSpace.sheaf) E P ω
    have hc := dualContraction_eq_counit ω E hE
    refine (congrArg Function.Bijective (funext fun ψ => ?_)).mpr h
    simp only [Ψ, contractionMap, hc]
    rfl
  -- duality against the trace
  have hZ : ∀ n : ℤ, ((@DerivedCategory.homologyFunctor X.Modules _ _
      (Scheme.Modules.hasDerivedCategory X) n).obj
      ((Scheme.Modules.derivedModelEquiv X).functor.obj Z)).IsQuasicoherent := by
    have hEq := isQuasicoherent_of_isFiniteLocallyFree E hE
    let eZ : (Scheme.Modules.derivedModelEquiv X).functor.obj Z ≅
        ((@DerivedCategory.singleFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X) 0).obj
          E)⟦-i⟧ :=
      (Scheme.Modules.derivedModelEquiv X).functor.mapIso
          ((tensorPullbackBaseShiftIso X.toRingedSpace i).app E0) ≪≫
        ((Scheme.Modules.derivedModelEquiv X).functor.commShiftIso (-i)).app E0 ≪≫
        (shiftFunctor _ (-i)).mapIso ((Scheme.Modules.derivedModelEquivCompQIso X).app
          ((CochainComplex.singleFunctor X.Modules 0).obj E))
    have hq : ∀ m : ℤ, ((@DerivedCategory.homologyFunctor X.Modules _ _
        (Scheme.Modules.hasDerivedCategory X) m).obj ((@DerivedCategory.singleFunctor X.Modules _ _
          (Scheme.Modules.hasDerivedCategory X) 0).obj E)).IsQuasicoherent := by
      let := Scheme.Modules.hasDerivedCategory X
      intro m
      rcases lt_trichotomy m 0 with hm | rfl | hm
      · exact isQuasicoherent_of_isZero X _
          (DerivedCategory.isZero_of_isGE
            ((DerivedCategory.singleFunctor X.Modules 0).obj E) 0 m hm)
      · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app E).symm hEq
      · exact isQuasicoherent_of_isZero X _
          (DerivedCategory.isZero_of_isLE
            ((DerivedCategory.singleFunctor X.Modules 0).obj E) 0 m hm)
    intro n
    let iso₁ := ((@DerivedCategory.homologyFunctor X.Modules _ _
      (Scheme.Modules.hasDerivedCategory X) 0).shiftIso (-i) n (-i + n) rfl).app
        ((@DerivedCategory.singleFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X) 0).obj
          E)
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (iso₁.symm ≪≫ (@DerivedCategory.homologyFunctor X.Modules _ _
        (Scheme.Modules.hasDerivedCategory X) n).mapIso eZ.symm)
      (hq (-i + n))
  have hB3 := bijective_map_comp_topTrace f hCM hequi d hd Z hZ
  -- `η ↦ gᵢ ∪ η`
  let cupGen : sheafCohomology f E j ⟶
      (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj (cohomologyModule Z d) :=
    (ModuleCat.restrictScalars.{u} (globalRingHom f)).map
      (ModuleCat.ofHom ((cupPairing (globalCupProduct c) P E0 i j).hom ∘ₗ
        TensorProduct.mk _ _ _ (generatingClass c i)) ≫ eqToHom (by rw [hij]))
  have hcupGen : Function.Bijective cupGen.hom := by
    have hiso : IsIso (c.pullback.map (pinnedSplitting X.toRingedSpace i j) ≫
        c.tensorComparison.app (baseShift X.toRingedSpace i, baseShift X.toRingedSpace j)) := by
      have : IsIso (c.tensorComparison.app
          (baseShift X.toRingedSpace i, baseShift X.toRingedSpace j)) :=
        NatIso.isIso_app_of_isIso _ _
      infer_instance
    have h₁ : Function.Bijective (fun η : cohomologyModule E0 j =>
        (cupPairing (globalCupProduct c) P E0 i j).hom (generatingClass c i ⊗ₜ η)) := by
      let χ' := asIso (c.pullback.map (pinnedSplitting X.toRingedSpace i j) ≫
        c.tensorComparison.app (baseShift X.toRingedSpace i, baseShift X.toRingedSpace j))
      have hχ : Function.Bijective (fun g :
          (T.obj (c.pullback.obj (baseShift X.toRingedSpace i))).obj
          (c.pullback.obj (baseShift X.toRingedSpace j)) ⟶ Z => χ'.hom ≫ g) :=
        ⟨fun g₁ g₂ h => (Iso.cancel_iso_hom_left χ' g₁ g₂).1 h,
          fun g => ⟨χ'.inv ≫ g, χ'.hom_inv_id_assoc g⟩⟩
      have hR : Function.Bijective
          ((fun g => (c.pullback.map (pinnedSplitting X.toRingedSpace i j) ≫
              c.tensorComparison.app (baseShift X.toRingedSpace i, baseShift X.toRingedSpace j)) ≫
            (T.obj P).map g) ∘ elementAdjunct c E0 j) :=
        hχ.comp ((bijective_map_tensorPullbackBaseShift X.toRingedSpace i _ _).comp
          (bijective_elementAdjunct c E0 j))
      have hEq : (elementAdjunct c Z (i + j)) ∘ (fun η : cohomologyModule E0 j =>
          (cupPairing (globalCupProduct c) P E0 i j).hom (generatingClass c i ⊗ₜ η)) =
          (fun g => (c.pullback.map (pinnedSplitting X.toRingedSpace i j) ≫
              c.tensorComparison.app (baseShift X.toRingedSpace i, baseShift X.toRingedSpace j)) ≫
            (T.obj P).map g) ∘ elementAdjunct c E0 j := by
        funext η
        exact (elementAdjunct_cupPairing_generatingClass c E0 i j η).trans
          (Category.assoc _ _ _).symm
      rw [← hEq] at hR
      exact (Function.Bijective.of_comp_iff' (bijective_elementAdjunct c Z (i + j)) _).1 hR
    have h₂ : Function.Bijective (eqToHom (show cohomologyModule Z (i + j) =
        cohomologyModule Z d by rw [hij])).hom :=
      (eqToIso (show cohomologyModule Z (i + j) = cohomologyModule Z d by
        rw [hij])).toLinearEquiv.bijective
    exact h₂.comp h₁
  let e := LinearEquiv.ofBijective cupGen.hom hcupGen
  have hformula : ∀ (ξ : sheafCohomology f (tensorModule ω (dualModule E)) i)
      (η : sheafCohomology f E j),
      serrePairing f hCM hequi d hd E i j hij ξ η =
        ((ModuleCat.restrictScalars.{u} (globalRingHom f)).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) d).map
            ((baseSections X.toRingedSpace).map (Ψ (elementAdjunct c G0 i ξ)))) ≫
          topTrace f hCM hequi d hd).hom (cupGen.hom η) := by
    intro ξ η
    rw [serrePairing_apply]
    refine congrArg (topTrace f hCM hequi d hd).hom ?_
    let H := fun n : ℤ =>
      DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) n
    let ξ' := elementAdjunct c G0 i ξ
    let y := (cupPairing (globalCupProduct c) P E0 i j).hom (generatingClass c i ⊗ₜ η)
    have h₁ := map_elementAdjunct_generatingClass c G0 i ξ
    have h₂ := cupPairing_naturality_apply (globalCupProduct c) ξ' (𝟙 E0) i j
      (generatingClass c i) η
    have hT : (Functor.uncurry.obj T).map (ξ' ×ₘ 𝟙 E0) = (T.map ξ').app E0 :=
      (congrArg (fun g => (T.map ξ').app E0 ≫ g) ((T.obj G0).map_id E0)).trans
        (Category.comp_id _)
    have h₃ := eqToHom_comp_homologyFunctor_map (X := X) (Ψ ξ') hij
    have hid : ((H j).map ((baseSections X.toRingedSpace).map (𝟙 E0))).hom η = η :=
      congrArg (fun φ => φ.hom η)
        ((congrArg (H j).map ((baseSections X.toRingedSpace).map_id E0)).trans ((H j).map_id _))
    let castω : cohomologyModule (singleModule ω) (i + j) ⟶ cohomologyModule (singleModule ω) d :=
      eqToHom (by rw [hij])
    let Hβ := (H (i + j)).map ((baseSections X.toRingedSpace).map (contractionMap ω E))
    have e₁ : (contractedCupProduct (dualizingModule f) E i j d hij).hom (ξ ⊗ₜ η) =
        castω.hom (Hβ.hom ((cupPairing (globalCupProduct c) G0 E0 i j).hom (ξ ⊗ₜ η))) := rfl
    have e₂ : (cupPairing (globalCupProduct c) G0 E0 i j).hom (ξ ⊗ₜ η) =
        ((H (i + j)).map ((baseSections X.toRingedSpace).map ((T.map ξ').app E0))).hom y :=
      (congrArg (fun z => (cupPairing (globalCupProduct c) G0 E0 i j).hom z)
        (congrArg₂ (fun a b => a ⊗ₜ[↑(baseRing X.toRingedSpace)] b) h₁.symm hid.symm)).trans
        (h₂.trans (congrArg (fun φ => ((H (i + j)).map
          ((baseSections X.toRingedSpace).map φ)).hom y) hT))
    have hcomp : (H (i + j)).map ((baseSections X.toRingedSpace).map ((T.map ξ').app E0)) ≫ Hβ =
        (H (i + j)).map ((baseSections X.toRingedSpace).map (Ψ ξ')) :=
      ((H (i + j)).map_comp _ _).symm.trans
        (congrArg (H (i + j)).map ((baseSections X.toRingedSpace).map_comp _ _).symm)
    exact e₁.trans ((congrArg (fun z => castω.hom (Hβ.hom z)) e₂).trans
      ((congrArg castω.hom (congrArg (fun φ => φ.hom y) hcomp)).trans
        (congrArg (fun φ => φ.hom y) h₃)))
  have hprecomp : Function.Bijective (fun φ : (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj
      (cohomologyModule Z d) ⟶ ModuleCat.of k k => φ.hom ∘ₗ e.toLinearMap) :=
    (e.arrowCongr (LinearEquiv.refl k k)).symm.bijective.comp ModuleCat.homEquiv.bijective
  have heq : (serrePairing f hCM hequi d hd E i j hij : _ → _) =
      (fun φ : (ModuleCat.restrictScalars.{u} (globalRingHom f)).obj (cohomologyModule Z d) ⟶
          ModuleCat.of k k => φ.hom ∘ₗ e.toLinearMap) ∘
        (fun β : Z ⟶ singleModule ω =>
          (ModuleCat.restrictScalars.{u} (globalRingHom f)).map
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) d).map
              ((baseSections X.toRingedSpace).map β)) ≫ topTrace f hCM hequi d hd) ∘ Ψ ∘
        elementAdjunct c G0 i := by
    funext ξ
    exact LinearMap.ext fun η => hformula ξ η
  rw [heq]
  exact hprecomp.comp (hB3.comp (hΨ.comp (bijective_elementAdjunct c G0 i)))

/-- **`Hⁿ(RΓ(X, ℱ[0])) = Rⁿ Γ(X, ℱ)`** for every integer `n`, for the derived global sections of
the cup product. -/
def homologyBaseSectionsSingleIso (n : ℤ) :
    DerivedCategory.singleFunctor X.Modules 0 ⋙ baseSections X.toRingedSpace ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) n ≅
      (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace ⊤).rightDerivedPlus
        n :=
  Functor.isoWhiskerRight (Stacks.DerivedFunctor.singleIsoResCompQh (A := X.Modules))
      (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen X.toRingedSpace ⊤ ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) n) ≪≫
    Stacks.DerivedFunctor.resCompQhReassocIso
      (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen X.toRingedSpace ⊤) n ≪≫
    Functor.isoWhiskerRight (Stacks.DerivedFunctor.resCompUnitIso
        (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace ⊤)
        (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen X.toRingedSpace ⊤)
        (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X.toRingedSpace ⊤)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective
          X.toRingedSpace)).symm
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) n) ≪≫
    Stacks.DerivedFunctor.resCompMapQhHomologyIso
      (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace ⊤) n ≪≫
    Functor.isoWhiskerLeft (Stacks.DerivedIndexing.resH (C := X.Modules) ⋙
        Functor.mapHomotopyCategory
          (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace ⊤)
          (ComplexShape.up ℤ))
      (DerivedCategory.homologyFunctorFactorsh
        (ModuleCat.{u} (baseRing X.toRingedSpace)) n) ≪≫
    (Stacks.DerivedIndexing.rightDerivedPlusIsoRes
      (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace ⊤) n).symm

/-- **`Hⁿ(X, ℱ) = 0` for `n < 0`**, part (1) of [Stacks, Tag 05TD]. -/
theorem isZero_cohomologyModule_singleModule_of_neg (F : X.Modules) {n : ℤ} (hn : n < 0) :
    IsZero (cohomologyModule (singleModule F) n) :=
  (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj
    (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace ⊤) n hn F).of_iso
      ((homologyBaseSectionsSingleIso (X := X) n).app F)

/-- **`Hⁿ(X, ℱ)` is finite dimensional** for `ℱ` coherent on `X` proper over `k`
([Stacks, Tag 02O6]), read in the framework of the cup product through `cohomologyBridge`. -/
theorem finiteDimensional_sheafCohomology (F : X.Modules) [F.IsCoherent] (n : ℤ) :
    FiniteDimensional k (sheafCohomology f F n) := by
  rcases lt_or_ge n 0 with hn | hn
  · have : Subsingleton (cohomologyModule (singleModule F) n) :=
      ModuleCat.subsingleton_of_isZero (isZero_cohomologyModule_singleModule_of_neg F hn)
    have : Subsingleton (sheafCohomology f F n) := this
    exact Module.Finite.of_finite
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hfin := finiteDimensional_cohomologyOverField_of_isProper k f F m
    let e₁ := ((cohomologyBridge f m).app (singleModule F)).toLinearEquiv
    let e₂ := ((@DerivedCategory.homologyFunctor (ModuleCat.{u} k) _ _ ModuleCat.hasDerivedCategory
      (m : ℤ)).mapIso ((@derivedGlobalSectionsOver k _ X f (Scheme.Modules.hasDerivedCategory X)
        ModuleCat.hasDerivedCategory).mapIso
        ((Scheme.Modules.derivedModelEquivCompQIso X).app
          ((CochainComplex.singleFunctor X.Modules 0).obj F)))).toLinearEquiv
    let e₃ := (cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f F m).symm
    exact Module.Finite.equiv (e₁.trans (e₂.trans e₃)).symm

/-- **[Stacks, Tag 0FW0].** Let `X` be a proper Cohen--Macaulay scheme over a field `k` which is
equidimensional of dimension `d`, let `ω_X^•` and `ω_X` be as in [Stacks, Tag 0FVV], so that
`ω_X^• = ω_X[d]` by [Stacks, Tag 0FVZ], and let `t : Hᵈ(X, ω_X) ⟶ k` be the trace of
[Stacks, Tag 0FVW] (`Stacks.Duality.topTrace`). Let `ℰ` be a finite locally free `𝒪_X`-module with
dual `ℰ^∨`. Then for all `i + j = d` the pairing

`Hⁱ(X, ω_X ⊗_{𝒪_X} ℰ^∨) × Hʲ(X, ℰ) ⟶ k,  (ξ, η) ↦ t((1 ⊗ ε)(ξ ∪ η))`

(`Stacks.Duality.serrePairing`) is perfect, where `∪` is the cup product of Cohomology,
Section 0FKU and `ε : ℰ^∨ ⊗_{𝒪_X} ℰ ⟶ 𝒪_X` is the evaluation map. -/
@[stacks 0FW0]
theorem serrePairing_isPerfPair (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (E : X.Modules) (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (i j : ℤ) (hij : i + j = d) :
    (serrePairing f hCM hequi d hd E i j hij).IsPerfPair := by
  have := isQuasicoherent_of_isFiniteLocallyFree E hE
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E :=
    ⟨hE.exists_isFiniteLocallyFreeData⟩
  have : E.IsFiniteType :=
    (Stacks.FiniteLocallyFree.isLocallyFree_isFiniteType_isFinitePresentation E).2.1
  have : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType E
  have := finiteDimensional_sheafCohomology f E j
  exact LinearMap.IsPerfPair.of_bijective _ (bijective_serrePairing f hCM hequi d hd E hE i j hij)

end Perfect

end Stacks.Duality

end
