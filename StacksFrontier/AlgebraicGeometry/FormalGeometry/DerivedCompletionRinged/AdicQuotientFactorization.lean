module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientLocalAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ReflectorCompletion
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedLimits

import StacksCore.Tactic.StacksAttribute

/-!
# The factorization of the derived reductions through the derived completion

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals and `K ↦ K^∧` a derived completion
functor, i.e. a left adjoint of the inclusion of the derived-complete objects into `D(𝒪)`.
Since `K ⊗^𝐋_𝒪 𝒪/ℐⁿ` is derived complete
(`AlgebraicGeometry.RingedSite.isDerivedComplete_derivedTensor_adicQuotient`), the derived
reduction `K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ` factors uniquely as `K ⟶ K^∧ ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ`; the factorizations
are compatible for varying `n`, and so induce a comparison map
`K^∧ ⟶ R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ)`. These are the constructions of [Stacks, Tag 0CQH], stated here for
an arbitrary sheaf of ideals and an arbitrary reflector; the tag itself, at its own hypothesis
that `ℐ` be of finite type and with the reflector of [Stacks, Tag 099F], is registered in
the sibling file `AdicQuotientCompletionComparison.lean`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor`: the factorization
  `K^∧ ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ`.
* `AlgebraicGeometry.RingedSite.adicQuotientTower`: the tower `n ↦ 𝒪/ℐⁿ⁺¹` as an inverse system.
* `AlgebraicGeometry.RingedSite.adicReductionTower`: the tower `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` in `D(𝒪)`.

## Main results

* `AlgebraicGeometry.RingedSite.existsUnique_derivedCompletion_factorization_adicQuotient`: the
  unique factorization.
* `AlgebraicGeometry.RingedSite.derivedCompletionAdicFactor_comp_map`: its compatibility.
* `Stacks.InverseSystem.exists_isDerivedLimit_comparison`: a cone over a tower in a
  pretriangulated category induces a map into a derived limit of the tower.
* `AlgebraicGeometry.RingedSite.exists_derivedCompletionComparison`: the comparison map
  `K^∧ ⟶ R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ)`.

## Implementation notes

A derived limit is determined only up to non-unique isomorphism, and is recorded by
`CategoryTheory.Pretriangulated.IsDerivedLimit` as the base of a distinguished Milnor triangle
`R lim Tₙ ⟶ ∏ Tₙ ⟶ ∏ Tₙ ⟶`; the comparison map is a map into such a base whose composites with
the projections are the factorizations. It is likewise not unique.

## References

* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace Stacks.InverseSystem

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A cone over a tower induces a map into a derived limit of the tower**, compatibly with
the projections. The cone, read as a map into the product, kills the Milnor difference, so it
factors through the base of the Milnor triangle by exactness of that triangle against the
source. The factorization is not claimed to be unique. -/
theorem exists_isDerivedLimit_comparison (T : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => T.obj ⟨n⟩] {Y : D} (c : ∀ n : ℕ, Y ⟶ T.obj ⟨n⟩)
    (hc : ∀ n : ℕ, c (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op = c n) :
    ∃ (L : D) (p : L ⟶ ∏ᶜ fun n : ℕ => T.obj ⟨n⟩)
      (δ : (∏ᶜ fun n : ℕ => T.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧) (g : Y ⟶ L),
      Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => T.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => T.obj ⟨n⟩) (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang D ∧
        ∀ n : ℕ, g ≫ p ≫ Pi.π (fun n : ℕ => T.obj ⟨n⟩) n = c n := by
  obtain ⟨L, p, δ, hδ⟩ := Pretriangulated.exists_isDerivedLimit T
  have hw : (Pi.lift c) ≫ (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => T.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => T.obj ⟨n⟩) (n + 1) ≫ T.map (homOfLE (Nat.le_succ n)).op) = 0 := by
    refine Pi.hom_ext _ _ fun n => ?_
    rw [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, Pi.lift_comp_π, ← Category.assoc,
      Pi.lift_comp_π, hc n, sub_self, zero_comp]
  obtain ⟨g, hg⟩ := (Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => T.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ => T.obj ⟨n⟩) (n + 1) ≫
      T.map (homOfLE (Nat.le_succ n)).op) δ).coyoneda_exact₂ hδ (Pi.lift c) hw
  have hg' : Pi.lift c = g ≫ p := hg
  refine ⟨L, p, δ, g, hδ, fun n => ?_⟩
  rw [← Category.assoc, ← hg', Pi.lift_comp_π]

end Stacks.InverseSystem

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- Countable products exist in `D(𝒪)`, as
`AlgebraicGeometry.RingedSite.hasProductsOfShape_nat_derivedCategory_ringSheaf` at a single
universe. -/
local instance hasProductsOfShape_nat_derivedCategory_ringSheaf_adicQuotientFactorization :
    HasProductsOfShape ℕ
      (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
  hasProductsOfShape_nat_derivedCategory_ringSheaf.{u, u, u} X

section Tower

/-- The tower `n ↦ 𝒪/ℐⁿ⁺¹` of quotients of the structure sheaf by the positive powers of `ℐ`, as
an inverse system indexed by `ℕᵒᵖ`. The index is shifted by one because [Stacks, Tag 0CQH] forms
the comparison map out of the reductions modulo `ℐⁿ` for `n ≥ 1`. -/
def adicQuotientTower : ℕᵒᵖ ⥤ SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Functor.ofOpSequence
    (X := fun n : ℕ => Stacks.Sites.adicQuotientModule (X := X) I (n + 1))
    fun n : ℕ => Stacks.Sites.adicQuotientModuleMap (X := X) I (Nat.le_succ (n + 1))

/-- The successive transition map of the tower is the transition map of the quotients. -/
theorem adicQuotientTower_map_succ (n : ℕ) :
    (adicQuotientTower X I).map (homOfLE (Nat.le_succ n)).op =
      Stacks.Sites.adicQuotientModuleMap (X := X) I (Nat.le_succ (n + 1)) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The tower `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` of derived reductions, as an inverse system in `D(𝒪)`. -/
abbrev adicReductionTower
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  adicQuotientTower X I ⋙
    DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0 ⋙
      (Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K

/-- Maps into the reductions that are compatible for varying `n` form a cone over the tower. -/
private theorem comp_adicReductionTower_map_succ
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    {A : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (f : ∀ n : ℕ, A ⟶ ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
      (adicQuotientObj X I n))
    (hf : ∀ {m n : ℕ} (h : m ≤ n), f n ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
            (Stacks.Sites.adicQuotientModuleMap (X := X) I h)) = f m) (n : ℕ) :
    f (n + 1 + 1) ≫ (adicReductionTower X I K).map (homOfLE (Nat.le_succ n)).op = f (n + 1) := by
  rw [← hf (Nat.le_succ (n + 1)), ← adicQuotientTower_map_succ]
  rfl

/-- The derived reductions form a cone over the reduction tower. -/
theorem adicQuotientReduction_comp_adicReductionTower_map_succ
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (n : ℕ) :
    adicQuotientReduction X I K (n + 1 + 1) ≫
        (adicReductionTower X I K).map (homOfLE (Nat.le_succ n)).op =
      adicQuotientReduction X I K (n + 1) :=
  comp_adicReductionTower_map_succ X I K (adicQuotientReduction X I K)
    (adicQuotientReduction_comp_map X I K) n

end Tower

variable [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]

/-- **The factorization `K^∧ ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ` of [Stacks, Tag 0CQH]**: the map the reflector
adjunction attaches to the derived reduction, whose target is derived complete. -/
def derivedCompletionAdicFactor
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (n : ℕ) :
    (derivedCompletion X I).obj K ⟶
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        (adicQuotientObj X I n) :=
  (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).map
    (((derivedCompletionAdjunction X I).homEquiv K
        ⟨_, isDerivedComplete_derivedTensor_adicQuotient X I K n⟩).symm
      (adicQuotientReduction X I K n))

/-- The factorization does factor the derived reduction through the derived completion. -/
theorem derivedCompletionUnit_comp_derivedCompletionAdicFactor
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (n : ℕ) :
    (derivedCompletionUnit X I).app K ≫ derivedCompletionAdicFactor X I K n =
      adicQuotientReduction X I K n :=
  ((derivedCompletionAdjunction X I).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- **The canonical factorization.** The derived reduction `K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ` factors uniquely
as `K ⟶ K^∧ ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ` through the derived completion, for an arbitrary sheaf of ideals
and an arbitrary reflector. -/
@[stacks 0CQH "second assertion: the canonical factorization `K → K^∧ → K ⊗^L O/I^n` of the
  canonical map, for the derived completion functor of Tag 099F"]
theorem existsUnique_derivedCompletion_factorization_adicQuotient
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (n : ℕ) :
    ∃! g : (derivedCompletion X I).obj K ⟶
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
          (adicQuotientObj X I n),
      (derivedCompletionUnit X I).app K ≫ g = adicQuotientReduction X I K n :=
  ⟨derivedCompletionAdicFactor X I K n,
    derivedCompletionUnit_comp_derivedCompletionAdicFactor X I K n,
    fun _g hg ↦ derivedCompletion_hom_ext X I
      (isDerivedComplete_derivedTensor_adicQuotient X I K n)
      (hg.trans (derivedCompletionUnit_comp_derivedCompletionAdicFactor X I K n).symm)⟩

/-- **The factorizations are compatible for varying `n`.** The factorization through `K^∧` of
the reduction modulo `ℐⁿ`, followed by the transition map `𝒪/ℐⁿ ⟶ 𝒪/ℐᵐ`, is the factorization
of the reduction modulo `ℐᵐ`. -/
@[stacks 0CQH "third assertion: the factorizations are compatible for varying `n`"]
theorem derivedCompletionAdicFactor_comp_map
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    {m n : ℕ} (h : m ≤ n) :
    derivedCompletionAdicFactor X I K n ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
            (Stacks.Sites.adicQuotientModuleMap (X := X) I h)) =
      derivedCompletionAdicFactor X I K m := by
  refine derivedCompletion_hom_ext X I (isDerivedComplete_derivedTensor_adicQuotient X I K m) ?_
  rw [← Category.assoc, derivedCompletionUnit_comp_derivedCompletionAdicFactor,
    derivedCompletionUnit_comp_derivedCompletionAdicFactor]
  exact adicQuotientReduction_comp_map X I K h

/-- The factorizations through the derived completion are a cone over the reduction tower. -/
theorem derivedCompletionAdicFactor_comp_adicReductionTower_map_succ
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (n : ℕ) :
    derivedCompletionAdicFactor X I K (n + 1 + 1) ≫
        (adicReductionTower X I K).map (homOfLE (Nat.le_succ n)).op =
      derivedCompletionAdicFactor X I K (n + 1) :=
  comp_adicReductionTower_map_succ X I K (derivedCompletionAdicFactor X I K)
    (derivedCompletionAdicFactor_comp_map X I K) n

/-- **The comparison map `K^∧ ⟶ R lim (K ⊗^𝐋_𝒪 𝒪/ℐⁿ)`.** The compatible factorizations
`K^∧ ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹` lift through the Milnor triangle of the reduction tower to a map into its
derived limit, whose composite with each projection is the corresponding factorization. -/
@[stacks 0CQH "fourth assertion: the comparison map `K^∧ → R lim (K ⊗^L O/I^n)` induced by the
  compatible factorizations; `R lim` is presented by its Milnor triangle"]
theorem exists_derivedCompletionComparison
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    ∃ (L : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (p : L ⟶ ∏ᶜ fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩)
      (δ : (∏ᶜ fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
      (c : (derivedCompletion X I).obj K ⟶ L),
      Triangle.mk p (Pi.lift fun n : ℕ =>
            Pi.π (fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩) (n + 1) ≫
              (adicReductionTower X I K).map (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang
            (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ∧
        ∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ => (adicReductionTower X I K).obj ⟨n⟩) n =
          derivedCompletionAdicFactor X I K (n + 1) :=
  Stacks.InverseSystem.exists_isDerivedLimit_comparison (adicReductionTower X I K)
    (fun n => derivedCompletionAdicFactor X I K (n + 1))
    (derivedCompletionAdicFactor_comp_adicReductionTower_map_succ X I K)

end AlgebraicGeometry.RingedSite

end
