module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.AdicSystem.CanonicalDerivedTensor
public import StacksFrontier.RingTheory.Module.AdicSystem.DerivedTensorScalarCompat
public import StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor

@[expose] public section

/-!
# Vanishing of Tor maps out of powers of an ideal

Let `I` be an ideal of a Noetherian ring `A`, let `M` be a finite `A`-module and let `N` be an
`A`-module annihilated by `I`.  For some positive power of `I` the inclusion `I^n M -> M`
induces the zero map on `Tor_p(-, N)` in every degree `p`.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.TorIdealPowerVanishing.torMap_idealPowerInclusion_eq_zero` (tag 0FXN) is the simultaneous
  vanishing in
  every degree.

## Implementation notes

Tor groups are the homology objects of the derived tensor product, so the homology degree
`-(p : Int)` represents `Tor_p`.  Positive powers are indexed by `n : Nat` with exponent
`n + 1`, matching the ideal-power system of tag 0G3N in
`StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor`, whose pro-isomorphism supplies the
factorisation of the inclusion through the derived tensor product.  The annihilation consequence
of associativity is `StacksDraft.ScalarCompat.tensor_unitMap_zero`.  This file registers no tag
other than 0FXN.

## References

* [Stacks Project, Tag 0FXN](https://stacks.math.columbia.edu/tag/0FXN)
-/

universe u

noncomputable section

namespace Stacks.TorIdealPowerVanishing

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false in
/-- If `M` is a finite module over a Noetherian ring and `N` is annihilated by an ideal `I`, then
for some positive power of `I` the inclusion `IⁿM ⟶ M` induces zero on `Tor_p(-, N)` for every
`p ≥ 0`, for the Tor formed from any derived tensor product bundle. The index `n` denotes the
positive exponent `n + 1`.

This is the form general in the bundle; the canonical derived tensor product is substituted in
`torMap_idealPowerInclusion_eq_zero`. -/
public theorem torMap_idealPowerInclusion_eq_zero_of_data
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (D : DerivedTensorData.DerivedTensorProduct A)
    (symmetry : D.tensor ≅ D.tensor.flip)
    (I : Ideal A) (M N : ModuleCat.{u} A) [Module.Finite A M]
    (hN : I ≤ Module.annihilator A N) :
    let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
    let N₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N
    ∃ n : ℕ, ∀ p : ℕ,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(p : ℤ))).map
          ((D.tensor.flip.obj N₀).map
            (DerivedCategory.Q.map
              (image.ι (Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerMultiplication K I
                n)))) = 0 := by
  open Stacks.AdicSystem.IdealPowerTensorComparison in
  intro K N₀
  have hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i) :=
    ⟨0, 0, le_rfl, fun _ hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  have hfinite : ∀ i : ℤ, Module.Finite A (K.X i) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      change Module.Finite A M
      infer_instance
    · have : Subsingleton (K.X i) := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)
      infer_instance
  obtain ⟨t, ht, α, hα, hinv⟩ :=
    derivedTensor_idealPowers_proIsomorphic_of_data D symmetry I K hbounded hfinite
  obtain ⟨n, hn, f, _, hf⟩ := hinv 0
  let ι : idealPowerSystem K I t ⟶ (Functor.const ℕᵒᵖ).obj (DerivedCategory.Q.obj K) :=
    NatTrans.ofOpSequence
      (fun n => DerivedCategory.Q.map (image.ι (idealPowerMultiplication K I n))) (by
      intro n
      simp only [idealPowerSystem, Functor.ofOpSequence_map_homOfLE_succ,
        Functor.const_obj_map, Functor.const_obj_obj, Category.comp_id,
        ← DerivedCategory.Q.map_comp, ht])
  have hfactor : f ≫ (derivedToIdealPowerMap D symmetry K I 0 ≫
      DerivedCategory.Q.map (image.ι (idealPowerMultiplication K I 0))) =
      DerivedCategory.Q.map (image.ι (idealPowerMultiplication K I n)) := by
    rw [← hα 0, ← Category.assoc, hf]
    simpa only [Functor.const_obj_map, Functor.const_obj_obj, Category.comp_id,
      ι, NatTrans.ofOpSequence_app] using ι.naturality (homOfLE hn).op
  -- Since `I` annihilates `N`, the multiplication map `I ⊗ N ⟶ A ⊗ N ⟶ N` is zero.
  have hscalar : ((tensoringRight (ModuleCat.{u} A)).obj N).map (idealPowerSubtype I 0) ≫
      (MonoidalCategory.leftUnitor N).hom = 0 := by
    apply ModuleCat.hom_ext
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul j m =>
        change (j : A) • m = 0
        apply Module.mem_annihilator.mp (hN ?_) m
        change (j : A) ∈ I
        simpa using j.property
    | add x y hx hy => simp only [map_add, hx, hy]
  have heq : derivedToIdealPowerMap D symmetry K I 0 ≫
      DerivedCategory.Q.map (image.ι (idealPowerMultiplication K I 0)) =
      (symmetry.hom.app ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (idealPowerModule I 0))).app (DerivedCategory.Q.obj K) ≫
        (D.comparison (idealPowerModule I 0)).app K ≫
        DerivedCategory.Q.map (DerivedTensorData.tensorRightUnitMapComplex K
          (idealPowerModule I 0) (idealPowerSubtype I 0)) := by
    simp only [derivedToIdealPowerMap, DerivedTensorData.tensorRightUnitMapComplex,
      idealPowerMultiplication, Category.assoc, ← DerivedCategory.Q.map_comp, image.fac]
  have hzero : (D.tensor.flip.obj N₀).map (derivedToIdealPowerMap D symmetry K I 0 ≫
      DerivedCategory.Q.map (image.ι (idealPowerMultiplication K I 0))) = 0 := by
    rw [heq]
    exact StacksDraft.ScalarCompat.tensor_unitMap_zero (idealPowerModule I 0)
      (idealPowerSubtype I 0) D symmetry K N hscalar
  exact ⟨n, fun p => by
    rw [← hfactor, Functor.map_comp, Functor.map_comp, hzero, Functor.map_zero, comp_zero]⟩

/-- **Stacks Project, Tag 0FXN.** If `M` is a finite module over a Noetherian ring and `N`
is annihilated by an ideal `I`, then for some positive power of `I` the inclusion
`IⁿM ⟶ M` induces zero on `Tor_p(-, N)` for every `p ≥ 0`. The index `n` denotes the
positive exponent `n + 1`. -/
@[stacks 0FXN]
public theorem torMap_idealPowerInclusion_eq_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M N : ModuleCat.{u} A) [Module.Finite A M]
    (hN : I ≤ Module.annihilator A N) :
    let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
    let N₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N
    ∃ n : ℕ, ∀ p : ℕ,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(p : ℤ))).map
          (((DerivedTensorData.canonicalDerivedTensorProduct A).tensor.flip.obj N₀).map
            (DerivedCategory.Q.map
              (image.ι (Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerMultiplication K I
                n)))) = 0 :=
  torMap_idealPowerInclusion_eq_zero_of_data _ (DerivedTensorData.canonicalSymmetry A) I M N hN

end Stacks.TorIdealPowerVanishing

end

end
