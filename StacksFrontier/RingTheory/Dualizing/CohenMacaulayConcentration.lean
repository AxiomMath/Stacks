module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Data.List.TFAE
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayCriterion
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayDuality
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds

/-!
# Cohen--Macaulay local rings and the concentration of a dualizing complex

Let `(A, 𝔪, κ)` be a Noetherian local ring with a normalized dualizing complex `ω_A^\bullet`,
and let `d = dim(A)`. If `A` is Cohen--Macaulay then `H^i(ω_A^\bullet) = 0` for `i ≠ -d`.

This is read off from the module-level criterion
`Dualizing.isCohenMacaulay_iff_ext_concentrated` applied to the regular module: `A` is
Cohen--Macaulay as a module over itself exactly when `Ext^i_A(A, ω_A^\bullet)` is nonzero for at
most one `i`, and `Ext^i_A(A, -)` is the `i`-th cohomology because the regular module placed in
degree zero corepresents `H^0` on the derived category.

## Main results

* `Dualizing.isZero_homology_shift`: if `H^{n+i}(K)` vanishes then so does `H^i(K⟦n⟧)`.
* `Dualizing.isZero_homology_of_iso_single`: a complex isomorphic to a single complex in degree
  `n` has no cohomology away from degree `n`.

## Implementation notes

The dimension of `A` enters as a natural number `d` together with the hypothesis
`ringKrullDim A = d`; such a `d` exists for every Noetherian local ring, so this adds no
assumption.

The criterion `Dualizing.isCohenMacaulay_iff_ext_concentrated` is stated for modules in the
universe `max v u` of the derived category, so it is applied to the universe-lifted regular module
`ULift.{v} A`; depth and the dimension of the support are invariant under the linear equivalence
`ULift.moduleEquiv`.

## References

* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

section ExtFromRegular

variable {A : Type u} [CommRing A]

/-- Evaluation at `1` identifies homomorphisms out of the universe-lifted regular module with
the module itself. -/
private noncomputable def homFromUliftRegular (M : ModuleCat.{max v u} A) :
    (ModuleCat.of A (ULift.{v} A) ⟶ M) ≃ₗ[A] M :=
  (ModuleCat.homLinearEquiv (S := A)).trans
    ((LinearEquiv.arrowCongr (ULift.moduleEquiv (R := A) (M := A)) (LinearEquiv.refl A M)).trans
      (LinearMap.ringLmapEquivSelf A A M))

private instance : Projective (ModuleCat.of A (ULift.{v} A)) :=
  ModuleCat.projective_of_free (M := ModuleCat.of A (ULift.{v} A))
    (Module.Free.chooseBasis A (ULift.{v} A))

/-- **`Ext` out of the regular module is cohomology.** The universe-lifted regular module placed
in degree zero corepresents `H^0`, so `Ext^i_A(A, K) = H^i(K)`. -/
private noncomputable def extFromUliftRegular
    (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ) :
    DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (ULift.{v} A))) K i ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K) :=
  (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of A (ULift.{v} A))
      ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) i).obj K) 0 A).trans
    ((homFromUliftRegular.{u, v} _).trans
      ((StacksDraft.DerivedHom.ExtComparison.homologyShiftNatIso.{u, v} A i).app K).toLinearEquiv)

private theorem subsingleton_ext_iff_isZero_homology
    (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ) :
    Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (ULift.{v} A))) K i) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  exact (extFromUliftRegular.{u, v} K i).toEquiv.subsingleton_congr

/-- The support dimension of the universe-lifted regular module is that of the regular module. -/
private theorem supportDim_ulift_eq_self :
    Module.supportDim A (ULift.{v} A) = Module.supportDim A A :=
  Module.supportDim_eq_of_equiv (ULift.moduleEquiv (R := A) (M := A))

end ExtFromRegular

section Concentration

variable {A : Type u} [CommRing A]

/-- Shifting moves cohomology: if `H^{n+i}(K)` vanishes then so does `H^i(K⟦n⟧)`. -/
theorem isZero_homology_shift
    (K : DerivedCategory (ModuleCat.{max v u} A)) (n i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) (n + i)).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
      ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n).obj K)) := by
  have h' : IsZero
      (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).shift (n + i)).obj K) := by
    rwa [DerivedCategory.shift_homologyFunctor]
  have h2 : IsZero (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).shift i).obj
      ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n).obj K)) :=
    h'.of_iso (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).shiftIso
      n i (n + i) rfl).app K)
  rwa [DerivedCategory.shift_homologyFunctor] at h2

/-- A single complex has no cohomology away from its degree. -/
theorem isZero_homology_of_iso_single
    (K : DerivedCategory (ModuleCat.{max v u} A)) (n : ℤ) (M : ModuleCat.{max v u} A)
    (h : Nonempty (K ≅ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) n).obj M))
    (i : ℤ) (hi : i ≠ n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K) := by
  obtain ⟨e⟩ := h
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) n).obj M)) :=
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) n M i hi).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} A) i).app
        ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) n).obj M))
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).mapIso e)

end Concentration

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- Cohen--Macaulayness of a Noetherian local ring is Cohen--Macaulayness of the
universe-lifted regular module at the maximal ideal. -/
private theorem isCohenMacaulayLocalRing_iff_ulift :
    IsCohenMacaulayLocalRing A ↔
      Module.IsCohenMacaulayAtMaximalIdeal A (ULift.{v} A) := by
  have hproper : IsLocalRing.maximalIdeal A • (⊤ : Submodule A A) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have hdepth : Module.depth A (IsLocalRing.maximalIdeal A) (ULift.{v} A) =
      Module.depthSup A (IsLocalRing.maximalIdeal A) A := by
    rw [Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal A)
        (ULift.moduleEquiv (R := A) (M := A)),
      Module.depth, ite_eq_right hproper, Module.depthSup_eq_iSup]
  rw [isCohenMacaulayLocalRing_iff_isCohenMacaulayModule_self, IsCohenMacaulayModule,
    Module.IsCohenMacaulayAtMaximalIdeal, hdepth, supportDim_ulift_eq_self.{u, v}]
  rfl

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The support dimension of the universe-lifted regular module is the Krull dimension. -/
private theorem supportDim_ulift (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞)) :
    Module.supportDim A (ULift.{v} A) = (d : WithBot ℕ∞) := by
  rw [supportDim_ulift_eq_self.{u, v}, Module.supportDim_self_eq_ringKrullDim, hdim]

/-- Over a Cohen--Macaulay local ring the cohomology of a normalized dualizing complex vanishes
away from degree `-dim(A)`. -/
private theorem isZero_homology_of_ne_neg_dim
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K)
    (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞))
    (hA : IsCohenMacaulayLocalRing A)
    (i : ℤ) (hi : i ≠ -(d : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K) := by
  have hCM : Module.IsCohenMacaulayAtMaximalIdeal A (ULift.{v} A) :=
    isCohenMacaulayLocalRing_iff_ulift.{u, v}.mp hA
  have hsupp : Module.supportDim A (ULift.{v} A) = (d : WithBot ℕ∞) :=
    supportDim_ulift.{u, v} d hdim
  by_cases hpos : 0 < i
  · by_contra hnz
    have hIcc := ext_degree_mem_Icc_of_nontrivial (M := ULift.{v} A) K hK d hsupp i
      (not_subsingleton_iff_nontrivial.mp
        (mt (subsingleton_ext_iff_isZero_homology.{u, v} K i).mp hnz))
    exact absurd (Set.mem_Icc.mp hIcc).2 (by omega)
  · have hnotDim : ¬ (0 ≤ -i ∧ Module.supportDim A (ULift.{v} A) =
        (((-i).toNat : ℕ∞) : WithBot ℕ∞)) := by
      rintro ⟨-, hEq⟩
      have hnat : d = (-i).toNat := mod_cast hsupp.symm.trans hEq
      omega
    have hcrit3 : Module.IsCohenMacaulayAtMaximalIdeal A (ULift.{v} A) ↔
        (∀ j : ℤ,
          ¬ (0 ≤ j ∧ Module.supportDim A (ULift.{v} A) = ((j.toNat : ℕ∞) : WithBot ℕ∞)) →
            Subsingleton (DerivedCategory.Ext
              ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
                (ModuleCat.of A (ULift.{v} A))) K (-j))) :=
      (isCohenMacaulay_iff_ext_concentrated (M := ULift.{v} A) K hK).out 1 3
    have hzero := hcrit3.mp hCM (-i) hnotDim
    rw [neg_neg] at hzero
    exact (subsingleton_ext_iff_isZero_homology.{u, v} K i).mp hzero

end Main

end Dualizing

end
