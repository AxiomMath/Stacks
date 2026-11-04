module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafExcisionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCompactSupportRightExact

/-!
# `H²_c` does not see a finite set of points

Let `Y` be a scheme over a finite field `k` with a compactification, `U ⊆ Y` an open subscheme
whose closed complement `Z` has dimension `0`, and `k̄` an algebraically closed extension of `k`.
For every sheaf `G` of `ℤ/m`-modules on `Y_étale`, the open part `j_! j⁻¹ G → G` induces an
isomorphism

`H²_c(Y_k̄, j_! j⁻¹ G) ≅ H²_c(Y_k̄, G)`:

in the long exact sequence of `0 → j_! j⁻¹ G → G → i_* i⁻¹ G → 0` the neighbouring terms
`Hⁱ_c(Y_k̄, i_* i⁻¹ G) = Hⁱ_c(Z_k̄, i⁻¹ G)` vanish for `i = 1, 2` because `Z` has dimension `0`
(`isZero_compactSupportFrobeniusCohomologyGroup_single_of_topologicalKrullDim_le`).
Together with `Hⁱ_c(U_k̄, -) ≅ Hⁱ_c(Y_k̄, j_! -)`
(`Stacks.EtaleCohomology.compactSupportSheafCohomologyRestrictOpenIso`) this computes the top
cohomology of a curve with compact support on its smooth compactification, as in the proof of
[Stacks, Tag 03VK].

## Main results

* `Stacks.EtaleCohomology.bijective_compactSupportSheafCohomology_two_extensionByZero_counit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {Y : Scheme.{u}}
  (fY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType fY] [QuasiCompact fY] [IsSeparated fY]
  (jY : CompactificationOf (Over.mk fY)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar] (m : ℕ) [NeZero m]
  {Z U : Scheme.{u}} (iZ : Z ⟶ Y) [IsClosedImmersion iZ] (jU : U ⟶ Y) [IsOpenImmersion jU]
  (hij : Set.range jU.base = (Set.range iZ.base)ᶜ)

omit [Fintype k] in
include hij in
/-- **`H²_c(Y_k̄, j_! j⁻¹ G) ≅ H²_c(Y_k̄, G)`** when the closed complement of the open `U` has
dimension `0`. -/
theorem bijective_compactSupportSheafCohomology_two_extensionByZero_counit [Finite k]
    (hZ : topologicalKrullDim Z ≤ 0) (G : EtaleModules.{u, 0} (ZMod m) Y) :
    Function.Bijective ((compactSupportSheafCohomology (ZMod m) fY jY kbar 2).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod m) jU).counit.app G)).hom := by
  have := Fintype.ofFinite k
  obtain ⟨h, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage (ZMod m) iZ jU hij G
  have hS' := hS.map_of_exact (HomologicalComplex.single (EtaleModules.{u, 0} (ZMod m) Y)
    (ComplexShape.up ℤ) 0)
  have hvan : ∀ i : ℤ, 0 < i → IsZero ((compactSupportSheafCohomology (ZMod m) fY jY kbar i).obj
      ((etaleModuleDirectImage.{u, 0} (ZMod m) iZ).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod m) iZ).obj G))) := fun i hi =>
    (isZero_compactSupportFrobeniusCohomologyGroup_single_of_topologicalKrullDim_le (iZ ≫ fY)
      (jY.restrictClosed iZ) kbar m ((etaleModuleInverseImage.{u, 0} (ZMod m) iZ).obj G) 0
      (by exact_mod_cast hZ) i (by lia)).of_iso
      ((compactSupportSheafCohomologyRestrictClosedIso (ZMod m) fY jY kbar i iZ).app
        ((etaleModuleInverseImage.{u, 0} (ZMod m) iZ).obj G)).symm
  have hge : ∀ X : EtaleModules.{u, 0} (ZMod m) Y, ∃ n : ℤ, CochainComplex.IsStrictlyGE
      ((HomologicalComplex.single (EtaleModules.{u, 0} (ZMod m) Y) (ComplexShape.up ℤ) 0).obj X)
      n := fun X => ⟨0, inferInstance⟩
  have hmono := mono_homology_compactSupportFrobeniusFunctor_map_f (ZMod m) fY jY kbar hS'
    (hge _) (hge _) (hge _) 1 2 (by norm_num) (hvan 1 (by norm_num))
  have hepi := epi_homology_compactSupportFrobeniusFunctor_map_f (ZMod m) fY jY kbar hS'
    (hge _) (hge _) (hge _) 2 (hvan 2 (by norm_num))
  exact ⟨(ModuleCat.mono_iff_injective _).1 hmono, (ModuleCat.epi_iff_surjective _).1 hepi⟩

end Stacks.EtaleCohomology

end
