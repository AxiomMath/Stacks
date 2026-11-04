module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# The unit of restriction to an open subspace on a module supported in it

Let `j : U ⟶ X` be an open immersion of algebraic spaces and let `Q` be an `𝒪_X`-module whose
support lies in `|U|`.  Then the unit `Q ⟶ j_*j^*Q` of the adjunction of Stacks 03LU is a
monomorphism: its kernel `N` restricts to zero on `U`, because `j^*` is exact and the restriction
of the unit is split by the counit, so the support of `N` misses `|U|`; but it lies in the support
of `Q`, which lies in `|U|`, so `N` has empty support and is zero.

Together with `CategoryTheory.Adjunction.kernelSubobject_map_cokernel_π_preimageQuotientMap` this
identifies a quotient of a direct image `j_*M` supported in `U` as the direct image of a
quotient of `M`.

## Main results

* `AlgebraicGeometry.Space.mono_modulePullbackAdjunction_unit_app`: the unit `Q ⟶ j_*j^*Q` is a
  monomorphism when the support of `Q` lies in the open subspace.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X : AlgebraicSpaces B S hS}

/-- **The unit of restriction to an open subspace is a monomorphism on a module supported in
it.**  For an open immersion `j : U ⟶ X` and an `𝒪_X`-module `Q` whose support lies in `|U|`,
the unit `Q ⟶ j_*j^*Q` of the adjunction of Stacks 03LU is a monomorphism.

Its kernel `N` has `j^*N = 0`: the restriction of the unit is split by the counit and `j^*` is
exact, `j` being flat.  So the support of `N` misses `|U|`, by the description of the support of
an étale pullback; it also lies in the support of `Q`, hence in `|U|`.  A module with empty
support is zero. -/
theorem mono_modulePullbackAdjunction_unit_app (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom)
    (Q : Modules.{u, u} B S hS X.1 X.2)
    (hQ : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj Q) ⊆
      Set.range (pointsMap B S hS U.1 j.hom)) :
    Mono ((modulePullbackAdjunction B S hS j).unit.app Q) := by
  have hje : IsEtale B S hS j.hom := isEtale_of_isOpenImmersion B S hS hj
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS j (isFlat_of_isEtale B S hS hje)
  have := (modulePullbackAdjunction B S hS j).isLeftAdjoint
  set adj := modulePullbackAdjunction B S hS j
  set η := adj.unit.app Q
  apply Preadditive.mono_of_isZero_kernel
  have hsplit : Mono ((modulePullback B S hS j).map η) :=
    mono_of_mono_fac (adj.left_triangle_components Q)
  have hZ : IsZero ((modulePullback B S hS j).obj (kernel η)) :=
    (isZero_kernel_of_mono ((modulePullback B S hS j).map η)).of_iso
      (PreservesKernel.iso (modulePullback B S hS j) η)
  have h1 := (supportOfSheaf_eq_empty_iff_isZero B S hS U _).2 hZ
  rw [supportOfSheaf_modulePullback_of_isEtale B S hS j hje] at h1
  have hmono : Mono ((SheafOfModules.toSheaf _).map (kernel.ι η)) :=
    preserves_mono_of_preservesLimit _ _
  have hsub := @supportOfSheaf_subset_of_mono B S hS X.1 X.2 _ _
    ((SheafOfModules.toSheaf _).map (kernel.ι η)) hmono
  refine isZero_of_supportOfSheaf_eq_empty B S hS X _ (Set.eq_empty_of_forall_notMem fun x hx => ?_)
  obtain ⟨y, rfl⟩ := hQ (hsub hx)
  exact Set.eq_empty_iff_forall_notMem.1 h1 y hx

end AlgebraicGeometry.Space

end
