module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportShortExactMonoEpi
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing

/-!
# `H²_c(X_k̄, -)` is right exact on a curve

Let `X` be a scheme of dimension at most one over a finite field `k`, with a compactification
`j`, and let `k̄` be an algebraically closed extension of `k`. For sheaves of `ℤ/m`-modules on
`X_étale`, `H³_c(X_k̄, -) = 0`
(`isZero_compactSupportFrobeniusCohomologyGroup_single_of_topologicalKrullDim_le`), so the long
exact sequence of `Hⁱ_c(X_k̄, -)` makes the top degree `H²_c(X_k̄, -)` a right exact functor: an
exact sequence `F₁ → F₀ → G → 0` gives an exact sequence
`H²_c(X_k̄, F₁) → H²_c(X_k̄, F₀) → H²_c(X_k̄, G) → 0`.

This is the right exactness used in the proof of [Stacks, Tag 03VK]: `H²_c` of a lisse sheaf is
computed from a presentation of its monodromy module.

## Main results

* `Stacks.EtaleCohomology.surjective_compactSupportSheafCohomology_two_map_of_epi`:
  `H²_c(X_k̄, -)` preserves epimorphisms.
* `Stacks.EtaleCohomology.exact_compactSupportSheafCohomology_two_map`: it carries an exact
  sequence `F₁ → F₀ → G → 0` to an exact sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
  (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosed kbar] (m : ℕ) [NeZero m]

omit [Fintype k] in
/-- `H³_c(X_k̄, G) = 0` for a sheaf of `ℤ/m`-modules on a scheme of dimension at most one. -/
theorem isZero_compactSupportSheafCohomology_three (hdim : topologicalKrullDim X ≤ 1) [Finite k]
    (G : EtaleModules.{u, 0} (ZMod m) X) :
    IsZero ((compactSupportSheafCohomology (ZMod m) f j kbar 3).obj G) :=
  isZero_compactSupportFrobeniusCohomologyGroup_single_of_topologicalKrullDim_le f j kbar m G 1
    (by exact_mod_cast hdim) 3 (by norm_num)

omit [NeZero m] in
/-- The short exact sequence `0 → ker b → F → G → 0` of an epimorphism, in degree zero. -/
private theorem shortExact_single_kernel {F G : EtaleModules.{u, 0} (ZMod m) X} (b : F ⟶ G)
    [Epi b] :
    ((ShortComplex.mk (kernel.ι b) b (kernel.condition b)).map
      (HomologicalComplex.single (EtaleModules.{u, 0} (ZMod m) X)
        (ComplexShape.up ℤ) 0)).ShortExact :=
  (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel b) inferInstance
    inferInstance).map_of_exact _

/-- An object placed in degree zero is a bounded below complex. -/
private theorem plus_single_obj {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    (F : C) : CochainComplex.plus C ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj F) :=
  ⟨0, inferInstance⟩

omit [Fintype k] in
/-- **`H²_c(X_k̄, -)` preserves epimorphisms** on a scheme of dimension at most one: the next
term `H³_c(X_k̄, ker b)` of the long exact sequence vanishes. -/
theorem surjective_compactSupportSheafCohomology_two_map_of_epi (hdim : topologicalKrullDim X ≤ 1)
    [Finite k] {F G : EtaleModules.{u, 0} (ZMod m) X} (b : F ⟶ G) [Epi b] :
    Function.Surjective ((compactSupportSheafCohomology (ZMod m) f j kbar 2).map b).hom := by
  have hS := shortExact_single_kernel m b
  have h := epi_homology_compactSupportFrobeniusFunctor_map_g (ZMod m) f j kbar hS
    (plus_single_obj (kernel b))
    (plus_single_obj F)
    (plus_single_obj G) 2 3 (by norm_num)
    (isZero_compactSupportSheafCohomology_three f j kbar m hdim (kernel b))
  exact (ModuleCat.epi_iff_surjective _).1 h

omit [Fintype k] in
/-- **Right exactness of `H²_c(X_k̄, -)`** on a scheme of dimension at most one: an exact
sequence `F₁ → F₀ → G → 0` of sheaves of `ℤ/m`-modules gives an exact sequence
`H²_c(X_k̄, F₁) → H²_c(X_k̄, F₀) → H²_c(X_k̄, G)`, whose last map is onto
(`surjective_compactSupportSheafCohomology_two_map_of_epi`). -/
theorem exact_compactSupportSheafCohomology_two_map (hdim : topologicalKrullDim X ≤ 1) [Finite k]
    {F₁ F₀ G : EtaleModules.{u, 0} (ZMod m) X} (a : F₁ ⟶ F₀) (b : F₀ ⟶ G) (w : a ≫ b = 0)
    (hab : (ShortComplex.mk a b w).Exact) [Epi b] :
    Function.Exact ((compactSupportSheafCohomology (ZMod m) f j kbar 2).map a).hom
      ((compactSupportSheafCohomology (ZMod m) f j kbar 2).map b).hom := by
  have := Fintype.ofFinite k
  set H := compactSupportSheafCohomology (ZMod m) f j kbar 2
  have hS := shortExact_single_kernel m b
  have hex := exact_homology_compactSupportFrobeniusFunctor_map (ZMod m) f j kbar hS
    (plus_single_obj (kernel b))
    (plus_single_obj F₀)
    (plus_single_obj G) 2
  -- `a` factors through `ker b` by an epimorphism
  let a' : F₁ ⟶ kernel b := kernel.lift b a w
  have ha' : a' ≫ kernel.ι b = a := kernel.lift_ι b a w
  have : Epi a' := by rwa [ShortComplex.exact_iff_epi_kernel_lift] at hab
  have hsurj := surjective_compactSupportSheafCohomology_two_map_of_epi f j kbar m hdim a'
  have hfac (t) : (H.map a).hom t = (H.map (kernel.ι b)).hom ((H.map a').hom t) := by
    rw [← ha', H.map_comp]
    rfl
  refine fun y => ⟨fun hy => ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := (hex y).1 hy
    obtain ⟨t, rfl⟩ := hsurj z
    exact ⟨t, hfac t⟩
  · rintro ⟨t, rfl⟩
    rw [hfac t]
    exact (hex _).2 ⟨_, rfl⟩

end Stacks.EtaleCohomology

end
