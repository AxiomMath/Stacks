module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# Dualizing complexes over a field

A dualizing complex over a field is a shift of the field itself. Over a field every object
of the derived category splits into its cohomology, so a *simple* object of the derived
category is a one-dimensional module placed in a single degree. This file proves that
splitting and the consequence for simple objects; together with the simplicity of a
dualizing complex over a field, these give Stacks 0A7L, which identifies
`RHom_A(κ, ω)` with a shift of `κ` for a maximal ideal `m ⊆ A` with residue field
`κ = A/m` and a dualizing complex `ω` over a Noetherian ring `A`.

## Main results

* `Dualizing.iso_coproduct_homology_field` — over a field, every cohomologically bounded
  object of the derived category splits as the coproduct of its cohomology modules placed
  in their degrees. Each cohomology module is projective, so all the relevant `Ext` groups
  vanish and the canonical decomposition map is an isomorphism.
* `Dualizing.simple_bounded_iso_shift_field` — consequently a cohomologically bounded simple
  object of the derived category of a field is a shift of the one-dimensional module in
  degree zero: exactly one summand survives, and a simple module over a field has rank one.

## Implementation notes

The results are universe-polymorphic in the module size: the derived category is taken of
`ModuleCat.{max v u} k` for a field `k : Type u`, which is the size at which the dualizing
machinery of `Dualizing.Complex` has enough injectives.

## References

* [Stacks Project, Tag 0A7L](https://stacks.math.columbia.edu/tag/0A7L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- The `n`-th cohomology module of `M`, placed in degree `n`. -/
private noncomputable abbrev homologySummand {k : Type u} [Field k]
    (M : DerivedCategory (ModuleCat.{max v u} k)) (n : ℤ) :
    DerivedCategory (ModuleCat.{max v u} k) :=
  (DerivedCategory.singleFunctor (ModuleCat.{max v u} k) n).obj
    ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) n).obj M)

/-- Over a field, a cohomologically bounded object of the derived category is the coproduct
of its cohomology modules placed in their respective degrees. -/
theorem iso_coproduct_homology_field
    {k : Type u} [Field k]
    (M : DerivedCategory (ModuleCat.{max v u} k)) (a b : ℤ)
    [M.IsGE a] [M.IsLE b] :
    Nonempty (M ≅ ∐ fun n : Set.Icc a b =>
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} k) n.1).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) n.1).obj M)) := by
  classical
  obtain ⟨j⟩ :=
    DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_eq_zero
      M a b (fun i _ p _ hp x => by
        have : Projective
            ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj M) :=
          inferInstance
        exact x.eq_zero_of_hasProjectiveDimensionLT 1 (by omega))
  let q : (Finset.Icc a b : Finset ℤ) ≃ Set.Icc a b :=
    { toFun := fun i => ⟨i, Finset.mem_Icc.mp i.property⟩
      invFun := fun i => ⟨i, Finset.mem_Icc.mpr i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let G := fun n : Set.Icc a b => homologySummand M n.1
  exact ⟨j ≪≫ biproduct.whiskerEquiv (g := G) q (fun _ => Iso.refl _) ≪≫
    biproduct.isoCoproduct G⟩

/-- Over a field, a cohomologically bounded simple object of the derived category is a shift
of the one-dimensional module placed in degree zero. -/
theorem simple_bounded_iso_shift_field
    {k : Type u} [Field k]
    (M : DerivedCategory (ModuleCat.{max v u} k)) (a b : ℤ)
    [M.IsGE a] [M.IsLE b] [Simple M] :
    ∃ n : ℤ, Nonempty
      (M ≅ ((DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0).obj
        (ModuleCat.of k (ULift.{v} k)))⟦n⟧) := by
  classical
  obtain ⟨e⟩ := iso_coproduct_homology_field M a b
  let G := fun n : Set.Icc a b => homologySummand M n.1
  have : Simple (∐ G) := Simple.of_iso e.symm
  obtain ⟨n, hn⟩ : ∃ n, Sigma.ι G n ≠ 0 := by
    by_contra! h
    exact Simple.not_isZero (∐ G)
      ((IsZero.iff_id_eq_zero _).mpr (Sigma.hom_ext _ _ fun n => by simp [h]))
  have : IsSplitMono (Sigma.ι G n) := IsSplitMono.mk'
    ⟨Sigma.desc (Pi.single n (𝟙 (G n))), by simp⟩
  have : IsIso (Sigma.ι G n) := isIso_of_mono_of_nonzero hn
  let j : M ≅ G n := e ≪≫ (asIso (Sigma.ι G n)).symm
  have : Simple (G n) := Simple.of_iso j.symm
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) n.1).obj M
  let F := DerivedCategory.singleFunctor (ModuleCat.{max v u} k) n.1
  have : F.PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    have hk : f.hom.ker = ⊥ := LinearMap.ker_eq_bot.mpr
      ((ModuleCat.mono_iff_injective f).mp hf)
    have : IsSplitMono f := IsSplitMono.mk'
      ⟨ModuleCat.ofHom f.hom.leftInverse,
        ModuleCat.hom_ext (LinearMap.leftInverse_comp_of_inj hk)⟩
    infer_instance
  have : Simple H := F.simple_of_simple_obj H
  have hrank : Module.finrank k H = 1 :=
    isSimpleModule_iff_finrank_eq_one.mp inferInstance
  have hfin : Module.finrank k (ULift.{v} k) = 1 := by simp
  let unitM : ModuleCat.{max v u} k := ModuleCat.of k (ULift.{v} k)
  let h : H ≅ unitM :=
    (LinearEquiv.ofFinrankEq H (ULift.{v} k) (hrank.trans hfin.symm)).toModuleIso
  let shiftIso :=
    ((DerivedCategory.singleFunctors (ModuleCat.{max v u} k)).shiftIso
      (-n.1) n.1 0 (by simp)).app unitM
  exact ⟨-n.1, ⟨j ≪≫ F.mapIso h ≪≫ shiftIso.symm⟩⟩

end Dualizing

end
