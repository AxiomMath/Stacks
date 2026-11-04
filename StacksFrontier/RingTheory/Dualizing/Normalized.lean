module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# Normalized dualizing complexes

A dualizing complex over a Noetherian local ring is *normalized* when its derived Hom from
the residue field is the residue field itself, placed in degree zero. Every dualizing complex
over a Noetherian local ring is a shift of a normalized one, so the normalization pins down
the one shift in which the comparison with the residue field is an honest module.

## Main definitions

* `Dualizing.IsNormalizedDualizingComplex` — a dualizing complex is normalized when its
  derived Hom from the residue field is isomorphic to the residue field in degree zero.

## Main results

* `Dualizing.residueFieldMap_finite` — a finite local homomorphism induces a finite
  homomorphism of residue fields.
* `Dualizing.exists_linearMap_retraction_of_finite_extension` — a finite field extension
  splits as a module over any base acting through the smaller field.
* `Dualizing.residueSingle_id_ne_zero` — the identity of the residue field in degree zero is
  nonzero in the derived category.
* `Dualizing.residueSingle_shift_hom_eq_zero` — over a field, there is no nonzero morphism
  from a module in degree zero to a nonzero shift of itself: positive shifts vanish because
  every module over a field is projective, and negative shifts because the two objects sit in
  disjoint parts of the standard t-structure.

## Implementation notes

The residue field on the right of the normalization is lifted to the module universe used by
the derived category, as `Dualizing.derivedHom` requires.
`Dualizing.derivedHom (IsLocalRing.residue A)` is the source's `RHom_A(κ, -)`.

## References

* [Stacks Project, Tag 0AX1](https://stacks.math.columbia.edu/tag/0AX1)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- A dualizing complex over a Noetherian local ring is normalized if its derived Hom
from the residue field is isomorphic to the residue field concentrated in degree zero. -/
def IsNormalizedDualizingComplex {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (K : DerivedCategory (ModuleCat.{max v u} A)) : Prop :=
  IsDualizingComplex K ∧
    Nonempty
      ((derivedHom.{u, v} (IsLocalRing.residue A)).obj K ≅
        (DerivedCategory.singleFunctor
          (ModuleCat.{max v u} (IsLocalRing.ResidueField A)) 0).obj
            ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField A)).obj
              (ModuleCat.of (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A))))

/-- A finite local homomorphism of local rings induces a finite homomorphism of residue
fields. -/
theorem residueFieldMap_finite
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : f.Finite) :
    (IsLocalRing.ResidueField.map f).Finite := by
  apply RingHom.Finite.of_comp_finite
    (f := IsLocalRing.residue A) (g := IsLocalRing.ResidueField.map f)
  rw [IsLocalRing.ResidueField.map_comp_residue]
  exact (RingHom.Finite.of_surjective _ IsLocalRing.residue_surjective).comp hf

/-- A finite extension of fields splits, as modules over any base ring acting through the
smaller field. -/
theorem exists_linearMap_retraction_of_finite_extension
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L] :
    ∃ (r : L →ₗ[A] K) (i : K →ₗ[A] L), r.comp i = LinearMap.id := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  refine ⟨r.restrictScalars A, (Algebra.linearMap K L).restrictScalars A, ?_⟩
  ext x
  exact LinearMap.congr_fun hr x

/-- The identity of a field, placed in degree zero, is a nonzero endomorphism in the derived
category. -/
theorem residueSingle_id_ne_zero (k : Type u) [Field k] :
    (𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0).obj
      ((ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k))) :
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0).obj
          ((ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k)) ⟶
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0).obj
          ((ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k))) ≠ 0 := by
  let M := (ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k)
  have hmod : (𝟙 M : M ⟶ M) ≠ 0 := by
    intro h
    have hh := congrArg (fun q => q.hom (ULift.up (1 : k))) h
    have hh' := congrArg ULift.down hh
    change (1 : k) = 0 at hh'
    exact one_ne_zero hh'
  intro h
  let F := DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0
  apply hmod
  apply F.map_injective
  simpa [M, F] using h

/-- Over a field, every morphism from a module in degree zero to a nonzero shift of itself
vanishes. -/
theorem residueSingle_shift_hom_eq_zero (k : Type u) [Field k]
    (n : ℤ) (hn : n ≠ 0) :
    ∀ φ : ((DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0).obj
      ((ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k))) ⟶
        (((DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0).obj
          ((ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k)))⟦n⟧), φ = 0 := by
  let M := (ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k)
  let S := (DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0).obj M
  intro φ
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hLE : S.IsLE 0 := inferInstance
    have hGE : (S⟦n⟧).IsGE (-n) :=
      DerivedCategory.TStructure.t.isGE_shift _ 0 n (-n) (by omega)
    exact DerivedCategory.TStructure.t.zero φ 0 (-n) (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m + 1 : ℤ) := ⟨(n - 1).toNat, by omega⟩
    have := HasExt.standard (ModuleCat.{max v u} k)
    let e : Abelian.Ext M M (m + 1) :=
      (Abelian.Ext.homLinearEquiv (R := k) (X := M) (Y := M)).symm φ
    simpa [e] using congrArg (Abelian.Ext.homLinearEquiv (R := k) (X := M) (Y := M))
      (Abelian.Ext.eq_zero_of_projective e)

end Dualizing

end
