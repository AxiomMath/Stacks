module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ContinuousModuleQuotientDescent

/-!
# Lisse sheaves on which the geometric fundamental group acts trivially

Let `U` be a connected scheme of a big étale site with a morphism `f : U ⟶ Spec k` to the
spectrum of a field, such that `π₁(U, x̄) → π₁(Spec k, f(x̄))` is surjective (for instance `U`
geometrically connected, Tag 0BTX). If `Q` is a finite `Λ`-module with a continuous action of
`π₁(U, x̄)` on which the kernel of that map (the geometric fundamental group) acts trivially, then
the lisse sheaf `ℱ_Q` on `U` is pulled back from `Spec k`: `ℱ_Q ≅ f⁻¹ ℱ_{Q₀}`, where `Q₀` is `Q`
with the descended action of `π₁(Spec k)`.

This is the first step in the computation of the Frobenius on `H²_c(U_k̄, ℱ_Q)` in the proof of
[Stacks, Tag 03VK]: the coinvariants `F''` of the level of `ℱ_ρ` form such a sheaf.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.specField`: `Spec k` as an object of the big étale site.
* `Stacks.EtaleCohomology.lisseBaseFieldModule`: the module `Q₀` over `π₁(Spec k)`.

## Main results

* `Stacks.EtaleCohomology.nonempty_etaleModuleInverseImage_lisseEtaleSheaf_baseField_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (k : Type u) [Field k] [Finite k]

include U in
/-- The spectrum of a finite field belongs to every big étale site that contains some scheme. -/
theorem contains_spec_finiteField : B.Contains (Spec (.of k)) :=
  Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit (.of k) U.2
    ((Cardinal.mk_le_aleph0 (α := k)).trans (U.1.aleph0_le_size.trans
      (Cardinal.self_le_power _ (Cardinal.one_le_aleph0))))

/-- `Spec k`, for a finite field `k`, as an object of the big étale site. -/
abbrev specField : B.Scheme :=
  B.obj (Spec (.of k)) (contains_spec_finiteField B U k)

/-- A morphism `U ⟶ Spec k` as a morphism of the big étale site. -/
abbrev specFieldHom (f : U.1 ⟶ Spec (.of k)) : U ⟶ specField B U k :=
  ObjectProperty.homMk f

end AlgebraicGeometry.BigEtaleSite

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] (k : Type u) [Field k]
  [Finite k] (f : U.1 ⟶ Spec (.of k)) (x : GeometricPoint U.1)
  (hs : Function.Surjective (etaleFundamentalGroupMap f x)) (Λ : Type) [CommRing Λ] [Finite Λ]
  (Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup U.1 x))
  (hQ : ∀ g, etaleFundamentalGroupMap f x g = 1 → Q.obj.obj.obj.ρ g = 1)

/-- **The module `Q₀` over `π₁(Spec k)`**: `Q`, with the action of `π₁(U, x̄)` descended along the
surjection `π₁(U, x̄) ↠ π₁(Spec k, f(x̄))`. -/
def lisseBaseFieldModule :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Spec (.of k)) (x.map f)) :=
  haveI := compactSpace_etaleFundamentalGroup U.1 x
  haveI := t2Space_etaleFundamentalGroup (Spec (.of k)) (x.map f)
  finiteTypeContinuousModuleDescent Λ (etaleFundamentalGroupMap f x) hs Q hQ

omit [Finite k] [Finite Λ] in
/-- The action of the image of `g` on `Q₀` is the action of `g` on `Q`. -/
theorem lisseBaseFieldModule_ρ_apply (g : EtaleFundamentalGroup U.1 x) (v : Q.obj.obj.obj.V) :
    ((lisseBaseFieldModule B U k f x hs Λ Q hQ).obj.obj.obj.ρ
        (etaleFundamentalGroupMap f x g)).asHom v =
      (Q.obj.obj.obj.ρ g).asHom v :=
  have := compactSpace_etaleFundamentalGroup U.1 x
  have := t2Space_etaleFundamentalGroup (Spec (.of k)) (x.map f)
  finiteTypeContinuousModuleDescentRepresentation_apply Λ (etaleFundamentalGroupMap f x) hs Q hQ g v

/-- **`ℱ_Q ≅ f⁻¹ ℱ_{Q₀}`**: a lisse sheaf on which the geometric fundamental group acts trivially
is pulled back from the base field (Tag 0DV6 along `f`). -/
theorem nonempty_etaleModuleInverseImage_lisseEtaleSheaf_baseField_iso :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ f).obj
        ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) Λ).obj
          (lisseBaseFieldModule B U k f x hs Λ Q hQ)) ≅
      (lisseEtaleSheaf B U x Λ).obj Q) := by
  have := compactSpace_etaleFundamentalGroup U.1 x
  have := t2Space_etaleFundamentalGroup (Spec (.of k)) (x.map f)
  obtain ⟨α⟩ := nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso B
    (BigEtaleSite.specFieldHom B U k f) x Λ (lisseBaseFieldModule B U k f x hs Λ Q hQ)
  exact ⟨α ≪≫ (lisseEtaleSheaf B U x Λ).mapIso
    (finiteTypeContinuousModuleDescentResIso Λ (etaleFundamentalGroupMap f x) hs Q hQ)⟩

end Stacks.EtaleCohomology

end
