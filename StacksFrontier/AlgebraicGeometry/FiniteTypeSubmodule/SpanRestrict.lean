module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.Affine

/-!
# Sections over a basic open are spanned by the restrictions of a saturating family

Let `N` be an `R`-module, `S ⊆ N` a subset, and `a ∈ R` an element such that a power of `a`
carries every element of `N` into the `R`-span of `S`. Then after localizing at any `f` for which
`a` becomes invertible, the whole localized module is spanned by the images of `S`.

Geometrically: if `M` is a quasi-coherent module on a scheme, `U` an affine open, and `S` a set
of sections of `M` over `U` such that some power of `a ∈ Γ(X, U)` carries every section over `U`
into the span of `S`, then over any basic open `D(g) ⊆ D(a)` every section of `M` is a
`Γ(X, D(g))`-combination of the restrictions of `S`.

This is the step of the affine paragraph of [Stacks Project, Tag 01PF] that turns the finitely
generated submodule `N' ⊆ N` produced by
`Stacks.AlgebraicGeometry.FiniteTypeSubmodule.exists_finite_basicOpen_cover_and_fg_submodule`
into the surjectivity statement the sheaf-level argument needs: the source's `N'_{a_i} = N_{a_i}`,
read over the basic opens of the cover rather than as an equality of localized submodules.

## Main results

* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.mem_span_image_of_forall_exists_pow_smul_mem`:
  the algebraic statement, for an arbitrary `IsLocalizedModule` presentation of the localization
  and with the invertibility of `a` as a hypothesis.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.isUnit_res_basicOpen_of_le`: a section is
  invertible on every basic open contained in its own.
* `mem_span_restrict_image_of_forall_exists_pow_smul_mem`, in the same namespace: the geometric
  statement over a basic open of an affine open.

## Implementation notes

The algebraic statement is phrased for an arbitrary `IsLocalizedModule (Submonoid.powers f) φ`
rather than for `LocalizedModule`, as the two lemmas of
`StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.Basic` are, so that
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ` meets it on the
nose and no transport between the sections of `M` over a basic open and a concrete localization
is needed.

The invertibility of `a` over `D(g)` is supplied by restricting the unit
`RingedSpace.isUnit_res_basicOpen` along `D(g) ≤ D(a)`; the composite of the two restriction maps
is the single restriction map because the homs of a lattice of opens are a subsingleton, which is
what `Subsingleton.elim` discharges.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u v

namespace Stacks.AlgebraicGeometry.FiniteTypeSubmodule

/-- If a power of `a` carries every element of `N` into the span of `S`, and `a` becomes
invertible in a localization of `R` away from `f`, then the localized module is spanned by the
images of `S`. -/
theorem mem_span_image_of_forall_exists_pow_smul_mem
    {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]
    (a f : R) (Rl : Type*) [CommRing Rl] [Algebra R Rl] [IsLocalization.Away f Rl]
    {Nl : Type*} [AddCommGroup Nl] [Module R Nl] [Module Rl Nl] [IsScalarTower R Rl Nl]
    (φ : N →ₗ[R] Nl) [IsLocalizedModule (Submonoid.powers f) φ]
    (ha : IsUnit (algebraMap R Rl a))
    {S : Set N} (hS : ∀ x : N, ∃ k : ℕ, a ^ k • x ∈ Submodule.span R S)
    (y : Nl) : y ∈ Submodule.span Rl (φ '' S) := by
  classical
  set p : Submodule Rl Nl := Submodule.span Rl (φ '' S) with hp
  have hmap : ∀ z : N, z ∈ Submodule.span R S → φ z ∈ p := by
    intro z hz
    have h1 : Submodule.span R S ≤ Submodule.comap φ (p.restrictScalars R) :=
      Submodule.span_le.2 fun w hw => Submodule.subset_span ⟨w, hw, rfl⟩
    exact h1 hz
  obtain ⟨⟨x, t⟩, ht⟩ := IsLocalizedModule.surj (Submonoid.powers f) φ y
  obtain ⟨k, hk⟩ := hS x
  have hφ : φ (a ^ k • x) ∈ p := hmap _ hk
  have hsmul : (algebraMap R Rl a) ^ k • ((t : R) • y) = φ (a ^ k • x) := by
    rw [map_smul]
    rw [Submonoid.smul_def] at ht
    rw [← ht, ← map_pow, algebraMap_smul, smul_smul]
  have hmem : ((t : R) • y) ∈ p :=
    (Submodule.smul_mem_iff_of_isUnit p (ha.pow k)).1 (hsmul ▸ hφ)
  rw [← algebraMap_smul Rl (t : R) y] at hmem
  exact (Submodule.smul_mem_iff_of_isUnit p (IsLocalization.map_units Rl t)).1 hmem

/-- A section is invertible on every basic open contained in its own basic open. -/
theorem isUnit_res_basicOpen_of_le {X : Scheme.{u}} {U : X.Opens} (a g : Γ(X, U))
    (hga : X.basicOpen g ≤ X.basicOpen a) :
    IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom a) := by
  have h1 := X.toRingedSpace.isUnit_res_basicOpen a
  have h0 : (homOfLE (X.basicOpen_le g)).op
      = (homOfLE (X.basicOpen_le a)).op ≫ (homOfLE hga).op := Subsingleton.elim _ _
  rw [h0, X.presheaf.map_comp, CommRingCat.comp_apply]
  exact h1.map (X.presheaf.map (homOfLE hga).op).hom

/-- **The saturation step of the affine paragraph of [Stacks Project, Tag 01PF].** If a power of
`a ∈ Γ(X, U)` carries every section of a quasi-coherent module `M` over an affine open `U` into
the span of a set `S` of such sections, then over a basic open `D(g) ⊆ D(a)` every section of `M`
lies in the `Γ(X, D(g))`-span of the restrictions of `S`. -/
theorem mem_span_restrict_image_of_forall_exists_pow_smul_mem
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (a g : Γ(X, U)) (hga : X.basicOpen g ≤ X.basicOpen a) (S : Set Γ(M, U))
    (hS : ∀ x : Γ(M, U), ∃ k : ℕ, a ^ k • x ∈ Submodule.span Γ(X, U) S)
    (y : Γ(M, X.basicOpen g)) :
    letI := moduleOfLE M (X.basicOpen_le g)
    y ∈ Submodule.span Γ(X, X.basicOpen g) (restrictₗ M (X.basicOpen_le g) '' S) := by
  let := algebraOfLE X (X.basicOpen_le g)
  let := moduleOfLE M (X.basicOpen_le g)
  have := isScalarTowerOfLE M (X.basicOpen_le g)
  have : IsLocalization.Away g Γ(X, X.basicOpen g) := hU.isLocalization_basicOpen g
  have : IsLocalizedModule (Submonoid.powers g) (restrictₗ M (X.basicOpen_le g)) :=
    isLocalizedModule_restrictₗ M hU g rfl (X.basicOpen_le g)
  exact mem_span_image_of_forall_exists_pow_smul_mem a g Γ(X, X.basicOpen g)
    (restrictₗ M (X.basicOpen_le g)) (isUnit_res_basicOpen_of_le a g hga) hS y

end Stacks.AlgebraicGeometry.FiniteTypeSubmodule

end
