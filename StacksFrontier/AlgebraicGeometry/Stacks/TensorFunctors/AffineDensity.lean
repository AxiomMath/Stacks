module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf

/-!
# Sheaves of modules on a fibred site are determined on the affine objects

Every object of the fppf site associated with a category fibred in groupoids over the big fppf
category of `S` is covered by objects lying over affine schemes
(`AlgebraicGeometry.FibredSite.exists_affine_ofArrows`).  Hence a morphism of presheaves of
modules which is injective (respectively surjective) on the sections over every affine object is
locally injective (respectively locally surjective), and a morphism of sheaves of modules which
is bijective on the sections over every affine object is an isomorphism.

## Main results

* `AlgebraicGeometry.FibredSite.isLocallyInjective_of_injective_affine` and
  `AlgebraicGeometry.FibredSite.isLocallySurjective_of_surjective_affine`.
* `AlgebraicGeometry.FibredSite.isIso_of_bijective_affine`: **a morphism of sheaves of modules
  which is bijective on the sections over every affine object is an isomorphism.**
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w m

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)

include hp in
/-- The sieve of arrows out of affine objects into an object of the fibred site is covering. -/
theorem affineArrows_mem (W : 𝒳) {T : Sieve W}
    (hT : ∀ {Y : 𝒳} (f : Y ⟶ W), IsAffineOver B S hS (p.obj Y) → T f) :
    T ∈ BigFppfOver.associatedTopology B S hS p .fppf W := by
  obtain ⟨I, y, φ, hy, hcov⟩ := exists_affine_ofArrows B S hS p hp W
  refine GrothendieckTopology.superset_covering _ ?_ hcov
  intro Z g hg
  rw [Sieve.mem_ofArrows_iff] at hg
  obtain ⟨j, a, rfl⟩ := hg
  exact T.downward_closed (hT (φ j) (hy j)) a

variable {R : Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) RingCat.{u}}

include hp in
/-- **A morphism of presheaves of modules injective over every affine object is locally
injective.** -/
theorem isLocallyInjective_of_injective_affine {M N : PresheafOfModules.{m} R.obj} (f : M ⟶ N)
    (hf : ∀ y : 𝒳, IsAffineOver B S hS (p.obj y) → Function.Injective (f.app (op y))) :
    PresheafOfModules.IsLocallyInjective (BigFppfOver.associatedTopology B S hS p .fppf) f where
  equalizerSieve_mem {X} a b h := affineArrows_mem hp X.unop (fun {Y} g hY => by
    have h' := congrArg (((PresheafOfModules.toPresheaf R.obj).obj N).map g.op) h
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply] at h'
    exact hf Y hY h')

include hp in
/-- **A morphism of presheaves of modules surjective over every affine object is locally
surjective.** -/
theorem isLocallySurjective_of_surjective_affine {M N : PresheafOfModules.{m} R.obj} (f : M ⟶ N)
    (hf : ∀ y : 𝒳, IsAffineOver B S hS (p.obj y) → Function.Surjective (f.app (op y))) :
    PresheafOfModules.IsLocallySurjective (BigFppfOver.associatedTopology B S hS p .fppf) f where
  imageSieve_mem {X} s := affineArrows_mem hp X (fun {Y} g hY => hf Y hY (N.map g.op s))

include hp in
/-- **A morphism of sheaves of modules which is bijective on the sections over every affine
object is an isomorphism.** -/
theorem isIso_of_bijective_affine {M N : SheafOfModules.{m} R} (f : M ⟶ N)
    (hf : ∀ y : 𝒳, IsAffineOver B S hS (p.obj y) → Function.Bijective (f.val.app (op y))) :
    IsIso f := by
  have := isLocallyInjective_of_injective_affine hp f.val fun y hy => (hf y hy).1
  have := isLocallySurjective_of_surjective_affine hp f.val fun y hy => (hf y hy).2
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective f

end AlgebraicGeometry.FibredSite
