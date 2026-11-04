module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Colimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Localization
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalenceExtensions

/-!
# The localization of a fibred site at an object, for arbitrary universes of `𝒳`

For a category `p : 𝒳 ⥤ (Sch/S)_fppf` fibred in groupoids with `𝒳 : Type v` and
`Category.{w} 𝒳`, this file states the localization statements of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization` (which takes
`𝒳 : Type (u + 1)`, `Category.{u} 𝒳`) at independent universes `v` and `w`: the equivalence of
sites `𝒳_fppf/x ≌ (Sch/U)_fppf` of Stacks 06WI with `U = p(x)`, the identification of the
structure sheaves on the two sides, and the transport of quasi-coherence along it. The
declarations are primed copies of the unprimed ones there, kept in their own module so that the
base file is unchanged.

## Main results

* `AlgebraicGeometry.FibredSite.localizationEquivalence'`: the equivalence `𝒳/x ≌ (Sch/U)_fppf`,
  and `AlgebraicGeometry.FibredSite.isDenseSubsite_localizationEquivalence_functor'`: it is an
  equivalence of sites.
* `AlgebraicGeometry.FibredSite.reindexRing_localizationEquivalence'`: the structure sheaves
  correspond on the nose.
* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImage'`:
  **Stacks 06WI**, a sheaf of modules is quasi-coherent if and only if every `x^*𝓕` is.
* `AlgebraicGeometry.FibredSite.isClosedUnderColimitsOfShape_over'`: closure of quasi-coherence
  under colimits on `𝒳/x`, from the same closure on `(Sch/U)_fppf`.

## References

* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

end CategoryTheory.Functor

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

end Stacks.SheafOfModules

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-! ### The localization at an arbitrary pair of universes for `𝒳`

The primed declarations below are the unprimed ones of `FibredSiteLocalization` for
`𝒳 : Type v`, `Category.{w} 𝒳` with `v` and `w` independent of the universe `u` of the schemes:
the equivalence of categories, the correspondence of coverings, the identification of the
structure sheaves and the quasi-coherence statements, Stacks 06WI among them, are all
universe-generic in `𝒳`.  Only the sheafification and colimit statements of that file need
`𝒳 : Type (u + 1)`, `Category.{u} 𝒳`, for a reason that has
nothing to do with the transport of quasi-coherence: sheafification of abelian presheaves on the
associated site is obtained from essential smallness of the site in the universe `u` of the
module sections. -/

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The localization of the associated fppf site of `𝒳` at an object `x`. -/
public abbrev localizedTopology'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    (x : 𝒳) : GrothendieckTopology (Over x) :=
  (BigFppfOver.associatedTopology B S hS p .fppf).over x

/-- The scheme `U = p(x)` an object `x` of `𝒳` lies over. -/
public abbrev baseScheme' (x : 𝒳) : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj (p.obj x)

/-- The scheme an object of `𝒳` lies over is one of the big fppf site. -/
public theorem contains_baseScheme' (x : 𝒳) : B.Contains (baseScheme' B S hS p x) :=
  (p.obj x).left.2

/-- **Stacks 06WI, the equivalence of categories `𝒳/x ≌ (Sch/U)_fppf`.**  It is the
localization of `p` at `x` (Stacks 0CN0) followed by the comparison of the iterated slice
`((Sch/S)_fppf)/U` with `(Sch/U)_fppf`, which is an equality of categories. -/
public noncomputable def localizationEquivalence' (x : 𝒳) :
    Over x ≌ BigFppfOver B (baseScheme' B S hS p x) (contains_baseScheme' B S hS p x) :=
  (hp.overPostEquivalence x).trans (Over.iteratedSliceEquiv (p.obj x))

/-- **Stacks 06WI, the equivalence of sites `𝒳_fppf/x ≌ (Sch/U)_fppf`.**  A sieve of `𝒳_fppf/x`
is covering exactly when its image is: on the `Over.post p` factor this is the correspondence of
coverings of Stacks 0CN0, whose hypothesis is `isInheritedTopology_inheritedTopology`, and on
the iterated-slice factor it is Mathlib's dense-subsite instance for
`CategoryTheory.Over.iteratedSliceEquiv`. -/
public instance isDenseSubsite_localizationEquivalence_functor' (x : 𝒳) :
    (localizationEquivalence' B S hS p hp x).functor.IsDenseSubsite
      (localizedTopology' B S hS p x)
      (BigFppfOver.topology B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x)) where
  functorPushforward_mem_iff {Y T} := by
    have hd : (Over.iteratedSliceForward (p.obj x)).IsDenseSubsite
        ((BigFppfOver.baseOverTopology B S hS .fppf).over (p.obj x))
        (BigFppfOver.topology B ((BigFppfOver.toScheme B S hS).obj (p.obj x))
          (p.obj x).left.2) :=
      inferInstanceAs ((Over.iteratedSliceEquiv (p.obj x)).functor.IsDenseSubsite
        ((B.topology.over (B.obj hS)).over (p.obj x)) (B.topology.over (p.obj x).left))
    have : p.IsFibered := hp.isFibered
    have h₁ := Functor.IsInheritedTopology.mem_over_iff_functorPushforward hp
      (Functor.isInheritedTopology_inheritedTopology p
        (BigFppfOver.baseOverTopology B S hS .fppf)) Y T
    have h₂ := Functor.functorPushforward_mem_iff
      (J := (BigFppfOver.baseOverTopology B S hS .fppf).over (p.obj x))
      (K := BigFppfOver.topology B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x))
      (G := Over.iteratedSliceForward (p.obj x))
      (S := Sieve.functorPushforward (Over.post (X := x) p) T)
    rw [show (localizationEquivalence' B S hS p hp x).functor =
      Over.post (X := x) p ⋙ Over.iteratedSliceForward (p.obj x) from rfl,
      Sieve.functorPushforward_comp]
    exact h₂.trans h₁.symm

/-- The inverse of the equivalence of sites of Stacks 06WI is a dense subsite inclusion too,
which is the form `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff_ofUniv` consumes. -/
public instance isDenseSubsite_localizationEquivalence_inverse' (x : 𝒳) :
    (localizationEquivalence' B S hS p hp x).inverse.IsDenseSubsite
      (BigFppfOver.topology B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x))
      (localizedTopology' B S hS p x) :=
  letI : (localizationEquivalence' B S hS p hp x).symm.inverse.IsDenseSubsite
      (localizedTopology' B S hS p x)
      (BigFppfOver.topology B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x)) :=
    isDenseSubsite_localizationEquivalence_functor' B S hS p hp x
  inferInstanceAs ((localizationEquivalence' B S hS p hp x).symm.functor.IsDenseSubsite _ _)

/-- **The ringed half of the equivalence `(𝒳/x, 𝒪_𝒳|) ≌ ((Sch/U)_fppf, 𝒪)`.**  The structure
sheaf of the associated fppf site of `𝒳`, restricted to `𝒳/x`, is the transport along
`AlgebraicGeometry.FibredSite.localizationEquivalence'` of the structure sheaf of the big fppf
site of the scheme `x` lies over — on the nose, because the structure sheaf of `𝒳` is the
restriction along `p` of the structure sheaf of `(Sch/S)_fppf` and because
`CategoryTheory.Over.iteratedSliceForward_forget` is an equality of functors. -/
public theorem reindexRing_localizationEquivalence' (x : 𝒳) :
    Stacks.SheafOfModules.reindexRing (localizedTopology' B S hS p x)
        (localizationEquivalence' B S hS p hp x)
        (BigFppfOver.structureSheaf B (baseScheme' B S hS p x)
          (contains_baseScheme' B S hS p x)) =
      (ringStructureSheafCore B S hS p hp .fppf).over x := rfl

end

/-! ### Quasi-coherence across the equivalence, at the same arbitrary pair of universes

The binder does not narrow.  Quasi-coherence is carried across an equivalence of ringed sites by
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff_ofUniv`
(`StacksFrontier/AlgebraicGeometry/Topologies/QuasicoherentSiteEquivalence.lean`), whose two sites
live in independent universes of objects and of morphisms, so matching `BigFppfOver B U hU`
(objects `Type (u + 1)`, morphisms `Type u`) with `Over x` (objects `Type (max v w)`, morphisms
`Type w`) costs nothing.  The index type of the covering family of `𝒳` that the sufficiency
direction of Stacks 06WI uses is `Type v`, which `CategoryTheory.ULift` supplies. -/

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The equivalence of the two categories of module sheaves induced by the equivalence of
ringed sites `(𝒳/x, 𝒪_𝒳|) ≌ ((Sch/U)_fppf, 𝒪)`. -/
public noncomputable def localizationModulesEquivalence' (x : 𝒳) :
    SheafOfModules.{u} (BigFppfOver.structureSheaf B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x)) ≌
      SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x) :=
  Stacks.SheafOfModules.reindexEquivalence (localizationEquivalence' B S hS p hp x)
    (BigFppfOver.structureSheaf B (baseScheme' B S hS p x) (contains_baseScheme' B S hS p x))

/-- **Stacks 03DM at clause (6), for the localization of Stacks 06WI**: quasi-coherence of a
module sheaf on `𝒳/x` is quasi-coherence of the corresponding module sheaf on
`(Sch/U)_fppf`. -/
public theorem isQuasicoherentOnSite_over_eq_inverseImage' (x : 𝒳) :
    SheafOfModules.isQuasicoherentOnSite.{max v w, w, u, u}
        ((ringStructureSheafCore B S hS p hp .fppf).over x) =
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (BigFppfOver.structureSheaf B (baseScheme' B S hS p x)
            (contains_baseScheme' B S hS p x))).inverseImage
        (localizationModulesEquivalence' B S hS p hp x).inverse := by
  ext M
  show M.IsQuasicoherentOnSite ↔
    ((localizationModulesEquivalence' B S hS p hp x).inverse.obj M).IsQuasicoherentOnSite
  rw [← Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff_ofUniv
    (J' := localizedTopology' B S hS p x) (localizationEquivalence' B S hS p hp x)
    (BigFppfOver.structureSheaf B (baseScheme' B S hS p x) (contains_baseScheme' B S hS p x))
    ((localizationModulesEquivalence' B S hS p hp x).inverse.obj M)]
  exact ((SheafOfModules.isQuasicoherentOnSite _).prop_iff_of_iso
    ((localizationModulesEquivalence' B S hS p hp x).counitIso.app M)).symm

/-- **The inverse image `x^*𝓕` at an object `x`.**  A sheaf of modules on the associated fppf
site of `𝒳` restricts to `𝒳_fppf/x`, and that site with its restricted structure sheaf *is* the
big fppf site of the scheme `U = p(x)`; this is the resulting sheaf of modules on
`(Sch/U)_fppf`. -/
public noncomputable abbrev objectInverseImage' (x : 𝒳)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) :
    SheafOfModules.{u} (BigFppfOver.structureSheaf B (baseScheme' B S hS p x)
      (contains_baseScheme' B S hS p x)) :=
  (localizationModulesEquivalence' B S hS p hp x).inverse.obj (M.over x)

/-- **Stacks 03DM at clause (6), read at a single module**: a sheaf of modules on `𝒳_fppf/x` is
quasi-coherent exactly when the corresponding sheaf of modules on `(Sch/U)_fppf` is. -/
public theorem isQuasicoherentOnSite_localization_iff' (x : 𝒳)
    (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x)) :
    M.IsQuasicoherentOnSite ↔
      ((localizationModulesEquivalence' B S hS p hp x).inverse.obj M).IsQuasicoherentOnSite :=
  Iff.of_eq (congrFun (isQuasicoherentOnSite_over_eq_inverseImage' B S hS p hp x) M)

/-- **Stacks 06WI.**  A sheaf of modules on the associated fppf site of a category fibred in
groupoids is quasi-coherent if and only if its inverse image `x^*𝓕` is a quasi-coherent sheaf on
the big fppf site `(Sch/U)_fppf` of the scheme `U = p(x)`, for every object `x` of `𝒳`.

Necessity is stability of quasi-coherence under restriction to a slice site, transported along
the equivalence of ringed sites `𝒳_fppf/x ≌ (Sch/U)_fppf`.  Sufficiency is Stacks 03DN for the
family of all objects of `𝒳`, which covers the final object: quasi-coherence is a local and
intrinsic property, so no further input is needed. -/
public theorem isQuasicoherentOnSite_iff_forall_objectInverseImage'
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) :
    M.IsQuasicoherentOnSite ↔
      ∀ x : 𝒳, (objectInverseImage' B S hS p hp x M).IsQuasicoherentOnSite := by
  refine ⟨fun hM x => (isQuasicoherentOnSite_localization_iff' B S hS p hp x (M.over x)).1
    (Stacks.SheafOfModules.isQuasicoherentOnSite_over M hM x), fun h => ?_⟩
  rw [Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite M]
  exact ⟨ULift.{v} 𝒳, fun i => i.down, Stacks.SheafOfModules.coversTop_ulift_self _,
    fun i => (isQuasicoherentOnSite_localization_iff' B S hS p hp i.down (M.over i.down)).2
      (h i.down)⟩

/-- Closure of quasi-coherence under colimits of shape `K` on the localization `𝒳/x`, from the
same closure on the big fppf site of the scheme `x` lies over.  This is the transport along the
equivalence of ringed sites of Stacks 06WI. -/
public theorem isClosedUnderColimitsOfShape_over' (x : 𝒳) (K : Type u) [Category.{u} K]
    (h : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (BigFppfOver.structureSheaf B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x))).IsClosedUnderColimitsOfShape K) :
    (SheafOfModules.isQuasicoherentOnSite.{max v w, w, u, u}
      ((ringStructureSheafCore B S hS p hp .fppf).over x)).IsClosedUnderColimitsOfShape K := by
  rw [isQuasicoherentOnSite_over_eq_inverseImage' B S hS p hp x]
  infer_instance

end

end AlgebraicGeometry.FibredSite

end
