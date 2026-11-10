module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKind
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationExtensions
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalenceExtensions

/-!
# Additions to `FibredSiteLocalizationSiteKind`

For a category `𝒳` fibred in groupoids over `(Sch/S)_fppf`, with objects and morphisms in
arbitrary universes, the localization of the inherited `τ`-topology of `𝒳` at an object `x` is
equivalent, as a ringed site, to `(Sch/U)_τ` for the base scheme `U` of `x`; quasi-coherence of
sheaves of modules is preserved across this equivalence.

## Main definitions

* `localizedTopologyKind'`: The localization at `x` of the inherited `τ`-topology of `𝒳`.
* `localizationModulesEquivalenceKind'`: The equivalence of categories of sheaves of modules
  induced by the equivalence of ringed sites.
* `objectInverseImageKind'`: The inverse image `x^*𝓕` of a sheaf of modules at an object `x`.

## Main results

* `isQuasicoherentOnSite_localization_iff_kind'`: A sheaf of modules on `𝒳_τ/x` is
  quasi-coherent exactly when its transport to `(Sch/U)_τ` is.
* `isQuasicoherentOnSite_iff_forall_objectInverseImageKind'`: The localization criterion for
  quasi-coherence on `𝒳_τ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-! ### The localization at an arbitrary topology, at an arbitrary pair of universes for `𝒳`

The primed declarations below are the ones above for `𝒳 : Type v`, `Category.{w} 𝒳` with `v`
and `w` independent of the universe `u` of the schemes, built on the primed declarations of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization`.  The
equivalence of ringed sites is universe-generic, and so is quasi-coherence across it: it rests on
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff_ofUniv`, which has four independent
universe parameters for its two sites, so matching `BigFppfOver B U hU` (objects `Type (u + 1)`,
morphisms `Type u`) with `Over x` (objects `Type (max v w)`, morphisms `Type w`) imposes no
constraint. -/

universe v w

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The localization at an object `x` of the inherited `τ`-topology of `𝒳`. -/
public abbrev localizedTopologyKind'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    (τ : SiteKind) (x : 𝒳) : GrothendieckTopology (Over x) :=
  (BigFppfOver.associatedTopology B S hS p τ).over x

/-- **The equivalence of sites `𝒳_τ/x ≌ (Sch/U)_τ`.**  A sieve of `𝒳_τ/x` is covering exactly
when its image is: on the `CategoryTheory.Over.post` factor this is the correspondence of
coverings of Stacks 0CN0, whose hypothesis is
`CategoryTheory.Functor.isInheritedTopology_inheritedTopology`, and on the iterated-slice factor
it is Mathlib's dense-subsite instance for `CategoryTheory.Over.iteratedSliceEquiv`. -/
public instance isDenseSubsite_localizationEquivalence_functor_kind' (τ : SiteKind) (x : 𝒳) :
    (localizationEquivalence' B S hS p hp x).functor.IsDenseSubsite
      (localizedTopologyKind' B S hS p τ x)
      (BigFppfOver.baseOverTopology B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x) τ) where
  functorPushforward_mem_iff {Y T} := by
    have hd : (Over.iteratedSliceForward (p.obj x)).IsDenseSubsite
        ((BigFppfOver.baseOverTopology B S hS τ).over (p.obj x))
        (BigFppfOver.baseOverTopology B ((BigFppfOver.toScheme B S hS).obj (p.obj x))
          (p.obj x).left.2 τ) :=
      inferInstanceAs ((Over.iteratedSliceEquiv (p.obj x)).functor.IsDenseSubsite
        (((B.baseTopology τ).over (B.obj hS)).over (p.obj x))
        ((B.baseTopology τ).over (p.obj x).left))
    have : p.IsFibered := hp.isFibered
    have h₁ := Functor.IsInheritedTopology.mem_over_iff_functorPushforward hp
      (Functor.isInheritedTopology_inheritedTopology p
        (BigFppfOver.baseOverTopology B S hS τ)) Y T
    have h₂ := Functor.functorPushforward_mem_iff
      (J := (BigFppfOver.baseOverTopology B S hS τ).over (p.obj x))
      (K := BigFppfOver.baseOverTopology B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x) τ)
      (G := Over.iteratedSliceForward (p.obj x))
      (S := Sieve.functorPushforward (Over.post (X := x) p) T)
    rw [show (localizationEquivalence' B S hS p hp x).functor =
      Over.post (X := x) p ⋙ Over.iteratedSliceForward (p.obj x) from rfl,
      Sieve.functorPushforward_comp]
    exact h₂.trans h₁.symm

/-- The inverse of the equivalence of sites `𝒳_τ/x ≌ (Sch/U)_τ` is a dense subsite inclusion
too, which is the form `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff_ofUniv`
consumes. -/
public instance isDenseSubsite_localizationEquivalence_inverse_kind' (τ : SiteKind) (x : 𝒳) :
    (localizationEquivalence' B S hS p hp x).inverse.IsDenseSubsite
      (BigFppfOver.baseOverTopology B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x) τ)
      (localizedTopologyKind' B S hS p τ x) :=
  letI : (localizationEquivalence' B S hS p hp x).symm.inverse.IsDenseSubsite
      (localizedTopologyKind' B S hS p τ x)
      (BigFppfOver.baseOverTopology B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x) τ) :=
    isDenseSubsite_localizationEquivalence_functor_kind' B S hS p hp τ x
  inferInstanceAs ((localizationEquivalence' B S hS p hp x).symm.functor.IsDenseSubsite _ _)

/-- **The ringed half of the equivalence `(𝒳_τ/x, 𝒪_𝒳|) ≌ ((Sch/U)_τ, 𝒪)`.**  The structure
sheaf of the associated `τ`-site of `𝒳`, restricted to `𝒳/x`, is the transport along
`AlgebraicGeometry.FibredSite.localizationEquivalence'` of the structure sheaf of the big
`τ`-site of the scheme `x` lies over — on the nose, because the structure sheaf of `𝒳` is the
restriction along `p` of the structure sheaf of `(Sch/S)_τ` and because
`CategoryTheory.Over.iteratedSliceForward_forget` is an equality of functors. -/
public theorem reindexRing_localizationEquivalence_kind' (τ : SiteKind) (x : 𝒳) :
    Stacks.SheafOfModules.reindexRing (localizedTopologyKind' B S hS p τ x)
        (localizationEquivalence' B S hS p hp x)
        (baseRingStructureSheaf B (baseScheme' B S hS p x)
          (contains_baseScheme' B S hS p x) τ) =
      (ringStructureSheafCore B S hS p hp τ).over x := rfl

/-- The equivalence of the two categories of sheaves of modules induced by the equivalence of
ringed sites `(𝒳_τ/x, 𝒪_𝒳|) ≌ ((Sch/U)_τ, 𝒪)`. -/
public noncomputable def localizationModulesEquivalenceKind' (τ : SiteKind) (x : 𝒳) :
    SheafOfModules.{u} (baseRingStructureSheaf B (baseScheme' B S hS p x)
        (contains_baseScheme' B S hS p x) τ) ≌
      SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp τ).over x) :=
  Stacks.SheafOfModules.reindexEquivalence (localizationEquivalence' B S hS p hp x)
    (baseRingStructureSheaf B (baseScheme' B S hS p x) (contains_baseScheme' B S hS p x) τ)

/-- **The inverse image `x^*𝓕` at an object `x`, for the topology `τ`.**  A sheaf of modules on
the associated `τ`-site of `𝒳` restricts to `𝒳_τ/x`, and that site with its restricted structure
sheaf *is* the big `τ`-site of the scheme `U = p(x)`; this is the resulting sheaf of modules on
`(Sch/U)_τ`. -/
public noncomputable abbrev objectInverseImageKind' (τ : SiteKind) (x : 𝒳)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) :
    SheafOfModules.{u} (baseRingStructureSheaf B (baseScheme' B S hS p x)
      (contains_baseScheme' B S hS p x) τ) :=
  (localizationModulesEquivalenceKind' B S hS p hp τ x).inverse.obj (M.over x)

/-! ### Quasi-coherence across the equivalence, at the same arbitrary pair of universes

The binder does not narrow.  Quasi-coherence is carried across an equivalence of ringed sites by
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff_ofUniv`
(`StacksFrontier/AlgebraicGeometry/Topologies/QuasicoherentSiteEquivalence.lean`), whose two sites
live in independent universes of objects and of morphisms, so matching `BigFppfOver B U hU`
(objects `Type (u + 1)`, morphisms `Type u`) with `Over x` (objects `Type (max v w)`, morphisms
`Type w`) costs nothing.  The index type of the covering family of `𝒳` that the sufficiency
direction uses is `Type v`, which `CategoryTheory.ULift` supplies. -/

/-- **Stacks 03DM at clause (6), for the localization of `𝒳_τ`**: quasi-coherence of a sheaf of
modules on `𝒳_τ/x` is quasi-coherence of the corresponding sheaf of modules on `(Sch/U)_τ`. -/
public theorem isQuasicoherentOnSite_over_eq_inverseImage_kind' (τ : SiteKind) (x : 𝒳) :
    SheafOfModules.isQuasicoherentOnSite.{max v w, w, u, u}
        ((ringStructureSheafCore B S hS p hp τ).over x) =
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (baseRingStructureSheaf B (baseScheme' B S hS p x)
            (contains_baseScheme' B S hS p x) τ)).inverseImage
        (localizationModulesEquivalenceKind' B S hS p hp τ x).inverse := by
  ext M
  change M.IsQuasicoherentOnSite ↔
    ((localizationModulesEquivalenceKind' B S hS p hp τ x).inverse.obj M).IsQuasicoherentOnSite
  rw [← Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff_ofUniv
    (J' := localizedTopologyKind' B S hS p τ x) (localizationEquivalence' B S hS p hp x)
    (baseRingStructureSheaf B (baseScheme' B S hS p x) (contains_baseScheme' B S hS p x) τ)
    ((localizationModulesEquivalenceKind' B S hS p hp τ x).inverse.obj M)]
  exact ObjectProperty.prop_iff_of_iso _
    ((localizationModulesEquivalenceKind' B S hS p hp τ x).counitIso.app M).symm

/-- **Stacks 03DM at clause (6), read at a single module**: a sheaf of modules on `𝒳_τ/x` is
quasi-coherent exactly when the corresponding sheaf of modules on `(Sch/U)_τ` is. -/
public theorem isQuasicoherentOnSite_localization_iff_kind' (τ : SiteKind) (x : 𝒳)
    (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp τ).over x)) :
    M.IsQuasicoherentOnSite ↔
      ((localizationModulesEquivalenceKind' B S hS p hp τ x).inverse.obj
        M).IsQuasicoherentOnSite :=
  Iff.of_eq (congrFun (isQuasicoherentOnSite_over_eq_inverseImage_kind' B S hS p hp τ x) M)

/-- **The localization criterion for quasi-coherence on `𝒳_τ`.**  A sheaf of modules on the
associated `τ`-site of a category fibred in groupoids is quasi-coherent if and only if its
inverse image `x^*𝓕` is a quasi-coherent sheaf on the big `τ`-site `(Sch/U)_τ` of the scheme
`U = p(x)`, for every object `x` of `𝒳`.

Necessity is stability of quasi-coherence under restriction to a slice site, transported along
the equivalence of ringed sites `𝒳_τ/x ≌ (Sch/U)_τ`.  Sufficiency is Stacks 03DN for the family
of all objects of `𝒳`, which covers the final object: quasi-coherence is a local and intrinsic
property, so no further input is needed.

At `τ = .fppf` this is the 06WI statement
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImage'`. -/
public theorem isQuasicoherentOnSite_iff_forall_objectInverseImageKind' (τ : SiteKind)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) :
    M.IsQuasicoherentOnSite ↔
      ∀ x : 𝒳, (objectInverseImageKind' B S hS p hp τ x M).IsQuasicoherentOnSite := by
  refine ⟨fun hM x => (isQuasicoherentOnSite_localization_iff_kind' B S hS p hp τ x
      (M.over x)).1 (Stacks.SheafOfModules.isQuasicoherentOnSite_over M hM x), fun h => ?_⟩
  rw [Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite M]
  exact ⟨ULift.{v} 𝒳, fun i => i.down, Stacks.SheafOfModules.coversTop_ulift_self _,
    fun i => (isQuasicoherentOnSite_localization_iff_kind' B S hS p hp τ i.down
      (M.over i.down)).2 (h i.down)⟩

end

end AlgebraicGeometry.FibredSite

end
