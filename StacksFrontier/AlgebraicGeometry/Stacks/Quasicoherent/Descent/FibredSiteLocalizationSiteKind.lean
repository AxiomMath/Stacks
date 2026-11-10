module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization

/-!
# The localization of an associated site at an object, for each of the five topologies

`AlgebraicGeometry.FibredSite.localizationEquivalence` identifies the slice `𝒳/x` of a category
`𝒳` fibred in groupoids over the big fppf category of schemes over `S` with the big fppf category
`Sch/U` of the scheme `U = p(x)` that `x` lies over.  That identification is an equivalence of
*categories* and so does not mention a topology at all; the module
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization` turns it into
an equivalence of **ringed sites** at the inherited fppf topology alone.

This file does the same at an arbitrary `AlgebraicGeometry.SiteKind`: the inherited `τ`-topology
of `𝒳` localized at `x` corresponds to the localized `τ`-topology of the big site of `U`, and the
restricted structure sheaf of `𝒳` is, on the nose, the transported structure sheaf of
`(Sch/U)_τ`.  Quasi-coherence of a sheaf of modules on `𝒳_τ` is therefore quasi-coherence of its
inverse images `x^*𝓕` on `(Sch/U)_τ`, one object at a time.

## Main definitions

* `AlgebraicGeometry.FibredSite.localizedTopologyKind`: the inherited `τ`-topology of `𝒳`,
  localized at an object.
* `AlgebraicGeometry.FibredSite.localizationModulesEquivalenceKind`: the equivalence of the two
  categories of sheaves of modules induced by the equivalence of ringed sites.
* `AlgebraicGeometry.FibredSite.objectInverseImageKind`: the inverse image `x^*𝓕` of a sheaf of
  modules on `𝒳_τ`, read on `(Sch/U)_τ`.

## Main results

* `AlgebraicGeometry.FibredSite.isDenseSubsite_localizationEquivalence_functor_kind` and
  `AlgebraicGeometry.FibredSite.isDenseSubsite_localizationEquivalence_inverse_kind`: **the
  equivalence of sites `𝒳_τ/x ≌ (Sch/U)_τ`**.
* `AlgebraicGeometry.FibredSite.reindexRing_localizationEquivalence_kind`: **its ringed half** —
  the restricted structure sheaf of `𝒳_τ` is the transported structure sheaf of `(Sch/U)_τ`, an
  equality rather than an isomorphism.
* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_localization_iff_kind`: quasi-coherence of
  a sheaf of modules on `𝒳_τ/x` is quasi-coherence of the corresponding sheaf of modules on
  `(Sch/U)_τ`.
* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImageKind`: a sheaf
  of modules on `𝒳_τ` is quasi-coherent exactly when `x^*𝓕` is quasi-coherent on `(Sch/U)_τ` for
  every object `x` of `𝒳`.

## Implementation notes

Nothing here carries a `stacks` attribute.  The 06WI attribute sits on
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImage`, the statement
at the inherited fppf topology, which is the topology the source's lemma is about; the statements
below are the same assertions at the coarser inherited topologies and belong to no tag of their
own.

Every proof is the one at the inherited fppf topology with `AlgebraicGeometry.BigFppfSite.topology`
replaced by `AlgebraicGeometry.BigFppfSite.baseTopology τ`, and the `τ = .fppf` instances of the
statements below are definitionally the fppf statements.  Only the dense-subsite witnesses are
restated as instances; the fppf ones remain available and at `τ = .fppf` the two overlap, which
costs nothing because they have the same conclusion.

*What this is for, and what it does not do.*  The two inputs of Stacks 0EM8 that this library
does not have are quasi-coherence of a module read for a coarser inherited topology, and the
inherited fppf sheaf condition of a module quasi-coherent for a coarser one; both are stated in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalence`.  The source checks each
after restricting to `𝒳/x` and reading `𝒳_τ/x = (Sch/U)_τ`, and that reading at a general `τ` is
what is below.  It does **not** discharge either input, and what remains after it is not the
same for the two;
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalenceInputs` carries out the
reduction and says what each one then needs.  For quasi-coherence read for a coarser topology it
is the essential surjectivity of `𝓕 ↦ 𝓕^a` at the big fppf site, Descent, Proposition 03DX (1),
carried in this library as
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule` and nothing else
(`AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_of_surjective`); that hypothesis is
reduced to `AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum` and to
reformulations of that datum, its other former input
`AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural` being the theorem
`AlgebraicGeometry.BigFppfOver.localComparisonPseudonatural`.  For the inherited fppf sheaf
condition it is instead the local step of Descent, Proposition 03DX at a coarser `τ`, which this
library has at `τ = fppf` only.

## References

* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 0CN0](https://stacks.math.columbia.edu/tag/0CN0)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The localization at an object `x` of the inherited `τ`-topology of `𝒳`. -/
public abbrev localizedTopologyKind (τ : SiteKind) (x : 𝒳) : GrothendieckTopology (Over x) :=
  (BigFppfOver.associatedTopology B S hS p τ).over x

/-- **The equivalence of sites `𝒳_τ/x ≌ (Sch/U)_τ`.**  A sieve of `𝒳_τ/x` is covering exactly
when its image is: on the `CategoryTheory.Over.post` factor this is the correspondence of
coverings of Stacks 0CN0, whose hypothesis is
`CategoryTheory.Functor.isInheritedTopology_inheritedTopology`, and on the iterated-slice factor
it is Mathlib's dense-subsite instance for `CategoryTheory.Over.iteratedSliceEquiv`. -/
public instance isDenseSubsite_localizationEquivalence_functor_kind (τ : SiteKind) (x : 𝒳) :
    (localizationEquivalence B S hS p hp x).functor.IsDenseSubsite
      (localizedTopologyKind B S hS p τ x)
      (BigFppfOver.baseOverTopology B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x) τ) where
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
      (K := BigFppfOver.baseOverTopology B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x) τ)
      (G := Over.iteratedSliceForward (p.obj x))
      (S := Sieve.functorPushforward (Over.post (X := x) p) T)
    rw [show (localizationEquivalence B S hS p hp x).functor =
      Over.post (X := x) p ⋙ Over.iteratedSliceForward (p.obj x) from rfl,
      Sieve.functorPushforward_comp]
    exact h₂.trans h₁.symm

/-- The inverse of the equivalence of sites `𝒳_τ/x ≌ (Sch/U)_τ` is a dense subsite inclusion
too, which is the form `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` consumes. -/
public instance isDenseSubsite_localizationEquivalence_inverse_kind (τ : SiteKind) (x : 𝒳) :
    (localizationEquivalence B S hS p hp x).inverse.IsDenseSubsite
      (BigFppfOver.baseOverTopology B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x) τ)
      (localizedTopologyKind B S hS p τ x) :=
  letI : (localizationEquivalence B S hS p hp x).symm.inverse.IsDenseSubsite
      (localizedTopologyKind B S hS p τ x)
      (BigFppfOver.baseOverTopology B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x) τ) :=
    isDenseSubsite_localizationEquivalence_functor_kind B S hS p hp τ x
  inferInstanceAs ((localizationEquivalence B S hS p hp x).symm.functor.IsDenseSubsite _ _)

/-- **The ringed half of the equivalence `(𝒳_τ/x, 𝒪_𝒳|) ≌ ((Sch/U)_τ, 𝒪)`.**  The structure
sheaf of the associated `τ`-site of `𝒳`, restricted to `𝒳/x`, is the transport along
`AlgebraicGeometry.FibredSite.localizationEquivalence` of the structure sheaf of the big
`τ`-site of the scheme `x` lies over — on the nose, because the structure sheaf of `𝒳` is the
restriction along `p` of the structure sheaf of `(Sch/S)_τ` and because
`CategoryTheory.Over.iteratedSliceForward_forget` is an equality of functors. -/
public theorem reindexRing_localizationEquivalence_kind (τ : SiteKind) (x : 𝒳) :
    Stacks.SheafOfModules.reindexRing (localizedTopologyKind B S hS p τ x)
        (localizationEquivalence B S hS p hp x)
        (baseRingStructureSheaf B (baseScheme B S hS p x)
          (contains_baseScheme B S hS p x) τ) =
      (ringStructureSheafCore B S hS p hp τ).over x := rfl

/-- The equivalence of the two categories of sheaves of modules induced by the equivalence of
ringed sites `(𝒳_τ/x, 𝒪_𝒳|) ≌ ((Sch/U)_τ, 𝒪)`. -/
public noncomputable def localizationModulesEquivalenceKind (τ : SiteKind) (x : 𝒳) :
    SheafOfModules.{u} (baseRingStructureSheaf B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x) τ) ≌
      SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp τ).over x) :=
  Stacks.SheafOfModules.reindexEquivalence (localizationEquivalence B S hS p hp x)
    (baseRingStructureSheaf B (baseScheme B S hS p x) (contains_baseScheme B S hS p x) τ)

/-- **Stacks 03DM at clause (6), for the localization of `𝒳_τ`**: quasi-coherence of a sheaf of
modules on `𝒳_τ/x` is quasi-coherence of the corresponding sheaf of modules on `(Sch/U)_τ`. -/
public theorem isQuasicoherentOnSite_over_eq_inverseImage_kind (τ : SiteKind) (x : 𝒳) :
    SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((ringStructureSheafCore B S hS p hp τ).over x) =
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (baseRingStructureSheaf B (baseScheme B S hS p x)
            (contains_baseScheme B S hS p x) τ)).inverseImage
        (localizationModulesEquivalenceKind B S hS p hp τ x).inverse := by
  ext M
  change M.IsQuasicoherentOnSite ↔
    ((localizationModulesEquivalenceKind B S hS p hp τ x).inverse.obj M).IsQuasicoherentOnSite
  rw [← Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff
    (J' := localizedTopologyKind B S hS p τ x) (localizationEquivalence B S hS p hp x)
    (baseRingStructureSheaf B (baseScheme B S hS p x) (contains_baseScheme B S hS p x) τ)
    ((localizationModulesEquivalenceKind B S hS p hp τ x).inverse.obj M)]
  exact ObjectProperty.prop_iff_of_iso _
    ((localizationModulesEquivalenceKind B S hS p hp τ x).counitIso.app M).symm

/-- **The inverse image `x^*𝓕` at an object `x`, for the topology `τ`.**  A sheaf of modules on
the associated `τ`-site of `𝒳` restricts to `𝒳_τ/x`, and that site with its restricted structure
sheaf *is* the big `τ`-site of the scheme `U = p(x)`; this is the resulting sheaf of modules on
`(Sch/U)_τ`. -/
public noncomputable abbrev objectInverseImageKind (τ : SiteKind) (x : 𝒳)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) :
    SheafOfModules.{u} (baseRingStructureSheaf B (baseScheme B S hS p x)
      (contains_baseScheme B S hS p x) τ) :=
  (localizationModulesEquivalenceKind B S hS p hp τ x).inverse.obj (M.over x)

/-- **Stacks 03DM at clause (6), read at a single module**: a sheaf of modules on `𝒳_τ/x` is
quasi-coherent exactly when the corresponding sheaf of modules on `(Sch/U)_τ` is. -/
public theorem isQuasicoherentOnSite_localization_iff_kind (τ : SiteKind) (x : 𝒳)
    (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp τ).over x)) :
    M.IsQuasicoherentOnSite ↔
      ((localizationModulesEquivalenceKind B S hS p hp τ x).inverse.obj
        M).IsQuasicoherentOnSite :=
  Iff.of_eq (congrFun (isQuasicoherentOnSite_over_eq_inverseImage_kind B S hS p hp τ x) M)

/-- **The localization criterion for quasi-coherence on `𝒳_τ`.**  A sheaf of modules on the
associated `τ`-site of a category fibred in groupoids is quasi-coherent if and only if its
inverse image `x^*𝓕` is a quasi-coherent sheaf on the big `τ`-site `(Sch/U)_τ` of the scheme
`U = p(x)`, for every object `x` of `𝒳`.

Necessity is stability of quasi-coherence under restriction to a slice site, transported along
the equivalence of ringed sites `𝒳_τ/x ≌ (Sch/U)_τ`.  Sufficiency is Stacks 03DN for the family
of all objects of `𝒳`, which covers the final object: quasi-coherence is a local and intrinsic
property, so no further input is needed.

At `τ = .fppf` this is the 06WI statement
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImage`. -/
public theorem isQuasicoherentOnSite_iff_forall_objectInverseImageKind (τ : SiteKind)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) :
    M.IsQuasicoherentOnSite ↔
      ∀ x : 𝒳, (objectInverseImageKind B S hS p hp τ x M).IsQuasicoherentOnSite := by
  refine ⟨fun hM x => (isQuasicoherentOnSite_localization_iff_kind B S hS p hp τ x
    (M.over x)).1 (Stacks.SheafOfModules.isQuasicoherentOnSite_over M hM x), fun h => ?_⟩
  rw [Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite M]
  exact ⟨ULift.{u + 1} 𝒳, fun i => i.down, Stacks.SheafOfModules.coversTop_ulift_self _,
    fun i => (isQuasicoherentOnSite_localization_iff_kind B S hS p hp τ i.down
      (M.over i.down)).2 (h i.down)⟩

end AlgebraicGeometry.FibredSite

end
