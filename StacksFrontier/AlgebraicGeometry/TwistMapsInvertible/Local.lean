module

public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic

/-!
# Invertibility of a module on a scheme from triviality on open subschemes

Invertibility of an `𝒪_X`-module is a local condition, and Stacks Tag 0B8M is already available
in the pointwise form "every point has an open neighbourhood over which the module becomes the
structure sheaf" —
`Stacks.InvertibleRankOneScheme.isInvertibleModule_of_forall_exists_mem_isoUnit_over`.
That form phrases the neighbourhood datum on the *slice site*, as `M.over U`. A trivialization
produced geometrically arrives instead as an isomorphism of the *restriction*
`M.restrict j ≅ 𝒪_Z` along an open immersion `j : Z ⟶ X`, with `Z` an abstract scheme rather than
an open subscheme of `X`. This file bridges the two, in both of the two steps that separate them.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit` and
  `overIsoUnitOfRestrictIsoUnit`: triviality of `M.over U` and triviality of `M.restrict U.ι`
  are interchangeable.
* `Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoRestrictOfIso`: restriction along an
  isomorphism of schemes is cancellable.
* `Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictOpensRangeIsoUnit`: a trivialization of
  `M` along an open immersion is a trivialization over the open subscheme that is its image.

## Main results

* `isInvertibleModule_of_forall_exists_restrict_isoUnit`, in the namespace below:
  **a module trivial on the open subschemes of a covering is invertible**, with the triviality
  stated as an isomorphism of restrictions.
* `isInvertibleModule_of_forall_exists_isoUnit_openImmersion`, in the same namespace:
  the same with the trivializing opens presented as the images of open immersions from abstract
  schemes. This is the form a chart-by-chart argument produces.

## The route

Nothing here is mathematics; all of it is transport, and each step is a named Mathlib or
repository isomorphism.

* The slice site and the open subscheme are related by
  `AlgebraicGeometry.Scheme.Modules.overEquiv`, an equivalence of categories, together with
  `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`, which identifies `M ↦ M.over U` followed by
  that equivalence with `M ↦ M.restrict U.ι`, and
  `Stacks.AlgebraicGeometry.CoherentFinite.overFunctorUnitIso`, which says the equivalence carries
  the structure sheaf to the structure sheaf. The direction out of the slice site is a composite;
  the direction into it is the same composite reflected through
  `CategoryTheory.Equivalence.fullyFaithfulFunctor`.
* Restriction along an isomorphism `e` is cancelled by restricting along `e.inv` and using
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`,
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` at `e.inv ≫ e.hom = 𝟙` and
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorId`.
* An open immersion `k : Z ⟶ X` is `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` followed by the
  inclusion of `k.opensRange`, so the two restrictions differ by restriction along an isomorphism,
  and `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` carries the structure sheaf back.

## Implementation notes

`isInvertibleModule_of_forall_exists_isoUnit_openImmersion` takes the open-immersion instance as an
ordinary existentially bound argument rather than as an instance binder, because the scheme `Z` and
the morphism `k` are themselves existentially bound and no instance can be registered for them. The
instance is introduced into the local context inside the proof, at which point
`Scheme.Modules.restrict` and `Scheme.Hom.opensRange` elaborate.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.TwistMapsInvertible

universe u

variable {X : Scheme.{u}}

/-! ### The slice site and the open subscheme -/

/-- **Triviality on the slice site gives triviality of the restriction.** The sections of `M` over
the opens below `U` are the sections of `M.restrict U.ι`, and the identification is the equivalence
`AlgebraicGeometry.Scheme.Modules.overEquiv`. -/
def restrictIsoUnitOfOverIsoUnit (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
      (Stacks.AlgebraicGeometry.CoherentFinite.overFunctorUnitIso U).symm

/-- **Triviality of the restriction gives triviality on the slice site.** The same composite as
`Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit`, reflected through the
fully faithful functor of the equivalence. -/
def overIsoUnitOfRestrictIsoUnit (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      Stacks.AlgebraicGeometry.CoherentFinite.overFunctorUnitIso U)

/-- **A module trivial on the open subschemes of a covering of `X` is invertible.** This is
`Stacks.InvertibleRankOneScheme.isInvertibleModule_of_forall_exists_mem_isoUnit_over` with the
trivialization stated on the open subscheme rather than on the slice site. -/
theorem isInvertibleModule_of_forall_exists_restrict_isoUnit (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    Stacks.Ample.IsInvertibleModule X M :=
  Stacks.InvertibleRankOneScheme.isInvertibleModule_of_forall_exists_mem_isoUnit_over X M
    fun x => (h x).imp fun _ hU => ⟨hU.1, hU.2.map (overIsoUnitOfRestrictIsoUnit M _)⟩

/-! ### Restriction along an isomorphism -/

/-- **Restriction along an isomorphism of schemes is cancellable**: restricting along `e.hom` and
then along `e.inv` returns the module it started from. -/
def restrictIsoRestrictOfIso {Y : Scheme.{u}} (M : X.Modules) (e : Y ≅ X) :
    M ≅ (M.restrict e.hom).restrict e.inv :=
  (Scheme.Modules.restrictFunctorId.app M).symm ≪≫
    ((Scheme.Modules.restrictFunctorCongr e.inv_hom_id).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorComp e.inv e.hom).app M

/-! ### Trivialization along an open immersion, and over its image -/

/-- **A trivialization of `M` along an open immersion is a trivialization over its image.** The
open immersion factors through the inclusion of its image by an isomorphism of schemes, and
restriction along that isomorphism is cancelled by
`Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoRestrictOfIso`. -/
def restrictOpensRangeIsoUnit (M : X.Modules) {Z : Scheme.{u}} (k : Z ⟶ X) [IsOpenImmersion k]
    (e : M.restrict k ≅ SheafOfModules.unit Z.ringCatSheaf) :
    M.restrict k.opensRange.ι ≅ SheafOfModules.unit k.opensRange.toScheme.ringCatSheaf :=
  letI i : Z ≅ k.opensRange.toScheme :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq k k.opensRange.ι (by simp)
  letI hfac : i.hom ≫ k.opensRange.ι = k :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac k k.opensRange.ι (by simp)
  restrictIsoRestrictOfIso (M.restrict k.opensRange.ι) i ≪≫
    (Scheme.Modules.restrictFunctor i.inv).mapIso
      (((Scheme.Modules.restrictFunctorComp i.hom k.opensRange.ι).app M).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr hfac).app M ≪≫ e) ≪≫
    Scheme.Modules.restrictUnitIso i.inv

/-- **A module trivial along a family of open immersions whose images cover `X` is invertible.**
This is the form a chart-by-chart argument produces: the trivializing neighbourhood of a point is
presented as the image of an open immersion from an abstract scheme, not as an open subscheme. -/
theorem isInvertibleModule_of_forall_exists_isoUnit_openImmersion (M : X.Modules)
    (h : ∀ x : X, ∃ (Z : Scheme.{u}) (k : Z ⟶ X) (_ : IsOpenImmersion k),
      x ∈ Set.range k.base ∧
        Nonempty ((Scheme.Modules.restrictFunctor k).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)) :
    Stacks.Ample.IsInvertibleModule X M := by
  refine isInvertibleModule_of_forall_exists_restrict_isoUnit M fun x => ?_
  obtain ⟨Z, k, hk, hx, ⟨e⟩⟩ := h x
  have := hk
  exact ⟨k.opensRange, hx, ⟨restrictOpensRangeIsoUnit M k e⟩⟩

end Stacks.AlgebraicGeometry.TwistMapsInvertible

end
