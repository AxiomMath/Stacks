module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModules
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# The resolution property does not see the base scheme

Let `g : T ⟶ S` be a morphism of a big fppf site and let `Λ X` be the lower-shriek extension of
Stacks 03I5 (2) of an algebraic space `X` over `T`, that is, `X` viewed over the larger base `S`;
the absolute view `AlgebraicGeometry.Space.viewOverIntegers` of Stacks 03BS is the case where `S`
is the terminal scheme `Spec ℤ`.

The resolution property of Stacks 0GUS quantifies over quasi-coherent modules of finite type on
the *small étale* site of an algebraic space, and étale morphisms of spaces do not see the base:
the small étale sites of `X` and of `Λ X` are equivalent as ringed sites, by
`AlgebraicGeometry.Space.SmallEtale.relocalize`, so their categories of `𝒪`-modules are identified
by `AlgebraicGeometry.Space.relocalizeModulesEquivalence` with no change of rings.  Each of the
three conditions occurring in Stacks 0GUS — quasi-coherence, finite type, finite local freeness —
is invariant under an equivalence of ringed sites, three instances of Stacks 03DM.  So the
resolution property is invariant under the change of base site, in both directions, and that is
what this file proves.

Nothing here assumes anything about `g`, `T` or `S` beyond their being objects of the big fppf
site, and nothing here is a special case: the result is an `Iff`.

## Main results

* `AlgebraicGeometry.Space.isFiniteTypeOnSite_relocalizeModulesEquivalence_iff` and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_relocalizeModulesEquivalence_iff`: finite
  type, Stacks 03DL (5), and finite local freeness, Stacks 03DL (2), are invariant under the
  equivalence of module categories.  These are the two companions of
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_relocalizeModulesEquivalence_iff`.
* `AlgebraicGeometry.Space.hasResolutionProperty_relocalize_iff`: **`Λ X` has the resolution
  property exactly when `X` does.**
* `AlgebraicGeometry.Space.hasResolutionProperty_viewOverIntegers_iff`: the same for the absolute
  view of Stacks 03BS — the `Spec ℤ` view of an algebraic space over `S` has the resolution
  property exactly when the space over `S` does.
* `AlgebraicGeometry.Space.hasResolutionProperty_of_viewOverIntegers`: the reflecting direction on
  its own, which is the direction a result proved over `Spec ℤ` needs in order to be read over a
  general base `S`.

## Implementation notes

The transport of the three module conditions is not proved here; the library already has it for
an arbitrary equivalence of ringed sites, as instances of Stacks 03DM:

* quasi-coherence by `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff`;
* finite type by `Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_reindex_iff`;
* finite local freeness by `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff`.

The inverse functor of `AlgebraicGeometry.Space.relocalizeModulesEquivalence` *is* the reindexing
`SheafOfModules.pushforward (𝟙 _)` of those three statements, with the reindexed sheaf of rings
equal to the sheaf of rings of the small étale ringed site of `X` on the nose
(`AlgebraicGeometry.Space.reindexRing_relocalize`, an equality by `rfl`), so the two wrappers below
are the bare transport results and need no comparison isomorphism.

Both directions of the main result need one iso-invariance step, because the round trip of the
equivalence returns a module only isomorphic to the one it started from: going from `X` to `Λ X`
that step is for finite local freeness
(`Stacks.SheafOfModules.Intrinsic.isFiniteLocallyFreeOnSite_of_iso`), and coming back it is for
quasi-coherence (`SheafOfModules.IsQuasicoherentOnSite.of_iso`) and for finite type
(`Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso`).

**The module universe is `{u, u}`**, the universe of the coefficient rings, as in
`AlgebraicGeometry.Space.IsResolutionBlowupStratified` and in every resolution-property
result of this library.  Here it is forced rather than chosen: the three transport results are
stated for a sheaf of modules whose sections live in the universe of its sheaf of rings.

**The algebraicity of `Λ X` is not a hypothesis.**  It is derived from that of `X` by
`AlgebraicGeometry.Space.isAlgebraicSpace_relocalize'` (Stacks 03I5 (2)).  Since
`AlgebraicGeometry.IsAlgebraicSpace` is a `Prop`, proof irrelevance makes the statements below
apply to any other proof of it a caller may be holding.

## References

* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) (X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B T hT X)

/-- **Finite type on the small étale site is invariant under the change of base site.**  A module
on `Λ X` is of finite type exactly when the module on `X` it corresponds to is.

This is Stacks 03DM for clause (5) of Stacks 03DL, read at the equivalence of small étale ringed
sites of `X` and of `Λ X`; it is the finite-type companion of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_relocalizeModulesEquivalence_iff`. -/
theorem isFiniteTypeOnSite_relocalizeModulesEquivalence_iff
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) :
    SheafOfModules.IsFiniteTypeOnSite
        ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M) ↔
      SheafOfModules.IsFiniteTypeOnSite M :=
  (Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_reindex_iff
    (J' := SmallEtale.topology B T hT X) (SmallEtale.relocalize B hT hS g X hX)
    (relocalizeRingSheaf B hT hS g X hX) M).symm

/-- **Finite local freeness on the small étale site is invariant under the change of base site.**
A module on `Λ X` is finite locally free exactly when the module on `X` it corresponds to is.

This is Stacks 03DM for clause (2) of Stacks 03DL, read at the equivalence of small étale ringed
sites of `X` and of `Λ X`. -/
theorem isFiniteLocallyFreeOnSite_relocalizeModulesEquivalence_iff
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
        ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite M :=
  Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff
    (J' := SmallEtale.topology B T hT X) (SmallEtale.relocalize B hT hS g X hX)
    (relocalizeRingSheaf B hT hS g X hX) M

/-- An epimorphism `f : E ⟶ e.inverse.obj M` transports along an equivalence to the epimorphism
`e.functor.map f ≫ e.counitIso.hom.app M`. -/
private theorem epi_functor_map_comp_counitIso {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) {E : C} {M : D} (f : E ⟶ e.inverse.obj M) [Epi f] :
    Epi (e.functor.map f ≫ e.counitIso.hom.app M) :=
  have : Functor.PreservesEpimorphisms e.functor :=
    Functor.preservesEpimorphisms_of_adjunction e.toAdjunction
  epi_comp' (Functor.map_epi _ f) (IsIso.epi_of_iso _)

/-- **The resolution property of Stacks 0GUS is invariant under the change of base site of
Stacks 03I5 (2).**  An algebraic space `X` over `T` has the resolution property exactly when `Λ X`,
the same space viewed over the larger base `S`, does.

The small étale sites of `X` and of `Λ X` are equivalent as ringed sites, so their categories of
`𝒪`-modules are equivalent with no change of rings, and quasi-coherence, finite type and finite
local freeness are each invariant under such an equivalence — three instances of Stacks 03DM.  An
epimorphism from a finite locally free module onto a quasi-coherent module of finite type
therefore crosses the equivalence in either direction. -/
theorem hasResolutionProperty_relocalize_iff :
    HasResolutionProperty.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
        (isAlgebraicSpace_relocalize' B hT hS g X hX) ↔
      HasResolutionProperty.{u, u} B T hT X hX := by
  refine ⟨fun hΛ => ⟨fun N hNft => ?_⟩, fun hXres => ⟨fun M hMft => ?_⟩⟩
  · have hqc : SheafOfModules.IsQuasicoherentOnSite
        ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj N.obj) :=
      (isQuasicoherentOnSite_relocalizeModulesEquivalence_iff B hT hS g X hX _).1
        (SheafOfModules.IsQuasicoherentOnSite.of_iso
          ((relocalizeModulesEquivalence B hT hS g X hX).unitIso.app N.obj) N.property)
    have hft : SheafOfModules.IsFiniteTypeOnSite
        ((relocalizeModulesEquivalence B hT hS g X hX).functor.obj N.obj) :=
      (isFiniteTypeOnSite_relocalizeModulesEquivalence_iff B hT hS g X hX _).1
        (Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso
          ((relocalizeModulesEquivalence B hT hS g X hX).unitIso.app N.obj) hNft)
    obtain ⟨E, hE, f, hf⟩ := hΛ.1
      (⟨(relocalizeModulesEquivalence B hT hS g X hX).functor.obj N.obj, hqc⟩ :
        QuasicoherentSheaves.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
          (isAlgebraicSpace_relocalize' B hT hS g X hX))
    have := hf
    exact ⟨(relocalizeModulesEquivalence B hT hS g X hX).inverse.obj E,
      (isFiniteLocallyFreeOnSite_relocalizeModulesEquivalence_iff B hT hS g X hX E).2 hE, _,
      epi_functor_map_comp_counitIso (relocalizeModulesEquivalence B hT hS g X hX).symm f⟩
  · have hft : SheafOfModules.IsFiniteTypeOnSite
        ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M.obj) :=
      (isFiniteTypeOnSite_relocalizeModulesEquivalence_iff B hT hS g X hX M.obj).2 hMft
    obtain ⟨E, hE, f, hf⟩ := hXres.1
      (⟨(relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M.obj,
        (isQuasicoherentOnSite_relocalizeModulesEquivalence_iff B hT hS g X hX M.obj).2
          M.property⟩ : QuasicoherentSheaves.{u, u} B T hT X hX)
    have := hf
    exact ⟨(relocalizeModulesEquivalence B hT hS g X hX).functor.obj E,
      (isFiniteLocallyFreeOnSite_relocalizeModulesEquivalence_iff B hT hS g X hX _).1
        (Stacks.SheafOfModules.Intrinsic.isFiniteLocallyFreeOnSite_of_iso
          ((relocalizeModulesEquivalence B hT hS g X hX).unitIso.app E) hE), _,
      epi_functor_map_comp_counitIso (relocalizeModulesEquivalence B hT hS g X hX) f⟩

/-! ### The absolute view of Stacks 03BS -/

/-- **The resolution property is invariant under the absolute view of Stacks 03BS.**  An algebraic
space over `S` has the resolution property exactly when its view over the terminal scheme
`Spec ℤ` does.

This is `AlgebraicGeometry.Space.hasResolutionProperty_relocalize_iff` at the structure morphism of
`S` to the terminal scheme, which is the morphism
`AlgebraicGeometry.Space.viewOverIntegers` is the lower-shriek extension along. -/
theorem hasResolutionProperty_viewOverIntegers_iff (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y) :
    HasResolutionProperty.{u, u} B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ Y)
        (isAlgebraicSpace_relocalize' B hS hZ (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) Y hY) ↔
      HasResolutionProperty.{u, u} B S hS Y hY :=
  hasResolutionProperty_relocalize_iff B hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) Y hY

/-- **The resolution property of the `Spec ℤ` view of an algebraic space is the resolution property
of the space over its own base.**

This is the reflecting half of
`AlgebraicGeometry.Space.hasResolutionProperty_viewOverIntegers_iff`, stated on its own because it
is the direction that a result proved over the terminal scheme — such as Step 1 of Stacks 0GV6,
`AlgebraicGeometry.Space.isResolutionBlowupStratified_top_of_isQuasiCompactSpace_overIntegers` —
needs in order to be read over a general base `S`.  The algebraicity hypothesis on the view is an
explicit binder here rather than
`AlgebraicGeometry.Space.isAlgebraicSpace_relocalize'`, so that it applies to whatever proof a
caller is holding; being a `Prop`, the two agree. -/
theorem hasResolutionProperty_of_viewOverIntegers (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ Y))
    (hres : HasResolutionProperty.{u, u} B (⊤_ Scheme.{u}) hZ
      (viewOverIntegers B S hS hZ Y) hY') :
    HasResolutionProperty.{u, u} B S hS Y hY :=
  (hasResolutionProperty_viewOverIntegers_iff B hS hZ Y hY).1 hres

end AlgebraicGeometry.Space

end
