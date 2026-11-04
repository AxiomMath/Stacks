module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentSelfChart

/-!
# Finite local freeness of a module on a representable algebraic space, from the scheme

Let `B` be a big fppf site containing a scheme `S` and let `U` be an object of the big fppf site
over `S`, with underlying scheme `T`.  A quasi-coherent `AlgebraicGeometry.Scheme.Modules` on `T`
— a quasi-coherent module on the *Zariski* site of `T` — becomes an `𝒪`-module on the small
étale site of the algebraic space `yoneda.obj U` under
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, which is Descent,
Proposition 03DX (2) at `τ = étale` followed by the comparison of the two small étale sites.
This file carries finite local freeness along that transport.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedQuasicoherentSchemeEquivalence`:
  **a finite locally free quasi-coherent module on `T` becomes a finite locally free `𝒪`-module
  on the small étale site of `yoneda.obj U`.**

## Implementation notes

The transport is the composite of two steps. The first is the passage from the Zariski site of
`T` to the small étale site of `T` along the associated-module functor of Stacks 03DU (4),
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule`. The hypothesis is
taken in the local-generators form `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` of
Stacks 01C6 (2), the form in which
`AlgebraicGeometry.isFiniteLocallyFree_universalConormalSheaf_of_isLocalCompleteIntersection`
(Stacks 06B9) states finite local freeness.

The second is `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff`,
Stacks 03DM for clause (2) of Stacks 03DL at the equivalence of ringed sites of the two small
étale sites.

The action of `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` on the
underlying module is the associated module read across the site comparison, by `rfl`
(`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence_functor_obj_obj`), so the two
steps compose directly. The same pattern gives finite type, clause (5) of Stacks 03DL, in
`AlgebraicGeometry.Space.isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence`.

## What this does and does not settle

This is the comparison numbered (1) in the section *What is not proved here* of the module that
declares `AlgebraicGeometry.Space.RepresentableConormalSheafComparison`
(`Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/Conormal.lean`).  That hypothesis is
**not** thereby discharged: it carries comparison (2) as well, the identification of
`AlgebraicGeometry.Space.conormalSheaf` of a formally unramified morphism of representable
algebraic spaces with `Stacks.Thickenings.universalConormalSheaf` of the corresponding morphism
of schemes.  What this file supplies is the transport of the *property* along a transport of the
*module*; without (2) there is nothing saying that the module `conormalSheaf` is the transport of
the scheme-level conormal sheaf, so the property cannot be moved onto it.  See that file for the
state of (2).

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **A finite locally free quasi-coherent module on a scheme is finite locally free on the small
étale site of the algebraic space the scheme represents.**  Let `U` be an object of the big fppf
site over `S` and let `M` be a quasi-coherent module on the Zariski site of the scheme underlying
`U` which is finite locally free in the sense of Stacks 01C6 (2).  Then the `𝒪`-module `M`
becomes on the small étale site of `yoneda.obj U` is finite locally free in the sense of
clause (2) of Stacks 03DL.

The two steps are the associated-module functor of Stacks 03DU (4) at the scheme, and the
comparison of the two small étale sites. -/
public theorem isFiniteLocallyFreeOnSite_representedQuasicoherentSchemeEquivalence
    (M : SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf)
    (hM : SheafOfModules.IsQuasicoherent M)
    (hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨M, hM⟩).obj := by
  have hetale : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M) :=
    _root_.AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property M hflf
  exact (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS U _).2 hetale

end AlgebraicGeometry.Space

end
