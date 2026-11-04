module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAlgebraRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnder
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnderlyingModule
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleTensor

/-!
# Quasi-coherent algebras on a representable algebraic space

Let `B` be a big fppf site containing a scheme `S`, let `U` be an object of the big fppf site
over `S` and let `T` be the scheme underlying `U`.  This file identifies the sheaves of
commutative `𝒪`-algebras on the small étale site of the algebraic space `yoneda.obj U` with the
sheaves of commutative `𝒪`-algebras on the small étale site of `T`, and matches quasi-coherence
across that identification.  It is the algebra counterpart of the module comparison of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedQuasicoherent.lean`, for the small étale site
on both sides.

## Main definitions

* `AlgebraicGeometry.Space.representedCommSheafCongr` is the transport of sheaves of commutative
  rings along the comparison equivalence of the two small étale sites.  The structure sheaf of
  *commutative* rings of the small étale site of `T` is
  `AlgebraicGeometry.Space.representedSchemeCommRingStructureSheaf`, imported from
  `StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleTensor`.
* `AlgebraicGeometry.Space.representedSchemeAlgebraModule` is the module underlying a sheaf of
  commutative algebras on the small étale site of `T`, and
  `AlgebraicGeometry.Space.representedSchemeAlgebraIsQuasicoherent` is quasi-coherence of that
  module on the site.
* `AlgebraicGeometry.Space.representedSmallEtaleAlgebraEquivalence` and
  `AlgebraicGeometry.Space.representedQuasicoherentAlgebraEquivalence` are the two equivalences:
  on all algebra sheaves, and on the quasi-coherent ones.
* `AlgebraicGeometry.Space.representedQuasicoherentAlgebraSchemeFunctor` composes the second with
  the Zariski restriction of
  `AlgebraicGeometry.SmallEtale.restrictQuasicoherentAlgebraToZariski` to land in the
  quasi-coherent `𝒪_T`-algebras on the Zariski site of `T`, which is where the scheme-level
  Stacks 01SA states its anti-equivalence.  That last leg is a functor and not an equivalence.

## Main results

* `AlgebraicGeometry.Space.representedCommSheafCongr_inverse_obj`: **the two structure sheaves
  of commutative rings agree**, by `rfl`.  This is the counterpart for sheaves of commutative
  rings of `AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`, and it holds
  for the same reason: the comparison of the two small étale sites leaves the underlying object
  of the category of size-bounded schemes unchanged, and both structure sheaves are the global
  regular functions on it.
* `AlgebraicGeometry.Space.underlyingModule_representedSmallEtaleAlgebraEquivalence`: the module
  underlying a transported algebra is the transport of the module underlying it, again by `rfl`.
* `AlgebraicGeometry.Space.isQuasicoherent_representedSmallEtaleAlgebraEquivalence_iff`:
  quasi-coherence is invariant under the comparison.

## Implementation notes

**The shape change is free and the site change is `rfl`.**  The two descriptions of an algebra
sheaf — a sectionwise family of ring homomorphisms out of the structure sheaf, which is
`AlgebraicGeometry.Space.AlgebraSheaf`, and a sheaf of commutative rings under the structure
sheaf, which is `CategoryTheory.Under` of it — are already identified in the universe of the
schemes by `AlgebraicGeometry.Space.AlgebraSheaf.underEquivalence`, whose two composites are the
identity definitionally.  The site change is then `CategoryTheory.Under.postEquiv` of the
transport of sheaves of commutative rings, which applies exactly because the structure sheaves
match on the nose.

That match is worth stating plainly, because the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineAlgebraAntiEquivalenceReduction.lean` record that
the algebra sides "differ in shape as well as site" and that the comparison is therefore
missing.  Both halves of that are supplied here, for the small étale site of `T`.  What is
*not* supplied — and what the quoted note is right about — is the passage from the small étale
site of `T` to its *Zariski* site, which is where the scheme-level Stacks 01SA takes its
algebras; see below.

**Why the transport is the inverse of
`AlgebraicGeometry.Space.representedCommSheafCongr`, not its functor.**
`CategoryTheory.Equivalence.sheafCongr` has as its *inverse* the precomposition with
`e.functor.op`, and it is that precomposition which carries the structure sheaf of the small
étale site of `T` to the structure sheaf of the small étale site of `yoneda.obj U`.  The functor
of the same equivalence is precomposition with `e.inverse.op` and carries neither to the other
on the nose, so `CategoryTheory.Under.postEquiv` is applied to the symmetric equivalence.

**The remaining leg is a functor, not an equivalence.**  The passage from the small étale site
of `T` to its Zariski site, where the scheme-level Stacks 01SA takes its algebras, is built as
`AlgebraicGeometry.SmallEtale.restrictQuasicoherentAlgebraToZariski` and composed in here as
`AlgebraicGeometry.Space.representedQuasicoherentAlgebraSchemeFunctor`.  It goes only one way.
The algebra analogue of Descent, Proposition 03DX (2) at `τ = étale` — an *equivalence* between
the quasi-coherent algebras on the two sites — is not available, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleAlgebraRestriction.lean` name
the two statements it would need: the multiplication of an algebra as a morphism out of a tensor
product on the small étale site, which exists in this development only on a scheme's Zariski
site, and invertibility of
`Stacks.SheafOfModules.AlgebraPushout.extendScalarsComparison`, which is unproved and is in
addition stated only for a `CategoryTheory.SmallCategory` site.

No declaration here carries a `stacks` tag.  This is an input to Stacks 081V, not an assertion
of it: 081V asserts an anti-equivalence between the algebraic spaces affine over `X` and the
quasi-coherent `𝒪_X`-algebras together with its compatibility with arbitrary base change, and
nothing below asserts either.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)

/-! ### The two structure sheaves of commutative rings -/

/-- Transport of sheaves of commutative rings along the comparison equivalence of the small
étale site of `yoneda.obj U` with the small étale site of the scheme underlying `U`. -/
abbrev representedCommSheafCongr :
    Sheaf (SmallEtale.topology B S hS (yoneda.obj U)) CommRingCat.{u} ≌
      Sheaf (representedSchemeSmallEtaleTopology B S hS U) CommRingCat.{u} :=
  (representedSmallEtaleEquivalence B S hS U).sheafCongr
    (SmallEtale.topology B S hS (yoneda.obj U))
    (representedSchemeSmallEtaleTopology B S hS U) CommRingCat.{u}

/-- **The two structure sheaves of commutative rings of the comparison equivalence agree.**
Precomposition with the comparison functor carries the structure sheaf of commutative rings of
the small étale site of the scheme underlying `U` to the structure sheaf of commutative rings of
the small étale site of the algebraic space `yoneda.obj U`.

This is the counterpart for sheaves of *commutative* rings of
`AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`, and holds by `rfl` for
the same reason: both structure sheaves are the global regular functions on the underlying
object of the category of size-bounded schemes, which the comparison leaves unchanged. -/
theorem representedCommSheafCongr_inverse_obj :
    (representedCommSheafCongr B S hS U).inverse.obj
        (representedSchemeCommRingStructureSheaf B S hS U) =
      structureSheaf B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) :=
  rfl

/-- Forgetting the commutativity of the structure sheaf of the small étale site of the scheme
underlying `U` gives `AlgebraicGeometry.Space.representedSchemeStructureSheaf`, the sheaf of
rings in which the modules on that site are indexed. -/
theorem ringSheaf_representedSchemeCommRingStructureSheaf :
    Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeCommRingStructureSheaf B S hS U) =
      representedSchemeStructureSheaf B S hS U :=
  rfl

/-! ### The module underlying an algebra on the small étale site of the scheme -/

/-- The module underlying a sheaf of commutative algebras on the small étale site of the scheme
underlying `U`, named at this site:
`AlgebraicGeometry.SmallEtale.algebraUnderlyingModule` of the scheme underlying `U` in the big
étale site associated with `B`. -/
abbrev representedSchemeAlgebraModule
    (A : Under (representedSchemeCommRingStructureSheaf B S hS U)) :
    SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U) :=
  _root_.AlgebraicGeometry.SmallEtale.algebraUnderlyingModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property A

/-- Quasi-coherence of a sheaf of commutative algebras on the small étale site of the scheme
underlying `U`, named at this site:
`AlgebraicGeometry.SmallEtale.AlgebraIsQuasicoherent` of the scheme underlying `U`. -/
abbrev representedSchemeAlgebraIsQuasicoherent :
    ObjectProperty (Under (representedSchemeCommRingStructureSheaf B S hS U)) :=
  _root_.AlgebraicGeometry.SmallEtale.AlgebraIsQuasicoherent (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property

/-! ### The two equivalences -/

/-- **The algebra sheaves on the small étale sites of `yoneda.obj U` and of the scheme
underlying `U` correspond.**  A sheaf of commutative algebras on the small étale site of the
scheme underlying `U` is the same thing as an `AlgebraicGeometry.Space.AlgebraSheaf` on the small
étale site of the algebraic space `yoneda.obj U`.

The site change is the transport of sheaves of commutative rings, available on the `Under`
categories because the two structure sheaves agree by
`AlgebraicGeometry.Space.representedCommSheafCongr_inverse_obj`; the shape change is
`AlgebraicGeometry.Space.AlgebraSheaf.underEquivalence`. -/
def representedSmallEtaleAlgebraEquivalence :
    Under (representedSchemeCommRingStructureSheaf B S hS U) ≌
      AlgebraSheaf.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) :=
  (Under.postEquiv (representedSchemeCommRingStructureSheaf B S hS U)
      (representedCommSheafCongr B S hS U).symm).trans
    AlgebraSheaf.underEquivalence.symm

/-- **The module underlying a transported algebra is the transport of its underlying module.**
Both are the algebra's own sections read on the small étale site of `yoneda.obj U`, with scalars
restricted along the structure morphism; the comparison of the sites is precomposition, which
changes neither. -/
theorem underlyingModule_representedSmallEtaleAlgebraEquivalence
    (A : Under (representedSchemeCommRingStructureSheaf B S hS U)) :
    ((representedSmallEtaleAlgebraEquivalence B S hS U).functor.obj A).underlyingModule =
      representedSmallEtaleModule B S hS U (representedSchemeAlgebraModule B S hS U A) :=
  rfl

/-- **Quasi-coherence is invariant under the comparison.**  A sheaf of commutative algebras on
the small étale site of the scheme underlying `U` has quasi-coherent underlying module exactly
when the algebra sheaf it becomes on the small étale site of `yoneda.obj U` is quasi-coherent.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleModule_iff` — Stacks
03DM for clause (6) of Stacks 03DL — applied to the underlying modules, which
`AlgebraicGeometry.Space.underlyingModule_representedSmallEtaleAlgebraEquivalence` identifies. -/
theorem isQuasicoherent_representedSmallEtaleAlgebraEquivalence_iff
    (A : Under (representedSchemeCommRingStructureSheaf B S hS U)) :
    AlgebraSheaf.IsQuasicoherent
        ((representedSmallEtaleAlgebraEquivalence B S hS U).functor.obj A) ↔
      representedSchemeAlgebraIsQuasicoherent B S hS U A := by
  rw [AlgebraSheaf.IsQuasicoherent, underlyingModule_representedSmallEtaleAlgebraEquivalence]
  exact isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U _

/-- Quasi-coherence of an algebra on the small étale site of the scheme underlying `U` is the
inverse image, along the equivalence of algebra categories, of quasi-coherence of an algebra
sheaf on the small étale site of `yoneda.obj U`.  This is the equality of object properties which
cuts the equivalence down to the quasi-coherent algebras. -/
theorem inverseImage_isQuasicoherent_representedSmallEtaleAlgebraEquivalence :
    ObjectProperty.inverseImage
        (AlgebraSheaf.IsQuasicoherent :
          ObjectProperty (AlgebraSheaf.{u, u} B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)))
        (representedSmallEtaleAlgebraEquivalence B S hS U).functor =
      representedSchemeAlgebraIsQuasicoherent B S hS U := by
  funext A
  exact propext (isQuasicoherent_representedSmallEtaleAlgebraEquivalence_iff B S hS U A)

/-- **The quasi-coherent algebras on the small étale sites of `yoneda.obj U` and of the scheme
underlying `U` correspond.**  The equivalence of algebra categories restricts to an equivalence
between the quasi-coherent algebras on the small étale site of the scheme underlying `U` and the
quasi-coherent `AlgebraicGeometry.Space.AlgebraSheaf` on the small étale site of the algebraic
space `yoneda.obj U`, which is `AlgebraicGeometry.Space.QuasicoherentAlgebra` there — the very
category in which Stacks 081V states its anti-equivalence. -/
def representedQuasicoherentAlgebraEquivalence :
    (representedSchemeAlgebraIsQuasicoherent B S hS U).FullSubcategory ≌
      QuasicoherentAlgebra B S hS
        ⟨yoneda.obj U, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U⟩ :=
  (representedSmallEtaleAlgebraEquivalence B S hS U).congrFullSubcategory
    (inverseImage_isQuasicoherent_representedSmallEtaleAlgebraEquivalence B S hS U)

/-- **A quasi-coherent algebra on a representable algebraic space is a quasi-coherent algebra on
the underlying scheme.**  This is the functor
`QCAlg(𝒪_{yoneda.obj U}) ⥤ QCAlg(𝒪_T)` for `T` the scheme underlying `U`, with the target the
quasi-coherent sheaves of commutative `𝒪_T`-algebras on the *Zariski* site of `T` — the category
in which the scheme-level Stacks 01SA,
`Stacks.AffineAlgebraEquivalence.affineQuasicoherentEquivalence`, states its anti-equivalence.

It is the inverse of
`AlgebraicGeometry.Space.representedQuasicoherentAlgebraEquivalence`, which changes the shape and
the site and is an equivalence, followed by
`AlgebraicGeometry.SmallEtale.restrictQuasicoherentAlgebraToZariski`, which restricts from the
small étale site of `T` to its Zariski site and is *not* known to be an equivalence.  So this is
a functor and not an equivalence; it is nevertheless the direction in which the construction of
Stacks 081V uses it, namely to restrict an algebra to an étale chart and apply 01SA there.  The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleAlgebraRestriction.lean` say
exactly which two statements an equivalence would need. -/
def representedQuasicoherentAlgebraSchemeFunctor :
    QuasicoherentAlgebra B S hS
        ⟨yoneda.obj U, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U⟩ ⥤
      Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra
        ((BigFppfOver.toScheme B S hS).obj U) :=
  (representedQuasicoherentAlgebraEquivalence B S hS U).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictQuasicoherentAlgebraToZariski
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property

end AlgebraicGeometry.Space

end
