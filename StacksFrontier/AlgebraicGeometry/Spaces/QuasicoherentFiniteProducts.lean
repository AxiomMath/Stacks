module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence is closed under finite products, unconditionally

`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure` proves that quasi-coherence of
sheaves of modules on a site is closed under binary products, under binary coproducts and under
finite products, but each of those statements carries one hypothesis: that *having a global
presentation is stable under restriction along a morphism of the site*.  That hypothesis is
exactly `Stacks.SheafOfModules.hasGlobalPresentation_overMap`, proved in
`StacksDraft.Ch18.Sec23.QuasicoherenceLocalOnCover` for the clause of Stacks 03DN about
quasi-coherence.  Discharging it here makes the three closure properties unconditional
instances, on an arbitrary site and over an arbitrary sheaf of rings, in every module universe.

## Main results

* `SheafOfModules.isQuasicoherentOnSite_isClosedUnderBinaryProducts`,
  `SheafOfModules.isQuasicoherentOnSite_isClosedUnderBinaryCoproducts` and
  `SheafOfModules.isQuasicoherentOnSite_isClosedUnderFiniteProducts`: the three closure
  properties of `SheafOfModules.isQuasicoherentOnSite`, as instances.
* `SheafOfModules.isQuasicoherentOnSite_biprod` and
  `SheafOfModules.isQuasicoherentOnSite_coprod`: a binary biproduct, respectively a binary
  direct sum, of quasi-coherent sheaves of modules is quasi-coherent.

## Implementation notes

The two files this one joins were written apart from each other, and neither imports the other:
`QuasicoherentClosure` is reached through
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck`, while
`QuasicoherenceLocalOnCover` sits over
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels` and mentions no algebraic
space.  Nothing but the import is needed to connect them: the hypothesis of the closure theorems
and the conclusion of `Stacks.SheafOfModules.hasGlobalPresentation_overMap` agree up to the
binders, which is what `hasGlobalPresentation_over` records.

The universes are those of `SheafOfModules.HasGlobalPresentation`: the site objects, the site
morphisms, the coefficient rings and the module sections are independent, and none of the three
instances constrains them.  In particular they apply on the small étale ringed site of an
algebraic space at `{u + 1, u, u, m}` with the module universe `m` free, which is where
`AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` asks for the finite-product
clause.

No `@[stacks 03M1]` tag is carried.  The direct-sum clause of Stacks 03M1 is about *arbitrary*
direct sums, and the argument here reaches only finite ones: two quasi-coherent modules are
presented on two possibly different coverings of an object, and a Grothendieck topology is
closed under binary intersections of covering sieves but not under infinite ones.  The remaining
clauses of Stacks 03M1 — kernels, cokernels, extensions, arbitrary direct sums and arbitrary
colimits — are not consequences of restriction-stability of global presentations.  All of them
reduce, by the étale localization of the source proof, to one statement about the slice of the
small étale site at an étale chart with affine underlying scheme: that a quasi-coherent module
there is the module associated with a module over a ring, hence *globally* presented, which is
the content of Stacks 03DX and rests on Stacks 03DW.  For the fppf site associated with a
category fibred in groupoids that statement is a theorem of this development with nothing
assumed, `AlgebraicGeometry.FibredSite.isAffineLocallySpanned_of_isQuasicoherentOnSite`; what is
missing is the same material for the small étale site.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Having a global presentation is stable under restriction along a morphism of the site, in
the binder shape in which the closure theorems of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure` ask for it.  This is
`Stacks.SheafOfModules.hasGlobalPresentation_overMap`. -/
private theorem hasGlobalPresentation_over (R : Sheaf J RingCat.{r}) :
    ∀ (M : SheafOfModules.{m} R) {X Y : C}, (X ⟶ Y) →
      (M.over Y).HasGlobalPresentation → (M.over X).HasGlobalPresentation :=
  fun M _ _ f h ↦ Stacks.SheafOfModules.hasGlobalPresentation_overMap M f h

/-- Quasi-coherence of sheaves of modules on a site is closed under binary products. -/
instance isQuasicoherentOnSite_isClosedUnderBinaryProducts (R : Sheaf J RingCat.{r}) :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderBinaryProducts :=
  isClosedUnderBinaryProducts_isQuasicoherentOnSite R (hasGlobalPresentation_over R)

/-- Quasi-coherence of sheaves of modules on a site is closed under binary coproducts. -/
instance isQuasicoherentOnSite_isClosedUnderBinaryCoproducts (R : Sheaf J RingCat.{r}) :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderBinaryCoproducts :=
  isClosedUnderBinaryCoproducts_isQuasicoherentOnSite R (hasGlobalPresentation_over R)

/-- Quasi-coherence of sheaves of modules on a site is closed under finite products.  This is
the third of the three closure properties that
`SheafOfModules.abelian_fullSubcategory_isQuasicoherentOnSite` consumes, and the only one of
them that needs no cohomological input. -/
instance isQuasicoherentOnSite_isClosedUnderFiniteProducts (R : Sheaf J RingCat.{r}) :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderFiniteProducts :=
  isClosedUnderFiniteProducts_isQuasicoherentOnSite R (hasGlobalPresentation_over R)

variable {R : Sheaf J RingCat.{r}}

/-- A binary biproduct of quasi-coherent sheaves of modules is quasi-coherent. -/
theorem isQuasicoherentOnSite_biprod {M N : SheafOfModules.{m} R} [HasBinaryBiproduct M N]
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (M ⊞ N).IsQuasicoherentOnSite :=
  IsQuasicoherentOnSite.biprod (hasGlobalPresentation_over R) hM hN

/-- The direct sum of two quasi-coherent sheaves of modules is quasi-coherent.  This is the
binary case of the direct-sum clause of Stacks 03M1. -/
@[ega "0 5.1.3" "special case", ega "I 4.1.1" "Direct sums: binary case"]
theorem isQuasicoherentOnSite_coprod (M N : SheafOfModules.{m} R) [HasBinaryCoproduct M N]
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (M ⨿ N).IsQuasicoherentOnSite :=
  IsQuasicoherentOnSite.coprod (hasGlobalPresentation_over R) M N hM hN

end SheafOfModules

end
