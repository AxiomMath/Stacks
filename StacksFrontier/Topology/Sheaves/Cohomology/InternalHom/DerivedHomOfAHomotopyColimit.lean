module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomCoproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom out of a homotopy colimit on a ringed space

Let `(X, O_X)` be a ringed space, let `(Kₙ, fₙ)` be a system of objects of `D(O_X)`, let
`K = hocolim Kₙ` be the derived colimit of Stacks 090Z and let `E` be an object of `D(O_X)`.
**Stacks 0DJI** says that when the `Kₙ` are perfect

`RSheafHom(K, E) = R lim (E ⊗^L_{O_X} Kₙ^∨)`,

the right-hand side being the derived limit of the inverse system of tensor products with the
dual perfect complexes `Kₙ^∨ = RSheafHom(Kₙ, O_X)`.

A topological space with a sheaf of commutative rings *is* a ringed site, namely the site of its
opens with the open-cover topology, so the ringed-site statement of Stacks 0A0A applies verbatim.
The declarations below read it off along `Stacks.SheafOfModules.ringedSite`, for the derived
tensor product of `Stacks.SheafOfModules.canonicalDerivedTensorProduct`, exactly as the dual and
the canonical map `M ⊗^L_{O_X} L^∨ ⟶ RSheafHom(L, M)` are read off in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual`.

The source's proof has two halves. The formal half rewrites the right-hand side as
`R lim RSheafHom(Kₙ, E)` and compares the triangle defining that derived limit with the image
under `RSheafHom(-, E)` of the triangle `⊕ Kₙ → ⊕ Kₙ → K` defining the derived colimit; the
comparison needs `RSheafHom(⊕ Kₙ, E) = ∏ RSheafHom(Kₙ, E)`. The other half is the rewriting
itself, which is the third assertion of Stacks 08DQ: the canonical map
`E ⊗^L_{O_X} Kₙ^∨ ⟶ RSheafHom(Kₙ, E)` of Stacks 08I1 is an isomorphism when `Kₙ` is perfect. The
formal half is proved in full at the site level, in the modules
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomCoproducts`, the latter
supplying the direct sum comparison. That assertion of Stacks 08DQ is proved, from perfectness
alone, as `Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect`
(`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom`), so both halves are
available and the tag holds in the source's own form, with the `Kₙ` perfect and nothing else
assumed. It is also kept below as the hypothesis `hdual` of a more general statement, which
applies to a system that is not perfect.

## Main definitions

* `Stacks.SheafOfModules.derivedSheafHomSystem`: the inverse system `n ↦ RSheafHom(Kₙ, E)`.
* `Stacks.SheafOfModules.tensorDerivedDualSystem`: the inverse system `n ↦ E ⊗^L_{O_X} Kₙ^∨`.

## Main results

* `Stacks.SheafOfModules.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit`:
  `RSheafHom(hocolim Kₙ, E) = R lim RSheafHom(Kₙ, E)`, unconditionally — for an arbitrary system
  of objects of `D(O_X)` and an arbitrary `E`. No perfectness is needed and nothing is assumed
  to exist.
* `Stacks.SheafOfModules.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit`: the statement of
  **Stacks 0DJI** for an arbitrary system, granted the third assertion of Stacks 08DQ for each
  `Kₙ` as the hypothesis `hdual`. Perfectness is not assumed, so this is the more general form.
* `Stacks.SheafOfModules.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit_of_isPerfect`:
  **Stacks 0DJI** as the Stacks Project states it — the `Kₙ` perfect, and nothing else assumed.
  `hdual` is discharged from perfectness by
  `Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect`.

## Implementation notes

The conclusion is the predicate `CategoryTheory.Pretriangulated.IsDerivedLimit`, that
`RSheafHom(K, E)` *is* a derived limit of the inverse system, rather than an isomorphism onto a
chosen `R lim`. In a pre-triangulated category a derived limit is unique only up to a non-unique
isomorphism, so there is no "the" `R lim` object for the source's equality sign to relate; the
predicate is the content of that equality, and it is not weaker. Unfolding it produces the two
morphisms of the defining triangle, and the proof constructs both of them explicitly — nothing
below is obtained from a choice principle applied to an existence statement.

There are two forms of the tag below, and perfectness distinguishes them. In the source,
perfectness of the `Kₙ` is used for exactly one thing: to invoke the third assertion of
Stacks 08DQ. `isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit_of_isPerfect` is the tag in
the source's own form, assuming perfectness and discharging that assertion from it;
`isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit` instead takes the assertion itself as the
hypothesis `hdual` and so does not assume perfectness, which makes it strictly more general —
it applies to a system that is not perfect. Perfectness of an object of `D(O_X)` is the notion
`AlgebraicGeometry.RingedSite.IsPerfect` at the site of opens.

**No existence assumption is carried.** `CategoryTheory.Pretriangulated.IsHomotopyColimit` and
`CategoryTheory.Pretriangulated.IsDerivedLimit` mention `⊕ Kₙ` and `∏` of the system in their
very types, so each takes a `Limits.HasCoproduct` or `Limits.HasProduct` instance argument, and
the site-level statements of Stacks 0A0A carry all three as hypotheses of their own. They are not
hypotheses of the source: a derived category of modules has all direct sums and all products.
Here they are discharged by instance search, from the two unconditional instances of Stacks 07D9
for the derived category of a Grothendieck abelian category,
`Stacks.Injectives.hasCoproducts_derivedCategory` and
`Stacks.Injectives.hasProducts_derivedCategory`, together with the Grothendieck abelianness of
sheaves of modules on a site, `Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`. Nothing
new is proved for this; the module
`StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts` is imported for those
instances, and that import alone removes the three binders.

Two things have to hold for them to be found, and both do. The systems are `abbrev`s rather than
`def`s, so instance search sees that their values are objects of `D(O_X)` rather than stopping at
an opaque constant. And the instances are stated with the abelian category as a bare argument,
`HasProducts (DerivedCategory A)`, so that `A` is determined by first-order matching; an instance
whose subject were `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)` for a variable
ringed site `X` could not be applied at all, instance search not unfolding
`Stacks.SheafOfModules.Tensor.ringSheaf X.O` to expose `X`.

## What this file does not contain

Nothing of the tag is missing. Every input the source's proof uses is proved: the direct sum
comparison `RSheafHom(⊕ Kₙ, E) ≅ ∏ RSheafHom(Kₙ, E)`
(`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison`), the whole comparison of
triangles, the existence of the direct sums and products the statement speaks of, and the
rewriting of the right-hand side.

That last one used to be the gap. **The third assertion of Stacks 08DQ**, that the canonical map
`E ⊗^L_{O_X} Kₙ^∨ ⟶ RSheafHom(Kₙ, E)` of Stacks 08I1 is an isomorphism for a perfect source, was
the one open input of the source's proof and is now proved unconditionally as
`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect`
(`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom`), from perfectness
alone.  Consequently the tag is available in the Stacks Project's own form, with the system of
`Kₙ` assumed perfect and nothing else assumed, as
`isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit_of_isPerfect` below;
`isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit` is kept as the more general statement,
which takes that assertion as a hypothesis and so applies to a system that is not perfect.

This docstring previously recorded the local invertibility as missing, and pointed at the
"What this file does not contain" section of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals` for a module-level morphism the
library does not define.  That route is not the one that closed it: see the "How it is proved"
section of `PerfectDualTensorHom` and the four steps in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionPerfect`.

What *is* still missing is not an input of the tag but a non-degenerate instance of it. The
hypothesis `hperf` of `isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit_of_isPerfect` is
satisfiable at this universe only by the zero object, through
`AlgebraicGeometry.RingedSite.isPerfect_of_isZero` off `CategoryTheory.Limits.isZero_zero`, so
every instance of the tag that can presently be formed is one in which the `Kₙ` vanish. The
reason is the one recorded under "*Non-vacuity*" in the section "The registration is
unconditional, and the hypothesis is inhabited" of `PerfectDualTensorHom`: at
the ringed-*site* spelling `AlgebraicGeometry.RingedSite.IsPerfect` of Stacks 08G5, the
local-models criteria (`isPerfect_of_forall_coveringFamily_strictlyPerfect`,
`isPerfect_of_locally`) both ask for a local model that is already strictly perfect and the
closure rules all consume a perfect object, so none of them bootstraps a nonzero one at the `u`
of this file. The obstruction is not a universe pin to `SheafOfModules.{0}`: each criterion is stated at `RingedSite.{u, u, w}`, so
each applies at the `u` of this file and still supplies nothing, the obstruction being the
absence of a base case rather than a universe. The statement that would fix it, and which
nothing in the library proves, is

```
theorem _ {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) … :
    (ringedSite Rc).IsPerfect (RingedSite.derivedStructureSheaf (ringedSite Rc))
```

i.e. perfectness of `O_X` in degree zero at that spelling and that universe. It is a statement
about Stacks 08G5, not about this tag; nothing below is conditional on it, and the theorems here
are no weaker for its absence.

## References

* [Stacks Project, Tag 0DJI](https://stacks.math.columbia.edu/tag/0DJI)
* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 090Z](https://stacks.math.columbia.edu/tag/090Z)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The inverse system `n ↦ RSheafHom(Kₙ, E)` attached to a system `F : ℕ ⥤ D(O_X)` of objects
of `D(O_X)` and an object `E` of `D(O_X)`. -/
abbrev derivedSheafHomSystem (F : ℕ ⥤ DerivedCategory (StructureSheafModules Rc))
    (E : DerivedCategory (StructureSheafModules Rc)) :
    ℕᵒᵖ ⥤ DerivedCategory (StructureSheafModules Rc) :=
  RingedSite.derivedSheafHomSystem (ringedSite Rc) F E

/-- **Derived internal Hom out of a derived colimit is the derived limit of the derived internal
Homs out of the terms**: if `K = hocolim Kₙ` then
`RSheafHom(K, E) = R lim RSheafHom(Kₙ, E)`.

This is the formal half of Stacks 0DJI, and holds unconditionally, for an arbitrary system of
objects of `D(O_X)`: `hK` is its only hypothesis, no perfectness is involved, and neither the
direct sum nor the product is assumed to exist. One input is the exactness of `RSheafHom(-, E)`
in its contravariant variable, which makes it carry the triangle `⊕ Kₙ → ⊕ Kₙ → K → (⊕ Kₙ)⟦1⟧`
defining the derived colimit to a distinguished triangle; the other is the direct sum comparison
`RSheafHom(⊕ Kₙ, E) ≅ ∏ RSheafHom(Kₙ, E)` of
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison`, which turns the middle
morphism of that triangle into the difference morphism of the system `n ↦ RSheafHom(Kₙ, E)`. -/
theorem isDerivedLimit_derivedSheafHom_of_isHomotopyColimit
    (F : ℕ ⥤ DerivedCategory (StructureSheafModules Rc))
    (E : DerivedCategory (StructureSheafModules Rc))
    {K : DerivedCategory (StructureSheafModules Rc)} (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (derivedSheafHomSystem Rc F E)
      (((derivedSheafHom Rc).flip.obj E).obj (op K)) :=
  RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit' (ringedSite Rc) F E hK

variable
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The inverse system `n ↦ E ⊗^L_{O_X} Kₙ^∨` attached to a system `F : ℕ ⥤ D(O_X)` of objects of
`D(O_X)` and an object `E` of `D(O_X)`: the opposite system followed by the derived dual and by
the derived tensor product with `E`. -/
abbrev tensorDerivedDualSystem (F : ℕ ⥤ DerivedCategory (StructureSheafModules Rc))
    (E : DerivedCategory (StructureSheafModules Rc)) :
    ℕᵒᵖ ⥤ DerivedCategory (StructureSheafModules Rc) :=
  RingedSite.tensorDerivedDualSystem (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) F E

/-- **The derived internal hom out of a homotopy colimit, as a derived limit of tensor duals.**
Let `(X, O_X)` be a ringed space, let `(Kₙ)` be a system of objects of `D(O_X)`, let
`K = hocolim Kₙ` be the derived colimit of Stacks 090Z, and let `E` be an object of `D(O_X)`
such that the canonical map `E ⊗^L_{O_X} Kₙ^∨ ⟶ RSheafHom(Kₙ, E)` of Stacks 08I1 is an
isomorphism for every `n`. Then

`RSheafHom(K, E) = R lim (E ⊗^L_{O_X} Kₙ^∨)`.

Under that condition the tensor-dual system is isomorphic to the system
`n ↦ RSheafHom(Kₙ, E)`, so the assertion is
`Stacks.SheafOfModules.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit` transported along
that isomorphism.  For perfect `Kₙ` this is
`isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit_of_isPerfect`, Stacks 0DJI. -/
theorem isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit
    (F : ℕ ⥤ DerivedCategory (StructureSheafModules Rc))
    (E : DerivedCategory (StructureSheafModules Rc))
    (hdual : ∀ n : ℕ, IsIso (derivedTensorDualToSheafHom Rc (F.obj n) E))
    {K : DerivedCategory (StructureSheafModules Rc)} (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (tensorDerivedDualSystem Rc F E)
      (((derivedSheafHom Rc).flip.obj E).obj (op K)) :=
  RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit' (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) F E hdual hK

/-- **Stacks 0DJI.** Let `(X, O_X)` be a ringed space, let `(Kₙ)` be a system of **perfect**
objects of `D(O_X)` and let `K = hocolim Kₙ`. Then for every object `E` of `D(O_X)`

`RSheafHom(K, E) = R lim (E ⊗^L_{O_X} Kₙ^∨)`.

The source uses the perfectness of the `Kₙ` to invoke the third assertion of Stacks 08DQ, which
is `isIso_derivedTensorDualToSheafHom_of_isPerfect`. -/
@[stacks 0DJI "the whole tag: for a system of perfect objects `Kₙ` of `D(O_X)` with \
`K = hocolim Kₙ` and every `E` in `D(O_X)`, the identity `RSheafHom(K, E) = R lim (E ⊗^L_{O_X} \
Kₙ^∨)`"]
theorem isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit_of_isPerfect
    (F : ℕ ⥤ DerivedCategory (StructureSheafModules Rc))
    (E : DerivedCategory (StructureSheafModules Rc))
    (hperf : ∀ n : ℕ, (ringedSite Rc).IsPerfect (F.obj n))
    {K : DerivedCategory (StructureSheafModules Rc)} (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (tensorDerivedDualSystem Rc F E)
      (((derivedSheafHom Rc).flip.obj E).obj (op K)) :=
  isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit Rc F E
    (fun n ↦ isIso_derivedTensorDualToSheafHom_of_isPerfect Rc (F.obj n) E (hperf n)) hK

end Stacks.SheafOfModules

end
