module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorCommShiftTwo
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product on a ringed site exists

Let `(C, O)` be a ringed site. This file proves Stacks 06YU: the derived tensor product of
sheaves of `O`-modules exists, as a bifunctor on the unbounded derived category `D(Mod(O))`
which is exact in each variable and which, together with its canonical natural map to the
ordinary total tensor product and its two one-sided K-flat comparison isomorphisms, is the
data recorded by `Stacks.SheafOfModules.DerivedTensorProduct`.

Every ingredient is proved elsewhere in the `DerivedTensor` modules of this directory:

* the bifunctor, `Stacks.SheafOfModules.derivedTensorBifunctor`, obtained by descending the
  total tensor product of complexes along the K-flat complexes (Stacks 06YS, 07A3, 0GSL) in
  one variable and along all complexes (Stacks 06YP) in the other;
* its comparison with the ordinary total tensor product on a K-flat factor, with naturality in
  both variables, `Stacks.SheafOfModules.kFlatComparison_naturality`;
* the canonical map `Stacks.SheafOfModules.toTensor` of Stacks 0FPH, its independence of the
  chosen resolution in the strong form `toTensor_comp_of_kFlat`, its naturality, and that it
  is invertible as soon as either factor is K-flat;
* the two-variable shift coherence of Stacks 079U,
  `Stacks.SheafOfModules.derivedTensorBifunctor_commShift₂Int`, and exactness in each variable
  **at the commutation with the shift that coherence carries**,
  `derivedTensorBifunctor_isTriangulated_obj` and `derivedTensorBifunctor_isTriangulated_flipObj`,
  from Stacks 06YM.

## Main results

* `Stacks.SheafOfModules.exists_derivedTensorProduct`: the derived tensor product exists.

## Main definitions

* `Stacks.SheafOfModules.canonicalDerivedTensorProduct`: the one built by
  `Stacks.SheafOfModules.derivedTensorProductOfExact`, opaque to the kernel (`irreducible_def`).
* `Stacks.SheafOfModules.derivedTensorProductFunctor`: its bifunctor, for clients.

## Implementation notes

**The objects of the site live in an arbitrary universe `c`, independent of the universe `u`
of its morphisms and of the sections of its structure sheaf and its modules.**  That is the
configuration of every small étale site — the small étale site of an algebraic space is an
`AlgebraicGeometry.RingedSite.{u + 1, u, u}` — and it is not the configuration the K-flat
machinery was originally available at.  What changed is the resolution: Stacks 06YS is taken
here in the form `Stacks.SheafOfModules.exists_kFlat_quasiIso`, which now resolves by *flat
modules supplied by a flat cover* rather than by the direct sums of extensions by zero
`j_{U!}O_U` of Stacks 077J.  The 077J ladder passes through a sheafification comparison, Stacks
03EV part (2), which pins the ring universe to the morphism universe of the site, and indexes
its cover by a type in `max c u`, which asks for colimits of that size in `Mod(O)`; the flat
cover does neither.  Nothing else in the chain — Stacks 06YM, 06YP, 06YQ, 07A3, 0GSL, and the
localization theory they feed — ever related the three universes.

The universe of the localization stays independent of all three, as `HasDerivedCategory.{d}`.

Two hypotheses are *not* discharged here and are carried by the statement, because at `c ≠ u`
they are not instances: sheafification and local bijectivity for `AddCommGrpCat.{u}` on a site
whose objects sit in `c`.  On an essentially `u`-small site, which is what a small étale site
is, Mathlib's `hasSheafifyEssentiallySmallSite` and
`GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` supply them.

**Why `canonicalDerivedTensorProduct` is an `irreducible_def`.**  The kernel ignores
reducibility attributes, and it compares arguments first only for applications of one constant
with regular reducibility hints.  Derived tensor objects are reached through `abbrev`s such as
`derivedTensorProductFunctor` and through structure projections such as `Functor.obj`, so with a
transparent body every kernel check between two spellings of such an object evaluates the
construction down to tensor products of modules: the kernel check of
`Stacks.Cohomology.DerivedInternalHomPullback.tensorHomBijection_homComplexComparison` took
45–49 s with a transparent body and 9–10 s with an opaque one.  An opaque body keeps the
construction itself available through `canonicalDerivedTensorProduct_def`, which a
`Classical.choice` body would not.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)

## Relation to the `Stacks.DerivedTensor.RingedSite` registration of 06YU

`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/ExistenceOnARingedSite.lean` carries
`@[stacks 06YU "existence and characterization"]` on a statement for a site with `C : Type u`,
`[SmallCategory.{u} C]` and a structure sheaf in `CommRingCat.{u}` — all four universes one `u`.
Tag 06YU itself relates none of them.  That registration is left exactly as it stands, together
with its development and its consumers; the statement below is the faithful one stated
beside it, with the object universe of the site free, and it carries the tag with a comment
string naming that shape.

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))]

/-- **Stacks 06YU.** The derived tensor product of sheaves of modules on a ringed site exists,
with its canonical natural map to the ordinary total tensor product, its one-sided K-flat
comparisons, and exactness in both variables.

The objects of the site form a type in an arbitrary universe `c`, while its morphisms, the
sections of its structure sheaf and the sections of its modules lie in one universe `u`; the
derived category's hom universe `d` is independent of both.  That is the configuration of a
small étale site, whose objects sit one universe above its morphisms. -/
@[stacks 06YU "existence, for a site whose objects form a type in an arbitrary universe while \
its morphisms, structure sheaf and modules lie in one universe"]
theorem exists_derivedTensorProduct :
    Nonempty (DerivedTensorProduct.{c, u, u, d} X) :=
  nonempty_derivedTensorProduct_of_exact X inferInstance (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance)

/-- The canonical derived tensor product of sheaves of modules on a ringed site, with its
natural map to the ordinary total tensor product, K-flat comparisons, and exactness in both
variables.  The objects of the site live in a universe of their own.

It is the construction `Stacks.SheafOfModules.derivedTensorProductOfExact`, made opaque with
`irreducible_def`; `canonicalDerivedTensorProduct_def` is the defining equation. -/
@[stacks 06YU "the derived tensor product, at a site whose objects form a type in an arbitrary \
universe while its morphisms, structure sheaf and modules lie in one universe"]
irreducible_def canonicalDerivedTensorProduct : DerivedTensorProduct.{c, u, u, d} X :=
  derivedTensorProductOfExact X inferInstance (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance)

/-- The canonical derived tensor product is the one built on
`Stacks.SheafOfModules.derivedTensorBifunctor` with the two-variable shift coherence
`Stacks.SheafOfModules.derivedTensorBifunctor_commShift₂Int`. -/
theorem canonicalDerivedTensorProduct_eq :
    canonicalDerivedTensorProduct.{c, u, d} X =
      derivedTensorProductOfExact X inferInstance (fun _ ↦ inferInstance)
        (fun _ ↦ inferInstance) :=
  canonicalDerivedTensorProduct_def X

/-- The bifunctor of the canonical derived tensor product is
`Stacks.SheafOfModules.derivedTensorBifunctor`. -/
theorem canonicalDerivedTensorProduct_tensor :
    (canonicalDerivedTensorProduct.{c, u, d} X).tensor = derivedTensorBifunctor X :=
  congrArg DerivedTensorProduct.tensor (canonicalDerivedTensorProduct_def X)

/-- The derived tensor bifunctor on the unbounded derived category of `X`. -/
abbrev derivedTensorProductFunctor :=
  (canonicalDerivedTensorProduct.{c, u, d} X).tensor

end Stacks.SheafOfModules

end
