module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude is a bounded flat representative, for the derived tensor product of the site

Stacks 08G1 says that an object `E` of `D(O)` on a ringed site `(C, O)` has Tor amplitude in
`[a, b]`, for `a ≤ b`, exactly when `E` is represented by a complex of flat `O`-modules
vanishing in every degree outside `[a, b]`.

`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_iff_exists_flatRepresentative`
states this against a *given* derived tensor product datum `T`, which keeps the universes of
the site free but leaves the datum to the caller. This file states the same equivalence for
the derived tensor product of the site itself,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` of Stacks 06YU: nothing beyond the
ringed site and the universe of the localization is supplied.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct`
  `.hasTorAmplitude_canonical_iff_exists_flatRepresentative`: **Stacks 08G1** for the derived
  tensor product of the site.

## Implementation notes

The three universes of the site are one here, and that is forced from both sides. The
construction of a derived tensor product, `Stacks.SheafOfModules.exists_derivedTensorProduct`,
puts the morphisms of the site and the sections of its structure sheaf and of its modules in a
single universe — the objects may sit in a universe of their own — because the K-flat
resolutions of Stacks 06YS it rests on do. The direction of Stacks 08G1 which produces the
representative needs the unit law
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso`, hence the monoidal structure on
`Mod(O)`, which is available when the sections live in the join of the two site universes.
Together those two pins leave `C : Type u` with `Category.{u} C` and sections in `u`.

At that single universe the site is small and every piece of sheafification, additivity and
totalisation infrastructure which the general statement carries as a hypothesis is an
instance, so none of it is assumed: only `HasDerivedCategory.{d}`, which names the hom
universe of the localization and is a genuine choice, remains, exactly as in
`Stacks.SheafOfModules.exists_derivedTensorProduct`.

## References

* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, u, u}} [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]

/-- **Stacks 08G1, for the derived tensor product of the site.** An object of `D(O)` has Tor
amplitude in `[a, b]`, measured against the derived tensor product
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` of Stacks 06YU, exactly when some
complex of flat `O`-modules vanishing in every degree outside `[a, b]` represents it.

No derived tensor product datum is assumed: the one the statement speaks of is the one Stacks
06YU constructs. -/
@[stacks 08G1 "for the derived tensor product of the site, with no datum assumed",
  sga "4 XVII 4.1.9" "(i) <=> (iii)", sga "6 I 5.1"]
theorem hasTorAmplitude_canonical_iff_exists_flatRepresentative
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (a b : ℤ) (hab : a ≤ b) :
    letI : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
    letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
    HasTorAmplitude (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X) E a b ↔
      ∃ K : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ,
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
          (O := X.O) (K.X i)) ∧
        (∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K.X i)) ∧
        Nonempty (DerivedCategory.Q.obj K ≅ E) :=
  let : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
  let : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
  hasTorAmplitude_iff_exists_flatRepresentative
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X) E a b hab

end Stacks.SheafOfModules.DerivedTensorProduct

end
