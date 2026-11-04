module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace

/-!
# Tor amplitude tested on the quasi-coherent modules alone

Tor amplitude in `[a, b]` for an object `E` of `D(O_X)`, Stacks 08CG, is a condition on the
derived tensor product of `E` with *every* `O_X`-module. For `X` a quasi-separated scheme and `E`
an object of `D_QCoh(O_X)`, Stacks 08EA says that the quasi-coherent modules already detect it:
the two conditions

1. `E` has Tor amplitude in `[a, b]`, and
2. `H^i(E ⊗^L_{O_X} F) = 0` for `i ∉ [a, b]` and every quasi-coherent `O_X`-module `F`

are equivalent. This file introduces condition (2) as a predicate and proves the implication
(1) ⟹ (2), which needs neither quasi-separatedness, nor `a ≤ b`, nor quasi-coherence of the
cohomology sheaves of `E`: it is the specialisation of the quantifier in (1) to the
quasi-coherent test modules, and holds on an arbitrary ringed space.

## Main results

* `Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent` is condition (2): the
  cohomology sheaves of `E ⊗^L_{O_X} F[0]` vanish outside `[a, b]` for every quasi-coherent
  `O_X`-module `F`.
* `Stacks.Cohomology.TorAmplitude.hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude` is the
  implication (1) ⟹ (2) of Stacks 08EA.
* `Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent.of_iso`: condition (2) depends
  only on the isomorphism class of `E`.

## Implementation notes

Both conditions are read against the *same* derived tensor product, namely the pinned
`Stacks.Cohomology.TorAmplitude.derTensor`, the canonical derived tensor product of Stacks 06YU
at the site of opens of `X`; and condition (1) is
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, which is stated against that same datum. This
is what makes the equivalence of Stacks 08EA a statement with content. The tree carries a second
Tor-amplitude predicate, `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`'s
`HasTorAmplitudeIn`, which takes the derived tensor product as a parameter; for the
first-projection certificate that predicate degenerates to the vanishing of the cohomology
sheaves of the object itself, so stating condition (1) at it would make (1) and (2) say the same
thing for a degenerate reason. That spelling is therefore not used here.

Condition (2) quantifies over `F : OXMod X` carrying `SheafOfModules.IsQuasicoherent`, rather
than over the objects of the full subcategory of quasi-coherent modules. The derived tensor
product is a bifunctor on `D(O_X)`, so a test object has to be an `O_X`-module in any case, and
the subcategory spelling would only add the inclusion functor to every application.

The derived category of `O_X`-modules is the one supplied by the ambient
`HasDerivedCategory` instance, with its hom universe left free. No use is made of the
locally-small model: condition (1) is `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, whose
`HasDerivedCategory` argument is the same instance that condition (2) is read at, so the two
conditions are statements about one derived category.

### Where the converse is

The converse, (2) ⟹ (1), is the substance of the lemma. It is
`AlgebraicGeometry.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent` in
`StacksFrontier/AlgebraicGeometry/Perfect/TorAmplitudeQuasiCoherentTestsGlobal.lean`, and the
equivalence of Stacks 08EA is
`AlgebraicGeometry.hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent` there.

Its proof restricts to an affine open `U = Spec A` of `X`, uses quasi-separatedness of `X` to
make `j_*` along `j : U → X` preserve quasi-coherence (Stacks 01LC) and hence
`QCoh(O_X) → QCoh(O_U)` essentially surjective, identifies `E|_U` with a complex of `A`-modules
(Stacks 06Z0), and concludes by the affine criterion (Stacks 08E9).

## References

* [Stacks Project, Lemma 36.10.6 (Tag 08EA)](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 20.48.5 (Tag 08E9)](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open StrictlyPerfect

namespace Stacks.Cohomology.TorAmplitude

universe u d

/-- `HasDerivedCategory` at the spelling the Tag 06YU development is stated at. The type is
`OXMod X` by `rfl`, but an instance proved at one spelling does not fire at the other. -/
local instance hasDerivedCategoryModulesQCoh (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u} X)] :
    HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) :=
  inferInstanceAs (HasDerivedCategory.{d} (OXMod.{u} X))

/-- **Condition (2) of Tag 08EA.** An object of `D(O_X)` satisfies this when its derived tensor
product with every *quasi-coherent* `O_X`-module, placed in degree `0`, has vanishing cohomology
in every degree outside `[a, b]`.

This is `Stacks.Cohomology.TorAmplitude.HasTorAmplitude` with the test modules cut down from all
`O_X`-modules to the quasi-coherent ones, read against the same derived tensor product
`Stacks.Cohomology.TorAmplitude.derTensor`. It is therefore implied by Tor amplitude in `[a, b]`
on any ringed space; that the two agree for `E` in `D_QCoh(O_X)` and `X` a quasi-separated
scheme is Tag 08EA. -/
def HasTorAmplitudeOnQuasicoherent (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u} X)] (E : DerivedCategory (OXMod.{u} X)) (a b : ℤ) : Prop :=
  ∀ F : OXMod.{u} X, F.IsQuasicoherent → ∀ i : ℤ, i ∉ Set.Icc a b →
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u} X) i).obj
      (((derTensor X).tensor.obj E).obj
        ((DerivedCategory.singleFunctor (OXMod.{u} X) 0).obj F)))

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]

/-- **Tag 08EA, (1) implies (2).** If an object of `D(O_X)` has Tor amplitude in `[a, b]`, then
its derived tensor product with every quasi-coherent `O_X`-module has vanishing cohomology
outside `[a, b]`.

The source calls this clear, and it is: both conditions are read against the same derived tensor
product, so this is the specialisation of the quantifier of Tag 08CG to the quasi-coherent test
modules. In particular neither quasi-separatedness of `X`, nor `a ≤ b`, nor quasi-coherence of
the cohomology sheaves of `E` is used, and `X` need only be a ringed space. -/
theorem hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude
    (E : DerivedCategory (OXMod.{u} X)) (a b : ℤ) (hE : HasTorAmplitude X E a b) :
    HasTorAmplitudeOnQuasicoherent X E a b :=
  fun F _ i hi => hE F i hi

/-- Condition (2) of Tag 08EA depends only on the isomorphism class of the object: the derived
tensor product and the cohomology functors are functorial in it. -/
theorem HasTorAmplitudeOnQuasicoherent.of_iso {E E' : DerivedCategory (OXMod.{u} X)} {a b : ℤ}
    (h : HasTorAmplitudeOnQuasicoherent X E a b) (e : E' ≅ E) :
    HasTorAmplitudeOnQuasicoherent X E' a b := fun F hF i hi =>
  (h F hF i hi).of_iso ((DerivedCategory.homologyFunctor (OXMod.{u} X) i).mapIso
    (((derTensor X).tensor.mapIso e).app
      ((DerivedCategory.singleFunctor (OXMod.{u} X) 0).obj F)))

end Stacks.Cohomology.TorAmplitude

end
