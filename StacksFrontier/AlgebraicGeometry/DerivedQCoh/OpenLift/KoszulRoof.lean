module

public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulDerivedSystemPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.DerivedTensorDatumBridge
import StacksCore.Tactic.StacksAttribute

/-!
# The roof of a lifted map of complexes on an affine scheme

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`,
let `X = Spec A` and let `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`.  Let `Iₑ` be the stages of the derived
Koszul system `Koszul.DerivedSystem.koszulDerivedSystem`, with their canonical maps
`ιₑ : Iₑ ⟶ 𝒪_X`, which become isomorphisms after restriction to `U`.

[Stacks, Tag 08EH] lifts a map `α : E|_U ⟶ E'|_U` of objects of `D_QCoh(𝒪_X)`, with `E` perfect,
to a *roof*

`E ⟵ E₁ ⟶ E'`

whose left leg restricts to an isomorphism on `U`, and its last sentence says that `E₁` may be
taken to be `E ⊗^L_{𝒪_X} I` for a perfect complex `I` on `X`.  The complex the source produces
is `I = Iₑ` for a large enough `e`, so `E₁ = Iₑ ⊗^L_{𝒪_X} E`; the right leg is obtained from the
tensor--internal-Hom bijection of [Stacks, Tag 08DI] out of a map `ξ : Iₑ ⟶ RSheafHom(E, E')`.

This file builds that object and that leg, and proves the object perfect.  What it does **not**
contain is the existence of `ξ`, which is [Stacks, Tag 08DD] -- the statement that the comparison
map `Koszul.DerivedSystem.cohomologyComparison` of [Stacks, Tag 08DC] is an isomorphism -- at the
object `RSheafHom(E, E')`.  Nothing here carries the attribute of Tag 08EH: the existence
statement of that tag is not proved, and the left leg of the roof is not constructed either, for
the reason recorded below.

## Main definitions

* `Koszul.DerivedSystem.koszulRoof`: the object `Iₑ ⊗^L_{𝒪_X} E` of `D(𝒪_X)`, the `E₁` of
  [Stacks, Tag 08EH].
* `Koszul.DerivedSystem.koszulRoofToTarget`: the right leg `Iₑ ⊗^L_{𝒪_X} E ⟶ E'` of the roof
  attached to a map `ξ : Iₑ ⟶ RSheafHom(E, E')`, namely its image under the
  tensor--internal-Hom bijection of [Stacks, Tag 08DI].

## Main results

* `Koszul.DerivedSystem.isPerfect_koszulRoof`: **the last sentence of [Stacks, Tag 08EH], object
  half.**  For `E` perfect the object `Iₑ ⊗^L_{𝒪_X} E` is perfect, every stage of the Koszul
  system being perfect.
* `Koszul.DerivedSystem.isPerfect_koszulRoof_two_stages`: the same statement with every binder
  instantiated -- the ring `ℤ`, the sequence `(2)`, and for `E` another stage of the Koszul
  system -- so that it depends on no hypothesis at all.

## What is missing, and why

The left leg of the roof is `ιₑ ⊗ 𝟙_E` followed by the unit isomorphism
`𝒪_X ⊗^L_{𝒪_X} E ≅ E`.  No unit isomorphism for
`Stacks.SheafOfModules.derivedTensor` is available -- the unitors the library has belong to other
derived tensor products (the scheme-level one of
`AlgebraicGeometry.PseudoCoherent.derivedTensorUnitLeftIso`, and the localized monoidal structure
of `Stacks.Cohomology.MonoidalDerived`) and no comparison with this one exists -- so the leg
cannot be written down here, and the statement that it restricts to an isomorphism on `U`, which
needs restriction to an open to commute with the derived tensor product *naturally* (the library
has `Stacks.Cohomology.RestrictionTensor.derivedTensorRestrictIsoOfKFlat` on objects only),
cannot be stated either.

## References

* [Stacks Project, Lemma 36.13.7 (Tag 08EH)](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Proposition 36.9.5 (Tag 08DD)](https://stacks.math.columbia.edu/tag/08DD)
* [Stacks Project, Tag 08DC](https://stacks.math.columbia.edu/tag/08DC)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Lemma 20.46.6 (Tag 09J5)](https://stacks.math.columbia.edu/tag/09J5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules

universe u

namespace Koszul.DerivedSystem

attribute [local instance] HasDerivedCategory.standard

variable {A : CommRingCat.{u}} {r : ℕ}

/-- The object `E₁ = Iₑ ⊗^L_{𝒪_X} E` of [Stacks, Tag 08EH]: the derived tensor product of the
stage `Iₑ` of the Koszul system with `E`. -/
public def koszulRoof (f : Fin r → A) (e : ℕ) (E : derivedCat A) : derivedCat A :=
  ((derivedTensor (Spec A).sheaf).obj ((koszulDerivedSystem f).obj (op e))).obj E

/-- **The last sentence of [Stacks, Tag 08EH], object half.**  For a perfect object `E` of
`D(𝒪_X)` the roof object `Iₑ ⊗^L_{𝒪_X} E` is perfect: the stages of the Koszul system are
perfect objects of `D(𝒪_X)`, and the derived tensor product of two perfect objects is perfect by
[Stacks, Tag 09J5]. -/
public theorem isPerfect_koszulRoof (f : Fin r → A) (e : ℕ) (E : derivedCat A)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec A).toRingedSpace) E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec A).toRingedSpace) (koszulRoof f e E) :=
  AlgebraicGeometry.RingedSpace.isPerfect_derivedTensor (Spec A).toRingedSpace _ E
    (isPerfect_koszulDerivedSystem_obj f e) hE

/-- The right leg of the roof of [Stacks, Tag 08EH].  A map `ξ : Iₑ ⟶ RSheafHom(E, E')`
corresponds, under the tensor--internal-Hom bijection of [Stacks, Tag 08DI], to a map
`Iₑ ⊗^L_{𝒪_X} E ⟶ E'`, which is the leg `γ` of the roof. -/
public def koszulRoofToTarget (f : Fin r → A) (e : ℕ) (E E' : derivedCat A)
    (ξ : (koszulDerivedSystem f).obj (op e) ⟶
      ((derivedSheafHom (Spec A).sheaf).obj (op E)).obj E') :
    koszulRoof f e E ⟶ E' :=
  derivedSheafHomTensorEquiv (Spec A).sheaf _ E E' ξ

/-- **A positive non-vacuity test for `isPerfect_koszulRoof`.**  Every binder is instantiated
from declarations that assume nothing: the ring is `ℤ`, the sequence is the one-term sequence
`(2)`, and the coefficient object is another stage of the same Koszul system, whose perfectness
is `Koszul.DerivedSystem.isPerfect_koszulDerivedSystem_obj`. -/
public theorem isPerfect_koszulRoof_two_stages :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec (CommRingCat.of ℤ)).toRingedSpace)
      (koszulRoof (A := CommRingCat.of ℤ) (fun _ : Fin 1 ↦ (2 : ℤ)) 1
        ((koszulDerivedSystem (fun _ : Fin 1 ↦ (2 : ℤ))).obj (op 0))) :=
  isPerfect_koszulRoof _ _ _ (isPerfect_koszulDerivedSystem_obj _ 0)

end Koszul.DerivedSystem

end
