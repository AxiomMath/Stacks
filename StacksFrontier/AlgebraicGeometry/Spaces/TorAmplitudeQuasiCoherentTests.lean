module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude on an algebraic space tested on the quasi-coherent modules alone

Tor amplitude in `[a, b]` for an object `E` of `D(𝒪_X)` on a ringed site, [Stacks, Tag 08FZ], is
a condition on the derived tensor product of `E` with *every* `𝒪_X`-module. For `X` a
quasi-separated algebraic space, `E` an object of `D_QCoh(𝒪_X)` and `a ≤ b`, [Stacks, Tag 08IL]
says that the quasi-coherent modules already detect it: the two conditions

1. `E` has Tor amplitude in `[a, b]`, and
2. `Hⁱ(E ⊗^L_{𝒪_X} ℱ) = 0` for `i ∉ [a, b]` and every quasi-coherent `𝒪_X`-module `ℱ`

are equivalent. Here `𝒪_X`-modules are the sheaves of modules on the small étale ringed site of
`X` and quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, as in the category `QCoh(𝒪_X)`
of [Stacks, Tag 03G9]. This file introduces condition (2) as a predicate and proves the
implication (1) ⟹ (2), which holds on an arbitrary algebraic space, for every `a` and `b` and
every object `E` of `D(𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.Space.HasTorAmplitudeOnQuasicoherent` is condition (2): the cohomology
  sheaves of `E ⊗^L_{𝒪_X} ℱ[0]` vanish outside `[a, b]` for every quasi-coherent
  `𝒪_X`-module `ℱ`.

## Main results

* `AlgebraicGeometry.Space.hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude` is the
  implication (1) ⟹ (2).
* `AlgebraicGeometry.Space.HasTorAmplitudeOnQuasicoherent.of_iso` and
  `AlgebraicGeometry.Space.HasTorAmplitudeOnQuasicoherent.mono`: condition (2) depends only on
  the isomorphism class of `E`, and holds in every larger interval.

## Implementation notes

Both conditions are read against the same derived tensor product, a term
`T : Stacks.SheafOfModules.DerivedTensorProduct` on the small étale ringed site of `X`.
Condition (1) is `Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude`, read on the small
étale site.

Condition (2) quantifies over `ℱ : AlgebraicGeometry.Space.Modules` carrying
`SheafOfModules.IsQuasicoherentOnSite`, rather than over the objects of the full subcategory
`AlgebraicGeometry.Space.QuasicoherentSheaves`.

The module universe is the universe `u` of the structure rings.

## References

* [Stacks Project, Lemma 75.13.8 (Tag 08IL)](https://stacks.math.columbia.edu/tag/08IL)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules (DerivedTensorProduct)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
  [HasDerivedCategory.{d} (Modules.{u, u} B S hS F hF)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS F hF).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS F hF).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u} B S hS F hF) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS F hF).O)
      (ComplexShape.up ℤ)]

/-- An object `E` of `D(𝒪_X)` on an algebraic space `X` satisfies this when its derived tensor
product `T` with every *quasi-coherent* `𝒪_X`-module, placed in degree `0`, has vanishing
cohomology in every degree outside `[a, b]`. This is condition (2) of [Stacks, Tag 08IL]. -/
def HasTorAmplitudeOnQuasicoherent
    (T : DerivedTensorProduct.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF))
    (E : RingedSite.DerivedModules.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF))
    (a b : ℤ) : Prop :=
  ∀ M : Modules.{u, u} B S hS F hF, M.IsQuasicoherentOnSite → ∀ i : ℤ, i ∉ Set.Icc a b →
    IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj
      ((T.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj M)))

/-- If an object of `D(𝒪_X)` on an algebraic space `X` has Tor amplitude in `[a, b]`, then its
derived tensor product with every quasi-coherent `𝒪_X`-module has vanishing cohomology outside
`[a, b]`. -/
@[stacks 08IL "(1) implies (2)"]
theorem hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude
    (T : DerivedTensorProduct.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF))
    (E : RingedSite.DerivedModules.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF))
    (a b : ℤ)
    (hE : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude T E a b) :
    HasTorAmplitudeOnQuasicoherent B S hS hF T E a b :=
  fun M _ i hi => hE M i hi

variable {B S hS hF}

/-- `HasTorAmplitudeOnQuasicoherent` depends only on the isomorphism class of the object. -/
theorem HasTorAmplitudeOnQuasicoherent.of_iso
    {T : DerivedTensorProduct.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF)}
    {E E' : RingedSite.DerivedModules.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF)}
    {a b : ℤ} (h : HasTorAmplitudeOnQuasicoherent B S hS hF T E a b) (e : E' ≅ E) :
    HasTorAmplitudeOnQuasicoherent B S hS hF T E' a b := fun M hM i hi =>
  (h M hM i hi).of_iso
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).mapIso
      ((T.tensor.mapIso e).app
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS F hF) 0).obj M)))

/-- `HasTorAmplitudeOnQuasicoherent` in an interval implies it in every larger interval. -/
theorem HasTorAmplitudeOnQuasicoherent.mono
    {T : DerivedTensorProduct.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF)}
    {E : RingedSite.DerivedModules.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF)}
    {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    (h : HasTorAmplitudeOnQuasicoherent B S hS hF T E a b) :
    HasTorAmplitudeOnQuasicoherent B S hS hF T E a' b' := fun M hM i hi =>
  h M hM i (by simp only [Set.mem_Icc, not_and_or, not_le] at hi ⊢; omega)

end AlgebraicGeometry.Space

end
