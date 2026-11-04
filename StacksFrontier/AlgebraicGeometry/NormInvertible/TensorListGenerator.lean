module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorPowerGenerator
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorFamily

/-!
# Local generators of the tensor product of a family over a list

Let `X` be a scheme, let `L : ι → 𝒪_X`-Mod be a family of sheaves of modules and let `U` be an
open of `X`. A section `s ∈ M(U)` *generates* `M` on `U` when multiplication by `s` is a bijection
`𝒪_X(V) → M(V)` for every `V ≤ U` (`Stacks.SheafOfModules.GeneratorSections`). This file carries
such sections through the iterated tensor product
`Stacks.SheafOfModules.schemeTensorList X L l = ⨂_{i ∈ l} L i` of a list of the family: a
generator of every factor on `U` gives a generator of the product on `U`, and the transition unit
of two of them is the product over the list of the transition units of the factors.

## Main definitions

* `Stacks.SheafOfModules.tensorListGenerator`: the generator of `⨂_{i ∈ l} L i` on `U` given by
  a generator of each factor on `U`.

## Main results

* `Stacks.SheafOfModules.tensorListGenerator_nil` and
  `Stacks.SheafOfModules.tensorListGenerator_cons`: the two recursion equations. The empty list
  gives the generator `1` of the structure sheaf, and consing an index tensors its generator on
  the left, by `Stacks.SheafOfModules.tmulGenerator`.
* `Stacks.SheafOfModules.tensorListGenerator_restrict`: it commutes with restriction.
* `Stacks.SheafOfModules.generatorRatioUnit_tensorListGenerator`: the transition unit of two
  such generators is the product over `l` of the transition units of the factors,
  `[⨂ sᵢ : ⨂ tᵢ] = ∏_{i ∈ l} [sᵢ : tᵢ]`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {ι : Type*} {X : Scheme.{u}}

/-- The generator of the tensor product over a list given by a generator of every factor: the
unit section of the structure sheaf for the empty list, and for `i :: l` the generator of `L i`
tensored onto the left of the generator for `l`. -/
noncomputable def tensorListGenerator (X : Scheme.{u})
    (L : ι → _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {U : Opens X.toRingedSpace.carrier}
    (g : ∀ i, GeneratorSections X.toRingedSpace (L i) U) (l : List ι) :
    GeneratorSections X.toRingedSpace (schemeTensorList X L l) U :=
  l.rec (generatorOfIso _ (Iso.refl _)) fun i _ ih ↦ tmulGenerator (g i) ih

/-- Over the empty list the generator is the one supplied by the identity trivialization of the
structure sheaf, namely the unit section. -/
theorem tensorListGenerator_nil (X : Scheme.{u})
    (L : ι → _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {U : Opens X.toRingedSpace.carrier}
    (g : ∀ i, GeneratorSections X.toRingedSpace (L i) U) :
    tensorListGenerator X L g [] =
      generatorOfIso (X := X.toRingedSpace)
        (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)) (Iso.refl _) :=
  rfl

/-- Consing an index tensors its generator onto the left of the generator of the rest. -/
theorem tensorListGenerator_cons (X : Scheme.{u})
    (L : ι → _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {U : Opens X.toRingedSpace.carrier}
    (g : ∀ i, GeneratorSections X.toRingedSpace (L i) U) (i : ι) (l : List ι) :
    tensorListGenerator X L g (i :: l) =
      tmulGenerator (g i) (tensorListGenerator X L g l) :=
  rfl

/-- The generator of a tensor product over a list commutes with restriction. -/
theorem tensorListGenerator_restrict (X : Scheme.{u})
    (L : ι → _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {U V : Opens X.toRingedSpace.carrier} (h : V ≤ U)
    (g : ∀ i, GeneratorSections X.toRingedSpace (L i) U) (l : List ι) :
    generatorRestrict (schemeTensorList X L l) h (tensorListGenerator X L g l) =
      tensorListGenerator X L (fun i => generatorRestrict (L i) h (g i)) l := by
  induction l with
  | nil => exact generatorOfIso_restrict _ (Iso.refl _) h
  | cons i l ih =>
      exact (tmulGenerator_restrict (g i) (tensorListGenerator X L g l) h).trans
        (congrArg (tmulGenerator _) ih)

/-- The transition unit of two generators of a tensor product over a list is the product over
the list of the transition units of the factors, `[⨂ sᵢ : ⨂ tᵢ] = ∏_{i ∈ l} [sᵢ : tᵢ]`. -/
theorem generatorRatioUnit_tensorListGenerator (X : Scheme.{u})
    (L : ι → _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (U : Opens X.toRingedSpace.carrier)
    (g g' : ∀ i, GeneratorSections X.toRingedSpace (L i) U) (l : List ι) :
    generatorRatioUnit (schemeTensorList X L l) U (tensorListGenerator X L g l)
        (tensorListGenerator X L g' l) =
      (l.map fun i => generatorRatioUnit (L i) U (g i) (g' i)).prod := by
  induction l with
  | nil => exact (generatorRatioUnit_self _ U _).trans List.prod_nil.symm
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons, ← ih]
      exact generatorRatioUnit_tmulGenerator (g i) (g' i) _ _

end Stacks.SheafOfModules

end
