module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCongr
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestriction
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTensor
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence

/-!
# The integer twists of a coherent triple by an invertible coherent triple

Let `A` be a local ring and `f ∈ A`, let `(F, F₀, α)` be a coherent triple for `(A, f)` and let
`(L, L₀, λ)` be an invertible one. For every integer `n` the triple

`(F ⊗ L^{⊗ n}, F₀ ⊗ L₀^{⊗ n}, α ⊗ λ^{⊗ n})`

is again a coherent triple, and these are the twists whose Euler characteristics
[Stacks, Tag 0F27] asserts to be given by a polynomial. Unlike the iterated tensor product
`Stacks.Algebraization.CoherentTriple.twistPow`, which is indexed by the natural numbers, this
family is indexed by all of `ℤ`, which is the indexing the discrete-calculus step of Tag 0F27
requires.

## Main definitions

* `Stacks.Algebraization.tensorPowScheme`: the integer tensor powers of an invertible
  `𝒪_X`-module, at the spelling in which the comparisons valid in every integer degree are
  stated.
* `Stacks.Algebraization.IsInvertibleTriple.alphaPow`: the `n`-th tensor power of the
  identification of an invertible coherent triple.
* `Stacks.Algebraization.CoherentTriple.twistZ`: the twist of a coherent triple by the `n`-th
  tensor power of an invertible coherent triple, for `n : ℤ`.

## Main results

* `Stacks.Algebraization.pullbackTensorPowSchemeIso`: the inverse image of a tensor power is the
  tensor power of the inverse image, in every integer degree.
* `Stacks.Algebraization.tensorPowSchemeCongr`: isomorphic invertible modules have isomorphic
  tensor powers, in every integer degree.
* `Stacks.Algebraization.isInvertibleTriple_twistZ`: every twist of an invertible coherent triple
  by an invertible coherent triple is invertible.

## Implementation notes

`Stacks.Algebraization.tensorPowScheme` is not a fourth construction of the tensor powers: it is
`Stacks.SheafOfModules.TensorPower.tensorPower` — the family carrying the Tag 01CU attribute, the
image of `𝒪_X` under the `n`-th power of the autoequivalence "tensor on the right by `L`" — with
its hypothesis supplied from `Stacks.Ample.IsInvertibleModule` by
`Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule`. It is an
`abbrev` for the same reason `Stacks.RelativeVeryAmple.tensorModules` is one, namely so that the
two spellings unify when isomorphisms are composed. Its comparison with the ampleness theory's
`Stacks.Ample.tensorPowModule` is
`Stacks.AlgebraicGeometry.PowerFamilyBridge.tensorPowerIsoTensorPow`.

That spelling is chosen for the two comparisons this file needs, both of which have to hold in
*every* integer degree, since the discrete-calculus step of Tag 0F27 constrains the function at
every integer. For `Stacks.SheafOfModules.TensorPower.tensorPower` they are
`Stacks.SheafOfModules.TensorPower.mapTensorPowerIso`, which transports tensor powers along any
functor carrying a tensor comparison and an identification of the structure sheaves, and
`Stacks.SheafOfModules.TensorPower.tensorPowerCongr`; both are single constructions valid in all
degrees at once. The ampleness theory's family has them too, but in two pieces: the nonnegative
degrees are `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` and `tensorPowModuleIsoOfIso`,
proved by induction, and the negative ones are
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso` and
`tensorPowModuleIsoOfIsoInt`, deduced from the nonnegative case and the uniqueness of a tensor
inverse. Either family would do; this one is used because `mapTensorPowerIso` gives the
inverse-image comparison for free from Tag 01CD, with no case split on the sign of the degree.

The tensor comparison for the inverse image is [Stacks, Tag 01CD] in the form
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso`, and the identification of the structure
sheaves is `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`.

Invertibility of the inverse image of an invertible module is [Stacks, Tag 0B8L], which instance
search does not reach through the definition `AlgebraicGeometry.Scheme.Modules.pullback`; it is
taken from the existing restatement at that spelling,
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.isInvertibleModule_schemeModulesPullback`,
rather than restated here.

The three conditions on the punctured-spectrum member of the twist — coherence,
`f`-torsion-freeness, and the identification — are the ones already established for a tensor
product with an invertible module in
`StacksFrontier/AlgebraicGeometry/Algebraization/CoherentTripleTensor.lean`; only the `n`-th power
of the identification is new here.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Algebraization

/-! ### The integer tensor powers, at the spelling with all-degree comparisons -/

/-- **The integer tensor powers of an invertible `𝒪_X`-module**, [Stacks, Tag 01CU], read as a
family `ℤ → X.Modules`. This is `Stacks.SheafOfModules.TensorPower.tensorPower` with its
hypothesis supplied from `Stacks.Ample.IsInvertibleModule`; it is the spelling in which the
comparisons valid in every integer degree are stated. Deliberately an `abbrev`. -/
@[ega "0 5.4.4", ega "III 7.9.14" "partial"]
public noncomputable abbrev tensorPowScheme (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) : X.Modules :=
  letI := isEquivalence_tensorRightFunctor_of_isInvertibleModule X L
  Stacks.SheafOfModules.TensorPower.tensorPower X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n

/-- **Every integer tensor power of an invertible `𝒪_X`-module is invertible.** -/
public theorem isInvertibleModule_tensorPowScheme (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) :
    Stacks.Ample.IsInvertibleModule X (tensorPowScheme X L n) := by
  let := isEquivalence_tensorRightFunctor_of_isInvertibleModule X L
  have hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 ‹_›
  exact (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower X.presheaf _ L n)

/-- **Isomorphic invertible `𝒪_X`-modules have isomorphic tensor powers, in every integer
degree.** -/
public noncomputable def tensorPowSchemeCongr (X : Scheme.{u}) {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L']
    (e : L ≅ L') (n : ℤ) : tensorPowScheme X L n ≅ tensorPowScheme X L' n :=
  letI := isEquivalence_tensorRightFunctor_of_isInvertibleModule X L
  letI := isEquivalence_tensorRightFunctor_of_isInvertibleModule X L'
  Stacks.SheafOfModules.TensorPower.tensorPowerCongr X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) e n

/-- **The inverse image of a tensor power is the tensor power of the inverse image, in every
integer degree.** The tensor comparison is [Stacks, Tag 01CD] and the identification of the
structure sheaves is `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`. -/
public noncomputable def pullbackTensorPowSchemeIso {X S : Scheme.{u}} (g : X ⟶ S)
    (L : S.Modules) [Stacks.Ample.IsInvertibleModule S L]
    [Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback g).obj L)] (n : ℤ) :
    (Scheme.Modules.pullback g).obj (tensorPowScheme S L n) ≅
      tensorPowScheme X ((Scheme.Modules.pullback g).obj L) n :=
  letI := isEquivalence_tensorRightFunctor_of_isInvertibleModule S L
  letI := isEquivalence_tensorRightFunctor_of_isInvertibleModule X
    ((Scheme.Modules.pullback g).obj L)
  Stacks.SheafOfModules.TensorPower.mapTensorPowerIso S.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf S) X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
    (Scheme.Modules.pullback g) L
    (fun M => pullbackTensorModulesIso g M L)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g) n

/-! ### The tensor powers of the identification of an invertible triple -/

/-- **The `n`-th tensor power of the identification of an invertible coherent triple.** It
identifies, over the punctured closed fibre, the inverse image of the `n`-th tensor power of the
member on the punctured spectrum with the inverse image of the `n`-th tensor power of the member
on the closed fibre, for every integer `n`. -/
public noncomputable def IsInvertibleTriple.alphaPow {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {L : CoherentTriple A f} (hL : IsInvertibleTriple L) (n : ℤ) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    (Scheme.Modules.pullback
          (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A))).obj
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n) ≅
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj
        (tensorPowScheme (closedFibre A f) L.F₀ n) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  pullbackTensorPowSchemeIso
      (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A)) L.F n ≪≫
    tensorPowSchemeCongr (puncturedClosedFibre A f).toScheme L.alpha n ≪≫
    (pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ n).symm

/-! ### The integer twists of a coherent triple -/

/-- **The twist of a coherent triple by the `n`-th tensor power of an invertible coherent
triple**, for `n : ℤ`. Its members are the tensor products of the members of the triple with the
`n`-th tensor powers of the members of the invertible triple, and its identification over the
punctured closed fibre is the tensor product of the two identifications, the second taken in its
`n`-th tensor power.

This is the family whose Euler characteristics [Stacks, Tag 0F27] asserts to be given by a
polynomial. -/
@[stacks 0F27 "the integer twists of a coherent triple by an invertible coherent triple"]
public noncomputable def CoherentTriple.twistZ {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) (n : ℤ) : CoherentTriple A f :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  letI := isInvertibleModule_tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n
  letI := isInvertibleModule_tensorPowScheme (closedFibre A f) L.F₀ n
  { F := tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme T.F
      (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)
    F₀ := tensorModules (closedFibre A f) T.F₀ (tensorPowScheme (closedFibre A f) L.F₀ n)
    coherent_F :=
      have : _root_.SheafOfModules.IsCoherent T.F := T.coherent_F
      AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible _ T.F _
    coherent_F₀ :=
      have : _root_.SheafOfModules.IsCoherent T.F₀ := T.coherent_F₀
      AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible _ T.F₀ _
    torsionFree := isFTorsionFree_tensorModules A f T.F _ T.torsionFree
    alpha :=
      pullbackTensorModulesIso
          (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A)) T.F _ ≪≫
        tensorModulesMapIso (puncturedClosedFibre A f).toScheme T.alpha (hL.alphaPow n) ≪≫
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ _).symm }

/-- The tensor product of an invertible module with an integer tensor power of one is invertible. -/
private theorem isInvertibleModule_tensorModules_tensorPowScheme (X : Scheme.{u})
    (T L : X.Modules) [Stacks.Ample.IsInvertibleModule X T]
    [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) :
    Stacks.Ample.IsInvertibleModule X (tensorModules X T (tensorPowScheme X L n)) :=
  have := isInvertibleModule_tensorPowScheme X L n
  isInvertibleModule_tensorModules _ T _

/-- **Every integer twist of an invertible coherent triple by an invertible coherent triple is
invertible.** -/
public theorem isInvertibleTriple_twistZ {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {T L : CoherentTriple A f} (hT : IsInvertibleTriple T) (hL : IsInvertibleTriple L) (n : ℤ) :
    IsInvertibleTriple (T.twistZ L hL n) where
  invertible_F :=
    have := hT.invertible_F
    have := hL.invertible_F
    isInvertibleModule_tensorModules_tensorPowScheme _ T.F L.F n
  invertible_F₀ :=
    have := hT.invertible_F₀
    have := hL.invertible_F₀
    isInvertibleModule_tensorModules_tensorPowScheme _ T.F₀ L.F₀ n

end Stacks.Algebraization

end
