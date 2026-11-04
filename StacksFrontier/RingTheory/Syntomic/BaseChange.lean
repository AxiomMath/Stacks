module

import Mathlib.RingTheory.Finiteness.Descent

public import StacksFrontier.RingTheory.CompleteIntersection.FieldExtension
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent
public import StacksFrontier.RingTheory.Syntomic.Defs

/-!
# Base change of syntomic ring maps

Let `R → S` be a ring map and let `R → R'` be a ring map with `S'` the base change of `S` along it,
so `S' = R' ⊗_R S`. This file proves:

* if `R → S` is syntomic then so is `R' → S'`, for an arbitrary `R → R'`;
* if moreover `R → R'` is faithfully flat, then `R' → S'` is syntomic if and only if `R → S` is,
  so that being syntomic is local on the base for the fpqc topology.

## Main definitions

* `Syntomic.BaseChange.fiberMap`: the comparison map `κ(p) ⊗_R S → κ(p') ⊗_{R'} S'` of fibres, for
  a prime `p'` of `R'` lying over a prime `p` of `R`.

## Main results

* `Syntomic.BaseChange.isPushout_fiber`: the fibre `κ(p') ⊗_{R'} S'` is the base change of the
  fibre `κ(p) ⊗_R S` along `κ(p) → κ(p')`.
* `Algebra.IsPushout.syntomic`: a base change of a syntomic ring map is syntomic.
* `Algebra.IsPushout.syntomic_iff`: being syntomic is fpqc local on the base.

## Implementation notes

The base change is an arbitrary pushout square of rings rather than the chosen model `R' ⊗_R S`:
`Algebra.IsPushout R S R' S'` for `Algebra.IsPushout.syntomic`, the square that
`RingHom.IsStableUnderBaseChange` quantifies over, and its transpose `Algebra.IsPushout R R' S S'`
for `Algebra.IsPushout.syntomic_iff`. The source's `S' = R' ⊗_R S` is `TensorProduct.isPushout`,
once `Algebra.TensorProduct.rightAlgebra` is a local instance for the second orientation.

`Syntomic.BaseChange.fiberAlgebraOfBase` is not a local instance. The restriction of scalars
`Algebra S (p'.Fiber S')` along `S → S'` also applies to the fibre `p.Fiber S = κ(p) ⊗_R S`, where
it would present `R → S → κ(p) ⊗_R S` as the `R`-algebra structure instead of the canonical
`R → κ(p) ⊗_R S`.

## References

* [StacksProject 00SN](https://stacks.math.columbia.edu/tag/00SN), Lemma 10.136.3
* [StacksProject 00SM](https://stacks.math.columbia.edu/tag/00SM), Lemma 10.136.2
* [StacksProject 00SL](https://stacks.math.columbia.edu/tag/00SL), Definition 10.136.1
* [StacksProject 00SJ](https://stacks.math.columbia.edu/tag/00SJ), Lemma 10.135.20
* [StacksProject 00HQ](https://stacks.math.columbia.edu/tag/00HQ), Lemma 10.39.16
* [StacksProject 00HI](https://stacks.math.columbia.edu/tag/00HI), Lemma 10.39.7
* [StacksProject 00F4](https://stacks.math.columbia.edu/tag/00F4), Lemma 10.6.2
-/

@[expose] public section

namespace Syntomic.BaseChange

open TensorProduct

section Ascent

variable (R R' S S' : Type*) [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R R'] [Algebra R S] [Algebra R S'] [Algebra R' S'] [Algebra S S']
  [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R R' S S']

/-- A base change of a flat algebra along an arbitrary pushout square is flat. -/
private theorem flat_of_isPushout [Module.Flat R S] : Module.Flat R' S' :=
  .of_linearEquiv (Algebra.IsPushout.equiv R R' S S').symm.toLinearEquiv

/-- A base change of an algebra of finite presentation along an arbitrary pushout square is of
finite presentation. -/
private theorem finitePresentation_of_isPushout [Algebra.FinitePresentation R S] :
    Algebra.FinitePresentation R' S' :=
  .equiv (Algebra.IsPushout.equiv R R' S S')

end Ascent

section Fiber

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R R' S S' : Type*) [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R R'] [Algebra R S] [Algebra R S'] [Algebra R' S'] [Algebra S S']
  [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R R' S S']
  (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime] [p'.LiesOver p]

attribute [local instance] Ideal.residueFieldAlgebra Ideal.isScalarTower_residueField

/-- The scalar tower `R → S' → κ(p') ⊗_{R'} S'` on the fibre of `R' → S'` at `p'`. -/
public theorem isScalarTower_baseChange_fiber : IsScalarTower R S' (p'.Fiber S') :=
  .to₁₃₄ R R' S' (p'.Fiber S')

attribute [local instance] isScalarTower_baseChange_fiber

/-- The fibre `κ(p') ⊗_{R'} S'` of `R' → S'` at `p'` as an `S`-algebra, by restriction of scalars
along `S → S'`. -/
public noncomputable abbrev fiberAlgebraOfBase : Algebra S (p'.Fiber S') :=
  Algebra.compHom (p'.Fiber S') (algebraMap S S')

/-- The comparison map `κ(p) ⊗_R S → κ(p') ⊗_{R'} S'` of fibres, induced by
`κ(p) → κ(p') → κ(p') ⊗_{R'} S'` and `S → S' → κ(p') ⊗_{R'} S'`. -/
public noncomputable def fiberMap : p.Fiber S →ₐ[R] p'.Fiber S' :=
  Algebra.pushoutDesc _ (IsScalarTower.toAlgHom R p.ResidueField (p'.Fiber S'))
    ((IsScalarTower.toAlgHom R S' (p'.Fiber S')).comp (IsScalarTower.toAlgHom R S S'))
    fun _ _ => mul_comm _ _

omit [Algebra.IsPushout R R' S S'] in
/-- The comparison map of fibres extends the residue field extension `κ(p) → κ(p')`. -/
public theorem fiberMap_algebraMap_residueField (x : p.ResidueField) :
    fiberMap R R' S S' p p' (algebraMap p.ResidueField (p.Fiber S) x) =
      algebraMap p.ResidueField (p'.Fiber S') x :=
  Algebra.pushoutDesc_left _ _ _ _ x

omit [Algebra.IsPushout R R' S S'] in
/-- The comparison map of fibres is compatible with `S → S'`. -/
public theorem fiberMap_algebraMap (x : S) :
    fiberMap R R' S S' p p' (algebraMap S (p.Fiber S) x) =
      algebraMap S' (p'.Fiber S') (algebraMap S S' x) :=
  Algebra.pushoutDesc_right _ _ _ _ x

/-- The fibre at `p'` as an algebra over the fibre at `p`, along the comparison map. -/
public noncomputable abbrev fiberAlgebra : Algebra (p.Fiber S) (p'.Fiber S') :=
  (fiberMap R R' S S' p p').toRingHom.toAlgebra

attribute [local instance] fiberAlgebra

omit [Algebra.IsPushout R R' S S'] in
/-- The comparison map of fibres is a map of `κ(p)`-algebras. -/
public theorem isScalarTower_residueField_fiber :
    IsScalarTower p.ResidueField (p.Fiber S) (p'.Fiber S') :=
  .of_algebraMap_eq fun x => (fiberMap_algebraMap_residueField R R' S S' p p' x).symm

attribute [local instance] isScalarTower_residueField_fiber

omit [Algebra.IsPushout R R' S S'] in
/-- The comparison map of fibres is a map of `S`-algebras. -/
public theorem isScalarTower_base_fiber :
    letI := fiberAlgebraOfBase R' S S' p'
    IsScalarTower S (p.Fiber S) (p'.Fiber S') :=
  let := fiberAlgebraOfBase R' S S' p'
  .of_algebraMap_eq fun x => (fiberMap_algebraMap R R' S S' p p' x).symm

/-- The fibre of a base change is the base change of the fibre: in a pushout square
`S' = R' ⊗_R S`, let `p'` be a prime of `R'` lying over a prime `p` of `R`. Then the fibre
`κ(p') ⊗_{R'} S'` of `R' → S'` at `p'` is the base change of the fibre `κ(p) ⊗_R S` of `R → S` at
`p` along the residue field extension `κ(p) → κ(p')`. -/
public theorem isPushout_fiber :
    Algebra.IsPushout p.ResidueField p'.ResidueField (p.Fiber S) (p'.Fiber S') := by
  let _ : Algebra S (p'.Fiber S') := fiberAlgebraOfBase R' S S' p'
  have : IsScalarTower S S' (p'.Fiber S') := .of_algebraMap_eq' rfl
  have : IsScalarTower R S (p'.Fiber S') := .to₁₂₄ R S S' (p'.Fiber S')
  have : IsScalarTower S (p.Fiber S) (p'.Fiber S') := isScalarTower_base_fiber R R' S S' p p'
  have : IsScalarTower R (p.Fiber S) (p'.Fiber S') :=
    .to₁₃₄ R p.ResidueField (p.Fiber S) (p'.Fiber S')
  exact (Algebra.IsPushout.comp_iff R p.ResidueField S (p.Fiber S)).mp
    ((Algebra.IsPushout.comp_iff R R' S S').mpr inferInstance)

attribute [local instance] isPushout_fiber

/-- The fibre of `R' → S'` at `p'` is a local complete intersection over `κ(p')` if and only if the
fibre of `R → S` at `p` is one over `κ(p)`. -/
private theorem isLocalCompleteIntersection_fiber_iff :
    IsLocalCompleteIntersection p'.ResidueField (p'.Fiber S') ↔
      IsLocalCompleteIntersection p.ResidueField (p.Fiber S) :=
  Algebra.IsPushout.isLocalCompleteIntersection_iff p.ResidueField p'.ResidueField
    (p.Fiber S) (p'.Fiber S')

end Fiber

section Descent

variable (R R' S S' : Type*) [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R R'] [Algebra R S] [Algebra R S'] [Algebra R' S'] [Algebra S S']
  [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R R' S S']

/-- A base change of a syntomic algebra along an arbitrary pushout square
`Algebra.IsPushout R R' S S'` is syntomic. -/
private theorem syntomic_baseChange [Algebra.Syntomic R S] : Algebra.Syntomic R' S' where
  flat := flat_of_isPushout R R' S S'
  finitePresentation := finitePresentation_of_isPushout R R' S S'
  isLocalCompleteIntersection_fiber p' _ :=
    (isLocalCompleteIntersection_fiber_iff R R' S S' (p'.under R) p').mpr
      (Algebra.Syntomic.isLocalCompleteIntersection_fiber (p'.under R))

/-- Descent along a faithfully flat base change: if `R' ⊗_R S` is syntomic over `R'` and `R → R'`
is faithfully flat, then `S` is syntomic over `R`. -/
private theorem syntomic_of_syntomic_baseChange [Module.FaithfullyFlat R R']
    [Algebra.Syntomic R' S'] : Algebra.Syntomic R S :=
  let e : R' ⊗[R] S ≃ₐ[R'] S' := Algebra.IsPushout.equiv R R' S S'
  have : Module.Flat R' (R' ⊗[R] S) := .of_linearEquiv e.toLinearEquiv
  have : Algebra.FinitePresentation R' (R' ⊗[R] S) := .equiv e.symm
  { flat := Module.Flat.of_flat_tensorProduct R S R'
    finitePresentation := .of_finitePresentation_tensorProduct_of_faithfullyFlat R'
    isLocalCompleteIntersection_fiber p _ := by
      obtain ⟨p', _, _⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := R') p
      exact (isLocalCompleteIntersection_fiber_iff R R' S S' p p').mp
        (Algebra.Syntomic.isLocalCompleteIntersection_fiber p') }

end Descent

end Syntomic.BaseChange

/-- Any base change of a syntomic ring map is syntomic: if `R → S` is syntomic and `S'` is the base
change of `S` along an arbitrary ring map `R → R'`, so `S' = S ⊗_R R'`, then `R' → S'` is
syntomic. -/
@[stacks 00SN "The base change is an arbitrary pushout square `Algebra.IsPushout R S R' S'`, the
square `RingHom.IsStableUnderBaseChange` quantifies over and the orientation of Mathlib's
`Algebra.IsPushout.isIntegral`; the source's literal `S' = S ⊗_R R'` is `TensorProduct.isPushout`.
Nothing is assumed about `R → R'`. See the module docstring."]
public theorem Algebra.IsPushout.syntomic (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (R' S' : Type*) [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R S'] [Algebra S S']
    [Algebra R' S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R S R' S'] [Algebra.Syntomic R S] :
    Algebra.Syntomic R' S' :=
  have : Algebra.IsPushout R R' S S' := .symm inferInstance
  Syntomic.BaseChange.syntomic_baseChange R R' S S'

/-- Let `R → S` be a ring map, let `R → R'` be faithfully flat and let `S'` be the base change of
`S` along `R → R'`, so `S' = R' ⊗_R S`. Then `R' → S'` is syntomic if and only if `R → S` is
syntomic. -/
@[stacks 00SM "The base change `S' = R' ⊗_R S` is an arbitrary pushout square
`Algebra.IsPushout R R' S S'`; the source's literal form is `inferInstance` once
`Algebra.TensorProduct.rightAlgebra` is a local instance. Faithful flatness is
`Module.FaithfullyFlat R R'`, the module-level form Mathlib's descent lemmas use. See the module
docstring."]
public theorem Algebra.IsPushout.syntomic_iff (R R' S S' : Type*) [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] [Algebra R R'] [Algebra R S] [Algebra R S'] [Algebra R' S']
    [Algebra S S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R R' S S'] [Module.FaithfullyFlat R R'] :
    Algebra.Syntomic R' S' ↔ Algebra.Syntomic R S :=
  ⟨fun _ => Syntomic.BaseChange.syntomic_of_syntomic_baseChange R R' S S',
    fun _ => Syntomic.BaseChange.syntomic_baseChange R R' S S'⟩

end
