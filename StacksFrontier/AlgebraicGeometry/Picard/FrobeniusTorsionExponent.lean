module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion

/-!
# The Frobenius formula on a Picard group, and torsion under a purely inseparable extension

`StacksFrontier/AlgebraicGeometry/Picard/FrobeniusTorsion.lean` proves that prime-to-`p` torsion in
the Picard group is unchanged by a base change of fields `k'/k` in which the `p ^ m`-th power of
every element of `k'` lies in `k`, for a bound `m` supplied with the extension. That proof rests
on the Frobenius formula: pullback along the absolute Frobenius is multiplication by `p` on the
Picard group of every scheme in characteristic `p`
(`Stacks.Picard.schemePullbackClass_absoluteFrobenius`, proved on first cohomology of the sheaf
of units in `StacksFrontier/AlgebraicGeometry/Picard/FrobeniusPicardClass.lean`), hence by `p ^ m`
along its `m`-fold iterate (`Stacks.Picard.schemePullbackClass_absoluteFrobeniusPow_eq_zsmul`).

This file takes the bound from the extension. Mathlib's `IsPurelyInseparable.HasExponent`
asserts exactly that such a bound exists, with `IsPurelyInseparable.exponent` the least one, and
it holds for every finite purely inseparable extension
(`IsPurelyInseparable.hasExponent_of_finiteDimensional`).

The file also records the module-theoretic form of the Frobenius formula: pullback along an
endomorphism `f` of a ringed space is multiplication by `n` on the Picard group as soon as `f^*L`
is isomorphic to `L ^ ⊗ n` for every invertible `L`
(`Stacks.Picard.pullbackClass_eq_zsmul_of_pullback_iso_tensorPower`), the class of an `n`-th
tensor power being `n` times the class (`Stacks.Picard.classOf_tensorPower`). The proof of the
Frobenius formula above does not go through it.

## Main results

* `Stacks.Picard.classOf_tensorPower` — the class of the `n`-th tensor power of an invertible
  sheaf of modules is `n` times its class.
* `Stacks.Picard.pullbackClass_eq_zsmul_of_pullback_iso_tensorPower`,
  `Stacks.Picard.schemePullbackClass_eq_zsmul_of_pullback_iso_tensorPower` — an endomorphism
  whose pullback is the `n`-th tensor power on invertible sheaves acts as multiplication by `n`
  on the Picard group.
* `Stacks.Picard.pullbackClass_unit_iso_tensorPower_unit` — the trivial sheaf satisfies that
  isomorphism, for every endomorphism and every exponent.
* `Stacks.Picard.bijOn_schemePullbackClass_zsmulTorsion_of_hasExponent` — prime-to-`p` torsion
  is unchanged by a base change of fields of finite exponent, for an arbitrary scheme over the
  base field.

## Implementation notes

No `@[stacks]` attribute is attached. Stacks Tag 0CD5 asserts the bijection of
`bijOn_schemePullbackClass_zsmulTorsion_of_hasExponent` for an arbitrary purely inseparable
extension, which need not have an exponent (the perfect closure of `𝔽_p(t)` has none). Its
statement under the tag's own hypotheses is
`Stacks.Picard.bijOn_schemePullbackClass_zsmulTorsion_of_isPurelyInseparable` in
`StacksFrontier/AlgebraicGeometry/Picard/TorsionBaseChange.lean`, which reduces to the theorem here
through the finite subextensions: that is where quasi-compactness, quasi-separatedness and
`H⁰(X, 𝒪_X) = k` are used. The theorem here needs none of the three.

## References

* [Stacks Project, Tag 0CD5](https://stacks.math.columbia.edu/tag/0CD5)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 03SM](https://stacks.math.columbia.edu/tag/03SM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open Stacks.SheafOfModules (IsInvertible isInvertible_unit isInvertible_tensorSheaf picardClass
  picardClass_zero picardClass_eq_iff picardClass_tensorSheaf
  tensorSheafMapIso tensorLeftFunctorObjUnitIso)

open Stacks.SheafOfModules.TensorPower (tensorPower tensorPowerSuccIso isInvertible_tensorPower
  tensorPowerReindex)

open Stacks.RingedSpace (structureIsSheaf pullbackFunctor modulePullback_isInvertible_of)

open RingedSpaceModuleAdjunction (modulePullbackObjUnitIso)
open Stacks.Frobenius

universe v u w

namespace Stacks.Picard

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The `n`-th tensor power of an invertible sheaf of modules has `n` times its Picard
class.** Addition of Picard classes is tensor product (Tag 01CX) and the tensor power satisfies
`L ^ ⊗ (n + 1) ≅ L ^ ⊗ n ⊗ L` (Tag 01CU), so this is an induction on `n`. -/
theorem classOf_tensorPower (L : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [hL : IsInvertible O hO L] (n : ℕ) :
    picardClass O hO (tensorPower O hO L (n : ℤ)) (isInvertible_tensorPower O hO L (n : ℤ)) =
      (n : ℤ) • picardClass O hO L hL := by
  induction n with
  | zero => exact (picardClass_zero O hO).trans (zero_zsmul _).symm
  | succ n ih =>
      calc picardClass O hO (tensorPower O hO L ((n + 1 : ℕ) : ℤ)) _
          = picardClass O hO
              ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
                  ((tensorPower O hO L (n : ℤ)))).obj (L)))
              (isInvertible_tensorSheaf O hO (tensorPower O hO L (n : ℤ)) L) :=
            ((picardClass_eq_iff O hO _ _ _ _).2
              ⟨tensorPowerSuccIso O hO L (n : ℤ) ≪≫
                tensorPowerReindex O hO L (by push_cast; ring)⟩).symm
        _ = picardClass O hO (tensorPower O hO L (n : ℤ)) _ + picardClass O hO L hL :=
            (picardClass_tensorSheaf O hO _ _ _ _ _).symm
        _ = ((n : ℤ) • picardClass O hO L hL) + picardClass O hO L hL := by rw [ih]
        _ = ((n + 1 : ℕ) : ℤ) • picardClass O hO L hL := by
            rw [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul]

/-- Every tensor power of the trivial sheaf of modules is trivial.

`Stacks.SheafOfModules.Invertible.tensorPowerUnitIso`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFullyFaithful/Basic.lean`) states the
same thing, and cannot be used here: it is about the *other* of the library's two unbridged
tensor-power developments, the one over `AlgebraicGeometry.SheafOfModules.IsInvertible`, whereas
the Picard group of `Stacks.Picard` is built from `Stacks.SheafOfModules.IsInvertible` and
`Stacks.SheafOfModules.TensorPower.tensorPower`. The two `tensorPower`s are different constants
and no bridge lemma identifies them. -/
def tensorPowerUnitIso (n : ℕ) :
    tensorPower O hO (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      O hO)) (n : ℤ) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) := by
  letI : IsInvertible O hO (SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :=
    isInvertible_unit O hO
  induction n with
  | zero => exact Iso.refl _
  | succ n ih =>
      refine (tensorPowerReindex O hO _ (by push_cast; ring)).trans
        ((tensorPowerSuccIso O hO _ (n : ℤ)).symm.trans ?_)
      exact (tensorSheafMapIso O hO ih (Iso.refl _)).trans (tensorLeftFunctorObjUnitIso O hO _)

end Site

section RingedSpace

variable {X : RingedSpace.{u, u}}

/-- The trivial sheaf of modules satisfies the isomorphism
`f^*L ≅ L ^ ⊗ n` of
`Stacks.Picard.pullbackClass_eq_zsmul_of_pullback_iso_tensorPower`, for every endomorphism `f`
of a ringed space and every exponent `n`. This is a satisfiability check on that hypothesis, in
the sense of its degenerate case: pullback carries the trivial sheaf to the trivial sheaf, and
every tensor power of the trivial sheaf is trivial. -/
def pullbackClass_unit_iso_tensorPower_unit (f : X ⟶ X) (n : ℕ) :
    (pullbackFunctor f).obj (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
        (structureIsSheaf X))) ≅
      tensorPower X.presheaf (structureIsSheaf X)
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
          (structureIsSheaf X)))
        (n : ℤ) :=
  (modulePullbackObjUnitIso f).trans (tensorPowerUnitIso X.presheaf (structureIsSheaf X) n).symm

/-- **Pullback along an endomorphism is multiplication by `n` on the Picard group as soon as it
is the `n`-th tensor power on invertible sheaves.** A Picard class is the class of a
representative, pullback is computed on representatives, and the class of an `n`-th tensor power
is `n` times the class. -/
theorem pullbackClass_eq_zsmul_of_pullback_iso_tensorPower (f : X ⟶ X) (n : ℕ)
    (h : ∀ (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      X.presheaf (structureIsSheaf X)))
      (_ : IsInvertible X.presheaf (structureIsSheaf X) L),
      Nonempty ((pullbackFunctor f).obj L ≅
        tensorPower X.presheaf (structureIsSheaf X) L (n : ℤ)))
    (x : ofRingedSpace X) : pullbackClass f x = (n : ℤ) • x := by
  have hrep : IsInvertible X.presheaf (structureIsSheaf X) (picardRepresentative X x).obj :=
    (picardRepresentative X x).property
  rw [← classOf_picardRepresentative X x,
    pullbackClass_classOf f (picardRepresentative X x).obj hrep,
    (picardClass_eq_iff X.presheaf (structureIsSheaf X) _ _
        (modulePullback_isInvertible_of f _ hrep)
        (isInvertible_tensorPower X.presheaf (structureIsSheaf X) _ (n : ℤ))).2
      (h (picardRepresentative X x).obj hrep),
    classOf_tensorPower]

end RingedSpace

section Schemes

/-- `Stacks.Picard.pullbackClass_eq_zsmul_of_pullback_iso_tensorPower` for an endomorphism of a
scheme. -/
theorem schemePullbackClass_eq_zsmul_of_pullback_iso_tensorPower {X : Scheme.{u}} (f : X ⟶ X)
    (n : ℕ)
    (h : ∀ (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      X.toRingedSpace.presheaf
        (structureIsSheaf X.toRingedSpace)))
      (_ : IsInvertible X.toRingedSpace.presheaf (structureIsSheaf X.toRingedSpace) L),
      Nonempty ((pullbackFunctor f.toLRSHom.toShHom).obj L ≅
        tensorPower X.toRingedSpace.presheaf (structureIsSheaf X.toRingedSpace) L (n : ℤ)))
    (x : ofScheme X) : schemePullbackClass f x = (n : ℤ) • x :=
  pullbackClass_eq_zsmul_of_pullback_iso_tensorPower f.toLRSHom.toShHom n h x

/-- **Prime-to-`p` torsion in the Picard group is unchanged by a base change of fields of finite
exponent.**

Let `k'/k` be an extension of fields of characteristic `p` admitting an exponent in the sense of
Mathlib's `IsPurelyInseparable.HasExponent`, that is, one for which some `p ^ e`-th power map
lands in `k`. Then for any `k`-scheme `X` and any integer `n` prime to `p`, pullback along
`X_{k'} → X` is a bijection from the `n`-torsion of `Pic X` onto the `n`-torsion of
`Pic X_{k'}`.

This is `Stacks.Picard.bijOn_schemePullbackClass_zsmulTorsion_of_pow_mem_range` with the exponent
taken from the extension. -/
theorem bijOn_schemePullbackClass_zsmulTorsion_of_hasExponent
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsPurelyInseparable.HasExponent k k']
    (p : ℕ) [Fact p.Prime] [CharP k p] {n : ℤ} (hn : n.natAbs.Coprime p)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    Set.BijOn
      (schemePullbackClass (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))))
      {x : ofScheme X | n • x = 0}
      {y : ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) | n • y = 0} := by
  have hk : IsInCharacteristic (Spec (CommRingCat.of k)) p :=
    isInCharacteristic_spec k p (CharP.cast_eq_zero k p)
  have : ExpChar k p := .prime Fact.out
  exact bijOn_schemePullbackClass_zsmulTorsion_of_pow_mem_range k k' p
    (IsPurelyInseparable.exponent k k')
    (fun x => IsPurelyInseparable.exponent_def' k p x) hn f hk

end Schemes

end Stacks.Picard

end
