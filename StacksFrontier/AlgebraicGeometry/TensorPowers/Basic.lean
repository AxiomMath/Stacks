module

public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowers.Monoidal
public import StacksFrontier.Topology.Sheaves.Modules.Invertible

/-!
# Tensor powers of an invertible sheaf of modules

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` and `L` an invertible sheaf of
`𝒪`-modules in the sense of `AlgebraicGeometry.SheafOfModules.IsInvertible`. This file defines
the integer tensor powers `L ^⊗ n` for `n : ℤ`, proves the addition law
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)`, identifies the zeroth power with the structure sheaf and the
first with `L`, and proves that **every** integer tensor power is again invertible. The
negative powers are the powers of the inverse of `L`, and the inverse of `L` is identified with
its dual, the internal hom into the structure sheaf.

This is Stacks Tag 01CU. The abstract construction lives in
`StacksFrontier/AlgebraicGeometry/TensorPowers/Monoidal.lean`; this file is the instantiation at
sheaves of modules, where the monoidal structure is
`Stacks.SheafInternalHom.monoidalCategory` and invertibility is the library's `IsInvertible`.

Along the way clauses (1) and (2) of Stacks Tag 01CT fall out: a tensor product of invertible
sheaves of modules is invertible, and so is the inverse of one.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.tensorInverse`: a chosen two-sided tensor inverse of an
  invertible sheaf of modules, extracted from the `Prop`-valued `IsInvertible` through the
  universal property.
* `AlgebraicGeometry.SheafOfModules.tensorInv`: the inverse sheaf of modules itself.
* `AlgebraicGeometry.SheafOfModules.tensorPow`: **the `n`-th tensor power**, for `n : ℤ`.
* `AlgebraicGeometry.SheafOfModules.unitIso` and
  `AlgebraicGeometry.SheafOfModules.tensorIso`: the monoidal unit and tensor product of
  `SheafOfModules` are `SheafOfModules.unit` and `Stacks.SheafOfModules.Tensor.sheafTensor`.
* `AlgebraicGeometry.SheafOfModules.tensorLeftFunctorIso`: the canonical tensor bifunctor
  `Stacks.SheafOfModules.Tensor.sheafTensor` at a left factor `L` is the monoidal
  `MonoidalCategory.tensorLeft L`.

## Main results

* `AlgebraicGeometry.SheafOfModules.isInvertible_iff_isEquivalence_tensorLeft`: the library's
  `IsInvertible` is exactly invertibility for the monoidal structure on `SheafOfModules`, i.e.
  `MonoidalCategory.tensorLeft L` being an equivalence. This is the bridge that lets the
  abstract file be used, and it is the only place where the canonical tensor functor
  `(Stacks.SheafOfModules.Tensor.sheafTensor _).obj L` is compared with `tensorLeft L`.
* `AlgebraicGeometry.SheafOfModules.tensorPowAddIso` and
  `AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf`: **the addition law**, in the monoidal
  spelling and in the `Stacks.SheafOfModules.Tensor.sheafTensor` spelling. The second needs no
  monoidal instance in its statement and is the one for consumers to use.
* `AlgebraicGeometry.SheafOfModules.isInvertible_tensorPow`: **every tensor power of an
  invertible sheaf of modules is invertible**, as an instance.
* `AlgebraicGeometry.SheafOfModules.tensorPowZeroIso`,
  `AlgebraicGeometry.SheafOfModules.tensorPowOneIso`,
  `AlgebraicGeometry.SheafOfModules.tensorPowNegOneIso`: the zeroth power is the structure
  sheaf, the first is `L`, the `(-1)`-st is the inverse.
* `AlgebraicGeometry.SheafOfModules.tensorPowMulNegIso`: `L ^⊗ n ⊗ L ^⊗ (-n) ≅ 𝒪`, so the
  inverse of the `n`-th power is the `(-n)`-th power.
* `AlgebraicGeometry.SheafOfModules.tensorPow_natCast` and
  `AlgebraicGeometry.SheafOfModules.tensorPow_neg_natCast_succ`: Stacks Tag 01CU's explicit
  formula — in nonnegative degree an iterated tensor product of `L`, in negative degree an
  iterated tensor product of the inverse — holds by `rfl`.
* `AlgebraicGeometry.SheafOfModules.tensorInvIsoIhomUnit` and
  `AlgebraicGeometry.SheafOfModules.tensorPowNegOneIsoIhomUnit`: **the inverse is the dual.**
  The right adjoint of `tensorLeft L` is both `MonoidalClosed.ihom L` and the inverse
  equivalence, and right adjoints are unique, so `L ^⊗ (-1) ≅ SheafHom(L, 𝒪)`.
* `AlgebraicGeometry.SheafOfModules.isInvertible_tensor` and
  `AlgebraicGeometry.SheafOfModules.isInvertible_tensorInv`: clauses (1) and (2) of Stacks
  Tag 01CT.

## Implementation notes

**Transparency and local instances.** `Stacks.SheafInternalHom.monoidalCategory`,
`braidedCategory` and `monoidalClosed` are deliberately `def`s in the sibling file, so that on
a site with chosen finite products they cannot collide with a second monoidal structure. They
are therefore brought in here with `attribute [local instance]`, confined to the two sections
that need them. A consequence that consumers must know: any statement of this file mentioning
`⊗` or `𝟙_` needs those local instances in scope to elaborate. The statements that do **not**
are `tensorPow` itself, `tensorPow_natCast`, `isInvertible_tensorPow` and
`tensorPowAddIsoSheaf`, which is why the last is provided in the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling alongside the monoidal one.

`Stacks.SheafInternalHom.tensorLeftIso` identifies the monoidal `tensorLeft L` with the
canonical tensor functor `(Stacks.SheafOfModules.Tensor.sheafTensor _).obj L`, and
`tensorLeftFunctorIso` is that comparison read in the other direction. Transporting
`IsEquivalence` across the iso needs a declaration whose *statement* spells the functor
canonically, which is what `tensorLeftFunctorIso` is. No compiler option is set anywhere in
this file.

**Universes.** The main section is polymorphic in the site universes `u v` and the module
universe `w` independently, exactly as `IsInvertible` and the monoidal structure are. The
`Dual` section is not: it needs `C : Type u`, `[SmallCategory C]` and
`𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}`, inherited verbatim from
`Stacks.SheafInternalHom.monoidalClosed`, which applies the special adjoint functor theorem at
the universe of the module sections. The identification of the inverse with the dual is the
only result subject to that constraint; the tensor powers and the addition law are not. This is
no real restriction for the geometric case, `Opens X` being a `SmallCategory`.

**Everything is at the sheaf level.** No result is moved between the presheaf and sheaf levels.
`MonoidalCategory.tensorLeft L` for a *presheaf* `L` being an equivalence and the sheaf-level
`IsInvertible` are different hypotheses, and the sheaf one does not imply the presheaf one, the
presheaf tensor product of two sheaves not being a sheaf; so `Stacks.InternalHom.dualIso` and
the rest of the presheaf-level dual API are not used here, and `tensorInvIsoIhomUnit` is proved
afresh from uniqueness of right adjoints at the sheaf level.

## What is not done

The commutativity and associativity constraints on the addition isomorphisms are not proved;
Stacks Tag 01CU asserts them with the formulation explicitly omitted. See the sibling file's
"What is not done" for why they are not formal consequences of `tensorPowAddIso`. Consequently
the graded ring `Γ_*(X, L) = ⨁ Γ(X, L ^⊗ n)` of Stacks Tag 01CV is not constructed, and neither
is the pullback compatibility of Stacks Tag 0B8L.

No normalisation of `tensorPowAddIso` against `tensorPowSuccIso` is proved: the expected
`tensorPowAddIso L n 1 = tensorPowSuccIso` modulo `tensorPowOneIso` is true of the construction
but is not recorded, since the recursion is on the second exponent and the identity needs the
unitors of the sheaf monoidal structure to be computed.

Nothing is stated in Mathlib's `AlgebraicGeometry.Scheme.Modules` spelling. The bridge exists —
`Stacks.SheafInternalHom.structureSheaf_eq_ringCatSheaf` and `schemeMonoidalCategory` — but
`IsInvertible`, which is the vocabulary this repository's consumers use, is stated over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`, so restating the powers over
  `X.Modules` would duplicate rather
than add.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

universe v u w

open CategoryTheory MonoidalCategory Limits Stacks.SheafOfModules.TensorSheafification
  Stacks.TensorPowers

namespace AlgebraicGeometry.SheafOfModules

section Powers

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory
attribute [local implicit_reducible] structureSheaf

/-- The monoidal unit of `SheafOfModules` is the structure sheaf. -/
noncomputable def unitIso :
    𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ≅
      _root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪) :=
  (Stacks.SheafInternalHom.sheafifyCounitIso 𝒪 h𝒪).app
    (_root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪))

/-- The monoidal tensor product of `SheafOfModules` is
`Stacks.SheafOfModules.Tensor.sheafTensor`. -/
noncomputable def tensorIso (F G : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    F ⊗ G ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
        (F)).obj (G)) :=
  (Stacks.SheafInternalHom.tensorLeftIso 𝒪 h𝒪 F).app G

/-- The canonical sheafified tensor functor `(Stacks.SheafOfModules.Tensor.sheafTensor _).obj L`
is the monoidal `tensorLeft L`. -/
noncomputable def tensorLeftFunctorIso
    (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj L ≅
      tensorLeft (C := _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) L :=
  (Stacks.SheafInternalHom.tensorLeftIso 𝒪 h𝒪 L).symm

/-- Invertibility of a sheaf of modules is invertibility for the monoidal structure. -/
theorem isInvertible_iff_isEquivalence_tensorLeft
    (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    IsInvertible 𝒪 h𝒪 L ↔ (tensorLeft L).IsEquivalence :=
  (isInvertible_iff_tensorLeftFunctor_isEquivalence 𝒪 h𝒪 L).trans
    (Functor.isEquivalence_iff_of_iso (tensorLeftFunctorIso 𝒪 h𝒪 L))

variable (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-- A chosen two-sided tensor inverse of an invertible sheaf of modules. -/
noncomputable def tensorInverse [h : IsInvertible 𝒪 h𝒪 L] : TensorInverse L :=
  let := (isInvertible_iff_isEquivalence_tensorLeft 𝒪 h𝒪 L).mp h
  tensorInverseOfTensorLeft L

/-- The inverse of an invertible sheaf of modules. -/
noncomputable abbrev tensorInv [IsInvertible 𝒪 h𝒪 L] :
    _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪) :=
  (tensorInverse 𝒪 h𝒪 L).inv

/-- The `n`-th tensor power of an invertible sheaf of modules. -/
noncomputable def tensorPow [IsInvertible 𝒪 h𝒪 L] (n : ℤ) :
    _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪) :=
  intTensorPow L (tensorInv 𝒪 h𝒪 L) n

/-- The zeroth tensor power is the monoidal unit, definitionally. -/
theorem tensorPow_zero [IsInvertible 𝒪 h𝒪 L] :
    tensorPow 𝒪 h𝒪 L 0 = 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) := rfl

/-- For `n ≥ 0` the `n`-th tensor power is the `n`-fold tensor product of `L`, as Stacks Tag
01CU's explicit formula says. -/
theorem tensorPow_natCast [IsInvertible 𝒪 h𝒪 L] (n : ℕ) :
    tensorPow 𝒪 h𝒪 L (n : ℤ) = natTensorPow L n := rfl

/-- For `n < 0` the `n`-th tensor power is the `|n|`-fold tensor product of the inverse of `L`,
as Stacks Tag 01CU's explicit formula says. -/
theorem tensorPow_neg_natCast_succ [IsInvertible 𝒪 h𝒪 L] (n : ℕ) :
    tensorPow 𝒪 h𝒪 L (-((n : ℤ) + 1)) = natTensorPow (tensorInv 𝒪 h𝒪 L) (n + 1) := rfl

/-- `L ^⊗ 0` is the structure sheaf. -/
noncomputable def tensorPowZeroIso [IsInvertible 𝒪 h𝒪 L] :
    tensorPow 𝒪 h𝒪 L 0 ≅ _root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪) :=
  unitIso 𝒪 h𝒪

/-- `L ^⊗ 1` is `L`. -/
noncomputable def tensorPowOneIso [IsInvertible 𝒪 h𝒪 L] : tensorPow 𝒪 h𝒪 L 1 ≅ L :=
  oneIso L _

/-- `L ^⊗ (-1)` is the inverse of `L`. -/
noncomputable def tensorPowNegOneIso [IsInvertible 𝒪 h𝒪 L] :
    tensorPow 𝒪 h𝒪 L (-1) ≅ tensorInv 𝒪 h𝒪 L :=
  negOneIso L _

/-- `L ^⊗ (n+1) ≅ L ^⊗ n ⊗ L`. -/
noncomputable def tensorPowSuccIso [IsInvertible 𝒪 h𝒪 L] (n : ℤ) :
    tensorPow 𝒪 h𝒪 L (n + 1) ≅ tensorPow 𝒪 h𝒪 L n ⊗ L :=
  (tensorInverse 𝒪 h𝒪 L).succIso n

/-- `L ^⊗ (n-1) ≅ L ^⊗ n ⊗ L ^⊗ (-1)`. -/
noncomputable def tensorPowPredIso [IsInvertible 𝒪 h𝒪 L] (n : ℤ) :
    tensorPow 𝒪 h𝒪 L (n - 1) ≅ tensorPow 𝒪 h𝒪 L n ⊗ tensorInv 𝒪 h𝒪 L :=
  (tensorInverse 𝒪 h𝒪 L).predIso n

/-- **The addition law.** -/
noncomputable def tensorPowAddIso [IsInvertible 𝒪 h𝒪 L] (n m : ℤ) :
    tensorPow 𝒪 h𝒪 L n ⊗ tensorPow 𝒪 h𝒪 L m ≅ tensorPow 𝒪 h𝒪 L (n + m) :=
  (tensorInverse 𝒪 h𝒪 L).addIso n m

/-- The addition law in the `Stacks.SheafOfModules.Tensor.sheafTensor` spelling. -/
noncomputable def tensorPowAddIsoSheaf [IsInvertible 𝒪 h𝒪 L] (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
        ((tensorPow 𝒪 h𝒪 L n))).obj ((tensorPow 𝒪 h𝒪 L m))) ≅
      tensorPow 𝒪 h𝒪 L (n + m) :=
  (tensorIso 𝒪 h𝒪 _ _).symm ≪≫ tensorPowAddIso 𝒪 h𝒪 L n m

/-- **Every tensor power of an invertible sheaf of modules is invertible.** -/
instance isInvertible_tensorPow [IsInvertible 𝒪 h𝒪 L] (n : ℤ) :
    IsInvertible 𝒪 h𝒪 (tensorPow 𝒪 h𝒪 L n) :=
  (isInvertible_iff_isEquivalence_tensorLeft 𝒪 h𝒪 _).mpr
    ((tensorInverse 𝒪 h𝒪 L).tensorInversePow n).isEquivalence_tensorLeft

/-- The evaluation isomorphism `L ⊗ L⁻¹ ≅ 𝒪` for the chosen inverse. With
`tensorInvIsoIhomUnit` this is the evaluation map of clause (2) of Stacks Tag 01CT. -/
noncomputable def tensorInvMulIso [IsInvertible 𝒪 h𝒪 L] :
    L ⊗ tensorInv 𝒪 h𝒪 L ≅ 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :=
  (tensorInverse 𝒪 h𝒪 L).mulIso

/-- `L ^⊗ n ⊗ L ^⊗ (-n) ≅ 𝒪`: the inverse of the `n`-th power is the `(-n)`-th power. -/
noncomputable def tensorPowMulNegIso [IsInvertible 𝒪 h𝒪 L] (n : ℤ) :
    tensorPow 𝒪 h𝒪 L n ⊗ tensorPow 𝒪 h𝒪 L (-n) ≅
      𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :=
  ((tensorInverse 𝒪 h𝒪 L).tensorInversePow n).mulIso

/-- The inverse of an invertible sheaf of modules is invertible. This is clause (2) of Stacks
Tag 01CT, stated for the chosen inverse; see `tensorInvIsoIhomUnit` for its identification with
the internal hom into the structure sheaf. -/
instance isInvertible_tensorInv [IsInvertible 𝒪 h𝒪 L] : IsInvertible 𝒪 h𝒪 (tensorInv 𝒪 h𝒪 L) :=
  (isInvertible_iff_isEquivalence_tensorLeft 𝒪 h𝒪 _).mpr
    (TensorInverse.isEquivalence_tensorLeft
      { inv := L
        mulIso := (tensorInverse 𝒪 h𝒪 L).mulIso'
        mulIso' := (tensorInverse 𝒪 h𝒪 L).mulIso })

/-- A tensor product of invertible sheaves of modules is invertible. This is clause (1) of
Stacks Tag 01CT. -/
instance isInvertible_tensor (N : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    [IsInvertible 𝒪 h𝒪 L] [IsInvertible 𝒪 h𝒪 N] : IsInvertible 𝒪 h𝒪 (L ⊗ N) :=
  (isInvertible_iff_isEquivalence_tensorLeft 𝒪 h𝒪 _).mpr
    ((tensorInverse 𝒪 h𝒪 L).tensor (tensorInverse 𝒪 h𝒪 N)).isEquivalence_tensorLeft

end Powers

section Dual

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.monoidalClosed

variable (L : _root_.SheafOfModules.{u} (structureSheaf 𝒪 h𝒪))

/-- **The inverse of an invertible sheaf of modules is its dual**, the internal hom into the
structure sheaf: the right adjoint of `tensorLeft L` is both `ihom L` and the inverse
equivalence, and right adjoints are unique. -/
noncomputable def tensorInvIsoIhomUnit [IsInvertible 𝒪 h𝒪 L] :
    tensorInv 𝒪 h𝒪 L ≅
      (ihom L).obj (𝟙_ (_root_.SheafOfModules.{u} (structureSheaf 𝒪 h𝒪))) :=
  let := (isInvertible_iff_isEquivalence_tensorLeft 𝒪 h𝒪 L).mp ‹_›
  ((Adjunction.rightAdjointUniq (ihom.adjunction L)
    (tensorLeft L).asEquivalence.toAdjunction).app _).symm

/-- **The `(-1)`-st tensor power is the dual.** -/
noncomputable def tensorPowNegOneIsoIhomUnit [IsInvertible 𝒪 h𝒪 L] :
    tensorPow 𝒪 h𝒪 L (-1) ≅
      (ihom L).obj (𝟙_ (_root_.SheafOfModules.{u} (structureSheaf 𝒪 h𝒪))) :=
  tensorPowNegOneIso 𝒪 h𝒪 L ≪≫ tensorInvIsoIhomUnit 𝒪 h𝒪 L

end Dual

end AlgebraicGeometry.SheafOfModules
