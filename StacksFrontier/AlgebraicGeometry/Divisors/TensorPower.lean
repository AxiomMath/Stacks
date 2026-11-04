module

public import StacksFrontier.Topology.Sheaves.Modules.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRaisedSymmetry

/-!
# Integer tensor powers of an invertible sheaf of modules

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` admitting sheafification, and let
`L` be an invertible sheaf of `𝒪`-modules. Tensoring on the right by `L` is then an
autoequivalence of the category of `𝒪`-modules, so it can be iterated an arbitrary *integer*
number of times, negative iterates using the chosen quasi-inverse. The `n`th tensor power
`L^{⊗ n}` is the image of the structure sheaf under the `n`th iterate.

This file also records the constraints of the sheaf tensor product itself — the two unitors,
the associator and the braiding — which are what a coherent multiplication
`L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` has to be compatible with. The associator is the one
place where Tag 05NA is used: the comparison between a nested sheaf tensor product and the
sheafification of the corresponding triple presheaf tensor product is an isomorphism by
`Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight` and `..._whiskerLeft`.

## Main definitions

* The right-tensor convention of Tag 01CU is the native sheaf tensor bifunctor's `.flip.obj L`.
* `Stacks.SheafOfModules.Invertible.tensorPowerEquivalence` is its `n`th integer iterate as an
  autoequivalence.
* `Stacks.SheafOfModules.Invertible.tensorPower` is `L^{⊗ n}`.
* `Stacks.SheafOfModules.Invertible.tensorProductBifunctor` is `(M, N) ↦ (M ⊗ N)^#`.
* `Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor`,
  `tensorProductRightUnitor`, `tensorProductAssociator` and `tensorProductBraiding` are the
  constraints of the sheaf tensor product.

## Main results

* `Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence`: right tensoring by an
  invertible sheaf is an equivalence, via `tensorLeftIsoTensorRight`.
* `Stacks.SheafOfModules.Invertible.isInvertible_iff_tensorRightFunctor_isEquivalence`: the
  converse as well, so that invertibility *is* the criterion Tag 0409 (2) states, namely that
  `F ↦ (F ⊗ L)^#` be an equivalence.
* `Stacks.SheafOfModules.Invertible.tensorPower_zero`: the zeroth power is the structure
  sheaf, by `rfl`.
* `Stacks.SheafOfModules.Invertible.tensorPowerOneIso`: the first power is `L`.
* `Stacks.SheafOfModules.Invertible.tensorPowerSuccIso`: `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}`.
* `Stacks.SheafOfModules.Invertible.tensorPowerReindex`: transport along an equality of
  exponents.

## Implementation notes

Tag 01CS states invertibility in terms of tensoring on the *left*, while Tag 01CU iterates
tensoring on the *right*. The two differ by the symmetry of the presheaf tensor product, which
is `tensorLeftIsoTensorRight`; it is what transfers the equivalence property across.

Integer iteration is Mathlib's `Equivalence`-power `e ^ n` (via `zpow`). Because that is
defined by recursion on the natural number and separately on the negative part, the successor
comparison `e.functor.obj ((e ^ n).functor.obj M) ≅ (e ^ (n + 1)).functor.obj M` has to be
built by the same case split; this is `powSuccIso`, assembled from `powNatSuccIso` and
`powNatInverseSuccIso`. For negative exponents the step is the counit of the equivalence.

The monoidal and symmetric structures on `PresheafOfModules (𝒪^#).obj` are obtained from
Mathlib's structures on `PresheafOfModules (structureRingPresheaf 𝒪)`, which is the same
category; the `letI`s that do so are local to each construction.

The coherent multiplication of tensor powers, Tag 01CU's
`TensorPowerCoherence`/`tensorPowerCoherence_exists`, is **not** in this file: it is genuine
content and is treated separately. Everything here is independent of
that step.

Invertibility of `tensorPower O hO L n` for every `n` and the multiplication isomorphism do not
need the coherence structure:
`Stacks.SheafOfModules.Invertible.tensorPower_isInvertible`
(`StacksFrontier/AlgebraicGeometry/Ample/AmpleCriteria.lean`) gives invertibility for every
`n : ℤ`, and `Stacks.SheafOfModules.Invertible.tensorPowerMulIso`
(`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Basic.lean`) is the multiplication
`L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}` for `a b : ℕ`. What `TensorPowerCoherence` is still needed
for is **commutativity**, which is not formal: see that file's implementation notes.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Symmetry of the tensor product identifies tensoring on the left, the convention of Tag
01CS, with tensoring on the right, the convention of Tag 01CU. -/
noncomputable def tensorLeftIsoTensorRight
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L := by
  letI := Stacks.hasSheafCompose_forget₂_commRingCat.{w, v, u} J
  exact (Stacks.SheafOfModules.TensorRaised.tensorRightRaisedIso.{u, v, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩ L).symm

/-- Tensoring on the right by an invertible sheaf is an equivalence. -/
noncomputable instance tensorRightFunctor_isEquivalence
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence := by
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        L).IsEquivalence :=
    Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence O hO L
  exact Functor.isEquivalence_of_iso (tensorLeftIsoTensorRight O hO L)

/-- **Stacks Project, Tag 0409 (2)**, equivalently **Tag 01CS**, in the source's own form: a
sheaf of `O`-modules `L` is invertible exactly when the functor `F ↦ (F ⊗_O L)^#` of the
source is an equivalence. The invertibility predicate is phrased through the universal
property of tensoring on the *left*, so this is the criterion the source states and the
predicate agreeing, the two tensor functors being identified by `tensorLeftIsoTensorRight`. -/
@[stacks 0409 "invertible"]
theorem isInvertible_iff_tensorRightFunctor_isEquivalence
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    IsInvertible O hO L ↔ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence :=
  (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence O hO L).trans
    (Functor.isEquivalence_iff_of_iso (tensorLeftIsoTensorRight O hO L))

/-- The autoequivalence obtained by tensoring on the right by `L` an integer number of times.
Negative powers use its chosen quasi-inverse. -/
@[implicit_reducible]
noncomputable def tensorPowerEquivalence
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℤ) :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ≌
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
      L).asEquivalence ^ n

/-- **Stacks Project, Tag 01CU.** The `n`th tensor power `L^{⊗ n}` of an invertible sheaf `L`,
for `n` an arbitrary integer: the image of the structure sheaf under the `n`th power of the
right-tensor autoequivalence. -/
@[stacks 01CU]
noncomputable def tensorPower
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℤ) :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  (tensorPowerEquivalence O hO L n).functor.obj
    (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- The zeroth tensor power is the structure sheaf. -/
@[simp]
theorem tensorPower_zero
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    tensorPower O hO L 0 = SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) := rfl

/-- The canonical identification of the first tensor power with `L`: the left unitor on the
underlying presheaves, followed by the counit of sheafification. -/
noncomputable def tensorPowerOneIso
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] : tensorPower O hO L 1 ≅ L := by
  letI : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
        := by
    change MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    infer_instance
  letI : IsIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit := by
    change IsIso
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).counit
    infer_instance
  change (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
      ((SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val ⊗
        L.val) ≅ L
  exact (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (λ_ L.val) ≪≫
    (asIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit).app L

/-- Iterating an autoequivalence commutes with applying it once more. The comparison is the
identity after reassociating the recursive iteration. -/
noncomputable def powNatSuccIso
    {A : Type u} [Category.{v} A] (e : A ≌ A) :
    (n : ℕ) → (M : A) →
      e.functor.obj ((e.powNat n).functor.obj M) ≅ (e.powNat (n + 1)).functor.obj M
  | 0, _ => Iso.refl _
  | 1, _ => Iso.refl _
  | n + 2, M => powNatSuccIso e (n + 1) (e.functor.obj M)

/-- Cancellation of the first inverse iterate by the original equivalence. -/
noncomputable def powNatInverseSuccIso
    {A : Type u} [Category.{v} A] (e : A ≌ A) :
    (n : ℕ) → (M : A) →
      e.functor.obj ((e.symm.powNat (n + 1)).functor.obj M) ≅ (e.symm.powNat n).functor.obj M
  | 0, M => e.counitIso.app M
  | 1, M => e.counitIso.app (e.inverse.obj M)
  | n + 2, M => powNatInverseSuccIso e (n + 1) (e.inverse.obj M)

/-- The successor comparison for integer iterates of an autoequivalence. For negative
exponents the step is the counit of the equivalence. -/
noncomputable def powSuccIso
    {A : Type u} [Category.{v} A] (e : A ≌ A) (n : ℤ) (M : A) :
    e.functor.obj ((e ^ n).functor.obj M) ≅ (e ^ (n + 1)).functor.obj M := by
  cases n with
  | ofNat k => exact powNatSuccIso e k M
  | negSucc k =>
      cases k with
      | zero => exact e.counitIso.app M
      | succ k => exact powNatInverseSuccIso e (k + 1) M

/-- `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}`: one more application of the right-tensor autoequivalence,
or its counit in negative degree. -/
noncomputable def tensorPowerSuccIso
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((tensorPower O hO L n))).obj (L)) ≅
      tensorPower O hO L (n + 1) :=
  powSuccIso ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
      L).asEquivalence n
    (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- Transport of tensor powers along an equality of exponents. -/
noncomputable def tensorPowerReindex
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] {n m : ℤ} (h : n = m) :
    tensorPower O hO L n ≅ tensorPower O hO L m := by
  subst h
  exact Iso.refl _

/-- The tensor product bifunctor on sheaves of modules: tensor the underlying presheaves and
sheafify. -/
@[implicit_reducible]
noncomputable def tensorProductBifunctor :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ×
        SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) := by
  letI : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
        := by
    change MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    infer_instance
  exact Functor.prod
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ⋙
    tensor (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj) ⋙
    Stacks.SheafOfModules.TensorSheafification.sheafify O hO

/-- The sheaf tensor product of two sheaves of modules, as a value of the bifunctor. -/
noncomputable abbrev tensorProduct
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :=
  (tensorProductBifunctor O hO).obj (M, N)

/-- The sheaf tensor bifunctor applied to a pair of isomorphisms. -/
noncomputable def tensorProductIso
    {M M' N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (e : M ≅ M') (f : N ≅ N') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
        (N)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (M')).obj (N')) :=
  (tensorProductBifunctor O hO).mapIso (Iso.prod e f)

/-- The left unit constraint of the sheaf tensor product: sheafify the presheaf left unitor,
then apply the sheafification counit. -/
noncomputable def tensorProductLeftUnitor
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))).obj (M)) ≅ M
        := by
  letI : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
        :=
    PresheafOfModules.monoidalCategory (R := O)
  letI : IsIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit := by
    change IsIso
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).counit
    infer_instance
  exact (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (λ_ M.val) ≪≫
    (asIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit).app M

/-- The right unit constraint of the sheaf tensor product. -/
noncomputable def tensorProductRightUnitor
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
        ((SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))) ≅ M :=
        by
  letI : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
        :=
    PresheafOfModules.monoidalCategory (R := O)
  letI : IsIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit := by
    change IsIso
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).counit
    infer_instance
  exact (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (ρ_ M.val) ≪≫
    (asIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit).app M

/-- The associativity constraint of the sheaf tensor product. The sheafification units compare
each nested sheaf tensor product with the sheafification of the corresponding triple presheaf
tensor product; Tag 05NA makes those comparisons isomorphisms, and between them sits the
presheaf associator. -/
noncomputable def tensorProductAssociator
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (M)).obj (N))))).obj (P)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (M)).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (N)).obj (P))))) := by
  letI : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
        :=
    PresheafOfModules.monoidalCategory (R := O)
  letI : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val) ▷ P.val)) :=
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight O hO
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val)) P.val
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO (M.val ⊗
        N.val))
  letI : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
      (M.val ◁ Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (N.val ⊗ P.val))) :=
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft O hO M.val
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (N.val ⊗ P.val))
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO (N.val ⊗
        P.val))
  let eLeft := asIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
    (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val) ▷ P.val))
  let eRight := asIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
    (M.val ◁ Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (N.val ⊗ P.val)))
  exact eLeft.symm ≪≫
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (α_ M.val N.val P.val) ≪≫
      eRight

/-- The symmetry constraint of the sheaf tensor product, obtained by sheafifying the presheaf
braiding. -/
noncomputable def tensorProductBraiding
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
        (N)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (N)).obj (M)) := by
  letI : MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
        :=
    PresheafOfModules.monoidalCategory (R := O)
  letI : SymmetricCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
        :=
    PresheafOfModules.symmetricCategory (R := O)
  exact (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (β_ M.val N.val)

end Stacks.SheafOfModules.Invertible

end
