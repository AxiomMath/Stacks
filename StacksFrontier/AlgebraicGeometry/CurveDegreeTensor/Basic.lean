module

public import StacksFrontier.AlgebraicGeometry.AmpleCurve.Basic
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.BaseCases
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Additivity of the degree in the tensor product on a proper curve

[Stacks, Tag 0AYX] computes the degree of a tensor product of locally free modules of constant
finite rank on a proper scheme of dimension at most one over a field:

`deg(ℰ ⊗ 𝒱) = rank(ℰ) · deg(𝒱) + rank(𝒱) · deg(ℰ)`.

Its proof reduces to a proper curve by [Stacks, Tag 0AYW] and then to [Stacks, Tag 0AYV], the
computation of `χ(X, ℰ ⊗ ℱ)` for `ℱ` merely coherent. This file carries out that second
reduction: from the form
`exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_devissage` of
Tag 0AYV on a curve (in the `AlgebraicGeometry` namespace), Tag 0AYX follows by arithmetic in the
Euler characteristics alone: writing `χ` for the Euler characteristic and
taking the fibre rank of a module of constant rank `m` to be `m` at the generic point,

`deg(ℰ ⊗ 𝒱) = χ(ℰ ⊗ 𝒱) − nm·χ(𝒪_X) = m·deg(ℰ) + n·χ(𝒱) − nm·χ(𝒪_X) = m·deg(ℰ) + n·deg(𝒱)`.

**The invertible case needs strictly less**, and it is the case the ampleness criterion of
[Stacks, Tag 0B5X] consumes. At rank one the rank of the tensor product is not an extra
hypothesis — the tensor product of two invertible modules is invertible by [Stacks, Tag 0B8M]
clause (2) — and clause (5) of [Stacks, Tag 0AYT] is already discharged, so the only inputs left
are the dévissage of [Stacks, Tag 01YH] and [Stacks, Tag 02O6] at the dévissage's two base
sheaves.

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `curveDegree_tensorSheaf_eq_add_of_devissage`: **[Stacks, Tag 0AYX] on a proper curve**, at
  every pair of ranks, from the hypotheses of [Stacks, Tag 0AYV] together with the rank of the
  tensor product.
* `invertibleCurveDegree_tensorSheaf_eq_add_of_devissage`: **the invertible case**,
  `deg(ℳ ⊗ 𝒩) = deg(ℳ) + deg(𝒩)`, with neither of those two extra inputs.
* `invertibleCurveDegree_tensorPower_eq_mul_of_devissage`: `deg(𝓛^{⊗ n}) = n · deg(𝓛)` for every
  integer `n`, with the hypothesis `hadd` of
  `AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul` discharged.
* `invertibleCurveDegree_pos_of_isAmple_of_devissage`: **the "only if" direction of
  [Stacks, Tag 0B5X]** with the hypothesis `hmul` of
  `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple` discharged, leaving `hpos`
  ([Stacks, Tag 0B40] part 2) as its one remaining degree input.

## Implementation notes

Every statement carries `hdev`, `hclosed` and `hunit` — the dévissage of [Stacks, Tag 01YH] and
finite dimensionality of [Stacks, Tag 02O6] at the structure sheaf and at the coherent modules
supported in a proper closed subset — as hypotheses, and is stated for a proper curve
`[IsCurve k f]`.

Both `AlgebraicGeometry.curveDegree` and `AlgebraicGeometry.invertibleCurveDegree` unfold to an
alternating sum of Euler characteristics (`AlgebraicGeometry.curveDegree_eq_eulerCharacteristic_sub`
and `AlgebraicGeometry.invertibleCurveDegree_eq_eulerCharacteristic_sub`), so once every term is
written in Euler characteristics the identity is linear arithmetic and the rank index never has
to be matched.

Tag 0AYV is stated with
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X.toRingedSpace`, the hypothesis `hadd`
of `AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul` with
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.toRingedSpace.presheaf
  (structureSheafRing X.toRingedSpace).property`.
The two are the same term; the statements below use the second, and the equation coming out of
Tag 0AYV is rebound at that spelling with a declared type, since a `rw` whose motive mentions the
other spelling fails its type-correctness check.

## References

* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules (nonvanishingLocus)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **[Stacks, Tag 0AYX] on a proper curve**: for `ℰ` and `𝒱` finite locally free of constant
ranks `n` and `m`,

`deg(ℰ ⊗ 𝒱) = m · deg(ℰ) + n · deg(𝒱)`.

The hypotheses `hdev`, `hclosed`, `hunit` and `h0AYT` are those of the form of
[Stacks, Tag 0AYV]
`exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_devissage`, and `hEV`
is the rank of the tensor product. The fibre rank of `𝒱` at the generic point is `m` by
`AlgebraicGeometry.Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank`, and then every
term is rewritten into Euler characteristics, where the identity is arithmetic. -/
theorem curveDegree_tensorSheaf_eq_add_of_devissage [IsCurve k f] [IsProper f]
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (hclosed : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (hunit : ∀ m,
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m))
    (hdim : topologicalKrullDim X ≤ 1) (E V : X.Modules) (n m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V m]
    (h0AYT : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G),
      topologicalKrullDim (_root_.SheafOfModules.supp G) ≤ 0 →
      ∃ hT : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))).IsCoherent,
        @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))) hT =
          (n : ℤ) * @eulerCharacteristic k _ X f _ G hG)
    (hEV : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.toRingedSpace.presheaf)
          (forget₂ CommRingCat RingCat)
          ((structureSheafRing X.toRingedSpace).property)⟩).obj (E)).obj (V))) (n * m)) :
    @curveDegree k _ X f _ hdim
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.toRingedSpace.presheaf)
            (forget₂ CommRingCat RingCat)
            ((structureSheafRing X.toRingedSpace).property)⟩).obj (E)).obj (V))) (n * m) hEV =
      (m : ℤ) * curveDegree k f hdim E n + (n : ℤ) * curveDegree k f hdim V m := by
  have hcV : SheafOfModules.IsCoherent V :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f V m
  have hO : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f _ 1
  obtain ⟨hT, hchi⟩ :=
    exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_devissage
      k f E n hdev hclosed hunit h0AYT V
  rw [Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank V m
    (genericPoint X)] at hchi
  have hchi' : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.toRingedSpace.presheaf)
            (forget₂ CommRingCat RingCat)
            ((structureSheafRing X.toRingedSpace).property)⟩).obj (E)).obj (V))) hT =
      (m : ℤ) * @curveDegree k _ X f _ hdim E n ‹_› +
        (n : ℤ) * eulerCharacteristic k f V := hchi
  rw [@curveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim _ (n * m) hEV hT hO,
    @curveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim V m ‹_› hcV hO, hchi']
  push_cast
  ring

/-- **The invertible case of [Stacks, Tag 0AYX]**: `deg(ℳ ⊗ 𝒩) = deg(ℳ) + deg(𝒩)` for `ℳ` and
`𝒩` invertible on a proper curve over a field. Both ranks are one, so the tag's
`rank(ℳ)·deg(𝒩) + rank(𝒩)·deg(ℳ)` reads as the plain sum.

Clause (5) of [Stacks, Tag 0AYT] holds at rank one, and `ℳ ⊗ 𝒩` has rank one because it is
invertible ([Stacks, Tag 01CT] part 1) and an invertible module is finite locally free of rank one
([Stacks, Tag 0B8M] clause 2). The invertibility witness `hMN` of the tensor product is an explicit
hypothesis, matching the hypothesis `hadd` of
`AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul`; the degree does not depend on it. -/
theorem invertibleCurveDegree_tensorSheaf_eq_add_of_devissage [IsCurve k f] [IsProper f]
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (hclosed : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (hunit : ∀ m,
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m))
    (hdim : topologicalKrullDim X ≤ 1) (M N : X.Modules)
    (hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
    (hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N)
    (hMN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.toRingedSpace.presheaf)
          (forget₂ CommRingCat RingCat)
          ((structureSheafRing X.toRingedSpace).property)⟩).obj (M)).obj (N)))) :
    @invertibleCurveDegree k _ X f _ hdim
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.toRingedSpace.presheaf)
            (forget₂ CommRingCat RingCat)
            ((structureSheafRing X.toRingedSpace).property)⟩).obj (M)).obj (N))) hMN =
      @invertibleCurveDegree k _ X f _ hdim M hM +
        @invertibleCurveDegree k _ X f _ hdim N hN := by
  have := hM
  have := hN
  have := hMN
  have hcM : SheafOfModules.IsCoherent M :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f M 1
  have hcN : SheafOfModules.IsCoherent N :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f N 1
  have hO : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f _ 1
  obtain ⟨hT, hchi⟩ :=
    exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_devissage_one
      k f M hdev hclosed hunit N
  rw [Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank N 1
    (genericPoint X)] at hchi
  rw [@curveDegree_eq_eulerCharacteristic_sub k _ X f _
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) M 1 _ hcM hO] at hchi
  have hchi' : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.toRingedSpace.presheaf)
            (forget₂ CommRingCat RingCat)
            ((structureSheafRing X.toRingedSpace).property)⟩).obj (M)).obj (N))) hT =
      (1 : ℤ) * (eulerCharacteristic k f M -
          (1 : ℤ) * eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf)) +
        1 * eulerCharacteristic k f N := hchi
  have e1 := @invertibleCurveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim _ hMN hT hO
  have e2 := @invertibleCurveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim M hM hcM hO
  have e3 := @invertibleCurveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim N hN hcN hO
  linarith [e1, e2, e3, hchi']

/-- **The degree of a tensor power, unconditionally in the tensor product**:
`deg(𝓛^{⊗ n}) = n · deg(𝓛)` for every integer `n`.

This is `AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul` with its hypothesis `hadd`
supplied by `AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_eq_add_of_devissage`. -/
theorem invertibleCurveDegree_tensorPower_eq_mul_of_devissage [IsCurve k f] [IsProper f]
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (hclosed : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (hunit : ∀ m,
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m))
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (n : ℤ) :
    @invertibleCurveDegree k _ X f _ hdim
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n)
        (tensorPower_isInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n) =
      n * invertibleCurveDegree k f hdim L :=
  invertibleCurveDegree_tensorPower_eq_mul k f hdim L
    (fun M N hM hN hMN =>
      invertibleCurveDegree_tensorSheaf_eq_add_of_devissage k f hdev hclosed hunit hdim
        M N hM hN hMN) n

/-- **The "only if" direction of [Stacks, Tag 0B5X] with its degree-of-a-tensor-power input
discharged**: an ample invertible sheaf on a proper curve over a field has positive degree, given
positivity of the degree of an invertible sheaf with a section that vanishes somewhere but not
everywhere.

This is `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple` with its hypothesis `hmul`
supplied by `AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul_of_devissage`; the
remaining hypothesis `hpos` follows from [Stacks, Tag 0B40] part 2. -/
theorem invertibleCurveDegree_pos_of_isAmple_of_devissage [IsCurve k f] [IsProper f]
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (hclosed : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (hunit : ∀ m,
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m))
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hpos : ∀ n : ℕ, 1 ≤ n → ∀ s : (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        (∃ x : X, x ∈ nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) →
        nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ≠ Set.univ →
        0 < @invertibleCurveDegree k _ X f _ hdim
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ))
          (tensorPower_isInvertible X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)))
    (hL : Scheme.Modules.IsAmple X L) :
    0 < invertibleCurveDegree k f hdim L :=
  invertibleCurveDegree_pos_of_isAmple k f hdim L
    (fun n => invertibleCurveDegree_tensorPower_eq_mul_of_devissage k f hdev hclosed hunit hdim
      L (n : ℤ)) hpos hL

end AlgebraicGeometry

end
