module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Equivalence
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback

/-!
# The comparison of two quadruples at the least common multiple of their degrees

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), and let `(d, f, L, ψ)` and
`(d', f, L', ψ')` be quadruples of Section 01NS over a test scheme `T`, with `d` and `d'`
positive. Tag 01NW asserts that the three conditions

1. the two quadruples are compatible at the cofactors `(a₀, a₀')` of the least common multiple
   `m₀ = a₀ d = a₀' d'` of their degrees,
2. the two quadruples are equivalent, that is compatible at `(d', d)`,
3. the two quadruples are compatible at some positive common multiple of their degrees,

say the same thing.
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Equivalence` proves (1) implies (2) and (2)
implies (3) — restriction to a more divisible common multiple, which is free — and reduces the
remaining implications to the *descent* of a comparison to a less divisible pair of degrees,
which it carries out in every positive degree
(`...Quadruple.hasCompAt_lcm_of_compatibleAt`). This file turns that degreewise family into a
comparison and closes the cycle.

## What had to be supplied

A comparison at `(a₀, a₀')` is not a single isomorphism but the isomorphism of graded algebras
`⨁_{n ∈ ℤ} L^{⊗ n a₀} ⟶ ⨁_{n ∈ ℤ} (L')^{⊗ n a₀'}` that `β : L^{⊗ a₀} ⟶ (L')^{⊗ a₀'}` induces, so
two things are needed beyond the descent in a positive degree.

* **The components in the non-positive degrees.** For `n ≤ 0` the component `ψ_{n a₀}` is no
  longer surjective, so the descent does not reach the degree `n a₀` from the degree `n a₀`
  itself. The component is nevertheless determined, and `scaledPred` constructs it: the two
  sides of the comparison at the index `n` tensored by `(L')^{⊗ a₀'}` are the two sides of the
  comparison at the index `n + 1`, and tensoring by an invertible module is an equivalence,
  hence fully faithful, so the comparison at `n` is the unique preimage. Taking that step
  downwards out of the index `1` builds `scaledIso` at every integer index.
* **Multiplicativity in an arbitrary pair of indices.** `scaledIso_mul` proves it for every pair
  of integer indices, negative ones included, by induction on the second index in both
  directions out of the index `0`; the step consumes the associativity law of Tag 01CU.

The compatibility of the resulting family with `ψ` is then proved at every index, positive or
not (`...Quadruple.isCompAt_scaledIso`). In a positive index this is the descent of
`Equivalence` together with the uniqueness that the surjectivity of `ψ` supplies; in a
non-positive index the component is cut out of the one at the index `1` by the one at the index
`1 - n`, and `...Quadruple.isCompAt_of_mul` is the observation that makes this work: of the two
degrees entering a descent, only the *second* has to be positive, because the surjection of the
second factor is whiskered into the first.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.mulPairIso`: **the homogeneous multiplication
  of the Laurent algebra with its total degree prescribed**, so that a multiplicativity square
  can be stated at the degrees a consumer asks for with no transport left over.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.scaledIso`: **the comparison
  `L^{⊗ n a} ≅ (L')^{⊗ n a'}` induced by an isomorphism `L^{⊗ a} ≅ (L')^{⊗ a'}`**, at every
  integer index `n`, as data.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.pairIso`: that comparison read as a
  family indexed by the pairs of degrees lying on the line through `(a₀, a₀')`, which is the
  shape `Quadruple.CompatibleAt` asks for.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.scaledIso_mul`: **the comparison is
  multiplicative at every pair of integer indices.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.isCompAt_scaledIso`: **the
  comparison is compatible with `ψ` in every degree**, the non-positive ones included.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.compatibleAt_lcm_of_compatibleAt`:
  **Tag 01NW, (3) implies (1)**, with the positive common multiple given explicitly.
* `...Quadruple.lcm_compatible_of_exists_compatible`, `...Quadruple.lcm_compatible_of_equivalent`
  and `...Quadruple.equivalent_of_exists_compatible`: **Tag 01NW, (3) implies (1), (2) implies
  (1) and (3) implies (2)**. With (1) implies (2) and (2) implies (3) of `Equivalence`, every
  implication among the three conditions now has a carrier.

## Implementation notes

The index `1` rather than the index `0` is where the recursion is anchored, in the following
sense: `scaledZero` is *defined* as the lowering step applied to the given isomorphism `β`, so
that `scaledIso_one` — the comparison at the index `1` is `β` — holds by the round-trip identity
of the two steps and needs no computation with the unit laws. That is what makes the
multiplicativity at the indices `(n, 1)` immediate from the successor law.

The generating isomorphism is taken at the degrees `(1 * a, 1 * a')` rather than at `(a, a')`.
The two are equal only propositionally, and taking the former means that the index-`1` component
of the family is the generator on the nose, with no reindexing anywhere in the induction.

Multiplicativity is stated with the total index a free variable constrained by a hypothesis,
`MulCompat β n m s` for any `s` with `n + m = s`, rather than at `s = n + m`. The inductive step
needs the square at the indices `(n + m, 1)` with total index `n + (m + 1)`, and the free total
index is what lets it be used there without transporting along the associativity of addition.

## References

* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-
The ring sheaf of the category the right-tensor functor of Tag 01CA lives on is
`Stacks.SheafOfModules.Tensor.ringSheaf` of the structure sheaf written out as a pair, while the
Laurent algebra of Section 01NS is graded by `structureRingSheaf`, which reads the same sheaf off
the ringed space through `AlgebraicGeometry.SheafedSpace.sheaf`. Both are plain `def`s, so neither
unfolds at the `instances` transparency a `rw` matches at, and a goal mentioning both is not
type-correct there. They are made `implicit_reducible` for this file, as the files upstream of it
already do for the same crossing.
-/
attribute [local implicit_reducible] AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

/-! ### The multiplication of the Laurent algebra at a prescribed total degree -/

variable {T : Scheme.{u}}

/-- **Every integral tensor power of an invertible module is invertible**, at the spelling the
Laurent algebra of Section 01NS is graded by. -/
theorem isInvertible_piece (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M] (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
      ((laurent M).piece n) :=
  isInvertible_tensorPower T.toRingedSpace.presheaf (isSheafStruct T) M n

attribute [local instance] isInvertible_piece

/-- Scaling an equality of degrees: if `n + m = s` then `n b + m b = s b`. -/
theorem degMul {n m s : ℤ} (h : n + m = s) (b : ℤ) : n * b + m * b = s * b := by
  rw [← h]; ring

section Pair

variable (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M]

/-- **The homogeneous multiplication of the Laurent algebra with its total degree prescribed**:
the coherent multiplication `L^{⊗ p} ⊗ L^{⊗ p'} ≅ L^{⊗ (p + p')}` of Tag 01CU followed by the
transport of the total degree along an equality `p + p' = s`.

Prescribing the total degree rather than reading it off is what lets a multiplicativity square be
stated at the degrees a consumer asks for; no reindexing is then left over. -/
abbrev mulPairIso {p p' s : ℤ} (h : p + p' = s) :
    (laurent M).piece p ⊗ (laurent M).piece p' ≅ (laurent M).piece s :=
  mulIso M p p' ≪≫ reindexIso M h

/-- Reindexing along an equality of a degree with itself is the identity. -/
theorem reindexIso_self {n : ℤ} (h : n = n) : reindexIso M h = Iso.refl _ := rfl

/-- **Multiplying by the degree-`b` piece**, the step of the recursion below: the multiplication
`L^{⊗ n b} ⊗ L^{⊗ 1 b} ≅ L^{⊗ (n + 1) b}`. -/
abbrev mulStepIso (b n : ℤ) :
    (laurent M).piece (n * b) ⊗ (laurent M).piece (1 * b) ≅ (laurent M).piece ((n + 1) * b) :=
  mulPairIso M (degMul (rfl : n + 1 = n + 1) b)

/-- **The associativity law of Tag 01CU with all four total degrees prescribed.** Both sides
multiply the three pieces in degrees `p`, `p'` and `p''` into the degree `r`. -/
theorem mulPairIso_assoc {p p' p'' s t r : ℤ}
    (h1 : p + p' = s) (h2 : p' + p'' = t) (h3 : s + p'' = r) (h4 : p + t = r) :
    ((mulPairIso M h1).hom ▷ (laurent M).piece p'') ≫ (mulPairIso M h3).hom =
      (α_ ((laurent M).piece p) ((laurent M).piece p') ((laurent M).piece p'')).hom ≫
        ((laurent M).piece p ◁ (mulPairIso M h2).hom) ≫ (mulPairIso M h4).hom := by
  subst h1
  subst h2
  subst h3
  simp only [Iso.trans_hom, reindexIso_self, Iso.refl_hom, Category.comp_id, Category.assoc]
  exact mulIso_assoc M p p' p''

/-- The isomorphism against which the multiplicativity square at the indices `(n, m + 1)` is
cancelled on the left: the associator followed by the multiplication step at the index `m`. -/
def mulHead (b n m : ℤ) :
    ((laurent M).piece (n * b) ⊗ (laurent M).piece (m * b)) ⊗ (laurent M).piece (1 * b) ≅
      (laurent M).piece (n * b) ⊗ (laurent M).piece ((m + 1) * b) :=
  α_ ((laurent M).piece (n * b)) ((laurent M).piece (m * b)) ((laurent M).piece (1 * b)) ≪≫
    MonoidalCategory.whiskerLeftIso ((laurent M).piece (n * b)) (mulStepIso M b m)

theorem mulHead_hom (b n m : ℤ) :
    (mulHead M b n m).hom =
      (α_ ((laurent M).piece (n * b)) ((laurent M).piece (m * b))
          ((laurent M).piece (1 * b))).hom ≫
        ((laurent M).piece (n * b) ◁ (mulStepIso M b m).hom) :=
  rfl

/-- `mulPairIso_assoc`, read from right to left, which is the shape the inductive step of the
multiplicativity square consumes. -/
theorem mulPairIso_assoc' {p p' p'' s t r : ℤ}
    (h1 : p + p' = s) (h2 : p' + p'' = t) (h3 : s + p'' = r) (h4 : p + t = r) :
    ((α_ ((laurent M).piece p) ((laurent M).piece p') ((laurent M).piece p'')).hom ≫
          ((laurent M).piece p ◁ (mulPairIso M h2).hom)) ≫ (mulPairIso M h4).hom =
      ((mulPairIso M h1).hom ▷ (laurent M).piece p'') ≫ (mulPairIso M h3).hom := by
  rw [Category.assoc]
  exact (mulPairIso_assoc M h1 h2 h3 h4).symm

end Pair

/-! ### The comparison of two Laurent algebras along a pair of scaled degrees -/

section Scaled

variable {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']
  {a a' : ℤ}

/-- **A comparison in a single scaled degree**: an isomorphism `L^{⊗ n a} ≅ (L')^{⊗ n a'}`
between the degree-`n a` piece of the Laurent algebra of `L` and the degree-`n a'` piece of the
Laurent algebra of `L'`.

The generating isomorphism is an argument of the abbreviation although it does not occur in the
body, and is named `_β` for that reason: the two modules and the two scaling factors are
implicit everywhere in this section, and naming the isomorphism is what determines them. -/
abbrev ScaledCmp (_β : (laurent L).piece (1 * a) ≅ (laurent L').piece (1 * a')) (n : ℤ) :
    Type u :=
  (laurent L).piece (n * a) ≅ (laurent L').piece (n * a')

variable (β : (laurent L).piece (1 * a) ≅ (laurent L').piece (1 * a'))

/-- **Splitting off the top factor and exchanging it**: `L^{⊗ (n+1) a} ≅ L^{⊗ n a} ⊗ (L')^{⊗ a'}`,
the multiplication step of Tag 01CU read backwards followed by `β` in the second factor. The
target is written as the image of `L^{⊗ n a}` under right tensoring by `(L')^{⊗ a'}`, which is
the shape the cancellation of `scaledPred` consumes. -/
def scaledClimb (n : ℤ) :
    (laurent L).piece ((n + 1) * a) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
          ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            T.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
            (isSheafStruct T)⟩).flip.obj
        ((laurent L').piece (1 * a'))).obj ((laurent L).piece (n * a)) :=
  (mulStepIso L a n).symm ≪≫
    MonoidalCategory.whiskerLeftIso ((laurent L).piece (n * a)) β

/-- **Raising the index by one.** Split the extra factor off by `scaledClimb`, apply the
comparison at `n` in the first factor, and reassemble by the multiplication step on the `L'`
side. Nothing here uses the sign of `n`. -/
def scaledSucc (n : ℤ) (φ : ScaledCmp β n) : ScaledCmp β (n + 1) :=
  scaledClimb β n ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
        ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          T.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
          (isSheafStruct T)⟩).flip.obj
      ((laurent L').piece (1 * a'))).mapIso φ ≪≫
    mulStepIso L' a' n

/-- **Lowering the index by one.** There is no recursion available: the negative tensor powers of
Tag 01CU are iterates of a chosen quasi-inverse of right tensoring, and `β` has no reason to
commute with that choice. The step is taken by cancellation instead. Tensoring on the right by
`(L')^{⊗ a'}` is an equivalence, hence fully faithful, and the two sides of the comparison at `n`
tensored by `(L')^{⊗ a'}` are, by Tag 01CU, the two sides of the comparison at `n + 1`; so the
comparison at `n` is the unique preimage. -/
def scaledPred (n : ℤ) (ψ : ScaledCmp β (n + 1)) : ScaledCmp β n :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
        ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          T.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
          (isSheafStruct T)⟩).flip.obj
      ((laurent L').piece (1 * a'))).preimageIso
    ((scaledClimb β n).symm ≪≫ ψ ≪≫ (mulStepIso L' a' n).symm)

/-- Tensoring the lowering step by `(L')^{⊗ a'}` undoes the cancellation it was defined by: this
is `CategoryTheory.Functor.map_preimage` for the fully faithful functor `- ⊗ (L')^{⊗ a'}`. -/
theorem mapIso_scaledPred (n : ℤ) (ψ : ScaledCmp β (n + 1)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
          ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            T.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
            (isSheafStruct T)⟩).flip.obj
        ((laurent L').piece (1 * a'))).mapIso (scaledPred β n ψ) =
      (scaledClimb β n).symm ≪≫ ψ ≪≫ (mulStepIso L' a' n).symm :=
  Iso.ext (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
        T.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
        (isSheafStruct T)⟩).flip.obj
    ((laurent L').piece (1 * a'))).map_preimage _)

/-- Lowering and then raising the index is the identity. -/
@[simp] theorem scaledSucc_scaledPred (n : ℤ) (ψ : ScaledCmp β (n + 1)) :
    scaledSucc β n (scaledPred β n ψ) = ψ := by
  simp only [scaledSucc, mapIso_scaledPred]
  exact iso_conj_left _ _ _

/-- Raising and then lowering the index is the identity. -/
@[simp] theorem scaledPred_scaledSucc (n : ℤ) (φ : ScaledCmp β n) :
    scaledPred β n (scaledSucc β n φ) = φ := by
  refine Iso.ext (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
        T.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
        (isSheafStruct T)⟩).flip.obj
    ((laurent L').piece (1 * a'))).map_injective ?_)
  have h : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
          ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            T.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
            (isSheafStruct T)⟩).flip.obj
        ((laurent L').piece (1 * a'))).mapIso (scaledPred β n (scaledSucc β n φ)) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
          ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
            T.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
            (isSheafStruct T)⟩).flip.obj
        ((laurent L').piece (1 * a'))).mapIso φ := by
    rw [mapIso_scaledPred]
    simp only [scaledSucc]
    exact iso_conj_right _ _ _
  exact congrArg Iso.hom h

/-- **The comparison at the index `0`.** It is not the identity: the degree-zero pieces of the
two Laurent algebras are both the structure sheaf, but the degrees `0 a` and `0 a'` are not the
integer `0` on the nose. Taking it as the lowering step applied to `β` is what makes the
comparison at the index `1` be `β` itself, with no unit-law computation. -/
def scaledZero : ScaledCmp β 0 :=
  scaledPred β 0 β

/-- The comparison at the nonnegative indices, by recursion. -/
def scaledIsoNat : (j : ℕ) → ScaledCmp β (j : ℤ)
  | 0 => scaledZero β
  | j + 1 => scaledSucc β (j : ℤ) (scaledIsoNat j)

/-- The comparison at the negative indices, by recursion downwards from the index `0`. -/
def scaledIsoNeg : (j : ℕ) → ScaledCmp β (Int.negSucc j)
  | 0 => scaledPred β (Int.negSucc 0) (scaledZero β)
  | j + 1 => scaledPred β (Int.negSucc (j + 1)) (scaledIsoNeg j)

/-- **The comparison `L^{⊗ n a} ≅ (L')^{⊗ n a'}` induced by an isomorphism
`L^{⊗ a} ≅ (L')^{⊗ a'}`, for every integer `n`, as data.** -/
def scaledIso : (n : ℤ) → ScaledCmp β n
  | Int.ofNat j => scaledIsoNat β j
  | Int.negSucc j => scaledIsoNeg β j

@[simp] theorem scaledIso_ofNat (j : ℕ) : scaledIso β (j : ℤ) = scaledIsoNat β j := rfl

@[simp] theorem scaledIso_negSucc (j : ℕ) :
    scaledIso β (Int.negSucc j) = scaledIsoNeg β j := rfl

/-- **The successor law, at every integer index.** -/
theorem scaledIso_succ (n : ℤ) : scaledIso β (n + 1) = scaledSucc β n (scaledIso β n) := by
  match n with
  | Int.ofNat j => rfl
  | Int.negSucc 0 => exact (scaledSucc_scaledPred β (Int.negSucc 0) (scaledZero β)).symm
  | Int.negSucc (j + 1) =>
      exact (scaledSucc_scaledPred β (Int.negSucc (j + 1)) (scaledIsoNeg β j)).symm

/-- **The predecessor law**: the successor law read downwards. -/
theorem scaledIso_pred (n : ℤ) : scaledIso β n = scaledPred β n (scaledIso β (n + 1)) := by
  rw [scaledIso_succ, scaledPred_scaledSucc]

/-- **The comparison at the index `1` is the given isomorphism.** This is what the choice of
`scaledZero` buys. -/
theorem scaledIso_one : scaledIso β 1 = β :=
  (scaledIso_succ β 0).trans (scaledSucc_scaledPred β 0 β)

/-- **The successor law as a commuting square**: the comparison is compatible with the
multiplication step of Tag 01CU. -/
theorem scaledIso_mulStep (n : ℤ) :
    (mulStepIso L a n).hom ≫ (scaledIso β (n + 1)).hom =
      ((laurent L).piece (n * a) ◁ β.hom) ≫
        ((scaledIso β n).hom ▷ (laurent L').piece (1 * a')) ≫ (mulStepIso L' a' n).hom := by
  rw [scaledIso_succ]
  have hmi : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
            ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
              T.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
              (isSheafStruct T)⟩).flip.obj
          ((laurent L').piece (1 * a'))).mapIso (scaledIso β n)).hom =
        (scaledIso β n).hom ▷ (laurent L').piece (1 * a') :=
    tensorRight_mapIso (X := T) _ _
  change (mulStepIso L a n).hom ≫
      (((mulStepIso L a n).inv ≫ ((laurent L).piece (n * a) ◁ β.hom)) ≫
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
              ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
                T.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
                (isSheafStruct T)⟩).flip.obj
            ((laurent L').piece (1 * a'))).mapIso (scaledIso β n)).hom ≫
          (mulStepIso L' a' n).hom)) = _
  rw [hmi]
  simp only [Category.assoc]
  exact Iso.hom_inv_id_assoc (mulStepIso L a n) _

/-! ### Multiplicativity of the comparison -/

/-- **The monoidal algebra behind the inductive step**, in the shape in which the two
multiplications in the target land in one and the same object, so that no transport of the total
degree is left over. This is `...LaurentPullback.monoidalStep` with its last morphism the
identity. -/
private theorem monoidalStep' {C : Type*} [Category C] [MonoidalCategory C]
    {A B D A' B' D' M N R : C} (x : A ⟶ A') (y : B ⟶ B') (z : D ⟶ D')
    (p : B' ⊗ D' ⟶ M) (q : A' ⊗ B' ⟶ N) (s : A' ⊗ M ⟶ R) (t : N ⊗ D' ⟶ R)
    (h : ((α_ A' B' D').hom ≫ (A' ◁ p)) ≫ s = (q ▷ D') ≫ t) :
    (α_ A B D).hom ≫ (A ◁ ((y ⊗ₘ z) ≫ p)) ≫ (x ▷ M) ≫ s =
      ((x ⊗ₘ y) ▷ D) ≫ (q ▷ D) ≫ (N ◁ z) ≫ t := by
  have h2 := monoidalStep x y z p q s t (𝟙 R) (by rw [Category.comp_id]; exact h)
  simpa using h2

/-- **The multiplicativity square of the comparison at the indices `(n, m)` with total index
`s`.** Multiplying in the Laurent algebra of `L` into the degree `s a` and then comparing agrees
with comparing at the indices `n` and `m` and then multiplying in the Laurent algebra of `L'`
into the degree `s a'`.

The total index is a free variable constrained by a hypothesis rather than read off as `n + m`:
that is what lets the inductive step use the square at the indices `(n + m, 1)` with total index
`n + (m + 1)` without any transport along the associativity of addition. -/
abbrev MulCompat (n m s : ℤ) : Prop :=
  ∀ h : n + m = s,
    (mulPairIso L (degMul h a)).hom ≫ (scaledIso β s).hom =
      ((scaledIso β n).hom ⊗ₘ (scaledIso β m).hom) ≫ (mulPairIso L' (degMul h a')).hom

/-- **Multiplicativity at the indices `(n, 1)`, for every integer `n`.** The multiplication step
is the successor step of the recursion, and the comparison is compatible with it
(`scaledIso_mulStep`); the comparison at the index `1` is `β` itself (`scaledIso_one`). -/
theorem mulCompat_one (n s : ℤ) (hs : n + 1 = s) : MulCompat β n 1 s := by
  subst hs
  intro h
  rw [scaledIso_mulStep, scaledIso_one, tensorHom_def', Category.assoc]

/-- The isomorphism against which the multiplicativity square at the indices `(n, m + 1)` is
cancelled on the right: compare at the index one, then multiply into the degree
`(n + (m + 1)) a'` on the `L'` side. -/
def mulTail (n m : ℤ) :
    (laurent L').piece ((n + m) * a') ⊗ (laurent L).piece (1 * a) ≅
      (laurent L').piece ((n + (m + 1)) * a') :=
  MonoidalCategory.whiskerLeftIso ((laurent L').piece ((n + m) * a')) (scaledIso β 1) ≪≫
    mulPairIso L' (degMul (show n + m + 1 = n + (m + 1) by ring) a')

theorem mulTail_hom (n m : ℤ) :
    (mulTail β n m).hom =
      ((laurent L').piece ((n + m) * a') ◁ (scaledIso β 1).hom) ≫
        (mulPairIso L' (degMul (show n + m + 1 = n + (m + 1) by ring) a')).hom :=
  rfl

/-- **The left-hand side of the square at the indices `(n, m + 1)`**, cut down by `mulHead` and
`mulTail` to the left-hand side of the square at the indices `(n, m)` whiskered by `L^{⊗ a}`.
The inputs are the associativity law of Tag 01CU and the case of the indices `(n + m, 1)`. -/
theorem mulCompat_lhs (n m : ℤ) :
    (α_ ((laurent L).piece (n * a)) ((laurent L).piece (m * a))
          ((laurent L).piece (1 * a))).hom ≫
        ((laurent L).piece (n * a) ◁ (mulStepIso L a m).hom) ≫
          ((mulPairIso L (degMul (show n + (m + 1) = n + (m + 1) from rfl) a)).hom ≫
            (scaledIso β (n + (m + 1))).hom) =
      (((mulPairIso L (degMul (show n + m = n + m from rfl) a)).hom ≫
            (scaledIso β (n + m)).hom) ▷ (laurent L).piece (1 * a)) ≫
        (mulTail β n m).hom := by
  rw [← Category.assoc, ← Category.assoc,
    mulPairIso_assoc' L (degMul (show n + m = n + m from rfl) a)
      (degMul (show m + 1 = m + 1 from rfl) a)
      (degMul (show n + m + 1 = n + (m + 1) by ring) a)
      (degMul (show n + (m + 1) = n + (m + 1) from rfl) a)]
  simp only [Category.assoc]
  rw [mulCompat_one β (n + m) (n + (m + 1)) (by ring) (by ring), mulTail_hom]
  simp only [Category.assoc, tensorHom_def, MonoidalCategory.comp_whiskerRight]

/-- **The right-hand side of the square at the indices `(n, m + 1)`**, cut down by `mulHead` and
`mulTail` to the right-hand side of the square at the indices `(n, m)` whiskered by `L^{⊗ a}`.
The inputs are the case of the indices `(m, 1)` and `monoidalStep'`. -/
theorem mulCompat_rhs (n m : ℤ) :
    (α_ ((laurent L).piece (n * a)) ((laurent L).piece (m * a))
          ((laurent L).piece (1 * a))).hom ≫
        ((laurent L).piece (n * a) ◁ (mulStepIso L a m).hom) ≫
          (((scaledIso β n).hom ⊗ₘ (scaledIso β (m + 1)).hom) ≫
            (mulPairIso L' (degMul (show n + (m + 1) = n + (m + 1) from rfl) a')).hom) =
      ((((scaledIso β n).hom ⊗ₘ (scaledIso β m).hom) ≫
            (mulPairIso L' (degMul (show n + m = n + m from rfl) a')).hom) ▷
          (laurent L).piece (1 * a)) ≫
        (mulTail β n m).hom := by
  rw [tensorHom_def' (scaledIso β n).hom (scaledIso β (m + 1)).hom]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, mulCompat_one β m (m + 1) rfl rfl, mulTail_hom]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  exact monoidalStep' (scaledIso β n).hom (scaledIso β m).hom (scaledIso β 1).hom
    (mulPairIso L' (degMul (show m + 1 = m + 1 from rfl) a')).hom
    (mulPairIso L' (degMul (show n + m = n + m from rfl) a')).hom
    (mulPairIso L' (degMul (show n + (m + 1) = n + (m + 1) from rfl) a')).hom
    (mulPairIso L' (degMul (show n + m + 1 = n + (m + 1) by ring) a')).hom
    (mulPairIso_assoc' L' (degMul (show n + m = n + m from rfl) a')
      (degMul (show m + 1 = m + 1 from rfl) a')
      (degMul (show n + m + 1 = n + (m + 1) by ring) a')
      (degMul (show n + (m + 1) = n + (m + 1) from rfl) a'))

/-- **The inductive step, upwards.** -/
theorem mulCompat_succ {n m s s' : ℤ} (hs : n + m = s) (hs' : n + (m + 1) = s')
    (h : MulCompat β n m s) : MulCompat β n (m + 1) s' := by
  subst hs
  subst hs'
  intro hh
  refine (Iso.cancel_iso_hom_left (mulHead L a n m) _ _).mp ?_
  rw [mulHead_hom]
  simp only [Category.assoc]
  rw [mulCompat_lhs, mulCompat_rhs, h rfl]

/-- Two morphisms that agree after right whiskering by an invertible module are equal. -/
private theorem eq_of_whiskerRight_eq
    {M N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (X : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) X]
    {g g' : M ⟶ N} (h : g ▷ X = g' ▷ X) : g = g' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
        T.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
        (isSheafStruct T)⟩).flip.obj X).map_injective
    ((bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T) g X).trans
      (h.trans (bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T) g' X).symm))

/-- **The inductive step, downwards.** This is the direction that reaches the non-positive
indices, and it is where the invertibility of `L^{⊗ a}` is used: the two sides of the square at
the indices `(n, m)` become equal after tensoring on the right by `L^{⊗ a}`, and tensoring by an
invertible module is an equivalence, hence faithful. -/
theorem mulCompat_of_succ {n m s s' : ℤ} (hs : n + m = s) (hs' : n + (m + 1) = s')
    (h : MulCompat β n (m + 1) s') : MulCompat β n m s := by
  subst hs
  subst hs'
  intro hh
  have h2 := congrArg (fun z => (mulHead L a n m).hom ≫ z) (h rfl)
  rw [mulHead_hom] at h2
  simp only [Category.assoc] at h2
  rw [mulCompat_lhs, mulCompat_rhs] at h2
  exact eq_of_whiskerRight_eq ((laurent L).piece (1 * a))
    ((Iso.cancel_iso_hom_right _ _ (mulTail β n m)).mp h2)

/-- **Multiplicativity at the indices `(n, 0)`** — the anchor of the induction, obtained from the
case of the indices `(n, 1)` read down one step. -/
theorem mulCompat_zero (n s : ℤ) (hs : n + 0 = s) : MulCompat β n 0 s :=
  mulCompat_of_succ β (m := 0) hs (show n + (0 + 1) = n + 1 by ring)
    (mulCompat_one β n (n + 1) rfl)

/-- **The comparison `L^{⊗ n a} ≅ (L')^{⊗ n a'}` is multiplicative at every pair of integer
indices**, negative ones included. The induction is on the second index, in both directions out
of the index `0`. -/
theorem scaledIso_mul (n m s : ℤ) (hs : n + m = s) : MulCompat β n m s := by
  revert s
  induction m using Int.induction_on with
  | zero => intro s hs; exact mulCompat_zero β n s hs
  | succ i ih => intro s hs; exact mulCompat_succ β rfl hs (ih _ rfl)
  | pred i ih =>
      intro s hs
      refine mulCompat_of_succ β (m := -(i : ℤ) - 1) hs
        (show n + (-(i : ℤ) - 1 + 1) = n + -(i : ℤ) by ring) ?_
      rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring]
      exact ih _ rfl

end Scaled

/-! ### Reindexing, and an isomorphism of the unit object which is multiplicative -/

section Transport

variable (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M]

/-- Reindexing a tensor power along an equality of degrees and back is the identity. -/
theorem reindexIso_hom_comp_hom {n m : ℤ} (h : n = m) (h' : m = n) :
    (reindexIso M h).hom ≫ (reindexIso M h').hom = 𝟙 _ := by
  subst h
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  rw [Category.id_comp]

/-- **The homogeneous multiplication of the Laurent algebra in the bidegree `(0, 0)` is the right
unitor** of Tag 01CA: the unit law of Tag 01CU, with the transport of the total degree `0 + 0` to
`0` the identity. -/
theorem mulIso_zero_zero : (mulIso M 0 0).hom = (ρ_ ((laurent M).piece 0)).hom :=
  (Category.comp_id _).symm.trans (mulIso_zero_right M 0)

end Transport

/-- **An isomorphism of the monoidal unit which is multiplicative for the right unitor is the
identity.** Both unitors agree on the unit object, so the two whiskerings of `g` by the unit are
carried to `g` by the unitor; the multiplicativity then reads `g ∘ g = g`, and `g` is
invertible. -/
private theorem hom_eq_id_of_mul {C : Type*} [Category C] [MonoidalCategory C]
    (g : (𝟙_ C) ≅ (𝟙_ C))
    (h : (g.hom ⊗ₘ g.hom) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ g.hom) :
    g.hom = 𝟙 (𝟙_ C) := by
  have h1 : (g.hom ⊗ₘ g.hom) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ g.hom ≫ g.hom := by
    rw [tensorHom_def, Category.assoc, ← MonoidalCategory.unitors_equal,
      MonoidalCategory.leftUnitor_naturality, MonoidalCategory.unitors_equal, ← Category.assoc,
      MonoidalCategory.rightUnitor_naturality, Category.assoc]
  rw [h1] at h
  have h2 : g.hom ≫ g.hom = g.hom := (Iso.cancel_iso_hom_left (ρ_ (𝟙_ C)) _ _).mp h
  have : IsIso g.hom := g.isIso_hom
  exact (cancel_epi g.hom).mp (h2.trans (Category.comp_id g.hom).symm)

/-! ### The comparison of two quadruples in every degree -/

namespace Quadruple

variable {S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d d' : ℤ}
  {P : Quadruple f A d} {Q : Quadruple f A d'}

/-- `Quadruple.isCompAt_tensor` with the two total degrees prescribed, so that the comparison
being tensored lives in the degrees a consumer asks for. -/
theorem isCompAt_tensor' {p q p' q' s t : ℤ}
    (hp : p * d = q * d') (hp' : p' * d = q' * d') (hs : p + p' = s) (ht : q + q' = t)
    (hst : s * d = t * d')
    (δ : (laurent P.L).piece s ⟶ (laurent Q.L).piece t) (hδ : IsCompAt P Q hst δ) :
    MonoidalCategoryStruct.tensorHom (P.twisting.app p) (P.twisting.app p') ≫
        (mulPairIso P.L hs).hom ≫ δ =
      MonoidalCategoryStruct.tensorHom
        ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)) ≫
          Q.twisting.app q)
        ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
          Q.twisting.app q') ≫ (mulPairIso Q.L ht).hom := by
  subst hs
  subst ht
  have h := isCompAt_tensor hp hp' hst δ hδ
  simp only [mulSheaf_laurent] at h
  simp only [Iso.trans_hom, reindexIso_self, Iso.refl_hom, Category.comp_id]
  exact h

/-- **Two comparisons in one pair of degrees whose multiplications by a common comparison agree
are equal**, in the form the recursion upwards needs: if the comparison in the degrees
`(p + p', q + q')` is multiplicative over comparisons in the degrees `(p, q)` and `(p', q')` that
are both compatible with `ψ`, and if *some* comparison in the degrees `(p + p', q + q')` is
compatible with `ψ`, then the given one is. The two surjections `ψ_p` and `ψ_{p'}` are cancelled,
which is what the positivity of `p` and `p'` supplies. -/
theorem isCompAt_of_mul_of_exists {p q p' q' s t : ℤ}
    (hp : p * d = q * d') (hp' : p' * d = q' * d') (hs : p + p' = s) (ht : q + q' = t)
    (hst : s * d = t * d') (hp0 : 0 < p) (hp'0 : 0 < p')
    (g : (laurent P.L).piece p ⟶ (laurent Q.L).piece q)
    (g' : (laurent P.L).piece p' ⟶ (laurent Q.L).piece q')
    (δ : (laurent P.L).piece s ⟶ (laurent Q.L).piece t)
    (hg : IsCompAt P Q hp g) (hg' : IsCompAt P Q hp' g')
    (hmul : MonoidalCategoryStruct.tensorHom g g' ≫ (mulPairIso Q.L ht).hom =
      (mulPairIso P.L hs).hom ≫ δ)
    (hex : ∃ δ₀ : (laurent P.L).piece s ⟶ (laurent Q.L).piece t, IsCompAt P Q hst δ₀) :
    IsCompAt P Q hst δ := by
  obtain ⟨δ₀, hδ₀⟩ := hex
  have e1 : P.twisting.app p ≫ g =
    (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp)) ≫
      Q.twisting.app q := hg
  have e2 : P.twisting.app p' ≫ g' =
    (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
      Q.twisting.app q' := hg'
  have hep : Epi (P.twisting.app p) := P.epi_app_of_pos hp0
  have hep' : Epi (P.twisting.app p') := P.epi_app_of_pos hp'0
  haveI htens : Epi (MonoidalCategoryStruct.tensorHom (P.twisting.app p)
      (P.twisting.app p')) := epi_tensorHom T.toRingedSpace _ _
  have key : MonoidalCategoryStruct.tensorHom (P.twisting.app p) (P.twisting.app p') ≫
        (mulPairIso P.L hs).hom ≫ δ =
      MonoidalCategoryStruct.tensorHom (P.twisting.app p) (P.twisting.app p') ≫
        (mulPairIso P.L hs).hom ≫ δ₀ := by
    rw [isCompAt_tensor' hp hp' hs ht hst δ₀ hδ₀, ← hmul, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom, e1, e2]
  have hδ : δ = δ₀ :=
    (Iso.cancel_iso_hom_left (mulPairIso P.L hs) _ _).mp ((cancel_epi _).mp key)
  rw [hδ]
  exact hδ₀

/-- **The descent of a comparison to a less divisible pair of degrees, in the form the
construction of the family needs**: a comparison in the degrees `(p, q)` which is multiplicative
over a comparison in the degrees `(p', q')` compatible with `ψ`, into a comparison in the degrees
`(p + p', q + q')` compatible with `ψ`, is itself compatible with `ψ`.

Only the second pair of degrees has to be positive. Both quotients are cancelled, but on the
first factor there is nothing to cancel: the surjection `ψ'_{q'}` of the second factor is
whiskered into the first, which is an epimorphism because a tensor product of epimorphisms is,
and the remaining whiskering by the invertible `(L')^{⊗ q'}` is faithful. -/
theorem isCompAt_of_mul {p q p' q' s t : ℤ}
    (hp : p * d = q * d') (hp' : p' * d = q' * d') (hs : p + p' = s) (ht : q + q' = t)
    (hst : s * d = t * d') (hp'0 : 0 < p') (hq'0 : 0 < q')
    (g : (laurent P.L).piece p ⟶ (laurent Q.L).piece q)
    (g' : (laurent P.L).piece p' ⟶ (laurent Q.L).piece q')
    (δ : (laurent P.L).piece s ⟶ (laurent Q.L).piece t)
    (hg' : IsCompAt P Q hp' g') (hδ : IsCompAt P Q hst δ)
    (hmul : MonoidalCategoryStruct.tensorHom g g' ≫ (mulPairIso Q.L ht).hom =
      (mulPairIso P.L hs).hom ≫ δ) :
    IsCompAt P Q hp g := by
  have e2 : P.twisting.app p' ≫ g' =
    (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
      Q.twisting.app q' := hg'
  have key := isCompAt_tensor' hp hp' hs ht hst δ hδ
  rw [← hmul, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, e2] at key
  have key2 := (Iso.cancel_iso_hom_right _ _ (mulPairIso Q.L ht)).mp key
  rw [tensorHom_def', tensorHom_def'] at key2
  haveI heq' : Epi (Q.twisting.app q') := Q.epi_app_of_pos hq'0
  haveI hw : Epi ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
      Q.twisting.app q') := epi_comp _ _
  haveI hwl : Epi (MonoidalCategoryStruct.whiskerLeft
      ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p * d)))
      ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
        Q.twisting.app q')) := by
    have := epi_tensorHom T.toRingedSpace
      (CategoryStruct.id ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (p * d))))
      ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hp')) ≫
        Q.twisting.app q')
    rwa [MonoidalCategory.id_tensorHom] at this
  have key3 := (cancel_epi _).mp key2
  exact eq_of_whiskerRight_eq ((laurent Q.L).piece q') key3

section Family

variable {a₀ a₀' : ℤ}

/-- The equality of degrees of the algebra at the index `n`: the degree-`n a₀` component of `ψ`
and the degree-`n a₀'` component of `ψ'` have the same source. -/
theorem scaledDegEq (hm₀ : a₀ * d = a₀' * d') (n : ℤ) : n * a₀ * d = n * a₀' * d' := by
  linear_combination n * hm₀

variable (β : (laurent P.L).piece (1 * a₀) ≅ (laurent Q.L).piece (1 * a₀'))

/-- **The inductive step upwards**: the comparison at the index `n + 1` is compatible with `ψ`
once the comparisons at the indices `n` and `1` are, provided some comparison in the degrees
`((n+1) a₀, (n+1) a₀')` is. -/
theorem isCompAt_scaledIso_succ (hm₀ : a₀ * d = a₀' * d') (ha₀ : 0 < a₀)
    (hβ : IsCompAt P Q (scaledDegEq hm₀ 1) (scaledIso β 1).hom)
    (hH : ∀ n : ℤ, 0 < n → HasCompAt P Q (n * a₀) (n * a₀'))
    {n : ℤ} (hn : 0 < n) (ih : IsCompAt P Q (scaledDegEq hm₀ n) (scaledIso β n).hom) :
    IsCompAt P Q (scaledDegEq hm₀ (n + 1)) (scaledIso β (n + 1)).hom := by
  refine isCompAt_of_mul_of_exists (scaledDegEq hm₀ n) (scaledDegEq hm₀ 1)
    (degMul (rfl : n + 1 = n + 1) a₀) (degMul (rfl : n + 1 = n + 1) a₀')
    (scaledDegEq hm₀ (n + 1)) (mul_pos hn ha₀) (by rw [one_mul]; exact ha₀)
    (scaledIso β n).hom (scaledIso β 1).hom (scaledIso β (n + 1)).hom ih hβ
    ((scaledIso_mul β n 1 (n + 1) rfl rfl).symm) ?_
  obtain ⟨hdeg, g, hg⟩ := hH (n + 1) (by omega)
  exact ⟨g.hom, hg⟩

/-- **The comparison at every positive index is compatible with `ψ`.** -/
theorem isCompAt_scaledIso_of_pos (hm₀ : a₀ * d = a₀' * d') (ha₀ : 0 < a₀)
    (hβ : IsCompAt P Q (scaledDegEq hm₀ 1) (scaledIso β 1).hom)
    (hH : ∀ n : ℤ, 0 < n → HasCompAt P Q (n * a₀) (n * a₀'))
    {n : ℤ} (hn : 0 < n) :
    IsCompAt P Q (scaledDegEq hm₀ n) (scaledIso β n).hom := by
  have key : ∀ k : ℕ,
      IsCompAt P Q (scaledDegEq hm₀ ((k : ℤ) + 1)) (scaledIso β ((k : ℤ) + 1)).hom := by
    intro k
    induction k with
    | zero => exact hβ
    | succ k ih =>
        have hc : ((k + 1 : ℕ) : ℤ) + 1 = ((k : ℤ) + 1) + 1 := by push_cast; ring
        rw [hc]
        exact isCompAt_scaledIso_succ β hm₀ ha₀ hβ hH (by omega) ih
  have hk : n = (((n - 1).toNat : ℕ) : ℤ) + 1 := by omega
  rw [hk]
  exact key _

/-- **The comparison at every index, positive or not, is compatible with `ψ`.** For a
non-positive index the comparison is cut out of the one at the index `1` by the one at the index
`1 - n`, both of which are positive; this is the step that `ψ` being no longer surjective in a
non-positive degree would seem to block, and it does not, because only the second factor of the
descent has to be positive. -/
theorem isCompAt_scaledIso (hm₀ : a₀ * d = a₀' * d') (ha₀ : 0 < a₀) (ha₀' : 0 < a₀')
    (hβ : IsCompAt P Q (scaledDegEq hm₀ 1) (scaledIso β 1).hom)
    (hH : ∀ n : ℤ, 0 < n → HasCompAt P Q (n * a₀) (n * a₀')) (n : ℤ) :
    IsCompAt P Q (scaledDegEq hm₀ n) (scaledIso β n).hom := by
  rcases lt_or_ge 0 n with hn | hn
  · exact isCompAt_scaledIso_of_pos β hm₀ ha₀ hβ hH hn
  refine isCompAt_of_mul (scaledDegEq hm₀ n) (scaledDegEq hm₀ (1 - n))
    (degMul (show n + (1 - n) = 1 by ring) a₀) (degMul (show n + (1 - n) = 1 by ring) a₀')
    (scaledDegEq hm₀ 1) (mul_pos (by omega) ha₀) (mul_pos (by omega) ha₀')
    (scaledIso β n).hom (scaledIso β (1 - n)).hom (scaledIso β 1).hom
    (isCompAt_scaledIso_of_pos β hm₀ ha₀ hβ hH (by omega)) hβ
    ((scaledIso_mul β n (1 - n) 1 (by ring) (by ring)).symm)

/-! ### The comparison as a family indexed by the scaled pairs of degrees -/

/-- **The comparison in a pair of degrees presented as a scaled pair `(n a₀, n a₀')`**: the
comparison at the index `n`, with its two degrees transported to the prescribed ones. -/
def pairIsoOf {p q : ℤ} (n : ℤ) (hp : p = n * a₀) (hq : q = n * a₀') :
    (laurent P.L).piece p ≅ (laurent Q.L).piece q :=
  reindexIso P.L hp ≪≫ scaledIso β n ≪≫ reindexIso Q.L hq.symm

/-- The presentation of a pair of degrees as a scaled pair is unique when `a₀ ≠ 0`, so the
comparison does not depend on it. -/
theorem pairIsoOf_congr (ha₀ : a₀ ≠ 0) {p q n n' : ℤ} (hp : p = n * a₀) (hq : q = n * a₀')
    (hp' : p = n' * a₀) (hq' : q = n' * a₀') :
    pairIsoOf β n hp hq = pairIsoOf β n' hp' hq' := by
  have hn : n = n' := mul_right_cancel₀ ha₀ (by rw [← hp]; exact hp')
  subst hn
  rfl

/-- **The comparison at a pair of degrees lying on the line through `(a₀, a₀')`**, which is the
shape of the family `Quadruple.CompatibleAt` asks for. -/
def pairIso (p q : ℤ) (h : IsScaledPair a₀ a₀' p q) :
    (laurent P.L).piece p ≅ (laurent Q.L).piece q :=
  pairIsoOf β h.choose h.choose_spec.1 h.choose_spec.2

/-- The family, computed at any presentation of the pair of degrees as a scaled pair. -/
theorem pairIso_eq (ha₀ : a₀ ≠ 0) {p q n : ℤ} (h : IsScaledPair a₀ a₀' p q)
    (hp : p = n * a₀) (hq : q = n * a₀') :
    pairIso β p q h = pairIsoOf β n hp hq :=
  pairIsoOf_congr β ha₀ _ _ hp hq

/-- **The family is multiplicative**, in the vocabulary of `Quadruple.CompatibleAt`: this is
`scaledIso_mul` with the two total degrees read off rather than prescribed, so that the two
transports cancel. -/
theorem pairIso_mul (ha₀ : a₀ ≠ 0) (p q p' q' : ℤ)
    (h : IsScaledPair a₀ a₀' p q) (h' : IsScaledPair a₀ a₀' p' q') :
    MonoidalCategoryStruct.tensorHom (pairIso β p q h).hom (pairIso β p' q' h').hom ≫
        (laurent Q.L).mulSheaf q q' =
      (laurent P.L).mulSheaf p p' ≫ (pairIso β (p + p') (q + q') (h.add h')).hom := by
  obtain ⟨n, hp, hq⟩ := id h
  obtain ⟨m, hp', hq'⟩ := id h'
  rw [pairIso_eq β ha₀ h hp hq, pairIso_eq β ha₀ h' hp' hq',
    pairIso_eq β ha₀ (h.add h') (show p + p' = (n + m) * a₀ by rw [hp, hp']; ring)
      (show q + q' = (n + m) * a₀' by rw [hq, hq']; ring)]
  subst hp
  subst hq
  subst hp'
  subst hq'
  have key := congrArg
    (fun z => z ≫ (reindexIso Q.L (degMul (rfl : n + m = n + m) a₀').symm).hom)
    (scaledIso_mul β n m (n + m) rfl rfl)
  simp only [pairIsoOf, Iso.trans_hom, reindexIso_self, Iso.refl_hom, Category.id_comp,
    Category.comp_id, mulSheaf_laurent, Category.assoc, reindexIso_hom_comp_hom] at key ⊢
  exact key.symm

/-- **The family is compatible with `ψ`**, in the vocabulary of `Quadruple.CompatibleAt`. -/
theorem pairIso_twisting (ha₀ : a₀ ≠ 0) (hm₀ : a₀ * d = a₀' * d') (ha₀pos : 0 < a₀)
    (ha₀'pos : 0 < a₀')
    (hβ : IsCompAt P Q (scaledDegEq hm₀ 1) (scaledIso β 1).hom)
    (hH : ∀ n : ℤ, 0 < n → HasCompAt P Q (n * a₀) (n * a₀'))
    (p q : ℤ) (h : IsScaledPair a₀ a₀' p q) :
    P.twisting.app p ≫ (pairIso β p q h).hom =
      (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (h.degree_eq hm₀))) ≫ Q.twisting.app q := by
  obtain ⟨n, hp, hq⟩ := id h
  rw [pairIso_eq β ha₀ h hp hq]
  subst hp
  subst hq
  simp only [pairIsoOf, Iso.trans_hom, reindexIso_self, Iso.refl_hom, Category.id_comp,
    Category.comp_id]
  exact isCompAt_scaledIso β hm₀ ha₀pos ha₀'pos hβ hH n

/-- **The family preserves the unit.** The degree-zero pieces of the two Laurent algebras are
the monoidal unit and both units are the identity (`oneHom_laurent`), so what has to be shown is
that the degree-zero component of the family is the identity; and that follows from
multiplicativity in the bidegree `(0, 0)`, where the multiplication of the Laurent algebra is the
right unitor. -/
theorem pairIso_one (ha₀ : a₀ ≠ 0) :
    SheafOfModules.GradedAlgebra.oneHom (laurent P.L) ≫
        (pairIso β 0 0 (IsScaledPair.zero a₀ a₀')).hom =
      SheafOfModules.GradedAlgebra.oneHom (laurent Q.L) := by
  have hid : (pairIso β 0 0 (IsScaledPair.zero a₀ a₀')).hom =
      𝟙 (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))) := by
    refine hom_eq_id_of_mul (pairIso β 0 0 (IsScaledPair.zero a₀ a₀')) ?_
    have hmul := pairIso_mul β ha₀ 0 0 0 0 (IsScaledPair.zero a₀ a₀')
      (IsScaledPair.zero a₀ a₀')
    have e1 : (laurent Q.L).mulSheaf 0 0 =
        (ρ_ (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)))).hom :=
      (mulSheaf_laurent Q.L 0 0).trans (mulIso_zero_zero Q.L)
    have e2 : (laurent P.L).mulSheaf 0 0 =
        (ρ_ (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)))).hom :=
      (mulSheaf_laurent P.L 0 0).trans (mulIso_zero_zero P.L)
    rw [e1, e2] at hmul
    exact hmul
  rw [hid, oneHom_laurent P.L, oneHom_laurent Q.L]
  exact Category.comp_id _

end Family

/-! ### Tag 01NW: the three conditions agree -/

/-- The least common multiple of two integers is a multiple of the first, with the cofactor
written on the left, which is the shape the three conditions of Tag 01NW are stated at. -/
theorem exists_lcm_cofactor (i j : ℤ) : ∃ c : ℤ, (Int.lcm i j : ℤ) = c * i := by
  have h0 : i.natAbs ∣ Int.lcm i j := Nat.dvd_lcm_left i.natAbs j.natAbs
  obtain ⟨c, hc⟩ := Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr h0)
  exact ⟨c, hc.trans (mul_comm i c)⟩

/-- **Stacks Project, Tag 01NW, (3) implies (1).** Two quadruples with positive degrees `d` and
`d'` which are compatible at *some* positive common multiple of their degrees are compatible at
the least common multiple `m₀ = a₀ d = a₀' d'`.

The isomorphism `β : L^{⊗ a₀} ⟶ (L')^{⊗ a₀'}` is the degree-one case of
`hasCompAt_lcm_of_compatibleAt`, which descends the given comparison to every positive index; the
comparison in the remaining indices is cut out of it by `isCompAt_scaledIso`, its
multiplicativity in every bidegree is `scaledIso_mul`, and the unit clause is then forced. -/
theorem compatibleAt_lcm_of_compatibleAt (hd : 0 < d) (hd' : 0 < d') {a a' a₀ a₀' : ℤ}
    (ha : 0 < a) (ha₀ : (Int.lcm d d' : ℤ) = a₀ * d) (ha₀' : (Int.lcm d d' : ℤ) = a₀' * d')
    (h : CompatibleAt P Q a a') : CompatibleAt P Q a₀ a₀' := by
  have hlcm : 0 < (Int.lcm d d' : ℤ) := by
    have h1 : 0 < Int.lcm d d' :=
      Nat.lcm_pos (Int.natAbs_pos.mpr hd.ne') (Int.natAbs_pos.mpr hd'.ne')
    exact_mod_cast h1
  have hA₀ : 0 < a₀ := by nlinarith
  have hA₀' : 0 < a₀' := by nlinarith
  have hm₀ : a₀ * d = a₀' * d' := by rw [← ha₀, ha₀']
  have hH : ∀ n : ℤ, 0 < n → HasCompAt P Q (n * a₀) (n * a₀') := fun n hn =>
    hasCompAt_lcm_of_compatibleAt hd hd' ha ha₀ ha₀' h hn
  obtain ⟨hdeg1, β, hβ0⟩ := hH 1 one_pos
  have hβ : IsCompAt P Q (scaledDegEq hm₀ 1) (scaledIso β 1).hom := by
    rw [scaledIso_one]
    exact hβ0
  exact ⟨hm₀, pairIso β, fun p q p' q' hpq hpq' => pairIso_mul β hA₀.ne' p q p' q' hpq hpq',
    pairIso_one β hA₀.ne',
    fun p q hpq => pairIso_twisting β hA₀.ne' hm₀ hA₀ hA₀' hβ hH p q hpq⟩

/-- **Stacks Project, Tag 01NW, (3) implies (1)**, with condition (3) in the existential form in
which `exists_compatible_of_equivalent` delivers it. -/
theorem lcm_compatible_of_exists_compatible (hd : 0 < d) (hd' : 0 < d') {a₀ a₀' : ℤ}
    (ha₀ : (Int.lcm d d' : ℤ) = a₀ * d) (ha₀' : (Int.lcm d d' : ℤ) = a₀' * d')
    (h : ∃ m a a' : ℤ, 0 < m ∧ m = a * d ∧ m = a' * d' ∧ CompatibleAt P Q a a') :
    CompatibleAt P Q a₀ a₀' := by
  obtain ⟨m, a, a', hm, hma, hma', hc⟩ := h
  have ha : 0 < a := by nlinarith
  exact compatibleAt_lcm_of_compatibleAt hd hd' ha ha₀ ha₀' hc

/-- **Stacks Project, Tag 01NW, (2) implies (1).** Two equivalent quadruples with positive
degrees are compatible at the least common multiple of their degrees: equivalence is
compatibility at the positive common multiple `d d'`, and (3) implies (1). -/
theorem lcm_compatible_of_equivalent (hd : 0 < d) (hd' : 0 < d') {a₀ a₀' : ℤ}
    (ha₀ : (Int.lcm d d' : ℤ) = a₀ * d) (ha₀' : (Int.lcm d d' : ℤ) = a₀' * d')
    (h : Equivalent P Q) : CompatibleAt P Q a₀ a₀' :=
  lcm_compatible_of_exists_compatible hd hd' ha₀ ha₀'
    (exists_compatible_of_equivalent hd hd' h)

/-- **Stacks Project, Tag 01NW, (3) implies (2).** Two quadruples with positive degrees which are
compatible at some positive common multiple of their degrees are equivalent: (3) implies (1) and
(1) implies (2). -/
theorem equivalent_of_exists_compatible (hd : 0 < d) (hd' : 0 < d')
    (h : ∃ m a a' : ℤ, 0 < m ∧ m = a * d ∧ m = a' * d' ∧ CompatibleAt P Q a a') :
    Equivalent P Q := by
  obtain ⟨a₀, ha₀⟩ := exists_lcm_cofactor d d'
  obtain ⟨a₀', ha₀'⟩ := exists_lcm_cofactor d' d
  rw [Int.lcm_comm] at ha₀'
  exact equivalent_of_lcm_compatible hd hd' ha₀ ha₀'
    (lcm_compatible_of_exists_compatible hd hd' ha₀ ha₀' h)

/-! ### The three conditions of Tag 01NW in one statement -/

/-- **[Stacks, Tag 01NW].** In Situation 01NN, let `T` be a scheme and let `(d, f, L, ψ)` and
`(d', f, L', ψ')` be two quadruples over `T` with `d` and `d'` positive, and write the least
common multiple `m` of `d` and `d'` as `m = a₀ d = a₀' d'`. Then the following three conditions
are equivalent:

1. the two quadruples are compatible at `(a₀, a₀')`, that is, there is an isomorphism
   `β : L^{⊗ a₀} ⟶ (L')^{⊗ a₀'}` for which `β ∘ ψ|_{f^*𝒜^{(m)}}` and `ψ'|_{f^*𝒜^{(m)}}` agree as
   graded ring maps;
2. the two quadruples are equivalent, that is, compatible at `(d', d)`;
3. the two quadruples are compatible at `(a, a')` for some positive common multiple
   `m = a d = a' d'` of their degrees.

The source's remaining clause `f = f'` is not a separate condition here: both quadruples are
taken over the same morphism `f : T ⟶ S`, which is a parameter of the type `Quadruple f 𝒜 d`,
so the two morphisms are equal by construction in all three conditions.

The five implications of the cycle are the five declarations above and in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Equivalence`:
`equivalent_of_lcm_compatible`, `exists_compatible_of_equivalent`,
`lcm_compatible_of_exists_compatible`, `lcm_compatible_of_equivalent` and
`equivalent_of_exists_compatible`. -/
@[stacks 01NW "for two quadruples over the same morphism with positive degrees d and d', and the \
least common multiple m of d and d' written as m = a d = a' d', these three conditions are \
equivalent: compatibility at the cofactors (a, a') of the least common multiple; equivalence of \
the two quadruples, i.e. compatibility at (d', d); and compatibility at the cofactors of some \
positive common multiple of the two degrees"]
theorem tfae_compatibleAt_lcm (hd : 0 < d) (hd' : 0 < d') {a₀ a₀' : ℤ}
    (ha₀ : (Int.lcm d d' : ℤ) = a₀ * d) (ha₀' : (Int.lcm d d' : ℤ) = a₀' * d') :
    List.TFAE
      [CompatibleAt P Q a₀ a₀',
        Equivalent P Q,
        ∃ m a a' : ℤ, 0 < m ∧ m = a * d ∧ m = a' * d' ∧ CompatibleAt P Q a a'] := by
  tfae_have 1 → 2 := equivalent_of_lcm_compatible hd hd' ha₀ ha₀'
  tfae_have 2 → 3 := exists_compatible_of_equivalent hd hd'
  tfae_have 3 → 1 := lcm_compatible_of_exists_compatible hd hd' ha₀ ha₀'
  tfae_have 2 → 1 := lcm_compatible_of_equivalent hd hd' ha₀ ha₀'
  tfae_have 3 → 2 := fun h => equivalent_of_exists_compatible hd hd' h
  tfae_finish

end Quadruple

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
