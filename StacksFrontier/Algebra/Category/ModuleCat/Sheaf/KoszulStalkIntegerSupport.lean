module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalkIntegerBridge
public import StacksCore.Tactic.StacksAttribute

/-!
# A chain complex supported in nonnegative degrees is determined by its nonnegative part

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/KoszulStalkIntegerBridge.lean` builds the
`ℤ`-indexed form `Stacks.ChainComplexIntBridge.natToInt K` of an `ℕ`-indexed chain complex `K`,
by extending by zero along `ComplexShape.embeddingDownNat` and restoring homological indexing
along `ComplexShape.embeddingDownIntUpInt`. That construction goes one way only: given `K` it
produces a `ℤ`-indexed complex. What several consumers meet is the opposite situation — a
`ℤ`-indexed complex `L` which happens to vanish in negative degrees, which is to be recognised
as the zero-extension of an `ℕ`-indexed complex it is compared with degreewise.

Mathlib has no such recognition principle. `HomologicalComplex.IsStrictlySupported` records
that a complex vanishes outside the range of an embedding, and `TruncGE`/`TruncLE` give
`isIso_πTruncGE_iff` and `isIso_ιTruncLE_iff` for the canonical maps to and from the
truncations, but there is no isomorphism `L ≅ (L.restriction e).extend e` for a strictly
supported `L`, and nothing that builds an isomorphism out of a comparison given only in the
degrees the embedding hits.

This file supplies it, in the two forms a consumer wants: a comparison of two `ℤ`-indexed
complexes which both vanish in negative degrees
(`Stacks.ChainComplexIntBridge.isoOfNonnegComparison`), and the specialization in which the
second one is `natToInt K` (`Stacks.ChainComplexIntBridge.isoNatToInt`).

## Main definitions

* `Stacks.ChainComplexIntBridge.nonnegComparison`: the degreewise isomorphism assembled from a
  family given in nonnegative degrees and from the vanishing in negative degrees.
* `Stacks.ChainComplexIntBridge.isoOfNonnegComparison`: **two `ℤ`-indexed chain complexes that
  vanish in negative degrees are isomorphic as soon as their nonnegative degrees are identified
  compatibly with the differentials.** Only the differentials between consecutive nonnegative
  degrees have to be matched; the remaining squares are automatic.
* `Stacks.ChainComplexIntBridge.isoNatToInt`: the same statement with the second complex taken
  to be `natToInt K`, so that the hypothesis is a comparison with the `ℕ`-indexed complex `K`
  itself.

## Main results

* `Stacks.ChainComplexIntBridge.natToInt_d_natCast`: the differential of `natToInt K` between
  consecutive nonnegative degrees is that of `K`, conjugated by `natToIntXIso`. This is the
  computation `natToInt_exactAt_iff` of the bridge file did not need and `isoNatToInt` does.
* `Stacks.ChainComplexIntBridge.isoOfNonnegComparison_hom_f_natCast` and
  `isoNatToInt_hom_f_natCast`: in degree `(n : ℤ)` the isomorphism is the given comparison, with
  no transport. This is what makes the isomorphisms usable in a formula about a specific degree.

## Implementation notes

**Why the hypothesis is only about consecutive nonnegative degrees.** The differential squares
of `ComplexShape.down ℤ` are indexed by pairs `(j + 1, j)`. If `j < 0` the target of both
composites is a zero object, so the square commutes for want of any other morphism; this is
`CategoryTheory.Limits.IsZero.eq_of_tgt` and needs no hypothesis. So the only squares carrying
content are those with `0 ≤ j`, which are exactly the ones `hd` below speaks about.

**The degreewise isomorphism is defined by a match on `Int`, not by `dite`.** Writing
`if 0 ≤ i then … else …` forces the nonnegative branch to transport along
`Int.toNat_of_nonneg`, and every later use of the isomorphism then carries an `eqToHom` that has
to be cleared. Matching on the two constructors of `Int` instead makes
`nonnegComparison … (n : ℤ) = α n` hold by `rfl`, because the pattern `Int.ofNat n` and the
coercion `((n : ℕ) : ℤ)` are the same term. That is the whole reason the `_hom_f_natCast` lemmas
below are `rfl`.

**Universes and generality.** Everything here is universe polymorphic in the ambient category
`C`, which needs only `HasZeroMorphisms` — not `HasZeroObject`, not additivity, not homology.
The vanishing in negative degrees is taken as a hypothesis in the form `IsZero (L.X n)` rather
than through `HomologicalComplex.IsStrictlySupported`, because the consumers obtain it from a
vanishing statement about sections and not from an embedding.

**No `@[stacks]` attribute.** This is homological algebra with no Stacks content: it asserts
nothing about sheaves, Koszul complexes or regular sequences. It is filed next to
`KoszulStalkIntegerBridge.lean` because it extends that file's `Stacks.ChainComplexIntBridge`
namespace and specializes to its `natToInt`, and splitting the namespace across two directories
would be worse than hosting generic material here, which that file already does.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 063C](https://stacks.math.columbia.edu/tag/063C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ChainComplexIntBridge

section Nonneg

variable {C : Type*} [Category C] [HasZeroMorphisms C] {L M : ChainComplex C ℤ}

/-- The degreewise comparison of two `ℤ`-indexed chain complexes, assembled from a family of
isomorphisms in nonnegative degrees and from the vanishing of both complexes in negative
degrees. -/
noncomputable def nonnegComparison (α : ∀ n : ℕ, L.X (n : ℤ) ≅ M.X (n : ℤ))
    (hL : ∀ n : ℤ, n < 0 → IsZero (L.X n)) (hM : ∀ n : ℤ, n < 0 → IsZero (M.X n)) :
    ∀ i : ℤ, L.X i ≅ M.X i
  | (n : ℕ) => α n
  | .negSucc n => (hL _ (Int.negSucc_lt_zero n)).iso (hM _ (Int.negSucc_lt_zero n))

/-- In a nonnegative degree the comparison is the given isomorphism, with no transport. -/
theorem nonnegComparison_natCast (α : ∀ n : ℕ, L.X (n : ℤ) ≅ M.X (n : ℤ))
    (hL : ∀ n : ℤ, n < 0 → IsZero (L.X n)) (hM : ∀ n : ℤ, n < 0 → IsZero (M.X n)) (n : ℕ) :
    nonnegComparison α hL hM (n : ℤ) = α n :=
  rfl

/-- **Two `ℤ`-indexed chain complexes which vanish in negative degrees are isomorphic as soon as
their nonnegative degrees are identified compatibly with the differentials.** Only the squares
between consecutive nonnegative degrees are an obligation: in every other square the target is a
zero object. -/
noncomputable def isoOfNonnegComparison (α : ∀ n : ℕ, L.X (n : ℤ) ≅ M.X (n : ℤ))
    (hd : ∀ n : ℕ, (α (n + 1)).hom ≫ M.d ((n + 1 : ℕ) : ℤ) (n : ℤ) =
      L.d ((n + 1 : ℕ) : ℤ) (n : ℤ) ≫ (α n).hom)
    (hL : ∀ n : ℤ, n < 0 → IsZero (L.X n)) (hM : ∀ n : ℤ, n < 0 → IsZero (M.X n)) :
    L ≅ M :=
  HomologicalComplex.Hom.isoOfComponents (nonnegComparison α hL hM) (fun i j hij => by
    rcases Int.lt_or_le j 0 with hj | hj
    · exact (hM j hj).eq_of_tgt _ _
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
      obtain rfl : i = ((n + 1 : ℕ) : ℤ) := by
        rw [ComplexShape.down_Rel] at hij; omega
      rw [nonnegComparison_natCast, nonnegComparison_natCast]
      exact hd n)

/-- In degree `(n : ℤ)` the isomorphism is the given comparison. -/
theorem isoOfNonnegComparison_hom_f_natCast (α : ∀ n : ℕ, L.X (n : ℤ) ≅ M.X (n : ℤ))
    (hd : ∀ n : ℕ, (α (n + 1)).hom ≫ M.d ((n + 1 : ℕ) : ℤ) (n : ℤ) =
      L.d ((n + 1 : ℕ) : ℤ) (n : ℤ) ≫ (α n).hom)
    (hL : ∀ n : ℤ, n < 0 → IsZero (L.X n)) (hM : ∀ n : ℤ, n < 0 → IsZero (M.X n)) (n : ℕ) :
    (isoOfNonnegComparison α hd hL hM).hom.f (n : ℤ) = (α n).hom :=
  rfl

end Nonneg

section NatToInt

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

/-- **The differential of `natToInt K` between consecutive nonnegative degrees** is the
differential of `K`, conjugated by the degreewise identification. -/
theorem natToInt_d_natCast (K : ChainComplex C ℕ) (n : ℕ) :
    (natToInt K).d ((n + 1 : ℕ) : ℤ) (n : ℤ) =
      (natToIntXIso K (n + 1)).hom ≫ K.d (n + 1) n ≫ (natToIntXIso K n).inv := by
  have h := (K.extend ComplexShape.embeddingDownNat).restriction_d_eq
      ComplexShape.embeddingDownIntUpInt (i := ((n + 1 : ℕ) : ℤ)) (j := ((n : ℕ) : ℤ))
      (i' := -((n + 1 : ℕ) : ℤ)) (j' := -((n : ℕ) : ℤ)) rfl rfl
  rw [K.extend_d_eq ComplexShape.embeddingDownNat (i := n + 1) (j := n)
    (i' := -((n + 1 : ℕ) : ℤ)) (j' := -((n : ℕ) : ℤ)) rfl rfl] at h
  simp only [Category.assoc] at h
  simp only [natToInt, natToIntXIso, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  exact h

/-- **A `ℤ`-indexed chain complex which vanishes in negative degrees is the zero-extension of an
`ℕ`-indexed one**, as soon as its nonnegative degrees are identified with that complex's degrees
compatibly with the differentials. This is the recognition principle Mathlib lacks for
`HomologicalComplex.IsStrictlySupported`. -/
noncomputable def isoNatToInt (L : ChainComplex C ℤ) (K : ChainComplex C ℕ)
    (α : ∀ n : ℕ, L.X (n : ℤ) ≅ K.X n)
    (hd : ∀ n : ℕ, (α (n + 1)).hom ≫ K.d (n + 1) n =
      L.d ((n + 1 : ℕ) : ℤ) (n : ℤ) ≫ (α n).hom)
    (hL : ∀ n : ℤ, n < 0 → IsZero (L.X n)) :
    L ≅ natToInt K :=
  isoOfNonnegComparison (fun n => (α n).trans (natToIntXIso K n).symm)
    (fun n => by
      rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, natToInt_d_natCast]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hd n, Category.assoc])
    hL (fun n hn => isZero_natToInt_X K n hn)

/-- In degree `(n : ℤ)` the isomorphism with the zero-extension is the given comparison,
followed by the degreewise identification of the zero-extension. -/
theorem isoNatToInt_hom_f_natCast (L : ChainComplex C ℤ) (K : ChainComplex C ℕ)
    (α : ∀ n : ℕ, L.X (n : ℤ) ≅ K.X n)
    (hd : ∀ n : ℕ, (α (n + 1)).hom ≫ K.d (n + 1) n =
      L.d ((n + 1 : ℕ) : ℤ) (n : ℤ) ≫ (α n).hom)
    (hL : ∀ n : ℤ, n < 0 → IsZero (L.X n)) (n : ℕ) :
    (isoNatToInt L K α hd hL).hom.f (n : ℤ) = (α n).hom ≫ (natToIntXIso K n).inv :=
  rfl

/-- The composite of `isoNatToInt` with the degreewise identification of the zero-extension
returns the given comparison. This is the form in which a formula about the germ of a specific
section in a specific degree is checked. -/
theorem natToIntXIso_hom_isoNatToInt_hom_f (L : ChainComplex C ℤ) (K : ChainComplex C ℕ)
    (α : ∀ n : ℕ, L.X (n : ℤ) ≅ K.X n)
    (hd : ∀ n : ℕ, (α (n + 1)).hom ≫ K.d (n + 1) n =
      L.d ((n + 1 : ℕ) : ℤ) (n : ℤ) ≫ (α n).hom)
    (hL : ∀ n : ℤ, n < 0 → IsZero (L.X n)) (n : ℕ) :
    (isoNatToInt L K α hd hL).hom.f (n : ℤ) ≫ (natToIntXIso K n).hom = (α n).hom := by
  rw [isoNatToInt_hom_f_natCast, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end NatToInt

section ModuleToAb

variable {R : Type u} [Ring R]

/-- **The differential of the bridged complex between consecutive nonnegative degrees** is the
differential of the `ℕ`-indexed complex of modules, with the module structure forgotten,
conjugated by the degreewise identification. -/
theorem natToIntAb_d_natCast (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    ((natToIntAbFunctor R).obj K).d ((n + 1 : ℕ) : ℤ) (n : ℤ) =
      (natToIntAbXIso K (n + 1)).hom ≫
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map (K.d (n + 1) n) ≫
          (natToIntAbXIso K n).inv := by
  have h : ((natToIntAbFunctor R).obj K).d ((n + 1 : ℕ) : ℤ) (n : ℤ) =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        ((natToInt K).d ((n + 1 : ℕ) : ℤ) (n : ℤ)) := rfl
  rw [h, natToInt_d_natCast, Functor.map_comp, Functor.map_comp]
  rfl

/-- **A `ℤ`-indexed chain complex of abelian groups which vanishes in negative degrees is the
bridged form of an `ℕ`-indexed chain complex of modules**, as soon as its nonnegative degrees
are identified with the underlying groups of that complex compatibly with the differentials.
This is the shape in which the `ℤ`-indexed, `AddCommGrpCat`-valued consumers of the Koszul
stalk comparison meet the statement: `natToIntAbFunctor_obj` rewrites the target into the
`extend`-then-`restriction`-then-`forget₂` spelling they use. -/
noncomputable def isoNatToIntAb (L : ChainComplex AddCommGrpCat.{u} ℤ)
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (α : ∀ n : ℕ, L.X (n : ℤ) ≅ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj (K.X n))
    (hd : ∀ n : ℕ, (α (n + 1)).hom ≫
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map (K.d (n + 1) n) =
      L.d ((n + 1 : ℕ) : ℤ) (n : ℤ) ≫ (α n).hom)
    (hL : ∀ n : ℤ, n < 0 → IsZero (L.X n)) :
    L ≅ (natToIntAbFunctor R).obj K :=
  isoOfNonnegComparison (fun n => (α n).trans (natToIntAbXIso K n).symm)
    (fun n => by
      rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, natToIntAb_d_natCast]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hd n, Category.assoc])
    hL (fun n hn => isZero_natToIntAb_X K n hn)

/-- In degree `(n : ℤ)` the isomorphism with the bridged complex is the given comparison,
followed by the degreewise identification. -/
theorem isoNatToIntAb_hom_f_natCast (L : ChainComplex AddCommGrpCat.{u} ℤ)
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (α : ∀ n : ℕ, L.X (n : ℤ) ≅ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj (K.X n))
    (hd : ∀ n : ℕ, (α (n + 1)).hom ≫
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map (K.d (n + 1) n) =
      L.d ((n + 1 : ℕ) : ℤ) (n : ℤ) ≫ (α n).hom)
    (hL : ∀ n : ℤ, n < 0 → IsZero (L.X n)) (n : ℕ) :
    (isoNatToIntAb L K α hd hL).hom.f (n : ℤ) = (α n).hom ≫ (natToIntAbXIso K n).inv :=
  rfl

/-- The composite of `isoNatToIntAb` with the degreewise identification returns the given
comparison. This is the form in which a formula about the germ of a specific section in a
specific degree is checked. -/
theorem natToIntAbXIso_hom_isoNatToIntAb_hom_f (L : ChainComplex AddCommGrpCat.{u} ℤ)
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (α : ∀ n : ℕ, L.X (n : ℤ) ≅ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj (K.X n))
    (hd : ∀ n : ℕ, (α (n + 1)).hom ≫
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map (K.d (n + 1) n) =
      L.d ((n + 1 : ℕ) : ℤ) (n : ℤ) ≫ (α n).hom)
    (hL : ∀ n : ℤ, n < 0 → IsZero (L.X n)) (n : ℕ) :
    (isoNatToIntAb L K α hd hL).hom.f (n : ℤ) ≫ (natToIntAbXIso K n).hom = (α n).hom := by
  rw [isoNatToIntAb_hom_f_natCast, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end ModuleToAb

end Stacks.ChainComplexIntBridge

end
