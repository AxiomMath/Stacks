module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic

/-!
# The invertible sheaves of pairs are the `n`-torsion of the Picard group

A pair on a scheme `S`, in the sense of Tag 040Q, is an invertible sheaf of `𝒪_S`-modules
together with a trivialization of its `n`-th tensor power
(`AlgebraicGeometry.TrivializedPower`). Tag 040Q's surjectivity step needs to know which Picard
classes occur as the class of the invertible sheaf of a pair, and the answer is: exactly the
`n`-torsion classes.

Two inputs do all the work. `AlgebraicGeometry.exists_trivializedPower_sheaf_iff` says that an
invertible sheaf carries a trivialization of its `n`-th tensor power exactly when that power is
trivial; and the Picard group of Tag 01CX, `Stacks.SheafOfModules.Picard.PicardGroup`, is the
group of isomorphism classes of invertible sheaves with addition the tensor product sheaf, so
`n` times a class is the class of the `n`-th tensor power and a class vanishes exactly when the
sheaf is trivial. Composing the two turns "the `n`-th power is trivial" into "the class is
`n`-torsion".

## Main results

* `AlgebraicGeometry.classOf_unit_eq_zero`: the class of the structure sheaf is `0`.
* `AlgebraicGeometry.classOf_eq_zero_iff`: a Picard class vanishes exactly when the invertible
  sheaf is isomorphic to the structure sheaf.
* `AlgebraicGeometry.classOf_tensorPower`: the class of the `n`-th tensor power of an invertible
  sheaf is `n` times its class.
* `AlgebraicGeometry.exists_trivializedPower_classOf_of_nsmul_eq_zero`: **an `n`-torsion class
  of the Picard group of `S` is the class of the invertible sheaf of a pair.** This is the
  direction Tag 040Q's surjectivity step consumes.
* `AlgebraicGeometry.exists_trivializedPower_classOf_iff`: the same statement as an equivalence,
  together with its easy converse.

## Implementation notes

The Picard group is instantiated at `O := S.presheaf` and
`hO := AlgebraicGeometry.ringSheafCond S`, which is the spelling
`AlgebraicGeometry.TrivializedPower` is stated over; its `sheaf` field then lands in
`AlgebraicGeometry.ringSheaf S`, which is `Stacks.SheafOfModules.Picard.classOf`'s argument type
by `rfl`, so nothing has to be transported. The three sheafification side conditions of
`Stacks.SheafOfModules.Picard.PicardGroup` — the two for the tensor product sheaf and the
slice-wise `[∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat]` for Tag 040B — are all
instances for the site of opens of a scheme, so no hypothesis is carried.

`AlgebraicGeometry.classOf_tensorPower` is proved by induction on `n` from
`Stacks.SheafOfModules.Picard.classOf_tensor` and the successor comparison
`Stacks.SheafOfModules.Invertible.tensorPowerSuccIso`, with the cast
`((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1` absorbed by
`Stacks.SheafOfModules.Invertible.tensorPowerReindex` rather than by rewriting inside
`classOf`, whose invertibility argument depends on the exponent. The library's existing
`Stacks.Picard.classOf_tensorPower` is not this statement: it is stated for the large carrier
`Stacks.SheafOfModules.PicardGroup` and for
`Stacks.SheafOfModules.TensorPower.tensorPower`, whereas the pairs of Tag 040Q are stated over
`Stacks.SheafOfModules.Invertible.tensorPower` and the group produced by Tag 040E is
`Stacks.SheafOfModules.Picard.PicardGroup`. The two tensor powers are the same sheaf —
`Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower`, by `rfl` — which is what lets
`AlgebraicGeometry.isInvertible_tensorPower` below borrow invertibility of the power from the
other development; the two Picard carriers are not bridged.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerSuccIso tensorPowerReindex
  tensorProductLeftUnitor)
open Stacks.SheafOfModules.Picard (PicardGroup classOf classOf_eq_classOf_iff classOf_tensor
  exists_classOf_eq)

universe u

namespace AlgebraicGeometry

/-- Every integer tensor power of an invertible sheaf of modules on a scheme is invertible. The
two developments of the integer tensor power agree by
`Stacks.SheafOfModules.Invertible.tensorPower_eq_tensorPower`, so this is
`Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower` read at the power
`AlgebraicGeometry.TrivializedPower` is stated over. -/
public theorem isInvertible_tensorPower (S : Scheme.{u})
    (L : SheafOfModules.{u} (ringSheaf S))
    [IsInvertible S.presheaf (ringSheafCond S) L] (n : ℤ) :
    IsInvertible S.presheaf (ringSheafCond S) (tensorPower S.presheaf (ringSheafCond S) L n) :=
  Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower S.presheaf (ringSheafCond S) L n

/-- The class of the structure sheaf in the Picard group of `S` is zero: the structure sheaf is
a unit for the tensor product sheaf, so its class is a neutral element for addition. -/
public theorem classOf_unit_eq_zero (S : Scheme.{u}) :
    classOf S.presheaf (ringSheafCond S) (SheafOfModules.unit (ringSheaf S))
      (Stacks.SheafOfModules.isInvertible_unit S.presheaf (ringSheafCond S)) = 0 := by
  have hU : IsInvertible S.presheaf (ringSheafCond S) (SheafOfModules.unit (ringSheaf S)) :=
    Stacks.SheafOfModules.isInvertible_unit S.presheaf (ringSheafCond S)
  have hUU : IsInvertible S.presheaf (ringSheafCond S)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
          (ringSheafCond S)⟩).obj (SheafOfModules.unit (ringSheaf S))).obj
          (SheafOfModules.unit (ringSheaf S)))) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf S.presheaf (ringSheafCond S) _ _
  have he := (classOf_eq_classOf_iff S.presheaf (ringSheafCond S) _ _ hUU hU).2
    ⟨tensorProductLeftUnitor S.presheaf (ringSheafCond S) (SheafOfModules.unit (ringSheaf S))⟩
  exact add_eq_left.mp ((classOf_tensor S.presheaf (ringSheafCond S) _ _ hU hU hUU).trans he)

/-- **A Picard class vanishes exactly when the invertible sheaf is trivial.** Equality of
classes is isomorphism of sheaves, and zero is the class of the structure sheaf. -/
public theorem classOf_eq_zero_iff (S : Scheme.{u}) (L : SheafOfModules.{u} (ringSheaf S))
    (hL : IsInvertible S.presheaf (ringSheafCond S) L) :
    classOf S.presheaf (ringSheafCond S) L hL = 0 ↔
      Nonempty (L ≅ SheafOfModules.unit (ringSheaf S)) := by
  have hiff := classOf_eq_classOf_iff S.presheaf (ringSheafCond S) L
    (SheafOfModules.unit (ringSheaf S)) hL
    (Stacks.SheafOfModules.isInvertible_unit S.presheaf (ringSheafCond S))
  exact ⟨fun h => hiff.1 (h.trans (classOf_unit_eq_zero S).symm),
    fun h => (hiff.2 h).trans (classOf_unit_eq_zero S)⟩

/-- **The `n`-th tensor power of an invertible sheaf has `n` times its Picard class.** Addition
of Picard classes is the tensor product sheaf (Tag 01CX) and the tensor power satisfies
`L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` (Tag 01CU), so this is an induction on `n` whose base case is the
vanishing of the class of the structure sheaf. -/
public theorem classOf_tensorPower (S : Scheme.{u}) (L : SheafOfModules.{u} (ringSheaf S))
    [hL : IsInvertible S.presheaf (ringSheafCond S) L] (n : ℕ) :
    classOf S.presheaf (ringSheafCond S) (tensorPower S.presheaf (ringSheafCond S) L (n : ℤ))
        (isInvertible_tensorPower S L (n : ℤ)) =
      n • classOf S.presheaf (ringSheafCond S) L hL := by
  induction n with
  | zero =>
      have h0 : classOf S.presheaf (ringSheafCond S)
          (tensorPower S.presheaf (ringSheafCond S) L ((0 : ℕ) : ℤ))
            (isInvertible_tensorPower S L ((0 : ℕ) : ℤ)) =
          classOf S.presheaf (ringSheafCond S) (SheafOfModules.unit (ringSheaf S))
            (Stacks.SheafOfModules.isInvertible_unit S.presheaf (ringSheafCond S)) :=
        (classOf_eq_classOf_iff S.presheaf (ringSheafCond S) _ _ _ _).2 ⟨Iso.refl _⟩
      exact (h0.trans (classOf_unit_eq_zero S)).trans (zero_nsmul _).symm
  | succ k ih =>
      have := isInvertible_tensorPower S L (k : ℤ)
      have hPL : IsInvertible S.presheaf (ringSheafCond S)
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
              (ringSheafCond S)⟩).obj
              (tensorPower S.presheaf (ringSheafCond S) L (k : ℤ))).obj L)) :=
        Stacks.SheafOfModules.isInvertible_tensorSheaf S.presheaf (ringSheafCond S) _ _
      calc classOf S.presheaf (ringSheafCond S)
              (tensorPower S.presheaf (ringSheafCond S) L ((k + 1 : ℕ) : ℤ))
              (isInvertible_tensorPower S L ((k + 1 : ℕ) : ℤ))
          = classOf S.presheaf (ringSheafCond S)
              ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
                Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
                  (ringSheafCond S)⟩).obj
                  (tensorPower S.presheaf (ringSheafCond S) L (k : ℤ))).obj L)) hPL :=
            ((classOf_eq_classOf_iff S.presheaf (ringSheafCond S) _ _ hPL _).2
              ⟨tensorPowerSuccIso S.presheaf (ringSheafCond S) L (k : ℤ) ≪≫
                tensorPowerReindex S.presheaf (ringSheafCond S) L (by push_cast; ring)⟩).symm
        _ = classOf S.presheaf (ringSheafCond S)
                (tensorPower S.presheaf (ringSheafCond S) L (k : ℤ))
                (isInvertible_tensorPower S L (k : ℤ)) +
              classOf S.presheaf (ringSheafCond S) L hL :=
            (classOf_tensor S.presheaf (ringSheafCond S) _ _ _ hL hPL).symm
        _ = k • classOf S.presheaf (ringSheafCond S) L hL +
              classOf S.presheaf (ringSheafCond S) L hL := by rw [ih]
        _ = (k + 1) • classOf S.presheaf (ringSheafCond S) L hL := (succ_nsmul _ k).symm

/-- An invertible sheaf has `n`-torsion Picard class exactly when its `n`-th tensor power is
trivial. -/
private theorem nsmul_classOf_eq_zero_iff (S : Scheme.{u}) (L : SheafOfModules.{u} (ringSheaf S))
    [hL : IsInvertible S.presheaf (ringSheafCond S) L] (n : ℕ) :
    n • classOf S.presheaf (ringSheafCond S) L hL = 0 ↔
      Nonempty (tensorPower S.presheaf (ringSheafCond S) L (n : ℤ) ≅
        SheafOfModules.unit (ringSheaf S)) := by
  rw [← classOf_tensorPower S L n]
  exact classOf_eq_zero_iff S _ (isInvertible_tensorPower S L (n : ℤ))

/-- **Stacks Project, Tag 040Q, surjectivity onto the `n`-torsion.** An `n`-torsion class of the
Picard group of `S` is the class of the invertible sheaf of a pair: choose an invertible sheaf
with that class, note that the class of its `n`-th tensor power is `n` times it and hence zero,
so that power is trivial, and `AlgebraicGeometry.exists_trivializedPower_sheaf_iff` produces the
pair. -/
public theorem exists_trivializedPower_classOf_of_nsmul_eq_zero (S : Scheme.{u}) (n : ℕ)
    (x : PicardGroup S.presheaf (ringSheafCond S)) (hx : n • x = 0) :
    ∃ P : TrivializedPower S n,
      classOf S.presheaf (ringSheafCond S) P.sheaf P.invertible = x := by
  obtain ⟨L, hL, rfl⟩ := exists_classOf_eq S.presheaf (ringSheafCond S) x
  obtain ⟨P, hP⟩ := (exists_trivializedPower_sheaf_iff S n L hL).2
    ((nsmul_classOf_eq_zero_iff S L n).1 hx)
  exact ⟨P, (classOf_eq_classOf_iff S.presheaf (ringSheafCond S) _ _ _ hL).2 ⟨eqToIso hP⟩⟩

/-- **Stacks Project, Tag 040Q, the Picard classes of pairs.** A class of the Picard group of
`S` is the class of the invertible sheaf of a pair exactly when it is `n`-torsion. The forward
direction is the trivialization of the `n`-th tensor power read through
`AlgebraicGeometry.classOf_tensorPower`; the converse is
`AlgebraicGeometry.exists_trivializedPower_classOf_of_nsmul_eq_zero`. -/
public theorem exists_trivializedPower_classOf_iff (S : Scheme.{u}) (n : ℕ)
    (x : PicardGroup S.presheaf (ringSheafCond S)) :
    (∃ P : TrivializedPower S n,
        classOf S.presheaf (ringSheafCond S) P.sheaf P.invertible = x) ↔ n • x = 0 := by
  refine ⟨?_, exists_trivializedPower_classOf_of_nsmul_eq_zero S n x⟩
  rintro ⟨P, rfl⟩
  let := P.invertible
  exact (nsmul_classOf_eq_zero_iff S P.sheaf n).2 ⟨P.trivialization⟩

end AlgebraicGeometry

end
