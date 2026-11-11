module

public import Mathlib.CategoryTheory.Triangulated.Generators
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# Operations on full subcategories along an exact functor

Let `F : C ⥤ D` be an exact functor of pretriangulated categories. For a full subcategory `A` of
`C`, write `F(A)` for the full subcategory of the objects `F X` with `X ∈ A`. This file proves
Derived Categories, Remark 13.35.5 ([Stacks, Tag 0FX5]): the operations of
Derived Categories, Section 13.35 are compatible with `F`,
`F(A[a, b]) = F(A)[a, b]`, `F(smd(A)) ⊂ smd(F(A))`, `F(add(A)) ⊂ add(F(A))`,
`F(A ⋆ B) ⊂ F(A) ⋆ F(B)` and `F(A^{⋆ n}) ⊂ F(A)^{⋆ n}`.

It then composes these: if `F` carries the objects of a property `P` of `C` into a property `Q`
of `D`, then `F` carries the explicit subcategory `smd(add(P[c, d])^{⋆ n})` of `C` into the
subcategory `smd(add(Q[c, d])^{⋆ n})` of `D`, **with the same shift interval `[c, d]` and the
same number `n` of extensions on both sides**, the form in which the explicit subcategories of
[Stacks, Tag 0FX9] are used.

## The argument

Each of the four closure operations making up `smd(add(−[c, d])^{⋆ n})` transfers separately,
and the composite statement is just their composition.

* *Shifts.* An object `X` of `P[c, d]` has `X⟦i⟧ ≅ Y` with `Y ∈ P` and `i ∈ [c, d]`. The
  commutation isomorphism of `F` with the shift turns this into `(F X)⟦i⟧ ≅ F Y`, with
  `F Y ∈ Q` by hypothesis and the *same* `i`. This is the only step that touches the interval,
  and it preserves it on the nose; no shift outside `[c, d]` is ever produced.
* *Finite direct sums.* The inverse image under `F` of a subcategory closed under binary
  products is again closed under binary products, because `X ⨯ Y` is the middle vertex of a
  distinguished triangle with vanishing third map, which `F` carries to a distinguished triangle
  with vanishing third map, hence to a split one.
* *Extensions.* An extension `A ⟶ X ⟶ B ⟶ A⟦1⟧` is carried by `F` to a distinguished triangle
  `F A ⟶ F X ⟶ F B ⟶ (F A)⟦1⟧`, so `X ∈ A ⋆ B` gives `F X ∈ F(A) ⋆ F(B)`; iterating gives the
  same count `n` of extensions on both sides.
* *Direct summands.* The inverse image under `F` of a subcategory stable under retracts is
  stable under retracts, a functor carrying a retract diagram to a retract diagram.

## Main results

* `isoClosure_strictMap_biSup_shift_eq_and_strictMap_operations_le` (in the
  `Stacks.TriangulatedGenerators` namespace): **[Stacks, Tag 0FX5]**, the five compatibilities.
* `retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le`: their composite for
  `smd(add(P[c, d])^{⋆ n})`, with the interval and the number of extensions tracked.

## Implementation notes

The shifted family `P[c, d]` is spelled `⨆ i ∈ Set.Icc c d, P.isoClosure.shift i`, as in
`StacksFrontier/CategoryTheory/Triangulated/Generators.lean`; `ObjectProperty.shift` is the inverse
image under the shift functor, and the `isoClosure` is what makes the family insensitive to `P`
not being closed under isomorphisms. The source's `smd` is
`CategoryTheory.ObjectProperty.retractClosure`, `add` is
`CategoryTheory.ObjectProperty.binaryProductsClosure` and `⋆` iterated `n` times is
`CategoryTheory.ObjectProperty.extensionProductIter`.

The image `F(A)` is `CategoryTheory.ObjectProperty.strictMap`, the literal image. The source's
equality `F(A[a, b]) = F(A)[a, b]` holds only up to isomorphism (`F(Y⟦-i⟧)` is isomorphic, not
equal, to `(F Y)⟦-i⟧`), so it is stated between closures under isomorphisms; it is proved for an
arbitrary set `S ⊆ ℤ` of shifts, which covers every interval `[a, b]` with
`-∞ ≤ a ≤ b ≤ ∞`. The other four statements are inclusions of the literal image, and their right
hand sides are closed under isomorphisms. Mathlib's `A.extensionProductIter n` has `n + 1`
factors, so the statement for every `n : ℕ` is the source's `F(A^{⋆ n}) ⊂ F(A)^{⋆ n}` for
every `n ≥ 1`.

Neither `[IsTriangulated C]` nor `[IsTriangulated D]` is assumed: no step needs the octahedral
property, since the iterated extension product is taken in the fixed bracketing of
`CategoryTheory.ObjectProperty.extensionProductIter_succ` and never reassociated.

The unbounded-shift form of the same transfer, with `P.shiftClosure ℤ` in place of `P[c, d]`,
is `Stacks.TriangulatedGenerators.triangEnvelopeIter_inverseImage_of_le`; it cannot supply this
statement, since passing through `ObjectProperty.triangEnvelopeIter` forgets the interval and
`CategoryTheory.ObjectProperty.triangEnvelopeIter_eq_iSup_retractClosure_extensionProductIter`
([Stacks, Tag 0FX9]) only recovers *some* window `[-m, m]`, with no bound on `m`.

## References

* [Stacks Project, Tag 0FX5](https://stacks.math.columbia.edu/tag/0FX5)
* [Stacks Project, Tag 0FX9](https://stacks.math.columbia.edu/tag/0FX9)
* [Stacks Project, Tag 0FX4](https://stacks.math.columbia.edu/tag/0FX4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

namespace Stacks.TriangulatedGenerators

/-! ### Transfer of the closure operations along a functor -/

section Shifts

variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]

/-- The shifts of `P` in a window transfer along a functor commuting with the shift **into the
same window**: if `X⟦i⟧ ≅ Y` with `Y` in `P` and `i ∈ [c, d]`, then the commutation isomorphism
of `F` with the shift gives `(F X)⟦i⟧ ≅ F Y` with `F Y` in `Q` and the same `i`. -/
private lemma biSup_shift_isoClosure_inverseImage_of_le {P : ObjectProperty C}
    {Q : ObjectProperty D} (h : ∀ ⦃X : C⦄, P X → Q (F.obj X)) (c d : ℤ) :
    (⨆ i ∈ Set.Icc c d, P.isoClosure.shift i) ≤
      (⨆ i ∈ Set.Icc c d, Q.isoClosure.shift i).inverseImage F := by
  refine iSup₂_le fun i hi X hX => ?_
  obtain ⟨Y, hY, ⟨e⟩⟩ := hX
  simp only [prop_inverseImage_iff, prop_iSup_iff]
  exact ⟨i, hi, F.obj Y, h hY, ⟨((F.commShiftIso i).app X).symm ≪≫ F.mapIso e⟩⟩

/-- **Shifts commute with images along a functor commuting with the shift.** For a set `S` of
integers, the closure under isomorphisms of the image `F(P[S])` of the shifts
`P[S] = {X : X⟦i⟧ ≅ Y, Y ∈ P, i ∈ S}` is the shifted family `F(P)[S]` of the image `F(P)`.
For `S = [a, b] ∩ ℤ` with `-∞ ≤ a ≤ b ≤ ∞` this is `F(P[a, b]) = F(P)[a, b]`, the two sides
being taken up to isomorphism. -/
lemma isoClosure_strictMap_biSup_shift_isoClosure (P : ObjectProperty C) (S : Set ℤ) :
    ((⨆ i ∈ S, P.isoClosure.shift i).strictMap F).isoClosure =
      ⨆ i ∈ S, (P.strictMap F).isoClosure.shift i := by
  refine le_antisymm ?_ (iSup₂_le fun i hi Z hZ => ?_)
  · rintro Z ⟨_, ⟨X, hX⟩, ⟨e⟩⟩
    simp only [prop_iSup_iff] at hX ⊢
    obtain ⟨i, hi, Y, hY, ⟨e'⟩⟩ := hX
    exact ⟨i, hi, F.obj Y, .mk Y hY,
      ⟨(shiftFunctor D i).mapIso e ≪≫ ((F.commShiftIso i).app X).symm ≪≫ F.mapIso e'⟩⟩
  · obtain ⟨_, ⟨Y, hY⟩, ⟨e⟩⟩ := hZ
    refine ⟨F.obj ((shiftFunctor C (-i)).obj Y), .mk _ ?_, ⟨?_⟩⟩
    · simp only [prop_iSup_iff]
      exact ⟨i, hi, Y, hY, ⟨(shiftFunctorCompIsoId C (-i) i (neg_add_cancel i)).app Y⟩⟩
    · exact ((shiftFunctorCompIsoId D i (-i) (add_neg_cancel i)).app Z).symm ≪≫
        (shiftFunctor D (-i)).mapIso e ≪≫ ((F.commShiftIso (-i)).app Y).symm

end Shifts

section Retracts

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

/-- The image along a functor of the direct summands of objects of `P` consists of direct
summands of objects of the image: `F(smd(P)) ⊂ smd(F(P))`. -/
lemma strictMap_retractClosure_le (P : ObjectProperty C) :
    P.retractClosure.strictMap F ≤ (P.strictMap F).retractClosure := by
  rintro _ ⟨X, ⟨Y, hY, ⟨r⟩⟩⟩
  exact ⟨F.obj Y, .mk Y hY, ⟨r.map F⟩⟩

end Retracts

section Transfer

variable {C D : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- The extension product transfers along an exact functor: an extension of an object of `A₂` by
an object of `A₁` is carried to an extension of an object of `B₂` by an object of `B₁`, since an
exact functor carries a distinguished triangle to a distinguished triangle. -/
private lemma extensionProduct_inverseImage_of_le {A₁ A₂ : ObjectProperty C}
    {B₁ B₂ : ObjectProperty D} (h₁ : A₁ ≤ B₁.inverseImage F) (h₂ : A₂ ≤ B₂.inverseImage F) :
    extensionProduct A₁ A₂ ≤ (extensionProduct B₁ B₂).inverseImage F := by
  rintro X ⟨Y, Z, f, g, w, hT, hY, hZ⟩
  exact ⟨F.obj Y, F.obj Z, F.map f, F.map g, _, F.map_distinguished _ hT, h₁ _ hY, h₂ _ hZ⟩

/-- Iterated extension products transfer along an exact functor, **with the same number of
extensions on both sides**: `n` extensions of objects of `A` are carried to `n` extensions of
objects of `B`. -/
private lemma extensionProductIter_inverseImage_of_le {A : ObjectProperty C}
    {B : ObjectProperty D} (h : A ≤ B.inverseImage F) (n : ℕ) :
    A.extensionProductIter n ≤ (B.extensionProductIter n).inverseImage F := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simp only [extensionProductIter_succ]
    exact extensionProduct_inverseImage_of_le F h ih

/-- The image along an exact functor of the finite direct sums of objects of `P` consists of
finite direct sums of objects of the image: `F(add(P)) ⊂ add(F(P))`. -/
lemma strictMap_binaryProductsClosure_le (P : ObjectProperty C) :
    P.binaryProductsClosure.strictMap F ≤ (P.strictMap F).binaryProductsClosure := by
  have := isClosedUnderBinaryProducts_inverseImage F (P.strictMap F).binaryProductsClosure
  rintro _ ⟨X, hX⟩
  exact limitsClosure_le (Q := (P.strictMap F).binaryProductsClosure.inverseImage F)
    (fun Y hY => le_limitsClosure _ _ _ (.mk Y hY)) X hX

/-- The image along an exact functor of an extension product is contained in the extension
product of the images: `F(A ⋆ B) ⊂ F(A) ⋆ F(B)`. -/
lemma strictMap_extensionProduct_le (A B : ObjectProperty C) :
    (extensionProduct A B).strictMap F ≤ extensionProduct (A.strictMap F) (B.strictMap F) := by
  rintro _ ⟨X, hX⟩
  exact extensionProduct_inverseImage_of_le F (fun Y hY => .mk Y hY) (fun Y hY => .mk Y hY) X hX

/-- The image along an exact functor of an iterated extension product is contained in the
iterated extension product of the image, with the same number of factors:
`F(A^{⋆ (n + 1)}) ⊂ F(A)^{⋆ (n + 1)}`. -/
lemma strictMap_extensionProductIter_le (A : ObjectProperty C) (n : ℕ) :
    (A.extensionProductIter n).strictMap F ≤ (A.strictMap F).extensionProductIter n := by
  rintro _ ⟨X, hX⟩
  exact extensionProductIter_inverseImage_of_le F (fun Y hY => .mk Y hY) n X hX

/-- **The operations on full subcategories are compatible with an exact functor.** Let
`F : C ⥤ D` be an exact functor of pretriangulated categories, and for a full subcategory `A` of
`C` write `F(A)` for the full subcategory `A.strictMap F` of the objects `F X` with `X ∈ A`.
Then, for full subcategories `A`, `B` of `C`, every set `S` of shifts and every `n`:
* `F(A[S]) = F(A)[S]` up to isomorphism, where `A[S]` consists of the objects `X ≅ Y⟦-i⟧` with
  `Y ∈ A` and `i ∈ S`; for `S = [a, b] ∩ ℤ`, `-∞ ≤ a ≤ b ≤ ∞`, this is `F(A[a, b]) = F(A)[a, b]`;
* `F(smd(A)) ⊂ smd(F(A))`;
* `F(add(A)) ⊂ add(F(A))`;
* `F(A ⋆ B) ⊂ F(A) ⋆ F(B)`;
* `F(A^{⋆ (n + 1)}) ⊂ F(A)^{⋆ (n + 1)}`, the source's `F(A^{⋆ n}) ⊂ F(A)^{⋆ n}` for `n ≥ 1`
  factors, `A.extensionProductIter n` having `n + 1` factors. -/
@[stacks 0FX5 "Each of `F(𝒜[a, b]) = F(𝒜)[a, b]` (for any set of shifts, up to isomorphism), \
`F(smd(𝒜)) ⊂ smd(F(𝒜))`, `F(add(𝒜)) ⊂ add(F(𝒜))`, `F(𝒜 ⋆ ℬ) ⊂ F(𝒜) ⋆ F(ℬ)` and \
`F(𝒜^{⋆ n}) ⊂ F(𝒜)^{⋆ n}`, with `F(𝒜) = 𝒜.strictMap F`."]
theorem isoClosure_strictMap_biSup_shift_eq_and_strictMap_operations_le
    (A B : ObjectProperty C) (S : Set ℤ) (n : ℕ) :
    ((⨆ i ∈ S, A.isoClosure.shift i).strictMap F).isoClosure =
        ⨆ i ∈ S, (A.strictMap F).isoClosure.shift i ∧
      A.retractClosure.strictMap F ≤ (A.strictMap F).retractClosure ∧
      A.binaryProductsClosure.strictMap F ≤ (A.strictMap F).binaryProductsClosure ∧
      (extensionProduct A B).strictMap F ≤ extensionProduct (A.strictMap F) (B.strictMap F) ∧
      (A.extensionProductIter n).strictMap F ≤ (A.strictMap F).extensionProductIter n :=
  ⟨isoClosure_strictMap_biSup_shift_isoClosure F A S, strictMap_retractClosure_le F A,
    strictMap_binaryProductsClosure_le F A, strictMap_extensionProduct_le F A B,
    strictMap_extensionProductIter_le F A n⟩

/-- **The bounded-shift form of `smd(add(P[c, d])^{⋆ n})` is functorial along an exact functor.**
Let `F : C ⥤ D` be an exact functor of pretriangulated categories, let `P` be a property of
objects of `C` and `Q` one of `D`, and suppose `F` carries every object satisfying `P` to one
satisfying `Q`. Then `F` carries `smd(add(P[c, d])^{⋆ n})` into `smd(add(Q[c, d])^{⋆ n})`: the
shift interval `[c, d]` and the number `n` of extensions are the same on both sides.

This composes the compatibilities of Derived Categories, Remark 13.35.5 ([Stacks, Tag 0FX5])
for the explicit subcategories `Cₙ = smd(add(E[c, d])^{⋆ n})` built from a bounded range of
shifts as in [Stacks, Tag 0FX9]. Tracking the interval is the content: the
unbounded-shift form `Stacks.TriangulatedGenerators.triangEnvelopeIter_inverseImage_of_le`,
stated with `ObjectProperty.triangEnvelopeIter`, gives no control on which shifts of `Q` the
image uses. -/
@[stacks 0FX5 "The composite `F(smd(add(𝒜[c, d])^{⋆ n})) ⊂ smd(add(F(𝒜)[c, d])^{⋆ n})`."]
theorem retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le
    {P : ObjectProperty C} {Q : ObjectProperty D} (h : ∀ ⦃X : C⦄, P X → Q (F.obj X))
    (c d : ℤ) (n : ℕ) :
    ((⨆ i ∈ Set.Icc c d, P.isoClosure.shift i).binaryProductsClosure.extensionProductIter n
      ).retractClosure ≤
      ((((⨆ i ∈ Set.Icc c d, Q.isoClosure.shift i).binaryProductsClosure.extensionProductIter n
        ).retractClosure).inverseImage F) := by
  have hadd := isClosedUnderBinaryProducts_inverseImage F
    (⨆ i ∈ Set.Icc c d, Q.isoClosure.shift i).binaryProductsClosure
  have hsmd := isStableUnderRetracts_inverseImage
    (((⨆ i ∈ Set.Icc c d, Q.isoClosure.shift i).binaryProductsClosure.extensionProductIter n
      ).retractClosure) F
  rw [retractClosure_le_iff]
  refine (extensionProductIter_inverseImage_of_le F (limitsClosure_le ?_) n).trans
    fun X hX => le_retractClosure _ _ hX
  exact (biSup_shift_isoClosure_inverseImage_of_le F h c d).trans
    fun X hX => le_limitsClosure _ _ _ hX

end Transfer

end Stacks.TriangulatedGenerators

end

