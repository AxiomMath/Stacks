module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.StrongGenerator.CoherentUniformGenerator
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory

/-!
# Uniform bounds for a homological or cohomological functor on the coherent modules

Let `k` be a field, let `X` be a scheme proper and smooth over `k`, let `𝒜` be an abelian
category and let `H : D_perf(𝒪_X) ⥤ 𝒜` be a homological functor whose cohomology
`H^i(K) = H(K[i])` is nonzero for only finitely many `i`, for every perfect `K`. Then there is an
`m ≥ 1`, depending on `H` and `X` but not on the module, with `H^i(ℱ) = 0` for every coherent
`𝒪_X`-module `ℱ` and every `i ∉ [-m, m]`; and the same for a cohomological functor. This is
[Stacks, Tag 0FZ8].

## The shape of the argument

[Stacks, Tag 0FZ7] supplies, uniformly in the coherent module `ℱ`, a finite locally free `𝒢` and
integers `m₀, n ≥ 1` with `ℱ ∈ smd(add(𝒢[-m₀, m₀])^{⋆ n})`. The functor `H` has a window on the
*single* object `𝒢`, say `H^i(𝒢) = 0` for `i ∉ [a, b]`, because its cohomology is finitely
supported; and [Stacks, Tag 0FX8] propagates a window from a generating class to the whole tower
`smd(add(−[c, d])^{⋆ n})`, adding `[c, d]` to it. So `H^i(ℱ) = 0` for `i ∉ [a - m₀, b + m₀]`, and
`m = 1 + |a - m₀| + |b + m₀|` is a bound of the asserted shape.

## Reading the tower inside `D_perf(𝒪_X)`

`H` is a functor on `D_perf(𝒪_X)`, so the window argument has to run there, whereas the
conclusion of [Stacks, Tag 0FZ7],
`AlgebraicGeometry.exists_uniform_generator_isCoherent_of_diagonalEnvelope`, is a membership in
the ambient `D(𝒪_X)`. The two are the same statement, and `Stacks.TriangulatedGenerators.`
`retractClosure_extensionProductIter_biSup_shift_of_map_ι` is the proof: for a strictly full
triangulated subcategory `P` of a pretriangulated category, the four closure operations making
up `smd(add(E[c, d])^{⋆ n})` are *reflected* along the inclusion `P.ι`. Each one separately:
a shift because `P.ι` commutes with the shift, finite direct sums because `P.ι` preserves binary
products, extensions because a distinguished triangle of `P.FullSubcategory` is by definition one
whose `P.ι`-image is distinguished — the lifting uses that `P.ι` is full — and direct summands
because `P.ι` is fully faithful. This is the converse direction to [Stacks, Tag 0FX5]
(`Stacks.TriangulatedGenerators.`
`retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le`), which pushes the same
subcategories *forward* along an arbitrary exact functor.

Nothing here needs the perfect objects to be stable under direct summands ([Stacks, Tag 08CS],
`Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod`). The summand that occurs is `ℱ` itself,
perfect by [Stacks, Tag 0FDC], inside an object of the tower, perfect because the tower is built
from `𝒢` by operations a triangulated subcategory is closed under.

## The cohomological case

A cohomological functor is a homological functor on the opposite category, as in
`CategoryTheory.exists_iso_comp_linearYoneda_of_finiteDimensional`: there is no separate
`IsCohomological` class, and `CategoryTheory.Functor.map_distinguished_op_exact` is the long
exact sequence of `H : Cᵒᵖ ⥤ 𝒜` on a distinguished triangle of `C`. [Stacks, Tag 0FX8],
`CategoryTheory.Functor.isZero_obj_shift_of_retractClosure_extensionProductIter`, is stated for a
covariant homological functor, so it does not cover this half of the tag;
`Stacks.TriangulatedGenerators.isZero_obj_op_shift_of_retractClosure_extensionProductIter` is the
contravariant form, proved from a common core which asks of a functor `G` only that the vanishing
of `G` be inherited by the middle object of a distinguished triangle. For a homological functor
that core is [Stacks, Tag 0FX8] itself, which is therefore used as it stands for the homological
half.

## Main results

* `Stacks.TriangulatedGenerators.retractClosure_extensionProductIter_biSup_shift_of_map_ι`:
  `smd(add(E[c, d])^{⋆ n})` is reflected along the inclusion of a strictly full triangulated
  subcategory.
* `Stacks.TriangulatedGenerators.isZero_obj_op_shift_of_retractClosure_extensionProductIter`:
  the window of a *cohomological* functor on the tower `smd(add(E[c, d])^{⋆ n})` is `[a + c,
  b + d]`, the contravariant form of [Stacks, Tag 0FX8].
* `AlgebraicGeometry.exists_uniform_bound_isZero_of_isHomological` and
  `AlgebraicGeometry.exists_uniform_bound_isZero_of_isCohomological`: **[Stacks, Tag 0FZ8]**, the
  homological and the cohomological case.

## Implementation notes

`D_perf(𝒪_X)` is the reducible abbreviation `AlgebraicGeometry.perfectDerived` written out. Its
triangulated structure is `Stacks.Cohomology.PerfectTriangulatedSubcategory.`
`isTriangulated_isPerfect` ([Stacks, Tag 0F8I]) at the locally small derived category of
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`; the universe arguments are written out
because the level of the derived-category instance is a `max` that unification will not read off
the value, exactly as in
`Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isTriangulated`, which is the
same statement at `CategoryTheory.HasDerivedCategory.standard` and so does not apply here.

The finiteness hypothesis is stated as the source states it, `{i | H^i(K) ≠ 0}` finite; the
window `[a, b]` it is used through is obtained from `Set.Finite.bddBelow` and
`Set.Finite.bddAbove`. The bound returned is `m = 1 + |a - m₀| + |b + m₀|` with `[a, b]` the
window on `𝒢` and `m₀` the half-width of [Stacks, Tag 0FZ7]; the `1 +` is what makes `1 ≤ m`.

`Stacks.TriangulatedGenerators.isZero_obj_op_shift_of_retractClosure_extensionProductIter`
repeats, for a plain functor, the five private auxiliary lemmas behind
`CategoryTheory.Functor.isZero_obj_shift_of_retractClosure_extensionProductIter` for a
homological one.

## References

* [Stacks Project, Tag 0FZ8](https://stacks.math.columbia.edu/tag/0FZ8)
* [Stacks Project, Tag 0FZ7](https://stacks.math.columbia.edu/tag/0FZ7)
* [Stacks Project, Tag 0FX8](https://stacks.math.columbia.edu/tag/0FX8)
* [Stacks Project, Tag 0FX5](https://stacks.math.columbia.edu/tag/0FX5)
* [Stacks Project, Tag 0147](https://stacks.math.columbia.edu/tag/0147)
* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

universe u

namespace Stacks.TriangulatedGenerators

/-- The image of a one-object class under a functor is the isomorphism closure of the one-object
class on the image. -/
private lemma map_singleton {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (Z : C) :
    (ObjectProperty.singleton Z).map F = (ObjectProperty.singleton (F.obj Z)).isoClosure := by
  ext Y
  constructor <;> rintro ⟨W, hW, ⟨e⟩⟩ <;> obtain rfl := (ObjectProperty.singleton_iff _ _).1 hW <;>
    exact ⟨_, (ObjectProperty.singleton_iff _ _).2 rfl, ⟨e.symm⟩⟩

/-! ### Closure operations on a full triangulated subcategory -/

section FullSubcategory

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

omit [P.IsClosedUnderIsomorphisms] in
/-- **A window of shifts is reflected along the inclusion of a full subcategory.** An object of
`C` whose shift by some `j ∈ [c, d]` is isomorphic to the image of an object of `E` is itself the
image of an object of `E[c, d]`, namely of a shift by `-j`. -/
private lemma biSup_shift_isoClosure_map_ι_le (E : ObjectProperty P.FullSubcategory) (c d : ℤ) :
    (⨆ j ∈ Set.Icc c d, (E.map P.ι).isoClosure.shift j) ≤
      (⨆ j ∈ Set.Icc c d, E.isoClosure.shift j).map P.ι := by
  refine iSup₂_le fun j hj Y hY => ?_
  obtain ⟨W, ⟨M, hM, ⟨e₀⟩⟩, ⟨e⟩⟩ := hY
  refine ⟨M⟦-j⟧, (prop_iSup_iff _ _).2 ⟨j, (prop_iSup_iff _ _).2 ⟨hj, ?_⟩⟩, ⟨?_⟩⟩
  · exact ⟨M, hM, ⟨shiftNegShift M j⟩⟩
  · exact ((P.ι.commShiftIso (-j)).app M) ≪≫
      (shiftFunctor C (-j)).mapIso (e₀ ≪≫ e.symm) ≪≫ shiftShiftNeg Y j

/-- **Finite direct sums are reflected along the inclusion of a full triangulated subcategory.**
The inclusion preserves binary products, so a binary product in `C` of images of objects of `S`
is the image of their binary product, taken in the subcategory. -/
private lemma binaryProductsClosure_map_ι_le (S : ObjectProperty P.FullSubcategory) :
    (S.map P.ι).binaryProductsClosure ≤ S.binaryProductsClosure.map P.ι := by
  have : (S.binaryProductsClosure.map P.ι).IsClosedUnderBinaryProducts := by
    refine isClosedUnderBinaryProducts_of_prop_prod _ ?_
    rintro A B ⟨M₁, hM₁, ⟨e₁⟩⟩ ⟨M₂, hM₂, ⟨e₂⟩⟩
    exact ⟨M₁ ⨯ M₂, prop_prod _ _ _ hM₁ hM₂,
      ⟨PreservesLimitPair.iso P.ι M₁ M₂ ≪≫ prod.mapIso e₁ e₂⟩⟩
  exact limitsClosure_le (map_monotone (le_limitsClosure _ _) _)

omit [P.IsClosedUnderIsomorphisms] in
/-- **Extensions are reflected along the inclusion of a full triangulated subcategory.** A
distinguished triangle of `C` whose outer objects are images of objects `M₁` and `M₃` of the
subcategory is isomorphic to the image of a distinguished triangle on `M₁` and `M₃`: fullness
lifts the third morphism, the subcategory has a cocone on the lift, and `isoTriangleOfIso₁₃`
identifies the two triangles. -/
private lemma extensionProduct_map_ι_le (S₁ S₂ : ObjectProperty P.FullSubcategory) :
    extensionProduct (S₁.map P.ι) (S₂.map P.ι) ≤ (extensionProduct S₁ S₂).map P.ι := by
  rintro K ⟨A, B, f, g, h, hT, ⟨M₁, hM₁, ⟨e₁⟩⟩, ⟨M₃, hM₃, ⟨e₃⟩⟩⟩
  obtain ⟨u, hu⟩ := P.ι.map_surjective (e₃.hom ≫ h ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv ≫
    (P.ι.commShiftIso (1 : ℤ)).inv.app M₁)
  obtain ⟨M₂, f', g', hT'⟩ := distinguished_cocone_triangle₂ u
  refine ⟨M₂, ⟨M₁, M₃, f', g', _, hT', hM₁, hM₃⟩, ⟨?_⟩⟩
  refine Triangle.π₂.mapIso (isoTriangleOfIso₁₃ _ (Triangle.mk f g h)
    (P.ι.map_distinguished _ hT') hT e₁ e₃ ?_)
  change (P.ι.map u ≫ (P.ι.commShiftIso (1 : ℤ)).hom.app M₁) ≫
    (shiftFunctor C (1 : ℤ)).map e₁.hom = e₃.hom ≫ h
  rw [hu]
  simp [← Functor.map_comp]

omit [P.IsClosedUnderIsomorphisms] in
/-- Iterated extensions are reflected along the inclusion of a full triangulated subcategory,
with the same number of extensions on both sides. -/
private lemma extensionProductIter_map_ι_le (S : ObjectProperty P.FullSubcategory) (n : ℕ) :
    (S.map P.ι).extensionProductIter n ≤ (S.extensionProductIter n).map P.ι := by
  induction n with
  | zero => simpa only [extensionProductIter_zero] using le_rfl
  | succ n ih =>
    rw [extensionProductIter_succ, extensionProductIter_succ]
    exact (monotone_extensionProduct_right _ ih).trans (extensionProduct_map_ι_le P S _)

/-- **The bounded-shift subcategory `smd(add(E[c, d])^{⋆ n})` is reflected along the inclusion of
a strictly full triangulated subcategory.** Let `P` be a strictly full triangulated subcategory
of a pretriangulated category `C` and let `E` be a property of objects of `P`. If the image in
`C` of an object `Z` of `P` is a direct summand of an `n`-fold extension of finite direct sums of
the shifts by `[c, d]` of images of objects of `E`, then `Z` itself lies in
`smd(add(E[c, d])^{⋆ n})` computed inside `P`.

This is the direction opposite to [Stacks, Tag 0FX5], which carries these subcategories forward
along an arbitrary exact functor; here the functor is the inclusion of a triangulated
subcategory, and what makes the reflection possible is that it is fully faithful and that every
object produced by the four closure operations from objects of `P` is again in `P`. -/
theorem retractClosure_extensionProductIter_biSup_shift_of_map_ι
    (E : ObjectProperty P.FullSubcategory) (c d : ℤ) (n : ℕ) {Z : P.FullSubcategory}
    (hZ : ((⨆ j ∈ Set.Icc c d,
      (E.map P.ι).isoClosure.shift j).binaryProductsClosure.extensionProductIter n).retractClosure
        (P.ι.obj Z)) :
    ((⨆ j ∈ Set.Icc c d,
      E.isoClosure.shift j).binaryProductsClosure.extensionProductIter n).retractClosure Z := by
  obtain ⟨Y, hY, ⟨r⟩⟩ := hZ
  obtain ⟨M, hM, ⟨e⟩⟩ := (monotone_extensionProductIter
    ((limitsClosure_monotone _ (biSup_shift_isoClosure_map_ι_le P E c d)).trans
      (binaryProductsClosure_map_ι_le P _)) n).trans
    (extensionProductIter_map_ι_le P _ n) Y hY
  obtain ⟨i', hi'⟩ := P.ι.map_surjective (r.i ≫ e.inv)
  obtain ⟨r', hr'⟩ := P.ι.map_surjective (e.hom ≫ r.r)
  refine ⟨M, hM, ⟨{ i := i', r := r', retract := P.ι.map_injective ?_ }⟩⟩
  rw [P.ι.map_comp, hi', hr', P.ι.map_id, Category.assoc, Iso.inv_hom_id_assoc, r.retract]

end FullSubcategory

/-! ### The window of a cohomological functor on a tower -/

section CohomologicalWindow

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable {D : Type*} [Category D] (G : C ⥤ D)

/-- Given `G : C ⥤ D` with `C` equipped with a `ℤ`-shift, and with the convention
`G^i(X) = G(X⟦i⟧)`, this is the class of objects `X` of `C` with `G^i(X) = 0` for `i ∉ [u, v]`. -/
private def vanishingOutside (u v : ℤ) : ObjectProperty C :=
  fun Y => ∀ i ∉ Set.Icc u v, IsZero (G.obj (Y⟦i⟧))

private instance (u v : ℤ) : (vanishingOutside G u v).IsClosedUnderIsomorphisms where
  of_iso e hX i hi := (hX i hi).of_iso ((shiftFunctor C i ⋙ G).mapIso e.symm)

private instance (u v : ℤ) : (vanishingOutside G u v).IsStableUnderRetracts where
  of_retract r hY i hi := (hY i hi).of_retract (r.map (shiftFunctor C i ⋙ G))

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- A wider window is a weaker condition. -/
private lemma vanishingOutside_mono {u v u' v' : ℤ} (hu : u' ≤ u) (hv : v ≤ v') :
    vanishingOutside G u v ≤ vanishingOutside G u' v' :=
  fun _ hX i hi ↦ hX i fun hi' ↦ hi (Set.Icc_subset_Icc hu hv hi')

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Shifting by `j` translates the window by `j`. -/
private lemma vanishingOutside_shift (u v j : ℤ) :
    (vanishingOutside G u v).shift j = vanishingOutside G (u + j) (v + j) := by
  ext Y
  exact ⟨fun hX i hi ↦ (G.isZero_obj_shift_shift_iff Y (i := i - j) (by omega)).1
      (hX _ (by simp only [Set.mem_Icc] at hi ⊢; omega)),
    fun hX i hi ↦ (G.isZero_obj_shift_shift_iff Y (k := j + i) rfl).2
      (hX _ (by simp only [Set.mem_Icc] at hi ⊢; omega))⟩

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The shifts by `j ∈ [c, d]` of a class `E` of objects with cohomology in `[a, b]` have their
cohomology in `[a + c, b + d]`. -/
private lemma iSup_shift_le_vanishingOutside {E : ObjectProperty C} {a b : ℤ}
    (hE : E ≤ vanishingOutside G a b) (c d : ℤ) :
    ⨆ j ∈ Set.Icc c d, E.shift j ≤ vanishingOutside G (a + c) (b + d) := by
  refine iSup₂_le fun j hj ↦ ?_
  rw [Set.mem_Icc] at hj
  calc E.shift j ≤ (vanishingOutside G a b).shift j := fun _ hX ↦ hE _ hX
    _ = vanishingOutside G (a + j) (b + j) := vanishingOutside_shift G a b j
    _ ≤ vanishingOutside G (a + c) (b + d) := vanishingOutside_mono G (by omega) (by omega)

variable (hext : ∀ T : Triangle C, T ∈ distTriang C →
  IsZero (G.obj T.obj₁) → IsZero (G.obj T.obj₃) → IsZero (G.obj T.obj₂))

include hext

/-- Objects with cohomology in a fixed window are closed under extensions, as soon as the
vanishing of `G` is inherited by the middle object of a distinguished triangle: shifting the
triangle by `i` turns the hypothesis into the assertion in degree `i`. -/
private lemma isTriangulatedClosed₂_vanishingOutside (u v : ℤ) :
    (vanishingOutside G u v).IsTriangulatedClosed₂ :=
  .mk' fun T hT h₁ h₃ i hi ↦
    hext _ (Triangle.shift_distinguished T hT i) (h₁ i hi) (h₃ i hi)

/-- Objects with cohomology in a fixed window are closed under finite direct sums: `A ⨯ B` is the
middle object of the distinguished triangle `A ⟶ A ⨯ B ⟶ B ⟶ A⟦1⟧`. -/
private lemma isClosedUnderBinaryProducts_vanishingOutside (u v : ℤ) :
    (vanishingOutside G u v).IsClosedUnderBinaryProducts := by
  have := isTriangulatedClosed₂_vanishingOutside G hext u v
  refine isClosedUnderBinaryProducts_of_prop_prod _ ?_
  intro A B hA hB
  exact ext_of_isTriangulatedClosed₂ _ _ (binaryProductTriangle_distinguished A B) hA hB

/-- **The window of `G` on the tower `smd(add(E[c, d])^{⋆ n})` is `[a + c, b + d]`**, for any
functor `G` whose vanishing is inherited by the middle object of a distinguished triangle. This
is the common core of [Stacks, Tag 0FX8] and of its contravariant form: the four closure
operations preserve the class of objects with cohomology in a fixed window, by the hypothesis
`hext` for extensions and for direct sums, by functoriality for isomorphisms and for direct
summands. -/
private theorem isZero_obj_shift_of_retractClosure_extensionProductIter_of_isZero_ext
    (E : ObjectProperty C) {a b : ℤ}
    (hE : ∀ ⦃Y : C⦄, E Y → ∀ i ∉ Set.Icc a b, IsZero (G.obj (Y⟦i⟧)))
    (c d : ℤ) (n : ℕ) {Y : C}
    (hY : ((⨆ j ∈ Set.Icc c d,
      E.isoClosure.shift j).binaryProductsClosure.extensionProductIter n).retractClosure Y)
    {i : ℤ} (hi : i ∉ Set.Icc (a + c) (b + d)) :
    IsZero (G.obj (Y⟦i⟧)) := by
  have := isTriangulatedClosed₂_vanishingOutside G hext (a + c) (b + d)
  have := isClosedUnderBinaryProducts_vanishingOutside G hext (a + c) (b + d)
  exact (retractClosure_le_iff _ _).2 (extensionProductIter_le_of_isTriangulatedClosed₂ _
    (limitsClosure_le (iSup_shift_le_vanishingOutside G
      ((isoClosure_le_iff _ _).2 fun _ hY' ↦ hE hY') c d)) n) Y hY i hi

end CohomologicalWindow

section Cohomological

open Opposite CategoryTheory.Pretriangulated.Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {A : Type*} [Category A] [Abelian A]

/-- **The window of a cohomological functor on the tower `smd(add(E[c, d])^{⋆ n})`.** Let
`H : Cᵒᵖ ⥤ 𝒜` be a cohomological functor on a triangulated category, with
`H^i(X) = H(X⟦i⟧)`, and let `E` be a class of objects of `C` with `H^i(E) = 0` for `E ∈ E` and
`i ∉ [a, b]`. Then every direct summand of an `n`-fold extension of finite direct sums of shifts
`E⟦-j⟧` with `E ∈ E` and `j ∈ [c, d]` satisfies `H^i(X) = 0` for `i ∉ [a + c, b + d]`.

This is the contravariant form of [Stacks, Tag 0FX8], whose statement
`CategoryTheory.Functor.isZero_obj_shift_of_retractClosure_extensionProductIter` is for a
covariant homological functor. The exactness used is
`CategoryTheory.Functor.map_distinguished_op_exact`. -/
theorem isZero_obj_op_shift_of_retractClosure_extensionProductIter
    (H : Cᵒᵖ ⥤ A) [H.IsHomological] (E : ObjectProperty C) {a b : ℤ}
    (hE : ∀ ⦃Y : C⦄, E Y → ∀ i ∉ Set.Icc a b, IsZero (H.obj (op (Y⟦i⟧))))
    (c d : ℤ) (n : ℕ) {Y : C}
    (hY : ((⨆ j ∈ Set.Icc c d,
      E.isoClosure.shift j).binaryProductsClosure.extensionProductIter n).retractClosure Y)
    {i : ℤ} (hi : i ∉ Set.Icc (a + c) (b + d)) :
    IsZero (H.obj (op (Y⟦i⟧))) :=
  (isZero_obj_shift_of_retractClosure_extensionProductIter_of_isZero_ext H.rightOp
    (fun T hT h₁ h₃ => ((H.map_distinguished_op_exact T hT).isZero_of_both_isZero
      h₃.unop h₁.unop).op) E (fun _ hY' i hi' => (hE hY' i hi').op) c d n hY hi).unop

end Cohomological

end Stacks.TriangulatedGenerators

namespace AlgebraicGeometry

open Stacks.Cohomology.PerfectComplexes Stacks.TriangulatedGenerators

/-- **The perfect objects form a triangulated subcategory of `D(𝒪_X)`**, at the locally small
derived category of `𝒪_X`-modules. This is
`Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect` read on the ringed
space underlying `X`, with the universe arguments written out. -/
instance isTriangulated_isPerfect_scheme (X : Scheme.{u}) :
    (show ObjectProperty (DerivedCategory X.Modules) from
      fun K => IsPerfect (X := X.toRingedSpace) K).IsTriangulated :=
  @Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect.{u, u}
    X.toRingedSpace inferInstance

/-- **The perfect objects form a strictly full subcategory of `D(𝒪_X)`**, at the locally small
derived category of `𝒪_X`-modules. This is
`Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect` read on the ringed space
underlying `X`, with the universe arguments written out. -/
instance isClosedUnderIsomorphisms_isPerfect_scheme (X : Scheme.{u}) :
    (show ObjectProperty (DerivedCategory X.Modules) from
      fun K => IsPerfect (X := X.toRingedSpace) K).IsClosedUnderIsomorphisms :=
  @Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect.{u, u, u}
    X.toRingedSpace inferInstance

/-- A coherent module on a scheme smooth over a field, placed in cohomological degree zero, as an
object of `D_perf(𝒪_X)`: it is perfect because such a scheme is regular ([Stacks, Tag 056S]) and
a coherent module on a regular scheme is perfect ([Stacks, Tag 0FDC]). -/
def coherentPerfect {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (F : X.Modules) [F.IsCoherent] :
    ObjectProperty.FullSubcategory
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K) :=
  ⟨(DerivedCategory.singleFunctor X.Modules 0).obj F,
    isPerfect_single_of_isCoherent_of_isRegular (isRegular_of_smooth_over_field f) F⟩

section Uniform

open Opposite CategoryTheory.Pretriangulated.Opposite

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [IsProper f] [Smooth f]
  (G : X.Modules) (hG : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G)
  (box diag : DerivedCategory (pullback f f).Modules)
  (hdiag : (ObjectProperty.singleton box).triangEnvelope diag)
  (Φ : ObjectProperty.FullSubcategory
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K) →
    DerivedCategory (pullback f f).Modules ⥤ DerivedCategory X.Modules)
  [∀ K, (Φ K).CommShift ℤ] [∀ K, (Φ K).IsTriangulated]
  (hdiagΦ : ∀ K, (Φ K).obj diag ≅ K.obj)
  (hboxΦ : ∀ K (a b : ℤ) (t : ℕ), K.obj.IsGE a → K.obj.IsLE b →
    (∀ M : X.Modules, M.IsQuasicoherent → ∀ i : ℕ, t ≤ i →
      IsZero (cohomologyOverField k f M i)) →
    ((⨆ i ∈ Set.Icc a (b + (t : ℤ)), (ObjectProperty.singleton
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)).isoClosure.shift
        i).binaryProductsClosure).retractClosure ((Φ K).obj box))

/-- **[Stacks, Tag 0FZ7] read inside `D_perf(𝒪_X)`.** By
`AlgebraicGeometry.exists_uniform_generator_isCoherent_of_diagonalEnvelope` there are `m, n ≥ 1`
and a perfect object `Z` — a finite locally free module in degree zero — such that every coherent
`𝒪_X`-module, viewed in `D_perf(𝒪_X)`, is a direct summand of an `n`-fold extension of finite
direct sums of the shifts of `Z` by the degrees in `[-m, m]`, the membership being read in
`D_perf(𝒪_X)` rather than in `D(𝒪_X)`. -/
private theorem exists_uniform_generator_coherentPerfect :
    ∃ (m n : ℕ) (Z : ObjectProperty.FullSubcategory
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K)),
      1 ≤ m ∧ 1 ≤ n ∧ ∀ (F : X.Modules) [F.IsCoherent],
        ((⨆ j ∈ Set.Icc (-(m : ℤ)) (m : ℤ),
          (ObjectProperty.singleton Z).isoClosure.shift
            j).binaryProductsClosure.extensionProductIter n).retractClosure
              (coherentPerfect f F) := by
  obtain ⟨m, n, 𝒢, hm, hn, h𝒢, hall⟩ :=
    exists_uniform_generator_isCoherent_of_diagonalEnvelope f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := h𝒢
  have : 𝒢.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X 𝒢
  refine ⟨m, n, coherentPerfect f 𝒢, hm, hn, ?_⟩
  intro F hF
  refine retractClosure_extensionProductIter_biSup_shift_of_map_ι
    (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K)
    (ObjectProperty.singleton (coherentPerfect f 𝒢)) (-(m : ℤ)) (m : ℤ) n ?_
  simp only [map_singleton, isoClosure_eq_self]
  exact hall F hF

/-- A property holding off a finite set of integers holds off a window `[a, b]`, and the window
`[a - m₀, b + m₀]` lies inside some `[-m, m]` with `1 ≤ m`. -/
private lemma exists_window_bound {P : ℤ → Prop} (h : {i | ¬ P i}.Finite) (m₀ : ℕ) :
    ∃ (a b : ℤ) (m : ℕ), (∀ i ∉ Set.Icc a b, P i) ∧ 1 ≤ m ∧
      ∀ i ∉ Set.Icc (-(m : ℤ)) (m : ℤ), i ∉ Set.Icc (a + -(m₀ : ℤ)) (b + (m₀ : ℤ)) := by
  obtain ⟨a, ha⟩ := h.bddBelow
  obtain ⟨b, hb⟩ := h.bddAbove
  refine ⟨a, b, 1 + (a - m₀).natAbs + (b + m₀).natAbs, fun i hi ↦ ?_, by omega, fun i hi ↦ ?_⟩
  · by_contra hz
    exact hi (Set.mem_Icc.2 ⟨ha hz, hb hz⟩)
  · simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
    omega

/-- **[Stacks, Tag 0FZ8], the homological case.** Let `k` be a field, let `X` be a scheme proper
and smooth over `k`, let `𝒜` be an abelian category and let `H : D_perf(𝒪_X) ⥤ 𝒜` be a
homological functor whose cohomology `H^i(K) = H(K[i])` is nonzero for only finitely many `i`,
for every perfect `K`. Then there is an `m ≥ 1`, independent of the module, with `H^i(ℱ) = 0` for
every coherent `𝒪_X`-module `ℱ` and every `i ∉ [-m, m]`.

[Stacks, Tag 0FZ7] is used as it stands, with no input of its own left open. The window of `H` on
the single generator it supplies exists because the cohomology of `H` is finitely supported, and
[Stacks, Tag 0FX8] widens it to the whole tower by the fixed amount `[-m₀, m₀]`, which is what
makes the bound uniform. -/
@[stacks 0FZ8 "the homological case, from Stacks 0FZ7 as it stands. The cohomological case of \
the final sentence is `AlgebraicGeometry.exists_uniform_bound_isZero_of_isCohomological`"]
theorem exists_uniform_bound_isZero_of_isHomological {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    (H : ObjectProperty.FullSubcategory
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K) ⥤ 𝒜)
    [H.IsHomological]
    (hfin : ∀ Z, {i : ℤ | ¬ IsZero (H.obj (Z⟦i⟧))}.Finite) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ (F : X.Modules) [F.IsCoherent] (i : ℤ),
      i ∉ Set.Icc (-(m : ℤ)) (m : ℤ) → IsZero (H.obj ((coherentPerfect f F)⟦i⟧)) := by
  obtain ⟨m₀, n, Z, hm₀, hn, hall⟩ := exists_uniform_generator_coherentPerfect f
  obtain ⟨a, b, m, hwin, hm, hbd⟩ := exists_window_bound (hfin Z) m₀
  refine ⟨m, hm, ?_⟩
  intro F hF i hi
  refine H.isZero_obj_shift_of_retractClosure_extensionProductIter
    (ObjectProperty.singleton Z) (a := a) (b := b) ?_ (-(m₀ : ℤ)) (m₀ : ℤ) n (hall F) ?_
  · intro Y hY
    obtain rfl := (ObjectProperty.singleton_iff _ _).1 hY
    exact hwin
  · exact hbd i hi

/-- **[Stacks, Tag 0FZ8], the cohomological case.** Let `k` be a field, let `X` be a scheme
proper and smooth over `k`, let `𝒜` be an abelian category and let `H : D_perf(𝒪_X)ᵒᵖ ⥤ 𝒜` be a
cohomological functor whose cohomology `H^i(K) = H(K[i])` is nonzero for only finitely many `i`,
for every perfect `K`. Then there is an `m ≥ 1`, independent of the module, with `H^i(ℱ) = 0` for
every coherent `𝒪_X`-module `ℱ` and every `i ∉ [-m, m]`.

This is the final sentence of the tag. A cohomological functor is a homological functor on the
opposite category, and the window argument is
`Stacks.TriangulatedGenerators.isZero_obj_op_shift_of_retractClosure_extensionProductIter`, the
contravariant form of [Stacks, Tag 0FX8]; [Stacks, Tag 0FZ7] is used as it stands, as in the
homological case. -/
@[stacks 0FZ8 "the cohomological case of the final sentence, with a cohomological functor read \
as a homological functor on the opposite category, and from Stacks 0FZ7 as it stands, as in the \
homological case"]
theorem exists_uniform_bound_isZero_of_isCohomological {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    (H : (ObjectProperty.FullSubcategory
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K))ᵒᵖ ⥤ 𝒜)
    [H.IsHomological]
    (hfin : ∀ Z, {i : ℤ | ¬ IsZero (H.obj (op (Z⟦i⟧)))}.Finite) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ (F : X.Modules) [F.IsCoherent] (i : ℤ),
      i ∉ Set.Icc (-(m : ℤ)) (m : ℤ) → IsZero (H.obj (op ((coherentPerfect f F)⟦i⟧))) := by
  obtain ⟨m₀, n, Z, hm₀, hn, hall⟩ := exists_uniform_generator_coherentPerfect f
  obtain ⟨a, b, m, hwin, hm, hbd⟩ := exists_window_bound (hfin Z) m₀
  refine ⟨m, hm, ?_⟩
  intro F hF i hi
  refine isZero_obj_op_shift_of_retractClosure_extensionProductIter H
    (ObjectProperty.singleton Z) (a := a) (b := b) ?_ (-(m₀ : ℤ)) (m₀ : ℤ) n (hall F) ?_
  · intro Y hY
    obtain rfl := (ObjectProperty.singleton_iff _ _).1 hY
    exact hwin
  · exact hbd i hi

end Uniform

end AlgebraicGeometry

end
