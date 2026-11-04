module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsPerfectIsCompact
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.CategoryTheory.Triangulated.TriangulatedEnvelopeInduction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RetractOfAPerfectObject
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory

/-!
# A perfect generator classically generates the perfect objects

Let `X` be a quasi-compact and quasi-separated scheme and let `G` be a perfect object of `D(𝒪_X)`
which generates `D_QCoh(𝒪_X)`. Then `G` is a *classical* generator of `D_perf(𝒪_X)`: the smallest
strictly full triangulated subcategory of `D_QCoh(𝒪_X)` closed under direct summands and containing
`G` is exactly the subcategory of perfect objects.

## Main definitions

* `perfectObjects`: `D_perf(𝒪_X)` as a property of the objects of `D_QCoh(𝒪_X)`.

## Main results

* `triangEnvelope_eq_of_le_isCompactObject_of_isWeakTriangulatedGenerator`: for a compact object
  `E` of a triangulated category with direct sums which weakly generates it, and a thick
  subcategory `P` consisting of compact objects and containing the shifts of `E`, the triangulated
  envelope `⟨E⟩` is `P`.
* `triangEnvelope_singleton_le_perfectObjects`: the inclusion `⟨G⟩ ≤ D_perf(𝒪_X)` for a perfect
  `G`.
* `triangEnvelope_eq_perfectObjects_of_isWeakTriangulatedGenerator`: **[Stacks, Tag 0GEF]**, that a
  perfect generator of `D_QCoh(𝒪_X)` is a classical generator of `D_perf(𝒪_X)`.
* `isCompactObject_eq_perfectObjects_of_isWeakTriangulatedGenerator`: the compact objects of
  `D_QCoh(𝒪_X)` are its perfect objects, for a quasi-compact quasi-separated `X` admitting a
  perfect generator.

## Implementation notes

Everything is read at the locally small derived category
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, so that `D_QCoh(𝒪_X)`, which is
`Stacks.Duality.quasiCoherentDerivedCategory X`, has its morphisms in the universe `u` of the
scheme. [Derived Categories, Tag 09SR] is stated for a category with direct sums indexed by its own
morphism universe, and at `CategoryTheory.HasDerivedCategory.standard` that universe is `u + 1`,
where those direct sums do not exist.

## References

* [The Stacks Project, Remark 36.17.2 (0GEF)](https://stacks.math.columbia.edu/tag/0GEF)
* [The Stacks Project, Lemma 36.3.1 (08DT)](https://stacks.math.columbia.edu/tag/08DT)
* [The Stacks Project, Proposition 36.17.1 (09M1)](https://stacks.math.columbia.edu/tag/09M1)
* [The Stacks Project, Proposition 13.37.6 (09SR)](https://stacks.math.columbia.edu/tag/09SR)
* [The Stacks Project, Lemma 13.5.1 (0ATH)](https://stacks.math.columbia.edu/tag/0ATH)
* [The Stacks Project, Theorem 36.15.3 (09IS)](https://stacks.math.columbia.edu/tag/09IS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty
open scoped ZeroObject

universe v u

namespace CategoryTheory.ObjectProperty

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{v} D]

/-- **A compact generator classically generates a thick subcategory of compact objects.** Let `D`
be a triangulated category with direct sums, let `E` be a compact object of `D` which is a weak
generator of `D`, and let `P` be a property of objects of `D` which is closed under finite direct
sums, satisfies the two-out-of-three property for distinguished triangles, is closed under direct
summands, holds on every shift of `E`, and holds only on compact objects. Then `P` is exactly the
triangulated envelope `⟨E⟩` of `E`. -/
theorem triangEnvelope_eq_of_le_isCompactObject_of_isWeakTriangulatedGenerator
    (E : D) [IsCompactObject.{v} E] (P : ObjectProperty D)
    (hsum : ∀ K L : D, P K → P L → P (K ⊞ L))
    (hext₁ : ∀ T ∈ distTriang D, P T.obj₂ → P T.obj₃ → P T.obj₁)
    (hext₂ : ∀ T ∈ distTriang D, P T.obj₁ → P T.obj₃ → P T.obj₂)
    (hext₃ : ∀ T ∈ distTriang D, P T.obj₁ → P T.obj₂ → P T.obj₃)
    (hsummand : ∀ K L : D, P (K ⊞ L) → P K ∧ P L)
    (hshift : ∀ n : ℤ, P ((CategoryTheory.shiftFunctor D n).obj E))
    (hcompact : P ≤ IsCompactObject.{v, _, _} (C := D))
    (hgen : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton E).triangEnvelope = P := by
  refine le_antisymm (triangEnvelope_singleton_le_of_sums_of_extensions_of_summands E P hsum
    hext₁ hext₂ hext₃ hsummand hshift) ?_
  rw [((isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated
    E).1 hgen).1]
  exact hcompact

end CategoryTheory.ObjectProperty

namespace Stacks.Duality.PerfectClassicalGenerator

variable (X : Scheme.{u})

/-- The quasi-coherence property that cuts `D_QCoh(𝒪_X)` out of `D(𝒪_X)`. -/
private abbrev qcoh : ObjectProperty (DerivedCategory X.Modules) :=
  DerivedCategoryB.derivedCategoryB (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf)

/-- **`D_perf(𝒪_X)` as a property of the objects of `D_QCoh(𝒪_X)`**: an object of the
quasi-coherent derived category is in it when the object of `D(𝒪_X)` underlying it is perfect in
the sense of [Stacks, Tag 08CM]. -/
def perfectObjects : ObjectProperty (Stacks.Duality.quasiCoherentDerivedCategory X) :=
  fun K => Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj

variable {X}

/-- An object of `D_QCoh(𝒪_X)` is perfect exactly when the object of `D(𝒪_X)` underlying it is
perfect. -/
theorem perfectObjects_iff (K : Stacks.Duality.quasiCoherentDerivedCategory X) :
    perfectObjects X K ↔
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K.obj :=
  Iff.rfl

/-- The zero object of `D_QCoh(𝒪_X)` is perfect. -/
theorem perfectObjects_zero :
    perfectObjects X (0 : Stacks.Duality.quasiCoherentDerivedCategory X) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (((qcoh X).ι.map_isZero (isZero_zero _)).isoZero.symm)
    Stacks.Cohomology.PerfectTriangulatedSubcategory.isPerfect_zero

/-- Perfectness of an object of `D_QCoh(𝒪_X)` depends only on its isomorphism class. -/
instance isClosedUnderIsomorphisms_perfectObjects :
    (perfectObjects X).IsClosedUnderIsomorphisms where
  of_iso e hK :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso ((qcoh X).ι.mapIso e) hK

/-- A shift of a perfect object of `D_QCoh(𝒪_X)` is perfect. -/
theorem perfectObjects_shift {K : Stacks.Duality.quasiCoherentDerivedCategory X}
    (hK : perfectObjects X K) (n : ℤ) : perfectObjects X (K⟦n⟧) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (((qcoh X).ι.commShiftIso n).app K).symm
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hK n)

/-- **Two out of three, second object.** If the outer two objects of a distinguished triangle in
`D_QCoh(𝒪_X)` are perfect, so is the middle one. -/
theorem perfectObjects_obj₂_of_distinguished
    (T : Triangle (Stacks.Duality.quasiCoherentDerivedCategory X))
    (hT : T ∈ distTriang (Stacks.Duality.quasiCoherentDerivedCategory X))
    (h₁ : perfectObjects X T.obj₁) (h₃ : perfectObjects X T.obj₃) :
    perfectObjects X T.obj₂ :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished
    ((qcoh X).ι.mapTriangle.obj T) ((qcoh X).ι.map_distinguished T hT) h₁ h₃

/-- **Two out of three, first object.** If the last two objects of a distinguished triangle in
`D_QCoh(𝒪_X)` are perfect, so is the first. -/
theorem perfectObjects_obj₁_of_distinguished
    (T : Triangle (Stacks.Duality.quasiCoherentDerivedCategory X))
    (hT : T ∈ distTriang (Stacks.Duality.quasiCoherentDerivedCategory X))
    (h₂ : perfectObjects X T.obj₂) (h₃ : perfectObjects X T.obj₃) :
    perfectObjects X T.obj₁ :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished
    ((qcoh X).ι.mapTriangle.obj T) ((qcoh X).ι.map_distinguished T hT) h₂ h₃

/-- **Two out of three, third object.** If the first two objects of a distinguished triangle in
`D_QCoh(𝒪_X)` are perfect, so is the third. -/
theorem perfectObjects_obj₃_of_distinguished
    (T : Triangle (Stacks.Duality.quasiCoherentDerivedCategory X))
    (hT : T ∈ distTriang (Stacks.Duality.quasiCoherentDerivedCategory X))
    (h₁ : perfectObjects X T.obj₁) (h₂ : perfectObjects X T.obj₂) :
    perfectObjects X T.obj₃ :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
    ((qcoh X).ι.mapTriangle.obj T) ((qcoh X).ι.map_distinguished T hT) h₁ h₂

/-- **A direct sum of two perfect objects of `D_QCoh(𝒪_X)` is perfect.** -/
theorem perfectObjects_biprod (K L : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hK : perfectObjects X K) (hL : perfectObjects X L) : perfectObjects X (K ⊞ L) :=
  perfectObjects_obj₂_of_distinguished (binaryBiproductTriangle K L)
    (binaryBiproductTriangle_distinguished K L) hK hL

/-- **A retract of a perfect object of `D_QCoh(𝒪_X)` is perfect.** -/
instance isStableUnderRetracts_perfectObjects :
    (perfectObjects X).IsStableUnderRetracts := by
  constructor
  intro A B r hB
  have hir : (qcoh X).ι.map r.i ≫ (qcoh X).ι.map r.r = CategoryStruct.id A.obj := by
    rw [← (qcoh X).ι.map_comp]
    rw [r.retract]
    exact (qcoh X).ι.map_id A
  exact Stacks.Cohomology.PerfectDirectSummands.isPerfect_of_retract _ _ hir hB

/-- **A direct summand of a perfect object of `D_QCoh(𝒪_X)` is perfect** ([Stacks, Tag 08CS]). -/
theorem perfectObjects_of_biprod (K L : Stacks.Duality.quasiCoherentDerivedCategory X)
    (h : perfectObjects X (K ⊞ L)) : perfectObjects X K ∧ perfectObjects X L :=
  ⟨ObjectProperty.IsStableUnderRetracts.of_biprod_left _ h,
    ObjectProperty.IsStableUnderRetracts.of_biprod_right _ h⟩

/-- **`D_perf(𝒪_X)` is a triangulated subcategory of `D_QCoh(𝒪_X)`**: it contains a zero object, is
stable under all shifts, and is closed under extensions. -/
instance isTriangulated_perfectObjects : (perfectObjects X).IsTriangulated where
  toContainsZero := ⟨⟨0, isZero_zero _, perfectObjects_zero⟩⟩
  toIsStableUnderShift := ⟨fun n => ⟨fun _ hK => perfectObjects_shift hK n⟩⟩
  toIsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' fun T hT h₁ h₃ =>
      perfectObjects_obj₂_of_distinguished T hT h₁ h₃

/-- **`D_perf(𝒪_X)` is saturated in `D_QCoh(𝒪_X)`** ([Stacks, Tag 05RB]): a direct summand of a
perfect object is perfect. -/
instance isSaturated_perfectObjects : (perfectObjects X).IsSaturated :=
  ObjectProperty.IsSaturated.of_isStableUnderRetracts _

/-- **`D_perf(𝒪_X)` is a thick subcategory of `D_QCoh(𝒪_X)`**: strictly full, triangulated and
saturated. -/
theorem isClosedUnderIsomorphisms_isTriangulated_and_isSaturated_perfectObjects
    (X : Scheme.{u}) :
    (perfectObjects X).IsClosedUnderIsomorphisms ∧ (perfectObjects X).IsTriangulated ∧
      (perfectObjects X).IsSaturated :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Every object built from a perfect `G` is perfect**, i.e. `⟨G⟩ ≤ D_perf(𝒪_X)`. No hypothesis
on `X` is needed. -/
theorem triangEnvelope_singleton_le_perfectObjects
    (G : Stacks.Duality.quasiCoherentDerivedCategory X) (hG : perfectObjects X G) :
    (ObjectProperty.singleton G).triangEnvelope ≤ perfectObjects X :=
  ObjectProperty.triangEnvelope_singleton_le_of_sums_of_extensions_of_summands G
    (perfectObjects X) perfectObjects_biprod
    (fun T hT => perfectObjects_obj₁_of_distinguished T hT)
    (fun T hT => perfectObjects_obj₂_of_distinguished T hT)
    (fun T hT => perfectObjects_obj₃_of_distinguished T hT)
    perfectObjects_of_biprod
    fun n => perfectObjects_shift hG n

/-- For a perfect generator `G`, the triangulated envelope `⟨G⟩` consists of the compact objects. -/
private theorem triangEnvelope_singleton_eq_isCompactObject [CompactSpace X] [QuasiSeparatedSpace X]
    (G : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hG : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) G.obj)
    (hgen : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton G).triangEnvelope =
      IsCompactObject.{u, _, _} (C := Stacks.Duality.quasiCoherentDerivedCategory X) :=
  have : IsCompactObject.{u} G := Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect X G hG
  ((isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated
      G).1 hgen).1

/-- **Stacks 0GEF**. Let `X` be a quasi-compact and quasi-separated scheme and let `G` be a perfect
object of `D(𝒪_X)` lying in `D_QCoh(𝒪_X)` and generating it, in the sense that an object of
`D_QCoh(𝒪_X)` receiving only zero morphisms from the shifts of `G` is zero. Then `G` is a classical
generator of `D_perf(𝒪_X)`: the smallest strictly full triangulated subcategory of `D_QCoh(𝒪_X)`
closed under direct summands and containing `G` is exactly the subcategory of perfect objects. -/
@[stacks 0GEF "for X quasi-compact and quasi-separated and G a perfect object generating \
D_QCoh(O_X), G is a classical generator of D_perf(O_X): the triangulated envelope of G is exactly \
the perfect objects"]
theorem triangEnvelope_eq_perfectObjects_of_isWeakTriangulatedGenerator
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (G : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hG : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) G.obj)
    (hgen : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton G).triangEnvelope = perfectObjects X :=
  le_antisymm (triangEnvelope_singleton_le_perfectObjects G hG)
    ((triangEnvelope_singleton_eq_isCompactObject G hG hgen) ▸ fun _ hK =>
      Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect X _ hK)

/-- **The compact objects of `D_QCoh(𝒪_X)` are its perfect objects**, for a quasi-compact
quasi-separated `X` admitting a perfect generator — i.e. [Stacks, Tag 09M1] in both directions at
the locally small model. -/
theorem isCompactObject_eq_perfectObjects_of_isWeakTriangulatedGenerator
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (G : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hG : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) G.obj)
    (hgen : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) :
    (IsCompactObject.{u, _, _} (C := Stacks.Duality.quasiCoherentDerivedCategory X)) =
      perfectObjects X :=
  (triangEnvelope_singleton_eq_isCompactObject G hG hgen).symm.trans
    (triangEnvelope_eq_perfectObjects_of_isWeakTriangulatedGenerator X G hG hgen)

end Stacks.Duality.PerfectClassicalGenerator

end
