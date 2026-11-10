module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Ring
public import StacksFrontier.CategoryTheory.Localization.Saturated.Defs
import StacksFrontier.CategoryTheory.Triangulated.Localization
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.CategoryTheory.Triangulated.ZeroRetract

/-!
# Quotients of a triangulated category

Let `C` be a triangulated category. The quotient of `C` by a full triangulated subcategory `P`
is the localization of `C` at the class `P.trW` of morphisms whose cone lies in `P`. This file
develops that construction: the two standard sources of a subcategory to quotient by, the class
of morphisms attached to a subcategory, the kernel of the quotient functor, and the resulting
bijection between subcategories and multiplicative systems.

Two subcategories are shown to be saturated pre-triangulated subcategories. The kernel of an
exact functor `F : C ⥤ D` — the objects `X` with `F X = 0` — and the kernel of a homological
functor `H : C ⥤ A` to an abelian category — the objects `X` with `H (X⟦n⟧) = 0` for every
`n : ℤ`. In both cases being a pre-triangulated subcategory comes from pulling the
corresponding property of the zero objects back along the functor, while saturation comes from
a stronger and cheaper statement: a retract of a zero object is zero, retracts are preserved by
every functor, and a direct summand is a retract, so both kernels are stable under retracts,
with no exactness hypothesis at all. Both are strictly full, and both become triangulated
subcategories as soon as `C` is a triangulated category.

Conversely a full triangulated subcategory `P` determines the class `S` of morphisms whose cone
is isomorphic to an object of `P`. That class is a multiplicative system compatible with the
triangulated structure — its multiplicativity and its compatibility with the triangulation rest
on the octahedron axiom — and it is *saturated* exactly when `P` is a saturated subcategory. The
octahedron argument for the cancellation axiom runs on the two triangles it produces out of
three composable morphisms: rotating them puts two morphisms in `S` whose composite is zero, and
a cone of a zero morphism is a biproduct, so saturation of `P` recovers the cone of the middle
morphism. In the other direction, a distinguished triangle on the inclusion `X ⟶ X ⊞ Y` has its
first morphism zero, and the cancellation axiom applied to it exhibits `X` as a cone of a
morphism of `S`.

Localizing at `S` gives the quotient `C/P`, and the kernel of the quotient functor is the
closure of `P` under direct summands: an object `Z` is killed exactly when some `Z ⊞ Z'` is
isomorphic to an object of `P`. Equivalently that kernel is the smallest strictly full saturated
triangulated subcategory containing `P`. Combining this with the observation that the class of
morphisms whose cone is killed by a localization at `S` is the class of morphisms the
localization inverts, the two constructions `S ↦ Ker(Q)` and `P ↦ P.trW` are mutually inverse,
order preserving bijections between the saturated multiplicative systems of `C` compatible with
the triangulated structure and the strictly full saturated triangulated subcategories of `C`;
each round trip on a non-saturated input is the saturation.

The kernel of a homological functor is the case of this correspondence that occurs in practice:
its associated class is the class of morphisms `f` with `Hⁱ(f)` invertible for every `i : ℤ`, by
the long exact cohomology sequence, and consequently `H` and each of its shifts factor through
the quotient of `C` by that kernel.

## Main results

* `CategoryTheory.Functor.isTriangulated_and_isSaturated_kernel`: for an exact functor `F`, the
  kernel of `F` is a saturated pre-triangulated subcategory of `C`.
* `CategoryTheory.Functor.isTriangulated_and_isSaturated_homologicalKernel`: the same for the
  kernel of a homological functor.
* `hasCalculusOfFractions_isCompatibleWithTriangulation_and_isSaturated_iff`, in the
  `CategoryTheory.ObjectProperty` namespace: the class of morphisms whose cone lies in a full
  triangulated subcategory `P` is a multiplicative system compatible with the triangulated
  structure, and it is saturated exactly when `P` is.
* `CategoryTheory.ObjectProperty.kernel_iff_exists_isoClosure_biprod_and_isLeast_kernel`: the
  kernel of a quotient functor consists of the direct summands of the objects of `P`, and is the
  smallest strictly full saturated triangulated subcategory containing `P`.
* `CategoryTheory.ObjectProperty.isLeast_trW_kernel_and_kernel_eq_self`: each round trip of the
  two constructions saturates, so on saturated inputs they are mutually inverse.
* `CategoryTheory.Functor.isSaturated_homologicalKernel_and_mem_trW_iff_and_exists_lift`: the
  kernel of a homological functor, the identification of its class of morphisms with the
  quasi-isomorphisms of `H`, and the factorizations of `H` and its shifts through the quotient.
* `StacksBoundedSubcategories.boundedBelow_isTriangulated`,
  `StacksBoundedSubcategories.boundedBelow_isSaturated` and their analogues for `boundedAbove`
  and `bounded`: for a homological functor `H`, the objects `X` with `H (X⟦n⟧) = 0` for `n ≪ 0`,
  for `n ≫ 0`, or for `|n| ≫ 0` form strictly full saturated pre-triangulated subcategories.
* `VerdierQuotientUniversalProperty.homological_universal_property` and
  `VerdierQuotientUniversalProperty.exact_universal_property`: a homological, respectively exact,
  functor killing `P` factors through the quotient functor `C ⥤ C/P`, uniquely up to unique
  isomorphism, and the factorization is again homological, respectively exact.

## Implementation notes

A *pre-triangulated subcategory* is a `P : ObjectProperty C` with
`CategoryTheory.ObjectProperty.IsTriangulated P`, Mathlib's form of the criterion of
[Stacks, Tag 05QX]: it packages that `P` contains the zero object, is stable under the shift by
`ℤ`, and is closed under extensions in distinguished triangles, and it is exactly what equips
`P.FullSubcategory` with a pre-triangulated structure for which the inclusion is exact. Being
*strictly full* is `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms`, and being
*saturated* — or *thick* — is `CategoryTheory.ObjectProperty.IsSaturated`. None of the
statements below asserts separately that a kernel is a triangulated subcategory when `C` is
triangulated: that is `ObjectProperty.instIsTriangulatedFullSubcategory` applied to the
pre-triangulated conjunct, with nothing added.

Saturation of a subcategory is deduced throughout from the stronger
`ObjectProperty.IsStableUnderRetracts`, which holds at a generality the source does not use: for
the kernel of an *arbitrary* functor, with no exactness hypothesis and no hypothesis on the
target beyond the existence of zero morphisms. The helpers are stated at that generality, and
`ObjectProperty.IsSaturated` being a condition on `P.isoClosure`, they are phrased so that no
hypothesis that `P` is closed under isomorphisms is needed.

Where a class of morphisms is characterised by a display, it enters as an arbitrary
`S : MorphismProperty C` together with a hypothesis identifying its members, so the result
applies verbatim to every spelling of that class — in particular to Mathlib's
`ObjectProperty.trW`. Likewise the quotient is never a chosen construction: the statements are
about an arbitrary `L : C ⥤ D` with `[L.IsLocalization P.trW]`, and nothing is assumed of `D`
beyond that. The statements that do need a structure on the target — that `P` is contained in
the kernel, and that the kernel is a saturated triangulated subcategory — are proved for the
canonical model `P.trW.Q` and transported along `kernel_eq_of_isLocalization`: two localizations
of `C` at the same class have the same kernel, being equivalent over `C`, and an equivalence
both preserves and reflects zero objects.

Subcategories are not assumed closed under isomorphisms, matching the source, which is why the
statements about the class attached to `P` and about saturation are phrased through
`P.isoClosure`, as the source phrases them through "isomorphic to an object of `P`".

## References

* [Stacks, Tag 05RC](https://stacks.math.columbia.edu/tag/05RC),
  [Tag 05RD](https://stacks.math.columbia.edu/tag/05RD),
  [Tag 05RE](https://stacks.math.columbia.edu/tag/05RE),
  [Tag 05RG](https://stacks.math.columbia.edu/tag/05RG),
  [Tag 05RJ](https://stacks.math.columbia.edu/tag/05RJ),
  [Tag 05RK](https://stacks.math.columbia.edu/tag/05RK),
  [Tag 05RL](https://stacks.math.columbia.edu/tag/05RL),
  [Tag 05RM](https://stacks.math.columbia.edu/tag/05RM).
* Saturated subcategories are [Stacks, Tag 05RB], saturated multiplicative systems are
  [Stacks, Tag 05Q8], the criterion for a pre-triangulated subcategory is [Stacks, Tag 05QX],
  and the characterisations of the objects killed by a quotient functor are [Stacks, Tag 05R8].
-/

@[expose] public section

universe v v' v'' v₁ v₂ u u' u'' u₁ u₂

/-! ### Saturated properties of objects -/

section Saturated

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : ObjectProperty C)

/-- A property `P` of the objects of a category with zero morphisms is *saturated* if whenever
a biproduct `X ⊞ Y` is isomorphic to an object satisfying `P`, then both `X` and `Y` are
isomorphic to objects satisfying `P`; equivalently, the objects isomorphic to an object
satisfying `P` are closed under direct summands. For a pre-triangulated subcategory, this is
also called being a *thick* subcategory. -/
@[stacks 05RB, sga "4½ Etat_0 2.1.1" "partial"]
public class IsSaturated : Prop where
  /-- If `X ⊞ Y` is isomorphic to an object satisfying `P`, then so is `X`. -/
  isoClosure_of_biprod_left {X Y : C} [HasBinaryBiproduct X Y] (h : P.isoClosure (X ⊞ Y)) :
    P.isoClosure X
  /-- If `X ⊞ Y` is isomorphic to an object satisfying `P`, then so is `Y`. -/
  isoClosure_of_biprod_right {X Y : C} [HasBinaryBiproduct X Y] (h : P.isoClosure (X ⊞ Y)) :
    P.isoClosure Y

/-- A property of objects that is stable under retracts is saturated: a direct summand of an
object is a retract of it, and a property stable under retracts is closed under isomorphisms,
so that it coincides with its isomorphism closure. -/
public lemma IsSaturated.of_isStableUnderRetracts [P.IsStableUnderRetracts] : P.IsSaturated where
  isoClosure_of_biprod_left h := by
    rw [P.isoClosure_eq_self] at h ⊢
    exact IsStableUnderRetracts.of_biprod_left P h
  isoClosure_of_biprod_right h := by
    rw [P.isoClosure_eq_self] at h ⊢
    exact IsStableUnderRetracts.of_biprod_right P h

end CategoryTheory.ObjectProperty

end Saturated

/-! ### Retracts, saturation, and the kernel of a functor -/

section Retracts

open CategoryTheory Limits ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- If `P` is stable under retracts, so is the property of being isomorphic to an object
satisfying `P`: the two properties agree, `P` being closed under isomorphisms. -/
private theorem isStableUnderRetracts_isoClosure (P : ObjectProperty C)
    [P.IsStableUnderRetracts] : P.isoClosure.IsStableUnderRetracts := by
  rw [P.isoClosure_eq_self]; infer_instance

namespace CategoryTheory.ObjectProperty

/-- A property of objects whose isomorphism closure is stable under retracts is saturated in
the sense of [Stacks, Tag 05RB], a direct summand of an object being a retract of it. -/
theorem isSaturated_of_isStableUnderRetracts_isoClosure [HasZeroMorphisms C]
    (P : ObjectProperty C) [P.isoClosure.IsStableUnderRetracts] : P.IsSaturated where
  isoClosure_of_biprod_left := IsStableUnderRetracts.of_biprod_left _
  isoClosure_of_biprod_right := IsStableUnderRetracts.of_biprod_right _

end CategoryTheory.ObjectProperty

/-- The kernel of an arbitrary functor `F` on a category with a shift by `ℤ` — the objects `X`
with `F (X⟦n⟧)` zero for every `n` — is stable under retracts: a retract `X` of `Y` gives a
retract `F (X⟦n⟧)` of `F (Y⟦n⟧)` for every `n : ℤ`, by applying `shiftFunctor C n ⋙ F`. -/
private theorem isStableUnderRetracts_homologicalKernel {A : Type u'} [Category.{v'} A]
    [HasShift C ℤ] [HasZeroMorphisms A] (F : C ⥤ A) :
    F.homologicalKernel.IsStableUnderRetracts where
  of_retract h hY n := (hY n).of_retract (h.map (shiftFunctor C n ⋙ F))

end Retracts

/-! ### The kernel of a localization functor -/

section Model

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

/-- An equivalence of categories both preserves and reflects zero objects. Neither category is
assumed to have a zero object. -/
private theorem isZero_functor_obj_iff {D₁ : Type u₁} {D₂ : Type u₂} [Category.{v₁} D₁]
    [Category.{v₂} D₂] (e : D₁ ≌ D₂) (X : D₁) : IsZero (e.functor.obj X) ↔ IsZero X :=
  ⟨fun h ↦ IsZero.of_full_of_faithful_of_isZero e.functor X h,
    fun h ↦ IsZero.of_full_of_faithful_of_isZero e.inverse _
      (h.of_iso (e.unitIso.app X).symm)⟩

/-- The kernel of a localization functor depends only on the class of morphisms that is
inverted, not on the model of the localized category. -/
private theorem kernel_eq_of_isLocalization {D₁ : Type u₁} {D₂ : Type u₂} [Category.{v₁} D₁]
    [Category.{v₂} D₂] (W : MorphismProperty C) (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂)
    [L₁.IsLocalization W] [L₂.IsLocalization W] : L₁.kernel = L₂.kernel := by
  ext Z
  exact (isZero_functor_obj_iff (Localization.uniq L₁ L₂ W) (L₁.obj Z)).symm.trans
    ((Localization.compUniqFunctor L₁ L₂ W).app Z).isZero_iff

/-- The kernel of a functor is closed under isomorphisms. -/
private theorem isClosedUnderIsomorphisms_kernel {D₁ : Type u₁} [Category.{v₁} D₁]
    (L : C ⥤ D₁) : L.kernel.IsClosedUnderIsomorphisms where
  of_iso e h := h.of_iso (L.mapIso e).symm

end Model

/-! ### The kernel of an exact functor -/

section KernelExact

open CategoryTheory Limits Pretriangulated ObjectProperty ZeroObject

section

variable {D : Type u'} [Category.{v'} D]

/-- The zero objects of a category are stable under retracts: if `X` is a retract of a zero
object `Y`, then the section `h.i` and the retraction `h.r` are mutually inverse, the identity
of `Y` being its only endomorphism, so `X ≅ Y` is zero as well. -/
private theorem isStableUnderRetracts_isZero :
    IsStableUnderRetracts (IsZero : ObjectProperty D) where
  of_retract h hY := hY.of_iso
    { hom := h.i, inv := h.r, hom_inv_id := h.retract, inv_hom_id := hY.eq_of_src _ _ }

/-- The zero objects of a category are stable under a shift whose functors preserve zero
morphisms, because such a functor sends a zero object to a zero object. -/
private theorem isStableUnderShift_isZero {A : Type*} [AddMonoid A] [HasShift D A]
    [HasZeroMorphisms D] [∀ a : A, (shiftFunctor D a).PreservesZeroMorphisms] :
    IsStableUnderShift (IsZero : ObjectProperty D) A where
  isStableUnderShiftBy a := ⟨fun _ hX => (shiftFunctor D a).map_isZero hX⟩

end

section

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

/-- The inverse image of a property stable under retracts is stable under retracts, since a
functor sends a retract to a retract. -/
private theorem isStableUnderRetracts_inverseImage (P : ObjectProperty D)
    [P.IsStableUnderRetracts] (F : C ⥤ D) : (P.inverseImage F).IsStableUnderRetracts where
  of_retract h hY := P.prop_of_retract (h.map F) hY

end

section

variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- If the outer terms of a distinguished triangle are zero, so is the middle term. -/
private theorem isTriangulatedClosed₂_isZero :
    IsTriangulatedClosed₂ (IsZero : ObjectProperty D) :=
  .mk' fun T hT => Triangle.isZero₂_of_isZero₁₃ T hT

end

attribute [local instance] isStableUnderRetracts_isZero isStableUnderShift_isZero
  isTriangulatedClosed₂_isZero isStableUnderRetracts_inverseImage
  isStableUnderRetracts_isoClosure

section

variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The zero objects of a pre-triangulated category form a triangulated subcategory. -/
private theorem isTriangulated_isZero :
    ObjectProperty.IsTriangulated (IsZero : ObjectProperty D) where

end

attribute [local instance] isTriangulated_isZero

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- Let `F : C ⥤ D` be an exact functor of pre-triangulated categories. The full subcategory of `C`
spanned by the objects `X` with `F X = 0`, namely `F.kernel`, is a pre-triangulated subcategory of
`C` which is saturated. It is strictly full (`ObjectProperty.IsClosedUnderIsomorphisms`) without
any hypothesis on `F`, and it is a triangulated subcategory as soon as `C` is a triangulated
category, by `CategoryTheory.ObjectProperty.instIsTriangulatedFullSubcategory`. -/
@[stacks 05RC, sga "4½ Etat_0 2.2" "thickness"]
theorem isTriangulated_and_isSaturated_kernel (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] :
    F.kernel.IsTriangulated ∧ F.kernel.IsSaturated :=
  ⟨inferInstance, isSaturated_of_isStableUnderRetracts_isoClosure _⟩

end CategoryTheory.Functor

end KernelExact

/-! ### The kernel of a homological functor -/

section KernelHomological

open CategoryTheory Limits Pretriangulated ObjectProperty

namespace CategoryTheory.Functor

variable {C : Type u} {A : Type u'} [Category.{v} C] [Category.{v'} A]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

/-- Let `H : C ⥤ A` be a homological functor from a pre-triangulated category to an abelian
category. The full subcategory of `C` spanned by the objects `X` with `H (X⟦n⟧) = 0` for all
`n : ℤ`, namely `H.homologicalKernel`, is a pre-triangulated subcategory of `C` which is saturated.
It is strictly full (`ObjectProperty.IsClosedUnderIsomorphisms`), and it is a triangulated
subcategory as soon as `C` is a triangulated category, by
`CategoryTheory.ObjectProperty.instIsTriangulatedFullSubcategory`. -/
@[stacks 05RD, sga "4½ Etat_0 2.4.1" "thickness"]
theorem isTriangulated_and_isSaturated_homologicalKernel (H : C ⥤ A) [H.IsHomological] :
    H.homologicalKernel.IsTriangulated ∧ H.homologicalKernel.IsSaturated :=
  have := isStableUnderRetracts_homologicalKernel H
  ⟨inferInstance, IsSaturated.of_isStableUnderRetracts _⟩

end CategoryTheory.Functor

end KernelHomological

/-! ### The two kernels agree -/

section KernelsAgree

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasShift C ℤ] [HasShift D ℤ]

/-- The kernel of a functor `F` commuting with the shift by `ℤ`, described as in [Stacks, Tag 05RD]
by the vanishing of `F (X⟦n⟧)` for all `n : ℤ`, is described as in [Stacks, Tag 05RC] by the
vanishing of `F X`: the homological kernel and the kernel of such a functor — in particular of an
exact functor of pre-triangulated categories — are the same strictly full subcategory of `C`. -/
@[stacks 05RF]
public theorem homologicalKernel_eq_kernel (F : C ⥤ D) [F.CommShift ℤ] :
    F.homologicalKernel = F.kernel := by
  ext X
  constructor
  · intro h
    exact (h 0).of_iso (F.mapIso ((shiftFunctorZero C ℤ).app X).symm)
  · intro h n
    refine (?_ : IsZero ((F.obj X)⟦n⟧)).of_iso ((F.commShiftIso n).app X)
    refine IsZero.of_full_of_faithful_of_isZero (shiftFunctor D (-n)) _ ?_
    exact h.of_iso ((shiftEquiv D n).unitIso.app (F.obj X)).symm

end CategoryTheory.Functor

end KernelsAgree

/-! ### The multiplicative system attached to a full triangulated subcategory -/

section Attached

open CategoryTheory Category Limits Preadditive Pretriangulated Triangulated ZeroObject

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If a cone of the zero morphism `A ⟶ B` satisfies an object property `Q` which is closed
under isomorphisms, under shifts and under direct summands, then so do `A` and `B`: such a
cone is isomorphic to `B ⊞ A⟦1⟧`. -/
private lemma prop_and_prop_of_trW_zero (Q : ObjectProperty C) [Q.IsStableUnderShift ℤ]
    [Q.IsClosedUnderIsomorphisms] (hQ : ∀ {X Y : C}, Q (X ⊞ Y) → Q X ∧ Q Y)
    {A B : C} (h : Q.trW (0 : A ⟶ B)) : Q A ∧ Q B := by
  obtain ⟨Z, g, k, hT, hZ⟩ := h
  obtain ⟨e, -, -⟩ :=
    exists_iso_binaryBiproduct_of_distTriang _ (rot_of_distTriang _ hT) (by cat_disch)
  obtain ⟨hB, hA⟩ := hQ (Q.prop_of_iso e hZ)
  exact ⟨(Q.prop_shift_iff_of_isStableUnderShift A 1).1 hA, hB⟩

/-- One half of the cancellation axiom MS4 for the class of morphisms whose cone satisfies
`Q`: if that class satisfies MS4, then `Q` is closed under direct summands. -/
private lemma prop_of_prop_biprod (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms]
    (hMS4 : ∀ {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
      Q.trW (f ≫ g) → Q.trW (g ≫ h) → Q.trW g)
    {X Y : C} [HasBinaryBiproduct X Y] (h : Q (X ⊞ Y)) : Q X := by
  obtain ⟨A, f, k, hT⟩ := distinguished_cocone_triangle₁ (biprod.inl : X ⟶ X ⊞ Y)
  have hf : f = 0 := by
    have h₁ : f ≫ (biprod.inl : X ⟶ X ⊞ Y) = 0 := comp_distTriang_mor_zero₁₂ _ hT
    simpa using congrArg (fun φ => φ ≫ (biprod.fst : X ⊞ Y ⟶ X)) h₁
  have h₀ : Q.trW (0 : A ⟶ X) := by rw [← hf]; exact ObjectProperty.trW.mk Q hT h
  refine (Q.trW_iff_of_distinguished _ (contractible_distinguished₁ X)).1
    (hMS4 (0 : A ⟶ 0) _ (biprod.inl : X ⟶ X ⊞ Y) ?_ ?_)
  · simpa using h₀
  · simpa using ObjectProperty.trW.mk Q (contractible_distinguished₁ (X ⊞ Y)) h

end

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- The cancellation axiom MS4 for the class of morphisms whose cone satisfies `Q`, when `Q` is
a triangulated subcategory closed under isomorphisms and under direct summands: if the
composites `a ≫ b` and `b ≫ c` have their cones in `Q`, then so does `b`. This is the
octahedron argument of [Stacks, Tag 05RG]. -/
private lemma trW_mem_of_comp_mem_comp_of_isTriangulated (Q : ObjectProperty C)
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms] (hQ : ∀ {X Y : C}, Q (X ⊞ Y) → Q X ∧ Q Y)
    {W X Y Z : C} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (hab : Q.trW (a ≫ b)) (hbc : Q.trW (b ≫ c)) : Q.trW b := by
  obtain ⟨Q₁, v₁, w₁, hT₁⟩ := distinguished_cocone_triangle a
  obtain ⟨Q₂, v₂, w₂, hT₂⟩ := distinguished_cocone_triangle b
  obtain ⟨Q₃, v₃, w₃, hT₃⟩ := distinguished_cocone_triangle c
  obtain ⟨Q₁₂, v₁₂, w₁₂, hT₁₂, hQ₁₂⟩ := hab
  obtain ⟨Q₂₃, v₂₃, w₂₃, hT₂₃, hQ₂₃⟩ := hbc
  have H := someOctahedron (u₁₂ := a) (u₂₃ := b) rfl hT₁ hT₂ hT₁₂
  have H' := someOctahedron (u₁₂ := b) (u₂₃ := c) rfl hT₂ hT₃ hT₂₃
  have hs : Q.trW (w₂ ≫ v₁⟦(1 : ℤ)⟧') :=
    ObjectProperty.trW.mk' Q (rot_of_distTriang _ H.mem) hQ₁₂
  have ht : Q.trW (w₃ ≫ v₂⟦(1 : ℤ)⟧') :=
    ObjectProperty.trW.mk' Q (rot_of_distTriang _ H'.mem) hQ₂₃
  have hz := Q.trW.comp_mem _ _ ht (hs.shift 1)
  have hzero : (w₃ ≫ v₂⟦(1 : ℤ)⟧') ≫ (w₂ ≫ v₁⟦(1 : ℤ)⟧')⟦(1 : ℤ)⟧' = 0 := by
    have h₀ : v₂ ≫ w₂ = 0 := comp_distTriang_mor_zero₂₃ _ hT₂
    rw [Functor.map_comp, assoc, ← assoc (v₂⟦(1 : ℤ)⟧'), ← Functor.map_comp, h₀,
      Functor.map_zero, zero_comp, comp_zero]
  rw [hzero] at hz
  obtain ⟨hQ₃, hQ₁'⟩ := prop_and_prop_of_trW_zero Q hQ hz
  have hQ₁ : Q Q₁ := by
    rw [← Q.prop_shift_iff_of_isStableUnderShift Q₁ (1 : ℤ),
      ← Q.prop_shift_iff_of_isStableUnderShift (Q₁⟦(1 : ℤ)⟧) (1 : ℤ)]
    exact hQ₁'
  have hQ₂ := Q.ext_of_isTriangulatedClosed₃ _ H.mem hQ₁ hQ₁₂
  exact ObjectProperty.trW.mk Q hT₂ hQ₂

end

end Attached

section AttachedMain

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- Let `C` be a triangulated category, let `P` be a full triangulated subcategory of `C`, and let
`S` be the class of morphisms `f` that fit into a distinguished triangle `(X, Y, Z, f, g, h)` with
`Z` isomorphic to an object of `P`. Then `S` is a multiplicative system (MS1, MS2, MS3, i.e. a left
and a right calculus of fractions) compatible with the triangulated structure on `C` (MS5, MS6),
and `S` is a saturated multiplicative system ([Stacks, Tag 05Q8]) if and only if `P` is saturated
([Stacks, Tag 05RB]). -/
@[stacks 05RG, sga "4½ Etat_0 2.2" "S=φ(B) sat. mult. system", sga "4½ Etat_0 2.3.1" "special case"]
theorem hasCalculusOfFractions_isCompatibleWithTriangulation_and_isSaturated_iff
    (P : ObjectProperty C) [P.IsTriangulated] (S : MorphismProperty C)
    (hS : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), S f ↔ ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧ P.isoClosure Z) :
    (S.HasLeftCalculusOfFractions ∧ S.HasRightCalculusOfFractions ∧
      S.IsCompatibleWithTriangulation) ∧ (S.IsSaturated ↔ P.IsSaturated) := by
  have hSW : S = P.trW := by
    ext X Y f
    rw [hS f, ← P.trW_isoClosure]
    exact ⟨fun ⟨Z, g, h, hT, hZ⟩ => ⟨Z, g, h, hT, hZ⟩,
      fun ⟨Z, g, h, hT, hZ⟩ => ⟨Z, g, h, hT, hZ⟩⟩
  subst hSW
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, ?_, ?_⟩
  · intro hsat
    have hMS4 : ∀ {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
        P.isoClosure.trW (f ≫ g) → P.isoClosure.trW (g ≫ h) → P.isoClosure.trW g := by
      intro X Y Z T f g h hfg hgh
      rw [P.trW_isoClosure] at hfg hgh ⊢
      exact hsat.mem_of_comp_mem_comp f g h hfg hgh
    exact
      { isoClosure_of_biprod_left := fun h => prop_of_prop_biprod _ hMS4 h
        isoClosure_of_biprod_right := fun h =>
          prop_of_prop_biprod _ hMS4 (P.isoClosure.prop_of_iso (biprod.braiding _ _) h) }
  · intro hP
    have hQ : ∀ {X Y : C}, P.isoClosure (X ⊞ Y) → P.isoClosure X ∧ P.isoClosure Y :=
      fun h => ⟨hP.isoClosure_of_biprod_left h, hP.isoClosure_of_biprod_right h⟩
    refine ⟨inferInstance, inferInstance, fun f g h hfg hgh => ?_⟩
    rw [← P.trW_isoClosure] at hfg hgh ⊢
    exact trW_mem_of_comp_mem_comp_of_isTriangulated P.isoClosure hQ f g h hfg hgh

end CategoryTheory.ObjectProperty

end AttachedMain

/-! ### The quotient category -/

section QuotientCategory

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The *quotient category* `C/P` of a pretriangulated category `C` by a subcategory
`P : ObjectProperty C`: the localization `S⁻¹C` of `C` at the class `S = P.trW` of morphisms whose
cone lies in `P`, which for `P` a full triangulated subcategory of a triangulated category is a
multiplicative system ([Stacks, Tag 05RG]). The *quotient functor* `Q : C ⥤ C/P` is the
localization functor `P.trW.Q` of this localization.

In that triangulated situation this is the Verdier quotient: `C/P` is then triangulated and the
quotient functor is exact ([Stacks, Tag 05R6]). -/
@[stacks 05RI,
  sga "4½ Etat_0 2.3.3",
  sga "4½ Etat_0 2.5",
  sga "4½ Etat_0 Problem1",
  sga "4½ Etat_0 Problem2"]
public abbrev verdierQuotient (P : ObjectProperty C) : Type u :=
  P.trW.Localization

end CategoryTheory.ObjectProperty

end QuotientCategory

/-! ### The kernel of a quotient functor -/

section QuotientKernel

open CategoryTheory Limits Pretriangulated ObjectProperty ZeroObject

section

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- An object killed by a localization of `C` at `P.trW` is a direct summand of an object
isomorphic to an object of `P`: this is the implication (1) ⇒ (3) ⇒ (4) of
[Stacks, Tag 05R8]. -/
private lemma exists_isoClosure_biprod (P : ObjectProperty C) [P.IsTriangulated]
    [IsTriangulated C] (L : C ⥤ D) [L.IsLocalization P.trW] {Z : C} (hZ : IsZero (L.obj Z)) :
    ∃ Z' : C, P.isoClosure (Z ⊞ Z') := by
  obtain ⟨Y, s, hs, fac⟩ :=
    (MorphismProperty.map_eq_iff_precomp L P.trW (𝟙 Z) 0).1 (hZ.eq_of_src _ _)
  rw [Category.comp_id, comp_zero] at fac
  rw [fac] at hs
  obtain ⟨W, g, h, hT, hW⟩ := (P.trW_iff _).1 hs
  obtain ⟨e, -, -⟩ :=
    exists_iso_binaryBiproduct_of_distTriang _ (rot_of_distTriang _ hT) (by aesop_cat)
  exact ⟨_, P.isoClosure.prop_of_iso e (P.le_isoClosure _ hW)⟩

/-- A full triangulated subcategory `P` is contained in the kernel of any additive localization
of `C` at `P.trW`: the rotation of the contractible triangle of `X` in `P` is a distinguished
triangle `X ⟶ 0 ⟶ X⟦1⟧` whose cone lies in `P`. -/
private lemma le_kernel (P : ObjectProperty C) [P.IsTriangulated] (L : C ⥤ D) [Preadditive D]
    [L.Additive] [L.IsLocalization P.trW] : P ≤ L.kernel := by
  intro X hX
  have h : P.trW (0 : X ⟶ 0) :=
    ObjectProperty.trW.mk P (rot_of_distTriang _ (contractible_distinguished X))
      (IsStableUnderShiftBy.le_shift (a := (1 : ℤ)) X hX)
  have := Localization.inverts L P.trW _ h
  exact (L.map_isZero (isZero_zero C)).of_iso (asIso (L.map (0 : X ⟶ (0 : C))))

end

namespace CategoryTheory.ObjectProperty

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

/-- Let `C` be a triangulated category, let `P` be a full triangulated subcategory of `C` and let
`L : C ⥤ D` be a localization of `C` at the class `P.trW` of morphisms whose cone lies in `P`, i.e.
a quotient functor `C ⥤ C/P` ([Stacks, Tag 05RI]). Then an object `Z` of `C` lies in the kernel of
`L` if and only if there is an object `Z'` such that `Z ⊞ Z'` is isomorphic to an object of `P`;
and the kernel of `L` is the smallest strictly full saturated ([Stacks, Tag 05RB]) triangulated
subcategory of `C` containing `P`. -/
@[stacks 05RK]
theorem kernel_iff_exists_isoClosure_biprod_and_isLeast_kernel
    (P : ObjectProperty C) [P.IsTriangulated] (L : C ⥤ D) [L.IsLocalization P.trW] :
    (∀ Z : C, L.kernel Z ↔ ∃ Z' : C, P.isoClosure (Z ⊞ Z')) ∧
      IsLeast {P' : ObjectProperty C | P'.IsClosedUnderIsomorphisms ∧ P'.IsTriangulated ∧
        P'.IsSaturated ∧ P ≤ P'} L.kernel := by
  obtain ⟨htri, hsat⟩ := Functor.isTriangulated_and_isSaturated_kernel P.trW.Q
  have hP : P ≤ P.trW.Q.kernel := le_kernel P P.trW.Q
  have hker : L.kernel = P.trW.Q.kernel := kernel_eq_of_isLocalization P.trW L P.trW.Q
  have := isClosedUnderIsomorphisms_kernel L
  have htriL : L.kernel.IsTriangulated := by rw [hker]; exact htri
  have hsatL : L.kernel.IsSaturated := by rw [hker]; exact hsat
  have hle : P ≤ L.kernel := by rw [hker]; exact hP
  have key : ∀ (P' : ObjectProperty C) [P'.IsClosedUnderIsomorphisms] [P'.IsSaturated],
      P ≤ P' → ∀ Z : C, (∃ Z' : C, P.isoClosure (Z ⊞ Z')) → P' Z :=
    fun P' _ _ hP' Z ⟨_, hZ'⟩ => P'.isoClosure_eq_self.le _
      (IsSaturated.isoClosure_of_biprod_left (monotone_isoClosure hP' _ hZ'))
  have hiff : ∀ Z : C, L.kernel Z ↔ ∃ Z' : C, P.isoClosure (Z ⊞ Z') :=
    fun Z ↦ ⟨fun hZ ↦ exists_isoClosure_biprod P L hZ, key _ hle Z⟩
  refine ⟨hiff, ⟨⟨inferInstance, htriL, hsatL, hle⟩, ?_⟩⟩
  intro P' hP'
  obtain ⟨h₁, -, h₃, h₄⟩ := hP'
  exact fun Z hZ ↦ key P' h₄ Z ((hiff Z).1 hZ)

end CategoryTheory.ObjectProperty

end QuotientKernel

/-! ### The correspondence between multiplicative systems and thick subcategories -/

section Correspondence

open CategoryTheory Limits Pretriangulated MorphismProperty

section

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- **[Stacks, Tag 05QR] in the localized category.** For an exact functor `L` of
pre-triangulated categories, a morphism `f` of the source has its cone in the kernel of `L`
exactly when `L f` is an isomorphism. -/
private theorem trW_kernel_iff_isIso_map (L : C ⥤ D) [L.CommShift ℤ]
    [L.IsTriangulated] {X Y : C} (f : X ⟶ Y) : L.kernel.trW f ↔ IsIso (L.map f) := by
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  exact (ObjectProperty.trW_iff_of_distinguished L.kernel (Triangle.mk f g h) hT).trans
    ((Triangle.isZero₃_iff_isIso₁ (L.mapTriangle.obj (Triangle.mk f g h))
      (L.map_distinguished _ hT)).trans (by rfl))

end

section

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The class of morphisms whose cone is killed by a localization `L` of `C` at a
multiplicative system `S` compatible with the triangulated structure is the saturation
`Ŝ = S.invertedClosure` of `S`, i.e. the class of morphisms inverted by `L`. -/
private theorem trW_kernel_eq_invertedClosure (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] [S.IsCompatibleWithTriangulation] (L : C ⥤ D)
    [L.IsLocalization S] : L.kernel.trW = S.invertedClosure := by
  rw [kernel_eq_of_isLocalization S L S.Q]
  ext X Y f
  rw [trW_kernel_iff_isIso_map S.Q f]
  rfl

end

namespace CategoryTheory.ObjectProperty

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

/-- Let `C` be a triangulated category. Passing from a multiplicative system `S` compatible with
the triangulated structure to the kernel `B(S)` of a localization of `C` at `S`, and from a full
triangulated subcategory `P` to the class `S(P) = P.trW` of morphisms whose cone lies in `P`, one
has:

* `S(B(S))` is the *saturation* of `S`: the smallest saturated multiplicative system
  ([Stacks, Tag 05Q8]) of `C` containing `S`;
* if `P` is a strictly full saturated ([Stacks, Tag 05RB]) triangulated subcategory, then
  `B(S(P)) = P`.

Together with [Stacks, Tag 05RK] — which says that `B(S(P))` is in general the smallest strictly
full saturated triangulated subcategory containing `P` — this says that the two constructions are
mutually inverse, order preserving bijections between the saturated multiplicative systems of `C`
compatible with the triangulated structure and the strictly full saturated triangulated
subcategories of `C`. -/
@[stacks 05RL]
theorem isLeast_trW_kernel_and_kernel_eq_self :
    (∀ (S : MorphismProperty C) [S.HasLeftCalculusOfFractions]
        [S.HasRightCalculusOfFractions] [S.IsCompatibleWithTriangulation]
        (L : C ⥤ D) [L.IsLocalization S],
      IsLeast {S' : MorphismProperty C | S'.IsSaturated ∧ S ≤ S'} L.kernel.trW) ∧
    (∀ (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] [P.IsSaturated]
        (L : C ⥤ D) [L.IsLocalization P.trW],
      L.kernel = P) := by
  refine ⟨fun S _ _ _ L _ ↦ ?_, fun P _ _ _ L _ ↦ ?_⟩
  · rw [trW_kernel_eq_invertedClosure S L]
    exact ⟨⟨MorphismProperty.isSaturated_invertedClosure S,
        MorphismProperty.le_invertedClosure S⟩,
      fun S' hS' ↦ MorphismProperty.invertedClosure_le_of_isSaturated S S' hS'.1 hS'.2⟩
  · obtain ⟨-, hmem, hlb⟩ :=
      kernel_iff_exists_isoClosure_biprod_and_isLeast_kernel P L
    exact le_antisymm (hlb ⟨inferInstance, inferInstance, inferInstance, le_rfl⟩) hmem.2.2.2

end CategoryTheory.ObjectProperty

end Correspondence

/-! ### The quasi-isomorphisms of a homological functor -/

section Quasi

open CategoryTheory Limits Pretriangulated ObjectProperty

section

variable {C : Type u} {A : Type u'} {D : Type u''} [Category.{v} C] [Category.{v'} A]
  [Category.{v''} D]

/-- **The universal property of a localization**, in the form the factorizations take: a
functor inverting a class of morphisms `W` factors through any localization of `C` at `W`. Only
the existence of the factorization is recorded, since it is unique up to a canonical
isomorphism (`Localization.liftNatIso`). -/
private theorem exists_lift_of_isInvertedBy {W : MorphismProperty C} {F : C ⥤ A}
    (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] :
    ∃ F' : D ⥤ A, Nonempty (L ⋙ F' ≅ F) :=
  ⟨Localization.lift F hF L, ⟨Localization.fac F hF L⟩⟩

end

section

variable {C : Type u} {A : Type u'} [Category.{v} C] [Category.{v'} A] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Abelian A]

/-- **The long exact cohomology sequence criterion.** A morphism `f` of `C` has its cone in the
kernel of a homological functor `H` if and only if `Hⁱ(f) = H (f⟦i⟧')` is an isomorphism for
every `i : ℤ`. This is `Functor.mem_homologicalKernel_trW_iff` for the tautological shift
sequence on `H`, so no shift sequence has to be assumed on `H`. -/
@[sga "4½ Etat_0 2.4.1" "more general", sga "6 I 1.4.2" "partial"]
private theorem homologicalKernel_trW_iff_isIso_map (H : C ⥤ A) [H.IsHomological] {X Y : C}
    (f : X ⟶ Y) : H.homologicalKernel.trW f ↔ ∀ i : ℤ, IsIso (H.map (f⟦i⟧')) := by
  let _ : H.ShiftSequence ℤ := Functor.ShiftSequence.tautological H ℤ
  rw [H.mem_homologicalKernel_trW_iff]
  rfl

/-- Each `Hⁱ = shiftFunctor C i ⋙ H` inverts the morphisms whose cone lies in `Ker(H)`. -/
private theorem isInvertedBy_shift_of_homologicalKernel_trW (H : C ⥤ A) [H.IsHomological]
    (i : ℤ) : H.homologicalKernel.trW.IsInvertedBy (shiftFunctor C i ⋙ H) :=
  fun _ _ f hf => ((homologicalKernel_trW_iff_isIso_map H f).1 hf) i

/-- `H = H⁰` itself inverts the morphisms whose cone lies in `Ker(H)`. -/
private theorem isInvertedBy_of_homologicalKernel_trW (H : C ⥤ A) [H.IsHomological] :
    H.homologicalKernel.trW.IsInvertedBy H :=
  (MorphismProperty.IsInvertedBy.iff_of_iso _
    (Functor.isoWhiskerRight (shiftFunctorZero C ℤ) H ≪≫ H.leftUnitor)).1
      (isInvertedBy_shift_of_homologicalKernel_trW H 0)

/-- **The multiplicative system of `Ker(H)` is saturated**: the class of morphisms whose cone
lies in `Ker(H)` is, by the membership criterion, the class of morphisms `f` with all `Hⁱ(f)`
isomorphisms, which is a saturated multiplicative system by [Stacks, Tag 05R5]. -/
private theorem isSaturated_homologicalKernel_trW (H : C ⥤ A) [H.IsHomological] :
    H.homologicalKernel.trW.IsSaturated :=
  (CategoryTheory.Functor.isSaturated_and_isCompatibleWithTriangulation H
    H.homologicalKernel.trW fun _ _ f => homologicalKernel_trW_iff_isIso_map H f).1

end

namespace CategoryTheory.Functor

variable {C : Type u} {A : Type u'} {D : Type u''} [Category.{v} C] [Category.{v'} A]
  [Category.{v''} D] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [CategoryTheory.IsTriangulated C]
  [Abelian A]

/-- Let `H : C ⥤ A` be a homological functor from a triangulated category to an abelian category,
write `Hⁱ = H(-⟦i⟧)`, and let `L : C ⥤ D` be a localization of `C` at the class of morphisms whose
cone lies in the kernel of `H`. Then:

* `Ker(H)` is a strictly full saturated ([Stacks, Tag 05RB]) triangulated subcategory of `C`;
* the multiplicative system attached to it by [Stacks, Tag 05RL] is saturated ([Stacks, Tag 05Q8]),
  compatible with the triangulated structure, and is the class
  `S = {f ∣ Hⁱ(f) is an isomorphism for all i ∈ ℤ}`;
* `H` factors through `L`, and so does every `Hⁱ`. -/
@[stacks 05RM, sga "4½ Etat_0 2.4.1", sga "4½ Etat_0 3.1.6" "factors through quotient"]
theorem isSaturated_homologicalKernel_and_mem_trW_iff_and_exists_lift
    (H : C ⥤ A) [H.IsHomological] (L : C ⥤ D)
    [L.IsLocalization H.homologicalKernel.trW] :
    (H.homologicalKernel.IsClosedUnderIsomorphisms ∧ H.homologicalKernel.IsTriangulated ∧
        H.homologicalKernel.IsSaturated) ∧
      (H.homologicalKernel.trW.IsSaturated ∧
          H.homologicalKernel.trW.IsCompatibleWithTriangulation ∧
          ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
            H.homologicalKernel.trW f ↔ ∀ i : ℤ, IsIso (H.map (f⟦i⟧'))) ∧
      (∃ H' : D ⥤ A, Nonempty (L ⋙ H' ≅ H)) ∧
      ∀ i : ℤ, ∃ H' : D ⥤ A, Nonempty (L ⋙ H' ≅ shiftFunctor C i ⋙ H) :=
  have := isStableUnderRetracts_homologicalKernel H
  ⟨⟨inferInstance, inferInstance, IsSaturated.of_isStableUnderRetracts _⟩,
    ⟨isSaturated_homologicalKernel_trW H, inferInstance,
      fun _ _ f => homologicalKernel_trW_iff_isIso_map H f⟩,
    exists_lift_of_isInvertedBy (isInvertedBy_of_homologicalKernel_trW H) L,
    fun i => exists_lift_of_isInvertedBy (isInvertedBy_shift_of_homologicalKernel_trW H i) L⟩

end CategoryTheory.Functor

end Quasi

end

section

@[expose] public section


open CategoryTheory CategoryTheory.Triangulated CategoryTheory.Pretriangulated
  CategoryTheory.Limits

namespace StacksBoundedSubcategories

variable {D A : Type*} [Category D] [Category A] [HasShift D ℤ]

/-- `H(X[n]) = 0`: the value of `H` on the `n`-fold shift of `X` is a zero object. -/
def vanishesAt (H : D ⥤ A) (X : D) (n : ℤ) : Prop :=
  IsZero (H.obj ((shiftFunctor D n).obj X))

/-- `D_H^+`: the objects `X` with `H(X[n]) = 0` for all `n ≪ 0`. -/
@[sga "4 Vbis 2.4.1"]
def boundedBelow (H : D ⥤ A) : ObjectProperty D :=
  fun X => ∃ N : ℤ, ∀ n : ℤ, n ≤ N → vanishesAt H X n

/-- `D_H^-`: the objects `X` with `H(X[n]) = 0` for all `n ≫ 0`. -/
@[sga "4½ Etat_0 1.2.3" "more general"]
def boundedAbove (H : D ⥤ A) : ObjectProperty D :=
  fun X => ∃ N : ℤ, ∀ n : ℤ, N ≤ n → vanishesAt H X n

/-- `D_H^b`: the objects `X` with `H(X[n]) = 0` for all `|n| ≫ 0`. -/
@[sga "4½ Etat_0 1.2.3" "more general", sga "6 I 1.1.5" "more general"]
def bounded (H : D ⥤ A) : ObjectProperty D :=
  fun X => ∃ N : ℤ, ∀ n : ℤ, N ≤ |n| → vanishesAt H X n

/-- `vanishesAt` is closed under isomorphism in the object. -/
theorem vanishesAt_of_iso (H : D ⥤ A) {X Y : D} (e : X ≅ Y) {n : ℤ}
    (h : vanishesAt H X n) : vanishesAt H Y n :=
  h.of_iso (H.mapIso ((shiftFunctor D n).mapIso e.symm))

/-- A property of objects defined by `vanishesAt` for `n` in a range depending on `N` is closed
under isomorphisms. -/
private theorem isClosedUnderIsomorphisms_of_exists_vanishesAt (H : D ⥤ A) (R : ℤ → ℤ → Prop)
    (P : ObjectProperty D) (hP : ∀ X, P X ↔ ∃ N, ∀ n, R N n → vanishesAt H X n) :
    P.IsClosedUnderIsomorphisms where
  of_iso e h := (hP _).2 (((hP _).1 h).imp fun _ hN n hn => vanishesAt_of_iso H e (hN n hn))

/-- `vanishesAt` in terms of the shifted homology functor `H.shift n`. -/
theorem vanishesAt_iff_shift (H : D ⥤ A) [H.ShiftSequence ℤ] (n : ℤ) (X : D) :
    vanishesAt H X n ↔ IsZero ((H.shift n).obj X) := by
  have e : (H.shift n).obj X ≅ H.obj ((shiftFunctor D n).obj X) :=
    (H.shiftIso n 0 n (by ring)).symm.app X ≪≫ (Functor.ShiftSequence.isoZero (F := H)).app _
  exact ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/-- `H((X[a])[n]) = 0` iff `H(X[a+n]) = 0`. -/
theorem vanishesAt_shift (H : D ⥤ A) (X : D) (a n : ℤ) :
    vanishesAt H ((shiftFunctor D a).obj X) n ↔ vanishesAt H X (a + n) := by
  constructor
  · intro h
    exact h.of_iso (H.mapIso ((shiftFunctorAdd' D a n (a + n) rfl).app X))
  · intro h
    exact h.of_iso (H.mapIso ((shiftFunctorAdd' D a n (a + n) rfl).symm.app X))

variable [HasZeroMorphisms A] in
/-- If `X` is a retract of `W` (`i ≫ r = 𝟙 X`) and `H(W[n]) = 0`, then `H(X[n]) = 0`. -/
theorem vanishesAt_of_retract (H : D ⥤ A) {X W : D} (i : X ⟶ W) (r : W ⟶ X)
    (hir : i ≫ r = 𝟙 X) {n : ℤ} (h : vanishesAt H W n) : vanishesAt H X n := by
  rw [vanishesAt, IsZero.iff_id_eq_zero]
  have hsh : (shiftFunctor D n).map i ≫ (shiftFunctor D n).map r = 𝟙 _ := by
    rw [← (shiftFunctor D n).map_comp, hir, (shiftFunctor D n).map_id]
  rw [← H.map_id, ← hsh, H.map_comp, h.eq_zero_of_tgt (H.map _)]
  simp

/-- An object is `H`-bounded if and only if it is both `H`-bounded below and `H`-bounded
above. -/
theorem bounded_iff (H : D ⥤ A) (X : D) :
    bounded H X ↔ boundedBelow H X ∧ boundedAbove H X := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨⟨-|N|, fun n hn => hN n ?_⟩, ⟨|N|, fun n hn => hN n ?_⟩⟩
    · linarith [le_abs_self N, neg_le_abs n]
    · linarith [le_abs_self N, le_abs_self n]
  · rintro ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩
    refine ⟨max |N₁| |N₂|, fun n hn => ?_⟩
    rcases le_or_gt 0 n with h | h
    · exact hN₂ n (by linarith [abs_of_nonneg h, le_abs_self N₂, le_max_right |N₁| |N₂|])
    · exact hN₁ n (by linarith [abs_of_neg h, neg_abs_le N₁, le_max_left |N₁| |N₂|])

variable [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] [Abelian A]

/-- A property of objects is saturated if whenever a biproduct `X ⊞ Y` has the property, so do
both `X` and `Y`. -/
def IsSaturated (P : ObjectProperty D) : Prop :=
  ∀ (X Y : D), P (X ⊞ Y) → P X ∧ P Y

/-- For a distinguished triangle, if `H(T.obj₁[n]) = 0` and `H(T.obj₃[n]) = 0`,
then `H(T.obj₂[n]) = 0`. -/
theorem vanishesAt_obj₂ (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
    (T : Triangle D) (hT : T ∈ distinguishedTriangles) (n : ℤ)
    (h1 : vanishesAt H T.obj₁ n) (h3 : vanishesAt H T.obj₃ n) :
    vanishesAt H T.obj₂ n := by
  have e2 : (H.shift n).obj T.obj₂ ≅ H.obj ((shiftFunctor D n).obj T.obj₂) :=
    (H.shiftIso n 0 n (by ring)).symm.app _ ≪≫ (Functor.ShiftSequence.isoZero (F := H)).app _
  have hz1 := (vanishesAt_iff_shift H n T.obj₁).1 h1
  have hz3 := (vanishesAt_iff_shift H n T.obj₃).1 h3
  have hexact := H.homologySequence_exact₂ T hT n
  have hf : (H.shift n).map T.mor₁ = 0 := hz1.eq_of_src _ _
  have hg : (H.shift n).map T.mor₂ = 0 := hz3.eq_of_tgt _ _
  exact (hexact.isZero_X₂ hf hg).of_iso e2.symm

/-- If `X` is a zero object, then `H(X[n]) = 0`. -/
theorem vanishesAt_of_isZero (H : D ⥤ A) [H.IsHomological] {X : D} (h : IsZero X)
    (n : ℤ) : vanishesAt H X n :=
  have : H.PreservesZeroMorphisms := Functor.IsHomological.toPreservesZeroMorphisms (F := H)
  Functor.map_isZero H (Functor.map_isZero (shiftFunctor D n) h)

/-- A property of objects defined by `vanishesAt` for `n` in a range depending on `N` is a
pre-triangulated subcategory if the ranges are stable under shifts and under intersections. -/
private theorem isTriangulated_of_exists_vanishesAt (H : D ⥤ A) [H.IsHomological]
    [H.ShiftSequence ℤ] (R : ℤ → ℤ → Prop) (P : ObjectProperty D)
    (hP : ∀ X, P X ↔ ∃ N, ∀ n, R N n → vanishesAt H X n)
    (hshift : ∀ a N, ∃ N', ∀ n, R N' n → R N (a + n))
    (hinter : ∀ N₁ N₃, ∃ N, ∀ n, R N n → R N₁ n ∧ R N₃ n) : P.IsTriangulated := by
  have hcz : P.ContainsZero :=
    ⟨_, isZero_zero D, (hP _).2 ⟨0, fun n _ => vanishesAt_of_isZero H (isZero_zero D) n⟩⟩
  have hsh : P.IsStableUnderShift ℤ := by
    refine ⟨fun a => ⟨?_⟩⟩
    rw [ObjectProperty.le_def]
    intro X hX
    obtain ⟨N, hN⟩ := (hP X).1 hX
    obtain ⟨N', hN'⟩ := hshift a N
    rw [ObjectProperty.prop_shift_iff, hP]
    refine ⟨N', fun n hn => ?_⟩
    rw [vanishesAt_shift]
    exact hN _ (hN' n hn)
  have hc2 : P.IsTriangulatedClosed₂ := by
    refine ⟨fun T hT h1 h3 => ?_⟩
    apply P.le_isoClosure
    obtain ⟨N₁, hN₁⟩ := (hP _).1 h1
    obtain ⟨N₃, hN₃⟩ := (hP _).1 h3
    obtain ⟨N, hN⟩ := hinter N₁ N₃
    exact (hP _).2 ⟨N, fun n hn =>
      vanishesAt_obj₂ H T hT n (hN₁ n (hN n hn).1) (hN₃ n (hN n hn).2)⟩
  exact ⟨⟩

/-- A property of objects that is stable under retracts is saturated. -/
private theorem isSaturated_of_retract (P : ObjectProperty D)
    (hP : ∀ {X W : D} (i : X ⟶ W) (r : W ⟶ X), i ≫ r = 𝟙 X → P W → P X) : IsSaturated P :=
  fun _ _ h =>
    ⟨hP biprod.inl biprod.fst biprod.inl_fst h, hP biprod.inr biprod.snd biprod.inr_snd h⟩

/-- The property `D_H^+` of being `H`-bounded below is closed under isomorphisms. -/
@[stacks 05RE "D_H^+ strictly full"]
theorem boundedBelow_strictlyFull (H : D ⥤ A) [H.IsHomological] :
    (boundedBelow H).IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_of_exists_vanishesAt H _ _ fun _ => Iff.rfl

/-- `D_H^+` is a pre-triangulated subcategory: it contains a zero object, is stable under every
shift `[n]`, and is closed under cones of distinguished triangles with two vertices in `D_H^+`. -/
@[stacks 05RE "D_H^+ pre-triangulated",
  sga "4½ Etat_0 1.2.3" "more general",
  sga "6 I 1.1.5" "more general"]
theorem boundedBelow_isTriangulated (H : D ⥤ A) [H.IsHomological]
    [H.ShiftSequence ℤ] :
    (boundedBelow H).IsTriangulated :=
  isTriangulated_of_exists_vanishesAt H (fun N n => n ≤ N) _ (fun _ => Iff.rfl)
    (fun a N => ⟨N - a, fun n hn => by omega⟩)
    (fun N₁ N₃ => ⟨min N₁ N₃, fun n hn => by omega⟩)

/-- `D_H^+` is saturated: if `X ⊞ Y` is bounded below then so are `X` and `Y`, each being a retract
of the biproduct. -/
@[stacks 05RE "D_H^+ saturated"]
theorem boundedBelow_isSaturated (H : D ⥤ A) [H.IsHomological] :
    IsSaturated (boundedBelow H) :=
  isSaturated_of_retract _ fun i r hir ⟨N, hN⟩ =>
    ⟨N, fun n hn => vanishesAt_of_retract H i r hir (hN n hn)⟩

/-- The property `D_H^-` of being `H`-bounded above is closed under isomorphisms. -/
@[stacks 05RE "D_H^- strictly full"]
theorem boundedAbove_strictlyFull (H : D ⥤ A) [H.IsHomological] :
    (boundedAbove H).IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_of_exists_vanishesAt H _ _ fun _ => Iff.rfl

/-- `D_H^-` is a pre-triangulated subcategory: it contains a zero object, is stable under every
shift `[n]`, and is closed under cones of distinguished triangles with two vertices in `D_H^-`. -/
@[stacks 05RE "D_H^- pre-triangulated",
  sga "4½ Etat_0 1.2.3" "more general",
  sga "6 I 1.1.5" "more general"]
theorem boundedAbove_isTriangulated (H : D ⥤ A) [H.IsHomological]
    [H.ShiftSequence ℤ] :
    (boundedAbove H).IsTriangulated :=
  isTriangulated_of_exists_vanishesAt H (fun N n => N ≤ n) _ (fun _ => Iff.rfl)
    (fun a N => ⟨N - a, fun n hn => by omega⟩)
    (fun N₁ N₃ => ⟨max N₁ N₃, fun n hn => by omega⟩)

/-- `D_H^-` is saturated: if `X ⊞ Y` is bounded above then so are `X` and `Y`, each being a retract
of the biproduct. -/
@[stacks 05RE "D_H^- saturated"]
theorem boundedAbove_isSaturated (H : D ⥤ A) [H.IsHomological] :
    IsSaturated (boundedAbove H) :=
  isSaturated_of_retract _ fun i r hir ⟨N, hN⟩ =>
    ⟨N, fun n hn => vanishesAt_of_retract H i r hir (hN n hn)⟩

/-- The property `D_H^b` of being `H`-bounded is closed under isomorphisms. -/
@[stacks 05RE "D_H^b strictly full"]
theorem bounded_strictlyFull (H : D ⥤ A) [H.IsHomological] :
    (bounded H).IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_of_exists_vanishesAt H _ _ fun _ => Iff.rfl

/-- `D_H^b` is a pre-triangulated subcategory: it contains a zero object, is stable under every
shift `[n]`, and is closed under cones of distinguished triangles with two vertices in `D_H^b`. -/
@[stacks 05RE "D_H^b pre-triangulated",
  sga "4½ Etat_0 1.2.3" "more general",
  sga "6 I 1.1.5" "more general"]
theorem bounded_isTriangulated (H : D ⥤ A) [H.IsHomological]
    [H.ShiftSequence ℤ] :
    (bounded H).IsTriangulated :=
  isTriangulated_of_exists_vanishesAt H (fun N n => N ≤ |n|) _ (fun _ => Iff.rfl)
    (fun a N => ⟨N + |a|, fun n hn => by
      rcases abs_cases a with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases n with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases abs_cases (a + n) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega⟩)
    (fun N₁ N₃ => ⟨max N₁ N₃, fun n hn => by omega⟩)

/-- `D_H^b` is saturated: if `X ⊞ Y` is bounded then so are `X` and `Y`, each being a retract of
the biproduct. -/
@[stacks 05RE "D_H^b saturated"]
theorem bounded_isSaturated (H : D ⥤ A) [H.IsHomological] :
    IsSaturated (bounded H) :=
  isSaturated_of_retract _ fun i r hir ⟨N, hN⟩ =>
    ⟨N, fun n hn => vanishesAt_of_retract H i r hir (hN n hn)⟩

noncomputable example (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
    (hP : (boundedBelow H).IsTriangulated) :
    Pretriangulated (boundedBelow H).FullSubcategory :=
  let := hP; inferInstance

noncomputable example (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]
    [IsTriangulated D] (hP : (boundedBelow H).IsTriangulated) :
    IsTriangulated (boundedBelow H).FullSubcategory :=
  let := hP; inferInstance

end StacksBoundedSubcategories

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false


open CategoryTheory CategoryTheory.Triangulated CategoryTheory.Pretriangulated Limits

namespace VerdierQuotientUniversalProperty

/-- The factorization `Localization.lift F hinv W.Q` of `F` through a localization is unique up to
a unique natural isomorphism compatible with the factorization isomorphisms. -/
private theorem existsUnique_iso_lift {C E : Type*} [Category C] [Category E]
    (W : MorphismProperty C) (F : C ⥤ E) (hinv : W.IsInvertedBy F) (G : W.Localization ⥤ E)
    (α : W.Q ⋙ G ≅ F) :
    ∃! e : G ≅ Localization.lift F hinv W.Q,
      Functor.whiskerLeft W.Q e.hom ≫ (Localization.fac F hinv W.Q).hom = α.hom := by
  let : Localization.Lifting W.Q W F (Localization.lift F hinv W.Q) :=
    ⟨Localization.fac F hinv W.Q⟩
  let : Localization.Lifting W.Q W F G := ⟨α⟩
  have hcomp : Functor.whiskerLeft W.Q (Localization.liftNatIso W.Q W F F G
      (Localization.lift F hinv W.Q) (Iso.refl F)).hom ≫
        (Localization.fac F hinv W.Q).hom = α.hom := by
    ext X
    have key := Localization.liftNatTrans_app W.Q W F F G
      (Localization.lift F hinv W.Q) (Iso.refl F).hom X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    change (Localization.liftNatTrans W.Q W F F G
      (Localization.lift F hinv W.Q) (Iso.refl F).hom).app (W.Q.obj X)
      ≫ (Localization.fac F hinv W.Q).hom.app X = α.hom.app X
    rw [key]
    have hL1 : Localization.Lifting.iso W.Q W F G = α := rfl
    have hL2 : Localization.Lifting.iso W.Q W F
        (Localization.lift F hinv W.Q) = Localization.fac F hinv W.Q := rfl
    rw [hL1, hL2]
    simp
  refine ⟨_, hcomp, fun e' he' => Iso.ext ?_⟩
  apply Localization.natTrans_ext W.Q W
  intro X
  rw [← cancel_mono ((Localization.fac F hinv W.Q).hom.app X)]
  exact (NatTrans.congr_app he' X).trans (NatTrans.congr_app hcomp X).symm

/-- **Universal property of the Verdier quotient for homological functors**.

Let `C` be a triangulated category, `P` a full triangulated subcategory (an
`ObjectProperty` with `P.IsTriangulated`), and `Q = P.trW.Q : C ⥤ C / P` the Verdier
quotient functor. Let `A` be abelian and `H : C ⥤ A` a homological functor whose
homological kernel contains `P` (this is the hypothesis `B ⊆ Ker(H)`). Then:

* **Existence + structure**: there is a functor `H' : C / P ⥤ A` together with a natural
  isomorphism `fac : Q ⋙ H' ≅ H` (the factorization `H = H' ∘ Q`), and `H'` is again
  homological.
* **Uniqueness (up to unique natural isomorphism)**: for any functor `G : C / P ⥤ A`
  equipped with a natural isomorphism `α : Q ⋙ G ≅ H`, there is a *unique* natural
  isomorphism `e : G ≅ H'` compatible with the factorization isomorphisms, i.e. such that
  `whiskerLeft Q e.hom ≫ fac.hom = α.hom`. -/
@[stacks 05RJ "(1)", sga "4½ Etat_0 2.4.1" "more general"]
theorem homological_universal_property
    {C A : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [Category A] [Abelian A]
    (P : ObjectProperty C) [P.IsTriangulated]
    (H : C ⥤ A) [H.IsHomological]
    (hker : P ≤ H.homologicalKernel) :
    ∃ (H' : P.trW.Localization ⥤ A) (fac : P.trW.Q ⋙ H' ≅ H),
      H'.IsHomological ∧
      ∀ (G : P.trW.Localization ⥤ A) (α : P.trW.Q ⋙ G ≅ H),
        ∃! e : G ≅ H', Functor.whiskerLeft P.trW.Q e.hom ≫ fac.hom = α.hom := by
  have hinv : P.trW.IsInvertedBy H := by
    intro X Y f hf
    rw [P.trW_iff] at hf
    obtain ⟨Z, g, h, dt, hZ⟩ := hf
    have hz : ∀ n : ℤ, IsZero (H.obj (Z⟦n⟧)) := hker Z hZ
    set T : Triangle C := Triangle.mk f g h with hT
    have hepi : Epi (H.map f) := by
      have hex := H.map_distinguished_exact T dt
      refine hex.epi_f ?_
      change H.map g = 0
      exact ((hz 0).of_iso (H.mapIso ((shiftFunctorZero C ℤ).app Z).symm)).eq_of_tgt _ _
    have hmono : Mono (H.map f) := by
      have dt' : T.invRotate ∈ distinguishedTriangles := inv_rot_of_distTriang T dt
      have hex := H.map_distinguished_exact T.invRotate dt'
      refine hex.mono_g ?_
      change H.map T.invRotate.mor₁ = 0
      exact (hz (-1)).eq_of_src _ _
    exact isIso_of_mono_of_epi (H.map f)
  refine ⟨Localization.lift H hinv P.trW.Q, Localization.fac H hinv P.trW.Q, ?_, ?_⟩
  · have : P.trW.Q.mapArrow.EssSurj := Localization.essSurj_mapArrow P.trW.Q P.trW
    exact Functor.isHomological_of_localization P.trW.Q
      (Localization.lift H hinv P.trW.Q) H (Localization.fac H hinv P.trW.Q)
  · exact existsUnique_iso_lift P.trW H hinv

set_option backward.isDefEq.respectTransparency true in
/-- A functor out of `P.trW.Localization` that is triangulated for the pretriangulated structure
`Triangulated.Localization.pretriangulated` is triangulated for the canonical one. -/
private theorem isTriangulated_bridge
    {C D' : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [Category D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
    [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
    (P : ObjectProperty C) [P.IsTriangulated]
    (L : P.trW.Localization ⥤ D') [csl : L.CommShift ℤ]
    (h : @Functor.IsTriangulated _ _ _ _ _ _ L csl _ _ _ _ _ _
      (Triangulated.Localization.pretriangulated P.trW.Q P.trW) _) :
    L.IsTriangulated := h

/-- **Universal property of the Verdier quotient for exact (triangulated) functors**.

Let `C` be a triangulated category, `P` a full triangulated subcategory, and
`Q = P.trW.Q : C ⥤ C / P` the Verdier quotient functor. Let `D'` be pretriangulated and
`F : C ⥤ D'` an exact (triangulated) functor: it is additive (`F.Additive`), commutes
with the shift (`F.CommShift ℤ`), and sends distinguished triangles to distinguished
triangles (`F.IsTriangulated`). Assume its kernel contains `P`, i.e. `F` sends every
object of `P` to a zero object (the hypothesis `B ⊆ Ker(F)`). Then:

* **Existence + structure**: there is a functor `F' : C / P ⥤ D'` equipped with a
  `CommShift ℤ` structure, a natural isomorphism `fac : Q ⋙ F' ≅ F` (the factorization
  `F = F' ∘ Q`) which commutes with the shift structures on both sides
  (`NatTrans.CommShift fac.hom ℤ`), and `F'` is again additive (`F'.Additive`) and
  exact/triangulated (`F'.IsTriangulated`).
* **Uniqueness (up to unique natural isomorphism)**: for any functor `G : C / P ⥤ D'`
  equipped with a natural isomorphism `α : Q ⋙ G ≅ F`, there is a *unique* natural
  isomorphism `e : G ≅ F'` compatible with the factorization isomorphisms, i.e. such that
  `whiskerLeft Q e.hom ≫ fac.hom = α.hom`. -/
@[stacks 05RJ "(2)",
  sga "4½ Etat_0 Problem1",
  sga "4½ Etat_0 2.2" "partial",
  sga "4½ Etat_0 2.3.2" "(A_S",
  sga "4½ Etat_0 2.3.3" "more general",
  sga "4½ Etat_0 4.2.3" "(b)",
  sga "4½ Etat_0 Problem2" "partial"]
theorem exact_universal_property
    {C D' : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [Category D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
    [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
    (P : ObjectProperty C) [P.IsTriangulated]
    (F : C ⥤ D') [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (hker : ∀ X, P X → IsZero (F.obj X)) :
    ∃ (F' : P.trW.Localization ⥤ D') (_ : F'.CommShift ℤ) (fac : P.trW.Q ⋙ F' ≅ F)
      (_ : NatTrans.CommShift fac.hom ℤ),
      F'.Additive ∧ F'.IsTriangulated ∧
      ∀ (G : P.trW.Localization ⥤ D') (α : P.trW.Q ⋙ G ≅ F),
        ∃! e : G ≅ F', Functor.whiskerLeft P.trW.Q e.hom ≫ fac.hom = α.hom := by
  have hinv : P.trW.IsInvertedBy F := by
    intro X Y f hf
    rw [P.trW_iff] at hf
    obtain ⟨Z, g, h, dt, hZ⟩ := hf
    have hZ0 : IsZero (F.obj Z) := hker Z hZ
    set T : Triangle C := Triangle.mk f g h with hT
    have dtF : F.mapTriangle.obj T ∈ distinguishedTriangles := F.map_distinguished T dt
    have h3 : IsZero (F.mapTriangle.obj T).obj₃ := hZ0
    exact (Triangle.isZero₃_iff_isIso₁ (F.mapTriangle.obj T) dtF).mp h3
  let hq : P.trW.Q.CommShift ℤ := MorphismProperty.commShift_Q P.trW ℤ
  have : P.trW.Q.Additive := Localization.functor_additive P.trW.Q P.trW
  have hess : P.trW.Q.mapArrow.EssSurj := Localization.essSurj_mapArrow P.trW.Q P.trW
  let lifting : Localization.Lifting P.trW.Q P.trW F (Localization.lift F hinv P.trW.Q) :=
    ⟨Localization.fac F hinv P.trW.Q⟩
  let hcs : (Localization.lift F hinv P.trW.Q).CommShift ℤ :=
    @Functor.commShiftOfLocalization C P.trW.Localization _ _ D' _ P.trW.Q P.trW _ ℤ _ _ F
      (Localization.lift F hinv P.trW.Q) lifting _ _ hq _
  have htri :=
    Triangulated.Localization.isTriangulated_functor P.trW.Q P.trW
  have hnat : NatTrans.CommShift
      (Localization.Lifting.iso P.trW.Q P.trW F (Localization.lift F hinv P.trW.Q)).hom ℤ :=
    @NatTrans.commShift_iso_hom_of_localization C P.trW.Localization _ _ D' _ P.trW.Q P.trW _ ℤ _ _
        F
      (Localization.lift F hinv P.trW.Q) lifting _ _ hq _
  refine ⟨Localization.lift F hinv P.trW.Q, hcs, Localization.fac F hinv P.trW.Q, hnat,
    ?_, ?_, ?_⟩
  · rw [Localization.functor_additive_iff P.trW.Q P.trW]
    exact Functor.additive_of_iso (Localization.fac F hinv P.trW.Q).symm
  · refine isTriangulated_bridge P (Localization.lift F hinv P.trW.Q) ?_
    exact @Functor.isTriangulated_of_precomp_iso C P.trW.Localization D' _ _ _ _ _ _
      P.trW.Q hq (Localization.lift F hinv P.trW.Q) hcs _ _ _ _ _ _ _ _ _ _
      (Triangulated.Localization.pretriangulated P.trW.Q P.trW) _ F
      (Localization.Lifting.iso P.trW.Q P.trW F (Localization.lift F hinv P.trW.Q)) _ _ htri hess
          hnat
  · exact existsUnique_iso_lift P.trW F hinv

end VerdierQuotientUniversalProperty

end

end
