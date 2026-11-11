module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Localization.Resolution
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Localization.Saturated.Closure

import StacksCore.Tactic.StacksAttribute

/-!
# Localization of a pre-triangulated category

Let `C` be a pre-triangulated category. To localize `C` at a class `W` of morphisms and land
again in a pre-triangulated category, `W` must be a multiplicative system compatible with the
triangulated structure: the axioms MS1, MS2, MS3 of a calculus of fractions, together with
MS5 (stability under the shift) and MS6 (a commuting square between two distinguished
triangles whose two given components lie in `W` is completed by a third component in `W`).
This file and the other parts of `StacksFrontier.CategoryTheory.Triangulated.Localization`
collect the results of that theory. This part treats the two standard sources of such a class,
the pre-triangulated structure the localization carries, and the exactness of a functor that
factors through it. The filtered index category attached to a distinguished triangle is in
`StacksFrontier.CategoryTheory.Triangulated.Localization.IndexCategory`, the comparison of the
localization of a subcategory with the localization of `C` in
`StacksFrontier.CategoryTheory.Triangulated.Localization.Resolutions`, and the Ore conditions
from MS6 and the objects killed by a localization functor in
`StacksFrontier.CategoryTheory.Triangulated.Localization.OreConditionsAndKernel`.

Two classes are shown to be saturated multiplicative systems compatible with the
triangulated structure. The first is the class of morphisms inverted by an exact functor
`F : C ⥤ D`; the second is the class of "quasi-isomorphisms" of a homological functor
`H : C ⥤ A` to an abelian category, the morphisms `f` with `Hⁱ(f)` invertible for every
`i : ℤ`. Both are handled through the class of morphisms whose cone lies in a triangulated
subcategory — the kernel of `F` in the first case, the kernel of `H` in the second — for
which MS1 and MS4 become statements about isomorphisms, while MS2 and MS3 are the calculus of
fractions that TR1 and TR2 produce. MS6 is TR3 in `C` followed, for the first class, by the
fact that a morphism of distinguished triangles of `D` with two invertible components has the
third invertible, and for the second by the five lemma applied to the long exact cohomology
sequences.

Given such a `W` and a localization functor `L : C ⥤ D`, the category `D` carries exactly one
pre-triangulated structure making `L` exact, the one whose distinguished triangles are the
triangles isomorphic to the image under `L` of a distinguished triangle of `C`. Existence is
Mathlib's `CategoryTheory.Triangulated.Localization.pretriangulated`; uniqueness is the
observation that a pre-triangulated structure making `L` exact has no choice of distinguished
triangles, since `L` is essentially surjective on arrows. A functor out of `C` inverting `W`
then factors through `L`, and the factorization is exact when the functor is, for the
commutation with the shift that the factorization induces on it.

## Main results

* `CategoryTheory.Functor.isSaturated_and_isCompatibleWithTriangulation_inverseImage_isomorphisms`:
  the class of morphisms inverted by an exact functor of pre-triangulated categories is a
  saturated multiplicative system compatible with the triangulated structure.
* `CategoryTheory.Functor.isSaturated_and_isCompatibleWithTriangulation`: the class of
  morphisms `f` with `Hⁱ(f)` an isomorphism for every `i : ℤ`, for a homological functor `H`,
  is a saturated multiplicative system compatible with the triangulated structure.
* `CategoryTheory.Triangulated.Localization.existsUnique_pretriangulated_and_isTriangulated`:
  `CategoryTheory.Triangulated.Localization.pretriangulated L W` is the unique
  pre-triangulated structure on the localization making the localization functor exact, and it
  is triangulated as soon as `C` is.
* `CategoryTheory.Functor.isTriangulated_of_localization`: a lift through the localization
  functor of an exact functor is exact, for the commutation with the shift that the lift
  inherits. The companion statement for a homological functor is Mathlib's
  `CategoryTheory.Functor.isHomological_of_localization`, which is registered against the same
  tag here rather than restated.

## Implementation notes

Throughout, a *multiplicative system* is a class satisfying both
`MorphismProperty.HasLeftCalculusOfFractions` and
`MorphismProperty.HasRightCalculusOfFractions` — each extends
`MorphismProperty.IsMultiplicative`, i.e. MS1, and adds one Ore and one cancellation
condition, so the two together are MS1, MS2 and MS3 — and a *saturated* multiplicative system
is `MorphismProperty.IsSaturated`, which bundles the two calculi with the cancellation axiom
MS4. Compatibility with the triangulated structure is
`MorphismProperty.IsCompatibleWithTriangulation`, which extends
`MorphismProperty.IsCompatibleWithShift ℤ` and so carries MS5 as well as MS6. Mathlib's MS5 asks
for stability under every shift `[n]`, `n : ℤ`, where Stacks asks only `f ∈ S ⇔ f[1] ∈ S`; for a
class with MS1 and MS6 the two agree (Remark 0H30,
`MorphismProperty.isCompatibleWithShift_iff_of_hasMS6`), and
`MorphismProperty.isCompatibleWithTriangulation_iff_shift_one_and_hasMS6` restates the definition
with Stacks' form of MS5. "Exact functor"
is `CategoryTheory.Functor.IsTriangulated`.

The ambient categories are only pre-triangulated wherever that suffices: none of the
arguments below uses the octahedron axiom TR4, which enters only as the hypothesis of the
last conjunct about the localization being triangulated. Mathlib's instances for
`ObjectProperty.trW` all assume `IsTriangulated`, so the two calculi of fractions are
restated here as `trW_hasLeftCalculusOfFractions` and `trW_hasRightCalculusOfFractions` over
a pre-triangulated category, with multiplicativity of `P.trW` as a hypothesis.

Where a class of morphisms is characterised by a display rather than named, it enters as an
arbitrary `S : MorphismProperty C` together with a hypothesis identifying its members, so
that the result applies verbatim to every spelling of that class. Likewise the localization
is never a chosen construction: the statements are about an arbitrary `L : C ⥤ D` with
`[L.IsLocalization W]`, which covers `W.Localization`, `W.Localization'` and every category
equivalent to them over `C`, so nothing has to be transported afterwards.

## References

* [Stacks, Tag 05R4](https://stacks.math.columbia.edu/tag/05R4),
  [Tag 05R5](https://stacks.math.columbia.edu/tag/05R5),
  [Tag 05R6](https://stacks.math.columbia.edu/tag/05R6),
  [Tag 05R7](https://stacks.math.columbia.edu/tag/05R7).
* Saturated multiplicative systems are [Stacks, Tag 05Q8], and the compatibility with the
  triangulated structure is [Stacks, Tag 05R2].
-/

@[expose] public section

universe v₁ v₂ v₃ v u₁ u₂ u₃ u

/-! ### Compatibility with the triangulated structure: MS5 and MS6 -/

add_to_stacks 05R2 "a multiplicative system compatible with the triangulated structure"
  CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation
add_to_stacks 05R2 "MS5, as stability under every shift `[n]`, `n : ℤ`; for a class with MS1 \
    and MS6 this is equivalent to Stacks' form `f ∈ S ⇔ f[1] ∈ S` by Remark 0H30, \
    `MorphismProperty.isCompatibleWithShift_iff_of_hasMS6`"
  CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation.toIsCompatibleWithShift
add_to_stacks 05R2 "MS6"
  CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation.compatible_with_triangulation

/-! ### The calculi of fractions of `P.trW` over a pre-triangulated category -/

section Shared

open CategoryTheory Limits Pretriangulated MorphismProperty

/-- A morphism which becomes an isomorphism after composing with a morphism on either side is
an isomorphism: it is a split epimorphism because `f ≫ g` is invertible, and a split
monomorphism because `g ≫ h` is. -/
private lemma isIso_of_isIso_comp_of_isIso_comp {C : Type u₁} [Category.{v₁} C] {X Y Z T : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (hfg : IsIso (f ≫ g)) (hgh : IsIso (g ≫ h)) :
    IsIso g := by
  have : IsSplitEpi g := ⟨⟨inv (f ≫ g) ≫ f, by rw [Category.assoc, IsIso.inv_hom_id]⟩⟩
  have : IsSplitMono g := ⟨⟨h ≫ inv (g ≫ h), by rw [← Category.assoc, IsIso.hom_inv_id]⟩⟩
  exact isIso_of_mono_of_isSplitEpi g

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The class of morphisms whose cone lies in a triangulated subcategory `P` has a left
calculus of fractions as soon as it is multiplicative; the ambient category need only be
pre-triangulated. -/
private lemma trW_hasLeftCalculusOfFractions (P : ObjectProperty C) [P.IsTriangulated]
    [P.trW.IsMultiplicative] : P.trW.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
    obtain ⟨Z, f, g, hT, mem⟩ := φ.hs
    obtain ⟨Y', s', f', mem'⟩ := distinguished_cocone_triangle₂ (g ≫ φ.f⟦(1 : ℤ)⟧')
    obtain ⟨b, ⟨hb₁, _⟩⟩ :=
      complete_distinguished_triangle_morphism₂ _ _ hT mem' φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.LeftFraction.mk b s' ⟨_, _, _, mem', mem⟩, hb₁.symm⟩
  ext := by
    rintro X' X Y f₁ f₂ s ⟨Z, g, h, hT, mem⟩ hf₁
    have hf₂ : s ≫ (f₁ - f₂) = 0 := by rw [Preadditive.comp_sub, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ _ hT _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle q
    refine ⟨Y', r, ⟨_, _, _, rot_of_distTriang _ mem', P.le_shift _ _ mem⟩, ?_⟩
    have eq := comp_distTriang_mor_zero₁₂ _ mem'
    dsimp at eq
    rw [← sub_eq_zero, ← Preadditive.sub_comp, hq, Category.assoc, eq, comp_zero]

/-- The class of morphisms whose cone lies in a triangulated subcategory `P` has a right
calculus of fractions as soon as it is multiplicative; the ambient category need only be
pre-triangulated. -/
private lemma trW_hasRightCalculusOfFractions (P : ObjectProperty C) [P.IsTriangulated]
    [P.trW.IsMultiplicative] : P.trW.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ := by
    obtain ⟨Z, f, g, hT, mem⟩ := φ.hs
    obtain ⟨X', f', h', mem'⟩ := distinguished_cocone_triangle₁ (φ.f ≫ f)
    obtain ⟨a, ⟨ha₁, _⟩⟩ :=
      complete_distinguished_triangle_morphism₁ _ _ mem' hT φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.RightFraction.mk f' ⟨_, _, _, mem', mem⟩ a, ha₁⟩
  ext Y Z Z' f₁ f₂ s hs hf₁ := by
    rw [P.trW_iff'] at hs
    obtain ⟨Z, g, h, hT, mem⟩ := hs
    have hf₂ : (f₁ - f₂) ≫ s = 0 := by rw [Preadditive.sub_comp, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ hT _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle₁ q
    refine ⟨Y', r, ⟨_, _, _, mem', mem⟩, ?_⟩
    have eq := comp_distTriang_mor_zero₁₂ _ mem'
    dsimp at eq
    rw [← sub_eq_zero, ← Preadditive.comp_sub, hq, reassoc_of% eq, zero_comp]

/-- MS6 for a class `W` compatible with shifts holds as soon as the third component of every
morphism of distinguished triangles with two components in `W` is in `W`: TR3 completes the
commuting square to such a morphism. -/
private lemma isCompatibleWithTriangulation_of_hom₃ (W : MorphismProperty C)
    [W.IsCompatibleWithShift ℤ]
    (h : ∀ {T₁ T₂ : Triangle C} (φ : T₁ ⟶ T₂), T₁ ∈ distTriang C → T₂ ∈ distTriang C →
      W φ.hom₁ → W φ.hom₂ → W φ.hom₃) : W.IsCompatibleWithTriangulation where
  compatible_with_triangulation T₁ T₂ hT₁ hT₂ a b ha hb comm := by
    obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b comm
    exact ⟨c, h (Triangle.homMk T₁ T₂ a b c comm hc₂ hc₃) hT₁ hT₂ ha hb, hc₂, hc₃⟩

end Shared

/-! ### The morphisms inverted by an exact functor -/

section InverseImage

open CategoryTheory Limits Pretriangulated MorphismProperty

section

variable {D : Type u₂} [Category.{v₂} D]

/-- The property of being a zero object is closed under isomorphisms. -/
private lemma isZero_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (IsZero (C := D)) where
  of_iso e h := h.of_iso e.symm

variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The zero objects of a pre-triangulated category form a triangulated subcategory: they
contain a zero object, they are stable under shifts because the shift functors are additive,
and they are stable under extensions by `Pretriangulated.Triangle.isZero₂_of_isZero₁₃`. -/
private lemma isZero_isTriangulated :
    ObjectProperty.IsTriangulated (IsZero (C := D)) where
  isStableUnderShiftBy a := ⟨fun _ h => (shiftFunctor D a).map_isZero h⟩
  ext₂' T hT h₁ h₃ := ⟨T.obj₂, Triangle.isZero₂_of_isZero₁₃ T hT h₁ h₃, ⟨Iso.refl _⟩⟩

end

attribute [local instance] isZero_isClosedUnderIsomorphisms isZero_isTriangulated

section

variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A morphism of a pre-triangulated category is an isomorphism precisely when its cone is a
zero object: this is `Pretriangulated.Triangle.isZero₃_iff_isIso₁`. -/
private lemma trW_isZero :
    ObjectProperty.trW (IsZero (C := D)) = isomorphisms D := by
  ext X Y f
  rw [isomorphisms.iff]
  constructor
  · rintro ⟨Z, g, h, hT, mem⟩
    exact (Triangle.isZero₃_iff_isIso₁ (Triangle.mk f g h) hT).1 mem
  · intro hf
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
    exact ⟨Z, g, h, hT, (Triangle.isZero₃_iff_isIso₁ _ hT).2 hf⟩

end

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The cancellation axiom MS4 for the class of morphisms inverted by a functor `F`: no
hypothesis on `F` or on the two categories is needed, only that a morphism of `D` which
becomes an isomorphism after composing with a morphism on either side is an isomorphism. -/
private lemma inverseImage_isomorphisms_mem_of_comp_mem_comp (F : C ⥤ D) {X Y Z T : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (hfg : (isomorphisms D).inverseImage F (f ≫ g))
    (hgh : (isomorphisms D).inverseImage F (g ≫ h)) :
    (isomorphisms D).inverseImage F g := by
  rw [inverseImage_iff, isomorphisms.iff] at hfg hgh ⊢
  rw [F.map_comp] at hfg hgh
  exact isIso_of_isIso_comp_of_isIso_comp _ _ _ hfg hgh

variable [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- The morphisms inverted by an exact functor `F` are exactly those whose cone is sent to
zero by `F`, i.e. those in `F.kernel.trW`. -/
private lemma trW_kernel (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    ObjectProperty.trW F.kernel = (isomorphisms D).inverseImage F := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff, trW_isZero]
  rfl

/-- MS6 for the morphisms inverted by an exact functor: TR3 in `C` produces a morphism
completing a commuting square between two distinguished triangles, and it is inverted by `F`
because the images of the two triangles are distinguished and the images of the first two
components are isomorphisms. MS5 is the stability of `F.kernel` under shifts. -/
@[sga "4½ Etat_0 2.2" "partial"]
private lemma inverseImage_isomorphisms_isCompatibleWithTriangulation
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    ((isomorphisms D).inverseImage F).IsCompatibleWithTriangulation :=
  have : ((isomorphisms D).inverseImage F).IsCompatibleWithShift ℤ := trW_kernel F ▸ inferInstance
  isCompatibleWithTriangulation_of_hom₃ _ fun φ hT₁ hT₂ ha hb => by
    rw [inverseImage_iff, isomorphisms.iff] at ha hb ⊢
    exact isIso₃_of_isIso₁₂ (F.mapTriangle.map φ) (F.map_distinguished _ hT₁)
      (F.map_distinguished _ hT₂) ha hb

end

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- Let `F : C ⥤ D` be an exact functor of pre-triangulated categories. The class
`W = (isomorphisms D).inverseImage F` of morphisms of `C` inverted by `F` is a saturated
multiplicative system (MS1, MS2, MS3 and the cancellation axiom MS4) compatible with the
triangulated structure on `C` (MS5, MS6). -/
@[stacks 05R4, sga "4½ Etat_0 2.2" "partial"]
theorem Functor.isSaturated_and_isCompatibleWithTriangulation_inverseImage_isomorphisms
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] :
    ((isomorphisms D).inverseImage F).IsSaturated ∧
      ((isomorphisms D).inverseImage F).IsCompatibleWithTriangulation := by
  have h := trW_kernel F
  have : (ObjectProperty.trW F.kernel).IsMultiplicative := h ▸ inferInstance
  exact ⟨⟨h ▸ trW_hasLeftCalculusOfFractions F.kernel,
      h ▸ trW_hasRightCalculusOfFractions F.kernel,
      inverseImage_isomorphisms_mem_of_comp_mem_comp F⟩,
    inverseImage_isomorphisms_isCompatibleWithTriangulation F⟩

end CategoryTheory

end InverseImage

/-! ### The quasi-isomorphisms of a homological functor -/

section Homological

open CategoryTheory Limits Pretriangulated ComposableArrows

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {A : Type u₂} [Category.{v₂} A] [Abelian A] (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]

/-- The five lemma for a homological functor: if a morphism `φ` of distinguished triangles is
such that `Hⁱ(φ.hom₁)` and `Hⁱ(φ.hom₂)` are isomorphisms for all `i`, then `Hⁿ(φ.hom₃)` is an
isomorphism, by the five lemma applied to the two long exact cohomology sequences in degrees
`n` and `n + 1`. -/
private lemma isIso_shift_map_hom₃ {T₁ T₂ : Triangle D} (hT₁ : T₁ ∈ distTriang D)
    (hT₂ : T₂ ∈ distTriang D) (φ : T₁ ⟶ T₂)
    (h₁ : ∀ i : ℤ, IsIso ((H.shift i).map φ.hom₁))
    (h₂ : ∀ i : ℤ, IsIso ((H.shift i).map φ.hom₂)) (n : ℤ) :
    IsIso ((H.shift n).map φ.hom₃) := by
  have := h₁ n
  have := h₁ (n + 1)
  have := h₂ n
  have := h₂ (n + 1)
  let Φ : H.homologySequenceComposableArrows₅ T₁ n (n + 1) rfl ⟶
      H.homologySequenceComposableArrows₅ T₂ n (n + 1) rfl :=
    homMk₅ ((H.shift n).map φ.hom₁) ((H.shift n).map φ.hom₂) ((H.shift n).map φ.hom₃)
      ((H.shift (n + 1)).map φ.hom₁) ((H.shift (n + 1)).map φ.hom₂)
      ((H.shift (n + 1)).map φ.hom₃)
      ((CommSq.mk φ.comm₁).map (H.shift n)).w ((CommSq.mk φ.comm₂).map (H.shift n)).w
      (H.homologySequenceδ_naturality φ n (n + 1) rfl).symm
      ((CommSq.mk φ.comm₁).map (H.shift (n + 1))).w
      ((CommSq.mk φ.comm₂).map (H.shift (n + 1))).w
  refine Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono' (k := 0) (by omega)
    (H.homologySequenceComposableArrows₅_exact T₁ hT₁ n (n + 1) rfl)
    (H.homologySequenceComposableArrows₅_exact T₂ hT₂ n (n + 1) rfl) Φ
    0 1 2 3 4 rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ <;> dsimp [Φ] <;> infer_instance

/-- MS1 for the quasi-isomorphisms of `H`: the class of morphisms whose cone has vanishing
cohomology is multiplicative, because it consists of the morphisms inverted by all the
functors `Hⁱ` and isomorphisms are closed under composition. -/
private lemma homologicalKernel_trW_isMultiplicative :
    H.homologicalKernel.trW.IsMultiplicative where
  id_mem X := H.homologicalKernel.trW_of_isIso (𝟙 X)
  comp_mem f g hf hg := by
    rw [H.mem_homologicalKernel_trW_iff] at hf hg ⊢
    intro n
    have := hf n
    have := hg n
    rw [Functor.map_comp]
    infer_instance

/-- MS4 for the quasi-isomorphisms of `H`: a morphism whose composite with a morphism on
either side has a cone with vanishing cohomology has one itself. -/
private lemma homologicalKernel_trW_mem_of_comp_mem_comp {X Y Z T : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ T) (hfg : H.homologicalKernel.trW (f ≫ g))
    (hgh : H.homologicalKernel.trW (g ≫ h)) : H.homologicalKernel.trW g := by
  rw [H.mem_homologicalKernel_trW_iff] at hfg hgh ⊢
  exact fun n => isIso_of_isIso_comp_of_isIso_comp ((H.shift n).map f) _ ((H.shift n).map h)
    (by simpa using hfg n) (by simpa using hgh n)

/-- MS6 for the quasi-isomorphisms of `H`: given two distinguished triangles and a commuting
pair of quasi-isomorphisms between their first two terms, TR3 produces a third morphism
completing them to a morphism of triangles, and the five lemma (`isIso_shift_map_hom₃`) makes
it a quasi-isomorphism. -/
private lemma homologicalKernel_trW_isCompatibleWithTriangulation :
    H.homologicalKernel.trW.IsCompatibleWithTriangulation :=
  isCompatibleWithTriangulation_of_hom₃ _ fun φ hT₁ hT₂ ha hb =>
    (H.mem_homologicalKernel_trW_iff _).2 fun n => isIso_shift_map_hom₃ H hT₁ hT₂ φ
      ((H.mem_homologicalKernel_trW_iff _).1 ha) ((H.mem_homologicalKernel_trW_iff _).1 hb) n

end Homological

section HomologicalMain

open CategoryTheory Limits Pretriangulated

/-- Let `H : 𝒟 ⥤ 𝒜` be a homological functor from a pre-triangulated category to an abelian
category. Then
`S = {f ∈ Arrows(𝒟) ∣ Hⁱ(f) is an isomorphism for all i ∈ ℤ}`
is a saturated multiplicative system compatible with the triangulated
structure on `𝒟` (MS5 and MS6). -/
@[stacks 05R5]
theorem CategoryTheory.Functor.isSaturated_and_isCompatibleWithTriangulation
    {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {A : Type u₂} [Category.{v₂} A] [Abelian A] (H : D ⥤ A) [H.IsHomological]
    (S : MorphismProperty D)
    (hS : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), S f ↔ ∀ i : ℤ, IsIso (H.map (f⟦i⟧'))) :
    S.IsSaturated ∧ S.IsCompatibleWithTriangulation := by
  let _ : H.ShiftSequence ℤ := Functor.ShiftSequence.tautological H ℤ
  have hSW : S = H.homologicalKernel.trW := by
    ext X Y f
    rw [hS, H.mem_homologicalKernel_trW_iff]
    rfl
  subst hSW
  have := homologicalKernel_trW_isMultiplicative H
  exact ⟨⟨trW_hasLeftCalculusOfFractions _, trW_hasRightCalculusOfFractions _,
      homologicalKernel_trW_mem_of_comp_mem_comp H⟩,
    homologicalKernel_trW_isCompatibleWithTriangulation H⟩

end HomologicalMain

/-! ### The pre-triangulated structure on the localization -/

section Structure

open CategoryTheory Limits Pretriangulated

/-- Two pre-triangulated structures on the same category are equal as soon as they have the
same distinguished triangles: the class of distinguished triangles is the only datum of
`CategoryTheory.Pretriangulated`, all its other fields being propositions. -/
private theorem pretriangulated_ext {D : Type u₂} [Category.{v₂} D] [HasZeroObject D]
    [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    {h₁ h₂ : Pretriangulated D}
    (h : (letI := h₁; distTriang D) = (letI := h₂; distTriang D)) :
    h₁ = h₂ := by
  obtain ⟨S₁, _, _, _, _, _⟩ := h₁
  obtain ⟨S₂, _, _, _, _, _⟩ := h₂
  congr 1

namespace CategoryTheory.Triangulated.Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (L : C ⥤ D)
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [L.CommShift ℤ] [L.Additive]
  (W : MorphismProperty C) [L.IsLocalization W] [W.HasLeftCalculusOfFractions]
  [W.IsCompatibleWithTriangulation]

/-- Let `C` be a pre-triangulated category, let `W` be a multiplicative system of morphisms of `C`
compatible with the triangulated structure, and let `L : C ⥤ D` be a localization functor for `W`,
where `D` is additive, has a shift with which `L` commutes, and `L` is additive. Then there is a
unique pre-triangulated structure on `D` making `L` exact, namely
`CategoryTheory.Triangulated.Localization.pretriangulated L W`, and it is triangulated whenever `C`
is. -/
@[stacks 05R6, sga "4½ Etat_0 Problem2" "A_S exists, Q exact", sga "4½ Etat_0 2.3.2" "partial"]
theorem existsUnique_pretriangulated_and_isTriangulated :
    (letI := pretriangulated L W; L.IsTriangulated) ∧
      (∀ h : Pretriangulated D, (letI := h; L.IsTriangulated) → h = pretriangulated L W) ∧
        (letI := pretriangulated L W; IsTriangulated C → IsTriangulated D) := by
  have := Localization.essSurj_mapArrow L W
  refine ⟨inferInstance, fun h hL => ?_, ?_⟩
  · exact pretriangulated_ext (Set.ext fun T => (let := h; L.distTriang_iff T).trans
      (let := pretriangulated L W; L.distTriang_iff T).symm)
  · let _ := pretriangulated L W
    intro _
    exact isTriangulated L W

end CategoryTheory.Triangulated.Localization

end Structure

/-! ### Exactness of a functor factoring through the localization -/

section Factorization

open CategoryTheory Limits Pretriangulated Localization

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (L : C ⥤ D)
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [L.CommShift ℤ] [L.IsTriangulated] [L.mapArrow.EssSurj]
  (W : MorphismProperty C) [L.IsLocalization W]

/-- Let `C` be a pre-triangulated category, `W` a multiplicative system of morphisms of `C`
compatible with the triangulated structure, and `L : C ⥤ D` the (exact) localization functor. If
`F : C ⥤ E` is an exact functor to a pre-triangulated category and `F' : D ⥤ E` is its
factorization through `L`, then `F'`, for the commutation with the shift it inherits from that
factorization, is exact. -/
@[stacks 05R7 "(2)", sga "4½ Etat_0 Problem2" "G is exact", sga "4½ Etat_0 2.3.2" "partial"]
theorem isTriangulated_of_localization
    {E : Type u₃} [Category.{v₃} E] [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (F : C ⥤ E) [F.CommShift ℤ] [F.IsTriangulated] (F' : D ⥤ E) [Lifting L W F F'] :
    letI := commShiftOfLocalization L W ℤ F F'
    F'.IsTriangulated :=
  let := commShiftOfLocalization L W ℤ F F'
  isTriangulated_of_precomp_iso (Lifting.iso L W F F')

end CategoryTheory.Functor

add_to_stacks 05R7 "(1)" CategoryTheory.Functor.isHomological_of_localization

end Factorization

end
