module

public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFullyFaithful
import all StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFullyFaithful

/-!
# Fibre products of glueing triples

The category `BeauvilleLaszlo.Space.GlueingData` of cartesian triples `(V, V', Y')` over
`U ← U' → X'` has fibre products, computed componentwise. The proof of Stacks 0F9U uses this
for the triple `(U ×_X T) ×_V (U ×_X T), …` of its relation: it is the fibre product of a
morphism of triples with itself.

## Main definitions

* `BeauvilleLaszlo.Space.glueingDataPullback`: the componentwise fibre product of two morphisms
  of cartesian glueing triples with a common target, with its two projections
  `BeauvilleLaszlo.Space.glueingDataPullbackFst` and
  `BeauvilleLaszlo.Space.glueingDataPullbackSnd`.

## Main results

* `BeauvilleLaszlo.Space.baseChange_preservesLimitsOfShape_cospan`: base change of algebraic
  spaces preserves fibre products.
* `BeauvilleLaszlo.Space.isPullback_glueingDataPullback`: the componentwise fibre product is a
  fibre product in the category of cartesian glueing triples.

## Implementation notes

The category of triples is a full subcategory of an iterated comma category whose right-hand
functors are base changes. Since base change preserves fibre products,
`CategoryTheory.Comma.fstSndJointlyReflectLimit` reduces the universal property to the three
componentwise fibre products, and the fully faithful inclusion of the full subcategory reflects
it.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

/-! ### Base change preserves fibre products -/

/-- **Base change of algebraic spaces preserves fibre products.** -/
theorem baseChange_preservesLimitsOfShape_cospan (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT) :
    PreservesLimitsOfShape WalkingCospan (baseChange B S T hS hT g) :=
  ⟨fun {K} =>
    have := baseChange_preservesPullback B S T hS hT g (K.map WalkingCospan.Hom.inl)
      (K.map WalkingCospan.Hom.inr)
    preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm⟩

/-! ### The componentwise fibre product of two morphisms of triples -/

section Pullback

variable (B : BigFppfSite.{u}) (U' U X' : Scheme.{u}) (hU' : B.Contains U')
  (hU : B.Contains U) (hX' : B.Contains X')
  (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')

attribute [local instance] baseChange_preservesLimitsOfShape_cospan

variable {U' U X' hU' hU hX' gU gX'}

/-- The structure arrow over `U` of the componentwise fibre product. -/
noncomputable abbrev glueingDataPullbackToU {D E T : GlueingData B U' U X' hU' hU hX' gU gX'}
    (a : D ⟶ T) (b : E ⟶ T) :
    pullback a.hom.left.left b.hom.left.left ⟶
      (baseChange B U' U hU' hU gU).obj (pullback a.hom.left.right b.hom.left.right) :=
  pullback.map _ _ _ _ D.obj.left.hom E.obj.left.hom T.obj.left.hom a.hom.left.w b.hom.left.w ≫
    (PreservesPullback.iso (baseChange B U' U hU' hU gU) a.hom.left.right b.hom.left.right).inv

/-- The structure arrow over `X'` of the componentwise fibre product. -/
noncomputable abbrev glueingDataPullbackToX' {D E T : GlueingData B U' U X' hU' hU hX' gU gX'}
    (a : D ⟶ T) (b : E ⟶ T) :
    pullback a.hom.left.left b.hom.left.left ⟶
      (baseChange B U' X' hU' hX' gX').obj (pullback a.hom.right b.hom.right) :=
  pullback.map _ _ _ _ D.obj.hom E.obj.hom T.obj.hom a.hom.w b.hom.w ≫
    (PreservesPullback.iso (baseChange B U' X' hU' hX' gX') a.hom.right b.hom.right).inv

/-- **The componentwise fibre product of two morphisms of cartesian glueing triples.** -/
noncomputable def glueingDataPullback {D E T : GlueingData B U' U X' hU' hU hX' gU gX'}
    (a : D ⟶ T) (b : E ⟶ T) : GlueingData B U' U X' hU' hU hX' gU gX' :=
  have : IsIso D.obj.left.hom := D.property.1
  have : IsIso E.obj.left.hom := E.property.1
  have : IsIso T.obj.left.hom := T.property.1
  have : IsIso D.obj.hom := D.property.2
  have : IsIso E.obj.hom := E.property.2
  have : IsIso T.obj.hom := T.property.2
  ⟨⟨⟨pullback a.hom.left.left b.hom.left.left, pullback a.hom.left.right b.hom.left.right,
      glueingDataPullbackToU B a b⟩, pullback a.hom.right b.hom.right,
      glueingDataPullbackToX' B a b⟩,
    ⟨inferInstanceAs (IsIso (glueingDataPullbackToU B a b)),
      inferInstanceAs (IsIso (glueingDataPullbackToX' B a b))⟩⟩

/-- The first projection of the componentwise fibre product. -/
noncomputable def glueingDataPullbackFst {D E T : GlueingData B U' U X' hU' hU hX' gU gX'}
    (a : D ⟶ T) (b : E ⟶ T) : glueingDataPullback B a b ⟶ D :=
  ObjectProperty.homMk
    { left :=
        { left := pullback.fst _ _
          right := pullback.fst _ _
          w := by
            dsimp only [glueingDataPullback, Functor.id_map]
            rw [glueingDataPullbackToU, Category.assoc, PreservesPullback.iso_inv_fst]
            simp only [pullback.map, pullback.lift_fst] }
      right := pullback.fst _ _
      w := by
        dsimp only [glueingDataPullback, Comma.fst_map]
        rw [glueingDataPullbackToX', Category.assoc, PreservesPullback.iso_inv_fst]
        simp only [pullback.map, pullback.lift_fst] }

/-- The second projection of the componentwise fibre product. -/
noncomputable def glueingDataPullbackSnd {D E T : GlueingData B U' U X' hU' hU hX' gU gX'}
    (a : D ⟶ T) (b : E ⟶ T) : glueingDataPullback B a b ⟶ E :=
  ObjectProperty.homMk
    { left :=
        { left := pullback.snd _ _
          right := pullback.snd _ _
          w := by
            dsimp only [glueingDataPullback, Functor.id_map]
            rw [glueingDataPullbackToU, Category.assoc, PreservesPullback.iso_inv_snd]
            simp only [pullback.map, pullback.lift_snd] }
      right := pullback.snd _ _
      w := by
        dsimp only [glueingDataPullback, Comma.fst_map]
        rw [glueingDataPullbackToX', Category.assoc, PreservesPullback.iso_inv_snd]
        simp only [pullback.map, pullback.lift_snd] }

/-- The two projections of the componentwise fibre product of `a` and `b` form a commutative
square with `a` and `b`. -/
theorem glueingDataPullback_condition {D E T : GlueingData B U' U X' hU' hU hX' gU gX'}
    (a : D ⟶ T) (b : E ⟶ T) :
    glueingDataPullbackFst B a b ≫ a = glueingDataPullbackSnd B a b ≫ b := by
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · apply Comma.hom_ext <;> exact pullback.condition
  · exact pullback.condition

/-- **The componentwise fibre product is the fibre product of cartesian glueing triples.** -/
theorem isPullback_glueingDataPullback {D E T : GlueingData B U' U X' hU' hU hX' gU gX'}
    (a : D ⟶ T) (b : E ⟶ T) :
    IsPullback (glueingDataPullbackFst B a b) (glueingDataPullbackSnd B a b) a b := by
  let ι := ObjectProperty.ι (fun Z : Comma
      (Comma.fst (𝟭 (AlgebraicSpaces B U' hU')) (baseChange B U' U hU' hU gU))
      (baseChange B U' X' hU' hX' gX') => IsIso Z.left.hom ∧ IsIso Z.hom)
  have hw := glueingDataPullback_condition B a b
  have hc : IsLimit (ι.mapCone (PullbackCone.mk _ _ hw)) := by
    apply Comma.fstSndJointlyReflectLimit
    · apply Comma.fstSndJointlyReflectLimit
      · exact (isLimitMapConePullbackConeEquiv
          (ι ⋙ Comma.fst _ _ ⋙ Comma.fst _ _) hw).symm
          (IsPullback.of_hasPullback a.hom.left.left b.hom.left.left).isLimit
      · exact (isLimitMapConePullbackConeEquiv
          (ι ⋙ Comma.fst _ _ ⋙ Comma.snd _ _) hw).symm
          (IsPullback.of_hasPullback a.hom.left.right b.hom.left.right).isLimit
    · exact (isLimitMapConePullbackConeEquiv (ι ⋙ Comma.snd _ _) hw).symm
        (IsPullback.of_hasPullback a.hom.right b.hom.right).isLimit
  exact IsPullback.of_map ι hw (IsPullback.of_isLimit (isLimitMapConePullbackConeEquiv ι hw hc))

end Pullback

end BeauvilleLaszlo.Space

end
