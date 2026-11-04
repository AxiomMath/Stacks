module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FieldFibreTopologicalDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeReasonablePermanence

/-!
# The relative conditions on a fibre product of algebraic spaces

Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of algebraic spaces over a scheme `S`. If `X`
and `Z` both satisfy one of the conditions of Stacks 03JX, then so does the fibre product
`X ×_Y Z`. This is Stacks 0ABZ, and the proof is the source's: by Stacks 0ABX the morphism `f`
has the corresponding relative condition of Stacks 03KZ, by Stacks 03L0 its base change
`Z ×_Y X ⟶ Z` still has it, and by Stacks 0ABY the condition on `Z` then passes to
`Z ×_Y X`.

## Main results

* `AlgebraicGeometry.Space.isDecentSpace_pullback`: **Stacks 0ABZ**, the decent case — a fibre
  product of decent algebraic spaces over an algebraic space is decent.
* `AlgebraicGeometry.Space.isReasonableSpace_pullback`: **Stacks 0ABZ**, the reasonable case —
  a fibre product of reasonable algebraic spaces over an algebraic space is reasonable.
* `AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_pullback`: **Stacks 0ABZ**, the
  case `(β)` — a fibre product of algebraic spaces with property `(β)` of Stacks 03JX has
  property `(β)`.

## Implementation notes

The fibre product is the fibre product of presheaves, which is an algebraic space by
Stacks 02X2. The chain of three lemmas runs over `Z ×_Y X`, whose projection to `Z` is the
base change `AlgebraicGeometry.Space.isDecent_baseChange` produces, so each result is carried
across the symmetry `pullback g f ≅ pullback f g` by the invariance of the absolute conditions
under an isomorphism.

Property `(β)` is `AlgebraicGeometry.Space.HasFiniteRelationFibersAtEveryPoint`, condition (1)
of Stacks 03JU at every point, whereas the case `(β)` of Stacks 0ABX and of Stacks 0ABY are
stated in this repository with condition (4) of that lemma, a monomorphic field-valued
representative. The equivalence
`AlgebraicGeometry.Space.hasFiniteRelationFiberAt_iff_hasMonomorphicFieldRepresentative`
translates between the two conditions at a point of an algebraic space.

The reasonable case needs no such bridge: reasonableness of an algebraic space is condition
(2) of Stacks 03JT both in the hypothesis of the reasonable case of Stacks 0ABX,
`AlgebraicGeometry.Space.isReasonable_of_isReasonableSpace_source`, and in the conclusion of
the reasonable case of Stacks 0ABY,
`AlgebraicGeometry.Space.isReasonableSpace_of_isReasonable`.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KZ](https://stacks.math.columbia.edu/tag/03KZ)
* [Stacks Project, Tag 03L0](https://stacks.math.columbia.edu/tag/03L0)
* [Stacks Project, Tag 0ABX](https://stacks.math.columbia.edu/tag/0ABX)
* [Stacks Project, Tag 0ABY](https://stacks.math.columbia.edu/tag/0ABY)
* [Stacks Project, Tag 0ABZ](https://stacks.math.columbia.edu/tag/0ABZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Conditions (1) and (4) of Stacks 03JU at a point -/

section Bridge

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

end Bridge

/-! ### The fibre product -/

section FibreProduct

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0ABZ, decent.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of algebraic spaces
over `S`. If `X` and `Z` are decent algebraic spaces, then so is `X ×_Y Z`.

Decency of `X` makes `f` a decent morphism by Stacks 0ABX, its base change `Z ×_Y X ⟶ Z` is
decent by Stacks 03L0, and decency of `Z` together with that of the base change gives decency
of `Z ×_Y X` by Stacks 0ABY. -/
@[stacks 0ABZ "decent"]
theorem isDecentSpace_pullback (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (hXdec : IsDecentSpace B S hS X) (hZdec : IsDecentSpace B S hS Z) :
    IsDecentSpace B S hS (pullback f g) :=
  isDecentSpace_of_iso B S hS (pullbackSymmetry g f)
    (isDecentSpace_of_isDecent B S hS (isAlgebraicSpace_pullback B S hS g f hZ hX hY) hZ
      (pullback.fst g f) hZdec
      (isDecent_baseChange B S hS f g (isDecent_of_isDecentSpace_source B S hS hX hY f hXdec)))

/-- **Stacks 0ABZ, reasonable.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of algebraic
spaces over `S`. If `X` and `Z` are reasonable algebraic spaces, then so is `X ×_Y Z`.

Reasonableness of `X` makes `f` a reasonable morphism by Stacks 0ABX, its base change
`Z ×_Y X ⟶ Z` is reasonable by Stacks 03L0, and reasonableness of `Z` together with that of
the base change gives reasonableness of `Z ×_Y X` by Stacks 0ABY. -/
@[stacks 0ABZ "reasonable"]
theorem isReasonableSpace_pullback (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (hXr : IsReasonableSpace B S hS X) (hZr : IsReasonableSpace B S hS Z) :
    IsReasonableSpace B S hS (pullback f g) :=
  isReasonableSpace_of_iso B S hS (pullbackSymmetry g f)
    (isReasonableSpace_of_isReasonable B S hS
      (isAlgebraicSpace_pullback B S hS g f hZ hX hY) hZ (pullback.fst g f) hZr
      (isReasonable_baseChange B S hS f g
        (isReasonable_of_isReasonableSpace_source B S hS hX hY f hXr)))

/-- **Stacks 0ABZ, property `(β)`.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of algebraic
spaces over `S`. If `X` and `Z` have property `(β)` of Stacks 03JX, then so does `X ×_Y Z`.

Property `(β)` of `X` makes `f` a morphism with property `(β)` by Stacks 0ABX, its base change
`Z ×_Y X ⟶ Z` has property `(β)` by Stacks 03L0, and property `(β)` of `Z` together with that
of the base change gives property `(β)` of `Z ×_Y X` by Stacks 0ABY. -/
@[stacks 0ABZ "property beta"]
theorem hasFiniteRelationFibersAtEveryPoint_pullback (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (hXβ : HasFiniteRelationFibersAtEveryPoint B S hS X)
    (hZβ : HasFiniteRelationFibersAtEveryPoint B S hS Z) :
    HasFiniteRelationFibersAtEveryPoint B S hS (pullback f g) := by
  have hP : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hZ hX hY
  -- Stacks 0ABX: `f` has property `(β)`, and Stacks 03L0: so does its base change to `Z`.
  have hbc : HasPropertyBeta B S hS (pullback.fst g f) :=
    hasPropertyBeta_baseChange B S hS f g
      (hasPropertyBeta_of_hasMonomorphicFieldRepresentative B S hS hX hY f fun x ↦
        (hasFiniteRelationFiberAt_iff_hasMonomorphicFieldRepresentative B S hS hX x).mp
          (hXβ x))
  -- Stacks 0ABY, in the form of condition (4) of Stacks 03JU on `Z` and on the base changes.
  have hmono : ∀ w : points B S hS (pullback g f),
      HasMonomorphicFieldRepresentative B S hS (pullback g f) w :=
    hasMonomorphicFieldRepresentative_of_target_of_baseChange B S hS (pullback.fst g f)
      (fun z ↦ (hasFiniteRelationFiberAt_iff_hasMonomorphicFieldRepresentative B S hS hZ z).mp
        (hZβ z))
      fun T h w ↦ (hasFiniteRelationFiberAt_iff_hasMonomorphicFieldRepresentative B S hS
        (isAlgebraicSpace_pullback B S hS h (pullback.fst g f)
          (isAlgebraicSpace_yoneda B S hS T) hP hZ) w).mp (hbc T h w)
  exact hasFiniteRelationFibersAtEveryPoint_of_iso B S hS (pullbackSymmetry g f) fun w ↦
    (hasFiniteRelationFiberAt_iff_hasMonomorphicFieldRepresentative B S hS hP w).mpr (hmono w)

end FibreProduct

end AlgebraicGeometry.Space

end
