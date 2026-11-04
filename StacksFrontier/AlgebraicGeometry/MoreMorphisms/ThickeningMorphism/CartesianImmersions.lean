module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Extension

/-!
# Immersions, finiteness and monomorphy across a cartesian morphism of thickenings

Let

```
X --f--→ S
|        |
i        j
↓        ↓
X' -f'-→ S'
```

be a cartesian square of schemes in which `j` is a *finite-order* thickening, so that `i` is
automatically its base change and no separate hypothesis on `i` is needed. Then `f` is a closed
immersion, finite, a monomorphism, or an immersion exactly when `f'` is.

In each case the implication from `f'` to `f` is base change. In the other direction each of the
first three properties forces `f` to be locally of finite type, and
`Stacks.Thickenings.locallyOfFiniteType_iff_of_isFiniteOrderThickening`, the local finite type
clause of the same tag, then makes `f'` locally of finite type too; the square has become a
`Stacks.Thickenings.CartesianFiniteTypeMorphism`, for which the corresponding clause of Stacks
0BPG is available with no hypothesis on the order of the thickenings. That disposes of closed
immersions, finiteness and immersions.

Monomorphy is not of that shape, because a monomorphism need not be locally of finite type, and
is argued separately. A morphism is a monomorphism exactly when the first projection of its
self-fibre-product is an isomorphism, so it suffices to make `pullback.fst f' f'` an
isomorphism. That projection sits in a *new* cartesian square of thickenings, obtained from the
given one by pulling the source thickening `i` back along it:

```
X ×_{X'} (X' ×_{S'} X') --→ X
|                           |
↓                           i
↓                           ↓
X' ×_{S'} X' -----fst-----→ X'
```

whose base thickening is `i`, of finite order because it is the base change of `j`. Its upper
map has the diagonal of `f'` as a section, and monomorphy of `f` makes that section a two-sided
inverse: a point of the upper left corner is a pair of points of `X'` with the same image in
`S'`, the first of which lies in `X`; cartesianness forces the second to lie in `X` as well, and
`f` being a monomorphism identifies the two. An isomorphism is a closed immersion, so the closed
immersion clause proved above makes `pullback.fst f' f'` a closed immersion, hence a
monomorphism. It is also a split epimorphism, retracted by the diagonal, so it is an
isomorphism, and monomorphy of `f'` is read off the kernel-pair square.

## Main results

* `Stacks.Thickenings.isClosedImmersion_iff_of_isFiniteOrderThickening`: part (1).
* `Stacks.Thickenings.isFinite_iff_of_isFiniteOrderThickening`: part (8).
* `Stacks.Thickenings.mono_iff_of_isFiniteOrderThickening`: part (9).
* `Stacks.Thickenings.isImmersion_iff_of_isFiniteOrderThickening`: part (10).

## Implementation notes

The commutative square is recorded by `CategoryTheory.IsPullback`, which avoids choosing a fibre
product; the hypothesis that the source inclusion `i` is a thickening is *not* taken, since it is
the base change of `j` along `f'` and finite-order thickenings are stable under base change
(Stacks 09ZX).

The monomorphy argument deliberately uses only the closed immersion clause of this tag, whose
proof runs through the infinitesimal criterion
`AlgebraicGeometry.isClosedImmersion_of_infinitesimal_baseChange` and not through any
characterisation of closed immersions as universally closed monomorphisms, so there is no
circularity.

## References

* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 0BPG](https://stacks.math.columbia.edu/tag/0BPG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings

universe u

variable {X X' S S' : Scheme.{u}}

/-- The source inclusion of a cartesian square whose base thickening has finite order is itself
a finite-order thickening, being its base change. -/
theorem isFiniteOrderThickening_left_of_isPullback {i : X ⟶ X'} {j : S ⟶ S'}
    {f : X ⟶ S} {f' : X' ⟶ S'} (hj : IsFiniteOrderThickening j)
    (hcart : IsPullback i f f' j) : IsFiniteOrderThickening i :=
  isFiniteOrderThickening_isStableUnderBaseChange.of_isPullback hcart.flip hj

/-- The cartesian locally finite type morphism of thickenings attached to a cartesian square
whose base thickening has finite order and whose morphism of closed subschemes is locally of
finite type: the local finite type clause of Stacks 09ZW supplies the second finiteness
hypothesis. -/
private def ofFiniteOrder (i : X ⟶ X') (j : S ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S')
    (hj : IsFiniteOrderThickening j) (hcart : IsPullback i f f' j)
    (hf : LocallyOfFiniteType f) : CartesianFiniteTypeMorphism.{u} where
  X := X
  X' := X'
  Y := S
  Y' := S'
  i := i
  j := j
  morphism := Arrow.homMk f f' hcart.w.symm
  sourceThickening := (isFiniteOrderThickening_left_of_isPullback hj hcart).isThickening
  targetThickening := hj.isThickening
  locallyOfFiniteType_left := hf
  locallyOfFiniteType_right :=
    (locallyOfFiniteType_iff_of_isFiniteOrderThickening i j f f' hj hcart).mp hf
  cartesian := hcart.flip

/-- A property of morphisms of schemes that is stable under base change, implies local finite type
and is invariant across cartesian locally finite type morphisms of thickenings, is invariant across
a cartesian morphism of thickenings whose base thickening has finite order. -/
private theorem iff_of_isFiniteOrderThickening (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f → LocallyOfFiniteType f)
    (hiff : ∀ C : CartesianFiniteTypeMorphism.{u}, P C.f ↔ P C.f')
    (i : X ⟶ X') (j : S ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S') (hj : IsFiniteOrderThickening j)
    (hcart : IsPullback i f f' j) : P f ↔ P f' :=
  ⟨fun hf => (hiff (ofFiniteOrder i j f f' hj hcart (hP f hf))).mp hf,
    fun hf' => MorphismProperty.of_isPullback hcart hf'⟩

/-- **Stacks 09ZW, part (1).** Being a closed immersion ascends and descends across a cartesian
morphism of thickenings when the thickening of the base has finite order. -/
@[stacks 09ZW "closed_immersion"]
theorem isClosedImmersion_iff_of_isFiniteOrderThickening (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S') (hj : IsFiniteOrderThickening j)
    (hcart : IsPullback i f f' j) : IsClosedImmersion f ↔ IsClosedImmersion f' :=
  iff_of_isFiniteOrderThickening @IsClosedImmersion (fun _ _ => inferInstance)
    CartesianFiniteTypeMorphism.isClosedImmersion_iff i j f f' hj hcart

/-- **Stacks 09ZW, part (8).** Being finite ascends and descends across a cartesian morphism of
thickenings when the thickening of the base has finite order. -/
@[stacks 09ZW "finite"]
theorem isFinite_iff_of_isFiniteOrderThickening (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S') (hj : IsFiniteOrderThickening j)
    (hcart : IsPullback i f f' j) : IsFinite f ↔ IsFinite f' :=
  iff_of_isFiniteOrderThickening @IsFinite (fun _ _ => inferInstance)
    CartesianFiniteTypeMorphism.isFinite_iff i j f f' hj hcart

/-- **Stacks 09ZW, part (10).** Being an immersion ascends and descends across a cartesian
morphism of thickenings when the thickening of the base has finite order. -/
@[stacks 09ZW "immersion"]
theorem isImmersion_iff_of_isFiniteOrderThickening (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S') (hj : IsFiniteOrderThickening j)
    (hcart : IsPullback i f f' j) : IsImmersion f ↔ IsImmersion f' :=
  iff_of_isFiniteOrderThickening @IsImmersion (fun _ _ => inferInstance)
    CartesianFiniteTypeMorphism.isImmersion_iff i j f f' hj hcart

/-! ### Monomorphy -/

/-- The section of the base change of `i` along `pullback.fst f' f'` cut out by the diagonal of
`f'`: a point of `X` goes to the pair consisting of its image in `X'` taken twice. -/
private noncomputable def monoSection (i : X ⟶ X') (f' : X' ⟶ S') :
    X ⟶ pullback i (pullback.fst f' f') :=
  pullback.lift (𝟙 X) (i ≫ pullback.diagonal f') (by simp)

section Mono

variable {i : X ⟶ X'} {j : S ⟶ S'} {f : X ⟶ S} {f' : X' ⟶ S'}

private theorem monoSection_comp_fst :
    monoSection i f' ≫ pullback.fst i (pullback.fst f' f') = 𝟙 X :=
  pullback.lift_fst _ _ _

private theorem monoSection_comp_snd :
    monoSection i f' ≫ pullback.snd i (pullback.fst f' f') = i ≫ pullback.diagonal f' :=
  pullback.lift_snd _ _ _

/-- The two projections of `X' ×_{S'} X'` agree on the base change of `i` along the first one,
as soon as `f` is a monomorphism.

A point of that base change is a pair `(a, b)` of points of `X'` with `f'(a) = f'(b)` and `a` in
`X`. The cartesian square identifies `X` with the inverse image of `S` in `X'`, so the common
value `f'(a) = f'(b)` lying in `S` exhibits `b` as a second factorisation of the pair through
`X` with the same image under `f`; monomorphy of `f` identifies it with the first. -/
private theorem snd_comp_fst_eq_snd_comp_snd (hcart : IsPullback i f f' j) (hf : Mono f) :
    pullback.snd i (pullback.fst f' f') ≫ pullback.fst f' f' =
      pullback.snd i (pullback.fst f' f') ≫ pullback.snd f' f' := by
  have h1 : pullback.snd f' f' ≫ f' = pullback.fst f' f' ≫ f' :=
    (pullback.condition (f := f') (g := f')).symm
  have h2 : pullback.snd i (pullback.fst f' f') ≫ pullback.fst f' f' =
      pullback.fst i (pullback.fst f' f') ≫ i :=
    (pullback.condition (f := i) (g := pullback.fst f' f')).symm
  have hcond : (pullback.snd i (pullback.fst f' f') ≫ pullback.snd f' f') ≫ f' =
      (pullback.fst i (pullback.fst f' f') ≫ f) ≫ j := by
    simp only [Category.assoc]
    rw [h1, ← Category.assoc, h2, Category.assoc, hcart.w]
  have hmono : Mono f := hf
  have hfst := hcart.lift_fst (pullback.snd i (pullback.fst f' f') ≫ pullback.snd f' f')
    (pullback.fst i (pullback.fst f' f') ≫ f) hcond
  have hsnd := hcart.lift_snd (pullback.snd i (pullback.fst f' f') ≫ pullback.snd f' f')
    (pullback.fst i (pullback.fst f' f') ≫ f) hcond
  rw [h2, ← hfst, (cancel_mono f).mp hsnd]

/-- If `f` is a monomorphism then the diagonal section is a two-sided inverse of the base change
of `i` along the first projection of `X' ×_{S'} X'`. -/
private theorem fst_comp_i_comp_diagonal (hcart : IsPullback i f f' j) (hf : Mono f) :
    pullback.fst i (pullback.fst f' f') ≫ i ≫ pullback.diagonal f' =
      pullback.snd i (pullback.fst f' f') := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    exact pullback.condition
  · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id,
      ← snd_comp_fst_eq_snd_comp_snd hcart hf]
    exact pullback.condition

/-- If `f` is a monomorphism then the base change of `i` along the first projection of
`X' ×_{S'} X'` is an isomorphism. -/
private theorem isIso_fst_pullback (hcart : IsPullback i f f' j) (hf : Mono f) :
    IsIso (pullback.fst i (pullback.fst f' f')) := by
  refine ⟨monoSection i f', ?_, monoSection_comp_fst⟩
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, monoSection_comp_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, monoSection_comp_snd, Category.id_comp]
    exact fst_comp_i_comp_diagonal hcart hf

/-- If `f` is a monomorphism then the first projection of `X' ×_{S'} X'` is a monomorphism.

The square pulling `i` back along that projection is a cartesian morphism of thickenings whose
base thickening `i` is of finite order and whose upper map is an isomorphism, hence a closed
immersion; part (1) transfers that to the projection, and a closed immersion of schemes is a
monomorphism. -/
private theorem mono_pullback_fst (hj : IsFiniteOrderThickening j)
    (hcart : IsPullback i f f' j) (hf : Mono f) : Mono (pullback.fst f' f') := by
  have := isIso_fst_pullback hcart hf
  have : IsClosedImmersion (pullback.fst f' f') :=
    (isClosedImmersion_iff_of_isFiniteOrderThickening
      (pullback.snd i (pullback.fst f' f')) i (pullback.fst i (pullback.fst f' f'))
      (pullback.fst f' f') (isFiniteOrderThickening_left_of_isPullback hj hcart)
      (IsPullback.of_hasPullback i (pullback.fst f' f')).flip).mp inferInstance
  infer_instance

end Mono

/-- **Stacks 09ZW, part (9).** Being a monomorphism ascends and descends across a cartesian
morphism of thickenings when the thickening of the base has finite order. -/
@[stacks 09ZW "monomorphism"]
theorem mono_iff_of_isFiniteOrderThickening (i : X ⟶ X') (j : S ⟶ S')
    (f : X ⟶ S) (f' : X' ⟶ S') (hj : IsFiniteOrderThickening j)
    (hcart : IsPullback i f f' j) : Mono f ↔ Mono f' := by
  refine ⟨fun hf => ?_, fun hf' => ?_⟩
  · have := mono_pullback_fst hj hcart hf
    have : IsSplitEpi (pullback.fst f' f') :=
      IsSplitEpi.mk' ⟨pullback.diagonal f', pullback.diagonal_fst f'⟩
    have : IsIso (pullback.fst f' f') := isIso_of_mono_of_isSplitEpi _
    exact IsKernelPair.mono_of_isIso_fst (IsPullback.of_hasPullback f' f')
  · have := hf'
    exact hcart.flip.mono_fst_of_mono

end Stacks.Thickenings

end
