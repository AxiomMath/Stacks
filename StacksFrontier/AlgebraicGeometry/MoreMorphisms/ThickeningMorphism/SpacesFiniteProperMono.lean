module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.EtaleLocalProperties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.SpacesImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SourceFiniteOrderMorphismImmersions

/-!
# Finiteness, monomorphisms and properness across a cartesian morphism of thickenings of
# algebraic spaces

Let

```
X --f--→ Y
|        |
↓        ↓
X' -f'-→ Y'
```

be a morphism of thickenings of algebraic spaces over a scheme `S` which identifies `X` with
`Y ×_{Y'} X'`, and in which `f` and `f'` are locally of finite type; that is, let it be an
`AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings`. This file proves
parts (2), (6) and (8) of Stacks 0BPJ: `f` is finite, a monomorphism, respectively proper exactly
when `f'` is; parts (3) and (7), closed immersions and immersions, are the base's declarations in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/SpacesImmersions.lean`, registered
here. Parts (1), (4) and (5)
are in `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/EtaleLocalProperties.lean`
and `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/Unramified.lean`.

In each case the implication from `f'` to `f` is base change along the cartesian square
(`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/BaseChange.lean`).

* **Properness, part (8)** is separatedness, local finite type, quasi-compactness and universal
  closedness. Separatedness, quasi-compactness and universal closedness are invariant under any
  morphism of thickenings by Stacks 09ZY, and both maps are locally of finite type.
* **Finiteness, part (2)** is properness together with local quasi-finiteness, by Stacks 0A4X;
  properness is part (8) and local quasi-finiteness is part (1).
* **Closed immersions, part (3)** are the universally closed, unramified, universally injective
  morphisms, by Stacks 05W8. Universal closedness is Stacks 09ZY, unramifiedness is part (5),
  and universal injectivity of `f'` follows from that of `X ⟶ Y ⟶ Y'` because `X ⟶ X'` is
  surjective. The source instead cites Stacks 08B2, whose formalization in this library carries
  the hypotheses of Stacks 07VT; the route through Stacks 05W8 needs none.
* **Immersions, part (7).** Following the source, `f` factors as a closed immersion into an open
  subspace `V ⊆ Y` (Stacks 04CE); `V` is the inverse image of an open subspace `V' ⊆ Y'` with
  the same points (Stacks 05ZP), `f'` factors through `V'`, and the square restricted to `V'` is
  again a cartesian morphism of thickenings with both maps locally of finite type, so part (3)
  applies to it.
* **Monomorphisms, part (6).** If `f` is a monomorphism, the first projection of
  `X' ×_{Y'} X'` sits in a cartesian morphism of thickenings with target thickening `X ⊆ X'`,
  whose ambient map is a base change of `f'`, hence locally of finite type, and whose map of
  smaller spaces is an isomorphism with inverse the diagonal. Part (3) makes the first
  projection a closed immersion, hence a monomorphism; split by the diagonal it is an
  isomorphism, so `f'` is a monomorphism. The source runs this through the conormal sheaf of
  the diagonal and part (5); the route here avoids the algebraic-space analogue of Stacks 08S2.

## Main results

* `AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings.isFinite_iff`:
  part (2).
* `AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings.mono_iff`: part (6).
* `AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings.isProper_iff`:
  part (8).

Parts (3) and (7) for such a morphism are the base's
`AlgebraicGeometry.Space.isClosedImmersion_iff_of_cartesianMorphismOfThickenings` and
`AlgebraicGeometry.Space.isImmersion_iff_of_cartesianMorphismOfThickenings` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/SpacesImmersions.lean`, which the
base registers for those parts only at the point test of Section 04XB; they are registered here
for parts (3) and (7) by `add_to_stacks`.

## References

* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 05W8](https://stacks.math.columbia.edu/tag/05W8)
* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Properness and finiteness -/

/-- **Stacks 0BPJ, part (8).** In a cartesian morphism of thickenings of algebraic spaces whose
two component maps are locally of finite type, the map between the smaller spaces is proper
exactly when the map between the ambient spaces is. -/
@[stacks 0BPJ "part (8): f is proper iff f' is"]
theorem isProper_iff (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) :
    IsProper B S hS T.f ↔ IsProper B S hS T.f' :=
  and_congr
    (isSeparated_iff_isSeparated_of_isThickening B S hS T.sourceThickening T.targetThickening
      T.morphism)
    (and_congr
      (and_congr (iff_of_true T.locallyOfFiniteType_left T.locallyOfFiniteType_right)
        (isQuasiCompact_iff_isQuasiCompact_of_isThickening B S hS T.sourceThickening
          T.targetThickening T.morphism))
      (universallyClosed_iff_universallyClosed_of_isThickening B S hS T.sourceThickening
        T.targetThickening T.morphism))

/-- **Stacks 0BPJ, part (2).** In a cartesian morphism of thickenings of algebraic spaces whose
two component maps are locally of finite type, the map between the smaller spaces is finite
exactly when the map between the ambient spaces is. -/
@[stacks 0BPJ "part (2): f is finite iff f' is"]
theorem isFinite_iff (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) :
    IsFinite B S hS T.f ↔ IsFinite B S hS T.f' :=
  ((isFinite_tfae B S hS T.sourceThickening.1.1 T.targetThickening.1.1 T.f).out 1 2).trans
    ((and_congr T.isProper_iff
        (isLocallyQuasiFinite_iff_of_cartesianMorphismOfThickenings B S hS T)).trans
      ((isFinite_tfae B S hS T.X'.2 T.Y'.2 T.f').out 1 2).symm)

/-! ### Closed immersions -/

/-! ### Immersions -/

/-! ### Monomorphisms -/

/-- If `f` is a monomorphism, then so is the first projection of `X' ×_{Y'} X'`.

Pulling `X ⊆ X'` back along the first projection gives a cartesian morphism of thickenings
whose target thickening is `X ⊆ X'`, whose ambient map, the first projection, is a base change
of `f'` and so locally of finite type, and whose morphism of smaller spaces is the canonical map
out of the inverse image. Monomorphy of `f` makes that map an isomorphism, with inverse the
diagonal of `f'`: a section `(a, b)` of the inverse image has `a` in `X`, hence `f'(b) = f'(a)`
in `Y`, hence `b` in `X` by cartesianness, and then `f(a) = f(b)` forces `a = b`. Part (3)
transfers the closed immersion property to the first projection. -/
theorem mono_pullback_fst_of_mono (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS)
    (hf : Mono T.f) : Mono (pullback.fst T.f' T.f') := by
  let P : AlgebraicSpaces B S hS :=
    ⟨pullback T.f' T.f', isAlgebraicSpace_pullback B S hS T.f' T.f' T.X'.2 T.X'.2 T.Y'.2⟩
  let p₁ : P ⟶ T.X' := ObjectProperty.homMk (pullback.fst T.f' T.f')
  let Z : Subfunctor P.1 := T.X.preimage (pullback.fst T.f' T.f')
  have hfstft : IsLocallyOfFiniteType B S hS (pullback.fst T.f' T.f') :=
    IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback T.f' T.f') T.X'.2
      T.Y'.2 T.locallyOfFiniteType_right
  let N : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS :=
    { X' := P
      Y' := T.X'
      X := Z
      Y := T.X
      sourceThickening := isThickening_preimage B S hS T.X p₁ T.sourceThickening
      targetThickening := T.sourceThickening
      morphism := Arrow.homMk (T.X.fromPreimage (pullback.fst T.f' T.f'))
        (pullback.fst T.f' T.f') (Subfunctor.fromPreimage_ι T.X _)
      locallyOfFiniteType_left :=
        IsLocallyOfFiniteType.of_isPullback B S hS
          (Subfunctor.isPullback_preimage (pullback.fst T.f' T.f') T.X) P.2 T.X'.2 hfstft
      locallyOfFiniteType_right := hfstft
      cartesian := Subfunctor.isPullback_preimage (pullback.fst T.f' T.f') T.X }
  -- The diagonal of `f'` on `X` lands in `Z`.
  have hrange : Subfunctor.range (T.X.ι ≫ pullback.diagonal T.f') ≤ Z := by
    rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp,
      show (T.X.ι ≫ pullback.diagonal T.f') ≫ pullback.fst T.f' T.f' = T.X.ι by simp]
    exact le_of_eq (Subfunctor.range_ι T.X)
  let δ : T.X.toFunctor ⟶ Z.toFunctor := Subfunctor.lift (T.X.ι ≫ pullback.diagonal T.f') hrange
  have hδ : δ ≫ Z.ι = T.X.ι ≫ pullback.diagonal T.f' := Subfunctor.lift_ι _ _
  -- On `Z` the two projections agree.
  have hfstsnd : Z.ι ≫ pullback.fst T.f' T.f' = Z.ι ≫ pullback.snd T.f' T.f' := by
    have hw : T.f ≫ T.Y.ι = T.X.ι ≫ T.f' := T.morphism.w
    have hcond : (T.X.fromPreimage (pullback.fst T.f' T.f') ≫ T.f) ≫ T.Y.ι =
        (Z.ι ≫ pullback.snd T.f' T.f') ≫ T.f' := by
      rw [Category.assoc, hw, ← Category.assoc, Subfunctor.fromPreimage_ι, Category.assoc,
        Category.assoc, pullback.condition]
    have hfst := T.cartesian.lift_fst
      (T.X.fromPreimage (pullback.fst T.f' T.f') ≫ T.f) (Z.ι ≫ pullback.snd T.f' T.f') hcond
    have hsnd := T.cartesian.lift_snd
      (T.X.fromPreimage (pullback.fst T.f' T.f') ≫ T.f) (Z.ι ≫ pullback.snd T.f' T.f') hcond
    rw [← hsnd, (cancel_mono T.f).mp hfst, Subfunctor.fromPreimage_ι]
  -- The morphism of smaller spaces of `N` is an isomorphism, with inverse `δ`.
  have hiso : IsIso (T.X.fromPreimage (pullback.fst T.f' T.f')) := by
    refine ⟨δ, ?_, ?_⟩
    · refine (cancel_mono Z.ι).mp ?_
      rw [Category.assoc, hδ, ← Category.assoc, Subfunctor.fromPreimage_ι, Category.id_comp]
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
        rfl
      · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id]
        exact hfstsnd.symm ▸ rfl
    · refine (cancel_mono T.X.ι).mp ?_
      rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, hδ]
      simp
  have hsmall : IsClosedImmersion B S hS N.f := by
    show IsClosedImmersion B S hS (T.X.fromPreimage (pullback.fst T.f' T.f'))
    exact isClosedImmersion_of_isIso B S hS _
  exact mono_of_isClosedImmersion B S hS _
    ((isClosedImmersion_iff_of_cartesianMorphismOfThickenings _ _ _ N).mp hsmall)

/-- **Stacks 0BPJ, part (6).** In a cartesian morphism of thickenings of algebraic spaces whose
two component maps are locally of finite type, the map between the smaller spaces is a
monomorphism exactly when the map between the ambient spaces is.

If `f` is a monomorphism, the first projection of `X' ×_{Y'} X'` is a monomorphism by
`mono_pullback_fst_of_mono` and a split epimorphism retracted by the diagonal, hence an
isomorphism, so `f'` is a monomorphism. The converse is base change. -/
@[stacks 0BPJ "part (6): f is a monomorphism iff f' is"]
theorem mono_iff (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) :
    Mono T.f ↔ Mono T.f' := by
  refine ⟨fun hf => ?_, T.mono⟩
  have hmono : Mono (pullback.fst T.f' T.f') := T.mono_pullback_fst_of_mono hf
  have hsplit : IsSplitEpi (pullback.fst T.f' T.f') :=
    IsSplitEpi.mk' ⟨pullback.diagonal T.f', pullback.diagonal_fst T.f'⟩
  have hiso : IsIso (pullback.fst T.f' T.f') := isIso_of_mono_of_isSplitEpi _
  exact IsKernelPair.mono_of_isIso_fst (IsPullback.of_hasPullback T.f' T.f')

end AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings

/- Parts (3) and (7) of Stacks 0BPJ for a cartesian morphism of thickenings of algebraic spaces
with both maps locally of finite type, as the base states them. -/
add_to_stacks 0BPJ "part (3): f is a closed immersion iff f' is"
  AlgebraicGeometry.Space.isClosedImmersion_iff_of_cartesianMorphismOfThickenings

add_to_stacks 0BPJ "part (7): f is an immersion iff f' is"
  AlgebraicGeometry.Space.isImmersion_iff_of_cartesianMorphismOfThickenings

end
