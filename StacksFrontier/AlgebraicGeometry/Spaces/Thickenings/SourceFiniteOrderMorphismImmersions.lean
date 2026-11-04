module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SourceFiniteOrderMorphism

/-!
# Immersions, properness, finiteness and monomorphy across a cartesian morphism of thickenings

Let

```
X --f--→ Y
|        |
↓        ↓
X' -f'-→ Y'
```

be a commutative square of algebraic spaces over a scheme `S` in which `X ⊂ X'` and `Y ⊂ Y'`
are thickenings, `X ⊂ X'` is of finite order, and the square identifies `X` with `Y ×_{Y'} X'`;
that is, let it be an `AlgebraicGeometry.Space.CartesianSourceFiniteOrderMorphismOfThickenings`.
This file proves parts (1), (7), (8), (9) and (10) of Stacks 09ZZ: `f` is a closed immersion,
proper, finite, a monomorphism, respectively an immersion exactly when `f'` is.

In each case the implication from `f'` to `f` is base change along the cartesian square.

* **Properness** is separatedness, local finite type, quasi-compactness and universal
  closedness; the first, third and fourth are invariant under any morphism of thickenings by
  Stacks 09ZY, and the second is part (2).
* **Finiteness** is properness together with local quasi-finiteness, by Stacks 0A4X.
* **Closed immersions** are the universally closed, unramified, universally injective
  morphisms, by Stacks 05W8. Universal closedness is Stacks 09ZY, unramifiedness is part (6),
  and universal injectivity of `f'` follows from that of `X ⟶ Y ⟶ Y'` because `X ⟶ X'` is
  surjective.
* **Immersions** factor as a closed immersion into an open subspace `V ⊆ Y` by Stacks 04CE;
  `V` is the inverse image of an open subspace `V' ⊆ Y'` by Stacks 05ZP, `f'` factors through
  `V'`, and the square restricted to `V'` is again of the shape of this file, so part (1) applies
  to it.
* **Monomorphisms.** If `f` is a monomorphism, the first projection of `X' ×_{Y'} X'` sits in a
  cartesian morphism of thickenings whose *target* thickening is `X ⊆ X'`, which is of finite
  order by hypothesis, and whose morphism of smaller spaces is an isomorphism with inverse the
  diagonal. Part (1) for cartesian morphisms of thickenings with finite-order target thickening,
  `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.isClosedImmersion_iff`,
  makes the first projection a closed immersion, hence a monomorphism; being split by the
  diagonal it is an isomorphism, so `f'` is a monomorphism. The source's proof goes through the
  conormal sheaf of the diagonal and part (5) instead; the route here avoids the spaces analogue
  of Stacks 08S2.

## Main results

* `AlgebraicGeometry.Space.CartesianSourceFiniteOrderMorphismOfThickenings.isClosedImmersion_iff`:
  part (1).
* `AlgebraicGeometry.Space.CartesianSourceFiniteOrderMorphismOfThickenings.isProper_iff`:
  part (7).
* `AlgebraicGeometry.Space.CartesianSourceFiniteOrderMorphismOfThickenings.isFinite_iff`:
  part (8).
* `AlgebraicGeometry.Space.CartesianSourceFiniteOrderMorphismOfThickenings.mono_iff`: part (9).
* `AlgebraicGeometry.Space.CartesianSourceFiniteOrderMorphismOfThickenings.isImmersion_iff`:
  part (10).

## References

* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 05W8](https://stacks.math.columbia.edu/tag/05W8)
* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space.CartesianSourceFiniteOrderMorphismOfThickenings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The cartesian square of a cartesian morphism of thickenings with finite-order source,
read in the category of algebraic spaces over `S`. -/
theorem isPullback_algebraicSpaces (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    IsPullback (ObjectProperty.homMk M.X.ι : M.sourceSpace ⟶ M.X') M.smallHom M.ambientHom
      (ObjectProperty.homMk M.Y.ι : M.targetSpace ⟶ M.Y') :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
    M.cartesian.flip

/-! ### Properness and finiteness -/

/-- **Stacks 09ZZ, part (7).** In a cartesian morphism of thickenings of algebraic spaces whose
source thickening is of finite order, the map between the smaller spaces is proper exactly when
the map between the ambient spaces is. -/
@[stacks 09ZZ "part (7): f is proper iff f' is"]
theorem isProper_iff (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    IsProper B S hS M.f ↔ IsProper B S hS M.f' :=
  and_congr
    (isSeparated_iff_isSeparated_of_isThickening B S hS M.sourceThickening M.targetThickening
      M.morphism)
    (and_congr
      (and_congr M.isLocallyOfFiniteType_iff
        (isQuasiCompact_iff_isQuasiCompact_of_isThickening B S hS M.sourceThickening
          M.targetThickening M.morphism))
      (universallyClosed_iff_universallyClosed_of_isThickening B S hS M.sourceThickening
        M.targetThickening M.morphism))

/-- **Stacks 09ZZ, part (8).** In a cartesian morphism of thickenings of algebraic spaces whose
source thickening is of finite order, the map between the smaller spaces is finite exactly when
the map between the ambient spaces is. -/
@[stacks 09ZZ "part (8): f is finite iff f' is"]
theorem isFinite_iff (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    IsFinite B S hS M.f ↔ IsFinite B S hS M.f' :=
  ((isFinite_tfae B S hS M.sourceThickening.1.1 M.targetThickening.1.1 M.f).out 1 2).trans
    ((and_congr M.isProper_iff M.isLocallyQuasiFinite_iff).trans
      ((isFinite_tfae B S hS M.X'.2 M.Y'.2 M.f').out 1 2).symm)

/-! ### Closed immersions -/

/-- Stacks 05W8 for algebraic spaces: a closed immersion is a universally closed, unramified,
universally injective morphism, and conversely. -/
private theorem isClosedImmersion_iff_conditions (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsClosedImmersion B S hS f ↔ UniversallyClosed B S hS f ∧
      (IsUnramified B S hS f ∧ UniversallyInjective B S hS f) :=
  (closedImmersion_conditions_tfae B S hS hX hY f).out 1 3

/-- **Stacks 09ZZ, part (1).** In a cartesian morphism of thickenings of algebraic spaces whose
source thickening is of finite order, the map between the smaller spaces is a closed immersion
exactly when the map between the ambient spaces is.

By Stacks 05W8 a closed immersion is a universally closed, unramified, universally injective
morphism. Universal closedness transfers by Stacks 09ZY and unramifiedness by part (6); the
composite `X ⟶ Y ⟶ Y'` is universally injective, it equals `X ⟶ X' ⟶ Y'`, and `X ⟶ X'` is
surjective, so `f'` is universally injective. -/
@[stacks 09ZZ "part (1): f is a closed immersion iff f' is"]
theorem isClosedImmersion_iff (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    IsClosedImmersion B S hS M.f ↔ IsClosedImmersion B S hS M.f' := by
  refine ⟨fun hf => ?_, fun hf' =>
    isClosedImmersion_of_isPullback B S hS M.isPullback_algebraicSpaces hf'⟩
  obtain ⟨huc, hunram, huinj⟩ := (isClosedImmersion_iff_conditions B S hS
    M.sourceThickening.1.1 M.targetThickening.1.1 M.f).mp hf
  refine (isClosedImmersion_iff_conditions B S hS M.X'.2 M.Y'.2 M.f').mpr
    ⟨(universallyClosed_iff_universallyClosed_of_isThickening B S hS
      M.sourceThickening M.targetThickening M.morphism).mp huc, M.isUnramified_iff.mp hunram, ?_⟩
  have hcomp := universallyInjective_comp B S hS M.targetThickening.1.1 M.Y'.2 M.f M.Y.ι huinj
    ((isClosedImmersion_iff_conditions B S hS M.targetThickening.1.1 M.Y'.2 M.Y.ι).mp
      M.targetThickening.1.2).2.2
  rw [show M.f ≫ M.Y.ι = M.X.ι ≫ M.f' from M.morphism.w] at hcomp
  exact universallyInjective_of_isSurjective_comp B S hS M.sourceThickening.1.1 M.X'.2 M.Y'.2
    M.X.ι M.f' hcomp M.sourceThickening.2

/-! ### Immersions -/

/-- If the morphism `f` of smaller spaces factors as a closed immersion into an open subspace
`V ⊆ Y`, then the ambient morphism `f'` is an immersion.

The open subspace `V` is the inverse image of a unique open subspace `V' ⊆ Y'`, by Stacks 05ZP,
and `f'` factors through `V'` because the two thickenings are bijective on points. Restricting
the square to `V'` gives a cartesian morphism of thickenings with the same finite-order source
thickening `X ⊆ X'`, so part (1) makes `X' ⟶ V'` a closed immersion. -/
theorem isImmersion_right_of_isClosedImmersion_into_openSubspace
    (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS)
    (V : Subfunctor M.Y.toFunctor) (hV : IsOpenSubspace B S hS V)
    (c : M.X.toFunctor ⟶ V.toFunctor) (hc : IsClosedImmersion B S hS c)
    (hcι : c ≫ V.ι = M.f) : IsImmersion B S hS M.f' := by
  obtain ⟨V', ⟨hV'open, hV'pre⟩, -⟩ :=
    existsUnique_isOpenSubspace_preimage_eq_of_isThickening B S hS M.targetThickening V hV
  subst hV'pre
  let V'sp : AlgebraicSpaces B S hS := ⟨V'.toFunctor, hV'open.1⟩
  let W : Subfunctor V'sp.1 := M.Y.preimage V'.ι
  have hA : IsPullback (V'.fromPreimage M.Y.ι) (V'.preimage M.Y.ι).ι V'.ι M.Y.ι :=
    Subfunctor.isPullback_preimage M.Y.ι V'
  have hB : IsPullback (M.Y.fromPreimage V'.ι) W.ι M.Y.ι V'.ι :=
    Subfunctor.isPullback_preimage V'.ι M.Y
  -- The two descriptions of `V ∩ V'` as a fibre product agree.
  let e : (V'.preimage M.Y.ι).toFunctor ≅ W.toFunctor := hA.flip.isoIsPullback _ _ hB
  have hmaps : (c ≫ V'.fromPreimage M.Y.ι) ≫ V'.ι = M.X.ι ≫ M.f' := by
    rw [Category.assoc, hA.w, ← Category.assoc, hcι]
    exact M.morphism.w
  -- The ambient morphism factors through `V'`, the thickenings being bijective on points.
  have hrange : Set.range (pointsMap B S hS M.X'.1 M.f') ⊆
      Set.range (pointsMap B S hS V'.toFunctor V'.ι) := by
    rintro y' ⟨x', rfl⟩
    obtain ⟨x, rfl⟩ := M.sourceThickening.2 x'
    exact ⟨pointsMap B S hS M.X.toFunctor (c ≫ V'.fromPreimage M.Y.ι) x,
      (congrFun (pointsMap_comp B S hS M.X.toFunctor (c ≫ V'.fromPreimage M.Y.ι) V'.ι) x).symm.trans
        (hmaps ▸ congrFun (pointsMap_comp B S hS M.X.toFunctor M.X.ι M.f') x)⟩
  obtain ⟨g', hg'⟩ :=
    (factorsThrough_openSubspace_iff_points B S hS M.Y'.2 M.X'.2 V' hV'open M.f').2 hrange
  have hw : (c ≫ e.hom) ≫ W.ι = M.X.ι ≫ g' := by
    refine (cancel_mono V'.ι).mp ?_
    simpa only [Category.assoc, e, hA.flip.isoIsPullback_hom_snd_assoc _ _ hB, hg'] using hmaps
  have hs : IsPullback ((c ≫ e.hom) ≫ M.Y.fromPreimage V'.ι) M.X.ι M.Y.ι (g' ≫ V'.ι) := by
    rw [show (c ≫ e.hom) ≫ M.Y.fromPreimage V'.ι = M.f from by
      rw [Category.assoc, hA.flip.isoIsPullback_hom_fst _ _ hB, hcι], hg']
    exact M.cartesian
  let N : CartesianSourceFiniteOrderMorphismOfThickenings B S hS :=
    { X' := M.X'
      Y' := V'sp
      X := M.X
      Y := W
      sourceFiniteOrder := M.sourceFiniteOrder
      targetThickening := isThickening_preimage B S hS M.Y
        (ObjectProperty.homMk V'.ι : V'sp ⟶ M.Y') M.targetThickening
      morphism := Arrow.homMk (c ≫ e.hom) g' hw
      cartesian := IsPullback.of_right hs hw hB }
  rw [← hg']
  have _ := isImmersion_isStableUnderComposition B S hS
  exact MorphismProperty.comp_mem _ _ _
    (isImmersion_of_isClosedImmersion B S hS (N.isClosedImmersion_iff.mp
      (MorphismProperty.RespectsIso.postcomp _ e.hom c hc)))
    (isImmersion_of_isOpenImmersion B S hS hV'open.2)

/-- **Stacks 09ZZ, part (10).** In a cartesian morphism of thickenings of algebraic spaces whose
source thickening is of finite order, the map between the smaller spaces is an immersion exactly
when the map between the ambient spaces is.

Stacks 04CE factors the immersion `f` as a closed immersion into an open subspace of `Y`, and
`isImmersion_right_of_isClosedImmersion_into_openSubspace` turns that into an immersion
factorisation of `f'`. -/
@[stacks 09ZZ "part (10): f is an immersion iff f' is"]
theorem isImmersion_iff (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    IsImmersion B S hS M.f ↔ IsImmersion B S hS M.f' := by
  refine ⟨fun hf => ?_, fun hf' =>
    isImmersion_of_isPullback B S hS M.isPullback_algebraicSpaces hf'⟩
  obtain ⟨c, hc, hcι⟩ := exists_isClosedImmersion_comp_ι_boundaryComplement B S hS
    M.targetThickening.1.1 M.sourceThickening.1.1 M.f hf
  exact M.isImmersion_right_of_isClosedImmersion_into_openSubspace _
    (isOpenSubspace_boundaryComplement B S hS M.targetThickening.1.1
      (isLocallyClosed_range_pointsMap_of_isImmersion B S hS M.targetThickening.1.1 M.f hf))
    c hc hcι

/-! ### Monomorphisms -/

/-- If `f` is a monomorphism, then so is the first projection of `X' ×_{Y'} X'`.

Pulling `X ⊆ X'` back along the first projection gives a cartesian morphism of thickenings
whose target thickening is `X ⊆ X'`, of finite order by hypothesis, and whose morphism of
smaller spaces is the canonical map out of the inverse image. Monomorphy of `f` makes that map
an isomorphism, with inverse the diagonal of `f'`: a section `(a, b)` of the inverse image has
`a` in `X`, hence `f'(b) = f'(a)` in `Y`, hence `b` in `X` by cartesianness, and then
`f(a) = f(b)` forces `a = b`. Part (1) in the finite-order-target case transfers the closed
immersion property to the first projection. -/
theorem mono_pullback_fst_of_mono (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS)
    (hf : Mono M.f) : Mono (pullback.fst M.f' M.f') := by
  let P : AlgebraicSpaces B S hS :=
    ⟨pullback M.f' M.f', isAlgebraicSpace_pullback B S hS M.f' M.f' M.X'.2 M.X'.2 M.Y'.2⟩
  let p₁ : P ⟶ M.X' := ObjectProperty.homMk (pullback.fst M.f' M.f')
  let Z : Subfunctor P.1 := M.X.preimage (pullback.fst M.f' M.f')
  let N : CartesianFiniteOrderMorphismOfThickenings B S hS :=
    { X' := P
      Y' := M.X'
      X := Z
      Y := M.X
      sourceThickening :=
        (isFiniteOrderThickening_preimage B S hS M.X p₁ M.sourceFiniteOrder).choose_spec.1
      targetFiniteOrder := M.sourceFiniteOrder
      morphism := Arrow.homMk (M.X.fromPreimage (pullback.fst M.f' M.f'))
        (pullback.fst M.f' M.f') (Subfunctor.fromPreimage_ι M.X _)
      cartesian := Subfunctor.isPullback_preimage (pullback.fst M.f' M.f') M.X }
  -- The diagonal of `f'` on `X` lands in `Z`.
  have hrange : Subfunctor.range (M.X.ι ≫ pullback.diagonal M.f') ≤ Z := by
    rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp,
      show (M.X.ι ≫ pullback.diagonal M.f') ≫ pullback.fst M.f' M.f' = M.X.ι by simp]
    exact le_of_eq (Subfunctor.range_ι M.X)
  let δ : M.X.toFunctor ⟶ Z.toFunctor := Subfunctor.lift (M.X.ι ≫ pullback.diagonal M.f') hrange
  have hδ : δ ≫ Z.ι = M.X.ι ≫ pullback.diagonal M.f' := Subfunctor.lift_ι _ _
  -- On `Z` the two projections agree.
  have hfstsnd : Z.ι ≫ pullback.fst M.f' M.f' = Z.ι ≫ pullback.snd M.f' M.f' := by
    have hcond : (M.X.fromPreimage (pullback.fst M.f' M.f') ≫ M.f) ≫ M.Y.ι =
        (Z.ι ≫ pullback.snd M.f' M.f') ≫ M.f' := by
      rw [Category.assoc, Category.assoc, show M.f ≫ M.Y.ι = M.X.ι ≫ M.f' from M.morphism.w,
        Subfunctor.fromPreimage_ι_assoc, pullback.condition]
    rw [← M.cartesian.lift_snd _ _ hcond, (cancel_mono M.f).mp (M.cartesian.lift_fst _ _ hcond),
      Subfunctor.fromPreimage_ι]
  -- The morphism of smaller spaces of `N` is an isomorphism, with inverse `δ`.
  have hiso : IsIso (M.X.fromPreimage (pullback.fst M.f' M.f')) := by
    refine ⟨δ, ?_, ?_⟩
    · refine (cancel_mono Z.ι).mp ?_
      rw [Category.assoc, hδ, ← Category.assoc, Subfunctor.fromPreimage_ι, Category.id_comp]
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
        rfl
      · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id]
        exact hfstsnd.symm ▸ rfl
    · refine (cancel_mono M.X.ι).mp ?_
      rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, hδ]
      simp
  exact mono_of_isClosedImmersion B S hS _ (N.isClosedImmersion_iff.mp
    (isClosedImmersion_of_isIso B S hS (M.X.fromPreimage (pullback.fst M.f' M.f'))))

/-- **Stacks 09ZZ, part (9).** In a cartesian morphism of thickenings of algebraic spaces whose
source thickening is of finite order, the map between the smaller spaces is a monomorphism
exactly when the map between the ambient spaces is.

If `f` is a monomorphism, the first projection of `X' ×_{Y'} X'` is a monomorphism by
`mono_pullback_fst_of_mono` and a split epimorphism retracted by the diagonal, hence an
isomorphism, so `f'` is a monomorphism. The converse is base change. -/
@[stacks 09ZZ "part (9): f is a monomorphism iff f' is"]
theorem mono_iff (M : CartesianSourceFiniteOrderMorphismOfThickenings B S hS) :
    Mono M.f ↔ Mono M.f' := by
  refine ⟨fun hf => ?_, fun _ => M.cartesian.mono_fst_of_mono⟩
  have := M.mono_pullback_fst_of_mono hf
  have : IsSplitEpi (pullback.fst M.f' M.f') :=
    IsSplitEpi.mk' ⟨pullback.diagonal M.f', pullback.diagonal_fst M.f'⟩
  have := isIso_of_mono_of_isSplitEpi (pullback.fst M.f' M.f')
  exact IsKernelPair.mono_of_isIso_fst (IsPullback.of_hasPullback M.f' M.f')

end AlgebraicGeometry.Space.CartesianSourceFiniteOrderMorphismOfThickenings

end
