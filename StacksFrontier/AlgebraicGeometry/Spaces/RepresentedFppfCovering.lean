module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# A covering of the site is an fppf covering of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `kᵢ : Vᵢ ⟶ U` be a family of
morphisms of the big fppf site of `S` whose underlying morphisms of schemes are flat, locally
of finite presentation, and jointly surjective. Then the represented family
`yoneda.map kᵢ : yoneda.obj Vᵢ ⟶ yoneda.obj U` is an fppf covering of algebraic spaces over
`S` in the sense of Stacks 03Y8, hence a covering family of the fppf precoverage of
Stacks 03YH.

## Main results

* `AlgebraicGeometry.Space.isFppfCovering_yoneda_map`: **Stacks 03Y8** for a represented
  family.
* `AlgebraicGeometry.Space.ofArrows_yoneda_mem_fppfPrecoverage`: the same family as a
  covering of `AlgebraicGeometry.Space.Topology.fppf.precoverage`.

## Implementation notes

The three clauses of `AlgebraicGeometry.Space.IsFppfCovering` come from three different
places.

* Algebraicity of the source and target is Stacks 025Z,
  `AlgebraicGeometry.isAlgebraicSpace_yoneda`.
* Flatness and local finite presentation of `yoneda.map kᵢ` as morphisms of algebraic spaces
  are `AlgebraicGeometry.Space.isFlat_yoneda_map` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_yoneda_map`; both are
  every-chart conditions (Stacks 03MJ (1)), and the chart squares are discharged by
  étale-local cancellation.
* Joint surjectivity is transported along the bijection
  `AlgebraicGeometry.Space.pointsEquivScheme` between the points of a represented
  presheaf and the points of the representing scheme (clause (1) of Stacks 03BX), using
  `AlgebraicGeometry.Space.pointsToScheme_pointsMap`, which says that bijection is
  natural in a morphism of the site.

The index type of the family may live in any universe, as for
`AlgebraicGeometry.Space.Topology.precoverage` itself.

## References

* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03Y8** for a represented family: a family of morphisms of the big fppf site of
`S` which is flat, locally of finite presentation and jointly surjective on the points of the
underlying schemes is an fppf covering of algebraic spaces over `S` after applying Yoneda. -/
theorem isFppfCovering_yoneda_map {I : Type v} {U : BigFppfOver B S hS}
    (V : I → BigFppfOver B S hS) (k : ∀ i, V i ⟶ U)
    (hflat : ∀ i, Flat ((BigFppfOver.toScheme B S hS).map (k i)))
    (hlfp : ∀ i, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (k i)))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj U, ∃ (i : I)
      (y : (BigFppfOver.toScheme B S hS).obj (V i)),
        (BigFppfOver.toScheme B S hS).map (k i) y = x) :
    IsFppfCovering B S hS (fun i => yoneda.obj (V i)) (fun i => yoneda.map (k i)) where
  target_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS U
  source_isAlgebraicSpace i := isAlgebraicSpace_yoneda B S hS (V i)
  flat i := isFlat_yoneda_map B S hS (k i) (hflat i)
  locallyOfFinitePresentation i := isLocallyOfFinitePresentation_yoneda_map B S hS (k i) (hlfp i)
  jointly_surjective := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨i, y, hy⟩ := hsurj (pointsToScheme B S hS U z)
    refine Set.mem_iUnion.2 ⟨i, (pointsEquivScheme B S hS (V i)).symm y, ?_⟩
    refine injective_pointsToScheme B S hS U ?_
    rw [pointsToScheme_pointsMap,
      show pointsToScheme B S hS (V i) ((pointsEquivScheme B S hS (V i)).symm y) = y
        from (pointsEquivScheme B S hS (V i)).apply_symm_apply y, hy]

/-- **Stacks 03YH** for a represented family: a flat, locally of finite presentation and
jointly surjective family of morphisms of the big fppf site of `S` is, after Yoneda, a
covering family of the fppf precoverage on the algebraic spaces over `S`. -/
theorem ofArrows_yoneda_mem_fppfPrecoverage {I : Type v} {U : BigFppfOver B S hS}
    (V : I → BigFppfOver B S hS) (k : ∀ i, V i ⟶ U)
    (hflat : ∀ i, Flat ((BigFppfOver.toScheme B S hS).map (k i)))
    (hlfp : ∀ i, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (k i)))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj U, ∃ (i : I)
      (y : (BigFppfOver.toScheme B S hS).obj (V i)),
        (BigFppfOver.toScheme B S hS).map (k i) y = x) :
    Presieve.ofArrows
        (fun i => (⟨yoneda.obj (V i), isAlgebraicSpace_yoneda B S hS (V i)⟩ :
          AlgebraicSpaces B S hS))
        (fun i => (ObjectProperty.homMk (yoneda.map (k i)) :
          (⟨yoneda.obj (V i), isAlgebraicSpace_yoneda B S hS (V i)⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) ∈
      (Topology.fppf.precoverage.{u, v} B S hS).coverings
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :=
  ⟨I, _, _, rfl, isAlgebraicSpace_yoneda B S hS U,
    fun i => isAlgebraicSpace_yoneda B S hS (V i),
    isFppfCovering_yoneda_map B S hS V k hflat hlfp hsurj⟩

end AlgebraicGeometry.Space

end
