module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartFactorisationLargeField
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreRegularSequenceGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreSliceFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover

/-!
# The flatness half of Stacks 06LW

Let `g : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` in a big fppf site which is
flat and locally of finite presentation, let `f₁, …, f_r ∈ Γ(X, 𝒪_X)`, let `Spec k ⟶ Y` be a
field-valued point of the target, let `F = X ×_Y Spec k` be the fibre and let `z` be a geometric
point of `F` at which the images of the `f_i` in the étale local ring `𝒪_{F, z̄}` form a regular
sequence.  This file proves that after replacing `X` by an open subspace containing the image of
`z` the closed subspace `V(f₁, …, f_r)` is flat over `Y`, which is the flatness half of the
conclusion of Stacks 06LW.

## Main results

* `exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_geometricFiber`:
  **the flatness half of Stacks 06LW.**

## Implementation notes

Steps three to five of the source's proof are
`exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_fiber_factorThroughChart`, which
concludes exactly this for a fibre over a field whose spectrum maps to `Y` *through a scheme
chart* `q : V ⟶ Y`, carrying that factorisation as its only extra hypothesis.  What is
performed here are the source's first two steps, which produce the factorisation.

The field is enlarged by `AlgebraicGeometry.Space.exists_geometricPoint_factorThroughChart`: the
given point of `|F|` is the image of a geometric point `z'` whose field spectrum `Spec k'`
carries both an extension `c : Spec k' ⟶ Spec k` and a morphism `ρ : Spec k' ⟶ V` with
`ρ ≫ q = c ≫ (Spec k ⟶ Y)`.  The fibre over `Spec k'` is the base change
`F' = F ×_{Spec k} Spec k'`, an algebraic space by
`AlgebraicGeometry.isAlgebraicSpace_pullback`, and it is the fibre of `g` over `Spec k' ⟶ Y` by
pasting the two cartesian squares, which is where the factorisation enters: the bottom edge of
the pasted square is `c ≫ (Spec k ⟶ Y)`, and that is `ρ ≫ q`.  The chart of `Y` is produced
from `Y` itself, so it is not part of the statement.

The regularity hypothesis travels to `F'` in two moves.  Across the change of geometric point
inside `F` — the enlarged point `z'` and the given point `z` share an image in `|F|` but are not
comparable — it travels through a common dominating point
(`AlgebraicGeometry.Space.GeometricPoint.exists_common_extension`) by
`AlgebraicGeometry.Space.forall_isRegular_etaleLocalRingMap_germ_iff_of_dominates`, used once in
each direction.  Across the projection `F' ⟶ F` it travels by
`AlgebraicGeometry.Space.isRegular_map_etaleLocalRingMap_comp_iff_of_isFlatAt`, whose flatness
hypothesis holds because the projection is a base change of `Spec k' ⟶ Spec k`
(`AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange`, Stacks 03MO), and a morphism to the
spectrum of a field is flat (`AlgebraicGeometry.flat_of_isField_stalk`).

The geometric point of `F'` above `z'` is
`AlgebraicGeometry.Space.exists_geometricPoint_pullback_fst_eq`, and it is produced as an equality
of geometric points rather than of their images: the étale local ring depends on the point itself,
so only an equality of points makes the comparison with `z'` a domination — by the identity — and
lets the previous paragraph's transport apply.  The germs the two transports move are identified
by `AlgebraicGeometry.Space.etaleLocalRingMap_comp`, inside the second lemma named above.

The two conversions between `List.ofFn` of a composite and `List.map` of a `List.ofFn` are
written as equalities of lists and used through `congrArg`, not as rewrites: the geometric point
of `X` under `z''` is the image of the geometric point of `F` under `z''` only up to definitional
unfolding of the functoriality of geometric points, and a rewrite under the type of a germ at
that point is not type correct where a definitional comparison is.

## References

* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. These are `local` (not `private`) instances, with names unique
to this file. -/
local instance (priority := high) hasPullbacks_presheaf_fibreSliceFlatnessEnlargement :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_fibreSliceFlatnessEnlargement
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_fibreSliceFlatnessEnlargement B S hS).has_limit _

/-- **Stacks 06LW, the flatness half of the conclusion.**  Let `g : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is flat and locally of finite presentation, let
`f₁, …, f_r ∈ Γ(X, 𝒪_X)`, let `Spec k ⟶ Y` be a field-valued point of the target, let
`ξ : F ⟶ X` and `π : F ⟶ Spec k` present `F` as the fibre `X ×_Y Spec k` and let `z` be a
geometric point of `F` at which the images of the `f_i` in the étale local ring `𝒪_{F, z̄}` form
a regular sequence.

Then there is an open subspace `W ⊆ X` containing the image of `z` such that
`V(f₁, …, f_r) ∩ W ⟶ Y` is flat.

The hypothesis is taken in the form the source's conclusion is used in — quantified over the
small étale neighbourhoods of the image of `z` in `X` — which is the same condition for one
neighbourhood as for all, the image of a germ of a global function under the comparison
homomorphism of Stacks 04NG not depending on the neighbourhood.  It is the form in which
Stacks 06MD states it, `AlgebraicGeometry.Stack.FibreIsRegularSequenceAt`. -/
@[stacks 06LW "the flatness half of the conclusion"]
theorem exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_geometricFiber
    (X Y F : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1)
    (hgflat : IsFlat B S hS g) (hglfp : IsLocallyOfFinitePresentation B S hS g)
    {r : ℕ} (fs : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (t : yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)) ⟶ Y.1)
    (ξ : F ⟶ X) {π : F.1 ⟶ yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))}
    (sq : IsPullback ξ.hom π g t)
    (z : GeometricPoint B S hS F.1)
    (hreg : ∀ Nx : SmallEtaleNeighborhood (geometricPointMap ξ.hom z),
      RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F.1 z)
        (List.ofFn fun i : Fin r => etaleLocalRingMap F.2 ξ.hom z
          (etaleLocalRingGerm B S hS X.1 (geometricPointMap ξ.hom z) (op Nx)
            ((fs i).eval (op Nx.chart))))) :
    ∃ (W : Subfunctor X.1) (_ : IsOpenSubspace B S hS W),
      pointsMap B S hS F.1 ξ.hom z.image ∈
          Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        IsFlat B S hS (((vanishingSubfunctor B S hS X fs).preimage W.ι).ι ≫ W.ι ≫ g) := by
  classical
  obtain ⟨V, q, hqS, hqE⟩ := Y.2.exists_atlas
  obtain ⟨z', c, ρ, hπc, hρ, himg⟩ := exists_geometricPoint_factorThroughChart B S hS V q hqS
    hk b t π z.image
  have hF' : IsAlgebraicSpace B S hS (pullback π (yoneda.map c)) :=
    isAlgebraicSpace_pullback B S hS π (yoneda.map c) F.2
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
  obtain ⟨z'', hz''⟩ := exists_geometricPoint_pullback_fst_eq B S hS π z' c hπc
  have hflatc : IsFlat B S hS (yoneda.map c) :=
    isFlat_yoneda_map B S hS c (flat_of_isField_stalk _ fun _ => isField_stalk_Spec_field k _)
  have _ := isFlat_isStableUnderBaseChange B S hS
  have hflatfst : IsFlat B S hS (pullback.fst π (yoneda.map c)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃A A' : AlgebraicSpaces B S hS⦄ (m : A ⟶ A') => IsFlat B S hS m.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk (X := F)
          (Y := (⟨yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)),
            isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS)) π)
        (ObjectProperty.homMk (X := (⟨yoneda.obj z'.val.siteObject,
            isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS))
          (Y := (⟨yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)),
            isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS)) (yoneda.map c))).flip
      hflatc
  have hflatat : IsFlatAt B S hS (pullback.fst π (yoneda.map c)) z''.image :=
    (isFlat_iff_forall_isFlatAt B S hS _).1 hflatfst _
  obtain ⟨rz, ⟨dz, hdz⟩, ⟨dz', hdz'⟩⟩ := GeometricPoint.exists_common_extension z z' rfl himg
  have hregz' := (forall_isRegular_etaleLocalRingMap_germ_iff_of_dominates B S hS ξ fs dz'
    hdz').2 ((forall_isRegular_etaleLocalRingMap_germ_iff_of_dominates B S hS ξ fs dz hdz).1 hreg)
  have hdomzz : FieldValuedPoint.Dominates B S hS F.1
      (geometricPointMap (pullback.fst π (yoneda.map c)) z'').val z'.val := by
    rw [hz'']
    exact FieldValuedPoint.dominates_refl B S hS F.1 z'.val
  obtain ⟨dzz, hdzz⟩ := hdomzz
  have hregzz := (forall_isRegular_etaleLocalRingMap_germ_iff_of_dominates B S hS ξ fs dzz
    hdzz).1 hregz'
  have hregF' : ∀ Nx : SmallEtaleNeighborhood
      (geometricPointMap (pullback.fst π (yoneda.map c) ≫ ξ.hom) z''),
      RingTheory.Sequence.IsRegular
        (etaleLocalRing B S hS (pullback π (yoneda.map c)) z'')
        (List.ofFn fun i : Fin r =>
          etaleLocalRingMap hF' (pullback.fst π (yoneda.map c) ≫ ξ.hom) z''
            (etaleLocalRingGerm B S hS X.1
              (geometricPointMap (pullback.fst π (yoneda.map c) ≫ ξ.hom) z'') (op Nx)
              ((fs i).eval (op Nx.chart)))) := by
    intro Nx
    have e1 : (List.ofFn fun i : Fin r => etaleLocalRingGerm B S hS X.1
          (geometricPointMap (pullback.fst π (yoneda.map c) ≫ ξ.hom) z'') (op Nx)
          ((fs i).eval (op Nx.chart))).map
        (etaleLocalRingMap hF' (pullback.fst π (yoneda.map c) ≫ ξ.hom) z'') =
        List.ofFn fun i : Fin r =>
          etaleLocalRingMap hF' (pullback.fst π (yoneda.map c) ≫ ξ.hom) z''
            (etaleLocalRingGerm B S hS X.1
              (geometricPointMap (pullback.fst π (yoneda.map c) ≫ ξ.hom) z'') (op Nx)
              ((fs i).eval (op Nx.chart))) := List.map_ofFn
    have e2 : (List.ofFn fun i : Fin r => etaleLocalRingGerm B S hS X.1
          (geometricPointMap ξ.hom (geometricPointMap (pullback.fst π (yoneda.map c)) z''))
          (op Nx) ((fs i).eval (op Nx.chart))).map
        (etaleLocalRingMap F.2 ξ.hom
          (geometricPointMap (pullback.fst π (yoneda.map c)) z'')) =
        List.ofFn fun i : Fin r => etaleLocalRingMap F.2 ξ.hom
          (geometricPointMap (pullback.fst π (yoneda.map c)) z'')
          (etaleLocalRingGerm B S hS X.1
            (geometricPointMap ξ.hom (geometricPointMap (pullback.fst π (yoneda.map c)) z''))
            (op Nx) ((fs i).eval (op Nx.chart))) := List.map_ofFn
    refine (iff_of_eq (congrArg (RingTheory.Sequence.IsRegular
      (etaleLocalRing B S hS (pullback π (yoneda.map c)) z'')) e1)).1 ?_
    refine (isRegular_map_etaleLocalRingMap_comp_iff_of_isFlatAt B S hS hF' F.2
      (pullback.fst π (yoneda.map c)) ξ.hom z'' hflatat _).2 ?_
    exact (iff_of_eq (congrArg (RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F.1
      (geometricPointMap (pullback.fst π (yoneda.map c)) z''))) e2)).2 (hregzz Nx)
  have hsq' : IsPullback (pullback.fst π (yoneda.map c) ≫ ξ.hom)
      (pullback.snd π (yoneda.map c)) g (yoneda.map ρ ≫ q) := by
    rw [hρ]
    exact (IsPullback.of_hasPullback π (yoneda.map c)).paste_horiz sq
  obtain ⟨W, hW, hmem, hflat⟩ :=
    exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_fiber_factorThroughChart
      B S hS X Y (⟨pullback π (yoneda.map c), hF'⟩ : AlgebraicSpaces B S hS) g hgflat hglfp fs
      V q hqS hqE z'.val.contained z'.val.toBase ρ
      (ObjectProperty.homMk (pullback.fst π (yoneda.map c) ≫ ξ.hom)) hsq' z'' hregF'
  refine ⟨W, hW, ?_, hflat⟩
  have hpt : pointsMap B S hS (pullback π (yoneda.map c))
      (pullback.fst π (yoneda.map c) ≫ ξ.hom) z''.image =
      pointsMap B S hS F.1 ξ.hom z.image := by
    rw [pointsMap_comp]
    exact congrArg (pointsMap B S hS F.1 ξ.hom)
      (((geometricPointMap_image (pullback.fst π (yoneda.map c)) z'').symm.trans
        (congrArg GeometricPoint.image hz'')).trans himg)
  rwa [← hpt]

end AlgebraicGeometry.Space

end
