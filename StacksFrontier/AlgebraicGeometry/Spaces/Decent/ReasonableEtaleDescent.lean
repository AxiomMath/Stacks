module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable

/-!
# Reasonableness descends along a quasi-compact surjection

Stacks 03L2 says that property `(β)`, decency and reasonableness all pass from the source of a
quasi-compact étale morphism which is surjective on points to its target. This file proves the
case of reasonableness: the degree bound on the fibres of an affine étale chart of the target
is the one reasonableness of the source provides for an affine étale chart of the base change
of that chart.

## Main results

* `AlgebraicGeometry.Space.isReasonableSpace_of_surjective_isQuasiCompact`: **Stacks 03L2** for
  reasonableness.

## Implementation notes

The argument is the one of the source. Let `φ : h_V ⟶ Y` be an étale chart of the target by an
affine scheme. Its base change `P = h_V ×_Y X` is a quasi-compact algebraic space, so Stacks
03H6 gives an affine scheme `W` and a surjective étale `w : h_W ⟶ P`; the composite
`ψ : h_W ⟶ X` with the projection to `X` is an étale chart of the source by an affine scheme,
and reasonableness of the source bounds the degrees of its fibres by some `n`. That same `n`
bounds the degrees of the fibres of `φ`.

Indeed, let `ξ : h_A ⟶ Y` be a field-valued point of the target, `A` having the spectrum of `k`
for underlying scheme. Surjectivity on points makes the algebraic space `h_A ×_Y X` nonempty,
so it has a field-valued point in the sense of Stacks 03BU: a field `L`, an object `D` of the
site with `Spec L` for underlying scheme, a morphism `τ : D ⟶ A` and a morphism
`β : h_D ⟶ X` over `ξ`. The fibre of `ψ` over `β` is then a scheme finite locally free of some
rank `r ≤ n` over `D`, and it maps to the fibre of `φ` over `τ ≫ ξ` by a base change of `w`,
hence by a surjective flat morphism. So Stacks 03JB bounds the degrees of the fibres of that
second fibre by `r`, which over a field spectrum is a rank, and the rank descends from `D` to
`A` because `Spec L ⟶ Spec k` is a one-element fpqc covering
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_isPullback_of_isoFieldSpec`).

The two fibres of `φ` and the comparison morphisms between the three fibres come from the
representability of `φ`, which holds because the target has a representable diagonal. The
projection `P ⟶ h_V` is not used to bound anything; it only supplies the morphism from the
fibre of `ψ` to `h_V` which the universal property of the fibre of `φ` consumes.

Étaleness of the morphism, which Stacks 03L2 also assumes, is not used: quasi-compactness
makes the base change `P` quasi-compact, and surjectivity on points produces the field-valued
point of `h_A ×_Y X`. Surjectivity of `|X| → |Y|` is surjectivity of the induced map on
equivalence classes of field-valued points, which is the meaning of surjectivity of `|f|` by
Stacks 03H5.

## References

* [Stacks Project, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03JB](https://stacks.math.columbia.edu/tag/03JB)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03JT](https://stacks.math.columbia.edu/tag/03JT)
* [Stacks Project, Tag 03L2](https://stacks.math.columbia.edu/tag/03L2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03L2, reasonable.** Let `f` be a quasi-compact morphism of algebraic spaces over
`S` which is surjective on points. If its source is reasonable, then so is its target.

An affine étale chart of the target is dominated, after base change along `f`, by an affine
étale chart of the source, and the bound reasonableness of the source gives the latter bounds
the degrees of the fibres of the former. Étaleness of `f`, which Stacks 03L2 also assumes, is
not used. -/
@[stacks 03L2 "reasonable"]
theorem isReasonableSpace_of_surjective_isQuasiCompact
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsQuasiCompact B S hS f)
    (hsurj : Function.Surjective (pointsMap B S hS X f))
    (hXr : IsReasonableSpace B S hS X) :
    IsReasonableSpace B S hS Y := by
  classical
  have hmul := isMultiplicative_presheaf_etale B S hS
  intro V hVaff φ hφet
  have hValg : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  -- The base change of `f` along the chart is a quasi-compact algebraic space.
  have hPalg : IsAlgebraicSpace B S hS (pullback φ f) :=
    isAlgebraicSpace_pullback B S hS φ f hValg hX hY
  have hPqc : IsQuasiCompactSpace B S hS (pullback φ f) :=
    hf (yoneda.obj V) hValg (isQuasiCompactSpace_yoneda_of_isAffine B S hS V hVaff) φ
  obtain ⟨W, w, hWaff, hwsurj, hwet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hPalg).mp hPqc
  -- It carries an affine étale chart of the source, whose fibres reasonableness bounds.
  have hsndet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd φ f) :=
    presheaf_of_isPullback B S hS (IsPullback.of_hasPullback φ f) hφet
  obtain ⟨n, hn⟩ := hXr W hWaff (w ≫ pullback.snd φ f)
    (MorphismProperty.comp_mem _ _ _ (presheaf_etale_of_isEtale B S hS hwet) hsndet)
  refine ⟨n, fun k _ A hA ξ => ?_⟩
  have hAalg : IsAlgebraicSpace B S hS (yoneda.obj A) := isAlgebraicSpace_yoneda B S hS A
  have hrep : yoneda.relativelyRepresentable φ :=
    Functor.relativelyRepresentable.of_diag hY.diagonal_representable φ
  have hfib : IsPullback (yoneda.map (hrep.fst' ξ)) (yoneda.map (hrep.snd ξ)) φ ξ :=
    hrep.isPullback' ξ
  -- A field-valued point of the fibre of `f` over `ξ`, which exists by surjectivity.
  obtain ⟨z, -⟩ := surjective_pointsMap_of_isPullback B S hS
    (IsPullback.of_hasPullback ξ f).flip hsurj
    ((pointsEquivScheme B S hS A).symm (hA.inv.base (Nonempty.some inferInstance)))
  obtain ⟨c, -⟩ := Quot.exists_rep z
  set γ : yoneda.obj c.siteObject ⟶ pullback ξ f :=
    fieldMorphism B S hS (pullback ξ f) c with hγ
  set τ : c.siteObject ⟶ A := yoneda.preimage (γ ≫ pullback.fst ξ f) with hτ
  set β : yoneda.obj c.siteObject ⟶ X := γ ≫ pullback.snd ξ f with hβ
  have hτβ : β ≫ f = yoneda.map τ ≫ ξ := by
    rw [hτ, yoneda.map_preimage, hβ, Category.assoc, Category.assoc,
      pullback.condition (f := ξ) (g := f)]
  have hD : (BigFppfOver.toScheme B S hS).obj c.siteObject ≅
      Spec (CommRingCat.of c.carrier) := Iso.refl _
  -- The fibre of the chart of the source over that point, finite of rank at most `n`.
  obtain ⟨W₀, pW, iW, r, hrn, hrank, hpullW⟩ := hn c.carrier c.siteObject hD β
  -- The fibre of the chart of the target over the extended point.
  have hfib' : IsPullback (yoneda.map (hrep.fst' (yoneda.map τ ≫ ξ)))
      (yoneda.map (hrep.snd (yoneda.map τ ≫ ξ))) φ (yoneda.map τ ≫ ξ) :=
    hrep.isPullback' _
  -- The comparison from the fibre of `ψ`, a base change of `w`, hence surjective and flat.
  have hcond : (iW ≫ w ≫ pullback.fst φ f) ≫ φ =
      yoneda.map pW ≫ (yoneda.map τ ≫ ξ) := by
    simp only [Category.assoc]
    rw [pullback.condition (f := φ) (g := f), reassoc_of% hpullW.w, hτβ]
  set j := hrep.lift' (yoneda.preimage (iW ≫ w ≫ pullback.fst φ f)) pW
    (by rwa [yoneda.map_preimage]) with hj
  have hjfst : yoneda.map (j ≫ hrep.fst' (yoneda.map τ ≫ ξ)) =
      iW ≫ w ≫ pullback.fst φ f := by
    rw [hj, Functor.congr_map yoneda (hrep.lift'_fst _ _ _), yoneda.map_preimage]
  have hjsnd : j ≫ hrep.snd (yoneda.map τ ≫ ξ) = pW := hrep.lift'_snd _ _ _
  -- The fibre of the chart of the target sits over `P`, cartesianly.
  set m : yoneda.obj (hrep.pullback (yoneda.map τ ≫ ξ)) ⟶ pullback φ f :=
    pullback.lift (yoneda.map (hrep.fst' (yoneda.map τ ≫ ξ)))
      (yoneda.map (hrep.snd (yoneda.map τ ≫ ξ)) ≫ β)
      (by rw [hfib'.w, Category.assoc, hτβ]) with hm
  have hm₁ : m ≫ pullback.fst φ f = yoneda.map (hrep.fst' (yoneda.map τ ≫ ξ)) :=
    pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd φ f =
      yoneda.map (hrep.snd (yoneda.map τ ≫ ξ)) ≫ β := pullback.lift_snd _ _ _
  have hmsq : IsPullback m (yoneda.map (hrep.snd (yoneda.map τ ≫ ξ)))
      (pullback.snd φ f) β :=
    (IsPullback.of_bot (by rw [hm₁, hτβ]; exact hfib'.flip) hm₂.symm
      (IsPullback.of_hasPullback φ f).flip).flip
  have hjw : iW ≫ w = yoneda.map j ≫ m := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [hm₁, ← hjfst, Functor.map_comp]
    · simp only [Category.assoc]
      rw [hm₂, hpullW.w, ← hjsnd, Functor.map_comp, Category.assoc]
  have hjsq : IsPullback iW (yoneda.map j) w m :=
    IsPullback.of_bot (by rwa [← Functor.map_comp, hjsnd]) hjw hmsq
  have hjP : ∀ Q : MorphismProperty Scheme.{u}, Q.IsStableUnderBaseChange →
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf w →
      Q ((BigFppfOver.toScheme B S hS).map j) := fun Q _ hQ =>
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS Q j).mp
      (presheaf_of_isPullback B S hS hjsq hQ)
  have _ : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map j) :=
    hjP _ inferInstance hwsurj
  have _ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map j) :=
    hjP _ inferInstance (presheaf_etale_of_isEtale B S hS hwet)
  have _ : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map j) := inferInstance
  -- The bound descends along the comparison, and over a field spectrum it is a rank.
  have _ : IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map pW) r := hrank
  have hbd : BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map j ≫
      (BigFppfOver.toScheme B S hS).map (hrep.snd (yoneda.map τ ≫ ξ))) (r : ℤ) := by
    rw [← Functor.map_comp, hjsnd]
    exact boundsFiberDegrees_of_isFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map pW) r
  obtain ⟨r', hr', hrank'⟩ := exists_rank_le_of_boundsFiberDegrees_of_specTarget
    ((BigFppfOver.toScheme B S hS).map (hrep.snd (yoneda.map τ ≫ ξ)))
    (boundsFiberDegrees_of_comp_of_surjective_flat _ _ (r : ℤ) hbd)
  -- Finally the rank descends from the field extension to the given field-valued point.
  set j' : hrep.pullback (yoneda.map τ ≫ ξ) ⟶ hrep.pullback ξ :=
    hrep.lift' (hrep.fst' (yoneda.map τ ≫ ξ)) (hrep.snd (yoneda.map τ ≫ ξ) ≫ τ)
      (by rw [Functor.map_comp, Category.assoc]; exact hfib'.w) with hj'
  have hj'fst : j' ≫ hrep.fst' ξ = hrep.fst' (yoneda.map τ ≫ ξ) := hrep.lift'_fst _ _ _
  have hj'snd : j' ≫ hrep.snd ξ = hrep.snd (yoneda.map τ ≫ ξ) ≫ τ := hrep.lift'_snd _ _ _
  have hsitesq : IsPullback j' (hrep.snd (yoneda.map τ ≫ ξ)) (hrep.snd ξ) τ := by
    refine IsPullback.of_map_of_faithful yoneda (IsPullback.of_right ?_ ?_ hfib)
    · rwa [← Functor.map_comp, hj'fst]
    · rw [← Functor.map_comp, hj'snd, Functor.map_comp]
  exact ⟨hrep.pullback ξ, hrep.snd ξ, yoneda.map (hrep.fst' ξ), r',
    hr'.trans hrn,
    isFiniteLocallyFreeOfRank_of_isPullback_of_isoFieldSpec B S hS hA hD hsitesq r' hrank',
    hfib⟩

end AlgebraicGeometry.Space

end
