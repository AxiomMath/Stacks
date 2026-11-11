module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineUnitLocusQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDenseAffineOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsFiniteOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothRelativeDimensionClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.TrivialDivisorEquation

/-!
# A nontrivial invertible module on a proper smooth family over a regular local base

Let `T` be an affine scheme with a regular Noetherian ring of functions and a point `t` which is
a specialization of every point (the closed point of `Spec` of a regular local ring), and let
`f : Y ⟶ h_T` be a flat, proper morphism of finite presentation from a nonempty algebraic space
whose closed fibre `Y ×_T Spec κ(t)` is smooth of relative dimension `n ≥ 1` over `κ(t)`. Then
`Y` carries an effective Cartier divisor `D` whose invertible module `𝒪_Y(D)` is not trivial.

This is the step of the discussion preceding Stacks 0D1R (the stack of proper flat algebraic
spaces is not algebraic) which produces a nontrivial element of `Pic(Y)` on the effective
algebraization `Y` of the universal deformation of a K3 surface: "Since `Y` is separated we can
find an affine open subscheme `V ⊂ Y`. Since the special fibre `X` of `Y` is smooth, we see that
`f` is smooth. Hence `Y` is regular being smooth over regular and it follows that the complement
`D` of `V` in `Y` is an effective Cartier divisor. Then `𝒪_Y(D)` is a nontrivial element of
`Pic(Y)`."

## The argument

* `f` is smooth of relative dimension `n` on every étale chart, because the closed fibre is and
  every point of `|Y|` specializes into the closed fibre
  (`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_smoothOfRelativeDimension_of_closedFibre`).
* So a surjective étale chart of `Y` is smooth over the regular scheme `T`, hence regular, and
  `Y` is regular; it is Noetherian and separated, being proper over the affine Noetherian `T`.
* Stacks 0ADD and 0DML give a dense affine open `u : h_W ⟶ Y` whose complement is an effective
  Cartier divisor `D`
  (`AlgebraicGeometry.Space.exists_denseAffineOpen_isEffectiveCartierDivisor_compl`).
* If `𝒪_Y(D)` were trivial, `D` would be the zero locus of one global function `g`
  (`AlgebraicGeometry.Space.exists_globalFunctions_zeroLocus_of_isTrivial`), so the affine `W`
  would be the locus where `g` is invertible; then `W ⟶ T` is locally quasi-finite
  (`AlgebraicGeometry.Space.locallyQuasiFinite_of_isAffine_unitLocus`, which uses that `g` is
  integral over `Γ(T)` because `f` is universally closed).
* But `W ⟶ T` is smooth of relative dimension `n ≥ 1` and `W` is nonempty (it is dense in the
  nonempty `|Y|`), which is incompatible with local quasi-finiteness
  (`AlgebraicGeometry.SmoothOfRelativeDimension.eq_zero_of_locallyQuasiFinite`).

The source proves the nontriviality on the generic fibre; the argument above works on the whole
of `Y` instead and needs no generic fibre.

## Main results

* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_of_smoothOfRelativeDimension`: an
  algebraic space smooth over a regular scheme is regular.
* `Space.exists_isEffectiveCartierDivisor_not_isTrivial_of_isProper_of_closedFibre`:
  the nontrivial invertible module `𝒪_Y(D)`.
* `Space.exists_isEffectiveCartierDivisor_not_isTrivial_of_isProper_of_isLocalRing`:
  the same over an affine base whose ring of functions is a regular local ring.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 0DML](https://stacks.math.columbia.edu/tag/0DML)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space which is smooth of some relative dimension over a regular scheme is
regular.**  A surjective étale chart of `Y` is smooth over `T`, hence a regular scheme. -/
theorem hasEtaleLocalProperty_isRegular_of_smoothOfRelativeDimension
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {T : BigFppfOver B S hS} (hreg : IsRegular ((BigFppfOver.toScheme B S hS).obj T))
    (f : Y ⟶ yoneda.obj T) (n : ℕ)
    (hsm : HoldsOnEveryEtaleChart B S hS (@SmoothOfRelativeDimension n) f) :
    HasEtaleLocalProperty B S hS Y (fun X : Scheme.{u} => IsRegular X) := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  refine ⟨V, b, hbSurj, hbEtale, ?_⟩
  have hsmV : SmoothOfRelativeDimension n
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (b ≫ f))) :=
    hsm V T b (𝟙 _) (yoneda.preimage (b ≫ f)) hbEtale (presheaf_etale_id B S hS T)
      (by rw [Functor.map_preimage, Category.comp_id])
  exact isRegular_of_smooth _
    (SmoothOfRelativeDimension.smooth n
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (b ≫ f)))) hreg

/-- **A nontrivial invertible module on a proper smooth family over a regular local base**
(the nontrivial element of `Pic(Y)` in the discussion before Stacks 0D1R).

Let `T` be an object of the big fppf site whose scheme is affine with Noetherian ring of
functions, regular, and has a point `t` which is a specialization of every point; let
`t₀ : T₀ ⟶ T` present `Spec κ(t) ⟶ T`. Let `f : Y ⟶ h_T` be flat, proper and of finite
presentation, with `|Y|` nonempty, such that the closed fibre `Y ×_{h_T} h_{T₀} ⟶ h_{T₀}` is
smooth of relative dimension `n ≠ 0` on every étale chart. Then there is an effective Cartier
divisor `D ⊆ Y` with `𝒪_Y(D)` not isomorphic to `𝒪_Y`. -/
theorem exists_isEffectiveCartierDivisor_not_isTrivial_of_isProper_of_closedFibre
    (Y : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]
    (hreg : IsRegular ((BigFppfOver.toScheme B S hS).obj T))
    (f : Y.1 ⟶ yoneda.obj T) (hfp : IsFinitePresentation B S hS f) (hflat : IsFlat B S hS f)
    (hprop : IsProper B S hS f)
    (t : (BigFppfOver.toScheme B S hS).obj T) (ht : ∀ s, s ⤳ t)
    (T₀ : BigFppfOver B S hS) (t₀ : T₀ ⟶ T)
    (e : (BigFppfOver.toScheme B S hS).obj T₀ ≅
      Spec (((BigFppfOver.toScheme B S hS).obj T).residueField t))
    (he : e.hom ≫ ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField t =
      (BigFppfOver.toScheme B S hS).map t₀)
    (n : ℕ) (hn : n ≠ 0)
    (hfib : HoldsOnEveryEtaleChart B S hS (@SmoothOfRelativeDimension n)
      (pullback.snd f (yoneda.map t₀)))
    (hne : Nonempty (points B S hS Y.1)) :
    ∃ (D : ClosedSubspaces B S hS Y.1) (hD : IsEffectiveCartierDivisor B S hS Y D),
      ¬ AlgebraicGeometry.SheafOfModules.IsTrivial (structureCommRings B S hS Y)
        (structureRingSheaf B S hS Y).property (associatedInvertibleSheaf B S hS Y D hD) := by
  -- `f` is smooth of relative dimension `n` on every étale chart
  have hsm : HoldsOnEveryEtaleChart B S hS (@SmoothOfRelativeDimension n) f :=
    holdsOnEveryEtaleChart_smoothOfRelativeDimension_of_closedFibre B S hS Y.2 f hfp.1 hflat
      hprop.2.2 t ht T₀ t₀ e he n hfib
  -- `Y` is regular, Noetherian and separated
  have hregY := hasEtaleLocalProperty_isRegular_of_smoothOfRelativeDimension B S hS Y.2 hreg f n
    hsm
  have hnoeth : IsNoetherian B S hS B.contains_terminal Y.1 :=
    isNoetherian_of_isProper_of_isAffine B S hS (W := Y) (T := T) (ObjectProperty.homMk f)
      B.contains_terminal hprop
  have hsep : IsAbsolutelySeparated B S hS B.contains_terminal Y.1 :=
    isAbsolutelySeparated_of_isSeparated_to_affine B S hS B.contains_terminal T inferInstance f
      hprop.1
  -- a dense affine open with an effective Cartier divisor as complement
  obtain ⟨W, u, hWaff, hu, hdense, D, hD, hDpts⟩ :=
    exists_denseAffineOpen_isEffectiveCartierDivisor_compl B S hS B.contains_terminal Y hsep
      hnoeth hregY
  refine ⟨D, hD, fun htriv => ?_⟩
  -- a trivialization gives an equation `g` of `D`
  obtain ⟨g, hg⟩ := exists_globalFunctions_zeroLocus_of_isTrivial B S hS Y D hD htriv
  have hpts : ∀ c : SmallEtale B S hS Y.1, IsAffine (chartScheme c) →
      chartPointsMap c ⁻¹' Set.range (pointsMap B S hS (yoneda.obj W) u) =
        ((chartScheme c).basicOpen (globalFunctionsChartRestriction B S hS Y c g) : Set _) := by
    intro c hc
    rw [← compl_compl (Set.range (pointsMap B S hS (yoneda.obj W) u)), ← hDpts,
      Set.preimage_compl, hg c hc, Scheme.zeroLocus_singleton, compl_compl]
  -- the unit locus `W` of `g` is quasi-finite over `T`
  let w : W ⟶ T := yoneda.preimage (u ≫ f)
  have hw : yoneda.map w = u ≫ f := Functor.map_preimage _ _
  have hqf : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map w) :=
    locallyQuasiFinite_of_isAffine_unitLocus B S hS inferInstance f hprop.2.2 hprop.2.1.1 g W
      hWaff u hu hpts w hw
  -- and smooth of relative dimension `n` over `T`
  have hsmW : SmoothOfRelativeDimension n ((BigFppfOver.toScheme B S hS).map w) :=
    hsm W T u (𝟙 _) w (presheaf_etale_of_isOpenImmersion B S hS hu)
      (presheaf_etale_id B S hS T) (by rw [hw, Category.comp_id])
  -- `W` is nonempty, being dense in the nonempty `|Y|`
  have hWne : Nonempty ((BigFppfOver.toScheme B S hS).obj W) := by
    obtain ⟨_, ⟨p, -⟩⟩ := hdense.nonempty
    exact ⟨schemePointsHomeomorph B S hS W p⟩
  exact hn (SmoothOfRelativeDimension.eq_zero_of_locallyQuasiFinite
    ((BigFppfOver.toScheme B S hS).map w))

/-- **A nontrivial invertible module on a proper smooth family over a regular local ring.**
The form of
`AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_not_isTrivial_of_isProper_of_closedFibre`
over an affine `T` whose ring of functions is a regular local ring, with `t` its closed point. -/
theorem exists_isEffectiveCartierDivisor_not_isTrivial_of_isProper_of_isLocalRing
    (Y : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]
    [IsRegularRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]
    (f : Y.1 ⟶ yoneda.obj T) (hfp : IsFinitePresentation B S hS f) (hflat : IsFlat B S hS f)
    (hprop : IsProper B S hS f)
    (T₀ : BigFppfOver B S hS) (t₀ : T₀ ⟶ T)
    (e : (BigFppfOver.toScheme B S hS).obj T₀ ≅
      Spec (((BigFppfOver.toScheme B S hS).obj T).residueField
        (((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv
          (IsLocalRing.closedPoint Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)))))
    (he : e.hom ≫ ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField
        (((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv
          (IsLocalRing.closedPoint Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))) =
      (BigFppfOver.toScheme B S hS).map t₀)
    (n : ℕ) (hn : n ≠ 0)
    (hfib : HoldsOnEveryEtaleChart B S hS (@SmoothOfRelativeDimension n)
      (pullback.snd f (yoneda.map t₀)))
    (hne : Nonempty (points B S hS Y.1)) :
    ∃ (D : ClosedSubspaces B S hS Y.1) (hD : IsEffectiveCartierDivisor B S hS Y D),
      ¬ AlgebraicGeometry.SheafOfModules.IsTrivial (structureCommRings B S hS Y)
        (structureRingSheaf B S hS Y).property (associatedInvertibleSheaf B S hS Y D hD) := by
  set X := (BigFppfOver.toScheme B S hS).obj T
  refine exists_isEffectiveCartierDivisor_not_isTrivial_of_isProper_of_closedFibre B S hS Y T
    (fun _ => ⟨⟨⊤, isAffineOpen_top X⟩, trivial, inferInstance⟩) f hfp hflat hprop
    (X.isoSpec.inv (IsLocalRing.closedPoint Γ(X, ⊤))) (fun s => ?_) T₀ t₀ e he n hn hfib hne
  have h := (IsLocalRing.specializes_closedPoint (X.isoSpec.hom s)).map
    X.isoSpec.inv.base.hom.continuous
  have hs : X.isoSpec.inv (X.isoSpec.hom s) = s := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rwa [hs] at h

end AlgebraicGeometry.Space

end
