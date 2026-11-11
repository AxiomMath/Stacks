module

public import StacksFrontier.AlgebraicGeometry.Descent.DischargedEtaleDescent
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AbsoluteNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineFinitePresentationFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationApproximationSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeFinitePresentationApproximation

/-!
# Factoring through an affine scheme of finite presentation over a quasi-separated space

Let `Y` be an algebraic space over a scheme `S` and let `g : Z → Y` be a morphism from a scheme.
We show that if `Y` is quasi-separated then `g` factors, Zariski locally on `Z`, through an
affine scheme which is locally of finite presentation over `Y`: for every point `z` of `Z` there
are an affine open neighbourhood `V` of `z`, an affine scheme `U` with a morphism `U → Y` locally
of finite presentation, and a factorization `V → U → Y` of `g|_V`. By
`Space.exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization` this is
exactly what the refinement of Stacks 0CM8 for `Z` a scheme asks for, so we obtain the whole of
Stacks 0CM8 for quasi-separated `Y`.

The proof follows the route of absolute Noetherian approximation. Viewing everything over
`Spec ℤ`, we may replace `Z` by an affine open neighbourhood `V₀` of `z` and `Y` by a
quasi-compact open subspace `Y'` through which `V₀ → Y` factors; `Y'` is quasi-compact and
quasi-separated, so it is the limit of a directed inverse system of algebraic spaces `Y_i` of
finite type over `Spec ℤ` with affine transition morphisms (Stacks 07SU). A stage `Y_i` is
locally of finite presentation over `Spec ℤ`, so `V₀ → Y' → Y_i` factors Zariski locally
through an affine scheme `U_i` locally of finite presentation over `Y_i`
(`AlgebraicGeometry.Space.exists_affine_isLocallyOfFinitePresentation_factorization_of_terminal`).
The projection `Y' → Y_i` is affine, so `U_i ×_{Y_i} Y'` is an affine scheme; it is locally of
finite presentation over `Y'` as a base change, hence over `Y`, and it receives the
neighbourhood of `z`.

## Main results

All declarations are in the namespace `AlgebraicGeometry.Space`.

* `PresentedNoetherianApproximation.isAffineHom_π`: the projections from the limit of a
  presented Noetherian approximation to its stages are affine.
* `IsLocallyOfFinitePresentation.of_isPullback`: base change of a morphism locally of finite
  presentation along a cartesian square of algebraic spaces.
* `exists_affine_isLocallyOfFinitePresentation_factorization_of_presentedNoetherianApproximation`:
  the factorization for a space over `Spec ℤ` carrying a presented Noetherian approximation.
* `exists_affine_isLocallyOfFinitePresentation_factorization_of_isAbsolutelyQuasiSeparated`: the
  factorization for a quasi-separated algebraic space over any base scheme.
* `exists_affine_isLocallyOfFinitePresentation_factorization_of_quasiSeparated_factorization`:
  the factorization for an arbitrary algebraic space `Y`, given a factorization of an affine
  open neighbourhood of `z` through a quasi-separated algebraic space locally of finite
  presentation over `Y`.
* `exists_affine_etale_isLocallyOfFinitePresentation_separation_of_isAbsolutelyQuasiSeparated`:
  Stacks 0CM8, including the refinement for `Z` a scheme, for `Y` quasi-separated.

## Implementation notes

*Affineness of the projections.* The approximation of Stacks 07SU comes with a presentation of
its limit: a limit atlas `V → Y'` which is the base change of the atlas `V_i → Y_i` of every
stage, with `V = lim V_i` a cofiltered limit of schemes with affine transition morphisms. The
base change of `Y' → Y_i` along the surjective étale `V_i → Y_i` is therefore the limit
projection `V → V_i`, an affine morphism of schemes, and affineness descends along surjective
étale morphisms (Stacks 03WG). No bound on the size of the index set is needed for this, in
contrast with Stacks 07SF, part (1).

*Change of base.* Absolute Noetherian approximation is available over `Spec ℤ` only, so the
statement over `S` is obtained from the one over `Spec ℤ` through the lower-shriek extension of
Stacks 03I5 (2): every chart of the extension of `Y` is the extension of a chart of `Y`
(`AlgebraicGeometry.exists_relocalizeChart`), local finite presentation is unchanged
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff`), and the extension is
faithful, which returns the factorization to the site of `S`.

## References

* [Stacks Project, Tag 0CM8](https://stacks.math.columbia.edu/tag/0CM8)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 03XR for an arbitrary cartesian square of algebraic spaces**, the case of being
locally of finite presentation. If `b` is the base change of a morphism `f` locally of finite
presentation along a cartesian square of presheaves on the big fppf site of `S` whose four
corners are algebraic spaces, then `b` is locally of finite presentation.

This is `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isStableUnderBaseChange` read on
morphisms of the presheaves carrying the algebraic spaces, as
`AlgebraicGeometry.Space.IsFinitePresentation.of_isPullback` is for finite presentation. -/
theorem IsLocallyOfFinitePresentation.of_isPullback (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {W X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B S hS b := by
  let P : ObjectProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := IsAlgebraicSpace B S hS
  let W' : P.FullSubcategory := ⟨W, hW⟩
  let X' : P.FullSubcategory := ⟨X, hX⟩
  let Y' : P.FullSubcategory := ⟨Y, hY⟩
  let Z' : P.FullSubcategory := ⟨Z, hZ⟩
  have h' : IsPullback (ObjectProperty.homMk a : W' ⟶ X')
      (ObjectProperty.homMk b : W' ⟶ Y')
      (ObjectProperty.homMk f : X' ⟶ Z') (ObjectProperty.homMk g : Y' ⟶ Z') :=
    IsPullback.of_map P.ι (ObjectProperty.hom_ext _ h.w) h
  have := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  exact MorphismProperty.of_isPullback
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) =>
      IsLocallyOfFinitePresentation B S hS k.hom) h' hf

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

local notation "𝕋" => BigFppfOver.toScheme B (⊤_ Scheme) hZ

namespace PresentedNoetherianApproximation

attribute [local instance] NoetherianApproximation.preorder NoetherianApproximation.nonempty
  NoetherianApproximation.isDirected

/-- **The projections of a presented Noetherian approximation are affine.** Let `A` be a
presented Noetherian approximation of an algebraic space `X` over `Spec ℤ`. Then every
projection `X ⟶ X_j` from the limit to a stage is affine.

The base change of the projection along the surjective étale atlas `V_j ⟶ X_j` of the stage is
the projection `V ⟶ V_j` from the limit atlas, which is a limit projection of a cofiltered system
of schemes with affine transition morphisms and hence affine; affineness descends along
surjective étale morphisms by Stacks 03WG. -/
theorem isAffineHom_π {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B _ hZ X) (A : PresentedNoetherianApproximation B hZ X)
    (j : A.Iᵒᵖ) : IsAffineHom B (⊤_ Scheme.{u}) hZ (A.π.app j) := by
  let P := A.presentation
  have : ∀ {i k : A.Iᵒᵖ} (g : i ⟶ k), AlgebraicGeometry.IsAffineHom ((P.atlas ⋙ 𝕋).map g) :=
    fun g => P.isAffineHom_atlas g
  have : InitiallySmall.{u} A.Iᵒᵖ := initiallySmall_of_essentiallySmall _
  have h₁ : AlgebraicGeometry.IsAffineHom ((𝕋).map (P.atlasCone.π.app j)) :=
    isAffineHom_π_app_of_initiallySmall (P.atlas ⋙ 𝕋) ((𝕋).mapCone P.atlasCone)
      P.isLimit_atlasCone j
  have hsq : IsPullback P.limitAtlas (yoneda.map (P.atlasCone.π.app j)) (A.π.app j)
      (P.atlasMap.app j) := (P.isPullback_limitAtlas j).flip
  have h₂ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) 𝕋).presheaf
        (yoneda.map (P.atlasCone.π.app j)) :=
    (presheaf_yoneda_map_iff B _ hZ inferInstance _).2 h₁
  have h₃ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) 𝕋).presheaf
        (pullback.snd (A.π.app j) (P.atlasMap.app j)) := by
    rw [← hsq.isoPullback_inv_snd]
    exact MorphismProperty.RespectsIso.precomp _ _ _ h₂
  exact isAffineHom_of_presheaf (presheaf_isAffineHom_of_surjectiveEtaleChart_unconditional hX
    (A.isAlgebraicSpace j) (isSurjective_of_presheafSurjective B _ hZ _ (P.surjective_atlasMap j))
    (isEtale_of_presheaf_etale B _ hZ (P.etale_atlasMap j)) h₃).2

end PresentedNoetherianApproximation

attribute [local instance] NoetherianApproximation.preorder NoetherianApproximation.nonempty
  NoetherianApproximation.isDirected in
/-- **Factorization through an affine scheme of finite presentation, over a presented
Noetherian approximation.** Let `Y` be an algebraic space over `Spec ℤ` carrying a presented
Noetherian approximation `A`, let `g : Z₀ ⟶ Y` be a morphism from an object of the site and let
`z` be a point of `|Z₀|`. Then there are an affine open neighbourhood `V` of `z` in `Z₀`, an
affine object `U` of the site with a morphism `ι : U ⟶ Y` locally of finite presentation, and a
factorization `V ⟶ U ⟶ Y` of the restriction of `g` to `V`.

Any stage `Y_j` of the approximation is locally of finite presentation over `Spec ℤ`, so the
composite `Z₀ ⟶ Y ⟶ Y_j` factors on an affine open neighbourhood of `z` through an affine `U_j`
locally of finite presentation over `Y_j`, by
`AlgebraicGeometry.Space.exists_affine_isLocallyOfFinitePresentation_factorization_of_terminal`.
The projection `Y ⟶ Y_j` is affine
(`AlgebraicGeometry.Space.PresentedNoetherianApproximation.isAffineHom_π`), so the base change
`U = U_j ×_{Y_j} Y` is represented by an affine object; it is locally of finite presentation
over `Y` as a base change, and the neighbourhood maps to it. -/
theorem
    exists_affine_isLocallyOfFinitePresentation_factorization_of_presentedNoetherianApproximation
    {Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {Z₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (hY : IsAlgebraicSpace B _ hZ Y) (A : PresentedNoetherianApproximation B hZ Y)
    (g : yoneda.obj Z₀ ⟶ Y) (z : points B _ hZ (yoneda.obj Z₀)) :
    ∃ (U V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (ι : yoneda.obj U ⟶ Y) (pV : V ⟶ Z₀)
      (v : points B _ hZ (yoneda.obj V)) (α₀ : V ⟶ U),
      IsAffine ((𝕋).obj U) ∧
      IsLocallyOfFinitePresentation B _ hZ ι ∧
      IsAffine ((𝕋).obj V) ∧
      AlgebraicGeometry.IsOpenImmersion ((𝕋).map pV) ∧
      pointsMap B _ hZ (yoneda.obj V) (yoneda.map pV) v = z ∧
      yoneda.map pV ≫ g = yoneda.map α₀ ≫ ι := by
  obtain ⟨j⟩ : Nonempty A.Iᵒᵖ := ⟨Opposite.op (Classical.arbitrary A.I)⟩
  have hYj := A.isAlgebraicSpace j
  obtain ⟨U, V, ι, pV, v, α₀, hU, hι, hV, hpV, hv, hfac⟩ :=
    exists_affine_isLocallyOfFinitePresentation_factorization_of_terminal B _ hZ hYj
      (isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B _ hZ hYj
        (isAlgebraicSpace_terminal B _ hZ) _
        (hasEtaleLocalProperty_isLocallyNoetherian_terminal B hZ)
        (isFiniteType_terminal_of_isFiniteType_viewOverIntegers B hZ
          (A.isFiniteTypeOverIntegers j)).1) (g ≫ A.π.app j) z
  obtain ⟨W, p, q, hpb⟩ := A.isAffineHom_π hY j ⟨U, hU⟩ ι
  have hw : (yoneda.map pV ≫ g) ≫ A.π.app j = yoneda.map α₀ ≫ ι := by
    rw [Category.assoc]
    exact hfac
  refine ⟨_, V, p, pV, v, yoneda.preimage (hpb.lift _ _ hw), W.property, ?_, hV, hpV, hv, ?_⟩
  · exact IsLocallyOfFinitePresentation.of_isPullback B _ hZ (isAlgebraicSpace_yoneda B _ hZ _)
      (isAlgebraicSpace_yoneda B _ hZ _) hY hYj hpb.flip hι
  · rw [Functor.map_preimage, hpb.lift_fst]

/-- The case `S = Spec ℤ` of
`exists_affine_isLocallyOfFinitePresentation_factorization_of_isAbsolutelyQuasiSeparated`. An
affine open neighbourhood `V₀` of `z` maps into a quasi-compact open subspace `Y'` of `Y`, which
is quasi-separated and so carries a presented Noetherian approximation (Stacks 07SU);
`exists_affine_isLocallyOfFinitePresentation_factorization_of_presentedNoetherianApproximation`
applies to `V₀ ⟶ Y'`, and the inclusion of `Y'` is an open immersion, hence locally of finite
presentation. -/
private theorem exists_affine_isLocallyOfFinitePresentation_factorization_overIntegers
    {Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {Z₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (hY : IsAlgebraicSpace B _ hZ Y) (hYqs : IsAbsolutelyQuasiSeparated B _ hZ hZ Y)
    (g : yoneda.obj Z₀ ⟶ Y) (z : points B _ hZ (yoneda.obj Z₀)) :
    ∃ (U V : BigFppfOver B (⊤_ Scheme.{u}) hZ) (ι : yoneda.obj U ⟶ Y) (pV : V ⟶ Z₀)
      (v : points B _ hZ (yoneda.obj V)) (α₀ : V ⟶ U),
      IsAffine ((𝕋).obj U) ∧
      IsLocallyOfFinitePresentation B _ hZ ι ∧
      IsAffine ((𝕋).obj V) ∧
      AlgebraicGeometry.IsOpenImmersion ((𝕋).map pV) ∧
      pointsMap B _ hZ (yoneda.obj V) (yoneda.map pV) v = z ∧
      yoneda.map pV ≫ g = yoneda.map α₀ ≫ ι := by
  classical
  obtain ⟨VO, hVO, hzVO⟩ : ∃ VO : ((𝕋).obj Z₀).Opens, IsAffine VO.toScheme ∧
      pointsToScheme B _ hZ Z₀ z ∈ VO := by
    obtain ⟨-, ⟨VO, hVO, rfl⟩, hz, -⟩ :=
      ((𝕋).obj Z₀).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (pointsToScheme B _ hZ Z₀ z)) isOpen_univ
    exact ⟨VO, hVO, hz⟩
  let V₀ := openSiteObject B _ hZ Z₀ VO
  let j₀ : V₀ ⟶ Z₀ := openSiteObjectHom B _ hZ Z₀ VO
  have hj₀ : (𝕋).map j₀ = VO.ι := map_openSiteObjectHom B _ hZ Z₀ VO
  have hV₀aff : IsAffine ((𝕋).obj V₀) := hVO
  obtain ⟨v₀, hv₀⟩ := exists_pointsMap_yonedaMap_eq_of_mem_range B _ hZ j₀ z (by
    rw [hj₀]
    exact ⟨⟨_, hzVO⟩, rfl⟩)
  obtain ⟨Y', hY', ⟨g', hg'⟩, hY'qc⟩ := exists_quasiCompact_openSubspace_factor B _ hZ
    (isAlgebraicSpace_yoneda B _ hZ V₀) hY
    (isQuasiCompactSpace_yoneda_of_isAffine B _ hZ V₀ hV₀aff) (yoneda.map j₀ ≫ g)
  have hY'qs : IsAbsolutelyQuasiSeparated B _ hZ hZ Y'.toFunctor :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B _ hZ hZ hY'.1 hYqs
      (isQuasiSeparated_of_mono B _ hZ Y'.ι inferInstance)
  obtain ⟨A⟩ := nonempty_presentedNoetherianApproximation hY'.1 hY'qc hY'qs
  obtain ⟨U, V, ι, pV, v, α₀, hU, hι, hV, hpV, hv, hfac⟩ :=
    exists_affine_isLocallyOfFinitePresentation_factorization_of_presentedNoetherianApproximation
      hY'.1 A g' v₀
  refine ⟨U, V, ι ≫ Y'.ι, pV ≫ j₀, v, α₀, hU, ?_, hV, ?_, ?_, ?_⟩
  · exact isLocallyOfFinitePresentation_comp B _ hZ (isAlgebraicSpace_yoneda B _ hZ U) hY'.1 hY
      ι Y'.ι hι (isLocallyOfFinitePresentation_of_isOpenImmersion B _ hZ hY'.2)
  · have : AlgebraicGeometry.IsOpenImmersion ((𝕋).map j₀) := by
      rw [hj₀]
      exact (inferInstance : AlgebraicGeometry.IsOpenImmersion VO.ι)
    rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp, pointsMap_comp, Function.comp_apply, hv, hv₀]
  · rw [Functor.map_comp, Category.assoc, ← hg', ← Category.assoc, hfac, Category.assoc]

/-- **A morphism from a scheme to a quasi-separated algebraic space factors Zariski locally
through an affine scheme locally of finite presentation over the space.** Let `Y` be a
quasi-separated algebraic space over `S`, let `g : Z₀ ⟶ Y` be a morphism from an object of the
big fppf site of `S`, and let `z` be a point of `|Z₀|`. Then there are an affine open
neighbourhood `V` of `z` in `Z₀`, an affine object `U` of the site with a morphism
`ι : U ⟶ Y` locally of finite presentation, and a factorization `V ⟶ U ⟶ Y` of the restriction
of `g` to `V`.

By `exists_affine_isLocallyOfFinitePresentation_factorization_of_separation` this is a
consequence of the refinement of Stacks 0CM8 for `Z` a scheme, and by
`exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization` it implies that
refinement.

The problem is viewed over `Spec ℤ` along the lower-shriek extension of Stacks 03I5 (2), where it
is solved by absolute Noetherian approximation, and the solution is read back over `S`: the
chart `U ⟶ Y` over `Spec ℤ` is the extension of a chart of `Y`
(`AlgebraicGeometry.exists_relocalizeChart`), local finite presentation is unchanged by the
extension, the affine open neighbourhood acquires its structure morphism to `S` from `Z₀`, and
the factorization descends because the extension is faithful. -/
theorem exists_affine_isLocallyOfFinitePresentation_factorization_of_isAbsolutelyQuasiSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z₀ : BigFppfOver B S hS}
    (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (g : yoneda.obj Z₀ ⟶ Y) (z : points B S hS (yoneda.obj Z₀)) :
    ∃ (U V : BigFppfOver B S hS) (ι : yoneda.obj U ⟶ Y) (pV : V ⟶ Z₀)
      (v : points B S hS (yoneda.obj V)) (α₀ : V ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsLocallyOfFinitePresentation B S hS ι ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pV) ∧
      pointsMap B S hS (yoneda.obj V) (yoneda.map pV) v = z ∧
      yoneda.map pV ≫ g = yoneda.map α₀ ≫ ι := by
  classical
  let h : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let Λ := OverShriek.relocalizePresheafFunctor h
  have _ := relocalizePresheaf_faithful h
  have hY' : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (Λ.obj Y) :=
    isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ h Y hY
  have hY'qs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (Λ.obj Y) :=
    isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ Y hYqs
  let g' := relocalizeChart B S (⊤_ Scheme.{u}) hS hZ h g
  let x : (BigFppfOver.toScheme B S hS).obj Z₀ := pointsToScheme B S hS Z₀ z
  let z' := (pointsEquivScheme B (⊤_ Scheme.{u}) hZ ((Over.map h).obj Z₀)).symm x
  obtain ⟨U', V', ι', pV', v', α', hU', hι', hV', hpV', hv', hfac'⟩ :=
    exists_affine_isLocallyOfFinitePresentation_factorization_overIntegers hY' hY'qs g' z'
  obtain ⟨ψU, hψU, a, hae⟩ := exists_relocalizeChart B S (⊤_ Scheme.{u}) hS hZ h U' ι'
  have hψV : (pV'.left ≫ Z₀.hom) ≫ h = V'.hom := by
    rw [Category.assoc]
    exact Over.w pV'
  let V : BigFppfOver B S hS := Over.mk (pV'.left ≫ Z₀.hom)
  let pV : V ⟶ Z₀ := Over.homMk pV'.left rfl
  let rbU := relocalizeBaseHom B S (⊤_ Scheme.{u}) hS hZ h hψU
  let rbV := relocalizeBaseHom B S (⊤_ Scheme.{u}) hS hZ h hψV
  have hstr : α'.left ≫ ψU = pV'.left ≫ Z₀.hom := by
    have h1 := congrArg (· ≫ OverShriek.relocalizeToYoneda h Y) hfac'
    simp only [Category.assoc, g', relocalizeChart_comp_relocalizeToYoneda, hae] at h1
    rw [← yoneda.map_comp, ← yoneda.map_comp, ← yoneda.map_comp] at h1
    have h2 := congrArg Over.Hom.left (yoneda.map_injective h1)
    simpa [rbU, relocalizeOverHom, relocalizeBaseHom] using h2.symm
  let α : V ⟶ Over.mk ψU := Over.homMk α'.left hstr
  obtain ⟨v, hv⟩ := exists_pointsMap_yonedaMap_eq_of_mem_range B S hS pV z
    ⟨pointsToScheme B (⊤_ Scheme.{u}) hZ V' v', by
      have h1 := pointsToScheme_pointsMap_yoneda B (⊤_ Scheme.{u}) hZ pV' v'
      rw [hv'] at h1
      exact h1.symm.trans
        (Equiv.apply_symm_apply (pointsEquivScheme B (⊤_ Scheme.{u}) hZ ((Over.map h).obj Z₀)) x)⟩
  refine ⟨Over.mk ψU, V, a, pV, v, α, hU', ?_, hV', hpV', hv, ?_⟩
  · rw [hae] at hι'
    simp only [relocalizeChart] at hι'
    rw [← Category.assoc] at hι'
    exact (Space.holdsOnEveryEtaleChart_relocalizeMap_iff B S (⊤_ Scheme.{u}) hS hZ h _ a).1
      ((Space.holdsOnEveryEtaleChart_iso_comp_iff B (⊤_ Scheme.{u}) hZ _ _ _).1 hι')
  · have e1 : pV' = rbV ≫ (Over.map h).map pV := Over.OverMorphism.ext (by
      simp [rbV, relocalizeBaseHom, pV])
    have e2 : α' ≫ rbU = rbV ≫ (Over.map h).map α := Over.OverMorphism.ext (by
      simp [rbU, rbV, relocalizeBaseHom, α])
    have key : relocalizeChart B S (⊤_ Scheme.{u}) hS hZ h (yoneda.map pV ≫ g) =
        relocalizeChart B S (⊤_ Scheme.{u}) hS hZ h (yoneda.map α ≫ a) := by
      rw [← relocalizeChart_naturality, ← relocalizeChart_naturality]
      apply (cancel_epi (yoneda.map rbV)).1
      rw [← Category.assoc, ← yoneda.map_comp, ← e1, ← Category.assoc, ← yoneda.map_comp, ← e2,
        yoneda.map_comp, Category.assoc, ← hae]
      exact hfac'
    simp only [relocalizeChart] at key
    exact Λ.map_injective ((Iso.cancel_iso_inv_left _ _ _).1 key)

/-- The factorization of an affine open neighbourhood of `z` through an affine scheme locally of
finite presentation over `Y`, for an *arbitrary* algebraic space `Y`, from a factorization of an
affine open neighbourhood `V₁` of `z` through a quasi-separated algebraic space `X'` locally of
finite presentation over `Y`: the quasi-separated case applied to `V₁ ⟶ X'` gives an affine
`U` locally of finite presentation over `X'`, hence over `Y`, receiving a smaller affine open
neighbourhood of `z`. -/
theorem exists_affine_isLocallyOfFinitePresentation_factorization_of_quasiSeparated_factorization
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z₀ V₁ : BigFppfOver B S hS}
    (hY : IsAlgebraicSpace B S hS Y) (hX' : IsAlgebraicSpace B S hS X')
    (hX'qs : IsAbsolutelyQuasiSeparated B S hS hZ X') (ψ : X' ⟶ Y)
    (hψ : IsLocallyOfFinitePresentation B S hS ψ)
    (g : yoneda.obj Z₀ ⟶ Y) (z : points B S hS (yoneda.obj Z₀))
    (p₁ : V₁ ⟶ Z₀) (hp₁ : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map p₁))
    (v₁ : points B S hS (yoneda.obj V₁)) (hv₁ : pointsMap B S hS _ (yoneda.map p₁) v₁ = z)
    (β : yoneda.obj V₁ ⟶ X') (hβ : β ≫ ψ = yoneda.map p₁ ≫ g) :
    ∃ (U V : BigFppfOver B S hS) (ι : yoneda.obj U ⟶ Y) (pV : V ⟶ Z₀)
      (v : points B S hS (yoneda.obj V)) (α₀ : V ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsLocallyOfFinitePresentation B S hS ι ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pV) ∧
      pointsMap B S hS (yoneda.obj V) (yoneda.map pV) v = z ∧
      yoneda.map pV ≫ g = yoneda.map α₀ ≫ ι := by
  obtain ⟨U, V, ι, pV, v, α₀, hU, hι, hV, hpV, hv, hfac⟩ :=
    exists_affine_isLocallyOfFinitePresentation_factorization_of_isAbsolutelyQuasiSeparated
      B S hS hZ hX' hX'qs β v₁
  refine ⟨U, V, ι ≫ ψ, pV ≫ p₁, v, α₀, hU,
    isLocallyOfFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS U) hX' hY ι ψ hι hψ,
    hV, ?_, ?_, ?_⟩
  · rw [(BigFppfOver.toScheme B S hS).map_comp]
    exact AlgebraicGeometry.IsOpenImmersion.comp _ _
  · rw [yoneda.map_comp, pointsMap_comp_apply, hv, hv₁]
  · rw [yoneda.map_comp, Category.assoc, ← hβ, ← Category.assoc, hfac, Category.assoc]

section Separation

attribute [local instance] pointTopology

/-- **Stacks 0CM8, for `Y` quasi-separated.** Let `f : X ⟶ Y` be a quasi-compact morphism of
algebraic spaces over `S` with `Y` quasi-separated.

1. For every morphism `g : Z ⟶ Y` of algebraic spaces, point `z` of `|Z|` and closed subset `T`
   of `|X ×_Y Z|` whose image in `|Z|` misses `z`, there are an affine étale neighbourhood
   `(V, v)` of `z`, an affine `Z'` and a factorization `V ⟶ Z' ⟶ Y` of `V ⟶ Y` whose second leg
   `b` is locally of finite presentation, and a closed subset `T'` of `|X ×_Y Z'|` whose image in
   `|Z'|` misses the image of `v` and which receives the inverse image of `T` along the
   comparison morphisms `r` and `q` of the three fibre products.
2. If moreover `Z` is a scheme, represented by an object `Z₀` of the site, then `V` may be taken
   to be an affine open neighbourhood of `z`: the étale neighbourhood is an open immersion
   `V ⟶ Z₀` sending `v` to `z`, with all the conclusions of the first part.

The first part is `exists_affine_etale_isLocallyOfFinitePresentation_separation`, which needs no
hypothesis on `Y`. The second part is
`exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization`, whose input — a
Zariski-local factorization of `Z₀ ⟶ Y` through an affine scheme locally of finite presentation
over `Y` — is supplied for quasi-separated `Y` by
`exists_affine_isLocallyOfFinitePresentation_factorization_of_isAbsolutelyQuasiSeparated`. -/
@[stacks 0CM8 "the whole lemma, including the refinement for Z a scheme (V an affine open \
neighbourhood of z), under the extra hypothesis that Y is quasi-separated. For an arbitrary Y \
the refinement is open: it is equivalent to Z -> Y factoring Zariski locally through an affine \
scheme locally of finite presentation over Y, which is proved here only for Y quasi-separated"]
theorem exists_affine_etale_isLocallyOfFinitePresentation_separation_of_isAbsolutelyQuasiSeparated
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f) :
    (∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_ : IsAlgebraicSpace B S hS Z) (g : Z ⟶ Y)
      (z : points B S hS Z) (T : Set (points B S hS (pullback f g))), IsClosed T →
      z ∉ pointsMap B S hS (pullback f g) (pullback.snd f g) '' T →
      ∃ (V Z' : BigFppfOver B S hS) (p : yoneda.obj V ⟶ Z)
        (v : points B S hS (yoneda.obj V)) (a : yoneda.obj V ⟶ yoneda.obj Z')
        (b : yoneda.obj Z' ⟶ Y) (T' : Set (points B S hS (pullback f b)))
        (r : pullback f (p ≫ g) ⟶ pullback f g) (q : pullback f (p ≫ g) ⟶ pullback f b),
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
        IsEtale B S hS p ∧
        pointsMap B S hS (yoneda.obj V) p v = z ∧
        p ≫ g = a ≫ b ∧
        IsLocallyOfFinitePresentation B S hS b ∧
        IsClosed T' ∧
        pointsMap B S hS (yoneda.obj V) a v ∉
          pointsMap B S hS (pullback f b) (pullback.snd f b) '' T' ∧
        r ≫ pullback.fst f g = pullback.fst f (p ≫ g) ∧
        r ≫ pullback.snd f g = pullback.snd f (p ≫ g) ≫ p ∧
        IsPullback r (pullback.snd f (p ≫ g)) (pullback.snd f g) p ∧
        q ≫ pullback.fst f b = pullback.fst f (p ≫ g) ∧
        q ≫ pullback.snd f b = pullback.snd f (p ≫ g) ≫ a ∧
        pointsMap B S hS (pullback f (p ≫ g)) q ''
          (pointsMap B S hS (pullback f (p ≫ g)) r ⁻¹' T) ⊆ T') ∧
    (∀ {Z₀ : BigFppfOver B S hS} (g : yoneda.obj Z₀ ⟶ Y) (z : points B S hS (yoneda.obj Z₀))
      (T : Set (points B S hS (pullback f g))), IsClosed T →
      z ∉ pointsMap B S hS (pullback f g) (pullback.snd f g) '' T →
      ∃ (V Z' : BigFppfOver B S hS) (p : yoneda.obj V ⟶ yoneda.obj Z₀) (pV : V ⟶ Z₀)
        (v : points B S hS (yoneda.obj V)) (a : yoneda.obj V ⟶ yoneda.obj Z')
        (b : yoneda.obj Z' ⟶ Y) (T' : Set (points B S hS (pullback f b)))
        (r : pullback f (p ≫ g) ⟶ pullback f g) (q : pullback f (p ≫ g) ⟶ pullback f b),
        p = yoneda.map pV ∧
        AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pV) ∧
        (BigFppfOver.toScheme B S hS).map pV (pointsToScheme B S hS V v) =
          pointsToScheme B S hS Z₀ z ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
        IsEtale B S hS p ∧
        pointsMap B S hS (yoneda.obj V) p v = z ∧
        p ≫ g = a ≫ b ∧
        IsLocallyOfFinitePresentation B S hS b ∧
        IsClosed T' ∧
        pointsMap B S hS (yoneda.obj V) a v ∉
          pointsMap B S hS (pullback f b) (pullback.snd f b) '' T' ∧
        r ≫ pullback.fst f g = pullback.fst f (p ≫ g) ∧
        r ≫ pullback.snd f g = pullback.snd f (p ≫ g) ≫ p ∧
        IsPullback r (pullback.snd f (p ≫ g)) (pullback.snd f g) p ∧
        q ≫ pullback.fst f b = pullback.fst f (p ≫ g) ∧
        q ≫ pullback.snd f b = pullback.snd f (p ≫ g) ≫ a ∧
        pointsMap B S hS (pullback f (p ≫ g)) q ''
          (pointsMap B S hS (pullback f (p ≫ g)) r ⁻¹' T) ⊆ T') := by
  refine ⟨fun hZsp g z T hT hz =>
    exists_affine_etale_isLocallyOfFinitePresentation_separation B S hS hX hY hZsp f g hf z T hT hz,
    fun {Z₀} g z T hT hz => ?_⟩
  obtain ⟨U, V₀, ι, pV₀, v₀, α₀, hU, hι, hV₀, hpV₀, hv₀, hfac⟩ :=
    exists_affine_isLocallyOfFinitePresentation_factorization_of_isAbsolutelyQuasiSeparated
      B S hS hZ hY hYqs g z
  exact exists_affineOpen_isLocallyOfFinitePresentation_separation_of_factorization B S hS hX hY
    f g hf z T hT hz ι hU hι hV₀ pV₀ hpV₀ v₀ hv₀ α₀ hfac

end Separation

end AlgebraicGeometry.Space
