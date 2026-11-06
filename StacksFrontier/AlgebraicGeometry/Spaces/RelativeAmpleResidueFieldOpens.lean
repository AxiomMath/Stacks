module

public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenChartSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleResidueFieldNeighbourhood

/-!
# Claim (A) of Stacks 0D3D at residue fields, with a Zariski open of the affine scheme

This file states the residue-field form of claim (A) of the proof of Stacks 0D3D with its
conclusion an open of the *scheme* `U` — the form in which the source states it, and the form
which does not depend on the base of the site — and derives from it the form
`AlgebraicGeometry.Space.AmpleSpreadsFromResidueFields`, whose conclusion is an open subspace of
`h_U`.

## Main definitions

* `AlgebraicGeometry.Space.AmpleSpreadsFromResidueFieldsToOpens`: for a proper `f' : X' ⟶ h_U`
  over an affine scheme `U`, an invertible `L'` and a point `u` of `U` over whose residue field
  `L'` is ample, there is an open `V ∋ u` of `U` such that `L'` is ample on the base change of
  `f'` to `V`.

## Main results

* `AlgebraicGeometry.Space.ampleSpreadsFromResidueFields_of_toOpens`: the open subspace of `h_U`
  cut out by `V` is as `AlgebraicGeometry.Space.AmpleSpreadsFromResidueFields` asks.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D33](https://stacks.math.columbia.edu/tag/0D33)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Claim (A) of the proof of Stacks 0D3D at residue fields, with an open of the scheme.** For
every affine scheme `U` of the site, every proper morphism `f' : X' ⟶ h_U` of algebraic spaces,
every invertible `𝒪_{X'}`-module `L'` and every point `u` of `U` such that the pullback of `L'`
is ample on every base change of `f'` along `Spec κ(u) ⟶ U`, there is an open `V ∋ u` of `U`
such that the pullback of `L'` is ample on every base change of `f'` along `V ⟶ U`. -/
def AmpleSpreadsFromResidueFieldsToOpens : Prop :=
  ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    ∀ {X' : AlgebraicSpaces B S hS} (f' : X' ⟶ representedAlgebraicSpace B S hS U),
      IsProper B S hS f'.hom →
    ∀ (L' : Modules.{u, u} B S hS X'.1 X'.2),
      Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X'.1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X'.1 X'.2).O)).property L' →
    ∀ (u : (BigFppfOver.toScheme B S hS).obj U),
      (∀ ⦃X₀ : AlgebraicSpaces B S hS⦄ (p₀ : X₀ ⟶ X')
        (f₀ : X₀ ⟶ representedAlgebraicSpace B S hS
          (residueFieldObject B S hS U u (B.residueField_spec_contains U.left.property u))),
        IsPullback p₀ f₀ f' (ObjectProperty.homMk (yoneda.map
          (residueFieldMap B S hS U u (B.residueField_spec_contains U.left.property u)))) →
        IsRelativelyAmple B S hS f₀ ((modulePullback B S hS p₀).obj L')) →
      ∃ V : ((BigFppfOver.toScheme B S hS).obj U).Opens, u ∈ V ∧
        ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X')
          (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub U V)),
          IsPullback p₁ f₁ f' (ObjectProperty.homMk (yoneda.map (openSubHom U V))) →
          IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L')

variable {B S hS}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
instance hasPullbacks_presheaf_relativeAmpleResidueFieldOpens :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

instance (priority := high) hasPullback_presheaf_relativeAmpleResidueFieldOpens
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The open subspace cut out by an open of the scheme.** Ampleness of `L'` over the base change
of `f'` to an open `V` of `U` is ampleness of `L'` over the open subspace of `h_U` cut out by `V`
(Stacks 0D33), and that subspace contains every point of `h_U` over `V`. -/
theorem isRelativelyAmpleOver_range_openSubHom {U : BigFppfOver B S hS}
    {X' : AlgebraicSpaces B S hS} (f' : X' ⟶ representedAlgebraicSpace B S hS U)
    (L' : Modules.{u, u} B S hS X'.1 X'.2) (V : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (hV : ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X')
      (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub U V)),
      IsPullback p₁ f₁ f' (ObjectProperty.homMk (yoneda.map (openSubHom U V))) →
      IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L')) :
    IsRelativelyAmpleOver f' L' (Subfunctor.range (yoneda.map (openSubHom U V))) := by
  have _ : Mono (yoneda.map (openSubHom U V)) :=
    mono_of_presheaf_isOpenImmersion (isOpenImmersion_yoneda_map_openSubHom U V)
  rintro X'' Y'' g p f'' hsq ⟨l, hl⟩
  let ι : representedAlgebraicSpace B S hS (openSub U V) ⟶ representedAlgebraicSpace B S hS U :=
    ObjectProperty.homMk (yoneda.map (openSubHom U V))
  let l' : Y'' ⟶ representedAlgebraicSpace B S hS (openSub U V) :=
    ObjectProperty.homMk (l ≫ inv (Subfunctor.toRange (yoneda.map (openSubHom U V))))
  have hl' : l' ≫ ι = g := by
    ext1
    change (l ≫ inv (Subfunctor.toRange _)) ≫ yoneda.map (openSubHom U V) = g.hom
    rwa [Category.assoc, (IsIso.inv_comp_eq _).2
      (Subfunctor.toRange_ι (yoneda.map (openSubHom U V))).symm]
  -- the base change of `f'` to `V`
  have hsq₁ := AlgebraicSpaces.isPullback_fiberProduct B S hS f' ι
  -- the given square is a base change of that one
  let pc : X'' ⟶ AlgebraicSpaces.fiberProduct B S hS f' ι :=
    hsq₁.lift p (f'' ≫ l') (by rw [Category.assoc, hl', hsq.w])
  have hpc : pc ≫ ObjectProperty.homMk (pullback.fst f'.hom ι.hom) = p := hsq₁.lift_fst _ _ _
  have hsqc : IsPullback pc f'' (ObjectProperty.homMk (pullback.snd f'.hom ι.hom)) l' :=
    IsPullback.of_right (by rwa [hpc, hl']) (hsq₁.lift_snd _ _ _) hsq₁
  rw [← hpc]
  exact (isRelativelyAmple_congr _ ((modulePullbackCompIso B S hS pc _).app L')).mp
    (isRelativelyAmple_baseChange hsqc _ (hV _ _ hsq₁))

/-- **The residue-field form of claim (A) with an open subspace, from the form with an open of the
scheme.** -/
theorem ampleSpreadsFromResidueFields_of_toOpens
    (h : AmpleSpreadsFromResidueFieldsToOpens B S hS) : AmpleSpreadsFromResidueFields B S hS := by
  intro U hU X' f' hf' L' hL' u hres
  obtain ⟨V, huV, hV⟩ := h U hU f' hf' L' hL' u hres
  refine ⟨Subfunctor.range (yoneda.map (openSubHom U V)),
    isOpenSubspace_subfunctorRange B S hS (isAlgebraicSpace_yoneda B S hS _)
      (isOpenImmersion_yoneda_map_openSubHom U V), fun t ht => ?_,
    isRelativelyAmpleOver_range_openSubHom f' L' V hV⟩
  obtain ⟨w, hw⟩ : t.class B S hS _ ∈ Set.range (pointsMap B S hS (yoneda.obj (openSub U V))
      (yoneda.map (openSubHom U V))) := by
    rw [range_pointsMap_yoneda_map_openSubHom]
    change pointsToScheme B S hS U (t.class B S hS _) ∈ V
    rwa [pointsToScheme_class, ht]
  refine ⟨pointsMap B S hS _ (Subfunctor.toRange (yoneda.map (openSubHom U V))) w, ?_⟩
  rwa [← pointsMap_comp_apply, Subfunctor.toRange_ι]

end AlgebraicGeometry.Space

end
