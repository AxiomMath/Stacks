module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleResidueFieldReduction

/-!
# Claim (A) of Stacks 0D3D from its residue-field form over affine schemes

The proof of Stacks 0D3D reduces its claim (A) — a field-valued point of the target over which
the pullback of `L` is ample has an open neighbourhood over which `L` is ample — first to affine
schemes `U` over the target and then, by Stacks 0D3C, to the residue fields `κ(u)` of points
of `U`. This file states the resulting residue-field form,
`AlgebraicGeometry.Space.AmpleSpreadsFromResidueFields`, for a proper morphism of algebraic
spaces to an affine scheme, and deduces from it, for any proper `f` and invertible `L`, the
form `AlgebraicGeometry.Space.AmpleNearFieldPointsOfAffines` of claim (A) which the
construction of the open locus consumes.

All declarations are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `AmpleSpreadsFromResidueFields`: for every proper morphism `f' : X' ⟶ h_U` of algebraic spaces
  to an affine scheme `U` of the site, every invertible `𝒪_{X'}`-module `L'` and every point `u` of
  `U` such that `L'` is ample over the base change of `f'` to `Spec κ(u)`, there is an open
  subspace of `h_U` containing the points over `u` over which `L'` is ample.

## Main results

* `ampleNearFieldPointsOfAffines_of_ampleSpreadsFromResidueFields`: claim (A) over affine
  schemes, for `f` proper and `L` invertible, from the residue-field form and the fpqc case of
  Stacks 0D3C.
* `exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_ampleSpreadsFromResidueFields`:
  the conclusion of Stacks 0D3D from the same two inputs.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D3C](https://stacks.math.columbia.edu/tag/0D3C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Claim (A) of the proof of Stacks 0D3D at residue fields over an affine scheme.** For
every affine scheme `U` of the site, every proper morphism `f' : X' ⟶ h_U` of algebraic spaces,
every invertible `𝒪_{X'}`-module `L'` and every point `u` of `U` such that the pullback of `L'`
is ample on every base change of `f'` along `Spec κ(u) ⟶ U`, there is an open subspace `W` of
`h_U` containing every point of `h_U` over `u`, over which `L'` is ample. -/
def AmpleSpreadsFromResidueFields : Prop :=
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
      ∃ W : Subfunctor (yoneda.obj U), IsOpenSubspace B S hS W ∧
        (∀ t : FieldValuedPoint B S hS (yoneda.obj U), schemePoint B S hS U t = u →
          t.class B S hS _ ∈ Set.range (pointsMap B S hS W.toFunctor W.ι)) ∧
        IsRelativelyAmpleOver f' L' W

variable {B S hS}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_relativeAmpleResidueFieldNeighbourhood :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_relativeAmpleResidueFieldNeighbourhood
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Claim (A) of Stacks 0D3D over affine schemes, from its residue-field form.** Let
`f : X ⟶ Y` be a proper morphism of algebraic spaces and `L` an invertible `𝒪_X`-module.
Granted the fpqc case of Stacks 0D3C and
`AlgebraicGeometry.Space.AmpleSpreadsFromResidueFields`, claim (A) holds over affine schemes
over `Y`.

For an affine `U` with `a : h_U ⟶ Y`, the base change `f_U : X_U ⟶ h_U` of `f` along `a` is
proper and the pullback `L_U` of `L` invertible. Ampleness over a field-valued point `r` of `U`
is ampleness over `r` for `f_U` (pasting), hence over the residue field of the point under `r`
(`AlgebraicGeometry.Space.isRelativelyAmple_residueField_of_fieldValuedPoint`); the residue-field
form gives an open subspace `W` of `h_U` over which `L_U` is ample, and ampleness over `W`
along `a` is ampleness of `L_U` over `W`, again by pasting. -/
theorem ampleNearFieldPointsOfAffines_of_ampleSpreadsFromResidueFields
    (hdesc : RelativeAmpleFpqcDescends B S hS) (hcore : AmpleSpreadsFromResidueFields B S hS)
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsProper B S hS f.hom)
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).property L) :
    AmpleNearFieldPointsOfAffines f L := by
  intro U hU a _ r X'' p'' f'' hsq hamp
  -- the base change of `f` to `U`
  let aₛ : representedAlgebraicSpace B S hS U ⟶ Y := ObjectProperty.homMk a
  let XU : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS f aₛ
  let pU : XU ⟶ X := ObjectProperty.homMk (pullback.fst f.hom aₛ.hom)
  let fU : XU ⟶ representedAlgebraicSpace B S hS U :=
    ObjectProperty.homMk (pullback.snd f.hom aₛ.hom)
  have hsqU : IsPullback pU fU f aₛ := AlgebraicSpaces.isPullback_fiberProduct B S hS f aₛ
  have hfU : IsProper B S hS fU.hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => IsProper B S hS k.hom)
      hsqU hf
  have hLU : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS XU.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS XU.1 XU.2).O)).property ((modulePullback B S hS pU).obj L) :=
    Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS pU) (L := L) (hL := hL)
  -- the square over `r` for `f_U`
  let rU : representedAlgebraicSpace B S hS r.siteObject ⟶ representedAlgebraicSpace B S hS U :=
    ObjectProperty.homMk (yonedaEquiv.symm r.value)
  have hra : rU ≫ aₛ = ObjectProperty.homMk (yonedaEquiv.symm r.value ≫ a) := rfl
  let p₁ : X'' ⟶ XU := hsqU.lift p'' (f'' ≫ rU) (by rw [Category.assoc, hra, hsq.w])
  have hp₁ : p₁ ≫ pU = p'' := hsqU.lift_fst _ _ _
  have hsq₁ : IsPullback p₁ f'' fU
      (ObjectProperty.homMk (yonedaEquiv.symm r.value ≫ 𝟙 (yoneda.obj U))) := by
    rw [Category.comp_id]
    exact IsPullback.of_right (by rwa [hp₁, hra]) (hsqU.lift_snd _ _ _) hsqU
  have hamp₁ : IsRelativelyAmple B S hS f''
      ((modulePullback B S hS p₁).obj ((modulePullback B S hS pU).obj L)) :=
    (isRelativelyAmple_congr _ ((modulePullbackCompIso B S hS p₁ pU).app L)).mpr (by rwa [hp₁])
  -- ampleness over the residue field, and the open subspace
  obtain ⟨W, hW, hpt, hampW⟩ := hcore U hU fU hfU _ hLU (schemePoint B S hS U r)
    fun X₀ p₀ f₀ h₀ => isRelativelyAmple_residueField_of_fieldValuedPoint fU
      ((modulePullback B S hS pU).obj L) hdesc hLU U (𝟙 _) r p₁ f'' hsq₁ hamp₁ (X' := X₀) p₀ f₀
      (by rwa [Category.comp_id])
  refine ⟨W, hW, hpt r rfl, ?_⟩
  -- ampleness over `W` along `a`
  rintro X' Y' g p f' hsq' ⟨l, hl⟩
  let gU : Y' ⟶ representedAlgebraicSpace B S hS U := ObjectProperty.homMk (l ≫ W.ι)
  have hg : gU ≫ aₛ = g := by
    ext1
    change (l ≫ W.ι) ≫ a = g.hom
    rwa [Category.assoc]
  let pU' : X' ⟶ XU := hsqU.lift p (f' ≫ gU) (by rw [Category.assoc, hg, hsq'.w])
  have hpU' : pU' ≫ pU = p := hsqU.lift_fst _ _ _
  rw [← hpU']
  exact (isRelativelyAmple_congr _ ((modulePullbackCompIso B S hS pU' pU).app L)).mp
    (hampW gU pU' f' (IsPullback.of_right (by rwa [hpU', hg]) (hsqU.lift_snd _ _ _) hsqU) ⟨l, rfl⟩)

/-- **The open subspace of Stacks 0D3D, from the residue-field form of claim (A).** Let
`f : X ⟶ Y` be a proper morphism of algebraic spaces and `L` an invertible `𝒪_X`-module.
Granted the fpqc case of Stacks 0D3C and `AlgebraicGeometry.Space.AmpleSpreadsFromResidueFields`,
there is an open subspace `V ⊆ Y` such that a morphism `g : Y' ⟶ Y` of algebraic spaces factors
through `V` if and only if the pullback of `L` to the base change of `f` along `g` is ample. -/
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_ampleSpreadsFromResidueFields
    (hdesc : RelativeAmpleFpqcDescends B S hS) (hcore : AmpleSpreadsFromResidueFields B S hS)
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsProper B S hS f.hom)
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).property L) :
    ∃ V : Subfunctor Y.1, IsOpenSubspace B S hS V ∧
      ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p f' f g →
          ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
            IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)) :=
  exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_ampleNearFieldPointsOfAffines hdesc hL
    (ampleNearFieldPointsOfAffines_of_ampleSpreadsFromResidueFields hdesc hcore hf hL)

end AlgebraicGeometry.Space

end
