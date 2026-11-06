module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeUnitSingle
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardDerivedTensor
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalModule
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceLimit
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityLimitStageDirected
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Convolution
public import StacksFrontier.AlgebraicGeometry.Intersection.ProductTorIndependence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Perfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.QcohPresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitPerfectCategoryColimit
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjectsCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# A relative equivalence over a limit of schemes comes from a finite stage, unconditionally

Let `S = lim_{i ∈ I} S_i` be the limit of a directed inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms, with a chosen index `0`, let
`X_0 ⟶ S_0` and `Y_0 ⟶ S_0` be smooth and proper, and put `X_i = X_0 ×_{S_0} S_i`,
`X = X_0 ×_{S_0} S` and likewise for `Y_0`. If `K` is the Fourier-Mukai kernel of a relative
equivalence from `X` to `Y` over `S`, then for some `i ≥ 0` there is a Fourier-Mukai kernel of a
relative equivalence from `X_i` to `Y_i` over `S_i`. This is [Stacks, Tag 0G0L].

`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/RelativeEquivalenceLimit.lean`
performs the source's assembly from four propositions: the two halves of [Stacks, Tag 09RF] read
along the tower of fibre products `X_i ×_{S_i} Y_i`, the base change of the diagonal kernel and
of the convolution kernel, and the perfectness of those two kernels. This module proves the four
propositions and so obtains [Stacks, Tag 0G0L] with no input beyond the source's hypotheses.

## Main results

* `AlgebraicGeometry.isPerfect_diagonalKernel` — for `f` smooth and separated the diagonal kernel
  `Δ_*𝒪_X` is perfect.
* `AlgebraicGeometry.isPerfect_fourierMukaiConvolution` — the convolution of two perfect kernels
  over a flat proper morphism of finite presentation is perfect.
* `AlgebraicGeometry.diagonalKernelAndConvolutionPerfect`,
  `AlgebraicGeometry.diagonalKernelAndConvolutionBaseChange`,
  `AlgebraicGeometry.perfectDescendsAlongBaseChangedTower` and
  `AlgebraicGeometry.perfectIsoDescendsAlongBaseChangedTower` — the four propositions.
* `AlgebraicGeometry.exists_isRelativeEquivalenceKernel_of_limit` — **[Stacks, Tag 0G0L]**.

## Implementation notes

*Perfectness.* The diagonal of a smooth morphism is a section of the smooth first projection,
hence a regular immersion ([Stacks, Tag 067R]), hence a local complete intersection morphism
([Stacks, Tag 069L]), hence perfect ([Stacks, Tag 069H]); the pushforward of the structure sheaf
along a perfect closed immersion is perfect ([Stacks, Tag 0G2E]), and the derived and the
ordinary pushforward agree along a closed immersion. The source cites [Stacks, Tag 0FDP] and
[Stacks, Tag 0B6G] here; the latter asks for a Noetherian base, which the stages `S_i` need not
be, and the route above needs none. For the convolution, `L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K'` is
perfect ([Stacks, Tag 09UA] and [Stacks, Tag 09JB]), hence perfect relative to the flat morphism
`pr_{13}` ([Stacks, Tag 0DI4]), and its direct image along `pr_{13}`, which is flat, proper and
of finite presentation as a base change of `Y ⟶ S`, is perfect ([Stacks, Tag 0DJT]).

*Base change.* The two isomorphisms are those of the source's proof of [Stacks, Tag 0G0K]:
[Stacks, Tag 08IB] (`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`) on the cartesian
square carrying the diagonal, with the Tor independence of [Stacks, Tag 0CTA], and on the
cartesian square carrying `pr_{13}`, which is flat. The tower's comparison morphisms are
`AlgebraicGeometry.baseChangeProduct`, attached to a factorisation `u ≫ s = s'`; the stage
`X_0 ×_{S_0} T'` is the base change of `X_0 ×_{S_0} T` along `u` by pasting
(`isPullback_baseChangeStage`), so the base-change isomorphisms are proved for an arbitrary
cartesian square, and the Tor independence of [Stacks, Tag 0CTA], which this library states at
the chosen pullbacks, is transported to it along the comparison isomorphism of the two pullbacks
(`AlgebraicGeometry.TorIndependent.iso_left`). The isomorphisms of
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/RelativeEquivalenceBaseChange.lean`
are private to that module and stated only at the chosen pullbacks `X ×_S S₁`, which the stages
of the tower are not, so the cartesian-square form is proved here.

*The tower is a situation of [Stacks, Tag 09RD].* The stages `X_i ×_{S_i} Y_i` for `i ≥ 0`, with
the comparison morphisms as transitions, form `AlgebraicGeometry.towerSituation`. Its limit is
proved by identifying the tower with the base change of the system along
`X_0 ×_{S_0} Y_0 ⟶ S_0`, whose limit is `AlgebraicGeometry.isLimitDirectedBaseChangeCone`; the
identification is the canonical isomorphism
`X_0 ×_{S_0} T ×_T Y_0 ×_{S_0} T ≅ T ×_{S_0} (X_0 ×_{S_0} Y_0)`, natural in `T`. The two halves
of [Stacks, Tag 09RF] along the tower are then
`AlgebraicGeometry.DescentSituation.perfect_isColimit` at this situation.

*Universes.* The index set lies in the universe of the schemes, as in [Stacks, Tag 09RE], over
which the two halves of [Stacks, Tag 09RF] are proved; over a larger index set [Stacks, Tag 09RE]
fails (`AlgebraicGeometry.DescentSituation.exists_not_isHomColimit`).

## References

* [Stacks Project, Tag 0G0L](https://stacks.math.columbia.edu/tag/0G0L)
* [Stacks Project, Tag 0G0K](https://stacks.math.columbia.edu/tag/0G0K)
* [Stacks Project, Tag 09RF](https://stacks.math.columbia.edu/tag/09RF)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0CTA](https://stacks.math.columbia.edu/tag/0CTA)
* [Stacks Project, Tag 0DJT](https://stacks.math.columbia.edu/tag/0DJT)
* [Stacks Project, Tag 0G2E](https://stacks.math.columbia.edu/tag/0G2E)
* [Stacks Project, Tag 067R](https://stacks.math.columbia.edu/tag/067R)
* [Stacks Project, Tag 069H](https://stacks.math.columbia.edu/tag/069H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

universe u

/-! ### Perfectness of the two kernels -/

section Perfect

variable {S X Y : Scheme.{u}}

/-- **The diagonal of a smooth morphism is perfect**: it is a section of the smooth first
projection, hence a regular immersion ([Stacks, Tag 067R]), hence a local complete intersection
morphism ([Stacks, Tag 069L]), hence perfect ([Stacks, Tag 069H]). -/
theorem perfect_diagonal_of_smooth (f : X ⟶ S) [Smooth f] : Perfect (pullback.diagonal f) := by
  have : Smooth (pullback.fst f f) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f f).flip inferInstance
  exact perfect_of_isLocalCompleteIntersectionMorphism
    (isLocalCompleteIntersectionMorphism_of_isRegularImmersion (pullback.diagonal f)
      (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section (pullback.fst f f)
        (pullback.diagonal f) (pullback.diagonal_fst f)))

/-- **The diagonal kernel of a smooth separated morphism is perfect.** The diagonal is a perfect
closed immersion, so `Δ_*𝒪_X` is perfect by [Stacks, Tag 0G2E], and it is the diagonal kernel
`RΔ_*𝒪_X` because derived and ordinary pushforward agree along a closed immersion. -/
theorem isPerfect_diagonalKernel (f : X ⟶ S) [Smooth f] [IsSeparated f] :
    IsPerfect (X := (pullback f f).toRingedSpace) (diagonalKernel f) := by
  have := perfect_diagonal_of_smooth f
  exact Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_iso
    (diagonalKernelIsoDiagonalModule f).symm
    (isPerfect_pushforward_structureSheaf (pullback.diagonal f))

/-- The derived direct image along a morphism of schemes, in the spelling of the convolution
kernel, is the one of `AlgebraicGeometry.derivedPushforwardModules`. -/
theorem dpush_obj_eq_derivedPushforwardModules_obj {V W : Scheme.{u}} (p : V ⟶ W)
    (M : DerivedCategory V.Modules) : (dpush p).obj M = (derivedPushforwardModules p).obj M :=
  rfl

/-- **The complex `L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K'` of two perfect kernels is perfect**, by
[Stacks, Tag 09UA] and [Stacks, Tag 09JB]. -/
theorem isPerfect_fourierMukaiConvolutionTensor (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory (pullback f g).Modules) (K' : DerivedCategory (pullback g f).Modules)
    (hK : IsPerfect (X := (pullback f g).toRingedSpace) K)
    (hK' : IsPerfect (X := (pullback g f).toRingedSpace) K') :
    IsPerfect (X := (fourierMukaiTripleProduct f g f).toRingedSpace)
      (fourierMukaiConvolutionTensor f g f K K') :=
  RingedSpace.isPerfect_canonicalDerivedTensorProduct
    (fourierMukaiTripleProduct f g f).toRingedSpace
    ((derivedPullback (fourierMukaiPr12 f g f).toLRSHom.toShHom).obj K)
    ((derivedPullback (fourierMukaiPr23 f g f).toLRSHom.toShHom).obj K')
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (fourierMukaiPr12 f g f).toLRSHom.toShHom K hK)
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (fourierMukaiPr23 f g f).toLRSHom.toShHom K' hK')

/-- **The convolution of two perfect kernels is perfect** when the middle morphism `g` is flat,
proper and of finite presentation. The complex `L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K'` is perfect
(`AlgebraicGeometry.isPerfect_fourierMukaiConvolutionTensor`), hence perfect relative to the flat
morphism `pr_{13}` ([Stacks, Tag 0DI4]), and `pr_{13}`, a base change of `g`, is flat, proper and
of finite presentation, so its derived direct image is perfect by [Stacks, Tag 0DJT]. -/
theorem isPerfect_fourierMukaiConvolution (f : X ⟶ S) (g : Y ⟶ S) [Flat g] [IsProper g]
    [LocallyOfFinitePresentation g] (K : DerivedCategory (pullback f g).Modules)
    (K' : DerivedCategory (pullback g f).Modules)
    (hK : IsPerfect (X := (pullback f g).toRingedSpace) K)
    (hK' : IsPerfect (X := (pullback g f).toRingedSpace) K') :
    IsPerfect (X := (pullback f f).toRingedSpace) (fourierMukaiConvolution f g f K K') := by
  have hsq := isPullback_fourierMukaiPr12_pr13 f g f
  have : Flat (fourierMukaiPr13 f g f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : IsProper (fourierMukaiPr13 f g f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : LocallyOfFinitePresentation (fourierMukaiPr13 f g f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  rw [fourierMukaiConvolution, dpush_obj_eq_derivedPushforwardModules_obj]
  exact open Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward in
    isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_flat _ _
      (Scheme.Hom.isPerfectRelativeTo_canonical_of_isPerfect _ _
        (isPerfect_fourierMukaiConvolutionTensor f g K K' hK hK'))

/-- **The diagonal kernel and the convolution kernel of perfect kernels are perfect**, for smooth
proper morphisms: the proposition `AlgebraicGeometry.DiagonalKernelAndConvolutionPerfect`. -/
theorem diagonalKernelAndConvolutionPerfect : DiagonalKernelAndConvolutionPerfect.{u} :=
  fun f g _ _ _ _ => ⟨isPerfect_diagonalKernel f,
    fun K K' hK hK' => isPerfect_fourierMukaiConvolution f g K K' hK hK'⟩

end Perfect

/-! ### Base change of the two kernels along a cartesian square -/

section Squares

universe v' u'

variable {C : Type u'} [Category.{v'} C] [HasPullbacks C]

section

variable {S S₁ X Y X₁ Y₁ : C} {f : X ⟶ S} {g : Y ⟶ S} {s : S₁ ⟶ S}
  {cX : X₁ ⟶ X} {f₁ : X₁ ⟶ S₁} {cY : Y₁ ⟶ Y} {g₁ : Y₁ ⟶ S₁}

/-- The comparison from the fibre product of two base changes to the original fibre product. -/
private abbrev prodMap (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    pullback f₁ g₁ ⟶ pullback f g :=
  pullback.map f₁ g₁ f g cX cY s hX.w.symm hY.w.symm

@[reassoc (attr := simp)]
private lemma prodMap_fst (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    prodMap hX hY ≫ pullback.fst f g = pullback.fst f₁ g₁ ≫ cX :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma prodMap_snd (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    prodMap hX hY ≫ pullback.snd f g = pullback.snd f₁ g₁ ≫ cY :=
  pullback.lift_snd _ _ _

/-- The second projection of a fibre product is compatible with base change. -/
private lemma isPullback_prodMap_snd (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    IsPullback (prodMap hX hY) (pullback.snd f₁ g₁) (pullback.snd f g) cY := by
  refine IsPullback.of_right ?_ (prodMap_snd hX hY) (IsPullback.of_hasPullback f g)
  have h := (IsPullback.of_hasPullback f₁ g₁).paste_horiz hX
  rw [prodMap_fst hX hY, ← hY.w] at *
  exact h

/-- The fibre product of two base changes is the base change of the fibre product. -/
private lemma isPullback_prodMap_base (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    IsPullback (prodMap hX hY) (pullback.snd f₁ g₁ ≫ g₁) (pullback.snd f g ≫ g) s :=
  (isPullback_prodMap_snd hX hY).paste_vert hY

/-- The diagonal is compatible with base change. -/
private lemma isPullback_prodMap_diagonal (hX : IsPullback cX f₁ f s) :
    IsPullback cX (pullback.diagonal f₁) (pullback.diagonal f) (prodMap hX hX) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_prodMap_snd hX hX)
  · simpa using (IsPullback.of_id_snd (f := cX))
  · apply pullback.hom_ext <;> simp

end

section Triple

variable {S S₁ X Y X₁ Y₁ : C} {f : X ⟶ S} {g : Y ⟶ S} {s : S₁ ⟶ S}
  {cX : X₁ ⟶ X} {f₁ : X₁ ⟶ S₁} {cY : Y₁ ⟶ Y} {g₁ : Y₁ ⟶ S₁}

/-- The projection `pr₁₃` of the left-associated triple fibre product `X ×_S Y ×_S X`. -/
private def tripleP13 (f : X ⟶ S) (g : Y ⟶ S) :
    pullback (pullback.snd f g ≫ g) f ⟶ pullback f f :=
  pullback.lift (pullback.fst (pullback.snd f g ≫ g) f ≫ pullback.fst f g)
    (pullback.snd (pullback.snd f g ≫ g) f)
    (by
      have h₁ : pullback.fst f g ≫ f = pullback.snd f g ≫ g := pullback.condition
      have h₂ : pullback.fst (pullback.snd f g ≫ g) f ≫ (pullback.snd f g ≫ g) =
          pullback.snd (pullback.snd f g ≫ g) f ≫ f := pullback.condition
      rw [Category.assoc, h₁, h₂])

@[reassoc (attr := simp)]
private lemma tripleP13_fst :
    tripleP13 f g ≫ pullback.fst f f =
      pullback.fst (pullback.snd f g ≫ g) f ≫ pullback.fst f g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma tripleP13_snd :
    tripleP13 f g ≫ pullback.snd f f = pullback.snd (pullback.snd f g ≫ g) f :=
  pullback.lift_snd _ _ _

/-- **`pr₁₃` is compatible with base change.** -/
private lemma isPullback_tripleP13 (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    IsPullback (prodMap (isPullback_prodMap_base hX hY) hX) (tripleP13 f₁ g₁)
      (tripleP13 f g) (prodMap hX hX) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_prodMap_snd hX hX)
  · rw [tripleP13_snd, tripleP13_snd]
    exact isPullback_prodMap_snd (isPullback_prodMap_base hX hY) hX
  · apply pullback.hom_ext <;> simp

end Triple

end Squares

section BaseChange

variable {V W : Scheme.{u}}

/-- `pr₁₃` of the triple fibre product is `AlgebraicGeometry.fourierMukaiPr13`. -/
private lemma tripleP13_eq {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    tripleP13 f g = fourierMukaiPr13 f g f := by
  apply pullback.hom_ext <;> simp [tripleP13, fourierMukaiPr13]

/-- The derived pullback of the structure sheaf in degree zero is the structure sheaf in degree
zero, `𝒪_W` being flat. -/
private def dpullUnitIso (p : V ⟶ W) :
    (dpull p).obj ((DerivedCategory.singleFunctor W.Modules 0).obj
        (SheafOfModules.unit W.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor V.Modules 0).obj (SheafOfModules.unit V.ringCatSheaf) :=
  Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso p.toLRSHom.toShHom _
      (Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_structureSheafModule
        W.toRingedSpace) ≪≫
    (DerivedCategory.singleFunctor V.Modules 0).mapIso
      (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso p.toLRSHom.toShHom)

/-- **Tor independence for the diagonal square** ([Stacks, Tag 0CTA]): for `f` flat, `X` and
`X₁ ×_{S₁} X₁` are Tor independent over `X ×_S X`, for any cartesian square exhibiting `X₁` as
the base change of `X` along `S₁ ⟶ S`. -/
private lemma torIndependent_diagonal_prodMap {S X S₁ X₁ : Scheme.{u}} {f : X ⟶ S}
    {f₁ : X₁ ⟶ S₁} {cX : X₁ ⟶ X} {s : S₁ ⟶ S} (hX : IsPullback cX f₁ f s) [Flat f] :
    TorIndependent (pullback.diagonal f) (prodMap hX hX) := by
  have h0 : TorIndependent (fourierMukaiBaseChangeMap f f s) (pullback.diagonal f) :=
    torIndependent_pullback_product_of_flat s f f (𝟙 X) (𝟙 X) rfl
  let e₀ : pullback f₁ f₁ ⟶ pullback (pullback.snd f s) (pullback.snd f s) :=
    pullback.map f₁ f₁ (pullback.snd f s) (pullback.snd f s) hX.isoPullback.hom
      hX.isoPullback.hom (𝟙 S₁) (by simp) (by simp)
  have : IsIso e₀ := by
    dsimp only [e₀]
    infer_instance
  have h1 := TorIndependent.iso_left (asIso e₀) h0
  have he : (asIso e₀).hom ≫ fourierMukaiBaseChangeMap f f s = prodMap hX hX := by
    apply pullback.hom_ext <;> simp [e₀, fourierMukaiBaseChangeMap]
  rw [he] at h1
  exact h1.symm

/-- [Stacks, Tag 08IB] on the cartesian square carrying the two diagonals, at `𝒪_X` in degree
zero. -/
private lemma isIso_derivedBaseChangeMap_diagonal {S X S₁ X₁ : Scheme.{u}} {f : X ⟶ S}
    {f₁ : X₁ ⟶ S₁} {cX : X₁ ⟶ X} {s : S₁ ⟶ S} (hX : IsPullback cX f₁ f s)
    [IsSeparated f] [Flat f] :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap cX.toLRSHom.toShHom
      (pullback.diagonal f₁).toLRSHom.toShHom (pullback.diagonal f).toLRSHom.toShHom
      (prodMap hX hX).toLRSHom.toShHom (shHom_comp_eq (isPullback_prodMap_diagonal hX).w)
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit X.ringCatSheaf))) :=
  derivedBaseChangeIsIsoOnQuasicoherent _ _ _ _ (isPullback_prodMap_diagonal hX) inferInstance
    inferInstance (torIndependent_diagonal_prodMap hX) _ _
    (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_homology_singleFunctor_obj
      0 _ (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X))

/-- **The diagonal kernel commutes with base change** along any cartesian square exhibiting `X₁`
as the base change of `X` along `S₁ ⟶ S`, for `f` flat and separated: [Stacks, Tag 08IB] on the
cartesian square carrying the two diagonals, whose Tor independence is
[Stacks, Tag 0CTA]. -/
private def diagonalKernelBaseChangeIso {S X S₁ X₁ : Scheme.{u}} {f : X ⟶ S}
    {f₁ : X₁ ⟶ S₁} {cX : X₁ ⟶ X} {s : S₁ ⟶ S} (hX : IsPullback cX f₁ f s)
    [IsSeparated f] [Flat f] :
    (dpull (prodMap hX hX)).obj (diagonalKernel f) ≅ diagonalKernel f₁ :=
  @asIso _ _ _ _ _ (isIso_derivedBaseChangeMap_diagonal hX) ≪≫
    (dpush (pullback.diagonal f₁)).mapIso (dpullUnitIso cX)

/-- **The convolution kernel commutes with base change** along cartesian squares exhibiting `X₁`
and `Y₁` as base changes of `X` and `Y` along `S₁ ⟶ S`, for `g` flat: [Stacks, Tag 08IB] on the
cartesian square carrying `pr₁₃`, which is flat, then the monoidality of derived pullback and
the composition isomorphisms. -/
private def convolutionBaseChangeIso {S X Y S₁ X₁ Y₁ : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f₁ : X₁ ⟶ S₁} {g₁ : Y₁ ⟶ S₁} {cX : X₁ ⟶ X} {cY : Y₁ ⟶ Y} {s : S₁ ⟶ S}
    (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] [Flat g]
    {K : DerivedCategory (pullback f g).Modules} (hK : IsQCohAll K)
    {K' : DerivedCategory (pullback g f).Modules} (hK' : IsQCohAll K') :
    (dpull (prodMap hX hX)).obj (fourierMukaiConvolution f g f K K') ≅
      fourierMukaiConvolution f₁ g₁ f₁ ((dpull (prodMap hX hY)).obj K)
        ((dpull (prodMap hY hX)).obj K') := by
  have hA1 : IsPullback (prodMap (isPullback_prodMap_base hX hY) hX)
      (fourierMukaiPr13 f₁ g₁ f₁) (fourierMukaiPr13 f g f) (prodMap hX hX) := by
    rw [← tripleP13_eq, ← tripleP13_eq]
    exact isPullback_tripleP13 hX hY
  have hsq := shHom_comp_eq hA1.w
  haveI : Flat (fourierMukaiPr13 f g f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_fourierMukaiPr12_pr13 f g f) inferInstance
  have htor : TorIndependent (fourierMukaiPr13 f g f) (prodMap hX hX) :=
    torIndependent_of_flat_left _ _
  have hM : IsQCohAll (fourierMukaiConvolutionTensor f g f K K') :=
    isQCohAll_dtenR (isQCohAll_dpull _ hK) (isQCohAll_dpull _ hK')
  have h12 : prodMap (isPullback_prodMap_base hX hY) hX ≫ fourierMukaiPr12 f g f =
      fourierMukaiPr12 f₁ g₁ f₁ ≫ prodMap hX hY := prodMap_fst _ _
  have h23 : prodMap (isPullback_prodMap_base hX hY) hX ≫ fourierMukaiPr23 f g f =
      fourierMukaiPr23 f₁ g₁ f₁ ≫ prodMap hY hX := by
    apply pullback.hom_ext <;>
      simp [fourierMukaiPr23, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  have hiso : IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
      (prodMap (isPullback_prodMap_base hX hY) hX).toLRSHom.toShHom
      (fourierMukaiPr13 f₁ g₁ f₁).toLRSHom.toShHom (fourierMukaiPr13 f g f).toLRSHom.toShHom
      (prodMap hX hX).toLRSHom.toShHom hsq (fourierMukaiConvolutionTensor f g f K K')) :=
    derivedBaseChangeIsIsoOnQuasicoherent _ _ _ _ hA1 inferInstance inferInstance htor hsq _ hM
  refine @asIso _ _ _ _ _ hiso ≪≫
    (dpush (fourierMukaiPr13 f₁ g₁ f₁)).mapIso ?_
  refine (dpullTensorIso (prodMap (isPullback_prodMap_base hX hY) hX)
      ((dpull (fourierMukaiPr23 f g f)).obj K')).app
      ((dpull (fourierMukaiPr12 f g f)).obj K) ≪≫ ?_
  exact (dtenR _ _).mapIso
      ((dpullCompIsoEq (prodMap (isPullback_prodMap_base hX hY) hX) (fourierMukaiPr12 f g f)
        (fourierMukaiPr12 f₁ g₁ f₁) (prodMap hX hY) h12).app K) ≪≫
    ((derivedTensorProductFunctor _).flip.mapIso
      ((dpullCompIsoEq (prodMap (isPullback_prodMap_base hX hY) hX) (fourierMukaiPr23 f g f)
        (fourierMukaiPr23 f₁ g₁ f₁) (prodMap hY hX) h23).app K')).app _

/-- **The stage `X₀ ×_{S₀} T'` is the base change of the stage `X₀ ×_{S₀} T` along `T' ⟶ T`**,
by pasting cartesian squares. -/
theorem isPullback_baseChangeStage {S₀ X₀ T T' : Scheme.{u}} (x : X₀ ⟶ S₀) {s : T ⟶ S₀}
    {s' : T' ⟶ S₀} {u : T' ⟶ T} (hu : u ≫ s = s') :
    IsPullback (baseChangeStage x hu) (pullback.snd x s') (pullback.snd x s) u := by
  refine IsPullback.of_right ?_ (baseChangeStage_snd x hu) (IsPullback.of_hasPullback x s)
  rw [baseChangeStage_fst, hu]
  exact IsPullback.of_hasPullback x s'

/-- **The diagonal kernel and the convolution kernel commute with base change along the tower**:
the proposition `AlgebraicGeometry.DiagonalKernelAndConvolutionBaseChange`, for smooth proper
morphisms `X₀ ⟶ S₀` and `Y₀ ⟶ S₀` and any factorisation `u ≫ s = s'`. -/
theorem diagonalKernelAndConvolutionBaseChange : DiagonalKernelAndConvolutionBaseChange.{u} := by
  intro S₀ X₀ Y₀ T T' x y s s' u hu _ _ _ _
  have hX := isPullback_baseChangeStage x hu
  have hY := isPullback_baseChangeStage y hu
  exact ⟨⟨diagonalKernelBaseChangeIso hX⟩, fun K K' hK hK' => ⟨convolutionBaseChangeIso hX hY
    (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K hK)
    (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K' hK')⟩⟩

end BaseChange

/-! ### The tower of fibre products is a situation of Tag 09RD -/

section TowerIso

variable {S₀ X₀ Y₀ T T' : Scheme.{u}} (x : X₀ ⟶ S₀) (y : Y₀ ⟶ S₀)

/-- The structure morphism `X₀ ×_{S₀} Y₀ ⟶ S₀`. -/
abbrev productToBase : pullback x y ⟶ S₀ := pullback.fst x y ≫ x

/-- The comparison `X_T ×_T Y_T ⟶ T ×_{S₀} (X₀ ×_{S₀} Y₀)`. -/
def towerProductHom (s : T ⟶ S₀) :
    pullback (pullback.snd x s) (pullback.snd y s) ⟶ pullback s (productToBase x y) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd x s)
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst x s) (pullback.snd _ _ ≫ pullback.fst y s)
      (by
        rw [Category.assoc, Category.assoc, pullback.condition (f := x) (g := s),
          ← Category.assoc, pullback.condition (f := pullback.snd x s) (g := pullback.snd y s),
          Category.assoc, ← pullback.condition (f := y) (g := s)]))
    (by
      rw [productToBase, ← Category.assoc (pullback.lift _ _ _), pullback.lift_fst,
        Category.assoc, Category.assoc, pullback.condition (f := x) (g := s)])

/-- The comparison `T ×_{S₀} (X₀ ×_{S₀} Y₀) ⟶ X_T ×_T Y_T`. -/
def towerProductInv (s : T ⟶ S₀) :
    pullback s (productToBase x y) ⟶ pullback (pullback.snd x s) (pullback.snd y s) :=
  pullback.lift
    (pullback.lift (pullback.snd _ _ ≫ pullback.fst x y) (pullback.fst _ _)
      (by
        rw [Category.assoc]
        exact (pullback.condition (f := s) (g := productToBase x y)).symm))
    (pullback.lift (pullback.snd _ _ ≫ pullback.snd x y) (pullback.fst _ _)
      (by
        rw [Category.assoc, ← pullback.condition (f := x) (g := y)]
        exact (pullback.condition (f := s) (g := productToBase x y)).symm))
    (by rw [pullback.lift_snd, pullback.lift_snd])

/-- The composite of `towerProductHom` with the projection to `T` is the composite projection
`X_T ×_T Y_T ⟶ X_T ⟶ T`. -/
@[reassoc (attr := simp)]
lemma towerProductHom_fst (s : T ⟶ S₀) :
    towerProductHom x y s ≫ pullback.fst s (productToBase x y) =
      pullback.fst _ _ ≫ pullback.snd x s :=
  pullback.lift_fst _ _ _

/-- The composite of `towerProductHom` with the projection to `X₀` is the projection
`X_T ×_T Y_T ⟶ X_T ⟶ X₀`. -/
@[reassoc (attr := simp)]
lemma towerProductHom_snd_fst (s : T ⟶ S₀) :
    towerProductHom x y s ≫ pullback.snd s (productToBase x y) ≫ pullback.fst x y =
      pullback.fst _ _ ≫ pullback.fst x s := by
  rw [towerProductHom, pullback.lift_snd_assoc, pullback.lift_fst]

/-- The composite of `towerProductHom` with the projection to `Y₀` is the projection
`X_T ×_T Y_T ⟶ Y_T ⟶ Y₀`. -/
@[reassoc (attr := simp)]
lemma towerProductHom_snd_snd (s : T ⟶ S₀) :
    towerProductHom x y s ≫ pullback.snd s (productToBase x y) ≫ pullback.snd x y =
      pullback.snd _ _ ≫ pullback.fst y s := by
  rw [towerProductHom, pullback.lift_snd_assoc, pullback.lift_snd]

/-- The composite of `towerProductInv` with the projection `X_T ×_T Y_T ⟶ X_T ⟶ X₀` is the
projection `T ×_{S₀} (X₀ ×_{S₀} Y₀) ⟶ X₀`. -/
@[reassoc (attr := simp)]
lemma towerProductInv_fst_fst (s : T ⟶ S₀) :
    towerProductInv x y s ≫ pullback.fst _ _ ≫ pullback.fst x s =
      pullback.snd s (productToBase x y) ≫ pullback.fst x y := by
  rw [towerProductInv, pullback.lift_fst_assoc, pullback.lift_fst]

/-- The composite of `towerProductInv` with the projection `X_T ×_T Y_T ⟶ X_T ⟶ T` is the
projection `T ×_{S₀} (X₀ ×_{S₀} Y₀) ⟶ T`. -/
@[reassoc (attr := simp)]
lemma towerProductInv_fst_snd (s : T ⟶ S₀) :
    towerProductInv x y s ≫ pullback.fst _ _ ≫ pullback.snd x s =
      pullback.fst s (productToBase x y) := by
  rw [towerProductInv, pullback.lift_fst_assoc, pullback.lift_snd]

/-- The composite of `towerProductInv` with the projection `X_T ×_T Y_T ⟶ Y_T ⟶ Y₀` is the
projection `T ×_{S₀} (X₀ ×_{S₀} Y₀) ⟶ Y₀`. -/
@[reassoc (attr := simp)]
lemma towerProductInv_snd_fst (s : T ⟶ S₀) :
    towerProductInv x y s ≫ pullback.snd _ _ ≫ pullback.fst y s =
      pullback.snd s (productToBase x y) ≫ pullback.snd x y := by
  rw [towerProductInv, pullback.lift_snd_assoc, pullback.lift_fst]

/-- The composite of `towerProductInv` with the projection `X_T ×_T Y_T ⟶ Y_T ⟶ T` is the
projection `T ×_{S₀} (X₀ ×_{S₀} Y₀) ⟶ T`. -/
@[reassoc (attr := simp)]
lemma towerProductInv_snd_snd (s : T ⟶ S₀) :
    towerProductInv x y s ≫ pullback.snd _ _ ≫ pullback.snd y s =
      pullback.fst s (productToBase x y) := by
  rw [towerProductInv, pullback.lift_snd_assoc, pullback.lift_snd]

/-- **The canonical isomorphism `X_T ×_T Y_T ≅ T ×_{S₀} (X₀ ×_{S₀} Y₀)`** for a scheme `T` over
`S₀`, where `X_T = X₀ ×_{S₀} T` and `Y_T = Y₀ ×_{S₀} T`. -/
def towerProductIso (s : T ⟶ S₀) :
    pullback (pullback.snd x s) (pullback.snd y s) ≅ pullback s (productToBase x y) where
  hom := towerProductHom x y s
  inv := towerProductInv x y s
  hom_inv_id := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp only [Category.assoc, towerProductHom_fst, towerProductHom_snd_fst,
        towerProductHom_snd_snd, towerProductInv_fst_fst, towerProductInv_fst_snd,
        towerProductInv_snd_fst, towerProductInv_snd_snd, Category.id_comp]
    exact pullback.condition
  inv_hom_id := by
    apply pullback.hom_ext <;> (try apply pullback.hom_ext) <;>
      simp only [Category.assoc, towerProductHom_fst, towerProductHom_snd_fst,
        towerProductHom_snd_snd, towerProductInv_fst_fst, towerProductInv_fst_snd,
        towerProductInv_snd_fst, Category.id_comp]

/-- **Naturality of `AlgebraicGeometry.towerProductHom`** along a factorisation `u ≫ s = s'`:
it intertwines the comparison of the fibre products with the base change of `u`. -/
lemma baseChangeProduct_towerProductHom {s : T ⟶ S₀} {s' : T' ⟶ S₀} {u : T' ⟶ T}
    (hu : u ≫ s = s') :
    baseChangeProduct x y hu ≫ towerProductHom x y s =
      towerProductHom x y s' ≫ pullback.map s' (productToBase x y) s (productToBase x y) u
        (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hu])
        (by rw [Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, towerProductHom_fst, pullback.lift_fst,
      towerProductHom_fst_assoc, baseChangeProduct_fst_assoc, baseChangeStage_snd]
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, towerProductHom_snd_fst,
        pullback.lift_snd_assoc, Category.comp_id, towerProductHom_snd_fst,
        baseChangeProduct_fst_assoc, baseChangeStage_fst]
    · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, towerProductHom_snd_snd,
        pullback.lift_snd_assoc, Category.comp_id, towerProductHom_snd_snd,
        baseChangeProduct_snd_assoc, baseChangeStage_fst]

/-- The comparison of the stages attached to `u = 𝟙` is the identity. -/
lemma baseChangeStage_id {s : T ⟶ S₀} (hu : 𝟙 T ≫ s = s) : baseChangeStage x hu = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- The comparison of the fibre products attached to `u = 𝟙` is the identity. -/
lemma baseChangeProduct_of_eq_id {s : T ⟶ S₀} {u : T ⟶ T} (hu : u ≫ s = s) (h : u = 𝟙 T) :
    baseChangeProduct x y hu = 𝟙 _ := by
  subst h
  apply pullback.hom_ext <;> simp [baseChangeStage_id]

end TowerIso

section Tower

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation.{u, u} I)
  {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base) (y : Y₀ ⟶ D.stage D.base)

/-- **The tower of fibre products** `i ↦ X_i ×_{S_i} Y_i` over the stages `i ≥ 0`, with the
comparison morphisms `AlgebraicGeometry.baseChangeProduct` as transition morphisms. -/
def towerDiagram : D.Stagesᵒᵖ ⥤ Scheme.{u} where
  obj k := pullback (pullback.snd x (D.transition k.unop.2))
    (pullback.snd y (D.transition k.unop.2))
  map {k k'} e := baseChangeProduct x y
    (D.transition_comp_transition k'.unop.2 (show k'.unop.1 ≤ k.unop.1 from leOfHom e.unop))
  map_id k := baseChangeProduct_of_eq_id x y _ (D.transition_refl k.unop.1)
  map_comp {k k' k''} e e' := (baseChangeProduct_comp x y _ _ _
    (D.transition_comp_transition (show k''.unop.1 ≤ k'.unop.1 from leOfHom e'.unop)
      (show k'.unop.1 ≤ k.unop.1 from leOfHom e.unop))).symm

/-- **The cone of the tower with apex `X ×_S Y`**, whose legs are the comparison morphisms from
the limit. -/
def towerCone : Cone (towerDiagram D x y) where
  pt := pullback (pullback.snd x (D.projection D.base)) (pullback.snd y (D.projection D.base))
  π :=
    { app k := baseChangeProduct x y (D.projection_comp_transition k.unop.2)
      naturality {k k'} e := by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map, towerDiagram]
        rw [Category.id_comp]
        exact (baseChangeProduct_comp x y _ _ _
          (D.projection_comp_transition (show k'.unop.1 ≤ k.unop.1 from leOfHom e.unop))).symm }

/-- The transition morphisms of the base-changed system are base changes of the transition
morphisms of the system. -/
lemma directedBaseChangeDiagram_map_eq {k k' : D.Stagesᵒᵖ} (e : k ⟶ k') :
    (directedBaseChangeDiagram D.system D.base (productToBase x y)).map e =
      pullback.map (D.transition k.unop.2) (productToBase x y) (D.transition k'.unop.2)
        (productToBase x y) (D.transition (show k'.unop.1 ≤ k.unop.1 from leOfHom e.unop))
        (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, D.transition_comp_transition])
        (by rw [Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · exact (directedBaseChangeDiagram_map_fst D.system D.base (productToBase x y) e).trans
      (pullback.lift_fst _ _ _).symm
  · exact (directedBaseChangeDiagram_map_snd D.system D.base (productToBase x y) e).trans
      ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm

/-- The legs of the base-changed cone are base changes of the projections of the system. -/
lemma directedBaseChangeCone_π_eq (k : D.Stagesᵒᵖ) :
    (directedBaseChangeCone D.system D.base (productToBase x y) D.limitCone).π.app k =
      pullback.map (D.projection D.base) (productToBase x y) (D.transition k.unop.2)
        (productToBase x y) (D.projection k.unop.1) (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, D.projection_comp_transition])
        (by rw [Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · exact (directedBaseChangeCone_π_fst D.system D.base (productToBase x y) D.limitCone
      k.unop).trans (pullback.lift_fst _ _ _).symm
  · exact (directedBaseChangeCone_π_snd D.system D.base (productToBase x y) D.limitCone
      k.unop).trans ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm

/-- The tower is isomorphic to the base change of the system along `X₀ ×_{S₀} Y₀ ⟶ S₀`. -/
def towerDiagramIso :
    towerDiagram D x y ≅ directedBaseChangeDiagram D.system D.base (productToBase x y) :=
  NatIso.ofComponents (fun k => towerProductIso x y (D.transition k.unop.2)) (by
    intro k k' e
    rw [directedBaseChangeDiagram_map_eq]
    exact baseChangeProduct_towerProductHom x y _)

/-- The cone of the tower, transported along `AlgebraicGeometry.towerDiagramIso`, is the cone of
the base-changed system with apex `S ×_{S₀} (X₀ ×_{S₀} Y₀)`. -/
def towerConeIso : (Cone.postcompose (towerDiagramIso D x y).hom).obj (towerCone D x y) ≅
    directedBaseChangeCone D.system D.base (productToBase x y) D.limitCone :=
  Cone.ext (towerProductIso x y (D.projection D.base)) (by
    intro k
    rw [directedBaseChangeCone_π_eq]
    exact baseChangeProduct_towerProductHom x y _)

/-- **The limit of the tower of fibre products is `X ×_S Y`.** -/
def isLimitTowerCone : IsLimit (towerCone D x y) :=
  haveI : Nonempty I := ⟨D.base⟩
  (IsLimit.equivOfNatIsoOfIso (towerDiagramIso D x y) _ _ (towerConeIso D x y)).symm
    (isLimitDirectedBaseChangeCone D.system D.base (productToBase x y) D.limitCone D.isLimit)

variable [QuasiCompact x] [QuasiSeparated x] [QuasiCompact y] [QuasiSeparated y]

/-- **The tower of fibre products `X_i ×_{S_i} Y_i`, `i ≥ 0`, as a situation of
[Stacks, Tag 09RD].** Its transitions are affine, being base changes of the transitions of the
system, its stages are quasi-compact and quasi-separated, lying quasi-compactly and
quasi-separatedly over the stages of the system, and its limit is `X ×_S Y`. -/
def towerSituation : DescentSituation.{u, u} D.Stages where
  system := towerDiagram D x y
  transition_affine {k k'} e := by
    have hu := D.transition_comp_transition k'.unop.2
      (show k'.unop.1 ≤ k.unop.1 from leOfHom e.unop)
    have sq := isPullback_prodMap_base (isPullback_baseChangeStage x hu)
      (isPullback_baseChangeStage y hu)
    have : IsAffineHom (D.transition (show k'.unop.1 ≤ k.unop.1 from leOfHom e.unop)) :=
      D.transition_affine _
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip inferInstance
  quasiCompact k := by
    change CompactSpace (pullback (pullback.snd x (D.transition k.2))
      (pullback.snd y (D.transition k.2)) : Scheme.{u})
    have := D.quasiCompact k.1
    have : QuasiCompact (pullback.snd x (D.transition k.2)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback x (D.transition k.2)) inferInstance
    have : QuasiCompact (pullback.snd y (D.transition k.2)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback y (D.transition k.2)) inferInstance
    have : QuasiCompact (pullback.snd (pullback.snd x (D.transition k.2))
        (pullback.snd y (D.transition k.2))) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback _ _) inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd (pullback.snd x (D.transition k.2)) (pullback.snd y (D.transition k.2)) ≫
        pullback.snd y (D.transition k.2))
  quasiSeparated k := by
    change QuasiSeparatedSpace (pullback (pullback.snd x (D.transition k.2))
      (pullback.snd y (D.transition k.2)) : Scheme.{u})
    have := D.quasiSeparated k.1
    have : QuasiSeparated (pullback.snd x (D.transition k.2)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback x (D.transition k.2)) inferInstance
    have : QuasiSeparated (pullback.snd y (D.transition k.2)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback y (D.transition k.2)) inferInstance
    have : QuasiSeparated (pullback.snd (pullback.snd x (D.transition k.2))
        (pullback.snd y (D.transition k.2))) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback _ _) inferInstance
    exact quasiSeparatedSpace_of_quasiSeparated
      (pullback.snd (pullback.snd x (D.transition k.2)) (pullback.snd y (D.transition k.2)) ≫
        pullback.snd y (D.transition k.2))
  limitCone := towerCone D x y
  isLimit := isLimitTowerCone D x y
  base := ⟨D.base, le_rfl⟩

end Tower

/-- **[Stacks, Tag 09RF], essential surjectivity, along the tower of fibre products**: the
proposition `AlgebraicGeometry.PerfectDescendsAlongBaseChangedTower`, for index sets in the
universe of the schemes. It is essential surjectivity in
`AlgebraicGeometry.DescentSituation.perfect_isColimit` at `AlgebraicGeometry.towerSituation`. -/
theorem perfectDescendsAlongBaseChangedTower : PerfectDescendsAlongBaseChangedTower.{u, u} := by
  intro I _ _ D X₀ Y₀ x y _ _ _ _ E hE
  obtain ⟨k, -, Ek, hEk, eEk⟩ := (towerSituation D x y).perfect_isColimit.1 E hE
  exact ⟨k.1, k.2, Ek, hEk, eEk⟩

/-- **[Stacks, Tag 09RF], descent of an isomorphism, along the tower of fibre products**: the
proposition `AlgebraicGeometry.PerfectIsoDescendsAlongBaseChangedTower`, for index sets in the
universe of the schemes. It is
`AlgebraicGeometry.DescentSituation.exists_transition_iso_of_projection_iso` at
`AlgebraicGeometry.towerSituation`. -/
theorem perfectIsoDescendsAlongBaseChangedTower :
    PerfectIsoDescendsAlongBaseChangedTower.{u, u} := by
  intro I _ _ D X₀ Y₀ x y _ _ _ _ i hi E F hE hF e
  obtain ⟨j, hij, ej⟩ :=
    (towerSituation D x y).exists_transition_iso_of_projection_iso ⟨i, hi⟩ E F hE hF e
  exact ⟨j.1, hij, ej⟩

/-! ### Stacks 0G0L -/

/-- **[Stacks, Tag 0G0L]: a relative equivalence over a limit of schemes comes from a finite
stage.** Let `S = lim S_i` be the limit of a directed inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms, with a chosen index `0`, let
`X_0 ⟶ S_0` and `Y_0 ⟶ S_0` be smooth and proper, and put `X_i = X_0 ×_{S_0} S_i`,
`X = X_0 ×_{S_0} S` and likewise for `Y_0`. If `K` is the Fourier-Mukai kernel of a relative
equivalence from `X` to `Y` over `S`, then for some `i ≥ 0` there is a Fourier-Mukai kernel of a
relative equivalence from `X_i` to `Y_i` over `S_i`.

The proof is the source's, performed by
`AlgebraicGeometry.exists_isRelativeEquivalenceKernel_of_descentSituation`: the kernel and its
partner descend to a stage by [Stacks, Tag 09RF]
(`AlgebraicGeometry.perfectDescendsAlongBaseChangedTower`), the diagonal kernel and the
convolution kernel commute with base change ([Stacks, Tag 08IB], [Stacks, Tag 0CTA]:
`AlgebraicGeometry.diagonalKernelAndConvolutionBaseChange`) and are perfect
(`AlgebraicGeometry.diagonalKernelAndConvolutionPerfect`), and the two displayed isomorphisms of
[Stacks, Tag 0G0I] descend to a later stage by [Stacks, Tag 09RF] again
(`AlgebraicGeometry.perfectIsoDescendsAlongBaseChangedTower`).

The source writes `X_i = S_i ×_{S_0} X_0`; the base change is taken here on the other side,
which differs by the symmetry of the fibre product. -/
@[stacks 0G0L]
theorem exists_isRelativeEquivalenceKernel_of_limit {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : DescentSituation.{u, u} I)
    {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base) (y : Y₀ ⟶ D.stage D.base)
    [Smooth x] [IsProper x] [Smooth y] [IsProper y]
    {K : DerivedCategory (pullback (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base))).Modules}
    (hK : IsRelativeEquivalenceKernel (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base)) K) :
    ∃ (i : I) (hi : D.base ≤ i) (Ki : DerivedCategory (pullback
      (pullback.snd x (D.transition hi)) (pullback.snd y (D.transition hi))).Modules),
      IsRelativeEquivalenceKernel (pullback.snd x (D.transition hi))
        (pullback.snd y (D.transition hi)) Ki :=
  exists_isRelativeEquivalenceKernel_of_descentSituation D
    perfectDescendsAlongBaseChangedTower perfectIsoDescendsAlongBaseChangedTower
    diagonalKernelAndConvolutionBaseChange diagonalKernelAndConvolutionPerfect x y hK

end AlgebraicGeometry

end
