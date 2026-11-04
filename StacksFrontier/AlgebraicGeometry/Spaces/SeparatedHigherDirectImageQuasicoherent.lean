module

public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverAffineFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePushforwardComposite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsTerminalBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Higher direct images of quasi-coherent modules along a separated morphism

Let `f : X ⟶ Y` be a quasi-compact and separated morphism of algebraic spaces over a scheme `S`
and let `𝓕` be a quasi-coherent `𝒪_X`-module.  Then every higher direct image `R^n f_*𝓕` is
quasi-coherent.  This is Stacks 0720 for a separated morphism.

## The proof

After the reduction to an affine base of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_affineTarget`,
the target `Y` is affine and the source `X` is quasi-compact and separated.  Choose an affine
scheme `U` with a surjective étale morphism `g : U ⟶ X` (Stacks 03H6).  Then

* `g ∘ f : U ⟶ Y` is a morphism between affine spaces, hence affine, and `g` is affine because
  `f` is separated (Stacks 08GB, part (2));
* for a quasi-coherent `𝒪_U`-module `𝓗` the higher direct images `R^q g_*𝓗` and
  `R^q (f ∘ g)_*𝓗` vanish for `q > 0` (Stacks 073H), so the Leray collapse
  `AlgebraicGeometry.Space.rightDerivedModulePushforwardCompIsoOfIsEtale` gives
  `R^q f_*(g_*𝓗) = 0` for `q > 0`;
* the unit `𝓕 ⟶ g_*g^*𝓕` is a monomorphism, restriction along the surjective étale `g` being
  faithful, and its cokernel `𝓖` is quasi-coherent (Stacks 03M9 and 03M1).

The long exact sequence of `0 ⟶ 𝓕 ⟶ g_*g^*𝓕 ⟶ 𝓖 ⟶ 0` then presents `R^{n+1} f_*𝓕` as the
cokernel of `R^n f_*(g_*g^*𝓕) ⟶ R^n f_*𝓖`, a morphism of quasi-coherent modules by induction
on `n`; the case `n = 0` is Stacks 03M9.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_isSeparated_of_isAffineSpace`:
  the affine-base case, for a quasi-compact source separated over the base.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_isSeparated`:
  `R^n f_*𝓕` is quasi-coherent for every quasi-compact separated `f` and quasi-coherent `𝓕`.
* `AlgebraicGeometry.Space.quasicoherentHigherDirectImages_of_isSeparated`: the higher direct
  images of a coherent module along a quasi-compact separated morphism are quasi-coherent.

## References

* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A base change of a separated morphism of algebraic spaces is separated (Stacks 03KL,
part (1)), for an arbitrary cartesian square of algebraic spaces. -/
theorem isSeparated_of_isPullback_algebraicSpaces {P X Y Z : AlgebraicSpaces B S hS}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback a b f g) (hf : IsSeparated B S hS f.hom) :
    IsSeparated B S hS b.hom := by
  have sq' : IsPullback a.hom b.hom f.hom g.hom := AlgebraicSpaces.isPullback_hom _ _ _ sq
  have hsnd := sq'.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f.hom g.hom)
  rw [← hsnd]
  exact isSeparated_comp B S hS _ _
    (isSeparated_of_isIso B S hS
      (sq'.isoIsPullback _ _ (IsPullback.of_hasPullback f.hom g.hom)).hom)
    (isSeparated_pullback B S hS f.hom g.hom hf)

variable {X Y : AlgebraicSpaces B S hS}

/-- **The last term of a right exact sequence of quasi-coherent modules is quasi-coherent.**  In
an exact sequence `A ⟶ B ⟶ C ⟶ 0` of `𝒪_X`-modules with `A` and `B` quasi-coherent, the module
`C` is quasi-coherent, being the cokernel of `A ⟶ B` (Stacks 03M1). -/
theorem isQuasicoherentOnSite_X₃_of_exact_of_epi
    {T : ShortComplex (Modules.{u, u} B S hS X.1 X.2)} (hT : T.Exact) (hg : Epi T.g)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite) :
    T.X₃.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel T.f) hT.gIsCokernel)
    (isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 T.f)

/-- **Stacks 0720 over an affine base, for a separated source.**  Let `f : X ⟶ Y` be a
quasi-compact and separated morphism of algebraic spaces over `S` whose target is affine and
whose source is quasi-compact.  Then `R^n f_*𝓕` is quasi-coherent for every quasi-coherent
`𝒪_X`-module `𝓕` and every `n`. -/
theorem isQuasicoherentOnSite_rightDerived_of_isSeparated_of_isAffineSpace (f : X ⟶ Y)
    (hY : IsAffineSpace B S hS Y.1) (hX : IsQuasiCompactSpace B S hS X.1)
    (hfqc : IsQuasiCompact B S hS f.hom) (hf : IsSeparated B S hS f.hom) (n : ℕ)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  have hZ := BigFppfSite.contains_terminal B
  obtain ⟨W, p, hW, hpsurj, hpet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  let U : AlgebraicSpaces B S hS := schemeSpace W
  let g : U ⟶ X := ObjectProperty.homMk p
  have hg : IsEtale B S hS g.hom := hpet
  have := hasInjectiveResolutions_modules B S hS U.1 U.2
  have hU : IsAffineSpace B S hS U.1 := isAffineSpace_yoneda B S hS W hW
  have hgf : IsAffineHom B S hS (g ≫ f).hom :=
    isAffineHom_of_isAffineSpace_source_of_isAffineSpace_target B S hS hZ _ hU hY
  have hgaff : IsAffineHom B S hS g.hom :=
    isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS g.hom f.hom hgf hf
  have hgqc : IsQuasiCompact B S hS g.hom :=
    isQuasiCompact_of_isAffineHom' B S hS g.hom U.2 X.2 hgaff
  have hgqs : IsQuasiSeparated B S hS g.hom :=
    isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isAffineHom B S hS g.hom U.2 X.2 hgaff)
  have hfqs : IsQuasiSeparated B S hS f.hom := isQuasiSeparated_of_isSeparated B S hS hf
  have hvan : ∀ (H : Modules.{u, u} B S hS U.1 U.2), H.IsQuasicoherentOnSite → ∀ q, 0 < q →
      IsZero (((modulePushforward B S hS f).rightDerived q).obj
        ((modulePushforward B S hS g).obj H)) := fun H hH q hq ↦
    (isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherent B S hS (g ≫ f) hgf
      H hH q hq).of_iso
      (rightDerivedModulePushforwardCompIsoOfIsEtale B S hS g hg f H
        (fun q hq ↦ isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherent B S hS
          g hgaff H hH q hq) q).symm
  have hfaith := faithful_etaleModulePullback.{u, u} B S hS W g hg hpsurj
  let adj := etaleModulePullbackAdjunction B S hS g hg
  induction n generalizing F with
  | zero =>
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((modulePushforward B S hS f).rightDerivedZeroIsoSelf.app F).symm
      (isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f hfqc hfqs F hF)
  | succ n ih =>
    let H := (etaleModulePullback.{u, u} B S hS g hg).obj F
    have hH : H.IsQuasicoherentOnSite := isQuasicoherentOnSite_etaleModulePullback B S hS g hg F hF
    have hgH : ((modulePushforward B S hS g).obj H).IsQuasicoherentOnSite :=
      isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS g hgqc hgqs H hH
    let E : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
      ShortComplex.mk (adj.unit.app F) (cokernel.π (adj.unit.app F)) (cokernel.condition _)
    have hE : E.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
    have : ((𝟭 (Modules.{u, u} B S hS X.1 X.2)).obj F).IsQuasicoherentOnSite := hF
    have : ((etaleModulePullback.{u, u} B S hS g hg ⋙ modulePushforward B S hS g).obj
      F).IsQuasicoherentOnSite := hgH
    have hG : (cokernel (adj.unit.app F)).IsQuasicoherentOnSite :=
      isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 (adj.unit.app F)
    obtain ⟨delta, -, hwin⟩ :=
      Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅ hE
        (modulePushforward B S hS f)
    exact isQuasicoherentOnSite_X₃_of_exact_of_epi B S hS ((hwin n).exact 1)
      (((hwin n).exact 2).epi_f ((hvan H hH (n + 1) n.succ_pos).eq_of_tgt _ _))
      (ih _ hgH) (ih _ hG)

/-- **Stacks 0720 for a separated morphism.**  Let `f : X ⟶ Y` be a quasi-compact and separated
morphism of algebraic spaces over `S` and let `𝓕` be a quasi-coherent `𝒪_X`-module.  Then
`R^n f_*𝓕` is quasi-coherent for every `n`. -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_of_isSeparated (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hf : IsSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite :=
  have : F.IsQuasicoherentOnSite := hF
  isQuasicoherentOnSite_rightDerived_of_forall_affine_chart B S hS f hfqc
    (isQuasiSeparated_of_isSeparated B S hS hf) F n
    (fun V ↦ preservesInjectiveObjects_etaleModulePullback B S hS
      (chartBaseChangeInclusion B S hS f V) (isEtale_chartBaseChangeInclusion B S hS f V))
    fun V hV hqc _ hX ↦
      isQuasicoherentOnSite_rightDerived_of_isSeparated_of_isAffineSpace B S hS
        (chartBaseChangeProjection B S hS f V)
        (isAffineSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V) hV) hX hqc
        (isSeparated_of_isPullback_algebraicSpaces B S hS
          (isPullback_chartBaseChangeInclusion B S hS f V) hf) n _
        (isQuasicoherentOnSite_etaleModulePullback B S hS (chartBaseChangeInclusion B S hS f V)
          (isEtale_chartBaseChangeInclusion B S hS f V) F hF)

/-- **Along a quasi-compact separated morphism every higher direct image of a coherent module is
quasi-coherent**: `AlgebraicGeometry.Space.QuasicoherentHigherDirectImages` holds for `f`. -/
theorem quasicoherentHigherDirectImages_of_isSeparated (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hf : IsSeparated B S hS f.hom) :
    QuasicoherentHigherDirectImages B S hS f := fun G hG n ↦
  isQuasicoherentOnSite_rightDerived_modulePushforward_of_isSeparated B S hS f hfqc hf G
    hG.toIsQuasicoherentOnSite n

end AlgebraicGeometry.Space

end
