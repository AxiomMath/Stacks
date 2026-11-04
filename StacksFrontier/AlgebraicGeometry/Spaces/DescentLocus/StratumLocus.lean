module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.FibreRank
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.IsoLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.PushforwardStratum
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria

/-!
# The descent locus over the bottom rank stratum

Let `f : X ⟶ Y` be flat, proper and of finite presentation with `𝒪_{Y'} ⟶ f'_*𝒪_{X'}` an
isomorphism for every base change, let `E` be a finite locally free `𝒪_X`-module and
`K = Rf_*E`. Let `q : Y₀ ⟶ Y` be universally of bottom rank `r` for `K` in degree `0` (it factors
through the stratum of Stacks 0D21), with `|Y₀|` over the locus where `E` has rank `r`. Over
`Y₀` put `f₀ : X₀ = X ×_Y Y₀ ⟶ Y₀`, `E₀` the pullback of `E`, `H = f₀_*E₀` (finite locally free
of rank `r`) and `φ : f₀^*H ⟶ E₀` the counit. Then for `h : T ⟶ Y₀` the descent condition of
Stacks 0D23 holds at `h ≫ q` exactly when `|T|` misses `C = |f₀|(Supp Coker φ)`, provided the base
change maps `h^*f₀_*E₀ ⟶ f_{h,*}(h')^*E₀` are isomorphisms; `C` is closed and étale locally
constructible.

## Main definitions

* `AlgebraicGeometry.Space.DescentStratum.stratumLocus`: the subset `C = |f₀|(Supp Coker φ)` of
  `|Y₀|`.

## Main results

* `AlgebraicGeometry.Space.DescentStratum.hasDescentAt_comp_iff_range_subset`: the descent
  condition holds at `h ≫ q` exactly when `|T|` misses `C`.
* `AlgebraicGeometry.Space.DescentStratum.isClosed_stratumLocus`: `C` is closed.
* `AlgebraicGeometry.Space.DescentStratum.isEtaleLocallyConstructible_stratumLocus`: `C` is
  étale locally constructible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.DescentStratum

open BottomRankLocus

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Base change of the hypotheses on `f` -/

section BaseChange

variable {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The base change of a proper morphism is proper. -/
theorem isProper_snd (hf : IsProper B S hS f.hom) : IsProper B S hS (pullback.snd f g).hom :=
  (isProper_isStableUnderBaseChange B S hS).of_isPullback (IsPullback.of_hasPullback f g) hf

/-- The base change of a morphism of finite presentation is of finite presentation. -/
theorem isFinitePresentation_snd (hf : IsFinitePresentation B S hS f.hom) :
    IsFinitePresentation B S hS (pullback.snd f g).hom :=
  ⟨(isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (IsPullback.of_hasPullback f g) hf.1,
    isQuasiCompact_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g)) hf.2.1,
    isQuasiSeparated_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g)) hf.2.2⟩

/-- The base change of a flat morphism is flat. -/
theorem isFlat_snd (hf : IsFlat B S hS f.hom) : IsFlat B S hS (pullback.snd f g).hom :=
  isFlat_of_isPullback_of_isAlgebraicSpace B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g)).flip X.2 Y.2 hf

end BaseChange

/-! ### Stacks 089Q on an algebraic space -/

/-- **An epimorphism between modules of the same rank is an isomorphism** (Stacks 089Q). -/
theorem isIso_of_epi_of_isFiniteLocallyFreeOfIntRank' {Z : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Z.1 Z.2} {r : ℤ}
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank M r)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank N r) (φ : M ⟶ N)
    [Epi φ] : IsIso φ :=
  @AlgebraicGeometry.SheafOfModules.isIso_of_epi_of_isFiniteLocallyFreeOfIntRank _ _ _ _
    (smallEtaleRingedSite_hasWeakSheafify_over B S hS _ Z.2)
    (smallEtaleRingedSite_wEqualsLocallyBijective_over B S hS _ Z.2) _ _
    (fun U a b => mul_comm (G := chartRing B S hS Z.1 Z.2 U.unop) a b)
    _ _ _ hM hN _ _

/-! ### Descent along a base change against the pullback of the counit -/

/-- Descent of `h'^*M₀` along `p`, with an invertible base change map, makes `h'^*` of the
counit invertible. -/
private theorem isIso_map_counit_of_descendsAlong_snd_aux {X₀ Y₀ T : AlgebraicSpaces B S hS}
    (p₀ : X₀ ⟶ Y₀) (M₀ : Modules.{u, u} B S hS X₀.1 X₀.2) (h : T ⟶ Y₀)
    (hp : IsIso (structureSharp B S hS (pullback.snd p₀ h)))
    (hβ : IsIso ((moduleBaseChangeMap p₀ h (pullback.snd p₀ h) (pullback.fst p₀ h)
        pullback.condition).app M₀))
    (hd : DescendsAlong (pullback.snd p₀ h) ((modulePullback B S hS (pullback.fst p₀ h)).obj M₀)) :
    IsIso ((modulePullback B S hS (pullback.fst p₀ h)).map
        ((modulePullbackAdjunction B S hS p₀).counit.app M₀)) := by
  have hs := moduleBaseChangeMap_adjoint_split p₀ h (pullback.snd p₀ h) (pullback.fst p₀ h)
    pullback.condition M₀
  rw [Adjunction.homEquiv_counit] at hs
  let c := (modulePullbackSquareComparison p₀ h (pullback.snd p₀ h)
    (pullback.fst p₀ h) pullback.condition).app ((modulePushforward B S hS p₀).obj M₀)
  obtain ⟨-, hc⟩ := (descendsAlong_iff _ hp _).1 hd
  have h1 : IsIso ((modulePullback B S hS (pullback.snd p₀ h)).map
      ((moduleBaseChangeMap p₀ h (pullback.snd p₀ h) (pullback.fst p₀ h)
        pullback.condition).app M₀) ≫
      (modulePullbackAdjunction B S hS (pullback.snd p₀ h)).counit.app
        ((modulePullback B S hS (pullback.fst p₀ h)).obj M₀)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) hc
  rw [hs] at h1
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ ((modulePullbackSquareComparison p₀ h
    (pullback.snd p₀ h) (pullback.fst p₀ h) pullback.condition).inv.app
      ((modulePushforward B S hS p₀).obj M₀)) _ (Iso.isIso_inv c) h1

/-- **Descent along a base change is the invertibility of the pulled back counit.** For
`p₀ : X₀ ⟶ Y₀`, an `𝒪_{X₀}`-module `M₀` and `h : T ⟶ Y₀` with base change `p : X_T ⟶ T`,
`h' : X_T ⟶ X₀`: if the structure map of `p` is invertible, the base change map
`h^*p₀_*M₀ ⟶ p_*h'^*M₀` is an isomorphism, and `p_*h'^*M₀` and `h'^*M₀` have the same rank,
then `h'^*M₀` descends along `p` exactly when `h'^*` of the counit `p₀^*p₀_*M₀ ⟶ M₀` is an
isomorphism. Without the base change map the second condition still implies the first. -/
theorem descendsAlong_snd_iff_isIso_map_counit {X₀ Y₀ T : AlgebraicSpaces B S hS}
    (p₀ : X₀ ⟶ Y₀) (M₀ : Modules.{u, u} B S hS X₀.1 X₀.2) (h : T ⟶ Y₀)
    (hp : IsIso (structureSharp B S hS (pullback.snd p₀ h))) {r : ℕ}
    (hr : SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePushforward B S hS (pullback.snd p₀ h)).obj
        ((modulePullback B S hS (pullback.fst p₀ h)).obj M₀)) (r : ℤ))
    (hM : SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePullback B S hS (pullback.fst p₀ h)).obj M₀) (r : ℤ)) :
    (IsIso ((modulePullback B S hS (pullback.fst p₀ h)).map
        ((modulePullbackAdjunction B S hS p₀).counit.app M₀)) →
      DescendsAlong (pullback.snd p₀ h) ((modulePullback B S hS (pullback.fst p₀ h)).obj M₀)) ∧
    (IsIso ((moduleBaseChangeMap p₀ h (pullback.snd p₀ h) (pullback.fst p₀ h)
        pullback.condition).app M₀) →
      DescendsAlong (pullback.snd p₀ h) ((modulePullback B S hS (pullback.fst p₀ h)).obj M₀) →
      IsIso ((modulePullback B S hS (pullback.fst p₀ h)).map
        ((modulePullbackAdjunction B S hS p₀).counit.app M₀))) := by
  have hs := moduleBaseChangeMap_adjoint_split p₀ h (pullback.snd p₀ h) (pullback.fst p₀ h)
    pullback.condition M₀
  rw [Adjunction.homEquiv_counit] at hs
  let c := (modulePullbackSquareComparison p₀ h (pullback.snd p₀ h)
    (pullback.fst p₀ h) pullback.condition).app ((modulePushforward B S hS p₀).obj M₀)
  refine ⟨fun hφ => ?_, fun hβ hd => ?_⟩
  · have h1 : IsIso ((modulePullbackSquareComparison p₀ h (pullback.snd p₀ h)
        (pullback.fst p₀ h) pullback.condition).inv.app ((modulePushforward B S hS p₀).obj M₀) ≫
        (modulePullback B S hS (pullback.fst p₀ h)).map
        ((modulePullbackAdjunction B S hS p₀).counit.app M₀)) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv c) hφ
    rw [← hs] at h1
    have hepi : Epi ((modulePullbackAdjunction B S hS (pullback.snd p₀ h)).counit.app
        ((modulePullback B S hS (pullback.fst p₀ h)).obj M₀)) :=
      @epi_of_epi _ _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ h1)
    refine (descendsAlong_iff _ hp _).2
      ⟨isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank hr, ?_⟩
    exact @isIso_of_epi_of_isFiniteLocallyFreeOfIntRank' _ _ _ _ _ _ _
      (isFiniteLocallyFreeOfIntRank_modulePullback _ hr) hM _ hepi
  · exact isIso_map_counit_of_descendsAlong_snd_aux p₀ M₀ h hp hβ hd

/-- For `p₀ : X₀ ⟶ Y₀`, an `𝒪_{X₀}`-module `M₀` and `h : T ⟶ Y₀` with base change
`p : X_T ⟶ T`, `h' : X_T ⟶ X₀`: if the structure map of `p` is invertible, the base change map
`h^*p₀_*M₀ ⟶ p_*h'^*M₀` is an isomorphism and `h'^*M₀` descends along `p`, then `h'^*` of the
counit `p₀^*p₀_*M₀ ⟶ M₀` is an isomorphism. -/
theorem isIso_map_counit_of_descendsAlong_snd {X₀ Y₀ T : AlgebraicSpaces B S hS}
    (p₀ : X₀ ⟶ Y₀) (M₀ : Modules.{u, u} B S hS X₀.1 X₀.2) (h : T ⟶ Y₀)
    (hp : IsIso (structureSharp B S hS (pullback.snd p₀ h)))
    (hβ : IsIso ((moduleBaseChangeMap p₀ h (pullback.snd p₀ h) (pullback.fst p₀ h)
        pullback.condition).app M₀))
    (hd : DescendsAlong (pullback.snd p₀ h) ((modulePullback B S hS (pullback.fst p₀ h)).obj M₀)) :
    IsIso ((modulePullback B S hS (pullback.fst p₀ h)).map
        ((modulePullbackAdjunction B S hS p₀).counit.app M₀)) :=
  isIso_map_counit_of_descendsAlong_snd_aux p₀ M₀ h hp hβ hd

/-- **The descent locus along a base change, generically.** For `p₀ : X₀ ⟶ Y₀` with
invertible structure maps of base changes, `M₀` of rank `r` with `p₀_*M₀` of rank `r`, and
`h : T ⟶ Y₀` along which the base change map is an isomorphism and `p_*h'^*M₀` has rank `r`,
the pullback `h'^*M₀` descends along `p` exactly when `|T|` misses
`|p₀|(Supp Coker(p₀^*p₀_*M₀ ⟶ M₀))`. -/
theorem descendsAlong_snd_iff_range_subset {X₀ Y₀ T : AlgebraicSpaces B S hS}
    (p₀ : X₀ ⟶ Y₀) (M₀ : Modules.{u, u} B S hS X₀.1 X₀.2) (h : T ⟶ Y₀)
    (hp : IsIso (structureSharp B S hS (pullback.snd p₀ h)))
    (hβ : IsIso ((moduleBaseChangeMap p₀ h (pullback.snd p₀ h) (pullback.fst p₀ h)
        pullback.condition).app M₀)) {r : ℕ}
    (hr : SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePushforward B S hS (pullback.snd p₀ h)).obj
        ((modulePullback B S hS (pullback.fst p₀ h)).obj M₀)) (r : ℤ))
    (hM : SheafOfModules.IsFiniteLocallyFreeOfIntRank M₀ (r : ℤ))
    (hH : SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePushforward B S hS p₀).obj M₀) (r : ℤ)) :
    DescendsAlong (pullback.snd p₀ h) ((modulePullback B S hS (pullback.fst p₀ h)).obj M₀) ↔
      Set.range (pointsMap B S hS T.1 h.hom) ⊆
        (pointsMap B S hS X₀.1 p₀.hom '' supportOfSheaf B S hS X₀.1 ((SheafOfModules.toSheaf _).obj
          (cokernel ((modulePullbackAdjunction B S hS p₀).counit.app M₀) :
            Modules.{u, u} B S hS X₀.1 X₀.2)))ᶜ := by
  have hH₀ := isFiniteLocallyFreeOfIntRank_modulePullback p₀ hH
  have hiff := @isIso_modulePullback_fst_map_iff_range_subset _ _ _ _ _ _ p₀ h _ _
    (isQuasicoherentOnSite_of_isFiniteLocallyFree _
      (isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank hH₀))
    (isQuasicoherentOnSite_of_isFiniteLocallyFree _
      (isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank hM))
    (@SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ _
      (isFinitePresentationOnSite_of_isFiniteLocallyFree _
        (isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank hM)))
    ((modulePullbackAdjunction B S hS p₀).counit.app M₀) _
    (isFiniteLocallyFreeOfIntRank_modulePullback _ hH₀)
    (isFiniteLocallyFreeOfIntRank_modulePullback _ hM)
  have hd := descendsAlong_snd_iff_isIso_map_counit p₀ M₀ h hp hr
    (isFiniteLocallyFreeOfIntRank_modulePullback _ hM)
  exact ⟨fun hdesc => hiff.1 (isIso_map_counit_of_descendsAlong_snd p₀ M₀ h hp hβ hdesc),
    fun hsub => hd.1 (hiff.2 hsub)⟩

/-! ### The descent locus over a base universally of bottom rank -/

section Locus

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (E : Modules.{u, u} B S hS X.1 X.2)
  {Y₀ : AlgebraicSpaces B S hS} (q : Y₀ ⟶ Y)

/-- The counit `f₀^*f₀_*E₀ ⟶ E₀` over `Y₀`. -/
abbrev stratumCounit :
    (modulePullback B S hS (pullback.snd f q)).obj
        ((modulePushforward B S hS (pullback.snd f q)).obj
          ((modulePullback B S hS (pullback.fst f q)).obj E)) ⟶
      (modulePullback B S hS (pullback.fst f q)).obj E :=
  (modulePullbackAdjunction B S hS (pullback.snd f q)).counit.app
    ((modulePullback B S hS (pullback.fst f q)).obj E)

/-- **The locus `C = |f₀|(Supp Coker φ)`** in `|Y₀|`. -/
def stratumLocus : Set (points B S hS Y₀.1) :=
  pointsMap B S hS (pullback f q).1 (pullback.snd f q).hom ''
    supportOfSheaf B S hS (pullback f q).1 ((SheafOfModules.toSheaf _).obj
      (cokernel (stratumCounit f E q) : Modules.{u, u} B S hS (pullback f q).1 (pullback f q).2))

variable (hP : IsProper B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
  (hE : SheafOfModules.IsFiniteLocallyFree E)
  (hiso : ∀ {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y),
    IsIso (structureSharp B S hS (pullback.snd f g)))
  {r : ℕ} (hqr : Set.range (pointsMap B S hS Y₀.1 q.hom) ⊆ rankFibreLocus f E r)
  (hH : SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePushforward B S hS (pullback.snd f q)).obj
        ((modulePullback B S hS (pullback.fst f q)).obj E)) (r : ℤ))

include hE hiso hqr hH in
/-- **The descent locus over a base universally of bottom rank.** Suppose `|Y₀|` lies over the
rank `r` locus of `E`, `f₀_*E₀` has rank `r`, every `f_{h,*}(h')^*E₀` has rank `r`, and the base
change maps of `f₀` at `E₀` are isomorphisms. Then the descent condition holds at `h ≫ q` exactly
when `|T|` misses `C`. -/
theorem hasDescentAt_comp_iff_range_subset
    (hr : ∀ {T : AlgebraicSpaces B S hS} (h : T ⟶ Y₀),
      SheafOfModules.IsFiniteLocallyFreeOfIntRank
        ((modulePushforward B S hS (pullback.snd (pullback.snd f q) h)).obj
          ((modulePullback B S hS (pullback.fst (pullback.snd f q) h)).obj
            ((modulePullback B S hS (pullback.fst f q)).obj E))) (r : ℤ))
    (hβ : ∀ {T : AlgebraicSpaces B S hS} (h : T ⟶ Y₀),
      IsIso ((moduleBaseChangeMap (pullback.snd f q) h (pullback.snd (pullback.snd f q) h)
        (pullback.fst (pullback.snd f q) h) pullback.condition).app
          ((modulePullback B S hS (pullback.fst f q)).obj E)))
    {T : AlgebraicSpaces B S hS} (h : T ⟶ Y₀) :
    HasDescentAt f E (h ≫ q) ↔
      Set.range (pointsMap B S hS T.1 h.hom) ⊆ (stratumLocus f E q)ᶜ := by
  rw [← hasDescentAt_comp_iff f E q h]
  exact descendsAlong_snd_iff_range_subset (pullback.snd f q)
    ((modulePullback B S hS (pullback.fst f q)).obj E) h
    (isIso_structureSharp_snd_snd f hiso q h) (hβ h) (hr h)
    (isFiniteLocallyFreeOfIntRank_fst_of_range_subset f hE q hqr) hH

include hP hE hqr in
/-- **The locus `C` is closed.** -/
theorem isClosed_stratumLocus : IsClosed (stratumLocus f E q) :=
  isClosed_image_supportOfSheaf_cokernel _ (isProper_snd f q hP).2.2
    (@SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ _
      (isFinitePresentationOnSite_of_isFiniteLocallyFree _
        (isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank
          (isFiniteLocallyFreeOfIntRank_fst_of_range_subset f hE q hqr)))) _

include hfp hE hqr hH in
/-- **The locus `C` is étale locally constructible.** -/
theorem isEtaleLocallyConstructible_stratumLocus :
    IsEtaleLocallyConstructible B S hS Y₀.1 (stratumLocus f E q) := by
  have hE₀ : SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePullback B S hS (pullback.fst f q)).obj E) (r : ℤ) :=
    isFiniteLocallyFreeOfIntRank_fst_of_range_subset f hE q hqr
  have hH₀ := isFiniteLocallyFreeOfIntRank_modulePullback (pullback.snd f q) hH
  have := isQuasicoherentOnSite_of_isFiniteLocallyFree _
    (isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank hH₀)
  have := isQuasicoherentOnSite_of_isFiniteLocallyFree _
    (isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank hE₀)
  have hfp₀ := isFinitePresentation_snd f q hfp
  exact isEtaleLocallyConstructible_image_supportOfSheaf_cokernel _ hfp₀.2.1 hfp₀.1
    (@SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ _
      (isFinitePresentationOnSite_of_isFiniteLocallyFree _
        (isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank hH₀)))
    (isFinitePresentationOnSite_of_isFiniteLocallyFree _
      (isFiniteLocallyFree_of_isFiniteLocallyFreeOfIntRank hE₀)) _

end Locus

section Derived

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (E : Modules.{u, u} B S hS X.1 X.2)
  {Y₀ : AlgebraicSpaces B S hS} (q : Y₀ ⟶ Y)
  (hP : IsProper B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
  (hfl : IsFlat B S hS f.hom) (hE : SheafOfModules.IsFiniteLocallyFree E)
  {r : ℕ} (hq : IsUniversallyFreeBottom (pushforwardComplex f E) 0 r q)

include hP hfp hfl hE hq in
/-- `f₀_*E₀` is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfIntRank_stratumPushforward :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePushforward B S hS (pullback.snd f q)).obj
        ((modulePullback B S hS (pullback.fst f q)).obj E)) (r : ℤ) := by
  obtain ⟨e⟩ := nonempty_pullbackHomology_pushforwardComplex_zero_iso f hP hfp hfl E hE q
  exact isFiniteLocallyFreeOfIntRank_of_iso B S hS e hq.self

include hP hfp hfl hE hq in
/-- For `h : T ⟶ Y₀` the module `f_{h,*}(h')^*E₀` is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfIntRank_stratumPushforward_comp {T : AlgebraicSpaces B S hS}
    (h : T ⟶ Y₀) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePushforward B S hS (pullback.snd (pullback.snd f q) h)).obj
        ((modulePullback B S hS (pullback.fst (pullback.snd f q) h)).obj
          ((modulePullback B S hS (pullback.fst f q)).obj E))) (r : ℤ) := by
  have hE₀ : SheafOfModules.IsFiniteLocallyFree
      ((modulePullback B S hS (pullback.fst f q)).obj E) :=
    isFiniteLocallyFree_modulePullback _ hE
  obtain ⟨e₀⟩ := nonempty_pullbackHomology_pushforwardComplex_zero_iso (pullback.snd f q)
    (isProper_snd f q hP) (isFinitePresentation_snd f q hfp) (isFlat_snd f q hfl) _ hE₀ h
  obtain ⟨e⟩ := nonempty_pullback_pushforwardComplex_iso f hP hfp hfl E hE q
  have e₁ : pullbackHomology (pushforwardComplex f E) 0 (h ≫ q) ≅
      pullbackHomology (pushforwardComplex (pullback.snd f q)
        ((modulePullback B S hS (pullback.fst f q)).obj E)) 0 h :=
    (pullbackHomologyCompIso _ 0 q h).symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso
        ((smallEtaleDerivedModulePullback B S hS h).mapIso e)
  exact isFiniteLocallyFreeOfIntRank_of_iso B S hS (e₁ ≪≫ e₀) (hq _ h)

end Derived


end AlgebraicGeometry.Space.DescentStratum

end
