module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperSupportCoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherent

/-!
# Coherence of the higher direct images of a module with proper support, with nothing carried

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` locally Noetherian, and let `𝓕` be a coherent `𝒪_X`-module whose support is
proper over `Y`.  **Stacks 08GC** asserts that `R^p f_*𝓕` is a coherent `𝒪_Y`-module for every
`p ≥ 0`.  The base carries a form of it,
`AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_hasProperSupport`, over
three hypotheses (Stacks 08AR, the étale-affine case of Stacks 03DW and a degeneration of the
relative Leray spectral sequence).  This file proves it with none.

The proof is the source's.  Stacks 0CZI writes `𝓕 = i_*𝓖` for a closed subspace `i : Z → X` with
`Z` proper over `Y` and `𝓖` coherent; the higher direct images along the affine morphism `i`
vanish (Stacks 073H for quasi-coherent modules); so `Ri_*(𝓖[0]) = (i_*𝓖)[0]` and, through
`R(closedSubspaceInclusion B S hS X Z ≫ f)_* = Rf_* ∘ Ri_*` (Stacks 0D6E, which replaces the
relative Leray spectral sequence), `R^p f_*𝓕 = R^p (closedSubspaceInclusion B S hS X Z ≫ f)_*𝓖`,
coherent by Stacks 08AR.

## Main results

* `AlgebraicGeometry.Space.nonempty_derivedModulePushforward_single_iso`: a module without higher
  direct images has derived direct image its direct image, placed in degree zero.
* `AlgebraicGeometry.Space.exists_closedSubspace_higherDirectImage_iso`: the reduction to a
  proper morphism.
* `AlgebraicGeometry.Space.isCoherent_higherDirectImage_of_hasProperSupport`: **Stacks 08GC**.
* `AlgebraicGeometry.Space.exists_isZero_higherDirectImage_of_hasProperSupport`: over a
  quasi-compact base the higher direct images vanish in high degrees (Stacks 073G).

## References

* [Stacks Project, Lemma 75.7.10 (Tag 08GC)](https://stacks.math.columbia.edu/tag/08GC)
* [Stacks Project, Lemma 75.7.7 (Tag 0CZI)](https://stacks.math.columbia.edu/tag/0CZI)
* [Stacks Project, Lemma 69.20.2 (Tag 08AR)](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- **A module without higher direct images has derived direct image its direct image, placed in
degree zero.**  `Rf_*(𝓜[0])` has no cohomology below degree zero by left t-exactness and none above
by hypothesis, so it is an object placed in degree zero, and its degree-zero cohomology is
`R^0 f_*𝓜 = f_*𝓜`. -/
theorem nonempty_derivedModulePushforward_single_iso (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : ∀ q : ℕ, 0 < q →
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      IsZero (((modulePushforward B S hS f).rightDerived q).obj M)) :
    Nonempty ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj M) ≅
      (DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj
        ((modulePushforward B S hS f).obj M)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have : (modulePushforward B S hS f).IsRightAdjoint :=
    ⟨_, ⟨modulePullbackAdjunction B S hS f⟩⟩
  set K := (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
    ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj M)
  have : K.IsGE 0 :=
    Stacks.DerivedFunctor.isGE_totalRightDerived_obj (modulePushforward B S hS f) _ 0
  have : K.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    obtain ⟨n, hn⟩ : ∃ n : ℕ, i - 0 = n := ⟨i.toNat, by omega⟩
    exact IsZero.of_iso (hM n (by omega))
      (homologyDerivedModulePushforwardSingleIso B S hS f M 0 i n hn)
  obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  refine ⟨e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso ?_⟩
  exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app N).symm ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso e.symm ≪≫
    homologyDerivedModulePushforwardSingleIso B S hS f M 0 0 0 rfl ≪≫
    (modulePushforward B S hS f).rightDerivedZeroIsoSelf.app M

/-- **The reduction of Stacks 08GC to a proper morphism.**  For `f` locally of finite type with
`Y` locally Noetherian and a coherent `𝓕` with support proper over `Y`, there are a closed subspace
`i : Z → X` with `i ≫ f` proper and a coherent, quasi-coherent `𝒪_Z`-module `𝓖` with
`R^p f_*𝓕 ≅ R^p (i ≫ f)_*𝓖` in every degree.

Stacks 0CZI (`AlgebraicGeometry.Space.hasProperSupport_tfae`) gives `Z` and `𝓖` with
`i_*𝓖 ≅ 𝓕`; `𝓖` is coherent because `X` is locally Noetherian (Stacks 04ZK).  The higher direct
images of `𝓖` along the affine `i` vanish (Stacks 073H), so `Ri_*(𝓖[0]) ≅ (i_*𝓖)[0]`, and
`R(i ≫ f)_* ≅ Rf_* ∘ Ri_*` (Stacks 0D6E) gives the identification on cohomology. -/
theorem exists_closedSubspace_higherDirectImage_iso (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hsupp : HasProperSupport B S hS X.2 Y.2 f.hom hf ((SheafOfModules.toSheaf _).obj F)) :
    ∃ (W : AlgebraicSpaces B S hS) (i : W ⟶ X) (G : Modules.{u, u} B S hS W.1 W.2),
      IsClosedImmersion B S hS i.hom ∧ G.IsQuasicoherentOnSite ∧ IsCoherent B S hS W.1 W.2 G ∧
        IsProper B S hS (i ≫ f).hom ∧
        ∀ p : ℕ,
          have := hasInjectiveResolutions_modules B S hS X.1 X.2
          have := hasInjectiveResolutions_modules B S hS W.1 W.2
          Nonempty (((modulePushforward B S hS f).rightDerived p).obj F ≅
            ((modulePushforward B S hS (i ≫ f)).rightDerived p).obj G) := by
  have _hFc := hF
  obtain ⟨Z, G, hGqc, -, hZp, ⟨e⟩⟩ :=
    ((hasProperSupport_tfae B S hS X Y f.hom hf F hF.toIsQuasicoherentOnSite
      (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X F)
      hF.toIsCoherentOnSite.isFiniteType).out 1 3).1 hsupp
  have hXn := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 Y.2 f.hom hf hY
  have hGcoh := isCoherent_of_modulePushforward_closedSubspace B S hS X hXn F Z G hGqc e
  obtain ⟨eG⟩ := nonempty_derivedModulePushforward_single_iso B S hS
    (closedSubspaceInclusion B S hS X Z) G (fun q hq =>
      isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite B S hS
        (closedSubspaceInclusion B S hS X Z)
        (isAffineHom_of_isClosedImmersion B S hS _ Z.2.2) G hGqc q hq)
  refine ⟨closedSubspaceToSpace B S hS X Z, closedSubspaceInclusion B S hS X Z, G, Z.2.2, hGqc,
    hGcoh, hZp, fun p => ⟨?_⟩⟩
  exact (homologyDerivedModulePushforwardSingleIso B S hS f F 0 p p (by simp)).symm ≪≫
    (DerivedCategory.homologyFunctor _ (p : ℤ)).mapIso
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).mapIso
          (eG ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e).symm ≪≫
        ((derivedModulePushforwardCompIso B S hS (closedSubspaceInclusion B S hS X Z) f).app
          _).symm) ≪≫
    homologyDerivedModulePushforwardSingleIso B S hS (closedSubspaceInclusion B S hS X Z ≫ f)
      G 0 p p (by simp)

/-- **Stacks 08GC.**  Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` which is locally of finite type with `Y` locally Noetherian, and let `𝓕` be a coherent
`𝒪_X`-module whose support is proper over `Y`.  Then `R^p f_*𝓕` is a coherent `𝒪_Y`-module for
every `p`.

By `AlgebraicGeometry.Space.exists_closedSubspace_higherDirectImage_iso`,
`R^p f_*𝓕 ≅ R^p (i ≫ f)_*𝓖` for a closed subspace `i : Z → X` proper over `Y` and a coherent
`𝒪_Z`-module `𝓖`; that is coherent by Stacks 08AR. -/
@[stacks 08GC, ega "III 3.2.1" "more general", ega "III 4.1.10" "more general"]
theorem isCoherent_higherDirectImage_of_hasProperSupport (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hsupp : HasProperSupport B S hS X.2 Y.2 f.hom hf ((SheafOfModules.toSheaf _).obj F))
    (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived p).obj F) := by
  obtain ⟨W, i, G, -, -, hGcoh, hZp, he⟩ :=
    exists_closedSubspace_higherDirectImage_iso B S hS f hf hY F hF hsupp
  exact isCoherent_of_iso B S hS Y.2 (he p).some.symm
    (isCoherent_higherDirectImage_of_isProper B S hS _ hZp hY G hGcoh p)

/-- **The higher direct images of a coherent module with proper support vanish in high degrees**,
over a quasi-compact and locally Noetherian base: the module is, by
`AlgebraicGeometry.Space.exists_closedSubspace_higherDirectImage_iso`, a direct image from a
closed subspace proper over `Y`, and a proper morphism is quasi-compact and quasi-separated, so
Stacks 073G bounds its higher direct images of quasi-coherent modules.  This is the boundedness
from above in the proof of Stacks 08GK. -/
theorem exists_isZero_higherDirectImage_of_hasProperSupport (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hsupp : HasProperSupport B S hS X.2 Y.2 f.hom hf ((SheafOfModules.toSheaf _).obj F)) :
    ∃ N : ℕ, ∀ p : ℕ, N ≤ p →
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      IsZero (((modulePushforward B S hS f).rightDerived p).obj F) := by
  obtain ⟨W, i, G, -, hGqc, -, hZp, he⟩ :=
    exists_closedSubspace_higherDirectImage_iso B S hS f hf hY F hF hsupp
  obtain ⟨N, hN⟩ := exists_forall_isZero_rightDerived_modulePushforward_of_qcqs B S hS
    (i ≫ f) hZp.2.1.2
    (isQuasiSeparated_of_isSeparated B S hS hZp.1) hYqc
  exact ⟨N, fun p hp => IsZero.of_iso (hN _ _ (𝟙 _) (𝟙 _) _ (IsPullback.id_horiz _) G hGqc p hp)
    (he p).some⟩

end AlgebraicGeometry.Space

end
