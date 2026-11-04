module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PuncturedSpectrumFirstHalf
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PicardRestrictionPullback
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.IdealPowerTowerSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalEquivalence
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocusPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankStalkBasis
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Characterization
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantNonzero
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageBaseChange
public import StacksFrontier.RingTheory.Support.Finite

/-!
# [Stacks, Tag 0F2D]: invertible modules on `U₀` extend to an open neighbourhood

Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`. Assume `A` is `f`-adically complete, `f` is
a nonzerodivisor, `H¹_𝔪(A/fA)` and `H²_𝔪(A/fA)` are finite `A`-modules and `H³_𝔪(A/fA) = 0`.
Let `U`, resp. `U₀`, be the punctured spectrum of `A`, resp. of `A/fA`. Then
`colim_{U₀ ⊆ U' ⊆ U open} Pic(U') ⟶ Pic(U₀)` is surjective.

The proof follows the source. Let `Uₙ` be the closed subscheme of `U` cut out by `(f𝒪_U)ⁿ⁺¹`.

1. Every invertible module on `U₀` is the restriction of a compatible system of invertible
   modules `ℒₙ` on the `Uₙ`: the exact sequence `Pic(Uₙ₊₁) → Pic(Uₙ) → H²(U₀, 𝒪_{U₀}) = 0` of
   [Stacks, Tag 0C6R]. This is
   `Stacks.PuncturedSpectrumPicard.exists_isCompatiblePullback_puncturedClosedFibre`, read here on
   the closed subschemes `V((f𝒪_U)ⁿ⁺¹)` (`exists_compatible_idealPowerStages`).
2. Regarded on `U` by closed-immersion pushforward ([Stacks, Tag 01QY]), the `ℒₙ` form an object
   of `Coh(U, f𝒪_U)` whose terms have finite free stalks over `𝒪_U / f ⁿ⁺¹𝒪_U`
   (`Stacks.Coherent.IdealPowerStageModules`).
3. By [Stacks, Tag 0EKZ] this object is the completion of a finite locally free module `𝒢` on an
   open `V ⊇ U₀` of `U`.
4. Restricting `𝒢` to `U₀` gives back `ℒ₀`, because the zeroth term of the completion is
   `𝒢 / f𝒢` and closed-immersion pushforward is fully faithful. So `𝒢` has rank one at the
   points of `U₀`, hence on an open `V' ⊇ U₀`, where it is invertible, and its class restricts
   to the given class on `U₀`.

## Main results

* `Stacks.PuncturedSpectrumPicard.picardColimitSurjective`: **[Stacks, Tag 0F2D]**.

## References

* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
* [Stacks Project, Tag 0EKZ](https://stacks.math.columbia.edu/tag/0EKZ)
* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
* [Stacks Project, Tag 01QY](https://stacks.math.columbia.edu/tag/01QY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open scoped AlgebraicGeometry

universe u

namespace Stacks.PuncturedSpectrumPicard

open Stacks.Picard (ofScheme schemePullbackClass schemePullbackClass_comp picardRepresentative
  classOf_picardRepresentative pullbackClass_classOf)
open Stacks.Thickenings (nthOrderToBase nthOrderSucc nthOrderZeroIso nthOrderInclusion)
open Stacks.Coherent (idealPowerStageSucc idealPowerStageSucc_subschemeι IdealPowerStageModules)

variable (A : Type u) [CommRing A] [IsLocalRing A] (f : A)

/-! ### The infinitesimal neighbourhoods as the closed subschemes cut out by powers -/

/-- The `n`-th infinitesimal neighbourhood of `U₀` in `U` is cut out by `(f𝒪_U)ⁿ⁺¹`. -/
theorem ker_nthOrderToBase_puncturedPrincipal (n : ℕ) :
    (nthOrderToBase (puncturedPrincipalImmersion A f) n).ker =
      puncturedPrincipalIdeal A f ^ (n + 1) := by
  have h := Stacks.Algebraization.ker_nthInfinitesimalNeighbourhoodι
    (puncturedPrincipalImmersion A f) n
  rw [Scheme.IdealSheafData.ker_subschemeι] at h
  exact h

/-- The infinitesimal neighbourhoods of `U₀` are closed subschemes of `U`. -/
instance isClosedImmersion_nthOrderToBase_puncturedPrincipal (n : ℕ) :
    IsClosedImmersion (nthOrderToBase (puncturedPrincipalImmersion A f) n) :=
  Stacks.Algebraization.isClosedImmersion_nthInfinitesimalNeighbourhoodι
    (puncturedPrincipalImmersion A f) n

/-- The identification of the `n`-th infinitesimal neighbourhood of `U₀` in `U` with the closed
subscheme `V((f𝒪_U)ⁿ⁺¹)`, over `U`. -/
def stageHom (n : ℕ) :
    Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood (puncturedPrincipalImmersion A f) n ⟶
      (puncturedPrincipalIdeal A f ^ (n + 1)).subscheme :=
  IsClosedImmersion.lift (puncturedPrincipalIdeal A f ^ (n + 1)).subschemeι
    (nthOrderToBase (puncturedPrincipalImmersion A f) n)
    (by rw [Scheme.IdealSheafData.ker_subschemeι, ker_nthOrderToBase_puncturedPrincipal])

/-- `Stacks.PuncturedSpectrumPicard.stageHom` is a morphism over `U`. -/
@[reassoc (attr := simp)]
theorem stageHom_subschemeι (n : ℕ) :
    stageHom A f n ≫ (puncturedPrincipalIdeal A f ^ (n + 1)).subschemeι =
      nthOrderToBase (puncturedPrincipalImmersion A f) n :=
  IsClosedImmersion.lift_fac _ _ _

/-- Two closed subschemes of `U` with the same ideal sheaf are identified. -/
instance isIso_stageHom (n : ℕ) : IsIso (stageHom A f n) :=
  IsClosedImmersion.isIso_of_ker_eq (nthOrderToBase (puncturedPrincipalImmersion A f) n)
    (puncturedPrincipalIdeal A f ^ (n + 1)).subschemeι (stageHom A f n)
    (stageHom_subschemeι A f n)
    (by rw [Scheme.IdealSheafData.ker_subschemeι, ker_nthOrderToBase_puncturedPrincipal])

/-- The identification of the infinitesimal neighbourhoods with the closed subschemes
`V((f𝒪_U)ⁿ⁺¹)` is compatible with the inclusions of the stages. -/
theorem stageHom_comp_idealPowerStageSucc (n : ℕ) :
    stageHom A f n ≫ idealPowerStageSucc (puncturedPrincipalIdeal A f) n =
      nthOrderSucc (puncturedPrincipalImmersion A f) n ≫ stageHom A f (n + 1) := by
  rw [← cancel_mono (puncturedPrincipalIdeal A f ^ (n + 1 + 1)).subschemeι, Category.assoc,
    idealPowerStageSucc_subschemeι, stageHom_subschemeι, Category.assoc, stageHom_subschemeι,
    Stacks.Thickenings.nthOrderSucc_toBase]

/-- The punctured closed fibre `U₀` is the closed subscheme `V(f𝒪_U)` of `U`. -/
def fibreStageIso :
    (Stacks.Algebraization.puncturedClosedFibre A f).toScheme ≅
      (puncturedPrincipalIdeal A f ^ (0 + 1)).subscheme :=
  ((puncturedPrincipalSubschemeIso A f).symm ≪≫ nthOrderZeroIso (puncturedPrincipalImmersion A f))
    ≪≫ asIso (stageHom A f 0)

/-- The identification of `U₀` with `V(f𝒪_U)`, followed by the closed immersion into `U`, is the
inclusion of `U₀` into `U`. -/
theorem fibreStageIso_hom_subschemeι :
    (fibreStageIso A f).hom ≫ (puncturedPrincipalIdeal A f ^ (0 + 1)).subschemeι =
      morphismRestrict (Stacks.Algebraization.closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A) := by
  have h1 : (baseIdealSubschemeIsoPullback A (Ideal.span {f})
      (Stacks.Divisors.puncturedSpectrum A).ι).inv ≫ (puncturedPrincipalIdeal A f).subschemeι =
      pullback.fst (Stacks.Divisors.puncturedSpectrum A).ι
        (Stacks.Algebraization.closedImmersion A f) := by
    rw [Iso.inv_comp_eq]
    exact (baseIdealSubschemeIsoPullback_hom_fst A (Ideal.span {f})
      (Stacks.Divisors.puncturedSpectrum A).ι).symm
  have h2 : (pullbackRestrictIsoRestrict (Stacks.Algebraization.closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A)).inv ≫
        pullback.snd (Stacks.Algebraization.closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A).ι =
      morphismRestrict (Stacks.Algebraization.closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A) := by
    rw [Iso.inv_comp_eq]
    exact (pullbackRestrictIsoRestrict_hom_morphismRestrict _ _).symm
  simp only [fibreStageIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    stageHom_subschemeι, Stacks.Thickenings.nthOrderZeroIso_hom,
    Stacks.Thickenings.nthOrderInclusion_toBase]
  simp only [puncturedPrincipalSubschemeIso, Iso.trans_inv, Category.assoc]
  rw [h1, pullbackSymmetry_inv_comp_fst, h2]

/-! ### Step 1: the compatible system of Picard classes on the stages -/

/-- **The first half of the source's proof, on the closed subschemes `V((f𝒪_U)ⁿ⁺¹)`.** For a
nonzerodivisor `f ∈ 𝔪` with `H³_𝔪(A/fA) = 0`, every Picard class on `U₀` extends to a family of
classes on the stages `V((f𝒪_U)ⁿ⁺¹)`, each the pullback of the next. -/
theorem exists_compatible_idealPowerStages [IsNoetherianRing A]
    (hf : f ∈ maximalIdeal A) (hreg : IsSMulRegular A f)
    (hvanish3 : IsZero (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 3))
    (c₀ : ofScheme (Stacks.Algebraization.puncturedClosedFibre A f).toScheme) :
    ∃ d : (n : ℕ) → ofScheme (puncturedPrincipalIdeal A f ^ (n + 1)).subscheme,
      d 0 = schemePullbackClass (fibreStageIso A f).inv c₀ ∧
        ∀ n, schemePullbackClass (idealPowerStageSucc (puncturedPrincipalIdeal A f) n) (d (n + 1)) =
          d n := by
  obtain ⟨c, hc0, hc⟩ := exists_isCompatiblePullback_puncturedClosedFibre A f hf hreg hvanish3 c₀
  refine ⟨fun n => schemePullbackClass (inv (stageHom A f n)) (c n), ?_, fun n => ?_⟩
  · show schemePullbackClass (inv (stageHom A f 0)) (c 0) = _
    rw [hc0, schemePullbackClass_comp]
    rfl
  · show schemePullbackClass _ (schemePullbackClass (inv (stageHom A f (n + 1))) (c (n + 1))) =
      schemePullbackClass (inv (stageHom A f n)) (c n)
    have hsq : idealPowerStageSucc (puncturedPrincipalIdeal A f) n ≫
        inv (stageHom A f (n + 1)) =
        inv (stageHom A f n) ≫ nthOrderSucc (puncturedPrincipalImmersion A f) n := by
      rw [IsIso.eq_inv_comp, ← Category.assoc, stageHom_comp_idealPowerStageSucc, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    refine (schemePullbackClass_comp _ _ _).trans ?_
    rw [hsq]
    exact (schemePullbackClass_comp _ _ _).symm.trans (congrArg _ (hc n))


/-! ### Invertible modules representing Picard classes -/

/-- The invertible module representing a Picard class of a scheme, as a module on the scheme. -/
abbrev classModule {Y : Scheme.{u}} (c : ofScheme Y) : Y.Modules :=
  (picardRepresentative Y.toRingedSpace c).obj

/-- If the pullback of a Picard class is another class, the pullback of the representing module
is isomorphic to the representing module of the other class. -/
theorem nonempty_iso_classModule_of_schemePullbackClass_eq {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    {c : ofScheme Z} {d : ofScheme Y} (h : schemePullbackClass g c = d) :
    Nonempty ((Scheme.Modules.pullback g).obj (classModule c) ≅ classModule d) := by
  have key := pullbackClass_classOf g.toLRSHom.toShHom (classModule c)
    (picardRepresentative Z.toRingedSpace c).property
  rw [classOf_picardRepresentative] at key
  rw [show schemePullbackClass g c = _ from key, ← classOf_picardRepresentative Y.toRingedSpace d]
    at h
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).mp h

/-- The module representing a Picard class is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_classModule {Y : Scheme.{u}} (c : ofScheme Y) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (classModule c) 1 :=
  ⟨((Stacks.SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
    (X := Y.toRingedSpace) (classModule c)).mp
      (picardRepresentative Y.toRingedSpace c).property).exists_isFiniteLocallyFreeOfRankData⟩

/-- The module representing a Picard class is finite locally free. -/
theorem isFiniteLocallyFree_classModule {Y : Scheme.{u}} (c : ofScheme Y) :
    Scheme.Modules.IsFiniteLocallyFree (classModule c) :=
  have := isFiniteLocallyFreeOfRank_one_classModule c
  (Scheme.Modules.isFiniteLocallyFree_iff _).mpr
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1)

/-- On a locally Noetherian scheme the module representing a Picard class is coherent. -/
theorem isCoherent_classModule {Y : Scheme.{u}} [IsLocallyNoetherian Y] (c : ofScheme Y) :
    _root_.SheafOfModules.IsCoherent.{u} (classModule c) :=
  have := (Scheme.Modules.isFiniteLocallyFree_iff _).mp (isFiniteLocallyFree_classModule c)
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree Y (classModule c)

/-! ### Step 2: the object of `Coh(U, f𝒪_U)` -/

/-- The stages `V((f𝒪_U)ⁿ⁺¹)` are locally Noetherian, being closed subschemes of `U`. -/
instance isLocallyNoetherian_idealPowerStage [IsNoetherianRing A] (n : ℕ) :
    IsLocallyNoetherian (puncturedPrincipalIdeal A f ^ (n + 1)).subscheme :=
  isLocallyNoetherian_of_isClosedImmersion (puncturedPrincipalIdeal A f ^ (n + 1)).subschemeι

/-- The compatible system of invertible modules on the stages `V((f𝒪_U)ⁿ⁺¹)` representing a
compatible family of Picard classes. -/
def stageModules [IsNoetherianRing A]
    (d : (n : ℕ) → ofScheme (puncturedPrincipalIdeal A f ^ (n + 1)).subscheme)
    (hd : ∀ n, schemePullbackClass (idealPowerStageSucc (puncturedPrincipalIdeal A f) n)
      (d (n + 1)) = d n) :
    IdealPowerStageModules (puncturedPrincipalIdeal A f) where
  obj n := classModule (d n)
  isCoherent n := isCoherent_classModule (d n)
  transitionIso n := (nonempty_iso_classModule_of_schemePullbackClass_eq _ (hd n)).some

/-! ### Step 3: [Stacks, Tag 0EKZ] on the punctured spectrum -/

/-- The standing situation of [Stacks, Tag 0EHC] for the ideals `(f) ⊆ 𝔪` of a Noetherian local
ring. -/
abbrev principalLocalSituation [IsNoetherianRing A] (hf : f ∈ maximalIdeal A) :
    Stacks.Algebraization.AlgebraizationSituation.{u} where
  A := A
  I := Ideal.span {f}
  a := maximalIdeal A
  I_le_a := (Ideal.span_singleton_le_iff_mem _).mpr hf

/-- The open `U = Spec A ∖ V(𝔪)` of the situation is the punctured spectrum. -/
theorem principalLocalSituation_U [IsNoetherianRing A] (hf : f ∈ maximalIdeal A) :
    (principalLocalSituation A f hf).U = Stacks.Divisors.puncturedSpectrum A :=
  TopologicalSpace.Opens.ext (congrArg (fun s : Set (PrimeSpectrum A) => sᶜ)
    (zeroLocus_maximalIdeal (R := A)))

/-- **[Stacks, Tag 0EKZ], the essential-surjectivity half, at an open equal to the open of the
situation**, with the ideal sheaf written as `f𝒪`. -/
theorem exists_completion_iso_of_eq_situation [IsNoetherianRing A] (hf : f ∈ maximalIdeal A)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A) (hnzd : f ∈ nonZeroDivisors A)
    (hH1 : Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 1))
    (hH2 : Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 2))
    (W : (Spec (.of A)).Opens) (hW : W = (principalLocalSituation A f hf).U)
    (F : Stacks.Coherent.CoherentAdicSystems
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {f}) W.ι))
    (hfree : ∀ (m : ℕ) (y : W.toScheme), ∃ r : ℕ,
      Nonempty ((Stacks.ModuleSkyscraper.modulesStalkFunctor W.toScheme y).obj (F.obj.obj (op m))
        ≃ₗ[W.toScheme.presheaf.stalk y]
        (Fin r → (W.toScheme.presheaf.stalk y ⧸ AlgebraicGeometry.IdealSheafData.stalk
          (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {f}) W.ι) y ^
            (m + 1))))) :
    ∃ V : W.toScheme.Opens,
      (W.ι.base ⁻¹' Set.range (Stacks.Algebraization.closedImmersion A f).base) ⊆
          (V : Set W.toScheme) ∧
        ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf,
          Scheme.Modules.IsFiniteLocallyFree G.obj ∧
          Nonempty (((Stacks.Algebraization.completionFunctor V.toScheme
              ((Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {f}) W.ι).comap
                V.ι)).obj G).obj ≅
            (F.obj ⋙ Scheme.Modules.restrictFunctor V.ι)) := by
  subst hW
  have hJ : Stacks.Algebraization.idealOnOpen (principalLocalSituation A f hf) =
      Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {f})
        (principalLocalSituation A f hf).U.ι :=
    (baseIdealSheaf_eq_comap A (Ideal.span {f}) (principalLocalSituation A f hf).U.ι).symm
  have h := (Stacks.Algebraization.completionEquivalence_principal_finiteLocallyFree
    (principalLocalSituation A f hf) rfl hcomplete hnzd
    (by rwa [← zeroLocus_maximalIdeal (R := A)] at hH1)
    (by rwa [← zeroLocus_maximalIdeal (R := A)] at hH2)).2.2
  unfold Stacks.Algebraization.HasFiniteFreeStalks
    Stacks.Algebraization.IsCompletionNearClosedFiniteLocallyFree
    Stacks.Algebraization.systemObj at h
  rw [hJ] at h
  exact h F hfree

/-! ### Step 4: the algebraization is invertible near `U₀` -/

/-- **A finite locally free module restricting to an invertible module is invertible near the
image.** Let `𝒢` be finite locally free on `V` and `j : Y ⟶ V` a morphism along which `𝒢`
restricts to the invertible module representing a Picard class. Then `𝒢` is free of rank one
near every point of the image of `j`, hence invertible on an open `W ⊆ V` containing that
image: near `j(y)` the module is free of some rank `r`, its restriction to `Y` is then free of
rank `r` near `y`, and an invertible module is free of rank one, so `r = 1`. -/
theorem exists_opens_isInvertible_of_pullback_iso {V Y : Scheme.{u}} (G : V.Modules)
    (hG : Scheme.Modules.IsFiniteLocallyFree G) (j : Y ⟶ V) (c : ofScheme Y)
    (e : (Scheme.Modules.pullback j).obj G ≅ classModule c) :
    ∃ W : V.Opens, Set.range j.base ⊆ (W : Set V) ∧
      Stacks.SheafOfModules.IsInvertible W.toScheme.toRingedSpace.presheaf
        (Stacks.RingedSpace.structureIsSheaf W.toScheme.toRingedSpace)
        ((Scheme.Modules.pullback W.ι).obj G) := by
  classical
  have hrank (y : Y) : FreeAtPointOfRank G (j.base y) 1 := by
    obtain ⟨U, hxU, I, hI, ⟨eU⟩⟩ := hG (j.base y)
    let eI : I ≃ ULift.{u} (Fin (Nat.card I)) := (Finite.equivFin I).trans Equiv.ulift.symm
    have h1 : FreeAtPointOfRank G (j.base y) (Nat.card I) :=
      freeAtPointOfRank_of_restrict_iso_free G hxU (Nat.card I)
        (eU ≪≫ (SheafOfModules.freeFunctor (R := U.toScheme.ringCatSheaf)).mapIso eI.toIso)
    have h3 : FreeAtPointOfRank (classModule c) y (Nat.card I) :=
      freeAtPointOfRank_of_moduleIso e (freeAtPointOfRank_pullback j G y _ h1)
    have h4 : FreeAtPointOfRank (classModule c) y 1 :=
      ⟨⊤, trivial, invertibleRank_pullback (⊤ : Y.Opens).ι (classModule c) 1
        ((Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_iff _ 1).mp
          (isFiniteLocallyFreeOfRank_one_classModule c))⟩
    rwa [← freeAtPointOfRank_unique (classModule c) h3 h4]
  let W : V.Opens := ⟨{x | FreeAtPointOfRank G x 1}, isOpen_setOf_freeAtPointOfRank G 1⟩
  refine ⟨W, ?_, ?_⟩
  · exact Set.range_subset_iff.mpr hrank
  · have hpt : ∀ z : W.toScheme, ∃ (U : W.toScheme.Opens) (_ : z ∈ U) (I : Type u),
        Nonempty (I ≃ Fin 1) ∧
        Nonempty (((Scheme.Modules.pullback W.ι).obj G).restrict U.ι ≅
          _root_.SheafOfModules.free.{u} I) := by
      intro z
      obtain ⟨U, hzU, -, he⟩ := exists_restrict_iso_free_le_of_freeAtPointOfRank
        ((Scheme.Modules.pullback W.ι).obj G) z 1 ⊤ trivial
        (freeAtPointOfRank_pullback W.ι G z 1 z.2)
      exact ⟨U, hzU, ULift.{u} (Fin 1), ⟨Equiv.ulift⟩, he⟩
    exact (Stacks.SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
      (X := W.toScheme.toRingedSpace) ((Scheme.Modules.pullback W.ι).obj G)).mpr
      ((Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_iff _ 1).mp
        (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.mk.{u, u, u}
          (Scheme.Modules.exists_isFiniteLocallyFreeOfRankData_of_pointwise _ 1 hpt)))

/-! ### The tag -/

/-- **[Stacks, Tag 0F2D].** Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`. Assume

1. `A` is `f`-adically complete,
2. `f` is a nonzerodivisor,
3. `H¹_𝔪(A/fA)` and `H²_𝔪(A/fA)` are finite `A`-modules, and
4. `H³_𝔪(A/fA) = 0`.

Let `U`, resp. `U₀`, be the punctured spectrum of `A`, resp. of `A/fA`. Then
`colim_{U₀ ⊆ U' ⊆ U open} Pic(U') ⟶ Pic(U₀)` is surjective: every invertible module on `U₀` is
the restriction of an invertible module on an open `U'` of `U` containing `U₀`. The conclusion is
`Stacks.PuncturedSpectrumPicard.PicardColimitSurjective`, the elementwise form of surjectivity
out of the filtered colimit.

The proof is the source's. A class on `U₀` extends to a compatible family along the
infinitesimal neighbourhoods `Uₙ = V((f𝒪_U)ⁿ⁺¹)` by [Stacks, Tag 0C6R] and
`H²(U₀, 𝒪_{U₀}) = H³_𝔪(A/fA) = 0` (`exists_compatible_idealPowerStages`); the representing
invertible modules, pushed forward to `U`, form a finite locally free object of `Coh(U, f𝒪_U)`
(`Stacks.Coherent.IdealPowerStageModules`); by [Stacks, Tag 0EKZ] it is the completion of a
finite locally free `𝒢` on an open `V ⊇ U₀` (`exists_completion_iso_of_eq_situation`); `𝒢`
restricts to the given module on `U₀`
(`Stacks.Coherent.IdealPowerStageModules.exists_pullback_iso_of_completion_iso`) and is
therefore invertible on an open `U' ⊇ U₀` (`exists_opens_isInvertible_of_pullback_iso`). -/
@[stacks 0F2D]
theorem picardColimitSurjective [IsNoetherianRing A] (hf : f ∈ maximalIdeal A)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A) (hreg : IsSMulRegular A f)
    (hH1 : Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 1))
    (hH2 : Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 2))
    (hvanish3 : IsZero (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 3)) :
    PicardColimitSurjective A f := by
  intro c₀
  obtain ⟨d, hd0, hd⟩ := exists_compatible_idealPowerStages A f hf hreg hvanish3 c₀
  let L := stageModules A f d hd
  have hfreeL : ∀ n, Scheme.Modules.IsFiniteLocallyFree (L.obj n) :=
    fun n => isFiniteLocallyFree_classModule (d n)
  obtain ⟨V, hV, G, hG, ⟨e⟩⟩ := exists_completion_iso_of_eq_situation A f hf hcomplete
    (mem_nonZeroDivisors_of_isSMulRegular hreg) hH1 hH2 (Stacks.Divisors.puncturedSpectrum A)
    (principalLocalSituation_U A f hf).symm L.adicSystem
    (fun m y => L.exists_stalk_linearEquiv_pi hfreeL m y)
  -- the closed immersion of `U₀` lands in `V`
  have hrange : Set.range (puncturedPrincipalIdeal A f ^ (0 + 1)).subschemeι.base ⊆
      (V : Set (Stacks.Divisors.puncturedSpectrum A).toScheme) := by
    rintro _ ⟨z, rfl⟩
    refine hV ⟨((Stacks.Algebraization.closedImmersion A f ⁻¹ᵁ
      Stacks.Divisors.puncturedSpectrum A).ι).base ((fibreStageIso A f).inv.base z), ?_⟩
    have h1 : (fibreStageIso A f).inv ≫ morphismRestrict (Stacks.Algebraization.closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A) =
        (puncturedPrincipalIdeal A f ^ (0 + 1)).subschemeι := by
      rw [← fibreStageIso_hom_subschemeι, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc, morphismRestrict_ι, Scheme.Hom.comp_base, TopCat.hom_comp,
      ContinuousMap.comp_apply] using
      congrArg (fun φ => φ.base z) (congrArg (· ≫ (Stacks.Divisors.puncturedSpectrum A).ι) h1)
  obtain ⟨j, hj, ⟨ej⟩⟩ := L.exists_pullback_iso_of_completion_iso V hrange G e
  obtain ⟨W, hW, hinv⟩ := exists_opens_isInvertible_of_pullback_iso G.obj hG j (d 0) ej
  have hjW : Set.range j.base ⊆ Set.range W.ι.base := by rwa [Scheme.Opens.range_ι]
  let j' := IsOpenImmersion.lift W.ι j hjW
  have hj' : j' ≫ W.ι = j := IsOpenImmersion.lift_fac _ _ _
  let cW : ofScheme W.toScheme := Stacks.SheafOfModules.picardClass _ _ _ hinv
  have hcW : schemePullbackClass j' cW = d 0 := by
    refine (pullbackClass_classOf j'.toLRSHom.toShHom _ hinv).trans ?_
    rw [← classOf_picardRepresentative _ (d 0)]
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).mpr
      ⟨(Scheme.Modules.pullbackComp j' W.ι).app G.obj ≪≫
        (Scheme.Modules.pullbackCongr hj').app G.obj ≪≫ ej⟩
  let eW := V.ι.isoImage W
  refine ⟨V.ι ''ᵁ W, (fibreStageIso A f).hom ≫ j' ≫ eW.hom, ?_, schemePullbackClass eW.inv cW, ?_⟩
  · rw [Category.assoc, Category.assoc, Scheme.Hom.isoImage_hom_ι, ← Category.assoc j',
      hj', hj, fibreStageIso_hom_subschemeι]
  · rw [schemePullbackClass_comp, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, ← schemePullbackClass_comp, hcW, hd0, schemePullbackClass_comp,
      Iso.hom_inv_id, Stacks.Picard.schemePullbackClass_id]

end Stacks.PuncturedSpectrumPicard

end
