module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FiniteLocallyFreePushPullUnranked
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubmoduleColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingClosedSubspaceFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingBlowupStrictTransformFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingRankStratumRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingStratificationFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCondition2
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeAffineChartBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformOffExceptional
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
public import StacksFrontier.RingTheory.Fitting.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Blowing up the Fitting strata of a finite cover

This file is Step 2 of the proof of Stacks 0ADD sketched in Stacks 0ADE, one Fitting stratum at
a time.  The remark asks for "a `U`-admissible blowup `b : X̃ ⟶ X` such that the strict
transform `Ỹ` of `Y` is flat over `X̃`" (Stacks 087E), for a finite surjective `Y ⟶ X`.  Here the
blowup is the one in the Fitting ideal: for the closed subspaces `Z_0 ⊇ Z_1 ⊇ ⋯` of `X` cut out by
the Fitting ideals of `F = g_*𝒪_Y` (Stacks 0CZ9), blow up `Z_r` in the closed subspace cut out by
`Fit_{r+1}` of the direct image of `Y ×_X Z_r`.  The direct image restricted to the stratum
`Z_r ∖ Z_{r+1}` is finite locally free of rank `r + 1` (Stacks 0CZA), so Stacks 0D0Q makes the
strict transform finite locally free
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_strictTransform_of_fittingIdeal`).

## Main results

* `AlgebraicGeometry.Space.fittingIdeal_eq_of_iso`: the Fitting ideal sheaves of isomorphic
  modules agree.
* `AlgebraicGeometry.Space.range_pointsMap_eq_preimage_of_definingIdealSheaf_eq_fittingIdeal`:
  the Fitting closed subspace of the restriction to a closed subspace lies over the Fitting
  closed subspace (Stacks 07U8 and 0CZ4).
* `AlgebraicGeometry.Space.exists_blowup_fittingStratum`: **Step 2 of Stacks 0ADE on one Fitting
  stratum**.

## References

* [Stacks Project, Tag 0ADE](https://stacks.math.columbia.edu/tag/0ADE)
* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 0D0Q](https://stacks.math.columbia.edu/tag/0D0Q)
* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 0CZA](https://stacks.math.columbia.edu/tag/0CZA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The Fitting ideal sheaves of isomorphic modules agree**: an isomorphism of modules is a
linear isomorphism on the sections over every chart, and the chartwise Fitting ideals are
invariant under linear isomorphisms. -/
theorem fittingIdeal_eq_of_iso {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F}
    {G G' : Modules.{u, u} B S hS F hF} (e : G ≅ G') (r : ℕ) :
    fittingIdeal B S hS F hF G r = fittingIdeal B S hS F hF G' r := by
  have key : ∀ {G G' : Modules.{u, u} B S hS F hF} (e : G ≅ G'),
      fittingIdeal B S hS F hF G r ≤ fittingIdeal B S hS F hF G' r := by
    intro G G' e
    refine fittingIdeal_le G r fun V hV b hfin hb => ?_
    let eV' : G.val.obj (op V) ≅ G'.val.obj (op V) :=
      { hom := e.hom.val.app (op V)
        inv := e.inv.val.app (op V)
        hom_inv_id := congrArg (fun h : G ⟶ G => h.val.app (op V)) e.hom_inv_id
        inv_hom_id := congrArg (fun h : G' ⟶ G' => h.val.app (op V)) e.inv_hom_id }
    let eV := eV'.toLinearEquiv
    have := hfin
    have : Module.Finite _ (G'.val.obj (op V)) := Module.Finite.equiv eV
    refine mem_fittingIdeal_of_mem_fittingIdealOnChart G' r V hV b ?_
    have h : fittingIdealOnChart B S hS F hF G r V = fittingIdealOnChart B S hS F hF G' r V := by
      unfold fittingIdealOnChart
      exact fittingIdeal_eq_of_linearEquiv_int eV r
    rwa [← h]
  exact le_antisymm (key e) (key e.symm)

/-- The isomorphism `(f_Z)_*𝒪 ≅ ι^*f_*𝒪` for the base change `f_Z` of an affine `f` along `ι`. -/
private theorem nonempty_iso_pushforwardStructureModule_pullback_snd_aux
    {X Ub W : AlgebraicSpaces B S hS}
    (g : Ub ⟶ X) (hg : IsAffineHom B S hS g.hom) (ι : W ⟶ X)
    (hfaff : IsAffineHom B S hS (pullback.snd g ι).hom) :
    Nonempty (pushforwardStructureModule B S hS (pullback.snd g ι) ≅
      (modulePullback B S hS ι).obj (pushforwardStructureModule B S hS g)) := by
  obtain ⟨e₀⟩ := nonempty_iso_modulePushforward_modulePullback_of_isAffineHom B S hS
    (pullback.fst g ι) (pullback.snd g ι) g ι (IsPullback.of_hasPullback g ι) hg hfaff
    (SheafOfModules.unit (structureRingSheaf B S hS Ub))
    (SheafOfModules.isQuasicoherentOnSite_unit _)
  exact ⟨(modulePushforward B S hS (pullback.snd g ι)).mapIso
      (modulePullbackUnitIso B S hS (pullback.fst g ι)).symm ≪≫ e₀⟩

/-- **The Fitting closed subspace of the restriction to a closed subspace.**  Let `f : U ⟶ X` be
finite, `F = f_*𝒪_U`, `ι : Z ⟶ X` a closed immersion and `f_Z : U ×_X Z ⟶ Z` the base change.
Then `(f_Z)_*𝒪_{U ×_X Z} ≅ ι^*F` (Stacks 07U8), and so a closed subspace `C ⊆ Z` cut out by
`Fit_k((f_Z)_*𝒪)` has the points of `Z` lying over the closed subspace of `X` cut out by
`Fit_k(F)` (Stacks 0CZ4). -/
theorem range_pointsMap_eq_preimage_of_definingIdealSheaf_eq_fittingIdeal
    {X Ub W : AlgebraicSpaces B S hS} (g : Ub ⟶ X) (hg : IsAffineHom B S hS g.hom)
    (ι : W ⟶ X) (hFqc : (pushforwardStructureModule B S hS g).IsQuasicoherentOnSite)
    (hFft : SheafOfModules.IsFiniteTypeOnSite (pushforwardStructureModule B S hS g))
    (hfaff : IsAffineHom B S hS (pullback.snd g ι).hom) (k : ℕ) (Zk : ClosedSubspaces B S hS X.1)
    (hZk : definingIdealSheaf B S hS X Zk =
      fittingIdeal B S hS X.1 X.2 (pushforwardStructureModule B S hS g) k)
    (C : ClosedSubspaces B S hS W.1)
    (hC : definingIdealSheaf B S hS W C =
      fittingIdeal B S hS W.1 W.2 (pushforwardStructureModule B S hS (pullback.snd g ι)) k) :
    Set.range (pointsMap B S hS C.1.toFunctor C.1.ι) =
      pointsMap B S hS W.1 ι.hom ⁻¹' Set.range (pointsMap B S hS Zk.1.toFunctor Zk.1.ι) := by
  -- `(f_Z)_*𝒪 ≅ ι^*F`
  obtain ⟨e⟩ := nonempty_iso_pushforwardStructureModule_pullback_snd_aux B S hS g hg ι hfaff
  rw [range_pointsMap_ι_eq_idealZeroLocus B S hS W C, hC, fittingIdeal_eq_of_iso B S hS e k,
    range_pointsMap_ι_eq_idealZeroLocus B S hS X Zk, hZk]
  simp only [idealZeroLocus]
  rw [idealUnitLocus_fittingIdeal_modulePullback B S hS _ hFqc hFft ι k, Set.preimage_compl]

/-- The direct image of the structure sheaf along the base change of an affine morphism along
`ι` is the inverse image along `ι` of the direct image (Stacks 07U8). -/
@[sga "3 VIB 11.1" "more general"]
theorem nonempty_iso_pushforwardStructureModule_pullback_snd {X Ub W : AlgebraicSpaces B S hS}
    (g : Ub ⟶ X) (hg : IsAffineHom B S hS g.hom) (ι : W ⟶ X)
    (hfaff : IsAffineHom B S hS (pullback.snd g ι).hom) :
    Nonempty (pushforwardStructureModule B S hS (pullback.snd g ι) ≅
      (modulePullback B S hS ι).obj (pushforwardStructureModule B S hS g)) := by
  exact nonempty_iso_pushforwardStructureModule_pullback_snd_aux B S hS g hg ι hfaff

/-- The points of an open complement `X ∖ Z` are the points of `X` outside `|Z|`. -/
theorem range_pointsMap_ι_openComplementOfClosedSubspace (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    Set.range (pointsMap B S hS (openComplementOfClosedSubspace B S hS X Z).1.toFunctor
      (openComplementOfClosedSubspace B S hS X Z).1.ι) =
        (Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι))ᶜ := by
  rw [← openSubspacesOrderIso_apply B S hS X.1 X.2 (openComplementOfClosedSubspace B S hS X Z)]
  exact congrArg TopologicalSpace.Opens.carrier
    ((openSubspacesOrderIso B S hS X.1 X.2).apply_symm_apply _)

/-- **Step 2 of Stacks 0ADE on one Fitting stratum.**  Let `g : U ⟶ X` be a finite surjective
morphism to a locally Noetherian algebraic space, let `Z_0 ⊇ Z_1 ⊇ ⋯` be the closed subspaces cut
out by the Fitting ideals of `g_*𝒪_U`, and fix `r`.  Blow up `Z_r` in the closed subspace
cut out by `Fit_{r+1}` of the direct image of the restriction of `g` over `Z_r`.  The result is a
proper `p : X' ⟶ X` landing in `|Z_r|`, an isomorphism over the stratum `|Z_r| ∖ |Z_{r+1}|` from
the dense open `O ⊆ X'` of points not over `|Z_{r+1}|`, together with a surjective finite locally
free `q : Y' ⟶ X'` (the strict transform, Stacks 0D0Q, 0866, 0864) and a morphism `σ : Y' ⟶ U`
over `X`. -/
theorem exists_blowup_fittingStratum {X Ub : AlgebraicSpaces B S hS}
    (hnoeth : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (g : Ub ⟶ X) (hg : IsFinite B S hS g.hom) (hgs : IsSurjective B S hS g.hom)
    (Zc : ℕ → ClosedSubspaces B S hS X.1)
    (hZc : ∀ r, definingIdealSheaf B S hS X (Zc r) =
      fittingIdeal B S hS X.1 X.2 (pushforwardStructureModule B S hS g) r) (r : ℕ) :
    ∃ (X' Y' : AlgebraicSpaces B S hS) (p : X' ⟶ X) (q : Y' ⟶ X') (σ : Y' ⟶ Ub)
      (O : Subfunctor X'.1),
      IsProper B S hS p.hom ∧ IsOpenSubspace B S hS O ∧
      Dense (Set.range (pointsMap B S hS O.toFunctor O.ι)) ∧
      (∀ a, pointsMap B S hS X'.1 p.hom a ∈
        Set.range (pointsMap B S hS (Zc r).1.toFunctor (Zc r).1.ι)) ∧
      (∀ a, a ∈ Set.range (pointsMap B S hS O.toFunctor O.ι) ↔
        pointsMap B S hS X'.1 p.hom a ∉
          Set.range (pointsMap B S hS (Zc (r + 1)).1.toFunctor (Zc (r + 1)).1.ι)) ∧
      Mono (O.ι ≫ p.hom) ∧ IsLocallyOfFiniteType B S hS (O.ι ≫ p.hom) ∧
      (∀ y ∈ Set.range (pointsMap B S hS (Zc r).1.toFunctor (Zc r).1.ι),
        y ∉ Set.range (pointsMap B S hS (Zc (r + 1)).1.toFunctor (Zc (r + 1)).1.ι) →
          ∃ a, pointsMap B S hS X'.1 p.hom a = y) ∧
      IsFiniteLocallyFree B S hS q ∧ IsSurjective B S hS q.hom ∧ σ ≫ g = q ≫ p := by
  classical
  set F := pushforwardStructureModule B S hS g with hFdef
  have hgaff : IsAffineHom B S hS g.hom := hg.isAffineHom
  have hUnoeth := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Ub.2 X.2 g.hom
    (isLocallyOfFiniteType_of_isFinite B S hS Ub.2 X.2 hg) hnoeth
  have hFcoh : IsCoherent B S hS X.1 X.2 F := by
    have : Fact (HasEtaleLocalProperty B S hS Ub.1
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) := ⟨hUnoeth⟩
    exact isCoherent_modulePushforward_of_isFinite' B S hS g hg hnoeth _
      (isCoherent_structureSheaf B S hS Ub.1 Ub.2)
  have hFqc : F.IsQuasicoherentOnSite := hFcoh.toIsQuasicoherentOnSite
  have := SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite F hFcoh.toIsCoherentOnSite
  have hFft : SheafOfModules.IsFiniteTypeOnSite F := inferInstance
  -- the closed subspace `Z_r`
  set Bsp := closedSubfunctorSpace B S hS (Zc r).2 with hBsp
  set ι := closedSubfunctorι B S hS (Zc r).2 with hι
  have hιci : IsClosedImmersion B S hS ι.hom := (Zc r).2.2
  have : Mono ι.hom := inferInstanceAs (Mono (Zc r).1.ι)
  have hBnoeth := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Bsp.2 X.2 ι.hom
    (isLocallyOfFiniteType_of_isImmersion B S hS ι.hom
      (isImmersion_of_isClosedImmersion B S hS hιci))
    hnoeth
  -- the base change `f : U ×_X Z_r ⟶ Z_r`
  have sq := IsPullback.of_hasPullback g ι
  set f := pullback.snd g ι with hfdef
  have hf : IsFinite B S hS f.hom :=
    isFinite_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) hg
  have hfaff : IsAffineHom B S hS f.hom := hf.isAffineHom
  have hUknoeth := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (pullback g ι).2 Bsp.2 f.hom
    (isLocallyOfFiniteType_of_isFinite B S hS (pullback g ι).2 Bsp.2 hf) hBnoeth
  set Fk := pushforwardStructureModule B S hS f with hFkdef
  have hFkcoh : IsCoherent B S hS Bsp.1 Bsp.2 Fk := by
    have : Fact (HasEtaleLocalProperty B S hS (pullback g ι).1
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) := ⟨hUknoeth⟩
    exact isCoherent_modulePushforward_of_isFinite' B S hS f hf hBnoeth _
      (isCoherent_structureSheaf B S hS (pullback g ι).1 (pullback g ι).2)
  have hFkqc : Fk.IsQuasicoherentOnSite := hFkcoh.toIsQuasicoherentOnSite
  have hFkfp := SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite Fk
    hFkcoh.toIsCoherentOnSite
  have hFkft : SheafOfModules.IsFiniteTypeOnSite Fk := inferInstance
  have hFkfin := module_finite_sections_of_isFiniteTypeOnSite Fk hFkqc hFkft
  obtain ⟨eFk⟩ := nonempty_iso_pushforwardStructureModule_pullback_snd B S hS g hgaff ι hfaff
  -- the centre `C`, cut out by `Fit_{r+1}`
  obtain ⟨C, hC⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS Bsp
    (fittingIdeal B S hS Bsp.1 Bsp.2 Fk (r + 1))
    (isQuasicoherentOnSite_fittingIdeal_of_isFiniteTypeOnSite B S hS Bsp Fk hFkqc hFkft (r + 1))
  have hCpts := range_pointsMap_eq_preimage_of_definingIdealSheaf_eq_fittingIdeal B S hS g hgaff
    ι hFqc hFft hfaff (r + 1) (Zc (r + 1)) (hZc (r + 1)) C hC
  have hCfp : IsFinitePresentation B S hS C.1.ι :=
    isFinitePresentation_fittingClosedSubspace B S hS Bsp Fk hFkqc hFkfp C (r + 1) hC
  obtain ⟨X', b, hb⟩ := exists_isBlowupAlong_of_isFinitePresentation C hCfp
  have hbproper : IsProper B S hS b.hom :=
    isProper_of_isBlowupAlong_of_isFinitePresentation B S hS C b hCfp hb
  -- the rank of `F_k` on the complement of the centre: that complement lands in the stratum
  have hrank : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite B S hS (openComplementSpace B S hS Bsp C).1
        (openComplementSpace B S hS Bsp C).2)
      ((modulePullback B S hS (openComplementHom B S hS Bsp C)).obj Fk) (r + 1) := by
    set j := openComplementHom B S hS Bsp C with hj
    have hjrange : ∀ a, pointsMap B S hS _ j.hom a ∉
        Set.range (pointsMap B S hS C.1.toFunctor C.1.ι) := by
      intro a ha
      have hmem : pointsMap B S hS _ j.hom a ∈
          Set.range (pointsMap B S hS (openComplement B S hS C.1).toFunctor
            (openComplement B S hS C.1).ι) := ⟨a, rfl⟩
      rw [range_pointsMap_ι_openComplement] at hmem
      exact hmem ha
    have hle : Subfunctor.range (j ≫ ι).hom ≤ fittingRankStratum B S hS X Zc (r + 1) := by
      refine le_inf ?_ ?_
      · exact (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι _).le
      · obtain ⟨φ, hφ⟩ := (factorsThrough_openSubspace_iff_points B S hS X.2
          (openComplementSpace B S hS Bsp C).2 (openComplement B S hS (Zc (r + 1)).1)
          (isOpenSubspace_openComplement B S hS X.2 _ (Zc (r + 1)).2) (j ≫ ι).hom).2 (by
            rintro _ ⟨a, rfl⟩
            rw [range_pointsMap_ι_openComplement]
            intro hz
            apply hjrange a
            rw [hCpts, Set.mem_preimage, ← pointsMap_comp_apply]
            exact hz)
        rw [← hφ]
        exact (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι _).le
    have hlift : ∃! y : (openComplementSpace B S hS Bsp C).1 ⟶
        (fittingRankStratum B S hS X Zc (r + 1)).toFunctor,
        y ≫ (fittingRankStratum B S hS X Zc (r + 1)).ι = (j ≫ ι).hom :=
      ⟨Subfunctor.lift (j ≫ ι).hom hle, Subfunctor.lift_ι _ _, fun y hy =>
        (cancel_mono (fittingRankStratum B S hS X Zc (r + 1)).ι).1
          (hy.trans (Subfunctor.lift_ι _ _).symm)⟩
    have h1 := (existsUnique_lift_fittingRankStratum_iff B S hS F hFqc hFft Zc hZc (r + 1)
      (j ≫ ι)).2 hlift
    let e : (modulePullback B S hS j).obj Fk ≅ (modulePullback B S hS (j ≫ ι)).obj F :=
      (modulePullback B S hS j).mapIso eFk ≪≫ (modulePullbackCompIso B S hS j ι).app F
    exact RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e.symm h1
  -- Stacks 0D0Q, 0866, 0864: the strict transform is finite locally free over the blowup
  have hflf := isFiniteLocallyFreeOfRank_strictTransform_of_fittingIdeal B S hS f hfaff (r + 1) C hC
    hb hFkqc hFkfin hrank
  set E := preimageClosedSubspace b C with hEdef
  set ιst := strictTransformSpaceι B S hS (f ≫ 𝟙 Bsp) b E.1 with hιst
  set g' := strictTransformPullbackMap B S hS f (𝟙 Bsp) b with hg'
  set tb := strictTransformPullbackToBlowUp B S hS (𝟙 Bsp) b with htb
  have hfp1 := AlgebraicSpaces.isPullback_fiberProduct B S hS (𝟙 Bsp) b
  have htbiso : IsIso tb := hfp1.isIso_snd_of_isIso
  have : IsIso tb.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map tb))
  set q := (ιst ≫ g') ≫ tb with hqdef
  have hq : IsFiniteLocallyFree B S hS q := by
    have h0 := (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS (ιst ≫ g')).2
      hflf.isFiniteLocallyFree
    refine (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS q).1 ?_
    have : (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf.RespectsIso := inferInstance
    exact MorphismProperty.RespectsIso.postcomp _ tb.hom (ιst ≫ g').hom h0
  set σ := ιst ≫ strictTransformPullbackToSource B S hS (f ≫ 𝟙 Bsp) b ≫ pullback.fst g ι
    with hσdef
  set p := b ≫ ι with hpdef
  -- the open `O` off the exceptional divisor
  set Uo := openComplementOfClosedSubspace B S hS Bsp C with hUo
  set O := Uo.1.preimage b.hom with hOdef
  have hO : IsOpenSubspace B S hS O := isOpenSubspace_preimage B S hS b.hom Uo.1 Bsp.2 X'.2 Uo.2
  have hOrange : Set.range (pointsMap B S hS O.toFunctor O.ι) =
      pointsMap B S hS X'.1 b.hom ⁻¹' (Set.range (pointsMap B S hS C.1.toFunctor C.1.ι))ᶜ := by
    rw [hOdef, pointsRange_preimage, range_pointsMap_ι_openComplementOfClosedSubspace]
  have hOiff : ∀ a, a ∈ Set.range (pointsMap B S hS O.toFunctor O.ι) ↔
      pointsMap B S hS X'.1 p.hom a ∉
        Set.range (pointsMap B S hS (Zc (r + 1)).1.toFunctor (Zc (r + 1)).1.ι) := by
    intro a
    rw [hOrange, Set.mem_preimage, Set.mem_compl_iff, hCpts, Set.mem_preimage,
      show p.hom = b.hom ≫ ι.hom from rfl, pointsMap_comp_apply]
  have hOp : O.ι ≫ p.hom = Uo.1.fromPreimage b.hom ≫ Uo.1.ι ≫ ι.hom := by
    rw [← Category.assoc, Subfunctor.fromPreimage_ι]
    rfl
  have hfromiso := isIso_fromPreimage_openComplement hb
  have hD := isEffectiveCartierDivisor_exceptionalDivisor hb
  have hOdense : Dense (Set.range (pointsMap B S hS O.toFunctor O.ι)) := by
    have hdense := dense_subspacePointSet_of_isSchemeTheoreticallyDense B S hS _
      (isSchemeTheoreticallyDense_openComplement_of_isEffectiveCartierDivisor B S hS X' _ hD)
    convert hdense using 1
    rw [subspacePointSet, range_pointsMap_ι_openComplement, hOrange, pointsRange_preimage,
      Set.preimage_compl]
  have hpproper : IsProper B S hS p.hom :=
    isProper_comp B S hS X'.2 Bsp.2 X.2 b.hom ι.hom hbproper
      (isProper_of_isClosedImmersion B S hS Bsp.2 X.2 ι.hom hιci)
  refine ⟨X', strictTransformSpace B S hS (f ≫ 𝟙 Bsp) b E.1, p, q, σ, O, hpproper, hO, hOdense,
    fun a => ⟨pointsMap B S hS X'.1 b.hom a, (pointsMap_comp_apply B S hS _ _ _).symm⟩, hOiff,
    ?_, ?_, ?_, hq, ?_, ?_⟩
  · rw [hOp]
    have hm1 : Mono (Uo.1.fromPreimage b.hom) := @IsIso.mono_of_iso _ _ _ _ _ hfromiso
    have hm2 : Mono (Uo.1.ι ≫ ι.hom) := @mono_comp _ _ _ _ _ _ (by infer_instance) _
      (inferInstanceAs (Mono (Zc r).1.ι))
    exact @mono_comp _ _ _ _ _ _ hm1 _ hm2
  · exact isLocallyOfFiniteType_comp' B S hS O.ι p.hom X'.2 X.2
      (isLocallyOfFiniteType_of_isEtale' B S hS O.ι (isEtale_of_isOpenImmersion B S hS hO.2))
      hpproper.2.1.1
  · rintro y ⟨y', rfl⟩ hy
    have hy'C : y' ∉ Set.range (pointsMap B S hS C.1.toFunctor C.1.ι) := by
      rw [hCpts]
      exact hy
    obtain ⟨u, rfl⟩ : y' ∈ Set.range (pointsMap B S hS Uo.1.toFunctor Uo.1.ι) := by
      rw [range_pointsMap_ι_openComplementOfClosedSubspace]
      exact hy'C
    refine ⟨pointsMap B S hS _ O.ι (pointsMap B S hS _ (inv (Uo.1.fromPreimage b.hom)) u), ?_⟩
    rw [← pointsMap_comp_apply, hOp, ← pointsMap_comp_apply, IsIso.inv_hom_id_assoc,
      pointsMap_comp_apply]
    rfl
  · -- the image of `q` is closed and contains the dense open `O`
    have hqfin : IsFinite B S hS q.hom := (isFinite_and_isFlat_of_isFiniteLocallyFree B S hS q hq).1
    have hcl : IsClosed (Set.range (pointsMap B S hS _ q.hom)) := by
      rw [← Set.image_univ]
      exact isClosed_of_universallyClosed B S hS X'.2 q.hom
        ((isFinite_iff_isAffineHom_and_isProper B S hS (strictTransformSpace B S hS (f ≫ 𝟙 Bsp)
          b E.1).2 X'.2 q.hom).1 hqfin).2.universallyClosed _ isClosed_univ
    have hsub : Set.range (pointsMap B S hS O.toFunctor O.ι) ⊆
        Set.range (pointsMap B S hS _ q.hom) := by
      rintro _ ⟨o, rfl⟩
      set a := pointsMap B S hS O.toFunctor O.ι o with ha
      have haC : pointsMap B S hS X'.1 b.hom a ∉
          Set.range (pointsMap B S hS C.1.toFunctor C.1.ι) := by
        have : a ∈ Set.range (pointsMap B S hS O.toFunctor O.ι) := ⟨o, rfl⟩
        rw [hOrange] at this
        exact this
      obtain ⟨u₀, hu₀⟩ := hgs (pointsMap B S hS _ ι.hom (pointsMap B S hS X'.1 b.hom a))
      obtain ⟨w, -, hw2⟩ := exists_point_of_isPullback_presheaf B S hS
        (AlgebraicSpaces.isPullback_hom B S hS sq) u₀ (pointsMap B S hS X'.1 b.hom a) hu₀
      obtain ⟨z, -, hz2⟩ := exists_point_of_isPullback_presheaf B S hS
        (AlgebraicSpaces.isPullback_hom B S hS
          (AlgebraicSpaces.isPullback_fiberProduct B S hS (f ≫ 𝟙 Bsp) b)) w a (by
            rw [Category.comp_id]
            exact hw2)
      have hle := preimage_openComplement_le_strictTransformSubfunctor B S hS (f ≫ 𝟙 Bsp) b E hD
      have hzpre : z ∈ Set.range (pointsMap B S hS _
          ((openComplementOfClosedSubspace B S hS X' E).1.preimage
            (strictTransformPullbackToBlowUp B S hS (f ≫ 𝟙 Bsp) b).hom).ι) := by
        rw [pointsRange_preimage, range_pointsMap_ι_openComplementOfClosedSubspace,
          Set.mem_preimage, Set.mem_compl_iff, hEdef]
        have hz2' : pointsMap B S hS _ (strictTransformPullbackToBlowUp B S hS (f ≫ 𝟙 Bsp) b).hom z
            = a := hz2
        rw [hz2', preimageClosedSubspace, pointsRange_preimage]
        exact haC
      obtain ⟨z', rfl⟩ := hzpre
      refine ⟨pointsMap B S hS _ (Subfunctor.homOfLe hle) z', ?_⟩
      have hcomp : ∀ y, pointsMap B S hS _ q.hom y =
          pointsMap B S hS _ (strictTransformPullbackToBlowUp B S hS (f ≫ 𝟙 Bsp) b).hom
            (pointsMap B S hS _ ιst.hom y) := by
        intro y
        rw [← pointsMap_comp_apply, ← strictTransformPullbackMap_toBlowUp B S hS f (𝟙 Bsp) b]
        rfl
      have hst : pointsMap B S hS _ ιst.hom (pointsMap B S hS _ (Subfunctor.homOfLe hle) z') =
          pointsMap B S hS _ ((openComplementOfClosedSubspace B S hS X' E).1.preimage
            (strictTransformPullbackToBlowUp B S hS (f ≫ 𝟙 Bsp) b).hom).ι z' := by
        rw [← pointsMap_comp_apply]
        exact congrArg (fun φ => pointsMap B S hS _ φ z') (Subfunctor.homOfLe_ι hle)
      rw [hcomp, hst]
      exact hz2
    intro a
    have : a ∈ closure (Set.range (pointsMap B S hS O.toFunctor O.ι)) := by
      rw [hOdense.closure_eq]
      trivial
    exact closure_minimal hsub hcl this
  · have hw : strictTransformPullbackToSource B S hS (𝟙 Bsp) b ≫ 𝟙 Bsp = tb ≫ b := hfp1.w
    have h2 := strictTransformPullbackMap_toSource B S hS f (𝟙 Bsp) b
    rw [hσdef, hqdef, hpdef]
    simp only [Category.assoc]
    have hw' : strictTransformPullbackToSource B S hS (𝟙 Bsp) b = tb ≫ b :=
      (Category.comp_id _).symm.trans hw
    rw [pullback.condition, ← Category.assoc tb b ι, ← hw', ← Category.assoc g', h2]
    simp only [Category.assoc]
    rfl

end AlgebraicGeometry.Space

end
