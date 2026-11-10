module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Depth
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPointsDepth
public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.QuasiAffineSource
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.GorensteinStep
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.GorensteinBlowupSequence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.LambdaOperations
public import StacksFrontier.RingTheory.CohenMacaulay.Witnesses
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exceptional inverse image of the structure sheaf in the situation of Tag 0EA3

Let `A` be a regular local ring and `h : Z ⟶ Spec A` a morphism of finite type from an affine
Cohen–Macaulay scheme which is étale at every point whose local ring has dimension at most one.
Then `h^!𝒪_{Spec A} ≅ 𝒪_Z` (placed in degree zero), for `h^!` computed at any compactification.

This is the first half of the proof of [Stacks, Tag 0EA3], in the form needed twice there: once
to conclude that `𝒪_{X, x}` is Gorenstein, and once more, after shrinking, as the identification
`f^!𝒪_Y = 𝒪_X` used to compute `ω_{X'/Y} = b^!f^!𝒪_Y = b^!𝒪_X`. The argument is the source's:

* `𝒪_{Spec A}` is a dualizing complex, `A` being regular, so `h^!𝒪_{Spec A}` is a dualizing
  complex ([Stacks, Tag 0AA3]);
* [Stacks, Tag 0EA0] with `r = 0` gives a map `𝒪_Z ⟶ ω_{Z/A} = H⁰(h^!𝒪)` which is an isomorphism
  at the points where `h` is étale;
* at the remaining points the local ring has dimension, hence (being Cohen–Macaulay) depth, at
  least two, and `ω_{Z/A}` has depth at least two by [Stacks, Tag 0E9V]
  (`Stacks.Duality.two_le_depth_stalk_upperShriekHomology`), so the map is an isomorphism by
  [Stacks, Tag 0AVM];
* a dualizing complex on a Cohen–Macaulay scheme has a single nonzero cohomology sheaf near each
  point ([Stacks, Tag 0AWT]); since `H⁰` is `𝒪_Z`, that sheaf is `H⁰`, and `h^!𝒪 ≅ 𝒪_Z[0]`.

## Main results

* `Stacks.PurityRamification.isDualizingComplex_derivedStructureSheaf_spec` — on the spectrum of
  a regular local ring the structure sheaf in degree zero is a dualizing complex.
* `Stacks.PurityRamification.nonempty_upperShriek_derivedStructureSheaf_iso` — `h^!𝒪 ≅ 𝒪_Z`.
* `Stacks.PurityRamification.isGorenstein_of_upperShriek` — such a `Z` is Gorenstein.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Duality

universe u

namespace Stacks.PurityRamification

/-! ### The structure sheaf of the spectrum of a regular local ring is dualizing -/

/-- On the spectrum of a regular local ring the structure sheaf, in degree zero, is a dualizing
complex. The single affine open `⊤` covers, and over it the model is `Γ(Spec A, ⊤) ≅ A` in degree
zero, which is dualizing because a regular local ring is Gorenstein ([Stacks, Tag 0AWX]); being
dualizing is checked on one affine open cover ([Stacks, Tag 0A86]). -/
theorem isDualizingComplex_derivedStructureSheaf_spec (A : Type u) [CommRing A]
    [IsRegularLocalRing A] :
    IsDualizingComplex (DerivedPushforward.derivedStructureSheaf (Spec (.of A))).obj := by
  let X := Spec (.of A)
  refine isDualizingComplex_iff_exists_affineOpenCover.mpr
    ⟨PUnit, fun _ => ⊤, fun _ => isAffineOpen_top X, by simp, fun _ => ?_⟩
  let : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let := HasDerivedCategory.standard (⊤ : X.Opens).toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, ⊤))
  let e : A ≃+* Γ(X, ⊤) := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  let : IsLocalRing Γ(X, ⊤) := e.isLocalRing
  have hG : Dualizing.IsGorensteinLocalRing Γ(X, ⊤) :=
    Dualizing.isGorensteinLocalRing_of_ringEquiv e.symm
      (Dualizing.IsRegularLocalRing.isGorensteinLocalRing A)
  refine ⟨(DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, ⊤)) 0).obj
    (ModuleCat.of Γ(X, ⊤) Γ(X, ⊤)), hG, ⟨?_⟩⟩
  have hU : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  exact
    ((Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (⊤ : X.Opens).toScheme.Modules 0).mapIso
      (Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι ≪≫
        (Scheme.Modules.restrictUnitIso hU.isoSpec.hom).symm ≪≫
        (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapIso
          (tildeSelf (R := Γ(X, ⊤))).symm) ≪≫
    (((tilde.functor Γ(X, ⊤) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategorySingleFunctor 0).app _).symm

/-- The spectrum of a regular local ring is Cohen–Macaulay: its local rings are regular. -/
@[ega "0 17.1.3"]
theorem isCohenMacaulay_spec (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    AlgebraicGeometry.IsCohenMacaulay (Spec (.of A)) := by
  have : IsNoetherianRing A := inferInstance
  have h := (AlgebraicGeometry.isCohenMacaulay_tfae_stalk (Spec (.of A))).out 1 2
  refine h.mpr ⟨inferInstance, fun p => ⟨inferInstance, ?_⟩⟩
  have := isRegularLocalRing_stalk_spec A p
  exact IsRegularLocalRing.isCohenMacaulayLocalRing _

/-! ### Étale points -/

/-- At a point where a morphism locally of finite type is étale, the residue field extension has
transcendence degree zero: it is finite ([Stacks, Tag 02GF]). -/
theorem residueTrdeg_eq_zero_of_etaleAt {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {x : X} (h : EtaleAt f x) : Stacks.Chow.residueTrdeg f x = 0 := by
  have hu := ((etaleAt_iff_smoothAt_and_unramifiedAt f x).mp h).2
  obtain ⟨-, hfin, -⟩ := ((unramifiedAt_tfae f x).out 1 7).mp hu
  let : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) := hfin
  change Algebra.trdeg (Y.residueField (f x)) (X.residueField x) = 0
  exact trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite _ _)

/-! ### An immersion into a smooth proper scheme -/

/-- A morphism locally of finite type from a quasi-affine scheme factors as an immersion followed
by the structure morphism of projective space, which is smooth and proper. -/
theorem exists_immersion_smooth_proper {Z S : Scheme.{u}} (h : Z ⟶ S) [Z.IsQuasiAffine]
    [LocallyOfFiniteType h] :
    ∃ (P : Scheme.{u}) (ι : Z ⟶ P) (g : P ⟶ S), IsImmersion ι ∧ Smooth g ∧ IsProper g ∧
      ι ≫ g = h := by
  obtain ⟨n, i, hi, hif⟩ := exists_immersion_affineSpace h
  let e : ULift.{u} (Fin n) ≃ {j : Fin (n + 1) // j ≠ Fin.last n} :=
    Equiv.ulift.trans (finSuccAboveEquiv (Fin.last n))
  refine ⟨projectiveSpaceOver n S, i ≫ projectiveSpaceOver.affineChart n (Fin.last n) e S,
    projectiveSpaceOver n S ↘ S, ?_, inferInstance, isProper_projectiveSpaceOver n S, ?_⟩
  · have : IsImmersion i := hi
    exact inferInstanceAs (IsImmersion (_ ≫ _))
  · rw [Category.assoc, projectiveSpaceOver.affineChart_over, hif]

/-! ### `h^!𝒪 ≅ 𝒪_Z` -/

/-- **`h^!𝒪_{Spec A} ≅ 𝒪_Z`.** Let `A` be a regular local ring and `h : Z ⟶ Spec A` a morphism
locally of finite type from an affine Cohen–Macaulay scheme, étale at every point whose local
ring has dimension at most one. Then for every compactification `j` of `h`, the exceptional
inverse image `h^!𝒪_{Spec A}` (`Stacks.Duality.upperShriek` at `j`) is the structure sheaf of
`Z` in degree zero.

This is the first part of the proof of [Stacks, Tag 0EA3]; see the module docstring. -/
theorem nonempty_upperShriek_derivedStructureSheaf_iso {A : Type u} [CommRing A]
    [IsRegularLocalRing A] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of A)) [IsAffine Z]
    [LocallyOfFiniteType h] (hCM : AlgebraicGeometry.IsCohenMacaulay Z)
    (het : ∀ z : Z, ringKrullDim (Z.presheaf.stalk z) ≤ 1 → EtaleAt h z)
    (j : CompactificationOf (Over.mk h)) :
    Nonempty ((upperShriek (ftsHomToBase h) j).obj
      (DerivedPushforward.derivedStructureSheaf (Spec (.of A))) ≅
        DerivedPushforward.derivedStructureSheaf Z) := by
  classical
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian h
  have hCMz : ∀ z : Z, IsCohenMacaulayLocalRing (Z.presheaf.stalk z) := by
    intro z
    obtain ⟨-, hz⟩ := ((AlgebraicGeometry.isCohenMacaulay_tfae_stalk Z).out 1 2).mp hCM
    obtain ⟨_, hz⟩ := hz z
    exact hz
  let F := ftsHomToBase h
  let K := (upperShriek F j).obj (DerivedPushforward.derivedStructureSheaf (Spec (.of A)))
  let KZ : DerivedCategory Z.Modules := K.obj
  have hK : IsDualizingComplex KZ :=
    isDualizingComplex_upperShriek_obj F j _ (isDualizingComplex_derivedStructureSheaf_spec A)
  obtain ⟨P, ι, g, hι, hg, hgp, hfac⟩ := exists_immersion_smooth_proper h
  have : @IsImmersion (FTS.mk h).left P ι := hι
  have : @Smooth P (FTS.mk (𝟙 (Spec (.of A)))).left g := hg
  have : @IsProper P (FTS.mk (𝟙 (Spec (.of A)))).left g := hgp
  have hKos : ∀ z : Z, ringKrullDim (Z.presheaf.stalk z) ≤ 1 → KoszulAt h z := fun z hz =>
    SmoothLocus.koszulAt_of_smoothAt ((etaleAt_iff_smoothAt_and_unramifiedAt h z).mp (het z hz)).1
  have htr : ∀ ξ : Z, closure {ξ} ∈ irreducibleComponents Z →
      Stacks.Chow.residueTrdeg h ξ = ((0 : ℕ) : Cardinal) := fun ξ hξ => by
    rw [Nat.cast_zero]
    refine residueTrdeg_eq_zero_of_etaleAt h (het ξ ?_)
    rw [Stacks.Chow.ringKrullDim_stalk_eq_zero_of_mem_genericPoints ⟨ξ, hξ⟩]
    norm_num
  obtain ⟨φ, hφ⟩ : ∃ φ : Scheme.Modules.exteriorPower
        (Scheme.Hom.relativeDifferentials F.left) 0 ⟶
        ClosedOpenProperFactorization.upperShriekHomology F j 0,
      ∀ x : Z, InfinitesimalLifting.SmoothAt F.left x →
        IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
          (Sheaf.toRingCat (Opens.grothendieckTopology
            ↥Z.toLocallyRingedSpace.toRingedSpace.carrier)
            Z.toLocallyRingedSpace.toRingedSpace.sheaf) x φ) :=
    SmoothLocus.exists_map_exteriorPower_isIso_of_smoothAt F 0 (isCohenMacaulay_spec A) ι g hfac
      hKos htr j
  let G : Z.Modules := (DerivedCategory.homologyFunctor Z.Modules 0).obj KZ
  have hGq : G.IsQuasicoherent := K.property 0
  have hGc : G.IsCoherent := isCoherent_homology_of_isDualizingComplex hK 0
  let ψ : Stacks.Ample.unitModule Z ⟶ G :=
    (VectorBundleKZero.exteriorPowerZeroIsoUnit Z _).inv ≫ φ
  have hψ : IsIso ψ := by
    have : (Stacks.Ample.unitModule Z).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
    refine AlgebraicGeometry.isIso_of_stalk_isIso_or_depth_two_and_not_associated ψ fun z => ?_
    by_cases hz : ringKrullDim (Z.presheaf.stalk z) ≤ 1
    · left
      have h1 := hφ z ((etaleAt_iff_smoothAt_and_unramifiedAt h z).mp (het z hz)).1
      have hφz : IsIso ((Stacks.ConormalSequenceRight.stalkAb Z z).map φ) :=
        (ClosedOpenProperFactorization.isIso_stalkMap_iff_isIso_stalkAb (Z := Z) z φ).mp h1
      have h2 : IsIso ((Stacks.ConormalSequenceRight.stalkAb Z z).map ψ) := by
        change IsIso ((Stacks.ConormalSequenceRight.stalkAb Z z).map
          ((VectorBundleKZero.exteriorPowerZeroIsoUnit Z _).inv ≫ φ))
        have h3 : IsIso ((Stacks.ConormalSequenceRight.stalkAb Z z).map
            (VectorBundleKZero.exteriorPowerZeroIsoUnit Z _).inv ≫
            (Stacks.ConormalSequenceRight.stalkAb Z z).map φ) :=
          (((Stacks.ConormalSequenceRight.stalkAb Z z).mapIso
            (VectorBundleKZero.exteriorPowerZeroIsoUnit Z _).symm) ≪≫
              @asIso _ _ _ _ ((Stacks.ConormalSequenceRight.stalkAb Z z).map φ) hφz).isIso_hom
        convert h3 using 2
        exact Functor.map_comp _ _ _
      exact h2
    · right
      have h2 : (2 : WithBot ℕ∞) ≤ ringKrullDim (Z.presheaf.stalk z) := by
        rw [not_le] at hz
        obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp
          (ne_bot_of_le_ne_bot (b := (1 : WithBot ℕ∞)) (by simp) hz.le)
        rw [← hd] at hz ⊢
        have h1 : (1 : ℕ∞) < d := by exact_mod_cast hz
        have h3 : (2 : ℕ∞) ≤ d := by
          have := Order.add_one_le_of_lt h1
          rwa [one_add_one_eq_two] at this
        exact (WithBot.coe_le_coe.mpr h3 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ d)
      have := isRegularLocalRing_stalk_spec A (F.left.base z)
      have hCMY : IsCohenMacaulayLocalRing ((Spec (.of A)).presheaf.stalk (F.left.base z)) :=
        IsRegularLocalRing.isCohenMacaulayLocalRing _
      have htrdeg : ∀ ξ : Z, closure {ξ} ∈ irreducibleComponents Z → z ∈ closure {ξ} →
          Stacks.Chow.residueTrdeg F.left ξ ≤ ((0 : ℕ) : Cardinal) := fun ξ hξ _ =>
        (htr ξ hξ).le
      refine ⟨?_, Stacks.Divisors.notMem_associatedPoints_of_one_le_depth G z ?_⟩
      · rw [Stacks.AmpleSectionConnected.depth_stalk_unit_eq]
        have hd : ((Module.depth (Z.presheaf.stalk z)
            (IsLocalRing.maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z) : ℕ∞) :
              WithBot ℕ∞) = ringKrullDim (Z.presheaf.stalk z) :=
          (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mp (hCMz z)
        rw [← hd] at h2
        have h2' : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ((Module.depth (Z.presheaf.stalk z)
            (IsLocalRing.maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z) : ℕ∞) :
              WithBot ℕ∞) := h2
        exact WithBot.coe_le_coe.mp h2'
      · exact le_trans (by norm_num)
          (SmoothLocus.two_le_depth_stalk_upperShriekHomology F j 0 z hCMY htrdeg h2)
  have hnt : ∀ z : Z, Nontrivial (G.presheaf.stalk z) := fun z =>
    ((Stacks.Ample.unitStalkEquiv Z z).symm.trans
      (AlgebraicGeometry.schemeStalkLinearEquiv (asIso ψ) z)).toEquiv.symm.nontrivial
  have hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor Z.Modules i).obj KZ) := by
    intro i hi
    refine (AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj
      Z.ringCatSheaf _).mpr fun y => ModuleCat.isZero_iff_subsingleton.mpr ?_
    obtain ⟨n, hn⟩ := (isCohenMacaulayLocalRing_stalk_iff_stalkwise KZ hK y).mp (hCMz y)
    have hn0 : n = 0 := by
      by_contra hne
      exact (not_subsingleton_iff_nontrivial.mpr (hnt y)) (hn 0 (Ne.symm hne))
    subst hn0
    exact hn i hi
  have hGE : KZ.IsGE 0 :=
    (DerivedCategory.isGE_iff KZ 0).mpr fun i hi => hzero i (by omega)
  have hLE : KZ.IsLE 0 :=
    (DerivedCategory.isLE_iff KZ 0).mpr fun i hi => hzero i (by omega)
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE KZ 0
  let eH : G ≅ Y := (DerivedCategory.homologyFunctor Z.Modules 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso Z.Modules 0).app Y
  exact ⟨ObjectProperty.isoMk _
    (e ≪≫ (DerivedCategory.singleFunctor Z.Modules 0).mapIso (eH.symm ≪≫ (asIso ψ).symm))⟩

/-- **The scheme `Z` is Gorenstein.** In the situation of
`Stacks.PurityRamification.nonempty_upperShriek_derivedStructureSheaf_iso`, the structure sheaf
of `Z` in degree zero is `h^!𝒪_{Spec A}`, a dualizing complex by [Stacks, Tag 0AA3]; so `Z` is
Gorenstein (`Stacks.PurityRamification.isGorenstein_of_isDualizingComplex_unit`). -/
theorem isGorenstein_of_isCohenMacaulay_of_etaleAt {A : Type u} [CommRing A]
    [IsRegularLocalRing A] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of A)) [IsAffine Z]
    [LocallyOfFiniteType h] (hCM : AlgebraicGeometry.IsCohenMacaulay Z)
    (het : ∀ z : Z, ringKrullDim (Z.presheaf.stalk z) ≤ 1 → EtaleAt h z) :
    AlgebraicGeometry.IsGorenstein Z := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian h
  obtain ⟨j, -⟩ := exists_quasiCompact_compactificationOf_of_isQuasiAffine h
  obtain ⟨e⟩ := nonempty_upperShriek_derivedStructureSheaf_iso h hCM het j
  have hK := isDualizingComplex_upperShriek_obj (ftsHomToBase h) j _
    (isDualizingComplex_derivedStructureSheaf_spec A)
  exact isGorenstein_of_isDualizingComplex_unit
    (isDualizingComplex_of_iso ((ObjectProperty.ι _).mapIso e) hK)

end Stacks.PurityRamification

end
