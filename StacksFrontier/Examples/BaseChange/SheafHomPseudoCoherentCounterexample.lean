module

public import StacksFrontier.AlgebraicGeometry.BaseChange.SheafHomFlatPushforwardBaseChange
public import StacksFrontier.Examples.BaseChange.ZModFourTor
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePseudoCoherentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedBelow
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BoundedAboveKFlatResolution
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Case (2) of Stacks 08IE is false

Case (2) of [Stacks, Tag 08IE] asserts that for a quasi-compact and quasi-separated
`f : X ⟶ S`, a pseudo-coherent `E ∈ D(𝒪_X)` and a bounded complex `𝒢^•` of quasi-coherent
`𝒪_X`-modules flat over `S`, the canonical map

`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)`

(`AlgebraicGeometry.sheafHomFlatBaseChangeMap`) is an isomorphism for every cartesian square. This
file proves that this fails for

* `S = X = Spec ℤ/4`, `f = id`,
* `E = (ℤ/2)~` (pseudo-coherent, resolved by `⋯ ⟶ ℤ/4 ⟶ ℤ/4 ⟶ ℤ/4`, but not perfect),
* `𝒢^• = 𝒪_X` in degree zero (bounded, quasi-coherent, flat over `S`),
* `g = g' : Spec ℤ/2 ⟶ Spec ℤ/4`, `X' = S' = Spec ℤ/2`, `f' = id`.

The gap in the source is in the proof of [Stacks, Tag 0DJA] (3): `L(g')^*` of the Hom complex
`𝓗om^•(P, 𝒢^•)` out of a bounded above complex `P` of finite free modules is computed term by term,
but that Hom complex is a bounded *below* complex of `S`-flat modules, which need not be K-flat.
The corrected statement (`errata.md`, entry **08IE(2)**), for `g` of finite Tor dimension, is
`AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent_of_hasFiniteTorDimension`.

## Main results

* `not_isIso_sheafHomFlatBaseChangeMap`: the map is not an isomorphism for the data above.
* `not_forall_isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent`: **case (2) of Stacks 08IE,
  negated**, at the source's hypotheses.

## References

* [Stacks Project, Tag 08IE](https://stacks.math.columbia.edu/tag/08IE)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open Stacks.SheafOfModules (derivedSheafHom)
open Stacks.Examples.ZModFour

namespace Stacks.Examples.SheafHomCounterexample

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

/-- `ℤ/4`. -/
abbrev R : CommRingCat.{0} := CommRingCat.of (ZMod 4)

/-- `ℤ/2`. -/
abbrev R' : CommRingCat.{0} := CommRingCat.of (ZMod 2)

/-- The reduction `ℤ/4 → ℤ/2`. -/
abbrev φ : R ⟶ R' := CommRingCat.ofHom toTwo

/-- `S = X = Spec ℤ/4`. -/
abbrev X : Scheme.{0} := Spec R

/-- `S' = X' = Spec ℤ/2`. -/
abbrev X' : Scheme.{0} := Spec R'

/-- `g = g' : Spec ℤ/2 ⟶ Spec ℤ/4`. -/
abbrev g : X' ⟶ X := Spec.map φ

/-- The cartesian square with `f = id`, `f' = id`. -/
theorem isPullback : IsPullback g (𝟙 X') (𝟙 X) g := IsPullback.id_vert g

/-- The square `g ≫ 𝟙 X = 𝟙 X' ≫ g` of underlying morphisms of ringed spaces commutes. -/
theorem sq : g.toLRSHom.toShHom ≫ (Scheme.Hom.toLRSHom (𝟙 X)).toShHom =
    (Scheme.Hom.toLRSHom (𝟙 X')).toShHom ≫ g.toLRSHom.toShHom :=
  comp_toShHom_of_comm isPullback.w

/-- `E = (ℤ/2)~`, as an object of `D(𝒪_X)`. -/
abbrev E : DerivedCategory X.Modules :=
  (tilde.functor R).mapDerivedCategory.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{0} (ZMod 4)) 0).obj two)

/-- `𝒢^• = 𝒪_X` in degree zero. -/
abbrev G : CochainComplex X.Modules ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit X.ringCatSheaf)

/-- `(ℤ/2)~` in degree zero, as a complex. -/
abbrev twoTildeComplex : CochainComplex X.Modules ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ((tilde.functor R).obj two)

/-- `E` is the class of `(ℤ/2)~` in degree zero. -/
def eIso : E ≅ DerivedCategory.Q.obj twoTildeComplex :=
  ((tilde.functor R).mapDerivedCategorySingleFunctor 0).app two ≪≫
    (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app ((tilde.functor R).obj two)

/-- `(ℤ/2)~` in degree zero is concentrated in degrees `≤ 0`. -/
instance isLE_twoTildeComplex : twoTildeComplex.IsLE 0 := inferInstance

/-- `L(g')^*E` lies in degrees `≤ 0`. -/
theorem isLE_pullback_E : ((derivedPullback g.toLRSHom.toShHom).obj E).IsLE 0 := by
  have := @Stacks.Cohomology.KFlatDerivedPullback.isLE_derivedPullback_Q_obj _ _
      g.toLRSHom.toShHom 0 twoTildeComplex isLE_twoTildeComplex
  exact @Triangulated.TStructure.isLE_of_iso _ _ _ _ _ _ _ DerivedCategory.TStructure.t _ _
    ((derivedPullback g.toLRSHom.toShHom).mapIso eIso).symm 0 this

/-- `(g')^*𝒢^•` lies in degrees `≥ 0`. -/
theorem isGE_pullback_G :
    (DerivedCategory.Q.obj ((pullbackComplex g.toLRSHom.toShHom).obj G)).IsGE 0 := by
  rw [DerivedCategory.isGE_Q_obj_iff]
  have : ((pullbackComplex g.toLRSHom.toShHom).obj G).IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact Functor.map_isZero _ (HomologicalComplex.isZero_single_obj_X _ _ _ i (by omega))
  infer_instance

/-- **The target of the base-change map has no cohomology in degree `-1`.** -/
theorem isZero_homology_target :
    IsZero ((DerivedCategory.homologyFunctor X'.Modules (-1)).obj
      ((derivedPushforward (Scheme.Hom.toLRSHom (𝟙 X')).toShHom).obj
        (((derivedSheafHom X'.sheaf).obj
            (op ((derivedPullback g.toLRSHom.toShHom).obj E))).obj
          (DerivedCategory.Q.obj ((pullbackComplex g.toLRSHom.toShHom).obj G))))) := by
  have h := Stacks.SheafOfModules.isGE_derivedSheafHom X'.sheaf
    ((derivedPullback g.toLRSHom.toShHom).obj E)
    (DerivedCategory.Q.obj ((pullbackComplex g.toLRSHom.toShHom).obj G)) 0 0
    isLE_pullback_E isGE_pullback_G
  have h' := isGE_derivedPushforward_obj_modules (𝟙 X') _ (0 - 0) h
  exact DerivedCategory.isZero_of_isGE _ (0 - 0) (-1) (by omega) (hX := h')
/-- Every term of the free resolution of `ℤ/2` over `ℤ/4` is finite free. -/
private theorem isFiniteFree_resolution_X (n : ℤ) :
    StacksDraft.PseudoCoherence.IsFiniteFree (resolution.cochainComplex.X n) := by
  by_cases hn : n ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hn
    have : Module.Finite (ZMod 4) four := inferInstance
    have : Module.Free (ZMod 4) four := inferInstance
    have e : four ≃ₗ[ZMod 4] resolution.cochainComplex.X (-k) :=
      (resolution.cochainComplexXIso (-k) k).toLinearEquiv.symm
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  · have : Subsingleton (resolution.cochainComplex.X n) := ModuleCat.isZero_iff_subsingleton.mp
      (CochainComplex.isZero_of_isStrictlyLE _ 0 _ (by omega))
    exact ⟨inferInstance, inferInstance⟩

/-- `ℤ/2` in degree zero is pseudo-coherent in `D(ℤ/4)`. -/
theorem isPseudoCoherent_two :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{0} (ZMod 4)) 0).obj two) :=
  ⟨resolution.cochainComplex, ⟨⟨0, inferInstance⟩, isFiniteFree_resolution_X⟩,
    ⟨RingTheory.TorIndependence.projectiveResolutionIsoSingle resolution⟩⟩

/-- `𝒢^• = 𝒪_X` is the sheaf associated with `ℤ/4` in degree zero. -/
def gIso : DerivedCategory.Q.obj G ≅
    (tilde.functor R).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{0} (ZMod 4)) 0).obj four) :=
  ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _).symm ≪≫
    (DerivedCategory.singleFunctor X.Modules 0).mapIso (tildeSelf (R := R)).symm ≪≫
    (((tilde.functor R).mapDerivedCategorySingleFunctor 0).app four).symm

/-- **`R𝓗om(E, 𝒪_X) ≅ E`**. -/
def sheafHomIso : ((derivedSheafHom X.sheaf).obj (op E)).obj (DerivedCategory.Q.obj G) ≅ E :=
  ((derivedSheafHom X.sheaf).obj (op E)).mapIso gIso ≪≫
    affinePseudoCoherentDerivedSheafHomIso R _ _ isPseudoCoherent_two
      ⟨0, inferInstance⟩ ≪≫
    (tilde.functor R).mapDerivedCategory.mapIso
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := ZMod 4)).hom.mapIso
          (Iso.prod ((DerivedCategory.singleFunctorIsoCompQ _ 0).app two).op.symm
            ((DerivedCategory.singleFunctorIsoCompQ _ 0).app four)) ≪≫
        derivedHomTwoFourIso ≪≫ ((DerivedCategory.singleFunctorIsoCompQ _ 0).app two).symm)

/-- The associated sheaf of a nonzero module is nonzero. -/
theorem not_isZero_tilde {M : ModuleCat.{0} R'} (hM : ¬ IsZero M) :
    ¬ IsZero ((tilde.functor R').obj M) := fun h => hM (by
  have : (tilde.functor R').Faithful := (tilde.fullyFaithfulFunctor (R := R')).faithful
  rw [IsZero.iff_id_eq_zero]
  refine Functor.map_injective (tilde.functor R') ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_of_src _ _)

/-- **The source of the base-change map has nonzero cohomology in degree `-1`.** -/
theorem not_isZero_homology_source :
    ¬ IsZero ((DerivedCategory.homologyFunctor X'.Modules (-1)).obj
      ((derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward (Scheme.Hom.toLRSHom (𝟙 X)).toShHom).obj
          (((derivedSheafHom X.sheaf).obj (op E)).obj (DerivedCategory.Q.obj G))))) := by
  intro h
  have hflat : ∀ n : ℤ, Module.Flat (ZMod 4) (resolution.cochainComplex.X n) := fun n => by
    have := (isFiniteFree_resolution_X n).2
    infer_instance
  have hPk : CochainComplex.KFlat.{0, 0} resolution.cochainComplex :=
    CochainComplex.KFlat.kFlat_of_flat resolution.cochainComplex 0
  have hT := Stacks.TildeStalk.kFlatComplex_tilde (R := R) resolution.cochainComplex hPk
  have e₀ : E ≅ DerivedCategory.Q.obj
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        resolution.cochainComplex) :=
    (tilde.functor R).mapDerivedCategory.mapIso
        (RingTheory.TorIndependence.projectiveResolutionIsoSingle resolution).symm ≪≫
      (tilde.functor R).mapDerivedCategoryFactors.app resolution.cochainComplex
  have e₁ : (derivedPushforward (Scheme.Hom.toLRSHom (𝟙 X)).toShHom).obj
      (((derivedSheafHom X.sheaf).obj (op E)).obj (DerivedCategory.Q.obj G)) ≅ E :=
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso
      X.toRingedSpace).app _ ≪≫ sheafHomIso
  have := Stacks.DerivedPullback.isIso_derivedPullbackComplexComparison_app_of_kFlat
    g.toLRSHom.toShHom _ hT
  have e₂ := asIso ((Stacks.DerivedPullback.derivedPullbackComplexComparison
    g.toLRSHom.toShHom).app
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj resolution.cochainComplex))
  have e₃ := DerivedCategory.Q.mapIso ((tildePullbackComplexIso R R' φ).app
    resolution.cochainComplex)
  have e₄ := (DerivedCategory.homologyFunctorFactors X'.Modules (-1)).app
    (((tilde.functor R').mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.extendScalars.{0, 0, 0} φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        resolution.cochainComplex))
  have e₅ := (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
    (tilde.functor R') (ComplexShape.up ℤ) (-1)).app
      (((ModuleCat.extendScalars.{0, 0, 0} φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        resolution.cochainComplex)
  have e₆ : (((ModuleCat.extendScalars.{0, 0, 0} φ.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj resolution.cochainComplex).homology (-1) ≅
        reducedPeriodic.homology 1 :=
    RingTheory.TorIndependence.extendComplexIso toTwo periodic (-1) ≪≫
      HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingDownNat
        (RingTheory.TorIndependence.embeddingDownNat_f 1)
  have h₁ := h.of_iso ((DerivedCategory.homologyFunctor X'.Modules (-1)).mapIso
    ((derivedPullback g.toLRSHom.toShHom).mapIso (e₁ ≪≫ e₀) ≪≫ e₂ ≪≫ e₃)).symm
  have h₂ := (h₁.of_iso e₄.symm).of_iso e₅.symm
  exact not_isZero_tilde (fun hz => not_isZero_reducedPeriodic_homology_one (hz.of_iso e₆.symm)) h₂

/-- **The base-change map of case (2) of Stacks 08IE is not an isomorphism** for
`S = X = Spec ℤ/4`, `f = id`, `E = (ℤ/2)~`, `𝒢^• = 𝒪_X` and `g : Spec ℤ/2 ⟶ Spec ℤ/4`. -/
theorem not_isIso_sheafHomFlatBaseChangeMap :
    ¬ IsIso (sheafHomFlatBaseChangeMap (𝟙 X) g (𝟙 X') g sq E G) := fun hiso =>
  not_isZero_homology_source (isZero_homology_target.of_iso
    ((DerivedCategory.homologyFunctor X'.Modules (-1)).mapIso
      (@asIso _ _ _ _ (sheafHomFlatBaseChangeMap (𝟙 X) g (𝟙 X') g sq E G) hiso)))

/-- `E = (ℤ/2)~` is pseudo-coherent. -/
theorem isPseudoCoherent_E : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E :=
  (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent' E).1
    ((isPseudoCoherent_mapDerivedCategory_tilde_iff _).2 isPseudoCoherent_two)

/-- The terms of `𝒢^• = 𝒪_X[0]` are quasi-coherent. -/
theorem isQuasicoherent_G (n : ℤ) : (G.X n).IsQuasicoherent := by
  by_cases hn : n = 0
  · subst hn
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X)
  · exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n hn)

/-- The terms of `𝒢^• = 𝒪_X[0]` are flat over `S = X`. -/
theorem isFlatOver_G (n : ℤ) : IsFlatOver (Scheme.Hom.toLRSHom (𝟙 X)).toShHom (G.X n) :=
  ProperFlatBaseChange.isFlatOver_singleDegreeComplex (𝟙 X) _
    (fun x => (isFlatOverAt_unit_iff_isFlatAt (𝟙 X) x).mpr
      ((Flat.iff_flat_stalkMap (𝟙 X)).mp inferInstance x)) n

/-- `𝒢^• = 𝒪_X[0]` is strictly concentrated in degrees `≥ 0`. -/
theorem isStrictlyGE_G : G.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ i (by omega)

/-- `𝒢^• = 𝒪_X[0]` is strictly concentrated in degrees `≤ 0`. -/
theorem isStrictlyLE_G : G.IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ i (by omega)

/-- It is not true that for every quasi-compact
and quasi-separated `f : X ⟶ S`, every pseudo-coherent `E ∈ D(𝒪_X)`, every bounded complex
`𝒢^•` of quasi-coherent `𝒪_X`-modules flat over `S` and every cartesian square, the canonical map
`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)` of
`AlgebraicGeometry.sheafHomFlatBaseChangeMap` is an isomorphism. -/
@[stacks 08IE "the erratum's counterexample: case (2) for an ARBITRARY base change is false; it \
fails for S = X = Spec ℤ/4, f = id, E = (ℤ/2)~, 𝒢^• = 𝒪_X and g : Spec ℤ/2 ⟶ Spec ℤ/4"]
theorem not_forall_isIso_sheafHomFlatBaseChangeMap_of_isPseudoCoherent :
    ¬ ∀ {X X' S S' : Scheme.{0}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
      (_ : IsPullback g' f' f g) (_ : QuasiCompact f) (_ : QuasiSeparated f)
      (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
        f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
      (E : DerivedCategory X.Modules) (_ : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ) (a b : ℤ) (_ : G.IsStrictlyGE a) (_ : G.IsStrictlyLE b)
      (_ : ∀ n : ℤ, (G.X n).IsQuasicoherent)
      (_ : ∀ n : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X n)),
      IsIso (sheafHomFlatBaseChangeMap f g f' g' sq E G) := fun h =>
  not_isIso_sheafHomFlatBaseChangeMap (h (𝟙 X) g (𝟙 X') g isPullback inferInstance inferInstance
    sq E isPseudoCoherent_E G 0 0 isStrictlyGE_G isStrictlyLE_G isQuasicoherent_G isFlatOver_G)

end Stacks.Examples.SheafHomCounterexample
