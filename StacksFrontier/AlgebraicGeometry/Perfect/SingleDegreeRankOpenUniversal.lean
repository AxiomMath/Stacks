module

import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedFinite
import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankStratum
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristic
import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.AffineAvatar
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpen
import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Homology.Perfect.SingleDegreeFibre
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackRightExact

/-!
# The universal property of the single-degree rank open along an arbitrary morphism

Let `X` be a scheme, `E` a perfect object of `D(𝒪_X)`, `i` an integer and `r` a natural number.
`AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen E i r` is the largest open subscheme of `X`
on which `E` is a finite locally free module of rank `r` placed in degree `i`. A morphism
`f : Y ⟶ X` factors through it exactly when `Lf^*E` is isomorphic to a finite locally free module
of rank `r` placed in degree `i`, and a point `x` lies in it exactly when the derived fibre
`E ⊗ᴸ κ(x)` has cohomology of dimension `r` in degree `i` and `0` in every other degree.

## Main results

* `AlgebraicGeometry.Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff_derivedPullback`:
  the universal property.
* `AlgebraicGeometry.Scheme.Modules.mem_singleDegreeRankOpen_iff`: the pointwise description.
* `AlgebraicGeometry.Scheme.Modules.exists_iso_singleFunctor_derivedPullback_of_fac`: the forward
  direction, for every object of the derived category.
* `AlgebraicGeometry.Scheme.Modules.finrank_derivedFibreHomology_eq`: the derived fibre of `M̃`
  at a point of `Spec A` is the derived fibre `M ⊗ᴸ_A κ(p)` of `M ∈ D(A)`.
* `AlgebraicGeometry.Scheme.Modules.derivedPullbackIsoMapDerivedCategoryRestrict`: along an open
  immersion the derived pullback is restriction.
* `Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleFunctorIso`: the derived
  pullback of a flat module placed in degree `q` is its ordinary pullback placed in degree `q`.

## References

* [The Stacks Project, Lemma 36.31.3 (0BDK)](https://stacks.math.columbia.edu/tag/0BDK)
* [The Stacks Project, Lemma 36.31.1 (0BDI)](https://stacks.math.columbia.edu/tag/0BDI)
* [The Stacks Project, Lemma 15.77.7 (0BCD)](https://stacks.math.columbia.edu/tag/0BCD)
* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [The Stacks Project, Lemma 36.10.7 (08EB)](https://stacks.math.columbia.edu/tag/08EB)
* [The Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPullbackComparison)
open CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Modules

/-! ### Derived pullback along an open immersion, and of a flat module in one degree -/

/-- Along an open immersion `f` the derived pullback `Lf^*` is isomorphic to restriction along
`f` applied degreewise. -/
def derivedPullbackIsoMapDerivedCategoryRestrict {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] :
    derivedPullback f.toLRSHom.toShHom ≅ (restrictFunctor f).mapDerivedCategory :=
  have : PreservesFiniteLimits (modulePullback f.toLRSHom.toShHom) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion f
  have : PreservesFiniteColimits (modulePullback f.toLRSHom.toShHom) :=
    preservesFiniteColimits_modulePullback _
  have : PreservesFiniteLimits (Scheme.Modules.pullback f) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion f
  have : PreservesFiniteColimits (Scheme.Modules.pullback f) :=
    preservesFiniteColimits_modulePullback f.toLRSHom.toShHom
  have : PreservesFiniteColimits (restrictFunctor f) :=
    preservesFiniteColimits_of_natIso (restrictFunctorIsoPullback f).symm
  SpecField.derivedPullbackMapDerivedIso f.toLRSHom.toShHom ≪≫
    Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso
      (Scheme.Modules.pullback f) (restrictFunctor f) (restrictFunctorIsoPullback f).symm

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Cohomology.FlatSingleDerivedPullback

/-- For `F` a flat `𝒪_Y`-module, `Lf^*(F[-q])` is isomorphic to the pullback `f^*F` placed in
degree `q`. -/
def derivedPullbackSingleFunctorIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing Y))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F) (q : ℤ) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) q).obj F) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) q).obj
        ((modulePullback f).obj F) := by
  haveI : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) q).obj F)) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f _
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.sheaf F hF q)
  exact (derivedPullback f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{u} (structureSheafRing Y)) q).app F) ≪≫
    asIso ((derivedPullbackComparison f).app _) ≪≫
    DerivedCategory.Qh.mapIso (((modulePullback f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app _) ≪≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback f) (ComplexShape.up ℤ) q).app F) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X)) q).app
      ((modulePullback f).obj F)).symm

end Stacks.Cohomology.FlatSingleDerivedPullback

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (E : DerivedCategory X.Modules) (i : ℤ) (r : ℕ)

/-- If `f = g ≫ ι_U` with `U = singleDegreeRankOpen E i r`, then `Lf^*E` is isomorphic to a
finite locally free module of rank `r` placed in degree `i`. -/
theorem exists_iso_singleFunctor_derivedPullback_of_fac {Y : Scheme.{u}} (f : Y ⟶ X)
    (g : Y ⟶ (singleDegreeRankOpen E i r).toScheme)
    (hg : g ≫ (singleDegreeRankOpen E i r).ι = f) :
    ∃ M : Y.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
        Nonempty ((derivedPullback f.toLRSHom.toShHom).obj E ≅
          (DerivedCategory.singleFunctor Y.Modules i).obj M) := by
  subst hg
  let U := singleDegreeRankOpen E i r
  let N : U.toScheme.Modules := (DerivedCategory.homologyFunctor U.toScheme.Modules i).obj
    ((restrictFunctor U.ι).mapDerivedCategory.obj E)
  have hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r :=
    isFiniteLocallyFreeOfRank_homology_singleDegreeRankOpen E i r
  obtain ⟨eU⟩ := nonempty_iso_singleFunctor_restrict_singleDegreeRankOpen E i r
  have hNflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := U.toScheme.sheaf) N :=
    AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree N
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N r)
  exact ⟨(Scheme.Modules.pullback g).obj N, isFiniteLocallyFreeOfRank_pullback g N r,
    ⟨eqToIso (congrArg (fun k => (derivedPullback.{u, u + 1, u + 1} k).obj E)
        (BottomRankStratum.comp_toLRSHom_toShHom g U.ι)) ≪≫
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        g.toLRSHom.toShHom U.ι.toLRSHom.toShHom).app E).symm ≪≫
      (derivedPullback g.toLRSHom.toShHom).mapIso
        ((derivedPullbackIsoMapDerivedCategoryRestrict U.ι).app E ≪≫ eU) ≪≫
      Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleFunctorIso
        g.toLRSHom.toShHom N hNflat i⟩⟩

/-! ### The derived fibres of a finite locally free module placed in one degree -/

/-- If `G ≅ M[-i]` with `M` finite locally free of rank `r`, then at every point the derived fibre
of `G` has cohomology of dimension `r` in degree `i` and `0` in every other degree. -/
theorem finrank_derivedFibre_of_iso_singleFunctor {Y : Scheme.{u}} {G : DerivedCategory Y.Modules}
    {M : Y.Modules} (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r)
    (e : G ≅ (DerivedCategory.singleFunctor Y.Modules i).obj M) (y : Y) (j : ℤ) :
    Module.finrank (Y.residueField y)
        ((moduleSpecΓFunctor (R := Y.residueField y)).obj
          ((DerivedCategory.homologyFunctor (Spec (Y.residueField y)).Modules j).obj
            ((derivedPullback (Y.fromSpecResidueField y).toLRSHom.toShHom).obj G))) =
      if j = i then r else 0 := by
  have hMflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) M :=
    AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree M
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M r)
  let N : (Spec (Y.residueField y)).Modules :=
    (Scheme.Modules.pullback (Y.fromSpecResidueField y)).obj M
  have eN : (derivedPullback (Y.fromSpecResidueField y).toLRSHom.toShHom).obj G ≅
      (DerivedCategory.singleFunctor (Spec (Y.residueField y)).Modules i).obj N :=
    (derivedPullback (Y.fromSpecResidueField y).toLRSHom.toShHom).mapIso e ≪≫
      Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleFunctorIso
        (Y.fromSpecResidueField y).toLRSHom.toShHom M hMflat i
  split_ifs with hji
  · subst hji
    refine (((moduleSpecΓFunctor (R := Y.residueField y)).mapIso
      ((DerivedCategory.homologyFunctor (Spec (Y.residueField y)).Modules j).mapIso eN ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (Spec (Y.residueField y)).Modules j).app N)).toLinearEquiv.finrank_eq).trans ?_
    exact BottomRankStratum.finrank_moduleSpecΓ_eq_of_isFiniteLocallyFreeOfRank
      (Field.toIsField _) N r (isFiniteLocallyFreeOfRank_pullback _ M r)
  · have hz : IsZero ((moduleSpecΓFunctor (R := Y.residueField y)).obj
        ((DerivedCategory.homologyFunctor (Spec (Y.residueField y)).Modules j).obj
          ((derivedPullback (Y.fromSpecResidueField y).toLRSHom.toShHom).obj G))) :=
      Functor.map_isZero _ (IsZero.of_iso (isZero_homologyFunctor_singleFunctor_obj N hji)
        ((DerivedCategory.homologyFunctor (Spec (Y.residueField y)).Modules j).mapIso eN))
    have := ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton

/-- If `Lf^*E ≅ M[-i]` with `M` finite locally free of rank `r`, then at the image of every point
of `Y` the derived fibre of `E` has cohomology of dimension `r` in degree `i` and `0` elsewhere. -/
theorem finrank_derivedFibre_of_derivedPullback_iso {Y : Scheme.{u}} (f : Y ⟶ X)
    {M : Y.Modules} (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r)
    (e : (derivedPullback f.toLRSHom.toShHom).obj E ≅
      (DerivedCategory.singleFunctor Y.Modules i).obj M) (y : Y) (j : ℤ) :
    Module.finrank (X.residueField (f.base y))
        ((moduleSpecΓFunctor (R := X.residueField (f.base y))).obj
          ((DerivedCategory.homologyFunctor (Spec (X.residueField (f.base y))).Modules j).obj
            ((derivedPullback (X.fromSpecResidueField (f.base y)).toLRSHom.toShHom).obj E))) =
      if j = i then r else 0 :=
  (DerivedFibreBetti.finrank_residueFibre_eq f E y j).symm.trans
    (finrank_derivedFibre_of_iso_singleFunctor i r hM e y j)

/-! ### The derived fibre of a complex of associated sheaves -/

/-- Over the spectrum of a field `K`, the cohomology of the derived fibre of `H` at the point has
the same dimension in each degree as the cohomology of `H`. -/
theorem finrank_derivedFibre_spec_field {K : CommRingCat.{u}} (hK : IsField K) (z : Spec K)
    (H : DerivedCategory (Spec K).Modules) (j : ℤ) :
    Module.finrank ((Spec K).residueField z)
        ((moduleSpecΓFunctor (R := (Spec K).residueField z)).obj
          ((DerivedCategory.homologyFunctor (Spec ((Spec K).residueField z)).Modules j).obj
            ((derivedPullback ((Spec K).fromSpecResidueField z).toLRSHom.toShHom).obj H))) =
      Module.finrank K ((moduleSpecΓFunctor (R := K)).obj
        ((DerivedCategory.homologyFunctor (Spec K).Modules j).obj H)) := by
  have key : ∀ g : Spec ((Spec K).residueField z) ⟶ Spec K,
      g = Spec.map (Spec.preimage ((Spec K).fromSpecResidueField z)) →
      Module.finrank ((Spec K).residueField z)
        ((moduleSpecΓFunctor (R := (Spec K).residueField z)).obj
          ((DerivedCategory.homologyFunctor (Spec ((Spec K).residueField z)).Modules j).obj
            ((derivedPullback g.toLRSHom.toShHom).obj H))) =
      Module.finrank K ((moduleSpecΓFunctor (R := K)).obj
        ((DerivedCategory.homologyFunctor (Spec K).Modules j).obj H)) := by
    rintro g rfl
    exact SpecField.finrank_derivedPullback hK (Field.toIsField _) _ H j
  exact key _ (Spec.map_preimage _).symm

/-- The point of `Spec κ(q)` lies over `q` under `Spec κ(q) ⟶ Spec A`. -/
theorem SpecMap_algebraMap_residueField_base {A : CommRingCat.{u}} (p : PrimeSpectrum A)
    (z : PrimeSpectrum p.asIdeal.ResidueField) :
    (Spec.map (CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField))).base z = p := by
  have hz : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top z.asIdeal).resolve_right z.isPrime.ne_top
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap A p.asIdeal.ResidueField) z.asIdeal = p.asIdeal
  rw [hz, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

/-- For a ring map `ρ : A ⟶ K` and `M ∈ D(A)`, the cohomology of `L(Spec ρ)^*M̃` has, in each
degree, global sections of the same `K`-dimension as the cohomology of `M ⊗ᴸ_A K`. -/
theorem finrank_homology_specDerivedPullback_tilde {A K : CommRingCat.{u}} (ρ : A ⟶ K)
    (M : DerivedCategory (ModuleCat.{u} A)) (j : ℤ) :
    Module.finrank K ((moduleSpecΓFunctor (R := K)).obj
        ((DerivedCategory.homologyFunctor (Spec K).Modules j).obj
          ((StandardModel.specDerivedPullback ρ).obj
            ((tilde.functor A).mapDerivedCategory.obj M)))) =
      Module.finrank K ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) j).obj
        ((totalDerivedExtensionScalars.{u, u, u} ρ.hom).functor.obj M)) := by
  let N := (totalDerivedExtensionScalars.{u, u, u} ρ.hom).functor.obj M
  let e₁ : (StandardModel.specDerivedPullback ρ).obj
        ((tilde.functor A).mapDerivedCategory.obj M) ≅
      (tilde.functor K).mapDerivedCategory.obj N :=
    (StandardModel.affinePullbackComparison A K ρ).app M
  let e₂ := (derivedHomologyMapIso (tilde.functor K) N j).symm
  let e₃ := ((tilde.toTildeΓNatIso (R := K)).app
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) j).obj N)).symm
  exact ((moduleSpecΓFunctor (R := K)).mapIso
    ((DerivedCategory.homologyFunctor (Spec K).Modules j).mapIso e₁ ≪≫ e₂) ≪≫
      e₃).toLinearEquiv.finrank_eq

/-- The dimension of the derived fibre cohomology at a point depends only on the point. -/
private theorem finrank_derivedFibre_congr {S : Scheme.{u}} {w w' : S} (h : w = w')
    (E : DerivedCategory S.Modules) (j : ℤ) :
    Module.finrank (S.residueField w)
        ((moduleSpecΓFunctor (R := S.residueField w)).obj
          ((DerivedCategory.homologyFunctor (Spec (S.residueField w)).Modules j).obj
            ((derivedPullback (S.fromSpecResidueField w).toLRSHom.toShHom).obj E))) =
      Module.finrank (S.residueField w')
        ((moduleSpecΓFunctor (R := S.residueField w')).obj
          ((DerivedCategory.homologyFunctor (Spec (S.residueField w')).Modules j).obj
            ((derivedPullback (S.fromSpecResidueField w').toLRSHom.toShHom).obj E))) := by
  subst h
  rfl

/-- For `M ∈ D(A)` and `p ∈ Spec A`, the cohomology of the derived fibre of `M̃` at `p`, computed on
`Spec κ(p)` with the scheme-theoretic residue field, has the same dimension in each degree as the
cohomology of `M ⊗ᴸ_A κ(p)` with the ring-theoretic residue field. -/
theorem finrank_derivedFibreHomology_eq {A : CommRingCat.{u}}
    (M : DerivedCategory (ModuleCat.{u} A))
    (p : PrimeSpectrum A) (j : ℤ) :
    Module.finrank p.asIdeal.ResidueField
        (StacksDraft.Perfect.derivedFibreHomology.{u, u} p.asIdeal M j) =
      Module.finrank ((Spec A).residueField p)
        ((moduleSpecΓFunctor (R := (Spec A).residueField p)).obj
          ((DerivedCategory.homologyFunctor (Spec ((Spec A).residueField p)).Modules j).obj
            ((derivedPullback ((Spec A).fromSpecResidueField p).toLRSHom.toShHom).obj
              ((tilde.functor A).mapDerivedCategory.obj M)))) := by
  let κ : CommRingCat.{u} := CommRingCat.of p.asIdeal.ResidueField
  let ρ : A ⟶ κ := CommRingCat.ofHom (algebraMap A p.asIdeal.ResidueField)
  let t : Spec κ ⟶ Spec A := Spec.map ρ
  let T := (tilde.functor A).mapDerivedCategory.obj M
  let z : PrimeSpectrum p.asIdeal.ResidueField := IsLocalRing.closedPoint _
  exact (finrank_homology_specDerivedPullback_tilde ρ M j).symm.trans
    ((finrank_derivedFibre_spec_field (Field.toIsField κ) z _ j).symm.trans
      ((DerivedFibreBetti.finrank_residueFibre_eq t T z j).trans
        (finrank_derivedFibre_congr (SpecMap_algebraMap_residueField_base p z) T j)))

/-! ### The pointwise description -/

/-- A perfect object `G` of `D(𝒪_{Spec A})` is isomorphic to `M̃` for a perfect object `M` of
`D(A)`. -/
theorem exists_isPerfect_iso_mapDerivedCategory_tilde (A : CommRingCat.{u})
    (G : DerivedCategory (Spec A).Modules)
    (hG : RingedSpace.IsPerfect.{u, u + 1} (X := (Spec A).toRingedSpace) G) :
    ∃ M : DerivedCategory (ModuleCat.{u} A), StacksDraft.Perfect.IsPerfect M ∧
      Nonempty ((tilde.functor A).mapDerivedCategory.obj M ≅ G) := by
  obtain ⟨M, -, ⟨eM⟩⟩ := RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde A G
    (DerivedFibreBetti.isPseudoCoherent_of_isPerfect G hG)
  have hT : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace)
      ((tilde.functor A).mapDerivedCategory.obj M) :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := (Spec A).toRingedSpace)
      eM.symm hG
  exact ⟨M, (isPerfect_tilde_iff M).1 hT, ⟨eM⟩⟩

/-- Let `E` be perfect and let `x ∈ X` be a point at which the derived fibre `E ⊗ᴸ κ(x)` has
cohomology of dimension `r` in degree `i` and `0` in every other degree. Then
`x ∈ singleDegreeRankOpen E i r`. -/
theorem mem_singleDegreeRankOpen_of_finrank
    (hE : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E) (x : X)
    (hx : ∀ j : ℤ, Module.finrank (X.residueField x)
        ((moduleSpecΓFunctor (R := X.residueField x)).obj
          ((DerivedCategory.homologyFunctor (Spec (X.residueField x)).Modules j).obj
            ((derivedPullback (X.fromSpecResidueField x).toLRSHom.toShHom).obj E))) =
      if j = i then r else 0) :
    x ∈ singleDegreeRankOpen E i r := by
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let A : CommRingCat.{u} := Γ(X, W)
  let φ : Spec A ⟶ X := hW.fromSpec
  let p : PrimeSpectrum A := hW.primeIdealOf ⟨x, hxW⟩
  have hp : φ.base p = x := hW.fromSpec_primeIdealOf ⟨x, hxW⟩
  let G := (derivedPullback φ.toLRSHom.toShHom).obj E
  have hG : RingedSpace.IsPerfect.{u, u + 1} (X := (Spec A).toRingedSpace) G :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback φ.toLRSHom.toShHom E hE
  obtain ⟨M, hM, ⟨eM⟩⟩ := exists_isPerfect_iso_mapDerivedCategory_tilde A G hG
  have hfib (j : ℤ) : Module.finrank p.asIdeal.ResidueField
      (StacksDraft.Perfect.derivedFibreHomology.{u, u} p.asIdeal M j) =
        if j = i then r else 0 := by
    rw [finrank_derivedFibreHomology_eq M p j, ← hx j]
    exact (((moduleSpecΓFunctor (R := (Spec A).residueField p)).mapIso
      ((DerivedCategory.homologyFunctor (Spec ((Spec A).residueField p)).Modules j).mapIso
        ((derivedPullback ((Spec A).fromSpecResidueField p).toLRSHom.toShHom).mapIso
          eM))).toLinearEquiv.finrank_eq).trans
      ((DerivedFibreBetti.finrank_residueFibre_eq φ E p j).trans
        (finrank_derivedFibre_congr hp E j))
  obtain ⟨g, hg, ⟨e⟩⟩ :=
    StacksDraft.Perfect.exists_away_iso_singleFunctor_free_of_fibre_concentrated.{u, u}
      p.asIdeal M hM i (fun j hj => by rw [hfib j, ite_eq_right hj])
  set n := Module.finrank p.asIdeal.ResidueField
    (StacksDraft.Perfect.derivedFibreHomology.{u, u} p.asIdeal M i) with hn_def
  have hn : n = r := by rw [hn_def, hfib i, ite_eq_left rfl]
  let Ag := Localization.Away g
  let B : CommRingCat.{u} := CommRingCat.of Ag
  let b : A ⟶ B := CommRingCat.ofHom (algebraMap A Ag)
  let F : ModuleCat.{u} B := ModuleCat.of Ag (ULift.{u} (Fin n → Ag))
  let ψ : Spec B ⟶ X := Spec.map b ≫ φ
  have hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((tilde.functor B).obj F) r := by
    rw [← hn]
    exact (Stacks.Modules.tilde_isFiniteLocallyFreeOfRank_iff_module Ag
      (ULift.{u} (Fin n → Ag)) n).2
      (Module.IsFiniteLocallyFreeOfRank.of_basis
        ((Pi.basisFun Ag (Fin n)).map ULift.moduleEquiv.symm))
  let eψ : (restrictFunctor ψ).mapDerivedCategory.obj E ≅
      (DerivedCategory.singleFunctor (Spec B).Modules i).obj ((tilde.functor B).obj F) :=
    ((derivedPullbackIsoMapDerivedCategoryRestrict ψ).app E).symm ≪≫
      eqToIso (congrArg (fun k => (derivedPullback.{u, u + 1, u + 1} k).obj E)
        (BottomRankStratum.comp_toLRSHom_toShHom (Spec.map b) φ)) ≪≫
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (Spec.map b).toLRSHom.toShHom φ.toLRSHom.toShHom).app E).symm ≪≫
      (StandardModel.specDerivedPullback b).mapIso eM.symm ≪≫
      (StandardModel.affinePullbackComparison A B b).app M ≪≫
      (tilde.functor B).mapDerivedCategory.mapIso e ≪≫
      ((tilde.functor B).mapDerivedCategorySingleFunctor i).app F
  obtain ⟨h, hh⟩ := (factorsThrough_singleDegreeRankOpen_iff E i r ψ).2
    ⟨(tilde.functor B).obj F, hF, ⟨eψ⟩⟩
  obtain ⟨q, hq⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A Ag)) := by
    rwa [PrimeSpectrum.localization_away_comap_range Ag g]
  have hψq : ψ.base q = x := by
    rw [← hp, ← hq]
    rfl
  have hmem : (h ≫ (singleDegreeRankOpen E i r).ι).base q ∈
      Set.range (singleDegreeRankOpen E i r).ι.base := ⟨h.base q, rfl⟩
  rwa [Scheme.Opens.range_ι, hh, hψq] at hmem

/-- For `E` perfect, a point `x`
lies in `singleDegreeRankOpen E i r` exactly when the derived fibre `E ⊗ᴸ κ(x)` has cohomology of
dimension `r` in degree `i` and `0` in every other degree. -/
theorem mem_singleDegreeRankOpen_iff
    (hE : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E) (x : X) :
    x ∈ singleDegreeRankOpen E i r ↔ ∀ j : ℤ, Module.finrank (X.residueField x)
        ((moduleSpecΓFunctor (R := X.residueField x)).obj
          ((DerivedCategory.homologyFunctor (Spec (X.residueField x)).Modules j).obj
            ((derivedPullback (X.fromSpecResidueField x).toLRSHom.toShHom).obj E))) =
      if j = i then r else 0 := by
  refine ⟨fun hx j => ?_, mem_singleDegreeRankOpen_of_finrank E i r hE x⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_iso_singleFunctor_derivedPullback_of_fac E i r
    (singleDegreeRankOpen E i r).ι (𝟙 _) (Category.id_comp _)
  exact finrank_derivedFibre_of_derivedPullback_iso E i r (singleDegreeRankOpen E i r).ι hM e
    ⟨x, hx⟩ j

/-! ### The universal property -/

/-- Let `E` be a perfect object of `D(𝒪_X)`, `i` an integer and `r` a natural number. A morphism
of schemes `f : Y ⟶ X` factors through `singleDegreeRankOpen E i r` exactly when `Lf^*E` is
isomorphic to a finite locally free `𝒪_Y`-module of rank `r` placed in degree `i`. -/
@[stacks 0BDK "part (2): the universal property along an arbitrary morphism, rank r : N"]
theorem factorsThrough_singleDegreeRankOpen_iff_derivedPullback
    (hE : RingedSpace.IsPerfect.{u, u + 1} (X := X.toRingedSpace) E) {Y : Scheme.{u}}
    (f : Y ⟶ X) :
    (∃ g : Y ⟶ (singleDegreeRankOpen E i r).toScheme,
        g ≫ (singleDegreeRankOpen E i r).ι = f) ↔
      ∃ M : Y.Modules,
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
          Nonempty ((derivedPullback f.toLRSHom.toShHom).obj E ≅
            (DerivedCategory.singleFunctor Y.Modules i).obj M) := by
  refine ⟨fun ⟨g, hg⟩ => exists_iso_singleFunctor_derivedPullback_of_fac E i r f g hg, ?_⟩
  rintro ⟨M, hM, ⟨e⟩⟩
  have hrange : Set.range f.base ⊆ Set.range (singleDegreeRankOpen E i r).ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact mem_singleDegreeRankOpen_of_finrank E i r hE (f.base y)
      (finrank_derivedFibre_of_derivedPullback_iso E i r f hM e y)
  exact ⟨IsOpenImmersion.lift _ f hrange, IsOpenImmersion.lift_fac _ _ _⟩

end AlgebraicGeometry.Scheme.Modules

end
