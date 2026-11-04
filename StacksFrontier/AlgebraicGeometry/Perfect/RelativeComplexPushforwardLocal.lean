module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeComplexProjectionFormula
public import StacksFrontier.Algebra.Homology.DerivedCategory.StupidTruncationTriangle
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.RestrictionSpellings
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.MiddleTwoOutOfThree
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
public import StacksFrontier.AlgebraicGeometry.Perfect.VanishingHigherDirectImagesFlatness
public import StacksFrontier.AlgebraicGeometry.Perfect.ScalarRestrictionFlatOverConverse
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.TorDimensionOpenBase
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapDegenerate
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineDerivedPresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedPushforwardOpenBase
public import StacksFrontier.Homology.PseudoCoherent.Locality
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image of a locally bounded relative complex: Tag 0FML in full

Let `a : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and let `F^•` be a
*locally bounded* complex of `a⁻¹𝒪_S`-modules whose terms are flat over `a⁻¹𝒪_S` and carry
compatible quasi-coherent `𝒪_X`-module structures (the differentials need not be `𝒪_X`-linear).
Write `Ra_*F^•` for the unbounded derived pushforward along the morphism of ringed spaces
`a' : (X, a⁻¹𝒪_S) ⟶ (S, 𝒪_S)`. This file proves conclusions (1)–(3) of [Stacks, Tag 0FML] —
`Ra_*F^•` is locally bounded, lies in `D_QCoh(𝒪_S)` and locally has finite Tor dimension — and
registers the tag on the conjunction of all five conclusions, (4) and (5) being the projection
formulas of `StacksFrontier.AlgebraicGeometry.Perfect.RelativeComplexProjectionFormula`, stated at
the same object.

## Main results

* `isLocallyBounded_derivedPushforward_relativeComplex`: **conclusion (1)**.
* `derivedCategoryB_derivedPushforward_relativeComplex`: **conclusion (2)**, for a locally
  bounded complex and at the unbounded `Ra_*`.
* `locallyHasFiniteTorDimension_derivedPushforward_relativeComplex`: **conclusion (3)**.
* `relativeDerivedPushforward_locallyBounded_qcoh_torDimension_projectionFormula`:
  **[Stacks, Tag 0FML]**, all five conclusions under the tag's hypotheses.
* `prop_derivedPullback_derivedPushforward_of_isLocallyBounded`: the **reduction to an affine
  base and the dévissage**, for an arbitrary morphism of ringed spaces: a property of objects
  over an open `V` of the target, closed under isomorphism, zero objects and extensions, holds at
  `(Rg_*F^•)|_V` as soon as it holds at each `(Rg_*(F^i[-i]))|_V`, provided the preimage of `V`
  is quasi-compact.

## Implementation notes

Conclusions (1)–(3) are local on `S`, as the source says. The localisation is carried out by
open base change: for an open `V ⊆ S`, the base change of `a'` along `V ⟶ S` is an open
immersion upstairs (taken as a genuine fibre product of ringed spaces), along which the
restriction of a locally bounded complex has finitely many nonzero terms because the preimage of
an affine `V` is quasi-compact; the dévissage through the stupid filtration then runs over that
base change, and its single terms are carried back to `S` by base change again. No restriction
of the non-`𝒪_X`-linear complex to an open subscheme, and no identification of ringed spaces
`(a⁻¹V, (a⁻¹𝒪_S)|) ≅ (a⁻¹V, (a|_V)⁻¹𝒪_V)`, is needed.

At a single term `b_*N`, `N` quasi-coherent on `X`, the derived pushforward along `a'` is `Ra_*N`
(the factorisation `b ≫ a' = a` of `Stacks.DeRhamDirectImage.toInverseImageBase_comp`), and the
three properties over an affine `V` are: boundedness, by left exactness and the uniform vanishing
of [Stacks, Tag 01XJ] for `a|_V`; quasi-coherence, by the quasi-coherence of the higher direct
images; and finite Tor dimension, from the Mayer–Vietoris bound on the Tor amplitude of a derived
direct image of an object of finite Tor amplitude over the base
(`exists_hasTorAmplitude_schemeDerivedPushforward_of_hasTorAmplitudeOver`), which is the
source's induction on quasi-compact opens through [Stacks, Tag 08DR] and [Stacks, Tag 08HZ].
Flatness of a term over `a⁻¹𝒪_S` is read as flatness of `N` over `S` by
`AlgebraicGeometry.Scheme.Hom.isFlatOver_of_isFlat_scalarRestriction`. Flatness is used only in
conclusion (3) (and, through the base, in (4)).

Conclusion (1) is read as: every point of `S` has an open neighbourhood `U` such that
`(Ra_*F^•)|_U` has only finitely many nonzero cohomology sheaves, which is the meaning of
"locally bounded" for an object of `D(𝒪_S)`; the proof gives this for every affine `U`.

## References

* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 08CJ](https://stacks.math.columbia.edu/tag/08CJ)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry
open Stacks.DeRhamDirectImage
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.AlgebraicGeometry.Tag01XJUniformVanishing
  (exists_isZero_rightDerived_pushforward_of_isAffine)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
  (isZero_homologyFunctor_derivedPushforward_of_isZero_rightDerivedPlus)
open Stacks.AlgebraicGeometry.VanishingHigherDirectImages
  (exists_hasTorAmplitude_schemeDerivedPushforward_of_hasTorAmplitudeOver)
open Stacks.AlgebraicGeometry.PerfectProperDirectImage
  (locallyHasFiniteTorDimension_of_forall_affineOpen_restrictFunctor)

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace Stacks.RelativeComplexPushforward

attribute [local instance] Stacks.DeRhamDirectImage.abelian_modules
  Stacks.DeRhamDirectImage.isGrothendieckAbelian_modules

section Devissage

variable {Z W : RingedSpace.{u, u}} (g : Z ⟶ W) (V : Opens W.carrier)

/-- **The reduction to an open of the base and the dévissage, for a locally bounded complex.**
Let `g : Z ⟶ W` be a morphism of ringed spaces, `V` an open of `W` whose preimage in `Z` is
quasi-compact, and `Q` a property of objects of `D(𝒪_V)` invariant under isomorphism, holding at
zero objects and closed under extensions in distinguished triangles. If `Q` holds at the
restriction to `V` of `Rg_*(F^i[-i])` for every `i`, it holds at the restriction to `V` of
`Rg_*F^•`, for every locally bounded complex `F^•` of `𝒪_Z`-modules.

The restriction to `V` is the derived pullback along the inclusion of `V`; by open base change
([Stacks, Tag 08FE] in the form
`Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions`) it is the
derived pushforward from the fibre product of the pullback of `F^•`, which has finitely many
nonzero terms, so the stupid filtration applies there; its single terms are carried back by the
same base change. -/
theorem prop_derivedPullback_derivedPushforward_of_isLocallyBounded
    (hcpt : IsCompact ((((Opens.map g.hom.base).obj V) : Opens Z.carrier) : Set Z.carrier))
    (Q : DerivedCategory (Modules (W.restrict V.isOpenEmbedding)) → Prop)
    (hiso : ∀ {A B : DerivedCategory (Modules (W.restrict V.isOpenEmbedding))}, (A ≅ B) →
      Q A → Q B)
    (hzero : ∀ A : DerivedCategory (Modules (W.restrict V.isOpenEmbedding)), IsZero A → Q A)
    (hext : ∀ T : Triangle (DerivedCategory (Modules (W.restrict V.isOpenEmbedding))),
      T ∈ distTriang _ → Q T.obj₁ → Q T.obj₃ → Q T.obj₂)
    (F : CochainComplex (Modules Z) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded Z F)
    (hsingle : ∀ i : ℤ, Q ((derivedPullback (W.ofRestrict V.isOpenEmbedding)).obj
      ((derivedPushforward g).obj
        ((DerivedCategory.singleFunctor (Modules Z) i).obj (F.X i))))) :
    Q ((derivedPullback (W.ofRestrict V.isOpenEmbedding)).obj
      ((derivedPushforward g).obj (DerivedCategory.Q.obj F))) := by
  set e := W.ofRestrict V.isOpenEmbedding with he
  have sq : IsPullback (pullback.fst g e) (pullback.snd g e) g e :=
    IsPullback.of_hasPullback g e
  have hrange : Set.range (pullback.fst g e).hom.base ⊆
      ((((Opens.map g.hom.base).obj V) : Opens Z.carrier) : Set Z.carrier) := by
    rintro z ⟨p, rfl⟩
    have hmem : (pullback.fst g e ≫ g).hom.base p ∈ ((V : Opens W.carrier) : Set W.carrier) := by
      rw [sq.w]
      exact (Stacks.DerivedGlueing.range_ofRestrict V).le
        (Stacks.DerivedGlueing.range_comp_subset_range (pullback.snd g e).hom.base e.hom.base
          ⟨p, rfl⟩)
    exact hmem
  have hbc : ∀ K : DerivedCategory (Modules Z),
      IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
        (pullback.fst g e) (pullback.snd g e) g e sq.w K) := fun K =>
    Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersions
      (pullback.fst g e) (pullback.snd g e) g e sq K
  refine hiso (@asIso _ _ _ _ (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
    (pullback.fst g e) (pullback.snd g e) g e sq.w _) (hbc _)).symm ?_
  refine hiso ((derivedPushforward (pullback.snd g e)).mapIso
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionComplexIso
      (pullback.fst g e) F).symm) ?_
  let : (derivedPushforward (pullback.snd g e)).CommShift ℤ :=
    (derivedAdjunction (pullback.snd g e)).rightAdjointCommShift ℤ
  let : (derivedAdjunction (pullback.snd g e)).CommShift ℤ :=
    (derivedAdjunction (pullback.snd g e)).commShift_of_leftAdjoint ℤ
  have : (derivedPushforward (pullback.snd g e)).IsTriangulated :=
    (derivedAdjunction (pullback.snd g e)).isTriangulated_rightAdjoint
  refine Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex_of_distTriang
    (fun A => Q ((derivedPushforward (pullback.snd g e)).obj A))
    (fun e' h => hiso ((derivedPushforward (pullback.snd g e)).mapIso e') h)
    (fun A hA => hzero _ ((derivedPushforward (pullback.snd g e)).map_isZero hA))
    (fun T hT h₁ h₃ => hext _ ((derivedPushforward (pullback.snd g e)).map_distinguished T hT)
      h₁ h₃) _
    (Stacks.Cohomology.LocallyBoundedPullback.finite_support_modulePullback_of_isLocallyBounded
      (pullback.fst g e) F hF _ hcpt hrange) fun i => ?_
  refine hiso ((derivedPushforward (pullback.snd g e)).mapIso
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionSingleIso
      (pullback.fst g e) i (F.X i))) ?_
  refine hiso (@asIso _ _ _ _ (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
    (pullback.fst g e) (pullback.snd g e) g e sq.w _) (hbc _)) ?_
  exact hsingle i

end Devissage

/-! ### Tor amplitude on a ringed space at a zero object -/

section TorAmplitudeShift

open Stacks.Cohomology.TorAmplitude

variable {Y : RingedSpace.{u, u}}

/-- **A zero object of `D(𝒪_Y)` has Tor amplitude in every interval**: its derived tensor
product with any module is zero, the derived tensor product being exact in its first variable. -/
theorem hasTorAmplitude_of_isZero_obj (E : DerivedCategory (Modules Y)) (hE : IsZero E)
    (a b : ℤ) :
    HasTorAmplitude Y E a b := by
  intro G i _
  let : ((derivedTensorProductFunctor Y.sheaf).flip.obj
      ((DerivedCategory.singleFunctor (Modules Y) 0).obj G)).CommShift ℤ :=
    (canonicalDerivedTensorProduct Y.sheaf).commShift_left _
  have : ((derivedTensorProductFunctor Y.sheaf).flip.obj
      ((DerivedCategory.singleFunctor (Modules Y) 0).obj G)).IsTriangulated :=
    (canonicalDerivedTensorProduct Y.sheaf).exact_left _
  exact (DerivedCategory.homologyFunctor (Modules Y) i).map_isZero
    (((derivedTensorProductFunctor Y.sheaf).flip.obj
      ((DerivedCategory.singleFunctor (Modules Y) 0).obj G)).map_isZero hE)

end TorAmplitudeShift

/-! ### The single-sheaf case, crossed to the morphism of schemes -/

section SingleSheafPushforward

open Stacks.SchemeCohomology (hom)

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The derived pushforwards along two equal morphisms agree. -/
def derivedPushforwardObjIsoOfEq {Z W : RingedSpace.{u, u}} {φ ψ : Z ⟶ W} (h : φ = ψ)
    (A : DerivedCategory (Modules Z)) :
    (derivedPushforward φ).obj A ≅ (derivedPushforward ψ).obj A := by
  subst h
  exact Iso.refl _

/-- `Ra'_*(b_*N[i]) ≅ Rf_*(N[i])`. -/
def derivedPushforwardRelativeSingleIso (N : X.Modules) (i : ℤ) :
    (derivedPushforward (inverseImageBaseProjection f)).obj
        ((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj
          ((pushforward (toInverseImageBase f)).obj N)) ≅
      (derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (Modules X.toRingedSpace) i).obj N) :=
  (derivedPushforward (inverseImageBaseProjection f)).mapIso
      (((shiftFunctorZero _ ℤ).app _).symm ≪≫
        (derivedPushforwardToInverseImageBaseSingleShiftIso f N i 0).symm ≪≫
        (derivedPushforward (toInverseImageBase f)).mapIso ((shiftFunctorZero _ ℤ).app _)) ≪≫
    (derivedPushforwardCompIso (toInverseImageBase f) (inverseImageBaseProjection f)).app _ ≪≫
    derivedPushforwardObjIsoOfEq (toInverseImageBase_comp f) _

/-- The restriction to an open `V` of the base of `Ra'_*(b_*N[i])` is the restriction of
`Rf_*(N[i])`. -/
def derivedPullbackRelativeSingleIso (V : S.Opens) (N : X.Modules) (i : ℤ) :
    (derivedPullback (S.toRingedSpace.ofRestrict V.isOpenEmbedding)).obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          ((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).obj
            ((pushforward (toInverseImageBase f)).obj N))) ≅
      (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor (Modules X.toRingedSpace) i).obj N)) :=
  (Stacks.RestrictionSpellings.derivedPullbackIsoRestrictFunctor S V).app _ ≪≫
    (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.mapIso
      (derivedPushforwardRelativeSingleIso f N i)

end SingleSheafPushforward

/-! ### The single-sheaf facts over an affine open of the base -/

section SingleSheafFacts

open Stacks.Cohomology.TorAmplitude

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `(Rf_*(N[i]))|_U ≅ ((Rf_*(N[0]))|_U)⟦-i⟧`. -/
def restrictPushforwardSingleShiftIso (U : S.Opens) (N : X.Modules) (i : ℤ) :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor (Modules X.toRingedSpace) i).obj N)) ≅
      (shiftFunctor (DerivedCategory U.toScheme.Modules) (-i)).obj
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor (Modules X.toRingedSpace) 0).obj N))) :=
  letI : (derivedPushforward f.toLRSHom.toShHom).CommShift ℤ :=
    (derivedAdjunction f.toLRSHom.toShHom).rightAdjointCommShift ℤ
  (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.mapIso
      ((derivedPushforward f.toLRSHom.toShHom).mapIso
        (((DerivedCategory.singleFunctors (Modules X.toRingedSpace)).shiftIso (-i) i 0
          (by omega)).app N).symm ≪≫
       ((derivedPushforward f.toLRSHom.toShHom).commShiftIso (-i)).app _) ≪≫
    ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.commShiftIso (-i)).app _

/-- Over an affine base, `Rg_*(N[0])` of a quasi-coherent `N` is cohomologically bounded:
below by left exactness, above by [Stacks, Tag 01XJ]. -/
theorem isBounded_derivedPushforward_single_of_isAffine {Y W : Scheme.{u}} (g : Y ⟶ W)
    [IsAffine W] [QuasiCompact g] [QuasiSeparated g] (N : Y.Modules) (hN : N.IsQuasicoherent) :
    DerivedCategoryB.IsBounded ((derivedPushforward g.toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor Y.Modules 0).obj N)) := by
  obtain ⟨n, hn⟩ :=
    exists_isZero_rightDerived_pushforward_of_isAffine g
  refine ⟨⟨0, fun p hp => ?_⟩, ⟨n, fun p hp => ?_⟩⟩
  · exact (DerivedCategory.isGE_iff _ 0).1
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.isGE_derivedPushforward g
        ((DerivedCategory.singleFunctor Y.Modules 0).obj N) 0 inferInstance) p hp
  · exact isZero_homologyFunctor_derivedPushforward_of_isZero_rightDerivedPlus g N p
      (hn p hp.le N hN)

/-- **Boundedness of the single-sheaf term over an affine open of the base.** -/
theorem isBounded_restrict_derivedPushforward_single [QuasiCompact f] [QuasiSeparated f]
    (V : S.affineOpens) (N : X.Modules) (hN : N.IsQuasicoherent) (i : ℤ) :
    DerivedCategoryB.IsBounded
      ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).mapDerivedCategory.obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor (Modules X.toRingedSpace) i).obj N))) := by
  have : IsAffine (V : S.Opens).toScheme := V.2
  have : N.IsQuasicoherent := hN
  refine DerivedCategoryB.isBounded_of_iso (restrictPushforwardSingleShiftIso f V N i).symm
    (DerivedCategoryB.isBounded_shift (-i) ?_)
  exact DerivedCategoryB.isBounded_of_iso
    ((schemeDerivedPushforward (f ∣_ (V : S.Opens))).mapIso
      ((Functor.mapDerivedCategorySingleFunctor
        (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι) 0).app N).symm ≪≫
      (schemeDerivedPushforwardRestrictOpensIso f (V : S.Opens) _).symm)
    (isBounded_derivedPushforward_single_of_isAffine (f ∣_ (V : S.Opens)) _ inferInstance)

/-- **Quasi-coherence of the single-sheaf term over an open of the base.** -/
theorem derivedCategoryB_restrict_derivedPushforward_single [QuasiCompact f] [QuasiSeparated f]
    (U : S.Opens) (N : X.Modules) (hN : N.IsQuasicoherent) (i : ℤ) :
    DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor (Modules X.toRingedSpace) i).obj N))) :=
  fun n => isQuasicoherent_homology_restrictFunctor_mapDerivedCategory U.ι
    (fun m => isQuasicoherent_homology_derivedPushforward_singleFunctor f N hN i m) n

/-- **The Tor bound on an affine open of the base for the derived direct image of a module flat
over the base, placed in degree `i`**, for `f` quasi-compact and quasi-separated:
`(Rf_*(ℱ[-i]))|_V` has Tor amplitude in `[i, b]` for some `b`.

This is the argument of `exists_hasTorAmplitude_restrict_derivedPushforward_single` in
`Stacks.AlgebraicGeometry.VanishingHigherDirectImages`, which assumes `f` of finite presentation
and the module in degree `0`, but uses only that `f` is quasi-compact and quasi-separated. -/
theorem exists_hasTorAmplitude_restrict_derivedPushforward_single_of_qcqs [QuasiCompact f]
    [QuasiSeparated f] (N : X.Modules) (hqc : N.IsQuasicoherent)
    (hflat : IsFlatOver f.toLRSHom.toShHom N) (V : S.affineOpens) (i : ℤ) :
    ∃ b : ℤ, HasTorAmplitude (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding)
      ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).mapDerivedCategory.obj
        ((schemeDerivedPushforward f).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj N)))) i b := by
  have : IsAffine (V : S.Opens).toScheme := V.2
  have : CompactSpace (f ⁻¹ᵁ (V : S.Opens)).toScheme :=
    isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := f) _ (V : S.Opens).isOpen V.2.isCompact)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ (V : S.Opens)).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ (V : S.Opens))
  have hEqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj N))).IsQuasicoherent :=
    fun j => (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor X.Modules j).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ X.Modules i).app N))
      (derivedCategoryB_isQuasicoherent_single N hqc i j)
  have hEtor : HasTorAmplitudeOver f
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj N)) i i := by
    refine hasTorAmplitudeOver_of_isFlatOver f _ i i fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [isFlatOver_iff_of_moduleIso f.toLRSHom.toShHom
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j N)]
      exact hflat
    · exact isFlatOver_of_isZero f _
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i N j hj)
  have hEtorV : HasTorAmplitudeOver (f ∣_ (V : S.Opens))
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj N))) i i :=
    (hasTorAmplitudeOver_comp_iff_of_isOpenImmersion (f ∣_ (V : S.Opens)) (V : S.Opens).ι _
      i i).1 (by
        rw [morphismRestrict_ι]
        exact hasTorAmplitudeOver_restrictFunctor f (f ⁻¹ᵁ (V : S.Opens)).ι _ i i hEtor)
  obtain ⟨b, hb⟩ := exists_hasTorAmplitude_schemeDerivedPushforward_of_hasTorAmplitudeOver
    (f ∣_ (V : S.Opens)) _
    (isQuasicoherent_homology_restrictFunctor_mapDerivedCategory (f ⁻¹ᵁ (V : S.Opens)).ι hEqc)
    i i hEtorV
  exact ⟨b, FlatOpcycles.hasTorAmplitude_of_iso
    (X := S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding) hb
    (schemeDerivedPushforwardRestrictOpensIso f (V : S.Opens) _)⟩

/-- **Finite Tor dimension of the single-sheaf term over an affine open of the base.** -/
theorem hasFiniteTorDimension_restrict_derivedPushforward_single [QuasiCompact f]
    [QuasiSeparated f] (V : S.affineOpens) (N : X.Modules) (hN : N.IsQuasicoherent)
    (hflat : IsFlatOver f.toLRSHom.toShHom N) (i : ℤ) :
    HasFiniteTorDimension (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding)
      ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).mapDerivedCategory.obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor (Modules X.toRingedSpace) i).obj N))) := by
  obtain ⟨b, hb⟩ :=
    exists_hasTorAmplitude_restrict_derivedPushforward_single_of_qcqs f N hN hflat V i
  exact ⟨i, b, FlatOpcycles.hasTorAmplitude_of_iso
    (X := S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding) hb
    ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).mapDerivedCategory.mapIso
      ((derivedPushforward f.toLRSHom.toShHom).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ X.Modules i).app N)))⟩

end SingleSheafFacts

/-! ### Conclusions (1), (2) and (3), and the tag -/

section Tag

open Stacks.Cohomology.TorAmplitude

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The reduction of conclusions (1)–(3) to a single quasi-coherent sheaf, over an affine open
of the base.** For a property `Q` of objects of `D(𝒪_V)` invariant under isomorphism, holding at
zero objects and closed under extensions in distinguished triangles, `Q` holds at the restriction
to `V` of `Ra'_*F^•` as soon as it holds at the restriction to `V` of `Rf_*(M^i[-i])` for every
`i`. -/
theorem prop_restrict_derivedPushforward_relativeComplex [QuasiCompact f] (V : S.affineOpens)
    (Q : DerivedCategory (Modules (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding)) →
      Prop)
    (hiso : ∀ {A B : DerivedCategory
      (Modules (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding))}, (A ≅ B) → Q A → Q B)
    (hzero : ∀ A : DerivedCategory
      (Modules (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding)), IsZero A → Q A)
    (hext : ∀ T : Triangle (DerivedCategory
        (Modules (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding))),
      T ∈ distTriang _ → Q T.obj₁ → Q T.obj₃ → Q T.obj₂)
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (M : ℤ → X.Modules)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i))
    (hsingle : ∀ i : ℤ, Q ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).mapDerivedCategory.obj
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (Modules X.toRingedSpace) i).obj (M i))))) :
    Q ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).mapDerivedCategory.obj
      ((derivedPushforward (inverseImageBaseProjection f)).obj (DerivedCategory.Q.obj F))) := by
  have key : Q ((derivedPullback (S.toRingedSpace.ofRestrict (V : S.Opens).isOpenEmbedding)).obj
      ((derivedPushforward (inverseImageBaseProjection f)).obj (DerivedCategory.Q.obj F))) := by
    refine prop_derivedPullback_derivedPushforward_of_isLocallyBounded
      (inverseImageBaseProjection f) (V : S.Opens) (f.isCompact_preimage V.2.isCompact) Q hiso
      hzero hext F hF fun i => ?_
    have e₁ := (derivedPullback (S.toRingedSpace.ofRestrict (V : S.Opens).isOpenEmbedding)).mapIso
      ((derivedPushforward (inverseImageBaseProjection f)).mapIso
        ((DerivedCategory.singleFunctor (Modules (inverseImageBase f)) i).mapIso (hFM i)))
    have e₂ := derivedPullbackRelativeSingleIso f V (M i) i
    exact hiso (e₁ ≪≫ e₂).symm (hsingle i)
  have e₃ := (Stacks.RestrictionSpellings.derivedPullbackIsoRestrictFunctor S V).app
    ((derivedPushforward (inverseImageBaseProjection f)).obj (DerivedCategory.Q.obj F))
  exact hiso e₃ key

/-- **Stacks Project, Tag 0FML, conclusion (1)**: `Ra_*F^•` is locally bounded. Every point of
`S` has an open neighbourhood `U` on which `(Ra_*F^•)|_U` has only finitely many nonzero
cohomology sheaves. Flatness of the terms is not needed for this conclusion. -/
theorem isLocallyBounded_derivedPushforward_relativeComplex
    [QuasiCompact f] [QuasiSeparated f]
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ DerivedCategoryB.IsBounded
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj (DerivedCategory.Q.obj F))) := by
  intro s
  have hs : s ∈ (⊤ : S.Opens) := trivial
  rw [← iSup_affineOpens_eq_top S] at hs
  obtain ⟨V, hV⟩ := Opens.mem_iSup.1 hs
  exact ⟨V, hV, prop_restrict_derivedPushforward_relativeComplex f V DerivedCategoryB.IsBounded
    (fun e h => DerivedCategoryB.isBounded_of_iso e h)
    (fun _ hA => DerivedCategoryB.isBounded_of_isZero hA)
    (fun T hT h₁ h₃ => DerivedCategoryB.isBounded_mem_obj₂_of_distinguished T hT h₁ h₃)
    F hF M hFM fun i => isBounded_restrict_derivedPushforward_single f V (M i) (hM i) i⟩

/-- The restriction to an affine open of `Ra_*F^•` lies in `D_QCoh`. -/
theorem derivedCategoryB_restrict_derivedPushforward_relativeComplex
    [QuasiCompact f] [QuasiSeparated f]
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i))
    (U : S.Opens) (hU : IsAffineOpen U) :
    DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj (DerivedCategory.Q.obj F))) := by
  have hB := Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre
    U.toScheme
  refine prop_restrict_derivedPushforward_relativeComplex f ⟨U, hU⟩
    (DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf))
    (fun e h => (DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _ hB).of_iso e h)
    (fun A hA => ?_)
    (fun T hT h₁ h₃ =>
      DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _ hB T hT h₁ h₃)
    F hF M hFM (fun i => derivedCategoryB_restrict_derivedPushforward_single f U (M i) (hM i) i)
  obtain ⟨Z, hZ, hPZ⟩ := (DerivedCategoryB.derivedCategoryB_containsZero _ hB).exists_zero
  exact (DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _ hB).of_iso
    (hZ.iso hA) hPZ

/-- **Stacks Project, Tag 0FML, conclusion (2)**: `Ra_*F^•` lies in `D_QCoh(𝒪_S)`, for a locally
bounded `F^•`. Flatness of the terms is not needed for this conclusion. -/
theorem derivedCategoryB_derivedPushforward_relativeComplex
    [QuasiCompact f] [QuasiSeparated f]
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    (DerivedCategoryB.derivedCategoryB (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) :
      ObjectProperty (DerivedCategory (Modules S.toRingedSpace)))
      ((derivedPushforward (inverseImageBaseProjection f)).obj (DerivedCategory.Q.obj F)) := by
  intro n
  refine isQuasicoherent_of_restrict_isAffineOpen _ fun U hU => ?_
  exact (_root_.SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.restrictFunctor U.ι) n).app _)
    (derivedCategoryB_restrict_derivedPushforward_relativeComplex f F hF M hM hFM U hU n)

/-- The restriction to an affine open of `Ra_*F^•` has finite Tor dimension. -/
theorem hasFiniteTorDimension_restrict_derivedPushforward_relativeComplex
    [QuasiCompact f] [QuasiSeparated f]
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hflatM : ∀ i, IsFlatOver f.toLRSHom.toShHom (M i))
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) (V : S.affineOpens) :
    HasFiniteTorDimension (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding)
      ((Scheme.Modules.restrictFunctor (V : S.Opens).ι).mapDerivedCategory.obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj (DerivedCategory.Q.obj F))) := by
  refine prop_restrict_derivedPushforward_relativeComplex f V
    (HasFiniteTorDimension (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding))
    (fun e h => ?_) (fun A hA => ?_) (fun T hT h₁ h₃ => ?_) F hF M hFM fun i =>
      hasFiniteTorDimension_restrict_derivedPushforward_single f V (M i) (hM i) (hflatM i) i
  · obtain ⟨a, b, h⟩ := h
    exact ⟨a, b, FlatOpcycles.hasTorAmplitude_of_iso
      (X := S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding) h e.symm⟩
  · exact ⟨0, 0, hasTorAmplitude_of_isZero_obj
      (Y := S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding) A hA 0 0⟩
  · obtain ⟨a, b, h₁⟩ := h₁
    obtain ⟨c, d, h₃⟩ := h₃
    exact ⟨min a c, max b d, FlatOpcycles.hasTorAmplitude_obj₂
      (X := S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding) T hT _ _
      (FlatOpcycles.hasTorAmplitude_mono
        (X := S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding) h₁
        (min_le_left _ _) (le_max_left _ _))
      (FlatOpcycles.hasTorAmplitude_mono
        (X := S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding) h₃
        (min_le_right _ _) (le_max_right _ _))⟩

/-- **Stacks Project, Tag 0FML, conclusion (3)**: `Ra_*F^•` locally has finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_derivedPushforward_relativeComplex
    [QuasiCompact f] [QuasiSeparated f]
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase f).sheaf) (F.X i))
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    LocallyHasFiniteTorDimension S.toRingedSpace
      ((derivedPushforward (inverseImageBaseProjection f)).obj (DerivedCategory.Q.obj F)) :=
  locallyHasFiniteTorDimension_of_forall_affineOpen_restrictFunctor S _ fun V =>
    hasFiniteTorDimension_restrict_derivedPushforward_relativeComplex f F hF M hM
      (fun i => Scheme.Hom.isFlatOver_of_isFlat_scalarRestriction f (M i)
        (AlgebraicGeometry.SheafOfModules.IsFlat.of_iso _ (hFM i) (hflat i))) hFM V

/-- **Stacks Project, Tag 0FML.** Let `a : X ⟶ S` be a quasi-compact and quasi-separated
morphism of schemes and `F^•` a locally bounded complex of `a⁻¹𝒪_S`-modules, each term `F^n` a
flat `a⁻¹𝒪_S`-module carrying the structure of a quasi-coherent `𝒪_X`-module `M n` compatible
with its `a⁻¹𝒪_S`-module structure (`F^n ≅ b_*(M n)` for `b : (X, 𝒪_X) ⟶ (X, a⁻¹𝒪_S)`; the
differentials of `F^•` need not be `𝒪_X`-linear). Write `Ra_*F^•` for the derived pushforward
along the morphism of ringed spaces `(X, a⁻¹𝒪_S) ⟶ (S, 𝒪_S)`. Then

1. `Ra_*F^•` is locally bounded: every point of `S` has an open neighbourhood `U` on which
   `(Ra_*F^•)|_U` has only finitely many nonzero cohomology sheaves;
2. `Ra_*F^•` lies in `D_QCoh(𝒪_S)`;
3. `Ra_*F^•` locally has finite Tor dimension;
4. `Ra_*F^• ⊗^𝐋_{𝒪_S} 𝒢 ≅ Ra_*(F^• ⊗_{a⁻¹𝒪_S} a⁻¹𝒢)` for every quasi-coherent `𝒢`;
5. the map of [Stacks, Tag 0B53] `Ra_*F^• ⊗^𝐋_{𝒪_S} K ⟶ Ra_*(F^• ⊗^𝐋_{a⁻¹𝒪_S} a⁻¹K)` is an
   isomorphism for every `K` in `D_QCoh(𝒪_S)`.

The tensor products in (4) and (5) are written in the order the map of [Stacks, Tag 0B53]
produces them, the opposite of the source's; the two orders agree by symmetry. Conclusions (4)
and (5) are `relativeComplexOrdinaryProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent` and
`isIso_projectionFormulaMap_relativeComplex_of_isLocallyBounded_of_isQuasicoherent`.
Conclusions (1)–(3) are local on `S`; over an affine open `V` the complex is bounded on the
quasi-compact `a⁻¹V`, and `prop_restrict_derivedPushforward_relativeComplex` reduces each of
them to a single quasi-coherent `M n`, where (1) is [Stacks, Tag 01XJ], (2) is the
quasi-coherence of the higher direct images and (3) is the Mayer–Vietoris bound on Tor amplitude
of a derived direct image of a module flat over the base. -/
@[stacks 0FML "all five conclusions, under exactly the source's hypotheses: a : X ⟶ S \
quasi-compact and quasi-separated, F^• a LOCALLY BOUNDED complex of a^{-1}O_S-modules with flat \
terms each carrying a compatible quasi-coherent O_X-module structure (differentials not \
O_X-linear); Ra_* is the unbounded derived pushforward along (X, a^{-1}O_S) ⟶ (S, O_S). (1) every \
point of S has an open neighbourhood U with (Ra_*F^•)|_U cohomologically bounded; (2) Ra_*F^• in \
D_QCoh(O_S); (3) LocallyHasFiniteTorDimension at the derived tensor product of Tag 06YU; (4) an \
isomorphism Ra_*F^• ⊗ᴸ G ≅ Ra_*(F^• ⊗ a^{-1}G) for G quasi-coherent; (5) invertibility of the \
Tag 0B53 map for K in D_QCoh(O_S). Tensor factors in (4), (5) are in the order the Tag 0B53 map \
produces them, the opposite of the source's"]
theorem relativeDerivedPushforward_locallyBounded_qcoh_torDimension_projectionFormula
    [QuasiCompact f] [QuasiSeparated f]
    (F : CochainComplex (Modules (inverseImageBase f)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase f) F)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase f).sheaf) (F.X i))
    (M : ℤ → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent)
    (hFM : ∀ i, F.X i ≅ (pushforward (toInverseImageBase f)).obj (M i)) :
    (∀ s : S, ∃ U : S.Opens, s ∈ U ∧ DerivedCategoryB.IsBounded
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj F)))) ∧
    (DerivedCategoryB.derivedCategoryB (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) :
      ObjectProperty (DerivedCategory (Modules S.toRingedSpace)))
      ((derivedPushforward (inverseImageBaseProjection f)).obj (DerivedCategory.Q.obj F)) ∧
    LocallyHasFiniteTorDimension S.toRingedSpace
      ((derivedPushforward (inverseImageBaseProjection f)).obj (DerivedCategory.Q.obj F)) ∧
    (∀ G : Modules S.toRingedSpace, G.IsQuasicoherent →
      Nonempty (((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
          ((derivedPushforward (inverseImageBaseProjection f)).obj
            (DerivedCategory.Q.obj F))).obj
        ((DerivedCategory.singleFunctor (Modules S.toRingedSpace) 0).obj G) ≅
        (derivedPushforward (inverseImageBaseProjection f)).obj
          (DerivedCategory.Q.obj
            (((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj F).obj
              ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
                ((RingedSpaceModuleAdjunction.modulePullback
                  (inverseImageBaseProjection f)).obj G)))))) ∧
    (∀ K : DerivedCategory (Modules S.toRingedSpace),
      DerivedCategoryB.derivedCategoryB
        (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf) K →
      IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
        (inverseImageBaseProjection f) (DerivedCategory.Q.obj F) K)) :=
  ⟨isLocallyBounded_derivedPushforward_relativeComplex f F hF M hM hFM,
    derivedCategoryB_derivedPushforward_relativeComplex f F hF M hM hFM,
    locallyHasFiniteTorDimension_derivedPushforward_relativeComplex f F hF hflat M hM hFM,
    fun G hG => ⟨relativeComplexOrdinaryProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent f
      G hG F hF hflat M hM hFM⟩,
    fun K hK => isIso_projectionFormulaMap_relativeComplex_of_isLocallyBounded_of_isQuasicoherent f
      K hK F hF M hM hFM⟩

end Tag

end Stacks.RelativeComplexPushforward

end
