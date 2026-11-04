module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocusValuationRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocus0BDP
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ValuativeClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocusRank
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Differentials
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.GeometricFibres
public import StacksCore.Tactic.StacksAttribute

/-!
# The descent locus of an invertible module with geometrically integral fibres is closed

Let `f : X ⟶ S` be flat, proper and of finite presentation with `𝒪_T ≅ f_{T,*}𝒪_{X_T}` after
every base change `T ⟶ S`, let `E` be an invertible `𝒪_X`-module, and suppose the geometric
fibres of `f` are integral: `X ×_S Spec k` is integral for every geometric point `Spec k ⟶ S`
(`k` algebraically closed). Then a descent locus `Z ⟶ S` of `E` (Tag 0BDP,
`AlgebraicGeometry.IsDescentLocus`) is a closed immersion. This is [Stacks, Tag 0BF0].

## The proof

The source's. The structure morphism of a descent locus is an immersion of finite presentation, so
by the valuative test (`AlgebraicGeometry.IsDescentLocus.isClosedImmersion_hom_of_valuationRing`,
[Stacks, Tag 02JQ]) it suffices that `E` descends along `h : Spec A ⟶ S` for a valuation ring `A`
as soon as it descends along `Spec K ⟶ Spec A ⟶ S`, `K` the fraction field. Over `Spec A` the base
change `X_A` satisfies the hypotheses of [Stacks, Tag 0EX8]
(`AlgebraicGeometry.ValuativeTriviality.isTrivial_of_isTrivial_genericFiber`): its closed fibre is
integral, `K = Γ(X_K, 𝒪)` by the hypothesis on `f`, and `E` is trivial on `X_K` because it is the
pullback of a finite locally free module on `Spec K`, which is free
(`nonempty_iso_unit_of_descendsFromBase`): an invertible module isomorphic to a free module has
rank one (`nonempty_iso_unit_of_iso_free`). So `E` is trivial on `X_A`, and descends along `h`.

## Main results

* `AlgebraicGeometry.IsDescentLocus.isClosedImmersion_hom_of_valuationRing`: a descent locus is a
  closed immersion when the descent condition lifts from the generic point of every valuation
  ring to the whole valuation ring.
* `AlgebraicGeometry.IsDescentLocus.isClosedImmersion_hom_of_geometricallyIntegral`:
  **[Stacks, Tag 0BF0]**, for every descent locus.

## Implementation notes

"`Z` is closed in `S`" is read as: the structure morphism of `Z` is a closed immersion. The
statement is made for an arbitrary descent locus `Z`, which is unique up to unique isomorphism
(`AlgebraicGeometry.IsDescentLocus.isoOfIsDescentLocus`), so it applies to the locus of
[Stacks, Tag 0BDP] whenever that exists. The hypothesis "`𝒪_T ⟶ p_*𝒪_{X_T}` is an isomorphism for
every `T ⟶ S`" is spelled as in `Stacks.AlgebraicGeometry.ProperFlatFamilyUnit`. "The geometric
fibres of `f` are integral" is the hypothesis `hgeom`: `X ×_S Spec k` is integral for every
geometric point `Spec k ⟶ S` of `S` ([Stacks, Tag 03PO]: `k` algebraically closed). The proof
uses the a priori stronger Mathlib condition `AlgebraicGeometry.GeometricallyIntegral f`
(integrality over every field `K`), which is equivalent to it by
`AlgebraicGeometry.geometricallyIntegral_iff_forall_isAlgClosed`.

## References

* [Stacks Project, Tag 0BF0](https://stacks.math.columbia.edu/tag/0BF0)
* [Stacks Project, Tag 0EX8](https://stacks.math.columbia.edu/tag/0EX8)
* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
* [Stacks Project, Tag 02JQ](https://stacks.math.columbia.edu/tag/02JQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open AlgebraicGeometry.ProperFlatBaseChange

universe u

namespace AlgebraicGeometry

namespace IsDescentLocus

variable {X S : Scheme.{u}} {f : X ⟶ S}
  {E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
  {Z : Over S}

/-- **A descent locus is closed when descent lifts along valuation rings.** Suppose that for
every valuation ring `A` with fraction field `K` and every morphism `h : Spec A ⟶ S`, the module
descends along `h` as soon as it descends along the composite `Spec K ⟶ Spec A ⟶ S`. Then the
structure morphism of a descent locus is a closed immersion.

The structure morphism is an immersion of finite presentation, hence a quasi-compact
preimmersion, and the hypothesis together with the universal property of the locus is exactly the
valuative test `AlgebraicGeometry.isClosedImmersion_of_valuationRing`. This is the first step of
the proof of [Stacks, Tag 0BF0](https://stacks.math.columbia.edu/tag/0BF0): there the hypothesis
is supplied, for an invertible module and a morphism with geometrically integral fibres, by
[Stacks, Tag 0EX8](https://stacks.math.columbia.edu/tag/0EX8), proved as
`AlgebraicGeometry.ValuativeTriviality.isTrivial_of_isTrivial_genericFiber`. -/
theorem isClosedImmersion_hom_of_valuationRing (hZ : IsDescentLocus f E Z)
    (H : ∀ (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
      (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] (h : Spec (.of A) ⟶ S),
      DescendsFromBase f E (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ h) →
        DescendsFromBase f E h) :
    IsClosedImmersion Z.hom := by
  have := hZ.isImmersion
  have : QuasiCompact Z.hom := hZ.finitePresentation.2.1
  refine isClosedImmersion_of_valuationRing Z.hom fun A _ _ _ K _ _ _ g h hgh => ?_
  obtain ⟨k, hk⟩ := (hZ.factorsThrough_iff h).2
    (H A K h ((hZ.factorsThrough_iff _).1 ⟨g, hgh⟩))
  exact ⟨k (IsLocalRing.closedPoint A), by rw [← hk]; exact (Scheme.Hom.comp_apply k Z.hom _).symm⟩

end IsDescentLocus

/-- **An invertible module isomorphic to a free module is trivial**, on a nonempty scheme. -/
theorem nonempty_iso_unit_of_iso_free {Y : Scheme.{u}} [Nonempty Y] (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] {I : Type u}
    (e : M ≅ SheafOfModules.free (R := Y.ringCatSheaf) I) :
    Nonempty (M ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  let K : Type u := Y.residueField y
  let ι : Spec (.of K) ⟶ Y := Y.fromSpecResidueField y
  have : Stacks.SheafOfModules.IsInvertible (Spec (.of K)).presheaf
      (structureSheafRing (Spec (.of K)).toRingedSpace).property
      ((modulePullback ι.toLRSHom.toShHom).obj M) :=
    modulePullback_isInvertible_scheme ι M
  obtain ⟨t⟩ := Stacks.PicardUFD.isTrivial_of_isInvertible_spec K
    ((modulePullback ι.toLRSHom.toShHom).obj M)
  let e' : SheafOfModules.unit (Spec (.of K)).ringCatSheaf ≅
      SheafOfModules.free (R := (Spec (.of K)).ringCatSheaf) I :=
    t.symm ≪≫ (modulePullback ι.toLRSHom.toShHom).mapIso e ≪≫
      modulePullbackObjFreeIso ι.toLRSHom.toShHom I
  let R : CommRingCat.{u} := CommRingCat.of K
  let φ : ModuleCat.of R R ≅ ModuleCat.of R (I →₀ R) :=
    tilde.toTildeΓNatIso.app (ModuleCat.of R R) ≪≫
      moduleSpecΓFunctor.mapIso (tildeSelf ≪≫ e' ≪≫ (tildeFinsupp I).symm) ≪≫
      (tilde.toTildeΓNatIso.app _).symm
  have hrk := φ.toLinearEquiv.rank_eq
  rw [Module.rank_self, rank_finsupp_self, Cardinal.lift_id] at hrk
  obtain ⟨_, hne⟩ := Cardinal.eq_one_iff_unique.1 hrk.symm
  have : Unique I := uniqueOfSubsingleton (Classical.choice hne)
  exact ⟨e ≪≫ coproductUniqueIso _⟩

/-- **A module descending along a point of the base is trivial there**, when it is invertible
and the fibre is nonempty: the descended module on the spectrum of a field is free, and an
invertible module isomorphic to a free one is trivial. -/
theorem nonempty_iso_unit_of_descendsFromBase {X S : Scheme.{u}} (f : X ⟶ S) (E : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E] (K : Type u) [Field K]
    (k : Spec (.of K) ⟶ S) [Nonempty ↥(pullback f k)] (h : DescendsFromBase f E k) :
    Nonempty ((modulePullback (pullback.fst f k).toLRSHom.toShHom).obj E ≅
      SheafOfModules.unit (pullback f k).ringCatSheaf) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  let N' : (Spec (.of K)).Modules := N
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} N' := hN
  have : N'.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree N'
  obtain ⟨I, ⟨eN⟩⟩ := GroupSchemeDifferentials.exists_free_iso_of_isQuasicoherent_spec_field K N'
  have := modulePullback_isInvertible_scheme (pullback.fst f k) E
  exact nonempty_iso_unit_of_iso_free _ (e.symm ≪≫
    (modulePullback (pullback.snd f k).toLRSHom.toShHom).mapIso eN ≪≫
      modulePullbackObjFreeIso (pullback.snd f k).toLRSHom.toShHom I)

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 0BF0].** Let `f : X ⟶ S` be flat, proper and of finite
presentation, with `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` an isomorphism for every base change `T ⟶ S`, let `E`
be an invertible `𝒪_X`-module, and let the geometric fibres of `f` be integral (`hgeom`:
`X ×_S Spec k` is integral for every algebraically closed field `k` and `Spec k ⟶ S`). Then every
descent locus `Z` of `E` over `f` (Tag 0BDP) is closed in `S`: its structure morphism is a closed
immersion. -/
@[stacks 0BF0]
theorem IsDescentLocus.isClosedImmersion_hom_of_geometricallyIntegral
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f a).toLRSHom.toShHom))
    (E : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E]
    (hgeom : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
      IsIntegral (pullback f s))
    {Z : Over S} (hZ : IsDescentLocus f E Z) :
    IsClosedImmersion Z.hom := by
  have : GeometricallyIntegral f := (geometricallyIntegral_iff_forall_isAlgClosed f).2 hgeom
  refine hZ.isClosedImmersion_hom_of_valuationRing fun A _ _ _ K _ _ _ h hK => ?_
  set g : Spec (.of K) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let EA : (pullback f h).Modules := (modulePullback (pullback.fst f h).toLRSHom.toShHom).obj E
  have : SheafOfModules.IsInvertible (pullback f h).presheaf (pullback f h).ringCatSheaf.2 EA :=
    modulePullback_isInvertible_scheme (pullback.fst f h) E
  let φ := pullbackLeftPullbackSndIso f h g
  -- the generic fibre
  have : IsIntegral (pullback f (g ≫ h)) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  obtain ⟨t⟩ := nonempty_iso_unit_of_descendsFromBase f E K (g ≫ h) hK
  have hgen : SheafOfModules.IsTrivial (pullback (pullback.snd f h) g).presheaf
      (pullback (pullback.snd f h) g).ringCatSheaf.2
      ((modulePullback (pullback.fst (pullback.snd f h) g).toLRSHom.toShHom).obj EA) := by
    have hfst : pullback.fst (pullback.snd f h) g ≫ pullback.fst f h =
        φ.hom ≫ pullback.fst f (g ≫ h) := (pullbackLeftPullbackSndIso_hom_fst f h g).symm
    refine ⟨((modulePullbackComp (pullback.fst (pullback.snd f h) g).toLRSHom.toShHom
      (pullback.fst f h).toLRSHom.toShHom).app E).symm ≪≫ eqToIso ?_ ≪≫
      (modulePullbackComp φ.hom.toLRSHom.toShHom
        (pullback.fst f (g ≫ h)).toLRSHom.toShHom).app E ≪≫
      (modulePullback φ.hom.toLRSHom.toShHom).mapIso t ≪≫
      modulePullbackObjUnitIso φ.hom.toLRSHom.toShHom⟩
    have hsh := congrArg (fun k => k.toLRSHom.toShHom) hfst
    simp only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] at hsh
    rw [hsh]
  have hΓ : Function.Bijective (pullback.snd (pullback.snd f h) g).appTop.hom := by
    have e1 : pullback.snd (pullback.snd f h) g = φ.hom ≫ pullback.snd f (g ≫ h) :=
      (pullbackLeftPullbackSndIso_hom_snd f h g).symm
    rw [e1, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    have : IsIso φ.hom.appTop := inferInstanceAs (IsIso (φ.hom.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso φ.hom.appTop).comp
      (bijective_appTop_of_isIso_structureSheafHom _ (hO (g ≫ h)))
  have : IsIntegral ((pullback.snd f h).fiber (IsLocalRing.closedPoint A)) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  obtain ⟨tA⟩ := ValuativeTriviality.isTrivial_of_isTrivial_genericFiber (pullback.snd f h)
    K EA hgen hΓ
  exact descendsFromBase_of_nonempty_iso_unit f E h ⟨tA⟩

end

end AlgebraicGeometry

end
