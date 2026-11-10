module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EssentialImage
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictCounit
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.RestrictPushforward
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentRefine
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedCohomology
public import StacksFrontier.AlgebraicGeometry.RestrictionSpellings
public import StacksFrontier.AlgebraicGeometry.RingedSpace.DerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived modules on a scheme supported on a subset

Let `X` be a scheme and `T ⊆ X` a subset. An object of the unbounded derived category of
`𝒪_X`-modules is *cohomologically supported on `T`* when every one of its cohomology sheaves
has vanishing stalks at the points outside `T`; this is the predicate
`AlgebraicGeometry.CohomologySupportedOn` of [Stacks, Tag 08DA]. This file proves that the
condition is monotone in `T`, detects the zero object, is pulled back by restriction to an open
subscheme and pushed forward, for closed `T`, by derived direct image along the inclusion of an
open subscheme, and it proves the induction on the support over a finite affine cover used in
[Stacks, Tag 09T6].

## Main results

* `Stacks.DerivedQCoh.cohomologySupportedOn_mono_standard`: the support condition grows with the
  subset.
* `Stacks.DerivedQCoh.isZero_of_cohomologySupportedOn_empty_standard`: an object supported on the
  empty set is zero.
* `Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestrict`: restriction to an open subscheme
  pulls the support back.
* `Stacks.DerivedQCoh.cohomologySupportedOn_of_iSup_eq_top`: the support condition is local on
  `X`.
* `Stacks.DerivedQCoh.isQuasicoherent_derivedRestrict`: restriction to an open subscheme
  preserves quasi-coherence of the cohomology sheaves.
* `Stacks.DerivedQCoh.cohomologySupportedOn_derivedPushforward`: derived direct image along the
  inclusion of an open subscheme preserves a closed support.
* `Stacks.DerivedQCoh.exists_derivedRestrict_triangle`: the triangle on the unit
  `E ⟶ Rj_*(E|_U)` has third vertex supported on `T \ U`.
* `Stacks.DerivedQCoh.property_of_finite_affine_support_standard`: the finite affine-cover
  induction on the support, over a quasi-compact scheme, at the standard model.

## Implementation notes

Everything here is stated at the standard model of the derived category,
`CategoryTheory.HasDerivedCategory.standard`, at which `AlgebraicGeometry.CohomologySupportedOn`
is stated. The instance is installed locally with a raised priority: the locally small models
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `SheafOfModules.hasDerivedCategory` are
global instances, and at equal priority instance search does not resolve
`HasDerivedCategory.{u + 1}`. The statements with a `_standard` suffix are the counterparts at
this model of the unsuffixed ones in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedDevissage.lean`.

Instance search does not cross between the spellings `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules X.ringCatSheaf` of the category of `𝒪_X`-modules, so the comparison
`Stacks.DerivedQCoh.restrictFunctorIsoJStar` of the two restriction functors is used at the term
level. `structureSheafRing` is made locally implicitly reducible so that the instances of the
sheaves of modules on an open subspace of a scheme are found in the ringed-space spelling of
[Stacks, Tag 08FE].

## References

* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction
open Stacks.Cohomology.ClosedSupportPerfect (pullbackOpenRestrictionIso
  derivedRestrictionAlongOpen_isRightDerived)
open Stacks.Cohomology.PushforwardRestriction (isZero_derived_of_homology_isZero
  isZero_sheafOfModules_of_stalk_isZero)
open Stacks.LocalCohomology (schemeRestrictFunctor_eq_moduleRestriction)

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing

namespace Stacks.DerivedQCoh

variable {X : Scheme.{u}}

/-- Enlarging the subset preserves the condition that all cohomology be supported on it. -/
theorem cohomologySupportedOn_mono_standard {S T : Set X} (hST : S ⊆ T)
    {E : DerivedCategory X.Modules} (hE : CohomologySupportedOn X.ringCatSheaf S E) :
    CohomologySupportedOn X.ringCatSheaf T E :=
  fun i x hx => hE i x fun h => hx (hST h)

/-- An object of the derived category all of whose cohomology is supported on the empty set is
zero: every cohomology sheaf then has all its stalks zero. -/
theorem isZero_of_cohomologySupportedOn_empty_standard (E : DerivedCategory X.Modules)
    (hE : CohomologySupportedOn X.ringCatSheaf (∅ : Set X) E) : IsZero E := by
  refine isZero_derived_of_homology_isZero E fun n => ?_
  exact isZero_sheafOfModules_of_stalk_isZero X.ringCatSheaf _ fun x => hE n x (by simp)

/-- Restriction of sheaves of modules along the inclusion of an open subscheme is the
restriction of modules to an open subspace of the underlying space. -/
private def restrictFunctorIsoJStar (U : X.Opens) :
    Scheme.Modules.restrictFunctor U.ι ≅ jStar U X.ringCatSheaf :=
  ((jStarAdjunction U X.ringCatSheaf).leftAdjointUniq
    (Scheme.Modules.restrictAdjunction U.ι)).symm

/-- **The stalks of a cohomology sheaf of a restriction.** At a point `y` of an open subscheme
`U ⊆ X`, the stalk of the `n`-th cohomology sheaf of the restriction of `E` to `U` is the stalk
at the image of `y` of the `n`-th cohomology sheaf of `E`. -/
private def stalkDerivedRestrictIso (U : X.Opens) (n : ℤ) (E : DerivedCategory X.Modules)
    (y : Usp U) :
    TopCat.Presheaf.stalk (X := Usp U)
        (((DerivedCategory.homologyFunctor U.toScheme.Modules n).obj
          ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E)).val.presheaf) y ≅
      TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor X.Modules n).obj E).val.presheaf) y.1 :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
      ((toAb (resRing U X.ringCatSheaf)).mapIso
        (((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryHomologyIso n).app E ≪≫
          (restrictFunctorIsoJStar U).app _)) ≪≫
    TopCat.Presheaf.stalkRestrictIso U
      (((DerivedCategory.homologyFunctor X.Modules n).obj E).val.presheaf) y

/-- **Restriction to an open subscheme pulls back the support.** If every cohomology sheaf of
`E` has vanishing stalks outside `T`, the same holds for the restriction of `E` to an open
subscheme `U` and the preimage of `T` in `U`. -/
theorem cohomologySupportedOn_derivedRestrict (U : X.Opens) (T : Set X)
    (E : DerivedCategory X.Modules) (hE : CohomologySupportedOn X.ringCatSheaf T E) :
    CohomologySupportedOn U.toScheme.ringCatSheaf (Subtype.val ⁻¹' T)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) :=
  fun n y hy => (hE n y.1 hy).of_iso (stalkDerivedRestrictIso U n E y)

/-- **Cohomological support is local on the base.** If a family of opens covers `X` and the
restriction of `E` to each member is supported on the preimage of `T`, then `E` is supported on
`T`. -/
theorem cohomologySupportedOn_of_iSup_eq_top {ι : Type*} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (T : Set X) (E : DerivedCategory X.Modules)
    (hE : ∀ i : ι, CohomologySupportedOn (U i).toScheme.ringCatSheaf (Subtype.val ⁻¹' T)
      ((Scheme.Modules.restrictFunctor (U i).ι).mapDerivedCategory.obj E)) :
    CohomologySupportedOn X.ringCatSheaf T E := by
  intro n x hx
  obtain ⟨i, hi⟩ : ∃ i : ι, x ∈ U i := by
    have htop : x ∈ (iSup U : X.Opens) := by rw [hU]; trivial
    simpa only [Opens.mem_iSup] using htop
  exact (hE i n ⟨x, hi⟩ hx).of_iso (stalkDerivedRestrictIso (U i) n E ⟨x, hi⟩).symm

/-- **Cohomological support is local for a covering by two opens.** -/
theorem cohomologySupportedOn_of_sup_eq_top (U V : X.Opens) (hUV : U ⊔ V = ⊤) (T : Set X)
    (E : DerivedCategory X.Modules)
    (hU : CohomologySupportedOn U.toScheme.ringCatSheaf (Subtype.val ⁻¹' T)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E))
    (hV : CohomologySupportedOn V.toScheme.ringCatSheaf (Subtype.val ⁻¹' T)
      ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj E)) :
    CohomologySupportedOn X.ringCatSheaf T E := by
  refine cohomologySupportedOn_of_iSup_eq_top (fun b : Bool => if b then U else V) ?_ T E ?_
  · rw [← hUV]
    refine le_antisymm (iSup_le fun b => ?_) (sup_le (le_iSup_of_le true le_rfl)
      (le_iSup_of_le false le_rfl))
    cases b with
    | false => exact le_sup_right
    | true => exact le_sup_left
  · intro b
    cases b with
    | false => exact hV
    | true => exact hU

/-- Cohomological support is invariant under isomorphism. -/
theorem cohomologySupportedOn_of_iso {Y : Scheme.{u}} (T : Set Y)
    {E E' : DerivedCategory Y.Modules} (e : E ≅ E')
    (hE : CohomologySupportedOn Y.ringCatSheaf T E) :
    CohomologySupportedOn Y.ringCatSheaf T E' := fun n x hx =>
  (hE n x hx).of_iso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
    ((toAb Y.ringCatSheaf).mapIso
      ((DerivedCategory.homologyFunctor Y.Modules n).mapIso e).symm))

/-- **Cohomological support is detected by a covering by two opens, for the derived pullback.**
If `U ⊔ V = ⊤` and the derived pullbacks of `E` to `U` and to `V` are supported on the preimages
of `T`, then `E` is supported on `T`. -/
theorem cohomologySupportedOn_of_derivedPullback_sup_eq_top (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (T : Set X) (E : DerivedCategory X.Modules)
    (hU : CohomologySupportedOn U.toScheme.ringCatSheaf (Subtype.val ⁻¹' T)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (X.toRingedSpace.ofRestrict U.isOpenEmbedding)).obj E))
    (hV : CohomologySupportedOn V.toScheme.ringCatSheaf (Subtype.val ⁻¹' T)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (X.toRingedSpace.ofRestrict V.isOpenEmbedding)).obj E)) :
    CohomologySupportedOn X.ringCatSheaf T E :=
  cohomologySupportedOn_of_sup_eq_top U V hUV T E
    (cohomologySupportedOn_of_iso _
      ((Stacks.RestrictionSpellings.derivedPullbackIsoRestrictFunctor X U).app E) hU)
    (cohomologySupportedOn_of_iso _
      ((Stacks.RestrictionSpellings.derivedPullbackIsoRestrictFunctor X V).app E) hV)

/-- **Restriction to an open subscheme preserves quasi-coherence of the cohomology.** -/
theorem isQuasicoherent_derivedRestrict (U : X.Opens) (E : DerivedCategory X.Modules)
    (hE : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) E) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) := by
  intro n
  let _ : ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent := hE n
  refine (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    ((((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryHomologyIso n).app E).symm) ?_
  exact inferInstanceAs ((Scheme.Modules.restrictFunctor U.ι).obj
    ((DerivedCategory.homologyFunctor X.Modules n).obj E)).IsQuasicoherent

/-- A sheaf of modules which is a zero object has all its stalks zero. -/
private theorem isZero_stalk_of_isZero_sheafOfModules {Y : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) {M : SheafOfModules.{u} O}
    (hM : IsZero M) (y : Y) :
    IsZero (TopCat.Presheaf.stalk (X := Y) M.val.presheaf y) :=
  (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero ((SheafOfModules.toSheaf O).obj M)).1
    (Functor.map_isZero (SheafOfModules.toSheaf O) hM) y

/-- The cohomology of a zero object of the derived category vanishes in every degree. -/
theorem isZero_homology_of_isZero {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {K : DerivedCategory C} (hK : IsZero K) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj K) :=
  Functor.map_isZero _ hK

/-- An object whose cohomology is supported on `T` restricts to zero on an open subscheme
disjoint from `T`. -/
private theorem isZero_derivedRestrict_of_supported (T : Set X) (V : X.Opens)
    (hV : (V : Set X) ⊆ Tᶜ) (E : DerivedCategory X.Modules)
    (hE : CohomologySupportedOn X.ringCatSheaf T E) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj E) := by
  refine isZero_derived_of_homology_isZero _ fun n => ?_
  exact isZero_sheafOfModules_of_stalk_isZero (resRing V X.ringCatSheaf) _
    fun y => cohomologySupportedOn_derivedRestrict V T E hE n y (hV y.2)

/-- **An object whose cohomology is supported on `T` restricts to zero on an open subscheme
disjoint from `T`.** -/
public alias isZero_derivedRestrict_of_cohomologySupportedOn_of_subset_compl :=
  isZero_derivedRestrict_of_supported

/-- **An object restricting to zero on an open subscheme is supported on its complement.** -/
public theorem cohomologySupportedOn_compl_opens_of_isZero_derivedRestrict (U : X.Opens)
    (G : DerivedCategory X.Modules)
    (hG : IsZero ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj G)) :
    CohomologySupportedOn X.ringCatSheaf ((U : Set X)ᶜ) G := by
  intro n x hx
  have hxU : x ∈ U := by simpa using hx
  refine IsZero.of_iso ?_ (stalkDerivedRestrictIso U n G ⟨x, hxU⟩).symm
  exact isZero_stalk_of_isZero_sheafOfModules (resRing U X.ringCatSheaf)
    (isZero_homology_of_isZero hG n) ⟨x, hxU⟩

/-- Alias of `Stacks.DerivedQCoh.cohomologySupportedOn_compl_opens_of_isZero_derivedRestrict`. -/
private alias cohomologySupportedOn_compl_of_isZero_derivedRestrict :=
  cohomologySupportedOn_compl_opens_of_isZero_derivedRestrict

/-- Restriction to an open subscheme is zero exactly when the derived pullback along the open
immersion of ringed spaces is. -/
private theorem isZero_derivedRestrict_iff_isZero_derivedPullback {Y : Scheme.{u}} (V : Y.Opens)
    (E : DerivedCategory Y.Modules) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj E) ↔
      IsZero ((modulePullback
        (Y.toRingedSpace.ofRestrict V.isOpenEmbedding)).mapDerivedCategory.obj E) := by
  have h (n : ℤ) : IsZero ((DerivedCategory.homologyFunctor _ n).obj
        ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj E)) ↔
      IsZero ((DerivedCategory.homologyFunctor _ n).obj
        ((modulePullback (Y.toRingedSpace.ofRestrict V.isOpenEmbedding)).mapDerivedCategory.obj
          E)) := by
    refine (((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategoryHomologyIso n).app
      E).isZero_iff.trans ?_
    rw [schemeRestrictFunctor_eq_moduleRestriction Y V]
    refine Iff.trans ?_ (((modulePullback
      (Y.toRingedSpace.ofRestrict V.isOpenEmbedding)).mapDerivedCategoryHomologyIso n).app
        E).isZero_iff.symm
    exact ((pullbackOpenRestrictionIso Y.toRingedSpace V).app _).isZero_iff.symm
  exact ⟨fun hz => isZero_derived_of_homology_isZero _ fun n =>
      (h n).1 (isZero_homology_of_isZero hz n),
    fun hz => isZero_derived_of_homology_isZero _ fun n =>
      (h n).2 (isZero_homology_of_isZero hz n)⟩

/-- Any total right derived functor of direct image along the inclusion of an open subscheme is
canonically isomorphic to `Stacks.Duality.derivedPushforward`. -/
private def derivedPushforwardIsoOfModel (U : X.Opens)
    (Rj : DerivedCategory U.toScheme.Modules ⥤ DerivedCategory X.Modules)
    (ηj : (Scheme.Modules.pushforward U.ι).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor ηj
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))] :
    Rj ≅ Stacks.Duality.derivedPushforward U.ι :=
  Functor.rightDerivedUnique Rj (Stacks.Duality.derivedPushforward U.ι) ηj
    ((Stacks.Duality.homotopyPushforward U.ι).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))

/-- **Derived direct image along the inclusion of an open subscheme preserves a closed
support.** Let `U ⊆ X` be an open subscheme, let `T ⊆ X` be closed and let `E` be an object of
the unbounded derived category of `𝒪_U`-modules whose cohomology is supported on the preimage
of `T`. Then the cohomology of `Rj_*E` is supported on `T`, for an arbitrary total right derived
functor `Rj_*` of direct image along the inclusion. -/
theorem cohomologySupportedOn_derivedPushforward (U : X.Opens) (T : Set X) (hT : IsClosed T)
    (Rj : DerivedCategory U.toScheme.Modules ⥤ DerivedCategory X.Modules)
    (ηj : (Scheme.Modules.pushforward U.ι).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor ηj
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))]
    (E : DerivedCategory U.toScheme.Modules)
    (hE : CohomologySupportedOn U.toScheme.ringCatSheaf (Subtype.val ⁻¹' T) E) :
    CohomologySupportedOn X.ringCatSheaf T (Rj.obj E) := by
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let W : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have hsquare : IsPullback W.ι (U.ι ∣_ V) U.ι V.ι :=
    (AlgebraicGeometry.isPullback_morphismRestrict U.ι V).flip
  have hRinged := AlgebraicGeometry.isPullback_toShHom W.ι (U.ι ∣_ V) U.ι V.ι hsquare
  let fR := U.ι.toLRSHom.toShHom
  let gR := (U.ι ∣_ V).toLRSHom.toShHom
  let iR := W.ι.toLRSHom.toShHom
  let jR := V.ι.toLRSHom.toShHom
  let Fi := modulePullback iR
  let Fj := modulePullback jR
  have : PreservesFiniteLimits Fi := inferInstanceAs (PreservesFiniteLimits
    (modulePullback (U.toScheme.toRingedSpace.ofRestrict W.isOpenEmbedding)))
  have : PreservesFiniteColimits Fi := inferInstanceAs (PreservesFiniteColimits
    (modulePullback (U.toScheme.toRingedSpace.ofRestrict W.isOpenEmbedding)))
  have : PreservesFiniteLimits Fj := inferInstanceAs (PreservesFiniteLimits
    (modulePullback (X.toRingedSpace.ofRestrict V.isOpenEmbedding)))
  have : PreservesFiniteColimits Fj := inferInstanceAs (PreservesFiniteColimits
    (modulePullback (X.toRingedSpace.ofRestrict V.isOpenEmbedding)))
  let Ri := Fi.mapDerivedCategory
  let Rv := Fj.mapDerivedCategory
  let αi := Fi.mapDerivedCategoryFactorsh.inv
  let αv := Fj.mapDerivedCategoryFactorsh.inv
  have hRi : Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    derivedRestrictionAlongOpen_isRightDerived U.toScheme.toRingedSpace W
  have hRv : Rv.IsRightDerivedFunctor αv (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    derivedRestrictionAlongOpen_isRightDerived X.toRingedSpace V
  let Df := Stacks.Duality.derivedPushforward U.ι
  let Dg := Stacks.Duality.derivedPushforward (U.ι ∣_ V)
  let αf := (Stacks.Duality.homotopyPushforward U.ι).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))
  let αg := (Stacks.Duality.homotopyPushforward (U.ι ∣_ V)).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso W.toScheme.Modules (ComplexShape.up ℤ))
  have hDf : Df.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ)) := inferInstance
  have hDg : Dg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso W.toScheme.Modules (ComplexShape.up ℤ)) := inferInstance
  have eBC : Df ⋙ Rv ≅ Ri ⋙ Dg :=
    @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _ fR iR jR gR _ _ hRinged
      _ _ _ _ Df Dg Ri Rv αf αg αi αv hDf hDg hRi hRv
  have hzeroRi : IsZero (Ri.obj E) :=
    (isZero_derivedRestrict_iff_isZero_derivedPullback W E).1
      (isZero_derivedRestrict_of_supported (X := U.toScheme) (Subtype.val ⁻¹' T) W
        (fun _ hy => hy) E hE)
  have : Dg.IsRightAdjoint :=
    (Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction (U.ι ∣_ V)).isRightAdjoint
  have : Dg.Additive := Functor.additive_of_preserves_binary_products _
  have hzeroRj : IsZero (Rv.obj (Rj.obj E)) := ((Functor.map_isZero Dg hzeroRi).of_iso
    (eBC.app E)).of_iso (Rv.mapIso ((derivedPushforwardIsoOfModel U Rj ηj).app E))
  have hzeroRes :
      IsZero ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj (Rj.obj E)) :=
    (isZero_derivedRestrict_iff_isZero_derivedPullback V _).2 hzeroRj
  exact fun n x hx =>
    cohomologySupportedOn_compl_of_isZero_derivedRestrict V (Rj.obj E) hzeroRes n x fun h => h hx

/-- **The cone of a morphism that becomes invertible on an open subscheme.** If two objects have
their cohomology supported on a closed subset `T` and a morphism between them restricts to an
isomorphism on an open subscheme `U`, the third vertex of a distinguished triangle on that
morphism has its cohomology supported on `T \ U`. -/
private theorem exists_cocone_supportedOn_diff (U : X.Opens) (T : Set X) (hT : IsClosed T)
    {E F : DerivedCategory X.Modules} (f : E ⟶ F)
    (hE : CohomologySupportedOn X.ringCatSheaf T E)
    (hF : CohomologySupportedOn X.ringCatSheaf T F)
    (hIso : IsIso ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map f)) :
    ∃ (G : DerivedCategory X.Modules) (g : F ⟶ G) (δ : G ⟶ E⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk f g δ ∈ distTriang _ ∧
        CohomologySupportedOn X.ringCatSheaf (T \ (U : Set X)) G := by
  classical
  obtain ⟨G, g, δ, hDist⟩ := Pretriangulated.distinguished_cocone_triangle f
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  have hGV : IsZero ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj G) :=
    Pretriangulated.Triangle.isZero₃_of_isZero₁₂
      ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.mapTriangle.obj
        (Pretriangulated.Triangle.mk f g δ))
      ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.map_distinguished _ hDist)
      (isZero_derivedRestrict_of_supported T V le_rfl E hE)
      (isZero_derivedRestrict_of_supported T V le_rfl F hF)
  have hGU : IsZero ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj G) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.mapTriangle.obj
        (Pretriangulated.Triangle.mk f g δ))
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map_distinguished _ hDist) hIso
  refine ⟨G, g, δ, hDist, fun n x hx => ?_⟩
  by_cases hxT : x ∈ T
  · exact cohomologySupportedOn_compl_of_isZero_derivedRestrict U G hGU n x fun h => hx ⟨hxT, h⟩
  · exact cohomologySupportedOn_compl_of_isZero_derivedRestrict V G hGV n x
      fun h => h hxT

/-- **Derived restriction is left adjoint to any total right derived functor of direct image
along the inclusion of an open subscheme.** -/
private def derivedRestrictAdjunctionOfModel (U : X.Opens)
    (Rj : DerivedCategory U.toScheme.Modules ⥤ DerivedCategory X.Modules)
    (ηj : (Scheme.Modules.pushforward U.ι).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor ηj
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))] :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ⊣ Rj :=
  (Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction U.ι).ofNatIsoRight
    (derivedPushforwardIsoOfModel U Rj ηj).symm

/-- Any total right derived functor of direct image along the inclusion of an open subscheme is
fully faithful: the counit of the derived adjunction is invertible. -/
private theorem nonempty_fullyFaithful_of_model (U : X.Opens)
    (Rj : DerivedCategory U.toScheme.Modules ⥤ DerivedCategory X.Modules)
    (ηj : (Scheme.Modules.pushforward U.ι).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor ηj
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))] :
    Nonempty Rj.FullyFaithful :=
  ⟨((Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction
      U.ι).fullyFaithfulROfIsIsoCounit).ofIso (derivedPushforwardIsoOfModel U Rj ηj).symm⟩

/-- **The restriction triangle removes an open subscheme from a closed support.** For an open
subscheme `U ⊆ X`, a closed `T ⊆ X` and an object `E` of the unbounded derived category of
`𝒪_X`-modules with cohomology supported on `T`, the unit `E ⟶ Rj_*(E|_U)` of the derived
adjunction fits into a distinguished triangle whose third vertex has its cohomology supported on
`T \ U`. -/
theorem exists_derivedRestrict_triangle (U : X.Opens) (T : Set X) (hT : IsClosed T)
    (Rj : DerivedCategory U.toScheme.Modules ⥤ DerivedCategory X.Modules)
    (ηj : (Scheme.Modules.pushforward U.ι).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor ηj
      (HomotopyCategory.quasiIso U.toScheme.Modules (ComplexShape.up ℤ))]
    (E : DerivedCategory X.Modules) (hE : CohomologySupportedOn X.ringCatSheaf T E)
    (hPush : CohomologySupportedOn X.ringCatSheaf T
      (Rj.obj ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E))) :
    ∃ S : Pretriangulated.Triangle (DerivedCategory X.Modules),
      S.obj₁ = E ∧
        S.obj₂ = Rj.obj ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) ∧
        S ∈ distTriang _ ∧
        CohomologySupportedOn X.ringCatSheaf (T \ (U : Set X)) S.obj₃ := by
  obtain ⟨ff⟩ := nonempty_fullyFaithful_of_model U Rj ηj
  let _ := ff.full
  let _ := ff.faithful
  let a := derivedRestrictAdjunctionOfModel U Rj ηj
  obtain ⟨G, g, δ, hS, hG⟩ :=
    exists_cocone_supportedOn_diff U T hT (a.unit.app E) hE hPush inferInstance
  exact ⟨Pretriangulated.Triangle.mk (a.unit.app E) g δ, rfl, rfl, hS, hG⟩

/-- **Finite affine-cover induction on the support.** Let `P` and `Q` be properties of objects
of the unbounded derived category of `𝒪_X`-modules on a quasi-compact scheme `X`. Suppose `P`
holds for zero objects and is stable under passing from the last two vertices of a
distinguished triangle to the first, and suppose that for every affine open `U` and every
closed `S` an object satisfying `Q` with cohomology supported on `S` fits into a distinguished
triangle whose second vertex satisfies `P` and whose third vertex satisfies `Q` with cohomology
supported on `S \ U`. Then `P` holds for every object satisfying `Q`. This is the statement at
the standard model of `D(𝒪_X)`. -/
theorem property_of_finite_affine_support_standard (X : Scheme.{u}) [CompactSpace X]
    (P Q : ObjectProperty (DerivedCategory X.Modules))
    (hzero : ∀ E, IsZero E → P E)
    (htri : ∀ T : Pretriangulated.Triangle (DerivedCategory X.Modules),
      T ∈ distTriang _ → P T.obj₂ → P T.obj₃ → P T.obj₁)
    (hstep : ∀ (U : X.Opens), IsAffineOpen U → ∀ (S : Set X), IsClosed S → ∀ E, Q E →
      CohomologySupportedOn X.ringCatSheaf S E →
      ∃ T : Pretriangulated.Triangle (DerivedCategory X.Modules),
        T.obj₁ = E ∧ T ∈ distTriang _ ∧ P T.obj₂ ∧ Q T.obj₃ ∧
        CohomologySupportedOn X.ringCatSheaf (S \ (U : Set X)) T.obj₃) :
    ∀ E, Q E → P E := by
  classical
  have hs : ∀ (s : Finset X.Opens), (∀ U ∈ s, IsAffineOpen U) →
      ∀ (S : Set X), IsClosed S → S ⊆ ⋃ U ∈ s, (U : Set X) →
        ∀ E, Q E → CohomologySupportedOn X.ringCatSheaf S E → P E := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _ S _ hSE E _ hE
        have hS0 : S ⊆ ∅ := by simpa using hSE
        exact hzero E (isZero_of_cohomologySupportedOn_empty_standard E
          (cohomologySupportedOn_mono_standard hS0 hE))
    | @insert U s hUs ih =>
        intro ha S hS hSE E hQE hE
        obtain ⟨T, hTE, hT, hP, hQ, hSupp⟩ := hstep U (ha U (by simp)) S hS E hQE hE
        have hrem : S \ (U : Set X) ⊆ ⋃ V ∈ s, (V : Set X) := by
          intro x hx
          obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp (hSE hx.1)
          rcases Finset.mem_insert.mp hV with rfl | hV
          · exact (hx.2 hxV).elim
          · exact Set.mem_iUnion₂.mpr ⟨V, hV, hxV⟩
        exact hTE ▸ htri T hT hP
          (ih (fun V hV => ha V (Finset.mem_insert_of_mem hV)) (S \ (U : Set X))
            (hS.inter U.isOpen.isClosed_compl) hrem T.obj₃ hQ hSupp)
  obtain ⟨ι, hι, V, hV, hcover⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_finite_affineOpen_cover X
  let _ : Fintype ι := Fintype.ofFinite ι
  intro E hE
  refine hs (Finset.univ.image V) ?_ Set.univ isClosed_univ ?_ E hE ?_
  · intro W hW
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hW
    exact hV a
  · intro x _
    obtain ⟨a, ha⟩ := hcover x
    exact Set.mem_iUnion₂.mpr ⟨V a, Finset.mem_image.mpr ⟨a, by simp, rfl⟩, ha⟩
  · intro n x hx
    exact (hx (Set.mem_univ x)).elim

end Stacks.DerivedQCoh

end
