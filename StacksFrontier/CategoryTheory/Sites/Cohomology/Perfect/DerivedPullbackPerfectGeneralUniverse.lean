module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.PullbackAlongAMorphismOfRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismsOfSites
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TruncatingApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension

/-!
# Perfectness is preserved by derived pullback, in every universe

Let `f : (C, O) ⟶ (D, O')` be a morphism of ringed sites and let `E` be a perfect object of
`D(O')`. Then `Lf^* E` is perfect. This is Stacks 08H6, proved here for ringed sites whose
categories, morphisms and sections all live in one universe `u`; the registered statement
`AlgebraicGeometry.RingedSite.Hom.isPerfect_derivedPullback` (module
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedPullbackAlongRingedTopoi`) is its
case
`u = 0`. The universe-`u` form is the one the models of the ringed spaces-étale sites of algebraic
spaces need.

## The argument

Perfectness is a local condition of a very concrete kind: by Stacks 08G6 (1), in the form
`AlgebraicGeometry.RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect`, an object of
`D(O)` is perfect as soon as every object of `C` admits a covering over each member `V` of which
there are a strictly perfect complex `P` of `O|_V`-modules and an isomorphism `P ≅ (Lf^* E)|_V`
*in the derived category*. So the whole proof is the production of such local models, and the
property "`V` carries a strictly perfect derived model of the restriction of a fixed complex" is
what travels; it is `HasStrictlyPerfectModel` below.

* Perfectness of `E` provides, above each object `W` of `D`, a covering whose members carry
  strictly perfect models of `E` — the chain-level quasi-isomorphisms of Stacks 08G5 become
  isomorphisms in the derived category of the slice.
* Stacks 08H2 says the objects `u(W)`, for `W` an object of `D`, cover the final object of
  `Sh(C)`, and `CategoryTheory.GrothendieckTopology.coversTop_obj_subtype` refines that to the
  objects `u(W)` with `W` carrying such a model.
* Over `u(W)` the degreewise pullback of the model along the localized morphism `f'` of Stacks
  04J0 is a strictly perfect model of `(Lf^* E)|_{u(W)}`: a strictly perfect complex is bounded
  above with flat terms, so `L(f')^*` is computed degreewise on it
  (`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedPullbackObjIsoOfFlat`), the degreewise
  pullback is strictly perfect by Stacks 08H3, and the target is identified with
  `(Lf^* E)|_{u(W)}` by the derived localization square
  (`AlgebraicGeometry.RingedSite.Hom.nonempty_derivedPullbackLocalizedIso`).
* Carrying a strictly perfect derived model along an arrow `V ⟶ u(W)` of `C` costs nothing:
  restriction to a smaller slice is exact, so it preserves strict perfectness and carries the
  isomorphism to an isomorphism. This is what makes the covering produced in the second step
  usable, its arrows having arbitrary sources with a map to some `u(W)`.

The criterion of Stacks 08G8 is deliberately *not* used: it would make the statement carry the
derived tensor product data that locally finite Tor dimension is measured against, and the
assertion of Stacks 08H6 asks for none.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.isPerfect_derivedPullback_general`: **Stacks 08H6**, in
  universe `u`.

## References

* [Stacks Project, Tag 08H6](https://stacks.math.columbia.edu/tag/08H6)
* [Stacks Project, Tag 08H2](https://stacks.math.columbia.edu/tag/08H2)
* [Stacks Project, Tag 08H3](https://stacks.math.columbia.edu/tag/08H3)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
open Stacks.Sheaves.DerivedPullback.KFlatPullback

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard


/-- Strict perfectness transported along a degreewise isomorphism of complexes, in any universe:
the two conditions are a finiteness condition on the terms and a retract condition on each term,
and an isomorphism preserves both. -/
private theorem isStrictlyPerfect_of_isoX_general {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {P Q : CochainComplex (SheafOfModules.{u} R) ℤ} (e : ∀ i : ℤ, P.X i ≅ Q.X i)
    (hP : IsStrictlyPerfect R P) : IsStrictlyPerfect R Q where
  bounded := hP.bounded.subset fun i hi hz => hi ((e i).symm.isZero_iff.mpr hz)
  termDirectSummand i :=
    IsDirectSummandOfFiniteFree.of_retract_general R ⟨(e i).inv, (e i).hom, (e i).inv_hom_id⟩
      (hP.termDirectSummand i)

/-! ### Carrying a strictly perfect model over an object of the site -/

section Model

variable (Z : RingedSite.{u, u, u})
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{u}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective

/-- Restriction along an arrow of the site preserves finite limits. -/
private instance overMapLimitsGeneral {U V : Z.C} (g : V ⟶ U) :
    PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction along an arrow of the site preserves finite colimits. -/
private instance overMapColimitsGeneral {U V : Z.C} (g : V ⟶ U) :
    PreservesFiniteColimits
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

/-- The property of an object `V` of a ringed site used throughout the proof of Stacks 08H6: the
restriction of the complex `K` to the slice over `V` is isomorphic, *in the derived category of
that slice*, to a strictly perfect complex of `O|_V`-modules.

This is the hypothesis of Stacks 08G6 (1) read at one object, in the form
`AlgebraicGeometry.RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect` consumes it,
and phrased against a chosen complex representative rather than against an object of `D(O)`
because that is the form which both pulls back along `f` and descends along an arrow of the
site. -/
private def HasStrictlyPerfectModel
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (V : Z.C) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (Z.restrictComplex K V))

/-- An isomorphism `K ≅ E` in the derived category restricts to the slice over `V`: the derived
image of the complex `K|_V` is `E|_V`. -/
private def restrictComplexIsoRestrict
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ}
    {E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))}
    (e : DerivedCategory.Q.obj K ≅ E) (V : Z.C) :
    DerivedCategory.Q.obj (Z.restrictComplex K V) ≅
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
        V).mapDerivedCategory.obj E :=
  ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      V).mapDerivedCategoryFactors.app K).symm ≪≫
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
      V).mapDerivedCategory.mapIso e

end Model

section Main

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasFiniteLimits X.C] [HasFiniteLimits Y.C] [PreservesFiniteLimits f.u]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, HasSheafify (Y.J.over U) AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]



attribute [local instance] ovSheafCompose


attribute [local instance] preservesFiniteLimitsOverMap' preservesFiniteColimitsOverMap'

attribute [local instance] derivedPullbackHasLeftDerived
  derivedPullbackLocalizedHasLeftDerived derivedPullbackLocalizedCommShift

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasFiniteLimits Y.C]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **A perfect complex carries strictly perfect derived models on a covering of every object.**
This is the definition of a perfect complex, Stacks 08G5, with the chain-level
quasi-isomorphisms turned into isomorphisms of the derived categories of the slices. -/
private theorem exists_coveringFamily_hasStrictlyPerfectModel
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Y.IsPerfectComplex K)
    (W : Y.C) :
    ∃ S : Presieve W, Sieve.generate S ∈ Y.J W ∧
      ∀ ⦃V : Y.C⦄ (g : V ⟶ W), S g → HasStrictlyPerfectModel Y K V := by
  obtain ⟨S, hS, hmodels⟩ := hK W
  refine ⟨S, hS, fun {V} g hg => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hmodels g hg
  let : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (C := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V)) q).2 hq
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map q)⟩⟩

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasFiniteLimits X.C]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **A strictly perfect derived model descends along an arrow of the site.** Restriction to a
smaller slice is exact, so it preserves strict perfectness and carries an isomorphism of the
derived categories to an isomorphism, and it carries a complex representative of a restriction
to a complex representative of the smaller restriction. -/
private theorem hasStrictlyPerfectModel_of_hom
    (K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {V V' : X.C} (a : V' ⟶ V)
    (h : HasStrictlyPerfectModel X K' V) : HasStrictlyPerfectModel X K' V' := by
  obtain ⟨P, hP, ⟨β⟩⟩ := h
  have hcmp : ((SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      a).mapHomologicalComplex (ComplexShape.up ℤ)).obj (X.restrictComplex K' V) ≅
      X.restrictComplex K' V' :=
    (Stacks.SheafOfModules.overFunctorMapComplexIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        a).app K'
  refine ⟨((SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      a).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a hP, ⟨?_⟩⟩
  exact ((SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      a).mapDerivedCategoryFactors.app P).symm ≪≫
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        a).mapDerivedCategory.mapIso β ≪≫
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        a).mapDerivedCategoryFactors.app (X.restrictComplex K' V) ≪≫
      DerivedCategory.Q.mapIso hcmp

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The pullback of a strictly perfect model is a strictly perfect model over the image
object.** If `K` carries a strictly perfect derived model over `W`, then a complex
representative `K'` of `Lf^* E` carries one over `u(W)`.

The model over `W` is pushed through the derived pullback along the localized morphism `f'` of
Stacks 04J0. A strictly perfect complex is bounded above with flat terms, so that functor is
computed on it by the degreewise pullback
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedPullbackObjIsoOfFlat`), and the
degreewise pullback is strictly perfect by Stacks 08H3. Its value on the target is
`(Lf^* E)|_{u(W)}` by the derived localization square. -/
private theorem hasStrictlyPerfectModel_image
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Y).O)))
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e' : DerivedCategory.Q.obj K' ≅ (derivedPullback f.toRingedToposSiteHom).obj E)
    (W : Y.C) (hW : HasStrictlyPerfectModel Y K W) :
    HasStrictlyPerfectModel X K' (f.u.obj W) := by
  obtain ⟨P₀, hP₀, ⟨α⟩⟩ := hW
  have hmos' := (f.localized W).isMorphismOfSites
  obtain ⟨n, hn⟩ := hP₀.bounded.bddAbove
  have hLE : P₀.IsStrictlyLE n := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    by_contra hz
    exact (not_le_of_gt hi) (hn hz)
  have hP₀' : IsStrictlyPerfect
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over W).O) P₀ := hP₀
  have hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (Y.over W).O) (P₀.X i) :=
    fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect hP₀' i
  have eFlat := derivedPullbackObjIsoOfFlat (f.localized W).toRingedToposSiteHom hmos' P₀ n hLE
    hflat
  have hSP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj W))
      ((pullbackComplex (f.localized W).toRingedToposSiteHom).obj P₀) :=
    isStrictlyPerfect_of_isoX_general
      (fun i => (f.localized W).pullbackToposIso.app (P₀.X i))
      (AlgebraicGeometry.RingedToposHom.isStrictlyPerfect_pullbackModules
        (f.localized W).ringedToposHom hP₀)
  have eTot : (derivedPullback (f.localized W).toRingedToposSiteHom).obj
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          W).mapDerivedCategory.obj E) ≅
      DerivedCategory.Q.obj (X.restrictComplex K' (f.u.obj W)) :=
    (f.nonempty_derivedPullbackLocalizedIso W E).some ≪≫
      (restrictComplexIsoRestrict X e' (f.u.obj W)).symm
  exact ⟨(pullbackComplex (f.localized W).toRingedToposSiteHom).obj P₀, hSP,
    ⟨eFlat.symm ≪≫
      (derivedPullback (f.localized W).toRingedToposSiteHom).mapIso
        (α ≪≫ restrictComplexIsoRestrict Y e W) ≪≫ eTot⟩⟩

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Stacks 08H6, in every universe.** The derived pullback along a morphism of ringed sites of a
perfect object of `D(O')` is perfect.

Stacks 08H2 makes the objects `u(W)` cover the final object of `Sh(C)`, and
`CategoryTheory.GrothendieckTopology.coversTop_obj_subtype` refines that covering to the `u(W)`
over which `K` carries a strictly perfect derived model. Over such an object the pullback of the
model is a strictly perfect derived model of `(Lf^* E)|_{u(W)}`
(`hasStrictlyPerfectModel_image`), and it descends along any arrow into `u(W)` by exactness of
restriction (`hasStrictlyPerfectModel_of_hom`), which is what the arrows of that covering
supply; Stacks 08G6 (1) assembles. -/
theorem Hom.isPerfect_derivedPullback_general
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Y).O)))
    (hE : Y.IsPerfect E) :
    X.IsPerfect ((derivedPullback f.toRingedToposSiteHom).obj E) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  obtain ⟨K', e'⟩ :
      Σ' K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
        DerivedCategory.Q.obj K' ≅ (derivedPullback f.toRingedToposSiteHom).obj E :=
    ⟨DerivedCategory.Q.objPreimage _, DerivedCategory.Q.objObjPreimageIso _⟩
  have := f.isMorphismOfSites.isContinuous
  have : PreservesFiniteLimits (f.u.sheafPullback (Type u) Y.J X.J) :=
    f.isMorphismOfSites.preservesFiniteLimits
  have : PreservesLimit (Functor.empty.{u} (Sheaf Y.J (Type u)))
      (f.u.sheafPullback (Type u) Y.J X.J) := inferInstance
  have hTop : X.J.CoversTop f.u.obj :=
    CategoryTheory.GrothendieckTopology.coversTop_obj_of_preservesTerminal_sheafPullback
      f.u Y.J X.J
  have hcover : X.J.CoversTop
      (fun W : {W : Y.C // HasStrictlyPerfectModel Y K W} => f.u.obj W.val) :=
    CategoryTheory.GrothendieckTopology.coversTop_obj_subtype f.u Y.J X.J hTop _
      (exists_coveringFamily_hasStrictlyPerfectModel K hK)
  refine isPerfect_of_forall_coveringFamily_strictlyPerfect X _ (fun U => ?_)
  refine ⟨(Sieve.ofObjects (fun W : {W : Y.C // HasStrictlyPerfectModel Y K W} =>
    f.u.obj W.val) U).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact hcover U
  rintro V g ⟨⟨W, hW⟩, ⟨k⟩⟩
  obtain ⟨P, hP, ⟨γ⟩⟩ := hasStrictlyPerfectModel_of_hom K' k
    (hasStrictlyPerfectModel_image f E K e K' e' W hW)
  exact ⟨P, hP, ⟨γ ≪≫ restrictComplexIsoRestrict X e' V⟩⟩

end Main

end AlgebraicGeometry.RingedSite

end
