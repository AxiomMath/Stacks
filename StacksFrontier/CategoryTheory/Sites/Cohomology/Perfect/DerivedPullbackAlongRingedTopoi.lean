module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.PullbackAlongAMorphismOfRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismsOfSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension

/-!
# Perfectness is preserved by derived pullback

Let `f : (C, O) ⟶ (D, O')` be a morphism of ringed sites and let `E` be a perfect object of
`D(O')`. Then `Lf^* E` is perfect. This is Stacks 08H6.

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

* `AlgebraicGeometry.RingedSite.Hom.isPerfect_derivedPullback`: **Stacks 08H6.**

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

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard


/-! ### Carrying a strictly perfect model over an object of the site -/

section Model

variable (Z : RingedSite.{0, 0, 0})
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{0}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective

/-- The property of an object `V` of a ringed site used throughout the proof of Stacks 08H6: the
restriction of the complex `K` to the slice over `V` is isomorphic, *in the derived category of
that slice*, to a strictly perfect complex of `O|_V`-modules.

This is the hypothesis of Stacks 08G6 (1) read at one object, in the form
`AlgebraicGeometry.RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect` consumes it,
and phrased against a chosen complex representative rather than against an object of `D(O)`
because that is the form which both pulls back along `f` and descends along an arrow of the
site. -/
private def HasStrictlyPerfectModel
    (K : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (V : Z.C) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (Z.restrictComplex K V))

/-- A derived-category isomorphism `Q K ≅ E` restricts to the slice over `V`: the restriction of
the complex `K` is isomorphic to the restriction of `E`. -/
private def restrictComplexIsoOfIso
    {K : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ}
    {E : DerivedCategory
      (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))}
    (e : DerivedCategory.Q.obj K ≅ E) (V : Z.C) :
    DerivedCategory.Q.obj (Z.restrictComplex K V) ≅
      (SheafOfModules.overFunctor.{0}
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).mapDerivedCategory.obj E :=
  ((SheafOfModules.overFunctor.{0}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).mapDerivedCategoryFactors.app K).symm ≪≫
    (SheafOfModules.overFunctor.{0}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).mapDerivedCategory.mapIso e

end Model

section Main

variable {X Y : RingedSite.{0, 0, 0}} (f : RingedSite.Hom X Y)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [HasSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasSheafify Y.J AddCommGrpCat.{0}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasFiniteLimits X.C] [HasFiniteLimits Y.C] [PreservesFiniteLimits f.u]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Y.C, HasSheafify (Y.J.over U) AddCommGrpCat.{0}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]



attribute [local instance] ovSheafCompose


attribute [local instance] overMapLimits overMapColimits

attribute [local instance] derivedPullbackHasLeftDerived
  derivedPullbackLocalizedHasLeftDerived derivedPullbackLocalizedCommShift

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [HasSheafify Y.J AddCommGrpCat.{0}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasFiniteLimits Y.C]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})] in
/-- **A perfect complex carries strictly perfect derived models on a covering of every object.**
This is the definition of a perfect complex, Stacks 08G5, with the chain-level
quasi-isomorphisms turned into isomorphisms of the derived categories of the slices. -/
private theorem exists_coveringFamily_hasStrictlyPerfectModel
    (K : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Y.IsPerfectComplex K)
    (W : Y.C) :
    ∃ S : Presieve W, Sieve.generate S ∈ Y.J W ∧
      ∀ ⦃V : Y.C⦄ (g : V ⟶ W), S g → HasStrictlyPerfectModel Y K V := by
  obtain ⟨S, hS, hmodels⟩ := hK W
  refine ⟨S, hS, fun {V} g hg => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hmodels g hg
  let : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (C := SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V)) q).2 hq
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map q)⟩⟩

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [HasSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasFiniteLimits X.C]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})] in
/-- **A strictly perfect derived model descends along an arrow of the site.** Restriction to a
smaller slice is exact, so it preserves strict perfectness and carries an isomorphism of the
derived categories to an isomorphism, and it carries a complex representative of a restriction
to a complex representative of the smaller restriction. -/
private theorem hasStrictlyPerfectModel_of_hom
    (K' : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {V V' : X.C} (a : V' ⟶ V)
    (h : HasStrictlyPerfectModel X K' V) : HasStrictlyPerfectModel X K' V' := by
  obtain ⟨P, hP, ⟨β⟩⟩ := h
  have hcmp : ((SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      a).mapHomologicalComplex (ComplexShape.up ℤ)).obj (X.restrictComplex K' V) ≅
        X.restrictComplex K' V' :=
    (Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).app K'
  refine ⟨((SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      a).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a hP, ⟨?_⟩⟩
  exact ((SheafOfModules.overMap.{0}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).mapDerivedCategoryFactors.app P).symm ≪≫
    (SheafOfModules.overMap.{0}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).mapDerivedCategory.mapIso β ≪≫
    (SheafOfModules.overMap.{0}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).mapDerivedCategoryFactors.app
      (X.restrictComplex K' V) ≪≫ DerivedCategory.Q.mapIso hcmp

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})] in
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
      (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Y).O)))
    (K : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (K' : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
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
      (Stacks.SheafOfModules.Tensor.ringSheaf.{0, 0, 0} (Y.over W).O) P₀ := hP₀
  have hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{0, 0, 0, 0}
      (O := (Y.over W).O) (P₀.X i) :=
    fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect hP₀' i
  have eFlat := derivedPullbackObjIsoOfFlat (f.localized W).toRingedToposSiteHom hmos' P₀ n hLE
    hflat
  have hSP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj W))
      ((pullbackComplex (f.localized W).toRingedToposSiteHom).obj P₀) :=
    isStrictlyPerfect_of_isoX
      (fun i => (f.localized W).pullbackToposIso.app (P₀.X i))
      (AlgebraicGeometry.RingedToposHom.isStrictlyPerfect_pullbackModules
        (f.localized W).ringedToposHom hP₀)
  have eTot : (derivedPullback (f.localized W).toRingedToposSiteHom).obj
        ((SheafOfModules.overFunctor.{0}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W).mapDerivedCategory.obj E) ≅
      DerivedCategory.Q.obj (X.restrictComplex K' (f.u.obj W)) :=
    (f.nonempty_derivedPullbackLocalizedIso W E).some ≪≫
      (restrictComplexIsoOfIso X e' (f.u.obj W)).symm
  exact ⟨(pullbackComplex (f.localized W).toRingedToposSiteHom).obj P₀, hSP,
    ⟨eFlat.symm ≪≫
      (derivedPullback (f.localized W).toRingedToposSiteHom).mapIso
        (α ≪≫ restrictComplexIsoOfIso Y e W) ≪≫ eTot⟩⟩

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})] in
/-- **Stacks 08H6.** The derived pullback along a morphism of ringed sites of a perfect object of
`D(O')` is perfect.

Stacks 08H2 makes the objects `u(W)` cover the final object of `Sh(C)`, and
`CategoryTheory.GrothendieckTopology.coversTop_obj_subtype` refines that covering to the `u(W)`
over which `K` carries a strictly perfect derived model. Over such an object the pullback of the
model is a strictly perfect derived model of `(Lf^* E)|_{u(W)}`
(`hasStrictlyPerfectModel_image`), and it descends along any arrow into `u(W)` by exactness of
restriction (`hasStrictlyPerfectModel_of_hom`), which is what the arrows of that covering
supply; Stacks 08G6 (1) assembles. -/
@[stacks 08H6]
theorem Hom.isPerfect_derivedPullback
    (E : DerivedCategory
      (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Y).O)))
    (hE : Y.IsPerfect E) :
    X.IsPerfect ((derivedPullback f.toRingedToposSiteHom).obj E) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  obtain ⟨K', e'⟩ : Σ' K' : CochainComplex
      (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      DerivedCategory.Q.obj K' ≅ (derivedPullback f.toRingedToposSiteHom).obj E :=
    ⟨DerivedCategory.Q.objPreimage _, DerivedCategory.Q.objObjPreimageIso _⟩
  have := f.isMorphismOfSites.isContinuous
  have : PreservesFiniteLimits (f.u.sheafPullback (Type 0) Y.J X.J) :=
    f.isMorphismOfSites.preservesFiniteLimits
  have : PreservesLimit (Functor.empty.{0} (Sheaf Y.J (Type 0)))
      (f.u.sheafPullback (Type 0) Y.J X.J) := inferInstance
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
  exact ⟨P, hP, ⟨γ ≪≫ restrictComplexIsoOfIso X e' V⟩⟩

end Main

end AlgebraicGeometry.RingedSite

end
