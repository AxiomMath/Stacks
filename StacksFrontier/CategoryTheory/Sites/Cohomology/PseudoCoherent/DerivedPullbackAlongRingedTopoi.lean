module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedApproximationOnASlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.PullbackAlongAMorphismOfRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismsOfSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension

/-!
# Pseudo-coherence is preserved by derived pullback

Let `f : (C, O) ⟶ (D, O')` be a morphism of ringed sites and let `E` be an `m`-pseudo-coherent
object of `D(O')`. Then `Lf^* E` is `m`-pseudo-coherent. This is Stacks 08H4.

## The argument

`E` is represented by an `m`-pseudo-coherent complex `K`, so every object `W` of `D` admits a
covering over each member of which `K` has a strictly perfect approximation in degrees `> m`.
Write `p` for the property "`W` carries such an approximation of `K|_W`".

* Stacks 08H2 says the objects `u(W)`, for `W` an object of `D`, cover the final object of
  `Sh(C)`, and `CategoryTheory.GrothendieckTopology.coversTop_obj_subtype` refines that to the
  objects `u(W)` with `p W`: the covering families `p` supplies are pushed forward along `u` and
  pulled back.
* Over `u(W)` with `p W` the pullback of the approximation is a strictly perfect approximation of
  `(Lf^* E)|_{u(W)}` *in the derived category*: `Lf'^*` of the approximation over `W` is still
  an approximation, because the derived pullback is triangulated and preserves boundedness above
  (`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.map_approximation_of_isLE`), its source is
  computed degreewise since a strictly perfect complex is bounded above with flat terms, strict
  perfectness is preserved by Stacks 08H3, and the target is identified with
  `(Lf^* E)|_{u(W)}` by the derived localization square
  (`AlgebraicGeometry.RingedSite.Hom.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits`).
* Carrying such a derived approximation along an arrow `V ⟶ u(W)` of `C` costs nothing:
  restriction to a smaller slice is exact, so it preserves strict perfectness and both
  cohomological conditions. This is what makes the covering produced in the first step usable,
  its arrows having arbitrary sources with a map to some `u(W)`.
* Finally a derived approximation over every member of a covering of each object is turned into
  the chain-level data the definition asks for by
  `AlgebraicGeometry.RingedSite.exists_coveringSieve_approximation_of_derived`, and Stacks 08FU
  (3) assembles.

None of this uses finite limits on either site or left exactness of `u`: Stacks 08H2 needs only
that `u_s` preserves the final object, and the derived localization square
`AlgebraicGeometry.RingedSite.Hom.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits` holds
for every morphism of ringed sites.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.isPseudoCoherentFrom_derivedPullback`: the derived pullback
  of an `m`-pseudo-coherent object is `m`-pseudo-coherent, for sites in `Type` with finite limits
  and a left exact `u`. This is a special case of Stacks 08H4; the tag itself, for an arbitrary
  morphism of ringed sites at `RingedSite.{u, u, u}` with no finite limits, is
  `AlgebraicGeometry.RingedSite.Hom.isPseudoCoherentFrom_derivedPullback_general`, in the
  module `DerivedPullbackAlongRingedTopoiGeneral` beside this one.

## References

* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Tag 08H2](https://stacks.math.columbia.edu/tag/08H2)
* [Stacks Project, Tag 08H3](https://stacks.math.columbia.edu/tag/08H3)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
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


section Main

variable {X Y : RingedSite.{0, 0, 0}} (f : RingedSite.Hom X Y)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [X.J.HasSheafCompose (forget RingCat.{0})] [Y.J.HasSheafCompose (forget RingCat.{0})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{0})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{0})]
  [HasSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasSheafify Y.J AddCommGrpCat.{0}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasFiniteLimits X.C] [HasFiniteLimits Y.C] [PreservesFiniteLimits f.u]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Y.C, HasSheafify (Y.J.over U) AddCommGrpCat.{0}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget RingCat.{0})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget RingCat.{0})]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget AddCommGrpCat.{0})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget AddCommGrpCat.{0})]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective


attribute [local instance] ovSheafCompose

attribute [local instance] overMapLimits overMapColimits

attribute [local instance] derivedPullbackHasLeftDerived
  derivedPullbackLocalizedHasLeftDerived derivedPullbackLocalizedCommShift

/-- The derived pullback along the localized morphism `f.localized W` is triangulated. -/
local instance pcDerivedPullbackLocalizedIsTriangulated (W : Y.C) :
    (derivedPullback (f.localized W).toRingedToposSiteHom).IsTriangulated :=
  isTriangulated_derivedPullback (f.localized W).toRingedToposSiteHom
    (f.localized W).isMorphismOfSites

/-- The property of an object `W` of the target site used in the proof of Stacks 08H4: the
complex `K` admits a strictly perfect approximation in degrees `> m` over `W`. -/
private def HasApproximation
    (K : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (m : ℤ) (W : Y.C) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) P ∧
    ∃ α : P ⟶ Y.restrictComplex K W,
      (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
      Epi (HomologicalComplex.homologyMap α m)

/-- The property of an object `V` of the source site produced by the proof of Stacks 08H4: a
strictly perfect complex of `O|_V`-modules approximates `K'|_V` in degrees `> m` in the derived
category, `K'` being a fixed complex representative of `Lf^* E`. -/
private def HasDerivedApproximation
    (K' : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) (V : X.C) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
    ∃ β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (X.restrictComplex K' V),
      (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β)) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map β)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [X.J.HasSheafCompose (forget RingCat.{0})] [X.J.HasSheafCompose (forget AddCommGrpCat.{0})]
  [HasSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasFiniteLimits X.C]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget RingCat.{0})]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget AddCommGrpCat.{0})] in
/-- **A derived strictly perfect approximation descends along an arrow of the site.**
Restriction to a smaller slice is exact, so it preserves strict perfectness and both
cohomological conditions, and it carries a complex representative of a restriction to a
complex representative of the smaller restriction. -/
private theorem hasDerivedApproximation_of_hom
    (K' : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) {V V' : X.C} (a : V' ⟶ V)
    (h : HasDerivedApproximation K' m V) : HasDerivedApproximation K' m V' := by
  obtain ⟨P, hP, β, hiso, hepi⟩ := h
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesEpimorphisms
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  set F := (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    a).mapDerivedCategory with hF
  have hFiso := map_approximation_of_isLE F
    (fun L n hL => have := hL
      Stacks.Homology.isLE_mapDerivedCategory_obj
        (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a) L n)
    β m hiso hepi
  have hcmp : (restrictCochainAlong X a).obj (X.restrictComplex K' V) ≅ X.restrictComplex K' V' :=
    (Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).app K'
  let G := SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a
  let eP := G.mapDerivedCategoryFactors.app P
  let eK := G.mapDerivedCategoryFactors.app (X.restrictComplex K' V) ≪≫
    DerivedCategory.Q.mapIso hcmp
  have hB := approximation_comp_iso (F.map β) eK m hFiso.1 hFiso.2
  have hC := iso_comp_approximation eP.symm _ m hB.1 hB.2
  exact ⟨(restrictCochainAlong X a).obj P,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a hP, _, hC.1, hC.2⟩

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [X.J.HasSheafCompose (forget RingCat.{0})] [X.J.HasSheafCompose (forget AddCommGrpCat.{0})]
  [HasFiniteLimits X.C]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget RingCat.{0})]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget AddCommGrpCat.{0})] in
/-- **Derived strictly perfect approximations on a covering of every object make an object of
`D(O)` `m`-pseudo-coherent.** This is the covering form of
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_derived_approximation`: the covering of an
object `U` that the definition of `m`-pseudo-coherence asks for is obtained by binding the given
covering of `U` with the coverings that
`AlgebraicGeometry.RingedSite.exists_coveringSieve_approximation_of_derived` produces over its
members, which is covering by transitivity. -/
private theorem isPseudoCoherentFrom_of_locally_derived_approximation
    (E : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (K : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (h : ∀ U : X.C, ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g → HasDerivedApproximation K m V) :
    X.IsPseudoCoherentFrom E m := by
  classical
  refine ⟨K, fun U => ?_, ⟨e⟩⟩
  obtain ⟨S₀, hS₀, hdata⟩ := h U
  have key : ∀ ⦃V : X.C⦄ (g : V ⟶ U), S₀ g →
      ∃ T : Sieve V, T ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (b : W ⟶ V), T b →
          ∃ P' : CochainComplex
              (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P' ∧
            ∃ α' : P' ⟶ X.restrictComplex K W,
              (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α' j)) ∧
              Epi (HomologicalComplex.homologyMap α' m) := by
    intro V g hg
    obtain ⟨P, hP, β, hiso, hepi⟩ := hdata g hg
    exact X.exists_coveringSieve_approximation_of_derived V K m P hP β hiso hepi
  set T : ∀ ⦃V : X.C⦄ ⦃g : V ⟶ U⦄, S₀ g → Sieve V := fun _ g hg => (key g hg).choose with hT
  have hTmem : ∀ ⦃V : X.C⦄ ⦃g : V ⟶ U⦄ (hg : S₀ g), T hg ∈ X.J V :=
    fun _ g hg => (key g hg).choose_spec.1
  have hS₀' : Sieve.generate S₀.arrows ∈ X.J U := by rw [Sieve.generate_sieve]; exact hS₀
  have hbind : Sieve.bind S₀.arrows T ∈ X.J U := by
    refine X.J.transitive hS₀' _ ?_
    rintro Z b ⟨V, g, g', hg', rfl⟩
    refine X.J.superset_covering ?_
      (X.J.pullback_stable g (hTmem (V := V) (g := g') hg'))
    rw [Sieve.pullback_comp]
    exact Sieve.pullback_monotone g (Sieve.le_pullback_bind S₀.arrows T g' hg')
  refine ⟨(Sieve.bind S₀.arrows T).arrows, ?_, fun W b hb => ?_⟩
  · rw [Sieve.generate_sieve]
    exact hbind
  · obtain ⟨V, g, g', hg', hg, rfl⟩ := hb
    exact (key g' hg').choose_spec.2 g hg

omit [X.J.HasSheafCompose (forget RingCat.{0})] [Y.J.HasSheafCompose (forget RingCat.{0})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{0})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{0})]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget RingCat.{0})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget RingCat.{0})]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget AddCommGrpCat.{0})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget AddCommGrpCat.{0})] in
/-- **The pullback of a strictly perfect approximation is a derived strictly perfect
approximation over the image object.** If `K` has a strictly perfect approximation in degrees
`> m` over `W`, then `Lf^* E` has one in the derived category over `u(W)`.

The approximation over `W` is read in `D(O'|_W)` and pushed through the derived pullback along
the localized morphism `f'` of Stacks 04J0: that functor is triangulated and preserves
boundedness above, so it preserves being an approximation in degrees `> m`
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.map_approximation_of_isLE`). Its value on the
source is computed by degreewise pullback, a strictly perfect complex being bounded above with
flat terms, and the degreewise pullback is strictly perfect by Stacks 08H3. Its value on the
target is `(Lf^* E)|_{u(W)}` by the derived localization square. -/
private theorem hasDerivedApproximation_image
    (E : DerivedCategory
      (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Y).O)))
    (m : ℤ)
    (K : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (K' : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e' : DerivedCategory.Q.obj K' ≅ (derivedPullback f.toRingedToposSiteHom).obj E)
    (W : Y.C) (hW : HasApproximation K m W) :
    HasDerivedApproximation K' m (f.u.obj W) := by
  obtain ⟨P₀, hP₀, α, hgt, hep⟩ := hW
  have hmos' := (f.localized W).isMorphismOfSites
  have hQα := approximation_Q_map α m hgt hep
  have eR : DerivedCategory.Q.obj (Y.restrictComplex K W) ≅
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        W).mapDerivedCategory.obj E :=
    ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        W).mapDerivedCategoryFactors.app K).symm ≪≫
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        W).mapDerivedCategory.mapIso e
  have hαR := approximation_comp_iso (DerivedCategory.Q.map α) eR m hQα.1 hQα.2
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
  have hA := map_approximation_of_isLE (derivedPullback (f.localized W).toRingedToposSiteHom)
    (fun L nn hL => isLE_derivedPullback_obj_of_isMorphismOfSites _ hmos' L nn hL)
    (DerivedCategory.Q.map α ≫ eR.hom) m hαR.1 hαR.2
  have hSP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj W))
      ((pullbackComplex (f.localized W).toRingedToposSiteHom).obj P₀) :=
    isStrictlyPerfect_of_isoX
      (fun i => (f.localized W).pullbackToposIso.app (P₀.X i))
      (AlgebraicGeometry.RingedToposHom.isStrictlyPerfect_pullbackModules
        (f.localized W).ringedToposHom hP₀)
  have eTot : (derivedPullback (f.localized W).toRingedToposSiteHom).obj
        ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          W).mapDerivedCategory.obj E) ≅
      DerivedCategory.Q.obj (X.restrictComplex K' (f.u.obj W)) :=
    (f.nonempty_derivedPullbackLocalizedIso W E).some ≪≫
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (f.u.obj W)).mapDerivedCategory.mapIso e'.symm ≪≫
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (f.u.obj W)).mapDerivedCategoryFactors.app K'
  have hB := approximation_comp_iso
    ((derivedPullback (f.localized W).toRingedToposSiteHom).map
      (DerivedCategory.Q.map α ≫ eR.hom)) eTot m hA.1 hA.2
  have hC := iso_comp_approximation eFlat.symm
    ((derivedPullback (f.localized W).toRingedToposSiteHom).map
      (DerivedCategory.Q.map α ≫ eR.hom) ≫ eTot.hom) m hB.1 hB.2
  exact ⟨(pullbackComplex (f.localized W).toRingedToposSiteHom).obj P₀, hSP,
    eFlat.inv ≫ (derivedPullback (f.localized W).toRingedToposSiteHom).map
      (DerivedCategory.Q.map α ≫ eR.hom) ≫ eTot.hom, hC.1, hC.2⟩

omit [X.J.HasSheafCompose (forget RingCat.{0})] [Y.J.HasSheafCompose (forget RingCat.{0})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{0})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{0})]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget RingCat.{0})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget RingCat.{0})]
  [∀ U : X.C, (X.J.over U).HasSheafCompose (forget AddCommGrpCat.{0})]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget AddCommGrpCat.{0})] in
/-- The derived pullback along a morphism of ringed sites of an `m`-pseudo-coherent object of
`D(O')` is `m`-pseudo-coherent, in the special case of sites in `Type` with finite limits and a
functor `u` preserving them. Stacks 08H4 itself, for an arbitrary morphism of ringed sites at
`RingedSite.{u, u, u}` and with none of these three classes, is
`AlgebraicGeometry.RingedSite.Hom.isPseudoCoherentFrom_derivedPullback_general`.

Stacks 08H2 makes the objects `u(W)` cover the final object of `Sh(C)`, and
`CategoryTheory.GrothendieckTopology.coversTop_obj_subtype` refines that covering to the `u(W)`
over which `K` carries a strictly perfect approximation. Over such an object the pullback of the
approximation is a derived strictly perfect approximation of `(Lf^* E)|_{u(W)}`
(`hasDerivedApproximation_image`), and it descends along any arrow into `u(W)` by exactness of
restriction (`hasDerivedApproximation_of_hom`), which is what the arrows of that covering
supply. -/
theorem Hom.isPseudoCoherentFrom_derivedPullback
    (E : DerivedCategory
      (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Y).O)))
    (m : ℤ)
    (hE : Y.IsPseudoCoherentFrom E m) :
    X.IsPseudoCoherentFrom ((derivedPullback f.toRingedToposSiteHom).obj E) m := by
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
      (fun W : {W : Y.C // HasApproximation K m W} => f.u.obj W.val) :=
    CategoryTheory.GrothendieckTopology.coversTop_obj_subtype f.u Y.J X.J hTop _ hK
  refine isPseudoCoherentFrom_of_locally_derived_approximation (X := X) _ m K' e' (fun U => ?_)
  refine ⟨Sieve.ofObjects (fun W : {W : Y.C // HasApproximation K m W} => f.u.obj W.val) U,
    hcover U, ?_⟩
  rintro V g ⟨⟨W, hW⟩, ⟨k⟩⟩
  exact hasDerivedApproximation_of_hom K' m k
    (hasDerivedApproximation_image f E m K e K' e' W hW)

end Main

end AlgebraicGeometry.RingedSite

end
