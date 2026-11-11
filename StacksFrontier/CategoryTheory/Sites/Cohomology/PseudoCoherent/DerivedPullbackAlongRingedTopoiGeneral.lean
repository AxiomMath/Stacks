module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedPullbackAlongRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedApproximationOnASliceGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral
import all StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedPullbackPerfectGeneralUniverse

/-!
# Pseudo-coherence is preserved by derived pullback along any morphism of ringed sites

Let `f : (C, O) ⟶ (D, O')` be a morphism of ringed sites, given by a continuous functor
`u : D ⥤ C` whose sheaf pullback `u_s` is exact, and let `E` be an `m`-pseudo-coherent object of
`D(O')`. Then `Lf^* E` is `m`-pseudo-coherent. This is Stacks 08H4, with no finite limits on
either site and no left exactness of `u`, at `RingedSite.{u, u, u}`: those are the universes at
which `AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom` and the derived pullback of
Stacks 06YY are defined for a morphism of ringed sites.

## The argument

It is the one of the source.

* Stacks 08H2 (the site-theoretic Sites 7.14.10) needs only that `u_s` preserves the final
  object: every object `U` of `C` has a covering `{U_i → U}` with maps `U_i → u(V_i)`.
  `CategoryTheory.GrothendieckTopology.coversTop_obj_subtype` refines it to the `u(V)` over which
  a fixed representative `K` of `E` has a strictly perfect approximation in degrees `> m`.
* Over such a `u(V)` the approximation is pushed through the derived pullback along the
  localized morphism `f'` of Stacks 04J0: `L(f')^*` is triangulated and preserves boundedness
  above, so the cone of the approximation stays in degrees `< m` and the image is again an
  approximation; on the strictly perfect source `L(f')^*` is the degreewise pullback, strictly
  perfect by Stacks 08H3; and the target is `(Lf^* E)|_{u(V)}` by the derived localization
  square `AlgebraicGeometry.RingedSite.Hom.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits`,
  which holds for every morphism of ringed sites.
* Restriction along `U_i → u(V)` is exact, so it carries the approximation down to `U_i`, and
  Stacks 08FU assembles.

The special case for sites in `Type` with finite limits and a left exact `u` is
`AlgebraicGeometry.RingedSite.Hom.isPseudoCoherentFrom_derivedPullback`.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.isPseudoCoherentFrom_derivedPullback_general`:
  **Stacks 08H4.**

## References

* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Tag 08H2](https://stacks.math.columbia.edu/tag/08H2)
* [Stacks Project, Tag 08H3](https://stacks.math.columbia.edu/tag/08H3)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
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

section General

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, HasSheafify (Y.J.over U) AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective

attribute [local instance] derivedPullbackHasLeftDerived
  derivedPullbackLocalizedHasLeftDerived derivedPullbackLocalizedCommShift

/-- The forgetful functor to rings composes with the sheaf condition on each slice of the site,
at the spelling `(Z.over U).J` of the localized topology. -/
private instance ovSheafComposeGeneral {Z : RingedSite.{u, u, u}}
    [∀ U : Z.C, (Z.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (U : Z.C) :
    (Z.over U).J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  (inferInstance : ∀ U : Z.C,
    (Z.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})) U

/-- Restriction along an arrow of the site preserves finite limits. -/
private instance overMapLimitsGeneral {Z : RingedSite.{u, u, u}}
    [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{u}]
    [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {U V : Z.C}
    (g : V ⟶ U) :
    PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction along an arrow of the site preserves finite colimits. -/
private instance overMapColimitsGeneral {Z : RingedSite.{u, u, u}}
    [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{u}]
    [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {U V : Z.C}
    (g : V ⟶ U) :
    PreservesFiniteColimits
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

/-- The property of an object `W` of the target site used in the proof of Stacks 08H4: the
complex `K` admits a strictly perfect approximation in degrees `> m` over `W`. -/
private def HasApproximationUniv
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (m : ℤ) (W : Y.C) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) P ∧
    ∃ α : P ⟶ Y.restrictComplex K W,
      (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
      Epi (HomologicalComplex.homologyMap α m)

/-- The property of an object `V` of the source site produced by the proof of Stacks 08H4: a
strictly perfect complex of `O|_V`-modules approximates `K'|_V` in degrees `> m` in the derived
category, `K'` being a fixed complex representative of `Lf^* E`. -/
private def HasDerivedApproximationUniv
    (K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) (V : X.C) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
    ∃ β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (X.restrictComplex K' V),
      (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β)) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map β)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A derived strictly perfect approximation descends along an arrow of the site.**
Restriction to a smaller slice is exact, so it preserves strict perfectness and both
cohomological conditions, and it carries a complex representative of a restriction to a
complex representative of the smaller restriction. -/
private theorem hasDerivedApproximationUniv_of_hom
    (K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) {V V' : X.C} (a : V' ⟶ V)
    (h : HasDerivedApproximationUniv K' m V) : HasDerivedApproximationUniv K' m V' := by
  obtain ⟨P, hP, β, hiso, hepi⟩ := h
  have := Stacks.SheafOfModules.LocalCokernel.overMap_preservesEpimorphisms
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a
  set F := (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    a).mapDerivedCategory with hF
  have hFiso := map_approximation_of_isLE F
    (fun L n hL => have := hL
      Stacks.Homology.isLE_mapDerivedCategory_obj
        (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a) L n)
    β m hiso hepi
  have hcmp : (restrictCochainAlong X a).obj (X.restrictComplex K' V) ≅ X.restrictComplex K' V' :=
    (Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a).app K'
  let G := SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a
  let eP := G.mapDerivedCategoryFactors.app P
  let eK := G.mapDerivedCategoryFactors.app (X.restrictComplex K' V) ≪≫
    DerivedCategory.Q.mapIso hcmp
  have hB := approximation_comp_iso (F.map β) eK m hFiso.1 hFiso.2
  have hC := iso_comp_approximation eP.symm _ m hB.1 hB.2
  exact ⟨(restrictCochainAlong X a).obj P,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a hP, _, hC.1, hC.2⟩

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Derived strictly perfect approximations on a covering of every object make an object of
`D(O)` `m`-pseudo-coherent.** The covering of an object `U` that the definition of
`m`-pseudo-coherence asks for is obtained by binding the given covering of `U` with the
coverings that
`AlgebraicGeometry.RingedSite.exists_coveringSieve_approximation_of_derived_general` produces
over its members, which is covering by transitivity. -/
private theorem isPseudoCoherentFrom_of_locally_derived_approximation_univ
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (h : ∀ U : X.C, ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U), S g → HasDerivedApproximationUniv K m V) :
    X.IsPseudoCoherentFrom E m := by
  classical
  refine ⟨K, fun U => ?_, ⟨e⟩⟩
  obtain ⟨S₀, hS₀, hdata⟩ := h U
  have key : ∀ ⦃V : X.C⦄ (g : V ⟶ U), S₀ g →
      ∃ T : Sieve V, T ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (b : W ⟶ V), T b →
          ∃ P' : CochainComplex
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P' ∧
            ∃ α' : P' ⟶ X.restrictComplex K W,
              (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α' j)) ∧
              Epi (HomologicalComplex.homologyMap α' m) := by
    intro V g hg
    obtain ⟨P, hP, β, hiso, hepi⟩ := hdata g hg
    exact X.exists_coveringSieve_approximation_of_derived_general V K m P hP β hiso hepi
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

/-- **The pullback of a strictly perfect approximation is a derived strictly perfect
approximation over the image object.** If `K` has a strictly perfect approximation in degrees
`> m` over `W`, then `Lf^* E` has one in the derived category over `u(W)`.

The approximation over `W` is read in `D(O'|_W)` and pushed through the derived pullback along
the localized morphism `f'` of Stacks 04J0: that functor is triangulated and preserves
boundedness above, so it preserves being an approximation in degrees `> m`
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.map_approximation_of_isLE`). Its value on the
source is computed by degreewise pullback, a strictly perfect complex being bounded above with
flat terms, and the degreewise pullback is strictly perfect by Stacks 08H3. Its value on the
target is `(Lf^* E)|_{u(W)}` by the derived localization square in the form
`AlgebraicGeometry.RingedSite.Hom.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits`, which
asks for no finite limits on either site. -/
private theorem hasDerivedApproximationUniv_image
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Y).O)))
    (m : ℤ)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e' : DerivedCategory.Q.obj K' ≅ (derivedPullback f.toRingedToposSiteHom).obj E)
    (W : Y.C) (hW : HasApproximationUniv K m W) :
    HasDerivedApproximationUniv K' m (f.u.obj W) := by
  obtain ⟨P₀, hP₀, α, hgt, hep⟩ := hW
  have hmos' := (f.localized W).isMorphismOfSites
  have hQα := approximation_Q_map α m hgt hep
  have eR : DerivedCategory.Q.obj (Y.restrictComplex K W) ≅
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        W).mapDerivedCategory.obj E :=
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        W).mapDerivedCategoryFactors.app K).symm ≪≫
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        W).mapDerivedCategory.mapIso e
  have hαR := approximation_comp_iso (DerivedCategory.Q.map α) eR m hQα.1 hQα.2
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
  have : (derivedPullback (f.localized W).toRingedToposSiteHom).IsTriangulated :=
    isTriangulated_derivedPullback (f.localized W).toRingedToposSiteHom hmos'
  have hA := map_approximation_of_isLE (derivedPullback (f.localized W).toRingedToposSiteHom)
    (fun L nn hL => isLE_derivedPullback_obj_of_isMorphismOfSites _ hmos' L nn hL)
    (DerivedCategory.Q.map α ≫ eR.hom) m hαR.1 hαR.2
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
    (f.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits W E).some ≪≫
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (f.u.obj W)).mapDerivedCategory.mapIso e'.symm ≪≫
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
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

/-- **Stacks 08H4.** Let `f : (C, O) ⟶ (D, O')` be a morphism of ringed sites, given by a
continuous functor `u : D ⥤ C` whose sheaf pullback `u_s` is exact, and let `E` be an
`m`-pseudo-coherent object of `D(O')`. Then `Lf^* E` is `m`-pseudo-coherent.

No finite limits are asked of either site and `u` need not be left exact. The statement is at
`RingedSite.{u, u, u}`, the universes at which
`AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom` and the derived pullback `Lf^*` of
Stacks 06YY are defined for a morphism of ringed sites.

Stacks 08H2 (the site-theoretic Sites 7.14.10) makes the objects `u(W)` cover every object of
`C`: each `U` has a covering `{U_i → U}` with maps `U_i → u(W_i)`.
`CategoryTheory.GrothendieckTopology.coversTop_obj_subtype` refines that covering to the `u(W)`
over which `K` carries a strictly perfect approximation. Over such an object the pullback of the
approximation is a derived strictly perfect approximation of `(Lf^* E)|_{u(W)}`, by the cone
argument for the triangulated, bounded-above-preserving `L(f')^*` together with
`L(f')^* P = (f')^* P` on the strictly perfect `P` and Stacks 08H3; it descends along any arrow
into `u(W)` by exactness of restriction, which is what the arrows of that covering supply. -/
@[stacks 08H4]
theorem Hom.isPseudoCoherentFrom_derivedPullback_general
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Y).O)))
    (m : ℤ)
    (hE : Y.IsPseudoCoherentFrom E m) :
    X.IsPseudoCoherentFrom ((derivedPullback f.toRingedToposSiteHom).obj E) m := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  obtain ⟨K', e'⟩ : Σ' K' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      DerivedCategory.Q.obj K' ≅ (derivedPullback f.toRingedToposSiteHom).obj E :=
    ⟨DerivedCategory.Q.objPreimage _, DerivedCategory.Q.objObjPreimageIso _⟩
  have := f.isMorphismOfSites.isContinuous
  have : PreservesFiniteLimits (f.u.sheafPullback (Type u) Y.J X.J) :=
    f.isMorphismOfSites.preservesFiniteLimits
  have : PreservesLimit (Functor.empty.{0} (Sheaf Y.J (Type u)))
      (f.u.sheafPullback (Type u) Y.J X.J) := inferInstance
  have hTop : X.J.CoversTop f.u.obj :=
    CategoryTheory.GrothendieckTopology.coversTop_obj_of_preservesTerminal_sheafPullback
      f.u Y.J X.J
  have hcover : X.J.CoversTop
      (fun W : {W : Y.C // HasApproximationUniv K m W} => f.u.obj W.val) :=
    CategoryTheory.GrothendieckTopology.coversTop_obj_subtype f.u Y.J X.J hTop _ hK
  refine isPseudoCoherentFrom_of_locally_derived_approximation_univ (X := X) _ m K' e'
    (fun U => ?_)
  refine ⟨Sieve.ofObjects (fun W : {W : Y.C // HasApproximationUniv K m W} => f.u.obj W.val) U,
    hcover U, ?_⟩
  rintro V g ⟨⟨W, hW⟩, ⟨k⟩⟩
  exact hasDerivedApproximationUniv_of_hom K' m k
    (hasDerivedApproximationUniv_image f E m K e K' e' W hW)

end General

end AlgebraicGeometry.RingedSite

end
