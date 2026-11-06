module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafAlgebraicCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoveringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableFromDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmoothEtaleRefinementRepresentable
public import StacksFrontier.CategoryTheory.Sites.Sheafification.SurjectionCoequalizer

/-!
# Algebraic spaces in the etale topology

Let `S` be a scheme contained in a chosen big fppf site `B`.  Its underlying category is the
common underlying category of the big fppf and the big etale site of Stacks 03FF, so a
presheaf `F` on the big category over `S` may be asked to be a sheaf for either topology
without any transport: `AlgebraicGeometry.BigFppfSite.toBigEtaleSite` carries `B`'s own cutoff
and covering bound by `rfl`, and `AlgebraicGeometry.etaleTopology B` is a topology on `B`'s own
category of schemes.

Stacks 07WF and Stacks 0BH4 are the two criteria of the section: an *etale* sheaf is already an
algebraic space as soon as it has a diagonal representable by algebraic spaces together with a
surjective smooth cover by a scheme, or a cover by an algebraic space which is representable by
algebraic spaces, surjective and etale.  Their value is that the sheaf hypothesis is only the
etale one; the fppf sheaf condition of Algebraic Spaces, Definition 025Y is part of the
conclusion.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_etaleTopology_of_space_atlas` and
  `AlgebraicGeometry.Space.isLocallySurjective_etaleTopology_of_space_atlas_smooth`: a map from
  an algebraic space which is representable by algebraic spaces, surjective and etale (resp.
  smooth) is locally surjective for the chosen etale topology.
* `AlgebraicGeometry.Space.iso_of_isLocallySurjective_of_common_kernelPair`: two maps out of one
  presheaf which are locally surjective for the etale topology and have the same kernel pair
  have isomorphic targets.
* `AlgebraicGeometry.Space.kernelPairRelation`: the kernel pair of a morphism of presheaves, as
  a pre-relation in the slice over its target, with its monicity and its equivalence-relation
  structure.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale_of_etale_space_atlas`:
  **Stacks 0BH4**.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isSheaf_etale_of_smooth_scheme_atlas`:
  **Stacks 07WF**.

## Implementation notes

The proof is the source's.  With `R = X \times_F X` the kernel pair of the given cover, the fppf
quotient sheaf `X/R` of Stacks 044J is an algebraic space by **Stacks 04S6**, part (1); the two
projections of a kernel pair are flat and locally of finite presentation because the cover is
smooth.  Stacks 06PG and Stacks 046O then make `X \to X/R` surjective with kernel pair `R`
again, and Stacks 0429 (resp. Stacks 042B) makes it smooth (resp. etale), so both `X \to F` and
`X \to X/R` are locally surjective for the etale topology with the same kernel pair.  Stacks
086K identifies their targets, and `F` inherits the algebraic-space condition from `X/R`.

Part (1) of Stacks 04S6 is carried as the explicit hypothesis
`AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf` -- the clause the proofs of both tags cite.
What this library has of Stacks 04S6 is conditions (5) and (6), in
`StacksFrontier/AlgebraicGeometry/Spaces/Representable/Bootstrap/FinalBootstrap.lean`, and neither
discharges part (1): both ask the diagonal of the presheaf concluded about to be representable,
which for `X/R` is not available, and both are themselves conditional on condition (3), carried
there as `AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection`.  The docstring
of `AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf` records in full why condition (3) does
not apply either.  Carrying a clause of Stacks 04S6 as a hypothesis is what that module,
`StacksFrontier/AlgebraicGeometry/Stacks/FlatPresentationRepresentableDiagonal.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentableFromDiagonal.lean` already do.

The grant is taken *only* for the quotient sheaf `X/R`, which is an fppf sheaf by construction;
the etale sheaf hypothesis on `F` is what identifies `F` with `X/R`, and no fppf descent for `F`
is assumed anywhere.

The comparison of the two quotients is carried out after composing with
`CategoryTheory.uliftFunctor`, since `CategoryTheory.coequalizer_of_surjection` is stated at the
universe `max v u` of a site with objects in `Type u` and morphisms in `Type v`, while the big
category over `S` has objects in `Type (u + 1)` and morphisms in `Type u`.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 046O](https://stacks.math.columbia.edu/tag/046O)
* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 042B](https://stacks.math.columbia.edu/tag/042B)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 06PG](https://stacks.math.columbia.edu/tag/06PG)
* [Stacks Project, Tag 086K](https://stacks.math.columbia.edu/tag/086K)
* [Stacks Project, Tag 0CFV](https://stacks.math.columbia.edu/tag/0CFV)
* [Stacks Project, Tag 07WF](https://stacks.math.columbia.edu/tag/07WF)
* [Stacks Project, Tag 0BH4](https://stacks.math.columbia.edu/tag/0BH4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_EtaleSheafSpaceCoverCriterion
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Fibre products of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance (priority := high) hasPullback_presheaf_EtaleSheafSpaceCoverCriterion
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks in the slice over a presheaf on the big fppf site over `S` (instance search
times out without this shortcut). -/
local instance hasPullbacks_over_presheaf_EtaleSheafSpaceCoverCriterion
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} :
    HasPullbacks (Over F) := inferInstance

/-- Fibre products in the slice over a presheaf on the big fppf site over `S` (instance
search times out without this shortcut). -/
local instance (priority := high) hasPullback_over_presheaf_EtaleSheafSpaceCoverCriterion
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X Y Z : Over F} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Etale-local surjectivity of a space-level atlas -/

/-- A family of morphisms of the common underlying category of the chosen big fppf and étale
sites which is jointly surjective and étale on underlying schemes generates a covering sieve of
the chosen étale topology. This is the many-member form of
`AlgebraicGeometry.Space.generate_singleton_mem_etaleTopology`. -/
private theorem generate_ofArrows_mem_etaleTopology (B : BigFppfSite.{u}) {X : B.Schemes}
    {J : Type (u + 1)} (Y : J → B.Schemes) (g : ∀ j, Y j ⟶ X)
    (hs : ∀ x, ∃ j, x ∈ Set.range (B.inclusion.map (g j)))
    (he : ∀ j, Etale (B.inclusion.map (g j))) :
    Sieve.generate (Presieve.ofArrows Y g) ∈ etaleTopology B X := by
  have hEt : Presieve.ofArrows (fun j ↦ B.inclusion.obj (Y j)) (fun j ↦ B.inclusion.map (g j)) ∈
      Scheme.etalePrecoverage (B.inclusion.obj X) :=
    (Scheme.ofArrows_mem_precoverage_iff (P := @Etale.{u})).2 ⟨hs, he⟩
  have hE : AlgebraicGeometry.IsEtaleCovering (⟨X, ⟨J, Y, g⟩⟩ : Covering B.Schemes) := by
    change ((⟨J, Y, g⟩ : PreZeroHypercover.{u + 1} X).map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj X)
    exact hEt
  obtain ⟨E', hE', hX, hComb⟩ := etaleCovering_has_representative B _ hE
  have hpre : (⟨J, Y, g⟩ : PreZeroHypercover.{u + 1} X).presieve₀ ∈ etalePrecoverage B X := by
    cases hX
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E'.2, rfl, hE'⟩
  exact Precoverage.generate_mem_toGrothendieck hpre

/-- A family of morphisms of the big fppf category over `S` which is jointly surjective and
étale on underlying schemes admits, on every arrow of a covering sieve of the chosen étale
topology, a factorisation through one of its members. This is the many-member form of
`AlgebraicGeometry.Space.exists_etaleCover_lift_of_surjective_etale`. -/
@[sga "3 IV 6.3.1"]
private theorem exists_etaleCover_lift_of_family (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {J : Type (u + 1)} {T : BigFppfOver B S hS}
    {Ys : J → BigFppfOver B S hS} (q : ∀ j, Ys j ⟶ T)
    (hs : ∀ x, ∃ j, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q j)))
    (he : ∀ j, Etale ((BigFppfOver.toScheme B S hS).map (q j))) :
    ∃ Z : Sieve T, Z ∈ (etaleTopology B).over (B.obj hS) T ∧
      ∀ ⦃W : BigFppfOver B S hS⦄ (k : W ⟶ T), Z k →
        ∃ (j : J) (b : W ⟶ Ys j), b ≫ q j = k := by
  have hbase : Sieve.generate (Presieve.ofArrows (fun j ↦ (Ys j).left)
      (fun j ↦ (BigFppfOver.forget B S hS).map (q j))) ∈ etaleTopology B T.left :=
    generate_ofArrows_mem_etaleTopology B _ _ hs he
  refine ⟨(Sieve.overEquiv T).symm (Sieve.generate (Presieve.ofArrows (fun j ↦ (Ys j).left)
    (fun j ↦ (BigFppfOver.forget B S hS).map (q j)))),
    (etaleTopology B).overEquiv_symm_mem_over T _ hbase, ?_⟩
  intro W k hk
  have hk₀ : Sieve.generate (Presieve.ofArrows (fun j ↦ (Ys j).left)
      (fun j ↦ (BigFppfOver.forget B S hS).map (q j))) k.left := by simpa using hk
  obtain ⟨V, a₀, b₀, hb₀, hfac₀⟩ := hk₀
  obtain ⟨j⟩ := hb₀
  refine ⟨j, Over.homMk a₀ ?_, ?_⟩
  · calc
      a₀ ≫ (Ys j).hom = a₀ ≫ (q j).left ≫ T.hom := by rw [← Over.w (q j)]
      _ = (a₀ ≫ (BigFppfOver.forget B S hS).map (q j)) ≫ T.hom := by
        rw [← Category.assoc]; rfl
      _ = k.left ≫ T.hom := by rw [hfac₀]
      _ = W.hom := Over.w k
  · exact Over.OverMorphism.ext hfac₀

/-- If `c' : h_V ⟶ T ×_F X` lies over `h : V ⟶ T` and `b ≫ h = k`, then `k` factors through
`a : X ⟶ F` after `ξ' : h_T ⟶ F`, i.e. `k` lies in the image sieve of `ξ'` along `a`. -/
private theorem imageSieve_yonedaEquiv_of_comp_eq
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : X ⟶ F) {T V W : BigFppfOver B S hS}
    (ξ' : yoneda.obj T ⟶ F) (c' : yoneda.obj V ⟶ pullback ξ' a) (h : V ⟶ T) (b : W ⟶ V)
    (k : W ⟶ T) (hc : c' ≫ pullback.fst ξ' a = yoneda.map h) (hbk : b ≫ h = k) :
    Presheaf.imageSieve a (yonedaEquiv ξ') k := by
  refine ⟨yonedaEquiv (yoneda.map b ≫ c' ≫ pullback.snd ξ' a), ?_⟩
  rw [← yonedaEquiv_comp, yonedaEquiv_naturality]
  refine congrArg yonedaEquiv ?_
  calc
    (yoneda.map b ≫ c' ≫ pullback.snd ξ' a) ≫ a
        = yoneda.map b ≫ c' ≫ pullback.snd ξ' a ≫ a := by simp only [Category.assoc]
    _ = yoneda.map b ≫ c' ≫ pullback.fst ξ' a ≫ ξ' := by rw [pullback.condition]
    _ = yoneda.map b ≫ (c' ≫ pullback.fst ξ' a) ≫ ξ' := by simp only [Category.assoc]
    _ = yoneda.map b ≫ yoneda.map h ≫ ξ' := by rw [hc]
    _ = yoneda.map (b ≫ h) ≫ ξ' := by rw [Functor.map_comp, Category.assoc]
    _ = yoneda.map k ≫ ξ' := by rw [hbk]

/-- A morphism from an algebraic space to a presheaf which is representable by algebraic
spaces, surjective and étale is locally surjective for the chosen étale topology. -/
theorem isLocallySurjective_etaleTopology_of_space_atlas
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : X ⟶ F)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hsurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) a ha)
    (hetale : HasProperty B S hS (etaleMorphisms B S hS) a ha) :
    Presheaf.IsLocallySurjective ((etaleTopology B).over (B.obj hS)) a := by
  refine ⟨fun {T} ξ ↦ ?_⟩
  set ξ' : yoneda.obj T ⟶ F := yonedaEquiv.symm ξ with hξ'
  obtain ⟨V, c, hcs, hce⟩ := (ha T ξ').exists_atlas
  -- The chosen chart of the base change, composed with the projection, is surjective and étale.
  have h1 : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c ≫ pullback.fst ξ' a) := hetale T ξ' V c hce
  have h2 : IsSurjective B S hS (c ≫ pullback.fst ξ' a) :=
    isSurjective_comp B S hS (isSurjective_of_presheafSurjective B S hS c hcs) (hsurj T ξ')
  -- Read it as a morphism of the site.
  set h : V ⟶ T := yoneda.preimage (c ≫ pullback.fst ξ' a)
  have hmap : yoneda.map h = c ≫ pullback.fst ξ' a := yoneda.map_preimage _
  have hEt : Etale ((BigFppfOver.toScheme B S hS).map h) :=
    (presheaf_yoneda_map_etale_iff B S hS h).1 (by rw [hmap]; exact h1)
  have hSu : Surjective ((BigFppfOver.toScheme B S hS).map h) :=
    (presheaf_yoneda_map_iff B S hS
      (inferInstance : MorphismProperty.IsStableUnderBaseChange (@Surjective.{u})) h).1
      ((presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj T)
        (isAlgebraicSpace_yoneda B S hS T) V (yoneda.map h)).2 (by rw [hmap]; exact h2))
  obtain ⟨Z, hZ, hlift⟩ := exists_etaleCover_lift_of_surjective_etale B S hS h hSu hEt
  refine ((etaleTopology B).over (B.obj hS)).superset_covering ?_ hZ
  intro W k hk
  obtain ⟨b, hbk⟩ := hlift k hk
  have hξ : ξ = yonedaEquiv ξ' := by rw [hξ']; simp
  rw [hξ]
  exact imageSieve_yonedaEquiv_of_comp_eq a ξ' c h b k hmap.symm hbk

/-- Same, with smooth in place of étale. -/
theorem isLocallySurjective_etaleTopology_of_space_atlas_smooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : X ⟶ F)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hsurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) a ha)
    (hsmooth : HasProperty B S hS (smoothMorphismProperty B S hS) a ha) :
    Presheaf.IsLocallySurjective ((etaleTopology B).over (B.obj hS)) a := by
  refine ⟨fun {T} ξ ↦ ?_⟩
  set ξ' : yoneda.obj T ⟶ F := yonedaEquiv.symm ξ with hξ'
  -- The projection of the base change is a one-member smooth covering of `h_T`.
  have hcov : IsSmoothCovering B S hS (fun _ : Unit ↦ pullback ξ' a)
      (fun _ ↦ pullback.fst ξ' a) := by
    refine ⟨isAlgebraicSpace_yoneda B S hS T, fun _ ↦ ha T ξ', fun _ ↦ hsmooth T ξ', ?_⟩
    rw [Set.iUnion_const, Set.range_eq_univ]
    exact hsurj T ξ'
  -- Refine it by an étale covering with representable members (Stacks 0CFV).
  obtain ⟨J, Yj, g, hEt, hfac⟩ :=
    exists_isEtaleCovering_representable_refining_isSmoothCovering B S hS hcov
  set k : ∀ j, Yj j ⟶ T := fun j ↦ yoneda.preimage (g j)
  have hkmap : ∀ j, yoneda.map (k j) = g j := fun j ↦ yoneda.map_preimage _
  have hket : ∀ j, Etale ((BigFppfOver.toScheme B S hS).map (k j)) := by
    intro j
    refine (presheaf_yoneda_map_etale_iff B S hS (k j)).1 ?_
    rw [hkmap j]
    exact (isEtale_iff_presheaf_of_yoneda B S hS (g j)).1 (hEt.etale j)
  have hkpt : ∀ x : (BigFppfOver.toScheme B S hS).obj T, ∃ j,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (k j)) := by
    intro x
    obtain ⟨y, hy⟩ := (bijective_pointsToScheme B S hS T).surjective x
    obtain ⟨j, t, ht⟩ :=
      Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hEt.jointly_surjective y)
    refine ⟨j, pointsToScheme B S hS (Yj j) t, ?_⟩
    rw [← pointsToScheme_pointsMap_yoneda B S hS (k j) t, hkmap j, ht, hy]
  obtain ⟨Z, hZ, hlift⟩ := exists_etaleCover_lift_of_family B S hS k hkpt hket
  refine ((etaleTopology B).over (B.obj hS)).superset_covering ?_ hZ
  intro W m hm
  obtain ⟨j, b, hbm⟩ := hlift m hm
  obtain ⟨-, φ, hφ⟩ := hfac j
  have hξ : ξ = yonedaEquiv ξ' := by rw [hξ']; simp
  rw [hξ]
  exact imageSieve_yonedaEquiv_of_comp_eq a ξ' φ (k j) b m (by rw [hφ, hkmap j]) hbm


/-! ### The comparison of two quotients in etale sheaves -/

/-- Two sections of a presheaf `U` which a map `g` with kernel pair `t, s : R ⟶ U` identifies are
identified by every map out of `U` which coequalizes `t` and `s`. -/
theorem app_eq_of_app_eq_of_isPullback_presheaf {C : Type*} [Category.{u} C]
    {R U Y Z : Cᵒᵖ ⥤ Type u} {t s : R ⟶ U} {g : U ⟶ Y} {h : U ⟶ Z}
    (hg : IsPullback t s g g) (hh : t ≫ h = s ≫ h)
    {V : C} {x y : U.obj (op V)} (hxy : g.app (op V) x = g.app (op V) y) :
    h.app (op V) x = h.app (op V) y := by
  obtain ⟨x', rfl⟩ : ∃ x' : yoneda.obj V ⟶ U, yonedaEquiv x' = x :=
    ⟨yonedaEquiv.symm x, yonedaEquiv.apply_symm_apply x⟩
  obtain ⟨y', rfl⟩ : ∃ y' : yoneda.obj V ⟶ U, yonedaEquiv y' = y :=
    ⟨yonedaEquiv.symm y, yonedaEquiv.apply_symm_apply y⟩
  have hx : x' ≫ g = y' ≫ g := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    exact hxy
  have hfst : hg.lift x' y' hx ≫ t = x' := hg.lift_fst _ _ hx
  have hsnd : hg.lift x' y' hx ≫ s = y' := hg.lift_snd _ _ hx
  have hcomp : x' ≫ h = y' ≫ h := by
    calc
      x' ≫ h = (hg.lift x' y' hx ≫ t) ≫ h := by rw [hfst]
      _ = hg.lift x' y' hx ≫ s ≫ h := by rw [Category.assoc, hh]
      _ = y' ≫ h := by rw [← Category.assoc, hsnd]
  have := congrArg yonedaEquiv hcomp
  rwa [yonedaEquiv_comp, yonedaEquiv_comp] at this

open Stacks.Sites.SurjectionCoequalizer in
/-- Two maps out of a common presheaf which are locally surjective for the chosen étale topology
and have the same kernel pair identify their targets, as soon as both targets are sheaves for
that topology. -/
theorem iso_of_isLocallySurjective_of_common_kernelPair
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {t s : R ⟶ U}
    {g : U ⟶ F} {q : U ⟶ F'}
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hF' : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F')
    (hU : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) U)
    (hg : IsPullback t s g g) (hq : IsPullback t s q q)
    (hlg : Presheaf.IsLocallySurjective ((etaleTopology B).over (B.obj hS)) g)
    (hlq : Presheaf.IsLocallySurjective ((etaleTopology B).over (B.obj hS)) q) :
    Nonempty (F ≅ F') := by
  classical
  -- Pass to the universe in which the coequalizer criterion is stated.
  have hUL : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS))
      (U ⋙ uliftFunctor.{u + 1}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor.{u + 1} hU
  have hFL : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS))
      (F ⋙ uliftFunctor.{u + 1}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor.{u + 1} hF
  have hQL : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS))
      (F' ⋙ uliftFunctor.{u + 1}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor.{u + 1} hF'
  set UF : Sheaf ((etaleTopology B).over (B.obj hS)) (Type (max u (u + 1))) :=
    ⟨U ⋙ uliftFunctor.{u + 1}, hUL⟩ with hUF
  set FF : Sheaf ((etaleTopology B).over (B.obj hS)) (Type (max u (u + 1))) :=
    ⟨F ⋙ uliftFunctor.{u + 1}, hFL⟩ with hFF
  set QQ : Sheaf ((etaleTopology B).over (B.obj hS)) (Type (max u (u + 1))) :=
    ⟨F' ⋙ uliftFunctor.{u + 1}, hQL⟩ with hQQ
  set φ : UF ⟶ FF := ⟨Functor.whiskerRight g uliftFunctor.{u + 1}⟩ with hφ
  set ψ : UF ⟶ QQ := ⟨Functor.whiskerRight q uliftFunctor.{u + 1}⟩ with hψ
  have hsurj : ∀ {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (hG : Presheaf.IsSheaf _ (G ⋙ uliftFunctor.{u + 1})) (f : U ⟶ G),
      Presheaf.IsLocallySurjective ((etaleTopology B).over (B.obj hS)) f →
      IsSurjectiveSheafType ((etaleTopology B).over (B.obj hS))
        (⟨Functor.whiskerRight f uliftFunctor.{u + 1}⟩ : UF ⟶ ⟨G ⋙ uliftFunctor.{u + 1}, hG⟩) :=
    fun _ f hf V ξ => ⟨Presheaf.imageSieve f ξ.down,
      Presheaf.imageSieve_mem ((etaleTopology B).over (B.obj hS)) f ξ.down,
      fun _ _ ⟨x, hx⟩ => ⟨ULift.up x, congrArg ULift.up hx⟩⟩
  have hsurjφ : IsSurjectiveSheafType ((etaleTopology B).over (B.obj hS)) φ := hsurj hFL g hlg
  have hsurjψ : IsSurjectiveSheafType ((etaleTopology B).over (B.obj hS)) ψ := hsurj hQL q hlq
  -- The two maps identify the same pairs of sections of `U`, having the same kernel pair.
  have hFQ : ∀ {V : BigFppfOver B S hS} (x y : U.obj (op V)),
      g.app (op V) x = g.app (op V) y → q.app (op V) x = q.app (op V) y := fun x y hxy ↦
    app_eq_of_app_eq_of_isPullback_presheaf hg hq.w hxy
  have hQF : ∀ {V : BigFppfOver B S hS} (x y : U.obj (op V)),
      q.app (op V) x = q.app (op V) y → g.app (op V) x = g.app (op V) y := fun x y hxy ↦
    app_eq_of_app_eq_of_isPullback_presheaf hq hg.w hxy
  have hcond : ∀ {A C : Sheaf ((etaleTopology B).over (B.obj hS)) (Type (max u (u + 1)))}
      (f : UF ⟶ A) (f' : UF ⟶ C),
      (∀ {V : BigFppfOver B S hS} (x y : UF.obj.obj (op V)),
        f.hom.app (op V) x = f.hom.app (op V) y → f'.hom.app (op V) x = f'.hom.app (op V) y) →
      pullback.fst f f ≫ f' = pullback.snd f f ≫ f' := by
    intro A C f f' hff'
    apply Sheaf.hom_ext
    ext ⟨V⟩ p
    exact hff' _ _ (congrArg (fun η : pullback f f ⟶ A ↦ η.hom.app (op V) p)
      (pullback.condition (f := f) (g := f)))
  have hcondψ : pullback.fst φ φ ≫ ψ = pullback.snd φ φ ≫ ψ :=
    hcond φ ψ fun x y h ↦ congrArg ULift.up (hFQ _ _ (congrArg ULift.down h))
  have hcondφ : pullback.fst ψ ψ ≫ φ = pullback.snd ψ ψ ≫ φ :=
    hcond ψ φ fun x y h ↦ congrArg ULift.up (hQF _ _ (congrArg ULift.down h))
  -- Both are coequalizers of their common kernel pair, hence isomorphic.
  have hcolφ := Classical.choice
    (coequalizer_of_surjection ((etaleTopology B).over (B.obj hS)) φ hsurjφ)
  have hcolψ := Classical.choice
    (coequalizer_of_surjection ((etaleTopology B).over (B.obj hS)) ψ hsurjψ)
  set a : FF ⟶ QQ := hcolφ.desc (Cofork.ofπ ψ hcondψ) with ha
  set b : QQ ⟶ FF := hcolψ.desc (Cofork.ofπ φ hcondφ) with hb
  have hfacφ : φ ≫ a = ψ := by
    have := hcolφ.fac (Cofork.ofπ ψ hcondψ) WalkingParallelPair.one
    simpa [coequalizerCofork] using this
  have hfacψ : ψ ≫ b = φ := by
    have := hcolψ.fac (Cofork.ofπ φ hcondφ) WalkingParallelPair.one
    simpa [coequalizerCofork] using this
  have hab : a ≫ b = 𝟙 FF := by
    refine Cofork.IsColimit.hom_ext hcolφ ?_
    simp only [coequalizerCofork, Cofork.π_ofπ]
    rw [← Category.assoc, hfacφ, hfacψ]
    exact (Category.comp_id φ).symm
  have hba : b ≫ a = 𝟙 QQ := by
    refine Cofork.IsColimit.hom_ext hcolψ ?_
    simp only [coequalizerCofork, Cofork.π_ofπ]
    rw [← Category.assoc, hfacψ, hfacφ]
    exact (Category.comp_id ψ).symm
  -- Descend the isomorphism along the fully faithful whiskering by `uliftFunctor`.
  have hiso : (F ⋙ uliftFunctor.{u + 1}) ≅ (F' ⋙ uliftFunctor.{u + 1}) :=
    (sheafToPresheaf _ _).mapIso ⟨a, b, hab, hba⟩
  exact ⟨((Functor.whiskeringRight ((BigFppfOver B S hS)ᵒᵖ) (Type u)
    (Type (max u (u + 1)))).obj uliftFunctor.{u + 1}).preimageIso hiso⟩


/-! ### The kernel pair of a morphism of presheaves -/

section KernelPair

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The kernel pair of `a`, as an object of the slice over `F`. -/
noncomputable abbrev kpRel (a : X ⟶ F) : Over F := Over.mk (pullback.fst a a ≫ a)

/-- The first projection of the kernel pair, in the slice over `F`. -/
noncomputable def kpFst (a : X ⟶ F) : kpRel a ⟶ (Over.mk a : Over F) :=
  Over.homMk (pullback.fst a a) rfl

/-- The second projection of the kernel pair, in the slice over `F`. -/
noncomputable def kpSnd (a : X ⟶ F) : kpRel a ⟶ (Over.mk a : Over F) :=
  Over.homMk (pullback.snd a a) pullback.condition.symm

/-- The kernel pair of `a`, as a pre-relation in the slice over `F`. -/
noncomputable def kernelPairRelation (a : X ⟶ F) :
    PreRelation (kpRel a) (Over.mk a : Over F) :=
  prod.lift (kpFst a) (kpSnd a)

/-- The target map of the kernel-pair relation is its first projection. -/
theorem kernelPairRelation_target (a : X ⟶ F) :
    (kernelPairRelation a).target = kpFst a :=
  prod.lift_fst (kpFst a) (kpSnd a)

/-- The source map of the kernel-pair relation is its second projection. -/
theorem kernelPairRelation_source (a : X ⟶ F) :
    (kernelPairRelation a).source = kpSnd a :=
  prod.lift_snd (kpFst a) (kpSnd a)

/-- On underlying presheaves, the target map of the kernel-pair relation is `pullback.fst`. -/
theorem kernelPairRelation_target_left (a : X ⟶ F) :
    (kernelPairRelation a).target.left = pullback.fst a a :=
  congrArg (fun h => h.left) (kernelPairRelation_target a)

/-- On underlying presheaves, the source map of the kernel-pair relation is `pullback.snd`. -/
theorem kernelPairRelation_source_left (a : X ⟶ F) :
    (kernelPairRelation a).source.left = pullback.snd a a :=
  congrArg (fun h => h.left) (kernelPairRelation_source a)




/-- The two projections of a kernel pair are jointly monic. -/
instance jointlyMono₂_kp (a : X ⟶ F) : JointlyMono₂ (kpFst a) (kpSnd a) where
  right_cancellation := by
    intro W f g h₁ h₂
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg (fun k => k.left) h₁
    · exact congrArg (fun k => k.left) h₂

/-- The diagonal of a morphism of presheaves into its kernel pair. -/
noncomputable def kpDiag (a : X ⟶ F) : X ⟶ pullback a a :=
  pullback.lift (𝟙 X) (𝟙 X) rfl

/-- The diagonal is a section of the first projection of the kernel pair. -/
theorem kpDiag_fst (a : X ⟶ F) : kpDiag a ≫ pullback.fst a a = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The diagonal is a section of the second projection of the kernel pair. -/
theorem kpDiag_snd (a : X ⟶ F) : kpDiag a ≫ pullback.snd a a = 𝟙 X :=
  pullback.lift_snd _ _ _

/-- The interchange of the two projections of a kernel pair. -/
noncomputable def kpSwap (a : X ⟶ F) : pullback a a ⟶ pullback a a :=
  pullback.lift (pullback.snd a a) (pullback.fst a a) pullback.condition.symm

/-- The interchange turns the first projection of the kernel pair into the second. -/
theorem kpSwap_fst (a : X ⟶ F) : kpSwap a ≫ pullback.fst a a = pullback.snd a a :=
  pullback.lift_fst _ _ _

/-- The interchange turns the second projection of the kernel pair into the first. -/
theorem kpSwap_snd (a : X ⟶ F) : kpSwap a ≫ pullback.snd a a = pullback.fst a a :=
  pullback.lift_snd _ _ _

/-- The composition witness for transitivity of a kernel pair. -/
noncomputable def kpTrans (a : X ⟶ F) :
    ((pullback (kpSnd a) (kpFst a)) : Over F).left ⟶ pullback a a :=
  pullback.lift ((pullback.fst (kpSnd a) (kpFst a) ≫ kpFst a).left)
    ((pullback.snd (kpSnd a) (kpFst a) ≫ kpSnd a).left)
    ((Over.w (pullback.fst (kpSnd a) (kpFst a) ≫ kpFst a)).trans
      (Over.w (pullback.snd (kpSnd a) (kpFst a) ≫ kpSnd a)).symm)

/-- The composition witness has the first projection of the first of two composable pairs. -/
theorem kpTrans_fst (a : X ⟶ F) :
    kpTrans a ≫ pullback.fst a a = (pullback.fst (kpSnd a) (kpFst a) ≫ kpFst a).left :=
  pullback.lift_fst _ _ _

/-- The composition witness has the second projection of the second of two composable pairs. -/
theorem kpTrans_snd (a : X ⟶ F) :
    kpTrans a ≫ pullback.snd a a = (pullback.snd (kpSnd a) (kpFst a) ≫ kpSnd a).left :=
  pullback.lift_snd _ _ _

/-- The kernel pair of a morphism of presheaves is an equivalence relation in the slice over
the target. -/
noncomputable def equivalenceRelation_kp (a : X ⟶ F) :
    EquivalenceRelation (kpFst a) (kpSnd a) where
  r := Over.homMk (kpDiag a) (by
    rw [show (kpRel a).hom = pullback.fst a a ≫ a from rfl, ← Category.assoc, kpDiag_fst,
      Category.id_comp]
    rfl)
  reflexivity₁ := Over.OverMorphism.ext (kpDiag_fst a)
  reflexivity₂ := Over.OverMorphism.ext (kpDiag_snd a)
  s := Over.homMk (kpSwap a) (by
    rw [show (kpRel a).hom = pullback.fst a a ≫ a from rfl, ← Category.assoc, kpSwap_fst]
    exact pullback.condition.symm)
  symmetry₁ := Over.OverMorphism.ext (kpSwap_fst a)
  symmetry₂ := Over.OverMorphism.ext (kpSwap_snd a)
  c := pullback.cone (kpSnd a) (kpFst a)
  isLimit := pullback.isLimit (kpSnd a) (kpFst a)
  t := Over.homMk (kpTrans a) (by
    rw [show (kpRel a).hom = pullback.fst a a ≫ a from rfl, ← Category.assoc, kpTrans_fst]
    exact Over.w (pullback.fst (kpSnd a) (kpFst a) ≫ kpFst a))
  transitivity₁ := Over.OverMorphism.ext (kpTrans_fst a)
  transitivity₂ := Over.OverMorphism.ext (kpTrans_snd a)

/-- The two projections of a kernel pair form an equivalence relation. -/
instance isEquivalenceRelation_kp (a : X ⟶ F) :
    IsEquivalenceRelation (kpFst a) (kpSnd a) :=
  (equivalenceRelation_kp a).isEquivalenceRelation




/-- A kernel pair is a relation: its pre-relation is a monomorphism. -/
instance mono_kernelPairRelation (a : X ⟶ F) : Mono (kernelPairRelation a) where
  right_cancellation {W} f g h := by
    have h₁ : f ≫ (kernelPairRelation a).target = g ≫ (kernelPairRelation a).target := by
      simp only [PreRelation.target, ← Category.assoc, h]
    have h₂ : f ≫ (kernelPairRelation a).source = g ≫ (kernelPairRelation a).source := by
      simp only [PreRelation.source, ← Category.assoc, h]
    rw [kernelPairRelation_target] at h₁
    rw [kernelPairRelation_source] at h₂
    exact JointlyMono₂.right_cancellation f g h₁ h₂

/-- A kernel pair is an equivalence relation. -/
instance isEquivalenceRelation_kernelPairRelation (a : X ⟶ F) :
    IsEquivalenceRelation (kernelPairRelation a).target (kernelPairRelation a).source := by
  rw [kernelPairRelation_target, kernelPairRelation_source]
  infer_instance




section Quotient

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- The quotient map of a kernel pair is smooth when the projections are. -/
theorem isSmooth_toQuotientSheaf_kernelPairRelation (a : X ⟶ F)
    (hX : IsAlgebraicSpace B S hS X) (hR : IsAlgebraicSpace B S hS (pullback a a))
    (hQ : IsAlgebraicSpace B S hS (quotientSheaf (kernelPairRelation a)).obj)
    (ht : IsSmooth B S hS (pullback.fst a a)) :
    IsSmooth B S hS (toQuotientSheaf (kernelPairRelation a)) :=
  holdsOnEveryEtaleChart_toQuotientSheaf (kernelPairRelation a)
    (isEquivalenceRelation_kernelPairRelation a) hR hX hQ
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
    Smooth.isEtaleLocalOnSourceAndTarget
    (holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
      Smooth.isEtaleLocalOnSourceAndTarget)
    (by rw [kernelPairRelation_target_left]; exact ht)

end Quotient

end KernelPair

/-! ### The two criteria -/

/-- **Stacks 04S6, part (1)**, carried as an explicit hypothesis: the fppf quotient sheaf of an
equivalence relation of algebraic spaces whose two maps are flat and locally of finite
presentation is an algebraic space.  This is the clause the proofs of Stacks 07WF and
Stacks 0BH4 cite for the algebraicity of `X = U/R`.

It is not implied by what this library carries of Stacks 04S6.  That is conditions (5) and (6)
of the source, `AlgebraicGeometry.Space.isAlgebraicSpace_of_diag_of_flat_chart` and
`AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable_diag_of_flat_scheme_chart`,
and neither applies to a quotient sheaf: both require the diagonal of the presheaf being
concluded about to be representable, which for `U/R` is not available and is of the same order
of difficulty as the conclusion.  Both are moreover themselves conditional on condition (3),
carried there as `AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection`, and
condition (3) does not apply either: it needs `U ⟶ U/R` to be representable by algebraic
spaces, which in this library is available only from
`AlgebraicGeometry.Space.relativelyRepresentable_quotientMap_of_isAlgebraicSpace`, gated on the
quotient already being an algebraic space, or from Stacks 0AMP, which is itself conditional on
condition (3).  The unconditional quotient-algebraicity results of the library
(`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase_unconditional` and the
Stacks 02WW route behind `@[stacks 076M]`) all require the relation to be one of *schemes*, so
they do not cover an equivalence relation of algebraic spaces either.

It does, however, *imply* condition (3), and the two other shapes in which this library carries a
clause of Stacks 04S6: see
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_of_quotientSheaf`,
`AlgebraicGeometry.Space.theorem04S6Quotient_of_quotientSheaf` and
`AlgebraicGeometry.Stack.bootstrap04S6Spaces_of_quotientSheaf`.  So this is the single statement
to prove, and proving it discharges every carried clause of the tag at once.

Granting it leaves the content of both tags intact.  `quotientSheaf j` is an fppf sheaf by
construction (Stacks 044J), so no fppf descent is assumed for the presheaf `F` of the two
criteria; the étale sheaf hypothesis on `F` is what identifies `F` with `U/R`, and it is
consumed in exactly one place,
`AlgebraicGeometry.Space.iso_of_isLocallySurjective_of_common_kernelPair`. -/
abbrev Bootstrap04S6QuotientSheaf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Prop :=
  letI : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z} (j : PreRelation R U),
    IsAlgebraicSpace B S hS R.left → IsAlgebraicSpace B S hS U.left →
    IsEquivalenceRelation j.target j.source →
    IsFlat B S hS j.target.left → IsLocallyOfFinitePresentation B S hS j.target.left →
    IsFlat B S hS j.source.left → IsLocallyOfFinitePresentation B S hS j.source.left →
    IsAlgebraicSpace B S hS (quotientSheaf j).obj

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The criterion of Stacks 0GE0 / 07WF / 0BH4: an étale sheaf with a surjective smooth
atlas by an algebraic space, representable by algebraic spaces, is an algebraic space. -/
theorem coreCriterion
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hX : IsAlgebraicSpace B S hS X) (a : X ⟶ F)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hsurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) a ha)
    (hsmooth : HasProperty B S hS (smoothMorphismProperty B S hS) a ha)
    (h04S6 : Bootstrap04S6QuotientSheaf B S hS) :
    IsAlgebraicSpace B S hS F := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  set j := kernelPairRelation a with hj
  -- The relation is an algebraic space.
  have hR : IsAlgebraicSpace B S hS (pullback a a) :=
    isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS a a ha hX
  -- Smoothness of the two projections of the kernel pair.
  have hri : (smoothMorphismProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hfst : IsSmooth B S hS (pullback.fst a a) :=
    hasProperty_pullback_fst_of_isAlgebraicSpace.{u, u} B S hS
      (smoothMorphismProperty B S hS) hX a a ha hsmooth
  have hsnd : IsSmooth B S hS (pullback.snd a a) := by
    let Po : AlgebraicSpaces B S hS := ⟨pullback a a, hR⟩
    let Xo : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let e : Po ≅ Po :=
      ObjectProperty.isoMk (fun G => IsAlgebraicSpace B S hS G) (pullbackSymmetry a a)
    have key := (MorphismProperty.cancel_left_of_respectsIso
      (P := smoothMorphismProperty B S hS) e.hom
      (ObjectProperty.homMk (pullback.fst a a) : Po ⟶ Xo)).mpr hfst
    rwa [show e.hom ≫ (ObjectProperty.homMk (pullback.fst a a) : Po ⟶ Xo) =
        ObjectProperty.homMk (pullback.snd a a) from
      ObjectProperty.hom_ext _ (pullbackSymmetry_hom_comp_fst a a)] at key
  -- Stacks 04S6 makes the quotient sheaf an algebraic space.
  have hQ : IsAlgebraicSpace B S hS (quotientSheaf j).obj := by
    refine h04S6 j hR hX (isEquivalenceRelation_kernelPairRelation a) ?_ ?_ ?_ ?_
    · rw [hj, kernelPairRelation_target_left a]; exact isFlat_of_isSmooth B S hS _ hfst
    · rw [hj, kernelPairRelation_target_left a]
      exact isLocallyOfFinitePresentation_of_isSmooth B S hS hfst
    · rw [hj, kernelPairRelation_source_left a]; exact isFlat_of_isSmooth B S hS _ hsnd
    · rw [hj, kernelPairRelation_source_left a]
      exact isLocallyOfFinitePresentation_of_isSmooth B S hS hsnd
  set q := toQuotientSheaf j with hq
  -- The relation is the kernel pair of the quotient map.
  have := mono_kernelPairRelation a
  have hqpb : IsPullback (pullback.fst a a) (pullback.snd a a) q q := by
    have h := isPullback_toQuotientSheaf j (isEquivalenceRelation_kernelPairRelation a)
      hR.isSheaf hX.isSheaf
    rw [hj] at h
    rw [kernelPairRelation_source_left a, kernelPairRelation_target_left a] at h
    exact h.flip
  -- The quotient map is representable by algebraic spaces, surjective and smooth.
  have hqrep : IsRepresentableByAlgebraicSpaces B S hS q :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS hX hQ q
  have hqsurj : IsSurjective B S hS q := isSurjective_toQuotientSheaf j
  have hqsm : IsSmooth B S hS q := by
    rw [hq, hj]
    exact isSmooth_toQuotientSheaf_kernelPairRelation a hX hR (by rw [← hj]; exact hQ) hfst
  have hqbc : ∀ P : MorphismProperty (AlgebraicSpaces B S hS), P.IsStableUnderBaseChange →
      P (ObjectProperty.homMk q : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨(quotientSheaf j).obj, hQ⟩) → HasProperty B S hS P q hqrep :=
    fun P _ hP U ξ => MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk ξ : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨(quotientSheaf j).obj, hQ⟩)
        (ObjectProperty.homMk q :
          (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨(quotientSheaf j).obj, hQ⟩)).flip hP
  have hqsurj' := hqbc (surjectiveMorphismProperty B S hS) inferInstance hqsurj
  have hqsm' := hqbc (smoothMorphismProperty B S hS) inferInstance hqsm
  -- Both maps out of `X` are locally surjective for the chosen étale topology.
  have hla := isLocallySurjective_etaleTopology_of_space_atlas_smooth B S hS a ha hsurj hsmooth
  have hlq :=
    isLocallySurjective_etaleTopology_of_space_atlas_smooth B S hS q hqrep hqsurj' hqsm'
  -- The étale topology is coarser than the fppf one, so `X` and the quotient are étale sheaves.
  have hle : (etaleTopology B).over (B.obj hS) ≤ BigFppfOver.topology B S hS := by
    intro Xo Z hZ
    rw [GrothendieckTopology.mem_over_iff] at hZ ⊢
    exact Stack.etaleTopology_le_topology B Xo.left hZ
  have hXeta := Presheaf.IsSheaf.of_le hle hX.isSheaf
  have hQeta := Presheaf.IsSheaf.of_le hle hQ.isSheaf
  obtain ⟨e⟩ := iso_of_isLocallySurjective_of_common_kernelPair B S hS hF hQeta hXeta
    (IsPullback.of_hasPullback a a) hqpb hla hlq
  exact hQ.of_iso e.symm

/-- **Stacks 0BH4.** Let `F` be a presheaf of sets on the big category over `S`, which is the
common underlying category of the chosen big fppf and big étale sites. If `F` is a sheaf for the
étale topology and there are an algebraic space `X` over `S` and a morphism `X ⟶ F` which is
representable by algebraic spaces, surjective and étale, then `F` is an algebraic space over `S`
in the sense of Algebraic Spaces, Definition 025Y.

The étale cover is smooth, so the criterion is the smooth one of
`AlgebraicGeometry.Space.coreCriterion`. -/
@[stacks 0BH4 "granted Stacks 04S6 part (1), the algebraicity of the fppf quotient \
sheaf of a flat locally finitely presented equivalence relation of algebraic spaces, carried as \
the hypothesis `h04S6`; the library's Stacks 04S6 is conditions (5) and (6), which need the \
quotient's diagonal and are themselves conditional on condition (3), so neither discharges it"]
theorem isAlgebraicSpace_of_isSheaf_etale_of_etale_space_atlas
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (a : X ⟶ F)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hsurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) a ha)
    (hetale : HasProperty B S hS (etaleMorphisms B S hS) a ha)
    (h04S6 : Bootstrap04S6QuotientSheaf B S hS) :
    IsAlgebraicSpace B S hS F :=
  coreCriterion B S hS hF hX a ha hsurj
    (hetale.mono (fun _ Y _ hf => isSmooth_of_isEtale B S hS Y.property hf)) h04S6

/-- **Stacks 07WF.** Let `F` be a presheaf of sets on the big category over `S`, which is the
common underlying category of the chosen big fppf and big étale sites. If `F` is a sheaf for the
étale topology, its diagonal `Δ : F ⟶ F × F` is representable by algebraic spaces, and there are
an object `U` of the category over `S` and a morphism `h_U ⟶ F` which is surjective and smooth,
then `F` is an algebraic space over `S` in the sense of Algebraic Spaces, Definition 025Y.

The representability by algebraic spaces of the cover is not a further hypothesis: it follows
from the representable diagonal by
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_diagonal`, and the surjectivity and
smoothness are asked of that witness. -/
@[stacks 07WF "granted Stacks 04S6 part (1), the algebraicity of the fppf quotient \
sheaf of a flat locally finitely presented equivalence relation of algebraic spaces, carried as \
the hypothesis `h04S6`; the library's Stacks 04S6 is conditions (5) and (6), which need the \
quotient's diagonal and are themselves conditional on condition (3), so neither discharges it"]
theorem isAlgebraicSpace_of_isSheaf_etale_of_smooth_scheme_atlas
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F)
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS (diag F))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (hsurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) a
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag
        (isAlgebraicSpace_yoneda B S hS U) a))
    (hsmooth : HasProperty B S hS (smoothMorphismProperty B S hS) a
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag
        (isAlgebraicSpace_yoneda B S hS U) a))
    (h04S6 : Bootstrap04S6QuotientSheaf B S hS) :
    IsAlgebraicSpace B S hS F :=
  coreCriterion B S hS hF (isAlgebraicSpace_yoneda B S hS U) a
    (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag
      (isAlgebraicSpace_yoneda B S hS U) a) hsurj hsmooth h04S6

end AlgebraicGeometry.Space

end
