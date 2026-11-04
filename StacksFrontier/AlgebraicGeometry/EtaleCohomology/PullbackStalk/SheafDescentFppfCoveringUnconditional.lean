module
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentFppfCovering
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentFppfCovering

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentEtale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FppfApplication.FiniteDomination
public import StacksFrontier.AlgebraicGeometry.PartTwoResidue.Complete
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# SheafDescentFppfCoveringUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentFppfCovering`, stated as
separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u t

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace AlgebraicGeometry

/-- A family of morphisms of a big étale site which is jointly surjective on points stays jointly
surjective after base change along any morphism of the site. -/
public theorem exists_mem_range_inclusion_map_pullback_snd_general (B : BigEtaleSite.{u})
    {Z T : B.Scheme} {K : Type*} {W : K → B.Scheme} (j : ∀ c, W c ⟶ Z) (p : T ⟶ Z)
    (hj : ∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c))) (t : B.inclusion.obj T) :
    ∃ c, t ∈ Set.range (B.inclusion.map (pullback.snd (j c) p)) := by
  obtain ⟨c, w, hw⟩ := hj (B.inclusion.map p t)
  have := preservesPullbacks_bigEtaleSiteInclusion B
  have hpb : IsPullback (B.inclusion.map (pullback.fst (j c) p))
      (B.inclusion.map (pullback.snd (j c) p)) (B.inclusion.map (j c)) (B.inclusion.map p) :=
    B.inclusion.map_isPullback (IsPullback.of_hasPullback (j c) p)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback w t hw
  refine ⟨c, hpb.isoPullback.inv z, ?_⟩
  rwa [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_snd]

/-- The functor sending a small étale sheaf on `Y` to its canonical descent datum for a family
of morphisms `f i : X i ⟶ Y` of a big étale site. For a one-member family this is the functor
of [Stacks, Tag 0GEY], `AlgebraicGeometry.smallEtaleSheafDescentFunctorGeneral`. -/
public noncomputable def smallEtaleSheafFamilyDescentFunctorGeneral (B : BigEtaleSite.{u})
    {I : Type t} {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y) :
    Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1)) ⥤
      (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.DescentData f :=
  (eqToHom ((smallEtaleSheafPullbackSystemGeneral B).fiber Y).symm).toFunctor ⋙
    (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData f

/-- For a one-member family the canonical descent functor is the one used by the library's
[Stacks, Tag 0GF2]. -/
public theorem smallEtaleSheafFamilyDescentFunctor_unit_general (B : BigEtaleSite.{u})
    {X Y : B.Scheme} (f : X ⟶ Y) :
    smallEtaleSheafFamilyDescentFunctorGeneral B (fun _ : Unit ↦ f) =
      smallEtaleSheafDescentFunctorGeneral B f := rfl

/-- The family descent functor is an equivalence exactly when the canonical descent functor of
the small étale sheaf pseudofunctor is. -/
public theorem isEquivalence_smallEtaleSheafFamilyDescentFunctor_iff (B : BigEtaleSite.{u})
    {I : Type t} {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y) :
    (smallEtaleSheafFamilyDescentFunctorGeneral B f).IsEquivalence ↔
      ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData f).IsEquivalence := by
  have :
      (eqToHom ((smallEtaleSheafPullbackSystemGeneral B).fiber Y).symm).toFunctor.IsEquivalence :=
    (Cat.equivOfIso
      (eqToIso ((smallEtaleSheafPullbackSystemGeneral B).fiber Y).symm)).isEquivalence_functor
  constructor
  · intro h
    dsimp only [smallEtaleSheafFamilyDescentFunctorGeneral] at h
    exact Functor.isEquivalence_of_comp_left
      (eqToHom ((smallEtaleSheafPullbackSystemGeneral B).fiber Y).symm).toFunctor _
  · intro h
    dsimp only [smallEtaleSheafFamilyDescentFunctorGeneral]
    infer_instance

/-- **Effective descent for small étale sheaves along a family with sections Zariski locally.**
Descent is effective along a family `h i : X i ⟶ Z` of morphisms of a big étale site such that
each member of an open covering of `Z` admits a section of some member of the family.

This is the closing step 'using that the problem is local on `Y` we reduce to the case where we
have a section, which is Lemma 0GEY' of the source argument for [Stacks, Tag 0GF2]. It is
proved as
`AlgebraicGeometry.smallEtaleSheafFamilyDescentZariskiLocal`. -/
public abbrev SmallEtaleSheafFamilyDescentZariskiLocalGeneral (B : BigEtaleSite.{u}) (I : Type t) :
    Prop :=
  ∀ {X : I → B.Scheme} {Z : B.Scheme} (h : ∀ i, X i ⟶ Z) {K : Type u} (W : K → B.Scheme)
    (j : ∀ c, W c ⟶ Z),
    (∀ c, IsOpenImmersion (B.inclusion.map (j c))) →
    (∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c))) →
    (∀ c, ∃ i, ∃ s : W c ⟶ X i, s ≫ h i = j c) →
    (smallEtaleSheafFamilyDescentFunctorGeneral B h).IsEquivalence


/-- **Effective descent for small étale sheaves along a family with sections Zariski locally on
its target.** Small étale sheaves form a stack for the étale, hence for the Zariski, topology
(`AlgebraicGeometry.smallEtaleSheafPullbackSystem_isStack`), so descent along a family is
effective as soon as each member of an open covering of its target admits a section of some
member of the family. -/
public theorem smallEtaleSheafFamilyDescentZariskiLocal (B : BigEtaleSite.{u}) (I : Type t) :
    SmallEtaleSheafFamilyDescentZariskiLocalGeneral B I := by
  intro X Z h K W j hopen hcover hsec
  have hét : ∀ c, Etale (B.inclusion.map (j c)) := fun c => by
    have := hopen c
    infer_instance
  exact (isEquivalence_smallEtaleSheafFamilyDescentFunctor_iff B h).2
    (isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_etale_sections B h W j hét
      hcover hsec)

/-- The first dévissage input, for a family. If each member `W c` of an open covering of `Z`
maps to `Y` through some member `f i : X i ⟶ Y` of the family over `g : Z ⟶ Y`, then the
projection `X i ×_Y Z ⟶ Z` admits a section over `W c` for that member, so descent of small
étale sheaves along the base-changed family is effective. -/
public theorem
    smallEtaleSheafFamilyDescentFunctor_isEquivalence_pullback_snd_of_sections_unconditional
    (B : BigEtaleSite.{u}) {I : Type t} {X : I → B.Scheme} {Y Z : B.Scheme} (f : ∀ i, X i ⟶ Y)
    (g : Z ⟶ Y) {K : Type u}
    {W : K → B.Scheme} (j : ∀ c, W c ⟶ Z)
    (hopen : ∀ c, IsOpenImmersion (B.inclusion.map (j c)))
    (hcover : ∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c)))
    (hfac : ∀ c, ∃ i, ∃ t : W c ⟶ X i, j c ≫ g = t ≫ f i) :
    (smallEtaleSheafFamilyDescentFunctorGeneral B (fun i ↦ pullback.snd (f i) g)).IsEquivalence :=
  smallEtaleSheafFamilyDescentZariskiLocal B I (fun i ↦ pullback.snd (f i) g) W j hopen hcover
    fun c => by
      obtain ⟨i, t, ht⟩ := hfac c
      exact ⟨i, pullback.lift t (j c) ht.symm, pullback.lift_snd _ _ _⟩

/-- The second dévissage input, for a family. If each member `W c` of an open covering of `Z`
maps to `Y` through some member `f i : X i ⟶ Y` of the family over `g : Z ⟶ Y`, then the
projection `X i ×_Y (Z ×_Y Z) ⟶ Z ×_Y Z` admits a section over the preimage of `W c` under the
first projection of `Z ×_Y Z` for that member, and those preimages are an open covering, so
descent of small étale sheaves along the base-changed family is effective. -/
public theorem
  smallEtaleSheafFamilyDescentFunctor_isEquivalence_pullback_snd_fst_comp_of_sections_unconditional
    (B : BigEtaleSite.{u}) {I : Type t} {X : I → B.Scheme} {Y Z : B.Scheme} (f : ∀ i, X i ⟶ Y)
    (g : Z ⟶ Y) {K : Type u}
    {W : K → B.Scheme} (j : ∀ c, W c ⟶ Z)
    (hopen : ∀ c, IsOpenImmersion (B.inclusion.map (j c)))
    (hcover : ∀ z, ∃ c, z ∈ Set.range (B.inclusion.map (j c)))
    (hfac : ∀ c, ∃ i, ∃ t : W c ⟶ X i, j c ≫ g = t ≫ f i) :
    (smallEtaleSheafFamilyDescentFunctorGeneral B
      (fun i ↦ pullback.snd (f i) (pullback.fst g g ≫ g))).IsEquivalence := by
  refine smallEtaleSheafFamilyDescentZariskiLocal B I
    (fun i ↦ pullback.snd (f i) (pullback.fst g g ≫ g))
    (fun c => pullback (j c) (pullback.fst g g))
    (fun c => pullback.snd (j c) (pullback.fst g g)) (fun c => ?_) (fun v => ?_) (fun c => ?_)
  · have := preservesPullbacks_bigEtaleSiteInclusion B
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (B.inclusion.map_isPullback (IsPullback.of_hasPullback (j c) (pullback.fst g g)))
      (hopen c)
  · exact exists_mem_range_inclusion_map_pullback_snd_general B j (pullback.fst g g) hcover v
  · obtain ⟨i, t, ht⟩ := hfac c
    refine ⟨i, pullback.lift (pullback.fst (j c) (pullback.fst g g) ≫ t)
      (pullback.snd (j c) (pullback.fst g g)) ?_, pullback.lift_snd _ _ _⟩
    rw [Category.assoc, ← ht, ← Category.assoc, pullback.condition, Category.assoc]

/-- **The reduction of [Stacks, Tag 0GF3] to its two dévissage inputs.** Descent of small étale
sheaves is effective along a family of morphisms dominated, in the sense of
[Stacks, Tag 0CP0], by a surjective integral morphism whose source carries an open covering each
member of which factors through some member of the family, by the integral branch of
[Stacks, Tag 0GF1] for a family. -/
public theorem smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_finiteDomination_unconditional
    (B : BigEtaleSite.{u}) {I : Type t} {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y)
    (hdom : FamilyFiniteDominationBySections B f) :
    (smallEtaleSheafFamilyDescentFunctorGeneral B f).IsEquivalence := by
  obtain ⟨Z, g, hgsurj, hgint, K, W, j, hopen, hcover, hfac⟩ := hdom
  have := hgsurj
  have := hgint
  have h₂ :=
   smallEtaleSheafFamilyDescentFunctor_isEquivalence_pullback_snd_fst_comp_of_sections_unconditional
      B f g j hopen hcover hfac
  exact (isEquivalence_smallEtaleSheafFamilyDescentFunctor_iff B f).2
    (isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_surjective_integral B f g
      ((isEquivalence_smallEtaleSheafFamilyDescentFunctor_iff B _).1
        (smallEtaleSheafFamilyDescentFunctor_isEquivalence_pullback_snd_of_sections_unconditional B
          f g j hopen hcover hfac))
      ((isEquivalence_smallEtaleSheafFamilyDescentFunctor_iff B _).1 h₂))

/-- **Descent for small étale sheaves along an fppf covering of a quasi-compact quasi-separated
base.** Let `{f i : X i ⟶ Y}` be a family of morphisms of a big étale site whose underlying
family of morphisms of schemes is an fppf covering, and let `Y` be quasi-compact and
quasi-separated. Then the canonical functor from sheaves on the small étale site of `Y` to
descent data for small étale sheaves with respect to the covering is an equivalence of
categories.

This is the source's argument for [Stacks, Tag 0GF2], run for a family: [Stacks, Tag 0CP0] is
`AlgebraicGeometry.familyFiniteDominationBySections_of_compactSpace`, its two dévissage inputs
have sections Zariski locally, and the integral branch of [Stacks, Tag 0GF1] concludes. It is the
first step of [Stacks, Tag 0GF3] for an arbitrary base,
`smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering_unconditional`. -/
public theorem
    smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering_of_compactSpace_unconditional
    (B : BigEtaleSite.{u}) {I : Type t}
    {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y)
    [CompactSpace (B.inclusion.obj Y)] [QuasiSeparatedSpace (B.inclusion.obj Y)]
    (hf : Presieve.ofArrows (fun i ↦ B.inclusion.obj (X i)) (fun i ↦ B.inclusion.map (f i)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj Y)) :
    (smallEtaleSheafFamilyDescentFunctorGeneral B f).IsEquivalence :=
  smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_finiteDomination_unconditional B f
    (familyFiniteDominationBySections_of_compactSpace B f hf)

/-- The base change of a family of morphisms of a big étale site whose underlying family of
morphisms of schemes is an fppf covering is again such a family. -/
public theorem ofArrows_inclusion_map_pullback_snd_mem_fppfPrecoverage (B : BigEtaleSite.{u})
    {I : Type t} {X : I → B.Scheme} {Y T : B.Scheme} (f : ∀ i, X i ⟶ Y) (p : T ⟶ Y)
    (hf : Presieve.ofArrows (fun i ↦ B.inclusion.obj (X i)) (fun i ↦ B.inclusion.map (f i)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj Y)) :
    Presieve.ofArrows (fun i ↦ B.inclusion.obj (pullback (f i) p))
        (fun i ↦ B.inclusion.map (pullback.snd (f i) p)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T) := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  exact Precoverage.mem_coverings_of_isPullback _ hf (B.inclusion.map p) _
    (fun i ↦ B.inclusion.map (pullback.fst (f i) p))
    fun i ↦ (B.inclusion.map_isPullback (IsPullback.of_hasPullback (f i) p)).flip

/-- **Effective descent for small étale sheaves is local on the base.** Let `f i : X i ⟶ Y` be a
family of morphisms of a big étale site and let `g k : V k ⟶ Y` be an open covering of `Y`. If
descent of small étale sheaves is effective along the base change of `f` to each `V k`, to each
`V k ×_Y V l` and to each `V k ×_Y V l ×_Y V m`, then it is effective along `f`.

This is the step 'this we may check locally' of the source proof of [Stacks, Tag 0GF2]. Small
étale sheaves form a stack for the étale topology
(`AlgebraicGeometry.isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_etale`), so
descent is effective along the open covering and along each of its base changes, and the
categorical dévissage
`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_of_baseChange_unconditional` concludes;
the joint faithfulness it asks for over the triple overlaps is the faithfulness of descent along
the base change of `f` there. -/
public theorem isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_openCover
    (B : BigEtaleSite.{u}) {I : Type t} {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y)
    {K : Type*} {V : K → B.Scheme} (g : ∀ k, V k ⟶ Y)
    (hopen : ∀ k, IsOpenImmersion (B.inclusion.map (g k)))
    (hcover : ∀ y, ∃ k, y ∈ Set.range (B.inclusion.map (g k)))
    (hV : ∀ k, ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun i ↦ pullback.snd (f i) (g k))).IsEquivalence)
    (hVV : ∀ k l, ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun i ↦ pullback.snd (f i) (pullback.fst (g k) (g l) ≫ g k))).IsEquivalence)
    (hVVV : ∀ k l m, ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
      (fun i ↦ pullback.snd (f i) (Pseudofunctor.tripleProj₁ g k l m ≫ g k))).IsEquivalence) :
    ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData f).IsEquivalence := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  have hét : ∀ k, Etale (B.inclusion.map (g k)) := fun k ↦ by
    have := hopen k
    infer_instance
  refine Pseudofunctor.isEquivalence_toDescentData_of_baseChange_unconditional f g
    (isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_etale B Y g hcover)
    (fun T t ↦ ?_) hV (fun k l ↦ ?_) (fun k l m G G' x y h ↦ ?_)
  · have : ∀ k, Etale (B.inclusion.map (pullback.fst t (g k))) := fun k ↦
      inclusion_map_baseChange_of_isStableUnderBaseChange B @Etale (hét k) t
    have : ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
        (fun k ↦ pullback.fst t (g k))).IsEquivalence := by
      refine isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_etale B T _
        fun x ↦ ?_
      obtain ⟨k, w, hw⟩ := hcover (B.inclusion.map t x)
      have hpb := B.inclusion.map_isPullback (IsPullback.of_hasPullback t (g k))
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x w hw.symm
      refine ⟨k, hpb.isoPullback.inv z, ?_⟩
      rwa [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst]
    exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩
  · have := hVV k l
    exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩
  · have := hVVV k l m
    exact Pseudofunctor.eq_of_toDescentData_faithful _ h

/-- The data of the affine open covering of an object of a big étale site, inside the site: its
members are open subschemes of an object of the site, so they lie in the site by
Stacks 000R (3). -/
private theorem exists_affine_openCover (B : BigEtaleSite.{u}) (Y : B.Scheme) :
    ∃ (K : Type u) (V : K → B.Scheme) (g : ∀ k, V k ⟶ Y),
      (∀ k, IsAffine (B.inclusion.obj (V k))) ∧ (∀ k, IsOpenImmersion (B.inclusion.map (g k))) ∧
      ∀ y, ∃ k, y ∈ Set.range (B.inclusion.map (g k)) := by
  let 𝒰 := (B.inclusion.obj Y).affineCover
  refine ⟨𝒰.I₀, fun k ↦ B.obj (𝒰.X k) (Scheme.size_lt_of_isOpenImmersion (𝒰.f k) Y.property),
    fun k ↦ ObjectProperty.homMk (𝒰.f k), fun k ↦ (inferInstance : IsAffine (𝒰.X k)),
    fun k ↦ (inferInstance : IsOpenImmersion (𝒰.f k)), fun y ↦ ⟨𝒰.idx y, 𝒰.covers y⟩⟩

/-- A property stable under base change and composition which holds for all the pairwise
projections `V k ×_Y V l ⟶ V k` holds for the first projection of each triple overlap. -/
private theorem inclusion_map_tripleProj₁_of_forall_fst (B : BigEtaleSite.{u})
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {K : Type*} {V : K → B.Scheme} {Y : B.Scheme} (g : ∀ k, V k ⟶ Y)
    (h : ∀ k l, P (B.inclusion.map (pullback.fst (g k) (g l)))) (k l m : K) :
    P (B.inclusion.map (Pseudofunctor.tripleProj₁ g k l m)) := by
  rw [Pseudofunctor.tripleProj₁, Functor.map_comp]
  exact P.comp_mem _ _
    (inclusion_map_baseChange_of_isStableUnderBaseChange B P (h l m) (pullback.snd (g k) (g l)))
    (h k l)

/-- **Descent for small étale sheaves along an fppf covering of a quasi-separated base.** The
base is covered by affine opens `V k`; each `V k`, each `V k ×_Y V l` and each
`V k ×_Y V l ×_Y V m` is quasi-compact, because `Y` is quasi-separated, and quasi-separated, as
an open subscheme of the affine `V k`, so the quasi-compact quasi-separated case applies to the
base change of the covering to each of them, and descent is local on the base. -/
public theorem smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering_of_quasiSeparated
    (B : BigEtaleSite.{u}) {I : Type t}
    {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y)
    [QuasiSeparatedSpace (B.inclusion.obj Y)]
    (hf : Presieve.ofArrows (fun i ↦ B.inclusion.obj (X i)) (fun i ↦ B.inclusion.map (f i)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj Y)) :
    (smallEtaleSheafFamilyDescentFunctorGeneral B f).IsEquivalence := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  obtain ⟨K, V, g, haff, hopen, hcover⟩ := exists_affine_openCover B Y
  have hqc : ∀ k, QuasiCompact (B.inclusion.map (g k)) := fun k ↦ by
    have := haff k
    exact quasiCompact_of_compactSpace _
  have key : ∀ {T A : B.Scheme} (q : T ⟶ Y) (p : T ⟶ A), IsAffine (B.inclusion.obj A) →
      IsOpenImmersion (B.inclusion.map p) → QuasiCompact (B.inclusion.map p) →
      ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
        (fun i ↦ pullback.snd (f i) q)).IsEquivalence := by
    intro T A q p _ _ _
    have : CompactSpace (B.inclusion.obj T) :=
      QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map p)
    have : QuasiSeparatedSpace (B.inclusion.obj T) :=
      quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map p)
    exact (isEquivalence_smallEtaleSheafFamilyDescentFunctor_iff B _).1 <|
     smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering_of_compactSpace_unconditional
        B _ (ofArrows_inclusion_map_pullback_snd_mem_fppfPrecoverage B f q hf)
  have hfst : ∀ k l, IsOpenImmersion (B.inclusion.map (pullback.fst (g k) (g l))) ∧
      QuasiCompact (B.inclusion.map (pullback.fst (g k) (g l))) := fun k l ↦
    ⟨inclusion_map_baseChange_of_isStableUnderBaseChange B @IsOpenImmersion (hopen l) (g k),
      inclusion_map_baseChange_of_isStableUnderBaseChange B @QuasiCompact (hqc l) (g k)⟩
  refine (isEquivalence_smallEtaleSheafFamilyDescentFunctor_iff B f).2
    (isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_openCover B f g hopen hcover
      (fun k ↦ key (g k) (𝟙 _) (haff k) ?_ ?_) (fun k l ↦ key _ _ (haff k) (hfst k l).1
        (hfst k l).2) (fun k l m ↦ key _ (Pseudofunctor.tripleProj₁ g k l m) (haff k) ?_ ?_))
  · exact (inferInstance : IsOpenImmersion (𝟙 (B.inclusion.obj (V k))))
  · exact (inferInstance : QuasiCompact (𝟙 (B.inclusion.obj (V k))))
  · exact inclusion_map_tripleProj₁_of_forall_fst B @IsOpenImmersion g (fun k l ↦ (hfst k l).1)
      k l m
  · exact inclusion_map_tripleProj₁_of_forall_fst B @QuasiCompact g (fun k l ↦ (hfst k l).2)
      k l m

/-- **[Stacks, Tag 0GF3].** Let `{f i : X i ⟶ Y}` be a family of morphisms of a big étale site
whose underlying family of morphisms of schemes is an fppf covering. Then the canonical functor
from sheaves on the small étale site of `Y` to descent data for small étale sheaves with respect
to the covering is an equivalence of categories.

The base is covered by affine opens `V k`; each `V k ×_Y V l` and each `V k ×_Y V l ×_Y V m` is
an open subscheme of the affine `V k`, hence quasi-separated, so the quasi-separated case
`smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering_of_quasiSeparated`
applies to the base change of the covering to each of them, and descent is local on the base
(`AlgebraicGeometry.isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_openCover`).
The quasi-separated case is reduced in the same way to the quasi-compact quasi-separated case,
which is the source's argument for [Stacks, Tag 0GF2] run for a family: [Stacks, Tag 0CP0], the
integral branch of [Stacks, Tag 0GF1], and sections Zariski locally. The source instead applies
[Stacks, Tag 0GF2] to the single morphism `∐ X i ⟶ Y`; the family is treated directly here. -/
@[stacks 0GF3]
public theorem smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering_unconditional
    (B : BigEtaleSite.{u}) {I : Type t} {X : I → B.Scheme} {Y : B.Scheme} (f : ∀ i, X i ⟶ Y)
    (hf : Presieve.ofArrows (fun i ↦ B.inclusion.obj (X i)) (fun i ↦ B.inclusion.map (f i)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj Y)) :
    (smallEtaleSheafFamilyDescentFunctorGeneral B f).IsEquivalence := by
  have := preservesPullbacks_bigEtaleSiteInclusion B
  obtain ⟨K, V, g, haff, hopen, hcover⟩ := exists_affine_openCover B Y
  have key : ∀ {T A : B.Scheme} (q : T ⟶ Y) (p : T ⟶ A), IsAffine (B.inclusion.obj A) →
      IsOpenImmersion (B.inclusion.map p) →
      ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData
        (fun i ↦ pullback.snd (f i) q)).IsEquivalence := by
    intro T A q p _ _
    have : QuasiSeparatedSpace (B.inclusion.obj T) :=
      quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map p)
    exact (isEquivalence_smallEtaleSheafFamilyDescentFunctor_iff B _).1
      (smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering_of_quasiSeparated
        B _ (ofArrows_inclusion_map_pullback_snd_mem_fppfPrecoverage B f q hf))
  have hfst : ∀ k l, IsOpenImmersion (B.inclusion.map (pullback.fst (g k) (g l))) := fun k l ↦
    inclusion_map_baseChange_of_isStableUnderBaseChange B @IsOpenImmersion (hopen l) (g k)
  refine (isEquivalence_smallEtaleSheafFamilyDescentFunctor_iff B f).2
    (isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_openCover B f g hopen hcover
      (fun k ↦ key (g k) (𝟙 _) (haff k) ?_) (fun k l ↦ key _ _ (haff k) (hfst k l))
      (fun k l m ↦ key _ (Pseudofunctor.tripleProj₁ g k l m) (haff k) ?_))
  · exact (inferInstance : IsOpenImmersion (𝟙 (B.inclusion.obj (V k))))
  · exact inclusion_map_tripleProj₁_of_forall_fst B @IsOpenImmersion g hfst k l m

/-- **[Stacks, Tag 0GF2].** Let `f : X ⟶ Y` be a morphism of a big étale site which is
surjective, flat and locally of finite presentation. Then the canonical functor from sheaves on
the small étale site of `Y` to descent data for `{X ⟶ Y}` is an equivalence of categories.

This is [Stacks, Tag 0GF3] for the one-member fppf covering `{f}`,
`smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering_unconditional`, whose
proof is the source's proof of this lemma: the problem is local on `Y`, which reduces it to a
quasi-compact quasi-separated base; there [Stacks, Tag 0CP0] supplies a finite surjective
`Z ⟶ Y` with an open covering of `Z` factoring through `X`, the dévissage of [Stacks, Tag 0GF1]
replaces `Y` by `Z` and `Z ×_Y Z`, and over those `f` has sections Zariski locally, which is
[Stacks, Tag 0GEY] after localizing once more. -/
@[stacks 0GF2]
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_fppf_unconditional
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) [Surjective (B.inclusion.map f)]
    [Flat (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)] :
    (smallEtaleSheafDescentFunctorGeneral B f).IsEquivalence := by
  rw [← smallEtaleSheafFamilyDescentFunctor_unit_general]
  refine smallEtaleSheafFamilyDescentFunctor_isEquivalence_of_fppfCovering_unconditional B _ ?_
  rw [Presieve.ofArrows_pUnit]
  exact Scheme.Hom.singleton_mem_fppfPrecoverage (B.inclusion.map f)

end AlgebraicGeometry

end
