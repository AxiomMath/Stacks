module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal

/-!
# Quasi-coherent on the small crystalline site implies locally quasi-coherent

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` of a global
crystalline situation.  [Stacks, Tag 07IT] is stated for `𝒞 = CRIS(X/S)` and for
`𝒞 = Cris(X/S)` alike, and it characterises quasi-coherence of `F` by two conditions read on the
restrictions `F_T` to the ambient schemes of the objects `(U, T, δ)`: that each `F_T` is a
quasi-coherent `𝒪_T`-module, which is local quasi-coherence in the sense of [Stacks, Tag 07IS],
and that `F` is a crystal.  This file proves the first of those two conditions from
quasi-coherence on the *small* site, that is, the implication (1) ⇒ (2)(a) of the tag for
`𝒞 = Cris(X/S)`:

> quasi-coherent on `Cris(X/S)` implies locally quasi-coherent.

The same implication for `𝒞 = CRIS(X/S)` is
`Crystalline.GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentImpliesLocal`, and it is
not a substitute for the statement proved here: a sheaf of modules on `Cris(X/S)` is in general
not the restriction of one on `CRIS(X/S)`, so the small-site statement does not follow from the
big-site one, and the small site is where the chapter's later statements — [Stacks, Tag 07MP] and
[Stacks, Tag 07MQ] among them — read local quasi-coherence.

## What is reused and what is redone

The transport of a global presentation across two sites whose objects and morphisms lie in
unrelated universes is site-generic and is reused verbatim from the big-site file: the objects of
`Cris(X/S)` lie in `Type (u + 1)` and the opens of `T` in `Type u`, so carrying a presentation
along the restriction functor is again a *shrinking* of the index types, performed by
`Stacks.SheafOfModules.MixedObjectUniverse.hasGlobalPresentation_pushforward`.  The lattice
pullback of two opens, `Crystalline.GlobalCrystallineSituation.Thickening`
`.isLimitPullbackConeOpens`, is reused too, being a statement about the opens of the ambient
scheme alone.

What is redone is everything that mentions the site: the restriction functor
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.restrictOpenFunctor` lands
in `Cris(X/S)`, so its preservation of pullbacks, the continuity of its localisation and the
transport of a presentation along it are proved here for the small site.  Each is the big-site
argument at the underlying objects and morphisms of `CRIS(X/S)`, the inclusion
`Cris(X/S) ⥤ CRIS(X/S)` being fully faithful: a morphism of `Cris(X/S)` into a restriction is one
of `CRIS(X/S)` into the restriction of the underlying object, which is why the universal property
and the point-membership statements below are the big site's at `.hom`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.isLimitPullbackConeRestrictOpen` — the restrictions to the opens of the ambient scheme
  preserve pullbacks, hence `Crystalline.GlobalCrystallineSituation.SmallSite`
  `.CrystallineThickening.isContinuous_restrictOpenPostFunctor`: the localised restriction functor
  is continuous.
* `Crystalline.GlobalCrystallineSituation.SmallSite.exists_hasGlobalPresentation_restrictOpen` — a
  quasi-coherent sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` has a global presentation on the
  restriction of every object to a small enough open of its ambient scheme.
* `Crystalline.GlobalCrystallineSituation.SmallSite`
  `.hasGlobalPresentation_moduleRestrictionSheaf_over` — a global presentation of `F` on the
  localised site over `(U ∩ V, V, δ|_V)` restricts to one of `F_T` on the Zariski site localised
  at `V`.
* `Crystalline.GlobalCrystallineSituation.SmallSite`
  `.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`
  — **[Stacks, Tag 07IT] for `𝒞 = Cris(X/S)`, the implication (1) ⇒ (2)(a): a quasi-coherent sheaf
  of `𝒪_{X/S}`-modules on the small crystalline site is locally quasi-coherent.**

## Implementation notes

Continuity of the localised restriction functor is obtained from
`CategoryTheory.Functor.isContinuous_overPost_of_preservesPullbacks`, whose hypotheses are that
the opens of the ambient scheme have pullbacks — they are a complete lattice — and that the
restriction functor preserves them.  The latter is the statement that the restriction of an object
to `V ⊓ W` is the fibre product of its restrictions to `V` and to `W`, proved from the universal
property of a restriction,
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
`.exists_comp_restrictOpenHom_eq`, in the form of the big site's lift, and from the structure
morphism of a restriction being a monomorphism in `Cris(X/S)`.

The comparison of structure sheaves on the localised sites is again the identity, and this time
that is a statement about two sites: the structure sheaf of `Cris(X/S)` is the restriction along
the inclusion of that of `CRIS(X/S)`, and the restrictions of an object of `Cris(X/S)` to the
opens of its ambient scheme are those of the underlying object, so restricting the small-site
structure sheaf along the small-site restriction functor gives back the big site's
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf` at the underlying object
— which is the sheaf of rings over which local quasi-coherence on the small site is stated.

## The other half, and the converse

This is one of the two halves of the implication (1) ⇒ (2) of the tag, as on the big site.  The
other half, (1) ⇒ (2)(b) — that a quasi-coherent module is a crystal — is
`Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_of_isQuasicoherentOnSite` of
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentCrystal`.  The converse
implication (2) ⇒ (1) is a separate statement.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Crystalline.GlobalCrystallineSituation.SmallSite

universe u

variable {S : GlobalCrystallineSituation.{u}}

namespace CrystallineThickening

/-- **A morphism of `Cris(X/S)` whose map of ambient schemes has image inside an open of the
ambient scheme of its target factors through the restriction to that open.**  This is the
factorisation of the underlying morphism of `CRIS(X/S)`,
`Crystalline.GlobalCrystallineSituation.Thickening.liftRestrictOpen`, read in the full subcategory
`Cris(X/S)`. -/
noncomputable def liftRestrictOpen {A B : CrystallineThickening S} (r : B ⟶ A)
    (V : A.obj.thickening.target.scheme.Opens)
    (hr : ∀ x : B.obj.thickening.target.scheme, r.hom.targetHom.hom.base x ∈ V) :
    B ⟶ A.restrictOpen V :=
  ObjectProperty.homMk (Thickening.liftRestrictOpen r.hom V hr)

/-- The factorisation `liftRestrictOpen r V hr` composed with the restriction morphism
`A.restrictOpenHom V` is `r`. -/
@[reassoc]
theorem liftRestrictOpen_comp {A B : CrystallineThickening S} (r : B ⟶ A)
    (V : A.obj.thickening.target.scheme.Opens)
    (hr : ∀ x : B.obj.thickening.target.scheme, r.hom.targetHom.hom.base x ∈ V) :
    liftRestrictOpen r V hr ≫ A.restrictOpenHom V = r :=
  ObjectProperty.hom_ext _ (Thickening.liftRestrictOpen_comp r.hom V hr)

/-- **A morphism of `Cris(X/S)` factoring through a restriction has ambient image inside the open
in question.** -/
theorem targetHom_base_mem_of_comp_restrictOpenHom {A B : CrystallineThickening S}
    (V : A.obj.thickening.target.scheme.Opens) (k : B ⟶ A.restrictOpen V) (r : B ⟶ A)
    (hk : k ≫ A.restrictOpenHom V = r) (y : B.obj.thickening.target.scheme) :
    r.hom.targetHom.hom.base y ∈ V :=
  Thickening.targetHom_base_mem_of_comp_restrictOpenHom V k.hom r.hom
    (congrArg (fun m : B ⟶ A ↦ m.hom) hk) y

/-- **Cancelling the structure morphism of a restriction.**  Two factorisations of one morphism of
`Cris(X/S)` through the restrictions to nested opens are compatible with the morphism between
those restrictions. -/
theorem restrictOpenLE_comp_eq {A B : CrystallineThickening S}
    {V W : A.obj.thickening.target.scheme.Opens} (h : V ≤ W) (k : B ⟶ A.restrictOpen V)
    (r : B ⟶ A) (hk : k ≫ A.restrictOpenHom V = r) (f : B ⟶ A.restrictOpen W)
    (hf : f ≫ A.restrictOpenHom W = r) : k ≫ restrictOpenLE A h = f := by
  rw [← cancel_mono (A.restrictOpenHom W), Category.assoc, restrictOpenLE_restrictOpenHom]
  exact hk.trans hf.symm

section Pullbacks

variable (A : CrystallineThickening S) {V W Z : A.obj.thickening.target.scheme.Opens}

/-- The restriction functor sends the two inclusions of an intersection into a commuting square,
both composites being the restriction to the intersection of the two opens. -/
theorem restrictOpenFunctor_map_inf_comm (f : V ⟶ Z) (g : W ⟶ Z) :
    (restrictOpenFunctor A).map (homOfLE (inf_le_left : V ⊓ W ≤ V)) ≫
        (restrictOpenFunctor A).map f =
      (restrictOpenFunctor A).map (homOfLE (inf_le_right : V ⊓ W ≤ W)) ≫
        (restrictOpenFunctor A).map g := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- **The two legs of a cone on the restrictions to two opens agree after composition with the
structure morphisms.**  Both composites are the morphism to the object itself through the
restriction to the open containing both. -/
theorem comp_restrictOpenHom_eq_of_pullbackCone_condition (f : V ⟶ Z) (g : W ⟶ Z)
    (s : PullbackCone ((restrictOpenFunctor A).map f) ((restrictOpenFunctor A).map g)) :
    s.snd ≫ A.restrictOpenHom W = s.fst ≫ A.restrictOpenHom V := by
  have e : ∀ {V Z : A.obj.thickening.target.scheme.Opens} (f : V ⟶ Z),
      (restrictOpenFunctor A).map f ≫ A.restrictOpenHom Z = A.restrictOpenHom V :=
    fun f ↦ restrictOpenLE_restrictOpenHom A (leOfHom f)
  rw [← e f, ← e g]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ A.restrictOpenHom Z) s.condition.symm).trans (Category.assoc _ _ _))

/-- **The restriction of an object of `Cris(X/S)` to the intersection of two opens of its ambient
scheme is the fibre product of its restrictions to the two opens.**  A cone consists of two
morphisms whose composites with the structure morphisms agree, so their common value is a
morphism into the object itself whose ambient image lies in both opens; it therefore factors
uniquely through the restriction to the intersection, by
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.liftRestrictOpen` and the
fact that the structure morphism of a restriction is a monomorphism. -/
noncomputable def isLimitPullbackConeRestrictOpen (f : V ⟶ Z) (g : W ⟶ Z) :
    IsLimit (PullbackCone.mk ((restrictOpenFunctor A).map (homOfLE (inf_le_left : V ⊓ W ≤ V)))
      ((restrictOpenFunctor A).map (homOfLE (inf_le_right : V ⊓ W ≤ W)))
      (restrictOpenFunctor_map_inf_comm A f g)) := by
  refine PullbackCone.IsLimit.mk _
    (fun s ↦ liftRestrictOpen (s.fst ≫ A.restrictOpenHom V) (V ⊓ W) (fun y ↦
      ⟨targetHom_base_mem_of_comp_restrictOpenHom V s.fst _ rfl y,
        targetHom_base_mem_of_comp_restrictOpenHom W s.snd _
          (comp_restrictOpenHom_eq_of_pullbackCone_condition A f g s) y⟩))
    (fun s ↦ restrictOpenLE_comp_eq inf_le_left _ _ (liftRestrictOpen_comp _ _ _) s.fst rfl)
    (fun s ↦ restrictOpenLE_comp_eq inf_le_right _ _ (liftRestrictOpen_comp _ _ _) s.snd
      (comp_restrictOpenHom_eq_of_pullbackCone_condition A f g s))
    (fun s m h₁ _ ↦ ?_)
  refine (cancel_mono (A.restrictOpenHom (V ⊓ W))).1
    (Eq.trans ?_ (liftRestrictOpen_comp _ _ _).symm)
  have e : (restrictOpenFunctor A).map (homOfLE (inf_le_left : V ⊓ W ≤ V)) ≫
      A.restrictOpenHom V = A.restrictOpenHom (V ⊓ W) :=
    restrictOpenLE_restrictOpenHom A inf_le_left
  exact (congrArg (fun t ↦ m ≫ t) e.symm).trans
    ((Category.assoc m _ _).symm.trans
      (congrArg (fun t ↦ t ≫ A.restrictOpenHom V) h₁))

end Pullbacks

/-- **The restrictions to the opens of the ambient scheme preserve pullbacks.**  Every cospan of
opens is isomorphic to the cospan of its two legs, whose pullback is the intersection. -/
instance preservesLimitsOfShape_walkingCospan_restrictOpenFunctor (A : CrystallineThickening S) :
    PreservesLimitsOfShape WalkingCospan (restrictOpenFunctor A) := by
  constructor
  intro G
  have _ : PreservesLimit (cospan (G.map WalkingCospan.Hom.inl) (G.map WalkingCospan.Hom.inr))
      (restrictOpenFunctor A) :=
    preservesLimit_of_preserves_limit_cone (Thickening.isLimitPullbackConeOpens A.obj _ _)
      ((isLimitMapConePullbackConeEquiv _ _).symm (isLimitPullbackConeRestrictOpen A _ _))
  exact preservesLimit_of_iso_diagram _ (diagramIsoCospan G).symm

/-- **The localisation of the restriction functor** at an open `V` of the ambient scheme and at the
restriction of the object to `V`.  This is `Over.post` of
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.restrictOpenFunctor`, named
so that its codomain is the slice over the restriction of the object rather than the slice over
the image of `V` under the restriction functor; the two are the same category, but only the first
is the one the restricted structure sheaf and the restricted module are stated over. -/
noncomputable def restrictOpenPostFunctor (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens) :
    Over V ⥤ Over (A.restrictOpen V) :=
  Over.post (X := V) (restrictOpenFunctor A)

/-- **The localisation of the restriction functor is continuous.**  This is the half of
[Stacks, Tag 03CF] that the localisation of a morphism of sites needs, available here because the
opens of the ambient scheme have pullbacks and the restriction functor preserves them. -/
instance isContinuous_restrictOpenPostFunctor (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens) :
    (restrictOpenPostFunctor A V).IsContinuous
      ((Opens.grothendieckTopology A.obj.thickening.target.scheme).over V)
      ((smallTopology S).over (A.restrictOpen V)) :=
  haveI := restrictOpenFunctor_isContinuous A
  Functor.isContinuous_overPost_of_preservesPullbacks _ _ _ V

/-- **The localisation of the restriction functor is cocontinuous**, the restriction functor being
so. -/
instance isCocontinuous_restrictOpenPostFunctor (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens) :
    (restrictOpenPostFunctor A V).IsCocontinuous
      ((Opens.grothendieckTopology A.obj.thickening.target.scheme).over V)
      ((smallTopology S).over (A.restrictOpen V)) :=
  haveI := restrictOpenFunctor_isCocontinuous A
  inferInstanceAs ((Over.post (X := V) (restrictOpenFunctor A)).IsCocontinuous
    ((Opens.grothendieckTopology A.obj.thickening.target.scheme).over V)
    ((smallTopology S).over ((restrictOpenFunctor A).obj V)))

/-- **The comparison of structure sheaves on the localised sites is the identity.**  The structure
sheaf of `Cris(X/S)` is the restriction along the inclusion of that of `CRIS(X/S)`, and the
restrictions of an object of `Cris(X/S)` to the opens of its ambient scheme are those of the
underlying object, so restricting it along the small-site restriction functor is the big site's
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf` at the underlying object;
localising at an open `V` and at the restriction of the object to `V` turns that into the
restriction along the localised functor of the localisation of `𝒪_{X/S}`. -/
noncomputable def restrictOpenPostStructureHom (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens) :
    (Thickening.ringRestrictionSheaf A.obj).over V ⟶
      ((restrictOpenPostFunctor A V).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology A.obj.thickening.target.scheme).over V)
        ((smallTopology S).over (A.restrictOpen V))).obj
          ((structureSheaf S).over (A.restrictOpen V)) :=
  𝟙 _

/-- The comparison `restrictOpenPostStructureHom A V` of structure sheaves is an isomorphism. -/
instance isIso_restrictOpenPostStructureHom (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens) : IsIso (restrictOpenPostStructureHom A V) :=
  inferInstanceAs (IsIso (𝟙 ((Thickening.ringRestrictionSheaf A.obj).over V)))

/-- Restriction of sheaves of modules along the localisation of the restriction functor preserves
colimits of size `u + 1`, the universe in which a global presentation on the localised small
crystalline site is indexed.  The four sheafification hypotheses are discharged here, inside a
statement that mentions only the universe `u + 1`, rather than in the proof of
`Crystalline.GlobalCrystallineSituation.SmallSite`
`.hasGlobalPresentation_moduleRestrictionSheaf_over`: in that proof instances of the same two
classes at the module universe `u` are also in play, and two candidate instances at an unresolved
value universe make the universe constraints unsolvable. -/
theorem preservesColimitsOfSize_pushforward_restrictOpenPostStructureHom
    (A : CrystallineThickening S) (V : A.obj.thickening.target.scheme.Opens) :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (show SheafOfModules.{u + 1} ((structureSheaf S).over (A.restrictOpen V)) ⥤
          SheafOfModules.{u + 1} ((Thickening.ringRestrictionSheaf A.obj).over V) from
        SheafOfModules.pushforward.{u + 1} (restrictOpenPostStructureHom A V)) := by
  have _ : HasSheafify ((smallTopology S).over (A.restrictOpen V)) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have _ : ((smallTopology S).over (A.restrictOpen V)).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have _ : HasSheafify
      ((Opens.grothendieckTopology A.obj.thickening.target.scheme).over V)
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      ((Opens.grothendieckTopology A.obj.thickening.target.scheme).over V)
      AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _
  exact Stacks.SheafOfModules.pushforward_preservesColimits.{u, u, u + 1, u + 1, u, u}
    (restrictOpenPostFunctor A V) (restrictOpenPostStructureHom A V)

end CrystallineThickening

/-- **A global presentation of a sheaf of `𝒪_{X/S}`-modules on the localised small crystalline site
over the restriction of an object to an open of its ambient scheme restricts to a global
presentation of the restricted module on the Zariski site localised at that open.**

The restriction `F_T` is the pushforward of `F` along
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.restrictOpenFunctor`, and
both the restricted structure sheaf and the restricted module are, on the localised sites, the
pushforwards along `Over.post` of the restrictions of `𝒪_{X/S}` and of `F`; the comparison of
structure sheaves is therefore the identity, and the transport is
`Stacks.SheafOfModules.MixedObjectUniverse.hasGlobalPresentation_pushforward`, whose index
universes are allowed to differ. -/
theorem hasGlobalPresentation_moduleRestrictionSheaf_over
    (M : SheafOfModules.{u} (structureSheaf S)) (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens)
    (h : (M.over (A.restrictOpen V)).HasGlobalPresentation) :
    ((CohomologyRestriction.moduleRestrictionSheaf M A).over V).HasGlobalPresentation :=
  Stacks.SheafOfModules.MixedObjectUniverse.hasGlobalPresentation_pushforward.{u + 1,
    u, u, u, u, u} (G := CrystallineThickening.restrictOpenPostFunctor A V)
    (R := (structureSheaf S).over (A.restrictOpen V))
    (R' := (Thickening.ringRestrictionSheaf A.obj).over V)
    (CrystallineThickening.restrictOpenPostStructureHom A V) (M.over (A.restrictOpen V))
    (CrystallineThickening.preservesColimitsOfSize_pushforward_restrictOpenPostStructureHom A V) h

/-- **A quasi-coherent sheaf of `𝒪_{X/S}`-modules on the small crystalline site has a global
presentation on the restriction of every object to a small enough open of its ambient scheme.**
Quasi-coherence gives a covering family of the object; cocontinuity of the restrictions to the
opens of the ambient scheme refines it by a family of such restrictions, and a global presentation
travels along the refining morphism.  This is the small-site form of
`Crystalline.GlobalCrystallineSituation.exists_hasGlobalPresentation_restrictOpen`. -/
theorem exists_hasGlobalPresentation_restrictOpen
    (M : SheafOfModules.{u} (structureSheaf S)) (hM : M.IsQuasicoherentOnSite)
    (A : CrystallineThickening S) (x : A.obj.thickening.target.scheme) :
    ∃ V : A.obj.thickening.target.scheme.Opens,
      x ∈ V ∧ (M.over (A.restrictOpen V)).HasGlobalPresentation := by
  have := CrystallineThickening.restrictOpenFunctor_isCocontinuous A
  obtain ⟨I, Y, f, hcov, hY⟩ := hM.locally_hasGlobalPresentation A
  have hpb : (Sieve.ofArrows Y f).pullback (A.restrictOpenHom ⊤) ∈
      smallTopology S ((CrystallineThickening.restrictOpenFunctor A).obj ⊤) :=
    (smallTopology S).pullback_stable _ hcov
  obtain ⟨V, g, hg, hxV⟩ :=
    (CrystallineThickening.restrictOpenFunctor A).cover_lift
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) (smallTopology S) hpb x
      (Opens.mem_top x)
  have hfac : (CrystallineThickening.restrictOpenFunctor A).map g ≫ A.restrictOpenHom ⊤ =
      A.restrictOpenHom V :=
    CrystallineThickening.restrictOpenLE_restrictOpenHom A g.le
  have hV : (Sieve.ofArrows Y f).arrows (A.restrictOpenHom V) := by
    rwa [← hfac]
  obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff Y f _).1 hV
  exact ⟨V, hxV,
    Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap M a (hY i)⟩

/-- **Stacks Project, Tag 07IT for `𝒞 = Cris(X/S)`, the implication (1) ⇒ (2)(a): a quasi-coherent
sheaf of `𝒪_{X/S}`-modules on the small crystalline site is locally quasi-coherent.**

Quasi-coherence gives, around every point of the ambient scheme `T` of every object `(U, T, δ)` of
`Cris(X/S)`, an open `V` on whose restriction `(U ∩ V, V, δ|_V)` the module has a global
presentation (`Crystalline.GlobalCrystallineSituation.SmallSite`
`.exists_hasGlobalPresentation_restrictOpen`, which is cocontinuity of the restriction functor).
Intersecting `V` with a given open `W` of `T` makes those opens into an open cover of `W`, and each
presentation restricts to one of `F_T` on the Zariski site localised at `V ⊓ W` by
`Crystalline.GlobalCrystallineSituation.SmallSite`
`.hasGlobalPresentation_moduleRestrictionSheaf_over`; that is quasi-coherence of `F_T` over `W`.

This is one of the two halves of the implication (1) ⇒ (2) of the tag; the other half, that a
quasi-coherent module is a crystal, is
`Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_of_isQuasicoherentOnSite` of
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentCrystal`. -/
@[stacks 07IT "the implication (1) ⇒ (2)(a) on the small site Cris(X/S): quasi-coherent implies
  locally quasi-coherent.  The same implication on the big site CRIS(X/S), and the other half
  (1) ⇒ (2)(b) that a quasi-coherent module is a crystal, on each of the two sites, carry this tag
  separately.  The converse (2) ⇒ (1) is a separate statement"]
theorem isLocallyQuasiCoherent_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (structureSheaf S)) (hM : M.IsQuasicoherentOnSite) :
    IsLocallyQuasiCoherent M := by
  choose V hxV hV using exists_hasGlobalPresentation_restrictOpen M hM
  intro A
  refine ⟨(CohomologyRestriction.moduleRestrictionSheaf M A).isSheaf, ⟨fun W ↦ ?_⟩⟩
  exact ⟨↥W, fun i ↦ V A i.1 ⊓ W, fun _ ↦ homOfLE inf_le_right,
    fun x hx ↦ ⟨V A x ⊓ W, homOfLE inf_le_right,
      Sieve.ofArrows_mk (fun i : ↥W ↦ V A i.1 ⊓ W) (fun _ ↦ homOfLE inf_le_right) ⟨x, hx⟩,
      ⟨hxV A x, hx⟩⟩,
    fun i ↦ hasGlobalPresentation_moduleRestrictionSheaf_over M A _
      (Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap M
        (CrystallineThickening.restrictOpenLE A (inf_le_left : V A i.1 ⊓ W ≤ V A i.1)) (hV A i.1))⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
