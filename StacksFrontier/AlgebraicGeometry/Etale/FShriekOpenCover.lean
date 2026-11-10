module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenInclusionComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Etale.SupportTransport

/-!
# The proper-support direct image along a directed open covering

Let `f : X ⟶ Y` be a separated morphism locally of finite type in a big étale site and let `X`
be covered by a family of open subschemes `X i` which is directed: any two of them are
contained in a third. Writing `f i` for the restriction of `f` to `X i`, the canonical
extension-by-zero maps `(f i)_! (F|_{X i}) ⟶ f_! F` exhibit `f_! F` as the colimit of the
directed diagram of the proper-support direct images of the restrictions.

## Main definitions

* `AlgebraicGeometry.SmallEtale.properSupportOfOpen` and
  `AlgebraicGeometry.SmallEtale.properSupportOfOpenMap` — the proper-support direct image of
  the restriction of `F` to an open subscheme of `X`, and its canonical extension-by-zero map
  to `f_! F`.
* `AlgebraicGeometry.SmallEtale.properSupportOpenCoverDiagram` — the directed diagram of the
  proper-support direct images of the restrictions of `F` to the members of the covering.
* `AlgebraicGeometry.SmallEtale.properSupportOpenCoverCocone` — the cocone on it with vertex
  `f_! F` whose legs are the canonical extension-by-zero maps.
* `AlgebraicGeometry.SmallEtale.properSupportOpenCoverFunctorDiagram` and
  `AlgebraicGeometry.SmallEtale.properSupportOpenCoverFunctorCocone` — the same diagram and
  cocone as functors of the sheaf, with vertex the proper-support direct image functor.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_properSupportOpenCoverTransition` — the canonical map
  from a member of the covering factors through the canonical map of a larger member.
* `AlgebraicGeometry.SmallEtale.properSupportOpenCoverCocone_isColimit` — that cocone is a
  colimit cocone.
* `AlgebraicGeometry.SmallEtale.fShriek_isColimit_openCover` — the colimit statement at one
  sheaf: a diagram, a cocone with vertex `f_! F` whose legs are the canonical maps, and the
  assertion that it is a colimit.
* `AlgebraicGeometry.SmallEtale.properSupportFunctor_isColimit_openCover` — the statement of
  the source, functorially in the sheaf: the functor `f_!` is the colimit, in the category of
  functors, of the functors `F ↦ f_{i,!}(F|_{X_i})` along the canonical maps.

## Implementation notes

The transition maps of the diagram are not written down: for a nested pair of members of the
covering the canonical map factors through the larger one by the transitivity of extension by
zero, and the factorisation is unique because the legs are monomorphisms. That uniqueness is
what makes the diagram functorial, so the diagram is defined by choosing the factorisations
and proving the functor laws by cancelling a leg.

That the cocone is a colimit is proved sectionwise, not by a universal property: the
comparison map out of the colimit is a monomorphism because the index category is filtered and
the legs are monomorphisms, and it is locally surjective because a section of `f_! F` over an
étale test object `V` can locally be lifted to one of the stages. The local lifting is the
geometric heart of the argument. The support of such a section is a closed subscheme of `X_V`
proper over `V`, hence each of its fibres is quasi-compact; by directedness a quasi-compact
subset of the covering lies in a single member, and properness makes the projection a closed
map, so the containment persists over a Zariski open neighbourhood in `V`. Those
neighbourhoods, as `V` ranges over the points of the test object, form an étale covering of it
on which the section lifts.

Local bijectivity of a morphism of sheaves of abelian groups is an isomorphism; to apply this
at an index category which need not be small, the statement is transported along the
sheafification equivalence with a small model of the site.

## References

* [Stacks Project, Tag 0F54](https://stacks.math.columbia.edu/tag/0F54)
* [Stacks Project, Tag 0F53](https://stacks.math.columbia.edu/tag/0F53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w z

namespace AlgebraicGeometry.SmallEtale

section OpenRestriction

variable (B : BigEtaleSite.{u}) {T X : B.Scheme} (j : T ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)]

/-- Restriction of abelian sheaves along an open immersion `j`, compared with the direct image
along post-composition with `j`: both are left adjoint to the direct image along base change
along `j`. -/
private noncomputable def openRestrictionComparison :
    (smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B T.obj T.property) ≅
      (openPostcompose B j).sheafPushforwardContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B T.obj T.property)
        (SmallEtale.topology B X.obj X.property) :=
  Adjunction.leftAdjointUniq
    ((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B T.obj T.property))
    (Adjunction.sheafPushforwardContinuous (openPostcomposeAdjunction B j)
      (SmallEtale.topology B T.obj T.property)
      (SmallEtale.topology B X.obj X.property) (E := AddCommGrpCat.{v}))

/-- Under the comparison of the two descriptions of restriction, the unit of the base-change
adjunction becomes restriction along the counit of post-composition. -/
private theorem openRestrictionComparison_unit
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (W : SmallEtale B X.obj X.property) :
    (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B T.obj T.property)).unit.app F).hom.app (op W) ≫
      ((openRestrictionComparison.{u, v} B j).hom.app F).hom.app
        (op ((smallEtaleBaseChange B j).obj W)) =
      F.obj.map ((openPostcomposeAdjunction B j).counit.app W).op :=
  congrArg (fun a => a.hom.app (op W))
    (Adjunction.unit_leftAdjointUniq_hom_app
      ((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B T.obj T.property))
      (Adjunction.sheafPushforwardContinuous (openPostcomposeAdjunction B j)
        (SmallEtale.topology B T.obj T.property)
        (SmallEtale.topology B X.obj X.property) (E := AddCommGrpCat.{v})) F)

end OpenRestriction

section BaseChangeGeometry

variable (B : BigEtaleSite.{u})

/-- A base change of an open immersion of a big étale site is an open immersion. -/
private theorem isOpenImmersion_map_pullback_fst {T X W : B.Scheme}
    (a : W ⟶ X) (j : T ⟶ X) [IsOpenImmersion (B.inclusion.map j)] :
    haveI := hasPullbacks_bigEtaleSite B
    IsOpenImmersion (B.inclusion.map (pullback.fst a j)) := by
  have := hasPullbacks_bigEtaleSite B
  have := preservesPullbacks_bigEtaleSiteInclusion B
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback a j).map B.inclusion).flip
    (inferInstance : IsOpenImmersion (B.inclusion.map j))

/-- The image of a base change of a morphism of a big étale site is the inverse image of the
original image. -/
private theorem range_map_pullback_fst {T X W : B.Scheme} (a : W ⟶ X) (j : T ⟶ X) :
    haveI := hasPullbacks_bigEtaleSite B
    Set.range (B.inclusion.map (pullback.fst a j)).base =
      (B.inclusion.map a).base ⁻¹' Set.range (B.inclusion.map j).base := by
  have := hasPullbacks_bigEtaleSite B
  let c := pullbackComparison B.inclusion a j
  have hc : c ≫ pullback.fst (B.inclusion.map a) (B.inclusion.map j) =
      B.inclusion.map (pullback.fst a j) := pullbackComparison_comp_fst _ _ _
  have hc' : inv c ≫ B.inclusion.map (pullback.fst a j) =
      pullback.fst (B.inclusion.map a) (B.inclusion.map j) := by
    rw [← hc, IsIso.inv_hom_id_assoc]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(B.inclusion.map (pullback.snd a j)).base z, ?_⟩
    simpa only [Functor.map_comp, Scheme.Hom.comp_apply] using (congrArg (fun k => k z)
      (congrArg B.inclusion.map (pullback.condition (f := a) (g := j)))).symm
  · rintro ⟨z, hz⟩
    obtain ⟨t, ht, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := B.inclusion.map a) (g := B.inclusion.map j) x z hz.symm
    exact ⟨(inv c).base t, (congrArg (fun k => k t) hc').trans ht⟩

/-- The inverse image of a closed subset proper over the base along an open immersion is proper
over the base, provided the closed subset is contained in the image of the open immersion: the
inverse image is then isomorphic to the original closed subscheme. -/
public theorem isProperOver_preimage_of_subset_range
    {T T' V : Scheme.{u}} (q : T' ⟶ T) (p : T ⟶ V)
    [IsOpenImmersion q] [LocallyOfFiniteType p]
    (Z : Closeds T) (hZ : IsProperOver p Z)
    (hZq : (Z : Set T) ⊆ Set.range q.base) :
    IsProperOver (q ≫ p) (Z.preimage q.continuous) := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hI : I.support = Z := by
    ext x
    simp [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let i := I.subschemeι
  let j := pullback.snd q i
  have hjrange : j.opensRange = ⊤ := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.opensRange_pullbackSnd]
    ext z
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hz : i.base z ∈ I.support := by
      simpa [i] using (Set.mem_range_self z : I.subschemeι z ∈ Set.range I.subschemeι)
    rw [hI] at hz
    exact hZq hz
  have : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j hjrange
  have hcomap : IsProper ((I.comap q).subschemeι ≫ q ≫ p) := by
    have heq : (I.comap q).subschemeι ≫ q ≫ p = (I.comapIso q).hom ≫ j ≫ i ≫ p := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc]
    rw [heq]
    infer_instance
  refine (isProperOver_iff_exists_isProper (q ≫ p) (Z.preimage q.continuous)).2
    ⟨I.comap q, ?_, hcomap⟩
  rw [Scheme.IdealSheafData.support_comap]
  rfl

end BaseChangeGeometry

section Shrinking

/-- If the fibre of a closed map over a point is covered by a directed family of opens, then
one member of the family contains the preimage of a whole open neighbourhood of that point. -/
private theorem exists_stage_of_isClosedMap {α β ι : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [Nonempty ι] {p : α → β} (hp : IsClosedMap p) {y : β}
    (hcompact : IsCompact (p ⁻¹' {y})) (U : ι → Set α) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (hdirected : Directed (· ⊆ ·) U) :
    ∃ i V, IsOpen V ∧ y ∈ V ∧ ∀ x, p x ∈ V → x ∈ U i := by
  obtain ⟨i, hi⟩ := hcompact.elim_directed_cover U hopen
    (fun x _ => Set.mem_iUnion.2 (hcover x)) hdirected
  exact ⟨i, (p '' (U i)ᶜ)ᶜ, (hp _ (hopen i).isClosed_compl).isOpen_compl,
    fun ⟨x, hxQ, hpx⟩ => hxQ (hi hpx),
    fun x hxV => Classical.byContradiction fun hxUi => hxV ⟨x, hxUi, rfl⟩⟩

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})

/-- The ideal sheaf cutting out the reduced closed subscheme on the support of a section of the
direct image of `F` over an étale test object. -/
private abbrev supportIdeal (V : SmallEtale B Y.obj Y.property)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj V))) :
    ((SmallEtale.toScheme B X.obj X.property).obj
      ((smallEtaleBaseChange B f).obj V)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj V) s).compl

/-- A section with proper support has quasi-compact support over each point of the test object:
its support is proper over the test object, and a proper morphism has quasi-compact fibres. -/
private theorem isCompact_supportIdeal_fiber [LocallyOfFiniteType (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj V)))
    (hs : properSupportSections B f F V s)
    (y : (SmallEtale.toScheme B Y.obj Y.property).obj V) :
    haveI := hasPullbacks_bigEtaleSite B
    IsCompact (((supportIdeal B f F V s).subschemeι ≫
      B.inclusion.map (pullback.fst V.obj.hom f)).base ⁻¹' {y}) := by
  have := hasPullbacks_bigEtaleSite B
  have : IsProper ((supportIdeal B f F V s).subschemeι ≫
      B.inclusion.map (pullback.fst V.obj.hom f)) := hs
  exact Scheme.Hom.isCompact_preimage_singleton _ y

/-- For a section with proper support and a directed open covering of the source, the support
lying over a Zariski neighbourhood of a point of the test object is contained in a single
member of the covering: the fibre of the support over that point is quasi-compact, hence lies
in one member, and the projection of the support is a closed map. -/
private theorem exists_stage_near_supportIdeal [LocallyOfFiniteType (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj V)))
    (hs : properSupportSections B f F V s)
    {ι : Type w} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (U : ι ⥤ B.Scheme) (j : U ⟶ (Functor.const ι).obj X)
    (hopen : ∀ i, IsOpenImmersion (B.inclusion.map (j.app i)))
    (hcover : ∀ x : X.obj, ∃ i, x ∈ Set.range (B.inclusion.map (j.app i)).base)
    (y : (SmallEtale.toScheme B Y.obj Y.property).obj V) :
    haveI := hasPullbacks_bigEtaleSite B
    ∃ i : ι, ∃ W : ((SmallEtale.toScheme B Y.obj Y.property).obj V).Opens, y ∈ W ∧
      ∀ z : (supportIdeal B f F V s).subscheme,
        ((supportIdeal B f F V s).subschemeι ≫
            B.inclusion.map (pullback.fst V.obj.hom f)).base z ∈ W →
          ((supportIdeal B f F V s).subschemeι ≫
            B.inclusion.map (pullback.snd V.obj.hom f)).base z ∈
            Set.range (B.inclusion.map (j.app i)).base := by
  have := hasPullbacks_bigEtaleSite B
  set I := supportIdeal B f F V s
  let p := I.subschemeι ≫ B.inclusion.map (pullback.fst V.obj.hom f)
  let q := I.subschemeι ≫ B.inclusion.map (pullback.snd V.obj.hom f)
  have hproper : IsProper p := hs
  have hpclosed : IsClosedMap p.base := p.isProperMap.isClosedMap
  let stage : ι → Set I.subscheme := fun i =>
    q.base ⁻¹' Set.range (B.inclusion.map (j.app i)).base
  have hstageOpen : ∀ i, IsOpen (stage i) := fun i =>
    (hopen i).isOpen_range.preimage q.continuous
  have hstageCover : ∀ z, ∃ i, z ∈ stage i := fun z => hcover (q.base z)
  have hmono : ∀ {i k : ι}, i ≤ k →
      Set.range (B.inclusion.map (j.app i)).base ⊆
        Set.range (B.inclusion.map (j.app k)).base := by
    intro i k hik
    have hcomp : B.inclusion.map (U.map (homOfLE hik)) ≫ B.inclusion.map (j.app k) =
        B.inclusion.map (j.app i) := by
      rw [← B.inclusion.map_comp]
      refine congrArg B.inclusion.map ?_
      simp
    rintro x ⟨z, hz⟩
    refine ⟨(B.inclusion.map (U.map (homOfLE hik))).base z, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using (congrArg (fun m => m z) hcomp).trans hz
  have hdirected : Directed (· ⊆ ·) stage := by
    intro i k
    obtain ⟨l, hil, hkl⟩ := IsDirected.directed (r := (· ≤ ·)) i k
    exact ⟨l, Set.preimage_mono (hmono hil), Set.preimage_mono (hmono hkl)⟩
  obtain ⟨i, W, hWopen, hy, hstage⟩ := exists_stage_of_isClosedMap hpclosed
    (isCompact_supportIdeal_fiber B f F V s hs y) stage hstageOpen hstageCover hdirected
  exact ⟨i, ⟨W, hWopen⟩, hy, hstage⟩

end Shrinking

section SupportRestriction

variable (B : BigEtaleSite.{u}) {T X : B.Scheme} (j : T ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})

/-- The maximal zero open of a section of the direct image along post-composition with an open
immersion is the maximal zero open of that section upstairs: the two sides are suprema over the
same Zariski opens, since post-composition identifies the open immersions of the small étale
site of `T` over an object with those of the small étale site of `X` over its image. -/
private theorem zeroOpen_openPostcompose (U : SmallEtale B T.obj T.property)
    (s : F.obj.obj (op ((openPostcompose B j).obj U))) :
    zeroOpen B T.obj T.property
        (((openPostcompose B j).sheafPushforwardContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B T.obj T.property)
          (SmallEtale.topology B X.obj X.property)).obj F) U s =
      zeroOpen B X.obj X.property F ((openPostcompose B j).obj U) s := by
  apply le_antisymm
  · apply sSup_le
    rintro W ⟨V, a, ha, hr, hz⟩
    exact le_sSup ⟨(openPostcompose B j).obj V, (openPostcompose B j).map a, ha, hr, hz⟩
  · let W : ((SmallEtale.toScheme B T.obj T.property).obj U).Opens :=
      zeroOpen B X.obj X.property F ((openPostcompose B j).obj U) s
    let V := openObject B T.obj T.property U W
    let a := openObjectι B T.obj T.property U W
    have ha' : (SmallEtale.toScheme B X.obj X.property).map
        ((openPostcompose B j).map a) = W.ι := openObjectι_map B T.obj T.property U W
    have : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map
        ((openPostcompose B j).map a)) :=
      isOpenImmersion_openObjectι B T.obj T.property U W
    have hz : F.obj.map ((openPostcompose B j).map a).op s = 0 := by
      refine (map_eq_zero_iff_le_zeroOpen B X.obj X.property F ((openPostcompose B j).obj U) s
        ((openPostcompose B j).obj V) ((openPostcompose B j).map a)).2 fun x hx => ?_
      change x ∈ Set.range ((SmallEtale.toScheme B X.obj X.property).map
        ((openPostcompose B j).map a)).base at hx
      rw [ha'] at hx
      obtain ⟨z, rfl⟩ := hx
      exact z.property
    exact le_sSup ⟨V, a, isOpenImmersion_openObjectι B T.obj T.property U W,
      (openObjectι_range B T.obj T.property U W).symm, hz⟩

/-- The support of a section of the restriction of `F` to an open subscheme is the support of
the corresponding section of the direct image along post-composition. -/
private theorem supportSection_openRestriction (U : SmallEtale B T.obj T.property)
    (s : (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B T.obj T.property)).obj F).obj.obj (op U)) :
    supportSection B T.obj T.property
        (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B T.obj T.property)).obj F) U s =
      supportSection B X.obj X.property F ((openPostcompose B j).obj U)
        (((openRestrictionComparison.{u, v} B j).hom.app F).hom.app (op U) s) := by
  unfold supportSection
  rw [← zeroOpen_sheafIso B T.obj T.property ((openRestrictionComparison.{u, v} B j).app F) U s]
  exact congrArg (fun W : ((SmallEtale.toScheme B T.obj T.property).obj U).Opens => W.carrierᶜ)
    (zeroOpen_openPostcompose B j F U _)

/-- The support of the unit of the restriction adjunction applied to a section is the inverse
image of the support of that section, along the base change of the open immersion. -/
private theorem supportSection_unit_app (W : SmallEtale B X.obj X.property)
    (s : F.obj.obj (op W)) :
    haveI := hasPullbacks_bigEtaleSite B
    supportSection B T.obj T.property
        (((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B T.obj T.property)).obj F)
        ((smallEtaleBaseChange B j).obj W)
        ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B T.obj T.property)).unit.app F).hom.app (op W) s) =
      (B.inclusion.map (pullback.fst W.obj.hom j)).base ⁻¹'
        supportSection B X.obj X.property F W s := by
  have := hasPullbacks_bigEtaleSite B
  refine (supportSection_openRestriction B j F ((smallEtaleBaseChange B j).obj W) _).trans ?_
  have h := congrArg (fun a => a s) (openRestrictionComparison_unit.{u, v} B j F W)
  refine (congrArg (supportSection B X.obj X.property F
    ((openPostcompose B j).obj ((smallEtaleBaseChange B j).obj W))) h).trans ?_
  refine (supportSection_map B X.obj X.property F W _
    ((openPostcomposeAdjunction B j).counit.app W) s).trans ?_
  rw [openPostcomposeAdjunction_counit_toScheme]
  rfl

end SupportRestriction

section Factorization

/-- A property of morphisms of schemes stable under composition holds for the image under the
inclusion of a composite of morphisms of a big étale site if it holds for both factors. -/
private theorem map_comp_mem (B : BigEtaleSite.{u}) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition] {X Y Z : B.Scheme} (j : X ⟶ Y) (f : Y ⟶ Z)
    (hj : P (B.inclusion.map j)) (hf : P (B.inclusion.map f)) : P (B.inclusion.map (j ≫ f)) :=
  MorphismProperty.comp_mem P _ _ hj hf

/-- The first projection of the comparison of a two-step base change with the base change along
the composite is the first projection of the one-step base change. -/
private theorem baseChangeCompIso_inv_fst (B : BigEtaleSite.{u}) {T X Y : B.Scheme}
    (j : T ⟶ X) (f : X ⟶ Y) (V : SmallEtale B Y.obj Y.property) :
    haveI := hasPullbacks_bigEtaleSite B
    ((smallEtaleBaseChange_compIso B T X Y j f).val.inv.app V).hom.left ≫
        pullback.fst (pullback.snd V.obj.hom f) j ≫ pullback.fst V.obj.hom f =
      pullback.fst V.obj.hom (j ≫ f) := by
  have := hasPullbacks_bigEtaleSite B
  have he := (smallEtaleBaseChange_compIso B T X Y j f).property V
  have he' : ((smallEtaleBaseChange_compIso B T X Y j f).val.inv.app V).hom =
      (Over.pullbackComp j f).hom.app V.obj := by
    have hi : (SmallEtale.inclusion B T.obj T.property).mapIso
        ((smallEtaleBaseChange_compIso B T X Y j f).val.app V) =
          (Over.pullbackComp j f).symm.app V.obj := Iso.ext he
    exact congrArg Iso.inv hi
  rw [he']
  have h := conjugateEquiv_counit (Over.mapPullbackAdj (j ≫ f))
    ((Over.mapPullbackAdj j).comp (Over.mapPullbackAdj f))
    (Over.mapComp j f).inv V.obj
  simp [Over.pullbackComp]

/-- The canonical map from the proper-support direct image of a restriction to a smaller open
subscheme factors through the one for a larger open subscheme, by transitivity of extension by
zero. -/
private theorem exists_openInclusionShriekMap_factor (B : BigEtaleSite.{u})
    {X'' X' X Y : B.Scheme} (i : X'' ⟶ X') (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map i)] [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    letI : IsOpenImmersion (B.inclusion.map (i ≫ j)) :=
      map_comp_mem B @IsOpenImmersion i j inferInstance inferInstance
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) :=
      map_comp_mem B @LocallyOfFiniteType j f inferInstance inferInstance
    letI : LocallyOfFiniteType (B.inclusion.map ((i ≫ j) ≫ f)) :=
      map_comp_mem B @LocallyOfFiniteType (i ≫ j) f inferInstance inferInstance
    let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X'.obj X'.property)).obj F
    let Fd := ((smallEtaleBaseChange B (i ≫ j)).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X''.obj X''.property)).obj F
    ∃ α : (fShriekSubsheaf B ((i ≫ j) ≫ f) Fd).val.obj.left ⟶
        (fShriekSubsheaf B (j ≫ f) F').val.obj.left,
      α ≫ (openInclusionShriekMap B j f F).val =
        (openInclusionShriekMap B (i ≫ j) f F).val := by
  have : IsOpenImmersion (B.inclusion.map (i ≫ j)) :=
    map_comp_mem B @IsOpenImmersion i j inferInstance inferInstance
  have : IsSeparated (B.inclusion.map (j ≫ f)) :=
    map_comp_mem B @IsSeparated j f inferInstance inferInstance
  have : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) :=
    map_comp_mem B @LocallyOfFiniteType j f inferInstance inferInstance
  have : LocallyOfFiniteType (B.inclusion.map ((i ≫ j) ≫ f)) :=
    map_comp_mem B @LocallyOfFiniteType (i ≫ j) f inferInstance inferInstance
  let e := openInclusionShriekCompIso B i j f F
  let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B X'.obj X'.property)).obj F
  refine ⟨e.inv ≫ (openInclusionShriekMap B i (j ≫ f) F').val, ?_⟩
  calc e.inv ≫ (openInclusionShriekMap B i (j ≫ f) F').val ≫
        (openInclusionShriekMap B j f F).val
      = e.inv ≫ (e.hom ≫ (openInclusionShriekMap B (i ≫ j) f F).val) := by
        rw [← openInclusionShriekMap_comp B i j f F]
    _ = (openInclusionShriekMap B (i ≫ j) f F).val := by
        rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

end Factorization

section Lifting

/-- A monomorphism of sheaves of abelian groups is injective on sections. -/
private theorem injective_app_of_mono {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A A' : Sheaf J AddCommGrpCat.{z}} (g : A ⟶ A') [Mono g] (V : Cᵒᵖ) :
    Function.Injective (g.hom.app V) :=
  (AddCommGrpCat.mono_iff_injective _).1
    ((NatTrans.mono_iff_mono_app (f := g.hom)).1 ((sheafToPresheaf J _).map_mono g) V)

attribute [local implicit_reducible] smallEtaleBaseChange

/-- A section of `f_! F` over an étale test object whose support lies inside the base change of
an open subscheme `T ⊆ X` comes from a section of the proper-support direct image on `T`: the
support is proper over the test object and contained in the open, so its inverse image there is
again proper, and the resulting section of the restriction has proper support. -/
private theorem exists_openInclusionShriekMap_preimage (B : BigEtaleSite.{u})
    {T X Y : B.Scheme} (j : T ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion (B.inclusion.map j)]
    [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property)
    (s : (fShriekSubsheaf B f F).val.obj.left.obj.obj (op V))
    (hs : haveI := hasPullbacks_bigEtaleSite B
      supportSection B X.obj X.property F ((smallEtaleBaseChange B f).obj V)
          ((fShriekSubsheaf B f F).val.arrow.hom.app (op V) s) ⊆
        Set.range (B.inclusion.map
          (pullback.fst ((smallEtaleBaseChange B f).obj V).obj.hom j)).base) :
    letI : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) :=
      map_comp_mem B @LocallyOfFiniteType j f inferInstance inferInstance
    ∃ t, (openInclusionShriekMap B j f F).val.hom.app (op V) t = s := by
  have : LocallyOfFiniteType (B.inclusion.map (j ≫ f)) :=
    map_comp_mem B @LocallyOfFiniteType j f inferInstance inferInstance
  have hpb := hasPullbacks_bigEtaleSite B
  let G := (fShriekSubsheaf B f F).val
  let F' := ((smallEtaleBaseChange B j).sheafPullback AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B T.obj T.property)).obj F
  let G' := (fShriekSubsheaf B (j ≫ f) F').val
  let W := (smallEtaleBaseChange B f).obj V
  let W' := (smallEtaleBaseChange B j).obj W
  let V' := (smallEtaleBaseChange B (j ≫ f)).obj V
  let e := (smallEtaleBaseChange_compIso B T X Y j f).val.app V
  let η := ((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B T.obj T.property)).unit.app F
  let a := G.arrow.hom.app (op V) s
  let b := η.hom.app (op W) a
  let b' := F'.obj.map e.inv.op b
  let Z := (zeroOpen B X.obj X.property F W a).compl
  let Z' := (zeroOpen B T.obj T.property F' W' b).compl
  let Z'' := (zeroOpen B T.obj T.property F' V' b').compl
  let p := B.inclusion.map (pullback.fst V.obj.hom f)
  let q := B.inclusion.map (pullback.fst W.obj.hom j)
  let r := (SmallEtale.toScheme B T.obj T.property).map e.inv
  have hpType : LocallyOfFiniteType p := locallyOfFiniteType_baseChangeProjection B f V
  have hqOpen : IsOpenImmersion q := isOpenImmersion_map_pullback_fst B W.obj.hom j
  have hrOpen : IsOpenImmersion r := IsOpenImmersion.of_isIso r
  have hqpType : LocallyOfFiniteType (q ≫ p) :=
    MorphismProperty.comp_mem (W := @LocallyOfFiniteType) _ _ inferInstance hpType
  have hZ : IsProperOver p Z := ((fShriekSubsheaf B f F).property V a).1 ⟨s, rfl⟩
  have hZ' : Z' = Z.preimage q.continuous :=
    SetLike.coe_injective (supportSection_unit_app.{u, v} B j F W a)
  have hproper' : IsProperOver (q ≫ p) Z' := by
    rw [hZ']
    exact isProperOver_preimage_of_subset_range q p Z hZ hs
  have hZ'' : Z'' = Z'.preimage r.continuous :=
    SetLike.coe_injective (supportSection_map B T.obj T.property F' W' V' e.inv b)
  have hrange : (Z' : Set ((SmallEtale.toScheme B T.obj T.property).obj W')) ⊆
      Set.range r.base := fun z _ =>
    ⟨((SmallEtale.toScheme B T.obj T.property).map e.hom).base z,
      congrArg (fun k => k z) ((SmallEtale.toScheme B T.obj T.property).mapIso e).hom_inv_id⟩
  have hpcomp : r ≫ q ≫ p = B.inclusion.map (pullback.fst V.obj.hom (j ≫ f)) := by
    have h := congrArg B.inclusion.map (baseChangeCompIso_inv_fst B j f V)
    rwa [B.inclusion.map_comp, B.inclusion.map_comp] at h
  have hb' : properSupportSections B (j ≫ f) F' V b' := by
    have h := isProperOver_preimage_of_subset_range r (q ≫ p) Z' hproper' hrange
    unfold IsProperOver at h
    rwa [← hZ'', hpcomp] at h
  obtain ⟨t, ht⟩ := ((fShriekSubsheaf B (j ≫ f) F').property V b').2 hb'
  refine ⟨t, ?_⟩
  let α := (openInclusionShriekMap B j f F).val
  let a' := G.arrow.hom.app (op V) (α.hom.app (op V) t)
  obtain ⟨hres, hsupp⟩ := (openInclusionShriekMap B j f F).property.2 V t
  have hb : F'.obj.map e.hom.op (G'.arrow.hom.app (op V) t) = b := by
    rw [ht]
    exact congrArg (fun m => m b) (F'.obj.mapIso e.op).inv_hom_id
  have hη : η.hom.app (op W) a' = η.hom.app (op W) a := hres.symm.trans hb
  let k := (openPostcomposeAdjunction B j).counit.app W
  have hk : (SmallEtale.toScheme B X.obj X.property).map k = q :=
    openPostcomposeAdjunction_counit_toScheme B j W
  have hkOpen : IsOpenImmersion ((SmallEtale.toScheme B X.obj X.property).map k) :=
    hk ▸ hqOpen
  have hka : F.obj.map k.op a' = F.obj.map k.op a := by
    have h := congrArg
      (fun z => ((openRestrictionComparison.{u, v} B j).hom.app F).hom.app (op W') z) hη
    have hm := openRestrictionComparison_unit.{u, v} B j F W
    exact (congrArg (fun m => m a') hm).symm.trans (h.trans (congrArg (fun m => m a) hm))
  have ha' : supportSection B X.obj X.property F W a' ⊆
      Set.range ((SmallEtale.toScheme B X.obj X.property).map k).base := by
    rw [hsupp, hk]
    exact Set.image_subset_range _ _
  have heq : a' = a :=
    eq_of_map_eq_of_supportSection_subset B X.obj X.property F k a' a ha'
      (by rwa [hk]) hka
  exact injective_app_of_mono G.arrow (op V) heq

end Lifting

section Stages

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})

/-- The proper-support direct image along `q ≫ f` of the restriction of `F` to an open
subscheme `q : T ⟶ X`. -/
public noncomputable def properSupportOfOpen {T : B.Scheme} (q : T ⟶ X)
    (hqo : IsOpenImmersion (B.inclusion.map q))
    (hq : LocallyOfFiniteType (B.inclusion.map (q ≫ f))) :
    Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v} := by
  letI : IsOpenImmersion (B.inclusion.map q) := hqo
  letI : LocallyOfFiniteType (B.inclusion.map (q ≫ f)) := hq
  exact (fShriekSubsheaf B (q ≫ f)
    (((smallEtaleBaseChange B q).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B T.obj T.property)).obj F)).val.obj.left

/-- Equal open immersions give the same proper-support direct image of the restriction. -/
public theorem properSupportOfOpen_congr {T : B.Scheme} {q r : T ⟶ X} (e : q = r)
    (hqo : IsOpenImmersion (B.inclusion.map q)) (hro : IsOpenImmersion (B.inclusion.map r))
    (hq : LocallyOfFiniteType (B.inclusion.map (q ≫ f)))
    (hr : LocallyOfFiniteType (B.inclusion.map (r ≫ f))) :
    properSupportOfOpen B f F q hqo hq = properSupportOfOpen B f F r hro hr := by
  subst r
  rfl

variable [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]

/-- **Stacks 0F53.** The canonical extension-by-zero map from the proper-support direct image
of the restriction of `F` to an open subscheme. -/
public noncomputable def properSupportOfOpenMap {T : B.Scheme} (q : T ⟶ X)
    (hqo : IsOpenImmersion (B.inclusion.map q))
    (hq : LocallyOfFiniteType (B.inclusion.map (q ≫ f))) :
    properSupportOfOpen B f F q hqo hq ⟶ (fShriekSubsheaf B f F).val.obj.left := by
  letI : IsOpenImmersion (B.inclusion.map q) := hqo
  letI : LocallyOfFiniteType (B.inclusion.map (q ≫ f)) := hq
  exact (openInclusionShriekMap B q f F).val

/-- Equal open immersions give the same canonical extension-by-zero map. -/
public theorem properSupportOfOpenMap_congr {T : B.Scheme} {q r : T ⟶ X} (e : q = r)
    (hqo : IsOpenImmersion (B.inclusion.map q)) (hro : IsOpenImmersion (B.inclusion.map r))
    (hq : LocallyOfFiniteType (B.inclusion.map (q ≫ f)))
    (hr : LocallyOfFiniteType (B.inclusion.map (r ≫ f))) :
    eqToHom (properSupportOfOpen_congr B f F e hqo hro hq hr).symm ≫
        properSupportOfOpenMap B f F q hqo hq = properSupportOfOpenMap B f F r hro hr := by
  subst r
  rfl

variable {ι : Type w} [Preorder ι] (U : ι ⥤ B.Scheme) (j : U ⟶ (Functor.const ι).obj X)
  (hopen : ∀ i, IsOpenImmersion (B.inclusion.map (j.app i)))

/-- The proper-support direct image of the restriction of `F` to one member of the open
covering. -/
public noncomputable def properSupportOpenCoverStage (i : ι) :
    Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v} :=
  properSupportOfOpen B f F (j.app i) (hopen i) (by
    have := hopen i
    change LocallyOfFiniteType (B.inclusion.map (j.app i) ≫ B.inclusion.map f)
    infer_instance)

/-- The canonical extension-by-zero map from one member of the open covering. -/
public noncomputable def properSupportOpenCoverLeg (i : ι) :
    properSupportOpenCoverStage B f F U j hopen i ⟶ (fShriekSubsheaf B f F).val.obj.left :=
  properSupportOfOpenMap B f F (j.app i) (hopen i) (by
    have := hopen i
    change LocallyOfFiniteType (B.inclusion.map (j.app i) ≫ B.inclusion.map f)
    infer_instance)

/-- The canonical extension-by-zero map from a member of the covering is a monomorphism. -/
public theorem mono_properSupportOpenCoverLeg (i : ι) :
    Mono (properSupportOpenCoverLeg B f F U j hopen i) := by
  have hi := hopen i
  have hif : LocallyOfFiniteType (B.inclusion.map (j.app i ≫ f)) :=
    map_comp_mem B @LocallyOfFiniteType (j.app i) f inferInstance inferInstance
  exact (openInclusionShriekMap B (j.app i) f F).property.1

/-- For a nested pair of members of the covering the canonical map from the smaller one factors
through the larger one. -/
public theorem exists_properSupportOpenCoverTransition {i k : ι} (h : i ≤ k) :
    ∃ α : properSupportOpenCoverStage B f F U j hopen i ⟶
        properSupportOpenCoverStage B f F U j hopen k,
      α ≫ properSupportOpenCoverLeg B f F U j hopen k =
        properSupportOpenCoverLeg B f F U j hopen i := by
  let g := U.map (homOfLE h)
  have hik : g ≫ j.app k = j.app i := by simp [g]
  have hjk : IsOpenImmersion (B.inclusion.map (j.app k)) := hopen k
  have hgjk : IsOpenImmersion (B.inclusion.map (g ≫ j.app k)) := by
    rw [hik]
    exact hopen i
  have hgOpen : IsOpenImmersion (B.inclusion.map g) := by
    have : IsOpenImmersion (B.inclusion.map g ≫ B.inclusion.map (j.app k)) := by
      rwa [← B.inclusion.map_comp]
    exact IsOpenImmersion.of_comp (B.inclusion.map g) (B.inclusion.map (j.app k))
  obtain ⟨α, hα⟩ := exists_openInclusionShriekMap_factor B g (j.app k) f F
  have hq : LocallyOfFiniteType (B.inclusion.map ((g ≫ j.app k) ≫ f)) :=
    map_comp_mem B @LocallyOfFiniteType (g ≫ j.app k) f inferInstance inferInstance
  have hkf : LocallyOfFiniteType (B.inclusion.map (j.app k ≫ f)) :=
    map_comp_mem B @LocallyOfFiniteType (j.app k) f inferInstance inferInstance
  have hif : LocallyOfFiniteType (B.inclusion.map (j.app i ≫ f)) :=
    have := hopen i
    map_comp_mem B @LocallyOfFiniteType (j.app i) f inferInstance inferInstance
  have hα' : α ≫ properSupportOfOpenMap B f F (j.app k) hjk hkf =
      properSupportOfOpenMap B f F (g ≫ j.app k) hgjk hq := by
    simpa [properSupportOfOpenMap] using hα
  refine ⟨eqToHom (properSupportOfOpen_congr B f F hik hgjk (hopen i) hq hif).symm ≫ α, ?_⟩
  have hfirst : (eqToHom (properSupportOfOpen_congr B f F hik hgjk (hopen i) hq hif).symm ≫
        α) ≫ properSupportOpenCoverLeg B f F U j hopen k =
      eqToHom (properSupportOfOpen_congr B f F hik hgjk (hopen i) hq hif).symm ≫
        properSupportOfOpenMap B f F (g ≫ j.app k) hgjk hq := by
    change (eqToHom _ ≫ α) ≫ properSupportOfOpenMap B f F (j.app k) hjk hkf = _
    exact (Category.assoc _ _ _).trans (congrArg (fun m => eqToHom _ ≫ m) hα')
  refine hfirst.trans ?_
  simpa [properSupportOpenCoverLeg] using
    properSupportOfOpenMap_congr B f F hik hgjk (hopen i) hq hif

/-- Shrinking the test object to a Zariski open over which the support lies inside one member
of the covering puts the support of the restricted section inside the base change of that
member. -/
private theorem supportSection_subset_stage_of_shrink (B : BigEtaleSite.{u})
    {X Y T : B.Scheme} (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)] (j : T ⟶ X)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (V : SmallEtale B Y.obj Y.property)
    (s : (fShriekSubsheaf B f F).val.obj.left.obj.obj (op V))
    (O : ((SmallEtale.toScheme B Y.obj Y.property).obj V).Opens)
    (hO : haveI := hasPullbacks_bigEtaleSite B
      ∀ z : (supportIdeal B f F V
          ((fShriekSubsheaf B f F).val.arrow.hom.app (op V) s)).subscheme,
        ((supportIdeal B f F V
            ((fShriekSubsheaf B f F).val.arrow.hom.app (op V) s)).subschemeι ≫
          B.inclusion.map (pullback.fst V.obj.hom f)).base z ∈ O →
          ((supportIdeal B f F V
              ((fShriekSubsheaf B f F).val.arrow.hom.app (op V) s)).subschemeι ≫
            B.inclusion.map (pullback.snd V.obj.hom f)).base z ∈
            Set.range (B.inclusion.map j).base) :
    haveI := hasPullbacks_bigEtaleSite B
    supportSection B X.obj X.property F
        ((smallEtaleBaseChange B f).obj (openObject B Y.obj Y.property V O))
        ((fShriekSubsheaf B f F).val.arrow.hom.app
          (op (openObject B Y.obj Y.property V O))
          ((fShriekSubsheaf B f F).val.obj.left.obj.map
            (openObjectι B Y.obj Y.property V O).op s)) ⊆
      Set.range (B.inclusion.map (pullback.fst
        ((smallEtaleBaseChange B f).obj (openObject B Y.obj Y.property V O)).obj.hom j)).base := by
  have := hasPullbacks_bigEtaleSite B
  let G := (fShriekSubsheaf B f F).val
  let V' := openObject B Y.obj Y.property V O
  let a := openObjectι B Y.obj Y.property V O
  let b := (smallEtaleBaseChange B f).map a
  let t : F.obj.obj (op ((smallEtaleBaseChange B f).obj V)) := G.arrow.hom.app (op V) s
  have hn : G.arrow.hom.app (op V') (G.obj.left.obj.map a.op s) = F.obj.map b.op t :=
    NatTrans.naturality_apply G.arrow.hom a.op s
  rw [hn, supportSection_map, range_map_pullback_fst]
  intro x hx
  let I := supportIdeal B f F V t
  have hr : Set.range I.subschemeι.base =
      supportSection B X.obj X.property F ((smallEtaleBaseChange B f).obj V) t := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr] at hx
  obtain ⟨z, hz⟩ := hx
  have hb₁ : ((SmallEtale.toScheme B X.obj X.property).map b) ≫
      B.inclusion.map (pullback.fst V.obj.hom f) =
      B.inclusion.map (pullback.fst V'.obj.hom f) ≫
        (SmallEtale.toScheme B Y.obj Y.property).map a :=
    (isPullback_baseChange_projection B f a).w
  have hb₂ : ((SmallEtale.toScheme B X.obj X.property).map b) ≫
      B.inclusion.map (pullback.snd V.obj.hom f) =
      B.inclusion.map (pullback.snd V'.obj.hom f) := by
    have h := congrArg B.inclusion.map (Over.w ((Over.pullback f).map a.hom))
    rwa [B.inclusion.map_comp] at h
  have hzO : (I.subschemeι ≫ B.inclusion.map (pullback.fst V.obj.hom f)).base z ∈ O := by
    change (B.inclusion.map (pullback.fst V.obj.hom f)).base (I.subschemeι.base z) ∈ O
    rw [hz]
    have heq := congrArg (fun k => k x) hb₁
    rw [openObjectι_map] at heq
    simp only [Scheme.Hom.comp_apply] at heq
    exact heq.symm ▸ ((B.inclusion.map (pullback.fst V'.obj.hom f)).base x).property
  have hzj := hO z hzO
  have heq := congrArg (fun k => k x) hb₂
  change (B.inclusion.map (pullback.snd V.obj.hom f)).base (I.subschemeι.base z) ∈ _ at hzj
  rw [hz] at hzj
  have hmem : (B.inclusion.map (pullback.snd V'.obj.hom f)).base x ∈
      Set.range (B.inclusion.map j).base := heq ▸ hzj
  exact hmem

/-- The directed diagram of the proper-support direct images of the restrictions of `F` to the
members of the covering. Its transition maps are the unique factorisations of the canonical
maps through one another. -/
public noncomputable def properSupportOpenCoverDiagram :
    ι ⥤ Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v} where
  obj i := properSupportOpenCoverStage B f F U j hopen i
  map {i k} h := Classical.choose
    (exists_properSupportOpenCoverTransition B f F U j hopen (leOfHom h))
  map_id i := by
    have : Mono (properSupportOpenCoverLeg B f F U j hopen i) :=
      mono_properSupportOpenCoverLeg B f F U j hopen i
    apply (cancel_mono (properSupportOpenCoverLeg B f F U j hopen i)).1
    rw [Category.id_comp]
    exact Classical.choose_spec
      (exists_properSupportOpenCoverTransition B f F U j hopen (leOfHom (𝟙 i)))
  map_comp {i k l} g h := by
    have : Mono (properSupportOpenCoverLeg B f F U j hopen l) :=
      mono_properSupportOpenCoverLeg B f F U j hopen l
    apply (cancel_mono (properSupportOpenCoverLeg B f F U j hopen l)).1
    have h₁ := Classical.choose_spec
      (exists_properSupportOpenCoverTransition B f F U j hopen (leOfHom g))
    have h₂ := Classical.choose_spec
      (exists_properSupportOpenCoverTransition B f F U j hopen (leOfHom h))
    have h₃ := Classical.choose_spec
      (exists_properSupportOpenCoverTransition B f F U j hopen (leOfHom (g ≫ h)))
    exact h₃.trans (h₁.symm.trans ((congrArg _ h₂.symm).trans (Category.assoc _ _ _).symm))

/-- The cocone on the directed diagram with vertex `f_! F`, whose legs are the canonical
extension-by-zero maps of the members of the covering. -/
public noncomputable def properSupportOpenCoverCocone :
    Cocone (properSupportOpenCoverDiagram B f F U j hopen) where
  pt := (fShriekSubsheaf B f F).val.obj.left
  ι := { app := properSupportOpenCoverLeg B f F U j hopen
         naturality := fun {_ _} h => Classical.choose_spec
           (exists_properSupportOpenCoverTransition B f F U j hopen (leOfHom h)) }

end Stages

section Colimit

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})

/-- Every section of `f_! F` over an étale test object is, after an étale covering of that
object, the image of a section from one member of the open covering. -/
private theorem exists_locally_properSupportOpenCoverLeg_preimage
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (U : ι ⥤ B.Scheme) (j : U ⟶ (Functor.const ι).obj X)
    (hopen : ∀ i, IsOpenImmersion (B.inclusion.map (j.app i)))
    (hcover : ∀ x : X.obj, ∃ i, x ∈ Set.range (B.inclusion.map (j.app i)).base)
    (V : SmallEtale B Y.obj Y.property)
    (s : (fShriekSubsheaf B f F).val.obj.left.obj.obj (op V)) :
    ∃ R : Sieve V, R ∈ SmallEtale.topology B Y.obj Y.property V ∧
      ∀ ⦃W⦄ (a : W ⟶ V), R a → ∃ i t,
        (properSupportOpenCoverLeg B f F U j hopen i).hom.app (op W) t =
          (fShriekSubsheaf B f F).val.obj.left.obj.map a.op s := by
  classical
  let G := (fShriekSubsheaf B f F).val
  let t : F.obj.obj (op ((smallEtaleBaseChange B f).obj V)) := G.arrow.hom.app (op V) s
  have ht : properSupportSections B f F V t :=
    ((fShriekSubsheaf B f F).property V t).1 ⟨s, rfl⟩
  choose idx O hy hO using exists_stage_near_supportIdeal B f F V t ht U j hopen hcover
  refine ⟨Sieve.ofArrows
    (fun y : (SmallEtale.toScheme B Y.obj Y.property).obj V =>
      openObject B Y.obj Y.property V (O y))
    (fun y => openObjectι B Y.obj Y.property V (O y)), ?_, ?_⟩
  · refine Stacks.EtaleCohomology.ofArrows_mem_topology B Y.property _ _ fun y => ⟨y, ?_⟩
    rw [openObjectι_range B Y.obj Y.property V (O y)]
    exact hy y
  · intro W a ha
    obtain ⟨y, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ a).1 ha
    have hji : IsOpenImmersion (B.inclusion.map (j.app (idx y))) := hopen (idx y)
    obtain ⟨q, hq⟩ := exists_openInclusionShriekMap_preimage B (j.app (idx y)) f F
      (openObject B Y.obj Y.property V (O y))
      (G.obj.left.obj.map (openObjectι B Y.obj Y.property V (O y)).op s)
      (supportSection_subset_stage_of_shrink B f (j.app (idx y)) F V s (O y) (hO y))
    refine ⟨idx y,
      (properSupportOpenCoverStage B f F U j hopen (idx y)).obj.map b.op q, ?_⟩
    have hn := NatTrans.naturality_apply
      (properSupportOpenCoverLeg B f F U j hopen (idx y)).hom b.op q
    change _ = G.obj.left.obj.map (b ≫ openObjectι B Y.obj Y.property V (O y)).op s
    change (properSupportOpenCoverLeg B f F U j hopen (idx y)).hom.app
      (op (openObject B Y.obj Y.property V (O y))) q = _ at hq
    rw [hn, hq]
    exact (congrArg (fun k => k s) (G.obj.left.obj.map_comp
      (openObjectι B Y.obj Y.property V (O y)).op b.op)).symm

end Colimit

section Vanishing

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})

/-- On a source with no points, every section of the proper-support direct image vanishes. -/
private theorem fShriekSubsheaf_eq_zero_of_isEmpty [IsEmpty X.obj]
    (V : SmallEtale B Y.obj Y.property)
    (s : (fShriekSubsheaf B f F).val.obj.left.obj.obj (op V)) : s = 0 := by
  let G := (fShriekSubsheaf B f F).val
  let W := (smallEtaleBaseChange B f).obj V
  let t : F.obj.obj (op W) := G.arrow.hom.app (op V) s
  have ht : F.obj.map (𝟙 W).op t = 0 :=
    (map_eq_zero_iff_le_zeroOpen B X.obj X.property F W t W (𝟙 W)).2
      fun x _ => ((inferInstance : IsEmpty X.obj).false
        ((B.inclusion.map W.obj.hom).base x)).elim
  have ht' : t = 0 := by simpa using ht
  exact injective_app_of_mono G.arrow (op V) (ht'.trans (map_zero _).symm)

end Vanishing

section LocalColimit

/-- A cocone of sheaves of abelian groups with monomorphic legs over a filtered small index
category whose vertex is locally covered by the images of the legs is a colimit cocone: the
comparison map out of the colimit is locally bijective, hence an isomorphism. -/
private def isColimit_of_locally_lifting {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Sheaf J AddCommGrpCat.{z}) (c : Cocone D)
    [HasSheafify J AddCommGrpCat.{z}]
    [HasColimitsOfShape I AddCommGrpCat.{z}]
    [HasExactColimitsOfShape I AddCommGrpCat.{z}]
    (hm : ∀ i, Mono (c.ι.app i))
    (hl : ∀ V (s : c.pt.obj.obj (op V)), ∃ R : Sieve V, R ∈ J V ∧
      ∀ ⦃W⦄ (a : W ⟶ V), R a → ∃ i t,
        (c.ι.app i).hom.app (op W) t = c.pt.obj.map a.op s) : IsColimit c := by
  have : IsConnected I := IsFiltered.isConnected I
  let p := colimit.desc D c
  have : ∀ i, Mono (c.ι.app i) := hm
  have hmonoι : Mono c.ι := NatTrans.mono_of_mono_app c.ι
  have hmonop : Mono p := CategoryTheory.Limits.colim.map_mono' c.ι (colimit.isColimit D)
    (isColimitConstCocone I c.pt) p
    (fun i => (colimit.ι_desc c i).trans (Category.comp_id _).symm)
  have hsurj : Sheaf.IsLocallySurjective p := by
    refine ⟨fun {V} s => ?_⟩
    obtain ⟨R, hR, hlR⟩ := hl V s
    refine J.superset_covering (fun W a ha => ?_) hR
    obtain ⟨i, t, ht⟩ := hlR a ha
    exact ⟨(colimit.ι D i).hom.app (op W) t,
      (congrArg (fun k => k.hom.app (op W) t) (colimit.ι_desc c i)).trans ht⟩
  have hinj : Sheaf.IsLocallyInjective p :=
    Presheaf.isLocallyInjective_of_injective J p.hom (injective_app_of_mono p)
  have hiso : IsIso p := (Sheaf.isLocallyBijective_iff_isIso p).1 ⟨hinj, hsurj⟩
  exact IsColimit.ofIsoColimit (colimit.isColimit D)
    (Cocone.ext (asIso p) (fun i => colimit.ι_desc c i))

/-- Sheafification of abelian groups exists on a small site. -/
private theorem hasSheafify_small {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{u} :=
  inferInstance

/-- The same criterion without the size assumptions on the site and the coefficients: both are
removed by composing with the universe-lifting functor and by transporting the topology to a
small model of the site. -/
private def isColimit_of_locally_lifting_of_univLE {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Sheaf J AddCommGrpCat.{z}) (c : Cocone D)
    (hm : ∀ i, Mono (c.ι.app i))
    (hl : ∀ V (s : c.pt.obj.obj (op V)), ∃ R : Sieve V, R ∈ J V ∧
      ∀ ⦃W⦄ (a : W ⟶ V), R a → ∃ i t,
        (c.ι.app i).hom.app (op W) t = c.pt.obj.map a.op s) : IsColimit c := by
  let J' := (equivSmallModel.{max u v w z} C).inverse.inducedTopology J
  letI : HasSheafify J' AddCommGrpCat.{max u v w z} := hasSheafify_small J'
  letI : HasSheafify J AddCommGrpCat.{max u v w z} :=
    hasSheafifyEssentiallySmallSite.{v, max u v w z, u, (max u v w z) + 1, max u v w z} J _
  letI : AB5OfSize.{w, w} AddCommGrpCat.{max u v w z} :=
    AB5OfSize_of_univLE.{w, w, max u v w z, max u v w z} _
  letI : HasExactColimitsOfShape I AddCommGrpCat.{max u v w z} := AB5OfSize.ofShape I
  letI : PreservesLimitsOfSize.{v, max u v} AddCommGrpCat.uliftFunctor.{max u v w, z} :=
    AddCommGrpCat.uliftFunctor_preservesLimitsOfSize
  letI : J.HasSheafCompose AddCommGrpCat.uliftFunctor.{max u v w, z} :=
    hasSheafCompose_of_preservesLimitsOfSize J
  letI : ReflectsColimitsOfSize.{w, w}
      (sheafCompose J AddCommGrpCat.uliftFunctor.{max u v w, z}) :=
    fullyFaithful_reflectsColimits _
  refine isColimitOfReflects (sheafCompose J AddCommGrpCat.uliftFunctor.{max u v w, z}) ?_
  refine isColimit_of_locally_lifting (D ⋙ sheafCompose J AddCommGrpCat.uliftFunctor)
    ((sheafCompose J AddCommGrpCat.uliftFunctor).mapCocone c) ?_ ?_
  · intro i
    have hmi : Mono (c.ι.app i) := hm i
    refine Sheaf.mono_of_injective _ fun V a b h => ?_
    exact ULift.ext <| injective_app_of_mono (c.ι.app i) V (congrArg ULift.down h)
  · intro V s
    obtain ⟨R, hR, h⟩ := hl V s.down
    refine ⟨R, hR, fun W a ha => ?_⟩
    obtain ⟨i, t, ht⟩ := h a ha
    exact ⟨i, ULift.up t, congrArg ULift.up ht⟩

end LocalColimit

section IsColimit

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
  {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)]
  (U : ι ⥤ B.Scheme) (j : U ⟶ (Functor.const ι).obj X)
  (hopen : ∀ i, IsOpenImmersion (B.inclusion.map (j.app i)))

/-- The canonical extension-by-zero maps of a directed open covering exhibit
the proper-support direct image as the colimit of the proper-support direct images of the
restrictions. -/
public theorem properSupportOpenCoverCocone_isColimit
    (hcover : ∀ x : X.obj, ∃ i, x ∈ Set.range (B.inclusion.map (j.app i)).base) :
    Nonempty (IsColimit (properSupportOpenCoverCocone B f F U j hopen)) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    have : IsEmpty X.obj := ⟨fun x => isEmptyElim (hcover x).choose⟩
    refine ⟨{ desc := fun _ => 0, fac := fun _ i => isEmptyElim i, uniq := ?_ }⟩
    intro q m hm
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext s
    rw [fShriekSubsheaf_eq_zero_of_isEmpty B f F V.unop s]
    exact (map_zero _).trans (map_zero _).symm
  | inr hi =>
    have : IsFiltered ι := isFiltered_of_directed_le_nonempty ι
    exact ⟨isColimit_of_locally_lifting_of_univLE
      (properSupportOpenCoverDiagram B f F U j hopen)
      (properSupportOpenCoverCocone B f F U j hopen)
      (mono_properSupportOpenCoverLeg B f F U j hopen)
      (exists_locally_properSupportOpenCoverLeg_preimage B f F U j hopen hcover)⟩

/-- For a separated morphism locally of finite type and a directed open covering of its source,
the proper-support direct image of one abelian sheaf is the colimit of the proper-support direct
images of its restrictions to the members of the covering, along the canonical
extension-by-zero maps. The functoriality in the sheaf is
`properSupportFunctor_isColimit_openCover`. -/
public theorem fShriek_isColimit_openCover
    (hcover : ∀ x : X.obj, ∃ i, x ∈ Set.range (B.inclusion.map (j.app i)).base) :
    let G := (fShriekSubsheaf B f F).val.obj.left
    ∃ (D : ι ⥤ Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v})
      (c : Cocone D),
      ∃ (hpt : c.pt = G),
        (∀ i,
          let ji : U.obj i ⟶ X := j.app i
          letI : IsOpenImmersion (B.inclusion.map ji) := hopen i
          letI : LocallyOfFiniteType (B.inclusion.map (ji ≫ f)) := by
            change LocallyOfFiniteType (B.inclusion.map ji ≫ B.inclusion.map f)
            infer_instance
          let Fi := ((smallEtaleBaseChange B ji).sheafPullback
            AddCommGrpCat.{v} (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B (U.obj i).obj (U.obj i).property)).obj F
          let Gi := (fShriekSubsheaf B (ji ≫ f) Fi).val.obj.left
          ∃ (hi : D.obj i = Gi),
            c.ι.app i ≫ eqToHom hpt =
              eqToHom hi ≫ (openInclusionShriekMap B ji f F).val) ∧
        Nonempty (IsColimit c) :=
  ⟨properSupportOpenCoverDiagram B f F U j hopen,
    properSupportOpenCoverCocone B f F U j hopen, rfl, fun _ => ⟨rfl, rfl⟩,
    properSupportOpenCoverCocone_isColimit B f F U j hopen hcover⟩

end IsColimit

section Functorial

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  {ι : Type w} [Preorder ι] (U : ι ⥤ B.Scheme) (j : U ⟶ (Functor.const ι).obj X)
  (hopen : ∀ i, IsOpenImmersion (B.inclusion.map (j.app i)))

/-- The functor `F ↦ f_{i,!}(F|_{X_i})` attached to one member of the open covering: restriction
to `X_i` followed by the proper-support direct image along the restriction `f_i` of `f`. -/
public noncomputable def properSupportOpenCoverStageFunctor (i : ι) :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v} ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v} :=
  let ji : U.obj i ⟶ X := j.app i
  letI : IsOpenImmersion (B.inclusion.map ji) := hopen i
  letI : LocallyOfFiniteType (B.inclusion.map (ji ≫ f)) := by
    change LocallyOfFiniteType (B.inclusion.map ji ≫ B.inclusion.map f)
    infer_instance
  (smallEtaleBaseChange B ji).sheafPullback AddCommGrpCat.{v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (U.obj i).obj (U.obj i).property) ⋙
    properSupportFunctor B (ji ≫ f)

/-- The canonical extension-by-zero maps `f_{i,!}(F|_{X_i}) ⟶ f_! F` of one member of the
covering, as a natural transformation in `F`. -/
public noncomputable def properSupportOpenCoverLegNatTrans (i : ι) :
    properSupportOpenCoverStageFunctor B f U j hopen i ⟶ properSupportFunctor B f where
  app F := properSupportOpenCoverLeg B f F U j hopen i
  naturality F H φ := by
    have := hopen i
    exact openInclusionShriekMap_naturality B (j.app i) f F H φ

/-- The directed diagram of the functors `F ↦ f_{i,!}(F|_{X_i})`, whose transition maps are, at
every sheaf, the transition maps of `properSupportOpenCoverDiagram`. -/
public noncomputable def properSupportOpenCoverFunctorDiagram :
    ι ⥤ (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v} ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v}) where
  obj i := properSupportOpenCoverStageFunctor B f U j hopen i
  map {i k} h :=
    { app F := (properSupportOpenCoverDiagram B f F U j hopen).map h
      naturality F H φ := by
        have : Mono (properSupportOpenCoverLeg B f H U j hopen k) :=
          mono_properSupportOpenCoverLeg B f H U j hopen k
        apply (cancel_mono (properSupportOpenCoverLeg B f H U j hopen k)).1
        have e₁ : (properSupportOpenCoverDiagram B f F U j hopen).map h ≫
            properSupportOpenCoverLeg B f F U j hopen k =
              properSupportOpenCoverLeg B f F U j hopen i :=
          (properSupportOpenCoverCocone B f F U j hopen).w h
        have e₂ : (properSupportOpenCoverDiagram B f H U j hopen).map h ≫
            properSupportOpenCoverLeg B f H U j hopen k =
              properSupportOpenCoverLeg B f H U j hopen i :=
          (properSupportOpenCoverCocone B f H U j hopen).w h
        have nᵢ : (properSupportOpenCoverStageFunctor B f U j hopen i).map φ ≫
            properSupportOpenCoverLeg B f H U j hopen i =
              properSupportOpenCoverLeg B f F U j hopen i ≫ (properSupportFunctor B f).map φ :=
          (properSupportOpenCoverLegNatTrans B f U j hopen i).naturality φ
        have nₖ : (properSupportOpenCoverStageFunctor B f U j hopen k).map φ ≫
            properSupportOpenCoverLeg B f H U j hopen k =
              properSupportOpenCoverLeg B f F U j hopen k ≫ (properSupportFunctor B f).map φ :=
          (properSupportOpenCoverLegNatTrans B f U j hopen k).naturality φ
        exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans (nᵢ.trans
          ((congrArg (· ≫ (properSupportFunctor B f).map φ) e₁).symm.trans
            ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) nₖ).symm.trans
              (Category.assoc _ _ _).symm))))) }
  map_id i := NatTrans.ext (funext fun F =>
    (properSupportOpenCoverDiagram B f F U j hopen).map_id i)
  map_comp g h := NatTrans.ext (funext fun F =>
    (properSupportOpenCoverDiagram B f F U j hopen).map_comp g h)

/-- The cocone on the diagram of functors with vertex the proper-support direct image functor
`f_!`, whose legs are the canonical extension-by-zero maps. -/
public noncomputable def properSupportOpenCoverFunctorCocone :
    Cocone (properSupportOpenCoverFunctorDiagram B f U j hopen) where
  pt := properSupportFunctor B f
  ι :=
    { app := properSupportOpenCoverLegNatTrans B f U j hopen
      naturality := fun {_ _} h => NatTrans.ext (funext fun F =>
        ((properSupportOpenCoverCocone B f F U j hopen).w h).trans (Category.comp_id _).symm) }

/-- The cocone of functors is a colimit cocone: colimits in a functor category are computed at
every object, and at a sheaf `F` it is `properSupportOpenCoverCocone`. -/
public theorem properSupportOpenCoverFunctorCocone_isColimit [IsDirected ι (· ≤ ·)]
    (hcover : ∀ x : X.obj, ∃ i, x ∈ Set.range (B.inclusion.map (j.app i)).base) :
    Nonempty (IsColimit (properSupportOpenCoverFunctorCocone B f U j hopen)) :=
  ⟨evaluationJointlyReflectsColimits _ fun F =>
    (properSupportOpenCoverCocone_isColimit B f F U j hopen hcover).some⟩

/-- **Stacks 0F54.** Let `f : X ⟶ Y` be separated and locally of finite type, and let the
`X_i = U i` form an open covering of `X` that is directed: any two members lie in a third.
Writing `f_i` for the restriction of `f` to `X_i`, the proper-support direct image is the
colimit `f_! F = colim_i f_{i,!}(F|_{X_i})` functorially in the abelian sheaf `F`, along the
canonical extension-by-zero maps: there is a directed diagram of functors whose value at `i` is
`F ↦ f_{i,!}(F|_{X_i})` and a colimit cocone on it, in the category of functors from abelian
sheaves on `X` to abelian sheaves on `Y`, whose vertex is the functor `f_!` and whose legs are,
at every sheaf `F`, the canonical maps `f_{i,!}(F|_{X_i}) ⟶ f_! F`. -/
@[stacks 0F54]
public theorem properSupportFunctor_isColimit_openCover [IsDirected ι (· ≤ ·)]
    (hcover : ∀ x : X.obj, ∃ i, x ∈ Set.range (B.inclusion.map (j.app i)).base) :
    ∃ (D : ι ⥤ (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v} ⥤
        Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v}))
      (c : Cocone D) (hpt : c.pt = properSupportFunctor B f),
      (∀ i,
        let ji : U.obj i ⟶ X := j.app i
        letI : IsOpenImmersion (B.inclusion.map ji) := hopen i
        letI : LocallyOfFiniteType (B.inclusion.map (ji ≫ f)) := by
          change LocallyOfFiniteType (B.inclusion.map ji ≫ B.inclusion.map f)
          infer_instance
        let res := (smallEtaleBaseChange B ji).sheafPullback AddCommGrpCat.{v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (U.obj i).obj (U.obj i).property)
        ∃ (hi : D.obj i = res ⋙ properSupportFunctor B (ji ≫ f)),
          ∀ F, (c.ι.app i ≫ eqToHom hpt).app F =
            (eqToHom hi).app F ≫ (openInclusionShriekMap B ji f F).val) ∧
        Nonempty (IsColimit c) :=
  ⟨properSupportOpenCoverFunctorDiagram B f U j hopen,
    properSupportOpenCoverFunctorCocone B f U j hopen, rfl,
    fun _ => ⟨rfl, fun _ => rfl⟩,
    properSupportOpenCoverFunctorCocone_isColimit B f U j hopen hcover⟩

end Functorial

end AlgebraicGeometry.SmallEtale

end
