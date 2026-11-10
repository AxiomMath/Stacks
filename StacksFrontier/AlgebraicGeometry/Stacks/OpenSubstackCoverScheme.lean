module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceIsoClass
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackCover
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented

/-!
# An algebraic stack covered by open substacks which are schemes (Stacks 05WF)

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site `B`, and let `𝒳_i`,
`i ∈ I`, be open substacks of `𝒳` which cover `𝒳` and are each a scheme. Stacks 05WF says that
`𝒳` is then a scheme.

A category fibred in groupoids over the big fppf site of `S` *is a scheme* here when it is
equivalent, over that site, to the category of elements of the representable presheaf of an
object of the site — that is, when it is representable by an algebraic space (Stacks 04SV) whose
representing presheaf is representable. That is the conclusion proved below.

The source argues in two steps: `𝒳` is an algebraic space by Stacks 05WE, and an algebraic space
has a largest open subspace which is a scheme (Stacks 03JH), so the schematic locus of `𝒳`
contains each `𝒳_i` and is therefore all of `𝒳`. Both steps are carried out here. The first is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isOpenSubstackCover`. The second
uses Stacks 03JH,
`AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_of_forall_pullbackFst`: a morphism of presheaves whose
  every base change to a scheme-valued point of its target is an open immersion of algebraic
  spaces is an open immersion.
* `AlgebraicGeometry.Space.isRepresentable_of_forall_le_schematicLocus`: an algebraic space whose
  every section locally lies in the schematic locus is a scheme.
* `AlgebraicGeometry.Stack.isOpenImmersion_representingMap`: the bridge of Stacks 04XB at the
  open-immersion property — the morphism of representing presheaves induced by an open immersion
  of stacks representable by algebraic spaces is an open immersion of algebraic spaces.
* `AlgebraicGeometry.Stack.exists_equivalenceOver_yoneda_of_isOpenSubstackCover`:
  **Stacks 05WF**.

## Implementation notes

**The open-immersion bridge carries no locality hypothesis.** The general bridge of Stacks 04XB
for represented source and target,
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`, asks for the property to
be local on the target for the fppf precoverage, which at the open-immersion property is Stacks
041X and is not in the library. It is not needed: locality enters that bridge only through
`AlgebraicGeometry.Space.prop_homMk_of_forall_yoneda`, and *being an open immersion is by
definition* the test on scheme-valued points — `AlgebraicGeometry.Space.IsOpenImmersion` is
`CategoryTheory.MorphismProperty.presheaf` of the inverse image of
`AlgebraicGeometry.IsOpenImmersion`, so the scheme-valued test is passed by taking identity base
changes. That is `AlgebraicGeometry.Space.isOpenImmersion_of_forall_pullbackFst`, and with it the
P-free half of the bridge,
`AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullbackOfPullback`, suffices. So
`AlgebraicGeometry.Stack.isOpenImmersion_representingMap` holds outright rather than under
Stacks 041X.

**Why the index type is not restricted.** The case `(θ)` of Stacks 03KE,
`AlgebraicGeometry.Space.isRepresentable_of_isZariskiCover`, is the same statement for a family
of open subspaces of an algebraic space, but it is
stated for an index type at the universe of the site, because the coproduct of the family has to
be a presheaf of that universe. The source's hypothesis is a *set* of open substacks, so that
would be faithful; it is also unnecessary. The schematic locus of Stacks 03JH contains each member
by maximality, with no reference to the family as a whole, so the covering condition can be used
section by section — which is
`AlgebraicGeometry.Space.isRepresentable_of_forall_le_schematicLocus`, the coproduct-free form of
Stacks 03KE's case `(θ)`. The main result below is therefore stated for an arbitrary index type,
as Stacks 05WE is, and no smallness or universe condition appears in its tag.

**The covering condition.** It is `AlgebraicGeometry.Stack.IsOpenSubstackCover`, the condition
Stacks 05WE is stated with: over the members of some covering sieve of the fppf topology the
chosen restriction of an object lies in one of the substacks. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackCover` for its relation to the union of Stacks
05UQ — it is the weaker of the two, so using it gives the stronger statement and it is not an
extra assumption.

**Transporting the substacks into the representing presheaf.** Once `𝒳` is representable by an
algebraic space `F`, each substack `𝒳_i`, being representable by the scheme `T_i`, gives a
morphism `a_i : h_{T_i} ⟶ F` of representing presheaves, Stacks 04SW
(`AlgebraicGeometry.Stack.representingMap`). Openness of `a_i` is the bridge above. That the
images cover is Stacks 04SW read on named sections,
`AlgebraicGeometry.Stack.morphismSpaceEquiv_app_sectionOfObj`: a section of `F` is named by an
object of a fibre of `𝒳`, the covering hypothesis puts the restriction of that object into one of
the substacks, and the section named there by the same object is the restricted section — so the
restricted section is in the image of `a_i`.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03KE](https://stacks.math.columbia.edu/tag/03KE)
* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 05WE](https://stacks.math.columbia.edu/tag/05WE)
* [Stacks Project, Tag 05WF](https://stacks.math.columbia.edu/tag/05WF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- `inferInstance` for `HasPullbacks` on presheaves over the big fppf site is a deep instance search
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_OpenSubstackCoverScheme :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_OpenSubstackCoverScheme
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **A morphism of presheaves all of whose scheme-valued base changes are open immersions is an
open immersion.**

Being an open immersion of algebraic spaces over `S` is, by definition, representability together
with every represented base change being an open immersion of schemes; so a base change of `m`
along a scheme-valued point `v` of its target is represented by the source of a base change of
`pullback.fst v m` along an identity, and is an open immersion for the same reason. No locality
of the open-immersion property is used. -/
theorem isOpenImmersion_of_forall_pullbackFst
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : F ⟶ G)
    (h : ∀ (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ G),
      IsOpenImmersion B S hS (pullback.fst v m)) :
    IsOpenImmersion B S hS m := by
  have : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative.of_exists ?_
  intro a g
  have hv := h a g
  refine ⟨hv.rep.pullback (𝟙 (yoneda.obj a)),
    hv.rep.fst (𝟙 (yoneda.obj a)) ≫ pullback.snd g m,
    hv.rep.snd (𝟙 (yoneda.obj a)), ?_, hv.property_snd (𝟙 (yoneda.obj a))⟩
  have hpaste := (hv.rep.isPullback (𝟙 (yoneda.obj a))).paste_horiz
    (IsPullback.of_hasPullback g m).flip
  simpa using hpaste

/-- **An algebraic space whose sections locally lie in the schematic locus is a scheme.**

This is the case `(θ)` of Stacks 03KE, `AlgebraicGeometry.Space.isRepresentable_of_isZariskiCover`,
with the covering family replaced by the condition it is used through: no coproduct of the family
is formed, so the family may be indexed by a type of any universe. The schematic locus is an open
subspace and therefore a sheaf, by the unconditional form of Stacks 03JH, so a section which lies
in it locally lies in it. -/
theorem isRepresentable_of_forall_le_schematicLocus
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (h : ∀ (V : BigFppfOver B S hS) (s : F.obj (op V)),
      ∃ R ∈ BigFppfOver.topology B S hS V, ∀ ⦃W : BigFppfOver B S hS⦄ (f : W ⟶ V), R f →
        F.map f.op s ∈ (schematicLocus B S hS F).obj (op W)) :
    F.IsRepresentable := by
  obtain ⟨hZopen, hZrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF
  have hFs : Presieve.IsSheaf (BigFppfOver.topology B S hS) F :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hF.isSheaf
  have hZs : Presieve.IsSheaf (BigFppfOver.topology B S hS)
      (schematicLocus B S hS F).toFunctor :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hZopen.1.isSheaf
  have hZtop : schematicLocus B S hS F = ⊤ := by
    refine le_antisymm le_top fun V s _ => ?_
    refine ((schematicLocus B S hS F).isSheaf_iff hFs).1 hZs V s ?_
    obtain ⟨R, hR, hmem⟩ := h V.unop s
    exact (BigFppfOver.topology B S hS).superset_covering (fun W f hf => hmem f hf) hR
  rw [hZtop] at hZrep
  have : (⊤ : Subfunctor F).toFunctor.IsRepresentable := hZrep
  exact isRepresentable_of_natIso _ (asIso (Subfunctor.ι (⊤ : Subfunctor F)))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The bridge of Stacks 04XB at the open-immersion property.** A 1-morphism `a : 𝒜 ⟶ 𝒞` of
categories fibred in groupoids over the big fppf site of `S` which is representable by algebraic
spaces and is an open immersion in the sense of Stacks 04XB, between two categories themselves
representable by algebraic spaces `F` and `G`, induces an open immersion `F ⟶ G` of algebraic
spaces over `S`.

Unlike `AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap` this carries no
locality hypothesis on the open-immersion property: see the implementation notes of this module.
A scheme-valued point `v` of `G` is a 1-morphism out of a slice of the site (Stacks 04SW), the
presheaf representing the base change of `a` along it is the fibre product of the representing
presheaves (`AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullbackOfPullback`), and that base
change is an open immersion by hypothesis; so the induced morphism is an open immersion by
`AlgebraicGeometry.Space.isOpenImmersion_of_forall_pullbackFst`. -/
theorem isOpenImmersion_representingMap
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (hopen : IsOpenImmersion B S hS a)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    Space.IsOpenImmersion B S hS (representingMap B S hS 𝒜 𝒞 F G eF eG a) := by
  refine Space.isOpenImmersion_of_forall_pullbackFst B S hS _ (fun V v => ?_)
  set u := CatFiberedInGroupoids.homFunctor (schemePointMap B S hS V G eG v)
  have hup := CatFiberedInGroupoids.homFunctor_comp_p (schemePointMap B S hS V G eG v)
  obtain ⟨T, hT, ⟨eT⟩⟩ := ha V u hup
  have h2 := (prop_algebraicSpaceMap_iff B S hS
    (Space.openImmersionProperty B S hS) V T hT).mp (hopen V u hup T hT ⟨eT⟩)
  exact ((Space.openImmersionProperty B S hS).arrow_mk_iso_iff
    (arrowIsoRelocalizeFibrePullbackOfPullback B S hS V a u hup
      F G eF eG v (representingMap_schemePointMap B S hS V G eG v) _ rfl
      (isAlgebraicSpace_pullback B S hS v _ (isAlgebraicSpace_yoneda B S hS V) hF hG)
      T eT hT)).mpr h2

variable {B S hS}

/-- **Stacks 05WF.** Let `𝒳` be an algebraic stack over `S` and let `𝒰 i`, `i ∈ I`, be open
substacks of `𝒳` which cover `𝒳` and are each a scheme, that is, equivalent over the site to the
category of elements of the representable presheaf of an object of the site. Then `𝒳` is a scheme.

The first step of the source's proof is Stacks 05WE,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isOpenSubstackCover`: it makes `𝒳` an
algebraic space `F`. The second step is the schematic locus of Stacks 03JH: each substack gives an
open immersion `h_{T_i} ⟶ F` whose image is therefore contained in the locus, the covering
hypothesis puts every section of `F` locally in one of those images, and the locus is a sheaf, so
it is all of `F` and `F` is a scheme. See the implementation notes of this module. -/
@[stacks 05WF]
theorem exists_equivalenceOver_yoneda_of_isOpenSubstackCover
    (𝒳 : AlgebraicStacks.{u, w} B S hS) {I : Type*} (𝒰 : I → OpenSubstack 𝒳)
    (hcover : IsOpenSubstackCover 𝒳 𝒰)
    (hscheme : ∀ i, ∃ T : BigFppfOver B S hS, Nonempty
      (StacksRepresentableCFG.EquivalenceOver
        (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val.val.p
        (presheafOfCategories (yoneda.obj T ⋙ typeToCat)).p)) :
    ∃ T : BigFppfOver B S hS, Nonempty
      (StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
        (presheafOfCategories (yoneda.obj T ⋙ typeToCat)).p) := by
  classical
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  choose T eT' using hscheme
  -- Each substack is representable by an algebraic space, namely the one a scheme represents.
  have hspace : ∀ i, IsRepresentableByAlgebraicSpace B S hS
      (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val := fun i =>
    ⟨yoneda.obj (T i), isAlgebraicSpace_yoneda B S hS (T i), eT' i⟩
  -- Stacks 05WE: `𝒳` is an algebraic space `F`.
  obtain ⟨F, hF, ⟨e⟩⟩ := isRepresentableByAlgebraicSpace_of_isOpenSubstackCover
    𝒳 𝒰 hcover hspace
  let eT : ∀ i, StacksRepresentableCFG.EquivalenceOver
      (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val.val.p
      (presheafOfCategories (yoneda.obj (T i) ⋙ typeToCat)).p := fun i => (eT' i).some
  let inc : ∀ i, (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic) ⟶ 𝒳 :=
    fun i => fullSubcategoryInclusion 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic
  -- The substacks, as open subspaces of `F`.
  let a : ∀ i, yoneda.obj (T i) ⟶ F := fun i =>
    representingMap B S hS
      (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val 𝒳.val
      (yoneda.obj (T i)) F (eT i) e (inc i).hom
  have hopen : ∀ i, Space.IsOpenImmersion B S hS (a i) := fun i =>
    isOpenImmersion_representingMap B S hS (inc i).hom (𝒰 i).isOpenImmersion.1
      (𝒰 i).isOpenImmersion.2 _ _ (isAlgebraicSpace_yoneda B S hS (T i)) hF (eT i) e
  -- Stacks 03JH, maximality: each of them lies in the schematic locus of `F`.
  have hle : ∀ i, Subfunctor.range (a i) ≤ Space.schematicLocus B S hS F := fun i =>
    Space.le_schematicLocus B S hS F _
      (Space.isOpenSubspace_range_of_isOpenImmersion (T i) (a i) (hopen i))
      (Space.isRepresentable_range_of_isOpenImmersion (T i) (a i) (hopen i))
  -- The covering hypothesis puts every section of `F` locally in one of them.
  have hrep : F.IsRepresentable := by
    refine Space.isRepresentable_of_forall_le_schematicLocus B S hS hF (fun V s => ?_)
    obtain ⟨z, hz, hs⟩ := PresheafOfCategories.exists_sectionOfObj e s
    obtain ⟨R, hR, hmem⟩ := hcover V ⟨z, hz⟩
    refine ⟨R, hR, fun W f hf => ?_⟩
    obtain ⟨i, hi⟩ := hmem f hf
    set P := Functor.pullbackFiber 𝒳.val.val.p ⟨z, hz⟩ f
    refine hle i (op W) ⟨PresheafOfCategories.sectionOfObj (eT i)
      ⟨P.1, hi⟩
      P.2, ?_⟩
    have hsec : PresheafOfCategories.sectionOfObj e
        P.1
        P.2 = F.map f.op s := by
      rw [← hs]
      exact PresheafOfCategories.sectionOfObj_map e hz
        P.2 f
        (Functor.IsPreFibered.pullbackMap hz f) inferInstance
    rw [← hsec]
    exact morphismSpaceEquiv_app_sectionOfObj B S hS
      (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val 𝒳.val
      (yoneda.obj (T i)) F (eT i) e
      ⟨CatFiberedInGroupoids.homFunctor (inc i).hom,
        CatFiberedInGroupoids.homFunctor_comp_p (inc i).hom⟩ _ _
  exact ⟨F.reprX, ⟨e.trans (PresheafOfCategories.equivalenceOverOfIso F.reprW.symm)⟩⟩

end AlgebraicGeometry.Stack

end
