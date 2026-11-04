module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FinitenessFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpaceDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty

/-!
# Local Noetherianity of the source of a 1-morphism of algebraic stacks (Stacks 06R6, 0CPM)

**Stacks 06R6** says that the source of a 1-morphism locally of finite type with locally
Noetherian target is locally Noetherian. It runs on the algebraic-space criteria of Stacks 04YF
throughout; see its own docstring.

The rest of this module is **Stacks 0CPM**, part (1).

**Stacks 0CPM** reads, verbatim: *"Let `j : 𝒳 → 𝒴` be an immersion of algebraic stacks. (1) If
`𝒴` is locally Noetherian, then `𝒳` is locally Noetherian and `j` is quasi-compact. (2) If `𝒴`
is Noetherian, then `𝒳` is Noetherian."* Its three clauses are therefore local Noetherianity of
the source, quasi-compactness of the immersion, and Noetherianity of the source. **This module
supplies the first.**

Local Noetherianity of an algebraic stack is **Stacks 04YG**, the smooth-scheme-atlas criterion
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` taken at Mathlib's
`AlgebraicGeometry.IsLocallyNoetherian`.

The argument is the source's. A smooth surjective chart `g : V ⟶ 𝒴` by a locally Noetherian
scheme is given; the 2-fibre product `𝒫 = V ×_𝒴 𝒳` is then an algebraic stack (**Stacks 04TF**)
whose first projection is a base change of `j` and whose second projection is a base change of
`g`. Being a base change of `j`, the first projection is representable by algebraic spaces
(**Stacks 0302**) and so `𝒫` is itself representable by an algebraic space `F` (the core of
**Stacks 0300**); being a base change of an immersion it is locally of finite type
(**Stacks 06ED** and **Stacks 045C**), so the morphism `F ⟶ V` of representing presheaves that
**Stacks 04XC** attaches to it is locally of finite type, and `F` is locally Noetherian by
**Stacks 04ZK**. An étale scheme chart `U ⟶ F` witnessing that — one exists by the very
definition of the étale-local property of **Stacks 03E6** — is smooth and surjective, hence so
is the induced 1-morphism `U ⟶ 𝒫` of algebraic stacks, and composing it with the second
projection gives the required locally Noetherian scheme atlas of `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.exists_oneMorphism_representingMap_eq'`: the surjectivity half of
  **Stacks 04SW** — every morphism of representing presheaves is induced by a 1-morphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyNoetherian_of_isImmersion`:
  **Stacks 0CPM**, part (1), local Noetherianity of the source.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType`:
  **Stacks 06R6**.

## Implementation notes

The source says "`U = 𝒳 ×_𝒴 V` is a scheme", using that a locally closed subspace of a scheme is
a scheme. This library has the immersion conditions of **Stacks 04YL** only as the relative
property of **Stacks 03YK**, and the bridge of **Stacks 04XB** that turns a relative property into
a property of the morphism of representing presheaves
(`AlgebraicGeometry.Stack.prop_representingMap_of_hasRelativeProperty`) carries locality at the
target for the fppf precoverage as an instance argument, which for immersions is **Stacks 042U**
and is not in this library. So the apex is only taken to be representable by an algebraic *space*
and the property carried across is local finite type, for which both instance hypotheses — Stacks
03XH and, through `AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`, Stacks 041S — are
available. That is enough: Stacks 04ZK is a statement about algebraic spaces, and an étale scheme
chart of the resulting space is as good a scheme atlas of the apex as the scheme itself would
have been.

`AlgebraicGeometry.Stack.exists_oneMorphism_representingMap_eq'` is what turns that étale chart
into a 1-morphism of algebraic stacks. `AlgebraicGeometry.Stack.morphismSpaceEquiv` is an
`Equiv`, so a morphism of representing presheaves is in the image of
`AlgebraicGeometry.Stack.representingMap`; a representative of the 2-isomorphism class it names is
a based functor, and `CategoryTheory.CatFiberedInGroupoids.homEquivBasedFunctor` reads that back
as a 1-morphism.

Smoothness of that 1-morphism is `AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth`
(**Stacks 075U**), the existential smooth-diagram test, and is supplied by the converse half of
Stacks 06FM for represented source and target, which needs no hypothesis on the tested property.
Surjectivity is `AlgebraicGeometry.Stack.IsSurjective` (**Stacks 04ZS**), surjectivity on points,
and is reached from the relative property through **Stacks 04XI**.

The two remaining clauses of Stacks 0CPM are in
`StacksFrontier/AlgebraicGeometry/Stacks/QuasiCompactImmersion.lean`, which consumes this one:

* *`j` is quasi-compact*, as the relative notion of **Stacks 03YK**, is
  `AlgebraicGeometry.Stack.AlgebraicStacks.hasRelativeProperty_quasiCompact_of_isImmersion`; it
  agrees with the absolute notion of **Stacks 050U** by **Stacks 050T**.
* *`𝒳` is Noetherian when `𝒴` is* — Noetherianity being **Stacks 0510**, quasi-compact,
  quasi-separated and locally Noetherian — is
  `AlgebraicGeometry.Stack.AlgebraicStacks.isNoetherianStack_of_isImmersion`, which takes its
  locally Noetherian conjunct from the theorem below.

## References

* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 0510](https://stacks.math.columbia.edu/tag/0510)
* [Stacks Project, Tag 06ED](https://stacks.math.columbia.edu/tag/06ED)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 0CPM](https://stacks.math.columbia.edu/tag/0CPM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The surjectivity half of Stacks 04SW.** For categories `𝒜` and `𝒞` fibred in groupoids over
the big fppf site of `S` represented by presheaves `F` and `G`, every morphism `c : F ⟶ G` of the
representing presheaves is induced by a 1-morphism `𝒜 ⟶ 𝒞`.

`AlgebraicGeometry.Stack.morphismSpaceEquiv` is an equivalence between the 2-isomorphism classes
of 1-morphisms and the morphisms `F ⟶ G`, and
`AlgebraicGeometry.Stack.representingMap` is its forward direction; a representative of the class
named by `c` is a functor over the site, which
`CategoryTheory.CatFiberedInGroupoids.homEquivBasedFunctor` reads back as a 1-morphism.

The objects are bare categories fibred in groupoids;
`AlgebraicGeometry.Stack.exists_oneMorphism_representingMap_eq` is the corresponding statement
for two algebraic stacks, whose conclusion is about the underlying 1-morphism of a morphism of
algebraic stacks. -/
theorem exists_oneMorphism_representingMap_eq'
    (𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (c : F ⟶ G) :
    ∃ a : 𝒜 ⟶ 𝒞, representingMap B S hS 𝒜 𝒞 F G eF eG a = c := by
  obtain ⟨Φ, hΦ⟩ := Quotient.exists_rep
    ((morphismSpaceEquiv B S hS 𝒜 𝒞 F G eF eG).symm c)
  refine ⟨(CatFiberedInGroupoids.homEquivBasedFunctor 𝒜 𝒞).symm ⟨Φ.1, Φ.2⟩, ?_⟩
  have hclass : (Quotient.mk (Functor.twoIsoSetoid 𝒜.val.p 𝒞.val.p)
      ⟨CatFiberedInGroupoids.homFunctor
        ((CatFiberedInGroupoids.homEquivBasedFunctor 𝒜 𝒞).symm ⟨Φ.1, Φ.2⟩),
        CatFiberedInGroupoids.homFunctor_comp_p _⟩) =
      Quotient.mk _ Φ := by
    congr 1
  rw [representingMap, hclass, hΦ, Equiv.apply_symm_apply]

namespace AlgebraicStacks

/-- An étale surjective scheme chart `c : U ⟶ F` of the algebraic space `F` representing `𝒜` is
induced by a 1-morphism `U ⟶ 𝒜`, representable by algebraic spaces, smooth and surjective. -/
private theorem exists_oneMorphism_smooth_surjective_of_etale_chart
    (𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    {U : BigFppfOver B S hS} (c : yoneda.obj U ⟶ F)
    (hcsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (hcet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c) :
    ∃ (a : schemeFibredCategory B S hS U ⟶ 𝒜)
      (harep : IsRepresentableByAlgebraicSpaces B S hS a.hom),
      HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ k => Space.IsSmooth B S hS k) a ∧
      HasRelativeProperty.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) a harep := by
  obtain ⟨a, ha⟩ := exists_oneMorphism_representingMap_eq' B S hS
    (schemeFibredCategory B S hS U) 𝒜 (yoneda.obj U) F
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eF c
  have harep : IsRepresentableByAlgebraicSpaces B S hS a.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS a
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) ⟨F, hF, ⟨eF⟩⟩
  refine ⟨a, harep, hasPropertyOnSomeSmoothDiagram_of_prop_representingMap B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) (yoneda.obj U) F
      (isAlgebraicSpace_yoneda B S hS U) hF
      (PresheafOfCategories.sliceElementsEquivalenceOver U) eF a ?_,
    (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) a harep (yoneda.obj U) F
      (isAlgebraicSpace_yoneda B S hS U) hF
      (PresheafOfCategories.sliceElementsEquivalenceOver U) eF).mpr ?_⟩ <;> rw [ha]
  · exact Space.isSmooth_of_isEtale B S hS hF (Space.isEtale_of_presheaf_etale B S hS hcet)
  · exact Space.isSurjective_of_presheafSurjective B S hS c hcsurj

/-- **Stacks 0CPM, part (1), first half**, verbatim: *"Let `j : 𝒳 → 𝒴` be an immersion of
algebraic stacks. If `𝒴` is locally Noetherian, then `𝒳` is locally Noetherian [and `j` is
quasi-compact]."* Local Noetherianity of an algebraic stack over `S` is the smooth-scheme-atlas
criterion of **Stacks 04YG** at `AlgebraicGeometry.IsLocallyNoetherian`.

The 2-fibre product `𝒫 = V ×_𝒴 𝒳` of a locally Noetherian smooth surjective scheme chart
`g : V ⟶ 𝒴` with `j` has first projection a base change of `j`, so `𝒫` is representable by an
algebraic space `F` and the induced morphism `F ⟶ V` is locally of finite type; `F` is then
locally Noetherian by Stacks 04ZK, and an étale scheme chart of `F` composed with the second
projection — a base change of `g`, hence smooth and surjective — is a locally Noetherian scheme
atlas of `𝒳`.

Quasi-compactness of `j`, the other half of part (1), and part (2) are in
`StacksFrontier/AlgebraicGeometry/Stacks/QuasiCompactImmersion.lean`, which consumes this
statement. -/
@[stacks 0CPM "part (1): the source is locally Noetherian"]
theorem isLocallyNoetherian_of_isImmersion
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (j : 𝒳 ⟶ 𝒴) (hj : IsImmersion B S hS j)
    (hY : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴) :
    HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳 := by
  classical
  obtain ⟨V, g, hgsurj, hgsm, hVN⟩ := hY
  -- the canonical 2-fibre product square over the cospan `(g, j)`
  let Qc : Bicategory.TwoCommSq g.hom j.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom j.hom
  have hQc : Bicategory.IsTwoFibreProduct Qc :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      g.hom j.hom
  -- the first projection is a base change of `j`, hence representable by algebraic spaces
  have hQfstRep : IsRepresentableByAlgebraicSpaces B S hS Qc.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      𝒳.val 𝒴.val (schemeFibredCategory B S hS V) j.hom g.hom Qc hQc hj.1
  -- so the apex is representable by an algebraic space
  obtain ⟨F, hF, ⟨eF⟩⟩ : IsRepresentableByAlgebraicSpace B S hS Qc.pt :=
    isRepresentableByAlgebraicSpace_of_representable.{u, u, u + 1} B S hS Qc.pt
      (schemeFibredCategory B S hS V) Qc.fst hQfstRep
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)
  -- and the first projection is locally of finite type, `j` being an immersion
  let : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS k.hom) :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  let : MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS k.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hm : Space.IsLocallyOfFiniteType B S hS
      (representingMap B S hS Qc.pt (schemeFibredCategory B S hS V) F (yoneda.obj V) eF
        (PresheafOfCategories.sliceElementsEquivalenceOver V) Qc.fst) :=
    prop_representingMap_of_hasRelativeProperty.{u, u} B S hS
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) =>
        Space.IsLocallyOfFiniteType B S hS k.hom) j.hom hj.1
      (fun U y hy G hG hr =>
        Space.isLocallyOfFiniteType_of_isImmersion B S hS _ (hj.2 U y hy G hG hr))
      (schemeFibredCategory B S hS V) g.hom Qc hQc F (yoneda.obj V) hF
      (isAlgebraicSpace_yoneda B S hS V) eF
      (PresheafOfCategories.sliceElementsEquivalenceOver V)
  -- so the representing algebraic space of the apex is locally Noetherian (Stacks 04ZK)
  obtain ⟨U, c, hcsurj, hcet, hUN⟩ : Space.HasEtaleLocalProperty B S hS F
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hF
      (isAlgebraicSpace_yoneda B S hS V) _ hm
      ((Space.exists_atlas_iff_of_representable B S hS (yoneda.obj V)
        (fun T : Scheme.{u} => IsLocallyNoetherian T) V (Iso.refl _)).mpr hVN)
  -- an étale scheme chart of that algebraic space is a smooth surjective chart of the apex
  obtain ⟨a, harep, hasm, hasurjrel⟩ :=
    exists_oneMorphism_smooth_surjective_of_etale_chart B S hS Qc.pt hF eF c hcsurj hcet
  -- the second projection is a base change of the chart `g`, hence smooth and surjective
  let Q : Bicategory.TwoCommSq g j := twoFibreProductSquare B S hS g j
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_twoFibreProductSquare B S hS g j
  let A : Stack.schemeStack B S hS U ⟶ Q.pt := Bicategory.InducedBicategory.mkHom a
  exact ⟨U, A ≫ Q.snd,
    isSurjective_comp B S hS A Q.snd
      ((pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS A harep).mpr hasurjrel)
      (isSurjective_of_isTwoFibreProduct B S hS Q hQ hgsurj),
    isSmooth_comp B S hS A Q.snd hasm
      (isSmooth_baseChange B S hS g j Q.swap (Bicategory.isTwoFibreProduct_swap hQ) hgsm),
    hUN⟩

/-- **Stacks 06R6.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. If `f` is
locally of finite type and `𝒴` is locally Noetherian, then `𝒳` is locally Noetherian. Local
Noetherianity of an algebraic stack over `S` is the smooth-scheme-atlas criterion of
**Stacks 04YG** at `AlgebraicGeometry.IsLocallyNoetherian`.

The source argues with scheme charts; here the whole argument runs on algebraic-space charts,
which is what the chapter's vocabulary already supports, and the scheme criterion is reached at
the two ends by **Stacks 04YF**. A smooth diagram over `f` is a pair of algebraic-space charts
`a : U ⟶ 𝒳` and `b : V ⟶ 𝒴` whose top horizontal morphism `h : U ⟶ V` is locally of finite
type, with `a` moreover surjective on objects; `V` is then a smooth algebraic-space chart of
`𝒴`, so it has the étale-local property of **Stacks 03E6** at local Noetherianity, and
**Stacks 04ZK** carries that along `h` to `U`. Since `a` is a smooth surjective algebraic-space
atlas of `𝒳`, that is the third criterion of Stacks 04YF for `𝒳`. -/
@[stacks 06R6]
theorem isLocallyNoetherian_of_isLocallyOfFiniteType
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : IsLocallyOfFiniteType B S hS f)
    (hY : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴) :
    HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳 := by
  classical
  -- local Noetherianity is local in the smooth topology, being local in the fppf topology
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  -- every smooth algebraic-space chart of `𝒴` has the étale-local property, by Stacks 04YF
  have hYchart : HasPropertyOnEverySpaceChart B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴 :=
    (exists_space_atlas_iff_forall_space B S hS
        (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴).1
      ((exists_scheme_atlas_iff_exists_space_atlas B S hS
        (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴).1 hY)
  -- a smooth diagram over `f`, whose top horizontal morphism is locally of finite type
  obtain ⟨U, V, hU, hV, a, b, h, -, ha, hasu, hb, hh⟩ :=
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳.property 𝒴.property f.hom).1 hf
  -- a relatively smooth chart of an algebraic stack is a smooth 1-morphism
  have hSmooth : ∀ {W} (hW : IsAlgebraicSpace B S hS W) {𝒵 : Stack.AlgebraicStacks B S hS}
      (k : fibredCategory B S hS W ⟶ 𝒵.val), IsRelativelySmooth B S hS k →
      IsSmooth B S hS
        (Bicategory.InducedBicategory.mkHom k : algebraicSpaceStack B S hS W hW ⟶ 𝒵) :=
    fun _ 𝒵 _ hk => hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒵.property _ hk.1 hk.2
  -- so `V` is locally Noetherian, and Stacks 04ZK carries that along `h` to `U`
  have hUN : Space.HasEtaleLocalProperty B S hS U
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hU hV h hh
      (hYchart V hV _ (hSmooth hV b hb))
  -- `a` presents `U` as a smooth surjective algebraic-space atlas of `𝒳`
  have haSurj : IsSurjective B S hS
      (Bicategory.InducedBicategory.mkHom a :
        algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳) :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS _ ha.1).mpr
      ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS a ha.1).1 hasu)
  exact (exists_scheme_atlas_iff_exists_space_atlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳).2
    ⟨U, hU, Bicategory.InducedBicategory.mkHom a, haSurj, hSmooth hU a ha, hUN⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
