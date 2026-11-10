module

public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.StabilizerDimensionObjectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartQuasiFinitePair
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidRelativeProperty

/-!
# The self-intersection of a point of a quasi-DM stack has dimension zero (Stacks 06MF)

Let `𝒳` be an algebraic stack over `S` which is **quasi-DM over `S`**
(`AlgebraicGeometry.Stack.IsQuasiDMOver`, **Stacks 050D** part (2)) and let
`ξ : Spec(k) ⟶ 𝒳` be a 1-morphism out of the algebraic stack represented by a field-valued
point `Spec(k) ⟶ S` of the base which is **locally of finite type**. Write
`ℛ = Spec(k) ×_{ξ, 𝒳, ξ} Spec(k)` for the self-intersection of `ξ` and let `R` be an algebraic
space representing it.

This file proves `dim(R) = 0` — more precisely `dim(R) ≤ 0`, the dimension of Stacks 04N6 being
a supremum in `WithBot ℕ∞` — which is the first paragraph of the proof of **Stacks 06MF**, and
the input that the chart construction of that theorem needs at a *general* quasi-DM algebraic
stack rather than at one which is locally quasi-finite over a field-valued point of the base.

The argument is the source's. The groupoid in algebraic spaces `(u, R, s, t, c)` of
**Stacks 04T4 (4)** carried by `ξ` is `AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid`;
its source and target are locally of finite type because they are base changes of `ξ`. Its
stabilizer (**Stacks 0447**) is
`G = R ×_{(t,s), u ×_S u, Δ} u = 𝒳 ×_{𝒳 × 𝒳} u`, and the pair `(t, s) : R ⟶ u ×_S u` is
locally quasi-finite by **Stacks 050H** part (5): it is a base change of the relative diagonal
`Δ_{𝒳/S}`, which is locally quasi-finite exactly because `𝒳` is quasi-DM over `S`. Hence `G` is
locally quasi-finite over `u = Spec(k)`, so `dim(G) ≤ 0` by **Stacks 0ACA**, and
**Stacks 06FF** — `AlgebraicGeometry.Space.dimension_arrows_eq_dimension_stabilizer` — gives
`dim(R) = dim(G)`.

Running **Stacks 0ACA** backwards then makes the two structure morphisms `s`, `t : R ⟶ Spec(k)`
of the groupoid themselves locally quasi-finite, which is the form in which the self-intersection
of a finite type point enters the slicing step of **Stacks 06MF**.

## Main results

* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_twoFibreProduct_sitePullbackObj`: the
  canonical 2-fibre product of `p ≫ q` with itself, for `q` a 1-morphism to the algebraic stack
  represented by *any* object of the site, is represented by the presheaf of the fibre product
  of the underlying objects of the site. This is
  `AlgebraicGeometry.Stack.nonempty_equivalenceOver_twoFibreProduct_sitePullback` with the
  field-valued point of the base replaced by an arbitrary object, which the proof there never
  used.
* `AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid`: the groupoid in algebraic spaces of
  **Stacks 04T4 (4)** carried by a 1-morphism out of a represented algebraic stack, with the
  canonical chart of the source as its object space.
* `AlgebraicGeometry.Stack.SelfIntersection.prop_sourceTarget_pointGroupoid`: **the join of the
  parts of Stacks 050H to the groupoid's own pre-relation** — the pair `(t, s) : R ⟶ u ×_S u` has
  every property of morphisms of algebraic spaces, stable under base change and local on the
  target for the fppf topology, which the relative diagonal `Δ_{𝒳/S}` has in the sense of
  Stacks 04XB.
* `AlgebraicGeometry.Stack.SelfIntersection.isLocallyQuasiFinite_sourceTarget_pointGroupoid`:
  the pair `(t, s) : R ⟶ u ×_S u` is locally quasi-finite when `𝒳` is quasi-DM over `S`, which
  is part (5).
* `AlgebraicGeometry.Stack.SelfIntersection.isUnramified_sourceTarget_pointGroupoid` and
  `...isSeparated_sourceTarget_pointGroupoid`: parts (4) and (3) there — the pair is unramified
  when `𝒳` is DM over `S`, and separated when `Δ_{𝒳/S}` is separated.
* `AlgebraicGeometry.Stack.SelfIntersection.isLocallyQuasiFinite_stabilizer_pointGroupoid` and
  `...dimension_stabilizerOverBase_pointGroupoid_le_zero`: the stabilizer is locally
  quasi-finite over the object space, hence of dimension at most zero when the object space has
  at most one point.
* `AlgebraicGeometry.Stack.SelfIntersection.isLocallyOfFiniteType_relationTarget` and
  `...isLocallyOfFiniteType_relationSource`: the two structure morphisms of the
  self-intersection groupoid are locally of finite type as soon as the point is.
* `AlgebraicGeometry.Stack.SelfIntersection.dimension_relation_le_zero`: **the result** —
  `dim(Spec(k) ×_𝒳 Spec(k)) ≤ 0`.
* `AlgebraicGeometry.Stack.SelfIntersection.isLocallyQuasiFinite_source_pointGroupoid` and
  `...isLocallyQuasiFinite_target_pointGroupoid`: the structure morphisms of the groupoid are
  locally quasi-finite.
* `AlgebraicGeometry.Stack.SelfIntersection.siteIsoOfIsoSpecField`: an object of the big fppf
  site of `S` whose underlying scheme is isomorphic to the spectrum of a field is isomorphic in
  the site to the field-valued point of the base that it determines, the site containing that
  spectrum by `...contains_spec_of_isoSpecField`.
* `AlgebraicGeometry.Stack.SelfIntersection.dimension_relation_le_zero_of_isoSpecField` and the
  two `...isLocallyQuasiFinite_*_pointGroupoid_of_isoSpecField`: the three results above with
  their hypothesis weakened from a field-valued point of the base to such an object of the site.
  That is the shape **Stacks 06MP** produces, and `AlgebraicGeometry.Stack.FieldSpectrum` is the
  structure carrying it; the normalization to the literal form that **Stacks 06FF** tests runs
  through the isomorphism of the site above, and through the isomorphism hypothesis that
  `AlgebraicGeometry.Space.dimension_arrows_eq_dimension_stabilizer_of_objects_iso` takes.

## Implementation notes

The one thing that has to be built is the identification of the groupoid-theoretic pair
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.sourceTarget` with the comparison 1-morphism
`AlgebraicGeometry.Stack.AlgebraicStacks.mapBase` of **Stacks 050H**; the library had no bridge
between the two. It is built once, for an arbitrary property of morphisms of algebraic spaces
over `S`, as `AlgebraicGeometry.Stack.SelfIntersection.prop_sourceTarget_pointGroupoid`, of which
the three parts of Stacks 050H that the groupoid division consumes are specialisations. Both
morphisms go into a fibre product of the object space with itself over the base, and the bridge
is their shared universal property:

* `AlgebraicGeometry.Stack.AlgebraicStacks.mapBase` at the cospan `(ξ, ξ)` and the structure
  morphism `σ : 𝒳 ⟶ S` is read on representing presheaves by **Stacks 04XC**
  (`AlgebraicGeometry.Stack.prop_representingMap_of_hasRelativeProperty`), which is where the
  condition of Stacks 04XB on `Δ_{𝒳/S}` is consumed, giving a morphism `R ⟶ h_{u ×_S u}` with
  `P` into the presheaf of the fibre product *in the site*;
* that presheaf is a pullback of `h_u ⟶ h_S` with itself
  (`AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProductSquare` and
  `AlgebraicGeometry.Stack.representingMap_representedChart_eq_yoneda_map_siteMap`), and so is
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.objectPairs` of the groupoid, because the
  structure morphism of the object space to the final algebraic space is the Yoneda image of the
  morphism of the site underlying `ξ ≫ σ` — the base being final, there is only one such
  morphism;
* `CategoryTheory.IsPullback.isoIsPullback` therefore compares the two, and the two composites
  of the comparison with the projections are the two structure morphisms of the groupoid, by
  `AlgebraicGeometry.Stack.representingMap_comp` and the compatibility of
  `AlgebraicGeometry.Stack.AlgebraicStacks.mapBase` with the projections, which holds by `rfl`;
  the comparison being an isomorphism, `P` crosses it because `P` respects isomorphisms.

That the morphisms of representing presheaves named by the two projections of the canonical
square are the `AlgebraicGeometry.Stack.SelfIntersection.relationTargetMap` and
`...relationSourceMap` of **Stacks 04T4 (4)** also holds by `rfl`, so no comparison is inserted
anywhere.

The two structure morphisms are locally of finite type by base change: the projections of the
canonical square are base changes of `ξ` (**Stacks 06FU**,
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_baseChange`, with
`CategoryTheory.Bicategory.isTwoFibreProduct_swap` for the second one) and
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_representingMap` reads that on the representing
presheaves. These are stated for an arbitrary representing space of the source rather than for
the canonical chart, because the unifier then identifies the representing map with the structure
morphism cheaply.

No `@[stacks]` attribute is claimed: **Stacks 06FF** is registered on
`AlgebraicGeometry.Space.dimension_arrows_eq_dimension_stabilizer` and
`AlgebraicGeometry.Space.dimension_arrows_eq_dimension_stabilizer_of_objects_iso`,
**Stacks 050H** part (5) on
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_mapBase_of_isQuasiDM`, and this is
a step of the proof of **Stacks 06MF**.

## References

* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 06FF](https://stacks.math.columbia.edu/tag/06FF)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the limits of presheaves on the big fppf site times out at the default limit
/-- Pullbacks of presheaves on the big fppf site of `S` (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_SelfIntersectionGroupoidStabilizerDimension :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_SelfIntersectionGroupoidStabilizerDimension
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The canonical 2-fibre product of `p ≫ q` with itself is represented by the fibre product
of the underlying objects of the site.** Let `q : 𝒴₀ ⟶ T` be a 1-morphism of algebraic stacks
over `S` to the algebraic stack represented by an object `T` of the site and let
`p : U ⟶ 𝒴₀` be a 1-morphism out of the algebraic stack represented by an object `U`. Then the
apex of `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare` at the cospan
`(p ≫ q, p ≫ q)` is represented by the presheaf of `AlgebraicGeometry.Stack.sitePullbackObj`,
the fibre product `U ×_T U` read in the site.

This is `AlgebraicGeometry.Stack.nonempty_equivalenceOver_twoFibreProduct_sitePullback` with no
hypothesis that `T` be a field-valued point of the base: that statement's field never entered
its proof, and the structure morphism of an algebraic stack over `S` goes to the algebraic stack
represented by the final object of the site, which is not a field-valued point.

The square of represented stacks over `U ×_T U` is a 2-fibre product of
`(schemeStackMap m, schemeStackMap m)` for `m` the morphism of the site underlying `p ≫ q`; both
legs are reindexed across `AlgebraicGeometry.Stack.schemeStackMapIso` to the cospan
`(p ≫ q, p ≫ q)`, the comparison with the canonical square is an equivalence, and
`CategoryTheory.StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence` composed with
`AlgebraicGeometry.Stack.representedChart` is the representation. -/
theorem nonempty_equivalenceOver_twoFibreProduct_sitePullbackObj
    (T : BigFppfOver B S hS) {𝒴₀ : AlgebraicStacks.{u, w} B S hS}
    (q : 𝒴₀ ⟶ schemeStack.{u, w} B S hS T)
    (U : BigFppfOver B S hS) (p : schemeStack.{u, w} B S hS U ⟶ 𝒴₀) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProduct B S hS (p ≫ q) (p ≫ q)).val.val.p
      (presheafOfCategories (yoneda.obj (sitePullbackObj B S hS
        (siteMap B S hS (p ≫ q)) (siteMap B S hS (p ≫ q))) ⋙ typeToCat)).p) := by
  classical
  set m := siteMap B S hS (p ≫ q) with hm
  let θ : schemeStackMap.{u, w} B S hS m ≅ p ≫ q := (schemeStackMapIso B S hS (p ≫ q)).symm
  let Wsq := ((schemeStackSquare.{u, w} B S hS
    (isPullback_sitePullback B S hS m m).w).reindexFst θ).reindexSnd θ
  have hWsq : Bicategory.IsTwoFibreProduct Wsq :=
    Bicategory.isTwoFibreProduct_reindexSnd θ (Bicategory.isTwoFibreProduct_reindexFst θ
      (isTwoFibreProduct_sitePullbackStackSquare.{u, w} B S hS m m))
  let a₀ : Bicategory.TwoCommSq.PreHom
      (AlgebraicStacks.twoFibreProductSquare B S hS (p ≫ q) (p ≫ q)) Wsq :=
    Quotient.out (hWsq.from _)
  exact (StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (AlgebraicStacks.twoFibreProductSquare B S hS (p ≫ q) (p ≫ q)).pt.val.property
    Wsq.pt.val.property
    (CatFiberedInGroupoids.homFunctor a₀.hom.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p a₀.hom.hom)
    (isEquivalence_of_isTwoFibreProductAlgebraicStacks B S hS
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS (p ≫ q) (p ≫ q))
      hWsq a₀)).map
    fun E => E.trans (representedChart B S hS _)

namespace SelfIntersection

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (kObj : BigFppfOver B S hS)
  (ξ : schemeStack.{u, w} B S hS kObj ⟶ 𝒳)
  (Rsp : AlgebraicSpaces B S hS)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (AlgebraicStacks.twoFibreProduct B S hS ξ ξ).val.val.p
    (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p)

/-- An isomorphism of presheaves on the big fppf site of `S` is an étale chart morphism: it is
representable because it is invertible, and every base change of it is invertible, hence étale,
on the underlying schemes. -/
private theorem inverseImageEtale_presheaf_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : F ⟶ G) [IsIso b] :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) b := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda b, ?_⟩
  intro A D g fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  let : IsIso snd := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful snd
  change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- **The groupoid in algebraic spaces of Stacks 04T4 (4) carried by a point of an algebraic
stack.** For a 1-morphism `ξ : U ⟶ 𝒳` out of the algebraic stack represented by an object `U` of
the site and an algebraic space `R` representing the self-intersection of `ξ`, this is
`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionGroupoid` with the canonical chart
`AlgebraicGeometry.Stack.representedChart` of `U` as the representation of the object space; its
object space is therefore `AlgebraicGeometry.schemeSpace U` on the nose, which is what
**Stacks 06FF** asks of a groupoid over a field. -/
noncomputable abbrev pointGroupoid :
    GroupoidInAlgebraicSpaces B S hS (Space.terminalSpace B S hS) :=
  selfIntersectionGroupoid (B := B) (S := S) (hS := hS)
    (𝒰 := (schemeStack.{u, w} B S hS kObj).val) (𝒳 := 𝒳.val) (f := ξ.hom.hom)
    (U := AlgebraicGeometry.schemeSpace kObj) (R := Rsp)
    (representedChart B S hS kObj) eR
    (isFiberedInSetoids_source (B := B) (S := S) (hS := hS)
      (𝒰 := (schemeStack.{u, w} B S hS kObj).val)
      (U := AlgebraicGeometry.schemeSpace kObj) (representedChart B S hS kObj))

/-- **A condition of Stacks 04XB at the relative diagonal of a stack over the base is a property
of the pair `(t, s)` of the self-intersection groupoid of a point.** For `ξ : U ⟶ 𝒳` a
1-morphism out of a represented algebraic stack and `P` a property of morphisms of algebraic
spaces over `S` which is stable under base change and local on the target for the fppf topology,
the morphism `AlgebraicGeometry.GroupoidInAlgebraicSpaces.sourceTarget` of
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid` — the pair of the target and the source,
read as a morphism `R ⟶ U ×_S U` of algebraic spaces over `S` — has `P` as soon as the relative
diagonal `Δ_{𝒳/S}` has `P` in the sense of **Stacks 04XB**.

This is the join of the parts of **Stacks 050H** to the groupoid's own pre-relation, at the
cospan `(ξ, ξ)` over the structure morphism of `𝒳`: those parts are stated for the comparison
1-morphism `U ×_𝒳 U ⟶ U ×_S U` of a cospan, which is a base change of `Δ_{𝒳/S}`, so
**Stacks 04XC** (`AlgebraicGeometry.Stack.prop_representingMap_of_hasRelativeProperty`) reads `P`
off it on representing presheaves; the identification of that comparison with the groupoid's pair
is explained in the module's implementation notes. -/
theorem prop_sourceTarget_pointGroupoid
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)] [P.RespectsIso]
    (hP : RelativeProperty.{u, u, u + 1} B S hS P
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom)) :
    P (GroupoidInAlgebraicSpaces.sourceTarget (pointGroupoid B S hS kObj ξ Rsp eR)) := by
  classical
  set σ := structureMorphism B S hS 𝒳 with hσ
  set m := siteMap B S hS (ξ ≫ σ) with hm
  set W := sitePullbackObj B S hS m m with hWdef
  obtain ⟨eG⟩ := nonempty_equivalenceOver_twoFibreProduct_sitePullbackObj B S hS
    (Over.mk (𝟙 (B.obj hS))) σ kObj ξ
  set 𝒵 := AlgebraicStacks.twoFibreProduct B S hS (ξ ≫ σ) (ξ ≫ σ) with h𝒵
  set Csq := AlgebraicStacks.twoFibreProductSquare B S hS (ξ ≫ σ) (ξ ≫ σ) with hCsqdef
  set rmfst := representingMap B S hS 𝒵.val (schemeStack.{u, w} B S hS kObj).val
    (yoneda.obj W) (yoneda.obj kObj) eG (representedChart B S hS kObj) Csq.fst.hom with hrmfst
  set rmsnd := representingMap B S hS 𝒵.val (schemeStack.{u, w} B S hS kObj).val
    (yoneda.obj W) (yoneda.obj kObj) eG (representedChart B S hS kObj) Csq.snd.hom with hrmsnd
  have hpbpre : IsPullback rmfst rmsnd (yoneda.map m) (yoneda.map m) := by
    let _hfib : (twoFibreProductStructureFunctor B S hS
        (schemeStack.{u, w} B S hS kObj).val (schemeStack.{u, w} B S hS kObj).val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (ξ ≫ σ).hom (ξ ≫ σ).hom).IsFibered :=
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (ξ ≫ σ).hom (ξ ≫ σ).hom).pt.property.isFibered
    rw [hm, ← representingMap_representedChart_eq_yoneda_map_siteMap B S hS (ξ ≫ σ), hrmfst, hrmsnd]
    exact isPullback_representingMap_twoFibreProductSquare B S hS
      (schemeStack.{u, w} B S hS kObj).val (schemeStack.{u, w} B S hS kObj).val
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
      (yoneda.obj kObj) (yoneda.obj kObj) (yoneda.obj (Over.mk (𝟙 (B.obj hS))))
      (representedChart B S hS kObj) (representedChart B S hS kObj)
      (representedChart B S hS (Over.mk (𝟙 (B.obj hS))))
      (ξ ≫ σ).hom (ξ ≫ σ).hom (yoneda.obj W) eG
  set rmMB := representingMap B S hS (AlgebraicStacks.twoFibreProduct B S hS ξ ξ).val 𝒵.val
    Rsp.obj (yoneda.obj W) eR eG (AlgebraicStacks.mapBase B S hS ξ ξ σ).hom with hrmMB
  have hbar : P (ObjectProperty.homMk rmMB :
      (⟨Rsp.obj, Rsp.property⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS)) :=
    prop_representingMap_of_hasRelativeProperty.{u, u + 1} B S hS P
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val σ.hom)
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS σ)
      hP 𝒵.val (AlgebraicStacks.mapCospan B S hS ξ ξ σ).hom
      (AlgebraicStacks.mapBaseSquare B S hS ξ ξ σ)
      (AlgebraicStacks.isTwoFibreProduct_mapBaseSquare B S hS ξ ξ σ)
      Rsp.obj (yoneda.obj W) Rsp.property (isAlgebraicSpace_yoneda B S hS W) eR eG
  have hob : (pointGroupoid B S hS kObj ξ Rsp eR).objectsToBase.hom = yoneda.map m :=
    (Space.baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _
  have hpbG : IsPullback
      (GroupoidInAlgebraicSpaces.objectPairsTarget (pointGroupoid B S hS kObj ξ Rsp eR)).hom
      (GroupoidInAlgebraicSpaces.objectPairsSource (pointGroupoid B S hS kObj ξ Rsp eR)).hom
      (yoneda.map m) (yoneda.map m) := by
    rw [← hob]
    exact IsPullback.of_hasPullback _ _
  have hfst : rmMB ≫ rmfst = (pointGroupoid B S hS kObj ξ Rsp eR).target.hom := by
    rw [hrmMB, hrmfst, ← representingMap_comp B S hS Rsp.obj (yoneda.obj W) (yoneda.obj kObj)
      eR eG (representedChart B S hS kObj) (AlgebraicStacks.mapBase B S hS ξ ξ σ).hom
      Csq.fst.hom]
    rfl
  have hsnd : rmMB ≫ rmsnd = (pointGroupoid B S hS kObj ξ Rsp eR).source.hom := by
    rw [hrmMB, hrmsnd, ← representingMap_comp B S hS Rsp.obj (yoneda.obj W) (yoneda.obj kObj)
      eR eG (representedChart B S hS kObj) (AlgebraicStacks.mapBase B S hS ξ ξ σ).hom
      Csq.snd.hom]
    rfl
  set hiso := IsPullback.isoIsPullback (yoneda.obj kObj) (yoneda.obj kObj) hpbpre hpbG
    with hisodef
  have hcfst : hiso.hom ≫
      (GroupoidInAlgebraicSpaces.objectPairsTarget
        (pointGroupoid B S hS kObj ξ Rsp eR)).hom = rmfst := by
    rw [hisodef]
    exact IsPullback.isoIsPullback_hom_fst _ _ hpbpre hpbG
  have hcsnd : hiso.hom ≫
      (GroupoidInAlgebraicSpaces.objectPairsSource
        (pointGroupoid B S hS kObj ξ Rsp eR)).hom = rmsnd := by
    rw [hisodef]
    exact IsPullback.isoIsPullback_hom_snd _ _ hpbpre hpbG
  have hrfst : (rmMB ≫ hiso.hom) ≫
      (GroupoidInAlgebraicSpaces.objectPairsTarget
        (pointGroupoid B S hS kObj ξ Rsp eR)).hom =
      (pointGroupoid B S hS kObj ξ Rsp eR).target.hom :=
    (Category.assoc _ _ _).trans ((congrArg (fun z => rmMB ≫ z) hcfst).trans hfst)
  have hrsnd : (rmMB ≫ hiso.hom) ≫
      (GroupoidInAlgebraicSpaces.objectPairsSource
        (pointGroupoid B S hS kObj ξ Rsp eR)).hom =
      (pointGroupoid B S hS kObj ξ Rsp eR).source.hom :=
    (Category.assoc _ _ _).trans ((congrArg (fun z => rmMB ≫ z) hcsnd).trans hsnd)
  have hkey : (GroupoidInAlgebraicSpaces.sourceTarget
      (pointGroupoid B S hS kObj ξ Rsp eR)).hom = rmMB ≫ hiso.hom :=
    hpbG.hom_ext
      ((GroupoidInAlgebraicSpaces.sourceTarget_target_projection _).trans hrfst.symm)
      ((GroupoidInAlgebraicSpaces.sourceTarget_source_projection _).trans hrsnd.symm)
  have heq : GroupoidInAlgebraicSpaces.sourceTarget (pointGroupoid B S hS kObj ξ Rsp eR) =
      (ObjectProperty.homMk rmMB :
          (⟨Rsp.obj, Rsp.property⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS)) ≫
        (ObjectProperty.isoMk _ hiso :
            (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ≅
              GroupoidInAlgebraicSpaces.objectPairs
                (pointGroupoid B S hS kObj ξ Rsp eR)).hom :=
    ObjectProperty.hom_ext _ hkey
  rw [heq]
  exact MorphismProperty.RespectsIso.postcomp _ _ _ hbar

/-- **The pair `(t, s)` of a self-intersection groupoid is locally quasi-finite when the stack is
quasi-DM over the base.** This is
`AlgebraicGeometry.Stack.SelfIntersection.prop_sourceTarget_pointGroupoid` at local
quasi-finiteness, which is **Stacks 050H** part (5): the comparison `U ×_𝒳 U ⟶ U ×_S U` is a base
change of the relative diagonal `Δ_{𝒳/S}`, which is locally quasi-finite by the definition of
quasi-DM (**Stacks 04YW**). -/
theorem isLocallyQuasiFinite_sourceTarget_pointGroupoid
    (h𝒳 : IsQuasiDMOver B S hS 𝒳) :
    Space.IsLocallyQuasiFinite B S hS
      (GroupoidInAlgebraicSpaces.sourceTarget
        (pointGroupoid B S hS kObj ξ Rsp eR)).hom :=
  prop_sourceTarget_pointGroupoid B S hS kObj ξ Rsp eR
    (Space.locallyQuasiFiniteProperty B S hS) h𝒳

/-- **The pair `(t, s)` of a self-intersection groupoid is unramified when the stack is DM over
the base.** This is
`AlgebraicGeometry.Stack.SelfIntersection.prop_sourceTarget_pointGroupoid` at unramifiedness,
which is **Stacks 050H** part (4): the comparison `U ×_𝒳 U ⟶ U ×_S U` is a base change of the
relative diagonal `Δ_{𝒳/S}`, which is unramified by the definition of DM (**Stacks 04YW**). -/
theorem isUnramified_sourceTarget_pointGroupoid
    (h𝒳 : IsDMOver B S hS 𝒳) :
    Space.IsUnramified B S hS
      (GroupoidInAlgebraicSpaces.sourceTarget
        (pointGroupoid B S hS kObj ξ Rsp eR)).hom := by
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u + 1} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  exact prop_sourceTarget_pointGroupoid B S hS kObj ξ Rsp eR
    (Space.unramifiedMorphismProperty B S hS) h𝒳.2

/-- **The pair `(t, s)` of a self-intersection groupoid is separated when the relative diagonal
of the stack over the base is.** This is
`AlgebraicGeometry.Stack.SelfIntersection.prop_sourceTarget_pointGroupoid` at separatedness,
which is **Stacks 050H** part (3): the comparison `U ×_𝒳 U ⟶ U ×_S U` is a base change of the
relative diagonal `Δ_{𝒳/S}`. -/
theorem isSeparated_sourceTarget_pointGroupoid
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom)) :
    Space.IsSeparated B S hS
      (GroupoidInAlgebraicSpaces.sourceTarget
        (pointGroupoid B S hS kObj ξ Rsp eR)).hom := by
  have : (Space.separatedProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.separated_isLocalAtTarget_fpqc.{u, u + 1} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  exact prop_sourceTarget_pointGroupoid B S hS kObj ξ Rsp eR
    (Space.separatedProperty B S hS) hΔ

/-- **The stabilizer of a self-intersection groupoid is locally quasi-finite over the object
space.** The stabilizer of **Stacks 0447** is the base change along the diagonal of `U ×_S U` of
the pair `(t, s)`, which is locally quasi-finite by
`AlgebraicGeometry.Stack.SelfIntersection.isLocallyQuasiFinite_sourceTarget_pointGroupoid`, and
local quasi-finiteness of morphisms of algebraic spaces is stable under base change
(**Stacks 03XL**).

In the notation of **Stacks 06MF** this is the statement that `G = 𝒳 ×_{𝒳 × 𝒳} u` is locally
quasi-finite over `u`. -/
theorem isLocallyQuasiFinite_stabilizer_pointGroupoid (h𝒳 : IsQuasiDMOver B S hS 𝒳) :
    Space.IsLocallyQuasiFinite B S hS
      (GroupoidInAlgebraicSpaces.stabilizer (pointGroupoid B S hS kObj ξ Rsp eR)).hom :=
  Space.IsLocallyQuasiFinite.of_isPullback B S hS
    (IsPullback.of_hasPullback
      (GroupoidInAlgebraicSpaces.sourceTarget (pointGroupoid B S hS kObj ξ Rsp eR)).hom
      (GroupoidInAlgebraicSpaces.diagonal (pointGroupoid B S hS kObj ξ Rsp eR)).hom).flip
    Rsp.property
    (GroupoidInAlgebraicSpaces.objectPairs (pointGroupoid B S hS kObj ξ Rsp eR)).property
    (isLocallyQuasiFinite_sourceTarget_pointGroupoid B S hS kObj ξ Rsp eR h𝒳)

/-- **The stabilizer of the self-intersection groupoid of a point has dimension at most zero.**
If moreover the scheme underlying the object `U` of the site has at most one point — as it does
when `U` is the spectrum of a field — then local quasi-finiteness of the stabilizer over the
object space is, by **Stacks 0ACA**, exactly the statement that the stabilizer has dimension at
most zero.

The source states this as `dim(G) = 0`; the dimension of **Stacks 04N6** is a supremum in
`WithBot ℕ∞`, so the empty space has dimension `⊥` and the unconditional form is the
inequality. -/
theorem dimension_stabilizerOverBase_pointGroupoid_le_zero (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj kObj)) :
    Space.dimension B S hS
        (GroupoidInAlgebraicSpaces.stabilizerOverBase
          (pointGroupoid B S hS kObj ξ Rsp eR)).obj
        (GroupoidInAlgebraicSpaces.stabilizerOverBase
          (pointGroupoid B S hS kObj ξ Rsp eR)).property ≤ 0 := by
  have hlqf := isLocallyQuasiFinite_stabilizer_pointGroupoid B S hS kObj ξ Rsp eR h𝒳
  exact (Space.isLocallyQuasiFinite_iff_dimension_le_zero B S hS
    (GroupoidInAlgebraicSpaces.stabilizerOverBase
      (pointGroupoid B S hS kObj ξ Rsp eR)).property hsub
    (GroupoidInAlgebraicSpaces.stabilizer (pointGroupoid B S hS kObj ξ Rsp eR)).hom
    (Space.holdsOnEveryEtaleChart_mono B S hS (fun _ hg => hg.1) hlqf)).mp hlqf

section FiniteType

variable (Usp : AlgebraicSpaces B S hS)
  (eU : StacksRepresentableCFG.EquivalenceOver
    (schemeStack.{u, w} B S hS kObj).val.val.p
    (presheafOfCategories (Usp.obj ⋙ typeToCat)).p)

/-- **The target morphism of a self-intersection groupoid is locally of finite type as soon as
the point is.** The first projection of the canonical 2-fibre product square of the cospan
`(ξ, ξ)` is a base change of `ξ`, hence locally of finite type by **Stacks 06FU**, and
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_representingMap` reads that on the morphism of
representing presheaves, which is
`AlgebraicGeometry.Stack.SelfIntersection.relationTarget` by `rfl`. -/
theorem isLocallyOfFiniteType_relationTarget
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    Space.IsLocallyOfFiniteType B S hS
      (relationTarget (B := B) (S := S) (hS := hS)
        (𝒰 := (schemeStack.{u, w} B S hS kObj).val) (𝒳 := 𝒳.val) (f := ξ.hom.hom)
        (U := Usp) (R := Rsp) eU eR).hom :=
  isLocallyOfFiniteType_representingMap B S hS Rsp.obj Usp.obj Rsp.property Usp.property eR eU
    (AlgebraicStacks.twoFibreProductSquare B S hS ξ ξ).fst
    (AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS ξ ξ
      (AlgebraicStacks.twoFibreProductSquare B S hS ξ ξ)
      (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS ξ ξ) hξ)

/-- **The source morphism of a self-intersection groupoid is locally of finite type as soon as
the point is.** The second projection is the first projection of the canonical square with its
two legs exchanged (`CategoryTheory.Bicategory.isTwoFibreProduct_swap`), so the argument of
`AlgebraicGeometry.Stack.SelfIntersection.isLocallyOfFiniteType_relationTarget` applies to it
too. -/
theorem isLocallyOfFiniteType_relationSource
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    Space.IsLocallyOfFiniteType B S hS
      (relationSource (B := B) (S := S) (hS := hS)
        (𝒰 := (schemeStack.{u, w} B S hS kObj).val) (𝒳 := 𝒳.val) (f := ξ.hom.hom)
        (U := Usp) (R := Rsp) eU eR).hom :=
  isLocallyOfFiniteType_representingMap B S hS Rsp.obj Usp.obj Rsp.property Usp.property eR eU
    (AlgebraicStacks.twoFibreProductSquare B S hS ξ ξ).snd
    (AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS ξ ξ
      (AlgebraicStacks.twoFibreProductSquare B S hS ξ ξ).swap
      (Bicategory.isTwoFibreProduct_swap
        (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS ξ ξ)) hξ)

end FiniteType

/-- `AlgebraicGeometry.Stack.SelfIntersection.isLocallyOfFiniteType_relationSource` at the
canonical chart of the object space, which is the source morphism of
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid`. -/
theorem isLocallyOfFiniteType_source_pointGroupoid
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    Space.IsLocallyOfFiniteType B S hS
      (pointGroupoid B S hS kObj ξ Rsp eR).source.hom :=
  isLocallyOfFiniteType_relationSource B S hS kObj ξ Rsp eR
    (AlgebraicGeometry.schemeSpace kObj) (representedChart B S hS kObj) hξ

/-- `AlgebraicGeometry.Stack.SelfIntersection.isLocallyOfFiniteType_relationTarget` at the
canonical chart of the object space, which is the target morphism of
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid`. -/
theorem isLocallyOfFiniteType_target_pointGroupoid
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    Space.IsLocallyOfFiniteType B S hS
      (pointGroupoid B S hS kObj ξ Rsp eR).target.hom :=
  isLocallyOfFiniteType_relationTarget B S hS kObj ξ Rsp eR
    (AlgebraicGeometry.schemeSpace kObj) (representedChart B S hS kObj) hξ

/-- An object of the site whose underlying scheme is isomorphic to a field spectrum has at most one
point. -/
private theorem subsingleton_toScheme_of_iso_spec (k : Type u) [Field k]
    (eK : (BigFppfOver.toScheme B S hS).obj kObj ≅ Spec (.of k)) :
    Subsingleton ((BigFppfOver.toScheme B S hS).obj kObj) :=
  have : Subsingleton (Spec (CommRingCat.of k) : Type u) := inferInstance
  ⟨fun _ _ => (Scheme.homeoOfIso eK).injective (Subsingleton.elim _ _)⟩

/-- The self-intersection of a point of a quasi-DM stack has dimension at most zero, when the
object space of its groupoid is isomorphic to the field-valued point `toBase` of the base. -/
private theorem dimension_relation_le_zero_of_objects_iso (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    (objects_iso : (pointGroupoid B S hS kObj ξ Rsp eR).objects ≅ AlgebraicGeometry.schemeSpace
      (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
    (hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj kObj))
    (h𝒳 : IsQuasiDMOver B S hS 𝒳) (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ) :
    Space.dimension B S hS Rsp.obj Rsp.property ≤ 0 :=
  (Space.dimension_arrows_eq_dimension_stabilizer_of_objects_iso B S hS hk toBase
    (pointGroupoid B S hS kObj ξ Rsp eR) objects_iso
    (isLocallyOfFiniteType_source_pointGroupoid B S hS kObj ξ Rsp eR hξ)
    (isLocallyOfFiniteType_target_pointGroupoid B S hS kObj ξ Rsp eR hξ)).trans_le
    (dimension_stabilizerOverBase_pointGroupoid_le_zero B S hS kObj ξ Rsp eR h𝒳 hsub)

section FieldPoint

variable (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
  (toBase : Spec (.of k) ⟶ S)
  {𝒳₀ : AlgebraicStacks.{u, w} B S hS}
  (ξ₀ : schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒳₀)
  (Rsp₀ : AlgebraicSpaces B S hS)
  (eR₀ : StacksRepresentableCFG.EquivalenceOver
    (AlgebraicStacks.twoFibreProduct B S hS ξ₀ ξ₀).val.val.p
    (presheafOfCategories (Rsp₀.obj ⋙ typeToCat)).p)

include eR₀ in
/-- **The self-intersection of a field-valued point of a quasi-DM algebraic stack has dimension
at most zero.** Let `𝒳` be an algebraic stack over `S` which is quasi-DM over `S` and let
`ξ : Spec(k) ⟶ 𝒳` be a 1-morphism out of the algebraic stack represented by a field-valued point
of the base which is locally of finite type. Then the algebraic space `R` representing the
self-intersection `Spec(k) ×_{ξ, 𝒳, ξ} Spec(k)` has dimension at most zero.

This is the first paragraph of the proof of **Stacks 06MF**. The stabilizer of the groupoid
`(u, R, s, t, c)` of **Stacks 04T4 (4)** is locally quasi-finite over `u = Spec(k)` because `𝒳`
is quasi-DM, hence of dimension at most zero
(`AlgebraicGeometry.Stack.SelfIntersection.dimension_stabilizerOverBase_pointGroupoid_le_zero`),
and **Stacks 06FF** — `AlgebraicGeometry.Space.dimension_arrows_eq_dimension_stabilizer`, whose
two hypotheses are supplied by
`AlgebraicGeometry.Stack.SelfIntersection.isLocallyOfFiniteType_source_pointGroupoid` and its
twin — says that the arrow space has the same dimension as the stabilizer.

The source writes `dim(R) = 0`; the dimension of **Stacks 04N6** is a supremum in `WithBot ℕ∞`,
so the faithful unconditional form is the inequality. -/
theorem dimension_relation_le_zero
    (h𝒳 : IsQuasiDMOver B S hS 𝒳₀)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ₀) :
    Space.dimension B S hS Rsp₀.obj Rsp₀.property ≤ 0 :=
  dimension_relation_le_zero_of_objects_iso B S hS _ ξ₀ Rsp₀ eR₀ k hk toBase (Iso.refl _)
    (subsingleton_toScheme_of_iso_spec B S hS _ k (Iso.refl _)) h𝒳 hξ

/-- **The source morphism of the self-intersection groupoid of a field-valued point of a
quasi-DM algebraic stack is locally quasi-finite.** This is **Stacks 0ACA** run backwards on
`AlgebraicGeometry.Stack.SelfIntersection.dimension_relation_le_zero`: the source morphism is
locally of finite type, its target has one point, and the dimension of its source is at most
zero. -/
theorem isLocallyQuasiFinite_source_pointGroupoid
    (h𝒳 : IsQuasiDMOver B S hS 𝒳₀)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ₀) :
    Space.IsLocallyQuasiFinite B S hS
      (pointGroupoid B S hS
        (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ξ₀ Rsp₀ eR₀).source.hom := by
  exact (Space.isLocallyQuasiFinite_iff_dimension_le_zero B S hS Rsp₀.property
    (subsingleton_toScheme_of_iso_spec B S hS _ k (Iso.refl _)) _
    (isLocallyOfFiniteType_source_pointGroupoid B S hS _ ξ₀ Rsp₀ eR₀ hξ)).mpr
    (dimension_relation_le_zero B S hS k hk toBase ξ₀ Rsp₀ eR₀ h𝒳 hξ)

/-- The twin of
`AlgebraicGeometry.Stack.SelfIntersection.isLocallyQuasiFinite_source_pointGroupoid` for the
target morphism. -/
theorem isLocallyQuasiFinite_target_pointGroupoid
    (h𝒳 : IsQuasiDMOver B S hS 𝒳₀)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ₀) :
    Space.IsLocallyQuasiFinite B S hS
      (pointGroupoid B S hS
        (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ξ₀ Rsp₀ eR₀).target.hom := by
  exact (Space.isLocallyQuasiFinite_iff_dimension_le_zero B S hS Rsp₀.property
    (subsingleton_toScheme_of_iso_spec B S hS _ k (Iso.refl _)) _
    (isLocallyOfFiniteType_target_pointGroupoid B S hS _ ξ₀ Rsp₀ eR₀ hξ)).mpr
    (dimension_relation_le_zero B S hS k hk toBase ξ₀ Rsp₀ eR₀ h𝒳 hξ)

end FieldPoint

/-! ### A field spectrum of the site, normalized to a field-valued point of the base -/

section FieldSpectrumNormalization

/-- **The spectrum of the field is itself an object of the big fppf site.** It is isomorphic to
the underlying scheme of `kObj₁`, which the site contains, and the size cutoff of
**Stacks 021R** that `AlgebraicGeometry.BigFppfSite.Contains` tests is an isomorphism invariant
by `AlgebraicGeometry.Scheme.size_congr`. -/
theorem contains_spec_of_isoSpecField (kObj₁ : BigFppfOver B S hS) (k : Type u) [Field k]
    (eK : (BigFppfOver.toScheme B S hS).obj kObj₁ ≅ Spec (.of k)) :
    B.Contains (Spec (.of k)) :=
  lt_of_eq_of_lt (Scheme.size_congr eK).symm kObj₁.left.property

/-- The structure morphism over the base scheme of the spectrum of the field, read through the
isomorphism with the underlying scheme of `kObj₁`. -/
noncomputable abbrev toBaseOfIsoSpecField (kObj₁ : BigFppfOver B S hS) (k : Type u) [Field k]
    (eK : (BigFppfOver.toScheme B S hS).obj kObj₁ ≅ Spec (.of k)) : Spec (.of k) ⟶ S :=
  eK.inv ≫ kObj₁.hom.hom

/-- **An object of the big fppf site of `S` whose underlying scheme is the spectrum of a field is
isomorphic in the site to the field-valued point of the base that it determines.** This is the
normalization that **Stacks 06FF** asks for: the tag tests the object space of a groupoid against
`Over.mk (⟨Spec k ⟶ S⟩)`, while **Stacks 06MP** hands over an object of the site together with an
isomorphism of its underlying scheme onto `Spec k`, and this isomorphism is what carries the one
shape to the other. -/
noncomputable def siteIsoOfIsoSpecField (kObj₁ : BigFppfOver B S hS) (k : Type u) [Field k]
    (eK : (BigFppfOver.toScheme B S hS).obj kObj₁ ≅ Spec (.of k)) :
    kObj₁ ≅ Over.mk ((⟨toBaseOfIsoSpecField B S hS kObj₁ k eK⟩ :
      B.obj (contains_spec_of_isoSpecField B S hS kObj₁ k eK) ⟶ B.obj hS)) := by
  refine Over.isoMk (ObjectProperty.isoMk _ eK :
    kObj₁.left ≅ B.obj (contains_spec_of_isoSpecField B S hS kObj₁ k eK)) ?_
  exact ObjectProperty.hom_ext _ (Iso.hom_inv_id_assoc eK kObj₁.hom.hom)

end FieldSpectrumNormalization

section FieldSpectrumPoint

variable (kObj₁ : BigFppfOver B S hS) (k : Type u) [Field k]
  (eK : (BigFppfOver.toScheme B S hS).obj kObj₁ ≅ Spec (.of k))
  {𝒳₁ : AlgebraicStacks.{u, w} B S hS}
  (ξ₁ : schemeStack.{u, w} B S hS kObj₁ ⟶ 𝒳₁)
  (Rsp₁ : AlgebraicSpaces B S hS)
  (eR₁ : StacksRepresentableCFG.EquivalenceOver
    (AlgebraicStacks.twoFibreProduct B S hS ξ₁ ξ₁).val.val.p
    (presheafOfCategories (Rsp₁.obj ⋙ typeToCat)).p)

include eK eR₁ in
/-- **The self-intersection of a field-valued point of a quasi-DM algebraic stack has dimension
at most zero, at a field spectrum of the site.** This is
`AlgebraicGeometry.Stack.SelfIntersection.dimension_relation_le_zero` — the first paragraph of
the proof of **Stacks 06MF** — with its hypothesis weakened: the 1-morphism out of a represented
algebraic stack is allowed to come from *any* object `kObj₁` of the big fppf site of `S` whose
underlying scheme is isomorphic to the spectrum of a field, rather than from an object of the
literal form `Over.mk (⟨Spec k ⟶ S⟩)`.

That is the shape in which **Stacks 06MP** produces its field-valued point, as
`AlgebraicGeometry.Stack.FieldSpectrum`. The two inputs are already at this generality: the
stabilizer bound
`AlgebraicGeometry.Stack.SelfIntersection.dimension_stabilizerOverBase_pointGroupoid_le_zero`
asks only that the underlying scheme have at most one point, which the isomorphism supplies, and
**Stacks 06FF** — `AlgebraicGeometry.Space.dimension_arrows_eq_dimension_stabilizer_of_objects_iso`
— takes an isomorphism of the object space with the field spectrum, which
`AlgebraicGeometry.Stack.SelfIntersection.siteIsoOfIsoSpecField` supplies through
`AlgebraicGeometry.schemeSpaceFunctor`. -/
theorem dimension_relation_le_zero_of_isoSpecField
    (h𝒳 : IsQuasiDMOver B S hS 𝒳₁)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ₁) :
    Space.dimension B S hS Rsp₁.obj Rsp₁.property ≤ 0 :=
  dimension_relation_le_zero_of_objects_iso B S hS kObj₁ ξ₁ Rsp₁ eR₁ k
    (contains_spec_of_isoSpecField B S hS kObj₁ k eK) (toBaseOfIsoSpecField B S hS kObj₁ k eK)
    ((AlgebraicGeometry.schemeSpaceFunctor B S hS).mapIso
      (siteIsoOfIsoSpecField B S hS kObj₁ k eK))
    (subsingleton_toScheme_of_iso_spec B S hS kObj₁ k eK) h𝒳 hξ

include eK eR₁ in
/-- **The source morphism of the self-intersection groupoid of a field spectrum of the site is
locally quasi-finite.** This is
`AlgebraicGeometry.Stack.SelfIntersection.isLocallyQuasiFinite_source_pointGroupoid` at the
weakened hypothesis of
`AlgebraicGeometry.Stack.SelfIntersection.dimension_relation_le_zero_of_isoSpecField`:
**Stacks 0ACA** run backwards on that dimension bound, the target of the source morphism having
one point. -/
theorem isLocallyQuasiFinite_source_pointGroupoid_of_isoSpecField
    (h𝒳 : IsQuasiDMOver B S hS 𝒳₁)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ₁) :
    Space.IsLocallyQuasiFinite B S hS
      (pointGroupoid B S hS kObj₁ ξ₁ Rsp₁ eR₁).source.hom := by
  exact (Space.isLocallyQuasiFinite_iff_dimension_le_zero B S hS Rsp₁.property
    (subsingleton_toScheme_of_iso_spec B S hS kObj₁ k eK) _
    (isLocallyOfFiniteType_source_pointGroupoid B S hS kObj₁ ξ₁ Rsp₁ eR₁ hξ)).mpr
    (dimension_relation_le_zero_of_isoSpecField B S hS kObj₁ k eK ξ₁ Rsp₁ eR₁ h𝒳 hξ)

include eK eR₁ in
/-- The twin of `isLocallyQuasiFinite_source_pointGroupoid_of_isoSpecField` for the target
morphism. -/
theorem isLocallyQuasiFinite_target_pointGroupoid_of_isoSpecField
    (h𝒳 : IsQuasiDMOver B S hS 𝒳₁)
    (hξ : AlgebraicStacks.IsLocallyOfFiniteType B S hS ξ₁) :
    Space.IsLocallyQuasiFinite B S hS
      (pointGroupoid B S hS kObj₁ ξ₁ Rsp₁ eR₁).target.hom := by
  exact (Space.isLocallyQuasiFinite_iff_dimension_le_zero B S hS Rsp₁.property
    (subsingleton_toScheme_of_iso_spec B S hS kObj₁ k eK) _
    (isLocallyOfFiniteType_target_pointGroupoid B S hS kObj₁ ξ₁ Rsp₁ eR₁ hξ)).mpr
    (dimension_relation_le_zero_of_isoSpecField B S hS kObj₁ k eK ξ₁ Rsp₁ eR₁ h𝒳 hξ)

end FieldSpectrumPoint

end SelfIntersection

end AlgebraicGeometry.Stack

end
