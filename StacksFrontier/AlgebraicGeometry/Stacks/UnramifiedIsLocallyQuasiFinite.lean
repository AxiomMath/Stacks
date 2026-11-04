module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordFibreProductPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismPrescribedTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedLocallyQuasiFinite

/-!
# An unramified 1-morphism of algebraic stacks is locally quasi-finite (Stacks 0H2Z)

**Stacks 0H2Z** asserts that an unramified 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
(**Stacks 0CIT**) is locally quasi-finite (**Stacks 06PU**). Local quasi-finiteness is the
conjunction of three conditions — quasi-DM, locally of finite type, and discreteness of the
space of points of the fibre over every field-valued point of the target — and this file proves
all three, with no hypothesis beyond unramifiedness.

## Main results

* `AlgebraicGeometry.Stack.exists_etalePresentation_twoFibreProductSquarePt_of_isDM`: for a
  Deligne–Mumford `f` and any 1-morphism `b : V ⟶ 𝒴` out of an algebraic space, the 2-fibre
  product `V ×_𝒴 𝒳` has a surjective étale presentation by a scheme (**Stacks 0CIA**, part (2),
  read across the exchange of the two factors).
* `AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isDM`: a Deligne–Mumford `f`
  admits the étale-smooth diagram of condition (2) of **Stacks 0CIF**.
* `AlgebraicGeometry.Stack.discreteTopology_points_fibre_of_isUnramified`: the fibre of an
  unramified `f` over a field-valued point of `𝒴` has discrete space of points.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_of_isUnramified`:
  **Stacks 0H2Z**.

## Implementation notes

The quasi-DM conjunct is
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_isUnramified` (**Stacks 050E**, part (2)).

The local finite type conjunct is read off the existential smooth-diagram test
`AlgebraicGeometry.Stack.AlgebraicStacks.hasPropertyOnSomeSmoothDiagram_of_isUnramified`, whose
diagram input `AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram` is produced here for every
Deligne–Mumford `f`: take a smooth presentation of `𝒴` by a scheme `U` (the fourth clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack`), read it from the algebraic space `yoneda.obj U`, and
present `yoneda.obj U ×_𝒴 𝒳` étale-surjectively by a scheme through **Stacks 0CIA**, part (2)
(`AlgebraicGeometry.Stack.AlgebraicStacks`
`.isDeligneMumfordStack_twoFibreProduct_of_isDM_algebraicSpace`,
which rests on the proved **Stacks 06N3**); the diagram is then
`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_etalePresentation`.

The field-valued-fibre conjunct follows the source's route through **Stacks 0CIY**, **06UF** and
**05W0**, specialised to a field-valued point `Spec(k) ⟶ 𝒴`. The fibre
`𝒵 = 𝒳 ×_𝒴 Spec(k)` is unramified over `Spec(k)` by **Stacks 0CIV**. Over the chart of
`Spec(k)` by the algebraic space it represents, **Stacks 0CIA** presents the 2-fibre product
étale-surjectively, so the universal étale-smooth test that unramifiedness of `𝒵 ⟶ Spec(k)` is
stated by produces an algebraic space `U` with a smooth surjective `U ⟶ 𝒵` and an unramified
`U ⟶ Spec(k)`
(`AlgebraicGeometry.Stack.exists_etaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram`).
By **Stacks 05W0** that morphism is locally quasi-finite, so `|U|` is discrete (**Stacks 0ACA**);
the smooth surjective `U ⟶ 𝒵` is open and surjective on points (**Stacks 06R7**), so every point
of `|𝒵|` is open.

## References

* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 05W0](https://stacks.math.columbia.edu/tag/05W0)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 06UF](https://stacks.math.columbia.edu/tag/06UF)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CIV](https://stacks.math.columbia.edu/tag/0CIV)
* [Stacks Project, Tag 0CIY](https://stacks.math.columbia.edu/tag/0CIY)
* [Stacks Project, Tag 0H2Z](https://stacks.math.columbia.edu/tag/0H2Z)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CIA, part (2), in the order of factors Stacks 0CIF uses.** Let `f : 𝒳 ⟶ 𝒴` be a
Deligne–Mumford 1-morphism of algebraic stacks and `b` a 1-morphism to `𝒴` out of the algebraic
stack of an algebraic space `V`. Then the apex of the canonical 2-fibre product of `(b, f)` has a
relatively étale presentation by a scheme of the site, surjective on objects.

Stacks 0CIA, part (2), gives a surjective étale presentation of the apex of `(f, b)`; composing
with the exchange of the two factors, an equivalence, keeps it étale and surjective on objects,
and surjectivity of the presentation is read through **Stacks 06D7**. -/
theorem exists_etalePresentation_twoFibreProductSquarePt_of_isDM
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsDM B S hS f)
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴) :
    ∃ (W : BigFppfOver B S hS)
      (pres : schemeFibredCategory B S hS W ⟶
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom).pt),
      IsRelativelyEtale B S hS pres ∧
      IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS W).val.p
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom).pt.val.p
        (CatFiberedInGroupoids.homFunctor pres) := by
  obtain ⟨_, _hfib, W, p, hrep, hp⟩ :=
    AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_of_isDM_algebraicSpace.{u, w}
      B S hS f hf V hV b
  let p' : schemeFibredCategory B S hS W ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).pt := p
  let sw := twoFibreProductSwapMap B S hS b.hom f.hom
  have hswEquiv : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor sw) := by
    show Functor.IsEquivalence (TwoFibreProductOver.swap _ _ _ _ _)
    infer_instance
  have hpsu : IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS W).val.p
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).pt.val.p
      (CatFiberedInGroupoids.homFunctor p') :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS p' hrep).2
      (fun U y hy F hF he => (hp U y hy F hF he).1)
  exact ⟨W, p' ≫ sw, isRelativelyEtale_comp_of_isEquivalence B S hS p' sw hswEquiv
      ⟨hrep, fun U y hy F hF he => (hp U y hy F hF he).2⟩,
    isSurjectiveOnObjects_comp B S hS _ _ _ (CatFiberedInGroupoids.homFunctor p')
      (CatFiberedInGroupoids.homFunctor sw) (CatFiberedInGroupoids.homFunctor_comp_p sw) hpsu
      (isSurjectiveOnObjects_of_isEquivalence B S hS sw hswEquiv)⟩

/-- **A Deligne–Mumford 1-morphism admits the étale-smooth diagram of Stacks 0CIF.** For a
Deligne–Mumford `f : 𝒳 ⟶ 𝒴` there is a 2-commutative square of algebraic spaces over `f` with
smooth right-hand vertical 1-morphism, surjective left-hand vertical 1-morphism, and étale
comparison to every 2-fibre product of the cospan.

The right-hand vertical 1-morphism is the smooth presentation of `𝒴` by a scheme `U`, read from
the algebraic space `yoneda.obj U` through the backward 1-morphism of its representing
equivalence; the étale presentation of the 2-fibre product is
`AlgebraicGeometry.Stack.exists_etalePresentation_twoFibreProductSquarePt_of_isDM`. -/
theorem hasSurjectiveEtaleSmoothDiagram_of_isDM
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsDM B S hS f) :
    HasSurjectiveEtaleSmoothDiagram B S hS f := by
  obtain ⟨_hfib, _, _, U, a, hrep, ha⟩ := 𝒴.property
  let a' : schemeFibredCategory B S hS U ⟶ 𝒴.val := Bicategory.InducedBicategory.mkHom a
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver U
  let aInv : fibredCategory B S hS (yoneda.obj U) ⟶ schemeFibredCategory B S hS U :=
    equivalenceOverInvMap B S hS (yoneda.obj U) eU
  have haInvEquiv : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor aInv) := by
    show Functor.IsEquivalence eU.inv.functor
    exact eU.toEquivalence.symm.isEquivalence_functor
  let b : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⟶
      𝒴 := Bicategory.InducedBicategory.mkHom (aInv ≫ a')
  have hbsm : IsRelativelySmooth B S hS b.hom :=
    isRelativelySmooth_of_isEquivalence_comp B S hS aInv a' haInvEquiv
      ⟨hrep, fun V y hy G hG he => (ha V y hy G hG he).2⟩
  have hasu : IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS U).val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor a') :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS a' hrep).2
      (fun V y hy G hG he => (ha V y hy G hG he).1)
  have hbsu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS (yoneda.obj U)).val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor b.hom) :=
    isSurjectiveOnObjects_comp B S hS _ _ _ (CatFiberedInGroupoids.homFunctor aInv)
      (CatFiberedInGroupoids.homFunctor a') (CatFiberedInGroupoids.homFunctor_comp_p a')
      (isSurjectiveOnObjects_equivalenceOverInvMap (𝒳 := schemeFibredCategory B S hS U) B S hS
        (yoneda.obj U) eU) hasu
  exact hasSurjectiveEtaleSmoothDiagram_of_etalePresentation.{u, w} B S hS f _ _ b hbsm hbsu
    (exists_etalePresentation_twoFibreProductSquarePt_of_isDM.{u, w} B S hS f hf _ _ b)

/-- **The field-valued fibres of an unramified 1-morphism are discrete.** For an unramified
`f : 𝒳 ⟶ 𝒴` and a field-valued point `g : Spec(k) ⟶ 𝒴`, the fibre `𝒳 ×_𝒴 Spec(k)` has discrete
space of points.

The fibre is unramified over `Spec(k)` (**Stacks 0CIV**); the étale-smooth diagram over the chart
of `Spec(k)` by its own algebraic space gives a smooth surjective `U ⟶ 𝒳 ×_𝒴 Spec(k)` from an
algebraic space with `U ⟶ Spec(k)` unramified, hence locally quasi-finite (**Stacks 05W0**), so
`|U|` is discrete (**Stacks 0ACA**); a smooth surjective 1-morphism is open and surjective on
points (**Stacks 06R7**). -/
theorem discreteTopology_points_fibre_of_isUnramified
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsUnramified B S hS f)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    (g : schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ 𝒴) :
    letI := pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val
    DiscreteTopology
      (points B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.val
        (twoFibreProductSquareAlgebraicStacks B S hS f g).pt.val.property) := by
  classical
  let K : BigFppfOver B S hS := Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)
  let C := twoFibreProductSquareAlgebraicStacks B S hS f g
  -- the fibre is unramified over `Spec(k)` (Stacks 0CIV)
  have hπ : IsUnramified B S hS C.snd :=
    isUnramified_snd_of_isTwoFibreProduct B S hS f g C
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g) hf
  -- the identity chart of `Spec(k)`, read from the algebraic space it represents
  let eK := PresheafOfCategories.sliceElementsEquivalenceOver K
  let b : algebraicSpaceStack.{u, w} B S hS (yoneda.obj K) (isAlgebraicSpace_yoneda B S hS K) ⟶
      schemeStack.{u, w} B S hS K :=
    Bicategory.InducedBicategory.mkHom
      (equivalenceOverInvMap (𝒳 := schemeFibredCategory B S hS K) B S hS (yoneda.obj K) eK)
  have hbsm : IsRelativelySmooth B S hS b.hom :=
    isRelativelySmooth_equivalenceOverInvMap (𝒳 := schemeFibredCategory B S hS K) B S hS
      (yoneda.obj K) (isAlgebraicSpace_yoneda B S hS K) eK
  have hbsu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS (yoneda.obj K)).val.p
      (schemeStack.{u, w} B S hS K).val.val.p (CatFiberedInGroupoids.homFunctor b.hom) :=
    isSurjectiveOnObjects_equivalenceOverInvMap (𝒳 := schemeFibredCategory B S hS K) B S hS
      (yoneda.obj K) eK
  -- the étale-smooth diagram over that chart (Stacks 0CIA, 0CIF)
  obtain ⟨U, hU, a, h, -, hasurj, hasm, -, -, hh⟩ :=
    exists_etaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram.{u, w} B S hS
      (fun {_ _} (q : _ ⟶ _) => Space.IsUnramified B S hS q.hom :
        MorphismProperty (AlgebraicSpaces B S hS)) C.snd (yoneda.obj K)
      (isAlgebraicSpace_yoneda B S hS K) b hbsm hbsu
      (exists_etalePresentation_twoFibreProductSquarePt_of_isDM.{u, w} B S hS C.snd hπ.1 _ _ b)
      hπ.2
  -- the chart `U` is unramified, hence locally quasi-finite, over `Spec(k)`, so `|U|` is discrete
  have hdU : @DiscreteTopology (Space.points B S hS U) (Space.pointTopology B S hS U) :=
    Space.discreteTopology_points_of_isLocallyQuasiFinite B S hS hU
      (inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))) h
      (Space.isLocallyQuasiFinite_of_isUnramified B S hS h hh)
  let := pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val
  let := pointTopology B S hS C.pt.val
  have hdA : DiscreteTopology (points B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val.val
      (algebraicSpaceStack.{u, w} B S hS U hU).val.property) := by
    let := Space.pointTopology B S hS U
    exact ((isHomeomorph_spacePointMap_representing B S hS U hU
      (algebraicSpaceStack.{u, w} B S hS U hU).val
      (StacksRepresentableCFG.EquivalenceOver.refl _)).homeomorph _).discreteTopology
  -- the left vertical 1-morphism is smooth, hence open on points, and surjective
  have hasmooth : AlgebraicStacks.IsSmooth B S hS a :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ q => Space.IsSmooth B S hS q) C.pt.property a.hom hasm.1 hasm.2
  refine discreteTopology_iff_isOpen_singleton.2 fun x => ?_
  obtain ⟨z, rfl⟩ := hasurj x
  rw [← Set.image_singleton]
  exact AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS a hasmooth _ (isOpen_discrete _)

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0H2Z.** An unramified 1-morphism of algebraic stacks over `S` (**Stacks 0CIT**) is
locally quasi-finite (**Stacks 06PU**): it is quasi-DM, locally of finite type, and its fibre over
every field-valued point of the target has discrete space of points.

The three conjuncts are `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_isUnramified`,
the existential smooth-diagram test
`AlgebraicGeometry.Stack.AlgebraicStacks.hasPropertyOnSomeSmoothDiagram_of_isUnramified` at the
diagram `AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isDM`, and
`AlgebraicGeometry.Stack.discreteTopology_points_fibre_of_isUnramified`. -/
@[stacks 0H2Z]
theorem isLocallyQuasiFinite_of_isUnramified
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : Stack.IsUnramified B S hS f) :
    IsLocallyQuasiFinite B S hS f :=
  ⟨isQuasiDM_of_isUnramified B S hS hf,
    (Stack.hasPropertyOnEverySmoothDiagram_iff_some B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳.property 𝒴.property f.hom).mpr
      (hasPropertyOnSomeSmoothDiagram_of_isUnramified B S hS _ f
        (Stack.hasSurjectiveEtaleSmoothDiagram_of_isDM.{u, w} B S hS f hf.1) hf
        (fun _ _ hg => Space.isLocallyOfFiniteType_of_isUnramified B S hS hg)),
    fun k _ hk toBase g =>
      Stack.discreteTopology_points_fibre_of_isUnramified.{u, w} B S hS f hf k hk toBase g⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
