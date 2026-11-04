module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothDiagramRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreUnramifiedFromChart
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubspaceOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The unramifiedness clause of Stacks 06N2's fibre hypothesis

**Stacks 06N2** consumes `AlgebraicGeometry.Stack.FibreIsUnramifiedNear`: an
`AlgebraicGeometry.Stack.OpenSubstack` of the 2-fibre product
`AlgebraicGeometry.Stack.fibreOverFieldPoint` `F = U ×_𝒳 Spec k` containing a prescribed point of
`|F|`, on which the *stack-level* unramifiedness of **Stacks 0CIT** holds of the structure
1-morphism `F ⟶ Spec k`.

What the chart construction of **Stacks 06N3** produces is the unramifiedness of a morphism of
*schemes*, which
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isUnramified_fibreSpace_of_unramifiedAt` of
`StacksFrontier.AlgebraicGeometry.Stacks.FibreUnramifiedFromChart` has already lifted to an **open
subspace** `W` of an algebraic space `Fsp` representing `F`, unramified over `Spec k` and
containing the point. This file carries that open subspace the remaining step, to the open
substack of `F` that Stacks 06N2 asks for, with both of its clauses.

## Main results

* `AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_isUnramified_isOpenSubspace`: an open
  subspace of a representing algebraic space of the fibre which is unramified over `Spec k` and
  contains a point produces `AlgebraicGeometry.Stack.FibreIsUnramifiedNear` at that point.
* `AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_unramifiedAt`: the same at the hypotheses the
  chart construction of **Stacks 06N3** delivers — an étale chart `N` of `Fsp` over `Spec k` and
  a point of it at which the morphism of schemes is unramified in the sense of **Stacks 02G4**.

## How it is proved

The open substack is cut out by the **essential image** of the composite
`AlgebraicGeometry.Stack.openSubspaceFibreMap`

    S_W ----> S_{Fsp} ----> F

of the 1-morphism of **Stacks 0458** attached to the inclusion `W.ι` with the chart
`AlgebraicGeometry.Stack.fibreSpaceChart` of the representing equivalence. The first factor is an
open immersion of algebraic stacks by
`AlgebraicGeometry.Stack.isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion`, the second
admits a quasi-inverse, so the composite is an open immersion by
`AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_comp_of_quasiInverse`, and **Stacks 0506**
makes its essential image an open substack. The open substack is built by hand from
`...isAlgebraicStack_essImage` and `...isOpenImmersion_essImageInclusion` rather than from the
existential `...exists_openSubstack_essImage`, so that the Stacks 0506 factorization
`...exists_isEquivalence_to_essImage` lands against that very algebraicity witness.

**The unramifiedness clause.** The only route the library offers to the stack-level
unramifiedness of **Stacks 0CIT** is
`AlgebraicGeometry.Stack.isUnramified_of_hasRelativeProperty_unramified` followed by the bridge of
**Stacks 04XB** for represented source and target,
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`. That bridge is applied not
at the open substack — whose representing equivalence is a choice, so that the induced morphism of
representing presheaves cannot be computed — but at `S_W`, which *is* the category of elements of
`W`, so the comparison there is the identity. The induced morphism of representing presheaves is
then computed outright, in
`AlgebraicGeometry.Stack.representingMap_openSubspaceFibreMap_comp`: by functoriality of
**Stacks 04SW** (`AlgebraicGeometry.Stack.representingMap_comp`) it is the composite of the
morphism induced by the first factor, which is `W.ι` itself by
`AlgebraicGeometry.Stack.representingMap_associatedMap`, the morphism induced by the chart, which
is the **identity** by `AlgebraicGeometry.Stack.representingMap_equivalenceOverInvMap`, and the
morphism induced by the structure 1-morphism, which is
`AlgebraicGeometry.Stack.fibreSpaceStructureMorphism` by definition. So the relative property of
**Stacks 03YK** at unramifiedness holds of `S_W ⟶ Spec k` exactly because `W ⟶ Spec k` is an
unramified morphism of algebraic spaces, which is the hypothesis.

It is then transported to the open substack along the Stacks 0506 factorization by **Stacks 0457**,
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences_symm`, at the 2-commutative square
`AlgebraicGeometry.Stack.AlgebraicStacks.toEssImageBasedSquareIso` whiskered with the structure
1-morphism. The 2-category of categories over the site is strict, so the whiskered square has the
required type on the nose. The Deligne–Mumford conjunct that
`...isUnramified_of_hasRelativeProperty_unramified` also asks for needs no transport: it is
**Stacks 050E**, part (3),
`AlgebraicGeometry.Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`, at the
representability of the inclusion composed with the structure 1-morphism — and that
representability is where the open substack's own representing datum enters,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_essImage_openSubspaceFibreMap`: the full
subcategory is equivalent to `S_W` over the site by **Stacks 003Z**, part (2),
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`, which upgrades the equivalence
of the underlying categories that Stacks 0506 delivers to an equivalence *over the site*, and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_equivalenceOver` then represents it by
the algebraic space `W`.

**The membership clause.** The point set of an open substack is the range of its inclusion on
points, so it suffices to see that the prescribed point is in the range of
`openSubspaceFibreMap` on points: the Stacks 0506 factorization and
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_comp` put that range inside the range of the
inclusion, 2-isomorphic 1-morphisms having the same map on points
(`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_eq_of_hom₂`). That the point is in the range of
the composite is `AlgebraicGeometry.Stack.spacePointMap_eq_pointsMap_comp` for the chart and
`AlgebraicGeometry.Stack.spacePointMap_algebraicSpaceStackMap` for the first factor, the latter
resting on `AlgebraicGeometry.Stack.presheafMapOfBasedFunctor_associatedMap`: the morphism of
presheaves underlying the 1-morphism of Stacks 0458 attached to `W.ι` is `W.ι`.

Note that the open substack produced here is **not** the one
`AlgebraicGeometry.Stack.exists_openSubstack_mem_pointSet_of_isOpenSubspace` produces: that one is
obtained from the open set of points by the surjectivity half of **Stacks 06FJ** and carries no
representing datum, which is what the unramifiedness clause needs.

## Implementation notes

No declaration carries a `@[stacks]` attribute: this is a step of the chart construction of
**Stacks 06N3**, whose registration sits on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`, and every tag
it rests on — Stacks 0506, 0457, 04XB, 04SW, 050E, 003Z, 0CIT — is registered where it is proved.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

/-! ### The morphism of presheaves underlying the 1-morphism of Stacks 0458 -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism of presheaves underlying the 1-morphism of Stacks 0458 attached to a morphism
of presheaves is that morphism.** The 1-morphism of **Stacks 0458** sends the object `(T, s)` of
the category of elements to `(T, a_T(s))`, and
`AlgebraicGeometry.Stack.presheafMapOfBasedFunctor` reads off the section of the image. -/
theorem presheafMapOfBasedFunctor_associatedMap
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    presheafMapOfBasedFunctor ((associatedMap B S hS a).1.hom) = a := by
  have key : ∀ x : (presheafOfCategories (G ⋙ typeToCat)).obj,
      elementSection G x x.base rfl = x.fiber.as := by
    intro x
    simp [elementSection]
  ext T s
  exact key _

/-- **The comparison of points commutes with the 1-morphism of algebraic stacks attached to a
morphism of algebraic spaces.** Transporting a point of `T` along `g` and then comparing it with
the points of the algebraic stack of `G` gives the same point as comparing first and transporting
along the induced 1-morphism.

This is `AlgebraicGeometry.Stack.spacePointMap_presheafMapOfBasedFunctor` read through
`AlgebraicGeometry.Stack.presheafMapOfBasedFunctor_associatedMap`. -/
theorem spacePointMap_algebraicSpaceStackMap
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (g : T ⟶ G)
    (p : Space.points B S hS T) :
    spacePointMap B S hS G (fibredCategory B S hS G)
        (BasedFunctor.id (fibredCategory B S hS G).val)
        (Space.pointsMap B S hS T g p) =
      AlgebraicStacks.pointsMap B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g)
        (spacePointMap B S hS T (fibredCategory B S hS T)
          (BasedFunctor.id (fibredCategory B S hS T).val) p) := by
  have h := spacePointMap_presheafMapOfBasedFunctor B S hS
    ((associatedMap B S hS g).1.hom) p
  rwa [presheafMapOfBasedFunctor_associatedMap B S hS g] at h

/-! ### The chart of the fibre by a representing algebraic space -/

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)

variable (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

/-- **The chart of the fibre by a representing algebraic space**, as a 1-morphism of algebraic
stacks: the backward 1-morphism `AlgebraicGeometry.Stack.equivalenceOverInvMap` of the
representing equivalence `eF`, read in the 2-category of algebraic stacks over `S`. -/
noncomputable abbrev fibreSpaceChart :
    algebraicSpaceStack.{u, w} B S hS Fsp hFsp ⟶
      fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g :=
  Bicategory.InducedBicategory.mkHom (equivalenceOverInvMap B S hS Fsp eF)

variable (W : Subfunctor Fsp) (hWsp : IsAlgebraicSpace B S hS W.toFunctor)

/-- **An open subspace of a representing algebraic space of the fibre, mapped into the fibre**:
the 1-morphism of **Stacks 0458** attached to the inclusion `W.ι`, followed by the chart
`AlgebraicGeometry.Stack.fibreSpaceChart` of the representing equivalence. Its essential image is
the open substack of the fibre that **Stacks 06N2** consumes. -/
noncomputable abbrev openSubspaceFibreMap :
    algebraicSpaceStack.{u, w} B S hS W.toFunctor hWsp ⟶
      fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g :=
  algebraicSpaceStackMap.{u, w} B S hS hWsp hFsp W.ι ≫
    fibreSpaceChart.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF

/-- **The morphism of representing presheaves induced by the structure 1-morphism of the open
subspace.** Read through the identity comparison on `S_W` — which *is* the category of elements of
`W` — and the representing equivalence `eF` of the fibre, the morphism of representing presheaves
that **Stacks 04SW** attaches to `S_W ⟶ F ⟶ Spec k` is the structure morphism of `W` over
`Spec k`.

Functoriality of Stacks 04SW splits it into three factors:
`AlgebraicGeometry.Stack.representingMap_associatedMap` gives `W.ι` for the first,
`AlgebraicGeometry.Stack.representingMap_equivalenceOverInvMap` gives the identity for the chart,
and the third is `AlgebraicGeometry.Stack.fibreSpaceStructureMorphism` by definition. -/
theorem representingMap_openSubspaceFibreMap_comp :
    representingMap B S hS (algebraicSpaceStack.{u, w} B S hS W.toFunctor hWsp).val
        (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)).val
        W.toFunctor (yoneda.obj (fieldPointObject B S hS k hk toBase))
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp ≫
          fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom =
      W.ι ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF := by
  have h₃ : representingMap B S hS
      (algebraicSpaceStack.{u, w} B S hS W.toFunctor hWsp).val
      (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val W.toFunctor Fsp
      (StacksRepresentableCFG.EquivalenceOver.refl _) eF
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp).hom =
      W.ι := by
    have h := representingMap_comp B S hS W.toFunctor Fsp Fsp
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) eF
      (algebraicSpaceStackMap.{u, w} B S hS hWsp hFsp W.ι).hom
      (fibreSpaceChart.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF).hom
    rw [representingMap_associatedMap B S hS W.toFunctor Fsp W.ι,
      representingMap_equivalenceOverInvMap B S hS Fsp eF, Category.comp_id] at h
    exact h
  have h₄ := representingMap_comp B S hS W.toFunctor Fsp
    (yoneda.obj (fieldPointObject B S hS k hk toBase))
    (StacksRepresentableCFG.EquivalenceOver.refl _) eF
    (PresheafOfCategories.sliceElementsEquivalenceOver _)
    (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp).hom
    (fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom
  rw [h₃] at h₄
  exact h₄

/-- **The open subspace, mapped into the fibre, is an open immersion of algebraic stacks.** The
first factor is one by
`AlgebraicGeometry.Stack.isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion` and the chart
admits a quasi-inverse, so
`AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_comp_of_quasiInverse` applies. -/
theorem isOpenImmersion_openSubspaceFibreMap
    (hWι : Space.IsOpenImmersion B S hS W.ι) :
    AlgebraicStacks.IsOpenImmersion B S hS
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp) :=
  AlgebraicStacks.isOpenImmersion_comp_of_quasiInverse B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hWsp hFsp W.ι)
    (fibreSpaceChart.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF)
    (representingEquivalence B S hS Fsp
      (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).inverse
    (representingEquivalence B S hS Fsp
      (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).unitIso
    (representingEquivalence B S hS Fsp
      (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).symm.equiv.isEquivalence_functor
    (isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion.{u, w} B S hS hWsp hFsp hWι)

/-! ### The open substack and its representing datum -/

/-- **The full subcategory cut out by the essential image of an immersion with representable
source is represented by the same algebraic space.** **Stacks 0506** factors an immersion of
algebraic stacks through the full subcategory cut out by its essential image by a 1-morphism whose
underlying functor is an equivalence of categories; **Stacks 003Z**, part (2),
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`, upgrades that to an
equivalence *over the big fppf site of `S`*, and composing with a representing equivalence of the
source represents the full subcategory by the same algebraic space.

This is the step the unramifiedness clause of **Stacks 06N2**'s fibre hypothesis needs: the open
substack it asks for is cut out by an essential image, and the relative property of
**Stacks 03YK** is read on its inclusion only after the inclusion is known to be representable by
algebraic spaces, which asks for exactly this. -/
theorem isRepresentableByAlgebraicSpace_essImage_of_isImmersion
    {𝒵 𝒲 : AlgebraicStacks.{u, w} B S hS} (i : 𝒵 ⟶ 𝒲)
    (hi : AlgebraicStacks.IsImmersion B S hS i)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒲
      (CatFiberedInGroupoids.homFunctor i.hom).essImage))
    (h𝒵 : IsRepresentableByAlgebraicSpace B S hS 𝒵.val) :
    IsRepresentableByAlgebraicSpace B S hS
      (fullSubcategoryAlgebraicStack 𝒲
        (CatFiberedInGroupoids.homFunctor i.hom).essImage hP).val := by
  obtain ⟨F', hF', ⟨e'⟩⟩ := h𝒵
  obtain ⟨ec⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    𝒵.val.property (AlgebraicStacks.isFiberedInGroupoids_essImage i)
    (AlgebraicStacks.toEssImageBased i).toFunctor (AlgebraicStacks.toEssImageBased i).w
    (AlgebraicStacks.isEquivalence_toEssImageBased i hi)
  exact ⟨F', hF', ⟨ec.symm.trans e'⟩⟩

/-- **The relative unramifiedness of the open subspace over `Spec k`.** The 1-morphism
`S_W ⟶ F ⟶ Spec k` has the relative property of **Stacks 03YK** at unramifiedness as soon as the
morphism of algebraic spaces `W ⟶ Spec k` is unramified.

The bridge of **Stacks 04XB** for represented source and target,
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`, is applied at the identity
comparison of `S_W` with `W` and the representing equivalence `eF` of the fibre; the morphism of
representing presheaves it produces is computed by
`AlgebraicGeometry.Stack.representingMap_openSubspaceFibreMap_comp`. -/
theorem relativeProperty_unramified_openSubspaceFibreMap_comp
    (hun : Space.IsUnramified B S hS
      (W.ι ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF)) :
    RelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS)
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp ≫
        fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom := by
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have ha : IsRepresentableByAlgebraicSpaces B S hS
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp ≫
        fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS _
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS W.toFunctor hWsp)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _)
  refine (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.unramifiedMorphismProperty B S hS)
    (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp ≫
      fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom ha W.toFunctor
    (yoneda.obj (fieldPointObject B S hS k hk toBase)) hWsp
    (isAlgebraicSpace_yoneda B S hS _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver _)).mpr ?_
  rw [representingMap_openSubspaceFibreMap_comp.{u, w} B S hS 𝒳 U hU k hk toBase f g
    Fsp hFsp eF W hWsp]
  exact hun

/-- **The prescribed point lies in the image of the open subspace on points.** The comparison of
points of `Fsp` with those of the fibre factors through the chart
`AlgebraicGeometry.Stack.fibreSpaceChart`
(`AlgebraicGeometry.Stack.spacePointMap_eq_pointsMap_comp`), and a point of `W` is carried to the
corresponding point of `S_W` by
`AlgebraicGeometry.Stack.spacePointMap_algebraicSpaceStackMap`. -/
theorem mem_range_pointsMap_openSubspaceFibreMap
    (z : Space.points B S hS Fsp)
    (hz : z ∈ Set.range (Space.pointsMap B S hS W.toFunctor W.ι)) :
    spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
        (representingEquivalence B S hS Fsp
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor z ∈
      Set.range (AlgebraicStacks.pointsMap B S hS
        (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp)) := by
  obtain ⟨wp, hwp⟩ := hz
  refine ⟨spacePointMap B S hS W.toFunctor (fibredCategory B S hS W.toFunctor)
    (BasedFunctor.id (fibredCategory B S hS W.toFunctor).val) wp, ?_⟩
  have h₂ : AlgebraicStacks.pointsMap B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hWsp hFsp W.ι)
        (spacePointMap B S hS W.toFunctor (fibredCategory B S hS W.toFunctor)
          (BasedFunctor.id (fibredCategory B S hS W.toFunctor).val) wp) =
      spacePointMap B S hS Fsp (fibredCategory B S hS Fsp)
        (BasedFunctor.id (fibredCategory B S hS Fsp).val) z := by
    rw [← hwp]
    exact (spacePointMap_algebraicSpaceStackMap.{u, w} B S hS hWsp hFsp W.ι wp).symm
  have h₃ := congrFun (spacePointMap_eq_pointsMap_comp B S hS Fsp
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
    (fibreSpaceChart.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF).hom.hom) z
  refine Eq.trans (congrFun (AlgebraicStacks.pointsMap_comp B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hWsp hFsp W.ι)
    (fibreSpaceChart.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF)) _) ?_
  show AlgebraicStacks.pointsMap B S hS
      (fibreSpaceChart.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF)
      (AlgebraicStacks.pointsMap B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hWsp hFsp W.ι) _) = _
  rw [h₂]
  exact h₃.symm

include hFsp hWsp in
/-- **The unramifiedness clause of the fibre hypothesis of Stacks 06N2, from an unramified open
subspace of a representing algebraic space.** Let `Fsp` represent the fibre
`F = U ×_𝒳 Spec k` through `eF`, let `W` be an open subspace of `Fsp` whose structure morphism to
`Spec k` is an unramified morphism of algebraic spaces, and let `z` be a point of `|Fsp|` lying in
`W`. Then `AlgebraicGeometry.Stack.FibreIsUnramifiedNear` holds at the point of `|F|` below `z`:
some open substack of `F` contains that point and is unramified over `Spec k` in the sense of
**Stacks 0CIT**.

The open substack is the essential image of
`AlgebraicGeometry.Stack.openSubspaceFibreMap`; see the module documentation. -/
theorem fibreIsUnramifiedNear_of_isUnramified_isOpenSubspace
    (hWι : Space.IsOpenImmersion B S hS W.ι)
    (hun : Space.IsUnramified B S hS
      (W.ι ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF))
    (z : Space.points B S hS Fsp)
    (hz : z ∈ Set.range (Space.pointsMap B S hS W.toFunctor W.ι)) :
    FibreIsUnramifiedNear.{u, w} B S hS 𝒳 U hU k hk toBase f g
      (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
        (representingEquivalence B S hS Fsp
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor z) := by
  have hi := isOpenImmersion_openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g
    Fsp hFsp eF W hWsp hWι
  have hiImm : AlgebraicStacks.IsImmersion B S hS
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp) :=
    ⟨hi.1, fun U' y hy E hE he =>
      Space.isImmersion_of_isOpenImmersion B S hS (hi.2 U' y hy E hE he)⟩
  have hP := AlgebraicStacks.isAlgebraicStack_essImage
    (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp) hiImm
  obtain ⟨c, hce, ⟨hcα⟩⟩ := AlgebraicStacks.exists_isEquivalence_to_essImage
    (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp) hiImm hP
  refine ⟨⟨(CatFiberedInGroupoids.homFunctor
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g
        Fsp hFsp eF W hWsp).hom).essImage, inferInstance, hP,
    AlgebraicStacks.isOpenImmersion_essImageInclusion
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp)
      hi hiImm hP⟩, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := mem_range_pointsMap_openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk
      toBase f g Fsp hFsp eF W hWsp z hz
    refine ⟨AlgebraicStacks.pointsMap B S hS c p, ?_⟩
    have h₁ : AlgebraicStacks.pointsMap B S hS (c ≫ fullSubcategoryInclusion
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _ hP) =
        AlgebraicStacks.pointsMap B S hS
          (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp) :=
      AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS hcα.hom
    refine Eq.trans ?_ hp
    exact (congrFun (AlgebraicStacks.pointsMap_comp B S hS c
      (fullSubcategoryInclusion
        (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _ hP)) p).symm.trans
      (congrFun h₁ p)
  · have h𝒱 := isRepresentableByAlgebraicSpace_essImage_of_isImmersion B S hS
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp)
      hiImm hP (isRepresentableByAlgebraicSpace_fibredCategory B S hS W.toFunctor hWsp)
    have hq : IsRepresentableByAlgebraicSpaces B S hS
        (fullSubcategoryInclusion
            (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _ hP ≫
          fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom :=
      isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS _ h𝒱
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _)
    refine isUnramified_of_hasRelativeProperty_unramified B S hS _ hq
      (isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS _ hq) ?_
    have _ha : Functor.IsEquivalence (AlgebraicStacks.toEssImageBased
        (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g
          Fsp hFsp eF W hWsp)).toFunctor :=
      AlgebraicStacks.isEquivalence_toEssImageBased _ hiImm
    have _hb : Functor.IsEquivalence (BasedFunctor.id
        (schemeStack.{u, w} B S hS
          (fieldPointObject B S hS k hk toBase)).val.val).toFunctor :=
      AlgebraicStacks.isEquivalence_basedFunctorId
    have hsq : BasedFunctor.comp (AlgebraicStacks.toEssImageBased
          (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp))
          ((fullSubcategoryInclusion
              (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _ hP ≫
            fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom) ≅
        BasedFunctor.comp
          ((openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp ≫
            fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom)
          (BasedFunctor.id (schemeStack.{u, w} B S hS
            (fieldPointObject B S hS k hk toBase)).val.val) :=
      Bicategory.whiskerRightIso
        (AlgebraicStacks.toEssImageBasedSquareIso
          (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp))
        (fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom
    exact relativeProperty_of_equivalences_symm B S hS
      (Space.unramifiedMorphismProperty B S hS)
      (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp ≫
        fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom
      (fullSubcategoryInclusion
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g) _ hP ≫
        fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g).hom.hom
      (AlgebraicStacks.toEssImageBased
        (openSubspaceFibreMap.{u, w} B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF W hWsp))
      (BasedFunctor.id _) hsq
      (relativeProperty_unramified_openSubspaceFibreMap_comp.{u, w} B S hS 𝒳 U hU k hk
        toBase f g Fsp hFsp eF W hWsp hun)

include hFsp in
/-- **The unramifiedness clause of the fibre hypothesis of Stacks 06N2, at the hypotheses the
chart construction of Stacks 06N3 delivers.** Let `Fsp` represent the fibre `F = U ×_𝒳 Spec k`,
let `N` be an étale chart of `Fsp` whose structure morphism `q` over `Spec k` factors the
structure morphism of `F`, and let `v` be a point of the scheme underlying `N` at which the
morphism of schemes `q` is unramified in the sense of **Stacks 02G4**. Then
`AlgebraicGeometry.Stack.FibreIsUnramifiedNear` holds at the point of `|F|` below `v`.

This is the hypothesis `AlgebraicGeometry.Stack.exists_openSubspace_isEtale_of_fibre` of
**Stacks 06N2** consumes, produced from the scheme-level unramifiedness that the slicing of the
source's chart delivers:
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isUnramified_fibreSpace_of_unramifiedAt` turns that
into an unramified open subspace of `Fsp` containing the point, and
`AlgebraicGeometry.Stack.fibreIsUnramifiedNear_of_isUnramified_isOpenSubspace` carries it to the
open substack of `F`. -/
theorem fibreIsUnramifiedNear_of_unramifiedAt
    (N : Space.SmallEtale B S hS Fsp)
    (q : (Space.SmallEtale.toOver B S hS Fsp).obj N ⟶ fieldPointObject B S hS k hk toBase)
    (hsq : N.obj.hom ≫ fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF =
      yoneda.map q)
    (v : Space.chartScheme N)
    (hv : UnramifiedAt ((BigFppfOver.toScheme B S hS).map q) v) :
    FibreIsUnramifiedNear.{u, w} B S hS 𝒳 U hU k hk toBase f g
      (spacePointMap B S hS Fsp (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
        (representingEquivalence B S hS Fsp
          (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val eF).functor
        (Space.chartPointsMap N v)) := by
  obtain ⟨W', hW', hun, hmem⟩ :=
    exists_isOpenSubspace_isUnramified_fibreSpace_of_unramifiedAt B S hS 𝒳 U hU k hk toBase
      f g Fsp hFsp eF N q hsq v hv
  exact fibreIsUnramifiedNear_of_isUnramified_isOpenSubspace.{u, w} B S hS 𝒳 U hU k hk toBase
    f g Fsp hFsp eF W' hW'.1 hW'.2 hun _ hmem

end AlgebraicGeometry.Stack

end
