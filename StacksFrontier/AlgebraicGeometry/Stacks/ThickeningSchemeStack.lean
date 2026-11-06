module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningSchemeRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SchemeOfAffineCase
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceSources
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsMap
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# Clause (2) of Stacks 0BPW: a thickening of algebraic stacks is a scheme exactly when its
ambient stack is

Let `𝒳 ⊂ 𝒳'` be a thickening of algebraic stacks over `S`. Clause (2) of **Stacks 0BPW** says
that `𝒳` is a scheme if and only if `𝒳'` is. Being a scheme is
`Stacks.RepresentableMorphism.IsRepresentableCFG` (**Stacks 02Y3**): the underlying fibred
category is equivalent over the big fppf site of `S` to the slice of that site over an object,
i.e. over a scheme over `S`.

`AlgebraicGeometry.Stack.isRepresentableCFG_iff_isThickening` proves the equivalence from one
hypothesis, `hAffineCase`, the affine case of **Stacks 05ZR** (the closed-immersion case of
**Stacks 07VS**). That hypothesis is proved as
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace`, and
the unconditional clause is `AlgebraicGeometry.Stack.isRepresentableCFG_iff_of_isThickening`
(`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningIsScheme`).

## Main results

* `CategoryTheory.PresheafOfCategories.elementsMapEquivalenceOver`: an isomorphism of presheaves
  of sets induces an equivalence, over the base, of their categories of elements.
* `AlgebraicGeometry.Stack.exists_equivalenceOver_elements_yoneda_of_isRepresentableCFG` and
  `AlgebraicGeometry.Stack.isRepresentableCFG_of_equivalenceOver_elements`: being a scheme in the
  sense of Stacks 02Y3, read as representability of the category fibred in groupoids by the
  presheaf of points of a scheme. These are the two translations between the slice form of
  **Stacks 02Y3** and the elements form that **Stacks 04SV** and **Stacks 04SW** are stated in.
* `AlgebraicGeometry.Space.isThickeningHom_of_isClosedImmersion_of_surjective_pointsMap`: a
  morphism of algebraic spaces over `S` which is a closed immersion and surjective on points is
  a thickening in the sense of `AlgebraicGeometry.Space.IsThickeningHom`.
* `AlgebraicGeometry.Stack.prop_representingMap_of_isThickening`: a condition of **Stacks 04XB**
  satisfied by a thickening of algebraic stacks is satisfied by the morphism of representing
  algebraic spaces.
* `AlgebraicGeometry.Stack.isThickeningHom_representingMap_of_isThickening`: that morphism of
  representing algebraic spaces is itself a thickening -- the previous result read at the closed
  immersions and at the surjections.
* `AlgebraicGeometry.Stack.isRepresentableCFG_iff_isThickening`: clause (2) of **Stacks 0BPW**,
  given the affine case of Stacks 05ZR.

## Implementation notes

As in the source, clause (2) follows from clause (1) together with More on Morphisms of Spaces,
Lemma 76.9.5 — **Stacks 05ZR**. A representation of one of the two stacks by a scheme `U` is,
through **Stacks 02Y3** and the identification of the slice with the category of elements of the
presheaf it represents (`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`), a
representation of it by the algebraic space `yoneda.obj U`; clause (1) carries that across the
thickening; and **Stacks 04SW** turns the thickening itself into a morphism `α` of the two
representing algebraic spaces (`AlgebraicGeometry.Stack.representingMap`). **Stacks 04XC**
(`AlgebraicGeometry.Stack.hasRelativeProperty_iff_forall_space_baseChange`), read at the degenerate
2-fibre product of `CategoryTheory.Bicategory.TwoCommSq.idCospan`, says that `α` is a closed
immersion and surjective on points, so `α` is a thickening of algebraic spaces. In the direction
towards the ambient stack Stacks 05ZR then makes its target representable; in the direction towards
the closed substack no thickening is needed at all, only that a closed immersion is relatively
representable, which is **Stacks 03KC**.

Clause (1) of this same tag,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_iff_isThickening`, is unconditional in both
directions, so the implication from the ambient stack to the closed substack below uses no
hypothesis at all. The converse needs Stacks 05ZR, and
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SchemeOfAffineCase` reduces 05ZR to its affine
case: an algebraic space receiving a surjective closed immersion from an affine algebraic space is
affine. That is `hAffineCase`, in exactly the spelling of
`AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_affineCase`. It is not the
universally quantified form of the conclusion here, which is about representability of a category
fibred in groupoids.

The source proves the affine case through Limits of Spaces (Stacks 07VS, by noetherian
approximation), or, for a thickening of finite order, by the deformation argument of the second
proof of 05ZR. A thickening here is of arbitrary order (its ideal is locally nil, not nilpotent),
so the second argument needs in addition an approximation of the ideal by finite-type,
hence nilpotent, quasi-coherent ideals (Stacks 07V9) and a stage-selection step.

## References

* [Stacks Project, Tag 02Y3](https://stacks.math.columbia.edu/tag/02Y3)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0BPW](https://stacks.math.columbia.edu/tag/0BPW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.PresheafOfCategories

universe v u

variable {C : Type u} [Category.{v} C] {F G H : Cᵒᵖ ⥤ Type v}

/-- `CategoryTheory.PresheafOfCategories.elementsMap` is functorial in the morphism of
presheaves. -/
theorem elementsMap_comp (m : F ⟶ G) (n : G ⟶ H) :
    elementsMap (m ≫ n) = elementsMap m ⋙ elementsMap n := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ u => ?_
  exact heq_of_eq (elements_hom_ext _ _ rfl)

/-- `CategoryTheory.PresheafOfCategories.elementsMap` takes the identity to the identity. -/
theorem elementsMap_id (F : Cᵒᵖ ⥤ Type v) : elementsMap (𝟙 F) = 𝟭 _ := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ u => ?_
  exact heq_of_eq (elements_hom_ext _ _ rfl)

/-- **An isomorphism of presheaves of sets induces an equivalence of their categories of elements
over the base.** Both functors are
`CategoryTheory.PresheafOfCategories.elementsMap`, and the two 2-cells are `eqToIso`s, because
`elementsMap` is functorial on the nose. -/
def elementsMapEquivalenceOver (e : F ≅ G) :
    StacksRepresentableCFG.EquivalenceOver
      (presheafOfCategories (F ⋙ typeToCat)).p
      (presheafOfCategories (G ⋙ typeToCat)).p where
  hom := ⟨elementsMap e.hom, rfl⟩
  inv := ⟨elementsMap e.inv, rfl⟩
  unitIso := eqToIso (by rw [← elementsMap_comp, e.hom_inv_id, elementsMap_id])
  counitIso := eqToIso (by rw [← elementsMap_comp, e.inv_hom_id, elementsMap_id])
  unit_over := by
    ext Z
    simp only [eqToIso.hom, Functor.whiskerRight_app, eqToHom_app, eqToHom_map]
  counit_over := by
    ext Z
    simp only [eqToIso.hom, Functor.whiskerRight_app, eqToHom_app, eqToHom_map]

end CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed immersion of algebraic spaces over `S` which is surjective on points is a
thickening**, in the morphism form `AlgebraicGeometry.Space.IsThickeningHom` of **Stacks 05ZK**,
part (1).

A closed immersion is a monomorphism (`AlgebraicGeometry.Space.mono_of_presheaf`, a closed
immersion of schemes being one), so it is an isomorphism onto its range; the range is a closed
subspace because it is isomorphic to the source as a presheaf over the target
(`AlgebraicGeometry.isAlgebraicSpace_of_iso`) and the inclusion of the range is the closed
immersion up to that isomorphism; and surjectivity of the inclusion of the range on points
follows from surjectivity of the morphism, the two differing by an isomorphism. -/
theorem isThickeningHom_of_isClosedImmersion_of_surjective_pointsMap
    {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X')
    (hi : IsClosedImmersion B S hS i.hom)
    (hs : Function.Surjective (pointsMap B S hS X.obj i.hom)) :
    IsThickeningHom B S hS i := by
  have hmono : Mono i.hom :=
    mono_of_presheaf (P := @AlgebraicGeometry.IsClosedImmersion.{u})
      (fun _ _ g hg => have : AlgebraicGeometry.IsClosedImmersion g := hg; inferInstance) hi
  refine (isThickeningHom_iff_of_mono i).2 ⟨⟨?_, ?_⟩, ?_⟩
  · exact isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange i.hom)) X.property
  · have hfactor : Subfunctor.toRange i.hom ≫ (Subfunctor.range i.hom).ι = i.hom :=
      Subfunctor.toRange_ι i.hom
    have h := MorphismProperty.RespectsIso.precomp
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (asIso (Subfunctor.toRange i.hom)).inv i.hom hi
    have heq : (asIso (Subfunctor.toRange i.hom)).inv ≫ i.hom
        = (Subfunctor.range i.hom).ι := by
      calc (asIso (Subfunctor.toRange i.hom)).inv ≫ i.hom
          = (asIso (Subfunctor.toRange i.hom)).inv ≫
            (Subfunctor.toRange i.hom ≫ (Subfunctor.range i.hom).ι) :=
            (congrArg (fun k => (asIso (Subfunctor.toRange i.hom)).inv ≫ k) hfactor).symm
        _ = (Subfunctor.range i.hom).ι :=
          (asIso (Subfunctor.toRange i.hom)).inv_hom_id_assoc _
    rwa [heq] at h
  · intro y
    obtain ⟨x, hx⟩ := hs y
    refine ⟨pointsMap B S hS X.obj (Subfunctor.toRange i.hom) x, ?_⟩
    have h := congrFun (pointsMap_comp B S hS X.obj (Subfunctor.toRange i.hom)
      (Subfunctor.range i.hom).ι) x
    rw [Subfunctor.toRange_ι, Function.comp_apply] at h
    rw [← h]
    exact hx

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Being a scheme, in the slice form of Stacks 02Y3 and the elements form of Stacks 04SV -/

/-- **A category fibred in groupoids representable by an object of the site is representable by
the presheaf of points of that object**, as an equivalence over the site with the category of
elements of the presheaf. This is
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver` read at a representation in the
sense of **Stacks 02Y3**; it is the translation the representability results of **Stacks 04SV**
and **Stacks 04SW** are stated in. -/
theorem exists_equivalenceOver_elements_yoneda_of_isRepresentableCFG
    (𝒯 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h : Stacks.RepresentableMorphism.IsRepresentableCFG 𝒯.val.p) :
    ∃ X : BigFppfOver B S hS, Nonempty (StacksRepresentableCFG.EquivalenceOver
      𝒯.val.p (presheafOfCategories (yoneda.obj X ⋙ typeToCat)).p) := by
  obtain ⟨X, E, hE⟩ := h
  obtain ⟨G, hG, ⟨η, -⟩, ⟨ε, -⟩⟩ := hE.exists_inverse
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    𝒯.isFiberedInGroupoids (StacksRepresentableCFG.over_isFiberedInSetoids X).isFiberedInGroupoids
    E hE.isCartesianFunctor.comm
    (CategoryTheory.Equivalence.mk E G ε.symm η).isEquivalence_functor
  exact ⟨X, ⟨k.trans (PresheafOfCategories.sliceElementsEquivalenceOver X)⟩⟩

/-- **A category fibred in groupoids represented by a representable presheaf is representable by
an object of the site**, that is, is a scheme in the sense of **Stacks 02Y3**. The converse of
`AlgebraicGeometry.Stack.exists_equivalenceOver_elements_yoneda_of_isRepresentableCFG`: the
representing presheaf is transported to the presheaf of points of its representing object by
`CategoryTheory.PresheafOfCategories.elementsMapEquivalenceOver`, and
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver` identifies that with the
slice. -/
theorem isRepresentableCFG_of_equivalenceOver_elements
    {𝒯 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : StacksRepresentableCFG.EquivalenceOver
      𝒯.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (hF : F.IsRepresentable) : Stacks.RepresentableMorphism.IsRepresentableCFG 𝒯.val.p := by
  obtain ⟨T, ⟨hT⟩⟩ := hF.has_representation
  refine Stacks.RepresentableMorphism.isRepresentableCFG_of_isRepresentable _ ⟨T, ⟨?_⟩⟩
  exact (e.trans (PresheafOfCategories.elementsMapEquivalenceOver hT.toIso.symm)).trans
    (PresheafOfCategories.sliceElementsEquivalenceOver T).symm

/-! ### The morphism of representing algebraic spaces induced by a thickening -/

section Representing

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- **A condition of Stacks 04XB satisfied by a thickening of algebraic stacks is satisfied by the
morphism of representing algebraic spaces**, whenever both stacks are representable by algebraic
spaces.

This is **Stacks 04XC** (`AlgebraicGeometry.Stack.hasRelativeProperty_iff_forall_space_baseChange`)
read at the degenerate 2-fibre product `𝒳 = 𝒳' ×_{𝒳'} 𝒳` of
`CategoryTheory.Bicategory.TwoCommSq.idCospan`, whose first projection is the thickening itself. -/
theorem prop_representingMap_of_isThickening
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i)
    (hP : HasRelativeProperty B S hS P i.hom hi.1.1)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒳'.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    P (ObjectProperty.homMk
        (representingMap B S hS 𝒳.val 𝒳'.val F G eF eG i.hom) :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) :=
  (hasRelativeProperty_iff_forall_space_baseChange B S hS P i.hom hi.1.1).mp hP
    𝒳'.val ⟨G, hG, ⟨eG⟩⟩ (𝟙 𝒳'.val) (Bicategory.TwoCommSq.idCospan i.hom)
    (Bicategory.isTwoFibreProduct_idCospan i.hom) F G hF hG eF eG

/-- The closed-immersion clause of
`AlgebraicGeometry.Stack.prop_representingMap_of_isThickening`. -/
private theorem closedImmersionProperty_representingMap_of_isThickening
    (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒳'.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    Space.closedImmersionProperty B S hS (ObjectProperty.homMk
        (representingMap B S hS 𝒳.val 𝒳'.val F G eF eG i.hom) :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) :=
  prop_representingMap_of_isThickening B S hS (Space.closedImmersionProperty B S hS) i hi
    (((AlgebraicStacks.isClosedImmersion_iff_forall_hasRelativeProperty B S hS i).1 hi.1).2
      hi.1.1) hF hG eF eG

/-- **The morphism of representing algebraic spaces induced by a thickening of algebraic stacks is
a thickening of algebraic spaces.** Both clauses come from
`AlgebraicGeometry.Stack.prop_representingMap_of_isThickening`: the closed-immersion clause of
**Stacks 04YL** part (2) at `AlgebraicGeometry.Space.closedImmersionProperty`, and surjectivity on
points at `AlgebraicGeometry.Space.surjectiveMorphismProperty` through **Stacks 04XI**
(`AlgebraicGeometry.Stack.pointsMap_surjective_iff_isRelativelySurjective`). They make it a
thickening by
`AlgebraicGeometry.Space.isThickeningHom_of_isClosedImmersion_of_surjective_pointsMap`. -/
theorem isThickeningHom_representingMap_of_isThickening
    (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒳'.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    Space.IsThickeningHom B S hS
      (ObjectProperty.homMk (representingMap B S hS 𝒳.val 𝒳'.val F G eF eG i.hom) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) := by
  have hc := closedImmersionProperty_representingMap_of_isThickening B S hS i hi hF hG eF eG
  have hsurj := prop_representingMap_of_isThickening.{u, w, u} B S hS
    (Space.surjectiveMorphismProperty B S hS) i hi
    ((pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS i hi.1.1).mp hi.2)
    hF hG eF eG
  exact Space.isThickeningHom_of_isClosedImmersion_of_surjective_pointsMap B S hS _ hc hsurj

end Representing

/-! ### Stacks 0BPW, clause (2) -/

section Thickening

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- **Clause (2) of Stacks 0BPW as the `if and only if` the source states, given the affine case
of Stacks 05ZR.** If `𝒳 ⊂ 𝒳'` is a thickening of algebraic
stacks over `S` then `𝒳` is a scheme if and only if `𝒳'` is, being a scheme in the sense of
**Stacks 02Y3**.

The implication from the ambient stack to the closed substack does not use `hAffineCase`: a
representation of `𝒳'` by a scheme makes `𝒳'` an algebraic space, the implication
of clause (1) (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isThickening`)
makes `𝒳` one, and the morphism of representing algebraic spaces is a closed immersion, hence
relatively representable, so **Stacks 03KC** makes the representing presheaf of `𝒳` representable.

The converse is where it enters: clause (1) in the other direction
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_iff_isThickening`) is unconditional,
and the resulting thickening of algebraic spaces
(`AlgebraicGeometry.Stack.isThickeningHom_representingMap_of_isThickening`) is fed to
**Stacks 05ZR** reduced to its affine case,
`AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_affineCase`.

`hAffineCase` says that an algebraic space receiving a surjective closed immersion from an affine
algebraic space is affine: the closed-immersion case of **Stacks 07VS**, proved as
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace`. The
binder-free form is `AlgebraicGeometry.Stack.isRepresentableCFG_iff_of_isThickening`. -/
theorem isRepresentableCFG_iff_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i)
    (hAffineCase : ∀ {P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : P ⟶ W),
      IsAlgebraicSpace B S hS P → IsAlgebraicSpace B S hS W → Space.IsClosedImmersion B S hS j →
      Space.IsSurjective B S hS j → Space.IsAffineSpace B S hS P →
      Space.IsAffineSpace B S hS W) :
    Stacks.RepresentableMorphism.IsRepresentableCFG 𝒳.val.val.p ↔
      Stacks.RepresentableMorphism.IsRepresentableCFG 𝒳'.val.val.p := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨U, ⟨eX⟩⟩ :=
      exists_equivalenceOver_elements_yoneda_of_isRepresentableCFG B S hS 𝒳.val h
    have hU := isAlgebraicSpace_yoneda B S hS U
    obtain ⟨G, hG, ⟨eY⟩⟩ :=
      (isRepresentableByAlgebraicSpace_iff_isThickening B S hS i hi).1
        ⟨yoneda.obj U, hU, ⟨eX⟩⟩
    refine isRepresentableCFG_of_equivalenceOver_elements B S hS eY ?_
    exact Space.isRepresentable_of_isThickeningHom_of_affineCase B S hS _
      (isThickeningHom_representingMap_of_isThickening B S hS i hi hU hG eX eY)
      (Functor.IsRepresentable.mk' (Iso.refl _)) hAffineCase
  · obtain ⟨U, ⟨eY⟩⟩ :=
      exists_equivalenceOver_elements_yoneda_of_isRepresentableCFG B S hS 𝒳'.val h
    have hU := isAlgebraicSpace_yoneda B S hS U
    obtain ⟨F, hF, ⟨eX⟩⟩ := isRepresentableByAlgebraicSpace_of_isThickening B S hS i hi
      ⟨yoneda.obj U, hU, ⟨eY⟩⟩
    refine isRepresentableCFG_of_equivalenceOver_elements B S hS eX ?_
    have hc := closedImmersionProperty_representingMap_of_isThickening B S hS i hi hF hU eX eY
    exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable
      (representingMap B S hS 𝒳.val 𝒳'.val F (yoneda.obj U) eX eY i.hom) hc.rep

end Thickening

end AlgebraicGeometry.Stack

end
