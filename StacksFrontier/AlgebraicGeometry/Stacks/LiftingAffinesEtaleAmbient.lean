module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleStabilizerPreservingIsomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningEtaleDeformationProperties

/-!
# A morphism of smooth lifts is étale on the ambient spaces (Stacks 0CJS)

Fix a thickening `ι : 𝒳 ⟶ 𝒳'` of algebraic stacks over `S`, an algebraic space `W` over `S` and
a smooth 1-morphism `x : W ⟶ 𝒳`, and consider the category
`AlgebraicGeometry.Stack.EtaleSmoothLift` of smooth lifts of étale opens of `W` along `ι`
(**Stacks 0CJP**). Stacks 0CJS says that for a morphism `(f, f', γ)` of that category the
component `f' : U' ⟶ V'` between the ambient algebraic spaces is étale.

The source's proof: `f` is étale as a morphism of the spaces-étale site of `W`, and **Stacks 0CJC**
applies, because `U' ⟶ 𝒳'` and `V' ⟶ 𝒳'` are smooth and `U = 𝒳 ×_{𝒳'} U'`,
`V = 𝒳 ×_{𝒳'} V'`. This file carries out that argument with no further input: the étale clause
of Stacks 0CJC is `AlgebraicGeometry.Stack.isEtale_ambient_of_isEtale`.

## Main results

* `AlgebraicGeometry.Stack.isEtale_algebraicSpaceStackFunctor_map_iff`: a morphism of algebraic
  spaces is étale exactly when the 1-morphism of algebraic stacks it induces is étale in the
  sense of **Stacks 0CIL**.
* `AlgebraicGeometry.Stack.isEtale_of_isTwoFibreProduct_of_isThickening`: the étale clause of
  Stacks 0CJC over a thickening `ι : 𝒳 ⟶ 𝒳'`, for a morphism of two cartesian squares over `ι`
  whose corners are algebraic spaces, read on morphisms of algebraic spaces.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.Hom.isEtale_ambient`: **Stacks 0CJS**.

## Implementation notes

Stacks 0CJC is stated in this library for 1-morphisms of algebraic stacks, and étaleness there
is the notion of **Stacks 0CIL**: Deligne–Mumford together with the universal étale-smooth
diagram test. The morphisms `f` and `f'` of 0CJS are morphisms of algebraic spaces, étale in the
sense of `AlgebraicGeometry.Space.IsEtale`. The two are matched by
`isEtale_algebraicSpaceStackFunctor_map_iff`: the 1-morphism attached to a morphism of algebraic
spaces is representable by algebraic spaces, its representing morphism is the morphism itself
(`AlgebraicGeometry.Stack.representingMap_associatedMap`), and for a representable 1-morphism
étaleness in the sense of Stacks 0CIL is étaleness of the representing morphism
(`AlgebraicGeometry.Stack.isRelativelyEtale_of_isEtale`,
`AlgebraicGeometry.AlgebraicStacks.isEtale_of_isRelativelyEtale` and the bridge
`AlgebraicGeometry.Stack.isRelativelyEtale_iff_isEtale_representingMap` of Stacks 04XB).

The diagram of Stacks 0CJC is fed as follows: its thickening of the base is `ι`, its ambient
1-morphism is the one induced by `f'`, the two cartesian squares are the two smooth lifts read
over the cospans `(x', ι)` and `(y', ι)` (the `isTwoFibreProduct` fields, swapped), the 2-cell
between the two legs to `𝒳'` is the inverse of `γ` (2-morphisms of algebraic stacks are
invertible), the restriction 2-cell is the transport along `f' ∘ i = j ∘ f`, the 2-cell between
the two legs to `𝒳` is the transport along `a = b ∘ f`, and the compatibility of the cube is the
coherence `i^*γ ∘ α = f^*β` of the morphism of smooth lifts, inverted. The three finiteness and
flatness conditions on `x'` and `y'` come from their smoothness.

This supersedes `AlgebraicGeometry.Stack.EtaleSmoothLift.isEtale_ambient`, which carries the
étale clause of Stacks 0CJC as its hypothesis `hCJC`.

**Inherited caveat.** Thickenings of algebraic stacks are
`AlgebraicGeometry.Stack.IsThickening` (**Stacks 0BPP**, part (1)), which omits the
homeomorphism-of-underlying-spaces clause of the source for want of a library site for the point
topology of Stacks 04XL. That omission is inherited here, through
`AlgebraicGeometry.Stack.EtaleSmoothLift`; it weakens the hypothesis on `ι`, so the statement
proved is at least as strong as the source's.

## References

* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CJC](https://stacks.math.columbia.edu/tag/0CJC)
* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CJS](https://stacks.math.columbia.edu/tag/0CJS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Étaleness of a morphism of algebraic spaces, read in the 2-category of algebraic stacks.**
A morphism `f` of algebraic spaces over `S` is étale exactly when the 1-morphism of algebraic
stacks it induces is étale in the sense of **Stacks 0CIL**.

The induced 1-morphism is representable by algebraic spaces, since its source is an algebraic
space and its target an algebraic stack, and the morphism of representing presheaves it induces
is `f` itself (**Stacks 0458** against **Stacks 04SW**). For a representable 1-morphism,
étaleness in the sense of Stacks 0CIL is the relative étaleness of **Stacks 04XB**, which in turn
is étaleness of the representing morphism. -/
theorem isEtale_algebraicSpaceStackFunctor_map_iff {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    IsEtale B S hS ((algebraicSpaceStackFunctor.{u, w} B S hS).map f) ↔
      Space.IsEtale B S hS f.hom := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map f).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).obj Y).property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS X.obj X.property) _
  have key : IsRelativelyEtale B S hS ((algebraicSpaceStackFunctor.{u, w} B S hS).map f).hom ↔
      Space.IsEtale B S hS (representingMap B S hS (fibredCategory B S hS X.obj)
        (fibredCategory B S hS Y.obj) X.obj Y.obj
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (associatedMap B S hS f.hom).1) :=
    isRelativelyEtale_iff_isEtale_representingMap B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map f).hom hrep X.obj Y.obj X.property
      Y.property (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
  rw [representingMap_associatedMap] at key
  exact ⟨fun h => key.1 (isRelativelyEtale_of_isEtale B S hS _ hrep h),
    fun h => AlgebraicStacks.isEtale_of_isRelativelyEtale B S hS _ (key.2 h)⟩

/-- **Inverting a coherence square of 2-morphisms.** In a category, let `ah : R ⟶ T` and
`c : T ⟶ Q` have left inverses `ai` and `ci`, and let `bi : P ⟶ R` be a right inverse of
`bh : R ⟶ P`. If `ah ≫ c` is `bh` up to transports, then `bi` followed by an identity is the
transport followed by `ci ≫ ai`.

This is the compatibility of the cube of **Stacks 0CJC** read off the coherence of a morphism of
smooth lifts; it is stated over an arbitrary category so that the objects involved, composites
of 1-morphisms of algebraic stacks that agree only up to the strict associativity of that
2-category, can be matched by unification rather than by rewriting. -/
theorem comp_eq_eqToHom_comp_of_comp_eq_eqToHom {𝒞 : Type*} [Category 𝒞] {P Q R T : 𝒞}
    {ah : R ⟶ T} {ai : T ⟶ R} {c : T ⟶ Q} {ci : Q ⟶ T} {bh : R ⟶ P} {bi : P ⟶ R}
    {e : R ⟶ R} {m : P ⟶ Q} (hL : R = R) (hR hR' : P = Q)
    (ha : ai ≫ ah = 𝟙 T) (hc : ci ≫ c = 𝟙 Q) (hb : bh ≫ bi = 𝟙 R)
    (he : e = 𝟙 R) (hm : m = eqToHom hR')
    (h : ah ≫ c = eqToHom hL ≫ bh ≫ eqToHom hR) :
    bi ≫ e = m ≫ ci ≫ ai := by
  subst he hm hR
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
  have hbi : bi = ci ≫ ai ≫ bh ≫ bi := by
    rw [← h]
    simp only [Category.assoc, reassoc_of% ha, reassoc_of% hc]
  rw [hbi, hb, Category.comp_id]

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'}

/-- **Stacks 0CJC, étale clause, for a morphism of cartesian squares of algebraic spaces over a
thickening.** Let `ι : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks over `S`, and consider two
2-commutative squares exhibiting algebraic spaces `U = 𝒳 ×_{𝒳'} U'` and `V = 𝒳 ×_{𝒳'} V'`,
with right-hand legs `x' : U' ⟶ 𝒳'` flat and locally of finite presentation and
`y' : V' ⟶ 𝒳'` locally of finite type. Let `f : U ⟶ V` and `f' : U' ⟶ V'` be morphisms of
algebraic spaces with `f' ∘ i = j ∘ f` and `u = v ∘ f`, and `γ : x' ⟶ y' ∘ f'` a 2-morphism
compatible with the two fillers, `i^*γ ∘ α = f^*β`. If `f` is étale then so is `f'`.

This is `AlgebraicGeometry.Stack.isEtale_ambient_of_isEtale` at the base thickening `ι`, with
étaleness of morphisms of algebraic spaces matched to that of 1-morphisms of algebraic stacks by
`AlgebraicGeometry.Stack.isEtale_algebraicSpaceStackFunctor_map_iff`. -/
theorem isEtale_of_isTwoFibreProduct_of_isThickening (hι : IsThickening ι)
    {U U' V V' : AlgebraicSpaces B S hS} {i : U ⟶ U'} {j : V ⟶ V'}
    {u : (algebraicSpaceStackFunctor B S hS).obj U ⟶ 𝒳}
    {v : (algebraicSpaceStackFunctor B S hS).obj V ⟶ 𝒳}
    {x' : (algebraicSpaceStackFunctor B S hS).obj U' ⟶ 𝒳'}
    {y' : (algebraicSpaceStackFunctor B S hS).obj V' ⟶ 𝒳'}
    {α : u ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map i ≫ x'}
    {β : v ≫ ι ≅ (algebraicSpaceStackFunctor B S hS).map j ≫ y'}
    (hU : IsTwoFibreProduct
      (⟨(algebraicSpaceStackFunctor B S hS).obj U, u,
        (algebraicSpaceStackFunctor B S hS).map i, α⟩ : TwoCommSq ι x'))
    (hV : IsTwoFibreProduct
      (⟨(algebraicSpaceStackFunctor B S hS).obj V, v,
        (algebraicSpaceStackFunctor B S hS).map j, β⟩ : TwoCommSq ι y'))
    (hx'flat : AlgebraicStacks.IsFlat B S hS x')
    (hx'fp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS x')
    (hy'ft : AlgebraicStacks.IsLocallyOfFiniteType B S hS y')
    {f : U ⟶ V} {f' : U' ⟶ V'}
    (hu : u = (algebraicSpaceStackFunctor B S hS).map f ≫ v)
    (hL : u ≫ ι = (algebraicSpaceStackFunctor B S hS).map f ≫ (v ≫ ι))
    (hij : i ≫ f' = f ≫ j)
    (γ : x' ⟶ (algebraicSpaceStackFunctor B S hS).map f' ≫ y')
    (hR : (algebraicSpaceStackFunctor B S hS).map f ≫
        ((algebraicSpaceStackFunctor B S hS).map j ≫ y') =
      (algebraicSpaceStackFunctor B S hS).map i ≫
        ((algebraicSpaceStackFunctor B S hS).map f' ≫ y'))
    (hcoh : α.hom ≫ ((algebraicSpaceStackFunctor B S hS).map i ◁ γ) =
      eqToHom hL ≫ ((algebraicSpaceStackFunctor B S hS).map f ◁ β.hom) ≫ eqToHom hR)
    (hf : Space.IsEtale B S hS f.hom) :
    Space.IsEtale B S hS f'.hom := by
  subst hu
  have hmap : (algebraicSpaceStackFunctor B S hS).map f ≫
      (algebraicSpaceStackFunctor B S hS).map j =
      (algebraicSpaceStackFunctor B S hS).map i ≫ (algebraicSpaceStackFunctor B S hS).map f' := by
    rw [← Functor.map_comp, ← Functor.map_comp, hij]
  have hc : ((algebraicSpaceStackFunctor B S hS).map i ◁ inv γ) ≫
      ((algebraicSpaceStackFunctor B S hS).map i ◁ γ) = 𝟙 _ := by
    rw [← whiskerLeft_comp, IsIso.inv_hom_id, whiskerLeft_id]
  have hb : ((algebraicSpaceStackFunctor B S hS).map f ◁ β.hom) ≫
      ((algebraicSpaceStackFunctor B S hS).map f ◁ β.inv) = 𝟙 _ := by
    rw [← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id]
  refine (isEtale_algebraicSpaceStackFunctor_map_iff.{u, w} f').1 ?_
  refine isEtale_ambient_of_isEtale B S hS (PX := TwoCommSq.swap _) (PY := TwoCommSq.swap _)
    hι (isTwoFibreProduct_swap hU) (isTwoFibreProduct_swap hV) (asIso γ).symm (eqToIso hmap)
    (Iso.refl _) ?_ hy'ft hx'flat hx'fp
    ((isEtale_algebraicSpaceStackFunctor_map_iff.{u, w} f).2 hf)
  -- the compatibility of the cube is the coherence `hcoh`, inverted
  exact comp_eq_eqToHom_comp_of_comp_eq_eqToHom hL hR (congrArg (· ≫ y') hmap)
    (Iso.inv_hom_id α) hc hb
    (id_whiskerRight _ _) (eqToHom_whiskerRight hmap y') hcoh

variable {hι : IsThickening ι} {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift.Hom

/-- **Stacks 0CJS.** For a morphism `(f, f', γ)` of smooth lifts of étale opens of `W` along the
thickening `ι : 𝒳 ⟶ 𝒳'` (**Stacks 0CJP**), from `(U, U', a, i, x', α)` to
`(V, V', b, j, y', β)`, the component `f' : U' ⟶ V'` between the ambient algebraic spaces is
étale.

As in the source: `f` is étale as a morphism of the spaces-étale site of `W`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.isEtale_base`, **Stacks 03FV**), and the étale clause
of **Stacks 0CJC** applies
(`AlgebraicGeometry.Stack.isEtale_of_isTwoFibreProduct_of_isThickening`), because `x'` and `y'`
are smooth — hence flat and locally of finite presentation, resp. locally of finite type — and
`U = 𝒳 ×_{𝒳'} U'`, `V = 𝒳 ×_{𝒳'} V'` are the `isTwoFibreProduct` fields of the two smooth
lifts. -/
@[stacks 0CJS]
theorem isEtale_ambient (ξ η : EtaleSmoothLift B S hS ι hι W x hx) (m : ξ ⟶ η) :
    Space.IsEtale B S hS (Hom.ambient m).hom :=
  isEtale_of_isTwoFibreProduct_of_isThickening hι ξ.isTwoFibreProduct η.isTwoFibreProduct
    (AlgebraicStacks.isFlat_of_isSmooth B S hS _ ξ.isSmooth_ambientMap)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS _
      ξ.isSmooth_ambientMap)
    (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS _
        η.isSmooth_ambientMap))
    (congrArg (· ≫ x) (base_leg ξ η (Hom.base m))) (left_leg ξ η (Hom.base m))
    (Hom.inclusion_comp m) (Hom.comm m)
    (right_leg ξ η (Hom.base m) (Hom.ambient m) (Hom.inclusion_comp m))
    (Hom.coherence m) (isEtale_base ξ η m)

end EtaleSmoothLift.Hom

end AlgebraicGeometry.Stack

end
