module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.SmoothTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# Descending a local complete intersection morphism of algebraic spaces through a smooth morphism

In a commutative triangle `X ⟶ Y ⟶ Z` of algebraic spaces over `S`, if `Y ⟶ Z` is smooth and the
composite `X ⟶ Z` is a local complete intersection morphism, then `X ⟶ Y` is a local complete
intersection morphism. This is the algebraic-spaces form of Stacks 069M, whose schemes form is
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_comp_of_smooth`.

## Main results

* `AlgebraicGeometry.Space.isLocalCompleteIntersection_of_comp_of_isSmooth`: if `g : Y ⟶ Z` is
  smooth and `f ≫ g` is a local complete intersection morphism, then so is `f : X ⟶ Y`.

## Implementation notes

The commutative triangle is presented by taking the morphism `X ⟶ Z` to be the composite
`f ≫ g`; a triangle with an arbitrary third edge is the same statement after rewriting along the
commutativity.

## References

* [Stacks Project, Tag 0CHL](https://stacks.math.columbia.edu/tag/0CHL)
* [Stacks Project, Tag 069M](https://stacks.math.columbia.edu/tag/069M)
* [Stacks Project, Tag 069P](https://stacks.math.columbia.edu/tag/069P)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `P` and `Q` be properties of morphisms of schemes with `P` étale local on the source and
target, and suppose `P` can be cancelled on the right by `Q`: whenever `v` has `Q` and `u ≫ v`
has `P`, then `u` has `P`. Then the induced every-étale-chart properties cancel the same way for
morphisms of algebraic spaces over `S`. -/
private theorem holdsOnEveryEtaleChart_of_comp_of_holdsOnEveryEtaleChart
    (P Q : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hcancel : ∀ {A A' C : Scheme.{u}} (u : A ⟶ A') (v : A' ⟶ C), Q v → P (u ≫ v) → P u)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : HoldsOnEveryEtaleChart B S hS Q g)
    (hfg : HoldsOnEveryEtaleChart B S hS P (f ≫ g)) :
    HoldsOnEveryEtaleChart B S hS P f := by
  let T := BigFppfOver.toScheme B S hS
  let QSurjective : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) T
  let R := QSurjective.presheaf
  have : QSurjective.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition.{u}
  have : R.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition QSurjective
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨W, c, hcSurj, hcEtale⟩ := hZ.exists_atlas
  obtain ⟨U, a, α, hα, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  obtain ⟨V', d, β, hβ, hdSurj, hdEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hY hZ g W c hcSurj hcEtale
  let aY : yoneda.obj U ⟶ Y := yoneda.map α ≫ b
  let Zp := hdEtale.rep.pullback aY
  let p : Zp ⟶ V' := hdEtale.rep.fst' aY
  let q : Zp ⟶ U := hdEtale.rep.snd aY
  let A : yoneda.obj Zp ⟶ X := yoneda.map q ≫ a
  have hsq := hdEtale.rep.isPullback' aY
  have hpb : yoneda.map p ≫ d = yoneda.map q ≫ aY := hsq.w
  have hqEtale : AlgebraicGeometry.Etale (T.map q) := hdEtale.property aY (yoneda.map p) q hsq
  have hqSurj : AlgebraicGeometry.Surjective (T.map q) := hdSurj.property aY (yoneda.map p) q hsq
  have hAEtale := etale_comp_of_scheme B S hS q a hqEtale haEtale
  have hASurj : R A :=
    MorphismProperty.comp_mem R _ _
      ((presheaf_yoneda_map_iff B S hS inferInstance q).2 hqSurj) haSurj
  have hAf : yoneda.map p ≫ d = A ≫ f := by
    rw [hpb]
    simp only [A, aY, ← hα, Category.assoc]
  have hQβ : Q (T.map β) := hg V' W d c β hdEtale hcEtale hβ.symm
  have hPcomp : P (T.map (p ≫ β)) := by
    refine hfg Zp W A c (p ≫ β) hAEtale hcEtale ?_
    rw [Functor.map_comp, Category.assoc, ← hβ, ← Category.assoc, hAf, Category.assoc]
  have hPp : P (T.map p) :=
    hcancel (T.map p) (T.map β) hQβ (by simpa only [Functor.map_comp] using hPcomp)
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hX hY f).mpr
    ⟨Zp, V', A, d, p, hAEtale, hdEtale, hASurj, hAf, hPp⟩

/-- Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over `S` with `g` smooth.
If the composite `f ≫ g` is a local complete intersection morphism, then so is `f`. -/
@[stacks 0CHL]
public theorem isLocalCompleteIntersection_of_comp_of_isSmooth
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : IsSmooth B S hS g)
    (hfg : IsLocalCompleteIntersection B S hS (f ≫ g)) :
    IsLocalCompleteIntersection B S hS f :=
  holdsOnEveryEtaleChart_of_comp_of_holdsOnEveryEtaleChart B S hS
    (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
      MorphismProperty Scheme.{u})
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
    (isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism
      _root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale)
    (fun u v hv huv =>
      @_root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_comp_of_smooth _ _ _ u v hv
        huv)
    hX hY hZ f g hg hfg

end AlgebraicGeometry.Space

end
