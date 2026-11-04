module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The two projections of a charted self-intersection, as morphisms of schemes (Stacks 04SW)

Let `p : U ⟶ 𝒴` be a 1-morphism from the algebraic stack represented by a scheme `U` of the site,
let `P` be a 2-commutative square over the cospan `(p, p)` — for instance a 2-fibre product
`U ×_𝒴 U` — and let `F` be a presheaf representing its apex. A morphism `c : h_R ⟶ F` out of the
presheaf represented by a scheme `R` of the site, such as an étale chart of `F`, then yields two
*morphisms of schemes* `R ⟶ U`: the composites of `c` with the morphisms of representing
presheaves that **Stacks 04SW** reads off the two legs of `P`.

This module records the two properties of that pair which the square itself expresses: the two
composites `R ⟶ U ⟶ 𝒴` are 2-isomorphic — the 2-cell being the square's own filler, transported
along the uniqueness clause of Stacks 04SW — and, when `P` is a 2-fibre product of a smooth
1-morphism with itself and `c` is étale, both morphisms of schemes are smooth.

## Main definitions

* `AlgebraicGeometry.Stack.chartLeg`: the morphism of schemes `R ⟶ U` obtained from a leg of the
  square and the chart `c`.

## Main results

* `AlgebraicGeometry.Stack.nonempty_twoIso_of_representingMap_eq`: two 1-morphisms of algebraic
  stacks between represented objects inducing the same morphism of representing presheaves are
  2-isomorphic — the uniqueness clause of **Stacks 04SW** read in the 2-category of algebraic
  stacks.
* `AlgebraicGeometry.Stack.nonempty_twoIso_chartLeg`: a leg of the square, precomposed with a
  1-morphism inducing `c`, is 2-isomorphic to the 1-morphism attached to `chartLeg`.
* `AlgebraicGeometry.Stack.nonempty_twoIso_chartLeg_comp`: the two composites
  `R ⟶ U ⟶ 𝒴` are 2-isomorphic.
* `AlgebraicGeometry.Stack.smooth_chartLeg_of_isSmooth` and
  `AlgebraicGeometry.Stack.smooth_chartLeg`: `chartLeg` is a smooth morphism of schemes when the
  leg is a smooth 1-morphism and the chart is étale, which both legs are when `P` is a 2-fibre
  product of a smooth `p` with itself.

## Implementation notes

`AlgebraicGeometry.Stack.AlgebraicStacks` is an induced bicategory on a subtype of the
2-category of categories fibred in groupoids, so a 2-isomorphism of algebraic stacks is a
one-field wrapper around one of categories fibred in groupoids;
`CategoryTheory.Bicategory.InducedBicategory.isoMk` is that wrapper. Its implicit 1-morphisms
are passed explicitly: left to the expected type, the unifier would solve them by structure
literals that are only definitionally equal to the intended 1-morphisms.

The 1-morphism `m : R ⟶ P.pt` inducing `c` is not canonical — Stacks 04SW returns a
2-isomorphism class — so it is produced inside the proof by
`AlgebraicGeometry.Stack.exists_oneMorphism_representingMap_eq` and the conclusion does not
mention it. `AlgebraicGeometry.Stack.nonempty_twoIso_chartLeg` takes it as data so that the two
legs are compared through *one* choice of `m`, which is what makes the square's filler apply.

The étale hypothesis on `c` is stated in the form the atlas of
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas` provides it, namely the presheaf-level
inverse-image property of étale morphisms of schemes, rather than as
`AlgebraicGeometry.Space.IsEtale`; the two are related by
`AlgebraicGeometry.Space.isEtale_of_presheaf_etale`, which is applied here.

No `@[stacks]` attribute is claimed: these are consequences of Stacks 04SW, Stacks 06FM and
Stacks 075W, which are registered elsewhere, in the shape the self-intersection of a smooth
chart is used in.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 03ZD](https://stacks.math.columbia.edu/tag/03ZD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The uniqueness clause of Stacks 04SW, in the 2-category of algebraic stacks.** Two
1-morphisms of algebraic stacks whose sources and targets are represented by presheaves `F` and
`G` and which induce the same morphism `F ⟶ G` are 2-isomorphic.

This is `AlgebraicGeometry.Stack.nonempty_unique_twoIso_of_representingMap_eq`, whose statement
is about the underlying 1-morphisms of categories fibred in groupoids, wrapped by
`CategoryTheory.Bicategory.InducedBicategory.isoMk`. -/
theorem nonempty_twoIso_of_representingMap_eq {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    {f g : 𝒳 ⟶ 𝒴}
    (h : representingMap B S hS 𝒳.val 𝒴.val F G eF eG f.hom =
      representingMap B S hS 𝒳.val 𝒴.val F G eF eG g.hom) :
    Nonempty (f ≅ g) := by
  obtain ⟨uq⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS 𝒳.val 𝒴.val F G eF eG h
  exact ⟨Bicategory.InducedBicategory.isoMk (f := f) (g := g) uq.default⟩

variable {𝒴 : AlgebraicStacks.{u, w} B S hS} (U : BigFppfOver B S hS)
  (p : schemeStack.{u, w} B S hS U ⟶ 𝒴) (P : Bicategory.TwoCommSq p p)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver P.pt.val.val.p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ F)

/-- **A leg of a charted 2-commutative square, as a morphism of schemes.** The morphism of
representing presheaves that **Stacks 04SW** reads off a leg `P.pt ⟶ U` of the square,
precomposed with the chart `c : h_R ⟶ F`, is a morphism `h_R ⟶ h_U` of representable presheaves,
hence comes from a unique morphism `R ⟶ U` of the site by full faithfulness of the Yoneda
embedding. -/
noncomputable abbrev chartLeg (leg : P.pt ⟶ schemeStack.{u, w} B S hS U) : R ⟶ U :=
  yoneda.preimage (c ≫ representingMap B S hS P.pt.val
    (schemeStack.{u, w} B S hS U).val F (yoneda.obj U) eF (representedChart B S hS U) leg.hom)

/-- **The leg of a charted square is computed by `chartLeg`.** If `m : R ⟶ P.pt` is a
1-morphism inducing the chart `c`, then `m ≫ leg` is 2-isomorphic to the 1-morphism of
represented algebraic stacks attached to the morphism of schemes `chartLeg … leg`.

Both induce the same morphism of representing presheaves — the left-hand side by functoriality
of Stacks 04SW, the right-hand side by
`AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap` — so
`AlgebraicGeometry.Stack.nonempty_twoIso_of_representingMap_eq` applies. -/
theorem nonempty_twoIso_chartLeg (leg : P.pt ⟶ schemeStack.{u, w} B S hS U)
    (m : schemeStack.{u, w} B S hS R ⟶ P.pt)
    (hm : representingMap B S hS (schemeStack.{u, w} B S hS R).val P.pt.val
      (yoneda.obj R) F (representedChart B S hS R) eF m.hom = c) :
    Nonempty (m ≫ leg ≅ schemeStackMap B S hS (chartLeg B S hS U p P F eF R c leg)) := by
  refine nonempty_twoIso_of_representingMap_eq B S hS (yoneda.obj R) (yoneda.obj U)
    (representedChart B S hS R) (representedChart B S hS U) ?_
  have hcomp := representingMap_comp (𝒜 := (schemeStack.{u, w} B S hS R).val)
    (ℬ := P.pt.val) (𝒞 := (schemeStack.{u, w} B S hS U).val) B S hS
    (yoneda.obj R) F (yoneda.obj U) (representedChart B S hS R) eF
    (representedChart B S hS U) m.hom leg.hom
  rw [show (m ≫ leg).hom = m.hom ≫ leg.hom from rfl, hcomp, hm,
    show (schemeStackMap B S hS (chartLeg B S hS U p P F eF R c leg)).hom =
      schemeFibredCategoryMap B S hS (chartLeg B S hS U p P F eF R c leg) from rfl,
    representingMap_schemeFibredCategoryMap, Functor.map_preimage]

/-- **The two legs of a charted 2-commutative square agree after composing with `p`.** For a
2-commutative square `P` over the cospan `(p, p)` and a chart `c : h_R ⟶ F` of its apex, the two
morphisms of schemes `chartLeg … P.fst` and `chartLeg … P.snd` have 2-isomorphic composites
`R ⟶ U ⟶ 𝒴`.

This is the square's own filler `P.iso`, pulled back along a 1-morphism `m : R ⟶ P.pt` inducing
`c` and transported to the two legs by
`AlgebraicGeometry.Stack.nonempty_twoIso_chartLeg`. -/
theorem nonempty_twoIso_chartLeg_comp :
    Nonempty (schemeStackMap B S hS (chartLeg B S hS U p P F eF R c P.fst) ≫ p ≅
      schemeStackMap B S hS (chartLeg B S hS U p P F eF R c P.snd) ≫ p) := by
  obtain ⟨m, hm⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := schemeStack.{u, w} B S hS R) (𝒴 := P.pt)
    (yoneda.obj R) F (representedChart B S hS R) eF c
  obtain ⟨e₁⟩ := nonempty_twoIso_chartLeg B S hS U p P F eF R c P.fst m hm
  obtain ⟨e₂⟩ := nonempty_twoIso_chartLeg B S hS U p P F eF R c P.snd m hm
  exact ⟨(Bicategory.whiskerRightIso e₁ p).symm ≪≫ (Bicategory.associator m P.fst p) ≪≫
    Bicategory.whiskerLeftIso m P.iso ≪≫ (Bicategory.associator m P.snd p).symm ≪≫
    Bicategory.whiskerRightIso e₂ p⟩

/-- **A leg of a charted square is a smooth morphism of schemes as soon as it is a smooth
1-morphism and the chart is étale.** By **Stacks 06FM** (here
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_represented`) the morphism of
representing presheaves that Stacks 04SW reads off the leg is a smooth morphism of algebraic
spaces; composing with the étale chart keeps it smooth (**Stacks 03ZD**), and smoothness of a
morphism of representable algebraic spaces is smoothness of the morphism of schemes
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`). -/
theorem smooth_chartLeg_of_isSmooth (hF : IsAlgebraicSpace B S hS F)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (leg : P.pt ⟶ schemeStack.{u, w} B S hS U)
    (hleg : AlgebraicStacks.IsSmooth B S hS leg) :
    Smooth ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c leg)) := by
  have hrep : Space.IsSmooth B S hS (representingMap B S hS P.pt.val
      (schemeStack.{u, w} B S hS U).val F (yoneda.obj U) eF (representedChart B S hS U)
      leg.hom) :=
    (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) P.pt.property
      (schemeStack.{u, w} B S hS U).property F (yoneda.obj U) hF
      (isAlgebraicSpace_yoneda B S hS U) eF (representedChart B S hS U) leg.hom).mp hleg
  have hcomp : Space.IsSmooth B S hS
      (yoneda.map (chartLeg B S hS U p P F eF R c leg)) := by
    rw [Functor.map_preimage]
    exact Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS R) hF
      (isAlgebraicSpace_yoneda B S hS U) c _
      (Space.isSmooth_of_isEtale B S hS hF (Space.isEtale_of_presheaf_etale B S hS hc)) hrep
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    Smooth.isEtaleLocalOnSourceAndTarget (chartLeg B S hS U p P F eF R c leg)).mp hcomp

/-- **Both legs of a charted 2-fibre product of a smooth 1-morphism with itself are smooth
morphisms of schemes.** Each leg is a base change of the smooth `p` (**Stacks 075W**, here
`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_baseChange`, applied to the square and to its
swap), so `AlgebraicGeometry.Stack.smooth_chartLeg_of_isSmooth` applies to both. -/
theorem smooth_chartLeg (hF : IsAlgebraicSpace B S hS F)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (hp : AlgebraicStacks.IsSmooth B S hS p) (hP : Bicategory.IsTwoFibreProduct P) :
    Smooth ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.fst)) ∧
      Smooth ((BigFppfOver.toScheme B S hS).map
        (chartLeg B S hS U p P F eF R c P.snd)) :=
  ⟨smooth_chartLeg_of_isSmooth B S hS U p P F eF R c hF hc P.fst
      (AlgebraicStacks.isSmooth_baseChange B S hS p p P hP hp),
    smooth_chartLeg_of_isSmooth B S hS U p P F eF R c hF hc P.snd
      (AlgebraicStacks.isSmooth_baseChange B S hS p p P.swap
        (Bicategory.isTwoFibreProduct_swap hP) hp)⟩

end AlgebraicGeometry.Stack

end
