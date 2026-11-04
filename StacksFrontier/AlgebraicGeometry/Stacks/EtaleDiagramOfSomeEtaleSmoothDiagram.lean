module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedEtaleDiagram

/-!
# The existential étale-smooth diagram criterion tests every étale diagram (Stacks 0CIF, 0CIY)

Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on the
source-and-target (**Stacks 0CFZ**) and, in addition, stable under *arbitrary* base change, and
let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. This file proves that one diagram
of condition (2) of **Stacks 0CIF** over `f` — smooth right-hand vertical 1-morphism, surjective
left-hand vertical 1-morphism, étale comparison to the 2-fibre product, top horizontal morphism
with `P` — forces `P` on the top horizontal morphism of *every* diagram over `f` with étale
comparison to the 2-fibre product, whether or not its right-hand vertical 1-morphism is smooth.
That is the diagram test `AlgebraicGeometry.Stack.HasPropertyOnEveryEtaleDiagram` of condition (2)
of **Stacks 0CIY**, at `P`.

## Main results

* `AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_comp_etale_of_baseChange`: the
  base change of a top horizontal morphism with `P` along an arbitrary 1-morphism, precomposed
  with an étale morphism, has `P`.
* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram`:
  the statement above.

## Implementation notes

The proof is the chase of
`Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram`
(condition (2) ⇒ condition (1) of Stacks 0CIF), and the reason it goes through for an arbitrary
right-hand vertical 1-morphism `b' : V' ⟶ 𝒴` of the arbitrary diagram is that smoothness of `b'`
enters that chase at exactly two places, both of which have a substitute here:

* the projection `V' ×_𝒴 𝒳 ⟶ 𝒳` is representable by algebraic spaces. That chase reads this off
  smoothness of `b'`; here it is read off `b'` itself, which is a 1-morphism from an algebraic
  space to an algebraic stack and hence representable by algebraic spaces because the diagonal of
  `𝒴` is (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`).
* the top horizontal morphism `U ⟶ V` of the given diagram is base changed along the projection
  `V' ×_𝒴 V ⟶ V`, which is the base change of `b'`. That chase needs this projection to be smooth
  because an étale-smooth local property is only stable under *smooth* base change; here `P` is
  assumed stable under every base change, which is the hypothesis `hbc`, and the base change step
  is `AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_comp_etale_of_baseChange`.

Smoothness of the *given* diagram's right-hand vertical 1-morphism is still used, exactly as
there: it makes the descent step at the end — **Stacks 0CG1**, (c) ⇒ (a) — apply.

No `@[stacks]` attribute: the statement is the engine of the étale case of **Stacks 0CIN** and is
not an assertion of the source on its own.

## References

* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CG1](https://stacks.math.columbia.edu/tag/0CG1)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIN](https://stacks.math.columbia.edu/tag/0CIN)
* [Stacks Project, Tag 0CIY](https://stacks.math.columbia.edu/tag/0CIY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The base change of a top horizontal morphism with `P`, for a base-change-stable `P`.** Let
`P` be étale-smooth local on the source-and-target and stable under base change, let
`hTop : U ⟶ V` have `P`, let `s : 𝒮 ⟶ V` be an arbitrary 1-morphism out of a category fibred in
groupoids over the big fppf site of `S`, and form the canonical 2-fibre product `𝒮 ×_V U`. Then
every étale morphism of algebraic spaces into the representing presheaf of that 2-fibre product,
composed with the morphism induced by its projection to `𝒮`, has `P`.

This is `AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_comp_etale` with the
smoothness of `s` dropped and smooth base change replaced by base change: under **Stacks 04SD**
the projection to `𝒮` is the pullback projection of `hTop` along the morphism induced by `s`. -/
theorem prop_representingMap_twoFibreProductFst_comp_etale_of_baseChange
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    (hbc : ∀ {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y), P f → ∀ (b : Y' ⟶ Y),
      P (ObjectProperty.homMk (pullback.snd f.hom b.hom) :
        AlgebraicSpaces.fiberProduct B S hS f b ⟶ Y'))
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (hTop : U ⟶ V)
    (hPtop : P (ObjectProperty.homMk hTop : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩))
    {𝒮 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (s : 𝒮 ⟶ fibredCategory B S hS V)
    (W₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW₃ : IsAlgebraicSpace B S hS W₃)
    (eW₃ : StacksRepresentableCFG.EquivalenceOver 𝒮.val.p
      (presheafOfCategories (W₃ ⋙ typeToCat)).p)
    (W₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hW₂ : IsAlgebraicSpace B S hS W₂)
    (eW₂ : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS 𝒮 (fibredCategory B S hS U)
        (fibredCategory B S hS V) s (associatedMap B S hS hTop).1)
      (presheafOfCategories (W₂ ⋙ typeToCat)).p)
    {WE : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hWE : IsAlgebraicSpace B S hS WE)
    (q : WE ⟶ W₂) (hq : Space.IsEtale B S hS q) :
    P (ObjectProperty.homMk (q ≫ representingMap B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
        (associatedMap B S hS hTop).1).pt 𝒮 W₂ W₃ eW₂ eW₃
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
        (associatedMap B S hS hTop).1).fst) :
      (⟨WE, hWE⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W₃, hW₃⟩) := by
  classical
  let β := representingMap B S hS 𝒮 (fibredCategory B S hS V) W₃ V eW₃
    (StacksRepresentableCFG.EquivalenceOver.refl _) s
  let hTopR := representingMap B S hS (fibredCategory B S hS U) (fibredCategory B S hS V) U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (associatedMap B S hS hTop).1
  have hrepTop : hTopR = hTop := representingMap_associatedMap B S hS U V hTop
  have hPtopR : P (ObjectProperty.homMk hTopR :
      (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩) := by
    rwa [hrepTop]
  -- Stacks 04SD: the representing presheaf of the 2-fibre product is the fibre product
  let _hfibered : (twoFibreProductStructureFunctor B S hS 𝒮 (fibredCategory B S hS U)
      (fibredCategory B S hS V) s (associatedMap B S hS hTop).1).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
      (associatedMap B S hS hTop).1).pt.property.isFibered
  let hfib : Presheaf.fibreProduct β hTopR ≅ W₂ :=
    fibreProductIsoRepresenting B S hS 𝒮 (fibredCategory B S hS U) (fibredCategory B S hS V)
      W₃ U V eW₃ (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) s (associatedMap B S hS hTop).1 W₂ eW₂
  have hfst : hfib.hom ≫ representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).pt 𝒮 W₂ W₃ eW₂ eW₃
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).fst =
      Presheaf.fibreProductFst β hTopR :=
    fibreProductIsoRepresenting_hom_comp_representingMap_fst B S hS 𝒮
      (fibredCategory B S hS U) (fibredCategory B S hS V) W₃ U V eW₃
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) s (associatedMap B S hS hTop).1 W₂ eW₂
  -- and therefore the pullback of `hTop` along the smooth morphism induced by `s`
  let ι := hfib.symm ≪≫ (Presheaf.isPullback_fibreProduct β hTopR).flip.isoPullback
  have hιsnd : ι.hom ≫ pullback.snd hTopR β =
      representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).pt 𝒮 W₂ W₃ eW₂ eW₃
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).fst := by
    have hιhom : ι.hom =
        hfib.inv ≫ (Presheaf.isPullback_fibreProduct β hTopR).flip.isoPullback.hom := rfl
    rw [hιhom, Category.assoc,
      (Presheaf.isPullback_fibreProduct β hTopR).flip.isoPullback_hom_snd, ← hfst,
      Iso.inv_hom_id_assoc]
  have hqιet : Space.IsEtale B S hS (q ≫ ι.hom) :=
    Space.isEtale_comp B S hS hq (Space.isEtale_of_isIso B S hS ι.hom)
  -- base change, then the étale precomposition field of Stacks 0CFZ
  let fU : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩ := ObjectProperty.homMk hTopR
  let fV : (⟨W₃, hW₃⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩ := ObjectProperty.homMk β
  have hbase := hbc fU hPtopR fV
  have hpre := hP.precomp_of_etale
    (ObjectProperty.homMk (q ≫ ι.hom) :
      (⟨WE, hWE⟩ : AlgebraicSpaces B S hS) ⟶ AlgebraicSpaces.fiberProduct B S hS fU fV)
    (ObjectProperty.homMk (pullback.snd fU.hom fV.hom) :
      AlgebraicSpaces.fiberProduct B S hS fU fV ⟶ ⟨W₃, hW₃⟩) hqιet hbase
  have hgoal : (q ≫ ι.hom) ≫ pullback.snd hTopR β =
      q ≫ representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).pt 𝒮 W₂ W₃ eW₂ eW₃
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} s
          (associatedMap B S hS hTop).1).fst :=
    (Category.assoc q ι.hom (pullback.snd hTopR β)).trans (congrArg (fun t => q ≫ t) hιsnd)
  exact hgoal ▸ hpre

/-- The representing morphism of a triple composite is the triple composite of the representing
morphisms. -/
private theorem representingMap_comp_comp
    {𝒜 ℬ 𝒞 𝒟 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver ℬ.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver 𝒞.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    (eK : StacksRepresentableCFG.EquivalenceOver 𝒟.val.p (presheafOfCategories (K ⋙ typeToCat)).p)
    (a : 𝒜 ⟶ ℬ) (b : ℬ ⟶ 𝒞) (c : 𝒞 ⟶ 𝒟) :
    representingMap B S hS 𝒜 𝒟 F K eF eK (a ≫ b ≫ c) =
      representingMap B S hS 𝒜 ℬ F G eF eG a ≫ (representingMap B S hS ℬ 𝒞 G H eG eH b ≫
        representingMap B S hS 𝒞 𝒟 H K eH eK c) := by
  rw [representingMap_comp B S hS F G K eF eG eK, representingMap_comp B S hS G H K eG eH eK]

/-- Two factorisations of a 1-morphism through different middle objects, which agree up to a
2-isomorphism, give equal composites of representing morphisms. -/
private theorem representingMap_comp_eq_of_twoIso_comp
    {𝒜 ℬ ℬ' 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G G' H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver ℬ.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (eG' : StacksRepresentableCFG.EquivalenceOver ℬ'.val.p
      (presheafOfCategories (G' ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver 𝒞.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    {a : 𝒜 ⟶ ℬ} {c : ℬ ⟶ 𝒞} {a' : 𝒜 ⟶ ℬ'} {c' : ℬ' ⟶ 𝒞} (ι : a ≫ c ≅ a' ≫ c') :
    representingMap B S hS 𝒜 ℬ F G eF eG a ≫ representingMap B S hS ℬ 𝒞 G H eG eH c =
      representingMap B S hS 𝒜 ℬ' F G' eF eG' a' ≫ representingMap B S hS ℬ' 𝒞 G' H eG' eH c' := by
  rw [← representingMap_comp, ← representingMap_comp]
  exact representingMap_congr_twoIso B S hS F H eF eH ι

/-- A 2-isomorphism from a 1-morphism to a composite of two 1-morphisms identifies its representing
morphism with the composite of the representing morphisms. -/
private theorem representingMap_eq_comp_of_twoIso
    {𝒜 ℬ 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver ℬ.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver 𝒞.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    {a : 𝒜 ⟶ 𝒞} {b : 𝒜 ⟶ ℬ} {c : ℬ ⟶ 𝒞} (ι : a ≅ b ≫ c) :
    representingMap B S hS 𝒜 𝒞 F H eF eH a =
      representingMap B S hS 𝒜 ℬ F G eF eG b ≫ representingMap B S hS ℬ 𝒞 G H eG eH c :=
  (representingMap_congr_twoIso B S hS F H eF eH ι).trans
    (representingMap_comp B S hS F G H eF eG eH b c)

/-- **The existential étale-smooth diagram criterion tests every étale diagram.** Let `P` be
étale-smooth local on the source-and-target and stable under base change. If some diagram of
algebraic spaces over `f : 𝒳 ⟶ 𝒴` with smooth right-hand vertical 1-morphism, surjective
left-hand vertical 1-morphism and étale comparison to every 2-fibre product of its cospan has `P`
on its top horizontal morphism, then *every* diagram with étale comparison to every 2-fibre
product of its cospan has `P` on its top horizontal morphism — its right-hand vertical
1-morphism need not be smooth.

The chase is that of
`Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram`;
the two places where it uses smoothness of the arbitrary diagram's right-hand vertical
1-morphism are replaced as described in the implementation notes of this module. -/
theorem hasPropertyOnEveryEtaleDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    (hbc : ∀ {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y), P f → ∀ (b : Y' ⟶ Y),
      P (ObjectProperty.homMk (pullback.snd f.hom b.hom) :
        AlgebraicSpaces.fiberProduct B S hS f b ⟶ Y'))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hsome : HasPropertyOnSomeEtaleSmoothDiagram B S hS P f) :
    HasPropertyOnEveryEtaleDiagram B S hS P f := by
  classical
  obtain ⟨U, V, hU, hV, a, b, hTop, η, hasu, hbsm, hcompar, hPtop⟩ := hsome
  intro U' V' hU' hV' a' b' h' η' hcompar'
  let hM := (associatedMap B S hS hTop).1
  let hM' := (associatedMap B S hS h').1
  let DC := diagramCone B S hS f.hom a.hom b.hom hTop η
  let DC' := diagramCone B S hS f.hom a'.hom b'.hom h' η'
  let J := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom
  let KK := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b'.hom f.hom
  have hJ : Bicategory.IsTwoFibreProduct J :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom
  have hKK : Bicategory.IsTwoFibreProduct KK :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b'.hom f.hom
  let m := CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} b.hom f.hom DC
  let k := CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} b'.hom f.hom DC'
  have hmet : IsRelativelyEtale B S hS m.hom := hcompar J hJ m
  have hket : IsRelativelyEtale B S hS k.hom := hcompar' KK hKK k
  let T₁ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} KK.snd a.hom
  let GG := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} J.snd a'.hom
  let Sq₃ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b'.hom b.hom
  let T₂ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Sq₃.snd hM
  let F' := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Sq₃.fst hM'
  let E := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} T₁.fst k.hom
  let E₂ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} GG.fst m.hom
  have hSq₃ : Bicategory.IsTwoFibreProduct Sq₃ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b'.hom b.hom
  -- the cancellations
  let A := CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} b'.hom f.hom a.hom
    (a.hom ≫ f.hom) (Iso.refl _)
  let D := CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} b'.hom b.hom hM
    (a.hom ≫ f.hom) η
  let A₂ := CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} b.hom f.hom a'.hom
    (a'.hom ≫ f.hom) (Iso.refl _)
  let D₂ := CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} b'.hom b.hom hM'
    (a'.hom ≫ f.hom) η'
  let Ecan := CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} KK.snd a.hom k.hom
    a'.hom k.isoSnd.symm
  let E₂can := CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} J.snd a'.hom m.hom
    a.hom m.isoSnd.symm
  have hD : Bicategory.IsTwoFibreProduct D :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} b'.hom b.hom hM
      (a.hom ≫ f.hom) η
  have hA₂ : Bicategory.IsTwoFibreProduct A₂ :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} b.hom f.hom
      a'.hom (a'.hom ≫ f.hom) (Iso.refl _)
  have hD₂ : Bicategory.IsTwoFibreProduct D₂ :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1} b'.hom b.hom hM'
      (a'.hom ≫ f.hom) η'
  have hE₂can : Bicategory.IsTwoFibreProduct E₂can :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1} J.snd a'.hom
      m.hom a.hom m.isoSnd.symm
  have hEcanSwap : Bicategory.IsTwoFibreProduct Ecan.swap :=
    Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1} KK.snd a.hom
        k.hom a'.hom k.isoSnd.symm)
  let cmp := Quotient.out (hD.from A)
  let cmp₂ := Quotient.out (hD₂.from A₂)
  let wcmp := Quotient.out (hE₂can.from Ecan.swap)
  -- route A
  let X := (Ecan.postcompose f.hom hM hM' η η').swap
  let Y := E₂can.postcompose f.hom hM' hM η' η
  let uA2 := (CatFiberedInGroupoids.cancelFstPostcomposePreHom.{u, u, u + 1, u + 1} b'.hom b.hom
    f.hom a.hom hM η DC' k).swap
  let uA1 := cmp.postcomposeSnd hM η
  let uA0 := CatFiberedInGroupoids.cancelSndPostcomposeSndPreHom.{u, u, u + 1, u + 1} b'.hom
    b.hom hM (a.hom ≫ f.hom) η
  let uA : Bicategory.TwoCommSq.PreHom X Sq₃ := uA2.comp (uA1.comp uA0)
  have huAhom : uA.hom = E.fst ≫ (cmp.hom ≫ T₂.fst) := rfl
  have huAfst : X.fst = E.snd ≫ hM' := rfl
  -- route B
  let uB3₀ := wcmp.postcompose f.hom hM' hM η' η
  let uB2 := CatFiberedInGroupoids.cancelFstPostcomposePreHom.{u, u, u + 1, u + 1} b.hom b'.hom
    f.hom a'.hom hM' η' DC m
  let uB1 := (cmp₂.postcomposeSnd hM' η').swap
  let uB0 := CatFiberedInGroupoids.cancelFstPostcomposeSndPreHom.{u, u, u + 1, u + 1} b'.hom
    b.hom hM' (a'.hom ≫ f.hom) η'
  let uB3 : Bicategory.TwoCommSq.PreHom X Y :=
    { hom := uB3₀.hom
      isoFst := uB3₀.isoFst
      isoSnd := uB3₀.isoSnd
      compat := by
        rw [show X.iso.hom = (Ecan.swap.postcompose f.hom hM' hM η' η).iso.hom from
          CatFiberedInGroupoids.swap_postcompose_iso_hom.{u, u, u + 1, u + 1} Ecan f.hom hM hM'
            η η']
        exact uB3₀.compat }
  let uB : Bicategory.TwoCommSq.PreHom X Sq₃ := uB3.comp (uB2.comp (uB1.comp uB0))
  have huBhom : uB.hom = wcmp.hom ≫ (E₂.fst ≫ (cmp₂.hom ≫ F'.fst)) := rfl
  -- ### Representability of the pieces
  have hUrep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS U) :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU
  have hU'rep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS U') :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS U' hU'
  have hV'rep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS V') :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS V' hV'
  have hVrep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS V) :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV
  have harep : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property hUrep a.hom
  have ha'rep : IsRepresentableByAlgebraicSpaces B S hS a'.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property hU'rep a'.hom
  have hMrep : IsRepresentableByAlgebraicSpaces B S hS hM.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS hM hUrep hVrep
  have hM'rep : IsRepresentableByAlgebraicSpaces B S hS hM'.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS hM' hU'rep hV'rep
  have hKKsndrep : IsRepresentableByAlgebraicSpaces B S hS KK.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS b'.hom f.hom
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴.property hV'rep
        b'.hom)
  have hJsndrep : IsRepresentableByAlgebraicSpaces B S hS J.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS b.hom f.hom hbsm.1
  have hT₁ : Bicategory.IsTwoFibreProduct T₁ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} KK.snd
      a.hom
  have hGGsq : Bicategory.IsTwoFibreProduct GG :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} J.snd
      a'.hom
  have hE : Bicategory.IsTwoFibreProduct E :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} T₁.fst
      k.hom
  have hE₂ : Bicategory.IsTwoFibreProduct E₂ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} GG.fst
      m.hom
  have hT₂ : Bicategory.IsTwoFibreProduct T₂ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} Sq₃.snd hM
  have hF'sq : Bicategory.IsTwoFibreProduct F' :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} Sq₃.fst hM'
  have hT₁fstrep : IsRepresentableByAlgebraicSpaces B S hS T₁.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS U) 𝒳.val KK.pt a.hom KK.snd T₁ hT₁ harep
  have hGGfstrep : IsRepresentableByAlgebraicSpaces B S hS GG.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS U') 𝒳.val J.pt a'.hom J.snd GG hGGsq ha'rep
  have hT₁sndrep : IsRepresentableByAlgebraicSpaces B S hS T₁.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS KK.snd a.hom hKKsndrep
  have hGGsndrep : IsRepresentableByAlgebraicSpaces B S hS GG.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS J.snd a'.hom hJsndrep
  have hT₁rep : IsRepresentableByAlgebraicSpace B S hS T₁.pt :=
    isRepresentableByAlgebraicSpace_of_representable B S hS T₁.pt (fibredCategory B S hS U)
      T₁.snd hT₁sndrep hUrep
  have hGGrep : IsRepresentableByAlgebraicSpace B S hS GG.pt :=
    isRepresentableByAlgebraicSpace_of_representable B S hS GG.pt (fibredCategory B S hS U')
      GG.snd hGGsndrep hU'rep
  have hSq₃rep : IsRepresentableByAlgebraicSpace B S hS Sq₃.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS V) 𝒴.val (fibredCategory B S hS V') b.hom b'.hom Sq₃ hSq₃ hbsm.1
      hV'rep
  have hT₂rep : IsRepresentableByAlgebraicSpace B S hS T₂.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS U) (fibredCategory B S hS V) Sq₃.pt hM Sq₃.snd T₂ hT₂ hMrep hSq₃rep
  have hF'rep : IsRepresentableByAlgebraicSpace B S hS F'.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS U') (fibredCategory B S hS V') Sq₃.pt hM' Sq₃.fst F' hF'sq hM'rep
      hSq₃rep
  have hEsndrep : IsRepresentableByAlgebraicSpaces B S hS E.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS T₁.fst k.hom hT₁fstrep
  have hE₂sndrep : IsRepresentableByAlgebraicSpaces B S hS E₂.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS GG.fst m.hom hGGfstrep
  have hErep : IsRepresentableByAlgebraicSpace B S hS E.pt :=
    isRepresentableByAlgebraicSpace_of_representable B S hS E.pt (fibredCategory B S hS U')
      E.snd hEsndrep hU'rep
  have hE₂rep : IsRepresentableByAlgebraicSpace B S hS E₂.pt :=
    isRepresentableByAlgebraicSpace_of_representable B S hS E₂.pt (fibredCategory B S hS U)
      E₂.snd hE₂sndrep hUrep
  -- ### Étaleness and smoothness of the projections used
  have hEfstet : IsRelativelyEtale B S hS E.fst :=
    isRelativelyEtale_baseChange B S hS (fibredCategory B S hS U') KK.pt T₁.pt k.hom T₁.fst E hE
      hket
  have hE₂fstet : IsRelativelyEtale B S hS E₂.fst :=
    isRelativelyEtale_baseChange B S hS (fibredCategory B S hS U) J.pt GG.pt m.hom GG.fst E₂ hE₂
      hmet
  have hSq₃fstsm : IsRelativelySmooth B S hS Sq₃.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V) 𝒴.val
      (fibredCategory B S hS V') b.hom b'.hom Sq₃ hSq₃ hbsm
  -- ### Surjectivity on objects of `E.snd`
  have haSu : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) a.hom harep :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1} B S hS a harep).1 hasu
  have hT₁fstsu : IsSurjectiveOnObjects B S hS T₁.pt.val.p KK.pt.val.p
      (CatFiberedInGroupoids.homFunctor T₁.fst) :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS T₁.fst
      hT₁fstrep).2
      (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) (fibredCategory B S hS U) 𝒳.val KK.pt a.hom
        KK.snd T₁ hT₁ harep haSu)
  have hEsndsu : IsSurjectiveOnObjects B S hS E.pt.val.p (fibredCategory B S hS U').val.p
      (CatFiberedInGroupoids.homFunctor E.snd) :=
    isSurjectiveOnObjects_twoFibreProductSnd.{u, u, u} B S hS T₁.pt KK.pt
      (fibredCategory B S hS U') T₁.fst k.hom hT₁fstsu
  -- ### The representing presheaves
  obtain ⟨W₂, hW₂, ⟨eW₂⟩⟩ := hT₂rep
  obtain ⟨W₃, hW₃, ⟨eW₃⟩⟩ := hSq₃rep
  obtain ⟨W₁, hW₁, ⟨eW₁⟩⟩ := hT₁rep
  obtain ⟨WG, hWG, ⟨eWG⟩⟩ := hGGrep
  obtain ⟨WF, hWF, ⟨eWF⟩⟩ := hF'rep
  obtain ⟨WE, hWE, ⟨eWE⟩⟩ := hErep
  obtain ⟨WE₂, hWE₂, ⟨eWE₂⟩⟩ := hE₂rep
  let eU' : StacksRepresentableCFG.EquivalenceOver (fibredCategory B S hS U').val.p
    (presheafOfCategories (U' ⋙ typeToCat)).p := StacksRepresentableCFG.EquivalenceOver.refl _
  let eV' : StacksRepresentableCFG.EquivalenceOver (fibredCategory B S hS V').val.p
    (presheafOfCategories (V' ⋙ typeToCat)).p := StacksRepresentableCFG.EquivalenceOver.refl _
  -- ### The four morphisms of algebraic spaces of the final diagram
  let φ := representingMap B S hS (fibredCategory B S hS U') (fibredCategory B S hS V') U' V'
    eU' eV' hM'
  let β := representingMap B S hS Sq₃.pt (fibredCategory B S hS V') W₃ V' eW₃ eV' Sq₃.fst
  let α := representingMap B S hS E.pt (fibredCategory B S hS U') WE U' eWE eU' E.snd
  let hh := representingMap B S hS E.pt Sq₃.pt WE W₃ eWE eW₃ uA.hom
  -- ### `β` is smooth, `α` is surjective on points
  have hβsm : Space.IsSmooth B S hS β :=
    (isRelativelySmooth_iff_isSmooth_representingMap B S hS Sq₃.fst hSq₃fstsm.1 W₃ V' hW₃ hV' eW₃
      eV').1 hSq₃fstsm
  have hαsurj : Space.IsSurjective B S hS α :=
    isSurjective_representingMap_of_isSurjectiveOnObjects B S hS E.snd WE U' eWE eU' hEsndsu
  -- ### The top horizontal morphism has `P`
  have hEfstEt : Space.IsEtale B S hS
      (representingMap B S hS E.pt T₁.pt WE W₁ eWE eW₁ E.fst) :=
    isEtale_representingMap_of_isRelativelyEtale B S hS E.fst hEfstet.1 WE W₁ hWE hW₁ eWE eW₁
      hEfstet
  have hcmpiso : IsIso (representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom) :=
    isIso_representingMap_preHom_of_isTwoFibreProduct B S hS
      (CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} b'.hom f.hom
        a.hom (a.hom ≫ f.hom) (Iso.refl _)) hD cmp W₁ W₂ eW₁ eW₂
  have hcmpEt : Space.IsEtale B S hS
      (representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom) :=
    Space.isEtale_of_isIso B S hS
      (representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom)
  have hPk := prop_representingMap_twoFibreProductFst_comp_etale_of_baseChange B S hS P hP hbc
    hU hV hTop hPtop Sq₃.snd W₃ hW₃ eW₃ W₂ hW₂ eW₂ hWE
    (representingMap B S hS E.pt T₁.pt WE W₁ eWE eW₁ E.fst ≫
      representingMap B S hS T₁.pt T₂.pt W₁ W₂ eW₁ eW₂ cmp.hom)
    (Space.isEtale_comp B S hS hEfstEt hcmpEt)
  have hPh : P (ObjectProperty.homMk hh : (⟨WE, hWE⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W₃, hW₃⟩) := by
    rwa [show hh = _ from representingMap_comp_comp B S hS WE W₁ W₂ W₃ eWE eW₁ eW₂ eW₃ E.fst
      cmp.hom T₂.fst, ← Category.assoc]
  -- ### The final square commutes
  have hcomm : α ≫ φ = hh ≫ β :=
    representingMap_comp_eq_of_twoIso_comp B S hS WE U' W₃ V' eWE eU' eW₃ eV' uA.isoFst
  -- ### The comparison into the fibre product is étale
  let δ := wcmp.hom ≫ (E₂.fst ≫ cmp₂.hom)
  have hδrep : representingMap B S hS E.pt F'.pt WE WF eWE eWF δ =
      representingMap B S hS E.pt E₂.pt WE WE₂ eWE eWE₂ wcmp.hom ≫
        (representingMap B S hS E₂.pt GG.pt WE₂ WG eWE₂ eWG E₂.fst ≫
          representingMap B S hS GG.pt F'.pt WG WF eWG eWF cmp₂.hom) :=
    representingMap_comp_comp B S hS WE WE₂ WG WF eWE eWE₂ eWG eWF wcmp.hom E₂.fst cmp₂.hom
  have hwcmpiso : IsIso (representingMap B S hS E.pt E₂.pt WE WE₂ eWE eWE₂ wcmp.hom) :=
    isIso_representingMap_preHom_of_isTwoFibreProduct B S hS hEcanSwap hE₂can wcmp WE WE₂ eWE eWE₂
  have hcmp₂iso : IsIso (representingMap B S hS GG.pt F'.pt WG WF eWG eWF cmp₂.hom) :=
    isIso_representingMap_preHom_of_isTwoFibreProduct B S hS hA₂ hD₂ cmp₂ WG WF eWG eWF
  have hδEt : Space.IsEtale B S hS (representingMap B S hS E.pt F'.pt WE WF eWE eWF δ) := by
    rw [hδrep]
    exact Space.isEtale_comp B S hS
      (Space.isEtale_of_isIso B S hS
        (representingMap B S hS E.pt E₂.pt WE WE₂ eWE eWE₂ wcmp.hom))
      (Space.isEtale_comp B S hS
        (isEtale_representingMap_of_isRelativelyEtale B S hS E₂.fst hE₂fstet.1 WE₂ WG hWE₂ hWG
          eWE₂ eWG hE₂fstet)
        (Space.isEtale_of_isIso B S hS
          (representingMap B S hS GG.pt F'.pt WG WF eWG eWF cmp₂.hom)))
  have hsqF : representingMap B S hS F'.pt (fibredCategory B S hS U') WF U' eWF eU' F'.snd ≫ φ
      = representingMap B S hS F'.pt Sq₃.pt WF W₃ eWF eW₃ F'.fst ≫ β :=
    representingMap_comp_eq_of_twoIso_comp B S hS WF U' W₃ V' eWF eU' eW₃ eV' F'.iso.symm
  let _hfib : (twoFibreProductStructureFunctor B S hS Sq₃.pt (fibredCategory B S hS U')
    (fibredCategory B S hS V') Sq₃.fst hM').IsFibered := F'.pt.property.isFibered
  let cF := pullback.lift
      (representingMap B S hS F'.pt (fibredCategory B S hS U') WF U' eWF eU' F'.snd)
      (representingMap B S hS F'.pt Sq₃.pt WF W₃ eWF eW₃ F'.fst) hsqF
  have hFiso : IsIso cF :=
    isIso_of_fibreProduct_projections B S hS β φ cF
      (fibreProductIsoRepresenting B S hS Sq₃.pt (fibredCategory B S hS U')
        (fibredCategory B S hS V') W₃ U' V' eW₃ eU' eV' Sq₃.fst hM' WF eWF)
      (by rw [pullback.lift_fst]
          exact fibreProductIsoRepresenting_hom_comp_representingMap_snd B S hS Sq₃.pt
            (fibredCategory B S hS U') (fibredCategory B S hS V') W₃ U' V' eW₃ eU' eV' Sq₃.fst
            hM' WF eWF)
      (by rw [pullback.lift_snd]
          exact fibreProductIsoRepresenting_hom_comp_representingMap_fst B S hS Sq₃.pt
            (fibredCategory B S hS U') (fibredCategory B S hS V') W₃ U' V' eW₃ eU' eV' Sq₃.fst
            hM' WF eWF)
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProduct_twoIso_of_preHom hSq₃ uA uB
  let ιB : E.snd ≅ δ ≫ F'.snd :=
    wcmp.isoFst ≪≫ Bicategory.whiskerLeftIso wcmp.hom
      (Bicategory.whiskerLeftIso E₂.fst cmp₂.isoSnd)
  have hliftEq : pullback.lift α hh hcomm =
      representingMap B S hS E.pt F'.pt WE WF eWE eWF δ ≫
        cF := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
      exact representingMap_eq_comp_of_twoIso B S hS WE WF U' eWE eWF eU' ιB
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
      exact representingMap_eq_comp_of_twoIso B S hS WE WF W₃ eWE eWF eW₃ θ
  have hetale : Space.IsEtale B S hS (pullback.lift α hh hcomm) := by
    rw [hliftEq]
    exact Space.isEtale_comp B S hS hδEt
      (Space.isEtale_of_isIso B S hS cF)
  -- ### Stacks 0CG1, (c) ⇒ (a)
  have hres := Space.prop_of_etale_smooth_surjective_square B S hS hP hU' hV' hWE hW₃ φ β α hh
    hcomm hβsm hαsurj hetale hPh
  have hφ : φ = h' := representingMap_associatedMap B S hS U' V' h'
  rwa [hφ] at hres

end AlgebraicGeometry.Stack

end
