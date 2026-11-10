module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackTensorSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ZariskiPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackTensorChase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensor

/-!
# Instantiating the monoidality chase for the base change of the Zariski reading

`CategoryTheory.Functor.tensor_baseChange_of_restriction` asks for a natural family of comparisons
`K'` of the restriction to the Zariski site with tensor products, which exists only on
quasi-coherent modules.  `CategoryTheory.Functor.tensor_baseChange_of_restriction_at` asks for it
only at the two pairs of objects that occur.  It is instantiated at the base change of the Zariski
reading along a morphism `h : T' ⟶ T` of test objects, read through
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos`, as a term
`AlgebraicGeometry.Space.zariskiReadingTensorSquareAux` whose type is the implication from the
eleven squares to the monoidality square; the squares are then proved one declaration each, so
that the spelling of every square is fixed by the instance.

## Main definitions

* `AlgebraicGeometry.Space.zariskiReadingTensorSquareAux`: the instance.

## Main results

* `CategoryTheory.Functor.tensor_baseChange_of_restriction_at`.
* `AlgebraicGeometry.Space.zariskiReadingTensorIso_hom_eq_topos`: the Zariski reading tensor
  isomorphism through the restriction comparisons, in the spelling of
  `AlgebraicGeometry.Space.representedReindexEquivalenceTopos`.
* `AlgebraicGeometry.Space.zariskiReadingTensorSquare_readingNaturality`,
  `..._baseChange_left`, `..._baseChange_right`, `..._baseChange_tensor`, `..._tensorIso_source`,
  `..._restrictTensorNaturality`, `..._tensorIso_target`, `..._pullbackTensor`,
  `..._restrictPullbackNaturality`: nine of the eleven squares.
* `AlgebraicGeometry.Space.zariskiReadingRestrictTensorIso_naturality`: the naturality of the
  restriction comparison with tensor products, from base changes to inverse images under
  Stacks 04M0.

The comparisons named here are isomorphisms, used through `Iso.hom`, and the categories of
modules on the Zariski sites are those of `AlgebraicGeometry.Scheme.Modules`, so that every
square is spelled as the lemma that proves it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u

namespace CategoryTheory

/-- `CategoryTheory.Functor.tensor_baseChange_of_restriction` with the comparison `K'` of the
restriction with tensor products given only at the two pairs of objects where it is used, and its
naturality only at the comparisons `μ`. -/
theorem Functor.tensor_baseChange_of_restriction_at
    {𝒩 𝒩' Et Et' 𝒵 𝒵' : Type*} [Category 𝒩] [Category 𝒩'] [Category Et] [Category Et']
    [i𝒵 : Category 𝒵] [i𝒵' : Category 𝒵']
    (T𝒩 : 𝒩 ⥤ 𝒩 ⥤ 𝒩) (T𝒩' : 𝒩' ⥤ 𝒩' ⥤ 𝒩') (TE : Et ⥤ Et ⥤ Et) (TE' : Et' ⥤ Et' ⥤ Et')
    (T𝒵 : 𝒵 ⥤ 𝒵 ⥤ 𝒵) (T𝒵' : 𝒵' ⥤ 𝒵' ⥤ 𝒵')
    (Ei : 𝒩 ⥤ Et) (Ei' : 𝒩' ⥤ Et') (r : Et ⥤ 𝒵) (r' : Et' ⥤ 𝒵') (R : 𝒩 ⥤ 𝒵) (R' : 𝒩' ⥤ 𝒵')
    (τs : 𝒵 ⥤ 𝒵') (gs : Et ⥤ Et') (φs : 𝒩 ⥤ 𝒩')
    (ι : ∀ X : 𝒩, r.obj (Ei.obj X) ≅ R.obj X) (ι' : ∀ X : 𝒩', r'.obj (Ei'.obj X) ≅ R'.obj X)
    (N M : 𝒩)
    (P : ∀ X : 𝒩, τs.obj (R.obj X) ⟶ R'.obj (φs.obj X))
    (μ : ∀ X : 𝒩, gs.obj (Ei.obj X) ⟶ Ei'.obj (φs.obj X))
    (cN : τs.obj (r.obj (Ei.obj N)) ⟶ r'.obj (gs.obj (Ei.obj N)))
    (cM : τs.obj (r.obj (Ei.obj M)) ⟶ r'.obj (gs.obj (Ei.obj M)))
    (cNM : τs.obj (r.obj (Ei.obj ((T𝒩.obj N).obj M))) ⟶
      r'.obj (gs.obj (Ei.obj ((T𝒩.obj N).obj M))))
    (cT : τs.obj (r.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M))) ⟶
      r'.obj (gs.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M))))
    (J : Ei.obj ((T𝒩.obj N).obj M) ⟶ (TE.obj (Ei.obj N)).obj (Ei.obj M))
    (K : r.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M)) ⟶
      (T𝒵.obj (r.obj (Ei.obj N))).obj (r.obj (Ei.obj M)))
    (Z : R.obj ((T𝒩.obj N).obj M) ⟶ (T𝒵.obj (R.obj N)).obj (R.obj M))
    (cφ : φs.obj ((T𝒩.obj N).obj M) ⟶ (T𝒩'.obj (φs.obj N)).obj (φs.obj M))
    (J' : Ei'.obj ((T𝒩'.obj (φs.obj N)).obj (φs.obj M)) ⟶
      (TE'.obj (Ei'.obj (φs.obj N))).obj (Ei'.obj (φs.obj M)))
    (K'₁ : r'.obj ((TE'.obj (gs.obj (Ei.obj N))).obj (gs.obj (Ei.obj M))) ⟶
      (T𝒵'.obj (r'.obj (gs.obj (Ei.obj N)))).obj (r'.obj (gs.obj (Ei.obj M))))
    (K'₂ : r'.obj ((TE'.obj (Ei'.obj (φs.obj N))).obj (Ei'.obj (φs.obj M))) ⟶
      (T𝒵'.obj (r'.obj (Ei'.obj (φs.obj N)))).obj (r'.obj (Ei'.obj (φs.obj M))))
    (Z' : R'.obj ((T𝒩'.obj (φs.obj N)).obj (φs.obj M)) ⟶
      (T𝒵'.obj (R'.obj (φs.obj N))).obj (R'.obj (φs.obj M)))
    (I : ∀ X Y : 𝒵, τs.obj ((T𝒵.obj X).obj Y) ⟶ (T𝒵'.obj (τs.obj X)).obj (τs.obj Y))
    (bc : gs.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M)) ⟶
      (TE'.obj (gs.obj (Ei.obj N))).obj (gs.obj (Ei.obj M)))
    (hι' : ∀ {X Y : 𝒩'} (f : X ⟶ Y), r'.map (Ei'.map f) ≫ (ι' Y).hom = (ι' X).hom ≫ R'.map f)
    (hFN : τs.map ((ι N).hom) ≫ P N = cN ≫ r'.map (μ N) ≫ (ι' (φs.obj N)).hom)
    (hFM : τs.map ((ι M).hom) ≫ P M = cM ≫ r'.map (μ M) ≫ (ι' (φs.obj M)).hom)
    (hFNM : τs.map ((ι ((T𝒩.obj N).obj M)).hom) ≫ P ((T𝒩.obj N).obj M) =
      cNM ≫ r'.map (μ ((T𝒩.obj N).obj M)) ≫ (ι' (φs.obj ((T𝒩.obj N).obj M))).hom)
    (hZ : Z = (ι _).inv ≫ r.map J ≫ K ≫
      ((T𝒵.map ((ι N).hom)).app _ ≫ (T𝒵.obj (R.obj N)).map ((ι M).hom)))
    (hK' : r'.map ((TE'.map (μ N)).app _ ≫ (TE'.obj _).map (μ M)) ≫ K'₂ =
        K'₁ ≫ ((T𝒵'.map (r'.map (μ N))).app _ ≫ (T𝒵'.obj _).map (r'.map (μ M))))
    (hZ' : Z' = (ι' _).inv ≫ r'.map J' ≫ K'₂ ≫
      ((T𝒵'.map ((ι' (φs.obj N)).hom)).app _ ≫
        (T𝒵'.obj (R'.obj (φs.obj N))).map ((ι' (φs.obj M)).hom)))
    (hI : ∀ {X X' Y Y' : 𝒵} (f : X ⟶ X') (g : Y ⟶ Y'),
      τs.map ((T𝒵.map f).app Y ≫ (T𝒵.obj X').map g) ≫ I X' Y' =
        I X Y ≫ ((T𝒵'.map (τs.map f)).app _ ≫ (T𝒵'.obj (τs.obj X')).map (τs.map g)))
    (hZP : τs.map K ≫ I _ _ ≫ ((T𝒵'.map cN).app _ ≫ (T𝒵'.obj _).map cM) =
      cT ≫ r'.map bc ≫ K'₁)
    (hc : τs.map (r.map J) ≫ cT = cNM ≫ r'.map (gs.map J))
    (hstar : gs.map J ≫ bc ≫ ((TE'.map (μ N)).app _ ≫ (TE'.obj _).map (μ M)) =
      μ ((T𝒩.obj N).obj M) ≫ Ei'.map cφ ≫ J') :
    τs.map Z ≫ I (R.obj N) (R.obj M) ≫
        ((T𝒵'.map (P N)).app _ ≫ (T𝒵'.obj (R'.obj (φs.obj N))).map (P M)) =
      P ((T𝒩.obj N).obj M) ≫ R'.map cφ ≫ Z' := by
  have eP : ∀ (X : 𝒩) (c' : τs.obj (r.obj (Ei.obj X)) ⟶ r'.obj (gs.obj (Ei.obj X)))
      (_ : τs.map ((ι X).hom) ≫ P X = c' ≫ r'.map (μ X) ≫ (ι' (φs.obj X)).hom),
      P X = τs.map ((ι X).inv) ≫ c' ≫ r'.map (μ X) ≫ (ι' (φs.obj X)).hom := by
    intro X c' h
    rw [← h, ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  have bm : ∀ {𝒞 𝒟 : Type _} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒞 ⥤ 𝒟) {A A' A'' X Y W : 𝒞}
      (f : A ⟶ A') (f' : A' ⟶ A'') (g : X ⟶ Y) (g' : Y ⟶ W),
      ((F.map f).app X ≫ (F.obj A').map g) ≫ ((F.map f').app Y ≫ (F.obj A'').map g') =
        (F.map (f ≫ f')).app X ≫ (F.obj A'').map (g ≫ g') := by
    intros
    simp only [Category.assoc, Functor.map_comp, NatTrans.comp_app, NatTrans.naturality_assoc]
  have e1 : ((T𝒵'.map (τs.map ((ι N).hom))).app _ ≫
      (T𝒵'.obj (τs.obj (R.obj N))).map (τs.map ((ι M).hom))) ≫
      ((T𝒵'.map (P N)).app _ ≫ (T𝒵'.obj (R'.obj (φs.obj N))).map (P M)) =
      ((T𝒵'.map cN).app _ ≫ (T𝒵'.obj _).map cM) ≫
        ((T𝒵'.map (r'.map (μ N))).app _ ≫ (T𝒵'.obj _).map (r'.map (μ M))) ≫
        ((T𝒵'.map ((ι' (φs.obj N)).hom)).app _ ≫
          (T𝒵'.obj (R'.obj (φs.obj N))).map ((ι' (φs.obj M)).hom)) := by
    rw [bm, hFN, hFM, ← bm, ← bm]
  have e2 := hK'
  have e3 : (ι' (φs.obj ((T𝒩.obj N).obj M))).hom ≫ R'.map cφ ≫ (ι' _).inv =
      r'.map (Ei'.map cφ) := by
    rw [← Category.assoc, ← hι', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hZ, hZ', eP _ _ hFNM]
  have hI2 := hI ((ι N).hom) ((ι M).hom)
  have hs := congrArg r'.map hstar
  simp only [Functor.map_comp, Category.assoc] at hI2 e1 hZP e2 e3 hc hs ⊢
  rw [reassoc_of% hI2, e1, reassoc_of% hZP, ← reassoc_of% e2, reassoc_of% hc,
    reassoc_of% e3, reassoc_of% hs]
/-- Transport of a naturality square of a tensor comparison across a change of spelling of the
source category, of its objects and of the morphisms. -/
theorem Functor.bifunctor_naturality_transport {C₁ C D : Type _}
    [i₁ : Category C₁] [i : Category C] [Category D]
    {r₁ : C₁ ⥤ D} {r : C ⥤ D} {T₁ : C₁ ⥤ C₁ ⥤ C₁} {TC : C ⥤ C ⥤ C} {TD : D ⥤ D ⥤ D}
    {M₁ N₁ M₁' N₁' : C₁} {M N M' N' : C} {a₁ : M₁ ⟶ M₁'} {b₁ : N₁ ⟶ N₁'} {a : M ⟶ M'}
    {b : N ⟶ N'}
    {K₁' : r₁.obj ((T₁.obj M₁).obj N₁) ⟶ (TD.obj (r₁.obj M₁)).obj (r₁.obj N₁)}
    {K₁ : r.obj ((TC.obj M).obj N) ⟶ (TD.obj (r.obj M)).obj (r.obj N)}
    {K₂' : r₁.obj ((T₁.obj M₁').obj N₁') ⟶ (TD.obj (r₁.obj M₁')).obj (r₁.obj N₁')}
    {K₂ : r.obj ((TC.obj M').obj N') ⟶ (TD.obj (r.obj M')).obj (r.obj N')}
    (src : r₁.map ((T₁.map a₁).app N₁ ≫ (T₁.obj M₁').map b₁) ≫ K₂' =
      K₁' ≫ ((TD.map (r₁.map a₁)).app _ ≫ (TD.obj (r₁.obj M₁')).map (r₁.map b₁)))
    (eC : C₁ = C) (ei : HEq i₁ i) (er : HEq r₁ r) (eT : HEq T₁ TC)
    (eM : HEq M₁ M) (eN : HEq N₁ N) (eM' : HEq M₁' M') (eN' : HEq N₁' N')
    (ha : HEq a₁ a) (hb : HEq b₁ b) (hK₁ : HEq K₁' K₁) (hK₂ : HEq K₂' K₂) :
    r.map ((TC.map a).app N ≫ (TC.obj M').map b) ≫ K₂ =
      K₁ ≫ ((TD.map (r.map a)).app _ ≫ (TD.obj (r.obj M')).map (r.map b)) := by
  subst eC; cases ei; cases er; cases eT; cases eM; cases eN; cases eM'; cases eN'; cases ha
  cases hb; cases hK₁; cases hK₂; exact src

end CategoryTheory

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The hypothesis number 1 of an elevenfold implication, as a proposition. -/
abbrev HypothesisOf₁₁_1 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → β) : Prop := α1
/-- The hypothesis number 2 of an elevenfold implication, as a proposition. -/
abbrev HypothesisOf₁₁_2 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → β) : Prop := α2
/-- The hypothesis number 3 of an elevenfold implication, as a proposition. -/
abbrev HypothesisOf₁₁_3 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → β) : Prop := α3
/-- The hypothesis number 4 of an elevenfold implication, as a proposition. -/
abbrev HypothesisOf₁₁_4 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → β) : Prop := α4
/-- The hypothesis number 5 of an elevenfold implication, as a proposition. -/
abbrev HypothesisOf₁₁_5 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → β) : Prop := α5
/-- The hypothesis number 6 of an elevenfold implication, as a proposition. -/
abbrev HypothesisOf₁₁_6 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → β) : Prop := α6
/-- The hypothesis number 7 of an elevenfold implication, as a proposition. -/
abbrev HypothesisOf₁₁_7 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → β) : Prop := α7
/-- The hypothesis number 8 of an elevenfold implication, as a proposition. -/
abbrev HypothesisOf₁₁_8 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → β) : Prop := α8
/-- The hypothesis number 9 of an elevenfold implication, as a proposition. -/
abbrev HypothesisOf₁₁_9 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → β) : Prop := α9
/-- The hypothesis number 10 of an elevenfold implication, as a proposition. -/
abbrev HypothesisOf₁₁_10 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → β) : Prop := α10
/-- The hypothesis number 11 of an elevenfold implication, as a proposition. -/
abbrev HypothesisOf₁₁_11 {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → β) : Prop := α11
/-- The hypothesis number 1 of a fivefold implication, as a proposition. -/
abbrev HypothesisOf₅_1 {α1 α2 α3 α4 α5 β : Prop} (_ : α1 → α2 → α3 → α4 → α5 → β) : Prop := α1
/-- The hypothesis number 2 of a fivefold implication, as a proposition. -/
abbrev HypothesisOf₅_2 {α1 α2 α3 α4 α5 β : Prop} (_ : α1 → α2 → α3 → α4 → α5 → β) : Prop := α2
/-- The hypothesis number 3 of a fivefold implication, as a proposition. -/
abbrev HypothesisOf₅_3 {α1 α2 α3 α4 α5 β : Prop} (_ : α1 → α2 → α3 → α4 → α5 → β) : Prop := α3
/-- The hypothesis number 4 of a fivefold implication, as a proposition. -/
abbrev HypothesisOf₅_4 {α1 α2 α3 α4 α5 β : Prop} (_ : α1 → α2 → α3 → α4 → α5 → β) : Prop := α4
/-- The hypothesis number 5 of a fivefold implication, as a proposition. -/
abbrev HypothesisOf₅_5 {α1 α2 α3 α4 α5 β : Prop} (_ : α1 → α2 → α3 → α4 → α5 → β) : Prop := α5

/-- An equation with a fivefold composite on the right, transported along equations of the
factors. -/
theorem _root_.CategoryTheory.eq_comp_comp_comp_comp_of_eq {𝒞 : Type*} [Category 𝒞]
    {A B C D E F : 𝒞} {Z : A ⟶ F} {a a' : A ⟶ B} {b b' : B ⟶ C} {c c' : C ⟶ D}
    {d d' : D ⟶ E} {e e' : E ⟶ F} (h : Z = a ≫ b ≫ c ≫ d ≫ e) (ha : a = a') (hb : b = b')
    (hc : c = c') (hd : d = d') (he : e = e') : Z = a' ≫ b' ≫ c' ≫ d' ≫ e' := by
  subst ha hb hc hd he; exact h

/-- The naturality of a comparison of the composite of an uncurried bifunctor with a functor,
in both arguments. -/
theorem _root_.CategoryTheory.NatTrans.naturality_uncurry_prod {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] {F : 𝒞 ⥤ 𝒞 ⥤ 𝒞} {F' : 𝒟 ⥤ 𝒟 ⥤ 𝒟} {G : 𝒞 ⥤ 𝒟}
    (α : Functor.uncurry.obj F ⋙ G ⟶ G.prod G ⋙ Functor.uncurry.obj F')
    {X X' Y Y' : 𝒞} (f : X ⟶ X') (g : Y ⟶ Y') :
    G.map ((F.map f).app Y ≫ (F.obj X').map g) ≫ α.app (X', Y') =
      α.app (X, Y) ≫ ((F'.map (G.map f)).app _ ≫ (F'.obj (G.obj X')).map (G.map g)) :=
  α.naturality (X := (X, Y)) (Y := (X', Y')) (f, g)

/-- The restriction to the Zariski site of the tensor product, at the inverse images under
Stacks 04M0 of two quasi-coherent modules. -/
def zariskiReadingRestrictTensorIso (U : BigFppfOver B S hS)
    (P Q : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              (_root_.AlgebraicGeometry.smallEtaleRingedSite
                (associatedBigEtaleSite B) U.left.obj U.left.property).toRingedTopos.O).obj
        ((representedReindexEquivalenceTopos U).inverse.obj P)).obj
          ((representedReindexEquivalenceTopos U).inverse.obj Q)) ≅
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).obj
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
          ((representedReindexEquivalenceTopos U).inverse.obj P))).obj
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
          ((representedReindexEquivalenceTopos U).inverse.obj Q)) :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q)
    ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app P).symm hP))
    ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app Q).symm hQ)))

/-- The comparison of Stacks 04M0 with tensor products, for the inverse. -/
def zariskiReadingInverseTensorIso (U : BigFppfOver B S hS)
    (P Q : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :
    (representedReindexEquivalenceTopos U).inverse.obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))).obj P).obj
          Q) ≅
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (_root_.AlgebraicGeometry.smallEtaleRingedSite
            (associatedBigEtaleSite B) U.left.obj U.left.property).toRingedTopos.O).obj
        ((representedReindexEquivalenceTopos U).inverse.obj P)).obj
          ((representedReindexEquivalenceTopos U).inverse.obj Q) :=
  representedSmallEtaleModuleInverseTensorIso B S hS U P Q

/-- `zariskiReadingTensorIso_hom_eq` through the named comparisons and the Zariski reading
isomorphism of `AlgebraicGeometry.Space.representedReindexEquivalenceTopos`, as a term whose type
fixes the spelling. -/
theorem zariskiReadingTensorIsoHomEqAux (U : BigFppfOver B S hS)
    (P Q : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    type_of% (fun ha hb hc hd he => (eq_comp_comp_comp_comp_of_eq
    (zariskiReadingTensorIso_hom_eq U P Q hP hQ) ha hb hc hd he :
    (zariskiReadingTensorIso U P Q hP hQ).hom =
      (zariskiReadingIsoTopos U).inv.app _ ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
        (zariskiReadingInverseTensorIso U P Q).hom ≫
        (zariskiReadingRestrictTensorIso U P Q hP hQ).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).map
              ((zariskiReadingIsoTopos U).hom.app P)).app _ ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).obj
                _).map ((zariskiReadingIsoTopos U).hom.app Q))) :=
  fun ha hb hc hd he => eq_comp_comp_comp_comp_of_eq
    (zariskiReadingTensorIso_hom_eq U P Q hP hQ) ha hb hc hd he

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorIso_hom_eq_topos`. -/
theorem zariskiReadingTensorIsoHomEq_1 (U : BigFppfOver B S hS)
    (P Q : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    HypothesisOf₅_1 (zariskiReadingTensorIsoHomEqAux U P Q hP hQ) := rfl
/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorIso_hom_eq_topos`. -/
theorem zariskiReadingTensorIsoHomEq_2 (U : BigFppfOver B S hS)
    (P Q : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    HypothesisOf₅_2 (zariskiReadingTensorIsoHomEqAux U P Q hP hQ) := rfl
/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorIso_hom_eq_topos`. -/
theorem zariskiReadingTensorIsoHomEq_3 (U : BigFppfOver B S hS)
    (P Q : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    HypothesisOf₅_3 (zariskiReadingTensorIsoHomEqAux U P Q hP hQ) := rfl
/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorIso_hom_eq_topos`. -/
theorem zariskiReadingTensorIsoHomEq_4 (U : BigFppfOver B S hS)
    (P Q : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    HypothesisOf₅_4 (zariskiReadingTensorIsoHomEqAux U P Q hP hQ) := rfl
/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorIso_hom_eq_topos`. -/
theorem zariskiReadingTensorIsoHomEq_5 (U : BigFppfOver B S hS)
    (P Q : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    HypothesisOf₅_5 (zariskiReadingTensorIsoHomEqAux U P Q hP hQ) := rfl

/-- The conclusion of a fivefold implication, as a proposition. -/
abbrev ConclusionOf₅ {α1 α2 α3 α4 α5 β : Prop} (_ : α1 → α2 → α3 → α4 → α5 → β) : Prop := β

/-- `zariskiReadingTensorIso_hom_eq` through the named comparisons. -/
theorem zariskiReadingTensorIso_hom_eq_topos (U : BigFppfOver B S hS)
    (P Q : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    ConclusionOf₅ (zariskiReadingTensorIsoHomEqAux U P Q hP hQ) :=
  zariskiReadingTensorIsoHomEqAux U P Q hP hQ (zariskiReadingTensorIsoHomEq_1 U P Q hP hQ)
    (zariskiReadingTensorIsoHomEq_2 U P Q hP hQ) (zariskiReadingTensorIsoHomEq_3 U P Q hP hQ)
    (zariskiReadingTensorIsoHomEq_4 U P Q hP hQ) (zariskiReadingTensorIsoHomEq_5 U P Q hP hQ)

variable {T T' : BigFppfOver B S hS} (h : T' ⟶ T)

/-- Small étale base change of a restriction to the Zariski site. -/
def zariskiReadingRestrictPullbackIso
    (A :
      _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T.left.obj T.left.property).toRingedTopos.O))
    (hA : A.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj A) ≅
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj
      ((smallEtaleRingedSiteHom
          (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A) :=
  _root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
    (associatedBigEtaleSite B) h.left A hA

/-- Stacks 03EL for small étale base change of schemes. -/
def zariskiReadingEtaleBaseChangeTensorIso
    (A A' :
      _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T.left.obj T.left.property).toRingedTopos.O)) :
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        h.left).toRingedToposSiteHom.pullbackToposGeneral.obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (_root_.AlgebraicGeometry.smallEtaleRingedSite
              (associatedBigEtaleSite B) T.left.obj T.left.property).toRingedTopos.O).obj A).obj
        A') ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (_root_.AlgebraicGeometry.smallEtaleRingedSite
            (associatedBigEtaleSite B) T'.left.obj T'.left.property).toRingedTopos.O).obj
        ((smallEtaleRingedSiteHom
            (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A)).obj
      ((smallEtaleRingedSiteHom
          (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A') :=
  Stacks.SheafOfModules.pullbackTensorIsoTransport
    (_root_.AlgebraicGeometry.SmallEtale.baseChangeRingedToposModulesHom
        (associatedBigEtaleSite B) h.left)
    (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesBaseChangeIso
        (associatedBigEtaleSite B) h.left) A A'

/-- The restriction to the Zariski site of the tensor product, after small étale base change. -/
def zariskiReadingRestrictPullbackTensorIso
    (A A' :
      _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T.left.obj T.left.property).toRingedTopos.O))
    (hA : A.IsQuasicoherentOnSite)
    (hA' : A'.IsQuasicoherentOnSite) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (_root_.AlgebraicGeometry.smallEtaleRingedSite
              (associatedBigEtaleSite B) T'.left.obj T'.left.property).toRingedTopos.O).obj
          ((smallEtaleRingedSiteHom
              (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj
            A)).obj
        ((smallEtaleRingedSiteHom
            (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A')) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((BigFppfOver.toScheme B S hS).obj T').zariskiRingedSite.toRingedTopos.O).obj
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj
            ((smallEtaleRingedSiteHom
                (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj
              A))).obj
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj
          ((smallEtaleRingedSiteHom
              (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj
            A')) :=
  _root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T') T'.left.property
      ((smallEtaleRingedSiteHom
          (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A)
      ((smallEtaleRingedSiteHom
          (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A')
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
        (associatedBigEtaleSite B) h.left _ hA)
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
        (associatedBigEtaleSite B) h.left _ hA')

/-- Stacks 03EL for the morphism of represented spaces. -/
def zariskiReadingSpaceTensorIso
    (P Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).obj P).obj
        Q) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))).obj
        ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
          P)).obj
      ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
        Q) :=
  Stacks.SheafOfModules.pullbackTensorIsoTransport
    (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)) (Iso.refl _) P Q

/-- Quasi-coherence of the tensor product sheaf of two quasi-coherent modules on `yoneda.obj T`. -/
theorem isQuasicoherentOnSite_sheafTensor_yoneda
    (P Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).obj P).obj
        Q).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.DerivedTensorProduct.isQuasicoherentOnSite_sheafTensor
    (X := smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) P Q hP hQ

/-- The naturality of the base change of a restriction. -/
theorem zariskiReadingRestrictPullbackIso_naturality
    {A A' :
      _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T.left.obj T.left.property).toRingedTopos.O)}
    (hA : A.IsQuasicoherentOnSite)
    (hA' : A'.IsQuasicoherentOnSite) (k : A ⟶ A') :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map k) ≫
      (zariskiReadingRestrictPullbackIso h A' hA').hom =
      (zariskiReadingRestrictPullbackIso h A hA).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
        ((smallEtaleRingedSiteHom
            (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.map k) :=
  _root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_naturality
    (associatedBigEtaleSite B) h.left hA hA' k

/-- The inverse images under Stacks 04M0 in the two spellings of the equivalence. -/
theorem heq_representedReindexEquivalenceTopos_inverse_obj
    (P : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')) :
    HEq ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj P)
      ((representedReindexEquivalenceTopos T').inverse.obj P) := HEq.rfl

/-- The restriction comparison with tensor products at inverse images under Stacks 04M0, in the
two spellings of the equivalence. -/
theorem heq_restrictModuleTensorIso_hom_zariskiReadingRestrictTensorIso
    (P Q : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    HEq (_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj P)
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.obj Q)
      ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T' _).1
        (SheafOfModules.IsQuasicoherentOnSite.of_iso
            ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app P).symm hP))
      ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T' _).1
        (SheafOfModules.IsQuasicoherentOnSite.of_iso
            ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app Q).symm hQ))).hom
    (zariskiReadingRestrictTensorIso T' P Q hP hQ).hom := HEq.rfl

/-- The modules on the small étale site of the scheme underlying `T'`, in two spellings. -/
theorem sheafOfModules_smallEtaleStructureSheaf_eq :
    _root_.SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T') T'.left.property) =
      _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T'.left.obj T'.left.property).toRingedTopos.O) := rfl

/-- The category of modules on the small étale site of the scheme underlying `T'`, in two
spellings. -/
theorem heq_sheafOfModules_instCategory_smallEtaleStructureSheaf :
    HEq (SheafOfModules.instCategory.{u}
        (R :=
          _root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T') T'.left.property))
      (SheafOfModules.instCategory.{u}
          (R :=
            Stacks.SheafOfModules.Tensor.ringSheaf
            (_root_.AlgebraicGeometry.smallEtaleRingedSite
              (associatedBigEtaleSite B) T'.left.obj T'.left.property).toRingedTopos.O)) := HEq.rfl

/-- The tensor product on the small étale site of the scheme underlying `T'`, in two spellings. -/
theorem heq_sheafTensor_smallEtaleRingedSite :
    HEq (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).toRingedTopos.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T'.left.obj T'.left.property).toRingedTopos.O) := HEq.rfl

/-- The restriction comparison with tensor products after base change, as the comparison it is
built from. -/
theorem heq_restrictModuleTensorIso_hom_zariskiReadingRestrictPullbackTensorIso
    (A A' :
      _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T.left.obj T.left.property).toRingedTopos.O))
    (hA : A.IsQuasicoherentOnSite) (hA' : A'.IsQuasicoherentOnSite) :
    HEq (_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property
        ((smallEtaleRingedSiteHom
            (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A)
        ((smallEtaleRingedSiteHom
            (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A')
        (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
          (associatedBigEtaleSite B) h.left _ hA)
      (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
          (associatedBigEtaleSite B) h.left _ hA')).hom
        (zariskiReadingRestrictPullbackTensorIso h A A' hA hA').hom :=
  HEq.rfl

/-- The naturality of the restriction comparison with tensor products, from base changes to
inverse images under Stacks 04M0. -/
theorem zariskiReadingRestrictTensorIso_naturality
    (A A' :
      _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T.left.obj T.left.property).toRingedTopos.O))
    (hA : A.IsQuasicoherentOnSite)
    (hA' : A'.IsQuasicoherentOnSite)
    (P Q : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
      (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite)
    (a : (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
          h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A ⟶
        (representedReindexEquivalenceTopos T').inverse.obj P)
      (b :
        (smallEtaleRingedSiteHom
          (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A' ⟶
        (representedReindexEquivalenceTopos T').inverse.obj Q) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (_root_.AlgebraicGeometry.smallEtaleRingedSite
              (associatedBigEtaleSite B) T'.left.obj T'.left.property).toRingedTopos.O).map a).app
        ((smallEtaleRingedSiteHom
            (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral.obj A') ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (_root_.AlgebraicGeometry.smallEtaleRingedSite
              (associatedBigEtaleSite B) T'.left.obj T'.left.property).toRingedTopos.O).obj
          ((representedReindexEquivalenceTopos T').inverse.obj P)).map b) ≫
        (zariskiReadingRestrictTensorIso T' P Q hP hQ).hom =
      (zariskiReadingRestrictPullbackTensorIso h A A' hA hA').hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                ((BigFppfOver.toScheme B S hS).obj T').zariskiRingedSite.toRingedTopos.O).map
              ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map a)).app _ ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                ((BigFppfOver.toScheme B S hS).obj T').zariskiRingedSite.toRingedTopos.O).obj _).map
            ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map b)) :=
  Functor.bifunctor_naturality_transport
    (_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso_hom_naturality
        (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T') T'.left.property
    (M' := (representedSmallEtaleModuleEquivalence B S hS T').inverse.obj P)
      (N' := (representedSmallEtaleModuleEquivalence B S hS T').inverse.obj Q) a b
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
        (associatedBigEtaleSite B) h.left _ hA)
      (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
        (associatedBigEtaleSite B) h.left _ hA')
    ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T' _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
          ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app P).symm hP))
    ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T' _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
          ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app Q).symm hQ)))
    sheafOfModules_smallEtaleStructureSheaf_eq
      heq_sheafOfModules_instCategory_smallEtaleStructureSheaf
    HEq.rfl heq_sheafTensor_smallEtaleRingedSite HEq.rfl HEq.rfl
    (heq_representedReindexEquivalenceTopos_inverse_obj P)
    (heq_representedReindexEquivalenceTopos_inverse_obj Q) HEq.rfl HEq.rfl
    (heq_restrictModuleTensorIso_hom_zariskiReadingRestrictPullbackTensorIso h A A' hA hA')
    (heq_restrictModuleTensorIso_hom_zariskiReadingRestrictTensorIso P Q hP hQ)

variable (N M : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite)

/-- **`CategoryTheory.Functor.tensor_baseChange_of_restriction_at` instantiated** at the base
change of the Zariski reading along `h`, with the readings through
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos`, Stacks 01CD on the schemes, the
restriction comparisons of Stacks 03DX and Stacks 03EL for small étale base change: a term whose
type is the implication from the eleven squares to the monoidality square, with the spelling of
every square fixed. -/
theorem zariskiReadingTensorSquareAux : type_of% (
  Functor.tensor_baseChange_of_restriction_at (𝒵 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (𝒵' := ((BigFppfOver.toScheme B S hS).obj T').Modules) (i𝒵 := Scheme.Modules.instCategory)
    (i𝒵' := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T.left.obj T.left.property).toRingedTopos.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T'.left.obj T'.left.property).toRingedTopos.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T').zariskiRingedSite.toRingedTopos.O)
      (representedReindexEquivalenceTopos T).inverse (representedReindexEquivalenceTopos T').inverse
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (zariskiReadingFunctor T) (zariskiReadingFunctor T')
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h))
      (smallEtaleRingedSiteHom
        (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules
    (fun X => (zariskiReadingIsoTopos T).app X) (fun X => (zariskiReadingIsoTopos T').app X)
    N M (fun X => (zariskiReadingPullbackHom h).app X)
    (fun X => Adjunction.equivalenceMateApp (representedReindexEquivalenceTopos T)
        (representedReindexEquivalenceTopos T')
      (representedSquareFactorizationIso B S hS h (relativelyRepresentable_yoneda_map B S hS h)).hom
        X)
    ((zariskiReadingRestrictPullbackIso h _
          (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN))).hom
    ((zariskiReadingRestrictPullbackIso h _
          (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))).hom
    ((zariskiReadingRestrictPullbackIso h _
          (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T _
      (isQuasicoherentOnSite_sheafTensor_yoneda N M hN hM)))).hom
    ((zariskiReadingRestrictPullbackIso h _
          (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_sheafTensor
            (associatedBigEtaleSite B)
        T.left.obj T.left.property _ _
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM)))).hom
    (zariskiReadingInverseTensorIso T N M).hom
    ((zariskiReadingRestrictTensorIso T N M hN hM).hom)
    (zariskiReadingTensorIso T N M hN hM).hom
    (zariskiReadingSpaceTensorIso h N M).hom
    (zariskiReadingInverseTensorIso T'
        ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
          N)
        ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
          M)).hom
    (zariskiReadingRestrictPullbackTensorIso h _ _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM)).hom
    (zariskiReadingRestrictTensorIso T'
        ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
          N)
        ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
          M)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) N hN)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) M hM)).hom
    (zariskiReadingTensorIso T' _ _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) N hN)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) M hM)).hom
    (fun X Y => (Stacks.RingedSpace.comparisonBifunctorIso
      ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app (X, Y))
    (zariskiReadingEtaleBaseChangeTensorIso h _ _).hom) :=
  Functor.tensor_baseChange_of_restriction_at (𝒵 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (𝒵' := ((BigFppfOver.toScheme B S hS).obj T').Modules) (i𝒵 := Scheme.Modules.instCategory)
    (i𝒵' := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T.left.obj T.left.property).toRingedTopos.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite
          (associatedBigEtaleSite B) T'.left.obj T'.left.property).toRingedTopos.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T').zariskiRingedSite.toRingedTopos.O)
      (representedReindexEquivalenceTopos T).inverse (representedReindexEquivalenceTopos T').inverse
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (zariskiReadingFunctor T) (zariskiReadingFunctor T')
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h))
      (smallEtaleRingedSiteHom
        (associatedBigEtaleSite B) h.left).toRingedToposSiteHom.pullbackToposGeneral
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules
    (fun X => (zariskiReadingIsoTopos T).app X) (fun X => (zariskiReadingIsoTopos T').app X)
    N M (fun X => (zariskiReadingPullbackHom h).app X)
    (fun X => Adjunction.equivalenceMateApp (representedReindexEquivalenceTopos T)
        (representedReindexEquivalenceTopos T')
      (representedSquareFactorizationIso B S hS h (relativelyRepresentable_yoneda_map B S hS h)).hom
        X)
    ((zariskiReadingRestrictPullbackIso h _
          (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN))).hom
    ((zariskiReadingRestrictPullbackIso h _
          (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))).hom
    ((zariskiReadingRestrictPullbackIso h _
          (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T _
      (isQuasicoherentOnSite_sheafTensor_yoneda N M hN hM)))).hom
    ((zariskiReadingRestrictPullbackIso h _
          (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_sheafTensor
            (associatedBigEtaleSite B)
        T.left.obj T.left.property _ _
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM)))).hom
    (zariskiReadingInverseTensorIso T N M).hom
    ((zariskiReadingRestrictTensorIso T N M hN hM).hom)
    (zariskiReadingTensorIso T N M hN hM).hom
    (zariskiReadingSpaceTensorIso h N M).hom
    (zariskiReadingInverseTensorIso T'
        ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
          N)
        ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
          M)).hom
    (zariskiReadingRestrictPullbackTensorIso h _ _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM)).hom
    (zariskiReadingRestrictTensorIso T'
        ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
          N)
        ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
          M)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) N hN)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) M hM)).hom
    (zariskiReadingTensorIso T' _ _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) N hN)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) M hM)).hom
    (fun X Y => (Stacks.RingedSpace.comparisonBifunctorIso
      ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app (X, Y))
    (zariskiReadingEtaleBaseChangeTensorIso h _ _).hom

/-- The naturality of the Zariski reading isomorphism of `T'`: the first square. -/
theorem zariskiReadingTensorSquare_readingNaturality :
    HypothesisOf₁₁_1 (zariskiReadingTensorSquareAux h N M hN hM) :=
  fun f => (zariskiReadingIsoTopos T').hom.naturality f

/-- The description of the base change at `N`: the second square. -/
theorem zariskiReadingTensorSquare_baseChange_left :
    HypothesisOf₁₁_2 (zariskiReadingTensorSquareAux h N M hN hM) :=
  pullback_map_zariskiReadingIsoTopos_hom_app_comp_zariskiReadingPullbackHom_app h N hN

/-- The description of the base change at `M`: the third square. -/
theorem zariskiReadingTensorSquare_baseChange_right :
    HypothesisOf₁₁_3 (zariskiReadingTensorSquareAux h N M hN hM) :=
  pullback_map_zariskiReadingIsoTopos_hom_app_comp_zariskiReadingPullbackHom_app h M hM

/-- The description of the base change at the tensor product sheaf: the fourth square. -/
theorem zariskiReadingTensorSquare_baseChange_tensor :
    HypothesisOf₁₁_4 (zariskiReadingTensorSquareAux h N M hN hM) :=
  pullback_map_zariskiReadingIsoTopos_hom_app_comp_zariskiReadingPullbackHom_app h
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).obj N).obj M)
      (isQuasicoherentOnSite_sheafTensor_yoneda N M hN hM)

/-- The Zariski reading tensor isomorphism of `T` through the restriction comparisons: the fifth
square. -/
theorem zariskiReadingTensorSquare_tensorIso_source :
    HypothesisOf₁₁_5 (zariskiReadingTensorSquareAux h N M hN hM) :=
  zariskiReadingTensorIso_hom_eq_topos T N M hN hM

/-- The Zariski reading tensor isomorphism of `T'` through the restriction comparisons: the
seventh square. -/
theorem zariskiReadingTensorSquare_tensorIso_target :
    HypothesisOf₁₁_7 (zariskiReadingTensorSquareAux h N M hN hM) :=
  zariskiReadingTensorIso_hom_eq_topos T'
    ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj N)
    ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj M)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS h) N hN)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS h) M hM)

/-- The naturality of Stacks 01CD for the morphism of schemes: the eighth square. -/
theorem zariskiReadingTensorSquare_pullbackTensor :
    HypothesisOf₁₁_8 (zariskiReadingTensorSquareAux h N M hN hM) :=
  fun f g => NatTrans.naturality_uncurry_prod (Stacks.RingedSpace.comparisonBifunctorIso
      ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom f g

/-- The naturality of the base change of the restriction at the comparison of Stacks 04M0 with
tensor products: the tenth square. -/
theorem zariskiReadingTensorSquare_restrictPullbackNaturality :
    HypothesisOf₁₁_10 (zariskiReadingTensorSquareAux h N M hN hM) :=
  zariskiReadingRestrictPullbackIso_naturality h
    (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T _
      (isQuasicoherentOnSite_sheafTensor_yoneda N M hN hM))
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_sheafTensor
        (associatedBigEtaleSite B)
      T.left.obj T.left.property _ _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))
    (zariskiReadingInverseTensorIso T N M).hom

/-- The naturality of the restriction comparison with tensor products at the comparisons of the
base change: the sixth square. -/
theorem zariskiReadingTensorSquare_restrictTensorNaturality :
    HypothesisOf₁₁_6 (zariskiReadingTensorSquareAux h N M hN hM) :=
  Functor.bifunctor_naturality_transport
    (_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso_hom_naturality
        (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T') T'.left.property
    (M' := (representedSmallEtaleModuleEquivalence B S hS T').inverse.obj
        ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
          N))
      (N' :=
        (representedSmallEtaleModuleEquivalence B S hS T').inverse.obj
        ((smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules.obj
          M))
    (Adjunction.equivalenceMateApp (representedReindexEquivalenceTopos T)
        (representedReindexEquivalenceTopos T')
      (representedSquareFactorizationIso B S hS h (relativelyRepresentable_yoneda_map B S hS h)).hom
        N)
    (Adjunction.equivalenceMateApp (representedReindexEquivalenceTopos T)
        (representedReindexEquivalenceTopos T')
      (representedSquareFactorizationIso B S hS h (relativelyRepresentable_yoneda_map B S hS h)).hom
        M)
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
        (associatedBigEtaleSite B) h.left _
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN))
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback
        (associatedBigEtaleSite B) h.left _
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))
    ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T' _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
          ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app
            ((smallEtaleRingedToposModulesHom B S hS
                (representedSpaceMap B S hS h)).pullbackModules.obj N)).symm
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
            (representedSpaceMap B S hS h) N hN)))
    ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T' _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
          ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app
            ((smallEtaleRingedToposModulesHom B S hS
                (representedSpaceMap B S hS h)).pullbackModules.obj M)).symm
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
            (representedSpaceMap B S hS h) M hM))))
    sheafOfModules_smallEtaleStructureSheaf_eq
      heq_sheafOfModules_instCategory_smallEtaleStructureSheaf
    HEq.rfl heq_sheafTensor_smallEtaleRingedSite HEq.rfl HEq.rfl
    (heq_representedReindexEquivalenceTopos_inverse_obj _)
    (heq_representedReindexEquivalenceTopos_inverse_obj _) HEq.rfl HEq.rfl
    (heq_restrictModuleTensorIso_hom_zariskiReadingRestrictPullbackTensorIso h _ _ _ _)
    (heq_restrictModuleTensorIso_hom_zariskiReadingRestrictTensorIso _ _ _ _)


end AlgebraicGeometry.Space
