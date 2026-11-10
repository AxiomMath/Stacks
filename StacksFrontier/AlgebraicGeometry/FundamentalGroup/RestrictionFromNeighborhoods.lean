module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleInternalHom
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProdHomEquiv
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of finite étale covers from the neighbourhoods of a closed subscheme

Let `X` be a scheme and `Y ⊆ X` a closed subscheme, given by its ideal sheaf, and let `𝒱` be the
set of open subschemes `V ⊆ X` containing `Y`, ordered by reverse inclusion
(`Stacks.FundamentalGroup.Neighborhood`). [Stacks, Tag 0ELA] asserts that the restriction functor
`colim_𝒱 FÉt_V ⟶ FÉt_Y` is fully faithful as soon as the completion functor
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is fully faithful on the finite locally free objects.

Two things are at stake in that statement and they are separated here.

* **What the conclusion says.** `𝒱` is a directed set, so the colimit of the categories `FÉt_V`
  is the one of Categories, Section 04AX: its objects are the covers at the finite stages and
  `Hom_{colim}(A, B) = colim_{V' ≥ V} Hom_{FÉt_{V'}}(A|_{V'}, B|_{V'})` for `A, B` at the stage
  `V`. Full faithfulness of a functor out of such a colimit is therefore exactly the pair of
  conditions recorded by `Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful`: every
  morphism between the restrictions to `Y` is the restriction of a morphism over some
  neighbourhood, and two morphisms over a neighbourhood that agree on `Y` agree after shrinking
  the neighbourhood. Note that both conditions are genuinely weaker than their pointwise
  analogues at a single `V`; the shrinking is the content.
* **What is proved.** The first paragraph of the source's proof: the category of finite étale
  coverings has an internal hom ([Stacks, Tag 0BL7]), so full faithfulness over the colimit
  follows from the statement that sections of a finite étale cover of a neighbourhood extend to
  a smaller neighbourhood and are determined there after further shrinking, which is
  `Stacks.FundamentalGroup.SectionsExtendNearSubscheme`. That reduction is the content of
  `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_sectionsExtendNearSubscheme`.

## Main definitions

* `Stacks.FundamentalGroup.SectionsExtendNearSubscheme` — sections of a finite étale cover of a
  neighbourhood of `Y` over `Y` extend to a smaller neighbourhood, and two sections over a
  neighbourhood that agree over `Y` agree after shrinking. Equivalently: for every neighbourhood
  `V` and every finite étale cover `U` of `V` the canonical map from the colimit over `V' ≥ V` of
  the sections of `U` over `V'` to the sections of `U` over `Y` is bijective.
* `Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful` — full faithfulness of the
  restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y`, expressed through the directed-colimit
  description of its hom sets.

## Main results

* `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_sectionsExtendNearSubscheme` —
  [Stacks, Tag 0ELA], granted the section-extension property. See the docstring there for
  exactly what is and is not covered: the completion hypothesis of the tag is **not** used, the
  shrinking form of the conclusion of [Stacks, Tag 0EL8] is granted in its place.

## Implementation notes

**Why sections are taken over a morphism.** A section of a finite étale cover `U` of `V` over a
smaller neighbourhood `V'` is recorded as a morphism `s : V' ⟶ U` with `s ≫ U.hom` the inclusion
`V' ⊆ V`, rather than as a section of the restricted cover `U|_{V'}`. The two are the same thing,
but in the first description restriction to a yet smaller neighbourhood, and to `Y`, is plain
precomposition; in the second it involves the comparison between iterated pullbacks. In
particular the system of section sets over the neighbourhoods is a strict functor, which is what
makes the colimit of the section sets an elementary object even though the colimit of the
categories `FÉt_V` is not.

**Where the comparison between iterated pullbacks does appear.** It cannot be avoided in the
conclusion: a morphism `φ` between covers of `V'` restricted to `Y` has source
`(A|_{V'})|_Y` whereas the morphism `f` it is compared with has source `A|_Y`, and these are two
independently chosen pullbacks. They are identified by
`Stacks.FundamentalGroup.Neighborhood.baseChangeCompIso`, and the fullness clause of
`FiniteEtaleColimitFullyFaithful` is accordingly the commuting square it fits in rather than a
plain equality.

**Shared material.** The identifications between morphisms of base-changed covers, morphisms
out of a product in the slice category, and sections live in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProdHomEquiv`. What is new here is
the compatibility of that identification with a *composite* base change, which is the form in
which it is needed when the base shrinks in two steps.

## References

* [Stacks Project, Tag 04AX](https://stacks.math.columbia.edu/tag/04AX)
* [Stacks Project, Tag 0BL7](https://stacks.math.columbia.edu/tag/0BL7)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FundamentalGroup

/-- **The identification of morphisms out of a product is compatible with a composite base
change.** Let `k = h ≫ g`. Restricting a morphism out of `A ×_S T` along `h`, and restricting
the corresponding morphism of covers of `T` along `h`, agree up to the comparison isomorphism
between base change along `k` and base change along `g` followed by base change along `h`.

This is the two-step form of `prodHomEquivBaseChangeHom_prod_map`, which is the case `g = 𝟙 S`. -/
private theorem prodHomEquivBaseChangeHom_prod_map_comp {S T T' : Scheme.{u}}
    (A B : FiniteEtaleOver S)
    (g : T ⟶ S) (h : T' ⟶ T) (k : T' ⟶ S) (hk : k = h ≫ g)
    (ξ : (Over.mk A.hom ⨯ Over.mk g : Over S) ⟶ Over.mk B.hom) :
    prodHomEquivBaseChangeHom A B k (prod.map (𝟙 (Over.mk A.hom : Over S))
          (Over.homMk h hk.symm : (Over.mk k : Over S) ⟶ Over.mk g) ≫ ξ) ≫
        (finiteEtaleBaseChangeComp h g k hk).hom.app B
      = (finiteEtaleBaseChangeComp h g k hk).hom.app A ≫
          (finiteEtaleBaseChange h).map (prodHomEquivBaseChangeHom A B g ξ) := by
  have hcomp : ∀ m : (finiteEtaleBaseChange k).obj A ⟶
      (finiteEtaleBaseChange h).obj ((finiteEtaleBaseChange g).obj B),
      (m.left ≫ finiteEtaleBaseChangeProj h ((finiteEtaleBaseChange g).obj B)) ≫
          ((finiteEtaleBaseChange g).obj B).hom
        = ((finiteEtaleBaseChange k).obj A).hom ≫ h := by
    intro m
    rw [Category.assoc, finiteEtaleBaseChangeProj_comp_hom, ← Category.assoc,
      MorphismProperty.Over.w m]
  refine finiteEtaleOver_hom_ext h
    (finiteEtaleBaseChangeProj_hom_ext g B ?_ ((hcomp _).trans (hcomp _).symm))
  have hkey : (prodLeftIsoBaseChange A k).inv ≫
        (prod.map (𝟙 (Over.mk A.hom : Over S))
          (Over.homMk h hk.symm : (Over.mk k : Over S) ⟶ Over.mk g)).left ≫
        (prodLeftIsoBaseChange A g).hom
      = ((finiteEtaleBaseChangeComp h g k hk).hom.app A).left ≫
          finiteEtaleBaseChangeProj h ((finiteEtaleBaseChange g).obj A) := by
    refine finiteEtaleBaseChangeProj_hom_ext g A ?_ ?_
    · rw [Category.assoc, Category.assoc, prodLeftIsoBaseChange_hom_proj, ← Over.comp_left,
        prod.map_fst,
        Over.comp_left, Over.id_left, Category.comp_id, prodLeftIsoBaseChange_inv_fst]
      exact (finiteEtaleBaseChangeComp_hom_app_left_proj h g k hk A).symm
    · rw [Category.assoc, Category.assoc, prodLeftIsoBaseChange_hom_hom, ← Over.comp_left,
        prod.map_snd,
        Over.comp_left, ← Category.assoc, prodLeftIsoBaseChange_inv_snd]
      change ((finiteEtaleBaseChange k).obj A).hom ≫ h
        = ((finiteEtaleBaseChangeComp h g k hk).hom.app A).left ≫
            finiteEtaleBaseChangeProj h ((finiteEtaleBaseChange g).obj A) ≫
            ((finiteEtaleBaseChange g).obj A).hom
      rw [finiteEtaleBaseChangeProj_comp_hom, ← Category.assoc]
      exact congrArg
        (fun z : ((finiteEtaleBaseChange k).obj A).left ⟶ T' => z ≫ h)
        (MorphismProperty.Over.w ((finiteEtaleBaseChangeComp h g k hk).hom.app A)).symm
  have hx : (prodLeftIsoBaseChange A k).inv ≫ (prod.map (𝟙 (Over.mk A.hom : Over S))
        (Over.homMk h hk.symm : (Over.mk k : Over S) ⟶ Over.mk g)).left ≫ ξ.left
      = ((finiteEtaleBaseChangeComp h g k hk).hom.app A).left ≫
          finiteEtaleBaseChangeProj h ((finiteEtaleBaseChange g).obj A) ≫
          (prodLeftIsoBaseChange A g).inv ≫ ξ.left := by
    rw [← Category.assoc ((finiteEtaleBaseChangeComp h g k hk).hom.app A).left, ← hkey]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, Category.assoc,
    Category.assoc, Category.assoc]
  rw [finiteEtaleBaseChangeComp_hom_app_left_proj h g k hk B]
  change baseChangeLift B k _ ≫ finiteEtaleBaseChangeProj k B
      = ((finiteEtaleBaseChangeComp h g k hk).hom.app A).left ≫
          (((finiteEtaleBaseChange h).map (prodHomEquivBaseChangeHom A B g ξ)).left ≫
            finiteEtaleBaseChangeProj h ((finiteEtaleBaseChange g).obj B)) ≫
          finiteEtaleBaseChangeProj g B
  rw [baseChangeLift_proj, finiteEtaleBaseChangeProj_naturality]
  change (prodLeftIsoBaseChange A k).inv ≫
      (prod.map (𝟙 (Over.mk A.hom : Over S))
        (Over.homMk h hk.symm : (Over.mk k : Over S) ⟶ Over.mk g) ≫ ξ).left
    = ((finiteEtaleBaseChangeComp h g k hk).hom.app A).left ≫
        (finiteEtaleBaseChangeProj h ((finiteEtaleBaseChange g).obj A) ≫
          (prodHomEquivBaseChangeHom A B g ξ).left) ≫ finiteEtaleBaseChangeProj g B
  change (prodLeftIsoBaseChange A k).inv ≫
      (prod.map (𝟙 (Over.mk A.hom : Over S))
        (Over.homMk h hk.symm : (Over.mk k : Over S) ⟶ Over.mk g) ≫ ξ).left
    = ((finiteEtaleBaseChangeComp h g k hk).hom.app A).left ≫
        (finiteEtaleBaseChangeProj h ((finiteEtaleBaseChange g).obj A) ≫
          baseChangeLift B g _) ≫ finiteEtaleBaseChangeProj g B
  rw [Category.assoc, baseChangeLift_proj, Over.comp_left]
  exact hx

/-! ### The section attached to a morphism of covers by the internal hom -/

/-- The section over `S` of the representing object `W` attached to a morphism of finite étale
covers `A ⟶ B` of `S`, through a representation `e` of the internal hom. -/
private def internalSection {S : Scheme.{u}} {A B : FiniteEtaleOver S} {W : Over S}
    (e : yoneda.obj W ≅ (prod.functor.obj (Over.mk A.hom)).op ⋙ yoneda.obj (Over.mk B.hom))
    (φ : A ⟶ B) : S ⟶ W.left :=
  ((Iso.toEquiv (e.app (Opposite.op (Over.mk (𝟙 S) : Over S)))).symm
    ((prodSelfHomEquiv A B).symm φ)).left

/-- The restriction along `g` of the section attached to a morphism of covers, as a morphism of
`S`-schemes from `T` into the representing object. -/
private def internalSectionOver {S T : Scheme.{u}} {A B : FiniteEtaleOver S} {W : Over S}
    (e : yoneda.obj W ≅ (prod.functor.obj (Over.mk A.hom)).op ⋙ yoneda.obj (Over.mk B.hom))
    (φ : A ⟶ B) (g : T ⟶ S) : (Over.mk g : Over S) ⟶ W :=
  overToSelf g ≫ (Iso.toEquiv (e.app (Opposite.op (Over.mk (𝟙 S) : Over S)))).symm
    ((prodSelfHomEquiv A B).symm φ)

/-- The underlying morphism of schemes of `internalSectionOver` is the restriction of the
section attached to the morphism of covers. -/
private theorem internalSectionOver_left {S T : Scheme.{u}} {A B : FiniteEtaleOver S}
    {W : Over S}
    (e : yoneda.obj W ≅ (prod.functor.obj (Over.mk A.hom)).op ⋙ yoneda.obj (Over.mk B.hom))
    (φ : A ⟶ B) (g : T ⟶ S) :
    (internalSectionOver e φ g).left = g ≫ internalSection e φ :=
  rfl

/-- The section attached to a morphism of covers is a section of the representing object. -/
private theorem internalSection_hom {S : Scheme.{u}} {A B : FiniteEtaleOver S} {W : Over S}
    (e : yoneda.obj W ≅ (prod.functor.obj (Over.mk A.hom)).op ⋙ yoneda.obj (Over.mk B.hom))
    (φ : A ⟶ B) : internalSection e φ ≫ W.hom = 𝟙 S :=
  Over.w _

/-- **Base change of a morphism of covers is restriction of its section.** The base change along
`g : T ⟶ S` of a morphism `φ : A ⟶ B` of finite étale covers of `S` corresponds, under the
representation `e` of the internal hom and the identification of morphisms out of a product, to
the restriction along `g` of the section attached to `φ`. -/
private theorem baseChange_map_eq {S T : Scheme.{u}} {A B : FiniteEtaleOver S} {W : Over S}
    (e : yoneda.obj W ≅ (prod.functor.obj (Over.mk A.hom)).op ⋙ yoneda.obj (Over.mk B.hom))
    (φ : A ⟶ B) (g : T ⟶ S) :
    (finiteEtaleBaseChange g).map φ
      = prodHomEquivBaseChangeHom A B g (Iso.toEquiv (e.app (Opposite.op (Over.mk g : Over S)))
          (internalSectionOver e φ g)) := by
  have hnat := NatTrans.naturality_apply e.hom (overToSelf g).op
    ((Iso.toEquiv (e.app (Opposite.op (Over.mk (𝟙 S) : Over S)))).symm
      ((prodSelfHomEquiv A B).symm φ))
  have h1 : Iso.toEquiv (e.app (Opposite.op (Over.mk g : Over S)))
        (internalSectionOver e φ g)
      = prod.map (𝟙 (Over.mk A.hom : Over S)) (overToSelf g) ≫
          Iso.toEquiv (e.app (Opposite.op (Over.mk (𝟙 S) : Over S)))
            ((Iso.toEquiv (e.app (Opposite.op (Over.mk (𝟙 S) : Over S)))).symm
              ((prodSelfHomEquiv A B).symm φ)) := hnat
  have h2 : Iso.toEquiv (e.app (Opposite.op (Over.mk g : Over S)))
        (internalSectionOver e φ g)
      = prod.map (𝟙 (Over.mk A.hom : Over S)) (overToSelf g) ≫
          (prodSelfHomEquiv A B).symm φ :=
    h1.trans (congrArg
      (fun z : (Over.mk A.hom ⨯ Over.mk (𝟙 S) : Over S) ⟶ Over.mk B.hom =>
        prod.map (𝟙 (Over.mk A.hom : Over S)) (overToSelf g) ≫ z)
      (Equiv.apply_symm_apply
        (Iso.toEquiv (e.app (Opposite.op (Over.mk (𝟙 S) : Over S))))
        ((prodSelfHomEquiv A B).symm φ)))
  refine ((congrArg (fun z : A ⟶ B => (finiteEtaleBaseChange g).map z)
      (Equiv.apply_symm_apply (prodSelfHomEquiv A B) φ)).symm.trans
    (prodHomEquivBaseChangeHom_prod_map g A B ((prodSelfHomEquiv A B).symm φ)).symm).trans ?_
  exact congrArg (fun z : (Over.mk A.hom ⨯ Over.mk g : Over S) ⟶ Over.mk B.hom =>
    prodHomEquivBaseChangeHom A B g z) h2.symm

/-- **Two morphisms of covers agree after a base change exactly when their sections do.** -/
private theorem baseChange_map_eq_iff {S T : Scheme.{u}} {A B : FiniteEtaleOver S} {W : Over S}
    (e : yoneda.obj W ≅ (prod.functor.obj (Over.mk A.hom)).op ⋙ yoneda.obj (Over.mk B.hom))
    (φ ψ : A ⟶ B) (g : T ⟶ S) :
    (finiteEtaleBaseChange g).map φ = (finiteEtaleBaseChange g).map ψ ↔
      g ≫ internalSection e φ = g ≫ internalSection e ψ := by
  rw [baseChange_map_eq e φ g, baseChange_map_eq e ψ g]
  constructor
  · intro hmap
    have hover := (Iso.toEquiv (e.app (Opposite.op (Over.mk g : Over S)))).injective
      ((prodHomEquivBaseChangeHom A B g).injective hmap)
    have hleft := congrArg (fun m : (Over.mk g : Over S) ⟶ W => m.left) hover
    rw [internalSectionOver_left, internalSectionOver_left] at hleft
    exact hleft
  · intro hsec
    exact congrArg (fun x : (Over.mk g : Over S) ⟶ W => prodHomEquivBaseChangeHom A B g
        (Iso.toEquiv (e.app (Opposite.op (Over.mk g : Over S))) x))
      (Over.OverMorphism.ext
        (by rw [internalSectionOver_left, internalSectionOver_left]; exact hsec))

/-! ### The two colimit conditions -/

variable (X : Scheme.{u}) (Y : X.IdealSheafData)

/-- **Sections of a finite étale cover extend to a neighbourhood of the closed subscheme,
uniquely after shrinking.** For every open neighbourhood `V` of the closed subscheme cut out by
`Y` and every finite étale cover `U` of `V`:

* every section of `U` over the closed subscheme is the restriction of a section of `U` over
  some smaller neighbourhood `V' ⊆ V`;
* two sections of `U` over a neighbourhood `V' ⊆ V` whose restrictions to the closed subscheme
  agree already agree over some smaller neighbourhood `V'' ⊆ V'`.

A section of `U` over `V'` is a morphism `V' ⟶ U` lying over the inclusion `V' ⊆ V`, so
restriction to a smaller neighbourhood and to the closed subscheme is precomposition and the
section sets form a strict functor on the neighbourhoods. Since the neighbourhoods are directed,
the two conditions together say exactly that the canonical map
`colim_{V' ⊆ V} Γ(V', U) ⟶ Γ(Y, U)` is bijective. -/
def SectionsExtendNearSubscheme : Prop :=
  (∀ (V : Neighborhood X Y) (U : FiniteEtaleOver (Neighborhood.open X Y V).toScheme)
      (t : Y.subscheme ⟶ U.left), t ≫ U.hom = Neighborhood.toSchemeHom X Y V →
    ∃ (V' : Neighborhood X Y) (i : V ⟶ V')
      (s : (Neighborhood.open X Y V').toScheme ⟶ U.left),
      s ≫ U.hom = X.homOfLE i.le ∧ Neighborhood.toSchemeHom X Y V' ≫ s = t) ∧
  (∀ (V V' : Neighborhood X Y) (i : V ⟶ V')
      (U : FiniteEtaleOver (Neighborhood.open X Y V).toScheme)
      (s₁ s₂ : (Neighborhood.open X Y V').toScheme ⟶ U.left),
      s₁ ≫ U.hom = X.homOfLE i.le → s₂ ≫ U.hom = X.homOfLE i.le →
      Neighborhood.toSchemeHom X Y V' ≫ s₁ = Neighborhood.toSchemeHom X Y V' ≫ s₂ →
    ∃ (V'' : Neighborhood X Y) (j : V' ⟶ V''),
      X.homOfLE j.le ≫ s₁ = X.homOfLE j.le ≫ s₂)

/-- **Full faithfulness of the restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y`.** The open
neighbourhoods `𝒱` of the closed subscheme cut out by `Y`, ordered by reverse inclusion, are
directed, so the colimit of the categories `FÉt_V` is the one of
[Stacks, Tag 04AX]: its objects are the finite étale covers of the individual neighbourhoods, and
`Hom_{colim}(A, B) = colim_{V' ⊆ V} Hom_{FÉt_{V'}}(A|_{V'}, B|_{V'})` for two covers `A`, `B` of
the neighbourhood `V`. Full faithfulness of the restriction functor to `FÉt_Y` is therefore the
conjunction of

* **fullness:** every morphism `A|_Y ⟶ B|_Y` is the restriction of a morphism
  `A|_{V'} ⟶ B|_{V'}` for some neighbourhood `V' ⊆ V`;
* **faithfulness:** two morphisms `A ⟶ B` of covers of `V` whose restrictions to the closed
  subscheme agree already agree after restriction to some neighbourhood `V' ⊆ V`.

Neither condition is implied by its pointwise analogue at a single neighbourhood, and neither
implies it: the quantifier over smaller neighbourhoods is the whole content.

In the fullness clause the restriction of `φ : A|_{V'} ⟶ B|_{V'}` to the closed subscheme has
source `(A|_{V'})|_Y` while `f` has source `A|_Y`; the two are identified by
`Stacks.FundamentalGroup.Neighborhood.baseChangeCompIso`, and the clause is stated as the square
that identification fits in. -/
def FiniteEtaleColimitFullyFaithful : Prop :=
  (∀ (V : Neighborhood X Y)
      (A B : FiniteEtaleOver (Neighborhood.open X Y V).toScheme)
      (f : (finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y V)).obj A ⟶
        (finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y V)).obj B),
    ∃ (V' : Neighborhood X Y) (i : V ⟶ V')
      (φ : (finiteEtaleBaseChange (X.homOfLE i.le)).obj A ⟶
        (finiteEtaleBaseChange (X.homOfLE i.le)).obj B),
      (Neighborhood.baseChangeCompIso X Y i).hom.app A ≫
          (finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y V')).map φ
        = f ≫ (Neighborhood.baseChangeCompIso X Y i).hom.app B) ∧
  (∀ (V : Neighborhood X Y)
      (A B : FiniteEtaleOver (Neighborhood.open X Y V).toScheme) (φ ψ : A ⟶ B),
      (finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y V)).map φ =
        (finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y V)).map ψ →
    ∃ (V' : Neighborhood X Y) (i : V ⟶ V'),
      (finiteEtaleBaseChange (X.homOfLE i.le)).map φ =
        (finiteEtaleBaseChange (X.homOfLE i.le)).map ψ)

/-! ### Tag 0ELA -/

/-- **[Stacks, Tag 0ELA], granted the section-extension input.** Let `X` be a scheme, let
`Y ⊆ X` be the closed subscheme cut out by the ideal sheaf `Y`, and let `𝒱` be the open
subschemes of `X` containing it, ordered by reverse inclusion. If sections of a finite étale
cover of a neighbourhood extend to a smaller neighbourhood and are determined there after
further shrinking, then the restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y` is fully faithful.

This is the first paragraph of the source's proof, which is the only part of it that is about
finite étale covers: the category of finite étale coverings has an internal hom
([Stacks, Tag 0BL7]), and a section of the internal hom `Hom_V(A, B)` over a base is exactly a
morphism `A ⟶ B` after that base change, so a morphism between the restrictions to the closed
subscheme is a section of the internal hom over the closed subscheme and full faithfulness over
the colimit is the extension property for sections of one finite étale cover.

**What is granted and what is not.** The hypothesis of the tag — full faithfulness of the
completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` on the finite locally free objects — is
**not** used here at all: the section-extension property
`Stacks.FundamentalGroup.SectionsExtendNearSubscheme` is assumed in its place. That property is
the shrinking form of the conclusion of [Stacks, Tag 0EL8], and deducing it from the completion
hypothesis is the rest of the source's proof: lift the section over the closed subscheme to the
infinitesimal neighbourhoods ([Stacks, Tag 0BQB]), algebraize the resulting compatible system of
module maps out of the finite locally free module `f _* 𝒪_U` over some smaller neighbourhood by
fullness of completion, and shrink once more to make the algebraized map multiplicative by
faithfulness of completion. That half is carried in this library only in its non-shrinking form,
on the nose at a single scheme, as
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithful`; the
shrinking form would need the restriction of a direct image algebra to an open subscheme and the
comparison of the infinitesimal neighbourhoods of the closed subscheme taken inside `X` and
inside a neighbourhood, neither of which has a carrier here.

It is **not** enough to assume the pointwise analogue of the hypothesis at each individual
neighbourhood, which would make the statement a formal consequence of Tag 0EL8 applied one
neighbourhood at a time. The quantifiers over smaller neighbourhoods in both
`SectionsExtendNearSubscheme` and `FiniteEtaleColimitFullyFaithful` are the content. -/
@[stacks 0ELA "granted SectionsExtendNearSubscheme: the shrinking form of Tag 0EL8"]
theorem finiteEtaleColimitFullyFaithful_of_sectionsExtendNearSubscheme
    (h : SectionsExtendNearSubscheme X Y) : FiniteEtaleColimitFullyFaithful X Y := by
  obtain ⟨hextend, hunique⟩ := h
  constructor
  · intro V A B f
    have _ : IsFinite (Over.mk A.hom :
      Over (Neighborhood.open X Y V).toScheme).hom := A.prop.1
    have _ : Etale (Over.mk A.hom : Over (Neighborhood.open X Y V).toScheme).hom := A.prop.2
    have _ : IsFinite (Over.mk B.hom :
      Over (Neighborhood.open X Y V).toScheme).hom := B.prop.1
    have _ : Etale (Over.mk B.hom : Over (Neighborhood.open X Y V).toScheme).hom := B.prop.2
    obtain ⟨W, hWfin, hWet, ⟨e⟩⟩ := exists_finiteEtale_internalHom
      (Neighborhood.open X Y V).toScheme (Over.mk A.hom) (Over.mk B.hom)
    obtain ⟨V', i, s, hs, hst⟩ := hextend V
      (MorphismProperty.Over.mk ⊤ W.hom ⟨hWfin, hWet⟩)
      ((Iso.toEquiv (e.app (Opposite.op (Over.mk (Neighborhood.toSchemeHom X Y V) :
        Over (Neighborhood.open X Y V).toScheme)))).symm
        ((prodHomEquivBaseChangeHom A B (Neighborhood.toSchemeHom X Y V)).symm f)).left
      (Over.w _)
    refine ⟨V', i, prodHomEquivBaseChangeHom A B (X.homOfLE i.le)
      (Iso.toEquiv (e.app (Opposite.op (Over.mk (X.homOfLE i.le) :
        Over (Neighborhood.open X Y V).toScheme))) (Over.homMk s hs)), ?_⟩
    have hnat := NatTrans.naturality_apply e.hom
      (Over.homMk (Neighborhood.toSchemeHom X Y V')
          (Neighborhood.toSchemeHom_comp X Y i) :
        (Over.mk (Neighborhood.toSchemeHom X Y V) :
          Over (Neighborhood.open X Y V).toScheme) ⟶ Over.mk (X.homOfLE i.le)).op
      (Over.homMk s hs : (Over.mk (X.homOfLE i.le) :
        Over (Neighborhood.open X Y V).toScheme) ⟶ W)
    have hsec : (Over.homMk (Neighborhood.toSchemeHom X Y V')
            (Neighborhood.toSchemeHom_comp X Y i) :
          (Over.mk (Neighborhood.toSchemeHom X Y V) :
            Over (Neighborhood.open X Y V).toScheme) ⟶ Over.mk (X.homOfLE i.le)) ≫
          (Over.homMk s hs : (Over.mk (X.homOfLE i.le) :
            Over (Neighborhood.open X Y V).toScheme) ⟶ W)
        = (Iso.toEquiv (e.app (Opposite.op (Over.mk (Neighborhood.toSchemeHom X Y V) :
            Over (Neighborhood.open X Y V).toScheme)))).symm
            ((prodHomEquivBaseChangeHom A B (Neighborhood.toSchemeHom X Y V)).symm f) :=
      Over.OverMorphism.ext hst
    have hnat2 : Iso.toEquiv (e.app (Opposite.op (Over.mk (Neighborhood.toSchemeHom X Y V) :
            Over (Neighborhood.open X Y V).toScheme)))
          ((Over.homMk (Neighborhood.toSchemeHom X Y V')
                (Neighborhood.toSchemeHom_comp X Y i) :
              (Over.mk (Neighborhood.toSchemeHom X Y V) :
                Over (Neighborhood.open X Y V).toScheme) ⟶ Over.mk (X.homOfLE i.le)) ≫
            (Over.homMk s hs : (Over.mk (X.homOfLE i.le) :
              Over (Neighborhood.open X Y V).toScheme) ⟶ W))
        = prod.map (𝟙 (Over.mk A.hom : Over (Neighborhood.open X Y V).toScheme))
            (Over.homMk (Neighborhood.toSchemeHom X Y V')
                (Neighborhood.toSchemeHom_comp X Y i) :
              (Over.mk (Neighborhood.toSchemeHom X Y V) :
                Over (Neighborhood.open X Y V).toScheme) ⟶ Over.mk (X.homOfLE i.le)) ≫
          Iso.toEquiv (e.app (Opposite.op (Over.mk (X.homOfLE i.le) :
            Over (Neighborhood.open X Y V).toScheme))) (Over.homMk s hs) := hnat
    have hf : f = prodHomEquivBaseChangeHom A B (Neighborhood.toSchemeHom X Y V)
        (prod.map (𝟙 (Over.mk A.hom : Over (Neighborhood.open X Y V).toScheme))
            (Over.homMk (Neighborhood.toSchemeHom X Y V')
                (Neighborhood.toSchemeHom_comp X Y i) :
              (Over.mk (Neighborhood.toSchemeHom X Y V) :
                Over (Neighborhood.open X Y V).toScheme) ⟶ Over.mk (X.homOfLE i.le)) ≫
          Iso.toEquiv (e.app (Opposite.op (Over.mk (X.homOfLE i.le) :
            Over (Neighborhood.open X Y V).toScheme))) (Over.homMk s hs)) :=
      (Equiv.apply_symm_apply (prodHomEquivBaseChangeHom A B (Neighborhood.toSchemeHom X Y V))
          f).symm.trans
        (congrArg
          (fun z : (Over.mk A.hom ⨯ Over.mk (Neighborhood.toSchemeHom X Y V) :
              Over (Neighborhood.open X Y V).toScheme) ⟶ Over.mk B.hom =>
            prodHomEquivBaseChangeHom A B (Neighborhood.toSchemeHom X Y V) z)
          (((Equiv.apply_symm_apply
                (Iso.toEquiv (e.app (Opposite.op (Over.mk (Neighborhood.toSchemeHom X Y V) :
                  Over (Neighborhood.open X Y V).toScheme))))
                ((prodHomEquivBaseChangeHom A B (Neighborhood.toSchemeHom X Y V)).symm
                    f)).symm.trans
            (congrArg
              (fun z : (Over.mk (Neighborhood.toSchemeHom X Y V) :
                  Over (Neighborhood.open X Y V).toScheme) ⟶ W =>
                Iso.toEquiv (e.app (Opposite.op (Over.mk (Neighborhood.toSchemeHom X Y V) :
                  Over (Neighborhood.open X Y V).toScheme))) z) hsec.symm)).trans hnat2))
    exact (prodHomEquivBaseChangeHom_prod_map_comp A B (X.homOfLE i.le)
          (Neighborhood.toSchemeHom X Y V') (Neighborhood.toSchemeHom X Y V)
          (Neighborhood.toSchemeHom_comp X Y i).symm _).symm.trans
      (congrArg (fun z : (finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y V)).obj A ⟶
            (finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y V)).obj B =>
          z ≫ (Neighborhood.baseChangeCompIso X Y i).hom.app B) hf.symm)
  · intro V A B φ ψ hφψ
    have _ : IsFinite (Over.mk A.hom :
      Over (Neighborhood.open X Y V).toScheme).hom := A.prop.1
    have _ : Etale (Over.mk A.hom : Over (Neighborhood.open X Y V).toScheme).hom := A.prop.2
    have _ : IsFinite (Over.mk B.hom :
      Over (Neighborhood.open X Y V).toScheme).hom := B.prop.1
    have _ : Etale (Over.mk B.hom : Over (Neighborhood.open X Y V).toScheme).hom := B.prop.2
    obtain ⟨W, hWfin, hWet, ⟨e⟩⟩ := exists_finiteEtale_internalHom
      (Neighborhood.open X Y V).toScheme (Over.mk A.hom) (Over.mk B.hom)
    have hsec : Neighborhood.toSchemeHom X Y V ≫ internalSection e φ
        = Neighborhood.toSchemeHom X Y V ≫ internalSection e ψ :=
      (baseChange_map_eq_iff e φ ψ (Neighborhood.toSchemeHom X Y V)).mp hφψ
    have hid : X.homOfLE (𝟙 V).le = 𝟙 (Neighborhood.open X Y V).toScheme :=
      Scheme.homOfLE_rfl X _
    obtain ⟨V', i, hshrink⟩ := hunique V V (𝟙 V)
      (MorphismProperty.Over.mk ⊤ W.hom ⟨hWfin, hWet⟩)
      (internalSection e φ) (internalSection e ψ)
      ((internalSection_hom e φ).trans hid.symm)
      ((internalSection_hom e ψ).trans hid.symm) hsec
    exact ⟨V', i, (baseChange_map_eq_iff e φ ψ (X.homOfLE i.le)).mpr hshrink⟩

end Stacks.FundamentalGroup

end
