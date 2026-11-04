module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.HomologyOnACategory
public import StacksFrontier.CategoryTheory.Abelian.Projective.DerivedTransfer
import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of the homology of a category

Let `f : C' ⥤ C` be a functor between small categories, let `F` be an abelian presheaf on `C`,
let `F'` be an abelian presheaf on `C'`, and let `t : F' ⟶ f.op ⋙ F` be a morphism to the
inverse image of `F`. This file constructs the canonical map `H_n(C', F') ⟶ H_n(C, F)` in every
degree and proves that it is compatible with identities, with composition, and with natural
isomorphisms of the indexing functors.

Write `res f` for restriction of presheaves along `f`, `presheafRestriction f`, which is exact.
Let `P` be the chosen projective resolution of `F` and `R` that of `F'`. Then `res f` applied to
`P` is a resolution of `f.op ⋙ F`, so `t` lifts to a chain map `R.complex ⟶ res f (P.complex)`,
unique up to homotopy. Applying `colim` over `C'ᵒᵖ` and composing with the canonical comparison
`colim_{C'ᵒᵖ} (f.op ⋙ G) ⟶ colim_{Cᵒᵖ} G`, which is `Limits.colimit.pre G f.op`, gives a map of
complexes whose homology is the map wanted.

## Main definitions

* `Stacks.CategoryHomology.presheafRestriction`: restriction of abelian presheaves along a
  functor.
* `Stacks.CategoryHomology.diagramColimitRestrictionPre`: the comparison
  `colim_{C'ᵒᵖ} ∘ res f ⟶ colim_{Cᵒᵖ}` at arbitrary coefficients, and
  `Stacks.CategoryHomology.colimitRestrictionPre`: the same at abelian coefficients.
* `Stacks.CategoryHomology.categoryHomologyMap`: the canonical map
  `H_n(C', F') ⟶ H_n(C, F)` induced by `f` and `t`.
* `Stacks.CategoryHomology.CategoryHomologyMapData`: the canonical maps packaged with their
  invariance under natural isomorphisms of indexing functors.

## Main results

* `Stacks.CategoryHomology.categoryHomologyMap_id` and
  `Stacks.CategoryHomology.categoryHomologyMap_comp`: the identity and composition laws.
* `Stacks.CategoryHomology.categoryHomologyMap_iso`: naturally isomorphic indexing functors with
  correspondingly reindexed coefficient morphisms induce the same map on homology.

## Implementation notes

The two categories may live in different universes, while the two presheaves take values in one
common universe `max u u' v` of abelian groups. At that universe the instance
`Stacks.CategoryHomology.presheafEnoughProjectives`, of shape
`EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})`, is not found by instance search: Lean's
level unifier does not solve `max u' ?v =?= max u u' v`. The construction is therefore stated
with `EnoughProjectives` as a hypothesis, and the public declarations supply it with explicit
universes.

## References

* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category

universe u u' u'' v uD vD

namespace Stacks.CategoryHomology

/-- Precomposition with a functor is an additive functor between functor categories into a
preadditive category. -/
@[ega "III 7.1.3" "more general"]
instance additive_whiskeringLeft_obj {X Y Z : Type*} [Category X] [Category Y] [Category Z]
    [Preadditive Z] (F : X ⥤ Y) : ((Functor.whiskeringLeft X Y Z).obj F).Additive where
  map_add := by intros; ext; simp

section Restriction

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C']

/-- Restriction of abelian presheaves along a functor `f : C' ⥤ C`, that is, precomposition with
`f.op`. On a site with the chaotic topology this is the inverse image functor. -/
@[sga "4 I 5.0" "special case"]
abbrev presheafRestriction (f : C' ⥤ C) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v} :=
  (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ AddCommGrpCat.{max u u' v}).obj f.op

/-- Restriction along a composite is the composite of the restrictions, on the nose. -/
lemma presheafRestriction_comp_map {C'' : Type u''} [SmallCategory C''] (f : C' ⥤ C)
    (g : C'' ⥤ C') {G H : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}} (β : G ⟶ H) :
    (presheafRestriction.{u, u'', max u' v} (g ⋙ f)).map β =
      (presheafRestriction.{u', u'', max u v} g).map
        ((presheafRestriction.{u, u', max u'' v} f).map β) :=
  rfl

/-- The natural transformation between restriction functors induced by a natural transformation
`α : g.op ⟶ f.op` of indexing functors. -/
def presheafRestrictionMap (f g : C' ⥤ C) (α : g.op ⟶ f.op) :
    presheafRestriction.{u, u', v} g ⟶ presheafRestriction.{u, u', v} f where
  app G := Functor.whiskerRight α G
  naturality _ _ β := NatTrans.ext (funext fun c => (β.naturality (α.app c)).symm)

/-- The components of `Stacks.CategoryHomology.presheafRestrictionMap`. Deliberately not a `simp`
lemma: the two sides are spelled at defeq but syntactically different types, so rewriting with it
can leave a goal that is no longer type-correct at `implicit` transparency. -/
lemma presheafRestrictionMap_app (f g : C' ⥤ C) (α : g.op ⟶ f.op)
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) :
    (presheafRestrictionMap.{u, u', v} f g α).app G = Functor.whiskerRight α G :=
  rfl

/-- `Stacks.CategoryHomology.presheafRestrictionMap` on chain complexes of presheaves. -/
abbrev presheafRestrictionMapComplex (f g : C' ⥤ C) (α : g.op ⟶ f.op)
    (K : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ℕ) :
    ((presheafRestriction.{u, u', v} g).mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
      ((presheafRestriction.{u, u', v} f).mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
  (NatTrans.mapHomologicalComplex (presheafRestrictionMap.{u, u', v} f g α)
    (ComplexShape.down ℕ)).app K

/-- The canonical comparison from the colimit over `C'ᵒᵖ` of the restriction of a diagram along
`f` to the colimit of the diagram itself, as a natural transformation
`res f ⋙ colim_{C'ᵒᵖ} ⟶ colim_{Cᵒᵖ}`, at arbitrary coefficients `D`. Its component at `G` is
`Limits.colimit.pre G f.op`. -/
@[sga "4 I 8.2.3"]
def diagramColimitRestrictionPre (f : C' ⥤ C) (D : Type uD) [Category.{vD} D]
    [HasColimitsOfShape Cᵒᵖ D] [HasColimitsOfShape C'ᵒᵖ D] :
    (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op ⋙ (colim : (C'ᵒᵖ ⥤ D) ⥤ D) ⟶
      (colim : (Cᵒᵖ ⥤ D) ⥤ D) where
  app G := colimit.pre G f.op
  naturality _ _ α := (colimit.pre_map α f.op).symm

/-- The canonical comparison from the colimit over `C'ᵒᵖ` of the restriction of a presheaf to the
colimit of the presheaf itself, as a natural transformation
`res f ⋙ colim_{C'ᵒᵖ} ⟶ colim_{Cᵒᵖ}`. This is
`Stacks.CategoryHomology.diagramColimitRestrictionPre` at abelian coefficients. -/
def colimitRestrictionPre (f : C' ⥤ C) :
    presheafRestriction.{u, u', v} f ⋙ (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _) ⟶
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _) :=
  diagramColimitRestrictionPre f AddCommGrpCat.{max u u' v}

/-- The components of `Stacks.CategoryHomology.colimitRestrictionPre`. Deliberately not a `simp`
lemma, for the reason given at `Stacks.CategoryHomology.presheafRestrictionMap_app`. -/
lemma colimitRestrictionPre_app (f : C' ⥤ C) (G : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) :
    (colimitRestrictionPre.{u, u', v} f).app G = colimit.pre G f.op :=
  rfl

/-- `Stacks.CategoryHomology.colimitRestrictionPre` on chain complexes. -/
abbrev colimitRestrictionPreComplex (f : C' ⥤ C)
    (K : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ℕ) :
    ((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
      (((presheafRestriction.{u, u', v} f).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) ⟶
    ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K :=
  (NatTrans.mapHomologicalComplex (colimitRestrictionPre.{u, u', v} f)
    (ComplexShape.down ℕ)).app K

/-- Reindexing the comparison `Stacks.CategoryHomology.colimitRestrictionPre` by a natural
transformation of indexing functors. -/
lemma colimitRestrictionPreComplex_restrictionMap (f g : C' ⥤ C) (α : g.op ⟶ f.op)
    (K : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ℕ) :
    ((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (presheafRestrictionMapComplex.{u, u', v} f g α K) ≫
        colimitRestrictionPreComplex.{u, u', v} f K =
      colimitRestrictionPreComplex.{u, u', v} g K := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  simpa [presheafRestrictionMap_app, colimitRestrictionPre_app] using
    (colimit.pre_map' (K.X i) α).symm

end Restriction

section Identity

variable {C : Type u} [SmallCategory C]

/-- The comparison `colimit.pre G (𝟭 C).op` for the identity functor is the identity. -/
lemma colimitPre_op_id (G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    colimit.pre G ((𝟭 C).op) = 𝟙 (colimit G) :=
  (colimit.pre_id (J := Cᵒᵖ) G).trans (colim.map_id G)

end Identity

section Composition

variable {C : Type u} {C' : Type u'} {C'' : Type u''} [SmallCategory C] [SmallCategory C']
  [SmallCategory C'']

/-- The comparison `Stacks.CategoryHomology.colimitRestrictionPreComplex` for a composite is the
composite of the comparisons, interleaved with a chain map out of the restriction. -/
lemma colimitRestrictionPreComplex_comp (f : C' ⥤ C) (g : C'' ⥤ C')
    {K : ChainComplex (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}) ℕ}
    {M : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}) ℕ}
    (ψ : K ⟶ ((presheafRestriction.{u, u', max u'' v} f).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj M) :
    ((colim : (C''ᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}) ⥤ _).mapHomologicalComplex
            (ComplexShape.down ℕ)).map
          (((presheafRestriction.{u', u'', max u v} g).mapHomologicalComplex
            (ComplexShape.down ℕ)).map ψ) ≫
        colimitRestrictionPreComplex.{u, u'', max u' v} (g ⋙ f) M =
      colimitRestrictionPreComplex.{u', u'', max u v} g K ≫
        (((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}) ⥤ _).mapHomologicalComplex
            (ComplexShape.down ℕ)).map ψ ≫
          colimitRestrictionPreComplex.{u, u', max u'' v} f M) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  have h1 : colimit.pre (K.X i) g.op ≫ colim.map (ψ.f i) =
      colim.map (Functor.whiskerLeft g.op (ψ.f i)) ≫ colimit.pre (f.op ⋙ M.X i) g.op :=
    colimit.pre_map _ _
  have h2 := colimit.pre_pre (M.X i) f.op g.op
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, colimitRestrictionPre_app]
  rw [← assoc, h1, assoc, h2]
  rfl

/-- The augmentation obtained by restricting along a composite is the iterated restriction of the
augmentation. -/
lemma presheafRestriction_comp_mapAugmentation (f : C' ⥤ C) (g : C'' ⥤ C')
    {Q : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}) ℕ}
    {Z : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}}
    (ε : Q ⟶ (ChainComplex.single₀ (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v})).obj Z) :
    (presheafRestriction.{u, u'', max u' v} (g ⋙ f)).mapAugmentation ε =
      (presheafRestriction.{u', u'', max u v} g).mapAugmentation
        ((presheafRestriction.{u, u', max u'' v} f).mapAugmentation ε) := by
  refine HomologicalComplex.to_single_hom_ext ?_
  simp only [Functor.mapAugmentation_f_zero]
  exact presheafRestriction_comp_map f g (ε.f 0)

end Composition

section Aux

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C']
  [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]
  [EnoughProjectives (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]

/-- The map on homology induced by `f : C' ⥤ C` and `t : F' ⟶ f.op ⋙ F`, with the
`EnoughProjectives` instances as hypotheses. -/
def homologyMapAux (f : C' ⥤ C) {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} (t : F' ⟶ f.op ⋙ F) (n : ℕ) :
    ((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerived n).obj F' ⟶
      ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerived n).obj F :=
  ProjectiveResolution.transferHomology colim (ProjectiveResolution.of F')
      ((presheafRestriction.{u, u', v} f).mapAugmentation (ProjectiveResolution.of F).π) t
      (colimitRestrictionPreComplex.{u, u', v} f (ProjectiveResolution.of F).complex) n ≫
    ((ProjectiveResolution.of F).isoLeftDerivedObj colim n).inv

/-- Any chain map from the chosen projective resolution of `F'` into the restriction of the chosen
projective resolution of `F` which is compatible with the augmentations computes
`Stacks.CategoryHomology.homologyMapAux`. -/
theorem homologyMapAux_eq (f : C' ⥤ C) {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} (t : F' ⟶ f.op ⋙ F) (n : ℕ)
    (φ : (ProjectiveResolution.of F').complex ⟶
      ((presheafRestriction.{u, u', v} f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (ProjectiveResolution.of F).complex)
    (hφ : φ ≫ (presheafRestriction.{u, u', v} f).mapAugmentation (ProjectiveResolution.of F).π =
      (ProjectiveResolution.of F').π ≫ (ChainComplex.single₀ _).map t) :
    homologyMapAux.{u, u', v} f t n =
      ((ProjectiveResolution.of F').isoLeftDerivedObj colim n).hom ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u u' v}
            (ComplexShape.down ℕ) n).map
          (((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).mapHomologicalComplex
              (ComplexShape.down ℕ)).map φ ≫
            colimitRestrictionPreComplex.{u, u', v} f (ProjectiveResolution.of F).complex) ≫
        ((ProjectiveResolution.of F).isoLeftDerivedObj colim n).inv := by
  dsimp only [homologyMapAux]
  rw [ProjectiveResolution.transferHomology_eq colim (ProjectiveResolution.of F')
      ((presheafRestriction.{u, u', v} f).mapAugmentation (ProjectiveResolution.of F).π) t
      (colimitRestrictionPreComplex.{u, u', v} f (ProjectiveResolution.of F).complex) n φ hφ]
  exact Category.assoc _ _ _

/-- Naturally isomorphic indexing functors, with coefficient morphisms matching under the induced
reindexing, induce the same map on homology. -/
theorem homologyMapAux_iso (f g : C' ⥤ C) (e : f ≅ g)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) (s : F' ⟶ g.op ⋙ F)
    (h : t = s ≫ Functor.whiskerRight (NatTrans.op e.hom) F) (n : ℕ) :
    homologyMapAux.{u, u', v} f t n = homologyMapAux.{u, u', v} g s n := by
  have haug : presheafRestrictionMapComplex.{u, u', v} f g (NatTrans.op e.hom)
          (ProjectiveResolution.of F).complex ≫
        (presheafRestriction.{u, u', v} f).mapAugmentation (ProjectiveResolution.of F).π =
      (presheafRestriction.{u, u', v} g).mapAugmentation (ProjectiveResolution.of F).π ≫
        (ChainComplex.single₀ _).map
          ((presheafRestrictionMap.{u, u', v} f g (NatTrans.op e.hom)).app F) := by
    refine HomologicalComplex.to_single_hom_ext ?_
    simpa using
      ((presheafRestrictionMap.{u, u', v} f g (NatTrans.op e.hom)).naturality
        ((ProjectiveResolution.of F).π.f 0)).symm
  have hψ := ProjectiveResolution.lift'_commutes s (ProjectiveResolution.of F')
    ((presheafRestriction.{u, u', v} g).mapAugmentation (ProjectiveResolution.of F).π)
  have hφ : (ProjectiveResolution.lift' s (ProjectiveResolution.of F')
          ((presheafRestriction.{u, u', v} g).mapAugmentation (ProjectiveResolution.of F).π) ≫
        presheafRestrictionMapComplex.{u, u', v} f g (NatTrans.op e.hom)
          (ProjectiveResolution.of F).complex) ≫
      (presheafRestriction.{u, u', v} f).mapAugmentation (ProjectiveResolution.of F).π =
      (ProjectiveResolution.of F').π ≫ (ChainComplex.single₀ _).map t := by
    rw [assoc, haug, ← assoc, hψ, assoc, ← Functor.map_comp, h]
    rfl
  rw [homologyMapAux_eq f t n _ hφ, homologyMapAux_eq g s n _ hψ,
    Functor.map_comp (colim.mapHomologicalComplex (ComplexShape.down ℕ)), assoc,
    colimitRestrictionPreComplex_restrictionMap]

end Aux

section AuxIdentity

variable {C : Type u} [SmallCategory C] [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})]

/-- The identity functor and the identity coefficient morphism induce the identity on homology. -/
theorem homologyMapAux_id (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    homologyMapAux.{u, u, v} (𝟭 C) (𝟙 F) n = 𝟙 _ := by
  have hφ : 𝟙 (ProjectiveResolution.of F).complex ≫
      (presheafRestriction.{u, u, v} (𝟭 C)).mapAugmentation (ProjectiveResolution.of F).π =
      (ProjectiveResolution.of F).π ≫ (ChainComplex.single₀ _).map (𝟙 F) := by
    refine ProjectiveResolution.comp_single₀_map_eq_of_f_zero _ _ _ _ ?_
    simp only [HomologicalComplex.id_f, id_comp, Functor.mapAugmentation_f_zero]
    rfl
  have key : ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).mapHomologicalComplex
            (ComplexShape.down ℕ)).map (𝟙 (ProjectiveResolution.of F).complex) ≫
        colimitRestrictionPreComplex.{u, u, v} (𝟭 C) (ProjectiveResolution.of F).complex =
      𝟙 (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ _).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (ProjectiveResolution.of F).complex) := by
    refine HomologicalComplex.hom_ext _ _ fun i => ?_
    simpa [colimitRestrictionPre_app] using
      colimitPre_op_id.{u, v} ((ProjectiveResolution.of F).complex.X i)
  rw [homologyMapAux_eq (𝟭 C) (𝟙 F) n _ hφ, key, CategoryTheory.Functor.map_id, id_comp,
    Iso.hom_inv_id]

end AuxIdentity

section AuxComposition

variable {C : Type u} {C' : Type u'} {C'' : Type u''} [SmallCategory C] [SmallCategory C']
  [SmallCategory C''] [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v})]
  [EnoughProjectives (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v})]
  [EnoughProjectives (C''ᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v})]

/-- The maps on homology compose. -/
theorem homologyMapAux_comp (f : C' ⥤ C) (g : C'' ⥤ C')
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}}
    {F'' : C''ᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}} (t : F' ⟶ f.op ⋙ F) (s : F'' ⟶ g.op ⋙ F')
    (n : ℕ) :
    homologyMapAux.{u, u'', max u' v} (g ⋙ f) (s ≫ Functor.whiskerLeft g.op t) n =
      homologyMapAux.{u', u'', max u v} g s n ≫ homologyMapAux.{u, u', max u'' v} f t n := by
  have hψf := ProjectiveResolution.lift'_commutes t (ProjectiveResolution.of F')
    ((presheafRestriction.{u, u', max u'' v} f).mapAugmentation (ProjectiveResolution.of F).π)
  have hψg := ProjectiveResolution.lift'_commutes s (ProjectiveResolution.of F'')
    ((presheafRestriction.{u', u'', max u v} g).mapAugmentation (ProjectiveResolution.of F').π)
  have hφ : (ProjectiveResolution.lift' s (ProjectiveResolution.of F'')
            ((presheafRestriction.{u', u'', max u v} g).mapAugmentation
              (ProjectiveResolution.of F').π) ≫
          ((presheafRestriction.{u', u'', max u v} g).mapHomologicalComplex
              (ComplexShape.down ℕ)).map
            (ProjectiveResolution.lift' t (ProjectiveResolution.of F')
              ((presheafRestriction.{u, u', max u'' v} f).mapAugmentation
                (ProjectiveResolution.of F).π))) ≫
        (presheafRestriction.{u, u'', max u' v} (g ⋙ f)).mapAugmentation
          (ProjectiveResolution.of F).π =
      (ProjectiveResolution.of F'').π ≫
        (ChainComplex.single₀ _).map (s ≫ Functor.whiskerLeft g.op t) := by
    rw [presheafRestriction_comp_mapAugmentation f g, assoc,
      Functor.map_comp_mapAugmentation, hψf, Functor.mapAugmentation_comp_single₀_map,
      ← assoc, hψg, assoc, ← CategoryTheory.Functor.map_comp]
    rfl
  rw [homologyMapAux_eq (g ⋙ f) _ n _ hφ, homologyMapAux_eq g s n _ hψg,
    homologyMapAux_eq f t n _ hψf]
  rw [Functor.map_comp (colim.mapHomologicalComplex (ComplexShape.down ℕ)), assoc,
    colimitRestrictionPreComplex_comp]
  simp only [Functor.map_comp, assoc, Iso.inv_hom_id_assoc]

end AuxComposition

section Card

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C']

/-- The canonical maps on homology induced by an indexing functor and a coefficient morphism,
including their independence under a natural isomorphism of indexing functors. Since the
coefficients are contravariant, `NatTrans.op e.hom` reindexes coefficients from `g` to `f`. -/
structure CategoryHomologyMapData (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v})
    (F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) (n : ℕ) where
  /-- The map induced by an indexing functor and a coefficient morphism. -/
  map (f : C' ⥤ C) (t : F' ⟶ f.op ⋙ F) :
    categoryHomology.{u', max u v} F' n ⟶ categoryHomology.{u, max u' v} F n
  /-- Reindexing by a natural isomorphism preserves the induced homology map. -/
  map_iso (f g : C' ⥤ C) (e : f ≅ g) (t : F' ⟶ f.op ⋙ F) (s : F' ⟶ g.op ⋙ F)
      (h : t = s ≫ Functor.whiskerRight (NatTrans.op e.hom) F) :
    map f t = map g s

/-- The canonical maps on the homology of a category induced by an indexing functor and a
coefficient morphism, together with their invariance under natural isomorphisms of indexing
functors. -/
@[stacks 08PH "homology_map"]
def categoryHomologyMapData (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v})
    (F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) (n : ℕ) : CategoryHomologyMapData F F' n := by
  haveI := presheafEnoughProjectives.{u, max u' v} C
  haveI := presheafEnoughProjectives.{u', max u v} C'
  exact
    { map := fun f t => homologyMapAux.{u, u', v} f t n
      map_iso := fun f g e t s h => homologyMapAux_iso.{u, u', v} f g e t s h n }

/-- The canonical map on homology induced by a functor `f : C' ⥤ C` and a
morphism `t : F' ⟶ f.op ⋙ F` to the inverse-image presheaf. -/
@[stacks 08PH "homology_map"]
def categoryHomologyMap (f : C' ⥤ C) {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} (t : F' ⟶ f.op ⋙ F) (n : ℕ) :
    categoryHomology.{u', max u v} F' n ⟶ categoryHomology.{u, max u' v} F n :=
  (categoryHomologyMapData F F' n).map f t

/-- Naturally isomorphic functors induce the same map on category homology when the coefficient
morphisms agree under the induced reindexing isomorphism. -/
@[stacks 08PH "homology_map"]
theorem categoryHomologyMap_iso (f g : C' ⥤ C) (e : f ≅ g)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) (s : F' ⟶ g.op ⋙ F)
    (h : t = s ≫ Functor.whiskerRight (NatTrans.op e.hom) F) (n : ℕ) :
    categoryHomologyMap f t n = categoryHomologyMap g s n :=
  (categoryHomologyMapData F F' n).map_iso f g e t s h

/-- The canonical map associated with the identity functor and the identity
coefficient morphism is the identity on homology. -/
@[stacks 08PH "homology_map"]
theorem categoryHomologyMap_id {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    categoryHomologyMap (𝟭 C) (𝟙 F) n = 𝟙 _ := by
  have := presheafEnoughProjectives.{u, max u v} C
  exact homologyMapAux_id.{u, v} F n

/-- Canonical homology maps compose under successive functors and coefficient
morphisms. -/
@[stacks 08PH "homology_map"]
theorem categoryHomologyMap_comp {C : Type u} {C' : Type u'} {C'' : Type u''} [SmallCategory C]
    [SmallCategory C'] [SmallCategory C''] (f : C' ⥤ C) (g : C'' ⥤ C')
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}}
    {F'' : C''ᵒᵖ ⥤ AddCommGrpCat.{max u u' u'' v}} (t : F' ⟶ f.op ⋙ F) (s : F'' ⟶ g.op ⋙ F')
    (n : ℕ) :
    categoryHomologyMap.{u, u'', max u' v} (g ⋙ f) (s ≫ Functor.whiskerLeft g.op t) n =
      categoryHomologyMap.{u', u'', max u v} g s n ≫
        categoryHomologyMap.{u, u', max u'' v} f t n := by
  have := presheafEnoughProjectives.{u, max u' u'' v} C
  have := presheafEnoughProjectives.{u', max u u'' v} C'
  have := presheafEnoughProjectives.{u'', max u u' v} C''
  exact homologyMapAux_comp.{u, u', u'', v} f g t s n

end Card

end Stacks.CategoryHomology

end
