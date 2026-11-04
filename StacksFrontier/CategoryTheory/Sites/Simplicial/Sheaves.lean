module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentRestriction
public import Mathlib.CategoryTheory.Bicategory.Modification.Lax
public import Mathlib.CategoryTheory.PUnit

/-!
# Sheaves on a simplicial site

For a simplicial site, sheaves on its total site are described by a sheaf in every simplicial
degree together with transition morphisms.  The identity and composition axioms for those
morphisms are most naturally packaged as a lax section of the pseudofunctor of inverse-image
functors.

## Main definitions

* `SimplicialSheafSystem` is the category of normalized systems attached to a pseudofunctor of
  component categories.
* `canonicalIdentityComparison`, `canonicalCompositionComparison`: the inverse-image unit and
  composition comparisons, mates of the site-induced direct-image comparisons of Situation 09WE.
* `componentCat`, `componentCatEquiv`, `componentCatMap`, `componentCatMapId`,
  `componentCatMapComp`: the component sheaf categories transported into the universe in which
  systems live, together with the transported inverse-image functors and their comparisons.
* `SimplicialSheafPresentation` records the coherent inverse-image functors on categories
  equivalent to the component sheaf categories and the equivalence with sheaves on the total site.

## Main results

* `SimplicialSheafPresentation.systemTransition_id`: in any presentation, the transition attached
  to an identity simplex map is the canonical identification of `f_𝟙⁻¹` with the identity.
* `SimplicialSheafPresentation.systemTransition_comp`: in any presentation, the transition
  attached to a composite simplex map is the composite of the two transitions, compared by
  `canonicalCompositionComparison`.

The equivalence of categories itself (Lemma 85.8.4) is not constructed in this module: a
presentation is assumed here, and `CategoryTheory.SimplicialSiteSituation.totalPresentation`
builds one.

## Implementation notes

A system is represented as a lax transformation from the constant terminal-category
pseudofunctor.  Its components are the sheaves `Fₙ`; its laxity cells are the maps
`f_φ⁻¹ Fₘ ⟶ Fₙ`.  The lax identity and composition laws are exactly the normalization at
identity maps and the compatibility with composition in the source.  The pseudofunctorial
comparison isomorphisms supply the canonical identifications used in those laws.

The component categories are represented in the universe in which the categories of sheaves live,
and are identified with them by equivalences. The identity and composition comparisons are
constructed from the site functors and the specified adjunctions, independently of the
presentation. The normalization and composition lemmas state that system maps use these
fixed comparisons. Component restriction is the existing precomposition functor
`CategoryTheory.SimplicialSiteSituation.restrict`. The component identification is natural in
the total-site sheaf.

The sheaf categories `Sheaf (S.componentTopology n) (Type u)` have objects one universe above
their morphisms, so they are not themselves objects of `Cat.{u + 1, u + 1}`; `componentCat`
lifts them with `AsSmall`, which is strict in the sense that `AsSmall.up ⋙ AsSmall.down` and
`AsSmall.down ⋙ AsSmall.up` are both the identity by definitional unfolding. The transported
comparisons are therefore the inverse-image comparisons whiskered on both sides.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Pseudofunctor
open scoped CategoryTheory.Bicategory CategoryTheory.Lax.LaxTrans

universe u

namespace CategoryTheory

namespace SimplicialSiteSituation

/-- The constant pseudofunctor with value the terminal category. -/
public abbrev terminalPseudofunctor :
    LocallyDiscrete SimplexCategory ⥤ᵖ Cat.{u + 1, u + 1} :=
  ((Functor.const SimplexCategory).obj (Cat.of (Discrete PUnit.{u + 2}))).toPseudofunctor'

/-- Systems of objects and transition maps for a pseudofunctor on the simplex category.

An object consists of an object `Fₙ` in every fibre and, for every `φ : [m] ⟶ [n]`, a map
`P(φ)(Fₘ) ⟶ Fₙ`.  The laws of a lax transformation impose compatibility with composition and
the normalized identity condition.  Morphisms are componentwise morphisms commuting with all
transition maps. -/
public abbrev SimplicialSheafSystem
    (P : LocallyDiscrete SimplexCategory ⥤ᵖ Cat.{u + 1, u + 1}) :=
  CategoryTheory.Lax.LaxTrans terminalPseudofunctor P.toLax

/-- The category structure on systems, whose morphisms are modifications of lax sections. -/
public instance (P : LocallyDiscrete SimplexCategory ⥤ᵖ Cat.{u + 1, u + 1}) :
    Category (SimplicialSheafSystem P) :=
  CategoryTheory.Lax.LaxTrans.homCategory

/-- The inverse-image unit comparison, the mate under the specified topos adjunction
of the site-induced direct-image unit comparison. -/
public noncomputable def canonicalIdentityComparison
    (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    (S.transitionMorphism (𝟙 n)).inverseImage ≅ 𝟭 _ :=
  Adjunction.leftAdjointUniq
    ((S.transitionMorphism (𝟙 n)).adj.ofNatIsoRight (S.pushforwardId n))
    Adjunction.id

/-- The inverse-image compositor, the mate under the specified topos adjunctions
of the site-induced direct-image compositor. -/
public noncomputable def canonicalCompositionComparison
    (S : SimplicialSiteSituation.{u})
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (S.transitionMorphism (ψ ≫ φ)).inverseImage ≅
      (S.transitionMorphism ψ).inverseImage ⋙ (S.transitionMorphism φ).inverseImage :=
  Adjunction.leftAdjointUniq (S.transitionMorphism (ψ ≫ φ)).adj
    (((S.transitionMorphism ψ).adj.comp (S.transitionMorphism φ).adj).ofNatIsoRight
      (S.pushforwardCompSymm ψ φ))

section Diagram

variable (S : SimplicialSiteSituation.{u})

/-- The category of sheaves in simplicial degree `n`, transported into the universe in which
systems of sheaves live. -/
public def componentCat (n : SimplexCategory) : Cat.{u + 1, u + 1} :=
  Cat.of (AsSmall.{u + 1} (Sheaf (S.componentTopology n) (Type u)))

/-- The transported component category is equivalent to the category of sheaves in degree `n`. -/
public def componentCatEquiv (n : SimplexCategory) :
    componentCat S n ≌ Sheaf (S.componentTopology n) (Type u) :=
  AsSmall.equiv.symm

/-- The inverse image of the morphism of topoi `f_φ`, transported to the component
categories. -/
public noncomputable def componentCatMap {m n : SimplexCategory} (φ : m ⟶ n) :
    componentCat S m ⟶ componentCat S n :=
  (AsSmall.down ⋙ (S.transitionMorphism φ).inverseImage ⋙ AsSmall.up).toCatHom

/-- The transported unit comparison. -/
public noncomputable def componentCatMapId (n : SimplexCategory) :
    componentCatMap S (𝟙 n) ≅ 𝟙 (componentCat S n) :=
  Cat.Hom.isoMk (Functor.isoWhiskerLeft AsSmall.down
    (Functor.isoWhiskerRight (canonicalIdentityComparison S n) AsSmall.up))

/-- The transported composition comparison. -/
public noncomputable def componentCatMapComp {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    componentCatMap S (ψ ≫ φ) ≅ componentCatMap S ψ ≫ componentCatMap S φ :=
  Cat.Hom.isoMk (Functor.isoWhiskerLeft AsSmall.down
    (Functor.isoWhiskerRight (canonicalCompositionComparison S ψ φ) AsSmall.up))

end Diagram


/-- A presentation of sheaves on the total site as systems on the component topoi.

The natural isomorphism in `transitionIso` identifies the transition functor of the coherent
diagram with the inverse image of the morphism of topoi `f_φ`. -/
public structure SimplicialSheafPresentation (S : SimplicialSiteSituation.{u}) where
  /-- The coherent diagram of component sheaf categories and inverse-image functors. -/
  diagram : LocallyDiscrete SimplexCategory ⥤ᵖ Cat.{u + 1, u + 1}
  /-- Identification of each fibre with the corresponding category of sheaves. -/
  componentEquivalence (n : SimplexCategory) :
    diagram.obj ⟨n⟩ ≌ Sheaf (S.componentTopology n) (Type u)
  /-- Identification of every transition with the inverse-image functor of the induced morphism
  of topoi. -/
  transitionIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (diagram.map ⟨φ⟩).toFunctor ⋙ (componentEquivalence n).functor ≅
      (componentEquivalence m).functor ⋙ (S.transitionMorphism φ).inverseImage
  /-- The pseudofunctor's unit agrees with the independently defined site-induced
  inverse-image comparison. -/
  identityComparison_isCanonical (n : SimplexCategory) (X : diagram.obj ⟨n⟩) :
    (transitionIso (𝟙 n)).hom.app X ≫
      (canonicalIdentityComparison S n).hom.app ((componentEquivalence n).functor.obj X) =
        (componentEquivalence n).functor.map
          ((diagram.mapId ⟨n⟩).hom.toNatTrans.app X)
  /-- The pseudofunctor's compositor agrees with the independently defined site-induced
  inverse-image comparison. -/
  compositionComparison_isCanonical {l m n : SimplexCategory}
      (ψ : l ⟶ m) (φ : m ⟶ n) (X : diagram.obj ⟨l⟩) :
    (componentEquivalence n).functor.map
        ((diagram.mapComp ⟨ψ⟩ ⟨φ⟩).hom.toNatTrans.app X) ≫
      (transitionIso φ).hom.app ((diagram.map ⟨ψ⟩).toFunctor.obj X) ≫
      (S.transitionMorphism φ).inverseImage.map ((transitionIso ψ).hom.app X) =
        (transitionIso (ψ ≫ φ)).hom.app X ≫
          (canonicalCompositionComparison S ψ φ).hom.app ((componentEquivalence l).functor.obj X)
  /-- The equivalence between sheaves on the total site and normalized systems. -/
  totalEquivalence :
    Sheaf S.totalTopology (Type u) ≌ SimplicialSheafSystem diagram

  /-- The equivalence has the actual fibrewise restriction as its `n`th component, rather
  than an arbitrary equivalence with a category of systems. -/
  componentRestrictionIso (F : Sheaf S.totalTopology (Type u)) (n : SimplexCategory) :
    (componentEquivalence n).functor.obj
        (((totalEquivalence.functor.obj F).app ⟨n⟩).toFunctor.obj ⟨PUnit.unit⟩) ≅
      (S.restrict n).obj F
  /-- The component identification is natural in the sheaf on the total site. -/
  componentRestriction_naturality {F G : Sheaf S.totalTopology (Type u)}
      (α : F ⟶ G) (n : SimplexCategory) :
    (componentEquivalence n).functor.map
        (((totalEquivalence.functor.map α).as.app ⟨n⟩).toNatTrans.app ⟨PUnit.unit⟩) ≫
        (componentRestrictionIso G n).hom =
      (componentRestrictionIso F n).hom ≫ (S.restrict n).map α

namespace SimplicialSheafPresentation

/-- The object in degree `n` underlying a system. -/
public def systemComponent {S : SimplicialSiteSituation.{u}}
    (P : SimplicialSheafPresentation S) (F : SimplicialSheafSystem P.diagram)
    (n : SimplexCategory) : Sheaf (S.componentTopology n) (Type u) :=
  (P.componentEquivalence n).functor.obj ((F.app ⟨n⟩).toFunctor.obj ⟨PUnit.unit⟩)

/-- The transition map `f_φ⁻¹ Fₘ ⟶ Fₙ` underlying a system. -/
public noncomputable def systemTransition {S : SimplicialSiteSituation.{u}}
    (P : SimplicialSheafPresentation S) (F : SimplicialSheafSystem P.diagram)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.obj (P.systemComponent F m) ⟶
      P.systemComponent F n :=
  (P.transitionIso φ).inv.app ((F.app ⟨m⟩).toFunctor.obj ⟨PUnit.unit⟩) ≫
    (P.componentEquivalence n).functor.map
      ((F.naturality ⟨φ⟩).toNatTrans.app ⟨PUnit.unit⟩)

/-- The lax unit law of a system, read off on the component in degree `n`. -/
@[stacks 09WF "identity transitions"]
public theorem systemTransition_id {S : SimplicialSiteSituation.{u}}
    (P : SimplicialSheafPresentation S) (F : SimplicialSheafSystem P.diagram)
    (n : SimplexCategory) :
    P.systemTransition F (𝟙 n) =
      (canonicalIdentityComparison S n).hom.app (P.systemComponent F n) := by
  have h := F.naturality_id (⟨n⟩ : LocallyDiscrete SimplexCategory)
  have h3 := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans h)
    (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2})
  have h4 : (P.diagram.mapId (⟨n⟩ : LocallyDiscrete SimplexCategory)).inv.toNatTrans.app
        ((F.app ⟨n⟩).toFunctor.obj ⟨PUnit.unit⟩) ≫
        (F.naturality (𝟙 (⟨n⟩ : LocallyDiscrete SimplexCategory))).toNatTrans.app ⟨PUnit.unit⟩ =
      (ρ_ (F.app (⟨n⟩ : LocallyDiscrete SimplexCategory))).hom.toNatTrans.app ⟨PUnit.unit⟩ ≫
        (λ_ (F.app (⟨n⟩ : LocallyDiscrete SimplexCategory))).inv.toNatTrans.app ⟨PUnit.unit⟩ ≫
        (F.app (⟨n⟩ : LocallyDiscrete SimplexCategory)).toFunctor.map
          ((terminalPseudofunctor.toLax.mapId
            (⟨n⟩ : LocallyDiscrete SimplexCategory)).toNatTrans.app ⟨PUnit.unit⟩) := h3
  have h5 : (P.diagram.mapId (⟨n⟩ : LocallyDiscrete SimplexCategory)).inv.toNatTrans.app
        ((F.app ⟨n⟩).toFunctor.obj ⟨PUnit.unit⟩) ≫
        (F.naturality (𝟙 (⟨n⟩ : LocallyDiscrete SimplexCategory))).toNatTrans.app ⟨PUnit.unit⟩ =
      𝟙 _ := by
    refine h4.trans ?_
    change 𝟙 _ ≫ 𝟙 _ ≫
      (F.app (⟨n⟩ : LocallyDiscrete SimplexCategory)).toFunctor.map (𝟙 _) = 𝟙 _
    rw [Category.id_comp, Category.id_comp]
    exact CategoryTheory.Functor.map_id _ _
  have key := (Iso.inv_comp_eq ((Cat.Hom.toNatIso
    (P.diagram.mapId (⟨n⟩ : LocallyDiscrete SimplexCategory))).app
    ((F.app ⟨n⟩).toFunctor.obj (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2})))).mp h5
  have key2 : (F.naturality (⟨𝟙 n⟩ : (⟨n⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toNatTrans.app
      ⟨PUnit.unit⟩ =
      (P.diagram.mapId (⟨n⟩ : LocallyDiscrete SimplexCategory)).hom.toNatTrans.app
        ((F.app ⟨n⟩).toFunctor.obj ⟨PUnit.unit⟩) := key.trans (Category.comp_id _)
  simp only [systemTransition, systemComponent, key2]
  rw [← P.identityComparison_isCanonical n, ← Category.assoc, Iso.inv_hom_id_app]
  simp

/-- The lax composition law of a system, read off on the component in degree `l`: the
transition attached to a composite simplex map is the composite of the two transitions,
compared by the canonical inverse-image compositor. -/
@[stacks 09WF "composition of transitions"]
public theorem systemTransition_comp {S : SimplicialSiteSituation.{u}}
    (P : SimplicialSheafPresentation S) (F : SimplicialSheafSystem P.diagram)
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    P.systemTransition F (ψ ≫ φ) =
      (canonicalCompositionComparison S ψ φ).hom.app (P.systemComponent F l) ≫
        (S.transitionMorphism φ).inverseImage.map (P.systemTransition F ψ) ≫
          P.systemTransition F φ := by
  have collapse : ∀ {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : Sheaf (S.componentTopology n) (Type u)}
      (a : O₁ ⟶ O₂) (a' : O₂ ⟶ O₁) (k : O₂ ⟶ O₃) (p : O₃ ⟶ O₄) (r : O₄ ⟶ O₅)
      (r' : O₅ ⟶ O₄) (s : O₁ ⟶ O₅) (v : O₅ ⟶ O₇) (w : O₃ ⟶ O₆) (x : O₆ ⟶ O₇)
      (x' : O₇ ⟶ O₆) (y : O₄ ⟶ O₇) (z : O₆ ⟶ O₈) (t : O₂ ⟶ O₈),
      a ≫ a' = 𝟙 O₁ → r ≫ r' = 𝟙 O₄ → x ≫ x' = 𝟙 O₆ → v = r' ≫ y →
      k ≫ p ≫ r = a' ≫ s → w ≫ x = p ≫ y → t = k ≫ w ≫ z →
      a ≫ t = s ≫ v ≫ x' ≫ z := by
    intro _ _ _ _ _ _ _ _ a a' k p r r' s v w x x' y z t ha hr hx hv hc hn ht
    have hs : s = a ≫ k ≫ p ≫ r := by
      rw [hc, ← Category.assoc, ha, Category.id_comp]
    subst ht
    subst hv
    subst hs
    simp only [Category.assoc]
    rw [← Category.assoc r r', hr, Category.id_comp, ← Category.assoc p y, ← hn,
      Category.assoc, ← Category.assoc x x', hx, Category.id_comp]
  have h := F.naturality_comp (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)
    (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)
  have h3 := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans h)
    (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2})
  simp only [Bicategory.Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_refl,
    Category.id_comp] at h3
  have hkey : (P.diagram.mapComp (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)
          (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).inv.toNatTrans.app
        ((F.app ⟨l⟩).toFunctor.obj ⟨PUnit.unit⟩) ≫
      (F.naturality ((⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩) ≫
        ⟨φ⟩)).toNatTrans.app ⟨PUnit.unit⟩ =
      (P.diagram.map (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toFunctor.map
          ((F.naturality (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)).toNatTrans.app
            ⟨PUnit.unit⟩) ≫
        (F.naturality (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toNatTrans.app
          ⟨PUnit.unit⟩ := by
    refine h3.trans ?_
    have hid : (Bicategory.whiskerRight
          (𝟙 (𝟙 (Cat.of (Discrete PUnit.{u + 2})) ≫ 𝟙 (Cat.of (Discrete PUnit.{u + 2}))))
          (F.app (⟨n⟩ : LocallyDiscrete SimplexCategory))).toNatTrans.app
          (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2}) =
        𝟙 ((F.app (⟨n⟩ : LocallyDiscrete SimplexCategory)).toFunctor.obj ⟨PUnit.unit⟩) :=
      CategoryTheory.Functor.map_id _ _
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (fun c =>
        ((P.diagram.map (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toFunctor.map
            ((F.naturality (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)).toNatTrans.app
              ⟨PUnit.unit⟩) ≫
          (F.naturality (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toNatTrans.app
            ⟨PUnit.unit⟩) ≫ c) hid).trans (Category.comp_id _)
  have hcomp : (F.naturality
          (⟨ψ ≫ φ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toNatTrans.app
        ⟨PUnit.unit⟩ =
      (P.diagram.mapComp (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)
            (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).hom.toNatTrans.app
          ((F.app ⟨l⟩).toFunctor.obj ⟨PUnit.unit⟩) ≫
        (P.diagram.map (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toFunctor.map
            ((F.naturality (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)).toNatTrans.app
              ⟨PUnit.unit⟩) ≫
          (F.naturality (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toNatTrans.app
            ⟨PUnit.unit⟩ :=
    (Iso.inv_comp_eq ((Cat.Hom.toNatIso (P.diagram.mapComp
      (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)
      (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩))).app
        ((F.app ⟨l⟩).toFunctor.obj (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2})))).mp hkey
  have ht : (P.componentEquivalence n).functor.map
        ((F.naturality
          (⟨ψ ≫ φ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toNatTrans.app
            ⟨PUnit.unit⟩) =
      (P.componentEquivalence n).functor.map
          ((P.diagram.mapComp (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)
              (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).hom.toNatTrans.app
            ((F.app ⟨l⟩).toFunctor.obj ⟨PUnit.unit⟩)) ≫
        (P.componentEquivalence n).functor.map
            ((P.diagram.map (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toFunctor.map
              ((F.naturality (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)).toNatTrans.app
                ⟨PUnit.unit⟩)) ≫
          (P.componentEquivalence n).functor.map
            ((F.naturality (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toNatTrans.app
              ⟨PUnit.unit⟩) :=
    (congrArg (fun c => (P.componentEquivalence n).functor.map c) hcomp).trans
      (((P.componentEquivalence n).functor.map_comp _ _).trans
        (congrArg (fun c => (P.componentEquivalence n).functor.map
              ((P.diagram.mapComp (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)
                  (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).hom.toNatTrans.app
                ((F.app ⟨l⟩).toFunctor.obj ⟨PUnit.unit⟩)) ≫ c)
          ((P.componentEquivalence n).functor.map_comp _ _)))
  have hcan := P.compositionComparison_isCanonical ψ φ
    ((F.app ⟨l⟩).toFunctor.obj (⟨PUnit.unit⟩ : Discrete PUnit.{u + 2}))
  have hnat : (P.componentEquivalence n).functor.map
        ((P.diagram.map (⟨φ⟩ : (⟨m⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨n⟩)).toFunctor.map
          ((F.naturality (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)).toNatTrans.app
            ⟨PUnit.unit⟩)) ≫
      (P.transitionIso φ).hom.app ((F.app ⟨m⟩).toFunctor.obj ⟨PUnit.unit⟩) =
      (P.transitionIso φ).hom.app
          ((P.diagram.map (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)).toFunctor.obj
            ((F.app ⟨l⟩).toFunctor.obj ⟨PUnit.unit⟩)) ≫
        (S.transitionMorphism φ).inverseImage.map
          ((P.componentEquivalence m).functor.map
            ((F.naturality (⟨ψ⟩ : (⟨l⟩ : LocallyDiscrete SimplexCategory) ⟶ ⟨m⟩)).toNatTrans.app
              ⟨PUnit.unit⟩)) :=
    (P.transitionIso φ).hom.naturality _
  exact collapse _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Iso.inv_hom_id_app (P.transitionIso (ψ ≫ φ)) _)
    (((S.transitionMorphism φ).inverseImage.map_comp _ _).symm.trans
      ((congrArg (fun c => (S.transitionMorphism φ).inverseImage.map c)
          (Iso.hom_inv_id_app (P.transitionIso ψ) _)).trans
        (CategoryTheory.Functor.map_id _ _)))
    (Iso.hom_inv_id_app (P.transitionIso φ) _)
    (CategoryTheory.Functor.map_comp _ _ _) hcan hnat ht

/-- The sheaf in degree `n` associated to a sheaf on the total site. -/
public def component {S : SimplicialSiteSituation.{u}}
    (P : SimplicialSheafPresentation S)
    (F : Sheaf S.totalTopology (Type u)) (n : SimplexCategory) :
    Sheaf (S.componentTopology n) (Type u) :=
  P.systemComponent (P.totalEquivalence.functor.obj F) n

/-- The transition map between the components of a sheaf on the total site. -/
public noncomputable def transition {S : SimplicialSiteSituation.{u}}
    (P : SimplicialSheafPresentation S)
    (F : Sheaf S.totalTopology (Type u)) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.obj (P.component F m) ⟶ P.component F n :=
  P.systemTransition (P.totalEquivalence.functor.obj F) φ

end SimplicialSheafPresentation

end SimplicialSiteSituation

end CategoryTheory
