module

public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedSystem
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Cartesian objects of the derived category of a simplicial site (Stacks 07TF (3))

In the simplicial-site situation `CategoryTheory.SimplicialSiteSituation` of Stacks 09WE an
abelian sheaf on the total site restricts to each component site, and a simplex map
`φ : [m] ⟶ [n]` compares the two restrictions through a transition
`f_φ^{-1} F_m ⟶ F_n`. Both pass to unbounded derived categories: restriction is exact, so it
induces `derivedComponent`, and the transition induces `derivedTransition`. An object `K` of
`D(C_total)` is *cartesian* when every one of those derived transitions is invertible.

The derived transition is not chosen freely. It is pinned down by two specifications carried
in `TransitionWitness`: the abelian transition it comes from has the transition of Tag 09WF as
its underlying map of sheaves of sets, and the derived transition is obtained from the abelian
one by applying it to complexes and localizing.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.abelianComponent`: restriction of abelian sheaves
  from the total site to the component site in one simplicial degree, with
  `abelianComponent_exact` saying it is exact.
* `CategoryTheory.SimplicialSiteSituation.derivedComponent`: the induced functor on unbounded
  derived categories.
* `CategoryTheory.SimplicialSiteSituation.TransitionWitness`: an abelian transition and a
  derived transition together with the two specifications above, and
  `canonicalTransitionWitness` the canonical one.
* `CategoryTheory.SimplicialSiteSituation.derivedTransition`: the canonical derived
  transition.
* `CategoryTheory.SimplicialSiteSituation.IsCartesianDerived`: **Stacks 07TF (3)**.

## Implementation notes

`abelianComponent` is the direct image of abelian sheaves along the component inclusion, which
is restriction because the inclusion is continuous. That it agrees with restriction of the
underlying sheaves of sets together with the induced group operations is the Tag 00YT
comparison `Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso`, specialized here as
`abelianComponentExternalIso`; `abelianComponentInternalIso` is its internal form, obtained from
it and the Tag 04JC inverse `CategoryTheory.Sites.AbelianSheaf.externalInternalIso`.

The abelian transition is assembled in two steps, `abelianTransitionStepOne` and
`abelianTransitionStepTwo`, through the intermediate functor `abelianTransitionMid`.

The two `HasDerivedCategory` instances are hypotheses rather than a fixed choice of model, as
in Tag 0D9G.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites

universe u v

namespace CategoryTheory.Functor

/-- A functor applied to an identity, composed with a morphism and an identity, is that
morphism. -/
theorem map_id_comp_comp_id {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) {X : C} {Y : D} (h : F.obj X ⟶ Y) :
    F.map (𝟙 X) ≫ h ≫ 𝟙 Y = h := by
  rw [F.map_id, Category.id_comp, Category.comp_id]

end CategoryTheory.Functor

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

attribute [local instance] CategoryTheory.sheafTypeCartesian

local instance totalBraided :
    BraidedCategory (Sheaf S.totalTopology (Type u)) := .ofCartesianMonoidalCategory

attribute [local instance] CategoryTheory.componentCartesian CategoryTheory.componentBraided

/-- Restriction of total-site sheaves of sets to a component is a braided functor. -/
local instance restrictBraided (n : SimplexCategory) :
    (S.restrict.{u, u} n).Braided := .ofChosenFiniteProducts _

local instance transitionPreservesFiniteLimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteLimits (S.transitionMorphism φ).inverseImage :=
  (S.transitionMorphism φ).preservesFiniteLimits

local instance transitionBraided {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.Braided := .ofChosenFiniteProducts _

/-- Restriction of abelian sheaves from the total site to one simplicial degree. -/
def abelianComponent (n : SimplexCategory) :
    Sheaf S.totalTopology Ab.{u} ⥤ Sheaf (S.componentTopology n) Ab.{u} :=
  (S.inclusion n).sheafPushforwardContinuous Ab.{u} (S.componentTopology n) S.totalTopology

/-- Restriction to a degree is exact on abelian sheaves. -/
theorem abelianComponent_exact (n : SimplexCategory) :
    exactFunctor (Sheaf S.totalTopology Ab.{u})
      (Sheaf (S.componentTopology n) Ab.{u}) (abelianComponent S n) := by
  let : PreservesLimits (abelianComponent S n) :=
    Functor.preservesLimits_sheafPushforwardContinuous (S.inclusion n)
      Ab.{u} (S.componentTopology n) S.totalTopology
  let : PreservesColimits (abelianComponent S n) :=
    Functor.preservesColimits_sheafPushforwardContinuous (S.inclusion n)
      Ab.{u} (S.componentTopology n) S.totalTopology
  constructor
  · show PreservesFiniteLimits (abelianComponent S n)
    infer_instance
  · show PreservesFiniteColimits (abelianComponent S n)
    infer_instance

/-- Restriction of abelian sheaves preserves finite limits. -/
instance abelianComponent_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (abelianComponent S n) :=
  (abelianComponent_exact S n).1

/-- Restriction of abelian sheaves preserves finite colimits. -/
instance abelianComponent_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (abelianComponent S n) :=
  (abelianComponent_exact S n).2

/-- Restriction of abelian sheaves is additive. -/
instance abelianComponent_additive (n : SimplexCategory) :
    (abelianComponent S n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restricting an abelian sheaf is restricting its underlying sheaf of sets with the induced
group operations: the Tag 00YT comparison for the component inclusion. -/
def abelianComponentExternalIso (n : SimplexCategory) :
    AbelianSheaf.internalSheaf.{u, u, u} S.totalTopology ⋙
        (S.restrict.{u, u} n).mapCommGrp ⋙
        AbelianSheaf.externalSheaf.{u, u, u} (S.componentTopology n) ≅
      abelianComponent S n :=
  Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso
    (S.inclusion n) (S.componentTopology n) S.totalTopology

/-- The internal form of `abelianComponentExternalIso`: the internal group object of a restricted
abelian sheaf is the restriction of its internal group object. -/
def abelianComponentInternalIso (n : SimplexCategory) :
    abelianComponent S n ⋙ AbelianSheaf.internalSheaf.{u, u, u} (S.componentTopology n) ≅
      AbelianSheaf.internalSheaf.{u, u, u} S.totalTopology ⋙
        (S.restrict.{u, u} n).mapCommGrp :=
  Functor.isoWhiskerRight (abelianComponentExternalIso S n).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (AbelianSheaf.externalInternalIso _) ≪≫
      Functor.rightUnitor _)

/-- Restriction `restrictAb` to a degree is exact on abelian sheaves. -/
theorem restrictAb_exact (n : SimplexCategory) :
    exactFunctor (Sheaf S.totalTopology Ab.{u})
      (Sheaf (S.componentTopology n) Ab.{u}) (restrictAb S n) :=
  abelianComponent_exact S n

/-- Restriction of abelian sheaves preserves finite limits. -/
instance restrictAb_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (restrictAb S n) :=
  (restrictAb_exact S n).1

/-- Restriction of abelian sheaves preserves finite colimits. -/
instance restrictAb_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (restrictAb S n) :=
  (restrictAb_exact S n).2

/-- Restriction of abelian sheaves is additive. -/
instance restrictAb_additive (n : SimplexCategory) :
    (restrictAb S n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restricting an abelian sheaf is restricting its underlying sheaf of sets with the induced
group operations: the Tag 00YT comparison for the component inclusion. -/
def restrictAbExternalIso (n : SimplexCategory) :
    AbelianSheaf.internalSheaf.{u, u, u} S.totalTopology ⋙
        (S.restrict.{u, u} n).mapCommGrp ⋙
        AbelianSheaf.externalSheaf.{u, u, u} (S.componentTopology n) ≅
      restrictAb S n :=
  Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso
    (S.inclusion n) (S.componentTopology n) S.totalTopology

/-- The internal form of `restrictAbExternalIso`: the internal group object of a restricted
abelian sheaf is the restriction of its internal group object. -/
def restrictAbInternalIso (n : SimplexCategory) :
    restrictAb S n ⋙ AbelianSheaf.internalSheaf.{u, u, u} (S.componentTopology n) ≅
      AbelianSheaf.internalSheaf.{u, u, u} S.totalTopology ⋙
        (S.restrict.{u, u} n).mapCommGrp :=
  Functor.isoWhiskerRight (restrictAbExternalIso S n).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (AbelianSheaf.externalInternalIso _) ≪≫
      Functor.rightUnitor _)

/-- The transition of Tag 09WF read on internal group objects. -/
def fiberTransitionCommGrp {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.restrict.{u, u} m).mapCommGrp ⋙
        (S.transitionMorphism φ).inverseImage.mapCommGrp ⟶
      (S.restrict.{u, u} n).mapCommGrp :=
  (Functor.mapCommGrpCompIso
      (F := S.restrict.{u, u} m) (G := (S.transitionMorphism φ).inverseImage)).inv ≫
    Functor.mapCommGrpNatTrans (fiberTransition S φ)

/-- The intermediate term of the abelian transition: internalize on the total site, restrict in
degree `m`, transport along `f_φ`, and read the group operations back off. -/
abbrev abelianTransitionMid {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf S.totalTopology Ab.{u} ⥤ Sheaf (S.componentTopology n) Ab.{u} :=
  AbelianSheaf.internalSheaf.{u, u, u} S.totalTopology ⋙
    (S.restrict.{u, u} m).mapCommGrp ⋙
    (S.transitionMorphism φ).inverseImage.mapCommGrp ⋙
    AbelianSheaf.externalSheaf.{u, u, u} (S.componentTopology n)

/-- First step of the abelian transition: replace the restriction in degree `m` by its internal
form, under `f_φ` and back. -/
def abelianTransitionStepOne {m n : SimplexCategory} (φ : m ⟶ n) :
    abelianComponent S m ⋙ abelianTransition S φ ⟶ abelianTransitionMid S φ :=
  Functor.whiskerRight (Functor.whiskerRight (abelianComponentInternalIso S m).hom
      (S.transitionMorphism φ).inverseImage.mapCommGrp)
    (AbelianSheaf.externalSheaf.{u, u, u} (S.componentTopology n))

/-- First step of the abelian transition: replace the restriction in degree `m` by its internal
form, under `f_φ` and back. -/
def abelianTransitionStepOne' {m n : SimplexCategory} (φ : m ⟶ n) :
    restrictAb S m ⋙ abelianTransition S φ ⟶ abelianTransitionMid S φ :=
  Functor.whiskerRight (Functor.whiskerRight (restrictAbInternalIso S m).hom
      (S.transitionMorphism φ).inverseImage.mapCommGrp)
    (AbelianSheaf.externalSheaf.{u, u, u} (S.componentTopology n))

/-- Second step of the abelian transition: apply the internal form of the Tag 09WF transition. -/
def abelianTransitionStepTwo {m n : SimplexCategory} (φ : m ⟶ n) :
    abelianTransitionMid S φ ⟶
      AbelianSheaf.internalSheaf.{u, u, u} S.totalTopology ⋙
        (S.restrict.{u, u} n).mapCommGrp ⋙
        AbelianSheaf.externalSheaf.{u, u, u} (S.componentTopology n) :=
  Functor.whiskerRight (Functor.whiskerLeft
      (AbelianSheaf.internalSheaf.{u, u, u} S.totalTopology) (fiberTransitionCommGrp S φ))
    (AbelianSheaf.externalSheaf.{u, u, u} (S.componentTopology n))

/-- The transition of abelian sheaves induced by the total-site arrows: the transition of
Tag 09WF carried through the identification of abelian sheaves with internal group objects. -/
def abelianTransitionOfFiber {m n : SimplexCategory} (φ : m ⟶ n) :
    abelianComponent S m ⋙ abelianTransition S φ ⟶ abelianComponent S n :=
  abelianTransitionStepOne S φ ≫ abelianTransitionStepTwo S φ ≫
    (abelianComponentExternalIso S n).hom

/-- The transition of abelian sheaves induced by the total-site arrows: the transition of
Tag 09WF carried through the identification of abelian sheaves with internal group objects. -/
def abelianTransitionOfFiber' {m n : SimplexCategory} (φ : m ⟶ n) :
    restrictAb S m ⋙ abelianTransition S φ ⟶ restrictAb S n :=
  abelianTransitionStepOne' S φ ≫ abelianTransitionStepTwo S φ ≫
    (restrictAbExternalIso S n).hom

/-- On underlying sheaves of sets the abelian transition is the transition of Tag 09WF between
two identities. -/
theorem abelianTransitionOfFiber_forget_aux {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianTransitionOfFiber S φ).app A) =
      (S.transitionMorphism φ).inverseImage.map (𝟙 ((S.restrict.{u, u} m).obj
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj A))) ≫
        (fiberTransition S φ).app ((sheafCompose S.totalTopology (forget Ab.{u})).obj A) ≫
        𝟙 ((S.restrict.{u, u} n).obj
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)) :=
  rfl

/-- On underlying sheaves of sets the abelian transition `abelianTransitionOfFiber'` is the
transition of Tag 09WF between two identities. -/
theorem abelianTransitionOfFiber_forget_aux' {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianTransitionOfFiber' S φ).app A) =
      (S.transitionMorphism φ).inverseImage.map (𝟙 ((S.restrict.{u, u} m).obj
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj A))) ≫
        (fiberTransition S φ).app ((sheafCompose S.totalTopology (forget Ab.{u})).obj A) ≫
        𝟙 ((S.restrict.{u, u} n).obj
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)) :=
  rfl

/-- The abelian transition has the transition of Tag 09WF as its underlying map of sheaves of
sets. -/
theorem abelianTransitionOfFiber_forget {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianTransitionOfFiber S φ).app A) =
      (fiberTransition S φ).app
        ((sheafCompose S.totalTopology (forget Ab.{u})).obj A) :=
  (abelianTransitionOfFiber_forget_aux S φ A).trans
    (Functor.map_id_comp_comp_id (S.transitionMorphism φ).inverseImage _)

/-- The abelian transition has the transition of Tag 09WF as its underlying map of sheaves of
sets. -/
theorem abelianTransitionOfFiber_forget' {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianTransitionOfFiber' S φ).app A) =
      (fiberTransition S φ).app
        ((sheafCompose S.totalTopology (forget Ab.{u})).obj A) :=
  abelianTransitionOfFiber_forget S φ A

variable [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- A derived abelian sheaf restricted to one simplicial degree. -/
@[implicit_reducible] def derivedComponent (n : SimplexCategory) :
    DerivedCategory (Sheaf S.totalTopology Ab.{u}) ⥤
      DerivedCategory (Sheaf (S.componentTopology n) Ab.{u}) :=
  (abelianComponent S n).mapDerivedCategory

/-- Restricting in degree `m` and then transporting along `f_φ` is, on derived categories, the
derived functor of the composite. -/
def derivedComponentCompIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianComponent S m ⋙ abelianTransition S φ).mapDerivedCategory ≅
      derivedComponent S m ⋙ derivedInverseImage S φ :=
  derivedCompIso (abelianComponent S m) (abelianTransition S φ) _ (Iso.refl _)

attribute [local implicit_reducible] abelianComponent

/-- Restricting in degree `m` and then transporting along `f_φ` is, on derived categories, the
derived functor of the composite. -/
def derivedComponentCompIso' {m n : SimplexCategory} (φ : m ⟶ n) :
    (restrictAb S m ⋙ abelianTransition S φ).mapDerivedCategory ≅
      derivedComponent S m ⋙ derivedInverseImage S φ :=
  derivedCompIso (restrictAb S m) (abelianTransition S φ) _ (Iso.refl _)

/-- The derived transition obtained from a transition of abelian sheaves, by applying it to
complexes and lifting through the localization at quasi-isomorphisms. -/
def derivedTransitionOfAbelian {m n : SimplexCategory} (φ : m ⟶ n)
    (α : abelianComponent S m ⋙ abelianTransition S φ ⟶ abelianComponent S n) :
    derivedComponent S m ⋙ derivedInverseImage S φ ⟶ derivedComponent S n :=
  (derivedComponentCompIso S φ).inv ≫
    derivedNatTrans (abelianComponent S m ⋙ abelianTransition S φ) (abelianComponent S n) α

/-- The derived transition obtained from a transition of abelian sheaves, by applying it to
complexes and lifting through the localization at quasi-isomorphisms. -/
def derivedTransitionOfAbelian' {m n : SimplexCategory} (φ : m ⟶ n)
    (α : restrictAb S m ⋙ abelianTransition S φ ⟶ restrictAb S n) :
    derivedComponent S m ⋙ derivedInverseImage S φ ⟶ derivedComponent S n :=
  (derivedComponentCompIso' S φ).inv ≫
    derivedNatTrans (restrictAb S m ⋙ abelianTransition S φ) (restrictAb S n) α

/-- On the image of a complex, `derivedTransitionOfAbelian` is the given abelian transition
applied to that complex, read through the two canonical identifications. -/
theorem derivedTransitionOfAbelian_Q {m n : SimplexCategory} (φ : m ⟶ n)
    (α : abelianComponent S m ⋙ abelianTransition S φ ⟶ abelianComponent S n)
    (A : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    (derivedTransitionOfAbelian S φ α).app (DerivedCategory.Q.obj A) ≫
        ((abelianComponent S n).mapDerivedCategoryFactors.hom.app A) =
      (derivedComponentCompIso S φ).inv.app (DerivedCategory.Q.obj A) ≫
      ((abelianComponent S m ⋙
        abelianTransition S φ).mapDerivedCategoryFactors.hom.app A) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α
        (ComplexShape.up ℤ)).app A) := by
  rw [derivedTransitionOfAbelian, NatTrans.comp_app, Category.assoc,
    derivedNatTrans_app_Q]

/-- On the image of a complex, `derivedTransitionOfAbelian'` is the given abelian transition
applied to that complex, read through the two canonical identifications. -/
theorem derivedTransitionOfAbelian_Q' {m n : SimplexCategory} (φ : m ⟶ n)
    (α : restrictAb S m ⋙ abelianTransition S φ ⟶ restrictAb S n)
    (A : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    (derivedTransitionOfAbelian' S φ α).app (DerivedCategory.Q.obj A) ≫
        ((restrictAb S n).mapDerivedCategoryFactors.hom.app A) =
      (derivedComponentCompIso' S φ).inv.app (DerivedCategory.Q.obj A) ≫
      ((restrictAb S m ⋙
        abelianTransition S φ).mapDerivedCategoryFactors.hom.app A) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α
        (ComplexShape.up ℤ)).app A) := by
  exact derivedTransitionOfAbelian_Q S φ α A

/-- The canonical abelian and derived transitions, with the specifications that the former has
the total-site restriction transition of Tag 09WF as its underlying map of sheaves of sets and
that the latter is obtained from it by localization of complexes. -/
structure TransitionWitness {m n : SimplexCategory} (φ : m ⟶ n) where
  /-- The transition of abelian sheaves. -/
  abelian : abelianComponent S m ⋙ abelianTransition S φ ⟶ abelianComponent S n
  /-- Its underlying map of sheaves of sets is the transition of Tag 09WF. -/
  abelian_forget (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map (abelian.app A) =
      (fiberTransition S φ).app
        ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)
  /-- The transition of derived categories. -/
  derived : derivedComponent S m ⋙ derivedInverseImage S φ ⟶ derivedComponent S n
  /-- On the image of a complex it is the abelian transition applied to that complex. -/
  derived_Q (A : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    derived.app (DerivedCategory.Q.obj A) ≫
        ((abelianComponent S n).mapDerivedCategoryFactors.hom.app A) =
      (derivedComponentCompIso S φ).inv.app (DerivedCategory.Q.obj A) ≫
      ((abelianComponent S m ⋙
        abelianTransition S φ).mapDerivedCategoryFactors.hom.app A) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex abelian
        (ComplexShape.up ℤ)).app A)

/-- The transition induced by the total-site arrows, first on abelian sheaves and then on their
unbounded derived categories. -/
def canonicalTransitionWitness {m n : SimplexCategory} (φ : m ⟶ n) :
    TransitionWitness S φ :=
  Classical.choice ⟨{
    abelian := abelianTransitionOfFiber S φ
    abelian_forget := abelianTransitionOfFiber_forget S φ
    derived := derivedTransitionOfAbelian S φ (abelianTransitionOfFiber S φ)
    derived_Q := derivedTransitionOfAbelian_Q S φ (abelianTransitionOfFiber S φ) }⟩

/-- The canonical transition on derived restrictions. -/
def derivedTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    derivedComponent S m ⋙ derivedInverseImage S φ ⟶ derivedComponent S n :=
  (canonicalTransitionWitness S φ).derived

/-- **Stacks 07TF (3).** An object of the derived category of abelian sheaves on the total site
is cartesian when the canonical transition along every simplex map is an isomorphism. -/
@[stacks 07TF "cartesian_derived_sheaf"]
abbrev IsCartesianDerived (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) : Prop :=
  ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), IsIso ((derivedTransition S φ).app K)

/-- The abelian transition of a witness is invertible at an abelian sheaf exactly when the
transition of Tag 09WF is invertible at its underlying sheaf of sets. -/
theorem isIso_transitionWitness_abelian_app_iff {m n : SimplexCategory} {φ : m ⟶ n}
    (w : TransitionWitness S φ) (A : Sheaf S.totalTopology Ab.{u}) :
    IsIso (w.abelian.app A) ↔
      IsIso ((fiberTransition S φ).app
        ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)) := by
  refine (isIso_iff_of_reflects_iso (w.abelian.app A)
    (sheafCompose (S.componentTopology n) (forget Ab.{u}))).symm.trans ?_
  rw [w.abelian_forget A]
  rfl

/-- The derived transition of a witness is invertible at an object of the derived category exactly
when its abelian transition is invertible at every cohomology sheaf of that object. -/
theorem isIso_transitionWitness_derived_app_iff {m n : SimplexCategory} {φ : m ⟶ n}
    (w : TransitionWitness S φ) (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    IsIso (w.derived.app K) ↔
      ∀ q : ℤ, IsIso (w.abelian.app
        ((DerivedCategory.homologyFunctor (Sheaf S.totalTopology Ab.{u}) q).obj K)) := by
  have hδ : ∀ A : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ,
      ((derivedComponentCompIso S φ).hom ≫ w.derived).app (DerivedCategory.Q.obj A) ≫
          (abelianComponent S n).mapDerivedCategoryFactors.hom.app A =
        (abelianComponent S m ⋙ abelianTransition S φ).mapDerivedCategoryFactors.hom.app A ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex w.abelian
            (ComplexShape.up ℤ)).app A) := fun A => by
    rw [NatTrans.comp_app, Category.assoc, w.derived_Q A, ← Category.assoc, ← NatTrans.comp_app,
      (derivedComponentCompIso S φ).hom_inv_id, NatTrans.id_app, Category.id_comp]
  rw [← Functor.isIso_app_iff_forall_isIso_app_homology w.abelian _ hδ K, NatTrans.comp_app,
    isIso_comp_left_iff]

/-- **Stacks 0D7L (1).** An object of the derived category of abelian sheaves on the total site of
a simplicial site is cartesian if and only if all of its cohomology sheaves are cartesian abelian
sheaves. -/
@[stacks 0D7L "cartesian derived sheaves are those with cartesian cohomology"]
theorem isCartesianDerived_iff_forall_isCartesianAbSheaf_homology'
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    IsCartesianDerived S K ↔
      ∀ q : ℤ, IsCartesianAbSheaf S
        ((DerivedCategory.homologyFunctor (Sheaf S.totalTopology Ab.{u}) q).obj K) :=
  ⟨fun hK q _ _ φ ↦ (isIso_transitionWitness_abelian_app_iff S (canonicalTransitionWitness S φ) _).1
      ((isIso_transitionWitness_derived_app_iff S (canonicalTransitionWitness S φ) K).1 (hK φ) q),
    fun hH _ _ φ ↦ (isIso_transitionWitness_derived_app_iff S (canonicalTransitionWitness S φ) K).2
      fun q ↦ (isIso_transitionWitness_abelian_app_iff S (canonicalTransitionWitness S φ) _).2
        (hH q φ)⟩

end CategoryTheory.SimplicialSiteSituation

end
