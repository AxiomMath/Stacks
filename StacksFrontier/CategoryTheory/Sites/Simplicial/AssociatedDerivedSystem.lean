module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransitionCoherence

/-!
# The simplicial system of the derived category of a sheaf on a total site (Stacks 0D9H)

In the simplicial-site situation `CategoryTheory.SimplicialSiteSituation` of Stacks 09WE an
object `K` of the derived category of abelian sheaves on the total site restricts to each
component site as `(S.derivedComponent n).obj K`, and a simplex map `φ : [m] ⟶ [n]` carries the
canonical derived transition `(S.derivedTransition φ).app K`. Stacks 0D9H says those data form a
simplicial system of the derived category in the sense of Stacks 0D9G, and that the system of a
cartesian object is cartesian. This file proves the two coherence laws and assembles the
system.

The canonical transitions of Stacks 07TF (3) are deliberately opaque --
`canonicalTransitionWitness` is a `Classical.choice` of a structure carrying an abelian transition,
a derived transition and their two specifications. `canonicalTransitionWitness_abelian` and
`derivedTransition_eq` puncture that opacity using nothing but the specifications, after which
every statement here is about the transparent `abelianTransitionOfFiber` and
`derivedTransitionOfAbelian`.

Both laws then reduce one level at a time. At the abelian level the compositor and unit laws for
the transition follow from the corresponding laws for the transition of sheaves of *sets* -- Stacks
09WF's `fiberTransition_comp` and `fiberTransition_id` -- because `sheafCompose _ (forget Ab)` is
faithful and the forgetful images of Tag 0D9G's compositor and unit are definitional. At the
derived level the abelian law is carried through the localization at quasi-isomorphisms. So no new
mathematics about derived categories appears here: the content is 09WF's, carried up two levels.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.associatedDerivedSystemData`: **Stacks 0D9H**, the
  simplicial system of derived restrictions, together with the equations fixing its objects and
  its transitions, and `associatedDerivedSystem` the system itself.

## Main results

* `CategoryTheory.SimplicialSiteSituation.associatedDerivedSystem_cartesian`: **Stacks 0D9H**,
  the system of a cartesian object is cartesian.
* `CategoryTheory.SimplicialSiteSituation.abelianTransitionOfFiber_comp_app` and
  `abelianTransitionOfFiber_id_app`: the compositor and unit laws for the abelian transition.
* `CategoryTheory.SimplicialSiteSituation.derivedTransition_eq`: the canonical derived transition
  is the localization of the canonical abelian one, with
  `canonicalTransitionWitness_abelian` the abelian half of the same identification.
* `CategoryTheory.SimplicialSiteSituation.derivedTransition_app_Q_comp`: the canonical derived
  transition on the image of a complex.
* `CategoryTheory.SimplicialSiteSituation.derivedTransition_comp`, `derivedTransition_comp_app`,
  `derivedTransition_id` and `derivedTransition_id_app`: the compositor and unit laws for the
  canonical derived transition; the first is the `map_comp` field of the system.

## Implementation notes

The forgetful images of Tag 0D9G's compositor and unit are definitional. `abelianIdIso_forget` is
`rfl`; `abelianCompIso_forget` is `rfl` up to the inverse image of one identity
(`abelianCompIso_forget_aux`), cancelled by the general `CategoryTheory.Functor.comp_map_id`.

Two spellings of one functor make the derived laws delicate, and the shape of this file is chosen
around that. `S.derivedComponent n ⋙ derivedInverseImage S φ` and
`(abelianComponent S n).mapDerivedCategory ⋙ (abelianTransition S φ).mapDerivedCategory` are
definitionally equal and are not type-correct at `implicit` transparency simultaneously, so a goal
mentioning both defeats `rw` -- which reports a pattern it prints as present -- and `simp`, which
reports "made no progress" or reports its lemmas unused. Every step that has to reassociate or
rewrite across that boundary is therefore done in a lemma whose objects are free variables
(`derivedInverseImageCompIso_hom_naturality_assoc` here, `derivedCompIso_refl_inv_app_Q_comp`,
`derivedCompIso_hom_app_Q_trans` and `derivedCompIso_hom_app_map_trans` in `DerivedSystem.lean`)
and the result is applied, never unfolded. `derivedInverseImage` carries a section-scoped
`local implicit_reducible` for the same reason, matching the `@[implicit_reducible]` its sibling
`derivedComponent` already has; unfolding it with `simp only` instead costs more than the default
heartbeat budget, because `derivedCompIso` takes nine instance arguments that must then be
synthesized again for `abelianTransition`.

The compositor law is for the same reason not proved here at all. `derivedTransition_comp` is a
single application of `CategoryTheory.derivedTransition_comp_of_app_Q`, which states and proves
it about abstract functors `L M N F G H`; the chain of rewrites run directly on the simplicial
instantiation exceeds the heartbeat budget at `whnf`, because each step re-synthesizes
`derivedCompIso`'s nine instance arguments, and raising the limit does not reach the end of it.
The abstract statement is where no such re-synthesis happens, so a declaration boundary in
generality -- not in file structure -- is what pays for this law.

`Functor.map_id` must be written fully qualified: inside `namespace CategoryTheory.*` the
unqualified name can resolve to the monad law, and it is a structure FIELD, so nothing unfolds it.

## References

* [Stacks Project, Tag 0D9H](https://stacks.math.columbia.edu/tag/0D9H)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites

namespace CategoryTheory.SimplicialSiteSituation


universe u v

variable (S : SimplicialSiteSituation.{u})

/-- The image under the forgetful functor of the compositor `abelianCompIso` at the restriction
of an abelian sheaf is the canonical composition comparison for sheaves of sets, followed by the
inverse image of an identity. -/
theorem abelianCompIso_forget_aux {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianCompIso S ψ φ).hom.app ((abelianComponent S l).obj A)) =
      (canonicalCompositionComparison S ψ φ).hom.app
        ((S.restrict.{u, u} l).obj
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)) ≫
      (S.transitionMorphism φ).inverseImage.map (𝟙 _) :=
  rfl

/-- The image under the forgetful functor of the compositor `abelianCompIso` at `restrictAb`
of an abelian sheaf is the canonical composition comparison for sheaves of sets, followed by the
inverse image of an identity. -/
theorem abelianCompIso_forget_aux' {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianCompIso S ψ φ).hom.app ((restrictAb S l).obj A)) =
      (canonicalCompositionComparison S ψ φ).hom.app
        ((S.restrict.{u, u} l).obj
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)) ≫
      (S.transitionMorphism φ).inverseImage.map (𝟙 _) := abelianCompIso_forget_aux S ψ φ A

/-- The image under the forgetful functor of the compositor `abelianCompIso` at the restriction
of an abelian sheaf is the canonical composition comparison for sheaves of sets. -/
theorem abelianCompIso_forget {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianCompIso S ψ φ).hom.app ((abelianComponent S l).obj A)) =
      (canonicalCompositionComparison S ψ φ).hom.app
        ((S.restrict.{u, u} l).obj
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)) :=
  (abelianCompIso_forget_aux S ψ φ A).trans
    (Functor.comp_map_id (S.transitionMorphism φ).inverseImage _)

/-- The image under the forgetful functor of the compositor `abelianCompIso` at `restrictAb`
of an abelian sheaf is the canonical composition comparison for sheaves of sets. -/
theorem abelianCompIso_forget' {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianCompIso S ψ φ).hom.app ((restrictAb S l).obj A)) =
      (canonicalCompositionComparison S ψ φ).hom.app
        ((S.restrict.{u, u} l).obj
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)) := abelianCompIso_forget S ψ φ A

/-- The image under the forgetful functor of the unit `abelianIdIso` at the restriction of an
abelian sheaf is the canonical identity comparison for sheaves of sets. -/
theorem abelianIdIso_forget (n : SimplexCategory) (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianIdIso S n).hom.app ((abelianComponent S n).obj A)) =
      (canonicalIdentityComparison S n).hom.app
        ((S.restrict.{u, u} n).obj
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)) :=
  rfl

/-- The image under the forgetful functor of the unit `abelianIdIso` at `restrictAb` of an
abelian sheaf is the canonical identity comparison for sheaves of sets. -/
theorem abelianIdIso_forget' (n : SimplexCategory) (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianIdIso S n).hom.app ((restrictAb S n).obj A)) =
      (canonicalIdentityComparison S n).hom.app
        ((S.restrict.{u, u} n).obj
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)) :=
  rfl

/-- The forgetful functor carries the abelian transition of a morphism of abelian sheaves to the
inverse image, along the transition morphism, of the underlying morphism of sheaves of sets. -/
theorem abelianTransition_map_forget {m n : SimplexCategory} (φ : m ⟶ n)
    {A B : Sheaf (S.componentTopology m) Ab.{u}} (f : A ⟶ B) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianTransition S φ).map f) =
      (S.transitionMorphism φ).inverseImage.map
        ((sheafCompose (S.componentTopology m) (forget Ab.{u})).map f) :=
  rfl

/-- The compositor law for the abelian transition: along `ψ ≫ φ` it is the compositor
`abelianCompIso` followed by the transitions along `ψ` and `φ`. -/
theorem abelianTransitionOfFiber_comp_app {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (abelianCompIso S ψ φ).hom.app ((abelianComponent S l).obj A) ≫
      (abelianTransition S φ).map ((abelianTransitionOfFiber S ψ).app A) ≫
      (abelianTransitionOfFiber S φ).app A =
      (abelianTransitionOfFiber S (ψ ≫ φ)).app A := by
  apply (sheafCompose (S.componentTopology n) (forget Ab.{u})).map_injective
  simp only [Functor.map_comp]
  rw [abelianCompIso_forget, abelianTransition_map_forget,
    abelianTransitionOfFiber_forget, abelianTransitionOfFiber_forget,
    abelianTransitionOfFiber_forget]
  exact (fiberTransition_comp S ψ φ
    ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)).symm

/-- The compositor law for the abelian transition `abelianTransitionOfFiber'`: along `ψ ≫ φ` it
is the compositor `abelianCompIso` followed by the transitions along `ψ` and `φ`. -/
theorem abelianTransitionOfFiber_comp_app' {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (abelianCompIso S ψ φ).hom.app ((restrictAb S l).obj A) ≫
      (abelianTransition S φ).map ((abelianTransitionOfFiber' S ψ).app A) ≫
      (abelianTransitionOfFiber' S φ).app A =
      (abelianTransitionOfFiber' S (ψ ≫ φ)).app A := abelianTransitionOfFiber_comp_app S ψ φ A

/-- The unit law for the abelian transition: along an identity simplex map it is the unit
`abelianIdIso`. -/
theorem abelianTransitionOfFiber_id_app (n : SimplexCategory)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (abelianTransitionOfFiber S (𝟙 n)).app A =
      (abelianIdIso S n).hom.app ((abelianComponent S n).obj A) := by
  apply (sheafCompose (S.componentTopology n) (forget Ab.{u})).map_injective
  rw [abelianIdIso_forget, abelianTransitionOfFiber_forget]
  exact fiberTransition_id S n ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)

/-- The unit law for the abelian transition `abelianTransitionOfFiber'`: along an identity
simplex map it is the unit `abelianIdIso`. -/
theorem abelianTransitionOfFiber_id_app' (n : SimplexCategory)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (abelianTransitionOfFiber' S (𝟙 n)).app A =
      (abelianIdIso S n).hom.app ((restrictAb S n).obj A) := abelianTransitionOfFiber_id_app S n A

section Derived

attribute [local implicit_reducible] CategoryTheory.derivedInverseImage

variable [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]


/-- The abelian transition of the canonical transition witness is `abelianTransitionOfFiber`. -/
theorem canonicalTransitionWitness_abelian {m n : SimplexCategory} (φ : m ⟶ n) :
    (canonicalTransitionWitness S φ).abelian = abelianTransitionOfFiber S φ := by
  refine NatTrans.ext (funext fun A => ?_)
  apply (sheafCompose (S.componentTopology n) (forget Ab.{u})).map_injective
  rw [(canonicalTransitionWitness S φ).abelian_forget, abelianTransitionOfFiber_forget]

/-- The abelian transition of the canonical transition witness is
`abelianTransitionOfFiber'`. -/
theorem canonicalTransitionWitness_abelian' {m n : SimplexCategory} (φ : m ⟶ n) :
    (canonicalTransitionWitness S φ).abelian = abelianTransitionOfFiber' S φ :=
  canonicalTransitionWitness_abelian S φ

/-- The canonical derived transition is the derived transition induced by the abelian transition
`abelianTransitionOfFiber`. -/
theorem derivedTransition_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    derivedTransition S φ =
      derivedTransitionOfAbelian S φ (abelianTransitionOfFiber S φ) := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf S.totalTopology Ab.{u}) (ComplexShape.up ℤ))
    (fun X => ?_)
  refine (cancel_mono ((abelianComponent S n).mapDerivedCategoryFactors.hom.app X)).1 ?_
  rw [derivedTransitionOfAbelian_Q, derivedTransition,
    (canonicalTransitionWitness S φ).derived_Q, canonicalTransitionWitness_abelian]

/-- The canonical derived transition is the derived transition induced by the abelian transition
`abelianTransitionOfFiber'`. -/
theorem derivedTransition_eq' {m n : SimplexCategory} (φ : m ⟶ n) :
    derivedTransition S φ =
      derivedTransitionOfAbelian' S φ (abelianTransitionOfFiber' S φ) :=
  derivedTransition_eq S φ

/-- The inverse of the compositor `derivedComponentCompIso` on the image of a complex, composed
with the localization comparison, is the derived inverse image of the comparison for the
restriction followed by the comparison for the transition. -/
theorem derivedComponentCompIso_inv_app_Q_comp {m n : SimplexCategory} (φ : m ⟶ n)
    (X : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)
    {Z : DerivedCategory (Sheaf (S.componentTopology n) Ab.{u})}
    (h : DerivedCategory.Q.obj
      (((abelianComponent S m ⋙ abelianTransition S φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X) ⟶ Z) :
    (derivedComponentCompIso S φ).inv.app (DerivedCategory.Q.obj X) ≫
        (abelianComponent S m ⋙ abelianTransition S φ).mapDerivedCategoryFactors.hom.app X ≫
          h =
      (derivedInverseImage S φ).map
          ((abelianComponent S m).mapDerivedCategoryFactors.hom.app X) ≫
        (abelianTransition S φ).mapDerivedCategoryFactors.hom.app
          (((abelianComponent S m).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫ h :=
  derivedCompIso_refl_inv_app_Q_comp _ _ X h

/-- The inverse of the compositor `derivedComponentCompIso'` on the image of a complex, composed
with the localization comparison, is the derived inverse image of the comparison for
`restrictAb` followed by the comparison for the transition. -/
theorem derivedComponentCompIso_inv_app_Q_comp' {m n : SimplexCategory} (φ : m ⟶ n)
    (X : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)
    {Z : DerivedCategory (Sheaf (S.componentTopology n) Ab.{u})}
    (h : DerivedCategory.Q.obj
      (((restrictAb S m ⋙ abelianTransition S φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X) ⟶ Z) :
    (derivedComponentCompIso' S φ).inv.app (DerivedCategory.Q.obj X) ≫
        (restrictAb S m ⋙ abelianTransition S φ).mapDerivedCategoryFactors.hom.app X ≫
          h =
      (derivedInverseImage S φ).map
          ((restrictAb S m).mapDerivedCategoryFactors.hom.app X) ≫
        (abelianTransition S φ).mapDerivedCategoryFactors.hom.app
          (((restrictAb S m).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫ h :=
  derivedComponentCompIso_inv_app_Q_comp S φ X h

/-- The canonical derived transition on the image of a complex, read through the identification
of the derived restriction with the localized one. -/
theorem derivedTransition_app_Q_comp {m n : SimplexCategory} (φ : m ⟶ n)
    (X : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    (derivedTransition S φ).app (DerivedCategory.Q.obj X) ≫
        (abelianComponent S n).mapDerivedCategoryFactors.hom.app X =
      (derivedInverseImage S φ).map
          ((abelianComponent S m).mapDerivedCategoryFactors.hom.app X) ≫
        (abelianTransition S φ).mapDerivedCategoryFactors.hom.app
          (((abelianComponent S m).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (abelianTransitionOfFiber S φ) (ComplexShape.up ℤ)).app X) := by
  rw [derivedTransition_eq, derivedTransitionOfAbelian_Q,
    derivedComponentCompIso_inv_app_Q_comp]

/-- The canonical derived transition on the image of a complex, read through the identification
of the derived restriction with the localized one. -/
theorem derivedTransition_app_Q_comp' {m n : SimplexCategory} (φ : m ⟶ n)
    (X : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    (derivedTransition S φ).app (DerivedCategory.Q.obj X) ≫
        (restrictAb S n).mapDerivedCategoryFactors.hom.app X =
      (derivedInverseImage S φ).map
          ((restrictAb S m).mapDerivedCategoryFactors.hom.app X) ≫
        (abelianTransition S φ).mapDerivedCategoryFactors.hom.app
          (((restrictAb S m).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (abelianTransitionOfFiber' S φ) (ComplexShape.up ℤ)).app X) :=
  derivedTransition_app_Q_comp S φ X

omit [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})] in
/-- The unit comparison of derived inverse images, on the image of a complex. -/
theorem derivedInverseImageIdIso_hom_app_Q (n : SimplexCategory)
    (Y : CochainComplex (Sheaf (S.componentTopology n) Ab.{u}) ℤ) :
    (derivedInverseImageIdIso S n).hom.app (DerivedCategory.Q.obj Y) =
      (abelianTransition S (𝟙 n)).mapDerivedCategoryFactors.hom.app Y ≫
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (abelianIdIso S n) (ComplexShape.up ℤ)).hom.app Y) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexIdIso
              (Sheaf (S.componentTopology n) Ab.{u}) (ComplexShape.up ℤ)).hom.app Y) := by
  have expand :
      (derivedInverseImageIdIso S n).hom.app (DerivedCategory.Q.obj Y) =
        (derivedNatIso (abelianTransition S (𝟙 n))
            (𝟭 (Sheaf (S.componentTopology n) Ab.{u})) (abelianIdIso S n)).hom.app
              (DerivedCategory.Q.obj Y) ≫
          (derivedIdIso (A := Sheaf (S.componentTopology n) Ab.{u})).hom.app
            (DerivedCategory.Q.obj Y) :=
    rfl
  rw [expand, derivedNatIso_hom_app_Q, derivedIdIso_hom_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The unit law for the canonical derived transition: along an identity simplex map it is the
unit comparison of derived inverse images, whiskered by the derived restriction. -/
theorem derivedTransition_id (n : SimplexCategory) :
    derivedTransition S (𝟙 n) =
      Functor.whiskerLeft (derivedComponent S n) (derivedInverseImageIdIso S n).hom ≫
        (Functor.rightUnitor (derivedComponent S n)).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf S.totalTopology Ab.{u}) (ComplexShape.up ℤ))
    (fun X => ?_)
  have collapse :
      (Functor.whiskerLeft (derivedComponent S n) (derivedInverseImageIdIso S n).hom ≫
          (Functor.rightUnitor (derivedComponent S n)).hom).app
            (DerivedCategory.Q.obj X) =
        (derivedInverseImageIdIso S n).hom.app
          ((derivedComponent S n).obj (DerivedCategory.Q.obj X)) :=
    Category.comp_id _
  have naturality :
      (derivedInverseImageIdIso S n).hom.app
            ((derivedComponent S n).obj (DerivedCategory.Q.obj X)) ≫
          (abelianComponent S n).mapDerivedCategoryFactors.hom.app X =
        (derivedInverseImage S (𝟙 n)).map
            ((abelianComponent S n).mapDerivedCategoryFactors.hom.app X) ≫
          (derivedInverseImageIdIso S n).hom.app
            (DerivedCategory.Q.obj
              (((abelianComponent S n).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) :=
    ((derivedInverseImageIdIso S n).hom.naturality _).symm
  refine (cancel_mono ((abelianComponent S n).mapDerivedCategoryFactors.hom.app X)).1 ?_
  rw [derivedTransition_app_Q_comp, collapse, naturality]
  refine congrArg (fun g => (derivedInverseImage S (𝟙 n)).map
    ((abelianComponent S n).mapDerivedCategoryFactors.hom.app X) ≫ g) ?_
  rw [derivedInverseImageIdIso_hom_app_Q]
  refine congrArg (fun g => (abelianTransition S (𝟙 n)).mapDerivedCategoryFactors.hom.app
    (((abelianComponent S n).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫ g) ?_
  rw [← Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  apply HomologicalComplex.hom_ext
  intro degree
  exact abelianTransitionOfFiber_id_app S n (X.X degree)


omit [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})] in
/-- Naturality of the derived inverse-image compositor, composed with a further morphism `h`. -/
theorem derivedInverseImageCompIso_hom_naturality_assoc {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    {K K' : DerivedCategory (Sheaf (S.componentTopology l) Ab.{u})} (g : K ⟶ K')
    {W : DerivedCategory (Sheaf (S.componentTopology n) Ab.{u})}
    (h : (derivedInverseImage S φ).obj ((derivedInverseImage S ψ).obj K') ⟶ W) :
    (derivedInverseImageCompIso S ψ φ).hom.app K ≫
        (derivedInverseImage S φ).map ((derivedInverseImage S ψ).map g) ≫ h =
      (derivedInverseImage S (ψ ≫ φ)).map g ≫
        (derivedInverseImageCompIso S ψ φ).hom.app K' ≫ h := by
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun t => t ≫ h)
    ((derivedInverseImageCompIso S ψ φ).hom.naturality g).symm

omit [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})] in
/-- The derived inverse-image compositor on the image of a complex, in the simplicial
vocabulary. -/
theorem derivedInverseImageCompIso_hom_app_Q {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (Y : CochainComplex (Sheaf (S.componentTopology l) Ab.{u}) ℤ) :
    (derivedInverseImageCompIso S ψ φ).hom.app (DerivedCategory.Q.obj Y) =
      (abelianTransition S (ψ ≫ φ)).mapDerivedCategoryFactors.hom.app Y ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (abelianCompIso S ψ φ)
          (ComplexShape.up ℤ)).hom.app Y) ≫
        (abelianTransition S φ).mapDerivedCategoryFactors.inv.app
          (((abelianTransition S ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≫
        (derivedInverseImage S φ).map
          ((abelianTransition S ψ).mapDerivedCategoryFactors.inv.app Y) :=
  derivedCompIso_hom_app_Q _ _ _ _ Y

/-- The unit law for the canonical derived transition, read at an object: along an identity
simplex map it is the unit comparison of derived inverse images. -/
theorem derivedTransition_id_app (n : SimplexCategory)
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    (derivedTransition S (𝟙 n)).app K =
      (derivedInverseImageIdIso S n).hom.app ((derivedComponent S n).obj K) := by
  rw [derivedTransition_id]
  exact Category.comp_id _

/-- The compositor law for the canonical derived transition: along `ψ ≫ φ` it is the derived
inverse-image compositor followed by the transitions along `ψ` and `φ`. -/
theorem derivedTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    derivedTransition S (ψ ≫ φ) =
      Functor.whiskerLeft (derivedComponent S l) (derivedInverseImageCompIso S ψ φ).hom ≫
        Functor.whiskerRight (derivedTransition S ψ) (derivedInverseImage S φ) ≫
        derivedTransition S φ :=
  derivedTransition_comp_of_app_Q (abelianComponent S l) (abelianComponent S m)
    (abelianComponent S n) (abelianTransition S ψ) (abelianTransition S φ)
    (abelianTransition S (ψ ≫ φ)) (abelianCompIso S ψ φ) (abelianTransitionOfFiber S ψ)
    (abelianTransitionOfFiber S φ) (abelianTransitionOfFiber S (ψ ≫ φ))
    (derivedTransition S ψ) (derivedTransition S φ) (derivedTransition S (ψ ≫ φ))
    (fun A => (abelianTransitionOfFiber_comp_app S ψ φ A).symm)
    (derivedTransition_app_Q_comp S ψ) (derivedTransition_app_Q_comp S φ)
    (derivedTransition_app_Q_comp S (ψ ≫ φ))

/-- The compositor law for the canonical derived transition, read at an object. -/
theorem derivedTransition_comp_app {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    (derivedTransition S (ψ ≫ φ)).app K =
      (derivedInverseImageCompIso S ψ φ).hom.app ((derivedComponent S l).obj K) ≫
        (derivedInverseImage S φ).map ((derivedTransition S ψ).app K) ≫
        (derivedTransition S φ).app K := by
  rw [derivedTransition_comp]
  rfl

/-- The canonical simplicial system of the derived category attached to an object `K` of the
derived category of abelian sheaves on the total site, together with the equations stating that
its object in degree `n` is the derived restriction of `K` and its transition along a simplex map
is the canonical derived transition at `K`. -/
@[stacks 0D9H "associated simplicial system"]
def associatedDerivedSystemData (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    { T : SimplicialDerivedSystem S //
      (∀ n, T.obj n = (derivedComponent S n).obj K) ∧
      (∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n),
        HEq (T.map φ) ((derivedTransition S φ).app K)) } :=
  ⟨{ obj := fun n => (derivedComponent S n).obj K
     map := fun φ => (derivedTransition S φ).app K
     map_comp := fun ψ φ => derivedTransition_comp_app S ψ φ K },
    fun _ => rfl, fun _ _ _ => HEq.rfl⟩

/-- The simplicial system of the derived category associated to an object of the derived
category of abelian sheaves on the total site. -/
def associatedDerivedSystem (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    SimplicialDerivedSystem S :=
  (associatedDerivedSystemData S K).val

/-- The simplicial system of derived restrictions of a cartesian object is cartesian. -/
@[stacks 0D9H "cartesian objects give cartesian systems"]
theorem associatedDerivedSystem_cartesian
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) (hK : S.IsCartesianDerived K) :
    (associatedDerivedSystem S K).Cartesian :=
  fun φ => hK φ

end Derived

end CategoryTheory.SimplicialSiteSituation

end
