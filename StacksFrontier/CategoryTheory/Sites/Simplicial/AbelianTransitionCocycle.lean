module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerived
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TransitionCocycle

/-!
# Pseudofunctoriality of the abelian restriction transitions of a simplicial site

Let `S` be a simplicial-site situation. Restricting an abelian sheaf on its total site to the
simplicial degrees and comparing across a simplex map gives the transition
`CategoryTheory.SimplicialSiteSituation.abelianComponentTransition`, the transition of Stacks
09WF read on abelian sheaves. This file proves that it is pseudofunctorial for the canonical
abelian inverse-image comparisons `abelianIdIso` and `abelianCompIso` of Stacks 0D9G: the
transition of an identity simplex map is the unit comparison, and the transition of a composite
is the composite of the transitions compared by the compositor.

## Main results

* `CategoryTheory.SimplicialSiteSituation.abelianComponentTransition_id` and
  `.abelianComponentTransition_comp`: the unit and cocycle laws on abelian sheaves.
* `CategoryTheory.SimplicialSiteSituation.forget_map_abelianComponentTransition_app`,
  `.forget_map_abelianIdIso_app` and `.forget_map_abelianCompIso_app`: the underlying sheaf of
  sets of each of the three maps involved, which is what reduces the two laws to the
  corresponding laws for sheaves of sets.
* `CategoryTheory.conjugate_transition_comp` and `.conjugate_transition_id`: the two laws
  transport along conjugation by isomorphisms, for an arbitrary pair of composable functors.

## Implementation notes

Forgetting the abelian group structure is faithful, so each law may be checked on underlying
sheaves of sets, where it is `CategoryTheory.SimplicialSiteSituation.fiberTransition_comp`,
respectively `fiberTransition_id`, of Stacks 09WF. The reduction is not literal, because the
abelian transition is built from the inverse image of the *component morphism of topoi* while
the transition of sheaves of sets is stated for plain restriction; the underlying map of the
abelian transition is therefore the transition of sheaves of sets conjugated by the comparison
`componentMorphismInverseImageIso` of Stacks 00XR (1). That conjugation is the content of
`forget_map_abelianComponentTransition_app`, and `conjugate_transition_comp` and
`conjugate_transition_id` say that the two laws are insensitive to it.

Each of the three underlying maps is computed by a single `rfl` after one stray
`f_φ⁻¹(𝟙)` is named: the abelian inverse image is *definitionally* the geometric inverse image
of the underlying sheaf of sets, which is what
`CategoryTheory.Sites.abelianInverseImage_forgetIso` records, so the comparisons assembled from
associators, unitors and `CategoryTheory.Functor.mapCommGrp` all forget to identities. The one
exception is the counit of the equivalence between abelian sheaves and commutative group
objects, which forgets to an identity *inside* an inverse image, and `Functor.map_id` must be
applied there; stating the goal with that factor present, through `Functor.map_id_comp` and
`Functor.comp_map_id`, keeps every intermediate expression type-correct.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites

universe u

namespace CategoryTheory

section Conjugation

variable {A : Type*} [Category A] {B : Type*} [Category B] {D : Type*} [Category D]

/-- The image of a triple composite under a functor. -/
theorem Functor.map_comp₃ (F : A ⥤ B) {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    F.map (f ≫ g ≫ h) = F.map f ≫ F.map g ≫ F.map h := by
  rw [F.map_comp, F.map_comp]

/-- The cocycle law is insensitive to conjugating the transitions by isomorphisms. If
transitions `tψ`, `tφ`, `tψφ` satisfy the cocycle law for a compositor `cmp`, then so do their
conjugates `sψ`, `sφ`, `sψφ` by isomorphisms `cl`, `cm`, `cn` of the source and target
objects. -/
theorem conjugate_transition_comp (Vψ : A ⥤ B) (Vφ : B ⥤ D) (Vψφ : A ⥤ D)
    (cmp : Vψφ ≅ Vψ ⋙ Vφ) {Pl Rl : A} (cl : Pl ≅ Rl) {Pm Rm : B} (cm : Pm ≅ Rm)
    {Pn Rn : D} (cn : Pn ≅ Rn)
    (tψ : Vψ.obj Rl ⟶ Rm) (tφ : Vφ.obj Rm ⟶ Rn) (tψφ : Vψφ.obj Rl ⟶ Rn)
    (ht : tψφ = cmp.hom.app Rl ≫ Vφ.map tψ ≫ tφ)
    (u : Vψφ.obj Pl ⟶ Vφ.obj (Vψ.obj Pl)) (hu : u = cmp.hom.app Pl)
    (sψ : Vψ.obj Pl ⟶ Pm) (hsψ : sψ = Vψ.map cl.hom ≫ tψ ≫ cm.inv)
    (sφ : Vφ.obj Pm ⟶ Pn) (hsφ : sφ = Vφ.map cm.hom ≫ tφ ≫ cn.inv)
    (sψφ : Vψφ.obj Pl ⟶ Pn) (hsψφ : sψφ = Vψφ.map cl.hom ≫ tψφ ≫ cn.inv) :
    sψφ = u ≫ Vφ.map sψ ≫ sφ := by
  subst hu hsψ hsφ hsψφ ht
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (Vφ.map cm.inv), ← Vφ.map_comp, cm.inv_hom_id, Vφ.map_id,
    Category.id_comp, ← Category.assoc (Vψφ.map cl.hom), cmp.hom.naturality cl.hom]
  simp only [Functor.comp_map, Category.assoc]

/-- The unit law is insensitive to conjugating the transition by an isomorphism. If a transition
`t` at an identity is the unit comparison `uid`, then so is its conjugate `s` by an isomorphism
`c` of the object. -/
theorem conjugate_transition_id (Vid : A ⥤ A) (uid : Vid ≅ 𝟭 A) {P R : A} (c : P ≅ R)
    (t : Vid.obj R ⟶ R) (ht : t = uid.hom.app R)
    (s : Vid.obj P ⟶ P) (hs : s = Vid.map c.hom ≫ t ≫ c.inv) :
    s = uid.hom.app P := by
  subst hs ht
  rw [← Category.assoc, uid.hom.naturality c.hom]
  simp

end Conjugation

namespace SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- The underlying map of sheaves of sets of the abelian unit comparison of Stacks 0D9G is the
unit comparison of Stacks 09WF. -/
theorem forget_map_abelianIdIso_app (n : SimplexCategory)
    (X : Sheaf (S.componentTopology n) Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map ((abelianIdIso S n).hom.app X) =
      (canonicalIdentityComparison S n).hom.app
        ((sheafCompose (S.componentTopology n) (forget Ab.{u})).obj X) :=
  rfl

/-- The underlying map of sheaves of sets of the abelian inverse-image compositor of Stacks
0D9G is the compositor of Stacks 09WF. -/
theorem forget_map_abelianCompIso_app {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (X : Sheaf (S.componentTopology l) Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianCompIso S ψ φ).hom.app X) =
      (canonicalCompositionComparison S ψ φ).hom.app
        ((sheafCompose (S.componentTopology l) (forget Ab.{u})).obj X) := by
  refine Eq.trans ?_ (Functor.comp_map_id (F := (S.transitionMorphism φ).inverseImage)
    (Y := (S.transitionMorphism ψ).inverseImage.obj
      ((sheafCompose (S.componentTopology l) (forget Ab.{u})).obj X)) _)
  ext V x
  rfl

/-- The underlying map of sheaves of sets of the abelian transition of Stacks 09WF is the
transition of sheaves of sets, conjugated by the identification of the inverse image of the
component morphism of topoi with plain restriction. -/
theorem forget_map_abelianComponentTransition_app {m n : SimplexCategory} (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (sheafCompose (S.componentTopology n) (forget Ab.{u})).map
        ((abelianComponentTransition S φ).app A) =
      (S.transitionMorphism φ).inverseImage.map
          ((componentMorphismInverseImageIso S m).hom.app
            ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)) ≫
        (fiberTransition S φ).app ((sheafCompose S.totalTopology (forget Ab.{u})).obj A) ≫
        (componentMorphismInverseImageIso S n).inv.app
          ((sheafCompose S.totalTopology (forget Ab.{u})).obj A) := by
  refine Eq.trans ?_ (Functor.map_id_comp (F := (S.transitionMorphism φ).inverseImage)
    (X := (componentMorphism S m).inverseImage.obj
      ((sheafCompose S.totalTopology (forget Ab.{u})).obj A)) _)
  ext V x
  rfl

/-- The cocycle law for the abelian transition of Stacks 09WF: the transition attached to a
composite simplex map is the composite of the two transitions, compared by the abelian
inverse-image compositor of Stacks 0D9G. -/
theorem abelianComponentTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (abelianComponentTransition S (ψ ≫ φ)).app A =
      (abelianCompIso S ψ φ).hom.app ((abelianComponent' S l).obj A) ≫
        (abelianTransition S φ).map ((abelianComponentTransition S ψ).app A) ≫
        (abelianComponentTransition S φ).app A := by
  refine (sheafCompose (S.componentTopology n) (forget Ab.{u})).map_injective ?_
  refine Eq.trans ?_ (Functor.map_comp₃ _ _ _ _).symm
  exact conjugate_transition_comp _ _ _ (canonicalCompositionComparison S ψ φ)
    ((componentMorphismInverseImageIso S l).app _) ((componentMorphismInverseImageIso S m).app _)
    ((componentMorphismInverseImageIso S n).app _) _ _ _ (fiberTransition_comp S ψ φ _)
    _ (forget_map_abelianCompIso_app S ψ φ _)
    _ (forget_map_abelianComponentTransition_app S ψ A)
    _ (forget_map_abelianComponentTransition_app S φ A)
    _ (forget_map_abelianComponentTransition_app S (ψ ≫ φ) A)

/-- The unit law for the abelian transition of Stacks 09WF: the transition attached to an
identity simplex map is the abelian inverse-image unit comparison of Stacks 0D9G. -/
theorem abelianComponentTransition_id (n : SimplexCategory)
    (A : Sheaf S.totalTopology Ab.{u}) :
    (abelianComponentTransition S (𝟙 n)).app A =
      (abelianIdIso S n).hom.app ((abelianComponent' S n).obj A) := by
  refine (sheafCompose (S.componentTopology n) (forget Ab.{u})).map_injective ?_
  refine Eq.trans ?_ (forget_map_abelianIdIso_app S n _).symm
  exact conjugate_transition_id _ (canonicalIdentityComparison S n)
    ((componentMorphismInverseImageIso S n).app _) _ (fiberTransition_id S n _)
    _ (forget_map_abelianComponentTransition_app S (𝟙 n) A)

end SimplicialSiteSituation

end CategoryTheory

end
