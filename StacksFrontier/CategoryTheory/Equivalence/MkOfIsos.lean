module

public import StacksCore.CategoryTheory.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The quasi-inverse determined by a choice of isomorphisms (Stacks 05SG)

Let `F : C ⥤ D` be fully faithful and suppose that for every object `X` of `D` we are given an
object `j X` of `C` and an isomorphism `i X : X ≅ F.obj (j X)`. Lemma 4.2.19 (Stacks 05SG) says
that there is a unique functor `G : D ⥤ C` with `G.obj = j` on objects such that the `i X` are
the components of a natural isomorphism `𝟭 D ≅ G ⋙ F`, and that this functor and `F` are
quasi-inverse equivalences of categories.

`CategoryTheory.Equivalence.mkOfIsos` constructs the equivalence. Here we prove that its inverse
is the unique such functor (`CategoryTheory.Equivalence.eq_mkOfIsos_inverse`) and bundle
existence, uniqueness and the quasi-inverse statement in
`CategoryTheory.Equivalence.existsUnique_functor_of_isos`.

The condition on `G` reads: `G.obj X = j X` for all `X` (written `h X`), and there is a natural
isomorphism `α : 𝟭 D ≅ G ⋙ F` whose component at `X` is `i X`, transported along `h X`.
-/

@[expose] public section

namespace CategoryTheory.Equivalence

variable {C D : Type*} [Category* C] [Category* D]

/-- Any functor `G : D ⥤ C` agreeing with `j` on objects such that the isomorphisms
`i X : X ≅ F.obj (j X)` are the components of a natural isomorphism `𝟭 D ≅ G ⋙ F` is equal to
the inverse of `Equivalence.mkOfIsos F hF j i`. -/
theorem eq_mkOfIsos_inverse (F : C ⥤ D) (hF : F.FullyFaithful) (j : D → C)
    (i : ∀ X, X ≅ F.obj (j X)) (G : D ⥤ C) (h : ∀ X, G.obj X = j X) (α : 𝟭 D ≅ G ⋙ F)
    (hα : ∀ X, α.hom.app X = (i X).hom ≫ eqToHom (congrArg F.obj (h X).symm)) :
    G = (mkOfIsos F hF j i).inverse := by
  have hj : G.obj = j := funext h
  subst hj
  refine Functor.ext (fun _ ↦ rfl) (fun X Y f ↦ ?_)
  change G.map f = 𝟙 _ ≫ hF.preimage ((i X).inv ≫ f ≫ (i Y).hom) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  apply hF.map_injective
  have hnat := α.hom.naturality f
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map, hα,
    eqToHom_refl, Category.comp_id] at hnat
  rw [hF.map_preimage, hnat, Iso.inv_hom_id_assoc]

/-- **Stacks 05SG.** Let `F : C ⥤ D` be fully faithful and, for every object `X` of `D`, let
`j X` be an object of `C` and `i X : X ≅ F.obj (j X)` an isomorphism. Then there is a unique
functor `G : D ⥤ C` such that `G` extends the rule `j` on objects (`h : ∀ X, G.obj X = j X`) and
the isomorphisms `i X` define an isomorphism of functors `α : 𝟭 D ≅ G ⋙ F` (the component of `α`
at `X` is `i X`, transported along `h X`). Moreover, any such `G` and `F` are quasi-inverse
equivalences of categories: there is an equivalence `e : C ≌ D` with `e.functor = F` and
`e.inverse = G`. -/
@[stacks 05SG "existence and uniqueness of the functor `j` extending the rule on objects for
which the `i_X` form an isomorphism `id ≅ F ∘ j`, and that `j` and `F` are quasi-inverse
equivalences; the equivalence itself is `CategoryTheory.Equivalence.mkOfIsos`"]
theorem existsUnique_functor_of_isos (F : C ⥤ D) (hF : F.FullyFaithful) (j : D → C)
    (i : ∀ X, X ≅ F.obj (j X)) :
    (∃! G : D ⥤ C, ∃ h : ∀ X, G.obj X = j X, ∃ α : 𝟭 D ≅ G ⋙ F,
        ∀ X, α.hom.app X = (i X).hom ≫ eqToHom (congrArg F.obj (h X).symm)) ∧
      ∀ G : D ⥤ C, (∃ h : ∀ X, G.obj X = j X, ∃ α : 𝟭 D ≅ G ⋙ F,
        ∀ X, α.hom.app X = (i X).hom ≫ eqToHom (congrArg F.obj (h X).symm)) →
        ∃ e : C ≌ D, e.functor = F ∧ e.inverse = G := by
  refine ⟨⟨(mkOfIsos F hF j i).inverse, ⟨fun _ ↦ rfl,
    NatIso.ofComponents (fun X ↦ i X) (fun {X Y} f ↦ by
      change f ≫ (i Y).hom = (i X).hom ≫ F.map (hF.preimage ((i X).inv ≫ f ≫ (i Y).hom))
      rw [hF.map_preimage, Iso.hom_inv_id_assoc]), fun _ ↦ (Category.comp_id _).symm⟩,
    fun G ⟨h, α, hα⟩ ↦ eq_mkOfIsos_inverse F hF j i G h α hα⟩, ?_⟩
  rintro G ⟨h, α, hα⟩
  exact ⟨mkOfIsos F hF j i, rfl, (eq_mkOfIsos_inverse F hF j i G h α hα).symm⟩

end CategoryTheory.Equivalence
