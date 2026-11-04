module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Recognising a coreflection from a counit candidate

Let `P` be a property of objects of a category `C` whose inclusion `P.ι` has a right adjoint `R`,
and let `F : C ⥤ C` be an endofunctor equipped with `ε : F ⟶ 𝟭 C`. Suppose `F` lands in `P`, that
`ε` is invertible on objects of `P`, and that `F` inverts every component of `ε`. Then `F`
*is* the coreflection: there is an isomorphism `R ⋙ P.ι ≅ F` carrying the adjunction counit to
`ε`.

The argument is the uniqueness of a right adjoint. The three hypotheses say exactly that
composing with `ε.app X` is a bijection from `Y ⟶ F.obj X` to `Y ⟶ X` for every `Y` in `P`, so
`F`, corestricted to `P`, satisfies the universal property of the right adjoint; the adjoint is
unique up to a unique isomorphism compatible with the counits, which is the normalization in the
conclusion.

The normalization is the point. Without it the isomorphism would be an unidentified comparison
and could not be composed with anything; carrying the counit across is what makes the resulting
description of the coreflection usable, and it is what Stacks 0A6R asserts when it says the Čech
complex *computes* `RΓ_Z` rather than merely being isomorphic to it.

## Main results

* `Stacks.LocalCohomology.CechFormula.bijective_comp_counit` — composing with an invertible
  component of `ε` is bijective.
* `Stacks.LocalCohomology.CechFormula.exists_normalized_coreflectionIso` — the normalized
  identification of `F` with the coreflection.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace Stacks.LocalCohomology.CechFormula

/-- **Composition with a counit candidate is bijective.** If `ε.app Y` is invertible and `F`
inverts `ε.app X`, then composing with `ε.app X` identifies `Y ⟶ F.obj X` with `Y ⟶ X`.

Injectivity: two morphisms agreeing after `ε.app X` have equal images under `F`, because
`F (ε.app X)` is a monomorphism; naturality of `ε` then transports that equality back, using
that `ε.app Y` is an epimorphism. Surjectivity: `inv (ε.app Y) ≫ F.map g` is a preimage of `g`,
again by naturality. -/
theorem bijective_comp_counit
    {C : Type u} [Category.{v} C] (F : C ⥤ C) (ε : F ⟶ 𝟭 C)
    (Y X : C) [IsIso (ε.app Y)] [IsIso (F.map (ε.app X))] :
    Function.Bijective (fun g : Y ⟶ F.obj X => g ≫ ε.app X) := by
  constructor
  · intro g h eq
    have he : F.map g = F.map h := by
      apply (cancel_mono (F.map (ε.app X))).1
      simpa only [← F.map_comp] using congrArg F.map eq
    apply (cancel_epi (ε.app Y)).1
    simpa only [Functor.id_map] using
      (ε.naturality g).symm.trans ((congrArg (fun k => k ≫ ε.app (F.obj X)) he).trans
        (ε.naturality h))
  · exact fun g => ⟨inv (ε.app Y) ≫ F.map g, by simp⟩

/-- **An endofunctor with a counit candidate is the coreflection.** Let `P.ι ⊣ R` and let
`ε : F ⟶ 𝟭 C` satisfy: `F` takes values in `P`, `ε` is invertible on `P`, and `F` inverts every
component of `ε`. Then `R ⋙ P.ι ≅ F`, by an isomorphism which carries the counit of the
adjunction to `ε`.

`F` corestricts to `P` as `P.lift F`, and `bijective_comp_counit` makes composition with `ε`
into the hom-set bijection of an adjunction `P.ι ⊣ P.lift F`. Uniqueness of the right adjoint
supplies the isomorphism, and `Adjunction.rightAdjointUniq_hom_app_counit` is exactly the
statement that it respects the counits. -/
theorem exists_normalized_coreflectionIso
    {C : Type u} [Category.{v} C] (P : ObjectProperty C) (R : C ⥤ P.FullSubcategory)
    (adj : P.ι ⊣ R) (F : C ⥤ C) (ε : F ⟶ 𝟭 C)
    (hF : ∀ X, P (F.obj X))
    (hε : ∀ Y, P Y → IsIso (ε.app Y))
    (hFε : ∀ X, IsIso (F.map (ε.app X))) :
    ∃ e : R ⋙ P.ι ≅ F, e.hom ≫ ε = adj.counit := by
  let G := P.lift F hF
  have hb (Y : P.FullSubcategory) (X : C) :
      Function.Bijective (fun g : Y ⟶ G.obj X => P.ι.map g ≫ ε.app X) := by
    have := hε Y.obj Y.property
    have := hFε X
    exact (bijective_comp_counit F ε Y.obj X).comp P.fullyFaithfulι.homEquiv.bijective
  let E : ∀ Y X, (P.ι.obj Y ⟶ X) ≃ (Y ⟶ G.obj X) :=
    fun Y X => (Equiv.ofBijective _ (hb Y X)).symm
  have hE (Y : P.FullSubcategory) (X : C) (g : P.ι.obj Y ⟶ X) :
      P.ι.map (E Y X g) ≫ ε.app X = g :=
    (Equiv.ofBijective _ (hb Y X)).apply_symm_apply g
  let adjG : P.ι ⊣ G := Adjunction.mkOfHomEquiv {
    homEquiv := E
    homEquiv_naturality_left_symm := by
      intro Y' Y X g k
      show P.ι.map (g ≫ k) ≫ ε.app X = P.ι.map g ≫ (P.ι.map k ≫ ε.app X)
      rw [P.ι.map_comp, Category.assoc]
    homEquiv_naturality_right := by
      intro Y X X' g k
      apply (hb Y X').injective
      show P.ι.map (E Y X' (g ≫ k)) ≫ ε.app X' =
        P.ι.map (E Y X g ≫ G.map k) ≫ ε.app X'
      rw [hE, P.ι.map_comp, Category.assoc]
      show g ≫ k = P.ι.map (E Y X g) ≫ F.map k ≫ ε.app X'
      rw [ε.naturality, ← Category.assoc, hE]
      rfl }
  refine ⟨Functor.isoWhiskerRight (adj.rightAdjointUniq adjG) P.ι ≪≫ P.liftCompιIso F hF, ?_⟩
  ext X
  have h := adj.rightAdjointUniq_hom_app_counit adjG X
  have hεG : adjG.counit.app X = ε.app X := by
    show P.ι.map (𝟙 (G.obj X)) ≫ ε.app X = ε.app X
    simp
  rw [hεG] at h
  refine Eq.trans ?_ h
  show (P.ι.map ((adj.rightAdjointUniq adjG).hom.app X) ≫
    (P.liftCompιIso F hF).hom.app X) ≫ ε.app X = _
  rw [Category.assoc,
    show (P.liftCompιIso F hF).hom.app X ≫ ε.app X = ε.app X from Category.id_comp _]

end Stacks.LocalCohomology.CechFormula
