module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Ext` is computed in a subcategory whose bounded derived category embeds fully faithfully

Let `Φ : 𝒞 ⥤ 𝒟` be an exact additive functor of abelian categories. It induces maps
`Ext^n_𝒞(X, Y) ⟶ Ext^n_𝒟(Φ X, Φ Y)` (`CategoryTheory.Functor.mapExtAddHom`), and this file
shows that those maps are **bijective** as soon as the induced functor
`D^b(𝒞) ⥤ D(𝒟)` is fully faithful.

That hypothesis is weaker than the ones Mathlib's
`CategoryTheory.Functor.mapExt_bijective_of_preservesProjectiveObjects` and
`CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects` use: those need enough
projectives, respectively enough injectives, in `𝒞`. The case this is written for has neither.
For `𝒞 = Coh(𝒪_X)` the coherent modules on a Noetherian scheme and `𝒟 = Mod(𝒪_X)`, the
hypothesis is exactly the fully faithfulness half of [Stacks, Tag 0FDB], already available as
`AlgebraicGeometry.full_boundedι_comp_coherentInModulesι` and
`AlgebraicGeometry.faithful_boundedι_comp_coherentInModulesι`; so `Ext`-groups between coherent
modules may be computed in the abelian category of coherent modules, which is what the dévissage
of [Stacks, Tag 0G2H] uses to efface a class by a *coherent* epimorphism.

## The reduction

`CategoryTheory.Abelian.Ext.mapExactFunctor_hom` identifies the map on `Ext` with the map

`Hom_{D(𝒞)}(X[0], Y[0]⟦n⟧) ⟶ Hom_{D(𝒟)}(Φ X[0], Φ Y[0]⟦n⟧)`

of the derived functor, conjugated by the isomorphisms
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` and
`CategoryTheory.Functor.commShiftIso`. Both source and target of that map are `t`-bounded — a
single complex is, and the shift of a bounded object is — so the map is bijective by the
hypothesis.

## Main results

* `CategoryTheory.Functor.bijective_mapDerivedCategory_map_of_bounded`: the derived functor is
  bijective on morphisms between `t`-bounded objects.
* `CategoryTheory.Functor.bijective_mapExtAddHom_of_boundedFullyFaithful`: **the induced maps on
  `Ext`-groups are bijective.**

## References

* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe t t' w w' v v' u u'

namespace CategoryTheory.Functor

variable {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞] {𝒟 : Type u'} [Category.{v'} 𝒟] [Abelian 𝒟]
  (Φ : 𝒞 ⥤ 𝒟) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  [HasDerivedCategory.{t} 𝒞] [HasDerivedCategory.{t'} 𝒟]

/-- **A derived functor which is fully faithful on bounded objects is bijective on the morphisms
between two bounded objects.** The hypothesis is about the composite
`D^b(𝒞) ⥤ D(𝒞) ⥤ D(𝒟)`, and the morphisms of the full subcategory `D^b(𝒞)` are those of
`D(𝒞)`. -/
public lemma bijective_mapDerivedCategory_map_of_bounded
    [(DerivedCategory.Bounded.ι (C := 𝒞) ⋙ Φ.mapDerivedCategory).Full]
    [(DerivedCategory.Bounded.ι (C := 𝒞) ⋙ Φ.mapDerivedCategory).Faithful]
    {A B : DerivedCategory 𝒞} (hA : DerivedCategory.TStructure.t.bounded A)
    (hB : DerivedCategory.TStructure.t.bounded B) :
    Function.Bijective (fun f : A ⟶ B => Φ.mapDerivedCategory.map f) := by
  let A' : DerivedCategory.Bounded 𝒞 := ⟨A, hA⟩
  let B' : DerivedCategory.Bounded 𝒞 := ⟨B, hB⟩
  have hS : Function.Bijective (fun f : A' ⟶ B' =>
      (DerivedCategory.Bounded.ι (C := 𝒞) ⋙ Φ.mapDerivedCategory).map f) :=
    ⟨Functor.map_injective _, Functor.map_surjective _⟩
  have hhom : Function.Bijective (fun f : A' ⟶ B' => (f.hom : A ⟶ B)) :=
    ⟨fun _ _ h => ObjectProperty.hom_ext _ h, fun g => ⟨ObjectProperty.homMk g, rfl⟩⟩
  exact (Function.Bijective.of_comp_iff
    (fun f : A ⟶ B => Φ.mapDerivedCategory.map f) hhom).1 hS

variable [HasExt.{w} 𝒞] [HasExt.{w'} 𝒟]

/-- **`Ext`-groups are computed in a subcategory whose bounded derived category embeds fully
faithfully.** If `D^b(𝒞) ⥤ D(𝒟)` is fully faithful then the canonical maps
`Ext^n_𝒞(X, Y) ⟶ Ext^n_𝒟(Φ X, Φ Y)` are bijective for all `X`, `Y` and `n`.

`CategoryTheory.Abelian.Ext.mapExactFunctor_hom` writes the map on `Ext` as the map of the
derived functor on `Hom(X[0], Y[0]⟦n⟧)`, conjugated by isomorphisms; both objects are
`t`-bounded, so `CategoryTheory.Functor.bijective_mapDerivedCategory_map_of_bounded` applies. -/
@[sga "6 II 2.1.3" "b(ii) ⇒ b(i)"]
public lemma bijective_mapExtAddHom_of_boundedFullyFaithful
    [(DerivedCategory.Bounded.ι (C := 𝒞) ⋙ Φ.mapDerivedCategory).Full]
    [(DerivedCategory.Bounded.ι (C := 𝒞) ⋙ Φ.mapDerivedCategory).Faithful]
    (X Y : 𝒞) (n : ℕ) : Function.Bijective (Φ.mapExtAddHom.{w, w'} X Y n) := by
  have hsingle (Z : 𝒞) : DerivedCategory.TStructure.t.bounded
      ((DerivedCategory.singleFunctor 𝒞 0).obj Z) := ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
  have hYb : DerivedCategory.TStructure.t.bounded
      (((DerivedCategory.singleFunctor 𝒞 0).obj Y)⟦(n : ℤ)⟧) := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hsingle Y
    exact ⟨⟨a - (n : ℤ), DerivedCategory.TStructure.t.isGE_shift _ a _ _ (by lia)⟩,
      ⟨b - (n : ℤ), DerivedCategory.TStructure.t.isLE_shift _ b _ _ (by lia)⟩⟩
  have hmap := Φ.bijective_mapDerivedCategory_map_of_bounded (hsingle X) hYb
  set α : Φ.mapDerivedCategory.obj ((DerivedCategory.singleFunctor 𝒞 0).obj X) ≅
      (DerivedCategory.singleFunctor 𝒟 0).obj (Φ.obj X) :=
    (Φ.mapDerivedCategorySingleFunctor 0).app X with hα
  set β : Φ.mapDerivedCategory.obj (((DerivedCategory.singleFunctor 𝒞 0).obj Y)⟦(n : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor 𝒟 0).obj (Φ.obj Y))⟦(n : ℤ)⟧ :=
    (Φ.mapDerivedCategory.commShiftIso (n : ℤ)).app
        ((DerivedCategory.singleFunctor 𝒞 0).obj Y) ≪≫
      (shiftFunctor (DerivedCategory 𝒟) (n : ℤ)).mapIso
        ((Φ.mapDerivedCategorySingleFunctor 0).app Y) with hβ
  have hfun : ⇑(Φ.mapExtAddHom.{w, w'} X Y n) =
      (Ext.homEquiv (C := 𝒟) (X := Φ.obj X) (Y := Φ.obj Y) (n := n)).symm ∘
        ((Iso.homCongr α β) ∘ ((fun f => Φ.mapDerivedCategory.map f) ∘
          (Ext.homEquiv (C := 𝒞) (X := X) (Y := Y) (n := n)))) := by
    funext e
    simp only [Function.comp_apply]
    rw [Equiv.eq_symm_apply]
    show (Φ.mapExtAddHom.{w, w'} X Y n e).hom = _
    rw [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_hom]
    simp [hα, hβ, Iso.homCongr, ShiftedHom.map, Category.assoc]
  rw [hfun]
  exact (Equiv.bijective _).comp
    (((Iso.homCongr α β).bijective).comp (hmap.comp (Equiv.bijective _)))

end CategoryTheory.Functor

end
