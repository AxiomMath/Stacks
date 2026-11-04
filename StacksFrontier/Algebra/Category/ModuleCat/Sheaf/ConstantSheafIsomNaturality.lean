module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsom

/-!
# The constant `Isom` comparison is natural along non-invertible maps of modules

Stacks Tag 093T (2) identifies the constant sheaf `Isom_Λ(M, N)̲` with the sheaf
`Isom_{Λ̲}(M̲, N̲)` of isomorphisms of the two constant sheaves
(`Stacks.ConstantSheaf.constantSheafIsomIso`). This file records that the identification is
natural in the module arguments along an *arbitrary* morphism of modules, not only along an
isomorphism of them, which is what
`Stacks.ConstantSheaf.moduleSheafIsomMapIso` provides.

The naturality asked for here is the one a tower of adic reductions needs: the transition maps of
`n ↦ M ⧸ Iⁿ M` are reductions, the induced maps of the sets of self-isomorphisms make
`n ↦ Isom_Λ(Mₙ, Mₙ)` an inverse system, and the comparison has to carry that system to the
system of automorphisms of the constant sheaves `Mₙ̲`. That is the input of Stacks Tag 09BV which
`CategoryTheory.Functor.nonempty_natIso_of_isMittagLeffler_isoTower` consumes.

## Main definitions

* `Stacks.ConstantSheaf.sheafHomMap`: the internal hom of sheaves is contravariantly functorial
  in its source and covariantly in its target. This is
  `Stacks.ConstantSheaf.moduleSheafHomMap` with no module structure on the sections, which is the
  form in which the subsheaf `Isom` maps to it.
* `Stacks.ConstantSheaf.sheafIsomIncl`: the inclusion of `Isom(F, G)` into the internal hom.

## Main results

* `Stacks.ConstantSheaf.constantSheafIsomHom_naturality`: the naturality square.

## Implementation notes

The proof is the universal property of sheafification rather than a local argument: the two
composites are morphisms out of `Isom_Λ(M, M)̲`, a sheafification, so `sheafify_hom_ext` reduces
the claim to the constant sections, on which the comparison is
`Stacks.ConstantSheaf.constantIsomNatTrans` and both sides are the image under the constant sheaf
functor of a square of module maps. No local triviality of a section of a constant sheaf, and no
gluing, is needed.

The reassociations which bring the two composites into the shape `toSheafify ≫ comparison ≫ rest`
are done in term mode, with the tail abstracted as a variable. Done by `rw` on the composites
themselves they produce a target which is not type-correct at `implicit` transparency: the
sections of `Isom` carry two spellings, `Stacks.ConstantSheaf.sheafIsom` at the coefficient
category `ModuleCat Λ` and `Stacks.ConstantSheaf.moduleSheafIsom`, whose `Quiver` instances are
reached by different paths.

## References

* [Stacks Project, Tag 093T](https://stacks.math.columbia.edu/tag/093T)
* [Stacks Project, Tag 09BV](https://stacks.math.columbia.edu/tag/09BV)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w x u' v'

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section SheafHom

variable {A : Type u'} [Category.{v'} A]

/-- **The internal hom of sheaves is contravariantly functorial in its source and covariantly
functorial in its target**: a section over `X`, a morphism of the restrictions to the slice site
`C/X`, is carried to its composite with the restrictions of the two given morphisms. -/
def sheafHomMap {F F' G G' : Sheaf J A} (u : F' ⟶ F) (w : G ⟶ G') :
    sheafHom F G ⟶ sheafHom F' G' :=
  ⟨{ app := fun X => TypeCat.ofHom fun α =>
        (J.overPullback A X.unop).map u ≫ α ≫ (J.overPullback A X.unop).map w
     naturality := fun {X Y} f => ConcreteCategory.hom_ext _ _ fun α => by
       apply Sheaf.hom_ext
       apply NatTrans.ext
       rfl }⟩

/-- The section of `sheafHomMap J u w` over `X` sends `α` to the composite of `α` with the
restrictions of `u` and `w` to the slice site `C/X`. -/
@[simp]
theorem sheafHomMap_app_apply {F F' G G' : Sheaf J A} (u : F' ⟶ F) (w : G ⟶ G') (X : Cᵒᵖ)
    (α : (sheafHom F G).obj.obj X) :
    (sheafHomMap J u w).hom.app X α =
      (J.overPullback A X.unop).map u ≫ α ≫ (J.overPullback A X.unop).map w :=
  rfl

/-- **The inclusion of `Isom(F, G)` into the internal hom**, an invertible section of the internal
hom being in particular a section of it. -/
def sheafIsomIncl (F G : Sheaf J A) : sheafIsom J A F G ⟶ sheafHom F G :=
  ⟨(sheafIsomSubfunctor J A F G).ι⟩

end SheafHom

section Naturality

variable (Λ : Type w) [CommRing Λ] (M N : ModuleCat.{max u v x} Λ)
  [Module.FinitePresentation Λ (M : Type (max u v x))]
  [Module.FinitePresentation Λ (N : Type (max u v x))]

omit [Module.FinitePresentation Λ (M : Type (max u v x))]
  [Module.FinitePresentation Λ (N : Type (max u v x))] in
/-- **The comparison of Tag 093T (2) is natural in its module arguments along arbitrary — in
particular non-invertible — maps.** Let `p : M ⟶ N` be a morphism of finitely presented
`Λ`-modules and let `red` carry a self-isomorphism of `M` to one of `N` compatibly with `p`.
Then the square

```
Isom_Λ(M, M)̲ ⟶ Isom_{Λ̲}(M̲, M̲) --- ≫ p̲ ---> SheafHom(M̲, N̲)
     |                                              ‖
   red̲                                              ‖
     v                                              ‖
Isom_Λ(N, N)̲ ⟶ Isom_{Λ̲}(N̲, N̲) --- p̲ ≫ ---> SheafHom(M̲, N̲)
```

commutes. `Stacks.ConstantSheaf.moduleSheafIsomMapIso` covers only conjugation by an
*isomorphism* of the arguments; a tower of adic reductions has reduction maps for its transition
maps, and those are not isomorphisms.

Both composites are morphisms out of a sheafification, so it is enough that they agree on the
constant sections, where the comparison is `e ↦ e̲` by
`Stacks.ConstantSheaf.constantIsomNatTrans_app_apply` and the square is the image under the
constant sheaf functor of the square `e ≫ p = p ≫ red e` of modules. -/
theorem constantSheafIsomHom_naturality (p : M ⟶ N)
    (red : ((M : Type (max u v x)) ≃ₗ[Λ] (M : Type (max u v x))) →
      ((N : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x))))
    (hred : ∀ e, ModuleCat.ofHom (LinearEquiv.toLinearMap e) ≫ p =
      p ≫ ModuleCat.ofHom (red e).toLinearMap) :
    constantSheafIsomHom J Λ M M ≫ sheafIsomIncl J _ _ ≫
        sheafHomMap J (𝟙 _) ((constantSheaf J (ModuleCat.{max u v x} Λ)).map p) =
      (constantSheaf J (Type (max u v x))).map (TypeCat.ofHom red) ≫
        constantSheafIsomHom J Λ N N ≫ sheafIsomIncl J _ _ ≫
          sheafHomMap J ((constantSheaf J (ModuleCat.{max u v x} Λ)).map p) (𝟙 _) := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext J _ _ (sheafHom _ _).property ?_
  have hred0 : ((constantSheaf J (Type (max u v x))).map (↾red)).hom
      = sheafifyMap J ((Functor.const Cᵒᵖ).map (↾red)) := rfl
  have hM : ∀ {Q : Cᵒᵖ ⥤ Type (max u v x)}
      (g : (moduleSheafIsom J Λ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)).obj ⟶ Q),
      CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
          ((M : Type (max u v x)) ≃ₗ[Λ] (M : Type (max u v x)))) ≫
          (constantSheafIsomHom J Λ M M).hom ≫ g =
        constantIsomNatTrans J Λ M M ≫ g := fun g =>
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ g) (toSheafify_constantSheafIsomHom J Λ M M))
  have hN : ∀ {Q : Cᵒᵖ ⥤ Type (max u v x)}
      (g : (moduleSheafIsom J Λ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N)
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N)).obj ⟶ Q),
      CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
          ((N : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x)))) ≫
          (constantSheafIsomHom J Λ N N).hom ≫ g =
        constantIsomNatTrans J Λ N N ≫ g := fun g =>
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ g) (toSheafify_constantSheafIsomHom J Λ N N))
  have hnat : ∀ {Q : Cᵒᵖ ⥤ Type (max u v x)}
      (g : sheafify J ((Functor.const Cᵒᵖ).obj
        ((N : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x)))) ⟶ Q),
      CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
          ((M : Type (max u v x)) ≃ₗ[Λ] (M : Type (max u v x)))) ≫
          sheafifyMap J ((Functor.const Cᵒᵖ).map (↾red)) ≫ g =
        (Functor.const Cᵒᵖ).map (↾red) ≫ CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
          ((N : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x)))) ≫ g := fun g =>
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ g) (toSheafify_naturality J
        ((Functor.const Cᵒᵖ).map (↾red))).symm).trans (Category.assoc _ _ _))
  simp only [ObjectProperty.FullSubcategory.comp_hom, hred0]
  refine (hM _).trans ((Eq.trans ?_
    (congrArg (fun t => (Functor.const Cᵒᵖ).map (↾red) ≫ t) (hN _)).symm).trans (hnat _).symm)
  apply NatTrans.ext
  funext X
  refine ConcreteCategory.hom_ext _ _ fun e => ?_
  have hcomp : ∀ {P Q R : ModuleCat.{max u v x} Λ} (a : P ⟶ Q) (b : Q ⟶ R),
      (J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
            ((constantSheaf J (ModuleCat.{max u v x} Λ)).map a) ≫
          (J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
            ((constantSheaf J (ModuleCat.{max u v x} Λ)).map b) =
        (J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
          ((constantSheaf J (ModuleCat.{max u v x} Λ)).map (a ≫ b)) := fun a b => by
    rw [← Functor.map_comp, ← Functor.map_comp]
  change (J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
        (𝟙 ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)) ≫
      ((J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).map
          (ModuleCat.ofHom (LinearEquiv.toLinearMap e)))) ≫
      (J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).map p) =
    (J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).map p) ≫
      ((J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).map
          (ModuleCat.ofHom (LinearEquiv.toLinearMap (red e))))) ≫
      (J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
        (𝟙 ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N))
  rw [CategoryTheory.Functor.map_id, Category.id_comp, CategoryTheory.Functor.map_id,
    Category.comp_id, hcomp, hcomp, hred e]

end Naturality

end Stacks.ConstantSheaf

end
