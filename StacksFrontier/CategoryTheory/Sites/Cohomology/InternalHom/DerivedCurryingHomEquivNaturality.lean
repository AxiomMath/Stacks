module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrySourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsNaturality
import StacksCore.Tactic.StacksAttribute

/-! # Naturality of the tensor–internal-Hom bijection of Stacks 08J8

Let `(C, O)` be a ringed site. The tensor–internal-Hom bijection of **Stacks 08J8**,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, identifies morphisms
`K ⟶ RSheafHom(L, M)` with morphisms `K ⊗^L_O L ⟶ M` in `D(O)`. This file proves it **natural
in all three objects**.

The bijection is the derived currying isomorphism of Stacks 08J9 read on degree-zero global
hypercohomology, with both sides identified with morphism groups by Stacks 08JA
(`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_globalSections_homologyMap`). Its naturality
is therefore the naturality of those two inputs composed: the currying isomorphism is natural by
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural`, and Stacks 08JA is natural by
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_bifunctor`, applied
twice: once at `(K, RSheafHom(L, M))` and once at `(K ⊗^L_O L, M)`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality`: **the bijection of
  Stacks 08J8 is natural in `K`, `L` and `M`.** Its source-variable clause alone is
  `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, imported.

## Implementation notes

The two naturality squares of Stacks 08JA are read against the bifunctor
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsFunctor`, so that the middle step is
literally `derivedCurryIso_natural` transported by derived global sections and degree-zero
cohomology. The element `θ` is replaced at the start by its preimage under Stacks 08JA at
`(K, RSheafHom(L, M))`, which is what lets
`derivedCurryHomEquiv_globalSections_homologyMap` be applied on both sides.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The tensor–internal-Hom bijection of Stacks 08J8 is natural in all three objects.** For
morphisms `k : K' ⟶ K`, `l : L' ⟶ L` and `m : M ⟶ M'` of `D(O)`, the bijection carries a
morphism `θ : K ⟶ RSheafHom(L, M)` precomposed with `k` and postcomposed with
`RSheafHom(l, m)` to its transpose precomposed with the derived tensor product of `k` and `l`
and postcomposed with `m`. -/
@[stacks 08J8 "naturality of the tensor-internal-Hom bijection in all three objects"]
theorem derivedCurryHomEquiv_naturality
    {K K' L L' M M' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K' ⟶ K) (l : L' ⟶ L) (m : M ⟶ M')
    (θ : K ⟶ ((derivedSheafHomBifunctor X).obj (op L)).obj M) :
    derivedCurryHomEquiv X K' L' M'
        (k ≫ θ ≫ (((derivedSheafHomBifunctor X).map l.op).app M ≫
          ((derivedSheafHomBifunctor X).obj (op L')).map m)) =
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map k).app L' ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map l) ≫
        derivedCurryHomEquiv X K L M θ ≫ m := by
  obtain ⟨w, rfl⟩ := (derivedSheafHomGlobalSectionsEquiv X K
    (((derivedSheafHomBifunctor X).obj (op L)).obj M)).surjective θ
  -- the middle step: `derivedCurryIso_natural`, read at the uncurried internal Hom
  have hcurry : (Functor.uncurry.obj (derivedSheafHomBifunctor X)).map
          (((k.op, ((derivedSheafHomBifunctor X).map l.op).app M ≫
              ((derivedSheafHomBifunctor X).obj (op L')).map m)) :
            ((op K, ((derivedSheafHomBifunctor X).obj (op L)).obj M) :
                (DerivedCategory
                    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
                  DerivedCategory
                    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
              (op K', ((derivedSheafHomBifunctor X).obj (op L')).obj M')) ≫
        (derivedCurryIso X K' L' M').hom =
      (derivedCurryIso X K L M).hom ≫
        (Functor.uncurry.obj (derivedSheafHomBifunctor X)).map
          ((((((Stacks.SheafOfModules.derivedTensorProductFunctor X).map k).app L' ≫
                ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map l).op, m)) :
            ((op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L), M) :
                (DerivedCategory
                    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
                  DerivedCategory
                    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
              (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K').obj L'), M')) :=
    by simpa only [Functor.uncurry_obj_map, Category.assoc] using derivedCurryIso_natural X k l m
  -- that square, transported by derived global sections and degree-zero cohomology
  have hmid := congrArg (fun z => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
    ((derivedModuleGlobalSections X).map z)) hcurry
  simp only [Functor.map_comp] at hmid
  have e1 := derivedSheafHomGlobalSectionsEquiv_naturality_bifunctor X k
    (((derivedSheafHomBifunctor X).map l.op).app M ≫
      ((derivedSheafHomBifunctor X).obj (op L')).map m) w
  have e2 := derivedCurryHomEquiv_globalSections_homologyMap X K' L' M'
    ((derivedSheafHomGlobalSectionsFunctor X).map
      (((k.op, ((derivedSheafHomBifunctor X).map l.op).app M ≫
          ((derivedSheafHomBifunctor X).obj (op L')).map m)) :
        ((op K, ((derivedSheafHomBifunctor X).obj (op L)).obj M) :
            (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
              DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
          (op K', ((derivedSheafHomBifunctor X).obj (op L')).obj M')) w)
  have e3 := derivedCurryHomEquiv_globalSections_homologyMap X K L M w
  have e4 := derivedSheafHomGlobalSectionsEquiv_naturality_bifunctor X
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map k).app L' ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map l) m
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map (derivedCurryIso X K L M).hom) w)
  rw [← e1, e2, e3, ← e4]
  exact congrArg (fun y => derivedSheafHomGlobalSectionsEquiv X
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K').obj L') M' y)
    (ConcreteCategory.congr_hom hmid w)

end AlgebraicGeometry.RingedSite

end
