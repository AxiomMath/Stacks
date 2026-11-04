module

public import
  StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomCompMap
import StacksCore.Tactic.StacksAttribute

/-!
# The composition law for the canonical map of Stacks 0GMX, with the composite supplied as data

Let `φ : X ⟶ Y` and `ψ : Y ⟶ Z` be morphisms of ringed topoi between the topoi of three ringed
sites. The composite is supplied as data: a third morphism `χ : X ⟶ Z` together with a comparison
`τ` of the geometric direct images carrying the composite structure map to the structure map of
`χ`. This is the form in which `Stacks.SheafOfModules.pullbackTensorIso_inv_app_comp`, the
composition law of Stacks 03EL, is stated, and
`AlgebraicGeometry.RingedToposHom.toModulesHomPushforwardIso` together with
`AlgebraicGeometry.RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso` is the instance of
that data belonging to the composite `ψ ∘ φ`.

This file proves the composition law of Stacks 0GMX in this form; the pair `(χ, τ)` is a
2-morphism from the composite to `χ`, so the law also expresses the invariance of the canonical
map under 2-isomorphisms of morphisms of ringed topoi. The law at the composite itself is
`Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_comp`.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.toposPullbackCompComparisonOf` and
  `Stacks.SheafOfModules.InternalHom.toposPullbackCompComparisonInvOf`: the comparisons
  `χ^*A ⟶ φ^*ψ^*A` and `φ^*ψ^*A ⟶ χ^*A` of pullbacks attached to `(χ, τ)`.

## Main results

* `Stacks.SheafOfModules.InternalHom.toposPullbackCompIsoOf_inv_app_naturality`: the comparison
  of pullbacks attached to `(χ, τ)` is natural past a morphism into the middle pullback, and the
  same at the inverse comparison of Stacks 03EL.
* `Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_compOf`: **the composition law
  for the canonical map of Stacks 0GMX, with the composite supplied as data.**

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Sheaves.RingedToposModules (fSharpSet fSharpSetComp pullbackModulesCompIso)

namespace Stacks.SheafOfModules.InternalHom

universe u

section CompData

variable {X Y Z : RingedSite.{u, u, u}}
  (φ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Y))
  (ψ : RingedToposHom (RingedSite.ringedTopos Y) (RingedSite.ringedTopos Z))
  (χ : RingedToposHom (RingedSite.ringedTopos X) (RingedSite.ringedTopos Z))
  (τ : φ.toModulesHom.toToposHom.pushforward ⋙ ψ.toModulesHom.toToposHom.pushforward ≅
      χ.toModulesHom.toToposHom.pushforward)
  (hτ : fSharpSetComp φ.toModulesHom ψ.toModulesHom ≫ τ.hom.app _ =
    fSharpSet χ.toModulesHom)

/-- The comparison `χ^*A ⟶ φ^*ψ^*A` of pullbacks of sheaves of modules attached to a comparison
of direct images, with the two pullbacks applied in turn. -/
def toposPullbackCompComparisonOf (A : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    (χ.toModulesHom.pullbackModules).obj A ⟶
      (φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj A) :=
  (pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom τ hτ).hom.app A

/-- The comparison `φ^*ψ^*A ⟶ χ^*A` attached to a comparison of direct images. -/
def toposPullbackCompComparisonInvOf (A : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    (φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj A) ⟶
      (χ.toModulesHom.pullbackModules).obj A :=
  (pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom τ hτ).inv.app A

/-- **The comparison of pullbacks attached to `(χ, τ)` is natural, past a morphism into the
middle pullback.** Pulling back `p ≫ ψ^*h` along `φ` and then applying the comparison is the
pullback of `p` followed by the comparison and `χ^*h`. -/
theorem toposPullbackCompIsoOf_inv_app_naturality
    {A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O)}
    {W : SheafOfModules.{u} (Tensor.ringSheaf Y.O)}
    (p : W ⟶ (toposPullback ψ).obj A) (h : A ⟶ B) :
    (toposPullback φ).map (p ≫ (toposPullback ψ).map h) ≫
        toposPullbackCompComparisonInvOf φ ψ χ τ hτ B =
      (toposPullback φ).map p ≫
        (pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom
            τ hτ).inv.app A ≫
          (χ.toModulesHom.pullbackModules).map h :=
  by
  rw [Functor.map_comp, Category.assoc]
  exact congrArg _ ((pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom
    τ hτ).inv.naturality h)

/-- `toposPullbackCompIsoOf_inv_app_naturality` at the inverse comparison of Stacks 03EL, which
is the morphism into the middle pullback that the canonical map of Stacks 0GMX supplies. -/
theorem toposPullbackCompIsoOf_inv_app_naturality_pullbackTensorIso
    (A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O))
    {T : SheafOfModules.{u} (Tensor.ringSheaf Z.O)}
    (h : ((sheafTensor Z.O).obj A).obj B ⟶ T) :
    (toposPullback φ).map
          ((pullbackTensorIso ψ.toModulesHom).inv.app (A, B) ≫ (toposPullback ψ).map h) ≫
        toposPullbackCompComparisonInvOf φ ψ χ τ hτ T =
      (toposPullback φ).map ((pullbackTensorIso ψ.toModulesHom).inv.app (A, B)) ≫
        (pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom τ hτ).inv.app
            (((sheafTensor Z.O).obj A).obj B) ≫
          (χ.toModulesHom.pullbackModules).map h :=
  toposPullbackCompIsoOf_inv_app_naturality φ ψ χ τ hτ
    (A := ((sheafTensor Z.O).obj A).obj B) (B := T)
    ((pullbackTensorIso ψ.toModulesHom).inv.app (A, B)) h

/-- The tensor product of the two comparisons of pullbacks attached to `(χ, τ)`, followed by the
tensor product of the two inverse comparisons, is the identity. -/
theorem tensorSheafBifunctor_map_toposPullbackCompComparisonOf_comp_inv
    (A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (Prod.mkHom (toposPullbackCompComparisonOf φ ψ χ τ hτ A)
            (toposPullbackCompComparisonOf φ ψ χ τ hτ B)) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (((pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom
                τ hτ).inv.app A,
            (pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom
                τ hτ).inv.app B) :
            (((φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj A),
              (φ.toModulesHom.pullbackModules).obj
                ((ψ.toModulesHom.pullbackModules).obj B)) :
              SheafOfModules.{u} (Tensor.ringSheaf X.O) ×
                SheafOfModules.{u} (Tensor.ringSheaf X.O)) ⟶
            ((χ.toModulesHom.pullbackModules).obj A,
              (χ.toModulesHom.pullbackModules).obj B)) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp]
  refine Eq.trans (congrArg _ ?_) (CategoryTheory.Functor.map_id _ _)
  exact Prod.hom_ext
    ((pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom τ hτ).hom_inv_id_app A)
    ((pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom τ hτ).hom_inv_id_app B)

/-- The composition law of Stacks 03EL with the tensor product of the comparisons of pullbacks
cancelled off it, for a composite supplied as data. -/
private theorem pullbackTensorIso_inv_app_compOf_cancel
    (A B : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
          (Prod.mkHom (toposPullbackCompComparisonOf φ ψ χ τ hτ A)
            (toposPullbackCompComparisonOf φ ψ χ τ hτ B)) ≫
        (pullbackTensorIso φ.toModulesHom).inv.app
          ((toposPullback ψ).obj A, (toposPullback ψ).obj B) ≫
        (toposPullback φ).map ((pullbackTensorIso ψ.toModulesHom).inv.app (A, B)) ≫
        (pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom χ.toModulesHom τ hτ).inv.app
            (((sheafTensor Z.O).obj A).obj B) =
      (pullbackTensorIso χ.toModulesHom).inv.app (A, B) :=
  cancelWhisker
    (tensorSheafBifunctor_map_toposPullbackCompComparisonOf_comp_inv φ ψ χ τ hτ A B)
    (pullbackTensorIso_inv_app_comp φ.toModulesHom ψ.toModulesHom χ.toModulesHom τ hτ A B)

/-- **The canonical map is compatible with composition, with the composite supplied as
data.** Let `φ : X ⟶ Y` and `ψ : Y ⟶ Z` be morphisms of ringed topoi between the
topoi of three ringed sites, let `χ : X ⟶ Z` play the role of their composite and let `τ` be a
comparison of the geometric direct images carrying the composite structure map to the structure
map of `χ`. Then the canonical map

`χ^* Hom_{O_Z}(F, G) ⟶ Hom_{O_X}(χ^*F, χ^*G)`

is the canonical map of `ψ` pulled back along `φ`, followed by the canonical map of `φ`, read
through the comparison of pullbacks attached to `(χ, τ)` at `Hom_{O_Z}(F, G)`, at the source of
the internal Hom sheaf — through `internalHomPre`, the comparison in the first variable — and at
its target. -/
@[stacks 0GMX "compatibility of the canonical map with composition, for a composite given as
data"]
theorem toposPullbackInternalHomMap_compOf
    (F G : SheafOfModules.{u} (Tensor.ringSheaf Z.O)) :
    toposPullbackInternalHomMap χ F G =
      toposPullbackCompComparisonOf φ ψ χ τ hτ ((internalHomSecondFunctor Z.J Z.O F).obj G) ≫
        (toposPullback φ).map (toposPullbackInternalHomMap ψ F G) ≫
          toposPullbackInternalHomMap φ ((toposPullback ψ).obj F) ((toposPullback ψ).obj G) ≫
            (internalHomPre X.O (toposPullbackCompComparisonOf φ ψ χ τ hτ F)).app
                ((toposPullback φ).obj ((toposPullback ψ).obj G)) ≫
              (internalHomSecondFunctor X.J X.O ((toposPullback χ).obj F)).map
                (toposPullbackCompComparisonInvOf φ ψ χ τ hτ G) := by
  have hP := sheafTensor_exchange_three X.O
    (toposPullbackCompComparisonOf φ ψ χ τ hτ ((internalHomSecondFunctor Z.J Z.O F).obj G))
    ((toposPullback φ).map (toposPullbackInternalHomMap ψ F G))
    (toposPullbackCompComparisonOf φ ψ χ τ hτ F)
  have hm := toposPullback_tensorEvaluation φ
    (A := (toposPullback ψ).obj ((internalHomSecondFunctor Z.J Z.O F).obj G))
    (toposPullbackInternalHomMap ψ F G)
  have hnat := toposPullbackCompIsoOf_inv_app_naturality_pullbackTensorIso φ ψ χ τ hτ
    ((internalHomSecondFunctor Z.J Z.O F).obj G) F (internalHomEvaluation Z.O F G)
  have hvx₀ := congrArg (fun z : (Functor.prod (toposPullback ψ) (toposPullback ψ) ⋙
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj
            ((internalHomSecondFunctor Z.J Z.O F).obj G, F) ⟶ (toposPullback ψ).obj G ↦
        (toposPullback φ).map z ≫ toposPullbackCompComparisonInvOf φ ψ χ τ hτ G)
      ((tensorEvaluation_toposPullbackInternalHomMap ψ F G).trans
        (toposPullbackEvaluation_eq ψ F G))
  have hvx := hvx₀.trans hnat
  have hkey := pullbackTensorIso_inv_app_compOf_cancel φ ψ χ τ hτ
    ((internalHomSecondFunctor Z.J Z.O F).obj G) F
  have hfin := toposPullbackEvaluationExchange hP hm hvx hkey
  apply tensorEvaluation_injective X.O ((toposPullback χ).obj F) ((toposPullback χ).obj G)
  rw [tensorEvaluation_toposPullbackInternalHomMap χ F G,
    toposPullbackEvaluation_eq χ F G,
    tensorEvaluation_comp, tensorEvaluation_comp,
    tensorEvaluation_comp_internalHomPre_comp_map,
    tensorEvaluation_toposPullbackInternalHomMap]
  exact hfin.symm

end CompData

end Stacks.SheafOfModules.InternalHom

end
