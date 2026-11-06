module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProduct
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations

/-!
# Right exactness of the external tensor product

Let `X` and `Y` be schemes over `S`. The external tensor product `E ⊠ G` of an `O_X`-module `E`
and an `O_Y`-module `G` is the tensor product of their pullbacks to `X ×_S Y`. This file records
that the construction is functorial and that it carries a pair of epimorphisms to an
epimorphism, which is the way a quotient of `O_X`-modules and a quotient of `O_Y`-modules
produce a quotient on the product.

## Main definitions

* `AlgebraicGeometry.tensorSheafSwap`: the tensor product of modules on a ringed space is
  symmetric.
* `AlgebraicGeometry.externalTensorProductMap`: the map of external tensor products induced by
  a map on each factor.

## Main results

* `AlgebraicGeometry.tensorSheafMap_epi_right`: tensoring on a ringed space is right exact in
  the second variable. That a pair of epimorphisms goes to an epimorphism is
  `Stacks.SheafOfModules.TensorPresentations.tensorSheafMap_epi_of_epi_of_epi` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations`, imported here.
* `AlgebraicGeometry.externalTensorProductMap_epi`: the external tensor product of two
  epimorphisms is an epimorphism.

## Implementation notes

Right exactness of the tensor product of modules on a ringed space is available in the first
variable only (`AlgebraicGeometry.SheafOfModules.tensorSheafMap_epi`, Tag 01CC). The second
variable is obtained from it by symmetry rather than by repeating the stalkwise argument, and
the symmetry is itself obtained by sheafifying the braiding of the objectwise tensor product of
presheaves of modules: `Stacks.SheafOfModules.TensorStalkRingedSpace.presheafTensor` is
definitionally Mathlib's monoidal
tensor product of presheaves of modules, which is symmetric, and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` is its sheafification.

## References

* [Stacks Project, Tag 01CC](https://stacks.math.columbia.edu/tag/01CC)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry

attribute [local implicit_reducible] Scheme.Modules

section RingedSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local implicit_reducible] structureSheafRing

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The objectwise tensor product of presheaves of `O_X`-modules, as Mathlib's monoidal
structure. It is definitionally `Stacks.SheafOfModules.TensorStalkRingedSpace.presheafTensor`. -/
noncomputable local instance presheafOfModulesMonoidal :
    MonoidalCategory (PresheafOfModules.{u} (O X)) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

/-- The objectwise tensor product of presheaves of `O_X`-modules is symmetric. -/
noncomputable local instance presheafOfModulesSymmetric :
    SymmetricCategory (PresheafOfModules.{u} (O X)) :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)

/-- **The same two structures, at the spelling `F.val` carries.** A sheaf of modules over
`structureSheafRing X` has `F.val : PresheafOfModules (structureSheafRing X).obj`, and a goal is
keyed into the typeclass discrimination tree with only `@[reducible]` definitions unfolded;
`structureSheafRing` is `@[instance_reducible]`, so the two instances above — keyed on
`O X = X.presheaf ⋙ forget₂ CommRingCat RingCat` — are not retrieved there, and the tensor
product of the structure that is retrieved is not `presheafTensor`.  The two presheaves of
rings are equal by `rfl`. -/
@[instance_reducible]
noncomputable local instance presheafOfModulesMonoidal' :
    MonoidalCategory (PresheafOfModules.{u} (structureSheafRing X).obj) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

@[instance_reducible]
noncomputable local instance presheafOfModulesSymmetric' :
    SymmetricCategory (PresheafOfModules.{u} (structureSheafRing X).obj) :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)

/-- The symmetry of the tensor product of modules on a ringed space, obtained by sheafifying
the braiding of the objectwise tensor product of presheaves of modules. -/
noncomputable def tensorSheafSwap (F G : SheafOfModules.{u} (structureSheafRing X)) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩)).obj (F, G) ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩)).obj (G, F) :=
  (sheafifyFunctor X).mapIso (β_ F.val G.val)

/-- The symmetry of the tensor product is natural: swapping the two factors exchanges the two
maps inducing a map of tensor products. -/
theorem tensorSheafSwap_naturality
    {F F' G G' : SheafOfModules.{u} (structureSheafRing X)} (φ : F ⟶ F') (ψ : G ⟶ G') :
    (tensorSheafSwap X F G).hom ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((ψ, φ) : (G, F) ⟶ (G', F')))
      = ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((φ, ψ) : (F, G) ⟶ (F', G'))) ≫
        (tensorSheafSwap X F' G').hom := by
  refine (congrArg (fun morphism => (tensorSheafSwap X F G).hom ≫ morphism)
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩ ψ φ)).trans ?_
  refine Eq.trans ?_ (congrArg (fun morphism => morphism ≫
      (tensorSheafSwap X F' G').hom)
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩ φ ψ).symm)
  exact ((sheafifyFunctor X).map_comp (β_ F.val G.val).hom
    (PresheafOfModules.tensorHom ψ.val φ.val)).symm.trans
      ((congrArg (sheafifyFunctor X).map
        (BraidedCategory.braiding_naturality φ.val ψ.val).symm).trans
        ((sheafifyFunctor X).map_comp (PresheafOfModules.tensorHom φ.val ψ.val)
          (β_ F'.val G'.val).hom))

/-- Maps of tensor products compose factorwise. -/
theorem tensorSheafMap_comp_tensorSheafMap
    {A B C D E F : SheafOfModules.{u} (structureSheafRing X)}
    (a : A ⟶ B) (b : B ⟶ C) (c : D ⟶ E) (d : E ⟶ F) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((a, c) : (A, D) ⟶ (B, E))) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((b, d) : (B, E) ⟶ (C, F))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((a ≫ b), (c ≫ d)) : (A, D) ⟶ (C, F))) := by
  exact ((Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩)).map_comp
    ((a, c) : (A, D) ⟶ (B, E)) ((b, d) : (B, E) ⟶ (C, F))).symm

/-- Tensoring an epimorphism of `O_X`-modules on the left by an `O_X`-module gives an
epimorphism. This is Tag 01CC in the second variable. -/
@[stacks 01CC "exactness at the right term, second variable"]
theorem tensorSheafMap_epi_right {G G' : SheafOfModules.{u} (structureSheafRing X)}
    (F : SheafOfModules.{u} (structureSheafRing X)) (ψ : G ⟶ G') [Epi ψ] :
    Epi (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 F), ψ) : (F, G) ⟶ (F, G')))) := by
  have : Epi (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((ψ, (𝟙 F)) : (G, F) ⟶ (G', F)))) :=
    AlgebraicGeometry.SheafOfModules.tensorSheafMap_epi (X := X) F ψ
  have hfac : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 F), ψ) : (F, G) ⟶ (F, G'))) =
      ((tensorSheafSwap X F G).hom ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map ((ψ, (𝟙 F)) : (G, F) ⟶ (G', F)))) ≫
        (tensorSheafSwap X F G').inv := by
    rw [tensorSheafSwap_naturality X (𝟙 F) ψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfac]
  exact epi_comp' (epi_comp' inferInstance this) inferInstance

end RingedSpace

section Scheme

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- Pullback of modules along a morphism of schemes is a left adjoint, so it preserves
epimorphisms. -/
instance modulesPullback_preservesEpimorphisms {Z W : Scheme.{u}} (h : Z ⟶ W) :
    (Scheme.Modules.pullback h).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction h)

/-- The map of external tensor products induced by a map of `O_X`-modules and a map of
`O_Y`-modules. -/
noncomputable abbrev externalTensorProductMap {E E' : X.Modules} {G G' : Y.Modules}
    (φ : E ⟶ E') (ψ : G ⟶ G') :
    externalTensorProduct f g E G ⟶ externalTensorProduct f g E' G' :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(pullback f g).toRingedSpace.presheaf, (pullback f g).toRingedSpace.IsSheaf⟩)).map
      (X := ((Scheme.Modules.pullback (pullback.fst f g)).obj E,
        (Scheme.Modules.pullback (pullback.snd f g)).obj G))
      (Y := ((Scheme.Modules.pullback (pullback.fst f g)).obj E',
        (Scheme.Modules.pullback (pullback.snd f g)).obj G'))
      (((Scheme.Modules.pullback (pullback.fst f g)).map φ,
        (Scheme.Modules.pullback (pullback.snd f g)).map ψ) :
        ((Scheme.Modules.pullback (pullback.fst f g)).obj E,
          (Scheme.Modules.pullback (pullback.snd f g)).obj G) ⟶
        ((Scheme.Modules.pullback (pullback.fst f g)).obj E',
          (Scheme.Modules.pullback (pullback.snd f g)).obj G'))

/-- The external tensor product of two epimorphisms is an epimorphism: a quotient of an
`O_X`-module and a quotient of an `O_Y`-module give a quotient of their external tensor
product on `X ×_S Y`. -/
theorem externalTensorProductMap_epi {E E' : X.Modules} {G G' : Y.Modules}
    (φ : E ⟶ E') (ψ : G ⟶ G') [Epi φ] [Epi ψ] :
    Epi (externalTensorProductMap f g φ ψ) := by
  exact @Stacks.SheafOfModules.TensorPresentations.tensorSheafMap_epi_of_epi_of_epi
    (pullback f g).toRingedSpace _ _ _ _ _ _ ((modulesPullback_preservesEpimorphisms _).preserves φ)
    ((modulesPullback_preservesEpimorphisms _).preserves ψ)

end Scheme

end AlgebraicGeometry
