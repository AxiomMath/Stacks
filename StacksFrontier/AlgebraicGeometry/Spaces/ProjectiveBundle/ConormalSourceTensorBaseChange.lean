module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SpaceBaseDescentTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourcePointBaseChange
public import StacksFrontier.CategoryTheory.BifunctorBaseChangeInverse

/-!
# Tensor products and the base change of the Zariski reading

Let `h : T' ⟶ T` be a morphism of test objects, `τ` the morphism of schemes underlying `h` and
`φ` the morphism of represented algebraic spaces.  The base change `τ^* R_T ⟶ R_{T'} φ^*` of the
Zariski reading is monoidal on quasi-coherent modules when it intertwines the Zariski reading
tensor isomorphisms with Stacks 01CD for `τ` and Stacks 03EL for `φ`.  This file records that
property as a proposition, in the spelling of the tensor product sheaf of the structure presheaf
used by Stacks 01CD, together with the identification of the monoidal tensor product of the
modules on a scheme with that tensor product sheaf, and the naturality of the base change in the
spelling of the pullback of modules.

## Main results

* `AlgebraicGeometry.Space.monoidalTensorSheafTensorIso`: the monoidal tensor product of the
  modules on a scheme is the tensor product sheaf of its structure presheaf.
* `AlgebraicGeometry.Space.ZariskiReadingPullbackTensorCompat`: the monoidality of the base
  change of the Zariski reading, as a proposition.
* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_naturality_modulePullback`: naturality of
  that base change, with the image under the pullback of modules written as such.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Bridge

variable (Y : Scheme.{u})

/-- The monoidal tensor product of `Y.Modules` is the tensor product sheaf
`Stacks.SheafOfModules.Tensor.sheafTensor` of the structure presheaf, through the identity. -/
def monoidalTensorSheafTensorIso (M N : Y.Modules) :
    (M ⊗ N : Y.Modules) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
          Y.ringCatSheaf.2⟩).obj M).obj N :=
  Iso.refl _

/-- A naturality square for the monoidal tensor product of `Y.Modules`, read in the tensor
product sheaf of the structure presheaf through `monoidalTensorSheafTensorIso`. -/
theorem monoidalTensorSheafTensorIso_naturality {W W' M N M' N' : Y.Modules} (r : W ⟶ W')
    (z : W ⟶ M ⊗ N) (z' : W' ⟶ M' ⊗ N') (f : M ⟶ M') (g : N ⟶ N')
    (hsq : r ≫ z' = z ≫ (f ⊗ₘ g)) :
    r ≫ z' ≫ (monoidalTensorSheafTensorIso Y M' N').hom =
      (z ≫ (monoidalTensorSheafTensorIso Y M N).hom) ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
            Y.ringCatSheaf.2⟩).map f).app N ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
            Y.ringCatSheaf.2⟩).obj M').map g) := by
  have H : (f ⊗ₘ g) ≫ (monoidalTensorSheafTensorIso Y M' N').hom =
      (monoidalTensorSheafTensorIso Y M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
            Y.ringCatSheaf.2⟩).map f).app N ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
            Y.ringCatSheaf.2⟩).obj M').map g) :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (monoidalTensorSheafTensorIso Y M' N').hom) hsq).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (z ≫ ·) H).trans (Category.assoc _ _ _).symm)

end Bridge

/-- Naturality of the base change of the Zariski reading, with the image of `f` under the
pullback of modules written as such. -/
theorem zariskiReadingPullbackHom_naturality_modulePullback {T T' : BigFppfOver B S hS}
    (h : T' ⟶ T)
    {M N : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2}
    (f : M ⟶ N) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
        ((zariskiReadingFunctor T).map f) ≫ (zariskiReadingPullbackHom h).app N =
      (zariskiReadingPullbackHom h).app M ≫
        (zariskiReadingFunctor T').map
          ((modulePullback B S hS (representedSpaceMap B S hS h)).map f) :=
  (zariskiReadingPullbackHom h).naturality f

section Tensor

variable {T T' : BigFppfOver B S hS} (h : T' ⟶ T)

/-- **The base change of the Zariski reading is monoidal on quasi-coherent modules**: the base
change `τ^*R_T(𝒩 ⊗ ℳ) ⟶ R_{T'}φ^*(𝒩 ⊗ ℳ) ≅ R_{T'}(φ^*𝒩 ⊗ φ^*ℳ)` against the tensor product
reading, Stacks 01CD for `τ` and the base change in both factors. -/
def ZariskiReadingPullbackTensorCompat : Prop :=
  ∀ (N M : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2)
    (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite),
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
        ((zariskiReadingTensorObjIso T N M hN hM).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
            ((zariskiReadingFunctor T).obj N) ((zariskiReadingFunctor T).obj M)).hom) ≫
      (Stacks.RingedSpace.comparisonBifunctorIso
          ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app
        ((zariskiReadingFunctor T).obj N, (zariskiReadingFunctor T).obj M) ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
                (forget₂ CommRingCat RingCat)
                ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩).map
            ((zariskiReadingPullbackHom h).app N)).app
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
            ((zariskiReadingFunctor T).obj M)) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
                (forget₂ CommRingCat RingCat)
                ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩).obj
            ((zariskiReadingFunctor T').obj
              ((modulePullback B S hS (representedSpaceMap B S hS h)).obj N))).map
            ((zariskiReadingPullbackHom h).app M)) =
      (zariskiReadingPullbackHom h).app
          (N ⊗ M : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2) ≫
        (zariskiReadingFunctor T').map
          (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h) N M).hom ≫
        (zariskiReadingTensorObjIso T' _ _
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
            (representedSpaceMap B S hS h) N hN)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
            (representedSpaceMap B S hS h) M hM)).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj N))
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj M))).hom

end Tensor

end AlgebraicGeometry.Space

end
