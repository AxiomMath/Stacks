module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafInternalHomNaturality
public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomOpModule

/-!
# `ℋom_ℤ(ℱ_M, ℱ_W) = ℱ_{Hom_ℤ(M, W)}` as sheaves of `Λᵐᵒᵖ`-modules

Let `X` be a connected scheme with a geometric point `x`, `Λ` a finite ring which is a
`ℤ/n`-algebra, `M` a finite `Λ`-module and `W` a finite `ℤ/n`-module, both with continuous actions
of `π₁(X, x)`. The internal Hom `ℋom_ℤ(ℱ_M, ℱ_W)` of abelian sheaves is a sheaf of
`Λᵐᵒᵖ`-modules through the action of `Λ` on `ℱ_M`
(`Stacks.AbelianInternalHom.homOpSheaf`). This file identifies it, as a sheaf of
`Λᵐᵒᵖ`-modules and naturally in `M`, with the sheaf `ℱ_{Hom_ℤ(M, W)}` attached by Tag 0DV5 (3) to
the finite `Λᵐᵒᵖ`-module `Hom_ℤ(M, W)` with the conjugation action
(`Stacks.GroupCohomology.homDualFunctor`).

## Main definitions

* `AlgebraicGeometry.etaleHomOpRepresentationFunctor`: `M ↦ ℋom_ℤ(ℱ_M, ℱ_W)`, as a functor to
  sheaves of `Λᵐᵒᵖ`-modules.
* `AlgebraicGeometry.representationSheafHomOpIso`: `ℋom_ℤ(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}`.
* `AlgebraicGeometry.representationSheafHomOpNatIso`: the same, as a natural isomorphism.
* `AlgebraicGeometry.representationSheafModuleSheafHomIso_naturality`: naturality in `M` of
  `SheafHom_{ℤ/n}(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf Stacks.GroupCohomology
  Stacks.AbelianInternalHom Stacks.ModuleCatLift

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ] (n : ℕ) [NeZero n] [Algebra (ZMod n) Λ]
  (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x))

/-- Multiplication by a scalar on `ℋom_ℤ(G, F)` is precomposition with multiplication by its
`unop` on `G`. -/
lemma sheafScalarEnd_homOpSheaf {C : Type (u + 1)} [Category.{u} C] (K : GrothendieckTopology C)
    {R : Type} [Ring R] (G : Sheaf K (ModuleCat.{u + 1} R)) (F : Sheaf K AddCommGrpCat.{u + 1})
    (a : Rᵐᵒᵖ) :
    sheafScalarEnd Rᵐᵒᵖ K (homOpSheaf K G F) a =
      Stacks.Sites.internalHomSheafPrecomp K (sheafScalarEnd R K G a.unop) F := by
  apply Sheaf.hom_ext
  ext U α
  rfl

/-- **`M ↦ ℋom_ℤ(ℱ_M, ℱ_W)`**, contravariant, from finite `Λ`-modules with a continuous action of
`π₁(X, x)` to sheaves of `Λᵐᵒᵖ`-modules on `X_étale`. -/
def etaleHomOpRepresentationFunctor :
    (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))ᵒᵖ ⥤
      Stacks.EtaleCohomology.EtaleModules.{u, 0} Λᵐᵒᵖ X.1 where
  obj M := homOpSheaf X.1.smallEtaleTopology ((representationSheaf B X x Λ).obj M.unop)
    (toAb X.1.smallEtaleTopology ((representationSheaf B X x (ZMod n)).obj W))
  map f := homOpMapLeft X.1.smallEtaleTopology ((representationSheaf B X x Λ).map f.unop)
    (toAb X.1.smallEtaleTopology ((representationSheaf B X x (ZMod n)).obj W))
  map_id M := (sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_injective (by
    change (internalHomFunctor X.1.smallEtaleTopology _).map ((sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((representationSheaf B X x Λ).map (𝟙 M.unop))).op = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, op_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl)
  map_comp f g := (sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_injective (by
    change (internalHomFunctor X.1.smallEtaleTopology _).map ((sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((representationSheaf B X x Λ).map (g.unop ≫ f.unop))).op = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, op_comp,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl)

/-- **`ℋom_ℤ(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}` as sheaves of `Λᵐᵒᵖ`-modules** on Mathlib's small
étale site: the abelian isomorphism `internalHomRepresentationSheafForgetIso` commutes with the
actions of `Λᵐᵒᵖ` (`internalHomRepresentationSheafForgetIso_smul`). -/
def representationSheafHomOpIso
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (etaleHomOpRepresentationFunctor B X x Λ n W).obj (op M) ≅
      (representationSheaf B X x Λᵐᵒᵖ).obj
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M)) where
  hom := sheafHomOfScalarComm.{u + 1} Λᵐᵒᵖ X.1.smallEtaleTopology
    (internalHomRepresentationSheafForgetIso B X x Λ n M W).hom fun a ↦
      (congrArg (· ≫ (internalHomRepresentationSheafForgetIso B X x Λ n M W).hom)
        (sheafScalarEnd_homOpSheaf X.1.smallEtaleTopology _ _ a)).trans
        (internalHomRepresentationSheafForgetIso_smul B X x Λ n M W a.unop)
  inv := sheafHomOfScalarComm.{u + 1} Λᵐᵒᵖ X.1.smallEtaleTopology
    (internalHomRepresentationSheafForgetIso B X x Λ n M W).inv fun a ↦
      (CommSq.mk ((congrArg (· ≫ (internalHomRepresentationSheafForgetIso B X x Λ n M W).hom)
        (sheafScalarEnd_homOpSheaf X.1.smallEtaleTopology _ _ a)).trans
        (internalHomRepresentationSheafForgetIso_smul B X x Λ n M W a.unop))).vert_inv.w
  hom_inv_id := (sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_injective
    (((sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_comp _ _).trans
      ((internalHomRepresentationSheafForgetIso B X x Λ n M W).hom_inv_id.trans
        ((sheafCompose X.1.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_id
            ((etaleHomOpRepresentationFunctor B X x Λ n W).obj (op M))).symm))
  inv_hom_id := (sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_injective
    (((sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_comp _ _).trans
      ((internalHomRepresentationSheafForgetIso B X x Λ n M W).inv_hom_id.trans
        ((sheafCompose X.1.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_id
            ((representationSheaf B X x Λᵐᵒᵖ).obj
              ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
                (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M)))).symm))

/-- The abelian sheaf map underlying `representationSheafHomOpIso` is
`internalHomRepresentationSheafForgetIso`. -/
lemma sheafCompose_map_representationSheafHomOpIso_hom
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (sheafCompose X.1.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map
        (representationSheafHomOpIso B X x Λ n W M).hom =
      (internalHomRepresentationSheafForgetIso B X x Λ n M W).hom :=
  rfl

/-- **`representationSheafHomOpIso` is natural in `M`.** -/
theorem representationSheafHomOpIso_naturality
    {M M' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (f : M' ⟶ M) :
    (etaleHomOpRepresentationFunctor B X x Λ n W).map f.op ≫
        (representationSheafHomOpIso B X x Λ n W M').hom =
      (representationSheafHomOpIso B X x Λ n W M).hom ≫
        (representationSheaf B X x Λᵐᵒᵖ).map
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W.obj)).map f.op) :=
  (sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_injective
    (((sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_comp _ _).trans
      ((internalHomRepresentationSheafForgetIso_naturality B X x Λ n f W).trans
        ((sheafCompose X.1.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_comp
            (representationSheafHomOpIso B X x Λ n W M).hom
            ((representationSheaf B X x Λᵐᵒᵖ).map
              ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
                (EtaleFundamentalGroup X.1 x)).obj W.obj)).map f.op))).symm))

/-- **`ℋom_ℤ(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}`, naturally in `M`, as sheaves of `Λᵐᵒᵖ`-modules.** -/
def representationSheafHomOpNatIso :
    etaleHomOpRepresentationFunctor B X x Λ n W ≅
      homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj) ⋙ representationSheaf B X x Λᵐᵒᵖ :=
  NatIso.ofComponents (fun M ↦ representationSheafHomOpIso B X x Λ n W M.unop)
    (fun f ↦ representationSheafHomOpIso_naturality B X x Λ n W f.unop)

/-- **`SheafHom_{ℤ/n}(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}` is natural in `M`**
(`AlgebraicGeometry.representationSheafModuleSheafHomIso`), as sheaves of `ℤ/n`-modules. -/
theorem representationSheafModuleSheafHomIso_naturality
    {M M' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (f : M' ⟶ M) :
    moduleSheafHomMap X.1.smallEtaleTopology (ZMod n)
        ((sheafCompose X.1.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1} (algebraMap (ZMod n) Λ))).map
          ((representationSheaf B X x Λ).map f)) (𝟙 _) ≫
        (representationSheafModuleSheafHomIso B X x Λ n M' W).hom =
      (representationSheafModuleSheafHomIso B X x Λ n M W).hom ≫
        (sheafCompose X.1.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1} (algebraMap (ZMod n) Λᵐᵒᵖ))).map
          ((representationSheaf B X x Λᵐᵒᵖ).map
            ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
              (EtaleFundamentalGroup X.1 x)).obj W.obj)).map f.op)) :=
  zmodSheafIsoOfForgetIso_naturality.{u, u + 1} X.1.smallEtaleTopology n _ _ _ _
    ((CommSq.mk (moduleSheafHomForgetIso_naturality.{u, u + 1} X.1.smallEtaleTopology n
      ((sheafCompose X.1.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1} (algebraMap (ZMod n) Λ))).map
        ((representationSheaf B X x Λ).map f))
      ((representationSheaf B X x (ZMod n)).obj W))).vert_comp
      (CommSq.mk (internalHomRepresentationSheafForgetIso_naturality B X x Λ n f W))).w

end AlgebraicGeometry

end
