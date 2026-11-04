module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisGlobalSectionsDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleHomOpExtensionByZero
public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomOpComplexSingle

/-!
# `Γ^Gal(X̄, ℋom^•_ℤ((j_! F)[0], M)) ≅ Γ^Gal(X, ℋom_ℤ(F, j⁻¹ M))`

Let `k` be a field, `k̄/k` a separable algebraic extension and `X` a quasi-compact and
quasi-separated `k`-scheme with a compactification `j : X ⟶ X̄`. For a sheaf `F` of `Λ`-modules
on `X_étale` and a complex `M` of abelian sheaves on `X̄_étale`, the complex of discrete Galois
`Λᵐᵒᵖ`-modules `Γ^Gal(X̄, ℋom^•_ℤ((j_! F)[0], M))` is `Γ^Gal(X, ℋom_ℤ(F, j⁻¹ M))` termwise:
`ℋom^•_ℤ((j_! F)[0], M) ≅ ℋom_ℤ(j_! F, M)` termwise
(`Stacks.AbelianInternalHom.homOpComplexSingleIso`), `ℋom_ℤ(j_! F, -) ≅ j_* ℋom_ℤ(F, j⁻¹ -)`
(`Stacks.EtaleCohomology.homOpExtensionByZeroIso`) and `Γ^Gal(X̄, j_* -) ≅ Γ^Gal(X, -)`
(`Stacks.EtaleCohomology.galoisGlobalSectionsDirectImageIso`).

## Main definitions

* `Stacks.EtaleCohomology.galoisHomOpSingleExtensionByZeroIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.AbelianInternalHom
  Stacks.ConstantSheaf Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- `ℋom_ℤ(G, -)` preserves zero morphisms. -/
local instance homOpFunctor_preservesZeroMorphisms_galoisHomOpSingle (Λ : Type) [Ring Λ]
    {Y : Scheme.{u}} (G : EtaleModules.{u, 0} Λ Y) :
    (homOpFunctor Y.smallEtaleTopology G).PreservesZeroMorphisms :=
  ⟨fun F F' => homOpMap_zero Y.smallEtaleTopology G F F'⟩

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f))

attribute [local instance] quasiCompact_overMk_hom_of_quasiCompact
  quasiSeparated_overMk_hom_of_quasiSeparated

variable [QuasiCompact f] [QuasiSeparated f]

/-- The degree-`i` comparison `ℋom^i_ℤ((j_! F)[0], M) ≅ j_* ℋom_ℤ(F, j⁻¹ M^i)` on `X̄`. -/
def homOpSingleExtensionByZeroXIso (F : EtaleModules.{u, 0} Λ X)
    (M : CochainComplex (Sheaf j.space.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (i : ℤ) :
    homOpComplexX j.space.smallEtaleTopology
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) M i ≅
      (etaleModuleDirectImage.{u, 0} Λᵐᵒᵖ j.immersion).obj
        (homOpSheaf X.smallEtaleTopology F ((etaleRestriction.{u, 0} j.immersion).obj (M.X i))) :=
  homOpComplexSingleXIso _ _ M i ≪≫ homOpExtensionByZeroIso j.immersion Λ F (M.X i)

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The isomorphisms `homOpSingleExtensionByZeroXIso` commute with the differentials of
`ℋom^•_ℤ((j_! F)[0], M)` and of `j_* ℋom_ℤ(F, j⁻¹ M)`. -/
lemma homOpSingleExtensionByZeroXIso_hom_comm (F : EtaleModules.{u, 0} Λ X)
    (M : CochainComplex (Sheaf j.space.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (i : ℤ) :
    (homOpSingleExtensionByZeroXIso Λ j F M i).hom ≫
        (etaleModuleDirectImage.{u, 0} Λᵐᵒᵖ j.immersion).map
          (homOpMap X.smallEtaleTopology F ((etaleRestriction.{u, 0} j.immersion).map
            (M.d i (i + 1)))) =
      homOpComplexD j.space.smallEtaleTopology
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) M i ≫
        (homOpSingleExtensionByZeroXIso Λ j F M (i + 1)).hom := by
  have h := homOpComplexSingleXIso_hom_comm j.space.smallEtaleTopology
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F) M i
  rw [homOpComplex_d] at h
  have hn := homOpExtensionByZeroIso_hom_naturality j.immersion Λ F (M.d i (i + 1))
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hn.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans (Category.assoc _ _ _))))

/-- The degree-wise isomorphisms `Γ^Gal(X̄, ℋom^i_ℤ((j_! F)[0], M)) ≅ Γ^Gal(X, ℋom_ℤ(F, j⁻¹ M^i))`
commute with the differentials. -/
lemma galoisHomOpSingleExtensionByZeroXIso_comm (F : EtaleModules.{u, 0} Λ X)
    (M : CochainComplex (Sheaf j.space.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (i : ℤ) :
    ((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).map
          (homOpSingleExtensionByZeroXIso Λ j F M i).hom ≫
        (galoisGlobalSectionsDirectImageIso Λᵐᵒᵖ kbar j).hom.app _) ≫
        (galoisGlobalSections Λᵐᵒᵖ (Over.mk f) kbar).map
          (homOpMap X.smallEtaleTopology F ((etaleRestriction.{u, 0} j.immersion).map
            (M.d i (i + 1)))) =
      (galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).map
          (homOpComplexD j.space.smallEtaleTopology
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) M i) ≫
        ((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).map
          (homOpSingleExtensionByZeroXIso Λ j F M (i + 1)).hom ≫
          (galoisGlobalSectionsDirectImageIso Λᵐᵒᵖ kbar j).hom.app _) := by
  rw [Category.assoc, ← (galoisGlobalSectionsDirectImageIso Λᵐᵒᵖ kbar j).hom.naturality,
    Functor.comp_map, ← Category.assoc, ← Functor.map_comp,
    homOpSingleExtensionByZeroXIso_hom_comm, Functor.map_comp, Category.assoc]

/-- **`Γ^Gal(X̄, ℋom^•_ℤ((j_! F)[0], M)) ≅ Γ^Gal(X, ℋom_ℤ(F, j⁻¹ M))`**, as complexes of
discrete Galois `Λᵐᵒᵖ`-modules. -/
def galoisHomOpSingleExtensionByZeroIso (F : EtaleModules.{u, 0} Λ X)
    (M : CochainComplex (Sheaf j.space.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    ((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex _).obj
        (homOpComplex j.space.smallEtaleTopology
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) M) ≅
      ((galoisGlobalSections Λᵐᵒᵖ (Over.mk f) kbar).mapHomologicalComplex _).obj
        (((homOpFunctor X.smallEtaleTopology F).mapHomologicalComplex _).obj
          (((etaleRestriction.{u, 0} j.immersion).mapHomologicalComplex _).obj M)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapIso
        (homOpSingleExtensionByZeroXIso Λ j F M i) ≪≫
      (galoisGlobalSectionsDirectImageIso Λᵐᵒᵖ kbar j).app _)
    (by
      rintro i _ rfl
      have h := galoisHomOpSingleExtensionByZeroXIso_comm Λ kbar j F M i
      rw [← homOpComplex_d] at h
      exact h)

/-- The degree-`i` component of `galoisHomOpSingleExtensionByZeroIso`: `Γ^Gal(X̄, -)` of
`ℋom^i_ℤ((j_! F)[0], M) ≅ ℋom_ℤ(j_! F, M^i) ≅ j_* ℋom_ℤ(F, j⁻¹ M^i)`, followed by
`Γ^Gal(X̄, j_* -) ≅ Γ^Gal(X, -)`. -/
lemma galoisHomOpSingleExtensionByZeroIso_hom_f (F : EtaleModules.{u, 0} Λ X)
    (M : CochainComplex (Sheaf j.space.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (i : ℤ) :
    (galoisHomOpSingleExtensionByZeroIso Λ kbar j F M).hom.f i =
      (galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).map
          ((homOpComplexSingleXIso _ _ M i).hom ≫
            (homOpExtensionByZeroIso j.immersion Λ F (M.X i)).hom) ≫
        (galoisGlobalSectionsDirectImageIso Λᵐᵒᵖ kbar j).hom.app _ :=
  rfl

end Stacks.EtaleCohomology

end
