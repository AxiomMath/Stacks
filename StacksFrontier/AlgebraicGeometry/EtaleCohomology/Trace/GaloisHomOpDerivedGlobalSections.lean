module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpSingleExtensionByZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisGlobalSectionsAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeInternalHomAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleHomOpResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicResolutionIso

/-!
# `Γ^Gal(Ȳ, ℋom^•_ℤ((i_! F)[0], K))` computes `RΓ^Gal(Y, ℋom_ℤ(F, ω))`

Let `k` be a field, `k̄/k` a separable algebraic extension and `i : Y ⟶ Ȳ` an open immersion of
quasi-compact and quasi-separated `k`-schemes. Let `F` be a sheaf of `Λ`-modules on `Y_étale` whose
underlying abelian sheaf is that of a locally constant sheaf of `ℤ/n`-modules with finitely
presented values, `ω` a sheaf of `ℤ/n`-modules on `Y` locally constant on an injective module, and
`i_! ω ⟶ K` an injective resolution in sheaves of `ℤ/n`-modules on `Ȳ`. Then the complex of
discrete Galois `Λᵐᵒᵖ`-modules `Γ^Gal(Ȳ, ℋom^•_ℤ((i_! F)[0], K))` represents
`RΓ^Gal(Y, ℋom_ℤ(F, ω))`:

* `Γ^Gal(Ȳ, ℋom^•_ℤ((i_! F)[0], K)) ≅ Γ^Gal(Y, ℋom_ℤ(F, i⁻¹ K))` termwise, by
  `ℋom_ℤ(i_! F, -) ≅ i_* ℋom_ℤ(F, i⁻¹ -)` and `Γ^Gal(Ȳ, i_* -) ≅ Γ^Gal(Y, -)`;
* `ℋom_ℤ(F, ω) ⟶ ℋom_ℤ(F, i⁻¹ K)` is a resolution, `i⁻¹ K` being an injective resolution of
  `i⁻¹ i_! ω = ω`;
* its terms are `Γ^Gal`-acyclic.

## Main definitions

* `Stacks.EtaleCohomology.galoisHomOpSingleExtensionByZeroOverIso`: the termwise isomorphism.
* `Stacks.EtaleCohomology.galoisHomOpDerivedLerayIso`: `Γ^Gal(Y, ℋom_ℤ(F, i⁻¹ K))` computes
  `RΓ^Gal(Y, ℋom_ℤ(F, ω))`.
* `Stacks.EtaleCohomology.galoisHomOpDerivedGlobalSectionsOverIso`: the composite.

## Implementation notes

The propositional instances occurring inside these complexes (the `IsRightCancelAdd ℤ` argument of
`ComplexShape.up ℤ`, the `PreservesZeroMorphisms` instances of `mapHomologicalComplex`,
`HasZeroObject`, `Etale`, ...) are restated below as local instances over the variables of the
file, so that each of their occurrences is a constant applied to variables. Found by instance
search they would be compound proof terms, which the definition elaborator abstracts into auxiliary
lemmas in definition bodies but not in declared types; the kernel then has to compare the complexes
up to these proofs, and does so by unfolding them, beyond its time budget.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.AbelianInternalHom
  Stacks.ConstantSheaf Stacks.Frobenius

universe w₁ w₂ w₃ w₄ u

namespace Stacks.EtaleCohomology

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the object
universe. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galoisHomOpDerived (Λ : Type)
    [Ring Λ] (Z : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Z) :=
  etaleModules_enoughInjectives.{u, 0} Λ Z

/-- `ℋom_ℤ(G, -)` preserves zero morphisms. -/
local instance homOpFunctor_preservesZeroMorphisms_galoisHomOpDerived (Λ : Type) [Ring Λ]
    {Z : Scheme.{u}} (G : EtaleModules.{u, 0} Λ Z) :
    (homOpFunctor Z.smallEtaleTopology G).PreservesZeroMorphisms :=
  ⟨fun F F' => homOpMap_zero Z.smallEtaleTopology G F F'⟩

/-- `forget ∘ ℋom_{ℤ/n}(G', -)` preserves zero morphisms. -/
local instance homAbFunctor_preservesZeroMorphisms_galoisHomOpDerived {Z : Scheme.{u}}
    {n : ℕ} (G' : EtaleModules.{u, 0} (ZMod n) Z) :
    (Stacks.ModuleInternalHom.homAbFunctor (ZMod n) Z.smallEtaleTopology
      G').PreservesZeroMorphisms :=
  inferInstanceAs ((Stacks.ModuleInternalHom.homFunctor Z.smallEtaleTopology (ZMod n) G' ⋙
    etaleModuleForgetAb.{u, 0} (ZMod n) Z).PreservesZeroMorphisms)

/-- Addition on `ℤ` is right cancellative. -/
theorem isRightCancelAdd_int_galoisHomOpDerived : IsRightCancelAdd ℤ := inferInstance

attribute [local instance 10000] isRightCancelAdd_int_galoisHomOpDerived

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar] {Y Yb : Over (Spec (.of k))} (i : Y ⟶ Yb) [IsOpenImmersion i.left]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom]

/-- `G(X)[0] ≅ G(X[0])`, with its source and target spelled as single complexes. -/
def singleObjMapIso {A B : Type*} [Category* A] [Category* B] [HasZeroMorphisms A]
    [HasZeroMorphisms B] [HasZeroObject A] [HasZeroObject B] (G : A ⥤ B)
    [G.PreservesZeroMorphisms] (Z : A) :
    (HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj (G.obj Z) ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj Z) :=
  ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).app Z).symm

/-- The forgetful functor from sheaves of `Λᵐᵒᵖ`-modules on `Y` to abelian sheaves preserves
zero morphisms. -/
local instance (priority := 10000) preservesZeroMorphisms_forgetAbOp_galoisHomOpDerived :
    (etaleModuleForgetAb.{u, 0} Λᵐᵒᵖ Y.left).PreservesZeroMorphisms := inferInstance

/-- The forgetful functor from sheaves of `ℤ/n`-modules on `Y` to abelian sheaves preserves zero
morphisms. -/
local instance (priority := 10000) preservesZeroMorphisms_forgetAbZMod_galoisHomOpDerived {n : ℕ} :
    (etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).PreservesZeroMorphisms := inferInstance

/-- The forgetful functor from sheaves of `ℤ/n`-modules on `Ȳ` to abelian sheaves preserves zero
morphisms. -/
local instance (priority := 10000)
    preservesZeroMorphisms_forgetAbZModBar_galoisHomOpDerived {n : ℕ} :
    (etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).PreservesZeroMorphisms := inferInstance

/-- `ℋom_ℤ(F, -)` on `Y` preserves zero morphisms. -/
local instance (priority := 10000) preservesZeroMorphisms_homOp_galoisHomOpDerived
    (F : EtaleModules.{u, 0} Λ Y.left) :
    (homOpFunctor Y.left.smallEtaleTopology F).PreservesZeroMorphisms := inferInstance

/-- `forget ∘ ℋom_{ℤ/n}(G', -)` on `Y` preserves zero morphisms. -/
local instance (priority := 10000) preservesZeroMorphisms_homAb_galoisHomOpDerived {n : ℕ}
    (G' : EtaleModules.{u, 0} (ZMod n) Y.left) :
    (Stacks.ModuleInternalHom.homAbFunctor (ZMod n) Y.left.smallEtaleTopology
      G').PreservesZeroMorphisms := inferInstance

/-- Restriction `i⁻¹` of sheaves of `ℤ/n`-modules along `i` preserves zero morphisms. -/
local instance (priority := 10000) preservesZeroMorphisms_restriction_galoisHomOpDerived {n : ℕ} :
    (etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
      i.left).PreservesZeroMorphisms := inferInstance

/-- Restriction `i⁻¹` of abelian sheaves along `i` preserves zero morphisms. -/
local instance (priority := 10000) preservesZeroMorphisms_etaleRestriction_galoisHomOpDerived :
    (etaleRestriction.{u, 0} i.left).PreservesZeroMorphisms := inferInstance

/-- `Γ^Gal(Y, -)` preserves zero morphisms. -/
local instance (priority := 10000) preservesZeroMorphisms_galoisGlobalSections_galoisHomOpDerived :
    (galoisGlobalSections Λᵐᵒᵖ Y kbar).PreservesZeroMorphisms := inferInstance

/-- `Γ^Gal(Y, -)` is additive. -/
local instance (priority := 10000) additive_galoisGlobalSections_galoisHomOpDerived :
    (galoisGlobalSections Λᵐᵒᵖ Y kbar).Additive := inferInstance

/-- Sheaves of `Λᵐᵒᵖ`-modules on `Y_étale` have enough injectives. -/
local instance (priority := 10000) enoughInjectives_galoisHomOpDerived :
    EnoughInjectives (EtaleModules.{u, 0} Λᵐᵒᵖ Y.left) := inferInstance

/-- Sheaves of `ℤ/n`-modules on `Y_étale` have a zero object. -/
local instance (priority := 10000) hasZeroObject_zmod_galoisHomOpDerived {n : ℕ} :
    HasZeroObject (EtaleModules.{u, 0} (ZMod n) Y.left) := inferInstance

/-- Sheaves of `ℤ/n`-modules on `Ȳ_étale` have a zero object. -/
local instance (priority := 10000) hasZeroObject_zmodBar_galoisHomOpDerived {n : ℕ} :
    HasZeroObject (EtaleModules.{u, 0} (ZMod n) Yb.left) := inferInstance

/-- Sheaves of `Λᵐᵒᵖ`-modules on `Y_étale` have a zero object. -/
local instance (priority := 10000) hasZeroObject_op_galoisHomOpDerived :
    HasZeroObject (EtaleModules.{u, 0} Λᵐᵒᵖ Y.left) := inferInstance

/-- Abelian sheaves on `Y_étale` have a zero object. -/
local instance (priority := 10000) hasZeroObject_ab_galoisHomOpDerived :
    HasZeroObject (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance

/-- The open immersion `i` is étale. -/
local instance (priority := 10000) etale_galoisHomOpDerived : Etale i.left := inferInstance

/-- `Γ^Gal(Ȳ, -)` preserves zero morphisms. -/
local instance (priority := 10000)
    preservesZeroMorphisms_galoisGlobalSectionsBar_galoisHomOpDerived :
    (galoisGlobalSections Λᵐᵒᵖ Yb kbar).PreservesZeroMorphisms := inferInstance

/-- Sheaves of `Λ`-modules on `Ȳ_étale` have a zero object. -/
local instance (priority := 10000) hasZeroObject_bar_galoisHomOpDerived :
    HasZeroObject (EtaleModules.{u, 0} Λ Yb.left) := inferInstance

/-- Abelian sheaves on `Ȳ_étale` have a zero object. -/
local instance (priority := 10000) hasZeroObject_abBar_galoisHomOpDerived :
    HasZeroObject (Sheaf Yb.left.smallEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance

/-- Sheaves of `Λᵐᵒᵖ`-modules on `Ȳ_étale` have a zero object. -/
local instance (priority := 10000) hasZeroObject_opBar_galoisHomOpDerived :
    HasZeroObject (EtaleModules.{u, 0} Λᵐᵒᵖ Yb.left) := inferInstance

/-! ### `Γ^Gal(Ȳ, ℋom^•_ℤ((i_! F)[0], M)) ≅ Γ^Gal(Y, ℋom_ℤ(F, i⁻¹ M))` -/

/-- The degree-`p` comparison `ℋom^p_ℤ((i_! F)[0], M) ≅ i_* ℋom_ℤ(F, i⁻¹ M^p)` on `Ȳ`. -/
def homOpSingleExtensionByZeroOverXIso (F : EtaleModules.{u, 0} Λ Y.left)
    (M : CochainComplex (Sheaf Yb.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (p : ℤ) :
    homOpComplexX Yb.left.smallEtaleTopology
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ i.left).obj F)) M p ≅
      (etaleModuleDirectImage.{u, 0} Λᵐᵒᵖ i.left).obj
        (homOpSheaf Y.left.smallEtaleTopology F ((etaleRestriction.{u, 0} i.left).obj (M.X p))) :=
  homOpComplexSingleXIso _ _ M p ≪≫ homOpExtensionByZeroIso i.left Λ F (M.X p)

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom] in
/-- The isomorphisms `homOpSingleExtensionByZeroOverXIso` commute with the differentials of
`ℋom^•_ℤ((i_! F)[0], M)` and of `i_* ℋom_ℤ(F, i⁻¹ M)`. -/
lemma homOpSingleExtensionByZeroOverXIso_hom_comm (F : EtaleModules.{u, 0} Λ Y.left)
    (M : CochainComplex (Sheaf Yb.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (p : ℤ) :
    (homOpSingleExtensionByZeroOverXIso Λ i F M p).hom ≫
        (etaleModuleDirectImage.{u, 0} Λᵐᵒᵖ i.left).map
          (homOpMap Y.left.smallEtaleTopology F ((etaleRestriction.{u, 0} i.left).map
            (M.d p (p + 1)))) =
      homOpComplexD Yb.left.smallEtaleTopology
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ i.left).obj F)) M p ≫
        (homOpSingleExtensionByZeroOverXIso Λ i F M (p + 1)).hom := by
  have h := homOpComplexSingleXIso_hom_comm Yb.left.smallEtaleTopology
    ((etaleModuleExtensionByZero.{u, 0} Λ i.left).obj F) M p
  rw [homOpComplex_d] at h
  have hn := homOpExtensionByZeroIso_hom_naturality i.left Λ F (M.d p (p + 1))
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hn.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans (Category.assoc _ _ _))))

/-- After `Γ^Gal(Ȳ, -)` and `Γ^Gal(Ȳ, i_* -) ≅ Γ^Gal(Y, -)`, the isomorphisms
`homOpSingleExtensionByZeroOverXIso` commute with the differentials. -/
lemma galoisHomOpSingleExtensionByZeroOverXIso_comm (F : EtaleModules.{u, 0} Λ Y.left)
    (M : CochainComplex (Sheaf Yb.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (p : ℤ) :
    ((galoisGlobalSections Λᵐᵒᵖ Yb kbar).map
          (homOpSingleExtensionByZeroOverXIso Λ i F M p).hom ≫
        (galoisGlobalSectionsMapDirectImageIso Λᵐᵒᵖ i kbar).hom.app _) ≫
        (galoisGlobalSections Λᵐᵒᵖ Y kbar).map
          (homOpMap Y.left.smallEtaleTopology F ((etaleRestriction.{u, 0} i.left).map
            (M.d p (p + 1)))) =
      (galoisGlobalSections Λᵐᵒᵖ Yb kbar).map
          (homOpComplexD Yb.left.smallEtaleTopology
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              ((etaleModuleExtensionByZero.{u, 0} Λ i.left).obj F)) M p) ≫
        ((galoisGlobalSections Λᵐᵒᵖ Yb kbar).map
          (homOpSingleExtensionByZeroOverXIso Λ i F M (p + 1)).hom ≫
          (galoisGlobalSectionsMapDirectImageIso Λᵐᵒᵖ i kbar).hom.app _) := by
  rw [Category.assoc, ← (galoisGlobalSectionsMapDirectImageIso Λᵐᵒᵖ i kbar).hom.naturality,
    Functor.comp_map, ← Category.assoc, ← Functor.map_comp,
    homOpSingleExtensionByZeroOverXIso_hom_comm, Functor.map_comp, Category.assoc]

set_option maxHeartbeats 1000000 in
-- elaborating the componentwise isomorphism of Galois global sections and its `simp` check
/-- **`Γ^Gal(Ȳ, ℋom^•_ℤ((i_! F)[0], M)) ≅ Γ^Gal(Y, ℋom_ℤ(F, i⁻¹ M))`**, as complexes of
discrete Galois `Λᵐᵒᵖ`-modules. -/
def galoisHomOpSingleExtensionByZeroOverIso (F : EtaleModules.{u, 0} Λ Y.left)
    (M : CochainComplex (Sheaf Yb.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    ((galoisGlobalSections Λᵐᵒᵖ Yb kbar).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (homOpComplex Yb.left.smallEtaleTopology
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ i.left).obj F)) M) ≅
      ((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleRestriction.{u, 0} i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (galoisGlobalSections Λᵐᵒᵖ Yb kbar).mapIso
        (homOpSingleExtensionByZeroOverXIso Λ i F M p) ≪≫
      (galoisGlobalSectionsMapDirectImageIso Λᵐᵒᵖ i kbar).app _)
    (by
      rintro p _ rfl
      simp only [Functor.mapHomologicalComplex_obj_d, homOpComplex_d]
      exact galoisHomOpSingleExtensionByZeroOverXIso_comm Λ kbar i F M p)

/-- The degree-`p` component of `galoisHomOpSingleExtensionByZeroOverIso`: `Γ^Gal(Ȳ, -)` of
`ℋom^p_ℤ((i_! F)[0], M) ≅ ℋom_ℤ(i_! F, M^p) ≅ i_* ℋom_ℤ(F, i⁻¹ M^p)`, followed by
`Γ^Gal(Ȳ, i_* -) ≅ Γ^Gal(Y, -)`. -/
lemma galoisHomOpSingleExtensionByZeroOverIso_hom_f (F : EtaleModules.{u, 0} Λ Y.left)
    (M : CochainComplex (Sheaf Yb.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (p : ℤ) :
    (galoisHomOpSingleExtensionByZeroOverIso Λ kbar i F M).hom.f p =
      (galoisGlobalSections Λᵐᵒᵖ Yb kbar).map
          ((homOpComplexSingleXIso _ _ M p).hom ≫
            (homOpExtensionByZeroIso i.left Λ F (M.X p)).hom) ≫
        (galoisGlobalSectionsMapDirectImageIso Λᵐᵒᵖ i kbar).hom.app _ :=
  rfl

section Derived

variable [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ Y.left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λᵐᵒᵖ k kbar)]
  [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λᵐᵒᵖ (fieldBaseChange Y kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)]
  {n : ℕ} [NeZero n]

/-- The map `ω[0] ⟶ i⁻¹ K₀` on `Y` obtained by restricting `ι₀ : (i_! ω)[0] ⟶ K₀` along `i` and
precomposing with the unit `ω ⟶ i⁻¹ i_! ω`. -/
def restrictionResolution (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ)
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) :
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ω ⟶
      ((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
        i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
        i.left).unit.app ω) ≫
    (singleObjMapIso
      (etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left) _).hom ≫
    ((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
      i.left).mapHomologicalComplex (ComplexShape.up ℤ)).map ι₀

/-- If `ι₀ : (i_! ω)[0] ⟶ K₀` is a quasi-isomorphism, then so is
`restrictionResolution i ω K₀ ι₀`. -/
instance quasiIso_restrictionResolution (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ)
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) [QuasiIso ι₀] :
    QuasiIso (restrictionResolution i ω K₀ ι₀) := by
  unfold restrictionResolution
  infer_instance

/-- `etaleHomOpForgetZModIso` on a complex, with source spelled as nested images. -/
def homOpForgetZModComplexIsoApp (F : EtaleModules.{u, 0} Λ Y.left)
    (G' : EtaleModules.{u, 0} (ZMod n) Y.left) (e : toAb _ F ≅ toAb _ G')
    (L : CochainComplex (EtaleModules.{u, 0} (ZMod n) Y.left) ℤ) :
    ((etaleModuleForgetAb.{u, 0} Λᵐᵒᵖ Y.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L)) ≅
      ((Stacks.ModuleInternalHom.homAbFunctor (ZMod n) Y.left.smallEtaleTopology
        G').mapHomologicalComplex (ComplexShape.up ℤ)).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (etaleHomOpForgetZModIso Λ F G' e).app (L.X p))
    (fun p q _ => ((etaleHomOpForgetZModIso Λ F G' e).hom.naturality (L.d p q)).symm)

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ Y.left)]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)] [NeZero n] in
/-- The isomorphisms `homOpForgetZModComplexIsoApp` are natural in the complex `L`. -/
lemma homOpForgetZModComplexIsoApp_naturality (F : EtaleModules.{u, 0} Λ Y.left)
    (G' : EtaleModules.{u, 0} (ZMod n) Y.left) (e : toAb _ F ≅ toAb _ G')
    {L L' : CochainComplex (EtaleModules.{u, 0} (ZMod n) Y.left) ℤ} (φ : L ⟶ L') :
    ((etaleModuleForgetAb.{u, 0} Λᵐᵒᵖ Y.left).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ)) ≫ (homOpForgetZModComplexIsoApp Λ F G' e L').hom =
      (homOpForgetZModComplexIsoApp Λ F G' e L).hom ≫
        ((Stacks.ModuleInternalHom.homAbFunctor (ZMod n) Y.left.smallEtaleTopology
          G').mapHomologicalComplex (ComplexShape.up ℤ)).map φ :=
  HomologicalComplex.hom_ext _ _ fun p => (etaleHomOpForgetZModIso Λ F G' e).hom.naturality (φ.f p)

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom]
  [NeZero n] in
/-- If every term of `K₀` is injective, then the sections of every term of `i⁻¹ K₀` over every
étale `Y`-scheme are injective `ℤ/n`-modules. -/
lemma moduleInjective_restriction_sections
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ)
    [∀ q, Injective (K₀.X q)] :
    ∀ (m : ℤ) (U : Y.left.Etaleᵒᵖ), Module.Injective (ZMod n)
      (((((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
        i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀).X m).obj.obj U) := fun m U => by
    have : Injective ((((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
        i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀).X m) :=
      injective_etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left (K₀.X m)
    exact moduleInjective_etaleModule_sections (ZMod n) _ U.unop

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ Y.left)]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)] in
/-- Applying `ℋom_ℤ(F, -)` termwise to the resolution `ω[0] ⟶ i⁻¹ K₀` gives a quasi-isomorphism,
for `F` with the underlying abelian sheaf of a locally constant sheaf of `ℤ/n`-modules with
finitely presented values and `ω` locally constant on an injective module. -/
lemma quasiIso_homOpMap_restrictionResolution (F : EtaleModules.{u, 0} Λ Y.left)
    (G' : EtaleModules.{u, 0} (ZMod n) Y.left) (e : toAb _ F ≅ toAb _ G')
    (hG' : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G')
    (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (hω : Stacks.ModuleInternalHom.IsLocallyConstantInjective Y.left.smallEtaleTopology (ZMod n) ω)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) [K₀.IsStrictlyGE 0]
    [∀ q, Injective (K₀.X q)]
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) [QuasiIso ι₀] :
    QuasiIso (((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (restrictionResolution i ω K₀ ι₀))) :=
  by
  have h₀ := Stacks.ModuleInternalHom.quasiIso_homFunctor_map Y.left.smallEtaleTopology (ZMod n) _
    (restrictionResolution i ω K₀ ι₀) (moduleInjective_restriction_sections i K₀) G' hG' hω
  have h : QuasiIso (((Stacks.ModuleInternalHom.homAbFunctor (ZMod n) Y.left.smallEtaleTopology
      G').mapHomologicalComplex (ComplexShape.up ℤ)).map (restrictionResolution i ω K₀ ι₀)) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
      (etaleModuleForgetAb.{u, 0} (ZMod n) Y.left)).2 h₀
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (etaleModuleForgetAb.{u, 0} Λᵐᵒᵖ Y.left)]
  have key := (quasiIso_iff_comp_left
    (homOpForgetZModComplexIsoApp Λ F G' e _).hom _).2 h
  have hsq := homOpForgetZModComplexIsoApp_naturality Λ F G' e (restrictionResolution i ω K₀ ι₀)
  exact (quasiIso_iff_comp_right _ (homOpForgetZModComplexIsoApp Λ F G' e _).hom).1 (hsq ▸ key)

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ Y.left)]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)] in
/-- The map `ℋom_ℤ(F, ω)[0] ⟶ ℋom_ℤ(F, i⁻¹ K₀)` is a quasi-isomorphism, under the hypotheses of
`quasiIso_homOpMap_restrictionResolution`. -/
theorem quasiIso_homOpRestrictionResolution (F : EtaleModules.{u, 0} Λ Y.left)
    (G' : EtaleModules.{u, 0} (ZMod n) Y.left) (e : toAb _ F ≅ toAb _ G')
    (hG' : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G')
    (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (hω : Stacks.ModuleInternalHom.IsLocallyConstantInjective Y.left.smallEtaleTopology (ZMod n) ω)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) [K₀.IsStrictlyGE 0]
    [∀ q, Injective (K₀.X q)]
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) [QuasiIso ι₀] :
    QuasiIso ((singleObjMapIso (homOpFunctor Y.left.smallEtaleTopology F)
        ((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).obj ω)).hom ≫
      ((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (singleObjMapIso (etaleModuleForgetAb.{u, 0} (ZMod n) Y.left) ω).hom ≫
      ((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (restrictionResolution i ω K₀ ι₀))) := by
  have h₃ := quasiIso_homOpMap_restrictionResolution Λ i F G' e hG' ω hω K₀ ι₀
  have h₁ : QuasiIso (singleObjMapIso (homOpFunctor Y.left.smallEtaleTopology F)
        ((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).obj ω)).hom :=
    quasiIso_of_isIso _
  have h₂ : QuasiIso (((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (singleObjMapIso (etaleModuleForgetAb.{u, 0} (ZMod n) Y.left) ω).hom) :=
    quasiIso_of_isIso _
  have h₂₃ := quasiIso_comp _ _ (hφ := h₂) (hφ' := h₃)
  exact quasiIso_comp _ _ (hφ := h₁) (hφ' := h₂₃)

omit [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom] [NeZero n] in
/-- If every term of `K₀` is injective, then every term of `ℋom_ℤ(F, i⁻¹ K₀)` is
`Γ^Gal(Y, -)`-acyclic. -/
lemma rightAcyclic_homOpRestriction (F : EtaleModules.{u, 0} Λ Y.left)
    (G' : EtaleModules.{u, 0} (ZMod n) Y.left) (e : toAb _ F ≅ toAb _ G')
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) [∀ q, Injective (K₀.X q)]
    (m : ℤ) :
    (galoisGlobalSections Λᵐᵒᵖ Y kbar).rightAcyclic
      ((((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
              i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀))).X m) := by
        have := injective_etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
          i.left (K₀.X m)
        exact rightAcyclic_galoisGlobalSections_of_fieldBaseChange Λᵐᵒᵖ Y kbar _
          (rightAcyclic_fieldBaseChange_etaleHomOp Λ Y kbar F G'
            ((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj
              (K₀.X m)) e)

/-- The identification `Γ^Gal(Y, ℋom_ℤ(F, i⁻¹ forget K₀)) ≅ Γ^Gal(Y, ℋom_ℤ(F, forget i⁻¹ K₀))`:
restriction and forgetting the `ℤ/n`-structure commute. -/
def galoisHomOpRestrictionForgetIso (F : EtaleModules.{u, 0} Λ Y.left)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) :
    ((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleRestriction.{u, 0} i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K₀))) ≅
      ((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
              i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀))) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun _ _ _ => (Category.id_comp _).trans (Category.comp_id _).symm)

/-- The resolution map `ℋom_ℤ(F, ω)[0] ⟶ ℋom_ℤ(F, i⁻¹ K₀)`. -/
def homOpRestrictionResolutionMap (F : EtaleModules.{u, 0} Λ Y.left)
    (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ)
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) :
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((homOpFunctor Y.left.smallEtaleTopology F).obj
          ((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).obj ω)) ⟶
      ((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
              i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀)) :=
  (singleObjMapIso (homOpFunctor Y.left.smallEtaleTopology F)
      ((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).obj ω)).hom ≫
      ((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (singleObjMapIso (etaleModuleForgetAb.{u, 0} (ZMod n) Y.left) ω).hom ≫
      ((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (restrictionResolution i ω K₀ ι₀))

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ Y.left)]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)] in
/-- `homOpRestrictionResolutionMap` is a quasi-isomorphism. -/
theorem quasiIso_homOpRestrictionResolutionMap (F : EtaleModules.{u, 0} Λ Y.left)
    (G' : EtaleModules.{u, 0} (ZMod n) Y.left) (e : toAb _ F ≅ toAb _ G')
    (hG' : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G')
    (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (hω : Stacks.ModuleInternalHom.IsLocallyConstantInjective Y.left.smallEtaleTopology (ZMod n) ω)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) [K₀.IsStrictlyGE 0]
    [∀ q, Injective (K₀.X q)]
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) [QuasiIso ι₀] :
    QuasiIso (homOpRestrictionResolutionMap Λ i F ω K₀ ι₀) :=
  quasiIso_homOpRestrictionResolution Λ i F G' e hG' ω hω K₀ ι₀

/-- `Γ^Gal(Y, ℋom_ℤ(F, i⁻¹ K₀)) ≅ RΓ^Gal(Y, ℋom_ℤ(F, ω))`, computed on the acyclic resolution. -/
def galoisHomOpDerivedLerayIso (F : EtaleModules.{u, 0} Λ Y.left)
    (G' : EtaleModules.{u, 0} (ZMod n) Y.left) (e : toAb _ F ≅ toAb _ G')
    (hG' : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G')
    (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (hω : Stacks.ModuleInternalHom.IsLocallyConstantInjective Y.left.smallEtaleTopology (ZMod n) ω)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) [K₀.IsStrictlyGE 0]
    [∀ q, Injective (K₀.X q)]
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) [QuasiIso ι₀] :
    DerivedCategory.Q.obj (((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((homOpFunctor Y.left.smallEtaleTopology F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
              i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀)))) ≅
      DerivedCategory.Plus.ι.obj ((galoisDerivedGlobalSections Λᵐᵒᵖ Y kbar).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((homOpFunctor Y.left.smallEtaleTopology F).obj
            ((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).obj ω)))) :=
  Functor.rightDerivedFunctorPlusSingleIsoOfAcyclic
    (galoisGlobalSections Λᵐᵒᵖ Y kbar)
    ((homOpFunctor Y.left.smallEtaleTopology F).obj
      ((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).obj ω)) _ 0
    (homOpRestrictionResolutionMap Λ i F ω K₀ ι₀)
    (hq := quasiIso_homOpRestrictionResolutionMap Λ i F G' e hG' ω hω K₀ ι₀)
    (rightAcyclic_homOpRestriction Λ kbar i F G' e K₀)

/-- The identification of `ℋom_ℤ(F, -)(ω)` with `ℋom_ℤ(F, ω)` inside `RΓ^Gal(Y, -)`. -/
def galoisDerivedHomOpSingleRespellIso (F : EtaleModules.{u, 0} Λ Y.left)
    (ω : EtaleModules.{u, 0} (ZMod n) Y.left) :
    DerivedCategory.Plus.ι.obj ((galoisDerivedGlobalSections Λᵐᵒᵖ Y kbar).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((homOpFunctor Y.left.smallEtaleTopology F).obj
            ((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).obj ω)))) ≅
      DerivedCategory.Plus.ι.obj ((galoisDerivedGlobalSections Λᵐᵒᵖ Y kbar).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (homOpSheaf Y.left.smallEtaleTopology F (toAb _ ω)))) :=
  Iso.refl _

/-- **`Γ^Gal(Ȳ, ℋom^•_ℤ((i_! F)[0], K)) ≅ RΓ^Gal(Y, ℋom_ℤ(F, ω))`** in the derived category of
discrete Galois `Λᵐᵒᵖ`-modules, for an open immersion `i : Y ⟶ Ȳ` of quasi-compact and
quasi-separated `k`-schemes and an injective resolution `i_! ω ⟶ K` in sheaves of `ℤ/n`-modules
on `Ȳ`. -/
def galoisHomOpDerivedGlobalSectionsOverIso (F : EtaleModules.{u, 0} Λ Y.left)
    (G' : EtaleModules.{u, 0} (ZMod n) Y.left) (e : toAb _ F ≅ toAb _ G')
    (hG' : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G')
    (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (hω : Stacks.ModuleInternalHom.IsLocallyConstantInjective Y.left.smallEtaleTopology (ZMod n) ω)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) [K₀.IsStrictlyGE 0]
    [∀ q, Injective (K₀.X q)]
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) [QuasiIso ι₀] :
    DerivedCategory.Q.obj (((galoisGlobalSections Λᵐᵒᵖ Yb kbar).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (homOpComplex Yb.left.smallEtaleTopology
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ i.left).obj F))
          (((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K₀))) ≅
      DerivedCategory.Plus.ι.obj ((galoisDerivedGlobalSections Λᵐᵒᵖ Y kbar).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (homOpSheaf Y.left.smallEtaleTopology F (toAb _ ω)))) :=
  DerivedCategory.Q.mapIso (galoisHomOpSingleExtensionByZeroOverIso Λ kbar i F
        (((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K₀) ≪≫
      galoisHomOpRestrictionForgetIso Λ kbar i F K₀) ≪≫
    galoisHomOpDerivedLerayIso Λ kbar i F G' e hG' ω hω K₀ ι₀ ≪≫
    galoisDerivedHomOpSingleRespellIso Λ kbar F ω

end Derived

end Stacks.EtaleCohomology

end
