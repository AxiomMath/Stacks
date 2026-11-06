module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseTrivialConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLevelStalk

/-!
# The stalks of a lisse sheaf, linearly over the coefficient ring

Let `X` be a connected scheme of a big étale site with a geometric point `x̄` and `Λ` a finite
commutative ring. The canonical equivalence `𝔈` of Tag 0DV5 (3) attaches to a finite type locally
constant sheaf of `Λ`-modules `F` a finite `Λ`-module `𝔈(F)` with a continuous action of
`π₁(X, x̄)`; along a path `t` from a geometric point `s̄` to `x̄`, the stalk of `F` at `s̄` is the
underlying abelian group of `𝔈(F)` (`Stacks.EtaleCohomology.finiteLocallyConstantAbelianStalkIso`).
The `Λ`-module structure of `𝔈(F)` is the image under the equivalence of Tag 0DV5 (2) of the
scalar endomorphisms of the underlying abelian sheaf of `F`. This file shows that the stalk
identification is `Λ`-linear, and deduces:

* the stalk of the lisse sheaf `ℱ_P` at `s̄` is `P` as a `Λ`-module, for every finite commutative
  `Λ` (the version over `ℤ/m` is `Stacks.EtaleCohomology.lisseEtaleSheafFiberIso`);
* the lisse sheaf of a finite `Λ`-module with the trivial action is the constant sheaf on that
  module (the version for `ℤ/m` itself is
  `Stacks.EtaleCohomology.nonempty_lisseEtaleSheaf_trivialContinuousModule_iso`).

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `finiteTypeLocallyConstantStalkLinearEquiv`: the stalk of `F` is `𝔈(F)`.
* `lisseSheafStalkLinearEquiv`: the stalk of `ℱ_P` is `P`.
* `lisseEtaleSheafModuleFiberIso`: the same on Mathlib's small étale site.
* `sheafFiber_comp_lisseEtaleSheafModuleFiberIso_hom`: under this identification, an endomorphism
  of the geometric point acts on the stalk of `ℱ_P` as an element of `π₁`.
* `nonempty_lisseEtaleSheaf_iso_constantSheaf_of_trivial`: the lisse sheaf of a module with the
  trivial action is the constant sheaf.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] ModuleCat.hasLimitsOfSize

section Equivariant

variable (Λ : Type) [CommRing Λ] {G : Type (u + 1)} [Group G] [TopologicalSpace G]

/-- An isomorphism of finite `Λ`-modules with continuous `G`-action from an equivariant linear
equivalence of the underlying modules. -/
def finiteTypeContinuousModuleIsoOfLinearEquiv
    {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G}
    (f : P.obj.obj.obj.V ≃ₗ[Λ] Q.obj.obj.obj.V)
    (hf : ∀ (g : G) (v : P.obj.obj.obj.V),
      f ((P.obj.obj.obj.ρ g).asHom.hom v) = (Q.obj.obj.obj.ρ g).asHom.hom (f v)) : P ≅ Q where
  hom := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom f.toLinearMap
      comm := fun g => by
        ext v
        exact hf g v }))
  inv := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom f.symm.toLinearMap
      comm := fun g => by
        ext w
        refine f.injective ?_
        change f (f.symm ((Q.obj.obj.obj.ρ g).asHom.hom w)) =
          f ((P.obj.obj.obj.ρ g).asHom.hom (f.symm w))
        rw [hf, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] }))
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun v => f.symm_apply_apply v
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun w => f.apply_symm_apply w

end Equivariant

section SMul

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Λ : Type) [CommRing Λ]

/-- **Multiplication by `a` on a sheaf of modules over a commutative ring**, as an endomorphism of
sheaves of modules on the site of Stacks 021B. -/
def etaleModuleSheafSMul (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)) (a : Λ) :
    F ⟶ F :=
  ObjectProperty.homMk
    { app := fun _ => ModuleCat.ofHom (a • LinearMap.id)
      naturality := fun _ _ f => by
        ext y
        exact ((F.obj.map f).hom.map_smul a y).symm }

/-- On underlying abelian sheaves, multiplication by `a` is the scalar operation `a` of the
dictionary of Tag 0DV5 (3). -/
theorem sheafCompose_forget₂_map_etaleModuleSheafSMul
    (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)) (a : Λ) :
    (sheafCompose (SmallEtale.topology B S hS)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        (etaleModuleSheafSMul B S hS Λ F a) =
      (moduleSheafScalarFunctor (SmallEtale.topology B S hS) Λ F).map
        (show SingleObj.star Λ ⟶ SingleObj.star Λ from a) := by
  ext U y
  rfl

/-- On the stalk, multiplication by `a` induces multiplication by `a`. -/
theorem etaleStalk_map_etaleModuleSheafSMul_apply (s : GeometricPoint S)
    (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)) (a : Λ)
    (v : (etaleStalkPresheafFunctor B S hS s (ModuleCat.{u + 1} Λ)).obj F.obj) :
    (colim.map (Functor.whiskerLeft ((CategoryOfElements.π (geometricPointFiber B S hS s)).op)
      (etaleModuleSheafSMul B S hS Λ F a).hom)).hom v = a • v :=
  colimMap_smulNatEnd_apply _ a v

end SMul

section Stalk

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [CommRing Λ] [Finite Λ]

local notation "𝔈" => finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ

/-- The finite locally constant abelian sheaf underlying a finite type locally constant sheaf of
`Λ`-modules, as an object of the source of the equivalence of Tag 0DV5 (2). -/
abbrev finiteTypeLocallyConstantAbelian (F : ObjectProperty.FullSubcategory
      (IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2))) :
    (Stacks.ConstantSheaf.isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory :=
  ((Stacks.ConstantSheaf.finiteLocallyConstantModuleSheafScalarActionEquivalence
    (SmallEtale.topology B X.1 X.2) Λ).functor.obj
      ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse.obj F)).obj.obj
    (SingleObj.star Λ)

/-- **The stalk of a finite type locally constant sheaf of `Λ`-modules is the module that Tag 0DV5
(3) attaches to it**, as abelian groups, along a path `t` from `s̄` to `x̄`. -/
def finiteTypeLocallyConstantStalkAddEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (F : ObjectProperty.FullSubcategory
      (IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2))) :
    (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj F.obj.obj ≃+
      ((𝔈).functor.obj F).obj.obj.obj.V :=
  (etaleStalkForget₂Iso B X.1 X.2 s Λ F.obj).addCommGroupIsoToAddEquiv.trans
    ((finiteLocallyConstantAbelianStalkIso B X t).app
      (finiteTypeLocallyConstantAbelian B X Λ F)).addCommGroupIsoToAddEquiv

/-- **The identification of the stalk is `Λ`-linear.** -/
theorem finiteTypeLocallyConstantStalkAddEquiv_smul {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (F : ObjectProperty.FullSubcategory
      (IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2))) (a : Λ)
    (v : (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj F.obj.obj) :
    finiteTypeLocallyConstantStalkAddEquiv B X x Λ t F (a • v) =
      a • finiteTypeLocallyConstantStalkAddEquiv B X x Λ t F v := by
  let φ := etaleModuleSheafSMul B X.1 X.2 Λ F.obj a
  let A := finiteTypeLocallyConstantAbelian B X Λ F
  let G := ((Stacks.ConstantSheaf.finiteLocallyConstantModuleSheafScalarActionEquivalence
    (SmallEtale.topology B X.1 X.2) Λ).functor.obj
      ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse.obj F)).obj
  let α : SingleObj.star Λ ⟶ SingleObj.star Λ := a
  have h0 := etaleStalk_map_etaleModuleSheafSMul_apply B X.1 X.2 Λ s F.obj a v
  have h1 := ConcreteCategory.congr_hom
    (etaleStalkForget₂Iso_hom_naturality B X.1 X.2 s Λ φ) v
  have h2 := ConcreteCategory.congr_hom
    ((finiteLocallyConstantAbelianStalkIso B X t).hom.naturality (G.map α))
    ((etaleStalkForget₂Iso B X.1 X.2 s Λ F.obj).hom v)
  have hφ : (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
      ((sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map φ) =
      (ObjectProperty.ι _ ⋙ abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map (G.map α) := by
    rw [sheafCompose_forget₂_map_etaleModuleSheafSMul]
    rfl
  show (finiteLocallyConstantAbelianStalkIso B X t).hom.app A
      ((etaleStalkForget₂Iso B X.1 X.2 s Λ F.obj).hom (a • v)) =
    a • (show ((𝔈).functor.obj F).obj.obj.obj.V from
      (finiteLocallyConstantAbelianStalkIso B X t).hom.app A
        ((etaleStalkForget₂Iso B X.1 X.2 s Λ F.obj).hom v))
  rw [← h0]
  simp only at h1 h2
  refine (congrArg ((finiteLocallyConstantAbelianStalkIso B X t).hom.app A) h1).trans ?_
  rw [hφ]
  exact h2

/-- **The stalk of a finite type locally constant sheaf of `Λ`-modules is the module that Tag 0DV5
(3) attaches to it**, linearly over `Λ`, along a path `t` from `s̄` to `x̄`. -/
def finiteTypeLocallyConstantStalkLinearEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (F : ObjectProperty.FullSubcategory
      (IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2))) :
    (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj F.obj.obj ≃ₗ[Λ]
      ((𝔈).functor.obj F).obj.obj.obj.V :=
  { finiteTypeLocallyConstantStalkAddEquiv B X x Λ t F with
    map_smul' := finiteTypeLocallyConstantStalkAddEquiv_smul B X x Λ t F }

/-- `finiteTypeLocallyConstantStalkLinearEquiv` agrees with
`finiteTypeLocallyConstantStalkAddEquiv` on elements. -/
theorem finiteTypeLocallyConstantStalkLinearEquiv_apply {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (F : ObjectProperty.FullSubcategory
      (IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2)))
    (v : (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj F.obj.obj) :
    finiteTypeLocallyConstantStalkLinearEquiv B X x Λ t F v =
      finiteTypeLocallyConstantStalkAddEquiv B X x Λ t F v :=
  rfl

/-- The underlying linear equivalence of an isomorphism of finite continuous modules. -/
def finiteTypeContinuousModuleLinearEquiv {G : Type (u + 1)} [Group G] [TopologicalSpace G]
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G} (e : P ≅ P') :
    P.obj.obj.obj.V ≃ₗ[Λ] P'.obj.obj.obj.V :=
  { finiteTypeContinuousModuleAddEquiv Λ e with
    map_smul' := fun a v => e.hom.hom.hom.hom.hom.hom.map_smul a v }

/-- **The stalk at `s̄` of the lisse sheaf `ℱ_P` is `P`, linearly over `Λ`**, along a path `t`
from `s̄` to `x̄`; its underlying additive map is `lisseSheafStalkAddEquiv`. -/
def lisseSheafStalkLinearEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj
      ((lisseSheaf B X x Λ).obj P).obj ≃ₗ[Λ] P.obj.obj.obj.V :=
  (finiteTypeLocallyConstantStalkLinearEquiv B X x Λ t ((𝔈).inverse.obj P)).trans
    (finiteTypeContinuousModuleLinearEquiv Λ ((𝔈).counitIso.app P))

/-- The two descriptions of the abelian stalk identification of `ℱ_P` agree. -/
theorem lisseSheafAbelianStalkAddEquiv_lisseSheafForget₂StalkAddEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (v : (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj
      ((lisseSheaf B X x Λ).obj P).obj) :
    lisseSheafAbelianStalkAddEquiv B X x Λ t P (lisseSheafForget₂StalkAddEquiv B X x Λ s P v) =
      finiteTypeLocallyConstantStalkAddEquiv B X x Λ t ((𝔈).inverse.obj P) v := rfl

omit [Finite Λ] in
/-- `finiteTypeContinuousModuleLinearEquiv` agrees with `finiteTypeContinuousModuleAddEquiv` on
elements. -/
theorem finiteTypeContinuousModuleLinearEquiv_apply {G : Type (u + 1)} [Group G]
    [TopologicalSpace G]
    {P P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G} (e : P ≅ P') (v) :
    finiteTypeContinuousModuleLinearEquiv Λ e v = finiteTypeContinuousModuleAddEquiv Λ e v := rfl

/-- `lisseSheafStalkLinearEquiv` agrees with `lisseSheafStalkAddEquiv` on elements. -/
theorem lisseSheafStalkLinearEquiv_apply {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (v : (etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} Λ)).obj
      ((lisseSheaf B X x Λ).obj P).obj) :
    lisseSheafStalkLinearEquiv B X x Λ t P v = lisseSheafStalkAddEquiv B X x Λ t P v := by
  rw [lisseSheafStalkLinearEquiv, LinearEquiv.trans_apply, lisseSheafStalkAddEquiv,
    AddEquiv.trans_apply, AddEquiv.trans_apply,
    lisseSheafAbelianStalkAddEquiv_lisseSheafForget₂StalkAddEquiv,
    finiteTypeContinuousModuleLinearEquiv_apply, finiteTypeLocallyConstantStalkLinearEquiv_apply]

/-- **The stalk of `ℱ_P` on Mathlib's small étale site is `P`**, as `Λ`-modules, for any finite
commutative ring `Λ`. -/
def lisseEtaleSheafModuleFiberIso {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (Scheme.pointSmallEtale s.hom).sheafFiber.obj ((lisseEtaleSheaf B X x Λ).obj P) ≅
      P.obj.obj.obj.V :=
  (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ s).app ((lisseSheaf B X x Λ).obj P) ≪≫
    (lisseSheafStalkLinearEquiv B X x Λ t P).toModuleIso

/-- **The action of an endomorphism `a` of the geometric point on the stalk of `ℱ_P` on Mathlib's
small étale site is the action of an element of `π₁`**, for any finite commutative ring `Λ`: if
the automorphism `σ` of the fibre functor at `s̄` is precomposition with `a`, it is the action on
`P` of the element that the path `t` transports `σ` to. -/
theorem sheafFiber_comp_lisseEtaleSheafModuleFiberIso_hom {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.asIso.hom = finiteEtaleFiberMap a)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X.1 a)).app
        ((lisseEtaleSheaf B X x Λ).obj P) ≫ (lisseEtaleSheafModuleFiberIso B X x Λ t P).hom =
      (lisseEtaleSheafModuleFiberIso B X x Λ t P).hom ≫
        (P.obj.obj.obj.ρ (etaleFundamentalGroupMulEquiv t σ)).asHom := by
  have R2' := congrArg (fun α => α.app ((lisseSheaf B X x Λ).obj P))
    (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B X Λ a)
  have hsq := moduleCat_iso_hom_comm_of_inv_comm
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X Λ s).app ((lisseSheaf B X x Λ).obj P))
    ((GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X.1 a)).app
      ((lisseEtaleSheaf B X x Λ).obj P))
    ((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} Λ)).app
      ((lisseSheaf B X x Λ).obj P).obj) R2'
  have h3 : (geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} Λ)).app
        ((lisseSheaf B X x Λ).obj P).obj ≫
          (lisseSheafStalkLinearEquiv B X x Λ t P).toModuleIso.hom =
      (lisseSheafStalkLinearEquiv B X x Λ t P).toModuleIso.hom ≫
        (P.obj.obj.obj.ρ (etaleFundamentalGroupMulEquiv t σ)).asHom := by
    ext v
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
      ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
    rw [lisseSheafStalkLinearEquiv_apply, lisseSheafStalkLinearEquiv_apply]
    exact lisseSheafStalkAddEquiv_geometricPointStalkMap B X x Λ t a σ hσ P v
  exact iso_trans_hom_comm _ _ _ _ _ hsq h3

/-- **The lisse sheaf of a finite `Λ`-module with the trivial action of `π₁(X, x̄)` is the constant
sheaf on that module**, as sheaves of `Λ`-modules on Mathlib's small étale site, for any finite
commutative ring `Λ`. -/
theorem nonempty_lisseEtaleSheaf_iso_constantSheaf_of_trivial
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (hP : ∀ g, P.obj.obj.obj.ρ g = 1) :
    Nonempty ((lisseEtaleSheaf B X x Λ).obj P ≅
      etaleModuleConstantSheaf Λ P.obj.obj.obj.V X.1) := by
  let M : ModuleCat.{u + 1} Λ := P.obj.obj.obj.V
  have : Finite (ToType M) := (moduleCat_isFG_iff_finite Λ M).mp P.property
  let c := constantSheafFiniteTypeLocallyConstantModule B X Λ M
  let Qc := (𝔈).functor.obj c
  let f : Qc.obj.obj.obj.V ≃ₗ[Λ] M :=
    (finiteTypeLocallyConstantStalkLinearEquiv B X x Λ (Iso.refl _) c).symm.trans
      (etaleStalkConstantSheafIso B X.1 X.2 x Λ M).toLinearEquiv
  let i : P ≅ Qc := finiteTypeContinuousModuleIsoOfLinearEquiv Λ f.symm fun g v => by
    rw [hP g, rho_eq_one_finiteTypeLocallyConstantModuleSheafEquivalence_constantSheaf B X Λ x M g]
    rfl
  refine ⟨(lisseEtaleSheaf B X x Λ).mapIso i ≪≫
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor.mapIso
      ((ObjectProperty.ι _).mapIso ((𝔈).unitIso.app c).symm ≪≫
        (sheafEquivInverseConstantSheafModuleIso B X Λ M).symm) ≪≫
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).counitIso.app _⟩

end Stalk

end Stacks.EtaleCohomology

end
