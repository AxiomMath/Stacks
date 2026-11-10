module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OfSections

/-!
# Descent of a cartesian system of modules on a simplicial site

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
A cartesian system of the family of modules on the components (modules `N_n` on the component
ringed topoi with isomorphisms `f_φ^*N_m ≅ N_n` satisfying the unit and cocycle laws) is the
system of restrictions of a cartesian sheaf of `O`-modules on the total site.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.systemTotalModule`: the sheaf of `O`-modules descended
  from a cartesian system.
* `CategoryTheory.SimplicialSiteSituation.systemTotalModuleComponentIso`: its restriction to the
  component of degree `n` is `N_n`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.systemTotalModule_isCartesian`: the descended module is
  cartesian.
* `CategoryTheory.SimplicialSiteSituation.componentTransition_systemTotalModule`: its transitions
  are those of the system.

## Implementation notes

The underlying sheaf of sets is the descent, by Stacks 09WF, of the system of underlying sheaves
of sets, whose transitions are the transposes of the direct-image forms of the transitions of
the system. Over an object of the total category, which is the image of an object `U` of the
component of its own degree `n`, its sections are identified with the sections of `N_n` over
`U`, and they are given the module structure of those. Restriction along an arrow of the total
category is then additive and semilinear: it factors through the direct-image transition, which
is a morphism of modules, followed by a map out of the sections of a direct image which is
natural in the sheaf, and so preserves the operations transported along the direct image.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Sheaves.RingedToposModules
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### The system of underlying sheaves of sets -/

section System

variable {S O} (N : (S.modulePseudoFamily O).CartesianSystem)

/-- The module in degree `n` of a cartesian system, as a module on the component ringed
topos. -/
def systemModule (n : SimplexCategory) : (S.componentRingedTopos O n).Modules := N.obj n

/-- The transition of a cartesian system, as an isomorphism of modules on the component ringed
topos. -/
def systemModuleTrans {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.componentModulePullback O φ).obj (systemModule N m) ≅ systemModule N n :=
  N.trans φ

/-- The transition of a cartesian system at an identity simplex map is the unit. -/
theorem systemModuleTrans_id (n : SimplexCategory) :
    (systemModuleTrans N (𝟙 n)).hom =
      (S.transitionPullbackModulesIdIso O n).hom.app (systemModule N n) :=
  N.trans_id n

/-- The transitions of a cartesian system satisfy the cocycle law. -/
theorem systemModuleTrans_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (systemModuleTrans N (ψ ≫ φ)).hom =
      (S.transitionPullbackModulesCompIso O ψ φ).hom.app (systemModule N l) ≫
        (S.componentModulePullback O φ).map (systemModuleTrans N ψ).hom ≫
          (systemModuleTrans N φ).hom :=
  (Iso.inv_comp_eq ((S.transitionPullbackModulesCompIso O ψ φ).app (systemModule N l))).mp
    (N.trans_comp ψ φ)

/-- The underlying sheaf of sets of the module in degree `n` of a cartesian system. -/
def systemModuleSheaf (n : SimplexCategory) : Sheaf (S.componentTopology n) (Type u) :=
  (S.componentModuleSheaf O n).obj (systemModule N n)

/-- The direct-image form `N_m ⟶ (f_φ)_*N_n` of the transition of a cartesian system. -/
def systemModuleDirectTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    systemModule N m ⟶ (S.transitionPushforwardModules O φ).obj (systemModule N n) :=
  (S.transitionPullbackAdj O φ).homEquiv _ _ (systemModuleTrans N φ).hom

/-- The direct-image transition of a cartesian system on underlying sheaves of sets. -/
def systemSheafDirectTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    systemModuleSheaf N m ⟶ (S.transitionMorphism φ).pushforward.obj (systemModuleSheaf N n) :=
  (S.componentModuleSheaf O m).map (systemModuleDirectTransition N φ)

/-- The direct-image transition of a cartesian system at an identity simplex map is the inverse
of the identification `(f_𝟙)_* ≅ 𝟭`. -/
theorem systemModuleDirectTransition_id (n : SimplexCategory) :
    systemModuleDirectTransition N (𝟙 n) =
      (S.transitionPushforwardModulesIdIso O n).inv.app (systemModule N n) := by
  rw [systemModuleDirectTransition, systemModuleTrans_id]
  exact S.homEquiv_transitionPullbackModulesIdIso_hom_app O n (systemModule N n)

/-- The direct-image transitions of a cartesian system satisfy the cocycle law. -/
theorem systemModuleDirectTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    systemModuleDirectTransition N (ψ ≫ φ) =
      systemModuleDirectTransition N ψ ≫
        (S.transitionPushforwardModules O ψ).map (systemModuleDirectTransition N φ) ≫
          (S.transitionPushforwardModulesCompIso O ψ φ).hom.app (systemModule N n) := by
  have hp : (S.transitionPullbackModulesCompIso O ψ φ).hom.app (systemModule N l) =
      (Adjunction.leftAdjointCompIso (S.transitionPullbackAdj O ψ)
        (S.transitionPullbackAdj O φ) (S.transitionPullbackAdj O (ψ ≫ φ))
        (S.transitionPushforwardModulesCompIso O ψ φ)).inv.app (systemModule N l) := by
    rw [S.transitionPullbackModulesCompIso_eq_leftAdjointCompIso]
    rfl
  rw [systemModuleDirectTransition, systemModuleTrans_comp, hp]
  exact Adjunction.homEquiv_leftAdjointCompIso_inv_app (S.transitionPullbackAdj O ψ)
    (S.transitionPullbackAdj O φ) (S.transitionPullbackAdj O (ψ ≫ φ))
    (S.transitionPushforwardModulesCompIso O ψ φ) (systemModuleTrans N ψ).hom
    (systemModuleTrans N φ).hom

/-- The direct-image transition of the underlying system at an identity simplex map is the
inverse of the unit comparison of Stacks 09WE. -/
theorem systemSheafDirectTransition_id (n : SimplexCategory) :
    systemSheafDirectTransition N (𝟙 n) = (S.pushforwardId n).inv.app (systemModuleSheaf N n) := by
  have h : (S.componentModuleSheaf O n).mapIso ((S.transitionPushforwardModulesIdIso O n).app
      (systemModule N n)) = (S.pushforwardId n).app (systemModuleSheaf N n) :=
    Iso.ext (S.componentModuleSheaf_transitionPushforwardModulesIdIso_hom O n (systemModule N n))
  rw [systemSheafDirectTransition, systemModuleDirectTransition_id]
  exact congrArg Iso.inv h

/-- The direct-image transitions of the underlying system satisfy the cocycle law. -/
theorem systemSheafDirectTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    systemSheafDirectTransition N (ψ ≫ φ) =
      systemSheafDirectTransition N ψ ≫
        (S.transitionMorphism ψ).pushforward.map (systemSheafDirectTransition N φ) ≫
          (S.pushforwardCompSymm ψ φ).hom.app (systemModuleSheaf N n) := by
  rw [systemSheafDirectTransition, systemModuleDirectTransition_comp, Functor.map_comp,
    Functor.map_comp, S.componentModuleSheaf_transitionPushforwardModules_map,
    S.componentModuleSheaf_transitionPushforwardModulesCompIso_hom]
  rfl

/-- The inverse-image transition `f_φ⁻¹G_m ⟶ G_n` of the underlying system. -/
def systemSheafTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.obj (systemModuleSheaf N m) ⟶ systemModuleSheaf N n :=
  ((S.transitionMorphism φ).adj.homEquiv _ _).symm (systemSheafDirectTransition N φ)

/-- The inverse-image transition of the underlying system at an identity simplex map is the
canonical unit comparison. -/
theorem systemSheafTransition_id (n : SimplexCategory) :
    systemSheafTransition N (𝟙 n) =
      (canonicalIdentityComparison S n).hom.app (systemModuleSheaf N n) := by
  apply ((S.transitionMorphism (𝟙 n)).adj.homEquiv _ _).injective
  rw [systemSheafTransition, Equiv.apply_symm_apply, systemSheafDirectTransition_id]
  exact (S.homEquiv_canonicalIdentityComparison_hom_app n (systemModuleSheaf N n)).symm

/-- The inverse-image transitions of the underlying system satisfy the cocycle law. -/
theorem systemSheafTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (S.pasteIso ψ φ (systemModuleSheaf N l)).hom ≫ systemSheafTransition N (ψ ≫ φ) =
      (S.transitionMorphism φ).inverseImage.map (systemSheafTransition N ψ) ≫
        systemSheafTransition N φ := by
  have key : systemSheafTransition N (ψ ≫ φ) =
      (canonicalCompositionComparison S ψ φ).hom.app (systemModuleSheaf N l) ≫
        (S.transitionMorphism φ).inverseImage.map (systemSheafTransition N ψ) ≫
          systemSheafTransition N φ := by
    apply ((S.transitionMorphism (ψ ≫ φ)).adj.homEquiv _ _).injective
    rw [S.homEquiv_canonicalCompositionComparison, systemSheafTransition,
      Equiv.apply_symm_apply, systemSheafTransition, Equiv.apply_symm_apply,
      systemSheafTransition, Equiv.apply_symm_apply, systemSheafDirectTransition_comp]
  rw [key, pasteIso, Iso.symm_hom, Iso.app_inv, Iso.inv_hom_id_app_assoc]

/-- The system of sheaves of sets underlying a cartesian system of modules. -/
def systemSheafSystem : SimplicialSheafSystem (componentPseudofunctor S) :=
  S.systemOfFibreTransitions (systemModuleSheaf N) (fun φ => systemSheafTransition N φ)
    (systemSheafTransition_id N) (fun ψ φ => systemSheafTransition_comp N ψ φ)

/-- The sheaf of sets on the total site descended from a cartesian system of modules. -/
def systemTotalSheafOfSets : Sheaf S.totalTopology (Type u) :=
  S.systemTotalSheaf (systemSheafSystem N)

/-- The restriction of the descended sheaf of sets to degree `n` is the underlying sheaf of sets
of `N_n`. -/
def systemTotalRestrictIso (n : SimplexCategory) :
    (S.restrict n).obj (systemTotalSheafOfSets N) ≅ systemModuleSheaf N n :=
  S.restrictIso (systemSheafSystem N) n

/-- The identifications of the restrictions of the descended sheaf of sets carry its
direct-image transitions to those of the system. -/
theorem systemTotalRestrictIso_hom_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (systemTotalRestrictIso N m).hom ≫ systemSheafDirectTransition N φ =
      (S.restrictTransition φ).app (systemTotalSheafOfSets N) ≫
        (S.transitionMorphism φ).pushforward.map (systemTotalRestrictIso N n).hom := by
  have h : S.systemDirectTransition (systemSheafSystem N) φ = systemSheafDirectTransition N φ :=
    ((S.transitionMorphism φ).adj.homEquiv _ _).apply_symm_apply _
  rw [← h]
  exact S.restrictIso_systemDirectTransition (systemSheafSystem N) φ

end System


/-! ### Restriction along an arrow between objects of components -/

section Restriction

variable {S O} (N : (S.modulePseudoFamily O).CartesianSystem)

/-- Restriction of the descended sheaf of sets along an arrow `(n, U) ⟶ (m, V)` of the total
category, read between the sections of `N_m` over `V` and of `N_n` over `U`. -/
def restrictionMap {m n : SimplexCategory} {U : S.component n} {V : S.component m}
    (g : (S.inclusion n).obj U ⟶ (S.inclusion m).obj V)
    (x : (systemModule N m).val.obj (op V)) : (systemModule N n).val.obj (op U) :=
  (systemTotalRestrictIso N n).hom.hom.app (op U)
    ((systemTotalSheafOfSets N).obj.map g.op ((systemTotalRestrictIso N m).inv.hom.app (op V) x))

/-- Restriction along an arrow of the total category is the direct-image transition of the
system followed by a map out of the sections of the direct image which is natural in the
sheaf. -/
theorem restrictionMap_eq {m n : SimplexCategory} {U : S.component n} {V : S.component m}
    (g : (S.inclusion n).obj U ⟶ (S.inclusion m).obj V) (φ : m ⟶ n)
    (ε : (S.transitionMorphism φ).pushforward ⋙
        Sheaf.sectionsFunctor.{u} (S.componentTopology m) (op V) ⟶
          Sheaf.sectionsFunctor (S.componentTopology n) (op U))
    (hε : ∀ H : Sheaf S.totalTopology (Type u),
      H.obj.map g.op = ((S.restrictTransition φ).app H).hom.app (op V) ≫
        ε.app ((S.restrict n).obj H))
    (x : (systemModule N m).val.obj (op V)) :
    restrictionMap N g x =
      ε.app (systemModuleSheaf N n) ((systemSheafDirectTransition N φ).hom.app (op V) x) := by
  have h₁ := congrArg (fun t => t ((systemTotalRestrictIso N m).inv.hom.app (op V) x))
    (hε (systemTotalSheafOfSets N))
  have h₂ := congrArg (fun t => t (((S.restrictTransition φ).app
      (systemTotalSheafOfSets N)).hom.app (op V)
      ((systemTotalRestrictIso N m).inv.hom.app (op V) x)))
    (ε.naturality (systemTotalRestrictIso N n).hom)
  have h₃ := congrArg (fun t => t.hom.app (op V)
      ((systemTotalRestrictIso N m).inv.hom.app (op V) x))
    (systemTotalRestrictIso_hom_comp N φ)
  have h₄ : (systemTotalRestrictIso N m).hom.hom.app (op V)
      ((systemTotalRestrictIso N m).inv.hom.app (op V) x) = x :=
    congrArg (fun t => t.hom.app (op V) x) (systemTotalRestrictIso N m).inv_hom_id
  refine (congrArg ((systemTotalRestrictIso N n).hom.hom.app (op U)) h₁).trans ?_
  refine h₂.symm.trans ?_
  refine congrArg (ε.app (systemModuleSheaf N n)) ?_
  refine h₃.symm.trans ?_
  exact congrArg ((systemSheafDirectTransition N φ).hom.app (op V)) h₄

/-- The ring map of an arrow `(n, U) ⟶ (m, V)` of the total category, read between the
sections of the component structure sheaves. -/
def ringRestriction {m n : SimplexCategory} {U : S.component n} {V : S.component m}
    (g : (S.inclusion n).obj U ⟶ (S.inclusion m).obj V) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O).obj.obj (op V) →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O).obj.obj (op U) :=
  ((S.totalRingSheaf O).obj.map g.op).hom

/-- The direct images of sheaves of sets along the transition morphisms, read on sections,
preserve finite products. -/
instance preservesFiniteProducts_pushforward_comp_sectionsFunctor {m n : SimplexCategory}
    (φ : m ⟶ n) (V : (S.component m)ᵒᵖ) :
    PreservesFiniteProducts ((S.transitionMorphism φ).pushforward ⋙
      Sheaf.sectionsFunctor.{u} (S.componentTopology m) V) := by
  have := (S.transitionMorphism φ).adj.rightAdjoint_preservesLimits.{0, 0}
  infer_instance

/-- Restriction along an arrow of the total category is additive. -/
theorem restrictionMap_add {m n : SimplexCategory} {U : S.component n} {V : S.component m}
    (g : (S.inclusion n).obj U ⟶ (S.inclusion m).obj V) (x y : (systemModule N m).val.obj (op V)) :
    restrictionMap N g (x + y) = restrictionMap N g x + restrictionMap N g y := by
  obtain ⟨φ, ε, hε⟩ := S.exists_restrictTransition_factorization g
  simp only [restrictionMap_eq N g φ ε hε]
  let ε' : (S.transitionRingedToposHom O φ).toModulesHom.toToposHom.pushforward ⋙
      Sheaf.sectionsFunctor (S.componentRingedTopos O m).J (op V) ⟶
        Sheaf.sectionsFunctor (S.componentRingedTopos O n).J (op U) := ε
  let d := (Sheaf.sectionsFunctor (S.componentRingedTopos O m).J (op V)).map
    ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O)).map
        (systemModuleDirectTransition N φ))
  have h₁ : d (x + y) = d x + d y := Sheaf.sectionsFunctor_map_moduleSheafFunctor_map_add
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O)
    (systemModuleDirectTransition N φ) (op V) x y
  have h₂ := (Sheaf.sectionsFunctor_map_moduleAddHom
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O)
    ((S.transitionPushforwardModules O φ).obj (systemModule N n)) (op V) (d x) (d y)).symm
  have h₃ := Stacks.Sheaves.RingedToposModules.moduleAddObj_pushforwardModules
    (S.transitionRingedToposHom O φ).toModulesHom (systemModule N n)
    (Sheaf.sectionsFunctor (S.componentRingedTopos O m).J (op V)) (d x) (d y)
  have h₄ := Sheaf.moduleAddObj_naturality
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)
    (systemModule N n) ε' (d x) (d y)
  have h₅ := Sheaf.sectionsFunctor_map_moduleAddHom
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)
    (systemModule N n) (op U) (ε'.app _ (d x)) (ε'.app _ (d y))
  exact (congrArg (ε'.app (systemModuleSheaf N n)) (h₁.trans (h₂.trans h₃))).trans (h₄.trans h₅)

/-- Restriction along an arrow of the total category is semilinear over the ring map of the
arrow. -/
theorem restrictionMap_smul {m n : SimplexCategory} {U : S.component n} {V : S.component m}
    (g : (S.inclusion n).obj U ⟶ (S.inclusion m).obj V)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O).obj.obj (op V))
    (x : (systemModule N m).val.obj (op V)) :
    restrictionMap N g (r • x) = ringRestriction g r • restrictionMap N g x := by
  obtain ⟨φ, ε, hε⟩ := S.exists_restrictTransition_factorization g
  simp only [restrictionMap_eq N g φ ε hε]
  let ε' : (S.transitionRingedToposHom O φ).toModulesHom.toToposHom.pushforward ⋙
      Sheaf.sectionsFunctor (S.componentRingedTopos O m).J (op V) ⟶
        Sheaf.sectionsFunctor (S.componentRingedTopos O n).J (op U) := ε
  let d := (Sheaf.sectionsFunctor (S.componentRingedTopos O m).J (op V)).map
    ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O)).map
        (systemModuleDirectTransition N φ))
  let r₀ : (Sheaf.sectionsFunctor (S.componentRingedTopos O m).J (op V)).obj
      (Sheaf.ringSheaf.{u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O)) := r
  let r' : ((S.transitionRingedToposHom O φ).toModulesHom.toToposHom.pushforward ⋙
      Sheaf.sectionsFunctor (S.componentRingedTopos O m).J (op V)).obj
        (Sheaf.ringSheaf.{u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :=
    (Sheaf.sectionsFunctor (S.componentRingedTopos O m).J (op V)).map
      ((sheafCompose (S.componentRingedTopos O m).J (forget RingCat.{u})).map
        (S.transitionRingedToposHom O φ).toModulesHom.fSharp) r₀
  have h₁ := Sheaf.sectionsFunctor_map_moduleSheafFunctor_map_smul
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O)
    (systemModuleDirectTransition N φ) (op V) r₀ x
  have h₂ := (Sheaf.sectionsFunctor_map_moduleSMulHom
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O)
    ((S.transitionPushforwardModules O φ).obj (systemModule N n)) (op V) r₀ (d x)).symm
  have h₃ := Stacks.Sheaves.RingedToposModules.moduleSMulObj_pushforwardModules
    (S.transitionRingedToposHom O φ).toModulesHom (systemModule N n)
    (Sheaf.sectionsFunctor (S.componentRingedTopos O m).J (op V)) r₀ (d x)
  have h₄ := Sheaf.moduleSMulObj_naturality
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)
    (systemModule N n) ε' r' (d x)
  have h₅ := Sheaf.sectionsFunctor_map_moduleSMulHom
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)
    (systemModule N n) (op U)
    (ε'.app (Sheaf.ringSheaf.{u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) r')
    (ε'.app _ (d x))
  have h₆ : ε'.app (Sheaf.ringSheaf.{u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) r' =
      (ringRestriction g r : (Sheaf.sectionsFunctor (S.componentRingedTopos O n).J (op U)).obj
        (Sheaf.ringSheaf.{u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O))) :=
    (congrArg (fun t => ε.app _ ((Sheaf.sectionsFunctor (S.componentTopology m) (op V)).map
      t r)) (S.transitionRingedToposHom_fSharpRing_forget O φ)).trans
      (ConcreteCategory.congr_hom (hε (Sheaf.ringSheaf.{u, u, u} (S.totalRingSheaf O))) r).symm
  refine (congrArg (ε'.app (systemModuleSheaf N n)) (h₁.trans (h₂.trans h₃))).trans
    (h₄.trans (h₅.trans ?_))
  exact congrArg (fun t => t • ε'.app (Sheaf.moduleSheaf.{u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O) (systemModule N n))
      (d x)) h₆

end Restriction

/-! ### The sheaf of modules -/

section TotalModule

variable {S O} (N : (S.modulePseudoFamily O).CartesianSystem)

/-- An object of the total category is the image of an object of the component of its own
degree. -/
theorem inclusion_obj_fibre (X : S.totalCategory) :
    (S.inclusion (S.totalObjDegree X)).obj (S.totalObjFibre X) = X :=
  S.inclusion_obj_totalObjFibre X

/-- Applying the isomorphism `systemTotalRestrictIso N k` to a section and then its inverse
returns the section. -/
theorem systemTotalRestrictIso_inv_hom_apply (k : SimplexCategory) (U : S.component k)
    (z : (systemTotalSheafOfSets N).obj.obj (op ((S.inclusion k).obj U))) :
    (systemTotalRestrictIso N k).inv.hom.app (op U)
      ((systemTotalRestrictIso N k).hom.hom.app (op U) z) = z :=
  congrArg (fun t => t.hom.app (op U) z) (systemTotalRestrictIso N k).hom_inv_id

/-- Applying the inverse of `systemTotalRestrictIso N k` to a section and then the isomorphism
returns the section. -/
theorem systemTotalRestrictIso_hom_inv_apply (k : SimplexCategory) (U : S.component k)
    (z : (systemModule N k).val.obj (op U)) :
    (systemTotalRestrictIso N k).hom.hom.app (op U)
      ((systemTotalRestrictIso N k).inv.hom.app (op U) z) = z :=
  congrArg (fun t => t.hom.app (op U) z) (systemTotalRestrictIso N k).inv_hom_id

omit N in
/-- Restricting along an equality of objects and back is the identity. -/
theorem map_eqToHom_map_eqToHom {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Type u) {a b : C}
    (h : a = b) (x : F.obj (op b)) :
    F.map (eqToHom h.symm).op (F.map (eqToHom h).op x) = x := by
  subst h
  simp

omit N in
/-- Restricting back along an equality of objects and then forth is the identity. -/
theorem map_eqToHom_map_eqToHom' {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Type u) {a b : C}
    (h : a = b) (x : F.obj (op a)) :
    F.map (eqToHom h).op (F.map (eqToHom h.symm).op x) = x :=
  map_eqToHom_map_eqToHom F h.symm x

/-- Restriction along `g` conjugated by equalities of objects is restriction along `g` followed by
the equality of the source. -/
private theorem map_eqToHom_comp_map_eqToHom_comp {C D : Type*} [Category* C] [Category* D]
    (F : Cᵒᵖ ⥤ D) {X Y X' Y' : C} (g : Y ⟶ X) (hX : X' = X) (hY : Y' = Y) :
    F.map (eqToHom hX).op ≫ F.map (eqToHom hY ≫ g ≫ eqToHom hX.symm).op =
      F.map g.op ≫ F.map (eqToHom hY).op := by
  subst hX hY
  simp

/-- The sections of the descended sheaf of sets over an object of the total category, identified
with the sections of the module of its degree over the corresponding object of the
component. -/
def sectionsEquiv (X : S.totalCategory) :
    (systemTotalSheafOfSets N).obj.obj (op X) ≃
      (systemModule N (S.totalObjDegree X)).val.obj (op (S.totalObjFibre X)) where
  toFun x := (systemTotalRestrictIso N (S.totalObjDegree X)).hom.hom.app (op (S.totalObjFibre X))
    ((systemTotalSheafOfSets N).obj.map (eqToHom (inclusion_obj_fibre X)).op x)
  invFun z := (systemTotalSheafOfSets N).obj.map (eqToHom (inclusion_obj_fibre X).symm).op
    ((systemTotalRestrictIso N (S.totalObjDegree X)).inv.hom.app (op (S.totalObjFibre X)) z)
  left_inv x :=
    (congrArg ((systemTotalSheafOfSets N).obj.map (eqToHom (inclusion_obj_fibre X).symm).op)
      (systemTotalRestrictIso_inv_hom_apply N _ _ _)).trans
      (map_eqToHom_map_eqToHom (systemTotalSheafOfSets N).obj (inclusion_obj_fibre X) x)
  right_inv z :=
    (congrArg ((systemTotalRestrictIso N (S.totalObjDegree X)).hom.hom.app
      (op (S.totalObjFibre X)))
      (map_eqToHom_map_eqToHom' (systemTotalSheafOfSets N).obj (inclusion_obj_fibre X) _)).trans
      (systemTotalRestrictIso_hom_inv_apply N _ _ z)

/-- The identification of sections commutes with restriction: restriction of the descended sheaf
of sets along an arrow is restriction of the system along the corresponding arrow between
objects of components. -/
theorem sectionsEquiv_map {X Y : S.totalCategory} (g : Y ⟶ X)
    (x : (systemTotalSheafOfSets N).obj.obj (op X)) :
    sectionsEquiv N Y ((systemTotalSheafOfSets N).obj.map g.op x) =
      restrictionMap N (eqToHom (inclusion_obj_fibre Y) ≫ g ≫ eqToHom (inclusion_obj_fibre X).symm)
        (sectionsEquiv N X x) := by
  have h₁ := systemTotalRestrictIso_inv_hom_apply N (S.totalObjDegree X) (S.totalObjFibre X)
    ((systemTotalSheafOfSets N).obj.map (eqToHom (inclusion_obj_fibre X)).op x)
  have h₂ := congrArg (fun t => t x)
    (map_eqToHom_comp_map_eqToHom_comp (systemTotalSheafOfSets N).obj g
      (inclusion_obj_fibre X) (inclusion_obj_fibre Y))
  refine Eq.symm ((congrArg (fun t => (systemTotalRestrictIso N (S.totalObjDegree Y)).hom.hom.app
    (op (S.totalObjFibre Y)) ((systemTotalSheafOfSets N).obj.map (eqToHom (inclusion_obj_fibre Y) ≫
      g ≫ eqToHom (inclusion_obj_fibre X).symm).op t)) h₁).trans ?_)
  exact congrArg _ h₂

/-- The identification of the ring of sections of the total structure sheaf over an object of
the total category with the ring of sections of the component structure sheaf over the
corresponding object of the component. -/
def sectionsRingHom (X : S.totalCategory) :
    (S.totalRingSheaf O).obj.obj (op X) →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf
          (S.componentRingedTopos O (S.totalObjDegree X)).O).obj.obj
        (op (S.totalObjFibre X)) :=
  ((S.totalRingSheaf O).obj.map (eqToHom (inclusion_obj_fibre X)).op).hom

/-- The additive group of sections of the descended sheaf of sets. -/
@[instance_reducible]
def sectionsAddCommGroup (X : S.totalCategory) :
    AddCommGroup ((systemTotalSheafOfSets N).obj.obj (op X)) :=
  (sectionsEquiv N X).addCommGroup

/-- The module of sections of the descended sheaf of sets over the sections of the total
structure sheaf. -/
@[instance_reducible]
def sectionsModule (X : S.totalCategory) :
    letI := sectionsAddCommGroup N X
    Module ((S.totalRingSheaf O).obj.obj (op X)) ((systemTotalSheafOfSets N).obj.obj (op X)) :=
  letI := sectionsAddCommGroup N X
  letI : Module ((S.totalRingSheaf O).obj.obj (op X))
      ((systemModule N (S.totalObjDegree X)).val.obj (op (S.totalObjFibre X))) :=
    Module.compHom _ (sectionsRingHom (O := O) X)
  AddEquiv.module _ (sectionsEquiv N X).addEquiv

attribute [local instance] sectionsAddCommGroup sectionsModule

/-- The identification `sectionsEquiv N X` sends a sum of sections to the sum of their
images. -/
theorem sectionsEquiv_add (X : S.totalCategory) (x y : (systemTotalSheafOfSets N).obj.obj (op X)) :
    sectionsEquiv N X (x + y) = sectionsEquiv N X x + sectionsEquiv N X y :=
  (sectionsEquiv N X).apply_symm_apply _

/-- The identification `sectionsEquiv N X` sends `r • x` to `sectionsRingHom X r` acting on the
image of `x`. -/
theorem sectionsEquiv_smul (X : S.totalCategory) (r : (S.totalRingSheaf O).obj.obj (op X))
    (x : (systemTotalSheafOfSets N).obj.obj (op X)) :
    sectionsEquiv N X (r • x) = sectionsRingHom X r • sectionsEquiv N X x :=
  (sectionsEquiv N X).apply_symm_apply _

/-- The ring maps of the identifications are compatible with restriction. -/
theorem ringRestriction_sectionsRingHom {X Y : S.totalCategory} (g : Y ⟶ X)
    (r : (S.totalRingSheaf O).obj.obj (op X)) :
    ringRestriction (eqToHom (inclusion_obj_fibre Y) ≫ g ≫ eqToHom (inclusion_obj_fibre X).symm)
        (sectionsRingHom X r) =
      sectionsRingHom Y ((S.totalRingSheaf O).obj.map g.op r) := by
  exact congrArg (fun t => t.hom r)
    (map_eqToHom_comp_map_eqToHom_comp (S.totalRingSheaf O).obj g
      (inclusion_obj_fibre X) (inclusion_obj_fibre Y))

/-- Restriction of the descended sheaf of sets is additive. -/
theorem sections_map_add {X Y : S.totalCategory} (g : Y ⟶ X)
    (x y : (systemTotalSheafOfSets N).obj.obj (op X)) :
    (systemTotalSheafOfSets N).obj.map g.op (x + y) =
      (systemTotalSheafOfSets N).obj.map g.op x + (systemTotalSheafOfSets N).obj.map g.op y := by
  apply (sectionsEquiv N Y).injective
  rw [sectionsEquiv_add, sectionsEquiv_map, sectionsEquiv_map, sectionsEquiv_map,
    sectionsEquiv_add, restrictionMap_add]

/-- Restriction of the descended sheaf of sets is semilinear. -/
theorem sections_map_smul {X Y : S.totalCategory} (g : Y ⟶ X)
    (r : (S.totalRingSheaf O).obj.obj (op X)) (x : (systemTotalSheafOfSets N).obj.obj (op X)) :
    (systemTotalSheafOfSets N).obj.map g.op (r • x) =
      (S.totalRingSheaf O).obj.map g.op r • (systemTotalSheafOfSets N).obj.map g.op x := by
  apply (sectionsEquiv N Y).injective
  rw [sectionsEquiv_smul, sectionsEquiv_map, sectionsEquiv_map, sectionsEquiv_smul,
    restrictionMap_smul, ringRestriction_sectionsRingHom]

/-- **The sheaf of `O`-modules descended from a cartesian system of modules.** -/
def systemTotalModule : SheafOfModules.{u} (S.totalRingSheaf O) :=
  letI : ∀ X : (S.totalCategory)ᵒᵖ, AddCommGroup ((systemTotalSheafOfSets N).obj.obj X) :=
    fun X => sectionsAddCommGroup N X.unop
  letI : ∀ X : (S.totalCategory)ᵒᵖ,
      Module ((S.totalRingSheaf O).obj.obj X) ((systemTotalSheafOfSets N).obj.obj X) :=
    fun X => sectionsModule N X.unop
  Sheaf.sheafOfModulesOfSections (S.totalRingSheaf O) (systemTotalSheafOfSets N)
    (fun g x y => sections_map_add N g.unop x y) (fun g r x => sections_map_smul N g.unop r x)

/-- The identification of the restriction of the descended sheaf of sets to degree `n`, read
on the sections over an object `U` of the component, through the identification of sections
over the corresponding object of the total category. -/
theorem systemTotalRestrictIso_hom_apply (n : SimplexCategory) (U : S.component n)
    (z : (systemTotalSheafOfSets N).obj.obj (op ((S.inclusion n).obj U))) :
    (systemTotalRestrictIso N n).hom.hom.app (op U) z =
      restrictionMap N (eqToHom (inclusion_obj_fibre ((S.inclusion n).obj U)).symm)
        (sectionsEquiv N _ z) := by
  refine Eq.symm ((congrArg (fun t => (systemTotalRestrictIso N n).hom.hom.app (op U)
    ((systemTotalSheafOfSets N).obj.map
      (eqToHom (inclusion_obj_fibre ((S.inclusion n).obj U)).symm).op t))
    (systemTotalRestrictIso_inv_hom_apply N _ _ _)).trans ?_)
  exact congrArg _ (map_eqToHom_map_eqToHom (systemTotalSheafOfSets N).obj
    (inclusion_obj_fibre ((S.inclusion n).obj U)) z)

/-- The ring map of the identification of objects, followed by that of its inverse, is the
identity. -/
theorem ringRestriction_sectionsRingHom_self (n : SimplexCategory) (U : S.component n)
    (r : (S.totalRingSheaf O).obj.obj (op ((S.inclusion n).obj U))) :
    ringRestriction (eqToHom (inclusion_obj_fibre ((S.inclusion n).obj U)).symm)
      (sectionsRingHom _ r) = r := by
  change ((S.totalRingSheaf O).obj.map (eqToHom (inclusion_obj_fibre ((S.inclusion n).obj U))).op ≫
      (S.totalRingSheaf O).obj.map
        (eqToHom (inclusion_obj_fibre ((S.inclusion n).obj U)).symm).op).hom r = r
  rw [← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id, Functor.map_id]
  rfl

/-- **The restriction of the descended sheaf of modules to degree `n` is `N_n`.** -/
def systemTotalModuleComponentIso (n : SimplexCategory) :
    S.componentModule O (systemTotalModule N) n ≅ systemModule N n :=
  isoOfSheafIso.{u, u, u}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)
    (M := S.componentModule O (systemTotalModule N) n) (N := systemModule N n)
    (systemTotalRestrictIso N n)
    ((moduleAddHom_comp_iff.{u, u, u} _).mpr fun X x y => by
      obtain ⟨U⟩ := X
      exact (systemTotalRestrictIso_hom_apply N n U _).trans
        ((congrArg (restrictionMap N _) (sectionsEquiv_add N _ x y)).trans
          ((restrictionMap_add N _ _ _).trans (congrArg₂ (· + ·)
            (systemTotalRestrictIso_hom_apply N n U x).symm
            (systemTotalRestrictIso_hom_apply N n U y).symm))))
    ((moduleSMulHom_comp_iff.{u, u, u} _).mpr fun X r x => by
      obtain ⟨U⟩ := X
      exact (systemTotalRestrictIso_hom_apply N n U _).trans
        ((congrArg (restrictionMap N _) (sectionsEquiv_smul N _ r x)).trans
          ((restrictionMap_smul N _ _ _).trans (congrArg₂ (· • ·)
            (ringRestriction_sectionsRingHom_self n U r)
            (systemTotalRestrictIso_hom_apply N n U x).symm))))

/-- The underlying morphism of sheaves of sets of the identification of the restriction of the
descended sheaf of modules. -/
theorem moduleSheafFunctor_map_systemTotalModuleComponentIso_hom (n : SimplexCategory) :
    (Sheaf.moduleSheafFunctor.{u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)).map
        (systemTotalModuleComponentIso N n).hom = (systemTotalRestrictIso N n).hom := rfl

/-- The identifications of the restrictions of the descended sheaf of modules carry its
direct-image transitions to those of the system. -/
theorem restrictTransitionModulesApp_systemTotalModule {m n : SimplexCategory} (φ : m ⟶ n) :
    (systemTotalModuleComponentIso N m).hom ≫
        (S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules.homEquiv _ _
          (systemModuleTrans N φ).hom =
      S.restrictTransitionModulesApp O φ (systemTotalModule N) ≫
        (S.transitionRingedToposHom O φ).pushforwardModules.map
          (systemTotalModuleComponentIso N n).hom := by
  apply hom_ext_moduleSheafFunctor
  exact Sheaf.hom_ext_sections fun X z =>
    congrArg (fun t => t.hom.app X z) (systemTotalRestrictIso_hom_comp N φ)

/-- **The transitions of the descended sheaf of modules are those of the system.** -/
theorem componentTransition_systemTotalModule {m n : SimplexCategory} (φ : m ⟶ n) :
    S.componentTransition O (systemTotalModule N) φ ≫ (systemTotalModuleComponentIso N n).hom =
      (S.componentModulePullback O φ).map (systemTotalModuleComponentIso N m).hom ≫
        (systemModuleTrans N φ).hom := by
  have h := Adjunction.homEquiv_naturality_right_square
    (S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules
    (systemTotalModuleComponentIso N m).hom
    ((S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules.homEquiv _ _
      (systemModuleTrans N φ).hom)
    (S.restrictTransitionModulesApp O φ (systemTotalModule N))
    (systemTotalModuleComponentIso N n).hom (restrictTransitionModulesApp_systemTotalModule N φ)
  have e := ((S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules.homEquiv
    (systemModule N m) (systemModule N n)).symm_apply_apply (systemModuleTrans N φ).hom
  exact h.symm.trans (congrArg (fun t =>
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
      (systemTotalModuleComponentIso N m).hom ≫ t) e)

/-- **The descended sheaf of modules is cartesian.** -/
theorem systemTotalModule_isCartesian : S.IsCartesianModule O (systemTotalModule N) := by
  intro m n φ
  have h : S.fiberTransitionModules O φ (systemTotalModule N) =
      (S.componentModulePullback O φ).map (systemTotalModuleComponentIso N m).hom ≫
        (systemModuleTrans N φ).hom ≫ (systemTotalModuleComponentIso N n).inv := by
    rw [← Category.assoc, ← componentTransition_systemTotalModule N φ, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
    rfl
  rw [h]
  have : IsIso ((S.componentModulePullback O φ).map (systemTotalModuleComponentIso N m).hom) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso' this (IsIso.comp_isIso' (Iso.isIso_hom (systemModuleTrans N φ))
    (Iso.isIso_inv (systemTotalModuleComponentIso N n)))

/-- The descended sheaf of modules, as a cartesian sheaf of modules. -/
def systemTotalCartesianModule : S.CartesianModuleSheaf O :=
  ⟨systemTotalModule N, systemTotalModule_isCartesian N⟩

/-- The identification of the restriction of the descended cartesian module to degree `n` with
the object of the system in degree `n`. -/
def systemTotalModuleObjIso (n : SimplexCategory) :
    S.componentModule O (systemTotalCartesianModule N).obj n ≅ N.obj n :=
  systemTotalModuleComponentIso N n

/-- The transitions of the cartesian system of the descended cartesian module are those of the
system. -/
theorem cartesianModuleSystem_trans_systemTotalCartesianModule {m n : SimplexCategory}
    (φ : m ⟶ n) :
    ((S.cartesianModuleSystem O (systemTotalCartesianModule N)).trans φ).hom ≫
        @Iso.hom ((S.modulePseudoFamily O).obj n) _ _ _ (systemTotalModuleObjIso N n) =
      ((S.modulePseudoFamily O).map φ).map
          (@Iso.hom ((S.modulePseudoFamily O).obj m) _ _ _ (systemTotalModuleObjIso N m)) ≫
        (N.trans φ).hom :=
  componentTransition_systemTotalModule N φ

end TotalModule

end CategoryTheory.SimplicialSiteSituation

end
