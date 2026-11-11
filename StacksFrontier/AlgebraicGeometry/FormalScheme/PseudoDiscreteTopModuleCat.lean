module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import StacksFrontier.AlgebraicGeometry.FormalScheme.PseudoDiscreteTopCat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-discrete sheaves of topological modules

Let `X` be a topological space with a basis of quasi-compact opens and `R` a ring, viewed as a
discrete topological ring. The source (Stacks, Section 87.2, Tag 0AHY) endows every sheaf of
`R`-modules on `X` with the structure of a sheaf of topological `R`-modules, the
*pseudo-discrete* one, and states that this construction is adjoint to the forgetful functor and
induces an equivalence between the category of sheaves of `R`-modules and the category of
pseudo-discrete sheaves of topological `R`-modules. This file proves both statements, reducing
the topological input to the case of sheaves of sets
(`StacksFrontier.AlgebraicGeometry.FormalScheme.PseudoDiscreteTopCat`): the pseudo-discrete topology
on the sections of a sheaf of modules is the pseudo-discrete topology on its underlying sheaf of
sets.

## Main definitions

* `AlgebraicGeometry.pseudoDiscreteModule`: the pseudo-discrete presheaf of topological modules.
* `AlgebraicGeometry.pseudoDiscreteModuleSheafAdjunction`: pseudo-discretisation of sheaves of
  modules is left adjoint to forgetting the topology.
* `AlgebraicGeometry.pseudoDiscreteModuleSheafEquivalence`: it is an equivalence between sheaves
  of modules and pseudo-discrete sheaves of topological modules.

## References

* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open TopCat.Presheaf.SheafCondition
open scoped Topology

universe u

namespace AlgebraicGeometry

variable {X : TopCat.{u}} {R : Type u} [Ring R] [TopologicalSpace R] [DiscreteTopology R]

/-- The underlying presheaf of sets of a presheaf of modules. -/
abbrev moduleSets (F : X.Presheaf (ModuleCat.{u} R)) : X.Presheaf (Type u) :=
  F ⋙ forget (ModuleCat.{u} R)

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- The pseudo-discrete topology makes addition continuous. -/
theorem continuousAdd_pseudoDiscreteTopologySet (F : X.Presheaf (ModuleCat.{u} R))
    (U : Opens X) :
    @ContinuousAdd (F.obj (op U)) (pseudoDiscreteTopologySet (moduleSets F) U) _ := by
  refine continuousAdd_iInf fun V => ?_
  let : TopologicalSpace (F.obj (op V.1)) := ⊥
  have : DiscreteTopology (F.obj (op V.1)) := ⟨rfl⟩
  have : ContinuousAdd (F.obj (op V.1)) := ⟨continuous_of_discreteTopology⟩
  exact continuousAdd_induced (F.map (homOfLE V.2.2).op).hom

/-- The pseudo-discrete topology makes scalar multiplication by the discrete ring `R`
continuous. -/
theorem continuousSMul_pseudoDiscreteTopologySet (F : X.Presheaf (ModuleCat.{u} R))
    (U : Opens X) :
    @ContinuousSMul R (F.obj (op U)) _ _ (pseudoDiscreteTopologySet (moduleSets F) U) := by
  refine continuousSMul_iInf fun V => ?_
  let : TopologicalSpace (F.obj (op V.1)) := ⊥
  have : DiscreteTopology (F.obj (op V.1)) := ⟨rfl⟩
  have : ContinuousSMul R (F.obj (op V.1)) := ⟨continuous_of_discreteTopology⟩
  exact continuousSMul_induced (F.map (homOfLE V.2.2).op).hom

/-- The sections of a presheaf of modules over `U`, as a topological module with the
pseudo-discrete topology. -/
def pseudoDiscreteModuleObj (F : X.Presheaf (ModuleCat.{u} R)) (U : Opens X) :
    TopModuleCat.{u} R :=
  letI : TopologicalSpace (F.obj (op U)) := pseudoDiscreteTopologySet (moduleSets F) U
  haveI := continuousAdd_pseudoDiscreteTopologySet F U
  haveI := continuousSMul_pseudoDiscreteTopologySet F U
  TopModuleCat.of R (F.obj (op U))

/-- A continuous `R`-linear map between topological modules, as a morphism of
`TopModuleCat R`. -/
abbrev topModuleCatHom {M N : TopModuleCat.{u} R} (f : M.toModuleCat ⟶ N.toModuleCat)
    (hf : Continuous f) : M ⟶ N :=
  ConcreteCategory.ofHom (C := TopModuleCat R) ⟨f.hom, hf⟩

/-- The *pseudo-discrete presheaf of topological modules* attached to a presheaf of modules. -/
def pseudoDiscreteModule (F : X.Presheaf (ModuleCat.{u} R)) :
    X.Presheaf (TopModuleCat.{u} R) where
  obj U := pseudoDiscreteModuleObj F U.unop
  map i := topModuleCatHom (M := pseudoDiscreteModuleObj F _) (N := pseudoDiscreteModuleObj F _)
    (F.map i) (continuous_pseudoDiscreteTopologySet_map (moduleSets F) (leOfHom i.unop))
  map_id U := by
    ext s
    exact congrArg (fun g => g.hom s) (F.map_id U)
  map_comp f g := by
    ext s
    exact congrArg (fun h => h.hom s) (F.map_comp f g)

/-- A presheaf of topological modules is *pseudo-discrete* when its module of sections over
every quasi-compact open is discrete. -/
def IsPseudoDiscreteModule (G : X.Presheaf (TopModuleCat.{u} R)) : Prop :=
  ∀ U : Opens X, IsCompact (U : Set X) → DiscreteTopology (G.obj (op U))

/-- The pseudo-discretisation is pseudo-discrete. -/
theorem isPseudoDiscreteModule_pseudoDiscreteModule (F : X.Presheaf (ModuleCat.{u} R)) :
    IsPseudoDiscreteModule (pseudoDiscreteModule F) :=
  fun _ hU => ⟨pseudoDiscreteTopologySet_eq_bot (moduleSets F) hU⟩

/-- Pseudo-discretisation as a functor from presheaves of modules to presheaves of topological
modules. -/
def pseudoDiscreteModuleFunctor :
    X.Presheaf (ModuleCat.{u} R) ⥤ X.Presheaf (TopModuleCat.{u} R) where
  obj F := pseudoDiscreteModule F
  map η :=
    { app := fun U => topModuleCatHom (M := pseudoDiscreteModuleObj _ _)
        (N := pseudoDiscreteModuleObj _ _) (η.app U)
        (continuous_pseudoDiscreteTopologySet_app
          (Functor.whiskerRight η (forget (ModuleCat.{u} R))) U.unop)
      naturality := fun _ _ i => by
        ext s
        exact congrArg (fun h => h.hom s) (η.naturality i) }

/-- Forgetting the topology of the pseudo-discretisation gives back the presheaf of modules. -/
def pseudoDiscreteModuleCompForgetIso (F : X.Presheaf (ModuleCat.{u} R)) :
    pseudoDiscreteModule F ⋙ forget₂ (TopModuleCat.{u} R) (ModuleCat.{u} R) ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The underlying presheaf of topological spaces of a presheaf of topological modules. -/
abbrev topModuleSpaces (G : X.Presheaf (TopModuleCat.{u} R)) : X.Presheaf TopCat.{u} :=
  G ⋙ forget₂ (TopModuleCat.{u} R) TopCat.{u}

/-- A morphism of presheaves of modules into the underlying presheaf of modules of a presheaf of
topological modules, as a morphism of the underlying presheaves of sets. -/
def moduleSetsHom (F : X.Presheaf (ModuleCat.{u} R)) (G : X.Presheaf (TopModuleCat.{u} R))
    (η : F ⟶ G ⋙ forget₂ (TopModuleCat.{u} R) (ModuleCat.{u} R)) :
    moduleSets F ⟶ topModuleSpaces G ⋙ forget TopCat.{u} where
  app U := TypeCat.ofHom (η.app U)
  naturality _ _ i := by
    ext s
    exact congrArg (fun h => h.hom s) (η.naturality i)

variable [PrespectralSpace X]

omit [DiscreteTopology R] in
/-- **A morphism of presheaves of modules into a sheaf of topological modules is continuous for
the pseudo-discrete topology.** -/
theorem continuous_app_of_isSheaf_topModuleCat (F : X.Presheaf (ModuleCat.{u} R))
    {G : X.Presheaf (TopModuleCat.{u} R)} (hG : G.IsSheaf)
    (η : F ⟶ G ⋙ forget₂ (TopModuleCat.{u} R) (ModuleCat.{u} R)) (U : Opens X) :
    Continuous[pseudoDiscreteTopologySet (moduleSets F) U, (G.obj (op U)).topologicalSpace]
      (η.app (op U)) :=
  continuous_app_of_isSheaf_topCat (moduleSets F)
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ (TopModuleCat.{u} R) TopCat.{u}) hG)
    (moduleSetsHom F G η) U

/-- On a space with a basis of quasi-compact opens, the pseudo-discrete presheaf of topological
modules attached to a sheaf of modules is a sheaf of topological modules. -/
theorem isSheaf_pseudoDiscreteModule_of_isSheaf (F : X.Presheaf (ModuleCat.{u} R))
    (hF : F.IsSheaf) : (pseudoDiscreteModule F).IsSheaf := by
  have hFs : (moduleSets F).IsSheaf :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ (forget (ModuleCat.{u} R)) hF
  refine (TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover _).2 fun ι cover => ?_
  let modLimit := (hF.isSheafOpensLeCover cover).some
  let fgt := forget₂ (TopModuleCat.{u} R) (ModuleCat.{u} R)
  refine ⟨IsLimit.mk (fun cone => topModuleCatHom
    (N := pseudoDiscreteModuleObj F (iSup cover)) (modLimit.lift (fgt.mapCone cone)) ?_)
    (fun cone V => ?_) ?_⟩
  · refine continuous_pseudoDiscreteSet_gluing_of_isSheaf (moduleSets F) hFs cover _
      fun V => ?_
    have hfac : ⇑(F.map ((opensLeCoverCocone cover).ι.app V).op).hom ∘
        ⇑(modLimit.lift (fgt.mapCone cone)).hom = ⇑((cone.π.app (op V)).hom) := by
      funext t
      exact congrArg (fun g => g.hom t) (modLimit.fac (fgt.mapCone cone) (op V))
    exact hfac ▸ (cone.π.app (op V)).hom.continuous
  · ext t
    exact congrArg (fun g => g.hom t) (modLimit.fac (fgt.mapCone cone) V)
  · intro cone morphism hfac
    ext t
    exact congrArg (fun g => g.hom t) (modLimit.uniq (fgt.mapCone cone) (fgt.map morphism)
      fun V => congrArg fgt.map (hfac V))

variable (X R) in
/-- Pseudo-discretisation as a functor from sheaves of modules to sheaves of topological
modules. -/
def pseudoDiscreteModuleSheafFunctor :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤
      Sheaf (Opens.grothendieckTopology X) (TopModuleCat.{u} R) :=
  ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ pseudoDiscreteModuleFunctor)
    fun F => isSheaf_pseudoDiscreteModule_of_isSheaf F.obj F.property

variable (X R) in
/-- Forgetting the topology of a sheaf of topological modules. -/
noncomputable abbrev sheafForgetTopModuleCat :
    Sheaf (Opens.grothendieckTopology X) (TopModuleCat.{u} R) ⥤
      Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  sheafCompose _ (forget₂ (TopModuleCat.{u} R) (ModuleCat.{u} R))

/-- The bijection between morphisms out of a pseudo-discretisation and morphisms into the
underlying sheaf of modules. -/
noncomputable def pseudoDiscreteModuleSheafHomEquiv
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (G : Sheaf (Opens.grothendieckTopology X) (TopModuleCat.{u} R)) :
    ((pseudoDiscreteModuleSheafFunctor X R).obj F ⟶ G) ≃
      (F ⟶ (sheafForgetTopModuleCat X R).obj G) where
  toFun φ := ObjectProperty.homMk
    ((pseudoDiscreteModuleCompForgetIso F.obj).inv ≫
      Functor.whiskerRight φ.hom (forget₂ (TopModuleCat.{u} R) (ModuleCat.{u} R)))
  invFun ψ := ObjectProperty.homMk
    { app := fun U => topModuleCatHom (M := pseudoDiscreteModuleObj F.obj U.unop) (ψ.hom.app U)
        (continuous_app_of_isSheaf_topModuleCat F.obj G.property ψ.hom U.unop)
      naturality := fun _ _ i => by
        ext s
        exact congrArg (fun h => h.hom s) (ψ.hom.naturality i) }
  left_inv φ := by
    ext
    rfl
  right_inv ψ := by
    ext
    rfl

/-- **Stacks 0AHY**: on a space with a basis of quasi-compact opens, pseudo-discretisation of
sheaves of modules over a ring is left adjoint to the forgetful functor from sheaves of
topological modules to sheaves of modules. -/
@[stacks 0AHY "the pseudo-discrete construction on sheaves of modules is adjoint to the \
forgetful functor"]
noncomputable def pseudoDiscreteModuleSheafAdjunction :
    pseudoDiscreteModuleSheafFunctor X R ⊣ sheafForgetTopModuleCat X R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pseudoDiscreteModuleSheafHomEquiv
      homEquiv_naturality_left_symm := by
        intros
        ext
        rfl
      homEquiv_naturality_right := by
        intros
        ext
        rfl }

variable (X R) in
/-- The full subcategory of pseudo-discrete sheaves of topological modules. -/
abbrev PseudoDiscreteModuleSheaf :=
  ObjectProperty.FullSubcategory
    fun G : Sheaf (Opens.grothendieckTopology X) (TopModuleCat.{u} R) =>
      IsPseudoDiscreteModule G.obj

omit [DiscreteTopology R] in
/-- On the sections of a pseudo-discrete sheaf of topological modules, the given topology is the
pseudo-discrete topology of the underlying sheaf of modules. -/
theorem pseudoDiscreteTopologySet_eq_of_isPseudoDiscreteModule
    {G : X.Presheaf (TopModuleCat.{u} R)} (hG : G.IsSheaf) (hpd : IsPseudoDiscreteModule G)
    (U : Opens X) :
    pseudoDiscreteTopologySet (moduleSets (G ⋙ forget₂ (TopModuleCat.{u} R) (ModuleCat.{u} R)))
      U = (G.obj (op U)).topologicalSpace :=
  pseudoDiscreteTopologySet_eq_of_isPseudoDiscreteTop
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ (TopModuleCat.{u} R) TopCat.{u}) hG)
    (fun V hV => hpd V hV) U

/-- The isomorphism between a pseudo-discrete sheaf of topological modules and the
pseudo-discretisation of its underlying sheaf of modules. -/
noncomputable def pseudoDiscreteModuleForgetIso (G : PseudoDiscreteModuleSheaf X R) :
    (pseudoDiscreteModuleSheafFunctor X R).obj ((sheafForgetTopModuleCat X R).obj G.obj) ≅
      G.obj :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun U =>
      { hom := topModuleCatHom
          (M := pseudoDiscreteModuleObj
            (G.obj.obj ⋙ forget₂ (TopModuleCat.{u} R) (ModuleCat.{u} R)) U.unop)
          (N := G.obj.obj.obj U) (𝟙 _) (by
            have := pseudoDiscreteTopologySet_eq_of_isPseudoDiscreteModule G.obj.property
              G.property U.unop
            exact continuous_id_of_le this.le)
        inv := topModuleCatHom (M := G.obj.obj.obj U)
          (N := pseudoDiscreteModuleObj
            (G.obj.obj ⋙ forget₂ (TopModuleCat.{u} R) (ModuleCat.{u} R)) U.unop) (𝟙 _) (by
            have := pseudoDiscreteTopologySet_eq_of_isPseudoDiscreteModule G.obj.property
              G.property U.unop
            exact continuous_id_of_le this.ge)
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ => rfl)

variable (X R) in
/-- **Stacks 0AHY**: on a space with a basis of quasi-compact opens, pseudo-discretisation is an
equivalence between the category of sheaves of modules over a ring and the category of
pseudo-discrete sheaves of topological modules; its inverse forgets the topology. -/
@[stacks 0AHY "equivalence between sheaves of modules and pseudo-discrete sheaves of \
topological modules"]
noncomputable def pseudoDiscreteModuleSheafEquivalence :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ≌ PseudoDiscreteModuleSheaf X R :=
  CategoryTheory.Equivalence.mk
    (ObjectProperty.lift
      (fun G : Sheaf (Opens.grothendieckTopology X) (TopModuleCat.{u} R) =>
        IsPseudoDiscreteModule G.obj)
      (pseudoDiscreteModuleSheafFunctor X R)
      fun F => isPseudoDiscreteModule_pseudoDiscreteModule F.obj)
    (ObjectProperty.ι
      (fun G : Sheaf (Opens.grothendieckTopology X) (TopModuleCat.{u} R) =>
        IsPseudoDiscreteModule G.obj) ⋙ sheafForgetTopModuleCat X R)
    (NatIso.ofComponents
      (fun F => ObjectProperty.isoMk _ (pseudoDiscreteModuleCompForgetIso F.obj).symm)
      (fun _ => by ext; rfl))
    (NatIso.ofComponents (fun G => ObjectProperty.isoMk _ (pseudoDiscreteModuleForgetIso G))
      (fun _ => by ext; rfl))

end AlgebraicGeometry

end
