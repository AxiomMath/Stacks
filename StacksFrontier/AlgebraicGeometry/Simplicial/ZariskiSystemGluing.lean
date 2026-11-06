module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiModulePseudoFamily
public import StacksFrontier.Topology.Simplicial.ComponentSheafCriterion

/-!
# Gluing a cartesian system of modules into a module on the total Zariski site

Let `X` be a simplicial scheme and `N` a cartesian system of the family of modules on the degrees
of `X`: modules `N_n` on the schemes `X_n` with isomorphisms `(X φ)^* N_m ≅ N_n` satisfying the
unit and cocycle laws. This file glues `N` into a sheaf of `𝒪_X`-modules on the total Zariski
site of `X`, whose sections over the object `(n, W)` are the sections of `N_n` over `W`, and
whose restriction along an arrow lying over a simplex map is the direct form of the transition
followed by a restriction inside one degree. The components of the glued module are the `N_n`,
and its transitions are those of `N`; in particular it is cartesian.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.systemDirectTransition`: the direct form
  `N_m ⟶ (X φ)_* N_n` of a transition of a cartesian system.
* `AlgebraicGeometry.SimplicialScheme.systemModule`: the glued module.
* `AlgebraicGeometry.SimplicialScheme.systemModuleComponentIso`: its component in degree `n` is
  `N_n`.

## Main results

* `AlgebraicGeometry.SimplicialScheme.systemDirectTransition_comp` and
  `systemDirectTransition_id`: the cocycle and unit laws in direct form, on sections.
* `AlgebraicGeometry.SimplicialScheme.isCartesianModule_systemModule`: the glued module is
  cartesian.

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 09VM](https://stacks.math.columbia.edu/tag/09VM)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Topology.Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {X : SimplicialObject Scheme.{u}} (N : (zariskiModuleFamily X).CartesianSystem)

/-- **The direct form of a transition of a cartesian system**, `N_m ⟶ (X φ)_* N_n` for a
simplex map `φ : m ⟶ n`: the transpose of the transition `(X φ)^* N_m ≅ N_n`. -/
noncomputable def systemDirectTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    N.obj m ⟶ (Scheme.Modules.pushforward (X.map φ.op)).obj (N.obj n) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ.op)).homEquiv _ _) (N.trans φ).hom

/-- The transition of a cartesian system is the transpose of its direct form. -/
theorem systemDirectTransition_homEquiv_symm {m n : SimplexCategory} (φ : m ⟶ n) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (X.map φ.op)).homEquiv _ _).symm
      (systemDirectTransition N φ) = (N.trans φ).hom :=
  Equiv.symm_apply_apply _ _

/-- **The cocycle law for the direct transitions of a cartesian system.** -/
theorem systemDirectTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    systemDirectTransition N (ψ ≫ φ) =
      (systemDirectTransition N ψ ≫
          (Scheme.Modules.pushforward (X.map ψ.op)).map (systemDirectTransition N φ)) ≫
        (Scheme.Modules.pushforwardComp (X.map φ.op) (X.map ψ.op)).hom.app (N.obj n) ≫
          (Scheme.Modules.pushforwardCongr (X.map_comp φ.op ψ.op).symm).hom.app (N.obj n) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction
    (X.map (ψ ≫ φ).op)).homEquiv _ _).symm.injective
  have h1 := homEquiv_symm_pushforwardComp_congr (X.map φ.op) (X.map ψ.op) (X.map (ψ ≫ φ).op)
    (X.map_comp φ.op ψ.op).symm (systemDirectTransition N ψ) (systemDirectTransition N φ)
  rw [systemDirectTransition_homEquiv_symm, systemDirectTransition_homEquiv_symm] at h1
  rw [h1, systemDirectTransition_homEquiv_symm, Iso.eq_inv_comp]
  exact N.trans_comp ψ φ

/-- **The unit law for the direct transitions of a cartesian system.** -/
theorem systemDirectTransition_id (n : SimplexCategory) :
    systemDirectTransition N (𝟙 n) =
      (Scheme.Modules.pushforwardId _).inv.app (N.obj n) ≫
        (Scheme.Modules.pushforwardCongr (X.map_id (op n))).inv.app (N.obj n) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction
    (X.map (𝟙 n).op)).homEquiv _ _).symm.injective
  rw [systemDirectTransition_homEquiv_symm, homEquiv_symm_pushforwardId]
  exact N.trans_id n

/-- The cocycle law for the direct transitions, on sections over an open. -/
theorem systemDirectTransition_comp_app {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (W : (X.obj (op l)).Opens) :
    (systemDirectTransition N (ψ ≫ φ)).app W =
      (systemDirectTransition N ψ).app W ≫
        (systemDirectTransition N φ).app (X.map ψ.op ⁻¹ᵁ W) ≫
        (N.obj n).presheaf.map
          (eqToHom (show X.map (ψ ≫ φ).op ⁻¹ᵁ W = X.map φ.op ⁻¹ᵁ X.map ψ.op ⁻¹ᵁ W by
            rw [op_comp, X.map_comp]; rfl)).op := by
  rw [systemDirectTransition_comp]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Category.assoc]
  exact congrArg (fun t => _ ≫ _ ≫ t) (Category.id_comp _)

/-- The unit law for the direct transitions, on sections over an open. -/
theorem systemDirectTransition_id_app (n : SimplexCategory) (W : (X.obj (op n)).Opens) :
    (systemDirectTransition N (𝟙 n)).app W =
      (N.obj n).presheaf.map
        (eqToHom (show X.map (𝟙 n).op ⁻¹ᵁ W = W by rw [op_id, X.map_id]; rfl)).op := by
  rw [systemDirectTransition_id]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardId_inv_app_app,
    Scheme.Modules.pushforwardCongr_inv_app_app]
  exact Category.id_comp _

/-- Two restriction maps of the presheaf of sections of a module of a scheme with the same
source and target are equal. -/
theorem presheaf_map_eq {Y : Scheme.{u}} (M : Y.Modules) {A B : Y.Opens} (i j : A ⟶ B) :
    M.presheaf.map i.op = M.presheaf.map j.op :=
  congrArg (fun k => M.presheaf.map k.op) (Subsingleton.elim i j)

/-- A composite of two restriction maps of the presheaf of sections of a module of a scheme is
the restriction map along any arrow between the outer opens. -/
theorem presheaf_map_comp_eq {Y : Scheme.{u}} (M : Y.Modules) {A B C : Y.Opens} (i : B ⟶ A)
    (j : C ⟶ B) (k : C ⟶ A) :
    M.presheaf.map i.op ≫ M.presheaf.map j.op = M.presheaf.map k.op := by
  rw [← Functor.map_comp, ← op_comp]
  exact presheaf_map_eq M _ _

/-! ### The glued presheaf -/

/-- The direct transition of a cartesian system on sections over an open `W` of `X_m`, read
into the sections of `N_n` over `(X φ)⁻¹ W`. -/
noncomputable def systemDirectApp {m n : SimplexCategory} (φ : m ⟶ n) (W : (X.obj (op m)).Opens) :
    Γ(N.obj m, W) ⟶ Γ(N.obj n, X.map φ.op ⁻¹ᵁ W) :=
  (systemDirectTransition N φ).app W

/-- The direct transitions on sections are natural in the open. -/
theorem systemDirectApp_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    {A B : (X.obj (op m)).Opens} (i : B ⟶ A) :
    (N.obj m).presheaf.map i.op ≫ systemDirectApp N φ B =
      systemDirectApp N φ A ≫ (N.obj n).presheaf.map ((Opens.map (X.map φ.op).base).map i).op :=
  (systemDirectTransition N φ).mapPresheaf.naturality i.op

/-- The cocycle law for the direct transitions on sections. -/
theorem systemDirectApp_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (W : (X.obj (op l)).Opens) :
    systemDirectApp N (ψ ≫ φ) W =
      systemDirectApp N ψ W ≫ systemDirectApp N φ (X.map ψ.op ⁻¹ᵁ W) ≫
        (N.obj n).presheaf.map
          (eqToHom (show X.map (ψ ≫ φ).op ⁻¹ᵁ W = X.map φ.op ⁻¹ᵁ X.map ψ.op ⁻¹ᵁ W by
            rw [op_comp, X.map_comp]; rfl)).op :=
  systemDirectTransition_comp_app N ψ φ W

/-- The unit law for the direct transitions on sections. -/
theorem systemDirectApp_id (n : SimplexCategory) (W : (X.obj (op n)).Opens) :
    systemDirectApp N (𝟙 n) W =
      (N.obj n).presheaf.map
        (eqToHom (show X.map (𝟙 n).op ⁻¹ᵁ W = W by rw [op_id, X.map_id]; rfl)).op :=
  systemDirectTransition_id_app N n W

/-- The restriction map of the glued presheaf along an arrow `f : (m, V) ⟶ (n, W)` of the total
Zariski site: the direct transition along the underlying map of simplicial degrees, followed by
the restriction from `(X f)⁻¹ W` to `V`. -/
noncomputable def systemPresheafMap {U V : ZariskiOpen X} (f : V ⟶ U) :
    Γ(N.obj U.degree.unop, U.toOpens) ⟶ Γ(N.obj V.degree.unop, V.toOpens) :=
  systemDirectApp N (SimplicialOpen.Hom.base f).unop U.toOpens ≫
    (N.obj V.degree.unop).presheaf.map (homOfLE (SimplicialOpen.Hom.le f)).op

/-- The restriction map of the glued presheaf along an identity is the identity. -/
theorem systemPresheafMap_id (U : ZariskiOpen X) :
    systemPresheafMap N (𝟙 U) = 𝟙 _ := by
  unfold systemPresheafMap
  exact ((congrArg (fun t => t ≫ _) (systemDirectApp_id N U.degree.unop U.toOpens)).trans
    (presheaf_map_comp_eq _ _ _ (𝟙 _))).trans ((N.obj U.degree.unop).presheaf.map_id _)

/-- The composite of two restriction maps of the glued presheaf, in terms of opens. -/
theorem systemDirectApp_comp_restrict {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (A : (X.obj (op l)).Opens) (B : (X.obj (op m)).Opens) (C : (X.obj (op n)).Opens)
    (hB : B ≤ X.map ψ.op ⁻¹ᵁ A) (hC : C ≤ X.map φ.op ⁻¹ᵁ B) (hC' : C ≤ X.map (ψ ≫ φ).op ⁻¹ᵁ A) :
    systemDirectApp N (ψ ≫ φ) A ≫ (N.obj n).presheaf.map (homOfLE hC').op =
      (systemDirectApp N ψ A ≫ (N.obj m).presheaf.map (homOfLE hB).op) ≫
        (systemDirectApp N φ B ≫ (N.obj n).presheaf.map (homOfLE hC).op) := by
  have k : C ⟶ X.map φ.op ⁻¹ᵁ X.map ψ.op ⁻¹ᵁ A :=
    homOfLE (hC.trans ((Opens.map (X.map φ.op).base).monotone hB))
  rw [systemDirectApp_comp, Category.assoc, Category.assoc, Category.assoc,
    ← Category.assoc ((N.obj m).presheaf.map (homOfLE hB).op), systemDirectApp_naturality,
    Category.assoc, presheaf_map_comp_eq _ _ _ k, presheaf_map_comp_eq _ _ _ k]

/-- The restriction maps of the glued presheaf compose. -/
theorem systemPresheafMap_comp {U V W : ZariskiOpen X} (f : V ⟶ U) (g : W ⟶ V) :
    systemPresheafMap N (g ≫ f) = systemPresheafMap N f ≫ systemPresheafMap N g :=
  systemDirectApp_comp_restrict N (SimplicialOpen.Hom.base f).unop
    (SimplicialOpen.Hom.base g).unop U.toOpens V.toOpens W.toOpens _ _ _

/-- **The glued presheaf of abelian groups.** Its sections over `(n, W)` are the sections of
`N_n` over `W`. -/
noncomputable def systemPresheaf : (ZariskiOpen X)ᵒᵖ ⥤ Ab.{u} where
  obj U := Γ(N.obj U.unop.degree.unop, U.unop.toOpens)
  map f := systemPresheafMap N f.unop
  map_id U := systemPresheafMap_id N U.unop
  map_comp f g := systemPresheafMap_comp N f.unop g.unop

/-- In each simplicial degree the glued presheaf is the presheaf of sections of the module of the
system in that degree. -/
noncomputable def systemPresheafComponentIso (n : SimplexCategoryᵒᵖ) :
    componentPresheaf (systemPresheaf N) n ≅ (N.obj n.unop).presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {W W'} i => by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    change systemDirectApp N (𝟙 n.unop) W.unop ≫ _ = _
    rw [systemDirectApp_id]
    exact presheaf_map_comp_eq _ _ _ _)

/-- The glued presheaf is a sheaf on the total Zariski site. -/
theorem systemPresheaf_isSheaf :
    Presheaf.IsSheaf (zariskiTopology X) (systemPresheaf N) :=
  isSheaf_of_isSheaf_componentPresheaf (systemPresheaf N) fun n =>
    (Presheaf.isSheaf_of_iso_iff (systemPresheafComponentIso N n)).mpr
      (Scheme.Modules.isSheaf (N.obj n.unop))

/-- The sections of the glued presheaf are modules over the sections of the structure sheaf. -/
noncomputable instance systemPresheaf_module (U : (ZariskiOpen X)ᵒᵖ) :
    Module ((Stacks.SheafOfModules.Tensor.ringSheaf
      (zariskiRingedTopos X).O).obj.obj U) ((systemPresheaf N).obj U) :=
  inferInstanceAs (Module Γ(X.obj (op U.unop.degree.unop), U.unop.toOpens)
    Γ(N.obj U.unop.degree.unop, U.unop.toOpens))

/-- The restriction maps of the glued presheaf are semilinear over the restriction maps of the
structure sheaf. -/
theorem systemPresheaf_map_smul ⦃U V : (ZariskiOpen X)ᵒᵖ⦄ (f : U ⟶ V)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O).obj.obj U)
    (x : (systemPresheaf N).obj U) :
    (systemPresheaf N).map f (r • x) =
      (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O).obj.map f r •
        (systemPresheaf N).map f x := by
  have h1 := Scheme.Modules.Hom.app_smul (systemDirectTransition N f.unop.base.unop)
    (U := U.unop.toOpens) r x
  have h2 := Scheme.Modules.map_smul (N.obj V.unop.degree.unop)
    (homOfLE (SimplicialOpen.Hom.le f.unop)) ((X.map f.unop.base.unop.op).app U.unop.toOpens r)
    ((systemDirectTransition N f.unop.base.unop).app U.unop.toOpens x)
  exact (congrArg (fun t => (N.obj V.unop.degree.unop).presheaf.map
    (homOfLE (SimplicialOpen.Hom.le f.unop)).op t) h1).trans h2

/-- **The module glued from a cartesian system.** -/
noncomputable def systemModule : Modules X where
  val := PresheafOfModules.ofPresheaf (systemPresheaf N) (systemPresheaf_map_smul N)
  isSheaf := systemPresheaf_isSheaf N

/-! ### The components and the transitions of the glued module -/

/-- The sections of the glued module over an object of the total Zariski site. -/
theorem systemModule_presheaf_obj (U : (ZariskiOpen X)ᵒᵖ) :
    (systemModule N).val.presheaf.obj U = Γ(N.obj U.unop.degree.unop, U.unop.toOpens) := rfl

/-- The comparison of the degree-`n` component of the glued module with `N_n`: the identity on
sections. -/
noncomputable def systemModuleComponentHom (n : SimplexCategory) :
    (componentModule X (op n)).obj (systemModule N) ⟶ N.obj n where
  val := PresheafOfModules.homMk (systemPresheafComponentIso N (op n)).hom (fun _ _ _ => rfl)

/-- The comparison of `N_n` with the degree-`n` component of the glued module: the identity on
sections. -/
noncomputable def systemModuleComponentInv (n : SimplexCategory) :
    N.obj n ⟶ (componentModule X (op n)).obj (systemModule N) where
  val := PresheafOfModules.homMk (systemPresheafComponentIso N (op n)).inv (fun _ _ _ => rfl)

/-- **The degree-`n` component of the glued module is `N_n`.** -/
noncomputable def systemModuleComponentIso (n : SimplexCategory) :
    (componentModule X (op n)).obj (systemModule N) ≅ N.obj n where
  hom := systemModuleComponentHom N n
  inv := systemModuleComponentInv N n
  hom_inv_id := Scheme.Modules.hom_ext _ _ fun _ => rfl
  inv_hom_id := Scheme.Modules.hom_ext _ _ fun _ => rfl

/-- On sections the comparison of a component of the glued module with `N_n` is the identity. -/
theorem systemModuleComponentIso_hom_app (n : SimplexCategory) (W : (X.obj (op n)).Opens) :
    (systemModuleComponentIso N n).hom.app W = 𝟙 _ := rfl

/-- On sections the comparison of `N_n` with a component of the glued module is the identity. -/
theorem systemModuleComponentIso_inv_app (n : SimplexCategory) (W : (X.obj (op n)).Opens) :
    (systemModuleComponentIso N n).inv.app W = 𝟙 _ := rfl

/-- The direct transition of the glued module is the direct transition of the system, read
through the identifications of the components. -/
theorem componentModuleDirectTransition_systemModule {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentModuleDirectTransition X φ.op).app (systemModule N) =
      (systemModuleComponentIso N m).hom ≫ systemDirectTransition N φ ≫
        (Scheme.Modules.pushforward (X.map φ.op)).map (systemModuleComponentIso N n).inv := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext x
  show systemPresheafMap N (SimplicialSheafSystem.transitionHom φ.op W) x =
    systemDirectApp N φ W x
  unfold systemPresheafMap
  have key : systemDirectApp N φ W ≫ (N.obj n).presheaf.map
      (homOfLE (le_refl (X.map φ.op ⁻¹ᵁ W))).op = systemDirectApp N φ W := by
    rw [presheaf_map_eq _ _ (𝟙 _), op_id, (N.obj n).presheaf.map_id, Category.comp_id]
  exact congrArg (fun t => (ConcreteCategory.hom t) x) key

/-- **The transition of the glued module is the transition of the system**, read through the
identifications of the components. -/
theorem componentModuleTransition_systemModule {m n : SimplexCategory} (φ : m ⟶ n) :
    componentModuleTransition X φ.op (systemModule N) =
      (Scheme.Modules.pullback (X.map φ.op)).map (systemModuleComponentIso N m).hom ≫
        (N.trans φ).hom ≫ (systemModuleComponentIso N n).inv := by
  rw [componentModuleTransition, componentModuleDirectTransition_systemModule,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    systemDirectTransition_homEquiv_symm]

/-- **The glued module is cartesian.** -/
theorem isCartesianModule_systemModule : IsCartesianModule X (systemModule N) := by
  intro a b ψ
  show IsIso (componentModuleTransition X ψ.unop.op (systemModule N))
  rw [componentModuleTransition_systemModule]
  infer_instance

end AlgebraicGeometry.SimplicialScheme

end
