module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import StacksFrontier.Topology.Sheaves.Glueing.Equivalence
public import StacksFrontier.Topology.Sheaves.Glueing.OModule
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Sheaves of `𝒪`-modules are the same thing as glueing data (Stacks 00AN)

Let `X` be a topological space, let `𝒪` be a sheaf of rings on `X` and let `X = ⋃ i, U i` be an
open covering. Restricting a sheaf of `𝒪`-modules `M` to each `U i`, and taking the comparison
isomorphisms over the overlaps to be the identity, produces a glueing datum of sheaves of
`𝒪`-modules in the sense of `TopCat.Sheaf.OModuleGlueData`. Stacks 00AN asserts that this functor
is an equivalence of categories; this file proves the `𝒪`-module case.

## Main definitions

* `TopCat.Sheaf.OModuleGlueData.Hom`: a morphism of glueing data of sheaves of `𝒪`-modules, i.e. a
  family of `𝒪`-linear maps of the local sheaves commuting with the comparison isomorphisms.
* `TopCat.Sheaf.oModuleGlueDataFunctor`: the functor `SheafOfModules 𝒪 ⥤ OModuleGlueData 𝒪 U`.
* `TopCat.Sheaf.OModuleGlueData.glued`: the sheaf of `𝒪`-modules glued from a glueing datum.

## Main results

* `TopCat.Sheaf.sheafOfModulesEquivGlueData`: **Stacks 00AN** for sheaves of `𝒪`-modules.

As in the proof of Stacks 00AN, the functor is fully faithful because maps of sheaves of
`𝒪`-modules glue (`TopCat.Sheaf.existsUnique_hom_of_localModuleHom`), and it is essentially
surjective by the glueing of Stacks 00AL and 00AM (`TopCat.Sheaf.OModuleGlueData.glued` together
with `TopCat.Sheaf.OModuleGlueData.sectionsLinearEquiv`).

## Implementation notes

As in `StacksFrontier/Topology/Sheaves/Glueing/Equivalence.lean`, the comparison isomorphisms of the
glueing datum attached to a sheaf `M` are literally the identity: the sections of `M|_{U i}` over
an open `V ≤ U i` are the sections `M(V)`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {ι : Type u} {U : ι → Opens X}

/-! ### The category of glueing data of sheaves of `𝒪`-modules -/

namespace OModuleGlueData

variable {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}

/-- A morphism of glueing data of sheaves of `𝒪`-modules: an `𝒪(V)`-linear map of the local
sheaves over each open `V ≤ U i`, compatible with restriction and with the comparison
isomorphisms over the overlaps. -/
@[ext]
structure Hom (D E : OModuleGlueData 𝒪 U) where
  /-- The `𝒪(V)`-linear map on sections over an open `V ≤ U i`. -/
  app : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i),
    (D.sheaf i).obj V hV →ₗ[𝒪.obj (op V)] (E.sheaf i).obj V hV
  /-- Compatibility with the restriction maps. -/
  naturality : ∀ (i : ι) {V W : Opens X} (hV : V ≤ U i) (hWV : W ≤ V)
      (s : (D.sheaf i).obj V hV),
      app i W (hWV.trans hV) ((D.sheaf i).map hWV s) = (E.sheaf i).map hWV (app i V hV s)
  /-- Compatibility with the comparison isomorphisms. -/
  trans_app : ∀ (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j)
      (s : (D.sheaf i).obj V hi),
      app j V hj (D.trans i j hi hj s) = E.trans i j hi hj (app i V hi s)

/-- Glueing data of sheaves of `𝒪`-modules with respect to a fixed family of opens form a
category. -/
instance : Category.{u} (OModuleGlueData 𝒪 U) where
  Hom D E := Hom D E
  id D := ⟨fun _ _ _ => LinearMap.id, by intros; rfl, by intros; rfl⟩
  comp f g := ⟨fun i V hV => (g.app i V hV).comp (f.app i V hV),
    by
      intro i V W hV hWV s
      rw [LinearMap.comp_apply, LinearMap.comp_apply, f.naturality, g.naturality],
    by
      intro i j V hi hj s
      rw [LinearMap.comp_apply, LinearMap.comp_apply, f.trans_app, g.trans_app]⟩
  id_comp _ := Hom.ext rfl
  comp_id _ := Hom.ext rfl
  assoc _ _ _ := Hom.ext rfl

end OModuleGlueData

variable {𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-! ### The functor from sheaves of `𝒪`-modules to glueing data -/

/-- The restriction of a presheaf of `𝒪`-modules to the opens contained in `W`. -/
noncomputable abbrev _root_.PresheafOfModules.toOModuleLocalPresheaf
    {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} 𝒪) (W : Opens X) :
    OModuleLocalPresheaf 𝒪 W where
  obj V _ := M.obj (op V)
  map hWV := M.resLE hWV
  map_id s := by
    rw [PresheafOfModules.resLE_apply,
      show (homOfLE (le_refl _) : _ ⟶ _).op = 𝟙 _ from Subsingleton.elim _ _,
      PresheafOfModules.map_id]
    rfl
  map_map hWV hZW s := M.resLE_resLE hWV hZW s

/-- The restriction of a sheaf of `𝒪`-modules to an open `W` is a sheaf. -/
theorem _root_.PresheafOfModules.isSheaf_toOModuleLocalPresheaf
    {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{u} 𝒪}
    (hM : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) M.presheaf)
    (W : Opens X) : (M.toOModuleLocalPresheaf W).IsSheaf :=
  TopCat.Presheaf.isSheaf_toLocalPresheaf
    (CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ _
      (CategoryTheory.forget AddCommGrpCat.{u}) hM) W

variable (U) in
/-- The functor sending a sheaf of `𝒪`-modules on `X` to its glueing data with respect to the
family `U`. The comparison isomorphisms of the resulting glueing datum are the identity. -/
noncomputable abbrev oModuleGlueDataFunctor : SheafOfModules.{u} 𝒪 ⥤ OModuleGlueData 𝒪.obj U where
  obj M :=
    { sheaf := fun i => M.val.toOModuleLocalPresheaf (U i)
      isSheaf := fun i => PresheafOfModules.isSheaf_toOModuleLocalPresheaf M.isSheaf (U i)
      trans := fun _ _ _ _ _ => LinearEquiv.refl _ _
      trans_map := by intros; rfl
      trans_trans := by intros; rfl }
  map ψ :=
    { app := fun _ V _ => (ψ.val.app (op V)).hom
      naturality := fun _ _ _ _ hWV s => PresheafOfModules.app_resLE ψ.val hWV s
      trans_app := by intros; rfl }
  map_id _ := OModuleGlueData.Hom.ext rfl
  map_comp _ _ := OModuleGlueData.Hom.ext rfl

/-- The local maps of `𝒪`-modules underlying a morphism of the glueing data attached to two
sheaves of `𝒪`-modules. -/
noncomputable def localModuleHomOfHom {M N : SheafOfModules.{u} 𝒪}
    (f : (oModuleGlueDataFunctor U).obj M ⟶ (oModuleGlueDataFunctor U).obj N) (i : ι) :
    LocalModuleHom M.val N.val (U i) where
  app V hV := ModuleCat.ofHom (f.app i V hV)
  naturality {_ _} hV hWV s := f.naturality i hV hWV s

/-- The local maps of `localModuleHomOfHom` agree on the overlaps: this is the compatibility of
`f` with the comparison isomorphisms, which are the identity here. -/
theorem localModuleHomOfHom_agree {M N : SheafOfModules.{u} 𝒪}
    (f : (oModuleGlueDataFunctor U).obj M ⟶ (oModuleGlueDataFunctor U).obj N) (i j : ι)
    (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j) :
    (localModuleHomOfHom f i).app V hVi = (localModuleHomOfHom f j).app V hVj :=
  ModuleCat.hom_ext (LinearMap.ext fun s => (f.trans_app i j hVi hVj s).symm)

/-- The glueing data functor for sheaves of `𝒪`-modules is faithful: a map of sheaves of
`𝒪`-modules is determined by its restrictions to the members of an open covering. -/
theorem oModuleGlueDataFunctor_faithful (hU : ⨆ i, U i = ⊤) :
    (oModuleGlueDataFunctor (𝒪 := 𝒪) U).Faithful where
  map_injective {_} {N} {ψ} {_} h :=
    SheafOfModules.hom_ext <| eq_hom_of_restrict hU N.isSheaf
      (fun _ V _ => ψ.val.app (op V)) (fun _ _ _ => rfl) fun i V hV =>
        ModuleCat.hom_ext (congrArg (fun m : OModuleGlueData.Hom _ _ => m.app i V hV) h).symm

/-- The glueing data functor for sheaves of `𝒪`-modules is full: local maps agreeing on the
overlaps glue to a map of sheaves of `𝒪`-modules. -/
theorem oModuleGlueDataFunctor_full (hU : ⨆ i, U i = ⊤) :
    (oModuleGlueDataFunctor (𝒪 := 𝒪) U).Full where
  map_surjective {M} {N} f := by
    obtain ⟨ψ, hψ, -⟩ := existsUnique_hom_of_localModuleHom U hU M.val N.val N.isSheaf
      (localModuleHomOfHom f) (localModuleHomOfHom_agree f)
    exact ⟨⟨ψ⟩, OModuleGlueData.Hom.ext (funext fun i => funext fun V => funext fun hV =>
      congrArg ModuleCat.Hom.hom (hψ i V hV))⟩

/-! ### The quasi-inverse -/

namespace OModuleGlueData

variable (D : OModuleGlueData 𝒪.obj U)

/-- **The sheaf of `𝒪`-modules glued from a glueing datum** (Stacks 00AL and 00AM). -/
noncomputable abbrev glued : SheafOfModules.{u} 𝒪 :=
  ⟨D.gluedPresheafOfModules, D.isSheaf_gluedPresheafOfModules⟩

/-- The glueing data of the sheaf of `𝒪`-modules glued from `D` is isomorphic to `D`, via the
comparison isomorphisms of Stacks 00AL. -/
noncomputable def gluedIso : (oModuleGlueDataFunctor U).obj D.glued ≅ D where
  hom :=
    { app := fun i _ hV => (D.sectionsLinearEquiv i hV).toLinearMap
      naturality := fun i _ _ hV hWV s => D.toAddGlueData.toGlueData.sectionsEquiv_map i hV hWV s
      trans_app := fun i j _ hi hj s =>
        (D.toAddGlueData.toGlueData.trans_sectionsEquiv i j hi hj s).symm }
  inv :=
    { app := fun i _ hV => (D.sectionsLinearEquiv i hV).symm.toLinearMap
      naturality := fun i _ _ hV hWV s =>
        D.toAddGlueData.toGlueData.sectionsEquiv_symm_map i hV hWV s
      trans_app := fun i j _ hi hj s =>
        D.toAddGlueData.toGlueData.trans_sectionsEquiv_symm i j hi hj s }
  hom_inv_id := Hom.ext (funext fun i => funext fun _ => funext fun hV =>
    LinearMap.ext fun s => (D.sectionsLinearEquiv i hV).symm_apply_apply s)
  inv_hom_id := Hom.ext (funext fun i => funext fun _ => funext fun hV =>
    LinearMap.ext fun s => (D.sectionsLinearEquiv i hV).apply_symm_apply s)

end OModuleGlueData

/-- The glueing data functor for sheaves of `𝒪`-modules is essentially surjective: every glueing
datum is the glueing data of the sheaf of `𝒪`-modules glued from it. -/
theorem oModuleGlueDataFunctor_essSurj : (oModuleGlueDataFunctor (𝒪 := 𝒪) U).EssSurj where
  mem_essImage D := ⟨D.glued, ⟨D.gluedIso⟩⟩

/-- **Stacks 00AN, sheaves of `𝒪`-modules.** Let `𝒪` be a sheaf of rings on a topological space
`X` and let `X = ⋃ i, U i` be an open covering. Restriction to the members of the covering is an
equivalence between the category of sheaves of `𝒪`-modules on `X` and the category of glueing
data of sheaves of `𝒪`-modules with respect to the covering. -/
@[stacks 00AN "sheaves of O-modules"]
noncomputable def sheafOfModulesEquivGlueData (hU : ⨆ i, U i = ⊤) :
    SheafOfModules.{u} 𝒪 ≌ OModuleGlueData 𝒪.obj U :=
  haveI := oModuleGlueDataFunctor_faithful (𝒪 := 𝒪) hU
  haveI := oModuleGlueDataFunctor_full (𝒪 := 𝒪) hU
  haveI := oModuleGlueDataFunctor_essSurj (𝒪 := 𝒪) (U := U)
  haveI : (oModuleGlueDataFunctor (𝒪 := 𝒪) U).IsEquivalence := {}
  (oModuleGlueDataFunctor U).asEquivalence

end TopCat.Sheaf
