module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestrictionOfLE
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictOpen
public import StacksFrontier.Topology.Sheaves.OpenImmersion.Coefficients

/-!
# Stacks 00A0 for (pre)sheaves of modules

Let `j : U ⟶ X` be an open embedding of topological spaces (the inclusion of an open subset in
Stacks 00A0), and let `R` be a presheaf (resp. sheaf) of rings on `X`, with restriction
`R|_U : V ↦ R(j V)`. Stacks 00A0 says that the descriptions of `j_p`, `j⁻¹` and their
interaction with `j_*` hold for (pre)sheaves of modules as well. Here `j⁻¹ G` of an
`R`-module `G` is a module over `j⁻¹ R = R|_U` (Stacks 008T, 008X), and `j_p`, `j⁻¹` are
characterized as the left adjoints of `j_*` from `R|_U`-modules to `R`-modules, the
`R`-module structure on `j_* F` coming from `R ⟶ j_* (R|_U)` (Stacks 008U, 008Y).

* (1) `restrictPresheafOfModulesAdjunction`: restriction of presheaves of `R`-modules,
  `G ↦ (V ↦ G(V))` as a presheaf of `R|_U`-modules, is left adjoint to `j_*`; so it is `j_p`.
  `restrictPresheafOfModulesIsoPullback` identifies it with Mathlib's
  `PresheafOfModules.pullback` when the latter exists.
* (4) `isIso_restrictPresheafOfModulesAdjunction_counit`: the counit `j_p j_* ⟶ 𝟭` is an
  isomorphism.
* (2) `restrictSheafOfModulesIsoPullback`: for sheaves of modules, the restriction
  `Stacks.SheafOfModules.restrictSheafOfModules` (left adjoint to `j_*` by
  `Stacks.SheafOfModules.restrictSheafOfModulesAdj`) is isomorphic to Mathlib's
  `SheafOfModules.pullback` along `R ⟶ j_* (R|_U)`, the left adjoint of `j_*`.
* (5) `isIso_restrictSheafOfModulesAdj_counit`: the counit `j⁻¹ j_* ⟶ 𝟭` is an isomorphism.
* (3) `Stacks.SheafOfModules.stalkRestrictIso` (registered here): the stalk of `G|_U` at `u` is
  the stalk of `G` at `j u`, semilinearly over the identification of stalks of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

universe v w u

namespace OpenImmersionSheaves

section Presheaf

variable {X U : TopCat.{u}} (j : U ⟶ X)
  (hj : Topology.IsOpenEmbedding (ConcreteCategory.hom j)) (R : X.Presheaf RingCat.{w})

/-- The restriction functor on presheaves of modules: a presheaf of `R`-modules `G` goes to
`V ↦ G(j V)`, a presheaf of modules over `R|_U = hj.functor.op ⋙ R`. -/
noncomputable abbrev restrictPresheafOfModules :
    PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (hj.functor.op ⋙ R) :=
  PresheafOfModules.pushforward (F := hj.functor) (𝟙 (hj.functor.op ⋙ R))

/-- The ring map `R ⟶ j_* (R|_U)`: on an open `W` of `X` it is restriction
`R(W) ⟶ R(j(j⁻¹ W))`. -/
noncomputable def ringHomPushforwardRestrict :
    R ⟶ (Opens.map j).op ⋙ hj.functor.op ⋙ R :=
  Functor.whiskerRight (NatTrans.op hj.isOpenMap.adjunction.counit) R

/-- The pushforward `j_*` from presheaves of `R|_U`-modules to presheaves of `R`-modules. -/
noncomputable abbrev pushforwardPresheafOfModules :
    PresheafOfModules.{v} (hj.functor.op ⋙ R) ⥤ PresheafOfModules.{v} R :=
  PresheafOfModules.pushforward (F := Opens.map j) (ringHomPushforwardRestrict j hj R)

/-- The unit `G ⟶ j_* (G|_U)`, restriction `G(W) ⟶ G(j(j⁻¹ W))`. -/
noncomputable def restrictPresheafOfModulesUnitApp (G : PresheafOfModules.{v} R) :
    G ⟶ (pushforwardPresheafOfModules j hj R).obj ((restrictPresheafOfModules j hj R).obj G) :=
  PresheafOfModules.homMk ((restrictPresheafAdjunction Ab.{v} j hj).unit.app G.presheaf)
    (fun W r m => G.map_smul (hj.isOpenMap.adjunction.counit.app W.unop).op r m)

/-- Restricting `R(j V) ⟶ R(j(j⁻¹(j V)))` back to `R(j V)` is the identity. -/
theorem ringHomPushforwardRestrict_map (V : (Opens U)ᵒᵖ) (r : R.obj (op (hj.functor.obj V.unop))) :
    (hj.functor.op ⋙ R).map (hj.isOpenMap.adjunction.unit.app V.unop).op
      ((ringHomPushforwardRestrict j hj R).app (op (hj.functor.obj V.unop)) r) = r := by
  change (R.map (hj.isOpenMap.adjunction.counit.app (hj.functor.obj V.unop)).op ≫
    R.map (hj.functor.map (hj.isOpenMap.adjunction.unit.app V.unop)).op) r = r
  rw [← R.map_comp, show (_ ≫ _ : op (hj.functor.obj V.unop) ⟶ op (hj.functor.obj V.unop)) = 𝟙 _
    from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]
  simp

/-- The counit `(j_* F)|_U ⟶ F`, restriction `F(j⁻¹(j V)) ⟶ F(V)`. -/
noncomputable def restrictPresheafOfModulesCounitApp
    (F : PresheafOfModules.{v} (hj.functor.op ⋙ R)) :
    (restrictPresheafOfModules j hj R).obj ((pushforwardPresheafOfModules j hj R).obj F) ⟶ F :=
  PresheafOfModules.homMk ((restrictPresheafAdjunction Ab.{v} j hj).counit.app F.presheaf)
    (fun V r m => (F.map_smul (hj.isOpenMap.adjunction.unit.app V.unop).op _ m).trans
      (congrArg (fun s => s • _) (ringHomPushforwardRestrict_map j hj R V r)))

/-- **Stacks 00A0 (1), for presheaves of modules.** Restriction of presheaves of `R`-modules
along the open embedding `j`, `G ↦ (V ↦ G(V))` as a presheaf of `R|_U`-modules, is left adjoint
to the pushforward `j_*` (with `R`-module structure through `R ⟶ j_* (R|_U)`). Since `j_p` on
presheaves of modules is the left adjoint of `j_*` (Stacks 008U), this says that `j_p G` is
given by `V ↦ G(V)`. Its underlying adjunction of presheaves of abelian groups is
`restrictPresheafAdjunction Ab j hj`. -/
@[stacks 00A0 "(1) for presheaves of modules: restriction is left adjoint to `j_*`, i.e. is
  `j_p`"]
noncomputable def restrictPresheafOfModulesAdjunction :
    restrictPresheafOfModules.{v} j hj R ⊣ pushforwardPresheafOfModules.{v} j hj R where
  unit :=
    { app := restrictPresheafOfModulesUnitApp j hj R
      naturality := fun G H f => (PresheafOfModules.toPresheaf R).map_injective <| by
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
        exact (restrictPresheafAdjunction Ab.{v} j hj).unit.naturality
          ((PresheafOfModules.toPresheaf R).map f) }
  counit :=
    { app := restrictPresheafOfModulesCounitApp j hj R
      naturality := fun F F' f =>
        (PresheafOfModules.toPresheaf (hj.functor.op ⋙ R)).map_injective <| by
          rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
          exact (restrictPresheafAdjunction Ab.{v} j hj).counit.naturality
            ((PresheafOfModules.toPresheaf (hj.functor.op ⋙ R)).map f) }
  left_triangle_components G :=
    (PresheafOfModules.toPresheaf (hj.functor.op ⋙ R)).map_injective <| by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
      exact (restrictPresheafAdjunction Ab.{v} j hj).left_triangle_components G.presheaf
  right_triangle_components F := (PresheafOfModules.toPresheaf R).map_injective <| by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact (restrictPresheafAdjunction Ab.{v} j hj).right_triangle_components F.presheaf

/-- **Stacks 00A0 (4), for presheaves of modules.** The counit `j_p j_* ⟶ 𝟭` on presheaves of
`R|_U`-modules is an isomorphism: on underlying presheaves of abelian groups it is the counit of
`restrictPresheafAdjunction Ab j hj`, an isomorphism by `isIso_restrictPresheafAdjunction_counit`,
and the forgetful functor to presheaves of abelian groups reflects isomorphisms. -/
@[stacks 00A0 "(4) for presheaves of modules"]
theorem isIso_restrictPresheafOfModulesAdjunction_counit :
    IsIso (restrictPresheafOfModulesAdjunction.{v} j hj R).counit := by
  have hA := isIso_restrictPresheafAdjunction_counit Ab.{v} j hj
  have happ : ∀ F, IsIso ((restrictPresheafOfModulesAdjunction.{v} j hj R).counit.app F) := by
    intro F
    have : IsIso ((PresheafOfModules.toPresheaf _).map
        ((restrictPresheafOfModulesAdjunction.{v} j hj R).counit.app F)) :=
      inferInstanceAs (IsIso ((restrictPresheafAdjunction Ab.{v} j hj).counit.app F.presheaf))
    exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  exact NatIso.isIso_of_isIso_app _

instance : (pushforwardPresheafOfModules.{v} j hj R).IsRightAdjoint :=
  (restrictPresheafOfModulesAdjunction.{v} j hj R).isRightAdjoint

/-- **Stacks 00A0 (1), for presheaves of modules, Mathlib's pullback.** Mathlib's
`PresheafOfModules.pullback` along `R ⟶ j_* (R|_U)` — the left adjoint of `j_*` — is the
restriction `G ↦ (V ↦ G(V))`. -/
@[stacks 00A0 "(1) for presheaves of modules, Mathlib's `PresheafOfModules.pullback`"]
noncomputable def restrictPresheafOfModulesIsoPullback :
    restrictPresheafOfModules.{v} j hj R ≅
      PresheafOfModules.pullback.{v} (ringHomPushforwardRestrict j hj R) :=
  (restrictPresheafOfModulesAdjunction.{v} j hj R).leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction _)

end Presheaf

section Sheaf

open Stacks.SheafOfModules

variable {Y Z : TopCat.{u}} {f : Z ⟶ Y} (hf : Topology.IsOpenEmbedding f)
  (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{w})

/-- **Stacks 00A0 (5), for sheaves of modules.** The counit `j⁻¹ j_* ⟶ 𝟭` of the adjunction
`Stacks.SheafOfModules.restrictSheafOfModulesAdj` between restriction of sheaves of modules
along the open embedding `f` and `j_*` is an isomorphism: its component at `F` and `V` is
restriction along the equality `V = f⁻¹(f V)`. -/
@[stacks 00A0 "(5) for sheaves of modules"]
theorem isIso_restrictSheafOfModulesAdj_counit :
    IsIso (restrictSheafOfModulesAdj.{v} hf R).counit := by
  have hP := isIso_restrictPresheafOfModulesAdjunction_counit.{v} f hf R.obj
  have happ : ∀ F, IsIso ((restrictSheafOfModulesAdj.{v} hf R).counit.app F) := by
    intro F
    have h : (SheafOfModules.forget _).map ((restrictSheafOfModulesAdj.{v} hf R).counit.app F) =
        (restrictPresheafOfModulesAdjunction.{v} f hf R.obj).counit.app F.val := by
      ext V x
      rfl
    have : IsIso ((SheafOfModules.forget _).map
        ((restrictSheafOfModulesAdj.{v} hf R).counit.app F)) := by
      rw [h]
      exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hP F.val
    exact isIso_of_reflects_iso ((restrictSheafOfModulesAdj.{v} hf R).counit.app F)
      (SheafOfModules.forget _)
  exact NatIso.isIso_of_isIso_app _

/-- The pushforward of sheaves of modules along `R ⟶ j_* (R|_U)` is a right adjoint, with left
adjoint the restriction `Stacks.SheafOfModules.restrictSheafOfModules`. -/
instance isRightAdjoint_pushforward_pushforwardSheafOfRingsHom :
    (SheafOfModules.pushforward.{v} (pushforwardSheafOfRingsHom hf R)).IsRightAdjoint :=
  (restrictSheafOfModulesAdj.{v} hf R).isRightAdjoint

/-- **Stacks 00A0 (2), for sheaves of modules.** For a sheaf of `R`-modules `G`, `j⁻¹ G` — the
pullback of sheaves of modules along `R ⟶ j_* (R|_U)`, i.e. the left adjoint of `j_*` (Mathlib's
`SheafOfModules.pullback`, Stacks 008Y) — is given by the rule `V ↦ G(V)`: it is isomorphic to
the restriction `Stacks.SheafOfModules.restrictSheafOfModules hf R`, whose underlying presheaf
is `V ↦ G(f V)` and needs no sheafification. -/
@[stacks 00A0 "(2) for sheaves of modules: Mathlib's `SheafOfModules.pullback` is restriction"]
noncomputable def restrictSheafOfModulesIsoPullback :
    restrictSheafOfModules.{v} hf R ≅
      SheafOfModules.pullback.{v} (pushforwardSheafOfRingsHom hf R) :=
  (restrictSheafOfModulesAdj.{v} hf R).leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction _)

end Sheaf

add_to_stacks 00A0 "(3) for sheaves of modules: the stalk of the restriction of a sheaf of
  modules at `z` is its stalk at `f z`, semilinearly over the identification of stalks of rings"
  Stacks.SheafOfModules.stalkRestrictIso

end OpenImmersionSheaves
