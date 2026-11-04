module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.ChartQuotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.LeftDualOnSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Evaluation of the dual at a local section, tensored with a module

Let `Y` be a scheme, `L` and `G` modules on `Y`, `V ⊆ Y` an open and `ω ∈ Γ(V, L)`.  A local
functional `λ` on `L` and a local section `g` of `G` give the local section `λ(ω) g` of `G` over
the part of their domain inside `V`.  This is bilinear, so it defines a morphism

`ev_ω : L^∨ ⊗ G ⟶ j_*(G|_V)`,

`λ ⊗ g ↦ λ(ω) g`.  It is the evaluation of the twist of Stacks 0G7T at the wedge of a family of
equations.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory
open Stacks.SheafOfModules.OnSpace (dualSheaf dualValue)
open Stacks.Perfect.SupportedFraction (globalSmul)

universe u

namespace Stacks.Perfect.ConormalClass

variable {Y : Scheme.{u}}

/-- A restriction map of the sections of a module is any chain of two restriction maps with the
same endpoints. -/
theorem modules_map_eq_map_map {Y' : Scheme.{u}} (M : Y'.Modules) {A B C : Y'.Opens} (a : C ⟶ A)
    (b : B ⟶ A) (c : C ⟶ B) (y : Γ(M, A)) :
    M.presheaf.map a.op y = M.presheaf.map c.op (M.presheaf.map b.op y) := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  exact congrArg (fun g => ConcreteCategory.hom (M.presheaf.map g) y)
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

section Sections

variable (V : Y.Opens) (G : Y.Modules)

/-- Scalars acting on the direct image of the restriction to `V`, on sections. -/
theorem push_res_smul (P : Y.Opens) (r : Γ(Y, P)) (n : Γ((push V).obj ((res V).obj G), P)) :
    r • n = (Y.presheaf.map (homOfLE (V.ι.image_preimage_le P)).op r •
      (show Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ P)) from n) : Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ P))) := by
  show (V.ι.app P r) • (show Γ((res V).obj G, V.ι ⁻¹ᵁ P) from n) = _
  refine (restrict_smul G V _ _ _).trans ?_
  congr 1

end Sections

section Evaluation

variable (L G : Y.Modules) (V : Y.Opens) (ω : Γ(L, V))

/-- The part of an open `P` inside `V`, as an object over `P`. -/
abbrev interOver (P : Y.Opens) : Over P := Over.mk (homOfLE (V.ι.image_preimage_le P))

/-- **The value `λ(ω) g`** of a local functional `λ` on `L` over `P` at `ω`, times a local
section `g` of `G` over `P`, on the part of `P` inside `V`. -/
def evalSmul (P : Y.Opens) (lam : (dualSheaf Y.toRingedSpace L).val.obj (op P)) (g : Γ(G, P)) :
    Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ P)) :=
  (show Γ(Y, V.ι ''ᵁ (V.ι ⁻¹ᵁ P)) from dualValue Y.toRingedSpace L lam (op (interOver V P))
      (L.presheaf.map (homOfLE (V.ι_image_le _)).op ω)) •
    G.presheaf.map (homOfLE (V.ι.image_preimage_le P)).op g

/-- The value `λ(ω) g` is additive in the functional `λ`. -/
theorem evalSmul_add_left (P : Y.Opens) (lam lam' : (dualSheaf Y.toRingedSpace L).val.obj (op P))
    (g : Γ(G, P)) :
    evalSmul L G V ω P (lam + lam') g = evalSmul L G V ω P lam g + evalSmul L G V ω P lam' g :=
  add_smul _ _ _

/-- The value `λ(ω) g` is additive in the section `g`. -/
theorem evalSmul_add_right (P : Y.Opens) (lam : (dualSheaf Y.toRingedSpace L).val.obj (op P))
    (g g' : Γ(G, P)) :
    evalSmul L G V ω P lam (g + g') = evalSmul L G V ω P lam g + evalSmul L G V ω P lam g' := by
  rw [evalSmul, evalSmul, evalSmul, map_add, smul_add]

/-- The value `(r λ)(ω) g` is `r` times `λ(ω) g`. -/
theorem evalSmul_smul_left (P : Y.Opens) (r : Γ(Y, P))
    (lam : (dualSheaf Y.toRingedSpace L).val.obj (op P)) (g : Γ(G, P)) :
    evalSmul L G V ω P (r • lam) g =
      (Y.presheaf.map (homOfLE (V.ι.image_preimage_le P)).op r • evalSmul L G V ω P lam g :
        Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ P))) :=
  mul_smul _ _ _

/-- The value `λ(ω) (r g)` is `r` times `λ(ω) g`. -/
theorem evalSmul_smul_right (P : Y.Opens) (r : Γ(Y, P))
    (lam : (dualSheaf Y.toRingedSpace L).val.obj (op P)) (g : Γ(G, P)) :
    evalSmul L G V ω P lam (r • g) =
      (Y.presheaf.map (homOfLE (V.ι.image_preimage_le P)).op r • evalSmul L G V ω P lam g :
        Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ P))) := by
  rw [evalSmul, evalSmul, Scheme.Modules.map_smul, smul_comm]

/-- For opens `P₂ ⊆ P`, the part of `P₂` inside `V` is contained in the part of `P` inside `V`. -/
theorem interOver_mono {P₂ P : Y.Opens} (k : P₂ ≤ P) :
    V.ι ''ᵁ (V.ι ⁻¹ᵁ P₂) ≤ V.ι ''ᵁ (V.ι ⁻¹ᵁ P) :=
  V.ι.image_mono (V.ι.preimage_mono k)

/-- The value of a local functional at a section is natural along a morphism of opens over `P`. -/
private theorem dualValue_map_left (L : Y.Modules) {P : Y.Opens}
    (lam : (dualSheaf Y.toRingedSpace L).val.obj (op P)) {A B : Over P} (φ : A ⟶ B)
    (a : Γ(L, A.left)) (b : Γ(L, B.left)) (h : L.presheaf.map φ.left.op b = a) :
    dualValue Y.toRingedSpace L lam (op A) a =
      Y.presheaf.map φ.left.op (dualValue Y.toRingedSpace L lam (op B) b) := by
  subst h
  exact congrArg (fun q => q.hom b) (lam.naturality φ.op)

/-- **The value `λ(ω) g` commutes with restriction.** -/
theorem evalSmul_restrict {P₂ P : Y.Opens} (k : P₂ ≤ P)
    (lam : (dualSheaf Y.toRingedSpace L).val.obj (op P)) (g : Γ(G, P)) :
    G.presheaf.map (homOfLE (interOver_mono V k)).op (evalSmul L G V ω P lam g) =
      evalSmul L G V ω P₂ ((dualSheaf Y.toRingedSpace L).val.map (homOfLE k).op lam)
        (G.presheaf.map (homOfLE k).op g) := by
  let φ : (Over.map (homOfLE k)).obj (interOver V P₂) ⟶ interOver V P :=
    Over.homMk (homOfLE (interOver_mono V k)) (Subsingleton.elim _ _)
  have hval := dualValue_map_left L lam φ
    (L.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ P₂))).op ω)
    (L.presheaf.map (homOfLE (V.ι_image_le _)).op ω)
    (modules_map_map_eq L _ _ _ (𝟙 _) ω |>.trans (by rw [op_id, L.presheaf.map_id]; rfl))
  refine (Scheme.Modules.map_smul G (homOfLE (interOver_mono V k)) _ _).trans ?_
  exact congrArg₂ (fun (a : Γ(Y, V.ι ''ᵁ (V.ι ⁻¹ᵁ P₂))) (b : Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ P₂))) => a • b)
    hval.symm (modules_map_map_eq G _ _ _ _ g)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules in
/-- **The evaluation at `ω`**, on the pointwise tensor product of presheaves of modules. -/
def evalPresheaf : PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf)
      (dualSheaf Y.toRingedSpace L).val G.val ⟶ ((push V).obj ((res V).obj G)).val := by
  refine PresheafOfModules.Hom.mk (fun U => ?_) ?_
  · exact ModuleCat.MonoidalCategory.tensorLift (fun lam g => evalSmul L G V ω U.unop lam g)
      (fun lam lam' g => evalSmul_add_left L G V ω U.unop lam lam' g)
      (fun r lam g => (evalSmul_smul_left L G V ω U.unop r lam g).trans
        (push_res_smul V G U.unop r _).symm)
      (fun lam g g' => evalSmul_add_right L G V ω U.unop lam g g')
      (fun r lam g => (evalSmul_smul_right L G V ω U.unop r lam g).trans
        (push_res_smul V G U.unop r _).symm)
  · intro U U' i
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro lam g
    exact (evalSmul_restrict L G V ω i.unop.le lam g).symm

end Evaluation

/-- **The monoidal structure of Stacks 01CA on the modules of a scheme**, at the `Y.Modules`
spelling. -/
@[instance_reducible]
noncomputable def modulesMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal Y.toRingedSpace

attribute [local instance] modulesMonoidal

/-- The dual `L^∨ = SheafHom(L, 𝒪_Y)` of a module on a scheme, at the `Y.Modules` spelling. -/
@[sga "3 III 0.6"]
abbrev dualModule (L : Y.Modules) : Y.Modules := dualSheaf Y.toRingedSpace L

section Sheaf

variable (L G : Y.Modules) (V : Y.Opens) (ω : Γ(L, V))

/-- **The evaluation `ev_ω : L^∨ ⊗ G ⟶ j_*(G|_V)`, `λ ⊗ g ↦ λ(ω) g`.** -/
def evalAt : dualModule L ⊗ G ⟶ (push V).obj ((res V).obj G) :=
  ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property).homEquiv
      (PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf)
        (dualSheaf Y.toRingedSpace L).val G.val) _).symm (evalPresheaf L G V ω)

/-- `ev_ω` on a local pure tensor. -/
theorem evalAt_tmul (P : Y.Opens) (lam : (dualSheaf Y.toRingedSpace L).val.obj (op P))
    (g : Γ(G, P)) :
    ((evalAt L G V ω).val.app (op P)).hom
      (Stacks.SheafOfModules.OnSpace.tensorObjTmul Y.toRingedSpace (dualModule L) G (op P) lam g) =
      evalSmul L G V ω P lam g := by
  have h := ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction
    Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property).homEquiv
      (PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf)
        (dualSheaf Y.toRingedSpace L).val G.val)
      ((push V).obj ((res V).obj G))).apply_symm_apply (evalPresheaf L G V ω)
  exact congrArg (fun q => (q.app (op P)).hom (lam ⊗ₜ[Y.presheaf.obj (op P)] g)) h

/-- The value at a multiple of `ω` is the multiple of the value. -/
theorem evalSmul_smul_section (a : Γ(Y, V)) (P : Y.Opens)
    (lam : (dualSheaf Y.toRingedSpace L).val.obj (op P)) (g : Γ(G, P)) :
    evalSmul L G V (a • ω) P lam g =
      (Y.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ P))).op a • evalSmul L G V ω P lam g :
        Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ P))) := by
  have h1 : L.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ P))).op (a • ω) =
      Y.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ P))).op a •
        L.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ P))).op ω :=
    Scheme.Modules.map_smul L _ a ω
  refine (congrArg (fun x => (show Γ(Y, V.ι ''ᵁ (V.ι ⁻¹ᵁ P)) from
    dualValue Y.toRingedSpace L lam (op (interOver V P)) x) •
      G.presheaf.map (homOfLE (V.ι.image_preimage_le P)).op g) h1).trans ?_
  refine (congrArg (fun r : Γ(Y, V.ι ''ᵁ (V.ι ⁻¹ᵁ P)) =>
    r • G.presheaf.map (homOfLE (V.ι.image_preimage_le P)).op g)
    ((lam.app (op (interOver V P))).hom.map_smul _ _)).trans ?_
  exact mul_smul _ _ _

/-- **Evaluation at a multiple.** `ev_{aω}` is `ev_ω` followed by multiplication by `a`. -/
theorem evalAt_smul (a : Γ(Y, V)) :
    evalAt L G V (a • ω) = evalAt L G V ω ≫ (push V).map
      (globalSmul (Y.presheaf.map (homOfLE V.ι_image_top.le).op a) ((res V).obj G)) := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext Y.toRingedSpace fun U lam g => ?_
  obtain ⟨P⟩ := U
  refine (evalAt_tmul L G V (a • ω) P lam g).trans ?_
  refine Eq.trans ?_ (congrArg ((((push V).map (globalSmul (Y.presheaf.map
    (homOfLE V.ι_image_top.le).op a) ((res V).obj G))).val.app (op P)).hom)
      (evalAt_tmul L G V ω P lam g)).symm
  refine Eq.trans ?_ (globalSmul_res_app V G _ (V.ι ⁻¹ᵁ P) _).symm
  have hr : restrictFun V (V.ι_image_le (V.ι ⁻¹ᵁ P))
      (Y.presheaf.map (homOfLE V.ι_image_top.le).op a) =
      Y.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ P))).op a :=
    restrictFun_chartEq V (fun _ : Fin 1 => a) _ 0
  refine (evalSmul_smul_section L G V ω a P lam g).trans ?_
  exact congrArg (fun r : Γ(Y, V.ι ''ᵁ (V.ι ⁻¹ᵁ P)) => r • evalSmul L G V ω P lam g) hr.symm

/-- **Naturality of the evaluation in the module tensored with.** -/
theorem evalAt_natural {G' : Y.Modules} (ψ : G ⟶ G') :
    (dualModule L ◁ ψ) ≫ evalAt L G' V ω = evalAt L G V ω ≫ (push V).map ((res V).map ψ) := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext Y.toRingedSpace fun U lam g => ?_
  obtain ⟨P⟩ := U
  refine (congrArg ((evalAt L G' V ω).val.app (op P)).hom
    (Stacks.SheafOfModules.OnSpace.whiskerLeft_tmul Y.toRingedSpace (dualModule L) ψ (op P)
      lam g)).trans ?_
  refine (evalAt_tmul L G' V ω P lam _).trans ?_
  refine Eq.trans ?_ (congrArg ((((push V).map ((res V).map ψ)).val.app (op P)).hom)
      (evalAt_tmul L G V ω P lam g)).symm
  refine Eq.trans ?_ (Scheme.Modules.Hom.app_smul ψ _ _).symm
  exact congrArg (fun y : Γ(G', V.ι ''ᵁ (V.ι ⁻¹ᵁ P)) => (show Γ(Y, V.ι ''ᵁ (V.ι ⁻¹ᵁ P)) from
      dualValue Y.toRingedSpace L lam (op (interOver V P))
        (L.presheaf.map (homOfLE (V.ι_image_le _)).op ω)) • y)
    (congrArg (fun q => q.hom g) (ψ.val.naturality (homOfLE (V.ι.image_preimage_le P)).op)).symm

end Sheaf

/-! ### Restricting to a smaller open -/

section Restrict

/-- For opens `V₂ ⊆ V`, the part of `P` inside `V₂` is contained in the part of `P` inside `V`. -/
theorem inter_mono_restrict {V₂ V : Y.Opens} (h : V₂ ≤ V) (P : Y.Opens) :
    V₂.ι ''ᵁ (V₂.ι ⁻¹ᵁ P) ≤ V.ι ''ᵁ (V.ι ⁻¹ᵁ P) := by
  rw [V₂.ι.image_preimage_eq_opensRange_inf, V.ι.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
  exact inf_le_inf_right _ h

variable {V₂ V : Y.Opens} (h : V₂ ≤ V) (G : Y.Modules)

/-- The restriction `j_*(G|_V) ⟶ j_*(G|_{V₂})` for `V₂ ⊆ V`. -/
def pushRestrict : (push V).obj ((res V).obj G) ⟶ (push V₂).obj ((res V₂).obj G) :=
  Stacks.AlgebraicGeometry.ModuleLimits.homOfSections
    (fun P n => G.presheaf.map (homOfLE (inter_mono_restrict h P)).op
      (show Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ P)) from n))
    (fun _ _ _ => map_add _ _ _)
    (fun P r n => by
      refine (congrArg (G.presheaf.map (homOfLE (inter_mono_restrict h P)).op)
        (push_res_smul V G P r n)).trans ?_
      refine (Scheme.Modules.map_smul G _ _ _).trans ?_
      refine Eq.trans ?_ (push_res_smul V₂ G P r _).symm
      exact congrArg (fun a : Γ(Y, V₂.ι ''ᵁ (V₂.ι ⁻¹ᵁ P)) =>
        a • G.presheaf.map (homOfLE (inter_mono_restrict h P)).op
          (show Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ P)) from n))
        (presheaf_map_map_eq Y.presheaf _ _ _ (𝟙 _) r |>.trans (by
          rw [Y.presheaf.map_id]; rfl)))
    (fun P P' hPP' n => modules_map_map_eq G (homOfLE (interOver_mono V hPP'))
      (homOfLE (inter_mono_restrict h P)) (homOfLE (inter_mono_restrict h P'))
      (homOfLE (interOver_mono V₂ hPP')) (show Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ P')) from n))

/-- On sections over `P`, `pushRestrict` is the restriction map of `G`. -/
theorem pushRestrict_app (P : Y.Opens) (n : Γ((push V).obj ((res V).obj G), P)) :
    (pushRestrict h G).app P n = G.presheaf.map (homOfLE (inter_mono_restrict h P)).op
      (show Γ(G, V.ι ''ᵁ (V.ι ⁻¹ᵁ P)) from n) :=
  rfl

variable (L : Y.Modules) (ω : Γ(L, V))

/-- **Evaluation at a restriction.** `ev_{ω|_{V₂}}` is `ev_ω` followed by the restriction. -/
theorem evalAt_restrict :
    evalAt L G V₂ (L.presheaf.map (homOfLE h).op ω) = evalAt L G V ω ≫ pushRestrict h G := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext Y.toRingedSpace fun U lam g => ?_
  obtain ⟨P⟩ := U
  refine (evalAt_tmul L G V₂ _ P lam g).trans ?_
  refine Eq.trans ?_ (congrArg (((pushRestrict h G).val.app (op P)).hom)
      (evalAt_tmul L G V ω P lam g)).symm
  let φ : interOver V₂ P ⟶ interOver V P :=
    Over.homMk (homOfLE (inter_mono_restrict h P)) (Subsingleton.elim _ _)
  have hval := dualValue_map_left L lam φ
    (L.presheaf.map (homOfLE (V₂.ι_image_le (V₂.ι ⁻¹ᵁ P))).op (L.presheaf.map (homOfLE h).op ω))
    (L.presheaf.map (homOfLE (V.ι_image_le _)).op ω) (modules_map_map_eq L _ _ _ _ ω)
  refine Eq.trans ?_ (Scheme.Modules.map_smul G (homOfLE (inter_mono_restrict h P)) _ _).symm
  exact congrArg₂ (fun (a : Γ(Y, V₂.ι ''ᵁ (V₂.ι ⁻¹ᵁ P))) (b : Γ(G, V₂.ι ''ᵁ (V₂.ι ⁻¹ᵁ P))) =>
      a • b) hval (modules_map_eq_map_map G _ _ _ g)

end Restrict

end Stacks.Perfect.ConormalClass
