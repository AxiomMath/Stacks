module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Base change of modules along a terminal object

Let `C` be a category with a terminal object `X` and let `O : Cᵒᵖ ⥤ RingCat` be a presheaf of
rings whose section rings are commutative. Write `R = O(X)`. Since `X` is terminal, `op X` is
initial in `Cᵒᵖ`, so every object `U` of `Cᵒᵖ` receives a unique morphism `ι_U : op X ⟶ U` and
hence a canonical ring map `ρ_U = O(ι_U) : R → O(U)`.

For an `R`-module `M` the assignment `U ↦ O(U) ⊗_R M` is a presheaf of `O`-modules, and the
resulting functor `baseChangePresheaf` is left adjoint to evaluation at `op X`. It is built by
composing the constant presheaf of modules over the constant presheaf of rings at `R` with the
change-of-rings functor along `ρ`.
-/

@[expose] public section

universe t v u r

open CategoryTheory CategoryTheory.Limits
open Stacks.PresheafOfModules.ChangeOfRings (ringPresheaf changeOfRings changeOfRingsAdjunction)

namespace Stacks.TerminalBaseChange

variable {C : Type u} [Category.{v} C]

/-- A presheaf of rings all of whose section rings are commutative. -/
class CommSections (O : Cᵒᵖ ⥤ RingCat.{r}) : Prop where
  /-- Multiplication in each section ring is commutative. -/
  mul_comm (U : Cᵒᵖ) (a b : O.obj U) : a * b = b * a

/-- A section ring of a presheaf of rings with commutative sections is a commutative ring, with
the ambient ring structure as its underlying ring. -/
instance commRingObj (O : Cᵒᵖ ⥤ RingCat.{r}) [CommSections O] (U : Cᵒᵖ) :
    CommRing (O.obj U) :=
  { (inferInstance : Ring (O.obj U)) with mul_comm := CommSections.mul_comm U }

section Iota

variable {X : C} (hX : IsTerminal X)

/-- The unique morphism `op X ⟶ U` in `Cᵒᵖ`, for `X` a terminal object of `C`. -/
def iota (U : Cᵒᵖ) : Opposite.op X ⟶ U := (hX.from U.unop).op

/-- `ι_U` followed by any morphism `U ⟶ V` is `ι_V`. -/
@[simp]
lemma iota_comp {U V : Cᵒᵖ} (a : U ⟶ V) : iota hX U ≫ a = iota hX V :=
  Quiver.Hom.unop_inj (hX.hom_ext _ _)

/-- `ι_{op X}` is the identity. -/
@[simp]
lemma iota_self : iota hX (Opposite.op X) = 𝟙 _ :=
  Quiver.Hom.unop_inj (hX.hom_ext _ _)

end Iota

variable (O : Cᵒᵖ ⥤ RingCat.{r}) [CommSections O]

/-- The lift of a presheaf of rings with commutative sections to a presheaf of commutative
rings; its underlying presheaf of rings is the original one. -/
def commPresheaf : Cᵒᵖ ⥤ CommRingCat.{r} where
  obj U := CommRingCat.of (O.obj U)
  map a := CommRingCat.ofHom (O.map a).hom
  map_id U := by rw [O.map_id]; rfl
  map_comp f g := by rw [O.map_comp]; rfl

/-- The underlying presheaf of rings of `commPresheaf O` is `O`. -/
lemma ringPresheaf_commPresheaf : ringPresheaf (commPresheaf O) = O := rfl

section Constant

variable (X : C)

/-- The constant presheaf of commutative rings with value the ring of sections `R = O(X)`. -/
def constRing : Cᵒᵖ ⥤ CommRingCat.{r} :=
  (Functor.const Cᵒᵖ).obj (CommRingCat.of (O.obj (Opposite.op X)))

/-- Every restriction map of the constant presheaf of rings is the identity. -/
lemma constRing_map_hom {U V : Cᵒᵖ} (a : U ⟶ V) :
    ((ringPresheaf (constRing O X)).map a).hom
      = RingHom.id ((ringPresheaf (constRing O X)).obj U) := by
  rw [show (ringPresheaf (constRing O X)).map a = 𝟙 ((ringPresheaf (constRing O X)).obj U) from
    CategoryTheory.Functor.map_id (forget₂ CommRingCat RingCat) _]
  exact RingCat.hom_id

/-- The constant presheaf of `R`-modules with value `M`, over the constant presheaf of rings at
`R = O(X)`; all of its restriction maps are the identity. -/
noncomputable def constModObj (M : ModuleCat.{max t r} (O.obj (Opposite.op X))) :
    PresheafOfModules.{max t r} (ringPresheaf (constRing O X)) where
  obj _ := M
  map a := (ModuleCat.restrictScalarsId'.{max t r} _ (constRing_map_hom O X a)).inv.app M
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The morphism of constant presheaves of modules induced by a morphism of modules. -/
noncomputable def constModMap {M N : ModuleCat.{max t r} (O.obj (Opposite.op X))} (φ : M ⟶ N) :
    constModObj.{t} O X M ⟶ constModObj.{t} O X N where
  app _ := φ
  naturality _ := rfl

/-- The functor sending an `R`-module to the constant presheaf of modules with that value, over
the constant presheaf of rings at `R = O(X)`. -/
noncomputable def constMod :
    ModuleCat.{max t r} (O.obj (Opposite.op X)) ⥤
      PresheafOfModules.{max t r} (ringPresheaf (constRing O X)) where
  obj M := constModObj.{t} O X M
  map φ := constModMap.{t} O X φ
  map_id _ := rfl
  map_comp _ _ := rfl

end Constant

section Terminal

variable {X : C} (hX : IsTerminal X)

/-- The canonical ring map `ρ_U : O(X) → O(U)` induced by the unique morphism `U ⟶ X` to the
terminal object. -/
def rho (U : Cᵒᵖ) : O.obj (Opposite.op X) →+* O.obj U := (O.map (iota hX U)).hom

/-- `ρ_U` followed by the restriction map along `U ⟶ V` is `ρ_V`. -/
lemma rho_comp {U V : Cᵒᵖ} (a : U ⟶ V) : (O.map a).hom.comp (rho O hX U) = rho O hX V := by
  rw [rho, rho, ← iota_comp hX a, O.map_comp, RingCat.hom_comp]

/-- Elementwise form of `rho_comp`. -/
lemma rho_comp_apply {U V : Cᵒᵖ} (a : U ⟶ V) (s : O.obj (Opposite.op X)) :
    (O.map a).hom (rho O hX U s) = rho O hX V s :=
  RingHom.congr_fun (rho_comp O hX a) s

/-- `ρ_{op X}` is the identity of `R`. -/
lemma rho_self : rho O hX (Opposite.op X) = RingHom.id (O.obj (Opposite.op X)) := by
  rw [rho, iota_self, O.map_id, RingCat.hom_id]

/-- The morphism of presheaves of rings from the constant presheaf at `R = O(X)` to `O`, whose
component at `U` is the canonical map `ρ_U : R → O(U)`. -/
def theta : constRing O X ⟶ commPresheaf O where
  app U := CommRingCat.ofHom (rho O hX U)
  naturality U V a := by
    ext z
    exact (rho_comp_apply O hX a z).symm

/-- Restriction along the unique morphism `op X ⟶ U`, for a presheaf of modules over the
constant presheaf of rings at `R = O(X)`. -/
noncomputable def constRestrict
    (F : PresheafOfModules.{max t r} (ringPresheaf (constRing O X))) (U : Cᵒᵖ) :
    F.obj (Opposite.op X) ⟶ F.obj U :=
  F.map (iota hX U) ≫
    (ModuleCat.restrictScalarsId'.{max t r} _
      (constRing_map_hom O X (iota hX U))).hom.app (F.obj U)

/-- `constRestrict` acts on elements as the restriction map along `ι_U`. -/
lemma constRestrict_apply (F : PresheafOfModules.{max t r} (ringPresheaf (constRing O X)))
    (U : Cᵒᵖ) (x : F.obj (Opposite.op X)) :
    (constRestrict O hX F U).hom x = F.map (iota hX U) x := rfl

/-- A morphism out of a constant presheaf of modules is determined by its component at `op X`:
every other component is obtained from it by restriction along `ι_U`. -/
lemma constMod_hom_app {M : ModuleCat.{max t r} (O.obj (Opposite.op X))}
    {F : PresheafOfModules.{max t r} (ringPresheaf (constRing O X))}
    (ψ : constModObj.{t} O X M ⟶ F) (U : Cᵒᵖ) (x : M) :
    ψ.app U x = F.map (iota hX U) (ψ.app (Opposite.op X) x) :=
  PresheafOfModules.naturality_apply ψ (iota hX U) x

/-- The constant presheaf of modules functor is left adjoint to evaluation at `op X`, because
`op X` is initial in `Cᵒᵖ`. -/
noncomputable def constModAdj :
    constMod.{t} O X ⊣
      PresheafOfModules.evaluation.{max t r} (ringPresheaf (constRing O X)) (Opposite.op X) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M F =>
        { toFun := fun ψ => ψ.app (Opposite.op X)
          invFun := fun φ =>
            { app := fun U => φ ≫ constRestrict O hX F U
              naturality := fun {U V} a => by
                refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
                have h := PresheafOfModules.map_comp_apply F (iota hX U) a (φ x)
                rw [iota_comp] at h
                exact h }
          left_inv := fun ψ => PresheafOfModules.hom_ext fun U =>
            ModuleCat.hom_ext (LinearMap.ext fun x => (constMod_hom_app O hX ψ U x).symm)
          right_inv := fun φ => by
            refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
            have h : F.map (iota hX (Opposite.op X)) (φ x) = φ x := by
              rw [iota_self hX, F.map_id]; rfl
            exact h }
      homEquiv_naturality_left_symm := fun f g =>
        PresheafOfModules.hom_ext fun _ => Category.assoc _ _ _
      homEquiv_naturality_right := fun f g => rfl }

/-- **Base change along the canonical maps out of the terminal object.** The functor sending an
`R`-module `M` to the presheaf of `O`-modules `U ↦ O(U) ⊗_R M`. -/
noncomputable def baseChangePresheaf :
    ModuleCat.{max t r} (O.obj (Opposite.op X)) ⥤ PresheafOfModules.{max t r} O :=
  constMod.{t} O X ⋙ changeOfRings (theta O hX)

/-- The sections over `U` of the base change presheaf of `M` are `O(U) ⊗_R M`, the extension of
scalars of `M` along `ρ_U`. -/
lemma baseChangePresheaf_obj_obj (M : ModuleCat.{max t r} (O.obj (Opposite.op X))) (U : Cᵒᵖ) :
    ((baseChangePresheaf.{t} O hX).obj M).obj U
      = (ModuleCat.extendScalars.{r, r, max t r} (rho O hX U)).obj M :=
  rfl

/-- Over `U`, the base change presheaf of a morphism `φ` is the extension of scalars of `φ` along
`ρ_U`. -/
lemma baseChangePresheaf_map_app {M N : ModuleCat.{max t r} (O.obj (Opposite.op X))} (φ : M ⟶ N)
    (U : Cᵒᵖ) :
    ((baseChangePresheaf.{t} O hX).map φ).app U
      = (ModuleCat.extendScalars.{r, r, max t r} (rho O hX U)).map φ :=
  rfl

/-- The component of `theta` at `op X` is the identity of `R`. -/
lemma theta_app_opX_hom :
    ((Functor.whiskerRight (theta O hX) (forget₂ CommRingCat RingCat)).app
      (Opposite.op X)).hom = RingHom.id (O.obj (Opposite.op X)) :=
  rho_self O hX

/-- Evaluating at `op X` a presheaf of `O`-modules regarded as a presheaf of modules over the
constant presheaf of rings gives back its sections over `op X`, because `ρ_{op X}` is the
identity of `R`. -/
noncomputable def evaluationRestrictIso :
    Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (theta O hX) ⋙
        PresheafOfModules.evaluation.{max t r} (ringPresheaf (constRing O X)) (Opposite.op X) ≅
      PresheafOfModules.evaluation.{max t r} O (Opposite.op X) :=
  Functor.isoWhiskerLeft (PresheafOfModules.evaluation.{max t r} O (Opposite.op X))
      (ModuleCat.restrictScalarsId'.{max t r} _ (theta_app_opX_hom O hX)) ≪≫
    (PresheafOfModules.evaluation.{max t r} O (Opposite.op X)).rightUnitor

/-- **The base change adjunction.** Base change along the canonical maps out of the terminal
object is left adjoint to evaluation at `op X`. -/
noncomputable def baseChangeAdj :
    baseChangePresheaf.{t} O hX ⊣ PresheafOfModules.evaluation.{max t r} O (Opposite.op X) :=
  Adjunction.ofNatIsoRight
    ((constModAdj.{t} O hX).comp (changeOfRingsAdjunction (theta O hX)))
    (evaluationRestrictIso.{t} O hX)

/-- The sections of the base change presheaf over `U` are the extension of scalars along the
canonical map `ρ_U : R → O(U)`. -/
noncomputable def baseChangeEvaluationIso (U : Cᵒᵖ) :
    baseChangePresheaf.{t} O hX ⋙ PresheafOfModules.evaluation.{max t r} O U ≅
      ModuleCat.extendScalars.{r, r, max t r} (rho O hX U) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The components of `baseChangeEvaluationIso` are identities. -/
@[simp]
lemma baseChangeEvaluationIso_hom_app (U : Cᵒᵖ)
    (M : ModuleCat.{max t r} (O.obj (Opposite.op X))) :
    (baseChangeEvaluationIso.{t} O hX U).hom.app M = 𝟙 _ :=
  rfl

/-- The components of the inverse of `baseChangeEvaluationIso` are identities. -/
@[simp]
lemma baseChangeEvaluationIso_inv_app (U : Cᵒᵖ)
    (M : ModuleCat.{max t r} (O.obj (Opposite.op X))) :
    (baseChangeEvaluationIso.{t} O hX U).inv.app M = 𝟙 _ :=
  rfl

/-- The base change functor is additive. -/
instance baseChangePresheaf_additive : (baseChangePresheaf.{t} O hX).Additive :=
  (baseChangeAdj.{t} O hX).left_adjoint_additive

/-- The base change functor preserves finite colimits. -/
noncomputable instance baseChangePresheaf_preservesFiniteColimits :
    PreservesFiniteColimits (baseChangePresheaf.{t} O hX) :=
  have : PreservesColimitsOfSize.{max t r, max t r} (baseChangePresheaf.{t} O hX) :=
    (baseChangeAdj.{t} O hX).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

end Terminal

end Stacks.TerminalBaseChange
