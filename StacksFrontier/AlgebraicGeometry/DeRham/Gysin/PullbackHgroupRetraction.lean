module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupDeRham
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageComparisonSections
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.Transverse

/-!
# Pulling Hodge classes back along a retraction and then along its section

Let `G : W ⟶ X` be a morphism of schemes over `S` with a section `i : X ⟶ W`, `i ≫ G = 𝟙 X`.
Pulling a Hodge class on `X` back to `W` along `G` and then back to `X` along `i` gives the class
back: the composite of the pullback maps of [Stacks, Tag 01F9] along the canonical maps of forms
is the identity of `Hⁿ(X, Ω^p_{X/S})`
(`Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup_formsBaseChangeHom_retraction`).

It is the composition law of pullback maps
(`Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup_canonical_comp`) together with the
fact that pulling a form back along `G` and then along `i` is pulling it back along
`i ≫ G = 𝟙 X`, which does nothing (`relativeDifferentialFormsPullback_id`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.DeRham.CohomologicalGysin Stacks.DeRham.GysinCohomologyDeRham

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- **Pulling back local forms along the identity is the identity**, over every open: the
pullback along `𝟙` is bijective, and it is idempotent because `𝟙 ≫ 𝟙 = 𝟙`. -/
theorem relativeDifferentialFormsPullback_id (π : X ⟶ S) (h : 𝟙 X ≫ π = π ≫ 𝟙 S) (d : ℤ)
    (U : X.Opens) (ω : Γ(relativeDifferentialForms π d, U)) :
    relativeDifferentialFormsPullback (𝟙 X) π π (𝟙 S) h d U ω = ω := by
  have hbij := bijective_relativeDifferentialFormsPullback_of_isIso (𝟙 X) π π h d U
  have h₃ : (𝟙 X ≫ 𝟙 X) ≫ π = π ≫ 𝟙 S := by simp
  have hcomp := Stacks.Gysin.relativeDifferentialFormsPullback_comp (𝟙 X) (𝟙 X) π π π (𝟙 S)
    (𝟙 S) (𝟙 S) h (by simp) (by simp) d U ω
  have hcongr := Stacks.Gysin.relativeDifferentialFormsPullback_congrMor (Category.id_comp (𝟙 X))
    π π (𝟙 S) h₃ h d U ω
  replace hcongr := (Stacks.Gysin.presheaf_map_le_refl _ _ _).symm.trans hcongr
  exact hbij.1 (hcongr.symm.trans hcomp).symm

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.DeRham.GysinCohomologyBaseChange

/-- The transport of a direct image along an equality of morphisms of ringed spaces restricts
sections along the equality of the preimage opens. -/
theorem eqToHom_modulePushforward_val_app {X X' : RingedSpace.{u, u}} {G₁ G₂ : X' ⟶ X}
    (hG : G₁ = G₂) (M' : RModules X') (U : (Opens X.carrier)ᵒᵖ)
    (hle : (Opens.map G₂.hom.base).obj U.unop ≤ (Opens.map G₁.hom.base).obj U.unop)
    (x : ((modulePushforward G₁).obj M').val.obj U) :
    (eqToHom (congrArg (fun G => (modulePushforward G).obj M') hG)).val.app U x =
      M'.val.map (homOfLE hle).op x := by
  subst hG
  rw [show (homOfLE hle).op = 𝟙 _ from rfl, M'.val.map_id]
  rfl

variable {X W S : Scheme.{u}}

/-- Reassociating a composite of five morphisms, at variables. -/
private lemma assoc_five {C : Type*} [Category* C] {x₀ x₁ x₂ x₃ x₄ x₅ : C} (a : x₀ ⟶ x₁)
    (b : x₁ ⟶ x₂) (c : x₂ ⟶ x₃) (d : x₃ ⟶ x₄) (e : x₄ ⟶ x₅) :
    (a ≫ b ≫ c) ≫ d ≫ e = a ≫ b ≫ c ≫ d ≫ e := by
  simp only [Category.assoc]

/-- A section of `G` gives a section of the underlying morphism of sheaved spaces. -/
private lemma toShHom_comp_eq_id {G : W ⟶ X} {i : X ⟶ W} (hi : i ≫ G = 𝟙 X) :
    i.toLRSHom.toShHom ≫ G.toLRSHom.toShHom = 𝟙 X.toRingedSpace :=
  congrArg (fun k : X ⟶ X => k.toLRSHom.toShHom) hi

/-- On sections, the canonical map of forms `Ω^p_{X/S} ⟶ g_*Ω^p_{X'/S'}` is the pullback of
local forms. -/
theorem formsBaseChangeHom_val_app {X' S' : Scheme.{u}} (g : X' ⟶ X) (π : X ⟶ S)
    (π' : X' ⟶ S') (t : S' ⟶ S) (hcomm : g ≫ π = π' ≫ t) (n : ℕ) (U : X.Opens)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms π (n : ℤ), U)) :
    (Stacks.Gysin.formsBaseChangeHom g π π' t hcomm (n : ℤ)).val.app (op U) ω =
      Scheme.Hom.relativeDifferentialFormsPullback g π π' t hcomm (n : ℤ) U ω := by
  have hu := ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv_unit _ _
    (Scheme.Hom.relativeDifferentialFormsMap g π π' t hcomm (n : ℤ))).trans
      (Stacks.DeRhamBaseChange.formsAdjoint_eq g π' π t hcomm n).symm
  exact (congrArg (fun φ => φ.val.app (op U) ω) hu).trans
    (Stacks.DeRhamBaseChange.formsAdjoint_app g π' π t hcomm n U ω)

variable (f : X ⟶ S) (G : W ⟶ X) (h : W ⟶ S) (w : G ≫ f = h ≫ 𝟙 S) (i : X ⟶ W)
  (w' : i ≫ h = f ≫ 𝟙 S) (hi : i ≫ G = 𝟙 X)

/-- The canonical maps of forms along `G` and then along a section `i` of `G` compose to the
identity of `Ω^p_{X/S}`, read through `(i ≫ G)_* = 𝟙_* = 𝟭`. -/
theorem formsBaseChangeHom_comp_retraction (p : ℕ) :
    Stacks.Gysin.formsBaseChangeHom G f h (𝟙 S) w p ≫
        (modulePushforward G.toLRSHom.toShHom).map
          (Stacks.Gysin.formsBaseChangeHom i h f (𝟙 S) w' p) ≫
        (modulePushforwardComp i.toLRSHom.toShHom G.toLRSHom.toShHom).hom.app
          (f.relativeDifferentialForms p) ≫
        eqToHom (congrArg (fun K => (modulePushforward K).obj (f.relativeDifferentialForms p))
          (show i.toLRSHom.toShHom ≫ G.toLRSHom.toShHom = 𝟙 X.toRingedSpace from
            congrArg (fun k : X ⟶ X => k.toLRSHom.toShHom) hi)) ≫
        (modulePushforwardId X.toRingedSpace).hom.app (f.relativeDifferentialForms p) =
      𝟙 _ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun ω => ?_))
  have h₃ : (i ≫ G) ≫ f = f ≫ 𝟙 S := by
    rw [Category.assoc, w, ← Category.assoc, w']; simp
  have hcomp := Stacks.Gysin.relativeDifferentialFormsPullback_comp G i f h f (𝟙 S) (𝟙 S)
    (𝟙 S) w w' h₃ p U.unop ω
  have hcongr := Stacks.Gysin.relativeDifferentialFormsPullback_congrMor hi f f (𝟙 S) h₃
    (by simp) p U.unop ω
  have hid := Scheme.Hom.relativeDifferentialFormsPullback_id f (by simp) p U.unop ω
  show _ = ω
  refine Eq.trans ?_ (hcongr.trans hid)
  have hK := toShHom_comp_eq_id hi
  refine (eqToHom_modulePushforward_val_app hK _ U (le_of_eq (by rw [hK])) _).trans ?_
  refine congrArg _ ?_
  refine Eq.trans ?_ hcomp.symm
  refine (formsBaseChangeHom_val_app i h f (𝟙 S) w' p _ _).trans ?_
  exact congrArg _ (formsBaseChangeHom_val_app G f h (𝟙 S) w p U.unop ω)

include hi in
/-- **Pulling a Hodge class back along a retraction and then along its section gives the class
back.** For `G : W ⟶ X` over `S` with a section `i`, `i ≫ G = 𝟙 X`, the composite of the pullback
maps `Hⁿ(X, Ω^p_{X/S}) ⟶ Hⁿ(W, Ω^p_{W/S}) ⟶ Hⁿ(X, Ω^p_{X/S})` of [Stacks, Tag 01F9] is the
identity. -/
theorem pullbackHgroup_formsBaseChangeHom_retraction (a m : ℤ) (n : ℕ) (hn : m - a = n)
    (p : ℕ) :
    pullbackHgroup (CohomologyPullbackComparison.canonical G.toLRSHom.toShHom) a m n hn
        (Stacks.Gysin.formsBaseChangeHom G f h (𝟙 S) w p) ≫
      pullbackHgroup (CohomologyPullbackComparison.canonical i.toLRSHom.toShHom) a m n hn
        (Stacks.Gysin.formsBaseChangeHom i h f (𝟙 S) w' p) = 𝟙 _ := by
  have hK := toShHom_comp_eq_id hi
  refine (pullbackHgroup_canonical_comp i.toLRSHom.toShHom G.toLRSHom.toShHom a m n hn _
    _).symm.trans ?_
  refine (pullbackHgroup_canonical_congr hK a m n hn _).trans ?_
  refine (pullbackHgroup_canonical_id a m n hn _).trans ?_
  exact (congrArg (Hfunctor (structureSheafRing X.toRingedSpace) ⊤ n).map
    ((assoc_five _ _ _ _ _).trans (formsBaseChangeHom_comp_retraction f G h w i w' hi p))).trans
    (CategoryTheory.Functor.map_id _ _)

end Stacks.DeRham.GysinCohomologyBaseChange

end
