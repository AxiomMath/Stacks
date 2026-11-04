module
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
import all StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# UnitComparisonUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison`, stated as separate
declarations beside the ones there: over more general coefficient universes, or with inputs
that are carried there as hypotheses discharged, together with the new results built on them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- On global sections, `𝒪_Y ⟶ f_* 𝒪_X` followed by the identification of `f⁻¹(⊤)` with `⊤` is
the map on global functions. -/
lemma unitToPushforwardUnit_app_top {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Γ(Y, ⊤)) :
    (Scheme.unitModule X).presheaf.map (eqToHom (show (⊤ : X.Opens) = f ⁻¹ᵁ ⊤ by simp)).op
        ((Scheme.Modules.unitToPushforwardUnit f).app ⊤ y) = f.appTop y := by
  have h := congrArg (fun φ : (Scheme.unitModule X).presheaf.obj (Opposite.op ⊤) ⟶
      (Scheme.unitModule X).presheaf.obj (Opposite.op ⊤) ↦
        φ (show Γ(Scheme.unitModule X, ⊤) from f.appTop y))
    ((Scheme.unitModule X).presheaf.map_id (Opposite.op (⊤ : X.Opens)))
  exact h.trans rfl

/-- The morphism of modules underlying `AlgebraicGeometry.pullbackSectionsMap` for the structure
sheaf, followed by `pullbackUnitIso`, is `pullbackUnitIso` followed by `𝒪_B ⟶ g_* 𝒪_A`. -/
private lemma pullbackUnitIso_sectionMorphism {S : Scheme.{u}} {A B : Over S} (g : A ⟶ B) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
        ((Scheme.Modules.pullback B.hom).obj (Scheme.unitModule S)) ≫
      (Scheme.Modules.pushforward g.left).map
        ((Scheme.Modules.pullbackComp g.left B.hom).hom.app (Scheme.unitModule S) ≫
          (Scheme.Modules.pullbackCongr (Over.w g)).hom.app (Scheme.unitModule S))) ≫
      (Scheme.Modules.pushforward g.left).map (Scheme.Modules.pullbackUnitIso A.hom).hom =
    (Scheme.Modules.pullbackUnitIso B.hom).hom ≫ Scheme.Modules.unitToPushforwardUnit g.left := by
  have hc := Scheme.Modules.pullbackUnitIso_comp_eq g.left B.hom A.hom (Over.w g)
  have ha : ((Scheme.Modules.pullbackComp g.left B.hom).hom.app (Scheme.unitModule S) ≫
        (Scheme.Modules.pullbackCongr (Over.w g)).hom.app (Scheme.unitModule S)) ≫
      (Scheme.Modules.pullbackUnitIso A.hom).hom =
      (Scheme.Modules.pullback g.left).map (Scheme.Modules.pullbackUnitIso B.hom).hom ≫
        (Scheme.Modules.pullbackUnitIso g.left).hom := by
    rw [← hc]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have hu : ∀ (N : A.left.Modules)
      (f : (Scheme.Modules.pullback g.left).obj
        ((Scheme.Modules.pullback B.hom).obj (Scheme.unitModule S)) ⟶ N),
      (Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
          ((Scheme.Modules.pullback B.hom).obj (Scheme.unitModule S)) ≫
        (Scheme.Modules.pushforward g.left).map f =
      (Scheme.Modules.pullbackPushforwardAdjunction g.left).homEquiv _ _ f :=
    fun _ f ↦ (Adjunction.homEquiv_unit _ _ _ f).symm
  rw [Category.assoc, ← Functor.map_comp, ha, hu,
    Adjunction.homEquiv_naturality_left, Scheme.Modules.pullbackUnitIso_homEquiv]

/-- **The pullback map on global sections of the pulled-back structure sheaf is the map on
global functions.** For a morphism `g : A ⟶ B` of schemes over `S`, identifying
`Γ(T, T.hom⁺ 𝒪_S)` with `Γ(T, 𝒪_T)` by `pullbackUnitIso` turns
`AlgebraicGeometry.pullbackSectionsMap` into `g.left.appTop`. -/
lemma Scheme.Modules.pullbackUnitIso_app_pullbackSectionsMap {S : Scheme.{u}} {A B : Over S}
    (g : A ⟶ B) (x : Γ((Scheme.Modules.pullback B.hom).obj (Scheme.unitModule S), ⊤)) :
    (Scheme.Modules.pullbackUnitIso A.hom).hom.app ⊤ (pullbackSectionsMap _ g x) =
      g.left.appTop ((Scheme.Modules.pullbackUnitIso B.hom).hom.app ⊤ x) := by
  have key : (Scheme.Modules.pullbackUnitIso A.hom).hom.app (g.left ⁻¹ᵁ ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
        ((Scheme.Modules.pullback B.hom).obj (Scheme.unitModule S)) ≫
      (Scheme.Modules.pushforward g.left).map
        ((Scheme.Modules.pullbackComp g.left B.hom).hom.app (Scheme.unitModule S) ≫
          (Scheme.Modules.pullbackCongr (Over.w g)).hom.app (Scheme.unitModule S))).app ⊤ x) =
      (Scheme.Modules.unitToPushforwardUnit g.left).app ⊤
        ((Scheme.Modules.pullbackUnitIso B.hom).hom.app ⊤ x) :=
    congrArg (fun φ ↦ (φ.app ⊤).hom x) (pullbackUnitIso_sectionMorphism g)
  refine (Scheme.Modules.Hom.app_presheaf_map _ _ _).trans
    ((congrArg (fun z ↦ (Scheme.unitModule A.left).presheaf.map
      (eqToHom (show (⊤ : A.left.Opens) = g.left ⁻¹ᵁ ⊤ by simp)).op z) key).trans ?_)
  exact unitToPushforwardUnit_app_top g.left _

end AlgebraicGeometry

end
