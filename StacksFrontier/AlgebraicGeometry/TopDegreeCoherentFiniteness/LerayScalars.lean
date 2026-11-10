module

public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.Scalars
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural

/-!
# Leray in the absence of higher direct images, `k`-linearly

For `π : Y ⟶ Z` over a field `k` and an `𝒪_Y`-module `M` whose higher direct images along `π`
vanish, `H^n(Y, M) ≅ H^n(Z, π_* M)` ([Stacks, Tag 01F4] part (1)). This file records that the
comparison respects the `k`-vector space structures of `AlgebraicGeometry.cohomologyOverField`,
so finite dimensionality passes from `H^n(Y, M)` to `H^n(Z, π_* M)`.

The comparison used is `Stacks.AffineCohomologyPushforward.schemeDerivedPlusNatTrans`, which is a
natural transformation of functors on all modules; its naturality at the scalar endomorphisms of
`AlgebraicGeometry.CohomologyScalars` is the `k`-linearity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.HypercoveringModules

universe u

namespace AlgebraicGeometry.CohomologyScalars

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] _root_.Stacks.SchemeCohomology.sheafOfModules_abelian
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

/-- **The direct image of a scalar endomorphism is a scalar endomorphism.** -/
theorem pushforward_map_scalarEndo {Y Z : Scheme.{u}} (π : Y ⟶ Z) (M : Y.Modules) (r : Γ(Z, ⊤)) :
    (Scheme.Modules.pushforward π).map (scalarEndo M (π.appTop r)) =
      scalarEndo ((Scheme.Modules.pushforward π).obj M) r := by
  let := globalSectionsLinear Y
  let := globalSectionsLinear Z
  ext V x
  change (scalarEndo M (π.appTop r)).app (π ⁻¹ᵁ V) x = (scalarEndo _ r).app V x
  have hL := Stacks.SheafOfModules.smul_val_app Y.ringCatSheaf _ ⊤ isTerminalTop (RingHom.id _)
    (π.appTop r) (𝟙 (show SheafOfModules.{u} Y.ringCatSheaf from M)) (op (π ⁻¹ᵁ V)) x
  have hR := Stacks.SheafOfModules.smul_val_app Z.ringCatSheaf _ ⊤ isTerminalTop (RingHom.id _)
    r (𝟙 (show SheafOfModules.{u} Z.ringCatSheaf from (Scheme.Modules.pushforward π).obj M))
    (op V) x
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hn : Y.presheaf.map (isTerminalTop.from (π ⁻¹ᵁ V)).op (π.appTop r) =
      π.app V (Z.presheaf.map (isTerminalTop.from V).op r) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  exact congrArg (fun t => (show Y.ringCatSheaf.obj.obj (op (π ⁻¹ᵁ V)) from t) •
    (show M.val.obj (op (π ⁻¹ᵁ V)) from x)) hn

variable (k : Type u) [Field k]

/-- The global section of `Y` given by `a : k` along `π ≫ g` is the pullback under `π` of the
global section of `Z` given by `a` along `g`. -/
theorem fieldScalar_comp {Y Z : Scheme.{u}} (π : Y ⟶ Z) (g : Z ⟶ Spec (.of k)) (a : k) :
    fieldScalar k (π ≫ g) a = π.appTop (fieldScalar k g a) := by
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ (π ≫ g).appLE ⊤ ⊤ _).hom a =
    (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ _) ≫ π.appTop).hom a
  have e1 : ∀ {A B : Scheme.{u}} (t : A ⟶ B) (e : (⊤ : A.Opens) ≤ t ⁻¹ᵁ ⊤),
      t.appLE ⊤ ⊤ e = t.appTop := fun {A B} t e => by
    have h : A.presheaf.map (homOfLE e).op = 𝟙 Γ(A, ⊤) :=
      Eq.trans (congrArg A.presheaf.map
        (Subsingleton.elim (homOfLE e).op (𝟙 (op (⊤ : A.Opens))))) (A.presheaf.map_id _)
    exact Eq.trans (congrArg (fun c ↦ t.appTop ≫ c) h) (Category.comp_id t.appTop)
  rw [e1, e1, Scheme.Hom.comp_appTop]
  rfl

/-- **Finite dimensionality passes along Leray when the higher direct images vanish.** -/
theorem finiteDimensional_pushforward_of_isZero_rightDerived {Y Z : Scheme.{u}} (π : Y ⟶ Z)
    (g : Z ⟶ Spec (.of k)) (M : Y.Modules)
    (hM : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward π).rightDerived q).obj M))
    (n : ℕ) [FiniteDimensional k (cohomologyOverField k (π ≫ g) M n)] :
    FiniteDimensional k (cohomologyOverField k g ((Scheme.Modules.pushforward π).obj M) n) := by
  let τ := Stacks.AffineCohomologyPushforward.schemeDerivedPlusNatTrans π (n : ℤ)
  have hτ : IsIso (τ.app M) :=
    Stacks.AffineCohomologyPushforward.isIso_derivedPlusPushforwardNatTrans_app
      (Stacks.SchemeCohomology.hom π) (n : ℤ)
      (Stacks.LeraySections.rightAcyclic_modulePushforward_of_isZero_rightDerived
        (Stacks.SchemeCohomology.hom π) hM)
  let eY := (Stacks.DerivedIndexing.rightDerivedIso (secF Y.ringCatSheaf (⊤ : Y.Opens)) n)
  let eZ := (Stacks.DerivedIndexing.rightDerivedIso (secF Z.ringCatSheaf (⊤ : Z.Opens)) n)
  let e : Hgroup Z.ringCatSheaf ⊤ n ((Scheme.Modules.pushforward π).obj M) ⟶
      Hgroup Y.ringCatSheaf ⊤ n M :=
    (eZ.app _ ≪≫ asIso (τ.app M) ≪≫ eY.symm.app M).hom
  have he_inj : Function.Injective e :=
    (ConcreteCategory.bijective_of_isIso e).1
  refine finiteDimensional_of_injective (f := g) (f' := π ≫ g) e.hom ?_ he_inj
  intro a x
  set gY := scalarEndo M (fieldScalar k (π ≫ g) a)
  have hg : (Scheme.Modules.pushforward π).map gY =
      scalarEndo ((Scheme.Modules.pushforward π).obj M) (fieldScalar k g a) := by
    simp only [gY]
    rw [fieldScalar_comp, pushforward_map_scalarEndo]
  rw [← hg]
  have h1 := ConcreteCategory.congr_hom (eZ.hom.naturality
    ((Scheme.Modules.pushforward π).map gY)) x
  have h2 := ConcreteCategory.congr_hom (τ.naturality gY) (eZ.hom.app _ x)
  have h3 := ConcreteCategory.congr_hom (eY.inv.naturality gY) (τ.app M (eZ.hom.app _ x))
  change eY.inv.app M (τ.app M (eZ.hom.app _
      (((secF Z.ringCatSheaf ⊤).rightDerived n).map ((Scheme.Modules.pushforward π).map gY) x))) =
    ((secF Y.ringCatSheaf ⊤).rightDerived n).map gY (eY.inv.app M (τ.app M (eZ.hom.app _ x)))
  refine (congrArg (fun t => eY.inv.app M (τ.app M t)) h1).trans ?_
  refine (congrArg (fun t => eY.inv.app M t) h2).trans ?_
  exact h3

end AlgebraicGeometry.CohomologyScalars

end
