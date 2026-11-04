module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomZariskiCone
public import StacksFrontier.AlgebraicGeometry.Quot.RelHomOpensCochains
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMonoRestrictionSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived

/-!
# The étale inputs of the Zariski gluing along the base changes over the opens

Along the cone `AlgebraicGeometry.Space.zarCone` of base changes over the opens of a test scheme,
whose legs and transition morphisms are étale monomorphisms:

* the relative Hom presheaves of modules into an injective module are flasque
  (`AlgebraicGeometry.Space.zarCone_relHomOpens_isFlasque`);
* the inverse images of a K-injective complex along the legs are K-injective
  (`AlgebraicGeometry.Space.zarCone_isKInjective`);
* the comparisons of the derived inverse images along the legs with the underived ones are
  invertible (`AlgebraicGeometry.Space.zarCone_isIso_α`).

Nothing here is registered.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] SmallEtale.instHasSheafify

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underived pullback datum of the derived pullback of modules is coherent. -/
theorem modulePullbackDataTopos_isCoherent : (modulePullbackDataTopos B S hS).IsCoherent :=
  (modulePullbackData_isCoherent B S hS).ofEq _
    (fun f => toModulesHom_pullbackModules_eq_modulePullback B S hS f)

/-- Surjectivity on morphisms transfers along an isomorphism of functors. -/
theorem _root_.CategoryTheory.Functor.map_surjective_of_natIso {C D : Type*} [Category* C]
    [Category* D] {F G : C ⥤ D} (e : F ≅ G) {M J : C}
    (h : Function.Surjective (G.map : (M ⟶ J) → _)) :
    Function.Surjective (F.map : (M ⟶ J) → _) := by
  intro x
  obtain ⟨y, hy⟩ := h (e.inv.app M ≫ x ≫ e.hom.app J)
  refine ⟨y, ?_⟩
  rw [← NatIso.naturality_2 e y, hy]
  simp

/-- **Flasqueness of a relative Hom presheaf from surjectivity of the transition inverse
images.** -/
theorem _root_.CategoryTheory.PullbackData.relHomOpens_isFlasque_of_surjective {X₀ : Type*}
    [TopologicalSpace X₀] {A : Type*} [Category* A] {M : A → Type*} [∀ a, Category* (M a)]
    [∀ a, Preadditive (M a)] (P : PullbackData A M) [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]
    (hP : P.IsCoherent) {π : Opens X₀ ⥤ A} {a₀ : A} (κ : PullbackData.ConeTo π a₀) (N N' : M a₀)
    (hs : ∀ {V U : Opens X₀} (h : V ≤ U),
      Function.Surjective ((P.pull (π.map (homOfLE h))).map :
        ((P.pull (κ.leg U)).obj N ⟶ (P.pull (κ.leg U)).obj N') → _)) :
    (P.relHomOpens hP κ N N').IsFlasque := by
  intro U V h (x : (P.pull (κ.leg V)).obj N ⟶ (P.pull (κ.leg V)).obj N')
  obtain ⟨y, hy⟩ := hs h ((P.triangle (κ.w (homOfLE h))).inv.app N ≫ x ≫
    (P.triangle (κ.w (homOfLE h))).hom.app N')
  refine ⟨y, ?_⟩
  show (P.triangle (κ.w (homOfLE h))).hom.app N ≫ (P.pull (π.map (homOfLE h))).map y ≫
    (P.triangle (κ.w (homOfLE h))).inv.app N' = x
  rw [hy]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Iso.hom_inv_id_app_assoc]

/-- The inverse image of the underived datum along an étale morphism is étale restriction. -/
def pmEtaleIso {X Y : AlgebraicSpaces B S hS} (r : X ⟶ Y) (hr : IsEtale B S hS r.hom) :
    (modulePullbackDataTopos B S hS).pull r ≅ etaleModulePullback.{u, u} B S hS r hr :=
  pullbackModulesIsoModulePullback B S hS r ≪≫ modulePullbackIsoEtaleModulePullback B S hS r hr

/-- The inverse image of an injective module along an étale morphism is injective. -/
theorem injective_pm_pull_obj {X Y : AlgebraicSpaces B S hS} (r : X ⟶ Y)
    (hr : IsEtale B S hS r.hom) (J : Modules.{u, u} B S hS Y.1 Y.2) [Injective J] :
    Injective (((modulePullbackDataTopos B S hS).pull r).obj J) :=
  let F := (modulePullbackDataTopos B S hS).pull r
  let G : type_of% F := etaleModulePullback.{u, u} B S hS r hr
  let e : F ≅ G := pmEtaleIso B S hS r hr
  have : Injective (G.obj J) := injective_etaleModulePullback_obj B S hS r hr J
  Injective.of_iso (e.app J).symm inferInstance

/-- **Restriction of the underived datum along an étale monomorphism is surjective on
morphisms into an injective module.** -/
theorem pm_pull_map_surjective {X Y : AlgebraicSpaces B S hS} (r : X ⟶ Y)
    (hr : IsEtale B S hS r.hom) [Mono r.hom] (M J : Modules.{u, u} B S hS Y.1 Y.2)
    [Injective J] :
    Function.Surjective (((modulePullbackDataTopos B S hS).pull r).map : (M ⟶ J) → _) :=
  let F := (modulePullbackDataTopos B S hS).pull r
  let G : type_of% F := etaleModulePullback.{u, u} B S hS r hr
  let e : F ≅ G := pmEtaleIso B S hS r hr
  Functor.map_surjective_of_natIso e
    (etaleModulePullback_map_surjective_of_injective B S hS r hr M J)

variable {B S hS} {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : SchemesOver Y)
  {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left)

/-- **Flasqueness of the relative Hom presheaves into an injective module.** -/
theorem zarCone_relHomOpens_isFlasque
    (N N' : Modules.{u, u} B S hS (baseChangeSpace f (restrictTest T h₀)).1
      (baseChangeSpace f (restrictTest T h₀)).2) [Injective N'] :
    ((modulePullbackDataTopos B S hS).relHomOpens (modulePullbackDataTopos_isCoherent B S hS)
      (zarCone f T h₀) N N').IsFlasque := by
  refine CategoryTheory.PullbackData.relHomOpens_isFlasque_of_surjective _ _ _ _ _
    fun {V U} h => ?_
  have := injective_pm_pull_obj B S hS _ (isEtale_zarCone_leg f T h₀ U) N'
  exact pm_pull_map_surjective B S hS _ (isEtale_zarSpaces_map f T h₀ (homOfLE h)) _ _

/-- The inverse images of a K-injective complex along the legs are K-injective. -/
theorem zarCone_isKInjective
    (L : CochainComplex (Modules.{u, u} B S hS (baseChangeSpace f (restrictTest T h₀)).1
      (baseChangeSpace f (restrictTest T h₀)).2) ℤ) (hL : L.IsKInjective)
    (W : Z₀.left.obj.Opens) :
    ((modulePullbackDataTopos B S hS).legComplex (zarCone f T h₀) L W).IsKInjective :=
  isKInjective_pullbackModules_of_isEtale B S hS _ (isEtale_zarCone_leg f T h₀ W) L hL

/-- The comparisons of the derived inverse images along the legs are invertible. -/
theorem zarCone_isIso_α (W : Z₀.left.obj.Opens)
    (M : HomotopyCategory (Modules.{u, u} B S hS (baseChangeSpace f (restrictTest T h₀)).1
      (baseChangeSpace f (restrictTest T h₀)).2) (ComplexShape.up ℤ)) :
    IsIso (((derivedModulePullbackLeftDerived B S hS).α ((zarCone f T h₀).leg W)).app M) :=
  isIso_smallEtaleDerivedModulePullbackComparison_app_of_isEtale B S hS _
    (isEtale_zarCone_leg f T h₀ W) M

end AlgebraicGeometry.Space

end
