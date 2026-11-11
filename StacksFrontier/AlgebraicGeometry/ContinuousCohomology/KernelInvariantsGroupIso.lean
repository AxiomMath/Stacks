module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.KernelInvariants
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictionInjectiveAcyclic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow

/-!
# Derived invariants under a kernel along an isomorphism of extensions

Let `π : Γ → Q` and `π' : Γ' → Q'` be continuous surjections of profinite groups onto Hausdorff
groups, `φ : Γ' ≃ Γ` and `ψ : Q ≃ Q'` isomorphisms of topological groups with `π' = ψ ∘ π ∘ φ`.
Then restricting along `φ`, taking the derived invariants `RH⁰(ker π', -)` with their residual
action of `Q'`, and restricting along `ψ` is the derived invariants `RH⁰(ker π, -)` with their
residual action of `Q`:

`RH⁰(ker π, M) ≅ res_ψ RH⁰(ker π', res_φ M)`.

Restriction along an isomorphism is an equivalence of categories of discrete modules
(`Stacks.GroupCohomology.continuousModuleResEquivalence`), so it preserves injective objects, and
the underived functors agree (`Stacks.GroupCohomology.kernelInvariantsFunctorResIso`): the
kernel of `π'` is the preimage of the kernel of `π`, and an element of `Q` acts through any lift
to `Γ`.

The universes are those of the étale fundamental group (`Γ`, `Γ'` in `Type (u + 1)`) and of the
Galois group of a field (`Q`, `Q'` in `Type u`), with modules in `Type (u + 1)`.

## Main definitions

* `Stacks.GroupCohomology.continuousModuleResEquivalence`
* `Stacks.GroupCohomology.kernelInvariantsFunctorResIso`
* `Stacks.GroupCohomology.derivedKernelInvariantsResIso`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.GroupCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Equivalence

variable (R : Type) [Ring R] {G H : Type v} [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] (φ₀ : G →ₜ* H) (φ : G ≃ₜ* H) (hφ : ∀ g, φ g = φ₀ g)

/-- **Restriction along an isomorphism of topological groups is an equivalence** of categories of
continuous discrete modules, with inverse the restriction along the inverse isomorphism. The
restriction is taken along any continuous homomorphism `φ₀` with the same values as `φ`. -/
def continuousModuleResEquivalence :
    Stacks.Injectives.ContinuousModule.{0, v, v} R H ≌
      Stacks.Injectives.ContinuousModule.{0, v, v} R G :=
  CategoryTheory.Equivalence.mk (continuousModuleRes.{0, v, v} R φ₀)
    (continuousModuleRes.{0, v, v} R (ContinuousMonoidHom.toContinuousMonoidHom φ.symm))
    (NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      (Action.mkIso (Iso.refl _) fun h ↦ by
        simp only [Iso.refl_hom]
        refine (congrArg (fun g ↦ (M.obj.obj.ρ g).asHom) ?_).symm
        change φ₀ (φ.symm h) = h
        rw [← hφ, ContinuousMulEquiv.apply_symm_apply])))
      fun _ ↦ ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <| Action.hom_ext _ _ <|
        ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl)
    (NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      (Action.mkIso (Iso.refl _) fun g ↦ by
        simp only [Iso.refl_hom]
        refine congrArg (fun g ↦ (M.obj.obj.ρ g).asHom) ?_
        change φ.symm (φ₀ g) = g
        rw [← hφ, ContinuousMulEquiv.symm_apply_apply])))
      fun _ ↦ ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <| Action.hom_ext _ _ <|
        ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl)

include φ hφ in
/-- Restriction along an isomorphism is an equivalence. -/
theorem isEquivalence_continuousModuleRes :
    (continuousModuleRes.{0, v, v} R φ₀).IsEquivalence :=
  (continuousModuleResEquivalence R φ₀ φ hφ).isEquivalence_functor

end Equivalence

/-! Exactness of restriction, pinned at the universes used below. -/

/-- Restriction is additive (groups in `Type (u + 1)`, modules in `Type (u + 1)`). -/
local instance (priority := 3000) additive_continuousModuleRes_succ {R : Type} [Ring R]
    {G H : Type (u + 1)} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (φ : G →ₜ* H) : (continuousModuleRes.{0, u + 1, u + 1} R φ).Additive :=
  Stacks.ContinuousCohomology.additive_continuousModuleRes.{0, u + 1, 0} R φ

/-- Restriction is left exact (groups in `Type (u + 1)`, modules in `Type (u + 1)`). -/
local instance (priority := 3000) preservesFiniteLimits_continuousModuleRes_succ {R : Type}
    [Ring R] {G H : Type (u + 1)} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (φ : G →ₜ* H) : PreservesFiniteLimits (continuousModuleRes.{0, u + 1, u + 1} R φ) :=
  Stacks.ContinuousCohomology.preservesFiniteLimits_continuousModuleRes.{0, u + 1, 0} R φ

/-- Restriction is right exact (groups in `Type (u + 1)`, modules in `Type (u + 1)`). -/
local instance (priority := 3000) preservesFiniteColimits_continuousModuleRes_succ {R : Type}
    [Ring R] {G H : Type (u + 1)} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (φ : G →ₜ* H) : PreservesFiniteColimits (continuousModuleRes.{0, u + 1, u + 1} R φ) :=
  Stacks.ContinuousCohomology.preservesFiniteColimits_continuousModuleRes.{0, u + 1, 0} R φ

/-- Restriction is additive (groups in `Type u`, modules in `Type (u + 1)`). -/
local instance (priority := 3000) additive_continuousModuleRes_lift {R : Type} [Ring R]
    {G H : Type u} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (φ : G →ₜ* H) : (continuousModuleRes.{0, u, u + 1} R φ).Additive :=
  Stacks.ContinuousCohomology.additive_continuousModuleRes.{0, u, u + 1} R φ

/-- Restriction is left exact (groups in `Type u`, modules in `Type (u + 1)`). -/
local instance (priority := 3000) preservesFiniteLimits_continuousModuleRes_lift {R : Type}
    [Ring R] {G H : Type u} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (φ : G →ₜ* H) : PreservesFiniteLimits (continuousModuleRes.{0, u, u + 1} R φ) :=
  Stacks.ContinuousCohomology.preservesFiniteLimits_continuousModuleRes.{0, u, u + 1} R φ

/-- Restriction is right exact (groups in `Type u`, modules in `Type (u + 1)`). -/
local instance (priority := 3000) preservesFiniteColimits_continuousModuleRes_lift {R : Type}
    [Ring R] {G H : Type u} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (φ : G →ₜ* H) : PreservesFiniteColimits (continuousModuleRes.{0, u, u + 1} R φ) :=
  Stacks.ContinuousCohomology.preservesFiniteColimits_continuousModuleRes.{0, u, u + 1} R φ

section Kernel

variable (R : Type) [Ring R] {Γ Γ' : Type (u + 1)} {Q Q' : Type u} [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] [CompactSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ']
  [CompactSpace Γ'] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q] [Group Q']
  [TopologicalSpace Q'] [IsTopologicalGroup Q'] [T2Space Q']
  (φ₀ : Γ' →ₜ* Γ) (φ : Γ' ≃ₜ* Γ) (hφ : ∀ g, φ g = φ₀ g) (ψ : Q ≃ₜ* Q')
  (π : Γ →ₜ* Q) (π' : Γ' →ₜ* Q') (hπ : Function.Surjective π) (hπ' : Function.Surjective π')
  (hcomp : ∀ g', π' g' = ψ (π (φ₀ g')))

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [IsTopologicalGroup Γ'] [CompactSpace Γ']
  [IsTopologicalGroup Q] [T2Space Q] [IsTopologicalGroup Q'] [T2Space Q'] in
include hφ hcomp in
/-- **The kernel of `π'` is the preimage of the kernel of `π`**, so the invariants agree. -/
theorem kernelInvariants_res_eq (M : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} R Γ) :
    kernelInvariants R π' ((continuousModuleRes.{0, u + 1, u + 1} R φ₀).obj M) =
      kernelInvariants R π M := by
  ext x
  constructor
  · intro hx
    change ∀ g : Γ, π g = 1 → (M.obj.obj.ρ g).asHom.hom x = x
    intro g hg
    have h := hx (φ.symm g) (by
      rw [hcomp, ← hφ, ContinuousMulEquiv.apply_symm_apply, hg, map_one])
    have e : φ₀ (φ.symm g) = g := by rw [← hφ, ContinuousMulEquiv.apply_symm_apply]
    rw [← e]
    exact h
  · intro hx g' hg'
    refine hx (φ₀ g') (ψ.injective ?_)
    rw [← hcomp, hg', map_one]

include φ hφ hcomp in
/-- **The underived functors agree**: `res_ψ ((res_φ M)^{ker π'}) ≅ M^{ker π}` as discrete
`Q`-modules, naturally in `M`. -/
def kernelInvariantsFunctorResIso :
    continuousModuleRes.{0, u + 1, u + 1} R φ₀ ⋙
        kernelInvariantsFunctor.{0, u + 1, u, u + 1} R π' hπ' ⋙
        continuousModuleRes.{0, u, u + 1} R (ContinuousMonoidHom.toContinuousMonoidHom ψ) ≅
      kernelInvariantsFunctor.{0, u + 1, u, u + 1} R π hπ :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (Action.mkIso
      (LinearEquiv.ofEq _ _ (kernelInvariants_res_eq R φ₀ φ hφ ψ π π' hcomp M)).toModuleIso
      fun q ↦ by
        refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext ?_)
        obtain ⟨γ, rfl⟩ := hπ q
        have h1 : ψ (π γ) = π' (φ.symm γ) := by
          rw [hcomp, ← hφ, ContinuousMulEquiv.apply_symm_apply]
        change (kernelInvariantsQuotientRepresentation R π' hπ'
            ((continuousModuleRes.{0, u + 1, u + 1} R φ₀).obj M) (ψ (π γ)) x).1 =
          (kernelInvariantsQuotientRepresentation R π hπ M (π γ)
            (LinearEquiv.ofEq _ _ (kernelInvariants_res_eq R φ₀ φ hφ ψ π π' hcomp M) x)).1
        rw [h1]
        have e : φ₀ (φ.symm γ) = γ := by rw [← hφ, ContinuousMulEquiv.apply_symm_apply]
        refine (kernelInvariantsQuotientRepresentation_apply R π' hπ' _ (φ.symm γ) x).trans ?_
        refine Eq.trans ?_ (kernelInvariantsQuotientRepresentation_apply R π hπ M γ _).symm
        exact congrArg (fun g ↦ (M.obj.obj.ρ g).asHom.hom x.1) e)))
    fun _ ↦ ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <| Action.hom_ext _ _ <|
      ModuleCat.hom_ext <| LinearMap.ext fun x ↦ Subtype.ext (by dsimp; rfl)

include φ hφ hcomp in
/-- **`RH⁰(ker π, -) ≅ res_ψ ∘ RH⁰(ker π', -) ∘ res_φ`** on bounded below derived categories. -/
def derivedKernelInvariantsResIso :
    derivedKernelInvariants.{0, u + 1, u, 0} R π hπ ≅
      (continuousModuleRes.{0, u + 1, u + 1} R φ₀).mapDerivedCategoryPlus ⋙
        derivedKernelInvariants.{0, u + 1, u, 0} R π' hπ' ⋙
        (continuousModuleRes.{0, u, u + 1} R
          (ContinuousMonoidHom.toContinuousMonoidHom ψ)).mapDerivedCategoryPlus :=
  haveI := Stacks.ContinuousCohomology.enoughInjectives.{0, u + 1, 0} R Γ
  haveI := Stacks.ContinuousCohomology.enoughInjectives.{0, u + 1, 0} R Γ'
  haveI := Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} R Q'
  haveI := isEquivalence_continuousModuleRes R φ₀ φ hφ
  (Functor.rightDerivedFunctorPlusNatIso (kernelInvariantsFunctorResIso R φ₀ φ hφ ψ π π' hπ hπ'
      hcomp)).symm ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic
      (continuousModuleRes.{0, u + 1, u + 1} R φ₀)
      (kernelInvariantsFunctor.{0, u + 1, u, u + 1} R π' hπ' ⋙
        continuousModuleRes.{0, u, u + 1} R (ContinuousMonoidHom.toContinuousMonoidHom ψ))
      (fun I hI ↦ by
        have : (continuousModuleRes.{0, u + 1, u + 1} R φ₀).PreservesInjectiveObjects :=
          Functor.preservesInjectiveObjects_of_isEquivalence
        have : Injective ((continuousModuleRes.{0, u + 1, u + 1} R φ₀).obj I) :=
          Functor.PreservesInjectiveObjects.injective_obj hI
        exact Functor.rightAcyclic_of_injective _
          ((continuousModuleRes.{0, u + 1, u + 1} R φ₀).obj I)) ≪≫
    Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        (continuousModuleRes.{0, u + 1, u + 1} R φ₀)) _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic
          (kernelInvariantsFunctor.{0, u + 1, u, u + 1} R π' hπ')
          (continuousModuleRes.{0, u, u + 1} R (ContinuousMonoidHom.toContinuousMonoidHom ψ))
          (fun _ _ ↦ (continuousModuleRes.{0, u, u + 1} R
            (ContinuousMonoidHom.toContinuousMonoidHom ψ)).rightAcyclic_of_exact _) ≪≫
        Functor.isoWhiskerLeft _
          (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
            (continuousModuleRes.{0, u, u + 1} R (ContinuousMonoidHom.toContinuousMonoidHom ψ))))

end Kernel

end Stacks.GroupCohomology

end
