module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ArtinReesChain
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.SheafPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.FormalFunctions Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

variable (A : Type u) [CommRing A] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A))

/-- **Artin-Rees for the global functions of a proper scheme** ([Stacks, Tag 02OB], clause (1),
for the structure sheaf): a global function which, on every affine open, lies in the `n`-th power
of `I · 𝒪_Y`, lies in `I ⁿ⁻ᶜ Γ(Y, 𝒪_Y)` for a constant `c` independent of `n`. -/
theorem exists_mem_pow_smul_top_of_forall_affineOpens [IsNoetherianRing A] [IsProper g]
    (I : Ideal A) :
    letI := (baseRingHom A g).toAlgebra
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ y : Γ(Y, ⊤),
      (∀ U : Y.affineOpens, Y.presheaf.map (homOfLE le_top : U.1 ⟶ ⊤).op y ∈
        (baseIdealSheaf A I g).ideal U ^ n) →
      y ∈ I ^ (n - c) • (⊤ : Submodule A Γ(Y, ⊤)) := by
  let := (baseRingHom A g).toAlgebra
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : (Scheme.unitModule Y).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  obtain ⟨c, hc, -, -⟩ := exists_uniform_bound_cohomology_idealPowerQuotient_of_isProper A g I
    (Scheme.unitModule Y) inferInstance 0
  refine ⟨c, fun n hn y hy => ?_⟩
  let G := Scheme.unitModule Y
  let P := idealPowerMultiple (baseIdealSheaf A I g) n G
  have hmem : y ∈ P.toSubmodule.obj (op ⊤) := by
    refine Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf.mem_of_forall_affineOpens P y
      fun W hW => ?_
    have h₁ : G.presheaf.map (homOfLE hW).op y =
        (Y.presheaf.map (homOfLE le_top : W.1 ⟶ ⊤).op y) •
          (show Γ(G, W.1) from (1 : Γ(Y, W.1))) :=
      (mul_one (Y.presheaf.map (homOfLE le_top : W.1 ⟶ ⊤).op y)).symm
    rw [idealPowerMultiple_toSubmodule_obj_affine, h₁]
    exact Submodule.smul_mem_smul (hy W) Submodule.mem_top
  let e := moduleGlobalSectionsRightDerivedZeroIso Y
  let y' : (AlgebraicGeometry.moduleGlobalSections Y).obj G := y
  let x : ((AlgebraicGeometry.moduleGlobalSections Y).rightDerived 0).obj G := (e.app G).inv y'
  have hex : (e.app G).hom.hom x = y' := by
    change ((e.app G).inv ≫ (e.app G).hom).hom y' = y'
    rw [Iso.inv_hom_id]
    rfl
  have hx : (((AlgebraicGeometry.moduleGlobalSections Y).rightDerived 0).map
      (cokernel.π (C := Y.Modules) P.ι)).hom x = 0 := by
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback (e.app _).hom)
    rw [map_zero]
    have hnat := congrArg (fun φ => φ.hom x) (e.hom.naturality (cokernel.π (C := Y.Modules) P.ι))
    refine hnat.trans ?_
    change ((AlgebraicGeometry.moduleGlobalSections Y).map (cokernel.π (C := Y.Modules) P.ι)).hom
      ((e.app G).hom.hom x) = 0
    rw [hex]
    exact (cokernel_π_app_eq_zero_iff G P ⊤ y).2 hmem
  let φ : cohomologyOverBase A g 0 G →ₗ[A] Γ(Y, ⊤) :=
    { toFun := fun z => (e.app G).hom.hom z
      map_add' := fun z w => map_add (e.app G).hom.hom z w
      map_smul' := fun a z =>
        (e.app G).hom.hom.map_smul (baseRingHom A g a)
          (show ((AlgebraicGeometry.moduleGlobalSections Y).rightDerived 0).obj G from z) }
  have hφ : φ x = y := hex
  have := Submodule.mem_map_of_mem (f := φ) (hc n hn hx)
  rw [Submodule.map_smul'', Submodule.map_top, hφ] at this
  exact Submodule.smul_mono le_rfl le_top this

end AlgebraicGeometry
