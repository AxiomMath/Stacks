module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationDirectedSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationSetBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationComponentLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base change map to the strict henselization, on global sections

For `φ : A ⟶ S` quasi-compact and quasi-separated and a geometric point `s` of `S`, the base
change map of sheaves of sets of the square of `φ` over the strict henselization
`π : Spec 𝒪^{sh}_{S,s} ⟶ S` is bijective on global sections over the strict henselization: this
is `Stacks.EtaleCohomology.EtaleLimitSections.bijective_smallEtaleSetBaseChange_app_unit` for the
system of affine étale neighbourhoods of `s` (`AlgebraicGeometry.nbhdConeIsLimit`).

## Main results

* `Stacks.EtaleCohomology.isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization`.
* `Stacks.EtaleCohomology.isIso_inverseImage_smallEtaleSetBaseChange_strictHenselization`: the
  base change map becomes an isomorphism after inverse image along the canonical lift of `s`
  (Stacks 03Q9 in degree zero, for sheaves of sets).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **The base change map to the strict henselization is bijective on global sections.** -/
theorem isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization {A : Scheme.{u}} (φ : A ⟶ S)
    [QuasiCompact φ] [QuasiSeparated φ] (F : Sheaf A.smallEtaleTopology (Type (u + 1))) :
    IsIso ((Sheaf.Γ (strictHenselization B S hS s).smallEtaleTopology (Type (u + 1))).map
      ((smallEtaleSetBaseChange.{u, 0} (pullback.fst φ (strictHenselizationToBase B S hS s))
        (pullback.snd φ (strictHenselizationToBase B S hS s)) φ (strictHenselizationToBase B S hS s)
        pullback.condition).app F)) := by
  obtain ⟨α, _, _, ⟨a₀⟩, G, _⟩ := exists_directed_nbhd B S hS s
  exact EtaleLimitSections.isIso_Γ_map_smallEtaleSetBaseChange_of_eq
    (nbhdSystem B S hS s G a₀) (nbhdCone B S hS s G a₀) φ (nbhdConeIsLimit B S hS s G a₀)
    (T := strictHenselization B S hS s) rfl (π' := strictHenselizationToBase B S hS s)
    (fun i => (nbhdCone_π_comp_hom B S hS s G a₀ i).trans (Category.id_comp _).symm) F

/-- **Stacks Project, Tag 03Q9 for sheaves of sets in degree zero.** Let `φ : A ⟶ S` be
quasi-compact and quasi-separated, `s` a geometric point of `S`, `π : Spec 𝒪^{sh}_{S,s} ⟶ S` the
strict henselization and `s̃` the canonical lift of `s` to it. For a sheaf of sets `F` on the small
étale site of `A`, the base change map `π⁻¹ φ_* F ⟶ (φ_π)_* p⁻¹ F` of the square of `φ` over `π`
becomes an isomorphism after inverse image along `s̃`: its stalk at `s̃` is the map
`(φ_* F)_{s} ⟶ Γ(A ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹F)`.

Over `Spec` of a separably closed field, stalks at the canonical point detect isomorphisms; the
stalk of `s̃⁻¹` there is the stalk at `s̃`, which is global sections over the strictly henselian
`Spec 𝒪^{sh}_{S,s}` since `s̃` lies over its closed point, and on global sections the base change
map is bijective (`isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization`). -/
@[sga "4 VIII 5.2" "degree q = 0"]
theorem isIso_inverseImage_smallEtaleSetBaseChange_strictHenselization {A : Scheme.{u}}
    (φ : A ⟶ S) [QuasiCompact φ] [QuasiSeparated φ]
    (F : Sheaf A.smallEtaleTopology (Type (u + 1))) :
    IsIso ((smallEtaleInverseImage.{u, 0} (geometricPointToStrictHenselization B S hS s)).map
      ((smallEtaleSetBaseChange.{u, 0} (pullback.fst φ (strictHenselizationToBase B S hS s))
        (pullback.snd φ (strictHenselizationToBase B S hS s)) φ (strictHenselizationToBase B S hS s)
        pullback.condition).app F)) := by
  refine isIso_of_geometricStalk_family.{0, u} (Ω := fun _ : PUnit.{u + 1} ↦ s.residueField)
    (fun _ ↦ 𝟙 (Spec (.of s.residueField))) ?_ _ (fun _ ↦ ?_)
  · ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨PUnit.unit, x, rfl⟩
  · let e := Functor.isoWhiskerLeft
        (smallEtaleInverseImage.{u, 0} (geometricPointToStrictHenselization B S hS s))
        (sheafFiberIdIsoGamma.{u, 0} s.residueField) ≪≫
      (stalkIsoInverseImageGamma.{u, 0} (geometricPointToStrictHenselization B S hS s)).symm ≪≫
      sheafFiberClosedPointIsoGamma.{u, 0} (geometricPointToStrictHenselization B S hS s)
        (geometricPointToStrictHenselization_base_default B S hS s)
    exact (NatIso.isIso_map_iff e _).2
      (isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization B S hS s φ F)

end Stacks.EtaleCohomology
