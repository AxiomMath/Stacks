module

public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Epi
public import StacksFrontier.AlgebraicGeometry.ProjInclusionDegreeSection.Unit

/-!
# Pulled-back sections over an arbitrary open, and the pseudofunctoriality of the inverse image

`Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection f M U x` is the image of a section
`x` of `M` over an open `U` in the sections of `f^*M` over `f⁻¹U`, under the unit of
`pullback ⊣ pushforward`. `Stacks.AlgebraicGeometry.PullbackUnit` follows *global* sections
through the structural isomorphisms of the inverse image; this file does the same over an
arbitrary open, by the same argument (`CategoryTheory.unit_conjugateEquiv`) read at `U` instead of
`⊤`, and records the naturality of the operation in the open.

## Main results

* `Stacks.Chow.GenuineChern.unitSection_restrict`: the operation commutes with restriction.
* `Stacks.Chow.GenuineChern.pullbackComp_inv_unitSection` and `pullbackComp_hom_unitSection`:
  along a composite.
* `Stacks.Chow.GenuineChern.pullbackCongr_hom_unitSection` and
  `pullbackCongr_inv_unitSection`: along two equal morphisms.
* `Stacks.Chow.GenuineChern.pullbackId_hom_unitSection`: along the identity.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Chow.GenuineChern

open Stacks.AlgebraicGeometry.RelativeProjDegreeOne

variable {X Y Z : Scheme.{u}}

/-- **Naturality in the open.** Pulling back a restricted section is restricting the pulled-back
section. -/
theorem unitSection_restrict (f : X ⟶ Y) (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U)
    (x : Γ(M, U)) :
    unitSection f M V (M.val.map (homOfLE h).op x) =
      ((Scheme.Modules.pullback f).obj M).val.map (homOfLE (f.preimage_mono h)).op
        (unitSection f M U x) :=
  PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val (homOfLE h).op x

/-- Equal morphisms of modules agree on every section over an open. -/
private theorem val_app_congr {M N : Y.Modules} {ρ σ : M ⟶ N} (h : ρ = σ) (U : Y.Opens)
    (s : Γ(M, U)) : ρ.val.app (op U) s = σ.val.app (op U) s := by
  rw [h]

/-- **Composition, backwards**, over an arbitrary open. -/
theorem pullbackComp_inv_unitSection (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens)
    (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U))
        (unitSection (f ≫ g) M U s) =
      unitSection f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) (unitSection g M U s) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  exact (val_app_congr h U s).symm

/-- **Composition, forwards**, over an arbitrary open. -/
theorem pullbackComp_hom_unitSection (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens)
    (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U))
        (unitSection f ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) (unitSection g M U s)) =
      unitSection (f ≫ g) M U s :=
  (congrArg (((Scheme.Modules.pullbackComp f g).hom.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U)))
      (pullbackComp_inv_unitSection f g M U s).symm).trans
    (Stacks.AlgebraicGeometry.PullbackUnit.natIso_hom_inv_app
      (Scheme.Modules.pullbackComp f g) M _ _)

/-- **Congruence**: the operation does not see which of two equal morphisms it is formed with. -/
theorem pullbackCongr_hom_unitSection {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules) (U : Y.Opens)
    (s : Γ(M, U)) :
    HEq (((Scheme.Modules.pullbackCongr hf).hom.app M).val.app (op (f ⁻¹ᵁ U))
        (unitSection f M U s)) (unitSection g M U s) := by
  subst hf
  rfl

/-- **Congruence, backwards.** -/
theorem pullbackCongr_inv_unitSection {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules) (U : Y.Opens)
    (s : Γ(M, U)) :
    HEq (((Scheme.Modules.pullbackCongr hf).inv.app M).val.app (op (g ⁻¹ᵁ U))
        (unitSection g M U s)) (unitSection f M U s) := by
  subst hf
  rfl

/-- **The identity**, over an arbitrary open. -/
theorem pullbackId_hom_unitSection (W : Scheme.{u}) (M : W.Modules) (U : W.Opens)
    (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackId W).hom.app M).val.app (op U) (unitSection (𝟙 W) M U s) = s := by
  have h := unit_conjugateEquiv (Adjunction.id)
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 W))
    (Scheme.Modules.pullbackId W).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact (val_app_congr h U s).symm

end Stacks.Chow.GenuineChern

end
