module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.KummerFlagClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionByZeroClosedSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification

/-!
# Adapted maps for a Kummer point class exist and are unique

Let `n : U ⟶ Y` be an open immersion and `D` a flag of `d` divisor data on `U`, with closed parts
`W_0, …, W_{d-1}`. The flag sheaf `E_0 ⋯ E_{d-1} Λ_U` vanishes away from `W_0 ∩ ⋯ ∩ W_{d-1}`
(`Stacks.EtaleCohomology.KummerFlag.isZero_restriction_flagSheaf`): `E_m = i_{m*} i_m⁻¹` kills the
open complement of `W_m` and commutes with restriction to opens. When that intersection is closed
in `Y` (more precisely: `Y = U ∪ O` with `O ∩ U` disjoint from it), restriction to `U` is
bijective on maps `Λ_Y ⟶ n_!(E_0 ⋯ E_{d-1} Λ_U)`
(`Stacks.EtaleCohomology.bijective_etaleModuleRestriction_map_extensionByZero`), so a map
adapted to the canonical map `Λ_U ⟶ E_0 ⋯ E_{d-1} Λ_U` exists and is unique
(`Stacks.EtaleCohomology.KummerFlag.existsUnique_isAdapted`).

## Main results

* `Stacks.EtaleCohomology.KummerFlag.isZero_restriction_flagSheaf`
* `Stacks.EtaleCohomology.KummerFlag.existsUnique_isAdapted`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology.KummerFlag

variable {N : ℕ}

/-- `E_W = i_* i⁻¹` preserves vanishing on an open: if `Q|_T = 0` then `(i_* i⁻¹ Q)|_T = 0`. -/
theorem isZero_restriction_closedRestriction {U W T : Scheme.{u}} (i : W ⟶ U)
    (o : T ⟶ U) [IsOpenImmersion o] (Q : EtaleModules.{u, 0} (ZMod N) U)
    (hQ : IsZero ((etaleModuleRestriction.{u, 0} (ZMod N) o).obj Q)) :
    IsZero ((etaleModuleRestriction.{u, 0} (ZMod N) o).obj
      ((closedRestriction (N := N) i).obj Q)) := by
  have h₁ : IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) o).obj Q) :=
    hQ.of_iso ((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) o).app Q)
  have h₂ : IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) (pullback.fst o i ≫ o)).obj Q) :=
    (Functor.map_isZero (etaleModuleInverseImage.{u, 0} (ZMod N) (pullback.fst o i)) h₁).of_iso
      ((etaleModuleInverseImageCompIso.{u, 0} (ZMod N) (pullback.fst o i) o).app Q)
  rw [pullback.condition] at h₂
  have h₃ : IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) (pullback.snd o i)).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj Q)) :=
    h₂.of_iso ((etaleModuleInverseImageCompIso.{u, 0} (ZMod N) (pullback.snd o i) i).app Q).symm
  have h₄ : IsZero ((etaleModuleRestriction.{u, 0} (ZMod N) (pullback.snd o i)).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj Q)) :=
    h₃.of_iso
      ((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) (pullback.snd o i)).app _).symm
  exact (Functor.map_isZero (etaleModuleDirectImage.{u, 0} (ZMod N) (pullback.fst o i)) h₄).of_iso
    ((etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{u + 1} (ZMod N))
      (IsPullback.of_hasPullback o i)).app _).symm

/-- **The flag sheaf vanishes off the closed part of each divisor**: on an open `T ⊆ U` disjoint
from some `W_m`, `(E_0 ⋯ E_{d-1} Λ_U)|_T = 0`. -/
theorem isZero_restriction_flagSheaf {U : Scheme.{u}} : ∀ {d : ℕ} (D : Fin d → DivisorDatum U)
    {T : Scheme.{u}} (o : T ⟶ U) [IsOpenImmersion o] (m : Fin d)
    (_ : Disjoint (Set.range o.base) (Set.range (D m).i.base)),
    IsZero ((etaleModuleRestriction.{u, 0} (ZMod N) o).obj (flagSheaf (N := N) D))
  | 0, _, _, _, _, m, _ => m.elim0
  | d + 1, D, T, o, _, m, hm => by
    refine Fin.cases (motive := fun m => Disjoint (Set.range o.base) (Set.range (D m).i.base) →
      IsZero ((etaleModuleRestriction.{u, 0} (ZMod N) o).obj (flagSheaf (N := N) D))) ?_ ?_ m hm
    · intro h0
      exact isZero_etaleModuleRestriction_etaleModuleDirectImage_of_disjoint (ZMod N) (D 0).i o
        h0.symm _
    · intro m' hm'
      exact isZero_restriction_closedRestriction (D 0).i o _
        (isZero_restriction_flagSheaf (fun m => D m.succ) o m' hm')

/-- **The flag sheaf vanishes off the intersection of the closed parts**: on an open `T ⊆ U`
none of whose points lies on every `W_m`, `(E_0 ⋯ E_{d-1} Λ_U)|_T = 0`. -/
theorem isZero_restriction_flagSheaf_of_forall {U : Scheme.{u}} {d : ℕ}
    (D : Fin d → DivisorDatum U) {T : Scheme.{u}} (o : T ⟶ U) [IsOpenImmersion o]
    (hT : ∀ t : T, ∃ m, o.base t ∉ Set.range (D m).i.base) :
    IsZero ((etaleModuleRestriction.{u, 0} (ZMod N) o).obj (flagSheaf (N := N) D)) := by
  refine isZero_of_isZero_etaleModuleRestriction (ZMod N)
    (fun m : Fin d => pullback.fst o (D m).j) (fun t => ?_) _ fun m => ?_
  · obtain ⟨m, hm⟩ := hT t
    have hm' : o.base t ∈ Set.range (D m).j.base := by rw [(D m).range_eq]; exact hm
    refine ⟨m, ?_⟩
    rw [Scheme.Pullback.range_fst]
    exact hm'
  · refine (isZero_restriction_flagSheaf D (pullback.fst o (D m).j ≫ o) m ?_).of_iso
      ((etaleModuleRestrictionCompIso (ZMod N) (pullback.fst o (D m).j) o).app
        (flagSheaf (N := N) D))
    rw [Set.disjoint_iff]
    rintro _ ⟨⟨t, rfl⟩, ⟨w, hw⟩⟩
    have h1 : (pullback.fst o (D m).j ≫ o).base t ∈ Set.range (D m).j.base := by
      rw [pullback.condition]
      exact ⟨_, rfl⟩
    rw [(D m).range_eq] at h1
    exact h1 ⟨w, hw⟩

variable {Y U O : Scheme.{u}} (n : U ⟶ Y) [IsOpenImmersion n] (m : O ⟶ Y) [IsOpenImmersion m]

/-- **A map adapted to the canonical map of a flag exists and is unique**, when `Y = U ∪ O` and
no point of `U ∩ O` lies on every closed part `W_m` of the flag (so the intersection of the `W_m`
is closed in `Y`). -/
theorem existsUnique_isAdapted [NeZero N] {d : ℕ} (D : Fin d → DivisorDatum U)
    (hcov : ∀ y : Y, y ∈ Set.range n.base ∨ y ∈ Set.range m.base)
    (hZ : ∀ x : U, n.base x ∈ Set.range m.base → ∃ k, x ∉ Set.range (D k).i.base) :
    ∃! z, IsAdapted n (flagUnit (N := N) D) z := by
  have hP : IsZero ((etaleModuleRestriction.{u, 0} (ZMod N) (pullback.snd m n)).obj
      (flagSheaf (N := N) D)) := by
    refine isZero_restriction_flagSheaf_of_forall D (pullback.snd m n) fun t => hZ _ ?_
    refine ⟨pullback.fst m n |>.base t, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have := isIso_extensionByZeroToDirectImage_of_isZero (ZMod N) n m (pullback.snd m n)
    (pullback.fst m n) (IsPullback.of_hasPullback m n) hcov _ hP
  have hb := bijective_etaleModuleRestriction_map_extensionByZero (ZMod N) n
    (unitSheaf (X := Y) N) (flagSheaf (N := N) D)
  obtain ⟨z, hz⟩ := hb.2 ((restrictionUnitSheafIso (N := N) n).hom ≫ flagUnit (N := N) D ≫
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) n).unit.app _)
  exact ⟨z, hz, fun z' hz' => hb.1 (hz'.trans hz.symm)⟩

end Stacks.EtaleCohomology.KummerFlag

end
