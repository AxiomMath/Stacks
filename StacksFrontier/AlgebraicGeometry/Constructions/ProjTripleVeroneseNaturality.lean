module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleDegreeFunctor

/-!
# The Veronese comparison `(L^{⊗ k}) ^⊗ m ≅ L ^⊗ (km)` is natural in `L`

Let `Y` be a scheme, `β : L ≅ L'` an isomorphism of `𝒪_Y`-modules and `k` a weight.
`Stacks.AlgebraicGeometry.ProjVeroneseRestrict.powVeroneseIso` compares the two presentations
`(L^{⊗ k}) ^⊗ m` and `L ^⊗ (km)` of the `m`-th tensor power of `L^{⊗ k}`. This file proves that
comparison **natural in `L`**: conjugating it by the tensor powers of `β` on both sides gives the
comparison for `L'`, where the left-hand side is the `m`-th tensor power of `β^{⊗ k}` and the
right-hand side the `(km)`-th tensor power of `β`.

## Main results

* `Stacks.Monoidal.PowerSystem.compare_trans`: the comparison isomorphisms of power systems
  compose, the comparison along `β` followed by the one along `γ` being the one along `β ≪≫ γ`.
* `Stacks.Monoidal.PowerSystem.compare_veronese_compare`: the comparison of the two `k`-th
  Veronese systems along the degree-`k` comparison is the degree-`km` comparison. In the language
  of tensor powers, `(β^{⊗ k})^{⊗ m} = β^{⊗ km}` with both `(L^{⊗ k})^{⊗ m}` and `L^{⊗ km}`
  presented as `L^{⊗ km}`.
* `Stacks.AlgebraicGeometry.ProjVeroneseRestrict.powVeroneseIso_natTensorPowCongr`: the
  comparison `(L^{⊗ k}) ^⊗ m ≅ L ^⊗ (km)` is natural in `L`.

## Implementation notes

`compare_veronese_compare` is not the specialisation of
`Stacks.Monoidal.PowerSystem.compare_veronese_veronese` to `a = a' = 1`: `S.veronese 1` is the
system `n ↦ S.obj (1 * n)` and not `S`, and `1 * n` does not reduce for a variable `n`, so that
specialisation would need a transport in every degree.

## References

* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace
open AlgebraicGeometry
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.GradedSections (natPowerSystem)
open Stacks.TensorPowers (natTensorPow)

namespace Stacks.Monoidal.PowerSystem

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The comparison isomorphisms of power systems compose**: comparing `S` with `T` along
`β : S.gen ≅ T.gen` and then `T` with `U` along `γ : T.gen ≅ U.gen` is comparing `S` with `U`
along `β ≪≫ γ`. -/
theorem compare_trans (S T U : PowerSystem C) (β : S.gen ≅ T.gen) (γ : T.gen ≅ U.gen) : ∀ n : ℕ,
    compare S T β n ≪≫ compare T U γ n = compare S U (β ≪≫ γ) n
  | 0 => by
      simp only [compare_zero]
      exact Iso.ext (by simp)
  | n + 1 => by
      simp only [compare_succ]
      rw [← compare_trans S T U β γ n]
      refine Iso.ext ?_
      simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Category.assoc,
        Iso.hom_inv_id_assoc]
      rw [← tensorHom_comp_tensorHom, Category.assoc]

/-- **The comparison of the two `k`-th Veronese systems along the degree-`k` comparison is the
degree-`km` comparison.** In the language of tensor powers this is `(β^{⊗ k})^{⊗ m} = β^{⊗ km}`,
with both sides' `m`-th power of the `k`-th power presented as the `km`-th power. -/
theorem compare_veronese_compare (S T : PowerSystem C) (β : S.gen ≅ T.gen) (k : ℕ) : ∀ m : ℕ,
    compare (S.veronese k) (T.veronese k) (compare S T β k) m = compare S T β (k * m)
  | 0 => rfl
  | m + 1 => by
      change compare (S.veronese k) (T.veronese k) (compare S T β k) (m + 1)
        = compare S T β (k * m + k)
      rw [compare_succ, compare_veronese_compare S T β k m]
      refine Iso.ext ?_
      simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom]
      rw [compare_mul S T β (k * m) k, Iso.inv_hom_id_assoc]

end Stacks.Monoidal.PowerSystem

namespace Stacks.AlgebraicGeometry.ProjVeroneseRestrict

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

universe u

open Stacks.Monoidal (PowerSystem)

variable {Y : Scheme.{u}} {L L' : Y.Modules}

/-- **The comparison `(L^{⊗ k}) ^⊗ m ≅ L ^⊗ (km)` is natural in `L`.** Conjugating it by the
tensor powers of an isomorphism `β : L ≅ L'` — the `m`-th power of `β^{⊗ k}` on the iterated side
and the `km`-th power of `β` on the Veronese side — gives the comparison for `L'`. -/
theorem powVeroneseIso_natTensorPowCongr (β : L ≅ L') (k m : ℕ) :
    natTensorPowCongr (natTensorPowCongr β k) m ≪≫ powVeroneseIso L' k m
      = powVeroneseIso L k m ≪≫ natTensorPowCongr β (k * m) := by
  have hγ : natTensorPowCongr β k
      = PowerSystem.compare (natPowerSystem L) (natPowerSystem L') β k :=
    ProjTripleClassifying.natTensorPowCongr_eq_compare β k
  have hleft : natTensorPowCongr (natTensorPowCongr β k) m ≪≫ powVeroneseIso L' k m
      = PowerSystem.compare (natPowerSystem (natTensorPow L k))
          ((natPowerSystem L').veronese k) (natTensorPowCongr β k) m := by
    rw [ProjTripleClassifying.natTensorPowCongr_eq_compare (natTensorPowCongr β k) m,
      powVeroneseIso, PowerSystem.compare_trans]
    congr 1
  have hright : powVeroneseIso L k m ≪≫ natTensorPowCongr β (k * m)
      = PowerSystem.compare (natPowerSystem (natTensorPow L k))
          ((natPowerSystem L').veronese k) (natTensorPowCongr β k) m := by
    rw [powVeroneseIso, hγ, ProjTripleClassifying.natTensorPowCongr_eq_compare β (k * m),
      ← PowerSystem.compare_veronese_compare (natPowerSystem L) (natPowerSystem L') β k m,
      PowerSystem.compare_trans]
    congr 1
  rw [hleft, hright]

/-- The inverse comparison for `L` followed by the `m`-th tensor power of `β^{⊗ k}` is the `km`-th
tensor power of `β` followed by the inverse comparison for `L'`. -/
theorem inv_comp_natTensorPowCongr (β : L ≅ L') (k m : ℕ) :
    (powVeroneseIso L k m).inv ≫ (natTensorPowCongr (natTensorPowCongr β k) m).hom
      = (natTensorPowCongr β (k * m)).hom ≫ (powVeroneseIso L' k m).inv := by
  have h := congrArg Iso.hom (powVeroneseIso_natTensorPowCongr β k m)
  simp only [Iso.trans_hom] at h
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact h

/-- On global sections, the `m`-th tensor power of `β^{⊗ k}` carries the image of a section of
`L ^⊗ (km)` under the inverse comparison for `L` to the image of its `β^{⊗ km}`-translate under the
inverse comparison for `L'`. -/
theorem natTensorPowCongr_app_powVeroneseIso_inv (β : L ≅ L') (k m : ℕ)
    (z : Γ(natTensorPow L (k * m), ⊤)) :
    (natTensorPowCongr (natTensorPowCongr β k) m).hom.app ⊤
        ((powVeroneseIso L k m).inv.app ⊤ z)
      = (powVeroneseIso L' k m).inv.app ⊤ ((natTensorPowCongr β (k * m)).hom.app ⊤ z) := by
  have h := congrArg (fun φ : natTensorPow L (k * m) ⟶ natTensorPow (natTensorPow L' k) m =>
    φ.app ⊤ z) (inv_comp_natTensorPowCongr β k m)
  simpa only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] using h

end Stacks.AlgebraicGeometry.ProjVeroneseRestrict

end
