module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.CoordinateSections
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence

/-!
# Zero schemes of coordinate sections

The zero scheme `Z(s)` of a global section `s` of an invertible module ([Stacks, Tag 02OQ]) does
not change when `s` is multiplied by a unit, and the zero scheme of a coordinate section
`Σⱼ q^*(cⱼ) · p^*(wⱼ)` pulls back to the zero scheme of the pulled-back coordinate section.

## Main results

* `Stacks.LinearSystemScheme.zeroScheme_unit_smul`: `Z(u s) = Z(s)` for a unit `u`.
* `Stacks.LinearSystemScheme.comap_zeroScheme_coordSection`: the inverse image of the zero scheme
  of a coordinate section along `h` is the zero scheme of the coordinate section for `h ≫ p`,
  `h ≫ q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.LinearSystemScheme

variable {X Y Y' T T' : Scheme.{u}}

/-- **The zero scheme of a section is unchanged by a unit multiple.** -/
theorem zeroScheme_unit_smul (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤))
    {r : Γ(X, ⊤)} (hr : IsUnit r) :
    zeroScheme X L (r • s) = zeroScheme X L s := by
  refine congrArg Scheme.IdealSheafData.ofIdeals (funext fun U => congrArg Ideal.span ?_)
  have hrU : IsUnit (X.presheaf.map (homOfLE (le_top (a := U.1))).op r) :=
    hr.map (X.presheaf.map (homOfLE (le_top (a := U.1))).op).hom
  ext a
  simp only [Set.mem_setOf_eq, Scheme.Modules.map_smul]
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨X.presheaf.map (homOfLE (le_top (a := U.1))).op r • φ, ?_⟩
    rw [LinearMap.smul_apply, map_smul]
  · rintro ⟨φ, rfl⟩
    refine ⟨(↑hrU.unit⁻¹ : Γ(X, U.1)) • φ, ?_⟩
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      hrU.val_inv_mul, one_mul]

variable (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  {n : ℕ} (w : Fin n → Γ(L, ⊤))

/-- **The zero scheme of a coordinate section pulls back to the zero scheme of the pulled-back
coordinate section.** -/
theorem comap_zeroScheme_coordSection (h : Y' ⟶ Y) (p : Y ⟶ X) (q : Y ⟶ T)
    (c : Fin n → Γ(T, ⊤)) :
    (zeroScheme Y ((Scheme.Modules.pullback p).obj L) (coordSection p q L w c)).comap h =
      zeroScheme Y' ((Scheme.Modules.pullback (h ≫ p)).obj L)
        (coordSection (h ≫ p) (h ≫ q) L w c) := by
  rw [← Stacks.Divisors.zeroScheme_pullback]
  exact zeroScheme_eq_of_iso ((Scheme.Modules.pullbackComp h p).app L)
    (coordSection_pullback h p q L w c)

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- Reading the base map of a coordinate section through a factorization. -/
theorem coordSection_comp (p : Y ⟶ X) (q : Y ⟶ T') (g : T' ⟶ T) (c : Fin n → Γ(T, ⊤)) :
    coordSection p (q ≫ g) L w c = coordSection p q L w (fun j => g.appTop (c j)) := by
  simp only [coordSection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

end Stacks.LinearSystemScheme

end
