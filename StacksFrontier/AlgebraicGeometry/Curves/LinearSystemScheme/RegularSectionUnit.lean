module

public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealGeometricStalk

/-!
# Sections with the same zero scheme differ by a unit

Let `M` be an invertible `𝒪_X`-module and `s, s'` global sections with the same zero scheme
([Stacks, Tag 02OQ]), which is an effective Cartier divisor. Then `s' = u s` for a unit `u` of
`Γ(X, 𝒪_X)`: on a trivializing affine open the two sections are nonzerodivisors generating the
same principal ideal, hence associates, and the local ratios glue.

## Main results

* `Stacks.LinearSystemScheme.exists_isUnit_smul_eq_of_zeroScheme_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.LinearSystemScheme

variable {X : Scheme.{u}} (M : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]

/-- Multiplication by a section whose zero scheme is an effective Cartier divisor is injective on
the sections over every open. -/
theorem smul_res_injective {s : Γ(M, ⊤)}
    (hs : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X M s)) (V : X.Opens)
    {r r' : Γ(X, V)}
    (h : r • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s =
      r' • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s) : r = r' := by
  have hreg := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X M
    (Stacks.Divisors.sectionsOfTop M s)).mp (by rwa [Stacks.Divisors.sectionsOfTop_eval_top])
  apply Scheme.Modules.injective_unitHomEquiv_symm_app_of_isRegularSection M _ hreg V
  rwa [Scheme.Modules.unitHomEquiv_symm_app_apply, Scheme.Modules.unitHomEquiv_symm_app_apply,
    Stacks.Divisors.sectionsOfTop_eval_top]

/-- **Locally, two sections with the same effective Cartier zero scheme differ by a unit.** -/
theorem exists_local_unit {s s' : Γ(M, ⊤)} (hZ : zeroScheme X M s = zeroScheme X M s')
    (hs : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X M s)) (x : X) :
    ∃ (V : X.Opens) (r : Γ(X, V)), x ∈ V ∧ IsUnit r ∧
      M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s' =
        r • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s := by
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem x
  obtain ⟨g, hxg, -, ⟨e⟩⟩ := exists_basicOpen_linearEquiv M U x hxU
  set V : X.affineOpens := ⟨X.basicOpen g, U.2.basicOpen g⟩
  have h1 := zeroScheme_ideal_of_trivialization X M s V e _ rfl
  have h2 := zeroScheme_ideal_of_trivialization X M s' V e _ rfl
  rw [hZ, h2] at h1
  set a := e (M.presheaf.map (homOfLE le_top).op s)
  set a' := e (M.presheaf.map (homOfLE le_top).op s')
  obtain ⟨r, hr⟩ : a ∣ a' := Ideal.mem_span_singleton.mp (h1 ▸ Ideal.mem_span_singleton_self a')
  obtain ⟨r', hr'⟩ : a' ∣ a :=
    Ideal.mem_span_singleton.mp (h1.symm ▸ Ideal.mem_span_singleton_self a)
  have hareg : ∀ b b' : Γ(X, V.1), b * a = b' * a → b = b' := by
    intro b b' hbb
    refine smul_res_injective M hs V.1 ?_
    apply e.injective
    rwa [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hrr : r * r' = 1 := hareg _ _ (by linear_combination (-r') * hr - hr')
  refine ⟨V.1, r, hxg, IsUnit.of_mul_eq_one r' hrr, ?_⟩
  apply e.injective
  rw [map_smul, smul_eq_mul]
  change a' = r * a
  rw [hr, mul_comm]

/-- **Two sections of an invertible module with the same effective Cartier zero scheme differ by a
global unit.** -/
theorem exists_isUnit_smul_eq_of_zeroScheme_eq {s s' : Γ(M, ⊤)}
    (hZ : zeroScheme X M s = zeroScheme X M s')
    (hs : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X M s)) :
    ∃ u : Γ(X, ⊤), IsUnit u ∧ s' = u • s := by
  choose V r hxV hr hV using exists_local_unit M hZ hs
  have hcov : (⊤ : X.Opens) ≤ iSup V := fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩
  have hres : ∀ {W W' : X.Opens} (h : W' ≤ W) (y : Γ(M, ⊤)),
      M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op y) =
        M.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op y := by
    intro W W' h y
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hloc : ∀ (x : X) {W : X.Opens} (h : W ≤ V x),
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s' =
        X.presheaf.map (homOfLE h).op (r x) • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s := by
    intro x W h
    rw [← hres h s', hV x, Scheme.Modules.map_smul, hres h s]
  obtain ⟨u, hu, -⟩ := X.sheaf.existsUnique_gluing' V ⊤ (fun x => homOfLE le_top) hcov r
    (fun x y => smul_res_injective M hs _
      ((hloc x inf_le_left).symm.trans (hloc y inf_le_right)))
  set u' : Γ(X, ⊤) := u
  have hu' : ∀ x, X.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op u' = r x := hu
  refine ⟨u', ?_, ?_⟩
  · refine Scheme.isUnit_of_basicOpen_eq_top u' (eq_top_iff.mpr fun x _ => ?_)
    have h1 : X.basicOpen (X.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op u') =
        V x := by
      rw [hu' x]
      exact X.basicOpen_of_isUnit (hr x)
    have h2 := X.basicOpen_res u' (homOfLE (le_top : V x ≤ ⊤)).op
    have := hxV x
    rw [← h1, h2] at this
    exact this.2
  · refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨M.presheaf, M.isSheaf⟩) V ⊤
      (fun x => homOfLE le_top) hcov _ _ fun x => ?_
    change M.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op s' =
      M.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op (u' • s)
    rw [hV x, Scheme.Modules.map_smul, hu' x]

end Stacks.LinearSystemScheme

end
