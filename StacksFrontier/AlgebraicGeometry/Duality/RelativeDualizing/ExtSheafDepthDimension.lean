module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AssociatedShiftFunction
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth
public import StacksFrontier.RingTheory.Dualizing.DualExtDepthDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Degree range, support dimension and depth for the Ext sheaves of a dualizing complex

Let `X` be a locally Noetherian scheme, let `ω_X^•` be a dualizing complex on `X`
([Stacks, Tag 0A87]) with associated dimension function `δ` ([Stacks, Tag 0AWF]), and let `F` be
a coherent `𝒪_X`-module.  Writing

`𝓔ⁱ = 𝓔xt^{-i}_{𝒪_X}(F, ω_X^•)`,

[Stacks, Tag 0ECM] asserts that each `𝓔ⁱ` is coherent and, at every point `x`, that

1. `𝓔ⁱ_x` is nonzero only for `δ(x) ≤ i ≤ δ(x) + dim Supp(F_x)`;
2. `dim Supp(𝓔^{i + δ(x)}_x) ≤ i`;
3. `depth(F_x)` is the least `i ≥ 0` with `𝓔^{i + δ(x)}_x ≠ 0`;
4. `x ∈ Supp(⨁_{j ≤ i} 𝓔^j)` if and only if `depth(F_x) + δ(x) ≤ i`.

Clauses (1)–(4) are proved here, under the hypothesis `Stacks.Duality.IsStalkwiseDualExt`. They
are the globalisation of the local-ring statement [Stacks, Tag 0DWZ] along the identification of
the stalk of `𝓔ⁱ` with `Ext^{δ(x) - i}_{𝒪_{X,x}}(F_x, ω^•_{X,x}[-δ(x)])`.

## Main definitions

* `Stacks.Duality.IsStalkwiseDualExt`: `K` is a dualizing complex on `X` ([Stacks, Tag 0A87]);
  at each point `x` the derived stalk of `K`, shifted by `-δ(x)`, is a *normalized* dualizing
  complex `ω` over `𝒪_{X,x}` (the defining property of the dimension function `δ`,
  [Stacks, Tag 0AWF]); and the stalk of `𝓔ⁱ` at `x` is `Ext^{δ(x) - i}_{𝒪_{X,x}}(F_x, ω)` (the
  stalk computation for the Ext sheaves, [Stacks, Tag 0A6H]).

## Main results

* `Stacks.Duality.extSheaf_stalk_degree_range`: clause (1), the vanishing range.
* `Stacks.Duality.supportDim_extSheaf_stalk_le`: clause (2), the support bound.
* `Stacks.Duality.depth_stalk_eq_iInf_nontrivial_extSheaf_stalk`: clause (3), the detection of
  depth by the first nonvanishing Ext sheaf.
* `Stacks.Duality.exists_nontrivial_extSheaf_stalk_iff_depth_add_le`: clause (4).

## References

* [Stacks Project, Tag 0ECM](https://stacks.math.columbia.edu/tag/0ECM)
* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- The local reading of the Ext sheaves of a dualizing complex, at every point of `X`.

`IsStalkwiseDualExt F K δ E` says that `K` is a dualizing complex on `X` ([Stacks, Tag 0A87])
and that for every `x : X` there is a complex `ω` over the local ring `𝒪_{X,x}` such that

* `ω` is a *normalized* dualizing complex over `𝒪_{X,x}`;
* `ω` is the derived stalk at `x` of some representative of `K`, shifted by `-δ(x)`, so that
  `δ` is a dimension function associated to `K` in the sense of [Stacks, Tag 0AWF];
* the stalk of `E i` at `x` is `Ext^{δ(x) - i}_{𝒪_{X,x}}(F_x, ω)` for every `i`, which is the
  stalk of `𝓔xt^{-i}(F, K)` computed in the local ring ([Stacks, Tag 0A6H]). -/
def IsStalkwiseDualExt (F : X.Modules) (K : DerivedCategory X.Modules) (δ : X → ℤ)
    (E : ℤ → X.Modules) : Prop :=
  IsDualizingComplex K ∧
    ∀ x : X, ∃ ω : DerivedCategory (ModuleCat.{u} ↑(X.presheaf.stalk x)),
      Dualizing.IsNormalizedDualizingComplex ω ∧
        (∃ C : CochainComplex X.Modules ℤ, Nonempty (DerivedCategory.Q.obj C ≅ K) ∧
          Nonempty (ω ≅ (derivedStalkOfComplex x C)⟦-δ x⟧)) ∧
        ∀ i : ℤ, Nonempty ((E i).presheaf.stalk x ≃ₗ[↑(X.presheaf.stalk x)]
          Dualizing.moduleExtInto (F.presheaf.stalk x) ω (δ x - i))

/-- For coherent `F`, the stalk of `F` is finite and the stalk of `E (i + δ x)` is
`Ext^{-i}(F_x, ω)` for a normalized dualizing complex `ω`. -/
private theorem finite_and_exists_equiv_moduleExtInto (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] {K : DerivedCategory X.Modules} {δ : X → ℤ}
    {E : ℤ → X.Modules} (hE : IsStalkwiseDualExt F K δ E) (x : X) :
    Module.Finite ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x) ∧
      ∃ ω : DerivedCategory (ModuleCat.{u} ↑(X.presheaf.stalk x)),
        Dualizing.IsNormalizedDualizingComplex ω ∧ ∀ i : ℤ,
          Nonempty ((E (i + δ x)).presheaf.stalk x ≃ₗ[↑(X.presheaf.stalk x)]
            Dualizing.moduleExtInto (F.presheaf.stalk x) ω (-i)) := by
  refine ⟨AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent F x, ?_⟩
  obtain ⟨ω, hω, -, hiso⟩ := hE.2 x
  refine ⟨ω, hω, fun i => ?_⟩
  obtain ⟨e⟩ := hiso (i + δ x)
  rw [show δ x - (i + δ x) = -i by ring] at e
  exact ⟨e⟩

/-- **Stacks Project, Tag 0ECM, clause (1).** For a coherent module `F` on a locally Noetherian
scheme and a dualizing complex `K` with dimension function `δ`, a nonzero stalk of the Ext sheaf
`𝓔ⁱ` at `x` forces `δ(x) ≤ i ≤ δ(x) + dim Supp(F_x)`; in particular that dimension is finite. -/
@[stacks 0ECM
  "clause (1): E^i_x ≠ 0 → δ(x) ≤ i ≤ δ(x) + dim Supp(F_x), given IsStalkwiseDualExt"]
theorem extSheaf_stalk_degree_range (F : X.Modules) [_root_.SheafOfModules.IsCoherent F]
    (K : DerivedCategory X.Modules) (δ : X → ℤ) (E : ℤ → X.Modules)
    (hE : IsStalkwiseDualExt F K δ E) (x : X) (i : ℤ)
    (hi : Nontrivial ↑((E i).presheaf.stalk x)) :
    δ x ≤ i ∧ ∃ d : ℕ,
      Module.supportDim ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x) = (d : WithBot ℕ∞) ∧
        i ≤ δ x + d := by
  obtain ⟨hF, ω, hω, hiso⟩ := finite_and_exists_equiv_moduleExtInto F hE x
  obtain ⟨e⟩ := hiso (i - δ x)
  rw [sub_add_cancel] at e
  have hnt := e.toEquiv.nontrivial_congr.mp hi
  obtain ⟨d, hd, hlo, hhi⟩ := Dualizing.moduleExtInto_degree_range ω hω (i - δ x) hnt
  exact ⟨by omega, d, hd, by omega⟩

/-- **Stacks Project, Tag 0ECM, clause (2).** The stalk of `𝓔^{i + δ(x)}` at `x` has support of
dimension at most `i`; for `i < 0` the bound is `⊥`, which says that the stalk vanishes. -/
@[stacks 0ECM
  "clause (2): dim Supp(E^{i + δ(x)}_x) ≤ i, given IsStalkwiseDualExt"]
theorem supportDim_extSheaf_stalk_le (F : X.Modules) [_root_.SheafOfModules.IsCoherent F]
    (K : DerivedCategory X.Modules) (δ : X → ℤ) (E : ℤ → X.Modules)
    (hE : IsStalkwiseDualExt F K δ E) (x : X) (i : ℤ) :
    Module.supportDim ↑(X.presheaf.stalk x) ↑((E (i + δ x)).presheaf.stalk x) ≤
      if 0 ≤ i then ((i.toNat : ℕ∞) : WithBot ℕ∞) else ⊥ := by
  obtain ⟨hF, ω, hω, hiso⟩ := finite_and_exists_equiv_moduleExtInto F hE x
  obtain ⟨e⟩ := hiso i
  rw [Module.supportDim_eq_of_equiv e]
  exact Dualizing.supportDim_moduleExtInto_le (F.presheaf.stalk x) ω hω i

/-- **Stacks Project, Tag 0ECM, clause (3).** The depth of `F_x` is the least `i ≥ 0` for which
the stalk of `𝓔^{i + δ(x)}` at `x` is nonzero.  If all of these stalks vanish, both sides are
`⊤`. -/
@[stacks 0ECM
  "clause (3): depth(F_x) = least i ≥ 0 with E^{i + δ(x)}_x ≠ 0, given IsStalkwiseDualExt"]
theorem depth_stalk_eq_iInf_nontrivial_extSheaf_stalk (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (K : DerivedCategory X.Modules) (δ : X → ℤ)
    (E : ℤ → X.Modules) (hE : IsStalkwiseDualExt F K δ E) (x : X) :
    Module.depth ↑(X.presheaf.stalk x) (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
        ↑(F.presheaf.stalk x) =
      ⨅ (k : ℕ) (_ : Nontrivial ↑((E ((k : ℤ) + δ x)).presheaf.stalk x)), (k : ℕ∞) := by
  obtain ⟨hF, ω, hω, hiso⟩ := finite_and_exists_equiv_moduleExtInto F hE x
  have hpred : ∀ k : ℕ, Nontrivial ↑((E ((k : ℤ) + δ x)).presheaf.stalk x) ↔
      Nontrivial (Dualizing.moduleExtInto (F.presheaf.stalk x) ω (-(k : ℤ))) := fun k =>
    (hiso k).elim fun e => e.toEquiv.nontrivial_congr
  rw [Dualizing.depth_eq_iInf_nontrivial_moduleExtInto ω hω]
  refine le_antisymm (le_iInf fun k => le_iInf fun hk => ?_)
    (le_iInf fun k => le_iInf fun hk => ?_)
  · exact iInf_le_of_le k (iInf_le _ ((hpred k).mp hk))
  · exact iInf_le_of_le k (iInf_le _ ((hpred k).mpr hk))

/-- **Stacks Project, Tag 0ECM, clause (4).** A point `x` lies in the support of
`⨁_{j ≤ i} 𝓔^j` — that is, some `𝓔^j` with `j ≤ i` has nonzero stalk at `x` — exactly when the
depth of `F_x` is finite and `depth(F_x) + δ(x) ≤ i`. -/
@[stacks 0ECM
  "clause (4): x ∈ Supp(⊕_{j ≤ i} E^j) ↔ depth(F_x) + δ(x) ≤ i, given IsStalkwiseDualExt"]
theorem exists_nontrivial_extSheaf_stalk_iff_depth_add_le (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (K : DerivedCategory X.Modules) (δ : X → ℤ)
    (E : ℤ → X.Modules) (hE : IsStalkwiseDualExt F K δ E) (x : X) (i : ℤ) :
    (∃ j : ℤ, j ≤ i ∧ Nontrivial ↑((E j).presheaf.stalk x)) ↔
      ∃ n : ℕ, Module.depth ↑(X.presheaf.stalk x)
            (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x)) ↑(F.presheaf.stalk x) = (n : ℕ∞) ∧
          (n : ℤ) + δ x ≤ i := by
  have hdepth := depth_stalk_eq_iInf_nontrivial_extSheaf_stalk F K δ E hE x
  constructor
  · rintro ⟨j, hji, hj⟩
    obtain ⟨hδj, -⟩ := extSheaf_stalk_degree_range F K δ E hE x j hj
    have hkj : ((j - δ x).toNat : ℤ) + δ x = j := by omega
    have hk' : Nontrivial ↑((E (((j - δ x).toNat : ℤ) + δ x)).presheaf.stalk x) := by
      rwa [hkj]
    have hle : Module.depth ↑(X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x)) ↑(F.presheaf.stalk x) ≤
        (((j - δ x).toNat : ℕ) : ℕ∞) := by
      rw [hdepth]
      exact iInf_le_of_le (j - δ x).toNat (iInf_le _ hk')
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle)
    refine ⟨m, hm.symm, ?_⟩
    rw [← hm] at hle
    have hmk : m ≤ (j - δ x).toNat := by exact_mod_cast hle
    omega
  · rintro ⟨n, hn, hni⟩
    have hiInf : (⨅ (k : ℕ) (_ : Nontrivial ↑((E ((k : ℤ) + δ x)).presheaf.stalk x)),
        (k : ℕ∞)) = (n : ℕ∞) := by rw [← hdepth, hn]
    have hex : ∃ k : ℕ, Nontrivial ↑((E ((k : ℤ) + δ x)).presheaf.stalk x) ∧ k ≤ n := by
      by_contra! hgt
      have hle : ((n : ℕ∞) + 1) ≤
          ⨅ (k : ℕ) (_ : Nontrivial ↑((E ((k : ℤ) + δ x)).presheaf.stalk x)), (k : ℕ∞) :=
        le_iInf fun k => le_iInf fun hk => by exact_mod_cast Nat.succ_le_of_lt (hgt k hk)
      rw [hiInf] at hle
      have hcon : (n + 1 : ℕ) ≤ n := by exact_mod_cast hle
      omega
    obtain ⟨k, hk, hkn⟩ := hex
    exact ⟨(k : ℤ) + δ x, by omega, hk⟩

end Stacks.Duality

end
