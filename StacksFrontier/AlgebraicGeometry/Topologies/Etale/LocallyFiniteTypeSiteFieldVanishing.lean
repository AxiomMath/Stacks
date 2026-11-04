module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleStalkDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteTypeTwiceDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparablyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.FiniteFieldCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteBound

/-!
# Vanishing above `d_V` on the small étale sites, over a finite or separably closed field

Let `S` be the spectrum of a field `k` which is finite or separably closed — the first two types
of base of Stacks 0DC6 — and let `V` be a quasi-compact scheme locally of finite type over `S`,
with the number `d_V = 1 + 2 dim(S) + sup_v (trdeg_k κ(v) + 2 dim 𝒪_{V,v})` of the example. For
every quasi-compact `W` locally of finite type over `S` with an étale morphism `W ⟶ V` over `S`,
and every abelian torsion sheaf `𝓖` on `W_ét`,

`H^p_ét(W, 𝓖) = 0` for `p > d_V`.

This is the cohomological content of condition (3) of Stacks 0DC4 in the example, on the small
étale sites of the members `V_i` of the coverings `{V_i ⟶ V}` of `Cov_V`.

## The proof

`cd(k) ≤ 1`: for `k` finite this is
`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_one_of_finite`, for `k` separably
closed `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed`. The
local rings of `W` have the dimensions of the local rings of `V` at the image points (an étale
morphism preserves them, Stacks 04N8), so `1 + 2 dim(W) ≤ d_V`, `dim S` being `0`. Hence
`2 dim(W) + cd(k) ≤ d_V`, and `AlgebraicGeometry.subsingleton_H_of_topologicalKrullDim_le`
(`cd(W) ≤ 2 dim(W) + cd(k)`) gives the vanishing.

## Main results

* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.subsingleton_H_of_etale_of_field`.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* [Stacks Project, Tag 0DC4](https://stacks.math.columbia.edu/tag/0DC4)
* [Stacks Project, Tag 04N8](https://stacks.math.columbia.edu/tag/04N8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- The spectrum of a field has dimension zero. -/
private lemma topologicalKrullDim_eq_zero_of_iso {S : Scheme.{u}} (k : Type u) [Field k]
    (e : S ≅ Spec (.of k)) : topologicalKrullDim S = 0 := by
  have hhomeo : IsHomeomorph e.hom.base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isHomeomorph
  rw [hhomeo.topologicalKrullDim_eq]
  show topologicalKrullDim (PrimeSpectrum k) = 0
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]

/-- Over a base of dimension zero, every local ring of `X` has dimension at most `(d - 1) / 2`,
where `d` is the bound `Hom.etaleCohomologyBound` of `f : X ⟶ S`. -/
private lemma _root_.AlgebraicGeometry.Scheme.Hom.ringKrullDim_stalk_le_of_etaleCohomologyBound_eq
    {X S : Scheme.{u}} (f : X ⟶ S) (hS : topologicalKrullDim S = 0) {d : ℕ}
    (hd : f.etaleCohomologyBound = d) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ ((d - 1) / 2 : ℕ) := by
  have hbound : (1 : WithBot ℕ∞) + 2 * ringKrullDim (X.presheaf.stalk x) ≤ d := by
    rw [← hd]
    show _ ≤ 1 + 2 * topologicalKrullDim S + _
    rw [hS, mul_zero, add_zero]
    refine add_le_add le_rfl
      ((le_add_of_nonneg_left ?_).trans (le_sup_of_le_right (le_iSup_of_le x le_rfl)))
    simp
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) :=
    ringKrullDim_nonneg_of_nontrivial
  have hrd : ringKrullDim (X.presheaf.stalk x) ≤ (d : WithBot ℕ∞) :=
    calc ringKrullDim (X.presheaf.stalk x)
        ≤ 2 * ringKrullDim (X.presheaf.stalk x) := by
          rw [two_mul]
          exact le_add_of_nonneg_left h0
      _ ≤ 1 + 2 * ringKrullDim (X.presheaf.stalk x) := le_add_of_nonneg_left zero_le_one
      _ ≤ d := hbound
  obtain ⟨r, hr⟩ : ∃ r : ℕ, ringKrullDim (X.presheaf.stalk x) = r := by
    induction hx : ringKrullDim (X.presheaf.stalk x) using WithBot.recBotCoe with
    | bot => rw [hx] at h0; exact absurd h0 (by simp)
    | coe a =>
      induction a using ENat.recTopCoe with
      | top =>
        rw [hx, ← WithBot.coe_natCast] at hrd
        exact absurd (top_le_iff.1 (WithBot.coe_le_coe.1 hrd)) (ENat.coe_ne_top d)
      | coe r => exact ⟨r, rfl⟩
  rw [hr] at hbound ⊢
  have : 1 + 2 * r ≤ d := by exact_mod_cast hbound
  exact_mod_cast (by omega : r ≤ (d - 1) / 2)

/-- **Vanishing above `d_V` over a finite or separably closed field** (Stacks 0DC6, base types
(1) and (2)). Let `S ≅ Spec k` with `k` a finite or a separably closed field, `V` a quasi-compact
scheme locally of finite type over `S`, and `W ⟶ V` a morphism over `S` from a quasi-compact
scheme `W` locally of finite type over `S` which is étale. Then `H^p_ét(W, 𝓖) = 0` for every
abelian torsion sheaf `𝓖` on `W_ét` and every `p > d_V`. -/
theorem subsingleton_H_of_etale_of_field {S : Scheme.{u}} (k : Type u) [Field k]
    (hk : Finite k ∨ IsSepClosed k) (e : S ≅ Spec (.of k)) (V : LocallyFiniteTypeEtale S)
    (hV : IsQuasiCompact V) (W : LocallyFiniteTypeEtale S) (hW : IsQuasiCompact W) (g : W ⟶ V)
    (hg : Etale ((forget S).map g))
    (G : Sheaf W.obj.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty W.obj.left.smallEtaleTopology G) (p : ℕ)
    (hp : V.obj.hom.etaleCohomologyBound < p) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} G p) := by
  have hS : IsUnboundedDescentEtaleBase S := by
    rcases hk with hk | hk
    · exact Or.inl ⟨k, inferInstance, hk, ⟨e⟩⟩
    · exact Or.inr (Or.inl ⟨k, inferInstance, hk, ⟨e⟩⟩)
  obtain ⟨d, hd⟩ := hS.exists_natCast_eq_etaleCohomologyBound V hV
  rw [hd] at hp
  have hdp : d < p := by exact_mod_cast hp
  have hcd : Scheme.etaleCohomologicalDimension (Spec (.of k)) ≤ 1 := by
    rcases hk with hk | hk
    · exact Scheme.etaleCohomologicalDimension_spec_le_one_of_finite k
    · exact (Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed k).trans zero_le_one
  have : LocallyOfFiniteType W.obj.hom := W.property
  have : CompactSpace W.obj.left := hW
  have hdimS := topologicalKrullDim_eq_zero_of_iso k e
  have hdimW : topologicalKrullDim W.obj.left ≤ ((d - 1) / 2 : ℕ) := by
    rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    exact iSup_le fun w ↦ (ringKrullDim_stalk_eq_of_etale ((forget S).map g) w).trans_le
      (V.obj.hom.ringKrullDim_stalk_le_of_etaleCohomologyBound_eq hdimS hd ((forget S).map g w))
  have hd1 : 1 ≤ d := by
    have h1 : (1 : WithBot ℕ∞) ≤ d := by
      rw [← hd]
      show _ ≤ 1 + 2 * topologicalKrullDim S + _
      rw [hdimS, mul_zero, add_zero]
      exact le_add_of_nonneg_right le_sup_left
    exact_mod_cast h1
  refine subsingleton_H_of_topologicalKrullDim_le k ((d - 1) / 2) W.obj.left (W.obj.hom ≫ e.hom)
    hdimW G hG p ?_
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) hcd)
  rw [← hc] at hcd ⊢
  have hc1 : c ≤ 1 := by exact_mod_cast hcd
  exact_mod_cast (by omega : 2 * ((d - 1) / 2) + c < p)

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
