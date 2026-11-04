module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Sum

/-!
# The sum of two effective Cartier divisors as a scheme-theoretic union

Let `X` be a scheme and `D, D' ⊆ X` effective Cartier divisors whose scheme-theoretic
intersection `D ∩ D'` is an effective Cartier divisor *on `D'`*.  Then the sum `D + D'` is the
scheme-theoretic union of `D` and `D'`.

In the ideal-sheaf presentation the sum is the product `ℐ_D · ℐ_{D'}`, the scheme-theoretic union
is the intersection `ℐ_D ⊓ ℐ_{D'}`, and the intersection `D ∩ D'` as a closed subscheme of `D'`
is `ℐ_D.comap ℐ_{D'}.subschemeι`; so the statement is `D * D' = D ⊓ D'`.

## Main results

* `Ideal.span_singleton_inf_span_singleton_of_isSMulRegular_quotient`: the ring-theoretic step,
  `(f) ⊓ (g) = (f * g)` when `f` is a nonzerodivisor modulo `g`.
* `AlgebraicGeometry.isRegular_of_span_singleton_eq`: a generator of a principal ideal with a
  nonzerodivisor generator is itself a nonzerodivisor.
* `AlgebraicGeometry.mul_eq_inf_of_comap_isEffectiveCartierDivisor`: **Stacks Tag 0C4R.**

## The argument

Equality of ideal sheaves is checked on a cover (`Scheme.IdealSheafData.ext_of_iSup_eq_top`), so
it is enough to produce, around every point `x`, an affine open on which the two ideals agree.

Off the support of either divisor that divisor's ideal is the unit ideal on a basic open
(`Stacks.Divisors.exists_basicOpen_ideal_eq_top`), and both sides collapse to the other ideal.
At a point of both supports, Tag 01WS
(`Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor`) gives
nonzerodivisor generators `f` of `ℐ_D` and `g` of `ℐ_{D'}` on affine opens around `x`, and a
nonzerodivisor generator `t` of `ℐ_D.comap ι` on an affine open of `D'` around a preimage `y` of
`x`.  Shrinking to a single affine open `U ⊆ X` whose preimage in `D'` sits inside the chart of
`t` — which is possible because `ι` is a closed immersion, so its map on sections is surjective
and a basic open of `D'` is the preimage of a basic open of `X` — the three statements read:
`ℐ_D(U) = (f)`, `ℐ_{D'}(U) = (g)`, and the image of `f` under `Γ(X, U) ↠ Γ(D', ι⁻¹U)` generates
the same ideal as the nonzerodivisor `t`, hence is itself a nonzerodivisor.  Since the kernel of
that surjection is `(g)`, the ring-theoretic lemma gives `(f) ⊓ (g) = (f * g)`, which is the
claim on `U`.

## References

* [Stacks Project, Tag 0C4R](https://stacks.math.columbia.edu/tag/0C4R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

/-- **`(f) ⊓ (g) = (f * g)` when `f` is a nonzerodivisor modulo `g`.**  Here `q` is a ring map
with kernel `(g)` whose value at `f` is a nonzerodivisor of the target.  One inclusion is the
general `(f) * (g) ≤ (f) ⊓ (g)`; the other is
`smul_top_inf_eq_smul_of_isSMulRegular_on_quot`, whose hypothesis — that `f` acts regularly on
`A ⧸ (g)` — is exactly the regularity of `q f`. -/
theorem Ideal.span_singleton_inf_span_singleton_of_isSMulRegular_quotient {A : Type u}
    {B : Type*} [CommRing A] [CommRing B] (f g : A) (q : A →+* B)
    (hker : RingHom.ker q = Ideal.span {g}) (hfg : IsSMulRegular B (q f)) :
    Ideal.span {f} ⊓ Ideal.span {g} = Ideal.span {f * g} := by
  have hreg : IsSMulRegular (A ⧸ Ideal.span {g}) f :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).2 fun x hx => by
      rw [← hker] at hx ⊢
      exact RingHom.mem_ker.mpr (hfg.right_eq_zero_of_smul
        (by simpa [smul_eq_mul, map_mul] using RingHom.mem_ker.mp hx))
  refine le_antisymm ?_ ?_
  · simpa only [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top,
      Ideal.span_singleton_mul_span_singleton]
      using smul_top_inf_eq_smul_of_isSMulRegular_on_quot hreg
  · rw [← Ideal.span_singleton_mul_span_singleton]
    exact le_inf Ideal.mul_le_left Ideal.mul_le_right

namespace AlgebraicGeometry

/-- Two generators of the same principal ideal differ by a factor, so if one is a nonzerodivisor
so is the other. -/
theorem isRegular_of_span_singleton_eq {A : Type u} [CommRing A] {f g : A} (hg : IsRegular g)
    (hfg : Ideal.span {f} = Ideal.span {g}) : IsRegular f := by
  obtain ⟨c, hc⟩ :=
    Ideal.mem_span_singleton'.mp (hfg.symm ▸ Ideal.subset_span (Set.mem_singleton g))
  exact (hc ▸ hg).of_mul_right

variable {X : Scheme.{u}}

/-- Restricting a principal generator of `I.ideal W` to a smaller affine open `V` gives a
generator of `I.ideal V`. -/
private theorem ideal_eq_span_map_of_le {Y : Scheme.{u}} (I : Y.IdealSheafData)
    {V W : Y.affineOpens} (h : V ≤ W) {f : Γ(Y, (W : Y.Opens))}
    (hf : I.ideal W = Ideal.span {f}) :
    I.ideal V = Ideal.span {(Y.presheaf.map (homOfLE h).op).hom f} := by
  rw [← I.map_ideal h, hf, Ideal.map_span, Set.image_singleton]

/-- Away from the support of `J` the product and the intersection of two ideal sheaves agree,
on a basic open where `J` is the unit ideal. -/
private theorem exists_affineOpen_ideal_mul_eq_inf_of_notMem_support (I J : X.IdealSheafData)
    (x : X) (hx : x ∉ J.supportSet) :
    ∃ U : X.affineOpens, x ∈ (U : Set X) ∧ I.ideal U * J.ideal U = I.ideal U ⊓ J.ideal U := by
  obtain ⟨V, hxV⟩ := exists_affineOpens_mem x
  obtain ⟨g, hxg, htop⟩ := exists_basicOpen_ideal_eq_top J V x hxV hx
  exact ⟨X.affineBasicOpen (U := V) g, hxg, by rw [htop, Ideal.mul_top, inf_top_eq]⟩

/-- On an affine open around every point, the product of the ideal sheaves of two effective
Cartier divisors agrees with their intersection, provided the scheme-theoretic intersection is an
effective Cartier divisor on the second one. -/
private theorem exists_affineOpen_ideal_mul_eq_inf (D D' : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hD' : IsEffectiveCartierDivisor D')
    (hinter : IsEffectiveCartierDivisor (D.comap D'.subschemeι)) (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : Set X) ∧ (D * D').ideal U = (D ⊓ D').ideal U := by
  classical
  have hmul : ∀ U : X.affineOpens, (D * D').ideal U = D.ideal U * D'.ideal U := fun _ => rfl
  have hinf : ∀ U : X.affineOpens, (D ⊓ D').ideal U = D.ideal U ⊓ D'.ideal U := fun _ => rfl
  by_cases hxD : x ∈ D.supportSet
  · by_cases hxD' : x ∈ D'.supportSet
    · obtain ⟨UD, hUD, hxUD, f, hf, hDf⟩ :=
        exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D hD x
      obtain ⟨UD', hUD', hxUD', g, hg, hD'g⟩ :=
        exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D' hD' x
      -- shrink to one affine open `U₀` carrying both generators
      obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter hUD hUD' x ⟨hxUD, hxUD'⟩
      set U₀ : X.affineOpens := X.affineBasicOpen (U := ⟨UD, hUD⟩) a with hU₀
      have hU₀D : U₀ ≤ (⟨UD, hUD⟩ : X.affineOpens) := X.affineBasicOpen_le (V := ⟨UD, hUD⟩) a
      have hU₀D' : U₀ ≤ (⟨UD', hUD'⟩ : X.affineOpens) :=
        hab.trans_le (X.affineBasicOpen_le (V := ⟨UD', hUD'⟩) b)
      -- the chart of the intersection, on the closed subscheme `D'`
      obtain ⟨y, hy⟩ : x ∈ Set.range D'.subschemeι := by
        rw [D'.range_subschemeι]
        exact Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mp hxD'
      have hyE : y ∈ (D.comap D'.subschemeι).supportSet := by
        refine Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr ?_
        rw [Scheme.IdealSheafData.support_comap]
        change D'.subschemeι y ∈ D.support
        rw [hy]
        exact Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mp hxD
      obtain ⟨V, hV, hyV, t, ht, hEt⟩ :=
        exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
          (D.comap D'.subschemeι) hinter y
      -- a basic open of `D'` inside both charts, cut out by a section of `X`
      have hyV₀ : y ∈ D'.subschemeι ⁻¹ᵁ (U₀ : X.Opens) := by
        change D'.subschemeι y ∈ (U₀ : X.Opens)
        exact hy ▸ hxa
      obtain ⟨r, s, hrs, hyr⟩ := exists_basicOpen_le_affine_inter hV
        (U₀.2.preimage D'.subschemeι) y ⟨hyV, hyV₀⟩
      obtain ⟨q, hq⟩ := D'.subschemeι_app_surjective U₀ s
      set U : X.affineOpens := X.affineBasicOpen (U := U₀) q with hU
      have hUU₀ : U ≤ U₀ := X.affineBasicOpen_le (V := U₀) q
      have hpre : D'.subschemeι ⁻¹ᵁ (U : X.Opens) = D'.subscheme.basicOpen s := by
        change D'.subschemeι ⁻¹ᵁ X.basicOpen q = D'.subscheme.basicOpen s
        rw [Scheme.preimage_basicOpen, hq]
      set VY : D'.subscheme.affineOpens :=
        ⟨D'.subschemeι ⁻¹ᵁ (U : X.Opens), U.2.preimage D'.subschemeι⟩ with hVY
      have hVYV : VY ≤ (⟨V, hV⟩ : D'.subscheme.affineOpens) :=
        show (VY : D'.subscheme.Opens) ≤ V from
          le_of_eq_of_le (hpre.trans hrs.symm) (D'.subscheme.basicOpen_le r)
      have hxU : x ∈ (U : Set X) := by
        have hys : y ∈ D'.subschemeι ⁻¹ᵁ X.basicOpen q := by
          rw [Scheme.preimage_basicOpen, hq]
          exact hrs ▸ hyr
        exact hy ▸ hys
      -- the three generators, restricted to `U`
      have hDU := ideal_eq_span_map_of_le D (hUU₀.trans hU₀D) hDf
      have hD'U := ideal_eq_span_map_of_le D' (hUU₀.trans hU₀D') hD'g
      have hEU := ideal_eq_span_map_of_le (D.comap D'.subschemeι) hVYV hEt
      have hcomap : (D.comap D'.subschemeι).ideal VY = Ideal.span
          {(D'.subschemeι.appLE (U : X.Opens) (VY : D'.subscheme.Opens) le_rfl).hom
            ((X.presheaf.map (homOfLE (hUU₀.trans hU₀D)).op).hom f)} := by
        refine (Stacks.IdealSheaf.ideal_comap_appLE D D'.subschemeι U VY le_rfl).trans ?_
        rw [hDU]
        exact (Ideal.map_span _ _).trans (congrArg Ideal.span Set.image_singleton)
      have hreg : IsRegular
          ((D'.subschemeι.appLE (U : X.Opens) (VY : D'.subscheme.Opens) le_rfl).hom
            ((X.presheaf.map (homOfLE (hUU₀.trans hU₀D)).op).hom f)) :=
        isRegular_of_span_singleton_eq (isRegular_res_of_isAffineOpen hV ht hVYV)
          (hcomap.symm.trans hEU)
      have hker : RingHom.ker
          (D'.subschemeι.appLE (U : X.Opens) (VY : D'.subscheme.Opens) le_rfl).hom =
          Ideal.span {(X.presheaf.map (homOfLE (hUU₀.trans hU₀D')).op).hom g} := by
        rw [Scheme.Hom.appLE_eq_app]
        exact (D'.ker_subschemeι_app U).trans hD'U
      refine ⟨U, hxU, ?_⟩
      rw [hmul, hinf, hDU, hD'U]
      exact (Ideal.span_singleton_mul_span_singleton _ _).trans
        (Ideal.span_singleton_inf_span_singleton_of_isSMulRegular_quotient _ _ _ hker
          hreg.isSMulRegular).symm
    · obtain ⟨U, hxU, heq⟩ := exists_affineOpen_ideal_mul_eq_inf_of_notMem_support D D' x hxD'
      exact ⟨U, hxU, by rw [hmul, hinf, heq]⟩
  · obtain ⟨U, hxU, heq⟩ := exists_affineOpen_ideal_mul_eq_inf_of_notMem_support D' D x hxD
    exact ⟨U, hxU, by rw [hmul, hinf, mul_comm, heq, inf_comm]⟩

/-- **Stacks Project, Tag 0C4R.**  Let `D, D' ⊆ X` be effective Cartier divisors such that the
scheme-theoretic intersection `D ∩ D'` is an effective Cartier divisor on `D'`.  Then `D + D'`
is the scheme-theoretic union of `D` and `D'`. -/
@[stacks 0C4R]
theorem mul_eq_inf_of_comap_isEffectiveCartierDivisor (D D' : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hD' : IsEffectiveCartierDivisor D')
    (hinter : IsEffectiveCartierDivisor (D.comap D'.subschemeι)) :
    D * D' = D ⊓ D' := by
  classical
  choose U hxU heq using exists_affineOpen_ideal_mul_eq_inf D D' hD hD' hinter
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U (le_antisymm le_top fun x _ => ?_) heq
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩

end AlgebraicGeometry

end
