module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffineChart
public import StacksFrontier.AlgebraicGeometry.Blowup.CentreNormalizeChart
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalChart
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreNormalCone
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FibrePrincipalDictionary
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullback
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Shrinking

/-!
# The strict transform `X'` as a component of the fibre at infinity

Let `X` be a scheme, `Z ⊆ X` the closed subscheme of a quasi-coherent ideal sheaf `ℐ`, and
`b : W ⟶ 𝐏¹_X` the blowup of `𝐏¹_X` in `∞(Z)`, with exceptional divisor `E`, fibre at infinity
`W_∞ = b⁻¹((𝐏¹_X)_∞)` and the closed immersion `X' ⟶ W` of the blowup `X'` of `X` in `Z`. Both
`E` and `W_∞` are effective Cartier divisors and `E ⊆ W_∞`, so `W_∞ = E + D` for an effective
Cartier divisor `D`. This file proves `D = X'`, which is assertions (2) and (4) of Stacks 0FBG:
`X'` is an effective Cartier divisor on `W` and `W_∞ = X' + E`. As a consequence the fibre at
infinity and the exceptional divisor agree away from `X'`: `W_∞ ∖ X' = E ∖ X'`.

The two inclusions are proved separately.

* `X' ⊆ D`. Restricted to `X'`, the divisor `W_∞` is all of `X'`, because `X' ⟶ W ⟶ 𝐏¹_X`
  factors through the infinity section; and `E` restricts to the exceptional divisor of
  `X' ⟶ X` (assertion (3)), an effective Cartier divisor. Cancelling it from
  `W_∞|_{X'} = E|_{X'} + D|_{X'}` leaves `D|_{X'} = X'`.
* `D ⊆ X'`. It suffices that `E` restricts to an effective Cartier divisor on `D`: then the
  morphism `D ⟶ W_∞ ⟶ X` lifts to the blowup `X'` of `X` in `Z` (Stacks 0806), and the lift
  followed by `X' ⟶ W` is the inclusion of `D`, both being morphisms to the blowup `W` over
  `𝐏¹_X` (Stacks 0806 again). That `E ∩ D` is Cartier on `D` is the one local computation. On the
  chart `Spec P[J/a]` of `W` over an affine open `Spec P ⊆ 𝐏¹_X` on which the divisor at infinity
  is cut out by `s`, with `J = I + (s)` the ideal of `∞(Z)` and `a ∈ J`, the divisor `D` is cut
  out by `s/a`, and the image of `a` is a nonzerodivisor modulo `s/a` as soon as `s` is a
  nonzerodivisor modulo every power of `I`.

That last condition is the transversality of the divisor at infinity to the infinitesimal
neighbourhoods of `π⁻¹(Z)`, `π : 𝐏¹_X ⟶ X`: the closed subscheme `π⁻¹(V(ℐⁿ))` is `𝐏¹_{V(ℐⁿ)}`,
and the divisor at infinity restricts to the divisor at infinity of `𝐏¹_{V(ℐⁿ)}`, which is an
effective Cartier divisor. So no coordinates on `𝐏¹_X` are used.

## Main results

* `Stacks.Chow.mem_span_of_algebraMap_mul_mem_span` — the ring-theoretic step: in the affine
  blowup algebra `P[J/a]` of `J = A + (s)`, with `s` a nonzerodivisor modulo every power of `A`,
  the image of `a` is a nonzerodivisor modulo `s/a`.
* `Stacks.Chow.isEffectiveCartierDivisor_comap_exceptionalIdeal_subschemeι` — for the blowup in
  `𝒦 + 𝒮` with `𝒮` an effective Cartier divisor transverse to the `V(𝒦ⁿ)`, the exceptional
  divisor restricts to an effective Cartier divisor on the residual divisor `D` of `b⁻¹𝒮 = E + D`.
* `Stacks.Chow.infinityCentreIdeal_eq_sup` — `ℐ_{∞(Z)} = π⁻¹ℐ + ℐ_{(𝐏¹_X)_∞}`.
* `Stacks.Chow.eq_strictTransformIdealAtInfinity_of_mul_eq` — any `D` with `W_∞ = E + D` is `X'`.
* `Stacks.Chow.fibreIdealAtInfinity_eq_mul_strictTransformIdealAtInfinity` — assertion (4),
  `W_∞ = X' + E`.
* `Stacks.Chow.isEffectiveCartierDivisor_strictTransformIdealAtInfinity` — assertion (2), `X'`
  is an effective Cartier divisor on `W`.
* `Stacks.Chow.comap_fibreIdealAtInfinity_ι_compl` and
  `Stacks.Chow.exceptionalComplIsoFibreCompl` — `W_∞ ∖ X' = E ∖ X'`, as closed subschemes of
  `W ∖ X'` and as schemes over `W`.

## Implementation notes

The charts are those of `Stacks.Blowup.blowUp`, the gluing of the `Proj` of the Rees algebras of
the sections of the centre, transported to the blowup `AlgebraicGeometry.blowUp` along
`AlgebraicGeometry.blowUpIso`, which is an isomorphism over the base. The source of Stacks 0FBG
proves `D = X'` on the two families of charts `D₊(S)` and `D₊(f)`, `f ∈ I`; here every chart
`D₊(a)`, `a ∈ J`, is treated at once, which avoids reducing the chart cover to those two
families.

The source assumes `ℐ` of finite type; none of the statements here needs it.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 02ON](https://stacks.math.columbia.edu/tag/02ON)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Algebra

variable {P : Type*} [CommRing P]

/-- `(A + L)ⁿ⁺¹ ≤ Aⁿ⁺¹ + L·(A + L)ⁿ` for ideals `A`, `L`. -/
theorem sup_pow_succ_le (A L : Ideal P) (n : ℕ) :
    (A ⊔ L) ^ (n + 1) ≤ A ^ (n + 1) ⊔ L * (A ⊔ L) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (A ⊔ L) ^ (n + 1 + 1) = (A ⊔ L) ^ (n + 1) * (A ⊔ L) := pow_succ _ _
      _ ≤ (A ^ (n + 1) ⊔ L * (A ⊔ L) ^ n) * (A ⊔ L) := Ideal.mul_mono_left ih
      _ ≤ A ^ (n + 1 + 1) ⊔ L * (A ⊔ L) ^ (n + 1) := by
        rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
        refine sup_le (sup_le ?_ ?_) ?_
        · rw [← pow_succ]
          exact le_sup_left
        · refine le_sup_of_le_right ?_
          rw [mul_comm]
          exact Ideal.mul_mono_right (Ideal.pow_right_mono le_sup_left _)
        · refine le_sup_of_le_right ?_
          rw [pow_succ, ← mul_assoc]
          exact sup_le (Ideal.mul_mono_right le_sup_left) (Ideal.mul_mono_right le_sup_right)

/-- In `P[1/a]`, the element `s/a` satisfies `a · (s/a) = s`. -/
private theorem algebraMap_mul_mk_away (a s : P) :
    algebraMap P (Localization.Away a) a * Localization.mk s ⟨a, Submonoid.mem_powers a⟩ =
      algebraMap P (Localization.Away a) s := by
  rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

/-- If `s` is a nonzerodivisor modulo every power of `A`, in the form `Aᵏ ∩ (s) ⊆ s·Aᵏ`, then
the same holds for the powers of `J = A + (s)`, with one power fewer:
`Jⁿ⁺¹ ∩ (s) ⊆ s·Jⁿ`. -/
theorem sup_span_pow_succ_inf_le (A : Ideal P) (s : P)
    (hA : ∀ k : ℕ, A ^ k ⊓ Ideal.span {s} ≤ Ideal.span {s} * A ^ k) (n : ℕ) :
    (A ⊔ Ideal.span {s}) ^ (n + 1) ⊓ Ideal.span {s} ≤
      Ideal.span {s} * (A ⊔ Ideal.span {s}) ^ n := by
  set L := Ideal.span {s}
  have hLM : L * (A ⊔ L) ^ n ≤ L := Submodule.mul_le.2 fun a ha b _ => Ideal.mul_mem_right b L ha
  calc (A ⊔ L) ^ (n + 1) ⊓ L ≤ (A ^ (n + 1) ⊔ L * (A ⊔ L) ^ n) ⊓ L :=
        inf_le_inf_right _ (sup_pow_succ_le A L n)
    _ = A ^ (n + 1) ⊓ L ⊔ L * (A ⊔ L) ^ n := by
        rw [inf_comm, inf_comm _ L, ← inf_sup_assoc_of_le _ hLM]
    _ ≤ L * (A ⊔ L) ^ n := by
        refine sup_le ((hA (n + 1)).trans (Ideal.mul_mono_right ?_)) le_rfl
        exact (Ideal.pow_le_pow_right (Nat.le_succ n)).trans (Ideal.pow_right_mono le_sup_left _)

/-- **The image of `a` is a nonzerodivisor modulo `s/a` on the chart `P[J/a]`**, for
`J = A + (s)` with `s` a nonzerodivisor modulo every power of `A`. Here `t ∈ P[J/a]` is any
element with `a·t = s`, that is, `t = s/a`. -/
theorem mem_span_of_algebraMap_mul_mem_span (J A : Ideal P) (s a : P)
    (hJ : J = A ⊔ Ideal.span {s})
    (hA : ∀ k : ℕ, A ^ k ⊓ Ideal.span {s} ≤ Ideal.span {s} * A ^ k)
    (ha : a ∈ J) (t : affineBlowup J a)
    (ht : algebraMap P _ a * t = algebraMap P _ s)
    (y : affineBlowup J a)
    (hy : algebraMap P _ a * y ∈ Ideal.span {t}) : y ∈ Ideal.span {t} := by
  subst hJ
  obtain ⟨n, x, hx, hyx⟩ := (affineBlowup_mem_iff (A ⊔ Ideal.span {s}) a ha y.1).1 y.2
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨m, x', hx', hzx⟩ := (affineBlowup_mem_iff (A ⊔ Ideal.span {s}) a ha z.1).1 z.2
  have ht' : (t : Localization.Away a) = Localization.mk s ⟨a, Submonoid.mem_powers a⟩ := by
    have h1 := congrArg Subtype.val ht
    change algebraMap P (Localization.Away a) a * (t : Localization.Away a) =
      algebraMap P (Localization.Away a) s at h1
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).mul_right_inj.1
      (h1.trans (algebraMap_mul_mk_away a s).symm)
  have hz' := congrArg Subtype.val hz
  change (z : Localization.Away a) * t = algebraMap P (Localization.Away a) a * y at hz'
  rw [hzx, hyx, ht', ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hz'
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := hz'
  simp only [Submonoid.coe_mul, one_mul] at hk
  have hkey : s * (a ^ (k + n) * x') = a ^ (k + m + 2) * x := by
    linear_combination hk
  have hmem : s * (a ^ (k + n) * x') ∈
      (A ⊔ Ideal.span {s}) ^ (k + m + n + 1 + 1) ⊓ Ideal.span {s} := by
    refine ⟨?_, Ideal.mem_span_singleton'.2 ⟨_, mul_comm _ _⟩⟩
    rw [hkey, show k + m + n + 1 + 1 = (k + m + 2) + n by ring, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow ha _) hx
  obtain ⟨j, hj, hsj⟩ := Ideal.mem_span_singleton_mul.1
    (sup_span_pow_succ_inf_le A s hA _ hmem)
  refine Ideal.mem_span_singleton'.2
    ⟨⟨Localization.mk j (⟨a ^ (k + m + n + 1), k + m + n + 1, rfl⟩ : Submonoid.powers a),
    mk_mem_affineBlowup_of_mem_pow (A ⊔ Ideal.span {s}) a hj⟩, Subtype.ext ?_⟩
  show Localization.mk j (⟨a ^ (k + m + n + 1), k + m + n + 1, rfl⟩ : Submonoid.powers a) *
    (t : Localization.Away a) = y
  rw [ht', hyx, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul]
  rw [mul_comm j s, hsj, hkey]
  ring

end Algebra

/-! ### Ideal sheaves -/

section IdealSheaf

/-- If an ideal sheaf `J` contains the kernel of a closed immersion `f`, then pushing its inverse
image forward along `f` returns `J`. -/
theorem map_comap_eq_of_ker_le {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (J : Y.IdealSheafData) (hJ : f.ker ≤ J) : (J.comap f).map f = J := by
  have hle : f.ker ≤ J.subschemeι.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
  have hl := IsClosedImmersion.lift_fac f J.subschemeι hle
  have hpb : IsPullback (IsClosedImmersion.lift f J.subschemeι hle) (𝟙 _) f J.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by rw [hl, Category.id_comp]⟩
  rw [← Scheme.IdealSheafData.ker_subschemeι J, ← ker_eq_comap_ker_of_isPullback hpb,
    Scheme.IdealSheafData.map_ker, hl]

/-- The inverse image of an ideal sheaf along `Spec Γ(P, U)[...] ⟶ Spec Γ(P, U) ≅ U`, read on
global sections: for a ring map `g : Γ(P, U) ⟶ R` it is the ideal generated by the image of the
ideal on `U`. -/
theorem ideal_comap_SpecMap_fromSpec_top {P : Scheme.{u}} (𝒜 : P.IdealSheafData)
    (U : P.affineOpens) {R : CommRingCat.{u}} (g : Γ(P, U.1) ⟶ R) :
    (𝒜.comap (Spec.map g ≫ (Stacks.RelativeProj.isAffineOpen U).fromSpec)).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      ((𝒜.ideal U).map g.hom).map (Scheme.ΓSpecIso R).inv.hom := by
  rw [Scheme.IdealSheafData.comap_comp, Stacks.IdealSheaf.ideal_comap_top_of_isAffine,
    Stacks.Blowup.ideal_comap_fromSpec_top, Stacks.Blowup.map_appTop_map_ΓSpecIso_inv]

end IdealSheaf

/-! ### The exceptional divisor restricted to a residual divisor -/

section Residual

/-- If an ideal sheaf `E` is generated by `e` on an affine open `V`, then its restriction to a
closed subscheme `D` is generated by the image of `e` on the preimage of `V`. -/
private theorem ideal_comap_subschemeι_eq_span {Y : Scheme.{u}} (E D : Y.IdealSheafData)
    (V : Y.affineOpens) (e : Γ(Y, V.1)) (hE : E.ideal V = Ideal.span {e}) :
    (E.comap D.subschemeι).ideal ⟨_, V.2.preimage D.subschemeι⟩ =
      Ideal.span {D.subschemeι.app V.1 e} := by
  rw [Stacks.IdealSheaf.ideal_comap_appLE E D.subschemeι V ⟨_, V.2.preimage D.subschemeι⟩
    le_rfl, Scheme.Hom.appLE_eq_app, hE, Ideal.map_span, Set.image_singleton]

/-- A closed subscheme `D` and an ideal sheaf `E` on `Y`: if on an affine open `V` the ideal `E`
is generated by a section `e` which is a nonzerodivisor modulo `D(V)`, then `E` restricted to `D`
is generated on the preimage of `V` by a nonzerodivisor. -/
theorem exists_isRegular_comap_subschemeι {Y : Scheme.{u}} (E D : Y.IdealSheafData)
    (V : Y.affineOpens) (e : Γ(Y, V.1)) (hE : E.ideal V = Ideal.span {e})
    (hD : ∀ x, e * x ∈ D.ideal V → x ∈ D.ideal V) :
    ∃ f : Γ(D.subscheme, D.subschemeι ⁻¹ᵁ V.1), IsRegular f ∧
      (E.comap D.subschemeι).ideal ⟨_, V.2.preimage D.subschemeι⟩ = Ideal.span {f} := by
  refine ⟨D.subschemeι.app V.1 e, ?_, ?_⟩
  · have hker : RingHom.ker (D.subschemeι.app V.1).hom = D.ideal V := D.ker_subschemeι_app V
    have key : ∀ x', (D.subschemeι.app V.1).hom e * x' = 0 → x' = 0 := by
      intro x' hx'
      obtain ⟨x, rfl⟩ := D.subschemeι_app_surjective V x'
      rw [← map_mul] at hx'
      have h1 : e * x ∈ D.ideal V := hker ▸ hx'
      exact (hker ▸ hD x h1 : x ∈ RingHom.ker (D.subschemeι.app V.1).hom)
    refine (Commute.isRegular_iff (fun b => mul_comm _ b)).2 fun x₁ x₂ h => ?_
    exact sub_eq_zero.1 (key (x₁ - x₂) (by rw [mul_sub, sub_eq_zero]; exact h))
  · exact ideal_comap_subschemeι_eq_span E D V e hE

/-- A principal ideal transported along a ring isomorphism. -/
theorem mem_span_singleton_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (ρ : A ≃+* B)
    (x : A) (y : B) : ρ x ∈ Ideal.span {y} ↔ x ∈ Ideal.span {ρ.symm y} := by
  simp only [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨ρ.symm r, by rw [← map_mul, hr, RingEquiv.symm_apply_apply]⟩
  · rintro ⟨r, hr⟩
    exact ⟨ρ r, by rw [← hr, map_mul, RingEquiv.apply_symm_apply]⟩

/-- **A local criterion for `E` to restrict to a Cartier divisor on `D`.** Let `c : Spec T ⟶ Y`
be an open immersion on which `E` and `D` are generated by `e` and `t`, with `e` a nonzerodivisor
modulo `t`. Then around every point of `D` in the image of `c`, the restriction of `E` to `D` is
generated on an affine open by a nonzerodivisor. -/
theorem exists_affineOpen_comap_subschemeι_of_chart {Y : Scheme.{u}} (E D : Y.IdealSheafData)
    {T : CommRingCat.{u}} (c : Spec T ⟶ Y) [IsOpenImmersion c] (e t : Γ(Spec T, ⊤))
    (hE : (E.comap c).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {e})
    (hD : (D.comap c).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {t})
    (he : ∀ y, e * y ∈ Ideal.span {t} → y ∈ Ideal.span {t}) (q : D.subscheme)
    (hq : D.subschemeι q ∈ Set.range c) :
    ∃ (U : D.subscheme.Opens) (hU : IsAffineOpen U), q ∈ U ∧
      ∃ f : Γ(D.subscheme, U), IsRegular f ∧
        (E.comap D.subschemeι).ideal ⟨U, hU⟩ = Ideal.span {f} := by
  let V : Y.affineOpens := ⟨c ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion c⟩
  let ρ : Γ(Y, V.1) ≃+* Γ(Spec T, ⊤) := (c.appIso ⊤).commRingCatIsoToRingEquiv
  have hmem : ∀ (K : Y.IdealSheafData) (x : Γ(Y, V.1)),
      x ∈ K.ideal V ↔ ρ x ∈ (K.comap c).ideal ⟨⊤, isAffineOpen_top _⟩ := by
    intro K x
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Ideal.mem_comap]
    show _ ↔ ((c.appIso ⊤).hom ≫ (c.appIso ⊤).inv) x ∈ _
    rw [Iso.hom_inv_id]
    rfl
  have hEV : E.ideal V = Ideal.span {ρ.symm e} := by
    ext x
    rw [hmem, hE, mem_span_singleton_ringEquiv]
  have hDV : ∀ x, ρ.symm e * x ∈ D.ideal V → x ∈ D.ideal V := by
    intro x hx
    rw [hmem, hD] at hx ⊢
    rw [map_mul, RingEquiv.apply_symm_apply] at hx
    exact he _ hx
  obtain ⟨f, hf, hfE⟩ := exists_isRegular_comap_subschemeι E D V _ hEV hDV
  refine ⟨_, V.2.preimage D.subschemeι, ?_, f, hf, hfE⟩
  obtain ⟨y, hy⟩ := hq
  show D.subschemeι q ∈ c ''ᵁ ⊤
  rw [← hy]
  exact ⟨y, trivial, rfl⟩

variable {P : Scheme.{u}} (𝒥 𝒦 𝒮 : P.IdealSheafData)

/-- **The exceptional divisor restricted to the residual divisor of a transverse Cartier divisor
is Cartier.** Let `𝒮` be an effective Cartier divisor on `P` which is transverse to a closed
subscheme `V(𝒦)` in the sense that it restricts to an effective Cartier divisor on every
infinitesimal neighbourhood `V(𝒦ⁿ)`, and let `b : W ⟶ P` be the blowup in `𝒥 = 𝒦 + 𝒮`, with
exceptional divisor `E`. If the inverse image of `𝒮` decomposes as `b⁻¹𝒮 = E + D`, then `E ∩ D`
is an effective Cartier divisor on `D`. -/
theorem isEffectiveCartierDivisor_comap_exceptionalIdeal_subschemeι (hJ : 𝒥 = 𝒦 ⊔ 𝒮)
    (h𝒮 : Stacks.Divisors.IsEffectiveCartierDivisor 𝒮)
    (h𝒦 : ∀ n : ℕ, Stacks.Divisors.IsEffectiveCartierDivisor (𝒮.comap (𝒦 ^ n).subschemeι))
    (D : (blowUp 𝒥).IdealSheafData)
    (hD : 𝒮.comap (blowUpToBase 𝒥) = exceptionalIdeal 𝒥 * D) :
    Stacks.Divisors.IsEffectiveCartierDivisor ((exceptionalIdeal 𝒥).comap D.subschemeι) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun q => ?_
  obtain ⟨U₀, hU₀, hpU, s, -, hsU⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor 𝒮 h𝒮
      (blowUpToBase 𝒥 (D.subschemeι q))
  let U : P.affineOpens := ⟨U₀, hU₀⟩
  have hreg : ∀ k : ℕ, (𝒦.ideal U) ^ k ⊓ Ideal.span {s} ≤ Ideal.span {s} * (𝒦.ideal U) ^ k := by
    intro k x ⟨hxk, hxs⟩
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hxs
    refine Ideal.mem_span_singleton_mul.2 ⟨w, ?_, mul_comm _ _⟩
    let ι := (𝒦 ^ k).subschemeι
    let V : (𝒦 ^ k).subscheme.affineOpens := ⟨ι ⁻¹ᵁ U₀, hU₀.preimage ι⟩
    have hr := isRegular_of_isEffectiveCartierDivisor_of_ideal_eq_span (h𝒦 k) V
      (ideal_comap_subschemeι_eq_span 𝒮 (𝒦 ^ k) U s hsU)
    have hker : RingHom.ker (ι.app U₀).hom = (𝒦.ideal U) ^ k :=
      (𝒦 ^ k).ker_subschemeι_app U
    rw [← hker] at hxk ⊢
    have h1 : (ι.app U₀).hom (w * s) = 0 := hxk
    rw [map_mul] at h1
    exact hr.right (show (ι.app U₀).hom w * _ = 0 * _ by rw [h1, zero_mul])
  have hsJ : s ∈ 𝒥.ideal U := by
    rw [hJ]
    exact Ideal.mem_sup_right (hsU ▸ Ideal.mem_span_singleton_self s)
  have hJU : 𝒥.ideal U = 𝒦.ideal U ⊔ Ideal.span {s} := by
    rw [hJ, ← hsU]
    rfl
  have hw : (AlgebraicGeometry.blowUpIso 𝒥).hom (D.subschemeι q) ∈
      Stacks.Blowup.blowUpToBase 𝒥 ⁻¹ᵁ U₀ := by
    show Stacks.Blowup.blowUpToBase 𝒥 ((AlgebraicGeometry.blowUpIso 𝒥).hom _) ∈ U₀
    rw [← Scheme.Hom.comp_apply, AlgebraicGeometry.blowUpIso_hom_blowUpToBase]
    exact hpU
  rw [← Stacks.Blowup.iSup_opensRange_blowUpAffineChart 𝒥 U] at hw
  obtain ⟨⟨a, ha⟩, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.1 hw
  let T : CommRingCat.{u} := CommRingCat.of (affineBlowup (𝒥.ideal U) a)
  let c : Spec T ⟶ blowUp 𝒥 :=
    Stacks.Blowup.blowUpAffineChart 𝒥 U ha ≫ (AlgebraicGeometry.blowUpIso 𝒥).inv
  have hcy : c y = D.subschemeι q := by
    show (AlgebraicGeometry.blowUpIso 𝒥).inv (Stacks.Blowup.blowUpAffineChart 𝒥 U ha y) = _
    rw [hy, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  have hcb : c ≫ blowUpToBase 𝒥 = Spec.map (CommRingCat.ofHom (algebraMap Γ(P, U.1) T)) ≫
      (Stacks.RelativeProj.isAffineOpen U).fromSpec := by
    rw [Category.assoc, ← AlgebraicGeometry.blowUpIso_hom_blowUpToBase, Iso.inv_hom_id_assoc]
    exact Stacks.Blowup.blowUpAffineChart_blowUpToBase 𝒥 U ha
  let φ : T ≃+* Γ(Spec T, ⊤) := (Scheme.ΓSpecIso T).symm.commRingCatIsoToRingEquiv
  have hE : ((exceptionalIdeal 𝒥).comap c).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {φ (algebraMap _ T a)} := by
    rw [exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp, hcb,
      ideal_comap_SpecMap_fromSpec_top, CommRingCat.hom_ofHom,
      Stacks.Blowup.affineBlowup_idealMap_eq_span _ _ ha, Ideal.map_span, Set.image_singleton]
    rfl
  have hS : (𝒮.comap (c ≫ blowUpToBase 𝒥)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {φ (algebraMap _ T s)} := by
    rw [hcb, ideal_comap_SpecMap_fromSpec_top, CommRingCat.hom_ofHom]
    show ((𝒮.ideal U).map _).map _ = _
    rw [hsU, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    rfl
  let t : T := ⟨Localization.mk s ⟨a, Submonoid.mem_powers a⟩,
    Algebra.subset_adjoin ⟨s, hsJ, rfl⟩⟩
  have hat : algebraMap _ T a * t = algebraMap _ T s := by
    exact Subtype.coe_injective (algebraMap_mul_mk_away a s)
  have hareg : IsRegular (φ (algebraMap _ T a)) :=
    Stacks.Divisors.isRegular_ringEquiv φ (isRegular_iff_mem_nonZeroDivisors.2
      (Stacks.Blowup.algebraMap_affineBlowup_mem_nonZeroDivisors (𝒥.ideal U) a))
  have hDc : (D.comap c).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {φ t} := by
    have h1 := congrArg (fun K : (Spec T).IdealSheafData => K.ideal ⟨⊤, isAffineOpen_top _⟩)
      (show 𝒮.comap (c ≫ blowUpToBase 𝒥) = (exceptionalIdeal 𝒥).comap c * D.comap c by
        rw [Scheme.IdealSheafData.comap_comp, hD, Stacks.IdealSheaf.comap_mul])
    simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply] at h1
    rw [hS, hE, ← hat, map_mul, ← Ideal.span_singleton_mul_span_singleton] at h1
    exact (Ideal.eq_of_span_singleton_mul_eq_span_singleton_mul
      (isRegular_iff_mem_nonZeroDivisors.1 hareg) h1).symm
  refine exists_affineOpen_comap_subschemeι_of_chart _ D c _ _ hE hDc ?_ q ⟨y, hcy⟩
  intro z hz
  rw [← φ.apply_symm_apply z, ← map_mul, mem_span_singleton_ringEquiv, φ.symm_apply_apply] at hz
  rw [← φ.apply_symm_apply z, mem_span_singleton_ringEquiv, φ.symm_apply_apply]
  exact mem_span_of_algebraMap_mul_mem_span _ (𝒦.ideal U) s a hJU hreg ha t hat _ hz

end Residual

/-! ### The blowup at infinity -/

section AtInfinity

variable {X : Scheme.{u}} (ℐ : X.IdealSheafData)

/-- The centre `∞(Z)` is cut out by `ℐ·𝒪_{𝐏¹_X}` together with the equation of the divisor at
infinity: `ℐ_{∞(Z)} = π⁻¹ℐ + ℐ_{(𝐏¹_X)_∞}`, for `π : 𝐏¹_X ⟶ X`. -/
theorem infinityCentreIdeal_eq_sup :
    infinityCentreIdeal ℐ = ℐ.comap (relativeProjectiveLine X ↘ X) ⊔ lineInfinityDivisor X := by
  have h := map_comap_eq_of_ker_le (lineInfinitySection X)
    (ℐ.comap (relativeProjectiveLine X ↘ X) ⊔ lineInfinityDivisor X) le_sup_right
  rwa [Scheme.IdealSheafData.comap_sup, ← Scheme.IdealSheafData.comap_comp,
    lineInfinitySection_comp, Scheme.IdealSheafData.comap_id, lineInfinityDivisor,
    AlgebraicGeometry.ker_comap_self, sup_bot_eq] at h

/-- The divisor at infinity of `𝐏¹_X` restricts to an effective Cartier divisor on the closed
subscheme `π⁻¹(T) = 𝐏¹_T` of `𝐏¹_X`, for every closed subscheme `T ⊆ X`. -/
theorem isEffectiveCartierDivisor_comap_lineInfinityDivisor_subschemeι (K : X.IdealSheafData) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((lineInfinityDivisor X).comap (K.comap (relativeProjectiveLine X ↘ X)).subschemeι) := by
  let g := projectiveLineBaseChange K.subschemeι
  have hpb := isPullback_projectiveLineBaseChange K.subschemeι
  have hker : g.ker = K.comap (relativeProjectiveLine X ↘ X) := by
    rw [AlgebraicGeometry.ker_eq_comap_ker_of_isPullback hpb.flip,
      Scheme.IdealSheafData.ker_subschemeι]
  have hsq : IsPullback (lineInfinitySection K.subscheme) K.subschemeι g
      (lineInfinitySection X) := by
    refine IsPullback.of_right ?_
      (absoluteConstantSection_comp_projectiveLineBaseChange integralInfinitySection
        K.subschemeι) hpb
    rw [lineInfinitySection_comp, lineInfinitySection_comp]
    exact IsPullback.id_horiz _
  have hL : (lineInfinityDivisor X).comap g = lineInfinityDivisor K.subscheme :=
    (AlgebraicGeometry.ker_eq_comap_ker_of_isPullback hsq).symm
  have hk : (K.comap (relativeProjectiveLine X ↘ X)).subschemeι.ker = g.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hker]
  let e := IsClosedImmersion.lift (K.comap (relativeProjectiveLine X ↘ X)).subschemeι g hk.le
  have he : e ≫ (K.comap (relativeProjectiveLine X ↘ X)).subschemeι = g :=
    IsClosedImmersion.lift_fac _ _ _
  have : IsIso e := IsClosedImmersion.isIso_lift _ g hk
  have h1 : ((lineInfinityDivisor X).comap
      (K.comap (relativeProjectiveLine X ↘ X)).subschemeι).comap e =
        lineInfinityDivisor K.subscheme := by
    rw [← Scheme.IdealSheafData.comap_comp, he, hL]
  have hcomap : (lineInfinityDivisor X).comap
      (K.comap (relativeProjectiveLine X ↘ X)).subschemeι =
      (lineInfinityDivisor K.subscheme).comap (inv e) := by
    rw [← h1, ← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  rw [hcomap]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
    (lineInfinityDivisor_isEffectiveCartierDivisor _) _

/-- **The exceptional divisor restricted to `D` is Cartier**, for any decomposition
`W_∞ = E + D` of the fibre at infinity of the blowup at infinity. -/
theorem isEffectiveCartierDivisor_comap_exceptionalIdealAtInfinity_subschemeι
    (D : (blowupAtInfinity ℐ).IdealSheafData)
    (hD : fibreIdealAtInfinity ℐ = exceptionalIdealAtInfinity ℐ * D) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((exceptionalIdealAtInfinity ℐ).comap D.subschemeι) := by
  refine isEffectiveCartierDivisor_comap_exceptionalIdeal_subschemeι (infinityCentreIdeal ℐ)
    (ℐ.comap (relativeProjectiveLine X ↘ X)) (lineInfinityDivisor X)
    (infinityCentreIdeal_eq_sup ℐ) (lineInfinityDivisor_isEffectiveCartierDivisor X)
    (fun n => ?_) D hD
  rw [← Stacks.IdealSheaf.comap_pow]
  exact isEffectiveCartierDivisor_comap_lineInfinityDivisor_subschemeι (ℐ ^ n)

/-- `X'` lies in the residual divisor: if `W_∞ = E + D` with `D` an ideal sheaf on `W`, then
`X' ⊆ D`. -/
theorem le_ker_blowUpToBlowupAtInfinity (D : (blowupAtInfinity ℐ).IdealSheafData)
    (hD : fibreIdealAtInfinity ℐ = exceptionalIdealAtInfinity ℐ * D) :
    D ≤ (blowUpToBlowupAtInfinity ℐ).ker := by
  rw [AlgebraicGeometry.le_ker_iff_comap_eq_bot]
  have hbot : (fibreIdealAtInfinity ℐ).comap (blowUpToBlowupAtInfinity ℐ) = ⊥ := by
    rw [fibreIdealAtInfinity, ← Scheme.IdealSheafData.comap_comp, blowUpToBlowupAtInfinity_comp,
      Scheme.IdealSheafData.comap_comp, lineInfinityDivisor, AlgebraicGeometry.ker_comap_self,
      Scheme.IdealSheafData.comap_bot]
  rw [hD, Stacks.IdealSheaf.comap_mul, comap_exceptionalIdealAtInfinity] at hbot
  refine Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal ℐ) ?_
  rw [hbot, Scheme.IdealSheafData.mul_bot]

/-- The residual divisor lies in `X'`: if `W_∞ = E + D`, then `D ⊆ X'`. -/
theorem ker_blowUpToBlowupAtInfinity_le (D : (blowupAtInfinity ℐ).IdealSheafData)
    (hD : fibreIdealAtInfinity ℐ = exceptionalIdealAtInfinity ℐ * D) :
    (blowUpToBlowupAtInfinity ℐ).ker ≤ D := by
  let ιD := D.subschemeι
  let b₀ := blowupAtInfinityToLine ℐ
  have hfib : fibreIdealAtInfinity ℐ ≤ D := by
    rw [hD, Scheme.IdealSheafData.le_def]
    intro U
    exact Submodule.mul_le.2 fun a _ b hb => Ideal.mul_mem_left _ a hb
  have hle : (lineInfinitySection X).ker ≤ (ιD ≫ b₀).ker := by
    rw [AlgebraicGeometry.le_ker_iff_comap_eq_bot, Scheme.IdealSheafData.comap_comp]
    show (fibreIdealAtInfinity ℐ).comap ιD = ⊥
    rw [← AlgebraicGeometry.le_ker_iff_comap_eq_bot, Scheme.IdealSheafData.ker_subschemeι]
    exact hfib
  let q := IsClosedImmersion.lift (lineInfinitySection X) (ιD ≫ b₀) hle
  have hq : q ≫ lineInfinitySection X = ιD ≫ b₀ := IsClosedImmersion.lift_fac _ _ _
  have hqp : q = ιD ≫ blowupAtInfinityToBase ℐ := by
    rw [blowupAtInfinityToBase, ← Category.assoc, ← hq, Category.assoc, lineInfinitySection_comp,
      Category.comp_id]
  have hcart := isEffectiveCartierDivisor_comap_exceptionalIdealAtInfinity_subschemeι ℐ D hD
  have hg : Stacks.Blowup.IsCartierOver (infinityCentreIdeal ℐ) (Over.mk (ιD ≫ b₀)) := by
    show Stacks.Divisors.IsEffectiveCartierDivisor ((infinityCentreIdeal ℐ).comap (ιD ≫ b₀))
    rwa [Scheme.IdealSheafData.comap_comp]
  have hp : Stacks.Blowup.IsCartierOver ℐ (Over.mk q) := by
    show Stacks.Divisors.IsEffectiveCartierDivisor (ℐ.comap q)
    have e1 : ℐ.comap q = (infinityCentreIdeal ℐ).comap (ιD ≫ b₀) := by
      rw [← hq, Scheme.IdealSheafData.comap_comp, comap_infinityCentreIdeal_lineInfinitySection]
    rwa [e1]
  let l := blowUpLift ℐ q hp
  have hl : l ≫ blowUpToBlowupAtInfinity ℐ ≫ b₀ = ιD ≫ b₀ := by
    show l ≫ blowUpToBlowupAtInfinity ℐ ≫ blowupAtInfinityToLine ℐ = _
    rw [blowUpToBlowupAtInfinity_comp, ← Category.assoc, blowUpLift_comp, hq]
  have h1 := blowUpLift_unique (infinityCentreIdeal ℐ) (ιD ≫ b₀) hg
    (l ≫ blowUpToBlowupAtInfinity ℐ) ((Category.assoc _ _ _).trans hl)
  have h2 := blowUpLift_unique (infinityCentreIdeal ℐ) (ιD ≫ b₀) hg ιD rfl
  have h3 : l ≫ blowUpToBlowupAtInfinity ℐ = ιD := h1.trans h2.symm
  calc (blowUpToBlowupAtInfinity ℐ).ker ≤ (l ≫ blowUpToBlowupAtInfinity ℐ).ker :=
        Scheme.Hom.le_ker_comp _ _
    _ = D := by rw [h3, Scheme.IdealSheafData.ker_subschemeι]

/-- **The residual divisor is `X'`.** If `W_∞ = E + D` for an ideal sheaf `D` on `W`, then `D` is
the ideal sheaf of the closed subscheme `X' ⊆ W`. -/
theorem eq_strictTransformIdealAtInfinity_of_mul_eq (D : (blowupAtInfinity ℐ).IdealSheafData)
    (hD : fibreIdealAtInfinity ℐ = exceptionalIdealAtInfinity ℐ * D) :
    D = strictTransformIdealAtInfinity ℐ :=
  le_antisymm (le_ker_blowUpToBlowupAtInfinity ℐ D hD) (ker_blowUpToBlowupAtInfinity_le ℐ D hD)

/-- `W_∞ = X' + E` as effective Cartier divisors on `W`, in the
ideal-sheaf presentation `ℐ_{W_∞} = ℐ_E · ℐ_{X'}`. -/
@[stacks 0FBG "(4): W_∞ = X' + E as effective Cartier divisors on W"]
theorem fibreIdealAtInfinity_eq_mul_strictTransformIdealAtInfinity :
    fibreIdealAtInfinity ℐ =
      exceptionalIdealAtInfinity ℐ * strictTransformIdealAtInfinity ℐ := by
  obtain ⟨D, -, hD⟩ := exists_isEffectiveCartierDivisor_fibreIdealAtInfinity_eq ℐ
  rwa [← eq_strictTransformIdealAtInfinity_of_mul_eq ℐ D hD]

/-- The strict transform `X'` is an effective Cartier divisor on `W`. -/
@[stacks 0FBG "(2): X' is an effective Cartier divisor on W"]
theorem isEffectiveCartierDivisor_strictTransformIdealAtInfinity :
    Stacks.Divisors.IsEffectiveCartierDivisor (strictTransformIdealAtInfinity ℐ) := by
  obtain ⟨D, hDc, hD⟩ := exists_isEffectiveCartierDivisor_fibreIdealAtInfinity_eq ℐ
  rwa [← eq_strictTransformIdealAtInfinity_of_mul_eq ℐ D hD]

/-! ### The open `W_∞ ∖ X'` -/

/-- The open complement `W ∖ X'` of the strict transform in the blowup at infinity. -/
abbrev strictTransformComplAtInfinity : (blowupAtInfinity ℐ).Opens :=
  (strictTransformIdealAtInfinity ℐ).support.compl

/-- Away from `X'` the strict transform's ideal sheaf is the unit ideal. -/
theorem comap_strictTransformIdealAtInfinity_ι_compl :
    (strictTransformIdealAtInfinity ℐ).comap
        (strictTransformComplAtInfinity ℐ).ι = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  apply SetLike.coe_injective
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
  exact Set.eq_empty_iff_forall_notMem.2 fun x hx => x.2 hx

/-- **`W_∞ ∖ X' = E ∖ X'`.** On the open complement of `X'` in `W` the fibre at infinity and the
exceptional divisor are the same closed subscheme. -/
theorem comap_fibreIdealAtInfinity_ι_compl :
    (fibreIdealAtInfinity ℐ).comap (strictTransformComplAtInfinity ℐ).ι =
      (exceptionalIdealAtInfinity ℐ).comap
        (strictTransformComplAtInfinity ℐ).ι := by
  rw [fibreIdealAtInfinity_eq_mul_strictTransformIdealAtInfinity, Stacks.IdealSheaf.comap_mul,
    comap_strictTransformIdealAtInfinity_ι_compl, Scheme.IdealSheafData.mul_top]

/-- The morphism `E ∖ X' ⟶ W_∞ ∖ X'` induced by the inclusion `E ⊆ W_∞`. -/
def exceptionalComplToFibreCompl :
    ((exceptionalIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ
        strictTransformComplAtInfinity ℐ).toScheme ⟶
      ((fibreIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ
        strictTransformComplAtInfinity ℐ).toScheme :=
  (Scheme.IdealSheafData.inclusion (fibreIdealAtInfinity_le_exceptionalIdealAtInfinity ℐ)).resLE
    _ _ (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])

/-- The morphism `E ∖ X' ⟶ W_∞ ∖ X'` commutes with the immersions of `E ∖ X'` and
`W_∞ ∖ X'` into `W`. -/
@[reassoc]
theorem exceptionalComplToFibreCompl_ι_subschemeι :
    exceptionalComplToFibreCompl ℐ ≫
        ((fibreIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ
          strictTransformComplAtInfinity ℐ).ι ≫
        (fibreIdealAtInfinity ℐ).subschemeι =
      ((exceptionalIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ
          strictTransformComplAtInfinity ℐ).ι ≫
        (exceptionalIdealAtInfinity ℐ).subschemeι := by
  rw [exceptionalComplToFibreCompl, Scheme.Hom.resLE_comp_ι_assoc,
    Scheme.IdealSheafData.inclusion_subschemeι]

/-- The morphism `E ∖ X' ⟶ W_∞ ∖ X'` is an isomorphism. -/
instance isIso_exceptionalComplToFibreCompl : IsIso (exceptionalComplToFibreCompl ℐ) := by
  let U : (blowupAtInfinity ℐ).Opens := strictTransformComplAtInfinity ℐ
  have hker : ∀ K : (blowupAtInfinity ℐ).IdealSheafData, (K.subschemeι ∣_ U).ker = K.comap U.ι :=
    fun K => by
      rw [AlgebraicGeometry.ker_eq_comap_ker_of_isPullback (isPullback_morphismRestrict _ _),
        Scheme.IdealSheafData.ker_subschemeι]
  refine IsClosedImmersion.isIso_of_ker_eq ((exceptionalIdealAtInfinity ℐ).subschemeι ∣_ U)
    ((fibreIdealAtInfinity ℐ).subschemeι ∣_ U) _ ?_ ?_
  · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, morphismRestrict_ι]
    exact exceptionalComplToFibreCompl_ι_subschemeι ℐ
  · rw [hker, hker, comap_fibreIdealAtInfinity_ι_compl]

/-- **`E ∖ X' ≅ W_∞ ∖ X'`**, as open subschemes of the exceptional divisor and of the fibre at
infinity. -/
def exceptionalComplIsoFibreCompl :
    ((exceptionalIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ
        strictTransformComplAtInfinity ℐ).toScheme ≅
      ((fibreIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ
        strictTransformComplAtInfinity ℐ).toScheme :=
  asIso (exceptionalComplToFibreCompl ℐ)

end AtInfinity

end Stacks.Chow

end
