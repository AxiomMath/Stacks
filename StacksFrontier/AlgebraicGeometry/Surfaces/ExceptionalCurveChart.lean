module

public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveGradedIndependence
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodMultiplicative
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningRestriction

/-!
# The thickenings of a divisor over an affine chart

Let `D` be an ideal sheaf on a scheme `X` and `V ⊆ X` an affine open. Over `V` the `n`-th
infinitesimal thickening `Eₙ = (D ^ (n + 1)).subscheme` is `Spec Γ(X, V) ⧸ D(V)ⁿ⁺¹`: the section
map `Γ(X, V) ⟶ Γ(Eₙ, Eₙ ∩ V)` is onto with kernel `D(V)ⁿ⁺¹`
(`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_surjective` and `ker_subschemeι_app`).
This file records how these presentations are compatible with restriction between closed
subschemes (`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_eq_of_le`), and proves the one
geometric input to the independence of monomials in [Stacks, Tag 0C2K]:

* `AlgebraicGeometry.Scheme.IdealSheafData.eq_zero_of_thickeningRestriction_eq_zero` — let `D`
  be an effective Cartier divisor whose subscheme `E` is integral, and `V` an affine open meeting
  `E`. A function on a thickening `Eₘ₊₁` which vanishes on `Eₘ` and over `V` is zero.

That is, a section of a power of the conormal sheaf of `E` vanishing on a nonempty open vanishes
(`AlgebraicGeometry.Scheme.IdealSheafData.eq_zero_of_thickeningChartRestrict_eq_zero`). It is
checked on a cover of `X` by affine opens `V'` on which `D` is cut out by a nonzerodivisor `t'`:
there the function is the class of `t'ᵐ⁺¹ g`, and its vanishing at a point of the nonempty open
`V ∩ V' ∩ E` makes `s g` divisible by `t'` for some `s` not divisible by `t'`
(`AlgebraicGeometry.Scheme.IdealSheafData.thickeningChartRestrict_eq_zero_of_germ_eq_zero`); since
`(t')` is prime, `E` being integral, `t'` divides `g`.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (V : X.affineOpens)

/-- The part of the `n`-th thickening lying over the open `V`. -/
public abbrev thickeningChart (n : ℕ) : (thickening D n).Opens :=
  (D ^ (n + 1)).subschemeι ⁻¹ᵁ V.1

/-- Restriction of a global function on the `n`-th thickening to the part over `V`. -/
public def thickeningChartRestrict (n : ℕ) :
    Γ(thickening D n, ⊤) →+* Γ(thickening D n, thickeningChart D V n) :=
  ((thickening D n).presheaf.map (homOfLE le_top).op).hom

/-- The presentation of the part of the `n`-th thickening over `V`: the section map of the closed
immersion, onto with kernel `D(V)ⁿ⁺¹`. -/
public def thickeningChartSection (n : ℕ) :
    Γ(X, V.1) →+* Γ(thickening D n, thickeningChart D V n) :=
  ((D ^ (n + 1)).subschemeι.app V.1).hom

public theorem thickeningChartSection_surjective (n : ℕ) :
    Function.Surjective (thickeningChartSection D V n) :=
  (D ^ (n + 1)).subschemeι_app_surjective V

public theorem ker_thickeningChartSection (n : ℕ) :
    RingHom.ker (thickeningChartSection D V n) = D.ideal V ^ (n + 1) :=
  (D ^ (n + 1)).ker_subschemeι_app V

public theorem thickeningChartSection_eq_zero_iff (n : ℕ) (b : Γ(X, V.1)) :
    thickeningChartSection D V n b = 0 ↔ b ∈ D.ideal V ^ (n + 1) := by
  rw [← RingHom.mem_ker, ker_thickeningChartSection]

/-- **Presentations over an affine open are compatible with restriction between closed
subschemes.** For ideal sheaves `I ≤ J` and an affine open `V`, if `b ∈ Γ(X, V)` presents a function
`z` on `V(I)` over `V`, it presents the restriction of `z` to `V(J)` over `V`. -/
public theorem subschemeι_app_eq_of_le {I J : X.IdealSheafData} (h : I ≤ J)
    (z : Γ(I.subscheme, ⊤)) (b : Γ(X, V.1))
    (hb : (I.subschemeι.app V.1).hom b = (I.subscheme.presheaf.map (homOfLE le_top).op).hom z) :
    (J.subschemeι.app V.1).hom b =
      (J.subscheme.presheaf.map (homOfLE le_top).op).hom ((inclusion h).appTop.hom z) := by
  set ι := inclusion h
  have hle : J.subschemeι ⁻¹ᵁ V.1 ≤ ι ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ V.1) := by
    rw [← Scheme.Hom.comp_preimage, inclusion_subschemeι]
  have hQ : ∀ (f : J.subscheme ⟶ X) (hf : f = J.subschemeι)
      (e : J.subschemeι ⁻¹ᵁ V.1 ≤ f ⁻¹ᵁ V.1),
      f.appLE V.1 (J.subschemeι ⁻¹ᵁ V.1) e = J.subschemeι.app V.1 := by
    rintro f rfl e
    exact Scheme.Hom.appLE_eq_app _
  have h1 : (J.subschemeι.app V.1).hom b =
      (ι.appLE (I.subschemeι ⁻¹ᵁ V.1) (J.subschemeι ⁻¹ᵁ V.1) hle).hom
        ((I.subschemeι.app V.1).hom b) := by
    rw [← hQ (ι ≫ I.subschemeι) (inclusion_subschemeι _) (by rw [inclusion_subschemeι]),
      Scheme.Hom.comp_appLE]
    rfl
  have h2 : (J.subscheme.presheaf.map (homOfLE le_top).op).hom ((inclusion h).appTop.hom z) =
      (ι.appLE (I.subschemeι ⁻¹ᵁ V.1) (J.subschemeι ⁻¹ᵁ V.1) hle).hom
        ((I.subscheme.presheaf.map (homOfLE le_top).op).hom z) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  rw [h1, h2, hb]

/-- **The presentations over `V` are compatible with restriction between thickenings.** If `b`
presents a function `z` on the `j`-th thickening over `V`, it presents the restriction of `z` to
the `i`-th thickening over `V`. -/
public theorem thickeningChartSection_eq_of_le {i j : ℕ} (h : i ≤ j)
    (z : Γ(thickening D j, ⊤)) (b : Γ(X, V.1))
    (hb : thickeningChartSection D V j b = thickeningChartRestrict D V j z) :
    thickeningChartSection D V i b =
      thickeningChartRestrict D V i (thickeningRestrictionLE D h z) :=
  subschemeι_app_eq_of_le V (pow_succ_le_pow_succ D h) z b hb

/-- A function on a thickening vanishing on the part over `V` has zero germ at every point over
`V`. -/
public theorem germ_eq_zero_of_thickeningChartRestrict_eq_zero {n : ℕ}
    {z : Γ(thickening D n, ⊤)} (hz : thickeningChartRestrict D V n z = 0)
    (x : thickening D n) (hx : x ∈ thickeningChart D V n) :
    (thickening D n).presheaf.germ ⊤ x trivial z = 0 := by
  rw [← (thickening D n).presheaf.germ_res_apply (homOfLE le_top) x hx z]
  exact (congrArg _ hz).trans (map_zero _)

/-- **The key local step.** Let `t` be a nonzerodivisor generating `D(V)`, with `(t)` prime. If a
function on the `d`-th thickening is presented over `V` by an element of `D(V)ᵈ` and its germ at
some point over `V` vanishes, then it vanishes over `V`. -/
public theorem thickeningChartRestrict_eq_zero_of_germ_eq_zero {t : Γ(X, V.1)}
    (ht : t ∈ nonZeroDivisors Γ(X, V.1)) (hVt : D.ideal V = Ideal.span {t})
    (hprime : (D.ideal V).IsPrime) {d : ℕ} {z : Γ(thickening D d, ⊤)}
    (hz : ∀ b, thickeningChartSection D V d b = thickeningChartRestrict D V d z →
      b ∈ D.ideal V ^ d)
    (p : thickening D d) (hp : p ∈ thickeningChart D V d)
    (hgerm : (thickening D d).presheaf.germ ⊤ p trivial z = 0) :
    thickeningChartRestrict D V d z = 0 := by
  obtain ⟨b, hb⟩ := thickeningChartSection_surjective D V d (thickeningChartRestrict D V d z)
  have hbd := hz b hb
  have hU : IsAffineOpen (thickeningChart D V d) := V.2.preimage _
  let P := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
  let _ : Algebra Γ(thickening D d, thickeningChart D V d) ((thickening D d).presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk _ ⟨p, hp⟩
  have hloc : IsLocalization.AtPrime ((thickening D d).presheaf.stalk p) P :=
    hU.isLocalization_stalk ⟨p, hp⟩
  have hgerm' : algebraMap Γ(thickening D d, thickeningChart D V d)
      ((thickening D d).presheaf.stalk p) (thickeningChartRestrict D V d z) = 0 :=
    ((thickening D d).presheaf.germ_res_apply (homOfLE le_top) p hp z).trans hgerm
  obtain ⟨⟨m, hm⟩, hms⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ _).1 hgerm'
  obtain ⟨μ, rfl⟩ := thickeningChartSection_surjective D V d m
  have hμ : μ ∉ Ideal.span {t} := by
    intro hμt
    apply hm
    have hpow : μ ^ (d + 1) ∈ D.ideal V ^ (d + 1) := by
      rw [hVt]
      exact Ideal.pow_mem_pow hμt _
    rw [← thickeningChartSection_eq_zero_iff, map_pow] at hpow
    exact (hU.primeIdealOf ⟨p, hp⟩).isPrime.mem_of_pow_mem (d + 1)
      (by rw [hpow]; exact P.zero_mem)
  have hμb : μ * b ∈ D.ideal V ^ (d + 1) := by
    rwa [← thickeningChartSection_eq_zero_iff, map_mul, hb]
  rw [hVt] at hbd hμb hprime
  have hb0 := SemistableReduction.mem_span_singleton_pow_succ_of_mul_mem ht hprime hμ hbd hμb
  rwa [← hVt, ← thickeningChartSection_eq_zero_iff, hb] at hb0

variable {D}

/-- **A function on a thickening vanishing to the right order everywhere and over one chart
meeting the curve is zero.** Let `D` be an effective Cartier divisor whose subscheme is integral,
and `z` a function on the `d`-th thickening which over every affine open `V'` is presented by an
element of `D(V')ᵈ`. If `z` vanishes over an affine open `V` meeting the subscheme, then `z = 0`. -/
public theorem eq_zero_of_thickeningChartRestrict_eq_zero
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) [IsIntegral D.subscheme] {d : ℕ}
    {z : Γ(thickening D d, ⊤)}
    (hz : ∀ (V' : X.affineOpens) (b : Γ(X, V'.1)),
      thickeningChartSection D V' d b = thickeningChartRestrict D V' d z → b ∈ D.ideal V' ^ d)
    (hV : Nonempty (D.subschemeι ⁻¹ᵁ V.1)) (h0 : thickeningChartRestrict D V d z = 0) :
    z = 0 := by
  have hrange : ∀ y : X, y ∈ Set.range (D ^ (d + 1)).subschemeι ↔ y ∈ Set.range D.subschemeι := by
    intro y
    rw [range_subschemeι, range_subschemeι, support_pow_succ]
  have hη : ∀ W : D.subscheme.Opens, Nonempty W → genericPoint D.subscheme ∈ W := fun W hW =>
    ((genericPoint_spec D.subscheme).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  obtain ⟨p, hp⟩ := (hrange (D.subschemeι (genericPoint D.subscheme))).2 ⟨_, rfl⟩
  have hpmem : ∀ W : X.affineOpens, Nonempty (D.subschemeι ⁻¹ᵁ W.1) →
      p ∈ thickeningChart D W d := by
    intro W hW
    show (D ^ (d + 1)).subschemeι p ∈ W.1
    rw [hp]
    exact hη _ hW
  refine TopCat.Presheaf.section_ext (thickening D d).sheaf ⊤ z 0 fun x _ => ?_
  refine Eq.trans ?_ (map_zero _).symm
  obtain ⟨V', hxV', t, ht, hVt⟩ :=
    Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor D hD ((D ^ (d + 1)).subschemeι x)
  obtain ⟨q, hq⟩ := (hrange _).1 ⟨x, rfl⟩
  have hV' : Nonempty (D.subschemeι ⁻¹ᵁ V'.1) := ⟨⟨q, show D.subschemeι q ∈ V'.1 by rwa [hq]⟩⟩
  have hprime : (D.ideal V').IsPrime := by
    rw [← D.ker_subschemeι_app V']
    exact RingHom.ker_isPrime _
  exact germ_eq_zero_of_thickeningChartRestrict_eq_zero D V'
    (thickeningChartRestrict_eq_zero_of_germ_eq_zero D V' ht hVt hprime (hz V') p
      (hpmem V' hV') (germ_eq_zero_of_thickeningChartRestrict_eq_zero D V h0 p (hpmem V hV)))
    x hxV'

/-- **A function on the `(m + 2)`-nd thickening vanishing on the `(m + 1)`-st and over one chart
meeting the curve is zero**, for an effective Cartier divisor with integral subscheme. -/
public theorem eq_zero_of_thickeningRestriction_eq_zero
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) [IsIntegral D.subscheme] {m : ℕ}
    {z : Γ(thickening D (m + 1), ⊤)} (hres : thickeningRestriction D m z = 0)
    (hV : Nonempty (D.subschemeι ⁻¹ᵁ V.1)) (h0 : thickeningChartRestrict D V (m + 1) z = 0) :
    z = 0 := by
  refine eq_zero_of_thickeningChartRestrict_eq_zero V hD (fun V' b hb => ?_) hV h0
  have h := thickeningChartSection_eq_of_le D V' (Nat.le_succ m) z b hb
  rwa [thickeningRestrictionLE_succ, hres, map_zero, thickeningChartSection_eq_zero_iff] at h

end AlgebraicGeometry.Scheme.IdealSheafData
