module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCoordinateChangeTorsor
import Mathlib.Tactic.ComputeDegree

/-!
# The isomorphisms between two Weierstrass equations form a finite scheme

Let `W` be the scheme of Weierstrass equations with invertible discriminant and `H` the group
scheme of coordinate changes `γ = (u, r, s, t)`, acting on `W`. The morphism
`H × W ⟶ W × W, (γ, C) ↦ (γ • C, C)` is **finite**: its fibre over a pair of equations `(C', C)`
is the scheme of coordinate changes carrying `C` to `C'`, that is of isomorphisms between the
two plane cubics.

The proof is an integrality computation on the coordinate ring of `H × W`, which is generated
over the coordinates of `W × W` by `u`, `u⁻¹`, `r`, `s` and `t`. Writing `aᵢ`, `bᵢ`, `Δ` for the
invariants of `C` and `aᵢ'`, `bᵢ'`, `Δ'` for those of `C' = γ • C`:

* `u¹² = Δ / Δ'` and `u⁻¹² = Δ' / Δ`, since `Δ' = u⁻¹² Δ`;
* `r⁴ - b₄ r² - (2 b₆ + u⁶ b₆') r + (u⁸ b₈' - b₈) = 0`, the difference of the transformation
  rule of `b₈` and `r` times that of `b₆`;
* `s² + a₁ s + (u² a₂' - a₂ - 3 r) = 0`, the transformation rule of `a₂`;
* `t² + (a₃ + r a₁) t + (u⁶ a₆' - a₆ - r a₄ - r² a₂ - r³) = 0`, the transformation rule of `a₆`.

Each relation is monic in the variable it solves for, with coefficients integral by the previous
ones, so the coordinate ring is integral, and it is of finite type.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isFinite_prodLift_actionMap_productToBase`:
  the morphism `(γ, C) ↦ (γ • C, C)` from `H × W` to `W × W` is finite.
* `CommRingCat.eq_top_of_isPushout`: a subring of a pushout of commutative rings containing the
  images of both legs is everything.

## References

* [Stacks Project, Tag 072S](https://stacks.math.columbia.edu/tag/072S)
* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public section

open CategoryTheory Limits

universe u

/-- **The two legs of a pushout of commutative rings generate it**: a subring containing the
images of both legs is the whole ring. -/
theorem CommRingCat.eq_top_of_isPushout {R B C P : CommRingCat.{u}} {f : R ⟶ B} {g : R ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr) (J : Subring P)
    (hl : ∀ b, inl b ∈ J) (hr : ∀ c, inr c ∈ J) : J = ⊤ := by
  let jl : B ⟶ CommRingCat.of J := CommRingCat.ofHom (inl.hom.codRestrict J hl)
  let jr : C ⟶ CommRingCat.of J := CommRingCat.ofHom (inr.hom.codRestrict J hr)
  have w : f ≫ jl = g ≫ jr := by
    ext x
    show inl (f x) = inr (g x)
    exact congrArg (fun φ : R ⟶ P ↦ φ x) h.w
  let d := h.desc jl jr w
  have hd : d ≫ CommRingCat.ofHom J.subtype = 𝟙 P := by
    refine h.hom_ext ?_ ?_
    · rw [IsPushout.inl_desc_assoc, Category.comp_id]
      rfl
    · rw [IsPushout.inr_desc_assoc, Category.comp_id]
      rfl
  refine eq_top_iff.2 fun x _ ↦ ?_
  have : (d ≫ CommRingCat.ofHom J.subtype) x = x := by
    rw [hd]
    rfl
  rw [← this]
  exact (d x).2

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

/-- A root of a monic polynomial whose coefficients are integral is integral. -/
private theorem mem_integralClosure_of_monic {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} (p : Polynomial (integralClosure R A)) (hp : p.Monic)
    (hx : Polynomial.aeval x p = 0) : x ∈ integralClosure R A :=
  isIntegral_trans (A := integralClosure R A) x ⟨p, hp, hx⟩

/-- A root of a monic quadratic with integral coefficients is integral. -/
private theorem mem_integralClosure_of_quadratic {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x b c : A} (hb : b ∈ integralClosure R A) (hc : c ∈ integralClosure R A)
    (h : x ^ 2 + b * x + c = 0) : x ∈ integralClosure R A := by
  refine mem_integralClosure_of_monic
    (Polynomial.X ^ 2 + Polynomial.C ⟨b, hb⟩ * Polynomial.X + Polynomial.C ⟨c, hc⟩) ?_ ?_
  · monicity!
  · simpa using h

/-- A root of a monic quartic without cubic term, with integral coefficients, is integral. -/
private theorem mem_integralClosure_of_quartic {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x b c d : A} (hb : b ∈ integralClosure R A) (hc : c ∈ integralClosure R A)
    (hd : d ∈ integralClosure R A) (h : x ^ 4 + b * x ^ 2 + c * x + d = 0) :
    x ∈ integralClosure R A := by
  refine mem_integralClosure_of_monic
    (Polynomial.X ^ 4 + Polynomial.C ⟨b, hb⟩ * Polynomial.X ^ 2 + Polynomial.C ⟨c, hc⟩ *
      Polynomial.X + Polynomial.C ⟨d, hd⟩) ?_ ?_
  · monicity!
  · simpa using h

/-- **The coordinate changes between two Weierstrass equations satisfy monic equations.** If
`C' = γ • C` for a coordinate change `γ = (u, r, s, t)` over a ring `A`, `R` is a subring of `A`
(through an algebra structure) whose integral closure contains the coefficients of `C` and `C'`
and the inverses of their discriminants, then `u`, `u⁻¹`, `r`, `s` and `t` are integral over
`R`. -/
theorem mem_integralClosure_variableChange {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (γ : WeierstrassCurve.VariableChange A) (C : WeierstrassCurve A)
    (ha₁ : C.a₁ ∈ integralClosure R A) (ha₂ : C.a₂ ∈ integralClosure R A)
    (ha₃ : C.a₃ ∈ integralClosure R A) (ha₄ : C.a₄ ∈ integralClosure R A)
    (ha₆ : C.a₆ ∈ integralClosure R A) (ha₁' : (γ • C).a₁ ∈ integralClosure R A)
    (ha₂' : (γ • C).a₂ ∈ integralClosure R A) (ha₃' : (γ • C).a₃ ∈ integralClosure R A)
    (ha₄' : (γ • C).a₄ ∈ integralClosure R A) (ha₆' : (γ • C).a₆ ∈ integralClosure R A)
    (δ δ' : A) (hδ : C.Δ * δ = 1) (hδ' : (γ • C).Δ * δ' = 1)
    (hδm : δ ∈ integralClosure R A) (hδm' : δ' ∈ integralClosure R A) :
    (γ.u : A) ∈ integralClosure R A ∧ ((γ.u⁻¹ : Aˣ) : A) ∈ integralClosure R A ∧
      γ.r ∈ integralClosure R A ∧ γ.s ∈ integralClosure R A ∧ γ.t ∈ integralClosure R A := by
  set J := integralClosure R A
  have hb (W : WeierstrassCurve A) (h₁ : W.a₁ ∈ J) (h₂ : W.a₂ ∈ J) (h₃ : W.a₃ ∈ J)
      (h₄ : W.a₄ ∈ J) (h₆ : W.a₆ ∈ J) :
      W.b₂ ∈ J ∧ W.b₄ ∈ J ∧ W.b₆ ∈ J ∧ W.b₈ ∈ J ∧ W.Δ ∈ J := by
    let WJ : WeierstrassCurve J := ⟨⟨_, h₁⟩, ⟨_, h₂⟩, ⟨_, h₃⟩, ⟨_, h₄⟩, ⟨_, h₆⟩⟩
    have hW : WJ.map (algebraMap J A) = W := rfl
    rw [← hW, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
      WeierstrassCurve.map_b₈, WeierstrassCurve.map_Δ]
    exact ⟨WJ.b₂.2, WJ.b₄.2, WJ.b₆.2, WJ.b₈.2, WJ.Δ.2⟩
  obtain ⟨hb₂, hb₄, hb₆, hb₈, hΔ⟩ := hb C ha₁ ha₂ ha₃ ha₄ ha₆
  obtain ⟨-, -, hb₆', hb₈', hΔ'⟩ := hb (γ • C) ha₁' ha₂' ha₃' ha₄' ha₆'
  set u : A := (γ.u : A)
  set v : A := ((γ.u⁻¹ : Aˣ) : A)
  have huv : u * v = 1 := γ.u.mul_inv
  have hpow (n : ℕ) (x : A) {y : A} (hx : x = v ^ n * y) : u ^ n * x = y := by
    rw [hx, ← mul_assoc, ← mul_pow, huv, one_pow, one_mul]
  have hΔv : (γ • C).Δ = v ^ 12 * C.Δ := WeierstrassCurve.variableChange_Δ C γ
  have hΔeq := hpow 12 _ hΔv
  have h12 {x D e : A} (hD : D ∈ J) (he : e ∈ J) (h : x ^ 12 = D * e) : x ∈ J :=
    IsIntegral.of_pow (n := 12) (by norm_num) (h ▸ J.mul_mem hD he)
  have hu : u ∈ J := h12 hΔ hδm' (by rw [← hΔeq, mul_assoc, hδ', mul_one])
  have hv : v ∈ J := h12 hΔ' hδm (by rw [hΔv, mul_assoc, hδ, mul_one])
  have E6 := hpow 6 _ (WeierstrassCurve.variableChange_b₆ C γ)
  have E8 := hpow 8 _ (WeierstrassCurve.variableChange_b₈ C γ)
  have hr : γ.r ∈ J := by
    refine mem_integralClosure_of_quartic (J.neg_mem hb₄)
      (J.neg_mem (J.add_mem (J.mul_mem (ofNat_mem J 2) hb₆) (J.mul_mem (J.pow_mem hu 6) hb₆')))
      (J.sub_mem (J.mul_mem (J.pow_mem hu 8) hb₈') hb₈) ?_
    linear_combination E8 - γ.r * E6
  have hs : γ.s ∈ J := by
    refine mem_integralClosure_of_quadratic ha₁
      (J.sub_mem (J.sub_mem (J.mul_mem (J.pow_mem hu 2) ha₂') ha₂)
        (J.mul_mem (ofNat_mem J 3) hr)) ?_
    linear_combination hpow 2 _ (WeierstrassCurve.variableChange_a₂ C γ)
  have ht : γ.t ∈ J := by
    refine mem_integralClosure_of_quadratic (J.add_mem ha₃ (J.mul_mem hr ha₁))
      (J.sub_mem (J.sub_mem (J.sub_mem (J.sub_mem (J.mul_mem (J.pow_mem hu 6) ha₆') ha₆)
        (J.mul_mem hr ha₄)) (J.mul_mem (J.pow_mem hr 2) ha₂)) (J.pow_mem hr 3)) ?_
    linear_combination hpow 6 _ (WeierstrassCurve.variableChange_a₆ C γ)
  exact ⟨hu, hv, hr, hs, ht⟩

/-- Elements of a localization `R[1/x]` of a polynomial ring are polynomials times powers of the
inverse of `x`: a subring `J` of a ring `A` contains the image under `ψ : R[1/x] →+* A` of every
element as soon as it contains the images of the variables and of `1/x`. -/
private theorem coordinateChangeRing_map_mem {A : Type u} [CommRing A]
    (ψ : coordinateChangeRing.{u} →+* A) (J : Subring A)
    (hX : ∀ i, ψ (algebraMap (MvPolynomial (Fin 4) (ULift.{u} ℤ)) _ (MvPolynomial.X i)) ∈ J)
    (hinv : ψ (↑universalChange.{u}.u⁻¹) ∈ J) (h : coordinateChangeRing.{u}) : ψ h ∈ J := by
  have hpoly : ∀ p : MvPolynomial (Fin 4) (ULift.{u} ℤ), ψ (algebraMap _ _ p) ∈ J := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      have : (algebraMap (ULift.{u} ℤ) coordinateChangeRing.{u} a) = ((a.down : ℤ) : _) := by
        rw [show a = ((a.down : ℤ) : ULift.{u} ℤ) from ULift.ext _ _ (by simp), map_intCast]
        simp
      rw [this, map_intCast]
      exact intCast_mem J _
    | add p q hp hq =>
      rw [map_add, map_add]
      exact J.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, map_mul]
      exact J.mul_mem hp (hX i)
  obtain ⟨⟨p, d⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (MvPolynomial.X 0 :
      MvPolynomial (Fin 4) (ULift.{u} ℤ))) h
  obtain ⟨n, hn⟩ := d.2
  have hu : (algebraMap (MvPolynomial (Fin 4) (ULift.{u} ℤ)) coordinateChangeRing.{u}
      (MvPolynomial.X 0)) * ↑universalChange.{u}.u⁻¹ = 1 := universalChange.{u}.u.mul_inv
  have key : IsLocalization.mk' coordinateChangeRing.{u} p d =
      algebraMap _ _ p * (↑universalChange.{u}.u⁻¹) ^ n := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, ← hn, map_pow, mul_assoc, ← mul_pow,
      mul_comm _ (algebraMap _ _ (MvPolynomial.X 0)), hu, one_pow, mul_one]
  show ψ (IsLocalization.mk' coordinateChangeRing.{u} p d) ∈ J
  rw [key, map_mul, map_pow]
  exact J.mul_mem (hpoly p) (J.pow_mem hinv n)

/-- **The morphism `(γ, C) ↦ (γ • C, C)` from `H × W` to `W × W` is integral**, viewed as a
morphism to the pullback of `W` and `W` over the terminal scheme. -/
private theorem isIntegralHom_prodLift_actionMap_productToBase_comp :
    IsIntegralHom (prod.lift actionMap.{u} productToBase.{u} ≫
      (prodIsoPullback base.{u} base.{u}).hom) := by
  let e := prodIsoPullback base.{u} base.{u}
  let g := prod.lift actionMap.{u} productToBase.{u} ≫ e.hom
  have hact : actionMap.{u} = g ≫ (e.inv ≫ prod.fst) := by simp [g]
  have hpb : productToBase.{u} = g ≫ (e.inv ≫ prod.snd) := by simp [g]
  rw [@HasAffineProperty.iff_of_isAffine _ _ IsIntegralHom.hasAffineProperty]
  refine ⟨inferInstance, ?_⟩
  show RingHom.IsIntegral g.appTop.hom
  let := g.appTop.hom.toAlgebra
  set J := integralClosure Γ(pullback (terminal.from base.{u}) (terminal.from base.{u}), ⊤)
    Γ(coordinateChangeProduct.{u}, ⊤)
  -- elements pulled back along `g` are integral
  have hmem (q : coordinateChangeProduct.{u} ⟶ base.{u})
      (π : pullback (terminal.from base.{u}) (terminal.from base.{u}) ⟶ base.{u})
      (hq : q = g ≫ π) (x : baseRing.{u}) : ringOf q x ∈ J := by
    rw [show ringOf q = (Scheme.ΓSpecIso _).inv ≫ π.appTop ≫ g.appTop by
      rw [ringOf, hq, Scheme.Hom.comp_appTop]]
    exact isIntegral_algebraMap
  -- the coordinate change and the two equations
  set γ := changeAt productToGroup.{u}
  set C := curveAt productToBase.{u}
  have hC' : curveAt actionMap.{u} = γ • C := curveAt_actionMap
  have hcoeff (q : coordinateChangeProduct.{u} ⟶ base.{u}) (hq : ∀ x, ringOf q x ∈ J) :
      (curveAt q).a₁ ∈ J ∧ (curveAt q).a₂ ∈ J ∧ (curveAt q).a₃ ∈ J ∧ (curveAt q).a₄ ∈ J ∧
        (curveAt q).a₆ ∈ J ∧ (curveAt q).Δ * ringOf q (↑isUnit_curve_Δ.{u}.unit⁻¹) = 1 := by
    refine ⟨hq _, hq _, hq _, hq _, hq _, ?_⟩
    rw [curveAt, WeierstrassCurve.map_Δ, ← map_mul, IsUnit.mul_val_inv, map_one]
  obtain ⟨h₁, h₂, h₃, h₄, h₆, hδ⟩ := hcoeff _ (hmem _ _ hpb)
  obtain ⟨h₁', h₂', h₃', h₄', h₆', hδ'⟩ := hcoeff _ (hmem _ _ hact)
  rw [hC'] at h₁' h₂' h₃' h₄' h₆' hδ'
  obtain ⟨hu, hv, hr, hs, ht⟩ := mem_integralClosure_variableChange γ C h₁ h₂ h₃ h₄ h₆
    h₁' h₂' h₃' h₄' h₆' _ _ hδ hδ' (hmem _ _ hpb _) (hmem _ _ hact _)
  -- the coordinate ring of `H × W` is generated by `H` and `W`
  have htop : J.toSubring = ⊤ := by
    refine CommRingCat.eq_top_of_isPushout (isPushout_appTop_of_isPullback
      (IsPullback.of_hasPullback coordinateChangeGroupToSpecZ.{u}
        (specULiftZIsTerminal.from base.{u}))) J.toSubring (fun b ↦ ?_) (fun c ↦ ?_)
    · have : (pullback.fst coordinateChangeGroupToSpecZ.{u}
          (specULiftZIsTerminal.from base.{u})).appTop b =
          ringOf productToGroup.{u} ((Scheme.ΓSpecIso _).hom b) := by
        simp [ringOf]
      rw [this]
      refine coordinateChangeRing_map_mem (ringOf productToGroup.{u}).hom J.toSubring
        (fun i ↦ ?_) hv _
      fin_cases i
      exacts [hu, hs, hr, ht]
    · have : (pullback.snd coordinateChangeGroupToSpecZ.{u}
          (specULiftZIsTerminal.from base.{u})).appTop c =
          ringOf productToBase.{u} ((Scheme.ΓSpecIso _).hom c) := by
        simp [ringOf]
      rw [this]
      exact hmem _ _ hpb _
  exact fun x ↦ show x ∈ J.toSubring from htop ▸ Subring.mem_top x

/-- **The morphism `(γ, C) ↦ (γ • C, C)` from `H × W` to `W × W` is finite.** Its fibre over a
pair `(C', C)` of Weierstrass equations is the scheme of coordinate changes carrying `C` to
`C'`. -/
theorem isFinite_prodLift_actionMap_productToBase :
    IsFinite (prod.lift actionMap.{u} productToBase.{u}) := by
  set f := prod.lift actionMap.{u} productToBase.{u}
  let e := prodIsoPullback base.{u} base.{u}
  suffices IsFinite (f ≫ e.hom) by
    rw [show f = (f ≫ e.hom) ≫ e.inv by simp]
    infer_instance
  let g := f ≫ e.hom
  have hpb : productToBase.{u} = g ≫ (e.inv ≫ prod.snd) := by simp [g, f]
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  refine ⟨isIntegralHom_prodLift_actionMap_productToBase_comp, ?_⟩
  have : LocallyOfFiniteType (g ≫ (e.inv ≫ prod.snd)) := by
    rw [← hpb]
    have := smooth_coordinateChangeGroupToSpecZ.{u}
    have : LocallyOfFiniteType coordinateChangeGroupToSpecZ.{u} := inferInstance
    infer_instance
  exact locallyOfFiniteType_of_comp g (e.inv ≫ prod.snd)

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
