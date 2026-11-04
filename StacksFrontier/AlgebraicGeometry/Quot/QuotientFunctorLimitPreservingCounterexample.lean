module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The algebra behind the failure of Stacks 082Q as written

Stacks 082Q asserts that `Q^{fp}_{F/X/B}` is limit preserving when `f : X → B` is quasi-compact
and quasi-separated and `F` is of finite presentation.  This is false; the counterexample is
`B = Spec ℚ[t]`, `X = Spec B₀` with `B₀ = ℚ[t][y_a : a ∈ ℚ]/((t - a) y_a)`, `F = 𝒪_X`, and the
limit `Spec ℚ(t) = lim Spec ℚ[t]_g` over `g ≠ 0`.  Over `ℚ(t)` every `y_a` dies, so the identity
quotient of `F` over `Spec ℚ(t)` lies in `Q^{fp}`.  This file proves the commutative algebra that
shows that it comes from no stage.

Let `g ≠ 0` and let `R_g = ℚ[t]_g[y_a : a ∈ ℚ]/((t - a) y_a)`, the base change of `B₀` to the
stage `ℚ[t]_g`.  The generic point is the ring map `R_g → ℚ(t)`, `y_a ↦ 0`.  A quotient `R_g/J`
which is flat over `ℚ[t]_g` and whose kernel `J` dies at the generic point is *not* of finite
presentation over `R_g`:

* flatness makes `R_g/J` torsion free over `ℚ[t]_g`, and `(t - a) y_a = 0`, so every `y_a` lies
  in `J`;
* `J` dies at the generic point, whose kernel is the ideal `(y_a : a ∈ ℚ)`, so `J = (y_a)`;
* a finitely presented quotient has a finitely generated kernel, but `(y_a)` is not finitely
  generated: for `a` outside a finite set of indices and off the roots of `g`, the ring map
  `R_g → ℚ`, `t ↦ a`, `y_a ↦ 1`, `y_b ↦ 0` for `b ≠ a`, kills the `y_b` with `b` in the finite
  set but not `y_a`.

## Main results

* `AlgebraicGeometry.QuotientFunctorCounterexample.not_finitePresentation_quotient`: a quotient
  of `R_g` which is flat over `ℚ[t]_g` and is the identity quotient at the generic point is not
  of finite presentation.

## References

* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
-/

@[expose] public noncomputable section

open Polynomial

namespace AlgebraicGeometry.QuotientFunctorCounterexample

variable (g : ℚ[X])

/-- The coordinate ring `ℚ[t]_g` of the stage `Spec ℚ[t]_g`. -/
abbrev StageRing : Type := Localization.Away g

/-- The relation `(t - a) y_a`. -/
def relation (a : ℚ) : MvPolynomial ℚ (StageRing g) :=
  MvPolynomial.C (algebraMap ℚ[X] (StageRing g) (X - C a)) * MvPolynomial.X a

/-- The ideal of the relations `(t - a) y_a`. -/
def relations : Ideal (MvPolynomial ℚ (StageRing g)) := Ideal.span (Set.range (relation g))

/-- The coordinate ring `R_g = ℚ[t]_g[y_a : a ∈ ℚ]/((t - a) y_a)` of the base change of
`X = Spec B₀` to the stage. -/
abbrev FibreRing : Type := MvPolynomial ℚ (StageRing g) ⧸ relations g

/-- The generator `y_a` of `R_g`. -/
def y (a : ℚ) : FibreRing g := Ideal.Quotient.mk _ (MvPolynomial.X a)

/-- The ideal `(y_a : a ∈ ℚ)` of `R_g`. -/
def yIdeal : Ideal (FibreRing g) := Ideal.span (Set.range (y g))

variable {g}

/-- The image of `c ∈ ℚ[t]_g` in `R_g` is the class of the constant polynomial `c`. -/
theorem algebraMap_fibreRing (c : StageRing g) :
    algebraMap (StageRing g) (FibreRing g) c = Ideal.Quotient.mk _ (MvPolynomial.C c) := by
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]

/-- The relation `(t - a) y_a` lies in the ideal of relations. -/
theorem relation_mem (a : ℚ) : relation g a ∈ relations g := Ideal.subset_span ⟨a, rfl⟩

/-- The relation `(t - a) y_a = 0` in `R_g`. -/
theorem algebraMap_mul_y (a : ℚ) :
    algebraMap (StageRing g) (FibreRing g) (algebraMap ℚ[X] (StageRing g) (X - C a)) * y g a =
      0 := by
  rw [algebraMap_fibreRing, y, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact relation_mem a

/-- A ring map out of `R_g`, given by its restriction to `ℚ[t]_g` and its values on the `y_a`,
provided the relations hold. -/
def lift {A : Type*} [CommRing A] (φ : StageRing g →+* A) (v : ℚ → A)
    (hv : ∀ a, φ (algebraMap ℚ[X] (StageRing g) (X - C a)) * v a = 0) : FibreRing g →+* A :=
  Ideal.Quotient.lift (relations g) (MvPolynomial.eval₂Hom φ v) (fun p hp => by
    have : relations g ≤ RingHom.ker (MvPolynomial.eval₂Hom φ v) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, relation, map_mul, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
      exact hv a
    exact this hp)

/-- The ring map `lift φ v hv` sends `y_a` to `v a`. -/
theorem lift_y {A : Type*} [CommRing A] (φ : StageRing g →+* A) (v : ℚ → A)
    (hv : ∀ a, φ (algebraMap ℚ[X] (StageRing g) (X - C a)) * v a = 0) (a : ℚ) :
    lift φ v hv (y g a) = v a := by
  simp [lift, y]

/-- The ring map `lift φ v hv` restricts to `φ` on `ℚ[t]_g`. -/
theorem lift_algebraMap {A : Type*} [CommRing A] (φ : StageRing g →+* A) (v : ℚ → A)
    (hv : ∀ a, φ (algebraMap ℚ[X] (StageRing g) (X - C a)) * v a = 0) (c : StageRing g) :
    lift φ v hv (algebraMap (StageRing g) (FibreRing g) c) = φ c := by
  rw [algebraMap_fibreRing]
  simp [lift]

variable (hg : g ≠ 0)

include hg in
/-- The powers of a nonzero polynomial `g` are nonzerodivisors of `ℚ[t]`. -/
theorem powers_le : Submonoid.powers g ≤ nonZeroDivisors ℚ[X] :=
  powers_le_nonZeroDivisors_of_noZeroDivisors hg

include hg in
/-- For `g ≠ 0`, the localization `ℚ[t]_g` is an integral domain. -/
theorem isDomain_stageRing : IsDomain (StageRing g) :=
  IsLocalization.isDomain_localization (powers_le hg)

/-- The map `ℚ[t]_g → ℚ(t)`. -/
def toFraction : StageRing g →+* FractionRing ℚ[X] :=
  IsLocalization.Away.lift g (g := algebraMap ℚ[X] (FractionRing ℚ[X]))
    (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (FractionRing ℚ[X]))).mpr hg))

/-- The map `ℚ[t]_g → ℚ(t)` restricts to the canonical map `ℚ[t] → ℚ(t)`. -/
theorem toFraction_algebraMap (p : ℚ[X]) :
    toFraction hg (algebraMap ℚ[X] (StageRing g) p) = algebraMap ℚ[X] (FractionRing ℚ[X]) p :=
  IsLocalization.lift_eq _ _

/-- The map `ℚ[t]_g → ℚ(t)` is injective. -/
theorem toFraction_injective : Function.Injective (toFraction hg) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) x
  have h := (IsLocalization.lift_mk'_spec (S := StageRing g) _ (p) (0 : FractionRing ℚ[X]) s).1
    (by rw [← hx]; rfl)
  rw [mul_zero, map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] (FractionRing ℚ[X]))] at h
  rw [h]
  exact IsLocalization.mk'_zero _

/-- The generic point `R_g → ℚ(t)`, `y_a ↦ 0`. -/
def generic : FibreRing g →+* FractionRing ℚ[X] :=
  lift (toFraction hg) (fun _ => 0) (fun _ => mul_zero _)

/-- The retraction `R_g → ℚ[t]_g`, `y_a ↦ 0`. -/
def retraction : FibreRing g →+* StageRing g :=
  lift (RingHom.id _) (fun _ => 0) (fun _ => mul_zero _)

/-- The generic point `R_g → ℚ(t)` is the retraction `R_g → ℚ[t]_g` followed by
`ℚ[t]_g → ℚ(t)`. -/
theorem generic_eq (r : FibreRing g) : generic hg r = toFraction hg (retraction r) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction p using MvPolynomial.induction_on with
  | C c => simp [generic, retraction, lift]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp => simp only [map_mul, hp]; simp [generic, retraction, lift]

/-- Every `r ∈ R_g` differs from the image of its retraction in `ℚ[t]_g` by an element of the
ideal `(y_a : a ∈ ℚ)`. -/
theorem sub_retraction_mem (r : FibreRing g) :
    r - algebraMap (StageRing g) (FibreRing g) (retraction r) ∈ yIdeal g := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction p using MvPolynomial.induction_on with
  | C c =>
    have : retraction (Ideal.Quotient.mk (relations g) (MvPolynomial.C c)) = c := by
      simp [retraction, lift]
    rw [this, algebraMap_fibreRing, sub_self]
    exact Ideal.zero_mem _
  | add p q hp hq =>
    rw [map_add, map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  | mul_X p a hp =>
    have h0 : retraction (Ideal.Quotient.mk (relations g) (p * MvPolynomial.X a)) = 0 := by
      simp [retraction, lift]
    rw [h0, map_zero, sub_zero, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)

/-- The kernel of the generic point is contained in the ideal `(y_a : a ∈ ℚ)`. -/
theorem ker_generic_le : RingHom.ker (generic hg) ≤ yIdeal g := by
  intro r hr
  rw [RingHom.mem_ker, generic_eq] at hr
  have h0 : retraction r = 0 := (map_eq_zero_iff _ (toFraction_injective hg)).1 hr
  simpa [h0] using sub_retraction_mem r

include hg in
/-- Flatness over `ℚ[t]_g` kills every `y_a`. -/
theorem y_mem_of_flat (J : Ideal (FibreRing g)) [Module.Flat (StageRing g) (FibreRing g ⧸ J)]
    (a : ℚ) : y g a ∈ J := by
  have := isDomain_stageRing hg
  have hne : algebraMap ℚ[X] (StageRing g) (X - C a) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsLocalization.injective (StageRing g) (powers_le hg))]
    exact X_sub_C_ne_zero a
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := FibreRing g ⧸ J)
    (mem_nonZeroDivisors_of_ne_zero hne)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine hreg ?_
  have h := ((Ideal.Quotient.mkₐ (StageRing g) J).toLinearMap.map_smul
    (algebraMap ℚ[X] (StageRing g) (X - C a)) (y g a)).symm
  have h0 : (algebraMap ℚ[X] (StageRing g) (X - C a)) • y g a = 0 := by
    rw [Algebra.smul_def]
    exact algebraMap_mul_y a
  rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, h0,
    map_zero] at h
  exact h.trans (smul_zero _).symm

/-- The evaluation `ℚ[t]_g → ℚ` at a point `a` off the roots of `g`. -/
def evalAt (a : ℚ) (ha : g.eval a ≠ 0) : StageRing g →+* ℚ :=
  IsLocalization.Away.lift g (g := Polynomial.evalRingHom a) (IsUnit.mk0 _ ha)

/-- The evaluation `ℚ[t]_g → ℚ` at `a` sends the image of `p ∈ ℚ[t]` to `p(a)`. -/
theorem evalAt_algebraMap (a : ℚ) (ha : g.eval a ≠ 0) (p : ℚ[X]) :
    evalAt a ha (algebraMap ℚ[X] (StageRing g) p) = p.eval a :=
  IsLocalization.lift_eq _ _

/-- The point `t = a`, `y_a = 1`, `y_b = 0` for `b ≠ a` of `R_g`. -/
def pointAt (a : ℚ) (ha : g.eval a ≠ 0) : FibreRing g →+* ℚ :=
  lift (evalAt a ha) (fun b => if b = a then 1 else 0) (fun b => by
    rw [evalAt_algebraMap]
    split_ifs with h
    · subst h; simp
    · simp)

include hg in
/-- **The ideal `(y_a : a ∈ ℚ)` of `R_g` is not finitely generated.** -/
theorem not_fg_yIdeal : ¬ (yIdeal g).FG := by
  classical
  rintro ⟨s, hs⟩
  have hmem : ∀ x ∈ s, ∃ T : Finset (FibreRing g), ↑T ⊆ Set.range (y g) ∧
      x ∈ Submodule.span (FibreRing g) (T : Set (FibreRing g)) := fun x hx =>
    Submodule.mem_span_finite_of_mem_span (by
      have : x ∈ yIdeal g := hs ▸ Ideal.subset_span hx
      exact this)
  choose T hTy hxT using hmem
  let T' : Finset (FibreRing g) := s.attach.biUnion fun x => T x.1 x.2
  have hT'y : ∀ t ∈ T', ∃ b, y g b = t := by
    intro t ht
    obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.1 ht
    exact hTy x.1 x.2 hx
  choose! idx hidx using hT'y
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (T'.image idx ∪ g.roots.toFinset)
  have ha₁ : a ∉ T'.image idx := fun h => ha (Finset.mem_union_left _ h)
  have ha₂ : g.eval a ≠ 0 := fun h => ha (Finset.mem_union_right _
    (Multiset.mem_toFinset.2 ((mem_roots hg).2 h)))
  have hker : yIdeal g ≤ RingHom.ker (pointAt a ha₂) := by
    rw [← hs, Ideal.span_le]
    intro x hx
    have hsub : Submodule.span (FibreRing g) (T x hx : Set (FibreRing g)) ≤
        RingHom.ker (pointAt a ha₂) := by
      refine Submodule.span_le.2 fun t ht => ?_
      have htT' : t ∈ T' := Finset.mem_biUnion.2 ⟨⟨x, hx⟩, Finset.mem_attach _ _, ht⟩
      have hb : idx t ≠ a := fun h => ha₁ (Finset.mem_image.2 ⟨t, htT', h⟩)
      rw [SetLike.mem_coe, RingHom.mem_ker, ← hidx t htT', pointAt, lift_y, if_neg hb]
    exact hsub (hxT x hx)
  have h1 := hker (Ideal.subset_span ⟨a, rfl⟩ : y g a ∈ yIdeal g)
  rw [RingHom.mem_ker, pointAt, lift_y, if_pos rfl] at h1
  exact one_ne_zero h1

include hg in
/-- **The algebra behind the failure of Stacks 082Q as written.**  Let `g ≠ 0` and let
`R_g = ℚ[t]_g[y_a : a ∈ ℚ]/((t - a) y_a)`.  A quotient `R_g/J` which is flat over `ℚ[t]_g`
and whose kernel `J` dies at the generic point `R_g → ℚ(t)` — that is, which is the identity
quotient over `ℚ(t)` — is not of finite presentation over `R_g`. -/
theorem not_finitePresentation_quotient (J : Ideal (FibreRing g))
    [Module.Flat (StageRing g) (FibreRing g ⧸ J)] (hJ : J ≤ RingHom.ker (generic hg)) :
    ¬ Module.FinitePresentation (FibreRing g) (FibreRing g ⧸ J) := by
  intro hfp
  have hJy : J = yIdeal g := le_antisymm (hJ.trans (ker_generic_le hg))
    (Ideal.span_le.2 (by rintro _ ⟨a, rfl⟩; exact y_mem_of_flat hg J a))
  have hfg := Module.FinitePresentation.fg_ker (Submodule.mkQ J) (Submodule.mkQ_surjective J)
  rw [Submodule.ker_mkQ, hJy] at hfg
  exact not_fg_yIdeal hg hfg

end AlgebraicGeometry.QuotientFunctorCounterexample

end
