module

public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentreChartCover

/-!
# The second-centre factorization over an affine open of the base

Let `X` be a scheme, `I` a finite-type quasi-coherent ideal sheaf, `b : X' = Bl_I(X) ⟶ X` the
blowup with exceptional ideal `E = I·𝒪_{X'}`, and `Z'` a finite-type ideal sheaf on `X'`. Fix an
affine open `U` of `X` and a finite family `A` of sections of `I` over `U`. This file produces,
for every large enough degree `d`, a finite set `G` of sections of `Iᵈ` over `U` whose pullbacks

* lie in `Eᵈ · Z'` on the chart attached to every member of `A`, and
* generate `Eᵈ · Z'` on each of those charts.

That is the affine-local half of the second-centre factorization of [Stacks, Tag 0803]; the
globalization is in `StacksFrontier/AlgebraicGeometry/Blowup/SecondCentre.lean`.

The mathematical content is the division step. A section `y` of `Z'` on the chart at `a` is a
fraction `x / aᵐ`; the candidate generator is `a^{d-m}·x`, and on the chart at another
denominator `b` that element is `bᵈ` times `h^{d-m}·w`, where `h` is the comparison unit
`a / b` and `w` is `x / bᵐ`. Over the basic open of `h` — which lies inside the chart at `a`,
because there `a` too generates the exceptional ideal — the sections `w` and `hᵐ · y` agree,
since `b` is a nonzerodivisor; so `w` lies in `Z'` there, and as the sections over that basic
open are the localization at `h`, some power of `h` already carries `w` into `Z'`. Taking `d`
past the finitely many exponents so produced makes every candidate generator a section of the
saturation.

## Main results

* `AlgebraicGeometry.exists_pow_mul_mem_ideal_of_chart`: the division step.
* `AlgebraicGeometry.exists_secondCentreGenerator`: one generator, for a single section of `Z'`
  on one chart.
* `AlgebraicGeometry.exists_secondCentreGenerators`: the finite set of generators, for all large
  degrees.
* `AlgebraicGeometry.exists_finset_span_eq`: a finite generating family of the centre over an
  affine open, containing the zero section.

## References

* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The division step.** Let `a` and `b` be two denominators over an affine open `U`, let
`x ∈ Γ(X, U)` be a section whose pullback to the chart at `a` is `y · aᵐ` with `y` a section of
`Z'`, and write the pullback of `a` to the chart at `b` as `h · b` and the pullback of `x` as
`bᵐ · w`. Then a power of `h` carries `w` into `Z'`. -/
theorem exists_pow_mul_mem_ideal_of_chart (Z' : (blowUp I).IdealSheafData)
    (U : X.affineOpens) (a b : I.ideal U) {m : ℕ} {x : Γ(X, U.1)}
    {y : Γ(blowUp I, (blowUpChartOpen I U a).1)}
    (hy : y ∈ Z'.ideal (blowUpChartOpen I U a))
    (hxy : y * (blowUpChartMap I U a).hom (a : Γ(X, U.1)) ^ m = (blowUpChartMap I U a).hom x)
    (h w : Γ(blowUp I, (blowUpChartOpen I U b).1))
    (hh : (blowUpChartMap I U b).hom (a : Γ(X, U.1))
      = h * (blowUpChartMap I U b).hom (b : Γ(X, U.1)))
    (hw : (blowUpChartMap I U b).hom x
      = (blowUpChartMap I U b).hom (b : Γ(X, U.1)) ^ m * w) :
    ∃ N : ℕ, h ^ N * w ∈ Z'.ideal (blowUpChartOpen I U b) := by
  classical
  have hDWb : (blowUp I).basicOpen h ≤ (blowUpChartOpen I U b).1 := (blowUp I).basicOpen_le h
  have hDWa : (blowUp I).basicOpen h ≤ (blowUpChartOpen I U a).1 :=
    basicOpen_le_blowUpChartOpen I U b a h hh
  have hDaff : IsAffineOpen ((blowUp I).basicOpen h) := (blowUpChartOpen I U b).2.basicOpen h
  set rb := (blowUp I).presheaf.map (homOfLE hDWb).op
  set ra := (blowUp I).presheaf.map (homOfLE hDWa).op
  have hcompat : ∀ r : Γ(X, U.1), rb.hom ((blowUpChartMap I U b).hom r)
      = ra.hom ((blowUpChartMap I U a).hom r) := by
    intro r
    have e1 : blowUpChartMap I U b ≫ rb
        = (blowUpToBase I).appLE U.1 ((blowUp I).basicOpen h)
          (hDWb.trans (blowUpChartOpen_le I U b)) := Scheme.Hom.appLE_map _ _ _
    have e2 : blowUpChartMap I U a ≫ ra
        = (blowUpToBase I).appLE U.1 ((blowUp I).basicOpen h)
          (hDWb.trans (blowUpChartOpen_le I U b)) := Scheme.Hom.appLE_map _ _ _
    exact congrArg (fun φ => φ.hom r) (e1.trans e2.symm)
  have hkey : rb.hom ((blowUpChartMap I U b).hom (b : Γ(X, U.1))) ^ m * rb.hom w
      = rb.hom ((blowUpChartMap I U b).hom (b : Γ(X, U.1))) ^ m
        * (rb.hom h ^ m * ra.hom y) := by
    have hleft : rb.hom ((blowUpChartMap I U b).hom (b : Γ(X, U.1))) ^ m * rb.hom w
        = ra.hom ((blowUpChartMap I U a).hom x) := by
      rw [← map_pow, ← map_mul, ← hw, hcompat]
    have hright : rb.hom ((blowUpChartMap I U b).hom (b : Γ(X, U.1))) ^ m
          * (rb.hom h ^ m * ra.hom y)
        = ra.hom ((blowUpChartMap I U a).hom x) := by
      have hstep : rb.hom ((blowUpChartMap I U b).hom (b : Γ(X, U.1))) ^ m * rb.hom h ^ m
          = ra.hom ((blowUpChartMap I U a).hom (a : Γ(X, U.1))) ^ m := by
        rw [← mul_pow, ← map_mul,
          mul_comm ((blowUpChartMap I U b).hom (b : Γ(X, U.1))) h, ← hh, hcompat]
      rw [← hxy, map_mul, map_pow, ← hstep]
      ring
    rw [hleft, hright]
  have : IsLocalization.Away h Γ(blowUp I, (blowUp I).basicOpen h) :=
    (blowUpChartOpen I U b).2.isLocalization_basicOpen h
  have hnzd : rb.hom ((blowUpChartMap I U b).hom (b : Γ(X, U.1)))
      ∈ nonZeroDivisors Γ(blowUp I, (blowUp I).basicOpen h) :=
    IsLocalization.map_nonZeroDivisors_le (Submonoid.powers h) _
      ⟨_, blowUpChartMap_self_mem_nonZeroDivisors I U b, rfl⟩
  have hcancel : rb.hom w = rb.hom h ^ m * ra.hom y := by
    have hsub : (rb.hom w - (rb.hom h ^ m * ra.hom y))
        * rb.hom ((blowUpChartMap I U b).hom (b : Γ(X, U.1))) ^ m = 0 := by
      rw [sub_mul, mul_comm (rb.hom w), mul_comm (rb.hom h ^ m * ra.hom y), hkey, sub_self]
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp (pow_mem hnzd m)).2 _ hsub)
  have hyD : ra.hom y ∈ Z'.ideal ⟨(blowUp I).basicOpen h, hDaff⟩ := by
    rw [← Scheme.IdealSheafData.map_ideal Z' (U := ⟨(blowUp I).basicOpen h, hDaff⟩) hDWa]
    exact Ideal.mem_map_of_mem _ hy
  have hwD : rb.hom w ∈ (Z'.ideal (blowUpChartOpen I U b)).map rb.hom := by
    rw [show (Z'.ideal (blowUpChartOpen I U b)).map rb.hom
        = Z'.ideal ⟨(blowUp I).basicOpen h, hDaff⟩ from
      Z'.map_ideal_basicOpen (blowUpChartOpen I U b) h, hcancel]
    exact Ideal.mul_mem_left _ _ hyD
  obtain ⟨_, ⟨N, rfl⟩, hMw⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers h)
      Γ(blowUp I, (blowUp I).basicOpen h) (Z'.ideal (blowUpChartOpen I U b)) w).mp hwD
  exact ⟨N, hMw⟩


/-- On a chart, the ideal of `Eᵈ · Z'` is the product of the `d`-th power of the exceptional
generator with the ideal of `Z'`. -/
theorem ideal_exceptionalPow_mul (Z' : (blowUp I).IdealSheafData) (U : X.affineOpens)
    (b : I.ideal U) (d : ℕ) :
    ((exceptionalIdeal I) ^ d * Z').ideal (blowUpChartOpen I U b)
      = Ideal.span {(blowUpChartMap I U b).hom (b : Γ(X, U.1)) ^ d}
        * Z'.ideal (blowUpChartOpen I U b) := by
  change ((exceptionalIdeal I).ideal (blowUpChartOpen I U b)) ^ d
      * Z'.ideal (blowUpChartOpen I U b) = _
  rw [ideal_exceptionalIdeal_blowUpChartOpen, Ideal.span_singleton_pow]

/-- The pullback of a section of the centre to a chart lies in the ideal generated by the
exceptional generator there. -/
theorem blowUpChartMap_mem_span (U : X.affineOpens) (b : I.ideal U) (r : Γ(X, U.1))
    (hr : r ∈ I.ideal U) :
    (blowUpChartMap I U b).hom r
      ∈ Ideal.span {(blowUpChartMap I U b).hom (b : Γ(X, U.1))} := by
  rw [← ideal_exceptionalIdeal_blowUpChartOpen I U b,
    show (exceptionalIdeal I).ideal (blowUpChartOpen I U b)
      = (I.ideal U).map (blowUpChartMap I U b).hom from
    Stacks.IdealSheaf.ideal_comap_appLE I (blowUpToBase I) U _ (blowUpChartOpen_le I U b)]
  exact Ideal.mem_map_of_mem _ hr

/-- **One generator of the second-centre factorization over an affine open.** For a section `y`
of `Z'` on the chart at `a`, all large enough degrees `d` admit a section `t` of `Iᵈ` whose
pullback to the chart at `a` is `aᵈ · y` and whose pullback to the chart at any `b` of a
prescribed finite family lies in `Eᵈ · Z'`. -/
theorem exists_secondCentreGenerator (Z' : (blowUp I).IdealSheafData) (U : X.affineOpens)
    (A : Finset (I.ideal U)) (a : I.ideal U)
    (y : Γ(blowUp I, (blowUpChartOpen I U a).1))
    (hy : y ∈ Z'.ideal (blowUpChartOpen I U a)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∃ t : Γ(X, U.1), t ∈ (I.ideal U) ^ d ∧
      (blowUpChartMap I U a).hom t
        = (blowUpChartMap I U a).hom (a : Γ(X, U.1)) ^ d * y ∧
      ∀ b ∈ A, (blowUpChartMap I U b).hom t ∈
        ((exceptionalIdeal I) ^ d * Z').ideal (blowUpChartOpen I U b) := by
  classical
  obtain ⟨m, x, hx, hxy⟩ := exists_mem_pow_mul_eq_blowUpChartMap I U a y
  have hdata : ∀ b : I.ideal U, ∃ (N : ℕ) (h w : Γ(blowUp I, (blowUpChartOpen I U b).1)),
      (blowUpChartMap I U b).hom (a : Γ(X, U.1))
          = h * (blowUpChartMap I U b).hom (b : Γ(X, U.1)) ∧
        (blowUpChartMap I U b).hom x
          = (blowUpChartMap I U b).hom (b : Γ(X, U.1)) ^ m * w ∧
        h ^ N * w ∈ Z'.ideal (blowUpChartOpen I U b) := by
    intro b
    obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp (blowUpChartMap_mem_span I U b _ a.2)
    obtain ⟨w, hw⟩ := exists_mul_eq_blowUpChartMap_of_mem_pow I U b hx
    obtain ⟨N, hN⟩ := exists_pow_mul_mem_ideal_of_chart I Z' U a b hy hxy h w hh.symm hw
    exact ⟨N, h, w, hh.symm, hw, hN⟩
  choose N h w hh hw hN using hdata
  refine ⟨m + A.sup N, fun d hd => ?_⟩
  have hsplit : ∀ {R : Type u} [CommRing R] (z : R), z ^ d = z ^ (d - m) * z ^ m :=
    fun z => (pow_sub_mul_pow z (by omega)).symm
  refine ⟨(a : Γ(X, U.1)) ^ (d - m) * x, ?_, ?_, fun b hb => ?_⟩
  · have := Ideal.mul_mem_mul (Ideal.pow_mem_pow a.2 (d - m)) hx
    rwa [← pow_add, Nat.sub_add_cancel (by omega)] at this
  · rw [map_mul, map_pow, ← hxy, hsplit]
    ring
  · have hmul : (blowUpChartMap I U b).hom ((a : Γ(X, U.1)) ^ (d - m) * x)
        = (blowUpChartMap I U b).hom (b : Γ(X, U.1)) ^ d * (h b ^ (d - m) * w b) := by
      rw [map_mul, map_pow, hh b, hw b, mul_pow, hsplit]
      ring
    rw [hmul, ideal_exceptionalPow_mul]
    refine Ideal.mul_mem_mul (Ideal.subset_span rfl) ?_
    have hle : N b ≤ A.sup N := Finset.le_sup hb
    rw [show d - m = (d - m - N b) + N b by omega, pow_add, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hN b)


/-- The generators produced one at a time, by induction on a finite family of pairs `(a, y)`
with `y` a section of `Z'` on the chart at `a`. -/
private theorem exists_secondCentreGenerators_of_finset (Z' : (blowUp I).IdealSheafData)
    (U : X.affineOpens)
    (A : Finset (I.ideal U))
    (J : Finset ((a : I.ideal U) × Γ(blowUp I, (blowUpChartOpen I U a).1)))
    (hJ : ∀ j ∈ J, j.2 ∈ Z'.ideal (blowUpChartOpen I U j.1)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∃ G : Finset Γ(X, U.1),
      (∀ t ∈ G, t ∈ (I.ideal U) ^ d) ∧
      (∀ b ∈ A, ∀ t ∈ G, (blowUpChartMap I U b).hom t ∈
        ((exceptionalIdeal I) ^ d * Z').ideal (blowUpChartOpen I U b)) ∧
      (∀ j ∈ J, (blowUpChartMap I U j.1).hom (j.1 : Γ(X, U.1)) ^ d * j.2 ∈
        Ideal.span ((fun t => (blowUpChartMap I U j.1).hom t) '' (G : Set Γ(X, U.1)))) := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨0, fun d _ => ⟨∅, by simp, by simp, by simp⟩⟩
  | @insert j J hj ih =>
    obtain ⟨d₁, hd₁⟩ := ih fun k hk => hJ k (Finset.mem_insert_of_mem hk)
    obtain ⟨d₂, hd₂⟩ :=
      exists_secondCentreGenerator I Z' U A j.1 j.2 (hJ j (Finset.mem_insert_self j J))
    refine ⟨max d₁ d₂, fun d hd => ?_⟩
    obtain ⟨G, hG1, hG2, hG3⟩ := hd₁ d ((le_max_left _ _).trans hd)
    obtain ⟨t, ht1, ht2, ht3⟩ := hd₂ d ((le_max_right _ _).trans hd)
    refine ⟨insert t G, ?_, ?_, ?_⟩
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact ht1
      · exact hG1 s hs
    · intro b hb s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact ht3 b hb
      · exact hG2 b hb s hs
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · rw [← ht2]
        exact Ideal.subset_span ⟨t, by simp, rfl⟩
      · exact Ideal.span_mono (Set.image_mono fun z hz => Finset.mem_insert_of_mem hz) (hG3 k hk)

/-- **The second-centre factorization over an affine open of the base.** For all large enough
degrees `d` there is a finite set of sections of `Iᵈ` over `U` whose pullbacks lie in `Eᵈ · Z'`
on every chart of a prescribed finite family, and generate `Eᵈ · Z'` on each of them. -/
theorem exists_secondCentreGenerators (Z' : (blowUp I).IdealSheafData) (hZ' : Z'.IsFiniteType)
    (U : X.affineOpens) (A : Finset (I.ideal U)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∃ G : Finset Γ(X, U.1),
      (∀ t ∈ G, t ∈ (I.ideal U) ^ d) ∧
      (∀ b ∈ A, ∀ t ∈ G, (blowUpChartMap I U b).hom t ∈
        ((exceptionalIdeal I) ^ d * Z').ideal (blowUpChartOpen I U b)) ∧
      (∀ b ∈ A, ((exceptionalIdeal I) ^ d * Z').ideal (blowUpChartOpen I U b) ≤
        Ideal.span ((fun t => (blowUpChartMap I U b).hom t) '' (G : Set Γ(X, U.1)))) := by
  classical
  have hgen : ∀ b : I.ideal U, ∃ Y : Finset Γ(blowUp I, (blowUpChartOpen I U b).1),
      Ideal.span (Y : Set Γ(blowUp I, (blowUpChartOpen I U b).1))
        = Z'.ideal (blowUpChartOpen I U b) := fun b => hZ' _
  choose Y hY using hgen
  obtain ⟨d₀, hd₀⟩ := exists_secondCentreGenerators_of_finset I Z' U A
    (A.biUnion fun b => (Y b).image fun y => (⟨b, y⟩ :
      (a : I.ideal U) × Γ(blowUp I, (blowUpChartOpen I U a).1))) (by
    intro j hj
    obtain ⟨b, hb, hj'⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj'
    rw [← hY b]
    exact Ideal.subset_span hy)
  refine ⟨d₀, fun d hd => ?_⟩
  obtain ⟨G, hG1, hG2, hG3⟩ := hd₀ d hd
  refine ⟨G, hG1, hG2, fun b hb => ?_⟩
  rw [ideal_exceptionalPow_mul, ← hY b, Ideal.span_mul_span]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨_, rfl, q, hq, rfl⟩
  exact hG3 ⟨b, q⟩ (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩)


/-- A finite generating family of the centre over an affine open, containing the zero section. -/
theorem exists_finset_span_eq (hI : I.IsFiniteType) (U : X.affineOpens) :
    ∃ A : Finset (I.ideal U), (0 : I.ideal U) ∈ A ∧
      Ideal.span ((fun a : I.ideal U => (a : Γ(X, U.1))) '' (A : Set (I.ideal U)))
        = I.ideal U := by
  classical
  obtain ⟨s, hs⟩ := hI U
  have hsub : ∀ z ∈ s, z ∈ I.ideal U := fun z hz => by rw [← hs]; exact Ideal.subset_span hz
  refine ⟨insert 0 (s.attach.image fun x => (⟨x.1, hsub x.1 x.2⟩ : I.ideal U)),
    Finset.mem_insert_self _ _, le_antisymm ?_ ?_⟩
  · refine Ideal.span_le.mpr ?_
    rintro z ⟨c, hc, rfl⟩
    exact c.2
  · refine hs.ge.trans (Ideal.span_le.mpr fun z hz => ?_)
    refine Ideal.subset_span ⟨⟨z, hsub z hz⟩, ?_, rfl⟩
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩)

end AlgebraicGeometry

end
