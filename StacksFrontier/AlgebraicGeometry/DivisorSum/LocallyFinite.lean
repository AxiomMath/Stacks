module

public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sum of a locally finite family of effective Cartier divisors

Let `X` be a scheme and let `Dᵢ` be a family of effective Cartier divisors on `X`, indexed by an
arbitrary type, which is **locally finite**: on every affine open all but finitely many of the
`Dᵢ` are the empty divisor. Then the sum `∑ nᵢ Dᵢ` makes sense for arbitrary multiplicities
`nᵢ : ℕ`, and it is again an effective Cartier divisor.

## Main definitions

* `Stacks.Divisors.IsLocallyFiniteFamily`: on every affine open all but finitely many members of
  the family are the unit ideal, i.e. the empty divisor.
* `Stacks.Divisors.locallyFiniteSum`: the sum `∑ nᵢ Dᵢ` of a locally finite family.

## Main results

* `Stacks.Divisors.locallyFiniteSum_ideal_eq_finsetProd`: on an affine open the sum agrees with
  the finite sum over any finite set of indices containing all those where the family is not the
  empty divisor there.
* `Stacks.Divisors.locallyFiniteSum_antitone`: **the sum is antitone in the multiplicities** —
  raising the `nᵢ` enlarges the divisor and so shrinks its sheaf of ideals.
* `Stacks.Divisors.isEffectiveCartierDivisor_locallyFiniteSum`: **the sum of a locally finite
  family of effective Cartier divisors is an effective Cartier divisor.**
* `Stacks.Divisors.ideal_eq_of_forall_exists_basicOpen`: a quasi-coherent sheaf of ideals is
  determined on an affine open by its restrictions to basic opens of it.
* `Stacks.Divisors.ideal_eq_of_mul_eq_mul_of_ideal_eq_span`: `I * J = I * K` forces `J` and `K` to
  agree on an affine open on which `I` is cut out by one nonzerodivisor.

## Implementation notes

**An intersection, not a product.** There is no product over an infinite family of ideal sheaves,
so the sum is defined as the intersection, over all finite sets of indices `s`, of the partial
sums `∑_{i ∈ s} nᵢ Dᵢ`. These partial sums decrease as `s` grows and are constant on an affine
open once `s` contains every index where the family is not the empty divisor there, so the
intersection is that stable value — which is the honest sum. The intersection makes sense for an
arbitrary family, so it can be written down before any finiteness hypothesis and
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals`, the largest ideal sheaf below a family of
ideals, needs no compatibility proof; local finiteness enters only when the sections are computed.

## References

* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
* [Stacks Project, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT)
* [Stacks Project, Tag 01WU](https://stacks.math.columbia.edu/tag/01WU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### Locally finite families -/

/-- A family of quasi-coherent sheaves of ideals on `X` is **locally finite** when on every affine
open all but finitely many of its members are the unit ideal — that is, when all but finitely many
of the corresponding closed subschemes are empty there. -/
def IsLocallyFiniteFamily {ι : Type*} (D : ι → X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, ∃ t : Finset ι, ∀ i ∉ t, (D i).ideal U = ⊤

/-- If every member of a family outside a finite set `t` is the unit ideal on an affine open `U`,
then the same holds on every affine open `W ≤ U`. -/
theorem forall_ideal_eq_top_of_le {ι : Type*} {D : ι → X.IdealSheafData} {U W : X.affineOpens}
    (hWU : W ≤ U) {t : Finset ι} (ht : ∀ i ∉ t, (D i).ideal U = ⊤) :
    ∀ i ∉ t, (D i).ideal W = ⊤ := by
  intro i hi
  rw [← (D i).map_ideal hWU, ht i hi]
  exact Ideal.map_top _

/-! ### The partial sums -/

/-- A larger partial sum is a larger divisor, hence a smaller ideal. -/
theorem finsetProd_ideal_le_of_subset {ι : Type*} (D : ι → X.IdealSheafData) (n : ι → ℕ)
    (U : X.affineOpens) {s s' : Finset ι} (h : s ⊆ s') :
    (∏ i ∈ s', D i ^ n i).ideal U ≤ (∏ i ∈ s, D i ^ n i).ideal U := by
  classical
  rw [Scheme.IdealSheafData.ideal_finsetProd_eq_prod,
    Scheme.IdealSheafData.ideal_finsetProd_eq_prod, ← Finset.prod_sdiff h]
  exact Ideal.mul_le_right

/-- **Raising the multiplicities enlarges the partial sum, hence shrinks its ideal.** -/
theorem finsetProd_ideal_le_of_le {ι : Type*} (D : ι → X.IdealSheafData) {n m : ι → ℕ}
    (h : n ≤ m) (U : X.affineOpens) (s : Finset ι) :
    (∏ i ∈ s, D i ^ m i).ideal U ≤ (∏ i ∈ s, D i ^ n i).ideal U := by
  rw [Scheme.IdealSheafData.ideal_finsetProd_eq_prod,
    Scheme.IdealSheafData.ideal_finsetProd_eq_prod]
  refine Finset.prod_le_prod' fun i _ => ?_
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  exact Ideal.pow_le_pow_right (h i)

/-- Enlarging the index set past the exceptional set of an affine open does not change the partial
sum there. -/
theorem finsetProd_ideal_eq_of_forall_eq_top {ι : Type*} (D : ι → X.IdealSheafData) (n : ι → ℕ)
    (U : X.affineOpens) {t s : Finset ι} (ht : ∀ i ∉ t, (D i).ideal U = ⊤) (hts : t ⊆ s) :
    (∏ i ∈ s, D i ^ n i).ideal U = (∏ i ∈ t, D i ^ n i).ideal U := by
  classical
  rw [Scheme.IdealSheafData.ideal_finsetProd_eq_prod,
    Scheme.IdealSheafData.ideal_finsetProd_eq_prod]
  refine (Finset.prod_subset hts ?_).symm
  intro i _ hit
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, ht i hit, ← Ideal.one_eq_top, one_pow]

/-- The intersection of all the partial sums on an affine open is the partial sum over any finite
set of indices containing the exceptional set of that open. -/
theorem iInf_finsetProd_ideal {ι : Type*} (D : ι → X.IdealSheafData) (n : ι → ℕ)
    (U : X.affineOpens) {t : Finset ι} (ht : ∀ i ∉ t, (D i).ideal U = ⊤) :
    (⨅ s : Finset ι, (∏ i ∈ s, D i ^ n i).ideal U) = (∏ i ∈ t, D i ^ n i).ideal U := by
  classical
  refine le_antisymm (iInf_le _ t) (le_iInf fun s => ?_)
  calc (∏ i ∈ t, D i ^ n i).ideal U
      = (∏ i ∈ s ∪ t, D i ^ n i).ideal U :=
        (finsetProd_ideal_eq_of_forall_eq_top D n U ht Finset.subset_union_right).symm
    _ ≤ (∏ i ∈ s, D i ^ n i).ideal U :=
        finsetProd_ideal_le_of_subset D n U Finset.subset_union_left

/-- For a locally finite family, the intersection of the partial sums is compatible with
restriction to a basic open. -/
theorem map_iInf_finsetProd_ideal {ι : Type*} {D : ι → X.IdealSheafData}
    (hD : IsLocallyFiniteFamily D) (n : ι → ℕ) (U : X.affineOpens) (g : Γ(X, U.1)) :
    (⨅ s : Finset ι, (∏ i ∈ s, D i ^ n i).ideal U).map
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom =
      ⨅ s : Finset ι, (∏ i ∈ s, D i ^ n i).ideal (X.affineBasicOpen g) := by
  obtain ⟨t, ht⟩ := hD U
  rw [iInf_finsetProd_ideal D n U ht, iInf_finsetProd_ideal D n (X.affineBasicOpen g)
    (forall_ideal_eq_top_of_le (X.affineBasicOpen_le g) ht)]
  exact (∏ i ∈ t, D i ^ n i).map_ideal_basicOpen U g

/-! ### The sum -/

/-- **The sum `∑ nᵢ Dᵢ` of a locally finite family of divisors**, realized as the intersection of
all its finite partial sums. -/
def locallyFiniteSum {ι : Type*} (D : ι → X.IdealSheafData) (n : ι → ℕ) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U => ⨅ s : Finset ι, (∏ i ∈ s, D i ^ n i).ideal U

/-- **The sum is antitone in the multiplicities**: raising the `nᵢ` enlarges the divisor
`∑ nᵢ Dᵢ`, so its sheaf of ideals shrinks. -/
theorem locallyFiniteSum_antitone {ι : Type*} (D : ι → X.IdealSheafData) :
    Antitone (locallyFiniteSum D) := by
  intro n m h
  rw [locallyFiniteSum, locallyFiniteSum]
  refine Scheme.IdealSheafData.ofIdeals_mono fun U => ?_
  exact le_iInf fun s => (iInf_le _ s).trans (finsetProd_ideal_le_of_le D h U s)

/-- For a locally finite family, the sections of the sum on an affine open are the intersection of
the sections of the partial sums. -/
theorem locallyFiniteSum_ideal {ι : Type*} {D : ι → X.IdealSheafData}
    (hD : IsLocallyFiniteFamily D) (n : ι → ℕ) (U : X.affineOpens) :
    (locallyFiniteSum D n).ideal U = ⨅ s : Finset ι, (∏ i ∈ s, D i ^ n i).ideal U := by
  let J : X.IdealSheafData :=
    { ideal := fun V => ⨅ s : Finset ι, (∏ i ∈ s, D i ^ n i).ideal V
      map_ideal_basicOpen := fun V g => map_iInf_finsetProd_ideal hD n V g }
  have hJ : locallyFiniteSum D n = J := Scheme.IdealSheafData.ofIdeals_ideal J
  exact congrFun (congrArg Scheme.IdealSheafData.ideal hJ) U

/-- **On an affine open the sum is a finite sum.** It agrees with the partial sum over any finite
set of indices containing every index where the family is not the empty divisor there. -/
theorem locallyFiniteSum_ideal_eq_finsetProd {ι : Type*} {D : ι → X.IdealSheafData}
    (hD : IsLocallyFiniteFamily D) (n : ι → ℕ) (U : X.affineOpens) {t : Finset ι}
    (ht : ∀ i ∉ t, (D i).ideal U = ⊤) :
    (locallyFiniteSum D n).ideal U = (∏ i ∈ t, D i ^ n i).ideal U := by
  rw [locallyFiniteSum_ideal hD n U, iInf_finsetProd_ideal D n U ht]

/-- **The sum of a locally finite family of effective Cartier divisors is an effective Cartier
divisor.** -/
@[stacks 0ESU "the locally finite sum E_k = D_{k+1} + 2D_{k+2} + ⋯ is effective Cartier",
  ega "IV 21.2.7" "partial"]
theorem isEffectiveCartierDivisor_locallyFiniteSum {ι : Type*} {D : ι → X.IdealSheafData}
    (hD : IsLocallyFiniteFamily D) (hcart : ∀ i, IsEffectiveCartierDivisor (D i)) (n : ι → ℕ) :
    IsEffectiveCartierDivisor (locallyFiniteSum D n) := by
  classical
  refine isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  have hmem : x ∈ (⨆ V : X.affineOpens, (V : X.Opens)) := by
    rw [iSup_affineOpens_eq_top]; trivial
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  obtain ⟨t, ht⟩ := hD U
  obtain ⟨V, hV, hxV, f, hf, hJf⟩ :=
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor _
      (isEffectiveCartierDivisor_prod t D n fun i _ => hcart i) x
  obtain ⟨a, b, hab, hxW⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter U.2 hV x ⟨hxU, hxV⟩
  let V' : X.affineOpens := ⟨V, hV⟩
  let a' : Γ(X, U.1) := a
  let b' : Γ(X, V'.1) := b
  let W : X.affineOpens := X.affineBasicOpen a'
  have hWU : W ≤ U := X.affineBasicOpen_le a'
  have hWV : W.1 ≤ V'.1 := hab.trans_le (X.affineBasicOpen_le b')
  have hgoal : (locallyFiniteSum D n).ideal W =
      Ideal.span {(X.presheaf.map (homOfLE hWV).op).hom f} := by
    rw [locallyFiniteSum_ideal_eq_finsetProd hD n W (forall_ideal_eq_top_of_le hWU ht),
      ← (∏ i ∈ t, D i ^ n i).map_ideal hWV, hJf, Ideal.map_span, Set.image_singleton]
    rfl
  exact ⟨W.1, W.2, hxW, (X.presheaf.map (homOfLE hWV).op).hom f,
    isRegular_res_of_eq_basicOpen hWV b' f hab hf, hgoal⟩

/-! ### Cancellation: a sum determines its complementary summand -/

/-- **Cancelling a nonzerodivisor from a product of ideals.** If `(f) I = (f) J` for a
nonzerodivisor `f`, then `I = J`. -/
theorem eq_of_span_singleton_mul_eq {R : Type*} [CommRing R] {f : R}
    (hf : f ∈ nonZeroDivisors R) {I J : Ideal R}
    (h : Ideal.span {f} * I = Ideal.span {f} * J) : I = J := by
  have key : ∀ I' J' : Ideal R, Ideal.span {f} * I' = Ideal.span {f} * J' → I' ≤ J' := by
    intro I' J' h' x hx
    have hfx : f * x ∈ Ideal.span {f} * J' := by
      rw [← h']
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) hx
    obtain ⟨z, hz, hfz⟩ := Ideal.mem_span_singleton_mul.mp hfx
    have hzx : z = x := by
      have h0 : f * (z - x) = 0 := by rw [mul_sub, hfz, sub_self]
      exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hf).1 _ h0)
    exact hzx ▸ hz
  exact le_antisymm (key I J h) (key J I h.symm)

/-- **A sum of divisors determines its complementary summand, locally.** If `I * J = I * K`, then
`J` and `K` have the same defining ideal on every affine open on which `I` is cut out by a single
nonzerodivisor. -/
theorem ideal_eq_of_mul_eq_mul_of_ideal_eq_span {I J K : X.IdealSheafData} (h : I * J = I * K)
    (U : X.affineOpens) {f : Γ(X, U.1)} (hf : IsRegular f) (hIf : I.ideal U = Ideal.span {f}) :
    J.ideal U = K.ideal U := by
  have h' : (I * J).ideal U = (I * K).ideal U :=
    congrFun (congrArg Scheme.IdealSheafData.ideal h) U
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hIf] at h'
  exact eq_of_span_singleton_mul_eq (isRegular_iff_mem_nonZeroDivisors.mp hf) h'

/-! ### Ideals determined on basic opens -/

/-- **A quasi-coherent sheaf of ideals is determined on an affine open by its restrictions to
basic opens.** If around every point of an affine open `U` there is a basic open of `U` on which
`J` is contained in `K`, then `J.ideal U ≤ K.ideal U`. -/
theorem ideal_le_of_forall_exists_basicOpen {J K : X.IdealSheafData} (U : X.affineOpens)
    (h : ∀ x ∈ (U.1 : Set X), ∃ g : Γ(X, U.1), x ∈ X.basicOpen g ∧
      J.ideal (X.affineBasicOpen g) ≤ K.ideal (X.affineBasicOpen g)) :
    J.ideal U ≤ K.ideal U := by
  classical
  intro x hx
  let s : Set Γ(X, U.1) :=
    {g | J.ideal (X.affineBasicOpen g) ≤ K.ideal (X.affineBasicOpen g)}
  have hcover : (⨆ f : s, X.basicOpen (f : Γ(X, U.1))) = U.1 := by
    refine le_antisymm (iSup_le fun f => X.basicOpen_le _) fun y hy => ?_
    obtain ⟨g, hyg, hg⟩ := h y hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hyg⟩
  have hspan : Ideal.span s = ⊤ := U.2.iSup_basicOpen_eq_self_iff.mp hcover
  let C : Ideal Γ(X, U.1) :=
    Submodule.comap (LinearMap.toSpanSingleton Γ(X, U.1) Γ(X, U.1) x) (K.ideal U)
  have hmemC : ∀ c : Γ(X, U.1), c ∈ C ↔ c * x ∈ K.ideal U := by
    intro c
    show c • x ∈ K.ideal U ↔ c * x ∈ K.ideal U
    rw [smul_eq_mul]
  have hrad : ∀ g ∈ s, g ∈ C.radical := by
    intro g hg
    have hWU : X.affineBasicOpen g ≤ U := X.affineBasicOpen_le g
    let : Algebra Γ(X, U.1) Γ(X, (X.affineBasicOpen g).1) :=
      (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
    have : IsLocalization.Away g Γ(X, (X.affineBasicOpen g).1) :=
      U.2.isLocalization_of_eq_basicOpen g (homOfLE hWU) rfl
    have hJW : algebraMap Γ(X, U.1) Γ(X, (X.affineBasicOpen g).1) x ∈
        J.ideal (X.affineBasicOpen g) := by
      rw [← J.map_ideal_basicOpen U g]
      exact Ideal.mem_map_of_mem _ hx
    have hKW : algebraMap Γ(X, U.1) Γ(X, (X.affineBasicOpen g).1) x ∈
        Ideal.map (algebraMap Γ(X, U.1) Γ(X, (X.affineBasicOpen g).1)) (K.ideal U) := by
      rw [show Ideal.map (algebraMap Γ(X, U.1) Γ(X, (X.affineBasicOpen g).1)) (K.ideal U) =
        K.ideal (X.affineBasicOpen g) from K.map_ideal_basicOpen U g]
      exact hg hJW
    obtain ⟨p, hp⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g)
      Γ(X, (X.affineBasicOpen g).1)).mp hKW
    have hp' : algebraMap Γ(X, U.1) Γ(X, (X.affineBasicOpen g).1) (x * (p.2 : Γ(X, U.1))) =
        algebraMap Γ(X, U.1) Γ(X, (X.affineBasicOpen g).1) (p.1 : Γ(X, U.1)) := by
      rw [map_mul]; exact hp
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers g)
      Γ(X, (X.affineBasicOpen g).1)).mp hp'
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp (c * p.2).2
    refine ⟨n, (hmemC _).mpr ?_⟩
    have hgn : g ^ n * x = (c : Γ(X, U.1)) * (p.1 : Γ(X, U.1)) := by
      rw [hn]
      show ((c : Γ(X, U.1)) * (p.2 : Γ(X, U.1))) * x = _
      linear_combination hc
    rw [hgn]
    exact Ideal.mul_mem_left _ _ p.1.2
  have hle : Ideal.span s ≤ C.radical := Ideal.span_le.mpr hrad
  have hCtop : C = ⊤ := Ideal.radical_eq_top.mp (le_antisymm le_top (hspan ▸ hle))
  have h1 : (1 : Γ(X, U.1)) ∈ C := by rw [hCtop]; exact Submodule.mem_top
  simpa using (hmemC 1).mp h1

/-- **A quasi-coherent sheaf of ideals is determined by its restrictions to basic opens.** Two
sheaves of ideals agreeing around every point of an affine open, on a basic open of it, agree on
that affine open. -/
theorem ideal_eq_of_forall_exists_basicOpen {J K : X.IdealSheafData} (U : X.affineOpens)
    (h : ∀ x ∈ (U.1 : Set X), ∃ g : Γ(X, U.1), x ∈ X.basicOpen g ∧
      J.ideal (X.affineBasicOpen g) = K.ideal (X.affineBasicOpen g)) :
    J.ideal U = K.ideal U :=
  le_antisymm
    (ideal_le_of_forall_exists_basicOpen U fun x hx =>
      let ⟨g, hxg, hg⟩ := h x hx; ⟨g, hxg, hg.le⟩)
    (ideal_le_of_forall_exists_basicOpen U fun x hx =>
      let ⟨g, hxg, hg⟩ := h x hx; ⟨g, hxg, hg.ge⟩)

end Stacks.Divisors

end
