module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.DualClosedPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.CotangentSpace
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety

/-!
# The standard affine chart of a projective space at a nonzero vector

Let `W` be a vector space over a field `k` and `w₀ ∈ W` a vector. The degree-one element
`w₀` of `Sym_k(W)` cuts out the standard open `D₊(w₀)` of `𝐏(W) = Proj (Sym_k W)`, which is the
spectrum of the degree-zero homogeneous localization `Sym_k(W)_(w₀)`; this file records that
chart in the form the family of projective transformations over a line needs:

* the open immersion `Spec Sym_k(W)_(w₀) ⟶ 𝐏(W)` lies over `Spec k`;
* the affine coordinates `w / w₀` are `k`-linear in `w`, and `w₀ / w₀ = 1`;
* **a `k`-point of the chart lying over the closed point `[μ]` of `𝐏(W)` cut out by a nonzero
  functional `μ` takes the value `μ(w) / μ(w₀)` on the coordinate `w / w₀`.**

The last statement is what identifies the specialisation of a family of endomorphisms written
in the affine coordinates with the endomorphism attached to `μ`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartRing`: the ring `Sym_k(W)_(w₀)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartι`: the chart `Spec Sym_k(W)_(w₀) ⟶ 𝐏(W)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartCoord`: the affine coordinate `w / w₀`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartι_comp_toSpec`: the chart lies over `Spec k`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartCoord_mem_iff`: a coordinate lies in the prime
  of a point of the chart exactly when the degree-one form lies in the image point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.apply_chartCoord_mul`: the value of a `k`-point on
  the affine coordinates.

## References

* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace HomogeneousLocalization

universe u

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

variable (k : Type u) [Field k] (W : Type u) [AddCommGroup W] [Module k W]

/-- **The coordinate ring of the standard chart at `w₀`**, the degree-zero homogeneous
localization of `Sym_k(W)` at the degree-one element `w₀`. -/
public abbrev chartRing (w₀ : W) : Type u :=
  HomogeneousLocalization.Away (fun n => SymPow.symmetricPower n k W) (SymmetricAlgebra.ι k W w₀)

/-- **The standard chart at `w₀`**, the open immersion `Spec Sym_k(W)_(w₀) ⟶ 𝐏(W)` onto the
standard open `D₊(w₀)`. -/
public def chartι (w₀ : W) : Spec (.of (chartRing k W w₀)) ⟶ projectiveSpaceOfModule k W :=
  Proj.awayι (fun n => SymPow.symmetricPower n k W) (SymmetricAlgebra.ι k W w₀)
    (ι_mem_symmetricPower_one k W w₀) Nat.one_pos

/-- The standard chart at `w₀` is an open immersion. -/
public instance isOpenImmersion_chartι (w₀ : W) : IsOpenImmersion (chartι k W w₀) := by
  unfold chartι
  infer_instance

/-- **The affine coordinate `w / w₀`** on the chart at `w₀`. -/
public def chartCoord (w₀ w : W) : chartRing k W w₀ :=
  HomogeneousLocalization.Away.isLocalizationElem (ι_mem_symmetricPower_one k W w₀)
    (ι_mem_symmetricPower_one k W w)

/-- The affine coordinate `w / w₀`, read in the localization of `Sym_k(W)` at the powers of
`w₀`, is the fraction `w / w₀`. -/
public theorem val_chartCoord (w₀ w : W) :
    (chartCoord k W w₀ w).val =
      Localization.mk (SymmetricAlgebra.ι k W w)
        ⟨SymmetricAlgebra.ι k W w₀, Submonoid.mem_powers _⟩ := by
  rw [chartCoord, HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk]
  simp only [pow_one]

/-- The affine coordinate `w / w₀` is additive in `w`. -/
public theorem chartCoord_add (w₀ w w' : W) :
    chartCoord k W w₀ (w + w') = chartCoord k W w₀ w + chartCoord k W w₀ w' := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_add, val_chartCoord, val_chartCoord, val_chartCoord, map_add,
    Localization.add_mk_self]

/-- The affine coordinate `w / w₀` is `k`-linear in `w`: a scalar comes out through
`algebraMap k (chartRing k W w₀)`. -/
public theorem chartCoord_smul (w₀ : W) (c : k) (w : W) :
    chartCoord k W w₀ (c • w) = algebraMap k (chartRing k W w₀) c * chartCoord k W w₀ w := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, val_chartCoord, val_chartCoord,
    val_algebraMap_homogeneousLocalization, Localization.mk_mul, one_mul, map_smul,
    Algebra.smul_def]

/-- The affine coordinate `w / w₀` commutes with subtraction in `w`. -/
public theorem chartCoord_sub (w₀ w w' : W) :
    chartCoord k W w₀ (w - w') = chartCoord k W w₀ w - chartCoord k W w₀ w' := by
  rw [eq_sub_iff_add_eq, ← chartCoord_add, sub_add_cancel]

/-- The affine coordinate `w₀ / w₀` is `1`. -/
public theorem chartCoord_self (w₀ : W) : chartCoord k W w₀ w₀ = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [val_chartCoord, HomogeneousLocalization.val_one]
  exact Localization.mk_self (⟨SymmetricAlgebra.ι k W w₀, Submonoid.mem_powers _⟩ :
    Submonoid.powers (SymmetricAlgebra.ι k W w₀))

/-- **The chart lies over `Spec k`.** -/
@[reassoc]
public theorem chartι_comp_toSpec (w₀ : W) :
    chartι k W w₀ ≫ projectiveSpaceOfModuleToSpec k W =
      Spec.map (CommRingCat.ofHom (algebraMap k (chartRing k W w₀))) := by
  rw [chartι, projectiveSpaceOfModuleToSpec, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- **The image of the chart is the standard open `D₊(w₀)`.** -/
public theorem range_chartι (w₀ : W) :
    Set.range (chartι k W w₀).base =
      {x | SymmetricAlgebra.ι k W w₀ ∉ x.asHomogeneousIdeal} := by
  have h := Proj.opensRange_awayι (fun n => SymPow.symmetricPower n k W)
    (SymmetricAlgebra.ι k W w₀) (ι_mem_symmetricPower_one k W w₀) Nat.one_pos
  ext x
  have hx := congrArg (fun U : (projectiveSpaceOfModule k W).Opens => x ∈ U) h
  simp only [Scheme.Hom.mem_opensRange, Proj.mem_basicOpen] at hx
  exact Iff.of_eq hx

/-- **A coordinate lies in the prime of a point of the chart exactly when the degree-one form
lies in the image point.** -/
public theorem chartCoord_mem_iff (w₀ w : W) (p : Spec (.of (chartRing k W w₀))) :
    chartCoord k W w₀ w ∈ p.asIdeal ↔
      SymmetricAlgebra.ι k W w ∈ ((chartι k W w₀).base p).asHomogeneousIdeal := by
  have h := Proj.awayι_preimage_basicOpen (fun n => SymPow.symmetricPower n k W)
    (ι_mem_symmetricPower_one k W w₀) Nat.one_pos (ι_mem_symmetricPower_one k W w) Nat.one_pos
  have hp := congrArg (fun U : (Spec (.of (chartRing k W w₀))).Opens => p ∈ U) h
  simp only [Scheme.Hom.mem_preimage, Proj.mem_basicOpen] at hp
  rw [← not_iff_not]
  exact (Iff.of_eq hp).symm

variable {k W}

/-- **The value of a `k`-point of the chart on the affine coordinates.** If a `k`-algebra map
`χ : Sym_k(W)_(w₀) → k` names a point of the chart lying over the closed point `[μ]` cut out by a
nonzero functional `μ`, then `χ(w / w₀) · μ(w₀) = μ(w)` for every `w`. -/
public theorem apply_chartCoord_mul {w₀ : W} (χ : chartRing k W w₀ →ₐ[k] k)
    {μ : Module.Dual k W} (hμ : μ ≠ 0) (x : Spec (.of k))
    (hx : (chartι k W w₀).base ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base x) =
      linearFunctionalPoint k W μ hμ) (w : W) :
    χ (chartCoord k W w₀ w) * μ w₀ = μ w := by
  -- the prime of the point is the kernel of `χ`
  have hker : ∀ y : chartRing k W w₀,
      y ∈ ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base x).asIdeal ↔ χ y = 0 := by
    intro y
    have hx0 : x.asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top x.asIdeal).resolve_right x.isPrime.ne_top
    rw [Spec.map_base]
    show y ∈ Ideal.comap χ.toRingHom x.asIdeal ↔ _
    rw [hx0, Ideal.mem_comap, Ideal.mem_bot]
    rfl
  have hzero : ∀ w' : W, μ w' = 0 → χ (chartCoord k W w₀ w') = 0 := by
    intro w' hw'
    rwa [← hker, chartCoord_mem_iff, hx, linearFunctionalPoint_ι_mem]
  set w' : W := μ w₀ • w - μ w • w₀ with hw'
  have hμw' : μ w' = 0 := by
    rw [hw', map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm, sub_self]
  have h := hzero w' hμw'
  rw [hw', chartCoord_sub, chartCoord_smul, chartCoord_smul, chartCoord_self, map_sub,
    _root_.map_mul, _root_.map_mul, AlgHom.commutes, AlgHom.commutes, _root_.map_one, mul_one,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, sub_eq_zero] at h
  rwa [mul_comm]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
