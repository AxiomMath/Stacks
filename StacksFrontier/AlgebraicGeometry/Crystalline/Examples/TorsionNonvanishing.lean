module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionDegreeZero
public import StacksFrontier.RingTheory.DividedPowers.TorsionWitnessRing

/-!
# The torsion element of [Stacks, Tag 07LJ] is nonzero

In the setting of `StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionDegreeZero` — the
base `(A, I, γ) = (ℤ_[p], (p), γ)`, the ring `C = 𝐅_p[x, y]/(x², xy, y²)` presented as
`C = P/J = ℤ_[p][x, y]/(p, x², xy, y²)`, the `p`-adically completed divided power envelope
`D = D_{P, γ}(J)^∧` with divided powers `γ̄`, and the element
`τ = γ̄_p(x²) γ̄_p(y²) − γ̄_p(xy)² ∈ D` — this module proves the last claim the source makes
about `τ` before drawing its conclusions:

`τ ≠ 0`.

The proof is the source's own.  It produces a divided power thickening `(B, K, δ)` of `C` over
the base, maps `D` to it, and computes that `τ` has nonzero image.  The thickening is the one
built in `StacksFrontier.RingTheory.DividedPowers.TorsionWitnessRing`.

## Main definitions

* `Crystalline.TorsionExample.witnessRing` is the explicit thickening `(B, K, δ)` of
  [Stacks, Tag 07LJ], packaged as a divided power ring.
* `Crystalline.TorsionExample.toWitnessRing` is the divided power morphism
  `D_{P, γ}(J) → B` that the universal property of the divided power envelope produces from the
  presentation `P → B`.

## Main results

* `Crystalline.TorsionExample.toWitnessRing_envelopeTau` — the image of the envelope-level
  element `γ_p(x²) γ_p(y²) − γ_p(xy)²` in `B` is `u v`.
* `Crystalline.TorsionExample.envelopeTau_ne_zero` — that element is nonzero in the envelope.
* `Crystalline.TorsionExample.tau_ne_zero` — **`τ ≠ 0` in `D`.**

## Implementation notes

Two steps have to be taken care of beyond the universal property.

First, `τ` lives in the *completed* envelope `D`, and the morphism produced by the universal
property goes out of the envelope itself.  The gap is closed without constructing any map out of
`D`: the prime `p` is zero in `B`, so if `τ` were zero then `envelopeTau` would lie in
`p · D_{P, γ}(J)` — that is what vanishing of the first level of the `p`-adic completion says —
and the image of `p · D_{P, γ}(J)` in `B` is zero, contradicting `u v ≠ 0`.

Second, `τ` is built from `γ̄_p`, the completed divided powers, while the computation happens
with `γ_p` in the envelope; `tau_eq_algebraMap_envelopeTau` of the setup module is exactly the
identification needed.

## The prime two

The operation `δ_p(a x² + b xy + c y² + d u + e v + f uv) = a^p u + c^p v` that the source puts
on `K` satisfies hypothesis (3) of [Stacks, Tag 07GS] only for odd `p`.  That is an erratum to
the source, and it is repaired rather than inherited: the divided powers used here are
`DividedPowers.TorsionWitness.dividedPowers`, which at `p = 2` adds to `δ_p` the quadratic term
whose polarisation is the surviving cross term, and which still sends `x²` to `u` and `y²` to
`v`.  Both statements below therefore hold at every prime, as in the source.

## The covering set of [Stacks, Tag 07LJ]

Two of its members live here, `toWitnessRing_envelopeTau` and `tau_ne_zero`.  The full table is
in the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.TorsionDegreeZero`.

## References

* [Stacks Project, Tag 07LJ](https://stacks.math.columbia.edu/tag/07LJ)
* [Stacks Project, Tag 07GS](https://stacks.math.columbia.edu/tag/07GS)
* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
-/

@[expose] public section

namespace Crystalline

namespace TorsionExample

open DividedPowers.TorsionWitness

variable (p : ℕ) [Fact p.Prime]

/-- The explicit divided power thickening `(B, K, δ)` of [Stacks, Tag 07LJ], packaged as a
divided power ring. -/
noncomputable abbrev witnessRing : DividedPowerRing :=
  DividedPowerRing.of (Witness p) (K p) (dividedPowers p)

/-- The structural divided power morphism from the base `(ℤ_[p], (p), γ)` to the witness
thickening. -/
noncomputable def witnessStructureMap :
    DividedPowers.DPMorphism (base p).dividedPowers (witnessRing p).dividedPowers :=
  DividedPowers.DPMorphism.mk' (isDPMorphism_toWitness p)

/-- The presentation `P = ℤ_[p][x, y] → B` as a morphism of ring--ideal pairs
`(P, J) → (B, K)`: the generators `p`, `x²`, `xy`, `y²` of `J` go to `0`, `x²`, `0`, `y²`, all of
which lie in `K`. -/
noncomputable def witnessPresentation :
    IdealPair.Hom (relations p) (witnessRing p).ideal :=
  IdealPair.Hom.ofRingHom (mvPolynomialHom p) (by
    have hrel : relations p = Ideal.span ({(p : polynomial p), polynomialX p ^ 2,
        polynomialX p * polynomialY p, polynomialY p ^ 2} : Set (polynomial p)) := rfl
    rw [hrel, Ideal.map_span, Ideal.span_le]
    rintro z ⟨w, hw, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    change (mvPolynomialHom p) w ∈ K p
    obtain rfl | rfl | rfl | rfl := hw
    · rw [map_natCast, DividedPowers.TorsionWitness.natCast_eq_zero]
      exact (K p).zero_mem
    · rw [map_pow, mvPolynomialHom_X_zero]
      exact x_sq_mem p
    · rw [map_mul, mvPolynomialHom_X_zero, mvPolynomialHom_X_one, x_mul_y_eq_zero]
      exact (K p).zero_mem
    · rw [map_pow, mvPolynomialHom_X_one]
      exact y_sq_mem p)

/-- The presentation `P → B` restricts on the base to the structural map, which is the
compatibility the universal property of the divided power envelope asks for. -/
theorem witnessPresentation_comp :
    IdealPair.Hom.comp (witnessPresentation p)
        (IdealPair.Hom.ofRingHom (algebraMap (base p) (polynomial p))
          (baseIdeal_le_relations p)) =
      IdealPair.Hom.ofDPMorphism (witnessStructureMap p) :=
  IdealPair.Hom.ext_toRingHom _ _ (mvPolynomialHom_comp_C p)

/-- The divided power morphism `D_{P, γ}(J) → B` produced by the universal property of the
divided power envelope from the presentation `P → B`. -/
noncomputable def toWitnessRing :
    DividedPowers.DPMorphism (envelope p).object.dividedPowers
      (witnessRing p).dividedPowers :=
  (((envelope p).homEquiv (witnessRing p) (witnessStructureMap p)).symm
    ⟨witnessPresentation p, witnessPresentation_comp p⟩).1

/-- The morphism `D_{P, γ}(J) → B` extends the presentation `P → B` along the canonical map from
`P` to the envelope.  This is the content of the universal property's characterisation. -/
theorem toWitnessRing_algebraMap (f : polynomial p) :
    toWitnessRing p ((envelope p).algebraMap.toRingHom f) = mvPolynomialHom p f := by
  have hq : ((envelope p).homEquiv (witnessRing p) (witnessStructureMap p))
      (((envelope p).homEquiv (witnessRing p) (witnessStructureMap p)).symm
        ⟨witnessPresentation p, witnessPresentation_comp p⟩) =
      ⟨witnessPresentation p, witnessPresentation_comp p⟩ :=
    Equiv.apply_symm_apply _ _
  have h := (envelope p).homEquiv_apply (witnessRing p) (witnessStructureMap p)
    (((envelope p).homEquiv (witnessRing p) (witnessStructureMap p)).symm
      ⟨witnessPresentation p, witnessPresentation_comp p⟩)
  rw [hq] at h
  exact (congrArg (fun g : IdealPair.Hom (relations p) (witnessRing p).ideal ↦
    g.toRingHom f) h).symm

/-- The image of `x` in `B` is the witness variable `x`. -/
theorem toWitnessRing_envelopeX :
    toWitnessRing p (envelopeX p) = x p := by
  rw [envelopeX, toWitnessRing_algebraMap, mvPolynomialHom_X_zero]

/-- The image of `y` in `B` is the witness variable `y`. -/
theorem toWitnessRing_envelopeY :
    toWitnessRing p (envelopeY p) = y p := by
  rw [envelopeY, toWitnessRing_algebraMap, mvPolynomialHom_X_one]

/-- The morphism `D_{P, γ}(J) → B` sends `γ_p(a)` to `δ_p(b)` whenever `a ∈ J̄` maps to `b`. -/
private theorem toWitnessRing_dpow_eq {a : (envelope p).object} {b : Witness p}
    (ha : a ∈ (envelope p).object.ideal) (hb : (toWitnessRing p).toRingHom a = b) :
    (toWitnessRing p).toRingHom ((envelope p).object.dividedPowers.dpow p a) =
      (dividedPowers p).dpow p b := by
  rw [← (toWitnessRing p).dpow_comp _ ha, hb]

/-- The image in `B` of `γ_p(x²)` is `u`: the morphism commutes with the divided powers, and
`δ_p(x²) = u`. -/
theorem toWitnessRing_dpow_envelopeX_sq :
    (toWitnessRing p).toRingHom
        ((envelope p).object.dividedPowers.dpow p (envelopeX p ^ 2)) = u p :=
  (toWitnessRing_dpow_eq p (envelopeX_sq_mem p)
    (by rw [map_pow]; exact congrArg (· ^ 2) (toWitnessRing_envelopeX p))).trans
    (dividedPowers_dpow_x_sq p)

/-- The image in `B` of `γ_p(y²)` is `v`. -/
theorem toWitnessRing_dpow_envelopeY_sq :
    (toWitnessRing p).toRingHom
        ((envelope p).object.dividedPowers.dpow p (envelopeY p ^ 2)) = v p :=
  (toWitnessRing_dpow_eq p (envelopeY_sq_mem p)
    (by rw [map_pow]; exact congrArg (· ^ 2) (toWitnessRing_envelopeY p))).trans
    (dividedPowers_dpow_y_sq p)

/-- The image in `B` of `γ_p(xy)` is `0`, because `xy` is already `0` in `B`. -/
theorem toWitnessRing_dpow_envelopeX_mul_envelopeY :
    (toWitnessRing p).toRingHom
        ((envelope p).object.dividedPowers.dpow p (envelopeX p * envelopeY p)) = 0 := by
  have hp : p.Prime := Fact.out
  rw [toWitnessRing_dpow_eq p (envelopeX_mul_envelopeY_mem p) (b := 0)]
  · exact (dividedPowers p).dpow_eval_zero hp.ne_zero
  · rw [map_mul]
    exact (congrArg₂ (· * ·) (toWitnessRing_envelopeX p) (toWitnessRing_envelopeY p)).trans
      (x_mul_y_eq_zero p)

/-- **The computation of [Stacks, Tag 07LJ].**  The element
`γ_p(x²) γ_p(y²) − γ_p(xy)²` of the divided power envelope has image `u v` in the witness
thickening `B`. -/
@[stacks 07LJ "the example's computation inside its witness thickening: the divided power \
morphism D_{P, γ}(J) -> B out of the universal property of the envelope sends \
γ_p(x^2) γ_p(y^2) - γ_p(xy)^2 to uv, which is nonzero in B (u_mul_v_ne_zero of \
RingTheory.DividedPowers.TorsionWitnessRing), at every prime p"]
theorem toWitnessRing_envelopeTau :
    (toWitnessRing p).toRingHom (envelopeTau p) = u p * v p := by
  rw [envelopeTau, map_sub, map_mul, map_pow, toWitnessRing_dpow_envelopeX_sq,
    toWitnessRing_dpow_envelopeY_sq, toWitnessRing_dpow_envelopeX_mul_envelopeY,
    zero_pow two_ne_zero, sub_zero]

/-- The envelope-level element `γ_p(x²) γ_p(y²) − γ_p(xy)²` is nonzero, since its image in the
witness thickening is `u v ≠ 0`. -/
theorem envelopeTau_ne_zero : envelopeTau p ≠ 0 := by
  intro hzero
  have h : (toWitnessRing p).toRingHom (envelopeTau p) = 0 := by rw [hzero, map_zero]
  rw [toWitnessRing_envelopeTau] at h
  exact u_mul_v_ne_zero p h

/-- **`τ ≠ 0` in `D`**, the last claim of [Stacks, Tag 07LJ] about `τ`.

Were `τ` zero, its first level in the `p`-adic completion would vanish, so the envelope-level
element `envelopeTau` would be a multiple of `p`.  Its image in the witness thickening `B` would
then be zero, `p` being zero in `B`; but that image is `u v ≠ 0`. -/
@[stacks 07LJ "the example's claim that τ ≠ 0 in D, at every prime p, by the source's own \
witness thickening B = F_p[x, y, u, v]/(x^3, x^2 y, x y^2, y^3, xu, yu, xv, yv, u^2, v^2) with \
the divided powers of DividedPowers.TorsionWitness on K = ker(B -> C), which send x^2 to u and \
y^2 to v, in which τ maps to uv ≠ 0, so that the first level of the p-adic completion already \
sees τ"]
theorem tau_ne_zero : tau p ≠ 0 := by
  intro hzero
  have hof : tau p =
      AdicCompletion.of (DividedPowers.pAdicIdeal (A := (envelope p).object) p)
        (envelope p).object (envelopeTau p) := by
    rw [tau_eq_algebraMap_envelopeTau]
    rfl
  have heval := congrArg
    (AdicCompletion.eval (DividedPowers.pAdicIdeal (A := (envelope p).object) p)
      (envelope p).object 1) hof
  rw [hzero, map_zero, AdicCompletion.eval_of] at heval
  have hmem : envelopeTau p ∈
      DividedPowers.pAdicIdeal (A := (envelope p).object) p ^ 1 •
        (⊤ : Submodule (envelope p).object (envelope p).object) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact heval.symm
  rw [pow_one, DividedPowers.pAdicIdeal, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨w, -, hw⟩ := hmem
  have himage : (toWitnessRing p).toRingHom (envelopeTau p) = 0 := by
    rw [← hw, smul_eq_mul, map_mul, map_natCast,
      DividedPowers.TorsionWitness.natCast_eq_zero, zero_mul]
  rw [toWitnessRing_envelopeTau] at himage
  exact u_mul_v_ne_zero p himage

end TorsionExample

end Crystalline

end
