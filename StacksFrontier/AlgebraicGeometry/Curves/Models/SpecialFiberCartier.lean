module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberLocalEquation
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksCore.Tactic.StacksAttribute

/-!
# The special fibre of a flat scheme over a discrete valuation ring is Cartier

Let `R` be a discrete valuation ring with uniformizer `π` and let `f : X ⟶ Spec(R)` be flat.
The scheme-theoretic special fibre of `f`, that is the closed subscheme of `X` cut out by the
kernel of the first projection from `X ×_{Spec R} Spec(k)`, is an effective Cartier divisor on
`X`.

The argument is the affine-local criterion for an effective Cartier divisor: on an affine chart
`Spec A ⊆ X` the image of `π` is a nonzerodivisor of `A`, because flatness makes `π` act
regularly, and the chart's part of the special fibre is `Spec(A/πA)`. Both of those are the
content of `Stacks.Models.map_mem_nonZeroDivisors_of_flat` and
`Stacks.Models.specialFiberAffineOpenIso`.

In particular this applies to the regular model of a smooth curve of
`Stacks.Models.RegularModelSituation`; neither regularity nor the generic fibre is used.

## Main results

* `Stacks.Models.isEffectiveCartierDivisor_specialFiber` — the special fibre of a flat scheme
  over a discrete valuation ring is an effective Cartier divisor.

## Implementation notes

The residue field is taken to be any field `k` together with an identification of it with
`IsLocalRing.ResidueField R` as an `R`-algebra, matching the data carried by
`Stacks.Models.RegularModelSituation`; the identification enters the proof through the
comparison of `Spec(k)` with `Spec(R/(π))`, which is what makes the special fibre the zero
scheme of the uniformizer.

## References

* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open Stacks.Divisors

namespace Stacks.Models

universe u

/-- **Stacks Project, Tag 0C5Z.** The scheme-theoretic special fibre of a scheme flat over a
discrete valuation ring is an effective Cartier divisor: on every affine chart it is the zero
scheme of the image of a uniformizer, which flatness keeps a nonzerodivisor. -/
@[stacks 0C5Z "special_fibre_cartier"]
public theorem isEffectiveCartierDivisor_specialFiber
    {R k : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field k] [Algebra R k]
    (residueEquiv : IsLocalRing.ResidueField R ≃ₐ[R] k)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f] :
    IsEffectiveCartierDivisor
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).ker := by
  let g : Spec (.of k) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let I : X.IdealSheafData := (pullback.fst f g).ker
  rw [isEffectiveCartierDivisor_iff_affineLocal]
  intro x _
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  let φ := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    f.appLE (⊤ : (Spec (.of R)).Opens) U (by simp)
  let _ : Algebra R Γ(X, U) := φ.hom.toAlgebra
  have hj : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
    change hU.fromSpec ≫ f = Spec.map φ
    dsimp [φ]
    rw [Spec.map_comp]
    simpa [Scheme.isoSpec_Spec_inv, IsAffineOpen.fromSpec_top] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU (by simp)).symm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let J := Ideal.span ({π} : Set R)
  let E : (R ⧸ J) ≃ₐ[R] k :=
    (Ideal.quotientEquivAlgOfEq R hπ.maximalIdeal_eq.symm).trans residueEquiv
  let q : Spec (.of (R ⧸ J)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let eSpec : Spec (.of k) ≅ Spec (.of (R ⧸ J)) :=
    Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.op
  have hg : g = eSpec.hom ≫ q := by
    have hmap : algebraMap R k = E.toAlgHom.toRingHom.comp (Ideal.Quotient.mk J) :=
      RingHom.ext fun r ↦ (E.commutes r).symm
    change Spec.map (CommRingCat.ofHom (algebraMap R k)) = _
    rw [show eSpec.hom = Spec.map (CommRingCat.ofHom E.toAlgHom.toRingHom) by
      simp [eSpec, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map], ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    exact congrArg (fun ψ ↦ Spec.map (CommRingCat.ofHom ψ)) hmap
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion g := by rw [hg]; infer_instance
  let pIso : pullback f g ≅ I.subscheme := asIso (pullback.fst f g).toImage
  let pbMap := pullback.map f g f q (𝟙 X) eSpec.hom (𝟙 (Spec (.of R))) (by simp) hg
  let _ : IsIso pbMap :=
    pullback.map_isIso f g f q (𝟙 X) eSpec.hom (𝟙 (Spec (.of R))) (by simp) hg
  let fibreIso : I.subscheme ≅ pullback f q := pIso.symm ≪≫ asIso pbMap
  have hfibre : fibreIso.hom ≫ pullback.fst f q = I.subschemeι := by
    have hpmap : pbMap ≫ pullback.fst f q = pullback.fst f g := by
      dsimp [pbMap, pullback.map]
      rw [pullback.lift_fst]
      simp
    change pIso.symm.hom ≫ pbMap ≫ pullback.fst f q = I.subschemeι
    rw [hpmap, ← Scheme.Hom.toImage_imageι (f := pullback.fst f g)]
    simp [pIso, I]
  refine ⟨U, hU, hxU, algebraMap R Γ(X, U) π,
    isRegular_iff_mem_nonZeroDivisors.2 ?_, ?_⟩
  · exact map_mem_nonZeroDivisors_of_flat π (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero) f
      hU.fromSpec hj
  · let fibreChart : pullback I.subschemeι U.ι ≅ pullback (hU.fromSpec ≫ f) q := by
      let i₁ := pullback.map I.subschemeι U.ι (pullback.fst f q) U.ι fibreIso.hom
        (𝟙 U.toScheme) (𝟙 X) (by simpa using hfibre.symm) (by simp)
      let i₂ := pullback.map (U.ι ≫ f) q (hU.fromSpec ≫ f) q hU.isoSpec.hom
        (𝟙 (Spec (.of (R ⧸ J)))) (𝟙 (Spec (.of R))) (by simp) (by simp)
      exact asIso i₁ ≪≫ pullbackSymmetry (pullback.fst f q) U.ι ≪≫
        pullbackRightPullbackFstIso f q U.ι ≪≫ asIso i₂
    have hchart : fibreChart.hom ≫ pullback.fst (hU.fromSpec ≫ f) q =
        pullback.snd I.subschemeι U.ι ≫ hU.isoSpec.hom := by
      simp only [fibreChart, Iso.trans_hom, asIso_hom, Category.assoc, pullback.map]
      simp only [← Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullbackSymmetry_hom_comp_fst, pullbackRightPullbackFstIso_hom_fst, Category.comp_id]
    refine ⟨fibreChart ≪≫ specialFiberAffineOpenIso π f hU.fromSpec hj, ?_⟩
    simpa [q, J, Category.assoc, specialFiberAffineOpenIso_hom_fst π f hU.fromSpec hj] using
      hchart.symm

end Stacks.Models

end
