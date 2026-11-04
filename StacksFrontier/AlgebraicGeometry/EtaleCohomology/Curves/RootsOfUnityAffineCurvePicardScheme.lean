module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurveJacobian
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeZeroAbelianVariety
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapSurjective
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.Main
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 03RR from the degree-zero Picard scheme of the compactification

`AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian_of_isQuasiProjective`
proves the three clauses of [Stacks, Tag 03RR] for an affine smooth curve `X ⊆ X̄` from a Jacobian
of `X̄`. This file instantiates the Jacobian with `Pic⁰_{X̄/k}`,
`Stacks.PicardFunctor.picardDegreeZeroSubgroup`, whose rational points are `Pic⁰(X̄)`
(`Stacks.PicardFunctor.bijective_picardDegreeZeroPoints`).

## Main results

* `AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_picardScheme`: the three
  clauses of [Stacks, Tag 03RR], with the Picard functor of `X̄` representable, clause (1) of
  [Stacks, Tag 0BA0] for the degree-zero component (smooth, proper, integral, of dimension the
  genus), the quasi-projectivity of `Pic⁰_{X̄/k}` and the theorem of the cube for it as inputs.
* `AlgebraicGeometry.exists_bigFppfSite_picardData`: the big fppf site, rational point and
  geometric irreducibility needed to speak of the Picard scheme of `X̄`.

## Implementation notes

No `@[stacks 03RR]` attribute is placed here: the inputs listed above are arguments.

## References

* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe t u

namespace AlgebraicGeometry

open Stacks.PicardFunctor

section PicardScheme

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] (E : BigEtaleSite.{u}) (hX : E.Contains X) (n : ℕ)
  [HasExt.{t} (Sheaf (SmallEtale.topology E X hX) AddCommGrpCat.{u})]
  (B : BigFppfSite.{u}) {Xbar : Scheme.{u}} (hXb : B.Contains Xbar)
  (hk : B.Contains (Spec (.of k))) (fb : B.obj hXb ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ Xbar) (hσ : σ ≫ B.inclusion.map fb = 𝟙 (Spec (.of k)))
  [IsCurve k (B.inclusion.map fb)] [IsProjectiveVariety k (B.inclusion.map fb)]
  [Smooth (B.inclusion.map fb)] [GeometricallyIrreducible (B.inclusion.map fb)]
  [(picardFunctor B hXb hk fb).IsRepresentable]

include f in
/-- **The three clauses of [Stacks, Tag 03RR] from the degree-zero Picard scheme.** Let `X` be an
affine smooth curve over an algebraically closed field `k`, `n` invertible in `k`, and
`j : X ⟶ X̄` an open immersion into a smooth projective curve of genus `g`, with `r` points
outside `X`. If the Picard functor of `X̄` is representable, its degree-zero component is a
smooth proper integral scheme over `k` of dimension `g`, `Pic⁰_{X̄/k}` is quasi-projective and
satisfies the theorem of the cube, then `H⁰_ét(X, μ_n) = μ_n(k)`,
`H¹_ét(X, μ_n) ≅ (𝐙/n𝐙)^{2g+r-1}` and `H^q_ét(X, μ_n) = 0` for `q ≥ 2`. -/
@[sga "4 IX 4.6" "special case"]
theorem etaleCohomology_rootsOfUnity_affineSmoothCurve_of_picardScheme (hn : IsUnit (n : k))
    [IsAffine X] (j : X ⟶ Xbar) [IsOpenImmersion j] (hj : j ≫ B.inclusion.map fb = f)
    (r : ℕ) (hr : Nat.card ↥(Set.range j.base)ᶜ = r)
    (hproper : IsProper (B.inclusion.map (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).hom))
    (hsmooth : Smooth (B.inclusion.map (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).hom))
    (hint : IsIntegral (B.inclusion.obj (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).left))
    (hdim : Stacks.Groupoids.abelianVarietyDimension
        (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X = genus (B.inclusion.map fb))
    (hcube : Stacks.Groupoids.HasTheoremOfTheCube
      (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X)
    (hq : IsQuasiProjective (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X.hom) :
    Function.Bijective (baseRootsToEtaleH0 E k X hX f n) ∧
      Nonempty (Sheaf.H (kummerSmallEtale E X hX n).X₁ 1 ≃+
        (Fin (2 * genus (B.inclusion.map fb) + r - 1) → ZMod n)) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale E X hX n).X₁ q) :=
  etaleCohomology_rootsOfUnity_affineSmoothCurve_of_jacobian_of_isQuasiProjective k X f E hX n hn
    (B.inclusion.map fb) j hj r hr (picardDegreeZeroSubgroup B hXb hk fb σ hσ)
    (isProper_picardDegreeZeroSubgroup_carrier B hXb hk fb σ hσ hproper)
    (smooth_picardDegreeZeroSubgroup_carrier B hXb hk fb σ hσ hsmooth)
    (connectedSpace_picardDegreeZeroSubgroup_carrier B hXb hk fb σ hσ hint) hdim
    (picardDegreeZeroPoints B hXb hk fb σ hσ) (picardDegreeZeroPoints_mul B hXb hk fb σ hσ)
    (bijective_picardDegreeZeroPoints B hXb hk fb σ hσ) hcube hq

end PicardScheme

/-- **The data of the Picard scheme of a smooth projective curve over an algebraically closed
field.** There is a big fppf site containing `X̄` and `Spec k`, the structure morphism is a
morphism of it, the curve has a rational point, and it is geometrically irreducible. -/
theorem exists_bigFppfSite_picardData {k : Type u} [Field k] [IsAlgClosed k] {Xbar : Scheme.{u}}
    (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k fbar] [Smooth fbar] [IsProjectiveVariety k fbar] :
    ∃ (B : BigFppfSite.{u}) (hXb : B.Contains Xbar) (hk : B.Contains (Spec (.of k)))
      (fb : B.obj hXb ⟶ B.obj hk), B.inclusion.map fb = fbar ∧
      (∃ σ : Spec (.of k) ⟶ Xbar, σ ≫ fbar = 𝟙 _) ∧ GeometricallyIrreducible fbar := by
  have : Small.{u} ({Xbar, Spec (.of k)} : Set Scheme.{u}) := inferInstance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing ({Xbar, Spec (.of k)} : Set Scheme.{u})
  have hXb : B.Contains Xbar := hB _ (by simp)
  have hk : B.Contains (Spec (.of k)) := hB _ (by simp)
  have : Nonempty Xbar := inferInstance
  refine ⟨B, hXb, hk, B.inclusion.preimage (X := B.obj hXb) (Y := B.obj hk) fbar,
    B.inclusion.map_preimage _, Stacks.AbelMap.exists_section_of_isSepClosed fbar, ?_⟩
  exact geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k Xbar fbar

section Assembly

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] (E : BigEtaleSite.{u}) (hX : E.Contains X) (n : ℕ)
  [HasExt.{t} (Sheaf (SmallEtale.topology E X hX) AddCommGrpCat.{u})]

include f in
/-- **[Stacks, Tag 03RR] over the remaining inputs about the Picard scheme.** The statement of
record, `X ⊆ X̄` an affine smooth curve in its smooth projective compactification over an
algebraically closed field, with the facts about the Picard scheme of `X̄` that are not yet
available collected in `hinp`: for every big fppf site carrying `X̄ ⟶ Spec k` and every rational
point, the Picard functor is representable, its degree-zero component is smooth, proper, integral
and of dimension the genus (clause (1) of [Stacks, Tag 0BA0]). Quasi-projectivity of
`Pic⁰_{X̄/k}` is [Stacks, Tag 0BF7] and the theorem of the cube for it is
`Stacks.Cube.hasTheoremOfTheCube`. -/
@[sga "4 IX 4.6" "special case"]
theorem etaleCohomology_rootsOfUnity_affineSmoothCurve_of_picardInputs (hn : IsUnit (n : k))
    [IsAffine X] {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k fbar] [Smooth fbar]
    [IsProjectiveVariety k fbar] (j : X ⟶ Xbar) [IsOpenImmersion j] (hj : j ≫ fbar = f)
    (r : ℕ) (hr : Nat.card ↥(Set.range j.base)ᶜ = r)
    (hinp : ∀ (B : BigFppfSite.{u}) (hXb : B.Contains Xbar) (hk : B.Contains (Spec (.of k)))
      (fb : B.obj hXb ⟶ B.obj hk) (σ : Spec (.of k) ⟶ Xbar)
      (hσ : σ ≫ B.inclusion.map fb = 𝟙 (Spec (.of k))) [IsCurve k (B.inclusion.map fb)]
      [IsProjectiveVariety k (B.inclusion.map fb)] [Smooth (B.inclusion.map fb)]
      [GeometricallyIrreducible (B.inclusion.map fb)],
      ∃ _ : (picardFunctor B hXb hk fb).IsRepresentable,
        IsProper (B.inclusion.map (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).hom) ∧
        Smooth (B.inclusion.map (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).hom) ∧
        IsIntegral (B.inclusion.obj (picardSchemeDegreeComponent B hXb hk fb σ hσ 0).left) ∧
        Stacks.Groupoids.abelianVarietyDimension
          (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X = genus (B.inclusion.map fb)) :
    Function.Bijective (baseRootsToEtaleH0 E k X hX f n) ∧
      Nonempty (Sheaf.H (kummerSmallEtale E X hX n).X₁ 1 ≃+
        (Fin (2 * genus fbar + r - 1) → ZMod n)) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale E X hX n).X₁ q) := by
  obtain ⟨B, hXb, hk, fb, hfb, ⟨σ, hσ⟩, hgi⟩ := exists_bigFppfSite_picardData fbar
  subst hfb
  obtain ⟨hrep, hproper, hsmooth, hint, hdim⟩ := hinp B hXb hk fb σ hσ
  have hq : IsQuasiProjective (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X.hom := by
    have := smooth_picardDegreeZeroSubgroup_carrier B hXb hk fb σ hσ hsmooth
    have := isProper_picardDegreeZeroSubgroup_carrier B hXb hk fb σ hσ hproper
    exact isQuasiProjective_of_groupScheme_over_field _
  have := isAbelianVariety_picardDegreeZero B hXb hk fb σ hσ hproper hsmooth hint
  exact etaleCohomology_rootsOfUnity_affineSmoothCurve_of_picardScheme k X f E hX n B hXb hk fb σ hσ
    hn j hj r hr hproper hsmooth hint hdim Stacks.Cube.hasTheoremOfTheCube hq

end Assembly

end AlgebraicGeometry

end
