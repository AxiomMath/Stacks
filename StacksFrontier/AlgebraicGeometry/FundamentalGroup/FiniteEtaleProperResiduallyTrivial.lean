module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLimit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.StrictlyHenselianClosedGeometricFibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite étale covers do not change under a residually trivial henselian extension

Let `R ⟶ A` be a local homomorphism of henselian local rings which induces a *bijection* of
residue fields, and let `π : Y ⟶ Spec R` be proper. Then base change along the projection
`Y_A ⟶ Y` is an equivalence on finite étale covers: a finite étale cover of `Y_A` descends,
uniquely up to isomorphism, to one of `Y`.

Both sides are compared with the closed fibre. By [Stacks, Tag 0A48]
(`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing`) base
change to the closed fibre is an equivalence for a proper scheme over a henselian local ring, and
that applies twice: to `π` over `R` and to its base change `Y_A ⟶ Spec A` over `A`. The two closed
fibres of `Y` agree, because `Spec κ(A) ⟶ Spec A ⟶ Spec R` is the closed point of `Spec R`
precomposed with the isomorphism of residue fields. So base change along the two-step projection
`Y_{κ(A)} ⟶ Y_A ⟶ Y` is an equivalence, and the second step is one as well; peeling it off leaves
the first.

This is the step of the proof of [Stacks, Tag 0C0Q] which reads "because `A ⟶ B'` induces a
trivial residue field extension, two applications of Lemma 58.9.1 show that `Z'` is the base
change of a finite étale morphism `Y ⟶ X`": there `A` is a strictly henselian discrete valuation
ring, `B'` is its integral closure in a finite subextension of the algebraic closure of its
fraction field, and the residue fields agree because that of `A` is algebraically closed
(`Stacks.Henselian.bijective_residueField_map_integralClosure`).

## Main results

* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_pullback_fst_of_comp` — the converse of
  `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_pullback_fst_comp`: from the two-step
  projection and the second step, the first step.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_pullback_fst_of_bijective_residueField` —
  the statement above.

## References

* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0C0Q](https://stacks.math.columbia.edu/tag/0C0Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### A pullback taken in two steps -/

/-- **Peeling off the second step of a two-step base change.** For `W ⟶ Z ⟶ S` and `f : X ⟶ S`,
if base change along the projection `X ×_S W ⟶ X` is an equivalence on finite étale covers and so
is base change along the second step `(X ×_S Z) ×_Z W ⟶ X ×_S Z`, then base change along the first
step `X ×_S Z ⟶ X` is an equivalence.

This is the converse of
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_pullback_fst_comp` and uses the same
factorization: `pullbackLeftPullbackSndIso` writes the projection `X ×_S W ⟶ X` as an isomorphism
followed by the composite of the other two, so base change along the composite is an equivalence,
and `CategoryTheory.Functor.isEquivalence_of_comp_right` removes the second factor. -/
theorem isEquivalence_finiteEtaleBaseChange_pullback_fst_of_comp {X S Z W : Scheme.{u}}
    (f : X ⟶ S) (b : Z ⟶ S) (a : W ⟶ Z)
    (hab : (finiteEtaleBaseChange (pullback.fst f (a ≫ b))).IsEquivalence)
    (ha : (finiteEtaleBaseChange (pullback.fst (pullback.snd f b) a)).IsEquivalence) :
    (finiteEtaleBaseChange (pullback.fst f b)).IsEquivalence := by
  rw [← pullbackLeftPullbackSndIso_inv_fst f b a] at hab
  have : (finiteEtaleBaseChange
      (pullback.fst (pullback.snd f b) a ≫ pullback.fst f b)).IsEquivalence := by
    have h := isEquivalence_finiteEtaleBaseChange_isIso_comp
      (pullbackLeftPullbackSndIso f b a).hom _ hab
    rwa [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at h
  have : (finiteEtaleBaseChange (pullback.fst f b) ⋙
      finiteEtaleBaseChange (pullback.fst (pullback.snd f b) a)).IsEquivalence :=
    Functor.isEquivalence_of_iso (finiteEtaleBaseChangeComp _ _)
  exact Functor.isEquivalence_of_comp_right (finiteEtaleBaseChange (pullback.fst f b))
    (finiteEtaleBaseChange (pullback.fst (pullback.snd f b) a))

/-! ### A residually trivial henselian extension -/

/-- **Finite étale covers of a proper scheme are unchanged by a residually trivial henselian
extension of the base.** Let `R ⟶ A` be a local homomorphism of henselian local rings inducing a
bijection on residue fields and let `π : Y ⟶ Spec R` be proper. Then base change along the
projection `Y_A ⟶ Y` is an equivalence on finite étale covers.

[Stacks, Tag 0A48] applies on both sides: to `π` over the henselian local `R`, and to the base
change `Y_A ⟶ Spec A` over the henselian local `A`. The residue-field bijection makes
`Spec κ(A) ⟶ Spec A ⟶ Spec R` equal to an isomorphism followed by `Spec κ(R) ⟶ Spec R`, so base
change along the two-step projection `Y_{κ(A)} ⟶ Y` is an equivalence; then
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_pullback_fst_of_comp` peels off the second
step, which is Tag 0A48 for `A`. -/
@[sga "3 VIIB 1.6.E" "(b), special case",
  sga "3 X 4.0" "more general",
  sga "4 XII 5.9" "more general",
  sga "4 XII 5.9bis" "more general",
  sga "7 IX 2.2.4" "more general",
  sga "7 XIII 1.2.1" "more general"]
theorem isEquivalence_finiteEtaleBaseChange_pullback_fst_of_bijective_residueField
    (R A : Type u) [CommRing R] [CommRing A] [HenselianLocalRing R] [HenselianLocalRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)]
    (hres : Function.Bijective (ResidueField.map (algebraMap R A)))
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) [IsProper π] :
    (finiteEtaleBaseChange (pullback.fst π
      (Spec.map (CommRingCat.ofHom (algebraMap R A))))).IsEquivalence := by
  let g : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let qR : Spec (.of (ResidueField R)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R)))
  let qA : Spec (.of (ResidueField A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))
  let ρ : CommRingCat.of (ResidueField R) ⟶ CommRingCat.of (ResidueField A) :=
    CommRingCat.ofHom (ResidueField.map (algebraMap R A))
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).mpr hres
  let θ : Spec (.of (ResidueField A)) ⟶ Spec (.of (ResidueField R)) := Spec.map ρ
  have : IsIso θ := inferInstanceAs (IsIso (Spec.map ρ))
  have hsq : qA ≫ g = θ ≫ qR := by
    simp only [qA, g, θ, qR, ← Spec.map_comp]
    exact congrArg Spec.map
      (CommRingCat.hom_ext (ResidueField.map_comp_residue (algebraMap R A)).symm)
  have hcomp : (finiteEtaleBaseChange (pullback.fst π (qA ≫ g))).IsEquivalence := by
    rw [hsq]
    exact isEquivalence_finiteEtaleBaseChange_pullback_fst_comp π qR θ
      (isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing R π)
      (isEquivalence_finiteEtaleBaseChange_of_isIso _)
  have : IsProper (pullback.snd π g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback π g) ‹IsProper π›
  exact isEquivalence_finiteEtaleBaseChange_pullback_fst_of_comp π g qA hcomp
    (isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing A (pullback.snd π g))

end AlgebraicGeometry

end
