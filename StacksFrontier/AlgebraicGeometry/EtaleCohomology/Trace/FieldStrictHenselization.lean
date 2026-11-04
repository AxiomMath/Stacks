module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantStalkComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibre
public import StacksCore.Tactic.StacksAttribute

/-!
# The strict henselization of a field at a separable geometric point

Let `k` be a field and `K` an algebraically closed extension of `k` which is separable over `k`;
for instance an algebraic closure of a perfect field. The strict henselization of `Spec k` at the
geometric point `Spec K ⟶ Spec k` is `Spec K` itself: the étale local ring of `Spec k` there is a
field, being the strict henselization of the field `𝒪_{Spec k}`, and evaluation of étale germs in
`K` maps it isomorphically onto the separable closure of `k` in `K`, which is `K`.

Consequently, for a scheme `X` over `k`, the base change `X ×_k Spec 𝒪^{sh}` of Étale Cohomology,
Theorem 03Q9 is `X_K = X ×_k Spec K`: the canonical morphism from the geometric fibre is an
isomorphism.

## Main results

* `Stacks.Frobenius.maximalIdeal_stalk_specField_eq_bot` — the local ring of `Spec k` is a field.
* `Stacks.Frobenius.bijective_structureSheafStalkToGeometricField_fieldGeometricPoint` — evaluation
  of étale germs at `Spec K` is bijective.
* `Stacks.Frobenius.isIso_geometricPointToStrictHenselization_fieldGeometricPoint` — `Spec K` is
  the strict henselization of `Spec k` at `Spec K ⟶ Spec k`.
* `Stacks.Frobenius.isIso_geometricFibreToStrictHenselizationBaseChange_fieldGeometricPoint` —
  `X_K ⟶ X ×_k Spec 𝒪^{sh}` is an isomorphism.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Polynomial

universe u

namespace Stacks.Frobenius

variable {k : Type u} [Field k]

/-- **The local ring of `Spec k` is a field**: its maximal ideal is `⊥`. -/
theorem maximalIdeal_stalk_specField_eq_bot (x : Spec (.of k)) :
    maximalIdeal ((Spec (.of k)).presheaf.stalk x) = ⊥ := by
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := CommRingCat.of k) x
  let : Algebra ↑(CommRingCat.of k) ↑((Spec (.of k)).presheaf.stalk x) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of k) x
  have : IsLocalization.AtPrime ↑((Spec (.of k)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of k) x
  let : Field ↑(CommRingCat.of k) := inferInstanceAs (Field k)
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime x.asIdeal
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal ((Spec (.of k)).presheaf.stalk x),
    hx, Ideal.map_bot]

variable (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] (B : BigEtaleSite.{u})
  (hS : B.Contains (Spec (.of k)))

/-- **The étale local ring of `Spec k` at `Spec K` is a field.** -/
theorem isField_etaleLocalRing_fieldGeometricPoint :
    IsField ↥(etaleLocalRing B (Spec (.of k)) hS (fieldGeometricPoint K)) := by
  let := geometricResidueAlgebra (Spec (.of k)) (fieldGeometricPoint K)
  have h₁ := IsHenselization.map_maximalIdeal
    (R := ↥((Spec (.of k)).presheaf.stalk ((fieldGeometricPoint (k := k) K).hom
      (closedPoint (fieldGeometricPoint (k := k) K).residueField))))
    (L := separableClosure (ResidueField ↥((Spec (.of k)).presheaf.stalk
      ((fieldGeometricPoint (k := k) K).hom
        (closedPoint (fieldGeometricPoint (k := k) K).residueField))))
      (fieldGeometricPoint (k := k) K).residueField)
    (Rh := (geometricHenselizationTower (Spec (.of k)) (fieldGeometricPoint K)).strictHenselization)
  rw [maximalIdeal_stalk_specField_eq_bot, Ideal.map_bot] at h₁
  exact MulEquiv.isField (isField_iff_maximalIdeal_eq.2 h₁.symm)
    (etaleLocalRingEquivStrictHenselization B (Spec (.of k)) hS
      (fieldGeometricPoint K)).symm.toMulEquiv

/-- Evaluation of étale germs at `Spec K` is injective. -/
theorem injective_structureSheafStalkToGeometricField_fieldGeometricPoint :
    Function.Injective
      (structureSheafStalkToGeometricField B (Spec (.of k)) hS (fieldGeometricPoint K)) := by
  let := (isField_etaleLocalRing_fieldGeometricPoint K B hS).toField
  exact (structureSheafStalkToGeometricField B (Spec (.of k)) hS (fieldGeometricPoint K)).injective

/-- The structure map `k ⟶ κ` to the residue field of the local ring of `Spec k`, through global
sections. -/
def residueFieldOfField :
    k →+* ResidueField ↥((Spec (.of k)).presheaf.stalk
      ((fieldGeometricPoint (k := k) K).hom
        (closedPoint (fieldGeometricPoint (k := k) K).residueField))) :=
  (residue _).comp (((Spec (.of k)).presheaf.germ ⊤ _ trivial).hom.comp
    (Scheme.ΓSpecIso (.of k)).inv.hom)

/-- Evaluation of étale germs at `Spec K` is surjective when `K` is separable over `k`. -/
theorem surjective_structureSheafStalkToGeometricField_fieldGeometricPoint
    [Algebra.IsSeparable k K] :
    Function.Surjective
      (structureSheafStalkToGeometricField B (Spec (.of k)) hS (fieldGeometricPoint K)) := by
  let := geometricResidueAlgebra (Spec (.of k)) (fieldGeometricPoint K)
  have hcomp : (algebraMap (ResidueField ↥((Spec (.of k)).presheaf.stalk
      ((fieldGeometricPoint (k := k) K).hom
        (closedPoint (fieldGeometricPoint (k := k) K).residueField))))
        (fieldGeometricPoint (k := k) K).residueField).comp (residueFieldOfField K) =
      algebraMap k K := by
    refine RingHom.ext fun c => ?_
    have h := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap k K))
    have h₁ := ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of k)).inv c)
    have h₂ : (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)
        = c := by
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
    have h₀ := ConcreteCategory.congr_hom
      (Scheme.residue_descResidueField (Scheme.stalkClosedPointTo (fieldGeometricPoint K).hom))
      (((Spec (.of k)).presheaf.germ ⊤ _ trivial) ((Scheme.ΓSpecIso (.of k)).inv c))
    refine h₀.trans (h₁.trans ?_)
    rw [CommRingCat.comp_apply, h₂]
    rfl
  have hsep : ∀ y : (fieldGeometricPoint (k := k) K).residueField,
      IsSeparable (ResidueField ↥((Spec (.of k)).presheaf.stalk
        ((fieldGeometricPoint (k := k) K).hom
          (closedPoint (fieldGeometricPoint (k := k) K).residueField)))) y := by
    intro y
    have hy : IsSeparable k y := Algebra.IsSeparable.isSeparable k y
    have hzero : aeval y ((minpoly k y).map (residueFieldOfField K)) = 0 := by
      rw [aeval_def, eval₂_map, hcomp, ← aeval_def, minpoly.aeval]
    exact Separable.of_dvd (Polynomial.Separable.map (f := residueFieldOfField K) hy)
      (minpoly.dvd _ y hzero)
  intro y
  obtain ⟨d, hd⟩ := (mem_range_etaleResidueFieldToGeometricField_iff B (Spec (.of k)) hS
    (fieldGeometricPoint K) y).2 (mem_separableClosure_iff.2 (hsep y))
  obtain ⟨a, rfl⟩ := residue_surjective d
  exact ⟨a, (etaleResidueFieldToGeometricField_residue B (Spec (.of k)) hS
    (fieldGeometricPoint K) a).symm.trans hd⟩

/-- **The strict henselization of `Spec k` at `Spec K` is `Spec K`**, when `K` is separable over
`k`. -/
theorem isIso_geometricPointToStrictHenselization_fieldGeometricPoint [Algebra.IsSeparable k K] :
    IsIso (geometricPointToStrictHenselization B (Spec (.of k)) hS (fieldGeometricPoint K)) := by
  let e := RingEquiv.ofBijective
    (structureSheafStalkToGeometricField B (Spec (.of k)) hS (fieldGeometricPoint K))
    ⟨injective_structureSheafStalkToGeometricField_fieldGeometricPoint K B hS,
      surjective_structureSheafStalkToGeometricField_fieldGeometricPoint K B hS⟩
  have : IsIso (CommRingCat.ofHom
      (structureSheafStalkToGeometricField B (Spec (.of k)) hS (fieldGeometricPoint K))) :=
    (RingEquiv.toCommRingCatIso e).isIso_hom
  unfold geometricPointToStrictHenselization
  infer_instance

/-- **`X_K` is the base change of `X` to the strict henselization of `Spec k` at `Spec K`**, when
`K` is separable over `k`: the canonical morphism from the geometric fibre is an isomorphism. -/
theorem isIso_geometricFibreToStrictHenselizationBaseChange_fieldGeometricPoint
    [Algebra.IsSeparable k K] (X : Over (Spec (.of k))) :
    IsIso (geometricFibreToStrictHenselizationBaseChange B hS X.hom (fieldGeometricPoint K)) := by
  have := isIso_geometricPointToStrictHenselization_fieldGeometricPoint K B hS
  have h : geometricFibreToStrictHenselizationBaseChange B hS X.hom (fieldGeometricPoint K) =
      pullback.map X.hom (fieldGeometricPoint K).hom X.hom
        (strictHenselizationToBase B (Spec (.of k)) hS (fieldGeometricPoint K)) (𝟙 _)
        (geometricPointToStrictHenselization B (Spec (.of k)) hS (fieldGeometricPoint K)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, geometricPointToStrictHenselization_comp]) := by
    refine pullback.hom_ext ?_ ?_
    · rw [geometricFibreToStrictHenselizationBaseChange, pullback.lift_fst, pullback.lift_fst,
        Category.comp_id]
    · rw [geometricFibreToStrictHenselizationBaseChange, pullback.lift_snd, pullback.lift_snd]
  rw [h]
  infer_instance

end Stacks.Frobenius

end
