module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionOnePoint
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionOpenPart
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpaceTruncations
public import StacksFrontier.Deformation.Artin.FunctorFormalObject

/-!
# Formal objects of Artin's contraction functor: the open part

In the situation of Stacks 0GH8 let `F` be Artin's contraction functor of Stacks 0GHA. A formal
object `ξ = (R, ξ_n)` of `F` consists of elements `ξ_n ∈ F(Spec(R/𝔪ⁿ⁺¹))`. As the proof of
Stacks 0GI8 observes, each `Spec(R/𝔪ⁿ⁺¹)` has a single point, so the closed subset `Z_n` of the
triple `ξ_n` is empty or everything, and since `Z_n` is the inverse image of `Z_{n+1}` the same
alternative holds for all `n`: either `ξ` is a formal object of `U'` or a formal object of `W`.
This file proves that dichotomy and that in the first case `ξ` is effective, by Stacks 0AQH in
the form `AlgebraicGeometry.FormalSpace.existsUnique_section_of_compatible_truncations` (the
source cites Stacks 07X8 here).

## Main results

* `Deformation.Artin.FormalBase.subsingleton_truncation`: `Spec(R/𝔪ⁿ⁺¹)` has a single point.
* `AlgebraicGeometry.Artin.ContractionSituation.formalObject_Z_eq_empty_or_eq_univ`: either every
  `Z_n` is empty or every `Z_n` is everything.
* `AlgebraicGeometry.Artin.ContractionSituation.mem_U'_of_restrict_mem`: a section of `X'` over
  `Spec R` whose restriction to the closed point lies in `U'` lies in `U'`.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_effective_of_Z_eq_empty`: a formal object
  of `F` with `Z_n = ∅` for all `n` is effective.

## References

* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace Deformation.Artin

/-- Every prime of `R/𝔪ⁿ⁺¹`, for `R` a local ring, pulls back to the maximal ideal `𝔪`. -/
theorem comap_quotient_mk_pow_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    (p : PrimeSpectrum (R ⧸ maximalIdeal R ^ (n + 1))) :
    p.asIdeal.comap (Ideal.Quotient.mk _) = maximalIdeal R := by
  have hle : maximalIdeal R ^ (n + 1) ≤ p.asIdeal.comap (Ideal.Quotient.mk _) := by
    intro x hx
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  exact ((maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
    (Ideal.IsPrime.le_of_pow_le hle)).symm

/-- The spectrum of `R/𝔪ⁿ⁺¹` has a single point: every prime of `R` containing `𝔪ⁿ⁺¹` is
`𝔪`. -/
theorem FormalBase.subsingleton_truncation {S : AlgebraicGeometry.Scheme.{u}} (A : FormalBase S)
    (n : ℕ) : Subsingleton (A.truncation n) := by
  change Subsingleton (PrimeSpectrum (A.R ⧸ maximalIdeal A.R ^ (n + 1)))
  exact ⟨fun p q => PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _
    Ideal.Quotient.mk_surjective
    ((comap_quotient_mk_pow_maximalIdeal p).trans (comap_quotient_mk_pow_maximalIdeal q).symm))⟩

/-- The spectrum of `R/𝔪ⁿ⁺¹` is nonempty. -/
theorem FormalBase.nonempty_truncation {S : AlgebraicGeometry.Scheme.{u}} (A : FormalBase S)
    (n : ℕ) : Nonempty (A.truncation n) := by
  have : Nontrivial (A.R ⧸ maximalIdeal A.R ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal A.R).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  exact inferInstanceAs (Nonempty (PrimeSpectrum (A.R ⧸ maximalIdeal A.R ^ (n + 1))))

end Deformation.Artin

namespace AlgebraicGeometry.Artin.ContractionSituation

open LocallyNoetherianOver Deformation.Artin

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- The value of Artin's functor on a morphism of the locally Noetherian site is transport of
triples. -/
theorem contractionFunctor_map_apply {V₁ V₂ : LocallyNoetherianOver B S hS} (φ : V₂ ⟶ V₁)
    (t : (contractionFunctor c).obj (op V₁)) :
    (contractionFunctor c).map φ.op t = mapTriple c φ.hom t :=
  rfl

/-- **Formal objects of `F` are formal objects of `U'` or of `W`.** For a formal object `ξ` of
Artin's functor, either every closed subset `Z_n` is empty or every `Z_n` is everything. -/
theorem formalObject_Z_eq_empty_or_eq_univ (A : FormalBase S)
    (hA : ∀ n, B.Contains (A.truncation n))
    (ξ : ∀ n, (contractionFunctor c).obj (op (truncationObj B S hS A hA n)))
    (hξ : ∀ n, (contractionFunctor c).map (truncationObjSucc B S hS A hA n).op (ξ (n + 1)) =
      ξ n) :
    (∀ n, (ξ n).Z = ∅) ∨ ∀ n, (ξ n).Z = Set.univ := by
  have hsub : ∀ n, Subsingleton
      ((BigFppfOver.toScheme B S hS).obj (truncationObj B S hS A hA n).obj) :=
    fun n => A.subsingleton_truncation n
  have hne : ∀ n, Nonempty (Space.points B S hS
      (yoneda.obj (truncationObj B S hS A hA n).obj)) := by
    intro n
    obtain ⟨x⟩ := A.nonempty_truncation n
    exact ⟨(Space.pointsEquivScheme B S hS _).symm x⟩
  have hZ : ∀ n x, x ∈ (ξ n).Z ↔ Space.pointsMap B S hS _
      (yoneda.map (truncationOverSucc B S hS A hA n)) x ∈ (ξ (n + 1)).Z := fun n x => by
    rw [← hξ n]
    rfl
  have hdich : ∀ n, (ξ n).Z = ∅ ∨ (ξ n).Z = Set.univ := fun n =>
    have := hsub n; (ξ n).Z_eq_empty_or_eq_univ
  rcases hdich 0 with h0 | h0
  · refine Or.inl fun n => ?_
    induction n with
    | zero => exact h0
    | succ n ih =>
      refine (hdich (n + 1)).resolve_right fun h => ?_
      obtain ⟨x⟩ := hne n
      simpa [ih] using (hZ n x).mpr (h ▸ Set.mem_univ _)
  · refine Or.inr fun n => ?_
    induction n with
    | zero => exact h0
    | succ n ih =>
      refine (hdich (n + 1)).resolve_left fun h => ?_
      obtain ⟨x⟩ := hne n
      have hx := (hZ n x).mp (ih ▸ Set.mem_univ _)
      rw [h] at hx
      exact hx

/-- The point of `Spec(R/𝔪)` maps to the closed point of `Spec R`. -/
theorem restrictionToBase_zero_apply (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n))
    (x : A.truncation 0) :
    (BigFppfOver.toScheme B S hS).map
        (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA 0) x =
      (closedPoint A.R : PrimeSpectrum A.R) := by
  change PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal A.R ^ (0 + 1))) x = _
  ext1
  change x.asIdeal.comap _ = maximalIdeal A.R
  exact comap_quotient_mk_pow_maximalIdeal x

/-- A section of `X'` over `Spec R`, for `R` a Noetherian complete local ring, lies in the open
subspace `U'` as soon as its restriction to `Spec(R/𝔪)` does: the inverse image of the closed set
`T'` is a closed subset of `Spec R`, and a nonempty one would contain the closed point. -/
theorem mem_U'_of_restrict_mem (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n))
    (y : c.X'.obj (op (baseOver B S hS A (A.contains_spec_of_contains_truncation hA))))
    (hy : c.X'.map (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA)
      hA 0).op y ∈ c.U'.obj (op (truncationOver B S hS A hA 0))) :
    y ∈ c.U'.obj (op (baseOver B S hS A (A.contains_spec_of_contains_truncation hA))) := by
  let V := baseOver B S hS A (A.contains_spec_of_contains_truncation hA)
  let ι := restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA 0
  change Set.range (Space.pointsMap B S hS (yoneda.obj V) (yonedaEquiv.symm y)) ⊆ c.T'ᶜ
  change Set.range (Space.pointsMap B S hS (yoneda.obj (truncationOver B S hS A hA 0))
    (yonedaEquiv.symm (c.X'.map ι.op y))) ⊆ c.T'ᶜ at hy
  rw [yonedaEquiv_symm_map, Space.pointsMap_comp] at hy
  rintro _ ⟨q, rfl⟩ hq
  have hC : IsClosed (Space.pointsMap B S hS _ (yonedaEquiv.symm y) ⁻¹' c.T') :=
    c.isClosed_T'.preimage (Space.continuous_pointsMap B S hS _)
  have hC' := (Space.isClosed_pointTopology_yoneda_iff_isClosed_image B S hS V _).mp hC
  have hm : (closedPoint A.R : PrimeSpectrum A.R) ∈ Space.pointsToScheme B S hS V ''
      (Space.pointsMap B S hS _ (yonedaEquiv.symm y) ⁻¹' c.T') :=
    (IsLocalRing.specializes_closedPoint (Space.pointsToScheme B S hS V q)).mem_closed hC'
      ⟨q, hq, rfl⟩
  obtain ⟨q', hq', hq'm⟩ := hm
  obtain ⟨x₀⟩ := A.nonempty_truncation 0
  obtain ⟨q₀, hq₀⟩ := Space.surjective_pointsToScheme B S hS (truncationOver B S hS A hA 0) x₀
  have hq₀' : Space.pointsMap B S hS _ (yoneda.map ι) q₀ = q' := by
    apply Space.injective_pointsToScheme B S hS V
    rw [Space.pointsToScheme_pointsMap_yoneda, hq₀, hq'm]
    exact restrictionToBase_zero_apply A hA x₀
  refine hy ⟨q₀, rfl⟩ ?_
  change Space.pointsMap B S hS _ (yonedaEquiv.symm y) (Space.pointsMap B S hS _ (yoneda.map ι) q₀)
    ∈ c.T'
  rw [hq₀']
  exact hq'

/-- The second component of a triple with empty closed subset is invariant under equality of
triples. -/
theorem Triple.uValue_congr {V : BigFppfOver B S hS} {t t' : Triple c V} (e : t = t')
    (h : t.Z = ∅) (h' : t'.Z = ∅) : t.uValue h = t'.uValue h' := by
  subst e
  rfl

/-- **Stacks 0GI8, the open part.** A formal object of Artin's functor whose closed subsets `Z_n`
are all empty is effective: it is a formal object of the algebraic space `U'`, effective by
Stacks 0AQH. -/
theorem exists_effective_of_Z_eq_empty (A : FormalBase S)
    (hA : ∀ n, B.Contains (A.truncation n))
    (ξ : ∀ n, (contractionFunctor c).obj (op (truncationObj B S hS A hA n)))
    (hξ : ∀ n, (contractionFunctor c).map (truncationObjSucc B S hS A hA n).op (ξ (n + 1)) =
      ξ n)
    (h : ∀ n, (ξ n).Z = ∅) :
    ∃ x : (contractionFunctor c).obj (op (baseObj B S hS A hA)),
      ∀ n, (contractionFunctor c).map (truncationObjIncl B S hS A hA n).op x = ξ n := by
  have := A.noetherian
  have hR : IsNoetherianCompleteLocalRing A.R := ⟨A.noetherian, inferInstance, A.complete⟩
  set hRS := A.contains_spec_of_contains_truncation hA
  let e : ∀ n, c.U'.obj (op (truncationOver B S hS A hA n)) := fun n =>
    (ξ n).u.app (op _) ⟨𝟙 _, (ξ n).id_mem_openSubspace (h n)⟩
  have he : ∀ n, c.X'.map (truncationOverSucc B S hS A hA n).op (e (n + 1)).1 = (e n).1 := by
    intro n
    have h' : (mapTriple c (truncationOverSucc B S hS A hA n) (ξ (n + 1))).Z = ∅ :=
      (congrArg Triple.Z (hξ n)).trans (h n)
    exact (Triple.uValue_mapTriple (truncationOverSucc B S hS A hA n) (ξ (n + 1)) (h (n + 1))
      h').symm.trans (Triple.uValue_congr c (hξ n) h' (h n))
  have hτ : ∀ n, truncationOverSucc B S hS A hA n ≫ restrictionToBase B S hS A hRS hA (n + 1) =
      restrictionToBase B S hS A hRS hA n := by
    intro n
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact adicThickeningSucc_ι A.R (maximalIdeal A.R) n
  obtain ⟨y, hy, -⟩ := FormalSpace.existsUnique_section_of_compatible_truncations hR
    (fun n => maximalIdeal A.R ^ (n + 1)) (fun n => Ideal.pow_le_self (Nat.succ_ne_zero n))
    (fun n => Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) (fun n => ⟨n + 1, le_rfl⟩)
    (fun k => ⟨k, Ideal.pow_le_pow_right (Nat.le_succ k)⟩) c.isAlgebraicSpace_X'
    (baseOver B S hS A hRS) (Iso.refl _) (fun n => truncationOver B S hS A hA n)
    (fun n => Iso.refl _) (fun n => restrictionToBase B S hS A hRS hA n)
    (fun n => by simp only [Iso.refl_hom]; rfl)
    (fun n => truncationOverSucc B S hS A hA n) hτ (fun n => (e n).1) he
  have hyU : y ∈ c.U'.obj (op (baseOver B S hS A hRS)) :=
    c.mem_U'_of_restrict_mem A hA y (by convert (e 0).2 using 1; exact hy 0)
  let u : yoneda.obj (baseOver B S hS A hRS) ⟶ c.U'.toFunctor := yonedaEquiv.symm ⟨y, hyU⟩
  refine ⟨c.emptyTriple _ u, fun n => ?_⟩
  change mapTriple c (restrictionToBase B S hS A hRS hA n) (c.emptyTriple _ u) = ξ n
  refine (emptyTriple_comp c _ u).symm.trans ?_
  have hun : yoneda.map (restrictionToBase B S hS A hRS hA n) ≫ u = yonedaEquiv.symm (e n) :=
    (yonedaEquiv_symm_map (F := c.U'.toFunctor) (restrictionToBase B S hS A hRS hA n).op
      (⟨y, hyU⟩ : c.U'.toFunctor.obj _)).symm.trans
      (congrArg yonedaEquiv.symm (show c.U'.toFunctor.map
        (restrictionToBase B S hS A hRS hA n).op ⟨y, hyU⟩ = e n from Subtype.ext (hy n)))
  refine (congrArg (c.emptyTriple _) hun).trans ?_
  refine (Triple.eq_emptyTriple c (ξ n) _ (h n) ?_).symm
  refine ext_openSubspace_compl_empty (h n) _ _ fun hh => ?_
  change c.U'.toFunctor.map (𝟙 _).op (e n) = (ξ n).u.app (op _) ⟨𝟙 _, hh⟩
  rw [op_id, Functor.map_id_apply]
  rfl

end AlgebraicGeometry.Artin.ContractionSituation

end
