module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartCover
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartDehomogenizedSquare
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.RelationPermutation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartNormalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpSingularPoints

/-!
# A rational double point in case I with a singular blowup has a good coordinate

Let `S` be a Situation [Stacks, Tag 0BGC] in case I, whose blowup `X` in the maximal ideal has a
singular point `p`. Then `S.A` has a good coordinate. Following the source: `p` lies in one of the
three standard charts; after renumbering the generators it lies in the chart of the first one;
there it is cut out on the exceptional curve by a proper ideal `M` of `κ[y₂, y₃]` with
`q(1, y₂, y₃) ∈ M²` (the first step of the Claim); and moving `p` to the origin of the chart makes
the first row of the quadratic form vanish, so that the first generator is a good coordinate
(`AlgebraicGeometry.exists_isGoodCoordinateForm_of_dehomogenized_mem_sq`).

## Main results

* `AlgebraicGeometry.RationalDoublePointSituation.exists_isGoodCoordinate`
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A quadratic relation modulo `𝔪³` among generators of the maximal ideal is a cubic
expansion. -/
theorem exists_cubicExpansion_of_mem_pow_three {A : Type u} [CommRing A] [IsLocalRing A]
    {x : Fin 3 → A} (hspan : Ideal.span (Set.range x) = maximalIdeal A) {r : A}
    (hr : r ∈ maximalIdeal A ^ 3) :
    ∃ b : Fin 3 → Fin 3 → Fin 3 → A, r = ∑ i, ∑ j, ∑ k, b i j k * (x i * x j * x k) := by
  rw [← hspan, span_pow_three_eq_span_triples] at hr
  exact exists_triple_expansion x hr

/-- A cubic expansion in generators of the maximal ideal lies in `𝔪³`. -/
theorem cubicExpansion_mem_pow_three {A : Type u} [CommRing A] [IsLocalRing A]
    {x : Fin 3 → A} (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (b : Fin 3 → Fin 3 → Fin 3 → A) :
    ∑ i, ∑ j, ∑ k, b i j k * (x i * x j * x k) ∈ maximalIdeal A ^ 3 := by
  have hx : ∀ i, x i ∈ maximalIdeal A := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => Ideal.sum_mem _ fun k _ => ?_
  refine Ideal.mul_mem_left _ _ ?_
  rw [pow_succ, pow_two]
  exact Ideal.mul_mem_mul (Ideal.mul_mem_mul (hx i) (hx j)) (hx k)

namespace RationalDoublePointSituation

variable (S : RationalDoublePointSituation.{u})

/-- **(A1) A rational double point in case I whose blowup is singular has a good coordinate.** -/
theorem exists_isGoodCoordinate (hcase : IsCaseOne S.A) (w : blowUp (maximalIdealSheaf S.A))
    (hw : w ∈ singularLocus (blowUp (maximalIdealSheaf S.A))) :
    ∃ e : S.A, IsFirstGeneratorOfGoodRelation S.A e := by
  have hwc := S.isClosed_singleton_of_mem_singularLocus_blowUp w hw
  have hwo := S.blowUpToBase_eq_closedPoint_of_mem_singularLocus w hw
  have hdimw := S.ringKrullDim_stalk_blowUp_eq_two w hwc
  have : IsLocallyNoetherian (blowUp (maximalIdealSheaf S.A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (maximalIdealSheaf S.A))
  -- pass to the global sections `Γ ≅ A`
  let ε : S.A ≃+* Γ(Spec (.of S.A), ⊤) := (Scheme.ΓSpecIso (.of S.A)).symm.commRingCatIsoToRingEquiv
  have : IsLocalHom (ε : S.A →+* Γ(Spec (.of S.A), ⊤)) := IsLocalHom.of_surjective _ ε.surjective
  have : IsNoetherianRing Γ(Spec (.of S.A), ⊤) := isNoetherianRing_of_ringEquiv S.A ε
  have hmaxε : Ideal.map (ε : S.A →+* Γ(Spec (.of S.A), ⊤)) (IsLocalRing.maximalIdeal S.A) =
      IsLocalRing.maximalIdeal Γ(Spec (.of S.A), ⊤) := IsLocalRing.map_ringEquiv_maximalIdeal ε
  have hresε : Function.Bijective (ResidueField.map (ε : S.A →+* Γ(Spec (.of S.A), ⊤))) :=
    (ResidueField.mapEquiv ε).bijective
  obtain ⟨x, a, hspan, hupper, hunit, hrel, hcaseΓ⟩ :=
    IsCaseOne.map_of_bijective _ hmaxε hresε hcase
  obtain ⟨j, hj, y, hymax, hyx, ⟨ey⟩⟩ := exists_chart_of_isClosed S.A x hspan w hwc hwo
  -- renumber so that the chart is the chart of the first generator
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 j
  obtain ⟨hupper', hunit', hrel', hcase'⟩ :=
    exists_permuted_caseOne_relation hunit hupper hrel hcaseΓ σ
  have hspan' : Ideal.span (Set.range (fun p => x (σ p))) =
      IsLocalRing.maximalIdeal Γ(Spec (.of S.A), ⊤) := by
    rw [show (fun p => x (σ p)) = x ∘ σ from rfl, Set.range_comp, Equiv.range_eq_univ,
      Set.image_univ, hspan]
  have hσ0 : x (σ 0) = x j := by simp [σ]
  -- the local ring at the point is the local ring of the chart
  let e' := ey.trans (Spec.stalkIso _ y).commRingCatIsoToRingEquiv
  have : IsNoetherianRing (Localization.AtPrime y.asIdeal) := isNoetherianRing_of_ringEquiv _ e'
  have hdimy : 2 ≤ ringKrullDim (Localization.AtPrime y.asIdeal) := by
    rw [← ringKrullDim_eq_of_ringEquiv e', hdimw]
  have hsingy : ¬ IsRegularLocalRing (Localization.AtPrime y.asIdeal) := fun h => by
    have := h
    exact hw (IsRegularLocalRing.of_ringEquiv e'.symm)
  obtain ⟨I, hI, hmem⟩ := exists_ne_top_dehomogenized_mem_sq_of_not_isRegularLocalRing
    (x := fun p => x (σ p)) ((maximalIdealSheaf S.A).ideal (topAffineOpen S.A))
    (maximalIdealSheaf_ideal_top S.A).symm (x j) hσ0 _ hspan' (permuteRelation a σ) hupper' hrel'
    y.asIdeal hyx hdimy hsingy
  obtain ⟨b, hb⟩ := exists_cubicExpansion_of_mem_pow_three hspan' hrel'
  obtain ⟨x'', a'', b'', hspan'', hupper'', -, -, -, -, -, hrel'', hgood''⟩ :=
    exists_isGoodCoordinateForm_of_dehomogenized_mem_sq (fun p => x (σ p)) hspan'
      (permuteRelation a σ) b hupper' hunit' hb hcase' I hI hmem
  have hgoodΓ : IsFirstGeneratorOfGoodRelation Γ(Spec (.of S.A), ⊤) (x'' 0) :=
    ⟨x'', a'', rfl, hspan'', hupper'', by rw [hrel'']; exact cubicExpansion_mem_pow_three hspan'' _,
      hgood''⟩
  have hmaxε' : Ideal.map (ε.symm : Γ(Spec (.of S.A), ⊤) →+* S.A)
      (IsLocalRing.maximalIdeal Γ(Spec (.of S.A), ⊤)) = IsLocalRing.maximalIdeal S.A :=
    IsLocalRing.map_ringEquiv_maximalIdeal ε.symm
  have : IsLocalHom (ε.symm : Γ(Spec (.of S.A), ⊤) →+* S.A) :=
    IsLocalHom.of_surjective _ ε.symm.surjective
  exact ⟨_, hgoodΓ.map _ hmaxε' (ResidueField.mapEquiv ε.symm).bijective⟩

end RationalDoublePointSituation

end AlgebraicGeometry

end
