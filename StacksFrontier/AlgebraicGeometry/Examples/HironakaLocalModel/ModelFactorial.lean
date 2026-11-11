module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaNotProjective
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.OriginFibreCharts
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective

/-!
# Hironaka's local model: the source of the tower is integral and locally factorial

Let `k` be a field, `A = k[x, y, z]`, `I = (x, y)`, `J = (x - y², z)`, and let
`T = Bl_{J'} Bl_I Spec A ⟶ Spec A` be the tower of Hironaka's example, `J'` the strict transform
of `V(J)`. Both centres are nonzero, so both blow-ups are integral ([Stacks, Tag 02ND]) and
surjective: a blow-up is an isomorphism off its centre, so the generic point of the base is in its
image, and a proper morphism has closed image.

The source `T` is covered by four affine charts (see
`Stacks.Examples.HironakaLocalModel.towerChart_cover`): two copies of `𝔸³_k` and two basic opens
of `𝔸³_k`. Their coordinate rings are polynomial rings over `k` and localizations of one, hence
unique factorization domains, so every point of `T` has an affine open neighbourhood whose ring of
sections is a unique factorization domain.

## Main results

* `Stacks.Examples.HironakaLocalModel.isIntegral_modelSpace`: `T` is integral.
* `Stacks.Examples.HironakaLocalModel.exists_affineOpen_uniqueFactorizationMonoid`: every point
  of `T` has an affine open neighbourhood with factorial ring of sections.
* `Stacks.Examples.HironakaLocalModel.surjective_modelTower`: the tower is surjective.

## References

* [Stacks Project, Tag 08KF](https://stacks.math.columbia.edu/tag/08KF)
* [Stacks Project, Tag 02ND](https://stacks.math.columbia.edu/tag/02ND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.TwoStepTower Stacks.Examples.HironakaNotProjective

universe u

namespace Stacks.Examples.HironakaLocalModel

/-! ### Generalities -/

/-- **An affine chart with factorial coordinate ring.** If `g : Spec R ⟶ X` is an open immersion
and `R` is a unique factorization monoid, every point of the range of `g` lies in an affine open
of `X` whose ring of sections is a unique factorization monoid. -/
theorem exists_affineOpen_uniqueFactorizationMonoid_of_isOpenImmersion {X : Scheme.{u}}
    {R : CommRingCat.{u}} [UniqueFactorizationMonoid R] (g : Spec R ⟶ X) [IsOpenImmersion g]
    {x : X} (hx : x ∈ Set.range g) :
    ∃ U : X.affineOpens, x ∈ (U : Set X) ∧ UniqueFactorizationMonoid Γ(X, U) := by
  refine ⟨⟨g.opensRange, isAffineOpen_opensRange g⟩, hx, ?_⟩
  change UniqueFactorizationMonoid Γ(X, g.opensRange)
  rw [← g.image_top_eq_opensRange]
  exact (g.appIso ⊤ ≪≫ Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv.symm
    |>.uniqueFactorizationMonoid ‹_›

/-- **A proper blow-up of an integral scheme in a nonzero centre is surjective**: the blow-up is
an isomorphism off its centre, which misses the generic point, and its image is closed. -/
theorem surjective_blowUpToBase_of_ne_bot {X : Scheme.{u}} [IsIntegral X]
    {I : X.IdealSheafData} (hI : I ≠ ⊥) [IsProper (blowUpToBase I)] :
    Surjective (blowUpToBase I) := by
  obtain ⟨y, hy⟩ :=
    exists_blowUpToBase_eq_of_notMem_support I (genericPoint_notMem_supportSet I hI)
  have hclosed : IsClosed (Set.range (blowUpToBase I).base) :=
    (blowUpToBase I).isClosedMap.isClosed_range
  refine (surjective_iff _).mpr fun x => ?_
  have hx : x ∈ closure ({genericPoint X} : Set X) := by
    rw [genericPoint_closure]
    trivial
  have hη : genericPoint X ∈ Set.range (blowUpToBase I).base := ⟨y, hy⟩
  exact closure_minimal (Set.singleton_subset_iff.mpr hη) hclosed hx

/-! ### The two centres are nonzero -/

variable (k : Type u) [Field k]

/-- The ideal sheaf on `Spec k[x, y, z]` of a nonzero ideal is nonzero. -/
theorem idealSheafOf_ne_bot {K : Ideal (Ring3 k)} (hK : K ≠ ⊥) : idealSheafOf k K ≠ ⊥ := by
  intro h
  apply hK
  have hK' := idealSheafOf_ideal_top k K
  rw [h] at hK'
  have h0 : K.map (gammaEquiv k : Ring3 k →+* Γ(ambient k, ⊤)) = ⊥ := hK'.symm
  exact (Ideal.map_eq_bot_iff_of_injective (gammaEquiv k).injective).mp h0

/-- The first centre `I = (x, y)` is nonzero. -/
theorem centreIdeal_ne_bot : centreIdeal k ≠ ⊥ := by
  refine idealSheafOf_ne_bot k fun h => X_ne_zero (R := k) (0 : Fin 3) ?_
  exact Ideal.span_eq_bot.mp h _ (Set.mem_insert _ _)

/-- The second centre `J'`, the strict transform of `V(x - y², z)`, is nonzero: on the chart `U₁`
it is cut out by `(1 - x·y₁², z)`. -/
theorem strictCurve_ne_bot : strictCurve k ≠ ⊥ := by
  intro h
  change strictCentre (centreIdeal k) (curveIdeal k) = ⊥ at h
  have h₀ := comap_chartι_zero_strictCentre k
  rw [h, Scheme.IdealSheafData.comap_bot] at h₀
  refine idealSheafOf_ne_bot k (K := Ideal.span {1 - X 0 * X 1 ^ 2, X 2})
    (fun hs => X_ne_zero (R := k) (2 : Fin 3) ?_) h₀.symm
  exact Ideal.span_eq_bot.mp hs _ (Set.mem_insert_of_mem _ rfl)

/-! ### Integrality and surjectivity -/

/-- The affine space `Spec k[x, y, z]` is integral. -/
instance isIntegral_ambient : IsIntegral (ambient k) := by
  have : IsDomain (CommRingCat.of (Ring3 k)) := inferInstanceAs (IsDomain (Ring3 k))
  infer_instance

/-- The first blow-up `Bl_I Spec k[x, y, z]` is integral. -/
instance isIntegral_firstBlowup : IsIntegral (blowUp (centreIdeal k)) :=
  isIntegral_blowUp (centreIdeal k) (centreIdeal_ne_bot k)

/-- **The source of the model tower is integral** ([Stacks, Tag 02ND], twice). -/
instance isIntegral_modelSpace : IsIntegral (modelSpace k) :=
  isIntegral_blowUp (strictCurve k) (strictCurve_ne_bot k)

/-- **The model tower is surjective**: both blow-ups are proper with nonzero centre on an
integral scheme. -/
theorem surjective_modelTower : Surjective (modelTower k) := by
  have hI := isFiniteType_of_isLocallyNoetherian (centreIdeal k)
  have := isProper_blowUpToBase hI
  have := isProper_blowUpToBase (isFiniteType_strictCentre hI (curveIdeal k))
  have := surjective_blowUpToBase_of_ne_bot (centreIdeal_ne_bot k)
  have := surjective_blowUpToBase_of_ne_bot (strictCurve_ne_bot k)
  change Surjective (blowUpToBase (strictCurve k) ≫ blowUpToBase (centreIdeal k))
  infer_instance

/-! ### Local factoriality -/

/-- **The source of the model tower is locally factorial**: every point has an affine open
neighbourhood whose ring of sections is a unique factorization monoid. The four charts of
`Stacks.Examples.HironakaLocalModel.towerChart_cover` have coordinate rings `k[x, y, z]` and
localizations of it. -/
theorem exists_affineOpen_uniqueFactorizationMonoid (x : modelSpace k) :
    ∃ U : (modelSpace k).affineOpens, x ∈ (U : Set (modelSpace k)) ∧
      UniqueFactorizationMonoid Γ(modelSpace k, U) := by
  have hR : UniqueFactorizationMonoid (CommRingCat.of (Ring3 k)) :=
    inferInstanceAs (UniqueFactorizationMonoid (Ring3 k))
  have hL₁ : UniqueFactorizationMonoid (CommRingCat.of (Localization.Away (unitEq k))) :=
    inferInstanceAs (UniqueFactorizationMonoid (Localization.Away (unitEq k)))
  have hL₂ : UniqueFactorizationMonoid (CommRingCat.of (Localization.Away (X 2 : Ring3 k))) :=
    inferInstanceAs (UniqueFactorizationMonoid (Localization.Away (X 2 : Ring3 k)))
  rcases towerChart_cover k x with h | h | h | h
  · exact exists_affineOpen_uniqueFactorizationMonoid_of_isOpenImmersion (towerChartOne k) h
  · exact exists_affineOpen_uniqueFactorizationMonoid_of_isOpenImmersion (towerChartTwo k) h
  · exact exists_affineOpen_uniqueFactorizationMonoid_of_isOpenImmersion
      (towerBasicChart k (unitEq k) (unitEq_mem_strictSpan k)) h
  · exact exists_affineOpen_uniqueFactorizationMonoid_of_isOpenImmersion
      (towerBasicChart k (X 2) (X_two_mem_strictSpan k)) h

end Stacks.Examples.HironakaLocalModel

end
