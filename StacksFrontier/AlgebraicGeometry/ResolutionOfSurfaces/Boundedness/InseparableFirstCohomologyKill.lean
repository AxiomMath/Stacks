module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparablePuncturedModification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableFrobeniusFractionField
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableFrobeniusSplittingLocalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CohomologyModelBridge

/-!
# A fixed element of `A` kills `H¹(Y, 𝒪_Y)` for `Y` finite over a rational modification

Let `A` be a Noetherian local normal domain of dimension two and characteristic `p`, with an
additive `θ : A → A` satisfying `θ(aᵖ z) = a θ(z)`, and let `A → B` be a finite injective map of
domains with a lift `ρ : B → A` of the `p`-th power map. Suppose `c ∈ A`, `bᵢ, βᵢ ∈ B` satisfy
`c s = ∑ᵢ θ(ρ(bᵢ) ρ(s)) βᵢ` for all `s ∈ B`
(`Stacks.ResolutionOfSurfaces.exists_smul_eq_sum_frobenius`).

Let `f : X ⟶ Spec A` be a normal modification with `H¹(X, 𝒪_X) = 0`, and `π : Y ⟶ X` finite
surjective with `Y` normal and `g : Y ⟶ Spec B` a modification over `Spec B ⟶ Spec A`. Then
`c` annihilates `H¹(Y, 𝒪_Y)`.

This is the step of [Stacks, Tag 0B4U] where the source invokes duality (Lemmas 0AX6, 0B4T and
0B4S): the Frobenius splitting replaces the trace, and the argument is
`AlgebraicGeometry.SeparableGoUp.rightDerived_map_toSheaf_smulEnd_eq_zero` on the open of `X` over
the punctured spectrum, whose hypotheses are supplied by
`AlgebraicGeometry.SeparableGoUp.surjective_restrict_puncturedPreimage` (Hartogs) and
`AlgebraicGeometry.SeparableGoUp.exists_mul_eq_of_mem_puncturedPreimage`.

## Main results

* `AlgebraicGeometry.SeparableGoUp.smul_firstCohomology_eq_zero_of_frobenius`: the statement
  above.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SeparableGoUp

attribute [local instance] HasDerivedCategory.standard

/-- **A Frobenius splitting kills `H¹(Y, 𝒪_Y)` for `Y` finite over a modification with
`H¹(X, 𝒪_X) = 0`.** With `c s = ∑ᵢ θ(ρ(bᵢ) ρ(s)) βᵢ` on `B`, multiplication by `c` is zero on
`H¹(Y, 𝒪_Y)`. -/
theorem smul_firstCohomology_eq_zero_of_frobenius (A B : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] (p : ℕ) [Fact p.Prime] [CharP A p] (ρ : B → A)
    (hρ : ∀ s, algebraMap A B (ρ s) = s ^ p) (θ : A →+ A) (hθ : ∀ a z, θ (a ^ p * z) = a * θ z)
    (c : A) {n : ℕ} (b β : Fin n → B) (hc : ∀ s : B, c • s = ∑ i, θ (ρ (b i) * ρ s) • β i)
    {X Y : Scheme.{u}} [IsNormal X] [IsNormal Y] (f : X ⟶ Spec (.of A)) (g : Y ⟶ Spec (.of B))
    (π : Y ⟶ X) [IsFinite π] [Surjective π] (hf : IsModification f) (hg : IsModification g)
    (hcomm : π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (hX : IsZeroFirstStructureSheafCohomology X) (x : firstCohomologyAsBaseModule Y g) :
    algebraMap A B c • x = 0 := by
  have : IsIntegral X := hf.source_isIntegral
  have : IsIntegral Y := hg.source_isIntegral
  let : Algebra A X.functionField := baseFunctionFieldAlgebra f
  let : Algebra B Y.functionField := baseFunctionFieldAlgebra g
  let : Algebra X.functionField Y.functionField := functionFieldAlgebra π
  let : Algebra A Y.functionField :=
    ((algebraMap B Y.functionField).comp (algebraMap A B)).toAlgebra
  have : IsFractionRing A X.functionField := isFractionRing_of_isBirational f hf.isBirational
  have : IsFractionRing B Y.functionField := isFractionRing_of_isBirational g hg.isBirational
  have : IsScalarTower A B Y.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A X.functionField Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    change Y.presheaf.germ ⊤ (genericPoint Y) trivial (baseSection Y g (algebraMap A B a)) =
      dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial (baseSection X f a))
    rw [← baseSection_comp f g π hcomm]
    exact (dominantFunctionFieldMap_germ π ⊤ trivial _).symm
  have hAK : Function.Injective (algebraMap A X.functionField) :=
    IsFractionRing.injective A X.functionField
  have : CharP X.functionField p := charP_of_injective_algebraMap hAK p
  have hdom : ∀ k : X.functionField,
      dominantFunctionFieldMap π k = algebraMap X.functionField Y.functionField k := fun _ => rfl
  -- `Lᵖ ⊆ K`
  have hpow : ∀ y : Y.functionField, ∃ k : X.functionField,
      dominantFunctionFieldMap π k = y ^ p := by
    intro y
    obtain ⟨s, t, -, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    refine ⟨algebraMap A X.functionField (ρ s) / algebraMap A X.functionField (ρ t), ?_⟩
    have hL : ∀ r : B, algebraMap X.functionField Y.functionField
        (algebraMap A X.functionField (ρ r)) = algebraMap B Y.functionField r ^ p := fun r => by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B Y.functionField,
        hρ, map_pow]
    rw [hdom, map_div₀, hL, hL, div_pow]
  -- the splitting on the function field of `X`
  obtain ⟨θK, hθKp, hθKf⟩ := Stacks.ResolutionOfSurfaces.exists_frobeniusSplitting_fractionRing
    (K := X.functionField) (Fact.out : p.Prime).one_lt.le θ hθ
  have hθKA : ∀ z, θK (algebraMap A X.functionField z) = algebraMap A X.functionField (θ z) := by
    intro z
    have := hθKf z 1 one_ne_zero
    simpa using this
  -- the open over the punctured spectrum
  have := nonempty_puncturedPreimage f hdim hf
  have hθstalk := exists_algebraMap_eq_thetaK f (puncturedPreimage f) θ θK (p := p)
    (fun z s hs => hθKf z s hs) (exists_mul_eq_of_mem_puncturedPreimage f hdim hf)
  have hXab : IsZero (((sectionsAb X).rightDerived 1).obj (unitAb X)) :=
    isZero_rightDerived_unitAb X
      ((isZeroFirstStructureSheafCohomology_iff_isZero_rightDerived X).1 hX)
  have hkill := rightDerived_map_toSheaf_smulEnd_eq_zero π p hpow (puncturedPreimage f) θK
    hθstalk (fun i => baseSection Y g (b i)) (fun i => baseSection Y g (β i)) (baseSection X f c)
    (fun σ k hk => by
      have h := Stacks.ResolutionOfSurfaces.smul_eq_sum_frobeniusSplitting_fractionRing
        (K := X.functionField) (L := Y.functionField) ρ hρ θ θK hθKp hθKA c b β hc σ k hk
      rw [IsScalarTower.algebraMap_apply A X.functionField Y.functionField] at h
      exact h) hXab (surjective_restrict_puncturedPreimage f hdim hf)
  have hmod := rightDerived_map_eq_zero_of_toSheaf X _ hkill
  -- transport to `H¹(Y, 𝒪_Y)`
  let E := firstCohomologyPushforwardEquiv f π
  let x' : firstCohomologyAsBaseModule Y (π ≫ f) := x
  have hx : c • x' = 0 := by
    apply E.injective
    rw [map_smul, map_zero]
    let y : ((Scheme.sectionsFunctor X).rightDerived 1).obj
        ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf)) := E x'
    change baseSection X f c • y = 0
    rw [← Scheme.rightDerived_sectionsFunctor_map_smulEnd_apply X (baseSection X f c) 1 _ y,
      hmod]
    rfl
  let x'' : ((Scheme.sectionsFunctor Y).rightDerived 1).obj (SheafOfModules.unit Y.ringCatSheaf) :=
    x
  change baseSection Y g (algebraMap A B c) • x'' = 0
  rw [← baseSection_comp f g π hcomm]
  exact hx

end AlgebraicGeometry.SeparableGoUp

end
