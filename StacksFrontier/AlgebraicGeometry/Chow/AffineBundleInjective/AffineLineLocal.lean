module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLine
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.Induction

/-!
# From `Spec A[T] ⟶ Spec A` to the affine line over an arbitrary base

Let `(S, δ)` be the base situation of chapter 42 and `T` a scheme locally of finite type over `S`.
Every point of `T` has an affine open neighbourhood `V ≅ Spec A`, over which the affine line
`𝔸¹_T ⟶ T` restricts to `𝔸¹_V ⟶ V`, isomorphic to `Spec A[X] ⟶ Spec A`. This gives a square of
open immersions from `Spec A[X] ⟶ Spec A` to `𝔸¹_T ⟶ T` in which `Spec A[X]` is the whole
inverse image of `Spec A`, along which the fibrewise properties of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.FibreStatements` and the discreteness
of the valuations at the closed points of the fibres pass.

## Main results

* `Stacks.Chow.exists_specPolynomial_square_affineLine` — the square of open immersions.
* `Stacks.Chow.hasFibreProperties_affineLine_of_specPolynomial` — the fibrewise properties of the
  affine line from those of `Spec A[X] ⟶ Spec A`.
* `Stacks.Chow.isDiscreteValuationRing_affineLine_of_specPolynomial` — the discrete valuation
  rings at the closed points of the fibres of the affine line, from those of `Spec A[X]`.

## References

* [Stacks Project, Tag 0GUB](https://stacks.math.columbia.edu/tag/0GUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-- **The affine line is locally `Spec A[X] ⟶ Spec A`**: every point of `T` lies in the image of
an open immersion `Spec A ⟶ T` under which the affine line restricts to `Spec A[X]`, by a square
of open immersions whose upper corner is the whole inverse image. -/
theorem exists_specPolynomial_square_affineLine (T : Scheme.{u}) (x : T) :
    ∃ (R : CommRingCat.{u}) (jX : Spec (CommRingCat.of (Polynomial R)) ⟶
        𝔸(ULift.{u} (Fin 1); T)) (_ : IsOpenImmersion jX) (jY : Spec R ⟶ T)
        (_ : IsOpenImmersion jY),
      jX ≫ (𝔸(ULift.{u} (Fin 1); T) ↘ T) =
          Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ jY ∧
        (𝔸(ULift.{u} (Fin 1); T) ↘ T).base ⁻¹' Set.range jY.base ⊆ Set.range jX.base ∧
        x ∈ Set.range jY.base := by
  obtain ⟨-, ⟨V₀, hV, rfl⟩, hxV, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : T.Opens := V₀
  change IsAffineOpen V at hV
  change x ∈ V at hxV
  set R : CommRingCat.{u} := Γ(T, V)
  set φ := hV.isoSpec
  have Hpb := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) V.ι
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin 1)) V.ι) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) Hpb.flip inferInstance
  have Hpb3 := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) φ.inv
  have : IsIso (AffineSpace.map (ULift.{u} (Fin 1)) φ.inv) := Hpb3.isIso_fst_of_isIso
  set mA3 := specPolynomialToAffineLine R ≫ AffineSpace.map (ULift.{u} (Fin 1)) φ.inv
  have : IsIso mA3 := inferInstance
  refine ⟨R, mA3 ≫ AffineSpace.map (ULift.{u} (Fin 1)) V.ι, inferInstance, φ.inv ≫ V.ι,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, Category.assoc mA3,
      ← Category.assoc, Category.assoc (specPolynomialToAffineLine R),
      AffineSpace.map_over, specPolynomialToAffineLine_over_assoc, Category.assoc]
  · intro z hz
    have hrange := range_fst_of_isPullback Hpb
    have hzV : z ∈ Set.range (AffineSpace.map (ULift.{u} (Fin 1)) V.ι).base := by
      rw [hrange]
      obtain ⟨t, ht⟩ := hz
      refine ⟨φ.inv t, ?_⟩
      rw [← ht]
      rfl
    obtain ⟨z', rfl⟩ := hzV
    refine ⟨(inv mA3) z', ?_⟩
    show ((inv mA3 ≫ mA3) ≫ AffineSpace.map (ULift.{u} (Fin 1)) V.ι) z' = _
    rw [IsIso.inv_hom_id, Category.id_comp]
  · refine ⟨φ.hom ⟨x, hxV⟩, ?_⟩
    show (φ.hom ≫ φ.inv ≫ V.ι) ⟨x, hxV⟩ = x
    rw [Iso.hom_inv_id_assoc]
    rfl

variable (C : ChowSituation.{u})

/-- **The fibrewise properties of the affine line, from those of `Spec A[X] ⟶ Spec A`.** -/
theorem hasFibreProperties_affineLine_of_specPolynomial
    (hL : ∀ (R : CommRingCat.{u}) (sV : Spec R ⟶ C.S) [LocallyOfFiniteType sV] (k : ℤ)
      (y : Spec R), FibreBoundaryLift C
        (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ sV) sV
        (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) 1 k y)
    (hU : ∀ (R : CommRingCat.{u}) (sV : Spec R ⟶ C.S) [LocallyOfFiniteType sV] (k : ℤ)
      (y : Spec R), FibreUnitDescent C
        (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ sV) sV
        (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) 1 k y)
    (T : Scheme.{u}) (sT : T ⟶ C.S) [LocallyOfFiniteType sT] :
    HasFibreProperties C ((𝔸(ULift.{u} (Fin 1); T) ↘ T) ≫ sT) sT
      (𝔸(ULift.{u} (Fin 1); T) ↘ T) 1 := by
  intro k x
  obtain ⟨R, jX, _, jY, _, hsq, hpre, ⟨y', rfl⟩⟩ := exists_specPolynomial_square_affineLine T x
  have hX : jX ≫ ((𝔸(ULift.{u} (Fin 1); T) ↘ T) ≫ sT) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ (jY ≫ sT) := by
    rw [← Category.assoc, hsq, Category.assoc]
  exact ⟨fibreBoundaryLift_of_openSquare C _ sT _ _ jX jY hsq hpre hX rfl 1 k y'
      (hL R (jY ≫ sT) k y'),
    fibreUnitDescent_of_openSquare C _ sT _ _ jX jY hsq hpre hX rfl 1 k y'
      (hU R (jY ≫ sT) k y')⟩

/-- **The local rings at the closed points of the fibres of the affine line are discrete
valuation rings**, given the same statement for `Spec A[X] ⟶ Spec A`. -/
theorem isDiscreteValuationRing_affineLine_of_specPolynomial
    (hdvr : ∀ (R : CommRingCat.{u}) {ζ w : Spec (CommRingCat.of (Polynomial R))} (hw : ζ ⤳ w),
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))).base ζ =
        (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))).base w → ζ ≠ w →
      IsDiscreteValuationRing ((integralComponentAt ζ).subscheme.presheaf.stalk
        (pointClosurePoint ζ (specializes_iff_mem_closure.mp hw))))
    (T : Scheme.{u}) (ζ w : 𝔸(ULift.{u} (Fin 1); T)) (hw : ζ ⤳ w)
    (hfib : (𝔸(ULift.{u} (Fin 1); T) ↘ T).base ζ = (𝔸(ULift.{u} (Fin 1); T) ↘ T).base w)
    (hne : ζ ≠ w) :
    IsDiscreteValuationRing ((integralComponentAt ζ).subscheme.presheaf.stalk
      (pointClosurePoint ζ (specializes_iff_mem_closure.mp hw))) := by
  obtain ⟨R, jX, _, jY, _, hsq, hpre, hx⟩ :=
    exists_specPolynomial_square_affineLine T ((𝔸(ULift.{u} (Fin 1); T) ↘ T).base w)
  obtain ⟨w', rfl⟩ := hpre hx
  obtain ⟨ζ', rfl⟩ := hpre (show _ ∈ Set.range jY.base by rw [hfib]; exact hx)
  have hw' : ζ' ⤳ w' := jX.isOpenEmbedding.isInducing.specializes_iff.mp hw
  have hpt : ∀ t, jY.base ((Spec.map (CommRingCat.ofHom
      (Polynomial.C : R →+* Polynomial R))).base t) =
      (𝔸(ULift.{u} (Fin 1); T) ↘ T).base (jX.base t) := fun t ↦
    (congrArg (fun g : Spec (CommRingCat.of (Polynomial R)) ⟶ T ↦ g.base t) hsq).symm
  have hfib' : (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))).base ζ' =
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))).base w' :=
    jY.isOpenEmbedding.injective (by rw [hpt, hpt, hfib])
  have hne' : ζ' ≠ w' := fun h ↦ hne (by rw [h])
  have hD := hdvr R hw' hfib' hne'
  set ψ := pointClosureOpenComparison jX ζ'
  have hψ := pointClosureOpenComparison_subschemeι jX ζ'
  have hP := pointClosureComparison_pointClosurePoint jX ζ' ψ hψ
    (specializes_iff_mem_closure.mp hw') (specializes_iff_mem_closure.mp hw)
  rw [← hP]
  have : IsIso (ψ.stalkMap (pointClosurePoint ζ' (specializes_iff_mem_closure.mp hw'))) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (asIso (ψ.stalkMap
      (pointClosurePoint ζ' (specializes_iff_mem_closure.mp hw')))).symm.commRingCatIsoToRingEquiv

end Stacks.Chow

end
