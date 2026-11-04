module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodChartSubschemeCohomology
public import StacksFrontier.Homology.Eta.Perfect.QuotientEtaRank

/-!
# The ranks of the cohomology of `Li^*Lη_I M` on the closed subscheme of Tag 0GTZ

Let `(X, D, M)` be a good triple, `T ⊆ D` the closed subscheme of More on Flatness, Tag 0GTZ and
`i : T ⟶ X` its inclusion.  At a point `t ∈ T` whose image `x` lies in the locus `W` where the
cohomology sheaves of `M` are locally free, the stalk `H^n(Li^*Lη_I M)_t` is free over `𝒪_{T,t}`
of the rank of `H^n(M)_x` over `𝒪_{X,x}`: this is part (3) of Tag 0GTZ.

Over a good chart `(U, A, f, M^•)` inside `W` through `x` the closed subscheme `T ∩ U` is
`Spec(A ⧸ fA)`, and `H^n(Li^*Lη_I M)_t` is `𝒪_{T,t} ⊗ H^n(η_f M^• ⊗_A A ⧸ fA)`, which the
cohomology computation of Tag 0GTA identifies with the reduction of `H^n(M^•)_x`.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.free_finrank_stalk_homology_goodChartSubscheme`:
  part (3) of Tag 0GTZ.

## References

* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0GTA](https://stacks.math.columbia.edu/tag/0GTA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u

/-- Freeness and finiteness transported along a linear equivalence, with the two module
structures read off the equivalence. -/
private theorem free_finite_of_linearEquiv {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] (iM : Module R M) (iN : Module R N) (e : M ≃ₗ[R] N)
    (h : Module.Free R M ∧ Module.Finite R M) : Module.Free R N ∧ Module.Finite R N :=
  have := h.1
  have := h.2
  ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

/-- Freeness transported along a linear equivalence, with the two module structures read off
the equivalence. -/
private theorem free_of_linearEquiv {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] (iM : Module R M) (iN : Module R N) (e : M ≃ₗ[R] N)
    (h : Module.Free R M) : Module.Free R N :=
  Module.Free.of_equiv e

/-- The rank is invariant under a linear equivalence, with the two module structures read off
the equivalence. -/
private theorem finrank_eq_of_linearEquiv {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] (iM : Module R M) (iN : Module R N) (e : M ≃ₗ[R] N) :
    Module.finrank R M = Module.finrank R N :=
  e.finrank_eq

namespace AlgebraicGeometry.ComplexAndDivisorSituation

open Stacks.Divisors.Eta (derivedEtaData)

variable {X : Scheme.{u}} (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
  (M : DerivedCategory X.Modules) (hM : RingedSpace.IsPerfect (X := X.toRingedSpace) M)

include hD in
/-- **Stacks Tag 0GTZ, part (3).**  For a good triple `(X, D, M)`, the closed subscheme
`i : T ⟶ D ⟶ X` of Tag 0GTZ and a point `t ∈ T` whose image `x` lies in the locus where the
cohomology sheaves of `M` are locally free, `H^n(Li^*Lη_I M)_t` is a free `𝒪_{T,t}`-module of the
rank of `H^n(M)_x` over `𝒪_{X,x}`. -/
theorem free_finrank_stalk_homology_goodChartSubscheme
    (hS : (standardSituation D hD M hM).IsGoodTriple) (n : ℤ)
    (t : ((standardSituation D hD M hM).goodChartSubscheme hS).subscheme)
    (hx : goodChartSubschemeIncl hS t ∈ (standardSituation D hD M hM).locallyFreeLocus) :
    letI F := (DerivedCategory.homologyFunctor
        ((standardSituation D hD M hM).goodChartSubscheme hS).subscheme.Modules n).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (goodChartSubschemeIncl hS).toLRSHom.toShHom).obj ((derivedEtaData D).functor.obj M))
    letI G := (DerivedCategory.homologyFunctor X.Modules n).obj M
    letI : Module (ToType (TopCat.Presheaf.stalk (((standardSituation D hD M hM).goodChartSubscheme
        hS).subscheme).presheaf t)) (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) :=
      RingedSpace.moduleStalk (X := (((standardSituation D hD M hM).goodChartSubscheme
        hS).subscheme).toRingedSpace) F t
    letI : Module (ToType (X.presheaf.stalk (goodChartSubschemeIncl hS t)))
        (ToType (TopCat.Presheaf.stalk G.val.presheaf (goodChartSubschemeIncl hS t))) :=
      RingedSpace.moduleStalk (X := X.toRingedSpace) G (goodChartSubschemeIncl hS t)
    Module.Free (ToType (TopCat.Presheaf.stalk (((standardSituation D hD M hM).goodChartSubscheme
        hS).subscheme).presheaf t)) (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) ∧
      Module.finrank (ToType (TopCat.Presheaf.stalk
          (((standardSituation D hD M hM).goodChartSubscheme hS).subscheme).presheaf t))
          (ToType (TopCat.Presheaf.stalk F.val.presheaf t)) =
        Module.finrank (ToType (X.presheaf.stalk (goodChartSubschemeIncl hS t)))
          (ToType (TopCat.Presheaf.stalk G.val.presheaf (goodChartSubschemeIncl hS t))) := by
  let : Module (ToType (TopCat.Presheaf.stalk (((standardSituation D hD M hM).goodChartSubscheme
      hS).subscheme).presheaf t)) (ToType (TopCat.Presheaf.stalk
        ((DerivedCategory.homologyFunctor
          ((standardSituation D hD M hM).goodChartSubscheme hS).subscheme.Modules n).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            (goodChartSubschemeIncl hS).toLRSHom.toShHom).obj
              ((derivedEtaData D).functor.obj M))).val.presheaf t)) :=
    RingedSpace.moduleStalk (X := (((standardSituation D hD M hM).goodChartSubscheme
      hS).subscheme).toRingedSpace) _ t
  have hxD : goodChartSubschemeIncl hS t ∈ (standardSituation D hD M hM).D.supportSet :=
    (standardSituation D hD M hM).D.mem_supportSet_subschemeι
      (((standardSituation D hD M hM).goodChartSubscheme hS).subschemeι t)
  obtain ⟨C, hI, hxU, hCW⟩ := (standardSituation D hD M hM).exists_good_chart_le_locallyFreeLocus
    hS _ hxD hx
  let T := (standardSituation D hD M hM).goodChartSubscheme hS
  let x := goodChartSubschemeIncl hS t
  let V := C.subschemeChartOpen hS
  have ht : t ∈ (V : T.subscheme.Opens) := hxU
  let B := Γ(T.subscheme, V.1)
  let φ : Γ(X, C.U) →+* B := C.subschemeSectionMap hS
  have hker : RingHom.ker φ = Ideal.span {C.f} :=
    C.ker_subschemeSectionMap_of_le_locallyFreeLocus hS hI hCW
  -- the model of `Li^*Lη_I M` on `T ∩ U`
  let e := restrictDerivedPullbackTildeModelIso (goodChartSubschemeIncl hS) C.U.2 V.2
    (C.subschemeChartOpen_le hS) _ C.etaComplex
    (Stacks.Eta.GoodBaseChange.kFlat_etaObject_toCochainComplex C.complex C.f C.regular hI)
    (C.etaChartModelIso D hD M hM)
  let eT := stalkHomologyTildeModelEquiv V.2 _ _ e n t ht
  let eX := stalkHomologyTildeModelEquiv C.U.2 M _ C.representsDerivedIso n x hxU
  let := (Stacks.Duality.affineGermRingHom V.2 t ht).toAlgebra
  let := (Stacks.Duality.affineGermRingHom C.U.2 x hxU).toAlgebra
  have := Stacks.Duality.isLocalization_affineGermRingHom V.2 t ht
  have := Stacks.Duality.isLocalization_affineGermRingHom C.U.2 x hxU
  have hfree : ∀ i, Module.Free (ToType (X.presheaf.stalk x))
      (ToType (X.presheaf.stalk x) ⊗[Γ(X, C.U)] C.complex.toCochainComplex.homology i) ∧
      Module.Finite (ToType (X.presheaf.stalk x))
        (ToType (X.presheaf.stalk x) ⊗[Γ(X, C.U)] C.complex.toCochainComplex.homology i) :=
    fun i => free_finite_of_linearEquiv _ _
      (stalkHomologyTildeModelEquiv C.U.2 M _ C.representsDerivedIso i x hxU)
      (((standardSituation D hD M hM).mem_locallyFreeLocus_iff x).mp hx i)
  have hq := IsAffineOpen.comap_primeIdealOf_appLE (f := goodChartSubschemeIncl hS)
    C.U.1 C.U.2 V.1 V.2 (C.subschemeChartOpen_le hS) ht
  have hq' : (V.2.primeIdealOf ⟨t, ht⟩).asIdeal.comap φ =
      (C.U.2.primeIdealOf ⟨x, hxU⟩).asIdeal := congrArg PrimeSpectrum.asIdeal hq
  obtain ⟨h1, h2⟩ :=
    Stacks.Eta.QuotientHomology.free_finrank_tensor_homology_extendScalars_etaObject
      (R := ToType (X.presheaf.stalk x)) (L := ToType (T.subscheme.presheaf.stalk t))
      C.f C.regular (C.U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
      C.complex.toCochainComplex
      (fun i => Module.Flat.isSMulRegular_of_isRegular
        (M := Fin (C.complex.rank i) → Γ(X, C.U)) C.regular) hfree φ
      (C.surjective_subschemeSectionMap hS) hker
      (V.2.primeIdealOf ⟨t, ht⟩).asIdeal hq' n
  exact ⟨free_of_linearEquiv _ _ eT.symm h1,
    ((finrank_eq_of_linearEquiv _ _ eT).trans h2).trans
      (finrank_eq_of_linearEquiv _ _ eX).symm⟩

end AlgebraicGeometry.ComplexAndDivisorSituation
