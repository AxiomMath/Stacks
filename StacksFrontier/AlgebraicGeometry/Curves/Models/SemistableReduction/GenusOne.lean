module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelExistence
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelSituation
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.GenusOneLocal
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.HigherGenusLocal
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.HigherGenusReduction

/-!
# Semistable reduction in genus one

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a smooth projective
curve of genus one over `K` with `H⁰(C, 𝒪_C) = K`. Section 0CEG of the Stacks project proves
clause (2) of the semistable reduction theorem (Tag 0CDN): there is a finite separable extension
`K'/K` such that `C_{K'}` has semistable reduction over `R'_𝔪` for every maximal ideal `𝔪` of the
integral closure `R'` of `R` in `K'`, and the special fibre of the minimal model of `C_{K'}` over
`R'_𝔪` is a smooth curve of genus one or a cycle of rational curves.

## Main definitions

* `Stacks.Models.HasGenusOneMinimalFibresAtMaximalIdeals` — for every maximal ideal `𝔪` of `R'`,
  the special fibre of every minimal model of `C'` over `R'_𝔪` is a smooth curve of genus one or a
  cycle of rational curves.

## Main results

* `Stacks.Models.exists_genusOne_semistableReduction_of_statements` — clause (2) of Tag 0CDN, with
  the statements of Tags 0CA6, 0CDU (1), 0CE6, 0C20 and 0C6U as premises.

## References

* [Stacks Project, Section 0CEG](https://stacks.math.columbia.edu/tag/0CEG)
* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] AddSubgroup.torsionBy.zmodModule

namespace Stacks.Models

variable (R : Type u) [CommRing R] (K' : Type u) [Field K'] [Algebra R K']

/-- **The minimal models over every localization of the integral closure have special fibre a
smooth curve of genus one or a cycle of rational curves.** Let `R'` be the integral closure of
`R` in the field `K'` and `C'` a smooth projective curve over `K'` with `H⁰(C', 𝒪) = K'`. For every
maximal ideal `𝔪` of `R'`, every localization `A` of `R'` at `𝔪` which is a discrete valuation ring
with fraction field `K'`, and every minimal model `X` of `C'` over `A`, the special fibre of `X` is
a smooth curve of genus one or a cycle of rational curves, read in the standing situation of Tag
0C61 attached to `X` (`Stacks.Models.regularProperModelSituation`). -/
def HasGenusOneMinimalFibresAtMaximalIdeals {C' : Scheme.{u}} (c' : C' ⟶ Spec (.of K'))
    [IsCurve K' c'] [Smooth c'] : Prop :=
  ∀ (𝔪 : Ideal (integralClosure R K')) [𝔪.IsMaximal] (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra (integralClosure R K') A] [IsLocalization.AtPrime A 𝔪]
    [Algebra A K'] [IsFractionRing A K'] [IsScalarTower (integralClosure R K') A K']
    (X : Scheme.{u}) (p : X ⟶ Spec (.of A))
    (e : C' ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap A K'))))
    (hmin : IsMinimalModel c' p e),
    haveI := hmin.isProper
    haveI := hmin.isIso_globalSections
    (regularProperModelSituation c' hmin.curveProjective p e hmin.isModel
        hmin.regular).IsSmoothGenusOneSpecialFiber ∨
      (regularProperModelSituation c' hmin.curveProjective p e hmin.isModel
        hmin.regular).IsCycleOfRationalCurves

/-- **Semistable reduction in genus one** (clause (2) of [Stacks, Tag 0CDN]). Let `R` be a discrete
valuation ring with fraction field `K` and `C` a smooth projective curve of genus one over `K`
with `H⁰(C, 𝒪_C) = K`. Then there is a finite separable extension `K'/K` such that `C_{K'}` has
semistable reduction over `R'_𝔪` for every maximal ideal `𝔪` of the integral closure `R'` of `R`
in `K'`, and the special fibre of every minimal model of `C_{K'}` over `R'_𝔪` is a smooth curve of
genus one or a cycle of rational curves, given the statements of [Stacks, Tags 0CA6, 0CDU (1),
0CE6, 0C20 and 0C6U] as the premises `h0CA6`, `h0CDU`, `h0CE6`, `h0C20`, `h0C20eq` and
`h0C6U`. -/
theorem exists_genusOne_semistableReduction_of_statements
    (h0CA6 : ∀ (S : RegularProperModelSituation.{u}), ¬ S.X.HasExceptionalCurveOfFirstKind →
      ∀ (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber),
        NumericalType.IsMinimal (S.associatedNumericalType n e))
    (h0CDU : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
      [Smooth f] [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (n : ℕ),
      IsUnit (n : k) → genus f = 1 →
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
        Algebra.IsSeparable k k' ∧
        (∃ x : Spec (.of k') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))),
          x ≫ pullback.snd _ _ = 𝟙 _) ∧
        Nonempty (AddSubgroup.torsionBy (Stacks.Picard.ofScheme
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) (n : ℤ) ≃+
          (Fin 2 → ZMod n)))
    (h0CE6 : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
      (_ : topologicalKrullDim (X : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime] (_ : IsUnit (ℓ : k)),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ≤
          genus g + geometricGenus k g)
    (h0C20 : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] [IsReduced X] (_hdim : topologicalKrullDim (X : Type u) = 1)
      (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ≤
          genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)))
    (h0C20eq : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [IsReduced X]
      (_hdim : topologicalKrullDim (X : Type u) = 1) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        (Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) =
            genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)) ↔
          ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
            Stacks.Curves.IsMulticrossSingularity k X x))
    (h0C6U : ∀ (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
      [IsCurve k f] [Smooth f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)],
      genus f = 0 → (∃ x, IsRationalPoint f x) →
        Nonempty (Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))))
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
    (hproj : IsProjective c) [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    (hg : genus c = 1) :
    haveI : IsProper c := hproj.isProper
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
      HasSemistableReductionAtMaximalIdeals R K'
        (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
        (hproj.pullback_snd _) ∧
      HasGenusOneMinimalFibresAtMaximalIdeals R K'
        (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K')))) := by
  have : IsProper c := hproj.isProper
  obtain ⟨ℓ, hℓ, hℓ6, -, hℓk⟩ := exists_prime_lt_le_nth_ne_zero (IsLocalRing.ResidueField R) 6
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓR : IsUnit (ℓ : R) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
    exact hℓk
  have hℓK : IsUnit (ℓ : K) := by simpa using hℓR.map (algebraMap R K)
  obtain ⟨K', _, _, hfin, hsep, ⟨x, hx⟩, ⟨τ⟩⟩ := h0CDU K c ℓ hℓK hg
  let : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hlocal : ∀ (𝔪 : Ideal (integralClosure R K')) [𝔪.IsMaximal] (A : Type u) [CommRing A]
      [IsDomain A] [IsDiscreteValuationRing A] [Algebra (integralClosure R K') A]
      [IsLocalization.AtPrime A 𝔪] [Algebra A K'] [IsFractionRing A K']
      [IsScalarTower (integralClosure R K') A K'] (X : Scheme.{u}) (p : X ⟶ Spec (.of A))
      (e : pullback c (Spec.map (CommRingCat.ofHom (algebraMap K K'))) ≅
        pullback p (Spec.map (CommRingCat.ofHom (algebraMap A K'))))
      (hmin : IsMinimalModel (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
        p e),
      have := hmin.isProper
      have := hmin.isIso_globalSections
      IsAtWorstNodalOfRelativeDimensionOne p ∧
        ((regularProperModelSituation _ hmin.curveProjective p e hmin.isModel
            hmin.regular).IsSmoothGenusOneSpecialFiber ∨
          (regularProperModelSituation _ hmin.curveProjective p e hmin.isModel
            hmin.regular).IsCycleOfRationalCurves) := by
    intro 𝔪 _ A _ _ _ _ _ _ _ _ X p e hmin
    have := hmin.isProper
    have := hmin.isIso_globalSections
    set S := regularProperModelSituation _ hmin.curveProjective p e hmin.isModel hmin.regular
      with hS
    have hexc : ¬ S.X.HasExceptionalCurveOfFirstKind := hmin.not_hasExceptionalCurveOfFirstKind
    have hgen : genus S.C_to_K = genus c := genus_pullback_snd_eq K K' (algebraMap K K') c
    have hk : (ℓ : S.k) ≠ 0 := by
      have hA : IsUnit (ℓ : A) := by
        simpa using (hℓR.map (algebraMap R (integralClosure R K'))).map
          (algebraMap (integralClosure R K') A)
      show (ℓ : IsLocalRing.ResidueField A) ≠ 0
      rw [← map_natCast (IsLocalRing.residue A)]
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hA
    have hτ : Nonempty (AddSubgroup.torsionBy (Stacks.Picard.ofScheme S.C) (ℓ : ℤ) ≃+
        (Fin 2 → ZMod ℓ)) := ⟨τ⟩
    obtain ⟨-, -, hgX⟩ := S.exists_isRationalPoint_smoothAt_specialFiber_and_genus_eq x hx
    have hle := genus_comp_le_of_isClosedImmersion S.k S.specialFiberToSpec
      (S.topologicalKrullDim_specialFiber S.nonempty_specialFiber).le S.specialFiber.reductionι
    have h1red : Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) ≤ 1 := by
      rw [← (structureSheafCohomologyIsoCohomologyOverField S.k _ 1).toLinearEquiv.finrank_eq,
        ← genus_eq_finrank_structureSheafCohomology]
      rw [hgX, hgen, hg] at hle
      exact hle
    exact S.genusOne_local h0CE6 h0C20 h0C20eq h0C6U (h0CA6 S hexc) h1red (hgen.trans hg) x hx
      ℓ (by omega) hk hτ
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, hfin, hsep, ?_, ?_⟩
  · intro 𝔪 _ A _ _ _ _ _ _ _ _
    obtain ⟨X, p, e, hmin⟩ := exists_isMinimalModel (R := A)
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
      (HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one
        _ (IsCurve.topologicalKrullDim_eq_one (k := K')
          (f := pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))).le)
      inferInstance
    have := hmin.isProper
    exact ⟨X, p, e, hmin.isModel, hmin.isProper, (hlocal 𝔪 A X p e hmin).1⟩
  · intro 𝔪 _ A _ _ _ _ _ _ _ _ X p e hmin
    exact (hlocal 𝔪 A X p e hmin).2

end Stacks.Models

end
