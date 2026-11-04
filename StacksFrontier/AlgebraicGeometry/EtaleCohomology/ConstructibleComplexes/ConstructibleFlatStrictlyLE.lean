module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekSumResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The constructible flat resolution of Tag 0960 with its upper bound kept

An object of `D(X_étale, Λ)` with constructible cohomology sheaves vanishing above `b` is
represented by a complex of constructible flat sheaves of `Λ`-modules which is strictly `LE b`.
This sharpens the implication (1) ⟹ (3) of Tag 0960, whose representing complex
(`Stacks.EtaleCohomology.IsRepresentedByBoundedAboveConstructibleFlatComplex`) is only bounded
above; a representative concentrated in an interval `[a, b]`, as in condition (2) of Tag 03TT,
needs the bound `b`.

## Main results

* `Stacks.EtaleCohomology.exists_isStrictlyLE_constructibleFlatComplex_of_isConstructible`:
  **Tag 0960, the implication (1) ⟹ (3), with the upper bound of the hypothesis carried into
  the conclusion.** An object of `D(X_étale, Λ)` with constructible cohomology sheaves vanishing
  above `b`, on a quasi-compact and quasi-separated `X` over a Noetherian `Λ`, is represented by
  a complex of constructible flat sheaves of `Λ`-modules which vanishes in every degree above
  `b`.

## Implementation notes

The coefficient universe is `max (u + 1) r`, the one extension by zero forces in Tag 095Z and
the one Tag 0960 is stated at.

## References

* [Stacks Project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)]

/-- **Tag 0960, the implication (1) ⟹ (3), with the upper bound carried into the conclusion.**
An object of `D(X_étale, Λ)` with constructible cohomology sheaves vanishing above `b` is
represented by a complex of constructible flat sheaves of `Λ`-modules vanishing in every degree
above `b`. -/
@[sga "4½ Rapport 4.7" "partial"]
public theorem exists_isStrictlyLE_constructibleFlatComplex_of_isConstructible
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))) (hK : IsConstructible B X Λ K) (b : ℤ)
    (hvan : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) i).obj K)) :
    ∃ L : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) ℤ,
      L.IsStrictlyLE b ∧ (∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (L.X i)) ∧
        Nonempty (DerivedCategory.Q.obj L ≅ K) := by
  have := isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ
  set P := isConstructibleModuleSheafProperty.{u, max (u + 1) r, r} B X Λ
  have hLE : K.IsLE b := by rw [DerivedCategory.isLE_iff]; exact hvan
  obtain ⟨A, hA, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  have hAhom : ∀ i : ℤ, P (A.homology i) := fun i =>
    P.prop_of_iso
      ((((DerivedCategory.homologyFunctorFactors _ i).app A).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e.symm).symm) (hK i)
  obtain ⟨Y, hY, f, hf, hterms⟩ :=
    Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis
      P (IsAffineShriekSum.{u, r} B X Λ) A
      (coversEpis_isAffineShriekSum B X Λ)
      (isAffineShriekSum_zero B X Λ)
      (fun _ _ => isAffineShriekSum_biprod B X Λ)
      (fun _ _ g _ hM => isAffineShriekSum_of_iso B X Λ (asIso g) hM)
      b hAhom
  refine ⟨Y, hY, fun i => ?_, ⟨asIso (DerivedCategory.Q.map f) ≪≫ e.symm⟩⟩
  obtain ⟨n, U, hU, ⟨eU⟩⟩ := hterms i
  exact isConstructibleFlatModuleSheaf_congr B X Λ eU.symm
    (isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant_of_quasiSeparated B X Λ U hU)

end Stacks.EtaleCohomology

end
