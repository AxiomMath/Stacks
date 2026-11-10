module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportShortExactHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicLimitWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle

/-!
# Excision for towers of sheaves and weights of the ℓ-adic limit

Let `X` be a scheme over a finite field `k` with a compactification `j`, `i : Z ⟶ X` a closed
immersion and `j_U : U ⟶ X` the open immersion of its complement.  For a sheaf `G` of
`Λ`-modules on `X_étale` the open–closed sequence `0 → j_{U!} j_U⁻¹ G → G → i_* i⁻¹ G → 0`
(Tag 095L) gives, through the distinguished triangle of `RΓ_c(X_k̄, -)`, exact sequences

`Hⁱ_c(X_k̄, j_{U!} j_U⁻¹ G) → Hⁱ_c(X_k̄, G) → Hⁱ_c(X_k̄, i_* i⁻¹ G)`

natural in `G` and commuting with the canonical geometric Frobenius.  Applied to the levels of an
ℓ-adic sheaf (a tower of sheaves of `ℤ_ℓ`-modules) and passed to the rational ℓ-adic limit, a
bound on the absolute values of the Frobenius characteristic roots of the two outer terms gives
the same bound on the middle term.  This is the dévissage step of the reduction of the weight
bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3) to
curves, on the ambient scheme `X`; the outer terms are then identified with the compactly
supported cohomology of `U` and of `Z`.

## Main definitions

* `Stacks.EtaleCohomology.compactSupportSheafCohomology`: `G ↦ Hⁱ_c(X_k̄, G)` on sheaves of
  `Λ`-modules on `X_étale`, `G` placed in degree `0`.
* `Stacks.EtaleCohomology.compactSupportSheafFrobenius`: the canonical `π_X^*` on it.

## Main results

* `Stacks.EtaleCohomology.exact_compactSupportSheafCohomology_openClosed`: the excision sequence
  is exact in the middle.
* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_rationalLim_of_openClosed`: weights of
  the rational ℓ-adic limit of a tower from those of its open and closed parts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- A sheaf of `Λ`-modules placed in degree `0`, as a bounded below complex. -/
public abbrev sheafSingleComplex :
    EtaleModules.{u, 0} Λ X ⥤ CochainComplex.Plus (EtaleModules.{u, 0} Λ X) :=
  ObjectProperty.lift _ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)
    (fun _ => ⟨0, inferInstance⟩)

/-- **`Hⁱ_c(X_k̄, G)`** for a sheaf `G` of `Λ`-modules on `X_étale` placed in degree `0`, through
the canonical `RΓ_c(X_k̄, -)` on which the geometric Frobenius acts. -/
public abbrev compactSupportSheafCohomology (i : ℤ) :
    EtaleModules.{u, 0} Λ X ⥤ ModuleCat.{u + 1} Λ :=
  sheafSingleComplex Λ ⋙ compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The canonical geometric Frobenius `π_X^*` on `Hⁱ_c(X_k̄, -)`, natural in the sheaf. -/
public abbrev compactSupportSheafFrobenius (i : ℤ) :
    compactSupportSheafCohomology Λ f j kbar i ⟶ compactSupportSheafCohomology Λ f j kbar i :=
  Functor.whiskerLeft (sheafSingleComplex Λ)
    (Functor.whiskerRight (canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j kbar p q hcard)
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i))

variable {Z U : Scheme.{u}} (iZ : Z ⟶ X) [IsClosedImmersion iZ] (jU : U ⟶ X) [IsOpenImmersion jU]
  (hij : Set.range jU.base = (Set.range iZ.base)ᶜ)

/-- The open part `j_{U!} j_U⁻¹` of a sheaf on `X`. -/
public abbrev etaleModuleOpenPart : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ X :=
  etaleModuleRestriction.{u, 0} Λ jU ⋙ etaleModuleExtensionByZero.{u, 0} Λ jU

/-- The closed part `i_* i⁻¹` of a sheaf on `X`. -/
public abbrev etaleModuleClosedPart : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ X :=
  etaleModuleInverseImage.{u, 0} Λ iZ ⋙ etaleModuleDirectImage.{u, 0} Λ iZ

omit [Fintype k] in
include hij in
/-- **Excision for `Hⁱ_c(X_k̄, -)`**: for a sheaf `G` on `X_étale`,
`Hⁱ_c(X_k̄, j_{U!} j_U⁻¹ G) → Hⁱ_c(X_k̄, G) → Hⁱ_c(X_k̄, i_* i⁻¹ G)` is exact, the maps being
induced by the counit of `j_{U!} ⊣ j_U⁻¹` and the unit of `i⁻¹ ⊣ i_*`. -/
public theorem exact_compactSupportSheafCohomology_openClosed [Finite k]
    (G : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    Function.Exact
      ((compactSupportSheafCohomology Λ f j kbar i).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jU).counit.app G)).hom
      ((compactSupportSheafCohomology Λ f j kbar i).map
        ((etaleModuleInverseImageAdj.{u, 0} Λ iZ).unit.app G)).hom := by
  obtain ⟨h, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ iZ jU hij G
  have hS' := hS.map_of_exact (HomologicalComplex.single (EtaleModules.{u, 0} Λ X)
    (ComplexShape.up ℤ) 0)
  exact exact_homology_compactSupportFrobeniusFunctor_map Λ f j kbar hS'
    ((sheafSingleComplex Λ).obj _).2 ((sheafSingleComplex Λ).obj _).2
    ((sheafSingleComplex Λ).obj _).2 i

section Tower

variable {ℓ : ℕ} [Fact ℓ.Prime] (T : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X)

include hij in
/-- **Weights of the rational ℓ-adic limit from its open and closed parts.**  Let `T` be a tower of
sheaves of `ℤ_ℓ`-modules on `X_étale` whose open parts have finite `Hⁱ_c(X_k̄, -)`.  If the
Frobenius characteristic roots on the rational limits of `n ↦ Hⁱ_c(X_k̄, j_{U!} j_U⁻¹ Tₙ)` and
`n ↦ Hⁱ_c(X_k̄, i_* i⁻¹ Tₙ)` have absolute values `q' ^ (w / 2)` with `w ≤ b`, so do those on the
rational limit of `n ↦ Hⁱ_c(X_k̄, Tₙ)`. -/
public theorem isCharpolyNormMixedOfWeightLE_rationalLim_of_openClosed (i : ℤ)
    [HasLimitsOfShape ℕᵒᵖ (ModuleCat.{u + 1} ℤ_[ℓ])]
    (hfin : ∀ n, Finite ((compactSupportSheafCohomology ℤ_[ℓ] f j kbar i).obj
      ((etaleModuleOpenPart ℤ_[ℓ] jU).obj (T.obj n))))
    [hA : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj
      ((T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU) ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i))]
    [hB : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj
      (T ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i))]
    [hC : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj
      ((T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ) ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i))]
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}
    (hU : IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map
      (Functor.whiskerLeft (T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU)
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i))).hom)
    (hZ : IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map
      (Functor.whiskerLeft (T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ)
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i))).hom) :
    IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim (ℓ := ℓ)).map
      (Functor.whiskerLeft T (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i))).hom := by
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj
      (T ⋙ 𝟭 _ ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) := hB
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj
      (T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) := hA
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj
      (T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) := hC
  refine isCharpolyNormMixedOfWeightLE_rationalLimMap_of_exact
    (Functor.whiskerLeft T
      (Functor.whiskerRight (etaleModuleExtensionByZeroAdj.{u, 0} ℤ_[ℓ] jU).counit
        (compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)))
    (Functor.whiskerLeft T (Functor.whiskerRight (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] iZ).unit
      (compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)))
    (fun n => exact_compactSupportSheafCohomology_openClosed ℤ_[ℓ] f j kbar iZ jU hij (T.obj n) i)
    hfin _ _ _ ?_ ?_ hU hZ
  all_goals
    exact NatTrans.ext (funext fun n =>
      ((compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i).naturality _).symm)

end Tower

end Stacks.EtaleCohomology

end
