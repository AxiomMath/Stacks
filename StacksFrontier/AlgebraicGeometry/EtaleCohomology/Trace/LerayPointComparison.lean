module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekLeray
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDimensionZeroHomology

/-!
# The Leray comparison over a base of dimension zero

Let `g : U ⟶ W` be a morphism of the big étale site with a compactification `j_g`, and
`f_W : W ⟶ Spec k` separated of finite type over a finite field, with `W` of dimension zero (for
instance `W = Spec κ` for a finite extension `κ` of `k`). Given the Leray comparison with
Frobenius `RΓ_c(U_k̄, K) ≅ RΓ_c(W_k̄, C K)` for a complex functor `C` computing `Rg_!`
(`Stacks.EtaleCohomology.LAdicSheaf.LerayFrobeniusComparison`), the cohomology in degree `r` is

`Hʳ_c(U_k̄, K) ≅ H⁰_c(W_k̄, Rʳ g_! K)`,

naturally in the ℓ-power torsion sheaf `K` and compatibly with the geometric Frobenius
(`Stacks.EtaleCohomology.LAdicSheaf.exists_lowerShriekHomology_compactSupportSheafCohomology_iso`):
`C K` has its cohomology `Hⁿ(C K) = Rⁿ g_! K` in degrees `≥ 0`, killed by a power of `ℓ`, so in
dimension zero `Hʳ_c(W_k̄, C K) = H⁰_c(W_k̄, Hʳ(C K))`
(`Stacks.EtaleCohomology.compactSupportDimensionZeroHomologyIso`).

For `W = Spec κ(w)`, `w` a closed point of the base of a morphism, this identifies the stalk of
`Rʳ g_! G` at `w`, with its Frobenius, with `Hʳ_c` of the fibre, in the reduction of the weight
bound of Weil II to curves ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.lerayComplexLift`: `C` lands in the complexes with torsion
  cohomology in degrees `≥ 0`.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_lowerShriekHomology_compactSupportSheafCohomology_iso`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` and `compactSupportFrobeniusFunctor` live in the
standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {U W : B.Scheme} (g : U ⟶ W)
  (jg : CompactificationOf (Over.mk (B.inclusion.map g)))

/-- **A complex functor computing `Rg_!` lands in the complexes with torsion cohomology in degrees
`≥ 0`**: `Hⁿ(C K) = Rⁿ g_! K` vanishes for `n < 0` and is killed by the power of `ℓ` killing
`K`. -/
def LAdicSheaf.lerayComplexLift
    (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))
    (ψ : C ⋙ DerivedCategory.Plus.Q ≅ LAdicSheaf.torsionLowerShriek B ℓ g jg) :
    (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      (torsionHomologyNonneg ℤ_[ℓ] W.1).FullSubcategory :=
  ObjectProperty.lift _ C fun K => by
    refine ⟨isGE_lerayComplex B ℓ g jg C ψ K, fun n => ?_⟩
    obtain ⟨N, hN⟩ := K.2
    refine ⟨ℓ ^ N, pow_pos (Fact.out : ℓ.Prime).pos N, ?_⟩
    refine nsmul_id_eq_zero_of_iso ((lerayComplexHomologyIso B ℓ g jg C ψ n).app K).symm ?_
    change ℓ ^ N • 𝟙 ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg n).obj K.1) = 0
    rw [← (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg n).map_id, ← Functor.map_nsmul, hN,
      Functor.map_zero]

variable {k : Type u} [Field k] [Fintype k] (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW]
  [QuasiCompact fW] [IsSeparated fW] (jW : CompactificationOf (Over.mk fW))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The Leray comparison over a base of dimension zero, in degree `r`**: from the Leray
comparison with Frobenius for `g` over `W` (Tags 0F7J, 0F7L), with `W` of dimension zero, there is
a compactification `j_U` of `U` over `k` such that for every `r`,
`H⁰_c(W_k̄, Rʳ g_! K) ≅ Hʳ_c(U_k̄, K)` naturally in the ℓ-power torsion sheaf `K`, commuting with
the geometric Frobenius. -/
theorem LAdicSheaf.exists_lowerShriekHomology_compactSupportSheafCohomology_iso
    (hdim : topologicalKrullDim W.1 ≤ 0)
    (hL : LAdicSheaf.LerayFrobeniusComparison B ℓ g jg fW jW kbar p q hcard) :
    ∃ jU : CompactificationOf (Over.mk (B.inclusion.map g ≫ fW)), ∀ r : ℕ,
      ∃ Ψ : (IsLPowerTorsion ℓ U.1).ι ⋙ lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r ⋙
          compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0 ≅
        (IsLPowerTorsion ℓ U.1).ι ⋙
          compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar r,
        Functor.whiskerLeft (IsLPowerTorsion ℓ U.1).ι (Functor.whiskerLeft
            (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r)
            (compactSupportSheafFrobenius ℤ_[ℓ] fW jW kbar p q hcard 0)) ≫ Ψ.hom =
          Ψ.hom ≫ Functor.whiskerLeft (IsLPowerTorsion ℓ U.1).ι
            (compactSupportSheafFrobenius ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar p q hcard r) := by
  obtain ⟨jU, C, ψ, φ, hφ⟩ := hL
  refine ⟨jU, fun r => ?_⟩
  let e₁ : (IsLPowerTorsion ℓ U.1).ι ⋙
      compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar r ≅
      C ⋙ compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jW kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) r :=
    Functor.isoWhiskerRight φ (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) r)
  let e₂ := Functor.isoWhiskerLeft (LAdicSheaf.lerayComplexLift B ℓ g jg C ψ)
    (compactSupportDimensionZeroHomologyIso ℤ_[ℓ] fW jW kbar hdim r)
  let e₃ : (C ⋙ CochainComplex.Plus.ι _ ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) r) ⋙
        compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0 ≅
      (IsLPowerTorsion ℓ U.1).ι ⋙ lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r ⋙
        compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0 :=
    Functor.isoWhiskerRight (lerayComplexHomologyIso B ℓ g jg C ψ r)
      (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0)
  refine ⟨(e₁ ≪≫ e₂ ≪≫ e₃).symm, ?_⟩
  refine comp_symm_hom_eq_of_comm _ _ _ (comp_trans_hom_eq_of_comm _ _ _
    (Functor.whiskerLeft C (Functor.whiskerRight
      (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] fW jW kbar p q hcard)
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) r))) _
    (NatTrans.ext (funext fun K => ?_)) (comp_trans_hom_eq_of_comm _ _ _
    (Functor.whiskerLeft (LAdicSheaf.lerayComplexLift B ℓ g jg C ψ)
      (Functor.whiskerLeft (torsionHomologyNonneg ℤ_[ℓ] W.1).ι
      (Functor.whiskerLeft (CochainComplex.Plus.ι (EtaleModules.{u, 0} ℤ_[ℓ] W.1) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) r)
        (compactSupportFrobeniusAlong ℤ_[ℓ] fW jW kbar p q hcard
          ((Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, 0} ℤ_[ℓ] W.1)).functor 0)
          0)))) _
    (NatTrans.ext (funext fun K => ?_)) (NatTrans.ext (funext fun K => ?_))))
  · have h := congrArg (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) (r : ℤ)).map
      (NatTrans.congr_app hφ K)
    simp only [Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app] at h
    exact h
  · exact NatTrans.congr_app
      (compactSupportDimensionZeroHomologyIso_hom_frobenius ℤ_[ℓ] fW jW kbar hdim p q hcard r)
      ((LAdicSheaf.lerayComplexLift B ℓ g jg C ψ).obj K)
  · exact ((compactSupportSheafFrobenius ℤ_[ℓ] fW jW kbar p q hcard 0).naturality
      ((lerayComplexHomologyIso B ℓ g jg C ψ r).hom.app K)).symm

end Stacks.EtaleCohomology
