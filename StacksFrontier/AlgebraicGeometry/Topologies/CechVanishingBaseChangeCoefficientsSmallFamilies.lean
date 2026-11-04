module

public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingBaseChangeCoefficients
public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechComplexAndAmitsur

/-!
# Čech vanishing for base-change coefficients along families indexed in the scheme universe

`AlgebraicGeometry.isZero_cechCohomology_succ_baseChange` proves positive-degree Čech vanishing
for the base-change presheaf `V ↦ Γ(V, 𝒪_V) ⊗_R M` of a module `M` in an arbitrary universe `m`,
along a standard covering whose index type lives in the universe `max u m` of the coefficients.
The families the geometry produces — the standard fppf families of a stack, for instance — are
indexed by a type in the universe `u` of the schemes.  This file removes that mismatch.

The only place the index universe enters is the one-member covering the finite family is
reduced to ([Stacks, Tag 03FI] part (3)): the Čech complex of a one-member family
`PreZeroHypercover.singleton.{w} h` is, through
`Stacks.CechSite.singletonCechCosimplicialIso`, the alternating coface complex of the sections
over the powers of the covering object, in which no index universe appears.  So the Čech
complexes of `singleton.{w} h` and `singleton.{w'} h` are isomorphic
(`Stacks.CechSite.cechComplexSingletonIsoOfIndexUniverse`), and the reduction can be run at the
index universe of the family.

## Main results

* `Stacks.CechSite.cechComplexSingletonIsoOfIndexUniverse`: the Čech complex of a one-member
  family does not depend on the index universe.
* `AlgebraicGeometry.isZero_cechCohomology_succ_of_amitsurRestriction_of_smallFamily`:
  positive-degree Čech vanishing on a standard `τ`-covering indexed in the universe of the
  schemes, for a finite-product-preserving abelian presheaf whose restriction to the slice is the
  Amitsur coefficient presheaf.
* `AlgebraicGeometry.isZero_cechCohomology_succ_baseChange_of_smallFamily`: the same for the
  base-change presheaf of a module.

No `@[stacks]` attribute is claimed, for the reason given in
`StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingBaseChangeCoefficients`.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CechSite Stacks.Descent

universe w w' v v' u u' m

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C] {T V : C} (h : V ⟶ T) [HasFiniteProducts (Over T)]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A] [HasProducts.{w'} A]
  (F : Cᵒᵖ ⥤ A)

/-- **The Čech complex of a one-member family does not depend on the index universe.**  Both
complexes are the alternating coface complex of the sections over the powers of the covering
object, by `Stacks.CechSite.singletonCechCosimplicialIso`. -/
def cechComplexSingletonIsoOfIndexUniverse :
    cechComplex (PreZeroHypercover.singleton.{w} h) F ≅
      cechComplex (PreZeroHypercover.singleton.{w'} h) F :=
  cechComplexIsoOfCosimplicialIso (PreZeroHypercover.singleton.{w} h) F
      (singletonCechCosimplicialIso.{w} h F) ≪≫
    (cechComplexIsoOfCosimplicialIso (PreZeroHypercover.singleton.{w'} h) F
      (singletonCechCosimplicialIso.{w'} h F)).symm

end Stacks.CechSite

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (U : Over S) [IsAffine U.left] (M : Type m) [AddCommGroup M]
  [Module (Γ(U.left, ⊤) : Type u) M]

/-- **Positive-degree Čech vanishing on a standard `τ`-covering of an affine object of `Over S`
indexed in the universe of the schemes**, for a finite-product-preserving abelian presheaf whose
restriction to the slice is the Amitsur coefficient presheaf of `M`.

This is `AlgebraicGeometry.isZero_cechCohomology_succ_of_amitsurRestriction` with the index
universe of the family freed from that of the coefficients: the finite family is reduced to the
one-member family `{∐ U_i → U}` at its own index universe
(`Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts`), and that one-member family
is moved to the index universe of the coefficients by
`Stacks.CechSite.cechComplexSingletonIsoOfIndexUniverse`. -/
theorem isZero_cechCohomology_succ_of_amitsurRestriction_of_smallFamily (τ : CoveringTopology)
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u m}) [PreservesFiniteProducts F]
    (e : (Over.forget U).op ⋙ F ≅ amitsurSliceModulePresheaf U M ⋙
      forget₂ (ModuleCat.{max u m} (Γ(U.left, ⊤) : Type u)) AddCommGrpCat.{max u m})
    (𝒱 : PreZeroHypercover.{u} U)
    (h : IsStandardCovering τ (fun i ↦ (𝒱.X i).left) (fun i ↦ (𝒱.f i).left))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology 𝒱 F p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  have hfin : Finite 𝒱.I₀ := h.finite_index
  have haff : IsAffine (∐ 𝒱.X).left := h.isAffine_left_sigmaObj τ S 𝒱
  let halg := overAffineSliceAlgebra U (Sigma.desc 𝒱.f)
  have hff := h.faithfullyFlat_left_sigmaDesc τ S 𝒱
  have hone : IsZero (cechCohomology
      (PreZeroHypercover.singleton.{max u m} (Sigma.desc 𝒱.f)) F (q + 1)) :=
    isZero_cechCohomology_singleton_of_iso.{max u m} (Sigma.desc 𝒱.f)
      ((overAffineAlgSpec U).obj
        (op (overAffineAlgObj U (Γ((∐ 𝒱.X).left, ⊤) : Type u)))).hom
      (mkIsoMkSpecOverAffineAlgObj U (Sigma.desc 𝒱.f)) F (q + 1)
      (isZero_cechCohomology_singleton_succ_of_amitsurRestriction U M F e
        (Γ((∐ 𝒱.X).left, ⊤) : Type u) q)
  have hone' : IsZero (cechCohomology
      (PreZeroHypercover.singleton.{u} (Sigma.desc 𝒱.f)) F (q + 1)) :=
    hone.of_iso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u m}
      (ComplexShape.up ℕ) (q + 1)).mapIso
        (cechComplexSingletonIsoOfIndexUniverse.{u, max u m} (Sigma.desc 𝒱.f) F))
  have := Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts.{u} 𝒱 F
  exact hone'.of_iso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u m}
    (ComplexShape.up ℕ) (q + 1)).mapIso (asIso (Stacks.CechSite.cechComplexMap 𝒱
      (PreZeroHypercover.singleton.{u} (Sigma.desc 𝒱.f))
      (Stacks.CechSite.coproductRefinement 𝒱) F))).symm

variable (Y : Scheme.{u}) [IsAffine Y] (N : Type m) [AddCommGroup N]
  [Module (Γ(Y, ⊤) : Type u) N]

/-- The `Γ(Y, ⊤)`-module structure on `N`, read as a module over
`Γ((terminalOver Y).left, ⊤)`. -/
local instance moduleTerminalOverLeftSmallFamily :
    Module (Γ((terminalOver Y).left, ⊤) : Type u) N :=
  inferInstanceAs (Module (Γ(Y, ⊤) : Type u) N)

/-- **Positive-degree Čech vanishing on a standard `τ`-covering of an affine scheme `Y` indexed
in the universe of the schemes, with the base-change presheaf of an `R`-module in an arbitrary
universe as coefficients.**  The form of `AlgebraicGeometry.isZero_cechCohomology_succ_baseChange`
the standard families of a stack are fed to. -/
theorem isZero_cechCohomology_succ_baseChange_of_smallFamily (τ : CoveringTopology)
    (𝒱 : PreZeroHypercover.{u} (terminalOver Y))
    (h : IsStandardCovering τ (fun i ↦ (𝒱.X i).left) (fun i ↦ (𝒱.f i).left))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology 𝒱 (baseChangeAbelianPresheaf Y N) p) :=
  isZero_cechCohomology_succ_of_amitsurRestriction_of_smallFamily (terminalOver Y) N τ
    (baseChangeAbelianPresheaf Y N) (baseChangeAbelianRestrictionIso Y N) 𝒱 h p hp

end AlgebraicGeometry

end
