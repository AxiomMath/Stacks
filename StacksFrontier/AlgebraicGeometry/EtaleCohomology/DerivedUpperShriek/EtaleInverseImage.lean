module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.IndependenceCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.AdjointExistenceUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FiniteDirectImageCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImageUnconditional
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareLocalization
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# For a separated étale morphism `Rj^!` is the inverse image `j^{-1}`

Let `j : U ⟶ X` be a separated étale morphism of quasi-compact and quasi-separated schemes and
let `Λ` be a torsion ring. The derived upper shriek `Rj^! : D(X_étale, Λ) ⥤ D(U_étale, Λ)` of
[Stacks, Tag 0G2C] is the right adjoint of the derived lower shriek `Rj_! = Rj̄_* ∘ j'_!` of a
compactification `j = j̄ ∘ j'` (`Stacks.EtaleCohomology.derivedUpperShriekUnbounded`). This file
proves [Stacks, Tag 0GL9]: for *every* compactification, `Rj^!` is the inverse image `j^{-1}`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroInverseImageAdjOfEtale`: for an étale `j`, the
  adjunction `j_! ⊣ j^{-1}` with `j^{-1}` the inverse image of sheaves of `Λ`-modules.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedIsoOfIsFinite`: for a compactification
  `j = j̄ ∘ j'` of an étale `j` with `j̄` finite, `Rj_! = Rj̄_* ∘ j'_!` is `j_!`
  ([Stacks, Tag 0GKM] in this case).
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedIsoExtensionByZero`: the same for every
  compactification, through [Stacks, Tag 0F7I].
* `Stacks.EtaleCohomology.derivedUpperShriekUnboundedIsoInverseImage`: **[Stacks, Tag 0GL9]**.

## Implementation notes

The proof is the source's: `Rj^!` and `j^{-1}` are both right adjoint to `Rj_! = j_!`.

That `Rj_! = j_!` is shown first for the compactification of Zariski's main theorem
(`Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization`), with `j̄` finite:
then `Rj̄_* = j̄_*` as `j̄_*` is exact, and `j̄_* ∘ j'_! = j_!` on sheaves
(`Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIsoDirectImageUniv`). For an arbitrary
compactification it follows by the canonical isomorphism of [Stacks, Tag 0F7I]
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompactificationIsoUniv`).

The inverse image `j^{-1}` is `Stacks.EtaleCohomology.etaleModuleInverseImage`, the left adjoint
of the direct image; it is exact, and `j^{-1} : D(X_étale, Λ) ⥤ D(U_étale, Λ)` is the functor
it induces on derived categories, which needs no deriving.

The coefficient ring is an arbitrary torsion ring `Λ : Type r`, in any universe, as for the
functor `Rj^!` of [Stacks, Tag 0G2C].

## References

* [Stacks Project, Tag 0GL9](https://stacks.math.columbia.edu/tag/0GL9)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0GKM](https://stacks.math.columbia.edu/tag/0GKM)
* [Stacks Project, Tag 0F5A](https://stacks.math.columbia.edu/tag/0F5A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

/- `etaleModules_enoughInjectives_univZero` is stated for the coefficient ring in `Type`; instance
search would try to unify an arbitrary coefficient universe with it and fail on the universe
constraint, so it is switched off here. -/
attribute [-instance] etaleModules_enoughInjectives_univZero

attribute [local instance 2000] etaleModules_enoughInjectives

attribute [local instance] HasDerivedCategory.standard

/-! ### `j_! ⊣ j^{-1}` for the inverse image -/

section Adjunction

variable (Λ : Type r) [Ring Λ] {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- For an étale `j : U ⟶ X`, extension by zero `j_!` is left adjoint to the inverse image
`j^{-1}` of sheaves of `Λ`-modules, which for an étale morphism is restriction. -/
def etaleModuleExtensionByZeroInverseImageAdjOfEtale :
    etaleModuleExtensionByZero.{u, r} Λ j ⊣ etaleModuleInverseImage.{u, r} Λ j :=
  (etaleModuleExtensionByZeroAdj.{u, r} Λ j).ofNatIsoRight
    (etaleModuleInverseImageRestrictionIso.{u, r} Λ j).symm

/-- Extension by zero along equal étale morphisms: `a_! ≅ b_!` when `a = b`. -/
def etaleModuleExtensionByZeroCongr {a b : U ⟶ X} [Etale a] [Etale b] (h : a = b) :
    etaleModuleExtensionByZero.{u, r} Λ a ≅ etaleModuleExtensionByZero.{u, r} Λ b := by
  subst h
  exact Iso.refl _

end Adjunction

/-! ### `Rj_! = j_!` for an étale `j` -/

section LowerShriek

variable (Λ : Type r) [Ring Λ] {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- **`Rj_! = j_!` through a finite compactification.** For a compactification `j = j̄ ∘ j'` of an
étale morphism `j` with `j̄` finite, the derived lower shriek `Rj_! = Rj̄_* ∘ j'_!` is the functor
induced on unbounded derived categories by extension by zero `j_!`: `j̄_*` is exact, so
`Rj̄_* = j̄_*`, and `j̄_* ∘ j'_! = j_!`. -/
def derivedLowerShriekUnboundedIsoOfIsFinite (c : CompactificationOf (Over.mk j))
    [IsFinite c.toBase] :
    derivedLowerShriekUnbounded.{u, r} j c Λ ≅
      (etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategory :=
  have hc : c.immersion ≫ c.toBase = j := Over.w c.obj.hom
  haveI : Etale (c.immersion ≫ c.toBase) := by rw [hc]; infer_instance
  Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ c.immersion)
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ c.toBase) ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.Injectives.KInjectiveResolution.isoMapDerivedCategoryOfIsRightDerivedFunctor
        (etaleModuleDirectImage.{u, r} Λ c.toBase) _
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ c.toBase)) ≪≫
    RingTheory.TorIndependence.mapDerivedCategoryCompNatIso _ _ _
      ((etaleModuleExtensionByZeroCompIsoDirectImageUniv Λ c.immersion c.toBase).symm ≪≫
        etaleModuleExtensionByZeroCongr Λ hc)

variable [IsSeparated j] [CompactSpace U] [CompactSpace X] [QuasiSeparatedSpace X]

/-- A separated étale morphism `j : U ⟶ X` with `U` quasi-compact and `X` quasi-compact and
quasi-separated has a compactification `j = j̄ ∘ j'` with `j̄` finite (Zariski's main theorem). -/
theorem exists_compactificationOf_isFinite_toBase :
    ∃ c : CompactificationOf (Over.mk j), IsFinite c.toBase := by
  have : QuasiCompact j := (quasiCompact_iff_compactSpace j).2 ‹_›
  obtain ⟨T, j', π, hj', -, hπ, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization j
  exact ⟨⟨StructuredArrow.mk (Y := Over.mk π) (Over.homMk (U := Over.mk j) j' hfac.symm),
    ⟨hj', inferInstanceAs (IsProper π)⟩⟩, hπ⟩

/-- **`Rj_! = j_!` for every compactification.** For a separated étale morphism `j : U ⟶ X` with
`U` quasi-compact and `X` quasi-compact and quasi-separated, a torsion ring `Λ` and an arbitrary
compactification `j = j̄ ∘ j'`, the derived lower shriek `Rj_! = Rj̄_* ∘ j'_!` is the functor
induced on unbounded derived categories by extension by zero `j_!`. It is so for the
compactification of Zariski's main theorem, and the functors `Rj_!` of two compactifications are
canonically isomorphic, [Stacks, Tag 0F7I]. -/
def derivedLowerShriekUnboundedIsoExtensionByZero (c : CompactificationOf (Over.mk j))
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    derivedLowerShriekUnbounded.{u, r} j c Λ ≅
      (etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategory :=
  have : QuasiCompact j := (quasiCompact_iff_compactSpace j).2 ‹_›
  let c₀ := (exists_compactificationOf_isFinite_toBase j).choose
  haveI : IsFinite c₀.toBase := (exists_compactificationOf_isFinite_toBase j).choose_spec
  derivedLowerShriekUnboundedCompactificationIsoUniv j c c₀ Λ hΛ ≪≫
    derivedLowerShriekUnboundedIsoOfIsFinite Λ j c₀

/-- The adjunction `Rj_! ⊣ j^{-1}` for a separated étale `j` and every compactification: `Rj_!` is
`j_!` (`Stacks.EtaleCohomology.derivedLowerShriekUnboundedIsoExtensionByZero`), whose derived
form is left adjoint to `j^{-1}`. -/
def derivedLowerShriekUnboundedInverseImageAdj (c : CompactificationOf (Over.mk j))
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    derivedLowerShriekUnbounded.{u, r} j c Λ ⊣
      (etaleModuleInverseImage.{u, r} Λ j).mapDerivedCategory :=
  (etaleModuleExtensionByZeroInverseImageAdjOfEtale.{u, r} Λ j).mapDerivedCategory.ofNatIsoLeft
    (derivedLowerShriekUnboundedIsoExtensionByZero Λ j c hΛ).symm

/-- **[Stacks, Tag 0GL9].** Let `j : U ⟶ X` be a separated étale morphism of quasi-compact and
quasi-separated schemes and let `Λ` be a torsion ring. For every compactification
`j = j̄ ∘ j'` of `U` over `X`, the functor `Rj^! : D(X_étale, Λ) ⥤ D(U_étale, Λ)` of
[Stacks, Tag 0G2C], the right adjoint of `Rj_! = Rj̄_* ∘ j'_!`, is the inverse image
`j^{-1} : D(X_étale, Λ) ⥤ D(U_étale, Λ)`.

This is the source's proof: both functors are right adjoint to `Rj_! = j_!`. Quasi-separatedness
of `U` is not needed and not assumed. The coefficient ring `Λ : Type r` is in an arbitrary
universe. -/
@[stacks 0GL9 "for every compactification of j and every torsion ring Λ, in any universe; \
j^{-1} is the inverse image of sheaves of Λ-modules"]
def derivedUpperShriekUnboundedIsoInverseImage (c : CompactificationOf (Over.mk j))
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    derivedUpperShriekUnbounded.{u, r} Λ c hΛ ≅
      (etaleModuleInverseImage.{u, r} Λ j).mapDerivedCategory :=
  (derivedLowerShriekUnboundedAdjunction.{u, r} Λ c hΛ).rightAdjointUniq
    (derivedLowerShriekUnboundedInverseImageAdj Λ j c hΛ)

end LowerShriek

end Stacks.EtaleCohomology

end
