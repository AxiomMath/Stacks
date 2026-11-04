module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafExcisionIso

/-!
# The Leray comparison `RΓ_c(U_k̄, K) ≅ RΓ_c(W_k̄, Rg_! K)`, compatibly with Frobenius

Let `g : U ⟶ W` be separated of finite type, with a compactification `j_g`, and let
`f_W : W ⟶ Spec k` be separated of finite type over a finite field, with a compactification `j_W`.
For a sheaf `K` of `ℤ_ℓ`-modules on `U` killed by a power of `ℓ`, the composition
`R(f_W ∘ g)_! ≅ R f_{W!} ∘ R g_!` ([Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)), base
change of `Rg_!` along `W_k̄ ⟶ W` ([Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)) and
the compatibility of both with the geometric Frobenius give, for a suitable compactification `j_U`
of `U`, an isomorphism `RΓ_c(U_k̄, K) ≅ RΓ_c(W_k̄, Rg_! K)` commuting with `π^*`. Here `Rg_! K` is
represented by a bounded below complex `C K` of sheaves on `W`, functorial in `K`, so that both
sides are values of `Stacks.EtaleCohomology.compactSupportFrobeniusFunctor`, on which the
canonical Frobenius `Stacks.EtaleCohomology.canonicalCompactSupportFrobeniusNatTrans` acts.

`Stacks.EtaleCohomology.LAdicSheaf.LerayFrobeniusComparison` records this comparison as a
proposition. It is the input of the Leray step of the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) to curves, consumed through the truncation
triangles of `C K`.

## Main definitions

* `Stacks.EtaleCohomology.IsLPowerTorsion`: the sheaves killed by a power of `ℓ`.
* `Stacks.EtaleCohomology.LAdicSheaf.LerayFrobeniusComparison`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` and `compactSupportFrobeniusFunctor` live in the
standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The sheaves of `ℤ_ℓ`-modules on `X_étale` killed by a power of `ℓ`. -/
def IsLPowerTorsion (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    ObjectProperty (EtaleModules.{u, 0} ℤ_[ℓ] X) :=
  fun K => ∃ N : ℕ, ℓ ^ N • 𝟙 K = 0

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {U W : B.Scheme} (g : U ⟶ W)
  (jg : CompactificationOf (Over.mk (B.inclusion.map g))) {k : Type u} [Field k] [Fintype k]
  (fW : W.1 ⟶ Spec (.of k)) (jW : CompactificationOf (Over.mk fW))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- `K ↦ Rg_! K` on ℓ-power torsion sheaves placed in degree `0`. -/
abbrev LAdicSheaf.torsionLowerShriek :
    (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      DerivedCategory.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1) :=
  (IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus _ ⋙ DerivedCategory.Plus.Q ⋙
    derivedLowerShriek.{u, 0} (B.inclusion.map g) jg ℤ_[ℓ]

/-- `K ↦ RΓ_c(U_k̄, K)` on ℓ-power torsion sheaves placed in degree `0`. -/
abbrev LAdicSheaf.torsionCompactSupport
    (jU : CompactificationOf (Over.mk (B.inclusion.map g ≫ fW))) :
    (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤ DerivedCategory.Plus (ModuleCat.{u + 1} ℤ_[ℓ]) :=
  (IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus _ ⋙
    compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar

/-- **The Leray comparison with Frobenius** (Tags 0F7J, 0F7L): for some compactification `j_U` of
`U` over `k`, a functor `C` from ℓ-power torsion sheaves on `U` to bounded below complexes on `W`
computing `Rg_!` (`C K ≅ Rg_! K` in `D⁺(W_ét)`, naturally), and a natural isomorphism
`RΓ_c(U_k̄, K) ≅ RΓ_c(W_k̄, C K)` commuting with the canonical geometric Frobenius. -/
def LAdicSheaf.LerayFrobeniusComparison : Prop :=
  ∃ (jU : CompactificationOf (Over.mk (B.inclusion.map g ≫ fW)))
    (C : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1))
    (_ : C ⋙ DerivedCategory.Plus.Q ≅ LAdicSheaf.torsionLowerShriek B ℓ g jg)
    (φ : LAdicSheaf.torsionCompactSupport B ℓ g fW kbar jU ≅
      C ⋙ compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jW kbar),
    Functor.whiskerLeft ((IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus _)
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] (B.inclusion.map g ≫ fW) jU kbar
          p q hcard) ≫ φ.hom =
      φ.hom ≫ Functor.whiskerLeft C
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] fW jW kbar p q hcard)

end Stacks.EtaleCohomology
