module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of the cohomology of constant torsion sheaves of modules on curves

Let `Λ` be a Noetherian ring, `M` a finite `Λ`-module annihilated by an integer `n > 0`, `k` an
algebraically closed field and `X` a separated scheme of finite type over `k` of dimension at
most one. [Stacks, Tag 0GJC] says that `H^q(X, M̲)` is a finite `Λ`-module for every `q`

1. if `n` is prime to the characteristic of `k`, and
2. if `X` is proper over `k`.

`Stacks.EtaleCohomology.TorsionModules.module_finite_etaleCohomology_constantSheaf` proves this
from the statement of [Stacks, Tag 03SC], `Stacks.EtaleCohomology.CurveTorsionCohomologyStatement`,
taken as a hypothesis. This file proves that statement, from Situation 0A52's eight statements for
torsion sheaves (`Stacks.EtaleCohomology.curveStatements_of_torsionSheafProperty_max` with its base
case `Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_zmod`, Lemma 0A5B for `ℤ/ℓ`),
and so obtains Tag 0GJC with no hypothesis beyond the source's.

## Main results

* `Stacks.EtaleCohomology.curveTorsionCohomologyStatement_holds`: the statement of Tag 03SC in
  the form `CurveTorsionCohomologyStatement`, which the theorems of the library that consume
  Tag 03SC take as their input `h03SC`.
* `Stacks.EtaleCohomology.TorsionModules.module_finite_etaleCohomology_constantSheaf_of_coprime`:
  Tag 0GJC part (1).
* `Stacks.EtaleCohomology.TorsionModules.module_finite_etaleCohomology_constantSheaf_of_isProper`:
  Tag 0GJC part (2).

## Implementation notes

The global instance `Stacks.EtaleCohomology.hasSheafifyEtale` (sheafification of sheaves of
`Λ`-modules at the coefficient universe `u + 1`) is switched off in this file: when instance
search tries it for the coefficients `ModuleCat.{max (u + 1) r} Λ` of the statements here, it
leaves the unsolvable universe constraint `max r (u + 1) = u + 1` behind. Files that restate
these results with the same imports need the same line.

## References

* [Stacks Project, Tag 0GJC](https://stacks.math.columbia.edu/tag/0GJC)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp

attribute [-instance] Stacks.EtaleCohomology.hasSheafifyEtale

/-- **The statement of [Stacks, Tag 03SC] holds**, in the form
`Stacks.EtaleCohomology.CurveTorsionCohomologyStatement`: for `k` algebraically closed, `X`
separated of finite type over `k` of dimension at most one and `F` a torsion abelian sheaf on
`X_étale`, the eight statements of Situation 0A52 hold for `F`. It is the bundle
`Stacks.EtaleCohomology.CurveStatements` of `curveStatements_of_torsionSheafProperty_max`, whose
base case, Lemma 0A5B for `ℤ/ℓ` on smooth curves, is `curveStatementsConstantOnSmoothCurves_zmod`,
read clause by clause; constructibility is taken on the canonical big étale site
`BigEtaleSite.containing X`. -/
@[sga "4½ Arcata 3.3.6", sga "5 VI 2.2.1" "special case"]
theorem curveTorsionCohomologyStatement_holds : CurveTorsionCohomologyStatement.{u, r} := by
  intro k _ _ X π _ _ _ hdim F hF
  have h : CurveStatements.{u, r, max (u + 1) r} π F :=
    curveStatements_of_torsionSheafProperty_max.{max (u + 1) r, r, u} π hdim
      (curveStatementsConstantOnSmoothCurves_zmod k) F hF
  have := SmallEtale.isRightAdjoint_smallEtalePushforward_addCommGrpCat.{u, r}
    (BigEtaleSite.containing X)
  have := SmallEtale.hasWeakSheafify_over_addCommGrpCat.{u, r} (BigEtaleSite.containing X)
  have : CharP k (ringChar k) := ringChar.charP k
  exact ⟨h.vanishing, h.affineVanishing, h.primePowerVanishing (ringChar k),
    h.finite_of_isPrimeToCharacteristicTorsion _ (BigEtaleSite.contains_containing X),
    fun hc hπ q => h.finite_of_isProper _ (BigEtaleSite.contains_containing X) hπ hc q,
    fun k' _ _ _ htors q => h.bijective_of_isPrimeToCharacteristicTorsion htors k' q,
    fun hπ k' _ _ _ q => h.bijective_of_isProper hπ k' q, fun U => h.surjective U⟩

namespace TorsionModules

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks Project, Tag 0GJC, part (1).** Let `Λ` be a Noetherian ring, `M` a finite
`Λ`-module annihilated by an integer `n > 0`, `k` an algebraically closed field and `X` a
separated scheme of finite type over `k` of dimension at most one. If `n` is prime to the
characteristic of `k`, then `H^q(X, M̲)` is a finite `Λ`-module for every `q`.

Here `X` is a scheme with a separated, locally of finite type and quasi-compact structure morphism
`π : X ⟶ Spec k`, the dimension is the Krull dimension of the underlying space, `M̲` is the
constant sheaf of `Λ`-modules on `X_étale` and `H^q(X, M̲)` is the `q`-th right derived functor
of global sections of sheaves of `Λ`-modules on `X_étale`. "Prime to the characteristic" is read
with the exponential characteristic, so that it is no condition in characteristic zero.

The proof is the source's (`module_finite_etaleCohomology_constantSheaf`), with the input
Tag 03SC supplied by `curveTorsionCohomologyStatement_holds`. -/
@[stacks 0GJC "part (1): n prime to char(k)"]
theorem module_finite_etaleCohomology_constantSheaf_of_coprime
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] (hX : topologicalKrullDim X ≤ 1)
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M] (n : ℕ) (hn : 0 < n)
    (hM : ∀ m : M, n • m = 0) (hnk : n.Coprime (ringExpChar k)) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) :=
  module_finite_etaleCohomology_constantSheaf.{u, r} Λ curveTorsionCohomologyStatement_holds.{u, r}
    π hX M n hn hM (Or.inl hnk) q

/-- **Stacks Project, Tag 0GJC, part (2).** Let `Λ` be a Noetherian ring, `M` a finite
`Λ`-module annihilated by an integer `n > 0`, `k` an algebraically closed field and `X` a
separated scheme of finite type over `k` of dimension at most one. If `X` is proper over `k`,
then `H^q(X, M̲)` is a finite `Λ`-module for every `q`.

Here `X` is a scheme with a separated, locally of finite type and quasi-compact structure morphism
`π : X ⟶ Spec k`, the dimension is the Krull dimension of the underlying space, `M̲` is the
constant sheaf of `Λ`-modules on `X_étale` and `H^q(X, M̲)` is the `q`-th right derived functor
of global sections of sheaves of `Λ`-modules on `X_étale`.

The proof is the source's (`module_finite_etaleCohomology_constantSheaf`), with the input
Tag 03SC supplied by `curveTorsionCohomologyStatement_holds`. -/
@[stacks 0GJC "part (2): X proper over k"]
theorem module_finite_etaleCohomology_constantSheaf_of_isProper
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [IsProper π]
    (hX : topologicalKrullDim X ≤ 1) (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M]
    (n : ℕ) (hn : 0 < n) (hM : ∀ m : M, n • m = 0) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) :=
  module_finite_etaleCohomology_constantSheaf.{u, r} Λ curveTorsionCohomologyStatement_holds.{u, r}
    π hX M n hn hM (Or.inr inferInstance) q

end TorsionModules

end Stacks.EtaleCohomology

end
