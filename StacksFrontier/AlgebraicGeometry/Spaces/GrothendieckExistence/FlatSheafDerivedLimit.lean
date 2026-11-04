module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.DerivedLimitBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedCoherator.AffineChartCase
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0CX5: the derived limit of the flat system of Situation 0CX4

In Situation [Stacks, Tag 0CX4] consider
`K = R lim_{D_QCoh(𝒪_X)}(Fₙ) = DQ_X(R lim_{D(𝒪_X)} Fₙ)`. Then `K` is in `D^b_QCoh(𝒪_X)` and in
fact `K` has nonzero cohomology sheaves only in degrees `≥ 0` ([Stacks, Tag 0CX5]).

The proof is
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit_bounded_of_affineCase` (the
source's argument through Example [Stacks, Tag 0CST]: `DQ_X` preserves derived limits, the affine
cohomology of `R lim Fₙ` is concentrated in degree `0` by [Stacks, Tag 0D3E], and `DQ_X` is left
t-exact and of bounded cohomological dimension, [Stacks, Tag 0CSS]) applied to the affine case of
the coherator, `AlgebraicGeometry.Space.affineCoheratorCase`, which carries no hypothesis.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit_bounded`: **Stacks 0CX5**.

## References

* [Stacks Project, Tag 0CX5](https://stacks.math.columbia.edu/tag/0CX5)
* [Stacks Project, Tag 0CST](https://stacks.math.columbia.edu/tag/0CST)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] isGrothendieckAbelian_modules enoughInjectives_modules

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- **[Stacks, Tag 0CX5].** In Situation [Stacks, Tag 0CX4] consider
`K = R lim_{D_QCoh(𝒪_X)}(Fₙ) = DQ_X(R lim_{D(𝒪_X)} Fₙ)`. Then `K` is in `D^b_QCoh(𝒪_X)` and in fact
`K` has nonzero cohomology sheaves only in degrees `≥ 0`.

Formally: the coherator `DQ_X`, the right adjoint of `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`, exists; the system
`(Fₙ)` (that is, `(iₙ,* Fₙ)` placed in degree `0`) has a derived limit `L = R lim_{D(𝒪_X)} Fₙ`; and
for every coherator `DQ_X` and every such `L`, `K = DQ_X(L)` is a derived limit of `(Fₙ)` in
`D_QCoh(𝒪_X)`, its cohomology sheaves vanish in negative degrees, and they vanish above some
degree; and every derived limit `K` of `(Fₙ)` in `D_QCoh(𝒪_X)` has the same two properties. -/
@[stacks 0CX5 "the full statement: DQ_X exists and R lim F_n exists in D(O_X); for every \
coherator DQ_X and every such derived limit L, K = DQ_X(L) is a derived limit of (F_n) in \
D_QCoh(O_X), and every derived limit K of (F_n) in D_QCoh(O_X) lies in D^b with cohomology \
sheaves only in degrees at least 0; nothing is granted or assumed"]
theorem derivedLimit_bounded :
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.IsLeftAdjoint ∧
    (∃ L, IsDerivedLimit D.derivedSystem L) ∧
    (∀ (DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
        (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory)
      (_ : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
      (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left),
      IsDerivedLimit D.derivedSystem L →
        (∃ _ : HasProduct fun n : ℕ => D.quasicoherentSystem.obj ⟨n⟩,
          IsDerivedLimit D.quasicoherentSystem (DQ.obj L)) ∧
        SpaceCohomologyVanishesBelow D.X.left 0
          ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L)) ∧
        ∃ c : ℤ, SpaceCohomologyVanishesAbove D.B D.S D.containsLimitBase D.X.left c
          ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L))) ∧
    ∀ (_ : HasProduct fun n : ℕ => D.quasicoherentSystem.obj ⟨n⟩)
      (K : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory),
      IsDerivedLimit D.quasicoherentSystem K →
        SpaceCohomologyVanishesBelow D.X.left 0
          ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj K) ∧
        ∃ c : ℤ, SpaceCohomologyVanishesAbove D.B D.S D.containsLimitBase D.X.left c
          ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj K) :=
  D.derivedLimit_bounded_of_affineCase (affineCoheratorCase D.B D.S D.containsLimitBase)

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
