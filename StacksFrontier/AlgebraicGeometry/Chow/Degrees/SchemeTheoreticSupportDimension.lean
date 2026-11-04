module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AnnihilatorSupport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The delta-dimension of the scheme-theoretic support of a coherent module

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project and
let `F` be a coherent `𝒪_X`-module. Two closed subschemes of `X` carry the support of `F`: the
reduced one `Stacks.Chow.reducedSupport F`, in which the cycle `[F]_k` of Stacks 02QX is read,
and the scheme-theoretic one `AlgebraicGeometry.annihilatorIdeal' F`, cut out by the annihilator,
along which Stacks 02OM descends `F`. They have the same underlying closed set, hence the same
delta-dimension, so a bound stated for one is a bound for the other.

## Main results

* `Stacks.Chow.range_subschemeι_annihilatorIdeal` — the scheme-theoretic support has the support
  of the module as its range.
* `Stacks.Chow.schemeDeltaDimension_annihilatorIdeal_eq` — the two closed subschemes carrying the
  support have the same delta-dimension.
* `Stacks.Chow.schemeDeltaDimension_annihilatorIdeal_le` — a delta-dimension bound on the reduced
  support is one on the scheme-theoretic support.

## References

* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- The closed immersion of the scheme-theoretic support of a coherent module has the support of
the module as its range: the annihilator ideal sheaf is carried by that support. -/
@[ega "III 4.1.10" "partial"]
theorem range_subschemeι_annihilatorIdeal (F : X.Modules) [F.IsCoherent] :
    Set.range (annihilatorIdeal' F).subschemeι.base = SheafOfModules.supp F := by
  have hqc := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have : F.IsQuasicoherent := hqc.1
  have : F.IsFiniteType := hqc.2
  rw [Scheme.IdealSheafData.range_subschemeι, ← supp_eq_annihilatorIdeal_support F]

/-- The reduced support and the scheme-theoretic support of a coherent module have the same
delta-dimension: they are closed subschemes of `X` with the same underlying closed set. -/
theorem schemeDeltaDimension_annihilatorIdeal_eq (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] :
    schemeDeltaDimension C ((annihilatorIdeal' F).subschemeι ≫ f) =
      schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) :=
  schemeDeltaDimension_eq_of_equal_ranges C f (annihilatorIdeal' F).subschemeι
    (reducedSupport F).subschemeι
    (by
      rw [range_subschemeι_annihilatorIdeal F, Scheme.IdealSheafData.range_subschemeι,
        coe_support_reducedSupport F])

/-- A delta-dimension bound on the reduced support of a coherent module is a bound on its
scheme-theoretic support. -/
theorem schemeDeltaDimension_annihilatorIdeal_le (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] {k : ℤ}
    (hF : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) :
    schemeDeltaDimension C ((annihilatorIdeal' F).subschemeι ≫ f) ≤ (k : EInt) := by
  rw [schemeDeltaDimension_annihilatorIdeal_eq C f F]
  exact hF

end Stacks.Chow

end
