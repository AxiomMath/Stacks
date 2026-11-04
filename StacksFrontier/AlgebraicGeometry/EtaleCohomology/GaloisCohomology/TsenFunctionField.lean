module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFields

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.Tsen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.TsenUnconditional
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksCore.Tactic.StacksAttribute

/-!
# Tsen's theorem for the function field of a variety

The function field of a variety of dimension `r` over an algebraically closed field `k` is a
\(C_r\) field (Stacks 03RD).

## Main results

* `AlgebraicGeometry.trdeg_residueField_genericPoint_eq`: the residue field at the generic point
  of an irreducible scheme of dimension `r`, locally of finite type over `k`, has transcendence
  degree `r` over `k`.
* `AlgebraicGeometry.isCField_functionField`: **Tsen's theorem** — the function field of a
  variety of dimension `r` over an algebraically closed field is a \(C_r\) field.

## Implementation notes

The proof is not the one of the source, which counts sections of multiples of an ample divisor
on a projective model by asymptotic Riemann–Roch (Stacks 0BJ8). It runs instead through the
field theory of `Tsen.lean` and `CFieldSystems.lean`: the function field is finitely generated
of transcendence degree `r` over `k` (the dimension formula of Stacks 0A21 at the generic
point), hence finite over a rational function field `k(x_1, ..., x_r)`. That rational function
field has the \(C_r\) property even for *systems* of forms, by the elementary dimension count
over `k[x_1, ..., x_r]` together with Stacks 03RB, and the property for systems passes to
finite extensions with no loss (`IsCFieldForSystems.of_module_finite`). This is Lang's route to
Tsen's theorem; it needs no projective model and no Riemann–Roch.

The dimension of the variety is `topologicalKrullDim X`, and the `Algebra k` structure on the
residue field at the generic point is the one fixed by
`AlgebraicGeometry.residueField_essFiniteType`. The function field is identified with that
residue field by `AlgebraicGeometry.genericResidueEquiv`, and the conclusion is transported
along it by `IsCField.of_ringEquiv`, so the statement itself needs no `Algebra k` structure on
the function field.

## References

* [Stacks Project, Tag 03RD](https://stacks.math.columbia.edu/tag/03RD)
* [Stacks Project, Tag 03RB](https://stacks.math.columbia.edu/tag/03RB)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* S. Lang, *On quasi algebraic closure*, Ann. of Math. 55 (1952), 373–390.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The residue field at the generic point of an irreducible scheme of dimension `r`, locally
of finite type over a field `k`, has transcendence degree `r` over `k`. This is the dimension
formula of Tag 0A21 read at the generic point. -/
@[ega "IV 4.1.1" "special case", ega "IV 5.2.1" "special case"]
theorem trdeg_residueField_genericPoint_eq (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IrreducibleSpace X] [LocallyOfFiniteType f] {r : ℕ}
    (hr : topologicalKrullDim X = r) :
    letI : Algebra k (X.residueField (genericPoint X)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.Γevaluation (genericPoint X)).hom.toAlgebra
    Algebra.trdeg k (X.residueField (genericPoint X)) = r := by
  let : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  have h := topologicalKrullDim_eq_trdeg_residueField k X f (genericPoint X)
    (genericPoint_spec X)
  rw [hr] at h
  have h1 : (r : ℕ∞) = Cardinal.toENat (Algebra.trdeg k (X.residueField (genericPoint X))) := by
    exact_mod_cast h
  exact Cardinal.toENat_eq_natCast.mp h1.symm

/-- **Stacks Project, Tag 03RD (Tsen's theorem).** The function field of a variety of dimension
`r` over an algebraically closed field `k` is a \(C_r\) field. -/
@[stacks 03RD]
theorem isCField_functionField (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] {r : ℕ} (hr : topologicalKrullDim X = r) :
    IsCField X.functionField r := by
  let : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  have : Algebra.EssFiniteType k (X.residueField (genericPoint X)) :=
    residueField_essFiniteType k f (genericPoint X)
  exact IsCField.of_ringEquiv (isCField_of_essFiniteType_trdeg_eq k _
    (trdeg_residueField_genericPoint_eq k f hr)) (genericResidueEquiv X).symm

end AlgebraicGeometry

end
