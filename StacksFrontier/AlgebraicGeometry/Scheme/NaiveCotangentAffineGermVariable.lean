module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineGermTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSectionsVariable

/-!
# The germ of the local section `1 ⊗ d [t]`

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space `X`, let `U`
be an open of `X` and let `x` be a point of `U`.  The degree `0` term `B ⊗[A[B]] Ω[A[B]/A]` of
`NL_{B/A}` has, over `U`, the distinguished local sections `1 ⊗ d [t]` attached to the variables
`[t]` of the canonical presentation `A[B] ⟶ B`, one for each section `t` of `B` over `U`
(`Stacks.Sites.Conormal.tensorDifferential` at `Stacks.SheafOfModules.variableSection`).  This
file computes the germ of such a section at `x` under the identification of Stacks 0D09 of that
stalk with the cotangent space of the canonical presentation of `Bₓ` over `Aₓ`: it is the basis
element `1 ⊗ d X_{tₓ}` indexed by the germ of `t`.

This is what makes the stalk of a map out of the degree `0` term computable.  The cotangent
space of `Generators.self Aₓ Bₓ` is free on the elements `1 ⊗ d X_s`
(`Algebra.Generators.cotangentSpaceBasis`), so a linear map out of it is determined by its
values on them, and this identity says which local sections of `B ⊗[A[B]] Ω[A[B]/A]` carry those
values.  In the proof of **Stacks 0E1Y** it is the half that meets
`Stacks.SheafOfModules.naiveCotangentTowerHomotopy_tensorDifferential_variableSection`, which
computes the value of the null homotopy of a tower on the very same local sections.

## Main results

* `Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_X`:
  the germ at `x` of the image of `1 ⊗ d X_t` under the comparison on sections is `1 ⊗ d X_{tₓ}`.
  Together with `Stacks.SheafOfModules.sectionsTensorComparison_one_tmul_D_X`, which identifies
  that image with the local section `1 ⊗ d [t]`, this is the germ of `1 ⊗ d [t]`.

## Implementation notes

The identity is stated through the comparison on sections rather than directly on the local
section `1 ⊗ d [t]`, and the reason is the elaborator's budget.
`Stacks.Sites.Conormal.tensorDifferential` is typed through `(conormalSequence …).X₂`, which is
`Stacks.Sites.Conormal.tensorDifferentialsSheaf` only after the sheafification in both is
unfolded.  Under `.obj U` that unification is affordable, and it is what
`Stacks.SheafOfModules.sectionsTensorComparison_one_tmul_D_X` performs; *under a stalk* — a
filtered colimit over the neighbourhoods of `x`, with the six algebra and scalar-tower instances
of the germ square in the local context — it exceeds `200000` heartbeats at `isDefEq`, and a
direct formulation was written and discarded for that reason.  Factoring the identity through
the comparison on sections keeps every statement on the cheap side of that unification, the
comparison's own codomain being spelled `tensorDifferentialsSheaf`.

Given that, the proof is the composite of three identities that already exist: the germ of the
comparison on sections is the cotangent-space map of the morphism of extensions given by the
germ maps
(`Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison`),
that map sends `b ⊗ d p` to `b ⊗ d` of the image of `p`
(`Algebra.Extension.CotangentSpace.map_tmul`), and the morphism of extensions carries the
variable `X_t` to the variable indexed by the germ of `t`
(`Stacks.SheafOfModules.germPolynomialHom_X`).

## References

* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), the comparison on
  sections.
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), where the identity is
  consumed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace Stacks.SheafOfModules

open TopCat.Presheaf Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {X : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : A ⟶ B) (x : X) (U : Opens X) (hx : x ∈ U)

/-- **The germ of the local section `1 ⊗ d [t]`.**  Under the identification of the stalk at `x`
of the degree `0` term of `NL_{B/A}` with the cotangent space of the canonical presentation of
`Bₓ` over `Aₓ` (Stacks 0D09), the germ at `x` of the image under the comparison on sections of
`1 ⊗ d X_t` is the element `1 ⊗ d X_{tₓ}` indexed by the germ of `t`.

That image is the local section `1 ⊗ d [t]` of `B ⊗[A[B]] Ω[A[B]/A]` attached to the variable
`[t]` of the canonical presentation
(`Stacks.SheafOfModules.sectionsTensorComparison_one_tmul_D_X`), so this computes the germ of
`1 ⊗ d [t]`.  Since the elements `1 ⊗ d X_s` form a basis of the cotangent space of
`Generators.self Aₓ Bₓ`, the identity determines a linear map out of that stalk from its values
on those local sections, which is how the stalk of the null homotopy inside the canonical map of
Stacks 0E1Y is computed. -/
theorem naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_X :
    letI := algebraSections (Opens.grothendieckTopology X) A B a (op U)
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    letI := algebraGerm A x U hx
    letI := algebraGerm B x U hx
    letI := algebraGermComp A B a x U hx
    haveI := isScalarTower_germ A B a x U hx
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
    ∀ t : ToType (B.obj.obj (op U)),
      naiveCotangentStalkCotangentSpaceEquiv A B a x
          (moduleGerm _ x U hx
            (sectionsTensorComparison.{u, u, u, u} (Opens.grothendieckTopology X) A B a (op U)
              ((1 : ToType (B.obj.obj (op U)))
                ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj (op U)))
                    (ToType (B.obj.obj (op U)))).toExtension.Ring]
                  KaehlerDifferential.D (ToType (A.obj.obj (op U)))
                    ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
                      (ToType (B.obj.obj (op U)))).toExtension.Ring) (MvPolynomial.X t)))) =
        (1 : ToType (stalk B.obj x))
          ⊗ₜ[(Algebra.Generators.self (ToType (stalk A.obj x))
              (ToType (stalk B.obj x))).toExtension.Ring]
            KaehlerDifferential.D (ToType (stalk A.obj x))
              ((Algebra.Generators.self (ToType (stalk A.obj x))
                (ToType (stalk B.obj x))).toExtension.Ring)
              (MvPolynomial.X ((germ B.obj U x hx).hom t)) := by
  let := algebraSections (Opens.grothendieckTopology X) A B a (op U)
  let := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  let := algebraGerm A x U hx
  let := algebraGerm B x U hx
  let := algebraGermComp A B a x U hx
  have _ := isScalarTower_germ A B a x U hx
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  intro t
  refine (naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison A B a x U hx
    ((1 : ToType (B.obj.obj (op U)))
      ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj (op U)))
          (ToType (B.obj.obj (op U)))).toExtension.Ring]
        KaehlerDifferential.D (ToType (A.obj.obj (op U)))
          ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
            (ToType (B.obj.obj (op U)))).toExtension.Ring) (MvPolynomial.X t))).trans ?_
  refine (Algebra.Extension.CotangentSpace.map_tmul (germSelfHom A B a x U hx)
    (1 : ToType (B.obj.obj (op U))) (MvPolynomial.X t)).trans ?_
  refine congrArg₂ (fun (bb : ToType (stalk B.obj x))
      (qq : (Algebra.Generators.self (ToType (stalk A.obj x))
        (ToType (stalk B.obj x))).toExtension.Ring) =>
      bb ⊗ₜ[(Algebra.Generators.self (ToType (stalk A.obj x))
          (ToType (stalk B.obj x))).toExtension.Ring]
        KaehlerDifferential.D (ToType (stalk A.obj x))
          ((Algebra.Generators.self (ToType (stalk A.obj x))
            (ToType (stalk B.obj x))).toExtension.Ring) qq) ?_ ?_
  · exact map_one (algebraMap (ToType (B.obj.obj (op U))) (ToType (stalk B.obj x)))
  · exact germPolynomialHom_X A B x U hx t

end Stacks.SheafOfModules

end

end
