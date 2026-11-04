module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentTower
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSections

/-!
# The comparison on sections, on the differential of a variable

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a site and let `U` be an object
of the site.  The degree `0` component

`sectionsTensorComparison : B(U) ⊗[A(U)[B(U)]] Ω[A(U)[B(U)]/A(U)] ⟶ (B ⊗[A[B]] Ω[A[B]/A])(U)`

of the canonical map `NL_{B(U)/A(U)} ⟶ NL_{B/A}(U)` of
`StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSections` is pinned down by its values
`b ⊗ d p ↦ b • (1 ⊗ d (λ p))` on pure differentials.  This file reads that formula on the
*variable* `X_t` attached to a section `t` of `B` over `U`: there the right-hand side is the
local section `1 ⊗ d [t]` of `B ⊗[A[B]] Ω[A[B]/A]`, whose value under the null homotopy of a
tower is computed by
`Stacks.SheafOfModules.naiveCotangentTowerHomotopy_tensorDifferential_variableSection`.

The two sides of that identity are the two halves of the proof of **Stacks 0E1Y** that have to
meet: the comparison on sections is what carries information to a stalk, while the homotopy
inside the canonical map `c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]` of that tag is described on the local
sections `1 ⊗ d [t]`.

## Main results

* `Stacks.SheafOfModules.freeAlgebraSectionsMap_variable`: the lax comparison
  `A(U)[B(U)] ⟶ (A[B])(U)` carries the variable `X_t` to the variable `[t]` of `A[B]`, that is,
  to `Stacks.SheafOfModules.variableSection`.
* `Stacks.SheafOfModules.sectionsTensorComparison_one_tmul_D_X`: the degree `0` component of the
  comparison on sections carries `1 ⊗ d X_t` to the local section `1 ⊗ d [t]`.
* `Stacks.SheafOfModules.naiveCotangentTowerHomotopy_sectionsTensorComparison_one_tmul_D_X`: the
  null homotopy of a tower carries the image of `1 ⊗ d X_t` to the conormal class of
  `[β t] - γ t`, which for `γ = 𝟙 B` and `β = b` is the relation `[φ(b)] - b[1]` of the proof of
  Stacks 0E1Y.

## Implementation notes

The local section `1 ⊗ d [t]` is written at the *canonical* presentation in the spelling
`Stacks.Sites.FreeAlgebra.canonicalPresentation`, which is the one the tower homotopy uses,
rather than in the spelling `presentation J A B a (underlyingPresheaf J B) (𝟙 _)` used by the
comparison on sections.  The two are definitionally equal
(`Stacks.Sites.FreeAlgebra.canonicalPresentation_eq_desc`) but not syntactically so, which is
why the proof below is a term-mode `Eq.trans` chain rather than a `rw`.

The same bridge is also why these identities are stated over sections rather than over a stalk.
`Stacks.Sites.Conormal.tensorDifferential` is typed through `(conormalSequence …).X₂`, which is
`Stacks.Sites.Conormal.tensorDifferentialsSheaf` only after the sheafification in both is
unfolded; that unification is affordable here, under `.obj U`, and it is not affordable under a
stalk.  The companion file
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineGermVariable` therefore takes the germ
of the left-hand side of `sectionsTensorComparison_one_tmul_D_X` rather than of the right.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), the comparison on
  sections.
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the canonical
  polynomial presentation.
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), where the identity is
  consumed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v u w z

noncomputable section

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {S : Type u} [Category.{v} S] (J : GrothendieckTopology S)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (U : Sᵒᵖ)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The lax comparison carries a variable to a variable.**  The component at `U` of the unit of
sheafification `A(U)[B(U)] ⟶ (A[B])(U)` sends the variable `X_t` indexed by a section `t` of `B`
over `U` to the variable `[t]` of `A[B]`.  Both are the image of `X_t` under the unit, the
variables of `A[B]` being by definition the sheafification of the variables of `A(-)[B(-)]`. -/
theorem freeAlgebraSectionsMap_variable (t : ToType (B.obj.obj U)) :
    freeAlgebraSectionsMap J A B U (MvPolynomial.X t) = variableSection J A B U t := rfl

/-- **The degree `0` comparison on sections, on the differential of a variable.**  The degree `0`
component of `NL_{B(U)/A(U)} ⟶ NL_{B/A}(U)` carries `1 ⊗ d X_t` to the local section `1 ⊗ d [t]`
of `B ⊗[A[B]] Ω[A[B]/A]` attached to the variable `[t]` of the canonical presentation.

This is `Stacks.SheafOfModules.sectionsTensorComparison_tmul` read at `b = 1` and
`p = X_t`, and it is the sections-level half of the comparison of the canonical map of
Stacks 0E1Y with its stalkwise description: the right-hand side is exactly the local section
whose image under the null homotopy of a tower is computed by
`Stacks.SheafOfModules.naiveCotangentTowerHomotopy_tensorDifferential_variableSection`. -/
theorem sectionsTensorComparison_one_tmul_D_X (t : ToType (B.obj.obj U)) :
    letI := algebraSections J A B a U
    sectionsTensorComparison.{v, u, w, z} J A B a U
        ((1 : ToType (B.obj.obj U))
          ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj U))
              (ToType (B.obj.obj U))).toExtension.Ring]
            KaehlerDifferential.D (ToType (A.obj.obj U))
              ((Algebra.Generators.self (ToType (A.obj.obj U))
                (ToType (B.obj.obj U))).toExtension.Ring) (MvPolynomial.X t)) =
      tensorDifferential.{v, u, w, z} J A (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (canonicalPresentation J A B a) U (variableSection J A B U t) := by
  let := algebraSections J A B a U
  refine Eq.trans (sectionsTensorComparison_tmul.{v, u, w, z} J A B a U 1 (MvPolynomial.X t)) ?_
  exact Eq.trans (one_smul _ _)
    (congrArg (tensorDifferential.{v, u, w, z} J A
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (canonicalPresentation J A B a) U) (freeAlgebraSectionsMap_variable J A B U t))

/-! ### The null homotopy of a tower on the sections-level generators -/

variable (C : Sheaf J CommRingCat.{w}) (b : B ⟶ C) (f : A ⟶ B) (β : B ⟶ C) (γ : B ⟶ B)
  (hβ : γ ≫ b = β) (hf : a ≫ γ = f)

include hβ hf in
/-- **The null homotopy of a tower, on the image of `1 ⊗ d X_t`.**  The homotopy
`B ⊗_{A[B]} Ω_{A[B]/A} ⟶ K/K²` of
`Stacks.SheafOfModules.naiveCotangentTowerNullHomotopy` carries the image under the comparison
on sections of `1 ⊗ d X_t` to the conormal class of `[β t] - γ t`.

This is
`Stacks.SheafOfModules.naiveCotangentTowerHomotopy_tensorDifferential_variableSection` read
through `Stacks.SheafOfModules.sectionsTensorComparison_one_tmul_D_X`, and it is the shape in
which the formula is consumed: the germ at a point of the element on the left is computed by
`Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_X`,
which is the basis element `1 ⊗ d X_{tₓ}` of the cotangent space of the canonical presentation
of the stalks.  For `γ = 𝟙 B` and `β = b` the right-hand side is the relation
`[φ(b)] - b[1]` of the proof of Stacks 0E1Y. -/
theorem naiveCotangentTowerHomotopy_sectionsTensorComparison_one_tmul_D_X
    (t : ToType (B.obj.obj U)) :
    letI := algebraSections J A B a U
    (naiveCotangentTowerHomotopy.{v, u, w, z} J A B C a b f β γ hβ hf).val.app U
        (sectionsTensorComparison.{v, u, w, z} J A B a U
          ((1 : ToType (B.obj.obj U))
            ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj U))
                (ToType (B.obj.obj U))).toExtension.Ring]
              KaehlerDifferential.D (ToType (A.obj.obj U))
                ((Algebra.Generators.self (ToType (A.obj.obj U))
                  (ToType (B.obj.obj U))).toExtension.Ring) (MvPolynomial.X t))) =
      conormalClass.{v, u, w, z} J B (freeAlgebraSheaf J B (underlyingPresheaf J C)) C
        (freeAlgebraSheafCoefficientMap J B (underlyingPresheaf J C))
        (canonicalPresentation J B C b) U (towerHomotopyRelation J B C b β γ hβ U t) := by
  let := algebraSections J A B a U
  rw [sectionsTensorComparison_one_tmul_D_X.{v, u, w, z} J A B a U t]
  exact naiveCotangentTowerHomotopy_tensorDifferential_variableSection.{v, u, w, z}
    J A B C a b f β γ hβ hf U t

end Stacks.SheafOfModules

end

end
