module

public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraAffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedGradedPolynomialCover
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Free
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.SchemeFinitePieces
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraTotalUnitalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The homogeneous sections of `𝒪_X[x_i]` over an affine open form a Noetherian ring

Let `X` be a scheme, `ι` a finite index type and `𝓟 = Sym(𝒪_X^ι)` the polynomial algebra on
`ι` variables, which is `SheafOfModules.sheafifiedSymmetricAlgebra` of the free sheaf of
modules on `ι`. That object is `Stacks.Coherent.polyAlgebra X ι`, declared in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedGradedPolynomialCover`; the results
below are stated of it directly rather than of a second abbreviation for it. Over an open `V`
the homogeneous sections of `𝓟` assemble into a ring
`Stacks.GradedAlgebra.Total`. This file proves two things about that ring, for `V` affine and
`Γ(X, V)` Noetherian:

* it is commutative, and
* it is Noetherian.

Both come from one comparison. `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra` is a second
construction of the symmetric algebra of a module sheaf on a scheme, and its ring of
homogeneous sections over an affine open has already been identified with the symmetric algebra
of the sections, by `Stacks.SymAlgSections.symPowersRingEquiv`. The two constructions are both
universal for a degree-one generator of the same sheaf of modules, so they are canonically
isomorphic in every degree, and
`SheafOfModules.GradedAlgebra.UnitalHom.totalRingHom` turns that isomorphism into a surjective
ring homomorphism between their rings of homogeneous sections. Commutativity and Noetherianity
are then carried across: the source is `Sym_{Γ(X, V)}(Γ(X, V)^ι)`, which is a polynomial ring in
`ι` variables by `SymmetricAlgebra.equivMvPolynomial`, hence Noetherian by the Hilbert basis
theorem.

The Noetherianity is what makes the graded kernel of a presentation by `𝓟`-modules again of
finite type: that is the step of part (2) of [Stacks, Tag 0897] at which the dévissage over an
auxiliary graded algebra has to produce a module it can re-enter the induction with.

## Main results

* `Stacks.SymmetricFree.isCommutative_symmetricAlgebraFree` — `Sym(𝒪_X^ι)` is a commutative
  sheaf of graded algebras.
* `Stacks.SymmetricFree.isNoetherianRing_total_symmetricAlgebraFree` — its ring of homogeneous
  sections over an affine open of a Noetherian scheme is Noetherian.

## References

* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SymmetricFree

variable (X : Scheme.{u}) (ι : Type u) [Finite ι]

/-- **The comparison of the two constructions of the symmetric algebra of `𝒪_X^ι`**, from
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra` to the sheafified symmetric algebra: both
are universal for a pairwise-commuting degree-one generator of `𝒪_X^ι`, so each descends to
the other. -/
def symmetricAlgebraFreeDesc : SheafOfModules.GradedAlgebra.UnitalHom
    (Scheme.Modules.symmetricAlgebra X (Stacks.SymGraded.freeModule (X := X) ι))
    (Stacks.Coherent.polyAlgebra X ι) :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X
      (Stacks.SymGraded.freeModule (X := X) ι)).isUniversal.desc _ _
    (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
      (Opens.grothendieckTopology ↥X)
      (Stacks.SymGraded.freeModule (X := X) ι)).isUniversal.1

/-- The comparison is an isomorphism in every degree: it is the homogeneous component of
`SheafOfModules.GradedAlgebra.IsUniversal.pieceIso`. -/
instance isIso_symmetricAlgebraFreeDesc_app (n : ℤ) :
    IsIso ((symmetricAlgebraFreeDesc X ι).app n) :=
  inferInstanceAs (IsIso
    (((Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X
        (Stacks.SymGraded.freeModule (X := X) ι)).isUniversal.pieceIso
      (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
        (Opens.grothendieckTopology ↥X)
        (Stacks.SymGraded.freeModule (X := X) ι)).isUniversal n).hom))

omit [Finite ι] in
/-- The comparison is surjective on the sections of every homogeneous piece over every open:
it is invertible there. -/
theorem surjective_symmetricAlgebraFreeDesc_app (n : ℤ) (W : (Opens ↥X)ᵒᵖ) :
    Function.Surjective (((symmetricAlgebraFreeDesc X ι).app n).val.app W) := fun y =>
  ⟨(inv ((symmetricAlgebraFreeDesc X ι).app n)).val.app W y,
    SheafOfModules.GradedAlgebra.app_inv_app_apply (symmetricAlgebraFreeDesc X ι) n W y⟩

/-- **`Sym(𝒪_X^ι)` is commutative.** Commutativity is known for
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra` and the comparison is surjective on
sections in every degree, so it transports. -/
instance isCommutative_symmetricAlgebraFree :
    (Stacks.Coherent.polyAlgebra X ι).IsCommutative :=
  letI : (Scheme.Modules.symmetricAlgebra X
      (Stacks.SymGraded.freeModule (X := X) ι)).IsCommutative :=
    ⟨Scheme.Modules.symmetricAlgebra_mul_comm X _⟩
  SheafOfModules.GradedAlgebra.UnitalHom.isCommutative_of_surjective
    (symmetricAlgebraFreeDesc X ι) (surjective_symmetricAlgebraFreeDesc_app X ι)

variable {X ι}

/-- **The homogeneous sections of `𝒪_X[x_i]` over an affine open form a Noetherian ring.**

Over an affine open `V` the ring of homogeneous sections of
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra` is `Sym_{Γ(X, V)}(Γ(X, V)^ι)`, by
`Stacks.SymAlgSections.symPowersRingEquiv` and the graded decomposition of a symmetric algebra;
the sections of the free sheaf on `ι` form a free module on `ι`, so that symmetric algebra is
the polynomial ring `Γ(X, V)[x_i : i ∈ ι]`, Noetherian by the Hilbert basis theorem. The
comparison with the sheafified symmetric algebra is surjective on homogeneous sections, and a
surjective ring homomorphism out of a Noetherian ring has Noetherian target. -/
@[sga "5 V 5.1.4" "special case"]
theorem isNoetherianRing_total_symmetricAlgebraFree {V : X.Opens} (hV : IsAffineOpen V)
    [IsNoetherianRing Γ(X, V)] :
    IsNoetherianRing ((Stacks.Coherent.polyAlgebra X ι).toPresheafGradedAlgebra.Total (op V)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let b : Module.Basis ι Γ(X, V) Γ(Stacks.SymGraded.freeModule (X := X) ι, V) :=
    Module.Basis.ofEquivFun
      (Stacks.SheafOfModules.freeSectionsIso (R := X.ringCatSheaf) ι (op V)).symm.toLinearEquiv
  have : IsNoetherianRing
      (SymmetricAlgebra Γ(X, V) Γ(Stacks.SymGraded.freeModule (X := X) ι, V)) :=
    isNoetherianRing_of_ringEquiv (MvPolynomial ι Γ(X, V))
      (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv
  have : IsNoetherianRing
      ((Scheme.Modules.symmetricAlgebra X
        (Stacks.SymGraded.freeModule (X := X) ι)).toPresheafGradedAlgebra.Total (op V)) :=
    isNoetherianRing_of_ringEquiv
      (SymmetricAlgebra Γ(X, V) Γ(Stacks.SymGraded.freeModule (X := X) ι, V))
      ((DirectSum.decomposeRingEquiv
          (fun n : ℕ => SymPow.symmetricPower n Γ(X, V)
            Γ(Stacks.SymGraded.freeModule (X := X) ι, V))).trans
        (Stacks.SymAlgSections.symPowersRingEquiv
          (Stacks.SymGraded.freeModule (X := X) ι) hV))
  exact isNoetherianRing_of_surjective _ _
    (SheafOfModules.GradedAlgebra.UnitalHom.totalRingHom (symmetricAlgebraFreeDesc X ι) (op V))
    (SheafOfModules.GradedAlgebra.UnitalHom.surjective_totalRingHom
      (symmetricAlgebraFreeDesc X ι) (op V)
      fun n => surjective_symmetricAlgebraFreeDesc_app X ι n (op V))

end Stacks.SymmetricFree

end
