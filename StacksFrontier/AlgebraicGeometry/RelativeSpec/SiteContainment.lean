module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.Size.AffineMorphism

/-!
# The relative spectrum of a quasi-coherent algebra lies in a big fppf site

The relative spectrum `\underline{Spec}_S(A)` of a quasi-coherent sheaf of commutative
`𝒪_S`-algebras is affine over `S`, with sections `A(U)` over an affine open `U` of `S`. Hence it
is an object of a big fppf site containing `S` as soon as the cardinalities of the rings `A(U)`
are bounded by a cardinal below the cutoff.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_relativeSpec`: the relative spectrum of a
  quasi-coherent algebra sheaf on a scheme contained in a big fppf site is contained in that
  site, provided the sections of the algebra over the affine opens of the base are bounded by a
  cardinal below the cutoff.
-/

@[expose] public noncomputable section

open Cardinal CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- The relative spectrum of a quasi-coherent algebra lies in a big fppf site containing the
base, as soon as the rings of sections of the algebra over the affine opens of the base are
bounded by a cardinal below the cutoff. -/
theorem BigFppfSite.contains_relativeSpec (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (A : Stacks.RelativeSpec.AlgebraSheaf S)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] (hS : B.Contains S)
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hA : ∀ U : S.affineOpens, #(A.right.obj.obj (op (U : S.Opens))) ≤ μ) :
    B.Contains (Stacks.AffineAlgebraEquivalence.relativeSpec A) :=
  B.contains_of_isAffineHom (Stacks.AffineAlgebraEquivalence.relativeSpecToBase A) hS hμ
    fun U => le_of_eq_of_le
      (mk_congr
        (((forget CommRingCat.{u}).mapIso
          (Stacks.AffineAlgebraEquivalence.sectionsIso A U)).toEquiv))
      (hA U)

end AlgebraicGeometry

end
