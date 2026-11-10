module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinate
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceFiniteType
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic

/-!
# The total space of a line bundle is an affine line over the base

Let `M` be an invertible module on a scheme `Y`. The line bundle `q : L(M) ⟶ Y` of [Stacks, Tag
01M2] is the relative spectrum of `Sym(M^{⊗ -1})`, and over an affine open `V = Spec B` of `Y`
trivializing `M^{⊗ -1}` the sections of that algebra are the polynomial ring `B[z]`, so
`q^{-1}V ≅ 𝔸¹_V` over `V`. Hence the structure morphism of the total space of a line bundle is
an **affine-space bundle of rank one**, and therefore flat, locally of finite type, and of
relative dimension one.

## Main definitions

* `Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv`: **`Γ(V, Sym(ℰ))` is a polynomial
  ring in `r` variables** over an affine open `V` carrying a basis of `Γ(ℰ, V)` indexed by
  `Fin r`, for the ungraded realization of `Sym(ℰ)` in `CommRingCat`.

## Main results

* `Stacks.LineBundle.Situation.isAffineSpaceBundle_totalSpaceToBase`: **the total space of a
  line bundle is an affine-space bundle of rank one over the scheme the bundle lives on.**
* `Stacks.LineBundle.isAffineSpaceBundle_lineBundleProj`: the same for the line bundle
  `lineBundleProj` of [Stacks, Tag 01M2].
* `Stacks.LineBundle.flat_lineBundleProj` and
  `Stacks.LineBundle.locallyOfFiniteTypeRelativeDimension_lineBundleProj`: **the structure
  morphism of the total space of a line bundle is flat of relative dimension one.**

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02NL](https://stacks.math.columbia.edu/tag/02NL)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.SymAlgSections

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] {V : X.Opens}
  (hV : IsAffineOpen V) {r : ℕ} (b : Module.Basis (Fin r) Γ(X, V) Γ(E, V))

/-- **`Γ(V, Sym(ℰ))` is a polynomial ring in `r` variables** over an affine open `V` carrying a
basis of `Γ(ℰ, V)` indexed by `Fin r`, for the ungraded realization of `Sym(ℰ)` in `CommRingCat`.
-/
def ungradedSymSectionsMvPolynomialEquiv :
    (ungradedSymAlgebraSheaf E).right.obj.obj (op V) ≃+* MvPolynomial (Fin r) Γ(X, V) :=
  (ungradedSymSectionsRingEquiv E hV).symm.trans
    (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv

/-- The identification of `Γ(V, Sym(ℰ))` with a polynomial ring carries the structure map of the
algebra sheaf to the inclusion of constants. -/
theorem ungradedSymSectionsMvPolynomialEquiv_app (s : Γ(X, V)) :
    ungradedSymSectionsMvPolynomialEquiv E hV b
        (((ungradedSymAlgebraSheaf E).hom.hom.app (op V)).hom s) = MvPolynomial.C s := by
  rw [← ungradedSymSectionsRingEquiv_algebraMap E hV s]
  change (SymmetricAlgebra.equivMvPolynomial b)
      ((ungradedSymSectionsRingEquiv E hV).symm
        (ungradedSymSectionsRingEquiv E hV
          (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V)) s))) = _
  rw [RingEquiv.symm_apply_apply, AlgEquiv.commutes, MvPolynomial.algebraMap_eq]

end Stacks.SymAlgSections

namespace Stacks.LineBundle

/-- **The line bundle of a situation is finite locally free of rank one** ([Stacks, Tag 0B8M]). -/
instance isFiniteLocallyFreeOfRank_lineBundle (D : Situation.{u}) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.L 1 :=
  Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme D.X D.L

/-- **The total space of a line bundle is an affine-space bundle of rank one.** -/
theorem Situation.isAffineSpaceBundle_totalSpaceToBase (D : Situation.{u}) :
    Stacks.Chow.IsAffineSpaceBundle D.totalSpaceToBase 1 := by
  intro y
  obtain ⟨V, hV, hyV, ⟨b⟩⟩ := Stacks.Chow.exists_isAffineOpen_basis_sections D.L 1 y
  obtain ⟨e, he⟩ := Stacks.Chow.exists_iso_affineSpace_of_mvPolynomialSections
    D.algebraSheaf ⟨V, hV⟩ 1
    (Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv D.L hV b)
    (Stacks.SymAlgSections.ungradedSymSectionsMvPolynomialEquiv_app D.L hV b)
  exact ⟨V, hyV, e, he⟩

/-- **The total space of a line bundle is flat over the scheme the bundle lives on.** -/
theorem Situation.flat_totalSpaceToBase (D : Situation.{u}) :
    AlgebraicGeometry.Flat D.totalSpaceToBase :=
  Stacks.Chow.flat_of_isAffineSpaceBundle _ 1 D.isAffineSpaceBundle_totalSpaceToBase

/-- **The total space of a line bundle has relative dimension one over the scheme the bundle
lives on.** -/
theorem Situation.relativeDimension_totalSpaceToBase (D : Situation.{u}) :
    AlgebraicGeometry.RelativeDimension D.totalSpaceToBase 1 :=
  Stacks.Chow.relativeDimension_of_isAffineSpaceBundle _ 1
    D.isAffineSpaceBundle_totalSpaceToBase

variable (Y : Scheme.{u}) (M : Y.Modules)
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

include hM in
/-- **The line bundle `L(M) ⟶ Y` of an invertible module is an affine-space bundle of rank one**,
for the line bundle `lineBundleProj` of [Stacks, Tag 01M2]. -/
theorem isAffineSpaceBundle_lineBundleProj :
    Stacks.Chow.IsAffineSpaceBundle (lineBundleProj Y M) 1 :=
  (inverseSituation Y M).isAffineSpaceBundle_totalSpaceToBase

include hM in
/-- **The structure morphism of the total space of a line bundle is flat.** -/
instance flat_lineBundleProj : AlgebraicGeometry.Flat (lineBundleProj Y M) :=
  Stacks.Chow.flat_of_isAffineSpaceBundle _ 1 (isAffineSpaceBundle_lineBundleProj Y M)

include hM in
/-- **The structure morphism of the total space of a line bundle is locally of finite type of
relative dimension one**, in the bundled form
`AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension`. -/
theorem locallyOfFiniteTypeRelativeDimension_lineBundleProj :
    AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension.{u} 1 (lineBundleProj Y M) :=
  ⟨inferInstanceAs (LocallyOfFiniteType (inverseSituation Y M).totalSpaceToBase),
    (inverseSituation Y M).relativeDimension_totalSpaceToBase⟩

end Stacks.LineBundle

end
