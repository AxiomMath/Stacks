module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.SymmetricToLaurentEpi
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.UngradedFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraHomComparison

/-!
# The Laurent spectrum over the total space of a line bundle

Let `L` be an invertible module on a scheme `X`. The total space of `L` is the relative spectrum
of `Sym(L) = ⨁_{n ≥ 0} L^{⊗ n}` over `X`, and the Laurent spectrum is the relative spectrum of
the Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}`. The comparison `Sym(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` of graded
algebras realizes to a morphism of sheaves of commutative `𝒪_X`-algebras, whose relative
spectrum is a morphism of the Laurent spectrum into the total space over `X`. The content of
Section 50.10 is that this morphism identifies the Laurent spectrum with the complement of the
zero section; this file constructs the morphism and its compatibility with the structure
morphisms to `X`.

## Main definitions

* `Stacks.LineBundle.Situation.algebraSheafToLaurent`: **the comparison
  `Sym(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` of the algebra sheaf of the line bundle with its Laurent algebra
  sheaf**, the ungraded realization of the comparison of graded algebras.
* `Stacks.LineBundle.Situation.laurentToTotalSpace`: **the morphism from the Laurent spectrum of
  the line bundle to its total space** induced by that comparison.

## Main results

* `Stacks.LineBundle.Situation.withAlgebra_laurentAlgebraSheaf`: carrying the Laurent algebra
  sheaf on the relative-spectrum situation of the total space gives the relative-spectrum
  situation of the Laurent spectrum, so the two relative spectra are literally comparable.
* `Stacks.LineBundle.Situation.algebraSheafToLaurent_incl`: the comparison of algebra sheaves
  carries a homogeneous local section of `Sym(L)` to its image in the same degree, which
  characterizes it.
* `Stacks.LineBundle.Situation.laurentToTotalSpace_comp_totalSpaceToBase`: the morphism from the
  Laurent spectrum to the total space is a morphism over `X`.
* `Stacks.LineBundle.Situation.ι_laurentToTotalSpace`: over an affine open `U` of `X` the
  morphism is the spectrum of the comparison on sections over `U`, read in the chart of `U`.

## Implementation notes

The relative-spectrum situation of the Laurent spectrum is `by rfl` the situation of the total
space with its algebra replaced by the Laurent algebra sheaf, because
`Stacks.RelativeSpec.RelativeSpecSituation.withAlgebra` is a `reducible` abbreviation building a
structure literal and quasi-coherence is a proposition. That is what lets the generic comparison
`Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom` be read directly as a morphism
`D.laurentSpectrum ⟶ D.totalSpace` without any transport.

`TopCat.Sheaf` is a semireducible definition for `CategoryTheory.Sheaf`, so a goal mentioning
both spellings of the base of the category of modules on a scheme is not type-correct at
reducible transparency; the statements here are therefore discharged in term mode, as recorded
in the implementation notes of `StacksFrontier.AlgebraicGeometry.RelativeSpec.CanonicalMap`.

## References

* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The relative-spectrum situation of the Laurent spectrum is that of the total space with
its algebra replaced by the Laurent algebra sheaf.** Both are the scheme on which `L` lives
carrying a quasi-coherent algebra, and quasi-coherence is a proposition. -/
theorem Situation.withAlgebra_laurentAlgebraSheaf :
    D.relativeSpecSituation.withAlgebra D.laurentAlgebraSheaf
        D.isQuasicoherent_laurentAlgebraSheaf =
      D.laurentRelativeSpecSituation :=
  rfl

/-- **The comparison `Sym(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` of the algebra sheaf of the line bundle with
its Laurent algebra sheaf**: the ungraded realization of the unique unital homomorphism of
graded algebras extending the degree-one generator. -/
def Situation.algebraSheafToLaurent : D.algebraSheaf ⟶ D.laurentAlgebraSheaf :=
  Stacks.RelativeSpec.ungradedAlgebraSheafMap D.X D.symmetricAlgebra D.laurentAlgebra
    D.symmetricAlgebra_mul_comm D.laurentAlgebra_mul_comm D.symmetricToLaurent

/-- **The comparison of the algebra sheaf of the line bundle with its Laurent algebra sheaf
carries a homogeneous local section of `Sym(L)` to its image in the same degree**, which
characterizes it. -/
theorem Situation.algebraSheafToLaurent_incl (n : ℤ) (U : D.X.Opens)
    (x : (D.symmetricAlgebra.piece n).val.obj (op U)) :
    (D.algebraSheafToLaurent.right.hom.app (op U)).hom (D.algebraSheafIncl n U x) =
      D.laurentAlgebraSheafIncl n U ((D.symmetricToLaurent.app n).val.app (op U) x) :=
  Stacks.RelativeSpec.ungradedAlgebraSheafMap_incl D.X D.symmetricAlgebra D.laurentAlgebra
    D.symmetricAlgebra_mul_comm D.laurentAlgebra_mul_comm D.symmetricToLaurent n U x

/-- **The morphism from the Laurent spectrum of the line bundle to its total space**: the
relative spectrum of the comparison `Sym(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}`, in the direction opposite to
that comparison. -/
def Situation.laurentToTotalSpace : D.laurentSpectrum ⟶ D.totalSpace :=
  Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom D.relativeSpecSituation
    D.laurentAlgebraSheaf D.isQuasicoherent_laurentAlgebraSheaf D.algebraSheafToLaurent

/-- **The morphism from the Laurent spectrum of the line bundle to its total space is a morphism
over the scheme on which `L` lives.** -/
theorem Situation.laurentToTotalSpace_comp_totalSpaceToBase :
    D.laurentToTotalSpace ≫ D.totalSpaceToBase = D.laurentSpectrumToBase :=
  Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_toBase D.relativeSpecSituation
    D.laurentAlgebraSheaf D.isQuasicoherent_laurentAlgebraSheaf D.algebraSheafToLaurent

/-- **The morphism from the Laurent spectrum to the total space carries the part of the Laurent
spectrum lying over an open `U` of the base onto the part of the total space lying over `U`**,
both being the inverse image of `U` along a structure morphism. -/
theorem Situation.laurentToTotalSpace_preimage (U : D.X.Opens) :
    D.laurentToTotalSpace ⁻¹ᵁ (D.totalSpaceToBase ⁻¹ᵁ U) = D.laurentSpectrumToBase ⁻¹ᵁ U :=
  (Scheme.Hom.comp_preimage D.laurentToTotalSpace D.totalSpaceToBase U).symm.trans
    (congrArg (fun k : D.laurentSpectrum ⟶ D.X => k ⁻¹ᵁ U)
      D.laurentToTotalSpace_comp_totalSpaceToBase)

/-- **Over an affine open `U` of the base the morphism from the Laurent spectrum to the total
space is the spectrum of the comparison on sections over `U`**: on the inverse image of `U` it is
the canonical map to the spectrum of the sections of the Laurent algebra sheaf, followed by the
spectrum of the comparison and the universal algebra map, and then the chart of `U`. -/
theorem Situation.ι_laurentToTotalSpace (U : D.X.affineOpens) :
    (D.laurentSpectrumToBase ⁻¹ᵁ U.1).ι ≫ D.laurentToTotalSpace =
      (D.laurentSpectrumToBase ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map (D.algebraSheafToLaurent.right.hom.app (op U.1) ≫
            (Stacks.RelativeSpec.universalAlgebraMap
              D.laurentRelativeSpecSituation).right.app (op U.1)) ≫
          (Stacks.RelativeSpec.gluedSpectrum D.relativeSpecSituation).chart U :=
  Stacks.RelativeSpec.ι_relativeSpectrumMapOfAlgebraHom D.relativeSpecSituation
    D.laurentAlgebraSheaf D.isQuasicoherent_laurentAlgebraSheaf D.algebraSheafToLaurent U

/-- **The morphism from the Laurent spectrum to the total space, read on sections over an affine
open `U` of the base**: the universal algebra map of `Sym(L)` at `U` followed by the sections of
the morphism is the comparison of algebra sheaves at `U` followed by the universal algebra map of
the Laurent algebra. -/
theorem Situation.laurentToTotalSpace_appLE (U : D.X.affineOpens) :
    (Stacks.RelativeSpec.universalAlgebraMap D.relativeSpecSituation).right.app (op U.1) ≫
        D.laurentToTotalSpace.appLE (D.totalSpaceToBase ⁻¹ᵁ U.1)
          (D.laurentSpectrumToBase ⁻¹ᵁ U.1) (D.laurentToTotalSpace_preimage U.1).ge =
      D.algebraSheafToLaurent.right.hom.app (op U.1) ≫
        (Stacks.RelativeSpec.universalAlgebraMap
          D.laurentRelativeSpecSituation).right.app (op U.1) :=
  Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_appLE D.relativeSpecSituation
    D.laurentAlgebraSheaf D.isQuasicoherent_laurentAlgebraSheaf D.algebraSheafToLaurent U
    (D.laurentToTotalSpace_preimage U.1).ge

end Stacks.LineBundle

end
