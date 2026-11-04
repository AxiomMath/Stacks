module

public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle

/-!
# Quasi-coherence of the conormal algebra and of the symmetric conormal algebra

Let `i : Z ⟶ X` be an immersion of schemes. The normal cone `C_ZX` and the normal bundle `N_ZX` of
[Stacks, Tag 0636] are the relative spectra over `Z` of the conormal algebra `𝒞_{Z/X,*}` and of
`Sym(𝒞_{Z/X})`, read as sheaves of commutative `𝒪_Z`-algebras. The relative spectrum asks for
those algebra sheaves to be quasi-coherent; this file proves that they are.

For `𝒞_{Z/X,*}` this is [Stacks, Tag 0630] together with the fact that a direct sum of
quasi-coherent modules is quasi-coherent: the homogeneous pieces are quasi-coherent and vanish in
negative degrees, and the module underlying the ungraded realization is the coproduct of the
pieces in nonnegative degrees (`Stacks.RelativeSpec.isQuasicoherent_gradedAlgebraSheaf`). For
`Sym(𝒞_{Z/X})` it is [Stacks, Tag 01CK], applied to the quasi-coherent conormal sheaf.

## Main results

* `Stacks.Conormal.isQuasicoherent_normalBundleAlgebra`: `Sym(𝒞_{Z/X})` is quasi-coherent.

The first half, `𝒞_{Z/X,*}` quasi-coherent, is the instance
`Stacks.Conormal.isQuasicoherent_conormalAlgebraSheaf`. Both are instances, so the normal cone and
the normal bundle of an immersion exist with no hypothesis.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 0636](https://stacks.math.columbia.edu/tag/0636)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **`Sym(𝒞_{Z/X})` is a quasi-coherent sheaf of `𝒪_Z`-algebras**: [Stacks, Tag 01CK] for the
conormal sheaf, which is quasi-coherent. -/
instance isQuasicoherent_normalBundleAlgebra :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra i) :=
  Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf Z (conormalSheafDegreeOne i)

end Stacks.Conormal

end
