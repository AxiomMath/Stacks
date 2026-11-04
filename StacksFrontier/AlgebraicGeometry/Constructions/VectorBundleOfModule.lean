module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.RelativeSpec
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The vector bundle associated to a quasi-coherent module

Let `S` be a scheme and let `ℰ` be a quasi-coherent `𝒪_S`-module. The *vector bundle associated
to `ℰ`* is the relative spectrum of the symmetric algebra of `ℰ`,

`𝐕(ℰ) = Spec_S(Sym(ℰ))`,

and this file constructs it. Following EGA II, Definition 1.7.8, `ℰ` is **not** assumed to be
finite locally free; for a general quasi-coherent `ℰ` the fibres of `𝐕(ℰ) ⟶ S` need not be
vector spaces of constant dimension, and the name is the source's.

The two ingredients are in place. `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf` is
`Sym(ℰ)` as a sheaf of commutative `𝒪_S`-algebras, in the shape of Stacks Tag 01LM, and
`Stacks.AffineAlgebraEquivalence.relativeSpec` is the relative spectrum of a quasi-coherent sheaf
of commutative `𝒪_S`-algebras. Quasi-coherence of `Sym(ℰ)` is Stacks Tag 01CK, and it is an
instance — `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_symmetricAlgebraSheaf` — deriving it
from quasi-coherence of `ℰ` alone, so `[ℰ.IsQuasicoherent]` is the only hypothesis below. No
finiteness and no local freeness is used anywhere.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.vectorBundle`: **the vector bundle `𝐕(ℰ) = Spec_S(Sym(ℰ))`**,
  with `vectorBundleToBase` its projection to `S` and `vectorBundleAffineOver` the pair of the
  two, as an object of the category of schemes affine over `S`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isAffineOpen_preimage_vectorBundleToBase` and
  `isAffineHom_vectorBundleToBase`: **the projection `𝐕(ℰ) ⟶ S` is an affine morphism**, and the
  part of `𝐕(ℰ)` over an affine open of `S` is affine.

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [EGA II, Definition 1.7.8]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (S : Scheme.{u}) (E : SheafOfModules.{u} S.ringCatSheaf)

/-- **The vector bundle `𝐕(ℰ) = Spec_S(Sym(ℰ))` associated to a quasi-coherent `𝒪_S`-module
`ℰ`**: the relative spectrum of the symmetric algebra of `ℰ`.

Following EGA II, Definition 1.7.8, `ℰ` is not assumed finite locally free. -/
@[stacks 01M2 "the vector bundle V(E) = Spec_S(Sym(E)) associated to a quasi-coherent module",
  ega "II 1.7.8",
  ega "IV 16.4.7",
  ega "IV 16.5.12" "more general",
  ega "IV 18.5.2",
  sga "3 I 4.6.3.1" "partial",
  sga "3 VIB 11.5",
  sga "4½ Sommes_trig 4.6" "partial",
  sga "6 VIII 5.2"]
def vectorBundle [E.IsQuasicoherent] : Scheme.{u} :=
  Stacks.AffineAlgebraEquivalence.relativeSpec (symmetricAlgebraSheaf S E)

/-- **The projection `𝐕(ℰ) ⟶ S`** of the vector bundle associated to `ℰ`. -/
def vectorBundleToBase [E.IsQuasicoherent] : vectorBundle S E ⟶ S :=
  Stacks.AffineAlgebraEquivalence.relativeSpecToBase (symmetricAlgebraSheaf S E)

/-- **The part of `𝐕(ℰ)` lying over an affine open of `S` is affine.** -/
theorem isAffineOpen_preimage_vectorBundleToBase [E.IsQuasicoherent] (U : S.affineOpens) :
    IsAffineOpen (vectorBundleToBase S E ⁻¹ᵁ (U : S.Opens)) :=
  Stacks.AffineAlgebraEquivalence.isAffineOpen_preimage_relativeSpecToBase
    (symmetricAlgebraSheaf S E) U

/-- **The projection of a vector bundle is an affine morphism.** -/
instance isAffineHom_vectorBundleToBase [E.IsQuasicoherent] :
    IsAffineHom (vectorBundleToBase S E) :=
  Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase (symmetricAlgebraSheaf S E)

/-- The vector bundle associated to `ℰ`, as an object of the category of schemes affine over
`S`. -/
def vectorBundleAffineOver [E.IsQuasicoherent] : AffineOver S :=
  Stacks.AffineAlgebraEquivalence.relativeSpecAffineOver (symmetricAlgebraSheaf S E)

end AlgebraicGeometry.Scheme.Modules

end
