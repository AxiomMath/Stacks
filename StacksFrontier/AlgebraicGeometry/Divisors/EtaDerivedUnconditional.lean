module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafTorsionFreeResolutions
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedQuasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# The derived décalage of an effective Cartier divisor exists

Let `X` be a scheme and let `D ⊆ X` be an effective Cartier divisor with ideal sheaf
`I ⊆ 𝒪_X`.  The derived décalage `Lη_I : D(𝒪_X) ⟶ D(𝒪_X)`, its identification with the
chain-level décalage `η_I` on complexes of `I`-torsion-free modules, and the representability of
every object of `D(𝒪_X)` by such a complex all hold with no further hypothesis: the ideal sheaf
of an effective Cartier divisor is invertible, and on a scheme the stalks of the structure sheaf
are local rings, so termwise `I`-torsion-free resolutions exist.

## Main results

* `Stacks.Divisors.Eta.hasTorsionFreeResolutions`: every cochain complex of `𝒪_X`-modules
  receives a quasi-isomorphism from a complex of `I`-torsion-free modules.
* `Stacks.Divisors.Eta.derivedEtaData`: the derived décalage of `D`, together with its two
  characterizing properties.

## Implementation notes

The derived category is the standard model, which is the one the construction of `Lη_I` is
written at; `Stacks.Divisors.Eta.DerivedEta` itself is stated at an arbitrary model, so a
consumer working at another model still carries it as a hypothesis.

A complex of `𝒪_X`-modules together with the torsion-freeness of its terms is the same datum as
a complex of objects of the full subcategory of `I`-torsion-free modules: forgetting the lift
`HomologicalComplex.liftObjectProperty` is the identity, which is what lets the comparison
natural isomorphism be evaluated at a bare complex.  The monomorphy of the ideal inclusion is
passed explicitly, two spellings of the structure sheaf of rings being in play.

## References

* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 0GT3](https://stacks.math.columbia.edu/tag/0GT3)
* [Stacks Project, Tag 0GT5](https://stacks.math.columbia.edu/tag/0GT5)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.IdealTorsion.Eta (HasTorsionFreeResolutions derivedEta derivedEta_iso
  hasTorsionFreeResolutions_of_isInvertible torsionFreeProperty)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors.Eta

variable {X : Scheme.{u}}

/-- **Termwise `I`-torsion-free resolutions exist for an effective Cartier divisor.**  Every
cochain complex of `𝒪_X`-modules receives a quasi-isomorphism from a complex whose terms are
annihilated by no nonzero section of the ideal sheaf: the ideal sheaf is invertible and the
stalks of `𝒪_X` are local rings. -/
@[stacks 0F8Q "the existence of termwise I-torsion-free resolutions for the ideal sheaf of an \
effective Cartier divisor on a scheme"]
theorem hasTorsionFreeResolutions (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    HasTorsionFreeResolutions X.toRingedSpace (idealSheafι D) :=
  hasTorsionFreeResolutions_of_isInvertible X.toRingedSpace _ _
    (mono_idealSheafι D) (isInvertible_idealSheaf D)

/-- **Stacks Project, Tag 0F8Q, for an effective Cartier divisor on a scheme.**  The derived
décalage `Lη_I : D(𝒪_X) ⟶ D(𝒪_X)`, its identification with the chain-level décalage `η_I` on
complexes of `I`-torsion-free `𝒪_X`-modules, and the fact that every object of `D(𝒪_X)` is
represented by such a complex. -/
@[stacks 0F8Q "the functor, its comparison with the chain-level décalage and the \
representability of every object, for the ideal sheaf of an effective Cartier divisor on a \
scheme"]
def derivedEtaData (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] : DerivedEta D where
  functor := @derivedEta X.toRingedSpace (idealSheaf D) (idealSheafι D)
    (mono_idealSheafι D) (isInvertible_idealSheaf D) (hasTorsionFreeResolutions D)
  objIso F htf :=
    (@derivedEta_iso X.toRingedSpace (idealSheaf D) (idealSheafι D)
      (mono_idealSheafι D) (isInvertible_idealSheaf D)
      (hasTorsionFreeResolutions D)).app
      (HomologicalComplex.liftObjectProperty
        (torsionFreeProperty X.toRingedSpace (idealSheafι D)) F htf)
  exists_isIdealTorsionFree_rep K := by
    obtain ⟨G, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) K
    obtain ⟨F, p, htf, hq⟩ := hasTorsionFreeResolutions D G
    have hiso : IsIso (DerivedCategory.Q.map p) :=
      Localization.inverts DerivedCategory.Q
        (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) p
        ((HomologicalComplex.mem_quasiIso_iff p).2 hq)
    exact ⟨F, htf, ⟨@asIso _ _ _ _ _ hiso ≪≫ e⟩⟩

end Stacks.Divisors.Eta

end
