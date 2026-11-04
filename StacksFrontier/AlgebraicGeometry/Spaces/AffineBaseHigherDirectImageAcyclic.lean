module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageSectionsOverChart
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional

/-!
# Higher direct images over an affine base are acyclic for global sections

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` with `Y` **affine**, and let
`F` be an `𝒪_X`-module each of whose higher direct images `R^q f_*F` is quasi-coherent.  Then
every `R^q f_*F` is acyclic for global sections on `Y`: `H^p(Y, R^q f_*F) = 0` for `p > 0`.

This is the hypothesis `hcoh` of `AlgebraicGeometry.Space.globalSectionsRightDerivedIso` and of
`AlgebraicGeometry.Space.cohomologyChartIsoSectionsHigherDirectImage` (Stacks 08EX), for which
the source's proof of 08EX cites Stacks 01XB on the small étale site, that is Stacks 03DW. The
quasi-coherence of the higher direct images is Stacks 0720. Over an affine base, 08EX then
carries only the acyclicity of the direct image of an injective module, Stacks 072Z.

## Main results

* `AlgebraicGeometry.Space.acyclicHigherDirectImages_of_isAffineSpace`: **the `hcoh` of
  Stacks 08EX over an affine base**, from quasi-coherence of the higher direct images.
* `AlgebraicGeometry.Space.acyclicHigherDirectImages_of_isAffineSpace_of_affineTarget`: the same
  with the quasi-coherence obtained from Stacks 0720, for a quasi-compact and quasi-separated `f`
  and a quasi-coherent `F`.
* `AlgebraicGeometry.Space.globalSectionsRightDerivedIsoOfIsAffineSpace`: **Stacks 08EX over an
  affine base**, `H^n(X, F) ≅ Γ(Y, R^nf_*F)`, with only Stacks 072Z carried. Its hypotheses are
  the ones the source carries in clause (2) of Stacks 073K.

## References

* [Stacks Project, Tag 08EX](https://stacks.math.columbia.edu/tag/08EX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The hypothesis `hcoh` of Stacks 08EX, over an affine base.**  If the base `Y` is an affine
algebraic space and every higher direct image `R^q f_*F` is quasi-coherent, then every `R^q f_*F`
is acyclic for global sections on `Y`. -/
theorem acyclicHigherDirectImages_of_isAffineSpace (f : X ⟶ Y)
    (hY : IsAffineSpace B S hS Y.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hqc : ∀ q : ℕ,
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      (((modulePushforward B S hS f).rightDerived q).obj F).IsQuasicoherentOnSite) :
    AcyclicHigherDirectImages B S hS f F :=
  fun q _ hp ↦
    isZero_rightDerived_globalSections_of_isAffineSpace B S hS Y hY _ (hqc q) _ hp

/-- **The hypothesis `hcoh` of Stacks 08EX for a quasi-compact and quasi-separated morphism to an
affine base**, with nothing carried: every higher direct image `R^q f_*F` of a quasi-coherent
`F` is acyclic for global sections on `Y`. -/
theorem acyclicHigherDirectImages_of_isAffineSpace_of_affineTarget (f : X ⟶ Y)
    (hY : IsAffineSpace B S hS Y.1) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] :
    AcyclicHigherDirectImages B S hS f F :=
  acyclicHigherDirectImages_of_isAffineSpace B S hS f hY F fun q ↦
    isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS f hfqc hfqs F q

/-- **Stacks 08EX over an affine base, with only Stacks 072Z carried**:  for a quasi-compact and
quasi-separated `f : X ⟶ Y` with `Y` an affine algebraic space and `F` a quasi-coherent
`𝒪_X`-module, the cohomology `H^n(X, F)` — read as the right derived functor of the composite
`Γ(Y, f_*−)` — is the module of global sections on `Y` of the higher direct image `R^nf_*F`.

The only further hypothesis is `h072Z`, Stacks 072Z through part (3) of Stacks 0731: acyclicity
for global sections of the direct image of an injective module. The other hypotheses are those
the source carries in clause (2) of **Stacks 073K**: `f` quasi-compact and quasi-separated, `F`
quasi-coherent, the base affine. -/
def globalSectionsRightDerivedIsoOfIsAffineSpace (f : X ⟶ Y)
    (hY : IsAffineSpace B S hS Y.1) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (h072Z : AcyclicPushforwardOfInjective B S hS f) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    ((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived n).obj F ≅
      (globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj
        (((modulePushforward B S hS f).rightDerived n).obj F) :=
  globalSectionsRightDerivedIso B S hS f F h072Z
    (acyclicHigherDirectImages_of_isAffineSpace_of_affineTarget B S hS f hY hfqc hfqs F) n

end AlgebraicGeometry.Space

end

end
