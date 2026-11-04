module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseHigherDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatBaseChangePushforwardCollapse

/-!
# The two sides of Stacks 073K part (2) are global sections of the two sides of part (1)

**Stacks 073K**, part (2) is a statement about modules:  its two sides are
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologySource`, which is
`H^i(X, 𝓕) ⊗_A B`, and `…affineCohomologyTarget`, which is `H^i(X', 𝓕')`, both read over
`B = Γ(Y', 𝒪_{Y'})`.  Part (1) is a statement about sheaves:  its degreewise map is
`AlgebraicGeometry.Space.higherDirectImageBaseChangeMap`, whose two sides are `g^*R^if_*𝓕` and
`R^if'_*𝓕'` as `𝒪_{Y'}`-modules.  This file identifies **`H^i(X, 𝓕)` read over `A` with
`Γ(Y, R^if_*𝓕)`, and `H^i(X', 𝓕')` read over `B` with `Γ(Y', R^if'_*𝓕')`.**  With the second of
those, part (1)'s *target* over an affine base **is** part (2)'s target.

The identification is the composite of
`AlgebraicGeometry.Space.derivedGlobalSectionsPushforwardIso`, the derived form of
**Stacks 0732** — `R^iΓ(Y, f_*−) ≅ R^iΓ(X, −)` with scalars restricted along
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` — and
`AlgebraicGeometry.Space.globalSectionsRightDerivedIsoOfIsAffineSpace`, **Stacks 08EX** over an
affine base, whose hypothesis `h072Z` is the only one carried.

## Main definitions

* `AlgebraicGeometry.Space.cohomologyRestrictScalarsIsoGlobalSectionsHigherDirectImage`: for a
  quasi-compact and quasi-separated `f : X ⟶ Y` with `Y` affine and `𝓕` quasi-coherent,
  **`H^i(X, 𝓕)` read over `Γ(Y, 𝒪_Y)` is `Γ(Y, R^if_*𝓕)`.**
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyOverBaseIsoGlobalSections`: the same
  at part (2)'s own left hand side before extension of scalars.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyTargetIsoGlobalSections`:
  **part (2)'s right hand side is `Γ(Y', R^if'_*𝓕')`**, the global sections of part (1)'s target.

## Implementation notes

*What is left.*  Identifying part (1)'s degreewise map over an affine base with part (2)'s
comparison map needs the target sides identified, the source sides identified, and the square of
the identifications and the two maps commuting.  Only the **target** is done here.  The
**source** is not:  part (2)'s source is `ModuleCat.extendScalars (globalSectionsRingHomSite g)`
applied to `Γ(Y, R^if_*𝓕)` — the tensor product `Γ(Y, R^if_*𝓕) ⊗_A B` — whereas part (1)'s
source is `Γ(Y', g^*R^if_*𝓕)`.  Identifying those is Descent, Proposition **03DX** (2) read on the
small étale site, which is not in this development; the quasi-coherence of `R^if_*𝓕` it would
need is **Stacks 0720**,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward'`.

*Quasi-compactness and quasi-separatedness of `f'`* are taken as arguments of the second corollary
rather than derived from those of `f` by **Stacks 03HF** and **Stacks 03KL**, which would need
`AlgebraicGeometry.Space.BaseChangeDiagram.isPullback` transported to the underlying presheaves.

*No Stacks attribute.*  **Stacks 0732** is registered on
`Stacks.Cohomology.Leray.exists_leraySpectralSequence` and **Stacks 08EX** on
`AlgebraicGeometry.Space.cohomologyChartIsoSectionsHigherDirectImage` and
`AlgebraicGeometry.Space.cohomologyAffineChartIsoSectionsHigherDirectImage`; what is below is a
composite of their content at an affine base, so it carries neither.  It is not **Stacks 073K**
either:  each corollary speaks about one side of the square only.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 08EX](https://stacks.math.columbia.edu/tag/08EX)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

-- Without the first, the module universe of `SheafOfModules.instAbelian` is left open and the
-- statements below do not elaborate
-- (`stuck at solving universe constraint u + 1 =?= max (u + 1) ?u`).
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] AlgebraicGeometry.RingedSite.globalSectionsCommRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Over an affine base, `H^i(X, 𝓕)` read over `A = Γ(Y, 𝒪_Y)` is `Γ(Y, R^if_*𝓕)`.**  For a
quasi-compact and quasi-separated `f : X ⟶ Y` with `Y` an affine algebraic space and `𝓕` a
quasi-coherent `𝒪_X`-module, the cohomology of `𝓕` on `X`, with its scalars restricted along the
comparison `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` of global section rings, is the module of global sections on
`Y` of the higher direct image. -/
def cohomologyRestrictScalarsIsoGlobalSectionsHigherDirectImage
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hY : IsAffineSpace B S hS Y.1)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (h072Z : AcyclicPushforwardOfInjective B S hS f) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (globalSectionsRestrictScalars B S hS f).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).obj F) ≅
      (globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj
        (((modulePushforward B S hS f).rightDerived i).obj F) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  ((derivedGlobalSectionsPushforwardIso B S hS f i).app F).symm ≪≫
    globalSectionsRightDerivedIsoOfIsAffineSpace B S hS f hY hfqc hfqs F h072Z i

namespace BaseChangeDiagram

variable {B S hS} (D : BaseChangeDiagram B S hS)

/-- **Part (2)'s left hand side before extension of scalars is `Γ(Y, R^if_*𝓕)`.**  For a cartesian
square of algebraic spaces with `Y` affine and `f` quasi-compact and quasi-separated,
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyOverBase` — the `A`-module `H^i(X, 𝓕)`
that part (2)'s source is the extension of scalars of — is the module of global sections on `Y` of
the higher direct image, which is the source of part (1)'s degreewise map before inverse image
along `g`. -/
def affineCohomologyOverBaseIsoGlobalSections (hY : IsAffineSpace B S hS D.Y.1)
    (hfqc : IsQuasiCompact B S hS D.f.hom) (hfqs : IsQuasiSeparated B S hS D.f.hom)
    (h072Z : AcyclicPushforwardOfInjective B S hS D.f) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    D.affineCohomologyOverBase i ≅
      (globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O)).obj
        (((modulePushforward B S hS D.f).rightDerived i).obj D.F) :=
  cohomologyRestrictScalarsIsoGlobalSectionsHigherDirectImage B S hS D.f hY hfqc hfqs D.F h072Z i

/-- **Part (2)'s right hand side is `Γ(Y', R^if'_*𝓕')`** — the global sections of the *target* of
part (1)'s degreewise map.  For a cartesian square of algebraic spaces with `Y'` affine and `f'`
quasi-compact and quasi-separated,
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyTarget`, which is `H^i(X', 𝓕')` read
over `B = Γ(Y', 𝒪_{Y'})`, is the module of global sections on `Y'` of `R^if'_*𝓕'`. -/
def affineCohomologyTargetIsoGlobalSections (hY' : IsAffineSpace B S hS D.Y'.1)
    (hf'qc : IsQuasiCompact B S hS D.f'.hom) (hf'qs : IsQuasiSeparated B S hS D.f'.hom)
    (h072Z : AcyclicPushforwardOfInjective B S hS D.f') (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    D.affineCohomologyTarget i ≅
      (globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS D.Y'.1 D.Y'.2).O)).obj
        (((modulePushforward B S hS D.f').rightDerived i).obj D.pulledBack) :=
  letI := D.isQuasicoherentOnSite_pulledBack
  cohomologyRestrictScalarsIsoGlobalSectionsHigherDirectImage B S hS D.f' hY' hf'qc hf'qs
    D.pulledBack h072Z i

end BaseChangeDiagram

end AlgebraicGeometry.Space

end
