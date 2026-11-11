module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AffineRestrictionPresentation
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystallineDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# Local quasi-coherence of `Ω_{X/S}`

Fix a global crystalline situation `(p, (S, I, γ), X)` and let `Ω_{X/S}` be the crystalline
differentials on the big crystalline category `CRIS(X/S)`.  Over an object `(U, T, δ)` the
restriction `(Ω_{X/S})_T` is the `𝒪_T`-module whose sections over an open `W` of `T` are the
sections of `Ω_{X/S}` over `(U ∩ W, W, δ|_W)`.  Local quasi-coherence of `Ω_{X/S}`, the first
clause of [Stacks, Tag 07KM], says that `(Ω_{X/S})_T` is a quasi-coherent `𝒪_T`-module for every
object of the site.  By [Stacks, Tag 07IZ] the restriction `(Ω_{X/S})_T` is the module
`Ω_{T/S,δ}` of divided power differentials of the ambient divided power scheme `T` over the base,
and by [Stacks, Tag 07IY] that module is quasi-coherent.  Here `Ω_{X/S}` is the presheaf of
`Crystalline.GlobalCrystallineSituation.crysDifferentials` and `(Ω_{X/S})_T` the sheaf associated
with its restriction; for the sheaf `Ω_{X/S}` on the small site, whose restriction to `T` is
`Ω_{T/S,δ}` by
`Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentialsSheafRestrictionIso`, see
`SmallSite/CrystallineDifferentialsSheaf.lean`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheaf` — the `𝒪_T`-module
  `(Ω_{X/S})_T`: the sheaf of `𝒪_T`-modules associated with the restriction of `Ω_{X/S}` to the
  ambient scheme of an object.
* `Crystalline.GlobalCrystallineSituation.crysDifferentialsRestrictionSheaf` — the same module
  with its scalars read in the restriction of `𝒪_{X/S}` to `T` rather than in `𝒪_T`.

## Main results

* `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheafIso` — the sheaf
  associated with the restriction of the presheaf `Ω_{X/S}` is `Ω_{T/S,δ}`.
* `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheaf_isQuasicoherent` and
  `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheaf_isQuasicoherentOnSite`
  — `(Ω_{X/S})_T` is a quasi-coherent `𝒪_T`-module, in Mathlib's sense and in the sense of
  [Stacks, Tag 03DL(6)].
* `Crystalline.GlobalCrystallineSituation.crysDifferentials_isLocallyQuasiCoherent` — `Ω_{X/S}`
  is locally quasi-coherent.

## Implementation notes

`Ω_{X/S}` is a presheaf of modules on `CRIS(X/S)`, not a sheaf
(`Crystalline.GlobalCrystallineSituation.crysDifferentials`), and its restriction to the ambient
scheme of an object is accordingly a presheaf of `𝒪_T`-modules
(`Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentials`).  A quasi-coherent
`𝒪_T`-module is by definition a sheaf, so the `𝒪_T`-module `(Ω_{X/S})_T` is the sheaf of
`𝒪_T`-modules *associated with* that presheaf.  The restriction of the associated sheaf of a
presheaf of modules to an open is the associated sheaf of the restriction, and `Ω_{T/S,δ}` is
likewise the sheafification of a presheaf of divided power differentials
(`Crystalline.dpDifferentialsSheaf`).

Quasi-coherence is stated in two forms, `SheafOfModules.IsQuasicoherent` and
`SheafOfModules.IsQuasicoherentOnSite`; on the Zariski site of a scheme the two agree, by
`SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite`.  The structure sheaf of `T` is
likewise spelled two ways: as the structure sheaf `𝒪_T` of the ambient scheme, and as the
restriction of the structure sheaf of `CRIS(X/S)` to the opens of `T`, whose sections over `W` are
the global sections of the open subscheme `W`.  The two are identified by
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`.

The predicate `Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent` takes a *sheaf* of
`𝒪_{X/S}`-modules on the crystalline site, and is not applied to `Ω_{X/S}` itself: by
`Crystalline.GlobalCrystallineSituation.comparisonIso` the restriction of `Ω_{X/S}` to `T` is the
presheaf `Crystalline.dpDifferentialsPresheaf` of divided power differentials, which is not a
sheaf on a general ambient scheme — already for the untwisted differentials of a proper curve its
global sections are the differentials of the global functions, a strictly smaller group than the
global sections of the sheaf.

## References

* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-- The `𝒪_T`-module `(Ω_{X/S})_T`: the sheaf of `𝒪_T`-modules associated with the restriction
of `Ω_{X/S}` to the ambient scheme `T` of an object `(U, T, δ)` of `CRIS(X/S)`. -/
def restrictedCrysDifferentialsSheaf (A : Thickening S) :
    SheafOfModules.{u} A.thickening.target.scheme.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 A.thickening.target.scheme.ringCatSheaf.obj)).obj
    (restrictedCrysDifferentials S A)

/-- The sheaf of `𝒪_T`-modules associated with the restriction of the presheaf `Ω_{X/S}` to the
ambient scheme of an object `(U, T, δ)` of `CRIS(X/S)` is the sheaf `Ω_{T/S,δ}` of divided power
differentials of `T` over `S`: the sheafification of
`Crystalline.GlobalCrystallineSituation.comparisonIso`.  This is a statement about the presheaf
`Ω_{X/S}`; [Stacks, Tag 07IZ], about the restriction of the sheaf `Ω_{X/S}` itself, is
`Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentialsSheafRestrictionIso`. -/
def restrictedCrysDifferentialsSheafIso (A : Thickening S) :
    (dpDifferentialsSheaf A.thickening.target S.S.scheme A.toBase.hom :
        SheafOfModules.{u} A.thickening.target.scheme.ringCatSheaf) ≅
      restrictedCrysDifferentialsSheaf S A :=
  (PresheafOfModules.sheafification (𝟙 A.thickening.target.scheme.ringCatSheaf.obj)).mapIso
    (comparisonIso A)

/-- The `𝒪_T`-module `(Ω_{X/S})_T` is quasi-coherent. -/
instance restrictedCrysDifferentialsSheaf_isQuasicoherent (A : Thickening S) :
    (restrictedCrysDifferentialsSheaf S A).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent A.thickening.target.scheme.ringCatSheaf).prop_of_iso
    (restrictedCrysDifferentialsSheafIso S A)
    (dpDifferentialsSheaf_isQuasicoherent A.thickening.target S.S.scheme A.toBase.hom)

/-- The `𝒪_T`-module `(Ω_{X/S})_T` is quasi-coherent in the sense of [Stacks, Tag 03DL(6)]:
every open of `T` has a cover on whose members the module is a cokernel of a map between free
modules. -/
theorem restrictedCrysDifferentialsSheaf_isQuasicoherentOnSite (A : Thickening S) :
    (restrictedCrysDifferentialsSheaf S A).IsQuasicoherentOnSite :=
  SheafOfModules.isQuasicoherentOnSite_of_isQuasicoherent (restrictedCrysDifferentialsSheaf S A)

/-- The module `(Ω_{X/S})_T` with its scalars read in the restriction of `𝒪_{X/S}`: the module
`Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsSheaf`, restricted along the
isomorphism `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`
from the restriction of the structure sheaf of `CRIS(X/S)` to the opens of `T` to `𝒪_T`. -/
def crysDifferentialsRestrictionSheaf (A : Thickening S) :
    SheafOfModules.{u} A.ringRestrictionSheaf :=
  (SheafOfModules.restrictScalars (Thickening.ringRestrictionSheafStructureIso A).hom).obj
    (restrictedCrysDifferentialsSheaf S A)

/-- `Ω_{X/S}` is locally quasi-coherent: for every object `(U, T, δ)` of `CRIS(X/S)` the
restriction `(Ω_{X/S})_T`, taken as the sheaf associated with the restriction of the presheaf
`Ω_{X/S}`, is a quasi-coherent module over the restriction of `𝒪_{X/S}` to the opens of `T`. -/
@[stacks 07KM "clause (1): Ω_{X/S} is locally quasi-coherent"]
theorem crysDifferentials_isLocallyQuasiCoherent (A : Thickening S) :
    (crysDifferentialsRestrictionSheaf S A).IsQuasicoherentOnSite :=
  Thickening.isQuasicoherentOnSite_ofAmbient A _
    (restrictedCrysDifferentialsSheaf_isQuasicoherentOnSite S A)

end Crystalline.GlobalCrystallineSituation

end
