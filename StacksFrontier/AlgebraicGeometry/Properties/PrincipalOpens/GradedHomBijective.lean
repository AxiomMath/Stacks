module

public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedHomInjective
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.Basic

/-!
# Bijectivity of the localized graded Hom map on a nonvanishing open

Let `X` be a quasi-compact and quasi-separated scheme, let `L` be an invertible `𝒪_X`-module
with global section `s` and nonvanishing open `X_s`, let `ℱ` be an `𝒪_X`-module of finite
presentation and let `𝒢` be a quasi-coherent `𝒪_X`-module. This file proves that the comparison
map of [Stacks, Tag 0B5M](https://stacks.math.columbia.edu/tag/0B5M)
`(⨁_n Hom(ℱ, 𝒢 ⊗ L^{⊗ n}))_{(s)} ⟶ Hom_{𝒪_{X_s}}(ℱ|_{X_s}, 𝒢|_{X_s})`
is bijective -- **part (2) of [Stacks, Tag 01XQ](https://stacks.math.columbia.edu/tag/01XQ)**.

## Main results

* `Stacks.SheafOfModules.sheafHomSpace_isQuasicoherent`: for `ℱ` of finite presentation and `𝒢`
  quasi-coherent, the internal Hom `ℋom(ℱ, 𝒢)` carrying the graded Hom module of Tag 0B5M is
  quasi-coherent.
* `Stacks.SheafOfModules.homLocalizationMap_surjective_of_twistedExtension`: surjectivity of the
  Tag 0B5M comparison map, granted the twisted extension property for `ℋom(ℱ, 𝒢)`.
* `Stacks.SheafOfModules.homLocalizationMap_bijective`: **[Stacks, Tag 01XQ] part (2)**.

## Implementation notes

The proofs are written in term mode, through `Exists.elim` rather than `obtain`, for the reason
recorded in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/NonvanishingGradedHom.lean`: building a
tactic motive over `Stacks.SheafOfModules.homAtNonvanishingOpen`, whose carrier is a localization of
the graded Hom
module at a `Module.compHom` instance, costs more than the heartbeat budget, while passing the
same terms positionally keeps every type known before it is checked. For the same reason the two
implications from finite presentation are taken from the Mathlib instances by name
(`SheafOfModules.instIsQuasicoherentOfIsFinitePresentation`,
`SheafOfModules.instIsFiniteTypeOfIsFinitePresentation`) instead of by instance search, which
does not terminate inside its budget at these types.

## References

* [Stacks Project, Tag 01XQ](https://stacks.math.columbia.edu/tag/01XQ)
* [Stacks Project, Tag 0B5M](https://stacks.math.columbia.edu/tag/0B5M)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
* [Stacks Project, Tag 0583](https://stacks.math.columbia.edu/tag/0583)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

open CategoryTheory _root_.AlgebraicGeometry Opposite Limits

universe u

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' TensorSheafification.structureSheaf

section Tag01XQBijectivity

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]
  (F G : X.Modules)

/-- **The internal Hom carrying the graded Hom module of Tag 0B5M is quasi-coherent** when the
source is of finite presentation and the target is quasi-coherent. This is
`AlgebraicGeometry.sheafHom_isQuasicoherent` ([Stacks, Tag 01LA]) at the spelling
`Stacks.SheafOfModules.sheafHomSpace` of the internal Hom. -/
theorem sheafHomSpace_isQuasicoherent [F.IsFinitePresentation] [G.IsQuasicoherent] :
    _root_.SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      (sheafHomSpace X.toRingedSpace F G) :=
  sheafHom_isQuasicoherent (X := X) F G

/-- **Surjectivity of the Tag 0B5M comparison map, granted the twisted extension property for
the internal Hom sheaf.** If every section of `ℋom(ℱ, 𝒢)` over `X_s` becomes, after tensoring
with some power of `s`, the restriction of a global twisted section, then every morphism
`ℱ|_{X_s} ⟶ 𝒢|_{X_s}` is the value of the Tag 0B5M map on a degree-zero fraction. -/
theorem homLocalizationMap_surjective_of_twistedExtension (s : L.sections)
    (hext : HasTwistedExtension X L (sheafHomSpace X.toRingedSpace F G) s) :
    Function.Surjective (homLocalizationMap X L F G s) :=
  fun g => (hext g.val).elim fun N hN => hN.elim fun b hb =>
    ⟨homFractionClass X L F G s N ((homToTwistedSection X L F G (N : ℤ)).symm b),
      homLocalizationMap_fraction X L F G s N
        ((homToTwistedSection X L F G (N : ℤ)).symm b) g.val
        ((congrArg (fun y => ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
                (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj
              ((sheafHomSpace X.toRingedSpace F G))).obj
              ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
              (N : ℤ))))).val.map (terminal.from (nonvanishingOpen L s)).op y)
          ((homToTwistedSection X L F G (N : ℤ)).apply_symm_apply b)).trans hb)⟩

/-- **[Stacks, Tag 01XQ] part (2).** Let `X` be a quasi-compact and quasi-separated scheme, let
`L` be an invertible `𝒪_X`-module, let `s` be a global section of `L`, let `ℱ` be an
`𝒪_X`-module of finite presentation and let `𝒢` be a quasi-coherent `𝒪_X`-module. The comparison
map of Tag 0B5M
`(⨁_n Hom(ℱ, 𝒢 ⊗ L^{⊗ n}))_{(s)} ⟶ Hom_{𝒪_{X_s}}(ℱ|_{X_s}, 𝒢|_{X_s})` is bijective.

The quasi-coherence of `ℱ` that the source assumes throughout the lemma is not carried
separately: finite presentation implies it, and implies the finite type that part (1) of the tag
asks for. -/
@[stacks 01XQ "bijective"]
theorem homLocalizationMap_bijective [CompactSpace X] [QuasiSeparatedSpace X]
    [F.IsFinitePresentation] [G.IsQuasicoherent] (s : L.sections) :
    Function.Bijective (homLocalizationMap X L F G s) :=
  have := _root_.SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  have := _root_.SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have := sheafHomSpace_isQuasicoherent X F G
  ⟨homLocalizationMap_injective X L F G s,
    homLocalizationMap_surjective_of_twistedExtension X L F G s
      (hasTwistedExtension X L (sheafHomSpace X.toRingedSpace F G) s)⟩

end Tag01XQBijectivity

end Stacks.SheafOfModules

end
