module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationColimit
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections on a nonvanishing open as a sequential colimit of twisted sections

Let `X` be a quasi-compact and quasi-separated scheme, let `L` be an invertible `𝒪_X`-module with
global section `s` and nonvanishing open `X_s`, and let `ℱ` be a quasi-coherent `𝒪_X`-module.
[Stacks, Tag 01PW] (2) says that the comparison map of [Stacks, Tag 0B5L]

`(⨁_n Γ(X, ℱ ⊗ L^{⊗ n}))_{(s)} ⟶ Γ(X_s, ℱ|_{X_s})`

is bijective. The source of its domain is a degree-zero homogeneous localization, and
`Stacks.SheafOfModules.isColimitDegreeZeroCocone` identifies such a localization with the colimit
of the homogeneous pieces under multiplication by the homogeneous element. Composing the two
reads Tag 01PW (2) as

`Γ(X_s, ℱ|_{X_s}) = colim_n Γ(X, ℱ ⊗ L^{⊗ n})`,

the colimit of the `ℕ`-indexed system whose transition maps are multiplication by `s`. That is the
form in which [Stacks, Tag 0EBN] uses the tag.

## Main definitions

* `Stacks.SheafOfModules.twistedSectionSequence`: **the `ℕ`-indexed system of twisted global
  sections** `ℕ ⥤ AddCommGrpCat`, with multiplication by `s` as its transition maps.
* `Stacks.SheafOfModules.twistedSectionCocone`: the cocone with vertex `Γ(X_s, ℱ|_{X_s})` whose
  `n`-th leg is the Tag 0B5L map applied to the fraction `m / sⁿ`.

## Main results

* `Stacks.SheafOfModules.isColimitTwistedSectionCocone`: **[Stacks, Tag 01PW] (2) as a sequential
  colimit** — the sections of `ℱ` over `X_s` are the colimit of the twisted global sections under
  multiplication by `s`.

## Implementation notes

The `n`-th term of the system is the degree-`n * 1` homogeneous piece
`Stacks.SheafOfModules.sectionModuleGrading` of the graded section module, which is the image of
`Γ(X, ℱ ⊗ L^{⊗ n})` under `DirectSum.of`; the exponent `n * 1` rather than `n` is what the
arbitrary-degree indexing of `Stacks.SheafOfModules.homogeneousSequence` produces at the degree
`1` of `s`, and `Nat.mul_one` crosses the two. That the term *is* `Γ(X, ℱ ⊗ L^{⊗ n})`, and that
the transition maps are multiplication by `s`, is not proved here: it is
`Stacks.SheafOfModules.twistedSectionSequenceObjIso` and
`Stacks.SheafOfModules.twistedSectionSequenceObjIso_naturality` of
`StacksFrontier/AlgebraicGeometry/Properties/PrincipalOpens/TwistedSectionTerms.lean`, which imports
this file.

Bijectivity is turned into an isomorphism of `AddCommGrpCat` by
`CategoryTheory.ConcreteCategory.isIso_iff_bijective`, and the colimit is transported along it by
`CategoryTheory.Limits.IsColimit.extendIso`, so the cocone here is literally the cocone of
`Stacks.SheafOfModules.degreeZeroCocone` extended along the Tag 0B5L map. Nothing is reproved.

The instance preamble is the one of
`StacksFrontier/AlgebraicGeometry/Properties/PrincipalOpens/GradedSectionInjective.lean`: the graded
structures on the section ring and the section module, and the `Module.compHom` action of the
degree-zero localized ring on the localized section module, are not found by instance search
through the two spellings of the structure sheaf, and the last of them is what gives the
degree-zero localization an additive structure at all.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite DirectSum Limits

universe u

section TwistedSectionColimit

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

attribute [local implicit_reducible] ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv
  Stacks.SchemeModulesSpelling.sectionRingGradedRing
  Stacks.SchemeModulesSpelling.sectionRingGradingGradedRing
  Stacks.SchemeModulesSpelling.sectionModuleModule

variable (H : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The decomposition of the section module into its homogeneous pieces, which instance search
does not find through the two spellings of the structure sheaf. -/
local instance sectionModuleDecompositionColim : DirectSum.Decomposition
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H) :=
  sectionModuleDecomposition (sectionSiteRing X) (sectionSiteSheaf X) L H

/-- The graded compatibility of the section-ring action, out of reach of instance search for the
same reason. -/
local instance sectionModuleGradedSMulColim : SetLike.GradedSMul
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H) :=
  sectionModuleGradedSMul (sectionSiteRing X) (sectionSiteSheaf X) L H

/-- The degree-zero homogeneous localization of the section ring acts on the localization of the
graded section module through its embedding into the full localization. Mathlib keeps this
`Module.compHom` action out of instance search, and the degree-zero localization is a submodule
over it, so it has to be in scope for that submodule's additive structure to be found at all; it
is the very instance under which Tag 0B5L was stated. -/
local instance sectionAwayModuleColim (s : L.sections) :
    Module (HomogeneousLocalization.Away
        (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s))
      (LocalizedModule.Away (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s)
        (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H)) :=
  Module.compHom (R := Localization.Away (homogeneousSection X L s))
    (LocalizedModule.Away (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
      (homogeneousSection X L s)
      (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L H))
    (algebraMap (HomogeneousLocalization.Away
      (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
      (homogeneousSection X L s))
      (Localization.Away (homogeneousSection X L s)))

/-- **The `ℕ`-indexed system of twisted global sections**, whose `n`-th term is the degree-`n`
piece `Γ(X, H ⊗ L^{⊗ n})` of the graded section module and whose transition maps are
multiplication by the global section `s`. -/
public def twistedSectionSequence (s : L.sections) : ℕ ⥤ AddCommGrpCat.{u} :=
  homogeneousSequence (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H)
    (homogeneousSection_mem X L s)

/-- **The cocone of twisted global sections over the sections on the nonvanishing open**: the
`n`-th leg sends a twisted global section `m` of degree `n` to the value of the [Stacks, Tag 0B5L]
comparison map on the fraction `m / sⁿ`, which is the section of `H` over `X_s` whose product with
`sⁿ` is the restriction of `m`. -/
public def twistedSectionCocone (s : L.sections) : Cocone (twistedSectionSequence X L H s) :=
  (degreeZeroCocone (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
      (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H)
      (homogeneousSection_mem X L s)).extend
    (AddCommGrpCat.ofHom (sectionLocalizationMap X L H s))

/-- The vertex of `twistedSectionCocone` is the group of sections of `H` over the nonvanishing
open of `s`. -/
@[simp]
public theorem twistedSectionCocone_pt (s : L.sections) :
    (twistedSectionCocone X L H s).pt =
      AddCommGrpCat.of (H.val.obj (op (nonvanishingOpen L s))) := rfl

/-- **The [Stacks, Tag 0B5L] comparison map as an isomorphism of abelian groups**, granted its
bijectivity. Its source is written as the vertex of
`Stacks.SheafOfModules.degreeZeroCocone`, which is the degree-zero localization. -/
public def sectionLocalizationGrpIso (s : L.sections)
    (hbij : Function.Bijective (sectionLocalizationMap X L H s)) :
    (degreeZeroCocone (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
        (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H)
        (homogeneousSection_mem X L s)).pt ≅
      AddCommGrpCat.of (H.val.obj (op (nonvanishingOpen L s))) where
  hom := AddCommGrpCat.ofHom (sectionLocalizationMap X L H s)
  inv := AddCommGrpCat.ofHom
    (AddEquiv.ofBijective (sectionLocalizationMap X L H s) hbij).symm.toAddMonoidHom
  hom_inv_id := by
    ext x
    exact (AddEquiv.ofBijective (sectionLocalizationMap X L H s) hbij).symm_apply_apply x
  inv_hom_id := by
    ext x
    exact (AddEquiv.ofBijective (sectionLocalizationMap X L H s) hbij).apply_symm_apply x

/-- **The twisted global sections are the colimit of the sections on the nonvanishing open as soon
as the [Stacks, Tag 0B5L] comparison map is bijective**, which is what [Stacks, Tag 01PW] (2)
supplies. -/
public def isColimitTwistedSectionCoconeOfBijective (s : L.sections)
    (hbij : Function.Bijective (sectionLocalizationMap X L H s)) :
    IsColimit (twistedSectionCocone X L H s) :=
  IsColimit.ofIsoColimit
    (isColimitDegreeZeroCocone (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
      (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L H)
      (homogeneousSection_mem X L s))
    (Cocone.ext (sectionLocalizationGrpIso X L H s hbij) fun _ => rfl)

/-- **[Stacks, Tag 01PW] (2) as a sequential colimit.** Let `X` be a quasi-compact and
quasi-separated scheme, let `L` be an invertible `𝒪_X`-module, let `s` be a global section of `L`
and let `ℱ` be a quasi-coherent `𝒪_X`-module. The sections of `ℱ` over the nonvanishing open `X_s`
are the colimit of the twisted global sections `Γ(X, ℱ ⊗ L^{⊗ n})` under multiplication by `s`.

The map out of the colimit is the one of [Stacks, Tag 0B5L], which Tag 01PW (2) says is bijective;
the identification of the degree-zero localization it is defined on with the colimit of the
homogeneous pieces is `Stacks.SheafOfModules.isColimitDegreeZeroCocone`. -/
@[ega "I 9.3.2" "special case", ega "III 1.2.2" "more general"]
public def isColimitTwistedSectionCocone [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] (s : L.sections) :
    IsColimit (twistedSectionCocone X L F s) :=
  isColimitTwistedSectionCoconeOfBijective X L F s (sectionLocalizationMap_bijective X L F s)

end TwistedSectionColimit

end Stacks.SheafOfModules

end
