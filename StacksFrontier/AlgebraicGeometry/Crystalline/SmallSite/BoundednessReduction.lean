module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DirectImageConcentration
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PerfectnessReduction

/-!
# The boundedness half of [Stacks, Tag 07MX] and [Stacks, Tag 07MY]

In the setting of [Stacks, Tag 07MX] and [Stacks, Tag 07MY], the cohomology `H^i(Cris(X/S), F)`
vanishes in all large degrees as soon as the Krull dimension of `X` is finite and
`R^j u_{X/S, *}F` vanishes in all large degrees.  By [Stacks, Tag 015M],
`RΓ(Cris(X/S), F) = RΓ(X_Zar, Ru_{X/S, *}F)`, and a bound `e` on the degrees of `Ru_{X/S, *}F`
together with a bound `d` on the Krull dimension of `X` bounds the degrees of `RΓ(Cris(X/S), F)`
by `e + d`.  Under the hypotheses of the two remarks, `S = Spec(A)` affine and `X → S₀` proper,
the space of `X` is quasi-compact and quasi-separated.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `ZariskiDirectImageBoundedAbove` — `R^j u_{X/S, *}F = 0` for `j` large.
* `TopologicalKrullDimensionFinite` — `dim X` is at most some natural number.
* `ZariskiDirectImageBoundedAbove07MX`, `ZariskiDirectImageBoundedAbove07MY` — the former under
  each tag's hypothesis block.

## Main results

* `isAffine_closedFiber_of_isAffine`, `compactSpace_of_isAffine_of_quasiCompact`,
  `quasiSeparatedSpace_of_isAffine_of_quasiSeparated` — if `S` is affine then so is `S₀`, and the
  space of `X` is quasi-compact (resp. quasi-separated) when `X → S₀` is.
* `isLE_derivedGlobalSections_of_isLE_derivedZariskiDirectImage` — if `dim X ≤ d` and
  `Ru_{X/S, *}F` lives in degrees `≤ e`, then `RΓ(Cris(X/S), F)` lives in degrees `≤ e + d`.
* `subsingleton_cohomology_of_isLE_derivedGlobalSections` — if `RΓ(Cris(X/S), F)` lives in
  degrees `≤ b`, then `H^i(Cris(X/S), F)` vanishes for `i > b`.
* `moduleCohomologyBoundedAbove_of_zariskiDirectImageBoundedAbove` — the cohomology of `F`
  vanishes in all large degrees if `dim X` is finite and `R^j u_{X/S, *}F` vanishes for large `j`.
* `boundedCohomology07MX_of_zariskiDirectImageBoundedAbove` and its 07MY twin —
  `BoundedCohomology07MX` (resp. `BoundedCohomology07MY`) from `TopologicalKrullDimensionFinite`
  and `ZariskiDirectImageBoundedAbove07MX` (resp. `ZariskiDirectImageBoundedAbove07MY`).
* `perfect07MX_of_perfectCohomology_of_zariskiDirectImageBoundedAbove` and its 07MY twin —
  `Perfect07MX` (resp. `Perfect07MY`) from the same two hypotheses together with
  `PerfectCohomology07MX` (resp. `PerfectCohomology07MY`).

## References

* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 066U](https://stacks.math.columbia.edu/tag/066U)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
* [Stacks Project, Tag 07MR](https://stacks.math.columbia.edu/tag/07MR)
* [Stacks Project, Tag 07MX](https://stacks.math.columbia.edu/tag/07MX)
* [Stacks Project, Tag 07MY](https://stacks.math.columbia.edu/tag/07MY)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### `X` is quasi-compact and quasi-separated under the hypotheses of 07MX and 07MY -/

/-- **The closed fibre of an affine divided power scheme is affine.** -/
theorem isAffine_closedFiber_of_isAffine (haff : IsAffine S.S.scheme) :
    IsAffine (DividedPowerScheme.closedFiber S.S) :=
  have := haff
  isAffine_of_isAffineHom (f := DividedPowerScheme.closedFiberι S.S)

/-- **The space of `X` is quasi-compact** when `S = Spec(A)` is affine and `X → S₀` is
quasi-compact. -/
theorem compactSpace_of_isAffine_of_quasiCompact (haff : IsAffine S.S.scheme)
    (hqc : QuasiCompact S.toClosedFiber) : CompactSpace ↥S.X :=
  have := isAffine_closedFiber_of_isAffine S haff
  have := hqc
  QuasiCompact.compactSpace_of_compactSpace S.toClosedFiber

/-- **The space of `X` is quasi-separated** when `S = Spec(A)` is affine and `X → S₀` is
quasi-separated. -/
theorem quasiSeparatedSpace_of_isAffine_of_quasiSeparated (haff : IsAffine S.S.scheme)
    (hqs : QuasiSeparated S.toClosedFiber) : QuasiSeparatedSpace ↥S.X :=
  have := isAffine_closedFiber_of_isAffine S haff
  have := hqs
  quasiSeparatedSpace_of_quasiSeparated S.toClosedFiber

/-! ### From the Zariski bound to `RΓ(Cris(X/S), F)` -/

section Bound

variable [CompactSpace ↥S.X] [QuasiSeparatedSpace ↥S.X]

/-- **`RΓ(Cris(X/S), F)` is concentrated in degrees `≤ e + d`** when `dim X ≤ d` and
`Ru_{X/S, *}F` is concentrated in degrees `≤ e`. -/
theorem isLE_derivedGlobalSections_of_isLE_derivedZariskiDirectImage
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (d e : ℕ)
    (hdim : topologicalKrullDim ↥S.X ≤ (d : WithBot ℕ∞))
    (hle : ((derivedZariskiDirectImage S).obj G).IsLE (e : ℤ)) :
    ((derivedGlobalSections S).obj G).IsLE ((e : ℤ) + (d : ℤ)) :=
  have : ((derivedZariskiDirectImage S ⋙ derivedZariskiGlobalSectionsFunctor S).obj G).IsLE
      ((e : ℤ) + (d : ℤ)) :=
    isLE_derivedZariskiGlobalSections_obj S ((derivedZariskiDirectImage S).obj G) d e hdim
      (isGE_derivedZariskiDirectImage_obj S G) hle
  DerivedCategory.Plus.TStructure.t.isLE_of_iso
    ((derivedGlobalSectionsIsoDerivedZariskiDirectImageObj S).app G).symm _

end Bound

/-- **If `RΓ(Cris(X/S), F)` is concentrated in degrees `≤ b`, then `H^i(Cris(X/S), F)` vanishes
for `i > b`.** -/
theorem subsingleton_cohomology_of_isLE_derivedGlobalSections
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (b : ℤ)
    (hLE : ((derivedGlobalSections S).obj G).IsLE b) (i : ℕ) (hi : b < (i : ℤ)) :
    Subsingleton (cohomology S G i) := by
  have hz : IsZero ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedGlobalSections S).obj G)) :=
    have := hLE
    DerivedCategory.Plus.isZero_homology_of_isLE ((derivedGlobalSections S).obj G) b (i : ℤ) hi
  refine (subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections S G i).2 ?_
  exact IsZero.of_iso hz ((Stacks.DerivedIndexing.rightDerivedIso (globalSections S) i).app G)

/-! ### Vanishing of the Zariski direct image and finiteness of `dim X` -/

/-- **`R^j u_{X/S, *}F = 0` for all large `j`**, for the abelian sheaf underlying a sheaf of
`𝒪_{X/S}`-modules. -/
def ZariskiDirectImageBoundedAbove (F : SheafOfModules.{u} (structureSheaf S)) : Prop :=
  ∃ e : ℕ, ∀ j : ℤ, (e : ℤ) < j →
    IsZero ((higherZariskiDirectImage S j).obj (abelianSheaf F))

/-- **The space of `X` has finite Krull dimension.** -/
def TopologicalKrullDimensionFinite : Prop :=
  ∃ d : ℕ, topologicalKrullDim ↥S.X ≤ (d : WithBot ℕ∞)

/-- **`H^i(Cris(X/S), F)` vanishes in all large degrees** as soon as `dim X` is finite and
`R^j u_{X/S, *}F` vanishes in all large degrees. -/
theorem moduleCohomologyBoundedAbove_of_zariskiDirectImageBoundedAbove
    [CompactSpace ↥S.X] [QuasiSeparatedSpace ↥S.X]
    (F : SheafOfModules.{u} (structureSheaf S))
    (hdim : TopologicalKrullDimensionFinite S)
    (hbd : ZariskiDirectImageBoundedAbove S F) :
    ModuleCohomologyBoundedAbove S F := by
  obtain ⟨d, hd⟩ := hdim
  obtain ⟨e, he⟩ := hbd
  refine (moduleCohomologyBoundedAbove_iff_abelian S F).2 ⟨e + d, fun i hi => ?_⟩
  exact subsingleton_cohomology_of_isLE_derivedGlobalSections S _ ((e : ℤ) + (d : ℤ))
    (isLE_derivedGlobalSections_of_isLE_derivedZariskiDirectImage S _ d e hd
      (isLE_derivedZariskiDirectImage_obj S _ (e : ℤ) he)) i
    (by omega)

/-- **`ZariskiDirectImageBoundedAbove` under the hypothesis block of [Stacks, Tag 07MX]**,
condition for condition and in the same order as `Perfect07MX` and `BoundedCohomology07MX`. -/
def ZariskiDirectImageBoundedAbove07MX : Prop :=
  IsAffine S.S.scheme → IsNilpotent (S.p : Γ(S.S.scheme, ⊤)) →
    IsProper S.toClosedFiber → Smooth S.toClosedFiber →
      ∀ F : SheafOfModules.{u} (structureSheaf S),
        IsFiniteLocallyFreeQuasicoherentCrystal F → ZariskiDirectImageBoundedAbove S F

/-- **`ZariskiDirectImageBoundedAbove` under the hypothesis block of [Stacks, Tag 07MY]**, with
07MY's block in place of 07MX's and nothing else changed. -/
def ZariskiDirectImageBoundedAbove07MY : Prop :=
  IsAffine S.S.scheme →
    IsAdicComplete (Ideal.span {(S.p : Γ(S.S.scheme, ⊤))}) ↥Γ(S.S.scheme, ⊤) →
      IsNilpotent (S.p : Γ(DividedPowerScheme.closedFiber S.S, ⊤)) →
        IsProper S.toClosedFiber → Smooth S.toClosedFiber →
          ∀ F : SheafOfModules.{u} (structureSheaf S),
            IsFiniteLocallyFreeQuasicoherentCrystal F → ZariskiDirectImageBoundedAbove S F

/-! ### The boundedness half of each remark -/

/-- The boundedness conclusion for `F` when `S` is affine and `X → S₀` is proper. -/
private theorem moduleCohomologyBoundedAbove_of_isAffine_of_isProper (haff : IsAffine S.S.scheme)
    (hproper : IsProper S.toClosedFiber) (F : SheafOfModules.{u} (structureSheaf S))
    (hdim : TopologicalKrullDimensionFinite S) (hbd : ZariskiDirectImageBoundedAbove S F) :
    ModuleCohomologyBoundedAbove S F :=
  have := hproper
  have : CompactSpace ↥S.X := compactSpace_of_isAffine_of_quasiCompact S haff inferInstance
  have : QuasiSeparatedSpace ↥S.X :=
    quasiSeparatedSpace_of_isAffine_of_quasiSeparated S haff inferInstance
  moduleCohomologyBoundedAbove_of_zariskiDirectImageBoundedAbove S F hdim hbd

/-- **The boundedness half of [Stacks, Tag 07MX] follows from the degree bound on `Ru_{X/S, *}F`
and the finiteness of `dim X`.** -/
theorem boundedCohomology07MX_of_zariskiDirectImageBoundedAbove
    (hdim : TopologicalKrullDimensionFinite S)
    (hbd : ZariskiDirectImageBoundedAbove07MX S) : BoundedCohomology07MX S := by
  intro haff hnil hproper hsmooth F hF
  exact moduleCohomologyBoundedAbove_of_isAffine_of_isProper S haff hproper F hdim
    (hbd haff hnil hproper hsmooth F hF)

/-- **The boundedness half of [Stacks, Tag 07MY] follows from the degree bound on `Ru_{X/S, *}F`
and the finiteness of `dim X`.** -/
theorem boundedCohomology07MY_of_zariskiDirectImageBoundedAbove
    (hdim : TopologicalKrullDimensionFinite S)
    (hbd : ZariskiDirectImageBoundedAbove07MY S) : BoundedCohomology07MY S := by
  intro haff hcomplete hnil hproper hsmooth F hF
  exact moduleCohomologyBoundedAbove_of_isAffine_of_isProper S haff hproper F hdim
    (hbd haff hcomplete hnil hproper hsmooth F hF)

/-! ### Each remark from its finiteness half -/

/-- **[Stacks, Tag 07MX] from the finiteness half**, together with the degree bound on
`Ru_{X/S, *}F` and the finiteness of `dim X`. -/
theorem perfect07MX_of_perfectCohomology_of_zariskiDirectImageBoundedAbove
    (hdim : TopologicalKrullDimensionFinite S)
    (hbd : ZariskiDirectImageBoundedAbove07MX S)
    (hp : PerfectCohomology07MX S) : Perfect07MX S :=
  perfect07MX_of_boundedCohomology_of_perfectCohomology S
    (boundedCohomology07MX_of_zariskiDirectImageBoundedAbove S hdim hbd) hp

/-- **[Stacks, Tag 07MY] from the finiteness half**, together with the degree bound on
`Ru_{X/S, *}F` and the finiteness of `dim X`. -/
theorem perfect07MY_of_perfectCohomology_of_zariskiDirectImageBoundedAbove
    (hdim : TopologicalKrullDimensionFinite S)
    (hbd : ZariskiDirectImageBoundedAbove07MY S)
    (hp : PerfectCohomology07MY S) : Perfect07MY S :=
  perfect07MY_of_boundedCohomology_of_perfectCohomology S
    (boundedCohomology07MY_of_zariskiDirectImageBoundedAbove S hdim hbd) hp

end Crystalline.GlobalCrystallineSituation.SmallSite

end
