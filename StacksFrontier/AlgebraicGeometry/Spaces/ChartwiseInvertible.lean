module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardInvertibleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelativeDualizingSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRankOneFreeLocusDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# A quasi-coherent module on an algebraic space that is invertible on an étale covering by schemes

Let `X` be an algebraic space and `F` a quasi-coherent `𝒪_X`-module on its small étale site. If
`{cᵢ : Vᵢ → X}` is an étale covering of `X` by schemes and every pullback
`cᵢ^*F` (read as an `𝒪_{Vᵢ}`-module on the scheme `Vᵢ`) is an invertible `𝒪_{Vᵢ}`-module, then
`F` is invertible. This is the étale-local nature of invertibility (Stacks 0B8Q read through
Stacks 03DX), in the shape the relative dualizing sheaf of a family of curves needs: its
invertibility is proved on the scheme charts of the total space (Stacks 0E6R), and has to be
read back on the algebraic space.

## Main results

* `AlgebraicGeometry.Space.isInvertibleModule_of_isEtaleCovering_baseChangeModule`: the
  criterion.
* `AlgebraicGeometry.Space.isInvertible_of_isEtaleCovering_baseChangeModule`: the same, with
  the conclusion in the spelling of the input `hωinv` of the argument of Stacks 0E74.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_affineRelativeDualizingSheaf`: the relative
  dualizing sheaf `H^{-1}(a(𝒪_Y))` is quasi-coherent, the input `hF` of the criterion for it.

## Implementation notes

**Unregistered helper** (for Stacks 0E74 through 0E6R). An étale covering is an fpqc covering
(Stacks 0DFQ, `AlgebraicGeometry.Space.isFpqcCovering_of_isEtaleCovering`), and invertibility of
a quasi-coherent module descends along fpqc coverings
(`AlgebraicGeometry.Space.isInvertibleModule_of_isFpqcCovering_of_isQuasicoherentOnSite`). On
the algebraic space represented by `Vᵢ` the pullback `cᵢ^*F` is quasi-coherent (Stacks 03GA), and
it is invertible because its reading on the scheme `Vᵢ`, which is
`AlgebraicGeometry.Space.baseChangeModule F Vᵢ cᵢ`, is
(`AlgebraicGeometry.Space.isInvertibleModule_of_idChartRestriction_iso`). Only a covering family
is needed, not every étale chart of `X`.

## References

* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Invertibility of a quasi-coherent module is read on an étale covering by schemes.** Let
`F` be a quasi-coherent `𝒪_X`-module and `cᵢ : Vᵢ → X` an étale covering of `X` by schemes of
the site. If every pullback `AlgebraicGeometry.Space.baseChangeModule F Vᵢ cᵢ` is an invertible
`𝒪_{Vᵢ}`-module, then `F` is invertible. -/
theorem isInvertibleModule_of_isEtaleCovering_baseChangeModule (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) {I : Type v}
    (V : I → BigFppfOver B S hS) (c : ∀ i, yoneda.obj (V i) ⟶ X.1)
    (hc : IsEtaleCovering B S hS (fun i ↦ yoneda.obj (V i)) c)
    (h : ∀ i, Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj (V i))
      (baseChangeModule B S hS F (V i) (c i))) :
    IsInvertibleModule X F := by
  let Xi : I → AlgebraicSpaces B S hS := fun i ↦
    ⟨yoneda.obj (V i), isAlgebraicSpace_yoneda B S hS (V i)⟩
  let f : ∀ i, Xi i ⟶ X := fun i ↦ ObjectProperty.homMk (c i)
  refine isInvertibleModule_of_isFpqcCovering_of_isQuasicoherentOnSite f
    (isFpqcCovering_of_isEtaleCovering B S hS _ _ hc) F hF fun i ↦ ?_
  have := h i
  exact isInvertibleModule_of_idChartRestriction_iso B S hS (V i) _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (f i) F hF)
    (baseChangeModule B S hS F (V i) (c i))
    (restrictToChartSchemeIdEtaleChartIso B S hS (V i) _).symm

/-- `AlgebraicGeometry.Space.isInvertibleModule_of_isEtaleCovering_baseChangeModule`, with the
conclusion spelled as the invertibility hypothesis `hωinv` of
`CurveFamily.hasNoRationalTailNoRationalBridge_iff_exists_isRelativelyAmple_of`. -/
theorem isInvertible_of_isEtaleCovering_baseChangeModule (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) {I : Type v}
    (V : I → BigFppfOver B S hS) (c : ∀ i, yoneda.obj (V i) ⟶ X.1)
    (hc : IsEtaleCovering B S hS (fun i ↦ yoneda.obj (V i)) c)
    (h : ∀ i, Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj (V i))
      (baseChangeModule B S hS F (V i) (c i))) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
      F :=
  isInvertibleModule_of_isEtaleCovering_baseChangeModule B S hS X F hF V c hc h

/-- **The relative dualizing sheaf over an affine base is quasi-coherent.** The cohomology
sheaves of an object of `D_QCoh(𝒪_X)` (Stacks 071X) are quasi-coherent by definition; here in
degree `-1`, at `AlgebraicGeometry.Space.affineRelativeDualizingComplex`. -/
theorem isQuasicoherentOnSite_affineRelativeDualizingSheaf {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfp : IsFinitePresentation B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1) :
    (affineRelativeDualizingSheaf hZ f hfp hY).IsQuasicoherentOnSite :=
  (affineRelativeDualizingComplex hZ f hfp hY).property (-1)

end AlgebraicGeometry.Space

end
