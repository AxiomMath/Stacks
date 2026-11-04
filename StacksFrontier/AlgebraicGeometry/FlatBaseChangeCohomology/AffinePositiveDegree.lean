module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentRefine
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.CechComparison
public import StacksFrontier.AlgebraicGeometry.TwistCohomologyFiniteness.Basic

/-!
# Flat base change for cohomology over an affine base, in every degree

Let

```
Y --p--> X
|        |
kY       iX
v        v
T --q--> S
```

be a cartesian square of schemes with `S` and `T` affine, let `q` be flat, let `iX` be separated
and quasi-compact, and let `F` be a quasi-coherent `𝒪_X`-module. Then for every `n`

`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Hⁿ(X, F) ≅ Hⁿ(Y, p^* F)`

as `Γ(T, ⊤)`-modules. This is the separated case of part (2) of [Stacks, Tag 02KH], for an
isomorphism assembled from the Čech comparison rather than the canonical base change map of
[Stacks, Tag 02N7]; the latter, for a quasi-compact quasi-separated `iX`, is
`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.cohomologyBaseChangeIso`.

## Main definitions

* `AlgebraicGeometry.cohomologyBaseChangeIsoOfCover`: the comparison isomorphism, for an
  explicitly given finite cover of `X` with affine finite intersections.

## Main results

* `AlgebraicGeometry.exists_finite_affineOpen_cover_inter_of_isAffine`: a scheme separated and
  quasi-compact over an affine base has a finite cover by affine opens all of whose nonempty
  finite intersections are affine.
* `AlgebraicGeometry.nonempty_cohomologyBaseChangeIso`: the comparison isomorphism exists for
  every separated quasi-compact `iX`, with no cover supplied.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.CechSheaf (cechComplex)
open Stacks.AlgebraicGeometry.SectionsBaseChange (baseRestrictScalars baseExtendScalars
  preservesHomology_baseChange cechBaseChangeIsoOfPreimage top_eq_iSup_preimage le_preimage_top)

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### A cover with affine finite intersections -/

/-- **A scheme quasi-compact and separated over an affine base has a finite cover by affine opens
all of whose nonempty finite intersections are affine.** -/
theorem exists_finite_affineOpen_cover_inter_of_isAffine {S X : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [IsSeparated f] [QuasiCompact f] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens), (⊤ : X.Opens) = ⨆ i, U i ∧
      ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ j, U (s j)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨ι, hι, V, hVaff, hVcov⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_finite_affineOpen_cover X
  have : IsSeparated (terminal.from X) := by
    rw [show terminal.from X = f ≫ terminal.from S from terminal.hom_ext _ _]
    infer_instance
  exact ⟨ι, hι, V, le_antisymm (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hVcov x)) le_top,
    fun r s => IsAffineOpen.iInf fun j => hVaff (s j)⟩

/-! ### Homology commutes with the two change-of-rings functors -/

/-- **Base change of a complex over an affine base commutes with homology when the base ring map
is flat.** -/
def baseChangeHomologyIso {S T X : Scheme.{u}} (iX : X ⟶ S) (q : T ⟶ S)
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
    (K : CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℕ) (n : ℕ) :
    (((baseRestrictScalars iX ⋙ baseExtendScalars q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology n ≅
      (baseRestrictScalars iX ⋙ baseExtendScalars q).obj (K.homology n) :=
  have := preservesHomology_baseChange iX q hq
  (K.sc n).mapHomologyIso (baseRestrictScalars iX ⋙ baseExtendScalars q)

/-- **Restriction of scalars commutes with homology**, being exact. -/
def baseRestrictScalarsHomologyIso {T Y : Scheme.{u}} (kY : Y ⟶ T)
    (K : CochainComplex (ModuleCat.{u} Γ(Y, ⊤)) ℕ) (n : ℕ) :
    (((baseRestrictScalars kY).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅
      (baseRestrictScalars kY).obj (K.homology n) :=
  have := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars
    (kY.appLE ⊤ ⊤ (le_preimage_top kY ⊤)).hom
  (K.sc n).mapHomologyIso (baseRestrictScalars kY)

/-! ### The comparison over an affine base -/

section

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {kY : Y ⟶ T}

/-- **Base change of the cohomology of a quasi-coherent module over an affine base, from a cover
with affine finite intersections.** For a cartesian square with `S` and `T` affine and `q` flat,
and a finite cover `U` of `X` whose nonempty finite intersections are affine,
`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Hⁿ(X, F) ≅ Hⁿ(Y, p^* F)` in every degree. -/
def cohomologyBaseChangeIsoOfCover [IsAffine S] [IsAffine T] [Flat q]
    (H : IsPullback p kY iX q) (F : X.Modules) [F.IsQuasicoherent] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ j, U (s j))) (n : ℕ) :
    (baseRestrictScalars iX ⋙ baseExtendScalars q).obj
        (((SheafOfModules.evaluation.{u} X.ringCatSheaf
          (op (⊤ : X.Opens))).rightDerived n).obj F) ≅
      (baseRestrictScalars kY).obj
        (((SheafOfModules.evaluation.{u} Y.ringCatSheaf
          (op (⊤ : Y.Opens))).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)) :=
  have hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom :=
    Flat.flat_appLE q (isAffineOpen_top S) (isAffineOpen_top T) (le_preimage_top q ⊤)
  have hpaff : IsAffineHom p := MorphismProperty.of_isPullback H.flip inferInstance
  have hU' : (⊤ : Y.Opens) = ⨆ i, p ⁻¹ᵁ U i := top_eq_iSup_preimage U hU p
  have hU'aff : ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ j, p ⁻¹ᵁ U (s j)) := by
    intro r s
    rw [← Stacks.ProjectiveCohomology.preimage_iInf p fun j => U (s j)]
    exact (hUaff r s).preimage p
  (baseRestrictScalars iX ⋙ baseExtendScalars q).mapIso
      (rightDerivedEvaluationCechHomologyIso X ⊤ U hU hUaff F n) ≪≫
    (baseChangeHomologyIso iX q hq (cechComplex.{u, u, u, u} (⊤ : X.Opens) U hU F) n).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
      (cechBaseChangeIsoOfPreimage H F U hU (fun {m} x => hUaff m x)
        (fun i => p ⁻¹ᵁ U i) (fun _ => rfl) hU') ≪≫
    baseRestrictScalarsHomologyIso kY
      (cechComplex.{u, u, u, u} (⊤ : Y.Opens) (fun i => p ⁻¹ᵁ U i) hU'
        ((Scheme.Modules.pullback p).obj F)) n ≪≫
    (baseRestrictScalars kY).mapIso
      (rightDerivedEvaluationCechHomologyIso Y ⊤ (fun i => p ⁻¹ᵁ U i) hU' hU'aff
        ((Scheme.Modules.pullback p).obj F) n).symm

/-- **Base change of the cohomology of a quasi-coherent module over an affine base.** For a
cartesian square with `S` and `T` affine, `q` flat and `iX` separated and quasi-compact,
`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Hⁿ(X, F) ≅ Hⁿ(Y, p^* F)` in every degree.

The isomorphism is not identified with the canonical base change map, and the hypothesis on `iX`
is separatedness rather than quasi-separatedness. -/
theorem nonempty_cohomologyBaseChangeIso [IsAffine S] [IsAffine T] [Flat q]
    (H : IsPullback p kY iX q) [IsSeparated iX] [QuasiCompact iX]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Nonempty
      ((baseRestrictScalars iX ⋙ baseExtendScalars q).obj
          (((SheafOfModules.evaluation.{u} X.ringCatSheaf
            (op (⊤ : X.Opens))).rightDerived n).obj F) ≅
        (baseRestrictScalars kY).obj
          (((SheafOfModules.evaluation.{u} Y.ringCatSheaf
            (op (⊤ : Y.Opens))).rightDerived n).obj ((Scheme.Modules.pullback p).obj F))) := by
  obtain ⟨ι, hι, U, hU, hUaff⟩ := exists_finite_affineOpen_cover_inter_of_isAffine iX
  exact ⟨cohomologyBaseChangeIsoOfCover H F U hU hUaff n⟩

end

end AlgebraicGeometry

end
