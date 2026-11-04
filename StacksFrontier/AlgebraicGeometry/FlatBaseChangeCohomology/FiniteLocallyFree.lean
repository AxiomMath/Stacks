module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffinePositiveDegree
public import StacksFrontier.AlgebraicGeometry.SectionsIso.Descent
public import StacksFrontier.Homology.ExtendScalars.FinitePresentationProducts

/-!
# Finite locally free base change for cohomology, with no quasi-compactness

Let

```
Y --p--> X
|        |
k        iX
v        v
T --q--> S
```

be a cartesian square of schemes with `S` and `T` affine, let `q` be **finite locally free**, let
`iX` be separated, and let `F` be a quasi-coherent `𝒪_X`-module. Then for every `n`

`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Hⁿ(X, F) ≅ Hⁿ(Y, p^* F)`.

`StacksFrontier/AlgebraicGeometry/FlatBaseChangeCohomology/AffinePositiveDegree.lean` proves the
same conclusion for a **flat** `q` and an `iX` that is separated *and quasi-compact*. What is
removed here is the quasi-compactness, and finite local freeness of `q` is exactly what pays
for it.

## Why finite local freeness removes the quasi-compactness

Both proofs compute the two cohomologies as the homology of explicit Čech complexes and identify
the complex upstairs with the base change of the complex downstairs. The degree-`n` term of a
Čech complex is a **product** over the `(n+1)`-tuples of members of the covering, so the
identification needs the change-of-rings functor `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} -` to commute with that
product. For a finite covering this is additivity and nothing more, which is why the flat
statement has to produce a finite covering and therefore has to assume `X` quasi-compact.

A finite locally free `q` makes `Γ(T, ⊤)` a *finitely presented* `Γ(S, ⊤)`-module, and tensoring
with a finitely presented module commutes with products over an **arbitrary** index
([Stacks, Tag 059K], here as
`ModuleCat.preservesLimitsOfShape_discrete_extendScalars`). The covering may then be taken to be
the covering of `X` by **all** of its affine opens, which exists for every scheme and whose
finite intersections are affine as soon as `X` is separated — no finiteness anywhere.

This is the sentence *"as `B` is finitely presented as an `A`-module we see that tensoring with
`B` over `A` commutes with products"* in the proof of [Stacks, Tag 0CKW].

## Main definitions

* `AlgebraicGeometry.cechBaseChangeIsoOfFinitePresentation`: the isomorphism of Čech complexes
  for an **arbitrary** index type, the finiteness of
  `Stacks.AlgebraicGeometry.SectionsBaseChange.cechBaseChangeIso` traded for finite presentation
  of `Γ(T, ⊤)` over `Γ(S, ⊤)`.
* `AlgebraicGeometry.cohomologyBaseChangeIsoOfCoverOfFinitePresentation`: the comparison
  isomorphism on cohomology, for an explicitly given cover of `X` — of arbitrary cardinality —
  with affine finite intersections.

## Main results

* `AlgebraicGeometry.exists_affineOpen_cover_inter_of_isSeparated`: a scheme separated over an
  affine base is covered by its affine opens, and every finite intersection of those is affine.
  This is the quasi-compactness-free replacement for
  `AlgebraicGeometry.exists_finite_affineOpen_cover_inter_of_isAffine`.
* `AlgebraicGeometry.nonempty_cohomologyBaseChangeIso_of_finitePresentation`: the comparison
  isomorphism exists for every separated `iX`, with the hypotheses on `q` read as flatness and
  finite presentation of the ring map on global sections.
* `AlgebraicGeometry.nonempty_cohomologyBaseChangeIso_of_isFiniteLocallyFree`: the same with the
  hypothesis on `q` in its geometric form, `Stacks.Morphisms.IsFiniteLocallyFree`.

## Relation to [Stacks, Tag 0CKW]

The statements here assume `iX` separated, which is the case treated in the second paragraph
of the source's proof. Tag 0CKW itself, for an arbitrary `X` and for the canonical map, is
`Stacks.Tag0CKW.isIso_cohomologyBaseChangeMap` in
`StacksFrontier/AlgebraicGeometry/FlatBaseChangeCohomology/FiniteLocallyFreeCanonical.lean`.

## References

* [Stacks Project, Tag 0CKW](https://stacks.math.columbia.edu/tag/0CKW)
* [Stacks Project, Tag 059K](https://stacks.math.columbia.edu/tag/059K)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.CechSheaf (cechComplex)
open Stacks.AlgebraicGeometry.SectionsBaseChange (baseRestrictScalars baseExtendScalars
  comparisonDeg comparisonDeg_comm top_eq_iSup_preimage le_preimage_top)

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### A covering by all the affine opens -/

/-- **A scheme separated over an affine base is covered by its affine opens, and every finite
intersection of those is affine.** The index type is the type of affine opens itself, so no
quasi-compactness is needed and the covering is in general infinite; separatedness over the
affine base makes the diagonal over the terminal scheme affine, hence the intersections affine.

This is `AlgebraicGeometry.exists_finite_affineOpen_cover_inter_of_isAffine` with the
quasi-compactness of the morphism — and the finiteness of the index it buys — dropped. -/
theorem exists_affineOpen_cover_inter_of_isSeparated {S X : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [IsSeparated f] :
    ∃ (ι : Type u) (U : ι → X.Opens), (⊤ : X.Opens) = ⨆ i, U i ∧
      ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ j, U (s j)) := by
  have : IsSeparated (terminal.from X) := by
    rw [show terminal.from X = f ≫ terminal.from S from terminal.hom_ext _ _]
    infer_instance
  refine ⟨{V : X.Opens // IsAffineOpen V}, Subtype.val, ?_,
    fun r s => IsAffineOpen.iInf fun j => (s j).2⟩
  refine le_antisymm ?_ le_top
  intro x _
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := x) (U := ⊤) (by simp)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW⟩, hxW⟩

/-! ### The Čech comparison over an arbitrary index type -/

section

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}
  (H : IsPullback p k iX q)

/-- **The Čech complex of the preimage covering is the base change of the Čech complex, for a
covering of arbitrary cardinality.** This is
`Stacks.AlgebraicGeometry.SectionsBaseChange.cechBaseChangeIso` with `[Finite ι]` replaced by
finite presentation of `Γ(T, ⊤)` over `Γ(S, ⊤)`.

Finiteness of the index is used in that lemma for one thing only: the degree-`n` term of a Čech
complex is a product over `Fin (n + 1) → ι`, and an additive functor preserves finite products.
Here the same product-preservation hypothesis of
`Stacks.CategoryTheory.CechComplex.cechComparisonIso` is discharged from
`ModuleCat.preservesLimitsOfShape_discrete_extendScalars` instead, which is [Stacks, Tag 059K].
No flatness is used; it enters only when homology is taken. -/
def cechBaseChangeIsoOfFinitePresentation [IsAffine S] [IsAffine T] (F : X.Modules)
    [F.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ {m : ℕ} (x : Fin (m + 1) → ι), IsAffineOpen (⨅ a, U (x a)))
    (hfp : letI := (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom.toAlgebra;
      Module.FinitePresentation ↑Γ(S, ⊤) ↑Γ(T, ⊤)) :
    ((baseRestrictScalars iX ⋙ baseExtendScalars q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (cechComplex.{u, u, u, u} (R := X.ringCatSheaf) (⊤ : X.Opens) U hU F) ≅
      ((baseRestrictScalars k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechComplex.{u, u, u, u} (R := Y.ringCatSheaf) (⊤ : Y.Opens) (fun i => p ⁻¹ᵁ U i)
          (top_eq_iSup_preimage U hU p) ((Scheme.Modules.pullback p).obj F)) :=
  cechComparisonIso _ _ _ _ _ _
    (fun x => comparisonDeg H F U hU hUaff x)
    (fun n =>
      letI := ModuleCat.preservesLimitsOfShape_discrete_extendScalars
        (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom hfp (Fin (n + 1) → ι)
      isLimitFanMap _ _ _ n)
    (fun n => isLimitFanMap _ _ _ n)
    (fun x h => comparisonDeg_comm H F U hU hUaff x h)

/-! ### The comparison on cohomology -/

/-- **Base change of the cohomology of a quasi-coherent module over an affine base, from a
covering of arbitrary cardinality with affine finite intersections.** For a cartesian square with
`S` and `T` affine, the ring map `Γ(S, ⊤) ⟶ Γ(T, ⊤)` flat and `Γ(T, ⊤)` a finitely presented
`Γ(S, ⊤)`-module, and any cover `U` of `X` whose nonempty finite intersections are affine,
`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Hⁿ(X, F) ≅ Hⁿ(Y, p^* F)` in every degree.

This is `AlgebraicGeometry.cohomologyBaseChangeIsoOfCover` with the finiteness of the cover
traded for finite presentation. -/
def cohomologyBaseChangeIsoOfCoverOfFinitePresentation [IsAffine S] [IsAffine T]
    (F : X.Modules) [F.IsQuasicoherent] {ι : Type u}
    (U : ι → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ j, U (s j)))
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
    (hfp : letI := (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom.toAlgebra;
      Module.FinitePresentation ↑Γ(S, ⊤) ↑Γ(T, ⊤)) (n : ℕ) :
    (baseRestrictScalars iX ⋙ baseExtendScalars q).obj
        (((SheafOfModules.evaluation.{u} X.ringCatSheaf
          (op (⊤ : X.Opens))).rightDerived n).obj F) ≅
      (baseRestrictScalars k).obj
        (((SheafOfModules.evaluation.{u} Y.ringCatSheaf
          (op (⊤ : Y.Opens))).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)) :=
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
      (cechBaseChangeIsoOfFinitePresentation H F U hU (fun {m} x => hUaff m x) hfp) ≪≫
    baseRestrictScalarsHomologyIso k
      (cechComplex.{u, u, u, u} (⊤ : Y.Opens) (fun i => p ⁻¹ᵁ U i) hU'
        ((Scheme.Modules.pullback p).obj F)) n ≪≫
    (baseRestrictScalars k).mapIso
      (rightDerivedEvaluationCechHomologyIso Y ⊤ (fun i => p ⁻¹ᵁ U i) hU' hU'aff
        ((Scheme.Modules.pullback p).obj F) n).symm

include H in
/-- **Base change of cohomology over an affine base along a flat, finitely presented ring map,
with `X` separated but not quasi-compact.** For a cartesian square with `S` and `T` affine, the
global-sections map `Γ(S, ⊤) ⟶ Γ(T, ⊤)` flat and making `Γ(T, ⊤)` a finitely presented
`Γ(S, ⊤)`-module, and `iX` separated, `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Hⁿ(X, F) ≅ Hⁿ(Y, p^* F)` in every
degree.

The covering used is the covering of `X` by all of its affine opens. The isomorphism is not
identified with the canonical base change map. -/
theorem nonempty_cohomologyBaseChangeIso_of_finitePresentation [IsAffine S] [IsAffine T]
    [IsSeparated iX] (F : X.Modules) [F.IsQuasicoherent]
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
    (hfp : letI := (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom.toAlgebra;
      Module.FinitePresentation ↑Γ(S, ⊤) ↑Γ(T, ⊤)) (n : ℕ) :
    Nonempty
      ((baseRestrictScalars iX ⋙ baseExtendScalars q).obj
          (((SheafOfModules.evaluation.{u} X.ringCatSheaf
            (op (⊤ : X.Opens))).rightDerived n).obj F) ≅
        (baseRestrictScalars k).obj
          (((SheafOfModules.evaluation.{u} Y.ringCatSheaf
            (op (⊤ : Y.Opens))).rightDerived n).obj ((Scheme.Modules.pullback p).obj F))) := by
  obtain ⟨ι, U, hU, hUaff⟩ := exists_affineOpen_cover_inter_of_isSeparated iX
  exact ⟨cohomologyBaseChangeIsoOfCoverOfFinitePresentation H F U hU hUaff hq hfp n⟩

include H in
/-- **Finite locally free base change for cohomology, with `X` separated but not quasi-compact.**
For a cartesian square with `S` and `T` affine, `q` finite locally free and `iX` separated,
`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Hⁿ(X, F) ≅ Hⁿ(Y, p^* F)` in every degree, for every quasi-coherent
`𝒪_X`-module `F`.

The two module-theoretic consequences of finite local freeness — flatness of `Γ(S, ⊤) ⟶ Γ(T, ⊤)`
and finite presentation of `Γ(T, ⊤)` over `Γ(S, ⊤)` — are read off by
`Stacks.Tag0CKW.flat_and_finitePresentation_of_isFiniteLocallyFree`, which is [Stacks, Tag 02KB].

For an arbitrary `X`, and for the canonical map, see
`Stacks.Tag0CKW.isIso_cohomologyBaseChangeMap`. -/
theorem nonempty_cohomologyBaseChangeIso_of_isFiniteLocallyFree [IsAffine S] [IsAffine T]
    [Stacks.Morphisms.IsFiniteLocallyFree q] [IsSeparated iX]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Nonempty
      ((baseRestrictScalars iX ⋙ baseExtendScalars q).obj
          (((SheafOfModules.evaluation.{u} X.ringCatSheaf
            (op (⊤ : X.Opens))).rightDerived n).obj F) ≅
        (baseRestrictScalars k).obj
          (((SheafOfModules.evaluation.{u} Y.ringCatSheaf
            (op (⊤ : Y.Opens))).rightDerived n).obj ((Scheme.Modules.pullback p).obj F))) := by
  obtain ⟨hflat, hfp⟩ := Stacks.Tag0CKW.flat_and_finitePresentation_of_isFiniteLocallyFree q
    (Stacks.Tag0CKW.appLE_top_eq_appTop q (le_preimage_top q ⊤))
  exact nonempty_cohomologyBaseChangeIso_of_finitePresentation H F hflat hfp n

end

end AlgebraicGeometry

end
