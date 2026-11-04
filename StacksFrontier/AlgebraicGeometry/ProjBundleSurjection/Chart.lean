module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.SegreClosedImmersion
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.Open
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A surjection of graded algebras, chart by chart

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras which is **surjective
on homogeneous local sections over the affine opens of the base**. Over an affine open `U` of `S`
it induces a morphism `Proj Γ(U, B) ⟶ Proj Γ(U, A)` defined on the whole chart; this morphism is
a closed immersion, commutes with the structure morphisms to `U`, and commutes with the
transitions of Tag 01NO.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjBundleSurjection.SurjectiveOnAffineSections`: surjectivity of a
  homomorphism of graded algebras on homogeneous sections over every affine open.
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap`: the morphism of charts.

## Main results

* `Stacks.AlgebraicGeometry.ProjBundleSurjection.mapHomOfTop_comp`: **functoriality of the
  everywhere-defined induced morphism of projective spectra.** For composable graded ring
  homomorphisms both satisfying Mathlib's hypothesis `ℬ₊ ≤ 𝒜₊.map ψ`, the morphism induced by
  the composite is the composite of the induced morphisms, for
  `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop`.
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.isClosedImmersion_chartMap`: each chart map is a
  closed immersion.
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap_comp_projInclusionMap`: the chart maps
  commute with the transitions of Tag 01NO. This is the glueing datum.
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap_comp_projInclusionToOpen`: each chart
  map is a morphism over the affine open of the base.

## How the composition law is obtained

`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` is built by glueing the maps of degree-zero
homogeneous localizations over the standard opens of the domain of definition, so a composition
law for it is not formal. It is obtained here by *leaving* that description: under Mathlib's
hypothesis the glued morphism is Mathlib's `AlgebraicGeometry.Proj.map`
(`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map`), and `AlgebraicGeometry.Proj.map`
has a composition law (`AlgebraicGeometry.Proj.map_comp`). Both hypotheses are available in the
situation at hand: a surjection satisfies Mathlib's inclusion outright, and restriction along an
inclusion of affine opens satisfies it by quasi-coherence
(`Stacks.AlgebraicGeometry.RelativeProjGeneral.irrelevant_le_map_res_of_le_opens`).

This is why the hypothesis here is honest surjectivity in **every** degree rather than the
eventual surjectivity of Tag 01N1. Eventual surjectivity gives `U(ψ) = ⊤` and a closed immersion,
but only the *radical* inclusion of irrelevant ideals
(`Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_iff_irrelevant_le_radical`), so
`AlgebraicGeometry.Proj.map` is unavailable and with it the composition law.

## Implementation notes

The surjectivity hypothesis is stated degreewise on `ℕ`-indexed homogeneous sections, through
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.sectionPieceHom`,
because that is the form in which the graded ring of sections is assembled; the negative
pieces are irrelevant to the section ring and no hypothesis is placed on them. Surjectivity
of the whole ring homomorphism is derived from it by `DirectSum.induction_on`, and
surjectivity of each graded component by reading off the summand.

The opens are indexed by `AlgebraicGeometry.Scheme.AffineZariskiSite`, which is the index of the
glueing, and the hypothesis is stated over `S.Opens` together with a proof of affineness, which
is the form `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData` uses. The two are the
same data and the translation is `U.toOpens`, `U.2`.

`AlgebraicGeometry.Proj.map` declares its `SetLike` carriers in the ring's own universe, so the
composition law is stated with all three carriers in `Type u`; the gradings occurring here are
`AddSubgroup` of the section rings, which are in `Type u`, so nothing is lost.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open HomogeneousIdeal
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.AlgebraicGeometry.ProjBundleSurjection

universe u

/-! ### Functoriality of the everywhere-defined induced morphism -/

section Composition

variable {A B C : Type u} {σ τ ω : Type u}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ω C] [AddSubgroupClass ω C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → ω) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- **Functoriality of `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop`.** For composable
graded ring homomorphisms each satisfying Mathlib's inclusion of irrelevant ideals, the morphism
of projective spectra induced by the composite is the composite of the induced morphisms. -/
@[ega "II 2.8.4" "special case"]
public theorem mapHomOfTop_comp (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞)
    (hφ : irrelevant ℬ ≤ (irrelevant 𝒜).map φ)
    (hψ : irrelevant 𝒞 ≤ (irrelevant ℬ).map ψ)
    (hdφ : mapDomain 𝒜 ℬ φ = ⊤) (hdψ : mapDomain ℬ 𝒞 ψ = ⊤)
    (hdc : mapDomain 𝒜 𝒞 (ψ.comp φ) = ⊤) :
    mapHomOfTop 𝒜 𝒞 (ψ.comp φ) hdc = mapHomOfTop ℬ 𝒞 ψ hdψ ≫ mapHomOfTop 𝒜 ℬ φ hdφ := by
  rw [mapHomOfTop_eq_map 𝒜 𝒞 (ψ.comp φ) (irrelevant_le_map_comp hφ hψ) hdc,
    mapHomOfTop_eq_map 𝒜 ℬ φ hφ hdφ, mapHomOfTop_eq_map ℬ 𝒞 ψ hψ hdψ,
    Proj.map_comp]

end Composition

/-! ### Surjectivity on sections -/

section Sections

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S}

/-- A homomorphism of sheaf-level graded algebras is *surjective on affine sections* if, over
every affine open of the base and in every nonnegative degree, every homogeneous section of the
target is the image of one of the source. -/
public def SurjectiveOnAffineSections (ψ : SheafGradedAlgebraHom A B) : Prop :=
  ∀ (U : S.Opens), IsAffineOpen U → ∀ n : ℕ, Function.Surjective (ψ.sectionPieceHom U n)

variable {ψ : SheafGradedAlgebraHom A B}

/-- Each graded component of the induced homomorphism of section rings is surjective. -/
public theorem surjective_gradedAddHom (hψ : SurjectiveOnAffineSections ψ) {U : S.Opens}
    (hU : IsAffineOpen U) (d : ℕ) :
    Function.Surjective (GradedRingHom.gradedAddHom (ψ.sectionHom U) d) := by
  rintro ⟨y, b, rfl⟩
  obtain ⟨a, rfl⟩ := hψ U hU d b
  exact ⟨⟨_, A.of_mem_grading U a⟩, Subtype.ext (ψ.sectionHom_of U a)⟩

/-- The induced homomorphism of the graded rings of sections over an affine open is surjective. -/
public theorem surjective_sectionHom (hψ : SurjectiveOnAffineSections ψ) {U : S.Opens}
    (hU : IsAffineOpen U) :
    Function.Surjective (ψ.sectionHom U) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n b =>
    obtain ⟨a, rfl⟩ := hψ U hU n b
    exact ⟨DirectSum.of (A.sectionPieces U) n a, ψ.sectionHom_of U a⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/-- A surjection satisfies Mathlib's inclusion of irrelevant ideals: a homogeneous element of
positive degree of the target has a homogeneous preimage of the same degree. -/
public theorem irrelevant_le_map_sectionHom (hψ : SurjectiveOnAffineSections ψ) {U : S.Opens}
    (hU : IsAffineOpen U) :
    irrelevant (B.grading U) ≤ (irrelevant (A.grading U)).map (ψ.sectionHom U) := by
  refine (irrelevant_le (B.grading U)).2 fun i hi x hx => ?_
  obtain ⟨a, ha⟩ := surjective_gradedAddHom hψ hU i ⟨x, hx⟩
  have hae : ψ.sectionHom U (a : A.sectionRing U) = x := congrArg Subtype.val ha
  change x ∈ ((irrelevant (A.grading U)).map (ψ.sectionHom U)).toAddSubmonoid
  rw [← hae]
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ hi a.2)

/-- The morphism induced by a surjection is defined on the whole chart. -/
public theorem mapDomain_sectionHom_eq_top (hψ : SurjectiveOnAffineSections ψ) {U : S.Opens}
    (hU : IsAffineOpen U) :
    mapDomain (A.grading U) (B.grading U) (ψ.sectionHom U) = ⊤ :=
  mapDomain_eq_top_of_surjective _ _ _ (surjective_sectionHom hψ hU)

end Sections

/-! ### The morphism of charts -/

section Chart

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} {ψ : SheafGradedAlgebraHom A B}

/-- **The morphism of charts.** Over an affine open `U` of the base, a surjection of graded
algebras induces a morphism `Proj Γ(U, B) ⟶ Proj Γ(U, A)` on the whole of the chart. -/
public def chartMap (hψ : SurjectiveOnAffineSections ψ) (U : S.Opens) (hU : IsAffineOpen U) :
    AlgebraicGeometry.Proj (B.grading U) ⟶ AlgebraicGeometry.Proj (A.grading U) :=
  mapHomOfTop (A.grading U) (B.grading U) (ψ.sectionHom U)
    (mapDomain_sectionHom_eq_top hψ hU)

/-- The morphism of charts is Mathlib's `AlgebraicGeometry.Proj.map`. -/
public theorem chartMap_eq_map (hψ : SurjectiveOnAffineSections ψ) (U : S.Opens)
    (hU : IsAffineOpen U) :
    chartMap hψ U hU = Proj.map (ψ.sectionHom U) (irrelevant_le_map_sectionHom hψ hU) :=
  mapHomOfTop_eq_map _ _ _ _ _

/-- **The morphism of charts is a closed immersion.** It is the morphism of projective spectra of
a surjection of graded rings, so this is Tag 01N1 part (2). -/
public theorem isClosedImmersion_chartMap (hψ : SurjectiveOnAffineSections ψ) (U : S.Opens)
    (hU : IsAffineOpen U) :
    IsClosedImmersion (chartMap hψ U hU) :=
  SegreClosedImmersion.isClosedImmersion_mapHomOfTop _ _ _ _
    (Filter.Eventually.of_forall (surjective_gradedAddHom hψ hU))

/-- The induced homomorphism of section rings carries the structure map of the source to the
structure map of the target: both send a function to its multiple of the unit, and `ψ` preserves
the unit and is `𝒪_S`-linear. -/
public theorem sectionHom_strHom (ψ : SheafGradedAlgebraHom A B) (U : S.Opens) (r : Γ(S, U)) :
    ψ.sectionHom U (A.strHom U r) = B.strHom U r := by
  change ψ.sectionHom U (DirectSum.of (A.sectionPieces U) 0 (r • A.one U)) =
    DirectSum.of (B.sectionPieces U) 0 (r • B.one U)
  rw [ψ.sectionHom_of U (r • A.one U)]
  refine congrArg (DirectSum.of (B.sectionPieces U) 0) ?_
  change (ψ.app 0).app U (r • A.one U) = r • B.one U
  rw [Scheme.Modules.Hom.app_smul, ψ.app_one U]

/-! ### Over the base -/

/-- The degree-zero corestriction of the structure map of the section ring, written at the
*sheaf-level* spelling `A.grading U` rather than at
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.strZero`'s spelling
`A.toGradedAlgebra.grading ⟨U, hU⟩`; the two are definitionally equal
(`Stacks.AlgebraicGeometry.ProjBundleSurjection.toGradedAlgebra_strZero`). -/
public def strZeroSheaf (A : SheafGradedAlgebra S) (U : S.Opens) :
    Γ(S, U) ⟶ CommRingCat.of (A.grading U 0) :=
  CommRingCat.ofHom ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U))

/-- The two spellings of the degree-zero structure map agree. -/
public theorem toGradedAlgebra_strZero (A : SheafGradedAlgebra S) (V : S.AffineZariskiSite) :
    A.toGradedAlgebra.strZero V = strZeroSheaf A V.toOpens := rfl

/-- The degree-zero structure map is the structure map of the section ring. -/
public theorem coe_strZeroSheaf_apply (A : SheafGradedAlgebra S) (U : S.Opens) (r : Γ(S, U)) :
    (strZeroSheaf A U r : A.sectionRing U) = A.strHom U r :=
  projZeroRingHom'_coe_of_mem (A.grading U) (A.strHom_mem U r)

/-- The degree-zero part of the induced homomorphism of section rings is compatible with the
corestricted structure morphisms of the two charts. -/
public theorem strZeroSheaf_comp_zeroHom (ψ : SheafGradedAlgebraHom A B) (U : S.Opens) :
    strZeroSheaf A U ≫
        CommRingCat.ofHom (zeroHom (A.grading U) (B.grading U) (ψ.sectionHom U)) =
      strZeroSheaf B U := by
  ext r : 2
  refine Subtype.ext ?_
  refine Eq.trans (coe_zeroHom_apply (A.grading U) (B.grading U)
    (ψ.sectionHom U) _) ?_
  refine Eq.trans (congrArg (fun x => ψ.sectionHom U x)
    (coe_strZeroSheaf_apply A U r)) ?_
  exact Eq.trans (sectionHom_strHom ψ U r) (coe_strZeroSheaf_apply B U r).symm

/-- The morphism of charts is compatible with the structure morphisms to the spectrum of the
functions on the affine open, before the identification of that spectrum with the open itself. -/
public theorem chartMap_comp_toSpecZero (hψ : SurjectiveOnAffineSections ψ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    chartMap hψ U hU ≫ Proj.toSpecZero (A.grading U) ≫ Spec.map (strZeroSheaf A U) =
      Proj.toSpecZero (B.grading U) ≫ Spec.map (strZeroSheaf B U) := by
  rw [chartMap, mapHomOfTop_toSpecZero_assoc, ← Spec.map_comp, strZeroSheaf_comp_zeroHom ψ U]

/-- **The morphism of charts is a morphism over the affine open of the base**, stated over the
small affine Zariski site. -/
@[reassoc]
public theorem chartMap_comp_toOpen (hψ : SurjectiveOnAffineSections ψ)
    (V : S.AffineZariskiSite) :
    chartMap hψ V.toOpens V.2 ≫ A.toGradedAlgebra.toOpen V = B.toGradedAlgebra.toOpen V :=
  (reassoc_of% chartMap_comp_toSpecZero hψ V.toOpens V.2 :) (h := _)

/-- **The morphism of charts is a morphism over the affine open of the base.** -/
@[reassoc]
public theorem chartMap_comp_projInclusionToOpen (hψ : SurjectiveOnAffineSections ψ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    chartMap hψ U hU ≫ projInclusionToOpen A U hU = projInclusionToOpen B U hU :=
  chartMap_comp_toOpen hψ (⟨U, hU⟩ : S.AffineZariskiSite)

/-! ### The glueing datum -/

/-- **The glueing datum.** The morphisms of charts commute with the transitions of Tag 01NO: for
an inclusion `U ⊆ V` of affine opens of the base, going down to the source over `U` and then
along the transition of the source agrees with going along the transition of the target and then
down to the source over `V`. -/
@[ega "II 3.5.1" "special case"]
public theorem chartMap_comp_projInclusionMap (hψ : SurjectiveOnAffineSections ψ)
    (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    chartMap hψ U hU ≫ projInclusionMap A U V h hU hV =
      projInclusionMap B U V h hU hV ≫ chartMap hψ V hV := by
  have hres : ∀ X : SheafGradedAlgebra S,
      irrelevant (X.grading U) ≤ (irrelevant (X.grading V)).map (X.res h) := fun X =>
    RelativeProjGeneral.irrelevant_le_map_res_of_le_opens X.toGradedAlgebra
      (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) h
  have hdomA : mapDomain (A.grading V) (A.grading U) (A.res h) = ⊤ :=
    projInclusionDomain_eq_top A U V h hU hV
  have hdomB : mapDomain (B.grading V) (B.grading U) (B.res h) = ⊤ :=
    projInclusionDomain_eq_top B U V h hU hV
  have hcomp : mapDomain (A.grading V) (B.grading U)
      ((ψ.sectionHom U).comp (A.res h)) = ⊤ :=
    mapDomain_eq_top_of_irrelevant_le_map _ _ _
      (irrelevant_le_map_comp (hres A) (irrelevant_le_map_sectionHom hψ hU))
  have hcomp' : mapDomain (A.grading V) (B.grading U)
      ((B.res h).comp (ψ.sectionHom V)) = ⊤ := by
    rw [ψ.res_comp_sectionHom h]; exact hcomp
  have e1 := mapHomOfTop_comp (A.grading V) (A.grading U) (B.grading U) (A.res h)
    (ψ.sectionHom U) (hres A) (irrelevant_le_map_sectionHom hψ hU) hdomA
    (mapDomain_sectionHom_eq_top hψ hU) hcomp
  have e2 := mapHomOfTop_comp (A.grading V) (B.grading V) (B.grading U) (ψ.sectionHom V)
    (B.res h) (irrelevant_le_map_sectionHom hψ hV) (hres B)
    (mapDomain_sectionHom_eq_top hψ hV) hdomB hcomp'
  have hA : projInclusionMap A U V h hU hV =
      mapHomOfTop (A.grading V) (A.grading U) (A.res h) hdomA := rfl
  have hB : projInclusionMap B U V h hU hV =
      mapHomOfTop (B.grading V) (B.grading U) (B.res h) hdomB := rfl
  rw [chartMap, chartMap, hA, hB, ← e1, ← e2]
  congr 1
  exact (ψ.res_comp_sectionHom h).symm

end Chart

end Stacks.AlgebraicGeometry.ProjBundleSurjection

end
