module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineBaseHom
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.AffineDegreeOpen
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.BaseSectionDictionary

/-!
# The morphism Lemma 01O1 attaches to a quadruple lies over the base

`StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.AffineDegreeOpen` builds, over an
affine base, the morphism `r : T ⟶ Proj_S(𝒜)` that [Stacks, Tag 01O1] attaches to a quadruple:
it is the classifying morphism `φ : T ⟶ U_d ⊆ Proj Γ(⊤, 𝒜)` of [Stacks, Tag 01NU], read into the
absolute `Proj` and then along the chart over `⊤`. It does not say that `r` lies over `S`, and
its module docstring recorded that as having nothing available to supply it.

**It does.** `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.`
`Quadruple.toProj_classifyingHom_comp_toSpecZero` is exactly the statement that `φ`, read into the
absolute `Proj` and followed by that scheme's structure morphism to `S`, is the quadruple's own
`f`; and `Stacks.VeryAmpleAffineBase.topChart_toBase` identifies the chart over `⊤` followed by
the structure morphism of `Proj_S(𝒜)` with that structure morphism of the absolute `Proj`. The
two spellings of the absolute structure morphism differ, which is the only content below: one is
`Stacks.VeryAmpleAffineBase.projStructureHom` and the other
`AlgebraicGeometry.Proj.toSpecZero` followed by the spectrum of the degree-zero structure map and
the affine identification of the base.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.structureRingHom_eq_strZeroSheaf`: the
  two spellings of the degree-zero structure map `Γ(S, ⊤) ⟶ 𝒜(⊤)_0` agree.
* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.classifyingHom_topChart_comp_toBase`:
  **the morphism the bridge builds lies over the base** — its composite with the structure
  morphism of `Proj_S(𝒜)` is the quadruple's own `f`.
* `Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.`
  `exists_hom_overBase_degreeOne_datum_of_isAffine`: the same assembled with the two inputs
  `...RelativeProjTwistChartBridge.exists_hom_degreeOne_datum_of_isAffine` already supplies, so
  that the morphism, the locus condition, the degree-one datum and the over-`S` identity come out
  of one statement.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeVeroneseTwists
open Stacks.BaseSectionDictionary
open Stacks.VeryAmpleAffineBase

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

variable {S T : Scheme.{u}} {B : SheafGradedAlgebra.{u} S} {k : ℕ} {f : T ⟶ S}

/-! ### The two spellings of the degree-zero structure map -/

/-- **The two spellings of the degree-zero structure map `Γ(S, ⊤) ⟶ 𝒜(⊤)_0` agree.**
`...RelativeProjQcohSheaf.AffineTripleSections.structureRingHom` corestricts the structure map of
the graded algebra to the degree-zero piece, while
`...ProjBundleSurjection.strZeroSheaf` composes it with the degree-zero projection of the graded
ring; the structure map lands in the degree-zero piece, so the projection leaves it alone. -/
theorem structureRingHom_eq_strZeroSheaf :
    AffineTripleSections.structureRingHom B
      = ProjBundleSurjection.strZeroSheaf B (⊤ : S.Opens) := by
  refine congrArg CommRingCat.ofHom (RingHom.ext fun r => Subtype.ext ?_)
  show (B.strHom (⊤ : S.Opens) r : B.sectionRing (⊤ : S.Opens))
    = (GradedRing.projZeroRingHom' (B.grading (⊤ : S.Opens)) (B.strHom ⊤ r) :
        B.sectionRing (⊤ : S.Opens))
  rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
    DirectSum.decompose_of_mem_same _ (B.strHom_mem (⊤ : S.Opens) r)]

/-! ### The morphism the bridge builds lies over the base -/

/-- **Stacks Project, Tag 01O1: the morphism attached to a quadruple over an affine base is a
morphism over `S`.** The classifying morphism `φ : T ⟶ U_d` of [Stacks, Tag 01NU], read into the
absolute `Proj Γ(⊤, 𝒜)` and then along the chart over `⊤`, composed with the structure morphism
of `Proj_S(𝒜)`, is the quadruple's own `f`. -/
theorem classifyingHom_topChart_comp_toBase [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (Q : Quadruple f (situationAlgebra B) (k : ℤ)) :
    (toProj (B.grading (⊤ : S.Opens)) (Quadruple.classifyingHom hk hqc Q) ≫
        topChart B (isAffineOpen_top S)) ≫ (relativeProj B).toBase = f := by
  rw [Category.assoc, topChart_toBase, projStructureHom_eq,
    ← structureRingHom_eq_strZeroSheaf, IsAffineOpen.fromSpec_top]
  exact Quadruple.toProj_classifyingHom_comp_toSpecZero hk hqc Q

/-! ### The three inputs of Lemma 01O1's `θ`-assertion, with the over-`S` identity -/

/-- **Over an affine base, every quadruple yields a morphism to the relative `Proj` that lands in
the relative degree-`d` locus, lies over the base, and carries the relative degree-one datum.**
This is `...RelativeProjTwistChartBridge.exists_hom_degreeOne_datum_of_isAffine` with the
over-`S` identity added, which `classifyingHom_topChart_comp_toBase` supplies; it is the shape
`...RelativeProjTwistChartBridge.pullbackTwistIso_over_base` consumes. -/
theorem exists_hom_overBase_degreeOne_datum_of_isAffine [IsAffine S] (hk : 0 < k)
    (D : RelativeProjTwists.TwistData B)
    (P : Quadruple f (situationAlgebra B) (k : ℤ)) :
    ∃ r : T ⟶ (relativeProj B).scheme,
      (∀ t : T, r.base t ∈ (relativeProj B).degreeOpen k) ∧
        r ≫ (relativeProj B).toBase = f ∧
          Nonempty ((pullbackTwistVeronese D (k : ℤ) r).piece 1 ≅ P.L) := by
  refine ⟨toProj (B.grading (⊤ : S.Opens)) (Quadruple.classifyingHom hk
      (fun n => B.isQuasicoherent n) P) ≫ topChart B (isAffineOpen_top S),
    mem_degreeOpen_toProj_topChart (isAffineOpen_top S) _,
    classifyingHom_topChart_comp_toBase hk (fun n => B.isQuasicoherent n) P, ⟨?_⟩⟩
  exact pullbackTwistVeronesePieceIso_one (isAffineOpen_top S) D _ ≪≫
    (ProjTripleClassifying.classifyingPair (B.grading (⊤ : S.Opens)) hk
      (veroneseSections P.twisting)
      (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top
        (fun n => B.isQuasicoherent n) P)).2

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
