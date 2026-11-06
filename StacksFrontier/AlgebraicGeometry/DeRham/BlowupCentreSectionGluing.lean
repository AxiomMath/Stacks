module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupCentreSection
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupCentreBundleChernClass
public import StacksFrontier.AlgebraicGeometry.Blowup.CentreConormalRank
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DirectImageSectionTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.DisjointOpenCoverRestriction
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundleLerayHirsch

/-!
# The section on the centre in the proof of [Stacks, Tag 0FUW], by decomposing the centre

Let `i : Z ⟶ X` be a closed immersion of schemes smooth over `S`, with conormal sheaf `𝒞` read on
`Z`, and `π : 𝐏(𝒞) ⟶ Z` its projective bundle. The rank of `𝒞` is locally constant, so `Z` is the
disjoint union of the open and closed pieces `Z_r` on which `𝒞` has rank `r`; if `Z` has positive
codimension at every point, `r ≥ 1` on every nonempty piece. Over `Z_r`, the projective bundle is
`𝐏(𝒞|_{Z_r})`, and the Leray--Hirsch isomorphism of Remark 0FUN (i) gives the section of
`c ⊕ Rπ_*θ` there, for `θ` the untwisted morphism of `c₁^{dR}(𝒪(1))`. Since `D(Z, (Z ⟶ S)⁻¹𝒪_S)`
decomposes as a product over the pieces, these sections glue to one over `Z`
(`Stacks.DeRham.BlowupTriangle.hasDirectImageSection_centreBundle`). Transported along the
identification `φ : E ≅ 𝐏(𝒞)` of the exceptional divisor over `Z`, which carries `𝒪(1)` to
`𝒪_{X'}(-E)|_E` ([Stacks, Tag 0FUT]), this is the section on the centre of the exceptional
divisor (`Stacks.DeRham.BlowupTriangle.hasCentreSection_exceptional`), and hence the splitting of
[Stacks, Tag 0FUW] at the standard models of the derived categories.

## Main results

* `Stacks.DeRham.BlowupTriangle.hasDirectImageSection_centreBundle`: the glued section on `𝐏(𝒞)`.
* `Stacks.DeRham.BlowupTriangle.hasCentreSection_exceptional`: the section on the centre of the
  exceptional divisor.
* `Stacks.DeRham.BlowupTriangle.exists_retraction_toBlowUp_standard`: the splitting.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 0FUN](https://stacks.math.columbia.edu/tag/0FUN)
* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DeRhamDirectImage AlgebraicGeometry.DeRhamLerayHirsch Stacks.AlgebraicGeometry
open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase tautologicalDatumTwist
  isInvertible_tautologicalDatumTwist)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open scoped Stacks.StandardDerivedModel

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose SheafedSpace.sheaf
  AlgebraicGeometry.RingedSpace.inverseImage

attribute [local instance] isOpenImmersion_inverseImageBaseMap

namespace Stacks.DeRham.BlowupTriangle

section Conversion

variable {E Z S : Scheme.{u}} (p : E ⟶ Z) (g : Z ⟶ S) (L : E.Modules)
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible E.sheaf.obj E.ringCatSheaf.property L]

/-- **The section on the centre from the section of `c ⊕ Rp_*θ`** for the first Chern class of
`ℒ`. -/
theorem hasCentreSection_of_hasDirectImageSection
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (p ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (p ≫ g))) ((2 : ℕ) : ℤ))
    (hξ : ξ = chernClassTwo p g L) (h : HasDirectImageSection p g ((2 : ℕ) : ℤ) ξ) :
    HasCentreSection p g L := by
  subst hξ
  have e := baseMap_eq_relativeBase p g
  obtain ⟨τ, ν, h₁, h₂, h₃⟩ := h
  have hc : (DerivedCategory.Q.map (chain p g) ≫
      unit (Stacks.DeRhamSmooth.relativeBase p g) (deRhamCochainComplex (p ≫ g))) ≫
        eqToHom (congrArg (fun k => (derivedPushforward k).obj (deRhamObject (p ≫ g))) e.symm) =
      deRhamDirectImageMap p g := by
    rw [← deRhamDirectImageMap_comp_eqToHom]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact exists_section_derivedPushforward_of_eq e.symm (show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num)
    _ _ hc (untwistedChern { X := E, S := S, f := p ≫ g, L := L })
    (classUntwisted (p ≫ g) ((2 : ℕ) : ℤ) (chernClassTwo p g L))
    (heq_of_eq (untwistedChern_eq_classUntwisted p g L)) ⟨τ, ν, h₁, h₂, h₃⟩

end Conversion

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] [Smooth f]
  [Smooth (i ≫ f)]

/-! ### The pieces of the centre -/

/-- The morphism of inverse-image ringed spaces of the inclusion of the piece `Z_r`. -/
abbrev pieceMap (r : ℕ) :
    inverseImageBase ((centreRankPiece f i r).ι ≫ i ≫ f) ⟶ inverseImageBase (i ≫ f) :=
  Stacks.DeRhamBaseChange.inverseImageBaseMap (centreRankPiece f i r).ι
    ((centreRankPiece f i r).ι ≫ i ≫ f) (i ≫ f) (𝟙 S) (Category.comp_id _).symm

/-- The inclusion `𝐏(𝒞|_{Z_r}) ⟶ 𝐏(𝒞)` lies over the inclusion `Z_r ⟶ Z`. -/
theorem centreBundlePieceMap_comp (r : ℕ) :
    centreBundlePieceMap f i r ≫ projectiveBundleToBase Z (centreConormal i) =
      projectiveBundleToBase (centreRankPiece f i r) (centreConormalPiece f i r) ≫
        (centreRankPiece f i r).ι :=
  (isPullback_centreBundlePieceMap f i r).w

/-- The inclusion `𝐏(𝒞|_{Z_r}) ⟶ 𝐏(𝒞)` commutes with the structure morphisms to `S`. -/
theorem centreBundlePieceMap_comp_structure (r : ℕ) :
    centreBundlePieceMap f i r ≫ projectiveBundleToBase Z (centreConormal i) ≫ i ≫ f =
      (projectiveBundleToBase (centreRankPiece f i r) (centreConormalPiece f i r) ≫
        (centreRankPiece f i r).ι ≫ i ≫ f) ≫ 𝟙 S := by
  rw [Category.comp_id, ← Category.assoc, centreBundlePieceMap_comp, Category.assoc]

/-- **`c₁^{dR}(𝒪(1))` restricts on `𝐏(𝒞|_{Z_r})` to its `c₁^{dR}(𝒪(1))`.** -/
theorem deRhamPullbackSquare_centreBundlePieceMap_chernClass (r : ℕ) :
    Stacks.DeRhamBaseChange.deRhamPullbackSquare (centreBundlePieceMap f i r)
        (projectiveBundleToBase (centreRankPiece f i r) (centreConormalPiece f i r) ≫
          (centreRankPiece f i r).ι ≫ i ≫ f)
        (projectiveBundleToBase Z (centreConormal i) ≫ i ≫ f) (𝟙 S)
        (centreBundlePieceMap_comp_structure f i r) 2
        (projectiveBundleChernClass (i ≫ f) (centreConormal i)) =
      projectiveBundleChernClass ((centreRankPiece f i r).ι ≫ i ≫ f)
        (centreConormalPiece f i r) := by
  rw [Stacks.ProjectiveBundleDeRham.projectiveBundleChernClass_eq_deRhamFirstChernClassPicard,
    Stacks.DeRhamBaseChange.deRhamPullbackSquare_deRhamFirstChernClassPicard,
    Stacks.ProjectiveBundleDeRham.projectiveBundleChernClass_eq_deRhamFirstChernClassPicard]
  exact congrArg (Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard _)
    (Stacks.WeilCohomology.picardClassOf_eq_of_iso _ _ _ _ _ (centreBundlePieceTwistIso f i r))

/-- Every point of `𝐏(𝒞)` over `Z_r` lies in `𝐏(𝒞|_{Z_r})`. -/
theorem mem_range_centreBundlePieceMap (r : ℕ) (x : projectiveBundle Z (centreConormal i))
    (hx : (projectiveBundleToBase Z (centreConormal i)).base x ∈
      Set.range (centreRankPiece f i r).ι.base) :
    x ∈ Set.range (centreBundlePieceMap f i r).base :=
  mem_range_snd_of_isPullback (isPullback_centreBundlePieceMap f i r).flip hx

/-- **The pieces of positive rank cover `Z`** when `Z` has positive codimension everywhere. -/
theorem exists_mem_centreRankPiece (hint : interior (Set.range i.base) = ∅) (z : Z) :
    ∃ r : ULift.{u} {r : ℕ // 0 < r}, z ∈ centreRankPiece f i r.down.1 := by
  have hz : z ∈ ⨆ r : ℕ, centreRankPiece f i r := by
    rw [iSup_centreRankPiece]
    trivial
  obtain ⟨r, hr⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  refine ⟨⟨r, Nat.pos_of_ne_zero fun h0 => ?_⟩, hr⟩
  subst h0
  rw [centreRankPiece_zero_eq_bot f i hint] at hr
  exact hr

/-! ### Gluing the sections over the pieces -/

/-- **The section of `c ⊕ Rπ_*θ` for the projective bundle of the conormal sheaf of the centre**,
for `θ` the untwisted morphism of `c₁^{dR}(𝒪(1))`, from the Leray--Hirsch isomorphisms
(Remark 0FUN (i)) over the pieces `Z_r`, `r ≥ 1`, which cover `Z` when `Z` has positive
codimension everywhere. -/
theorem hasDirectImageSection_centreBundle (hint : interior (Set.range i.base) = ∅) :
    HasDirectImageSection (projectiveBundleToBase Z (centreConormal i)) (i ≫ f) ((2 : ℕ) : ℤ)
      (projectiveBundleChernClass (i ≫ f) (centreConormal i)) := by
  have hdisj : Pairwise fun (r s : ULift.{u} {r : ℕ // 0 < r}) =>
      Disjoint (Set.range (pieceMap f i r.down.1).hom.base)
        (Set.range (pieceMap f i s.down.1).hom.base) := by
    intro r s hrs
    rw [inverseImageBaseMap_base, inverseImageBaseMap_base, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    have hne : r.down.1 ≠ s.down.1 := fun h => hrs (ULift.ext (Subtype.ext h))
    refine Set.disjoint_left.2 fun z hr hs => ?_
    have h := (disjoint_centreRankPiece f i hne).le_bot
      (show z ∈ centreRankPiece f i r.down.1 ⊓ centreRankPiece f i s.down.1 from ⟨hr, hs⟩)
    simp at h
  have hcov : ∀ z : (inverseImageBase (i ≫ f) : TopCat), ∃ r : ULift.{u} {r : ℕ // 0 < r},
      z ∈ Set.range (pieceMap f i r.down.1).hom.base := by
    intro z
    obtain ⟨r, hr⟩ := exists_mem_centreRankPiece f i hint z
    refine ⟨r, ?_⟩
    rw [inverseImageBaseMap_base, Scheme.Opens.range_ι]
    exact hr
  unfold HasDirectImageSection
  refine CategoryTheory.Pretriangulated.exists_retraction_and_section_of_forall_map
    (fun r : ULift.{u} {r : ℕ // 0 < r} =>
      (RingedSpaceModuleAdjunction.modulePullback (pieceMap f i r.down.1)).mapDerivedCategory)
    (fun φ hφ =>
      Cohomology.DisjointOpenCover.eq_zero_of_forall_modulePullback_mapDerivedCategory_map_eq_zero
        (fun r : ULift.{u} {r : ℕ // 0 < r} => pieceMap f i r.down.1) hdisj hcov φ hφ) _ _
    fun r => ?_
  have := isIso_projectiveBundleLerayHirschMorphism ((centreRankPiece f i r.down.1).ι ≫ i ≫ f)
    (centreConormalPiece f i r.down.1) r.down.1
  have hP := exists_section_of_isIso_lerayHirschPowerMorphism
    (projectiveBundleToBase (centreRankPiece f i r.down.1) (centreConormalPiece f i r.down.1))
    ((centreRankPiece f i r.down.1).ι ≫ i ≫ f) 2
    (projectiveBundleChernClass ((centreRankPiece f i r.down.1).ι ≫ i ≫ f)
      (centreConormalPiece f i r.down.1)) r.down.1 r.down.2
  have hP' : HasDirectImageSection
      (projectiveBundleToBase (centreRankPiece f i r.down.1) (centreConormalPiece f i r.down.1))
      ((centreRankPiece f i r.down.1).ι ≫ i ≫ f) ((2 : ℕ) : ℤ)
      (Stacks.DeRhamBaseChange.deRhamPullbackSquare (centreBundlePieceMap f i r.down.1)
        (projectiveBundleToBase (centreRankPiece f i r.down.1) (centreConormalPiece f i r.down.1) ≫
          (centreRankPiece f i r.down.1).ι ≫ i ≫ f)
        (projectiveBundleToBase Z (centreConormal i) ≫ i ≫ f) (𝟙 S)
        (centreBundlePieceMap_comp_structure f i r.down.1) ((2 : ℕ) : ℤ)
        (projectiveBundleChernClass (i ≫ f) (centreConormal i))) :=
    HasDirectImageSection.of_eq hP
      (deRhamPullbackSquare_centreBundlePieceMap_chernClass f i r.down.1).symm
  exact exists_section_mapDerivedCategory_of_restrict (centreBundlePieceMap f i r.down.1)
    (projectiveBundleToBase Z (centreConormal i))
    (projectiveBundleToBase (centreRankPiece f i r.down.1) (centreConormalPiece f i r.down.1))
    (centreRankPiece f i r.down.1).ι (i ≫ f) (centreBundlePieceMap_comp_structure f i r.down.1)
    (Category.comp_id _).symm (mem_range_centreBundlePieceMap f i r.down.1)
    (centreBundlePieceMap_comp f i r.down.1) ((2 : ℕ) : ℤ)
    (projectiveBundleChernClass (i ≫ f) (centreConormal i)) hP'

/-! ### The section on the centre of the exceptional divisor -/

/-- **The section on the centre of the exceptional divisor** for `𝒪_{X'}(-E)|_E`, from the
Leray--Hirsch isomorphisms (Remark 0FUN (i)) over the pieces `Z_r`, `r ≥ 1`, of the centre, which
cover `Z` when `Z` has positive codimension everywhere. -/
theorem hasCentreSection_exceptional (hint : interior (Set.range i.base) = ∅) :
    HasCentreSection (exceptionalProjection i) (i ≫ f) (exceptionalSituation f i).L
      (hL := (exceptionalSituation f i).invertible) :=
  hasCentreSection_of_hasDirectImageSection (exceptionalProjection i) (i ≫ f)
    (exceptionalSituation f i).L (hL := (exceptionalSituation f i).invertible) _
    (deRhamPullbackSquare_centreBundleChernClass f i)
    (HasDirectImageSection.of_isIso (exceptionalDivisorIsoCentreBundle f i).hom
      (projectiveBundleToBase Z (centreConormal i)) (exceptionalProjection i) (i ≫ f)
      (exceptionalDivisorIsoCentreBundle_hom_toBase f i)
      (exceptionalDivisorIsoCentreBundle_hom_comp_structure f i) ((2 : ℕ) : ℤ)
      (projectiveBundleChernClass (i ≫ f) (centreConormal i))
      (hasDirectImageSection_centreBundle f i hint))

/-- **[Stacks, Tag 0FUW] at the standard models of the derived categories**, from the
Leray--Hirsch isomorphisms (Remark 0FUN (i)) over the pieces `Z_r`, `r ≥ 1`, of the centre: if
`Z` has positive codimension in `X` at every point, the canonical map
`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` has a retraction. -/
theorem exists_retraction_toBlowUp_standard (hint : interior (Set.range i.base) = ∅) :
    ∃ r : blowUpDeRham f i ⟶ deRham f, toBlowUp f i ≫ r = 𝟙 _ :=
  exists_retraction_toBlowUp_of_hasCentreSection f i (hasCentreSection_exceptional f i hint)

end Stacks.DeRham.BlowupTriangle

end
