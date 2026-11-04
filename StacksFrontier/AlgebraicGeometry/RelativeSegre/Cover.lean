module

public import StacksFrontier.AlgebraicGeometry.RelativeSegre.Chart
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic
public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.Basic

/-!
# The affine pieces cover the fibre product of two projective bundles

Let `H` and `G` be quasi-coherent modules on a scheme `X`. The affine pieces
`D₊(a) ×_U D₊(b)` of `𝐏(H) ×_X 𝐏(G)`, for `U` an affine open of `X` and `a`, `b` degree-one
elements of `Γ(U, Sym H)` and `Γ(U, Sym G)`, cover the fibre product: over `U` the bundle `𝐏(H)`
is `Proj Γ(U, Sym H)`, whose standard opens `D₊(a)` at the degree-one elements cover it since
`Γ(U, Sym H)` is generated in degree one.

## Main definitions

* `Stacks.RelativeSegre.pieceCover`: the open cover of `𝐏(H) ×_X 𝐏(G)` by the affine pieces.

## Main results

* `Stacks.RelativeSegre.iSup_basicOpen_eq_top`: the standard opens of the degree-one elements
  cover `Proj Γ(U, Sym E)`.
* `Stacks.RelativeSegre.range_pieceMap`: the image of a piece is the intersection of the inverse
  images of the two standard charts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.RelativeSegre

variable {X : Scheme.{u}}

section Cover

variable (E : X.Modules) [E.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)

/-- **The standard opens of the degree-one elements cover the chart** `Proj Γ(U, Sym E)`. -/
theorem iSup_basicOpen_eq_top (hU : IsAffineOpen U) :
    ⨆ a : (alg E).grading U 1, Proj.basicOpen ((alg E).grading U) (a : (alg E).sectionRing U) =
      ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' _ _ (fun a => ⟨1, a.2⟩) ?_
  rw [Subtype.range_coe_subtype]
  exact Stacks.SymGraded.adjoin_grading_one_eq_top E U
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) hU

/-- Every point of the chart of `𝐏(E)` over `U` lies in the standard chart of a degree-one
element. -/
theorem exists_mem_range_chartι (p : (bun E).scheme) (hp : (bun E).toBase p ∈ U) :
    ∃ a : (alg E).grading U 1, p ∈ Set.range (chartι E hU a) := by
  obtain ⟨q, -, rfl⟩ : p ∈ (bun E).chart U hU ''ᵁ ⊤ := by
    rw [Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top]
    exact hp
  have hq : q ∈ (⨆ a : (alg E).grading U 1,
      Proj.basicOpen ((alg E).grading U) (a : (alg E).sectionRing U)) := by
    rw [iSup_basicOpen_eq_top E hU]
    trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hq
  rw [← Proj.opensRange_awayι _ _ a.2 Nat.one_pos] at ha
  obtain ⟨y, rfl⟩ := ha
  exact ⟨a, y, rfl⟩

end Cover

section Pieces

variable (H G : X.Modules) [H.IsQuasicoherent] [G.IsQuasicoherent]

/-- **The image of a piece** is the set of points of `𝐏(H) ×_X 𝐏(G)` whose two projections lie
in the two standard charts. -/
theorem range_pieceMap {U : X.Opens} (hU : IsAffineOpen U) (a : (alg H).grading U 1)
    (b : (alg G).grading U 1) :
    Set.range (pieceMap H G hU a b) =
      pullback.fst (bun H).toBase (bun G).toBase ⁻¹' Set.range (chartι H hU a) ∩
        pullback.snd (bun H).toBase (bun G).toBase ⁻¹' Set.range (chartι G hU b) := by
  rw [← Scheme.Pullback.range_map _ _ (bun H).toBase (bun G).toBase (chartι H hU a)
    (chartι G hU b) hU.fromSpec (chartι_toBase H hU a).symm (chartι_toBase G hU b).symm]
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(pullbackSpecIso _ _ _).hom y, ?_⟩
    rw [pieceMap, Scheme.Hom.comp_apply]
    congr 1
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl

/-- The index set of the cover of `𝐏(H) ×_X 𝐏(G)` by affine pieces: an affine open `U` of `X`
and degree-one elements of `Γ(U, Sym H)` and `Γ(U, Sym G)`. -/
structure PieceIndex where
  /-- The affine open of the base. -/
  U : X.Opens
  /-- It is affine. -/
  hU : IsAffineOpen U
  /-- The degree-one element of `Γ(U, Sym H)`. -/
  a : (alg H).grading U 1
  /-- The degree-one element of `Γ(U, Sym G)`. -/
  b : (alg G).grading U 1

/-- Every point of the fibre product lies in an affine piece. -/
theorem exists_mem_range_pieceMap (z : (pullback (bun H).toBase (bun G).toBase : Scheme.{u})) :
    ∃ i : PieceIndex H G, z ∈ Set.range (pieceMap H G i.hU i.a i.b) := by
  set p₁ : pullback (bun H).toBase (bun G).toBase ⟶ (bun H).scheme := pullback.fst _ _
  set p₂ : pullback (bun H).toBase (bun G).toBase ⟶ (bun G).scheme := pullback.snd _ _
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show (bun H).toBase (p₁ z) ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨a, ha⟩ := exists_mem_range_chartι H hU (p₁ z) hxU
  have hxU' : (bun G).toBase (p₂ z) ∈ U := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hxU
  obtain ⟨b, hb⟩ := exists_mem_range_chartι G hU (p₂ z) hxU'
  refine ⟨⟨U, hU, a, b⟩, ?_⟩
  rw [range_pieceMap]
  exact ⟨ha, hb⟩

/-- **The open cover of `𝐏(H) ×_X 𝐏(G)` by the affine pieces** `D₊(a) ×_U D₊(b)`. -/
def pieceCover : (pullback (bun H).toBase (bun G).toBase).OpenCover :=
  Scheme.Cover.mkOfCovers (PieceIndex H G)
    (fun i => Spec (CommRingCat.of (pieceRing H G i.a i.b)))
    (fun i => pieceMap H G i.hU i.a i.b)
    (exists_mem_range_pieceMap H G) (fun i => isOpenImmersion_pieceMap H G i.hU i.a i.b)

end Pieces

end Stacks.RelativeSegre

end
