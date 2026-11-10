module

public import StacksFrontier.AlgebraicGeometry.RelativeSegre.Restrict

/-!
# The relative Segre morphism `𝐏(H) ×_X 𝐏(G) ⟶ 𝐏(H ⊗ G)`

Let `H` and `G` be quasi-coherent modules on a scheme `X`. The Segre morphisms of the affine
pieces `D₊(a) ×_U D₊(b)` of `𝐏(H) ×_X 𝐏(G)` agree on the overlaps of the pieces: over a common
affine open this is `Stacks.RelativeSegre.pieceSegre_compat_sameBase`, and a piece agrees with its
restriction to a smaller affine open by `Stacks.RelativeSegre.pieceSegre_compat_res`. They
therefore glue to a morphism `𝐏(H) ×_X 𝐏(G) ⟶ 𝐏(H ⊗ G)`, the relative Segre morphism.

## Main definitions

* `Stacks.RelativeSegre.segre`: the relative Segre morphism.

## Main results

* `Stacks.RelativeSegre.pieceMap_segre`: on a piece it is the Segre morphism of the piece.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.RelativeSegre

variable {X : Scheme.{u}}

section RangeRes

variable (E : X.Modules) [E.IsQuasicoherent] {U W : X.Opens} (hU : IsAffineOpen U)
  (hW : IsAffineOpen W) (hWU : W ≤ U)

/-- A point of the standard chart of `a` lying over a smaller affine open `W` lies in the standard
chart of the restriction of `a` to `W`. -/
theorem mem_range_chartι_res (a : (alg E).grading U 1) (p : (bun E).scheme)
    (hp : p ∈ Set.range (chartι E hU a)) (hpW : (bun E).toBase p ∈ W) :
    p ∈ Set.range (chartι E hW (resDeg1 E hWU a)) := by
  have := isOpenImmersion_chart E hU
  obtain ⟨q', -, rfl⟩ : p ∈ (bun E).chart W hW ''ᵁ ⊤ := by
    rw [Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top]
    exact hpW
  obtain ⟨q, hq⟩ := hp
  have hq' : Proj.map ((alg E).res hWU) (irrelevant_le_map_res E hU hW hWU) q' =
      Proj.awayι ((alg E).grading U) (a : (alg E).sectionRing U) a.2 Nat.one_pos q := by
    apply ((bun E).chart U hU).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← chart_res E hU hW hWU]
    exact hq.symm
  have hmem : q' ∈ Proj.map ((alg E).res hWU) (irrelevant_le_map_res E hU hW hWU) ⁻¹ᵁ
      Proj.basicOpen ((alg E).grading U) (a : (alg E).sectionRing U) := by
    change Proj.map _ _ q' ∈ Proj.basicOpen ((alg E).grading U) (a : (alg E).sectionRing U)
    rw [hq', ← Proj.opensRange_awayι _ _ a.2 Nat.one_pos]
    exact ⟨q, rfl⟩
  rw [Proj.map_preimage_basicOpen, ← Proj.opensRange_awayι _ _ (resDeg1 E hWU a).2
    Nat.one_pos] at hmem
  obtain ⟨q'', rfl⟩ := hmem
  exact ⟨q'', rfl⟩

end RangeRes

section Glue

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

variable (H G : X.Modules) [H.IsQuasicoherent] [G.IsQuasicoherent]

/-- A point of a piece lying over a smaller affine open lies in the restricted piece. -/
theorem mem_range_pieceMap_res {U W : X.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (hWU : W ≤ U) (a : (alg H).grading U 1) (b : (alg G).grading U 1)
    (z : (pullback (bun H).toBase (bun G).toBase : Scheme.{u}))
    (hz : z ∈ Set.range (pieceMap H G hU a b))
    (hzW : (bun H).toBase (pullback.fst (bun H).toBase (bun G).toBase z) ∈ W) :
    z ∈ Set.range (pieceMap H G hW (resDeg1 H hWU a) (resDeg1 G hWU b)) := by
  rw [range_pieceMap] at hz ⊢
  refine ⟨mem_range_chartι_res H hU hW hWU a _ hz.1 hzW,
    mem_range_chartι_res G hU hW hWU b _ hz.2 ?_⟩
  rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  exact hzW

/-- A point of a piece lies over the affine open of the piece. -/
private theorem toBase_fst_mem_of_mem_range_pieceMap {U : X.Opens} (hU : IsAffineOpen U)
    (a : (alg H).grading U 1) (b : (alg G).grading U 1)
    (z : (pullback (bun H).toBase (bun G).toBase : Scheme.{u}))
    (hz : z ∈ Set.range (pieceMap H G hU a b)) :
    (bun H).toBase (pullback.fst (bun H).toBase (bun G).toBase z) ∈ U := by
  obtain ⟨y, rfl⟩ := hz
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pieceMap_fst_assoc, chartι_toBase,
    Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact hU.range_fromSpec.subset ⟨_, rfl⟩

/-- Compatibility of the Segre morphism of a piece with that of its restriction, for a morphism
factoring through the restricted piece. -/
private theorem comp_pieceSegre_eq_lift_comp {T T' : Scheme.{u}} (j : PieceIndex H G)
    {D : X.Opens} (hD : IsAffineOpen D) (hDj : D ≤ j.U) (f : T' ⟶ T)
    (s : T ⟶ Spec (CommRingCat.of (pieceRing H G j.a j.b)))
    (r : Set.range (f ≫ s ≫ pieceMap H G j.hU j.a j.b) ⊆
      Set.range (pieceMap H G hD (resDeg1 H hDj j.a) (resDeg1 G hDj j.b))) :
    f ≫ s ≫ pieceSegre H G j.hU j.a j.b =
      IsOpenImmersion.lift _ _ r ≫
        pieceSegre H G hD (resDeg1 H hDj j.a) (resDeg1 G hDj j.b) := by
  rw [← Category.assoc]
  refine pieceSegre_compat_res H G j.hU hD hDj j.a j.b _ _ ?_
  rw [IsOpenImmersion.lift_fac, Category.assoc]

/-- **The Segre morphisms of any two pieces agree on their overlap.** -/
theorem pieceSegre_compat (i k : PieceIndex H G) {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of (pieceRing H G i.a i.b)))
    (s' : T ⟶ Spec (CommRingCat.of (pieceRing H G k.a k.b)))
    (hs : s ≫ pieceMap H G i.hU i.a i.b = s' ≫ pieceMap H G k.hU k.a k.b) :
    s ≫ pieceSegre H G i.hU i.a i.b = s' ≫ pieceSegre H G k.hU k.a k.b := by
  set w := s ≫ pieceMap H G i.hU i.a i.b with hw
  have hD : ∀ t : T, ∃ D : X.Opens, IsAffineOpen D ∧ D ≤ i.U ∧ D ≤ k.U ∧
      (bun H).toBase (pullback.fst (bun H).toBase (bun G).toBase (w t)) ∈ D := by
    intro t
    have hi := toBase_fst_mem_of_mem_range_pieceMap H G i.hU i.a i.b (w t) ⟨s t, rfl⟩
    have hk := toBase_fst_mem_of_mem_range_pieceMap H G k.hU k.a k.b (w t) ⟨s' t, by rw [hs]; rfl⟩
    obtain ⟨D, hDaff, hxD, hDle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X.isBasis_affineOpens (show _ ∈ i.U ⊓ k.U from ⟨hi, hk⟩)
    exact ⟨D, hDaff, hDle.trans inf_le_left, hDle.trans inf_le_right, hxD⟩
  choose D hDaff hDi hDk hxD using hD
  let O : T → T.Opens := fun t => w ⁻¹ᵁ
    ((pieceMap H G (hDaff t) (resDeg1 H (hDi t) i.a) (resDeg1 G (hDi t) i.b)).opensRange ⊓
      (pieceMap H G (hDaff t) (resDeg1 H (hDk t) k.a) (resDeg1 G (hDk t) k.b)).opensRange)
  have hO : TopologicalSpace.IsOpenCover O := by
    refine eq_top_iff.mpr fun t _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨t, ?_⟩
    refine ⟨mem_range_pieceMap_res H G i.hU (hDaff t) (hDi t) i.a i.b (w t) ⟨s t, rfl⟩ (hxD t),
      mem_range_pieceMap_res H G k.hU (hDaff t) (hDk t) k.a k.b (w t) ?_ (hxD t)⟩
    rw [hs]
    exact ⟨s' t, rfl⟩
  refine (T.openCoverOfIsOpenCover O hO).hom_ext _ _ fun t => ?_
  change (O t).ι ≫ _ = (O t).ι ≫ _
  have hr₁ : Set.range ((O t).ι ≫ s ≫ pieceMap H G i.hU i.a i.b) ⊆
      Set.range (pieceMap H G (hDaff t) (resDeg1 H (hDi t) i.a) (resDeg1 G (hDi t) i.b)) := by
    rintro _ ⟨y, rfl⟩
    exact (show (O t).ι y ∈ O t from y.2).1
  have hr₂ : Set.range ((O t).ι ≫ s' ≫ pieceMap H G k.hU k.a k.b) ⊆
      Set.range (pieceMap H G (hDaff t) (resDeg1 H (hDk t) k.a) (resDeg1 G (hDk t) k.b)) := by
    rw [← hs]
    rintro _ ⟨y, rfl⟩
    exact (show (O t).ι y ∈ O t from y.2).2
  rw [comp_pieceSegre_eq_lift_comp H G i (hDaff t) (hDi t) _ s hr₁,
    comp_pieceSegre_eq_lift_comp H G k (hDaff t) (hDk t) _ s' hr₂]
  refine pieceSegre_compat_sameBase H G (hDaff t) _ _ _ _ _ _ ?_
  rw [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, ← hs]

/-- **The relative Segre morphism** `𝐏(H) ×_X 𝐏(G) ⟶ 𝐏(H ⊗ G)`, glued from the Segre morphisms of
the affine pieces `D₊(a) ×_U D₊(b)`. -/
def segre : pullback (bun H).toBase (bun G).toBase ⟶ (bun (tens H G)).scheme :=
  (pieceCover H G).glueMorphisms (fun i => pieceSegre H G i.hU i.a i.b) fun i k =>
    pieceSegre_compat H G i k _ _ pullback.condition

/-- On a piece, the relative Segre morphism is the Segre morphism of the piece. -/
@[reassoc]
theorem pieceMap_segre (i : PieceIndex H G) :
    pieceMap H G i.hU i.a i.b ≫ segre H G = pieceSegre H G i.hU i.a i.b :=
  (pieceCover H G).ι_glueMorphisms _ _ i

end Glue

end Stacks.RelativeSegre

end
