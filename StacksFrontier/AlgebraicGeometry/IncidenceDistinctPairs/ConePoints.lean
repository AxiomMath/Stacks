module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.ConverseCollinear
public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.IncidenceDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closed points of the projection cone come from the incidence variety

Tag 0B1R bounds the dimension of the part of `Y ∩ r_p^{-1}(r_p(Z))` away from `Z` by exhibiting it
inside the image of the fibre of the incidence variety over `p`. This file supplies that
inclusion at the closed points, which is where it can be checked: a closed point of
`r_p^{-1}(r_p(Z))` lies on a line joining `p` to a *closed* point of `Z`, and a triple of closed
points on a line is a point of the incidence variety.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_of_projection_eq`: **a closed
  point with the same image as a point of `Z` under the projection away from `p` is collinear
  with `p` and a *closed* point of `Z`.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.pointSubmodule_inf_le_of_inf_le`: collinearity of
  three distinct closed points does not depend on which of them is singled out.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_mem_incidenceVariety`: **a collinear triple
  of closed points with the first in `Y ∖ Z` and the second in `Z` is the image of a point of the
  incidence variety over the distinct pairs.**

## Implementation notes

The closed point of `Z` is produced from an arbitrary one by specialization. A point `z` of `Z`
with `r_p(z) = r_p(x)` need not be closed, and the *linear-algebra* form of collinearity does not
pass to specializations of `z`; the *projection* form does, because the image of a closed point
of the domain under `r_p` is closed — that is
`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_projection` applied to the singleton
`{x}`, which is disjoint from the centre since `x ≠ p`. So a closed point in the closure of `z`,
which exists because `𝐏(V)` is a Jacobson space, still has the same image under `r_p` as `x`, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_linearSubspace_inf_of_projection_eq` turns that
back into the linear-algebra form.

The point of the incidence variety is assembled from rational points. Over an algebraically
closed field a closed point of a scheme of finite type is the image of a section of the structure
morphism (`AlgebraicGeometry.pointOfClosedPoint`), so the pair `(x, z)` and the triple
`(x, z, p)` are images of morphisms out of `Spec k` built by `pullback.lift`; no point of a fibre
product has to be produced by hand except at the last step, where
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback` lifts the pair consisting of the
collinear triple and the point of the base.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### A closed point of `Z` on the line -/

/-- A point of the domain of the projection away from a closed point `p` that specializes from a
point of the fibre through a closed point `x ≠ p` lies in that fibre. -/
private theorem projection_eq_of_mem_closure [IsAlgClosed k] [Module.Finite k V] [Nontrivial V]
    {p x : projectiveSpaceOfModule k V}
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hxc : IsClosed ({x} : Set (projectiveSpaceOfModule k V))) (hxp : x ≠ p)
    [Nontrivial ↥(pointSubmodule k V p)]
    {x' z' w : (projectionDomain k V (pointSubmodule k V p)).toScheme}
    (hx'eq : (projectionDomain k V (pointSubmodule k V p)).ι.base x' = x)
    (hz'proj : (projection k V (pointSubmodule k V p)).base z' =
      (projection k V (pointSubmodule k V p)).base x')
    (hw : w ∈ closure ({z'} : Set (projectionDomain k V (pointSubmodule k V p)).toScheme)) :
    (projection k V (pointSubmodule k V p)).base w =
      (projection k V (pointSubmodule k V p)).base x' := by
  have hdisj : Disjoint ({x} : Set (projectiveSpaceOfModule k V))
      (linearSubspace k V (pointSubmodule k V p)) := by
    rw [linearSubspace_pointSubmodule k V p hpc]
    exact Set.disjoint_singleton.mpr hxp
  have hsing : (projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹'
      ({x} : Set (projectiveSpaceOfModule k V)) = {x'} := by
    refine Set.Subset.antisymm (fun y hy => Set.mem_singleton_iff.mpr ?_)
      (Set.singleton_subset_iff.mpr hx'eq)
    exact (projectionDomain k V (pointSubmodule k V p)).ι.isOpenEmbedding.injective
      (hy.trans hx'eq.symm)
  have hclosedim := isClosed_image_projection k V (pointSubmodule k V p) hxc hdisj
  rw [hsing, Set.image_singleton] at hclosedim
  have hprojcl := image_closure_subset_closure_image
    (f := (projection k V (pointSubmodule k V p)).base)
    (Scheme.Hom.continuous (projection k V (pointSubmodule k V p)))
    (s := ({z'} : Set (projectionDomain k V (pointSubmodule k V p)).toScheme))
  rw [Set.image_singleton] at hprojcl
  have h := hprojcl ⟨w, hw, rfl⟩
  rwa [hz'proj, hclosedim.closure_eq, Set.mem_singleton_iff] at h

/-- **A closed point of the projection cone through `Z` is collinear with `p` and a closed point
of `Z`.** -/
public theorem exists_isClosed_of_projection_eq [IsAlgClosed k] [Module.Finite k V]
    [Nontrivial V] {p x : projectiveSpaceOfModule k V}
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hxc : IsClosed ({x} : Set (projectiveSpaceOfModule k V))) (hxp : x ≠ p)
    (hWnt : Nontrivial ↥(pointSubmodule k V p))
    {Z : Set (projectiveSpaceOfModule k V)} (hZ : IsClosed Z) (hpZ : p ∉ Z)
    {x' z' : (projectionDomain k V (pointSubmodule k V p)).toScheme}
    (hx'eq : (projectionDomain k V (pointSubmodule k V p)).ι.base x' = x)
    (hz'Z : z' ∈ (projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹' Z)
    (hz'proj : (projection k V (pointSubmodule k V p)).base z' =
      (projection k V (pointSubmodule k V p)).base x') :
    ∃ z ∈ Z, IsClosed ({z} : Set (projectiveSpaceOfModule k V)) ∧
      pointSubmodule k V p ⊓ pointSubmodule k V z ≤ pointSubmodule k V x := by
  have := hWnt
  have : JacobsonSpace (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k V)
  obtain ⟨z₀, hz₀cl, hz₀c⟩ :=
    nonempty_inter_closedPoints (X := projectiveSpaceOfModule k V)
      ⟨(projectionDomain k V (pointSubmodule k V p)).ι.base z',
        subset_closure (Set.mem_singleton _)⟩ isClosed_closure.isLocallyClosed
  have hz₀Z : z₀ ∈ Z :=
    (hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz'Z)) hz₀cl
  have hz₀p : z₀ ≠ p := fun h => hpZ (h ▸ hz₀Z)
  obtain ⟨z₀', hz₀'⟩ : z₀ ∈ Set.range (projectionDomain k V (pointSubmodule k V p)).ι.base := by
    rw [Scheme.Opens.range_ι, coe_mapDomain_pointSubmodule k V p hpc]
    exact hz₀p
  have hz₀closure : z₀' ∈ closure ({z'} :
      Set (projectionDomain k V (pointSubmodule k V p)).toScheme) := by
    rw [((projectionDomain k V (pointSubmodule k V p)).ι.isOpenEmbedding.isInducing
      ).closure_eq_preimage_closure_image
      ({z'} : Set (projectionDomain k V (pointSubmodule k V p)).toScheme),
      Set.image_singleton, Set.mem_preimage, hz₀']
    exact hz₀cl
  refine ⟨z₀, hz₀Z, hz₀c, ?_⟩
  have hmem := mem_linearSubspace_inf_of_projection_eq k V (pointSubmodule k V p) x' z₀'
    (projection_eq_of_mem_closure k V hpc hxc hxp hx'eq hz'proj hz₀closure).symm
  rw [mem_linearSubspace_iff] at hmem
  have hx'v : (x'.val : projectiveSpaceOfModule k V) = x := hx'eq
  have hz₀v : (z₀'.val : projectiveSpaceOfModule k V) = z₀ := hz₀'
  rw [hx'v, hz₀v] at hmem
  exact hmem

/-! ### Collinearity of three closed points is symmetric -/

/-- Two submodules of the same corank, one inside the other, are equal. -/
private theorem eq_of_le_of_finrank_quotient_eq [FiniteDimensional k V]
    {P Q : Submodule k V} {d : ℕ} (hP : Module.finrank k (V ⧸ P) = d)
    (hQ : Module.finrank k (V ⧸ Q) = d) (hle : P ≤ Q) : P = Q := by
  have h1 := P.finrank_quotient_add_finrank
  have h2 := Q.finrank_quotient_add_finrank
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

/-- **Collinearity of three distinct closed points does not depend on which of them is singled
out.** The degree-one forms vanishing at two distinct closed points have corank two, so the
three such submodules attached to the three pairs of a collinear triple coincide. -/
@[sga "7 XVII 2.1" "partial"]
public theorem pointSubmodule_inf_le_of_inf_le [IsAlgClosed k] [Module.Finite k V]
    {p x z : projectiveSpaceOfModule k V}
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hxc : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (hzc : IsClosed ({z} : Set (projectiveSpaceOfModule k V)))
    (hpz : p ≠ z) (hxz : x ≠ z)
    (hle : pointSubmodule k V p ⊓ pointSubmodule k V z ≤ pointSubmodule k V x) :
    pointSubmodule k V x ⊓ pointSubmodule k V z ≤ pointSubmodule k V p := by
  have h0 : Module.finrank k (V ⧸ (pointSubmodule k V p ⊓ pointSubmodule k V z)) = 2 :=
    finrank_quotient_lineSubmodule k V hpc hzc hpz
  have h1 : Module.finrank k (V ⧸ (pointSubmodule k V x ⊓ pointSubmodule k V z)) = 2 :=
    finrank_quotient_lineSubmodule k V hxc hzc hxz
  rw [← eq_of_le_of_finrank_quotient_eq k V h0 h1 (le_inf hle inf_le_right)]
  exact inf_le_left

/-- The first projection of a lifted point into a fibre product is the first component. -/
private theorem pullback_fst_base_lift {X Y Z W : Scheme} {f : X ⟶ Z} {g : Y ⟶ Z}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) (w : W) :
    (pullback.fst f g).base ((pullback.lift a b h).base w) = a.base w := by
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst]

/-- The second projection of a lifted point into a fibre product is the second component. -/
private theorem pullback_snd_base_lift {X Y Z W : Scheme} {f : X ⟶ Z} {g : Y ⟶ Z}
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) (w : W) :
    (pullback.snd f g).base ((pullback.lift a b h).base w) = b.base w := by
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]

/-- A rational point of `𝐏(V) ×_k 𝐏(V)` and a closed point `p` of `𝐏(V)` give a point of the
triple product over both. -/
private theorem exists_prFst_eq_and_pr₃_eq [IsAlgClosed k] [Module.Finite k V] [Nontrivial V]
    {p : projectiveSpaceOfModule k V} (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (σ : Spec (CommRingCat.of k) ⟶ prodTwo k V) (hσ : σ ≫ prodTwoToSpec k V = 𝟙 _)
    (a : Spec (CommRingCat.of k)) :
    ∃ t : prodThree k V, (prFst k V).base t = σ.base a ∧ (pr₃ k V).base t = p := by
  have hcond : σ ≫ prodTwoToSpec k V =
      pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) p hpc ≫
        projectiveSpaceOfModuleToSpec k V := by
    rw [hσ, pointOfClosedPoint_comp]
  refine ⟨(pullback.lift σ _ hcond).base a, ?_, ?_⟩
  · exact pullback_fst_base_lift σ _ hcond a
  · exact (pullback_snd_base_lift σ _ hcond a).trans (pointOfClosedPoint_apply _ p hpc a)

/-! ### A collinear triple of closed points is a point of the incidence variety -/

variable (Y Z : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y) (hZ : IsClosed Z)

/-- The map from `Y ×_k Z` to `𝐏(V) ×_k 𝐏(V)` lies over `Spec k` through the first factor. -/
private theorem prodOfClosedToProdTwo_comp_prodTwoToSpec :
    prodOfClosedToProdTwo k V Y Z hY hZ ≫ prodTwoToSpec k V =
      pullback.fst (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ) ≫
        closedSubschemeOfToSpec k V Y hY := by
  have hmapfst : prodOfClosedToProdTwo k V Y Z hY hZ ≫
      pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) =
      pullback.fst (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ) ≫
        closedSubschemeOfι k V Y hY := pullback.lift_fst _ _ _
  rw [prodTwoToSpec, ← Category.assoc, hmapfst]
  exact Category.assoc _ _ _

/-- A pair of closed points, the first in `Y ∖ Z` and the second in `Z`, is a rational point of the
distinct pairs. -/
private theorem exists_prodOfClosedOffSnd_of_isClosed [IsAlgClosed k] [Module.Finite k V]
    [Nontrivial V] {x z : projectiveSpaceOfModule k V}
    (hxc : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (hzc : IsClosed ({z} : Set (projectiveSpaceOfModule k V)))
    (hxY : x ∈ Y) (hxZ : x ∉ Z) (hzZ : z ∈ Z) :
    ∃ b : (prodOfClosedOffSnd k V Y Z hY hZ).toScheme,
      (pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V)).base
        ((prodOfClosedOffSndToProdTwo k V Y Z hY hZ).base b) = x ∧
      (pullback.snd (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V)).base
        ((prodOfClosedOffSndToProdTwo k V Y Z hY hZ).base b) = z ∧
      ∃ σ : Spec (CommRingCat.of k) ⟶ prodTwo k V, σ ≫ prodTwoToSpec k V = 𝟙 _ ∧
        ∃ a, σ.base a = (prodOfClosedOffSndToProdTwo k V Y Z hY hZ).base b := by
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V Y hY
  have := locallyOfFiniteType_closedSubschemeOfToSpec k V Z hZ
  obtain ⟨x₁, hx₁, hx₁c⟩ := exists_isClosed_closedSubschemeOf k V Y hY hxc hxY
  obtain ⟨z₁, hz₁, hz₁c⟩ := exists_isClosed_closedSubschemeOf k V Z hZ hzc hzZ
  set σx := pointOfClosedPoint (closedSubschemeOfToSpec k V Y hY) x₁ hx₁c with hσx
  set σz := pointOfClosedPoint (closedSubschemeOfToSpec k V Z hZ) z₁ hz₁c with hσz
  have hσ : σx ≫ closedSubschemeOfToSpec k V Y hY = σz ≫ closedSubschemeOfToSpec k V Z hZ := by
    rw [hσx, hσz, pointOfClosedPoint_comp, pointOfClosedPoint_comp]
  set s : Spec (CommRingCat.of k) ⟶ prodOfClosed k V Y Z hY hZ := pullback.lift σx σz hσ
  obtain ⟨a⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨IsLocalRing.closedPoint k⟩
  have hsfst : (pullback.fst (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ)).base (s.base a) = x₁ :=
    (pullback_fst_base_lift σx σz hσ a).trans (pointOfClosedPoint_apply _ x₁ hx₁c a)
  have hssnd : (pullback.snd (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ)).base (s.base a) = z₁ :=
    (pullback_snd_base_lift σx σz hσ a).trans (pointOfClosedPoint_apply _ z₁ hz₁c a)
  have hmemopen : s.base a ∈ prodOfClosedOffSnd k V Y Z hY hZ := by
    have h : (s.base a ∈ prodOfClosedOffSnd k V Y Z hY hZ) =
        ((closedSubschemeOfι k V Y hY).base ((pullback.fst
          (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ)).base
            (s.base a)) ∈ Zᶜ) := rfl
    rw [h, hsfst, hx₁]
    exact hxZ
  have hfb : (prodOfClosedOffSndToProdTwo k V Y Z hY hZ).base ⟨s.base a, hmemopen⟩ =
      (prodOfClosedToProdTwo k V Y Z hY hZ).base (s.base a) := rfl
  have hsx : s ≫ pullback.fst (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ) = σx := pullback.lift_fst _ _ _
  refine ⟨⟨s.base a, hmemopen⟩, by rw [hfb, fst_prodOfClosedToProdTwo, hsfst, hx₁],
    by rw [hfb, snd_prodOfClosedToProdTwo, hssnd, hz₁],
    s ≫ prodOfClosedToProdTwo k V Y Z hY hZ, ?_, a, rfl⟩
  rw [Category.assoc, prodOfClosedToProdTwo_comp_prodTwoToSpec]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ closedSubschemeOfToSpec k V Y hY) hsx)).trans (pointOfClosedPoint_comp _ _ _)

/-- **A collinear triple of closed points with the first in `Y ∖ Z` and the second in `Z` comes
from a point of the incidence variety over the distinct pairs**, which lies over `p` and whose
first base coordinate is the first point. -/
public theorem exists_mem_incidenceVariety [IsAlgClosed k] [Module.Finite k V] [Nontrivial V]
    {x z p : projectiveSpaceOfModule k V}
    (hxc : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (hzc : IsClosed ({z} : Set (projectiveSpaceOfModule k V)))
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hxY : x ∈ Y) (hxZ : x ∉ Z) (hzZ : z ∈ Z)
    (hle : pointSubmodule k V x ⊓ pointSubmodule k V z ≤ pointSubmodule k V p) :
    ∃ τ : incidenceVariety k V (prodOfClosedOffSndToProdTwo k V Y Z hY hZ),
      (incidenceVarietyToProj k V (prodOfClosedOffSndToProdTwo k V Y Z hY hZ)).base τ = p ∧
        (pullback.fst (projectiveSpaceOfModuleToSpec k V)
            (projectiveSpaceOfModuleToSpec k V)).base
          ((prodOfClosedOffSndToProdTwo k V Y Z hY hZ).base
            ((incidenceVarietyToBase k V
              (prodOfClosedOffSndToProdTwo k V Y Z hY hZ)).base τ)) = x := by
  obtain ⟨b, hfstx, hsndz, σ, hσ, a, ha⟩ :=
    exists_prodOfClosedOffSnd_of_isClosed k V Y Z hY hZ hxc hzc hxY hxZ hzZ
  obtain ⟨t, hprFst, hpr₃⟩ := exists_prFst_eq_and_pr₃_eq k V hpc σ hσ a
  rw [ha] at hprFst
  set f := prodOfClosedOffSndToProdTwo k V Y Z hY hZ
  have hpr₁ : (pr₁ k V).base t = x := by
    have h : (pr₁ k V).base t = (pullback.fst (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V)).base ((prFst k V).base t) := rfl
    rw [h, hprFst, hfstx]
  have hpr₂ : (pr₂ k V).base t = z := by
    have h : (pr₂ k V).base t = (pullback.snd (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V)).base ((prFst k V).base t) := rfl
    rw [h, hprFst, hsndz]
  have hxz : x ≠ z := fun h => hxZ (h ▸ hzZ)
  have hcol : t ∈ collinearLocus k V := by
    refine mem_collinearLocus_of_isClosed k V (hpr₁ ▸ hxc) (hpr₂ ▸ hzc) ?_ ?_
    · rwa [hpr₁, hpr₂]
    · rwa [hpr₁, hpr₂, hpr₃]
  obtain ⟨c, hc⟩ : t ∈ Set.range (collinearSubschemeι k V).base :=
    (range_collinearSubschemeι k V).symm ▸ hcol
  have hcproj : (collinearProj k V).base c = f.base b := by
    change (prFst k V).base ((collinearSubschemeι k V).base c) = f.base b
    rw [hc, hprFst]
  obtain ⟨τ, hτfst, hτsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := collinearProj k V) (g := f) c b hcproj
  refine ⟨τ, ?_, ?_⟩
  · have h1 : (incidenceVarietyToProj k V f).base τ =
        (collinearProj₃ k V).base ((pullback.fst (collinearProj k V) f).base τ) := rfl
    have h2 : (collinearProj₃ k V).base c = (pr₃ k V).base
        ((collinearSubschemeι k V).base c) := rfl
    rw [h1, hτfst, h2, hc, hpr₃]
  · have h3 : (pullback.fst (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V)).base
          (f.base ((incidenceVarietyToBase k V f).base τ)) =
        (pullback.fst (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base
          (f.base ((pullback.snd (collinearProj k V) f).base τ)) := rfl
    rw [h3, hτsnd, hfstx]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
