module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowPrimeCycleTransverse
public import StacksFrontier.AlgebraicGeometry.Intersection.ComputingIntersectionMultiplicities.CohenMacaulayCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.ExteriorProductIntersection
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma
public import StacksFrontier.AlgebraicGeometry.Intersection.ProductTorIndependence
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackCycles
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaWhole
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ClosedImmersionIdealSheaves

/-!
# Intersecting a closed subvariety with a flat pullback

Let `P` be a nonsingular variety over an algebraically closed field, let `s : X ⟶ P` be a closed
immersion of a variety and let `p : P ⟶ T` be a flat morphism to a variety such that `s ≫ p` is
flat as well. For a closed subscheme `Z ⊆ T` the closed subschemes `p⁻¹(Z)` and `s(X)` of `P` are
Tor independent, so their intersection product is the cycle of their scheme theoretic
intersection, which is `s((s ≫ p)⁻¹(Z))`:

`p^*[Z] · [X] = s_*((s ≫ p)^*[Z])`.

This is the computation behind Section 43.23 of the source (Tag 0B0H): for the graph
`Γ_f ⊆ X × Y` of a morphism `f : X ⟶ Y` it gives `pr_X^*(α) · [Γ_f] = s_*(α)` for every cycle
`α` on `X` (the source's "remark on graphs" in the proof of Tag 0B2X) and, when `f` is flat,
`pr_Y^*(β) · [Γ_f] = s_*(f^*β)` (the computation of part (4) of Tag 0B2X).

## Main definitions

* `Stacks.Intersection.ChowRing.graph`: the graph morphism `X ⟶ X ×_k Y` of `f : X ⟶ Y`.

## Main results

* `Stacks.Intersection.ChowRing.torIndependent_comap_ker`: Tor independence of `p⁻¹(Z)` and
  `s(X)`.
* `Stacks.Intersection.ChowRing.cycleAssociatedToClosedSubscheme_comap_sup_ker`: the cycle of
  their scheme theoretic intersection is `s_*` of the cycle of `(s ≫ p)⁻¹(Z)`.
* `Stacks.Intersection.ChowRing.torFormulaCycleIntersectionProduct_comap_closedImmersion`: the
  identity `[p⁻¹(Z)] · [X] = s_*[(s ≫ p)⁻¹(Z)]` of cycles on `P`.
* `Stacks.Intersection.ChowRing.torFormulaCycleIntersectionProduct_flatPullback_closedImmersion`
  and `Stacks.Intersection.ChowRing.intersectProperly_flatPullback_closedImmersion`: the same for
  the flat pullback `p^*(w)` of an arbitrary cycle, which moreover meets `[X]` properly.

## References

* [Stacks Project, Tag 0B0H](https://stacks.math.columbia.edu/tag/0B0H)
* [Stacks Project, Tag 0B2X](https://stacks.math.columbia.edu/tag/0B2X)
* [Stacks Project, Tag 0CTA](https://stacks.math.columbia.edu/tag/0CTA)
* [Stacks Project, Tag 0B0W](https://stacks.math.columbia.edu/tag/0B0W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.ChowRing

/-! ### The closed subscheme cut out by a closed immersion -/

section ClosedImmersion

variable {X P T : Scheme.{u}} (s : X ⟶ P) [IsClosedImmersion s]

/-- A closed immersion is the closed immersion of the closed subscheme cut out by its kernel,
followed by an isomorphism. -/
theorem inv_toImage_comp (s : X ⟶ P) [IsClosedImmersion s] :
    inv s.toImage ≫ s = s.ker.subschemeι := by
  rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]

/-- **Stacks 0CTA for a closed immersion.** Let `p : P ⟶ T` be flat and let `s : X ⟶ P` be a
closed immersion such that `s ≫ p` is flat. For every ideal sheaf `I` on `T` the closed
subschemes `p⁻¹(V(I))` and `s(X)` of `P` are Tor independent. -/
theorem torIndependent_comap_ker (p : P ⟶ T) [Flat p] [Flat (s ≫ p)] (I : T.IdealSheafData) :
    TorIndependent (I.comap p).subschemeι s.ker.subschemeι := by
  have : Flat (s.ker.subschemeι ≫ p) := by
    rw [← inv_toImage_comp s, Category.assoc]
    infer_instance
  simpa only [Scheme.IdealSheafData.comapIso_hom_fst] using TorIndependent.iso_left
    (I.comapIso p) (torIndependent_pullback_fst_of_flat I.subschemeι p s.ker.subschemeι)

omit [IsClosedImmersion s] in
/-- The inverse image `p⁻¹(V(I))` pulled back along the closed immersion `s` is
`(s ≫ p)⁻¹(V(I))`. -/
theorem comap_comap_eq (p : P ⟶ T) (I : T.IdealSheafData) :
    (I.comap p).comap s = I.comap (s ≫ p) := by
  rw [Scheme.IdealSheafData.comap_comp]

/-- **The scheme theoretic intersection of `p⁻¹(V(I))` with `s(X)` is `s((s ≫ p)⁻¹(V(I)))`.**
The closed subscheme of `P` cut out by `(p⁻¹ I) ⊔ ker s` is isomorphic over `P` to the closed
subscheme `(s ≫ p)⁻¹(V(I))` of `X` followed by `s`. -/
theorem exists_iso_comap_sup_ker (p : P ⟶ T) (I : T.IdealSheafData) :
    ∃ e : (I.comap (s ≫ p)).subscheme ≅ ((I.comap p) ⊔ s.ker).subscheme,
      e.hom ≫ ((I.comap p) ⊔ s.ker).subschemeι = (I.comap (s ≫ p)).subschemeι ≫ s := by
  set W := I.comap p with hW
  set J := s.ker with hJ
  have hWs : W.comap s = I.comap (s ≫ p) := comap_comap_eq s p I
  let a : (I.comap (s ≫ p)).subscheme ⟶ W.subscheme :=
    Scheme.IdealSheafData.subschemeMap _ W s (by
      rw [← hWs]; exact W.le_map_comap s)
  have ha : a ≫ W.subschemeι = (I.comap (s ≫ p)).subschemeι ≫ s :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have hpb₁ : IsPullback (I.comap (s ≫ p)).subschemeι a s W.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ ha.symm (by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι, hWs])
  have hpb₂ : IsPullback ((I.comap (s ≫ p)).subschemeι ≫ s.toImage) a J.subschemeι
      W.subschemeι :=
    hpb₁.of_iso (Iso.refl _) (asIso s.toImage) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp only [Iso.refl_hom, Category.comp_id, asIso_hom]
          exact (Scheme.Hom.toImage_imageι s).symm) (by simp)
  have hpb₃ := (Scheme.IdealSheafData.isPullback_subscheme_sup P W J).flip
  refine ⟨hpb₂.isoIsPullback _ _ hpb₃, ?_⟩
  rw [← Scheme.IdealSheafData.inclusion_subschemeι (le_sup_right : J ≤ W ⊔ J),
    IsPullback.isoIsPullback_hom_fst_assoc, Category.assoc]
  exact congrArg _ (Scheme.Hom.toImage_imageι s)

/-- The underlying space of a closed immersion has the same dimension as its range. -/
private theorem topologicalKrullDim_range_eq (s : X ⟶ P) [IsClosedImmersion s] :
    topologicalKrullDim (Set.range s.base) = topologicalKrullDim X := by
  rw [← Set.image_univ, topologicalKrullDim_image_eq_of_isEmbedding s.isClosedEmbedding.isEmbedding]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph

end ClosedImmersion

/-- Dimensions of `P` and `X` over a variety `T` differ by the relative dimensions. -/
private theorem dim_add_eq_of_relative_dim (K : Type u) [Field K] {X Y T : Scheme.{u}}
    (sT : T ⟶ Spec (.of K)) [IsVariety K sT] (dP dX ep eq : ℕ)
    (hdP : topologicalKrullDim Y = (dP : WithBot ℕ∞))
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hep : topologicalKrullDim Y = topologicalKrullDim T + (ep : WithBot ℕ∞))
    (heq : topologicalKrullDim X = topologicalKrullDim T + (eq : WithBot ℕ∞)) :
    dP + eq = dX + ep := by
  have h1 := hdP.symm.trans hep
  have h2 := hdX.symm.trans heq
  obtain ⟨dT, hdT⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety K sT
  rw [hdT] at h1 h2
  have h1' : dP = dT + ep := by exact_mod_cast h1
  have h2' : dX = dT + eq := by exact_mod_cast h2
  omega

/-- If a point of a variety has relative dimension `d`, then `d` is a natural number. -/
private theorem exists_natCast_of_relativeDimension_eq (K : Type u) [Field K] {T : Scheme.{u}}
    (sT : T ⟶ Spec (.of K)) [IsVariety K sT] (t : T) (d : ℤ)
    (h : relativeDimension (fieldChowSituation K).dimensionFunction sT t = d) :
    ∃ d' : ℕ, d = (d' : ℤ) :=
  ⟨d.toNat, by
    have := relativeDimension_nonneg (fieldChowSituation K) (fun _ _ => rfl) sT t
    omega⟩

/-! ### The intersection product with a flat pullback -/

section Transversal

variable (K : Type u) [Field K] [IsAlgClosed K] {X P T : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  (sP : P ⟶ Spec (.of K)) (sT : T ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sP]
  [IsVariety K sT] (s : X ⟶ P) [IsClosedImmersion s] (hs : s ≫ sP = sX)
  (p : P ⟶ T) [Flat p] (hp : p ≫ sT = sP)

omit [IsAlgClosed K] [IsVariety K sP] [Flat p] in
include hs sT hp in
/-- The image under the closed immersion `s` of `(s ≫ p)⁻¹(Z)` is the intersection of `s(X)`
with `p⁻¹(Z)`, and so has dimension at most `dim Z + e` when `s ≫ p` is flat of relative
dimension `e`. -/
theorem topologicalKrullDim_preimage_inter_range_le [Flat (s ≫ p)] (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim T + (e : WithBot ℕ∞))
    (Z : Closeds T) (d : ℕ) (hZ : topologicalKrullDim (Z : Set T) ≤ (d : WithBot ℕ∞)) :
    topologicalKrullDim ↥(p.base ⁻¹' (Z : Set T) ∩ Set.range s.base) ≤
      ((d + e : ℕ) : WithBot ℕ∞) := by
  have hq : (s ≫ p) ≫ sT = sX := by rw [Category.assoc, hp, hs]
  have himg : p.base ⁻¹' (Z : Set T) ∩ Set.range s.base =
      s.base '' ((s ≫ p).base ⁻¹' (Z : Set T)) :=
    (Set.image_preimage_eq_inter_range (f := s.base) (t := p.base ⁻¹' (Z : Set T))).symm
  rw [himg, topologicalKrullDim_image_eq_of_isEmbedding s.isClosedEmbedding.isEmbedding]
  exact Stacks.Intersection.CycleFlatPullback.topologicalKrullDim_preimage_le K sX sT (s ≫ p)
    hq e he Z d hZ

include sT hp in
/-- **The intersection product of a flat pullback with a closed subvariety.** Let `P` be a
nonsingular variety over an algebraically closed field `K`, let `s : X ⟶ P` be a closed
immersion of a variety of dimension `dX`, and let `p : P ⟶ T` be flat to a variety `T` with
`s ≫ p` flat; write `dim P = dim T + ep` and `dim X = dim T + eq`. For a closed subscheme `Z ⊆ T`
of dimension at most `d`,

`[p⁻¹(Z)]_{d + ep} · [X]_{dX} = s_*[(s ≫ p)⁻¹(Z)]_{d + eq}`

as cycles on `P`. -/
theorem torFormulaCycleIntersectionProduct_comap_closedImmersion (hP : IsRegular P)
    [Flat (s ≫ p)] (dP dX ep eq d : ℕ) (hdP : topologicalKrullDim P = (dP : WithBot ℕ∞))
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hep : topologicalKrullDim P = topologicalKrullDim T + (ep : WithBot ℕ∞))
    (heq : topologicalKrullDim X = topologicalKrullDim T + (eq : WithBot ℕ∞))
    (I : T.IdealSheafData) (hI : topologicalKrullDim (I.support : Set T) ≤ (d : WithBot ℕ∞)) :
    letI : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP ((d + eq : ℕ) : ℤ)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP (I.comap p).subschemeι
          ((d + ep : ℕ) : ℤ)).1
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP s (dX : ℤ)).1 =
      (properPushforward (fieldChowSituation K) sX sP s hs ((d + eq : ℕ) : ℤ)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sX
          (I.comap (s ≫ p)).subschemeι ((d + eq : ℕ) : ℤ))).1 := by
  have : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
  set W := I.comap p with hW
  set J := s.ker with hJ
  have hWsupp : (W.support : Set P) = p.base ⁻¹' (I.support : Set T) := by
    rw [hW, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  have hJsupp : (J.support : Set P) = Set.range s.base := by
    rw [hJ, Scheme.Hom.support_ker, s.isClosedEmbedding.isClosed_range.closure_eq]
  have hWd : topologicalKrullDim (W.support : Set P) ≤ ((d + ep : ℕ) : WithBot ℕ∞) := by
    rw [hWsupp]
    exact Stacks.Intersection.CycleFlatPullback.topologicalKrullDim_preimage_le K sP sT p hp ep
      hep I.support d hI
  have hJd : topologicalKrullDim (J.support : Set P) ≤ (dX : WithBot ℕ∞) := by
    rw [hJsupp, topologicalKrullDim_range_eq, hdX]
  have hWJd : topologicalKrullDim ↥((W.support : Set P) ∩ (J.support : Set P)) ≤
      ((d + eq : ℕ) : WithBot ℕ∞) := by
    rw [hWsupp, hJsupp]
    exact topologicalKrullDim_preimage_inter_range_le K sX sP sT s hs p hp eq heq I.support d hI
  have hrs : (d + ep) + dX = dP + (d + eq) := by
    have := dim_add_eq_of_relative_dim K sT dP dX ep eq hdP hdX hep heq
    omega
  have := isFiniteType_of_isCoherent (subschemeStructureSheaf W)
  have := isFiniteType_of_isCoherent (subschemeStructureSheaf J)
  have hFr : topologicalKrullDim (SheafOfModules.supp (subschemeStructureSheaf W) : Set P) ≤
      ((d + ep : ℕ) : WithBot ℕ∞) := by rw [supp_subschemeStructureSheaf]; exact hWd
  have hGs : topologicalKrullDim (SheafOfModules.supp (subschemeStructureSheaf J) : Set P) ≤
      (dX : WithBot ℕ∞) := by rw [supp_subschemeStructureSheaf]; exact hJd
  have hFG : topologicalKrullDim (SheafOfModules.supp (subschemeStructureSheaf W) ∩
      SheafOfModules.supp (subschemeStructureSheaf J) : Set P) ≤ ((d + eq : ℕ) : WithBot ℕ∞) := by
    rw [supp_subschemeStructureSheaf, supp_subschemeStructureSheaf]; exact hWJd
  obtain ⟨-, htor⟩ := Stacks.Intersection.ReductionToDiagonal.torFormula K sP hP
    (subschemeStructureSheaf W) (subschemeStructureSheaf J) (isCoherent_subschemeStructureSheaf W)
    (isCoherent_subschemeStructureSheaf J) (d + ep) dX (d + eq) dP hdP hrs hFr hGs hFG
  have hW' := congrArg Subtype.val
    (cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf (fieldChowSituation K)
      sP W.subschemeι ((d + ep : ℕ) : ℤ)
      (ExteriorProductProjections.schemeDeltaDimension_subschemeι_le K sP W (d + ep) hWd))
  have hJ' := congrArg Subtype.val
    (cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf (fieldChowSituation K)
      sP J.subschemeι (dX : ℤ)
      (ExteriorProductProjections.schemeDeltaDimension_subschemeι_le K sP J dX hJd))
  have hsJ : cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP s (dX : ℤ) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP J.subschemeι (dX : ℤ) :=
    cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation K) sP s J.subschemeι
      (asIso s.toImage) (Scheme.Hom.toImage_imageι s) _
  rw [hsJ, hW', hJ']
  refine htor.trans ?_
  have hCM := cycleAssociatedToClosedSubscheme_eq_intersectionProductCycle_of_tor_subsingleton
    (fieldChowSituation K) sP hP W J ((d + eq : ℕ) : ℤ) dP hdP.le
    (ExteriorProductProjections.schemeDeltaDimension_subschemeι_le K sP (W ⊔ J) (d + eq) (by
      rw [Scheme.IdealSheafData.support_sup, Closeds.coe_inf]; exact hWJd))
    (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation K) sP hP
      (subschemeStructureSheaf W) (subschemeStructureSheaf J)
      (isCoherent_subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf J)
      ((d + eq : ℕ) : ℤ) fun w hw => relativeDimension_le_of_topologicalKrullDim_le
        (fieldChowSituation K) (fun _ _ => rfl) sP ((SheafOfModules.isClosed_supp _).inter
          (SheafOfModules.isClosed_supp _)) hFG hw)
    (fun z _ hzW hzJ i hi => tor_subsingleton_stalk_of_torIndependent W J
      (torIndependent_comap_ker s p I) z hzW hzJ i hi)
  refine hCM.symm.trans ?_
  obtain ⟨e, he⟩ := exists_iso_comap_sup_ker s p I
  rw [← cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation K) sP
      ((I.comap (s ≫ p)).subschemeι ≫ s) (W ⊔ J).subschemeι e he,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]

include sT hp in
/-- **The intersection product of the flat pullback of a cycle with a closed subvariety.** In the
situation of `torFormulaCycleIntersectionProduct_comap_closedImmersion`, for every `d`-cycle `w`
on `T`,

`p^*(w) · [X] = s_*((s ≫ p)^*(w))`

as cycles on `P`, the products and pullbacks being graded by `d + ep`, `dX` and `d + eq`. -/
theorem torFormulaCycleIntersectionProduct_flatPullback_closedImmersion (hP : IsRegular P)
    [Flat (s ≫ p)] (dP dX ep eq : ℕ) (hdP : topologicalKrullDim P = (dP : WithBot ℕ∞))
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hep : topologicalKrullDim P = topologicalKrullDim T + (ep : WithBot ℕ∞))
    (heq : topologicalKrullDim X = topologicalKrullDim T + (eq : WithBot ℕ∞)) (d : ℤ)
    (w : CycleGroup (fieldChowSituation K) sT d) :
    letI : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
    letI : LocallyOfFiniteType p := locallyOfFiniteType_of_isVariety_comp K sP sT p hp
    letI : LocallyOfFiniteType (s ≫ p) := locallyOfFiniteType_of_isVariety_comp K sX sT (s ≫ p)
      (by rw [Category.assoc, hp, hs])
    torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP (d + (eq : ℤ))
        (flatPullback (fieldChowSituation K) sP sT p hp ep
          (relativeDimension_of_flat_of_isVariety K sP sT p hp ep hep) d w).1
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP s (dX : ℤ)).1 =
      (properPushforward (fieldChowSituation K) sX sP s hs (d + (eq : ℤ))
        (flatPullback (fieldChowSituation K) sX sT (s ≫ p) (by rw [Category.assoc, hp, hs]) eq
          (relativeDimension_of_flat_of_isVariety K sX sT (s ≫ p)
            (by rw [Category.assoc, hp, hs]) eq heq) d w)).1 := by
  classical
  let : IsLocallyNoetherian P := isLocallyNoetherian_of_isRegular hP
  let : LocallyOfFiniteType p := locallyOfFiniteType_of_isVariety_comp K sP sT p hp
  have hq : (s ≫ p) ≫ sT = sX := by rw [Category.assoc, hp, hs]
  let : LocallyOfFiniteType (s ≫ p) := locallyOfFiniteType_of_isVariety_comp K sX sT (s ≫ p) hq
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace sP
  set hrelp := relativeDimension_of_flat_of_isVariety K sP sT p hp ep hep
  set hrelq := relativeDimension_of_flat_of_isVariety K sX sT (s ≫ p) hq eq heq
  have hw : (Function.support w.1).Finite := finite_support_of_compactSpace w.1
  have hprime : ∀ v ∈ hw.toFinset,
      torFormulaCycleIntersectionProduct (fieldChowSituation K) sP hP (d + (eq : ℤ))
          (flatPullback (fieldChowSituation K) sP sT p hp ep hrelp d
            (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sT
              (integralComponentAt v).subschemeι d)).1
          (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP s (dX : ℤ)).1 =
        (properPushforward (fieldChowSituation K) sX sP s hs (d + (eq : ℤ))
          (flatPullback (fieldChowSituation K) sX sT (s ≫ p) hq eq hrelq d
            (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sT
              (integralComponentAt v).subschemeι d))).1 := by
    intro v hv
    have hvd : relativeDimension (fieldChowSituation K).dimensionFunction sT v = d :=
      (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) sT d w.1).1 w.2 v
        (hw.mem_toFinset.1 hv)
    obtain ⟨d', rfl⟩ := exists_natCast_of_relativeDimension_eq K sT v d hvd
    have hsupp : topologicalKrullDim ((integralComponentAt v).support : Set T) ≤
        (d' : WithBot ℕ∞) := by
      rw [coe_support_integralComponentAt,
        ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq K sT v d'
          hvd]
    have hδ := ExteriorProductProjections.schemeDeltaDimension_subschemeι_le K sT
      (integralComponentAt v) d' hsupp
    rw [flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le _ _ _ _ _ _ _ _ _ hδ,
      flatPullback_cycleAssociatedToClosedSubscheme_comap_of_le _ _ _ _ _ _ _ _ _ hδ]
    have h := torFormulaCycleIntersectionProduct_comap_closedImmersion K sX sP sT s hs p hp hP
      dP dX ep eq d' hdP hdX hep heq (integralComponentAt v) hsupp
    simp only [Nat.cast_add] at h
    exact h
  have hdecomp := cycle_eq_sum_zsmul_primeCycles w hw
  rw [hdecomp, map_sum, map_sum, ← properPushforwardHom_apply, map_sum]
  simp only [map_zsmul, AddSubgroup.val_finsetSum, AddSubgroup.coe_zsmul]
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct_sum_left]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [cycleIntersectionProduct_zsmul_left _ _ (finite_support_of_compactSpace _)
    (finite_support_of_compactSpace _), properPushforwardHom_apply]
  exact congrArg _ (hprime v hv)

omit [IsAlgClosed K] in
include sX hs sT hp in
/-- **The flat pullback of a cycle meets a closed subvariety properly** in the situation of
`torFormulaCycleIntersectionProduct_flatPullback_closedImmersion`: `p^*(w)` and `[X]` intersect
properly for every `d`-cycle `w` on `T`. -/
theorem intersectProperly_flatPullback_closedImmersion [Flat (s ≫ p)] (dP dX ep eq : ℕ)
    (hdP : topologicalKrullDim P = (dP : WithBot ℕ∞))
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hep : topologicalKrullDim P = topologicalKrullDim T + (ep : WithBot ℕ∞))
    (heq : topologicalKrullDim X = topologicalKrullDim T + (eq : WithBot ℕ∞)) (d : ℤ)
    (w : CycleGroup (fieldChowSituation K) sT d) :
    letI : LocallyOfFiniteType p := locallyOfFiniteType_of_isVariety_comp K sP sT p hp
    AlgebraicCycle.IntersectProperly
        (flatPullback (fieldChowSituation K) sP sT p hp ep
          (relativeDimension_of_flat_of_isVariety K sP sT p hp ep hep) d w).1
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) sP s (dX : ℤ)).1 := by
  classical
  let : LocallyOfFiniteType p := locallyOfFiniteType_of_isVariety_comp K sP sT p hp
  have : IsIntegral X := IsVariety.toIsIntegral (k := K) (f := sX)
  intro W' V hW' hV
  have hVgen : V.isIrreducible.genericPoint = s.base (genericPoint X) := by
    by_contra hne
    exact hV (cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne (fieldChowSituation K) sP
      s _ hne)
  have hVset : (V : Set P) = Set.range s.base := by
    rw [CycleFlatPullback.coe_eq_closure_genericPoint V, hVgen, ← Set.image_singleton,
      s.isClosedEmbedding.closure_image_eq, genericPoint_spec, Set.image_univ]
  have hVdim : topologicalKrullDim (V : Set P) = (dX : WithBot ℕ∞) := by
    rw [hVset, topologicalKrullDim_range_eq, hdX]
  have hW'mem := (mem_cyclesOfDimension (fieldChowSituation K) sP (d + (ep : ℤ)) _).1
    (flatPullback (fieldChowSituation K) sP sT p hp ep
      (relativeDimension_of_flat_of_isVariety K sP sT p hp ep hep) d w).2 W' hW'
  rw [flatPullback_apply] at hW'
  obtain ⟨hwt, -⟩ := mul_ne_zero_iff.1 hW'
  set t := p.base W'.isIrreducible.genericPoint with ht
  have htd : relativeDimension (fieldChowSituation K).dimensionFunction sT t = d :=
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) sT d w.1).1 w.2 t hwt
  obtain ⟨d', rfl⟩ := exists_natCast_of_relativeDimension_eq K sT t d htd
  have hW'dim : topologicalKrullDim (W' : Set P) = ((d' + ep : ℕ) : WithBot ℕ∞) :=
    CycleFlatPullback.topologicalKrullDim_coe_eq K sP W' (d' + ep) (by rw [hW'mem]; push_cast; rfl)
  have hZdim : topologicalKrullDim (closure ({t} : Set T)) ≤ (d' : WithBot ℕ∞) :=
    (ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq K sT t d'
      htd).le
  have hsub : (W' : Set P) ⊆ p.base ⁻¹' closure ({t} : Set T) := by
    rw [CycleFlatPullback.coe_eq_closure_genericPoint W']
    exact closure_minimal (Set.singleton_subset_iff.2 (subset_closure rfl))
      (isClosed_closure.preimage p.continuous)
  have hinter : topologicalKrullDim ↥((W' : Set P) ∩ (V : Set P)) ≤
      ((d' + eq : ℕ) : WithBot ℕ∞) := by
    refine le_trans (topologicalKrullDim_le_of_subset ?_)
      (topologicalKrullDim_preimage_inter_range_le K sX sP sT s hs p hp eq heq
        (Closeds.closure {t}) d' hZdim)
    rw [hVset]
    exact Set.inter_subset_inter_left _ hsub
  have hrs : (d' + eq) + dP = (d' + ep) + dX := by
    have := dim_add_eq_of_relative_dim K sT dP dX ep eq hdP hdX hep heq
    omega
  rw [AlgebraicGeometry.intersectProperly_iff, hW'dim, hVdim, hdP]
  refine le_trans (add_le_add hinter le_rfl) (le_of_eq ?_)
  rw [← Nat.cast_add, ← Nat.cast_add, hrs]

end Transversal

end Stacks.Intersection.ChowRing

end
