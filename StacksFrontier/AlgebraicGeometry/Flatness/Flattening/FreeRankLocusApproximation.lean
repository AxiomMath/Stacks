module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BaseChangeCofilteredLimit
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocusDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibrePointFreeness
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation

/-!
# Approximating the generic-point condition over a cofiltered limit of affine bases

Let `f : X ⟶ S` be the smooth family of Situation 05MP with a module of finite presentation, and
let `T = lim T_i` be a cofiltered limit of affine schemes over `S`. If the module pulled back to
`X ×_S T` is free of rank `p` near the generic point of every fibre over `T`, then the same holds
over one stage `T_i` of the system. This is the second clause of Stacks 05MS.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.exists_mem_baseRankLocus_of_isLimit`: for each
  point of the limit base, some stage already has the corresponding point in the image of its
  free-rank locus.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.exists_condition_of_isLimit`: the generic-point
  condition over the limit holds over some stage.

## References

* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u}) (p : ℕ)

/-- For every point of the limit of a cofiltered system of affine schemes over the base, the
generic-point condition over the limit forces the image of that point in some stage into the
image of the free-rank locus of that stage. -/
theorem exists_mem_baseRankLocus_of_isLimit [D.F.IsFinitePresentation]
    {I : Type u} [Category.{u} I] [IsCofiltered I] (E : I ⥤ Over D.S) (c : Cone E)
    (hc : IsLimit ((Over.forget D.S).mapCone c))
    (hE : ∀ i, IsAffine ((Over.forget D.S).obj (E.obj i)))
    (hcond : D.Condition p c.pt) (τ : c.pt.left) :
    ∃ j : I, (c.π.app j).left τ ∈ D.baseRankLocus p (E.obj j) := by
  classical
  have hEL : ∀ k : I, IsAffine (E.obj k).left := hE
  obtain ⟨ξ, hξ⟩ := D.exists_isGenericPoint_fiber_baseChangeMap c.pt τ
  obtain ⟨A, hxA, hA⟩ := hcond τ ξ hξ
  obtain ⟨A₁, hA₁aff, hxA₁, hA₁le⟩ := exists_isAffineOpen_mem_and_subset hxA
  obtain ⟨i, B, -, hBpre⟩ :=
    D.exists_preimage_eq_transitionHom E c hc hE A₁ hA₁aff.isCompact
  have hyB : D.transitionHom (c.π.app i) ((D.baseChangeMap c.pt).fiberι τ ξ) ∈ B := by
    show (D.baseChangeMap c.pt).fiberι τ ξ ∈ D.transitionHom (c.π.app i) ⁻¹ᵁ B
    rwa [hBpre]
  obtain ⟨V, hVaff, hyV, hVle⟩ := exists_isAffineOpen_mem_and_subset hyB
  have hWle : D.transitionHom (c.π.app i) ⁻¹ᵁ V ≤ A := by
    refine le_trans ?_ hA₁le
    rw [← hBpre]
    exact Scheme.Hom.preimage_mono _ hVle
  have hflat := D.isFlatOver_of_invertibleRank p c.pt _
    (invertibleRank_pullback_of_le (D.baseChangeModule c.pt) p hWle hA)
  obtain ⟨j, e, hjflat⟩ := D.exists_isFlatOver_preimage E c hc hE i V hVaff hflat
  refine ⟨j, ?_⟩
  obtain ⟨ξj, hξj⟩ := D.exists_isGenericPoint_fiber_baseChangeMap (E.obj j) ((c.π.app j).left τ)
  have hmap : D.transitionHom (c.π.app j) ((D.baseChangeMap c.pt).fiberι τ ξ) =
      (D.baseChangeMap (E.obj j)).fiberι ((c.π.app j).left τ) ξj :=
    D.transitionHom_fiberι_of_isGenericPoint (c.π.app j) τ hξ hξj
  have hyjV : (D.baseChangeMap (E.obj j)).fiberι ((c.π.app j).left τ) ξj ∈
      D.transitionHom (E.map e) ⁻¹ᵁ V := by
    show D.transitionHom (E.map e) _ ∈ V
    rw [← hmap]
    have hh : D.transitionHom (E.map e)
          (D.transitionHom (c.π.app j) ((D.baseChangeMap c.pt).fiberι τ ξ)) =
        D.transitionHom (c.π.app i) ((D.baseChangeMap c.pt).fiberι τ ξ) := by
      rw [show c.π.app i = c.π.app j ≫ E.map e from (c.w e).symm, D.transitionHom_comp]
      rfl
    rwa [hh]
  have hWaff : IsAffineOpen (D.transitionHom (E.map e) ⁻¹ᵁ V) :=
    have := hEL i
    have := hEL j
    have : IsAffineHom (D.transitionHom (E.map e)) := D.isAffineHom_transitionHom (E.map e)
    IsAffineHom.isAffine_preimage V hVaff
  have hWa : IsAffine (D.transitionHom (E.map e) ⁻¹ᵁ V).toScheme := hWaff
  have hTq : QuasiSeparatedSpace ((E.obj j).left) := have := hEL j; inferInstance
  have hfpW : AlgebraicGeometry.FinitePresentation
      ((D.transitionHom (E.map e) ⁻¹ᵁ V).ι ≫ D.baseChangeMap (E.obj j)) :=
    finitePresentation_of_compactSpace _ inferInstance
  have hgen := isGenericPoint_asFiber_comp_ι (D.baseChangeMap (E.obj j))
    (D.transitionHom (E.map e) ⁻¹ᵁ V)
    (⟨(D.baseChangeMap (E.obj j)).fiberι ((c.π.app j).left τ) ξj, hyjV⟩)
    (isGenericPoint_asFiber (D.baseChangeMap (E.obj j)) _ ξj hξj)
  obtain ⟨n, hn⟩ := exists_freeAtPointOfRank_of_isFlatOverAt
    ((D.transitionHom (E.map e) ⁻¹ᵁ V).ι ≫ D.baseChangeMap (E.obj j)) hfpW _ _ hgen (hjflat _)
  have hn' : FreeAtPointOfRank (D.baseChangeModule (E.obj j))
      ((D.baseChangeMap (E.obj j)).fiberι ((c.π.app j).left τ) ξj) n :=
    freeAtPointOfRank_of_opens _ _ _ n hn
  have hnp : n = p := by
    refine freeAtPointOfRank_unique (D.baseChangeModule c.pt) ?_ (hcond τ ξ hξ)
    refine D.freeAtPointOfRank_transitionHom n (c.π.app j) ?_
    rwa [hmap]
  refine ⟨(D.baseChangeMap (E.obj j)).fiberι ((c.π.app j).left τ) ξj, ?_, ?_⟩
  · rwa [← hnp]
  · have hr : (D.baseChangeMap (E.obj j)).fiberι ((c.π.app j).left τ) ξj ∈
        Set.range ((D.baseChangeMap (E.obj j)).fiberι ((c.π.app j).left τ)) := ⟨ξj, rfl⟩
    rwa [Scheme.Hom.range_fiberι] at hr

/-- **Stacks Project, Tag 05MS, part (2)**, at the level of the generic-point condition: when the
module pulled back to the base change along a cofiltered limit of affine schemes over the base is
free of rank `p` near the generic point of every fibre, the same already holds over one stage of
the system. -/
theorem exists_condition_of_isLimit [D.F.IsFinitePresentation]
    {I : Type u} [Category.{u} I] [IsCofiltered I] (E : I ⥤ Over D.S) (c : Cone E)
    (hc : IsLimit ((Over.forget D.S).mapCone c))
    (hE : ∀ i, IsAffine ((Over.forget D.S).obj (E.obj i)))
    (hpt : IsAffine ((Over.forget D.S).obj c.pt))
    (hcond : D.Condition p c.pt) :
    ∃ i, D.Condition p (E.obj i) := by
  classical
  have hAff : ∀ k : I, IsAffine ((E ⋙ Over.forget D.S).obj k) := hE
  have hptL : IsAffine c.pt.left := hpt
  have hcompact : ∀ k : I, CompactSpace ((E ⋙ Over.forget D.S).obj k) :=
    fun k => have := hAff k; inferInstance
  have haffhom : ∀ {k l : I} (e : k ⟶ l), IsAffineHom ((E ⋙ Over.forget D.S).map e) :=
    fun {k l} e => have := hAff k; have := hAff l; isAffineHom_of_isAffine _
  have hmono : ∀ {k j : I} (_ : k ⟶ j),
      (c.π.app j).left ⁻¹' D.baseRankLocus p (E.obj j) ⊆
        (c.π.app k).left ⁻¹' D.baseRankLocus p (E.obj k) := by
    intro k j e
    have hw : (c.π.app k).left ≫ (E.map e).left = (c.π.app j).left := by
      rw [← Over.comp_left, c.w e]
    rw [← hw]
    intro z hz
    exact D.preimage_baseRankLocus_subset p (E.map e) hz
  have hcov : (Set.univ : Set c.pt.left) ⊆
      ⋃ j : I, (c.π.app j).left ⁻¹' D.baseRankLocus p (E.obj j) := by
    intro τ _
    obtain ⟨j, hj⟩ := D.exists_mem_baseRankLocus_of_isLimit p E c hc hE hcond τ
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun j : I => ((c.π.app j).left ⁻¹' D.baseRankLocus p (E.obj j) : Set ↥c.pt.left))
    (fun j => (D.isOpen_baseRankLocus p (E.obj j)).preimage (c.π.app j).left.continuous) hcov
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (C := I) s
  have hGk : ∀ τ : c.pt.left, (c.π.app k).left τ ∈ D.baseRankLocus p (E.obj k) := by
    intro τ
    obtain ⟨j, hjs, hτ⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ τ))
    exact hmono (hk hjs).some hτ
  have htop : (⨆ _ : Unit, ((Over.forget D.S).mapCone c).π.app k ⁻¹ᵁ
      (⟨D.baseRankLocus p (E.obj k), D.isOpen_baseRankLocus p (E.obj k)⟩ :
        ((E ⋙ Over.forget D.S).obj k).Opens)) = ⊤ := by
    rw [iSup_const]
    exact TopologicalSpace.Opens.ext (Set.eq_univ_iff_forall.mpr hGk)
  obtain ⟨m, e, hm⟩ := exists_iSup_map_preimage_eq_top (E ⋙ Over.forget D.S)
    ((Over.forget D.S).mapCone c) hc
    (fun _ : Unit => (⟨D.baseRankLocus p (E.obj k), D.isOpen_baseRankLocus p (E.obj k)⟩ :
      ((E ⋙ Over.forget D.S).obj k).Opens)) htop
  rw [iSup_const] at hm
  refine ⟨m, (D.condition_iff_baseRankLocus_eq_univ p (E.obj m)).mpr
    (Set.eq_univ_iff_forall.mpr fun z => ?_)⟩
  refine D.preimage_baseRankLocus_subset p (E.map e) ?_
  have hz : z ∈ ((E ⋙ Over.forget D.S).map e ⁻¹ᵁ
      (⟨D.baseRankLocus p (E.obj k), D.isOpen_baseRankLocus p (E.obj k)⟩ :
        ((E ⋙ Over.forget D.S).obj k).Opens)) := by
    rw [hm]; trivial
  exact hz

end AlgebraicGeometry.FreeAtGenericPointsSituation

end
