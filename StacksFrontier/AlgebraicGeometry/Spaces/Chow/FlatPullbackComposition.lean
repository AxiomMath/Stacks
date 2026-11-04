module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FiniteLocallyFreePushPull
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatCompositeRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackAssociatedCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles

/-!
# Flat pullback of cycles along a composite

In Situation 0EDT let `X/B`, `Y/B` and `Z/B` be good and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms over the base which are flat of relative dimensions `r` and `s`. **Stacks 0EPA** says
that `g ∘ f` is flat of relative dimension `r + s` and that

`f^* ∘ g^* = (g ∘ f)^*` as maps `Z_k(Z) → Z_{k+r+s}(X)`.

The first assertion is `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_comp`; this file
proves the second.

## Main results

* `AlgebraicGeometry.Space.ambientGenericPoint_eq_of_flatPullbackMult_ne_zero`: an integral
  closed subspace `A' ⊆ Y` whose flat pullback contains `T ⊆ X` has the image of the generic
  point of `T` for its generic point.
* `AlgebraicGeometry.Space.eq_of_flatPullbackMult_ne_zero`: so at most one `A'` contributes to a
  given `T`.
* `AlgebraicGeometry.Space.flatPullbackMult_comp_eq_finsum`: the multiplicities of the flat
  pullback along `g ∘ f` are the convolution of those along `g` and along `f`,
  `m_{T, (g ∘ f)^{-1}(A)} = ∑_{A'} m_{A', g^{-1}(A)} · m_{T, f^{-1}(A')}`.
* `AlgebraicGeometry.Space.flatPullbackMap_comp`: the identity `(g ∘ f)^* = f^* ∘ g^*`.
* `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_comp_and_flatPullbackMap_comp`: both
  assertions of Stacks 0EPA.

## Implementation notes

The cycle `(g ∘ f)^*[A]` is compared with `f^*(g^*[A])` through part (1) of Stacks 0EPB,
`AlgebraicGeometry.Space.flatPullback_closedSubspaceCycle_preimage`, applied to the closed
subspace `g^{-1}(A) ⊆ Y`; the subspace `(g ∘ f)^{-1}(A)` is `f^{-1}(g^{-1}(A))` definitionally,
as subfunctors.

## References

* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### At most one subspace of the target contributes -/

section Unique

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- **A subspace whose flat pullback contains `T` has the image of the generic point of `T` for
its generic point.** Let `A' ⊆ Y` and `T ⊆ X` be integral closed subspaces with `T` occurring in
`f^*[A']`. Then the generic point of `A'` is the image under `f` of the generic point of `T`. -/
theorem ambientGenericPoint_eq_of_flatPullbackMult_ne_zero
    (A' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hne : flatPullbackMult D sX hX sY hY f hbase r hflat hr A' T ≠ 0) :
    A'.ambientGenericPoint D.site D.base D.base_mem =
      pointsMap D.site D.base D.base_mem X f
        (T.ambientGenericPoint D.site D.base D.base_mem) := by
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hcl : IsClosed (subspacePointSet D.site D.base D.base_mem Y A'.subspace) :=
    isClosed_subspacePointSet_of_isClosedSubspace D hY.1 A'.subspace A'.isClosedSubspace
  have hmem := mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat
    hr A' T hne
  have hTdim := deltaDimension_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr
    A' T hne
  have hbound : deltaDimensionClosed D sY hY
      (subspacePointSet D.site D.base D.base_mem Y A'.subspace) hcl ≤
        ((deltaDimension D sY A' : ℤ) : EInt) :=
    le_of_eq (deltaDimensionSubspace_integralClosedSubspace D sY hY A')
  obtain ⟨hδ, C, hC⟩ := exists_isGenericPoint_image D sX hX sY hY f hbase r hr
    (deltaDimension D sY A') _ hcl hbound T hTdim hmem
  set A'' := closedSetComponent D.site D.base D.base_mem hY.1 hYdec
    (subspacePointSet D.site D.base D.base_mem Y A'.subspace) hcl C with hA''
  have hagp : A''.ambientGenericPoint D.site D.base D.base_mem =
      pointsMap D.site D.base D.base_mem X f
        (T.ambientGenericPoint D.site D.base D.base_mem) :=
    ambientGenericPoint_closedSetComponent D hY.1 hYdec _ hcl C _ hmem hC
  have hdim : deltaDimension D sY A'' = deltaDimension D sY A' := by
    rw [deltaDimension_eq_of_isGenericPoint D sY hY.1 A'' _
      (hagp ▸ A''.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1)]
    exact hδ
  have hA''A' : A'' = A' :=
    eq_of_mem_subspacePointSet_ambientGenericPoint D sY hY A' A'' (by rw [hagp]; exact hmem)
      hdim
  rw [← hA''A', hagp]

/-- **At most one integral closed subspace of the target contributes to a given `T`.** Two
integral closed subspaces `A₁, A₂ ⊆ Y` whose flat pullbacks both contain `T ⊆ X` are equal. -/
theorem eq_of_flatPullbackMult_ne_zero
    (A₁ A₂ : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (h₁ : flatPullbackMult D sX hX sY hY f hbase r hflat hr A₁ T ≠ 0)
    (h₂ : flatPullbackMult D sX hX sY hY f hbase r hflat hr A₂ T ≠ 0) :
    A₁ = A₂ := by
  have hg₁ := ambientGenericPoint_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat
    hr A₁ T h₁
  have hd₁ := deltaDimension_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr
    A₁ T h₁
  have hd₂ := deltaDimension_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr
    A₂ T h₂
  refine eq_of_mem_subspacePointSet_ambientGenericPoint D sY hY A₂ A₁ ?_ (by lia)
  rw [hg₁]
  exact mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr A₂ T h₂

end Unique

/-! ### Composing two flat morphisms -/

section Composite

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY) (r s : ℕ)
    (hff : IsFlat D.site D.base D.base_mem f)
    (hfr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hgf : IsFlat D.site D.base D.base_mem g)
    (hgs : HasRelativeDimension s D.site D.base D.base_mem g)

/-- **The multiplicities of a composite flat pullback are the convolution of the two.** For an
integral closed subspace `A ⊆ Z` and an integral closed subspace `T ⊆ X`,

`m_{T, (g ∘ f)^{-1}(A)} = ∑_{A'} m_{A', g^{-1}(A)} · m_{T, f^{-1}(A')}`. -/
theorem flatPullbackMult_comp_eq_finsum
    (A : IntegralClosedSubspace D.site D.base D.base_mem Z)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    flatPullbackMult D sX hX sZ hZ (f ≫ g)
        (comp_structureMorphism_eq D sX sY sZ f g hfbase hgbase) (r + s)
        (isFlat_and_hasRelativeDimension_comp D sX hX sY hY sZ hZ f g hfbase hgbase r s
          hff hfr hgf hgs).2.1
        (isFlat_and_hasRelativeDimension_comp D sX hX sY hY sZ hZ f g hfbase hgbase r s
          hff hfr hgf hgs).2.2 A T =
      ∑ᶠ A' : IntegralClosedSubspace D.site D.base D.base_mem Y,
        flatPullbackMult D sY hY sZ hZ g hgbase s hgf hgs A A' *
          flatPullbackMult D sX hX sY hY f hfbase r hff hfr A' T := by
  obtain ⟨hdim, hkey⟩ := flatPullback_closedSubspaceCycle_preimage D sX hX sY hY f hfbase r hff
    hfr (deltaDimension D sZ A + (s : ℤ)) (A.subspace.preimage g)
    (isClosedSubspace_preimage_integralClosedSubspace D sY hY sZ hZ g A)
    (deltaDimensionSubspace_preimage_integralClosedSubspace_le D sY hY sZ hZ g hgbase s hgf
      hgs A)
  have hT := congrArg (fun c : CycleGroup D sX (deltaDimension D sZ A + (s : ℤ) + (r : ℤ)) =>
    c.1 T) hkey
  simp only [flatPullbackMap_apply] at hT
  have hdeg : deltaDimension D sZ A + (((r + s : ℕ) : ℤ)) =
      deltaDimension D sZ A + (s : ℤ) + (r : ℤ) := by push_cast; ring
  rw [closedSubspaceCycle_coe] at hT
  unfold flatPullbackMult flatPullbackIntegralCycle
  rwa [closedSubspaceCycle_coe, hdeg]

/-- **The flat pullback of cycles composes: `(g ∘ f)^* = f^* ∘ g^*`.** As homomorphisms
`Z_k(Z) → Z_n(X)` for `k + (r + s) = n`, the flat pullback along `g ∘ f`, which is flat of
relative dimension `r + s` by `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_comp`, is
the flat pullback along `g` followed by the flat pullback along `f`. -/
theorem flatPullbackMap_comp (k n : ℤ) (hn : k + ((r + s : ℕ) : ℤ) = n) :
    flatPullbackMap D sX hX sZ hZ (f ≫ g)
        (comp_structureMorphism_eq D sX sY sZ f g hfbase hgbase) (r + s)
        (isFlat_and_hasRelativeDimension_comp D sX hX sY hY sZ hZ f g hfbase hgbase r s
          hff hfr hgf hgs).2.1
        (isFlat_and_hasRelativeDimension_comp D sX hX sY hY sZ hZ f g hfbase hgbase r s
          hff hfr hgf hgs).2.2 k n hn =
      (flatPullbackMap D sX hX sY hY f hfbase r hff hfr (k + (s : ℤ)) n
          (by push_cast at hn; omega)).comp
        (flatPullbackMap D sY hY sZ hZ g hgbase s hgf hgs k (k + (s : ℤ)) rfl) := by
  classical
  refine AddMonoidHom.ext fun α => Subtype.ext (funext fun T => ?_)
  rw [AddMonoidHom.comp_apply]
  simp only [flatPullbackMap_apply]
  by_cases hex : ∃ A0 : IntegralClosedSubspace D.site D.base D.base_mem Y,
      flatPullbackMult D sX hX sY hY f hfbase r hff hfr A0 T ≠ 0
  · obtain ⟨A0, hA0⟩ := hex
    have huniq : ∀ A' : IntegralClosedSubspace D.site D.base D.base_mem Y, A' ≠ A0 →
        flatPullbackMult D sX hX sY hY f hfbase r hff hfr A' T = 0 := by
      intro A' hA'
      by_contra h
      exact hA' (eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hfbase r hff hfr A' A0 T h hA0)
    rw [finsum_eq_single _ A0 (fun A' hA' => by rw [huniq A' hA', mul_zero]),
      finsum_mul]
    refine finsum_congr fun A => ?_
    rw [flatPullbackMult_comp_eq_finsum D sX hX sY hY sZ hZ f g hfbase hgbase r s hff hfr hgf
      hgs A T, finsum_eq_single _ A0 (fun A' hA' => by rw [huniq A' hA', mul_zero]), mul_assoc]
  · simp only [not_exists, not_not] at hex
    refine Eq.trans (finsum_eq_zero_of_forall_eq_zero fun A => ?_)
      (finsum_eq_zero_of_forall_eq_zero fun A' => by rw [hex A', mul_zero]).symm
    rw [flatPullbackMult_comp_eq_finsum D sX hX sY hY sZ hZ f g hfbase hgbase r s hff hfr hgf
      hgs A T, finsum_eq_zero_of_forall_eq_zero fun A' => by rw [hex A', mul_zero], mul_zero]

/-- In Situation 0EDT let `X/B`, `Y/B` and `Z/B` be good and let `f : X ⟶ Y`
and `g : Y ⟶ Z` be morphisms over the base which are flat of relative dimensions `r` and `s`.
Then

1. `g ∘ f` is flat of relative dimension `r + s` (and locally of finite type), and
2. `f^* ∘ g^* = (g ∘ f)^*` as maps `Z_k(Z) → Z_{k+r+s}(X)`, for every `k`.

The degree of the target is any `n` with `k + (r + s) = n`, which is how
`AlgebraicGeometry.Space.flatPullbackMap` is graded. The flat pullback along `g ∘ f` in part (2)
is formed with the flatness and relative dimension that part (1) provides. -/
@[stacks 0EPA "both assertions: g ∘ f is flat of relative dimension r + s, and
  f^* ∘ g^* = (g ∘ f)^* as maps Z_k(Z) → Z_{k+r+s}(X)"]
theorem isFlat_and_hasRelativeDimension_comp_and_flatPullbackMap_comp :
    (IsLocallyOfFiniteType D.site D.base D.base_mem (f ≫ g) ∧
      IsFlat D.site D.base D.base_mem (f ≫ g) ∧
        HasRelativeDimension (r + s) D.site D.base D.base_mem (f ≫ g)) ∧
      ∀ (k n : ℤ) (hn : k + ((r + s : ℕ) : ℤ) = n),
        (flatPullbackMap D sX hX sY hY f hfbase r hff hfr (k + (s : ℤ)) n
            (by push_cast at hn; omega)).comp
          (flatPullbackMap D sY hY sZ hZ g hgbase s hgf hgs k (k + (s : ℤ)) rfl) =
        flatPullbackMap D sX hX sZ hZ (f ≫ g)
          (comp_structureMorphism_eq D sX sY sZ f g hfbase hgbase) (r + s)
          (isFlat_and_hasRelativeDimension_comp D sX hX sY hY sZ hZ f g hfbase hgbase r s
            hff hfr hgf hgs).2.1
          (isFlat_and_hasRelativeDimension_comp D sX hX sY hY sZ hZ f g hfbase hgbase r s
            hff hfr hgf hgs).2.2 k n hn :=
  ⟨isFlat_and_hasRelativeDimension_comp D sX hX sY hY sZ hZ f g hfbase hgbase r s hff hfr hgf
      hgs,
    fun k n hn => (flatPullbackMap_comp D sX hX sY hY sZ hZ f g hfbase hgbase r s hff hfr hgf
      hgs k n hn).symm⟩

end Composite

end AlgebraicGeometry.Space

end
