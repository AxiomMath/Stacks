module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesSeparablePoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.SmoothPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleStalkFree
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Chow.EtaleSeparableResidueField
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Sober.Generization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local rings of schemes over a field

Four facts about the local rings of schemes over a field `k`.

## Main results

* `Stacks.Chow.isRegularLocalRing_stalk_of_smooth` — the local rings of a scheme smooth over `k`
  are regular (Stacks 056S).
* `Stacks.Chow.injective_stalkFunctor_map_unitHomEquiv_symm_of_isDomain` — if `L` is invertible,
  `s` a global section and `O_{X,ξ}` a domain, then multiplication by `s` on stalks at `ξ` is
  injective as soon as the germ `s_ξ` is nonzero.
* `Stacks.Chow.hasSeparableResidueField_of_smooth_of_relativeDimension_le_zero` — every residue
  field of a smooth `k`-scheme all of whose points have dimension `0` is separable over `k`.
* `Stacks.Chow.ringKrullDim_stalk_eq_of_isClosed` — at a closed point of an integral scheme locally
  of finite type over `k`, the local ring has dimension `trdeg_k k(X) = dim X`.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Chow

/-- Every local ring of a scheme smooth over a field is regular. -/
theorem isRegularLocalRing_stalk_of_smooth {k : Type u} [Field k] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of k)) [Smooth q] (y : Y) : IsRegularLocalRing (Y.presheaf.stalk y) :=
  (isRegular_of_smooth_over_field q).isRegularLocalRing_stalk y

/-- Let `M` be an invertible module, `s` a global section of `M` and `ξ` a point at which the
local ring is a domain. If the germ of `s` at `ξ` is nonzero, then multiplication by `s`,
`O_X → M`, is injective on stalks at `ξ`. -/
theorem injective_stalkFunctor_map_unitHomEquiv_symm_of_isDomain {W : Scheme.{u}}
    (M : W.Modules) [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj
      W.ringCatSheaf.property M]
    (s : M.sections) (ξ : W) [IsDomain (W.presheaf.stalk ξ)]
    (hs : (M.presheaf.Γgerm ξ).hom (s.eval (op ⊤)) ≠ 0) :
    Function.Injective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ξ).map
        ((Scheme.Modules.toPresheaf W).map (M.unitHomEquiv.symm s)))) := by
  have := (Stacks.InvertibleStalk.isInvertible_presheaf_iff M).2 ‹_›
  obtain ⟨V, hV, e, he⟩ := Stacks.InvertibleStalk.exists_germ_isStalkBasis M ξ
  obtain ⟨c, hc⟩ := he.surjective ((M.presheaf.Γgerm ξ).hom (s.eval (op ⊤)))
  intro a b hab
  have hab' : LocallyFreeRank.stalkLMap (M.unitHomEquiv.symm s).val ξ a =
    LocallyFreeRank.stalkLMap (M.unitHomEquiv.symm s).val ξ b := hab
  have hc' : c • TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf V ξ hV e =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf ⊤ ξ trivial
        (s.eval (op ⊤)) := hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hs (hc.symm.trans (zero_smul _ _))
  rw [stalkLMap_unitHomEquiv_symm_apply M s ξ a, stalkLMap_unitHomEquiv_symm_apply M s ξ b, ← hc',
    smul_smul, smul_smul] at hab'
  exact (structureSheafStalkLinearEquiv W ξ).injective (mul_right_cancel₀ hc0 (he.injective hab'))

/-- A scheme smooth over a field `k` all of whose points have dimension at most `0` over `k` has
residue fields separable over `k`. -/
theorem hasSeparableResidueField_of_smooth_of_relativeDimension_le_zero (k : Type u) [Field k]
    {Y : Scheme.{u}} (q : Y ⟶ (fieldChowSituation k).S) [Smooth q]
    (hdim : ∀ y : Y, relativeDimension (fieldChowSituation k).dimensionFunction q y ≤ 0)
    (y : Y) : HasSeparableResidueField k q y := by
  have hzero : ∀ z : Y, relativeDimension (fieldChowSituation k).dimensionFunction q z = 0 :=
    fun z => le_antisymm (hdim z) (add_nonneg le_rfl (Int.natCast_nonneg _))
  have hfib : ∀ z : Y, topologicalKrullDimAt (q.fiber (q z)) (q.asFiber z) =
      ((0 : ℕ) : WithBot ℕ∞) := by
    intro z
    have hcl : IsClosed ({z} : Set Y) :=
      isClosed_singleton_of_relativeDimension_eq_zero k q (hzero z)
    have hgen : z ∈ genericPoints Y := by
      refine (mem_genericPoints_iff_forall_specializes_eq z).2 fun w hwz => ?_
      by_contra hne
      simpa [hzero] using relativeDimension_lt_of_mem_closure_of_ne (fieldChowSituation k) q
        (specializes_iff_mem_closure.mp hwz) (Ne.symm hne)
    rw [← topologicalKrullDimAt_eq_fiber_of_subsingleton q z,
      topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point q z hcl,
      AlgebraicGeometry.ringKrullDim_stalk_eq_zero_of_mem_genericPoints Y z hgen]
    rfl
  have : SmoothOfRelativeDimension 0 q :=
    Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq q 0 hfib
  exact hasSeparableResidueField_of_smoothOfRelativeDimension_zero k q y

/-- At a closed point `x` of an integral scheme `X` locally of finite type over a field `k`, the
local ring has dimension `n`, the `δ`-dimension of the generic point of `X`. -/
@[ega "II 7.4.1" "(a) ⇒ (b) for integral X"]
theorem ringKrullDim_stalk_eq_of_isClosed (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] [IsIntegral X]
    (x : X) (hx : IsClosed ({x} : Set X)) (n : ℕ)
    (hn : relativeDimension (fieldChowSituation k).dimensionFunction p (genericPoint X) = n) :
    ringKrullDim (X.presheaf.stalk x) = n := by
  have hgen : IsGenericPoint (genericPoint X) (Set.univ : Set X) :=
    (IrreducibleSpace.isIrreducible_univ X).isGenericPoint_genericPoint isClosed_univ
  have htop := topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k)
    (fun _ _ ↦ rfl) p (𝟙 X) (genericPoint X) hgen
  rw [show (𝟙 X : X ⟶ X).base (genericPoint X) = genericPoint X from rfl, hn,
    Int.toNat_natCast] at htop
  rw [← topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point p x hx,
    ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X p x, htop]

end Stacks.Chow

end
