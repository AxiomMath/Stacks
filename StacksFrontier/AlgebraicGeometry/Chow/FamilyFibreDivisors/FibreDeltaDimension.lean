module

public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDivisorPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrimeDivisorDimension

/-!
# The delta-dimension of the two fibres of an integral family over the projective line

Let `W ⊆ X ×_S 𝐏¹_S` be an integral closed subscheme of relative dimension `k + 1` over the base,
contained in neither of the two distinguished sections. Its zero and infinity fibres
`Stacks.Chow.zeroFiber` and `Stacks.Chow.infinityFiber` are closed subschemes of `X`, and this
file proves the bound `dim_δ ≤ k` for both.

The bound is the hypothesis every statement of Stacks 02S5 takes — see
`Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent` and
`Stacks.Chow.fibreDifference_isRationallyEquivalentToZeroWithin` — and it was not available as a
theorem anywhere. Being able to discharge it is what lets a consumer of Stacks 02S5 start from
the output of Stacks 02S4 part (4) (`Stacks.Chow.exists_familyFibreDifferences`), which supplies
the relative dimension of `W` and the two non-degeneracy conditions and nothing about the
fibres.

## Main results

* `Stacks.Chow.schemeDeltaDimension_isEffectiveCartierDivisor_le` — an effective Cartier divisor
  on an integral scheme over the base drops the delta-dimension by at least one. This is
  Stacks 02RK read as a bound on the whole divisor rather than component by component.
* `Stacks.Chow.schemeDeltaDimension_zeroFiber_eq_zeroDivisor`,
  `Stacks.Chow.schemeDeltaDimension_infinityFiber_eq_infinityDivisor` — the fibre of `W`, as a
  closed subscheme of `X`, and the divisor it cuts on `W` have the same delta-dimension: they
  are two closed subschemes of `X ×_S 𝐏¹_S` with the same underlying closed set.
* `Stacks.Chow.schemeDeltaDimension_zeroFiber_le`,
  `Stacks.Chow.schemeDeltaDimension_infinityFiber_le` — the bound `dim_δ ≤ k`.

## Implementation notes

The fibre `W₀ = W ×_{X ×_S 𝐏¹_S} X` along the zero section and the divisor
`Stacks.Chow.zeroDivisor` cut on `W` by the image of that section are *different* closed
subschemes of *different* ambient schemes, and the comparison between them used here is only
topological: both, read as closed subschemes of `X ×_S 𝐏¹_S`, have underlying closed set
`Set.range (zeroSection f) ∩ Set.range W.subschemeι`, and delta-dimension depends only on the
underlying closed set. The scheme structures do differ in general, so no stronger identification
is claimed.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### An effective Cartier divisor drops the delta-dimension -/

/-- **Stacks 02RK, as a bound on a whole divisor.** An effective Cartier divisor on an integral
scheme locally of finite type over the base has delta-dimension at most one less than that of the
ambient scheme: every irreducible component of it drops the delta-dimension by exactly one. -/
theorem schemeDeltaDimension_isEffectiveCartierDivisor_le (C : ChowSituation.{u})
    {Y : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral Y]
    (D : Y.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    schemeDeltaDimension C (D.subschemeι ≫ p) ≤ schemeDeltaDimension C p + (-1 : ℤ) := by
  rw [schemeDeltaDimension_eq_iSup]
  exact iSup_le fun Z ↦ le_of_eq
    (deltaDimension_irreducibleComponent_isEffectiveCartierDivisor C p D hD Z)

/-! ### The fibre and the divisor have the same underlying closed set -/

/-- The image in the ambient scheme of the inverse image of a closed subscheme along a morphism
is the intersection of the image of that morphism with the support. -/
private theorem range_subschemeι_comap_comp {A B : Scheme.{u}} (s : A ⟶ B)
    (I : B.IdealSheafData) :
    Set.range ((I.comap s).subschemeι ≫ s) = Set.range s ∩ (I.support : Set B) := by
  change Set.range (s ∘ (I.comap s).subschemeι) = _
  rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.support_comap]
  exact Set.image_preimage_eq_range_inter

/-- The fibre of `W` along a closed-immersion section and the divisor cut on `W` by the image of
that section have the same image in `X ×_S 𝐏¹_S`, namely the intersection of the image of the
section with the support of `W`. -/
private theorem range_comap_section_eq {X S : Scheme.{u}} (f : X ⟶ S)
    (W : (projectiveLineProduct f).IdealSheafData) (s : X ⟶ projectiveLineProduct f)
    [IsClosedImmersion s] :
    Set.range ((W.comap s).subschemeι ≫ s) =
      Set.range (((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure (Set.range s), isClosed_closure⟩).comap W.subschemeι).subschemeι ≫
          W.subschemeι) := by
  have hclosed : IsClosed (Set.range s) := s.isClosedEmbedding.isClosed_range
  rw [range_subschemeι_comap_comp, range_subschemeι_comap_comp,
    ← Scheme.IdealSheafData.range_subschemeι W,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  change Set.range s ∩ Set.range W.subschemeι =
    Set.range W.subschemeι ∩ closure (Set.range s)
  rw [hclosed.closure_eq]
  exact Set.inter_comm _ _

/-- Equal morphisms to the base have equal delta-dimension. The instance argument of
`Stacks.Chow.schemeDeltaDimension` depends on the morphism, so an equality of morphisms cannot be
rewritten under it; substituting first and appealing to proof irrelevance of the instance can. -/
theorem schemeDeltaDimension_congr (C : ChowSituation.{u}) {Y : Scheme.{u}}
    {g h : Y ⟶ C.S} [LocallyOfFiniteType g] [LocallyOfFiniteType h] (e : g = h) :
    schemeDeltaDimension C g = schemeDeltaDimension C h := by
  subst e
  rfl

/-- Delta-dimension is invariant under precomposition with an isomorphism: an isomorphism is a
closed immersion whose image is everything, as is the identity. -/
theorem schemeDeltaDimension_comp_iso (C : ChowSituation.{u}) {A Y : Scheme.{u}} (e : A ≅ Y)
    (p : Y ⟶ C.S) [LocallyOfFiniteType p] :
    schemeDeltaDimension C (e.hom ≫ p) = schemeDeltaDimension C p := by
  have hrange : Set.range e.hom = Set.range (𝟙 Y) := by
    refine (Set.range_eq_univ.mpr fun y ↦ ⟨e.inv y, ?_⟩).trans
      (Set.range_eq_univ.mpr fun y ↦ ⟨y, rfl⟩).symm
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  refine (schemeDeltaDimension_eq_of_equal_ranges C p e.hom (𝟙 Y) hrange).trans ?_
  exact schemeDeltaDimension_congr C (Category.id_comp p)

/-- The fibre of `W` along a closed-immersion section of `X ×_S 𝐏¹_S ⟶ X`, read over the base
`S` through `X`, has the same delta-dimension as the divisor it cuts on `W`, read over the base
through `W`. -/
private theorem schemeDeltaDimension_comap_section_eq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (W : (projectiveLineProduct f).IdealSheafData)
    (s : X ⟶ projectiveLineProduct f) [IsClosedImmersion s]
    (hs : s ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) = 𝟙 X) :
    schemeDeltaDimension C ((W.comap s).subschemeι ≫ f) =
      schemeDeltaDimension C
        (((Scheme.IdealSheafData.vanishingIdeal
            ⟨closure (Set.range s), isClosed_closure⟩).comap W.subschemeι).subschemeι ≫
          familyBase f W) := by
  have hdim := schemeDeltaDimension_eq_of_equal_ranges C
    (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f)
    ((W.comap s).subschemeι ≫ s)
    (((Scheme.IdealSheafData.vanishingIdeal
      ⟨closure (Set.range s), isClosed_closure⟩).comap W.subschemeι).subschemeι ≫ W.subschemeι)
    (range_comap_section_eq f W s)
  have hA : ((W.comap s).subschemeι ≫ s) ≫
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) =
      (W.comap s).subschemeι ≫ f := by
    rw [Category.assoc, ← Category.assoc s, hs, Category.id_comp]
  exact (schemeDeltaDimension_congr C hA).symm.trans hdim

/-! ### The two bounds -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (W : (projectiveLineProduct f).IdealSheafData)

/-- The zero fibre of `W` in `X` and the zero divisor of `W` on `W` have the same
delta-dimension. -/
theorem schemeDeltaDimension_zeroFiber_eq_zeroDivisor :
    schemeDeltaDimension C ((zeroFiber f W).subschemeι ≫ f) =
      schemeDeltaDimension C ((zeroDivisor f W).subschemeι ≫ familyBase f W) :=
  schemeDeltaDimension_comap_section_eq C f W (zeroSection f) (zeroSection_comp_fst f)

/-- The infinity fibre of `W` in `X` and the infinity divisor of `W` on `W` have the same
delta-dimension. -/
theorem schemeDeltaDimension_infinityFiber_eq_infinityDivisor :
    schemeDeltaDimension C ((infinityFiber f W).subschemeι ≫ f) =
      schemeDeltaDimension C ((infinityDivisor f W).subschemeι ≫ familyBase f W) :=
  schemeDeltaDimension_comap_section_eq C f W (infinitySection f) (infinitySection_comp_fst f)

/-- `(k + 1) - 1 = k`, as extended integers. -/
theorem coe_add_neg_one (k : ℤ) : ((k + 1 : ℤ) : EInt) + (-1 : ℤ) = (k : EInt) := by
  rw [← coe_add_coe_eq_coe_add, show k + 1 + (-1 : ℤ) = k by omega]

/-- A closed subscheme with the same delta-dimension as an effective Cartier divisor on `W` has
delta-dimension at most `k`, when `W` has relative dimension `k + 1`. -/
private theorem schemeDeltaDimension_le_of_eq_cartierDivisor [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (D : W.subscheme.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    {F : Scheme.{u}} (g : F ⟶ C.S) [LocallyOfFiniteType g]
    (h : schemeDeltaDimension C g = schemeDeltaDimension C (D.subschemeι ≫ familyBase f W)) :
    schemeDeltaDimension C g ≤ (k : EInt) := by
  refine h.le.trans ((schemeDeltaDimension_isEffectiveCartierDivisor_le C (familyBase f W) D
    hD).trans ?_)
  rw [schemeDeltaDimension_familyBase C f W hDim, coe_add_neg_one]

/-- **The delta-dimension bound on the zero fibre.** For an integral closed subscheme
`W ⊆ X ×_S 𝐏¹_S` of relative dimension `k + 1` over the base and not contained in the image of
the zero section, the zero fibre of `W` has delta-dimension at most `k`.

The zero divisor of `W` is an effective Cartier divisor on `W` by Stacks 02S4 part (1), so it has
delta-dimension at most `dim_δ(W) - 1 = k` by Stacks 02RK, and the zero fibre has the same
delta-dimension because it has the same image in `X ×_S 𝐏¹_S`. -/
theorem schemeDeltaDimension_zeroFiber_le [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f)) :
    schemeDeltaDimension C ((zeroFiber f W).subschemeι ≫ f) ≤ (k : EInt) := by
  exact schemeDeltaDimension_le_of_eq_cartierDivisor C f W hDim _
    (zeroDivisor_isEffectiveCartierDivisor f W h₀) _
    (schemeDeltaDimension_zeroFiber_eq_zeroDivisor C f W)

/-- **The delta-dimension bound on the infinity fibre.** The infinity-section twin of
`Stacks.Chow.schemeDeltaDimension_zeroFiber_le`. -/
theorem schemeDeltaDimension_infinityFiber_le [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    schemeDeltaDimension C ((infinityFiber f W).subschemeι ≫ f) ≤ (k : EInt) := by
  exact schemeDeltaDimension_le_of_eq_cartierDivisor C f W hDim _
    (infinityDivisor_isEffectiveCartierDivisor f W hInf) _
    (schemeDeltaDimension_infinityFiber_eq_infinityDivisor C f W)

end Stacks.Chow

end
