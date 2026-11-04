module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSymmetricPower
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMap
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank

/-!
# Hilbert families of points over an algebraically closed field

For a separated smooth relative curve `X` over a field `k`, the family `[x₁] + ⋯ + [xₙ]` of a
tuple of points is compatible with base change, and over an algebraically closed field every
degree-`d` Hilbert family over `Spec k` is of this form.

## Main results

* `Stacks.Hilbert.baseChange_familyOfPoints`: the base change of `[x₁] + ⋯ + [xₙ]` along
  `g` is `[g ≫ x₁] + ⋯ + [g ≫ xₙ]`.
* `Stacks.Hilbert.exists_familyOfPoints_eq`: over an algebraically closed field every Hilbert
  family over `Spec k` is a sum of rational points.

## References

* [Stacks Project, Tag 0B9F](https://stacks.math.columbia.edu/tag/0B9F)
* [Stacks Project, Tag 0B9G](https://stacks.math.columbia.edu/tag/0B9G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-- **The family of a tuple of points is compatible with base change**: the base change of
`[x₁] + ⋯ + [xₙ]` along `g : T' ⟶ T` is `[g ≫ x₁] + ⋯ + [g ≫ xₙ]`. -/
theorem baseChange_familyOfPoints {S : Scheme.{u}} (X : Over S) [SmoothOfRelativeDimension 1 X.hom]
    [IsSeparated X.hom] {T' T : Over S} (g : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ X)) :
    Stacks.Hilbert.baseChange X g (familyOfPoints X T x) =
      familyOfPoints X T' fun i => g ≫ x i := by
  refine HilbertFamily.ext ?_
  show (familyOfPoints X T x).ideal.comap (familyBaseChangeMap X g) = _
  rw [familyOfPoints_ideal, familyOfPoints_ideal, Stacks.IdealSheaf.comap_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := isClosedImmersion_pointGraph_of_isSeparated X _ (x i)
  exact pointIdeal_comap_familyBaseChangeMap X g _

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The point `Spec k` as a scheme over `Spec k`. -/
abbrev fieldPoint (k : Type u) [Field k] : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))

/-- **A Hilbert family over an algebraically closed field is a sum of rational points.** Let
`X` be a separated scheme smooth of relative dimension one and locally of finite type over an
algebraically closed field `k`. Every degree-`d` Hilbert family of `X` over `Spec k` is the sum
`[x₁] + ⋯ + [x_d]` of `d` rational points. -/
theorem exists_familyOfPoints_eq (X : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 X.hom]
    [IsSeparated X.hom] :
    ∀ (d : ℕ) (Z : HilbertFamily X (fieldPoint k) d),
      ∃ x : Fin d → (fieldPoint k ⟶ X), familyOfPoints X (fieldPoint k) x = Z := by
  have := SmoothOfRelativeDimension.smooth 1 X.hom
  have hlft : LocallyOfFiniteType X.hom := inferInstance
  intro d
  induction d with
  | zero =>
    intro Z
    refine ⟨Fin.elim0, HilbertFamily.ext ?_⟩
    rw [Z.ideal_eq_top]
    exact HilbertFamily.ideal_eq_top _
  | succ d ih =>
    intro Z
    set B := ((Over.pullback (fieldPoint k).hom).obj X).left
    set p : B ⟶ X.left := pullback.fst X.hom (𝟙 (Spec (.of k)))
    have hp : IsIso p := inferInstance
    have h1 := Z.isFiniteLocallyFreeOfRank
    obtain ⟨hfin, hflat, -⟩ :=
      (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
        (Z.ideal.subschemeι ≫ ((Over.pullback (fieldPoint k).hom).obj X).hom)).mp
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (d + 1))
    have hne : Nonempty Z.ideal.subscheme := by
      by_contra hcon
      have : IsEmpty Z.ideal.subscheme := not_nonempty_iff.mp hcon
      have h0 := Stacks.Morphisms.isFiniteLocallyFreeOfRank_zero_of_isEmpty_source
        (Z.ideal.subschemeι ≫ ((Over.pullback (fieldPoint k).hom).obj X).hom)
      let : IsFinite (Z.ideal.subschemeι ≫ ((Over.pullback (fieldPoint k).hom).obj X).hom) := hfin
      let : Flat (Z.ideal.subschemeι ≫ ((Over.pullback (fieldPoint k).hom).obj X).hom) := hflat
      obtain ⟨s⟩ := (inferInstance : Nonempty (Spec (.of k)))
      have e0 := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ 0).mp h0 s
      have e1 := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).mp h1 s
      omega
    have : JacobsonSpace (fieldPoint k).left := inferInstanceAs (JacobsonSpace (Spec (.of k)))
    have := LocallyOfFiniteType.jacobsonSpace
      (Z.ideal.subschemeι ≫ ((Over.pullback (fieldPoint k).hom).obj X).hom)
    obtain ⟨w, -, hw⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set Z.ideal.subscheme))
      Set.univ_nonempty isClosed_univ.isLocallyClosed
    set z := Z.ideal.subschemeι w
    have hz : IsClosed {p z} := by
      have h1 : IsClosed (Z.ideal.subschemeι '' {w}) :=
        Z.ideal.subschemeι.isClosedEmbedding.isClosedMap _ hw
      have h2 := (asIso p).hom.homeomorph.isClosedMap _ h1
      simpa [Set.image_singleton] using h2
    set x₀ := pointOfClosedPoint X.hom (p z) hz
    let x₀' : fieldPoint k ⟶ X := Over.homMk x₀ (pointOfClosedPoint_comp _ _ _)
    have hgraph : Set.range (pointGraph X (fieldPoint k) x₀') ⊆ (Z.ideal.support : Set B) := by
      rintro _ ⟨t, rfl⟩
      have hpt : pointGraph X (fieldPoint k) x₀' t = z := by
        apply (asIso p).hom.homeomorph.injective
        show p (pointGraph X (fieldPoint k) x₀' t) = p z
        rw [← Scheme.Hom.comp_apply]
        have hc : pointGraph X (fieldPoint k) x₀' ≫ pullback.fst X.hom (𝟙 _) = x₀ :=
          pullback.lift_fst _ _ _
        show (pointGraph X (fieldPoint k) x₀' ≫ pullback.fst X.hom (𝟙 _)) t = p z
        rw [hc]
        exact pointOfClosedPoint_apply _ _ _ _
      rw [hpt, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w, rfl⟩
    have : IsReduced (fieldPoint k).left := inferInstanceAs (IsReduced (Spec (.of k)))
    obtain ⟨g', hg'⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
      Z.ideal (pointGraph X (fieldPoint k) x₀')).2 hgraph
    have hle : Z.ideal ≤ pointIdeal X (fieldPoint k) x₀' := by
      rw [pointIdeal, ← hg']
      exact Z.ideal.ker_subschemeι.symm.le.trans (Scheme.Hom.le_ker_comp _ _)
    obtain ⟨D', hD'⟩ := exists_familyAddPoint_eq Z x₀' hle
    obtain ⟨x', hx'⟩ := ih D'
    refine ⟨Fin.cons x₀' x', HilbertFamily.ext ?_⟩
    rw [familyOfPoints_ideal, Fin.prod_univ_succ, Fin.cons_zero, hD', ← hx',
      familyOfPoints_ideal, mul_comm]
    simp only [Fin.cons_succ]

end Stacks.Hilbert
