module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Intersection.CohenMacaulayIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.ProductOverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothAscent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Composition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionBasePoint
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphCodimension
public import StacksFrontier.RingTheory.CohenMacaulay.Witnesses

/-!
# Unit laws and graphs for composition of correspondences

Let `k` be a field and let `X`, `Y`, `Z` be schemes smooth and separated over `k`, of constant
dimensions. Stacks 0FG2 shows that the class `[Δ_X] = [Γ_{id_X}] ∈ Corr⁰(X, X)` of the diagonal is
a two-sided unit for composition of correspondences, and Stacks 0FG3 that graphs compose,
`[Γ_g] ∘ [Γ_f] = [Γ_{f ∘ g}]` for `f : Y ⟶ X` and `g : Z ⟶ Y`. In both proofs the composition
`c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')` of the classes of closed subschemes `A ⊆ X × Y` and
`B ⊆ Y × Z` is computed by the formula of Stacks 0FFD for the proper intersection
`pr₁₂⁻¹(A) ∩ pr₂₃⁻¹(B)` inside `X × Y × Z`: this intersection is the fibre product `A ×_Y B` over
the middle factor, the Cohen–Macaulay hypotheses of 0FFD ascend to `pr₁₂⁻¹(A)` and `pr₂₃⁻¹(B)`
because these are smooth over `A` and `B`, and when `A ×_Y B ⟶ X × Z` is a closed immersion its
pushforward along `pr₁₃` is its own class. For `A = Δ_X` and `B = Z` the fibre product is `Z`
itself; for `A = Γ_f` and `B = Γ_g` it is `Γ_{f ∘ g}`.

The intersection products of composition are formed with a family of diagonal classes
`Δ : Stacks.WeilCohomology.DiagonalClassFamily k`. This file isolates the one property of `Δ`
that the computation uses, the proper-intersection formula of Stacks 0FFD for the products
formed with `Δ`, and proves the unit laws and the composition of graphs for every family having
it, both for schemes of constant dimension and for schemes of mixed dimension.

## Main definitions

* `Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula`: Stacks 0FFD, in the
  generality of Stacks 0FEA, for the intersection products formed with a family of diagonal
  classes.
* `Stacks.WeilCohomology.compositionFibre`: the fibre product `A ×_Y B` over the middle factor,
  identified with `pr₁₂⁻¹(A) ∩ pr₂₃⁻¹(B)` by `Stacks.WeilCohomology.compositionFibreIso`.
* `Stacks.WeilCohomology.diagonalCorr`: the diagonal correspondence `[Δ_X] ∈ Corr⁰(X, X)` of a
  quasi-compact scheme of mixed dimension, blockwise the diagonal of each equidimensional part.

## Main results

All names are in the namespace `Stacks.WeilCohomology` unless stated otherwise.

* `DiagonalClassFamily.ProperIntersectionFormula.compositionInt_closedSubscheme`:
  `[B] ∘ [A] = [A ×_Y B]` under the hypotheses of the proper-intersection formula.
* `DiagonalClassFamily.ProperIntersectionFormula.composition_graph_id` and
  `DiagonalClassFamily.ProperIntersectionFormula.composition_id_graph`:
  `c ∘ [Δ_X] = c` and `[Δ_Y] ∘ c = c` (Stacks 0FG2) for schemes of constant dimension.
* `DiagonalClassFamily.ProperIntersectionFormula.composition_graph_graph`:
  `[Γ_g] ∘ [Γ_f] = [Γ_{f ∘ g}]` (Stacks 0FG3) for schemes of constant dimension.
* `DiagonalClassFamily.ProperIntersectionFormula.comp_diagonalCorr` and
  `DiagonalClassFamily.ProperIntersectionFormula.diagonalCorr_comp`: the
  unit laws (Stacks 0FG2) for schemes of mixed dimension.
* `Stacks.Chow.cycleGroup_addMonoidHom_ext`: on a quasi-compact scheme, additive maps out of the
  group of `k`-cycles are determined by their values on integral closed subschemes.

## Implementation notes

**The property of the family of diagonal classes.** For the canonical family (Stacks 0FBR) the
proper-intersection formula is Stacks 0FFD, proved there from the Gysin formula of Stacks 0FEA
and from Stacks 045J. The canonical family is not yet available, so every result here is stated
for an arbitrary family having that property, and none carries a `@[stacks]` attribute. The
formula is stated as Stacks 0FEA gives it: `W` is smooth and separated of constant dimension
rather than integral, and the closed subschemes are only required to have all their irreducible
components of the given delta-dimension. The source's reduction needs this generality: after
replacing `X` and `Y` by the components containing the images of `Z`, the schemes `X × X × Y` and
`X × Z` are still not integral in general, since an integral scheme smooth over `k` need not be
geometrically irreducible.

**Cohen–Macaulay hypotheses.** The source verifies them at the generic point of the intersection
using the regularity of the local rings of `X × Z` and `Δ × Y`. Here they are deduced at every
point of maximal delta-dimension from the local rings of `A` and `B`, along the smooth morphisms
`pr₁₂⁻¹(A) ⟶ A` and `pr₂₃⁻¹(B) ⟶ B` (Stacks 0C0W): for an integral `Z` such a point is the generic
point, where the local ring is a field, and a scheme smooth over `k` has Cohen–Macaulay local
rings.

**Generators.** The source writes a correspondence as a finite combination of classes of integral
closed subschemes. A cycle on a scheme locally of finite type is a locally finite sum, and it is a
finite sum when the scheme is quasi-compact, which is what
`Stacks.Chow.cycleGroup_addMonoidHom_ext` uses. Accordingly the unit laws assume the scheme
that is not the middle factor of the composition to be quasi-compact, as it is for the smooth
projective schemes of the source; the middle factor is proper, as composition requires.

**Degrees.** The composition of correspondences of degrees `r` and `s` lands in degree `r + s`, so
the unit laws compare `c` with `c ∘ [Δ_X]` through
`Stacks.WeilCohomology.correspondenceCongr` (or `Stacks.WeilCohomology.corrCongr` in mixed
dimension) along `s = 0 + s` and `r = r + 0`.

## References

* [Stacks Project, Tag 0FG2](https://stacks.math.columbia.edu/tag/0FG2)
* [Stacks Project, Tag 0FG3](https://stacks.math.columbia.edu/tag/0FG3)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
* [Stacks Project, Tag 0FEA](https://stacks.math.columbia.edu/tag/0FEA)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.Chow

/-- **Cycles on a quasi-compact scheme are generated by integral closed subschemes.** Two additive
maps out of `Z_k(X)`, for `X` quasi-compact, agree as soon as they agree on the fundamental cycle
`[Z]_k` of every integral closed subscheme `Z ⊆ X` of delta-dimension `k`; here `Z` runs over the
reduced closures `Stacks.Chow.integralComponentAt x` of the points of relative dimension `k`. A
cycle on a quasi-compact scheme has finite support, so it is the finite sum of these fundamental
cycles weighted by its coefficients. -/
theorem cycleGroup_addMonoidHom_ext {C : ChowSituation.{u}} {X : Scheme.{u}} {p : X ⟶ C.S}
    [LocallyOfFiniteType p] [CompactSpace X] {k : ℤ} {M : Type*} [AddCommGroup M]
    {φ ψ : CycleGroup C p k →+ M}
    (h : ∀ x : X, relativeDimension C.dimensionFunction p x = k →
      φ (cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι k) =
        ψ (cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι k)) :
    φ = ψ := by
  classical
  ext α
  have hfin : (Function.support α.1).Finite := by
    simpa using LocallyFiniteSupport.finite_inter_support_of_isCompact
      α.1.locallyFiniteSupport isCompact_univ
  have hdim : ∀ x ∈ hfin.toFinset, relativeDimension C.dimensionFunction p x = k := fun x hx ↦
    (mem_cyclesOfDimension_iff_forall_point C p k α.1).1 α.2 x (hfin.mem_toFinset.1 hx)
  have hα : α = ∑ x ∈ hfin.toFinset, α.1 x •
      cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι k := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro y
    simp only [AddSubgroup.val_finset_sum, AddSubgroup.coe_zsmul,
      Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]
    by_cases hy : α.1 y = 0
    · rw [hy, eq_comm]
      refine Finset.sum_eq_zero fun x hx ↦ ?_
      have hne : y ≠ x := fun h ↦ hfin.mem_toFinset.1 hx (h ▸ hy)
      rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p k x hne, mul_zero]
    · have hmem : y ∈ hfin.toFinset := hfin.mem_toFinset.2 hy
      rw [Finset.sum_eq_single y (fun x _ hxy ↦ by
          rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p k x
            (Ne.symm hxy), mul_zero])
        (fun h ↦ (h hmem).elim),
        cycleAssociatedToClosedSubscheme_integralComponentAt_self C p y
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C p y
            (hdim y hmem)), mul_one]
  rw [hα, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [map_zsmul, map_zsmul, h x (hdim x hx)]

end Stacks.Chow

namespace Stacks.WeilCohomology

open Stacks.Chow

/-! ### The proper-intersection formula as a property of a family of diagonal classes -/

/-- A family of diagonal classes satisfies the **proper-intersection formula** (Stacks 0FFD, in
the generality of Stacks 0FEA) if the intersection product it defines computes proper
Cohen–Macaulay intersections: for `W` smooth and separated over `k` of constant dimension `N`,
closed subschemes `V₁, V₂ ⊆ W` all of whose irreducible components have delta-dimension `n₁`,
respectively `n₂`, and `d = n₁ + n₂ - N`, if

1. `dim_δ (V₁ ∩ V₂) ≤ d`, and
2. `𝒪_{V₁,ξ}` and `𝒪_{V₂,ξ}` are Cohen–Macaulay at every `ξ ∈ V₁ ∩ V₂` with `δ(ξ) = d`,

then `[V₁]_{n₁} · [V₂]_{n₂} = [V₁ ∩ V₂]_d` in `CH_d(W)`, where `V₁ ∩ V₂ = V₁ ×_W V₂` is the
scheme-theoretic intersection.

For the canonical family of diagonal classes (Stacks 0FBR) this is Stacks 0FFD, proved there from
Stacks 0FEA and Stacks 045J; that instance is not yet available, since the canonical family is
not yet constructed. -/
def DiagonalClassFamily.ProperIntersectionFormula {k : Type u} [Field k]
    (Δ : DiagonalClassFamily k) : Prop :=
  ∀ {W V₁ V₂ : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
    [Smooth sW] [IsSeparated sW] (N : ℕ) (hN : RelativeDimension sW N) (i₁ : V₁ ⟶ W)
    [IsClosedImmersion i₁] (i₂ : V₂ ⟶ W) [IsClosedImmersion i₂] (n₁ n₂ d : ℤ)
    (hd : n₁ + n₂ - N = d),
    (∀ T : irreducibleComponents V₁, deltaDimension (fieldChowSituation k) (i₁ ≫ sW)
        ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = n₁) →
    (∀ T : irreducibleComponents V₂, deltaDimension (fieldChowSituation k) (i₂ ≫ sW)
        ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = n₂) →
    schemeDeltaDimension (fieldChowSituation k) (Limits.pullback.fst i₁ i₂ ≫ i₁ ≫ sW) ≤ (d : EInt) →
    Intersection.CohenMacaulayAtIntersection k sW i₁ i₂ d →
    chowGroupDegreeEquiv (fieldChowSituation k) sW hd
        (selfIntersectionProduct (fieldChowSituation k)
            (fieldChowSituation_dimensionFunction_of_isClosed k)
          (fieldGysinSystem k) sW N (Δ sW N hN) n₁ n₂
          (QuotientAddGroup.mk
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sW i₁ n₁))
          (QuotientAddGroup.mk
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sW i₂ n₂))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sW
        (Limits.pullback.fst i₁ i₂ ≫ i₁) d)

/-! ### The fibre product over the middle factor -/

section Fibre

variable {S X Y Z A B : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}
  (a : A ⟶ Limits.pullback sX sY) (b : B ⟶ Limits.pullback sY sZ)

/-- The fibre product `A ×_Y B` of closed subschemes `A ⊆ X × Y` and `B ⊆ Y × Z` over the middle
factor `Y`. It is the scheme-theoretic intersection `pr₁₂⁻¹(A) ∩ pr₂₃⁻¹(B)` inside `X × Y × Z`
(`Stacks.WeilCohomology.compositionFibreIso`). -/
abbrev compositionFibre : Scheme.{u} :=
  Limits.pullback (a ≫ pullback.snd sX sY) (b ≫ pullback.fst sY sZ)

/-- The two maps `A ×_Y B ⟶ S` through `A` and through `B` agree. -/
theorem compositionFibre_condition :
    pullback.fst (a ≫ pullback.snd sX sY) (b ≫ pullback.fst sY sZ) ≫ a ≫ prodBase sX sY =
      (pullback.snd (a ≫ pullback.snd sX sY) (b ≫ pullback.fst sY sZ) ≫ b ≫
        pullback.snd sY sZ) ≫ sZ := by
  simp only [prodBase, Category.assoc]
  rw [pullback.condition (f := sX), ← Category.assoc a, ← Category.assoc,
    pullback.condition (f := a ≫ pullback.snd sX sY), Category.assoc, Category.assoc,
    pullback.condition (f := sY)]

/-- The inclusion `A ×_Y B ⟶ X × Y × Z`, `(α, β) ↦ (a(α), pr₂ b(β))`. -/
def compositionFibre.toTriple : compositionFibre a b ⟶ tripleProduct sX sY sZ :=
  pullback.lift (pullback.fst _ _ ≫ a) (pullback.snd _ _ ≫ b ≫ pullback.snd sY sZ)
    (compositionFibre_condition a b)

/-- The morphism `A ×_Y B ⟶ X × Z`, `(α, β) ↦ (pr₁ a(α), pr₂ b(β))`. -/
def compositionFibre.toProduct : compositionFibre a b ⟶ Limits.pullback sX sZ :=
  pullback.lift (pullback.fst _ _ ≫ a ≫ pullback.fst sX sY)
    (pullback.snd _ _ ≫ b ≫ pullback.snd sY sZ)
    (by simpa only [prodBase, Category.assoc] using compositionFibre_condition a b)

/-- `pr₁₂` of the inclusion of `A ×_Y B` is the inclusion of `A`. -/
@[reassoc (attr := simp)]
theorem compositionFibre.toTriple_pr₁₂ :
    compositionFibre.toTriple a b ≫ pr₁₂ sX sY sZ = pullback.fst _ _ ≫ a :=
  pullback.lift_fst _ _ _

/-- The third coordinate of the inclusion of `A ×_Y B` is the second coordinate of `B`. -/
@[reassoc (attr := simp)]
theorem compositionFibre.toTriple_snd :
    compositionFibre.toTriple a b ≫ pullback.snd (prodBase sX sY) sZ =
      pullback.snd _ _ ≫ b ≫ pullback.snd sY sZ :=
  pullback.lift_snd _ _ _

/-- `pr₂₃` of the inclusion of `A ×_Y B` is the inclusion of `B`. -/
@[reassoc (attr := simp)]
theorem compositionFibre.toTriple_pr₂₃ :
    compositionFibre.toTriple a b ≫ pr₂₃ sX sY sZ = pullback.snd _ _ ≫ b := by
  apply pullback.hom_ext
  · rw [Category.assoc, pr₂₃_fst, compositionFibre.toTriple_pr₁₂_assoc, pullback.condition,
      Category.assoc]
  · rw [Category.assoc, pr₂₃_snd, compositionFibre.toTriple_snd, Category.assoc]

/-- `pr₁₃` of the inclusion of `A ×_Y B` is the morphism `A ×_Y B ⟶ X × Z`. -/
theorem compositionFibre.toTriple_pr₁₃ :
    compositionFibre.toTriple a b ≫ pr₁₃ sX sY sZ = compositionFibre.toProduct a b := by
  apply pullback.hom_ext
  · rw [Category.assoc, pr₁₃_fst, compositionFibre.toTriple_pr₁₂_assoc,
      compositionFibre.toProduct, pullback.lift_fst]
  · rw [Category.assoc, pr₁₃_snd, compositionFibre.toTriple_snd,
      compositionFibre.toProduct, pullback.lift_snd]

/-- The comparison morphism from the intersection `pr₁₂⁻¹(A) ∩ pr₂₃⁻¹(B)` to `A ×_Y B`. -/
def compositionFibreHom :
    (Limits.pullback (pullback.fst (pr₁₂ sX sY sZ) a) (pullback.fst (pr₂₃ sX sY sZ) b) :
      Scheme.{u}) ⟶ compositionFibre a b :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
    simp only [Category.assoc]
    rw [← pullback.condition_assoc (f := pr₁₂ sX sY sZ) (g := a), ← pr₂₃_fst,
      ← pullback.condition_assoc (f := pr₂₃ sX sY sZ) (g := b), pullback.condition_assoc])

/-- The `A`-coordinate of the comparison morphism. -/
@[reassoc (attr := simp)]
theorem compositionFibreHom_fst :
    compositionFibreHom a b ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.snd _ _ :=
  pullback.lift_fst _ _ _

/-- The `B`-coordinate of the comparison morphism. -/
@[reassoc (attr := simp)]
theorem compositionFibreHom_snd :
    compositionFibreHom a b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The comparison morphism is compatible with the inclusions into `X × Y × Z`. -/
@[reassoc]
theorem compositionFibreHom_toTriple :
    compositionFibreHom a b ≫ compositionFibre.toTriple a b =
      pullback.fst _ _ ≫ pullback.fst (pr₁₂ sX sY sZ) a := by
  apply pullback.hom_ext
  · rw [Category.assoc, compositionFibre.toTriple_pr₁₂, compositionFibreHom_fst_assoc,
      Category.assoc, ← pullback.condition]
  · rw [Category.assoc, compositionFibre.toTriple_snd, compositionFibreHom_snd_assoc]
    simp only [Category.assoc]
    rw [← pullback.condition_assoc (f := pr₂₃ sX sY sZ) (g := b), pr₂₃_snd,
      ← pullback.condition_assoc]

/-- The inverse comparison morphism, from `A ×_Y B` to the intersection. -/
def compositionFibreInv : compositionFibre a b ⟶
    (Limits.pullback (pullback.fst (pr₁₂ sX sY sZ) a) (pullback.fst (pr₂₃ sX sY sZ) b) :
      Scheme.{u}) :=
  pullback.lift
    (pullback.lift (compositionFibre.toTriple a b) (pullback.fst _ _)
      (compositionFibre.toTriple_pr₁₂ a b))
    (pullback.lift (compositionFibre.toTriple a b) (pullback.snd _ _)
      (compositionFibre.toTriple_pr₂₃ a b))
    (by rw [pullback.lift_fst, pullback.lift_fst])

/-- The scheme-theoretic intersection of `pr₁₂⁻¹(A)` and `pr₂₃⁻¹(B)` inside `X × Y × Z` is the
fibre product `A ×_Y B` over the middle factor. -/
def compositionFibreIso :
    (Limits.pullback (pullback.fst (pr₁₂ sX sY sZ) a) (pullback.fst (pr₂₃ sX sY sZ) b) :
      Scheme.{u}) ≅ compositionFibre a b where
  hom := compositionFibreHom a b
  inv := compositionFibreInv a b
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, compositionFibreInv, pullback.lift_fst_assoc,
          pullback.lift_fst, compositionFibreHom_toTriple, Category.id_comp]
      · rw [Category.assoc, Category.assoc, compositionFibreInv, pullback.lift_fst_assoc,
          pullback.lift_snd, compositionFibreHom_fst, Category.id_comp]
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, compositionFibreInv, pullback.lift_snd_assoc,
          pullback.lift_fst, compositionFibreHom_toTriple, Category.id_comp, pullback.condition]
      · rw [Category.assoc, Category.assoc, compositionFibreInv, pullback.lift_snd_assoc,
          pullback.lift_snd, compositionFibreHom_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, compositionFibreHom_fst, compositionFibreInv, pullback.lift_fst_assoc,
        pullback.lift_snd, Category.id_comp]
    · rw [Category.assoc, compositionFibreHom_snd, compositionFibreInv, pullback.lift_snd_assoc,
        pullback.lift_snd, Category.id_comp]

/-- The forward map of `Stacks.WeilCohomology.compositionFibreIso`. -/
@[simp]
theorem compositionFibreIso_hom : (compositionFibreIso a b).hom = compositionFibreHom a b := rfl

end Fibre

/-! ### Dimensions and Cohen–Macaulay local rings along flat and smooth morphisms -/

section Helpers

/-- The delta-dimension of an irreducible closed subset depends on the structure morphism only
through its value. -/
theorem deltaDimension_congr {C : ChowSituation.{u}} {T : Scheme.{u}} {q g : T ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType g] (h : q = g)
    (V : TopologicalSpace.IrreducibleCloseds T) :
    deltaDimension C q V = deltaDimension C g V := by
  subst h
  rfl

/-- Along a flat morphism `g : P ⟶ T` of relative dimension `r`, if every irreducible component
of `T` has delta-dimension `m` then every irreducible component of `P` has delta-dimension
`m + r` (Stacks 02R8). -/
theorem deltaDimension_irreducibleComponent_of_flat {C : ChowSituation.{u}} {P T : Scheme.{u}}
    (g : P ⟶ T) [LocallyOfFiniteType g] [Flat g] (q : T ⟶ C.S) [LocallyOfFiniteType q] (r : ℕ)
    (hg : RelativeDimension g r) {m : ℤ}
    (hT : ∀ V : irreducibleComponents T,
      deltaDimension C q ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = m)
    (W : irreducibleComponents P) :
    deltaDimension C (g ≫ q) ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents _ W.2⟩ =
      m + r := by
  obtain ⟨V, hV⟩ := exists_irreducibleComponent_map_genericPoint g W
  rw [deltaDimension_irreducibleComponent_eq_add C g q r hg W V hV, hT V]

/-- If every irreducible component of a scheme has delta-dimension `m`, its delta-dimension is at
most `m`. -/
theorem schemeDeltaDimension_le_of_forall_irreducibleComponent {C : ChowSituation.{u}}
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] {m : ℤ}
    (hT : ∀ V : irreducibleComponents T,
      deltaDimension C q ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = m) :
    schemeDeltaDimension C q ≤ (m : EInt) :=
  iSup_le fun V ↦ (congrArg (fun z : ℤ ↦ (z : EInt)) (hT V)).le

/-- Every irreducible component of a scheme of constant relative dimension `e` over a field has
delta-dimension `e`. -/
theorem deltaDimension_irreducibleComponent_of_relativeDimension (k : Type u) [Field k]
    {T : Scheme.{u}} (q : T ⟶ Spec (.of k)) [LocallyOfFiniteType q] (e : ℕ)
    (hq : RelativeDimension q e) (V : irreducibleComponents T) :
    deltaDimension (fieldChowSituation k) q
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = e := by
  refine relativeDimension_of_mem_irreducibleComponents_of_relativeDimension k q e hq _ ?_
  rw [(V.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ V.2)).def]
  exact V.2

/-- The local rings of a scheme smooth over a field are Cohen–Macaulay. -/
theorem isCohenMacaulayLocalRing_stalk_of_smooth (k : Type u) [Field k] {T : Scheme.{u}}
    (q : T ⟶ Spec (.of k)) [Smooth q] (t : T) :
    letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
    IsCohenMacaulayLocalRing (T.presheaf.stalk t) :=
  (Scheme.Hom.isCohenMacaulayAt_iff_of_field k q t).mp
    (((isCohenMacaulay_iff_flat_and_fibers q _).mpr
      ⟨inferInstance, isCohenMacaulay_fiber_of_smooth q⟩) t)

/-- Along a smooth morphism `g : P ⟶ T` of schemes locally of finite type over a field, the local
ring of `P` at a point is Cohen–Macaulay as soon as the local ring of `T` at its image is. -/
theorem isCohenMacaulayLocalRing_stalk_of_smooth_of_isCohenMacaulayLocalRing (k : Type u)
    [Field k] {P T : Scheme.{u}} (g : P ⟶ T) [Smooth g] (q : T ⟶ Spec (.of k))
    [LocallyOfFiniteType q] (p : P)
    (hT : letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
      IsCohenMacaulayLocalRing (T.presheaf.stalk (g p))) :
    letI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (g ≫ q)
    IsCohenMacaulayLocalRing (P.presheaf.stalk p) :=
  let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (g ≫ q)
  AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_of_smooth g p hT

end Helpers

/-! ### Composition of the classes of two closed subschemes -/

section Calculus

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
  [Smooth sX] [Smooth sY] [Smooth sZ] [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ]
  (Δ : DiagonalClassFamily k)

/-- On Chow groups, flat pullback carries the class of a closed subscheme of delta-dimension at
most `n` to the class of its scheme-theoretic inverse image (Stacks 02RB). -/
theorem flatPullbackChow_mk_cycleAssociatedToClosedSubscheme {C : ChowSituation.{u}}
    {X' X V : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (q : X' ⟶ X) [LocallyOfFiniteType q] [Flat q]
    (hbase : q ≫ sX = sX') (r : ℕ) (hq : RelativeDimension q r) (i : V ⟶ X)
    [IsClosedImmersion i] (n : ℤ) (hV : schemeDeltaDimension C (i ≫ sX) ≤ (n : EInt))
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX' sX q hbase r hq n) :
    flatPullbackChow C sX' sX q hbase r hq n hfac
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C sX i n)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C sX' (pullback.fst q i)
        (n + (r : ℤ))) := by
  rw [← flatPullback_cycleAssociatedToClosedSubscheme_of_le C sX' sX q hbase r hq i n hV]
  rfl

/-- **The composition of the classes of two closed subschemes is a proper intersection.** Let
`a : A ⟶ X × Y` and `b : B ⟶ Y × Z` be closed subschemes of delta-dimensions at most `e - r` and
`f - s`. If the inverse images `pr₁₂⁻¹(A)` and `pr₂₃⁻¹(B)` in `X × Y × Z` meet properly in the
sense of `Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula`, then for a family
of diagonal classes satisfying that formula the class `pr₁₂^*[A] · pr₂₃^*[B]` is the class of the
scheme-theoretic intersection `pr₁₂⁻¹(A) ∩ pr₂₃⁻¹(B)`. -/
theorem compositionCycle_closedSubscheme
    (hΔ : Δ.ProperIntersectionFormula) {d e f : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f) (r s : ℤ) {A B : Scheme.{u}}
    (a : A ⟶ Limits.pullback sX sY) [IsClosedImmersion a] (b : B ⟶ Limits.pullback sY sZ)
    [IsClosedImmersion b]
    (ha : schemeDeltaDimension (fieldChowSituation k) (a ≫ prodBase sX sY) ≤
      (((e : ℤ) - r : ℤ) : EInt))
    (hb : schemeDeltaDimension (fieldChowSituation k) (b ≫ prodBase sY sZ) ≤
      (((f : ℤ) - s : ℤ) : EInt))
    (h₁ : ∀ T : irreducibleComponents (Limits.pullback (pr₁₂ sX sY sZ) a : Scheme.{u}),
      deltaDimension (fieldChowSituation k) (pullback.fst (pr₁₂ sX sY sZ) a ≫ tripleBase sX sY sZ)
        ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = (e : ℤ) - r + f)
    (h₂ : ∀ T : irreducibleComponents (Limits.pullback (pr₂₃ sX sY sZ) b : Scheme.{u}),
      deltaDimension (fieldChowSituation k) (pullback.fst (pr₂₃ sX sY sZ) b ≫ tripleBase sX sY sZ)
        ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = (f : ℤ) - s + d)
    (h₃ : schemeDeltaDimension (fieldChowSituation k)
      (pullback.fst (pullback.fst (pr₁₂ sX sY sZ) a) (pullback.fst (pr₂₃ sX sY sZ) b) ≫
        pullback.fst (pr₁₂ sX sY sZ) a ≫ tripleBase sX sY sZ) ≤ (((f : ℤ) - (r + s) : ℤ) : EInt))
    (h₄ : Intersection.CohenMacaulayAtIntersection k (tripleBase sX sY sZ)
      (pullback.fst (pr₁₂ sX sY sZ) a) (pullback.fst (pr₂₃ sX sY sZ) b) ((f : ℤ) - (r + s))) :
    compositionCycle k sX sY sZ Δ hX hY hZ r s
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) a ((e : ℤ) - r)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sY sZ) b ((f : ℤ) - s))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (tripleBase sX sY sZ)
        (pullback.fst (pullback.fst (pr₁₂ sX sY sZ) a) (pullback.fst (pr₂₃ sX sY sZ) b) ≫
          pullback.fst (pr₁₂ sX sY sZ) a) ((f : ℤ) - (r + s))) := by
  simp only [compositionCycle, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    AddMonoidHom.coe_toIntLinearMap, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv]
  rw [flatPullbackChow_mk_cycleAssociatedToClosedSubscheme (tripleBase sX sY sZ) (prodBase sX sY)
      (pr₁₂ sX sY sZ) (pr₁₂_comp_prodBase sX sY sZ) f (relativeDimension_pr₁₂ k sX sY sZ hZ) a _ ha,
    flatPullbackChow_mk_cycleAssociatedToClosedSubscheme (tripleBase sX sY sZ) (prodBase sY sZ)
      (pr₂₃ sX sY sZ) (pr₂₃_comp_prodBase sX sY sZ) d (relativeDimension_pr₂₃ k sX sY sZ hX) b _ hb]
  exact hΔ (tripleBase sX sY sZ) _ (relativeDimension_tripleBase k sX sY sZ hX hY hZ) _ _ _ _ _
    _ h₁ h₂ h₃ h₄

/-- **The composition of the classes of two closed subschemes, read on the fibre product over the
middle factor.** Let `a : A ⟶ X × Y` and `b : B ⟶ Y × Z` be closed subschemes all of whose
irreducible components have delta-dimension `e - r`, respectively `f - s`, and let
`A ×_Y B ⟶ X × Z` be a closed immersion. If `dim_δ (A ×_Y B) ≤ f - (r + s)` and the local rings
of `A` and `B` are Cohen–Macaulay at the images of the points of `A ×_Y B` of delta-dimension
`f - (r + s)`, then, for a family of diagonal classes satisfying the proper-intersection formula,
`[B] ∘ [A] = [A ×_Y B]` in `CH_{f-(r+s)}(X × Z)`.

This is the computation of the proofs of Stacks 0FG2 and 0FG3: `A ×_Y B` is the
scheme-theoretic intersection `pr₁₂⁻¹(A) ∩ pr₂₃⁻¹(B)`, and the Cohen–Macaulay hypotheses ascend
to `pr₁₂⁻¹(A)` and `pr₂₃⁻¹(B)`, which are smooth over `A` and `B`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.compositionInt_closedSubscheme
    {Δ : DiagonalClassFamily k} (hΔ : Δ.ProperIntersectionFormula) [IsProper sY] {d e f : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f)
    (r s : ℤ) {A B : Scheme.{u}} (a : A ⟶ Limits.pullback sX sY) [IsClosedImmersion a]
    (b : B ⟶ Limits.pullback sY sZ) [IsClosedImmersion b]
    [IsClosedImmersion (compositionFibre.toProduct a b)]
    (hA : ∀ T : irreducibleComponents A, deltaDimension (fieldChowSituation k)
      (a ≫ prodBase sX sY) ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ =
        (e : ℤ) - r)
    (hB : ∀ T : irreducibleComponents B, deltaDimension (fieldChowSituation k)
      (b ≫ prodBase sY sZ) ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ =
        (f : ℤ) - s)
    (hdim : schemeDeltaDimension (fieldChowSituation k)
      (compositionFibre.toProduct a b ≫ prodBase sX sZ) ≤ (((f : ℤ) - (r + s) : ℤ) : EInt))
    (hCM : letI : IsLocallyNoetherian A :=
        LocallyOfFiniteType.isLocallyNoetherian (a ≫ prodBase sX sY)
      letI : IsLocallyNoetherian B :=
        LocallyOfFiniteType.isLocallyNoetherian (b ≫ prodBase sY sZ)
      ∀ x : compositionFibre a b,
        relativeDimension (fieldChowSituation k).dimensionFunction
            (compositionFibre.toProduct a b ≫ prodBase sX sZ) x = (f : ℤ) - (r + s) →
          IsCohenMacaulayLocalRing (A.presheaf.stalk
              ((pullback.fst (a ≫ pullback.snd sX sY) (b ≫ pullback.fst sY sZ)).base x)) ∧
            IsCohenMacaulayLocalRing (B.presheaf.stalk
              ((pullback.snd (a ≫ pullback.snd sX sY) (b ≫ pullback.fst sY sZ)).base x))) :
    compositionInt k sX sY sZ Δ hX hY hZ r s
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) a ((e : ℤ) - r)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sY sZ) b ((f : ℤ) - s))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sX sZ) (compositionFibre.toProduct a b) ((f : ℤ) - (r + s))) := by
  let : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian (a ≫ prodBase sX sY)
  let : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian (b ≫ prodBase sY sZ)
  have : Smooth (pr₂₃ sX sY sZ) :=
    MorphismProperty.of_isPullback (isPullback_pr₁₂_pr₂₃ sX sY sZ) inferInstance
  have hCMeq : ∀ {W : Scheme.{u}} [IsLocallyNoetherian W] {x y : W}, x = y →
      IsCohenMacaulayLocalRing (W.presheaf.stalk x) →
        IsCohenMacaulayLocalRing (W.presheaf.stalk y) := by
    intro W _ x y h hx
    subst h
    exact hx
  set φ := compositionFibreIso a b with hφ
  have hmor : φ.hom ≫ compositionFibre.toProduct a b ≫ prodBase sX sZ =
      pullback.fst (pullback.fst (pr₁₂ sX sY sZ) a) (pullback.fst (pr₂₃ sX sY sZ) b) ≫
        pullback.fst (pr₁₂ sX sY sZ) a ≫ tripleBase sX sY sZ := by
    rw [← compositionFibre.toTriple_pr₁₃, Category.assoc, pr₁₃_comp_prodBase, hφ,
      compositionFibreIso_hom, compositionFibreHom_toTriple_assoc]
  have ha := schemeDeltaDimension_le_of_forall_irreducibleComponent _ hA
  have hb := schemeDeltaDimension_le_of_forall_irreducibleComponent _ hB
  have h₁ : ∀ T : irreducibleComponents (Limits.pullback (pr₁₂ sX sY sZ) a : Scheme.{u}),
      deltaDimension (fieldChowSituation k)
          (pullback.fst (pr₁₂ sX sY sZ) a ≫ tripleBase sX sY sZ)
          ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = (e : ℤ) - r + f := by
    intro T
    rw [deltaDimension_congr (g := pullback.snd (pr₁₂ sX sY sZ) a ≫ a ≫ prodBase sX sY)
      (by rw [← pullback.condition_assoc])]
    exact deltaDimension_irreducibleComponent_of_flat _ _ f
      (relativeDimension_pullback_snd _ a f (relativeDimension_pr₁₂ k sX sY sZ hZ)) hA T
  have h₂ : ∀ T : irreducibleComponents (Limits.pullback (pr₂₃ sX sY sZ) b : Scheme.{u}),
      deltaDimension (fieldChowSituation k)
          (pullback.fst (pr₂₃ sX sY sZ) b ≫ tripleBase sX sY sZ)
          ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = (f : ℤ) - s + d := by
    intro T
    rw [deltaDimension_congr (g := pullback.snd (pr₂₃ sX sY sZ) b ≫ b ≫ prodBase sY sZ)
      (by rw [← pullback.condition_assoc, pr₂₃_comp_prodBase])]
    exact deltaDimension_irreducibleComponent_of_flat _ _ d
      (relativeDimension_pullback_snd _ b d (relativeDimension_pr₂₃ k sX sY sZ hX)) hB T
  have h₃ : schemeDeltaDimension (fieldChowSituation k)
      (pullback.fst (pullback.fst (pr₁₂ sX sY sZ) a) (pullback.fst (pr₂₃ sX sY sZ) b) ≫
        pullback.fst (pr₁₂ sX sY sZ) a ≫ tripleBase sX sY sZ) ≤
          (((f : ℤ) - (r + s) : ℤ) : EInt) := by
    rw [← schemeDeltaDimension_congr _ hmor, schemeDeltaDimension_comp_iso]
    exact hdim
  have h₄ : Intersection.CohenMacaulayAtIntersection k (tripleBase sX sY sZ)
      (pullback.fst (pr₁₂ sX sY sZ) a) (pullback.fst (pr₂₃ sX sY sZ) b)
      ((f : ℤ) - (r + s)) := by
    intro ζ hζ
    have hx : relativeDimension (fieldChowSituation k).dimensionFunction
        (compositionFibre.toProduct a b ≫ prodBase sX sZ) (φ.hom.base ζ) =
          (f : ℤ) - (r + s) := by
      rw [← relativeDimension_comp_closedImmersion, hmor]
      exact hζ
    obtain ⟨hA', hB'⟩ := hCM _ hx
    refine ⟨isCohenMacaulayLocalRing_stalk_of_smooth_of_isCohenMacaulayLocalRing k
      (pullback.snd (pr₁₂ sX sY sZ) a) (a ≫ prodBase sX sY) _ (hCMeq ?_ hA'),
      isCohenMacaulayLocalRing_stalk_of_smooth_of_isCohenMacaulayLocalRing k
      (pullback.snd (pr₂₃ sX sY sZ) b) (b ≫ prodBase sY sZ) _ (hCMeq ?_ hB')⟩
    · rw [← Scheme.Hom.comp_apply, hφ, compositionFibreIso_hom, compositionFibreHom_fst,
        Scheme.Hom.comp_apply]
    · rw [← Scheme.Hom.comp_apply, hφ, compositionFibreIso_hom, compositionFibreHom_snd,
        Scheme.Hom.comp_apply]
  have hι : IsClosedImmersion (compositionFibre.toTriple a b) := by
    rw [← Iso.inv_hom_id_assoc φ (compositionFibre.toTriple a b), hφ, compositionFibreIso_hom,
      compositionFibreHom_toTriple]
    infer_instance
  have hι₁₃ : IsClosedImmersion (compositionFibre.toTriple a b ≫ pr₁₃ sX sY sZ) := by
    rw [compositionFibre.toTriple_pr₁₃]
    infer_instance
  simp only [compositionInt, LinearMap.compr₂_apply, AddMonoidHom.coe_toIntLinearMap]
  rw [compositionCycle_closedSubscheme k sX sY sZ Δ hΔ hX hY hZ r s a b ha hb
      h₁ h₂ h₃ h₄,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ (compositionFibre.toTriple a b) φ
      (by rw [hφ, compositionFibreIso_hom, compositionFibreHom_toTriple])]
  refine (properChowPushforward_mk _ _ _ _ _ _ _ _).trans ?_
  rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
    cycleAssociatedToClosedSubscheme_congr _ _ _ _ (compositionFibre.toTriple_pr₁₃ a b)]
  rfl

end Calculus

/-! ### Integral closed subschemes -/

section Integral

/-- The class of a closed subscheme, transported along an equality of degrees, is its class in
the other degree. -/
theorem chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme {C : ChowSituation.{u}}
    {T V : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (i : V ⟶ T) [IsClosedImmersion i]
    {n n' : ℤ} (h : n = n') :
    chowGroupDegreeEquiv C q h (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C q i n)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C q i n') := by
  subst h
  rfl

/-- The unique irreducible component of an irreducible scheme of delta-dimension `m` has
delta-dimension `m`. -/
theorem deltaDimension_irreducibleComponent_of_irreducibleSpace {C : ChowSituation.{u}}
    {T : Scheme.{u}} [IrreducibleSpace T] (q : T ⟶ C.S) [LocallyOfFiniteType q] {m : ℤ}
    (hT : schemeDeltaDimension C q = (m : EInt)) (V : irreducibleComponents T) :
    deltaDimension C q ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = m := by
  have hV : (V : Set T) = Set.univ :=
    Set.eq_univ_of_univ_subset (V.2.2 (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _))
  rw [schemeDeltaDimension_eq_genericPoint] at hT
  rw [deltaDimension_eq_of_isGenericPoint C q _ (genericPoint T)
    (by change IsGenericPoint _ (V : Set T); rw [hV]; exact genericPoint_spec T)]
  exact WithBotTop.coe_injective hT

/-- In an irreducible scheme locally of finite type over the base, the only point whose relative
dimension is that of the generic point is the generic point. -/
theorem eq_genericPoint_of_relativeDimension_eq {C : ChowSituation.{u}} {T : Scheme.{u}}
    [IrreducibleSpace T] (q : T ⟶ C.S) [LocallyOfFiniteType q] {t : T}
    (h : relativeDimension C.dimensionFunction q t =
      relativeDimension C.dimensionFunction q (genericPoint T)) :
    t = genericPoint T := by
  by_contra hne
  obtain ⟨δ, hδ⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
    C.dimensionFunction q
  have hlt := δ.strictAnti_specializes (genericPoint_specializes t) (Ne.symm hne)
  rw [← hδ, ← hδ] at h
  omega

/-- The local ring of an integral scheme locally of finite type over a field at a point of
maximal relative dimension is Cohen–Macaulay: the point is the generic point, where the local
ring is the function field. -/
theorem isCohenMacaulayLocalRing_stalk_of_relativeDimension_eq (k : Type u) [Field k]
    {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ Spec (.of k)) [LocallyOfFiniteType q] {t : T}
    (h : relativeDimension (fieldChowSituation k).dimensionFunction q t =
      relativeDimension (fieldChowSituation k).dimensionFunction q (genericPoint T)) :
    letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
    IsCohenMacaulayLocalRing (T.presheaf.stalk t) := by
  let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
  obtain rfl := eq_genericPoint_of_relativeDimension_eq (C := fieldChowSituation k) q h
  exact Field.isCohenMacaulayLocalRing T.functionField

end Integral

/-! ### The unit laws and composition of graphs -/

section Laws

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
  [Smooth sX] [Smooth sY] [Smooth sZ] [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ]
  {Δ : DiagonalClassFamily k}

attribute [local instance] isClosedImmersion_graphMorphism

/-- **`c ∘ [Δ_X] = c` on the class of an integral closed subscheme.** For an integral closed
subscheme `Z ⊆ X × Y` of delta-dimension `e - s`, the composition of `[Z]` with the class of the
diagonal of `X` is `[Z]`. The intersection `Δ × Y ∩ X × Z` is the image of `Z` under
`(Δ, 1) : X × Y ⟶ X × X × Y`, and `pr₁₃` maps it isomorphically onto `Z`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.compositionInt_graph_id_mk
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sX] {d e : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (s : ℤ) {V : Scheme.{u}} [IsIntegral V]
    (i : V ⟶ Limits.pullback sX sY) [IsClosedImmersion i]
    (hV : schemeDeltaDimension (fieldChowSituation k) (i ≫ prodBase sX sY) =
      (((e : ℤ) - s : ℤ) : EInt)) :
    compositionInt k sX sX sY Δ hX hX hY 0 s
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sX) (graphMorphism sX sX (𝟙 X) (Category.id_comp sX)) ((d : ℤ) - 0)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) i ((e : ℤ) - s))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sX sY) i ((e : ℤ) - (0 + s))) := by
  set Γ := graphMorphism sX sX (𝟙 X) (Category.id_comp sX) with hΓ
  have hΓs : Γ ≫ pullback.snd sX sX = 𝟙 X := graphMorphism_snd _ _ _ _
  have hΓf : Γ ≫ pullback.fst sX sX = 𝟙 X := graphMorphism_fst _ _ _ _
  have : IsIso (Γ ≫ pullback.snd sX sX) := by rw [hΓs]; infer_instance
  have hκ : compositionFibre.toProduct Γ i = pullback.snd _ _ ≫ i := by
    apply pullback.hom_ext
    · rw [compositionFibre.toProduct, pullback.lift_fst, hΓf, Category.comp_id, Category.assoc]
      exact (Category.comp_id _).symm.trans
        ((congrArg (pullback.fst _ _ ≫ ·) hΓs).symm.trans pullback.condition)
    · rw [compositionFibre.toProduct, pullback.lift_snd, Category.assoc]
  have : IsClosedImmersion (compositionFibre.toProduct Γ i) := by rw [hκ]; infer_instance
  have hgen := hV
  rw [schemeDeltaDimension_eq_genericPoint] at hgen
  replace hgen := WithBotTop.coe_injective hgen
  rw [hΔ.compositionInt_closedSubscheme k sX sX sY hX hX hY 0 s Γ i
    (fun T ↦ by
      rw [deltaDimension_congr (g := sX)
        (by rw [hΓ, prodBase, ← Category.assoc, graphMorphism_fst, Category.id_comp]), sub_zero]
      exact deltaDimension_irreducibleComponent_of_relativeDimension k sX d hX T)
    (deltaDimension_irreducibleComponent_of_irreducibleSpace _ hV)
    (by
      rw [schemeDeltaDimension_congr _ (show compositionFibre.toProduct Γ i ≫ prodBase sX sY =
          (asIso (pullback.snd _ _)).hom ≫ i ≫ prodBase sX sY by
            rw [hκ, asIso_hom, Category.assoc]),
        schemeDeltaDimension_comp_iso, hV, zero_add])
    (fun x hx ↦ ⟨isCohenMacaulayLocalRing_stalk_of_smooth k sX _,
      isCohenMacaulayLocalRing_stalk_of_relativeDimension_eq k (i ≫ prodBase sX sY) (by
        rw [← relativeDimension_comp_closedImmersion, ← Category.assoc, ← hκ, hx, hgen,
          zero_add])⟩)]
  exact congrArg _ (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (asIso (pullback.snd _ _))
    hκ.symm _)

/-- **`[Δ_Y] ∘ c = c` on the class of an integral closed subscheme.** For an integral closed
subscheme `Z ⊆ X × Y` of delta-dimension `e - r`, the composition of the class of the diagonal of
`Y` with `[Z]` is `[Z]`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.compositionInt_mk_graph_id
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sY] {d e : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (r : ℤ) {V : Scheme.{u}} [IsIntegral V]
    (i : V ⟶ Limits.pullback sX sY) [IsClosedImmersion i]
    (hV : schemeDeltaDimension (fieldChowSituation k) (i ≫ prodBase sX sY) =
      (((e : ℤ) - r : ℤ) : EInt)) :
    compositionInt k sX sY sY Δ hX hY hY r 0
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) i ((e : ℤ) - r)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sY sY) (graphMorphism sY sY (𝟙 Y) (Category.id_comp sY)) ((e : ℤ) - 0))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sX sY) i ((e : ℤ) - (r + 0))) := by
  set Γ := graphMorphism sY sY (𝟙 Y) (Category.id_comp sY) with hΓ
  have hΓf : Γ ≫ pullback.fst sY sY = 𝟙 Y := graphMorphism_fst _ _ _ _
  have hΓs : Γ ≫ pullback.snd sY sY = 𝟙 Y := graphMorphism_snd _ _ _ _
  have : IsIso (Γ ≫ pullback.fst sY sY) := by rw [hΓf]; infer_instance
  have hκ : compositionFibre.toProduct i Γ = pullback.fst _ _ ≫ i := by
    apply pullback.hom_ext
    · rw [compositionFibre.toProduct, pullback.lift_fst, Category.assoc]
    · rw [compositionFibre.toProduct, pullback.lift_snd, hΓs, Category.comp_id, Category.assoc]
      exact (Category.comp_id _).symm.trans
        ((congrArg (pullback.snd _ _ ≫ ·) hΓf).symm.trans pullback.condition.symm)
  have : IsClosedImmersion (compositionFibre.toProduct i Γ) := by rw [hκ]; infer_instance
  have hgen := hV
  rw [schemeDeltaDimension_eq_genericPoint] at hgen
  replace hgen := WithBotTop.coe_injective hgen
  rw [hΔ.compositionInt_closedSubscheme k sX sY sY hX hY hY r 0 i Γ
    (deltaDimension_irreducibleComponent_of_irreducibleSpace _ hV)
    (fun T ↦ by
      rw [deltaDimension_congr (g := sY)
        (by rw [hΓ, prodBase, ← Category.assoc, graphMorphism_fst, Category.id_comp]), sub_zero]
      exact deltaDimension_irreducibleComponent_of_relativeDimension k sY e hY T)
    (by
      rw [schemeDeltaDimension_congr _ (show compositionFibre.toProduct i Γ ≫ prodBase sX sY =
          (asIso (pullback.fst _ _)).hom ≫ i ≫ prodBase sX sY by
            rw [hκ, asIso_hom, Category.assoc]),
        schemeDeltaDimension_comp_iso, hV, add_zero])
    (fun x hx ↦ ⟨isCohenMacaulayLocalRing_stalk_of_relativeDimension_eq k (i ≫ prodBase sX sY) (by
        rw [← relativeDimension_comp_closedImmersion, ← Category.assoc, ← hκ, hx, hgen,
          add_zero]),
      isCohenMacaulayLocalRing_stalk_of_smooth k sY _⟩)]
  exact congrArg _ (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (asIso (pullback.fst _ _))
    hκ.symm _)

/-- **`[Γ_g] ∘ [Γ_f] = [Γ_{f ∘ g}]` on integral Chow groups.** For morphisms `f : Y ⟶ X` and
`g : Z ⟶ Y` over `k`, the composition of the graph classes is the graph class of `g ≫ f`. The
intersection `Γ_f × Z ∩ X × Γ_g` is the image of `(f ∘ g, g, 1) : Z ⟶ X × Y × Z`, which `pr₁₃`
maps isomorphically onto `Γ_{f ∘ g}`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.compositionInt_graph_graph
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sY] {d e n : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ n) (f : Y ⟶ X) (hf : f ≫ sX = sY)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    compositionInt k sX sY sZ Δ hX hY hZ 0 0
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sY) (graphMorphism sX sY f hf) ((e : ℤ) - 0)))
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sY sZ) (graphMorphism sY sZ g hg) ((n : ℤ) - 0))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sX sZ) (graphMorphism sX sZ (g ≫ f) (by rw [Category.assoc, hf, hg]))
        ((n : ℤ) - (0 + 0))) := by
  set Γf := graphMorphism sX sY f hf with hΓf
  set Γg := graphMorphism sY sZ g hg with hΓg
  set Γgf := graphMorphism sX sZ (g ≫ f) (by rw [Category.assoc, hf, hg]) with hΓgf
  have hΓf₁ : Γf ≫ pullback.fst sX sY = f := graphMorphism_fst _ _ _ _
  have hΓf₂ : Γf ≫ pullback.snd sX sY = 𝟙 Y := graphMorphism_snd _ _ _ _
  have hΓg₁ : Γg ≫ pullback.fst sY sZ = g := graphMorphism_fst _ _ _ _
  have hΓg₂ : Γg ≫ pullback.snd sY sZ = 𝟙 Z := graphMorphism_snd _ _ _ _
  have : IsIso (Γf ≫ pullback.snd sX sY) := by rw [hΓf₂]; infer_instance
  have hfst : pullback.fst (Γf ≫ pullback.snd sX sY) (Γg ≫ pullback.fst sY sZ) =
      pullback.snd (Γf ≫ pullback.snd sX sY) (Γg ≫ pullback.fst sY sZ) ≫ g :=
    (Category.comp_id _).symm.trans ((congrArg (pullback.fst _ _ ≫ ·) hΓf₂).symm.trans
      (pullback.condition.trans (congrArg (pullback.snd _ _ ≫ ·) hΓg₁)))
  have hκ : compositionFibre.toProduct Γf Γg = pullback.snd _ _ ≫ Γgf := by
    apply pullback.hom_ext
    · rw [compositionFibre.toProduct, pullback.lift_fst, Category.assoc, hΓgf,
        graphMorphism_fst sX sZ (g ≫ f), hΓf₁, hfst, Category.assoc]
    · rw [compositionFibre.toProduct, pullback.lift_snd, Category.assoc, hΓgf,
        graphMorphism_snd sX sZ (g ≫ f), hΓg₂]
  have : IsClosedImmersion (compositionFibre.toProduct Γf Γg) := by rw [hκ]; infer_instance
  have hΓgfZ : Γgf ≫ prodBase sX sZ = sZ := by
    rw [hΓgf, prodBase, ← Category.assoc, graphMorphism_fst sX sZ (g ≫ f), Category.assoc, hf,
      hg]
  rw [hΔ.compositionInt_closedSubscheme k sX sY sZ hX hY hZ 0 0 Γf Γg
    (fun T ↦ by
      rw [deltaDimension_congr (g := sY) (by rw [prodBase, ← Category.assoc, hΓf₁, hf]),
        sub_zero]
      exact deltaDimension_irreducibleComponent_of_relativeDimension k sY e hY T)
    (fun T ↦ by
      rw [deltaDimension_congr (g := sZ) (by rw [prodBase, ← Category.assoc, hΓg₁, hg]),
        sub_zero]
      exact deltaDimension_irreducibleComponent_of_relativeDimension k sZ n hZ T)
    (by
      rw [schemeDeltaDimension_congr _ (show compositionFibre.toProduct Γf Γg ≫ prodBase sX sZ =
          (asIso (pullback.snd _ _)).hom ≫ sZ by rw [hκ, asIso_hom, Category.assoc, hΓgfZ]),
        schemeDeltaDimension_comp_iso, add_zero]
      exact schemeDeltaDimension_le_of_forall_irreducibleComponent sZ
        (deltaDimension_irreducibleComponent_of_relativeDimension k sZ n hZ))
    (fun x _ ↦ ⟨isCohenMacaulayLocalRing_stalk_of_smooth k sY _,
      isCohenMacaulayLocalRing_stalk_of_smooth k sZ _⟩)]
  exact congrArg _ (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ (asIso (pullback.snd _ _))
    hκ.symm _)

/-- Additive maps out of the Chow group of a compact scheme agree if they agree on the classes of
the integral components of the points of the right relative dimension. -/
private theorem chowGroup_apply_eq_of_forall_integralComponentAt {C : ChowSituation.{u}}
    {T : Scheme.{u}} (p : T ⟶ C.S) [LocallyOfFiniteType p] [CompactSpace T] {n : ℤ} {M : Type*}
    [AddCommGroup M] {φ ψ : chowGroup C p n →+ M}
    (h : ∀ x : T, relativeDimension C.dimensionFunction p x = n →
      φ (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt x).subschemeι n)) =
        ψ (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C p
          (integralComponentAt x).subschemeι n)))
    (c : chowGroup C p n) : φ c = ψ c := by
  induction c using QuotientAddGroup.induction_on with
  | H α =>
    exact DFunLike.congr_fun (cycleGroup_addMonoidHom_ext
      (φ := φ.comp (QuotientAddGroup.mk' _)) (ψ := ψ.comp (QuotientAddGroup.mk' _)) h) α

/-- **`c ∘ [Δ_X] = c` on integral Chow groups.** For `X` proper and `Y` quasi-compact, smooth
over `k` of dimensions `d` and `e`, and a family of diagonal classes satisfying the
proper-intersection formula, composing a class `c ∈ CH_{e-s}(X × Y)` with the class of the
diagonal of `X` returns `c`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.compositionInt_graph_id
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sX] [QuasiCompact sY] {d e : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (s : ℤ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - s)) :
    compositionInt k sX sX sY Δ hX hX hY 0 s
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sX) (graphMorphism sX sX (𝟙 X) (Category.id_comp sX)) ((d : ℤ) - 0))) c =
      chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY) (by rw [zero_add]) c := by
  have : CompactSpace (Limits.pullback sX sY : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (prodBase sX sY)
  refine chowGroup_apply_eq_of_forall_integralComponentAt (prodBase sX sY)
    (φ := (compositionInt k sX sX sY Δ hX hX hY 0 s
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sX sX) (graphMorphism sX sX (𝟙 X) (Category.id_comp sX))
            ((d : ℤ) - 0)))).toAddMonoidHom)
    (ψ := (chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY)
      (show (e : ℤ) - s = e - (0 + s) by rw [zero_add])).toAddMonoidHom) (fun x hx ↦ ?_) c
  have := isIntegral_integralComponentAt x
  simp only [LinearMap.toAddMonoidHom_coe, AddEquiv.coe_toAddMonoidHom]
  rw [hΔ.compositionInt_graph_id_mk k sX sY hX hY s _
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ _ x hx),
    chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme]

/-- **`[Δ_Y] ∘ c = c` on integral Chow groups.** For `X` quasi-compact and `Y` proper, smooth
over `k` of dimensions `d` and `e`, and a family of diagonal classes satisfying the
proper-intersection formula, composing the class of the diagonal of `Y` with a class
`c ∈ CH_{e-r}(X × Y)` returns `c`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.compositionInt_id_graph
    (hΔ : Δ.ProperIntersectionFormula) [QuasiCompact sX] [IsProper sY] {d e : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (r : ℤ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX sY) ((e : ℤ) - r)) :
    compositionInt k sX sY sY Δ hX hY hY r 0 c
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
          (prodBase sY sY) (graphMorphism sY sY (𝟙 Y) (Category.id_comp sY)) ((e : ℤ) - 0))) =
      chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY) (by rw [add_zero]) c := by
  have : CompactSpace (Limits.pullback sX sY : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (prodBase sX sY)
  refine chowGroup_apply_eq_of_forall_integralComponentAt (prodBase sX sY)
    (φ := ((compositionInt k sX sY sY Δ hX hY hY r 0).flip
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sY sY) (graphMorphism sY sY (𝟙 Y) (Category.id_comp sY))
          ((e : ℤ) - 0)))).toAddMonoidHom)
    (ψ := (chowGroupDegreeEquiv (fieldChowSituation k) (prodBase sX sY)
      (show (e : ℤ) - r = e - (r + 0) by rw [add_zero])).toAddMonoidHom) (fun x hx ↦ ?_) c
  have := isIntegral_integralComponentAt x
  simp only [LinearMap.toAddMonoidHom_coe, AddEquiv.coe_toAddMonoidHom, LinearMap.flip_apply]
  rw [hΔ.compositionInt_mk_graph_id k sX sY hX hY r _
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ _ x hx),
    chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme]

/-- **Stacks 0FG2, the right unit law, for a family of diagonal classes satisfying the
proper-intersection formula.** For `X` proper and `Y` quasi-compact, smooth over `k` of
dimensions `d` and `e`, and a correspondence `c ∈ Corrˢ(X, Y)`, composing `c` with the class
`[Δ_X] = [Γ_{id_X}] ∈ Corr⁰(X, X)` of the diagonal returns `c`: `c ∘ [Δ_X] = c`, the degrees
`s` and `0 + s` being identified.

This is the statement of the source for the canonical family of diagonal classes once that
family is shown to satisfy `Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula`
(Stacks 0FFD); that instance is pending, as the canonical family is not yet constructed. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.composition_graph_id
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sX] [QuasiCompact sY] {d e : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (s : ℤ)
    (c : Correspondence (fieldChowSituation k) sX sY e s) :
    composition k sX sX sY Δ hX hX hY 0 s
        (graphCorrespondence sX sX (𝟙 X) (Category.id_comp sX) d) c =
      correspondenceCongr k sX sY (zero_add s).symm c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul q c =>
    rw [graphCorrespondence, composition_tmul, correspondenceCongr_tmul, one_mul,
      hΔ.compositionInt_graph_id k sX sY hX hY s c]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Stacks 0FG2, the left unit law, for a family of diagonal classes satisfying the
proper-intersection formula.** For `X` quasi-compact and `Y` proper, smooth over `k` of
dimensions `d` and `e`, and a correspondence `c ∈ Corrʳ(X, Y)`, composing the class
`[Δ_Y] = [Γ_{id_Y}] ∈ Corr⁰(Y, Y)` of the diagonal with `c` returns `c`: `[Δ_Y] ∘ c = c`, the
degrees `r` and `r + 0` being identified.

This is the statement of the source for the canonical family of diagonal classes once that
family is shown to satisfy `Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula`
(Stacks 0FFD); that instance is pending, as the canonical family is not yet constructed. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.composition_id_graph
    (hΔ : Δ.ProperIntersectionFormula) [QuasiCompact sX] [IsProper sY] {d e : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (r : ℤ)
    (c : Correspondence (fieldChowSituation k) sX sY e r) :
    composition k sX sY sY Δ hX hY hY r 0 c
        (graphCorrespondence sY sY (𝟙 Y) (Category.id_comp sY) e) =
      correspondenceCongr k sX sY (add_zero r).symm c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul q c =>
    rw [graphCorrespondence, composition_tmul, correspondenceCongr_tmul, mul_one,
      hΔ.compositionInt_id_graph k sX sY hX hY r c]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- **Stacks 0FG3, functoriality of graphs, for a family of diagonal classes satisfying the
proper-intersection formula.** For morphisms `f : Y ⟶ X` and `g : Z ⟶ Y` of schemes smooth over
`k` of dimensions `d`, `e`, `n`, with `X` separated and `Y` proper, the composition of the graph
correspondences is the graph correspondence of the composite: `[Γ_g] ∘ [Γ_f] = [Γ_{f ∘ g}]` in
`Corr⁰(X, Z)`, the degrees `0` and `0 + 0` being identified.

This is the statement of the source for the canonical family of diagonal classes once that
family is shown to satisfy `Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula`
(Stacks 0FFD); that instance is pending, as the canonical family is not yet constructed. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.composition_graph_graph
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sY] {d e n : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ n) (f : Y ⟶ X) (hf : f ≫ sX = sY)
    (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    composition k sX sY sZ Δ hX hY hZ 0 0 (graphCorrespondence sX sY f hf e)
        (graphCorrespondence sY sZ g hg n) =
      correspondenceCongr k sX sZ (add_zero 0).symm
        (graphCorrespondence sX sZ (g ≫ f) (by rw [Category.assoc, hf, hg]) n) := by
  rw [graphCorrespondence, graphCorrespondence, graphCorrespondence, composition_tmul,
    correspondenceCongr_tmul, one_mul, hΔ.compositionInt_graph_graph k sX sY sZ hX hY hZ f hf g hg,
    chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme]

end Laws

/-! ### Mixed dimension -/

section Mixed

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  [Smooth sX] [Smooth sY] [IsSeparated sX] [IsSeparated sY]

/-- The class `[Δ_{X_d}] ∈ Corr⁰(X_d, X_d)` of the diagonal of the part of `X` of dimension `d`,
as a pure block of `Corr⁰(X, X)`. -/
abbrev diagonalBlock (d : ℕ) : Corr k sX sX 0 :=
  DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ d
    (graphCorrespondence (partBase sX d) (partBase sX d) (𝟙 _) (Category.id_comp _) d))

/-- **The diagonal correspondence** `[Δ_X] ∈ Corr⁰(X, X)` of a quasi-compact scheme `X` smooth
over `k`: on the decomposition `X = ∐_d X_d` into equidimensional parts, its `(d, d)` block is the
class `[Δ_{X_d}] = [Γ_{id}]` of the diagonal of `X_d`, and its other blocks vanish. Only finitely
many parts are nonempty, and the sum runs over those. -/
def diagonalCorr [QuasiCompact sX] : Corr k sX sX 0 :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  ∑ d ∈ (finite_setOf_nonempty_dimPart sX).toFinset, diagonalBlock k sX d

variable {Δ : DiagonalClassFamily k}

omit [IsSeparated sX] in
/-- A part of a quasi-compact scheme is quasi-compact over the base. -/
theorem quasiCompact_partBase [QuasiCompact sX] (d : ℕ) : QuasiCompact (partBase sX d) := by
  have := (isClopenDecomposition_dimPart sX).isProper_ι d
  infer_instance

/-- The block `[Δ_{X_d}]` composed with a pure block `c ∈ Corrˢ(X_d, Y_e)` is `c`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.comp_diagonalBlock_lof_lof
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sX] [QuasiCompact sY] (s : ℤ) (d e : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e s) :
    comp k sX sX sY Δ 0 s (diagonalBlock k sX d) (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) =
      DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e
        (correspondenceCongr k (partBase sX d) (partBase sY e) (zero_add s).symm x)) := by
  have := quasiCompact_partBase k sY e
  rw [comp_lof_lof_lof_lof, hΔ.composition_graph_id k (partBase sX d) (partBase sY e)]

/-- The pure block `c ∈ Corrʳ(X_d, Y_e)` composed with `[Δ_{Y_e}]` is `c`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.comp_lof_lof_diagonalBlock
    (hΔ : Δ.ProperIntersectionFormula) [QuasiCompact sX] [IsProper sY] (r : ℤ) (d e : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r) :
    comp k sX sY sY Δ r 0 (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) (diagonalBlock k sY e) =
      DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e
        (correspondenceCongr k (partBase sX d) (partBase sY e) (add_zero r).symm x)) := by
  have := quasiCompact_partBase k sX d
  rw [comp_lof_lof_lof_lof, hΔ.composition_id_graph k (partBase sX d) (partBase sY e)]

/-- `[Δ_X]` composed with a pure block `c ∈ Corrˢ(X_d, Y_e)` is `c`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.comp_diagonalCorr_lof_lof
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sX] [QuasiCompact sY] (s : ℤ) (d e : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e s) :
    comp k sX sX sY Δ 0 s (diagonalCorr k sX) (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) =
      DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e
        (correspondenceCongr k (partBase sX d) (partBase sY e) (zero_add s).symm x)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  unfold diagonalCorr
  rw [map_sum, LinearMap.sum_apply]
  by_cases hd : (dimPart sX d : Set X).Nonempty
  · rw [Finset.sum_eq_single d]
    · exact hΔ.comp_diagonalBlock_lof_lof k sX sY s d e x
    · intro d' _ hd'
      exact comp_lof_lof_lof_of_ne k sX sX sY Δ 0 s d' d' d hd' _ _
    · intro h
      exact (h ((finite_setOf_nonempty_dimPart sX).mem_toFinset.2 hd)).elim
  · have : IsEmpty (dimPart sX d).toScheme := ⟨fun x ↦ hd ⟨x.1, x.2⟩⟩
    have := subsingleton_correspondence_of_isEmpty_left (fieldChowSituation k)
      (partBase sX d) (partBase sY e) e s
    rw [Subsingleton.elim x 0]
    simp

/-- A pure block `c ∈ Corrʳ(X_d, Y_e)` composed with `[Δ_Y]` is `c`. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.comp_lof_lof_diagonalCorr
    (hΔ : Δ.ProperIntersectionFormula) [QuasiCompact sX] [IsProper sY] (r : ℤ) (d e : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r) :
    comp k sX sY sY Δ r 0 (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) (diagonalCorr k sY) =
      DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e
        (correspondenceCongr k (partBase sX d) (partBase sY e) (add_zero r).symm x)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  unfold diagonalCorr
  rw [map_sum]
  by_cases he : (dimPart sY e : Set Y).Nonempty
  · rw [Finset.sum_eq_single e]
    · exact hΔ.comp_lof_lof_diagonalBlock k sX sY r d e x
    · intro e' _ he'
      exact comp_lof_lof_lof_of_ne k sX sY sY Δ r 0 d e e' (Ne.symm he') _ _
    · intro h
      exact (h ((finite_setOf_nonempty_dimPart sY).mem_toFinset.2 he)).elim
  · have : IsEmpty (dimPart sY e).toScheme := ⟨fun x ↦ he ⟨x.1, x.2⟩⟩
    have := subsingleton_correspondence_of_isEmpty_right (fieldChowSituation k)
      (partBase sX d) (partBase sY e) e r
    rw [Subsingleton.elim x 0]
    simp

/-- **Stacks 0FG2, the right unit law in mixed dimension, for a family of diagonal classes
satisfying the proper-intersection formula.** For `X` proper and `Y` quasi-compact, smooth over
`k`, and `c ∈ Corrˢ(X, Y)`, `c ∘ [Δ_X] = c`, the degrees `s` and `0 + s` being identified.

The instance of `Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula` for the
canonical family of diagonal classes (Stacks 0FFD) is pending. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.comp_diagonalCorr
    (hΔ : Δ.ProperIntersectionFormula) [IsProper sX] [QuasiCompact sY] (s : ℤ)
    (c : Corr k sX sY s) :
    comp k sX sX sY Δ 0 s (diagonalCorr k sX) c = corrCongr k sX sY (zero_add s).symm c := by
  induction c using Corr.induction_on with
  | zero => simp [LinearEquiv.map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | lof d e x => rw [corrCongr_lof_lof, hΔ.comp_diagonalCorr_lof_lof k sX sY s d e x]

/-- **Stacks 0FG2, the left unit law in mixed dimension, for a family of diagonal classes
satisfying the proper-intersection formula.** For `X` quasi-compact and `Y` proper, smooth over
`k`, and `c ∈ Corrʳ(X, Y)`, `[Δ_Y] ∘ c = c`, the degrees `r` and `r + 0` being identified.

The instance of `Stacks.WeilCohomology.DiagonalClassFamily.ProperIntersectionFormula` for the
canonical family of diagonal classes (Stacks 0FFD) is pending. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.diagonalCorr_comp
    (hΔ : Δ.ProperIntersectionFormula) [QuasiCompact sX] [IsProper sY] (r : ℤ)
    (c : Corr k sX sY r) :
    comp k sX sY sY Δ r 0 c (diagonalCorr k sY) = corrCongr k sX sY (add_zero r).symm c := by
  induction c using Corr.induction_on with
  | zero => simp [LinearEquiv.map_zero]
  | add a b ha hb => rw [map_add, LinearMap.add_apply, map_add, ha, hb]
  | lof d e x => rw [corrCongr_lof_lof, hΔ.comp_lof_lof_diagonalCorr k sX sY r d e x]

end Mixed

end Stacks.WeilCohomology

namespace Stacks.WeilCohomology

open Stacks.Chow

/-! ### The proper-intersection formula from the excess intersection formula -/

/-- **The proper-intersection formula from the excess intersection formula at vanishing
excess.** A family of diagonal classes satisfies the proper-intersection formula (Stacks 0FFD)
as soon as, for every scheme `W` smooth and separated over `k` of constant dimension `N`, its
class `Δ^! ∈ A^N(W ⟶ W ×_k W)` satisfies `Stacks.Chow.BivariantClass.CapRegularFormula` in every
degree: `Δ^! ∩ [V]_n = [W ×_{Δ, W ×_k W} V]_{n-N}` for every `V ⟶ W ×_k W` pure of
`δ`-dimension `n` along which the diagonal pulls back to a regular closed immersion of
codimension `N`. For the canonical class `c(Δ, 𝒯_{W/k})` of Stacks 0FBK that is Stacks 0FBM at
vanishing excess.

The proof is
`Stacks.Chow.Intersection.selfIntersectionProduct_mk_cycleAssociatedToClosedSubscheme`, which is
the source's proof of Stacks 0FFD through Stacks 0FEA and Stacks 045J. -/
theorem DiagonalClassFamily.ProperIntersectionFormula.of_capRegularFormula {k : Type u} [Field k]
    (Δ : DiagonalClassFamily k)
    (hΔ : ∀ {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
      [Smooth sW] [IsSeparated sW] (N : ℕ) (hN : RelativeDimension sW N) (n : ℤ),
      (Δ sW N hN).CapRegularFormula (fieldChowSituation k) (fieldGysinSystem k) sW
        (selfProductStructure (fieldChowSituation k) sW) (pullback.diagonal sW)
        (diagonal_comp_selfProductStructure (fieldChowSituation k) sW) N n) :
    Δ.ProperIntersectionFormula := by
  intro W V₁ V₂ sW _ _ _ N hN i₁ _ i₂ _ n₁ n₂ d hd h₁ h₂ h₃ h₄
  let _ : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  exact Intersection.selfIntersectionProduct_mk_cycleAssociatedToClosedSubscheme k
    (fieldGysinSystem k) sW N (Δ sW N hN) i₁ i₂ n₁ n₂ d hd
    ((Δ sW N hN).capCohenMacaulayFormula_of_capRegularFormula (fieldChowSituation k)
      (fieldGysinSystem k) sW (selfProductStructure (fieldChowSituation k) sW)
      (pullback.diagonal sW) (diagonal_comp_selfProductStructure (fieldChowSituation k) sW) N
      (VirtualNormalBundle.ofIsRegularImmersion _ (isRegularImmersion_diagonal_of_smooth sW))
      (Intersection.isFiniteLocallyFreeOfRank_ofIsRegularImmersion_diagonal sW hN)
      (hΔ sW N hN (n₁ + n₂)))
    h₁ h₂ h₃ h₄

end Stacks.WeilCohomology

end
