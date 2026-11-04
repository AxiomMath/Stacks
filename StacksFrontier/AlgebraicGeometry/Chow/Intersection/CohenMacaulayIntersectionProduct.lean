module

public import StacksFrontier.AlgebraicGeometry.Chow.Intersection.CohenMacaulayProperIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalCapRegularFormula
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Assembly.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalCapFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysin
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.Intersection.DiagonalGysinCapRegular
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NotDominant
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.SelfIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantStalkRank
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.ProductOverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ClosedImmersionIdealSheaves
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsRank
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairSplitConormalSequence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Composition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphCodimension
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
import all StacksFrontier.AlgebraicGeometry.Chow.Intersection.CohenMacaulayProperIntersection

/-!
# Cohen–Macaulay proper intersections on a smooth scheme: the intersection product

Let `k` be a field, let `X` be an integral scheme smooth over `k`, and let `Y, Z ⊆ X` be integral
closed subschemes. Put `d = dim Y + dim Z - dim X`, and assume that `dim (Y ∩ Z) ≤ d` and that
`𝒪_{Y,ξ}` and `𝒪_{Z,ξ}` are Cohen–Macaulay at every point `ξ` of `Y ∩ Z` with `δ(ξ) = d`. Stacks
0FFD asserts that `[Y] · [Z] = [Y ∩ Z]_d` in `CH_d(X)`.

The source's proof is the one formalized here. The product is `[Y] · [Z] = Δ^!([Y × Z])` for the
Gysin class `Δ^! = c(Δ : X ⟶ X ×_k X, 𝒯_{X/k})` of the diagonal; the scheme-theoretic
intersection is `Y ∩ Z = X ×_{Δ, X ×_k X} (Y ×_k Z)`; `Y ×_k Z` is pure of dimension
`dim Y + dim Z`; its local rings at the points of `Y ∩ Z` of `δ`-dimension `d` are Cohen–Macaulay
by Stacks 045J; and the Gysin formula of Stacks 0FEA then gives `Δ^! ∩ [Y ×_k Z] = [Y ∩ Z]_d`.

Everything is proved in the generality the source's later uses need (Stacks 0FG2, 0FG3): `X` is
any scheme smooth over `k` of constant dimension, and `Y`, `Z` are closed
subschemes all of whose irreducible components have the same `δ`-dimension. Along the way the
exterior product `[A] × [B] = [A ×_k B]` of Stacks 0FBU is extended from integral closed
subschemes to arbitrary ones, and the normal bundle of the diagonal of a smooth morphism is shown
to have rank the relative dimension.

## Main definitions

The intersection `Y ∩ Z ⟶ Y ×_k Z`, its identification with the diagonal pullback, hypothesis (2)
of Stacks 0FFD (`Stacks.Chow.Intersection.CohenMacaulayAtIntersection`) and hypotheses (2), (3)
and (4) of Stacks 0FEA (`Stacks.Chow.Intersection.GysinFormulaHypotheses`) are in
`StacksFrontier.AlgebraicGeometry.Chow.Intersection.CohenMacaulayProperIntersection`.

* `Stacks.Chow.Intersection.pullbackIsoSubschemeSupComap`: the product `A ×_S B` of two closed
  subschemes is the closed subscheme cut out by `pr⁻¹(ker a) + pr⁻¹(ker b)`.

## Main results

* `Stacks.Chow.Intersection.isCohenMacaulayLocalRing_stalk_intersectionToProduct`: under
  hypothesis (2) of Stacks 0FFD, the product `Y ×_k Z` is Cohen–Macaulay at the points of the
  intersection of `δ`-dimension `d` (Stacks 045J).
* `Stacks.Chow.Intersection.gysinFormulaHypotheses_of_cohenMacaulay`: under the two hypotheses
  of Stacks 0FFD, the hypotheses of the Gysin formula of Stacks 0FEA hold.
* `Stacks.Chow.Intersection.relativeDimension_toNat_of_forall_deltaDimension_eq` and
  `Stacks.Chow.Intersection.deltaDimension_irreducibleComponent_pullback`: a scheme pure of
  `δ`-dimension `n` over a field has relative dimension `n`, and a product of schemes pure of
  `δ`-dimensions `n` and `m` is pure of `δ`-dimension `n + m`.
* `Stacks.Chow.Intersection.exteriorProduct_cycleAssociatedToClosedSubscheme`: the exterior
  product of the cycles of two closed subschemes is the cycle of their product.
* `Stacks.Chow.Intersection.isFiniteLocallyFreeOfRank_ofIsRegularImmersion_diagonal`: the
  normal bundle of the diagonal of a smooth morphism of relative dimension `N` has rank `N`.
* `Stacks.Chow.Intersection.cap_fundamentalChowClass_exteriorToSelfProduct`: Stacks 0FFD in the
  Gysin form `Δ^! ∩ [V₁ ×_k V₂] = [V₁ ∩ V₂]`.
* `Stacks.Chow.Intersection.selfIntersectionProduct_mk_cycleAssociatedToClosedSubscheme`: Stacks
  0FFD in the intersection-product form `[V₁] · [V₂] = [V₁ ∩ V₂]_d`, for closed subschemes of
  pure dimension of a scheme smooth over `k`.
* `Stacks.Chow.Intersection.selfIntersectionProduct_mk_of_cohenMacaulayAtIntersection`: Stacks
  0FFD under the source's hypotheses, for any class satisfying the conclusion of Stacks 0FEA.
* `selfIntersectionProduct_diagonalGysinClass_mk_of_cohenMacaulayAtIntersection`:
  **Stacks 0FFD**, for the Gysin class of the diagonal of Stacks 0FBR
  (`Stacks.Chow.Intersection.diagonalGysinClassOverField`).

## Implementation notes

**The Gysin class of the diagonal.** The intersection product
`Stacks.Chow.selfIntersectionProduct` is formed with a bivariant class
`Δ^! ∈ A^N(X ⟶ X ×_k X)` of the diagonal that is an argument. The source's proof uses one property
of `Δ^! = c(Δ, 𝒯_{X/k})` beyond bivariance, the conclusion of Stacks 0FEA:
`Δ^! ∩ [V]_n = [X ×_{X ×_k X} V]_{n-N}` whenever `V ⟶ X ×_k X` is pure of `δ`-dimension `n`,
`dim_δ(X ×_{X ×_k X} V) ≤ n - N` and the local rings of `V` at the points of `δ`-dimension `n - N`
of `X ×_{X ×_k X} V` are Cohen–Macaulay. That is
`Stacks.Chow.BivariantClass.CapCohenMacaulayFormula`, and the results here hold for every class
satisfying it.

For a class of the closed immersion of a separated `X`, the property follows from the excess
intersection formula of Stacks 0FBM at vanishing excess
(`Stacks.Chow.BivariantClass.CapRegularFormula`) by Stacks 0FEA
(`Stacks.Chow.BivariantClass.capCohenMacaulayFormula_of_capRegularFormula`), hypothesis (1) of
Stacks 0FEA being discharged by
`Stacks.Chow.Intersection.isFiniteLocallyFreeOfRank_ofIsRegularImmersion_diagonal`: the virtual
normal sheaf is the normal bundle of the regular immersion `Δ` (Stacks 0FBR), the dual of the
conormal sheaf `𝒞_Δ ≅ Ω_{X/k}` (Stacks 08S2), of rank `N` by Stacks 02G1. For the Gysin class of
the diagonal of Stacks 0FBR, separated or not, it follows from the same formula for its closed
factor (`Stacks.Chow.diagonalGysinClass_capCohenMacaulayFormula`).

**Separatedness.** None is assumed, as in the source: the property of `Δ^!` used is stated for a
class of any morphism, and the diagonal enters only through the pullbacks
`X ×_{X ×_k X} V`.

**Dimensions.** The `δ`-dimension of a point is `Stacks.Chow.relativeDimension` for the
constant-zero dimension function of `Spec k`. Hypothesis (1) is stated in the general form as a
bound on `Stacks.Chow.schemeDeltaDimension`, and in the source form as
`dim (Y ∩ Z) + dim X ≤ dim Y + dim Z` for the topological Krull dimension, which is
`dim (Y ∩ Z) ≤ d` written without subtracting, so that it makes sense also for `d < 0`.

**Stacks 045J.** The step the source performs by quoting Algebra, Lemma 10.163.3 (Stacks 045J)
is `AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_pullback_of_field`.

## References

* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
* [Stacks Project, Tag 0FEA](https://stacks.math.columbia.edu/tag/0FEA)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0FBU](https://stacks.math.columbia.edu/tag/0FBU)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 045J](https://stacks.math.columbia.edu/tag/045J)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.Intersection

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}

/-- Under hypothesis (2) of Stacks 0FFD, the local ring of the product `Y ×_k Z` is Cohen–Macaulay
at every point of the intersection `Y ∩ Z` of `δ`-dimension `d`: this is Stacks 045J, in the form
`AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_pullback_of_field`, applied at the image of the
point in `Y ×_k Z`. -/
theorem isCohenMacaulayLocalRing_stalk_intersectionToProduct (k : Type u) [Field k]
    {X Y Z : Scheme.{u}} (p : X ⟶ Spec (.of k)) [Smooth p] (i : Y ⟶ X) [IsClosedImmersion i]
    (j : Z ⟶ X) [IsClosedImmersion j] {d : ℤ} (hCM : CohenMacaulayAtIntersection k p i j d)
    (ζ : ↑(pullback i j))
    (hζ : relativeDimension (fieldDimensionFunction k) (pullback.fst i j ≫ i ≫ p) ζ = d) :
    letI : IsLocallyNoetherian ↑(pullback (i ≫ p) (j ≫ p)) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (i ≫ p) (j ≫ p) ≫ i ≫ p)
    IsCohenMacaulayLocalRing
      ((pullback (i ≫ p) (j ≫ p) : Scheme.{u}).presheaf.stalk
        ((intersectionToProduct p i j).base ζ)) := by
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  let _ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (j ≫ p)
  exact AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_pullback_of_field k (i ≫ p) (j ≫ p)
    ((intersectionToProduct p i j).base ζ)
    (isCohenMacaulayLocalRing_stalk_of_eq
      (base_apply_comp (intersectionToProduct_fst p i j) ζ).symm (hCM ζ hζ).1)
    (isCohenMacaulayLocalRing_stalk_of_eq
      (base_apply_comp (intersectionToProduct_snd p i j) ζ).symm (hCM ζ hζ).2)

/-- **The verification of the hypotheses of Stacks 0FEA in the proof of Stacks 0FFD.** Let `k` be a
field, let `X` be an integral scheme smooth over `k` of dimension `dX`, and let `Y, Z ⊆ X` be
integral closed subschemes of dimensions `dY` and `dZ`. Put `d = dY + dZ - dX`. Assume

1. `dim (Y ∩ Z) ≤ d`, and
2. `𝒪_{Y,ξ}` and `𝒪_{Z,ξ}` are Cohen–Macaulay for every `ξ ∈ Y ∩ Z` with `δ(ξ) = d`.

Then hypotheses (2), (3) and (4) of the higher-codimension Gysin formula of Stacks 0FEA hold for
the diagonal `Δ : X ⟶ X ×_k X` and the morphism `Y ×_k Z ⟶ X ×_k X`, in the topological form
`Stacks.Chow.Intersection.GysinFormulaHypotheses`: this is what the source's proof establishes
before quoting that formula. The conclusion `[Y] · [Z] = [Y ∩ Z]_d` that the source draws from it
is `selfIntersectionProduct_diagonalGysinClass_mk_of_cohenMacaulayAtIntersection`. -/
theorem gysinFormulaHypotheses_of_cohenMacaulay (k : Type u) [Field k]
    {X Y Z : Scheme.{u}} (p : X ⟶ Spec (.of k)) [Smooth p] [IsIntegral X]
    (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y]
    (j : Z ⟶ X) [IsClosedImmersion j] [IsIntegral Z]
    (dX dY dZ d : ℕ)
    (_hXdim : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (hZdim : topologicalKrullDim Z = (dZ : WithBot ℕ∞))
    (_hd : dY + dZ = dX + d)
    (hIntDim : topologicalKrullDim ↑(pullback i j) ≤ (d : WithBot ℕ∞))
    (hCM : CohenMacaulayAtIntersection k p i j (d : ℤ)) :
    GysinFormulaHypotheses k p i j dY dZ d := by
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  let _ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (j ≫ p)
  refine ⟨?_, ?_, ?_⟩
  · rw [AlgebraicGeometry.topologicalKrullDim_pullback k (i ≫ p) (j ≫ p), hYdim, hZdim]
  · exact (topologicalKrullDim_diagonalPullback p i j).trans_le hIntDim
  · exact isCohenMacaulayLocalRing_stalk_intersectionToProduct k p i j hCM

/-! ### The diagonal pullback and the intersection -/

/-- Under the identification `X ×_{Δ, X ×_k X} (Y ×_k Z) ≅ Y ∩ Z`, the inclusion of `Y ∩ Z` into
`X` is the first projection of the diagonal pullback. -/
@[reassoc]
theorem diagonalPullbackIso_hom_fst_comp (p : X ⟶ Spec (.of k)) (i : Y ⟶ X) (j : Z ⟶ X) :
    (diagonalPullbackIso p i j).hom ≫ pullback.fst i j ≫ i =
      pullback.fst (pullback.diagonal p) _ := by
  have h := congrArg (· ≫ pullback.fst p p) (pullback.condition (f := pullback.diagonal p)
    (g := pullback.map (i ≫ p) (j ≫ p) p p i j (𝟙 _) (Category.comp_id _) (Category.comp_id _)))
  simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.map,
    pullback.lift_fst] at h
  rw [diagonalPullbackIso, ← Category.assoc, pullbackDiagonalMapIdIso_hom_fst, Category.assoc, ← h]

/-- Under the identification `X ×_{Δ, X ×_k X} (Y ×_k Z) ≅ Y ∩ Z`, the inclusion of `Y ∩ Z` into
`Y ×_k Z` is the second projection of the diagonal pullback. -/
@[reassoc]
theorem diagonalPullbackIso_hom_intersectionToProduct (p : X ⟶ Spec (.of k)) (i : Y ⟶ X)
    (j : Z ⟶ X) :
    (diagonalPullbackIso p i j).hom ≫ intersectionToProduct p i j = pullback.snd _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, intersectionToProduct_fst, diagonalPullbackIso,
      pullbackDiagonalMapIdIso_hom_fst]
  · rw [Category.assoc, intersectionToProduct_snd, diagonalPullbackIso,
      pullbackDiagonalMapIdIso_hom_snd]

/-! ### Schemes of pure dimension over a field -/

section PureDimension

variable (k)

/-- An irreducible component of a scheme locally of finite type over a field has dimension the
relative dimension of its generic point (Stacks 02QO). -/
private theorem topologicalKrullDim_irreducibleComponent_eq {T : Scheme.{u}}
    (q : T ⟶ Spec (.of k)) [LocallyOfFiniteType q] {V : Set T} (hV : V ∈ irreducibleComponents T) :
    topologicalKrullDim V =
      (relativeDimension (fieldChowSituation k).dimensionFunction q hV.1.genericPoint).toNat := by
  have h := topologicalKrullDim_closure_singleton_eq k q hV.1.genericPoint
  rwa [(hV.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents V hV)).def] at h

/-- **A scheme pure of dimension `n` over a field has relative dimension `n` over it.** If every
irreducible component of a scheme `T` locally of finite type over `k` has `δ`-dimension `n`, then
`T ⟶ Spec k` has relative dimension `n` in the sense of Stacks 02NJ: the unique fibre is `T`
itself, every component of which has dimension `n` (Stacks 02QO). -/
theorem relativeDimension_toNat_of_forall_deltaDimension_eq {T : Scheme.{u}}
    (q : T ⟶ Spec (.of k)) [LocallyOfFiniteType q] {n : ℤ}
    (hT : ∀ V : irreducibleComponents T, deltaDimension (fieldChowSituation k) q
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = n) :
    RelativeDimension q n.toNat := by
  have hcomp : ∀ V ∈ irreducibleComponents T,
      topologicalKrullDim V = (n.toNat : WithBot ℕ∞) := by
    intro V hV
    rw [topologicalKrullDim_irreducibleComponent_eq k q hV]
    have hn : relativeDimension (fieldChowSituation k).dimensionFunction q hV.1.genericPoint = n :=
      hT ⟨V, hV⟩
    rw [hn]
  have hequi : TopologicalSpace.Equidimensional T := fun V hV V' hV' => by
    rw [hcomp V hV, hcomp V' hV']
  have : Subsingleton (Spec (.of k)) := by
    show Subsingleton (PrimeSpectrum k)
    infer_instance
  intro s hs
  have hpre : q.base ⁻¹' {s} = (Set.univ : Set T) := by
    ext y
    simp [Subsingleton.elim (q.base y) s]
  let e : q.fiber s ≃ₜ T :=
    (q.fiberHomeo s).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ T))
  refine ⟨TopologicalSpace.Equidimensional.of_homeomorph e hequi, ?_⟩
  rw [IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph]
  obtain ⟨t⟩ := hs
  obtain ⟨V, hV, -, hVdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k T q (e t)
  rw [← topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k T q hequi (e t), ← hVdim,
    hcomp V hV]

/-- On a nonempty scheme pure of `δ`-dimension `n` over a field, `n` is non-negative. -/
theorem nonneg_of_forall_deltaDimension_eq {T : Scheme.{u}} (q : T ⟶ Spec (.of k))
    [LocallyOfFiniteType q] {n : ℤ}
    (hT : ∀ V : irreducibleComponents T, deltaDimension (fieldChowSituation k) q
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = n) (t : T) : 0 ≤ n := by
  rw [← hT ⟨irreducibleComponent t, irreducibleComponent_mem_irreducibleComponents t⟩]
  exact relativeDimension_fieldChowSituation_nonneg k q _

/-- **The dimension of a product over a field.** If every irreducible component of `Y` has
`δ`-dimension `n` and every irreducible component of `Z` has `δ`-dimension `m`, then every
irreducible component of `Y ×_k Z` has `δ`-dimension `n + m`. The projection `Y ×_k Z ⟶ Z` is
flat of relative dimension `n`, being the base change of `Y ⟶ Spec k`, so this is Stacks 02R8
for it. -/
theorem deltaDimension_irreducibleComponent_pullback {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p] (q : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType q] {n m : ℤ}
    (hY : ∀ V : irreducibleComponents Y, deltaDimension (fieldChowSituation k) p
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = n)
    (hZ : ∀ V : irreducibleComponents Z, deltaDimension (fieldChowSituation k) q
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = m)
    (T : irreducibleComponents (pullback p q : Scheme.{u})) :
    deltaDimension (fieldChowSituation k) (pullback.fst p q ≫ p)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = n + m := by
  have hrel : RelativeDimension (pullback.snd p q) n.toNat :=
    RelativeDimension.of_isPullback (IsPullback.of_hasPullback p q)
      (relativeDimension_toNat_of_forall_deltaDimension_eq k p hY)
  obtain ⟨V, hV⟩ := exists_irreducibleComponent_map_genericPoint (pullback.snd p q) T
  have h := deltaDimension_irreducibleComponent_eq_add (fieldChowSituation k) (pullback.snd p q) q
    n.toNat hrel T V hV
  obtain ⟨t, -⟩ := T.2.1.nonempty
  have hn := nonneg_of_forall_deltaDimension_eq k p hY ((pullback.fst p q).base t)
  have hswap : deltaDimension (fieldChowSituation k) (pullback.fst p q ≫ p)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ =
      deltaDimension (fieldChowSituation k) (pullback.snd p q ≫ q)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ := by
    show relativeDimension _ _ _ = relativeDimension _ _ _
    rw [pullback.condition]
  rw [hswap, h, hZ V, Int.toNat_of_nonneg hn, add_comm]

end PureDimension

/-! ### The product of two closed subschemes -/

section ProductSubscheme

variable {S A B X' Y' : Scheme.{u}} (f : X' ⟶ S) (g : Y' ⟶ S) (fA : A ⟶ S) (gB : B ⟶ S)
  (a : A ⟶ X') [IsClosedImmersion a] (b : B ⟶ Y') [IsClosedImmersion b]

/-- The product `a ×_S b : A ×_S B ⟶ X ×_S Y` of two closed immersions is a closed immersion. -/
instance isClosedImmersion_pullbackMap (e₁ : fA ≫ 𝟙 S = a ≫ f) (e₂ : gB ≫ 𝟙 S = b ≫ g) :
    IsClosedImmersion (pullback.map fA gB f g a b (𝟙 S) e₁ e₂) := by
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion.{u}) ‹_› ‹_›
    (by simpa using e₁) (by simpa using e₂)

variable {f g fA gB a b}

/-- **The product of two closed subschemes is cut out by the sum of the inverse images of their
ideals.** For closed immersions `a : A ⟶ X` and `b : B ⟶ Y` over `S`, the product
`A ×_S B ⟶ X ×_S Y` is the closed subscheme of `X ×_S Y` cut out by
`pr_X⁻¹(ker a) + pr_Y⁻¹(ker b)`. -/
def pullbackIsoSubschemeSupComap (hA : a ≫ f = fA) (hB : b ≫ g = gB) :
    (pullback fA gB : Scheme.{u}) ≅
      (a.ker.comap (pullback.fst f g) ⊔ b.ker.comap (pullback.snd f g)).subscheme := by
  let I := a.ker.comap (pullback.fst f g)
  let J := b.ker.comap (pullback.snd f g)
  let h := pullback.map fA gB f g a b (𝟙 S) (by simp [hA]) (by simp [hB])
  have hI : I ≤ h.ker := by
    have e : h = pullback.lift h (pullback.fst fA gB ≫ a.toImage) (by
        rw [Category.assoc, Scheme.Hom.toImage_imageι]
        exact pullback.lift_fst _ _ _) ≫ pullback.fst (pullback.fst f g) a.ker.subschemeι :=
      (pullback.lift_fst _ _ _).symm
    rw [e]
    exact Scheme.Hom.le_ker_comp _ _
  have hJ : J ≤ h.ker := by
    have e : h = pullback.lift h (pullback.snd fA gB ≫ b.toImage) (by
        rw [Category.assoc, Scheme.Hom.toImage_imageι]
        exact pullback.lift_snd _ _ _) ≫ pullback.fst (pullback.snd f g) b.ker.subschemeι :=
      (pullback.lift_fst _ _ _).symm
    rw [e]
    exact Scheme.Hom.le_ker_comp _ _
  let ψ : (pullback fA gB : Scheme.{u}) ⟶ (I ⊔ J).subscheme :=
    IsClosedImmersion.lift (I ⊔ J).subschemeι h (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact sup_le hI hJ)
  have hψ : ψ ≫ (I ⊔ J).subschemeι = h := IsClosedImmersion.lift_fac _ _ _
  let qA : (I ⊔ J).subscheme ⟶ A :=
    Scheme.IdealSheafData.inclusion (le_sup_left : I ≤ I ⊔ J) ≫ (a.ker.comapIso _).hom ≫
      pullback.snd _ _ ≫ (asIso a.toImage).inv
  let qB : (I ⊔ J).subscheme ⟶ B :=
    Scheme.IdealSheafData.inclusion (le_sup_right : J ≤ I ⊔ J) ≫ (b.ker.comapIso _).hom ≫
      pullback.snd _ _ ≫ (asIso b.toImage).inv
  have hqA : qA ≫ a = (I ⊔ J).subschemeι ≫ pullback.fst f g := by
    have : (asIso a.toImage).inv ≫ a = a.imageι := by
      rw [asIso_inv, IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
    simp only [qA, Category.assoc, this]
    rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc,
      Scheme.IdealSheafData.inclusion_subschemeι_assoc]
  have hqB : qB ≫ b = (I ⊔ J).subschemeι ≫ pullback.snd f g := by
    have : (asIso b.toImage).inv ≫ b = b.imageι := by
      rw [asIso_inv, IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
    simp only [qB, Category.assoc, this]
    rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc,
      Scheme.IdealSheafData.inclusion_subschemeι_assoc]
  let φ : (I ⊔ J).subscheme ⟶ (pullback fA gB : Scheme.{u}) :=
    pullback.lift qA qB (by
      rw [← hA, ← hB, ← Category.assoc, hqA, ← Category.assoc, hqB, Category.assoc,
        Category.assoc, pullback.condition])
  have hφ : φ ≫ h = (I ⊔ J).subschemeι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hqA]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hqB]
  refine ⟨ψ, φ, ?_, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← cancel_mono a, Category.assoc,
        hqA, ← Category.assoc, hψ, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, ← cancel_mono b, Category.assoc,
        hqB, ← Category.assoc, hψ, pullback.lift_snd]
  · rw [← cancel_mono (I ⊔ J).subschemeι, Category.assoc, hψ, hφ, Category.id_comp]

/-- The isomorphism `Stacks.Chow.Intersection.pullbackIsoSubschemeSupComap` identifies the
product of the two closed immersions with the closed immersion of the subscheme. -/
@[reassoc (attr := simp)]
theorem pullbackIsoSubschemeSupComap_hom_subschemeι (hA : a ≫ f = fA) (hB : b ≫ g = gB) :
    (pullbackIsoSubschemeSupComap hA hB).hom ≫
        (a.ker.comap (pullback.fst f g) ⊔ b.ker.comap (pullback.snd f g)).subschemeι =
      pullback.map fA gB f g a b (𝟙 S) (by simp [hA]) (by simp [hB]) :=
  IsClosedImmersion.lift_fac _ _ _

end ProductSubscheme

/-! ### The exterior product of the classes of two closed subschemes -/

section ExteriorProduct

variable (k)

/-- The exterior product of the cycles of two closed subschemes `I ⊆ X` and `J ⊆ Y`, the first of
constant relative dimension `r` over the field and the second of `δ`-dimension at most `m`, is
the cycle of the product `I ×_k J`, cut out by `pr_X⁻¹(I) + pr_Y⁻¹(J)`.

At a point `z` over `x ∈ X` and `y ∈ Y` the coefficient of `[I]_r × [J]_m` is
`[I]_r(x) · [J]_m(y)` times the multiplicity of `z` in `closure {x} ×_k closure {y}`; the
multiplicity of `z` in `I ×_k J` factors in the same way, by the multiplicativity of
multiplicities in products (`Stacks.Chow.closedSubschemeCycleCoeff_product_left` and
`Stacks.Chow.closedSubschemeCycleCoeff_product_right`), which rests on Stacks 02RE. -/
theorem exteriorProduct_cycleAssociatedToClosedSubscheme_subschemeι {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY]
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (r : ℕ)
    (hI : RelativeDimension (I.subschemeι ≫ sX) r) {m : ℤ}
    (hJ : schemeDeltaDimension (fieldChowSituation k) (J.subschemeι ≫ sY) ≤ (m : EInt)) :
    exteriorProduct (fieldChowSituation k) sX sY r m
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX I.subschemeι r)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY J.subschemeι m) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k) (pullback.fst sX sY ≫ sX)
        (I.comap (pullback.fst sX sY) ⊔ J.comap (pullback.snd sX sY)).subschemeι (r + m) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [exteriorProduct_apply]
  show closedSubschemeCycleCoeff _ sX I.subschemeι r ((pullback.fst sX sY).base z) *
      closedSubschemeCycleCoeff _ sY J.subschemeι m ((pullback.snd sX sY).base z) *
      exteriorProductWeight _ sX sY (r + m) ((pullback.fst sX sY).base z)
        ((pullback.snd sX sY).base z) z =
    closedSubschemeCycleCoeff _ (pullback.fst sX sY ≫ sX)
      (I.comap (pullback.fst sX sY) ⊔ J.comap (pullback.snd sX sY)).subschemeι (r + m) z
  by_cases hx : (pullback.fst sX sY).base z ∈ I.support
  · rw [closedSubschemeCycleCoeff_product_left _ sX sY I J r hI m hJ z hx]
    by_cases hy : closedSubschemeCycleCoeff _ sY J.subschemeι m ((pullback.snd sX sY).base z) = 0
    · rw [hy]
      ring
    have hδ : relativeDimension (fieldChowSituation k).dimensionFunction sY
        ((pullback.snd sX sY).base z) = m :=
      (mem_cyclesOfDimension_iff_forall_point _ sY m _).1
        (cycleAssociatedToClosedSubscheme _ sY J.subschemeι m).2 _ hy
    obtain ⟨hm, hK⟩ := pointClosure_relativeDimension k sY _ m hδ
    have hIr : schemeDeltaDimension (fieldChowSituation k) (I.subschemeι ≫ sX) ≤
        ((r : ℤ) : EInt) :=
      iSup_le fun V ↦ (congrArg (fun z : ℤ ↦ (z : EInt))
        (Stacks.WeilCohomology.relativeDimension_of_mem_irreducibleComponents_of_relativeDimension
          k _ r hI _ (by
          rw [(V.2.1.isGenericPoint_genericPoint
            (isClosed_of_mem_irreducibleComponents _ V.2)).def]
          exact V.2))).le
    have H := closedSubschemeCycleCoeff_product_right _ sX sY I _ m.toNat hK r hIr z
      (mem_support_vanishingIdeal_closure_self _)
    rw [hm] at H
    rw [H]
    simp only [exteriorProductWeight, exteriorProductIdeal]
    ring
  · have h1 : closedSubschemeCycleCoeff _ sX I.subschemeι r ((pullback.fst sX sY).base z) = 0 :=
      cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range _ sX I.subschemeι r
        (by rwa [Scheme.IdealSheafData.range_subschemeι])
    have h2 : closedSubschemeCycleCoeff _ (pullback.fst sX sY ≫ sX)
        (I.comap (pullback.fst sX sY) ⊔ J.comap (pullback.snd sX sY)).subschemeι (r + m) z = 0 :=
      cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range _ _ _ _ (by
        rw [Scheme.IdealSheafData.range_subschemeι]
        intro hz
        have hz' := Scheme.IdealSheafData.support_antitone
          (le_sup_left : I.comap (pullback.fst sX sY) ≤ _) hz
        rw [Scheme.IdealSheafData.support_comap] at hz'
        exact hx hz')
    rw [h1, h2]
    ring

/-- **The exterior product of the classes of two closed subschemes is the class of their
product.** Let `a : A ⟶ X` and `b : B ⟶ Y` be closed subschemes of schemes locally of finite type
over a field, every irreducible component of `A` of `δ`-dimension `n` and `B` of `δ`-dimension at
most `m`. Then

`[A]_n × [B]_m = [A ×_k B]_{n+m}` in `Z_{n+m}(X ×_k Y)`.

This is the defining rule of the exterior product of Stacks 0FBU, extended from integral closed
subschemes to closed subschemes which need not be integral or reduced. -/
theorem exteriorProduct_cycleAssociatedToClosedSubscheme {X Y A B : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY]
    (a : A ⟶ X) [IsClosedImmersion a] (b : B ⟶ Y) [IsClosedImmersion b]
    (sA : A ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sA]
    (sB : B ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sB]
    (hA : a ≫ sX = sA) (hB : b ≫ sY = sB) {n m : ℤ}
    (hAn : ∀ V : irreducibleComponents A, deltaDimension (fieldChowSituation k) sA
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = n)
    (hBm : schemeDeltaDimension (fieldChowSituation k) sB ≤ (m : EInt)) :
    exteriorProduct (fieldChowSituation k) sX sY n m
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX a n)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY b m) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k) (pullback.fst sX sY ≫ sX)
        (pullback.map sA sB sX sY a b (𝟙 _) (by simp [hA]) (by simp [hB])) (n + m) := by
  subst hA hB
  rcases isEmpty_or_nonempty A with hAe | ⟨⟨t⟩⟩
  · have hA0 : cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX a n = 0 :=
      cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty _ sX a n
    have : IsEmpty (pullback (a ≫ sX) (b ≫ sY) : Scheme.{u}) :=
      Function.isEmpty (pullback.fst (a ≫ sX) (b ≫ sY)).base
    rw [hA0, map_zero, AddMonoidHom.zero_apply,
      cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty]
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le (nonneg_of_forall_deltaDimension_eq k _ hAn t)
  have hrel : RelativeDimension (a ≫ sX) r := by
    simpa using relativeDimension_toNat_of_forall_deltaDimension_eq k _ hAn
  -- replace `A` and `B` by the closed subschemes cut out by the kernels
  let eA : A ≅ a.ker.subscheme := asIso a.toImage
  let eB : B ≅ b.ker.subscheme := asIso b.toImage
  have heA : eA.hom ≫ a.ker.subschemeι = a := a.toImage_imageι
  have heB : eB.hom ≫ b.ker.subschemeι = b := b.toImage_imageι
  have hI : RelativeDimension (a.ker.subschemeι ≫ sX) r := by
    have h' : eA.inv ≫ a = a.ker.subschemeι := by rw [Iso.inv_comp_eq, heA]
    have hsq : IsPullback eA.inv (a.ker.subschemeι ≫ sX) (a ≫ sX) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← Category.assoc, h']⟩
    exact RelativeDimension.of_isPullback hsq hrel
  have hJ : schemeDeltaDimension (fieldChowSituation k) (b.ker.subschemeι ≫ sY) ≤ (m : EInt) := by
    refine schemeDeltaDimension_le_of_forall_relativeDimension_le _ sY _ fun w ↦ ?_
    have h' : eB.inv ≫ b = b.ker.subschemeι := by rw [Iso.inv_comp_eq, heB]
    have hw : b.ker.subschemeι.base w = b.base (eB.inv.base w) := by
      rw [← Scheme.Hom.comp_apply, h']
    exact hw ▸ relativeDimension_le_of_schemeDeltaDimension_le _ sY b hBm _
  rw [cycleAssociatedToClosedSubscheme_eq_of_iso _ sX a a.ker.subschemeι eA heA,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ sY b b.ker.subschemeι eB heB,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ (pullback.fst sX sY ≫ sX) _ _
      (pullbackIsoSubschemeSupComap rfl rfl)
      (pullbackIsoSubschemeSupComap_hom_subschemeι rfl rfl)]
  exact exteriorProduct_cycleAssociatedToClosedSubscheme_subschemeι k sX sY _ _ r hI hJ

end ExteriorProduct

/-! ### The normal bundle of the diagonal of a smooth morphism -/

section NormalBundle

/-- **The normal bundle of the diagonal of a smooth morphism has rank the relative dimension.**
For `W ⟶ S` smooth of relative dimension `N`, the diagonal is a regular immersion
(`Stacks.Chow.isRegularImmersion_diagonal_of_smooth`, Stacks 0FBR) and its normal bundle, the
virtual normal bundle `Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion` of Stacks 0FBQ, is
the dual of the conormal sheaf `𝒞_Δ ≅ Ω_{W/S}` (Stacks 08S2), that is the tangent sheaf
`𝒯_{W/S}`, finite locally free of rank `N`. -/
theorem isFiniteLocallyFreeOfRank_ofIsRegularImmersion_diagonal {W S : Scheme.{u}}
    (sW : W ⟶ S) [Smooth sW] [IsLocallyNoetherian W] {N : ℕ} (hN : RelativeDimension sW N) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (VirtualNormalBundle.ofIsRegularImmersion (pullback.diagonal sW)
        (isRegularImmersion_diagonal_of_smooth sW)).bundle N := by
  have hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := W.ringCatSheaf)
      (conormalModule (pullback.diagonal sW)) N :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal sW)
      (Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials_of_relativeDimension
        sW hN)
  exact Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf _ N hC

end NormalBundle

/-! ### Stacks 0FFD for a Gysin class of the diagonal -/

section ProductMaps

variable {W V₁ V₂ : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S)

/-- The morphism `W ×_k W ⟶ W ×_k W` from the self-product of `W` over `𝟙 W ≫ sW`, on which the
intersection product of `Stacks.Chow.selfIntersectionProduct` caps, to the self-product over
`sW`. -/
private abbrev idSelfProductMap :
    (pullback (𝟙 W ≫ sW) (𝟙 W ≫ sW) : Scheme.{u}) ⟶ pullback sW sW :=
  exteriorToSelfProduct (fieldChowSituation k) sW (𝟙 W) (𝟙 W)

/-- The product `V₁ ×_k V₂ ⟶ W ×_k W` of two morphisms into `W`, with target the self-product
of `W` over `𝟙 W ≫ sW`. -/
private abbrev selfProductMap (i₁ : V₁ ⟶ W) (i₂ : V₂ ⟶ W) :
    (pullback (i₁ ≫ sW) (i₂ ≫ sW) : Scheme.{u}) ⟶ pullback (𝟙 W ≫ sW) (𝟙 W ≫ sW) :=
  pullback.map (i₁ ≫ sW) (i₂ ≫ sW) (𝟙 W ≫ sW) (𝟙 W ≫ sW) i₁ i₂ (𝟙 _) (by simp) (by simp)

end ProductMaps

section Immersion

/-- **The relative dimension is unchanged by an immersion.** For an immersion `i : Z ⟶ X` the
function `δ_{X/S}` of Stacks 02JW pulls back to `δ_{Z/S}`: `i` is a closed immersion into the open
subscheme `i.coborderRange`, followed by the inclusion of that open subscheme, and neither changes
the relative dimension. -/
theorem relativeDimension_comp_isImmersion {X Z S : Scheme.{u}} (δ : DimensionFunction S)
    (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S) (z : Z) :
    relativeDimension δ (i ≫ p) z = relativeDimension δ p (i z) := by
  have h := i.liftCoborder_ι
  calc relativeDimension δ (i ≫ p) z
      = relativeDimension δ (i.liftCoborder ≫ (i.coborderRange.ι ≫ p)) z := by
        rw [← Category.assoc, h]
    _ = relativeDimension δ (i.coborderRange.ι ≫ p) (i.liftCoborder z) :=
        relativeDimension_comp_closedImmersion δ _ _ z
    _ = relativeDimension δ p (i.coborderRange.ι (i.liftCoborder z)) :=
        relativeDimension_comp_isOpenImmersion δ _ _ _
    _ = relativeDimension δ p (i z) := by rw [← Scheme.Hom.comp_apply, h]

end Immersion

section GysinClass

variable (k) (G : GysinSystem (fieldChowSituation k)) {W V₁ V₂ : Scheme.{u}}
  (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]

/-- Transport of the class of a closed subscheme along an equality of structure morphisms. -/
theorem chowGroupCongr_mk_cycleAssociatedToClosedSubscheme {C : ChowSituation.{u}}
    {T Z : Scheme.{u}} {q q' : T ⟶ C.S} [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (hq : q = q') (i : Z ⟶ T) [IsClosedImmersion i] (n : ℤ) :
    chowGroupCongr C hq n (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C q i n)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C q' i n) := by
  subst hq
  rfl

/-- **Stacks 0FFD, the Gysin form.** Let `W` be smooth over `k` of relative dimension `N`, and let
`Δ^! ∈ A^N(W ⟶ W ×_k W)` be a bivariant class of the diagonal satisfying the conclusion of Stacks
0FEA in degree `n₁ + n₂` (`Stacks.Chow.BivariantClass.CapCohenMacaulayFormula`). Let
`V₁, V₂ ⊆ W` be closed subschemes all of whose irreducible components have `δ`-dimension `n₁`,
respectively `n₂`, such that

1. `dim_δ(V₁ ∩ V₂) ≤ n₁ + n₂ - N`, and
2. `𝒪_{V₁,ξ}` and `𝒪_{V₂,ξ}` are Cohen–Macaulay at every `ξ ∈ V₁ ∩ V₂` of `δ`-dimension
   `n₁ + n₂ - N`.

Then `Δ^! ∩ [V₁ ×_k V₂]_{n₁+n₂} = [W ×_{Δ, W ×_k W} (V₁ ×_k V₂)]_{n₁+n₂-N}`.

This is the source's proof: Stacks 0FEA applies to `V₁ ×_k V₂ ⟶ W ×_k W`, whose irreducible
components have `δ`-dimension `n₁ + n₂`
(`Stacks.Chow.Intersection.deltaDimension_irreducibleComponent_pullback`), whose pullback of the
diagonal is `V₁ ∩ V₂` (`Stacks.Chow.Intersection.diagonalPullbackIso`), and whose local rings at
the points of `δ`-dimension `n₁ + n₂ - N` of the intersection are Cohen–Macaulay by Stacks 045J. -/
theorem cap_fundamentalChowClass_exteriorToSelfProduct {N : ℕ}
    (D : BivariantClass (fieldChowSituation k) G sW (selfProductStructure _ sW)
      (pullback.diagonal sW) (diagonal_comp_selfProductStructure _ sW) N) {n₁ n₂ : ℤ}
    (hD : D.CapCohenMacaulayFormula (fieldChowSituation k) G sW (selfProductStructure _ sW)
      (pullback.diagonal sW) (diagonal_comp_selfProductStructure _ sW) N (n₁ + n₂))
    (i₁ : V₁ ⟶ W) [IsClosedImmersion i₁] (i₂ : V₂ ⟶ W) [IsClosedImmersion i₂]
    (h₁ : ∀ T : irreducibleComponents V₁, deltaDimension (fieldChowSituation k) (i₁ ≫ sW)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = n₁)
    (h₂ : ∀ T : irreducibleComponents V₂, deltaDimension (fieldChowSituation k) (i₂ ≫ sW)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = n₂)
    (hdim : schemeDeltaDimension (fieldChowSituation k) (pullback.fst i₁ i₂ ≫ i₁ ≫ sW) ≤
      ((n₁ + n₂ - N : ℤ) : EInt))
    (hCM : CohenMacaulayAtIntersection k sW i₁ i₂ (n₁ + n₂ - N)) :
    D.cap (exteriorToSelfProduct _ sW i₁ i₂) (n₁ + n₂)
        (fundamentalChowClass _ (exteriorToSelfProduct _ sW i₁ i₂ ≫ selfProductStructure _ sW)
          (n₁ + n₂)) =
      fundamentalChowClass _
        (pullback.fst (pullback.diagonal sW) (exteriorToSelfProduct _ sW i₁ i₂) ≫ sW)
        (n₁ + n₂ - N) := by
  let _ : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have hrel : ∀ ξ : (pullback (pullback.diagonal sW) (exteriorToSelfProduct _ sW i₁ i₂) :
      Scheme.{u}),
      relativeDimension (fieldChowSituation k).dimensionFunction
          (exteriorToSelfProduct _ sW i₁ i₂ ≫ selfProductStructure _ sW)
          ((pullback.snd (pullback.diagonal sW) (exteriorToSelfProduct _ sW i₁ i₂)).base ξ) =
        relativeDimension (fieldChowSituation k).dimensionFunction
          (pullback.fst i₁ i₂ ≫ i₁ ≫ sW) ((diagonalPullbackIso sW i₁ i₂).hom.base ξ) := by
    intro ξ
    rw [← relativeDimension_comp_isImmersion _
        (pullback.snd (pullback.diagonal sW) (exteriorToSelfProduct _ sW i₁ i₂))
        (exteriorToSelfProduct _ sW i₁ i₂ ≫ selfProductStructure _ sW) ξ,
      ← Category.assoc, ← pullback.condition, Category.assoc,
      diagonal_comp_selfProductStructure]
    exact (relativeDimension_of_iso _ _ _ (diagonalPullbackIso sW i₁ i₂)
      (diagonalPullbackIso_hom_fst_comp_assoc sW i₁ i₂ sW) ξ).symm
  refine hD _ ?_ ?_ ?_
  · intro T
    show relativeDimension _ _ _ = _
    rw [exteriorToSelfProduct_comp_selfProductStructure]
    exact deltaDimension_irreducibleComponent_pullback k (i₁ ≫ sW) (i₂ ≫ sW) h₁ h₂ T
  · have hpt : ∀ ξ, relativeDimension (fieldChowSituation k).dimensionFunction
        (pullback.snd (pullback.diagonal sW) (exteriorToSelfProduct _ sW i₁ i₂) ≫
          (exteriorToSelfProduct _ sW i₁ i₂ ≫ selfProductStructure _ sW)) ξ ≤ n₁ + n₂ - N :=
      fun ξ ↦ by
        rw [relativeDimension_comp_isImmersion, hrel]
        exact relativeDimension_le_of_schemeDeltaDimension_le' _ _ hdim _
    simpa using schemeDeltaDimension_le_of_forall_relativeDimension_le _
      (pullback.snd (pullback.diagonal sW) (exteriorToSelfProduct _ sW i₁ i₂) ≫
        (exteriorToSelfProduct _ sW i₁ i₂ ≫ selfProductStructure _ sW)) (𝟙 _)
      (by simpa using hpt)
  · intro ξ hξ
    rw [hrel] at hξ
    let : IsLocallyNoetherian (pullback (i₁ ≫ sW) (i₂ ≫ sW) : Scheme.{u}) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (i₁ ≫ sW) (i₂ ≫ sW) ≫ i₁ ≫ sW)
    exact isCohenMacaulayLocalRing_stalk_of_eq
      (base_apply_comp (diagonalPullbackIso_hom_intersectionToProduct sW i₁ i₂) ξ)
      (isCohenMacaulayLocalRing_stalk_intersectionToProduct k sW i₁ i₂ hCM _ hξ)

/-- `Stacks.Chow.Intersection.cap_fundamentalChowClass_exteriorToSelfProduct` for a morphism
`V₁ ×_k V₂ ⟶ W ×_k W` presented in another form. -/
private theorem cap_fundamentalChowClass_of_eq_exteriorToSelfProduct {N : ℕ}
    (D : BivariantClass (fieldChowSituation k) G sW (selfProductStructure _ sW)
      (pullback.diagonal sW) (diagonal_comp_selfProductStructure _ sW) N) {n₁ n₂ : ℤ}
    (hD : D.CapCohenMacaulayFormula (fieldChowSituation k) G sW (selfProductStructure _ sW)
      (pullback.diagonal sW) (diagonal_comp_selfProductStructure _ sW) N (n₁ + n₂))
    (i₁ : V₁ ⟶ W) [IsClosedImmersion i₁] (i₂ : V₂ ⟶ W) [IsClosedImmersion i₂]
    (h₁ : ∀ T : irreducibleComponents V₁, deltaDimension (fieldChowSituation k) (i₁ ≫ sW)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = n₁)
    (h₂ : ∀ T : irreducibleComponents V₂, deltaDimension (fieldChowSituation k) (i₂ ≫ sW)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = n₂)
    (hdim : schemeDeltaDimension (fieldChowSituation k) (pullback.fst i₁ i₂ ≫ i₁ ≫ sW) ≤
      ((n₁ + n₂ - N : ℤ) : EInt))
    (hCM : CohenMacaulayAtIntersection k sW i₁ i₂ (n₁ + n₂ - N))
    (g : (pullback (i₁ ≫ sW) (i₂ ≫ sW) : Scheme.{u}) ⟶ pullback sW sW) [LocallyOfFiniteType g]
    (hg : g = exteriorToSelfProduct _ sW i₁ i₂) :
    D.cap g (n₁ + n₂) (fundamentalChowClass _ (g ≫ selfProductStructure _ sW) (n₁ + n₂)) =
      fundamentalChowClass _ (pullback.fst (pullback.diagonal sW) g ≫ sW) (n₁ + n₂ - N) := by
  subst hg
  exact cap_fundamentalChowClass_exteriorToSelfProduct k G sW D hD i₁ i₂ h₁ h₂ hdim hCM

omit [Smooth sW] in
/-- The defining formula of the product `Stacks.Chow.selfIntersectionProduct`, with the
transports along `𝟙 W ≫ sW = sW` written out. -/
private theorem selfIntersectionProduct_apply (D : ℤ)
    (Dc : BivariantClass (fieldChowSituation k) G sW (selfProductStructure _ sW)
      (pullback.diagonal sW) (diagonal_comp_selfProductStructure _ sW) D) (n m : ℤ)
    (α : chowGroup (fieldChowSituation k) sW n) (β : chowGroup (fieldChowSituation k) sW m) :
    selfIntersectionProduct (fieldChowSituation k)
        (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k) G sW D Dc n m α β =
      chowPushforwardOfIso (fieldChowSituation k) (pullback.fst (𝟙 W) (𝟙 W) ≫ (𝟙 W ≫ sW)) sW
        (pullback.fst (𝟙 W) (𝟙 W)) (by rw [Category.id_comp]) (n + m - D)
        (intersectionProduct (fieldChowSituation k)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k) G sW (𝟙 W) (𝟙 W) D Dc n m
          (TensorProduct.tmul ℤ
            (chowGroupCongr (fieldChowSituation k) (Category.id_comp sW).symm n α)
            (chowGroupCongr (fieldChowSituation k) (Category.id_comp sW).symm m β))) :=
  rfl

/-- **Stacks 0FFD, the intersection-product form.** Let `W` be smooth over `k` of relative
dimension `N`, and let `Δ^! ∈ A^N(W ⟶ W ×_k W)` be a bivariant class of the diagonal satisfying
the conclusion of Stacks 0FEA in degree `n₁ + n₂`
(`Stacks.Chow.BivariantClass.CapCohenMacaulayFormula`). Let `V₁, V₂ ⊆ W` be closed subschemes all
of whose irreducible components have `δ`-dimension `n₁`, respectively `n₂`, put
`d = n₁ + n₂ - N`, and assume

1. `dim_δ(V₁ ∩ V₂) ≤ d`, and
2. `𝒪_{V₁,ξ}` and `𝒪_{V₂,ξ}` are Cohen–Macaulay at every `ξ ∈ V₁ ∩ V₂` with `δ(ξ) = d`.

Then `[V₁]_{n₁} · [V₂]_{n₂} = [V₁ ∩ V₂]_d` in `CH_d(W)`, for the intersection product
`Stacks.Chow.selfIntersectionProduct` formed with `Δ^!`, where `V₁ ∩ V₂ = V₁ ×_W V₂`.

The product is `Δ^!([V₁] × [V₂])` read on `W`. The exterior product `[V₁] × [V₂]` is the
pushforward of `[V₁ ×_k V₂]` along `V₁ ×_k V₂ ⟶ W ×_k W`
(`Stacks.Chow.Intersection.exteriorProduct_cycleAssociatedToClosedSubscheme`), the cap product
commutes with that pushforward (Stacks 0B76 (1)), `Δ^! ∩ [V₁ ×_k V₂] = [V₁ ∩ V₂]` by
`Stacks.Chow.Intersection.cap_fundamentalChowClass_exteriorToSelfProduct`, and the pushforward of
the fundamental class of `V₁ ∩ V₂` to `W` is the class of `V₁ ∩ V₂` as a closed subscheme. -/
theorem selfIntersectionProduct_mk_cycleAssociatedToClosedSubscheme (N : ℕ)
    (D : BivariantClass (fieldChowSituation k) G sW (selfProductStructure _ sW)
      (pullback.diagonal sW) (diagonal_comp_selfProductStructure _ sW) N)
    (i₁ : V₁ ⟶ W) [IsClosedImmersion i₁] (i₂ : V₂ ⟶ W) [IsClosedImmersion i₂] (n₁ n₂ d : ℤ)
    (hd : n₁ + n₂ - N = d)
    (hD : D.CapCohenMacaulayFormula (fieldChowSituation k) G sW (selfProductStructure _ sW)
      (pullback.diagonal sW) (diagonal_comp_selfProductStructure _ sW) N (n₁ + n₂))
    (h₁ : ∀ T : irreducibleComponents V₁, deltaDimension (fieldChowSituation k) (i₁ ≫ sW)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = n₁)
    (h₂ : ∀ T : irreducibleComponents V₂, deltaDimension (fieldChowSituation k) (i₂ ≫ sW)
      ⟨T, T.2.1, isClosed_of_mem_irreducibleComponents _ T.2⟩ = n₂)
    (hdim : schemeDeltaDimension (fieldChowSituation k) (pullback.fst i₁ i₂ ≫ i₁ ≫ sW) ≤
      (d : EInt))
    (hCM : CohenMacaulayAtIntersection k sW i₁ i₂ d) :
    chowGroupDegreeEquiv (fieldChowSituation k) sW hd
        (selfIntersectionProduct (fieldChowSituation k)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k) G sW N D n₁ n₂
          (QuotientAddGroup.mk
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sW i₁ n₁))
          (QuotientAddGroup.mk
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sW i₂ n₂))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sW
        (pullback.fst i₁ i₂ ≫ i₁) d) := by
  subst hd
  rw [selfIntersectionProduct_apply, chowGroupCongr_mk_cycleAssociatedToClosedSubscheme,
    chowGroupCongr_mk_cycleAssociatedToClosedSubscheme,
    intersectionProduct_apply, chowExteriorProduct_tmul_mk,
    exteriorProduct_cycleAssociatedToClosedSubscheme k (𝟙 W ≫ sW) (𝟙 W ≫ sW) i₁ i₂ (i₁ ≫ sW)
      (i₂ ≫ sW) (by simp) (by simp) h₁
      (iSup_le fun V ↦ (congrArg (fun z : ℤ ↦ (z : EInt)) (h₂ V)).le)]
  -- the product `V₁ ×_k V₂ ⟶ W ×_k W` factors through the self-product of `W` over `𝟙 W ≫ sW`
  have hHg : selfProductMap sW i₁ i₂ ≫ idSelfProductMap sW =
      exteriorToSelfProduct (fieldChowSituation k) sW i₁ i₂ := by
    apply pullback.hom_ext <;> simp [selfProductMap, idSelfProductMap, exteriorToSelfProduct]
  have hA : pullback.fst (i₁ ≫ sW) (i₂ ≫ sW) ≫ i₁ ≫ sW =
      (selfProductMap sW i₁ i₂ ≫ idSelfProductMap sW) ≫
        selfProductStructure (fieldChowSituation k) sW := by
    rw [hHg, exteriorToSelfProduct_comp_selfProductStructure]
  -- the exterior product `[V₁] × [V₂]` is the pushforward of `[V₁ ×_k V₂]`
  have hstep : chowGroupCongr (fieldChowSituation k)
      (exteriorToSelfProduct_comp_selfProductStructure (fieldChowSituation k) sW (𝟙 W)
        (𝟙 W)).symm (n₁ + n₂)
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (pullback.fst (𝟙 W ≫ sW) (𝟙 W ≫ sW) ≫ 𝟙 W ≫ sW) (selfProductMap sW i₁ i₂) (n₁ + n₂))) =
      properChowPushforward (fieldChowSituation k)
        ((selfProductMap sW i₁ i₂ ≫ idSelfProductMap sW) ≫
          selfProductStructure (fieldChowSituation k) sW)
        (idSelfProductMap sW ≫ selfProductStructure (fieldChowSituation k) sW)
        (selfProductMap sW i₁ i₂) (by simp only [Category.assoc]) (n₁ + n₂)
        (properPushforwardDescends _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k)
          ((selfProductMap sW i₁ i₂ ≫ idSelfProductMap sW) ≫
            selfProductStructure (fieldChowSituation k) sW) (n₁ + n₂)) := by
    rw [← properPushforward_cycleAssociatedToClosedSubscheme_id (fieldChowSituation k)
      (pullback.fst (i₁ ≫ sW) (i₂ ≫ sW) ≫ i₁ ≫ sW) _ (selfProductMap sW i₁ i₂) (by simp)
      (n₁ + n₂)]
    refine (properChowPushforward_chowGroupCongr (fieldChowSituation k) hA
      (exteriorToSelfProduct_comp_selfProductStructure (fieldChowSituation k) sW (𝟙 W)
        (𝟙 W)).symm (selfProductMap sW i₁ i₂) (by simp) (by simp only [Category.assoc])
      (n₁ + n₂) (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
      (fundamentalChowClass (fieldChowSituation k)
        (pullback.fst (i₁ ≫ sW) (i₂ ≫ sW) ≫ i₁ ≫ sW) (n₁ + n₂))).trans ?_
    rw [chowGroupCongr_fundamentalChowClass]
  rw [hstep]
  -- the cap product commutes with that pushforward (Stacks 0B76 (1)), and Stacks 0FEA applies
  have hB := isPullback_bivariantBaseChangeMap (pullback.diagonal sW) (idSelfProductMap sW)
    (selfProductMap sW i₁ i₂)
  have : IsClosedImmersion (bivariantBaseChangeMap (pullback.diagonal sW) (idSelfProductMap sW)
      (selfProductMap sW i₁ i₂)) :=
    MorphismProperty.of_isPullback hB inferInstance
  rw [D.proper_naturality (idSelfProductMap sW) (selfProductMap sW i₁ i₂) _ hB
      (bivariantBaseChangeMap_fst _ _ _) (n₁ + n₂) (properPushforwardDescends _ _ _ _ _ _)
      (properPushforwardDescends _ _ _ _ _ _),
    cap_fundamentalChowClass_of_eq_exteriorToSelfProduct k G sW D hD i₁ i₂ h₁ h₂ hdim hCM _
      hHg]
  -- push the fundamental class of `W ×_{Δ, W ×_k W} (V₁ ×_k V₂) ≅ V₁ ∩ V₂` forward to `W`
  let e := pullback.congrHom (rfl : pullback.diagonal sW = pullback.diagonal sW) hHg ≪≫
    diagonalPullbackIso sW i₁ i₂
  have h1 : (pullbackDiagonalMapIdIso (𝟙 W) (𝟙 W) sW).hom ≫ pullback.fst (𝟙 W) (𝟙 W) =
      pullback.fst (pullback.diagonal sW) (idSelfProductMap sW) := by
    have h := diagonalPullbackIso_hom_fst_comp sW (𝟙 W) (𝟙 W)
    rwa [Category.comp_id] at h
  have hcomp : e.hom ≫ pullback.fst i₁ i₂ ≫ i₁ =
      ((𝟙 _ ≫ bivariantBaseChangeMap (pullback.diagonal sW) (idSelfProductMap sW)
        (selfProductMap sW i₁ i₂)) ≫ (pullbackDiagonalMapIdIso (𝟙 W) (𝟙 W) sW).hom) ≫
        pullback.fst (𝟙 W) (𝟙 W) := by
    simp only [e, Iso.trans_hom, Category.assoc, Category.id_comp,
      diagonalPullbackIso_hom_fst_comp, h1, bivariantBaseChangeMap_fst, pullback.congrHom_hom]
    simp
  have hfinal := cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation k) sW _ _ e hcomp
    (n₁ + n₂ - N)
  rw [← properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
      (fieldChowSituation k) (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W ≫ sW) sW
      (pullback.fst (𝟙 W) (𝟙 W)) (by rw [Category.id_comp]),
    ← properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
      (fieldChowSituation k) (pullback.fst (pullback.diagonal sW) (idSelfProductMap sW) ≫ sW)
      (pullback.fst (𝟙 W) (𝟙 W) ≫ 𝟙 W ≫ sW) (pullbackDiagonalMapIdIso (𝟙 W) (𝟙 W) sW).hom
      (pullbackDiagonalMapIdIso_hom_comp_structure (fieldChowSituation k) sW (𝟙 W) (𝟙 W)),
    ← properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
      (fieldChowSituation k)
      (pullback.fst (pullback.diagonal sW) (selfProductMap sW i₁ i₂ ≫ idSelfProductMap sW) ≫ sW)
      (pullback.fst (pullback.diagonal sW) (idSelfProductMap sW) ≫ sW) _
      (by rw [← Category.assoc, bivariantBaseChangeMap_fst])] at hfinal
  rw [← hfinal]
  rfl

end GysinClass

/-! ### The source's hypotheses -/

section Source

variable (k)

/-- On an integral scheme of dimension `e` locally of finite type over a field, the generic point
has `δ`-dimension `e` (Stacks 02QO). -/
theorem relativeDimension_genericPoint_eq_of_topologicalKrullDim_eq {T : Scheme.{u}}
    [IsIntegral T] (q : T ⟶ Spec (.of k)) [LocallyOfFiniteType q] {e : ℕ}
    (hT : topologicalKrullDim T = (e : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction q (genericPoint T) = e := by
  have h := topologicalKrullDim_closure_singleton_eq k q (genericPoint T)
  rw [(genericPoint_spec T).def, IsHomeomorph.topologicalKrullDim_eq _
    (Homeomorph.Set.univ T).isHomeomorph, hT] at h
  have h0 := relativeDimension_fieldChowSituation_nonneg k q (genericPoint T)
  have h' : e = (relativeDimension (fieldChowSituation k).dimensionFunction q
      (genericPoint T)).toNat := by exact_mod_cast h
  omega

/-- On an integral scheme of dimension `e` locally of finite type over a field, the only
irreducible component has `δ`-dimension `e`. -/
theorem deltaDimension_eq_of_isIntegral {T : Scheme.{u}} [IsIntegral T] (q : T ⟶ Spec (.of k))
    [LocallyOfFiniteType q] {e : ℕ} (hT : topologicalKrullDim T = (e : WithBot ℕ∞))
    (V : irreducibleComponents T) :
    deltaDimension (fieldChowSituation k) q
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = e := by
  have hV : (V : Set T) = Set.univ :=
    V.2.eq_of_le (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _)
  have hgen : V.2.1.genericPoint = genericPoint T :=
    (V.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ V.2)).eq
      (by rw [hV]; exact genericPoint_spec T)
  show relativeDimension _ q V.2.1.genericPoint = _
  rw [hgen]
  exact relativeDimension_genericPoint_eq_of_topologicalKrullDim_eq k q hT

/-- **Stacks 0FFD, under the source's hypotheses.** Let `k` be a field, let `X` be an integral
scheme smooth over `k` of dimension `dX`, and let `Y, Z ⊆ X` be integral closed
subschemes of dimensions `dY` and `dZ`. Put `d = dY + dZ - dX`, and assume

1. `dim(Y ∩ Z) ≤ d`, and
2. `𝒪_{Y,ξ}` and `𝒪_{Z,ξ}` are Cohen–Macaulay for every `ξ ∈ Y ∩ Z` with `δ(ξ) = d`.

Then `[Y] · [Z] = [Y ∩ Z]_d` in `CH_d(X)`, for the intersection product formed with any Gysin
class `Δ^! ∈ A^{dX}(X ⟶ X ×_k X)` of the diagonal satisfying the conclusion of Stacks 0FEA in
degree `dY + dZ` (`Stacks.Chow.BivariantClass.CapCohenMacaulayFormula`).

This is `Stacks.Chow.Intersection.selfIntersectionProduct_mk_cycleAssociatedToClosedSubscheme`
read at the source's hypotheses: an integral scheme of dimension `e` over `k` is pure of
`δ`-dimension `e`. Hypothesis (1) is stated as
`dim(Y ∩ Z) + dX ≤ dY + dZ`, which is `dim(Y ∩ Z) ≤ d` without the subtraction, so that it has a
meaning also for `d < 0`, where it says that `Y ∩ Z` is empty.

The class `Δ^!` of the source is the Gysin class of the diagonal of Stacks 0FBR, which satisfies
the formula (`Stacks.Chow.diagonalGysinClass_capCohenMacaulayFormula`); the statement for that
class is `selfIntersectionProduct_diagonalGysinClass_mk_of_cohenMacaulayAtIntersection`. -/
theorem selfIntersectionProduct_mk_of_cohenMacaulayAtIntersection
    (G : GysinSystem (fieldChowSituation k)) {X Y Z : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] [Smooth p]
    [IsIntegral X] (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y] (j : Z ⟶ X)
    [IsClosedImmersion j] [IsIntegral Z] (dX dY dZ : ℕ) (d : ℤ)
    (hXdim : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (hZdim : topologicalKrullDim Z = (dZ : WithBot ℕ∞)) (hd : (dY : ℤ) + dZ - dX = d)
    (D : BivariantClass (fieldChowSituation k) G p (selfProductStructure _ p)
      (pullback.diagonal p) (diagonal_comp_selfProductStructure _ p) dX)
    (hD : D.CapCohenMacaulayFormula (fieldChowSituation k) G p (selfProductStructure _ p)
      (pullback.diagonal p) (diagonal_comp_selfProductStructure _ p) dX ((dY : ℤ) + dZ))
    (hIntDim : topologicalKrullDim ↑(pullback i j) + (dX : WithBot ℕ∞) ≤
      (dY : WithBot ℕ∞) + (dZ : WithBot ℕ∞))
    (hCM : CohenMacaulayAtIntersection k p i j d) :
    chowGroupDegreeEquiv (fieldChowSituation k) p hd
        (selfIntersectionProduct (fieldChowSituation k)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k) G p dX D dY dZ
          (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p i dY))
          (QuotientAddGroup.mk
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p j dZ))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
        (pullback.fst i j ≫ i) d) := by
  refine selfIntersectionProduct_mk_cycleAssociatedToClosedSubscheme k G p dX D i j dY dZ d hd
    hD (deltaDimension_eq_of_isIntegral k (i ≫ p) hYdim)
    (deltaDimension_eq_of_isIntegral k (j ≫ p) hZdim) ?_ hCM
  refine iSup_le fun V ↦ WithBotTop.coe_le_coe.mpr ?_
  have h := topologicalKrullDim_irreducibleComponent_eq k (pullback.fst i j ≫ i ≫ p) V.2
  have hle := (h ▸ topologicalKrullDim_subspace_le _ (V : Set ↑(pullback i j)) :
    (((relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst i j ≫ i ≫ p)
      V.2.1.genericPoint).toNat : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↑(pullback i j))
  have hsum : (((relativeDimension (fieldChowSituation k).dimensionFunction
      (pullback.fst i j ≫ i ≫ p) V.2.1.genericPoint).toNat + dX : ℕ) : WithBot ℕ∞) ≤
      ((dY + dZ : ℕ) : WithBot ℕ∞) := by
    push_cast
    exact (add_le_add hle le_rfl).trans hIntDim
  have h0 := relativeDimension_fieldChowSituation_nonneg k (pullback.fst i j ≫ i ≫ p)
    V.2.1.genericPoint
  show relativeDimension _ _ V.2.1.genericPoint ≤ d
  have : (relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst i j ≫ i ≫ p)
      V.2.1.genericPoint).toNat + dX ≤ dY + dZ := by exact_mod_cast hsum
  omega

/-- An integral scheme of dimension `dX` locally of finite type over `k` has relative dimension
`dX` over `k` in the sense of Stacks 02NJ. -/
theorem relativeDimension_of_isIntegral_of_topologicalKrullDim_eq {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] {dX : ℕ}
    (hXdim : topologicalKrullDim X = (dX : WithBot ℕ∞)) : RelativeDimension p dX := by
  have h := relativeDimension_of_isIntegral_over_field k p
  rwa [relativeDimension_genericPoint_eq_of_topologicalKrullDim_eq k p hXdim,
    Int.toNat_natCast] at h

/-- **The Gysin class of the diagonal of `X ⟶ Spec k`** (Stacks 0FBR), for `X` smooth over `k` of
relative dimension `N`, read as a class in `A^N(X ⟶ X ×_k X)` for the structure morphisms of the
intersection product `Stacks.Chow.selfIntersectionProduct`. -/
noncomputable def diagonalGysinClassOverField (p : X ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType p] [Smooth p] {N : ℕ} (hN : RelativeDimension p N) :
    BivariantClass (fieldChowSituation k) (Stacks.WeilCohomology.fieldGysinSystem k) p
      (selfProductStructure _ p) (pullback.diagonal p) (diagonal_comp_selfProductStructure _ p)
      N :=
  bivariantClassCongrBase (fieldChowSituation k) (Stacks.WeilCohomology.fieldGysinSystem k)
    (pullback.diagonal p) (diagonal_comp_selfProductStructure _ p) rfl (N : ℤ)
    (diagonalGysinClass (fieldChowSituation k) p p hN)

/-- The Gysin class of the diagonal of `X ⟶ Spec k` satisfies the conclusion of Stacks 0FEA in
every degree (`Stacks.Chow.diagonalGysinClass_capCohenMacaulayFormula`), read for the structure
morphisms of the intersection product. -/
theorem diagonalGysinClassOverField_capCohenMacaulayFormula (p : X ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType p] [Smooth p] {N : ℕ} (hN : RelativeDimension p N) (n : ℤ) :
    (diagonalGysinClassOverField k p hN).CapCohenMacaulayFormula (fieldChowSituation k)
      (Stacks.WeilCohomology.fieldGysinSystem k) p (selfProductStructure _ p)
      (pullback.diagonal p) (diagonal_comp_selfProductStructure _ p) N n := by
  have h := diagonalGysinClass_capCohenMacaulayFormula (fieldChowSituation k) p p hN n
  intro V gV _ hV hZV hCM
  refine eq_of_heq (((bivariantClassCongrBase_cap (fieldChowSituation k)
      (Stacks.WeilCohomology.fieldGysinSystem k) (pullback.diagonal p)
      (diagonal_comp_selfProductStructure _ p) rfl (N : ℤ)
      (diagonalGysinClass (fieldChowSituation k) p p hN) gV n _ _ HEq.rfl).trans
    (heq_of_eq (h gV hV hZV hCM))).trans ?_)
  exact fundamentalChowClass_heq_of_hom_eq _ (by simp) _

/-- **Stacks Project, Tag 0FFD.** Let `k` be a field, let `X` be an integral scheme smooth over
`k` of dimension `dX`, and let `Y, Z ⊆ X` be integral closed subschemes of dimensions `dY` and
`dZ`. Put `d = dY + dZ - dX`, and assume

1. `dim(Y ∩ Z) ≤ d`, and
2. `𝒪_{Y,ξ}` and `𝒪_{Z,ξ}` are Cohen–Macaulay for every `ξ ∈ Y ∩ Z` with `δ(ξ) = d`.

Then `[Y] · [Z] = [Y ∩ Z]_d` in `CH_d(X)`, where the intersection product
`Stacks.Chow.selfIntersectionProduct` is formed with the Gysin class `Δ^!` of the diagonal of
`X ⟶ Spec k` (Stacks 0FBR), and `Y ∩ Z = Y ×_X Z` is the scheme-theoretic intersection.

This is the source's proof: `Y ×_k Z` is pure of dimension `dY + dZ`, its local rings at the
points of `Y ∩ Z` of `δ`-dimension `d` are Cohen–Macaulay by Stacks 045J, and Stacks 0FEA for
`Δ^!` (`Stacks.Chow.diagonalGysinClass_capCohenMacaulayFormula`, from Stacks 0FBM at vanishing
excess for its closed factor) gives `Δ^! ∩ [Y ×_k Z] = [Y ∩ Z]_d`. Hypothesis (1) is stated as
`dim(Y ∩ Z) + dX ≤ dY + dZ`, which is `dim(Y ∩ Z) ≤ d` without the subtraction. -/
@[stacks 0FFD]
theorem selfIntersectionProduct_diagonalGysinClass_mk_of_cohenMacaulayAtIntersection
    {X Y Z : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] [Smooth p]
    [IsIntegral X] (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y] (j : Z ⟶ X)
    [IsClosedImmersion j] [IsIntegral Z] (dX dY dZ : ℕ) (d : ℤ)
    (hXdim : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y = (dY : WithBot ℕ∞))
    (hZdim : topologicalKrullDim Z = (dZ : WithBot ℕ∞)) (hd : (dY : ℤ) + dZ - dX = d)
    (hIntDim : topologicalKrullDim ↑(pullback i j) + (dX : WithBot ℕ∞) ≤
      (dY : WithBot ℕ∞) + (dZ : WithBot ℕ∞))
    (hCM : CohenMacaulayAtIntersection k p i j d) :
    chowGroupDegreeEquiv (fieldChowSituation k) p hd
        (selfIntersectionProduct (fieldChowSituation k)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
          (Stacks.WeilCohomology.fieldGysinSystem k) p dX
          (diagonalGysinClassOverField k p
            (relativeDimension_of_isIntegral_of_topologicalKrullDim_eq k p hXdim)) dY dZ
          (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p i dY))
          (QuotientAddGroup.mk
            (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p j dZ))) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
        (pullback.fst i j ≫ i) d) :=
  selfIntersectionProduct_mk_of_cohenMacaulayAtIntersection k _ p i j dX dY dZ d hXdim hYdim
    hZdim hd _ (diagonalGysinClassOverField_capCohenMacaulayFormula k p _ _) hIntDim hCM

end Source

end Stacks.Chow.Intersection

end
