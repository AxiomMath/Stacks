module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductProjections
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.AssociatedToModule
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.Intersection.ComputingIntersectionMultiplicities.CohenMacaulayCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.ProductTorIndependence
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackCycles
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularSmooth
public import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseFibreAux
public import StacksCore.Tactic.StacksAttribute

/-!
# Exterior products as intersection products of pullbacks

Let `X` and `Y` be nonsingular varieties over an algebraically closed field `k`, let `α` be an
`r`-cycle on `X` and `β` an `s`-cycle on `Y`. This file proves Stacks 0B0R:

1. `pr_Y^*(β) = [X] × β` and `pr_X^*(α) = α × [Y]`;
2. `α × [Y]` and `[X] × β` intersect properly on `X × Y`;
3. `α × β = (α × [Y]) · ([X] × β) = pr_X^*(α) · pr_Y^*(β)` in `Z_{r+s}(X × Y)`.

## The proof

By linearity everything reduces to prime cycles `α = [V]`, `β = [W]`. The components of
`α × [Y]` are the products `V × Y`, cut out in `X × Y` by the inverse image under `pr_X` of the
ideal of `V`; over an algebraically closed field `V × Y` is again a variety (Tag 05P3), so it is
the reduced closure of its generic point, and `α × [Y] = ∑ nᵢ [Vᵢ × Y]` as a sum over the
components of `α`. Likewise `[X] × β = ∑ mⱼ [X × Wⱼ]`.

Proper intersection (2) is the dimension count `(V × Y) ∩ (X × W) = V × W` with
`dim(V × W) ≤ dim V + dim W` (Tag 0AZM), obtained from the flatness of `V × Y ⟶ Y` and the
topological form of Tag 02RE.

For (3), the product `(V × Y) · (X × W)` of Section 43.14 is the alternating sum of the cycles of
the `Tor` sheaves of `𝒪_{V × Y}` and `𝒪_{X × W}`. These two closed subschemes are Tor independent
(Tag 0CTA, `AlgebraicGeometry.torIndependent_comap_fst_comap_snd`), so only
`Tor_0 = 𝒪_{V × W}` survives and the product is `[V × W]_{r+s}`
(`TorFormula.cycleAssociatedToClosedSubscheme_eq_intersectionProductCycle_of_tor_subsingleton`).
The source gets the same vanishing from Tag 0B02, by observing that `𝒪_{V × Y, ξ}` and
`𝒪_{X × W, ξ}` are Cohen-Macaulay at the generic point `ξ` of `V × W`; Tor independence gives
the vanishing at every point at once and needs neither nonsingularity of `X` and `Y` nor
Cohen-Macaulayness. The nonsingularity of `X` and `Y` is what makes `X × Y` nonsingular
(`AlgebraicGeometry.isRegular_pullback_of_isRegular`), the setting in which the intersection
product is defined.

## Main results

* `flatPullback_projections_eq_exteriorProduct`: part (1), for varieties over an algebraically
  closed field.
* `intersectProperly_exteriorProduct_fundamentalCycle`: part (2).
* `exteriorProduct_eq_intersectionProduct`: part (3), first equality.
* `torFormulaSubvarietyProductTotal_fibreGenericPoints`: the case of prime cycles:
  `(V × Y) · (X × W) = [V × W]_{r+s}`.
* `exteriorProduct_projections`: all three parts.

## Implementation notes

The ground field is `k` and every scheme comes with its structure morphism to `Spec k`; cycles
are graded by the Chow situation `Stacks.Chow.fieldChowSituation k`, as in the neighbouring files
on proper intersections (`Stacks.Intersection.CycleFlatPullback`, Tag 0B0Z). The product
`X × Y` is `pullback sX sY` with structure morphism `pullback.fst sX sY ≫ sX`, and its two
projections are `pullback.fst sX sY = pr_X` and `pullback.snd sX sY = pr_Y`. The fundamental cycle
`[Y]` is `Stacks.Chow.cycleAssociatedToClosedSubscheme _ sY (𝟙 Y) dY`, the cycle of `Y` as a
closed subscheme of itself. Dimensions are natural numbers `dX`, `dY` together with the equations
`dim X = dX`, `dim Y = dY`, and the cycle dimensions `r`, `s` are natural numbers: over a field
`Z_k = 0` for `k < 0`.

The intersection product is `AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct` of
Tag 0B08, the bilinear extension of the Tor-formula product of two closed subvarieties of
Section 43.14, on `X × Y`, which is regular because `X` and `Y` are.

The source writes the last expression of part (3) as `pr_Y^*(α) · pr_X^*(β)`; since `α` lives on
`X` and `β` on `Y`, the subscripts are interchanged there, and the reading forced by part (1),
`pr_X^*(α) · pr_Y^*(β)`, is the one formalized.

## References

* [Stacks Project, Tag 0B0R](https://stacks.math.columbia.edu/tag/0B0R)
* [Stacks Project, Tag 0AZM](https://stacks.math.columbia.edu/tag/0AZM)
* [Stacks Project, Tag 0B02](https://stacks.math.columbia.edu/tag/0B02)
* [Stacks Project, Tag 0CTA](https://stacks.math.columbia.edu/tag/0CTA)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.ExteriorProductProjections

/-! ### Reduced closed subschemes and their generic points -/

/-- A closed subscheme which is reduced is cut out by the vanishing ideal of its support. -/
theorem vanishingIdeal_support_of_isReduced {Z : Scheme.{u}} (I : Z.IdealSheafData)
    [IsReduced I.subscheme] : Scheme.IdealSheafData.vanishingIdeal I.support = I := by
  have h : Closeds.closure (I.subschemeι.base '' ((⊤ : Closeds I.subscheme) : Set I.subscheme)) =
      I.support := by
    apply SetLike.coe_injective
    simp only [Closeds.coe_closure, Closeds.coe_top, Set.image_univ]
    rw [show Set.range I.subschemeι.base = (I.support : Set Z) from I.range_subschemeι]
    exact I.support.isClosed.closure_eq
  rw [← h, ← Scheme.IdealSheafData.map_vanishingIdeal, Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.nilradical_eq_bot, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_subschemeι]

/-- The closure of the image of the generic point of an integral closed subscheme is its
support. -/
theorem closure_singleton_subschemeι_genericPoint {Z : Scheme.{u}} (I : Z.IdealSheafData)
    [IsIntegral I.subscheme] :
    closure ({I.subschemeι.base (genericPoint I.subscheme)} : Set Z) = I.support := by
  rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
    genericPoint_spec, Set.image_univ]
  exact I.range_subschemeι

/-- An integral closed subscheme is the reduced closure of the image of its generic point. -/
theorem integralComponentAt_subschemeι_genericPoint {Z : Scheme.{u}} (I : Z.IdealSheafData)
    [IsIntegral I.subscheme] :
    integralComponentAt (I.subschemeι.base (genericPoint I.subscheme)) = I := by
  have h : Closeds.closure ({I.subschemeι.base (genericPoint I.subscheme)} : Set Z) =
      I.support := SetLike.coe_injective (closure_singleton_subschemeι_genericPoint I)
  rw [integralComponentAt, h, vanishingIdeal_support_of_isReduced]

/-- If an integral closed subscheme is the inverse image under `f` of the closure of a point `x`
in the image of `f`, the generic point of the subscheme lies over `x`: it lies over a point of
the closure of `x`, and it specializes to a point lying over `x`. -/
theorem map_subschemeι_genericPoint_eq {P Z : Scheme.{u}} (f : P ⟶ Z) (I : P.IdealSheafData)
    [IsIntegral I.subscheme] (x : Z)
    (hI : (I.support : Set P) = f.base ⁻¹' closure ({x} : Set Z))
    (hx : x ∈ Set.range f.base) :
    f.base (I.subschemeι.base (genericPoint I.subscheme)) = x := by
  set p := I.subschemeι.base (genericPoint I.subscheme) with hpdef
  have hcl := closure_singleton_subschemeι_genericPoint I
  have hp : p ∈ (I.support : Set P) := hcl ▸ subset_closure rfl
  rw [hI] at hp
  obtain ⟨z, hz⟩ := hx
  have hzI : z ∈ (I.support : Set P) := by
    rw [hI, Set.mem_preimage, hz]
    exact subset_closure rfl
  rw [← hcl] at hzI
  have h1 : x ⤳ f.base p := specializes_iff_mem_closure.mpr hp
  have h2 : f.base p ⤳ x := hz ▸ (specializes_iff_mem_closure.mpr hzI).map f.continuous
  exact (h2.antisymm h1).eq

/-- Over a field, a point whose closure has dimension `n` has relative dimension `n`. -/
theorem relativeDimension_eq_of_topologicalKrullDim_closure (k : Type u) [Field k]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p] (z : Z) (n : ℕ)
    (h : topologicalKrullDim (closure ({z} : Set Z)) = (n : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction p z = n := by
  have hnn := relativeDimension_nonneg (fieldChowSituation k) (fun _ _ ↦ rfl) p z
  rw [topologicalKrullDim_closure_singleton_eq k p z] at h
  have h' : (relativeDimension (fieldChowSituation k).dimensionFunction p z).toNat = n := by
    exact_mod_cast h
  omega

/-- Over a field, a point of relative dimension `n` has closure of dimension `n`. -/
theorem topologicalKrullDim_closure_of_relativeDimension_eq (k : Type u) [Field k]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p] (z : Z) (n : ℕ)
    (h : relativeDimension (fieldChowSituation k).dimensionFunction p z = n) :
    topologicalKrullDim (closure ({z} : Set Z)) = (n : WithBot ℕ∞) := by
  rw [topologicalKrullDim_closure_singleton_eq k p z, h]
  simp

/-- Over a field, a closed subscheme of dimension at most `n` has delta-dimension at most `n`. -/
theorem schemeDeltaDimension_subschemeι_le (k : Type u) [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p] (I : Z.IdealSheafData) (n : ℕ)
    (h : topologicalKrullDim (I.support : Set Z) ≤ (n : WithBot ℕ∞)) :
    schemeDeltaDimension (fieldChowSituation k) (I.subschemeι ≫ p) ≤ ((n : ℤ) : EInt) :=
  schemeDeltaDimension_le_of_forall_point (fieldChowSituation k) p I.subschemeι fun z ↦
    relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation k) (fun _ _ ↦ rfl) p
      I.support.isClosed h (by
        rw [← I.range_subschemeι]
        exact Set.mem_range_self z)

/-- A closed subscheme of a variety which is integral is again a variety. -/
theorem isVariety_subschemeι_comp (k : Type u) [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [IsVariety k p] (I : Z.IdealSheafData) [IsIntegral I.subscheme] :
    IsVariety k (I.subschemeι ≫ p) := by
  constructor

/-- The reduced closure of a point of a variety, over the base, is a variety. -/
private theorem isVariety_closure_subschemeι_comp (k : Type u) [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [IsVariety k p] (z : Z) :
    IsVariety k ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({z} : Set Z))).subschemeι ≫ p) :=
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure z
  isVariety_subschemeι_comp k p _

/-! ### The products `V × Y` and `X × W` -/

section Product

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k))

/-- Over a field every point of `X` has a point of `X × Y` over it, `Y` being nonempty. -/
theorem mem_range_fst [Nonempty Y] (x : X) : x ∈ Set.range (pullback.fst sX sY).base := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x (Classical.arbitrary Y)
    (Subsingleton.elim (α := Spec (.of k)) _ _)
  exact ⟨z, hz⟩

/-- Over a field every point of `Y` has a point of `X × Y` over it, `X` being nonempty. -/
theorem mem_range_snd [Nonempty X] (y : Y) : y ∈ Set.range (pullback.snd sX sY).base := by
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (Classical.arbitrary X) y
    (Subsingleton.elim (α := Spec (.of k)) _ _)
  exact ⟨z, hz⟩

variable [IsAlgClosed k] [IsVariety k sX] [IsVariety k sY]

/-- **`V × Y` is integral.** Over an algebraically closed field the inverse image under `pr_X` of
the reduced closure `V` of a point of `X` is the product `V ×_k Y` of two varieties, which is a
variety by Tag 05P3. -/
instance isIntegral_comap_fst (x : X) :
    IsIntegral ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap (pullback.fst sX sY)).subscheme := by
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  have := isVariety_subschemeι_comp k sX
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)))
  have := isVariety_pullback k ((Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({x} : Set X))).subschemeι ≫ sX) sY
  have : Nonempty ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap (pullback.fst sX sY)).subscheme :=
    ⟨(pointClosureFibreIso sX sY x).inv.base (Classical.arbitrary _)⟩
  exact isIntegral_of_isOpenImmersion (pointClosureFibreIso sX sY x).hom

/-- The inverse image of the reduced closure of `y : Y` under the second projection, as a closed
subscheme of `X ×_S Y`, is the fibre product `X ×_S closure {y}`. -/
def pointClosureFibreSndIso {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (y : Y) :
    (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).comap (pullback.snd f g)).subscheme) ≅
      pullback f ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).subschemeι ≫ g) :=
  ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comapIso (pullback.snd f g)).trans
    (pullbackLeftPullbackSndIso f g (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).subschemeι)

/-- **`X × W` is integral**, by Tag 05P3. -/
instance isIntegral_comap_snd (y : Y) :
    IsIntegral ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap (pullback.snd sX sY)).subscheme := by
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure y
  have := isVariety_subschemeι_comp k sY
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y)))
  have := isVariety_pullback k sX ((Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({y} : Set Y))).subschemeι ≫ sY)
  have : Nonempty ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap (pullback.snd sX sY)).subscheme :=
    ⟨(pointClosureFibreSndIso sX sY y).inv.base (Classical.arbitrary _)⟩
  exact isIntegral_of_isOpenImmersion (pointClosureFibreSndIso sX sY y).hom

omit [IsAlgClosed k] in
/-- **`dim(V × Y) = dim V + dim Y`**, by Tag 0B2M. -/
theorem topologicalKrullDim_comap_fst (x : X) :
    topologicalKrullDim ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap (pullback.fst sX sY)).subscheme =
      topologicalKrullDim (closure ({x} : Set X)) + topologicalKrullDim Y := by
  have := isVariety_closure_subschemeι_comp k sX x
  rw [IsHomeomorph.topologicalKrullDim_eq _
      (pointClosureFibreIso sX sY x).hom.homeomorph.isHomeomorph,
    topologicalKrullDim_pullback_of_isVariety, topologicalKrullDim_subscheme,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]

omit [IsAlgClosed k] in
/-- **`dim(X × W) = dim X + dim W`**, by Tag 0B2M. -/
theorem topologicalKrullDim_comap_snd (y : Y) :
    topologicalKrullDim ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap (pullback.snd sX sY)).subscheme =
      topologicalKrullDim X + topologicalKrullDim (closure ({y} : Set Y)) := by
  have := isVariety_closure_subschemeι_comp k sY y
  rw [IsHomeomorph.topologicalKrullDim_eq _
      (pointClosureFibreSndIso sX sY y).hom.homeomorph.isHomeomorph,
    topologicalKrullDim_pullback_of_isVariety, topologicalKrullDim_subscheme,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]

/-- **`dim(V × W) ≤ dim V + dim W`.** The support of the product `closure {x} ×_k closure {y}`
inside `X ×_k Y` has dimension at most `r + s` when `closure {x}` has dimension `r` and
`closure {y}` dimension at most `s`: it is the inverse image of `closure {y}` under the flat
projection `V × Y ⟶ Y` of relative dimension `r`, and the topological form of Tag 02RE
applies. -/
theorem topologicalKrullDim_support_exteriorProductIdeal_le (x : X) (y : Y) (r s : ℕ)
    (hx : topologicalKrullDim (closure ({x} : Set X)) = (r : WithBot ℕ∞))
    (hy : topologicalKrullDim (closure ({y} : Set Y)) ≤ (s : WithBot ℕ∞)) :
    topologicalKrullDim ((exteriorProductIdeal sX sY x y).support :
      Set (pullback sX sY : Scheme.{u})) ≤ ((s + r : ℕ) : WithBot ℕ∞) := by
  set V := (Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({x} : Set X))).comap (pullback.fst sX sY) with hV
  set q : V.subscheme ⟶ Y := V.subschemeι ≫ pullback.snd sX sY with hq
  have : Flat q := flat_pointClosurePullback_snd sX sY x
  have : IsVariety k (q ≫ sY) := by constructor
  have he : topologicalKrullDim V.subscheme = topologicalKrullDim Y + (r : WithBot ℕ∞) := by
    rw [hV, topologicalKrullDim_comap_fst, hx, add_comm]
  have hpre := Stacks.Intersection.CycleFlatPullback.topologicalKrullDim_preimage_le k (q ≫ sY)
    sY q rfl r he (Closeds.closure ({y} : Set Y)) s (by rw [Closeds.coe_closure]; exact hy)
  have hset : ((exteriorProductIdeal sX sY x y).support : Set (pullback sX sY : Scheme.{u})) =
      V.subschemeι.base '' (V.subschemeι.base ⁻¹'
        ((pullback.snd sX sY).base ⁻¹' (Closeds.closure ({y} : Set Y) : Set Y))) := by
    rw [Set.image_preimage_eq_range_inter, show Set.range V.subschemeι.base =
        (V.support : Set (pullback sX sY : Scheme.{u})) from V.range_subschemeι,
      exteriorProductIdeal, Scheme.IdealSheafData.support_sup, ← hV]
    simp [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rw [hset]
  have hemb : Topology.IsEmbedding V.subschemeι.base := V.subschemeι.isClosedEmbedding.isEmbedding
  rw [← IsHomeomorph.topologicalKrullDim_eq _ (hemb.homeomorphImage _).isHomeomorph]
  exact hpre

end Product

/-! ### Cycles of closed subschemes -/

/-- A point at which the cycle of a closed subscheme has a nonzero coefficient lies on the closed
subscheme and has the relative dimension at which the cycle is formed. -/
theorem mem_range_and_relativeDimension_of_cycleAssociatedToClosedSubscheme_ne_zero
    (C : ChowSituation.{u}) {Z W : Scheme.{u}} (p : Z ⟶ C.S) [LocallyOfFiniteType p]
    (i : W ⟶ Z) [IsClosedImmersion i] (n : ℤ) (z : Z)
    (h : (cycleAssociatedToClosedSubscheme C p i n).1 z ≠ 0) :
    z ∈ Set.range i.base ∧ relativeDimension C.dimensionFunction p z = n := by
  change closedSubschemeCycleCoeff C p i n z ≠ 0 at h
  unfold closedSubschemeCycleCoeff at h
  split_ifs at h with hex
  · obtain ⟨ξ, h1, h2⟩ := hex
    exact ⟨⟨ξ.1, h1⟩, h2⟩
  · exact absurd rfl h

/-! ### The intersection product of two cycles with reindexed components -/

/-- **The intersection product of two cycles whose components are indexed by two other sets.**
If the components of `a` are the points `ι x`, with coefficient `α x`, and those of `b` the points
`κ y`, with coefficient `β y`, for injective `ι` and `κ` and finitely supported `α` and `β`, then
`a · b = ∑ₓ ∑_y α x β y (ι x) · (κ y)`. -/
theorem cycleIntersectionProduct_eq_sum_of_reindex {P A B : Scheme.{u}}
    (prod : P → P → AlgebraicCycle P ℤ) (a b : AlgebraicCycle P ℤ) (α : A → ℤ) (β : B → ℤ)
    (sα : Finset A) (sβ : Finset B) (hα : ∀ x, α x ≠ 0 → x ∈ sα) (hβ : ∀ y, β y ≠ 0 → y ∈ sβ)
    (ι : A → P) (κ : B → P) (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (haι : ∀ x, a (ι x) = α x) (hbκ : ∀ y, b (κ y) = β y)
    (ha : ∀ p, a p ≠ 0 → p ∈ Set.range ι) (hb : ∀ q, b q ≠ 0 → q ∈ Set.range κ) :
    cycleIntersectionProduct prod a b = ∑ x ∈ sα, ∑ y ∈ sβ, (α x * β y) • prod (ι x) (κ y) := by
  classical
  rw [cycleIntersectionProduct,
    finsum_eq_sum_of_support_subset _ (s := sα.image ι ×ˢ sβ.image κ) ?_, Finset.sum_product,
    Finset.sum_image fun x _ x' _ h ↦ hι h]
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_image fun y _ y' _ h ↦ hκ h]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    simp only [cycleIntersectionProductSummand, haι, hbκ]
  · intro q hq
    obtain ⟨h1, h2⟩ := support_cycleIntersectionProductSummand_subset prod a b hq
    obtain ⟨x, hx⟩ := ha q.1 h1
    obtain ⟨y, hy⟩ := hb q.2 h2
    have hx' : α x ≠ 0 := by rw [← haι, hx]; exact h1
    have hy' : β y ≠ 0 := by rw [← hbκ, hy]; exact h2
    simp only [Finset.coe_product, Finset.coe_image, Set.mem_prod, Set.mem_image,
      Finset.mem_coe]
    exact ⟨⟨x, hα x hx', hx⟩, ⟨y, hβ y hy', hy⟩⟩

/-! ### The generic points of `V × Y` and `X × W` -/

section GenericPoints

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k)) [IsVariety k sX] [IsVariety k sY]

/-- The generic point of `closure {x} × Y`, the component of `[closure {x}] × [Y]`. -/
def fstFibreGenericPoint (x : X) : (pullback sX sY : Scheme.{u}) :=
  ((Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({x} : Set X))).comap (pullback.fst sX sY)).subschemeι.base
      (genericPoint _)

/-- The generic point of `X × closure {y}`, the component of `[X] × [closure {y}]`. -/
def sndFibreGenericPoint (y : Y) : (pullback sX sY : Scheme.{u}) :=
  ((Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({y} : Set Y))).comap (pullback.snd sX sY)).subschemeι.base
      (genericPoint _)

/-- The first projection maps the generic point of `closure {x} × Y` to `x`. -/
theorem fst_fstFibreGenericPoint (x : X) :
    (pullback.fst sX sY).base (fstFibreGenericPoint sX sY x) = x :=
  map_subschemeι_genericPoint_eq _ _ x
    (by simp [Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.coe_support_vanishingIdeal])
    (mem_range_fst sX sY x)

/-- The second projection maps the generic point of `X × closure {y}` to `y`. -/
theorem snd_sndFibreGenericPoint (y : Y) :
    (pullback.snd sX sY).base (sndFibreGenericPoint sX sY y) = y :=
  map_subschemeι_genericPoint_eq _ _ y
    (by simp [Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.coe_support_vanishingIdeal])
    (mem_range_snd sX sY y)

/-- The second projection maps the generic point of `closure {x} × Y` to the generic point of
`Y`. -/
theorem snd_fstFibreGenericPoint (x : X) :
    (pullback.snd sX sY).base (fstFibreGenericPoint sX sY x) = genericPoint Y :=
  snd_genericPoint_pointClosurePullback sX sY x
    ⟨genericPoint _, by simp [genericPoints_eq_singleton]⟩

/-- The first projection maps the generic point of `X × closure {y}` to the generic point of
`X`. -/
theorem fst_sndFibreGenericPoint (y : Y) :
    (pullback.fst sX sY).base (sndFibreGenericPoint sX sY y) = genericPoint X :=
  fst_genericPoint_pointClosurePullback sX sY y
    ⟨genericPoint _, by simp [genericPoints_eq_singleton]⟩

/-- The map `x ↦ fstFibreGenericPoint sX sY x` is injective. -/
theorem fstFibreGenericPoint_injective : Function.Injective (fstFibreGenericPoint sX sY) :=
  fun x x' h ↦ by
    rw [← fst_fstFibreGenericPoint sX sY x, h, fst_fstFibreGenericPoint]

/-- The map `y ↦ sndFibreGenericPoint sX sY y` is injective. -/
theorem sndFibreGenericPoint_injective : Function.Injective (sndFibreGenericPoint sX sY) :=
  fun y y' h ↦ by
    rw [← snd_sndFibreGenericPoint sX sY y, h, snd_sndFibreGenericPoint]

/-- The integral closed subscheme with generic point `fstFibreGenericPoint sX sY x` is the inverse
image under the first projection of the reduced closed subscheme `closure {x}`. -/
theorem integralComponentAt_fstFibreGenericPoint (x : X) :
    integralComponentAt (fstFibreGenericPoint sX sY x) =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst sX sY) :=
  integralComponentAt_subschemeι_genericPoint _

/-- The integral closed subscheme with generic point `sndFibreGenericPoint sX sY y` is the
inverse image under the second projection of the reduced closed subscheme `closure {y}`. -/
theorem integralComponentAt_sndFibreGenericPoint (y : Y) :
    integralComponentAt (sndFibreGenericPoint sX sY y) =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).comap (pullback.snd sX sY) :=
  integralComponentAt_subschemeι_genericPoint _

/-- The component `closure {x} × Y` has relative dimension `r + dim Y` when `x` has relative
dimension `r`. -/
theorem relativeDimension_fstFibreGenericPoint (x : X) (r dY : ℕ)
    (hx : relativeDimension (fieldChowSituation k).dimensionFunction sX x = r)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst sX sY ≫ sX)
      (fstFibreGenericPoint sX sY x) = (r : ℤ) + (dY : ℤ) := by
  have h := relativeDimension_eq_of_topologicalKrullDim_closure k (pullback.fst sX sY ≫ sX)
    (fstFibreGenericPoint sX sY x) (r + dY) (by
      rw [fstFibreGenericPoint, closure_singleton_subschemeι_genericPoint,
        ← topologicalKrullDim_subscheme, topologicalKrullDim_comap_fst,
        topologicalKrullDim_closure_of_relativeDimension_eq k sX x r hx, hdY]
      push_cast; rfl)
  rw [h]; push_cast; rfl

/-- The component `X × closure {y}` has relative dimension `dim X + s` when `y` has relative
dimension `s`. -/
theorem relativeDimension_sndFibreGenericPoint (y : Y) (s dX : ℕ)
    (hy : relativeDimension (fieldChowSituation k).dimensionFunction sY y = s)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst sX sY ≫ sX)
      (sndFibreGenericPoint sX sY y) = (dX : ℤ) + (s : ℤ) := by
  have h := relativeDimension_eq_of_topologicalKrullDim_closure k (pullback.fst sX sY ≫ sX)
    (sndFibreGenericPoint sX sY y) (dX + s) (by
      rw [sndFibreGenericPoint, closure_singleton_subschemeι_genericPoint,
        ← topologicalKrullDim_subscheme, topologicalKrullDim_comap_snd,
        topologicalKrullDim_closure_of_relativeDimension_eq k sY y s hy, hdX]
      push_cast; rfl)
  rw [h]; push_cast; rfl

omit [IsAlgClosed k] in
/-- The generic point of a variety of dimension `d` has relative dimension `d`. -/
theorem relativeDimension_genericPoint {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k)) [IsVariety k p]
    (d : ℕ) (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction p (genericPoint Z) = d :=
  relativeDimension_eq_of_topologicalKrullDim_closure k p _ d (by
    rw [genericPoint_spec, ← hd]
    exact (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq)

end GenericPoints

/-- The fundamental cycle of a variety of dimension `d` has coefficient one at the generic
point. -/
private theorem fundamentalCycle_apply_genericPoint {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [IsVariety k p] (d : ℕ) (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 Z) (d : ℤ)).1
      (genericPoint Z) = 1 :=
  cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint (fieldChowSituation k) p (𝟙 Z)
    (d : ℤ) (by simpa using relativeDimension_genericPoint p d hd)

/-- A point at which the cycle of an integral closed subscheme is nonzero is the image of its
generic point. -/
private theorem eq_genericPoint_of_cycleAssociatedToClosedSubscheme_ne_zero
    (C : ChowSituation.{u}) {Y Z : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] (n : ℤ) {y : Y}
    (h : (cycleAssociatedToClosedSubscheme C sY i n).1 y ≠ 0) :
    y = i (genericPoint Z) :=
  of_not_not fun hne ↦
    h (cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne C sY i n hne)

/-- The exterior product weight at the generic point of an integral component is one. -/
private theorem exteriorProductWeight_apply_genericPoint (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (n : ℤ) (x : X) (y : Y)
    (I : (pullback f g : Scheme.{u}).IdealSheafData) [IsIntegral I.subscheme]
    (h : exteriorProductIdeal f g x y = I) {z : (pullback f g : Scheme.{u})}
    (hz : z = I.subschemeι (genericPoint I.subscheme))
    (hdim : relativeDimension C.dimensionFunction (pullback.fst f g ≫ f) z = n) :
    exteriorProductWeight C f g n x y z = 1 := by
  subst hz
  rw [exteriorProductWeight, closedSubschemeCycleCoeff_congr _ _ h]
  exact cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint C _ I.subschemeι n hdim

/-- A point with nonzero exterior product weight is the image of the generic point of the
integral component. -/
private theorem eq_genericPoint_of_exteriorProductWeight_ne_zero (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (n : ℤ) (x : X) (y : Y)
    (I : (pullback f g : Scheme.{u}).IdealSheafData) [IsIntegral I.subscheme]
    (h : exteriorProductIdeal f g x y = I) {z : (pullback f g : Scheme.{u})}
    (hz : exteriorProductWeight C f g n x y z ≠ 0) :
    z = I.subschemeι (genericPoint I.subscheme) := by
  rw [exteriorProductWeight, closedSubschemeCycleCoeff_congr _ _ h] at hz
  exact eq_genericPoint_of_cycleAssociatedToClosedSubscheme_ne_zero C _ I.subschemeι n hz

/-- A point at which a cycle of dimension `n` is nonzero has relative dimension `n`. -/
private theorem relativeDimension_eq_of_cycle_apply_ne_zero (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] {n : ℤ} (α : CycleGroup C f n) {x : X}
    (hα : α.1 x ≠ 0) : relativeDimension C.dimensionFunction f x = n :=
  (mem_cyclesOfDimension_iff_forall_point C f _ α.1).1 α.2 x hα

/-! ### The cycles `α × [Y]` and `[X] × β` -/

section Coefficients

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k)) [IsVariety k sX] [IsVariety k sY]

/-- The coefficient of `α × [Y]` at the generic point of `closure {x} × Y` is `α x`. -/
theorem exteriorProduct_fundamentalCycle_apply_fstFibreGenericPoint (dY : ℕ)
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) (r : ℕ)
    (α : CycleGroup (fieldChowSituation k) sX (r : ℤ)) (x : X) :
    (exteriorProduct (fieldChowSituation k) sX sY (r : ℤ) (dY : ℤ) α
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY (𝟙 Y) (dY : ℤ))).1
      (fstFibreGenericPoint sX sY x) = α.1 x := by
  rw [exteriorProduct_apply, fst_fstFibreGenericPoint, snd_fstFibreGenericPoint,
    fundamentalCycle_apply_genericPoint sY dY hdY, mul_one]
  by_cases hα : α.1 x = 0
  · rw [hα, zero_mul]
  have hw := exteriorProductWeight_apply_genericPoint (fieldChowSituation k) sX sY
    ((r : ℤ) + (dY : ℤ)) x (genericPoint Y) _ (exteriorProductIdeal_genericPoint_right sX sY x)
    (z := fstFibreGenericPoint sX sY x) rfl
    (relativeDimension_fstFibreGenericPoint sX sY x r dY
      (relativeDimension_eq_of_cycle_apply_ne_zero (fieldChowSituation k) sX α hα) hdY)
  rw [hw, mul_one]

/-- The coefficient of `[X] × β` at the generic point of `X × closure {y}` is `β y`. -/
theorem fundamentalCycle_exteriorProduct_apply_sndFibreGenericPoint (dX : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞)) (s : ℕ)
    (β : CycleGroup (fieldChowSituation k) sY (s : ℤ)) (y : Y) :
    (exteriorProduct (fieldChowSituation k) sX sY (dX : ℤ) (s : ℤ)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX (𝟙 X) (dX : ℤ)) β).1
      (sndFibreGenericPoint sX sY y) = β.1 y := by
  rw [exteriorProduct_apply, fst_sndFibreGenericPoint, snd_sndFibreGenericPoint,
    fundamentalCycle_apply_genericPoint sX dX hdX, one_mul]
  by_cases hβ : β.1 y = 0
  · rw [hβ, zero_mul]
  have hw := exteriorProductWeight_apply_genericPoint (fieldChowSituation k) sX sY
    ((dX : ℤ) + (s : ℤ)) (genericPoint X) y _ (exteriorProductIdeal_genericPoint_left sX sY y)
    (z := sndFibreGenericPoint sX sY y) rfl
    (relativeDimension_sndFibreGenericPoint sX sY y s dX
      (relativeDimension_eq_of_cycle_apply_ne_zero (fieldChowSituation k) sY β hβ) hdX)
  rw [hw, mul_one]

/-- The only components of `α × [Y]` are the products `closure {x} × Y`. -/
theorem eq_fstFibreGenericPoint_of_exteriorProduct_fundamentalCycle_ne_zero (dY r : ℕ)
    (α : CycleGroup (fieldChowSituation k) sX (r : ℤ)) (p : (pullback sX sY : Scheme.{u}))
    (hp : (exteriorProduct (fieldChowSituation k) sX sY (r : ℤ) (dY : ℤ) α
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY (𝟙 Y) (dY : ℤ))).1 p ≠ 0) :
    p = fstFibreGenericPoint sX sY ((pullback.fst sX sY).base p) := by
  rw [exteriorProduct_apply] at hp
  obtain ⟨h12, hw⟩ := mul_ne_zero_iff.1 hp
  have hgen : (pullback.snd sX sY).base p = genericPoint Y :=
    eq_genericPoint_of_cycleAssociatedToClosedSubscheme_ne_zero (fieldChowSituation k) sY (𝟙 Y) _
      (mul_ne_zero_iff.1 h12).2
  rw [hgen] at hw
  exact eq_genericPoint_of_exteriorProductWeight_ne_zero (fieldChowSituation k) sX sY _ _ _ _
    (exteriorProductIdeal_genericPoint_right sX sY _) hw

/-- The only components of `[X] × β` are the products `X × closure {y}`. -/
theorem eq_sndFibreGenericPoint_of_fundamentalCycle_exteriorProduct_ne_zero (dX s : ℕ)
    (β : CycleGroup (fieldChowSituation k) sY (s : ℤ)) (q : (pullback sX sY : Scheme.{u}))
    (hq : (exteriorProduct (fieldChowSituation k) sX sY (dX : ℤ) (s : ℤ)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX (𝟙 X) (dX : ℤ)) β).1 q ≠ 0) :
    q = sndFibreGenericPoint sX sY ((pullback.snd sX sY).base q) := by
  rw [exteriorProduct_apply] at hq
  obtain ⟨h12, hw⟩ := mul_ne_zero_iff.1 hq
  have hgen : (pullback.fst sX sY).base q = genericPoint X :=
    eq_genericPoint_of_cycleAssociatedToClosedSubscheme_ne_zero (fieldChowSituation k) sX (𝟙 X) _
      (mul_ne_zero_iff.1 h12).1
  rw [hgen] at hw
  exact eq_genericPoint_of_exteriorProductWeight_ne_zero (fieldChowSituation k) sX sY _ _ _ _
    (exteriorProductIdeal_genericPoint_left sX sY _) hw

end Coefficients

/-! ### The product of two subvarieties of `X × Y` in product position -/

section Product

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k))

/-- A product of two schemes locally of finite type over a field is locally Noetherian. -/
@[ega "I 6.6.7" "special case"]
instance isLocallyNoetherian_pullback_of_field [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY] : IsLocallyNoetherian (pullback sX sY : Scheme.{u}) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.fst sX sY ≫ sX)

variable [IsAlgClosed k] [IsVariety k sX] [IsVariety k sY]

/-- A point carrying a nonzero coefficient in the product `[closure {x} × closure {y}]_{r+s}`
lies over `y`, for `x` of relative dimension `r` and `y` of relative dimension `s`: such a point
has relative dimension `r + s`, and if it lay over a proper specialization `y'` of `y` it would
lie on `closure {x} × closure {y'}`, whose dimension is smaller than `r + s`. -/
theorem snd_eq_of_exteriorProductWeight_ne_zero (x : X) (y : Y) (r s : ℕ)
    (hx : relativeDimension (fieldChowSituation k).dimensionFunction sX x = r)
    (hy : relativeDimension (fieldChowSituation k).dimensionFunction sY y = s)
    (z : (pullback sX sY : Scheme.{u}))
    (hz : exteriorProductWeight (fieldChowSituation k) sX sY ((r : ℤ) + (s : ℤ)) x y z ≠ 0) :
    (pullback.snd sX sY).base z = y := by
  obtain ⟨hzE, hzdim⟩ :=
    mem_range_and_relativeDimension_of_cycleAssociatedToClosedSubscheme_ne_zero _ _ _ _ z hz
  rw [Scheme.IdealSheafData.range_subschemeι, exteriorProductIdeal,
    Scheme.IdealSheafData.support_sup] at hzE
  simp only [Closeds.coe_inf, Set.mem_inter_iff, Scheme.IdealSheafData.support_comap,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    Closeds.coe_preimage, Set.mem_preimage] at hzE
  obtain ⟨hzx, hzy⟩ := hzE
  set y' := (pullback.snd sX sY).base z with hy'
  by_contra hne
  have hrx := topologicalKrullDim_closure_of_relativeDimension_eq k sX x r hx
  have hsy := topologicalKrullDim_closure_of_relativeDimension_eq k sY y s hy
  obtain ⟨t, ht⟩ : ∃ t : ℕ, topologicalKrullDim (closure ({y'} : Set Y)) = (t : WithBot ℕ∞) :=
    ⟨_, topologicalKrullDim_closure_singleton_eq k sY y'⟩
  -- `closure {y'}` is strictly smaller than `closure {y}`
  have hlt : IrreducibleCloseds.closureSingleton y' < IrreducibleCloseds.closureSingleton y := by
    refine lt_of_le_of_ne (fun a ha ↦ ?_) fun h ↦ hne ?_
    · exact closure_minimal (Set.singleton_subset_iff.2 hzy) isClosed_closure ha
    · have h' := congrArg (fun W : IrreducibleCloseds Y ↦ (W : Set Y)) h
      exact isGenericPoint_closure.eq (show IsGenericPoint y (closure ({y'} : Set Y)) from
        h'.symm)
  have hdimlt := topologicalKrullDim_lt_of_lt_irreducibleCloseds _ _
    hlt (by
      change topologicalKrullDim (closure ({y'} : Set Y)) ≠ ⊤
      rw [ht]
      exact (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top t)).ne)
  change topologicalKrullDim (closure ({y'} : Set Y)) <
    topologicalKrullDim (closure ({y} : Set Y)) at hdimlt
  rw [ht, hsy, Nat.cast_lt] at hdimlt
  -- `z` lies on `closure {x} × closure {y'}`, which is too small
  have hzE' : closure ({z} : Set (pullback sX sY : Scheme.{u})) ⊆
      ((exteriorProductIdeal sX sY x y').support : Set (pullback sX sY : Scheme.{u})) := by
    refine closure_minimal (Set.singleton_subset_iff.2 ?_)
      (exteriorProductIdeal sX sY x y').support.isClosed
    rw [exteriorProductIdeal, Scheme.IdealSheafData.support_sup]
    simp only [Closeds.coe_inf, Set.mem_inter_iff, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
      Closeds.coe_preimage, Set.mem_preimage]
    exact ⟨hzx, subset_closure rfl⟩
  have hle := (topologicalKrullDim_le_of_subset hzE').trans
    (topologicalKrullDim_support_exteriorProductIdeal_le sX sY x y' r t hrx ht.le)
  rw [topologicalKrullDim_closure_of_relativeDimension_eq k (pullback.fst sX sY ≫ sX) z (r + s)
    (by rw [hzdim]; push_cast; rfl), Nat.cast_le] at hle
  omega

/-- **The product `(closure {x} × Y) · (X × closure {y})` is `[closure {x} × closure {y}]_{r+s}`.**
For `x` of dimension `r` and `y` of dimension `s`, the Tor-formula product of Section 43.14 of
the two closed subvarieties `closure {x} × Y` and `X × closure {y}` of the nonsingular variety
`X × Y` is the cycle of their scheme-theoretic intersection `closure {x} × closure {y}`. The two
are Tor independent, so only `Tor_0` contributes. -/
theorem torFormulaSubvarietyProductTotal_fibreGenericPoints
    (hP : IsRegular (pullback sX sY : Scheme.{u})) (x : X) (y : Y) (r s : ℕ)
    (hx : relativeDimension (fieldChowSituation k).dimensionFunction sX x = r)
    (hy : relativeDimension (fieldChowSituation k).dimensionFunction sY y = s) :
    torFormulaSubvarietyProductTotal (fieldChowSituation k) (pullback.fst sX sY ≫ sX) hP
        ((r : ℤ) + (s : ℤ)) (fstFibreGenericPoint sX sY x) (sndFibreGenericPoint sX sY y) =
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (pullback.fst sX sY ≫ sX)
        (exteriorProductIdeal sX sY x y).subschemeι ((r : ℤ) + (s : ℤ))).1 := by
  set V := integralComponentAt (fstFibreGenericPoint sX sY x) with hVdef
  set W := integralComponentAt (sndFibreGenericPoint sX sY y) with hWdef
  have hV : V = (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap (pullback.fst sX sY) :=
    integralComponentAt_fstFibreGenericPoint sX sY x
  have hW : W = (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap (pullback.snd sX sY) :=
    integralComponentAt_sndFibreGenericPoint sX sY y
  have hVW : V ⊔ W = exteriorProductIdeal sX sY x y := by rw [hV, hW]; rfl
  have hdimE : topologicalKrullDim ((exteriorProductIdeal sX sY x y).support :
      Set (pullback sX sY : Scheme.{u})) ≤ ((r + s : ℕ) : WithBot ℕ∞) := by
    rw [add_comm r s]
    exact topologicalKrullDim_support_exteriorProductIdeal_le sX sY x y r s
      (topologicalKrullDim_closure_of_relativeDimension_eq k sX x r hx)
      (topologicalKrullDim_closure_of_relativeDimension_eq k sY y s hy).le
  have hcast : ((r : ℤ) + (s : ℤ)) = ((r + s : ℕ) : ℤ) := by push_cast; rfl
  have hbound : TorSupportBound (fieldChowSituation k) (pullback.fst sX sY ≫ sX) hP
      ((r : ℤ) + (s : ℤ)) (fstFibreGenericPoint sX sY x) (sndFibreGenericPoint sX sY y) := by
    rw [hcast]
    refine torSupportBound_of_topologicalKrullDim_le k _ hP (r + s) _ _ ?_
    rw [← coe_support_integralComponentAt, ← coe_support_integralComponentAt, ← hVdef, ← hWdef,
      ← Closeds.coe_inf, ← Scheme.IdealSheafData.support_sup, hVW]
    exact hdimE
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety k
    (pullback.fst sX sY ≫ sX)
  rw [torFormulaSubvarietyProductTotal_eq_of_bound _ _ _ _ hbound, ← hVW]
  refine (cycleAssociatedToClosedSubscheme_eq_intersectionProductCycle_of_tor_subsingleton
    (fieldChowSituation k) (pullback.fst sX sY ≫ sX) hP V W ((r : ℤ) + (s : ℤ)) d hd.le ?_ hbound
    ?_).symm
  · rw [hVW, hcast]
    exact schemeDeltaDimension_subschemeι_le k _ _ (r + s) hdimE
  · intro z _ hzV hzW i hi
    rw [hV] at hzV ⊢
    rw [hW] at hzW ⊢
    exact tor_subsingleton_stalk_comap_fst_comap_snd k sX sY _ _ z hzV hzW i hi

end Product

/-- The multiplicity of the exterior product at a point is the coefficient there of the cycle of
the product of the two reduced closures. -/
theorem exteriorProductWeight_eq_cycleAssociatedToClosedSubscheme (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (j : ℤ) (x : X) (y : Y) (z : (pullback f g : Scheme.{u})) :
    exteriorProductWeight C f g j x y z =
      (cycleAssociatedToClosedSubscheme C (pullback.fst f g ≫ f)
        (exteriorProductIdeal f g x y).subschemeι j).1 z :=
  rfl

/-! ### Stacks 0B0R -/

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k)) [IsVariety k sX] [IsVariety k sY]

/-- The first projection `X × Y ⟶ X` of a product of varieties is flat of relative dimension
`dim Y`. -/
theorem relativeDimension_pullbackFst (dY : ℕ) (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) :
    AlgebraicGeometry.RelativeDimension (pullback.fst sX sY) dY :=
  relativeDimension_of_flat_of_isVariety k (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl
    dY (by rw [topologicalKrullDim_pullback_of_isVariety, hdY])

/-- The second projection `X × Y ⟶ Y` of a product of varieties is flat of relative dimension
`dim X`. -/
theorem relativeDimension_pullbackSnd (dX : ℕ) (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞)) :
    AlgebraicGeometry.RelativeDimension (pullback.snd sX sY) dX :=
  relativeDimension_of_flat_of_isVariety k (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
    pullback.condition.symm dX (by rw [topologicalKrullDim_pullback_of_isVariety, hdX, add_comm])

/-- **Stacks 0B0R, part (1)**, for varieties over an algebraically closed field:
`pr_Y^*(β) = [X] × β` and `pr_X^*(α) = α × [Y]`. -/
theorem flatPullback_projections_eq_exteriorProduct (dX dY : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) (r s : ℕ)
    (α : CycleGroup (fieldChowSituation k) sX (r : ℤ))
    (β : CycleGroup (fieldChowSituation k) sY (s : ℤ)) :
    (flatPullback (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
        pullback.condition.symm dX (relativeDimension_pullbackSnd sX sY dX hdX) (s : ℤ) β).1 =
      (exteriorProduct (fieldChowSituation k) sX sY (dX : ℤ) (s : ℤ)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX (𝟙 X) (dX : ℤ)) β).1 ∧
    (flatPullback (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl dY
        (relativeDimension_pullbackFst sX sY dY hdY) (r : ℤ) α).1 =
      (exteriorProduct (fieldChowSituation k) sX sY (r : ℤ) (dY : ℤ) α
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY (𝟙 Y) (dY : ℤ))).1 :=
  ⟨flatPullbackSnd_eq_fundamentalCycle_exteriorProduct (fieldChowSituation k) sX sY dX _
      (relativeDimension_genericPoint sX dX hdX) (s : ℤ) β,
    flatPullbackFst_eq_exteriorProduct_fundamentalCycle (fieldChowSituation k) sX sY dY _
      (relativeDimension_genericPoint sY dY hdY) (r : ℤ) α⟩

/-- **Stacks 0B0R, part (2)**: `α × [Y]` and `[X] × β` intersect properly on `X × Y`. The
components are `V × Y` and `X × W` for components `V` of `α` and `W` of `β`, of dimensions
`r + dim Y` and `dim X + s`, and they meet in `V × W`, of dimension at most `r + s`. -/
theorem intersectProperly_exteriorProduct_fundamentalCycle (dX dY : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) (r s : ℕ)
    (α : CycleGroup (fieldChowSituation k) sX (r : ℤ))
    (β : CycleGroup (fieldChowSituation k) sY (s : ℤ)) :
    AlgebraicCycle.IntersectProperly
      (exteriorProduct (fieldChowSituation k) sX sY (r : ℤ) (dY : ℤ) α
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY (𝟙 Y) (dY : ℤ))).1
      (exteriorProduct (fieldChowSituation k) sX sY (dX : ℤ) (s : ℤ)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX (𝟙 X) (dX : ℤ)) β).1 := by
  intro W V hW hV
  set x := (pullback.fst sX sY).base W.isIrreducible.genericPoint with hxdef
  set y := (pullback.snd sX sY).base V.isIrreducible.genericPoint with hydef
  have hw := eq_fstFibreGenericPoint_of_exteriorProduct_fundamentalCycle_ne_zero sX sY dY r α _ hW
  have hv := eq_sndFibreGenericPoint_of_fundamentalCycle_exteriorProduct_ne_zero sX sY dX s β _ hV
  rw [← hxdef] at hw
  rw [← hydef] at hv
  have hαx : α.1 x ≠ 0 := by
    rw [← exteriorProduct_fundamentalCycle_apply_fstFibreGenericPoint sX sY dY hdY r α x, ← hw]
    exact hW
  have hβy : β.1 y ≠ 0 := by
    rw [← fundamentalCycle_exteriorProduct_apply_sndFibreGenericPoint sX sY dX hdX s β y, ← hv]
    exact hV
  have hrx : relativeDimension (fieldChowSituation k).dimensionFunction sX x = r :=
    relativeDimension_eq_of_cycle_apply_ne_zero (fieldChowSituation k) sX α hαx
  have hsy : relativeDimension (fieldChowSituation k).dimensionFunction sY y = s :=
    relativeDimension_eq_of_cycle_apply_ne_zero (fieldChowSituation k) sY β hβy
  have hWset : (W : Set (pullback sX sY : Scheme.{u})) =
      closure {fstFibreGenericPoint sX sY x} := by
    rw [CycleFlatPullback.coe_eq_closure_genericPoint W, ← hw]
  have hVset : (V : Set (pullback sX sY : Scheme.{u})) =
      closure {sndFibreGenericPoint sX sY y} := by
    rw [CycleFlatPullback.coe_eq_closure_genericPoint V, ← hv]
  have hdimW : topologicalKrullDim (W : Set (pullback sX sY : Scheme.{u})) =
      ((r + dY : ℕ) : WithBot ℕ∞) := by
    rw [hWset]
    exact topologicalKrullDim_closure_of_relativeDimension_eq k _ _ _
      (by rw [relativeDimension_fstFibreGenericPoint sX sY x r dY hrx hdY]; push_cast; rfl)
  have hdimV : topologicalKrullDim (V : Set (pullback sX sY : Scheme.{u})) =
      ((dX + s : ℕ) : WithBot ℕ∞) := by
    rw [hVset]
    exact topologicalKrullDim_closure_of_relativeDimension_eq k _ _ _
      (by rw [relativeDimension_sndFibreGenericPoint sX sY y s dX hsy hdX]; push_cast; rfl)
  have hinter : ((W : Set (pullback sX sY : Scheme.{u})) ∩ (V : Set (pullback sX sY : Scheme.{u})))
      = ((exteriorProductIdeal sX sY x y).support : Set (pullback sX sY : Scheme.{u})) := by
    rw [hWset, hVset, fstFibreGenericPoint, sndFibreGenericPoint,
      closure_singleton_subschemeι_genericPoint, closure_singleton_subschemeι_genericPoint,
      exteriorProductIdeal, Scheme.IdealSheafData.support_sup, Closeds.coe_inf]
  have hdimWV := topologicalKrullDim_support_exteriorProductIdeal_le sX sY x y r s
    (topologicalKrullDim_closure_of_relativeDimension_eq k sX x r hrx)
    (topologicalKrullDim_closure_of_relativeDimension_eq k sY y s hsy).le
  have hdimP :
      topologicalKrullDim (pullback sX sY : Scheme.{u}) = ((dX + dY : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_pullback_of_isVariety, hdX, hdY]; push_cast; rfl
  rw [AlgebraicGeometry.intersectProperly_iff, hinter, hdimW, hdimV, hdimP]
  refine (add_le_add hdimWV le_rfl).trans ?_
  rw [← Nat.cast_add, ← Nat.cast_add, Nat.cast_le]
  omega

/-- **Stacks 0B0R, part (3), first equality**: `α × β = (α × [Y]) · ([X] × β)` in
`Z_{r+s}(X × Y)`, the intersection product being the one of Section 43.17 on the nonsingular
variety `X × Y`. By linearity, `(α × [Y]) · ([X] × β) = ∑ nᵢ mⱼ (Vᵢ × Y) · (X × Wⱼ)`, and each
`(Vᵢ × Y) · (X × Wⱼ)` is `[Vᵢ × Wⱼ]`. -/
theorem exteriorProduct_eq_intersectionProduct (hX : IsRegular X) (hY : IsRegular Y) (dX dY : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) (r s : ℕ)
    (α : CycleGroup (fieldChowSituation k) sX (r : ℤ))
    (β : CycleGroup (fieldChowSituation k) sY (s : ℤ)) :
    (exteriorProduct (fieldChowSituation k) sX sY (r : ℤ) (s : ℤ) α β).1 =
      torFormulaCycleIntersectionProduct (fieldChowSituation k) (pullback.fst sX sY ≫ sX)
        (isRegular_pullback_of_isRegular sX sY hX hY) ((r : ℤ) + (s : ℤ))
        (exteriorProduct (fieldChowSituation k) sX sY (r : ℤ) (dY : ℤ) α
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY (𝟙 Y) (dY : ℤ))).1
        (exteriorProduct (fieldChowSituation k) sX sY (dX : ℤ) (s : ℤ)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX (𝟙 X) (dX : ℤ)) β).1 := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hαfin := finite_support_of_compactSpace α.1
  have hβfin := finite_support_of_compactSpace β.1
  have hP := isRegular_pullback_of_isRegular sX sY hX hY
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct_eq_sum_of_reindex _ _ _
    α.1 β.1 hαfin.toFinset hβfin.toFinset (fun x hx ↦ hαfin.mem_toFinset.2 hx)
    (fun y hy ↦ hβfin.mem_toFinset.2 hy) (fstFibreGenericPoint sX sY)
    (sndFibreGenericPoint sX sY) (fstFibreGenericPoint_injective sX sY)
    (sndFibreGenericPoint_injective sX sY)
    (exteriorProduct_fundamentalCycle_apply_fstFibreGenericPoint sX sY dY hdY r α)
    (fundamentalCycle_exteriorProduct_apply_sndFibreGenericPoint sX sY dX hdX s β)
    (fun p hp ↦ ⟨_, (eq_fstFibreGenericPoint_of_exteriorProduct_fundamentalCycle_ne_zero sX sY
      dY r α p hp).symm⟩)
    (fun q hq ↦ ⟨_, (eq_sndFibreGenericPoint_of_fundamentalCycle_exteriorProduct_ne_zero sX sY
      dX s β q hq).symm⟩)]
  have hrel : ∀ x ∈ hαfin.toFinset,
      relativeDimension (fieldChowSituation k).dimensionFunction sX x = r := fun x hx ↦
    relativeDimension_eq_of_cycle_apply_ne_zero (fieldChowSituation k) sX α
      (hαfin.mem_toFinset.1 hx)
  have hrel' : ∀ y ∈ hβfin.toFinset,
      relativeDimension (fieldChowSituation k).dimensionFunction sY y = s := fun y hy ↦
    relativeDimension_eq_of_cycle_apply_ne_zero (fieldChowSituation k) sY β
      (hβfin.mem_toFinset.1 hy)
  rw [Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun y hy ↦ by
    rw [torFormulaSubvarietyProductTotal_fibreGenericPoints sX sY hP x y r s (hrel x hx)
      (hrel' y hy)]]
  apply Function.locallyFinsuppWithin.ext
  intro z
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul,
    ← exteriorProductWeight_eq_cycleAssociatedToClosedSubscheme]
  rw [exteriorProduct_apply]
  set x₀ := (pullback.fst sX sY).base z
  set y₀ := (pullback.snd sX sY).base z
  rw [Finset.sum_eq_single x₀]
  · by_cases hα : α.1 x₀ = 0
    · simp [hα]
    have hx₀ : x₀ ∈ hαfin.toFinset := hαfin.mem_toFinset.2 hα
    rw [Finset.sum_eq_single y₀]
    · intro y hy hne
      have hw : exteriorProductWeight (fieldChowSituation k) sX sY ((r : ℤ) + (s : ℤ)) x₀ y z
          = 0 := by
        by_contra hw
        exact hne (snd_eq_of_exteriorProductWeight_ne_zero sX sY x₀ y r s (hrel x₀ hx₀)
          (hrel' y hy) z hw).symm
      rw [hw, mul_zero]
    · intro hy₀
      have : β.1 y₀ = 0 := by simpa using hy₀
      simp [this]
  · intro x _ hne
    refine Finset.sum_eq_zero fun y _ ↦ ?_
    rw [exteriorProductWeight_eq_zero_of_ne (fieldChowSituation k) sX sY _ x y z
      (Ne.symm hne), mul_zero]
  · intro hx₀
    have : α.1 x₀ = 0 := by simpa using hx₀
    simp [this]

/-- **Stacks Project, Tag 0B0R.** Let `X` and `Y` be nonsingular varieties over an algebraically
closed field `k`, let `α ∈ Z_r(X)` and `β ∈ Z_s(Y)`. Then

1. `pr_Y^*(β) = [X] × β` and `pr_X^*(α) = α × [Y]`,
2. `α × [Y]` and `[X] × β` intersect properly on `X × Y`, and
3. `α × β = (α × [Y]) · ([X] × β) = pr_X^*(α) · pr_Y^*(β)` in `Z_{r+s}(X × Y)`.

A variety is `AlgebraicGeometry.IsVariety` over `Spec k` and nonsingular is
`AlgebraicGeometry.IsRegular`, as in Section 43.3; `dX`, `dY` are the dimensions of `X` and `Y`.
The product `X × Y` is `pullback sX sY` with structure morphism `pullback.fst sX sY ≫ sX`, and
`pr_X = pullback.fst sX sY`, `pr_Y = pullback.snd sX sY`; `pr_X^*` and `pr_Y^*` are the flat
pullbacks of cycles of Tag 02RB along these flat morphisms of relative dimension `dY` and `dX`.
`[X]` and `[Y]` are the fundamental cycles, `×` is the exterior product of Section 43.16, and
`·` is the intersection product of Section 43.17 on the nonsingular variety `X × Y`. The cycle
groups `Z_{dX+s}`, `Z_{s+dX}` (and their analogues) are distinct types carrying the same cycles,
so the identities are equalities of the underlying algebraic cycles. -/
@[stacks 0B0R]
theorem exteriorProduct_projections (hX : IsRegular X) (hY : IsRegular Y) (dX dY : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) (r s : ℕ)
    (α : CycleGroup (fieldChowSituation k) sX (r : ℤ))
    (β : CycleGroup (fieldChowSituation k) sY (s : ℤ)) :
    -- (1)
    ((flatPullback (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
        pullback.condition.symm dX (relativeDimension_pullbackSnd sX sY dX hdX) (s : ℤ) β).1 =
      (exteriorProduct (fieldChowSituation k) sX sY (dX : ℤ) (s : ℤ)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX (𝟙 X) (dX : ℤ)) β).1 ∧
    (flatPullback (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY) rfl dY
        (relativeDimension_pullbackFst sX sY dY hdY) (r : ℤ) α).1 =
      (exteriorProduct (fieldChowSituation k) sX sY (r : ℤ) (dY : ℤ) α
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY (𝟙 Y) (dY : ℤ))).1) ∧
    -- (2)
    AlgebraicCycle.IntersectProperly
      (exteriorProduct (fieldChowSituation k) sX sY (r : ℤ) (dY : ℤ) α
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY (𝟙 Y) (dY : ℤ))).1
      (exteriorProduct (fieldChowSituation k) sX sY (dX : ℤ) (s : ℤ)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX (𝟙 X) (dX : ℤ)) β).1 ∧
    -- (3)
    ((exteriorProduct (fieldChowSituation k) sX sY (r : ℤ) (s : ℤ) α β).1 =
      torFormulaCycleIntersectionProduct (fieldChowSituation k) (pullback.fst sX sY ≫ sX)
        (isRegular_pullback_of_isRegular sX sY hX hY) ((r : ℤ) + (s : ℤ))
        (exteriorProduct (fieldChowSituation k) sX sY (r : ℤ) (dY : ℤ) α
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY (𝟙 Y) (dY : ℤ))).1
        (exteriorProduct (fieldChowSituation k) sX sY (dX : ℤ) (s : ℤ)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX (𝟙 X) (dX : ℤ)) β).1 ∧
    (exteriorProduct (fieldChowSituation k) sX sY (r : ℤ) (s : ℤ) α β).1 =
      torFormulaCycleIntersectionProduct (fieldChowSituation k) (pullback.fst sX sY ≫ sX)
        (isRegular_pullback_of_isRegular sX sY hX hY) ((r : ℤ) + (s : ℤ))
        (flatPullback (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sX (pullback.fst sX sY)
          rfl dY (relativeDimension_pullbackFst sX sY dY hdY) (r : ℤ) α).1
        (flatPullback (fieldChowSituation k) (pullback.fst sX sY ≫ sX) sY (pullback.snd sX sY)
          pullback.condition.symm dX (relativeDimension_pullbackSnd sX sY dX hdX) (s : ℤ) β).1)
    := by
  obtain ⟨h1β, h1α⟩ := flatPullback_projections_eq_exteriorProduct sX sY dX dY hdX hdY r s α β
  have h3 := exteriorProduct_eq_intersectionProduct sX sY hX hY dX dY hdX hdY r s α β
  refine ⟨⟨h1β, h1α⟩,
    intersectProperly_exteriorProduct_fundamentalCycle sX sY dX dY hdX hdY r s α β, h3, ?_⟩
  rw [h1α, h1β]
  exact h3

end Main

end Stacks.Intersection.ExteriorProductProjections

end
