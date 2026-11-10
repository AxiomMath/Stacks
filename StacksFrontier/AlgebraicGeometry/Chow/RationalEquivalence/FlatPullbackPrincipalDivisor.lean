module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrimeDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback of a principal divisor

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
schemes locally of finite type over `S` with `Y` integral of delta-dimension `k`, and let
`f : X ⟶ Y` be flat of constant relative dimension `r`. For a nonzero rational function `g` on
`Y` the flat pullback of the principal divisor of `g` is

  `f^* div_Y(g) = ∑_j n_j i_{j,*} div_{X_j}(g ∘ f|_{X_j})`

as `(k + r - 1)`-cycles on `X`, where the sum runs over the irreducible components `X_j` of `X`
taken with their reduced structure, `i_j : X_j ⟶ X` is the inclusion and `n_j` is the
multiplicity of `X_j` in `X`.

## Main results

* `Stacks.Chow.flatPullback_principalDivisor_eq_sum_components` — **Stacks 0EPH**: the
  componentwise formula, read coefficientwise at each point of `X`.
* `Stacks.Chow.flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal` — the flat pullback
  multiplicity at a point is the colength of the extended maximal ideal of the point below it.
* `Stacks.Chow.coheight_eq_one_of_relativeDimension_eq_sub_one` — on a scheme whose components
  all have relative dimension `n` at their generic points, relative dimension `n - 1` means
  codimension one.
* `Stacks.Chow.ord_div_algebraMap_eq_length_sub` — the order of vanishing of a quotient of two
  elements of a local ring of codimension one is the difference of their colengths.

## Implementation notes

The formula is stated coefficientwise, because the irreducible components of a locally
Noetherian scheme need not form a finite set, so neither side is a finite sum of cycles; at a
fixed point of `X` only finitely many components contribute and the right hand side is a locally
finite sum.

A reduced irreducible component is written `Stacks.Chow.integralComponentAt` of its generic
point, which is the repository's name for the reduced induced structure on the closure of a
point; `Stacks.Chow.integralComponentAt_genericPoint_eq_vanishingIdeal` identifies it with the
vanishing ideal sheaf of the component as a closed subset. That each such component is integral,
dominates `Y` and has delta-dimension `k + r` are consequences of flatness rather than extra
hypotheses, and they appear in the statement as the named lemmas
`Stacks.Chow.isIntegral_integralComponentAt`,
`Stacks.Chow.isDominant_subschemeι_integralComponentAt_comp` and
`Stacks.Chow.schemeDeltaDimension_integralComponentAt_comp` rather than as assumptions.

The proof follows the source and splits into three cases at a point `x` of `X`. Away from
relative dimension `k + r - 1` both sides vanish, because both are `(k + r - 1)`-cycles. If `x`
lies over the generic point of `Y` both sides vanish again, since `g` is a unit in the local
ring there. Otherwise write `A = 𝒪_{Y, f x}` and `B = 𝒪_{X, x}`; then `A → B` is a flat local
homomorphism of Noetherian local rings, `A` is a one-dimensional domain, `B` is
one-dimensional, and writing `g = a / b` the identity to be proved becomes

  `length_A(A/aA) · length_B(B/m_A B) = ∑_i length_{B/q_i}(B/(a, q_i)) · length_{B_{q_i}}(B_{q_i})`

summed over the minimal primes `q_i` of `B`, and similarly for `b`. The left hand side is the
flat pullback coefficient, by the length formula of Stacks 02QG applied to the flat base change
`length_B(B/aB) = length_A(A/aA) · length_B(B/m_A B)`; the right hand side is the sum over the
components of `X` through `x`, which correspond one-to-one with the minimal primes of `B`.

## References

* [Stacks Project, Tag 0EPH](https://stacks.math.columbia.edu/tag/0EPH)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02QT](https://stacks.math.columbia.edu/tag/02QT)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order TopologicalSpace

universe u

namespace AlgebraicGeometry.IdealSheafData

/-! ### Stalks of ideal sheaves -/

/-- The kernel of the stalk map of the closed immersion of the subscheme cut out by an ideal
sheaf is the stalk of that ideal sheaf. -/
theorem ker_stalkMap_subschemeι_eq_stalk {X : Scheme.{u}} (I : X.IdealSheafData)
    (ξ : I.subscheme) :
    RingHom.ker (I.subschemeι.stalkMap ξ).hom = stalk I (I.subschemeι.base ξ) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hξU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (I.subschemeι.base ξ)) isOpen_univ
  rw [← stalk_ker_eq_of_affine_target I.subschemeι ξ U hU hξU, I.ker_subschemeι]

end AlgebraicGeometry.IdealSheafData

namespace Stacks.Chow

/-- The generic point of an irreducible component is a generic point of that component. -/
private theorem isGenericPoint_genericPoint_component {T : Type*} [TopologicalSpace T]
    [QuasiSober T] (W : irreducibleComponents T) : IsGenericPoint W.2.1.genericPoint (W : Set T) :=
  W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents (W : Set T) W.2)

/-! ### The reduced irreducible components of a scheme -/

/-- The reduced induced structure on an irreducible component of `X` is the integral closed
subscheme attached to the generic point of that component. -/
theorem integralComponentAt_genericPoint_eq_vanishingIdeal {X : Scheme.{u}}
    (W : irreducibleComponents X) :
    integralComponentAt W.2.1.genericPoint =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨(W : Set X), isClosed_of_mem_irreducibleComponents (W : Set X) W.2⟩ := by
  unfold integralComponentAt
  congr 1
  exact Closeds.ext (isGenericPoint_genericPoint_component W)

/-- The reduced induced structure on an irreducible component of `X` has that component as the
range of its closed immersion into `X`. -/
theorem range_subschemeι_integralComponentAt_genericPoint {X : Scheme.{u}}
    (W : irreducibleComponents X) :
    Set.range (integralComponentAt W.2.1.genericPoint).subschemeι.base = (W : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
  exact isGenericPoint_genericPoint_component W

/-- **Stacks 02R8.** Along a flat morphism to an integral scheme every reduced irreducible
component of the source dominates the target: the image of an irreducible component of the
source of a flat morphism is dense. -/
theorem isDominant_subschemeι_integralComponentAt_comp {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) [Flat f] (W : irreducibleComponents X) :
    IsDominant ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f) := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  have hrange :
      Set.range ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f).base =
        f.base '' (W : Set X) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      range_subschemeι_integralComponentAt_genericPoint]
  rw [hrange]
  exact dense_image_irreducibleComponent f W

/-- Along a flat morphism of relative dimension `r` to an integral scheme of delta-dimension
`k`, the generic point of an irreducible component of the source has relative dimension
`k + r`: it maps to the generic point of the target, where the delta-dimension is `k`, and the
residue-field extension there has transcendence degree `r`. -/
theorem relativeDimension_genericPoint_irreducibleComponent (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) {k : ℤ}
    (hY : schemeDeltaDimension C sY = (k : EInt)) (W : irreducibleComponents X) :
    relativeDimension C.dimensionFunction sX W.2.1.genericPoint = k + (r : ℤ) := by
  have hgen : relativeDimension C.dimensionFunction sY (genericPoint Y) = k := by
    have h := schemeDeltaDimension_eq_genericPoint C sY
    rw [hY] at h
    exact (WithBotTop.coe_injective h).symm
  have hstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY f
    W.2.1.genericPoint
  rw [toNat_residueTrdeg_genericPoint f W r hf,
    map_genericPoint_irreducibleComponent_eq_genericPoint f W, hgen] at hstep
  rw [← hbase]
  exact hstep

/-- Along a flat morphism of relative dimension `r` to an integral scheme of delta-dimension
`k`, every reduced irreducible component of the source has delta-dimension `k + r`. -/
theorem schemeDeltaDimension_integralComponentAt_comp (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) {k : ℤ}
    (hY : schemeDeltaDimension C sY = (k : EInt)) (W : irreducibleComponents X) :
    schemeDeltaDimension C ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX) =
      ((k + (r : ℤ) : ℤ) : EInt) := by
  rw [schemeDeltaDimension_subschemeι_comp C sX _ (isIntegral_integralComponentAt _),
    genericPointOf_integralComponentAt,
    relativeDimension_genericPoint_irreducibleComponent C sX sY f hbase r hf hY W]

/-! ### Points of codimension one -/

/-- A point strictly below a maximal point has coheight at least one. -/
private theorem one_le_coheight_of_lt_of_isMax {α : Type*} [Preorder α] {a b : α} (hlt : a < b)
    (hb : IsMax b) : 1 ≤ coheight a := by
  simpa [hb.coheight_eq_zero] using coheight_add_one_le hlt

/-- The generic point of an integral scheme is a maximal point. -/
private theorem isMax_genericPoint_of_isIntegral {T : Scheme.{u}} [IsIntegral T] :
    IsMax (genericPoint T) := fun w _ ↦ genericPoint_specializes w

/-- If `y` is a nontrivial generalization of `x` in a scheme, then `x < y`. -/
private theorem lt_of_specializes_of_ne {T : Scheme.{u}} {x y : T} (h : y ⤳ x) (hne : y ≠ x) :
    x < y :=
  lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr h,
    fun hback ↦ hne (Specializes.antisymm h (Scheme.le_iff_specializes.mp hback)).eq⟩

/-- A point of an integral scheme other than the generic point has coheight at least one. -/
private theorem one_le_coheight_of_ne_genericPoint {T : Scheme.{u}} [IsIntegral T] {z : T}
    (hz : z ≠ genericPoint T) : 1 ≤ coheight z :=
  one_le_coheight_of_lt_of_isMax
    (lt_of_specializes_of_ne (genericPoint_specializes z) hz.symm) isMax_genericPoint_of_isIntegral

/-- Every point of a topological space lies on an irreducible component: the closure of the
point is irreducible, hence contained in a component. -/
theorem exists_mem_irreducibleComponents {T : Type*} [TopologicalSpace T] (z : T) :
    ∃ W : irreducibleComponents T, z ∈ (W : Set T) := by
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({z} : Set T)) (isIrreducible_iff_closure.mpr isIrreducible_singleton)
  exact ⟨⟨W, hW⟩, hsub (subset_closure rfl)⟩

/-- If every irreducible component of `X` has relative dimension `n` at its generic point, then
no point of `X` has relative dimension exceeding `n`: a point is a specialization of the generic
point of a component containing it, and relative dimension drops strictly along a nontrivial
specialization. -/
theorem relativeDimension_le_of_forall_genericPoint (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {n : ℤ}
    (hgen : ∀ W : irreducibleComponents X,
      relativeDimension C.dimensionFunction sX W.2.1.genericPoint = n)
    (z : X) : relativeDimension C.dimensionFunction sX z ≤ n := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
    C.dimensionFunction sX
  rw [← hd z]
  obtain ⟨W, hzW⟩ := exists_mem_irreducibleComponents z
  have hηdim : d W.2.1.genericPoint = n := by rw [hd, hgen W]
  by_cases heq : W.2.1.genericPoint = z
  · rw [← heq]
    exact hηdim.le
  · have hlt := d.strictAnti_specializes
      ((isGenericPoint_genericPoint_component W).specializes hzW) heq
    omega

/-- On a scheme all of whose irreducible components have relative dimension `n` at their generic
points, a nontrivial generalization of a point of relative dimension `n - 1` is a maximal point:
it already has relative dimension `n`, which is the largest value available, so it admits no
further nontrivial generalization. -/
theorem isMax_of_specializes_of_relativeDimension_eq_sub_one (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {n : ℤ}
    (hgen : ∀ W : irreducibleComponents X,
      relativeDimension C.dimensionFunction sX W.2.1.genericPoint = n)
    {x : X} (hx : relativeDimension C.dimensionFunction sX x = n - 1)
    {z : X} (hzx : z ⤳ x) (hne : z ≠ x) : IsMax z := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
    C.dimensionFunction sX
  have hle : ∀ w : X, d w ≤ n := fun w ↦ by
    rw [hd w]
    exact relativeDimension_le_of_forall_genericPoint C sX hgen w
  have hdz : d z = n := by
    have hlt := d.strictAnti_specializes hzx hne
    have hdx : d x = n - 1 := by rw [hd x, hx]
    have := hle z
    omega
  intro w hwz
  by_contra hwne
  have hne' : w ≠ z := fun heq ↦ hwne (heq ▸ le_rfl)
  have hlt := d.strictAnti_specializes hwz hne'
  have := hle w
  omega

/-- On a scheme all of whose irreducible components have relative dimension `n` at their generic
points, a point of relative dimension `n - 1` has codimension one: it is a nontrivial
specialization of the generic point of a component, which gives codimension at least one, and
every nontrivial generalization of it is maximal, which gives codimension at most one. -/
theorem coheight_eq_one_of_relativeDimension_eq_sub_one (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {n : ℤ}
    (hgen : ∀ W : irreducibleComponents X,
      relativeDimension C.dimensionFunction sX W.2.1.genericPoint = n)
    {x : X} (hx : relativeDimension C.dimensionFunction sX x = n - 1) : coheight x = 1 := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
    C.dimensionFunction sX
  have hdx : d x = n - 1 := by rw [hd x, hx]
  refine le_antisymm (coheight_le_coe_iff.mpr fun z hxz ↦ ?_) ?_
  · have hzx : z ⤳ x := Scheme.le_iff_specializes.mp hxz.le
    have hne : z ≠ x := fun heq ↦ lt_irrefl x (heq ▸ hxz)
    rw [IsMax.coheight_eq_zero
      (isMax_of_specializes_of_relativeDimension_eq_sub_one C sX hgen hx hzx hne)]
    norm_num
  · obtain ⟨W, hxW⟩ := exists_mem_irreducibleComponents x
    have hηx : W.2.1.genericPoint ⤳ x := (isGenericPoint_genericPoint_component W).specializes hxW
    have hηdim : d W.2.1.genericPoint = n := by rw [hd, hgen W]
    have hne : W.2.1.genericPoint ≠ x := fun heq ↦ by rw [heq, hdx] at hηdim; omega
    exact one_le_coheight_of_lt_of_isMax
      (lt_of_specializes_of_ne hηx hne)
      (isMax_of_specializes_of_relativeDimension_eq_sub_one C sX hgen hx hηx hne)

/-- Along a flat morphism to an integral scheme, a point whose nontrivial generalizations are
all maximal and which does not lie over the generic point of the target has image of codimension
one: a generalization of its image lifts to a generalization of the point, which is then the
generic point of an irreducible component and so lies over the generic point of the target. -/
@[ega "IV 21.10.7" "special case"]
theorem coheight_map_eq_one_of_flat {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) [Flat f]
    {x : X} (hxmax : ∀ z : X, z ⤳ x → z ≠ x → IsMax z)
    (hy : f.base x ≠ genericPoint Y) : coheight (f.base x) = 1 := by
  refine le_antisymm (coheight_le_coe_iff.mpr fun y' hylt ↦ ?_) ?_
  · obtain ⟨x', hx'x, hfx'⟩ := Flat.generalizingMap f (Scheme.le_iff_specializes.mp hylt.le)
    have hx'ne : x' ≠ x := fun heq ↦ ne_of_lt hylt (heq ▸ hfx')
    obtain ⟨W, hx'W⟩ := exists_mem_irreducibleComponents x'
    have hηx' : W.2.1.genericPoint ⤳ x' :=
      (isGenericPoint_genericPoint_component W).specializes hx'W
    have heq : W.2.1.genericPoint = x' :=
      (Specializes.antisymm hηx'
        (Scheme.le_iff_specializes.mp
          (hxmax x' hx'x hx'ne (Scheme.le_iff_specializes.mpr hηx')))).eq
    have hy' : y' = genericPoint Y := by
      rw [← hfx', ← heq, map_genericPoint_irreducibleComponent_eq_genericPoint f W]
    rw [hy', IsMax.coheight_eq_zero isMax_genericPoint_of_isIntegral]
    norm_num
  · exact one_le_coheight_of_ne_genericPoint hy

/-! ### Relative dimension along a morphism of bounded relative dimension -/

/-- Relative dimension does not increase along a specialization: a dimension function is
strictly antitone for specialization. -/
theorem relativeDimension_le_of_specializes (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {y z : X} (h : y ⤳ z) :
    relativeDimension C.dimensionFunction sX z ≤
      relativeDimension C.dimensionFunction sX y := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
    C.dimensionFunction sX
  rw [← hd, ← hd]
  by_cases heq : y = z
  · rw [heq]
  · exact (d.strictAnti_specializes h heq).le

/-- For a morphism of relative dimension `r` the residue-field extension has transcendence
degree at most `r` at every point: by Stacks 02FX the dimension of the fibre at the point is
the dimension of the local ring of the fibre plus that transcendence degree, and the fibre is
equidimensional of dimension `r`. -/
theorem toNat_residueTrdeg_le_of_relativeDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) (x : X) :
    Cardinal.toNat (residueTrdeg f x) ≤ r := by
  have hq : LocallyOfFiniteType (f.fiberToSpecResidueField (f.base x)) := by
    change LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField (f.base x)))
    infer_instance
  have hfibre := hf (f.base x) ⟨f.asFiber x⟩
  have hAt := @topologicalKrullDimAt_eq_of_equidimensional _ _ (f.fiber (f.base x))
    (f.fiberToSpecResidueField (f.base x)) hq r hfibre.1 hfibre.2 (f.asFiber x)
  have hfx := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f x
  change topologicalKrullDimAt (f.fiber (f.base x)) (f.asFiber x) =
    ringKrullDim ((f.fiber (f.base x)).presheaf.stalk (f.asFiber x)) +
      (Cardinal.toENat (residueTrdeg f x) : WithBot ℕ∞) at hfx
  rw [hAt] at hfx
  have hcoe : (Cardinal.toENat (residueTrdeg f x) : WithBot ℕ∞) ≤ (r : WithBot ℕ∞) := by
    rw [hfx]
    exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial
  have henat : Cardinal.toENat (residueTrdeg f x) ≤ (r : ℕ∞) := by exact_mod_cast hcoe
  simpa [Cardinal.toNat_toENat] using ENat.toNat_le_toNat henat (by simp)

/-- A closed subscheme all of whose points have relative dimension at most `k` has
delta-dimension at most `k`: the delta-dimension is the supremum over the irreducible
components of the relative dimension of their generic points. -/
theorem schemeDeltaDimension_le_of_forall_point (C : ChowSituation.{u}) {X Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] {k : ℤ}
    (h : ∀ z : Z, relativeDimension C.dimensionFunction sX (i.base z) ≤ k) :
    schemeDeltaDimension C (i ≫ sX) ≤ (k : EInt) := by
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le fun W ↦ ?_
  rw [deltaDimension_eq_of_isGenericPoint C (i ≫ sX)
      ⟨(W : Set Z), W.2.1, isClosed_of_mem_irreducibleComponents (W : Set Z) W.2⟩
      W.2.1.genericPoint
      (isGenericPoint_genericPoint_component W),
    relativeDimension_comp_closedImmersion]
  exact WithBotTop.coe_le_coe.mpr (h W.2.1.genericPoint)

/-- **Stacks 02QT.** A point whose relative dimension is that of its image plus the relative
dimension of the morphism is the image of a generic point of an irreducible component of the
scheme-theoretic inverse image of the reduced closure of that image: no point of that inverse
image has larger relative dimension, since relative dimension does not grow along a
specialization in the target and the residue transcendence degree is at most `r`. -/
theorem exists_genericPoints_comap_integralComponentAt (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hbase : f ≫ sY = sX) (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (x : X)
    (hdim : relativeDimension C.dimensionFunction sX x =
      relativeDimension C.dimensionFunction sY (f.base x) + (r : ℤ)) :
    ∃ ξ : genericPoints ((integralComponentAt (f.base x)).comap f).subscheme,
      ((integralComponentAt (f.base x)).comap f).subschemeι.base ξ.1 = x := by
  have hsupp : (((integralComponentAt (f.base x)).comap f).support : Set X) =
      f.base ⁻¹' ((integralComponentAt (f.base x)).support : Set Y) := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hclosure : ((integralComponentAt (f.base x)).support : Set Y) = closure {f.base x} :=
    coe_support_integralComponentAt _
  have hxmem : x ∈ (((integralComponentAt (f.base x)).comap f).support : Set X) := by
    rw [hsupp, hclosure]
    exact subset_closure rfl
  obtain ⟨ξ₀, hξ₀⟩ : ∃ z : ((integralComponentAt (f.base x)).comap f).subscheme,
      ((integralComponentAt (f.base x)).comap f).subschemeι.base z = x := by
    rwa [← Scheme.IdealSheafData.range_subschemeι] at hxmem
  have hbound : ∀ z : ((integralComponentAt (f.base x)).comap f).subscheme,
      relativeDimension C.dimensionFunction sX
          (((integralComponentAt (f.base x)).comap f).subschemeι.base z) ≤
        relativeDimension C.dimensionFunction sY (f.base x) + (r : ℤ) := by
    intro z
    have hmem : f.base (((integralComponentAt (f.base x)).comap f).subschemeι.base z) ∈
        closure ({f.base x} : Set Y) := by
      rw [← hclosure, ← Set.mem_preimage, ← hsupp,
        ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    have hstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY f
      (((integralComponentAt (f.base x)).comap f).subschemeι.base z)
    rw [hbase] at hstep
    rw [hstep]
    have hbase' := relativeDimension_le_of_specializes C sY
      (specializes_iff_mem_closure.mpr hmem)
    have htr := toNat_residueTrdeg_le_of_relativeDimension f r hf
      (((integralComponentAt (f.base x)).comap f).subschemeι.base z)
    omega
  obtain ⟨W, hW⟩ := isGenericPoint_component_of_relativeDimension_eq C sX
    ((integralComponentAt (f.base x)).comap f).subschemeι
    (schemeDeltaDimension_le_of_forall_point C sX
      ((integralComponentAt (f.base x)).comap f).subschemeι hbound) ξ₀
    (by rw [hξ₀]; exact hdim)
  refine ⟨⟨ξ₀, ?_⟩, hξ₀⟩
  simp only [genericPoints, Set.mem_ofPred_eq, hW.def]
  exact W.2

/-! ### The flat pullback multiplicity as a length -/

/-- On an affine open the ideal of the reduced induced structure on the closure of a point is
the prime of that point. -/
theorem ideal_integralComponentAt {X : Scheme.{u}} (x : X) (U : X.affineOpens)
    (hx : x ∈ (U : X.Opens)) :
    (integralComponentAt x).ideal U = (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hU : IsAffineOpen (U : X.Opens) := U.2
  have _ : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hsingle : hU.fromSpec.base ⁻¹' ({x} : Set X) = {hU.primeIdealOf ⟨x, hx⟩} := by
    ext z
    exact ⟨fun hz ↦ hU.fromSpec.isOpenEmbedding.injective
        (by rw [hU.fromSpec_primeIdealOf]; exact hz),
      by rintro rfl; exact hU.fromSpec_primeIdealOf ⟨x, hx⟩⟩
  have hcl : hU.fromSpec.base ⁻¹' closure ({x} : Set X) =
      closure {hU.primeIdealOf ⟨x, hx⟩} := by
    rw [hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hU.fromSpec.continuous, hsingle]
    rfl
  rw [integralComponentAt, Scheme.IdealSheafData.vanishingIdeal_ideal]
  refine (congrArg PrimeSpectrum.vanishingIdeal hcl).trans ?_
  rw [PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]

/-- The stalk at `x` of the reduced induced structure on the closure of `x` is the maximal
ideal of the local ring at `x`: on an affine open the ideal is the prime of `x`, and the local
ring is the localization there. -/
theorem idealSheafStalk_integralComponentAt_self {X : Scheme.{u}} (x : X) :
    IdealSheafData.stalk (integralComponentAt x) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU,
    ideal_integralComponentAt x ⟨U, hU⟩ hxU]
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((⟨U, hU⟩ : X.affineOpens).2.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal _ (X.presheaf.stalk x)

/-- The multiplicity of an irreducible component of the scheme-theoretic inverse image of a
closed subscheme is the length of the quotient of the local ring upstairs by the extension of
the stalk of the ideal sheaf downstairs. -/
theorem componentMultiplicity_comap_eq_length_quotient {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (ξ : genericPoints (I.comap f).subscheme) :
    componentMultiplicity (I.comap f).subschemeι ξ =
      ((Module.length (X.presheaf.stalk ((I.comap f).subschemeι.base ξ.1))
        (X.presheaf.stalk ((I.comap f).subschemeι.base ξ.1) ⧸
          Ideal.map (f.stalkMap ((I.comap f).subschemeι.base ξ.1)).hom
            (IdealSheafData.stalk I
              (f.base ((I.comap f).subschemeι.base ξ.1))))).toNat : ℤ) := by
  rw [componentMultiplicity_eq_length_quotient_ker,
    IdealSheafData.ker_stalkMap_subschemeι_eq_stalk, IdealSheafData.stalk_comap]

/-- **Stacks 02RB.** At a point `x` of relative dimension `j` which is the image of a generic
point of the scheme-theoretic inverse image of the reduced closure of `f x`, the flat pullback
multiplicity is the length of `𝒪_{X, x}` modulo the ideal generated by the maximal ideal of
`𝒪_{Y, f x}`. -/
theorem flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X ⟶ Y) (j : ℤ) (x : X)
    (hex : ∃ ξ : genericPoints ((integralComponentAt (f.base x)).comap f).subscheme,
      ((integralComponentAt (f.base x)).comap f).subschemeι.base ξ.1 = x)
    (hdim : relativeDimension C.dimensionFunction sX x = j) :
    flatPullbackWeight C sX f j x =
      ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
        Ideal.map (f.stalkMap x).hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))))).toNat : ℤ) := by
  classical
  have hExists : ∃ ξ : genericPoints ((integralComponentAt (f.base x)).comap f).subscheme,
      ((integralComponentAt (f.base x)).comap f).subschemeι.base ξ.1 = x ∧
        relativeDimension C.dimensionFunction sX x = j :=
    ⟨hex.choose, hex.choose_spec, hdim⟩
  have hfold : flatPullbackWeight C sX f j x =
      closedSubschemeCycleCoeff C sX
        ((integralComponentAt (f.base x)).comap f).subschemeι j x := rfl
  rw [hfold, closedSubschemeCycleCoeff, dite_eq_left hExists,
    componentMultiplicity_comap_eq_length_quotient f (integralComponentAt (f.base x)),
    (Classical.choose_spec hExists).1, idealSheafStalk_integralComponentAt_self]

end Stacks.Chow

namespace AlgebraicGeometry

/-! ### Colengths under a flat local homomorphism -/

/-- For a flat local homomorphism `A → B` of local rings, the colength of a principal ideal
generated by an element of `A` is the colength of that element in `A` times the colength of the
extended maximal ideal: the quotient `B ⧸ aB` is the base change of `A ⧸ aA`. -/
theorem length_quotient_span_algebraMap {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Flat A B] (a : A) :
    Module.length B (B ⧸ Ideal.span {algebraMap A B a}) =
      Module.length A (A ⧸ Ideal.span {a}) *
        Module.length B (B ⧸ extendedMaximalIdeal A B) := by
  have hmap : Ideal.map (algebraMap A B) (Ideal.span {a}) =
      Ideal.span {algebraMap A B a} := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [← hmap, (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (Ideal.span {a})).toLinearEquiv.length_eq]
  exact (length_baseChange_eq_length_mul_length_quotient A B (A ⧸ Ideal.span {a})).symm

/-- **Stacks 02QG, in the flat form.** For a flat local homomorphism `A → B` of Noetherian local
rings with `B` one-dimensional, and a nonzerodivisor coming from `A`, the colength of that
element in `A` times the colength of the extended maximal ideal is the sum over the minimal
primes `p` of `B` of the length of `B_p` times the colength of `(a, p)`. -/
theorem length_quotient_extendedMaximalIdeal_mul_eq_finsum_minimalPrimes
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B] [IsNoetherianRing B]
    (hdim : ringKrullDim B = 1) (a : A) (hreg : IsSMulRegular B (algebraMap A B a)) :
    ((Module.length A (A ⧸ Ideal.span {a})).toNat : ℤ) *
        ((Module.length B (B ⧸ extendedMaximalIdeal A B)).toNat : ℤ) =
      ∑ᶠ p : {p : PrimeSpectrum B // p.asIdeal ∈ minimalPrimes B},
        ((Module.length (Localization.AtPrime p.1.asIdeal)
            (Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
          ((Module.length B (B ⧸ (Ideal.span {algebraMap A B a} ⊔ p.1.asIdeal))).toNat : ℤ) := by
  let _ : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr (by rw [hdim]; norm_num)
  have hnonzero : algebraMap A B a ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_right]
    intro other hzero
    exact hreg (by simpa [smul_eq_mul, mul_comm] using hzero)
  have hfinite : Module.length B (B ⧸ Ideal.span {algebraMap A B a}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton B hnonzero)
  rw [← natCast_length_quotient_span_eq_sum_minimalPrimes (algebraMap A B a) hreg hdim hfinite,
    length_quotient_span_algebraMap a, ENat.toNat_mul, Nat.cast_mul]

/-- The colength of a principal ideal together with the kernel of a surjection is the colength
of the image of the generator downstairs: the preimage of the ideal generated by the image is
the ideal generated by the element together with the kernel. -/
theorem length_quotient_span_sup_ker {B C : Type*} [CommRing B] [CommRing C] (ψ : B →+* C)
    (hψ : Function.Surjective ψ) (a : B) :
    Module.length B (B ⧸ (Ideal.span {a} ⊔ RingHom.ker ψ)) =
      Module.length C (C ⧸ Ideal.span {ψ a}) := by
  let J : Ideal C := Ideal.span {ψ a}
  let φ : B →+* C ⧸ J := (Ideal.Quotient.mk J).comp ψ
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective.comp hψ
  have hkerφ : RingHom.ker φ = Ideal.span {a} ⊔ RingHom.ker ψ := by
    rw [← RingHom.comap_ker, Ideal.mk_ker,
      show (J : Ideal C) = Ideal.map ψ (Ideal.span {a}) by
        rw [Ideal.map_span, Set.image_singleton],
      Ideal.comap_map_of_surjective ψ hψ, ← RingHom.ker_eq_comap_bot]
  let _ : Algebra B C := ψ.toAlgebra
  let _ : Algebra B (C ⧸ J) := φ.toAlgebra
  let _ : IsScalarTower B C (C ⧸ J) := IsScalarTower.of_algebraMap_eq' rfl
  have hone : Module.length B (B ⧸ RingHom.ker φ) = Module.length B (C ⧸ J) :=
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId B (C ⧸ J)) hφ).toLinearEquiv.length_eq
  rw [← hkerφ, hone]
  exact Module.length_eq_of_surjective (M := C ⧸ J) hψ

/-- A nonzero element of the local ring at the generic point of an integral scheme is a unit:
that local ring is the function field. -/
theorem isUnit_of_ne_zero_of_eq_genericPoint {Y : Scheme.{u}} [IsIntegral Y] {y : Y}
    (hy : y = genericPoint Y) {a : Y.presheaf.stalk y} (ha : a ≠ 0) : IsUnit a := by
  subst hy
  exact isUnit_iff_ne_zero.mpr ha

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### Orders of vanishing as colength differences -/

/-- The order of vanishing of a quotient of two elements of the local ring at a point of
codimension one is the difference of their colengths there. -/
theorem ord_div_algebraMap_eq_length_sub {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {x : X} (hx : coheight x = 1) {a b : X.presheaf.stalk x} (ha : a ≠ 0) (hb : b ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a /
        algebraMap (X.presheaf.stalk x) X.functionField b) x =
      ((Module.length (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸ Ideal.span {b})).toNat : ℤ) := by
  let _ : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hinj := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have hne (v : X.presheaf.stalk x) (hv : v ≠ 0) :
      algebraMap (X.presheaf.stalk x) X.functionField v ≠ 0 :=
    fun h ↦ hv (hinj (by simpa using h))
  have hA := hne a ha
  have hB := hne b hb
  have hq : algebraMap (X.presheaf.stalk x) X.functionField a /
      algebraMap (X.presheaf.stalk x) X.functionField b ≠ 0 := div_ne_zero hA hB
  rw [ord_eq_ordInt x hx _ hq]
  have hkey := ordInt_mul (X.presheaf.stalk x)
    (algebraMap (X.presheaf.stalk x) X.functionField a /
      algebraMap (X.presheaf.stalk x) X.functionField b)
    (algebraMap (X.presheaf.stalk x) X.functionField b) hq hB
  have hcast : ordInt (X.presheaf.stalk x)
      (algebraMap (X.presheaf.stalk x) X.functionField a /
        algebraMap (X.presheaf.stalk x) X.functionField b *
        algebraMap (X.presheaf.stalk x) X.functionField b) (mul_ne_zero hq hB) =
      ordInt (X.presheaf.stalk x) (algebraMap (X.presheaf.stalk x) X.functionField a) hA := by
    congr 1
    exact div_mul_cancel₀ _ hB
  rw [hcast, ordInt_algebraMap _ a ha hA, ordInt_algebraMap _ b hb hB] at hkey
  omega

/-- Every nonzero rational function on an integral scheme is a quotient of two nonzero elements
of the local ring at any given point. -/
theorem exists_div_algebraMap_stalk_eq {Y : Scheme.{u}} [IsIntegral Y] (y : Y)
    {g : Y.functionField} (hg : g ≠ 0) :
    ∃ a b : Y.presheaf.stalk y, a ≠ 0 ∧ b ≠ 0 ∧
      algebraMap (Y.presheaf.stalk y) Y.functionField a /
        algebraMap (Y.presheaf.stalk y) Y.functionField b = g := by
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective (A := Y.presheaf.stalk y) g
  refine ⟨a, b, ?_, mem_nonZeroDivisors_iff_ne_zero.mp hb, hfrac⟩
  intro ha
  rw [ha, map_zero, zero_div] at hfrac
  exact hg hfrac.symm

/-- **Stacks 02JU.** The function-field map of a dominant morphism of integral schemes is
compatible with the stalk maps: a germ at a point is carried to the germ of its image. -/
theorem algebraMap_functionField_stalkMap {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y]
    (h : T ⟶ Y) [IsDominant h] (z : T) (v : Y.presheaf.stalk (h.base z)) :
    algebraMap (T.presheaf.stalk z) T.functionField ((h.stalkMap z).hom v) =
      dominantFunctionFieldMap h
        (algebraMap (Y.presheaf.stalk (h.base z)) Y.functionField v) := by
  have hgen : h.base (genericPoint T) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral h).out 1 2).mp (inferInstance : IsDominant h)
  have hsp : genericPoint T ⤳ z := genericPoint_specializes z
  have hspY : h.base (genericPoint T) ⤳ h.base z := h.base.hom.map_specializes hsp
  have hcongr : Y.presheaf.stalkSpecializes (genericPoint_specializes (h.base z)) ≫
      eqToHom (congrArg Y.presheaf.stalk hgen.symm) =
      Y.presheaf.stalkSpecializes hspY := by
    rw [← stalkCongr_eq_eqToHom hgen.symm, TopCat.Presheaf.stalkCongr_hom]
    exact Y.presheaf.stalkSpecializes_comp _ _
  have hnat := Scheme.Hom.stalkSpecializes_stalkMap h (genericPoint T) z hsp
  have hmor : h.stalkMap z ≫ T.presheaf.stalkSpecializes hsp =
      Y.presheaf.stalkSpecializes (genericPoint_specializes (h.base z)) ≫
        eqToHom (congrArg Y.presheaf.stalk hgen.symm) ≫ h.stalkMap (genericPoint T) := by
    rw [← hnat, ← Category.assoc, hcongr]
  have hfield : dominantFunctionFieldMap h =
      (eqToHom (congrArg Y.presheaf.stalk hgen.symm) ≫ h.stalkMap (genericPoint T)).hom := by
    rw [dominantFunctionFieldMap, stalkMap_eqToHom_eq_cast h (genericPoint T) _ hgen]
  rw [hfield]
  exact congrArg (fun m : Y.presheaf.stalk (h.base z) ⟶ T.functionField ↦ m.hom v) hmor

/-- The order of vanishing upstairs of the pullback of a quotient of two elements of the local
ring downstairs is the difference of the colengths of their images in the local ring
upstairs. -/
theorem ord_dominantFunctionFieldMap_eq_length_sub {T Y : Scheme.{u}} [IsIntegral T]
    [IsIntegral Y] [IsLocallyNoetherian T] (h : T ⟶ Y) [IsDominant h] {z : T}
    (hz : coheight z = 1) {a b : Y.presheaf.stalk (h.base z)} (ha : a ≠ 0) (hb : b ≠ 0) :
    T.ord (dominantFunctionFieldMap h
        (algebraMap (Y.presheaf.stalk (h.base z)) Y.functionField a /
          algebraMap (Y.presheaf.stalk (h.base z)) Y.functionField b)) z =
      ((Module.length (T.presheaf.stalk z)
          (T.presheaf.stalk z ⧸ Ideal.span {(h.stalkMap z).hom a})).toNat : ℤ) -
        ((Module.length (T.presheaf.stalk z)
          (T.presheaf.stalk z ⧸ Ideal.span {(h.stalkMap z).hom b})).toNat : ℤ) := by
  have hinjAll : ∀ w : T, Function.Injective (h.stalkMap w) :=
    ((tfae_isDominant_of_isIntegral h).out 1 6).mp (inferInstance : IsDominant h)
  have hne (v : Y.presheaf.stalk (h.base z)) (hv : v ≠ 0) : (h.stalkMap z).hom v ≠ 0 :=
    fun hzero ↦ hv (hinjAll z (by simpa using hzero))
  rw [map_div₀, ← algebraMap_functionField_stalkMap h z a,
    ← algebraMap_functionField_stalkMap h z b,
    ord_div_algebraMap_eq_length_sub hz (hne a ha) (hne b hb)]

/-- Over the generic point of the target a pulled-back rational function has order of vanishing
zero: it is a quotient of units of the local ring there, whose images are units upstairs. -/
theorem ord_dominantFunctionFieldMap_eq_zero_of_map_eq_genericPoint {T Y : Scheme.{u}}
    [IsIntegral T] [IsIntegral Y] [IsLocallyNoetherian T] (h : T ⟶ Y) [IsDominant h] {z : T}
    (hz : coheight z = 1) (hgen : h.base z = genericPoint Y) {g : Y.functionField}
    (hg : g ≠ 0) : T.ord (dominantFunctionFieldMap h g) z = 0 := by
  obtain ⟨a, b, ha, hb, hrep⟩ := exists_div_algebraMap_stalk_eq (h.base z) hg
  have hunit (v : Y.presheaf.stalk (h.base z)) (hv : v ≠ 0) :
      Module.length (T.presheaf.stalk z)
        (T.presheaf.stalk z ⧸ Ideal.span {(h.stalkMap z).hom v}) = 0 := by
    have htop : Ideal.span {(h.stalkMap z).hom v} = ⊤ :=
      Ideal.span_singleton_eq_top.mpr
        ((isUnit_of_ne_zero_of_eq_genericPoint hgen hv).map (h.stalkMap z).hom)
    rw [htop]
    have _ : Subsingleton (T.presheaf.stalk z ⧸ (⊤ : Ideal (T.presheaf.stalk z))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.length_eq_zero
  rw [← hrep, ord_dominantFunctionFieldMap_eq_length_sub h hz ha hb, hunit a ha, hunit b hb]
  simp

/-- A point of an integral closed subscheme which is not its generic point and whose image has
codimension one has codimension one: a closed immersion is a strictly monotone injection for
specialization, and the generic point is the unique maximal point. -/
theorem coheight_eq_one_of_isClosedImmersion {X T : Scheme.{u}} (i : T ⟶ X)
    [IsClosedImmersion i] [IsIntegral T] {z : T} (hx : coheight (i.base z) = 1)
    (hz : z ≠ genericPoint T) : coheight z = 1 := by
  have hmono : StrictMono (fun w : T ↦ i.base w) := by
    intro first second hlt
    refine lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr
      ((Scheme.le_iff_specializes.mp hlt.le).map i.continuous), fun hback ↦ hlt.ne ?_⟩
    exact i.isClosedEmbedding.injective
      (Specializes.antisymm (Scheme.le_iff_specializes.mp hback)
        ((Scheme.le_iff_specializes.mp hlt.le).map i.continuous)).eq
  have hle := Order.coheight_le_coheight_apply_of_strictMono (fun w : T ↦ i.base w) hmono z
  rw [hx] at hle
  exact le_antisymm hle (one_le_coheight_of_ne_genericPoint hz)

/-! ### The principal divisor on a component, pushed forward -/

/-- The coefficient at `x` of the pushforward along the closed immersion of an integral closed
subscheme `I` of the principal divisor on `I` of a rational function pulled back from `Y` is the
difference of the colengths, in the local ring of `X` at `x`, of the numerator and the
denominator together with the stalk of the ideal sheaf of `I`. -/
theorem properPushforward_principalDivisorCycle_apply_eq_length_sub (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : X.IdealSheafData)
    (hI : IsIntegral I.subscheme) (f : X ⟶ Y) [IsIntegral Y]
    (hdom : IsDominant (I.subschemeι ≫ f)) {n : ℤ}
    (hn : schemeDeltaDimension C (I.subschemeι ≫ sX) = (n : EInt)) {g : Y.functionField}
    {x : X} (hxI : x ∈ Set.range I.subschemeι.base) (hcoh : coheight x = 1)
    (hxgen : x ≠ genericPointOf I hI) {a b : Y.presheaf.stalk (f.base x)} (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hrep : algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a /
      algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField b = g) :
    letI := hI
    letI := hdom
    (properPushforward C (I.subschemeι ≫ sX) sX I.subschemeι rfl (n - 1)
        (principalDivisorCycle C (I.subschemeι ≫ sX) hn
          (dominantFunctionFieldMap (I.subschemeι ≫ f) g))).1 x =
      ((Module.length (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸
            (Ideal.span {(f.stalkMap x).hom a} ⊔ IdealSheafData.stalk I x))).toNat : ℤ) -
        ((Module.length (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸
            (Ideal.span {(f.stalkMap x).hom b} ⊔ IdealSheafData.stalk I x))).toNat : ℤ) := by
  let := hI
  let := hdom
  let : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ sX)
  obtain ⟨z, hz⟩ := hxI
  subst hz
  have hzgen : z ≠ genericPoint I.subscheme := fun heq ↦ hxgen (by rw [heq]; rfl)
  have hzcoh : coheight z = 1 := coheight_eq_one_of_isClosedImmersion _ hcoh hzgen
  have hcomp (v : Y.presheaf.stalk (f.base (I.subschemeι.base z))) :
      ((I.subschemeι ≫ f).stalkMap z).hom v =
        (I.subschemeι.stalkMap z).hom
          ((f.stalkMap (I.subschemeι.base z)).hom v) := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have htransfer (v : Y.presheaf.stalk (f.base (I.subschemeι.base z))) :
      Module.length (X.presheaf.stalk (I.subschemeι.base z))
          (X.presheaf.stalk (I.subschemeι.base z) ⧸
            (Ideal.span {(f.stalkMap (I.subschemeι.base z)).hom v} ⊔
              IdealSheafData.stalk I (I.subschemeι.base z))) =
        Module.length (I.subscheme.presheaf.stalk z)
          (I.subscheme.presheaf.stalk z ⧸
            Ideal.span {((I.subschemeι ≫ f).stalkMap z).hom v}) := by
    rw [← IdealSheafData.ker_stalkMap_subschemeι_eq_stalk I z,
      length_quotient_span_sup_ker (I.subschemeι.stalkMap z).hom
        (I.subschemeι.stalkMap_surjective z), hcomp v]
  rw [properPushforward_apply_image_of_isClosedImmersion, principalDivisorCycle_apply,
    ← hrep, htransfer a, htransfer b]
  exact ord_dominantFunctionFieldMap_eq_length_sub (I.subschemeι ≫ f) hzcoh ha hb

/-! ### Stacks 0EPH -/

/-- A flat algebra over a domain carries every nonzero element of the base to a regular
element. -/
theorem isSMulRegular_algebraMap_of_ne_zero {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Module.Flat A B] {v : A} (hv : v ≠ 0) :
    IsSMulRegular B (algebraMap A B v) := by
  have hvSMul : IsSMulRegular B v := Module.Flat.isSMulRegular_of_isRegular (R := A) (M := B)
    (isRegular_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hv))
  have hvB : IsRegular (algebraMap A B v) := by
    rw [isRegular_iff_eq_zero_of_mul]
    exact ⟨fun z hz ↦ hvSMul (by simpa [Algebra.smul_def] using hz),
      fun z hz ↦ hvSMul (by simpa [Algebra.smul_def, mul_comm] using hz)⟩
  exact Module.Flat.isSMulRegular_of_isRegular (R := B) (M := B) hvB

/-- A finite sum of a function vanishing off a predicate is the sum of any function matching it
along an equivalence from the subtype of that predicate. -/
theorem finsum_eq_finsum_of_equiv_subtype {α β M : Type*} [AddCommMonoid M] {p : α → Prop}
    {f : α → M} {g : β → M} (e : {a // p a} ≃ β) (hf : ∀ a, ¬ p a → f a = 0)
    (h : ∀ a : {a // p a}, f a = g (e a)) : ∑ᶠ a, f a = ∑ᶠ b, g b := by
  rw [← finsum_eq_of_bijective e e.bijective h, finsum_subtype_eq_finsum_cond]
  refine finsum_congr fun a ↦ ?_
  by_cases ha : p a
  · simp only [ha, finsum_true]
  · simp only [ha, finsum_false, hf a ha]

section ComponentFormula

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
  [Flat f] (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) {k : ℤ}
  (hY : schemeDeltaDimension C sY = (k : EInt))

/-- At a point lying over the generic point of `Y`, the pushforward of the principal divisor of
`g` pulled back to a reduced irreducible component of `X` vanishes. -/
theorem properPushforward_principalDivisorCycle_integralComponentAt_apply_eq_zero
    {g : Y.functionField} (hg : g ≠ 0) (x : X) (hy : f.base x = genericPoint Y)
    (W : irreducibleComponents X) :
    letI : IsIntegral (integralComponentAt W.2.1.genericPoint).subscheme :=
      isIntegral_integralComponentAt _
    letI := isDominant_subschemeι_integralComponentAt_comp f W
    (properPushforward C ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX) sX
      (integralComponentAt W.2.1.genericPoint).subschemeι rfl (k + (r : ℤ) - 1)
      (principalDivisorCycle C _
        (schemeDeltaDimension_integralComponentAt_comp C sX sY f hbase r hf hY W)
        (dominantFunctionFieldMap
          ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f) g))).1 x = 0 := by
  let : IsIntegral (integralComponentAt W.2.1.genericPoint).subscheme :=
    isIntegral_integralComponentAt _
  let := isDominant_subschemeι_integralComponentAt_comp f W
  let : IsLocallyNoetherian (integralComponentAt W.2.1.genericPoint).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX)
  by_cases hmem : x ∈ Set.range (integralComponentAt W.2.1.genericPoint).subschemeι.base
  · obtain ⟨z, hz⟩ := hmem
    rw [← hz, properPushforward_apply_image_of_isClosedImmersion, principalDivisorCycle_apply]
    have hzgen : ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f).base z =
        genericPoint Y := by
      change f.base ((integralComponentAt W.2.1.genericPoint).subschemeι.base z) = _
      rwa [hz]
    by_cases hzc : coheight z = 1
    · exact ord_dominantFunctionFieldMap_eq_zero_of_map_eq_genericPoint _ hzc hzgen hg
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hzc _
  · exact properPushforward_apply_of_notMem_range C _ sX _ rfl _ _ hmem

/-- At a point `x` of relative dimension `k + r - 1` not lying over the generic point of `Y`,
writing `g = a / b` in the local ring of `Y` at `f x`, the flat pullback of the principal divisor
of `g` at `x` is a sum over the minimal primes `p` of `𝒪_{X, x}` of
`length(𝒪_{X,x,p}) · (length(𝒪_{X,x}/(a, p)) - length(𝒪_{X,x}/(b, p)))`. -/
theorem flatPullback_principalDivisorCycle_apply_eq_finsum_minimalPrimes {g : Y.functionField}
    (x : X) (hx : relativeDimension C.dimensionFunction sX x = k + (r : ℤ) - 1)
    (hy : f.base x ≠ genericPoint Y) {a b : Y.presheaf.stalk (f.base x)} (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hrep : algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a /
      algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField b = g) :
    (flatPullback C sX sY f hbase r hf (k - 1) (principalDivisorCycle C sY hY g)).1 x =
      ∑ᶠ p : {p : PrimeSpectrum (X.presheaf.stalk x) //
          p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)},
        (((Module.length (Localization.AtPrime p.1.asIdeal)
            (Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
          ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
            (Ideal.span {(f.stalkMap x).hom a} ⊔ p.1.asIdeal))).toNat : ℤ) -
        ((Module.length (Localization.AtPrime p.1.asIdeal)
            (Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
          ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
            (Ideal.span {(f.stalkMap x).hom b} ⊔ p.1.asIdeal))).toNat : ℤ)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hgen := relativeDimension_genericPoint_irreducibleComponent C sX sY f hbase r hf hY
  have hcoh : coheight x = 1 :=
    coheight_eq_one_of_relativeDimension_eq_sub_one C sX hgen (n := k + (r : ℤ)) (by omega)
  have hycoh : coheight (f.base x) = 1 := coheight_map_eq_one_of_flat f
    (fun z hzx hne ↦ isMax_of_specializes_of_relativeDimension_eq_sub_one C sX hgen
      (n := k + (r : ℤ)) (by omega) hzx hne) hy
  let : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have halg : algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) =
      (f.stalkMap x).hom := RingHom.algebraMap_toAlgebra _
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) := by
    rw [halg]
    infer_instance
  have : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have hBdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight x]
    exact_mod_cast hcoh
  have hydim : relativeDimension C.dimensionFunction sY (f.base x) = k - 1 := by
    rw [← deltaDimension_closure_singleton C sY (f.base x)]
    exact deltaDimension_closure_singleton_eq_sub_one C sY hY hycoh
  have hex := exists_genericPoints_comap_integralComponentAt C sX sY f hbase r hf x
    (by rw [hx, hydim]; ring)
  have hweight : flatPullbackWeight C sX f ((k - 1) + (r : ℤ)) x =
      ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
        extendedMaximalIdeal (Y.presheaf.stalk (f.base x))
          (X.presheaf.stalk x))).toNat : ℤ) := by
    rw [flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal C sX f _ x hex
      (by omega), extendedMaximalIdeal, halg]
  have : Finite {p : PrimeSpectrum (X.presheaf.stalk x) //
      p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)} :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing (X.presheaf.stalk x) ⊥).preimage
      fun p _ q _ h ↦ PrimeSpectrum.ext h).to_subtype
  rw [flatPullback_apply, principalDivisorCycle_apply, hweight, ← hrep,
    ord_div_algebraMap_eq_length_sub hycoh ha hb, sub_mul,
    length_quotient_extendedMaximalIdeal_mul_eq_finsum_minimalPrimes hBdim a
      (isSMulRegular_algebraMap_of_ne_zero ha),
    length_quotient_extendedMaximalIdeal_mul_eq_finsum_minimalPrimes hBdim b
      (isSMulRegular_algebraMap_of_ne_zero hb)]
  exact (finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)).symm

/-- At a point `x` of relative dimension `k + r - 1`, writing `g = a / b` in the local ring of `Y`
at `f x`, the term of an irreducible component `W` through `x` in the sum of Stacks 0EPH is the
term of the minimal prime of `𝒪_{X, x}` corresponding to `W`. -/
theorem cycleAssociatedToClosedSubscheme_mul_properPushforward_apply_eq_length_sub
    {g : Y.functionField} (x : X)
    (hx : relativeDimension C.dimensionFunction sX x = k + (r : ℤ) - 1)
    {a b : Y.presheaf.stalk (f.base x)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hrep : algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a /
      algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField b = g)
    (W : {W : irreducibleComponents X // x ∈ (W : Set X)}) :
    (cycleAssociatedToClosedSubscheme C sX (𝟙 X) (k + (r : ℤ))).1 W.1.2.1.genericPoint *
        (letI : IsIntegral (integralComponentAt W.1.2.1.genericPoint).subscheme :=
           isIntegral_integralComponentAt _
         letI := isDominant_subschemeι_integralComponentAt_comp f W.1
         (properPushforward C ((integralComponentAt W.1.2.1.genericPoint).subschemeι ≫ sX) sX
           (integralComponentAt W.1.2.1.genericPoint).subschemeι rfl (k + (r : ℤ) - 1)
           (principalDivisorCycle C _
             (schemeDeltaDimension_integralComponentAt_comp C sX sY f hbase r hf hY W.1)
             (dominantFunctionFieldMap
               ((integralComponentAt W.1.2.1.genericPoint).subschemeι ≫ f) g))).1 x) =
      ((Module.length (Localization.AtPrime (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal)
          (Localization.AtPrime (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal)).toNat :
            ℤ) *
        ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
          (Ideal.span {(f.stalkMap x).hom a} ⊔
            (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal))).toNat : ℤ) -
      ((Module.length (Localization.AtPrime (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal)
          (Localization.AtPrime (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal)).toNat :
            ℤ) *
        ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
          (Ideal.span {(f.stalkMap x).hom b} ⊔
            (irreducibleComponentsEquivMinimalPrimes x W).1.asIdeal))).toNat : ℤ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hgen := relativeDimension_genericPoint_irreducibleComponent C sX sY f hbase r hf hY
  have hcoh : coheight x = 1 :=
    coheight_eq_one_of_relativeDimension_eq_sub_one C sX hgen (n := k + (r : ℤ)) (by omega)
  let : IsIntegral (integralComponentAt W.1.2.1.genericPoint).subscheme :=
    isIntegral_integralComponentAt _
  let := isDominant_subschemeι_integralComponentAt_comp f W.1
  set p : PrimeSpectrum (X.presheaf.stalk x) :=
    (irreducibleComponentsEquivMinimalPrimes x W).1 with hpdef
  have hp : X.fromSpecStalk x p = (genericPoints.ofComponent W.1 : X) :=
    fromSpecStalk_irreducibleComponentsEquivMinimalPrimes x W
  have hWdim : deltaDimension C sX
      ⟨W.1.1, W.1.2.1, isClosed_of_mem_irreducibleComponents W.1.1 W.1.2⟩ =
      k + (r : ℤ) - 1 + 1 := by
    rw [deltaDimension_eq_of_isGenericPoint C sX _ W.1.2.1.genericPoint
      (isGenericPoint_genericPoint_component W.1), hgen W.1]
    ring
  have hmult : (cycleAssociatedToClosedSubscheme C sX (𝟙 X) (k + (r : ℤ))).1
      W.1.2.1.genericPoint =
      ((Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal)).toNat : ℤ) := by
    have hcyc := cycleAssociatedToClosedSubscheme_id_apply_eq_length C sX
      (k + (r : ℤ) - 1) W.1 hWdim x p hp
    rwa [show k + (r : ℤ) - 1 + 1 = k + (r : ℤ) by ring] at hcyc
  have hxrange : x ∈ Set.range (integralComponentAt W.1.2.1.genericPoint).subschemeι.base := by
    rw [range_subschemeι_integralComponentAt_genericPoint W.1]
    exact W.2
  have hxgen : x ≠ genericPointOf (integralComponentAt W.1.2.1.genericPoint)
      (isIntegral_integralComponentAt _) := by
    rw [genericPointOf_integralComponentAt]
    intro heq
    rw [heq, hgen W.1] at hx
    omega
  have hstalk : IdealSheafData.stalk (integralComponentAt W.1.2.1.genericPoint) x =
      p.asIdeal := by
    rw [integralComponentAt_genericPoint_eq_vanishingIdeal W.1]
    exact stalk_vanishingIdeal_eq_of_mem_minimalPrimes x W.1 W.2 p
      (irreducibleComponentsEquivMinimalPrimes x W).2
      (hp ▸ (genericPoints.isGenericPoint_ofComponent W.1).mem)
  have hpush := properPushforward_principalDivisorCycle_apply_eq_length_sub C sX
    (integralComponentAt W.1.2.1.genericPoint) (isIntegral_integralComponentAt _) f
    (isDominant_subschemeι_integralComponentAt_comp f W.1)
    (schemeDeltaDimension_integralComponentAt_comp C sX sY f hbase r hf hY W.1)
    hxrange hcoh hxgen ha hb hrep
  rw [hstalk] at hpush
  rw [hmult, hpush, mul_sub]

/-- At a point `x` of relative dimension `k + r - 1`, writing `g = a / b` in the local ring of `Y`
at `f x`, the sum of Stacks 0EPH at `x` is the corresponding sum over the minimal primes of
`𝒪_{X, x}`. -/
theorem finsum_components_eq_finsum_minimalPrimes {g : Y.functionField} (x : X)
    (hx : relativeDimension C.dimensionFunction sX x = k + (r : ℤ) - 1)
    {a b : Y.presheaf.stalk (f.base x)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hrep : algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a /
      algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField b = g) :
    ∑ᶠ W : irreducibleComponents X,
        (cycleAssociatedToClosedSubscheme C sX (𝟙 X) (k + (r : ℤ))).1 W.2.1.genericPoint *
          (letI : IsIntegral (integralComponentAt W.2.1.genericPoint).subscheme :=
             isIntegral_integralComponentAt _
           letI := isDominant_subschemeι_integralComponentAt_comp f W
           (properPushforward C ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX) sX
             (integralComponentAt W.2.1.genericPoint).subschemeι rfl (k + (r : ℤ) - 1)
             (principalDivisorCycle C _
               (schemeDeltaDimension_integralComponentAt_comp C sX sY f hbase r hf hY W)
               (dominantFunctionFieldMap
                 ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f) g))).1 x) =
      ∑ᶠ p : {p : PrimeSpectrum (X.presheaf.stalk x) //
          p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)},
        (((Module.length (Localization.AtPrime p.1.asIdeal)
            (Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
          ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
            (Ideal.span {(f.stalkMap x).hom a} ⊔ p.1.asIdeal))).toNat : ℤ) -
        ((Module.length (Localization.AtPrime p.1.asIdeal)
            (Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
          ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
            (Ideal.span {(f.stalkMap x).hom b} ⊔ p.1.asIdeal))).toNat : ℤ)) := by
  refine finsum_eq_finsum_of_equiv_subtype (irreducibleComponentsEquivMinimalPrimes x)
    (fun W hW ↦ ?_)
    (cycleAssociatedToClosedSubscheme_mul_properPushforward_apply_eq_length_sub C sX sY f hbase r
      hf hY x hx ha hb hrep)
  let : IsIntegral (integralComponentAt W.2.1.genericPoint).subscheme :=
    isIntegral_integralComponentAt _
  let := isDominant_subschemeι_integralComponentAt_comp f W
  refine mul_eq_zero_of_right _ (properPushforward_apply_of_notMem_range C _ sX _ rfl _ _
    fun hrange ↦ hW ?_)
  rwa [range_subschemeι_integralComponentAt_genericPoint W] at hrange

end ComponentFormula

/-- **Stacks 0EPH.** Let `C = (S, δ)` be the base situation of chapter 42, let `X` and `Y` be
locally of finite type over `S` with `Y` integral of delta-dimension `k`, and let `f : X ⟶ Y` be
flat of relative dimension `r`. For a nonzero rational function `g` on `Y`,

  `f^* div_Y(g) = ∑_j n_j i_{j,*} div_{X_j}(g ∘ f|_{X_j})`

as `(k + r - 1)`-cycles on `X`, where the sum is over the irreducible components `X_j` of `X`
with their reduced structure and `n_j` is the multiplicity of `X_j` in the fundamental cycle
`[X]_{k + r}`. The identity is read coefficientwise at a point `x` of `X`. -/
@[stacks 0EPH]
theorem flatPullback_principalDivisor_eq_sum_components (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) {k : ℤ}
    (hY : schemeDeltaDimension C sY = (k : EInt)) (g : Y.functionField) (hg : g ≠ 0) (x : X) :
    (flatPullback C sX sY f hbase r hf (k - 1) (principalDivisorCycle C sY hY g)).1 x =
      ∑ᶠ W : irreducibleComponents X,
        (cycleAssociatedToClosedSubscheme C sX (𝟙 X) (k + (r : ℤ))).1 W.2.1.genericPoint *
          (letI : IsIntegral (integralComponentAt W.2.1.genericPoint).subscheme :=
             isIntegral_integralComponentAt _
           letI := isDominant_subschemeι_integralComponentAt_comp f W
           (properPushforward C ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX) sX
             (integralComponentAt W.2.1.genericPoint).subschemeι rfl (k + (r : ℤ) - 1)
             (principalDivisorCycle C _
               (schemeDeltaDimension_integralComponentAt_comp C sX sY f hbase r hf hY W)
               (dominantFunctionFieldMap
                 ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f) g))).1 x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  by_cases hx : relativeDimension C.dimensionFunction sX x = k + (r : ℤ) - 1
  · by_cases hy : f.base x = genericPoint Y
    · rw [flatPullback_apply, principalDivisorCycle_apply, hy,
        Scheme.ord_eq_zero_of_coheight_neq_one
          (by simpa using (IsMax.coheight_eq_zero
            (isMax_genericPoint_of_isIntegral (T := Y))) ▸
              (by decide : ¬ (0 : ℕ∞) = 1)) g, zero_mul, eq_comm]
      exact finsum_eq_zero_of_forall_eq_zero fun W ↦ mul_eq_zero_of_right _
        (properPushforward_principalDivisorCycle_integralComponentAt_apply_eq_zero C sX sY f
          hbase r hf hY hg x hy W)
    · obtain ⟨a, b, ha, hb, hrep⟩ := exists_div_algebraMap_stalk_eq (f.base x) hg
      rw [flatPullback_principalDivisorCycle_apply_eq_finsum_minimalPrimes C sX sY f hbase r hf hY
        x hx hy ha hb hrep,
        finsum_components_eq_finsum_minimalPrimes C sX sY f hbase r hf hY x hx ha hb hrep]
  · have hzero (n : ℤ) (hn : n = k + (r : ℤ) - 1) (c : CycleGroup C sX n) : c.1 x = 0 := by
      by_contra hne
      have := (mem_cyclesOfDimension_iff_forall_point C sX n c.1).mp c.2 x hne
      omega
    rw [hzero (k - 1 + (r : ℤ)) (by omega), eq_comm]
    exact finsum_eq_zero_of_forall_eq_zero fun W ↦ mul_eq_zero_of_right _ (hzero _ rfl _)

end Stacks.Chow

end
