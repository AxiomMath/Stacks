module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaBaseCase
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaWhole
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TripleProductCycleAssociativity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.TransversalCycleMultiplicity
import StacksCore.Tactic.StacksAttribute

/-!
# Associativity of the intersection product of three closed subvarieties

Let `X` be a nonsingular variety over an algebraically closed field — the convention of the
chapter, Tag 0AZ8 — and let `U`, `V`, `W` be closed subvarieties intersecting properly pairwise
and satisfying

`dim (U ∩ V ∩ W) ≤ dim U + dim V + dim W - 2 dim X`.

Then `U · (V · W) = (U · V) · W` as cycles on `X`, where `·` is the intersection product of
Section 43.14 for two closed subvarieties and its bilinear extension of Tag 0B08 for a
subvariety against a cycle. This is Tag 0B1L.

The proof is the source's. Each side is computed by the Tor formula of Tag 0B0W, available here
as `Stacks.Intersection.ReductionToDiagonal.torFormula`: writing `V · W` as the alternating sum
`∑ⱼ (-1)ʲ [Torⱼ(𝒪_V, 𝒪_W)]` and using that the product of cycles is linear in each variable,

`U · (V · W) = ∑ⱼ (-1)ʲ (𝒪_U · Torⱼ(𝒪_V, 𝒪_W)) = ∑ᵢⱼ (-1)^(i+j) [Torᵢ(𝒪_U, Torⱼ(𝒪_V, 𝒪_W))]`,

and symmetrically `(U · V) · W = ∑ᵢⱼ (-1)^(i+j) [Torᵢ(Torⱼ(𝒪_U, 𝒪_V), 𝒪_W)]`. The two double
sums agree because the iterated `Tor` modules of the three stalks have equal alternating double
sums of lengths; that regrouping is
`AlgebraicGeometry.TorFormula.intersectionProductCycle_assoc_of_closures`.

## Main results

* `Stacks.Intersection.ReductionToDiagonal.torFormulaCycleIntersectionProduct_assoc` —
  **Tag 0B1L**, `U · (V · W) = (U · V) · W`, at every expected dimension, together with the
  properness of the two outer intersections `U, V · W` and `U · V, W` that the statement
  presupposes.
* `Stacks.Intersection.ReductionToDiagonal.torFormulaCycleIntersectionProduct_assoc_of_closures` —
  the main case, in which the three expected dimensions are natural numbers.
* `Stacks.Intersection.ReductionToDiagonal.torFormulaCycleIntersectionProduct_single_left_eq_zero`
  and its right-hand companion — the degenerate case: when `U ∩ V ∩ W` is empty both sides vanish.

## Implementation notes

Closed subvarieties are their generic points, as cycles are: `U`, `V`, `W` are the reduced
closures of three points `u`, `v`, `w` of `X`, and the prime cycle `[U]` is
`Function.locallyFinsuppWithin.single u 1`.

`WithBot ℕ∞` has no subtraction, so the displayed hypothesis
`dim (U ∩ V ∩ W) ≤ dim U + dim V + dim W - 2 dim X` is spelled
`dim (U ∩ V ∩ W) + 2 dim X ≤ dim U + dim V + dim W`, in the way proper intersection itself is
spelled in Tag 0AZQ; the two agree because all the dimensions involved are finite, the empty set
having dimension `⊥`. The dimensions of `X`, `U`, `V`, `W` are named as natural numbers `dX`,
`r`, `s`, `t`, and the three expected dimensions `r + s - dX`, `s + t - dX` and
`r + s + t - 2 dX`, in which the products are formed, are integers. One of them can be negative —
three curves on a surface meeting pairwise in points, with empty triple intersection — and then
`U ∩ V ∩ W` is empty and both sides of the identity are zero. Otherwise all three are natural
numbers, and the identity is the main case
`torFormulaCycleIntersectionProduct_assoc_of_closures`, which spells them as `p`, `q`, `m` with
the relations `r + s = dX + p`, `s + t = dX + q` and `r + s + t = 2 dX + m`.

The source's statement presupposes that the two outer products are defined, that is, that `U`
and `V · W` intersect properly and that `U · V` and `W` do (Definition 0AZQ); the registered
statement proves both. The product of cycles of Tag 0B08 is read at every pair of points, the
zero cycle at a pair whose `Tor` sheaves are too big; these two properness clauses are what make
every pair actually contributing to the outer products a properly intersecting one, so that the
outer products are the ones of the source.

Linearity of the product of cycles in one variable along an alternating sum is
`AlgebraicGeometry.TorFormula.cycleIntersectionProduct_finsum_zsmul_left` and its right-hand
companion, which refine the bilinearity of
`AlgebraicGeometry.TorFormula.cycleIntersectionProduct` from two summands to a finitely supported
family. Each cycle has to have finitely many components for that, which on a quasi-compact `X` —
in particular on a variety — is automatic.

## References

* [Stacks Project, Lemma 43.20.1 (Tag 0B1L)](https://stacks.math.columbia.edu/tag/0B1L)
* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZ8](https://stacks.math.columbia.edu/tag/0AZ8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.TorFormula
open Stacks.Chow

namespace Stacks.Intersection.ReductionToDiagonal

universe u

variable {X : Scheme.{u}}

/-! ### The dimension of a closed subvariety as a delta-dimension -/

/-- **Over a field the dimension of the reduced closure of a point is its delta-dimension.** If
the closure of `{x}` has dimension `r`, then the integral closed subscheme it carries has
delta-dimension `r` for the base situation `Spec k`. This is Tag 02QO read at the reduced closure
of a point. -/
theorem schemeDeltaDimension_integralComponentAt_eq_of_topologicalKrullDim_eq (k : Type u)
    [Field k] (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f] (x : X) (r : ℕ)
    (hx : topologicalKrullDim (closure ({x} : Set X)) = (r : WithBot ℕ∞)) :
    schemeDeltaDimension (fieldChowSituation k)
      ((integralComponentAt x).subschemeι ≫ f) = ((r : ℤ) : EInt) := by
  have : JacobsonSpace (fieldChowSituation k).S :=
    inferInstanceAs (JacobsonSpace (AlgebraicGeometry.Spec (CommRingCat.of k)))
  have := isIntegral_integralComponentAt x
  have hcar : topologicalKrullDim ↥(integralComponentAt x).subscheme = (r : WithBot ℕ∞) := by
    rw [← hx, ← coe_support_integralComponentAt x, ← Scheme.IdealSheafData.range_subschemeι]
    exact IsHomeomorph.topologicalKrullDim_eq _
      (IsClosedImmersion.isClosedEmbedding
        (integralComponentAt x).subschemeι).isEmbedding.toHomeomorph.isHomeomorph
  have hgen : IsGenericPoint (genericPoint ↥(integralComponentAt x).subscheme)
      (Set.univ : Set ↥(integralComponentAt x).subscheme) :=
    (IrreducibleSpace.isIrreducible_univ _).isGenericPoint_genericPoint isClosed_univ
  have htop := topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k)
    (fun _ _ => rfl) f (integralComponentAt x).subschemeι
    (genericPoint ↥(integralComponentAt x).subscheme) hgen
  rw [hcar] at htop
  have hrd : relativeDimension (fieldChowSituation k).dimensionFunction f
      (genericPointOf (integralComponentAt x) (isIntegral_integralComponentAt x)) = (r : ℤ) := by
    have hnonneg := relativeDimension_nonneg (fieldChowSituation k) (fun _ _ => rfl) f
      (genericPointOf (integralComponentAt x) (isIntegral_integralComponentAt x))
    have hnat : (relativeDimension (fieldChowSituation k).dimensionFunction f
        (genericPointOf (integralComponentAt x)
          (isIntegral_integralComponentAt x))).toNat = r := by
      exact_mod_cast htop.symm
    omega
  rw [genericPointOf_integralComponentAt x] at hrd
  rw [schemeDeltaDimension_integralComponentAt (fieldChowSituation k) f x, hrd]

/-! ### Tag 0B1L -/

/-- **Associativity in nonnegative expected dimensions.** Let `X` be a nonsingular variety over
an algebraically closed field of dimension `dX`, and let `U`, `V`, `W` be the reduced closures of
three points `u`, `v`, `w`, of dimensions `r`, `s`, `t`, intersecting properly pairwise. Assume
the three expected dimensions are natural numbers `p = r + s - dX`, `q = s + t - dX` and
`m = r + s + t - 2 dX`, and that `dim (U ∩ V ∩ W) ≤ m`. Then, as cycles on `X`,

`U · (V · W) = (U · V) · W`,

the product being the one of Section 43.14 for two closed subvarieties and its bilinear extension
of Tag 0B08 for a subvariety against a cycle.

This is the main case of Tag 0B1L, the one in which the triple intersection is nonempty; the
whole lemma, at every expected dimension and with the properness of the two outer intersections,
is `torFormulaCycleIntersectionProduct_assoc`. -/
theorem torFormulaCycleIntersectionProduct_assoc_of_closures [DecidableEq X] (k : Type u)
    [Field k] [IsAlgClosed k] (f : X ⟶ Spec (.of k)) [IsVariety k f] (hX : IsRegular X)
    (u v w : X) (dX r s t p q m : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hu : topologicalKrullDim (closure ({u} : Set X)) = (r : WithBot ℕ∞))
    (hv : topologicalKrullDim (closure ({v} : Set X)) = (s : WithBot ℕ∞))
    (hw : topologicalKrullDim (closure ({w} : Set X)) = (t : WithBot ℕ∞))
    (huv : AlgebraicGeometry.IntersectProperly
      ⟨closure {u}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (hvw : AlgebraicGeometry.IntersectProperly
      ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (_huw : AlgebraicGeometry.IntersectProperly
      ⟨closure {u}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (hp : r + s = dX + p) (hq : s + t = dX + q) (hm : r + s + t = 2 * dX + m)
    (huvw : topologicalKrullDim
        (↥(closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X))) ≤
      (m : WithBot ℕ∞)) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX (m : ℤ)
        (Function.locallyFinsuppWithin.single u 1)
        (torSubvarietyProductOfBound (fieldChowSituation k) f hX (q : ℤ)
          (torSupportBound_of_intersectProperly k f hX v w hdX
            (by rw [hv, hw, ← Nat.cast_add, ← Nat.cast_add, hq]) hvw)) =
      torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX (m : ℤ)
        (torSubvarietyProductOfBound (fieldChowSituation k) f hX (p : ℤ)
          (torSupportBound_of_intersectProperly k f hX u v hdX
            (by rw [hu, hv, ← Nat.cast_add, ← Nat.cast_add, hp]) huv))
        (Function.locallyFinsuppWithin.single w 1) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hreg : ∀ z : X, IsRegularLocalRing (X.presheaf.stalk z) :=
    fun z => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX z
  have hcUV : ∀ i : ℕ,
      _root_.SheafOfModules.IsCoherent (torSheaf X (structureSheafAt u) (structureSheafAt v) i) :=
    fun i => isCoherent_torSheaf_of_isRegular X hX (structureSheafAt u) (structureSheafAt v)
      (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v) i
  have hcVW : ∀ j : ℕ,
      _root_.SheafOfModules.IsCoherent (torSheaf X (structureSheafAt v) (structureSheafAt w) j) :=
    fun j => isCoherent_torSheaf_of_isRegular X hX (structureSheafAt v) (structureSheafAt w)
      (isCoherent_structureSheafAt v) (isCoherent_structureSheafAt w) j
  -- the two inner products are legitimate, the pairs intersecting properly
  have hdimUV : topologicalKrullDim (closure ({u} : Set X)) +
      topologicalKrullDim (closure ({v} : Set X)) =
      (dX : WithBot ℕ∞) + (p : WithBot ℕ∞) := by
    rw [hu, hv, ← Nat.cast_add, ← Nat.cast_add, hp]
  have hdimVW : topologicalKrullDim (closure ({v} : Set X)) +
      topologicalKrullDim (closure ({w} : Set X)) =
      (dX : WithBot ℕ∞) + (q : WithBot ℕ∞) := by
    rw [hv, hw, ← Nat.cast_add, ← Nat.cast_add, hq]
  have hbUV : TorSupportBound (fieldChowSituation k) f hX (p : ℤ) u v :=
    torSupportBound_of_intersectProperly k f hX u v hdX hdimUV huv
  have hbVW : TorSupportBound (fieldChowSituation k) f hX (q : ℤ) v w :=
    torSupportBound_of_intersectProperly k f hX v w hdX hdimVW hvw
  -- the dimensions of the supports of `𝒪_U` and `𝒪_W`
  have hsu : topologicalKrullDim (SheafOfModules.supp (structureSheafAt u)) ≤
      (r : WithBot ℕ∞) := by rw [supp_structureSheafAt]; exact le_of_eq hu
  have hsw : topologicalKrullDim (SheafOfModules.supp (structureSheafAt w)) ≤
      (t : WithBot ℕ∞) := by rw [supp_structureSheafAt]; exact le_of_eq hw
  -- the dimension of the intersection of each properly intersecting pair
  have hinterUV : topologicalKrullDim (↥(closure ({u} : Set X) ∩ closure ({v} : Set X))) ≤
      (p : WithBot ℕ∞) :=
    topologicalKrullDim_inter_le_of_intersectProperly_of_add_eq huv hdX hdimUV
  have hinterVW : topologicalKrullDim (↥(closure ({v} : Set X) ∩ closure ({w} : Set X))) ≤
      (q : WithBot ℕ∞) :=
    topologicalKrullDim_inter_le_of_intersectProperly_of_add_eq hvw hdX hdimVW
  -- the supports of the two inner families of `Tor` sheaves
  have hsVW : ∀ j : ℕ, topologicalKrullDim (SheafOfModules.supp
      (torSheaf X (structureSheafAt v) (structureSheafAt w) j)) ≤ (q : WithBot ℕ∞) := fun j =>
    le_trans (Topology.IsEmbedding.inclusion
      (supp_torSheaf_structureSheafAt_subset v w j)).isInducing.topologicalKrullDim_le hinterVW
  have hsUV : ∀ i : ℕ, topologicalKrullDim (SheafOfModules.supp
      (torSheaf X (structureSheafAt u) (structureSheafAt v) i)) ≤ (p : WithBot ℕ∞) := fun i =>
    le_trans (Topology.IsEmbedding.inclusion
      (supp_torSheaf_structureSheafAt_subset u v i)).isInducing.topologicalKrullDim_le hinterUV
  -- the displayed bound on the triple intersection, read on the two relevant pairs
  have htL : ∀ j : ℕ, topologicalKrullDim
      (↥(SheafOfModules.supp (structureSheafAt u) ∩ SheafOfModules.supp
        (torSheaf X (structureSheafAt v) (structureSheafAt w) j))) ≤ (m : WithBot ℕ∞) := by
    intro j
    refine le_trans ((Topology.IsEmbedding.inclusion ?_).isInducing.topologicalKrullDim_le) huvw
    intro z hz
    rw [supp_structureSheafAt] at hz
    exact ⟨⟨hz.1, (supp_torSheaf_structureSheafAt_subset v w j hz.2).1⟩,
      (supp_torSheaf_structureSheafAt_subset v w j hz.2).2⟩
  have htR : ∀ i : ℕ, topologicalKrullDim
      (↥(SheafOfModules.supp (torSheaf X (structureSheafAt u) (structureSheafAt v) i) ∩
        SheafOfModules.supp (structureSheafAt w))) ≤ (m : WithBot ℕ∞) := by
    intro i
    refine le_trans ((Topology.IsEmbedding.inclusion ?_).isInducing.topologicalKrullDim_le) huvw
    intro z hz
    rw [supp_structureSheafAt] at hz
    exact ⟨supp_torSheaf_structureSheafAt_subset u v i hz.1, hz.2⟩
  -- `[U] = [𝒪_U]_r` and `[W] = [𝒪_W]_t`
  have hcycU := coherentSheafCycle_structureSheafAt (fieldChowSituation k) f u (r : ℤ)
    (schemeDeltaDimension_integralComponentAt_eq_of_topologicalKrullDim_eq k f u r hu)
    (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k f
      (structureSheafAt u) r hsu)
  have hcycW := coherentSheafCycle_structureSheafAt (fieldChowSituation k) f w (t : ℤ)
    (schemeDeltaDimension_integralComponentAt_eq_of_topologicalKrullDim_eq k f w t hw)
    (schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k f
      (structureSheafAt w) t hsw)
  refine Eq.trans ?_ (Eq.trans
    (intersectionProductCycle_assoc_of_closures k f hX u v w dX m hdX.le huvw) ?_)
  · refine Eq.trans (cycleIntersectionProduct_finsum_zsmul_right
      (torFormulaSubvarietyProductTotal (fieldChowSituation k) f hX (m : ℤ))
      (Function.locallyFinsuppWithin.single u 1) (fun j : ℕ => (-1 : ℤ) ^ j)
      (fun j : ℕ => coherentSheafCycle (fieldChowSituation k) f
        (torSheaf X (structureSheafAt v) (structureSheafAt w) j) (q : ℤ) (hbVW j))
      (finite_support_torSheafCycle (fieldChowSituation k) f hX (structureSheafAt v)
        (structureSheafAt w) (isCoherent_structureSheafAt v) (isCoherent_structureSheafAt w)
        (q : ℤ) hbVW hreg dX hdX.le)) ?_
    refine finsum_congr fun j => congrArg (fun z => ((-1 : ℤ) ^ j) • z) ?_
    rw [← hcycU]
    exact (torFormula k f hX (structureSheafAt u)
      (torSheaf X (structureSheafAt v) (structureSheafAt w) j) (isCoherent_structureSheafAt u)
      (isCoherent_torSheaf_of_isRegular X hX (structureSheafAt v) (structureSheafAt w)
        (isCoherent_structureSheafAt v) (isCoherent_structureSheafAt w) j)
      r q m dX hdX (by omega) hsu (hsVW j) (htL j)).2
  · refine Eq.trans ?_ (cycleIntersectionProduct_finsum_zsmul_left
      (torFormulaSubvarietyProductTotal (fieldChowSituation k) f hX (m : ℤ))
      (fun i : ℕ => (-1 : ℤ) ^ i)
      (fun i : ℕ => coherentSheafCycle (fieldChowSituation k) f
        (torSheaf X (structureSheafAt u) (structureSheafAt v) i) (p : ℤ) (hbUV i))
      (finite_support_torSheafCycle (fieldChowSituation k) f hX (structureSheafAt u)
        (structureSheafAt v) (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v)
        (p : ℤ) hbUV hreg dX hdX.le)
      (Function.locallyFinsuppWithin.single w 1)).symm
    refine finsum_congr fun i => congrArg (fun z => ((-1 : ℤ) ^ i) • z) ?_
    rw [← hcycW]
    exact ((torFormula k f hX (torSheaf X (structureSheafAt u) (structureSheafAt v) i)
      (structureSheafAt w)
      (isCoherent_torSheaf_of_isRegular X hX (structureSheafAt u) (structureSheafAt v)
        (isCoherent_structureSheafAt u) (isCoherent_structureSheafAt v) i)
      (isCoherent_structureSheafAt w)
      p t m dX hdX (by omega) (hsUV i) hsw (htR i)).2).symm

/-! ### The whole lemma, at every expected dimension

The statement above spells the three expected dimensions as natural numbers, which leaves out the
configurations in which one of them is negative, for instance three curves on a surface meeting
pairwise in points and with empty triple intersection. In such a configuration the triple
intersection `U ∩ V ∩ W` is empty, and both sides of the identity vanish. The registered form
below takes the expected dimensions as the integers `dim U + dim V - dim X`,
`dim V + dim W - dim X` and `dim U + dim V + dim W - 2 dim X` and covers every case. -/

/-- **A dimension bound bounds the relative dimension of every point.** If a closed subset `T` of
a scheme locally of finite type over a field satisfies `dim T + d ≤ N`, then every point of `T`
has relative dimension `δ` with `δ + d ≤ N`. -/
theorem relativeDimension_add_le_of_topologicalKrullDim_add_le (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {T : Set X} (hT : IsClosed T) {d N : ℕ}
    (h : topologicalKrullDim T + (d : WithBot ℕ∞) ≤ (N : WithBot ℕ∞)) {z : X} (hz : z ∈ T) :
    relativeDimension (fieldChowSituation k).dimensionFunction f z + d ≤ N := by
  have hnn := relativeDimension_nonneg (fieldChowSituation k) (fun _ _ => rfl) f z
  have hle : topologicalKrullDim (closure ({z} : Set X)) ≤ topologicalKrullDim T :=
    (Topology.IsEmbedding.inclusion
      (closure_minimal (Set.singleton_subset_iff.2 hz) hT)).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_closure_singleton_eq k f z] at hle
  have h3 : (relativeDimension (fieldChowSituation k).dimensionFunction f z).toNat + d ≤ N := by
    exact_mod_cast le_trans (add_le_add hle le_rfl) h
  omega

/-- If two points have closures of dimensions `r`, `s` meeting properly in `X` of dimension `dX`,
then `dim (closure {x} ∩ closure {y}) + dX ≤ r + s`. -/
private theorem topologicalKrullDim_inter_add_le_of_intersectProperly {x y : X} {dX r s : ℕ}
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hx : topologicalKrullDim (closure ({x} : Set X)) = (r : WithBot ℕ∞))
    (hy : topologicalKrullDim (closure ({y} : Set X)) = (s : WithBot ℕ∞))
    (hprop : AlgebraicGeometry.IntersectProperly
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩) :
    topologicalKrullDim (↥(closure ({x} : Set X) ∩ closure ({y} : Set X))) + (dX : WithBot ℕ∞) ≤
      ((r + s : ℕ) : WithBot ℕ∞) := by
  have hprop' : topologicalKrullDim (↥(closure ({x} : Set X) ∩ closure ({y} : Set X))) +
      topologicalKrullDim X ≤ topologicalKrullDim (closure ({x} : Set X)) +
        topologicalKrullDim (closure ({y} : Set X)) := hprop
  rw [hdX, hx, hy] at hprop'
  exact_mod_cast hprop'

/-- **The Section 43.14 product is legitimate at every expected dimension.** Let `x`, `y` be
points of a regular scheme over a field whose reduced closures, of dimensions `r` and `s`,
intersect properly in `X` of dimension `dX`. Then the `Tor` sheaves of their structure sheaves
satisfy the delta-dimension bound for the integer `r + s - dX`, which is what makes the product
`closure {x} · closure {y}` of Tag 0AZR an `(r + s - dX)`-cycle; when `r + s < dX` the two
closures are disjoint and the bound holds vacuously. -/
theorem torSupportBound_of_intersectProperly_of_eq (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X)
    (x y : X) {dX r s : ℕ} (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hx : topologicalKrullDim (closure ({x} : Set X)) = (r : WithBot ℕ∞))
    (hy : topologicalKrullDim (closure ({y} : Set X)) = (s : WithBot ℕ∞))
    (hprop : AlgebraicGeometry.IntersectProperly
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩) :
    TorSupportBound (fieldChowSituation k) f hX ((r : ℤ) + s - dX) x y := by
  have h := topologicalKrullDim_inter_add_le_of_intersectProperly hdX hx hy hprop
  intro i
  have := isCoherent_torSheaf_of_isRegular X hX (structureSheafAt x) (structureSheafAt y)
    (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) i
  refine schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f _ fun z hz => ?_
  have := relativeDimension_add_le_of_topologicalKrullDim_add_le k f
    (isClosed_closure.inter isClosed_closure) h (supp_torSheaf_structureSheafAt_subset x y i hz)
  push_cast at this
  linarith

/-- The Section 43.14 product only depends on the dimension index, not on the proof of the
delta-dimension bound for it. -/
theorem torSubvarietyProductOfBound_congr (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X) {k k' : ℤ} (hk : k = k')
    {x y : X} (h : TorSupportBound C f hX k x y) (h' : TorSupportBound C f hX k' x y) :
    torSubvarietyProductOfBound C f hX k h = torSubvarietyProductOfBound C f hX k' h' := by
  subst hk
  rfl

/-- **Two closed subvarieties of known dimensions inside a small set intersect properly.** If the
closed subvarieties `W`, `V` of dimensions `A`, `B` of a scheme of dimension `dX` satisfy
`dim (W ∩ V) + 2 dX ≤ A + B + dX`, they intersect properly. -/
theorem intersectProperly_of_topologicalKrullDim_inter_add_le (W V : IrreducibleCloseds X)
    {A B dX : ℕ} (hW : topologicalKrullDim (W : Set X) = (A : WithBot ℕ∞))
    (hV : topologicalKrullDim (V : Set X) = (B : WithBot ℕ∞))
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (h : topologicalKrullDim (↥((W : Set X) ∩ (V : Set X))) + ((dX + dX : ℕ) : WithBot ℕ∞) ≤
      ((A + B + dX : ℕ) : WithBot ℕ∞)) :
    AlgebraicGeometry.IntersectProperly W V := by
  rw [AlgebraicGeometry.intersectProperly_iff, hW, hV, hdX]
  set a := topologicalKrullDim (↥((W : Set X) ∩ (V : Set X))) with ha
  clear_value a
  rcases eq_or_ne a ⊥ with rfl | hbot
  · simp
  lift a to ℕ∞ using hbot with b
  have h' : b + ((dX + dX : ℕ) : ℕ∞) ≤ ((A + B + dX : ℕ) : ℕ∞) := by exact_mod_cast h
  have hb : b ≠ ⊤ := by
    rintro rfl
    simp at h'
  lift b to ℕ using hb
  have h'' : b + (dX + dX) ≤ A + B + dX := by exact_mod_cast h'
  have h3 : b + dX ≤ A + B := by omega
  exact_mod_cast h3

/-- A closed subvariety is the closure of its generic point. -/
theorem coe_irreducibleCloseds_eq_closure_genericPoint (W : IrreducibleCloseds X) :
    (W : Set X) = closure ({W.isIrreducible.genericPoint} : Set X) :=
  (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).def.symm

/-- **Cancelling a dimension.** If `a + d ≤ m + d` in `WithBot ℕ∞` for natural numbers `m`, `d`,
then `a ≤ m`. -/
theorem withBot_le_of_add_le_add {a : WithBot ℕ∞} {m d : ℕ}
    (h : a + (d : WithBot ℕ∞) ≤ ((m + d : ℕ) : WithBot ℕ∞)) : a ≤ (m : WithBot ℕ∞) := by
  rcases eq_or_ne a ⊥ with rfl | hbot
  · simp
  lift a to ℕ∞ using hbot with b
  have h' : b + (d : ℕ∞) ≤ (m : ℕ∞) + (d : ℕ∞) := by exact_mod_cast h
  exact_mod_cast (WithTop.add_le_add_iff_right (by exact_mod_cast ENat.natCast_ne_top d)).1 h'

/-- Over a field, a point whose relative dimension is `b - dX` has closure of dimension a natural
number `c` with `c + dX = b`. -/
theorem exists_topologicalKrullDim_closure_eq_of_relativeDimension_add_eq (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (z : X) {b dX : ℕ}
    (hz : relativeDimension (fieldChowSituation k).dimensionFunction f z + dX = b) :
    ∃ c : ℕ, topologicalKrullDim (closure ({z} : Set X)) = (c : WithBot ℕ∞) ∧ c + dX = b := by
  have hnn := relativeDimension_nonneg (fieldChowSituation k) (fun _ _ => rfl) f z
  refine ⟨(relativeDimension (fieldChowSituation k).dimensionFunction f z).toNat,
    topologicalKrullDim_closure_singleton_eq k f z, by omega⟩

/-- **The components of a Section 43.14 product.** A point carrying a nonzero coefficient in
`closure {x} · closure {y}`, formed in dimension `n`, lies on both closures and has relative
dimension `n`. -/
theorem mem_inter_and_relativeDimension_eq_of_torSubvarietyProductOfBound_ne_zero (k : Type u)
    [Field k] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) {dX : ℕ} (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞)) (n : ℤ)
    {x y : X} (h : TorSupportBound (fieldChowSituation k) f hX n x y) {z : X}
    (hz : torSubvarietyProductOfBound (fieldChowSituation k) f hX n h z ≠ 0) :
    z ∈ closure ({x} : Set X) ∩ closure ({y} : Set X) ∧
      relativeDimension (fieldChowSituation k).dimensionFunction f z = n := by
  refine ⟨?_, ?_⟩
  · by_contra hn
    exact hz (torSubvarietyProductOfBound_apply_eq_zero_of_notMem_inter (fieldChowSituation k)
      f hX n h dX hdX.le hn)
  · by_contra hn
    exact hz (torSubvarietyProductOfBound_apply_eq_zero_of_relativeDimension_ne
      (fieldChowSituation k) f hX n h dX hdX.le hn)

/-- **The closure of a component of a product lies in a closed set containing the point.** -/
theorem closure_singleton_subset_of_mem {S : Set X} (hS : IsClosed S) {z : X} (hz : z ∈ S) :
    closure ({z} : Set X) ⊆ S :=
  closure_minimal (Set.singleton_subset_iff.2 hz) hS

/-- **`U` and `V · W` intersect properly.** Let `U`, `V`, `W` be the reduced closures of three
points of a scheme of finite type over a field, of dimensions `r`, `s`, `t`, in `X` of dimension
`dX`, with `dim (U ∩ V ∩ W) + 2 dX ≤ r + s + t`. Then the prime cycle `[U]` and the product
`V · W` of Section 43.14 in dimension `s + t - dX` intersect properly. -/
theorem intersectProperly_single_torSubvarietyProductOfBound [DecidableEq X] (k : Type u)
    [Field k] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (u v w : X) {dX r s t : ℕ}
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hu : topologicalKrullDim (closure ({u} : Set X)) = (r : WithBot ℕ∞))
    (h : TorSupportBound (fieldChowSituation k) f hX ((s : ℤ) + t - dX) v w)
    (huvw : topologicalKrullDim
        (↥(closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X))) +
          ((dX + dX : ℕ) : WithBot ℕ∞) ≤ ((r + s + t : ℕ) : WithBot ℕ∞)) :
    AlgebraicCycle.IntersectProperly (Function.locallyFinsuppWithin.single u (1 : ℤ))
      (torSubvarietyProductOfBound (fieldChowSituation k) f hX ((s : ℤ) + t - dX) h) := by
  intro W' V' h1 h2
  have hW' : W'.isIrreducible.genericPoint = u := by
    by_contra hne
    exact h1 (by rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right hne])
  obtain ⟨hzVW, hzdim⟩ :=
    mem_inter_and_relativeDimension_eq_of_torSubvarietyProductOfBound_ne_zero k f hX hdX _ h h2
  obtain ⟨c, hc, hcb⟩ := exists_topologicalKrullDim_closure_eq_of_relativeDimension_add_eq k f
    V'.isIrreducible.genericPoint (b := s + t) (dX := dX) (by rw [hzdim]; push_cast; ring)
  have hWc := coe_irreducibleCloseds_eq_closure_genericPoint W'
  have hVc := coe_irreducibleCloseds_eq_closure_genericPoint V'
  rw [hW'] at hWc
  refine intersectProperly_of_topologicalKrullDim_inter_add_le W' V' (A := r) (B := c)
    (by rw [hWc]; exact hu) (by rw [hVc]; exact hc) hdX ?_
  have hsub : (W' : Set X) ∩ (V' : Set X) ⊆
      closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X) := by
    rw [hWc, hVc]
    rintro y ⟨hyu, hyz⟩
    have hy := closure_singleton_subset_of_mem (isClosed_closure.inter isClosed_closure) hzVW hyz
    exact ⟨⟨hyu, hy.1⟩, hy.2⟩
  have hNr : ((r + s + t : ℕ) : WithBot ℕ∞) = ((r + c + dX : ℕ) : WithBot ℕ∞) := by
    congr 1
    omega
  exact le_trans (add_le_add
    (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le le_rfl)
    (le_trans huvw (le_of_eq hNr))

/-- **`U · V` and `W` intersect properly.** The companion of
`intersectProperly_single_torSubvarietyProductOfBound` for the other bracketing. -/
theorem intersectProperly_torSubvarietyProductOfBound_single [DecidableEq X] (k : Type u)
    [Field k] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (u v w : X) {dX r s t : ℕ}
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hw : topologicalKrullDim (closure ({w} : Set X)) = (t : WithBot ℕ∞))
    (h : TorSupportBound (fieldChowSituation k) f hX ((r : ℤ) + s - dX) u v)
    (huvw : topologicalKrullDim
        (↥(closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X))) +
          ((dX + dX : ℕ) : WithBot ℕ∞) ≤ ((r + s + t : ℕ) : WithBot ℕ∞)) :
    AlgebraicCycle.IntersectProperly
      (torSubvarietyProductOfBound (fieldChowSituation k) f hX ((r : ℤ) + s - dX) h)
      (Function.locallyFinsuppWithin.single w (1 : ℤ)) := by
  intro W' V' h1 h2
  have hV' : V'.isIrreducible.genericPoint = w := by
    by_contra hne
    exact h2 (by rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right hne])
  obtain ⟨hzUV, hzdim⟩ :=
    mem_inter_and_relativeDimension_eq_of_torSubvarietyProductOfBound_ne_zero k f hX hdX _ h h1
  obtain ⟨c, hc, hcb⟩ := exists_topologicalKrullDim_closure_eq_of_relativeDimension_add_eq k f
    W'.isIrreducible.genericPoint (b := r + s) (dX := dX) (by rw [hzdim]; push_cast; ring)
  have hWc := coe_irreducibleCloseds_eq_closure_genericPoint W'
  have hVc := coe_irreducibleCloseds_eq_closure_genericPoint V'
  rw [hV'] at hVc
  refine intersectProperly_of_topologicalKrullDim_inter_add_le W' V' (A := c) (B := t)
    (by rw [hWc]; exact hc) (by rw [hVc]; exact hw) hdX ?_
  have hsub : (W' : Set X) ∩ (V' : Set X) ⊆
      closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X) := by
    rw [hWc, hVc]
    rintro y ⟨hyz, hyw⟩
    exact ⟨closure_singleton_subset_of_mem (isClosed_closure.inter isClosed_closure) hzUV hyz,
      hyw⟩
  have hNr : ((r + s + t : ℕ) : WithBot ℕ∞) = ((c + t + dX : ℕ) : WithBot ℕ∞) := by
    congr 1
    omega
  exact le_trans (add_le_add
    (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le le_rfl)
    (le_trans huvw (le_of_eq hNr))

/-- **A product of two closed subvarieties with disjoint closures vanishes.** -/
theorem torFormulaSubvarietyProductTotal_eq_zero_of_inter_eq_empty (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X)
    {dX : ℕ} (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞)) (n : ℤ) {a b : X}
    (hab : closure ({a} : Set X) ∩ closure ({b} : Set X) = ∅) :
    torFormulaSubvarietyProductTotal (fieldChowSituation k) f hX n a b = 0 := by
  refine Function.locallyFinsuppWithin.ext fun y => ?_
  refine torFormulaSubvarietyProductTotal_apply_eq_zero_of_notMem_inter (fieldChowSituation k)
    f hX n a b dX hdX.le fun hy => ?_
  rw [hab] at hy
  exact hy

/-- **With empty triple intersection, `U · (V · W)` vanishes.** If `U ∩ V ∩ W = ∅`, the product
of `[U]` with the Section 43.14 product `V · W` is zero in every dimension. -/
theorem torFormulaCycleIntersectionProduct_single_left_eq_zero [DecidableEq X] (k : Type u)
    [Field k] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (u v w : X) {dX : ℕ} (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (n m : ℤ) (h : TorSupportBound (fieldChowSituation k) f hX n v w)
    (hT : closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X) = ∅) :
    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX m
      (Function.locallyFinsuppWithin.single u 1)
      (torSubvarietyProductOfBound (fieldChowSituation k) f hX n h) = 0 := by
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct]
  refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
  rw [cycleIntersectionProductSummand]
  by_cases hq1 : q.1 = u
  swap
  · rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right hq1, zero_mul, zero_smul]
  by_cases hq : torSubvarietyProductOfBound (fieldChowSituation k) f hX n h q.2 = 0
  · rw [hq, mul_zero, zero_smul]
  have hz := (mem_inter_and_relativeDimension_eq_of_torSubvarietyProductOfBound_ne_zero k f hX
    hdX n h hq).1
  rw [torFormulaSubvarietyProductTotal_eq_zero_of_inter_eq_empty k f hX hdX m ?_, smul_zero]
  refine Set.eq_empty_of_subset_empty fun y hy => ?_
  rw [← hT]
  have hy2 := closure_singleton_subset_of_mem (isClosed_closure.inter isClosed_closure) hz hy.2
  rw [hq1] at hy
  exact ⟨⟨hy.1, hy2.1⟩, hy2.2⟩

/-- **With empty triple intersection, `(U · V) · W` vanishes.** -/
theorem torFormulaCycleIntersectionProduct_single_right_eq_zero [DecidableEq X] (k : Type u)
    [Field k] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (u v w : X) {dX : ℕ} (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (n m : ℤ) (h : TorSupportBound (fieldChowSituation k) f hX n u v)
    (hT : closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X) = ∅) :
    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX m
      (torSubvarietyProductOfBound (fieldChowSituation k) f hX n h)
      (Function.locallyFinsuppWithin.single w 1) = 0 := by
  rw [torFormulaCycleIntersectionProduct, cycleIntersectionProduct]
  refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
  rw [cycleIntersectionProductSummand]
  by_cases hq2 : q.2 = w
  swap
  · rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right hq2, mul_zero, zero_smul]
  by_cases hq : torSubvarietyProductOfBound (fieldChowSituation k) f hX n h q.1 = 0
  · rw [hq, zero_mul, zero_smul]
  have hz := (mem_inter_and_relativeDimension_eq_of_torSubvarietyProductOfBound_ne_zero k f hX
    hdX n h hq).1
  rw [torFormulaSubvarietyProductTotal_eq_zero_of_inter_eq_empty k f hX hdX m ?_, smul_zero]
  refine Set.eq_empty_of_subset_empty fun y hy => ?_
  rw [← hT]
  have hy1 := closure_singleton_subset_of_mem (isClosed_closure.inter isClosed_closure) hz hy.1
  rw [hq2] at hy
  exact ⟨hy1, hy.2⟩

/-- **Stacks Project, Tag 0B1L.** Let `X` be a nonsingular variety over an algebraically closed
field — the convention of the chapter, Tag 0AZ8 — of dimension `dX`, and let `U`, `V`, `W` be
closed subvarieties, namely the reduced closures of three points `u`, `v`, `w`, of dimensions
`r`, `s`, `t`. Assume `U`, `V`, `W` intersect properly pairwise and that

`dim (U ∩ V ∩ W) ≤ dim U + dim V + dim W - 2 dim X`.

Then `U` and `V · W` intersect properly, `U · V` and `W` intersect properly — so that the two
iterated products are defined, as the source's statement presupposes — and, as cycles on `X`,

`U · (V · W) = (U · V) · W`.

Here `V · W` and `U · V` are the products of Section 43.14 (Tag 0AZR) in dimensions
`s + t - dX` and `r + s - dX`, and the outer products are their bilinear extension of Tag 0B08 in
dimension `r + s + t - 2 dX`; the three expected dimensions are integers, so that the
configurations in which one of them is negative are included. -/
@[stacks 0B1L "the whole lemma: `U · (V · W) = (U · V) · W` as cycles on `X`, for three closed \
subvarieties of a nonsingular variety over an algebraically closed field — the chapter's own \
convention, Tag 0AZ8 — intersecting properly pairwise and satisfying the displayed dimension \
bound, together with the properness of the two outer intersections that the statement \
presupposes. Closed subvarieties are their generic points, so `U`, `V`, `W` are the reduced \
closures of three points and `[U]` is the prime cycle at `u`. The inner products `V · W` and \
`U · V` are the Section 43.14 product of Tag 0AZR in the integer expected dimensions \
`dim V + dim W - dim X` and `dim U + dim V - dim X`, and the outer products the bilinear \
extension of Tag 0B08 in dimension `dim U + dim V + dim W - 2 dim X`. `WithBot ℕ∞` has no \
subtraction, so the displayed bound is spelled \
`dim (U ∩ V ∩ W) + 2 dim X ≤ dim U + dim V + dim W`, as proper intersection is in Tag 0AZQ."]
theorem torFormulaCycleIntersectionProduct_assoc [DecidableEq X] (k : Type u) [Field k]
    [IsAlgClosed k] (f : X ⟶ Spec (.of k)) [IsVariety k f] (hX : IsRegular X)
    (u v w : X) (dX r s t : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hu : topologicalKrullDim (closure ({u} : Set X)) = (r : WithBot ℕ∞))
    (hv : topologicalKrullDim (closure ({v} : Set X)) = (s : WithBot ℕ∞))
    (hw : topologicalKrullDim (closure ({w} : Set X)) = (t : WithBot ℕ∞))
    (huv : AlgebraicGeometry.IntersectProperly
      ⟨closure {u}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (hvw : AlgebraicGeometry.IntersectProperly
      ⟨closure {v}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (_huw : AlgebraicGeometry.IntersectProperly
      ⟨closure {u}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (huvw : topologicalKrullDim
        (↥(closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X))) +
          ((2 * dX : ℕ) : WithBot ℕ∞) ≤ ((r + s + t : ℕ) : WithBot ℕ∞)) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    AlgebraicCycle.IntersectProperly (Function.locallyFinsuppWithin.single u (1 : ℤ))
        (torSubvarietyProductOfBound (fieldChowSituation k) f hX ((s : ℤ) + t - dX)
          (torSupportBound_of_intersectProperly_of_eq k f hX v w hdX hv hw hvw)) ∧
      AlgebraicCycle.IntersectProperly
        (torSubvarietyProductOfBound (fieldChowSituation k) f hX ((r : ℤ) + s - dX)
          (torSupportBound_of_intersectProperly_of_eq k f hX u v hdX hu hv huv))
        (Function.locallyFinsuppWithin.single w (1 : ℤ)) ∧
      torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + s + t - 2 * dX)
          (Function.locallyFinsuppWithin.single u 1)
          (torSubvarietyProductOfBound (fieldChowSituation k) f hX ((s : ℤ) + t - dX)
            (torSupportBound_of_intersectProperly_of_eq k f hX v w hdX hv hw hvw)) =
        torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + s + t - 2 * dX)
          (torSubvarietyProductOfBound (fieldChowSituation k) f hX ((r : ℤ) + s - dX)
            (torSupportBound_of_intersectProperly_of_eq k f hX u v hdX hu hv huv))
          (Function.locallyFinsuppWithin.single w 1) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have h2 : (2 * dX : ℕ) = dX + dX := by omega
  rw [h2] at huvw
  refine ⟨intersectProperly_single_torSubvarietyProductOfBound k f hX u v w hdX hu _ huvw,
    intersectProperly_torSubvarietyProductOfBound_single k f hX u v w hdX hw _ huvw, ?_⟩
  by_cases hne : (closure ({u} : Set X) ∩ closure ({v} : Set X) ∩ closure ({w} : Set X)).Nonempty
  swap
  · -- the triple intersection is empty, and both sides vanish
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [torFormulaCycleIntersectionProduct_single_left_eq_zero k f hX u v w hdX _ _ _ hne,
      torFormulaCycleIntersectionProduct_single_right_eq_zero k f hX u v w hdX _ _ _ hne]
  -- the triple intersection is nonempty, so the three expected dimensions are natural numbers
  obtain ⟨z, hz⟩ := hne
  have hδ := relativeDimension_nonneg (fieldChowSituation k) (fun _ _ => rfl) f z
  have hT' := relativeDimension_add_le_of_topologicalKrullDim_add_le k f
    ((isClosed_closure.inter isClosed_closure).inter isClosed_closure) huvw hz
  have hUV' := topologicalKrullDim_inter_add_le_of_intersectProperly hdX hu hv huv
  have hVW' := topologicalKrullDim_inter_add_le_of_intersectProperly hdX hv hw hvw
  have hp' := relativeDimension_add_le_of_topologicalKrullDim_add_le k f
    (isClosed_closure.inter isClosed_closure) hUV' hz.1
  have hq' := relativeDimension_add_le_of_topologicalKrullDim_add_le k f
    (isClosed_closure.inter isClosed_closure) hVW' ⟨hz.1.2, hz.2⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ, r + s = dX + p := ⟨r + s - dX, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, s + t = dX + q := ⟨s + t - dX, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, r + s + t = 2 * dX + m := ⟨r + s + t - 2 * dX, by omega⟩
  have e1 : ((r : ℤ) + s - dX) = (p : ℤ) := by omega
  have e2 : ((s : ℤ) + t - dX) = (q : ℤ) := by omega
  have e3 : ((r : ℤ) + s + t - 2 * dX) = (m : ℤ) := by omega
  have hmd : ((r + s + t : ℕ) : WithBot ℕ∞) = ((m + (dX + dX) : ℕ) : WithBot ℕ∞) := by
    congr 1
    omega
  have hTm := withBot_le_of_add_le_add (le_trans huvw (le_of_eq hmd))
  rw [torSubvarietyProductOfBound_congr (fieldChowSituation k) f hX e1 _
      (torSupportBound_of_intersectProperly k f hX u v hdX
        (by rw [hu, hv, ← Nat.cast_add, ← Nat.cast_add, hp]) huv),
    torSubvarietyProductOfBound_congr (fieldChowSituation k) f hX e2 _
      (torSupportBound_of_intersectProperly k f hX v w hdX
        (by rw [hv, hw, ← Nat.cast_add, ← Nat.cast_add, hq]) hvw), e3]
  exact torFormulaCycleIntersectionProduct_assoc_of_closures k f hX u v w dX r s t p q m
    hdX hu hv hw huv hvw _huw hp hq hm hTm

end Stacks.Intersection.ReductionToDiagonal

end
