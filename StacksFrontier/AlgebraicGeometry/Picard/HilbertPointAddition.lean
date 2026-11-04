module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorDegreeDifference
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorZariskiGluing
public import StacksFrontier.AlgebraicGeometry.Picard.PointIdeal
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# Adding a point to a family of divisors on a smooth relative curve

Let `X ⟶ S` be smooth of relative dimension one and let `H` and `H'` represent the Hilbert
functors of points `Hilb^d_{X/S}` and `Hilb^{d+1}_{X/S}`. *Point addition* is the morphism
`H ×_S X ⟶ H'` of `S`-schemes which sends a pair `(D, x)`, consisting of a degree-`d` family
`D ⊆ X ×_S T` and a relative point `x : T ⟶ X`, to the family `D + x`, cut out by the product of
the ideal of `D` with the ideal of the graph of `x`. This file proves that point addition is
finite locally free of degree `d + 1`.

The proof is the one of the source. The universal degree-`(d+1)` family `D_univ ⊆ X ×_S H'` is
finite locally free of degree `d + 1` over `H'` by construction, so it suffices to factor point
addition as an isomorphism `H ×_S X ≅ D_univ` followed by the structure morphism of `D_univ`.
That isomorphism is checked on points: a `T`-point of `D_univ` is a degree-`(d+1)` family `D` on
`X ×_S T` together with a relative point `x` whose graph factors through `D`, and subtracting the
graph of `x` from `D` — which is possible, with a degree-`d` remainder, by Stacks Tag 0B9F —
inverts point addition.

## Main definitions

* `Stacks.Hilbert.IsPointAddition` — the characterising property of the point-addition morphism:
  on every family it multiplies the ideal by the ideal of the graph of the point.
* `Stacks.Hilbert.familyAddPoint` — the degree-`(d+1)` family obtained from a degree-`d` family
  by adding the graph of a relative point.
* `Stacks.Hilbert.addPoint` — the point-addition morphism itself, for a separated `X ⟶ S`.

## Main results

* `Stacks.Hilbert.IsPointAddition.isFiniteLocallyFreeOfRank_left` — **Stacks Tag 0B9G**: point
  addition is finite locally free of degree `d + 1`.
* `Stacks.Hilbert.IsPointAddition.exists_iso_universalFamily_subscheme` — point addition
  identifies `H ×_S X` with the universal divisor `D_univ ⊆ X ×_S H'` as schemes (used in
  Stacks Tag 0B9J).
* `Stacks.Hilbert.isPointAddition_addPoint` — `addPoint` is a point-addition morphism, so the
  hypothesis of the previous statement is satisfiable.
* `Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor` — one may cancel an effective
  Cartier divisor from a sum of divisors.

## Implementation notes

*How "the morphism" is named.* The source speaks of "the morphism
`Hilb^d_{X/S} ×_S X ⟶ Hilb^{d+1}_{X/S}`". Here the subject is any morphism `f` of `S`-schemes
satisfying `Stacks.Hilbert.IsPointAddition`, the equation that pins it down: for every family
classified by `g : T ⟶ H ×_S X` the family classified by `g ≫ f` has ideal the product of the
ideal of the first component with the point ideal of the second. Two such morphisms agree, since
`H'` represents the degree-`(d+1)` functor and a family is determined by its ideal sheaf; so the
hypothesis names the source's morphism and nothing else. The degree statement is proved for all
of them at once, with no hypothesis on `X ⟶ S` beyond smoothness of relative dimension one.

*Why the construction, and only the construction, assumes `X ⟶ S` separated.* Adding the graph
of a point to a family presupposes that the graph is a closed subscheme. For a `T`-point lying
on a family this is automatic: the graph then factors through a scheme that is finite locally
free, hence separated, over `T`, and a section of a separated morphism is a closed immersion.
But to *construct* point addition one must add the graph of the universal point
`H ×_S X ⟶ X` to the universal degree-`d` family, and that graph is the base change of the
diagonal of `X ⟶ S`; whenever `H` has an `X`-valued point — for instance always when `d = 0`,
where `Hilb^0_{X/S}` is `S` — its being a closed immersion forces `X ⟶ S` to be separated.
Smoothness of relative dimension one does not supply this. So
`Stacks.Hilbert.addPoint` carries `AlgebraicGeometry.IsSeparated`, while the degree statement
tagged with 0B9G does not.

*Divisors are ideal sheaves.* A closed subscheme is presented by its quasi-coherent sheaf of
ideals, `AlgebraicGeometry.Scheme.IdealSheafData`, and the sum of two divisors is the product of
their ideals. The ideal of the graph of a relative point is
`Stacks.Hilbert.pointIdeal`, the kernel ideal sheaf of `Stacks.Hilbert.pointGraph`.

## References

* [Stacks Project, Tag 0B9G](https://stacks.math.columbia.edu/tag/0B9G)
* [Stacks Project, Tag 0B9F](https://stacks.math.columbia.edu/tag/0B9F)
* [Stacks Project, Tag 0B9E](https://stacks.math.columbia.edu/tag/0B9E)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Divisors

/-- Cancelling a nonzerodivisor from a product of ideals: if `r` is left regular then
`(r) * I = (r) * J` forces `I = J`. -/
private theorem eq_of_span_singleton_mul_eq_span_singleton_mul {R : Type*} [CommSemiring R]
    {r : R} (hr : IsLeftRegular r) {I J : Ideal R}
    (h : Ideal.span {r} * I = Ideal.span {r} * J) : I = J := by
  rw [le_antisymm_iff] at h
  rw [le_antisymm_iff]
  rw [Ideal.span_singleton_mul_le_span_singleton_mul,
    Ideal.span_singleton_mul_le_span_singleton_mul] at h
  constructor
  · intro a ha
    obtain ⟨b, hb, hab⟩ := h.1 a ha
    exact hr hab ▸ hb
  · intro a ha
    obtain ⟨b, hb, hab⟩ := h.2 a ha
    exact hr hab ▸ hb

/-- **An effective Cartier divisor can be cancelled from a sum.** If `K` is an effective Cartier
divisor and `K + I = K + J` as divisors, in the ideal-sheaf presentation `K * I = K * J`, then
`I = J`.

Locally on an affine open `K` is cut out by a single nonzerodivisor, and multiplication by the
ideal it generates is injective on ideals. -/
theorem eq_of_mul_eq_mul_of_isEffectiveCartierDivisor {Y : Scheme.{u}} {K I J : Y.IdealSheafData}
    (hK : IsEffectiveCartierDivisor K) (h : K * I = K * J) : I = J := by
  choose U hU hyU r hr hKr using
    exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor K hK
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun y : Y => ⟨U y, hU y⟩)
    (eq_top_iff.2 fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hyU z⟩) fun y => ?_
  refine eq_of_span_singleton_mul_eq_span_singleton_mul (hr y).left ?_
  have hy := congrArg (fun L : Y.IdealSheafData => L.ideal ⟨U y, hU y⟩) h
  simpa only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hKr y] using hy

end Stacks.Divisors

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-! ### The graph of a relative point and its ideal -/

/-- The graph of a relative point `x : T ⟶ X` has `x` as its first component. -/
@[simp]
theorem pointGraph_comp_fst (X T : Over S) (x : T ⟶ X) :
    pointGraph X T x ≫ pullback.fst X.hom T.hom = x.left :=
  pullback.lift_fst _ _ _

/-- The graph of a relative point is a section of the base-change projection, in the reassociated
form needed to rewrite underneath a composition. -/
@[simp]
theorem pointGraph_comp_snd_assoc {W : Scheme.{u}} (X T : Over S) (x : T ⟶ X)
    (h : T.left ⟶ W) : pointGraph X T x ≫ pullback.snd X.hom T.hom ≫ h = h := by
  rw [← Category.assoc, pointGraph_comp_snd, Category.id_comp]

/-- The graph of a relative point is a section of the structure morphism of `X ×_S T`. -/
theorem pointGraph_comp_hom (X T : Over S) (x : T ⟶ X) :
    pointGraph X T x ≫ ((Over.pullback T.hom).obj X).hom = 𝟙 T.left :=
  pointGraph_comp_snd X T x

/-- The base-change comparison map `X ×_S T' ⟶ X ×_S T` is the identity on the `X`-component. -/
@[simp]
alias familyBaseChangeMap_comp_fst := familyBaseChangeMap_fst

/-- The base-change comparison map `X ×_S T' ⟶ X ×_S T` is `g` on the base component. -/
@[simp]
alias familyBaseChangeMap_comp_snd := familyBaseChangeMap_snd

/-- The base-change comparison map, expressed with the structure morphisms of the slice. -/
theorem familyBaseChangeMap_comp_hom (X : Over S) {T' T : Over S} (g : T' ⟶ T) :
    familyBaseChangeMap X g ≫ ((Over.pullback T.hom).obj X).hom =
      ((Over.pullback T'.hom).obj X).hom ≫ g.left :=
  familyBaseChangeMap_comp_snd X g

/-- The graph of a relative point is compatible with base change. -/
theorem pointGraph_comp_familyBaseChangeMap (X : Over S) {T' T : Over S} (g : T' ⟶ T)
    (x : T ⟶ X) :
    pointGraph X T' (g ≫ x) ≫ familyBaseChangeMap X g = g.left ≫ pointGraph X T x := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, familyBaseChangeMap_comp_fst, pointGraph_comp_fst, Category.assoc,
      pointGraph_comp_fst, Over.comp_left]
  · rw [Category.assoc, familyBaseChangeMap_comp_snd, ← Category.assoc, pointGraph_comp_snd,
      Category.id_comp, Category.assoc, pointGraph_comp_snd, Category.comp_id]

/-- The graph of a relative point exhibits the base `T'` as the fibre product of the graph over
`T` with the base-change comparison map: the comparison morphism is an isomorphism. -/
theorem isIso_pullback_lift_pointGraph (X : Over S) {T' T : Over S} (g : T' ⟶ T) (x : T ⟶ X) :
    IsIso (pullback.lift (pointGraph X T' (g ≫ x)) g.left
      (pointGraph_comp_familyBaseChangeMap X g x)) := by
  have hcond : pullback.fst (familyBaseChangeMap X g) (pointGraph X T x) ≫
        familyBaseChangeMap X g =
      pullback.snd (familyBaseChangeMap X g) (pointGraph X T x) ≫ pointGraph X T x :=
    pullback.condition
  -- the first projection, followed by the structure morphism, inverts the comparison map
  have hrg : pullback.fst (familyBaseChangeMap X g) (pointGraph X T x) ≫
        pullback.snd X.hom T'.hom ≫ g.left =
      pullback.snd (familyBaseChangeMap X g) (pointGraph X T x) := by
    simpa only [Category.assoc, familyBaseChangeMap_comp_snd, pointGraph_comp_snd,
      Category.comp_id] using congrArg (fun m => m ≫ pullback.snd X.hom T.hom) hcond
  have hfx : pullback.snd (familyBaseChangeMap X g) (pointGraph X T x) ≫ x.left =
      pullback.fst (familyBaseChangeMap X g) (pointGraph X T x) ≫
        pullback.fst X.hom T'.hom := by
    simpa only [Category.assoc, familyBaseChangeMap_comp_fst, pointGraph_comp_fst] using
      (congrArg (fun m => m ≫ pullback.fst X.hom T.hom) hcond).symm
  refine ⟨pullback.fst (familyBaseChangeMap X g) (pointGraph X T x) ≫
      pullback.snd X.hom T'.hom, ?_, ?_⟩
  · rw [← Category.assoc, pullback.lift_fst, pointGraph_comp_snd]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      refine pullback.hom_ext ?_ ?_
      · simpa only [Category.assoc, pointGraph_comp_fst, Over.comp_left] using
          (congrArg (fun m => m ≫ x.left) hrg).trans hfx
      · rw [Category.assoc, pointGraph_comp_snd, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      simpa only [Category.assoc] using hrg

/-- **The point ideal is compatible with base change.** When the graph of `x : T ⟶ X` is a closed
immersion, the inverse image of its ideal along the base-change comparison map is the ideal of
the graph of the base-changed point. -/
theorem pointIdeal_comap_familyBaseChangeMap (X : Over S) {T' T : Over S} (g : T' ⟶ T)
    (x : T ⟶ X) [IsClosedImmersion (pointGraph X T x)] :
    (pointIdeal X T x).comap (familyBaseChangeMap X g) = pointIdeal X T' (g ≫ x) := by
  have := isIso_pullback_lift_pointGraph X g x
  rw [pointIdeal, pointIdeal, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
      (pointGraph X T x) (familyBaseChangeMap X g),
    ← Scheme.Hom.ker_comp_of_isIso (pullback.lift (pointGraph X T' (g ≫ x)) g.left
      (pointGraph_comp_familyBaseChangeMap X g x)) (pullback.fst _ _),
    pullback.lift_fst]

/-- The closed subscheme cut out by the point ideal is the base: its structure morphism is an
isomorphism, because the graph of the point is a closed immersion and a section. -/
theorem isIso_subschemeι_pointIdeal_comp (X T : Over S) (x : T ⟶ X)
    [IsClosedImmersion (pointGraph X T x)] :
    IsIso ((pointIdeal X T x).subschemeι ≫ ((Over.pullback T.hom).obj X).hom) := by
  -- the graph factors through the closed subscheme it cuts out, by an isomorphism
  have hle : (pointIdeal X T x).subschemeι.ker ≤ (pointGraph X T x).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, pointIdeal]
  obtain ⟨a, hfac⟩ : ∃ a : T.left ⟶ (pointIdeal X T x).subscheme,
      a ≫ (pointIdeal X T x).subschemeι = pointGraph X T x :=
    ⟨IsClosedImmersion.lift (pointIdeal X T x).subschemeι (pointGraph X T x) hle,
      IsClosedImmersion.lift_fac _ _ hle⟩
  have hiso : IsIso a :=
    IsClosedImmersion.isIso_of_ker_eq (pointGraph X T x) (pointIdeal X T x).subschemeι a hfac
      ((pointIdeal X T x).ker_subschemeι).symm
  have hcomp : IsIso (a ≫ (pointIdeal X T x).subschemeι ≫
      ((Over.pullback T.hom).obj X).hom) := by
    rw [← Category.assoc, hfac, pointGraph_comp_hom]
    infer_instance
  exact IsIso.of_isIso_comp_left a _

/-- **The graph of a relative point is a degree-one divisor.** When the graph of `x : T ⟶ X` is a
closed immersion, the closed subscheme of `X ×_S T` it cuts out is finite locally free of
degree one over `T`. -/
theorem isFiniteLocallyFreeOfRank_pointIdeal (X T : Over S) (x : T ⟶ X)
    [IsClosedImmersion (pointGraph X T x)] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((pointIdeal X T x).subschemeι ≫ ((Over.pullback T.hom).obj X).hom) 1 :=
  have := isIso_subschemeι_pointIdeal_comp X T x
  Stacks.Morphisms.isFiniteLocallyFreeOfRank_one_of_isIso _

/-- A section of a separated morphism is a closed immersion. -/
private theorem isClosedImmersion_of_comp_eq_id_of_isSeparated {A B : Scheme.{u}} (p : B ⟶ A)
    [IsSeparated p] (s : A ⟶ B) (h : s ≫ p = 𝟙 A) : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ p) := by rw [h]; infer_instance
  exact IsClosedImmersion.of_comp s p

/-- **A relative point lying on a family has a closed graph.** If the graph of `x : T ⟶ X`
factors through a Hilbert family, it is a closed immersion: the factoring morphism is a section
of a finite locally free, hence separated, morphism. -/
theorem isClosedImmersion_pointGraph_of_factors {X T : Over S} {n : ℕ}
    (D : HilbertFamily X T n) (x : T ⟶ X) (a : T.left ⟶ D.ideal.subscheme)
    (ha : a ≫ D.ideal.subschemeι = pointGraph X T x) :
    IsClosedImmersion (pointGraph X T x) := by
  have hrank := D.isFiniteLocallyFreeOfRank
  have haff : IsAffineHom (D.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) :=
    hrank.toIsAffineHom
  have hsep : IsSeparated (D.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) :=
    IsSeparated.of_isAffineHom _
  have := isClosedImmersion_of_comp_eq_id_of_isSeparated
    (D.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) a
    (by rw [← Category.assoc, ha, pointGraph_comp_hom])
  rw [← ha]
  infer_instance

/-- **A relative point contained in a family has a closed graph.** If the ideal of a Hilbert
family is contained in the point ideal of `x`, that is, if the graph of `x` is a closed subscheme
of the family, then the graph of `x` is a closed immersion. -/
theorem isClosedImmersion_pointGraph_of_le {X T : Over S} {n : ℕ} (D : HilbertFamily X T n)
    (x : T ⟶ X) (h : D.ideal ≤ pointIdeal X T x) :
    IsClosedImmersion (pointGraph X T x) :=
  isClosedImmersion_pointGraph_of_factors D x
    (IsClosedImmersion.lift D.ideal.subschemeι (pointGraph X T x)
      (by rwa [D.ideal.ker_subschemeι])) (IsClosedImmersion.lift_fac _ _ _)

/-! ### Adding a point to a family -/

/-- **The sum of a degree-`d` family and the graph of a relative point.** On a smooth relative
curve it is a degree-`(d+1)` family, by additivity of the degree of a sum of divisors
(Stacks Tag 0B9E). -/
def familyAddPoint (X T : Over S) [SmoothOfRelativeDimension 1 X.hom] {d : ℕ}
    (D : HilbertFamily X T d) (x : T ⟶ X)
    (hx : IsClosedImmersion (pointGraph X T x)) : HilbertFamily X T (d + 1) where
  ideal := D.ideal * pointIdeal X T x
  isFiniteLocallyFreeOfRank :=
    have := hx
    have := D.isFiniteLocallyFreeOfRank
    have := isFiniteLocallyFreeOfRank_pointIdeal X T x
    have : SmoothOfRelativeDimension 1 ((Over.pullback T.hom).obj X).hom :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback X.hom T.hom) inferInstance
    isFiniteLocallyFreeOfRank_mul ((Over.pullback T.hom).obj X).hom D.ideal
      (pointIdeal X T x) d 1

@[simp]
theorem familyAddPoint_ideal (X T : Over S) [SmoothOfRelativeDimension 1 X.hom] {d : ℕ}
    (D : HilbertFamily X T d) (x : T ⟶ X) (hx : IsClosedImmersion (pointGraph X T x)) :
    (familyAddPoint X T D x hx).ideal = D.ideal * pointIdeal X T x :=
  rfl

/-- The base change `X ×_S T ⟶ T` of a smooth relative curve is again smooth of relative
dimension one. -/
private theorem smoothOfRelativeDimension_one_pullback_hom (X T : Over S)
    [SmoothOfRelativeDimension 1 X.hom] :
    SmoothOfRelativeDimension 1 ((Over.pullback T.hom).obj X).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback X.hom T.hom) inferInstance

/-- **Subtracting a relative point from a family.** On a smooth relative curve, a
degree-`(d+1)` family containing the graph of a relative point `x` is the sum of a degree-`d`
family and the graph of `x`. This is Stacks Tag 0B9F applied to the pair of divisors. -/
theorem exists_familyAddPoint_eq {X T : Over S} [SmoothOfRelativeDimension 1 X.hom] {d : ℕ}
    (D : HilbertFamily X T (d + 1)) (x : T ⟶ X) (h : D.ideal ≤ pointIdeal X T x) :
    ∃ D' : HilbertFamily X T d, D.ideal = D'.ideal * pointIdeal X T x := by
  have hx := isClosedImmersion_pointGraph_of_le D x h
  have := isFiniteLocallyFreeOfRank_pointIdeal X T x
  have := D.isFiniteLocallyFreeOfRank
  have := smoothOfRelativeDimension_one_pullback_hom X T
  obtain ⟨E, hE, hrank⟩ := exists_isFiniteLocallyFreeOfRank_sub_mul_eq_of_le
    ((Over.pullback T.hom).obj X).hom (pointIdeal X T x) D.ideal 1 (d + 1) h
  rw [Nat.add_sub_cancel] at hrank
  exact ⟨⟨E, hrank⟩, hE.trans (mul_comm _ _)⟩

/-! ### Point addition between representing Hilbert schemes -/

/-- **The characterising property of point addition.** A morphism `f : H ×_S X ⟶ H'` of
`S`-schemes, where `H` represents `Hilb^d_{X/S}` and `H'` represents `Hilb^{d+1}_{X/S}`, *is
point addition* when on every family it adds the graph of the point: the family classified by
`g ≫ f` is cut out by the product of the ideal of the family classified by the first component of
`g` with the point ideal of the second component of `g`. -/
def IsPointAddition {X H H' : Over S} {d : ℕ} (hH : RepresentsHilbertFunctorOfRank X H d)
    (hH' : RepresentsHilbertFunctorOfRank X H' (d + 1)) (f : H ⨯ X ⟶ H') : Prop :=
  ∀ (T : Over S) (g : T ⟶ H ⨯ X),
    (hH'.family (g ≫ f)).ideal =
      (hH.family (g ≫ prod.fst)).ideal * pointIdeal X T (g ≫ prod.snd)

namespace IsPointAddition

variable {X H H' : Over S} [SmoothOfRelativeDimension 1 X.hom] {d : ℕ}
  {hH : RepresentsHilbertFunctorOfRank X H d}
  {hH' : RepresentsHilbertFunctorOfRank X H' (d + 1)} {f : H ⨯ X ⟶ H'}

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- The family classified by `g ≫ f` contains the graph of the point component of `g`. -/
theorem family_ideal_le (hf : IsPointAddition hH hH' f) (T : Over S) (g : T ⟶ H ⨯ X) :
    (hH'.family (g ≫ f)).ideal ≤ pointIdeal X T (g ≫ prod.snd) := by
  rw [hf T g]
  exact fun _ => Ideal.mul_le_right

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- The graph of the point component of any `T`-point of `H ×_S X` is a closed immersion: it is
contained in the family obtained by adding it. -/
theorem isClosedImmersion_pointGraph (hf : IsPointAddition hH hH' f) (T : Over S)
    (g : T ⟶ H ⨯ X) : IsClosedImmersion (pointGraph X T (g ≫ prod.snd)) :=
  isClosedImmersion_pointGraph_of_le (hH'.family (g ≫ f)) _ (hf.family_ideal_le T g)

/-- **Point addition is injective on points.** Two `T`-points of `H ×_S X` with the same image
under point addition and the same point component are equal: the family component is recovered by
cancelling the graph of the point from the sum. -/
theorem eq_of_comp_eq (hf : IsPointAddition hH hH' f) {T : Over S} (g g' : T ⟶ H ⨯ X)
    (ha : g ≫ f = g' ≫ f) (hx : g ≫ prod.snd = g' ≫ prod.snd) : g = g' := by
  have hci := hf.isClosedImmersion_pointGraph T g
  have := isFiniteLocallyFreeOfRank_pointIdeal X T (g ≫ prod.snd)
  have hfl : Stacks.Morphisms.IsFiniteLocallyFree
      ((pointIdeal X T (g ≫ prod.snd)).subschemeι ≫ ((Over.pullback T.hom).obj X).hom) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  have := smoothOfRelativeDimension_one_pullback_hom X T
  have hK : Stacks.Divisors.IsEffectiveCartierDivisor (pointIdeal X T (g ≫ prod.snd)) :=
    (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree
      ((Over.pullback T.hom).obj X).hom (pointIdeal X T (g ≫ prod.snd))).1
  refine prod.hom_ext ?_ hx
  refine hH.family.injective (HilbertFamily.ext ?_)
  refine Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor hK ?_
  have he := congrArg (fun t => (hH'.family t).ideal) ha
  rw [hf T g, hf T g', ← hx] at he
  simpa only [mul_comm] using he

end IsPointAddition

/-- The universal degree-`(d+1)` family on a representing scheme. -/
private def universalFamily {X H' : Over S} {d : ℕ}
    (hH' : RepresentsHilbertFunctorOfRank X H' (d + 1)) : HilbertFamily X H' (d + 1) :=
  hH'.family (𝟙 H')

namespace IsPointAddition

variable {X H H' : Over S} [SmoothOfRelativeDimension 1 X.hom] {d : ℕ}
  {hH : RepresentsHilbertFunctorOfRank X H d}
  {hH' : RepresentsHilbertFunctorOfRank X H' (d + 1)} {f : H ⨯ X ⟶ H'}

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- The ideal of the family classified by `t : T ⟶ H'` is the inverse image of the ideal of the
universal family. -/
private theorem family_ideal_eq_comap {T : Over S}
    (hH' : RepresentsHilbertFunctorOfRank X H' (d + 1)) (t : T ⟶ H') :
    (hH'.family t).ideal =
      (universalFamily hH').ideal.comap (familyBaseChangeMap X t) := by
  have h := hH'.naturality t (𝟙 H')
  rw [Category.comp_id] at h
  exact h

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- A morphism into `X ×_S H'` whose composite with the base-change comparison map lands in a
family is bounded by the universal ideal. -/
private theorem universal_ideal_le_ker {T : Over S}
    (hH' : RepresentsHilbertFunctorOfRank X H' (d + 1)) (t : T ⟶ H') (x : T ⟶ X)
    (h : (hH'.family t).ideal ≤ pointIdeal X T x) :
    (universalFamily hH').ideal ≤
      (pointGraph X T x ≫ familyBaseChangeMap X t).ker := by
  rw [← Scheme.IdealSheafData.map_ker]
  refine Scheme.IdealSheafData.le_map_iff_comap_le.mpr ?_
  rw [← family_ideal_eq_comap hH' t]
  exact h

/-- **The incidence morphism.** Point addition lifts to the universal degree-`(d+1)` family: the
graph of the universal point, pushed into `X ×_S H'` along point addition, factors through the
universal family. -/
private def incidence (hf : IsPointAddition hH hH' f) :
    (H ⨯ X).left ⟶ (universalFamily hH').ideal.subscheme :=
  IsClosedImmersion.lift (universalFamily hH').ideal.subschemeι
    (pointGraph X (H ⨯ X) prod.snd ≫ familyBaseChangeMap X f)
    (by
      rw [(universalFamily hH').ideal.ker_subschemeι]
      refine universal_ideal_le_ker hH' f prod.snd ?_
      simpa only [Category.id_comp] using hf.family_ideal_le (H ⨯ X) (𝟙 _))

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- The incidence morphism, composed with the inclusion of the universal family, is the graph of
the universal point pushed along point addition. -/
private theorem incidence_comp_subschemeι (hf : IsPointAddition hH hH' f) :
    hf.incidence ≫ (universalFamily hH').ideal.subschemeι =
      pointGraph X (H ⨯ X) prod.snd ≫ familyBaseChangeMap X f :=
  IsClosedImmersion.lift_fac _ _ _

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- The incidence morphism followed by the structure morphism of the universal family is point
addition. This is the factorisation that computes the degree. -/
private theorem incidence_comp_hom (hf : IsPointAddition hH hH' f) :
    hf.incidence ≫ (universalFamily hH').ideal.subschemeι ≫
        ((Over.pullback H'.hom).obj X).hom = f.left := by
  rw [← Category.assoc, hf.incidence_comp_subschemeι, Category.assoc,
    familyBaseChangeMap_comp_hom, ← Category.assoc, pointGraph_comp_hom, Category.id_comp]

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- The incidence morphism followed by the `X`-component of the universal family is the point
component. -/
private theorem incidence_comp_fst (hf : IsPointAddition hH hH' f) :
    hf.incidence ≫ (universalFamily hH').ideal.subschemeι ≫
        pullback.fst X.hom H'.hom = (prod.snd : H ⨯ X ⟶ X).left := by
  rw [← Category.assoc, hf.incidence_comp_subschemeι, Category.assoc,
    familyBaseChangeMap_comp_fst, pointGraph_comp_fst]

/-- **Point addition is surjective on points, with a prescribed point component.** A
degree-`(d+1)` family together with a relative point contained in it comes from a unique
`T`-point of `H ×_S X`. -/
private theorem exists_comp_eq (hf : IsPointAddition hH hH' f) {T : Over S} (t : T ⟶ H')
    (x : T ⟶ X) (h : (hH'.family t).ideal ≤ pointIdeal X T x) :
    ∃ g : T ⟶ H ⨯ X, g ≫ f = t ∧ g ≫ prod.snd = x := by
  obtain ⟨D', hD'⟩ := exists_familyAddPoint_eq (hH'.family t) x h
  refine ⟨prod.lift (hH.family.symm D') x, ?_, prod.lift_snd _ _⟩
  refine hH'.family.injective (HilbertFamily.ext ?_)
  rw [hf T (prod.lift (hH.family.symm D') x), prod.lift_fst, prod.lift_snd,
    Equiv.apply_symm_apply]
  exact hD'.symm

/-- **Points of the universal family come from `H ×_S X`, over a fixed base.** If `v` lands in
the universal degree-`(d+1)` family and exhibits, through the inclusion, the graph of the
relative point `x` inside the family classified by `t`, then `v` is the image under the incidence
morphism of a point of `H ×_S X`. -/
private theorem exists_comp_incidence_eq_of (hf : IsPointAddition hH hH' f) {T : Over S}
    (t : T ⟶ H') (x : T ⟶ X) (v : T.left ⟶ (universalFamily hH').ideal.subscheme)
    (hv : v ≫ (universalFamily hH').ideal.subschemeι =
      pointGraph X T x ≫ familyBaseChangeMap X t) :
    ∃ g : T ⟶ H ⨯ X, g.left ≫ hf.incidence = v := by
  have hle : (hH'.family t).ideal ≤ pointIdeal X T x := by
    rw [family_ideal_eq_comap hH' t, pointIdeal]
    refine Scheme.IdealSheafData.le_map_iff_comap_le.mp ?_
    rw [Scheme.IdealSheafData.map_ker, ← hv]
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using
      Scheme.Hom.le_ker_comp v (universalFamily hH').ideal.subschemeι
  obtain ⟨g, hgt, hgx⟩ := hf.exists_comp_eq t x hle
  refine ⟨g, (cancel_mono (universalFamily hH').ideal.subschemeι).mp ?_⟩
  rw [Category.assoc, hf.incidence_comp_subschemeι, hv]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, familyBaseChangeMap_comp_fst, pointGraph_comp_fst]
    rw [← Over.comp_left, hgx]
  · simp only [Category.assoc, familyBaseChangeMap_comp_snd, pointGraph_comp_snd_assoc]
    rw [← Over.comp_left, hgt]

/-- Every `T`-point of the universal family is the image of a point of `H ×_S X` under the
incidence morphism. The scheme `T` is made a scheme over `S` through the point of `H'` that the
universal family carries. -/
private theorem exists_comp_incidence_eq (hf : IsPointAddition hH hH' f) (T : Scheme.{u})
    (v : T ⟶ (universalFamily hH').ideal.subscheme) :
    ∃ g : T ⟶ (H ⨯ X).left, g ≫ hf.incidence = v := by
  obtain ⟨g, hg⟩ := hf.exists_comp_incidence_eq_of
    (T := Over.mk (v ≫ (universalFamily hH').ideal.subschemeι ≫
      pullback.snd X.hom H'.hom ≫ H'.hom))
    (Over.homMk (v ≫ (universalFamily hH').ideal.subschemeι ≫ pullback.snd X.hom H'.hom)
      (by simp only [Over.mk_hom, Category.assoc]))
    (Over.homMk (v ≫ (universalFamily hH').ideal.subschemeι ≫ pullback.fst X.hom H'.hom)
      (by simp only [Over.mk_hom, Category.assoc, pullback.condition]))
    v (by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, familyBaseChangeMap_comp_fst, pointGraph_comp_fst,
          Over.homMk_left]
      · simp only [Category.assoc, familyBaseChangeMap_comp_snd, pointGraph_comp_snd_assoc,
          Over.homMk_left])
  exact ⟨g.left, hg⟩

/-- The incidence morphism is a monomorphism: a `T`-point of `H ×_S X` is determined by its
image under point addition together with its point component. -/
private theorem mono_incidence (hf : IsPointAddition hH hH' f) : Mono hf.incidence := by
  constructor
  intro T u u' h
  have ha : u ≫ f.left = u' ≫ f.left := by
    have := congrArg (fun m => m ≫ (universalFamily hH').ideal.subschemeι ≫
      ((Over.pullback H'.hom).obj X).hom) h
    simpa only [Category.assoc, hf.incidence_comp_hom] using this
  have hxl : u ≫ (prod.snd : H ⨯ X ⟶ X).left = u' ≫ (prod.snd : H ⨯ X ⟶ X).left := by
    have := congrArg (fun m => m ≫ (universalFamily hH').ideal.subschemeι ≫
      pullback.fst X.hom H'.hom) h
    simpa only [Category.assoc, hf.incidence_comp_fst] using this
  have hb : u' ≫ (H ⨯ X).hom = u ≫ (H ⨯ X).hom := by
    have hw : f.left ≫ H'.hom = (H ⨯ X).hom := Over.w f
    rw [← hw, ← Category.assoc, ← Category.assoc, ha]
  exact congrArg Over.Hom.left
    (hf.eq_of_comp_eq (T := Over.mk (u ≫ (H ⨯ X).hom))
      (Over.homMk u (by simp only [Over.mk_hom]))
      (Over.homMk u' (by simp only [Over.mk_hom]; exact hb))
      (Over.OverMorphism.ext (by simpa only [Over.comp_left, Over.homMk_left] using ha))
      (Over.OverMorphism.ext (by simpa only [Over.comp_left, Over.homMk_left] using hxl)))

/-- The incidence morphism `H ×_S X ⟶ D_univ` is an isomorphism: it is a monomorphism, and it is
surjective on `T`-points for every scheme `T`. -/
private theorem isIso_incidence (hf : IsPointAddition hH hH' f) : IsIso hf.incidence := by
  have := hf.mono_incidence
  refine isIso_of_yoneda_map_bijective _ fun T => ⟨fun u u' h => ?_, ?_⟩
  · exact (cancel_mono hf.incidence).mp h
  · exact hf.exists_comp_incidence_eq T

/-- **Stacks Project, Tag 0B9G.** Let `X ⟶ S` be smooth of relative dimension one and suppose
the Hilbert functors `Hilb^d_{X/S}` are representable, say by `H` in degree `d` and by `H'` in
degree `d + 1`. The point-addition morphism `H ×_S X ⟶ H'` is finite locally free of degree
`d + 1`.

It factors as the incidence isomorphism `H ×_S X ≅ D_univ` onto the universal degree-`(d+1)`
family followed by the structure morphism of `D_univ`, which is finite locally free of degree
`d + 1` because `D_univ` is a degree-`(d+1)` family. The incidence morphism is an isomorphism
because it is bijective on points: surjectivity is the subtraction of a point from a family
(Stacks Tag 0B9F) and injectivity is the cancellation of the graph of the point from the sum. -/
@[stacks 0B9G]
theorem isFiniteLocallyFreeOfRank_left (hf : IsPointAddition hH hH' f) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank f.left (d + 1) := by
  have hπ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((universalFamily hH').ideal.subschemeι ≫ ((Over.pullback H'.hom).obj X).hom) (d + 1) :=
    (universalFamily hH').isFiniteLocallyFreeOfRank
  have := hf.isIso_incidence
  have := Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp (asIso hf.incidence)
    ((universalFamily hH').ideal.subschemeι ≫ ((Over.pullback H'.hom).obj X).hom) hπ
  rwa [asIso_hom, hf.incidence_comp_hom] at this

/-- **The universal divisor is `H ×_S X`** (the identification in the proof of Stacks Tag 0B9G,
quoted in Stacks Tag 0B9J). Point addition identifies `H ×_S X` with the universal
degree-`(d+1)` family `D_univ ⊆ X ×_S H'`, as schemes: there is an isomorphism
`H ×_S X ≅ D_univ` which, followed by the inclusion of `D_univ` into `X ×_S H'`, is the morphism
`(D, x) ↦ (x, D + x)` — its `X`-component is the point and its `H'`-component is point
addition. -/
theorem exists_iso_universalFamily_subscheme (hf : IsPointAddition hH hH' f) :
    ∃ e : (H ⨯ X).left ≅ (hH'.family (𝟙 H')).ideal.subscheme,
      e.hom ≫ (hH'.family (𝟙 H')).ideal.subschemeι ≫ pullback.fst X.hom H'.hom =
          (prod.snd : H ⨯ X ⟶ X).left ∧
        e.hom ≫ (hH'.family (𝟙 H')).ideal.subschemeι ≫ ((Over.pullback H'.hom).obj X).hom =
          f.left := by
  exact ⟨@asIso _ _ _ _ hf.incidence hf.isIso_incidence, hf.incidence_comp_fst,
    hf.incidence_comp_hom⟩

end IsPointAddition

/-! ### Construction of point addition for a separated relative curve -/

variable {X H H' : Over S} [SmoothOfRelativeDimension 1 X.hom] {d : ℕ}

/-- For a separated `X ⟶ S` the graph of any relative point is a closed immersion: it is a
section of the base change of `X ⟶ S`, which is again separated. -/
theorem isClosedImmersion_pointGraph_of_isSeparated (X T : Over S) [IsSeparated X.hom]
    (x : T ⟶ X) : IsClosedImmersion (pointGraph X T x) := by
  -- instance search cannot see through `Over.pullback`, so the instance is pinned by hand
  have hsep : IsSeparated ((Over.pullback T.hom).obj X).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X.hom T.hom))
  exact isClosedImmersion_of_comp_eq_id_of_isSeparated ((Over.pullback T.hom).obj X).hom _
    (pointGraph_comp_hom X T x)

/-- **Point addition.** For a separated smooth relative curve `X ⟶ S`, the morphism
`H ×_S X ⟶ H'` classifying the sum of the universal degree-`d` family and the graph of the
universal point. -/
def addPoint [IsSeparated X.hom] (hH : RepresentsHilbertFunctorOfRank X H d)
    (hH' : RepresentsHilbertFunctorOfRank X H' (d + 1)) : H ⨯ X ⟶ H' :=
  hH'.family.symm (familyAddPoint X (H ⨯ X) (hH.family prod.fst) prod.snd
    (isClosedImmersion_pointGraph_of_isSeparated X (H ⨯ X) prod.snd))

/-- **`addPoint` is point addition.** In particular the hypothesis of
`Stacks.Hilbert.IsPointAddition.isFiniteLocallyFreeOfRank_left` is satisfiable. -/
theorem isPointAddition_addPoint [IsSeparated X.hom]
    (hH : RepresentsHilbertFunctorOfRank X H d)
    (hH' : RepresentsHilbertFunctorOfRank X H' (d + 1)) :
    IsPointAddition hH hH' (addPoint hH hH') := by
  intro T g
  have hci := isClosedImmersion_pointGraph_of_isSeparated X (H ⨯ X) (prod.snd : H ⨯ X ⟶ X)
  rw [hH'.naturality g (addPoint hH hH'), addPoint, Equiv.apply_symm_apply,
    familyAddPoint_ideal, Stacks.IdealSheaf.comap_mul,
    pointIdeal_comap_familyBaseChangeMap X g prod.snd, hH.naturality g prod.fst]

end Stacks.Hilbert

end
