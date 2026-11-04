module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FiniteLocallyFreePushPull
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCondition2

/-!
# Stacks 0EPE for the unranked definition of finite local freeness

Let `f : X ⟶ Y` be a finite locally free morphism of algebraic spaces over a scheme `S`.
**Stacks 0EPE** asserts three things: `f` is proper, `f` is flat of relative dimension `0`, and
`f_*f^*α = dα` on `Z_k(Y)` when `f` has degree `d`.
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FiniteLocallyFreePushPull` proves the three for the
degree-`d` definition of Stacks 03ZV.  This file restates the first two, and the third, for the
unranked definition `AlgebraicGeometry.Space.IsFiniteLocallyFree`: neither properness nor
flatness of relative dimension `0` uses the rank, and in the third clause the degree enters only
through the hypothesis `hdeg`.

## Main results

* `AlgebraicGeometry.Space.isFinite_and_isFlat_of_isFiniteLocallyFree`: a finite locally free
  morphism is finite, flat and locally of finite presentation, which is Stacks 0416 for the
  definition of Stacks 03ZV.
* `AlgebraicGeometry.Space.isProper_of_isFiniteLocallyFree`: **Stacks 0EPE**, that `f` is
  proper, for an arbitrary morphism of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_zero_of_isFiniteLocallyFree`:
  **Stacks 0EPE**, that `f` is flat of relative dimension `0`, likewise.
* `AlgebraicGeometry.Space.properPushforward_flatCyclePullback_of_isFiniteLocallyFree`:
  **Stacks 0EPE**, the identity `f_*f^*α = dα` on `Z_k(Y)`.

## Implementation notes

**No clause here carries a chart comparison as a hypothesis, and neither does the ranked file.**
The comparison of the direct-image reading of finite local freeness with the representable one is
Stacks 03ZU, `AlgebraicGeometry.Space.presheaf_iff_isFiniteLocallyFree`, proved in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableChart`, and its form with the
representability hypothesis discharged from the affineness conjunct of Stacks 03ZV is
`AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree` — Stacks 03ZW,
conditions (1) and (2).  The rank is not needed to cross between the two readings, so the three
clauses are stated for the unranked definition of Stacks 03ZV, and Stacks 0416 is applied to it
directly.  For the third clause, finite local freeness enters only through quasi-compactness,
which is all the proper pushforward of Stacks 0EP1 asks for, so the degree `d` is pinned by the
hypothesis `hdeg` alone.

## References

* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 0416](https://stacks.math.columbia.edu/tag/0416)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EPE](https://stacks.math.columbia.edu/tag/0EPE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-! ### Stacks 0EPE: properness and flatness of relative dimension zero -/

section QuasiFinite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A finite locally free morphism of algebraic spaces over `S`, in the unranked sense of
Stacks 03ZV, is finite, flat and locally of finite presentation.

The direct-image definition of Stacks 03ZV passes to the representable reading of Stacks 03ZW by
`AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree` — Stacks 03ZU with
its representability hypothesis discharged from the affineness conjunct — and there the
equivalence with finite, flat and locally of finite presentation is Stacks 0416. -/
theorem isFinite_and_isFlat_of_isFiniteLocallyFree {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFiniteLocallyFree B S hS f) :
    IsFinite B S hS f.hom ∧ IsFlat B S hS f.hom ∧
      IsLocallyOfFinitePresentation B S hS f.hom :=
  (isFiniteLocallyFree_presheaf_iff B S hS X.property Y.property f.hom).1
    ((isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS f).2 hf)

/-- **Stacks 0EPE, first conclusion.** A finite locally free morphism of algebraic spaces over
`S` is proper.

A finite locally free morphism is finite by Stacks 0416, and a finite morphism is proper by
Stacks 04NZ. Neither the rank nor the goodness hypotheses of Situation 0EDT are used, so the
conclusion is drawn for the unranked definition of Stacks 03ZV and an arbitrary morphism of
algebraic spaces over `S`. -/
@[stacks 0EPE "f is proper"]
theorem isProper_of_isFiniteLocallyFree {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFiniteLocallyFree B S hS f) :
    IsProper B S hS f.hom :=
  ((isFinite_iff_isAffineHom_and_isProper B S hS X.property Y.property f.hom).1
    (isFinite_and_isFlat_of_isFiniteLocallyFree B S hS f hf).1).2

/-- A finite locally free morphism is quasi-compact: it is proper, and a proper morphism is of
finite type. -/
theorem isQuasiCompact_of_isFiniteLocallyFree {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFiniteLocallyFree B S hS f) :
    IsQuasiCompact B S hS f.hom :=
  (isProper_of_isFiniteLocallyFree B S hS f hf).2.1.2

/-- **Stacks 0EPE, second conclusion.** A finite locally free morphism of algebraic spaces
over `S` is flat of relative dimension `0`: it is flat and locally of finite type, and has
relative dimension `0` at every point of its source.

Flatness is Stacks 0416. For the relative dimension, the morphism is finite, hence locally
quasi-finite and locally of finite type, and Stacks 04NV turns local quasi-finiteness into the
vanishing of the relative dimension at every point. Neither the rank nor the goodness hypotheses
of Situation 0EDT are used. -/
@[stacks 0EPE "f is flat of relative dimension 0"]
theorem isFlat_and_hasRelativeDimension_zero_of_isFiniteLocallyFree
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFiniteLocallyFree B S hS f) :
    IsFlat B S hS f.hom ∧ IsLocallyOfFiniteType B S hS f.hom ∧
      HasRelativeDimension 0 B S hS f.hom := by
  obtain ⟨hfin, hflat, -⟩ := isFinite_and_isFlat_of_isFiniteLocallyFree B S hS f hf
  have hlft : IsLocallyOfFiniteType B S hS f.hom :=
    isLocallyOfFiniteType_of_isFinite B S hS X.property Y.property hfin
  exact ⟨hflat, hlft, (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS
    f.hom hlft).1 (isLocallyQuasiFinite_of_isFinite B S hS X.property Y.property hfin)⟩

end QuasiFinite

/-! ### Stacks 0EPE: pushforward after pullback is multiplication by the degree -/

section Formula

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : AlgebraicSpaces D.site D.base D.base_mem}

/-- **Stacks 0EPE, third conclusion.** In Situation 0EDT let `X/B` and `Y/B` be good and let
`f : X ⟶ Y` be finite locally free, with `hdeg` recording the degree `d` of its fibre over the
generic point of every integral closed subspace of δ-dimension `k`. Then `f_*f^*α = dα` for
every `α ∈ Z_k(Y)`.

Only the term of the flat pullback at `W'` itself survives in the coefficient of `f_*f^*α` at
an integral closed subspace `W' ⊆ Y`, by
`AlgebraicGeometry.Space.eq_cycleImageSubspace_of_mult_ne_zero`, and what is left is `α_{W'}`
times the degree `hdeg` of the fibre over the generic point of `W'`; at a `W'` of δ-dimension
other than `k` the coefficient of `α` there vanishes and both sides are zero.

Finite local freeness enters only through quasi-compactness, which is all the proper pushforward
of Stacks 0EP1 asks for, so the rank of Stacks 03ZV is not imposed on `f`: the degree `d` is
pinned by `hdeg` alone. -/
@[stacks 0EPE "f_* f^* alpha = d alpha"]
theorem properPushforward_flatCyclePullback_of_isFiniteLocallyFree
    (sX : X.obj ⟶ D.space) (hX : D.IsGood sX) (sY : Y.obj ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f.hom ≫ sY = sX) (d : ℕ)
    (hf : IsFiniteLocallyFree D.site D.base D.base_mem f)
    (pb : FlatCyclePullback D sX hX sY hY f.hom 0)
    (k : ℤ)
    (hdeg : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y.obj,
      deltaDimension D sY W = k →
      ∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
          cycleImageSubspace D sY hY f.hom T = W},
        pb.mult W T * (cycleResidueDegree D sX hX sY hY f.hom
          (T.ambientGenericPoint D.site D.base D.base_mem) : ℤ) = (d : ℤ))
    (α : CycleGroup D sY k) :
    properPushforward D sX hX sY hY hbase
        (isQuasiCompact_of_isFiniteLocallyFree D.site D.base D.base_mem f hf) k
        (pb.map k k (by simp) α) = (d : ℤ) • α := by
  have h0 : k + ((0 : ℕ) : ℤ) = k := by simp
  refine Subtype.ext (funext fun W' => ?_)
  -- where the multiplicity does not vanish, the weight of Stacks 0EP0 is the residue degree
  have hweq : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem X.obj,
      cycleImageSubspace D sY hY f.hom T = W' →
      pb.mult W' T * properPushforwardWeight D sX hX sY hY f.hom T =
        pb.mult W' T * (cycleResidueDegree D sX hX sY hY f.hom
          (T.ambientGenericPoint D.site D.base D.base_mem) : ℤ) := by
    intro T hT
    by_cases hmult : pb.mult W' T = 0
    · rw [hmult, zero_mul, zero_mul]
    · refine congrArg _ (properPushforwardWeight_eq_cycleResidueDegree D sX hX sY hY f.hom ?_)
      rw [hT]
      simpa using (pb.deltaDimension_eq_of_mult_ne_zero W' T hmult).symm
  -- only the term of the flat pullback at `W'` itself contributes
  have hterm : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem X.obj,
      cycleImageSubspace D sY hY f.hom T = W' →
      (pb.map k k h0 α).1 T * properPushforwardWeight D sX hX sY hY f.hom T =
        α.1 W' * (pb.mult W' T * properPushforwardWeight D sX hX sY hY f.hom T) := by
    intro T hT
    by_cases hweight : properPushforwardWeight D sX hX sY hY f.hom T = 0
    · rw [hweight, mul_zero, mul_zero, mul_zero]
    · have hsingle : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y.obj, W ≠ W' →
          α.1 W * pb.mult W T = 0 := by
        intro W hW
        by_cases hmult : pb.mult W T = 0
        · rw [hmult, mul_zero]
        · exact absurd ((eq_cycleImageSubspace_of_mult_ne_zero D sX hX sY hY f pb T hweight
            W hmult).symm.trans hT) hW
      rw [pb.coeff k k h0 α T, finsum_eq_single _ W' hsingle, mul_assoc]
  calc _
      = ∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
          cycleImageSubspace D sY hY f.hom T = W'},
          α.1 W' * (pb.mult W' T * properPushforwardWeight D sX hX sY hY f.hom T) :=
        finsum_mem_congr rfl hterm
    _ = α.1 W' * ∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
          cycleImageSubspace D sY hY f.hom T = W'},
          pb.mult W' T * properPushforwardWeight D sX hX sY hY f.hom T :=
        (mul_finsum_mem _ _).symm
    _ = ((d : ℤ) • α).1 W' := by
        rw [AddSubgroup.coe_zsmul, Pi.smul_apply, zsmul_eq_mul]
        by_cases hk : deltaDimension D sY W' = k
        · have hsum : (∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
              cycleImageSubspace D sY hY f.hom T = W'},
              pb.mult W' T * properPushforwardWeight D sX hX sY hY f.hom T) = (d : ℤ) :=
            (finsum_mem_congr rfl hweq).trans (hdeg W' hk)
          rw [hsum, mul_comm]
          norm_cast
        · have hαW' : α.1 W' = 0 := by
            by_contra hne
            exact hk (α.2.2 W' hne)
          rw [hαW', zero_mul, mul_zero]

end Formula

end AlgebraicGeometry.Space

end
