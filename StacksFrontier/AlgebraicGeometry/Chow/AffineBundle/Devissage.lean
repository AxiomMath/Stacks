module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence

/-!
# The devissage of Stacks 02TT

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be an
affine-space bundle of rank `r` between schemes locally of finite type over `S`. The proof of
Stacks 02TT reduces the surjectivity of `f^* : A_k(Y) ⟶ A_{k+r}(X)` to a statement about a
single integral closed subscheme `W ⊆ X` lying over the generic point of an integral base. This
file carries out that reduction.

The reduction is organised around the prime cycle `[x]` of a point `x ∈ X` of delta-dimension
`k + r`. Call `x` *good* (`Stacks.Chow.IsGoodPoint`) when `[x]` is rationally equivalent to a flat
pullback `f^*β` of a `k`-cycle `β` supported on the closure of `f x`, through a rational
equivalence witnessed inside `f⁻¹(closure {f x})`. The three steps are:

* **summation** (`Stacks.Chow.exists_isRationallyEquivalentToZero_sub_flatPullback`): if every
  point in the support of a `(k + r)`-cycle `α` is good and `f` is quasi-compact, then `α` is
  rationally equivalent to a flat pullback. The cycles `β` attached to the components of `α` are
  supported on the closures of their images, which form a locally finite family because `f` is
  quasi-compact, and the rational equivalences are summed by Stacks 02RZ;
* **localization** (`Stacks.Chow.hasGenericDecomposition_of_isOpenImmersion_square`): the
  statement that `[x]` is rationally equivalent to `f^*β` up to a cycle carried by points not
  lying over `f x` (`Stacks.Chow.HasGenericDecomposition`) may be checked after restricting to
  an open subscheme of the base containing `f x`, by Stacks 02RC and the localization sequence
  Stacks 02RX;
* **induction** (`Stacks.Chow.isGoodPoint_of_hasGenericDecomposition`): if the decomposition
  holds for every affine-space bundle over an integral base at every point over the generic
  point, then every point of every affine-space bundle is good. The base is replaced by the
  closure `Z` of `f x`, the decomposition on `f⁻¹(Z)` produces a cycle carried by points over
  `Z` minus its generic point, and those points are good by induction on the delta-dimension of
  their images.

## Main definitions

* `Stacks.Chow.pointCycle` — the prime cycle `[x]` of a point of delta-dimension `k`.
* `Stacks.Chow.IsGoodPoint` — `[x]` is rationally equivalent, inside `f⁻¹(closure {f x})`, to the
  flat pullback of a cycle supported on `closure {f x}`.
* `Stacks.Chow.HasGenericDecomposition` — `[x] - f^*β - γ` is rationally equivalent to zero for
  a cycle `γ` carried by points not lying over `f x`.

## Main results

* `Stacks.Chow.exists_isRationallyEquivalentToZero_sub_flatPullback` — summation.
* `Stacks.Chow.hasGenericDecomposition_of_isOpenImmersion_square` — localization.
* `Stacks.Chow.isGoodPoint_of_hasGenericDecomposition` — induction.
* `Stacks.Chow.flatPullbackChow_surjective_of_hasGenericDecomposition` — **Stacks 02TT**, granted
  the generic decomposition over integral bases.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RC](https://stacks.math.columbia.edu/tag/02RC)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Prime cycles of points -/

section PointCycle

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

open Classical in
/-- The prime cycle `[x]` of a point `x` of delta-dimension `k`: coefficient one at `x` and zero
elsewhere. -/
def pointCycle (k : ℤ) (x : X) (hx : relativeDimension C.dimensionFunction sX x = k) :
    CycleGroup C sX k :=
  ⟨Function.locallyFinsuppWithin.single x 1, by
    rw [mem_cyclesOfDimension_iff_forall_point]
    intro y hy
    by_cases h : y = x
    · rw [h, hx]
    · simp [h] at hy⟩

open Classical in
/-- The coefficient of the prime cycle of `x` is one at `x` and zero elsewhere. -/
theorem pointCycle_apply (k : ℤ) (x : X) (hx : relativeDimension C.dimensionFunction sX x = k)
    (y : X) : (pointCycle C sX k x hx).1 y = if y = x then 1 else 0 := by
  simp [pointCycle]

/-- A cycle is the locally finite sum of the prime cycles of the points of its support, weighted
by its coefficients. -/
theorem cycle_eq_finsum_pointCycle (k : ℤ) (α : CycleGroup C sX k) (y : X) :
    α.1 y = ∑ᶠ t : {t : X // α.1 t ≠ 0}, α.1 t.1 *
      (pointCycle C sX k t.1 ((mem_cyclesOfDimension_iff_forall_point C sX k α.1).mp α.2 _
        t.2)).1 y := by
  by_cases hy : α.1 y = 0
  · rw [hy]
    refine (finsum_eq_zero_of_forall_eq_zero fun t ↦ ?_).symm
    rw [pointCycle_apply]
    split_ifs with h
    · exact absurd (h ▸ hy) t.2
    · simp
  · rw [finsum_eq_single _ (⟨y, hy⟩ : {t : X // α.1 t ≠ 0})]
    · simp [pointCycle_apply]
    · intro t ht
      rw [pointCycle_apply, if_neg]
      · simp
      · intro h
        exact ht (Subtype.ext h.symm)

/-- Restriction along an open immersion carries the prime cycle of a point of the open subscheme
to the prime cycle of its preimage. -/
theorem cycleGroupRestrict_pointCycle {U : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
    (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ) (x : U)
    (hx : relativeDimension C.dimensionFunction sX (j.base x) = k)
    (hx' : relativeDimension C.dimensionFunction sU x = k) :
    cycleGroupRestrict C sX sU j hj k (pointCycle C sX k (j.base x) hx) =
      pointCycle C sU k x hx' := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [cycleGroupRestrict_apply, pointCycle_apply, pointCycle_apply]
  by_cases h : y = x
  · subst h; simp
  · rw [if_neg h, if_neg fun h' ↦ h (j.isOpenEmbedding.injective h')]

/-- Proper pushforward along a closed immersion carries the prime cycle of a point to the prime
cycle of its image. -/
theorem properPushforward_pointCycle {Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (k : ℤ) (z : Z)
    (hz : relativeDimension C.dimensionFunction sZ z = k)
    (hz' : relativeDimension C.dimensionFunction sX (i.base z) = k) :
    properPushforward C sZ sX i hi k (pointCycle C sZ k z hz) =
      pointCycle C sX k (i.base z) hz' := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  by_cases hy : y ∈ Set.range i.base
  · obtain ⟨y, rfl⟩ := hy
    rw [properPushforward_apply_image_of_isClosedImmersion, pointCycle_apply, pointCycle_apply]
    by_cases h : y = z
    · subst h; simp
    · rw [if_neg h, if_neg fun h' ↦ h (i.isClosedEmbedding.injective h')]
  · rw [properPushforward_apply_of_notMem_range C sZ sX i hi k _ hy, pointCycle_apply, if_neg]
    rintro rfl
    exact hy ⟨z, rfl⟩

end PointCycle

/-! ### Rational equivalence within a carrier -/

section Within

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {k : ℤ} {T : Set X}

/-- Rational equivalence to zero within a carrier is preserved by negation: the same family of
integral closed subschemes witnesses it, with the inverse rational functions. -/
theorem IsRationallyEquivalentToZeroWithin.neg {α : CycleGroup C sX k}
    (h : IsRationallyEquivalentToZeroWithin C sX k α T) :
    IsRationallyEquivalentToZeroWithin C sX k (-α) T := by
  obtain ⟨J, W, hW, hDim, hLocal, hsub, g, hg⟩ := h
  refine ⟨J, W, hW, hDim, hLocal, hsub, fun j ↦ (g j)⁻¹, fun x ↦ ?_⟩
  show -α.1 x = principalDivisorFamilyCoefficient C sX W hW (fun j ↦ (g j)⁻¹) x
  rw [hg x, principalDivisorFamilyCoefficient, ← finsum_neg_distrib]
  refine finsum_congr fun j ↦ ?_
  rw [principalDivisorPushforward_inv]
  rfl

/-- Rational equivalence to zero within a carrier is preserved by addition: the two witnessing
families are concatenated. -/
theorem IsRationallyEquivalentToZeroWithin.add {α β : CycleGroup C sX k}
    (hα : IsRationallyEquivalentToZeroWithin C sX k α T)
    (hβ : IsRationallyEquivalentToZeroWithin C sX k β T) :
    IsRationallyEquivalentToZeroWithin C sX k (α + β) T := by
  have h := rationallyEquivalentToZeroWithin_finsum C sX k
    (fun b : ULift.{u} Bool ↦ if b.down then α else β) (fun _ ↦ T)
    (locallyFinite_of_finite _) (fun b ↦ by
      by_cases hb : b.down
      · simpa [hb] using hα
      · simpa [hb] using hβ) (α := α + β) (fun x ↦ ?_)
  · exact h.mono (by simp)
  · rw [finsum_eq_sum_of_fintype]
    show α.1 x + β.1 x = _
    rw [show (Finset.univ : Finset (ULift.{u} Bool)) = {⟨true⟩, ⟨false⟩} by
      ext ⟨_ | _⟩ <;> simp, Finset.sum_pair (by simp)]
    simp

/-- Rational equivalence to zero within a carrier is preserved by integer multiples. -/
theorem IsRationallyEquivalentToZeroWithin.zsmul {α : CycleGroup C sX k}
    (h : IsRationallyEquivalentToZeroWithin C sX k α T) (n : ℤ) :
    IsRationallyEquivalentToZeroWithin C sX k (n • α) T := by
  induction n using Int.induction_on with
  | zero => simpa using isRationallyEquivalentToZeroWithin_zero C sX k T
  | succ n ih =>
    rw [add_smul, one_smul]
    exact ih.add h
  | pred n ih =>
    rw [sub_smul, one_smul, sub_eq_add_neg]
    exact ih.add h.neg

end Within

/-! ### Good points and the summation step -/

section Summation

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
  (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)

/-- A point `x` of `X` of delta-dimension `k + r` is **good** for `f` when its prime cycle `[x]`
is rationally equivalent to the flat pullback `f^*β` of a `k`-cycle `β` supported on the closure
of `f x`, through a rational equivalence witnessed inside `f⁻¹(closure {f x})`. -/
def IsGoodPoint (x : X) : Prop :=
  ∃ hx : relativeDimension C.dimensionFunction sX x = k + (r : ℤ),
    ∃ β : CycleGroup C sY k, (∀ y, β.1 y ≠ 0 → y ∈ closure {f.base x}) ∧
      IsRationallyEquivalentToZeroWithin C sX (k + (r : ℤ))
        (pointCycle C sX (k + (r : ℤ)) x hx - flatPullback C sX sY f hbase r hf k β)
        (f.base ⁻¹' closure {f.base x})

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f] [Flat f] in
/-- For `f` quasi-compact, the closures of the images of the points of a locally finite set form
a locally finite family: a quasi-compact open neighbourhood `V` of a point of `Y` meets the
closure of `f x` only if `f x ∈ V`, and `f⁻¹(V)` is quasi-compact, so it contains only finitely
many points of a locally finite set. -/
theorem locallyFinite_closure_image_of_locallyFiniteSupport [QuasiCompact f] (c : X → ℤ)
    (hc : LocallyFiniteSupport c) :
    LocallyFinite fun t : {t : X // c t ≠ 0} ↦ closure ({f.base t.1} : Set Y) := by
  intro y
  obtain ⟨V, hV, hyV⟩ : ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V := by
    obtain ⟨-, ⟨W, hW, rfl⟩, hyW, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨W, hW, hyW⟩
  refine ⟨V, V.isOpen.mem_nhds hyV, ?_⟩
  have hfin := hc.finite_inter_support_of_isCompact (f.isCompact_preimage hV.isCompact)
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  rintro t ⟨z, hz, hzV⟩
  exact ⟨(specializes_iff_mem_closure.mpr hz).mem_open V.isOpen hzV, t.2⟩

/-- **The summation step of Stacks 02TT.** If `f` is quasi-compact and every point of the support
of a `(k + r)`-cycle `α` on `X` is good, then `α` is rationally equivalent to the flat pullback
of a `k`-cycle on `Y`.

The good points supply cycles `β_x` supported on the closures of the `f x`; these form a locally
finite family by `Stacks.Chow.locallyFinite_closure_image_of_locallyFiniteSupport`, so
`β = ∑ α(x) β_x` is a cycle. The difference `α - f^*β` is then the locally finite sum of the
`α(x) ([x] - f^*β_x)`, each rationally equivalent to zero inside `f⁻¹(closure {f x})`, and those
carriers form a locally finite family; Stacks 02RZ sums the rational equivalences. -/
theorem exists_isRationallyEquivalentToZero_sub_flatPullback [QuasiCompact f]
    (α : CycleGroup C sX (k + (r : ℤ)))
    (hgood : ∀ x, α.1 x ≠ 0 → IsGoodPoint C sX sY f hbase r hf k x) :
    ∃ β : CycleGroup C sY k, IsRationallyEquivalentToZero C sX (k + (r : ℤ))
      (α - flatPullback C sX sY f hbase r hf k β) := by
  classical
  set J := {t : X // α.1 t ≠ 0}
  choose hx β hβsupp hβ using fun j : J ↦ hgood j.1 j.2
  set F : J → Set Y := fun j ↦ closure {f.base j.1}
  have hFloc : LocallyFinite F :=
    locallyFinite_closure_image_of_locallyFiniteSupport f α.1 α.1.locallyFiniteSupport
  have hsupp : ∀ j, Function.support (fun y ↦ α.1 j.1 * (β j).1 y) ⊆ F j :=
    fun j y hy ↦ hβsupp j y (right_ne_zero_of_mul hy)
  have hloc := locallyFiniteSupport_finsum_of_locallyFinite F hFloc
    (fun j y ↦ α.1 j.1 * (β j).1 y) hsupp (fun j z ↦ by
      obtain ⟨t, ht, hfin⟩ := (β j).1.locallyFiniteSupport z
      exact ⟨t, ht, hfin.subset fun y hy ↦ ⟨hy.1, right_ne_zero_of_mul hy.2⟩⟩)
  let B : AlgebraicCycle Y ℤ :=
    ⟨fun y ↦ ∑ᶠ j, α.1 j.1 * (β j).1 y, by simp, fun z _ ↦ hloc z⟩
  have hBmem : B ∈ cyclesOfDimension C sY k := by
    rw [mem_cyclesOfDimension_iff_forall_point]
    intro y hy
    obtain ⟨j, hj⟩ : ∃ j, α.1 j.1 * (β j).1 y ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (by change (∑ᶠ j, α.1 j.1 * (β j).1 y) = 0; simp [h])
    exact (mem_cyclesOfDimension_iff_forall_point C sY k _).mp (β j).2 y
      (right_ne_zero_of_mul hj)
  refine ⟨⟨B, hBmem⟩, rationallyEquivalentToZero_finsum C sX (k + (r : ℤ))
    (fun j ↦ α.1 j.1 • (pointCycle C sX (k + (r : ℤ)) j.1 (hx j) -
      flatPullback C sX sY f hbase r hf k (β j)))
    (fun j ↦ f.base ⁻¹' F j) (hFloc.preimage_continuous f.continuous)
    (fun j ↦ (hβ j).zsmul _) fun x ↦ ?_⟩
  have hfinA : (Function.support fun j : J ↦
      α.1 j.1 * (pointCycle C sX (k + (r : ℤ)) j.1 (hx j)).1 x).Finite := by
    refine Set.Subsingleton.finite fun i hi j hj ↦ Subtype.ext ?_
    simp only [Function.mem_support, pointCycle_apply] at hi hj
    split_ifs at hi hj <;> simp_all
  have hfinB : (Function.support fun j : J ↦
      α.1 j.1 * (β j).1 (f.base x) * flatPullbackWeight C sX f (k + (r : ℤ)) x).Finite :=
    (finite_support_of_locallyFinite F hFloc (fun j y ↦ α.1 j.1 * (β j).1 y) hsupp
      (f.base x)).subset fun _ hj ↦ left_ne_zero_of_mul hj
  have hval : ∀ j : J, (α.1 j.1 • (pointCycle C sX (k + (r : ℤ)) j.1 (hx j) -
      flatPullback C sX sY f hbase r hf k (β j))).1 x =
        α.1 j.1 * (pointCycle C sX (k + (r : ℤ)) j.1 (hx j)).1 x -
          α.1 j.1 * (β j).1 (f.base x) * flatPullbackWeight C sX f (k + (r : ℤ)) x := by
    intro j
    show α.1 j.1 * ((pointCycle C sX (k + (r : ℤ)) j.1 (hx j)).1 x -
      (flatPullback C sX sY f hbase r hf k (β j)).1 x) = _
    rw [flatPullback_apply]
    ring
  rw [finsum_congr hval, finsum_sub_distrib hfinA hfinB]
  show α.1 x - (flatPullback C sX sY f hbase r hf k ⟨B, hBmem⟩).1 x = _
  rw [flatPullback_apply]
  show α.1 x - (∑ᶠ j, α.1 j.1 * (β j).1 (f.base x)) *
    flatPullbackWeight C sX f (k + (r : ℤ)) x = _
  rw [finsum_mul, ← cycle_eq_finsum_pointCycle C sX _ α x]

end Summation

/-! ### The generic decomposition and its localization -/

section GenericDecomposition

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
  (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)

/-- A point `x` of `X` of delta-dimension `k + r` has a **generic decomposition** for `f` when
`[x] - f^*β - γ` is rationally equivalent to zero for a `k`-cycle `β` on `Y` and a
`(k + r)`-cycle `γ` on `X` carried by points not lying over `f x`. Over an integral base and for
`x` over the generic point, this says that `[x]` is a flat pullback modulo rational equivalence
and cycles not dominating the base. -/
def HasGenericDecomposition (x : X) : Prop :=
  ∃ hx : relativeDimension C.dimensionFunction sX x = k + (r : ℤ),
    ∃ (β : CycleGroup C sY k) (γ : CycleGroup C sX (k + (r : ℤ))),
      (∀ t, γ.1 t ≠ 0 → f.base t ≠ f.base x) ∧
        pointCycle C sX (k + (r : ℤ)) x hx - flatPullback C sX sY f hbase r hf k β - γ ∈
          rationalEquivalences C sX (k + (r : ℤ))

end GenericDecomposition

/-- A commuting square of scheme morphisms commutes on underlying points. -/
private theorem base_apply_eq_of_comp_eq {P Q R S : Scheme.{u}} {a : P ⟶ Q} {b : Q ⟶ S}
    {c : P ⟶ R} {d : R ⟶ S} (h : a ≫ b = c ≫ d) (t : P) :
    b.base (a.base t) = d.base (c.base t) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun φ : P ⟶ S ↦ φ.base t) h

/-- **Localization of the generic decomposition.** Consider a square `mA ≫ q = q' ≫ mB` of
schemes over the base whose horizontal legs `mA : A' ⟶ A` and `mB : B' ⟶ B` are open immersions,
whose vertical legs `q` and `q'` are flat of relative dimension `r`, and for which no point of
`A` outside `A'` lies over the image of a point `w` of `A'` (for instance because `A'` is the
whole inverse image of `B'`). A generic decomposition for `q'` at `w` gives one for `q` at
`mA w`.

The cycles `β'` and `γ'` on the open pieces extend to `B` and `A` by Stacks 02RC, and the
extended combination restricts to a combination rationally equivalent to zero on `A'`. By the
localization sequence Stacks 02RX it is then rationally equivalent to a cycle carried by the
closed complement of `A'`, which consists of points not lying over the image of `w`; that cycle
is absorbed into `γ`. -/
theorem hasGenericDecomposition_of_isOpenImmersion_square (C : ChowSituation.{u})
    {A B A' B' : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA'] (sB' : B' ⟶ C.S)
    [LocallyOfFiniteType sB'] (q : A ⟶ B) [LocallyOfFiniteType q] [Flat q] (hq : q ≫ sB = sA)
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension q r) (mA : A' ⟶ A) [IsOpenImmersion mA]
    (hmA : mA ≫ sA = sA') (mB : B' ⟶ B) [IsOpenImmersion mB] (hmB : mB ≫ sB = sB')
    (q' : A' ⟶ B') [LocallyOfFiniteType q'] [Flat q'] (hq' : q' ≫ sB' = sA')
    (hw : mA ≫ q = q' ≫ mB) (hr' : AlgebraicGeometry.RelativeDimension q' r)
    (k : ℤ) (w : A') (hout : ∀ t, t ∉ Set.range mA.base → q.base t ≠ q.base (mA.base w))
    (h : HasGenericDecomposition C sA' sB' q' hq' r hr' k w) :
    HasGenericDecomposition C sA sB q hq r hr k (mA.base w) := by
  obtain ⟨hw', β', γ', hγ', hrat⟩ := h
  have hwdim : relativeDimension C.dimensionFunction sA (mA.base w) = k + (r : ℤ) := by
    rw [← hw', ← hmA, relativeDimension_comp_isOpenImmersion]
  have hpt : ∀ t : A', q.base (mA.base t) = mB.base (q'.base t) := base_apply_eq_of_comp_eq hw
  obtain ⟨β, hβ⟩ := cycleGroupRestrict_surjective C sB sB' mB hmB k β'
  obtain ⟨γ1, hγ1⟩ := cycleGroupRestrict_surjective C sA sA' mA hmA (k + (r : ℤ)) γ'
  set c := pointCycle C sA (k + (r : ℤ)) (mA.base w) hwdim -
    flatPullback C sA sB q hq r hr k β - γ1 with hc
  have hcres : cycleGroupRestrict C sA sA' mA hmA (k + (r : ℤ)) c =
      pointCycle C sA' (k + (r : ℤ)) w hw' - flatPullback C sA' sB' q' hq' r hr' k β' - γ' := by
    rw [hc, map_sub, map_sub, cycleGroupRestrict_pointCycle C sA sA' mA hmA _ w hwdim hw',
      cycleGroupRestrict_flatPullback C sA sB sA' sB' q hq r hr mA hmA mB hmB q' hq' hw hr' k β,
      hβ, hγ1]
  -- the open subscheme `V = mA(A')` and its closed complement
  set V : A.Opens := mA.opensRange
  set T : A.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨(V : Set A)ᶜ, V.isOpen.isClosed_compl⟩ with hT
  have hcompl : Set.range T.subschemeι.base = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, hT,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Opens.range_ι]
    rfl
  have he : mA.isoOpensRange.inv ≫ sA' = V.ι ≫ sA :=
    isoOpensRange_inv_comp_base C sA sA' mA hmA
  have hres : cycleGroupOpensRestrict C sA V (k + (r : ℤ)) c =
      cycleGroupRestrict C sA' (V.ι ≫ sA) mA.isoOpensRange.inv he (k + (r : ℤ))
        (cycleGroupRestrict C sA sA' mA hmA (k + (r : ℤ)) c) := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun v ↦ ?_)
    rw [cycleGroupOpensRestrict_apply, cycleGroupRestrict_apply, cycleGroupRestrict_apply,
      ← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_inv_comp]
  have hratV : RationallyEquivalent C (V.ι ≫ sA) (k + (r : ℤ))
      (cycleGroupOpensRestrict C sA V (k + (r : ℤ)) c)
      (cycleGroupOpensRestrict C sA V (k + (r : ℤ)) 0) := by
    show _ - _ ∈ _
    rw [map_zero, sub_zero, hres, hcres]
    exact cycleGroupRestrict_mem_rationalEquivalences C sA' (V.ι ≫ sA) mA.isoOpensRange.inv
      he (k + (r : ℤ)) hrat
  obtain ⟨γ2, hγ2⟩ := exists_rationallyEquivalent_properPushforward_of_cycleGroupRestrict C sA
    (T.subschemeι ≫ sA) T.subschemeι rfl V hcompl (k + (r : ℤ)) c 0 hratV
  refine ⟨hwdim, β, γ1 + properPushforward C (T.subschemeι ≫ sA) sA T.subschemeι rfl
    (k + (r : ℤ)) γ2, fun t ht ↦ ?_, ?_⟩
  · by_cases htA : t ∈ Set.range mA.base
    · obtain ⟨t', rfl⟩ := htA
      have hnot : mA.base t' ∉ Set.range T.subschemeι.base := by
        rw [hcompl, Set.mem_compl_iff, not_not, Scheme.Opens.range_ι]
        exact ⟨t', rfl⟩
      change γ1.1 (mA.base t') + (properPushforward C (T.subschemeι ≫ sA) sA T.subschemeι rfl
        (k + (r : ℤ)) γ2).1 (mA.base t') ≠ 0 at ht
      rw [properPushforward_apply_of_notMem_range C _ sA T.subschemeι rfl _ γ2 hnot,
        add_zero] at ht
      have hγt : γ'.1 t' ≠ 0 := by
        rw [← hγ1]
        exact ht
      rw [hpt, hpt]
      exact fun heq ↦ hγ' t' hγt (mB.isOpenEmbedding.injective heq)
    · exact hout t htA
  · have hsub : pointCycle C sA (k + (r : ℤ)) (mA.base w) hwdim -
        flatPullback C sA sB q hq r hr k β - (γ1 + properPushforward C (T.subschemeι ≫ sA) sA
          T.subschemeι rfl (k + (r : ℤ)) γ2) =
        c - (0 + properPushforward C (T.subschemeι ≫ sA) sA T.subschemeι rfl (k + (r : ℤ))
          γ2) := by
      rw [hc]
      abel
    rwa [hsub]

/-! ### The induction on the delta-dimension of the image -/

/-- The hypothesis of the induction in Stacks 02TT: every affine-space bundle of rank `r` over an
integral base has a generic decomposition in degree `k` at every point lying over the generic
point of the base, phrased as a point whose image specializes to every point of the base. -/
def GenericDecompositionHolds (C : ChowSituation.{u}) (r : ℕ) (k : ℤ) : Prop :=
  ∀ {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (q : A ⟶ B) [LocallyOfFiniteType q] [Flat q] (hq : q ≫ sB = sA)
    (hr : AlgebraicGeometry.RelativeDimension q r), IsAffineSpaceBundle q r → IsIntegral B →
    ∀ w : A, relativeDimension C.dimensionFunction sA w = k + (r : ℤ) →
      (∀ b : B, q.base w ⤳ b) → HasGenericDecomposition C sA sB q hq r hr k w

/-- **The induction step of Stacks 02TT.** Granted the generic decomposition over integral bases,
every point of delta-dimension `k + r` of an affine-space bundle of rank `r` is good.

The proof is by induction on the delta-dimension of the image `y = f x`. The bundle is restricted
to the closure `Z` of `y`, an integral closed subscheme of the base, where `x` lies over the
generic point; the generic decomposition there writes `[x]` as a flat pullback plus a cycle `γ`
carried by points whose images are proper specializations of `y`. Those images have smaller
delta-dimension, and at least `k` by the bound on the transcendence degree of the fibres, so the
points of the support of `γ` are good by induction, and the summation step makes `γ` a flat
pullback. Pushing the resulting rational equivalence forward from `f⁻¹(Z)` to `X` along the
closed immersion, with Stacks 02RG for the flat pullback, exhibits `x` as good. -/
theorem isGoodPoint_of_genericDecompositionHolds (C : ChowSituation.{u}) (r : ℕ) (k : ℤ)
    (hgen : GenericDecompositionHolds C r k) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sY = sX)
    (hf : AlgebraicGeometry.RelativeDimension f r) (hbundle : IsAffineSpaceBundle f r) (x : X)
    (hx : relativeDimension C.dimensionFunction sX x = k + (r : ℤ)) :
    IsGoodPoint C sX sY f hbase r hf k x := by
  suffices H : ∀ n : ℕ, ∀ {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
      (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
      (hbase : f ≫ sY = sX) (hf : AlgebraicGeometry.RelativeDimension f r),
      IsAffineSpaceBundle f r → ∀ x : X,
        relativeDimension C.dimensionFunction sX x = k + (r : ℤ) →
        relativeDimension C.dimensionFunction sY (f.base x) ≤ k + n →
        IsGoodPoint C sX sY f hbase r hf k x from
    H (relativeDimension C.dimensionFunction sY (f.base x) - k).toNat sX sY f hbase hf hbundle
      x hx (by omega)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y sX _ sY _ f _ _ hbase hf hbundle x hx hn
  set y := f.base x
  set Z : Y.IdealSheafData := integralComponentAt y
  have _ : LocallyOfFiniteType (comapRestrict Z f) := locallyOfFiniteType_comapRestrict Z f
  have _ : Flat (comapRestrict Z f) := flat_comapRestrict Z f
  have hbundleZ := isAffineSpaceBundle_comapRestrict f hbundle Z
  have _ : QuasiCompact (comapRestrict Z f) := quasiCompact_of_isAffineSpaceBundle _ r hbundleZ
  have hbaseZ := comapRestrict_comp_base C sX sY f hbase Z
  have hfZ := relativeDimension_comapRestrict Z f hf
  have hsuppZ : (Z.support : Set Y) = closure {y} := coe_support_integralComponentAt y
  have hrangeZ' : Set.range (Z.comap f).subschemeι.base = f.base ⁻¹' closure {y} := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_comap, hsuppZ]
  obtain ⟨xt, hxt⟩ : x ∈ Set.range (Z.comap f).subschemeι.base := by
    rw [hrangeZ']
    exact subset_closure rfl
  have hpt : ∀ t, Z.subschemeι.base ((comapRestrict Z f).base t) =
      f.base ((Z.comap f).subschemeι.base t) :=
    base_apply_eq_of_comp_eq (comapRestrict_subschemeι Z f)
  have hxtdim : relativeDimension C.dimensionFunction ((Z.comap f).subschemeι ≫ sX) xt =
      k + (r : ℤ) := by
    rw [relativeDimension_comp_closedImmersion, hxt, hx]
  have hyZ : Z.subschemeι.base ((comapRestrict Z f).base xt) = y := by rw [hpt, hxt]
  have hmemZ : ∀ b : Z.subscheme, Z.subschemeι.base b ∈ closure {y} := fun b ↦ by
    rw [← hsuppZ, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨b, rfl⟩
  have hgenpt : ∀ b : Z.subscheme, (comapRestrict Z f).base xt ⤳ b := by
    intro b
    rw [← Z.subschemeι.isClosedEmbedding.isInducing.specializes_iff, hyZ,
      specializes_iff_mem_closure]
    exact hmemZ b
  obtain ⟨hxt', β, γ, hγ, hrat⟩ := hgen ((Z.comap f).subschemeι ≫ sX) (Z.subschemeι ≫ sY)
    (comapRestrict Z f) hbaseZ hfZ hbundleZ (isIntegral_integralComponentAt y) xt hxtdim hgenpt
  -- the points carrying `γ` are good, by induction
  have hgood : ∀ t, γ.1 t ≠ 0 → IsGoodPoint C ((Z.comap f).subschemeι ≫ sX)
      (Z.subschemeι ≫ sY) (comapRestrict Z f) hbaseZ r hfZ k t := by
    intro t ht
    have htdim := (mem_cyclesOfDimension_iff_forall_point C _ _ γ.1).mp γ.2 t ht
    have hne : Z.subschemeι.base ((comapRestrict Z f).base t) ≠ y := by
      rw [← hyZ]
      exact fun h ↦ hγ t ht (Z.subschemeι.isClosedEmbedding.injective h)
    have hlt := relativeDimension_lt_of_mem_closure_of_ne C sY (hmemZ _) hne
    have hdimZ : relativeDimension C.dimensionFunction (Z.subschemeι ≫ sY)
        ((comapRestrict Z f).base t) =
        relativeDimension C.dimensionFunction sY
          (Z.subschemeι.base ((comapRestrict Z f).base t)) :=
      relativeDimension_comp_closedImmersion _ _ _ _
    have hstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction (Z.subschemeι ≫ sY)
      (comapRestrict Z f) t
    rw [hbaseZ] at hstep
    have htr := toNat_residueTrdeg_le_of_relativeDimension (comapRestrict Z f) r hfZ t
    exact ih (relativeDimension C.dimensionFunction (Z.subschemeι ≫ sY)
      ((comapRestrict Z f).base t) - k).toNat (by omega) _ _ (comapRestrict Z f) hbaseZ hfZ
      hbundleZ t htdim (by omega)
  obtain ⟨β'', hβ''⟩ := exists_isRationallyEquivalentToZero_sub_flatPullback C
    ((Z.comap f).subschemeι ≫ sX) (Z.subschemeι ≫ sY) (comapRestrict Z f) hbaseZ r hfZ k γ
    hgood
  have hsum : IsRationallyEquivalentToZero C ((Z.comap f).subschemeι ≫ sX) (k + (r : ℤ))
      (pointCycle C _ (k + (r : ℤ)) xt hxt' -
        flatPullback C _ _ (comapRestrict Z f) hbaseZ r hfZ k (β + β'')) := by
    rw [map_add]
    show _ ∈ rationalEquivalences _ _ _
    convert add_mem hrat hβ'' using 1
    abel
  have hpush := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C
    ((Z.comap f).subschemeι ≫ sX) sX (Z.comap f).subschemeι rfl (k + (r : ℤ)) hsum
  rw [hrangeZ', properPushforward_sub, properPushforward_pointCycle C sX _ _ rfl _ xt hxt'
    (by rw [hxt]; exact hx)] at hpush
  refine ⟨hx, properPushforward C (Z.subschemeι ≫ sY) sY Z.subschemeι rfl k (β + β''),
    fun y' hy' ↦ ?_, ?_⟩
  · by_contra hmem
    refine hy' (properPushforward_apply_of_notMem_range C _ sY Z.subschemeι rfl k _ ?_)
    rwa [Scheme.IdealSheafData.range_subschemeι, hsuppZ]
  · rw [flatPullback_properPushforward_comap C sX sY f hbase r hf k Z (β + β'')]
    convert hpush using 3
    exact hxt.symm

/-- **Stacks 02TT, granted the generic decomposition over integral bases**, on cycles: every
`(k + r)`-cycle on the total space of an affine-space bundle of rank `r` is rationally
equivalent to the flat pullback of a `k`-cycle on the base. Every point is good by
`Stacks.Chow.isGoodPoint_of_genericDecompositionHolds`, and an affine-space bundle is
quasi-compact, so the summation step applies. -/
theorem exists_isRationallyEquivalentToZero_sub_flatPullback_of_genericDecompositionHolds
    (C : ChowSituation.{u}) (r : ℕ) (k : ℤ) (hgen : GenericDecompositionHolds C r k)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sY = sX) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hbundle : IsAffineSpaceBundle f r) (α : CycleGroup C sX (k + (r : ℤ))) :
    ∃ β : CycleGroup C sY k, IsRationallyEquivalentToZero C sX (k + (r : ℤ))
      (α - flatPullback C sX sY f hbase r hf k β) :=
  have _ : QuasiCompact f := quasiCompact_of_isAffineSpaceBundle f r hbundle
  exists_isRationallyEquivalentToZero_sub_flatPullback C sX sY f hbase r hf k α fun x hx ↦
    isGoodPoint_of_genericDecompositionHolds C r k hgen sX sY f hbase hf hbundle x
      ((mem_cyclesOfDimension_iff_forall_point C sX _ α.1).mp α.2 x hx)

/-- **Stacks 02TT, granted the generic decomposition over integral bases**: flat pullback along
an affine-space bundle of rank `r` is surjective on Chow groups in degree `k`. -/
theorem flatPullbackChow_surjective_of_genericDecompositionHolds (C : ChowSituation.{u})
    (r : ℕ) (k : ℤ) (hgen : GenericDecompositionHolds C r k) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sY = sX)
    (hf : AlgebraicGeometry.RelativeDimension f r) (hbundle : IsAffineSpaceBundle f r)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hbase r hf k) :
    Function.Surjective (flatPullbackChow C sX sY f hbase r hf k hfac) := by
  intro a
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  obtain ⟨β, hβ⟩ :=
    exists_isRationallyEquivalentToZero_sub_flatPullback_of_genericDecompositionHolds C r k
      hgen sX sY f hbase hf hbundle α
  refine ⟨QuotientAddGroup.mk' _ β, ?_⟩
  rw [flatPullbackChow_mk]
  exact (QuotientAddGroup.eq_iff_sub_mem).mpr (by rw [← neg_sub]; exact neg_mem hβ)

end Stacks.Chow

end
