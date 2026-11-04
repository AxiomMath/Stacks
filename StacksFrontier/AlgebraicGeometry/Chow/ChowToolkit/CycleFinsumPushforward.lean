module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily

/-!
# Locally finite sums of Chow classes carried by closed subschemes

Let `Y` be a scheme locally of finite type over the base scheme of chapter 42 of the Stacks
Project and let `(T i)_i` be a locally finite family of closed subschemes of `Y`. Stacks 02RZ,
available as `Stacks.Chow.rationallyEquivalent_finsum_of_closedSupports`, says that rational
equivalences over such a family may be summed. What it does *not* say, and what this file
supplies, is that the sum exists in the first place: a family of `k`-cycles `b i` on the `T i`
has a well-defined locally finite sum of pushforwards, both as a cycle on `Y` and — this is the
point — as a **Chow class** on `Y`, independent of the cycles chosen to represent the classes of
the `b i`.

The devissage of Stacks 02TT needs exactly this. Its first step writes a class on the total space
of an affine-space bundle as a locally finite sum over the integral closed subschemes carrying the
images of the components of a representing cycle, and produces a class on each of those
subschemes; to assemble them into a single class on the base one must add infinitely many classes,
which a Chow group does not let one do. The sum has to be formed on representatives and shown
independent of them, and the independence is Stacks 02RZ.

## Main results

* `Stacks.Chow.support_properPushforward_subschemeι_subset` — the pushforward of a cycle on a
  closed subscheme `T ⊆ Y` is supported on `T`.
* `Stacks.Chow.exists_cycle_finsum_properPushforward` — the locally finite sum of the
  pushforwards of a family of `k`-cycles on a locally finite family of closed subschemes is a
  `k`-cycle on `Y`.
* `Stacks.Chow.chowGroupMk_finsum_properPushforward_congr` — **Stacks 02RZ as well-definedness of
  the sum of Chow classes**: two families of representatives of the same classes assemble to the
  same class on `Y`.
* `Stacks.Chow.exists_chowGroup_finsum_properPushforward` — the locally finite sum of a family of
  Chow classes carried by a locally finite family of closed subschemes, as a class on `Y`
  together with the property that pins it down: every assembly from representatives represents
  it.

## Implementation notes

The sum of classes is produced in existential form rather than as a definition. A definition
would have to choose representatives, and the only way to use it would be to unfold that choice
again through `Stacks.Chow.chowGroupMk_finsum_properPushforward_congr`; the existential statement
carries the same information with the choice already discharged, and is what the devissage
consumes.

The index type is restricted to `Type u`, the universe of the schemes, in the two Chow-level
results: `Stacks.Chow.IsRationallyEquivalentToZero` quantifies the index type of its witnessing
family over `Type u`, so Stacks 02RZ is only available there. The cycle-level assembly has no
such restriction.

## References

* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-! ### The support of a pushforward from a closed subscheme -/

/-- **The pushforward of a cycle on a closed subscheme `T ⊆ Y` is supported on `T`.** Away from
`T.support` the fibre of `T.subschemeι` is empty, so the locally finite sum computing the
coefficient of the pushforward there is empty; the image of `T.subschemeι` is `T.support` by
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`. -/
theorem support_properPushforward_subschemeι_subset (k : ℤ) (T : Y.IdealSheafData)
    (c : CycleGroup C (T.subschemeι ≫ sY) k) :
    Function.support (properPushforward C (T.subschemeι ≫ sY) sY T.subschemeι rfl k c).1 ⊆
      (T.support : Set Y) := by
  rw [← T.range_subschemeι]
  intro y hy
  by_contra hny
  exact hy (properPushforward_apply_of_notMem_range C (T.subschemeι ≫ sY) sY T.subschemeι rfl k
    c hny)

/-! ### The locally finite sum of pushforwards, on cycles -/

/-- **The locally finite sum of the pushforwards of cycles carried by a locally finite family of
closed subschemes.** Given a locally finite family `(T i)_i` of closed subschemes of `Y` and a
`k`-cycle `b i` on each `T i`, the function `y ↦ ∑_i (i_i)_* (b i) (y)` is the coefficient
function of a `k`-cycle on `Y`.

Each summand is supported on `T i` by
`Stacks.Chow.support_properPushforward_subschemeι_subset`, so the sum has locally finite support
by `Stacks.Chow.locallyFiniteSupport_finsum_of_locallyFinite`; and each summand is a `k`-cycle,
so at a point where the sum is nonzero some summand already forces the delta-dimension to be
`k`. -/
theorem exists_cycle_finsum_properPushforward (k : ℤ) {I : Type*} (T : I → Y.IdealSheafData)
    (hT : LocallyFinite fun i ↦ ((T i).support : Set Y))
    (b : ∀ i, CycleGroup C ((T i).subschemeι ≫ sY) k) :
    ∃ β : CycleGroup C sY k, ∀ y : Y, β.1 y =
      ∑ᶠ i : I, (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k (b i)).1
        y := by
  have hsub : ∀ i, Function.support (fun y ↦
      (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k (b i)).1 y) ⊆
      ((T i).support : Set Y) := fun i ↦
    support_properPushforward_subschemeι_subset C sY k (T i) (b i)
  have hlfs : ∀ i, LocallyFiniteSupport (fun y ↦
      (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k (b i)).1 y) :=
    fun i ↦ (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k
      (b i)).1.locallyFiniteSupport
  have hloc := locallyFiniteSupport_finsum_of_locallyFinite (fun i ↦ ((T i).support : Set Y)) hT
    (fun i y ↦ (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k (b i)).1 y)
    hsub hlfs
  refine ⟨⟨⟨fun y ↦ ∑ᶠ i : I,
      (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k (b i)).1 y, by simp,
      fun z _ ↦ hloc z⟩, ?_⟩, fun _ ↦ rfl⟩
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro y hy
  have hex : ∃ i, (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k
      (b i)).1 y ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    refine hy ?_
    show (∑ᶠ i : I, (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k
      (b i)).1 y) = 0
    rw [show (fun i : I ↦ (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k
      (b i)).1 y) = fun _ ↦ (0 : ℤ) from funext h]
    exact finsum_zero
  obtain ⟨i, hi⟩ := hex
  exact (mem_cyclesOfDimension_iff_forall_point C sY k _).1
    (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k (b i)).2 y hi

/-! ### The locally finite sum of pushforwards, on Chow classes -/

/-- **Stacks 02RZ as well-definedness of the locally finite sum of Chow classes.** If `a i` and
`b i` are `k`-cycles on the members of a locally finite family of closed subschemes of `Y`
representing the same Chow class for every `i`, then the two cycles on `Y` assembled from them
as locally finite sums of pushforwards represent the same Chow class.

This is `Stacks.Chow.rationallyEquivalent_finsum_of_closedSupports` read through
`QuotientAddGroup.eq_iff_sub_mem`. -/
theorem chowGroupMk_finsum_properPushforward_congr (k : ℤ) {I : Type u}
    (T : I → Y.IdealSheafData) (hT : LocallyFinite fun i ↦ ((T i).support : Set Y))
    (a b : ∀ i, CycleGroup C ((T i).subschemeι ≫ sY) k)
    (hab : ∀ i, QuotientAddGroup.mk' (rationalEquivalences C ((T i).subschemeι ≫ sY) k) (a i) =
      QuotientAddGroup.mk' (rationalEquivalences C ((T i).subschemeι ≫ sY) k) (b i))
    {α β : CycleGroup C sY k}
    (hα : ∀ y : Y, α.1 y = ∑ᶠ i : I,
      (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k (a i)).1 y)
    (hβ : ∀ y : Y, β.1 y = ∑ᶠ i : I,
      (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k (b i)).1 y) :
    QuotientAddGroup.mk' (rationalEquivalences C sY k) α =
      QuotientAddGroup.mk' (rationalEquivalences C sY k) β :=
  QuotientAddGroup.eq_iff_sub_mem.2
    (rationallyEquivalent_finsum_of_closedSupports C sY k T hT a b
      (fun i ↦ QuotientAddGroup.eq_iff_sub_mem.1 (hab i)) hα hβ)

/-- **The locally finite sum of a family of Chow classes carried by a locally finite family of
closed subschemes.** Given a locally finite family `(T i)_i` of closed subschemes of `Y` and a
class `β i ∈ A_k(T i)` for each `i`, there is a class `b ∈ A_k(Y)` with the property that
*every* assembly of representatives represents it: whenever `c i` is a `k`-cycle representing
`β i` for each `i` and `γ` is a `k`-cycle on `Y` whose coefficients are the locally finite sums
of those of the pushforwards of the `c i`, the class of `γ` is `b`.

Existence of one assembly is `Stacks.Chow.exists_cycle_finsum_properPushforward`; that every
other assembly represents the same class is Stacks 02RZ, in the form
`Stacks.Chow.chowGroupMk_finsum_properPushforward_congr`. -/
theorem exists_chowGroup_finsum_properPushforward (k : ℤ) {I : Type u}
    (T : I → Y.IdealSheafData) (hT : LocallyFinite fun i ↦ ((T i).support : Set Y))
    (β : ∀ i, chowGroup C ((T i).subschemeι ≫ sY) k) :
    ∃ b : chowGroup C sY k, ∀ (c : ∀ i, CycleGroup C ((T i).subschemeι ≫ sY) k)
      (_ : ∀ i, QuotientAddGroup.mk' (rationalEquivalences C ((T i).subschemeι ≫ sY) k) (c i) =
        β i)
      (γ : CycleGroup C sY k)
      (_ : ∀ y : Y, γ.1 y = ∑ᶠ i : I,
        (properPushforward C ((T i).subschemeι ≫ sY) sY (T i).subschemeι rfl k (c i)).1 y),
      QuotientAddGroup.mk' (rationalEquivalences C sY k) γ = b := by
  choose c₀ hc₀ using fun i ↦
    QuotientAddGroup.mk'_surjective (rationalEquivalences C ((T i).subschemeι ≫ sY) k) (β i)
  obtain ⟨γ₀, hγ₀⟩ := exists_cycle_finsum_properPushforward C sY k T hT c₀
  refine ⟨QuotientAddGroup.mk' (rationalEquivalences C sY k) γ₀, fun c hc γ hγ ↦ ?_⟩
  exact chowGroupMk_finsum_properPushforward_congr C sY k T hT c c₀
    (fun i ↦ (hc i).trans (hc₀ i).symm) hγ hγ₀

end Stacks.Chow

end
