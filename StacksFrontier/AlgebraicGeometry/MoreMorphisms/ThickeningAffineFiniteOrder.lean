module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafInclusion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffine

/-!
# Affineness of a finite-order thickening reduces to the first-order case

[Stacks Project, Tag 06AD] says that any thickening of an affine scheme is affine.
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffine` reduces that statement to the
surjectivity of `i.appTop`, which is a first-cohomology vanishing. This file removes the
dependence on the *order* of the thickening from the finite-order case: a finite-order thickening
of an affine scheme is affine as soon as every **first-order** thickening of an affine scheme is.

The reduction is the adic filtration of the defining ideal sheaf. For `i : X ⟶ X'` a closed
immersion with ideal sheaf `I = i.ker`, the closed subschemes `V(I ^ (k + 1))` interpolate
between `V(I) = X` and `V(I ^ (n + 1)) = V(⊥) = X'`, and each inclusion
`V(I ^ (k + 1)) ⟶ V(I ^ (k + 2))` is a first-order thickening, because the square of its defining
ideal sheaf is cut out by `I ^ (2 * k + 2)`, which is contained in `I ^ (k + 2)`.

Note that this route does **not** pass through Serre's criterion, which is what the Stacks proof
of the finite-order case uses: it needs the first-order case of [Stacks Project, Tag 06AD] only,
and no statement about arbitrary quasi-coherent modules.

## Main results

* `Stacks.Thickenings.isFirstOrderThickening_inclusion_pow`: the inclusion of the closed
  subscheme cut out by `I ^ (k + 1)` into the one cut out by `I ^ (k + 2)` is a first-order
  thickening.
* `Stacks.Thickenings.isAffine_subscheme_ker_pow_of_firstOrder`: granted the first-order case of
  [Stacks Project, Tag 06AD], every `V(i.ker ^ (k + 1))` of a closed immersion `i` with affine
  source is affine.
* `Stacks.Thickenings.isAffine_of_isNthOrderThickening_of_firstOrder` and
  `Stacks.Thickenings.isAffine_of_isFiniteOrderThickening_of_firstOrder`: the finite-order case of
  [Stacks Project, Tag 06AD] follows from the first-order case.
* `Stacks.Thickenings.isAffine_of_isFiniteOrderThickening_of_surjective_appTop`: the same with the
  first-order case given in its cohomological form, as surjectivity of the map on global
  sections. This is the precise remaining content of the finite-order case of
  [Stacks Project, Tag 06AD].

## Implementation notes

The first-order hypothesis is taken as an explicit universally quantified argument rather than as
a typeclass or a section variable, because it is a statement about *all* first-order thickenings
of *all* affine schemes and is applied at the interpolating subschemes, not at `i` itself.

The defining ideal sheaf of an inclusion of closed subschemes is computed by
`Stacks.ClosedImmersion.ker_inclusion_ideal`, which is available only on the charts
`I.subschemeι ⁻¹ᵁ U` lying over an affine open `U` of the ambient scheme. Those charts cover the
subscheme, so `AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top` turns the chartwise
computation into the required equality of ideal sheaf data.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Thickenings

variable {X X' : Scheme.{u}}

/-- **Powers of an ideal sheaf datum decrease.**  Checked ideal by ideal on affine opens, where it
is `Ideal.pow_le_pow_right`. -/
theorem idealSheafData_pow_le_pow (I : X.IdealSheafData) {m n : ℕ} (h : n ≤ m) :
    I ^ m ≤ I ^ n :=
  Scheme.IdealSheafData.le_def.mpr fun U ↦ by
    simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply] using Ideal.pow_le_pow_right h

/-- A family of opens covers the space as soon as every point lies in one of them. -/
private theorem iSup_eq_top_of_forall_mem {α ι : Type*} [TopologicalSpace α] {V : ι → Opens α}
    (h : ∀ x, ∃ j, x ∈ V j) : ⨆ j, V j = ⊤ :=
  top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr (h x)

/-- **The charts of a closed subscheme over the affine opens of the ambient scheme cover it.** -/
theorem iSup_preimage_affineOpens_subschemeι (I : X.IdealSheafData) :
    (⨆ U : X.affineOpens, I.subschemeι ⁻¹ᵁ U.1) = ⊤ :=
  iSup_eq_top_of_forall_mem fun x ↦ (Opens.mem_iSup (s := fun U : X.affineOpens ↦ U.1)).mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ (I.subschemeι x)))

/-- **Each step of the adic filtration is a first-order thickening.**  The defining ideal sheaf of
the inclusion of `V(I ^ (k + 1))` into `V(I ^ (k + 2))` is, on the chart over an affine open `U`,
the image of `(I ^ (k + 1)).ideal U`; its square is therefore the image of
`(I ^ (2 * k + 2)).ideal U`, which is contained in the kernel `(I ^ (k + 2)).ideal U` of the chart
map. -/
theorem isFirstOrderThickening_inclusion_pow (I : X.IdealSheafData) (k : ℕ)
    (h : I ^ (k + 2) ≤ I ^ (k + 1)) :
    IsFirstOrderThickening (Scheme.IdealSheafData.inclusion h) := by
  refine ⟨inferInstance, ?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : X.affineOpens ↦ ⟨(I ^ (k + 2)).subschemeι ⁻¹ᵁ U.1, U.2.preimage _⟩)
    (iSup_preimage_affineOpens_subschemeι _) fun U ↦ ?_
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot,
    Pi.bot_apply, Stacks.ClosedImmersion.ker_inclusion_ideal h U, ← Ideal.map_pow,
    Ideal.map_eq_bot_iff_le_ker, Scheme.IdealSheafData.ker_subschemeι_app, ← pow_mul]
  exact Ideal.pow_le_pow_right (by omega)

/-- **Granted the first-order case of [Stacks Project, Tag 06AD], every stage of the adic
filtration of a closed immersion with affine source is affine.**  An induction on `k`: the base
case is that `V(i.ker)` is the scheme-theoretic image of `i`, which a closed immersion identifies
with its source, and the inductive step is the hypothesis applied to
`Stacks.Thickenings.isFirstOrderThickening_inclusion_pow`. -/
theorem isAffine_subscheme_ker_pow_of_firstOrder
    (H : ∀ (Z Z' : Scheme.{u}) (j : Z ⟶ Z'), IsFirstOrderThickening j → IsAffine Z → IsAffine Z')
    {i : X ⟶ X'} [IsClosedImmersion i] [IsAffine X] (k : ℕ) :
    IsAffine ((i.ker ^ (k + 1)).subscheme) := by
  induction k with
  | zero =>
    rw [zero_add, pow_one]
    exact IsAffine.of_isIso (CategoryTheory.inv i.toImage)
  | succ k ih =>
    exact H _ _ _ (isFirstOrderThickening_inclusion_pow i.ker k
      (idealSheafData_pow_le_pow i.ker (Nat.le_succ _))) ih

/-- **The `n`th-order case of [Stacks Project, Tag 06AD] follows from the first-order case.**  The
`n`th stage of the adic filtration is cut out by `i.ker ^ (n + 1) = ⊥`, hence is the ambient
scheme itself. -/
theorem isAffine_of_isNthOrderThickening_of_firstOrder
    (H : ∀ (Z Z' : Scheme.{u}) (j : Z ⟶ Z'), IsFirstOrderThickening j → IsAffine Z → IsAffine Z')
    {n : ℕ} {i : X ⟶ X'} (hi : IsNthOrderThickening n i) [IsAffine X] : IsAffine X' := by
  have := hi.1
  have := isAffine_subscheme_ker_pow_of_firstOrder H (i := i) n
  rw [hi.2] at this
  exact IsAffine.of_isIso (CategoryTheory.inv (Scheme.IdealSheafData.subschemeι ⊥))

/-- **The finite-order case of [Stacks Project, Tag 06AD] follows from the first-order case.** -/
theorem isAffine_of_isFiniteOrderThickening_of_firstOrder
    (H : ∀ (Z Z' : Scheme.{u}) (j : Z ⟶ Z'), IsFirstOrderThickening j → IsAffine Z → IsAffine Z')
    {i : X ⟶ X'} (hi : IsFiniteOrderThickening i) [IsAffine X] : IsAffine X' :=
  isAffine_of_isNthOrderThickening_of_firstOrder H ⟨hi.1, hi.2.choose_spec⟩

/-- **The finite-order case of [Stacks Project, Tag 06AD] follows from the surjectivity of the map
on global sections of a first-order thickening of an affine scheme.**  This is the reduction of
`Stacks.Thickenings.isAffine_of_isFiniteOrderThickening_of_firstOrder` composed with
`Stacks.Thickenings.isAffine_of_isThickening_of_surjective_appTop`; the surjectivity it asks for
is the vanishing of the first cohomology of the defining ideal sheaf, which for a first-order
thickening is a quasi-coherent module on the affine closed subscheme. -/
theorem isAffine_of_isFiniteOrderThickening_of_surjective_appTop
    (H : ∀ (Z Z' : Scheme.{u}) (j : Z ⟶ Z'), IsFirstOrderThickening j → IsAffine Z →
      Function.Surjective j.appTop.hom)
    {i : X ⟶ X'} (hi : IsFiniteOrderThickening i) [IsAffine X] : IsAffine X' :=
  isAffine_of_isFiniteOrderThickening_of_firstOrder
    (fun Z Z' j hj hZ ↦ isAffine_of_isThickening_of_surjective_appTop (X := Z) hj.isThickening
      (H Z Z' j hj hZ)) hi

/-! ### The standard cover input for the first-order case -/

/-- **A thickening of an affine scheme has a finite standard cover.**  Every point of the ambient
scheme has an affine open neighbourhood whose preimage is a basic open of the affine closed
subscheme, by `Stacks.Thickenings.IsThickening.exists_isAffineOpen_preimage_eq_basicOpen`, and the
ambient scheme is quasi-compact, so finitely many of these cover it.  The cutting sections then
generate the unit ideal, because their basic opens cover the affine closed subscheme.

This is the input shape of `Stacks.Cohomology.Cech.isZero_cechCohomology_of_isStandardOpenCover`
([Stacks Project, Tag 01X9]) and of `Stacks.RingTheory.CechAcyclicity.cech_exact`: it needs no
hypothesis on the order of the thickening and no surjectivity of `i.appTop`. -/
theorem IsThickening.exists_finite_isAffineOpen_cover_preimage_eq_basicOpen [IsAffine X]
    {i : X ⟶ X'} (hi : IsThickening i) :
    ∃ (n : ℕ) (V : Fin n → X'.Opens) (a : Fin n → Γ(X, (⊤ : X.Opens))),
      (∀ j, IsAffineOpen (V j)) ∧ (⨆ j, V j) = ⊤ ∧
        (∀ j, i ⁻¹ᵁ V j = X.basicOpen (a j)) ∧ Ideal.span (Set.range a) = ⊤ := by
  have := hi.compactSpace
  choose V a hVaff hxV hpre using hi.exists_isAffineOpen_preimage_eq_basicOpen
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X' ↦ (V x : Set X'))
    (fun x ↦ (V x).2) fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxV x⟩
  refine ⟨s.card, fun j ↦ V (s.equivFin.symm j), fun j ↦ a (s.equivFin.symm j),
    fun j ↦ hVaff _, ?_, fun j ↦ hpre _, ?_⟩
  · refine iSup_eq_top_of_forall_mem fun x ↦ ?_
    obtain ⟨y, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨s.equivFin ⟨y, hy.1⟩, by simpa using hy.2⟩
  · rw [← (isAffineOpen_top X).self_le_iSup_basicOpen_iff]
    intro y _
    obtain ⟨z, hz⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ (i y)))
    refine Opens.mem_iSup.mpr ⟨⟨a (s.equivFin.symm (s.equivFin ⟨z, hz.1⟩)), _, rfl⟩, ?_⟩
    refine (hpre (s.equivFin.symm (s.equivFin ⟨z, hz.1⟩))).le ?_
    simpa using hz.2

end Stacks.Thickenings

end
