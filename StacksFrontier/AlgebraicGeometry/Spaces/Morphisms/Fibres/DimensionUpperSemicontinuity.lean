module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionFieldFibre

/-!
# Upper semicontinuity of the fibre dimension of a proper morphism

The fibre-dimension function of a proper morphism of algebraic spaces over a scheme `S` is upper
semicontinuous on the points of its target.

## Main results

* `AlgebraicGeometry.Space.fiberDimension_eq_bot_iff`: the fibre dimension is `⊥` exactly outside
  the image of the morphism on points.
* `AlgebraicGeometry.Space.isOpen_setOf_fiberDimension_le`: for a closed morphism locally of
  finite type the locus where the fibre dimension is at most `n` is open.
* `AlgebraicGeometry.Space.upperSemicontinuous_fiberDimension` is **Stacks 0D4Q**.

## Implementation notes

A proper morphism is closed on points, so the image of a closed subset of `|X|` is closed in
`|Y|`. For a natural number `n` the complement of the locus `{y | n_{X/Y}(y) ≤ n}` is exactly the
image of the closed locus where the relative dimension is nowhere bounded by `n`, the latter being
closed because its complement is open by Stacks 04NT. Together with the description of the fibre
over a point outside the image this gives openness of all the sublevel sets of the fibre-dimension
function: the one below `⊥` is empty, the one below `0` is the complement of the image, the one
below `n + 1` is `{y | n_{X/Y}(y) ≤ n}`, and the one below `⊤` is the union of all of those.

## References

* [Stacks Project, Tag 0D4Q](https://stacks.math.columbia.edu/tag/0D4Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The fibre dimension of a morphism of presheaves is `⊥` at a point of the target exactly when
no point of the source lies over it: the defining infimum is then over all of `WithBot ℕ∞`, and
otherwise it is bounded below by `0`. -/
theorem fiberDimension_eq_bot_iff (f : X ⟶ Y) (y : points B S hS Y) :
    fiberDimension B S hS f y = ⊥ ↔ y ∉ Set.range (pointsMap B S hS X f) := by
  rw [fiberDimension]
  constructor
  · rintro hbot ⟨x, hxy⟩
    have hle : (0 : WithBot ℕ∞) ≤ sInf {d : WithBot ℕ∞ | ∀ x : points B S hS X,
        pointsMap B S hS X f x = y →
          ∃ e : ℕ∞, HasRelativeDimensionAt e B S hS f x ∧ (e : WithBot ℕ∞) ≤ d} := by
      refine le_sInf fun d hd ↦ ?_
      obtain ⟨e, -, hed⟩ := hd x hxy
      exact le_trans (by simp) hed
    rw [hbot] at hle
    exact (not_le_of_gt (WithBot.bot_lt_coe (0 : ℕ∞))) hle
  · exact fun hy ↦ le_antisymm (sInf_le fun x hxy ↦ absurd ⟨x, hxy⟩ hy) bot_le

/-- For a closed morphism of algebraic spaces over `S` which is locally of finite type, the locus
in the target where the fibre dimension is at most a natural number `n` is open: its complement is
the image of the closed locus of points of the source where the relative dimension is nowhere
bounded by `n`. -/
theorem isOpen_setOf_fiberDimension_le (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (hclosed : IsClosedMorphism B S hS f) (n : ℕ) :
    IsOpen {y : points B S hS Y | fiberDimension B S hS f y ≤ (n : WithBot ℕ∞)} := by
  have heq : {y : points B S hS Y | fiberDimension B S hS f y ≤ (n : WithBot ℕ∞)}ᶜ =
      pointsMap B S hS X f '' {x : points B S hS X |
        ¬ ∃ d : ℕ∞, d ≤ (n : ℕ∞) ∧ HasRelativeDimensionAt d B S hS f x} := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_image]
    rw [fiberDimension_le_iff]
    constructor
    · intro hy
      obtain ⟨x, hnot⟩ := not_forall.mp hy
      obtain ⟨hxy, hbad⟩ := not_imp.mp hnot
      exact ⟨x, fun ⟨d, hdn, hdrel⟩ ↦ hbad ⟨d, hdrel, WithBot.coe_le_coe.mpr hdn⟩, hxy⟩
    · rintro ⟨x, hx, hxy⟩ hall
      obtain ⟨e, he, hen⟩ := hall x hxy
      exact hx ⟨e, WithBot.coe_le_coe.mp hen, he⟩
  rw [← isClosed_compl_iff, heq]
  exact hclosed _ (isOpen_setOf_hasRelativeDimensionAt_le B S hS hX hY f hf n).isClosed_compl

/-- **Stacks 0D4Q.** The fibre-dimension function of a proper morphism of algebraic spaces over
`S` is upper semicontinuous on the points of its target. -/
@[stacks 0D4Q]
theorem upperSemicontinuous_fiberDimension (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsProper B S hS f) :
    UpperSemicontinuous (fiberDimension B S hS f) := by
  obtain ⟨-, ⟨hft, -⟩, huc⟩ := hf
  have hclosed := isClosed_of_universallyClosed B S hS hY f huc
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro b
  cases b with
  | bot => simp
  | coe b =>
    cases b with
    | top =>
      have heq : (fiberDimension B S hS f) ⁻¹' Set.Iio (⊤ : WithBot ℕ∞) =
          ⋃ n : ℕ, {y : points B S hS Y |
            fiberDimension B S hS f y ≤ (n : WithBot ℕ∞)} := by
        ext y
        simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_ofPred_eq]
        constructor
        · intro hy
          cases hd : fiberDimension B S hS f y with
          | bot => exact ⟨0, by simp⟩
          | coe d =>
            cases d with
            | top => simp_all
            | coe m => exact ⟨m, by simp⟩
        · rintro ⟨m, hm⟩
          exact lt_of_le_of_lt hm (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top m))
      rw [WithBot.coe_top, heq]
      exact isOpen_iUnion fun n ↦ isOpen_setOf_fiberDimension_le B S hS hX hY f hft hclosed n
    | coe n =>
      cases n with
      | zero =>
        have heq : (fiberDimension B S hS f) ⁻¹' Set.Iio (((0 : ℕ) : ℕ∞) : WithBot ℕ∞) =
            (Set.range (pointsMap B S hS X f))ᶜ := by
          ext y
          simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_compl_iff]
          rw [Nat.cast_zero, ← bot_eq_zero, WithBot.lt_coe_bot,
            fiberDimension_eq_bot_iff B S hS f y]
        rw [heq]
        exact hclosed.isClosed_range.isOpen_compl
      | succ n =>
        have heq : (fiberDimension B S hS f) ⁻¹' Set.Iio (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) =
            {y : points B S hS Y | fiberDimension B S hS f y ≤ (n : WithBot ℕ∞)} := by
          ext y
          simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_ofPred_eq]
          rw [show (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = (n : WithBot ℕ∞) + 1 by norm_cast]
          exact ENat.WithBot.lt_add_one_iff
        rw [heq]
        exact isOpen_setOf_fiberDimension_le B S hS hX hY f hft hclosed n

end AlgebraicGeometry.Space

end
