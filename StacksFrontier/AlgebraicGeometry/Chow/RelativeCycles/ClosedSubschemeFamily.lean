module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleFamily
public import StacksCore.Tactic.StacksAttribute

/-!
# The family of cycles associated to a closed subscheme

Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `r ≥ 0` be an integer, and
let `Z ⊂ X` be a closed subscheme. For a point `s` of `S` write `Z_s` for the inverse image of
`Z` in the scheme-theoretic fibre `X_s`, equivalently the scheme-theoretic fibre of `Z` at `s`
viewed as a closed subscheme of `X_s`, and assume `dim (Z_s) ≤ r` for every `s`.

Each fibre `X_s` is locally of finite type over the residue field `κ(s)`, so the cycle `[Z_s]_r`
of Chow homology is defined on it, and `s ↦ [Z_s]_r` is a family of `r`-cycles on the fibres of
`X/S`: the family `[Z/X/S]_r`. The family is defined for every `r`, with no dimension
hypothesis; `Stacks.Chow.fiberClosedSubscheme_schemeDeltaDimension_le` records what the
hypothesis gives.

## Main definitions

* `Stacks.Chow.fiberClosedImmersion` — the closed subscheme `Z_s` of the fibre `X_s`, as the
  base change of `Z ⟶ X` along `X_s ⟶ X`.
* `Stacks.Chow.familyAssociatedToClosedSubscheme` — the family `[Z/X/S]_r`.

## Main results

* `Stacks.Chow.fiberClosedSubscheme_schemeDeltaDimension_le` — if `dim (Z_s) ≤ r` then `Z_s`
  has delta-dimension at most `r` over `Spec κ(s)`.
* `Stacks.Chow.familyAssociatedToClosedSubscheme_apply` — the member of `[Z/X/S]_r` over `s` is
  the cycle `[Z_s]_r`.
* `Stacks.Chow.familyAssociatedToClosedSubscheme_apply_coeff` — at the image of the generic
  point of a component of `Z_s` of delta-dimension `r` the coefficient is that component's
  multiplicity, and
  `Stacks.Chow.familyAssociatedToClosedSubscheme_apply_coeff_eq_zero` — every other coefficient
  vanishes.

## References

* [Stacks Project, Tag 0H4S](https://stacks.math.columbia.edu/tag/0H4S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S : Scheme.{u}}

/-! ### The closed subscheme on a fibre -/

/-- The inverse image `Z_s = Z ×_X X_s` of a closed subscheme `i : Z ⟶ X` in the
scheme-theoretic fibre `X_s`, as a closed subscheme of `X_s`: the base change of `i` along
`X_s ⟶ X`. -/
def fiberClosedImmersion (f : X ⟶ S) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (s : S) :
    pullback i (f.fiberι s) ⟶ f.fiber s :=
  pullback.snd i (f.fiberι s)

/-- The inverse image of a closed subscheme in a fibre is a closed subscheme of that fibre. -/
instance fiberClosedImmersion_isClosedImmersion (f : X ⟶ S) {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (s : S) : IsClosedImmersion (fiberClosedImmersion f i s) :=
  inferInstanceAs (IsClosedImmersion (pullback.snd i (f.fiberι s)))

/-- The image of `Z_s` in the fibre `X_s` has the same topological dimension as `Z_s`. -/
theorem topologicalKrullDim_range_fiberClosedImmersion (f : X ⟶ S) {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (s : S) :
    topologicalKrullDim ↥(Set.range (fiberClosedImmersion f i s)) =
      topologicalKrullDim ↥(pullback i (f.fiberι s)) :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (fiberClosedImmersion f i s).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

/-- A point of `Z_s` has relative dimension at most `r` over `Spec κ(s)` as soon as `Z_s` has
dimension at most `r`. -/
theorem relativeDimension_fiberClosedImmersion_le (f : X ⟶ S) [LocallyOfFiniteType f]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] {r : ℕ} (s : S)
    (hdim : topologicalKrullDim ↥(pullback i (f.fiberι s)) ≤ (r : WithBot ℕ∞))
    (w : ↥(pullback i (f.fiberι s))) :
    relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) (fiberClosedImmersion f i s w) ≤ (r : ℤ) := by
  have : JacobsonSpace (fieldChowSituation (S.residueField s)).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of (S.residueField s))))
  have hrange : topologicalKrullDim ↥(Set.range (fiberClosedImmersion f i s)) ≤
      (r : WithBot ℕ∞) :=
    (topologicalKrullDim_range_fiberClosedImmersion f i s).trans_le hdim
  exact relativeDimension_le_of_mem_of_topologicalKrullDim_le _ (fun _ _ ↦ rfl) _
    (fiberClosedImmersion f i s).isClosedEmbedding.isClosed_range hrange (Set.mem_range_self w)

/-- If every fibre `Z_s` has dimension at most `r`, then `Z_s` has delta-dimension at most `r`
over `Spec κ(s)`. -/
theorem fiberClosedSubscheme_schemeDeltaDimension_le (f : X ⟶ S) [LocallyOfFiniteType f]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (r : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim ↥(pullback i (f.fiberι s)) ≤ (r : WithBot ℕ∞))
    (s : S) :
    schemeDeltaDimension (fieldChowSituation (S.residueField s))
      (fiberClosedImmersion f i s ≫ f.fiberToSpecResidueField s) ≤ ((r : ℤ) : EInt) :=
  schemeDeltaDimension_le_of_forall_relativeDimension_le
    (fieldChowSituation (S.residueField s)) (f.fiberToSpecResidueField s)
    (fiberClosedImmersion f i s)
    (relativeDimension_fiberClosedImmersion_le f i s (hdim s))

/-! ### The family of cycles -/

/-- The family `[Z/X/S]_r` of `r`-cycles on the fibres of `f` attached to a
closed subscheme `i : Z ⟶ X` whose fibres have dimension at most `r`: its member over `s` is the
cycle `[Z_s]_r` of the inverse image of `Z` in the fibre over `s`. -/
@[stacks 0H4S "the associated family"]
def familyAssociatedToClosedSubscheme (f : X ⟶ S) [LocallyOfFiniteType f] {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (r : ℕ) : FamilyOfCycles f r :=
  fun s => cycleAssociatedToClosedSubscheme (fieldChowSituation (S.residueField s))
    (f.fiberToSpecResidueField s) (fiberClosedImmersion f i s) (r : ℤ)

/-- The member of `[Z/X/S]_r` over a point `s` of the base is the cycle
`[Z_s]_r` of the inverse image of `Z` in the fibre over `s`. -/
@[stacks 0H4S "fibrewise formula"]
theorem familyAssociatedToClosedSubscheme_apply (f : X ⟶ S) [LocallyOfFiniteType f]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (r : ℕ) (s : S) :
    familyAssociatedToClosedSubscheme f i r s =
      cycleAssociatedToClosedSubscheme (fieldChowSituation (S.residueField s))
        (f.fiberToSpecResidueField s) (fiberClosedImmersion f i s) (r : ℤ) :=
  rfl

/-- The coefficient of `[Z/X/S]_r` on the fibre over `s` at the image of the generic point of an
irreducible component of `Z_s` of relative dimension `r` is that component's multiplicity. -/
theorem familyAssociatedToClosedSubscheme_apply_coeff (f : X ⟶ S) [LocallyOfFiniteType f]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (r : ℕ) (s : S)
    (ξ : genericPoints ↥(pullback i (f.fiberι s)))
    (hξ : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) (fiberClosedImmersion f i s ξ.1) = (r : ℤ)) :
    (familyAssociatedToClosedSubscheme f i r s).1 (fiberClosedImmersion f i s ξ.1) =
      componentMultiplicity (fiberClosedImmersion f i s) ξ :=
  cycleAssociatedToClosedSubscheme_apply (fieldChowSituation (S.residueField s))
    (f.fiberToSpecResidueField s) (fiberClosedImmersion f i s) (r : ℤ) ξ hξ

/-- A point of the fibre over `s` that is not the image of the generic point of a component of
`Z_s` of relative dimension `r` has coefficient zero in `[Z/X/S]_r`. -/
theorem familyAssociatedToClosedSubscheme_apply_coeff_eq_zero (f : X ⟶ S)
    [LocallyOfFiniteType f] {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (r : ℕ) (s : S)
    (x : f.fiber s)
    (hx : ¬ ∃ ξ : genericPoints ↥(pullback i (f.fiberι s)),
      fiberClosedImmersion f i s ξ.1 = x ∧
        relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
          (f.fiberToSpecResidueField s) x = (r : ℤ)) :
    (familyAssociatedToClosedSubscheme f i r s).1 x = 0 :=
  cycleAssociatedToClosedSubscheme_apply_eq_zero (fieldChowSituation (S.residueField s))
    (f.fiberToSpecResidueField s) (fiberClosedImmersion f i s) (r : ℤ) x hx

end Stacks.Chow

end

