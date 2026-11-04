module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.DivisorRankStrata
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ModificationProperties
public import StacksCore.Tactic.StacksAttribute

/-!
# The locus of isomorphy in Macpherson's graph construction

Let `X` be a scheme, let `E` be a perfect object of `D(𝒪_X)` and let `U ⊆ X` be the maximal
open subscheme over which the cohomology sheaves of `E` are locally free.  Write
`p : 𝐏¹_X ⟶ X` for the projection, `𝐀¹_X = D₊(T₀) ⊆ 𝐏¹_X` for the first standard affine chart
and `(𝐏¹_X)_∞ = V₊(T₀)` for the complementary effective Cartier divisor.  Then

`(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)`

is a triple as in Situation 0F8S, and Stacks tag 0F90 lists five properties of the morphism
`b : W ⟶ 𝐏¹_X` of tag 0GTY, of the divisor `W_∞ = b⁻¹((𝐏¹_X)_∞)` and of the object
`Q = Lη_ℐ Lb^*Lp^*E` of tag 0F8U attached to that triple.

The source's construction is the data `(S, p, U)` where `S` is a triple as in Situation 0F8S
whose scheme is `𝐏¹_X` and whose divisor is `(𝐏¹_X)_∞`, where `p : S.X ⟶ X` is the projection
and where `U ⊆ X` is the locally free locus of `E`.  The divisor being `(𝐏¹_X)_∞`, the chart
`𝐀¹_X` *is*
`AlgebraicGeometry.ComplexAndDivisorSituation.divisorComplement`, the complement of the support
of `S.D`, and `𝐏¹_U` is `p ⁻¹ᵁ U`.  Clause (1) of the tag therefore reads: `b` is an
isomorphism over the union of `p ⁻¹ᵁ U` with the divisor complement.  Its half over the divisor
complement is clause (1) of tag 0F9Y and is available outright from the universal property; its
half over the locally free locus is tag 0F8W.

This file supplies the geometry that tag 0F90 adds to the section it quotes: the passage from
isomorphy over each member of a family of open subschemes to isomorphy over their supremum, the
same passage for scheme-theoretic containment in a closed subscheme, and the combination of
the two halves of clause (1) over an arbitrary open subscheme of the locally free locus.

## Main results

* `AlgebraicGeometry.isIso_morphismRestrict_of_le` and
  `AlgebraicGeometry.isIso_morphismRestrict_iSup`: a morphism which is an isomorphism over an
  open subscheme is one over every smaller open subscheme, and a morphism which is an
  isomorphism over each member of a family of open subschemes is one over their supremum.
* `AlgebraicGeometry.isIso_resLE_of_le` and `AlgebraicGeometry.isIso_resLE_sup`: the same two
  facts in the `AlgebraicGeometry.Scheme.Hom.resLE` spelling in which "isomorphism over `V`" is
  written in this section.
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_ι_eq_bot_of_le`: an ideal sheaf vanishing on an
  open subscheme vanishes on every smaller one; equivalently, scheme-theoretic containment of an
  open subscheme in a closed subscheme passes to smaller open subschemes.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isIso_resLE_sup_divisorComplement`:
  a morphism with properties (1) and (2) of tag 0GTY which is an isomorphism over the locally
  free locus `W` is an isomorphism over `V ⊔ (X ∖ D)` for every open `V ≤ W`.

## The clauses of tag 0F90

This file carries no attribute for tag 0F90.  The triple `(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)` and the
clauses of the tag are in `StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.MacphersonGraph`;
clause (1) there is `isIso_resLE_sup_divisorComplement` below with `V = p ⁻¹ᵁ U`.

## Implementation notes

"Isomorphism over `V`" is `IsIso (b.resLE V (b ⁻¹ᵁ V) le_rfl)`, the spelling of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.LocallyFreeLocus` and of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ModificationProperties`.  The two
restriction facts are proved in Mathlib's `f ∣_ V` spelling, where
`AlgebraicGeometry.IsZariskiLocalAtTarget.restrict` and `of_iSup_eq_top` apply directly and
`AlgebraicGeometry.morphismRestrictRestrict` identifies a double restriction with a single one,
and are then transported by `AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict`.

The supremum statement is proved for an arbitrary family rather than for two opens, and the
two-open case is deduced by indexing over `Bool`; the source needs only the latter.

Scheme-theoretic containment of an open subscheme `V` in the closed subscheme cut out by an
ideal sheaf `J` is `J.comap V.ι = ⊥`, which is the spelling of tag 0GTZ in
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubscheme`.

## References

* [Stacks Project, Tag 0F90](https://stacks.math.columbia.edu/tag/0F90)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0F8W](https://stacks.math.columbia.edu/tag/0F8W)
* [Stacks Project, Tag 0F8X](https://stacks.math.columbia.edu/tag/0F8X)
* [Stacks Project, Tag 0F9Y](https://stacks.math.columbia.edu/tag/0F9Y)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace StrictlyPerfect

universe u d

namespace AlgebraicGeometry

/-! ### Restriction of the locus over which a morphism is an isomorphism -/

/-- Restricting to `V` and then to the preimage of `V' ≤ V` is an isomorphism iff restricting to
`V'` is. -/
private theorem isIso_morphismRestrict_restrict_iff {X Y : Scheme.{u}} (b : X ⟶ Y)
    {V V' : Y.Opens} (h : V' ≤ V) : IsIso ((b ∣_ V) ∣_ (V.ι ⁻¹ᵁ V')) ↔ IsIso (b ∣_ V') := by
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ V') = V' := by
    simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 h]
  have := (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict b V (V.ι ⁻¹ᵁ V'))
  rw [he] at this
  exact this

/-- A morphism which is an isomorphism over an open subscheme is an isomorphism over every
smaller open subscheme: restricting to `V` and then to the preimage of `V' ≤ V` is restricting
to `V'`, and being an isomorphism is preserved by restriction. -/
theorem isIso_morphismRestrict_of_le {X Y : Scheme.{u}} (b : X ⟶ Y) {V V' : Y.Opens}
    (h : V' ≤ V) (hV : IsIso (b ∣_ V)) : IsIso (b ∣_ V') :=
  (isIso_morphismRestrict_restrict_iff b h).1
    (IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) hV _)

/-- A morphism which is an isomorphism over each member of a family of open subschemes is an
isomorphism over their supremum: the preimages of the members cover the supremum, and being an
isomorphism is Zariski local at the target. -/
theorem isIso_morphismRestrict_iSup {X Y : Scheme.{u}} (b : X ⟶ Y) {ι : Type*}
    (V : ι → Y.Opens) (hV : ∀ i, IsIso (b ∣_ V i)) : IsIso (b ∣_ (⨆ i, V i)) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun i => (⨆ i, V i).ι ⁻¹ᵁ V i) ?_
    fun i => (isIso_morphismRestrict_restrict_iff b (le_iSup V i)).2 (hV i)
  rw [← Scheme.Hom.preimage_iSup]
  simp

/-- `AlgebraicGeometry.isIso_morphismRestrict_of_le` in the `resLE` spelling of "isomorphism
over an open subscheme". -/
theorem isIso_resLE_of_le {X Y : Scheme.{u}} (b : X ⟶ Y) {V V' : Y.Opens} (h : V' ≤ V)
    (hV : IsIso (b.resLE V (b ⁻¹ᵁ V) le_rfl)) :
    IsIso (b.resLE V' (b ⁻¹ᵁ V') le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at hV ⊢
  exact isIso_morphismRestrict_of_le b h hV

/-- A morphism which is an isomorphism over each of two open subschemes is an isomorphism over
their union; this is `AlgebraicGeometry.isIso_morphismRestrict_iSup` for a family indexed by
`Bool`, in the `resLE` spelling of "isomorphism over an open subscheme". -/
theorem isIso_resLE_sup {X Y : Scheme.{u}} (b : X ⟶ Y) {V₁ V₂ : Y.Opens}
    (h₁ : IsIso (b.resLE V₁ (b ⁻¹ᵁ V₁) le_rfl))
    (h₂ : IsIso (b.resLE V₂ (b ⁻¹ᵁ V₂) le_rfl)) :
    IsIso (b.resLE (V₁ ⊔ V₂) (b ⁻¹ᵁ (V₁ ⊔ V₂)) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at h₁ h₂ ⊢
  have h : (V₁ ⊔ V₂ : Y.Opens) = ⨆ i : Bool, (if i then V₁ else V₂) := by
    rw [iSup_bool_eq]; simp
  rw [h]
  refine isIso_morphismRestrict_iSup b _ fun i => ?_
  cases i with
  | false => simpa using h₂
  | true => simpa using h₁

/-- An ideal sheaf which vanishes on an open subscheme vanishes on every smaller open
subscheme.  Read as scheme-theoretic containment: if an open subscheme `V` is contained in the
closed subscheme cut out by `J`, so is every open subscheme `V' ≤ V`. -/
theorem Scheme.IdealSheafData.comap_ι_eq_bot_of_le {Z : Scheme.{u}} (J : Z.IdealSheafData)
    {V V' : Z.Opens} (h : V' ≤ V) (hJ : J.comap V.ι = ⊥) : J.comap V'.ι = ⊥ := by
  rw [← Scheme.homOfLE_ι (X := Z) h, Scheme.IdealSheafData.comap_comp, hJ,
    Scheme.IdealSheafData.comap_bot]

namespace ComplexAndDivisorSituation

/-! ### The union of the locally free locus with the divisor complement -/

namespace IsGoodBlowup

variable {S : ComplexAndDivisorSituation.{u, d}} {X' : Scheme.{u}} {b : X' ⟶ S.X}

/-- A morphism `b : X' ⟶ X` with properties (1) and (2) of Stacks tag 0GTY which is an
isomorphism over the locally free locus `W` is an isomorphism over `V ⊔ (X ∖ D)` for every open
subscheme `V ≤ W`.

Over `V` this is the hypothesis `hW` restricted along `hV`, by
`AlgebraicGeometry.isIso_resLE_of_le`; over `X ∖ D` it is clause (1) of Stacks tag 0F9Y,
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isIso_resLE_divisorComplement`; and
the two are combined by `AlgebraicGeometry.isIso_resLE_sup`.

This is the shape in which clause (1) of Stacks tag 0F90 would be read, with `V = p ⁻¹ᵁ U` for
the projection `p : 𝐏¹_X ⟶ X` and the locally free locus `U` of `E`; the module documentation
explains what is still missing before the hypothesis `hW` can be removed. -/
theorem isIso_resLE_sup_divisorComplement (hb : S.IsGoodBlowup b)
    (hW : IsIso (b.resLE S.locallyFreeLocus (b ⁻¹ᵁ S.locallyFreeLocus) le_rfl))
    {V : S.X.Opens} (hV : V ≤ S.locallyFreeLocus) :
    IsIso (b.resLE (V ⊔ S.divisorComplement) (b ⁻¹ᵁ (V ⊔ S.divisorComplement)) le_rfl) :=
  isIso_resLE_sup b (isIso_resLE_of_le b hV hW) hb.isIso_resLE_divisorComplement

end IsGoodBlowup

end ComplexAndDivisorSituation

end AlgebraicGeometry

end
