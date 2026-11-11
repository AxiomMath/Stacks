module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.RelativeSpec
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The size of a relative spectrum

The *size* of a scheme (`AlgebraicGeometry.Scheme.size`, Stacks Section 000H) is the maximum of `ℵ₀`, the
number of its affine opens, and the cardinalities of its rings of sections over affine opens.
Tag 000R lists the constructions under which a size bound is preserved; the relative spectrum of
a quasi-coherent algebra, Tag 01LP, is not among them, and this file supplies the missing clause:
for a quasi-coherent sheaf of commutative `𝒪_S`-algebras `A`,

`size (relativeSpec A) ≤ c` whenever `size S ≤ c` and `#A(U) ≤ c` for every affine open `U`.

This is the bound a big site needs in order to contain the relative spectrum of an algebra over
one of its objects, and it is what makes the relative spectrum usable as a chart in the
construction of a relative spectrum over an algebraic space.

## Main results

* `Stacks.AffineAlgebraEquivalence.size_coe_preimage_relativeSpecToBase`: the open subscheme of
  the relative spectrum over an affine open `U` of the base has size `max ℵ₀ #A(U)`.
* `Stacks.AffineAlgebraEquivalence.size_relativeSpec_le`: the size bound for the relative
  spectrum.
* `Stacks.AffineAlgebraEquivalence.size_relativeSpec_lt`: the same read against a strong prelimit
  cutoff, in the shape Tag 000R (6) is applied in.

## Implementation notes

The argument is clause (6) of Tag 000R — a small open covering by small opens — with each member
of the covering handled by Tag 000P for a spectrum, `AlgebraicGeometry.Scheme.size_Spec`.  It is
the same argument as `AlgebraicGeometry.Scheme.Hom.size_normalization_le`, run for an arbitrary
quasi-coherent algebra instead of for the integral closure of `𝒪_Y` in `f_* 𝒪_X`: there the
covering of the normalization is by the preimages of the affine opens of the target and the
sections over a member are the integral closure of `Γ(Y, U)` in `Γ(X, f⁻¹U)`, here the covering
is by the preimages of the affine opens of the base and the sections over a member are `A(U)`.

No cardinality bound on `A` is extracted here, and none is available: quasi-coherence carries
none.  The bound on `#A(U)` is a hypothesis, which is what makes the statement usable — a caller
with a concrete algebra, such as the integral closure of `𝒪_X` in `f_* 𝒪_Y` of Tag 0821, bounds
its own sections and gets the containment of the relative spectrum in return.

Unlike `AlgebraicGeometry.Scheme.Hom.size_normalization_le`, which identifies the sections of
the normalization over a member of the covering with a ring and then bounds that ring, this file
identifies the *open subscheme* over a member with `Spec A(U)`.  That is available with no sheaf
computation at all: the preimage of an affine open `U` is the range of the open immersion
`Spec A(U) ⟶ relativeSpec A` by
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι`, and an open
immersion is an isomorphism onto its range.

## References

* [Stacks Project, Section 000H](https://stacks.math.columbia.edu/tag/000H)
* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal Opposite
open TopologicalSpace

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {S : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf S)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]

/-- The size of the open subscheme of the relative spectrum over an affine open of the base,
indexed by the directed affine cover. -/
private theorem size_coe_preimage_toBase (U : S.directedAffineCover.I₀) :
    ((((relativeSpecGluingData A).toBase ⁻¹ᵁ (coverOpen U : S.Opens)) : Scheme.{u})).size =
      max ℵ₀ #(Stacks.RelativeSpec.AlgebraSheaf.sections A (coverOpen U : S.Opens)) := by
  have hrange : (S.directedAffineCover.f U).opensRange = (coverOpen U : S.Opens) :=
    Scheme.Opens.opensRange_ι _
  have hpre := (relativeSpecGluingData A).toBase_preimage_eq_opensRange_ι U
  rw [hrange] at hpre
  rw [hpre, ← Scheme.size_congr (colimit.ι (relativeSpecGluingData A).functor U).isoOpensRange]
  exact Scheme.size_Spec _

/-- **The open subscheme of the relative spectrum over an affine open of the base has size
`max ℵ₀ #A(U)`.**

The preimage of `U` is the range of the open immersion `Spec A(U) ⟶ relativeSpec A` indexed by
`U` in the directed affine cover, so it is isomorphic to `Spec A(U)`, whose size is
`max ℵ₀ #A(U)` by Tag 000P. -/
theorem size_coe_preimage_relativeSpecToBase (U : S.affineOpens) :
    (((relativeSpecToBase A ⁻¹ᵁ (U : S.Opens)) : Scheme.{u})).size =
      max ℵ₀ #(Stacks.RelativeSpec.AlgebraSheaf.sections A (U : S.Opens)) :=
  size_coe_preimage_toBase A U

/-- **The relative spectrum of a quasi-coherent algebra has size bounded by that of the base and
of the algebra's sections.**  If `size S ≤ c` and `#A(U) ≤ c` for every affine open `U` of `S`,
then `size (relativeSpec A) ≤ c`.

This is clause (6) of Tag 000R applied to the covering of the relative spectrum by the preimages
of the affine opens of `S`, whose index type is `S.affineOpens` and whose members have size
`max ℵ₀ #A(U)` by `Stacks.AffineAlgebraEquivalence.size_coe_preimage_relativeSpecToBase`. -/
theorem size_relativeSpec_le {c : Cardinal.{u}} (hS : S.size ≤ c)
    (hA : ∀ U : S.affineOpens,
      #(Stacks.RelativeSpec.AlgebraSheaf.sections A (U : S.Opens)) ≤ c) :
    (relativeSpec A).size ≤ c := by
  have : Nonempty S.affineOpens := ⟨⟨⊥, isAffineOpen_bot S⟩⟩
  refine (Scheme.size_le_of_iSup_eq_top
      (fun U : S.affineOpens => relativeSpecToBase A ⁻¹ᵁ (U : S.Opens))
      ((relativeSpecToBase A).iSup_preimage_eq_top (iSup_affineOpens_eq_top S))).trans
    (max_le (S.mk_affineOpens_le_size.trans hS) (ciSup_le' fun U => ?_))
  rw [size_coe_preimage_relativeSpecToBase A U]
  exact max_le (S.aleph0_le_size.trans hS) (hA U)

/-- **Tag 000R (6) for a relative spectrum.**  Let `κ` be an uncountable strong prelimit and `T`
a scheme of size below `κ`.  If the base and the sections of the algebra over every affine open
are bounded by `size(T) ^ ℵ₀`, then the relative spectrum has size below `κ`.

This is the shape in which the size bound is read against the cutoff of a big site: a strong
prelimit above `ℵ₀` is closed under `lam ↦ lam ^ ℵ₀`. -/
theorem size_relativeSpec_lt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) {T : Scheme.{u}} (hT : T.size < κ)
    (hS : S.size ≤ T.size ^ ℵ₀)
    (hA : ∀ U : S.affineOpens,
      #(Stacks.RelativeSpec.AlgebraSheaf.sections A (U : S.Opens)) ≤ T.size ^ ℵ₀) :
    (relativeSpec A).size < κ :=
  (size_relativeSpec_le A hS hA).trans_lt (power_aleph0_lt_of_isStrongPrelimit hκ hsl hT)

end Stacks.AffineAlgebraEquivalence

end
