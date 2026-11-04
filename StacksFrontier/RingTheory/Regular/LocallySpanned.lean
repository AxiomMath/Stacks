module

public import StacksFrontier.RingTheory.Regular.Ideal
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.MonomialComparison

/-!
# Ideals locally spanned by a family with a prescribed property

The regular, Koszul-regular, `H₁`-regular and quasi-regular ideals of Stacks tag 07CV are all
defined by the same scheme: an ideal `I` of `R` has the property when, at every prime `p`
containing `I`, some principal localization `R_g` with `g ∉ p` has `I R_g` spanned by a finite
family with the corresponding property. This file isolates that scheme as
`Ideal.IsLocallySpannedBy`, taking the property of finite families as a parameter, and identifies
the three predicates of Stacks tag 07CV that are relevant to the regularity conditions on an
immersion as instances of it.

Naming the common shape is what makes it possible to treat the three conditions of Stacks tag
063D uniformly when they are compared, on an affine open, with the kernel of a morphism on
sections; that comparison is the affine half of Stacks tag 0694.

## Main definitions

* `Ideal.IsLocallySpannedBy`: the ideal is, locally on its zero locus, spanned by a finite family
  satisfying the given property.

## Main results

* `Ideal.isKoszulRegular_iff_isLocallySpannedBy`, `Ideal.isH1Regular_iff_isLocallySpannedBy` and
  `Ideal.isQuasiregularIdeal_iff_isLocallySpannedBy`: parts (2), (3) and (4) of Stacks tag 07CV
  are instances of the scheme.

## Implementation notes

For the quasi-regular condition the identification is not definitional. The predicate
`Quasiregular.IsQuasiregularIdeal` is built on `Quasiregular.IsQuasiregularSeq`, whereas the
quasi-regular condition on an ideal sheaf is built on `RingTheory.Sequence.IsQuasiRegular`
applied to the list spelled out by the family; the two sequence predicates are identified by
`Quasiregular.isQuasiregularSeq_iff_isQuasiRegular`. The instance recorded here is the latter,
list-based one, the form used for ideal sheaves.

## References

* [Stacks Project, Definition 10.69.1 (Tag 07CV)](https://stacks.math.columbia.edu/tag/07CV)
-/

@[expose] public section

namespace Ideal

universe u

variable {R : Type u} [CommRing R]

/-- **An ideal locally spanned by a family with a prescribed property.** For `Seq` a property of
finite families of elements of a commutative ring, the ideal `I` of `R` is locally spanned by a
`Seq`-family when, at every prime `p` containing `I`, there is `g ∉ p` such that the extension of
`I` to the principal localization `R_g` is spanned by a finite family satisfying `Seq`.

This is the common shape of the four conditions of Stacks tag 07CV. -/
def IsLocallySpannedBy (Seq : ∀ {A : Type u} [CommRing A] {r : ℕ}, (Fin r → A) → Prop)
    (I : Ideal R) : Prop :=
  ∀ p : PrimeSpectrum R, I ≤ p.asIdeal →
    ∃ g : R, g ∉ p.asIdeal ∧
      ∃ (r : ℕ) (f : Fin r → Localization.Away g), Seq f ∧
        I.map (algebraMap R (Localization.Away g)) = Ideal.span (Set.range f)

/-- **Part (2) of Stacks tag 07CV is an instance of the scheme.** A Koszul-regular ideal is one
locally spanned by a Koszul-regular family. -/
theorem isKoszulRegular_iff_isLocallySpannedBy (I : Ideal R) :
    I.IsKoszulRegular ↔ I.IsLocallySpannedBy (fun f => Koszul.IsKoszulRegular f) :=
  Iff.rfl

/-- **Part (3) of Stacks tag 07CV is an instance of the scheme.** An `H₁`-regular ideal is one
locally spanned by an `H₁`-regular family. -/
theorem isH1Regular_iff_isLocallySpannedBy (I : Ideal R) :
    I.IsH1Regular ↔ I.IsLocallySpannedBy (fun f => Koszul.IsH1Regular f) :=
  Iff.rfl

/-- **Part (4) of Stacks tag 07CV is an instance of the scheme.** A quasi-regular ideal is one
locally spanned by a family whose list is a quasi-regular sequence; the two spellings of
quasi-regularity of a finite family agree by
`Quasiregular.isQuasiregularSeq_iff_isQuasiRegular`. -/
theorem isQuasiregularIdeal_iff_isLocallySpannedBy (I : Ideal R) :
    Quasiregular.IsQuasiregularIdeal I ↔
      I.IsLocallySpannedBy
        (fun {A} _ _ f => RingTheory.Sequence.IsQuasiRegular A (List.ofFn f)) := by
  refine forall_congr' fun p => imp_congr_right fun _ => ?_
  exact exists_congr fun g => and_congr_right fun _ => exists_congr fun r =>
    exists_congr fun f =>
      and_congr_left fun _ => Quasiregular.isQuasiregularSeq_iff_isQuasiRegular f

end Ideal

end
