module

public import StacksFrontier.Algebra.Homology.ShortComplex.ShortExactTransport
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection

/-!
# Stacks Tag 0C6K: the normal sequence of an effective Cartier divisor

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with inclusion `i : D ⟶ X`. Then

`0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* 𝒩_{D/X} ⟶ 0`

is short exact, the first map being multiplication by the canonical section `1_D` and the last
term the pushforward of the normal sheaf of `D` in `X`. In the decomposition of
[Stacks, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K) this is the label
`divisor_normal_sequence`: the first of the two sequences the remark derives for a divisor,
"using Lemmas 31.15.10 and 31.15.2".

## Main results

* `Stacks.Divisors.shortExact_divisor_normal`: **Stacks Tag 0C6K, the label
  `divisor_normal_sequence`.** The statement carries the identification
  `i^* 𝒪_X(D) ≅ 𝒩_{D/X}` along with the short exactness, as the source does: the sequence the
  remark writes has `i_* 𝒩_{D/X}` in its last spot, and that is the same object as
  `i_* i^* 𝒪_X(D)` only through Tag 0B3P.

## Where the two inputs come from

Both of the lemmas Tag 0C6K cites are in the library, and they are exactly the two inputs:

* **Tag 01X0** says the canonical section `1_D` of `𝒪_X(D)` is regular and that its zero scheme
  is `D` again. Fed to the regular-section sequence of this same tag, that gives
  `0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* i^* 𝒪_X(D) ⟶ 0`, which is
  `Stacks.Divisors.isShortExactUnitSequence_canonicalSections`.
* **Tag 0B3P** says the normal sheaf of `D` is `𝒪_X(D)|_D`, which is
  `Stacks.Divisors.normalSheafIsoInvertibleSheaf`.

So the content here is the transport of the first along the second, which is
`Stacks.ShortComplex.shortExact_comp_iso`: a short complex whose third object is replaced by an
isomorphic one, the third map being postcomposed with that isomorphism, is short exact as soon
as the original is.

## Implementation notes

The isomorphism of Tag 0B3P is stated with the ringed-space-level
`RingedSpaceModuleAdjunction.modulePullback` along `i.toLRSHom.toShHom`, while the sequence is
stated with the scheme-level `AlgebraicGeometry.Scheme.Modules.pullback`. The two functors are
equal by `rfl` but not syntactically, so the crossing is made once, by a `have` whose type is
written in the scheme-level spelling and whose proof is the ringed-space-level isomorphism. The
same holds of `Stacks.Divisors.invertibleSheaf`, which is indexed by
`structureSheafRing X.toRingedSpace`, against `AlgebraicGeometry.Scheme.Modules`, indexed by
`X.ringCatSheaf`. No transparency option is involved.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **Tag 0B3P's normal-sheaf clause in the scheme-level pullback spelling.** `𝒪_X(D)|_D` is the
normal sheaf of `D` in `X`, with the restriction written as
`AlgebraicGeometry.Scheme.Modules.pullback` rather than as
`RingedSpaceModuleAdjunction.modulePullback` along `i.toLRSHom.toShHom`. The two functors are
the same, so this is `Stacks.Divisors.normalSheafIsoInvertibleSheaf` read backwards at the
other spelling. -/
def pullbackInvertibleSheafIsoNormalSheaf :
    (Scheme.Modules.pullback D.subschemeι).obj (invertibleSheaf D) ≅
      normalSheaf D.subschemeι :=
  (normalSheafIsoInvertibleSheaf D).symm

/-- **Stacks Tag 0C6K, the label `divisor_normal_sequence`.** For an effective Cartier divisor
`D ⊆ X` with inclusion `i`, the normal sheaf `𝒩_{D/X}` is the restriction `i^* 𝒪_X(D)`, and

`0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* 𝒩_{D/X} ⟶ 0`

is short exact, the first map being multiplication by the canonical section `1_D` and the second
the unit of `i^* ⊣ i_*` followed by the pushforward of that identification. -/
@[stacks 0C6K "divisor_normal_sequence"]
theorem shortExact_divisor_normal :
    let i := D.subschemeι
    let L : X.Modules := invertibleSheaf D
    let N : D.subscheme.Modules := normalSheaf i
    ∃ e : (Scheme.Modules.pullback i).obj L ≅ N,
      let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
      let f : O ⟶ L := L.unitHomEquiv.symm (canonicalSections D)
      let g : L ⟶ (Scheme.Modules.pushforward i).obj N :=
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L ≫
          (Scheme.Modules.pushforward i).map e.hom
      ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact := by
  refine ⟨pullbackInvertibleSheafIsoNormalSheaf D, ?_⟩
  obtain ⟨h0, hse⟩ := isShortExactUnitSequence_canonicalSections D
  exact Stacks.ShortComplex.shortExact_comp_iso _ _ h0 hse
    ((Scheme.Modules.pushforward D.subschemeι).mapIso
      (pullbackInvertibleSheafIsoNormalSheaf D))

end Stacks.Divisors

end
