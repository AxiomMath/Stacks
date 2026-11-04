module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.PiecePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow

/-!
# Restriction to an open subscheme commutes with proper pushforward

Let `p : Y' ⟶ Y` be a proper morphism of schemes locally of finite type over the base scheme of
chapter 42 of the Stacks Project, and let `V ⊆ Y` be an open subscheme. Write `W = p^{-1}(V)` and
let `p|_V : W ⟶ V` be the restriction of `p`, so that

  `W --W.ι--> Y'`
  `|p|_V       |p`
  `V --V.ι--> Y`

is cartesian. Restriction of cycles to an open subscheme then commutes with proper pushforward:

  `(p_* β)|_V = (p|_V)_* (β|_W)`   in   `Z_k(V)`.

This is the special case of Stacks 02RG — flat pullback commutes with proper pushforward in a
cartesian square — in which the flat morphism is the inclusion of an open subscheme. The general
statement is not in this repository; this case is, and it is proved directly from the coefficient
formula of Stacks 02R4 rather than by specializing anything.

The reason it is cheap is that an open immersion is a base change along which *fibres do not
change*. Over a point `z` of `V` the fibre of `p|_V` is carried bijectively onto the fibre of `p`
by `W.ι`, because a point of `Y'` lying over a point of `V` already lies in `W`; the residue
degree is unchanged because the residue field map of an open immersion is an isomorphism; and
delta-dimension is unchanged by `Stacks.Chow.relativeDimension_opensι_comp`. So the locally finite
sum defining the pushforward has the same terms on both sides.

## Main definitions

* `Stacks.Chow.chowGroupOpensRestrict` — restriction of Chow classes to an open subscheme,
  `A_k(X) ⟶ A_k(V)`, granted Stacks 02S1 along the inclusion of that subscheme.

## Main results

* `Stacks.Chow.opensι_morphismRestrict_base`,
  `Stacks.Chow.image_preimage_morphismRestrict` — the fibre of the restricted morphism over a
  point of `V` is the fibre of the morphism itself, carried into `W` by `W.ι`.
* `Stacks.Chow.opensRestrictCycle_properPushforward`,
  `Stacks.Chow.cycleGroupOpensRestrict_properPushforward` — **the open-immersion case of Stacks
  02RG**, on coefficient functions and on cycle groups.
* `Stacks.Chow.chowGroupOpensRestrict_properChowPushforward` — the same identity on Chow groups.

## Implementation notes

### Why the single-open restriction is carried here and not derived from the clopen one

`Stacks.Chow.chowGroupClopenRestrict` already restricts Chow classes to the pieces of a
decomposition into open and closed subschemes, so its composite with a projection restricts to one
piece. That route is not taken, because it needs the whole of
`Stacks.Chow.RationalEquivalenceDecomposes` — an `iff` quantified over every cycle — whereas
restriction to a *single* open subscheme needs only the forward half, which is Stacks 02S1 along
the inclusion of that subscheme. `Stacks.Chow.chowGroupOpensRestrict` therefore takes exactly the
standing hypothesis `Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalence` that this
development threads everywhere, and nothing about a decomposition. It also does not require `V` to
be closed; only the proper pushforward in the results below requires properness of `p`, which is a
hypothesis on `p` and not on `V`.

### Degrees, and why there is no cast here

Restriction to an open subscheme *is* flat pullback along the inclusion, of relative dimension
zero (`Stacks.Chow.cycleGroupOpensRestrict_eq_flatPullback`). Writing it as
`Stacks.Chow.flatPullbackChow` would therefore land in degree `k + (0 : ℕ)` rather than `k` and
force a transport of the degree at every use, as it does in
`Stacks.Chow.cycleGroupOpensRestrict_mem_rationalEquivalences`. Defining
`Stacks.Chow.chowGroupOpensRestrict` directly as the map induced on quotients by
`Stacks.Chow.cycleGroupOpensRestrict` keeps the degree syntactically `k` on both sides, so the
identity below is an equation and not a `HEq`.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow

variable {Y' Y : Scheme.{u}}

/-! ### The fibres of a morphism restricted over an open subscheme of its target -/

/-- The inclusion of an open subscheme is injective on points. -/
theorem opensι_base_injective (V : Y.Opens) : Function.Injective V.ι.base :=
  fun _ _ h ↦ Subtype.ext h

/-- The square identifying the restriction of `p` over an open subscheme `V` of its target, read
on points: the image in `Y` of the value of `p|_V` at a point of `p^{-1}(V)` is the value of `p`
at that point of `Y'`. -/
theorem opensι_morphismRestrict_base (p : Y' ⟶ Y) (V : Y.Opens)
    (w : ((p ⁻¹ᵁ V) : Scheme.{u})) :
    V.ι.base ((p ∣_ V).base w) = p.base ((p ⁻¹ᵁ V).ι.base w) := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-- **The fibres of a morphism do not change when it is restricted over an open subscheme of its
target.** The fibre of `p|_V` over a point `z` of `V` is carried bijectively onto the fibre of `p`
over the image of `z` by the inclusion of `p^{-1}(V)`.

The content is the inclusion from right to left: a point of `Y'` whose image is in `V` already
lies in `p^{-1}(V)`. This is what makes the open-immersion case of Stacks 02RG a coefficient
computation. -/
theorem image_preimage_morphismRestrict (p : Y' ⟶ Y) (V : Y.Opens) (z : (V : Scheme.{u})) :
    (p ⁻¹ᵁ V).ι.base '' ((p ∣_ V).base ⁻¹' {z}) = p.base ⁻¹' {V.ι.base z} := by
  ext x
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [← opensι_morphismRestrict_base p V w, hw]
  · intro hx
    have hxV : x ∈ (↑(p ⁻¹ᵁ V) : Set Y') := (hx ▸ z.2 : p.base x ∈ V)
    rw [← Scheme.Opens.range_ι (p ⁻¹ᵁ V)] at hxV
    obtain ⟨w, rfl⟩ := hxV
    exact ⟨w, opensι_base_injective V ((opensι_morphismRestrict_base p V w).trans hx), rfl⟩

/-! ### Restriction commutes with proper pushforward -/

/-- The restriction of `p` over an open subscheme `V` of its target is a morphism over the base:
`p|_V` followed by the inclusion of `V` is the inclusion of `p^{-1}(V)` followed by `p`. -/
theorem morphismRestrict_comp_opensι_comp {S : Scheme.{u}} (p : Y' ⟶ Y) (V : Y.Opens)
    (sY' : Y' ⟶ S) (sY : Y ⟶ S) (hp : p ≫ sY = sY') :
    (p ∣_ V) ≫ (V.ι ≫ sY) = (p ⁻¹ᵁ V).ι ≫ sY' := by
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hp]

variable (C : ChowSituation.{u}) (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY'] (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (p : Y' ⟶ Y) [IsProper p] (hp : p ≫ sY = sY') (V : Y.Opens) (k : ℤ)

/-- **The open-immersion case of Stacks 02RG, on coefficient functions.** Pushing a cycle forward
along a proper morphism and restricting the result to an open subscheme `V` of the target is the
same as restricting to `p^{-1}(V)` and pushing forward along the restricted morphism.

Both sides are the locally finite sum of Stacks 02R4 over the fibre, and
`Stacks.Chow.image_preimage_morphismRestrict` identifies the two fibres. The weights agree because
the residue degree of the restricted morphism is the residue degree of `p`
(`Stacks.Chow.residueDegree_morphismRestrict`) and delta-dimension does not see an open subscheme
(`Stacks.Chow.relativeDimension_opensι_comp`). -/
theorem opensRestrictCycle_properPushforward (β : CycleGroup C sY' k) :
    opensRestrictCycle V (properPushforward C sY' sY p hp k β).1 =
      (properPushforward C ((p ⁻¹ᵁ V).ι ≫ sY') (V.ι ≫ sY) (p ∣_ V)
        (morphismRestrict_comp_opensι_comp p V sY' sY hp) k
        (cycleGroupOpensRestrict C sY' (p ⁻¹ᵁ V) k β)).1 := by
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [opensRestrictCycle_apply, properPushforward_apply, properPushforward_apply,
    ← image_preimage_morphismRestrict p V z,
    finsum_mem_image (Set.injOn_of_injective (opensι_base_injective (p ⁻¹ᵁ V)))]
  refine finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_
  rw [cycleGroupOpensRestrict_apply, relativeDimension_opensι_comp,
    relativeDimension_opensι_comp, opensι_morphismRestrict_base,
    residueDegree_morphismRestrict]

/-- **The open-immersion case of Stacks 02RG, on cycle groups.** -/
theorem cycleGroupOpensRestrict_properPushforward (β : CycleGroup C sY' k) :
    cycleGroupOpensRestrict C sY V k (properPushforward C sY' sY p hp k β) =
      properPushforward C ((p ⁻¹ᵁ V).ι ≫ sY') (V.ι ≫ sY) (p ∣_ V)
        (morphismRestrict_comp_opensι_comp p V sY' sY hp) k
        (cycleGroupOpensRestrict C sY' (p ⁻¹ᵁ V) k β) :=
  Subtype.ext (opensRestrictCycle_properPushforward C sY' sY p hp V k β)

/-! ### Restriction of Chow classes, and the same identity there -/

variable {X : Scheme.{u}}

/-- **Restriction of Chow classes to an open subscheme**, `A_k(X) ⟶ A_k(V)`, granted Stacks 02S1
along the inclusion of that subscheme.

Restriction of cycles preserves rational equivalence precisely under that hypothesis, by
`Stacks.Chow.cycleGroupOpensRestrict_mem_rationalEquivalences`, so this is the induced map on
quotients. See the implementation notes for why it is not obtained from
`Stacks.Chow.chowGroupClopenRestrict`. -/
def chowGroupOpensRestrict (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (V : X.Opens) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (V.ι ≫ f) f V.ι rfl 0
      (relativeDimension_opensι V) k) :
    chowGroup C f k →+ chowGroup C (V.ι ≫ f) k :=
  QuotientAddGroup.map (rationalEquivalences C f k) (rationalEquivalences C (V.ι ≫ f) k)
    (cycleGroupOpensRestrict C f V k)
    fun _ hc ↦ cycleGroupOpensRestrict_mem_rationalEquivalences C f V k hfac hc

/-- Restricting the Chow class of a cycle to an open subscheme gives the class of the restricted
cycle. -/
@[simp]
theorem chowGroupOpensRestrict_mk (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (V : X.Opens) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (V.ι ≫ f) f V.ι rfl 0
      (relativeDimension_opensι V) k) (c : CycleGroup C f k) :
    chowGroupOpensRestrict C f V k hfac (QuotientAddGroup.mk' (rationalEquivalences C f k) c) =
      QuotientAddGroup.mk' (rationalEquivalences C (V.ι ≫ f) k)
        (cycleGroupOpensRestrict C f V k c) :=
  rfl

/-- **The open-immersion case of Stacks 02RG, on Chow groups.** Pushing a Chow class forward along
a proper morphism and restricting the result to an open subscheme of the target is the same as
restricting and pushing forward along the restricted morphism.

Both maps are induced on quotients by the corresponding maps of cycle groups, so this is
`Stacks.Chow.cycleGroupOpensRestrict_properPushforward` read on representatives. -/
theorem chowGroupOpensRestrict_properChowPushforward
    (hfacV : FlatPullbackFactorsThroughRationalEquivalence C (V.ι ≫ sY) sY V.ι rfl 0
      (relativeDimension_opensι V) k)
    (hfacW : FlatPullbackFactorsThroughRationalEquivalence C ((p ⁻¹ᵁ V).ι ≫ sY') sY'
      (p ⁻¹ᵁ V).ι rfl 0 (relativeDimension_opensι (p ⁻¹ᵁ V)) k)
    (hfacP : ProperPushforwardFactorsThroughRationalEquivalence C sY' sY p hp k)
    (hfacP' : ProperPushforwardFactorsThroughRationalEquivalence C ((p ⁻¹ᵁ V).ι ≫ sY')
      (V.ι ≫ sY) (p ∣_ V) (morphismRestrict_comp_opensι_comp p V sY' sY hp) k)
    (α : chowGroup C sY' k) :
    chowGroupOpensRestrict C sY V k hfacV
        (properChowPushforward C sY' sY p hp k hfacP α) =
      properChowPushforward C ((p ⁻¹ᵁ V).ι ≫ sY') (V.ι ≫ sY) (p ∣_ V)
        (morphismRestrict_comp_opensι_comp p V sY' sY hp) k hfacP'
        (chowGroupOpensRestrict C sY' (p ⁻¹ᵁ V) k hfacW α) := by
  induction α using QuotientAddGroup.induction_on with
  | H β =>
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C (V.ι ≫ sY) k))
      (cycleGroupOpensRestrict_properPushforward C sY' sY p hp V k β)

end Stacks.Chow

end
