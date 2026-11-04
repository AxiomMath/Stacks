module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ClosedSubschemeProjection
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ProjectiveLineSections
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Dimensions of a base-changed family over the projective line

Let `B` be a flat base-change situation of Chow homology with dimension shift `c`, let
`f : X ⟶ S` be locally of finite type and let `W ⊆ X ×_S 𝐏¹_S` be a closed subscheme. Its base
change `Stacks.Chow.baseChangedFamily` is a closed subscheme of `X' ×_{S'} 𝐏¹_{S'}`, and this
file bounds the three dimensions a consumer of Stacks 02S5 has to know about it:

* the relative dimension of the base change over the new base, at every point;
* the delta-dimension of its zero fibre;
* the delta-dimension of its infinity fibre.

Together with the associated-point condition — not proved here — these are exactly the
hypotheses of `Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent` and of
`Stacks.Chow.fibreDifference_isRationallyEquivalentToZeroWithin` for the base-changed family,
and they are what a cycle-level treatment of
[Stacks, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ) needs on the new base.

## Main results

* `Stacks.Chow.isPullback_familyBase_baseChangedFamily` — the base-changed family really is the
  base change of `W` along `g`, as a cartesian square over `g`.
* `Stacks.Chow.relativeDimension_familyBase_baseChangedFamily_le` — if `W` is integral of
  relative dimension `k + 1` over the old base, every point of the base change has relative
  dimension at most `k + c + 1` over the new base.
* `Stacks.Chow.schemeDeltaDimension_baseChange_comap_le` — the bound of Stacks 0FVI part (1) in
  the `AlgebraicGeometry.Scheme.IdealSheafData.comap` spelling: the inverse image along
  `X' ⟶ X` of a closed subscheme of delta-dimension at most `k` has delta-dimension at most
  `k + c`.
* `Stacks.Chow.schemeDeltaDimension_zeroFiber_baseChangedFamily_le`,
  `Stacks.Chow.schemeDeltaDimension_infinityFiber_baseChangedFamily_le` — the two fibre bounds.

## Implementation notes

The relative dimension bound is Stacks 0FVH read through
`Stacks.Chow.schemeDeltaDimension_baseChange_le`: `W` being integral, its delta-dimension over
the old base is `k + 1`, so the delta-dimension of `W ×_S S'` over the new base is at most
`k + 1 + c`; the base-changed family *is* `W ×_S S'`, by the cartesian square pasted from the
square of `Stacks.Chow.isPullback_projectiveLineProductBaseChange` and the square exhibiting an
inverse-image closed subscheme as a fibre product. Delta-dimension is transported across the
resulting isomorphism by `Stacks.Chow.schemeDeltaDimension_comp_iso`, and a delta-dimension
bound becomes a bound at every point by
`Stacks.Chow.relativeDimension_le_of_schemeDeltaDimension_le` at the identity.

The two fibre bounds are the `comap` form of Stacks 0FVI part (1) applied to the fibres of `W`
themselves: by `Stacks.Chow.zeroFiber_baseChangedFamily` the zero fibre of the base-changed
family is the inverse image along `X' ⟶ X` of the zero fibre of `W`, whose delta-dimension is at
most `k` by `Stacks.Chow.schemeDeltaDimension_zeroFiber_le`.

## References

* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVH](https://stacks.math.columbia.edu/tag/0FVH)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### An inverse-image closed subscheme as a fibre product -/

/-- The inverse image of a closed subscheme along a morphism is the fibre product of that
morphism with the closed subscheme, as a cartesian square. -/
@[ega "IV 8.6.2" "more general"]
private theorem isPullback_subschemeι_comap {A Y : Scheme.{u}} (I : Y.IdealSheafData)
    (s : A ⟶ Y) :
    IsPullback ((I.comapIso s).hom ≫ pullback.snd s I.subschemeι) (I.comap s).subschemeι
      I.subschemeι s := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso s) (I.comapIso_hom_fst s) rfl).flip
  rw [← I.comapIso_hom_fst s, Category.assoc, pullback.condition, Category.assoc]

/-! ### The base-changed family is a base change -/

variable (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}} (f : X ⟶ B.base.S)
  [LocallyOfFiniteType f] (W : (projectiveLineProduct f).IdealSheafData)

omit [LocallyOfFiniteType f] in
/-- **The base-changed family is the base change of `W`.** The square

```
W ×_S S' ---> W
   |          |
   v          v
   S' -- g --> S
```

is cartesian, the vertical maps being the structure morphisms of `W` and of its base change as
closed subschemes of the two families of projective lines. -/
theorem isPullback_familyBase_baseChangedFamily :
    IsPullback
      ((W.comapIso (projectiveLineProductBaseChange f B.g)).hom ≫
        pullback.snd (projectiveLineProductBaseChange f B.g) W.subschemeι)
      (familyBase (pullback.snd f B.g) (baseChangedFamily f B.g W)) (familyBase f W) B.g :=
  (isPullback_subschemeι_comap W (projectiveLineProductBaseChange f B.g)).paste_vert
    (isPullback_projectiveLineProductBaseChange f B.g)

/-! ### The relative dimension of the base-changed family -/

/-- **The relative dimension bound for a base-changed family.** If `W` is integral of relative
dimension `k + 1` at its generic points over the old base, then every point of its base change
has relative dimension at most `k + c + 1` over the new base.

This is the first hypothesis of Stacks 02S5 for the base-changed family. -/
theorem relativeDimension_familyBase_baseChangedFamily_le [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension B.base.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (ζ : (baseChangedFamily f B.g W).subscheme) :
    relativeDimension B.baseChange.dimensionFunction
        (familyBase (pullback.snd f B.g) (baseChangedFamily f B.g W)) ζ ≤ (k + B.c) + 1 := by
  have hsq := isPullback_familyBase_baseChangedFamily B f W
  have hbase : schemeDeltaDimension B.baseChange (pullback.snd (familyBase f W) B.g) ≤
      ((k + 1 + B.c : ℤ) : EInt) :=
    schemeDeltaDimension_baseChange_le B (familyBase f W)
      (le_of_eq (schemeDeltaDimension_familyBase B.base f W hDim))
  have hle := relativeDimension_le_of_schemeDeltaDimension_le B.baseChange
    (pullback.snd (familyBase f W) B.g) (𝟙 _) (k := k + 1 + B.c) (by simpa using hbase)
    (hsq.isoPullback.hom ζ)
  have hmor : familyBase (pullback.snd f B.g) (baseChangedFamily f B.g W) =
      hsq.isoPullback.hom ≫ pullback.snd (familyBase f W) B.g := hsq.isoPullback_hom_snd.symm
  have hrd : relativeDimension B.baseChange.dimensionFunction
      (familyBase (pullback.snd f B.g) (baseChangedFamily f B.g W)) ζ =
      relativeDimension B.baseChange.dimensionFunction
        (hsq.isoPullback.hom ≫ pullback.snd (familyBase f W) B.g) ζ :=
    congrArg (fun m ↦ relativeDimension B.baseChange.dimensionFunction m ζ) hmor
  have hζ : relativeDimension B.baseChange.dimensionFunction
      (familyBase (pullback.snd f B.g) (baseChangedFamily f B.g W)) ζ ≤ k + 1 + B.c := by
    rw [hrd, relativeDimension_comp_closedImmersion B.baseChange.dimensionFunction
      hsq.isoPullback.hom (pullback.snd (familyBase f W) B.g) ζ]
    simpa using hle
  omega

/-! ### The dimension bound of Stacks 0FVI (1) in the `comap` spelling -/

/-- **Stacks 0FVI, part (1), dimension bound, for an inverse-image ideal sheaf.** The inverse
image along the projection `X' ⟶ X` of a closed subscheme of `X` of delta-dimension at most `k`
has delta-dimension at most `k + c` over the new base.

This is `Stacks.Chow.schemeDeltaDimension_baseChange_closedSubscheme_le` read at the closed
subscheme `AlgebraicGeometry.Scheme.IdealSheafData.comap`, which is the spelling in which fibres
of a base-changed family arrive; nothing of Stacks 0FVI is reproved. -/
theorem schemeDeltaDimension_baseChange_comap_le (I : X.IdealSheafData) {k : ℤ}
    (hI : schemeDeltaDimension B.base (I.subschemeι ≫ f) ≤ (k : EInt)) :
    schemeDeltaDimension B.baseChange
        ((I.comap (pullback.fst f B.g)).subschemeι ≫ pullback.snd f B.g) ≤
      ((k + B.c : ℤ) : EInt) := by
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le B.baseChange
    (pullback.snd f B.g) (I.comap (pullback.fst f B.g)).subschemeι fun w ↦ ?_
  obtain ⟨w', hw'⟩ : (I.comap (pullback.fst f B.g)).subschemeι w ∈
      Set.range (pullback.snd I.subschemeι (pullback.fst f B.g)) := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨(I.comapIso (pullback.fst f B.g)).hom ≫
        pullback.snd (pullback.fst f B.g) I.subschemeι |>.base w,
      congrArg (fun m : (I.comap (pullback.fst f B.g)).subscheme ⟶ X => m w)
        (isPullback_subschemeι_comap I (pullback.fst f B.g)).w⟩
  rw [← hw']
  exact relativeDimension_le_of_schemeDeltaDimension_le B.baseChange (pullback.snd f B.g)
    (pullback.snd I.subschemeι (pullback.fst f B.g))
    (schemeDeltaDimension_baseChange_closedSubscheme_le B f I.subschemeι hI) w'

/-! ### The two fibre bounds for a base-changed family -/

/-- **The zero-fibre bound for a base-changed family.** If `W` is integral of relative dimension
`k + 1` at its generic points over the old base and is not contained in the image of the zero
section, then the zero fibre of its base change has delta-dimension at most `k + c` over the
new base.

This is the second hypothesis of Stacks 02S5 for the base-changed family. The zero fibre of the
base change is the inverse image of the zero fibre of `W`, whose delta-dimension is at most `k`
by `Stacks.Chow.schemeDeltaDimension_zeroFiber_le`. -/
theorem schemeDeltaDimension_zeroFiber_baseChangedFamily_le [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension B.base.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f)) :
    schemeDeltaDimension B.baseChange
        ((zeroFiber (pullback.snd f B.g) (baseChangedFamily f B.g W)).subschemeι ≫
          pullback.snd f B.g) ≤ ((k + B.c : ℤ) : EInt) := by
  rw [zeroFiber_baseChangedFamily]
  exact schemeDeltaDimension_baseChange_comap_le B f (zeroFiber f W)
    (schemeDeltaDimension_zeroFiber_le B.base f W hDim h₀)

/-- **The infinity-fibre bound for a base-changed family.** The infinity-section twin of
`Stacks.Chow.schemeDeltaDimension_zeroFiber_baseChangedFamily_le`, the third hypothesis of
Stacks 02S5 for the base-changed family. -/
theorem schemeDeltaDimension_infinityFiber_baseChangedFamily_le [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension B.base.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    schemeDeltaDimension B.baseChange
        ((infinityFiber (pullback.snd f B.g) (baseChangedFamily f B.g W)).subschemeι ≫
          pullback.snd f B.g) ≤ ((k + B.c : ℤ) : EInt) := by
  rw [infinityFiber_baseChangedFamily]
  exact schemeDeltaDimension_baseChange_comap_le B f (infinityFiber f W)
    (schemeDeltaDimension_infinityFiber_le B.base f W hDim hInf)

end Stacks.Chow

end
