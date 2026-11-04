module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSubintegral
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Effective
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EffectiveRelative
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FibrePointResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FibreDimension.IntegralReduction

/-!
# Relative cycles do not see the nilpotents in the base

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type and let
`r ≥ 0`. The reduction `S_red ⟶ S` is a surjective closed immersion, hence a universal
homeomorphism, and it induces an isomorphism on the residue field at every point. Base change
along it is therefore a bijection
`z(X/S, r) ⟶ z(X ×_S S_red / S_red, r)`
by Stacks 0H5G, and it matches effective relative cycles with effective relative cycles, because
base change preserves effectivity and, the morphism being surjective, also reflects it. So the
monoid `z^eff(X/S, r)` of effective relative `r`-cycles is unchanged when the base is replaced by
its reduction.

This is the reason Stacks Remark 0H5Y gives for the contravariant functor
`S' ↦ z^eff(S' ×_S X / S', r)` on schemes locally of finite type over `S` not to be
representable: it takes the same value on `S'` and on `S'_red`. The counter example the remark
leaves to the reader is
`Stacks.Chow.not_isRepresentable_effectiveRelativeCyclesFunctor_specFieldExt`.

## Main definitions

* `Stacks.Chow.relativeCyclesAddEquivReduction` — base change to the reduction of the base as an
  additive equivalence `z(X/S, r) ≃ z(X ×_S S_red / S_red, r)`.
* `Stacks.Chow.effectiveRelativeCyclesAddEquivReduction` — the same equivalence on the monoids of
  effective relative cycles.
* `Stacks.Chow.relativeCyclesAddEquivReductionReduction` — the invariance in the form the source
  writes it, `z(X/S, r) ≃ z(X_red/S_red, r)`.

## Main results

* `AlgebraicGeometry.Scheme.universalHomeomorphism_reductionι`,
  `AlgebraicGeometry.Scheme.reductionι_surjective` and
  `AlgebraicGeometry.Scheme.isLocallyNoetherian_reduction` — the three properties of `S_red ⟶ S`
  that Stacks 0H5G and Stacks 0H5U consume.
* `Stacks.Chow.relativeCyclesAddEquivReduction_coe` — the equivalence is base change along
  `S_red ⟶ S`.
* `AlgebraicGeometry.Scheme.isThickening_reductionToPullback` — `X_red ⟶ X ×_S S_red` is a
  thickening.

## Implementation notes

The monoid `z^eff(X/S, r)` whose invariance is proved here is the one of Stacks Project
Definition 0H5R, namely `Stacks.Chow.effectiveRelativeCycles` of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EffectiveRelative`; it is the value at `S` of
the functor the remark considers.

### Where the rest of Stacks 0H5Y is

The remark asks whether `S' ↦ z^eff(S' ×_S X / S', r)` is representable and answers no, giving as
the reason that the group of relative cycles does not change when `S'` is replaced by `S'_red`.
The reason is what is proved here, at the level of generality of an arbitrary `f : X ⟶ S`; the
remark's functor at a base `S'` locally of finite type over `S` is the case of the projection
`S' ×_S X ⟶ S'`. The functor itself is `Stacks.Chow.effectiveRelativeCyclesFunctor`; its
non-representability, and the characteristic `2` example of the remark, are in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.NonRepresentable` and
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SymmetricSquarePlane`.

### `X'_red` versus `X' ×_{S'} S'_red`

The source writes the invariance as `z(X'/S', r) = z(X'_red/S'_red, r)`. Two versions are proved
here. The first replaces only the base, `z(X/S, r) = z(X ×_S S_red / S_red, r)`, for relative
cycles and for effective ones; it is what Stacks 0H5G delivers directly, and what the functor of
the remark sees, its value at `S_red` being a group of cycles on `S_red ×_S X`. The second is the
source's: `X_red ⟶ X ×_S S_red` is a thickening over `S_red`, so proper pushforward along it
identifies `z(X_red/S_red, r)` with `z(X ×_S S_red / S_red, r)` (Tag 0H5E), and composing with the
first gives `z(X/S, r) = z(X_red/S_red, r)`.

### The reduction morphism

`AlgebraicGeometry.Scheme.reductionι` is a `def`, not an `abbrev`, so the instances already
available for `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` of the nilradical are not
found for it by instance search; they are transported by `inferInstanceAs`, which is what
`AlgebraicGeometry.Scheme.isClosedImmersion_reductionι` already does in
`StacksFrontier.AlgebraicGeometry.Scheme.Reduction`. Local Noetherianness of the reduction is not
proved from affine covers: a closed immersion is finite, hence locally of finite type, so
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` applies.

## References

* [Stacks Project, Remark 0H5Y](https://stacks.math.columbia.edu/tag/0H5Y)
* [Stacks Project, Lemma 0H5G](https://stacks.math.columbia.edu/tag/0H5G)
* [Stacks Project, Definition 0H5R](https://stacks.math.columbia.edu/tag/0H5R)
* [Stacks Project, Lemma 0H5S](https://stacks.math.columbia.edu/tag/0H5S)
* [Stacks Project, Lemma 0H5U](https://stacks.math.columbia.edu/tag/0H5U)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Lemma 0H5E](https://stacks.math.columbia.edu/tag/0H5E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The reduction of a scheme is universally homeomorphic to the scheme through `X_red ⟶ X`:
this is Stacks 054M for the closed subscheme cut out by the nilradical. -/
@[ega "I 5.1.3" "partial", ega "IV 2.4.8" "(ii)"]
instance universalHomeomorphism_reductionι : UniversalHomeomorphism X.reductionι :=
  inferInstanceAs (UniversalHomeomorphism X.nilradical.subschemeι)

/-- `X_red ⟶ X` is surjective, as a morphism property. -/
@[ega "I 5.1.3" "partial"]
instance reductionι_surjective : Surjective X.reductionι :=
  ⟨X.surjective_reductionι⟩

/-- The reduction of a locally Noetherian scheme is locally Noetherian: `X_red ⟶ X` is a closed
immersion, hence locally of finite type. -/
instance isLocallyNoetherian_reduction [IsLocallyNoetherian X] :
    IsLocallyNoetherian X.reduction :=
  LocallyOfFiniteType.isLocallyNoetherian X.reductionι

end AlgebraicGeometry.Scheme

namespace Stacks.Chow

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ)

/-! ### Replacing the base by its reduction -/

/-- The group of relative `r`-cycles does not change when the base is replaced by its reduction: base change along `S_red ⟶ S` is an additive equivalence
`z(X/S, r) ≃ z(X ×_S S_red / S_red, r)`.

This is Stacks 0H5G applied to the reduction morphism, which is a universal homeomorphism and
induces isomorphisms on all residue fields. The invariance of Stacks Remark 0H5Y in the form the
source writes it, with the source replaced by its reduction too, is
`Stacks.Chow.relativeCyclesAddEquivReductionReduction`. -/
def relativeCyclesAddEquivReduction :
    ↥(relativeCycles f r) ≃+ ↥(relativeCycles (pullback.snd f S.reductionι) r) :=
  relativeCyclesAddEquivOfUniversalHomeomorphism f S.reductionι
    (fun _ => inferInstance) r

/-- The equivalence of `Stacks.Chow.relativeCyclesAddEquivReduction` is base change along
`S_red ⟶ S`, read on the underlying families of cycles on fibres. -/
@[simp]
theorem relativeCyclesAddEquivReduction_coe (α : ↥(relativeCycles f r)) :
    (relativeCyclesAddEquivReduction f r α).1 = baseChangeFamily f S.reductionι r α.1 :=
  relativeCyclesAddEquivOfUniversalHomeomorphism_coe f S.reductionι
    (fun _ => inferInstance) r α

/-- The monoid of effective relative `r`-cycles does not change when the base is replaced by its reduction: base change along `S_red ⟶ S` is an additive
equivalence `z^eff(X/S, r) ≃ z^eff(X ×_S S_red / S_red, r)`.

Base change preserves effectivity by Stacks 0H5S, and `S_red ⟶ S` being surjective it also
reflects it by Stacks 0H5U, so the equivalence of
`Stacks.Chow.relativeCyclesAddEquivReduction` matches the two submonoids.

This is the reason the remark gives for the functor `S' ↦ z^eff(S' ×_S X / S', r)` not being
representable: it takes the same value on `S'` and on `S'_red`. -/
def effectiveRelativeCyclesAddEquivReduction :
    ↥(effectiveRelativeCycles f r) ≃+
      ↥(effectiveRelativeCycles (pullback.snd f S.reductionι) r) where
  toFun α := ⟨relativeCyclesAddEquivReduction f r α.1, by
    rw [mem_effectiveRelativeCycles, relativeCyclesAddEquivReduction_coe]
    exact isEffectiveFamily_baseChangeFamily f S.reductionι r α.1.1 α.2⟩
  invFun β := ⟨(relativeCyclesAddEquivReduction f r).symm β.1, by
    rw [mem_effectiveRelativeCycles]
    refine (isEffectiveFamily_iff_baseChangeFamily f S.reductionι r _).mpr ?_
    rw [← relativeCyclesAddEquivReduction_coe f r,
      (relativeCyclesAddEquivReduction f r).apply_symm_apply]
    exact β.2⟩
  left_inv α := Subtype.ext ((relativeCyclesAddEquivReduction f r).symm_apply_apply α.1)
  right_inv β := Subtype.ext ((relativeCyclesAddEquivReduction f r).apply_symm_apply β.1)
  map_add' α β := Subtype.ext (map_add (relativeCyclesAddEquivReduction f r) α.1 β.1)

/-- The equivalence of `Stacks.Chow.effectiveRelativeCyclesAddEquivReduction` is base change
along `S_red ⟶ S`, read on the underlying families of cycles on fibres. -/
@[simp]
theorem effectiveRelativeCyclesAddEquivReduction_coe (α : ↥(effectiveRelativeCycles f r)) :
    (effectiveRelativeCyclesAddEquivReduction f r α).1.1 =
      baseChangeFamily f S.reductionι r α.1.1 :=
  relativeCyclesAddEquivReduction_coe f r α.1

end Stacks.Chow

/-! ### The reduction of the source and of the base -/

namespace AlgebraicGeometry.Scheme

/-- The closed immersion `X_red ⟶ X ×_S S_red`. -/
noncomputable def reductionToPullback {X S : Scheme.{u}} (f : X ⟶ S) :
    X.reduction ⟶ pullback f S.reductionι :=
  pullback.lift X.reductionι (reductionMap f) (reductionMap_comp_reductionι f).symm

/-- `X_red ⟶ X ×_S S_red` is a thickening: it is a closed immersion, `X ×_S S_red ⟶ X` being one,
and surjective, `X ×_S S_red ⟶ X` being injective. -/
theorem isThickening_reductionToPullback {X S : Scheme.{u}} (f : X ⟶ S) :
    Stacks.Thickenings.IsThickening (reductionToPullback f) := by
  have h : reductionToPullback f ≫ pullback.fst f S.reductionι = X.reductionι :=
    pullback.lift_fst _ _ _
  haveI : IsClosedImmersion (reductionToPullback f ≫ pullback.fst f S.reductionι) :=
    h ▸ inferInstance
  refine ⟨IsClosedImmersion.of_comp _ (pullback.fst f S.reductionι), fun y => ?_⟩
  obtain ⟨x, hx⟩ := X.surjective_reductionι (pullback.fst f S.reductionι y)
  refine ⟨x, (pullback.fst f S.reductionι).isEmbedding.injective ?_⟩
  simpa [← h] using hx

instance isClosedImmersion_reductionToPullback {X S : Scheme.{u}} (f : X ⟶ S) :
    IsClosedImmersion (reductionToPullback f) :=
  (isThickening_reductionToPullback f).1

theorem reductionToPullback_snd {X S : Scheme.{u}} (f : X ⟶ S) :
    reductionToPullback f ≫ pullback.snd f S.reductionι = reductionMap f :=
  pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme

namespace Stacks.Chow

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ)

/-- **Stacks Project, Remark 0H5Y.** `z(X/S, r) = z(X_red/S_red, r)`: the group of relative
`r`-cycles does not change when both the source and the base are replaced by their reductions.
Base change along `S_red ⟶ S` identifies `z(X/S, r)` with `z(X ×_S S_red / S_red, r)`
(`Stacks.Chow.relativeCyclesAddEquivReduction`), and `X_red ⟶ X ×_S S_red` is a thickening over
`S_red`, along which proper pushforward identifies the groups of relative cycles (Tag 0H5E). -/
@[stacks 0H5Y "the invariance z(X/S, r) = z(X_red/S_red, r)"]
noncomputable def relativeCyclesAddEquivReductionReduction :
    ↥(relativeCycles f r) ≃+ ↥(relativeCycles (Scheme.reductionMap f) r) :=
  (relativeCyclesAddEquivReduction f r).trans
    (relativeCyclesAddEquivOfIsThickening (Scheme.reductionMap f) (pullback.snd f S.reductionι)
      (Scheme.reductionToPullback f) (Scheme.reductionToPullback_snd f)
      (Scheme.isThickening_reductionToPullback f) r).symm

end Stacks.Chow

end
