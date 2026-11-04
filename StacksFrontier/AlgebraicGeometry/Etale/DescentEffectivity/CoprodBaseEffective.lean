module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.BaseFpqcReflect
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.OpenInduction

/-!
# Effectivity of a descent datum base changed to a binary coproduct of bases

Let `f : X ⟶ S` be a surjective integral morphism, `D` a descent datum relative to `X / S` with
étale underlying scheme, and `a : W ⟶ S`, `b : W' ⟶ S` two morphisms of the base. This file shows
that if `D` is étale effective after base change along `a` and after base change along `b`, then
it is étale effective after base change along `coprod.desc a b : W ⨿ W' ⟶ S`.

The two summands are complementary opens of the coproduct
(`AlgebraicGeometry.isCompl_opensRange_inl_inr`), so they are an open cover of it, and
[Stacks, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM) in the form
`AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isOpenCover` reduces effectivity over
`W ⨿ W'` to effectivity over each of the two summand opens. Over the summand open cut out by
`coprod.inl` the base changed datum is, by transitivity of base change
(`AlgebraicGeometry.DescentDatum.isEtaleEffective_changeDatum_comp_iff`), the base change of `D`
along `coprod.inl ≫ coprod.desc a b = a`, and likewise for `coprod.inr` and `b`. The full
faithfulness hypotheses of Tag 0BTM hold because the projection `X ×_S (W ⨿ W') ⟶ W ⨿ W'` is
again surjective and integral.

Combined with
`AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isEtaleEffective_changeDatum`, this is the
form in which the proof of [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
descends along a two member fpqc covering: the covering is presented as a single morphism out of
a binary coproduct, and what is known is effectivity along each of its two members separately.

## Main results

* `AlgebraicGeometry.iSup_cond_opensRange_coprod_inl_inr`: the two summands of a binary coproduct
  of schemes are an open cover of it.
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_changeDatum_opensRange_comp`: base change to
  the image of an open immersion `j : T ⟶ W` inside a base `W` has the same étale effectivity as
  base change along `j ≫ w`.
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_changeDatum_coprod_desc`: **a descent datum
  étale effective after base change along each of two morphisms is étale effective after base
  change along the morphism they describe out of the binary coproduct.**
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isEtaleEffective_changeDatum_coprod_desc`:
  **étale effectivity along each member of a two member fpqc covering presented as a morphism out
  of a binary coproduct gives étale effectivity of the datum itself.**

## Implementation notes

The open cover is indexed by `Bool`, the family being `cond`; `iSup_bool_eq` turns its supremum
into the join of the two summand opens, which is where
`AlgebraicGeometry.isCompl_opensRange_inl_inr` applies.

The identification of the datum over a summand open with the base change along the corresponding
coprojection is split into two steps, each a separate declaration from
`StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.ChangeTransitivity`: the open immersion
is compared with the inclusion of its image by `AlgebraicGeometry.Scheme.Hom.isoOpensRange`, and
only then are the two base changes composed. No equality of schemes is transported.

## References

* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-! ### The two summands of a binary coproduct as an open cover -/

/-- **The two summands of a binary coproduct of schemes are an open cover of it**, in the
`Bool`-indexed shape that `AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isOpenCover`
consumes. -/
theorem iSup_cond_opensRange_coprod_inl_inr (W W' : Scheme.{u}) :
    (⨆ c : Bool, cond c (coprod.inl : W ⟶ W ⨿ W').opensRange
      (coprod.inr : W' ⟶ W ⨿ W').opensRange) = ⊤ := by
  rw [iSup_bool_eq]
  exact (isCompl_opensRange_inl_inr W W').sup_eq_top

namespace DescentDatum

variable {S X W W' : Scheme.{u}}

/-! ### Base change to the image of an open immersion of the base -/

/-- **Base change to the image of an open immersion of the base has the same étale effectivity as
base change along the open immersion.** For `j : T ⟶ W` an open immersion and `w : W ⟶ S`, the
datum based changed along `w` and then restricted to the image of `j` is étale effective exactly
when the datum based changed along `j ≫ w` is. -/
theorem isEtaleEffective_changeDatum_opensRange_comp {f : X ⟶ S} (D : DescentDatum f)
    [Etale D.over.hom] (w : W ⟶ S) {T : Scheme.{u}} (j : T ⟶ W) [IsOpenImmersion j] :
    ((D.changeDatum w).baseDatum j.opensRange).IsEtaleEffective ↔
      (D.changeDatum (j ≫ w)).IsEtaleEffective := by
  have hj : j.isoOpensRange.hom ≫ j.opensRange.ι ≫ w = j ≫ w := by
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  exact (isEtaleEffective_changeDatum_comp_iff D).trans
    ((isEtaleEffective_changeDatum_iso_comp_iff D (j.opensRange.ι ≫ w) j.isoOpensRange).symm.trans
      (isEtaleEffective_changeDatum_of_eq D hj))

/-! ### Effectivity over a binary coproduct of bases -/

/-- **A descent datum étale effective after base change along each of two morphisms of the base
is étale effective after base change along the morphism they describe out of the binary
coproduct.** The two summands are an open cover of the coproduct, so Tag 0BTM applies to the
base changed datum; over each summand open the base changed datum is the base change of the
original along the corresponding coprojection composed with `coprod.desc a b`, which is the
corresponding morphism itself. The full faithfulness hypotheses of Tag 0BTM hold because the
projection of the base changed datum is again surjective and integral. -/
theorem isEtaleEffective_changeDatum_coprod_desc {f : X ⟶ S} [Surjective f] [IsIntegralHom f]
    (D : DescentDatum f) [Etale D.over.hom] (a : W ⟶ S) (b : W' ⟶ S)
    (ha : (D.changeDatum a).IsEtaleEffective) (hb : (D.changeDatum b).IsEtaleEffective) :
    (D.changeDatum (coprod.desc a b)).IsEtaleEffective := by
  have hff := fun {T : Scheme.{u}} (U : T ⟶ W ⨿ W') ↦
    fullyFaithful_etaleDescentFunctor_baseChange_of_isIntegralHom
      (pullback.snd f (coprod.desc a b)) U
  refine isEtaleEffective_of_isOpenCover (D.changeDatum (coprod.desc a b))
    (fun c : Bool ↦ cond c (coprod.inl : W ⟶ W ⨿ W').opensRange
      (coprod.inr : W' ⟶ W ⨿ W').opensRange)
    (iSup_cond_opensRange_coprod_inl_inr W W') ?_ (fun _ _ ↦ hff _)
    fun _ _ _ ↦ (hff _).faithful
  rintro (_ | _)
  · exact (isEtaleEffective_changeDatum_opensRange_comp D _ _).mpr
      ((isEtaleEffective_changeDatum_of_eq D (coprod.inr_desc a b)).mpr hb)
  · exact (isEtaleEffective_changeDatum_opensRange_comp D _ _).mpr
      ((isEtaleEffective_changeDatum_of_eq D (coprod.inl_desc a b)).mpr ha)

/-- **Étale effectivity along each member of a two member fpqc covering presented as a morphism
out of a binary coproduct gives étale effectivity of the datum itself.** This is
`AlgebraicGeometry.DescentDatum.isEtaleEffective_changeDatum_coprod_desc` fed into the
fpqc-locality of étale effectivity in the base,
`AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isEtaleEffective_changeDatum`. -/
theorem isEtaleEffective_of_isEtaleEffective_changeDatum_coprod_desc (f : X ⟶ S) [Surjective f]
    [IsIntegralHom f] (a : W ⟶ S) (b : W' ⟶ S) [Flat (coprod.desc a b)]
    [Surjective (coprod.desc a b)] [QuasiCompact (coprod.desc a b)] (D : DescentDatum f)
    [Etale D.over.hom] (hqc : QuasiCompact D.over.hom) (hsep : IsSeparated D.over.hom)
    (ha : (D.changeDatum a).IsEtaleEffective) (hb : (D.changeDatum b).IsEtaleEffective) :
    D.IsEtaleEffective :=
  isEtaleEffective_of_isEtaleEffective_changeDatum f (coprod.desc a b) D hqc hsep
    (isEtaleEffective_changeDatum_coprod_desc D a b ha hb)

end DescentDatum

end AlgebraicGeometry

end
