module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.RestrictPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction along an open immersion commutes with proper pushforward in a cartesian square

Let `S` be the base scheme of chapter 42 of the Stacks Project and let

  `A' --mA--> A`
  `|q'         |q`
  `B' --mB--> B`

be a cartesian square of schemes locally of finite type over `S`, in which `q` is proper and
`mB` — hence also `mA` — is an open immersion. Restriction of cycles along `mB` then commutes
with proper pushforward along `q`:

  `(q_* α)|_{B'} = q'_* (α|_{A'})`   in   `Z_k(B')`,

and the same identity holds on Chow groups.

This is the special case of Stacks 02RG — flat pullback commutes with proper pushforward in a
cartesian square — in which the flat morphism is an open immersion. The general statement is not
in this repository; this case is, and it is proved directly from the coefficient formula of
Stacks 02R4 rather than by specializing anything. It generalizes
`Stacks.Chow.cycleGroupOpensRestrict_properPushforward`, which is the same statement for the
canonical square built from an open subscheme `V ⊆ B` and its inverse image `q^{-1}(V)`, to a
square whose horizontal legs are arbitrary open immersions.

The reason it is cheap is that an open immersion is a base change along which *fibres do not
change*. Over a point `z` of `B'` the fibre of `q'` is carried bijectively onto the fibre of `q`
over `mB z` by `mA`: the two commute, `mA` is injective, and a point of `A` lying over `mB z`
lies in the range of `mA` because the square is cartesian. The weights agree because the residue
field map of an open immersion is an isomorphism, so the residue degrees of `q` and `q'` agree,
and because relative dimension does not see an open immersion either. So the locally finite sum
of Stacks 02R4 has the same terms on both sides.

## Main results

* `Stacks.Chow.range_base_of_isPullback`,
  `Stacks.Chow.image_preimage_singleton_of_isPullback` — the range of `mA` is the inverse image
  under `q` of the range of `mB`, and consequently the fibre of `q'` over a point `z` of `B'` is
  carried bijectively onto the fibre of `q` over `mB z` by `mA`.
* `Stacks.Chow.residueDegree_of_isPullback` — the residue degree of `q` at `mA w` is the residue
  degree of `q'` at `w`.
* `Stacks.Chow.isProper_of_isPullback` — the leg of the square opposite a proper morphism is
  proper.
* `Stacks.Chow.cycleGroupRestrict_properPushforward`,
  `Stacks.Chow.chowGroupRestrict_properChowPushforward` — **the open-immersion case of Stacks
  02RG**, on cycle groups and on Chow groups.

## Implementation notes

Properness of `q'` is taken as an instance hypothesis in the two main results rather than
synthesized inside them, because it depends on the cartesian square and so is not available to
instance search; it is supplied by `Stacks.Chow.isProper_of_isPullback`, and a consumer writes
`haveI := isProper_of_isPullback q mA mB q' hsq` before applying the results. Doing so is also
what makes the hypothesis `Stacks.Chow.ProperPushforwardFactorsThroughRationalEquivalence` for
`q'` expressible at all.

Neither restriction needs a hypothesis: restriction of cycles along an open immersion over the
base preserves rational equivalence outright, by
`Stacks.Chow.cycleGroupRestrict_mem_rationalEquivalences`, so `Stacks.Chow.chowGroupRestrict`
carries none. Only the two proper pushforwards carry one, which is Stacks 02S2 for `q` and
for `q'`.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow

variable {A B A' B' : Scheme.{u}}

/-! ### The fibres of the two vertical legs of a cartesian square -/

/-- A cartesian square read on points: the image in `B` of the value of `q'` at a point of `A'`
is the value of `q` at the image of that point in `A`. -/
theorem base_comm_of_isPullback {q : A ⟶ B} {mA : A' ⟶ A} {mB : B' ⟶ B} {q' : A' ⟶ B'}
    (hsq : IsPullback mA q' q mB) (w : A') :
    q.base (mA.base w) = mB.base (q'.base w) := by
  rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply]

/-- In a cartesian square whose horizontal legs are open immersions, the range of `mA` is the
inverse image under `q` of the range of `mB`: a point of `A` lying over a point of the open
subscheme `B'` of `B` already lies in the open subscheme `A'` of `A`. -/
theorem range_base_of_isPullback (q : A ⟶ B) (mA : A' ⟶ A) [IsOpenImmersion mA]
    (mB : B' ⟶ B) [IsOpenImmersion mB] (q' : A' ⟶ B') (hsq : IsPullback mA q' q mB) :
    Set.range mA.base = q.base ⁻¹' Set.range mB.base := by
  simpa only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.coe_opensRange, Scheme.Hom.coe_preimage] using
    congrArg (fun U : A.Opens => (U : Set A))
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback hsq.flip (⊤ : B'.Opens))

/-- **The fibres of a morphism do not change under base change along an open immersion.** In a
cartesian square whose horizontal legs are open immersions, the fibre of `q'` over a point `z` of
`B'` is carried bijectively onto the fibre of `q` over `mB z` by `mA`.

This is what makes the open-immersion case of Stacks 02RG a coefficient computation. -/
theorem image_preimage_singleton_of_isPullback (q : A ⟶ B) (mA : A' ⟶ A) [IsOpenImmersion mA]
    (mB : B' ⟶ B) [IsOpenImmersion mB] (q' : A' ⟶ B') (hsq : IsPullback mA q' q mB) (z : B') :
    mA.base '' (q'.base ⁻¹' {z}) = q.base ⁻¹' {mB.base z} := by
  ext x
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [base_comm_of_isPullback hsq, hw]
  · intro hx
    obtain ⟨w, rfl⟩ : x ∈ Set.range mA.base := by
      rw [range_base_of_isPullback q mA mB q' hsq]
      exact ⟨z, hx.symm⟩
    exact ⟨w, mB.isOpenEmbedding.injective (by rwa [← base_comm_of_isPullback hsq]), rfl⟩

/-- In a cartesian square whose horizontal legs are open immersions, the residue degree of `q` at
`mA w` is the residue degree of `q'` at `w`: the residue field map of an open immersion is an
isomorphism, so neither horizontal leg changes a residue degree. -/
theorem residueDegree_of_isPullback (q : A ⟶ B) (mA : A' ⟶ A) [IsOpenImmersion mA]
    (mB : B' ⟶ B) [IsOpenImmersion mB] (q' : A' ⟶ B') (hsq : IsPullback mA q' q mB) (w : A') :
    q.residueDegree (mA.base w) = q'.residueDegree w := by
  rw [← residueDegree_isOpenImmersion_comp mA q w, hsq.w,
    residueDegree_comp_isOpenImmersion q' mB w]

/-- The leg of a cartesian square opposite a proper morphism is proper: properness is stable
under base change. -/
@[ega "III 4.3.4" "more general"]
theorem isProper_of_isPullback (q : A ⟶ B) [IsProper q] (mA : A' ⟶ A) (mB : B' ⟶ B)
    (q' : A' ⟶ B') (hsq : IsPullback mA q' q mB) : IsProper q' :=
  MorphismProperty.of_isPullback hsq (P := @IsProper) inferInstance

/-! ### Restriction commutes with proper pushforward in a cartesian square -/

variable (C : ChowSituation.{u})

/-- **The open-immersion case of Stacks 02RG, on cycle groups.** In a cartesian square of schemes
locally of finite type over the base whose vertical legs `q`, `q'` are proper and whose horizontal
legs `mA`, `mB` are open immersions, pushing a cycle forward along `q` and restricting the result
along `mB` is the same as restricting along `mA` and pushing forward along `q'`.

Both sides are the locally finite sum of Stacks 02R4 over the fibre, and
`Stacks.Chow.image_preimage_singleton_of_isPullback` identifies the two fibres. The weights agree
by `Stacks.Chow.residueDegree_of_isPullback` and
`Stacks.Chow.relativeDimension_comp_isOpenImmersion`. -/
theorem cycleGroupRestrict_properPushforward (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA']
    (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB'] (q : A ⟶ B) [IsProper q] (hq : q ≫ sB = sA)
    (mA : A' ⟶ A) [IsOpenImmersion mA] (hmA : mA ≫ sA = sA')
    (mB : B' ⟶ B) [IsOpenImmersion mB] (hmB : mB ≫ sB = sB')
    (q' : A' ⟶ B') [IsProper q'] (hq' : q' ≫ sB' = sA')
    (hsq : IsPullback mA q' q mB) (k : ℤ) (α : CycleGroup C sA k) :
    cycleGroupRestrict C sB sB' mB hmB k (properPushforward C sA sB q hq k α) =
      properPushforward C sA' sB' q' hq' k (cycleGroupRestrict C sA sA' mA hmA k α) := by
  subst hmA hmB
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  rw [cycleGroupRestrict_apply, properPushforward_apply, properPushforward_apply,
    ← image_preimage_singleton_of_isPullback q mA mB q' hsq z,
    finsum_mem_image (Set.injOn_of_injective mA.isOpenEmbedding.injective)]
  refine finsum_congr fun w ↦ finsum_congr fun _ ↦ ?_
  rw [cycleGroupRestrict_apply, relativeDimension_comp_isOpenImmersion,
    relativeDimension_comp_isOpenImmersion, base_comm_of_isPullback hsq w,
    residueDegree_of_isPullback q mA mB q' hsq w]

/-- **The open-immersion case of Stacks 02RG, on Chow groups.** In a cartesian square of schemes
locally of finite type over the base whose vertical legs `q`, `q'` are proper and whose horizontal
legs `mA`, `mB` are open immersions, pushing a Chow class forward along `q` and restricting the
result along `mB` is the same as restricting along `mA` and pushing forward along `q'`.

All four maps are induced on quotients by the corresponding maps of cycle groups, so this is
`Stacks.Chow.cycleGroupRestrict_properPushforward` read on representatives. -/
theorem chowGroupRestrict_properChowPushforward (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA']
    (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB'] (q : A ⟶ B) [IsProper q] (hq : q ≫ sB = sA)
    (mA : A' ⟶ A) [IsOpenImmersion mA] (hmA : mA ≫ sA = sA')
    (mB : B' ⟶ B) [IsOpenImmersion mB] (hmB : mB ≫ sB = sB')
    (q' : A' ⟶ B') [IsProper q'] (hq' : q' ≫ sB' = sA')
    (hsq : IsPullback mA q' q mB) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB q hq k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C sA' sB' q' hq' k)
    (α : chowGroup C sA k) :
    chowGroupRestrict C sB sB' mB hmB k (properChowPushforward C sA sB q hq k hfac α) =
      properChowPushforward C sA' sB' q' hq' k hfac'
        (chowGroupRestrict C sA sA' mA hmA k α) := by
  induction α using QuotientAddGroup.induction_on with
  | H β =>
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C sB' k))
      (cycleGroupRestrict_properPushforward C sA sB sA' sB' q hq mA hmA mB hmB q' hq' hsq k β)

end Stacks.Chow

end
