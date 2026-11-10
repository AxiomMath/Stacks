module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.RationalEquivalenceFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.OpenImmersionRationalEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Chow groups of the pieces of a decomposition into open and closed subschemes

Let `X` be a scheme locally of finite type over the base scheme of chapter 42 of the Stacks
Project. Chapter 42 writes `X = \coprod_{i \in I} X_i` for a decomposition into open and closed
subschemes and then uses `CH_k(X) = \prod_{i \in I} CH_k(X_i)`, the projections being restriction
of cycles. In the applications the pieces arrive not as open *subschemes* of `X` but as schemes
`W i` equipped with open immersions `W i ⟶ X` whose ranges decompose `X` — a base change of a
piece inclusion, say, is a morphism of that shape and not the inclusion of an open subscheme.

This file supplies the two things that situation needs. First, restriction of Chow classes along
an *arbitrary* open immersion over the base, `Stacks.Chow.chowGroupRestrict`, carrying no
hypothesis: restriction of cycles along an open immersion is restriction to the image followed by
transport along the isomorphism onto the image, and both halves are known to preserve rational
equivalence. Second, the product decomposition
`Stacks.Chow.chowGroupClopenRestrictEquiv`, again unconditional.

Unconditionality is the point of the second half. `Stacks.Chow.chowGroupClopenEquiv` carries the
hypothesis `Stacks.Chow.RationalEquivalenceDecomposes`, and that hypothesis is discharged
outright by `Stacks.Chow.rationalEquivalenceDecomposes_of_isClopenDecomposition` below: its
forward half is Stacks 02S1 at the piece inclusions, which is
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_opensι`, and its reverse half is
`Stacks.Chow.rationalEquivalenceDecomposes_mpr`, which needs nothing.

## Main definitions

* `Stacks.Chow.chowGroupRestrict` — restriction of Chow classes along an open immersion over the
  base, `CH_k(X) ⟶ CH_k(U)`.
* `Stacks.Chow.chowGroupClopenRestrictEquiv` — `CH_k(X) ≅ ∏_i CH_k(W i)` for a decomposition of
  `X` into open and closed subschemes presented by open immersions `W i ⟶ X`.

## Main results

* `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion` — **Stacks 02S1
  along an arbitrary open immersion.**
* `Stacks.Chow.cycleGroupRestrict_eq_properPushforward` — restriction of cycles along an open
  immersion is restriction to the image followed by transport along the isomorphism onto it.
* `Stacks.Chow.chowGroupRestrict_comp`, `Stacks.Chow.chowGroupRestrict_id`,
  `Stacks.Chow.chowGroupRestrict_congr` — functoriality of restriction.
* `Stacks.Chow.chowGroupRestrict_opensι`, `Stacks.Chow.chowGroupRestrict_of_isIso` —
  restriction along the inclusion of an open subscheme is
  `Stacks.Chow.chowGroupOpensRestrictOfIsOpenImmersion`, and restriction along an isomorphism is
  pushforward along its inverse.
* `Stacks.Chow.rationalEquivalenceDecomposes_of_isClopenDecomposition` — rational equivalence
  decomposes along a decomposition into open and closed subschemes, with no hypothesis.
* `Stacks.Chow.chowGroupClopenRestrictEquiv_apply` — the components of the product decomposition
  are restriction along the given open immersions.

## Implementation notes

### Degrees, and why restriction is not written as a flat pullback

Restriction along an open immersion `j` *is* flat pullback along `j` in relative dimension zero,
which is `Stacks.Chow.cycleGroupRestrict_eq_flatPullback`. Writing it as
`Stacks.Chow.flatPullbackChow` would land in degree `k + (0 : ℕ)` rather than `k` and force a
transport of the degree at every use. `Stacks.Chow.chowGroupRestrict` is therefore the map induced
on quotients by `Stacks.Chow.cycleGroupRestrict`, whose degree is `k` on the nose, exactly as
`Stacks.Chow.chowGroupOpensRestrict` is for the inclusion of an open subscheme.

### The index universe

`Stacks.Chow.chowGroupClopenRestrictEquiv` restricts the index type to `Type u`, inherited from
`Stacks.Chow.rationalEquivalenceDecomposes_mpr`: the witness index of
`Stacks.Chow.IsRationallyEquivalentToZero` is quantified over `Type u` and the assembled witness
is a sigma over the index type. The decomposition of *cycles*,
`Stacks.Chow.cycleGroupClopenEquiv`, is free of that restriction.

### No `@[stacks]` attribute for the product decomposition

The identity `CH_k(X) = ∏_i CH_k(X_i)` is used without comment in the proofs of Stacks 0FDZ and
Stacks 02UC and is not the statement of either tag, so the results about it are untagged here,
following `StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.ChowGroup` and
`StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Cycles`.

## References

* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Restriction along an arbitrary open immersion -/

variable (C : ChowSituation.{u}) {X U V : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X) [IsOpenImmersion j]

/-- Proper pushforward along an isomorphism over the base has at a point the coefficient of the
original cycle at the point corresponding under the inverse. -/
private theorem properPushforward_apply_of_iso {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (i : A ≅ B)
    (hi : i.hom ≫ sB = sA) (k : ℤ) (c : CycleGroup C sA k) (b : B) :
    (properPushforward C sA sB i.hom hi k c).1 b = c.1 (i.inv b) := by
  have hpt : i.hom (i.inv b) = b := by simp [← Scheme.Hom.comp_apply]
  have h := properPushforward_apply_of_isIso C sA sB i.hom hi k c (i.inv b)
  rwa [hpt] at h

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sU] in
/-- The inverse of the isomorphism onto the image of an open immersion over the base is itself a
morphism over the base. -/
theorem isoOpensRange_inv_comp_base (hj : j ≫ sX = sU) :
    j.isoOpensRange.inv ≫ sU = j.opensRange.ι ≫ sX := by
  rw [← hj, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]

variable (hj : j ≫ sX = sU) (k : ℤ)

/-- Restriction of cycles along an open immersion is restriction to the image followed by
transport along the isomorphism onto the image: both sides have at a point of `U` the coefficient
of the given cycle at its image in `X`. -/
theorem cycleGroupRestrict_eq_properPushforward (c : CycleGroup C sX k) :
    cycleGroupRestrict C sX sU j hj k c =
      properPushforward C (j.opensRange.ι ≫ sX) sU j.isoOpensRange.inv
        (isoOpensRange_inv_comp_base C sX sU j hj) k
        (cycleGroupOpensRestrict C sX j.opensRange k c) := by
  refine Subtype.ext ?_
  apply Function.locallyFinsuppWithin.ext
  intro x
  have himg : j.opensRange.ι.base (j.isoOpensRange.hom.base x) = j.base x := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_hom_ι]
  refine Eq.trans ?_ (properPushforward_apply_of_iso C (j.opensRange.ι ≫ sX) sU
    j.isoOpensRange.symm (isoOpensRange_inv_comp_base C sX sU j hj) k _ x).symm
  rw [cycleGroupRestrict_apply, cycleGroupOpensRestrict_apply]
  exact congrArg _ himg.symm

/-- Restriction of cycles along an open immersion carries cycles rationally equivalent to zero to
cycles rationally equivalent to zero: restriction to the image does so by Stacks 02S1 for the
inclusion of an open subscheme, and transport along an isomorphism does so by Stacks 02S2 for an
isomorphism. -/
theorem cycleGroupRestrict_mem_rationalEquivalences {c : CycleGroup C sX k}
    (hc : c ∈ rationalEquivalences C sX k) :
    cycleGroupRestrict C sX sU j hj k c ∈ rationalEquivalences C sU k := by
  rw [cycleGroupRestrict_eq_properPushforward]
  exact properPushforwardFactorsThroughRationalEquivalence_of_isIso C
    (j.opensRange.ι ≫ sX) sU j.isoOpensRange.inv (isoOpensRange_inv_comp_base C sX sU j hj) k _
    (cycleGroupOpensRestrict_mem_rationalEquivalences C sX j.opensRange k
      (flatPullbackFactorsThroughRationalEquivalence_of_opensι C sX j.opensRange k) hc)

/-- **Stacks 02S1 along an arbitrary open immersion.** Flat pullback along an open immersion over
the base carries cycles rationally equivalent to zero to cycles rationally equivalent to zero.

Flat pullback along an open immersion in relative dimension zero is restriction of cycles, by
`Stacks.Chow.cycleGroupRestrict_eq_flatPullback`, up to a transport of the degree from `k + 0` to
`k`; the statement for restriction is
`Stacks.Chow.cycleGroupRestrict_mem_rationalEquivalences`. -/
@[stacks 02S1 "flat pullback along an arbitrary open immersion preserves rational equivalence"]
theorem flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion :
    FlatPullbackFactorsThroughRationalEquivalence C sU sX j hj 0
      (relativeDimension_of_isOpenImmersion j) k := by
  have hcast : ∀ {m : ℤ} (hm : k + ((0 : ℕ) : ℤ) = m)
      (β : CycleGroup C sU (k + ((0 : ℕ) : ℤ))),
      (hm ▸ β : CycleGroup C sU m) ∈ rationalEquivalences C sU m →
        β ∈ rationalEquivalences C sU (k + ((0 : ℕ) : ℤ)) := by
    intro m hm β hβ
    cases hm
    exact hβ
  have hk : k + ((0 : ℕ) : ℤ) = k := by simp
  intro α hα
  refine hcast hk _ ?_
  have heq : (hk ▸ flatPullback C sU sX j hj 0 (relativeDimension_of_isOpenImmersion j) k α :
      CycleGroup C sU k) = cycleGroupRestrict C sX sU j hj k α := by
    refine Subtype.ext ?_
    rw [val_cycleGroup_cast C sU hk]
    exact (cycleGroupRestrict_eq_flatPullback C sX sU j hj
      (relativeDimension_of_isOpenImmersion j) k α).symm
  rw [heq]
  exact cycleGroupRestrict_mem_rationalEquivalences C sX sU j hj k hα

/-- **Restriction of Chow classes along an open immersion over the base**, `CH_k(X) ⟶ CH_k(U)`.

This carries no hypothesis: restriction of cycles preserves rational equivalence by
`Stacks.Chow.cycleGroupRestrict_mem_rationalEquivalences`. -/
def chowGroupRestrict : chowGroup C sX k →+ chowGroup C sU k :=
  QuotientAddGroup.map (rationalEquivalences C sX k) (rationalEquivalences C sU k)
    (cycleGroupRestrict C sX sU j hj k)
    fun _ hc ↦ cycleGroupRestrict_mem_rationalEquivalences C sX sU j hj k hc

/-- On the class of a cycle, restriction of Chow classes along an open immersion is the class of
the restricted cycle. -/
@[simp]
theorem chowGroupRestrict_mk (c : CycleGroup C sX k) :
    chowGroupRestrict C sX sU j hj k (QuotientAddGroup.mk' (rationalEquivalences C sX k) c) =
      QuotientAddGroup.mk' (rationalEquivalences C sU k) (cycleGroupRestrict C sX sU j hj k c) :=
  rfl

/-- Restriction of Chow classes along an open immersion is restriction to the image followed by
transport along the isomorphism onto the image. -/
theorem chowGroupRestrict_eq_chowPushforwardOfIso :
    chowGroupRestrict C sX sU j hj k =
      (chowPushforwardOfIso C (j.opensRange.ι ≫ sX) sU j.isoOpensRange.inv
          (isoOpensRange_inv_comp_base C sX sU j hj) k).comp
        (chowGroupOpensRestrictOfIsOpenImmersion C sX j.opensRange k) := by
  refine AddMonoidHom.ext fun α ↦ ?_
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    change chowGroupRestrict C sX sU j hj k (QuotientAddGroup.mk' _ c) = _
    rw [chowGroupRestrict_mk, cycleGroupRestrict_eq_properPushforward]
    rfl

/-- Restriction of Chow classes along the inclusion of an open subscheme is
`Stacks.Chow.chowGroupOpensRestrictOfIsOpenImmersion`. -/
theorem chowGroupRestrict_opensι (W : X.Opens) :
    chowGroupRestrict C sX (W.ι ≫ sX) W.ι rfl k =
      chowGroupOpensRestrictOfIsOpenImmersion C sX W k :=
  rfl

/-- Restriction of cycles along an isomorphism over the base is proper pushforward along the
inverse isomorphism. -/
theorem cycleGroupRestrict_of_isIso (e : U ⟶ X) [IsIso e] (he : e ≫ sX = sU)
    (c : CycleGroup C sX k) :
    cycleGroupRestrict C sX sU e he k c =
      properPushforward C sX sU (inv e) (by rw [IsIso.inv_comp_eq, he]) k c := by
  refine Subtype.ext ?_
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [cycleGroupRestrict_apply]
  exact (properPushforward_apply_of_iso C sX sU (asIso e).symm
    (by simp [← he]) k c x).symm

/-- Restriction of Chow classes along an isomorphism over the base is proper pushforward along
the inverse isomorphism. -/
theorem chowGroupRestrict_of_isIso (e : U ⟶ X) [IsIso e] (he : e ≫ sX = sU) :
    chowGroupRestrict C sX sU e he k =
      chowPushforwardOfIso C sX sU (inv e) (by rw [IsIso.inv_comp_eq, he]) k := by
  refine AddMonoidHom.ext fun α ↦ ?_
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C sU k))
      (cycleGroupRestrict_of_isIso C sX sU k e he c)

/-! ### Functoriality -/

variable (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (i : V ⟶ U) [IsOpenImmersion i]
  (hi : i ≫ sU = sV)

/-- Restriction of cycles along open immersions is functorial. -/
theorem cycleGroupRestrict_comp (c : CycleGroup C sX k) :
    cycleGroupRestrict C sU sV i hi k (cycleGroupRestrict C sX sU j hj k c) =
      cycleGroupRestrict C sX sV (i ≫ j) (by rw [Category.assoc, hj, hi]) k c := by
  refine Subtype.ext ?_
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [cycleGroupRestrict_apply, cycleGroupRestrict_apply, cycleGroupRestrict_apply,
    Scheme.Hom.comp_apply]

/-- Restriction of Chow classes along open immersions is functorial. -/
theorem chowGroupRestrict_comp (α : chowGroup C sX k) :
    chowGroupRestrict C sU sV i hi k (chowGroupRestrict C sX sU j hj k α) =
      chowGroupRestrict C sX sV (i ≫ j) (by rw [Category.assoc, hj, hi]) k α := by
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C sV k))
      (cycleGroupRestrict_comp C sX sU j hj k sV i hi c)

omit [LocallyOfFiniteType sU] [IsOpenImmersion j] [LocallyOfFiniteType sV] [IsOpenImmersion i] in
/-- Restriction of cycles along the identity is the identity. -/
theorem cycleGroupRestrict_id (c : CycleGroup C sX k) :
    cycleGroupRestrict C sX sX (𝟙 X) (Category.id_comp sX) k c = c := by
  refine Subtype.ext ?_
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [cycleGroupRestrict_apply]
  rfl

omit [LocallyOfFiniteType sU] [IsOpenImmersion j] [LocallyOfFiniteType sV] [IsOpenImmersion i] in
/-- Restriction of Chow classes along the identity is the identity. -/
@[simp]
theorem chowGroupRestrict_id (α : chowGroup C sX k) :
    chowGroupRestrict C sX sX (𝟙 X) (Category.id_comp sX) k α = α := by
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C sX k))
      (cycleGroupRestrict_id C sX k c)

omit [LocallyOfFiniteType sV] [IsOpenImmersion i] in
/-- Restriction of Chow classes is unchanged by replacing the open immersion with an equal one. -/
theorem chowGroupRestrict_congr (j' : U ⟶ X) [IsOpenImmersion j'] (hjj' : j = j')
    (hj' : j' ≫ sX = sU) :
    chowGroupRestrict C sX sU j hj k = chowGroupRestrict C sX sU j' hj' k := by
  subst hjj'
  rfl

end Stacks.Chow

/-! ### The product decomposition along a decomposition into open and closed subschemes -/

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {I : Type u} {W : I → Scheme.{u}} (s : ∀ i, W i ⟶ C.S) [∀ i, LocallyOfFiniteType (s i)]
  (m : ∀ i, W i ⟶ X) [∀ i, IsOpenImmersion (m i)] (hm : ∀ i, m i ≫ sX = s i)

/-- **Rational equivalence decomposes along a decomposition into open and closed subschemes**,
with no hypothesis.

The forward half is Stacks 02S1 at the piece inclusions,
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_opensι`, and the reverse half is
`Stacks.Chow.rationalEquivalenceDecomposes_mpr`, which needs none. This discharges the hypothesis
of `Stacks.Chow.chowGroupClopenEquiv`. -/
theorem rationalEquivalenceDecomposes_of_isClopenDecomposition {U : I → X.Opens}
    (h : IsClopenDecomposition U) (k : ℤ) : RationalEquivalenceDecomposes C sX h k :=
  rationalEquivalenceDecomposes_of_flatPullbackFactors C sX h k
    fun i ↦ flatPullbackFactorsThroughRationalEquivalence_of_opensι C sX (U i) k

variable (h : IsClopenDecomposition fun i ↦ (m i).opensRange) (k : ℤ)

/-- **`CH_k(X) = ∏_i CH_k(X_i)` for a decomposition of `X` into open and closed subschemes
presented by open immersions `W i ⟶ X`.**

This is `Stacks.Chow.chowGroupClopenEquiv` with its hypothesis discharged by
`Stacks.Chow.rationalEquivalenceDecomposes_of_isClopenDecomposition`, followed by the transport
of each factor along the isomorphism of `W i` with the open subscheme it covers. The components
are restriction along the given immersions, by
`Stacks.Chow.chowGroupClopenRestrictEquiv_apply`. -/
def chowGroupClopenRestrictEquiv : chowGroup C sX k ≃+ ∀ i, chowGroup C (s i) k :=
  (chowGroupClopenEquiv C sX h k
      (rationalEquivalenceDecomposes_of_isClopenDecomposition C sX h k)).trans
    (AddEquiv.piCongrRight fun i ↦ chowGroupEquivOfIso C ((m i).opensRange.ι ≫ sX) (s i)
      (m i).isoOpensRange.inv (isoOpensRange_inv_comp_base C sX (s i) (m i) (hm i)) k)

/-- The components of the product decomposition `CH_k(X) = ∏_i CH_k(X_i)` are restriction of Chow
classes along the given open immersions. -/
@[simp]
theorem chowGroupClopenRestrictEquiv_apply (α : chowGroup C sX k) (i : I) :
    chowGroupClopenRestrictEquiv C sX s m hm h k α i =
      chowGroupRestrict C sX (s i) (m i) (hm i) k α := by
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    change chowPushforwardOfIso C ((m i).opensRange.ι ≫ sX) (s i) (m i).isoOpensRange.inv
        (isoOpensRange_inv_comp_base C sX (s i) (m i) (hm i)) k
        (chowGroupClopenEquiv C sX h k
          (rationalEquivalenceDecomposes_of_isClopenDecomposition C sX h k)
          (QuotientAddGroup.mk' (rationalEquivalences C sX k) c) i) = _
    rw [chowGroupClopenEquiv_apply, chowGroupClopenRestrict_mk, chowPushforwardOfIso_mk]
    exact (congrArg (QuotientAddGroup.mk' (rationalEquivalences C (s i) k))
      (cycleGroupRestrict_eq_properPushforward C sX (s i) (m i) (hm i) k c)).symm

end Stacks.Chow

end
