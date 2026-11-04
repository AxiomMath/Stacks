module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.QuasiFiniteFibreStalk
public import StacksFrontier.RingTheory.CohenMacaulay.RadicalRegularSequence

/-!
# The regular sequence slicing a smooth relation through a point (Stacks 06LC)

Let `a, b : R ⟶ U` be two morphisms of schemes with `b` **smooth**, and let `r₀` be a point of
`R`.  Write `F` for the scheme-theoretic fibre of `b` through `r₀` and `A = 𝒪_{F, r₀}` for its
local ring there.  The composite `F ⟶ R ⟶ U` along `a` has a scheme-theoretic fibre of its own —
the *double fibre*, the locus where both `a` and `b` take the value they take at `r₀` — and the
point of it below `r₀` may or may not be isolated.

When it **is** isolated, **Stacks 06LC** produces functions `f₁, …, f_d` in the maximal ideal of
`𝒪_{U, a r₀}` whose germs, pulled back along `a` and restricted to the fibre of `b`, form a
regular sequence in `A` — and `d` is the Krull dimension of `A`, so that the quotient of `A` by
the sequence is zero-dimensional.  That is exactly the input of the slicing lemma **Stacks 06LI**
in the form
`Stacks.AlgebraicGeometry.exists_affineOpenImmersion_flat_zeroScheme_of_isRegular_fiber`, and this
file assembles it: `A` is regular, hence Noetherian and Cohen–Macaulay, because `b` is smooth,
and the closed fibre `A / 𝔪·A` is the local ring of the double fibre, hence zero-dimensional.

## Main results

* `AlgebraicGeometry.comp_stalkMap_cast`: the stalk map of a composite, read through the
  transport along an equality of points of the intermediate scheme.
* `AlgebraicGeometry.mem_maximalIdeal_stalk_cast`: membership in the maximal ideal of a stalk,
  carried along an equality of points.
* `AlgebraicGeometry.exists_mem_maximalIdeal_isRegular_fiberStalk_of_smooth`: the regular
  sequence, in the shape the slicing lemma consumes, together with its length.

## Implementation notes

The statement is phrased with the transport `(b.fiberι_asFiber r₀).symm ▸ …` that
`Stacks.AlgebraicGeometry.exists_affineOpenImmersion_flat_zeroScheme_of_isRegular_fiber` and
`Stacks.AlgebraicGeometry.germ_fiberι_appTop_apply` already use: the local ring of `R` at `r₀` and
at the image of the point of the fibre of `b` are the same ring, but at points equal only
propositionally, so one of the two has to be carried across.  Both transports needed are proved
by substituting the equality in a statement where the point it moves is a variable —
`AlgebraicGeometry.comp_stalkMap_cast` for the stalk maps and
`AlgebraicGeometry.mem_maximalIdeal_stalk_cast` for the membership in the maximal ideal — which is
why the hypothesis of **Stacks 06LC** is checked at the composite `F ⟶ U` and the conclusion read
at `r₀`.

Nothing here is specific to the two legs of a self-intersection: `a` is an arbitrary morphism to
`U`, and only smoothness of `b` and isolation of the point of the double fibre are used.  The
hypothesis is stated as isolation of that point rather than as quasi-finiteness of `F ⟶ U`,
because the morphism `F ⟶ R` out of a scheme-theoretic fibre is not locally of finite type, so
`AlgebraicGeometry.quasiFiniteAt_iff_fiberDimensionAt_eq_zero` does not apply to the composite.

No `@[stacks]` attribute is claimed: **Stacks 06LC** is registered on
`exists_isRegular_map_length_eq_ringKrullDim`, and this is that statement
with its two hypotheses discharged geometrically.

## References

* [Stacks Project, Tag 06LC](https://stacks.math.columbia.edu/tag/06LC)
* [Stacks Project, Lemma 37.24.1 (Tag 06LI)](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **The stalk map of a composite, read through the transport along an equality of points.**
For `k : F ⟶ R`, `a : R ⟶ U`, a point `v` of `F` and a point `q` of `R` with `k v = q`, the stalk
map of `k ≫ a` at `v` is the stalk map of `a` at `q` followed by that of `k` at `v`, both
transported along the equality. -/
theorem comp_stalkMap_cast {F R U : Scheme.{u}} (k : F ⟶ R) (a : R ⟶ U) (v : F) {q : R}
    (h : k v = q) (x : U.presheaf.stalk (a (k v))) :
    (k.stalkMap v).hom (h.symm ▸ (a.stalkMap q).hom ((congrArg a h) ▸ x))
      = ((k ≫ a).stalkMap v).hom x := by
  subst h
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- Membership in the maximal ideal of a stalk is carried along an equality of points. -/
theorem mem_maximalIdeal_stalk_cast {X : Scheme.{u}} {p q : X} (h : p = q)
    {s : X.presheaf.stalk p} (hs : s ∈ maximalIdeal (X.presheaf.stalk p)) :
    (h ▸ s) ∈ maximalIdeal (X.presheaf.stalk q) := by
  subst h
  exact hs

/-- **The regular sequence slicing a smooth relation through a point.**  Let `a, b : R ⟶ U` with
`b` smooth, let `r₀ : R` and suppose the point below `r₀` of the double fibre — the
scheme-theoretic fibre of the composite `b.fiber (b r₀) ⟶ R ⟶ U` along `a` — is isolated.  Then
there are `d` elements of the maximal ideal of `𝒪_{U, a r₀}` whose germs, pulled back along `a`
and restricted to the fibre of `b`, form a regular sequence in `𝒪_{b.fiber (b r₀), r₀}`, and `d`
is the Krull dimension of that local ring.

The local ring of the fibre of the smooth `b` is regular, hence Noetherian and Cohen–Macaulay
(`AlgebraicGeometry.isCohenMacaulayLocalRing_fiberStalk_of_smooth`), and its closed fibre along
the composite is the local ring of the double fibre, hence zero-dimensional
(`AlgebraicGeometry.ringKrullDim_quotient_stalkFibreIdeal_eq_zero_of_isIsolatedPoint`); those are
the two hypotheses of **Stacks 06LC**.

The length of the sequence is part of the conclusion of Stacks 06LC and is carried through here:
it is what makes the quotient of `𝒪_{b.fiber (b r₀), r₀}` by the sequence zero-dimensional
(`Stacks.AlgebraicGeometry.ringKrullDim_quotient_eq_zero_of_isRegular`), which is the local
statement behind the quasi-finiteness of the slice of **Stacks 06MF**. -/
theorem exists_mem_maximalIdeal_isRegular_fiberStalk_of_smooth {R U : Scheme.{u}} (a b : R ⟶ U)
    [Smooth b] (r₀ : R)
    (hiso : IsIsolatedPoint ((b.fiberι (b r₀) ≫ a).asFiber (b.asFiber r₀))) :
    ∃ (d : ℕ) (t : Fin d → U.presheaf.stalk (a r₀)),
      (∀ i, t i ∈ maximalIdeal (U.presheaf.stalk (a r₀))) ∧
        ((d : ℕ) : WithBot ℕ∞) =
          ringKrullDim ((b.fiber (b r₀)).presheaf.stalk (b.asFiber r₀)) ∧
        RingTheory.Sequence.IsRegular ((b.fiber (b r₀)).presheaf.stalk (b.asFiber r₀))
          (List.ofFn fun i => ((b.fiberι (b r₀)).stalkMap (b.asFiber r₀)).hom
            ((b.fiberι_asFiber r₀).symm ▸ (a.stalkMap r₀).hom (t i))) := by
  classical
  let := isNoetherianRing_fiberStalk_of_locallyOfFiniteType b (b r₀) (b.asFiber r₀)
  have hCM := isCohenMacaulayLocalRing_fiberStalk_of_smooth b r₀
  have h0 := ringKrullDim_quotient_stalkFibreIdeal_eq_zero_of_isIsolatedPoint
    (b.fiberι (b r₀) ≫ a) (b.asFiber r₀) hiso
  have hloc : ∀ x ∈ maximalIdeal
        (U.presheaf.stalk ((b.fiberι (b r₀) ≫ a) (b.asFiber r₀))),
      (((b.fiberι (b r₀) ≫ a).stalkMap (b.asFiber r₀)).hom) x ∈
        maximalIdeal ((b.fiber (b r₀)).presheaf.stalk (b.asFiber r₀)) := by
    intro x hx
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (isUnit_of_map_unit
      (((b.fiberι (b r₀) ≫ a).stalkMap (b.asFiber r₀)).hom) x hu)
  obtain ⟨l, hlen, hmem, hreg⟩ :=
    Stacks.CohenMacaulay.exists_isRegular_map_mem_maximalIdeal_of_ringKrullDim_quotient_eq_zero
      hCM (((b.fiberι (b r₀) ≫ a).stalkMap (b.asFiber r₀)).hom) hloc h0
  refine ⟨l.length, fun i => (congrArg a (b.fiberι_asFiber r₀)) ▸ l.get i,
    fun i => mem_maximalIdeal_stalk_cast _ (hmem _ (l.get_mem i)), hlen, ?_⟩
  have hofFn : (List.ofFn fun i : Fin l.length =>
        (((b.fiberι (b r₀) ≫ a).stalkMap (b.asFiber r₀)).hom) (l.get i))
      = l.map (((b.fiberι (b r₀) ≫ a).stalkMap (b.asFiber r₀)).hom) := by
    simp only [List.get_eq_getElem]
    exact List.ofFn_getElem_eq_map _ _
  rw [congrArg List.ofFn (funext fun i : Fin l.length =>
    comp_stalkMap_cast (b.fiberι (b r₀)) a (b.asFiber r₀) (b.fiberι_asFiber r₀) (l.get i)),
    hofFn]
  exact hreg

end AlgebraicGeometry

end
