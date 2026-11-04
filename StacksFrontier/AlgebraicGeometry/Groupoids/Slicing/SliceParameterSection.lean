module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SliceRegularParameter

/-!
# The slicing parameter as a section of an affine chart

Stacks 0461 chooses its cutting parameter inside the ring of sections of an affine chart around
`u`: the slice is `Spec(A/fA)` for an `f` in the prime of `A` at `u`. The parameter-choice engine
of `SliceDimensionDrop.lean`, on the other hand, produces an element of the *maximal ideal of the
local ring* `𝒪_{U, u}`, because that is the ideal whose extension to `𝒪_{F_u, e(u)}` cuts the
dimension down. This file closes that gap.

The local ring of a scheme at a point of an affine open is the localization of the ring of
sections at the prime of the point, so every element of its maximal ideal is `b/s` with `b` in that
prime and `s` outside it; since the germ of `s` is a unit, the element is a unit multiple of the
germ of `b`. Multiplying a ring element by a unit changes neither the ideal it generates nor
whether it is a nonzerodivisor, so the whole conclusion of the engine transfers from the element
of the maximal ideal to the germ of a genuine section.

## Main results

* `AlgebraicGeometry.IsAffineOpen.exists_mem_primeIdealOf_germ_eq_unit_mul`: an element of the
  maximal ideal of `𝒪_{X, x}` is a unit multiple of the germ at `x` of a section over an affine
  open containing `x` which lies in the prime of that point.
* `AlgebraicGeometry.GroupoidScheme.exists_mem_primeIdealOf_isSMulRegular_cohenMacaulay_quotient`:
  the parameter choice of Stacks 0461 with the parameter a section of an affine chart, which is
  the form in which the slice construction `exists_slice_of_mem_primeIdealOf` consumes it.

## Implementation notes

The transfer lemmas are stated for a unit multiple rather than for an equality of generated
ideals, because `IsSMulRegular` is a statement about the element and not about the ideal; the
equality of ideals is then `Ideal.span_singleton_mul_left_unit`.

A ring homomorphism carries a unit to a unit, so the unit relation in the local ring of `U` at
`u` is transported to `𝒪_{F_u, e(u)}` by applying the target map; no locality of that map is
used.

## References

* [Stacks Project, Tag 0461](https://stacks.math.columbia.edu/tag/0461)
-/

@[expose] public section

open CategoryTheory IsLocalRing Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- **An element of the maximal ideal is a unit multiple of the germ of a section.** Let `V` be an
affine open of a scheme `X` containing a point `x`. Every element of the maximal ideal of
`𝒪_{X, x}` is a unit multiple of the germ at `x` of a section over `V` lying in the prime ideal of
`x`.

The local ring at `x` is the localization of `Γ(X, V)` at that prime, so the element is `b/s` with
`b` in the prime and `s` outside it, and the germ of `s` is then a unit. -/
public theorem IsAffineOpen.exists_mem_primeIdealOf_germ_eq_unit_mul {X : Scheme.{u}}
    {V : X.Opens} (hV : IsAffineOpen V) {x : X} (hx : x ∈ V)
    {f : X.presheaf.stalk x} (hf : f ∈ maximalIdeal (X.presheaf.stalk x)) :
    ∃ b ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal, ∃ v : (X.presheaf.stalk x)ˣ,
      X.presheaf.germ V x hx b = (v : X.presheaf.stalk x) * f := by
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  have := hV.isLocalization_stalk (⟨x, hx⟩ : V)
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.mk'_surjective
    (hV.primeIdealOf (⟨x, hx⟩ : V)).asIdeal.primeCompl f
  replace hbs : IsLocalization.mk' (X.presheaf.stalk x) b s = f := hbs
  refine ⟨b, ?_, (IsLocalization.map_units (M := (hV.primeIdealOf (⟨x, hx⟩ : V)).asIdeal.primeCompl)
    (X.presheaf.stalk x) s).unit, ?_⟩
  · refine (IsLocalization.AtPrime.mk'_mem_maximal_iff (X.presheaf.stalk x)
      (hV.primeIdealOf (⟨x, hx⟩ : V)).asIdeal b s).mp ?_
    exact hbs ▸ hf
  · have h := IsLocalization.mk'_spec' (X.presheaf.stalk x) b s
    rw [hbs] at h
    exact h.symm

namespace GroupoidScheme

/-- **The parameter choice of Stacks 0461, with the parameter a section of an affine chart.** In
the situation of `exists_mem_maximalIdeal_isSMulRegular_cohenMacaulay_quotient`, and given an
affine open `A` of the object scheme containing `u`, the parameter can be taken to be the germ at
`u` of a section over `A` lying in the prime ideal of `u`.

This is the form in which the slicing construction consumes the parameter: the slice is the
vanishing locus of a section of an affine chart, which is `exists_slice_of_mem_primeIdealOf`,
while the engine produces an element of the maximal ideal of the local ring. The two are
reconciled by `IsAffineOpen.exists_mem_primeIdealOf_germ_eq_unit_mul`: a unit multiple of the
parameter generates the same ideal and is a nonzerodivisor exactly when the parameter is. -/
public theorem exists_mem_primeIdealOf_isSMulRegular_cohenMacaulay_quotient
    {S : Scheme.{u}} (G : GroupoidScheme S) [LocallyOfFiniteType G.source.left]
    [LocallyOfFiniteType G.target.left] (u : G.objects.left) (hu : IsFiniteTypePoint u)
    (A : G.objects.left.affineOpens) (huA : u ∈ A.1)
    [IsNoetherianRing ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u))]
    (hCM : Module.IsMaximalCohenMacaulay
      ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u))
      ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u)))
    (hlt : topologicalKrullDim ((stabilizer G).hom.fiber u) <
      ringKrullDim ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u))) :
    ∃ b ∈ (A.2.primeIdealOf ⟨u, huA⟩).asIdeal,
      IsSMulRegular ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u))
          ((targetSourceFiberStalkMap G u).hom
            (G.objects.left.presheaf.germ A.1 u huA b)) ∧
        ∃ _ : IsLocalRing ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u) ⧸
            Ideal.span {(targetSourceFiberStalkMap G u).hom
              (G.objects.left.presheaf.germ A.1 u huA b)}),
          IsCohenMacaulayLocalRing
              ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u) ⧸
                Ideal.span {(targetSourceFiberStalkMap G u).hom
                  (G.objects.left.presheaf.germ A.1 u huA b)}) ∧
            ringKrullDim ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u) ⧸
                Ideal.span {(targetSourceFiberStalkMap G u).hom
                  (G.objects.left.presheaf.germ A.1 u huA b)}) + 1 =
              ringKrullDim
                ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u)) := by
  obtain ⟨f, hfmem, hfreg, hloc, hCMq, hdrop⟩ :=
    exists_mem_maximalIdeal_isSMulRegular_cohenMacaulay_quotient G u hu hCM hlt
  obtain ⟨b, hb, v, hv⟩ := A.2.exists_mem_primeIdealOf_germ_eq_unit_mul huA hfmem
  set τ := (targetSourceFiberStalkMap G u).hom with hτ
  set w : ((G.source.left.fiber u).presheaf.stalk (sourceFiberIdentity G u))ˣ :=
    (Units.map (τ : _ →* _) v) with hw
  have hgerm : τ (G.objects.left.presheaf.germ A.1 u huA b) = (w : _) * τ f := by
    rw [hv, map_mul]
    rfl
  have hspan : Ideal.span {τ (G.objects.left.presheaf.germ A.1 u huA b)} =
      Ideal.span {τ f} := by
    rw [hgerm]
    exact Ideal.span_singleton_mul_left_unit w.isUnit _
  refine ⟨b, hb, ?_, ?_⟩
  · rw [hgerm]
    exact (w.isUnit.isSMulRegular _).mul hfreg
  · rw [hspan]
    exact ⟨hloc, hCMq, hdrop⟩

end GroupoidScheme

end AlgebraicGeometry

end
