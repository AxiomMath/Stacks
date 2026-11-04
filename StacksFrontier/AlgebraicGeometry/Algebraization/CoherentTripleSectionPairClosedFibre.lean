module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionPair
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleUnitHomNaturality

/-!
# The closed-fibre member of the section pair of the induction step

The second clause of `Stacks.Algebraization.HasHilbertInductionStep` needs a global section of
each member of the fixed invertible triple `L`, the two corresponding over the punctured closed
fibre, with the punctured-spectrum one avoiding the associated points of the triple being
twisted. `Stacks.Algebraization.exists_section_nonvanishing_on_associatedPoints` supplies the
punctured-spectrum member; this file supplies the closed-fibre member and the correspondence,
and assembles the two into the morphism of coherent triples
`CoherentTriple.unit A f h ⟶ L` that [Stacks, Tag 0F27] calls `(s, s_0)`.

The source chooses `s` first and then writes "after multiplying `s` by a suitable element of
`𝔪` we may assume `λ(s mod f) = s_0|_{U_0}` for some `s_0 ∈ Γ(X_0, ℒ_0)`; details omitted". That
adjustment is **not needed when `depth(A) ≥ 3`**. The closed-fibre
member `L.F₀` of an invertible triple is invertible, hence reflexive, so when `depth(A) ≥ 3` --
equivalently `depth(A/fA) ≥ 2`, which is the hypothesis of both [Stacks, Tag 0F2A] and
[Stacks, Tag 0F2B], the only two consumers of Tag 0F27 -- Hartogs extension on `A/fA` makes
`L.F₀` the direct image of its own restriction to the punctured closed fibre. Restriction
`Γ(X_0, ℒ_0) → Γ(U_0, ℒ_0)` is then *bijective*, so `s_0` exists for the section `s` already
chosen, uniquely and with no adjustment; and the nonvanishing condition, which constrains only
`s`, is untouched. This is the same observation the source makes in the proof of Tag 0F2B when
it writes `M_0 = Γ(X_0, ℒ_0) = Γ(U_0, ℒ_0)`.

## Main definitions

* `Stacks.Algebraization.CoherentTriple.homUnitOfGlobalSections`: the morphism of coherent
  triples `CoherentTriple.unit A f h ⟶ L` attached to a corresponding pair of global sections.
* `Stacks.Algebraization.CoherentTriple.mulSectionTwistZOfGlobalSections`: multiplication by
  such a pair, as a morphism from the `n`-th twist of a coherent triple to its `(n + 1)`-st.

## Main results

* `Stacks.Algebraization.bijective_pullbackGlobalSections_puncturedClosedFibre`: restriction to
  the punctured closed fibre is bijective on the global sections of an invertible module on the
  closed fibre, when `depth(A) ≥ 3`.
* `Stacks.Algebraization.exists_eq_globalSectionsMap`: **every global section of the
  punctured-spectrum member of an invertible triple has a closed-fibre partner**, with no
  adjustment.
* `Stacks.Algebraization.exists_sectionPair_nonvanishing_on_associatedPoints`: the section pair
  of the induction step, the punctured-spectrum member avoiding
  `Ass(T.F) ∪ Ass(T.F / f T.F)`.
* `Stacks.Algebraization.exists_homUnit_nonvanishing_on_associatedPoints`: the same, read as a
  morphism of coherent triples out of the unit triple.

## Implementation notes

The hypothesis `3 ≤ Module.depth A (maximalIdeal A) A` is not a hypothesis of
`Stacks.Algebraization.HasHilbertInductionStep`, which carries only `hf` and `hreg`; nor is it a
hypothesis of Tag 0F27 itself. So these results do not discharge its second clause as that
predicate is stated, and the depth hypothesis must not be added to the predicate: Tag 0F27's
conclusion is stated against it.

Discharging the clause verbatim needs the source's omitted adjustment, and that adjustment has
two halves. The prime-avoidance half -- a multiplier `g ∈ 𝔪` whose powers keep the section
nonvanishing on the finitely many associated points -- is depth-free and is
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionPairAvoidance`.

The other half is **not** finiteness of the length of the cokernel of
`Stacks.Algebraization.globalSectionsMap`. That statement is *false* without the depth
hypothesis, so `Stacks.Algebraization.finiteLength_cokernel_globalSectionsMap` cannot be
restated without it. Take `A = k[[X, Y]]`, which has depth two, and `f = X`; let `T` be the
triple with `T.F = 𝒪_U`, `T.F₀ = 𝒪_{X_0}` and `T.alpha` the identity. Then
`Γ(U, 𝒪_U) = A` by Hartogs, the closed fibre is `Spec k[[Y]]`, the punctured closed fibre is its
generic point, and `globalSectionsMap` is `A → k((Y))` with image `k[[Y]]`. Its cokernel
`k((Y))/k[[Y]]` is the injective hull of the residue field of `k[[Y]]`: it is supported at the
closed point and `𝔪`-power torsion, but it is not finitely generated -- the chain
`k[[Y]] ⊂ Y⁻¹k[[Y]] ⊂ Y⁻²k[[Y]] ⊂ ⋯` never stabilises -- so it does not have finite length.
Support at the closed point is therefore not enough, and neither is `f`-regularity with
coherence: both hold in this example. Tag 0F28 assumes `depth(A) ≥ 3` for exactly this reason,
and in `Stacks.Algebraization.finiteLength_cokernel_globalSectionsMap` the depth hypothesis is
used in precisely one place, to get surjectivity of
`Stacks.Algebraization.closedFibreRestriction` out of
`Stacks.Algebraization.isIso_unit_puncturedClosedFibre`; that surjectivity is the vanishing of
`H¹_𝔪(A/fA)`, which is what fails above.

What the adjustment actually needs is the weaker, depth-free statement that a given section over
the punctured closed fibre is carried into the image of restriction by a power of a given
`g ∈ 𝔪`. **That is proved**, as
`Stacks.Algebraization.hasPowerExtendableClosedFibreSections` in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionPairDepthFree`, so the clause
no longer needs the depth hypothesis of this file, and
`Stacks.Algebraization.exists_sectionPair_nonvanishing_on_associatedPoints` is superseded by
`Stacks.Algebraization.exists_sectionPair_nonvanishing_on_associatedPoints_depthFree`.

It is **not** proved by the route through local cohomology -- that the cokernel of
`Stacks.Algebraization.closedFibreRestriction` is `𝔪`-power torsion because it injects into
`H¹_𝔪(ℒ₀)` (`Stacks.LocalCohomology.isIPowerTorsion_lowDegreeComparison`). That route needs an
isomorphism `ℒ₀ ≅ complementTilde A I M` for `M` the sections over the *closed fibre*, and the
only producer of one in the repository,
`Stacks.LocalCohomology.iso_restrict_tilde_globalSectionsModule`, builds it for `M` the sections
over the *punctured* spectrum, which makes the cokernel statement vacuous here. The route taken
instead is the global-sections clause of [Stacks, Tag 01YB].

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 0F28](https://stacks.math.columbia.edu/tag/0F28)
* [Stacks Project, Tag 0F2A](https://stacks.math.columbia.edu/tag/0F2A)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.AlgebraicGeometry.PrincipalIdealExtension

universe u

namespace Stacks.Algebraization

/-! ### Restriction to the punctured closed fibre is bijective on global sections -/

/-- **Restriction to the punctured closed fibre is bijective on the global sections of an
invertible module on the closed fibre.** The closed fibre is the spectrum of `A / fA`, whose
depth is at least two when that of `A` is at least three, and an invertible module is coherent
and reflexive, so Hartogs extension identifies it with the direct image of its restriction. -/
public theorem bijective_pullbackGlobalSections_puncturedClosedFibre (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (F₀ : (closedFibre A f).Modules) [Stacks.Ample.IsInvertibleModule (closedFibre A f) F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    Function.Bijective (pullbackGlobalSections (puncturedClosedFibre A f).ι F₀) := by
  have hI : Ideal.span {f} ≠ (⊤ : Ideal A) := fun h =>
    (maximalIdeal.isMaximal A).ne_top
      (top_unique (h ▸ Ideal.span_le.mpr (by simpa using hf)))
  have : Nontrivial (A ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing (A ⧸ Ideal.span {f}) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
  have := isIso_unit_puncturedClosedFibre A f hf hreg F₀ hdepth
  exact bijective_pullbackGlobalSections_of_isIso_unit (puncturedClosedFibre A f).ι F₀

/-! ### The closed-fibre partner of a global section -/

/-- **Every global section of the punctured-spectrum member of an invertible triple has a
closed-fibre partner.** Its image under `Stacks.Algebraization.globalSectionsMap` is the
restriction of a global section of the closed-fibre member, because that restriction is
bijective. No adjustment of the section is needed, so a nonvanishing condition imposed on it
survives. -/
public theorem exists_eq_globalSectionsMap {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (x : Γ(L.F, ⊤)) :
    ∃ x₀ : Γ(L.F₀, ⊤),
      globalSectionsMap A f L x =
        pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀ := by
  let := hL.invertible_F₀
  obtain ⟨x₀, hx₀⟩ := (bijective_pullbackGlobalSections_puncturedClosedFibre A f hf hreg L.F₀
    hdepth).surjective (globalSectionsMap A f L x)
  exact ⟨x₀, hx₀.symm⟩

/-! ### The morphism of coherent triples out of the unit -/

/-- **The morphism of coherent triples `(s, s_0) : (𝒪_U, 𝒪_{X_0}, 1) ⟶ (ℒ, ℒ_0, λ)` of
[Stacks, Tag 0F27].** It is the pair of morphisms out of the structure sheaves attached to two
corresponding global sections; its compatibility square is
`Stacks.Algebraization.hcompat_of_eq_globalSectionsMap` read through
`Stacks.Algebraization.hcompat_iff_hom_compatible`. -/
public noncomputable def CoherentTriple.homUnitOfGlobalSections {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A}
    (h : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme))
    {L : CoherentTriple A f} (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤))
    (hx : globalSectionsMap A f L x =
      pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀) :
    (CoherentTriple.unit A f h).Hom L where
  onPunctured := Scheme.Modules.unitHomEquivTop L.F x
  onClosedFibre := Scheme.Modules.unitHomEquivTop L.F₀ x₀
  compatible :=
    (hcompat_iff_hom_compatible h (Scheme.Modules.unitHomEquivTop L.F x)
      (Scheme.Modules.unitHomEquivTop L.F₀ x₀)).1
      (hcompat_of_eq_globalSectionsMap x x₀ hx)

/-- **Multiplication by a corresponding pair of global sections of an invertible triple**, as a
morphism from the `n`-th twist of a coherent triple to its `(n + 1)`-st. This is the left-hand
map of the short exact sequence of the induction step of [Stacks, Tag 0F27], with the
compatibility hypothesis of `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` discharged
from the equation of global sections. -/
public noncomputable def CoherentTriple.mulSectionTwistZOfGlobalSections {A : Type u}
    [CommRing A] [IsLocalRing A] {f : A} (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤))
    (hx : globalSectionsMap A f L x =
      pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀)
    (n : ℤ) : (T.twistZ L hL n).Hom (T.twistZ L hL (n + 1)) :=
  T.mulSectionTwistZ L hL (Scheme.Modules.unitHomEquivTop L.F x)
    (Scheme.Modules.unitHomEquivTop L.F₀ x₀) (hcompat_of_eq_globalSectionsMap x x₀ hx) n

/-! ### The section pair of the induction step -/

/-- **The section pair of the induction step of [Stacks, Tag 0F27].** For the fixed invertible
triple `L` over a Noetherian local ring of depth at least three and any triple `T` being
twisted, there is a global section of each member of `L`, corresponding over the punctured
closed fibre, whose punctured-spectrum member does not vanish at any point of
`Ass(T.F) ∪ Ass(T.F / f T.F)`. -/
public theorem exists_sectionPair_nonvanishing_on_associatedPoints {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (T : CoherentTriple A f) :
    letI := hL.invertible_F
    ∃ (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤)),
      globalSectionsMap A f L x =
          pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀ ∧
        (Stacks.Divisors.associatedPoints T.F ∪
            Stacks.Divisors.associatedPoints
              (cokernel (smulPowHom T.F (scalarOnOpen A f ⊤) 1))) ⊆
          (Stacks.NonvanishingOpen.nonvanishingOpen
            (Stacks.Divisors.puncturedSpectrum A).toScheme L.F x : Set _) := by
  let := hL.invertible_F
  obtain ⟨x, hx⟩ := exists_section_nonvanishing_on_associatedPoints hL T
  obtain ⟨x₀, hx₀⟩ := exists_eq_globalSectionsMap hf hreg hdepth hL x
  exact ⟨x, x₀, hx₀, hx⟩

/-- **The section pair of the induction step, as a morphism of coherent triples out of the unit
triple.** This is the morphism `(s, s_0)` of [Stacks, Tag 0F27], together with the global
section its punctured-spectrum member comes from and the nonvanishing of that section on the
associated points of `T.F` and of `T.F / f T.F`. -/
public theorem exists_homUnit_nonvanishing_on_associatedPoints {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (T : CoherentTriple A f) :
    letI := hL.invertible_F
    ∃ (x : Γ(L.F, ⊤))
      (φ : (CoherentTriple.unit A f hL.isFTorsionFree_unitModule).Hom L),
      φ.onPunctured = Scheme.Modules.unitHomEquivTop L.F x ∧
        (Stacks.Divisors.associatedPoints T.F ∪
            Stacks.Divisors.associatedPoints
              (cokernel (smulPowHom T.F (scalarOnOpen A f ⊤) 1))) ⊆
          (Stacks.NonvanishingOpen.nonvanishingOpen
            (Stacks.Divisors.puncturedSpectrum A).toScheme L.F x : Set _) := by
  let := hL.invertible_F
  obtain ⟨x, x₀, hx₀, hx⟩ :=
    exists_sectionPair_nonvanishing_on_associatedPoints hf hreg hdepth hL T
  exact ⟨x, CoherentTriple.homUnitOfGlobalSections hL.isFTorsionFree_unitModule x x₀ hx₀,
    rfl, hx⟩

end Stacks.Algebraization

end
