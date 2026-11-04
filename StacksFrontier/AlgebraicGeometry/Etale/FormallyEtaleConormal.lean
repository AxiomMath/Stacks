module

public import StacksFrontier.AlgebraicGeometry.Conormal.FirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleSmoothUnramified
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallyEtale.Lifting
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalSheaf

/-!
# Formal étaleness through the universal thickening, the conormal sheaf and the differentials

Let `f : X ⟶ S` be a morphism of schemes. [Stacks Project, Tag 04FE] characterises formal
étaleness of `f` in three further ways, each of them a condition on the universal first-order
thickening of `X` over `S`:

1. `f` is formally étale;
2. `f` is formally unramified and its universal first-order thickening is `X` itself;
3. `f` is formally unramified and its conormal sheaf `𝒞_{X/S}` vanishes;
4. the relative differentials `Ω_{X/S}` vanish and `𝒞_{X/S}` vanishes.

Each of (2), (3), (4) is stated as an equivalence with (1), so the three results together are the
cycle of equivalences the source asserts.

## Main results

* `AlgebraicGeometry.formallyEtale_iff_isIso_inclusion`: the equivalence of (1) and (2).
* `AlgebraicGeometry.isIso_inclusion_iff_isZero_universalConormalSheaf`: for a formally
  unramified morphism, triviality of the universal first-order thickening is vanishing of the
  conormal sheaf.
* `AlgebraicGeometry.formallyEtale_iff_isZero_universalConormalSheaf`: the equivalence of (1)
  and (3).
* `AlgebraicGeometry.formallyEtale_iff_isZero_relativeDifferentials_and_universalConormalSheaf`:
  the equivalence of (1) and (4).

## Implementation notes

Assertions (3) and (4) mention the conormal sheaf `Stacks.Thickenings.universalConormalSheaf`,
which is only defined for a formally unramified morphism. They are therefore stated as the
existence of a proof of formal unramifiedness together with the vanishing, the proof being used
to form the sheaf. In (4) that proof is obtained from the vanishing of the differentials through
[Stacks Project, Tag 02H9], so no separate unramifiedness clause appears.

"The universal first-order thickening of `X` over `S` is equal to `X`" is expressed by the
canonical inclusion `X ⟶ X'` being an isomorphism.

The equivalence (2) ⟺ (3) is
`Stacks.Conormal.isIso_iff_isZero_immersionConormalSheaf` applied to that inclusion: it is a
first-order thickening, so its conormal sheaf is its defining ideal sheaf, and the two vanish
together. The direction (1) ⟹ (2) uses the unique lifting property across the thickening
itself, `AlgebraicGeometry.FormallyEtale.existsUnique_lift` of [Stacks Project, Tag 04FD],
to produce a retraction, and the universal property of the thickening to see that the retraction
is a two-sided inverse. The direction (2) ⟹ (1) transports an arbitrary lifting problem across
that isomorphism and solves it by the universal property.

Formal unramifiedness of a formally étale morphism is not reproved here: it is the second half
of [Stacks Project, Tag 02HH],
`AlgebraicGeometry.formallyEtale_iff_formallySmooth_and_formallyUnramified`.

## References

* [Stacks Project, Tag 02H9](https://stacks.math.columbia.edu/tag/02H9)
* [Stacks Project, Tag 02HG](https://stacks.math.columbia.edu/tag/02HG)
* [Stacks Project, Tag 02HH](https://stacks.math.columbia.edu/tag/02HH)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
* [Stacks Project, Tag 04FD](https://stacks.math.columbia.edu/tag/04FD)
* [Stacks Project, Tag 04FE](https://stacks.math.columbia.edu/tag/04FE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Stacks Project, Tag 04FE, equivalence of (1) and (2).** A morphism of schemes is formally
étale if and only if it is formally unramified and the inclusion of its source into its universal
first-order thickening is an isomorphism, that is, the universal first-order thickening of `X`
over `S` is `X` itself.

Formal unramifiedness is part of the right-hand side because the universal first-order
thickening is only defined under it; for a formally étale morphism it comes from
[Stacks Project, Tag 02HH].

Forwards, the unique lifting property of [Stacks Project, Tag 04FD] applied to the thickening
itself produces a retraction of the inclusion, and the universal property of the thickening
identifies the other composite with the identity. Backwards, a lifting problem for `f` is
transported along the isomorphism and solved by the universal property, uniquely because the
universal property's lift is unique. -/
@[stacks 04FE "equivalence of (1) and (2)"]
public theorem formallyEtale_iff_isIso_inclusion (f : X ⟶ S) :
    FormallyEtale f ↔
      ∃ hf : FormallyUnramified f,
        letI : FormallyUnramified f := hf
        IsIso (universalFirstOrderThickening f).inclusion := by
  constructor
  · intro hf
    obtain ⟨-, hu⟩ := (formallyEtale_iff_formallySmooth_and_formallyUnramified f).mp hf
    let : FormallyUnramified f := hu
    refine ⟨hu, ?_⟩
    set t := universalFirstOrderThickening f
    have hc : 𝟙 X ≫ f = t.inclusion ≫ t.toBase := by
      rw [Category.id_comp, t.isUniversal.inclusion_toBase]
    obtain ⟨h, hh, -⟩ := FormallyEtale.existsUnique_lift f hf t.inclusion
      t.isUniversal.isFirstOrderThickening t.toBase (𝟙 X) hc
    obtain ⟨_, -, hauniq⟩ := t.isUniversal.existsUnique_lift t.inclusion
      t.isUniversal.isFirstOrderThickening (𝟙 X) t.toBase hc.symm
    have hright : h ≫ t.inclusion = 𝟙 t.ambient := by
      refine (hauniq (h ≫ t.inclusion) ⟨?_, ?_⟩).trans
        (hauniq (𝟙 t.ambient) ⟨by simp, by simp⟩).symm
      · rw [← Category.assoc, hh.1, Category.id_comp]
      · rw [Category.assoc, t.isUniversal.inclusion_toBase, hh.2]
    exact ⟨⟨h, hh.1, hright⟩⟩
  · rintro ⟨hf, hI⟩
    let : FormallyUnramified f := hf
    set t := universalFirstOrderThickening f
    let : IsIso t.inclusion := hI
    intro T T' hT hT' i hi p g hg
    let : IsAffine T := hT
    let : IsAffine T' := hT'
    obtain ⟨a, ha, hauniq⟩ := t.isUniversal.existsUnique_lift i hi g p hg.symm
    let e : X ≅ t.ambient := asIso t.inclusion
    have hhom : e.hom = t.inclusion := rfl
    have he : e.inv ≫ f = t.toBase := by
      rw [Iso.inv_comp_eq, hhom, t.isUniversal.inclusion_toBase]
    refine ⟨a ≫ e.inv, ⟨?_, ?_⟩, ?_⟩
    · rw [← Category.assoc, ha.1, Category.assoc, ← hhom, e.hom_inv_id, Category.comp_id]
    · rw [Category.assoc, he, ha.2]
    · intro b hb
      have hba : b ≫ e.hom = a := by
        refine hauniq (b ≫ e.hom) ⟨?_, ?_⟩
        · rw [← Category.assoc, hb.1, hhom]
        · rw [Category.assoc, hhom, t.isUniversal.inclusion_toBase, hb.2]
      rw [← hba, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- For a formally unramified morphism, the universal first-order thickening is trivial exactly
when the conormal sheaf of [Stacks Project, Tag 04F4] vanishes.

The conormal sheaf is by definition the conormal sheaf of the inclusion into the universal
first-order thickening, and that inclusion is a first-order thickening, so this is
`Stacks.Conormal.isIso_iff_isZero_immersionConormalSheaf`. -/
public theorem isIso_inclusion_iff_isZero_universalConormalSheaf (f : X ⟶ S)
    [FormallyUnramified f] :
    IsIso (universalFirstOrderThickening f).inclusion ↔ IsZero (universalConormalSheaf f) :=
  Stacks.Conormal.isIso_iff_isZero_immersionConormalSheaf
    (universalFirstOrderThickening f).inclusion
    (universalFirstOrderThickening f).isUniversal.isFirstOrderThickening.2

/-- **Stacks Project, Tag 04FE, equivalence of (1) and (3).** A morphism of schemes is formally
étale if and only if it is formally unramified and its conormal sheaf `𝒞_{X/S}` vanishes.

This is the equivalence of (1) and (2) combined with
`AlgebraicGeometry.isIso_inclusion_iff_isZero_universalConormalSheaf`. -/
@[stacks 04FE "equivalence of (1) and (3)"]
public theorem formallyEtale_iff_isZero_universalConormalSheaf (f : X ⟶ S) :
    FormallyEtale f ↔
      ∃ hf : FormallyUnramified f,
        letI : FormallyUnramified f := hf
        IsZero (universalConormalSheaf f) := by
  rw [formallyEtale_iff_isIso_inclusion]
  refine exists_congr fun hf => ?_
  let : FormallyUnramified f := hf
  exact isIso_inclusion_iff_isZero_universalConormalSheaf f

/-- **Stacks Project, Tag 04FE, equivalence of (1) and (4).** A morphism of schemes is formally
étale if and only if both its sheaf of relative differentials `Ω_{X/S}` and its conormal sheaf
`𝒞_{X/S}` vanish.

The formal unramifiedness needed to form the conormal sheaf is supplied by the vanishing of the
differentials, through [Stacks Project, Tag 02H9]. -/
@[stacks 04FE "equivalence of (1) and (4)"]
public theorem formallyEtale_iff_isZero_relativeDifferentials_and_universalConormalSheaf
    (f : X ⟶ S) :
    FormallyEtale f ↔
      ∃ hΩ : IsZero (Scheme.Hom.relativeDifferentials f),
        letI : FormallyUnramified f :=
          (Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials f).mpr hΩ
        IsZero (universalConormalSheaf f) := by
  rw [formallyEtale_iff_isZero_universalConormalSheaf]
  constructor
  · rintro ⟨hf, hC⟩
    let : FormallyUnramified f := hf
    exact ⟨(Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials f).mp hf, hC⟩
  · rintro ⟨hOmega, hC⟩
    exact ⟨(Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials f).mpr hOmega, hC⟩

end AlgebraicGeometry

end
