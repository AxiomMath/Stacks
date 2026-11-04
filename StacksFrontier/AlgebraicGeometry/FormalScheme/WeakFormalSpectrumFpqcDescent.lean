module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcDescent
public import StacksFrontier.AlgebraicGeometry.FormalScheme.McQuillanFormalScheme

/-!
# Descent of points of McQuillan's formal spectrum along a faithfully flat morphism

Stacks 0AI3 records that the counterparts of Lemmas 87.2.1 and 87.2.2 hold for the larger
category of formal schemes built on weak admissibility, with the same proofs. The separatedness
half of the counterpart of Lemma 87.2.2 is
`AlgebraicGeometry.isSeparated_fpqcTopology_mcQuillanFormalSchemePoints`; this file supplies the
*existence* half at an affine test scheme, which is the affine descent step the source's proof of
Lemma 87.2.2 reduces to.

Let `A` be a topological ring and let `P` be a weak ideal system on it with a member `I₀`. Let
`Spec S → Spec R` be a faithfully flat morphism of affine schemes. A point
`Spec S ⟶ Spf_P A` of the formal spectrum taken along `P` whose two pullbacks to a scheme over
`Spec R` always agree descends to a point `Spec R ⟶ Spf_P A`, provided the canonical map
`A → Γ(Spf_P A, 𝒪)` is an isomorphism.

This is the source's argument verbatim, and it is `P`-generic: the point factors through some
`Spec (A/I)` with `I` a member of the system by
`AlgebraicGeometry.exists_factor_spfQuotientPointOn`; the factorisation inherits the descent
condition because `Spec (A/I) → Spf_P A` is injective on points
(`AlgebraicGeometry.schemeToFormalScheme_map_comp_spfQuotientPointOn_injective`); and a morphism of
*schemes* descends along a faithfully flat morphism because the fpqc topology is subcanonical.
Nothing in it asks that the members of `P` be the powers of a single ideal.

For the ideals of definition of an admissible ring the hypothesis on the canonical map is Stacks
0AHY; for the weak ideals of definition of a weakly admissible ring it is
`AlgebraicGeometry.isIso_spfwGammaHom`, which is itself the identification that the intersection
and fundamental-system clauses of Stacks 0AI3 buy.

## Main results

* `AlgebraicGeometry.exists_comp_eq_of_flat_surjective_spfLTRSOn`: the descent, for an arbitrary
  weak ideal system.
* `AlgebraicGeometry.exists_comp_eq_of_flat_surjective_spfwLTRS`: **Stacks 0AI3**, the same for
  McQuillan's formal spectrum of a weakly admissible topological ring.

## References

* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open TopologicalRing

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

omit [IsLinearTopology A A] in
/-- **A point of a formal spectrum over an affine scheme descends along a faithfully flat
morphism of affine schemes.** Let `P` be a weak ideal system on `A` with member `I₀`, and suppose
the canonical map `A → Γ(Spf_P A, 𝒪)` is an isomorphism. Let `Spec S → Spec R` be flat and
surjective. A point `u : Spec S ⟶ Spf_P A` of locally topologically ringed spaces whose two
pullbacks along any pair of morphisms agreeing over `Spec R` agree is the pullback of a point
`Spec R ⟶ Spf_P A`.

The point `u` factors as `Spec S → Spec (A/I) → Spf_P A` for some member `I` of the system by
`AlgebraicGeometry.exists_factor_spfQuotientPointOn`; the morphism of schemes
`Spec S → Spec (A/I)` inherits the descent condition because `Spec (A/I) → Spf_P A` is injective
on points, so it descends to `Spec R → Spec (A/I)` by subcanonicity of the fpqc topology, and
composing the descended morphism with `Spec (A/I) → Spf_P A` gives the point sought. -/
theorem exists_comp_eq_of_flat_surjective_spfLTRSOn (I₀ : SpfIndex A P)
    (hiso : IsIso (spfGammaHomOn A P)) {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hflat : Flat (Spec.map φ)) (hsurj : Surjective (Spec.map φ))
    (u : schemeToLTRSObj (Spec S) ⟶ spfLTRSOn A P I₀)
    (hu : ∀ {Z : Scheme.{u}} (p₁ p₂ : Z ⟶ Spec S), p₁ ≫ Spec.map φ = p₂ ≫ Spec.map φ →
      schemeToLTRS.map p₁ ≫ u = schemeToLTRS.map p₂ ≫ u) :
    ∃ t : schemeToLTRSObj (Spec R) ⟶ spfLTRSOn A P I₀,
      schemeToLTRS.map (Spec.map φ) ≫ t = u := by
  obtain ⟨I, a, ha⟩ := exists_factor_spfQuotientPointOn A I₀ hiso (Spec S) u
  have hbridge : ∀ {Z W : Scheme.{u}} (p : Z ⟶ W),
      (schemeToFormalScheme.map p).hom = schemeToLTRS.map p := fun _ => rfl
  have ha' : schemeToLTRS.map a ≫ spfQuotientPointOn A I₀ I = u := by
    rw [← hbridge a]; exact ha
  have key : ∀ (Z : Scheme.{u}) (p : Z ⟶ Spec S),
      (schemeToFormalScheme.map (p ≫ a)).hom ≫ spfQuotientPointOn A I₀ I
        = schemeToLTRS.map p ≫ u := fun Z p => by
    rw [hbridge, schemeToLTRS.map_comp]
    exact (Category.assoc _ _ _).trans (congrArg (schemeToLTRS.map p ≫ ·) ha')
  have hdesc : ∀ {Z : Scheme.{u}} (p₁ p₂ : Z ⟶ Spec S),
      p₁ ≫ Spec.map φ = p₂ ≫ Spec.map φ → p₁ ≫ a = p₂ ≫ a := fun {Z} p₁ p₂ hp =>
    schemeToFormalScheme_map_comp_spfQuotientPointOn_injective A I₀ I
      ((key Z p₁).trans ((hu p₁ p₂ hp).trans (key Z p₂).symm))
  have := hsurj
  have hsheaf := (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fpqcTopology.{u}) (yoneda.obj (Spec (spfQuotientOn A I))))
    _ (Scheme.Hom.generate_singleton_mem_propQCTopology (P := @Flat) (Spec.map φ) hflat)
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_singleton] at hsheaf
  obtain ⟨t, ht, -⟩ := hsheaf a hdesc
  have ht' : Spec.map φ ≫ t = a := ht
  exact ⟨schemeToLTRS.map t ≫ spfQuotientPointOn A I₀ I,
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ spfQuotientPointOn A I₀ I)
      ((schemeToLTRS.map_comp _ t).symm.trans (congrArg schemeToLTRS.map ht))).trans ha')⟩

/-- **Stacks 0AI3**, the existence half of the counterpart of Lemma 87.2.2 at an affine test
scheme. For a weakly admissible topological ring `A`, a point `Spec S ⟶ Spfw A` of McQuillan's
formal spectrum whose two pullbacks along any pair of morphisms agreeing over `Spec R` agree
descends along a faithfully flat morphism `Spec S → Spec R` of affine schemes.

This is the affine descent step the source's proof of Lemma 87.2.2 reduces to, and it is that
proof unchanged: the weak ideals of definition of `A` form a weak ideal system, and the
identification `Γ(Spfw A, 𝒪) = A` it consumes is
`AlgebraicGeometry.isIso_spfwGammaHom`. The separatedness half, which together with this one is
the sheaf condition for the covering `{Spec S → Spec R}`, is
`AlgebraicGeometry.isSeparated_fpqcTopology_mcQuillanFormalSchemePoints`. -/
@[stacks 0AI3 "the counterpart of Lemma 87.2.2: existence of an amalgamation at an affine test \
scheme, for a point of McQuillan's formal spectrum of a weakly admissible ring along a \
faithfully flat morphism of affine schemes"]
theorem exists_comp_eq_of_flat_surjective_spfwLTRS (hA : IsWeaklyAdmissible A)
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (hflat : Flat (Spec.map φ))
    (hsurj : Surjective (Spec.map φ)) (u : schemeToLTRSObj (Spec S) ⟶ spfwLTRS A hA.1)
    (hu : ∀ {Z : Scheme.{u}} (p₁ p₂ : Z ⟶ Spec S), p₁ ≫ Spec.map φ = p₂ ≫ Spec.map φ →
      schemeToLTRS.map p₁ ≫ u = schemeToLTRS.map p₂ ≫ u) :
    ∃ t : schemeToLTRSObj (Spec R) ⟶ spfwLTRS A hA.1,
      schemeToLTRS.map (Spec.map φ) ≫ t = u :=
  exists_comp_eq_of_flat_surjective_spfLTRSOn A (weaklyPreAdmissibleSpfIndex A hA.1)
    (isIso_spfwGammaHom A hA) φ hflat hsurj u hu

end

end AlgebraicGeometry

end
