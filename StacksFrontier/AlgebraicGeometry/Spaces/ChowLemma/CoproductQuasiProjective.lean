module

public import StacksFrontier.AlgebraicGeometry.Blowup.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.CoproductImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.HProjective

/-!
# Disjoint unions of H-projective and H-quasi-projective schemes over a base

The induction of Stacks 089J ends by forming the disjoint union `X' ⨿ T'` of two schemes which
are H-quasi-projective over `Spec A` and using it as the source of the cover. For that step one
needs the disjoint union of two H-quasi-projective schemes over a base to be H-quasi-projective
over that base, which is the statement proved here — modulo one input about projective spaces
alone, stated as `AlgebraicGeometry.HasDisjointProjectiveEmbeddings`.

## Main definitions

* `AlgebraicGeometry.HasDisjointProjectiveEmbeddings`: the property of a base scheme `S` that
  any two relative projective spaces over it embed as closed subschemes of a single relative
  projective space over it *with disjoint images*. Concretely this is the pair of
  complementary linear embeddings `ℙⁿ_S, ℙᵐ_S ↪ ℙ^{n + m + 1}_S`.

## Main results

* `AlgebraicGeometry.isProjectiveMorphism_coprodDesc`: for a base with disjoint projective
  embeddings, the disjoint union of two schemes H-projective over it is H-projective over it.
* `AlgebraicGeometry.isHQuasiProjective_coprodDesc`: the same for H-quasi-projectivity.

## Implementation notes

The hypothesis `AlgebraicGeometry.HasDisjointProjectiveEmbeddings S` is a statement about
projective spaces over `S` and mentions neither of the two schemes being glued. It holds for
every base, by `AlgebraicGeometry.hasDisjointProjectiveEmbeddings` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChowLemma/DisjointProjectiveEmbeddings.lean`.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.QuasiProjectiveCompactification

universe u

namespace AlgebraicGeometry

/-- **Two relative projective spaces over `S` embed disjointly in a third.** For every pair of
dimensions `n`, `m` there are a dimension `N` and two closed immersions over `S` of `ℙⁿ_S` and
`ℙᵐ_S` into `ℙᴺ_S` whose images are disjoint.

This is the input `ℙⁿ_S ⊔ ℙᵐ_S ↪ ℙ^{n + m + 1}_S` — the pair of complementary linear
embeddings — on which the two results below depend. It is a statement about projective spaces
over `S` only. -/
def HasDisjointProjectiveEmbeddings (S : Scheme.{u}) : Prop :=
  ∀ n m : ℕ, ∃ (N : ℕ) (a : projectiveSpaceOver n S ⟶ projectiveSpaceOver N S)
    (b : projectiveSpaceOver m S ⟶ projectiveSpaceOver N S),
    IsClosedImmersion a ∧ IsClosedImmersion b ∧
      a ≫ (projectiveSpaceOver N S ↘ S) = (projectiveSpaceOver n S ↘ S) ∧
      b ≫ (projectiveSpaceOver N S ↘ S) = (projectiveSpaceOver m S ↘ S) ∧
      Disjoint (Set.range a.base) (Set.range b.base)

/-- A morphism out of a coproduct is determined by its composites with the two inclusions. -/
private theorem coprod_desc_comp_eq_desc {X Y Z S : Scheme.{u}} {a : X ⟶ Z} {b : Y ⟶ Z}
    {h : Z ⟶ S} {f : X ⟶ S} {g : Y ⟶ S} (ha : a ≫ h = f) (hb : b ≫ h = g) :
    coprod.desc a b ≫ h = coprod.desc f g := by
  rw [coprod.desc_comp, ha, hb]

/-- **The disjoint union of two schemes H-projective over `S` is H-projective over `S`**, for a
base with disjoint projective embeddings.

The two closed immersions into `ℙⁿ_S` and `ℙᵐ_S` are composed with the two disjoint closed
immersions into `ℙᴺ_S`; the composites are closed immersions with disjoint images, so the
morphism they induce out of the coproduct is a closed immersion by
`AlgebraicGeometry.isClosedImmersion_coprodDesc`, and it is a morphism over `S`. -/
theorem isProjectiveMorphism_coprodDesc {X Y S : Scheme.{u}}
    (hS : HasDisjointProjectiveEmbeddings S) {f : X ⟶ S} {g : Y ⟶ S}
    (hf : IsProjectiveMorphism f) (hg : IsProjectiveMorphism g) :
    IsProjectiveMorphism (coprod.desc f g) := by
  obtain ⟨n, i, hi, hif⟩ := hf
  obtain ⟨m, j, hj, hjg⟩ := hg
  obtain ⟨N, a, b, ha, hb, haS, hbS, hab⟩ := hS n m
  have := hi
  have := hj
  have := ha
  have := hb
  have hdisj : Disjoint (Set.range (i ≫ a).base) (Set.range (j ≫ b).base) := by
    refine hab.mono (fun _ hp => ?_) (fun _ hp => ?_)
    · obtain ⟨x, rfl⟩ := hp
      exact ⟨i.base x, rfl⟩
    · obtain ⟨x, rfl⟩ := hp
      exact ⟨j.base x, rfl⟩
  refine ⟨N, coprod.desc (i ≫ a) (j ≫ b),
    isClosedImmersion_coprodDesc (i ≫ a) (j ≫ b) hdisj,
    coprod_desc_comp_eq_desc (by rw [Category.assoc, haS, hif])
      (by rw [Category.assoc, hbS, hjg])⟩

/-- **The disjoint union of two schemes H-quasi-projective over `S` is H-quasi-projective over
`S`**, for a base with disjoint projective embeddings.

Each of the two is an open subscheme of a scheme H-projective over `S` by Tag 07RM, in the
form `exists_isOpenImmersion_isHProjective_of_isHQuasiProjective` of the namespace
`Stacks.QuasiProjectiveCompactification`. The disjoint union of the two compactifications is
H-projective over `S` by
`AlgebraicGeometry.isProjectiveMorphism_coprodDesc`, the disjoint union of the two open
immersions is an open immersion by `AlgebraicGeometry.isOpenImmersion_coprodDesc` — the images
of the two coproduct inclusions being disjoint — and the composite is quasi-compact by
`AlgebraicGeometry.quasiCompact_coprodDesc`. Tag 07RM backwards concludes.

This is the step with which the induction of Stacks 089J assembles the cover `X' ⨿ T' ⟶ X`
out of the cover of the open stratum and the cover of its complement. -/
theorem isHQuasiProjective_coprodDesc {X Y S : Scheme.{u}}
    (hS : HasDisjointProjectiveEmbeddings S) {f : X ⟶ S} {g : Y ⟶ S}
    (hf : IsHQuasiProjective f) (hg : IsHQuasiProjective g) :
    IsHQuasiProjective (coprod.desc f g) := by
  obtain ⟨X', jX, p, hjX, hp, hjXp⟩ :=
    exists_isOpenImmersion_isHProjective_of_isHQuasiProjective (f := f) hf
  obtain ⟨Y', jY, q, hjY, hq, hjYq⟩ :=
    exists_isOpenImmersion_isHProjective_of_isHQuasiProjective (f := g) hg
  have := hjX
  have := hjY
  have := hf.quasiCompact
  have := hg.quasiCompact
  have hdisj : Disjoint (Set.range (jX ≫ (coprod.inl : X' ⟶ X' ⨿ Y')).base)
      (Set.range (jY ≫ (coprod.inr : Y' ⟶ X' ⨿ Y')).base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact absurd hy (inr_ne_inl X' Y' (jX.base x) (jY.base y))
  refine isHQuasiProjective_of_exists_isOpenImmersion_isHProjective
    (quasiCompact_coprodDesc f g)
    ⟨X' ⨿ Y', coprod.desc (jX ≫ coprod.inl) (jY ≫ coprod.inr), coprod.desc p q,
      isOpenImmersion_coprodDesc (jX ≫ coprod.inl) (jY ≫ coprod.inr) hdisj,
      isProjectiveMorphism_coprodDesc hS hp hq,
      coprod_desc_comp_eq_desc (by rw [Category.assoc, coprod.inl_desc, hjXp])
        (by rw [Category.assoc, coprod.inr_desc, hjYq])⟩

end AlgebraicGeometry

end
