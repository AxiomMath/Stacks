module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.Etale

/-!
# Étaleness from an étale covering of the source

A morphism of schemes is étale as soon as its source is covered by étale morphisms along which
it becomes étale. This is `AlgebraicGeometry.etale_isLocalAtSource` (Tag 036W) read through the
description of the members of the étale precoverage, and it is stated here in the pointwise form
in which it is used: a family of étale morphisms into the source whose ranges cover it and whose
composites with the morphism are étale.

No finite presentation hypothesis is assumed. Descending étaleness along a flat base change requires
the morphism to be locally of finite presentation (Tag 0476,
`AlgebraicGeometry.etaleAt_iff_of_isPullback`), and that hypothesis is genuinely needed there. Along
an *étale* covering of the source no such hypothesis is needed: local finite presentation of the
morphism is itself a consequence, by Tag 02KL, which is how
`Stacks.Etale.etale_of_comp_surjective_etale` is proved. So a morphism whose étaleness is only known
after an étale base change can be concluded étale without knowing beforehand that it is locally of
finite presentation.

## Main results

* `AlgebraicGeometry.etale_of_forall_comp_etale`: **a morphism with an étale covering of its
  source along which it becomes étale is étale.**
* `AlgebraicGeometry.etale_of_forall_exists_etale_comp`: the same with the covering family
  replaced by a pointwise existence statement.

## References

* [Stacks Project, Tag 02KL](https://stacks.math.columbia.edu/tag/02KL)
* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 036W](https://stacks.math.columbia.edu/tag/036W)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A morphism of schemes with an étale covering of its source along which it becomes étale is
étale.** No finite presentation hypothesis is needed: unlike descent along a flat base change,
descent along an étale covering of the source supplies local finite presentation itself. -/
theorem etale_of_forall_comp_etale {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*}
    {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    (hsurj : ∀ x : X, ∃ i, x ∈ Set.range (g i).base)
    (hg : ∀ i, Etale (g i)) (hgf : ∀ i, Etale (g i ≫ f)) :
    Etale f := by
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := @Etale.{u})
    (K := Scheme.etalePrecoverage) (R := Presieve.ofArrows W g)
    ((Scheme.ofArrows_mem_precoverage_iff
      (P := (@Etale.{u} : MorphismProperty Scheme.{u}))).mpr ⟨hsurj, hg⟩) ?_
  rintro U k ⟨i⟩
  exact hgf i

/-- **A morphism of schemes is étale as soon as every point of its source is in the range of an
étale morphism whose composite with it is étale.** The covering family is indexed by the points
of the source. -/
theorem etale_of_forall_exists_etale_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : ∀ x : X, ∃ (W : Scheme.{u}) (g : W ⟶ X), Etale g ∧ Etale (g ≫ f) ∧
      x ∈ Set.range g.base) :
    Etale f := by
  choose W g hg hgf hmem using H
  exact etale_of_forall_comp_etale f g (fun x => ⟨x, hmem x⟩) hg hgf

end AlgebraicGeometry

end
