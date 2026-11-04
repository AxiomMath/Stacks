module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.FibreHomologyDeltaFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.FreePresheafFibreDecomposition

/-!
# Universality of the fibre-homology δ-functor

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site `(D, O_D)`, as in
Stacks 08P8, with small fibres. For an abelian presheaf `F` on the total category the presheaves

```
L_{n,p}(F) : V ↦ H_n(C_V, F|_{C_V})
```

of Stacks 08PI form a homological δ-functor
(`Stacks.Sites.FibredCategory.fiberHomologyPresheafDeltaFunctor`), as do their associated sheaves
`L_n(F)`. Both are **universal** in the sense of the dual of Stacks 010T.

Both δ-functors are coeffaceable: every abelian presheaf on the total category receives an
epimorphism `Stacks.CategoryHomology.uliftFreeCoverHom` from a direct sum of universe-lifted free
abelian presheaves on representables, and the fibre homology of that direct sum vanishes in every
positive degree.

## Main results

* `Stacks.CategoryHomology.isZero_of_isZero_evaluation`: a diagram is a zero object as soon as
  all its values are.
* `Stacks.CategoryHomology.presheafComp_directSumPresheaf`: restriction of presheaves along a
  functor commutes with sectionwise direct sums.
* `Stacks.CategoryHomology.categoryHomology_isZero_of_directSum`: vanishing of the homology of a
  small category in a positive degree passes to sectionwise direct sums of coefficients.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.Coeffaceable.postcomp`: coeffaceability is
  preserved by postcomposition with an exact additive functor.
* `Stacks.Sites.FibredCategory.isZero_fiberHomologyPresheaf_uliftFreeCover`: the fibre homology of
  the canonical presentation of an abelian presheaf vanishes in every positive degree.
* `Stacks.Sites.FibredCategory.coeffaceable_fiberHomologyPresheafDeltaFunctor` and
  `Stacks.Sites.FibredCategory.isUniversal_fiberHomologyPresheafDeltaFunctor`: the δ-functor of
  the presheaves `L_{n,p}` is coeffaceable, hence universal.
* `Stacks.Sites.FibredCategory.coeffaceable_fiberHomologySheafDeltaFunctor` and
  `Stacks.Sites.FibredCategory.isUniversal_fiberHomologySheafDeltaFunctor`: the δ-functor of the
  sheaves `L_n` of Stacks 08PI is coeffaceable, hence universal.

## References

* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08PI](https://stacks.math.columbia.edu/tag/08PI)
* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryHomology

/-- A diagram in a category with zero morphisms is a zero object as soon as all its values are. -/
lemma isZero_of_isZero_evaluation.{uI, vI, uB, vB} {I : Type uI} [Category.{vI} I]
    {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B] {X : I ⥤ B}
    (h : ∀ i, IsZero (X.obj i)) : IsZero X :=
  X.isZero h

/-- **Restriction of abelian presheaves along a functor commutes with sectionwise direct sums.** -/
lemma presheafComp_directSumPresheaf.{u, u', w'} {C : Type u} {C' : Type u'} [SmallCategory C]
    [SmallCategory C'] (f : C' ⥤ C) {ι : Type w'} (G : ι → (Cᵒᵖ ⥤ AddCommGrpCat.{w'})) :
    f.op ⋙ directSumPresheaf G = directSumPresheaf fun i => f.op ⋙ G i :=
  rfl

/-- **Vanishing of the homology of a small category passes to sectionwise direct sums of the
coefficients.** -/
theorem categoryHomology_isZero_of_directSum.{u, v} {C : Type u} [SmallCategory C]
    {ι : Type (max u v)} (G : ι → (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})) (n : ℕ)
    (h : ∀ i, IsZero (categoryHomology.{u, v} (G i) (n + 1))) :
    IsZero (categoryHomology.{u, v} (directSumPresheaf G) (n + 1)) :=
  categoryHomology_isZero_of_replacementComplex_homology_isZero.{u, v} _ (n + 1)
    (replacementComplex_homology_isZero_of_directSum G n fun i =>
      (h i).of_iso (categoryHomologyReplacementIso.{u, v} (G i) (n + 1)).symm)

namespace HomologicalDeltaFunctor

universe uA vA uB vB uB' vB'

variable {A : Type uA} [Category.{vA} A] [Abelian A] {B : Type uB} [Category.{vB} B] [Abelian B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] (E : B ⥤ B') [E.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- **Coeffaceability is preserved by postcomposition with an exact additive functor.** -/
theorem Coeffaceable.postcomp (H : HomologicalDeltaFunctor A B) [H.Coeffaceable] :
    (H.postcomp E).Coeffaceable where
  nonempty X n := by
    obtain ⟨e⟩ := Coeffaceable.nonempty (H := H) X n
    refine ⟨{ P := e.P, π := e.π, epi := e.epi, map_π := ?_ }⟩
    show E.map ((H.functor (n + 1)).map e.π) = 0
    rw [e.map_π, E.map_zero]

end HomologicalDeltaFunctor

end Stacks.CategoryHomology

namespace Stacks.Sites.FibredCategory

open Stacks.CategoryHomology

universe uD vD uC w

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

variable (s : FibredCategorySituation.{uD, vD, uC, uC, w})

/-- **The fibre homology of the canonical presentation of an abelian presheaf vanishes in positive
degrees.** -/
theorem isZero_fiberHomologyPresheaf_uliftFreeCover
    (X : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (n : ℕ) :
    IsZero ((fiberHomologyPresheafFunctor s (n + 1)).obj
      (uliftFreeCover.{uC, max w uD vD uC} X)) := by
  refine isZero_of_isZero_evaluation fun V => ?_
  have heq : (Functor.Fiber.fiberInclusion (p := s.p) (S := V.unop)).op ⋙
        uliftFreeCover.{uC, max w uD vD uC} X =
      directSumPresheaf (fun i : uliftFreeCoverIndex.{uC, max w uD vD uC} X =>
        (Functor.Fiber.fiberInclusion (p := s.p) (S := V.unop)).op ⋙
          uliftFreeRepresentablePresheaf.{uC, max w uD vD uC} i.1) :=
    presheafComp_directSumPresheaf.{uC, uC, max w uD vD uC} _ _
  refine categoryHomology_isZero_of_iso.{uC, max w uD vD uC} (eqToIso heq) (n + 1) ?_
  refine categoryHomology_isZero_of_directSum.{uC, max w uD vD uC} _ n fun i => ?_
  exact categoryHomology_fiberRestriction_isZero.{uC, uD, vD, max w uD vD uC} i.1 V.unop n

/-- **The δ-functor of the presheaves of fibre homology is coeffaceable.** Every abelian presheaf
on the total category is an epimorphic image of the canonical presentation by universe-lifted free
abelian presheaves on representables — the presheaves `j_{U'!}^{PAb} ℤ_{U'}` of Stacks 08PJ — and
all the presheaves `L_{m,p}` with `m ≥ 1` vanish on that presentation. -/
theorem coeffaceable_fiberHomologyPresheafDeltaFunctor :
    (fiberHomologyPresheafDeltaFunctor s).Coeffaceable :=
  HomologicalDeltaFunctor.Coeffaceable.of_exists_epi_isZero _ fun X n =>
    ⟨uliftFreeCover.{uC, max w uD vD uC} X, uliftFreeCoverHom.{uC, max w uD vD uC} X,
      inferInstance, isZero_fiberHomologyPresheaf_uliftFreeCover s X n⟩

/-- **The δ-functor of the presheaves of fibre homology is universal**, by the dual of Stacks
010T: every morphism of δ-functors into it is determined by, and can be prescribed arbitrarily
in, degree zero. -/
theorem isUniversal_fiberHomologyPresheafDeltaFunctor :
    (fiberHomologyPresheafDeltaFunctor s).IsUniversal :=
  have := coeffaceable_fiberHomologyPresheafDeltaFunctor s
  HomologicalDeltaFunctor.isUniversal_of_coeffaceable _

/-- **The δ-functor of the sheaves `L_n` of Stacks 08PI is coeffaceable.** -/
theorem coeffaceable_fiberHomologySheafDeltaFunctor
    [HasSheafify s.base.J AddCommGrpCat.{max w uD vD uC}] :
    (fiberHomologySheafDeltaFunctor s).Coeffaceable :=
  have := coeffaceable_fiberHomologyPresheafDeltaFunctor s
  HomologicalDeltaFunctor.Coeffaceable.postcomp
    (presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC})
    (fiberHomologyPresheafDeltaFunctor s)

/-- **The δ-functor of the sheaves `L_n` of Stacks 08PI is universal**, by the dual of Stacks
010T: every morphism of δ-functors into it is determined by, and can be prescribed arbitrarily
in, degree zero. -/
theorem isUniversal_fiberHomologySheafDeltaFunctor
    [HasSheafify s.base.J AddCommGrpCat.{max w uD vD uC}] :
    (fiberHomologySheafDeltaFunctor s).IsUniversal :=
  have := coeffaceable_fiberHomologySheafDeltaFunctor s
  HomologicalDeltaFunctor.isUniversal_of_coeffaceable _

end Stacks.Sites.FibredCategory

end
