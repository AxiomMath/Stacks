module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.UniversalHomeomorphismFilteredColimit
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.RingColimitFiltered
public import StacksCore.Tactic.StacksAttribute

/-!
# The universal property of the absolute weak normalization of a ring

Let `A` be a commutative ring. Among the `A`-algebras whose spectrum morphism to `Spec A` is a
universal homeomorphism, the absolute weak normalization `Algebra.AbsoluteWeakNormalization A`
is terminal.

## Main definitions

* `Algebra.IsAbsoluteWeakNormalizationCandidate` is the property of an `A`-algebra whose
  spectrum morphism to `Spec A` is a universal homeomorphism.
* `Algebra.AbsoluteWeakNormalizationCategory` is the category of those algebras.
* `Algebra.absoluteWeakNormalizationCandidate` is the absolute weak normalization, regarded as
  an object of that category.
* `Algebra.stageToAbsoluteWeakNormalization` is the canonical map into the absolute weak
  normalization from an algebra which occurs in the colimit defining it.

## Main results

* `Algebra.stageToAbsoluteWeakNormalization_unique`: a finitely presented candidate has exactly
  one `A`-algebra map to the absolute weak normalization.
* `Algebra.ind_absoluteWeakNormalizationObject`: every candidate is a filtered colimit of
  finitely presented candidates.
* `Algebra.absoluteWeakNormalizationCandidate_isTerminal`: the terminality of the absolute weak
  normalization in the candidate category.

## Implementation notes

The algebras occurring in the colimit are the finitely presented candidates, that is the
objects of `Algebra.absoluteWeakNormalizationObject A`; the colimit is indexed by a small model
of that category, so the canonical map out of such an algebra is read off from the colimit leg
at a representative, and the equivalence with the small model makes it independent of the
representative.

For a general candidate the map is obtained by writing it as a filtered colimit of finitely
presented candidates, which is Tag 0EUJ, and descending the family of canonical maps of the
stages. Uniqueness is uniqueness at each stage, which in turn is the finite presentability of
the stage: a map out of it into a filtered colimit factors through some leg.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

## References

* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUJ](https://stacks.math.columbia.edu/tag/0EUJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] Cardinal.fact_isRegular_aleph0

universe u

namespace Algebra

variable (A : Type u) [CommRing A]

/-! ### The canonical map out of a finitely presented stage -/

/-- The canonical map to the absolute weak normalization from a finitely presented `A`-algebra
which is a universal homeomorphism over `A`, through a representative of it in the small index
category of the defining colimit. -/
def stageToAbsoluteWeakNormalization (C : CommAlgCat.{u} A)
    (hC : absoluteWeakNormalizationObject A C) :
    C ⟶ CommAlgCat.of A (AbsoluteWeakNormalization A) :=
  let e := equivSmallModel.{u} (absoluteWeakNormalizationObject A).FullSubcategory
  let c : (absoluteWeakNormalizationObject A).FullSubcategory := ⟨C, hC⟩
  (ObjectProperty.ι (absoluteWeakNormalizationObject A)).map (e.unitIso.app c).hom ≫
    colimit.ι (absoluteWeakNormalizationDiagram A) (e.functor.obj c)

/-- The canonical maps out of the finitely presented stages are compatible with the
`A`-algebra maps between them. -/
lemma stageToAbsoluteWeakNormalization_natural {C E : CommAlgCat.{u} A}
    (hC : absoluteWeakNormalizationObject A C) (hE : absoluteWeakNormalizationObject A E)
    (f : C ⟶ E) :
    f ≫ stageToAbsoluteWeakNormalization A E hE = stageToAbsoluteWeakNormalization A C hC := by
  let Q := absoluteWeakNormalizationObject A
  let e := equivSmallModel.{u} Q.FullSubcategory
  let c : Q.FullSubcategory := ⟨C, hC⟩
  let d : Q.FullSubcategory := ⟨E, hE⟩
  let f' : c ⟶ d := ObjectProperty.homMk f
  let D := absoluteWeakNormalizationDiagram A
  have hn := congrArg (ObjectProperty.ι Q).map (e.unitIso.hom.naturality f')
  change f'.hom ≫ (ObjectProperty.ι Q).map (e.unitIso.hom.app d) =
      (ObjectProperty.ι Q).map (e.unitIso.hom.app c) ≫ D.map (e.functor.map f') at hn
  show f'.hom ≫ ((ObjectProperty.ι Q).map (e.unitIso.hom.app d) ≫
    colimit.ι D (e.functor.obj d)) = (ObjectProperty.ι Q).map
      (e.unitIso.hom.app c) ≫ colimit.ι D (e.functor.obj c)
  rw [← Category.assoc, hn, Category.assoc, colimit.w]

/-- On an algebra which already occurs in the defining diagram, the canonical map is the
colimit leg. -/
lemma stageToAbsoluteWeakNormalization_diagram (i : AbsoluteWeakNormalizationIndex A) :
    stageToAbsoluteWeakNormalization A ((absoluteWeakNormalizationDiagram A).obj i)
        ⟨absoluteWeakNormalizationDiagram_obj_finitePresentation A i,
          absoluteWeakNormalizationDiagram_obj_universalHomeomorphism A i⟩ =
      colimit.ι (absoluteWeakNormalizationDiagram A) i := by
  classical
  let Q := absoluteWeakNormalizationObject A
  let e := equivSmallModel.{u} Q.FullSubcategory
  let D := absoluteWeakNormalizationDiagram A
  let c : Q.FullSubcategory := e.inverse.obj i
  let α : e.functor.obj c ⟶ i := e.counitIso.hom.app i
  let q : c.obj ⟶ D.obj (e.functor.obj c) :=
    (ObjectProperty.ι Q).map (e.unitIso.hom.app c)
  have htriangle : q ≫ D.map α = 𝟙 c.obj := by
    show (ObjectProperty.ι Q).map (e.unitIso.hom.app c ≫ e.inverse.map α) =
      (ObjectProperty.ι Q).map (𝟙 c)
    exact congrArg (ObjectProperty.ι Q).map (by simp [c, α])
  show q ≫ colimit.ι D (e.functor.obj c) = colimit.ι D i
  rw [← colimit.w D α, ← Category.assoc, htriangle, Category.id_comp]

/-- A finitely presented `A`-algebra which is a universal homeomorphism over `A` has exactly
one `A`-algebra map to the absolute weak normalization. -/
lemma stageToAbsoluteWeakNormalization_unique (C : CommAlgCat.{u} A)
    (hC : absoluteWeakNormalizationObject A C)
    (f : C ⟶ CommAlgCat.of A (AbsoluteWeakNormalization A)) :
    f = stageToAbsoluteWeakNormalization A C hC := by
  classical
  let D := absoluteWeakNormalizationDiagram A
  let e := commAlgCatEquivUnder (CommRingCat.of A)
  have hfp : IsFinitelyPresentable.{u} C :=
    (isCardinalPresentable_iff_of_isEquivalence (X := C) (κ := Cardinal.aleph0) e.functor).mp
      ((CommRingCat.isFinitelyPresentable_under_tfae (e.functor.obj C)).out 1 2 |>.mp
        (RingHom.finitePresentation_algebraMap.mpr hC.1))
  obtain ⟨i, p, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (colimit.isColimit D) f
  let hi : absoluteWeakNormalizationObject A (D.obj i) :=
    ⟨absoluteWeakNormalizationDiagram_obj_finitePresentation A i,
      absoluteWeakNormalizationDiagram_obj_universalHomeomorphism A i⟩
  calc
    f = p ≫ colimit.ι D i := hp.symm
    _ = p ≫ stageToAbsoluteWeakNormalization A (D.obj i) hi := by
      rw [stageToAbsoluteWeakNormalization_diagram]
    _ = stageToAbsoluteWeakNormalization A C hC :=
      stageToAbsoluteWeakNormalization_natural A hC hi p

/-! ### The candidate category and its terminal object -/

/-- The property of an `A`-algebra whose spectrum morphism to `Spec A` is a universal
homeomorphism. -/
def IsAbsoluteWeakNormalizationCandidate : ObjectProperty (CommAlgCat.{u} A) :=
  fun B => UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B)))

/-- The category of `A`-algebras whose spectrum morphism to `Spec A` is a universal
homeomorphism. -/
abbrev AbsoluteWeakNormalizationCategory :=
  (IsAbsoluteWeakNormalizationCandidate A).FullSubcategory

/-- The absolute weak normalization of `A`, as an object of the category of `A`-algebras whose
spectrum morphism to `Spec A` is a universal homeomorphism. -/
def absoluteWeakNormalizationCandidate : AbsoluteWeakNormalizationCategory A :=
  ⟨CommAlgCat.of A (AbsoluteWeakNormalization A),
    absoluteWeakNormalization_universalHomeomorphism A⟩

/-- **Stacks 0EUJ.** Every `A`-algebra which is a universal homeomorphism over `A` is a
filtered colimit of finitely presented such algebras. -/
lemma ind_absoluteWeakNormalizationObject (C : CommAlgCat.{u} A)
    (hC : IsAbsoluteWeakNormalizationCandidate A C) :
    ObjectProperty.ind.{u} (absoluteWeakNormalizationObject A) C := by
  let e := commAlgCatEquivUnder (CommRingCat.of A)
  obtain ⟨J, hSmall, hFilt, pres, hStages⟩ :=
    isFilteredColimit_finitePresentation_universalHomeomorphism (algebraMap A C) hC
  let _ : SmallCategory J := hSmall
  let _ : IsFiltered J := hFilt
  let U := Under.mk (CommRingCat.ofHom (algebraMap A C))
  have hIso : U ≅ e.functor.obj C := Under.isoMk (Iso.refl (CommRingCat.of C))
  let pres' := (pres.ofIso hIso).map e.inverse
  have hStage' : ∀ j, absoluteWeakNormalizationObject A (pres'.diag.obj j) := fun j => by
    let Xj := pres.diag.obj j
    let _ : Algebra A Xj.right := Xj.hom.hom.toAlgebra
    show Algebra.FinitePresentation A Xj.right ∧
      UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A Xj.right)).op)
    exact ⟨RingHom.finitePresentation_algebraMap.mp
      (show (algebraMap A Xj.right).FinitePresentation from (hStages j).1), (hStages j).2⟩
  exact ⟨J, hSmall, hFilt, pres'.ofIso (e.unitIso.app C).symm, hStage'⟩

/-- A filtered colimit presentation of an `A`-algebra by finitely presented `A`-algebras which
are universal homeomorphisms over `A`. -/
structure CandidatePresentation (C : CommAlgCat.{u} A) where
  /-- The indexing category of the presentation. -/
  J : Type u
  /-- Its category structure. -/
  instSmallCategory : SmallCategory J
  /-- The indexing category is filtered. -/
  instIsFiltered : IsFiltered J
  /-- The colimit presentation itself. -/
  pres : ColimitPresentation J C
  /-- Every stage is a finitely presented universal homeomorphism over `A`. -/
  stages : ∀ j, absoluteWeakNormalizationObject A (pres.diag.obj j)

/-- Every `A`-algebra which is a universal homeomorphism over `A` has such a presentation. -/
theorem nonempty_candidatePresentation (C : CommAlgCat.{u} A)
    (hC : IsAbsoluteWeakNormalizationCandidate A C) :
    Nonempty (CandidatePresentation A C) := by
  obtain ⟨J, hSmall, hFilt, pres, hStages⟩ := ind_absoluteWeakNormalizationObject A C hC
  exact ⟨⟨J, hSmall, hFilt, pres, hStages⟩⟩

/-- The canonical map from an `A`-algebra which is a universal homeomorphism over `A` to the
absolute weak normalization, descended from a filtered presentation by finitely presented
stages. -/
def candidateToAbsoluteWeakNormalization (C : CommAlgCat.{u} A)
    (hC : IsAbsoluteWeakNormalizationCandidate A C) :
    C ⟶ CommAlgCat.of A (AbsoluteWeakNormalization A) := by
  classical
  let p := Classical.choice (nonempty_candidatePresentation A C hC)
  let _ := p.instSmallCategory
  let _ := p.instIsFiltered
  exact p.pres.isColimit.desc
    { pt := CommAlgCat.of A (AbsoluteWeakNormalization A)
      ι :=
        { app := fun j => stageToAbsoluteWeakNormalization A (p.pres.diag.obj j) (p.stages j)
          naturality := fun {i j} _ =>
            stageToAbsoluteWeakNormalization_natural A (p.stages i) (p.stages j) _ } }

/-- The canonical map out of a candidate is the only `A`-algebra map to the absolute weak
normalization, so it does not depend on the presentation used to build it. -/
lemma candidateToAbsoluteWeakNormalization_unique (C : CommAlgCat.{u} A)
    (hC : IsAbsoluteWeakNormalizationCandidate A C)
    (f : C ⟶ CommAlgCat.of A (AbsoluteWeakNormalization A)) :
    f = candidateToAbsoluteWeakNormalization A C hC := by
  classical
  let p := Classical.choice (nonempty_candidatePresentation A C hC)
  let _ := p.instSmallCategory
  let _ := p.instIsFiltered
  refine p.pres.isColimit.hom_ext fun j => ?_
  rw [stageToAbsoluteWeakNormalization_unique A _ (p.stages j) (p.pres.ι.app j ≫ f)]
  dsimp only [candidateToAbsoluteWeakNormalization]
  rw [p.pres.isColimit.fac]

/-- **Stacks 0EUR.** The absolute weak normalization of `A` is terminal among the `A`-algebras
whose spectrum morphism to `Spec A` is a universal homeomorphism. -/
@[stacks 0EUR "awn_final"]
def absoluteWeakNormalizationCandidate_isTerminal :
    IsTerminal (absoluteWeakNormalizationCandidate A) :=
  IsTerminal.ofUniqueHom
    (fun Y => ObjectProperty.homMk (candidateToAbsoluteWeakNormalization A Y.obj Y.property))
    (fun Y f => ObjectProperty.hom_ext (IsAbsoluteWeakNormalizationCandidate A)
      (candidateToAbsoluteWeakNormalization_unique A Y.obj Y.property f.hom))

end Algebra

end
