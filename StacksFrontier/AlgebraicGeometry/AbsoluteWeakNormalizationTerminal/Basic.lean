module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationIndex.Basic
public import StacksFrontier.AlgebraicGeometry.IndPresentation.Ind

/-!
# The universal property of absolute weak normalization

Let `A` be a commutative ring.  Among `A`-algebras whose maps on spectra are universal
homeomorphisms, the absolute weak normalization of `A` is a final object.

## Main definitions

* `AlgebraicGeometry.IsAbsoluteWeakNormalizationCandidate` is the property cutting out the
  `A`-algebras in question.
* `AlgebraicGeometry.AbsoluteWeakNormalizationCategory` is the category they form.
* `AlgebraicGeometry.absoluteWeakNormalizationCategoryObject` is the absolute weak
  normalization, regarded as an object of that category.

## Main results

* `AlgebraicGeometry.absoluteWeakNormalizationCategoryObject_isTerminal`: it is terminal
  there.

## Implementation notes

The absolute weak normalization is the colimit of the finitely presented such algebras, and
every such algebra is a filtered colimit of finitely presented ones (Tag 0EUJ,
`AlgebraicGeometry.isFilteredColimit_finitePresentation_universalHomeomorphism`).

The condition defining `AlgebraicGeometry.AbsoluteWeakNormalizationCategory` is
`AlgebraicGeometry.IsAbsoluteWeakNormalizationCandidate`, which asks only that the map on
spectra be a universal homeomorphism; finite presentation is *not* imposed, which is why its
terminal object is the colimit rather than one of the stages.  The stages themselves are
`Algebra.absoluteWeakNormalizationObject`, and the fact that the colimit is itself a candidate is
`AlgebraicGeometry.absoluteWeakNormalization_universalHomeomorphism`.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tag 0EUR is used: `A` is an arbitrary commutative ring, with no
Noetherian or reducedness assumption.

## What is not done

Nothing here characterizes *when* the canonical map out of a candidate is an isomorphism; that
is Tag 0EUR's `awn_characterization` label, and it needs the special-element criterion of Tag
0CNC in addition.  Nothing here is about schemes other than spectra of rings, so the initiality
of `AlgebraicGeometry.UniversalHomeomorphismOver X` for a general scheme `X` (Tag 0EUS) is still
unproved after this file.

## References

* [Stacks Project, Tag 0EUJ](https://stacks.math.columbia.edu/tag/0EUJ)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Cardinal
attribute [local instance] Cardinal.fact_isRegular_aleph0

universe u

namespace AlgebraicGeometry


/-- The map from a finitely presented candidate algebra to the defining colimit, using a
representative in its small index category. -/
noncomputable def awnStageMap (A : Type u) [CommRing A]
    (C : CommAlgCat.{u} A) (hC : Algebra.absoluteWeakNormalizationObject A C) :
    C ⟶ CommAlgCat.of A
      (Algebra.AbsoluteWeakNormalization A) := by
  let e := equivSmallModel.{u} (Algebra.absoluteWeakNormalizationObject A).FullSubcategory
  let c : (Algebra.absoluteWeakNormalizationObject A).FullSubcategory := ⟨C, hC⟩
  exact (ObjectProperty.ι (Algebra.absoluteWeakNormalizationObject A)).map (e.unitIso.app c).hom ≫
    colimit.ι (Algebra.absoluteWeakNormalizationDiagram A)
      (e.functor.obj c)

/-- The representative maps commute with morphisms between candidate algebras. -/
lemma awnStageMap_natural (A : Type u) [CommRing A]
    {C E : CommAlgCat.{u} A} (hC : Algebra.absoluteWeakNormalizationObject A C)
    (hE : Algebra.absoluteWeakNormalizationObject A E)
    (f : C ⟶ E) :
    f ≫ awnStageMap A E hE = awnStageMap A C hC := by
  let Q := Algebra.absoluteWeakNormalizationObject A
  let e := equivSmallModel.{u} Q.FullSubcategory
  let c : Q.FullSubcategory := ⟨C, hC⟩
  let d : Q.FullSubcategory := ⟨E, hE⟩
  let f' : c ⟶ d := ObjectProperty.homMk f
  let D := Algebra.absoluteWeakNormalizationDiagram A
  have hn := congrArg (ObjectProperty.ι Q).map (e.unitIso.hom.naturality f')
  change f'.hom ≫ (ObjectProperty.ι Q).map (e.unitIso.hom.app d) =
      (ObjectProperty.ι Q).map (e.unitIso.hom.app c) ≫ D.map (e.functor.map f') at hn
  change f'.hom ≫ ((ObjectProperty.ι Q).map (e.unitIso.hom.app d) ≫
    colimit.ι D (e.functor.obj d)) = (ObjectProperty.ι Q).map
      (e.unitIso.hom.app c) ≫ colimit.ι D (e.functor.obj c)
  rw [← Category.assoc, hn, Category.assoc, colimit.w]

/-- On an object already in the defining diagram, the representative map is its colimit leg. -/
lemma awnStageMap_diagram_ι (A : Type u) [CommRing A]
    (i : Algebra.AbsoluteWeakNormalizationIndex A) :
    awnStageMap A
        ((Algebra.absoluteWeakNormalizationDiagram A).obj i)
        ⟨Algebra.absoluteWeakNormalizationDiagram_obj_finitePresentation A i,
          Algebra.absoluteWeakNormalizationDiagram_obj_universalHomeomorphism A i⟩ =
      colimit.ι (Algebra.absoluteWeakNormalizationDiagram A) i := by
  let Q := Algebra.absoluteWeakNormalizationObject A
  let e := equivSmallModel.{u} Q.FullSubcategory
  let D := Algebra.absoluteWeakNormalizationDiagram A
  let c : Q.FullSubcategory := e.inverse.obj i
  let α : e.functor.obj c ⟶ i := e.counitIso.hom.app i
  let q : c.obj ⟶ D.obj (e.functor.obj c) :=
    (ObjectProperty.ι Q).map (e.unitIso.hom.app c)
  have htriangle : q ≫ D.map α = 𝟙 c.obj :=
    congrArg (ObjectProperty.ι Q).map
      (by simp [c, α] : e.unitIso.hom.app c ≫ e.inverse.map α = 𝟙 c)
  calc
    awnStageMap A (D.obj i) c.property = q ≫ colimit.ι D (e.functor.obj c) := rfl
    _ = q ≫ D.map α ≫ colimit.ι D i := by
      simpa only [Category.assoc] using congrArg (fun z => q ≫ z) (colimit.w D α).symm
    _ = 𝟙 c.obj ≫ colimit.ι D i := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ colimit.ι D i) htriangle
    _ = colimit.ι D i := by simp

/-- Every `A`-algebra map from a finitely presented candidate to the colimit is canonical. -/
lemma awnStageMap_unique (A : Type u) [CommRing A]
    (C : CommAlgCat.{u} A) (hC : Algebra.absoluteWeakNormalizationObject A C)
    (f : C ⟶ CommAlgCat.of A
      (Algebra.AbsoluteWeakNormalization A)) :
    f = awnStageMap A C hC := by
  let D := Algebra.absoluteWeakNormalizationDiagram A
  let e := commAlgCatEquivUnder (CommRingCat.of A)
  have hfp : IsFinitelyPresentable.{u} C := by
    have hfp' : IsFinitelyPresentable.{u} (e.functor.obj C) :=
      ((CommRingCat.isFinitelyPresentable_under_tfae (e.functor.obj C)).out 1 2).mp
        (RingHom.finitePresentation_algebraMap.mpr hC.1)
    simpa only [IsFinitelyPresentable] using
      (isCardinalPresentable_iff_of_isEquivalence (X := C) (κ := Cardinal.aleph0) e.functor).mp hfp'
  obtain ⟨i, p, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (colimit.isColimit D) f
  calc
    f = p ≫ colimit.ι D i := hp.symm
    _ = p ≫ awnStageMap A (D.obj i)
        ⟨Algebra.absoluteWeakNormalizationDiagram_obj_finitePresentation A i,
          Algebra.absoluteWeakNormalizationDiagram_obj_universalHomeomorphism A i⟩ := by
      rw [awnStageMap_diagram_ι]
    _ = awnStageMap A C hC := awnStageMap_natural A hC
      ⟨Algebra.absoluteWeakNormalizationDiagram_obj_finitePresentation A i,
        Algebra.absoluteWeakNormalizationDiagram_obj_universalHomeomorphism A i⟩ p

/-- The property of an `A`-algebra whose map on spectra is a universal homeomorphism. -/
public def IsAbsoluteWeakNormalizationCandidate (A : Type u) [CommRing A] :
    ObjectProperty (CommAlgCat.{u} A) :=
  fun B => UniversalHomeomorphism
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)

/-- The category of ring maps `A → B` which give universal homeomorphisms on spectra. -/
public abbrev AbsoluteWeakNormalizationCategory (A : Type u) [CommRing A] :=
  (IsAbsoluteWeakNormalizationCandidate A).FullSubcategory

/-- The absolute weak normalization, regarded as an object of the category of `A`-algebras
whose maps on spectra are universal homeomorphisms. -/
public noncomputable def absoluteWeakNormalizationCategoryObject (A : Type u) [CommRing A] :
    AbsoluteWeakNormalizationCategory A :=
  ⟨CommAlgCat.of A
      (Algebra.AbsoluteWeakNormalization A),
    absoluteWeakNormalization_universalHomeomorphism A⟩

/-- A candidate algebra is a filtered colimit of finitely presented candidate algebras. -/
lemma awnCandidate_ind (A : Type u) [CommRing A]
    (C : CommAlgCat.{u} A)
    (hC : IsAbsoluteWeakNormalizationCandidate A C) :
    ObjectProperty.ind.{u} (Algebra.absoluteWeakNormalizationObject A) C := by
  let e := commAlgCatEquivUnder (CommRingCat.of A)
  obtain ⟨J, hSmall, hFilt, pres, hStages⟩ :=
    isFilteredColimit_finitePresentation_universalHomeomorphism (algebraMap A C) hC
  let : SmallCategory J := hSmall
  let : IsFiltered J := hFilt
  let U := Under.mk (CommRingCat.ofHom (algebraMap A C))
  have hIso : U ≅ e.functor.obj C := Under.isoMk (Iso.refl (CommRingCat.of C))
  let pres' := (pres.ofIso hIso).map e.inverse
  have hUnit : C ≅ e.inverse.obj (e.functor.obj C) := e.unitIso.app C
  have hStage' : ∀ j, Algebra.absoluteWeakNormalizationObject A (pres'.diag.obj j) := by
    intro j
    let Xj := pres.diag.obj j
    let : Algebra A Xj.right := Xj.hom.hom.toAlgebra
    change Algebra.FinitePresentation A Xj.right ∧
      UniversalHomeomorphism
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A Xj.right)).op)
    exact ⟨RingHom.finitePresentation_algebraMap.mp (hStages j).1, (hStages j).2⟩
  exact ⟨J, hSmall, hFilt, pres'.ofIso hUnit.symm, hStage'⟩

/-- A filtered colimit presentation of an algebra by finitely presented universal
homeomorphisms over the base. -/
private structure AwnCandidatePresentation (A : Type u) [CommRing A]
    (C : CommAlgCat.{u} A) where
  J : Type u
  instSmallCategory : SmallCategory J
  instIsFiltered : IsFiltered J
  pres : ColimitPresentation J C
  stages : ∀ j, Algebra.absoluteWeakNormalizationObject A (pres.diag.obj j)

attribute [-simp] AwnCandidatePresentation.mk.injEq AwnCandidatePresentation.mk.sizeOf_spec

/-- Every universal-homeomorphism algebra has such a filtered presentation. -/
private theorem existsAwnCandidatePresentation (A : Type u) [CommRing A]
    (C : CommAlgCat.{u} A)
    (hC : IsAbsoluteWeakNormalizationCandidate A C) :
    Nonempty (AwnCandidatePresentation A C) := by
  rcases awnCandidate_ind A C hC with ⟨J, hSmall, hFilt, pres, hStages⟩
  exact ⟨⟨J, hSmall, hFilt, pres, hStages⟩⟩

/-- The cocone over a diagram of finitely presented candidates given by the stage maps. -/
private noncomputable def awnStageCocone (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]
    (D : J ⥤ CommAlgCat.{u} A) (hD : ∀ j, Algebra.absoluteWeakNormalizationObject A (D.obj j)) :
    Cocone D where
  pt := CommAlgCat.of A (Algebra.AbsoluteWeakNormalization A)
  ι :=
    { app := fun j => awnStageMap A (D.obj j) (hD j)
      naturality := fun {i j} f => awnStageMap_natural A (hD i) (hD j) (D.map f) }

/-- The canonical map from a universal-homeomorphism algebra to the absolute weak
normalization, obtained from its filtered presentation. -/
private noncomputable def awnCandidateMap (A : Type u) [CommRing A]
    (C : CommAlgCat.{u} A)
    (hC : IsAbsoluteWeakNormalizationCandidate A C) :
    C ⟶ CommAlgCat.of A
      (Algebra.AbsoluteWeakNormalization A) := by
  classical
  let p := Classical.choice (existsAwnCandidatePresentation A C hC)
  let := p.instSmallCategory
  exact p.pres.isColimit.desc (awnStageCocone A p.pres.diag p.stages)

/-- The map constructed from a candidate presentation is independent of every choice. -/
private lemma awnCandidateMap_unique (A : Type u) [CommRing A]
    (C : CommAlgCat.{u} A)
    (hC : IsAbsoluteWeakNormalizationCandidate A C)
    (f : C ⟶ CommAlgCat.of A
      (Algebra.AbsoluteWeakNormalization A)) :
    f = awnCandidateMap A C hC := by
  classical
  let p := Classical.choice (existsAwnCandidatePresentation A C hC)
  let := p.instSmallCategory
  change f = p.pres.isColimit.desc (awnStageCocone A p.pres.diag p.stages)
  refine p.pres.isColimit.hom_ext fun j => ?_
  exact (awnStageMap_unique A (p.pres.diag.obj j) (p.stages j) (p.pres.ι.app j ≫ f)).trans
    (p.pres.isColimit.fac (awnStageCocone A p.pres.diag p.stages) j).symm



end AlgebraicGeometry

end

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The absolute weak normalization of `A` is final among `A`-algebras which give universal
homeomorphisms on spectra. -/
@[stacks 0EUR "awn_final"]
public noncomputable def absoluteWeakNormalizationCategoryObject_isTerminal
    (A : Type u) [CommRing A] :
    IsTerminal (absoluteWeakNormalizationCategoryObject A) :=
  IsTerminal.ofUniqueHom
    (fun Y => ObjectProperty.homMk (awnCandidateMap A Y.obj Y.property))
    (fun Y f => ObjectProperty.hom_ext (IsAbsoluteWeakNormalizationCandidate A)
      (awnCandidateMap_unique A Y.obj Y.property f.hom))

end AlgebraicGeometry

end
