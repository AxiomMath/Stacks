module

public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes

/-!
# Exact functors preserve cellular complexes

Let `P` be a class of objects of an abelian category `A`. A cochain complex is `P`-cellular when
it is the colimit of a ladder of bounded above complexes with terms in `P`, each a resolution of
the corresponding canonical truncation (Stacks 0794, Stacks 06XX); these are the complexes by
which the left derived functors of Stacks 0794 are computed.

An exact functor `G : A ⥤ B` commuting with colimits indexed by `ℕ` carries such a presentation to
one of the same kind: it carries the ladder to a ladder, the colimit to a colimit, bounded above
complexes to bounded above complexes and quasi-isomorphisms in a degree to quasi-isomorphisms in
that degree. So `G` carries `P`-cellular complexes to `P'`-cellular complexes for any class `P'`
containing the image of `P`.

## Main results

* `StacksDraft.UnboundedLeftDerivedFunctor.IsPCellular.map`: an exact functor commuting with
  `ℕ`-indexed colimits carries `P`-cellular complexes to `P'`-cellular complexes.

## References

* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.UnboundedLeftDerivedFunctor

variable {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B] [Abelian B]

/-- For a functor `G`, the image under `G` of the system `Functor.ofSequence g` is the system of
the images `Functor.ofSequence (G g)`. -/
def ofSequenceMapIso (G : A ⥤ B) {X : ℕ → A} (g : ∀ n, X n ⟶ X (n + 1)) :
    Functor.ofSequence (fun n => G.map (g n)) ≅ Functor.ofSequence g ⋙ G :=
  let hom : Functor.ofSequence (fun n => G.map (g n)) ⟶ Functor.ofSequence g ⋙ G :=
    NatTrans.ofSequence (fun n => 𝟙 _) (fun n => by
      simp only [Functor.ofSequence_map_homOfLE_succ, Functor.comp_map]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have : IsIso hom := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    exact ⟨⟨𝟙 _, Category.comp_id _, Category.comp_id _⟩⟩
  asIso hom

omit [Abelian A] [Abelian B] in
/-- Each component of `(ofSequenceMapIso G g).hom` is the identity. -/
@[simp]
lemma ofSequenceMapIso_hom_app (G : A ⥤ B) {X : ℕ → A} (g : ∀ n, X n ⟶ X (n + 1)) (n : ℕ) :
    (ofSequenceMapIso G g).hom.app n = 𝟙 _ :=
  rfl

/-- **An exact functor commuting with `ℕ`-indexed colimits carries `P`-cellular complexes to
`P'`-cellular complexes**, whenever it carries the objects satisfying `P` to objects satisfying
`P'`. -/
theorem IsPCellular.map (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [HasColimitsOfShape ℕ A] [PreservesColimitsOfShape ℕ G]
    {P : ObjectProperty A} {P' : ObjectProperty B} (hPP' : ∀ X, P X → P' (G.obj X))
    {S : CochainComplex A ℤ} (hS : IsPCellular P S) :
    IsPCellular P' ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj S) := by
  obtain ⟨Q, g, c, hc, e, hle, hQ, hstage⟩ := hS
  let GH := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let iso := ofSequenceMapIso GH g
  let c' : Cocone (Functor.ofSequence (fun n => GH.map (g n))) :=
    (Cocone.precompose iso.hom).obj (GH.mapCocone c)
  have hc' : IsColimit c' :=
    (IsColimit.precomposeHomEquiv iso (GH.mapCocone c)).symm (isColimitOfPreserves GH hc)
  refine ⟨fun n => GH.obj (Q n), fun n => GH.map (g n), c', hc', GH.mapIso e,
    fun n => ?_, fun n i => hPP' _ (hQ n i), fun n i hi => ?_⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact G.map_isZero ((Q n).isZero_of_isStrictlyLE n i hi)
  · have := hstage n i hi
    have h : c'.ι.app n ≫ (GH.mapIso e).hom = GH.map (c.ι.app n ≫ e.hom) :=
      (congrArg (· ≫ GH.map e.hom) (Category.id_comp (GH.map (c.ι.app n)))).trans
        (GH.map_comp _ _).symm
    rw [h]
    exact HomologicalComplex.quasiIsoAt_map_of_preservesHomology _ G i

end StacksDraft.UnboundedLeftDerivedFunctor

end
