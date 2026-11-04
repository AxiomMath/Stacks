module

public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedSupport

/-!
# Vanishing and weakly associated points on an algebraic space

Let `X` be an algebraic space over `S` and `F` an `𝒪_X`-module. If `F` is the zero module then
it has no weakly associated points: every section of `F` vanishes, hence every geometric stalk
of the abelian sheaf underlying `F` is zero, so the support of that sheaf is empty, and the
weakly associated points lie in the support.

## Main results

* `AlgebraicGeometry.Space.weaklyAssociatedPoints_eq_empty_of_isZero`: a zero `𝒪_X`-module has
  no weakly associated points.

## Implementation notes

The statement is proved for an arbitrary `𝒪_X`-module rather than only for a quasi-coherent
one, since quasi-coherence plays no role in this direction. The converse — that an
`𝒪_X`-module with no weakly associated points vanishes — is genuinely a statement about
quasi-coherent modules and is not proved here.

Emptiness of the geometric stalks uses that the small étale neighbourhoods of a geometric
point are cofiltered, by `AlgebraicGeometry.Space.isCofiltered_smallEtaleNeighborhood`: the
set-valued stalk is a quotient of the disjoint union of the sections over all neighbourhoods,
so two germs are compared on a common refinement.

## References

* [Stacks Project, Tag 0CU0](https://stacks.math.columbia.edu/tag/0CU0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

/-- The sections of a zero `𝒪_X`-module over any étale chart form a subsingleton. -/
theorem subsingleton_sections_of_isZero
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) {F : Modules.{u, m} B S hS X.1 X.2} (hF : IsZero F)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) : Subsingleton (F.val.obj U) :=
  AddCommGrpCat.subsingleton_of_isZero
    (Functor.map_isZero ((evaluation _ _).obj U)
      (Functor.map_isZero (PresheafOfModules.toPresheaf.{m} _)
        (Functor.map_isZero (SheafOfModules.forget _) hF)))

/-- The support of the abelian sheaf underlying a zero `𝒪_X`-module is empty. -/
private theorem supportOfSheaf_eq_empty_of_isZero
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) {F : Modules.{u, m} B S hS X.1 X.2} (hF : IsZero F) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨p, -, hp⟩ := (mem_supportOfSheaf_iff_exists B S hS X.1 _ x).mp hx
  have := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 p
  set D := SmallEtaleNeighborhood.sections (x := p)
    (((SheafOfModules.toSheaf _).obj F).obj ⋙ forget AddCommGrpCat.{m})
  refine hp ⟨fun a b => ?_⟩
  obtain ⟨N, σ, rfl⟩ := D.ιColimitType_jointly_surjective a
  obtain ⟨M, τ, rfl⟩ := D.ιColimitType_jointly_surjective b
  obtain ⟨L, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs N M
  exact (D.ιColimitType_eq_iff_of_isFiltered _ _).mpr ⟨L, f, g,
    (subsingleton_sections_of_isZero B S hS X hF (Opposite.op L.unop.chart)).elim _ _⟩

/-- **Stacks 0CU0**, the direction that a vanishing module has no weakly associated points: a
zero `𝒪_X`-module on an algebraic space has empty set of weakly associated points. -/
@[stacks 0CU0 "a zero module has no weakly associated points"]
theorem weaklyAssociatedPoints_eq_empty_of_isZero
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (F : Modules.{u, m} B S hS X.1 X.2) (hF : IsZero F) :
    weaklyAssociatedPoints B S hS X F = ∅ :=
  Set.eq_empty_of_subset_empty (supportOfSheaf_eq_empty_of_isZero B S hS X hF ▸
    weaklyAssociatedPoints_subset_supportOfSheaf B S hS X F)

end AlgebraicGeometry.Space

end
