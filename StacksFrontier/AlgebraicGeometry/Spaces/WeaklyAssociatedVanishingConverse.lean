module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishing

/-!
# A module on an algebraic space with empty support vanishes

Let `X` be an algebraic space over `S` and `F` an `𝒪_X`-module. The support of the abelian
sheaf underlying `F` is empty exactly when `F` is the zero module: a section whose germ vanishes
at every geometric point of a chart vanishes on a covering of that chart, because the geometric
points are a conservative family of points of the small étale site.

Together with the inclusion `WeakAss(F) ⊆ Supp(F)` of Stacks 0CTY this is one half of each of
the two statements of Stacks 0CU0, and it reduces the remaining half — that a quasi-coherent
module with no weakly associated point vanishes — to the assertion that a nonempty support
contains a weakly associated point.

## Main results

* `AlgebraicGeometry.Space.isZero_of_supportOfSheaf_eq_empty`: an `𝒪_X`-module whose underlying
  abelian sheaf has empty support is zero.
* `AlgebraicGeometry.Space.supportOfSheaf_eq_empty_iff_isZero`: the support of the abelian sheaf
  underlying an `𝒪_X`-module is empty exactly when the module is zero.

## Implementation notes

Both statements hold for an arbitrary `𝒪_X`-module, with its sections in a universe independent
of that of the schemes; quasi-coherence is not used.

Vanishing is read off the set-valued stalks rather than the module stalks: the zero endomorphism
of the underlying sheaf of sets is injective on every stalk, hence injective on sections by
Stacks 04K5, and an injective zero map forces every section to vanish.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 0CTY](https://stacks.math.columbia.edu/tag/0CTY)
* [Stacks Project, Tag 0CU0](https://stacks.math.columbia.edu/tag/0CU0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

/-- An `𝒪_X`-module all of whose set-valued geometric stalks are subsingletons is zero: the zero
endomorphism of the underlying sheaf of sets is then injective on stalks, hence on sections. -/
theorem isZero_of_stalkSet_subsingleton (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS) (F : Modules.{u, m} B S hS X.1 X.2)
    (hstalk : ∀ x : GeometricPoint B S hS X.1,
      Subsingleton (stalkSet x (F.val.presheaf ⋙ forget AddCommGrpCat.{m}))) :
    IsZero F := by
  let J := SmallEtale.topology B S hS X.1
  let G : Sheaf J (Type m) :=
    (sheafCompose J (forget AddCommGrpCat.{m})).obj ((SheafOfModules.toSheaf.{m} _).obj F)
  let a : G ⟶ G :=
    (sheafCompose J (forget AddCommGrpCat.{m})).map
      ((SheafOfModules.toSheaf.{m} _).map (0 : F ⟶ F))
  have ha := (injective_iff_stalkSetMap_injective B S hS X.1 X.2 a).mpr
    fun x => @Function.injective_of_subsingleton _ _ (hstalk x) _
  refine (IsZero.iff_id_eq_zero F).mpr ?_
  ext U s
  exact ha U.unop (by change (0 : F.val.obj U) = 0; rfl)

/-- An `𝒪_X`-module on an algebraic space whose underlying abelian sheaf has empty support is
the zero module. -/
theorem isZero_of_supportOfSheaf_eq_empty (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS) (F : Modules.{u, m} B S hS X.1 X.2)
    (h : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) = ∅) :
    IsZero F := by
  refine isZero_of_stalkSet_subsingleton B S hS X F fun p => ?_
  by_contra hp
  exact Set.eq_empty_iff_forall_notMem.mp h p.image ⟨p, rfl, hp⟩

/-- The support of the abelian sheaf underlying an `𝒪_X`-module on an algebraic space is empty
exactly when the module is zero. -/
theorem supportOfSheaf_eq_empty_iff_isZero (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicSpaces B S hS) (F : Modules.{u, m} B S hS X.1 X.2) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) = ∅ ↔ IsZero F := by
  refine ⟨isZero_of_supportOfSheaf_eq_empty B S hS X F, fun hF => ?_⟩
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

end AlgebraicGeometry.Space

end
