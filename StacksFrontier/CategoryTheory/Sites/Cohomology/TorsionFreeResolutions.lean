module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Resolutions of abelian sheaves by sectionwise torsion-free ones

A cochain complex of abelian sheaves which is cohomologically bounded above admits a
quasi-isomorphism onto it from a complex whose terms are all sectionwise torsion-free.  This is
the input to every dévissage that reduces a statement about abelian sheaves to the torsion-free
case, and in particular to [Stacks, Tag 0D6J].

## Main results

* `CategoryTheory.exists_isTorsionFree_resolution_of_isLE`

## Implementation notes

The construction is not done here: it is
`CochainComplex.exists_quasiIso_prop` ([Stacks, Tag 05T7]), which resolves a complex termwise by
any object property whose objects admit epis onto everything.  All this file does is instantiate
it at sectionwise torsion-freeness, whose epi input is
`ModuleSheafCohomology.exists_isTorsionFree_epi` -- the free abelian group sheaf on the sections.
Closure under subobjects is needed for one thing only, and it is not the resolution: it supplies
the `ObjectProperty.ContainsZero` witness, via `0 ↪ G` for any torsion-free `G`.

**The universes are kept independent**: the site's object universe, its morphism universe and
the sheaf universe are three separate variables.  That is what makes the statement usable for
the small étale site -- that site is large and only essentially small, and its sheaves live at a
module universe above the site's.  A variant stated for a `SmallCategory` site with every
universe collapsed to one, such as
`Stacks.Cohomology.ForgetModule.exists_torsionFree_resolution_of_isLE`, cannot be instantiated
there; the statement here specialises to it.

## References

* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe w v u

namespace CategoryTheory

variable {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]

/-- **A cohomologically bounded-above complex of abelian sheaves is resolved by sectionwise
torsion-free ones.**  [Stacks, Tag 05T7] applied to sectionwise torsion-freeness. -/
theorem exists_isTorsionFree_resolution_of_isLE
    (K : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (n : ℤ) [K.IsLE n] :
    ∃ (G : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (q : G ⟶ K), QuasiIso q ∧
      (∀ i V, Module.IsTorsionFree ℤ ((G.X i).obj.obj V)) := by
  let P : ObjectProperty (Sheaf J AddCommGrpCat.{u}) := fun F =>
    ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V)
  have hP : ∀ F : Sheaf J AddCommGrpCat.{u},
      ∃ (G : Sheaf J AddCommGrpCat.{u}) (_ : P G) (q : G ⟶ F), Epi q := fun F =>
    (ModuleSheafCohomology.exists_isTorsionFree_epi J F).imp fun _ ⟨q, hG, hq⟩ => ⟨hG, q, hq⟩
  let : P.ContainsZero := by
    obtain ⟨G, -, hG, -⟩ := ModuleSheafCohomology.exists_isTorsionFree_epi J 0
    exact ⟨0, isZero_zero _, ModuleSheafCohomology.isTorsionFree_of_mono J (0 : 0 ⟶ G) hG⟩
  obtain ⟨G, q, hq, hG, -⟩ := (CochainComplex.exists_quasiIso_prop P hP n).2 K
  exact ⟨G, q, hq, hG⟩

end CategoryTheory

end
