module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSystemGluing
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialPseudoFamilyPair

/-!
# The pair of the module glued from the cartesian system of a pair

Let `X` be a simplicial scheme and `(F, α)` a pair of the family of modules on the degrees of
`X`. The module on the total Zariski site glued from the cartesian system of `(F, α)` is
cartesian, and its pair is `(F, α)`: its component in degree zero is identified with `F`, and the
comparison of its two transitions to degree one is carried to `α`. This is the essential
surjectivity in Stacks 07TH for the total Zariski site.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.systemModulePairIso`: the identification of the pair of the
  glued module with the pair.

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {X : SimplicialObject Scheme.{u}}

/-- The cartesian system of the module glued from a cartesian system is identified with it,
compatibly with the transitions. -/
theorem cartesianModuleSystem_trans_systemModule (N : (zariskiModuleFamily X).CartesianSystem)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((cartesianModuleSystem X (systemModule N) (isCartesianModule_systemModule N)).trans φ).hom ≫
        (systemModuleComponentIso N n).hom =
      ((zariskiModuleFamily X).map φ).map (systemModuleComponentIso N m).hom ≫ (N.trans φ).hom := by
  show componentModuleTransition X φ.op (systemModule N) ≫ _ = _
  rw [componentModuleTransition_systemModule, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The cartesian system of the module glued from the cartesian system of a pair. -/
noncomputable def pairGluedSystem (A : (zariskiModuleFamily X).Pair) :
    (zariskiModuleFamily X).CartesianSystem :=
  cartesianModuleSystem X (systemModule ((zariskiModuleFamily X).pairSystem A.obj A.iso A.cocycle))
    (isCartesianModule_systemModule _)

/-- The identification of the objects of `pairGluedSystem A` with those of the cartesian system of
`A`. -/
noncomputable def pairGluedIso (A : (zariskiModuleFamily X).Pair) (n : SimplexCategory) :
    (pairGluedSystem A).obj n ≅ ((zariskiModuleFamily X).pairSystem A.obj A.iso A.cocycle).obj n :=
  systemModuleComponentIso _ n

/-- The identification `pairGluedIso` is compatible with the transitions. -/
theorem pairGluedIso_trans (A : (zariskiModuleFamily X).Pair) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    ((pairGluedSystem A).trans φ).hom ≫ (pairGluedIso A n).hom =
      ((zariskiModuleFamily X).map φ).map (pairGluedIso A m).hom ≫
        (((zariskiModuleFamily X).pairSystem A.obj A.iso A.cocycle).trans φ).hom :=
  cartesianModuleSystem_trans_systemModule _ φ

/-- The identification of the object in degree zero of `pairGluedSystem A` with that of `A`. -/
noncomputable def pairGluedZeroIso (A : (zariskiModuleFamily X).Pair) :
    (pairGluedSystem A).obj ⦋0⦌ ≅ A.obj :=
  pairGluedIso A ⦋0⦌ ≪≫ (zariskiModuleFamily X).pairZeroIso A.obj

/-- The identification in degree zero is compatible with the comparison isomorphisms. -/
theorem pairGlued_comm (A : (zariskiModuleFamily X).Pair) :
    (zariskiModuleFamily X).ToPairComm A (pairGluedSystem A) (pairGluedZeroIso A).hom :=
  (zariskiModuleFamily X).toPairComm_of_iso_pairSystem A (pairGluedSystem A)
    (pairGluedIso A) (pairGluedIso_trans A)

/-- The pair of the cartesian module glued from the cartesian system of a pair is that pair. -/
noncomputable def systemModulePairIso (A : (zariskiModuleFamily X).Pair) :
    (pairGluedSystem A).toPair ≅ A :=
  (zariskiModuleFamily X).toPairIsoMk A (pairGluedSystem A) (pairGluedZeroIso A) (pairGlued_comm A)

end AlgebraicGeometry.SimplicialScheme

end
