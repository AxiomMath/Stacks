module

public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.Devissage
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Additive

/-!
# The Eilenberg–Watts comparison at a free module

Let `R` be a commutative ring and `F : ModuleCat R ⥤ ModuleCat R` an `R`-linear functor. The
comparison map `Stacks.EilenbergWatts.wattsMap F M : F(R) ⊗[R] M ⟶ F(M)` is an isomorphism at
`M = R`, hence at every free module with a basis indexed by a type whose direct sums `F` preserves.

Unlike `Stacks.EilenbergWatts.isIso_wattsMap`, this needs no right exactness of `F` and no
preservation of colimits beyond the direct sums actually indexed by the bases in play.

## Main results

* `Stacks.EilenbergWatts.isIso_wattsMap_of_basis`: the comparison map is an isomorphism at a
  module with a basis indexed by a type whose direct sums `F` preserves.
* `Stacks.EilenbergWatts.wattsComplexIso`: for a complex of free modules the comparison maps
  assemble into an isomorphism of complexes `F(R) ⊗[R] P^• ≅ F(P^•)`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.EilenbergWatts

/-- A natural transformation invertible at an object is invertible at every isomorphic object. -/
theorem isIso_app_of_iso {C D : Type*} [Category C] [Category D] {G H : C ⥤ D}
    (α : G ⟶ H) {X Y : C} (e : X ≅ Y) (h : IsIso (α.app Y)) : IsIso (α.app X) := by
  have key : α.app X = G.map e.hom ≫ α.app Y ≫ H.map e.inv := by simp
  rw [key]
  infer_instance

variable {R : Type u} [CommRing R] (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
  [F.Additive] [F.Linear R]

/-- **The Eilenberg–Watts comparison map is an isomorphism at `R^{(J)}`**, for an index type `J`
whose direct sums `F` preserves. -/
theorem isIso_wattsMap_finsupp (J : Type u) (hF : PreservesColimitsOfShape (Discrete J) F) :
    IsIso (wattsMap F (ModuleCat.of R (J →₀ R))) :=
  have := hF
  isIso_app_of_isColimit (wattsNatTrans F) (ModuleCat.finsuppCoconeIsColimit R R J) fun j => by
    obtain ⟨_⟩ := j
    exact isIso_wattsMap_unit F

/-- **The Eilenberg–Watts comparison map is an isomorphism at a free module** with a basis indexed
by a type whose direct sums `F` preserves. -/
theorem isIso_wattsMap_of_basis {J : Type u} (N : ModuleCat.{u} R) (b : Module.Basis J R N)
    (hF : PreservesColimitsOfShape (Discrete J) F) :
    IsIso (wattsMap F N) :=
  isIso_app_of_iso (wattsNatTrans F)
    (b.repr.toModuleIso : N ≅ ModuleCat.of R (J →₀ R)) (isIso_wattsMap_finsupp F J hF)

/-- **For a complex of free modules the Eilenberg–Watts comparison is an isomorphism of
complexes** `F(R) ⊗[R] P^• ≅ F(P^•)`, given in each degree by the comparison map. -/
def wattsComplexIso (P : CochainComplex (ModuleCat.{u} R) ℤ) {J : ℤ → Type u}
    (b : ∀ i, Module.Basis (J i) R (P.X i))
    (hF : ∀ i : ℤ, PreservesColimitsOfShape (Discrete (J i)) F) :
    ((tensorLeft (F.obj (ModuleCat.of R R))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => @asIso _ _ _ _ (wattsMap F (P.X i)) (isIso_wattsMap_of_basis F _ (b i) (hF i)))
    fun i j _ => by simpa using ((wattsNatTrans F).naturality (P.d i j)).symm

end Stacks.EilenbergWatts

end
