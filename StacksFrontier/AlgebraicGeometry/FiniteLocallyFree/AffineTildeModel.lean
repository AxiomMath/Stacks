module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf

/-!
# Finite local freeness from affine models

A sheaf of modules on a scheme which, near every point, is the sheaf `H̃` attached on an affine
open `V` to a finite projective `Γ(X, V)`-module `H` is finite locally free.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_forall_tilde_model`: a sheaf of
  modules locally of the form `H̃` with `H` finite projective is finite locally free.

## References

* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Finite local freeness from affine models.**  If every point of `X` has an affine open
neighbourhood `V` over which `F` is the sheaf `H̃` attached to a finite projective
`Γ(X, V)`-module `H`, transported along `V ≅ Spec Γ(X, V)`, then `F` is finite locally free:
`H̃` is finite locally free on `Spec Γ(X, V)` (Stacks tag 05JM), finite local freeness restricts
along the isomorphism `V ≅ Spec Γ(X, V)`, and it glues along the cover of `X` by the `V`. -/
theorem isFiniteLocallyFree_of_forall_tilde_model {X : Scheme.{u}} (F : X.Modules)
    (h : ∀ x : X, ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : x ∈ V) (H : ModuleCat.{u} Γ(X, V)),
      Module.Finite Γ(X, V) H ∧ Module.Projective Γ(X, V) H ∧
        Nonempty ((restrictFunctor V.ι).obj F ≅
          (tilde.functor Γ(X, V) ⋙ restrictFunctor hV.isoSpec.hom).obj H)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F := by
  choose V hV hxV H hfin hproj e using h
  refine (Scheme.Modules.isFiniteLocallyFree_iff F).1 ?_
  refine isFiniteLocallyFree_of_iSup_eq_top V
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩) fun x ↦ ?_
  have _ := hfin x
  have _ := hproj x
  have hloc : Module.IsFiniteLocallyFree Γ(X, V x) (H x) :=
    (Module.isFiniteLocallyFree_iff_finite_projective _ _).2 ⟨hfin x, hproj x⟩
  have ht : IsFiniteLocallyFree
      (AlgebraicGeometry.tilde (R := CommRingCat.of Γ(X, V x)) (ModuleCat.of Γ(X, V x) (H x))) :=
    (tilde_isFiniteLocallyFree_iff Γ(X, V x) (H x)).2 hloc
  exact IsFiniteLocallyFree.of_iso (e x).some.symm (ht.restrict (hV x).isoSpec.hom)

end AlgebraicGeometry.Scheme.Modules

end
