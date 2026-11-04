module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatTensorShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# A retract of a flat sheaf of modules is flat

Let `(C, O)` be a ringed site and let `M` be a retract of a sheaf of `O`-modules `N`, that is,
let there be morphisms `i : M ⟶ N` and `r : N ⟶ M` with `i ≫ r = 𝟙 M`. If `N` is flat then so
is `M`.

This is the direct-summand companion of the two-out-of-three statements of Stacks 03EY: there a
term of a short exact sequence is flat because the two others are, here a direct summand is flat
because the ambient module is. Together with the flatness of the structure sheaf it is what makes
a direct summand of a finite free module flat.

## Main results

* `Stacks.SheafOfModules.FlatRetract.isFlat_of_retract`: a retract of a flat sheaf of modules is
  flat.
* `Stacks.SheafOfModules.FlatRetract.isFlat_of_iso`: flatness transports along an isomorphism of
  sheaves of modules.

## Implementation notes

Flatness of `M` is exactness of `- ⊗_O M`, whose right exactness is automatic (Stacks 05NB, in
the form `Stacks.SheafOfModules.preservesColimits_sheafTensorObj`); the whole content is
therefore preservation of monomorphisms, which is
`Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_of_mono_sheafTensor_map`.

For a monomorphism `ι : A ⟶ B` the naturality square of `M ⊗ - ⟶ N ⊗ -` at `ι` exhibits
`(M ⊗ ι) ≫ (i ⊗ B)` as `(i ⊗ A) ≫ (N ⊗ ι)`. The first factor of the latter is a split
monomorphism, because `i` is one and tensoring is a functor, and the second is a monomorphism
because `N` is flat; so `M ⊗ ι` is a monomorphism by
`Stacks.SheafOfModules.FlatTensorShortExact.mono_of_fac`. This is the same factorisation
argument as part (2) of Stacks 03EY, with the split monomorphism taking the place of the
monomorphism Stacks 03EX supplies there.

The argument is carried out in the tensor order `M ⊗ -`, which is the order the naturality is
available in, and transported to the order `- ⊗ M` that the definition of flatness uses by the
bridge `Stacks.SheafOfModules.isFlat_of_exactFunctor_sheafTensorFlip`, which is how
`isFlat_of_mono_sheafTensor_map` is stated.

All three universes — the objects and the morphisms of the site and the sections of the
structure sheaf — stay independent.

## References

* [The Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
* [The Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules.FlatRetract

-- The sections universe `w` is independent of the two site universes, so Mathlib's
-- size-restricted instances do not supply the sheaf-condition composition through which
-- `Stacks.SheafOfModules.Tensor.ringSheaf` and `IsFlat` are stated.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})

/-- **A retract of a flat sheaf of modules is flat.** If `i : M ⟶ N` and `r : N ⟶ M` satisfy
`i ≫ r = 𝟙 M` and `N` is flat, then `M` is flat. -/
theorem isFlat_of_retract
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (i : M ⟶ N) (r : N ⟶ M) (hir : i ≫ r = 𝟙 M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) N) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) M := by
  refine Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_of_mono_sheafTensor_map R M ?_
  intro A B ι hι
  have hsplit : ∀ P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R),
      Mono (((Stacks.SheafOfModules.Tensor.sheafTensor R).map i).app P) := by
    intro P
    refine (IsSplitMono.mk' ⟨((Stacks.SheafOfModules.Tensor.sheafTensor R).map r).app P, ?_⟩).mono
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, hir,
      CategoryTheory.Functor.map_id, NatTrans.id_app]
  have hNflat : PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj N) :=
    ((exactFunctor_iff _).1 (Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat R hN)).1
  have hv : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj N).map ι) := inferInstance
  refine Stacks.SheafOfModules.FlatTensorShortExact.mono_of_fac
    (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).map ι)
    (((Stacks.SheafOfModules.Tensor.sheafTensor R).map i).app B)
    (((Stacks.SheafOfModules.Tensor.sheafTensor R).map i).app A ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj N).map ι) ?_
    (Stacks.SheafOfModules.FlatTensorShortExact.mono_comp' _ _ (hsplit A) hv)
  exact ((Stacks.SheafOfModules.Tensor.sheafTensor R).map i).naturality ι

/-- **Flatness transports along an isomorphism of sheaves of modules**: if `M ≅ N` and `M` is
flat, then `N` is flat. -/
theorem isFlat_of_iso
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)} (e : M ≅ N)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) N :=
  isFlat_of_retract R e.inv e.hom e.inv_hom_id hM

end Stacks.SheafOfModules.FlatRetract

end
