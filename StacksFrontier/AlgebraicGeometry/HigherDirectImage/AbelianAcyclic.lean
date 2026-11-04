module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.ModuleAbelianComparison
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.ModuleDirectSums
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise

/-!
# Acyclicity of a quasi-coherent module for the direct image of abelian sheaves

Let `f : X ⟶ Y` be an affine morphism of schemes and let `M` be a quasi-coherent
`𝒪_X`-module. [Stacks, Tag 01XC] says that `M` is right acyclic for the direct image of sheaves
of **modules** along `f`. This file records the same statement for the direct image of **abelian
sheaves** along `f`, applied to the sheaf of abelian groups underlying `M`.

The two statements are not interchangeable by unfolding: `Scheme.Modules.pushforward f` and the
abelian direct image are different functors, out of different abelian categories, so their
derived functors are a priori unrelated and so are their acyclic objects. What relates them is
the comparison of higher direct images
`Stacks.AlgebraicGeometry.HigherDirectImage.rightDerivedPushforwardToSheafIso`, and the
observation that both functors are left exact, so that for either of them acyclicity *is* the
vanishing of all the higher derived functors.

## Main results

* `Stacks.AlgebraicGeometry.HigherDirectImage.rightAcyclic_abelianPushforward_toSheaf`: **the
  abelian sheaf underlying a module that is right acyclic for the direct image of modules is
  right acyclic for the direct image of abelian sheaves.**
* `rightAcyclic_abelianPushforward_toSheaf_of_isAffineHom`, in the same namespace: **the abelian
  sheaf underlying a quasi-coherent module is right acyclic for the direct image of abelian
  sheaves along an affine morphism** — the abelian reading of [Stacks, Tag 01XC].

## What this is for

The de Rham complex of a morphism of schemes is pushed forward as a complex of abelian sheaves
(`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap`), so the identification of `f_*` with
`Rf_*` on it asks for acyclicity of its terms for the *abelian* direct image, while
[Stacks, Tag 01XC] supplies acyclicity for the direct image of modules. The module docstrings of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceDeRhamPushforward` and
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceAffineModel` record that mismatch as
one of the two remaining gaps for [Stacks, Tag 0FUI]; what is below is the general lemma that
closes it, and `StacksFrontier.AlgebraicGeometry.DeRham.TotalSpaceAbelianAcyclic` is its reading for
the projection from the total space of a line bundle.

No `@[stacks]` attribute is attached. [Stacks, Tag 01XC] is already carried, for the direct image
of modules, by `Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom`, and the
comparison that carries it across is the untagged
`Stacks.AlgebraicGeometry.HigherDirectImage.rightDerivedPushforwardToSheafIso` — whose own module
docstring explains that [Stacks, Tag 01F1] part (2) is carried at the ringed-space spelling. This
is a reading of results already registered, not a further source result, and in particular it is
not [Stacks, Tag 0FUI], which is a statement about a quasi-isomorphism of de Rham complexes.

## Implementation notes

The abelian direct image is not respelled here: it is
`Stacks.AlgebraicGeometry.HigherDirectImage.abelianPushforward` of
`StacksFrontier.AlgebraicGeometry.HigherDirectImage.ModuleDirectSums`, which is already the spelling
in which `rightDerivedPushforwardToSheafIso` states the comparison, and which
`Stacks.AlgebraicGeometry.HigherDirectImage.abelianPushforward_eq` identifies with the direct
image along the continuous map of underlying spaces.

## References

* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.HigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **An `𝒪_X`-module all of whose higher direct images vanish has an underlying abelian sheaf
that is right acyclic for the direct image of abelian sheaves.**

Both the direct image of modules and the direct image of abelian sheaves are left exact, being
right adjoints, so for either of them right acyclicity is exactly the vanishing of every higher
derived functor ([Stacks, Tag 015C] part (2), available as
`Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived`). The comparison
`rightDerivedPushforwardToSheafIso` identifies `R^n f_*^{ab}` of the underlying abelian sheaf
with the underlying abelian sheaf of `R^n f_*`, and the forgetful functor, being additive,
carries a zero object to a zero object. -/
theorem rightAcyclic_abelianPushforward_toSheaf (M : X.Modules)
    (hM : ∀ n : ℕ, 0 < n → IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    (abelianPushforward f).rightAcyclic
      ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M) := by
  refine (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived
    (abelianPushforward f) _).2 fun n hn => ?_
  exact IsZero.of_iso ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map_isZero (hM n hn))
    ((rightDerivedPushforwardToSheafIso f n).app M).symm

/-- **[Stacks, Tag 01XC] for the direct image of abelian sheaves.** If `f : X ⟶ Y` is an affine
morphism of schemes and `M` is a quasi-coherent `𝒪_X`-module, then the sheaf of abelian groups
underlying `M` is right acyclic for the direct image of abelian sheaves along `f`.

This is the abelian reading of the acyclicity that [Stacks, Tag 01XC] provides for the direct
image of sheaves of modules, and it is the form that a complex of abelian sheaves pushed forward
along `f` — such as the de Rham complex — needs in order to identify `f_*` with `Rf_*`. -/
theorem rightAcyclic_abelianPushforward_toSheaf_of_isAffineHom (M : X.Modules) [IsAffineHom f]
    [M.IsQuasicoherent] :
    (abelianPushforward f).rightAcyclic
      ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M) :=
  rightAcyclic_abelianPushforward_toSheaf f M fun n hn =>
    (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ n M).2
      (Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom
        f M (n : ℤ) (by exact_mod_cast hn))

end Stacks.AlgebraicGeometry.HigherDirectImage

end
