module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceMiddleExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDirectImageAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection

/-!
# A derivation vanishing on the defining ideal descends along the structure map

Let `Z` be a closed subspace of an algebraic space `X` over `Bb`, with inclusion `i : Z ⟶ X` and
defining ideal sheaf `𝓘 ⊆ 𝒪_X`, let `M` be an `𝒪_Z`-module, and let `D : 𝒪_X ⟶ i_*M` be a
`Bb`-derivation which vanishes on every local section of `𝓘`.

The structure map `i♯ : 𝒪_X ⟶ i_*𝒪_Z` is locally surjective and `𝓘` is exactly its kernel
(Stacks 03MB), so `D` descends along it.  This file constructs the descended derivation

```
  D̄ : i_*𝒪_Z ⟶ i_*M
```

of the direct-image sheaf of rings, over the direct-image coefficients of Stacks 03D1, and
proves its Leibniz rule, its compatibility with étale restriction and its vanishing on the
sections read from the base.  The descent is `Stacks.Sites.QuotientDerivation.descend`.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `conormalQuotientDerivation`: `D` and its vanishing on `𝓘`, as
  `Stacks.Sites.QuotientDerivation` data through `i♯`.
* `conormalDescend`: the descended derivation of `i_*𝒪_Z` on sections.

## Main results

* `conormalDescend_structureSharp`: the descent computes `D`, that is `D̄(i♯ a) = D(a)`.
* `conormalDescend_mul`: **the Leibniz rule** for `D̄`, for all sections of `i_*𝒪_Z`.
* `conormalDescend_map`: compatibility with étale restriction.
* `conormalDescend_base_eq_zero`: **the vanishing on the base**, `D̄` kills the sections read
  from `b^{-1}𝒪_{Bb}` through `i♯`.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  as the kernel of the structure map, and its local surjectivity.
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1), the direct image of
  modules over the direct-image sheaf of rings.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Sites

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb)
  (M : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1)
  (D : PresheafOfModulesOfCommRing.Derivation'
    ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj M).val
    (structureSharpInverseImage B S hS b).hom)
  (hvanish : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U), D.d x.1 = 0)

/-- The structure map of the inclusion of a closed subspace is locally surjective. -/
private instance isLocallySurjective_structureSharp_subspaceInclusion :
    Sheaf.IsLocallySurjective (structureSharp B S hS (subspaceInclusion B S hS X Z)) :=
  isLocallySurjective_structureSharp B S hS _ Z.2.2

include hvanish

/-- **A `Bb`-derivation of `𝒪_X` with values in `i_*M` vanishing on the defining ideal sheaf is
derivation data through the structure map `i♯ : 𝒪_X ⟶ i_*𝒪_Z`.** -/
noncomputable def conormalQuotientDerivation :
    QuotientDerivation (structureSharp B S hS (subspaceInclusion B S hS X Z))
      ((moduleDirectImage B S hS (subspaceInclusion B S hS X Z)).obj M) where
  d := D.d
  d_mul a c := D.d_mul a c
  d_map f x := D.d_map f x
  d_eq_zero_of_app_eq_zero a ha :=
    hvanish _ ⟨a, (mem_definingIdealAt_iff B S hS X Z _ a).2 ha⟩

section Descend

variable {U : (SmallEtale B S hS X.1)ᵒᵖ}

/-- **The descended derivation of `i_*𝒪_Z`, on sections**: the descent of
`AlgebraicGeometry.Space.conormalQuotientDerivation` along the structure map of a closed
immersion, which is locally surjective (Stacks 03MB). -/
noncomputable def conormalDescend :
    (structureRingSheafDirectImage B S hS (subspaceInclusion B S hS X Z)).obj.obj U →+
      ((moduleDirectImage B S hS (subspaceInclusion B S hS X Z)).obj M).val.obj U :=
  haveI := isLocallySurjective_structureSharp B S hS (subspaceInclusion B S hS X Z) Z.2.2
  (conormalQuotientDerivation B S hS Z b M D hvanish).descend

/-- **The descent computes the given derivation**: `D̄(i♯ a) = D(a)`. -/
theorem conormalDescend_structureSharp (a : (structureRingSheaf B S hS X).obj.obj U) :
    conormalDescend B S hS Z b M D hvanish
        (((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U).hom a) =
      D.d a :=
  (conormalQuotientDerivation B S hS Z b M D hvanish).descend_app a

/-- **The Leibniz rule for the descended derivation**, for *every* pair of sections of `i_*𝒪_Z`
over an object of the small étale site of `X`, not only for the pairs in the image of `i♯`. -/
theorem conormalDescend_mul
    (x y : (structureRingSheafDirectImage B S hS (subspaceInclusion B S hS X Z)).obj.obj U) :
    conormalDescend B S hS Z b M D hvanish (x * y) =
      x • conormalDescend B S hS Z b M D hvanish y +
        y • conormalDescend B S hS Z b M D hvanish x :=
  (conormalQuotientDerivation B S hS Z b M D hvanish).descend_mul x y

/-- The descended derivation commutes with étale restriction. -/
theorem conormalDescend_map {V : (SmallEtale B S hS X.1)ᵒᵖ} (f : U ⟶ V)
    (x : (structureRingSheafDirectImage B S hS (subspaceInclusion B S hS X Z)).obj.obj U) :
    conormalDescend B S hS Z b M D hvanish
        ((structureRingSheafDirectImage B S hS (subspaceInclusion B S hS X Z)).obj.map f x) =
      ((moduleDirectImage B S hS (subspaceInclusion B S hS X Z)).obj M).val.map f
        (conormalDescend B S hS Z b M D hvanish x) :=
  (conormalQuotientDerivation B S hS Z b M D hvanish).descend_map f x

/-- **The descended derivation vanishes on the sections read from the base.**  A section of
`b^{-1}𝒪_{Bb}`, taken into `i_*𝒪_Z` through `b♯` and then `i♯`, is killed. -/
theorem conormalDescend_base_eq_zero (s : (inverseImageStructureSheaf B S hS b).obj.obj U) :
    conormalDescend B S hS Z b M D hvanish
        (((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U).hom
          ((structureSharpInverseImage B S hS b).hom.app U s)) = 0 :=
  (conormalDescend_structureSharp B S hS Z b M D hvanish _).trans (D.d_app s)

end Descend

end AlgebraicGeometry.Space

end
