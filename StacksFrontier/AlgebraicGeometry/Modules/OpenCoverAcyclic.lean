module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictFunctorAlongIso

/-!
# Acyclicity of a complex of modules on a scheme is local on an open cover

A sheaf of modules on a scheme vanishes as soon as its restrictions to the members of an open
cover vanish, and — restriction along an open immersion being exact — a bounded or unbounded
cochain complex of `𝒪_X`-modules is acyclic as soon as its restrictions to the members of an
open cover are acyclic. The same statements are given in the inverse-image spelling and in the
bounded below homotopy category.

## Main results

* `Stacks.AlgebraicGeometry.Modules.isZero_of_isZero_restrictFunctor` and
  `Stacks.AlgebraicGeometry.Modules.isZero_of_isZero_pullback`: **a sheaf of modules whose
  restrictions to an open cover vanish is zero.**
* `Stacks.AlgebraicGeometry.Modules.acyclic_of_acyclic_restrictFunctor` and
  `Stacks.AlgebraicGeometry.Modules.acyclic_of_acyclic_pullback`: **acyclicity of a cochain
  complex of `𝒪_X`-modules is local on an open cover.**
* `Stacks.AlgebraicGeometry.Modules.plus_subcategoryAcyclic_of_pullback`: the same in
  `K⁺(Mod(𝒪_X))`, for the acyclic complexes as an object property.

## Implementation notes

Nothing here is new mathematics; the point is that the two inputs were present and the
conclusion was not. The inputs are
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`, invertibility of a
morphism of `𝒪_X`-modules being local on an open cover, and the exactness of restriction along
an open immersion, `AlgebraicGeometry.Scheme.Modules.restrictFunctor_preservesFiniteLimits`
together with the left adjointness of the restriction — from which instance search already
produces `(Scheme.Modules.restrictFunctor f).PreservesHomology` and, through
`AlgebraicGeometry.Scheme.Modules.pullback_preservesFiniteLimits`, also
`(Scheme.Modules.pullback f).PreservesHomology`. So no exactness statement is proved here.

Vanishing is read off invertibility rather than from the sheaf condition directly: a zero object
`Z` has `(0 : Z ⟶ Z) = 𝟙 Z`, so the restrictions of `0 : M ⟶ M` are invertible, hence so is
`0 : M ⟶ M`, which forces `𝟙 M = 0`. This is the argument of
`Stacks.Adequate.isZero_of_isZero_map` and it avoids a second copy of the section-level
bookkeeping that `Stacks.AlgebraicGeometry.Modules.injective_app_of_cover` already carries.
`AlgebraicGeometry.RingedSpace.isZero_of_restrictModules` is the same statement for a bare
ringed space and the `restrictModules` spelling of restriction; it is not usable here, those
two spellings of a sheaf of modules on a scheme not being interchangeable.

Acyclicity is transported one degree at a time through
`CategoryTheory.ShortComplex.mapHomologyIso`, exactly as
`Stacks.Adequate.acyclic_map_iff` does for a single exact functor reflecting isomorphisms. Here
no single restriction reflects isomorphisms — that is what makes the covering family necessary —
so the reflection step is replaced by the vanishing statement above.

The covering hypothesis is `TopologicalSpace.IsOpenCover`, matching
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`, and the open immersions are
the inclusions `(U i).ι` of the members. For a family of open immersions with arbitrary sources
the same conclusion follows by composing with the isomorphisms onto their open images.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Modules

/-- If a homology-preserving functor maps `K` to an acyclic complex, it kills each homology of
`K`. -/
private theorem isZero_obj_homology_of_acyclic_map {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    (K : CochainComplex C ℤ) (n : ℤ)
    (h : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic) :
    IsZero (F.obj (K.homology n)) := by
  have hn := h n
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hn
  exact hn.of_iso ((K.sc n).mapHomologyIso F).symm

variable {X : Scheme.{u}} {I : Type*} (U : I → X.Opens) (hU : IsOpenCover U)

include hU

/-! ### Vanishing is local on an open cover -/

/-- **A sheaf of modules whose restrictions to an open cover vanish is zero.** Each restriction
of `0 : M ⟶ M` is an endomorphism of a zero object, hence the identity, hence invertible;
invertibility is local on the cover, so `0 : M ⟶ M` is invertible and `𝟙 M = 0`. -/
public theorem isZero_of_isZero_restrictFunctor {M : X.Modules}
    (h : ∀ i, IsZero ((Scheme.Modules.restrictFunctor (U i).ι).obj M)) : IsZero M := by
  have hiso : IsIso (0 : M ⟶ M) := by
    refine AffineBaseChange.isIso_of_isIso_restrict (0 : M ⟶ M) U hU fun i => ?_
    rw [Functor.map_zero, (h i).eq_of_src (0 : _ ⟶ _) (𝟙 _)]
    infer_instance
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : M ⟶ M), zero_comp]

/-- **A sheaf of modules whose inverse images along an open cover vanish is zero**, the inverse
image along an open immersion being isomorphic to the restriction. -/
public theorem isZero_of_isZero_pullback {M : X.Modules}
    (h : ∀ i, IsZero ((Scheme.Modules.pullback (U i).ι).obj M)) : IsZero M :=
  isZero_of_isZero_restrictFunctor U hU fun i =>
    (h i).of_iso ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app M)

/-! ### Acyclicity is local on an open cover -/

/-- **Acyclicity of a cochain complex of `𝒪_X`-modules is local on an open cover.** Restriction
along an open immersion preserves homology, so the homology of the restricted complex is the
restriction of the homology; a sheaf of modules all of whose restrictions to the cover vanish is
zero. -/
public theorem acyclic_of_acyclic_restrictFunctor (K : CochainComplex X.Modules ℤ)
    (h : ∀ i, (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic) : K.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact isZero_of_isZero_restrictFunctor U hU fun i =>
    isZero_obj_homology_of_acyclic_map _ K n (h i)

/-- `Stacks.AlgebraicGeometry.Modules.acyclic_of_acyclic_restrictFunctor` in the inverse-image
spelling: a cochain complex of `𝒪_X`-modules whose inverse images along an open cover are
acyclic is acyclic. -/
public theorem acyclic_of_acyclic_pullback (K : CochainComplex X.Modules ℤ)
    (h : ∀ i, (((Scheme.Modules.pullback (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic) : K.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact isZero_of_isZero_pullback U hU fun i => isZero_obj_homology_of_acyclic_map _ K n (h i)

/-- **Acyclicity in `K⁺(Mod(𝒪_X))` is local on an open cover**, in the inverse-image spelling:
this is the form the localization machinery of `K⁺` consumes. -/
public theorem plus_subcategoryAcyclic_of_pullback (L : HomotopyCategory.Plus X.Modules)
    (h : ∀ i, HomotopyCategory.Plus.subcategoryAcyclic (U i).toScheme.Modules
      ((Scheme.Modules.pullback (U i).ι).mapHomotopyCategoryPlus.obj L)) :
    HomotopyCategory.Plus.subcategoryAcyclic X.Modules L := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective L
  have key (i : I) : (((Scheme.Modules.pullback (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K.obj).Acyclic := by
    have hi : HomotopyCategory.subcategoryAcyclic (U i).toScheme.Modules
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((Scheme.Modules.pullback (U i).ι).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K.obj)) := h i
    rwa [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hi
  show HomotopyCategory.subcategoryAcyclic X.Modules
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K.obj)
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact acyclic_of_acyclic_pullback U hU K.obj key

end Stacks.AlgebraicGeometry.Modules

end
