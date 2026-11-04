module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.AffineVanishingUnbounded
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsPushforward
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Derived global sections over a base with a one-point space

Let `A` be a commutative ring whose spectrum is a single point — a field, for instance — and let
`f : X ⟶ Spec A` be a scheme over `A`. Then

`R Γ(X, -) ≅ R Γ(Spec A, -) ∘ Rf_*`

with no hypothesis on `f` at all: the comparison `AlgebraicGeometry.baseLerayComparison` of
`StacksFrontier/AlgebraicGeometry/DerivedGlobalSectionsPushforward.lean` is an isomorphism.

The reason is that on a space with at most one point global sections are *exact*, so derived
global sections on `Spec A` are global sections and the unit of `RΓ(Spec A, -)` is invertible at
every complex — in particular at the direct image of a K-injective complex, which is exactly the
condition `AlgebraicGeometry.isIso_baseLerayComparison_iff` reduces the comparison to. No
flatness of `f` and no preservation of K-injectivity by `f_*` is needed.

This is the case of [Stacks, Tag 0D5W] that the duality of [Stacks, Tag 0BS2] over a field
consumes: it identifies the derived global sections
`AlgebraicGeometry.derivedGlobalSectionsOver` whose cohomology is
`AlgebraicGeometry.cohomologyOverField` with the derived direct image
`Stacks.Duality.derivedPushforward` that the right adjoint of [Stacks, Tag 0A9E] is stated for.

## Main results

* `AlgebraicGeometry.preservesEpimorphisms_evaluation_of_subsingleton` and
  `AlgebraicGeometry.preservesFiniteColimits_evaluation_of_subsingleton`: sections over an open
  with at most one point are exact, for a sheaf of modules over any sheaf of rings on a
  topological space.
* `AlgebraicGeometry.isIso_derivedGlobalSectionsOverUnit_app_of_exact`: when `A`-linear global
  sections on `Spec A` are exact, the unit of their total right derived functor is invertible at
  every complex.
* `AlgebraicGeometry.isIso_baseLerayComparison_of_exact` and
  `AlgebraicGeometry.derivedGlobalSectionsOverIsoDerivedPushforwardOfExact`: the comparison
  `RΓ(X, -) ⟶ RΓ(Spec A, -) ∘ Rf_*` and the natural isomorphism it is, with no hypothesis on
  `f`.
* `AlgebraicGeometry.derivedGlobalSectionsOverIsoDerivedPushforwardOfField`: the same over a
  field, where the exactness hypothesis is discharged.

## Implementation notes

**Why sections over a one-point open are exact.** A covering sieve of an open `W` with at most
one point must contain an open containing that point, and an open of `W` containing it is `W`
itself; so a locally surjective map of sheaves is surjective on sections over `W`. This is the
argument of the private
`Stacks.Cohomology.DerivedSectionsLeray.preservesEpimorphisms_evaluation_of_subsingleton` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayForDerivedSections.lean`,
reproved here for an arbitrary sheaf of rings on a topological space rather than for the
structure sheaf of a ringed space, because that declaration is `private` and because the ringed
space is not the shape needed.

**From exactness to the unit.** `Stacks.DerivedFunctor.HigherDerivedOfExact.everywhere_defined`
([Stacks, Tag 015F] part (3)) says that for an exact functor the functor induced termwise on
derived categories is a right derived functor, with a comparison that is an *isomorphism*. The
canonical unit of `AlgebraicGeometry.derivedGlobalSectionsOver` composed with the comparison of
right derived functors is that isomorphism, and the comparison is invertible because both are
right derived functors; so the canonical unit is invertible too.

**Spelling.** `AlgebraicGeometry.globalSectionsOver` is declared with source
`AlgebraicGeometry.Scheme.Modules`, whose `Category` and `Preadditive` instances are declared
separately from those of `SheafOfModules`, so instance search does not cross between the two
spellings; the exactness of its first factor is therefore supplied by passing the instance
explicitly to `CategoryTheory.Limits.comp_preservesFiniteColimits`, as
`AlgebraicGeometry.globalSectionsOver_preservesFiniteLimits` does for finite limits.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 015F](https://stacks.math.columbia.edu/tag/015F)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Sections over an open with at most one point are exact -/

/-- **Sections over an open with at most one point preserve epimorphisms.** A covering sieve of
such an open `W` must contain an open containing its unique point, and any open of `W`
containing that point is `W` itself; so an epimorphism of sheaves of modules, being locally
surjective, is surjective on sections over `W`. -/
public theorem preservesEpimorphisms_evaluation_of_subsingleton {Z : Type u} [TopologicalSpace Z]
    (R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (W : Opens Z)
    [Subsingleton W] [Nonempty W] :
    (SheafOfModules.evaluation.{u} R (op W)).PreservesEpimorphisms where
  preserves {M N} φ hφ := by
    have := hφ
    rw [ModuleCat.epi_iff_surjective]
    intro t
    have hepi : Epi ((SheafOfModules.toSheaf.{u} R).map φ) := inferInstance
    have hloc := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      ((SheafOfModules.toSheaf.{u} R).map φ)).mpr hepi
    obtain ⟨x, hx⟩ := ‹Nonempty W›
    have := hloc
    have hcov := Presheaf.imageSieve_mem (Opens.grothendieckTopology Z)
      ((SheafOfModules.toSheaf.{u} R).map φ).hom t
    obtain ⟨U, i, ⟨s, hs⟩, hxU⟩ := hcov x hx
    have hUW : U = W := le_antisymm (leOfHom i) (by
      intro y hy
      have he : (⟨y, hy⟩ : W) = ⟨x, hx⟩ := Subsingleton.elim _ _
      have hxy : y = x := congrArg Subtype.val he
      exact hxy.symm ▸ hxU)
    subst U
    have hi : i = 𝟙 W := Subsingleton.elim _ _
    subst i
    exact ⟨s, by
      show φ.val.app (op W) s = t
      rw [op_id, (((SheafOfModules.toSheaf.{u} R).obj N).obj).map_id] at hs
      exact hs⟩

/-- **Sections over an open with at most one point are exact.** Sections over any open are left
exact, and over an open with at most one point they also preserve epimorphisms, so they preserve
homology and hence finite colimits. -/
public theorem preservesFiniteColimits_evaluation_of_subsingleton {Z : Type u}
    [TopologicalSpace Z] (R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (W : Opens Z)
    [Subsingleton W] [Nonempty W] :
    PreservesFiniteColimits (SheafOfModules.evaluation.{u} R (op W)) := by
  have hepi := preservesEpimorphisms_evaluation_of_subsingleton R W
  have hker : ∀ {M N : SheafOfModules.{u} R} (φ : M ⟶ N),
      PreservesLimit (parallelPair φ 0) (SheafOfModules.evaluation.{u} R (op W)) :=
    fun _ => inferInstance
  have : (SheafOfModules.evaluation.{u} R (op W)).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-! ### Exactness of global sections on a base with a one-point space -/

variable {A : Type u} [CommRing A]

section OnePoint

variable [Subsingleton (Spec (.of A))] [Nonempty (Spec (.of A))]

omit [Nonempty (Spec (.of A))] in
/-- The whole space of `Spec A` has at most one point when `Spec A` does. -/
public theorem subsingleton_top_opens_spec :
    Subsingleton ↥(⊤ : Opens ↑(Spec (.of A))) :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩

omit [Subsingleton (Spec (.of A))] in
/-- The whole space of `Spec A` is nonempty when `Spec A` is. -/
public theorem nonempty_top_opens_spec : Nonempty ↥(⊤ : Opens ↑(Spec (.of A))) :=
  ⟨⟨Classical.arbitrary _, trivial⟩⟩

/-- **`A`-linear global sections on `Spec A` are exact when `Spec A` is a single point.**
Sections over an open with at most one point are exact, and restriction of scalars along
`A ≅ Γ(Spec A, 𝒪)` is exact. -/
public theorem preservesFiniteColimits_globalSectionsOver_id :
    PreservesFiniteColimits (globalSectionsOver (𝟙 (Spec (.of A)))) :=
  @comp_preservesFiniteColimits _ _ _ _ _ _ _ _
    (@preservesFiniteColimits_evaluation_of_subsingleton _ _ (Spec (.of A)).ringCatSheaf ⊤
      subsingleton_top_opens_spec nonempty_top_opens_spec)
    (StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits _)

end OnePoint

/-! ### The comparison with no hypothesis on the morphism -/

/-- **The unit of `RΓ(Spec A, -)` is invertible everywhere when global sections are exact.**
For an exact functor the functor induced termwise on unbounded derived categories is already a
right derived functor, with an *invertible* comparison ([Stacks, Tag 015F] part (3)); the
canonical unit of `AlgebraicGeometry.derivedGlobalSectionsOver` differs from it by the
comparison of two right derived functors, which is invertible, so it is invertible too. -/
public theorem isIso_derivedGlobalSectionsOverUnit_app_of_exact
    [PreservesFiniteColimits (globalSectionsOver (𝟙 (Spec (.of A))))]
    (K : HomotopyCategory (Spec (.of A)).Modules (ComplexShape.up ℤ)) :
    IsIso ((derivedGlobalSectionsOverUnit (𝟙 (Spec (.of A)))).app K) := by
  have hRD := (Stacks.DerivedFunctor.HigherDerivedOfExact.everywhere_defined
    (globalSectionsOver (𝟙 (Spec (.of A))))).2
  have hdesc : IsIso ((derivedGlobalSectionsOver (𝟙 (Spec (.of A)))).rightDerivedDesc
      (derivedGlobalSectionsOverUnit (𝟙 (Spec (.of A))))
      (HomotopyCategory.quasiIso (Spec (.of A)).Modules (ComplexShape.up ℤ)) _
      (Stacks.DerivedFunctor.HigherDerivedOfExact.canonical
        (globalSectionsOver (𝟙 (Spec (.of A)))))) :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 hRD
  have hfac := (derivedGlobalSectionsOver (𝟙 (Spec (.of A)))).rightDerived_fac_app
    (derivedGlobalSectionsOverUnit (𝟙 (Spec (.of A))))
    (HomotopyCategory.quasiIso (Spec (.of A)).Modules (ComplexShape.up ℤ)) _
    (Stacks.DerivedFunctor.HigherDerivedOfExact.canonical
      (globalSectionsOver (𝟙 (Spec (.of A))))) K
  have hcan : IsIso ((Stacks.DerivedFunctor.HigherDerivedOfExact.canonical
      (globalSectionsOver (𝟙 (Spec (.of A))))).app K) := by
    have : IsIso (Stacks.DerivedFunctor.HigherDerivedOfExact.canonical
        (globalSectionsOver (𝟙 (Spec (.of A))))) :=
      @Iso.isIso_inv _ _ _ _
        (globalSectionsOver (𝟙 (Spec (.of A)))).mapDerivedCategoryFactorsh
    infer_instance
  have := hdesc
  exact (isIso_comp_right_iff _ _).mp (hfac ▸ hcan)

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **[Stacks, Tag 0D5W] over a base whose global sections are exact.** The comparison
`RΓ(X, -) ⟶ RΓ(Spec A, -) ∘ Rf_*` is an isomorphism, with no hypothesis on `f`: the condition
that `AlgebraicGeometry.isIso_baseLerayComparison_iff` reduces it to is the invertibility of the
unit of `RΓ(Spec A, -)` at the direct image of a K-injective complex, and when global sections
on `Spec A` are exact that unit is invertible at every complex. -/
public theorem isIso_baseLerayComparison_of_exact
    [PreservesFiniteColimits (globalSectionsOver (𝟙 (Spec (.of A))))] :
    IsIso (baseLerayComparison f) := by
  rw [isIso_baseLerayComparison_iff]
  intro I _
  exact isIso_derivedGlobalSectionsOverUnit_app_of_exact _

/-- **Derived global sections over the base are derived pushforward to the base**, over a base
whose `A`-linear global sections are exact and with no hypothesis on `f`. -/
public def derivedGlobalSectionsOverIsoDerivedPushforwardOfExact
    [PreservesFiniteColimits (globalSectionsOver (𝟙 (Spec (.of A))))] :
    derivedGlobalSectionsOver f ≅
      Stacks.Duality.derivedPushforward f ⋙ derivedGlobalSectionsOver (𝟙 (Spec (.of A))) :=
  have := isIso_baseLerayComparison_of_exact f
  asIso (baseLerayComparison f)

/-! ### Over a field -/

/-- **Derived global sections over a field are derived pushforward to `Spec k`.** For a scheme
`f : X ⟶ Spec k` over a field, with no hypothesis on `f` at all, the total right derived functor
`RΓ(X, -) : D(𝒪_X) ⥤ D(k)` of `k`-linear global sections — the functor whose cohomology is
`AlgebraicGeometry.cohomologyOverField` — is derived direct image `Rf_*` followed by derived
global sections on `Spec k`.

This identifies the two spellings of derived global sections over the base: the
`AlgebraicGeometry.derivedGlobalSectionsOver` of the cohomology of a variety, and the
`Stacks.Duality.derivedPushforward` that the right adjoint of [Stacks, Tag 0A9E] and the
`D_QCoh` development are stated for. `Spec k` is a single point, so global sections there are
exact and [Stacks, Tag 0D5W] needs nothing of `f`. -/
public def derivedGlobalSectionsOverIsoDerivedPushforwardOfField (k : Type u) [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) :
    derivedGlobalSectionsOver g ≅
      Stacks.Duality.derivedPushforward g ⋙ derivedGlobalSectionsOver (𝟙 (Spec (.of k))) :=
  have : PreservesFiniteColimits (globalSectionsOver (𝟙 (Spec (.of k)))) :=
    preservesFiniteColimits_globalSectionsOver_id
  derivedGlobalSectionsOverIsoDerivedPushforwardOfExact g

end AlgebraicGeometry

end
