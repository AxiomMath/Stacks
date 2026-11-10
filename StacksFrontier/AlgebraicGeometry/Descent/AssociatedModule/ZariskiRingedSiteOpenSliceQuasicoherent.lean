module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ZariskiRingedSiteOpenSliceLocality
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Quasi-coherence of the cohomology travels across the open slice

The induction of Stacks 0DII carries a predicate `P` with two conjuncts: that `ε^*E` is
`m`-pseudo-coherent, and that the cohomology sheaves of `E` are quasi-coherent.  The locality
reduction `AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme`
moves the *first* conjunct from the open subscheme `V` to `X`: it asks, over each member `V` of a
covering, for `m`-pseudo-coherence of the restriction `E|_V` read as a complex of `𝒪_V`-modules
along Mathlib's `AlgebraicGeometry.Scheme.Modules.overEquiv`.  Nothing there carries the *second*
conjunct, and that is what this module supplies: quasi-coherence of the cohomology sheaves of `E`
implies quasi-coherence of the cohomology sheaves of that reading of `E|_V` on the scheme `V`.

This is not the cone propagation of
`AlgebraicGeometry.isQuasicoherent_homology_obj₃_of_distinguished_zariskiRingedSite`, which is a
statement inside a single `D(𝒪_S)`.  Here two categories are crossed: restriction along `V ⊆ X`
and the slice identification `AlgebraicGeometry.Scheme.Modules.overEquiv V`.

## The shape of the argument

The composite that the locality reduction applies to a module is
`SheafOfModules.overFunctor X.ringCatSheaf V ⋙ (Scheme.Modules.overEquiv V).functor`, and Mathlib
already identifies it: `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` is a natural
isomorphism from it to `AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι`, restriction along
the open immersion `V.ι : V ⟶ X`.  Quasi-coherence of a restriction along an open immersion is
Mathlib's `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`, and quasi-coherent
modules are closed under isomorphism; so no quasi-coherence is reproved here, and in particular
no second encoding of the slice identification is introduced — the equivalence used is Mathlib's,
as in the module
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ZariskiRingedSiteOpenSliceTransport`.

Passing from modules to the derived category is
`CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso`: an exact additive functor
commutes with the cohomology functors of the derived categories.  Both functors of the composite
are exact — the slice identification because it is an equivalence, restriction to a slice by
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits` and its colimit
counterpart — so the cohomology of the transported object is the transport of the cohomology, and
the module-level statement applies to it.

## Main results

* `AlgebraicGeometry.Scheme.isQuasicoherent_modulesOverEquiv_over`: **a quasi-coherent
  `𝒪_X`-module restricts to a quasi-coherent `𝒪_V`-module** across the slice identification.
* `AlgebraicGeometry.Scheme.isQuasicoherent_homology_modulesOverEquiv_overFunctor`: **the second
  conjunct of `P`, transported across the open slice.**  If every cohomology sheaf of `E` is
  quasi-coherent, then so is every cohomology sheaf of the reading of `E|_V` as a complex of
  `𝒪_V`-modules.
* `AlgebraicGeometry.Scheme`
  `.isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme_quasicoherent`: **`P` as a whole
  survives the locality reduction.**  It is the locality capstone with the local hypothesis
  weakened: over a member `V` of the covering one may now assume the quasi-coherence conjunct,
  because it is discharged by the transport above rather than assumed.

## Implementation notes

No new spelling or exactness bridge is declared.  The three the statements need — exactness of
restriction to a slice in both variances, and the derived-category model for Mathlib's
`AlgebraicGeometry.Scheme.Modules` of an open subscheme — are the ones the locality capstone
already declares, and the `attribute [local instance]` lines below take the attribute on *those*
declarations.  A fresh pair would be definitionally equal and not syntactically the same, and the
statements here have to be the ones the capstone consumes; they are `local` there deliberately
(see its implementation notes) and stay so.

A consumer of these statements outside this file has to re-take the same attribute, because the
instances occur in the statements through `CategoryTheory.Functor.mapDerivedCategory`.  That is a
property inherited from the capstone, not added here.

## References

* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 01BE](https://stacks.math.columbia.edu/tag/01BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u d d' dV

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- **A quasi-coherent `𝒪_X`-module stays quasi-coherent across the open slice.**  Restricting a
sheaf of `𝒪_X`-modules to the slice of the Zariski site at an open `V` and reading the result as a
sheaf of `𝒪_V`-modules along Mathlib's `AlgebraicGeometry.Scheme.Modules.overEquiv` gives a
quasi-coherent module.

The composite is Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι`, by
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`, and restriction along an open immersion
preserves quasi-coherence by
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`. -/
theorem isQuasicoherent_modulesOverEquiv_over (V : X.Opens)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))
    (hM : M.IsQuasicoherent) :
    ((Scheme.Modules.overEquiv V).functor.obj
      ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O) V).obj
        M)).IsQuasicoherent := by
  -- `AlgebraicGeometry.RingedSite.ringSheaf` is a `def`, so the hypothesis has to be restated at
  -- the spelling `AlgebraicGeometry.Scheme.ringCatSheaf` that Mathlib's restriction is about.
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M := hM
  have : ((Scheme.Modules.restrictFunctor V.ι).obj M).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor V.ι M
  exact (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.overFunctorEquiv V).app M).symm inferInstance

-- Exactness of restriction to a slice of the Zariski site, with the attribute taken on the very
-- declarations whose instances the locality capstone's statement is elaborated against: a second
-- pair of bridges would be definitionally equal but not syntactically the same, and the statements
-- below have to be the ones the capstone consumes.
attribute [local instance] overFunctorPreservesFiniteLimits overFunctorPreservesFiniteColimits

variable [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))]
  [∀ U : X.Opens,
    HasDerivedCategory.{d'}
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O).over U))]
  [∀ U : X.Opens,
    HasDerivedCategory.{dV}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf U.toScheme.zariskiRingedSite.O))]

attribute [local instance] hasDerivedCategory_opensToSchemeModules
  hasDerivedCategory_ringCatSheafOver

/-- **Quasi-coherence of the cohomology travels across the open slice.**  Let `E` be an object of
`D(𝒪_X)` all of whose cohomology sheaves are quasi-coherent.  Then every cohomology sheaf of the
reading of its restriction `E|_V` as a complex of `𝒪_V`-modules — along Mathlib's
`AlgebraicGeometry.Scheme.Modules.overEquiv`, which is the object the locality reduction
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme` asks about
— is quasi-coherent.

This is the second conjunct of the predicate `P` of the induction of Stacks 0DII carried across
the open-slice identification; the first conjunct's transport is
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiOver_of_modulesOverEquiv`.

Both functors crossed are exact, so each commutes with the cohomology functors of the derived
categories (`CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso`); the cohomology of
the transported object is therefore the transport of the cohomology, and
`AlgebraicGeometry.Scheme.isQuasicoherent_modulesOverEquiv_over` applies to it. -/
theorem isQuasicoherent_homology_modulesOverEquiv_overFunctor (V : X.Opens)
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)))
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)) j).obj
        E).IsQuasicoherent)
    (j : ℤ) :
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O)) j).obj
      ((Scheme.Modules.overEquiv V).functor.mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O) V).mapDerivedCategory.obj
          E))).IsQuasicoherent := by
  refine (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.overEquiv V).functor.mapDerivedCategoryCompHomologyFunctorIso j).app
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O) V).mapDerivedCategory.obj
          E) ≪≫
      (Scheme.Modules.overEquiv V).functor.mapIso
        (((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)
          V).mapDerivedCategoryCompHomologyFunctorIso j).app E)).symm ?_
  exact isQuasicoherent_modulesOverEquiv_over X V _ (hE j)

/-- **`P` as a whole survives the locality reduction.**  This is the locality capstone
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme` with its
local hypothesis *weakened*: over a member `V` of the covering, `m`-pseudo-coherence of the
restriction `E|_V` on the scheme `V` need only be proved under the assumption that `E|_V` has
quasi-coherent cohomology there, because that assumption is discharged by
`AlgebraicGeometry.Scheme.isQuasicoherent_homology_modulesOverEquiv_overFunctor` from the
corresponding assumption on `E`.

So the predicate `P` of the induction of Stacks 0DII — `m`-pseudo-coherence together with
quasi-coherence of the cohomology — is available in full over each member of the covering, which
is what the reduction "the question is local, so we may assume `X` affine" has to provide for
0DII.  The capstone itself is unchanged; this is a consequence of it. -/
theorem isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme_quasicoherent
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)))
    (m : ℤ)
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)) j).obj
        E).IsQuasicoherent)
    (h : ∀ U : X.Opens, ∃ S : Presieve U, Sieve.generate S ∈ X.zariskiRingedSite.J U ∧
      ∀ ⦃V : X.Opens⦄ (f : V ⟶ U), S f →
        (∀ j : ℤ, ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O)) j).obj
          ((Scheme.Modules.overEquiv V).functor.mapDerivedCategory.obj
            ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)
              V).mapDerivedCategory.obj E))).IsQuasicoherent) →
        V.toScheme.zariskiRingedSite.IsPseudoCoherentFrom
          ((Scheme.Modules.overEquiv V).functor.mapDerivedCategory.obj
            ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)
              V).mapDerivedCategory.obj E)) m) :
    X.zariskiRingedSite.IsPseudoCoherentFrom E m := by
  refine isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme X E m fun U => ?_
  obtain ⟨S, hS, hdata⟩ := h U
  exact ⟨S, hS, fun {V} f hf =>
    hdata f hf fun j => isQuasicoherent_homology_modulesOverEquiv_overFunctor X V E hE j⟩

end AlgebraicGeometry.Scheme

end
