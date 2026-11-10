module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedPushforwardQcoh
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedSectionsOverObject
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSmallEtaleTopSectionsDictionary
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionsRestriction

/-!
# On an affine scheme: pseudo-coherence on the small étale site is that of `RΓ(ε(T), -)`

Let `T` be an affine scheme and let `F` be an object of the derived category of `𝒪`-modules on the
small étale site of `T`, all of whose cohomology sheaves are quasi-coherent.  Then, in each degree
separately, `F` is `m`-pseudo-coherent on that site exactly when the complex `RΓ(ε(T), F)` of
`𝒪(ε(T))`-modules — derived sections at the object of the small étale site which is the whole of
`T` — is `m`-pseudo-coherent.

`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineSmallEtaleTopSectionsDictionary.lean` proves
the same comparison with the right-hand side read on the *Zariski* side, as the complex `RΓ(T, E₀)`
of `Γ(T, 𝒪_T)`-modules for an `E₀` with `ε^*E₀ ≅ F`. What this file adds is the identification of
that complex with derived sections of `F` itself at the final object of the small étale site — the
comparison recorded as missing in the module documentation there — and so a statement in which no
object of `D(𝒪_T)` appears at all.

That is the shape the chart comparisons of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean` consume: both sides of
the derived-sections dictionary at an affine étale chart of an algebraic space have been carried by
them to the small étale site of the chart's *scheme*, and the left-hand side arrives there as
derived sections at that site's final object, not as anything on the small Zariski site.

## Main results

* `Stacks.DerivedFunctor.totalRightDerivedRestrictScalarsIso`: deriving a functor into
  `ModuleCat R'` and then restricting scalars along `φ : R →+* R'` derives the composite.  This is
  `Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso` at the exact
  functor `ModuleCat.restrictScalars φ`, named because the instances of that general statement are
  found only when the two module categories are the ones `φ` itself names; see the implementation
  notes.
* `AlgebraicGeometry.SmallEtale.derivedRestrictModuleObjIso`: for `E₀` in `D_QCoh(𝒪_T)` and an
  isomorphism `ε^*E₀ ≅ F`, the identification `Rε_*F ≅ E₀`.  This is the unit of `ε^* ⊣ Rε_*`,
  invertible at a complex with quasi-coherent cohomology, which is the content of **Stacks 071Q**
  in the direction this file needs.
* `AlgebraicGeometry.isPseudoCoherentFrom_derivedSectionsOverTop_iff_derivedSectionsUnbounded`:
  `m`-pseudo-coherence of derived sections of `F` at the whole of `T`, read on the small étale
  site, is `m`-pseudo-coherence of `RΓ(T, E₀)`.
* `AlgebraicGeometry.isPseudoCoherentFrom_derivedSectionsOverTop_iff`: **the statement of the
  header**, with no `E₀` left in it.

## How it is proved

The one comparison which is not bookkeeping is the second result above read through the first:
derived sections at the whole of `T` on the small étale site, and derived sections over `⊤` on the
small Zariski site of `Rε_*F`, differ by the restriction of scalars along the structure map of `ε`
at `⊤`.  The module-valued clause of Stacks 0D6H at `ε`,
`AlgebraicGeometry.SmallEtale.derivedModuleSectionsRestrictModuleIso`, is exactly that statement —
but with the restriction of scalars *inside* the derived functor, where it has to be in order for
the underived statement to be an equality.  Pulling it out is
`Stacks.DerivedFunctor.totalRightDerivedRestrictScalarsIso`, restriction of scalars being exact.

What is then compared are two complexes over two different rings, `𝒪(ε(⊤))` and `Γ(T, 𝒪_T)`.  They
are isomorphic and not equal — `AlgebraicGeometry.SmallEtale.structureMap` at `⊤` is the inverse of
`AlgebraicGeometry.Scheme.Opens.topIso`, so the two rings do not even have the same universe in
their object slot — and the restriction of scalars along that isomorphism is absorbed by
`StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv` at `RingEquiv.ofBijective` of
`AlgebraicGeometry.SmallEtale.bijective_structureMap_hom_app`, which preserves *and* reflects
pseudo-coherence and so costs nothing in either direction.

The last result then feeds that to
`AlgebraicGeometry.isPseudoCoherentFrom_iff_derivedSectionsUnbounded_top_of_iso`, the `E₀` and the
isomorphism being supplied by `AlgebraicGeometry.exists_derived_associatedModuleOfSheaf_iso` —
Stacks 071Q as essential surjectivity of `ε^*` — from quasi-coherence of `F` alone.  Every link is
a biconditional, so both directions come out of the one composite.

## Implementation notes

Everything below is stated on *objects*, not on functors.  Stating the composite of the last leg of
the chart transport with the comparison across `ε` as an isomorphism of functors is out of reach;
on objects each step is cheap.

`Stacks.DerivedFunctor.totalRightDerivedRestrictScalarsIso` is a named specialization rather than
an inline application of the general postcomposition isomorphism. Applied inline at the concrete
data of `ε`, the instance arguments `CategoryTheory.Functor.Additive` and
`CategoryTheory.Limits.PreservesFiniteLimits` of `ModuleCat.restrictScalars` are asked for at the
spelling of the two module categories which the *statement* names — for the codomain, the value at
`⊤` of the pushforward of the structure sheaf along the inclusion of the small Zariski site — and
not at the spelling `ModuleCat.restrictScalars` itself produces. The two are definitionally equal,
but instance search does not unfold the pushforward to see it, and the instances are not found.
Stated once with the ring homomorphism abstract, as it is here, the instances are found at the only
spelling there is, and the application to `ε` is then a defeq check that the elaborator does make.

The derived-category model of the sheaves of modules on the small étale site is left to
`CategoryTheory.HasDerivedCategory.standard` at priority 10000 rather than carried as a binder, and
the two ambient-universe instances answering `CategoryTheory.Abelian` and
`CategoryTheory.IsGrothendieckAbelian` for sheaves of modules are removed, both for the reasons
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineSmallEtaleTopSectionsDictionary.lean`.

No `stacks` tag is placed: the results below are Stacks 0D6H, Stacks 071Q, Stacks 08HE, Stacks 08E7
and Stacks 09VA composed, and the bare attribute for each sits on its own statement.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits

namespace Stacks.DerivedFunctor

universe v₁ u₁ uR uR' w wG wD wD₁ wD₂

/-- **Deriving a functor and then restricting scalars derives the composite.** For
`F : A ⥤ Mod R'` additive out of a Grothendieck abelian category and `φ : R →+* R'`, the unbounded
right derived functor of `F` followed by the functor that restriction of scalars along `φ` induces
on derived categories is canonically the unbounded right derived functor of `F` followed by that
restriction of scalars.

This is `Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso` at
`ModuleCat.restrictScalars φ`, which is exact.  It is named rather than applied inline because the
exactness instances of restriction of scalars are found only at the spelling of the two module
categories that `φ` itself names; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineSmallEtaleTopSectionsOnSite.lean`. -/
public def totalRightDerivedRestrictScalarsIso
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
    [HasDerivedCategory.{wD} A]
    {R : Type uR} {R' : Type uR'} [Ring R] [Ring R']
    [HasDerivedCategory.{wD₁} (ModuleCat.{w} R')]
    [HasDerivedCategory.{wD₂} (ModuleCat.{w} R)]
    (F : A ⥤ ModuleCat.{w} R') [F.Additive] (φ : R →+* R') :
    totalRightDerived F ⋙ (ModuleCat.restrictScalars.{w} φ).mapDerivedCategory ≅
      totalRightDerived (F ⋙ ModuleCat.restrictScalars.{w} φ) :=
  Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso F _

end Stacks.DerivedFunctor

namespace AlgebraicGeometry

universe u

/-- **`Rε_*F ≅ E₀` for `E₀` in `D_QCoh(𝒪_T)` with `ε^*E₀ ≅ F`.**  The unit of `ε^* ⊣ Rε_*` is
invertible at a complex of `𝒪_T`-modules with quasi-coherent cohomology — which is Stacks 071Q in
the direction that recovers `E₀` from its image — so `E₀ ≅ Rε_*ε^*E₀`, and the given isomorphism
carries the right-hand side to `Rε_*F`. -/
public def SmallEtale.derivedRestrictModuleObjIso (B : BigEtaleSite.{u}) (T : Scheme.{u})
    (hT : B.Contains T)
    (F : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT).O)))
    (E₀ : DerivedCategory (SheafOfModules.{u} T.ringCatSheaf))
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor T.Modules i).obj E₀).IsQuasicoherent)
    (e : (SmallEtale.associatedModuleOfSheaf B T hT).mapDerivedCategory.obj E₀ ≅ F) :
    (SmallEtale.derivedRestrictModule.{u + 1, u + 1} B T hT).obj F ≅ E₀ :=
  haveI := SmallEtale.isIso_derivedAssociatedModuleAdjunction_unit_app B T hT E₀ hE₀
  ((SmallEtale.derivedRestrictModule.{u + 1, u + 1} B T hT).mapIso e).symm ≪≫
    (asIso ((SmallEtale.derivedAssociatedModuleAdjunction B T hT).unit.app E₀)).symm

/-- **Derived sections at the whole of `T` on the small étale site are `RΓ(T, E₀)`, as far as
pseudo-coherence can tell.**  Let `T` be a scheme in a big étale site, let `F` be an object of the
derived category of `𝒪`-modules on its small étale site, and let `E₀` be an object of `D(𝒪_T)` with
quasi-coherent cohomology together with an isomorphism `ε^*E₀ ≅ F`.  Then the complex
`RΓ(ε(T), F)` of `𝒪(ε(T))`-modules is `m`-pseudo-coherent if and only if the complex `RΓ(T, E₀)` of
`Γ(T, 𝒪_T)`-modules is.

No affineness is needed: this is the comparison of the two derived-sections functors across `ε` at
the final object, and nothing about pseudo-coherence on a site enters.  See "How it is proved" in
the module documentation. -/
public theorem isPseudoCoherentFrom_derivedSectionsOverTop_iff_derivedSectionsUnbounded
    (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)
    (F : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT).O)))
    (E₀ : DerivedCategory (SheafOfModules.{u} T.ringCatSheaf))
    (hE₀ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor T.Modules i).obj E₀).IsQuasicoherent)
    (e : (SmallEtale.associatedModuleOfSheaf B T hT).mapDerivedCategory.obj E₀ ≅ F) (m : ℤ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.evaluation.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT).O)
            (op (SmallEtale.opensObj B T hT ⊤)))).obj F) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((derivedSectionsUnbounded T ⊤).obj E₀) m := by
  have hiso :
      (ModuleCat.restrictScalars.{u}
            ((SmallEtale.structureMap B T hT).hom.app
              (op (⊤ : T.Opens))).hom).mapDerivedCategory.obj
          ((Stacks.DerivedFunctor.totalRightDerived
            (SheafOfModules.evaluation.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT).O)
              (op (SmallEtale.opensObj B T hT ⊤)))).obj F) ≅
        (derivedSectionsUnbounded T ⊤).obj E₀ :=
    (Stacks.DerivedFunctor.totalRightDerivedRestrictScalarsIso
        (SheafOfModules.evaluation.{u} (SmallEtale.structureSheaf B T hT)
          (op ((SmallEtale.opensToSmallEtale B T hT).obj ⊤)))
        ((SmallEtale.structureMap B T hT).hom.app (op (⊤ : T.Opens))).hom).app F ≪≫
      (SmallEtale.derivedModuleSectionsRestrictModuleIso B T hT ⊤).app F ≪≫
      (derivedSectionsUnbounded T ⊤).mapIso
        (SmallEtale.derivedRestrictModuleObjIso B T hT F E₀ hE₀ e)
  refine Iff.trans ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv.{u, u, u}
    (RingEquiv.ofBijective _ (SmallEtale.bijective_structureMap_hom_app B T hT ⊤))
    ((Stacks.DerivedFunctor.totalRightDerived
      (SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT).O)
        (op (SmallEtale.opensObj B T hT ⊤)))).obj F)).1 m) ?_
  exact ⟨fun h => StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso h hiso,
    fun h => StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso h hiso.symm⟩

/-- **On one affine scheme, pseudo-coherence on the small étale site is pseudo-coherence of derived
sections at the site's final object, in a fixed degree.**  Let `T` be an affine scheme in a big
étale site and let `F` be an object of the derived category of `𝒪`-modules on its small étale site
all of whose cohomology sheaves are quasi-coherent.  Then `F` is `m`-pseudo-coherent on that site
if and only if the complex `RΓ(ε(T), F)` of `𝒪(ε(T))`-modules is `m`-pseudo-coherent.

This is the whole scheme side of the derived-sections dictionary at an affine étale chart of an
algebraic space — item (iii) of the display in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsolute.lean` — with the
chart and the algebraic space removed, and with no object of `D(𝒪_T)` left in the statement.

It is `AlgebraicGeometry.isPseudoCoherentFrom_iff_derivedSectionsUnbounded_top_of_iso` composed
with `AlgebraicGeometry.isPseudoCoherentFrom_derivedSectionsOverTop_iff_derivedSectionsUnbounded`,
the object `E₀` of `D_QCoh(𝒪_T)` and the isomorphism `ε^*E₀ ≅ F` that both of them take being
supplied by `AlgebraicGeometry.exists_derived_associatedModuleOfSheaf_iso` — Stacks 071Q as
essential surjectivity of `ε^*` — from quasi-coherence of `F` alone. -/
public theorem isPseudoCoherentFrom_derivedSectionsOverTop_iff
    (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T) [IsAffine T]
    (F : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT).O)))
    (hF : DerivedCategoryB.derivedCategoryB (SmallEtale.qcohOnSite B T hT) F) (m : ℤ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.evaluation.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT).O)
            (op (SmallEtale.opensObj B T hT ⊤)))).obj F) m ↔
      (smallEtaleRingedSite B T hT).IsPseudoCoherentFrom F m := by
  obtain ⟨E₀, hE₀, ⟨e⟩⟩ := exists_derived_associatedModuleOfSheaf_iso B T hT F hF
  exact (isPseudoCoherentFrom_derivedSectionsOverTop_iff_derivedSectionsUnbounded
      B T hT F E₀ hE₀ e m).trans
    (isPseudoCoherentFrom_iff_derivedSectionsUnbounded_top_of_iso B T hT F E₀ hE₀ e m).symm

end AlgebraicGeometry

end
