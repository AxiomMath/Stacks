module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes

/-!
# The derived localization square of a morphism of ringed sites

Let `f : (C, O) ⟶ (D, O')` be a morphism of ringed sites given by `u : D ⥤ C`, let `W` be an
object of `D` and put `U = u(W)`. Stacks 04J0 makes the square

```
  (Sh(C/U), O_U)   --j_U-->  (Sh(C), O)
       | f'                     | f
  (Sh(D/W), O'_W)  --j_W-->  (Sh(D), O')
```

commute, and `AlgebraicGeometry.RingedSite.Hom.localizedPullbackToposSquare` is the resulting
commuting square of *underived* pullbacks of sheaves of modules,
`f^* ⋙ (-|_U) ≅ (-|_W) ⋙ (f')^*`. This file derives it: for every object `E` of `D(O')`,

```
  L(f')^* (E|_W)  ≅  (Lf^* E)|_U .
```

## The argument

The comparison is produced objectwise, which is all its consumers need, and the object chosen to
produce it at is a K-flat resolution that *stays* K-flat after restriction to the slice —
`Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction`. On such a resolution
`K` both derived pullbacks are computed by the degreewise ones, by the computation clause of
Stacks 06YY, and restriction to a slice is exact, so it is computed degreewise too. The
comparison is then the underived square read at `K`:

```
  (Lf^* E)|_U ≅ Q(j_U(f^* K)) ≅ Q((f')^*(j_W K)) ≅ L(f')^*(Q(j_W K)) ≅ L(f')^*(E|_W).
```

Nothing here is a second construction of the square: the only mathematical input is
`localizedPullbackToposSquare`, and the only input about K-flatness is the one resolution.

No finite limits are needed on either site, nor that `u` preserve them: the localized morphism
`f'` of Stacks 04J0 exists for any morphism of ringed sites, the underived square holds for it,
and the resolution is built without binary products on the site.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits`:
  the derived localization square, objectwise, with no finite limits on either site.
* `AlgebraicGeometry.RingedSite.Hom.nonempty_derivedPullbackLocalizedIso`: the same, stated
  for sites with finite limits and a finite-limit-preserving `u`.

## References

* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Degreewise pullback along a morphism of ringed sites, followed by localization, has an
everywhere-defined left derived functor: a morphism of ringed sites is in particular a morphism
of the underlying sites, which is what
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`
asks for. -/
local instance derivedPullbackHasLeftDerived :
    (pullbackOnHomotopy f.toRingedToposSiteHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Y).O))
        (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy _ f.isMorphismOfSites

variable (W : Y.C)
  [HasSheafify (X.J.over (f.u.obj W)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj W)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Y.J.over W) AddCommGrpCat.{u}]
  [(Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj W)).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Y.J.over W).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The same existence statement for the localization of `f` at an object `W` of the target,
which is again a morphism of ringed sites by Stacks 04J0. -/
local instance derivedPullbackLocalizedHasLeftDerived :
    (pullbackOnHomotopy (f.localized W).toRingedToposSiteHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (Y.over W)).O))
        (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy _ (f.localized W).isMorphismOfSites

/-- The derived pullback along the localization of `f` at an object `W` of the target commutes
with the shift. -/
local instance derivedPullbackLocalizedCommShift :
    (derivedPullback (f.localized W).toRingedToposSiteHom).CommShift ℤ :=
  Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_commShift
    (f.localized W).toRingedToposSiteHom

/-- Restriction of sheaves of `O'`-modules to the slice over `W` preserves finite colimits. -/
local instance localizedOverFunctorColimits :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W

/-- Restriction of sheaves of `O`-modules to the slice over `u(W)` preserves finite limits. -/
local instance localizedOverFunctorLimits' :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj W)) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits (f.u.obj W)

/-- Restriction of sheaves of `O`-modules to the slice over `u(W)` preserves finite colimits. -/
local instance localizedOverFunctorColimits' :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj W)) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits (f.u.obj W)

/-- On a K-flat complex with flat terms, the derived pullback is the degreewise one. -/
private def derivedPullbackObjIsoOfKFlat {A B : RingedTopos.{u, u, u}}
    [A.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify A.J AddCommGrpCat.{u}] [A.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify B.J AddCommGrpCat.{u}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (g : RingedToposSiteHom A B) (hmos : g.u.IsMorphismOfSites B.J A.J)
    [(pullbackOnHomotopy g).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B.O))
        (ComplexShape.up ℤ))]
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)) ℤ)
    (hK : IsKFlat (Y := B) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :
    (derivedPullback g).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((pullbackComplex g).obj K) :=
  derivedPullbackObjIsoOfIsIsoComparison g K
    (isIso_derivedPullbackComparison_app_of_isKFlat g hmos _ hK)

omit [(X.J.over (f.u.obj W)).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Y.J.over W).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The derived localization square of Stacks 04J0.** Pulling an object `E` of `D(O')` back
along `f` and then restricting to the slice over `U = u(W)` is isomorphic to restricting `E` to
the slice over `W` and then pulling back along the localized morphism `f'`.

The comparison is produced at a K-flat resolution with flat terms whose restriction to the slice
over `W` is again K-flat with flat terms
(`Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction`); on such a complex
both derived pullbacks are the degreewise ones, by the computation clause of Stacks 06YY, and
the comparison is then the underived square
`AlgebraicGeometry.RingedSite.Hom.localizedPullbackToposSquare` read at that complex. -/
theorem Hom.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Y).O))) :
    Nonempty ((derivedPullback (f.localized W).toRingedToposSiteHom).obj
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W).mapDerivedCategory.obj E) ≅
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj W)).mapDerivedCategory.obj
        ((derivedPullback f.toRingedToposSiteHom).obj E)) := by
  obtain ⟨K, s, hKflat, hKterms, hs, -, hJKflat, hJKterms⟩ :=
    Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction Y.O W
      (DerivedCategory.Q.objPreimage E)
  have := hs
  have hQs : IsIso (DerivedCategory.Q.map s) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  have eK : DerivedCategory.Q.obj K ≅ E :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  set JK := (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W).mapHomologicalComplex
    (ComplexShape.up ℤ) |>.obj K with hJK
  have eg := derivedPullbackObjIsoOfKFlat f.toRingedToposSiteHom f.isMorphismOfSites K
    ⟨hKflat, hKterms⟩
  have ef := derivedPullbackObjIsoOfKFlat (f.localized W).toRingedToposSiteHom
    (f.localized W).isMorphismOfSites JK ⟨hJKflat, hJKterms⟩
  refine ⟨?_⟩
  refine (derivedPullback (f.localized W).toRingedToposSiteHom).mapIso
      ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W).mapDerivedCategory.mapIso eK.symm) ≪≫ ?_
  refine (derivedPullback (f.localized W).toRingedToposSiteHom).mapIso
      ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W).mapDerivedCategoryFactors.app K) ≪≫ ?_
  have eSq : ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj W)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((pullbackComplex f.toRingedToposSiteHom).obj K) ≅
      (pullbackComplex (f.localized W).toRingedToposSiteHom).obj JK :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (f.localizedPullbackToposSquare W).app (K.X i))
      (fun i j _ ↦ ((f.localizedPullbackToposSquare W).hom.naturality (K.d i j)).symm)
  refine ef ≪≫ DerivedCategory.Q.mapIso eSq.symm ≪≫ ?_
  refine ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj W)).mapDerivedCategoryFactors.app
      ((pullbackComplex f.toRingedToposSiteHom).obj K)).symm ≪≫ ?_
  exact (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj W)).mapDerivedCategory.mapIso
    (eg.symm ≪≫ (derivedPullback f.toRingedToposSiteHom).mapIso eK)

omit [(X.J.over (f.u.obj W)).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Y.J.over W).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The derived localization square of Stacks 04J0**, in the form in which the two sites are
assumed to have finite limits and `u` to preserve them. This is the special case of
`AlgebraicGeometry.RingedSite.Hom.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits`, which
needs none of the three classes. -/
theorem Hom.nonempty_derivedPullbackLocalizedIso
    [HasFiniteLimits Y.C] [HasFiniteLimits X.C] [PreservesFiniteLimits f.u]
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Y).O))) :
    Nonempty ((derivedPullback (f.localized W).toRingedToposSiteHom).obj
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W).mapDerivedCategory.obj E) ≅
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj W)).mapDerivedCategory.obj
        ((derivedPullback f.toRingedToposSiteHom).obj E)) :=
  f.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits W E

end AlgebraicGeometry.RingedSite

end
