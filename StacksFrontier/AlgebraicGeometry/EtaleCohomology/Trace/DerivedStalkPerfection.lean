module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatStalk
public import StacksFrontier.Homology.Perfect.LargeUniverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived étale stalk and the perfection of the stalks of a coefficient complex

The étale stalk at a geometric point is an exact functor on sheaves of `Λ`-modules over any
coefficient ring `Λ`, so it induces a functor on unbounded derived categories, the *derived
stalk* `D(X_étale, Λ) ⥤ D(Λ)`.  With that in hand the perfection of the stalks of an object of
`D(X_étale, Λ)` becomes a statement about the object and not about a chosen complex
representing it: if the object is represented by a bounded complex of constructible flat sheaves
of `Λ`-modules then its derived stalk at every geometric point is a perfect complex of
`Λ`-modules.

## Main definitions

* `AlgebraicGeometry.derivedEtaleModuleStalkFunctor` — the derived stalk
  `D(X_étale, Λ) ⥤ D(Λ)` at a geometric point.
* `AlgebraicGeometry.derivedEtaleModuleStalkEndo` — the endomorphism of the derived stalk
  functor induced by an endomorphism of the stalk functor.

## Main results

* `AlgebraicGeometry.etaleModuleStalkFunctor_additive`,
  `AlgebraicGeometry.preservesFiniteLimits_etaleModuleStalkFunctor` and
  `AlgebraicGeometry.preservesFiniteColimits_etaleModuleStalkFunctor` — exactness of the étale
  module stalk functor, in the instance form the derived construction consumes.
* `AlgebraicGeometry.derivedEtaleModuleStalk_isPerfect_of_isRepresentedByConstructibleFlatComplex`
  — the derived stalk of an object of `D(X_étale, Λ)` satisfying condition (2) of
  [Stacks, Tag 03TT] is a perfect complex of `Λ`-modules.
* `AlgebraicGeometry.aB5OfSize_moduleCat_of_univLE` — the exactness of filtered colimits that
  the left-exactness half asks for, at every module universe containing the universe of the
  site.

## Implementation notes

**Exactness comes from Mathlib's points of a site.**  `AlgebraicGeometry.etaleModuleStalkFunctor`
is, by definition, the fibre functor `CategoryTheory.GrothendieckTopology.Point.sheafFiber` of
the point `AlgebraicGeometry.geometricSitePoint` of the small étale site: both are the
composition of `CategoryTheory.sheafToPresheaf` with the colimit over the category of elements of
the fibre.  Mathlib proves that a fibre functor preserves finite limits and finite colimits, so
nothing about stalks has to be redone here; additivity is read off the two factors, the inclusion
of the sheaves and the colimit, and needs neither.

The left-exactness half asks that filtered colimits of size `u` in `ModuleCat.{w} Λ` be exact,
`CategoryTheory.AB5OfSize.{u, u}`; `ModuleCat.{w} Λ` has it natively at `u = w` and in general
whenever the site universe is no larger than the module universe, by
`CategoryTheory.AB5OfSize_of_univLE`.  The right-exactness half asks for limits of size `u`,
which is what the skyscraper sheaf adjoint to the stalk needs.  Both sizes are those of the
small étale site, independently of the universes of the modules and of the coefficient ring.

**The coefficient ring is arbitrary.**  Nothing here multiplies two scalars: the stalk is a
colimit of modules of sections and the perfection input,
`AlgebraicGeometry.stalk_isPerfect_of_isConstructibleFlatModuleSheaf`, is stated for an arbitrary
ring.  This is the generality the trace formula works in, where `Λ` is a finite and possibly
noncommutative ring such as the group ring `(ℤ/ℓⁿℤ)[G]` of a finite group.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w r

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]

/-- The left-exactness input below, exactness of filtered colimits of the size of the small
étale site, holds whenever that size is at most the module universe — in particular at the
coefficient universe `max (u + 1) r` this chapter works in.  Filtered colimits in
`ModuleCat.{w} Λ` are exact at their own size, `CategoryTheory.AB5`, and
`CategoryTheory.AB5OfSize_of_univLE` shrinks that to any smaller size. -/
@[sga "3 I 3.1.1" "special case"]
public theorem aB5OfSize_moduleCat_of_univLE (Λ' : Type r) [Ring Λ'] [UnivLE.{u, w}]
    [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ')] :
    AB5OfSize.{u, u} (ModuleCat.{w} Λ') := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{w} := AB5OfSize_of_univLE.{u, u, w, w} _
  refine ⟨fun J _ _ => ?_⟩
  exact HasExactColimitsOfShape.domain_of_functor J
    (forget₂ (ModuleCat.{w} Λ') AddCommGrpCat.{w})

/-! ### Exactness of the étale module stalk -/

/-- **The étale module stalk functor is additive.**  It is the inclusion of the sheaves followed
by the colimit over the category of pointed étale neighbourhoods, and both of those are
additive. -/
instance etaleModuleStalkFunctor_additive (s : GeometricPoint X.obj) :
    (etaleModuleStalkFunctor B X Λ s).Additive :=
  have : (etaleStalkPresheafFunctor B X.obj X.property s (ModuleCat.{w} Λ)).Additive :=
    inferInstanceAs
      (elementColimit (geometricPointFiber B X.obj X.property s) (ModuleCat.{w} Λ)).Additive
  inferInstanceAs (sheafToPresheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ) ⋙
    etaleStalkPresheafFunctor B X.obj X.property s (ModuleCat.{w} Λ)).Additive

/-- **The étale module stalk functor is left exact.**  It is the fibre functor of the point
`AlgebraicGeometry.geometricSitePoint` of the small étale site, and the fibre functor at a point
of a site preserves finite limits once filtered colimits of the size of the site are exact in the
target. -/
instance preservesFiniteLimits_etaleModuleStalkFunctor
    [AB5OfSize.{u, u} (ModuleCat.{w} Λ)] (s : GeometricPoint X.obj) :
    PreservesFiniteLimits (etaleModuleStalkFunctor B X Λ s) :=
  have : HasFiniteLimits (ModuleCat.{w} Λ) := inferInstance
  inferInstanceAs
    (PreservesFiniteLimits ((geometricSitePoint B X s).sheafFiber (A := ModuleCat.{w} Λ)))

/-- **The étale module stalk functor is right exact.**  It is the fibre functor of the point
`AlgebraicGeometry.geometricSitePoint` of the small étale site, which is left adjoint to the
skyscraper sheaf and so preserves all colimits. -/
instance preservesFiniteColimits_etaleModuleStalkFunctor
    [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)] (s : GeometricPoint X.obj) :
    PreservesFiniteColimits (etaleModuleStalkFunctor B X Λ s) :=
  inferInstanceAs
    (PreservesFiniteColimits ((geometricSitePoint B X s).sheafFiber (A := ModuleCat.{w} Λ)))

/-! ### The derived stalk -/

variable [AB5OfSize.{u, u} (ModuleCat.{w} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)]

/-- **The derived stalk at a geometric point**: the functor
`D(X_étale, Λ) ⥤ D(Λ)` induced by the exact stalk functor.  It is an abbreviation, so that the
properties of `CategoryTheory.Functor.mapDerivedCategory` — that it is triangulated, and that it
is computed on a complex by taking stalks degreewise,
`CategoryTheory.Functor.mapDerivedCategoryFactors` — apply to it with no unfolding. -/
public abbrev derivedEtaleModuleStalkFunctor (s : GeometricPoint X.obj) :
    DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ⥤
      DerivedCategory (ModuleCat.{w} Λ) :=
  (etaleModuleStalkFunctor B X Λ s).mapDerivedCategory

/-- The derived stalk of a cochain complex of sheaves of `Λ`-modules is the stalk complex: the
instance of `CategoryTheory.Functor.mapDerivedCategoryFactors` for the stalk functor. -/
public def derivedEtaleModuleStalkObjQIso (s : GeometricPoint X.obj)
    (K : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ) :
    (derivedEtaleModuleStalkFunctor B X Λ s).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (etaleModuleStalkComplex B X Λ s K) :=
  (etaleModuleStalkFunctor B X Λ s).mapDerivedCategoryFactors.app K

/-- **An endomorphism of the stalk functor induces one of the derived stalk functor.**  The
degreewise endomorphism of stalk complexes inverts no quasi-isomorphism, so it descends along the
localization that defines the derived category. -/
public def derivedEtaleModuleStalkEndo (s : GeometricPoint X.obj)
    (τ : etaleModuleStalkFunctor B X Λ s ⟶ etaleModuleStalkFunctor B X Λ s) :
    derivedEtaleModuleStalkFunctor B X Λ s ⟶ derivedEtaleModuleStalkFunctor B X Λ s :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) (ComplexShape.up ℤ))
    ((etaleModuleStalkFunctor B X Λ s).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    ((etaleModuleStalkFunctor B X Λ s).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    (derivedEtaleModuleStalkFunctor B X Λ s) (derivedEtaleModuleStalkFunctor B X Λ s)
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ))
      DerivedCategory.Q)

omit [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)] in
/-- The induced endomorphism of the derived stalk is, on the class of a cochain complex, the
degreewise endomorphism of its stalk complex, read through
`AlgebraicGeometry.derivedEtaleModuleStalkObjQIso`. -/
public theorem derivedEtaleModuleStalkEndo_app_Q (s : GeometricPoint X.obj)
    (τ : etaleModuleStalkFunctor B X Λ s ⟶ etaleModuleStalkFunctor B X Λ s)
    (K : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) ℤ) :
    (derivedEtaleModuleStalkEndo B X Λ s τ).app (DerivedCategory.Q.obj K) =
      (derivedEtaleModuleStalkObjQIso B X Λ s K).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
        (derivedEtaleModuleStalkObjQIso B X Λ s K).inv := by
  simp only [derivedEtaleModuleStalkEndo, derivedEtaleModuleStalkObjQIso,
    Localization.liftNatTrans_app, Localization.Lifting.iso]
  rfl

/-! ### Perfection of the derived stalk -/

/-- **The derived stalk of an object of `D_ctf(X_étale, Λ)` is perfect.**  For an object of
`D(X_étale, Λ)` represented by a bounded complex of constructible flat sheaves of `Λ`-modules —
condition (2) of [Stacks, Tag 03TT] — the derived stalk at every geometric point is a perfect
complex of `Λ`-modules.

The stalk functor is exact, so the derived stalk of the object is the stalk complex of the
representing complex; and the stalk complex of a bounded complex of constructible flat sheaves is
perfect, by
`AlgebraicGeometry.stalk_isPerfect_of_isConstructibleFlatModuleSheaf`. -/
public theorem derivedEtaleModuleStalk_isPerfect_of_isRepresentedByConstructibleFlatComplex
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)))
    (hK : Stacks.EtaleCohomology.IsRepresentedByConstructibleFlatComplex B X Λ K)
    (s : GeometricPoint X.obj) :
    StacksDraft.Perfect.IsPerfect
      ((derivedEtaleModuleStalkFunctor B X Λ s).obj K) := by
  obtain ⟨C, a, b, hGE, hLE, hflat, ⟨e⟩⟩ := hK
  exact StacksDraft.Perfect.isPerfect_of_iso
    ((derivedEtaleModuleStalkFunctor B X Λ s).mapIso e.symm ≪≫
      derivedEtaleModuleStalkObjQIso B X Λ s C)
    (stalk_isPerfect_of_isConstructibleFlatModuleSheaf B X Λ C ⟨⟨a, hGE⟩, ⟨b, hLE⟩⟩ hflat s)

end AlgebraicGeometry

end
