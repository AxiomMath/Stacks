module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingKernelStalkChase
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkUniverseLift

/-!
# The square of Stacks 0AEX in the category where Stacks 0AER lives

The step the source of Stacks 0AF0 marks "(omitted)" pastes two cartesian squares: the one of
Stacks 0AEX, which is a square of `𝒪_X`-modules read at a geometric module stalk, and the one of
Stacks 0AER, which is a square of geometric stalks of *abelian sheaves*.  The two live in
different categories, and at different universes: the geometric stalk of an abelian sheaf on the
small étale site is a filtered colimit over a neighbourhood category whose objects sit one
universe above the sections, so it exists only in `AddCommGrpCat.{u + 1}`, whereas the module
sections are at `u`.

This file puts the first square in the category of the second.  The reading of an `𝒪_X`-module as
an abelian group at `u + 1` — forget the module structure, lift the coefficients, take the
geometric stalk — is left exact, because
`AlgebraicGeometry.Space.geometricModuleStalkCompUliftIso` identifies it with the geometric module
stalk at `u` followed by two functors that are left exact for free; so it carries the square of
Stacks 0AEX across.

## Main results

* `AlgebraicGeometry.Space.moduleAbelianStalk`: an `𝒪_X`-module read as an abelian group at
  `u + 1`, namely its underlying abelian sheaf with the coefficients lifted, taken at a geometric
  stalk.  This is the functor in which both squares of the omitted chase can be compared.
* `AlgebraicGeometry.Space.preservesFiniteLimits_moduleAbelianStalk`: that reading is left exact.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel_moduleAbelianStalk`:
  **the square of Stacks 0AEX, at a glueing triple and a geometric point, as a cartesian square
  of abelian groups at `u + 1`** — the universe and the category of Stacks 0AER.
* `AlgebraicGeometry.Space.FormalGlueingSituation.V_eq_openComplementPreimage` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.spaceV_eq_openComplementPreimageSpace`: the
  open complement `V = Y ∖ f^{-1}Z` of Situation 0AEV is the one Stacks 0AER is stated over.
  The two are built by different constructions and are not definitionally equal.

## Implementation notes

The left exactness is taken from the module stalk rather than factor by factor: of the three
factors, `SheafOfModules.toSheaf` and `AlgebraicGeometry.Space.smallEtaleAbelianStalk` have
`CategoryTheory.Limits.PreservesFiniteLimits` instances, but the middle one — the universe lift of
the coefficients — does not, only
`AlgebraicGeometry.Space.preservesLimitsOfShape_sheafCompose_uliftFunctor` for one finite shape at
a time.  Going through `AlgebraicGeometry.Space.geometricModuleStalkCompUliftIso` avoids that: the
geometric module stalk at `u` is exact as the fibre at a point of a site, and the two functors
after it — the forgetful functor of a module category and the universe lift of abelian groups —
are left exact by instance search, so the composite is, and the comparison isomorphism transports
that.

The transport is `apply`, not a term: elaborated as a term,
`CategoryTheory.Limits.preservesFiniteLimits_of_natIso` fixes its source functor only after its
own instance argument has been searched for, so the search runs against a metavariable and fails
even with the composite's left exactness already in context.  Under `apply` the source is known
first and the search succeeds; `CategoryTheory.Limits.comp_preservesFiniteLimits` then needs no
mention, being what that search finds.

What is still owed to finish the omitted chase is the identification of the bottom row of the
square below with the top row of the square of Stacks 0AER, for which see the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/FormalGlueingKernelStalkChase.lean`.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 0AER](https://stacks.math.columbia.edu/tag/0AER)
* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
* [Stacks Project, Tag 04K1](https://stacks.math.columbia.edu/tag/04K1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An `𝒪_X`-module read as an abelian group at the universe of the abelian geometric stalk.**
The underlying abelian sheaf of an `𝒪_X`-module, its coefficients lifted from the universe `u` of
the module sections to `u + 1`, taken at the geometric stalk at `x`.

This is the functor in which a square of `𝒪_X`-modules and a square of geometric stalks of
abelian sheaves can be compared: the geometric module stalk of
`AlgebraicGeometry.Space.geometricModuleStalkFunctor` lives at `u` and the abelian one of
`AlgebraicGeometry.Space.smallEtaleAbelianStalk` only from `u + 1` upwards, and
`AlgebraicGeometry.Space.geometricModuleStalkCompUliftIso` says that this composite is the first
followed by the lift. -/
def moduleAbelianStalk (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X) ⋙
    sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
      smallEtaleAbelianStalk B S hS x

/-- **Reading an `𝒪_X`-module as an abelian group at `u + 1` is left exact.**  By
`AlgebraicGeometry.Space.geometricModuleStalkCompUliftIso` the composite is the geometric module
stalk at `u` — exact, being the fibre at a point of a site — followed by the forgetful functor of
a module category and the universe lift of abelian groups, both left exact. -/
instance preservesFiniteLimits_moduleAbelianStalk (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) :
    PreservesFiniteLimits (moduleAbelianStalk B S hS X x) := by
  apply preservesFiniteLimits_of_natIso
    (geometricModuleStalkCompUliftIso B S hS X (structureRingSheaf B S hS X) x)

namespace FormalGlueingSituation

variable {B S hS}

/-- **The square of Stacks 0AEX as a cartesian square of abelian groups at `u + 1`.**  At a
glueing triple `t` and a geometric point `x̄` of `X`, the square
```
Ker(j_*ℋ ⊕ f_*𝒢 ⟶ (f ∘ j')_*𝒢|_V)_x̄  ⟶  (j_*ℋ)_x̄
              ↓                               ↓
         (f_*𝒢)_x̄             ⟶    ((f ∘ j')_*𝒢|_V)_x̄
```
of abelian groups at `u + 1` is cartesian.

This is
`AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel_app` carried across
`AlgebraicGeometry.Space.moduleAbelianStalk`, which is left exact.  It is the left-hand square of
the diagram chase the source of Stacks 0AF0 omits, now in the category and at the universe where
the right-hand square — `AlgebraicGeometry.Space.isPullback_directImageStalkMap`, which is
Stacks 0AER — lives, so that the two can be pasted by
`CategoryTheory.IsPullback.paste_vert` once their shared row is identified. -/
theorem isPullback_glueingKernel_moduleAbelianStalk (D : FormalGlueingSituation B S hS)
    (x : GeometricPoint B S hS D.spaceX.1) (t : D.moduleGlueingComma) :
    IsPullback ((moduleAbelianStalk B S hS D.spaceX x).map (D.glueingKernelFst.app t))
      ((moduleAbelianStalk B S hS D.spaceX x).map (D.glueingKernelSnd.app t))
      ((moduleAbelianStalk B S hS D.spaceX x).map (D.restrictionOverlapMap.app t))
      ((moduleAbelianStalk B S hS D.spaceX x).map (D.ambientOverlapMap.app t)) :=
  (D.isPullback_glueingKernel_app t).map (moduleAbelianStalk B S hS D.spaceX x)

/-- **The `V` of Situation 0AEV is the `V` of Stacks 0AER.**  In Situation 0AEV the open
complement `V = Y ∖ f^{-1}Z` is built as `AlgebraicGeometry.Space.openComplement` of the
inverse image of `Z` — the subfunctor of sections whose restrictions into `f^{-1}Z` are over
empty schemes — whereas Stacks 0AER builds it as
`AlgebraicGeometry.Space.openComplementOfClosedSubspace`, the open subspace that part (1) of
Stacks 03BZ attaches to the complement of the point set of `f^{-1}Z`.  The two constructions
agree.

They are *not* definitionally equal, and the identification is needed before the two squares of
the omitted chase of Stacks 0AF0 can be compared: the square of Stacks 0AEX is built from
`AlgebraicGeometry.Space.FormalGlueingSituation.openImmersionOver`, the inclusion of the first
`V`, and the square of Stacks 0AER from
`AlgebraicGeometry.Space.openComplementPreimageι`, the inclusion of the second.

Both subfunctors are open subspaces with the same point set — the complement of the point set of
`f^{-1}Z`, by `AlgebraicGeometry.Space.range_pointsMap_ι_openComplement` on one side and
`AlgebraicGeometry.Space.subspacePointSet_openComplement` on the other — and an open subspace is
determined by its point set, which is the antisymmetry of
`AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset`. -/
theorem V_eq_openComplementPreimage (D : FormalGlueingSituation B S hS) :
    D.V = (openComplementOfClosedSubspace B S hS D.spaceY
      ⟨D.Z.preimage D.ambientMorphism.hom,
        isClosedSubspace_preimage B S hS D.ambientMorphism.hom D.Z
          D.spaceX.property D.spaceY.property D.closed_Z⟩).1 := by
  set W : OpenSubspaces B S hS D.spaceY.1 :=
    openComplementOfClosedSubspace B S hS D.spaceY
      ⟨D.Z.preimage D.ambientMorphism.hom,
        isClosedSubspace_preimage B S hS D.ambientMorphism.hom D.Z
          D.spaceX.property D.spaceY.property D.closed_Z⟩ with hW
  have hptsL : Set.range (pointsMap B S hS D.V.toFunctor D.V.ι) =
      (Set.range (pointsMap B S hS (D.Z.preimage D.f).toFunctor (D.Z.preimage D.f).ι))ᶜ := by
    rw [D.V_eq_openComplement_preimage]
    exact range_pointsMap_ι_openComplement B S hS _
  have hptsR : Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) =
      (Set.range (pointsMap B S hS (D.Z.preimage D.f).toFunctor (D.Z.preimage D.f).ι))ᶜ := by
    rw [hW]
    exact subspacePointSet_openComplement B S hS D.spaceY _
  have hpts : Set.range (pointsMap B S hS D.V.toFunctor D.V.ι) =
      Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) := hptsL.trans hptsR.symm
  exact le_antisymm (le_of_range_pointsMap_ι_subset B S hS W.2 hpts.le)
    (le_of_range_pointsMap_ι_subset B S hS D.isOpenSubspace_V hpts.ge)

/-- **The `V` of Situation 0AEV is the `V` of Stacks 0AER, as algebraic spaces.**
`AlgebraicGeometry.Space.FormalGlueingSituation.V_eq_openComplementPreimage` read at the level of
the algebraic space the two subfunctors present: the source of
`AlgebraicGeometry.Space.FormalGlueingSituation.openImmersionOver`, which the square of
Stacks 0AEX is built from, is the source of `AlgebraicGeometry.Space.openComplementPreimageι`,
which the square of Stacks 0AER is built from.  Being an algebraic space is a property, so the
two objects are equal as soon as the functors are. -/
theorem spaceV_eq_openComplementPreimageSpace (D : FormalGlueingSituation B S hS) :
    D.spaceV = openComplementPreimageSpace B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩ := by
  have h : D.V.toFunctor =
      (openComplementPreimageSpace B S hS D.ambientMorphism ⟨D.Z, D.closed_Z⟩).obj :=
    congrArg Subfunctor.toFunctor D.V_eq_openComplementPreimage
  exact ObjectProperty.FullSubcategory.ext h

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
