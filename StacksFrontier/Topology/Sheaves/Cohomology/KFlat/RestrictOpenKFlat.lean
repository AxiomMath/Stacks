module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestrictOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictOpenExactness

/-!
# Restriction to an open subspace preserves K-flatness

Let `(W, 𝒪_W)` be a ringed space and `U ⊆ W` open. If `K` is a K-flat complex of
`𝒪_W`-modules then `K|_U` is a K-flat complex of `𝒪_U`-modules. This is [Stacks, Tag 06YC] —
the degreewise pullback of a K-flat complex is K-flat — read at restriction to an open
subspace, which is the one shape of pullback not otherwise covered: 06YC is proved as
`Stacks.Cohomology.DerivedPullbackTensor.kFlat_modulePullback` for
`RingedSpaceModuleAdjunction.modulePullback` of an arbitrary morphism of ringed spaces, and
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` is a different functor, isomorphic to
the pullback along the open immersion but not equal to it. For restriction to a *slice* of a
ringed site, `StacksFrontier/CategoryTheory/Sites/Cohomology/KFlat/RestrictionToSlice.lean` has
only the resolution-level statement — the restriction of the colimit presentation produced by
Stacks 06YS is K-flat — and records that the unrestricted transport is unavailable there,
because the acyclic complexes on `C/U` are not the restrictions of the acyclic complexes on
`C`. The stalk criterion is what replaces that argument here, and it is available only for a
ringed space.

## Main results

* `Stacks.Cohomology.RestrictOpenKFlat.kFlat_moduleRestriction`: **[Stacks, Tag 06YC] for
  restriction to an open subspace.**
* `Stacks.Cohomology.RestrictOpenKFlat.restrictStalkComplexIso`: the stalk complex of a
  restriction is the stalk complex, with its scalars restricted along the comparison of the two
  stalk rings.
* `Stacks.Cohomology.RestrictOpenKFlat.kFlat_of_iso`: K-flatness of a complex of modules is
  invariant under isomorphism of complexes. The tree had this only privately or buried in the
  inverse-system development.

## Implementation notes

The proof is the stalk criterion for K-flatness ([Stacks, Tag 06YB],
`Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise`) in both directions, with
nothing in between but a change of rings: a point of `U` is a point of `W`, the stalk of `K|_U`
there is the stalk of `K`, and the two stalk rings are isomorphic rather than equal — the
comparison being `AlgebraicGeometry.RingedSpace.restrictModulesStalkRingIso`, whose
module-level form is the natural isomorphism
`AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso`. Restriction of scalars along a ring
isomorphism preserves K-flatness, which is
`AlgebraicGeometry.kFlat_restrictScalars_ringEquiv`. This is the same argument
`AlgebraicGeometry.kFlat_modulesStalkFunctor` makes for a scheme's stalk, and no step of it is
new; what is new is that it is made for the restriction functor.

Four kinds of instance have to be seated by hand, none of them new mathematics.

* `(⊗_{𝒪_U})`-additivity and the existence of the total tensor complex on the open subspace.
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_additive` and its two
  companions are instances for *every* ringed space, and `restrictToOpen W U` is one, but
  instance search does not find them at that argument; they are applied explicitly here.
* `Additive` of the stalk functor of the open subspace at the
  `Stacks.SheafOfModules.Tensor.ringSheaf` spelling, and commutativity of the stalk ring there.
  Both exist for every ringed space and are not found at `restrictToOpen W U`; without the
  second, the `CommRing` instance that `CochainComplex.KFlat` takes over the stalk of `𝒪_U` is
  simply absent, and the right-hand side of the stalk criterion cannot be written there.
* `Additive` of `ModuleCat.restrictScalars` along the stalk-ring comparison. Mathlib has this
  instance for every ring map, and it is not found here either — the two stalk rings carry both
  a `RingCat`-derived and a `CommRing`-derived `Ring` instance, definitionally equal but not
  syntactically so. It is proved outright instead: restriction of scalars does not change the
  underlying map of a morphism, so additivity is `rfl`.

No `@[stacks 06YC]` attribute is added: the tag is already carried, by
`Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional`, for pullback along an
arbitrary morphism of ringed spaces, of which this is the case of an open immersion in a
different spelling of the functor.

## References

* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.Cohomology.RestrictOpenKFlat

/-! ### K-flatness of complexes of modules transports along an isomorphism -/

/-- **K-flatness of a complex of `A`-modules is invariant under isomorphism of complexes.**
Stated here because the only forms of it in the tree are private
(`StacksFrontier/Homology/KFlat/FilteredResolution.lean`) or buried in the inverse-system
development. The total tensor complex is written as the composite of
`Functor.mapBifunctorHomologicalComplex` with `HomologicalComplex₂.totalFunctor` rather than as
the monoidal product, so that no monoidal structure on `CochainComplex (ModuleCat A) ℤ` has to
be in scope. -/
theorem kFlat_of_iso {A : Type u} [CommRing A]
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ} (e : P ≅ Q) (hP : P.KFlat) : Q.KFlat := by
  intro M hM
  let F := (((MonoidalCategory.curriedTensor
      (ModuleCat.{u} A)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj M) ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  exact HomologicalComplex.Acyclic.of_iso (F.mapIso e) (hP M hM)

variable (W : RingedSpace.{u, u}) (U : Opens W.carrier)

/-! ### The tensor product on the open subspace -/

/-- `⊗_{𝒪_U}` is additive in its first variable.
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_additive` is this for every
ringed space; instance search does not find it at `restrictToOpen W U`. -/
instance sheafTensor_additive_restrictToOpen :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (restrictToOpen W U).sheaf).Additive :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_additive (restrictToOpen W U)

/-- `M ⊗_{𝒪_U} -` is additive. See
`Stacks.Cohomology.RestrictOpenKFlat.sheafTensor_additive_restrictToOpen`. -/
instance sheafTensor_obj_additive_restrictToOpen
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      (restrictToOpen W U).sheaf)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (restrictToOpen W U).sheaf).obj
      M).Additive :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_obj_additive
    (restrictToOpen W U) M

/-- The total tensor complex of two complexes of `𝒪_U`-modules exists. See
`Stacks.Cohomology.RestrictOpenKFlat.sheafTensor_additive_restrictToOpen`. -/
instance hasMapBifunctor_sheafTensor_restrictToOpen
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      (restrictToOpen W U).sheaf)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (restrictToOpen W U).sheaf)
      (ComplexShape.up ℤ) :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.hasMapBifunctor_sheafTensor
    (restrictToOpen W U) K L

/-! ### The two stalk rings -/

/-- `AlgebraicGeometry.RingedSpace.commRing_stalk_tensorRingSheaf` at the open subspace.
Without it the `CommRing` instance that `CochainComplex.KFlat` and
`AlgebraicGeometry.kFlat_restrictScalars_ringEquiv` take over the stalk of `𝒪_U` is simply not
found at the spelling `AlgebraicGeometry.SheafOfModules.stalkComplex` produces. -/
instance commRing_stalk_restrictToOpen (z : (restrictToOpen W U).carrier) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (restrictToOpen W U).sheaf).obj z)) :=
  AlgebraicGeometry.RingedSpace.commRing_stalk_tensorRingSheaf (restrictToOpen W U) z

/-- **The comparison of the stalk rings as a ring equivalence**: for `y ∈ U` the stalk of
`𝒪_U` at `y` is the stalk of `𝒪_W` at `y`. This is
`AlgebraicGeometry.RingedSpace.restrictModulesStalkRingIso`, an isomorphism in `RingCat`, read
as a `RingEquiv` so that `AlgebraicGeometry.kFlat_restrictScalars_ringEquiv` applies to it. -/
abbrev restrictStalkRingEquiv {y : W.carrier} (hy : y ∈ U) :
    ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
          (restrictToOpen W U).sheaf).obj ⟨y, hy⟩) ≃+*
      ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf).obj y) :=
  (AlgebraicGeometry.RingedSpace.restrictModulesStalkRingIso W U hy).ringCatIsoToRingEquiv

/-- **Restriction of scalars along the stalk-ring comparison is additive.** Mathlib has this
for every ring map, and it is not found here: the two stalk rings carry a `RingCat`-derived and
a `CommRing`-derived `Ring` instance which are definitionally but not syntactically equal.
Restriction of scalars leaves the underlying map of a morphism alone, so additivity is `rfl`. -/
instance additive_restrictScalars_restrictStalk {y : W.carrier} (hy : y ∈ U) :
    (ModuleCat.restrictScalars.{u} (restrictStalkRingEquiv W U hy).toRingHom).Additive :=
  ⟨fun {_ _ _ _} => rfl⟩

/-- `AlgebraicGeometry.RingedSpace.additive_stalkFunctor_tensorRingSheaf` at the open subspace,
which instance search does not find there — the same failure as for
`Stacks.Cohomology.RestrictOpenKFlat.sheafTensor_additive_restrictToOpen`. -/
instance additive_stalkFunctor_restrictToOpen (z : (restrictToOpen W U).carrier) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (restrictToOpen W U).sheaf) z).Additive :=
  AlgebraicGeometry.RingedSpace.additive_stalkFunctor_tensorRingSheaf (restrictToOpen W U) z

/-! ### The stalk complex of a restriction -/

/-- **The stalk complex of a restriction is the stalk complex with restricted scalars**:
for `y ∈ U`, `(K|_U)_y` is `K_y` read over `𝒪_{U,y}` along the comparison
`Stacks.Cohomology.RestrictOpenKFlat.restrictStalkRingEquiv` of the two stalk rings.

It is `AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso` applied in each degree; the
commutation with the differentials is that isomorphism's naturality. -/
def restrictStalkComplexIso {y : W.carrier} (hy : y ∈ U)
    (K : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf)) ℤ) :
    AlgebraicGeometry.SheafOfModules.stalkComplex (restrictToOpen W U).sheaf ⟨y, hy⟩
        (((moduleRestriction W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((ModuleCat.restrictScalars.{u}
          (restrictStalkRingEquiv W U hy).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (AlgebraicGeometry.SheafOfModules.stalkComplex W.sheaf y K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso W U hy).app (K.X i))
    (fun i j _ => ((AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso
      W U hy).hom.naturality (K.d i j)).symm)

/-! ### Stacks 06YC for restriction to an open subspace -/

/-- **[Stacks, Tag 06YC] for restriction to an open subspace.** The restriction to an open
`U ⊆ W` of a K-flat complex of `𝒪_W`-modules is a K-flat complex of `𝒪_U`-modules.

Both directions of the stalk criterion [Stacks, Tag 06YB] are used, and between them there is
only a change of rings: a point of `U` is a point of `W`, the stalk complex of `K|_U` there is
the stalk complex of `K` with its scalars restricted along the comparison of the two stalk
rings (`Stacks.Cohomology.RestrictOpenKFlat.restrictStalkComplexIso`), and restriction of
scalars along a ring isomorphism preserves K-flatness
(`AlgebraicGeometry.kFlat_restrictScalars_ringEquiv`). -/
theorem kFlat_moduleRestriction
    (K : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat.{u, u, u} W.sheaf K) :
    Stacks.SheafOfModules.KFlat.{u, u, u} (restrictToOpen W U).sheaf
      (((moduleRestriction W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise (restrictToOpen W U).sheaf
    (((moduleRestriction W U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).2 (by
      intro z
      have h := (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise
        W.sheaf K).1 hK z.1
      have h2 := @AlgebraicGeometry.kFlat_restrictScalars_ringEquiv
        (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf).obj z.1))
        (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
            (restrictToOpen W U).sheaf).obj z))
        (AlgebraicGeometry.RingedSpace.commRing_stalk_tensorRingSheaf W z.1)
        (AlgebraicGeometry.RingedSpace.commRing_stalk_tensorRingSheaf (restrictToOpen W U) z)
        (restrictStalkRingEquiv W U z.2) _ h
      exact kFlat_of_iso (restrictStalkComplexIso W U z.2 K).symm h2)

end Stacks.Cohomology.RestrictOpenKFlat

end
