module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbedding
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedTensorStalk
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula along the inclusion of a closed subset, with no hypothesis

Let `(X, 𝒪_X)` be a ringed space, `Z ⊆ X` a closed subset, and
`i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` the inclusion.  [Stacks, Tag 0B55] says that the
projection-formula map of [Stacks, Tag 0B53]

`Ri_*E ⊗^𝐋_{𝒪_X} K ⟶ Ri_*(E ⊗^𝐋_{𝒪_X|_Z} Li^*K)`

is an isomorphism, for *every* `E` in `D(𝒪_X|_Z)` and `K` in `D(𝒪_X)`.

`Stacks.Cohomology.SupportedComplexes.isIso_projectionFormulaMap_closedSubsetInclusion` proves
this on one hypothesis: that `Ri_*E ⊗^𝐋 K` have its cohomology sheaves supported on `Z`.  This
file discharges that hypothesis and states the conclusion as the source states it.

## Main results

* `AlgebraicGeometry.cohomologySupportedOn_iff_forall_isZero_derivedStalk`: a complex of
  `𝒪`-modules has cohomology supported on `T` exactly when its *derived* stalk vanishes at every
  point outside `T`.  This is the translation between the `AddCommGrpCat`-valued stalk of a
  cohomology sheaf, which `AlgebraicGeometry.CohomologySupportedOn` is phrased with, and the
  `ModuleCat`-valued derived stalk functor.
* `Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIsoGeneral`: **the derived form of
  [Stacks, Tag 01CB] with both tensor factors arbitrary**, extending
  `Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso`, whose second factor is a
  module in degree zero.
* `Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left`: the
  derived tensor product of a complex with cohomology supported on `T` with an *arbitrary*
  complex again has cohomology supported on `T`.
* `cohomologySupportedOn_derivedPushforward_closedSubsetInclusion` in
  `Stacks.Cohomology.SupportedComplexes`: the cohomology sheaves of `Ri_*E` are supported on `Z`.
* `isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed` in the same namespace:
  **[Stacks, Tag 0B55] for the inclusion of a closed subset, with no hypothesis beyond
  closedness of `Z`.**

## Implementation notes

The support statement is proved on stalks, which is where the derived tensor product can be
computed.  For `x ∉ Z`:

* the derived stalk of `Ri_*E` at `x` vanishes.  Its cohomology sheaves are supported on `Z` —
  [Stacks, Tag 0AEF] part (1),
  `Stacks.Cohomology.SupportedComplexes.pushforward_supported`, carried from the functor induced
  on derived categories by the exact functor `i_*` to `Ri_*` along the comparison of
  [Stacks, Tag 0E2K] — and an object of a derived category whose cohomology all vanishes is a
  zero object, which is `CategoryTheory.DerivedCategory.isZero_of_forall_isZero_homology`;
* taking derived stalks carries `⊗^𝐋_{𝒪_X}` to `⊗^𝐋_{𝒪_{X,x}}`, by the derived form of
  [Stacks, Tag 01CB].  The statement in the library,
  `Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso`, has its second factor a
  module placed in degree zero, so `derivedTensorStalkIsoGeneral` below assembles the general
  form from the two-K-flat core `derivedTensorStalkIsoOfKFlat` by the same pattern: replace both
  arguments by the chosen K-flat representatives `kFlatModel` and transport along
  `kFlatModelIso`;
* the derived tensor product of [Stacks, Tag 0BYI] over the stalk ring is exact, hence additive,
  in its first variable, so it takes the vanishing first factor to a zero object.

Both the derived stalk functor and `CohomologySupportedOn` are then read through
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` — the stalk functor is exact, so it
commutes with the cohomology of the derived category — and
`AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff`, which says the stalk of a sheaf
of modules vanishes as a module exactly when it vanishes as an abelian group.

Nothing in `ProjectionFormulaClosedEmbedding.lean` is changed: the conditional theorem is
applied as it stands, with the hypothesis supplied.

**Why the exactness of the stalk functor is handed over as a term here.** Nothing about the
stalk functor is reproved below; each `let` names an instance that already exists —
`AlgebraicGeometry.SheafOfModules.stalkFunctor_additive`,
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits` and
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`, Stacks 01AH — and hands it
to the elaborator where it is wanted.  Each is stated for an opaque sheaf of rings `𝒪`, so its
discrimination-tree key carries `𝒪.obj`; but `Stacks.SheafOfModules.Tensor.ringSheaf` is an
`abbrev` whose body is a `Sheaf` literal, so in `(Stacks.SheafOfModules.Tensor.ringSheaf R).obj`
the projection iota-reduces to `R.obj ⋙ forget₂ CommRingCat RingCat` while the key is computed.
The two keys disagree, so instance *lookup* never offers the instance even though applying it
succeeds — the ambient categories are implicit type arguments of
`CategoryTheory.Functor.Additive` and of `PreservesFiniteLimits`, hence part of the key.  The
`PreservesFiniteColimits` half of exactness then follows from `PreservesColimits` by Mathlib's
generic instance, which is keyed on an arbitrary functor and is retrieved without trouble.

The `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` term is not a spelling problem
but a cost one: that instance is found in about 1500 heartbeats, which is affordable once, but
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct` asks for
`∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive` as a *single* synthesis
goal, and inside that binder the same search is repeated for every candidate tried, spending the
20000-heartbeat budget before any of them is settled.  Named in the local context, synthesis
finds it without search; the heartbeat limits themselves are untouched.  Both readings are
recorded at length in the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedTensorStalk`, which supplies the
same instances the same way at every use.  The third namespace below works over
`AlgebraicGeometry.structureSheafRing`, which is a `def`, so there the key stays `𝒪.obj` and
none of this is needed.

## References

* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u d

/-! ### Vanishing in the derived category -/

namespace CategoryTheory.DerivedCategory

/-- An object of the unbounded derived category with no cohomology is a zero object. -/
lemma isZero_of_forall_isZero_homology {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {E : DerivedCategory C}
    (h : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor C n).obj E)) : IsZero E := by
  have hiso : IsIso (0 : E ⟶ E) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    rw [Functor.map_zero]
    exact ⟨0, by simp [((IsZero.iff_id_eq_zero _).1 (h n))],
      by simp [((IsZero.iff_id_eq_zero _).1 (h n))]⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : E ⟶ E), zero_comp]

end CategoryTheory.DerivedCategory

/-! ### Cohomological support read off the derived stalks -/

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-- **Cohomological support, as vanishing of the derived stalks.** A complex of
`𝒪`-modules has its cohomology sheaves supported on `T` exactly when its derived stalk
vanishes at every point outside `T`. -/
theorem cohomologySupportedOn_iff_forall_isZero_derivedStalk (T : Set X)
    (E : DerivedCategory (SheafOfModules.{u} O)) :
    CohomologySupportedOn O T E ↔ ∀ y : X, y ∉ T →
      IsZero ((SheafOfModules.stalkFunctor O y).mapDerivedCategory.obj E) := by
  refine ⟨fun hE y hy => ?_, fun hE n y hy => ?_⟩
  · refine DerivedCategory.isZero_of_forall_isZero_homology fun n => ?_
    refine IsZero.of_iso ?_ (((SheafOfModules.stalkFunctor O y).mapDerivedCategoryHomologyIso
      n).app E)
    exact (SheafOfModules.isZero_stalkFunctor_obj_iff O y _).2 (hE n y hy)
  · rw [← SheafOfModules.isZero_stalkFunctor_obj_iff O y]
    exact IsZero.of_iso (Functor.map_isZero (DerivedCategory.homologyFunctor _ n) (hE y hy))
      (((SheafOfModules.stalkFunctor O y).mapDerivedCategoryHomologyIso n).app E).symm

end AlgebraicGeometry

/-! ### The derived tensor product of a supported complex -/

namespace Stacks.SheafOfModules.DerivedTensorStalk

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})
  (x : X)

/-- **The derived form of Stacks 01CB for two arbitrary complexes.** Taking stalks carries the
derived tensor product of Stacks 06YU to the canonical derived tensor product of Stacks 0BYI
over the stalk ring, with *both* arguments arbitrary objects of the derived category. -/
def derivedTensorStalkIsoGeneral
    (E F : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R)) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    letI : (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI : Limits.PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI : Limits.PreservesColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
      AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    ((stalkDerivedTensor R x).obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj E)).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj F) ≅
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor.obj E).obj F) :=
  letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  letI : (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  letI : Limits.PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  letI : Limits.PreservesColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  ((stalkDerivedTensor R x).mapIso
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.mapIso
            (kFlatModelIso R E).symm)).app _ ≪≫
    ((stalkDerivedTensor R x).obj _).mapIso
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.mapIso
            (kFlatModelIso R F).symm) ≪≫
    derivedTensorStalkIsoOfKFlat R x (kFlatModel R E) (kFlatModel R F)
      (kFlat_kFlatModel R E) (kFlat_kFlatModel R F) ≪≫
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.mapIso
      (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor.mapIso
          (kFlatModelIso R E)).app _ ≪≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor.obj E).mapIso
          (kFlatModelIso R F))

/-- Tensoring a zero object of `D(Λ)` with anything is zero: the derived tensor product is
exact, hence additive, in its first variable. -/
lemma isZero_derivedTensor_of_isZero_left {Λ : Type u} [CommRing Λ]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct Λ)
    (A B : CochainComplex.DerivedTensor.DObj Λ) (hA : IsZero A) :
    IsZero ((T.tensor.obj A).obj B) := by
  let _ := T.commShift_left B
  let _ := T.exact_left B
  exact Functor.map_isZero (T.tensor.flip.obj B) hA

/-- **The derived tensor product of a complex supported on `T` with an arbitrary complex is
supported on `T`.** Stalkwise this is immediate: the derived stalk of the tensor product is the
tensor product of the derived stalks over the stalk ring (`derivedTensorStalkIsoGeneral`, the
derived form of Stacks 01CB), and the first of them vanishes outside `T`. -/
theorem cohomologySupportedOn_derivedTensor_of_left (T : Set X)
    (A K : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R))
    (hA : AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) T A) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) T
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R).obj A).obj K) := by
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  rw [AlgebraicGeometry.cohomologySupportedOn_iff_forall_isZero_derivedStalk]
  intro y hy
  let : (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y).Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  let : Limits.PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  let : Limits.PreservesColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  refine IsZero.of_iso ?_ (derivedTensorStalkIsoGeneral R y A K).symm
  exact isZero_derivedTensor_of_isZero_left
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct _) _ _
    ((AlgebraicGeometry.cohomologySupportedOn_iff_forall_isZero_derivedStalk _ T A).1 hA y hy)

end Stacks.SheafOfModules.DerivedTensorStalk

/-! ### The projection formula, with no hypothesis -/

namespace Stacks.Cohomology.SupportedComplexes

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

include hZ

/-- **The cohomology sheaves of `Ri_*E` are supported on `Z`.** This is
`pushforward_supported` — Stacks 0AEF part (1) — carried along the comparison of
[Stacks, Tag 0E2K] from the functor induced on derived categories by the exact functor `i_*`
to the total right derived functor `Ri_*`. -/
theorem cohomologySupportedOn_derivedPushforward_closedSubsetInclusion
    (E : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z
      ((derivedPushforward (closedSubsetInclusion X Z)).obj E) := by
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  exact Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso
    (structureSheafRing X) Z
    ((closedSubsetPushforwardComparison X Z hZ).app E)
    (pushforward_supported X Z hZ E)

/-- **The derived tensor product `Ri_*E ⊗^𝐋_{𝒪_X} K` has its cohomology supported on `Z`**, for
every `E` in `D(𝒪_X|_Z)` and every `K` in `D(𝒪_X)`.  This is the hypothesis `hsupp` of
`isIso_projectionFormulaMap_closedSubsetInclusion`, discharged. -/
theorem cohomologySupportedOn_derivedTensor_derivedPushforward_closedSubsetInclusion
    (E : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z))))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z
      (((derivedTensorProductFunctor X.sheaf).obj
        ((derivedPushforward (closedSubsetInclusion X Z)).obj E)).obj K) :=
  Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left
    X.sheaf Z _ K (cohomologySupportedOn_derivedPushforward_closedSubsetInclusion X Z hZ E)

/-- **[Stacks, Tag 0B55] for the inclusion of a closed subset.**  The projection-formula map of
[Stacks, Tag 0B53]

`Ri_*E ⊗^𝐋_{𝒪_X} K ⟶ Ri_*(E ⊗^𝐋_{𝒪_X|_Z} Li^*K)`

is an isomorphism for arbitrary `E` in `D(𝒪_X|_Z)` and `K` in `D(𝒪_X)`, with no hypothesis on
either beyond closedness of `Z`, which is the source's hypothesis that `i` be a homeomorphism
onto a closed subset.

This is `isIso_projectionFormulaMap_closedSubsetInclusion` with its support hypothesis supplied
by `cohomologySupportedOn_derivedTensor_derivedPushforward_closedSubsetInclusion`. -/
/-
The conclusion here is UNCONDITIONAL, as in the source: no support hypothesis, and nothing on `E`
or `K`. The clause records a narrowing of the *hypothesis* instead. [Stacks, Tag 0B55] allows any
morphism of ringed spaces `f : X ⟶ Y` which is a homeomorphism onto a closed subset, whereas this
statement is about `closedSubsetInclusion X Z`, the canonical inclusion carrying the *restricted*
structure sheaf. Those differ: `(pt, k[t]) ⟶ (pt, k)` is a homeomorphism onto a closed subset but
its comorphism is not a restriction, so it is not of this form. The general case needs the
projection formula for an arbitrary such `f`, which is not proved here.
-/
@[stacks 0B55 "for the canonical inclusion of a closed subset, with its restricted structure \
sheaf; the conclusion is unconditional, but the source's hypothesis -- any morphism of ringed \
spaces that is a homeomorphism onto a closed subset -- is narrowed to that inclusion"]
theorem isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed
    (E : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z))))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (projectionFormulaMap (closedSubsetInclusion X Z) E K) :=
  isIso_projectionFormulaMap_closedSubsetInclusion X Z hZ E K
    (cohomologySupportedOn_derivedTensor_derivedPushforward_closedSubsetInclusion X Z hZ E K)

end Stacks.Cohomology.SupportedComplexes

end
