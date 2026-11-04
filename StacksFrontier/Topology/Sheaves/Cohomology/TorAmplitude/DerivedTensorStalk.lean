module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwiseRingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.CanonicalSheafCertificate
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived tensor product and stalks

Taking stalks carries the derived tensor product of Stacks 06YU on a ringed space to the
canonical derived tensor product of Stacks 0BYI over the stalk ring:
`(E ⊗^{L}_{𝒪_X} ℱ)_x ≅ E_x ⊗^{L}_{𝒪_{X,x}} ℱ_x`. This is the derived form of Stacks 01CB, and
it is the one hypothesis that `AlgebraicGeometry.SheafOfModules.hasTorAmplitudeIn_iff_forall_stalk`
— Stacks 09U9 — carries undischarged. Discharging it turns Stacks 09U9 into an unconditional
statement about the canonical derived tensor products on both sides.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorStalk.stalkDerivedTensor`: the canonical derived tensor
  product of Stacks 0BYI over the stalk ring at a point.
* `Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso`: **the derived form of
  Stacks 01CB**, which is the hypothesis `hstalk` of Stacks 09U9.

## Main results

* `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_iff_forall_stalk` is **Stacks 09U9**: the
  Stacks 08CG Tor amplitude of a ringed space, read against the derived tensor product of
  Stacks 06YU, holds in `[a, b]` exactly when it holds at every stalk. This is the covering
  declaration of the tag; it carries no hypothesis.
* `Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeIn_canonical_iff_forall_stalk`: the
  same equivalence in the ringed-site vocabulary, which is where it is proved.
* `AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_canonicalCertified_iff_forall_stalk`: the same
  for the canonical certificate of Stacks 08CG on a ringed space.

## Implementation notes

The proof is the one the source gives. Both arguments are replaced by K-flat complexes
(Stacks 06YS), on which both derived tensor products are total tensor complexes; the stalk of a
K-flat complex is K-flat (Stacks 06YB,
`Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise`), so the comparison of the
stalk-level derived tensor product applies; and the stalk of a total tensor complex is the
total tensor complex of the stalks
(`Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorComplexIso`, which is the underived
Stacks 01CB `Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso` fed through
`AlgebraicGeometry.SheafOfModules.stalkTotalComplexIso`). The stalk functor is exact, so it
descends to the derived categories compatibly with the localization, which is
`CategoryTheory.Functor.mapDerivedCategoryFactors`.

`hstalk` asks only for an isomorphism for each point, object and module, with no naturality or
coherence; so the chosen K-flat representatives may be picked with `Exists.choose` and the two
sides transported along them. No descent of a natural transformation off the K-flat
representatives is needed, and none is proved here.

Everything is stated over a sheaf of commutative rings on `Opens X` — the ringed-site form —
and not over an `AlgebraicGeometry.RingedSpace`, because that is the only spelling in which the
`CommRing` instance on the stalk ring is found by synthesis; the reason is recorded in the
implementation notes of `StacksFrontier.Topology.Sheaves.Modules.StalkTensor`. The ringed-space
consumers at the end apply the site results at `X.sheaf`.

The stalk-level derived category is `CategoryTheory.HasDerivedCategory.standard`, because
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` bakes that model in; the model on
`X` stays a binder.

**Why the exactness of the stalk functor is seated by hand here.** Nothing about the stalk
functor is reproved in this file; every `letI` below names the instance that already exists —
`AlgebraicGeometry.SheafOfModules.stalkFunctor_additive` (in
`StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic`),
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness`) and
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`, Stacks 01AH (in
`StacksFrontier.Topology.Sheaves.Modules.Colimits`) — and hands it to the elaborator as a term.
Each of those is stated for an opaque sheaf of rings `𝒪`, so its discrimination-tree key
carries `𝒪.obj`; but `Stacks.SheafOfModules.Tensor.ringSheaf` is an `abbrev` whose body is a
`Sheaf` literal, so in `(Stacks.SheafOfModules.Tensor.ringSheaf R).obj` the projection
iota-reduces to `R.obj ⋙ forget₂ CommRingCat RingCat` while the key is being computed. The two
keys therefore disagree and instance *lookup* never offers the instance, even though applying
it succeeds — the categories `Mod(𝒪)` and `Mod(𝒪)_x` are implicit *type* arguments of
`CategoryTheory.Functor.Additive` and of `PreservesFiniteLimits`, hence part of the key.
The same statements over a ringed space go through untouched, which is why the two consumers
at the end of the file need none of this: `AlgebraicGeometry.structureSheafOfRings` is a `def`,
so there the key stays `𝒪.obj`.

The `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` seatings are a different
matter and are not a spelling problem: that instance is found in about 1500 heartbeats, but
`Stacks.SheafOfModules.KFlat.KFlat` asks for
`∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive` and for the family of
`HomologicalComplex.HasMapBifunctor`s, and each of those is a *single* synthesis goal inside
whose binder the same search is repeated for every candidate tried; the 20000-heartbeat budget
is spent before any of them is settled. Naming the instance once in the local context, where
synthesis finds it without search, is what keeps the goal inside the budget — the limit itself
is untouched.

## References

* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Lemma 17.16.1 (Tag 01CB)](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u d

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.SheafOfModules.DerivedTensorStalk

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})
  (x : X)

/-- The canonical derived tensor product of Stacks 0BYI over the stalk ring at `x`. -/
def stalkDerivedTensor :
    DerivedCategory (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)) ⥤
      DerivedCategory (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)) ⥤
        DerivedCategory (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)) :=
  (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
    (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)).tensor

/-- The stalk at `x` of a module placed in degree zero is its stalk, placed in degree zero. -/
def stalkSingleIso (F : Stacks.DerivedTensor.RingedSite.Modules R) :
    AlgebraicGeometry.SheafOfModules.stalkComplex R x
        ((CochainComplex.singleFunctor
          (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj F) ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)) 0).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).obj F) :=
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  (HomologicalComplex.singleMapHomologicalComplex
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x) (ComplexShape.up ℤ) 0).app F

section Statement

variable [HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules R)]

/-- The derived stalk functor computes the stalk complex: the stalk functor is exact, so its
derived functor is the degreewise stalk read through the localization. -/
def derivedStalkQIso
    (K : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (AlgebraicGeometry.SheafOfModules.stalkComplex R x K) :=
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  (AlgebraicGeometry.SheafOfModules.stalkFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategoryFactors.app K

/-- Every object of `D(R)` is represented by a K-flat complex: Stacks 06YS. -/
theorem exists_kFlat_representative (E : DerivedCategory
    (Stacks.DerivedTensor.RingedSite.Modules R)) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    ∃ K : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ,
      Stacks.SheafOfModules.KFlat.KFlat R K ∧
        Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  have hes := Localization.essSurj (DerivedCategory.Q
    (C := Stacks.DerivedTensor.RingedSite.Modules R))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
  obtain ⟨K, q, hK, -, hq, -⟩ := Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution R
    (DerivedCategory.Q.objPreimage E)
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  exact ⟨K, hK, ⟨asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-- A chosen K-flat complex representing an object of `D(R)`. -/
def kFlatModel (E : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R)) :
    CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ :=
  (exists_kFlat_representative R E).choose

/-- The chosen representative is K-flat. -/
theorem kFlat_kFlatModel (E : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R)) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    Stacks.SheafOfModules.KFlat.KFlat R (kFlatModel R E) :=
  (exists_kFlat_representative R E).choose_spec.1

/-- The chosen K-flat complex does represent the object. -/
def kFlatModelIso (E : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R)) :
    DerivedCategory.Q.obj (kFlatModel R E) ≅ E :=
  (exists_kFlat_representative R E).choose_spec.2.some

/-- **The derived form of Stacks 01CB, at K-flat representatives.** For K-flat complexes `K`
and `P`, the stalk of the derived tensor product of Stacks 06YU is the derived tensor product
of the stalks over the stalk ring. -/
def derivedTensorStalkIsoOfKFlat
    (K P : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    ∀ (_hK : Stacks.SheafOfModules.KFlat.KFlat R K)
      (_hP : Stacks.SheafOfModules.KFlat.KFlat R P),
    ((stalkDerivedTensor R x).obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj
              (DerivedCategory.Q.obj K))).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj
            (DerivedCategory.Q.obj P)) ≅
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor.obj
          (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj P)) :=
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  fun hK hP =>
  ((stalkDerivedTensor R x).mapIso (derivedStalkQIso R x K)).app _ ≪≫
    ((stalkDerivedTensor R x).obj _).mapIso (derivedStalkQIso R x P) ≪≫
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct _).comparison
      (AlgebraicGeometry.SheafOfModules.stalkComplex R x K)
      (AlgebraicGeometry.SheafOfModules.stalkComplex R x P)
      ((Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise R K).1 hK x)
      ((Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise R P).1 hP x) ≪≫
    (DerivedCategory.Q.mapIso
      (Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorComplexIso R x K P)).symm ≪≫
    (derivedStalkQIso R x
      (((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K).obj P)).symm ≪≫
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.mapIso
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparison
        K P hK hP).symm

/-- The stalk at `x` of a module, placed in degree zero, is the derived stalk of the module
placed in degree zero. -/
def derivedStalkSingleIso (F : Stacks.DerivedTensor.RingedSite.Modules R) :
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    (DerivedCategory.singleFunctor (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)) 0).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).obj F) ≅
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj F) :=
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  (DerivedCategory.Q.mapIso (stalkSingleIso R x F)).symm ≪≫
    (derivedStalkQIso R x
      ((CochainComplex.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj F)).symm

/-- **The derived form of Stacks 01CB.** Taking stalks carries the derived tensor product of
Stacks 06YU to the canonical derived tensor product of Stacks 0BYI over the stalk ring.

This is the hypothesis `hstalk` of Stacks 09U9, discharged for the canonical derived tensor
products on both sides: resolve both arguments by K-flat complexes (Stacks 06YS), on which both
derived tensor products are total tensor complexes, and use that the stalk of a K-flat complex
is K-flat (Stacks 06YB) and that the stalk of a total tensor complex is the total tensor complex
of the stalks. -/
def derivedTensorStalkIso
    (E : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R))
    (F : Stacks.DerivedTensor.RingedSite.Modules R) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    letI := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    ((stalkDerivedTensor R x).obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj E)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).obj F)) ≅
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.obj
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor.obj E).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  let := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  ((stalkDerivedTensor R x).mapIso
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.mapIso
            (kFlatModelIso R E).symm)).app _ ≪≫
    ((stalkDerivedTensor R x).obj _).mapIso (derivedStalkSingleIso R x F ≪≫
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.mapIso
          (kFlatModelIso R
            ((DerivedCategory.singleFunctor
              (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj F)).symm) ≪≫
    derivedTensorStalkIsoOfKFlat R x (kFlatModel R E)
      (kFlatModel R ((DerivedCategory.singleFunctor
        (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj F))
      (kFlat_kFlatModel R E)
      (kFlat_kFlatModel R ((DerivedCategory.singleFunctor
        (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj F)) ≪≫
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapDerivedCategory.mapIso
      (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor.mapIso
          (kFlatModelIso R E)).app _ ≪≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor.obj E).mapIso
          (kFlatModelIso R ((DerivedCategory.singleFunctor
            (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj F)))

/-- **Stacks 09U9, with no hypothesis left.** An object of `D(R)` has Tor amplitude in `[a, b]`
exactly when each of its stalks does, the derived tensor products being the canonical one of
Stacks 06YU on `X` and the canonical one of Stacks 0BYI over each stalk ring.

This is `AlgebraicGeometry.SheafOfModules.hasTorAmplitudeIn_iff_forall_stalk` with its
hypothesis `hstalk` supplied by `derivedTensorStalkIso`. -/
theorem hasTorAmplitudeIn_canonical_iff_forall_stalk
    (E : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules R)) (a b : ℤ) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      inferInstance
    letI := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
    letI := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
    letI := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
    CategoryTheory.DerivedCategory.HasTorAmplitudeIn
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor E a b ↔
      ∀ y : X, CategoryTheory.DerivedCategory.HasTorAmplitudeIn (stalkDerivedTensor R y)
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y).mapDerivedCategory.obj E)
        a b :=
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  let := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  let := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  let := fun (y : X) => AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) y
  AlgebraicGeometry.SheafOfModules.hasTorAmplitudeIn_iff_forall_stalk
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor
    (stalkDerivedTensor R) (fun y E' F => derivedTensorStalkIso R y E' F) E a b

end Statement

end Stacks.SheafOfModules.DerivedTensorStalk

/-! ### The ringed-space consumers -/

namespace AlgebraicGeometry.RingedSpace

open StrictlyPerfect

variable (X : AlgebraicGeometry.RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

-- `HasDerivedCategory` at the spelling of Stacks 06YU: the type is `OXMod X` by `rfl`, but
-- `structureSheafOfRings` is not reducible, so an instance proved at one spelling does not fire
-- at the other. Seated here, not restated.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **Stacks 09U9 at the canonical certificate of Stacks 08CG.** An object of `D(𝒪_X)` has Tor
amplitude in `[a, b]` for the genuine derived tensor product exactly when each of its stalks
has Tor amplitude in `[a, b]` over the stalk ring.

The hypothesis `hstalk` of Stacks 09U9 is supplied by
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso`, the derived form of
Stacks 01CB. -/
theorem hasTorAmplitudeIn_canonicalCertified_iff_forall_stalk
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) :
    (canonicalCertifiedDerivedSheafTensoringOfResolvingComplexes X).HasTorAmplitudeIn E a b ↔
      ∀ x : X.carrier, CategoryTheory.DerivedCategory.HasTorAmplitudeIn
        (Stacks.SheafOfModules.DerivedTensorStalk.stalkDerivedTensor X.sheaf x)
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings X) x
          ).mapDerivedCategory.obj E) a b :=
  CertifiedDerivedSheafTensoring.hasTorAmplitudeIn_iff_forall_stalk
    (canonicalCertifiedDerivedSheafTensoringOfResolvingComplexes X)
    (Stacks.SheafOfModules.DerivedTensorStalk.stalkDerivedTensor X.sheaf)
    (fun y E' F => Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso
      X.sheaf y E' F) E a b

end AlgebraicGeometry.RingedSpace

/-! ### Stacks 09U9 in the Tor-amplitude vocabulary of Stacks 08CG -/

namespace Stacks.Cohomology.TorAmplitude

-- `_root_`-qualified: inside this namespace, `open StrictlyPerfect` would be read as
-- `Stacks.StrictlyPerfect`, which is a different namespace and does not carry `OXMod`.
open _root_.StrictlyPerfect

variable (X : AlgebraicGeometry.RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

attribute [local instance] hasDerivedCategoryModules

/-- **Stacks 09U9.** Let `(X, 𝒪_X)` be a ringed space and `E` an object of `D(𝒪_X)`. Then `E`
has Tor amplitude in `[a, b]` if and only if, for every point `x` of `X`, the stalk `E_x` has
Tor amplitude in `[a, b]` as an object of `D(𝒪_{X, x})`.

Both sides are read against *the* derived tensor product and against nothing else:
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude` is the Stacks 08CG predicate at
`Stacks.Cohomology.TorAmplitude.derTensor`, the derived tensor product of Stacks 06YU on
`D(𝒪_X)`, and the stalk side is the Stacks 08CG predicate at
`Stacks.SheafOfModules.DerivedTensorStalk.stalkDerivedTensor`, the canonical derived tensor
product of Stacks 0BYI over the stalk ring. What the Stacks proof cites — Stacks 01CB and
exactness of stalks — is `Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso`.

The two steps are both `Iff`s of the same proposition read in two vocabularies:
`AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_canonicalCertified_iff` says the Stacks 08CG
predicate at the canonical derived tensor product is this one, and
`AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_canonicalCertified_iff_forall_stalk` is
`Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeIn_canonical_iff_forall_stalk`, the
stalkwise criterion, at that derived tensor product.

`AlgebraicGeometry.SheafOfModules.hasTorAmplitudeIn_iff_forall_stalk` is the engine: the same
equivalence for derived tensor products supplied as bare bifunctors on `D(𝒪_X)` and on each
`D(𝒪_{X, x})`, together with the isomorphism identifying them on stalks. -/
@[stacks 09U9 "Tor amplitude in [a, b] on a ringed space holds exactly when it holds at every
stalk, for the derived tensor product of Stacks 06YU on D(O_X) and the canonical derived tensor
product of Stacks 0BYI over each stalk ring; the derived form of Stacks 01CB that the source
proof cites is derivedTensorStalkIso in this file.",
  sga "6 I 5.6.2" "ringed space case", sga "4 XVII 4.2.8" "clause (iii)"]
theorem hasTorAmplitude_iff_forall_stalk
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) :
    HasTorAmplitude X E a b ↔
      ∀ x : X.carrier, CategoryTheory.DerivedCategory.HasTorAmplitudeIn
        (Stacks.SheafOfModules.DerivedTensorStalk.stalkDerivedTensor X.sheaf x)
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings X) x
          ).mapDerivedCategory.obj E) a b :=
  (AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_canonicalCertified_iff X E a b).symm.trans
    (AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_canonicalCertified_iff_forall_stalk X E a b)

end Stacks.Cohomology.TorAmplitude

end
