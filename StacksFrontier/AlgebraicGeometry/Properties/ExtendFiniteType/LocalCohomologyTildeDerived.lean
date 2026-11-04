module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDerivedModules
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.QuasicoherentSupportedComplexes
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyTildeSupported
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Basic
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.Coreflection

/-!
# Local cohomology is cohomology with support on the spectrum, for an arbitrary complex

Let `A` be a commutative ring, let `I ⊆ A` be a finitely generated ideal, let `X = Spec A` and
let `Z = V(I)`. This module proves [Stacks, Tag 0A6T]: for every object `K` of `D(A)`,
corresponding to `K̃` in `D_QCoh(𝒪_X)` by the derived Spec–Γ equivalence of
[Stacks, Tag 06Z0], there is an isomorphism

`RΓ_Z(K) ≅ RΓ_Z(X, K̃)`

in `D(A)`, functorial in `K`, where the left-hand side is the local cohomology functor of
[Stacks, Tag 0A6Q] and the right-hand side is cohomology with support in `Z`, here in the form
`RΓ(X, i_* R𝓗_Z(K̃))`. The tag itself, with the total right derived functor of `Γ_Z(X, -)` on
the right, is derived from this as
`Stacks.LocalCohomologyTilde.localCohomologyIsoDerivedSectionsWithSupport`.

## Main definitions

* `Stacks.LocalCohomologyTilde.derivedSupportedTilde` — the functor
  `K ↦ RΓ(Spec A, i_* R𝓗_{V(I)}(K̃))` on `D(A)`, the right-hand side of the tag read as an
  endofunctor of `D(A)` through the equivalence of Tag 06Z0.
* `Stacks.LocalCohomologyTilde.derivedSupportedTildeToId` — its canonical map to the identity.

## Main results

* `Stacks.LocalCohomologyTilde.derivedPowerTorsion_derivedSupportedTilde` — `RΓ_Z(X, K̃)` has
  `I`-power-torsion cohomology.
* `Stacks.LocalCohomologyTilde.isIso_derivedSupportedTildeToId_app` — the canonical map is
  invertible on objects with `I`-power-torsion cohomology.
* `Stacks.LocalCohomologyTilde.isIso_derivedSupportedTilde_map_toId` — the functor inverts every
  component of its canonical map.
* `Stacks.LocalCohomologyTilde.localCohomologyDerivedSupportedTildeIso` and
  `Stacks.LocalCohomologyTilde.localCohomologyDerivedSupportedTildeIso_comp_toId` — Tag 0A6T
  in the form `RΓ(X, i_* R𝓗_Z(-))`, and its normalization against the counit defining `RΓ_Z`.

## Implementation notes

The proof is the universal property of `RΓ_Z` rather than the source's triangle-and-Čech
computation. `RΓ_Z` is by construction the coreflection of `D(A)` onto the objects with
`I`-power-torsion cohomology ([Stacks, Tag 0A6R]), so it is enough to exhibit
`K ↦ RΓ_Z(X, K̃)` as such a coreflection, which is the three hypotheses of
`Stacks.LocalCohomology.CechFormula.exists_normalized_coreflectionIso`. That route also
delivers the normalization, and it never forms a cone, so the functoriality the source's proof
had to be repaired to obtain is automatic here.

All three hypotheses come from material already in the library. The geometric input is
[Stacks, Tag 0G7G]: `i_* R𝓗_Z` carries `D_QCoh(𝒪_X)` into the complexes supported on `Z` and is
there right adjoint to the inclusion. Its hypothesis is that `X ∖ Z` be retrocompact, which for
`Z = V(I)` is exactly finite generation of `I`
(`PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg`) — this is the only place the tag's
finite-generation hypothesis is used, and it is used in the same way the source uses it, to
make the complement a finite union of standard opens. The translation between the two
subcategories is
`Stacks.LocalCohomologyTilde.derivedPowerTorsion_iff_cohomologySupportedOn_tilde`: an object of
`D(A)` has `I`-power-torsion cohomology exactly when its sheafification is supported on `V(I)`.

`RΓ_Z(X, -)` appears here in the form `RΓ(X, i_* R𝓗_Z(-))` rather than as the total right
derived functor of `Γ_Z(X, -)` directly
(`Stacks.Cohomology.SectionsWithSupport.canonicalDerivedSectionsWithSupport`). The two are the
same functor by [Stacks, Tag 0G70]; that identification, and with it Tag 0A6T with the
right-hand side of [Stacks, Section 0G6Y] itself, is
`Stacks.LocalCohomologyTilde.localCohomologyIsoDerivedSectionsWithSupport`, where the tag is
registered.

Everything is stated at `CategoryTheory.HasDerivedCategory.standard`, the model at which Tag
06Z0's equivalence and Tag 0G7G's adjunction are both available. The local attribute carries
**priority 10000**: the import closure reaches
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose `HasDerivedCategory`
declarations are global instances, and a global instance beats a default-priority local
attribute.

Several instance arguments are supplied explicitly with `@` and the invertibility of a composite
is transported with the private `isIso_of_eq` rather than by `rw`. Both are forced by the two
definitionally equal spellings of the structure sheaf of `Spec A` — `(Spec A).ringCatSheaf` and
`structureSheafRing (Spec A).toRingedSpace` — which a rewrite motive does not accept; the same
obstruction is documented in the implementation notes of Tag 0G7G's file.

## References

* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0G70](https://stacks.math.columbia.edu/tag/0G70)
* [Stacks Project, Tag 0G7G](https://stacks.math.columbia.edu/tag/0G7G)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Perfect.SupportedQuasicoherent

-- Standard model only: `quasiCoherentSupportedInclusionAdj` (0G7G), the 06Z0 equivalence.
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomologyTilde

variable {A : CommRingCat.{u}} {I : Ideal A}

/-- `Z = V(I)`, as a subset of the space underlying `Spec A`. -/
abbrev vanishingSet (A : CommRingCat.{u}) (I : Ideal A) : Set ↥(Spec A) :=
  supportSubset (PrimeSpectrum.zeroLocus (I : Set A))

/-- `V(I)` is closed in `Spec A`. -/
theorem isClosed_vanishingSet (A : CommRingCat.{u}) (I : Ideal A) :
    IsClosed (vanishingSet A I) :=
  PrimeSpectrum.isClosed_zeroLocus _

/-- For a finitely generated ideal `I`, the complement of `V(I)` is retrocompact in `Spec A`. -/
theorem isRetrocompact_compl_vanishingSet (hI : I.FG) :
    IsRetrocompact (vanishingSet A I)ᶜ :=
  PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg hI

/-- `D_QCoh(𝒪_{Spec A})`, the target of derived sheafification. -/
abbrev derivedQCoh (A : CommRingCat.{u}) :
    ObjectProperty (DerivedCategory (Spec A).Modules) :=
  DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)

section Main

variable (hI : I.FG)

/-- The adjunction of Stacks 0G7G (2) at `X = Spec A` and `Z = V(I)`: `i_* R𝓗_Z` is right
adjoint to the inclusion of the complexes supported on `Z`. -/
abbrev supportAdj :
    quasiCoherentSupportedInclusion (Spec A) (vanishingSet A I) ⊣
      quasiCoherentDerivedSupport (Spec A) (vanishingSet A I) (isClosed_vanishingSet A I)
        (isRetrocompact_compl_vanishingSet hI) :=
  quasiCoherentSupportedInclusionAdj (Spec A) (vanishingSet A I) (isClosed_vanishingSet A I)
    (isRetrocompact_compl_vanishingSet hI)

/-- The coreflection `i_* R𝓗_{V(I)}` read as an endofunctor of `D_QCoh(𝒪_{Spec A})`. -/
abbrev supportComonad :
    (derivedQCoh A).FullSubcategory ⥤ (derivedQCoh A).FullSubcategory :=
  quasiCoherentDerivedSupport (Spec A) (vanishingSet A I) (isClosed_vanishingSet A I)
      (isRetrocompact_compl_vanishingSet hI) ⋙
    quasiCoherentSupportedInclusion (Spec A) (vanishingSet A I)

/-- The derived Spec–Γ adjunction of Stacks 06Z0, whose unit and counit are invertible. -/
abbrev tildeAdj (A : CommRingCat.{u}) :
    derivedTilde A ⊣ derivedGlobalSectionsQuasicoherent A :=
  AlgebraicGeometry.StandardModel.derivedTildeQuasicoherentAdjunction A

/-- The counit of the derived Spec–Γ adjunction `tildeAdj A` is an isomorphism. -/
theorem tildeAdj_counit_isIso (A : CommRingCat.{u}) : IsIso (tildeAdj A).counit :=
  have := AlgebraicGeometry.StandardModel.derivedGlobalSectionsQuasicoherent_isEquivalence A
  Adjunction.counit_isIso_of_R_fully_faithful _

/-- **`K ↦ RΓ(Spec A, i_* R𝓗_{V(I)}(K̃))`**, the right-hand side of Tag 0A6T read as an
endofunctor of `D(A)` through the derived Spec–Γ equivalence of Tag 06Z0. -/
def derivedSupportedTilde :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  derivedTilde A ⋙ supportComonad hI ⋙ derivedGlobalSectionsQuasicoherent A

/-- The value of the coreflection has cohomology sheaves supported on `V(I)`: this is the
support half of Stacks 0G7G (1), recorded in the corestriction. -/
theorem cohomologySupportedOn_supportComonad (E : (derivedQCoh A).FullSubcategory) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace)
      (vanishingSet A I) ((derivedQCoh A).ι.obj ((supportComonad hI).obj E)) :=
  ((quasiCoherentDerivedSupport (Spec A) (vanishingSet A I) (isClosed_vanishingSet A I)
    (isRetrocompact_compl_vanishingSet hI)).obj E).property.2

/-- The sheafification of `W` is the inclusion of `W̃` read in `D_QCoh`: Tag 06Z0's
`derivedTildeCompι`, at one object. -/
def tildeObjIso (W : DerivedCategory (ModuleCat.{u} A)) :
    (tildeSheafFunctor A).mapDerivedCategory.obj W ≅
      (derivedQCoh A).ι.obj ((derivedTilde A).obj W) :=
  ((derivedTildeCompι A).app W).symm

/-- The inclusion of the complexes supported on `V(I)` into `D_QCoh(𝒪_{Spec A})` is faithful. -/
instance quasiCoherentSupportedInclusion_faithful :
    (quasiCoherentSupportedInclusion (Spec A) (vanishingSet A I)).Faithful := by
  unfold quasiCoherentSupportedInclusion
  infer_instance

/-- The inclusion of the complexes supported on `V(I)` into `D_QCoh(𝒪_{Spec A})` is full. -/
instance quasiCoherentSupportedInclusion_full :
    (quasiCoherentSupportedInclusion (Spec A) (vanishingSet A I)).Full := by
  unfold quasiCoherentSupportedInclusion
  infer_instance

/-- The unit of the derived Spec–Γ adjunction of Tag 06Z0, as an isomorphism: derived
sheafification is an equivalence, so `K ⟶ RΓ(Spec A, K̃)` is invertible. -/
def tildeUnitIso (A : CommRingCat.{u}) :
    𝟭 (DerivedCategory (ModuleCat.{u} A)) ≅
      derivedTilde A ⋙ derivedGlobalSectionsQuasicoherent A :=
  asIso (tildeAdj A).unit

/-- The canonical map `RΓ(Spec A, i_* R𝓗_{V(I)}(K̃)) ⟶ K`: the counit of Stacks 0G7G (2),
read over `A` through the invertible unit of the derived Spec–Γ adjunction of Tag 06Z0. -/
def derivedSupportedTildeToId :
    derivedSupportedTilde hI ⟶ 𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  Functor.whiskerRight (Functor.whiskerLeft (derivedTilde A) (supportAdj hI).counit)
      (derivedGlobalSectionsQuasicoherent A) ≫
    (tildeUnitIso A).inv

/-- **The sheafification of `RΓ(Spec A, i_* R𝓗_{V(I)}(K̃))` is `i_* R𝓗_{V(I)}(K̃)`**: the counit
of the derived Spec–Γ adjunction is invertible, `i_* R𝓗_{V(I)}(K̃)` lying in `D_QCoh`. -/
theorem cohomologySupportedOn_tilde_derivedSupportedTilde
    (K : DerivedCategory (ModuleCat.{u} A)) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace)
      (vanishingSet A I)
      ((tildeSheafFunctor A).mapDerivedCategory.obj ((derivedSupportedTilde hI).obj K)) :=
  DerivedQCoh.cohomologySupportedOn_of_iso _
    (((derivedQCoh A).ι.mapIso
        (asIso ((tildeAdj A).counit.app
          ((supportComonad hI).obj ((derivedTilde A).obj K))))).symm ≪≫
      (tildeObjIso ((derivedSupportedTilde hI).obj K)).symm)
    (cohomologySupportedOn_supportComonad hI ((derivedTilde A).obj K))

/-- **The first hypothesis of the coreflection criterion.** For every `K` in `D(A)` the complex
`RΓ(Spec A, i_* R𝓗_{V(I)}(K̃))` has `I`-power-torsion cohomology: its sheafification is
`i_* R𝓗_{V(I)}(K̃)`, which is supported on `V(I)` by Stacks 0G7G (1), and the dictionary of
`derivedPowerTorsion_iff_cohomologySupportedOn_tilde` turns that into power torsion. -/
theorem derivedPowerTorsion_derivedSupportedTilde (K : DerivedCategory (ModuleCat.{u} A)) :
    Dualizing.derivedPowerTorsionProperty (A : Type u) I hI
      ((derivedSupportedTilde hI).obj K) :=
  (derivedPowerTorsion_iff_cohomologySupportedOn_tilde hI _).mpr
    (cohomologySupportedOn_tilde_derivedSupportedTilde hI K)

/-- The sheafification of an object with `I`-power-torsion cohomology is supported on `V(I)`,
read in `D_QCoh(𝒪_{Spec A})`. -/
theorem cohomologySupportedOn_derivedTilde_of_derivedPowerTorsion
    {Y : DerivedCategory (ModuleCat.{u} A)}
    (hY : Dualizing.derivedPowerTorsionProperty (A : Type u) I hI Y) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace)
      (vanishingSet A I) ((derivedQCoh A).ι.obj ((derivedTilde A).obj Y)) :=
  DerivedQCoh.cohomologySupportedOn_of_iso _ (tildeObjIso Y)
    ((derivedPowerTorsion_iff_cohomologySupportedOn_tilde hI Y).mp hY)

/-- A functor sends an isomorphism to an isomorphism (the hypothesis as an explicit argument). -/
private theorem isIso_map_of_isIso {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y : C} {f : X ⟶ Y} (hf : IsIso f) : IsIso (F.map f) := F.map_isIso f

/-- **The second hypothesis of the coreflection criterion.** On an object `Y` of `D(A)` with
`I`-power-torsion cohomology the canonical map `RΓ(Spec A, i_* R𝓗_{V(I)}(Ỹ)) ⟶ Y` is an
isomorphism: `Ỹ` is then supported on `V(I)`, so it lies in the image of the inclusion and the
counit of Stacks 0G7G (2) is invertible there. -/
theorem isIso_derivedSupportedTildeToId_app
    (Y : DerivedCategory (ModuleCat.{u} A))
    (hY : Dualizing.derivedPowerTorsionProperty (A : Type u) I hI Y) :
    IsIso ((derivedSupportedTildeToId hI).app Y) := by
  have hcounit : IsIso ((supportAdj hI).counit.app ((derivedTilde A).obj Y)) :=
    Adjunction.isIso_counit_app_of_iso (supportAdj hI)
      (Y := (⟨(derivedQCoh A).ι.obj ((derivedTilde A).obj Y),
        ⟨((derivedTilde A).obj Y).property,
          cohomologySupportedOn_derivedTilde_of_derivedPowerTorsion hI hY⟩⟩ :
          (Stacks.Duality.quasiCoherentSupported (Spec A) (vanishingSet A I)).FullSubcategory))
      (Iso.refl _)
  have h2 : IsIso ((tildeUnitIso A).inv.app Y) :=
    NatIso.inv_app_isIso (tildeUnitIso A) Y
  exact IsIso.comp_isIso' (isIso_map_of_isIso (derivedGlobalSectionsQuasicoherent A) hcounit) h2

/-! ### The third hypothesis: the coreflection inverts its own counit -/

/-- If `f = g` and `g` is an isomorphism, then so is `f`. -/
private theorem isIso_of_eq {C : Type*} [Category* C] {X Y : C} {f g : X ⟶ Y}
    (h : f = g) (hg : IsIso g) : IsIso f := h ▸ hg

/-- For an adjunction with fully faithful left adjoint the right adjoint inverts every component
of the counit: the right triangle identity exhibits that image as a one-sided inverse of a
component of the unit, which is invertible because the left adjoint is fully faithful. -/
theorem isIso_quasiCoherentDerivedSupport_map_counit_app
    (E : (derivedQCoh A).FullSubcategory) :
    IsIso ((quasiCoherentDerivedSupport (Spec A) (vanishingSet A I) (isClosed_vanishingSet A I)
      (isRetrocompact_compl_vanishingSet hI)).map ((supportAdj hI).counit.app E)) := by
  have : IsIso (supportAdj hI).unit := Adjunction.unit_isIso_of_L_fully_faithful _
  have hu : IsIso ((supportAdj hI).unit.app
      ((quasiCoherentDerivedSupport (Spec A) (vanishingSet A I) (isClosed_vanishingSet A I)
        (isRetrocompact_compl_vanishingSet hI)).obj E)) :=
    NatIso.isIso_app_of_isIso _ _
  exact isIso_of_eq
    (IsIso.inv_eq_of_hom_inv_id ((supportAdj hI).right_triangle_components E)).symm
    inferInstance

/-- **Derived sheafification carries the canonical map `RΓ(Spec A, i_* R𝓗_Z(K̃)) ⟶ K` to the
counit of Stacks 0G7G (2)**, preceded by an invertible component of the counit of the derived
Spec–Γ adjunction of Tag 06Z0. -/
theorem derivedTilde_map_derivedSupportedTildeToId_app
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (derivedTilde A).map ((derivedSupportedTildeToId hI).app K) =
      (tildeAdj A).counit.app ((supportComonad hI).obj ((derivedTilde A).obj K)) ≫
        (supportAdj hI).counit.app ((derivedTilde A).obj K) :=
  have : IsIso ((derivedTilde A).map ((tildeUnitIso A).hom.app K)) :=
    Functor.map_isIso (derivedTilde A) ((tildeUnitIso A).hom.app K)
  have hsplit : (derivedTilde A).map ((derivedSupportedTildeToId hI).app K) =
      (derivedTilde A).map ((derivedGlobalSectionsQuasicoherent A).map
          ((supportAdj hI).counit.app ((derivedTilde A).obj K))) ≫
        (derivedTilde A).map ((tildeUnitIso A).inv.app K) :=
    (derivedTilde A).map_comp _ _
  have hinvl : (derivedTilde A).map ((tildeUnitIso A).hom.app K) ≫
      (derivedTilde A).map ((tildeUnitIso A).inv.app K) = 𝟙 _ :=
    ((derivedTilde A).map_comp _ _).symm.trans
      (((congrArg (derivedTilde A).map ((tildeUnitIso A).hom_inv_id_app K)).trans
        ((derivedTilde A).map_id _)))
  have hinv : (derivedTilde A).map ((tildeUnitIso A).inv.app K) =
      (tildeAdj A).counit.app ((derivedTilde A).obj K) :=
    (cancel_epi ((derivedTilde A).map ((tildeUnitIso A).hom.app K))).mp
      (hinvl.trans ((tildeAdj A).left_triangle_components K).symm)
  hsplit.trans ((congrArg (fun g => _ ≫ g) hinv).trans
    ((tildeAdj A).counit.naturality ((supportAdj hI).counit.app ((derivedTilde A).obj K))))

/-- **The third hypothesis of the coreflection criterion.** The functor
`K ↦ RΓ(Spec A, i_* R𝓗_{V(I)}(K̃))` inverts every component of its canonical map to the
identity: after sheafification that map is the counit of Stacks 0G7G (2) preceded by an
isomorphism, and the right adjoint of an adjunction with fully faithful left adjoint inverts the
counit. -/
theorem isIso_derivedSupportedTilde_map_toId
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((derivedSupportedTilde hI).map ((derivedSupportedTildeToId hI).app K)) := by
  have h1 := isIso_quasiCoherentDerivedSupport_map_counit_app hI ((derivedTilde A).obj K)
  have := tildeAdj_counit_isIso A
  have h2 := isIso_map_of_isIso (quasiCoherentDerivedSupport (Spec A) (vanishingSet A I)
    (isClosed_vanishingSet A I) (isRetrocompact_compl_vanishingSet hI))
    (NatIso.isIso_app_of_isIso (tildeAdj A).counit
      ((supportComonad hI).obj ((derivedTilde A).obj K)))
  have h3 := isIso_of_eq
    ((congrArg (quasiCoherentDerivedSupport (Spec A) (vanishingSet A I)
        (isClosed_vanishingSet A I) (isRetrocompact_compl_vanishingSet hI)).map
      (derivedTilde_map_derivedSupportedTildeToId_app hI K)).trans
      ((quasiCoherentDerivedSupport (Spec A) (vanishingSet A I) (isClosed_vanishingSet A I)
        (isRetrocompact_compl_vanishingSet hI)).map_comp _ _))
    (IsIso.comp_isIso' h2 h1)
  exact isIso_map_of_isIso (derivedGlobalSectionsQuasicoherent A)
    (isIso_map_of_isIso (quasiCoherentSupportedInclusion (Spec A) (vanishingSet A I)) h3)

/-! ### Tag 0A6T -/

/-- **Stacks 0A6T, with the normalization against the counits.** -/
theorem exists_localCohomologyDerivedSupportedTildeIso :
    ∃ e : Dualizing.localCohomologyFunctor (A : Type u) I hI ⋙
        (Dualizing.derivedPowerTorsionProperty (A : Type u) I hI).ι ≅
      derivedSupportedTilde hI,
      e.hom ≫ derivedSupportedTildeToId hI =
        (Dualizing.localCohomologyAdjunction (A : Type u) I hI).counit :=
  Stacks.LocalCohomology.CechFormula.exists_normalized_coreflectionIso _ _
    (Dualizing.localCohomologyAdjunction (A : Type u) I hI) (derivedSupportedTilde hI)
    (derivedSupportedTildeToId hI) (derivedPowerTorsion_derivedSupportedTilde hI)
    (isIso_derivedSupportedTildeToId_app hI) (isIso_derivedSupportedTilde_map_toId hI)

/-- **Stacks 0A6T, in the form `RΓ(X, i_* R𝓗_Z(-))`.** Let `A` be a ring, let `I ⊆ A` be a
finitely generated ideal and set `Z = V(I) ⊆ X = Spec A`. For `K ∈ D(A)`, corresponding to
`K̃ ∈ D_QCoh(𝒪_X)` by the derived Spec–Γ equivalence of [Stacks, Tag 06Z0], there is an isomorphism

`RΓ_Z(K) ≅ RΓ_Z(X, K̃)`

in `D(A)`, functorial in `K`: on the left the local cohomology functor of
[Stacks, Tag 0A6Q] and on the right cohomology with support in `Z`, in the form
`RΓ(X, i_* R𝓗_Z(-))`. The form with the total right derived functor of `Γ_Z(X, -)` on the right,
under which the tag is registered, is
`Stacks.LocalCohomologyTilde.localCohomologyIsoDerivedSectionsWithSupport`. The isomorphism is
normalized by `localCohomologyDerivedSupportedTildeIso_comp_toId`: it carries the counit of the
adjunction defining `RΓ_Z` to the canonical map `RΓ_Z(X, K̃) ⟶ K`. -/
def localCohomologyDerivedSupportedTildeIso :
    Dualizing.localCohomologyFunctor (A : Type u) I hI ⋙
        (Dualizing.derivedPowerTorsionProperty (A : Type u) I hI).ι ≅
      derivedSupportedTilde hI :=
  Classical.choose (p := fun e => e.hom ≫ derivedSupportedTildeToId hI =
    (Dualizing.localCohomologyAdjunction (A : Type u) I hI).counit)
    (exists_localCohomologyDerivedSupportedTildeIso hI)

/-- **The normalization of the comparison.** The isomorphism of
`localCohomologyDerivedSupportedTildeIso` carries the counit of the adjunction defining local
cohomology to the canonical map `RΓ_Z(X, K̃) ⟶ K`. This is what the tag asserts when it writes
the comparison as an equality of functors rather than as a bare isomorphism. -/
theorem localCohomologyDerivedSupportedTildeIso_comp_toId :
    (localCohomologyDerivedSupportedTildeIso hI).hom ≫ derivedSupportedTildeToId hI =
      (Dualizing.localCohomologyAdjunction (A : Type u) I hI).counit :=
  (exists_localCohomologyDerivedSupportedTildeIso hI).choose_spec

end Main

end Stacks.LocalCohomologyTilde

end
