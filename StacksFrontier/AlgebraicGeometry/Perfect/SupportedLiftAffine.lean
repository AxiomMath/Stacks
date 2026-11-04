module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedBiprodShiftAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedLiftAffineSpec
public import StacksFrontier.CategoryTheory.RoofTransportAlongEquivalence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism

/-!
# The affine case of [Stacks, Tag 09IM] at a general affine scheme

`StacksFrontier/AlgebraicGeometry/Perfect/SupportedLiftAffineSpec.lean` proves the affine case of
[Stacks, Tag 09IM], in the strengthened form the iteration of [Stacks, Tag 09IN] needs, at
`X = Spec A`. Its consumer — the two-open step of [Stacks, Tag 09IM] — applies it at an *affine
open* `V` of a general scheme, that is at `V.toScheme`, which is affine but is not `Spec A`. This
module moves it there.

[Stacks, Tag 08EK] has already been moved: in
`StacksFrontier/AlgebraicGeometry/Perfect/SupportedBiprodShiftAffine.lean`,
`exists_isPerfect_supported_biprod_shift_iso_restrict_of_isAffine` is it at any affine scheme.
What is left is the roof of [Stacks, Tag 08EH], and the device for moving it is
`Stacks.LiftingProblem.exists_roof_of_equivalence`: the existence of a roof transports along a
pair of equivalences of the two derived categories commuting with the two restriction functors.
The two equivalences are the derived pullbacks along an isomorphism of ringed spaces, and the
comparison between them is the *natural* square

`Le^* ⋙ (·)|_U ≅ (·)|_{e(U)} ⋙ L(X|_U ≅ Y|_{e(U)})^*`

which is `Stacks.Perfect.SupportedLiftAffine.derivedRestrictModulesIsoOfIso` below.

## Main definitions and results

* `Stacks.Perfect.SupportedLiftAffine.derivedRestrictModulesIsoOfIso`: the square above, as an
  isomorphism of functors.
* `Stacks.Perfect.SupportedLiftAffine.exists_roof_of_isCompact_of_isoSpec` and
  `Stacks.Perfect.SupportedLiftAffine.exists_roof_of_isCompact_of_isAffine`:
  **[Stacks, Tag 08EH] at a quasi-compact open of a general affine scheme**, with the middle
  object perfect and supported.
* `exists_isPerfect_supported_hom_biprod_shift_iso_restrict_of_isAffine`, in this namespace:
  **the affine case of [Stacks, Tag 09IM] at a general affine scheme, in the strengthened form.**

The registrations of [Stacks, Tag 08EK], [Stacks, Tag 08EH] and [Stacks, Tag 09IM] are on other
declarations, so no tag attribute is placed in this module.

## Implementation notes

**The square is natural, and that is the whole reason this module can exist.**
`Stacks.Perfect.SupportedBiprodShiftAffine.derivedRestrictModulesObjIsoOfIso` is the same
comparison at *one object*, which is all [Stacks, Tag 08EK]'s transport needed: there the object
produced over `Spec A` is pulled back and its restriction computed once. The roof cannot be moved
that way, because `Stacks.LiftingProblem.exists_roof_of_equivalence` has to read a *morphism* of
restrictions over `Spec A` and push the resulting morphism back, so it needs the naturality
square at `β` and at `γ`. Each of the five factors of the one-object comparison is a component of
a natural transformation, so the natural version is the same composite written at functor level;
nothing new is proved here.

**The quasi-coherence hypothesis travels because the isomorphism is one of schemes.** The three
classes of objects are carried backwards and forwards by five implications rather than by the
equivalence, so that both sides use the honest predicate. For perfectness and for cohomological
support the transports along an isomorphism of ringed spaces are already available
(`Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_iff` and
`Stacks.Cohomology.SupportedComplexes.cohomologySupportedOn_derivedPullback`). For
quasi-coherence of the cohomology sheaves no ringed-space statement is needed and none exists:
the hypothesis is an isomorphism of *schemes*, so
`Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel` — [Stacks, Tag 08DW] part (1)
— applies to its inverse directly. That is why the isomorphism here is one of schemes and not,
as in `exists_isPerfect_supported_biprod_shift_iso_restrict_of_isoSpec` of
`Stacks.Perfect.SupportedBiprodShiftAffine`, one of ringed spaces.

**The two transported class hypotheses are separate lemmas.** The forward transport of support
and the whole application of `Stacks.LiftingProblem.exists_roof_of_equivalence` do not elaborate
together inside the default heartbeat budget: the five implications are then checked against a
conclusion still carrying the metavariables of the six class arguments. Split off, each is
checked against a small statement and the application is a single term.

**`HasDerivedCategory.standard`** is a local instance at priority `10000`, as in the modules this
one consumes: without the priority a different derived-category model is selected and their
statements are then about a different category, with no error naming the cause.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 09IN](https://stacks.math.columbia.edu/tag/09IN)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.DerivedPullbackAlongIso (derivedPullbackEquivalence)
open Stacks.Cohomology.SupportedComplexes (closedSubsetPreimage
  cohomologySupportedOn_derivedPullback)
open Stacks.Cohomology.TransportAlongIso (isPerfect_derivedPullback_iff
  ringedSpaceIsoOfSchemeIso)
open Stacks.Perfect.SupportedBiprodShiftAffine (imageOpenOfIso restrictIsoOfIso
  restrictIsoOfIso_hom_comp_ofRestrict inv_base_hom_base preimage_inv_base_eq_image
  exists_isPerfect_supported_biprod_shift_iso_restrict_of_isAffine)

universe u

namespace Stacks.Perfect.SupportedLiftAffine

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The naturality square of restriction against an isomorphism -/

section Square

variable {X Y : RingedSpace.{u, u}} (e : X ≅ Y) (U : Opens X)

/-- **Restricting to `U` a derived pullback along `e` is pulling back the restriction to `e(U)`**,
naturally in the object.

This is `Stacks.Perfect.SupportedBiprodShiftAffine.derivedRestrictModulesObjIsoOfIso` written at
functor level: each derived restriction is the derived pullback along the inclusion of its open,
derived pullbacks along composable morphisms compose by [Stacks, Tag 0D5S], and the two routes
from `X|_U` to `Y` agree by
`Stacks.Perfect.SupportedBiprodShiftAffine.restrictIsoOfIso_hom_comp_ofRestrict`. -/
def derivedRestrictModulesIsoOfIso :
    derivedPullback e.hom ⋙ AlgebraicGeometry.RingedSpace.derivedRestrictModules X U ≅
      AlgebraicGeometry.RingedSpace.derivedRestrictModules Y (imageOpenOfIso e U) ⋙
        derivedPullback (restrictIsoOfIso e U).hom :=
  Functor.isoWhiskerLeft (derivedPullback e.hom)
      (AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback X U) ≪≫
    Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (X.ofRestrict U.isOpenEmbedding) e.hom ≪≫
    eqToIso (congrArg (fun f : X.restrict U.isOpenEmbedding ⟶ Y => derivedPullback f)
      (restrictIsoOfIso_hom_comp_ofRestrict e U).symm) ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (restrictIsoOfIso e U).hom
      (Y.ofRestrict (imageOpenOfIso e U).isOpenEmbedding)).symm ≪≫
    Functor.isoWhiskerRight
      (AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback Y
        (imageOpenOfIso e U)).symm (derivedPullback (restrictIsoOfIso e U).hom)

/-- **The image of a quasi-compact open under an isomorphism of ringed spaces is quasi-compact.**
`Stacks.Perfect.SupportedBiprodShiftAffine.imageOpenOfIso` is written as a preimage under `e.inv`,
and `Stacks.Perfect.SupportedBiprodShiftAffine.preimage_inv_base_eq_image` identifies it with the
image under `e.hom`, which is compact because `e.hom` is continuous. -/
theorem isCompact_imageOpenOfIso (hU : IsCompact ((U : Opens X) : Set X)) :
    IsCompact ((imageOpenOfIso e U : Opens Y) : Set Y) := by
  show IsCompact (e.inv.hom.base ⁻¹' (U : Set X))
  rw [preimage_inv_base_eq_image e (U : Set X)]
  exact hU.image e.hom.hom.base.hom.continuous

/-- **Cohomological support travels forward along `e`.** An object of `D(𝒪_Y)` supported on the
preimage of `T ⊆ X` under `e.inv` pulls back along `e.hom` to an object supported on `T`: the two
preimages compose to the identity.

This is the fifth of the five class implications
`Stacks.LiftingProblem.exists_roof_of_equivalence` asks for, split off so that it is checked
against its own statement; see the implementation notes. -/
theorem cohomologySupportedOn_derivedPullback_hom (T : Set X)
    (R : DerivedCategory (OXMod.{u, u} Y))
    (hR : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing Y)
      (e.inv.hom.base ⁻¹' T) R) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) T
      ((derivedPullback e.hom).obj R) := by
  have hset : closedSubsetPreimage e.hom (e.inv.hom.base ⁻¹' T) = T := by
    ext x
    show e.inv.hom.base (e.hom.hom.base x) ∈ T ↔ x ∈ T
    rw [inv_base_hom_base]
  exact hset ▸ cohomologySupportedOn_derivedPullback e.hom (e.inv.hom.base ⁻¹' T) R hR

end Square

/-! ### The roof at a general affine scheme -/

/-- **[Stacks, Tag 08EH] at a quasi-compact open of a scheme isomorphic to `Spec A`.** Let
`esch : W ≅ Spec A` be an isomorphism of schemes, `T ⊆ W` a subset, `U ⊆ W` a quasi-compact open,
`P` a perfect object of `D(𝒪_W)` with cohomology supported on `T`, `E` an object of `D(𝒪_W)` with
quasi-coherent cohomology and `α : P|_U ⟶ E|_U`. Then there is a roof `P ←β— R —γ→ E` with `R`
perfect and supported on `T`, `β|_U` invertible and `γ|_U = β|_U ≫ α`.

`Stacks.Perfect.SupportedLiftAffineSpec.exists_roof_of_isCompact` is the statement at `Spec A`,
and `Stacks.LiftingProblem.exists_roof_of_equivalence` transports it along the two derived
pullbacks of `esch` and of the induced isomorphism of open subspaces, compared by
`Stacks.Perfect.SupportedLiftAffine.derivedRestrictModulesIsoOfIso`.

The registration of [Stacks, Tag 08EH] is on another declaration, so no tag
attribute is placed here. -/
theorem exists_roof_of_isCompact_of_isoSpec {A : CommRingCat.{u}} {W : Scheme.{u}}
    (esch : W ≅ Spec A) (T : Set W) (U : W.Opens)
    (hU : IsCompact ((U : W.Opens) : Set W))
    (P E : DerivedCategory (OXMod.{u, u} W.toRingedSpace))
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) P)
    (hPT : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing W.toRingedSpace) T P)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E).IsQuasicoherent)
    (α : (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace U).obj P ⟶
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace U).obj E) :
    ∃ (R : DerivedCategory (OXMod.{u, u} W.toRingedSpace)) (β : R ⟶ P) (γ : R ⟶ E),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) R ∧
        AlgebraicGeometry.CohomologySupportedOn (structureSheafRing W.toRingedSpace) T R ∧
          IsIso ((AlgebraicGeometry.RingedSpace.derivedRestrictModules
              W.toRingedSpace U).map β) ∧
            (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace U).map γ =
              (AlgebraicGeometry.RingedSpace.derivedRestrictModules
                W.toRingedSpace U).map β ≫ α :=
  Stacks.LiftingProblem.exists_roof_of_equivalence
    (derivedPullbackEquivalence (ringedSpaceIsoOfSchemeIso esch))
    (derivedPullbackEquivalence (restrictIsoOfIso (ringedSpaceIsoOfSchemeIso esch) U))
    (derivedRestrictModulesIsoOfIso (ringedSpaceIsoOfSchemeIso esch) U)
    (Pp := Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace))
    (Sp := AlgebraicGeometry.CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace)
      ((ringedSpaceIsoOfSchemeIso esch).inv.hom.base ⁻¹' T))
    (Qp := fun B => ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (Spec A).toRingedSpace)) i).obj
        B).IsQuasicoherent)
    (Pp' := Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace))
    (Sp' := AlgebraicGeometry.CohomologySupportedOn (structureSheafRing W.toRingedSpace) T)
    (Qp' := fun B => ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj B).IsQuasicoherent)
    (fun P' hP' => (isPerfect_derivedPullback_iff (ringedSpaceIsoOfSchemeIso esch).symm P').2 hP')
    (cohomologySupportedOn_derivedPullback (ringedSpaceIsoOfSchemeIso esch).inv T)
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel esch.inv)
    (fun R hR => (isPerfect_derivedPullback_iff (ringedSpaceIsoOfSchemeIso esch) R).2 hR)
    (cohomologySupportedOn_derivedPullback_hom (ringedSpaceIsoOfSchemeIso esch) T)
    (Stacks.Perfect.SupportedLiftAffineSpec.exists_roof_of_isCompact
      ((ringedSpaceIsoOfSchemeIso esch).inv.hom.base ⁻¹' T)
      (imageOpenOfIso (ringedSpaceIsoOfSchemeIso esch) U)
      (isCompact_imageOpenOfIso (ringedSpaceIsoOfSchemeIso esch) U hU))
    P E hP hPT hE α

/-- **[Stacks, Tag 08EH] at a quasi-compact open of a general affine scheme.**
`Stacks.Perfect.SupportedLiftAffine.exists_roof_of_isCompact_of_isoSpec` along
`AlgebraicGeometry.Scheme.isoSpec`. The two-open step of [Stacks, Tag 09IM] applies it at an
affine open `V` of a general scheme, that is at `W = V.toScheme`, which is affine by
`AlgebraicGeometry.IsAffineOpen.isAffine_toScheme`.

The registration of [Stacks, Tag 08EH] is on another declaration, so no tag
attribute is placed here. -/
theorem exists_roof_of_isCompact_of_isAffine (W : Scheme.{u}) [IsAffine W] (T : Set W)
    (U : W.Opens) (hU : IsCompact ((U : W.Opens) : Set W))
    (P E : DerivedCategory (OXMod.{u, u} W.toRingedSpace))
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) P)
    (hPT : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing W.toRingedSpace) T P)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E).IsQuasicoherent)
    (α : (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace U).obj P ⟶
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace U).obj E) :
    ∃ (R : DerivedCategory (OXMod.{u, u} W.toRingedSpace)) (β : R ⟶ P) (γ : R ⟶ E),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) R ∧
        AlgebraicGeometry.CohomologySupportedOn (structureSheafRing W.toRingedSpace) T R ∧
          IsIso ((AlgebraicGeometry.RingedSpace.derivedRestrictModules
              W.toRingedSpace U).map β) ∧
            (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace U).map γ =
              (AlgebraicGeometry.RingedSpace.derivedRestrictModules
                W.toRingedSpace U).map β ≫ α :=
  exists_roof_of_isCompact_of_isoSpec W.isoSpec T U hU P E hP hPT hE α

/-! ### The affine case of [Stacks, Tag 09IM] at a general affine scheme -/

/-- **The affine case of [Stacks, Tag 09IM] at a general affine scheme, in the strengthened
form.** Let `W` be an affine scheme, let `T ⊆ W` be closed with quasi-compact complement, let
`U ⊆ W` be a quasi-compact open and let `E` be an object of `D(𝒪_W)` with quasi-coherent
cohomology. For every perfect `F` on `U` supported on `T ∩ U` and every `α : F ⟶ E|_U` there are
a perfect `R` on `W` supported on `T`, a map `β : R ⟶ E` and an isomorphism
`eR : R|_U ≅ F ⊕ F[1]` with `β|_U = eR.hom ≫ biprod.fst ≫ α`.

The two inputs are [Stacks, Tag 08EK] at an affine scheme,
`exists_isPerfect_supported_biprod_shift_iso_restrict_of_isAffine` in
`Stacks.Perfect.SupportedBiprodShiftAffine`, and [Stacks, Tag 08EH] at an affine scheme,
`Stacks.Perfect.SupportedLiftAffine.exists_roof_of_isCompact_of_isAffine`; they are combined by
`Stacks.Perfect.SupportedLiftAffineSpec.exists_iso_of_split_and_roof`, exactly as at `Spec A`.

The registrations of [Stacks, Tag 08EK], [Stacks, Tag 08EH] and [Stacks, Tag 09IM] are on other
declarations, so no tag attribute is placed here. -/
theorem exists_isPerfect_supported_hom_biprod_shift_iso_restrict_of_isAffine (W : Scheme.{u})
    [IsAffine W] (T : Set W) (hT : IsClosed T) (hTc : IsCompact Tᶜ) (U : W.Opens)
    (hU : IsCompact ((U : W.Opens) : Set W))
    (E : DerivedCategory (OXMod.{u, u} W.toRingedSpace))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) i).obj E).IsQuasicoherent)
    (F : DerivedCategory (OXMod.{u, u} (W.toRingedSpace.restrict U.isOpenEmbedding)))
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := W.toRingedSpace.restrict U.isOpenEmbedding) F)
    (hFT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing (W.toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) F)
    (α : F ⟶ (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace U).obj E) :
    ∃ (R : DerivedCategory (OXMod.{u, u} W.toRingedSpace)) (β : R ⟶ E),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) R ∧
        AlgebraicGeometry.CohomologySupportedOn (structureSheafRing W.toRingedSpace) T R ∧
          ∃ eR : (AlgebraicGeometry.RingedSpace.derivedRestrictModules
              W.toRingedSpace U).obj R ≅ F ⊞ F⟦(1 : ℤ)⟧,
            (AlgebraicGeometry.RingedSpace.derivedRestrictModules W.toRingedSpace U).map β =
              eR.hom ≫ biprod.fst ≫ α :=
  Stacks.Perfect.SupportedLiftAffineSpec.exists_iso_of_split_and_roof _ α biprod.fst _ _
    (exists_isPerfect_supported_biprod_shift_iso_restrict_of_isAffine W T hT hTc U hU F hF hFT)
    (fun P hP hPT a => exists_roof_of_isCompact_of_isAffine W T U hU P E hP hPT hE a)

end Stacks.Perfect.SupportedLiftAffine

end
