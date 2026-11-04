module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.Homology.PseudoCoherentRelative.TildePseudoCoherent
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Tor amplitude over the base of an associated sheaf on an affine scheme

Let `f : Spec A ⟶ Spec R` be the morphism of affine schemes of a ring map `R → A` and let `M^•`
be a complex of `A`-modules. The sheaf `M̃^•` on `Spec A` has Tor amplitude in `[a, b]` over the
base in the stalkwise sense of `AlgebraicGeometry.HasTorAmplitudeOver` exactly when `M^•`, read
as a complex of `R`-modules, has Tor amplitude in `[a, b]` over `R`, and exactly when the
complex of `f^{-1}𝒪_{Spec R}`-modules attached to `M^•` has Tor amplitude in `[a, b]` over
`f^{-1}𝒪_{Spec R}`.

The two sheaf-side conditions are two unrelated spellings of "finite Tor dimension over the
base": one reads the stalks of `M̃^•` over the local rings of `Spec R`, the other works on the
ringed space `(Spec A, f^{-1}𝒪_{Spec R})`. Identifying them is what lets a consumer phrased with
`HasTorAmplitudeOver` invoke Stacks 0DHY, and through it reach the certificate form of finite Tor
dimension that Stacks 0DHX consumes.

## Main definitions

* `relativeStalkTildeFunctorIso`: the stalk at a prime `q` of `A` of the sheaf associated to an
  `A`-module, read over the local ring of `Spec R`, is `A_q ⊗_A -` read over `R_{q ∩ R}`.
* `relativeStalkComplexTildeIso`: the same degreewise on complexes, which is
  `AlgebraicGeometry.relativeStalkComplex` of `M̃^•`.

## Main results

* `hasTorAmplitudeOver_iff_hasTorAmplitude_relativeComplex`:
  the identification of the two relative structures — `M̃^•` has Tor amplitude in `[a, b]` over
  the base stalkwise if and only if the complex of `f^{-1}𝒪_{Spec R}`-modules attached to `M^•`
  has Tor amplitude in `[a, b]` over `f^{-1}𝒪_{Spec R}`.
* `hasTorAmplitudeOver_tildeComplex_iff`:
  Stacks 0DHY read on the stalkwise side — the same condition holds if and only if `M^•`, read
  as a complex of `R`-modules, has Tor amplitude in `[a, b]` over `R`.
* `exists_hasTorAmplitudeOver_tildeComplex_iff` and
  `exists_hasTorAmplitudeOver_iff_locallyHasFiniteTorDimension`: the finite-Tor-dimension forms
  of the previous two.
* `hasFiniteTorDimension_iff_hasFiniteTorDimensionCanonical`:
  finite Tor dimension at an arbitrary certified derived tensor product is finite Tor dimension
  at the canonical one, which is the form in which a consumer quantified over a derived tensoring
  datum states its hypothesis.
* `hasTorAmplitudeCanonicalLift_relativeStalkComplex_tilde_iff`:
  the single-prime statement the three results above are assembled from.

## Implementation notes

Both sides sit at `CategoryTheory.HasDerivedCategory.standard`, which is the derived-category
model of `StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange` and of
`StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine` alike, so nothing here transports
between derived-category models.

The content is the single-prime identification, and it is a chase through three comparisons.
`AlgebraicGeometry.HasTorAmplitudeOver` reads the stalk through
`Stacks.ModuleSkyscraper.modulesStalkFunctor`, over the `CommRingCat`-valued stalk, whereas
Stacks 01HV is available over the `RingCat`-valued stalk of the sheaf of rings; the two are
compared by `AlgebraicGeometry.restrictScalarsStalkObjIso`, promoted to an isomorphism of
functors by `modulesStalkRestrictScalarsFunctorIso` below. That the two stalk functors have the
same source at all rests on `(Spec A).ringCatSheaf` being
`structureSheafRing (Spec A).toRingedSpace` and on
`Stacks.TildeStalk.specStalkFunctor` being
`AlgebraicGeometry.SheafOfModules.stalkFunctor (Spec A).ringCatSheaf`, both by `rfl`.
The coefficient rings are then matched by `relativeStalkRingHom_eq_algebraMap`, which identifies
the composite `𝒪_{Spec R, q ∩ R} ⟶ A_q` of the stalk map of `f` with the two stalk-ring
comparisons as `algebraMap R_{q ∩ R} A_q` after `AlgebraicGeometry.Spec.stalkIso`; its input is
Mathlib's `AlgebraicGeometry.Scheme.localRingHom_comp_stalkIso`.

The pseudo-coherence counterpart of this bridge is the affine one,
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_tilde_iff` of
`StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine`, which already relates the
sheaf-level predicate on `Spec A` to the `ModuleCat` predicate
`StacksDraft.PseudoCoherence.IsPseudoCoherent`; it is not the comparison between
`derivedRestrictModules` and derived pullback used for restriction to an open, and neither
subsumes the other.

## References

* [Stacks Project, Tag 0DHY](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 0654](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Tag 0B67](https://stacks.math.columbia.edu/tag/0B67)
* [Stacks Project, Tag 0DJF](https://stacks.math.columbia.edu/tag/0DJF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude

universe u

namespace AlgebraicGeometry.AffineRelativeTorAmplitude

attribute [local instance] HasDerivedCategory.standard

/-! ### The two spellings of the stalk of a sheaf of modules -/

/-- **The two stalk functors on sheaves of `𝒪_X`-modules agree.** The stalk over the local ring
`𝒪_{X,x}` is the stalk over the `RingCat`-valued stalk of the sheaf of rings with its scalars
restricted along the comparison between them. This is
`AlgebraicGeometry.restrictScalarsStalkObjIso` as an isomorphism of functors; naturality holds
because both components are the identity on the underlying abelian group. -/
def modulesStalkRestrictScalarsFunctorIso (X : Scheme.{u}) (x : X) :
    AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x ⋙
        ModuleCat.restrictScalars (AlgebraicGeometry.ringCatStalkRingEquiv x).symm.toRingHom ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor X x :=
  NatIso.ofComponents (fun M => AlgebraicGeometry.restrictScalarsStalkObjIso x M) (fun _ => rfl)

/-! ### The coefficient ring of a relative stalk on an affine scheme -/

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- **The two stalk-ring comparisons of `𝒪_{Spec A}` at a prime `q` cancel.** The `RingCat`-valued
stalk is `A_q` by `specStalkRingIso` and the `CommRingCat`-valued stalk is `A_q` by
`AlgebraicGeometry.Spec.stalkIso`; passing from the second to the first and then to `A_q` is
passing directly. -/
theorem specStalkRingEquiv_comp_ringCatStalkRingEquiv_symm (q : PrimeSpectrum A) :
    (specStalkRingEquiv A q).toRingHom.comp
        (AlgebraicGeometry.ringCatStalkRingEquiv
          (X := Spec (CommRingCat.of A)) q).symm.toRingHom
      = (Spec.stalkIso (CommRingCat.of A) q).hom.hom :=
  congrArg RingCat.Hom.hom
    ((SemilinearStalk.commStalkIso (Spec (CommRingCat.of A)).presheaf q).inv_hom_id_assoc
      ((forget₂ CommRingCat.{u} RingCat.{u}).map (Spec.stalkIso (CommRingCat.of A) q).hom))

/-- **The stalk of `𝒪_{Spec R}` at the image of a prime `q` of `A` is `R_{q ∩ R}`**, as a ring
isomorphism. This is `AlgebraicGeometry.Spec.stalkIso`, with the localisation named at the ideal
`q ∩ R` rather than at the image point, which is the spelling the module API matches against. -/
def baseStalkRingEquiv (q : PrimeSpectrum A) :
    ToType ((Spec (CommRingCat.of R)).presheaf.stalk ((specMap R A).base q)) ≃+*
      Localization.AtPrime (Ideal.under R q.asIdeal) :=
  (Spec.stalkIso (CommRingCat.of R) ((specMap R A).base q)).commRingCatIsoToRingEquiv

/-- **The stalk map of `f : Spec A ⟶ Spec R` is the localisation map `R_{q ∩ R} ⟶ A_q`**, read
through `AlgebraicGeometry.Spec.stalkIso` at both ends. This is Mathlib's
`AlgebraicGeometry.Scheme.localRingHom_comp_stalkIso` with the target comparison moved to the
other side. -/
theorem stalkMap_comp_specStalkIso (q : PrimeSpectrum A) :
    (specMap R A).stalkMap q ≫ (Spec.stalkIso (CommRingCat.of A) q).hom
      = (Spec.stalkIso (CommRingCat.of R) ((specMap R A).base q)).hom ≫
        CommRingCat.ofHom (Localization.localRingHom (Ideal.under R q.asIdeal) q.asIdeal
          (algebraMap R A) rfl) :=
  (Iso.eq_comp_inv (Spec.stalkIso (CommRingCat.of A) q)).mp
    ((Category.assoc _ _ _).trans
      (Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom (algebraMap R A)) q)).symm

/-- **The ring homomorphism over which a relative stalk at a prime `q` of `A` is read.** The
stalk map of `f : Spec A ⟶ Spec R` followed by the two comparisons that present the stalk of
`𝒪_{Spec A}` at `q` as `A_q` is `algebraMap R_{q ∩ R} A_q` for
`Localization.AtPrime.algebraOfLiesOver`, preceded by the presentation of the stalk of
`𝒪_{Spec R}` at `q ∩ R` as `R_{q ∩ R}`. -/
theorem relativeStalkRingHom_eq_algebraMap (q : PrimeSpectrum A) :
    letI : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
        (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
    (specStalkRingEquiv A q).toRingHom.comp
        ((AlgebraicGeometry.ringCatStalkRingEquiv
            (X := Spec (CommRingCat.of A)) q).symm.toRingHom.comp
          ((specMap R A).stalkMap q).hom)
      = (algebraMap (Localization.AtPrime (Ideal.under R q.asIdeal))
          (Localization.AtPrime q.asIdeal)).comp (baseStalkRingEquiv R A q).toRingHom :=
  (RingHom.comp_assoc _ _ _).symm.trans
    ((congrArg (fun t => RingHom.comp t ((specMap R A).stalkMap q).hom)
        (specStalkRingEquiv_comp_ringCatStalkRingEquiv_symm A q)).trans
      (congrArg CommRingCat.Hom.hom (stalkMap_comp_specStalkIso R A q)))

/-! ### The relative stalk of an associated sheaf -/

/-- **Stacks 01HV read over the base.** The stalk at a prime `q` of `A` of the sheaf associated
to an `A`-module, viewed over the local ring of `Spec R` at `q ∩ R` along the stalk map of
`f : Spec A ⟶ Spec R`, is `A_q ⊗_A -` viewed over `R_{q ∩ R}` along `algebraMap R_{q ∩ R} A_q`,
naturally in the module.

This composes Stacks 01HV over the `RingCat`-valued stalk (`tildeStalkRestrictScalarsIso`) with
the comparison `modulesStalkRestrictScalarsFunctorIso` between the two stalk functors, the
coefficient rings being matched by `relativeStalkRingHom_eq_algebraMap`. -/
def relativeStalkTildeFunctorIso (q : PrimeSpectrum A) :
    letI : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
        (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
    tilde.functor (CommRingCat.of A) ⋙
        (Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec (CommRingCat.of A)) q ⋙
          ModuleCat.restrictScalars ((specMap R A).stalkMap q).hom) ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.AtPrime q.asIdeal)) ⋙
        (ModuleCat.restrictScalars.{u}
            (algebraMap (Localization.AtPrime (Ideal.under R q.asIdeal))
              (Localization.AtPrime q.asIdeal)) ⋙
          ModuleCat.restrictScalars.{u} (baseStalkRingEquiv R A q).toRingHom) := by
  letI : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
  refine Functor.isoWhiskerLeft (tilde.functor (CommRingCat.of A))
      (Functor.isoWhiskerRight
        (modulesStalkRestrictScalarsFunctorIso (Spec (CommRingCat.of A)) q).symm
        (ModuleCat.restrictScalars ((specMap R A).stalkMap q).hom)) ≪≫ ?_
  refine Functor.isoWhiskerLeft (tilde.functor (CommRingCat.of A))
      (Functor.associator _ _ _) ≪≫ ?_
  refine (Functor.associator (tilde.functor (CommRingCat.of A)) _ _).symm ≪≫ ?_
  refine Functor.isoWhiskerRight
      (tildeStalkRestrictScalarsIso (CommRingCat.of A) q (specStalkRingEquiv A q)
        (algebraMap A (Localization.AtPrime q.asIdeal))
        (specStalkRingIso_comp_germ_eq_algebraMap A q)) _ ≪≫ ?_
  refine Functor.associator _ _ _ ≪≫ ?_
  refine Functor.isoWhiskerLeft
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.AtPrime q.asIdeal))) ?_
  refine Functor.isoWhiskerLeft _
      (ModuleCat.restrictScalarsComp'.{u} ((specMap R A).stalkMap q).hom
        (AlgebraicGeometry.ringCatStalkRingEquiv
          (X := Spec (CommRingCat.of A)) q).symm.toRingHom _ rfl).symm ≪≫ ?_
  exact (ModuleCat.restrictScalarsComp'.{u} _ (specStalkRingEquiv A q).toRingHom _
      (relativeStalkRingHom_eq_algebraMap R A q).symm).symm ≪≫
    ModuleCat.restrictScalarsComp'.{u} (baseStalkRingEquiv R A q).toRingHom
      (algebraMap (Localization.AtPrime (Ideal.under R q.asIdeal))
        (Localization.AtPrime q.asIdeal)) _ rfl

/-- **The relative stalk complex of `M̃^•` at a prime `q` of `A`.** It is the localisation
`A_q ⊗_A M^•` of `M^•`, read over `R_{q ∩ R}` and then over the local ring of `Spec R` at
`q ∩ R`. This is `relativeStalkTildeFunctorIso` applied degreewise. -/
def relativeStalkComplexTildeIso (q : PrimeSpectrum A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    letI : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
        (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
    relativeStalkComplex (specMap R A) (Stacks.AffineTilde.tildeComplex M) q ≅
      (CochainComplex.restrictScalars (baseStalkRingEquiv R A q).toRingHom).obj
        ((CochainComplex.restrictScalars
            (algebraMap (Localization.AtPrime (Ideal.under R q.asIdeal))
              (Localization.AtPrime q.asIdeal))).obj
          ((CochainComplex.extendScalars
            (algebraMap A (Localization.AtPrime q.asIdeal))).obj M)) :=
  letI : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
  letI : (Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec (CommRingCat.of A)) q).Additive :=
    AlgebraicGeometry.modulesStalkFunctor_additive (X := Spec (CommRingCat.of A)) q
  (NatIso.mapHomologicalComplex (relativeStalkTildeFunctorIso R A q)
    (ComplexShape.up ℤ)).app M

/-! ### Tor amplitude over the base of an associated sheaf -/

/-- **The single-prime form of the bridge.** The relative stalk complex of `M̃^•` at a prime `q`
of `A` has Tor amplitude in `[a, b]` over the local ring of `Spec R` at `q ∩ R` if and only if
the localisation of `M^•` at `q` has Tor amplitude in `[a, b]` over `R_{q ∩ R}`.

The relative stalk complex is that localisation by `relativeStalkComplexTildeIso`, the change of
coefficient ring along `AlgebraicGeometry.Spec.stalkIso` is harmless because it is a ring
isomorphism, and the two Tor-amplitude conventions are compared by
`hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF`. -/
theorem hasTorAmplitudeCanonicalLift_relativeStalkComplex_tilde_iff (q : PrimeSpectrum A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) :
    HasTorAmplitudeCanonicalLift.{u, u, u}
        (DerivedCategory.Q.obj
          (relativeStalkComplex (specMap R A) (Stacks.AffineTilde.tildeComplex M) q)) a b ↔
      HasTorAmplitudeAt R M q.asIdeal a b := by
  let : Algebra (Localization.AtPrime (Ideal.under R q.asIdeal))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (Ideal.under R q.asIdeal) q.asIdeal
  refine Iff.trans ⟨hasTorAmplitudeCanonical_of_moduleLift _ a b,
    hasTorAmplitudeCanonical_moduleLift _ a b⟩ ?_
  refine Iff.trans ⟨hasTorAmplitudeCanonical_of_iso
      (DerivedCategory.Q.mapIso (relativeStalkComplexTildeIso R A q M)) a b,
    hasTorAmplitudeCanonical_of_iso
      (DerivedCategory.Q.mapIso (relativeStalkComplexTildeIso R A q M).symm) a b⟩ ?_
  exact (hasTorAmplitudeCanonical_restrictScalars_ringEquiv_iff
    (baseStalkRingEquiv R A q) _ a b).trans (hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF _ a b)

/-- **Tor amplitude over the base of `M̃^•` is a condition at the primes of `A`.** The sheaf
`M̃^•` has Tor amplitude in `[a, b]` over `f : Spec A ⟶ Spec R` if and only if for every prime
`q` of `A` the localisation of `M^•` at `q` has Tor amplitude in `[a, b]` over `R_{q ∩ R}`.

`AlgebraicGeometry.HasTorAmplitudeOver` asks only for *some* complex representing the object; by
`AlgebraicGeometry.relativeStalkAmplitude_of_derivedIso` the stalkwise bound does not depend on
that choice, so `M̃^•` itself may be used. -/
theorem hasTorAmplitudeOver_tildeComplex_iff_forall_isPrime
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) :
    HasTorAmplitudeOver (specMap R A)
        (DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M)) a b ↔
      ∀ (q : Ideal A) [q.IsPrime], HasTorAmplitudeAt R M q a b := by
  constructor
  · intro ⟨K, ⟨eK⟩, hK⟩ q hq
    exact (hasTorAmplitudeCanonicalLift_relativeStalkComplex_tilde_iff R A ⟨q, hq⟩ M a b).1
      (relativeStalkAmplitude_of_derivedIso (specMap R A) a b eK hK ⟨q, hq⟩)
  · exact fun h => ⟨Stacks.AffineTilde.tildeComplex M, ⟨Iso.refl _⟩, fun x =>
      (hasTorAmplitudeCanonicalLift_relativeStalkComplex_tilde_iff R A x M a b).2
        (@h (x : PrimeSpectrum A).asIdeal (x : PrimeSpectrum A).isPrime)⟩

/-- **Stacks 0DHY read on the stalkwise side.** The sheaf `M̃^•` has Tor amplitude in `[a, b]`
over `f : Spec A ⟶ Spec R` if and only if `M^•`, read as a complex of `R`-modules, has Tor
amplitude in `[a, b]` over `R`.

The condition at the primes of `A` produced by
`hasTorAmplitudeOver_tildeComplex_iff_forall_isPrime` is the module side of Stacks 0DHY,
`hasTorAmplitudeCanonical_restrictScalars_iff_forall_isPrime`. -/
theorem hasTorAmplitudeOver_tildeComplex_iff (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) :
    HasTorAmplitudeOver (specMap R A)
        (DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M)) a b ↔
      HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) a b :=
  (hasTorAmplitudeOver_tildeComplex_iff_forall_isPrime R A M a b).trans
    (hasTorAmplitudeCanonical_restrictScalars_iff_forall_isPrime R A M a b).symm

/-- **Finite Tor dimension over the base of an associated sheaf.** The sheaf `M̃^•` has Tor
amplitude over `f : Spec A ⟶ Spec R` in some interval if and only if `M^•`, read as a complex of
`R`-modules, has finite Tor dimension over `R`. -/
theorem exists_hasTorAmplitudeOver_tildeComplex_iff (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (∃ a b : ℤ, HasTorAmplitudeOver (specMap R A)
        (DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M)) a b) ↔
      HasFiniteTorDimensionCanonical R (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) :=
  (exists_congr fun a => exists_congr fun b =>
      hasTorAmplitudeOver_tildeComplex_iff R A M a b).trans
    (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical R _).symm

section RelativeRingedSpace

open Stacks.Cohomology.TorAmplitude (LocallyHasFiniteTorDimension)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] Stacks.Cohomology.TorAmplitude.restrictModules_preservesFiniteLimits
  Stacks.Cohomology.TorAmplitude.restrictModules_preservesFiniteColimits

/-- **The identification of the two relative structures.** The sheaf `M̃^•` has Tor amplitude in
`[a, b]` over `f : Spec A ⟶ Spec R` in the stalkwise sense of
`AlgebraicGeometry.HasTorAmplitudeOver` if and only if the complex of `f^{-1}𝒪_{Spec R}`-modules
attached to `M^•` has Tor amplitude in `[a, b]` over `f^{-1}𝒪_{Spec R}`.

Both sides are Stacks 0DHY's two readings of the same hypothesis, and they are compared through
the module side: the left by `hasTorAmplitudeOver_tildeComplex_iff` and the right by Stacks 0DHY
part (1). -/
theorem hasTorAmplitudeOver_iff_hasTorAmplitude_relativeComplex
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) :
    HasTorAmplitudeOver (specMap R A)
        (DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M)) a b ↔
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude (relativeRingedSpace R A)
        (DerivedCategory.Q.obj (relativeComplex R A M)) a b :=
  (hasTorAmplitudeOver_tildeComplex_iff R A M a b).trans
    (hasTorAmplitude_relativeComplex_iff R A M a b).symm

/-- **The finite-Tor-dimension form of the identification.** The sheaf `M̃^•` has Tor amplitude
over `f : Spec A ⟶ Spec R` in some interval if and only if the complex of
`f^{-1}𝒪_{Spec R}`-modules attached to `M^•` locally has finite Tor dimension. -/
theorem exists_hasTorAmplitudeOver_iff_locallyHasFiniteTorDimension
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (∃ a b : ℤ, HasTorAmplitudeOver (specMap R A)
        (DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M)) a b) ↔
      LocallyHasFiniteTorDimension (relativeRingedSpace R A)
        (DerivedCategory.Q.obj (relativeComplex R A M)) :=
  (exists_hasTorAmplitudeOver_tildeComplex_iff R A M).trans
    (locallyHasFiniteTorDimension_relativeComplex_iff R A M).symm

end RelativeRingedSpace

/-! ### Finite Tor dimension at an arbitrary certified derived tensor product -/

/-- **Finite Tor dimension does not depend on the certified derived tensor product.** For any
bifunctor on `D(S)` certified as a derived tensor product in the sense of Stacks 0652, finite
Tor dimension read off it is finite Tor dimension at the canonical derived tensor product of
Stacks 0BYI.

Both sides are the existence of a representative by a bounded complex of flat modules
(Stacks 0654), which `StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative` proves
over an arbitrary certificate. This is the form in which a statement quantified over a derived
tensoring datum, such as Stacks 0DHX, asks for its finite-Tor-dimension hypothesis. -/
theorem hasFiniteTorDimension_iff_hasFiniteTorDimensionCanonical {S : Type u} [CommRing S]
    {derivedTensor : DerivedCategory (ModuleCat.{u} S) ⥤
      DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} S)}
    (comparison : ∀ N : ModuleCat.{u} S,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} S,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{u} S)) :
    HasFiniteTorDimension derivedTensor comparison isLeftDerived K ↔
      HasFiniteTorDimensionCanonical S K :=
  (exists_congr fun a => exists_congr fun b =>
      (hasTorAmplitude_iff_hasFlatRepresentative comparison isLeftDerived K a b).trans
        (hasTorAmplitudeCanonical_iff_hasFlatRepresentative S K a b).symm).trans
    (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical S K).symm

end AlgebraicGeometry.AffineRelativeTorAmplitude

end
