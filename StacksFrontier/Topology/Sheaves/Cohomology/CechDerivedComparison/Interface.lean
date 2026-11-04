module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DeltaFunctorOfPresheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor

/-!
# The Čech-to-derived comparison of Stacks 01EN, over the δ-functor of Stacks 01EK

Stacks 01EN compares the Čech cohomology δ-functor of a covering `𝒰` of an open `U` of a
ringed space — the δ-functor of Stacks 01EK, built on the Čech complex functor of Stacks 01EJ —
with the right derived functors of its degree-zero part. This file sets up that comparison
*over those two interfaces*, rather than over the bespoke Čech complex
`Stacks.Cohomology.CechDerived.cechComplexFunctor`, and discharges the parts of it that are
available.

`CechDerivedComparison` bundles the whole assertion: that presheaves of modules have enough
injectives, that degree-zero Čech cohomology is left exact, that the Čech complex functor is
exact, that every short exact sequence admits a compatible short exact sequence of injective
resolutions, and that there is a δ-functor whose components are the right derived functors of
degree-zero Čech cohomology, whose connecting morphisms are computed by those resolutions, and
which is uniquely isomorphic to the Čech δ-functor over
`CategoryTheory.Functor.toRightDerivedZero`.

## The universe constraint

The comparison here is stated at a single universe.  Nothing in the mathematics forces that:
`PresheafOfModules.enoughInjectivesU` and `isGrothendieckAbelianU` give enough injectives at
four independent universes, over `PresheafOfModules.hasSeparatorU`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GrothendieckAbelian.lean`).  The four-universe
form of this whole structure is `Stacks.Cohomology.CechComparisonU.CechDerivedComparison`, and
`cechDerivedComparisonEquiv` identifies it with this one at `u = r = v = w`, with both round
trips `rfl`.

## Main definitions

* `Modules`, `SectionModules`: presheaves of `O`-modules and modules over the sections on the
  covered open.
* `cechCohomologyFunctor`, `cechCohomologyZeroFunctor`: Čech cohomology of the covering, from
  the complex functor of Stacks 01EJ; `cechDeltaFunctor` is the δ-functor of Stacks 01EK.
* `ResolutionShortComplex`: a short exact sequence of injective resolutions lifting a short
  exact sequence of presheaves, whose image under degree-zero Čech cohomology is again short
  exact.
* `rightDerivedConnecting`: the connecting morphism of the higher right derived functors
  computed from such a sequence of resolutions.
* `CechDerivedComparison`: the full assertion of Stacks 01EN, first part.

## Main results

The fields of `CechDerivedComparison` that are available are proved here:

* `enoughInjectives_modules`: presheaves of `O`-modules have enough injectives.
* `preservesFiniteLimits_cechCohomologyZeroFunctor`: degree-zero Čech cohomology is left exact.
* `cechComplexFunctor_shortExact`: the Čech complex functor carries short exact sequences of
  presheaves to short exact sequences of complexes.
* `derivedDeltaFunctor`, `derivedDeltaFunctor_functor`: a cohomological δ-functor whose
  degree-`n` component is, on the nose, the `n`-th right derived functor of degree-zero Čech
  cohomology.

## What is still missing

Two fields of `CechDerivedComparison` have no proof here, and neither is a universe or
statability obstruction:

* `resolutions`, the injective horseshoe at the level of objects. The horseshoe for *complexes*
  is available as `CategoryTheory.ShortComplex.ShortExact.exists_shortExact_injectiveResolution`
  (Stacks 013T); what is needed is its object-level form, transported along
  `CategoryTheory.InjectiveResolution.toCochainComplexResolution` and
  `CochainComplex.InjectiveResolution.toNatResolution`, together with the observation that the
  middle term of the horseshoe is a degreewise biproduct, so that the sequence of resolutions is
  degreewise split and therefore stays short exact under the additive functor
  `cechCohomologyZeroFunctor`.
* `derivedδ_eq`, the identification of the connecting morphism of `derivedDeltaFunctor` — which
  is the one attached to a distinguished triangle of `D⁺` — with `rightDerivedConnecting`,
  the one computed degreewise on a short exact sequence of injective resolutions.

The remaining three fields `deltaIso`, `normalized` and `unique` follow from universality of
both δ-functors exactly as in `Stacks.Cohomology.CechComparison.deltaIso`, once the Čech
δ-functor of Stacks 01EK is known to be effaceable. Effaceability is proved in
`Stacks.Cohomology.CechGodement.effaceable_cechDeltaFunctor` for the bespoke Čech complex
`Stacks.Cohomology.CechDerived.cechComplexFunctor`, not for the one of Stacks 01EJ used here.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 01EK](https://stacks.math.columbia.edu/tag/01EK)
* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
* [Stacks Project, Tag 013T](https://stacks.math.columbia.edu/tag/013T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechExactFunctor (presheafCechComplexFunctor)

universe u

namespace Stacks.Cohomology.CechComparison

attribute [local instance] HasDerivedCategory.standard

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, u} (TopCat.of X))

/-- Presheaves of modules over the structure sheaf. -/
abbrev Modules := PresheafOfModules.{u} O.obj

/-- Modules over the ring of sections on the covered open. -/
abbrev SectionModules := ModuleCat.{u} (O.obj.obj (op 𝒰.U))

/-- **Presheaves of modules on the open-set site have enough injectives**, the input Stacks
01EN takes from Stacks 01DV. Mathlib's `PresheafOfModules.instIsGrothendieckAbelian` makes the
category Grothendieck abelian, and a Grothendieck abelian category has enough injectives
(Stacks 079H). This is the statement that fixes the universes: the instance requires the site,
the structure ring and the module universe to agree. -/
instance enoughInjectives_modules : EnoughInjectives (Modules.{u} O) :=
  inferInstance

/-- The Čech complex functor of Stacks 01EJ is additive, being exact. A direct computation of
`map_add` needs a transparency option; exactness gives it for free. -/
instance cechComplexFunctor_additive :
    (presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).Additive :=
  exactFunctor_le_additiveFunctor _ _ _
    (CechExactFunctor.presheafCechComplexFunctor_exact O.obj 𝒰.U 𝒰.obj 𝒰.le)

/-- Čech cohomology of the covering `𝒰` in degree `n`, with values in modules over the ring of
sections on the covered open: the degree-`n` cohomology of the Čech complex functor of Stacks
01EJ. -/
def cechCohomologyFunctor (n : ℕ) : Modules.{u} O ⥤ SectionModules.{u} O 𝒰 :=
  presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le ⋙
    HomologicalComplex.homologyFunctor _ (up ℕ) n

/-- Degree-zero Čech cohomology of the covering, the functor Stacks 01EN right-derives. -/
abbrev cechCohomologyZeroFunctor := cechCohomologyFunctor.{u} O 𝒰 0

/-- **The Čech cohomology δ-functor of Stacks 01EK**, including its natural connecting
morphisms. -/
abbrev cechDeltaFunctor : DeltaFunctor (Modules.{u} O) (SectionModules.{u} O 𝒰) :=
  (CechCohomologyDelta.presheafCechCohomologyDeltaFunctor.{u, u, u, u}
    O.obj 𝒰.U 𝒰.obj 𝒰.le).val

/-- The component functors of the Čech δ-functor of Stacks 01EK are the Čech cohomology
functors built from the complex of Stacks 01EJ. -/
theorem cechDeltaFunctor_functor (n : ℕ) :
    (cechDeltaFunctor.{u} O 𝒰).functor n = cechCohomologyFunctor.{u} O 𝒰 n :=
  (CechCohomologyDelta.presheafCechCohomologyDeltaFunctor.{u, u, u, u}
    O.obj 𝒰.U 𝒰.obj 𝒰.le).property n

/-- Čech cohomology of the covering in each degree is an additive functor. -/
instance cechCohomologyFunctor_additive (n : ℕ) :
    (cechCohomologyFunctor.{u} O 𝒰 n).Additive := by
  dsimp only [cechCohomologyFunctor]
  infer_instance

/-- **Degree-zero Čech cohomology is left exact.** It is the degree-zero functor of the
δ-functor of Stacks 01EK, and the long exact sequence makes `0 → Ȟ⁰(X₁) → Ȟ⁰(X₂) → Ȟ⁰(X₃)`
exact for every short exact sequence of presheaves of modules. -/
instance preservesFiniteLimits_cechCohomologyZeroFunctor :
    PreservesFiniteLimits (cechCohomologyZeroFunctor.{u} O 𝒰) := by
  have h : PreservesFiniteLimits ((cechDeltaFunctor.{u} O 𝒰).functor 0) :=
    CechDerived.preservesFiniteLimits_functor_zero _
  rw [cechDeltaFunctor_functor.{u} O 𝒰 0] at h
  exact h

/-- **The Čech complex functor carries short exact sequences to short exact sequences**, by the
exactness of Stacks 01EJ. This is the `cechExact` field of `CechDerivedComparison`. -/
theorem cechComplexFunctor_shortExact (S : ShortComplex (Modules.{u} O)) (hS : S.ShortExact) :
    (S.map (presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le)).ShortExact :=
  CechCohomologyDelta.presheafCechComplexFunctor_shortExact.{u, u, u, u}
    O.obj 𝒰.U 𝒰.obj 𝒰.le S hS

/-- A short exact sequence of injective resolutions lifting a short exact sequence of
presheaves, whose image under degree-zero Čech cohomology is short exact. Such resolutions
are supplied by the injective horseshoe construction (the sequence is split in each degree). -/
structure ResolutionShortComplex (S : ShortComplex (Modules.{u} O)) where
  /-- An injective resolution of the first term. -/
  J₁ : InjectiveResolution S.X₁
  /-- An injective resolution of the second term. -/
  J₂ : InjectiveResolution S.X₂
  /-- An injective resolution of the third term. -/
  J₃ : InjectiveResolution S.X₃
  /-- The first map of the lifted sequence of resolutions. -/
  f : J₁.cocomplex ⟶ J₂.cocomplex
  /-- The second map of the lifted sequence of resolutions. -/
  g : J₂.cocomplex ⟶ J₃.cocomplex
  /-- The lifted sequence is a complex. -/
  zero : f ≫ g = 0
  /-- The first square commutes. -/
  comm_f : J₁.ι.f 0 ≫ f.f 0 = S.f ≫ J₂.ι.f 0
  /-- The second square commutes. -/
  comm_g : J₂.ι.f 0 ≫ g.f 0 = S.g ≫ J₃.ι.f 0
  /-- The lifted sequence is short exact. -/
  shortExact : (ShortComplex.mk f g zero).ShortExact
  /-- Degree-zero Čech cohomology, applied degreewise, keeps it short exact; this holds because
  the horseshoe sequence is split in each degree. -/
  mappedShortExact : ((ShortComplex.mk f g zero).map
    ((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℕ))).ShortExact

/-- The standard connecting morphism of the actual higher right-derived functors,
computed using a compatible short exact sequence of injective resolutions. -/
def rightDerivedConnecting {S : ShortComplex (Modules.{u} O)}
    (J : ResolutionShortComplex.{u} O 𝒰 S) (n : ℕ) :
    ((cechCohomologyZeroFunctor.{u} O 𝒰).rightDerived n).obj S.X₃ ⟶
      ((cechCohomologyZeroFunctor.{u} O 𝒰).rightDerived (n + 1)).obj S.X₁ :=
  (J.J₃.isoRightDerivedObj (cechCohomologyZeroFunctor.{u} O 𝒰) n).hom ≫
    J.mappedShortExact.δ n (n + 1) rfl ≫
    (J.J₁.isoRightDerivedObj (cechCohomologyZeroFunctor.{u} O 𝒰) (n + 1)).inv

/-- **A cohomological δ-functor realizing the right derived functors of degree-zero Čech
cohomology.** This is the `derivedDeltaFunctor` field of `CechDerivedComparison`: the δ-functor
`Stacks.Cohomology.CechDelta.rightDerivedDeltaFunctor` of Stacks 05TE, whose connecting
morphisms come from the long exact sequence of `D⁺` and whose components are Mathlib's
`CategoryTheory.Functor.rightDerived`. -/
def derivedDeltaFunctor : DeltaFunctor (Modules.{u} O) (SectionModules.{u} O 𝒰) :=
  CechDelta.rightDerivedDeltaFunctor (cechCohomologyZeroFunctor.{u} O 𝒰)

/-- The degree-`n` component of `derivedDeltaFunctor` is, on the nose, the `n`-th right derived
functor of degree-zero Čech cohomology. This is the `derivedFunctor_eq` field of
`CechDerivedComparison`. -/
theorem derivedDeltaFunctor_functor (n : ℕ) :
    (derivedDeltaFunctor.{u} O 𝒰).functor n =
      (cechCohomologyZeroFunctor.{u} O 𝒰).rightDerived n :=
  rfl

/-- Data of the canonical Čech-to-derived δ-functor isomorphism. Existence of
injectives and left exactness are conclusions, not assumptions on the ringed space.
The comparison is an isomorphism of the existing δ-functor of Tag 01EK, unique
with its canonical degree-zero component. The target has the actual right-derived
functors and the connecting morphisms computed by injective resolutions. -/
structure CechDerivedComparison where
  /-- Presheaves of modules have enough injectives; a conclusion, not an assumption. -/
  [enoughInjectives : EnoughInjectives (Modules.{u} O)]
  /-- Degree-zero Čech cohomology is left exact. -/
  leftExact : PreservesFiniteLimits (cechCohomologyZeroFunctor.{u} O 𝒰)
  /-- The Čech complex functor of Stacks 01EJ is exact. -/
  cechExact : ∀ (S : ShortComplex (Modules.{u} O)), S.ShortExact →
    (S.map (presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le)).ShortExact
  /-- Every short exact sequence of presheaves of modules admits a compatible short exact
  sequence of injective resolutions. -/
  resolutions : ∀ (S : ShortComplex (Modules.{u} O)), S.ShortExact →
    Nonempty (ResolutionShortComplex.{u} O 𝒰 S)
  /-- A δ-functor realizing the right derived functors of degree-zero Čech cohomology. -/
  derivedDeltaFunctor : DeltaFunctor (Modules.{u} O) (SectionModules.{u} O 𝒰)
  /-- Its components are Mathlib's right derived functors. -/
  derivedFunctor_eq (n : ℕ) : derivedDeltaFunctor.functor n =
    (cechCohomologyZeroFunctor.{u} O 𝒰).rightDerived n
  /-- Its connecting morphisms are the ones computed by injective resolutions. -/
  derivedδ_eq {S : ShortComplex (Modules.{u} O)}
      (hS : S.ShortExact) (J : ResolutionShortComplex.{u} O 𝒰 S) (n : ℕ) :
    (eqToHom (derivedFunctor_eq n).symm).app S.X₃ ≫ derivedDeltaFunctor.δ hS n ≫
      (eqToHom (derivedFunctor_eq (n + 1))).app S.X₁ =
        rightDerivedConnecting.{u} O 𝒰 J n
  /-- The comparison itself, an isomorphism of δ-functors. -/
  deltaIso : cechDeltaFunctor.{u} O 𝒰 ≅ derivedDeltaFunctor
  /-- It is normalized by `CategoryTheory.Functor.toRightDerivedZero` in degree zero. -/
  normalized :
    eqToHom (cechDeltaFunctor_functor.{u} O 𝒰 0).symm ≫ deltaIso.hom.app 0 ≫
        eqToHom (derivedFunctor_eq 0) =
      (cechCohomologyZeroFunctor.{u} O 𝒰).toRightDerivedZero
  /-- It is the unique normalized one. -/
  unique : ∀ e : cechDeltaFunctor.{u} O 𝒰 ≅ derivedDeltaFunctor,
    eqToHom (cechDeltaFunctor_functor.{u} O 𝒰 0).symm ≫ e.hom.app 0 ≫
        eqToHom (derivedFunctor_eq 0) =
      (cechCohomologyZeroFunctor.{u} O 𝒰).toRightDerivedZero → e = deltaIso

end Stacks.Cohomology.CechComparison

end
