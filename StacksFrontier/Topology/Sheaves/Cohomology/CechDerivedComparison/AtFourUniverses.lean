module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.CechFunctorAtFourUniverses
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.CompatibleInjectiveResolutions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Čech-to-derived comparison of Stacks 01EN, at four independent universes

Let `X` be a space, `O` a sheaf of rings on `X` and `𝒰` an indexed open covering of an open
`U ⊆ X`. `Stacks.Cohomology.CechComparison.CechDerivedComparison` states the comparison of
Stacks 01EN —
that Čech cohomology of `𝒰` on presheaves of `O`-modules is the right derived functor of its
degree-zero part — with the space universe, the ring universe, the module universe and the
covering index universe all equal. This file states it with the four independent, the common
module universe being `max u r v w`, which is the generality in which the Čech-to-cohomology
spectral sequence of [Stacks, Tag 01ES] and its consumers need it.

## The universe situation

The module docstring of the monomorphic `Stacks.Cohomology.CechComparison` interface records
the four
universes as *identified* by the `EnoughInjectives` input, on the grounds that
`PresheafOfModules.instIsGrothendieckAbelian` needs the site, the presheaf of rings and the
modules in one universe. That is true of Mathlib's instance and false of the statement: the
separator that the instance is really asking for is already available with the three universes
independent, as `PresheafOfModules.hasSeparatorU` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GrothendieckAbelian.lean`, and the other three
fields of `CategoryTheory.IsGrothendieckAbelian` are universe-independent as Mathlib proves
them. So `enoughInjectivesU` below gives enough injectives on `PresheafOfModules.{max u r t} R`
over `RingCat.{r}` on any `u`-small site, and `enoughInjectives_modules` specializes it to the
open-set site at the four universes of Stacks 01EN. Nothing in the comparison identifies the
universes.

What is *not* available here is effaceability of the Čech δ-functor. The three fields that need
it are stated and proved under `[(CechSpectral.cechDeltaFunctor O 𝒰).Effaceable]` as a
hypothesis, so that the whole four-universe comparison is reduced to that one instance by
`cechDerivedComparisonOfEffaceable`. The Godement argument proving it is
`Stacks.Cohomology.CechGodementU.isZero_homology_god`, stated at the four universes directly
(the Godement sections `∀ W ≤ V, M(W)` live in the module universe).

## Main definitions

* `PresheafOfModules.isGrothendieckAbelianU`, `PresheafOfModules.enoughInjectivesU`: presheaves
  of modules are Grothendieck abelian and have enough injectives, with the site, ring and module
  universes independent.
* `ResolutionShortComplex`, `rightDerivedConnecting`, `derivedDeltaFunctor`: the ingredients of
  the comparison, at the four universes.
* `CechDerivedComparison`: the full assertion of Stacks 01EN, first part, at the four universes.
* `cechDerivedComparisonOfEffaceable`: the comparison, from effaceability of the Čech δ-functor
  and the identification of the connecting morphisms.

## Main results

* `enoughInjectives_modules`: presheaves of `O`-modules have enough injectives at the four
  universes; this is what the monomorphic file's docstring reports as impossible.
* `preservesFiniteLimits_cechCohomologyZeroFunctor`, `cechComplexFunctor_shortExact`,
  `nonempty_resolutionShortComplex`, `derivedDeltaFunctor_functor`: the fields of
  `CechDerivedComparison` that need no effaceability.
* `deltaIso`, `normalized_deltaIso`, `unique_deltaIso`: the three fields that do.
* `cechDerivedComparisonEquiv`: with the four universes equal, this structure and
  `Stacks.Cohomology.CechComparison.CechDerivedComparison` are in bijection by copying fields,
  both round trips being `rfl`.

## Implementation notes

The large dependent field types of `CechDerivedComparison` are factored into the reducible
abbreviations `CechExactProperty`, `ResolutionsProperty`, `DerivedConnectingProperty` and
`NormalizedProperty`; this is what keeps the structure declaration inside the default
elaboration budget.

The module universe handed to the Čech machinery of [Stacks, Tag 01EJ] and [Stacks, Tag 01EK] is
`max u r v w` rather than `v`, exactly as in `Stacks.Cohomology.CechSpectral`:
those functors land in modules at `max (module universe) w`, so feeding them `max u r v w` gives
back `max u r v w` and the four universes stay free.

Nothing here carries the tag `01EN`: the tag belongs on a complete `CechDerivedComparison`, and
the `derivedδ_eq` field is not proved in this repository yet.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 01EK](https://stacks.math.columbia.edu/tag/01EK)
* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
* [Stacks Project, Tag 013T](https://stacks.math.columbia.edu/tag/013T)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
* [Stacks Project, Tag 079H](https://stacks.math.columbia.edu/tag/079H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe t u r v w

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ RingCat.{r})
  [HasColimitsOfShape (Discrete C) AddCommGrpCat.{max u r t}]

/-- **Presheaves of modules over a presheaf of rings on a small site form a Grothendieck
abelian category**, with the site, ring and module universes independent. Mathlib's
`PresheafOfModules.instIsGrothendieckAbelian` requires all three to agree; local smallness,
filtered colimits and AB5 are already universe-independent as Mathlib proves them, and the
separator is `PresheafOfModules.hasSeparatorU`. -/
@[sga "4 V 2.5.2" "more general"]
theorem isGrothendieckAbelianU :
    IsGrothendieckAbelian.{max u r t} (PresheafOfModules.{max u r t} R) where
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun J _ _ ↦ ⟨⟨fun _ _ _ ↦ ⟨fun {F} ↦
    have : PreservesLimit F (colim (J := J) ⋙ toPresheaf R) :=
      preservesLimit_of_natIso _ (preservesColimitNatIso (toPresheaf R)).symm
    preservesLimit_of_reflects_of_preserves _ (toPresheaf R)⟩⟩⟩⟩
  hasSeparator := hasSeparatorU.{t, u, r} R

/-- **Presheaves of modules over a presheaf of rings on a small site have enough injectives**,
with the site, ring and module universes independent: the category is Grothendieck abelian, and
a Grothendieck abelian category has enough injectives (Stacks 079H).

Because the module universe appears as `max u r t`, universe unification cannot infer `t` from a
goal; apply this with explicit universe arguments, in the order `t`, `u`, `r`. -/
@[sga "3 I 3.1.2"]
theorem enoughInjectivesU : EnoughInjectives (PresheafOfModules.{max u r t} R) :=
  have := isGrothendieckAbelianU.{t, u, r} R
  inferInstance

end PresheafOfModules

namespace Stacks.Cohomology.CechComparisonU

attribute [local instance] HasDerivedCategory.standard

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, w} (TopCat.of X))

/-- Presheaves of modules over the structure sheaf, in an independent module universe. -/
abbrev Modules := PresheafOfModules.{v} O.obj

/-- Modules over the ring of sections on the covered open. -/
abbrev SectionModules := ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))

/-- **Presheaves of `O`-modules on a ringed space have enough injectives, with the space, ring,
module and covering index universes independent**: `PresheafOfModules.enoughInjectivesU` on the
site of opens, whose smallness in the space universe is what that theorem asks for. This is the
`enoughInjectives` field of `CechDerivedComparison`, and it is the input that the monomorphic
`Stacks.Cohomology.CechComparison` interface reports as identifying the four universes.

The covering is an argument only so that the index universe `w` occurs on its own in the
statement; the conclusion does not depend on it. -/
@[sga "4 V 2.5.2" "special case"]
theorem enoughInjectives_modules
    (_𝒱 : CechExactFunctor.CechOpenCover.{u, w} (TopCat.of X)) :
    EnoughInjectives (Modules.{u, r, max u r v w} O) :=
  PresheafOfModules.enoughInjectivesU.{max v w, u, r} O.obj

/-- Degree-zero Čech cohomology of the covering, the functor Stacks 01EN right-derives. -/
abbrev cechCohomologyZeroFunctor :
    Modules.{u, r, max u r v w} O ⥤ SectionModules.{u, r, max u r v w} O 𝒰 :=
  CechSpectral.cechCohomologyFunctor.{u, r, v, w} O 𝒰 0

/-- **Degree-zero Čech cohomology is left exact**, at four independent universes. It is the
degree-zero functor of the δ-functor of Stacks 01EK, and the long exact sequence makes
`0 → Ȟ⁰(X₁) → Ȟ⁰(X₂) → Ȟ⁰(X₃)` exact for every short exact sequence of presheaves of modules.
This is the `leftExact` field of `CechDerivedComparison`. -/
instance preservesFiniteLimits_cechCohomologyZeroFunctor :
    PreservesFiniteLimits (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) := by
  have h : PreservesFiniteLimits ((CechSpectral.cechDeltaFunctor.{u, r, v, w} O 𝒰).functor 0) :=
    CechDerived.preservesFiniteLimits_functor_zero _
  rw [CechSpectral.cechDeltaFunctor_functor.{u, r, v, w} O 𝒰 0] at h
  exact h

/-- **The Čech complex functor carries short exact sequences to short exact sequences**, at
four independent universes, by the exactness of Stacks 01EJ. This is the `cechExact` field of
`CechDerivedComparison`. -/
theorem cechComplexFunctor_shortExact (S : ShortComplex (Modules.{u, r, max u r v w} O))
    (hS : S.ShortExact) :
    (S.map (CechSpectral.cechComplexFunctor.{u, r, v, w} O 𝒰)).ShortExact :=
  CechCohomologyDelta.presheafCechComplexFunctor_shortExact.{u, r, max u r v w, w}
    O.obj 𝒰.U 𝒰.obj 𝒰.le S hS

/-- A short exact sequence of injective resolutions lifting a short exact sequence of
presheaves of `O`-modules, whose image under degree-zero Čech cohomology, applied degreewise,
is again short exact. Such resolutions are supplied by the injective horseshoe construction,
whose sequence is split in each degree. -/
structure ResolutionShortComplex (S : ShortComplex (Modules.{u, r, max u r v w} O)) where
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
    ((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).mapHomologicalComplex (up ℕ))).ShortExact

/-- **Every short exact sequence of presheaves of `O`-modules admits a compatible short exact
sequence of injective resolutions**, at four independent universes: the `ℕ`-indexed injective
horseshoe of Stacks 013T, whose degreewise splitting survives the additive functor
`cechCohomologyZeroFunctor`. This is the `resolutions` field of `CechDerivedComparison`. -/
theorem nonempty_resolutionShortComplex (S : ShortComplex (Modules.{u, r, max u r v w} O))
    (hS : S.ShortExact) : Nonempty (ResolutionShortComplex.{u, r, v, w} O 𝒰 S) := by
  let _ := enoughInjectives_modules.{u, r, v, w} O 𝒰
  obtain ⟨J₁, J₂, J₃, f, g, w', hse, hcomm_f, hcomm_g, hsplit⟩ :=
    hS.exists_injectiveResolution_shortExact
  exact ⟨{ J₁ := J₁
           J₂ := J₂
           J₃ := J₃
           f := f
           g := g
           zero := w'
           comm_f := hcomm_f
           comm_g := hcomm_g
           shortExact := hse
           mappedShortExact :=
             HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
               (((hsplit n).choose).map
                 (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)).shortExact }⟩

/-- The standard connecting morphism of the actual higher right-derived functors, computed
using a compatible short exact sequence of injective resolutions. -/
def rightDerivedConnecting [EnoughInjectives (Modules.{u, r, max u r v w} O)]
    {S : ShortComplex (Modules.{u, r, max u r v w} O)}
    (J : ResolutionShortComplex.{u, r, v, w} O 𝒰 S) (n : ℕ) :
    ((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerived n).obj S.X₃ ⟶
      ((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerived (n + 1)).obj S.X₁ :=
  (J.J₃.isoRightDerivedObj (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) n).hom ≫
    J.mappedShortExact.δ n (n + 1) rfl ≫
    (J.J₁.isoRightDerivedObj (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) (n + 1)).inv

/-- **A cohomological δ-functor realizing the right derived functors of degree-zero Čech
cohomology**, at four independent universes: the δ-functor of Stacks 05TE, whose connecting
morphisms come from the long exact sequence of `D⁺`. This is the `derivedDeltaFunctor` field of
`CechDerivedComparison`. -/
def derivedDeltaFunctor [EnoughInjectives (Modules.{u, r, max u r v w} O)] :
    DeltaFunctor (Modules.{u, r, max u r v w} O) (SectionModules.{u, r, max u r v w} O 𝒰) :=
  CechDelta.rightDerivedDeltaFunctor (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)

/-- The degree-`n` component of `derivedDeltaFunctor` is, on the nose, the `n`-th right derived
functor of degree-zero Čech cohomology. This is the `derivedFunctor_eq` field of
`CechDerivedComparison`. -/
theorem derivedDeltaFunctor_functor [EnoughInjectives (Modules.{u, r, max u r v w} O)] (n : ℕ) :
    (derivedDeltaFunctor.{u, r, v, w} O 𝒰).functor n =
      (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerived n :=
  rfl

/-! ### The field types

The four large dependent field types of `CechDerivedComparison`, factored out as reducible
abbreviations so that the structure declaration elaborates within the default budget.
-/

/-- The `cechExact` field type of `CechDerivedComparison`: the Čech complex functor of Stacks
01EJ carries short exact sequences of presheaves to short exact sequences of complexes. -/
abbrev CechExactProperty : Prop :=
  ∀ S : ShortComplex (Modules.{u, r, max u r v w} O), S.ShortExact →
    (S.map (CechSpectral.cechComplexFunctor.{u, r, v, w} O 𝒰)).ShortExact

/-- The `resolutions` field type of `CechDerivedComparison`: every short exact sequence of
presheaves of `O`-modules is covered by a compatible short exact sequence of injective
resolutions. -/
abbrev ResolutionsProperty : Prop :=
  ∀ S : ShortComplex (Modules.{u, r, max u r v w} O), S.ShortExact →
    Nonempty (ResolutionShortComplex.{u, r, v, w} O 𝒰 S)

/-- The `derivedδ_eq` field type of `CechDerivedComparison`: the connecting morphisms of a
δ-functor whose components are the right derived functors of degree-zero Čech cohomology are
the ones computed degreewise on a short exact sequence of injective resolutions. -/
abbrev DerivedConnectingProperty [EnoughInjectives (Modules.{u, r, max u r v w} O)]
    (G : DeltaFunctor (Modules.{u, r, max u r v w} O) (SectionModules.{u, r, max u r v w} O 𝒰))
    (hG : ∀ n : ℕ, G.functor n = (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerived n) :
    Prop :=
  ∀ {S : ShortComplex (Modules.{u, r, max u r v w} O)} (hS : S.ShortExact)
    (J : ResolutionShortComplex.{u, r, v, w} O 𝒰 S) (n : ℕ),
    (eqToHom (hG n).symm).app S.X₃ ≫ G.δ hS n ≫ (eqToHom (hG (n + 1))).app S.X₁ =
      rightDerivedConnecting.{u, r, v, w} O 𝒰 J n

/-- The `normalized` field type of `CechDerivedComparison`: an isomorphism from the Čech
δ-functor of Stacks 01EK to a realization of the right derived functors is normalized when its
degree-zero component is `CategoryTheory.Functor.toRightDerivedZero`. -/
abbrev NormalizedProperty [EnoughInjectives (Modules.{u, r, max u r v w} O)]
    (G : DeltaFunctor (Modules.{u, r, max u r v w} O) (SectionModules.{u, r, max u r v w} O 𝒰))
    (hG : ∀ n : ℕ, G.functor n = (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerived n)
    (e : CechSpectral.cechDeltaFunctor.{u, r, v, w} O 𝒰 ≅ G) : Prop :=
  eqToHom (CechSpectral.cechDeltaFunctor_functor.{u, r, v, w} O 𝒰 0).symm ≫ e.hom.app 0 ≫
      eqToHom (hG 0) =
    (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).toRightDerivedZero

/-! ### The comparison isomorphism

Universality of the right-derived δ-functor is unconditional; universality of the Čech
δ-functor is where effaceability enters, and it is the only input of Stacks 01EN that this file
carries as a hypothesis rather than proving.
-/

/-- **Universality of the right-derived δ-functor**, at four independent universes. Its
positive-degree components are the higher right derived functors of degree-zero Čech cohomology,
which differ from those of its own degree-zero component only by the canonical identification of
a left exact functor with its zeroth right derived functor; the higher right derived functors
vanish on injectives, so Stacks 010T applies. -/
instance isUniversal_derivedDeltaFunctor [EnoughInjectives (Modules.{u, r, max u r v w} O)] :
    (derivedDeltaFunctor.{u, r, v, w} O 𝒰).IsUniversal :=
  DeltaFunctor.isUniversal_of_functor_iso_rightDerived _ fun n ↦
    letI : ((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerived 0).Additive :=
      Functor.additive_of_iso
        (Functor.rightDerivedZeroIsoSelf (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)).symm
    (CechDelta.rightDerivedIsoOfIso
      (Functor.rightDerivedZeroIsoSelf (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰))
      (n + 1)).symm

/-- The degree-zero component of the comparison: the canonical identification of degree-zero
Čech cohomology with its own zeroth right derived functor, read through the identifications of
the degree-zero components of the two δ-functors. -/
def deltaIsoZero [EnoughInjectives (Modules.{u, r, max u r v w} O)] :
    (CechSpectral.cechDeltaFunctor.{u, r, v, w} O 𝒰).functor 0 ≅
      (derivedDeltaFunctor.{u, r, v, w} O 𝒰).functor 0 :=
  eqToIso (CechSpectral.cechDeltaFunctor_functor.{u, r, v, w} O 𝒰 0) ≪≫
    (Functor.rightDerivedZeroIsoSelf (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)).symm ≪≫
    eqToIso (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 0).symm

section Effaceable

variable [EnoughInjectives (Modules.{u, r, max u r v w} O)]
  [(CechSpectral.cechDeltaFunctor.{u, r, v, w} O 𝒰).Effaceable]

/-- **Universality of the Čech δ-functor, Stacks 010T**, at four independent universes, granted
its effaceability. -/
instance isUniversal_cechDeltaFunctor :
    (CechSpectral.cechDeltaFunctor.{u, r, v, w} O 𝒰).IsUniversal :=
  DeltaFunctor.isUniversal_of_effaceable _

/-- **The Čech-to-derived comparison of Stacks 01EN at four independent universes**, granted
effaceability of the Čech δ-functor: both δ-functors are universal, and universal δ-functors
with isomorphic degree-zero parts are isomorphic (Stacks 010U). This is the `deltaIso` field of
`CechDerivedComparison`. -/
def deltaIso :
    CechSpectral.cechDeltaFunctor.{u, r, v, w} O 𝒰 ≅ derivedDeltaFunctor.{u, r, v, w} O 𝒰 :=
  DeltaFunctor.IsUniversal.isoOfIso (deltaIsoZero.{u, r, v, w} O 𝒰)

/-- The comparison induces `deltaIsoZero` in degree zero. -/
theorem deltaIso_hom_app_zero :
    (deltaIso.{u, r, v, w} O 𝒰).hom.app 0 = (deltaIsoZero.{u, r, v, w} O 𝒰).hom :=
  DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero (deltaIsoZero.{u, r, v, w} O 𝒰)

/-- **The comparison is normalized by `CategoryTheory.Functor.toRightDerivedZero`**, at four
independent universes. This is the `normalized` field of `CechDerivedComparison`. -/
theorem normalized_deltaIso :
    NormalizedProperty.{u, r, v, w} O 𝒰 (derivedDeltaFunctor.{u, r, v, w} O 𝒰)
      (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰) (deltaIso.{u, r, v, w} O 𝒰) := by
  rw [NormalizedProperty, deltaIso_hom_app_zero]
  simp [deltaIsoZero]

/-- **The normalized comparison is unique**, at four independent universes, by Stacks 010U: an
isomorphism of universal δ-functors is determined by its degree-zero component. This is the
`unique` field of `CechDerivedComparison`. -/
theorem unique_deltaIso
    (e : CechSpectral.cechDeltaFunctor.{u, r, v, w} O 𝒰 ≅ derivedDeltaFunctor.{u, r, v, w} O 𝒰)
    (he : NormalizedProperty.{u, r, v, w} O 𝒰 (derivedDeltaFunctor.{u, r, v, w} O 𝒰)
      (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰) e) :
    e = deltaIso.{u, r, v, w} O 𝒰 :=
  DeltaFunctor.IsUniversal.iso_ext
    ((cancel_mono (eqToHom (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 0))).1
      ((cancel_epi
        (eqToHom (CechSpectral.cechDeltaFunctor_functor.{u, r, v, w} O 𝒰 0).symm)).1
          (he.trans (normalized_deltaIso.{u, r, v, w} O 𝒰).symm)))

end Effaceable

/-- **Data of the canonical Čech-to-derived δ-functor isomorphism of Stacks 01EN, at four
independent universes.** Existence of injectives and left exactness are conclusions, not
assumptions on the ringed space. The comparison is an isomorphism of the existing δ-functor of
Stacks 01EK, unique with its canonical degree-zero component; the target has the actual
right-derived functors and the connecting morphisms computed by injective resolutions. -/
structure CechDerivedComparison where
  /-- Presheaves of modules have enough injectives; a conclusion, not an assumption. -/
  [enoughInjectives : EnoughInjectives (Modules.{u, r, max u r v w} O)]
  /-- Degree-zero Čech cohomology is left exact. -/
  leftExact : PreservesFiniteLimits (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)
  /-- The Čech complex functor of Stacks 01EJ is exact. -/
  cechExact : CechExactProperty.{u, r, v, w} O 𝒰
  /-- Every short exact sequence of presheaves of modules admits a compatible short exact
  sequence of injective resolutions. -/
  resolutions : ResolutionsProperty.{u, r, v, w} O 𝒰
  /-- A δ-functor realizing the right derived functors of degree-zero Čech cohomology. -/
  derivedDeltaFunctor : DeltaFunctor (Modules.{u, r, max u r v w} O)
    (SectionModules.{u, r, max u r v w} O 𝒰)
  /-- Its components are Mathlib's right derived functors. -/
  derivedFunctor_eq (n : ℕ) : derivedDeltaFunctor.functor n =
    (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerived n
  /-- Its connecting morphisms are the ones computed by injective resolutions. -/
  derivedδ_eq : DerivedConnectingProperty.{u, r, v, w} O 𝒰 derivedDeltaFunctor derivedFunctor_eq
  /-- The comparison itself, an isomorphism of δ-functors. -/
  deltaIso : CechSpectral.cechDeltaFunctor.{u, r, v, w} O 𝒰 ≅ derivedDeltaFunctor
  /-- It is normalized by `CategoryTheory.Functor.toRightDerivedZero` in degree zero. -/
  normalized : NormalizedProperty.{u, r, v, w} O 𝒰 derivedDeltaFunctor derivedFunctor_eq deltaIso
  /-- It is the unique normalized one. -/
  unique : ∀ e : CechSpectral.cechDeltaFunctor.{u, r, v, w} O 𝒰 ≅ derivedDeltaFunctor,
    NormalizedProperty.{u, r, v, w} O 𝒰 derivedDeltaFunctor derivedFunctor_eq e → e = deltaIso

/-- **The whole four-universe comparison of Stacks 01EN, from two inputs**: effaceability of the
Čech δ-functor of Stacks 01EK and the identification of the connecting morphisms of the
right-derived δ-functor with the ones computed on injective resolutions. Every other field is
proved above at the four universes, so these two are exactly what the comparison still owes;
neither
is a universe obstruction. -/
def cechDerivedComparisonOfEffaceable
    [(CechSpectral.cechDeltaFunctor.{u, r, v, w} O 𝒰).Effaceable]
    (hδ : letI := enoughInjectives_modules.{u, r, v, w} O 𝒰
      DerivedConnectingProperty.{u, r, v, w} O 𝒰 (derivedDeltaFunctor.{u, r, v, w} O 𝒰)
        (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰)) :
    CechDerivedComparison.{u, r, v, w} O 𝒰 :=
  letI := enoughInjectives_modules.{u, r, v, w} O 𝒰
  { enoughInjectives := enoughInjectives_modules.{u, r, v, w} O 𝒰
    leftExact := preservesFiniteLimits_cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰
    cechExact := cechComplexFunctor_shortExact.{u, r, v, w} O 𝒰
    resolutions := nonempty_resolutionShortComplex.{u, r, v, w} O 𝒰
    derivedDeltaFunctor := derivedDeltaFunctor.{u, r, v, w} O 𝒰
    derivedFunctor_eq := derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰
    derivedδ_eq := hδ
    deltaIso := deltaIso.{u, r, v, w} O 𝒰
    normalized := normalized_deltaIso.{u, r, v, w} O 𝒰
    unique := unique_deltaIso.{u, r, v, w} O 𝒰 }

/-! ### Specialization to one universe

With the four universes equal, everything above is on the nose the development of
`Stacks.Cohomology.CechComparison`.
-/

section Specialization

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, u} (TopCat.of X))

/-- With all four universes equal, the presheaves of modules of this file are, on the nose,
those of `Stacks.Cohomology.CechComparison`. -/
theorem modules_eq_comparison :
    Modules.{u, u, u} O = CechComparison.Modules.{u} O :=
  rfl

/-- With all four universes equal, degree-zero Čech cohomology of this file is, on the nose,
the functor that `Stacks.Cohomology.CechComparison` right-derives. -/
theorem cechCohomologyZeroFunctor_eq_comparison :
    cechCohomologyZeroFunctor.{u, u, u, u} O 𝒰 =
      CechComparison.cechCohomologyZeroFunctor.{u} O 𝒰 :=
  rfl

/-- With all four universes equal, the compatible sequences of injective resolutions of this
file are those of `Stacks.Cohomology.CechComparison`: the two structures have
definitionally equal fields, so the bijection copies them across. -/
def resolutionShortComplexEquiv (S : ShortComplex (Modules.{u, u, u} O)) :
    ResolutionShortComplex.{u, u, u, u} O 𝒰 S ≃
      CechComparison.ResolutionShortComplex.{u} O 𝒰 S where
  toFun J :=
    { J₁ := J.J₁, J₂ := J.J₂, J₃ := J.J₃, f := J.f, g := J.g, zero := J.zero
      comm_f := J.comm_f, comm_g := J.comm_g, shortExact := J.shortExact
      mappedShortExact := J.mappedShortExact }
  invFun J :=
    { J₁ := J.J₁, J₂ := J.J₂, J₃ := J.J₃, f := J.f, g := J.g, zero := J.zero
      comm_f := J.comm_f, comm_g := J.comm_g, shortExact := J.shortExact
      mappedShortExact := J.mappedShortExact }
  left_inv _ := rfl
  right_inv _ := rfl

/-- With all four universes equal, the connecting morphism computed from a sequence of
resolutions is the one of `Stacks.Cohomology.CechComparison`. -/
theorem rightDerivedConnecting_eq_comparison
    {S : ShortComplex (Modules.{u, u, u} O)}
    (J : ResolutionShortComplex.{u, u, u, u} O 𝒰 S) (n : ℕ) :
    rightDerivedConnecting.{u, u, u, u} O 𝒰 J n =
      CechComparison.rightDerivedConnecting.{u} O 𝒰 (resolutionShortComplexEquiv O 𝒰 S J) n :=
  rfl

/-- **With all four universes equal, the comparison data of this file is the comparison data of
`Stacks.Cohomology.CechComparison`.** Every field of the four-universe structure is
definitionally the corresponding monomorphic field, so the bijection copies the data across and
both round trips are `rfl`; only the two fields quantifying over sequences of injective
resolutions are reindexed, along `resolutionShortComplexEquiv`, whose two directions are
themselves field-by-field copies. The four-universe statement is therefore a genuine
generalization of the monomorphic one, with no transport in the way: a construction of either
yields the other. -/
def cechDerivedComparisonEquiv :
    CechDerivedComparison.{u, u, u, u} O 𝒰 ≃ CechComparison.CechDerivedComparison.{u} O 𝒰 where
  toFun c :=
    { enoughInjectives := c.enoughInjectives
      leftExact := c.leftExact
      cechExact := c.cechExact
      resolutions := fun S hS ↦ (c.resolutions S hS).map (resolutionShortComplexEquiv O 𝒰 S)
      derivedDeltaFunctor := c.derivedDeltaFunctor
      derivedFunctor_eq := c.derivedFunctor_eq
      derivedδ_eq := fun hS J n ↦
        c.derivedδ_eq hS ((resolutionShortComplexEquiv O 𝒰 _).symm J) n
      deltaIso := c.deltaIso
      normalized := c.normalized
      unique := fun e he ↦ c.unique e he }
  invFun c :=
    { enoughInjectives := c.enoughInjectives
      leftExact := c.leftExact
      cechExact := c.cechExact
      resolutions := fun S hS ↦
        (c.resolutions S hS).map (resolutionShortComplexEquiv O 𝒰 S).symm
      derivedDeltaFunctor := c.derivedDeltaFunctor
      derivedFunctor_eq := c.derivedFunctor_eq
      derivedδ_eq := fun hS J n ↦ c.derivedδ_eq hS (resolutionShortComplexEquiv O 𝒰 _ J) n
      deltaIso := c.deltaIso
      normalized := c.normalized
      unique := fun e he ↦ c.unique e he }
  left_inv _ := rfl
  right_inv _ := rfl

end Specialization

end Stacks.Cohomology.CechComparisonU

end
