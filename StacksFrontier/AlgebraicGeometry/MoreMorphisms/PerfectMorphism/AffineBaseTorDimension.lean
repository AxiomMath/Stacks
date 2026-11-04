module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.DerivedTildeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.ChartRestrictScalars
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles

/-!
# The affine base case of the Tor-dimension half of Stacks 08EV

Let `φ : R ⟶ S` be a map of commutative rings and let `A` be an object of `D(𝒪_{Spec S})`
represented by the sheafification of a complex of `S`-modules. Then
`R(Spec φ)_*A` is the sheafification of that complex read over `R`, so its Tor amplitude over
`𝒪_{Spec R}` is the Tor amplitude of the complex over `R`, which is bounded by
[Stacks, Tag 0B66] as soon as `S` has finite Tor dimension over `R`. That is the affine case of
the Tor-dimension half of [Stacks, Tag 08EV], and this file proves it.

## Main results

* `AlgebraicGeometry.schemeDerivedPushforwardObjQIso`: **[Stacks, Tag 0G9N] for an affine morphism
  of schemes, as an object-level isomorphism.** For a complex `K` of quasi-coherent
  `𝒪_X`-modules, `Rf_*K` is the object represented by the termwise direct image `f_*K`.
* `AlgebraicGeometry.affinePushforwardTildeDerivedObjIso` and
  `...affinePushforwardTildeDerivedObjIso'`: **[Stacks, Tag 0A9F] at a complex.**
  `R(Spec φ)_*(M̃) ≅ (M restricted to R)~`, for `M` a complex of `S`-modules.
* `AlgebraicGeometry.hasTorAmplitude_schemeDerivedPushforward_tilde`: the Tor-amplitude estimate
  at a complex of modules, with the two intervals added.
* `AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_specMap`: **the affine base
  case.** If `S` has finite Tor dimension over `R`, if `A` is the sheafification of some complex
  of `S`-modules and if `A` has finite Tor dimension on `Spec S`, then `R(Spec φ)_*A` has finite
  Tor dimension on `Spec R`.

## Implementation notes

**No model crossing is needed.** [Stacks, Tag 0A9F] is formalized as
`AlgebraicGeometry.derivedTildeCompDerivedQuasicoherentPushforwardIso`, at the *locally small*
model of the derived categories and on the quasi-coherent subcategory `D_QCoh`, whereas
`AlgebraicGeometry.schemeDerivedPushforward` and [Stacks, Tag 08E9] are read at
`CategoryTheory.HasDerivedCategory.standard`; restating that isomorphism at an arbitrary model
would mean restating the other half of [Stacks, Tag 08D7] there too. The route taken here avoids
`D_QCoh` and derived sheafification entirely:

* [Stacks, Tag 0G9N] at an arbitrary model is already in the tree, as
  `AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom` — the comparison
  `f_*K ⟶ Rf_*K` is invertible for `K` a complex of quasi-coherent modules. At the standard model
  `AlgebraicGeometry.AnyModel.derivedPushforward` and `AlgebraicGeometry.schemeDerivedPushforward`
  are the *same functor by `rfl`*, both being the total right derived functor of degreewise direct
  image followed by localization, and likewise for the two units; so that statement applies to
  `schemeDerivedPushforward` directly. It is restated as an isomorphism of objects here, which is
  what a transport of Tor amplitude consumes.
* [Stacks, Tag 01I9] — `AlgebraicGeometry.pushforwardTildeIso` — is an isomorphism of *abelian*
  functors, so no derived category appears in it; applied degreewise by
  `CategoryTheory.NatIso.mapHomologicalComplex` it carries the termwise direct image of a
  sheafified complex to the sheafification of the complex with scalars restricted.
* [Stacks, Tag 08E9] (`AlgebraicGeometry.hasTorAmplitude_tilde_iff`) then reads the Tor amplitude
  of a sheafified complex off the module side, and it is already at the standard model.

The two `CategoryTheory.Functor.mapHomologicalComplexCompIso (Iso.refl _)` factors are the
identification of `(F ⋙ G).mapHomologicalComplex` with
`F.mapHomologicalComplex ⋙ G.mapHomologicalComplex`, which
`CategoryTheory.NatIso.mapHomologicalComplex` of [Stacks, Tag 01I9] does not produce on its own.

**The hypothesis on `φ`** is finite Tor dimension of `S` as an `R`-module, in the canonical
spelling `StacksDraft.TorAmplitude.HasTorAmplitudeCanonical` at the module placed in degree zero.
That is exactly the second clause of a perfect ring map, [Stacks, Tag 067H] (2), and it is what
`AlgebraicGeometry.Perfect.perfect_appLE` supplies for the chart ring map of a perfect morphism;
see `AlgebraicGeometry.hasFiniteTorDimensionCanonical_restrictScalars_appLE`, which performs that
derivation.

**The hypothesis on `A`** is that it is the sheafification of a complex of `S`-modules. It is
not an added hypothesis of [Stacks, Tag 08EV]: on an affine scheme an object of `D(𝒪_X)` with
quasi-coherent cohomology is of that form, which is the essential-surjectivity clause of
[Stacks, Tag 06Z0] (`Stacks.DerivedQCoh.exists_iso_derivedTildeEquiv_obj_of_isDQCoh`); it is
carried here rather than discharged, because that statement is phrased through
`Stacks.DerivedQCoh.derivedTildeEquiv` on `D(QCoh)` and the translation to the present spelling
is a separate step.

**No `@[stacks]` attribute is placed anywhere in this file.** The two Tor-amplitude statements
are the affine case of the Tor-dimension half of the *proof* of [Stacks, Tag 08EV] and no tag
states them. For the two isomorphisms the reason is the one already recorded in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardAnyModel.lean`:
[Stacks, Tag 0G9N] is stated for a quasi-compact quasi-separated morphism and what is available
here is the affine case; and [Stacks, Tag 0A9F] is stated as a correspondence between the whole of
`D_QCoh(𝒪_{Spec S})` and the whole of `D(S)` under the equivalences of [Stacks, Tag 06Z0], which
is already registered in full at
`AlgebraicGeometry.derivedTildeCompDerivedQuasicoherentPushforwardIso`, whereas what is below is
that correspondence at one object of each side.

## References

* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Tag 0B66](https://stacks.math.columbia.edu/tag/0B66)
* [Stacks Project, Tag 067H](https://stacks.math.columbia.edu/tag/067H)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.TorAmplitude StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Tag 0G9N for an affine morphism, as an isomorphism of objects -/

/-- **[Stacks, Tag 0G9N] for an affine morphism of schemes, as an isomorphism of objects.** For a
complex `K` of quasi-coherent `𝒪_X`-modules and `f : X ⟶ S` affine, `Rf_*K` is the object of
`D(𝒪_S)` represented by the termwise direct image `f_*K`.

The invertibility of the comparison is
`AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom`, which is stated at
an arbitrary model of the derived categories; at the standard model that model's derived direct
image and its unit are `AlgebraicGeometry.schemeDerivedPushforward` and
`AlgebraicGeometry.schemeDerivedPushforwardUnit` by `rfl`, which is why the invertibility is
transferred by a type ascription. -/
def schemeDerivedPushforwardObjQIso {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    (K : CochainComplex X.Modules ℤ) (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    (schemeDerivedPushforward f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((Scheme.Modules.pushforward f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
  haveI : IsIso ((schemeDerivedPushforwardUnit f).app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K)) :=
    AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom.{u + 1} f K hqc
  (schemeDerivedPushforward f).mapIso
      ((DerivedCategory.quotientCompQhIso X.Modules).app K).symm ≪≫
    (asIso ((schemeDerivedPushforwardUnit f).app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K))).symm ≪≫
    (Stacks.SmallDerivedCategory.mapHomotopyCategoryCompQhFactors
      (Scheme.Modules.pushforward f)).app K

/-! ### Tag 0A9F at a complex of modules -/

/-- **[Stacks, Tag 0A9F] at a complex of modules.** For `φ : R ⟶ S` and `M` a complex of
`S`-modules, the derived direct image along `Spec φ` of the sheafification of `M` is the
sheafification of `M` read as a complex of `R`-modules.

The sheafification of a complex of modules is a complex of quasi-coherent modules, so
`AlgebraicGeometry.schemeDerivedPushforwardObjQIso` computes the left-hand side termwise, and
[Stacks, Tag 01I9] (`AlgebraicGeometry.pushforwardTildeIso`) identifies the termwise direct image
degreewise. -/
def affinePushforwardTildeDerivedObjIso {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : CochainComplex (ModuleCat.{u} S) ℤ) :
    (schemeDerivedPushforward (Spec.map φ)).obj
        (DerivedCategory.Q.obj (((tilde.functor S).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) ≅
      (tilde.functor R).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) :=
  schemeDerivedPushforwardObjQIso (Spec.map φ)
      (((tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
      (fun n => inferInstanceAs ((tilde.functor S).obj (M.X n)).IsQuasicoherent) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)))
          (ComplexShape.up ℤ)).app M ≪≫
        (NatIso.mapHomologicalComplex (pushforwardTildeIso R S φ) (ComplexShape.up ℤ)).app M ≪≫
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (ModuleCat.restrictScalars φ.hom ⋙ tilde.functor R))
          (ComplexShape.up ℤ)).app M).symm) ≪≫
    ((tilde.functor R).mapDerivedCategoryFactors.app
      (((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)).symm

/-- **[Stacks, Tag 0A9F] at a complex of modules, with restriction of scalars read on derived
categories.** This is the shape in which the Tor-amplitude statements of
[Stacks, Tag 066K] and [Stacks, Tag 0B66] are phrased. -/
def affinePushforwardTildeDerivedObjIso' {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : CochainComplex (ModuleCat.{u} S) ℤ) :
    (schemeDerivedPushforward (Spec.map φ)).obj
        (DerivedCategory.Q.obj (((tilde.functor S).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) ≅
      (tilde.functor R).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj
          (DerivedCategory.Q.obj M)) :=
  affinePushforwardTildeDerivedObjIso φ M ≪≫
    (tilde.functor R).mapDerivedCategory.mapIso
      (((ModuleCat.restrictScalars φ.hom).mapDerivedCategoryFactors.app M).symm)

/-! ### The Tor-amplitude estimate -/

/-- **The affine base case of the Tor-dimension half of [Stacks, Tag 08EV], at a complex of
modules.** Let `φ : R ⟶ S`, let `M` be a complex of `S`-modules of Tor amplitude in `[a, b]` over
`S` and suppose `S`, placed in degree zero, has Tor amplitude in `[c, d]` over `R`. Then
`R(Spec φ)_*(M̃)` has Tor amplitude in `[a + c, b + d]` on `Spec R`.

[Stacks, Tag 0A9F] at a complex rewrites the left-hand side as the sheafification of `M` read
over `R`; [Stacks, Tag 08E9] reads its Tor amplitude off the module side; and
[Stacks, Tag 0B66] at `L = S[0]` adds the two intervals. -/
theorem hasTorAmplitude_schemeDerivedPushforward_tilde {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : CochainComplex (ModuleCat.{u} S) ℤ) (a b c d : ℤ)
    (hφ : letI : Algebra (R : Type u) (S : Type u) := φ.hom.toAlgebra
      HasTorAmplitudeCanonical (R : Type u)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          ((ModuleCat.restrictScalars (algebraMap (R : Type u) (S : Type u))).obj
            (ModuleCat.of (S : Type u) (S : Type u)))) c d)
    (hM : HasTorAmplitudeCanonical (S : Type u) (DerivedCategory.Q.obj M) a b) :
    HasTorAmplitude (Spec R).toRingedSpace
      ((schemeDerivedPushforward (Spec.map φ)).obj
        (DerivedCategory.Q.obj (((tilde.functor S).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)))
      (a + c) (b + d) := by
  let : Algebra (R : Type u) (S : Type u) := φ.hom.toAlgebra
  refine FlatOpcycles.hasTorAmplitude_of_iso (X := (Spec R).toRingedSpace)
    ((hasTorAmplitude_tilde_iff _ (a + c) (b + d)).2 ?_)
    (affinePushforwardTildeDerivedObjIso' φ M)
  exact hasTorAmplitudeCanonical_restrictScalars_of_hasTorAmplitudeCanonical
    (R : Type u) (S : Type u) M a b c d hφ hM

/-- **Tor amplitude of a sheafified complex, read on the module side.** The converse direction of
[Stacks, Tag 08E9] with the sheafification written degreewise, which is the spelling
`AlgebraicGeometry.affinePushforwardTildeDerivedObjIso` produces. -/
theorem hasTorAmplitudeCanonical_of_hasTorAmplitude_tildeComplex {S : CommRingCat.{u}}
    (M : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    (h : HasTorAmplitude (Spec S).toRingedSpace
      (DerivedCategory.Q.obj (((tilde.functor S).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)) a b) :
    HasTorAmplitudeCanonical (S : Type u) (DerivedCategory.Q.obj M) a b :=
  (hasTorAmplitude_tilde_iff (DerivedCategory.Q.obj M) a b).1
    (FlatOpcycles.hasTorAmplitude_of_iso (X := (Spec S).toRingedSpace) h
      ((tilde.functor S).mapDerivedCategoryFactors.app M))

/-- **The affine base case of the Tor-dimension half of [Stacks, Tag 08EV].** Let `φ : R ⟶ S` be a
map of commutative rings along which `S` has finite Tor dimension, and let `A` be an object of
`D(𝒪_{Spec S})` isomorphic to the sheafification of a complex of `S`-modules. If `A` has finite
Tor dimension on `Spec S` then `R(Spec φ)_*A` has finite Tor dimension on `Spec R`.

The interval for the complex of modules is read back from the sheaf side by [Stacks, Tag 08E9]
rather than computed, so no compatibility between the chosen complex and `RΓ(Spec S, A)` is
needed — the clause of [Stacks, Tag 06Z0] which that statement declines to assert is not used.

`hφ` is the second clause of a perfect ring map, [Stacks, Tag 067H] (2), which is what
`AlgebraicGeometry.Perfect.perfect_appLE` supplies for the chart ring map of a perfect morphism of
schemes. -/
theorem hasFiniteTorDimension_schemeDerivedPushforward_specMap
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : letI : Algebra (R : Type u) (S : Type u) := φ.hom.toAlgebra
      ∃ c d : ℤ, HasTorAmplitudeCanonical (R : Type u)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          ((ModuleCat.restrictScalars (algebraMap (R : Type u) (S : Type u))).obj
            (ModuleCat.of (S : Type u) (S : Type u)))) c d)
    (A : DerivedCategory (Spec S).Modules)
    (hA : ∃ M : CochainComplex (ModuleCat.{u} S) ℤ, Nonempty (A ≅
      DerivedCategory.Q.obj (((tilde.functor S).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)))
    (hTor : HasFiniteTorDimension (Spec S).toRingedSpace A) :
    HasFiniteTorDimension (Spec R).toRingedSpace
      ((schemeDerivedPushforward (Spec.map φ)).obj A) := by
  let : Algebra (R : Type u) (S : Type u) := φ.hom.toAlgebra
  obtain ⟨c, d, hcd⟩ := hφ
  obtain ⟨M, ⟨e⟩⟩ := hA
  obtain ⟨a, b, hab⟩ := hTor
  refine ⟨a + c, b + d, FlatOpcycles.hasTorAmplitude_of_iso (X := (Spec R).toRingedSpace)
    (hasTorAmplitude_schemeDerivedPushforward_tilde φ M a b c d hcd ?_)
    ((schemeDerivedPushforward (Spec.map φ)).mapIso e)⟩
  exact hasTorAmplitudeCanonical_of_hasTorAmplitude_tildeComplex M a b
    (FlatOpcycles.hasTorAmplitude_of_iso (X := (Spec S).toRingedSpace) hab e.symm)

end AlgebraicGeometry

end
