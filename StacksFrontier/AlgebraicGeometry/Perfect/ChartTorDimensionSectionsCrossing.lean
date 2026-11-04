module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectSectionsChart
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTorDimensionLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictFunctorAlongIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso

/-!
# The Tor-dimension clause of Stacks 0DI2 on a chart, between its two sides

Clauses (2) and (3) of Stacks 0DI2 are conditions on the complex of sections `RΓ(U, E)` over an
affine open `U ⊆ f⁻¹(V)`, read over `Γ(S, V)`; clause (1) is a condition on the sheaf side, on
the inverse-image ringed space `(X, f⁻¹𝒪_S)`. This file is the crossing between the two sides on
one chart.

The module side is crossed to the *stalkwise* sheaf-side condition
`AlgebraicGeometry.HasTorAmplitudeOver` of the restricted morphism `f.resLE V U e : U ⟶ V`:
finite Tor dimension of `RΓ(U, E)` over `Γ(S, V)` is finite Tor dimension of `E|_U` over that
morphism. This is Stacks 0DHY at an affine open of a *general* morphism of schemes.

The stalkwise condition is identified with
`AlgebraicGeometry.Scheme.Hom.ChartHasFiniteTorDimension`, which reads finite Tor dimension on the
ringed space `(X, f⁻¹𝒪_S)|_U`, by the statement
`AlgebraicGeometry.Scheme.Hom.ChartTorSpellingsAgree` named here and proved as
`AlgebraicGeometry.Scheme.Hom.chartTorSpellingsAgree` in
`StacksFrontier/AlgebraicGeometry/Perfect/InverseImageTorAmplitudeStalk.lean`; the two crossings
below take it as an argument so that this file stays below that one.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.ChartTorSpellingsAgree`: on one chart, the two sheaf-side
  readings of "`E` has finite Tor dimension over `f⁻¹𝒪_S` there" agree — the ringed-space one of
  Stacks 08CG on `(X, f⁻¹𝒪_S)|_U`, and the stalkwise one of Stacks 0DJF over `f.resLE V U e`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_hasTorAmplitudeOver_resLE_iff_hasFiniteTorDimension`:
  **Stacks 0DHY on an affine open of a general morphism**, between the module side and the
  stalkwise sheaf side, given an affine presentation of `E|_U`.
* `AlgebraicGeometry.Scheme.Hom.chartHasFiniteTorDimension_iff_hasFiniteTorDimension_sections`:
  the Tor-dimension crossing of clauses (2) and (3) of Stacks 0DI2.
* `AlgebraicGeometry.Scheme.Hom.sectionsRelativelyPerfect_iff`: the whole module-side chart
  condition — both conjuncts — against the two sheaf-side ones.

## Implementation notes

**The two transports.** The module side and the stalkwise sheaf side are joined by transport
along `AlgebraicGeometry.IsAffineOpen.isoSpec`, which
`AlgebraicGeometry.exists_hasTorAmplitudeOver_resLE_iff` performs: the predicate is stalkwise, so
an isomorphism of schemes moves it with no comparison of ringed spaces at all. The ringed-space
reading is reached from the stalkwise one at the points of `U`, by Stacks 09U9 on the open
subspace `(X, f⁻¹𝒪_S)|_U`.

**The flatness and finite presentation of `f`** are absent from the first two crossings and
present in the last. The Tor-dimension conjunct of the module-side condition is
`StacksDraft.TorAmplitude.HasFiniteTorDimension`, which takes no algebra hypotheses; only
`AlgebraicGeometry.Scheme.Hom.SectionsRelativelyPerfect`, which is
`StacksDraft.PseudoCoherence.IsRelativelyPerfect` and takes `Module.Flat` and
`Algebra.FinitePresentation` as instance arguments, needs them.

## References

* [The Stacks Project, Lemma 36.35.3 (0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [The Stacks Project, Lemma 36.21.3 (0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
* [The Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [The Stacks Project, Definition 20.48.1 (08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks 0DHY on an affine open of a general morphism of schemes.** Let `V ⊆ S` and
`U ⊆ f⁻¹(V)` be affine opens, let `EU` be an object of `D(𝒪_U)` and let `𝕃` be an object of
`D(Γ(X, U))` whose derived sheafification is the transport of `EU` to `Spec Γ(X, U)`. Then `EU`
has finite Tor dimension over `f.resLE V U e` exactly when `𝕃`, read over `Γ(S, V)` along the
chart ring map `f.appLE V U e`, has finite Tor dimension.

Both sides move along `AlgebraicGeometry.IsAffineOpen.isoSpec`: the left-hand side because
`AlgebraicGeometry.HasTorAmplitudeOver` is stalkwise
(`AlgebraicGeometry.exists_hasTorAmplitudeOver_resLE_iff`), the right-hand side because it does
not refer to the geometry at all. On the spectra the two are identified by Stacks 0DHY,
`AlgebraicGeometry.AffineRelativeTorAmplitude.exists_hasTorAmplitudeOver_tildeComplex_iff`.

This is the biconditional of which
`AlgebraicGeometry.hasFiniteTorDimensionCanonical_of_hasTorAmplitudeOver_resLE` is the forward
implication; neither flatness nor local finite presentation of `f` is used. -/
public theorem exists_hasTorAmplitudeOver_resLE_iff_hasFiniteTorDimension
    {V : S.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (EU : DerivedCategory U.toScheme.Modules) (𝕃 : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (eL : (derivedPullback hU.isoSpec.inv.toLRSHom.toShHom).obj EU ≅
      (tilde.functor Γ(X, U)).mapDerivedCategory.obj 𝕃) :
    (∃ a b : ℤ, HasTorAmplitudeOver (f.resLE V U e) EU a b) ↔
      (letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
       HasFiniteTorDimension (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).tensor
         (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).comparison
         (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).isLeftDerived
         ((ModuleCat.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).mapDerivedCategory.obj 𝕃)) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  obtain ⟨M, eQ⟩ : Σ' M : CochainComplex (ModuleCat.{u} Γ(X, U)) ℤ,
      DerivedCategory.Q.obj M ≅ 𝕃 :=
    ⟨DerivedCategory.Q.objPreimage 𝕃, DerivedCategory.Q.objObjPreimageIso 𝕃⟩
  have eT : (derivedPullback hU.isoSpec.inv.toLRSHom.toShHom).obj EU ≅
      DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M) :=
    eL ≪≫ (tilde.functor Γ(X, U)).mapDerivedCategory.mapIso eQ.symm ≪≫
      (tilde.functor Γ(X, U)).mapDerivedCategoryFactors.app M
  have eR : ((ModuleCat.restrictScalars
        (algebraMap Γ(S, V) Γ(X, U))).mapDerivedCategory.obj 𝕃) ≅
      DerivedCategory.Q.obj (((ModuleCat.restrictScalars
        (algebraMap Γ(S, V) Γ(X, U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
    (ModuleCat.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).mapDerivedCategory.mapIso eQ.symm ≪≫
      (ModuleCat.restrictScalars
        (algebraMap Γ(S, V) Γ(X, U))).mapDerivedCategoryFactors.app M
  refine Iff.trans (exists_hasTorAmplitudeOver_resLE_iff f hV hU e EU).symm ?_
  refine Iff.trans (exists_congr fun a => exists_congr fun b =>
    ⟨fun h => hasTorAmplitudeOver_of_iso eT a b h,
      fun h => hasTorAmplitudeOver_of_iso eT.symm a b h⟩) ?_
  refine Iff.trans (AffineRelativeTorAmplitude.exists_hasTorAmplitudeOver_tildeComplex_iff
    Γ(S, V) Γ(X, U) M) ?_
  refine Iff.trans ?_ (PseudoCoherence.hasFiniteTorDimension_canonicalDerivedTensoringDatum_iff
    Γ(S, V) _).symm
  refine Iff.trans (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _) ?_
  refine Iff.trans ?_ (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).symm
  exact exists_congr fun a => exists_congr fun b =>
    ⟨fun h => hasTorAmplitudeCanonical_of_iso eR.symm a b h,
      fun h => hasTorAmplitudeCanonical_of_iso eR a b h⟩

/-- **The affine presentation of `E|_U` in derived-pullback form.** On an affine open `U` of `X`,
the transport of `E|_U` to `Spec Γ(X, U)` along `AlgebraicGeometry.IsAffineOpen.isoSpec` is the
derived sheafification of `RΓ(U, E)`.

`AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedTilde_derivedSectionsSpec` is this with the
transport written as a pushforward along `hU.isoSpec.inv`; the derived pullback along that
isomorphism is restriction along it by
`AlgebraicGeometry.Scheme.Modules.derivedPullbackObjIsoRestrictFunctor`, and restriction cancels
the pushforward by Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`. The
presenting object is `AlgebraicGeometry.derivedSectionsUnbounded` over `U` rather than derived
global sections on the spectrum, by
`AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedSectionsSpec`. -/
public theorem nonempty_derivedPullback_isoSpec_iso_tilde_derivedSections
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Nonempty ((derivedPullback hU.isoSpec.inv.toLRSHom.toShHom).obj
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) ≅
      (tilde.functor Γ(X, U)).mapDerivedCategory.obj ((derivedSectionsUnbounded X U).obj E)) := by
  obtain ⟨e₁⟩ := hU.nonempty_iso_derivedTilde_derivedSectionsSpec E hE
  obtain ⟨eΓ⟩ := hU.nonempty_iso_derivedSectionsSpec E
  refine ⟨Scheme.Modules.derivedPullbackObjIsoRestrictFunctor hU.isoSpec.inv _ ≪≫
    (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory.mapIso e₁ ≪≫ ?_⟩
  refine ?_ ≪≫ (tilde.functor Γ(X, U)).mapDerivedCategory.mapIso eΓ
  exact (Functor.mapDerivedCategoryCompIso
      (Scheme.Modules.restrictFunctorAdjCounitIso hU.isoSpec.inv)).app _ ≪≫
    (Functor.mapDerivedCategoryId (Spec Γ(X, U)).Modules).app _

/-- **Stacks 0DHY on an affine open of a general morphism of schemes, at the derived sections.**
Let `f : X ⟶ S` be a morphism of schemes, let `E` be an object of `D(𝒪_X)` with quasi-coherent
cohomology sheaves, and let `V ⊆ S` and `U ⊆ f⁻¹(V)` be affine opens. Then `E|_U` has finite Tor
dimension over `f.resLE V U e` exactly when the complex of `Γ(X, U)`-modules `RΓ(U, E)`, read
over `Γ(S, V)` along the chart ring map `f.appLE V U e`, has finite Tor dimension.

This is
`AlgebraicGeometry.Scheme.Hom.exists_hasTorAmplitudeOver_resLE_iff_hasFiniteTorDimension` with
the affine presentation discharged by
`AlgebraicGeometry.Scheme.Hom.nonempty_derivedPullback_isoSpec_iso_tilde_derivedSections`. The
right-hand side is the Tor-dimension conjunct of
`AlgebraicGeometry.Scheme.Hom.SectionsRelativelyPerfect`, which is the module-side condition of
clauses (2) and (3) of Stacks 0DI2; the left-hand side is the *stalkwise* sheaf-side condition,
not the ringed-space one of clause (1). -/
public theorem exists_hasTorAmplitudeOver_resLE_iff_hasFiniteTorDimension_derivedSections
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    {V : S.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V) :
    (∃ a b : ℤ, HasTorAmplitudeOver (f.resLE V U e)
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) a b) ↔
      (letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
       HasFiniteTorDimension (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).tensor
         (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).comparison
         (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).isLeftDerived
         ((ModuleCat.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).mapDerivedCategory.obj
           ((derivedSectionsUnbounded X U).obj E))) := by
  obtain ⟨eL⟩ := nonempty_derivedPullback_isoSpec_iso_tilde_derivedSections E hE hU
  exact exists_hasTorAmplitudeOver_resLE_iff_hasFiniteTorDimension f hV hU e _ _ eL

/-! ### The two sheaf-side readings, and the crossings they give -/

/-- **The two sheaf-side readings of finite Tor dimension over `f⁻¹𝒪_S` on one chart.** The
ringed-space one of part (2) of Stacks 08CG, read on `(X, f⁻¹𝒪_S)|_U` at the canonical
certificate family, and the stalkwise one of Stacks 0DJF, read over the restricted morphism
`f.resLE V U e : U ⟶ V`, are equivalent. This holds for every pair of opens; it is
`AlgebraicGeometry.Scheme.Hom.chartTorSpellingsAgree`. -/
public def ChartTorSpellingsAgree (E : DerivedCategory X.Modules) (V : S.Opens) (U : X.Opens)
    (e : U ≤ f ⁻¹ᵁ V) : Prop :=
  ChartHasFiniteTorDimension f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) E U ↔
    ∃ a b : ℤ, HasTorAmplitudeOver (f.resLE V U e)
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) a b

/-- **The Tor-dimension crossing of clauses (2) and (3) of Stacks 0DI2.** On an
affine open `U ⊆ f⁻¹(V)` with `V ⊆ S` affine, the sheaf-side Tor-dimension condition of
clause (1) on that chart holds exactly when the complex of `Γ(X, U)`-modules `RΓ(U, E)`, read
over `Γ(S, V)`, has finite Tor dimension — which is the Tor-dimension conjunct of the
module-side condition of clauses (2) and (3).

It is `AlgebraicGeometry.Scheme.Hom.ChartTorSpellingsAgree` followed by
`exists_hasTorAmplitudeOver_resLE_iff_hasFiniteTorDimension_derivedSections`; `hagree` is
supplied by `AlgebraicGeometry.Scheme.Hom.chartTorSpellingsAgree`. -/
public theorem chartHasFiniteTorDimension_iff_hasFiniteTorDimension_sections
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    {V : S.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (hagree : ChartTorSpellingsAgree f E V U e) :
    ChartHasFiniteTorDimension f
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base)) E U ↔
      (letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
       HasFiniteTorDimension (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).tensor
         (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).comparison
         (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).isLeftDerived
         ((ModuleCat.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).mapDerivedCategory.obj
           ((derivedSectionsUnbounded X U).obj E))) :=
  hagree.trans
    (exists_hasTorAmplitudeOver_resLE_iff_hasFiniteTorDimension_derivedSections f E hE hV hU e)

/-- **The whole module-side chart condition of Stacks 0DI2, against the sheaf side.** For
`f : X ⟶ S` flat and locally of finite presentation and `E` with quasi-coherent cohomology
sheaves, the complex `RΓ(U, E)` is `Γ(S, V)`-perfect exactly when `E|_U` is pseudo-coherent and
has finite Tor dimension over `f⁻¹𝒪_S` on `U`.

The pseudo-coherence conjunct is
`AlgebraicGeometry.isPseudoCoherent_derivedRestrictModules_iff_derivedSections` and is
unconditional; the Tor-dimension conjunct is
`AlgebraicGeometry.Scheme.Hom.chartHasFiniteTorDimension_iff_hasFiniteTorDimension_sections`.
With `hagree` supplied by `AlgebraicGeometry.Scheme.Hom.chartTorSpellingsAgree`, this turns the
sheaf-side implications into the three-way equivalence
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_tfae`. -/
public theorem sectionsRelativelyPerfect_iff [Flat f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    {V : S.Opens} {U : X.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (hagree : ChartTorSpellingsAgree f E V U e) :
    SectionsRelativelyPerfect f E hV hU e ↔
      (RingedSpace.IsPseudoCoherent
          ((RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E) ∧
        ChartHasFiniteTorDimension f
          (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
            (RingedSpace.inverseImage S.toRingedSpace f.base)) E U) :=
  and_congr (isPseudoCoherent_derivedRestrictModules_iff_derivedSections E hE hU).symm
    (chartHasFiniteTorDimension_iff_hasFiniteTorDimension_sections f E hE hV hU e hagree).symm

end AlgebraicGeometry.Scheme.Hom

end
