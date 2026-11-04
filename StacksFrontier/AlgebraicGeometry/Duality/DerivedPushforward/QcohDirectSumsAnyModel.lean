module

public import StacksFrontier.AlgebraicGeometry.DerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSums
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedPushforwardSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSumsSupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingExistenceSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSumsLocallySmall

/-!
# `Rf_*` commutes with arbitrary direct sums on `D_QCoh`, away from the standard model

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes. That
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` commutes with direct sums — [Stacks, Tag 08DZ] — is proved in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean` at
`CategoryTheory.HasDerivedCategory.standard`. `HasDerivedCategory` carries the localized category
as *data*, so that statement says nothing about the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model at which
`Stacks.Duality.quasiCoherentDerivedCategory` and the duality statements built on it live. This
file removes the pin.

The pin is needed for exactly one input, part (2) of [Stacks, Tag 08D5] — the uniform bound on the
cohomological dimension of `Rf_*` after pullback to a quasi-compact open of the target — whose
chain of Čech and basis inputs is stated at the standard model throughout. Everything else in the
Tag 08DZ argument already carries the model as a binder, so the whole of it is recovered here from
a single transport, run by the device of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardAnyModel.lean`: the bound
is re-expressed with **no derived category in it at all** — for `I` a K-injective resolution of a
complex `K` with quasi-coherent cohomology in degrees `≤ d`, the degree-`m` cohomology sheaf of
`f_*I` dies on the open for `m > d + N - 1` — and then read back at an arbitrary
`[HasDerivedCategory.{w}]`, where `derivedPushforwardObjIso` below identifies `Rf_*K` with the
object represented by `f_*I`.

## Main definitions

* `Stacks.Duality.DerivedPushforward.AnyModel.derivedPushforwardObjIso` — `Rf_*K` is the
  degreewise direct image of a K-injective resolution of `K`, at an arbitrary chosen model. This
  is the transport device; `homologyDerivedPushforwardQObjIso` beside it is its effect on one
  cohomology sheaf.
* `Stacks.Duality.DerivedPushforward.qcqsQuasiCoherentDerivedPushforwardLocallySmall` — the
  restricted functor `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` at the locally small model, with no
  hypothesis.

## Main results

* `Stacks.Duality.DerivedPushforward.AnyModel.exists_isZero_homology_pushforward_pullback` and
  `isQuasicoherent_homology_pushforward_of_qcqs` — parts (2) and (1) of [Stacks, Tag 08D5] with
  no derived category in the statement.
* `Stacks.Duality.DerivedPushforward.AnyModel.exists_isLE_derivedPushforwardPullback_obj` — part
  (2) of [Stacks, Tag 08D5] at an arbitrary chosen model. **This is the transport the rest of the
  file rests on.**
* `Stacks.Duality.DerivedPushforward.isQuasicoherent_homology_derivedPushforward_locallySmall` —
  part (1) of [Stacks, Tag 08D5] at the locally small model, with no compactness of the target.
* `LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward`, in the
  namespace `Stacks.Duality.DerivedPushforward` — [Stacks, Tag 08DZ] at the locally small model,
  with part (1) of [Stacks, Tag 08D5] as the hypothesis `hpush` that writing the restricted
  functor down requires.
* `preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward_locallySmall`, in the
  same namespace — **[Stacks, Tag 08DZ]**, with `hpush` discharged.

## Implementation notes

**The model, and where it is a binder.** The statements of the `AnyModel` namespace carry
`HasDerivedCategory` as a hypothesis at a free morphism universe. Tag 08DZ itself cannot: its
proof tests invertibility of the direct-sum comparison over the affine opens of the target, so it
needs a model of `D(𝒪_U)` for every affine open `U ⊆ S` at the *same* morphism universe, and the
only uniform choices available are the locally small model and the standard one. The two
statements at the end therefore carry no binder, which puts them at the locally small model — the
one at which `D_QCoh(𝒪_X)` has the `Type u`-indexed direct sums of [Stacks, Tag 08DT], so that
the index types of the conclusion and the morphism universe agree and Brown representability
([Stacks, Tag 0GYH]) applies. At the standard model they do not, which is why the statement there
is of no use to [Stacks, Tag 0A9E].

**`attribute [local instance 10000] HasDerivedCategory.standard`, not a plain `local instance`.**
The import closure contains `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`; at equal
priority instance search picks that one, which would make the statements of `section Standard`
mention a model their inputs are not stated at. The attribute is scoped to that section, so
everything outside it is at a binder or at the locally small model.

**No second copy of a functor that already carries the model as a binder.** Three of the
constructions this file needs — pullback to an open of the target
(`Stacks.Duality.DerivedPushforward.derivedPullbackOpenAtModel`), `Rf_*` followed by it
(`derivedPushforwardPullbackAtModel`) and the comparison `f_* ⟶ Rf_*`
(`AlgebraicGeometry.derivedPushforwardUnitAtModel`) — are model-free constructions that were pinned
where they are declared only because their first consumer happened to want one model. They carry
`[HasDerivedCategory.{w}]` as a binder there instead, and are used here at the binder of this
file; nothing of the kind is restated. What genuinely cannot be reused is a *theorem* pinned by
its proof, which is part (2) of [Stacks, Tag 08D5] alone.

**Two registrations of Tag 08DZ.** The tag is attached here and in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean`; each
states the whole tag, at a different model of the derived categories, and neither subsumes the
other, `HasDerivedCategory` being data.

**Part (1) of [Stacks, Tag 08D5] is transported again, from a different input.**
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` already carries part (1) at
the locally small model, but with `CompactSpace S`, which Tag 08DZ does not have; it transports
`AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward`, where that compactness is
a hypothesis. The version here transports `AlgebraicGeometry.isQuasicoherent_derivedPushforward`,
the declaration that carries the tag, which has no compactness in it.

## References

* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace
open StacksDraft.PseudoCoherence (mapDerivedCategoryCompHomologyFunctorIso)

universe w u

namespace Stacks.Duality.DerivedPushforward.AnyModel

attribute [local instance]
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

attribute [local instance] AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion

/-! ### K-injective resolutions and the derived direct image at an arbitrary model -/

/-- **Every complex of `𝒪_X`-modules admits a quasi-isomorphism into a K-injective complex.** -/
theorem exists_quasiIso_isKInjective_modules (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) :
    ∃ (I : CochainComplex X.Modules ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor X.Modules).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion X.Modules).app K, inferInstance,
    inferInstance⟩

section Device

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- **`Rf_*K` is the degreewise direct image of a K-injective resolution of `K`.** Given a
quasi-isomorphism `s : K ⟶ I` into a K-injective complex, the object `Rf_*K` of the chosen
derived category of the target is the one represented by the complex `f_*I`.

This is the device that moves a statement about the cohomology sheaves of `Rf_*` between models of
the derived categories: the complex `f_*I` mentions no derived category, so a statement about its
cohomology sheaves, proved at `CategoryTheory.HasDerivedCategory.standard`, can be read back
here. -/
def derivedPushforwardObjIso {K I : CochainComplex X.Modules ℤ} (s : K ⟶ I)
    (hI : I.IsKInjective) (hs : QuasiIso s) :
    (Stacks.Duality.derivedPushforward f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((Scheme.Modules.pushforward f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  have := hI
  have := (Stacks.SmallDerivedCategory.isIso_Qh_map_quotient_map_iff s).2 hs
  have := Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective
    (Scheme.Modules.pushforward f) I
  (Stacks.Duality.derivedPushforward f).mapIso
      ((DerivedCategory.quotientCompQhIso X.Modules).app K).symm ≪≫
    (Stacks.Duality.derivedPushforward f).mapIso (asIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) ≪≫
    (asIso ((AlgebraicGeometry.derivedPushforwardUnitAtModel.{w} f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
    (Stacks.SmallDerivedCategory.mapHomotopyCategoryCompQhFactors
      (Scheme.Modules.pushforward f)).app I

/-- The cohomology sheaves of `Rf_*` read off a K-injective resolution: `H^m(Rf_*K)` is the
degree-`m` cohomology sheaf of the complex `f_*I`. -/
def homologyDerivedPushforwardQObjIso {K I : CochainComplex X.Modules ℤ} (s : K ⟶ I)
    (hI : I.IsKInjective) (hs : QuasiIso s) (m : ℤ) :
    (DerivedCategory.homologyFunctor Y.Modules m).obj
        ((Stacks.Duality.derivedPushforward f).obj (DerivedCategory.Q.obj K)) ≅
      (((Scheme.Modules.pushforward f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homology m :=
  (DerivedCategory.homologyFunctor Y.Modules m).mapIso
      (derivedPushforwardObjIso.{w} f s hI hs) ≪≫
    (DerivedCategory.homologyFunctorFactors Y.Modules m).app _

/-- Every object `E` of the derived category is some `K`, with a K-injective resolution `s : K ⟶ I`,
such that `H^i K ≅ H^i E` and `H^m(Rf_*E) ≅ H^m(f_*I)`. -/
private theorem exists_resolution_homology_iso (E : DerivedCategory X.Modules) :
    ∃ (K I : CochainComplex X.Modules ℤ) (s : K ⟶ I) (_ : I.IsKInjective) (_ : QuasiIso s),
      (∀ i : ℤ, Nonempty (K.homology i ≅ (DerivedCategory.homologyFunctor X.Modules i).obj E)) ∧
      ∀ m : ℤ, Nonempty ((DerivedCategory.homologyFunctor Y.Modules m).obj
          ((Stacks.Duality.derivedPushforward f).obj E) ≅
        (((Scheme.Modules.pushforward f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I).homology m) := by
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective_modules X (DerivedCategory.Q.objPreimage E)
  let eQ := DerivedCategory.Q.objObjPreimageIso E
  exact ⟨_, I, s, hI, hs,
    fun i ↦ ⟨((DerivedCategory.homologyFunctorFactors X.Modules i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules i).mapIso eQ⟩,
    fun m ↦ ⟨(DerivedCategory.homologyFunctor Y.Modules m).mapIso
      ((Stacks.Duality.derivedPushforward f).mapIso eQ.symm) ≪≫
        homologyDerivedPushforwardQObjIso.{w} f s hI hs m⟩⟩

end Device

/-- A complex with quasi-coherent cohomology sheaves has quasi-coherent cohomology in the derived
category. -/
private theorem isQuasicoherent_homology_Q_obj {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
    {K : CochainComplex X.Modules ℤ} (hqc : ∀ i : ℤ, (K.homology i).IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj (DerivedCategory.Q.obj K)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors X.Modules i).app K).symm (hqc i)

/-! ### The uniform bound of [Stacks, Tag 08D5] part (2), with no derived category -/

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 08D5] part (2), after pullback to a quasi-compact open of the target, with no
derived category in the statement.** Let `f : X ⟶ S` be quasi-compact and quasi-separated and let
`j : V ⟶ S` be an open immersion with `V` quasi-compact. There is an `N`, depending only on `f`
and `j`, such that for every complex `K` of `𝒪_X`-modules with quasi-coherent cohomology living
in degrees `≤ d` and every quasi-isomorphism `s : K ⟶ I` into a K-injective complex, the
restriction to `V` of the degree-`m` cohomology sheaf of `f_*I` vanishes for `m > d + N - 1`.

The complex `f_*I` computes `Rf_*K`, so this is
`AlgebraicGeometry.isLE_rightDerived_pullback_obj` read at the object represented by `K`;
separating the statement from the derived category is what lets it be used at a model other than
`CategoryTheory.HasDerivedCategory.standard`. -/
theorem exists_isZero_homology_pushforward_pullback {X S V : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    (j : V ⟶ S) [IsOpenImmersion j] [CompactSpace V] :
    ∃ N : ℤ, ∀ (K I : CochainComplex X.Modules ℤ) (s : K ⟶ I), I.IsKInjective → QuasiIso s →
      (∀ i : ℤ, (K.homology i).IsQuasicoherent) →
      ∀ d : ℤ, (∀ i : ℤ, d < i → IsZero (K.homology i)) →
      ∀ m : ℤ, d + N - 1 < m →
        IsZero ((Scheme.Modules.pullback j).obj
          ((((Scheme.Modules.pushforward f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I).homology m)) := by
  obtain ⟨N, hN⟩ := AlgebraicGeometry.isLE_rightDerived_pullback_obj f j
    (Stacks.Duality.derivedPushforward f) (AlgebraicGeometry.derivedPushforwardUnitAtModel f)
  refine ⟨N, fun K I s hI hs hqc d hd m hm ↦ ?_⟩
  have hE : (DerivedCategory.Q.obj K).IsLE d :=
    (DerivedCategory.isLE_iff _ d).2 fun i hi ↦
      (hd i hi).of_iso ((DerivedCategory.homologyFunctorFactors X.Modules i).app K)
  have hz : IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
      (((Scheme.Modules.pullback j).mapDerivedCategory).obj
        ((Stacks.Duality.derivedPushforward f).obj (DerivedCategory.Q.obj K)))) :=
    DerivedCategory.isZero_of_isLE _ (d + N - 1) m hm
      (hX := hN (DerivedCategory.Q.obj K) d (isQuasicoherent_homology_Q_obj hqc) hE)
  exact hz.of_iso
    ((Scheme.Modules.pullback j).mapIso
        (homologyDerivedPushforwardQObjIso f s hI hs m).symm ≪≫
      ((mapDerivedCategoryCompHomologyFunctorIso (Scheme.Modules.pullback j) m).app
        ((Stacks.Duality.derivedPushforward f).obj (DerivedCategory.Q.obj K))).symm)

/-- **Part (1) of [Stacks, Tag 08D5] with no derived category in the statement.** Let
`f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes — no compactness of `S` is
assumed — let `K` be a complex of `𝒪_X`-modules whose cohomology sheaves are quasi-coherent, and
let `s : K ⟶ I` be a quasi-isomorphism into a K-injective complex. Then the cohomology sheaves of
`f_*I`, the complex computing `Rf_*K`, are quasi-coherent.

This is `AlgebraicGeometry.isQuasicoherent_derivedPushforward` read at the object represented by
`K`. That result is stated for `AlgebraicGeometry.RingedSpace.derivedPushforward` of the
underlying morphism of ringed spaces, so the isomorphism identifying `Rf_*K` with the object
represented by `f_*I` is assembled here for *that* functor — from the invertibility of its
comparison map at the K-injective `I`
(`AlgebraicGeometry.RingedSpace.isIso_derivedPushforwardUnit_app_of_isKInjective`) and the
invertibility of `s` in the derived category of the source. Going through
`CategoryTheory.Functor.rightDerivedUnique` instead would mix the two spellings of the module
category inside an instance goal, which instance search does not solve. -/
theorem isQuasicoherent_homology_pushforward_of_qcqs {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
    {K I : CochainComplex X.Modules ℤ} (s : K ⟶ I) (hI : I.IsKInjective) (hs : QuasiIso s)
    (hqc : ∀ i : ℤ, (K.homology i).IsQuasicoherent) (m : ℤ) :
    ((((Scheme.Modules.pushforward f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology m).IsQuasicoherent := by
  have hRS := AlgebraicGeometry.isQuasicoherent_derivedPushforward f
    ⟨DerivedCategory.Q.obj K, isQuasicoherent_homology_Q_obj hqc⟩ m
  have hQs : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map s)) :=
    (Stacks.SmallDerivedCategory.isIso_Qh_map_quotient_map_iff s).2 hs
  have _ := AlgebraicGeometry.RingedSpace.isIso_derivedPushforwardUnit_app_of_isKInjective
    f.toLRSHom.toShHom I hI
  let objIso : (AlgebraicGeometry.RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj
        (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((Scheme.Modules.pushforward f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    (AlgebraicGeometry.RingedSpace.derivedPushforward f.toLRSHom.toShHom).mapIso
        ((DerivedCategory.quotientCompQhIso X.Modules).app K).symm ≪≫
      (AlgebraicGeometry.RingedSpace.derivedPushforward f.toLRSHom.toShHom).mapIso
        (@asIso _ _ _ _ _ hQs) ≪≫
      (asIso ((AlgebraicGeometry.RingedSpace.derivedPushforwardUnit f.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
      (Stacks.SmallDerivedCategory.mapHomotopyCategoryCompQhFactors
        (Scheme.Modules.pushforward f)).app I
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor S.Modules m).mapIso objIso ≪≫
      (DerivedCategory.homologyFunctorFactors S.Modules m).app _) hRS

end Standard

/-! ### Pullback to an open of the target, at an arbitrary model -/

section Pullback

variable {S V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]
  [HasDerivedCategory.{w} S.Modules] [HasDerivedCategory.{w} V.Modules]

/-- `Stacks.Duality.DerivedPushforward.derivedPullbackOpenAtModel` preserves direct sums: pullback
does, being a left adjoint, hence so does its action on cochain complexes, and the localization
functor is essentially surjective and preserves direct sums. -/
theorem preservesColimitsOfShape_discrete_derivedPullbackOpen (α : Type u) :
    PreservesColimitsOfShape (Discrete α) (derivedPullbackOpenAtModel.{w} j) := by
  have h₁ : PreservesColimitsOfShape (Discrete α)
      ((Scheme.Modules.pullback j).mapHomologicalComplex (ComplexShape.up ℤ)) := inferInstance
  have h₂ : PreservesColimitsOfShape (Discrete α) (DerivedCategory.Q (C := V.Modules)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts V.Modules α
  have h₃ : PreservesColimitsOfShape (Discrete α)
      ((Scheme.Modules.pullback j).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) := comp_preservesColimitsOfShape _ _
  have h₄ : PreservesColimitsOfShape (Discrete α)
      (DerivedCategory.Q ⋙ (Scheme.Modules.pullback j).mapDerivedCategory) :=
    (preservesColimitsOfShape_iff_of_natIso
      (Scheme.Modules.pullback j).mapDerivedCategoryFactors).2 h₃
  have h₅ : PreservesColimitsOfShape (Discrete α) (DerivedCategory.Q (C := S.Modules)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts S.Modules α
  exact preservesColimitsOfShape_discrete_of_essSurj_comp
    DerivedCategory.Q (Scheme.Modules.pullback j).mapDerivedCategory α

/-- `Stacks.Duality.DerivedPushforward.derivedPullbackOpenAtModel` preserves lower cohomological
bounds: it is exact, so it commutes with the cohomology functors. -/
theorem isGE_derivedPullbackOpen_obj (E : DerivedCategory S.Modules) (n : ℤ) (hE : E.IsGE n) :
    ((derivedPullbackOpenAtModel.{w} j).obj E).IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact ((Scheme.Modules.pullback j).map_isZero (E.isZero_of_isGE n i hi)).of_iso
    ((mapDerivedCategoryCompHomologyFunctorIso (Scheme.Modules.pullback j) i).app E)

end Pullback

/-! ### The derived direct image followed by pullback to an open of the target -/

section Local

variable {X S : Scheme.{u}} (f : X ⟶ S) {V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} S.Modules]
  [HasDerivedCategory.{w} V.Modules]

/-- **The uniform cohomological bound of [Stacks, Tag 08D5] part (2), after pullback to a
quasi-compact open of the target, at an arbitrary chosen model of the derived categories.**

This is the single input of [Stacks, Tag 08DZ] that
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean` could not
state away from `CategoryTheory.HasDerivedCategory.standard`. The model-free
`Stacks.Duality.DerivedPushforward.AnyModel.exists_isZero_homology_pushforward_pullback` carries
its content, and
`Stacks.Duality.DerivedPushforward.AnyModel.homologyDerivedPushforwardQObjIso` reads that content
back here: the object `E` is represented by a complex `K`, and `Rf_*E` by the degreewise direct
image of a K-injective resolution of `K`. -/
theorem exists_isLE_derivedPushforwardPullback_obj [AlgebraicGeometry.QuasiCompact f]
    [AlgebraicGeometry.QuasiSeparated f] [CompactSpace V] :
    ∃ N : ℤ, ∀ (E : DerivedCategory X.Modules) (d : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
      E.IsLE d → ((derivedPushforwardPullbackAtModel.{w} f j).obj E).IsLE (d + N - 1) := by
  obtain ⟨N, hN⟩ := exists_isZero_homology_pushforward_pullback f j
  refine ⟨N, fun E d hqc hE ↦ (DerivedCategory.isLE_iff _ (d + N - 1)).2 fun m hm ↦ ?_⟩
  obtain ⟨K, I, s, hI, hs, hK, hiso⟩ := exists_resolution_homology_iso.{w} f E
  exact (hN K I s hI hs
    (fun i ↦ (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (hK i).some.symm (hqc i)) d
    (fun i hi ↦ (DerivedCategory.isZero_of_isLE E d i hi).of_iso (hK i).some) m hm).of_iso
    ((mapDerivedCategoryCompHomologyFunctorIso (Scheme.Modules.pullback j) m).app
        ((Stacks.Duality.derivedPushforward f).obj E) ≪≫
      (Scheme.Modules.pullback j).mapIso (hiso m).some)

/-- `Rf_*` followed by pullback to an open of the target preserves lower cohomological bounds:
`Rf_*` moves cohomology to the right and pullback along an open immersion is exact. -/
theorem isGE_derivedPushforwardPullback_obj (E : DerivedCategory X.Modules) (n : ℤ)
    (hE : E.IsGE n) : ((derivedPushforwardPullbackAtModel.{w} f j).obj E).IsGE n :=
  isGE_derivedPullbackOpen_obj.{w} j _ n
    (Stacks.DerivedFunctor.isGE_totalRightDerived_obj (Scheme.Modules.pushforward f) E n)

end Local

/-! ### Quasi-coherence of a direct sum -/

/-- The cohomology sheaves of a direct sum of objects with quasi-coherent cohomology are
quasi-coherent: cohomology commutes with direct sums, and quasi-coherent modules are closed
under them. -/
theorem isQuasicoherent_homology_sigmaObj {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
    {α : Type u} (E : α → DerivedCategory X.Modules)
    (hqc : ∀ k (i : ℤ), ((DerivedCategory.homologyFunctor X.Modules i).obj (E k)).IsQuasicoherent)
    (i : ℤ) : ((DerivedCategory.homologyFunctor X.Modules i).obj (∐ E)).IsQuasicoherent := by
  have hpres : PreservesColimit (Discrete.functor E)
      (DerivedCategory.homologyFunctor X.Modules i) :=
    (Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor X.Modules i).preservesColimit
  refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (PreservesCoproduct.iso (DerivedCategory.homologyFunctor X.Modules i) E).symm ?_
  exact isQuasicoherent_sigmaObj X _ fun k ↦ hqc k i

/-! ### The two cuts, and the statement over an affine open of the target -/

section Cuts

variable {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} S.Modules]

section Open
variable {V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j] [HasDerivedCategory.{w} V.Modules]

/-- **The upper cut.** For a family lying in degrees `≥ a`, the direct-sum comparison morphism
of `Rf_*` followed by pullback to a quasi-compact open of the target is invertible in every
degree `q`: the triangle `τ_{≤ q}E ⟶ E ⟶ τ_{> q}E` has its third vertex carried into degrees
`≥ q + 1`, which `H^q` and `H^{q-1}` do not see, and its first vertex lies in the window
`[a, q]`, where the dévissage of
`Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isGE_isLE` applies. -/
theorem isIso_homologyMap_sigmaComparison_of_isGE {α : Type u}
    (Z : α → DerivedCategory X.Modules) (a : ℤ)
    (hge : ∀ k, (Z k).IsGE a) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor V.Modules q).map
      (sigmaComparison (derivedPushforwardPullbackAtModel.{w} f j) Z)) := by
  have hvan : ∀ (k : α) (m : ℤ), m < q + 1 →
      IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
        ((derivedPushforwardPullbackAtModel.{w} f j).obj
          ((DerivedCategory.TStructure.t.truncGT q).obj (Z k)))) := fun k m hm ↦
    DerivedCategory.isZero_of_isGE _ (q + 1) m hm
      (hX := isGE_derivedPushforwardPullback_obj.{w} f j _ (q + 1) inferInstance)
  have hsum : ∀ m : ℤ, m < q + 1 → IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
      ((derivedPushforwardPullbackAtModel.{w} f j).obj
        (∐ fun k ↦ (DerivedCategory.TStructure.t.truncGT q).obj (Z k)))) := fun m hm ↦
    DerivedCategory.isZero_of_isGE _ (q + 1) m hm
      (hX := isGE_derivedPushforwardPullback_obj.{w} f j _ (q + 1)
        (Stacks.Duality.isGE_sigmaObj X.Modules _ (q + 1) fun _ ↦ inferInstance))
  have hbase : IsIso ((DerivedCategory.homologyFunctor V.Modules q).map
      (sigmaComparison (derivedPushforwardPullbackAtModel.{w} f j)
        fun k ↦ (DerivedCategory.TStructure.t.truncLE q).obj (Z k))) := by
    have hb : IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f)
        (fun k ↦ (DerivedCategory.TStructure.t.truncLE q).obj (Z k))) := by
      refine isIso_sigmaComparison_of_isGE_isLE f a q _ (fun k ↦ ?_) (fun _ ↦ ?_)
      · have := hge k
        infer_instance
      · infer_instance
    have hRj : IsIso (sigmaComparison (derivedPullbackOpenAtModel.{w} j)
        (fun k ↦ (Stacks.Duality.derivedPushforward f).obj
          ((DerivedCategory.TStructure.t.truncLE q).obj (Z k)))) :=
      isIso_sigmaComparison_of_preservesColimit _ _
        (preservesColimitsOfShape_discrete_derivedPullbackOpen.{w} j α).preservesColimit
    have hPsi : IsIso (sigmaComparison (derivedPushforwardPullbackAtModel.{w} f j)
        (fun k ↦ (DerivedCategory.TStructure.t.truncLE q).obj (Z k))) := by
      rw [sigmaComparison_comp]
      infer_instance
    infer_instance
  exact isIso_homologyMap_sigmaComparison_of_isIso_obj₁ (derivedPushforwardPullbackAtModel.{w} f j)
    (fun k ↦ Triangle.mk
      ((DerivedCategory.TStructure.t.truncLEι q).app (Z k))
      ((DerivedCategory.TStructure.t.truncGTπ q).app (Z k))
      ((DerivedCategory.TStructure.t.truncGTδLE q).app (Z k)))
    (fun k ↦ DerivedCategory.TStructure.t.triangleLEGT_distinguished q (Z k)) q
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ q fun k ↦ hvan k q (by omega))
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ (q - 1)
      fun k ↦ hvan k (q - 1) (by omega))
    (hsum q (by omega)) (hsum (q - 1) (by omega)) hbase

variable [CompactSpace V]

/-- **The two cuts together.** For a family of objects of `D(𝒪_X)` with quasi-coherent
cohomology, the direct-sum comparison morphism of `Rf_*` followed by pullback to a quasi-compact
open of the target is invertible in every degree `q`. The triangle
`τ_{≤ q - N}E ⟶ E ⟶ τ_{> q - N}E`, with `N` the bound of [Stacks, Tag 08D5] part (2), has its
first vertex carried into degrees `≤ q - 1`, which `H^q` and `H^{q+1}` do not see, and its third
vertex lies in degrees `≥ q - N + 1`, where
`Stacks.Duality.DerivedPushforward.AnyModel.isIso_homologyMap_sigmaComparison_of_isGE`
applies. -/
theorem isIso_homologyMap_sigmaComparison_pullback {α : Type u}
    (E : α → DerivedCategory X.Modules)
    (hqc : ∀ (k : α) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj (E k)).IsQuasicoherent) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor V.Modules q).map
      (sigmaComparison (derivedPushforwardPullbackAtModel.{w} f j) E)) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforwardPullback_obj.{w} f j
  have hqcW : ∀ (k : α) (i : ℤ), ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.TStructure.t.truncLE (q - N)).obj (E k))).IsQuasicoherent := fun k i ↦
    Stacks.Duality.isQuasicoherent_homology_truncLE (E k) (hqc k) (q - N) i
  have hvan : ∀ (k : α) (m : ℤ), q - 1 < m →
      IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
        ((derivedPushforwardPullbackAtModel.{w} f j).obj
          ((DerivedCategory.TStructure.t.truncLE (q - N)).obj (E k)))) := fun k m hm ↦
    DerivedCategory.isZero_of_isLE _ (q - N + N - 1) m (by omega)
      (hX := hN _ (q - N) (hqcW k) inferInstance)
  have hsum : ∀ m : ℤ, q - 1 < m → IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
      ((derivedPushforwardPullbackAtModel.{w} f j).obj
        (∐ fun k ↦ (DerivedCategory.TStructure.t.truncLE (q - N)).obj (E k)))) := fun m hm ↦
    DerivedCategory.isZero_of_isLE _ (q - N + N - 1) m (by omega)
      (hX := hN _ (q - N) (fun i ↦ isQuasicoherent_homology_sigmaObj.{w} _ hqcW i)
        (Stacks.Duality.isLE_sigmaObj X.Modules _ (q - N) fun _ ↦ inferInstance))
  exact isIso_homologyMap_sigmaComparison_of_isIso_obj₃ (derivedPushforwardPullbackAtModel.{w} f j)
    (fun k ↦ Triangle.mk
      ((DerivedCategory.TStructure.t.truncLEι (q - N)).app (E k))
      ((DerivedCategory.TStructure.t.truncGTπ (q - N)).app (E k))
      ((DerivedCategory.TStructure.t.truncGTδLE (q - N)).app (E k)))
    (fun k ↦ DerivedCategory.TStructure.t.triangleLEGT_distinguished (q - N) (E k)) q
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ q fun k ↦ hvan k q (by omega))
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ (q + 1)
      fun k ↦ hvan k (q + 1) (by omega))
    (hsum q (by omega)) (hsum (q + 1) (by omega))
    (isIso_homologyMap_sigmaComparison_of_isGE.{w} f j
      (fun k ↦ (DerivedCategory.TStructure.t.truncGT (q - N)).obj (E k)) (q - N + 1)
      (fun _ ↦ inferInstance) q)

end Open

end Cuts

/-- **`D_QCoh(𝒪_Z)` is closed under direct sums** indexed by a type of the scheme universe, at an
arbitrary chosen model of the derived category. This is [Stacks, Tag 08DT]. -/
theorem isClosedUnderCoproducts_derivedQuasicoherent (Z : Scheme.{u})
    [HasDerivedCategory.{w} Z.Modules] (α : Type u) :
    (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).IsClosedUnderColimitsOfShape
      (Discrete α) :=
  Stacks.Duality.derivedCategoryB_isClosedUnderCoproducts _ _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre Z)
    (isQuasicoherent_sigmaObj Z)

end Stacks.Duality.DerivedPushforward.AnyModel

/-! ### [Stacks, Tag 08DZ] at the locally small model

The statements of this section carry no `HasDerivedCategory` binder, so the model of every derived
category in them is the locally small one, `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.
A binder is not an option here: invertibility of the direct-sum comparison is checked over the
affine opens of the target, so the argument needs a model of `D(𝒪_U)` for every affine open
`U ⊆ S` at the *same* morphism universe, and the only such uniform choices are the locally small
one and `CategoryTheory.HasDerivedCategory.standard`. The locally small one is the model at which
`D_QCoh(𝒪_X)` has the `Type u`-indexed direct sums of [Stacks, Tag 08DT] and at which the duality
statements built on `Stacks.Duality.quasiCoherentDerivedCategory` live; the standard model is the
one `StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean`
treats.
-/

namespace Stacks.Duality.DerivedPushforward

attribute [local instance]
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

attribute [local instance] AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion

variable {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f]

/-! ### The tag, with part (1) of [Stacks, Tag 08D5] discharged -/

/-- **Part (1) of [Stacks, Tag 08D5] at the locally small model.** For a quasi-compact and
quasi-separated morphism of schemes — with no compactness of the target — derived direct image
carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_S)`.

This is `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs` without the
hypothesis `CompactSpace S`, and it is obtained from a different standard-model input: that
statement transports `AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward`, which
carries the compactness, whereas the model-free
`Stacks.Duality.DerivedPushforward.AnyModel.isQuasicoherent_homology_pushforward_of_qcqs`
transports `AlgebraicGeometry.isQuasicoherent_derivedPushforward`, which does not. -/
@[ega "III 6.2.3" "more general", sga "3 I 6.6" "more general"]
theorem isQuasicoherent_homology_derivedPushforward_locallySmall
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ) :
    ((DerivedCategory.homologyFunctor S.Modules i).obj
      ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent := by
  obtain ⟨L, I, s, hI, hs, hL, hiso⟩ := AnyModel.exists_resolution_homology_iso f K.obj
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso (hiso i).some.symm
    (AnyModel.isQuasicoherent_homology_pushforward_of_qcqs f s hI hs
      (fun n ↦ (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (hL n).some.symm
        (K.2 n)) i)

/-- **`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)`** for a quasi-compact and quasi-separated morphism of
schemes, at the locally small model. That `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_S)` is
part (1) of [Stacks, Tag 08D5], `isQuasicoherent_homology_derivedPushforward_locallySmall`, so no
hypothesis is left. -/
abbrev qcqsQuasiCoherentDerivedPushforwardLocallySmall :
    Stacks.Duality.quasiCoherentDerivedCategory X ⥤
      Stacks.Duality.quasiCoherentDerivedCategory S :=
  Stacks.Duality.quasiCoherentDerivedPushforward f
    (isQuasicoherent_homology_derivedPushforward_locallySmall f)

/-- **[Stacks, Tag 08DZ].** Let `f : X ⟶ S` be a quasi-separated and quasi-compact morphism of
schemes. Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` commutes with direct sums: for every index type
`α` of the scheme universe it preserves `α`-indexed direct sums.

The index types are those of the scheme universe because those are the ones for which
`D_QCoh(𝒪_X)` has direct sums at all ([Stacks, Tag 08DT],
`Stacks.Duality.DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory`).

This is the tag at the locally small model of the derived categories, where that universe of index
types is also the morphism universe; the companion registration
`preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward`
is the tag at `CategoryTheory.HasDerivedCategory.standard`, where the two universes differ. -/
@[stacks 08DZ "locally_small_model"]
theorem preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward_locallySmall
    (α : Type u) :
    PreservesColimitsOfShape (Discrete α)
      (qcqsQuasiCoherentDerivedPushforwardLocallySmall f) :=
  LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward f _ α

end Stacks.Duality.DerivedPushforward

end
