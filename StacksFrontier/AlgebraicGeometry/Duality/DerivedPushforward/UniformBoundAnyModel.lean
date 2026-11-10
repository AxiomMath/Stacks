module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBound
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel
import StacksCore.Tactic.StacksAttribute

/-!
# The uniform cohomological bound for `Rf_*`, at an arbitrary derived category

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `Y` quasi-compact.
[Stacks, Tag 08D5] part (2) — that `Rf_*` raises the upper cohomological bound of an object with
quasi-coherent cohomology by an amount depending on `f` alone — is proved in
`StacksFrontier/AlgebraicGeometry/UnboundedDerivedDirectImage/UniformBound.lean` and restated in the
duality spelling in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/UniformBound.lean`, both at
`CategoryTheory.HasDerivedCategory.standard`. `HasDerivedCategory` carries the localized category
as *data*, so neither statement says anything about the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the model at which
`Stacks.Duality.quasiCoherentDerivedCategory` has the direct sums Brown representability asks for.
This file removes the pin.

The route is the one
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/QcqsPushforwardAnyModel.lean` takes for
part (1) of the same tag: the statement is first re-expressed with **no derived category in it at
all** — for `s : K ⟶ I` a K-injective resolution of a complex with quasi-coherent cohomology
living in degrees `≤ b`, the complex `f_*I`, which computes `Rf_*K`, has vanishing cohomology
sheaves in degrees `≥ b + N` — and then read back at an arbitrary `[HasDerivedCategory.{w}]`,
where `Stacks.Duality.derivedPushforwardObjIso` identifies `Rf_*E` with the object represented by
`f_*I`.

## Main definitions

* `Stacks.Duality.derivedPushforwardUnit` — the canonical comparison `f_* ⟶ Rf_*` for
  `Stacks.Duality.derivedPushforward`, at an arbitrary chosen model.
* `Stacks.Duality.derivedPushforwardObjIso` — `Rf_*K` is the termwise direct image of a
  K-injective resolution of `K`, at an arbitrary chosen model.

## Main results

* `Stacks.Duality.exists_isZero_homology_modulePushforward_of_qcqs` — **[Stacks, Tag 08D5]
  part (2) with no derived category in the statement.**
* `Stacks.Duality.exists_isZero_homology_derivedPushforward_anyModel` — the same at an arbitrary
  chosen model of the two derived categories.
* `Stacks.Duality.exists_isLE_derivedPushforward_obj_anyModel` — that result in the `IsLE` form
  its consumers want, at an arbitrary chosen model. This is the transport of
  `Stacks.Duality.exists_isLE_derivedPushforward_obj` off `HasDerivedCategory.standard`.

## Implementation notes

**Everything is in the `AlgebraicGeometry.Scheme.Modules` spelling of the category of
`𝒪_X`-modules**, with `Rf_*` spelled `Stacks.Duality.derivedPushforward`, which already takes the
choice of derived category as a binder rather than resolving it at definition time. That is what
makes the standard-model input `Stacks.Duality.exists_isLE_derivedPushforward_obj` usable with no
crossing between the two interchangeable spellings `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules (structureSheafRing X.toRingedSpace)`: those are definitionally
equal but carry separately declared instances, and instance search does not cross them.

**`attribute [local instance 10000] HasDerivedCategory.standard`, not a plain `local instance`.**
The import closure carries the locally small `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`
as a global instance; at equal priority instance search picks that one, which would make the
statement of the standard-model section mention a model its input is not stated at. The attribute
is scoped to `section Standard`, so the arbitrary-model statements after it are unaffected.

**The comparison `f_* ⟶ Rf_*` is rebuilt here rather than imported.**
`Stacks.Duality.DerivedPushforward.derivedPushforwardUnit` of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean` is the
same
total right derived unit, but that file installs `HasDerivedCategory.standard` at raised priority
for the whole of it, so its statement is pinned. The definition below is the same term with the
model left as a binder, and the K-injective criterion of [Stacks, Tag 070K] applies to it because
`AlgebraicGeometry.Scheme.Modules` is a Grothendieck abelian category and therefore admits
functorial K-injective resolutions ([Stacks, Tag 079P]).

**No part (3).** [Stacks, Tag 08D5] is a lemma in three parts and its covering set is the three
of them; part (3), that the integer `N` survives an arbitrary base change, is not available at any
model. The attribute below therefore names the part it carries, exactly as the two statements it
transports do.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.Duality

/-! ### K-injective resolutions of complexes of `𝒪_X`-modules -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The comparison `f_* ⟶ Rf_*` at an arbitrary model -/

section AnyModel

variable [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- The canonical comparison `f_* ⟶ Rf_*` of `Stacks.Duality.derivedPushforward`, at an arbitrary
chosen model of the two derived categories. -/
abbrev derivedPushforwardUnit :
    (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedPushforward f :=
  (homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- A K-injective complex computes the derived direct image at any chosen model: on it the
canonical comparison `f_*I ⟶ Rf_*I` is invertible. This is the second half of the K-injective
criterion of [Stacks, Tag 070K], whose hypothesis — the existence of K-injective resolutions in
the source — is model-free. -/
theorem isIso_derivedPushforwardUnit_app_of_isKInjective
    (I : CochainComplex X.Modules ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedPushforwardUnit.{w} f).app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, w, w, u + 1, u + 1, u + 1}
      (homotopyPushforward.{w} f)
      (AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X)).2
    DerivedCategory.Qh (derivedPushforward.{w} f) (derivedPushforwardUnit.{w} f) I hI

/-- **`Rf_*K` is the termwise direct image of a K-injective resolution of `K`.** Given a
quasi-isomorphism `s : K ⟶ I` into a K-injective complex, the object `Rf_*K` of the chosen derived
category of the target is the one represented by the complex `f_*I`: the comparison map is
invertible at `I`, and `s` becomes invertible in the derived category of the source. -/
def derivedPushforwardObjIso {K I : CochainComplex X.Modules ℤ} (s : K ⟶ I)
    (hI : I.IsKInjective) (hs : QuasiIso s) :
    (derivedPushforward.{w} f).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj (((Scheme.Modules.pushforward f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  have := (Stacks.SmallDerivedCategory.isIso_Qh_map_quotient_map_iff s).2 hs
  have := isIso_derivedPushforwardUnit_app_of_isKInjective.{w} f I hI
  (derivedPushforward.{w} f).mapIso (asIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) ≪≫
    (asIso ((derivedPushforwardUnit.{w} f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
    (Stacks.SmallDerivedCategory.mapHomotopyCategoryCompQhFactors
      (Scheme.Modules.pushforward f)).app I

/-- The cohomology sheaves of the object of `D(𝒪_X)` represented by a complex `K` are the
cohomology sheaves of `K`. -/
def homologyQhObjIso (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules n).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K)) ≅
      K.homology n :=
  (DerivedCategory.homologyFunctor X.Modules n).mapIso
      ((DerivedCategory.quotientCompQhIso X.Modules).app K) ≪≫
    (DerivedCategory.homologyFunctorFactors X.Modules n).app K

end AnyModel

/-! ### The bound with no derived category in the statement -/

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 08D5] part (2) with no derived category in the statement.** Let `f : X ⟶ Y` be
a quasi-compact and quasi-separated morphism of schemes with `Y` quasi-compact. There is an
integer `N`, depending on `f` alone, such that for every complex `K` of `𝒪_X`-modules whose
cohomology sheaves are quasi-coherent and vanish in degrees `> b`, and every quasi-isomorphism
`s : K ⟶ I` into a K-injective complex, the cohomology sheaves of `f_*I` — the complex computing
`Rf_*K` — vanish in degrees `≥ b + N`.

This is `Stacks.Duality.exists_isLE_derivedPushforward_obj` read at the object represented by `K`.
That object is `Rf_*K`, and `Stacks.Duality.derivedPushforwardObjIso` identifies it with the
object represented by `f_*I`. Separating the statement from the derived category is what lets it
be used at a model other than `CategoryTheory.HasDerivedCategory.standard`; see the module
documentation. -/
theorem exists_isZero_homology_modulePushforward_of_qcqs
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] :
    ∃ N : ℤ, ∀ (K I : CochainComplex X.Modules ℤ),
      (∀ n : ℤ, (K.homology n).IsQuasicoherent) → ∀ b : ℤ,
      (∀ n : ℤ, b < n → IsZero (K.homology n)) →
      ∀ s : K ⟶ I, I.IsKInjective → QuasiIso s → ∀ m : ℤ, b + N ≤ m →
        IsZero ((((Scheme.Modules.pushforward f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I).homology m) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj f
  refine ⟨N + 1, fun K I hqc b hle s hI hs m hm ↦ ?_⟩
  have hcoh : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient X.Modules
        (ComplexShape.up ℤ)).obj K))).IsQuasicoherent := fun n =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (homologyQhObjIso K n).symm (hqc n)
  have hEle : (DerivedCategory.Qh.obj ((HomotopyCategory.quotient X.Modules
      (ComplexShape.up ℤ)).obj K)).IsLE b :=
    (DerivedCategory.isLE_iff _ _).2 fun i hi ↦ (hle i hi).of_iso (homologyQhObjIso K i)
  have hpush := hN _ hcoh b hEle
  have hbase : IsZero ((DerivedCategory.homologyFunctor Y.Modules m).obj
      ((derivedPushforward f).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K)))) :=
    DerivedCategory.isZero_of_isLE _ (b + N) m (by omega)
  exact hbase.of_iso (((DerivedCategory.homologyFunctor Y.Modules m).mapIso
      (derivedPushforwardObjIso f s hI hs) ≪≫
    (DerivedCategory.homologyFunctorFactors Y.Modules m).app _).symm)

end Standard

/-! ### The bound at an arbitrary model -/

section AnyModel

variable [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- **[Stacks, Tag 08D5] part (2) at an arbitrary chosen model of the derived categories.** Let
`f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `Y` quasi-compact.
There is an integer `N`, depending on `f` alone, such that `H^m(Rf_*E) = 0` for `m ≥ b + N`
whenever `E` is an object of `D(𝒪_X)` with quasi-coherent cohomology living in degrees `≤ b`.

Every object of the derived category is represented by a complex `K`, and
`Stacks.Duality.derivedPushforwardObjIso` identifies `Rf_*E` with the object represented by `f_*I`
for a K-injective resolution `K ⟶ I`; the cohomology sheaves of that complex vanish in the stated
range by the model-free
`Stacks.Duality.exists_isZero_homology_modulePushforward_of_qcqs`. -/
theorem exists_isZero_homology_derivedPushforward_anyModel
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] :
    ∃ N : ℤ, ∀ E : DerivedCategory X.Modules,
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent) →
      ∀ b : ℤ, E.IsLE b → ∀ m : ℤ, b + N ≤ m →
        IsZero ((DerivedCategory.homologyFunctor Y.Modules m).obj
          ((derivedPushforward.{w} f).obj E)) := by
  obtain ⟨N, hN⟩ := exists_isZero_homology_modulePushforward_of_qcqs f
  refine ⟨N, fun E hcoh b hE m hm ↦ ?_⟩
  let K := DerivedCategory.Q.objPreimage E
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have eK : ∀ n : ℤ, (DerivedCategory.homologyFunctor X.Modules n).obj E ≅ K.homology n :=
    fun n => ((DerivedCategory.homologyFunctor X.Modules n).mapIso eQ).symm ≪≫
      (DerivedCategory.homologyFunctorFactors X.Modules n).app K
  have hKcoh : ∀ n : ℤ, (K.homology n).IsQuasicoherent := fun n =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (eK n) (hcoh n)
  have hKle : ∀ n : ℤ, b < n → IsZero (K.homology n) := fun n hn =>
    (DerivedCategory.isZero_of_isLE E b n hn).of_iso (eK n).symm
  obtain ⟨I, s, hI, hs⟩ := AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X K
  exact (hN K I hKcoh b hKle s hI hs m hm).of_iso
    ((((DerivedCategory.homologyFunctorFactors Y.Modules m).app _).symm ≪≫
      (DerivedCategory.homologyFunctor Y.Modules m).mapIso
        ((derivedPushforwardObjIso.{w} f s hI hs).symm ≪≫ (derivedPushforward.{w} f).mapIso
          ((DerivedCategory.quotientCompQhIso X.Modules).app K ≪≫ eQ))).symm)

/-- **[Stacks, Tag 08D5] part (2), at an arbitrary chosen model of the derived categories, in the
`IsLE` form.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `Y`
quasi-compact. There is an integer `N`, depending on `f` alone, such that `Rf_*E` lives in degrees
`≤ b + N` for every object `E` of `D(𝒪_X)` with quasi-coherent cohomology living in degrees `≤ b`.

This is `Stacks.Duality.exists_isLE_derivedPushforward_obj` with the choice of derived category a
binder rather than a term; the degree drops by one in the repackaging because
`Stacks.Duality.exists_isZero_homology_derivedPushforward_anyModel` asserts vanishing *at*
`b + N`. -/
@[stacks 08D5 "part (2), at an arbitrary derived category"]
theorem exists_isLE_derivedPushforward_obj_anyModel
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] :
    ∃ N : ℤ, ∀ E : DerivedCategory X.Modules,
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent) →
      ∀ b : ℤ, E.IsLE b → ((derivedPushforward.{w} f).obj E).IsLE (b + N) := by
  obtain ⟨N, hN⟩ := exists_isZero_homology_derivedPushforward_anyModel.{w} f
  exact ⟨N - 1, fun E hE b hb ↦
    (DerivedCategory.isLE_iff _ _).2 fun i hi ↦ hN E hE b hb i (by omega)⟩

end AnyModel

end Stacks.Duality

end
