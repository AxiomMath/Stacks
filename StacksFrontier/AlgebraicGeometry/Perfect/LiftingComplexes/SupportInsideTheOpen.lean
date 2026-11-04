module

public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme
public import StacksFrontier.RingTheory.Dualizing.Ext
import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a map from a perfect complex supported inside the open

Let `X` be a scheme, `U ⊆ X` an open subscheme and `T ⊆ X` a closed subset *contained in* `U`.
Let `E` be an object of the derived category of `𝒪_X`-modules and let `P` be a perfect object of
`D(𝒪_U)` whose cohomology is supported on `T`. Every map `α : P ⟶ E|_U` is the restriction of a
map `β : R ⟶ E` out of a perfect object `R` of `D(𝒪_X)` supported on `T`, with `P` a direct
summand of `R|_U` compatibly with `α` and `β|_U`. In fact `R|_U` *is* `P`, so the summand is the
whole of it.

The object is the extension by zero `j_! P`, and `β` is the transpose of `α` along the derived
adjunction `j_! ⊣ j^*`. Perfectness of `j_! P` is [Stacks, Tag 08DP] together with
[Stacks, Tag 08DF]: on an object whose cohomology is supported on a closed subset of `X` the
derived direct image agrees with extension by zero, and the derived direct image of a perfect
object with closed support is perfect. The inclusion `P ⟶ (j_! P)|_U` is the unit of the derived
adjunction, which is invertible because the underived unit is ([Stacks, Tag 00AB]); and the
compatibility is the triangle identity, in the form `η ≫ j^*(transpose) = id`.

## Main results

* `Stacks.Perfect.LiftingComplexes.isPerfect_jShriek_of_cohomologySupportedOn`: the extension by
  zero of a perfect object of `D(𝒪_U)` supported on a closed subset of `X` contained in `U` is
  perfect.
* `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_isClosed_subset`:
  [Stacks, Tag 09IM] for a closed subset contained in the open, where `R|_U` is `P` itself.

## Implementation notes

**This is not where [Stacks, Tag 09IM] is registered.** The general statement -- `T` closed with
retrocompact complement, so that `T` may meet `X ∖ U` -- is
`Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift`, which carries the tag; it is proved by
the source's induction over an affine cover of `X`, whose step glues the object already built over
a smaller open to the one the affine case produces over the next affine. The statement below is
kept because under the condition `T ⊆ U` none of that machinery is needed: the boundary of `U` is
disjoint from the support and extension by zero already lands in the perfect objects, which is a
shorter proof and a stronger conclusion -- `R|_U` *is* `P`, rather than containing it as a
summand.

The hypotheses of the general statement that this one does not use are dropped rather than
assumed: `X` need not be quasi-compact or quasi-separated, the complement of `T` need not be
retrocompact, and `E` need not have quasi-coherent cohomology.

The two spellings of restriction to an open subspace meet here, as they do in
[Stacks, Tag 08EP]: `AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace U` is
`ExtensionByZeroModules.jStar U X.ringCatSheaf`, definitionally. The statements below use the
first, and the proofs the second, which is the spelling the extension-by-zero adjunction and its
unit are stated in. The derived adjunction is reached by dot notation on the underived one, so
that its two functors are fixed by the adjunction's own type before the exactness instances are
looked for; the prefix form `Adjunction.mapDerivedCategory` searches for them against the first
spelling and does not find them.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology Stacks.Cohomology.ClosedSupportPerfect
open Stacks.Cohomology.PushforwardRestriction (extensionByZeroToDerivedPushforward
  cohomologySupportedOn_jShriek)

namespace Stacks.Perfect.LiftingComplexes

universe u

attribute [local instance 10000] HasDerivedCategory.standard


/-- **Extension by zero of a perfect object supported inside the open is perfect.** Let `T` be a
closed subset of a scheme `X` contained in an open subscheme `U`, and let `P` be a perfect object
of `D(𝒪_U)` whose cohomology is supported on `T`. Then `j_! P` is a perfect object of `D(𝒪_X)`.

The derived direct image `Rj_* P` is perfect by [Stacks, Tag 08DP], because the image of the
support in `X` is `T`, which is closed; and the comparison `j_! P ⟶ Rj_* P` is invertible on an
object with that support by [Stacks, Tag 08DF]. -/
theorem isPerfect_jShriek_of_cohomologySupportedOn
    (X : Scheme.{u}) (U : X.Opens) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    (P : DerivedCategory.{u + 1} (U : Scheme.{u}).Modules)
    (hP : RingedSpace.IsPerfect (X := (U : Scheme.{u}).toRingedSpace) P)
    (hPT : CohomologySupportedOn (U : Scheme.{u}).ringCatSheaf
      ((fun x : U ↦ (x.1 : X)) ⁻¹' T) P) :
    RingedSpace.IsPerfect (X := X.toRingedSpace)
      ((ExtensionByZeroModules.jShriek U X.ringCatSheaf).mapDerivedCategory.obj P) := by
  classical
  set O := X.ringCatSheaf
  have : (ExtensionByZeroModules.jPush U O).Additive := by
    have : (ExtensionByZeroModules.jPush U O).IsRightAdjoint :=
      (ExtensionByZeroModules.jStarAdjunction U O).isRightAdjoint
    exact Functor.additive_of_preserves_binary_products _
  let C := SheafOfModules.{u} (ExtensionByZeroModules.resRing U O)
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  let J := (ExtensionByZeroModules.jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh (C := SheafOfModules.{u} O)
  have hC : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f := by
    let R := (Stacks.Injectives.exists_functorial_quasiIso_isKInjective C).some
    exact fun K => ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K, R.quasiIso K⟩
  have : J.HasPointwiseRightDerivedFunctor W :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u + 1, u + 1, u + 1, u + 1} J hC).1
  let Rj := J.totalRightDerived (DerivedCategory.Qh (C := C)) W
  let αj := J.totalRightDerivedUnit (DerivedCategory.Qh (C := C)) W
  have hRj : Rj.IsRightDerivedFunctor αj W := inferInstance
  have hTimage : IsClosed ((X.toRingedSpace.ofRestrict U.isOpenEmbedding).hom.base ''
      ((fun x : U ↦ (x.1 : X)) ⁻¹' T)) := by
    have heq : (X.toRingedSpace.ofRestrict U.isOpenEmbedding).hom.base ''
        ((fun x : U ↦ (x.1 : X)) ⁻¹' T) = T := by
      ext x
      refine ⟨?_, fun hx => ⟨⟨x, hTU hx⟩, hx, rfl⟩⟩
      rintro ⟨y, hy, rfl⟩
      exact hy
    rwa [heq]
  have : IsIso ((extensionByZeroToDerivedPushforward O U Rj αj).app P) :=
    isIso_extensionByZeroToDerivedPushforward_app_of_supported' O U T hT hTU Rj αj hRj P hPT
  exact (isPerfect_derivedPushforward_of_closedSupport X.toRingedSpace U
      ((fun x : U ↦ (x.1 : X)) ⁻¹' T) hTimage Rj αj P hP hPT (hRj := hRj)).of_iso
    (asIso ((extensionByZeroToDerivedPushforward O U Rj αj).app P)).symm

/-- **The unit of the derived extension-by-zero adjunction is invertible.** The underived unit
of `j_! ⊣ j^*` is invertible by [Stacks, Tag 00AB], so the unit of the derived adjunction is
invertible on every object: a derived unit is invertible wherever the underived one inverts the
cohomology sheaves. -/
theorem isIso_derivedJShriekAdjunction_unit (X : Scheme.{u}) (U : X.Opens)
    (P : DerivedCategory.{u + 1} (U : Scheme.{u}).Modules) :
    IsIso ((ExtensionByZeroModules.jShriekAdjunction U
      X.ringCatSheaf).mapDerivedCategory.unit.app P) := by
  have := ExtensionByZeroModules.isIso_jShriekAdjunction_unit U X.ringCatSheaf
  exact @Dualizing.PowerTorsionBaseChange.mapDerivedAdjunction_unit_isIso.{u + 1, u + 1, u, u}
    (SheafOfModules.{u} (ExtensionByZeroModules.resRing U X.ringCatSheaf)) _ _
    (HasDerivedCategory.standard
      (SheafOfModules.{u} (ExtensionByZeroModules.resRing U X.ringCatSheaf)))
    (SheafOfModules.{u} X.ringCatSheaf) _ _
    (HasDerivedCategory.standard (SheafOfModules.{u} X.ringCatSheaf)) _ _ _ _ _ _ _ _
    (ExtensionByZeroModules.jShriekAdjunction U X.ringCatSheaf) P fun _ => inferInstance

/-- **[Stacks, Tag 09IM] for a closed subset contained in the open.** Let `X` be a scheme, `U` an
open subscheme, `T ⊆ U` a closed subset of `X`, and `E` an object of the derived category of
`𝒪_X`-modules. Every map `α : P ⟶ E|_U` out of a perfect object `P` of `D(𝒪_U)` whose cohomology
is supported on `T` comes from a map `β : R ⟶ E` out of a perfect object `R` of `D(𝒪_X)` whose
cohomology is supported on `T`, in the sense that `P` is a direct summand of `R|_U` by an
inclusion `i` with `i ≫ β|_U = α`.

Take `R = j_! P` and `β` the transpose of `α` along the derived adjunction `j_! ⊣ j^*`. The
inclusion is the unit of that adjunction, which is invertible, so the summand is all of `R|_U`;
and `i ≫ β|_U = α` is the identity `η ≫ j^*(transpose) = id` defining the transpose. -/
theorem exists_isPerfect_lift_of_isClosed_subset
    (X : Scheme.{u}) (U : X.Opens) (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    (E : DerivedCategory.{u + 1} X.Modules)
    (P : DerivedCategory.{u + 1} (U : Scheme.{u}).Modules)
    (hP : RingedSpace.IsPerfect (X := (U : Scheme.{u}).toRingedSpace) P)
    (hPT : CohomologySupportedOn (U : Scheme.{u}).ringCatSheaf
      ((fun x : U ↦ (x.1 : X)) ⁻¹' T) P)
    (α : P ⟶ (RingedSpace.restrictModules.{u, u} X.toRingedSpace U).mapDerivedCategory.obj E) :
    ∃ (R : DerivedCategory.{u + 1} X.Modules) (β : R ⟶ E),
      RingedSpace.IsPerfect (X := X.toRingedSpace) R ∧
      CohomologySupportedOn X.ringCatSheaf T R ∧
      ∃ (i : P ⟶
            (RingedSpace.restrictModules.{u, u} X.toRingedSpace U).mapDerivedCategory.obj R)
        (p : (RingedSpace.restrictModules.{u, u} X.toRingedSpace U).mapDerivedCategory.obj R ⟶
            P),
        i ≫ p = 𝟙 P ∧
        i ≫ (RingedSpace.restrictModules.{u, u}
          X.toRingedSpace U).mapDerivedCategory.map β = α := by
  classical
  have hunit := isIso_derivedJShriekAdjunction_unit X U P
  let adj := (ExtensionByZeroModules.jShriekAdjunction U X.ringCatSheaf).mapDerivedCategory
  let e := @asIso _ _ _ _ (adj.unit.app P) hunit
  exact ⟨(ExtensionByZeroModules.jShriek U X.ringCatSheaf).mapDerivedCategory.obj P,
    (adj.homEquiv P E).symm α,
    isPerfect_jShriek_of_cohomologySupportedOn X U T hT hTU P hP hPT,
    cohomologySupportedOn_jShriek X.ringCatSheaf U T P hPT,
    e.hom, e.inv, e.hom_inv_id,
    (adj.homEquiv_unit (X := P) (Y := E) (f := (adj.homEquiv P E).symm α)).symm.trans
      ((adj.homEquiv P E).apply_symm_apply α)⟩

end Stacks.Perfect.LiftingComplexes

end
