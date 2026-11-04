module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.CoverDetection
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Maps out of the derived pushforward of a complex with closed support inside the open

Let `X` be a scheme, `V ⊆ X` an open subscheme, `T ⊆ V` a closed subset of `X` and `K` an object
of `D(𝒪_V)` whose cohomology is supported on `T`. Then, for every `E` in `D(𝒪_X)` and every
`n ∈ ℤ`,

> `Hom_{D(𝒪_X)}(K'[n], E) ≅ Hom_{D(𝒪_V)}(K[n], E|_V)`, where `K' = R(V → X)_* K`,

and in particular one group vanishes exactly when the other does. This is the Hom identification
the proof of [Stacks, Tag 09IS] performs: there `V` is the affine open of the inductive step,
`T = X ∖ U` is the complement of the quasi-compact open already treated, `K` is the Koszul object
on equations cutting out `T` in `V`, and `K'` its pushforward, so that the vanishing of
`Hom(K'[n], E)` on `X` is exactly the hypothesis (2) of [Stacks, Tag 09IR] for `E|_V` on `V`.

The identification is **not** base change. It is the derived adjunction `j_! ⊣ j^*` of
[Stacks, Tag 08BT] together with the identification `j_! K = Rj_* K` of [Stacks, Tag 08DF],
part (2), which holds exactly because the cohomology of `K` is supported on a closed subset of
`X` contained in `V`.

## Main results

* `Stacks.ExtensionByZero.homShiftJShriekEquiv` — the adjunction bijection
  `Hom((j_! K)[n], E) ≅ Hom(K[n], E|_V)` on a ringed space, at an arbitrary model.
* `Stacks.DerivedQCoh.AnyModel.forall_hom_shift_derivedPushforward_eq_zero_iff` — the vanishing
  form of the identification for `Rj_*`, at the scheme level and at an arbitrary model.
* `Stacks.DerivedQCoh.AnyModel.rightOrthogonal_shiftClosure_singleton_derivedPushforward_iff` —
  the same, written as right orthogonality to the shift closure, which is the shape the
  compact-generation machinery of
  `StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/` consumes.

## Implementation notes

**Everything is at an arbitrary model.** `Stacks.ExtensionByZero`'s own derived form of
[Stacks, Tag 08BT], `exists_derivedJShriek_restriction_adjunction`, is proved under a file-local
`CategoryTheory.HasDerivedCategory.standard`, but that is a property of the statement, not of the
construction: `CategoryTheory.Adjunction.mapDerivedCategory` applied to the underived
`ExtensionByZeroModules.jShriekAdjunction` carries the model as an instance argument, and that is
what is used below. Likewise [Stacks, Tag 08DF] part (2) takes the derived pushforward and its
unit as arguments, so it applies verbatim to `Stacks.Duality.derivedPushforward V.ι` and the total
right derived unit of `Stacks.Duality.homotopyPushforward V.ι`, at whatever model those are read
at. This is what makes the results usable at the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which is the only model at which
[Stacks, Tag 09IS] is proved.

**The support hypothesis is `Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn`, not
`AlgebraicGeometry.CohomologySupportedOn`.** The two predicates have the same body; the first
carries a `[HasDerivedCategory _]` binder and the second is fixed to the standard model by a
file-local instance in `StacksFrontier/AlgebraicGeometry/Perfect/SupportedCohomology.lean`. Only the
first can be written here. The `@`-application of the predicate in the statement is what names the
model explicitly, the predicate being an `abbrev` whose model argument is otherwise found by
instance search.

**Why the three steps are applied with explicit instance arguments.** `Scheme.Modules X`,
`SheafOfModules X.ringCatSheaf` and `Stacks.StrictlyPerfect.OXMod X.toRingedSpace` are one type
written three ways, definitionally but not reducibly equal, and
`ExtensionByZeroModules.resRing V X.ringCatSheaf` is a fourth way of writing
`V.toScheme.ringCatSheaf`. Instance search does not cross between them, so each use site either
declares the instance it needs with `let` or hands it over positionally. In particular
`ExtensionByZeroModules.jStar V X.ringCatSheaf` is the same term as
`AlgebraicGeometry.RingedSpace.restrictModules X.toRingedSpace V`, and its exactness is taken from
the latter's instances so that
`Stacks.DerivedQCoh.AnyModel.derivedJStarIsoRestrictFunctor` applies to it.

## References

* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open TopologicalSpace
open ExtensionByZeroModules
open Stacks.Cohomology.PushforwardRestriction

universe v₁ u₁ u w w'

namespace CategoryTheory.ObjectProperty

/-- **Right orthogonality to the shift closure of a single object, written out.** An object `E` is
right orthogonal to the shift closure of `{K}` exactly when every morphism `K⟦n⟧ ⟶ E` vanishes,
for every integer `n`.

This is the general form of `Stacks.Koszul.Truncation.rightOrthogonal_koszulObject_iff`, which is
the same bookkeeping specialised to the Koszul object of
[Stacks, Tag 08CZ]; that declaration is the case `K = koszulObject f` and could be replaced by
this one. -/
theorem rightOrthogonal_shiftClosure_singleton_iff_forall_hom_eq_zero
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasShift C ℤ] (K E : C) :
    ((singleton K).shiftClosure ℤ).rightOrthogonal E ↔ ∀ (n : ℤ) (g : K⟦n⟧ ⟶ E), g = 0 := by
  constructor
  · intro h n g
    exact h g ⟨K, n, Iso.refl _, (singleton_iff K K).2 rfl⟩
  · rintro h Z g ⟨W, n, e, hW⟩
    obtain rfl := (singleton_iff _ _).1 hW
    rw [← cancel_epi e.inv, comp_zero]
    exact h n _

end CategoryTheory.ObjectProperty

namespace Stacks.ExtensionByZero

variable {Y : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (V : Opens Y)
  [HasDerivedCategory.{w} (SheafOfModules.{u} O)]
  [HasDerivedCategory.{w'} (SheafOfModules.{u} (resRing V O))]
  [(jShriek V O).Additive] [PreservesFiniteLimits (jShriek V O)]
  [PreservesFiniteColimits (jShriek V O)]
  [(jStar V O).Additive] [PreservesFiniteLimits (jStar V O)]
  [PreservesFiniteColimits (jStar V O)]

/-- **[Stacks, Tag 08BT] at an arbitrary model.** Extension by zero from an open subspace is left
adjoint to restriction on unbounded derived categories.

`Stacks.ExtensionByZero.exists_derivedJShriek_restriction_adjunction` is this adjunction with the
standard model installed; the construction itself does not need one, because
`CategoryTheory.Adjunction.mapDerivedCategory` takes both derived categories as instance
arguments. -/
noncomputable def derivedJShriekAdjunction :
    (jShriek V O).mapDerivedCategory ⊣ (jStar V O).mapDerivedCategory :=
  (jShriekAdjunction V O).mapDerivedCategory

/-- **Maps out of a shift of an extension by zero.** For `K` in `D(𝒪_V)` and `E` in `D(𝒪_Y)`,
morphisms `(j_! K)⟦n⟧ ⟶ E` correspond bijectively to morphisms `K⟦n⟧ ⟶ E|_V`.

The shift is moved across `j_!` by its commutation with the shift — `j_!` is exact, so
`CategoryTheory.Functor.mapDerivedCategory` of it is triangulated — and the resulting morphisms
out of `j_!(K⟦n⟧)` are transposed along
`Stacks.ExtensionByZero.derivedJShriekAdjunction`. -/
@[sga "4 XVII 5.1.3" "special case"]
noncomputable def homShiftJShriekEquiv
    (K : DerivedCategory (SheafOfModules.{u} (resRing V O)))
    (E : DerivedCategory (SheafOfModules.{u} O)) (n : ℤ) :
    (((jShriek V O).mapDerivedCategory.obj K)⟦n⟧ ⟶ E) ≃
      (K⟦n⟧ ⟶ (jStar V O).mapDerivedCategory.obj E) :=
  (Iso.homCongr
      (((jShriek V O).mapDerivedCategory.commShiftIso (A := ℤ) n).app K) (Iso.refl E)).symm.trans
    ((derivedJShriekAdjunction O V).homEquiv _ E)

/-- **The vanishing form of `Stacks.ExtensionByZero.homShiftJShriekEquiv`.** Every morphism from
every shift of `j_! K` into `E` vanishes exactly when every morphism from every shift of `K` into
`E|_V` does.

A bijection of Hom-groups need not be additive, so the transfer is made through
`Subsingleton`: a Hom-group all of whose elements vanish is a subsingleton, subsingletons
transfer along a bijection, and a subsingleton Hom-group has all its elements equal to zero
because it contains zero. -/
theorem forall_hom_shift_jShriek_eq_zero_iff
    (K : DerivedCategory (SheafOfModules.{u} (resRing V O)))
    (E : DerivedCategory (SheafOfModules.{u} O)) :
    (∀ (n : ℤ) (g : ((jShriek V O).mapDerivedCategory.obj K)⟦n⟧ ⟶ E), g = 0) ↔
      ∀ (n : ℤ) (g : K⟦n⟧ ⟶ (jStar V O).mapDerivedCategory.obj E), g = 0 :=
  forall_congr' fun n => (subsingleton_iff_forall_eq 0).symm.trans
    ((homShiftJShriekEquiv O V K E n).subsingleton_congr.trans (subsingleton_iff_forall_eq 0))

end Stacks.ExtensionByZero

namespace Stacks.DerivedQCoh.AnyModel

/-- The canonical comparison from degreewise direct image along the inclusion of an open
subscheme to `Stacks.Duality.derivedPushforward`, which is its total right derived functor. This
is the natural transformation the adjunction
`Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction` is built from, named so that
[Stacks, Tag 08DF] can be applied to that derived pushforward. -/
noncomputable def homotopyPushforwardUnit {X : Scheme.{u}} (V : X.Opens)
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} V.toScheme.Modules] :
    Stacks.Duality.homotopyPushforward V.ι ⟶
      DerivedCategory.Qh ⋙ Stacks.Duality.derivedPushforward V.ι :=
  (Stacks.Duality.homotopyPushforward V.ι).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso V.toScheme.Modules (ComplexShape.up ℤ))

/-- Vanishing of a Hom-group is transported along invertible maps on either side: conjugating by
`u` and `v` is a bijection between the two groups which carries zero to zero. -/
private theorem forall_hom_eq_zero_iff_of_isIso {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {A A' B B' : C} (u : A' ⟶ A) (v : B ⟶ B') [IsIso u] [IsIso v] :
    (∀ g : A ⟶ B, g = 0) ↔ ∀ g : A' ⟶ B', g = 0 := by
  have key : ∀ {A A' B B' : C} (u : A' ⟶ A) (v : B ⟶ B') [IsIso u] [IsIso v],
      (∀ g : A ⟶ B, g = 0) → ∀ g : A' ⟶ B', g = 0 := fun u v _ _ h g => by
    simpa using congrArg (fun k => u ≫ k ≫ v) (h (inv u ≫ g ≫ inv v))
  exact ⟨key u v, key (inv u) (inv v)⟩

variable {X : Scheme.{u}} (V : X.Opens)
  [hX : HasDerivedCategory.{w} X.Modules] [hV : HasDerivedCategory.{w} V.toScheme.Modules]
  (T : Set X) (hT : IsClosed T) (hTV : T ⊆ (V : Set X))
  (K : DerivedCategory V.toScheme.Modules)
  (hK : @CohomologySupportedOn _ (resRing V X.ringCatSheaf) hV
    ((fun x : Usp V ↦ x.1) ⁻¹' T) K)

include hT hTV hK

/-- **Maps out of a shift of `Rj_* K` vanish exactly when maps out of the corresponding shift of
`K` on `V` vanish.** Let `V` be an open subscheme of a scheme `X`, let `T ⊆ V` be closed in `X`
and let `K` be an object of `D(𝒪_V)` whose cohomology is supported on `T`. Then, for `E` in
`D(𝒪_X)`, every morphism `(Rj_* K)⟦n⟧ ⟶ E` vanishes for every `n` if and only if every morphism
`K⟦n⟧ ⟶ E|_V` does.

This is the Hom identification the proof of [Stacks, Tag 09IS] uses. Three steps: the comparison
`j_! K ⟶ Rj_* K` is invertible by [Stacks, Tag 08DF] part (2), the support hypothesis being
exactly its hypothesis; morphisms out of the shifts of `j_! K` are transposed to morphisms into
`E|_V` by `Stacks.ExtensionByZero.forall_hom_shift_jShriek_eq_zero_iff`, the derived form of
[Stacks, Tag 08BT]; and the restriction so produced is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` by
`Stacks.DerivedQCoh.AnyModel.derivedJStarIsoRestrictFunctor`. No base change is involved. -/
theorem forall_hom_shift_derivedPushforward_eq_zero_iff (E : DerivedCategory X.Modules) :
    (∀ (n : ℤ) (g : ((Stacks.Duality.derivedPushforward V.ι).obj K)⟦n⟧ ⟶ E), g = 0) ↔
      ∀ (n : ℤ)
        (g : K⟦n⟧ ⟶ (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj E), g = 0 := by
  let hjp : (jPush V X.ringCatSheaf).Additive := by
    have : (jPush V X.ringCatSheaf).IsRightAdjoint :=
      (jStarAdjunction V X.ringCatSheaf).isRightAdjoint
    exact Functor.additive_of_preserves_binary_products _
  have hRD : (Stacks.Duality.derivedPushforward V.ι).IsRightDerivedFunctor
      (homotopyPushforwardUnit V)
      (HomotopyCategory.quasiIso V.toScheme.Modules (ComplexShape.up ℤ)) :=
    inferInstanceAs ((Functor.totalRightDerived _ DerivedCategory.Qh _).IsRightDerivedFunctor
      (Functor.totalRightDerivedUnit _ DerivedCategory.Qh _) _)
  have hiso := @isIso_extensionByZeroToDerivedPushforward_app_of_supported _ X.ringCatSheaf V
    T hT hTV hX hV (Stacks.Duality.derivedPushforward V.ι)
    (homotopyPushforwardUnit V) hRD K hK
  let : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf) := hX
  let : HasDerivedCategory.{w} (SheafOfModules.{u} (resRing V X.ringCatSheaf)) := hV
  let : Category.{w, u + 1}
    (DerivedCategory (SheafOfModules.{u} (resRing V X.ringCatSheaf))) := inferInstance
  let : Category.{w, u + 1}
    (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) := inferInstance
  let : Preadditive (DerivedCategory (SheafOfModules.{u} (resRing V X.ringCatSheaf))) :=
    inferInstance
  let : Preadditive (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) := inferInstance
  let : (jStar V X.ringCatSheaf).Additive :=
    RingedSpace.restrictModules_additive X.toRingedSpace V
  let : PreservesFiniteLimits (jStar V X.ringCatSheaf) :=
    RingedSpace.restrictModules_preservesFiniteLimits X.toRingedSpace V
  let : PreservesFiniteColimits (jStar V X.ringCatSheaf) :=
    RingedSpace.restrictModules_preservesFiniteColimits X.toRingedSpace V
  refine (forall_congr' fun n =>
    @forall_hom_eq_zero_iff_of_isIso (DerivedCategory X.Modules) _ _ _ _ _ _
      ((shiftFunctor (DerivedCategory X.Modules) n).map
        ((@extensionByZeroToDerivedPushforward _ X.ringCatSheaf V hX hV
          (Stacks.Duality.derivedPushforward V.ι) (homotopyPushforwardUnit V)).app K))
      (𝟙 E)
      (@Functor.map_isIso _ _ _ _ _ _ (shiftFunctor (DerivedCategory X.Modules) n) _ hiso)
      (IsIso.id _)).trans ?_
  exact (Stacks.ExtensionByZero.forall_hom_shift_jShriek_eq_zero_iff X.ringCatSheaf V K E).trans
    (forall_congr' fun n =>
      @forall_hom_eq_zero_iff_of_isIso (DerivedCategory V.toScheme.Modules) _ _ _ _ _ _
        (𝟙 (K⟦n⟧)) ((derivedJStarIsoRestrictFunctor X V).app E).hom (IsIso.id _)
        (Iso.isIso_hom _))

/-- **The Hom identification of [Stacks, Tag 09IS] as an orthogonality condition.** An object `E`
of `D(𝒪_X)` is right orthogonal to the shift closure of `Rj_* K` exactly when `E|_V` is right
orthogonal to the shift closure of `K`, for `K` supported on a closed subset of `X` contained in
`V`.

This is the shape the generation step consumes: the hypothesis of
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_openImmersion` and of
[Stacks, Tag 09IR] are both stated through `ObjectProperty.shiftClosure`. -/
theorem rightOrthogonal_shiftClosure_singleton_derivedPushforward_iff
    (E : DerivedCategory X.Modules) :
    ((singleton ((Stacks.Duality.derivedPushforward V.ι).obj K)).shiftClosure ℤ).rightOrthogonal
        E ↔
      ((singleton K).shiftClosure ℤ).rightOrthogonal
        ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj E) :=
  (rightOrthogonal_shiftClosure_singleton_iff_forall_hom_eq_zero _ _).trans
    ((forall_hom_shift_derivedPushforward_eq_zero_iff V T hT hTV K hK E).trans
      (rightOrthogonal_shiftClosure_singleton_iff_forall_hom_eq_zero _ _).symm)

end Stacks.DerivedQCoh.AnyModel

end
