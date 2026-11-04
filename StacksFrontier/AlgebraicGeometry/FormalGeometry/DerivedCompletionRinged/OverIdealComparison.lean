module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompletionUnitRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.OverIdealGlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# `K^∧|_U` is the derived completion of `K|_U`

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪`, let
`ℐ = (f_1, …, f_r)` be the sheaf of ideals they generate and let `U` be an object of `𝒞`. This
file proves, for such an `ℐ`, the assertion of [Stacks, Tag 0A0F]: *derived completion commutes
with restriction to the localized ringed site* `(𝒞/U, 𝒪_U)`, along the restricted sheaf of ideals
`ℐ|_U`, with both completion functors those of [Stacks, Tag 099B]. The Remark itself, for `ℐ` of
finite type and the completion functors of [Stacks, Tag 099F], is
`AlgebraicGeometry.RingedSite.derivedCompletion_restrict` of
`LocalizationCompletionFiniteType.lean`, which carries the tag.

Everything here is stated at `ℐ|_U = AlgebraicGeometry.RingedSite.overIdeal ℐ U`, the sheaf of
ideals whose sections over `V/U` are the sections of `ℐ` over `V` — the restriction of `ℐ` the
Remark is about — and the reflector of [Stacks, Tag 099F] is supplied on both sites by
[Stacks, Tag 099B], so no declaration below takes the existence of a derived completion functor
as an input. The one typeclass input is `HasWeakSheafify X.J CommRingCat`, the standing
assumption under which this library builds the Čech completion functor; the slice inherits it.

## Main definitions

All declarations below are in the namespace `AlgebraicGeometry.RingedSite`.

* `derivedCompletionRestrictComparisonOverIdeal`: the map `a` of [Stacks, Tag 0A0F] for such an
  `ℐ`, the canonical natural map `(K|_U)^∧ ⟶ K^∧|_U`, where the completion on the slice is along
  `ℐ|_U`.
* `derivedCompletionRestrictIsoOverIdeal`: the assertion of [Stacks, Tag 0A0F] for such an `ℐ` —
  the natural isomorphism `(-)|_U ⋙ (-)^∧_{ℐ|_U} ≅ (-)^∧_ℐ ⋙ (-)|_U` of functors
  `D(𝒪) ⥤ D(𝒪_U)`, which says that `K^∧|_U` *is* the derived completion of `K|_U`.

## Main results

* `isRightAdjoint_ι_isDerivedComplete_overIdeal_idealOfGlobalSections`: the conclusion of
  [Stacks, Tag 099F] at `ℐ|_U` on the slice, from [Stacks, Tag 099B] there.
* `derivedCompletionUnit_comp_derivedCompletionRestrictComparisonOverIdeal`: the identity that
  singles `a` out among all maps `(K|_U)^∧ ⟶ K^∧|_U` — its composite with the completion map
  `K|_U ⟶ (K|_U)^∧` is the restriction of the completion map `K ⟶ K^∧`.
* `isIso_derivedCompletionRestrictComparisonOverIdeal_app`: **`a` is an isomorphism at every
  `K`.**

## Implementation notes

**The two sheaves of ideals on the slice.** `CompletionUnitRestriction.lean` proves `a` invertible
with the completion on the slice taken along `(f_1|_U, …, f_r|_U)`, the sheaf of ideals generated
*on the slice* by the restricted generators, because that is the ideal sheaf for which
[Stacks, Tag 099B] directly supplies a reflector there. The Remark is about `ℐ|_U`. The two agree,
by `overIdeal_idealOfGlobalSections` of `OverIdealGlobalSections.lean`, so
`isIso_derivedCompletionRestrictComparison_of_eq_idealOfGlobalSections_app` below transports that
invertibility along the equality and the statements here are about `ℐ|_U` itself.

**How the reflector reaches `ℐ|_U`.** `isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections`
of `CompletionIdempotent.lean` — [Stacks, Tag 099B], with no hypothesis — gives the reflector of
`D(𝒪_U)` at `(f_1|_U, …, f_r|_U)`; rewriting along the same equality of sheaves of ideals moves
it to `ℐ|_U`. On `(𝒞, 𝒪)` the reflector at `ℐ` is that tag applied to `f_1, …, f_r` themselves.

**The Remark's second route.** Besides the construction that proves the assertion, the source
offers an argument through a second canonical map `b : K^∧ ⟶ Rj_*((K|_U)^∧)` built from
[Stacks, Tag 099J], and says of the final step — that the adjoint of `b` inverts `a` — that it is
formal and omits it. The invertibility of `a` is proved here through the first route, the Čech
construction of [Stacks, Tag 099B], which is the one the source names first: "it follows from the
construction in the proof of the proposition". The map `b` and its adjoint, for `ℐ` of finite
type, are `derivedCompletion_restrict_secondMap` of `LocalizationCompletionPushforward.lean`.

## References

* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0F](https://stacks.math.columbia.edu/tag/0A0F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (U : X.C) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **The conclusion of [Stacks, Tag 099F] on the slice, at the restricted sheaf of ideals
itself.** For `ℐ = (f_1, …, f_r)` the inclusion of the objects of `D(𝒪_U)` derived complete along
`ℐ|_U` into `D(𝒪_U)` has a left adjoint.

`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections`, which is
[Stacks, Tag 099B], gives this at the sheaf of ideals generated on the slice by the restricted
generators `f_1|_U, …, f_r|_U`; that sheaf of ideals is `ℐ|_U`, by
`AlgebraicGeometry.RingedSite.overIdeal_idealOfGlobalSections`. -/
theorem isRightAdjoint_ι_isDerivedComplete_overIdeal_idealOfGlobalSections :
    (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} (X.over U)
      (overIdeal (idealOfGlobalSections X f) U))).IsRightAdjoint :=
  overIdeal_idealOfGlobalSections X U f ▸
    isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections (X.over U)
      (fun i ↦ globalSectionOver X U (f i))

/-- **The canonical map `a : (K|_U)^∧ ⟶ K^∧|_U` of [Stacks, Tag 0A0F]**, natural in `K`, in the
special case of
`ℐ = (f_1, …, f_r)` the sheaf of ideals generated by a finite family of global sections of `𝒪`
and the completion on the slice taken along the restriction `ℐ|_U`.

It is `AlgebraicGeometry.RingedSite.derivedCompletionRestrictComparison` of
`LocalizationCompletion.lean` with both reflectors supplied by [Stacks, Tag 099B]: upstairs by
`isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections`, on the slice by
`isRightAdjoint_ι_isDerivedComplete_overIdeal_idealOfGlobalSections`. The containment the
construction consumes is an identity here, since the sections of `ℐ|_U` over `V/U` are by
definition those of `ℐ` over `V`.

That this map is an isomorphism at every `K` is
`isIso_derivedCompletionRestrictComparisonOverIdeal_app` below. -/
def derivedCompletionRestrictComparisonOverIdeal :
    letI := isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections X f
    letI := isRightAdjoint_ι_isDerivedComplete_overIdeal_idealOfGlobalSections X U f
    (SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory ⋙
        derivedCompletion (X.over U) (overIdeal (idealOfGlobalSections X f) U) ⟶
      derivedCompletion X (idealOfGlobalSections X f) ⋙
        (SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory :=
  let := isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections X f
  let := isRightAdjoint_ι_isDerivedComplete_overIdeal_idealOfGlobalSections X U f
  derivedCompletionRestrictComparison X (idealOfGlobalSections X f) U
    (overIdeal (idealOfGlobalSections X f) U) (fun _ _ hg ↦ hg)

/-- **The identity that singles out the map `a` of [Stacks, Tag 0A0F]**: its composite with the
completion map `K|_U ⟶ (K|_U)^∧` is the restriction of the completion map `K ⟶ K^∧`. By
`AlgebraicGeometry.RingedSite.eq_derivedCompletionRestrictComparison_of_derivedCompletionUnit_comp`
no other map `(K|_U)^∧ ⟶ K^∧|_U` has this property. -/
theorem derivedCompletionUnit_comp_derivedCompletionRestrictComparisonOverIdeal
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    letI := isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections X f
    letI := isRightAdjoint_ι_isDerivedComplete_overIdeal_idealOfGlobalSections X U f
    (derivedCompletionUnit (X.over U) (overIdeal (idealOfGlobalSections X f) U)).app
          ((SheafOfModules.overFunctor.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K) ≫
        (derivedCompletionRestrictComparisonOverIdeal X U f).app K =
      (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.map
        ((derivedCompletionUnit X (idealOfGlobalSections X f)).app K) :=
  let := isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections X f
  let := isRightAdjoint_ι_isDerivedComplete_overIdeal_idealOfGlobalSections X U f
  derivedCompletionUnit_comp_derivedCompletionRestrictComparison X (idealOfGlobalSections X f) U
    (overIdeal (idealOfGlobalSections X f) U) (fun _ _ hg ↦ hg) K

/-- **The invertibility of `a` transported along an equality of sheaves of ideals on the slice.**
`AlgebraicGeometry.RingedSite.isIso_derivedCompletionRestrictComparisonGlobalSections_app` proves
`a` invertible when the completion on the slice is taken along the sheaf of ideals generated
there by `f_1|_U, …, f_r|_U`; any sheaf of ideals equal to that one gives the same map, so `a` is
invertible for it too. -/
theorem isIso_derivedCompletionRestrictComparison_of_eq_idealOfGlobalSections_app
    (IU : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))))
    (hIU : IU = idealOfGlobalSections (X.over U) (fun i ↦ globalSectionOver X U (f i)))
    (hmem : ∀ (W : Over U)
      (g : ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)).obj.obj (op W)),
      g ∈ IU.toSubmodule.obj (op W) →
        g ∈ (idealOfGlobalSections X f).toSubmodule.obj (op W.left))
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    letI := isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections X f
    letI : (ObjectProperty.ι
        (IsDerivedComplete.{u, u, u, u} (X.over U) IU)).IsRightAdjoint :=
      hIU ▸ isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections (X.over U)
        (fun i ↦ globalSectionOver X U (f i))
    IsIso ((derivedCompletionRestrictComparison X
        (idealOfGlobalSections X f) U IU hmem).app K) := by
  subst hIU
  exact isIso_derivedCompletionRestrictComparisonGlobalSections_app X U f K

/-- **The canonical map `a : (K|_U)^∧ ⟶ K^∧|_U` of [Stacks, Tag 0A0F] is an isomorphism**, for
`ℐ = (f_1, …, f_r)` generated by a finite family of global sections of `𝒪` and the completion on
the slice taken along the restriction `ℐ|_U`.

`isIso_derivedCompletionRestrictComparison_of_eq_idealOfGlobalSections_app` at the equality
`AlgebraicGeometry.RingedSite.overIdeal_idealOfGlobalSections`. -/
theorem isIso_derivedCompletionRestrictComparisonOverIdeal_app
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    letI := isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections X f
    letI := isRightAdjoint_ι_isDerivedComplete_overIdeal_idealOfGlobalSections X U f
    IsIso ((derivedCompletionRestrictComparisonOverIdeal X U f).app K) :=
  isIso_derivedCompletionRestrictComparison_of_eq_idealOfGlobalSections_app X U f
    (overIdeal (idealOfGlobalSections X f) U) (overIdeal_idealOfGlobalSections X U f)
    (fun _ _ hg ↦ hg) K

/-- **`K^∧|_U` is the derived completion of `K|_U`**, the assertion of [Stacks, Tag 0A0F], here
for the special case of
`ℐ = (f_1, …, f_r)` the sheaf of ideals generated by a finite family of global sections of `𝒪`
and `U` any object of `𝒞`, derived completion along `ℐ` followed by restriction to the localized
ringed site `(𝒞/U, 𝒪_U)` is isomorphic, naturally in `K`, to restriction followed by derived
completion along the restricted sheaf of ideals `ℐ|_U`.

The isomorphism is the Remark's canonical map `a`, which
`derivedCompletionUnit_comp_derivedCompletionRestrictComparisonOverIdeal` pins down as the one
compatible with the two completion maps; it is invertible at every `K` by
`isIso_derivedCompletionRestrictComparisonOverIdeal_app`. -/
def derivedCompletionRestrictIsoOverIdeal :
    letI := isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections X f
    letI := isRightAdjoint_ι_isDerivedComplete_overIdeal_idealOfGlobalSections X U f
    (SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory ⋙
        derivedCompletion (X.over U) (overIdeal (idealOfGlobalSections X f) U) ≅
      derivedCompletion X (idealOfGlobalSections X f) ⋙
        (SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory :=
  let := isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections X f
  let := isRightAdjoint_ι_isDerivedComplete_overIdeal_idealOfGlobalSections X U f
  let : ∀ K, IsIso ((derivedCompletionRestrictComparisonOverIdeal X U f).app K) :=
    isIso_derivedCompletionRestrictComparisonOverIdeal_app X U f
  let := NatIso.isIso_of_isIso_app (derivedCompletionRestrictComparisonOverIdeal X U f)
  asIso (derivedCompletionRestrictComparisonOverIdeal X U f)

end AlgebraicGeometry.RingedSite

end
