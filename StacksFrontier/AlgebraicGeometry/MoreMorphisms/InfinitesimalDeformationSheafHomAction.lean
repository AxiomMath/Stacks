module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheaf
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobal
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroPerturbation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The action of the sheaf of homomorphisms on the sheaf of infinitesimal deformations

Let `S` be a scheme, let `i : X ⟶ X'` be a first-order thickening, let `j : Y ⟶ Y'` be an
immersion, let `p : X' ⟶ S` and `q : Y' ⟶ S` be structure morphisms, let `a : X ⟶ Y` and let
`A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` be a map of `𝒪_X`-modules. [Stacks Project, Tag 04FH] makes the
rule assigning to an open `V` of `X'` the set of morphisms `V ⟶ Y'` over `S` restricting to `a`
on `X ∩ V` and inducing `A` there — the set of [Stacks Project, Tag 04FI] — into a sheaf of sets
on `X'`. [Stacks Project, Tag 04FJ] asserts that the sheaf
`SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` **acts** on that sheaf, simply transitively over any open
carrying a section.

This file proves the action half of that assertion for **arbitrary** schemes: the action, with its
two group laws, compatible with the restriction maps of the sheaf. The transitivity half is
`Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationSheafHomTransitivity.lean`,
which is built on this file's `Stacks.Thickenings.homSectionAct`. Nothing is affine; the datum
is the one of the source, a morphism of sheaves of `𝒪_X`-modules out of the pulled-back sheaf of
relative differentials read over an open; and the third condition of [Stacks Project, Tag 04FI]
is the equality of maps of conormal **sheaves**, not of conormal modules.

## How the sections of the sheaf of homomorphisms are read

The sections of `SheafHom_{𝒪_X}(M, N)` over an open `U` of `X` are, by the definition of the
internal hom of [Stacks Project, Tag 01CO], the `𝒪_U`-linear maps `M|_U ⟶ N|_U`. Here `M|_U` is
Mathlib's `SheafOfModules.over`, the restriction of `M` to the site of opens contained in `U`, so
a section is exactly a family of `Γ(X, W)`-linear maps `Γ(M, W) ⟶ Γ(N, W)`, one for each open
`W ≤ U`, compatible with restriction. That family is
`Stacks.Thickenings.moduleHomSections.app`, its restriction map to a smaller open is
`Stacks.Thickenings.moduleHomSections.restrict`, and the restriction map is restriction of the
family (`Stacks.Thickenings.moduleHomSections.restrict_app`), which holds by definition.

## Main definitions

* `Stacks.Thickenings.moduleHomSections`: the sections over an open of the sheaf of
  homomorphisms of two sheaves of modules, with `Stacks.Thickenings.moduleHomSections.app` and
  `Stacks.Thickenings.moduleHomSections.restrict`.
* `Stacks.Thickenings.deformationHomSections`: those sections for
  `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` over the part of `X` cut out by an open of `X'`. This is
  the group that acts.
* `Stacks.Thickenings.liftOpen`: the open of `X'` over which the comorphism of a lift over an
  open `V` of `X'` is read, and `Stacks.Thickenings.liftAppLE`, that comorphism.
* `Stacks.Thickenings.homSectionValue`: the derivation `D = θ ∘ d_{Y/S}` of Equation
  [Stacks Project, Tag 04BV], on sections, for a lift over an open.
* `Stacks.Thickenings.homSectionPerturbation`: that derivation as a
  `Stacks.Thickenings.SquareZeroPerturbation` of the lift.
* `Stacks.Thickenings.homSectionAct`: the lift `θ ⬝ b` of [Stacks Project, Tag 0CK1] over an open
  of `X'`.
* `Stacks.Thickenings.compatibleLiftsVAdd` and
  `Stacks.Thickenings.compatibleLiftsAddAction`: the action itself.

## Main results

* `Stacks.Thickenings.appLE_comm_of_comm_restrict`: the commuting square of a lift over an open,
  on sections — the identity that turns the Leibniz rule of the pulled-back universal
  differential into the Leibniz rule along the comorphism of the lift.
* `Stacks.Thickenings.homSectionAct_app`: Equation [Stacks Project, Tag 04BV] for `θ ⬝ b`.
* `Stacks.Thickenings.comm_homSectionAct`, `Stacks.Thickenings.comp_homSectionAct`,
  `Stacks.Thickenings.immersionConormalSheafMap_homSectionAct`: the three conditions of
  [Stacks Project, Tag 04FI] for `θ ⬝ b`.
* `Stacks.Thickenings.immersionConormalSheafMap_congr_of_appLE_eq`: two lifts with the same
  underlying map whose comorphisms agree on the defining ideal of `j` induce the same map of
  conormal sheaves.
* `Stacks.Thickenings.homSectionAct_zero` and `Stacks.Thickenings.homSectionAct_add`: the group
  laws of the action.
* `Stacks.Thickenings.compatibleLiftsRestrict_compatibleLiftsVAdd`: the action commutes with the
  restriction maps of the sheaf of [Stacks Project, Tag 04FH].
* `Stacks.Thickenings.exists_addAction_compatibleLifts`: the three previous groups of results
  assembled into the action clause of [Stacks Project, Tag 04FJ], which carries the attribute.
* `Stacks.Thickenings.eq_of_appLE_eq`: two lifts of `a` over an open with the same comorphism are
  equal, and `Stacks.Thickenings.homSectionAct_appLE`, Equation [Stacks Project, Tag 04BV] for
  `θ ⬝ b` over an arbitrary pair of opens.
* `Stacks.Thickenings.ker_morphismRestrict_sq_eq_bot`: the defining ideal of a first-order
  thickening restricted to an open is again square-zero.
* `Stacks.Thickenings.moduleHomSections.restrict_self`,
  `Stacks.Thickenings.moduleHomSections.restrict_restrict`,
  `Stacks.Thickenings.moduleHomSections.restrict_zero` and
  `Stacks.Thickenings.moduleHomSections.restrict_add`: the restriction maps of the sheaf of
  homomorphisms are functorial and additive, so that the sections over the opens of `X'` form a
  presheaf of additive groups and the action below is an action of presheaves of groups.

## Implementation notes

The moved lift is *constructed*, over an arbitrary open `V` of `X'` and with no affineness
anywhere, by `Stacks.Thickenings.SquareZeroPerturbation.perturb` applied to the lift
`b : V ⟶ Y'`: its comorphism over an open `W` of `Y'` is `b^♯ + D` with
`D g = θ (d_{Y/S} (j^♯ g))` read inside `𝒪_{X'}` through the inclusion
`Stacks.Thickenings.conormalSection` of the defining ideal. Multiplicativity is the square-zero
condition, `Stacks.Thickenings.conormalSection_mul_conormalSection`.

The one piece of bookkeeping is that the sections of `𝒪_V` over `b⁻¹W` are the sections of
`𝒪_{X'}` over `Stacks.Thickenings.liftOpen V b W`, the image of `b⁻¹W` in `X'`. These are the
same module, but not reducibly so, so the comorphism of the lift is named a second time in the
`𝒪_{X'}` reading as `Stacks.Thickenings.liftAppLE`, and the commuting square of the lift is
proved first over the image `(i⁻¹V).ι ''ᵁ ((i ∣_ V)⁻¹(b⁻¹W))` of the open of the restricted
thickening — where `AlgebraicGeometry.morphismRestrict_app'` applies verbatim — and then
restricted to `i⁻¹(liftOpen V b W)`, the two being equal by
`AlgebraicGeometry.image_morphismRestrict_preimage`.

Condition (3) is where the conormal *sheaves* enter. The affine characterisation
`Stacks.Immersion.IsInducedConormalSheafMap` of [Stacks Project, Tag 01R4] refers to the ambient
comorphism only through its values on the defining ideal of `j`, and `θ ⬝ b` and `b` agree there
because `d_{Y/S}` kills `j^♯` of such a section. So the map induced by `b` satisfies the
characterisation of the square of `θ ⬝ b`, and
`Stacks.Immersion.immersionConormalSheafMap_unique` identifies the two. That argument is isolated
as `Stacks.Thickenings.immersionConormalSheafMap_congr_of_appLE_eq`, for two arbitrary lifts: at
that generality the terms are small enough to elaborate inside one heartbeat budget, which they
are not when the perturbed lift is substituted first.

### Simple transitivity

The **transitivity** clause of [Stacks Project, Tag 04FJ] — that over an open carrying a lift the
action is simply transitive — is
`Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq`, in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationSheafHomTransitivity.lean`,
also for arbitrary schemes. It is this file's `Stacks.Thickenings.homSectionAct` identified with
the lift `θ ⬝ b` of the library's other conormal track
(`Stacks.Thickenings.derivationActionSheaf`), where the unrestricted
[Stacks Project, Tag 04FG] — `Stacks.Thickenings.exists_isDerivationAction` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDerivationSheaf.lean`, read for the
restricted thickening `i ∣_ V` — supplies the section and
`Stacks.Thickenings.eq_of_isDerivationAction` its uniqueness. The translation of the datum
between the two tracks is
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationConormalTrack.lean` and the
translation of the conormal inclusion is in the transitivity file itself.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Immersion Stacks.ClosedImmersion.IdealSheafAffine
open Stacks.ClosedImmersion.AffineConormal

universe u

namespace Stacks.Thickenings

/-! ### Sections of the sheaf of homomorphisms of two sheaves of modules -/

section HomSections

variable {X : Scheme.{u}} {M N : X.Modules}

/-- **The sections over an open `U` of the sheaf of homomorphisms** `SheafHom_{𝒪_X}(M, N)` of
[Stacks Project, Tag 01CO]: the `𝒪_U`-linear maps `M|_U ⟶ N|_U`, with `M|_U` the restriction
`SheafOfModules.over` of `M` to the site of opens contained in `U`. -/
abbrev moduleHomSections (M N : X.Modules) (U : X.Opens) : Type u := M.over U ⟶ N.over U

/-- **A section of `SheafHom_{𝒪_X}(M, N)` over `U`, read on sections over an open `W ≤ U`.** -/
def moduleHomSections.app {U : X.Opens} (θ : moduleHomSections M N U) {W : X.Opens}
    (hW : W ≤ U) (s : Γ(M, W)) : Γ(N, W) :=
  (θ.val.app (op (Over.mk (homOfLE hW)))).hom s

/-- A section of `SheafHom_{𝒪_X}(M, N)` acts additively on sections over `W`. -/
@[simp]
theorem moduleHomSections.app_add {U : X.Opens} (θ : moduleHomSections M N U) {W : X.Opens}
    (hW : W ≤ U) (s t : Γ(M, W)) : θ.app hW (s + t) = θ.app hW s + θ.app hW t :=
  map_add _ _ _

/-- A section of `SheafHom_{𝒪_X}(M, N)` sends the zero section over `W` to zero. -/
@[simp]
theorem moduleHomSections.app_zero {U : X.Opens} (θ : moduleHomSections M N U) {W : X.Opens}
    (hW : W ≤ U) : θ.app hW (0 : Γ(M, W)) = 0 :=
  map_zero _

/-- A section of `SheafHom_{𝒪_X}(M, N)` acts `Γ(X, W)`-linearly on sections over `W`. -/
theorem moduleHomSections.app_smul {U : X.Opens} (θ : moduleHomSections M N U) {W : X.Opens}
    (hW : W ≤ U) (r : Γ(X, W)) (s : Γ(M, W)) : θ.app hW (r • s) = r • θ.app hW s :=
  (θ.val.app (op (Over.mk (homOfLE hW)))).hom.map_smul r s

/-- **A section of `SheafHom_{𝒪_X}(M, N)` commutes with restriction of sections.** -/
theorem moduleHomSections.map_app {U : X.Opens} (θ : moduleHomSections M N U) {W W' : X.Opens}
    (hW : W ≤ U) (hW' : W' ≤ W) (s : Γ(M, W)) :
    θ.app (hW'.trans hW) (M.presheaf.map (homOfLE hW').op s)
      = N.presheaf.map (homOfLE hW').op (θ.app hW s) :=
  PresheafOfModules.naturality_apply θ.val
    (Over.homMk (homOfLE hW') (by exact Subsingleton.elim _ _) :
      Over.mk (homOfLE (hW'.trans hW)) ⟶ Over.mk (homOfLE hW)).op s

/-- The zero section of `SheafHom_{𝒪_X}(M, N)` sends every section over `W` to zero. -/
@[simp]
theorem moduleHomSections.zero_app {U : X.Opens} {W : X.Opens} (hW : W ≤ U) (s : Γ(M, W)) :
    (0 : moduleHomSections M N U).app hW s = 0 := rfl

/-- The sum of two sections of `SheafHom_{𝒪_X}(M, N)` acts on sections over `W` as the sum of
their actions. -/
@[simp]
theorem moduleHomSections.add_app {U : X.Opens} (θ η : moduleHomSections M N U) {W : X.Opens}
    (hW : W ≤ U) (s : Γ(M, W)) : (θ + η).app hW s = θ.app hW s + η.app hW s := rfl

/-- **The restriction map of `SheafHom_{𝒪_X}(M, N)`.** -/
def moduleHomSections.restrict {U U' : X.Opens} (hU : U' ≤ U) (θ : moduleHomSections M N U) :
    moduleHomSections M N U' :=
  (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE hU)).inv.app M ≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE hU)).map θ ≫
    (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE hU)).hom.app N

/-- **The restriction map of `SheafHom_{𝒪_X}(M, N)` is restriction of the family of maps on
sections**: a section over `U` and its restriction to `U'` act in the same way on the sections
over an open `W ≤ U'`. -/
@[simp]
theorem moduleHomSections.restrict_app {U U' : X.Opens} (hU : U' ≤ U)
    (θ : moduleHomSections M N U) {W : X.Opens} (hW : W ≤ U') (s : Γ(M, W)) :
    (moduleHomSections.restrict hU θ).app hW s = θ.app (hW.trans hU) s :=
  rfl

/-- **Restricting a section of `SheafHom_{𝒪_X}(M, N)` to the same open does nothing.** -/
@[simp]
theorem moduleHomSections.restrict_self {U : X.Opens} (θ : moduleHomSections M N U) :
    moduleHomSections.restrict le_rfl θ = θ := rfl

/-- **The restriction maps of `SheafHom_{𝒪_X}(M, N)` compose.** -/
theorem moduleHomSections.restrict_restrict {U U' U'' : X.Opens} (hU : U' ≤ U) (hU' : U'' ≤ U')
    (θ : moduleHomSections M N U) :
    moduleHomSections.restrict hU' (moduleHomSections.restrict hU θ)
      = moduleHomSections.restrict (hU'.trans hU) θ := rfl

/-- **The restriction maps of `SheafHom_{𝒪_X}(M, N)` are additive.** -/
@[simp]
theorem moduleHomSections.restrict_zero {U U' : X.Opens} (hU : U' ≤ U) :
    moduleHomSections.restrict (M := M) (N := N) hU 0 = 0 := rfl

/-- **The restriction maps of `SheafHom_{𝒪_X}(M, N)` are additive.** -/
theorem moduleHomSections.restrict_add {U U' : X.Opens} (hU : U' ≤ U)
    (θ η : moduleHomSections M N U) :
    moduleHomSections.restrict hU (θ + η)
      = moduleHomSections.restrict hU θ + moduleHomSections.restrict hU η := rfl

end HomSections


/-! ### The opens over which a lift over an open of `X'` is read -/

section Opens

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}

/-- **The open of `X'` carrying the comorphism of a lift over an open `V`.** For a morphism
`b : V ⟶ Y'` out of an open `V` of `X'` and an open `W` of `Y'`, the sections of `𝒪_V` over
`b⁻¹W` are the sections of `𝒪_{X'}` over this open of `X'`. -/
abbrev liftOpen (V : X'.Opens) (b : V.toScheme ⟶ Y') (W : Y'.Opens) : X'.Opens :=
  V.ι ''ᵁ (b ⁻¹ᵁ W)

/-- `Stacks.Thickenings.liftOpen` is contained in `V`. -/
theorem liftOpen_le (V : X'.Opens) (b : V.toScheme ⟶ Y') (W : Y'.Opens) :
    liftOpen V b W ≤ V :=
  V.ι_image_le _

/-- The part of `X` cut out by `Stacks.Thickenings.liftOpen` lies in the part cut out by `V`. -/
theorem preimage_liftOpen_le (i : X ⟶ X') (V : X'.Opens) (b : V.toScheme ⟶ Y')
    (W : Y'.Opens) : i ⁻¹ᵁ (liftOpen V b W) ≤ i ⁻¹ᵁ V :=
  i.preimage_mono (liftOpen_le V b W)

/-- **The comorphism of a lift over an open, read on `𝒪_{X'}`.** The component over `W` of the
comorphism of `b : V ⟶ Y'`, with its target written as the sections of `𝒪_{X'}` over
`Stacks.Thickenings.liftOpen`, which is the same module. -/
def liftAppLE (V : X'.Opens) (b : V.toScheme ⟶ Y') (W : Y'.Opens) :
    Γ(Y', W) ⟶ Γ(X', liftOpen V b W) :=
  b.appLE W (b ⁻¹ᵁ W) le_rfl

/-- `Stacks.Thickenings.liftAppLE` is the comorphism of `b` over `W`. -/
theorem liftAppLE_eq_app (V : X'.Opens) (b : V.toScheme ⟶ Y') (W : Y'.Opens) :
    liftAppLE V b W = b.app W :=
  Scheme.Hom.appLE_eq_app b

/-- **The part of `X` cut out by `Stacks.Thickenings.liftOpen` maps into `j⁻¹W`.** This is what
makes the pulled-back universal differential of a section of `𝒪_{Y'}` over `W` available there. -/
theorem preimage_liftOpen_le_preimage {V : X'.Opens} {b : V.toScheme ⟶ Y'}
    (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j) (W : Y'.Opens) :
    i ⁻¹ᵁ (liftOpen V b W) ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W) := by
  rw [← image_morphismRestrict_preimage i V (b ⁻¹ᵁ W), ← Scheme.Hom.comp_preimage, cb,
    Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  exact Scheme.Hom.image_preimage_le _ _

/-- **The commuting square of a lift over an open, on sections over the image open.** -/
private theorem liftAppLE_comp_appLE {V : X'.Opens} {b : V.toScheme ⟶ Y'}
    (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j) (W : Y'.Opens)
    (h1 : (i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)) ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) :
    liftAppLE V b W ≫
        i.appLE (liftOpen V b W) ((i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)))
          (image_morphismRestrict_preimage i V (b ⁻¹ᵁ W)).le
      = j.app W ≫ a.appLE (j ⁻¹ᵁ W) ((i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W))) h1 := by
  have h2 : ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)) ≤ ((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, cb]
  have hid : (i ⁻¹ᵁ V).ι.appLE ((i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)))
      ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)) (((i ⁻¹ᵁ V).ι.preimage_image_eq _).ge) = 𝟙 _ := by
    rw [Scheme.Opens.ι_appLE]
    exact X.presheaf.map_id _
  have hA : ((i ⁻¹ᵁ V).ι ≫ a).appLE (j ⁻¹ᵁ W) ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)) h2
      = a.appLE (j ⁻¹ᵁ W) ((i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W))) h1 :=
    ((Scheme.Hom.appLE_comp_appLE ((i ⁻¹ᵁ V).ι) a (j ⁻¹ᵁ W)
        ((i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W))) ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)) h1
        (((i ⁻¹ᵁ V).ι.preimage_image_eq _).ge)).symm.trans
      (congrArg (fun z : Γ(X, (i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W))) ⟶
          Γ(X, (i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W))) =>
        a.appLE (j ⁻¹ᵁ W) ((i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W))) h1 ≫ z) hid)).trans
      (Category.comp_id _)
  have hI : i.appLE (liftOpen V b W) ((i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)))
      (image_morphismRestrict_preimage i V (b ⁻¹ᵁ W)).le = (i ∣_ V).app (b ⁻¹ᵁ W) :=
    (morphismRestrict_app' i V (b ⁻¹ᵁ W)).symm
  have hstep2 : b.appLE W (b ⁻¹ᵁ W) le_rfl ≫ (i ∣_ V).app (b ⁻¹ᵁ W)
      = j.app W ≫ ((i ⁻¹ᵁ V).ι ≫ a).appLE (j ⁻¹ᵁ W) ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)) h2 := by
    rw [← Scheme.Hom.appLE_eq_app (f := i ∣_ V) (U := b ⁻¹ᵁ W),
      Scheme.Hom.appLE_comp_appLE (i ∣_ V) b W (b ⁻¹ᵁ W) _ le_rfl le_rfl,
      appLE_congr_hom cb W ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)) le_rfl h2,
      ← Scheme.Hom.appLE_eq_app (f := j) (U := W),
      Scheme.Hom.appLE_comp_appLE ((i ⁻¹ᵁ V).ι ≫ a) j W (j ⁻¹ᵁ W) _ le_rfl h2]
  exact (congrArg (fun z : Γ(X', liftOpen V b W) ⟶
      Γ(X, (i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W))) => liftAppLE V b W ≫ z) hI).trans
    (hstep2.trans (congrArg (fun z : Γ(Y, j ⁻¹ᵁ W) ⟶
      Γ(X, (i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W))) => j.app W ≫ z) hA))

/-- **The commuting square of a lift over an open, on sections.** For a lift `b : V ⟶ Y'` of
`a` along `j` over an open `V` of `X'`, the two routes from `Γ(Y', W)` to
`Γ(X, i⁻¹(liftOpen V b W))` agree: through `𝒪_Y` and `a`, or through `𝒪_{X'}` and `b`. -/
theorem appLE_comm_of_comm_restrict {V : X'.Opens} {b : V.toScheme ⟶ Y'}
    (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j) (W : Y'.Opens) (g : Γ(Y', W)) :
    (a.appLE (j ⁻¹ᵁ W) (i ⁻¹ᵁ (liftOpen V b W))
          (preimage_liftOpen_le_preimage cb W)).hom ((j.app W).hom g)
      = (i.app (liftOpen V b W)).hom ((liftAppLE V b W).hom g) := by
  have hE : (i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)) = i ⁻¹ᵁ (liftOpen V b W) :=
    image_morphismRestrict_preimage i V (b ⁻¹ᵁ W)
  have h1 : (i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W)) ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W) :=
    hE ▸ preimage_liftOpen_le_preimage cb W
  have hres := congrArg
    (fun z : Γ(Y', W) ⟶ Γ(X, (i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W))) =>
      z ≫ X.presheaf.map (homOfLE hE.ge).op) (liftAppLE_comp_appLE cb W h1)
  simp only [Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.appLE_eq_app] at hres
  exact (congrArg (fun z : Γ(Y', W) ⟶ Γ(X, i ⁻¹ᵁ (liftOpen V b W)) => z.hom g) hres).symm

end Opens

/-! ### The derivation attached to a section of the sheaf of homomorphisms -/

section Value

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}

/-- **The sections over the part of `X` cut out by an open `V` of `X'` of the sheaf
`SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})`.** This is the group that acts on the lifts of `a` over
`V`, the group of [Stacks Project, Tag 04FJ]. -/
abbrev deformationHomSections (i : X ⟶ X') [IsImmersion i] (a : X ⟶ Y) (pY : Y ⟶ S)
    (V : X'.Opens) : Type u :=
  moduleHomSections (Smooth.pullbackCotangentSheaf pY a) (conormalModules i) (i ⁻¹ᵁ V)

variable [IsClosedImmersion i] {V : X'.Opens} {b : V.toScheme ⟶ Y'}

/-- **The derivation `D = θ ∘ d_{Y/S}` of Equation [Stacks Project, Tag 04BV], on sections, for a
lift over an open.** For a section `θ` of `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` over the part of
`X` cut out by `V`, this is the composite
`Γ(Y', W) --j^♯--> Γ(Y, j⁻¹W) --d--> Γ(a^*Ω_{Y/S}, ·) --θ--> Γ(𝒞_{X/X'}, ·) ⟶ Γ(X', ·)`,
read over the open `Stacks.Thickenings.liftOpen` of `X'`. It is the perturbation that moves `b`
to `θ ⬝ b`. -/
def homSectionValue (hsq : i.ker ^ 2 = ⊥) (pY' : Y' ⟶ S)
    (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (θ : deformationHomSections i a (j ≫ pY') V) (W : Y'.Opens) (g : Γ(Y', W)) :
    Γ(X', liftOpen V b W) :=
  conormalSection hsq (liftOpen V b W)
    (θ.app (preimage_liftOpen_le i V b W)
      (Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W) (preimage_liftOpen_le_preimage cb W)
        ((j.app W).hom g)))

variable {hsq : i.ker ^ 2 = ⊥} {pY' : Y' ⟶ S} {cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j}
  {θ : deformationHomSections i a (j ≫ pY') V}

/-- `Stacks.Thickenings.homSectionValue` is additive. -/
theorem homSectionValue_add (W : Y'.Opens) (s t : Γ(Y', W)) :
    homSectionValue hsq pY' cb θ W (s + t)
      = homSectionValue hsq pY' cb θ W s + homSectionValue hsq pY' cb θ W t := by
  rw [homSectionValue, homSectionValue, homSectionValue, map_add, map_add,
    moduleHomSections.app_add, conormalSection_add]

/-- `Stacks.Thickenings.homSectionValue` kills the zero section. -/
theorem homSectionValue_zero (W : Y'.Opens) :
    homSectionValue hsq pY' cb θ W 0 = 0 := by
  rw [homSectionValue, map_zero, map_zero, moduleHomSections.app_zero, conormalSection_zero]

/-- `Stacks.Thickenings.homSectionValue` kills the unit section, as a derivation must. -/
theorem homSectionValue_one (W : Y'.Opens) :
    homSectionValue hsq pY' cb θ W 1 = 0 := by
  rw [homSectionValue, map_one, Smooth.pullbackD_one, moduleHomSections.app_zero,
    conormalSection_zero]

/-- **The values of `Stacks.Thickenings.homSectionValue` lie in the defining ideal of `i`.** -/
theorem homSectionValue_mem_ker (W : Y'.Opens) (g : Γ(Y', W)) :
    homSectionValue hsq pY' cb θ W g ∈ RingHom.ker (i.app (liftOpen V b W)).hom :=
  conormalSection_mem_ker hsq (liftOpen V b W) _

/-- **Two values of `Stacks.Thickenings.homSectionValue` multiply to zero**, the square-zero
condition that makes the perturbed comorphism multiplicative. -/
theorem homSectionValue_mul_homSectionValue (W : Y'.Opens) (s t : Γ(Y', W)) :
    homSectionValue hsq pY' cb θ W s * homSectionValue hsq pY' cb θ W t = 0 :=
  conormalSection_mul_conormalSection hsq (liftOpen V b W) _ _

/-- **The Leibniz rule for `Stacks.Thickenings.homSectionValue`**, along the comorphism of the
lift `b`: the scalar action of `Γ(Y, j⁻¹W)` on the conormal sections is multiplication by
`b^♯` through the commuting square of the lift. -/
theorem homSectionValue_leibniz (W : Y'.Opens) (s t : Γ(Y', W)) :
    homSectionValue hsq pY' cb θ W (s * t)
      = (liftAppLE V b W).hom s * homSectionValue hsq pY' cb θ W t
        + (liftAppLE V b W).hom t * homSectionValue hsq pY' cb θ W s := by
  rw [homSectionValue, homSectionValue, homSectionValue, map_mul, Smooth.pullbackD_mul',
    moduleHomSections.app_add, moduleHomSections.app_smul, moduleHomSections.app_smul,
    conormalSection_add, appLE_comm_of_comm_restrict cb W s,
    appLE_comm_of_comm_restrict cb W t, conormalSection_smul, conormalSection_smul]

/-- **`Stacks.Thickenings.homSectionValue` kills the sections pulled back from `S`**, which is
the `𝒪_S`-linearity of the universal derivation of `Ω_{Y/S}`. -/
theorem homSectionValue_appLE (W₀ : S.Opens) (W : Y'.Opens) (hW : W ≤ pY' ⁻¹ᵁ W₀)
    (r : Γ(S, W₀)) :
    homSectionValue hsq pY' cb θ W ((pY'.appLE W₀ W hW).hom r) = 0 := by
  have h1 := Scheme.Hom.appLE_comp_appLE j pY' W₀ W (j ⁻¹ᵁ W) hW le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h1
  have h2 : (j.app W).hom ((pY'.appLE W₀ W hW).hom r)
      = ((j ≫ pY').appLE W₀ (j ⁻¹ᵁ W) (le_rfl.trans ((TopologicalSpace.Opens.map j.base).map
          (homOfLE hW)).le)).hom r :=
    congrArg (fun z : Γ(S, W₀) ⟶ Γ(Y, j ⁻¹ᵁ W) => z.hom r) h1
  rw [homSectionValue, h2, Smooth.pullbackD_appLE, moduleHomSections.app_zero,
    conormalSection_zero]

/-- **`Stacks.Thickenings.homSectionValue` kills the defining ideal of `j`**, since the
universal differential is applied to the image of the section under `j^♯`. -/
theorem homSectionValue_eq_zero_of_app_eq_zero (W : Y'.Opens) (g : Γ(Y', W))
    (hg : (j.app W).hom g = 0) : homSectionValue hsq pY' cb θ W g = 0 := by
  rw [homSectionValue, hg, map_zero, moduleHomSections.app_zero, conormalSection_zero]

/-- **`Stacks.Thickenings.homSectionValue` commutes with restriction to a smaller open of
`Y'`.** -/
theorem homSectionValue_map {W W' : Y'.Opens} (hW : W' ≤ W) (s : Γ(Y', W)) :
    homSectionValue hsq pY' cb θ W' ((Y'.presheaf.map (homOfLE hW).op).hom s)
      = (X'.presheaf.map (homOfLE (V.ι.image_mono (b.preimage_mono hW))).op).hom
          (homSectionValue hsq pY' cb θ W s) := by
  have hUle : i ⁻¹ᵁ (liftOpen V b W') ≤ i ⁻¹ᵁ (liftOpen V b W) :=
    i.preimage_mono (V.ι.image_mono (b.preimage_mono hW))
  have hn := Scheme.Hom.map_appLE j (le_rfl : j ⁻¹ᵁ W' ≤ j ⁻¹ᵁ W') (homOfLE hW).op
  rw [Scheme.Hom.appLE_eq_app] at hn
  have hj : (j.app W').hom ((Y'.presheaf.map (homOfLE hW).op).hom s)
      = (Y.presheaf.map (homOfLE (j.preimage_mono hW)).op).hom ((j.app W).hom s) :=
    congrArg (fun z : Γ(Y', W) ⟶ Γ(Y, j ⁻¹ᵁ W') => z.hom s) hn
  have hmid : i ⁻¹ᵁ (liftOpen V b W') ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W) :=
    hUle.trans (preimage_liftOpen_le_preimage cb W)
  rw [homSectionValue, homSectionValue, hj,
    pullbackD_shrink' (j ≫ pY') a (j.preimage_mono hW) hmid
      (preimage_liftOpen_le_preimage cb W') ((j.app W).hom s),
    ← Smooth.map_pullbackD (j ≫ pY') a (j ⁻¹ᵁ W) (preimage_liftOpen_le_preimage cb W) hmid hUle,
    moduleHomSections.map_app θ (preimage_liftOpen_le i V b W) hUle,
    conormalSection_map hsq (V.ι.image_mono (b.preimage_mono hW))]

end Value

/-! ### The lift moved by a section of the sheaf of homomorphisms -/

section Act

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
  [IsClosedImmersion i] {V : X'.Opens} {b : V.toScheme ⟶ Y'}
  {hsq : i.ker ^ 2 = ⊥} {pY' : Y' ⟶ S} {cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j}
  {θ : deformationHomSections i a (j ≫ pY') V}

/-- `Stacks.Thickenings.liftAppLE` and the comorphism of `b` have the same value on a section. -/
theorem liftAppLE_hom_apply (V : X'.Opens) (b : V.toScheme ⟶ Y') (W : Y'.Opens)
    (g : Γ(Y', W)) : (liftAppLE V b W).hom g = (b.app W).hom g :=
  congrArg (fun z : Γ(Y', W) ⟶ Γ(X', liftOpen V b W) => z.hom g) (liftAppLE_eq_app V b W)

/-- Restriction of sections on an open subscheme is restriction of sections on the ambient
scheme. -/
theorem toScheme_presheaf_map_homOfLE {V : X'.Opens} {O O' : V.toScheme.Opens} (h : O' ≤ O) :
    V.toScheme.presheaf.map (homOfLE h).op
      = X'.presheaf.map (homOfLE (V.ι.image_mono h)).op :=
  congrArg (fun z : (V.ι ''ᵁ O') ⟶ (V.ι ''ᵁ O) => X'.presheaf.map z.op)
    (Subsingleton.elim _ _)

/-- The comorphism of `f` over `W` and `O` is the comorphism over `W`, restricted to `O`. -/
private theorem appLE_hom_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {W : Y.Opens} {O : X.Opens}
    (h : O ≤ f ⁻¹ᵁ W) (g : Γ(Y, W)) :
    (f.appLE W O h).hom g = (X.presheaf.map (homOfLE h).op).hom ((f.app W).hom g) :=
  rfl

/-- **The derivation `D = θ ∘ d_{Y/S}` as a square-zero perturbation of the lift `b`.** -/
@[sga "3 III 4.9" "partial"]
def homSectionPerturbation (hsq : i.ker ^ 2 = ⊥) (pY' : Y' ⟶ S)
    (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (θ : deformationHomSections i a (j ≫ pY') V) : SquareZeroPerturbation b where
  value W g := homSectionValue hsq pY' cb θ W g
  value_zero W := homSectionValue_zero W
  value_one W := homSectionValue_one W
  value_add W s t := homSectionValue_add W s t
  value_leibniz W s t := by
    rw [← liftAppLE_hom_apply V b W s, ← liftAppLE_hom_apply V b W t]
    exact homSectionValue_leibniz W s t
  value_mul_value W s t := homSectionValue_mul_homSectionValue W s t
  value_naturality hWV s := by
    rw [toScheme_presheaf_map_homOfLE (b.preimage_mono hWV)]
    exact homSectionValue_map hWV s

/-- **The lift `θ ⬝ b` of [Stacks Project, Tag 0CK1] over an open of `X'`.** The morphism
`V ⟶ Y'` with the same underlying map as `b` and comorphism `b^♯ + D`, where
`D = θ ∘ d_{Y/S}` is the derivation of Equation [Stacks Project, Tag 04BV] attached to the
section `θ` of `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` over the part of `X` cut out by `V`. -/
def homSectionAct (hsq : i.ker ^ 2 = ⊥) (pY' : Y' ⟶ S)
    (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (θ : deformationHomSections i a (j ≫ pY') V) : V.toScheme ⟶ Y' :=
  (homSectionPerturbation hsq pY' cb θ).perturb

/-- `θ ⬝ b` has the same underlying map as `b`. -/
@[simp]
theorem homSectionAct_base : (homSectionAct hsq pY' cb θ).base = b.base := rfl

/-- `θ ⬝ b` has the same preimages of opens as `b`. -/
theorem homSectionAct_preimage (W : Y'.Opens) :
    homSectionAct hsq pY' cb θ ⁻¹ᵁ W = b ⁻¹ᵁ W := rfl

/-- **Equation [Stacks Project, Tag 04BV]: the comorphism of `θ ⬝ b` is `b^♯ + D`.** -/
theorem homSectionAct_app (W : Y'.Opens) (g : Γ(Y', W)) :
    ((homSectionAct hsq pY' cb θ).app W).hom g =
      @HAdd.hAdd Γ(V.toScheme, b ⁻¹ᵁ W) Γ(V.toScheme, b ⁻¹ᵁ W) Γ(V.toScheme, b ⁻¹ᵁ W)
        inferInstance ((b.app W).hom g) (homSectionValue hsq pY' cb θ W g) :=
  SquareZeroPerturbation.perturb_app (homSectionPerturbation hsq pY' cb θ) W g

/-- `θ ⬝ b` and `b` have the same comorphism on a section where the perturbation vanishes. -/
private theorem homSectionAct_app_of_homSectionValue_eq_zero {W : Y'.Opens} {g : Γ(Y', W)}
    (hz : homSectionValue hsq pY' cb θ W g = 0) :
    ((homSectionAct hsq pY' cb θ).app W).hom g = (b.app W).hom g :=
  (homSectionAct_app W g).trans
    ((congrArg (fun z : Γ(V.toScheme, b ⁻¹ᵁ W) => (b.app W).hom g + z) hz).trans (add_zero _))

/-- **The comorphism of `i ∣_ V` kills the values of the perturbation**, because they are
sections of the defining ideal of `i`. -/
theorem morphismRestrict_app_homSectionValue (W : Y'.Opens) (g : Γ(Y', W)) :
    ((i ∣_ V).app (b ⁻¹ᵁ W)).hom (homSectionValue hsq pY' cb θ W g) = 0 :=
  (congrArg
      (fun z : Γ(X', liftOpen V b W) ⟶
          Γ(X, (i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W))) =>
        z.hom (homSectionValue hsq pY' cb θ W g))
      (morphismRestrict_app' i V (b ⁻¹ᵁ W))).trans (by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply,
      RingHom.mem_ker.mp (homSectionValue_mem_ker W g), map_zero]
    rfl)

/-- **`θ ⬝ b` is again a lift of `a` along `j`**, condition (2) of [Stacks Project, Tag 04FI].
The perturbation takes values in the defining ideal of `i`, so it disappears after composing
with `i ∣_ V`. -/
theorem comm_homSectionAct :
    i ∣_ V ≫ homSectionAct hsq pY' cb θ = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j := by
  refine Eq.trans ?_ cb
  refine Scheme.Hom.ext rfl (fun W ↦ CommRingCat.hom_ext (RingHom.ext fun g ↦ ?_))
  refine (CommRingCat.comp_apply _ _ g).trans ((presheaf_map_self _ _).trans ?_)
  refine (congrArg ((i ∣_ V).app (b ⁻¹ᵁ W)).hom (homSectionAct_app W g)).trans ?_
  refine (map_add _ _ _).trans ?_
  rw [morphismRestrict_app_homSectionValue, add_zero]
  rfl

/-- **`θ ⬝ b` is again a morphism over the base `S`**, condition (1) of
[Stacks Project, Tag 04FI]. The perturbation kills the sections pulled back from `S`, because a
derivation is `𝒪_S`-linear. -/
theorem comp_homSectionAct {pX' : X' ⟶ S} (hb : b ≫ pY' = V.ι ≫ pX') :
    homSectionAct hsq pY' cb θ ≫ pY' = V.ι ≫ pX' := by
  refine Eq.trans ?_ hb
  refine Scheme.Hom.ext rfl (fun W₀ ↦ CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_))
  refine (CommRingCat.comp_apply _ _ r).trans ((presheaf_map_self _ _).trans ?_)
  have hz : homSectionValue hsq pY' cb θ (pY' ⁻¹ᵁ W₀) ((pY'.app W₀).hom r) = 0 := by
    rw [← Scheme.Hom.appLE_eq_app (f := pY') (U := W₀)]
    exact homSectionValue_appLE W₀ (pY' ⁻¹ᵁ W₀) le_rfl r
  have ha : ((b ≫ pY').app W₀).hom r = (b.app (pY' ⁻¹ᵁ W₀)).hom ((pY'.app W₀).hom r) := rfl
  exact (homSectionAct_app_of_homSectionValue_eq_zero hz).trans ha.symm

end Act

/-! ### Two lifts agreeing on the defining ideal induce the same map of conormal sheaves -/

section ConormalCongr

variable {Z Z' W W' : Scheme.{u}}

/-- **A section of an ideal with an affine model is killed by the comorphism.** -/
theorem app_eq_zero_of_mem_affineModel (j : W ⟶ W') [IsImmersion j] (W₀ : W'.Opens)
    (hW₀ : IsAffineOpen W₀) (J : Ideal Γ(W', W₀))
    (eW : CategoryTheory.Limits.pullback j W₀.ι ≅ Spec (quotRing J))
    (heW : CategoryTheory.Limits.pullback.snd j W₀.ι ≫ hW₀.isoSpec.hom =
      eW.hom ≫ quotImmersion Γ(W', W₀) J)
    (α : J) : (j.app W₀).hom (α : Γ(W', W₀)) = 0 := by
  have hJ : RingHom.ker (j.appLE W₀ (j ⁻¹ᵁ W₀) le_rfl).hom = J :=
    Stacks.Conormal.ker_appLE_eq_of_affineModel j W₀ hW₀ J eW heW
  rw [← Scheme.Hom.appLE_eq_app (f := j) (U := W₀)]
  exact RingHom.mem_ker.mp (hJ.ge α.2)

/-- **Two lifts with the same underlying map and the same comorphism on the defining ideal of `j`
induce the same map of conormal sheaves.** The affine characterisation
`Stacks.Immersion.IsInducedConormalSheafMap` of [Stacks Project, Tag 01R4] refers to the ambient
comorphism only through its values on the defining ideal of `j`, so the map induced by one of the
two squares satisfies the characterisation of the other, and
`Stacks.Immersion.immersionConormalSheafMap_unique` identifies them. -/
theorem immersionConormalSheafMap_congr_of_appLE_eq (i : Z ⟶ Z') (j : W ⟶ W')
    [IsImmersion i] [IsImmersion j] (f : Z ⟶ W) (k k' : Z' ⟶ W')
    (ck : i ≫ k = f ≫ j) (ck' : i ≫ k' = f ≫ j)
    (hbase : ∀ W₀ : W'.Opens, k' ⁻¹ᵁ W₀ ≤ k ⁻¹ᵁ W₀)
    (happ : ∀ (U : Z'.Opens) (W₀ : W'.Opens) (h : U ≤ k ⁻¹ᵁ W₀) (h' : U ≤ k' ⁻¹ᵁ W₀)
      (g : Γ(W', W₀)), (j.app W₀).hom g = 0 →
        (k'.appLE W₀ U h').hom g = (k.appLE W₀ U h).hom g) :
    immersionConormalSheafMap i j f k' (toShHom_square ck')
      = immersionConormalSheafMap i j f k (toShHom_square ck) := by
  refine (immersionConormalSheafMap_unique i j f k' ck' _ ?_).symm
  intro U hU W₀ hW₀ hUW I J eZ heZ eW heW α β hβ
  exact isInducedConormalSheafMap_immersionConormalSheafMap i j f k ck U hU W₀ hW₀
    (hUW.trans (hbase W₀)) I J eZ heZ eW heW α β
    (hβ.trans (happ U W₀ (hUW.trans (hbase W₀)) hUW (α : Γ(W', W₀))
      (app_eq_zero_of_mem_affineModel j W₀ hW₀ J eW heW α)))

end ConormalCongr

/-! ### The moved lift induces the same map of conormal sheaves -/

section Conormal

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
  [IsClosedImmersion i] [IsImmersion j] {V : X'.Opens} {b : V.toScheme ⟶ Y'}
  {hsq : i.ker ^ 2 = ⊥} {pY' : Y' ⟶ S} {cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j}
  {θ : deformationHomSections i a (j ≫ pY') V}

/-- **`θ ⬝ b` and `b` have the same comorphism on the defining ideal of `j`**, because the
perturbation is `θ` applied to the universal differential of a section killed by `j^♯`. -/
theorem homSectionAct_appLE_of_app_eq_zero {U : V.toScheme.Opens} {W : Y'.Opens}
    (h : U ≤ b ⁻¹ᵁ W) (h' : U ≤ homSectionAct hsq pY' cb θ ⁻¹ᵁ W) (g : Γ(Y', W))
    (hg : (j.app W).hom g = 0) :
    ((homSectionAct hsq pY' cb θ).appLE W U h').hom g = (b.appLE W U h).hom g := by
  rw [appLE_hom_apply _ h', appLE_hom_apply _ h,
    homSectionAct_app_of_homSectionValue_eq_zero (homSectionValue_eq_zero_of_app_eq_zero W g hg)]
  rfl

/-- **`θ ⬝ b` induces the same map of conormal sheaves as `b`**, condition (3) of
[Stacks Project, Tag 04FI]. It is
`Stacks.Thickenings.immersionConormalSheafMap_congr_of_appLE_eq` applied to the two lifts, whose
comorphisms agree on the defining ideal of `j` by
`Stacks.Thickenings.homSectionAct_appLE_of_app_eq_zero`. -/
theorem immersionConormalSheafMap_homSectionAct :
    immersionConormalSheafMap (i ∣_ V) j ((i ⁻¹ᵁ V).ι ≫ a) (homSectionAct hsq pY' cb θ)
        (toShHom_square (comm_homSectionAct (θ := θ)))
      = immersionConormalSheafMap (i ∣_ V) j ((i ⁻¹ᵁ V).ι ≫ a) b (toShHom_square cb) :=
  immersionConormalSheafMap_congr_of_appLE_eq (i ∣_ V) j ((i ⁻¹ᵁ V).ι ≫ a) b
    (homSectionAct hsq pY' cb θ) cb (comm_homSectionAct (θ := θ))
    (fun W₀ ↦ (homSectionAct_preimage W₀).le)
    fun _ _ h h' g hg ↦ homSectionAct_appLE_of_app_eq_zero h h' g hg

end Conormal

/-! ### The action laws -/

section Laws

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
  [IsClosedImmersion i] {V : X'.Opens} {b : V.toScheme ⟶ Y'}
  {hsq : i.ker ^ 2 = ⊥} {pY' : Y' ⟶ S} {cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j}

/-- The zero section of `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` has zero perturbation. -/
theorem homSectionValue_zero_section (W : Y'.Opens) (g : Γ(Y', W)) :
    homSectionValue hsq pY' cb (0 : deformationHomSections i a (j ≫ pY') V) W g = 0 := by
  rw [homSectionValue, moduleHomSections.zero_app, conormalSection_zero]

/-- The perturbation attached to a sum of two sections is the sum of the two perturbations. -/
theorem homSectionValue_add_section (θ η : deformationHomSections i a (j ≫ pY') V)
    (W : Y'.Opens) (g : Γ(Y', W)) :
    homSectionValue hsq pY' cb (θ + η) W g
      = homSectionValue hsq pY' cb θ W g + homSectionValue hsq pY' cb η W g := by
  rw [homSectionValue, homSectionValue, homSectionValue, moduleHomSections.add_app,
    conormalSection_add]

variable {θ η : deformationHomSections i a (j ≫ pY') V}

/-- **The perturbation does not see which lift it is attached to**, since the two lifts have the
same preimages of opens and the commuting square enters only through a proof. -/
theorem homSectionValue_of_comm_homSectionAct (W : Y'.Opens) (g : Γ(Y', W)) :
    homSectionValue hsq pY'
        (comm_homSectionAct (hsq := hsq) (pY' := pY') (cb := cb) (θ := η)) θ W g
      = homSectionValue hsq pY' cb θ W g := rfl

/-- **The zero section fixes every lift.** -/
theorem homSectionAct_zero :
    homSectionAct hsq pY' cb (0 : deformationHomSections i a (j ≫ pY') V) = b := by
  refine Scheme.Hom.ext rfl (fun W ↦ CommRingCat.hom_ext (RingHom.ext fun g ↦ ?_))
  refine (CommRingCat.comp_apply _ _ g).trans ((presheaf_map_self _ _).trans ?_)
  exact homSectionAct_app_of_homSectionValue_eq_zero (homSectionValue_zero_section W g)

/-- **A sum acts as the composite of the two actions**: moving a lift by `θ + η` is moving it by
`η` and then moving the result by `θ`. -/
theorem homSectionAct_add :
    homSectionAct hsq pY' cb (θ + η)
      = homSectionAct hsq pY'
          (comm_homSectionAct (hsq := hsq) (pY' := pY') (cb := cb) (θ := η)) θ := by
  refine Scheme.Hom.ext rfl (fun W ↦ CommRingCat.hom_ext (RingHom.ext fun g ↦ ?_))
  refine (CommRingCat.comp_apply _ _ g).trans ((presheaf_map_self _ _).trans ?_)
  rw [homSectionAct_app, homSectionAct_app, homSectionAct_app, homSectionValue_add_section]
  exact (add_assoc _ _ _).symm.trans (add_right_comm _ _ _)

end Laws

/-! ### Restricting the action to a smaller open -/

section Restrict

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
  [IsClosedImmersion i] {V : X'.Opens} {b : V.toScheme ⟶ Y'}
  {hsq : i.ker ^ 2 = ⊥} {pY' : Y' ⟶ S} {cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j}
  {θ : deformationHomSections i a (j ≫ pY') V}

/-- `Stacks.Thickenings.liftOpen` shrinks when the open of `X'` does. -/
theorem liftOpen_homOfLE_le {V V' : X'.Opens} (hV : V' ≤ V) (b : V.toScheme ⟶ Y')
    (W : Y'.Opens) : liftOpen V' (X'.homOfLE hV ≫ b) W ≤ liftOpen V b W :=
  X'.ι_image_homOfLE_le_ι_image hV (b ⁻¹ᵁ W)

/-- **The perturbation commutes with restriction to a smaller open of `X'`.** The perturbation of
the restricted lift by the restricted section of `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` is the
restriction of the perturbation. -/
theorem homOfLE_app_homSectionValue {V' : X'.Opens} (hV : V' ≤ V)
    (cb' : i ∣_ V' ≫ (X'.homOfLE hV ≫ b) = ((i ⁻¹ᵁ V').ι ≫ a) ≫ j) (W : Y'.Opens)
    (g : Γ(Y', W)) :
    ((X'.homOfLE hV).app (b ⁻¹ᵁ W)).hom (homSectionValue hsq pY' cb θ W g)
      = homSectionValue hsq pY' cb'
          (moduleHomSections.restrict (i.preimage_mono hV) θ) W g := by
  have hmap : ((X'.homOfLE hV).app (b ⁻¹ᵁ W) :
        Γ(X', liftOpen V b W) ⟶ Γ(X', liftOpen V' (X'.homOfLE hV ≫ b) W))
      = X'.presheaf.map (homOfLE (liftOpen_homOfLE_le hV b W)).op :=
    Scheme.homOfLE_app hV (b ⁻¹ᵁ W)
  refine (congrArg (fun z : Γ(X', liftOpen V b W) ⟶ Γ(X', liftOpen V' (X'.homOfLE hV ≫ b) W) =>
    z.hom (homSectionValue hsq pY' cb θ W g)) hmap).trans ?_
  rw [homSectionValue, homSectionValue,
    conormalSection_map hsq (liftOpen_homOfLE_le hV b W),
    ← moduleHomSections.map_app θ (preimage_liftOpen_le i V b W)
      (i.preimage_mono (liftOpen_homOfLE_le hV b W)),
    Smooth.map_pullbackD (j ≫ pY') a (j ⁻¹ᵁ W) (preimage_liftOpen_le_preimage cb W)
      ((i.preimage_mono (liftOpen_homOfLE_le hV b W)).trans
        (preimage_liftOpen_le_preimage cb W))
      (i.preimage_mono (liftOpen_homOfLE_le hV b W))]
  rfl

/-- **The action commutes with restriction to a smaller open of `X'`.** Restricting `θ ⬝ b` to a
smaller open `V'` of `X'` is acting on the restriction of `b` by the restriction of `θ`, which is
what makes the action of [Stacks Project, Tag 04FJ] an action on the sheaf of
[Stacks Project, Tag 04FH]. -/
theorem homOfLE_comp_homSectionAct {V' : X'.Opens} (hV : V' ≤ V)
    (cb' : i ∣_ V' ≫ (X'.homOfLE hV ≫ b) = ((i ⁻¹ᵁ V').ι ≫ a) ≫ j) :
    X'.homOfLE hV ≫ homSectionAct hsq pY' cb θ
      = homSectionAct hsq pY' cb' (moduleHomSections.restrict (i.preimage_mono hV) θ) := by
  refine Scheme.Hom.ext rfl (fun W ↦ CommRingCat.hom_ext (RingHom.ext fun g ↦ ?_))
  refine (CommRingCat.comp_apply _ _ g).trans ((presheaf_map_self _ _).trans ?_)
  refine (congrArg ((X'.homOfLE hV).app (b ⁻¹ᵁ W)).hom (homSectionAct_app W g)).trans ?_
  refine (map_add _ _ _).trans ?_
  rw [homSectionAct_app, homOfLE_app_homSectionValue hV cb' W g]
  rfl

end Restrict

/-! ### The action on the sheaf of infinitesimal deformations -/

section CompatibleLifts

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} [IsClosedImmersion i]
  [IsImmersion j]

/-- **The action of a section of `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` on a compatible lift**,
the action of [Stacks Project, Tag 04FJ] over an open `V` of `X'`. The lift `θ ⬝ b` of
`Stacks.Thickenings.homSectionAct` is again one of the lifts of [Stacks Project, Tag 04FI]: it is
a morphism over `S` (`Stacks.Thickenings.comp_homSectionAct`), it restricts to `a` on the part of
`X` cut out by `V` (`Stacks.Thickenings.comm_homSectionAct`), and it induces the same map of
conormal sheaves (`Stacks.Thickenings.immersionConormalSheafMap_homSectionAct`). -/
def compatibleLiftsVAdd (hsq : i.ker ^ 2 = ⊥) (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens)
    (θ : deformationHomSections i a (j ≫ pY') V) (c : compatibleLifts pX' pY' a A V) :
    compatibleLifts pX' pY' a A V :=
  ⟨homSectionAct hsq pY' c.2.2.choose θ, comp_homSectionAct c.2.1, comm_homSectionAct,
    immersionConormalSheafMap_homSectionAct.trans c.2.2.choose_spec⟩

/-- The lift underlying `Stacks.Thickenings.compatibleLiftsVAdd` is
`Stacks.Thickenings.homSectionAct`. -/
theorem compatibleLiftsVAdd_coe (hsq : i.ker ^ 2 = ⊥) (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens)
    (θ : deformationHomSections i a (j ≫ pY') V) (c : compatibleLifts pX' pY' a A V) :
    (compatibleLiftsVAdd hsq pX' pY' a A V θ c).1 = homSectionAct hsq pY' c.2.2.choose θ := rfl

/-- **The additive group of sections of `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` over the part of
`X` cut out by `V` acts on the lifts of [Stacks Project, Tag 04FI] over `V`.** -/
@[instance_reducible]
def compatibleLiftsAddAction (hsq : i.ker ^ 2 = ⊥) (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens) :
    AddAction (deformationHomSections i a (j ≫ pY') V) (compatibleLifts pX' pY' a A V) where
  vadd θ c := compatibleLiftsVAdd hsq pX' pY' a A V θ c
  zero_vadd _ := Subtype.ext homSectionAct_zero
  add_vadd _ _ _ := Subtype.ext homSectionAct_add

/-- **The action is compatible with the restriction maps of the sheaf of
[Stacks Project, Tag 04FH].** -/
theorem compatibleLiftsRestrict_compatibleLiftsVAdd (hsq : i.ker ^ 2 = ⊥) (pX' : X' ⟶ S)
    (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) {V V' : X'.Opens} (hV : V' ≤ V)
    (θ : deformationHomSections i a (j ≫ pY') V) (c : compatibleLifts pX' pY' a A V) :
    compatibleLiftsRestrict pX' pY' a A hV (compatibleLiftsVAdd hsq pX' pY' a A V θ c)
      = compatibleLiftsVAdd hsq pX' pY' a A V'
          (moduleHomSections.restrict (i.preimage_mono hV) θ)
          (compatibleLiftsRestrict pX' pY' a A hV c) :=
  Subtype.ext (homOfLE_comp_homSectionAct hV _)

/-- **The restriction map of the sheaf of [Stacks Project, Tag 04FH]** is
`Stacks.Thickenings.compatibleLiftsRestrict`. -/
theorem compatibleLiftsPresheaf_map (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) {V V' : X'.Opens} (hV : V' ≤ V) :
    (compatibleLiftsPresheaf pX' pY' a A).map (homOfLE hV).op
      = compatibleLiftsRestrict pX' pY' a A hV := rfl

/-- **The sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` acts on the sheaf of
[Stacks Project, Tag 04FI]**, [Stacks Project, Tag 04FJ] for arbitrary schemes.

Let `S` be a scheme, let `i : X ⟶ X'` be a first-order thickening, let `j : Y ⟶ Y'` be an
immersion, let `p : X' ⟶ S` and `q : Y' ⟶ S` be the structure morphisms, let `a : X ⟶ Y` and let
`A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` be a map of `𝒪_X`-modules. For every open `V` of `X'` the additive
group of sections of `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` over the part `i⁻¹V` of `X` cut out
by `V` acts on the set `Stacks.Thickenings.compatibleLifts` of [Stacks Project, Tag 04FI] of
lifts of `a` over `V` inducing `A`, and the action commutes with the restriction maps of the
sheaf `Stacks.Thickenings.compatibleLiftsPresheaf` of [Stacks Project, Tag 04FH]: it is an action
of sheaves.

Nothing is affine, the datum is the one of the source — a morphism of sheaves of `𝒪_X`-modules
out of the pulled-back sheaf of relative differentials, read over an open — and the third
condition of [Stacks Project, Tag 04FI] is the equality of maps of conormal **sheaves**.

The action is `Stacks.Thickenings.compatibleLiftsVAdd`, the group laws are
`Stacks.Thickenings.homSectionAct_zero` and `Stacks.Thickenings.homSectionAct_add`, and the
compatibility with restriction is
`Stacks.Thickenings.compatibleLiftsRestrict_compatibleLiftsVAdd`. -/
@[stacks 04FJ "the action of SheafHom(a^*Ω, 𝒞) on the sheaf of Tag 04FI, for arbitrary schemes"]
theorem exists_addAction_compatibleLifts (hsq : i.ker ^ 2 = ⊥) (pX' : X' ⟶ S) (pY' : Y' ⟶ S)
    (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) :
    ∃ act : ∀ V : X'.Opens, deformationHomSections i a (j ≫ pY') V →
        compatibleLifts pX' pY' a A V → compatibleLifts pX' pY' a A V,
      (∀ (V : X'.Opens) (c : compatibleLifts pX' pY' a A V), act V 0 c = c) ∧
        (∀ (V : X'.Opens) (θ η : deformationHomSections i a (j ≫ pY') V)
          (c : compatibleLifts pX' pY' a A V), act V (θ + η) c = act V θ (act V η c)) ∧
        ∀ (V V' : X'.Opens) (hV : V' ≤ V) (θ : deformationHomSections i a (j ≫ pY') V)
          (c : compatibleLifts pX' pY' a A V),
          compatibleLiftsRestrict pX' pY' a A hV (act V θ c)
            = act V' (moduleHomSections.restrict (i.preimage_mono hV) θ)
                (compatibleLiftsRestrict pX' pY' a A hV c) :=
  ⟨fun V θ c => compatibleLiftsVAdd hsq pX' pY' a A V θ c,
    fun _ _ => Subtype.ext homSectionAct_zero,
    fun _ _ _ _ => Subtype.ext homSectionAct_add,
    fun _ _ hV θ c => compatibleLiftsRestrict_compatibleLiftsVAdd hsq pX' pY' a A hV θ c⟩

end CompatibleLifts

/-! ### Towards simple transitivity -/

section Transitivity

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
  [IsClosedImmersion i] {V : X'.Opens}

/-- **The defining ideal of a restricted first-order thickening is square-zero.** -/
theorem ker_morphismRestrict_sq_eq_bot (hsq : i.ker ^ 2 = ⊥) (V : X'.Opens) :
    (i ∣_ V).ker ^ 2 = ⊥ :=
  (IsFirstOrderThickening.morphismRestrict ⟨inferInstance, hsq⟩ V).2

/-- **Two lifts of `a` over an open with the same comorphism are equal.** The underlying maps
agree because the restricted thickening is surjective, and the comorphisms are then forced to
agree open by open. -/
theorem eq_of_appLE_eq (hsq : i.ker ^ 2 = ⊥) {b c : V.toScheme ⟶ Y'}
    (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (cc : i ∣_ V ≫ c = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (h : ∀ (W : Y'.Opens) (O : V.toScheme.Opens) (hA : O ≤ b ⁻¹ᵁ W) (g : Γ(Y', W)),
      (c.appLE W O (le_preimage_of_comm (ker_morphismRestrict_sq_eq_bot hsq V) cb cc hA)).hom g
        = (b.appLE W O hA).hom g) :
    c = b := by
  refine Scheme.Hom.ext
    (base_eq_of_comm (ker_morphismRestrict_sq_eq_bot hsq V) cb cc) fun W ↦ ?_
  refine CommRingCat.hom_ext (RingHom.ext fun g ↦ ?_)
  have hmap : ∀ ζ : (b ⁻¹ᵁ W : V.toScheme.Opens) ⟶ c ⁻¹ᵁ W,
      (V.toScheme.presheaf.map ζ.op).hom ((c.app W).hom g)
        = (c.appLE W (b ⁻¹ᵁ W)
            (le_preimage_of_comm (ker_morphismRestrict_sq_eq_bot hsq V) cb cc
              le_rfl)).hom g := by
    intro ζ
    rw [presheaf_map_eq ζ.op (homOfLE (le_preimage_of_comm
      (ker_morphismRestrict_sq_eq_bot hsq V) cb cc (le_refl (b ⁻¹ᵁ W)))).op]
    rfl
  refine Eq.trans (hmap _) ?_
  rw [h W (b ⁻¹ᵁ W) le_rfl g, Scheme.Hom.appLE_eq_app]

variable {b : V.toScheme ⟶ Y'} {hsq : i.ker ^ 2 = ⊥} {pY' : Y' ⟶ S}
  {cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j}
  {θ : deformationHomSections i a (j ≫ pY') V}

/-- **Equation [Stacks Project, Tag 04BV] for `θ ⬝ b`, over an arbitrary pair of opens.** -/
theorem homSectionAct_appLE (W : Y'.Opens) (O : V.toScheme.Opens) (hA : O ≤ b ⁻¹ᵁ W)
    (hA' : O ≤ homSectionAct hsq pY' cb θ ⁻¹ᵁ W) (g : Γ(Y', W)) :
    ((homSectionAct hsq pY' cb θ).appLE W O hA').hom g
      = (b.appLE W O hA).hom g
        + (V.toScheme.presheaf.map (homOfLE hA).op).hom
            (homSectionValue hsq pY' cb θ W g) := by
  rw [appLE_hom_apply _ hA', appLE_hom_apply _ hA, homSectionAct_app]
  exact map_add _ _ _

end Transitivity

end Stacks.Thickenings

end
