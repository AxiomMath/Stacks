module

public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension of coherent reflexive modules across a depth-two complement

Let `X` be a locally Noetherian scheme and `j : U ⟶ X` an open subscheme whose complement
consists of points at which `𝒪_X` has depth at least two. [Stacks, Tag 0EBJ] asserts that `j^*`
and `j_*` are inverse equivalences between the coherent reflexive `𝒪_X`-modules and the coherent
reflexive `𝒪_U`-modules. This file proves the two halves of that assertion that need no input
beyond what is already proved.

*The forward half* is `isIso_unit_of_isReflexive`: a coherent reflexive `F` is recovered from its
restriction, `F ≅ j_*j^*F`. Its stalks outside `U` have depth at least two by
[Stacks, Tag 0EBI] part (1), and Hartogs extension ([Stacks, Tag 0E9I]) then says the unit of the
restriction–direct-image adjunction is an isomorphism at `F`. `isoPushforwardRestrict` records the
resulting isomorphism with `j^*F` rewritten as the restriction `F|_U`, which is the spelling the
rest of the theory uses.

*The backward half* is `isCoherent_isReflexive_pushforward_of_extension`: if a coherent reflexive
`𝒪_U`-module `G` is the restriction of *some* coherent `𝒪_X`-module `E`, then `j_*G` is coherent
and reflexive. The argument is the source's: replace `E` by its reflexive hull `E^∨∨`, which is
reflexive by `isReflexive_doubleDual_of_isReflexive_restrict` and still restricts to `G` on `U`,
and then apply the forward half to it. Note that the hull is reflexive here *without* the source's
integrality hypothesis — see the discussion below.

## Main results

* `isIso_unit_of_isReflexive` — the forward half of [Stacks, Tag 0EBJ]: a coherent reflexive
  module is recovered from its restriction to `U`.
* `isoPushforwardRestrict` — the same, as an isomorphism `F ≅ j_*(F|_U)`.
* `isCoherent_isReflexive_pushforward_of_extension` — the backward half of [Stacks, Tag 0EBJ],
  granted a coherent extension of `G` to `X`.

## Implementation notes

**No `@[stacks 0EBJ]` attribute is placed here.** Tag 0EBJ is a single assertion — an equivalence
of two categories together with the identification of the two functors — and this file proves
neither of the two further ingredients that assertion needs: the existence of a coherent extension
of `G` to the whole of `X` ([Stacks, Tag 0G41] part (2), which no declaration on this branch
carries), and the affine-locality of the conclusion that reduces the general case to the
quasi-compact one 0G41 requires. A tag on a fraction of a covering set makes the whole tag render
as formalized.

**Integrality is not assumed, and the source assumes it.** [Stacks, Tag 0EBJ] is stated for an
*integral* locally Noetherian scheme, and its proof uses that hypothesis in one place: the step
"after replacing `F` by its reflexive hull, we may assume `F` is reflexive" is [Stacks, Tag 0AY4],
whose algebraic core [Stacks, Tag 0AV3] is stated for a Noetherian **domain**. That step is
avoided here. `isReflexive_doubleDual_of_isReflexive_restrict`, of
`Stacks.AlgebraicGeometry.ReflexiveEquivalence`, obtains reflexivity of the hull from the depth
hypothesis instead, via [Stacks, Tag 0AV5] (`one_le_depth_and_two_le_depth_linearMap`), which asks
only for a Noetherian local ring. The forward half likewise needs no integrality, because
[Stacks, Tag 0EBI] part (1) is proved without it. So both statements below are generalizations of
the source and not weakenings of it.

The coherence predicate is written `_root_.SheafOfModules.IsCoherent` throughout. That is not
cosmetic: this branch carries two distinct coherence constants with identical fields, and inside
the `Stacks.` namespace both the unqualified name and dot notation resolve to the other one, with
no error anywhere. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/PushforwardCoherent.lean`.

`isCoherent_of_iso` is taken from `Stacks.AlgebraicGeometry.CoherentDevissage`, which is the
universe-`u` restatement of it; the older copy in
`Stacks.AlgebraicGeometry.HigherDirectImageCoherent` is available only in universe `0` and so does
not apply to a general `Scheme.{u}`.

## References

* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
* [Stacks Project, Tag 0AY4](https://stacks.math.columbia.edu/tag/0AY4)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.ReflexiveEquivalence

universe u

namespace Stacks.FundamentalGroup.DepthCoherence

variable {X : Scheme.{u}}

/-! ### A coherent reflexive module is recovered from its restriction -/

/-- **The forward half of [Stacks, Tag 0EBJ].** A coherent reflexive module on a locally
Noetherian scheme is recovered from its restriction to an open `U` whose complement carries depth
at least two: the unit of the restriction–direct-image adjunction is an isomorphism at `F`.

The stalks of `F` outside `U` inherit depth two from `𝒪_X` by [Stacks, Tag 0EBI] part (1), and
Hartogs extension ([Stacks, Tag 0E9I]) concludes. -/
@[ega "IV 21.13.4" "partial", sga "6 II 2.2.7.2" "more general", sga "7 XI 1.1" "partial"]
public theorem isIso_unit_of_isReflexive [IsLocallyNoetherian X] (U : X.Opens) (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) :=
  AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two X F U
    fun x hx => depth_stalk_ge_two_of_isReflexive F hF x (hdepth x hx)

/-- **A coherent reflexive module is the direct image of its restriction.** This is
`isIso_unit_of_isReflexive` with the inverse image `j^*F` rewritten as the restriction `F|_U`
along `Scheme.Modules.restrictFunctorIsoPullback`. -/
public def isoPushforwardRestrict [IsLocallyNoetherian X] (U : X.Opens) (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    F ≅ (Scheme.Modules.pushforward U.ι).obj (F.restrict U.ι) :=
  have := isIso_unit_of_isReflexive U F hF hdepth
  asIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) ≪≫
    (Scheme.Modules.pushforward U.ι).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm

/-! ### The direct image of a coherent reflexive module that extends -/

/-- **The backward half of [Stacks, Tag 0EBJ], granted an extension.** Let `G` be a coherent
reflexive module on an open `U` of a locally Noetherian scheme `X` whose complement carries depth
at least two, and suppose `G` is the restriction of *some* coherent `𝒪_X`-module `E`. Then `j_*G`
is coherent and reflexive.

This is the source's argument. Reflexivity of `G` transports to `E|_U`, so the reflexive hull
`E^∨∨` is reflexive by
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_doubleDual_of_isReflexive_restrict` —
the step for which the source invokes [Stacks, Tag 0AY4] and hence integrality, and which is
available here unconditionally. The canonical map `E ⟶ E^∨∨` restricts to an isomorphism on `U`,
so `E^∨∨|_U ≅ G`, and the forward half identifies `E^∨∨` with `j_*G`. -/
public theorem isCoherent_isReflexive_pushforward_of_extension [IsLocallyNoetherian X]
    (U : X.Opens) (G : U.toScheme.Modules) (E : X.Modules)
    [_root_.SheafOfModules.IsCoherent E] (e : E.restrict U.ι ≅ G) (hG : IsReflexive G)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward U.ι).obj G) ∧
      IsReflexive ((Scheme.Modules.pushforward U.ι).obj G) := by
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have hEUc : _root_.SheafOfModules.IsCoherent (E.restrict U.ι) := isCoherent_restrict U E
  have hGc : _root_.SheafOfModules.IsCoherent G :=
    _root_.Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso e.symm
  have hEU : IsReflexive (E.restrict U.ι) := isReflexive_of_iso e.symm hG
  have hHc : _root_.SheafOfModules.IsCoherent (dualSheaf (dualSheaf E)) := isCoherent_doubleDual E
  have hHr : IsReflexive (dualSheaf (dualSheaf E)) :=
    isReflexive_doubleDual_of_isReflexive_restrict U E hEU hdepth
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (toDoubleDual E)) :=
    isIso_restrict_toDoubleDual U E hEU
  have eH : dualSheaf (dualSheaf E) ≅ (Scheme.Modules.pushforward U.ι).obj G :=
    isoPushforwardRestrict U (dualSheaf (dualSheaf E)) hHr hdepth ≪≫
      (Scheme.Modules.pushforward U.ι).mapIso
        ((asIso ((Scheme.Modules.restrictFunctor U.ι).map (toDoubleDual E))).symm ≪≫ e)
  have hPc : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward U.ι).obj G) :=
    _root_.Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso eH.symm
  exact ⟨hPc, isReflexive_of_iso eH hHr⟩

end Stacks.FundamentalGroup.DepthCoherence

end
