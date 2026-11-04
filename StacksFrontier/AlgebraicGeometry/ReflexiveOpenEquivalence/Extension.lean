module

public import StacksFrontier.AlgebraicGeometry.ReflexiveFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Adjunction
public import StacksFrontier.AlgebraicGeometry.ReflexiveStalk.Restriction
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullCoherentReflexive

/-!
# Tag 0EBJ from the extension step alone

Let `X` be an integral locally Noetherian scheme and let `U` be an open subscheme whose
complement consists of points where the local ring has depth at least two.  The source's proof
of [Stacks, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ) deduces the equivalence from a
single geometric input: *every coherent module on `U` is the restriction of a coherent module on
`X`* (the affine case of [Stacks, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)).  Granted
that, one replaces the extension by its reflexive hull and the direct-image step
`hpushforward` — the last hypothesis of
`Stacks.AlgebraicGeometry.ReflexiveModules.reflexiveCoherentEquivalenceOfPushforward` — follows
from Tag 0EBI part (1) and Tag 0E9I, both proved.

This file carries out that deduction.  Everything in the source's argument except the extension
itself is discharged here.

## Main results

* `isIso_restrictFunctor_map_of_bijective_stalkHom`: a morphism of `𝒪_X`-modules whose stalk
  maps are bijective at every point of an open `U` restricts to an isomorphism over `U`.
* `isCoherent_and_isReflexive_pushforward_of_isReflexive_extension`: **the direct-image step**,
  for a module that extends to a coherent *reflexive* module on `X`.  This is `hpushforward`
  with the extension as its only input.
* `isCoherent_restrict_of_isCoherent`: the restriction of a coherent module to an open
  subscheme is coherent.
* `exists_isReflexive_extension_of_isCoherent_extension`: the source's "after replacing `F` by
  its reflexive hull we may assume `F` is reflexive", for a coherent extension of a coherent
  *reflexive* module on `U`.
* `reflexiveCoherentEquivalenceOfReflexiveExtension`: **the statement of Tag 0EBJ from the
  extension step alone**, for an extension assumed coherent and reflexive.
* `reflexiveCoherentEquivalenceOfCoherentExtension`: **the same, from an extension assumed only
  coherent** — which is the source's own geometric input, the affine case of Tag 0G41 part (1).

## Method

Write `j : U ⟶ X` for the inclusion.  Given a coherent reflexive `F` on `X` with `F|_U ≅ 𝒢`,
Tag 0EBI part (1) (`two_le_depth_stalk_of_isReflexive`) turns the depth hypothesis on the local
rings off `U` into the same bound for the stalks of `F`, and Tag 0E9I
(`isIso_unit_restrict_pushforward_of_depth_ge_two`) then says the unit `F ⟶ j_*j^*F` is an
isomorphism.  Since `j^*F ≅ 𝒢`, this exhibits `j_*𝒢` as isomorphic to `F`, so it is coherent and
reflexive.  Note that integrality of `X` is not used for this step.

Passing from a coherent extension to a reflexive one is the reflexive hull: `F⁎⁎` is coherent
and reflexive by the hull clause of Tag 0EBH, and the canonical map `F ⟶ F⁎⁎` restricts to an
isomorphism over `U` because its stalk at a point of `U` is bijective exactly when the stalk of
`F` there is a reflexive module — that is `bijective_stalkHom_toDoubleDual_iff`, Tag 0AY3 — and
`isIso_restrictFunctor_map_of_bijective_stalkHom` turns pointwise bijectivity over `U` into
invertibility of the restricted morphism.  The latter is the naturality of Mathlib's
`Scheme.Modules.restrictStalkNatIso`, which identifies the stalk of a restriction at a point of
`U` with the stalk of the module at the image point.

## Implementation notes

**No `@[stacks 0EBJ]` attribute is attached**: one hypothesis remains, namely the extension
step, and the tag asserts the equivalence unconditionally.  The remaining input is recorded in
the hypothesis `hextend` of `reflexiveCoherentEquivalenceOfReflexiveExtension`, and it is Tag
0G41 part (1) on the affine opens of `X` together with the hull step above.

Reflexivity of the stalks of the extension over `U` is *derived* from reflexivity of `𝒢`, not
assumed.  The derivation needs a comparison of the stalk of `F` at a point of `U`, as a module
over the local ring of `X` there, with the stalk of `F|_U` over the local ring of `U`, and a
transfer of `Module.IsReflexive` along the resulting equivalence of local rings.  Those are
`module_isReflexive_modStalk_of_restrict` and `Module.IsReflexive.of_ringEquiv`; the germ
computation behind the first had existed in the tree only as three mutually unreachable
`private` copies of `AlgebraicGeometry.restrictStalkMap_smul`, and the second is absent
from Mathlib, which transports reflexivity only along a linear equivalence over a fixed ring.

## References

* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 0EBI](https://stacks.math.columbia.edu/tag/0EBI)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open Stacks.SheafOfModules.SheafHomStalk

/-- A morphism of `𝒪_X`-modules whose maps of stalks are bijective at every point of an open
`U` restricts to an isomorphism over `U`.

The stalk of the restriction of a module at a point of `U` is the stalk of the module at the
image point, naturally in the module; that is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, and its naturality square transports
the bijectivity. -/
public theorem isIso_restrictFunctor_map_of_bijective_stalkHom {X : Scheme.{u}} (U : X.Opens)
    {F G : X.Modules} (f : F ⟶ G)
    (h : ∀ x : X, x ∈ U → Function.Bijective (stalkHom f x)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  refine isIso_of_bijective_stalkHom _ fun w => ?_
  have hb := h (U.ι.base w) w.2
  have h1 : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} (U.ι.base w)).map
      ((Scheme.Modules.toPresheaf X).map f)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab => hb.1 ?_, fun m => ?_⟩
    · exact ((stalkFunctor_map_apply f (U.ι.base w) a).symm.trans hab).trans
        (stalkFunctor_map_apply f (U.ι.base w) b)
    · obtain ⟨a, ha⟩ := hb.2 m
      exact ⟨a, (stalkFunctor_map_apply f (U.ι.base w) a).trans ha⟩
  have hr : (TopCat.Presheaf.stalkFunctor Ab.{u} w).map
        ((Scheme.Modules.toPresheaf U.toScheme).map
          ((Scheme.Modules.restrictFunctor U.ι).map f)) ≫
          (Scheme.Modules.restrictStalkNatIso U.ι w).hom.app G =
      (Scheme.Modules.restrictStalkNatIso U.ι w).hom.app F ≫
        (TopCat.Presheaf.stalkFunctor Ab.{u} (U.ι.base w)).map
          ((Scheme.Modules.toPresheaf X).map f) :=
    (Scheme.Modules.restrictStalkNatIso U.ι w).hom.naturality f
  have hcomp : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} w).map
        ((Scheme.Modules.toPresheaf U.toScheme).map
          ((Scheme.Modules.restrictFunctor U.ι).map f)) ≫
          (Scheme.Modules.restrictStalkNatIso U.ι w).hom.app G) := by
    rw [hr]
    infer_instance
  have h2 : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} w).map
      ((Scheme.Modules.toPresheaf U.toScheme).map
        ((Scheme.Modules.restrictFunctor U.ι).map f))) :=
    IsIso.of_isIso_comp_right _ ((Scheme.Modules.restrictStalkNatIso U.ι w).hom.app G)
  rw [ConcreteCategory.isIso_iff_bijective] at h2
  refine ⟨fun a b hab => h2.1 ?_, fun m => ?_⟩
  · exact ((stalkFunctor_map_apply _ w a).trans hab).trans
      (stalkFunctor_map_apply _ w b).symm
  · obtain ⟨a, ha⟩ := h2.2 m
    exact ⟨a, (stalkFunctor_map_apply _ w a).symm.trans ha⟩

/-- **The direct-image step of Stacks, Tag 0EBJ, from a coherent reflexive extension.**  If a
module `𝒢` on an open subscheme `U` whose complement has structure-sheaf depth at least two is
the restriction of a coherent reflexive module `F` on `X`, then the direct image of `𝒢` is
coherent and reflexive — indeed it is isomorphic to `F`.

This is the hypothesis `hpushforward` of `reflexiveCoherentEquivalenceOfPushforward`, for such a
`𝒢`.  Integrality of `X` is not used. -/
public theorem isCoherent_and_isReflexive_pushforward_of_isReflexive_extension (X : Scheme.{u})
    [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (G : U.toScheme.Modules) (F : X.Modules) (hFcoh : F.IsCoherent) (hFrefl : IsReflexive F)
    (e : F.restrict U.ι ≅ G) :
    ((Scheme.Modules.pushforward U.ι).obj G).IsCoherent ∧
      IsReflexive ((Scheme.Modules.pushforward U.ι).obj G) := by
  have hF := hFcoh
  have hdualcoh : (dualSheaf F).IsCoherent :=
    Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_dualSheaf F
  have hdualfp : (dualSheaf F).IsFinitePresentation :=
    isFinitePresentation_of_isCoherent (dualSheaf F)
  -- Tag 0EBI part (1): the stalks of `F` inherit the depth bound off `U`.
  have hdF : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    fun x hx => two_le_depth_stalk_of_isReflexive X F hFrefl x (hdepth x hx)
  -- Tag 0E9I: `F` is the direct image of its own restriction.
  have hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) :=
    isIso_unit_restrict_pushforward_of_depth_ge_two X F U hdF
  let eG : (Scheme.Modules.pullback U.ι).obj F ≅ G :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm ≪≫ e
  let iso : F ≅ (Scheme.Modules.pushforward U.ι).obj G :=
    asIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) ≪≫
      (Scheme.Modules.pushforward U.ι).mapIso eG
  exact ⟨Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (R := X.ringCatSheaf) iso.symm,
    isReflexive_of_iso iso hFrefl⟩

/-- The restriction of a coherent module to an open subscheme of a locally Noetherian scheme is
coherent: restriction is the pullback along the inclusion, and Tag 0EBF's coherence clause needs
only local Noetherianity of the source. -/
public theorem isCoherent_restrict_of_isCoherent (X : Scheme.{u}) [IsLocallyNoetherian X]
    (U : X.Opens) (F : X.Modules) (hFcoh : F.IsCoherent) : (F.restrict U.ι).IsCoherent :=
  let : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  let := hFcoh
  let := AlgebraicGeometry.isCoherent_pullback U.ι F
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    (R := U.toScheme.ringCatSheaf) ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F)

/-- **The source's reduction to a reflexive extension.**  A coherent extension of a coherent
*reflexive* module `𝒢` on `U` may be replaced by its reflexive hull, which is a coherent
reflexive extension of `𝒢`.

The hull is coherent and reflexive by the hull clause of Tag 0EBH, and the canonical map
`F ⟶ F⁎⁎` restricts to an isomorphism over `U` by Tag 0AY3 at the points of `U`.  The stalks of
`F` over `U` are reflexive modules because they are the stalks of `𝒢`: that is Tag 0AY3 for `𝒢`
on `U` followed by `module_isReflexive_modStalk_of_restrict`, the semilinear comparison of the
stalk of a restriction with the stalk of the module at the image point. -/
public theorem exists_isReflexive_extension_of_isCoherent_extension (X : Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (G : U.toScheme.Modules) (hGrefl : IsReflexive G) (F : X.Modules) (hFcoh : F.IsCoherent)
    (e : F.restrict U.ι ≅ G) :
    ∃ F' : X.Modules, F'.IsCoherent ∧ IsReflexive F' ∧ Nonempty (F'.restrict U.ι ≅ G) := by
  have hF := hFcoh
  have : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have hdualcoh : (dualSheaf F).IsCoherent :=
    Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_dualSheaf F
  have hdualfp : (dualSheaf F).IsFinitePresentation :=
    isFinitePresentation_of_isCoherent (dualSheaf F)
  let _ : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  let _ : (F.restrict U.ι).IsCoherent := isCoherent_restrict_of_isCoherent X U F hFcoh
  let _ : G.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (R := U.toScheme.ringCatSheaf) e.symm
  -- Tag 0AY3 on `U`: the stalks of the reflexive module `𝒢` are reflexive modules.
  have hGstalk : ∀ w : U.toScheme,
      Module.IsReflexive (ringStalk U.toScheme.sheaf w) (modStalk G w) :=
    ((isReflexive_tfae U.toScheme G).out 1 2).mp hGrefl
  -- Crossing the open immersion: they are the stalks of `F` at the points of `U`.
  have hstalk : ∀ x : X, x ∈ U →
      Module.IsReflexive (ringStalk X.sheaf x) (modStalk F x) := fun x hx =>
    module_isReflexive_modStalk_of_restrict U.ι F ⟨x, hx⟩
      (module_isReflexive_modStalk_of_iso e.symm ⟨x, hx⟩ (hGstalk ⟨x, hx⟩))
  have hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (toDoubleDual F)) :=
    isIso_restrictFunctor_map_of_bijective_stalkHom U (toDoubleDual F)
      fun x hx => (bijective_stalkHom_toDoubleDual_iff F x).mpr (hstalk x hx)
  exact ⟨reflexiveHull F,
    Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_doubleDual F,
    isReflexive_reflexiveHull X F,
    ⟨(asIso ((Scheme.Modules.restrictFunctor U.ι).map (toDoubleDual F))).symm ≪≫ e⟩⟩

/-- **The statement of Stacks, Tag 0EBJ, from the extension step alone.**  On an integral
locally Noetherian scheme, restriction to an open subscheme whose complement has structure-sheaf
depth at least two is an equivalence on coherent reflexive modules, with direct image as its
inverse, provided every coherent reflexive module on the open subscheme is the restriction of a
coherent reflexive module on the whole scheme.

This is `reflexiveCoherentEquivalenceOfPushforward` with its `hpushforward` hypothesis
discharged by `isCoherent_and_isReflexive_pushforward_of_isReflexive_extension`.  The extension
step is the one input that remains, and it is the affine case of Tag 0G41 together with
`exists_isReflexive_extension_of_isCoherent_extension`. -/
-- stacks attribute for 0EBJ withheld: the extension step is still assumed here.
public noncomputable def reflexiveCoherentEquivalenceOfReflexiveExtension (X : Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hextend : ∀ G : U.toScheme.Modules, G.IsCoherent → IsReflexive G →
      ∃ F : X.Modules, F.IsCoherent ∧ IsReflexive F ∧ Nonempty (F.restrict U.ι ≅ G)) :
    Σ e : ReflexiveCoherentModules X ≌ ReflexiveCoherentModules U.toScheme,
      (e.functor ⋙ ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pullback U.ι) ×
      (e.inverse ⋙ ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pushforward U.ι) :=
  reflexiveCoherentEquivalenceOfPushforward X U hdepth
    fun G hGcoh hGrefl =>
      let F := hextend G hGcoh hGrefl
      isCoherent_and_isReflexive_pushforward_of_isReflexive_extension X U hdepth G
        F.choose F.choose_spec.1 F.choose_spec.2.1 F.choose_spec.2.2.some

/-- **The statement of Stacks, Tag 0EBJ, from the source's own geometric input.**  Same as
`reflexiveCoherentEquivalenceOfReflexiveExtension`, but the extension assumed of a coherent
reflexive module on `U` need only be *coherent*, not reflexive: that is exactly the extension
statement the source quotes, the affine case of
[Stacks, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41) part (1).

Reflexivity of the extension is then recovered by
`exists_isReflexive_extension_of_isCoherent_extension`, the source's "after replacing `F` by its
reflexive hull we may assume `F` is reflexive". -/
-- stacks attribute for 0EBJ withheld: the extension step is still assumed here.
public noncomputable def reflexiveCoherentEquivalenceOfCoherentExtension (X : Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hextend : ∀ G : U.toScheme.Modules, G.IsCoherent → IsReflexive G →
      ∃ F : X.Modules, F.IsCoherent ∧ Nonempty (F.restrict U.ι ≅ G)) :
    Σ e : ReflexiveCoherentModules X ≌ ReflexiveCoherentModules U.toScheme,
      (e.functor ⋙ ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pullback U.ι) ×
      (e.inverse ⋙ ObjectProperty.ι
          (fun F : X.Modules => F.IsCoherent ∧ IsReflexive F) ≅
        ObjectProperty.ι
          (fun F : U.toScheme.Modules =>
            F.IsCoherent ∧ IsReflexive F) ⋙
          Scheme.Modules.pushforward U.ι) :=
  reflexiveCoherentEquivalenceOfReflexiveExtension X U hdepth
    fun G hGcoh hGrefl =>
      let F := hextend G hGcoh hGrefl
      exists_isReflexive_extension_of_isCoherent_extension X U G hGrefl F.choose
        F.choose_spec.1 F.choose_spec.2.some

end Stacks.AlgebraicGeometry.ReflexiveModules

end
