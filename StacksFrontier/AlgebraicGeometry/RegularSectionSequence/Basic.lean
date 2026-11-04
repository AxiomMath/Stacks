module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact

/-!
# Stacks Tag 0C6K: the exact sequence of a regular section, reduced to two named inputs

Stacks Tag 0C6K is Remark 31.15.11 of the Stacks Project, and its label `regular_section_sequence`
is the first of the two sequences it records: for `L` an invertible `𝒪_X`-module, `s` a *regular*
global section of `L` and `i : Z(s) ⟶ X` the inclusion of its zero scheme,

`0 ⟶ 𝒪_X ⟶ L ⟶ i_* (L|_{Z(s)}) ⟶ 0`

is short exact, and — this is the first of the label's **two** assertions, and it needs no
regularity — the restriction map `L ⟶ i_* (L|_{Z(s)})` *is* the cokernel of `s`.

This file proves both assertions for an **arbitrary** closed subscheme in place of the zero
scheme, on two hypotheses which are named once and are exactly what the zero scheme is still owed;
and it proves, in full generality, the categorical lemma that is the engine of both.

## Main definitions

* `Stacks.RegularSectionSequence.restrictionAdjunction` and
  `Stacks.RegularSectionSequence.restrictionUnit`: the pullback–pushforward adjunction along the
  inclusion of a closed subscheme, and its unit `L ⟶ i_* i^* L`, which is the label's second
  arrow.
* `Stacks.RegularSectionSequence.zeroScheme`: Stacks Tag 02OQ's zero scheme, in library
  vocabulary.

## Main results

* `Stacks.RegularSectionSequence.exists_cokernelIso_of_isIso_unit_app`: **the engine, and it is
  pure category theory.** For an adjunction `P ⊣ R` between categories with zero morphisms and a
  morphism `f` whose composite with the unit vanishes, if the unit is an isomorphism at
  `cokernel f` then `cokernel f ≅ R (P N)` compatibly with the cokernel projection. The
  hypothesis that `P` preserve the relevant colimit is not taken: `P` is a left adjoint, so it is
  derived.
* `Stacks.RegularSectionSequence.shortExact_of_mono_of_exists_cokernelIso`: in an abelian category,
  a monomorphism followed by any arrow identified with its cokernel projection is a short exact
  sequence. This is the step from the label's first assertion to its second.
* `Stacks.RegularSectionSequence.exists_cokernelIso_restrictionUnit` and
  `Stacks.RegularSectionSequence.shortExact_restrictionUnit`: **both assertions of the label
  `regular_section_sequence`**, for an arbitrary closed subscheme `D` of `X` and an arbitrary
  `f : 𝒪_X ⟶ L`, on the two hypotheses below.
* `Stacks.RegularSectionSequence.shortExact_restrictionUnit_zeroScheme`: the same at the zero
  scheme of a section, which is the label's own shape.

## No Stacks attribute is attached, and what is missing

The two theorems above carry two hypotheses that the Stacks statement does not, so they do not
prove Tag 0C6K and the attribute is not attached. The hypotheses are:

* `hz`, that `f ≫ (L ⟶ i_* i^* L) = 0` — the section restricts to zero on the subscheme. At the
  zero scheme this says the image of `s` lies in the ideal sheaf of `Z(s)`, which is the
  non-trivial direction of Stacks Tag 02OQ's characterisation of that ideal. The zero scheme is
  `Scheme.IdealSheafData.ofIdeals` of an affine-local family, and `ofIdeals` returns the
  *largest* quasi-coherent ideal sheaf contained in that family, so membership in the family is
  not by itself membership in the ideal sheaf. That the family is already quasi-coherent **is**
  available: it is `AlgebraicGeometry.zeroScheme_ideal` of `../Divisors/ZeroSchemeData.lean`,
  carrying Tag 02OQ's clause `the defining ideal`, proved for an invertible `L` from the
  localization of the dual. What `hz` still needs beyond it is that the ideal so described
  annihilates the restriction of `s`, which is a separate step.
* `hiso`, that the unit is an isomorphism at `cokernel f` — equivalently, that `cokernel f` is in
  the essential image of `i_*`. This is **Stacks Tag 08KS**, Sheaves of Modules Lemma 17.13.4:
  for a closed immersion of ringed spaces, `i_*` is exact and fully faithful with essential image
  the modules killed by the ideal sheaf.

**And the mathematics of the second one is proved — the gap is a bridge, not a theorem.** Tag
08KS's ringed-space statement is recorded as not covered at
`StacksFrontier/AlgebraicGeometry/ClosedImmersion/DerivedPushforwardComparison.lean` ("exactness
only; full faithfulness and the essential image are not covered"), and the descent machinery at
`StacksFrontier/Topology/Sheaves/Functors/Module/ExactSupportSections.lean` says in its own module
documentation that what it proves is "*not* the essential-surjectivity half of Tag 08KS". But the
**ringed-topos** form of the identical lemma, Stacks Tag 08M3, is proved and tagged here in all
three of its parts:

* `AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardFullyFaithful/Basic.lean`);
* `AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardEssentialImageDirect/Criterion.lean`)
  — "an `𝒪'`-module is in the essential image exactly when the kernel ideal annihilates it",
  which is `hiso`'s content;
* exactness
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardEssentialImageDirect/Exactness.lean`).

So what is missing between `hiso` and a theorem is a **comparison**: a
`CategoryTheory.ClosedRingedImmersion` built from a scheme-theoretic closed immersion — its
`MorphismOfTopoi.IsClosedImmersion` field, the local surjectivity field being available as
`Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isLocallySurjective_c_of_isClosedImmersion`
(`../ClosedImmersionTFAE/Basic.lean:119`) — together with an identification of
`AlgebraicGeometry.RingedToposHom.pushforwardModules` with
`AlgebraicGeometry.Scheme.Modules.pushforward`. That is a bridging result in its own right and not
part of Tag 0C6K.

## Implementation notes

**Everything is stated over `SheafOfModules.{u} X.ringCatSheaf` rather than over
`AlgebraicGeometry.Scheme.Modules`, and that is forced.** `Scheme.Modules` is a `def`, and
`SheafOfModules.unit X.ringCatSheaf` inhabits the unwrapped category, so a hom from the unit to an
object named through `Scheme.Modules.pushforward` elaborates with no `Zero` on its hom type and
`f ≫ g = 0` fails to parse at all, with the error reported as a
missing `OfNat` instance rather than as a category mismatch. Stating the arrows over
`SheafOfModules.pushforward` and `SheafOfModules.pullback` at
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`, which is what `Scheme.Modules.pushforward` and
`Scheme.Modules.pullback` are *defined* to be, fixes it outright. Callers holding
`X.Modules` objects still apply, and
`Stacks.RegularSectionSequence.shortExact_restrictionUnit_zeroScheme` is one: it passes an
`X.Modules` to `restrictionUnit` with no transport.

For the same reason the three instances below are supplied by hand. `IsRightAdjoint` of the
pushforward is required even to *write* `SheafOfModules.pullback`, and `Additive` of both functors
is what gives `PreservesZeroMorphisms`; Mathlib proves all three, but about the `Scheme.Modules`
wrappers, so instance search does not see them through the `def`.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.RegularSectionSequence

/-! ### The categorical engine -/

/-- **The cokernel of a morphism killed by the unit of an adjunction.** Let `P ⊣ R` be an
adjunction between categories with zero morphisms, both functors preserving zero morphisms, and
let `f : M ⟶ N` be a morphism with `f ≫ η_N = 0`. If the unit is an isomorphism at `cokernel f`
then `cokernel f ≅ R (P N)`, compatibly with the cokernel projection and the unit.

Preservation of the cokernel colimit by `P` is not a hypothesis: `P` is a left adjoint, so it
preserves every colimit, and the instance is produced inside the proof. The proof that `P f = 0`
is the adjunction's own naturality, not an additivity argument. -/
theorem exists_cokernelIso_of_isIso_unit_app {A : Type*} [Category A] {B : Type*} [Category B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] {P : A ⥤ B} {R : B ⥤ A} (adj : P ⊣ R)
    [P.PreservesZeroMorphisms] [R.PreservesZeroMorphisms]
    {M N : A} (f : M ⟶ N) [HasCokernel f]
    [IsIso (adj.unit.app (cokernel f))] (hf : f ≫ adj.unit.app N = 0) :
    ∃ e : cokernel f ≅ R.obj (P.obj N), cokernel.π f ≫ e.hom = adj.unit.app N := by
  have hPf : P.map f = 0 := by
    apply (adj.homEquiv M (P.obj N)).injective
    change adj.unit.app M ≫ R.map (P.map f) = adj.unit.app M ≫ R.map 0
    change adj.unit.app M ≫ (P ⋙ R).map f = _
    rw [← adj.unit.naturality f]
    simpa using hf
  have : PreservesColimit (parallelPair f 0) P :=
    (adj.leftAdjoint_preservesColimits).preservesColimitsOfShape.preservesColimit
  have hcol := isColimitOfHasCokernelOfPreservesColimit P f
  have : IsIso (P.map (cokernel.π f)) := CokernelCofork.IsColimit.isIso_π _ hcol hPf
  refine ⟨asIso (adj.unit.app (cokernel f)) ≪≫ (R.mapIso (asIso (P.map (cokernel.π f)))).symm, ?_⟩
  change cokernel.π f ≫ adj.unit.app (cokernel f) ≫ _ = _
  have hn := adj.unit.naturality (cokernel.π f)
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, Iso.symm_hom, Functor.mapIso_inv, asIso_inv, ← Functor.map_comp,
    IsIso.hom_inv_id]
  rw [R.map_id]
  exact Category.comp_id _

/-- **A monomorphism and an arrow identified with its cokernel projection form a short exact
sequence.** The composite vanishes because the cokernel projection kills `f`, and short exactness
transports along the isomorphism of short complexes. -/
theorem shortExact_of_mono_of_exists_cokernelIso {C : Type*} [Category C] [Abelian C]
    {O L M : C} (f : O ⟶ L) [Mono f] (g : L ⟶ M)
    (h : ∃ e : cokernel f ≅ M, cokernel.π f ≫ e.hom = g) :
    ∃ hz : f ≫ g = 0, (ShortComplex.mk f g hz).ShortExact := by
  obtain ⟨e, he⟩ := h
  have hz : f ≫ g = 0 := by rw [← he, ← Category.assoc, cokernel.condition, zero_comp]
  refine ⟨hz, ?_⟩
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
      (S₂ := ShortComplex.mk f g hz) (Iso.refl _) (Iso.refl _) e (by simp) (by simpa using he.symm))
    (ShortComplex.shortExact_mk_cokernel_π f)

/-! ### Restriction to a closed subscheme -/

section Geom

/-- Pushforward of modules along a morphism of schemes is a right adjoint. Mathlib proves this
about `AlgebraicGeometry.Scheme.Modules.pushforward`, which is a `def` wrapping the functor named
here, so instance search does not find it through the wrapper. -/
instance isRightAdjoint_sheafOfModulesPushforward {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs (Scheme.Modules.pushforward g).IsRightAdjoint

/-- Pullback of modules along a morphism of schemes is additive; see
`Stacks.RegularSectionSequence.isRightAdjoint_sheafOfModulesPushforward` for why this is restated.
-/
instance additive_sheafOfModulesPullback {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    (SheafOfModules.pullback.{u} g.toRingCatSheafHom).Additive :=
  inferInstanceAs (Scheme.Modules.pullback g).Additive

/-- Pushforward of modules along a morphism of schemes is additive; see
`Stacks.RegularSectionSequence.isRightAdjoint_sheafOfModulesPushforward` for why this is restated.
-/
instance additive_sheafOfModulesPushforward {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).Additive :=
  inferInstanceAs (Scheme.Modules.pushforward g).Additive

variable {X : Scheme.{u}} (D : X.IdealSheafData)
  (L : SheafOfModules.{u} X.ringCatSheaf)

/-- The pullback–pushforward adjunction along the inclusion of a closed subscheme. -/
abbrev restrictionAdjunction :
    SheafOfModules.pullback.{u} D.subschemeι.toRingCatSheafHom ⊣
      SheafOfModules.pushforward.{u} D.subschemeι.toRingCatSheafHom :=
  SheafOfModules.pullbackPushforwardAdjunction D.subschemeι.toRingCatSheafHom

/-- Restriction of an `𝒪_X`-module to a closed subscheme, pushed forward to `X`: the unit
`L ⟶ i_* i^* L` of the adjunction, which is the second arrow of Stacks Tag 0C6K's sequence. -/
abbrev restrictionUnit :
    L ⟶ (SheafOfModules.pushforward.{u} D.subschemeι.toRingCatSheafHom).obj
      ((SheafOfModules.pullback.{u} D.subschemeι.toRingCatSheafHom).obj L) :=
  (restrictionAdjunction D).unit.app L

/-- **The first assertion of Stacks Tag 0C6K's label `regular_section_sequence`**, for an
arbitrary closed subscheme `D` in place of the zero scheme: the restriction map
`L ⟶ i_* (L|_D)` is the cokernel of `f : 𝒪_X ⟶ L`, compatibly with the cokernel projection. No
regularity of `f` is used, as in the source.

The two hypotheses are what the zero scheme of a section is still owed; see the module
documentation, which names the missing declaration for each and why no attribute is attached. -/
theorem exists_cokernelIso_restrictionUnit
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (hz : f ≫ restrictionUnit D L = 0)
    (hiso : IsIso ((restrictionAdjunction D).unit.app (cokernel f))) :
    ∃ e : cokernel f ≅ (SheafOfModules.pushforward.{u} D.subschemeι.toRingCatSheafHom).obj
        ((SheafOfModules.pullback.{u} D.subschemeι.toRingCatSheafHom).obj L),
      cokernel.π f ≫ e.hom = restrictionUnit D L :=
  exists_cokernelIso_of_isIso_unit_app (restrictionAdjunction D) f hz

/-- **The second assertion of Stacks Tag 0C6K's label `regular_section_sequence`**, for an
arbitrary closed subscheme `D` in place of the zero scheme: for `f : 𝒪_X ⟶ L` a monomorphism —
which for `f` the multiplication map of a global section is exactly regularity of that section,
Stacks Tag 01WY in the form `AlgebraicGeometry.IsRegularSection`
(`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/RegularSections.lean`) — the sequence
`0 ⟶ 𝒪_X ⟶ L ⟶ i_* (L|_D) ⟶ 0` is short exact. -/
theorem shortExact_restrictionUnit
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ L) [Mono f]
    (hz : f ≫ restrictionUnit D L = 0)
    (hiso : IsIso ((restrictionAdjunction D).unit.app (cokernel f))) :
    ∃ h : f ≫ restrictionUnit D L = 0,
      (ShortComplex.mk f (restrictionUnit D L) h).ShortExact :=
  shortExact_of_mono_of_exists_cokernelIso f _
    (exists_cokernelIso_restrictionUnit D L f hz hiso)

end Geom

/-! ### The zero scheme of a section -/

section ZeroScheme

/-- **Stacks Tag 02OQ's zero scheme** of a global section of an invertible module, in library
vocabulary: the largest quasi-coherent ideal sheaf whose ideal on each affine open is contained in
the ideal generated by the values of the restricted section under the local linear functionals.

The invertibility of `M` is not needed to write the definition and is therefore not taken; it is
needed for the characterisation of the resulting ideal, which is Tag 02OQ's own second assertion
and is `AlgebraicGeometry.zeroScheme_ideal` of
`../Divisors/ZeroSchemeData.lean`: `ofIdeals` loses nothing, because the defining family is
already a quasi-coherent ideal sheaf. This definition is that one with the invertibility
instance dropped, so that it can be written for an arbitrary `M`. -/
def zeroScheme (X : Scheme.{u}) (M : X.Modules) (t : Γ(M, ⊤)) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U =>
    Ideal.span {a : Γ(X, U.1) | ∃ φ : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1),
      a = φ (M.presheaf.map (homOfLE le_top).op t)}

/-- **The label `regular_section_sequence` of Stacks Tag 0C6K, in its own shape**, on the two
inputs the zero scheme is owed: for `s` a regular global section of `M` — regularity being
monicity of the multiplication map, which is Stacks Tag 01WY — the sequence
`0 ⟶ 𝒪_X ⟶ M ⟶ i_* (M|_{Z(s)}) ⟶ 0` is short exact.

That an `X.Modules` is accepted by `Stacks.RegularSectionSequence.restrictionUnit`, which is
stated over `SheafOfModules.{u} X.ringCatSheaf`, is checked here by elaboration: the application
below carries no transport. -/
theorem shortExact_restrictionUnit_zeroScheme (X : Scheme.{u}) (M : X.Modules)
    (s : M.sections) (hs : Mono (M.unitHomEquiv.symm s))
    (hz : M.unitHomEquiv.symm s ≫
        restrictionUnit (zeroScheme X M (s.eval (Opposite.op ⊤))) M = 0)
    (hiso : IsIso ((restrictionAdjunction
        (zeroScheme X M (s.eval (Opposite.op ⊤)))).unit.app
      (cokernel (M.unitHomEquiv.symm s)))) :
    ∃ h : M.unitHomEquiv.symm s ≫
        restrictionUnit (zeroScheme X M (s.eval (Opposite.op ⊤))) M = 0,
      (ShortComplex.mk (M.unitHomEquiv.symm s)
        (restrictionUnit (zeroScheme X M (s.eval (Opposite.op ⊤))) M) h).ShortExact :=
  shortExact_restrictionUnit _ M _ hz hiso

end ZeroScheme

end Stacks.RegularSectionSequence

end
