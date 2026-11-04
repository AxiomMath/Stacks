module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# Vanishing of the higher direct images along an affine morphism of algebraic spaces

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Stacks 073H asserts that `R^i f_* 𝓕 = 0` for `i > 0` and every quasi-coherent
`𝒪_X`-module `𝓕`.  The source's proof is two steps: an affine morphism of algebraic spaces is
representable, so Equation 69.3.0.1 (Stacks 071Z) identifies the restriction `(R^i f_*𝓕)|_V` to
an étale scheme chart `V` of `Y` with `R^i f'_*(𝓕|_U)` for the base change `f' : U ⟶ V`; and
`U = V ×_Y X` is then affine over the scheme `V`, so that higher direct image vanishes.

This file supplies the first step in full and reduces Stacks 073H to the second, which is
carried as the explicit named hypothesis `h03DW`.  The `@[stacks 073H]` attribute below is
therefore **qualified**: it claims the reduction, not the affine case, and Stacks 073H without
any qualifier is exactly the conclusion below with `h03DW` discharged.  The arrangement, and the
naming of the hypothesis, follow
`AlgebraicGeometry.Space.moduleHigherPushforwardEtaleBaseChangeIso_of_preservesInjectives`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardEtaleBaseChange.lean`), which
names its carried input `h03F3` in the same way — there the input has since been proved, and the
`@[stacks 03LX]` attribute sits on the unqualified form.

## Main definitions

* `AlgebraicGeometry.Space.ChartwiseIsZeroHigherDirectImage` is the hypothesis `h03DW`: the
  higher direct images of the chart base changes of `f` vanish in degree `n`.

## Main results

* `SheafOfModules.isZero_iff_forall_isZero_obj`: a sheaf of modules on a site is zero exactly
  when all of its modules of sections are zero.
* `AlgebraicGeometry.Space.isZero_iff_forall_isZero_etaleModulePullback_chartToSpace`: an
  `𝒪_Y`-module on the small étale site of an algebraic space is zero exactly when its
  restriction along every étale scheme chart is zero.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`: the first sentence of the
  source's proof — an affine morphism of algebraic spaces is representable.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_chartwise` and
  `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom`: **Stacks 073H
  with `h03DW` carried**, for a representable and for an affine morphism respectively.  The
  second carries the qualified `@[stacks 073H]` attribute.

## Implementation notes

*What `h03DW` is, and why it is not bounded side-work.*  After the reduction the goal is that
`R^n f'_*` vanishes for an affine morphism `f' : U ⟶ V` of *affine schemes*.  The source cites
Cohomology of Schemes, Lemma 30.2.3 (Stacks 01XC) here, and that lemma is proved in this
repository as `Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom`
(`StacksFrontier/AlgebraicGeometry/AffineCohomologyVanishing/Basic.lean`) — but entirely on
the **Zariski** site: its modules are `AlgebraicGeometry.Scheme.Modules` and its vanishing input
is Serre's criterion on an affine open (Stacks 01XB).  The direct images of Stacks 073H live on
the *small étale* sites, so the citation silently uses the comparison of étale with Zariski
cohomology for quasi-coherent modules, that is Stacks 03DW, equivalently Descent, Proposition
03DX(2) and Étale Cohomology, Theorem 03OJ.  None of those three tags is carried anywhere in
this repository, and two files say so about themselves:
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSections.lean` (lines 77–95, including a dated
correction about which of 03DW and 03DX(2) is the input) and
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleAffinePresentationSurjectivity.lean` (line 724,
"surjectivity half of the vanishing statement which Stacks 03DW rests on").  Discharging
`h03DW` therefore unlocks much more than this tag: the same keystone blocks Stacks 03M9 and the
family of statements that reduce quasi-coherence on a small étale site to sections over one
affine chart.  `StacksFrontier/AlgebraicGeometry/Spaces/ShortExactQuasicoherent.lean` is another
consumer and is where the name `h03DW` used below comes from; it carries the degree-one case of
the same input, in the form "the epimorphism of a short exact sequence is surjective on the
sections over every affine étale chart".  What the repository does hold is the first-cohomology
half — Čech vanishing on
cofinal coverings, `@[stacks 03F9]` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/VanishingOnCofinalCoverings.lean`, and
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/BigSiteColimits/H1Vanishing.lean` — whereas
03DW's own proof routes through 03F9, 03FJ, 03F7, 01XD and 013P.

*Why Stacks 071Z's caveat does not propagate here.*
`AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso` is an isomorphism with the
right endpoints which is not identified with the canonical base-change comparison map; its own
file records that.  That caveat would bite a statement about the comparison *map*, but the
conclusion here is `CategoryTheory.Limits.IsZero`, a property of an object, and `IsZero`
transports along `CategoryTheory.Limits.IsZero.of_iso` for an arbitrary isomorphism.  So nothing
canonical about the comparison is used, and no caveat is inherited.

*Quasi-coherence is not a hypothesis.*  The source states Stacks 073H for a quasi-coherent
`𝓕`, and quasi-coherence is what would discharge `h03DW`; the reduction itself uses none of it,
so the statements below quantify over an arbitrary `𝒪_X`-module.  The degree runs over `ℕ` in
the injective-resolution convention `CategoryTheory.Functor.rightDerived`, as in Stacks 071Z.

*The detection lemma.*  The restriction of modules along an étale morphism of algebraic spaces
is literally restriction of sections — `AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj`
is `rfl` — and the identity chart of the algebraic space represented by a chart `V`,
`AlgebraicGeometry.Space.idEtaleChart`, postcomposes to `V` itself, again by `rfl`.  So the
sections of a module over `V` are recovered from its restriction to `V`, which is what makes
`isZero_iff_forall_isZero_etaleModulePullback_chartToSpace` cheap.  The forward implication
instead uses additivity, `AlgebraicGeometry.Space.etaleModulePullback_additive`.

*The two local priority raises* are the ones
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardEtaleBaseChange.lean` documents:
with the module-universe-`max u v r w` instances for the cohomology of modules on a site
in the import closure, search for
`Abelian` and `EnoughInjectives` on the modules at module universe `u` commits to them and then
fails on the universe constraint.  Both attributes are `local`.

## References

* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u m

namespace SheafOfModules

/-- A sheaf of modules on a site is zero exactly when all of its modules of sections are zero.

Both directions go through `CategoryTheory.Limits.IsZero.iff_id_eq_zero`: the identity of a
sheaf of modules is zero exactly when the identity of its underlying presheaf of modules is,
and that happens exactly when every component is zero. -/
theorem isZero_iff_forall_isZero_obj {C : Type*} [Category* C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{m} R) :
    IsZero M ↔ ∀ U : C, IsZero (M.val.obj (Opposite.op U)) := by
  have hz : ∀ (P Q : SheafOfModules.{m} R), (0 : P ⟶ Q).val = 0 := fun _ _ => rfl
  simp only [IsZero.iff_id_eq_zero]
  constructor
  · intro h U
    have h2 : SheafOfModules.Hom.val (𝟙 M) = SheafOfModules.Hom.val (0 : M ⟶ M) := by rw [h]
    simpa [hz] using congrArg (fun φ => PresheafOfModules.Hom.app φ (Opposite.op U)) h2
  · intro h
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
    simpa [hz] using h U.unop

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Detecting the zero module on the small étale site -/

/-- The sections of the restriction of an `𝒪_Y`-module to an étale scheme chart `V`, over the
identity chart of the algebraic space represented by `V`, are its sections over `V`.

Restriction along an étale morphism is restriction of sections, and postcomposing the identity
chart with the structure morphism of `V` gives `V` back, so this holds by `rfl`. -/
theorem etaleModulePullback_chartToSpace_obj_val_obj_idEtaleChart (Y : AlgebraicSpaces B S hS)
    (M : Modules.{u, m} B S hS Y.obj Y.property) (V : SmallEtale B S hS Y.obj) :
    ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V)).obj M).val.obj
        (Opposite.op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.obj).obj V))) =
      M.val.obj (Opposite.op V) := rfl

/-- An `𝒪_Y`-module on the small étale site of an algebraic space is zero exactly when its
restriction along every étale scheme chart of `Y` is zero.

The forward implication is additivity of restriction; the converse reads the sections over a
chart off the sections of the restriction over the identity chart. -/
theorem isZero_iff_forall_isZero_etaleModulePullback_chartToSpace (Y : AlgebraicSpaces B S hS)
    (M : Modules.{u, m} B S hS Y.obj Y.property) :
    IsZero M ↔ ∀ V : SmallEtale B S hS Y.obj,
      IsZero ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).obj M) := by
  constructor
  · intro h V
    have := etaleModulePullback_additive.{u, m} B S hS (chartToSpace B S hS Y V)
      (isEtale_chartToSpace B S hS Y V)
    exact Functor.map_isZero _ h
  · intro h
    rw [SheafOfModules.isZero_iff_forall_isZero_obj]
    intro V
    exact (SheafOfModules.isZero_iff_forall_isZero_obj _ _).mp (h V)
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.obj).obj V))

/-! ### Affine morphisms of algebraic spaces are representable -/

/-- **The first sentence of the proof of Stacks 073H.** An affine morphism of algebraic spaces
over `S` is representable.

This is the representability conjunct of condition (1) of Stacks 03WG, reached from condition
(2) by `AlgebraicGeometry.Space.presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace`. -/
theorem relativelyRepresentable_of_isAffineHom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) : yoneda.relativelyRepresentable f.hom :=
  (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS X.property Y.property hf).1

/-! ### Stacks 073H, reduced to the affine case on the small étale site -/

/-- The hypothesis `h03DW` of the two theorems below: for every étale scheme chart `V` of `Y`
the base change `f' : V ×_Y X ⟶ V` of a representable `f` has vanishing degree-`n` higher
direct image on the restriction `𝓕|_{V ×_Y X}`.

For an affine `f` and a quasi-coherent `𝓕` this is the étale-site analogue of Stacks 01XC, that
is Stacks 03DW; see the implementation notes of this file. -/
def ChartwiseIsZeroHigherDirectImage {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (F : Modules.{u, u} B S hS X.obj X.property) (n : ℕ) : Prop :=
  ∀ V : SmallEtale B S hS Y.obj,
    have := hasInjectiveResolutions_modules B S hS
      (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).obj
      (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).property
    IsZero
      (((modulePushforward B S hS (smallBaseChangeChartMap B S hS f hf V)).rightDerived n).obj
        ((etaleModulePullback B S hS
          (chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V))
          (isEtale_chartToSpace B S hS X ((smallBaseChange B S hS f hf).obj V))).obj F))

/-- **Stacks 073H for a representable morphism, with the affine case carried as `h03DW`.**

If `f : X ⟶ Y` is a representable morphism of algebraic spaces over `S` whose chart base
changes have vanishing degree-`n` higher direct images, then `R^n f_* 𝓕 = 0`.

A module on the small étale site of `Y` is zero as soon as its restriction to every étale scheme
chart is zero, and over the chart `V` that restriction is `R^n f'_*(𝓕|_{V ×_Y X})` by
Equation 69.3.0.1, `AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso`.  Because
the conclusion is a vanishing statement about an object, only the existence of that isomorphism
is used, not its identification with the canonical base-change map. -/
theorem isZero_rightDerived_modulePushforward_of_chartwise {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (F : Modules.{u, u} B S hS X.obj X.property) (n : ℕ)
    (h03DW : ChartwiseIsZeroHigherDirectImage B S hS f hf F n) :
    have := hasInjectiveResolutions_modules B S hS X.obj X.property
    IsZero (((modulePushforward B S hS f).rightDerived n).obj F) := by
  have := hasInjectiveResolutions_modules B S hS X.obj X.property
  rw [isZero_iff_forall_isZero_etaleModulePullback_chartToSpace]
  intro V
  have := hasInjectiveResolutions_modules B S hS
    (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).obj
    (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).property
  exact (h03DW V).of_iso ((moduleHigherPushforwardChartBaseChangeIso B S hS f hf V n).app F).symm

/-- **Stacks 073H with the affine case carried as `h03DW`.**

If `f : X ⟶ Y` is an affine morphism of algebraic spaces over `S` whose chart base changes have
vanishing degree-`n` higher direct images, then `R^n f_* 𝓕 = 0`.

This is the previous theorem with representability supplied by
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`.  The source's statement is
this one for `n > 0` and quasi-coherent `𝓕` with `h03DW` discharged; neither restriction on `n`
nor on `𝓕` is used by the reduction, and `h03DW` is not available in this repository. -/
@[stacks 073H "the reduction of the source's statement along étale scheme charts, by Stacks 071Z;
the affine case of the source's proof — the étale-site analogue of Stacks 01XC, that is
Stacks 03DW — is carried as the hypothesis `h03DW` and is not proved"]
theorem isZero_rightDerived_modulePushforward_of_isAffineHom {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.obj X.property) (n : ℕ)
    (h03DW : ChartwiseIsZeroHigherDirectImage B S hS f
      (relativelyRepresentable_of_isAffineHom B S hS f hf) F n) :
    have := hasInjectiveResolutions_modules B S hS X.obj X.property
    IsZero (((modulePushforward B S hS f).rightDerived n).obj F) :=
  isZero_rightDerived_modulePushforward_of_chartwise B S hS f _ F n h03DW

end AlgebraicGeometry.Space

end
