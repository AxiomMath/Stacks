module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageIsoComp

/-!
# The composition law for the units of Stacks 03LU

Stacks 03LU attaches to a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` contained
in a big fppf site `B` the adjunction `f^* ⊣ f_*` of `𝒪`-modules and the two composition
comparisons `AlgebraicGeometry.Space.modulePushforwardCompIso` and
`AlgebraicGeometry.Space.modulePullbackCompIso`.  This file proves the compatibility of the
units with those comparisons at a single module: for `g : Z ⟶ X` and `i : X ⟶ Y`, the unit at
`i`, followed by the direct image along `i` of the unit at `g`, followed by the two
comparisons, is the unit at `g ≫ i`.

**What it is for.**  It is the arrow half of the sequence of Stacks 03M8.  In the notation of
that lemma — `τ : U ⟶ X` the surjective étale chart, `t, s : R ⟶ U` the two projections of
`R = U ×_X U`, `ρ = t ≫ τ = s ≫ τ`, `a = τ ≫ f` and `b = ρ ≫ f` — the sequence

`0 → f_*F → a_*(F|_U) → b_*(F|_R)`

has as its first arrow the direct image along `f` of the unit at `τ`, and as its second the
difference of the two arrows built from the units at `t` and at `s`; that the composite of the
first with either of the two is one and the same morphism, so that the difference kills the
image of `f_*F`, is this law read at `t` and at `s` in turn.  The reading of `F|_U` involved is
the inverse image `τ^*F` of Stacks 03LU, which for an étale morphism is étale restriction by
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, Stacks' Equation 03LW.

`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationArrows.lean` states the same
three arrows with `AlgebraicGeometry.Space.etaleModulePullback` in place of
`AlgebraicGeometry.Space.modulePullback` and records that it cannot prove the corresponding
composition law: the route there is to transport the set-level law along the underlying sheaf of
sets, and that needs the unit of `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` to be
the set-level unit, which is the comparison
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitComparison.lean` leaves open.  In
the spelling of this file no transport occurs and no sheaf of sets appears.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackChartUnitArrow` is the first arrow `f_*F ⟶ a_*(F|_U)`
  of the source's sequence, for `a = τ ≫ f`.
* `AlgebraicGeometry.Space.modulePullbackRestrictionArrow` is the arrow
  `τ_*(F|_U) ⟶ (h ≫ τ)_*(F|_R)` attached to `h : R ⟶ U`; in Stacks 03M8 it is `t^*` for `h = t`
  and `s^*` for `h = s`.
* `AlgebraicGeometry.Space.modulePullbackChartParallelArrow` is the second arrow
  `a_*(F|_U) ⟶ b_*(F|_R)`, one for each `h`.

## Main results

* `AlgebraicGeometry.Space.moduleCompAdjunction_unit_app`: the unit of
  `AlgebraicGeometry.Space.moduleCompAdjunction` — the composite of the two adjunctions with its
  right adjoint read through the comparison of direct images — split into its three factors.
* `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_app`: **the composition law for
  the units of Stacks 03LU at a single module.**
* `AlgebraicGeometry.Space.modulePullbackPresentationComplex`: the first arrow of the source's
  sequence followed by the second is the first arrow attached to `h ≫ τ`, so the composite does
  not depend on the factorization of `b` through `a` that built the second arrow.
* `AlgebraicGeometry.Space.modulePullbackPresentationComplex_eq`: **the sequence of Stacks 03M8
  is a complex, in `Mod(𝒪_Y)`** — for `t, s : R ⟶ U` with `s ≫ τ = t ≫ τ` the two parallel
  arrows agree after the first arrow, so the source's difference `t^* - s^*` vanishes on the
  image of `f_*F`.
* `AlgebraicGeometry.Space.modulePullbackPresentationUnitArrow_congr`: the first arrow is
  compatible with an equality of the morphisms it is attached to, which is what lets the arrows
  of `t` and of `s` be compared at all.

## What is still owed for Stacks 03M8

**Exactness**, and no declaration in this file carries `@[stacks 03M8]`.  A complex is not an
exact sequence, and nothing here asserts that the first arrow is a kernel of the second.
Exactness is where surjectivity of `τ` and the square `R = U ×_X U` enter; the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/PushforwardPresentationExact.lean` record which
identifications of the sections of the three terms are still missing.

What exactness does **not** need, on this route: the comparison of the two units that
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitComparison.lean` leaves open, and
that `AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_unit` carries as the
hypothesis `hu`.  That comparison is what the `AlgebraicGeometry.Space.etaleModulePullback`
spelling of `StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationArrows.lean`
needs in order to transport the set-level statement, because there the three terms are read
through their underlying sheaves of sets.  In the spelling of this file the inverse image is the
one of Stacks 03LU throughout, no transport along Stacks' Equation 03LW occurs, and the unit is
never compared with anything: the composition law
`AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_app` is proved from the mate
property of the comparison of inverse images, and the sections of the unit are already available
as `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_val_app`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSpellingBridge.lean`), which is what a
descent argument on sections consumes.

The complex clause above is stated with the arrows **written out** rather than through
`AlgebraicGeometry.Space.modulePullbackChartUnitArrow`,
`AlgebraicGeometry.Space.modulePullbackRestrictionArrow` and
`AlgebraicGeometry.Space.modulePullbackChartParallelArrow`.  The composites it displays are the
bodies of those three definitions, but the step identifying a body with the name standing for it
is not available at these types: see this file's implementation notes.

## Implementation notes

Neither unit is computed and nothing below unfolds
`AlgebraicGeometry.Space.modulePullbackAdjunction`.  The law is the defining property of
`AlgebraicGeometry.Space.modulePullbackCompIso` as the mate of the comparison of direct images,
which the library already carries in whiskered form as
`AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom`, together with the
split of the composite unit.

That split is `CategoryTheory.Adjunction.comp_ofNatIsoRight_unit_app`, but it is not applied to
`AlgebraicGeometry.Space.moduleCompAdjunction` directly: asking the elaborator to match that
definition against the `CategoryTheory.Adjunction.ofNatIsoRight` of a
`CategoryTheory.Adjunction.comp` reaches the heartbeat limit in `whnf`, with or without the
arguments of the general lemma supplied explicitly.  The equality of the two **adjunctions** is
affordable — it is `rfl`, one delta step, with no component ever elaborated — so the split is
obtained by transporting along that equality with `congrArg`, which is the same economy as the
one recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitComparison.lean`: at these types an
equality of isomorphisms, or of adjunctions, is cheap where the corresponding equality of
components is not.

**Why the complex clause is stated with the arrows written out, and where the budget goes.**
The binding constraint at these types is the **kernel**, not the elaborator, and it is reached
by naming a composite rather than by any particular tactic.  Concretely:

* the *statements* are cheap.  The complex clause, with the arrows named or written out, is
  elaborated and kernel-checked in a fifth of a second when its proof is left open;
* a single application of a general lemma is cheap.  `CategoryTheory.Category.assoc`,
  `congrArg` against the cancellation `CategoryTheory.Iso.hom_inv_id_app` of the composition
  comparison, and the identification of `(τ_* ⋙ f_*).obj N` with `f_*(τ_*N)` each cost a fifth
  of a second;
* the equation `modulePullbackRestrictionArrow τ h F = <its body>`, which is one delta step,
  is **not** available: by `Eq.refl` it reaches the elaborator's limit at `whnf`, and by `rw`
  or by `simp only` with the definition — where the elaborator succeeds, since it applies the
  equation lemma rather than unfolding — the *kernel* then exceeds its budget on that equation
  lemma's own proof.  So the named form of the law
  `unit_τ ≫ modulePullbackRestrictionArrow τ h F = unit_{h ≫ τ}` is unreachable, and with it
  every statement that mentions the arrow and needs its factors;
* a proof that mentions a *written-out* composite where a general lemma expects a variable is
  likewise rejected by the kernel: the four-step chain `assoc`, `assoc.symm`, `congrArg` against
  `hom_inv_id_app`, `id_comp` is checked in a fifth of a second when the restriction arrow is a
  variable `ρ`, and exceeds the kernel's budget when the same chain is written at the arrow
  itself — with `rw`, with `simp only`, and in term form alike.

Hence the shape above: `AlgebraicGeometry.Space.modulePullbackPresentationComplex_of_unit_comp`
keeps `ρ` a variable and takes its defining property as a hypothesis, and
`AlgebraicGeometry.Space.modulePullbackPresentationComplex` instantiates it — the arrow entering
only as an *argument*, which the kernel checks against the declared type structurally.  The same
instantiation at `AlgebraicGeometry.Space.modulePullbackRestrictionArrow` itself is also
affordable, so a future named form of the clause needs only the delta step above
and nothing else.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X Y : AlgebraicSpaces B S hS}

/-- **The unit of the composite adjunction of Stacks 03LU, split into its three factors**: the
unit at `i`, the direct image along `i` of the unit at `g`, and the composition comparison of
the direct images. -/
theorem moduleCompAdjunction_unit_app (g : Z ⟶ X) (i : X ⟶ Y)
    (F : Modules.{u, u} B S hS Y.1 Y.2) :
    (moduleCompAdjunction B S hS g i).unit.app F =
      (modulePullbackAdjunction B S hS i).unit.app F ≫
        (modulePushforward B S hS i).map
          ((modulePullbackAdjunction B S hS g).unit.app
            ((modulePullback B S hS i).obj F)) ≫
        (modulePushforwardCompIso B S hS g i).hom.app
          ((modulePullback B S hS g).obj ((modulePullback B S hS i).obj F)) :=
  (congrArg
      (fun A : modulePullback B S hS i ⋙ modulePullback B S hS g ⊣
          modulePushforward B S hS (g ≫ i) ↦ A.unit.app F)
      (moduleCompAdjunction_eq B S hS g i)).trans
    (Adjunction.comp_ofNatIsoRight_unit_app (modulePullbackAdjunction B S hS i)
      (modulePullbackAdjunction B S hS g) (modulePushforwardCompIso B S hS g i) F)

/-- **The composition law for the units of the Stacks 03LU adjunction, at a single module.**
For morphisms `g : Z ⟶ X` and `i : X ⟶ Y` of algebraic spaces and an `𝒪_Y`-module `F`, the unit
at `i`, followed by the direct image along `i` of the unit at `g`, followed by the composition
comparison `AlgebraicGeometry.Space.modulePushforwardCompIso` of the direct images and the
direct image of the composition comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of the inverse images, is the unit at `g ≫ i`.

This is the arrow half of the sequence of Stacks 03M8; see this file's header.  It is
`AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom`, the defining
property of the comparison of inverse images as the mate of the comparison of direct images,
with the composite unit split by
`AlgebraicGeometry.Space.moduleCompAdjunction_unit_app`. -/
theorem modulePullbackAdjunction_unit_comp_app (g : Z ⟶ X) (i : X ⟶ Y)
    (F : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackAdjunction B S hS i).unit.app F ≫
        (modulePushforward B S hS i).map
          ((modulePullbackAdjunction B S hS g).unit.app
            ((modulePullback B S hS i).obj F)) ≫
        (modulePushforwardCompIso B S hS g i).hom.app
          ((modulePullback B S hS g).obj ((modulePullback B S hS i).obj F)) ≫
        (modulePushforward B S hS (g ≫ i)).map
          ((modulePullbackCompIso B S hS g i).hom.app F) =
      (modulePullbackAdjunction B S hS (g ≫ i)).unit.app F := by
  have hmate := CategoryTheory.NatTrans.congr_app
    (unit_comp_whiskerRight_modulePullbackCompIso_hom B S hS g i) F
  rw [NatTrans.comp_app, Functor.whiskerRight_app,
    moduleCompAdjunction_unit_app B S hS g i F] at hmate
  rw [← hmate]
  simp only [Category.assoc]

/-! ### The arrows of the sequence of Stacks 03M8 -/

section Sequence

variable {U R : AlgebraicSpaces B S hS}

/-- **The first arrow `f_*F ⟶ a_*(F|_U)` of the sequence of Stacks 03M8**, for `a = τ ≫ f`: the
direct image along `f` of the unit of `AlgebraicGeometry.Space.modulePullbackAdjunction` at
`τ`, followed by the composition comparison of the direct images of Stacks 03LU. -/
noncomputable def modulePullbackChartUnitArrow (f : X ⟶ Y) (τ : U ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS f).obj F ⟶
      (modulePushforward B S hS (τ ≫ f)).obj ((modulePullback B S hS τ).obj F) :=
  (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS τ).unit.app F) ≫
    (modulePushforwardCompIso B S hS τ f).hom.app ((modulePullback B S hS τ).obj F)

/-- **The arrow `τ_*(F|_U) ⟶ ρ_*(F|_R)` attached to `h : R ⟶ U`**, with `ρ` written out as
`h ≫ τ`: the direct image along `τ` of the unit of
`AlgebraicGeometry.Space.modulePullbackAdjunction` at `h`, followed by the composition
comparison of the direct images and the direct image of the composition comparison of the
inverse images.

In Stacks 03M8, with `R = U ×_X U` and `t, s : R ⟶ U` its two projections, this is `t^*` for
`h = t` and `s^*` for `h = s`. -/
noncomputable def modulePullbackRestrictionArrow (τ : U ⟶ X) (h : R ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS τ).obj ((modulePullback B S hS τ).obj F) ⟶
      (modulePushforward B S hS (h ≫ τ)).obj ((modulePullback B S hS (h ≫ τ)).obj F) :=
  (modulePushforward B S hS τ).map
        ((modulePullbackAdjunction B S hS h).unit.app
          ((modulePullback B S hS τ).obj F)) ≫
      (modulePushforwardCompIso B S hS h τ).hom.app
        ((modulePullback B S hS h).obj ((modulePullback B S hS τ).obj F)) ≫
      (modulePushforward B S hS (h ≫ τ)).map
        ((modulePullbackCompIso B S hS h τ).hom.app F)

/-- **The second arrow `a_*(F|_U) ⟶ b_*(F|_R)` of the sequence of Stacks 03M8**, one for each
`h : R ⟶ U`, with `a = τ ≫ f` and `b = (h ≫ τ) ≫ f`: the direct image along `f` of
`AlgebraicGeometry.Space.modulePullbackRestrictionArrow`, conjugated by the composition
comparisons of the direct images along `τ ≫ f` and along `(h ≫ τ) ≫ f`.

For `h = t` it is the source's `t^*` and for `h = s` the source's `s^*`. -/
noncomputable def modulePullbackChartParallelArrow (f : X ⟶ Y) (τ : U ⟶ X) (h : R ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS (τ ≫ f)).obj ((modulePullback B S hS τ).obj F) ⟶
      (modulePushforward B S hS ((h ≫ τ) ≫ f)).obj
        ((modulePullback B S hS (h ≫ τ)).obj F) :=
  (modulePushforwardCompIso B S hS τ f).inv.app ((modulePullback B S hS τ).obj F) ≫
    (modulePushforward B S hS f).map (modulePullbackRestrictionArrow B S hS τ h F) ≫
      (modulePushforwardCompIso B S hS (h ≫ τ) f).hom.app
        ((modulePullback B S hS (h ≫ τ)).obj F)

/-! ### The sequence is a complex -/

/-- **The first arrow of the sequence of Stacks 03M8 followed by the second is the first arrow
attached to `ρ`**, for any second arrow built from a morphism `ρ : τ_*(F|_U) ⟶ ρ'_*(F|_R)` whose
composite with the unit at `τ` is the unit at `ρ'`.

The two composites in the middle are the composition comparison of Stacks 03LU and its inverse,
so they cancel, and what is left is the direct image along `f` of the hypothesis.

The hypothesis is the composition law
`AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_app` read through the arrow: it is
*not* an extra assumption, and
`AlgebraicGeometry.Space.modulePullbackPresentationComplex` below discharges it for the arrow
the source prescribes.  It is a hypothesis here, and `ρ` a variable rather than
`AlgebraicGeometry.Space.modulePullbackRestrictionArrow`, for the reason recorded in this file's
implementation notes: with `ρ` a variable the proof is checked in a fraction of a second, and
with the arrow's three factors written into it the kernel exceeds its budget. -/
theorem modulePullbackPresentationComplex_of_unit_comp (f : X ⟶ Y) (τ : U ⟶ X) (ρ' : R ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (ρ : (modulePushforward B S hS τ).obj ((modulePullback B S hS τ).obj F) ⟶
      (modulePushforward B S hS ρ').obj ((modulePullback B S hS ρ').obj F))
    (hρ : (modulePullbackAdjunction B S hS τ).unit.app F ≫ ρ =
      (modulePullbackAdjunction B S hS ρ').unit.app F) :
    ((modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS τ).unit.app F) ≫
          (modulePushforwardCompIso B S hS τ f).hom.app ((modulePullback B S hS τ).obj F)) ≫
        (modulePushforwardCompIso B S hS τ f).inv.app ((modulePullback B S hS τ).obj F) ≫
          (modulePushforward B S hS f).map ρ ≫
            (modulePushforwardCompIso B S hS ρ' f).hom.app
              ((modulePullback B S hS ρ').obj F) =
      (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS ρ').unit.app F) ≫
        (modulePushforwardCompIso B S hS ρ' f).hom.app ((modulePullback B S hS ρ').obj F) :=
  ((Category.assoc _ _ _).trans
    (congrArg
      (fun m ↦ (modulePushforward B S hS f).map
          ((modulePullbackAdjunction B S hS τ).unit.app F) ≫ m)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg
            (fun m ↦ m ≫ (modulePushforward B S hS f).map ρ ≫
              (modulePushforwardCompIso B S hS ρ' f).hom.app
                ((modulePullback B S hS ρ').obj F))
            ((modulePushforwardCompIso B S hS τ f).hom_inv_id_app
              ((modulePullback B S hS τ).obj F))).trans
          (Category.id_comp _))))).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg
        (fun m ↦ m ≫ (modulePushforwardCompIso B S hS ρ' f).hom.app
          ((modulePullback B S hS ρ').obj F))
        (((modulePushforward B S hS f).map_comp _ _).symm.trans
          (congrArg (modulePushforward B S hS f).map hρ))))

/-- **The first arrow of the sequence of Stacks 03M8 followed by the second is the first arrow
attached to `h ≫ τ`.**  Both arrows are written out: the left-hand side is
`AlgebraicGeometry.Space.modulePullbackChartUnitArrow` of `τ` followed by
`AlgebraicGeometry.Space.modulePullbackChartParallelArrow` of `h`, with the three factors of
`AlgebraicGeometry.Space.modulePullbackRestrictionArrow` written into the latter, and the
right-hand side is `AlgebraicGeometry.Space.modulePullbackChartUnitArrow` of `h ≫ τ`.

So the composite `f_*F → a_*(F|_U) → b_*(F|_R)` does not depend on which factorization of `b`
through `a` built the second arrow, which is what makes the source's difference `t^* - s^*`
vanish on the image of `f_*F`; see
`AlgebraicGeometry.Space.modulePullbackPresentationComplex_eq`.

This is `AlgebraicGeometry.Space.modulePullbackPresentationComplex_of_unit_comp` with its
hypothesis discharged by `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_app`. -/
theorem modulePullbackPresentationComplex (f : X ⟶ Y) (τ : U ⟶ X) (h : R ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS τ).unit.app F) ≫
          (modulePushforwardCompIso B S hS τ f).hom.app ((modulePullback B S hS τ).obj F)) ≫
        (modulePushforwardCompIso B S hS τ f).inv.app ((modulePullback B S hS τ).obj F) ≫
          (modulePushforward B S hS f).map
              ((modulePushforward B S hS τ).map
                  ((modulePullbackAdjunction B S hS h).unit.app
                    ((modulePullback B S hS τ).obj F)) ≫
                (modulePushforwardCompIso B S hS h τ).hom.app
                    ((modulePullback B S hS h).obj ((modulePullback B S hS τ).obj F)) ≫
                  (modulePushforward B S hS (h ≫ τ)).map
                    ((modulePullbackCompIso B S hS h τ).hom.app F)) ≫
            (modulePushforwardCompIso B S hS (h ≫ τ) f).hom.app
              ((modulePullback B S hS (h ≫ τ)).obj F) =
      (modulePushforward B S hS f).map
          ((modulePullbackAdjunction B S hS (h ≫ τ)).unit.app F) ≫
        (modulePushforwardCompIso B S hS (h ≫ τ) f).hom.app
          ((modulePullback B S hS (h ≫ τ)).obj F) :=
  modulePullbackPresentationComplex_of_unit_comp B S hS f τ (h ≫ τ) F
    ((modulePushforward B S hS τ).map
        ((modulePullbackAdjunction B S hS h).unit.app ((modulePullback B S hS τ).obj F)) ≫
      (modulePushforwardCompIso B S hS h τ).hom.app
          ((modulePullback B S hS h).obj ((modulePullback B S hS τ).obj F)) ≫
        (modulePushforward B S hS (h ≫ τ)).map
          ((modulePullbackCompIso B S hS h τ).hom.app F))
    (modulePullbackAdjunction_unit_comp_app B S hS h τ F)

/-- **The first arrow of the sequence of Stacks 03M8 is compatible with an equality of the
morphisms it is attached to.**  For `k = l : R ⟶ X` the first arrow of `k`, followed by the
transport of its target along that equality, is the first arrow of `l`.

This is what lets the two parallel arrows attached to the two projections `t, s` of
`R = U ×_X U` be compared: their targets are *named* `(t ≫ τ) ≫ f` and `(s ≫ τ) ≫ f`, and the
source's `b` is only *equal* to both. -/
theorem modulePullbackPresentationUnitArrow_congr (f : X ⟶ Y) {k l : R ⟶ X} (e : k = l)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS k).unit.app F) ≫
          (modulePushforwardCompIso B S hS k f).hom.app ((modulePullback B S hS k).obj F)) ≫
        eqToHom (congrArg (fun m : R ⟶ X ↦ (modulePushforward B S hS (m ≫ f)).obj
          ((modulePullback B S hS m).obj F)) e) =
      (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS l).unit.app F) ≫
        (modulePushforwardCompIso B S hS l f).hom.app ((modulePullback B S hS l).obj F) := by
  cases e
  simp

/-- **The sequence of Stacks 03M8 is a complex, in `Mod(𝒪_Y)`.**  Let `f : X ⟶ Y` be a morphism
of algebraic spaces, let `τ : U ⟶ X` be a chart and let `t, s : R ⟶ U` satisfy `s ≫ τ = t ≫ τ`
— in Stacks 03M8, `R = U ×_X U` with its two projections.  Put `a = τ ≫ f` and `b = (t ≫ τ) ≫ f`.
Then the two parallel arrows `a_*(F|_U) ⟶ b_*(F|_R)` attached to `t` and to `s` agree after the
first arrow `f_*F ⟶ a_*(F|_U)`, the one attached to `s` being transported to the target of the
one attached to `t` along `s ≫ τ = t ≫ τ`:

`f_*F → a_*(F|_U) ⇉ b_*(F|_R)`

is a fork.  Equivalently the source's difference `t^* - s^*` vanishes on the image of `f_*F`,
which is the "complex" half of the source's exactness assertion — the half that needs neither
surjectivity of `τ` nor the cartesian square `R = U ×_X U`.

Both composites are the first arrow attached to `t ≫ τ`, by
`AlgebraicGeometry.Space.modulePullbackPresentationComplex` and
`AlgebraicGeometry.Space.modulePullbackPresentationUnitArrow_congr`. -/
theorem modulePullbackPresentationComplex_eq (f : X ⟶ Y) (τ : U ⟶ X) (t s : R ⟶ U)
    (hts : s ≫ τ = t ≫ τ) (F : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS τ).unit.app F) ≫
          (modulePushforwardCompIso B S hS τ f).hom.app ((modulePullback B S hS τ).obj F)) ≫
        (modulePushforwardCompIso B S hS τ f).inv.app ((modulePullback B S hS τ).obj F) ≫
          (modulePushforward B S hS f).map
              ((modulePushforward B S hS τ).map
                  ((modulePullbackAdjunction B S hS t).unit.app
                    ((modulePullback B S hS τ).obj F)) ≫
                (modulePushforwardCompIso B S hS t τ).hom.app
                    ((modulePullback B S hS t).obj ((modulePullback B S hS τ).obj F)) ≫
                  (modulePushforward B S hS (t ≫ τ)).map
                    ((modulePullbackCompIso B S hS t τ).hom.app F)) ≫
            (modulePushforwardCompIso B S hS (t ≫ τ) f).hom.app
              ((modulePullback B S hS (t ≫ τ)).obj F) =
      (((modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS τ).unit.app F) ≫
            (modulePushforwardCompIso B S hS τ f).hom.app ((modulePullback B S hS τ).obj F)) ≫
          (modulePushforwardCompIso B S hS τ f).inv.app ((modulePullback B S hS τ).obj F) ≫
            (modulePushforward B S hS f).map
                ((modulePushforward B S hS τ).map
                    ((modulePullbackAdjunction B S hS s).unit.app
                      ((modulePullback B S hS τ).obj F)) ≫
                  (modulePushforwardCompIso B S hS s τ).hom.app
                      ((modulePullback B S hS s).obj ((modulePullback B S hS τ).obj F)) ≫
                    (modulePushforward B S hS (s ≫ τ)).map
                      ((modulePullbackCompIso B S hS s τ).hom.app F)) ≫
              (modulePushforwardCompIso B S hS (s ≫ τ) f).hom.app
                ((modulePullback B S hS (s ≫ τ)).obj F)) ≫
        eqToHom (congrArg (fun m : R ⟶ X ↦ (modulePushforward B S hS (m ≫ f)).obj
          ((modulePullback B S hS m).obj F)) hts) :=
  (modulePullbackPresentationComplex B S hS f τ t F).trans
    ((congrArg
        (fun m ↦ m ≫ eqToHom (congrArg (fun m : R ⟶ X ↦
          (modulePushforward B S hS (m ≫ f)).obj ((modulePullback B S hS m).obj F)) hts))
        (modulePullbackPresentationComplex B S hS f τ s F)).trans
      (modulePullbackPresentationUnitArrow_congr B S hS f hts F)).symm

end Sequence

end AlgebraicGeometry.Space

end
