module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleRepresentedNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleSchemeAgreementImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSquarePieceMapCompositionLaw

/-!
# Part (2) of Stacks 04G2 at immersion generality: the statement, and its working form

Let
```
R --j--→ V
|        |
b        a
↓        ↓
R' -j'-→ V'
```
be a commutative square of the big fppf category over a scheme `S` contained in a big fppf site
`B` whose two horizontal morphisms are **immersions** of schemes — the generality at which the
source states the clause.  Part (2) of [Stacks Project, Tag 04G2] says that when every space of
[Stacks Project, Tag 04CP] is a scheme, the canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of that tag is
the map of Morphisms, Lemma [Stacks Project, Tag 01R4]; Tag 04CP's own hypothesis on the two
horizontal arrows is that they are immersions, not that they are closed immersions.

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleRepresentedNaturality.lean` proves the
corresponding naturality for a square of **closed** immersions.  This file states part (2) at
immersion generality and reduces it to a statement of exactly the shape that closed naturality
has, so that the two can be compared factor for factor.

## Main definitions

* `AlgebraicGeometry.Space.representedConormalOfImmersionKernelIdealZPowIso`: the comparison of
  part (1) at **immersion** generality
  (`AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`), respelled so that its
  source is the associated module of the ringed-space conormal sheaf of the underlying morphism
  of schemes and its target the inverse image of
  `AlgebraicGeometry.Space.kernelIdealSheafZPow` in degree one.

## Main results

* `AlgebraicGeometry.Space.conormalMapOfImmersions_conormalModuleOfImmersionRepresentedIso`:
  **part (2) of [Stacks Project, Tag 04G2] at immersion generality follows from the naturality
  of that respelling.**  The hypothesis `hnat` is an equation of exactly the shape of the closed
  case's conclusion, with
  `AlgebraicGeometry.Space.representedConormalOfImmersionKernelIdealZPowIso` in place of
  `AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso`; the conclusion is that the
  part-(1) comparison at immersion generality carries the canonical map of
  [Stacks Project, Tag 04CP] to the associated module of
  `Stacks.Immersion.immersionConormalSheafMap`, the map of [Stacks Project, Tag 01R4].

## Why the passage between the two forms is pure conjugation

Both canonical maps are the "self" map of the square conjugated by a canonical
change-of-ambient isomorphism, and the two conjugations are structurally parallel:

* spaces-side, `AlgebraicGeometry.Space.conormalMapOfImmersions` is
  `AlgebraicGeometry.Space.kernelIdealZPowSquareMap` in degree one conjugated by
  `AlgebraicGeometry.Space.conormalModuleOfImmersionZPowIso`
  (`AlgebraicGeometry.Space.conormalMapOfImmersions_eq_kernelIdealZPowSquareMap`);
* schemes-side, `Stacks.Immersion.immersionConormalSheafMap` is
  `Stacks.ClosedImmersion.conormalSheafMap` of the very same square conjugated by
  `Stacks.Immersion.conormalSheafSelfIso`.

So the only thing that has to be moved across is the schemes-side conjugator at `j'`, which the
transport of the inverse image carries by its **naturality in the module**,
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_naturality`.  No composition law
and no value of any comparison is used, and nothing about closedness enters: both
`AlgebraicGeometry.Space.kernelIdealZPowSquareMap` and
`Stacks.ClosedImmersion.conormalSheafMap` are defined for arbitrary morphisms, and the whole
passage is one instantiation of `Stacks.CategoryTheory.conjugated_square_eq_of`, a lemma whose
morphisms all live in one category and each of whose six hypotheses is an existing lemma applied
verbatim.

`AlgebraicGeometry.Space.representedConormalOfImmersionKernelIdealZPowIso` is spelled through
`Stacks.Immersion.conormalSheafSelfIso` rather than through its inverse
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf`, because that is the spelling
`Stacks.Immersion.immersionConormalSheafMap` is defined at; taking the other one costs a
conversion at every one of the six hypotheses.

## What this file does not prove, named precisely

It does **not** prove `hnat`.  What `hnat` needs beyond the closed case is the source's own
reduction to a pair of ambient open subspaces on which both horizontal morphisms become closed
immersions, and then the closed naturality at that square together with the two composition laws
— `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp` spaces-side and
`Stacks.Immersion.immersionConormalSheafMap_comp` schemes-side — transporting it back.

Three facts about that reduction determine its shape.

* **The pair is not `U' = (j').coborderRange`, `U = j.coborderRange ⊓ a⁻¹ᵁ (j').coborderRange`.**
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalImmersionSquareAmbient.lean` builds the pair in
  two steps instead — first the open `a⁻¹ᵁ (j').coborderRange`, then the canonical coborder
  ambient of the resulting factorisation — so that the closedness of the lift is the instance
  `AlgebraicGeometry.Space.isClosedImmersion_toScheme_map_immersionCoborderLift` and no
  restriction argument through `AlgebraicGeometry.isClosedImmersion_resLE_of_le_coborderRange`
  is needed.
* **The closed naturality at that square does not by itself finish the reduction.**  Part (1) at
  immersion generality is defined at **one** ambient — the coborder ambient
  `AlgebraicGeometry.Space.immersionCoborderObj` of `j`, through the cartesian square of
  `AlgebraicGeometry.Space.isPullback_representedSpaceMap_immersionCoborderLift` — while
  `AlgebraicGeometry.Space.squareAmbientObj` is a different, smaller open of `V` with no morphism
  to it.  So the difference between `hnat` and the closed conclusion is **not** the one-symbol
  respelling of `AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso` described below: a
  change of ambient stands between them.  What supplies the missing morphism is
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalCoborderSquareAmbient.lean`, which applies the
  construction of the file above **one level up**, to the square with `j` replaced by its coborder
  lift, so that its ambient is an open of an open of
  `AlgebraicGeometry.Space.immersionCoborderObj` and
  `AlgebraicGeometry.Space.coborderSquareHom` is a morphism into the ambient part (1) is defined
  at.  Both squares it produces have two closed immersions along their horizontal rows, so the
  unconditional closed naturality applies to each, and both instantiations elaborate.
* **The agreement of the two part-(1) comparisons across the change of ambient is proved.**  It is
  `AlgebraicGeometry.Space.conormalChangeOfAmbientAgreement` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalChangeOfAmbientAgreement.lean`, with nothing
  assumed: `AlgebraicGeometry.Space.representedConormalOfImmersionKernelIdealZPowIso` at `j` and
  `AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso` at the closed coborder lift of
  `j` are carried to one another by `AlgebraicGeometry.Space.kernelIdealZPowSquareMap` of the
  change-of-ambient square, up to the unit law of [Stacks Project, Tag 03LU] and the associated
  module of `Stacks.Immersion.conormalSheafSelfIso`.

## The reduction of `hnat`

The shape of the reduction is fixed and every square it needs is stated.  Writing
`L`, `L'` for the coborder lifts of `j` and `j'`, `C`, `C'` for their ambients, `J` for
`AlgebraicGeometry.Space.coborderSquareLift`, `W` for its ambient,
`w = AlgebraicGeometry.Space.coborderSquareHom`,
`A = AlgebraicGeometry.Space.coborderSquareMap`, the four squares are

* `S₁ = (J, L, 𝟙, w)` and `S₂ = (J, L', b, A)`, both with two closed immersions along their rows,
  so the unconditional closed naturality
  `AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso_of_comp_eq`
  applies to each;
* `S₃` and `S₄`, the change-of-ambient squares at `j` and at `j'`, so
  `AlgebraicGeometry.Space.conormalChangeOfAmbientAgreement` applies to each.

Writing `D` for the outer rectangle of `S₁` over `S₃` and `D'` for that of `S₂` over `S₄`, the
two coincide, and `D` is also the outer rectangle of `D`'s upper square over the square `hnat` is
about.  So `hnat` is the **lower** square of a stack whose outer rectangle and upper square are
both known.  Both directions of that stacking are `Stacks.CategoryTheory.square_transport_comp`
and `Stacks.CategoryTheory.square_transport_of_comp` of
`StacksFrontier/CategoryTheory/SquareTransportComposition.lean`, at plain variables, with the three
composition laws as hypotheses.

All three are proved — `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp` spaces-side,
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp` for the transport, and
`Stacks.ClosedImmersion.conormalSheafMap_comp` schemes-side — and the unit law the stack's upper
left edge needs is proved unconditionally as
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_id`.  So is the cancellation.
What remains is the assembly, and nothing else.  The two less evident ingredients are these.

* `Stacks.ClosedImmersion.conormalSheafMap_comp`, the vertical composition law for the
  ringed-space conormal square map, is
  `StacksFrontier/AlgebraicGeometry/Thickenings/ConormalSheafSquareComposition.lean`.  Its
  ideal-sheaf half is `Stacks.ClosedImmersion.idealSheafMap_comp`; the other ingredient is the
  pasting law for three stacked
  `RingedSpaceModuleAdjunction.modulePullbackSquareIso`, which is
  `RingedSpaceModuleAdjunction.modulePullbackSquareIso_paste`, after which the law is one
  instantiation of `Stacks.CategoryTheory.square_map_comp`.  The ringed-space mirror of the
  spaces-side six-lemma toolkit is in that file.
  **The difficulty is not the pasting mathematics.**  Composition of morphisms of ringed spaces
  is definitionally associative, so `(a ≫ b) ≫ c` and `a ≫ b ≫ c` are convertible but not
  syntactically equal, and neither are `modulePullback ((a ≫ b) ≫ c)` and
  `modulePullback (a ≫ b ≫ c)`.  A composite of natural transformations crossing the two
  spellings elaborates and kernel-checks, and is then not type-correct at the `implicit`
  transparency level at which `rw` checks its motive and `simp` its congruences — so every
  subsequent tactic fails reporting that mismatch rather than anything about the step it was
  asked to take.  Naming the junction as an explicit
  `CategoryTheory.eqToHom (congrArg RingedSpaceModuleAdjunction.modulePullback (Category.assoc …))`
  — which is an identity, `RingedSpaceModuleAdjunction.modulePullback_eqToHom_assoc` — removes it,
  and the whole file then checks in 0.3 s.
  `Stacks.Immersion.immersionConormalSheafMap_comp` is not a substitute: it is stated at
  `Stacks.Conormal.conormalSheaf`, the conormal sheaf of the *coborder lift*, so using it would
  move the whole statement to a spelling in which neither base case is available.
* the cancellability of the upper square's canonical map, which
  `Stacks.CategoryTheory.square_transport_of_comp` takes as its hypothesis `hki`, is
  `AlgebraicGeometry.Space.isIso_kernelIdealZPowSquareMap_coborderSquare_comp` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalCoborderSquareAmbientIso.lean`.
  It does not go through `Stacks.Immersion.isIso_immersionConormalSheafMap_ι`, and no
  identification of `AlgebraicGeometry.Space.coborderSquareHom` with an
  `AlgebraicGeometry.Scheme.Opens.ι` is involved.  Each of `S₁` and `S₃` is a cartesian square
  whose right edge is étale, so [Stacks Project, Tag 04CO] applies to each; and that tag is proved
  as an **isomorphism**, `AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso`,
  whose forward map is exactly the canonical map of [Stacks Project, Tag 04CP] by
  `AlgebraicGeometry.Space.conormalModuleOfImmersionEtaleRestrictionIso_hom`.
  `AlgebraicGeometry.Space.coborderEtaleRestrictionIso` is that construction at `S₃` already, and
  is the template.  Finally, `AlgebraicGeometry.Space.coborderSquareHom` is
  `AlgebraicGeometry.Space.squareAmbientHom`, a composite of **two** `openSubHom`s and **no**
  `openSubMap` — it is `AlgebraicGeometry.Space.squareAmbientMap`, the other edge, that carries
  the `openSubMap` — which is what makes both the monomorphism property and étaleness one lemma
  applied twice.

## The assembly

Only the assembly remains: three instantiations of the stacking engine of
`StacksFrontier/CategoryTheory/SquareTransportComposition.lean` at the geometric instance.
`Stacks.CategoryTheory.square_transport_comp` once for the outer rectangle of `S₂` over `S₄` and
once for that of `S₁` over `S₃`, and `Stacks.CategoryTheory.square_transport_of_comp` for `hnat`
itself.  Two things about that assembly are worth recording.

* **Which rectangle is which.**  `D` is the outer rectangle of `S₂` over `S₄`, namely
  `(J, j', b, A ≫ ι')`; it is also the outer rectangle of `S₁` over `S₃` — namely
  `(J, j, 𝟙 ≫ 𝟙, w ≫ ι)` — stacked over the square `hnat` is about, because
  `AlgebraicGeometry.Space.squareAmbientMap_comp_openSubHom` gives `A ≫ ι' = w ≫ ι ≫ a`.  So the
  upper square of the final stack is **not** `S₁` but the rectangle `S₁` over `S₃`, which is why
  the cancellation is stated at that rectangle
  (`AlgebraicGeometry.Space.isIso_kernelIdealZPowSquareMap_coborderSquare_comp`) and not at `S₁`
  alone.
* **The functor is the inverse image along an identity.**
  `Stacks.CategoryTheory.square_transport_of_comp` takes the image under one functor `F` of the
  lower square's equation, and by
  `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp` that functor is the inverse image along
  the upper square's left edge, here `𝟙 ≫ 𝟙`.  So `hfaith` is the faithfulness of the inverse
  image along an identity, which `AlgebraicGeometry.Space.modulePullbackIdIso` supplies, and not
  a property of `AlgebraicGeometry.Space.modulePullback` at a general morphism, which is false.
  Matching `D` to that outer rectangle means transporting the square along
  `𝟙 ≫ 𝟙 ≫ b = b` and `(w ≫ ι) ≫ a = A ≫ ι'`, which is where the transports of this assembly
  live.

## On duplication

`AlgebraicGeometry.Space.representedConormalOfImmersionKernelIdealZPowIso` has the same type as
`AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso`, under a weaker
hypothesis on `j` (immersion rather than closed immersion).  It is **not** a renamed copy: the
closed-immersion one is built from
`AlgebraicGeometry.Space.representedAssociatedModuleKernelIdealZPowIso`, which exists only for a
closed immersion because it needs the kernel ideal sheaf of `j` to be quasi-coherent on the small
étale site, while this one is built from part (1) at immersion generality, which carries the
ambient open subspace of [Stacks Project, Tag 04CE].  Generalising the closed-immersion
declaration in place would be the better shape; it is not done here because that would mean
editing `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleRepresentedNaturality.lean`, and
because the two constructions are related only through the change-of-ambient agreement described
above.

**Naming the respelling is not a convenience but a budget requirement.**  The
alternative — dropping the definition and writing its three-factor composite out inside the
hypothesis and the conclusion of the theorem below, which removes the shared statement entirely —
elaborates and is then a **kernel deterministic timeout**, while the version with the composite
named checks in 40 s.  Nothing else about the file changes between the two, and no attribute
reaches the kernel.  So the duplicate cannot be removed by inlining; it can only be removed by
generalising the closed-immersion declaration in place.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- **Transferring a naturality square across a conjugation by two bridges, at variables.**

Read against the geometric instance: `zi` is the inverse of the spaces-side bridge of
[Stacks Project, Tag 09RR] at the right-hand immersion, `k` the canonical map of the square at
the kernel ideal sheaf, `zh` and `ph` the spaces-side bridge and part (1) at the left-hand
immersion, `pq` the respelled comparison at the right-hand immersion, `t2` and `t1` the transport
of the inverse image at the two schemes-side presentations of the conormal sheaf, and `fi` the
associated module of the schemes-side canonical map.

Every morphism lives in one category and is implicit, determined by the hypothesis naming it, so
no argument at the point of use is a restatement. -/
theorem conjugated_square_eq_of {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ : C}
    {u : A₀ ⟶ A₁} {v : A₁ ⟶ A₂} {pq : A₂ ⟶ A₃} {zi : A₀ ⟶ A₃} {q : A₁ ⟶ A₃}
    {k : A₃ ⟶ A₄} {zh : A₄ ⟶ A₅} {ph : A₅ ⟶ A₆}
    {t2 : A₂ ⟶ A₇} {fc : A₇ ⟶ A₈} {psi : A₈ ⟶ A₄} {ah : A₈ ⟶ A₆}
    {t1 : A₁ ⟶ A₉} {fn : A₉ ⟶ A₇} {fnc : A₉ ⟶ A₈} {fi : A₉ ⟶ A₆}
    (h₁ : zi = u ≫ q) (h₂ : q = v ≫ pq)
    (h₃ : pq ≫ k = t2 ≫ fc ≫ psi)
    (h₄ : psi ≫ zh ≫ ph = ah)
    (h₅ : v ≫ t2 = t1 ≫ fn)
    (h₆ : fn ≫ fc = fnc) (h₇ : fnc ≫ ah = fi) :
    (zi ≫ k ≫ zh) ≫ ph = u ≫ t1 ≫ fi := by
  subst h₁ h₂ h₄ h₆ h₇
  simp only [Category.assoc, reassoc_of% h₃, reassoc_of% h₅]

/-- Two inverse pairs cancelled out of a four-fold composite in front of a morphism. -/
theorem eq_hom_comp_inv_comp_hom_comp_inv_comp {A₀ A₁ A₂ A₃ : C} (p : A₀ ≅ A₁) (e : A₂ ≅ A₁)
    (m : A₀ ⟶ A₃) : m = p.hom ≫ e.inv ≫ e.hom ≫ p.inv ≫ m := by
  simp

/-- Two inverse pairs cancelled out of a composite that begins and ends with one isomorphism's
forward map. -/
theorem hom_comp_inv_comp_inv_comp_hom_comp_hom {A₀ A₁ A₂ A₃ : C} (p : A₀ ≅ A₁) (e : A₂ ≅ A₁)
    (m : A₃ ≅ A₀) : (e.hom ≫ p.inv ≫ m.inv) ≫ m.hom ≫ p.hom = e.hom := by
  simp

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local irreducible] modulePullback modulePullbackCompIso
  representedModuleObjPullbackIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R V : BigFppfOver B S hS} (j : R ⟶ V)
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)]

/-- **The comparison of [Stacks Project, Tag 04G2] (1) at immersion generality, respelled as the
inverse image of the kernel ideal sheaf in degree one.**

It is the associated module of `Stacks.Immersion.conormalSheafSelfIso`, followed by the inverse
of part (1) at immersion generality
(`AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`), followed by the inverse of
the bridge `AlgebraicGeometry.Space.conormalModuleOfImmersionZPowIso` of
[Stacks Project, Tag 09RR] in degree one.

Its type is that of `AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso`, which is the
same respelling of the closed case; the module documentation records why this is a different
construction and not a copy. -/
noncomputable def representedConormalOfImmersionKernelIdealZPowIso :
    (representedSmallEtaleModuleEquivalence B S hS R).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj R) R.left.property).obj
          (Stacks.ClosedImmersion.conormalSheaf
            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)) ≅
      (modulePullback B S hS (representedSpaceMap B S hS j)).obj
        (kernelIdealSheafZPow B S hS (representedSpaceMap B S hS j) 1).toSheafOfModules :=
  (representedSmallEtaleModuleEquivalence B S hS R).functor.mapIso
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj R) R.left.property).mapIso
        (Stacks.Immersion.conormalSheafSelfIso ((BigFppfOver.toScheme B S hS).map j))) ≪≫
    (conormalModuleOfImmersionRepresentedIso B S hS j).symm ≪≫
      (conormalModuleOfImmersionZPowIso B S hS (representedSpaceMap B S hS j)
        (isImmersion_representedSpaceMap B S hS j)).symm

/-- The three factors of
`AlgebraicGeometry.Space.representedConormalOfImmersionKernelIdealZPowIso`, written out.  True by
`rfl`; it is a declaration of its own so that the conjugation below receives it verbatim. -/
theorem representedConormalOfImmersionKernelIdealZPowIso_hom :
    (representedConormalOfImmersionKernelIdealZPowIso B S hS j).hom =
      ((representedSmallEtaleModuleEquivalence B S hS R).functor.mapIso
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).mapIso
              (Stacks.Immersion.conormalSheafSelfIso
                ((BigFppfOver.toScheme B S hS).map j)))).hom ≫
        (conormalModuleOfImmersionRepresentedIso B S hS j).inv ≫
          (conormalModuleOfImmersionZPowIso B S hS (representedSpaceMap B S hS j)
            (isImmersion_representedSpaceMap B S hS j)).inv :=
  rfl

/-- **The bridge of [Stacks Project, Tag 09RR] inverted, factored through the respelling.**  The
inverse of `AlgebraicGeometry.Space.conormalModuleOfImmersionZPowIso` is part (1) at immersion
generality, followed by the associated module of the inverse of
`Stacks.Immersion.conormalSheafSelfIso`, followed by the respelling.

This is the first of the two cancellations that carry part (2) between its two forms. -/
theorem conormalModuleOfImmersionZPowIso_inv_eq :
    (conormalModuleOfImmersionZPowIso B S hS (representedSpaceMap B S hS j)
          (isImmersion_representedSpaceMap B S hS j)).inv =
      (conormalModuleOfImmersionRepresentedIso B S hS j).hom ≫
        (((representedSmallEtaleModuleEquivalence B S hS R).functor.mapIso
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj R) R.left.property).mapIso
                (Stacks.Immersion.conormalSheafSelfIso
                  ((BigFppfOver.toScheme B S hS).map j)))).inv ≫
          (representedConormalOfImmersionKernelIdealZPowIso B S hS j).hom) :=
  by
    rw [representedConormalOfImmersionKernelIdealZPowIso_hom]
    erw [Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

/-- **The respelling composed back with the two bridges is the associated module of
`Stacks.Immersion.conormalSheafSelfIso`.**  The second of the two cancellations. -/
theorem representedConormalOfImmersionKernelIdealZPowIso_hom_comp :
    (representedConormalOfImmersionKernelIdealZPowIso B S hS j).hom ≫
        (conormalModuleOfImmersionZPowIso B S hS (representedSpaceMap B S hS j)
            (isImmersion_representedSpaceMap B S hS j)).hom ≫
          (conormalModuleOfImmersionRepresentedIso B S hS j).hom =
      ((representedSmallEtaleModuleEquivalence B S hS R).functor.mapIso
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).mapIso
              (Stacks.Immersion.conormalSheafSelfIso
                ((BigFppfOver.toScheme B S hS).map j)))).hom :=
  by
    rw [representedConormalOfImmersionKernelIdealZPowIso_hom]
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

section Square

variable {R' V' : BigFppfOver B S hS} (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')
    [hj' : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j')]

/-- The schemes-side canonical map of a square of immersions, with its two conjugating
isomorphisms bracketed the way the conjugation lemma consumes them. -/
theorem immersionConormalSheafMap_eq_comp (hsq : j ≫ a = b ≫ j') :
    Stacks.Immersion.immersionConormalSheafMap
        ((BigFppfOver.toScheme B S hS).map j) ((BigFppfOver.toScheme B S hS).map j')
        ((BigFppfOver.toScheme B S hS).map b) ((BigFppfOver.toScheme B S hS).map a)
        (toShHom_square_of_comp_eq B S hS j j' b a hsq) =
      ((Scheme.Modules.pullback (B.inclusion.map b.left)).map
            (Stacks.Immersion.conormalSheafSelfIso
              ((BigFppfOver.toScheme B S hS).map j')).inv ≫
          Stacks.ClosedImmersion.conormalSheafMap
            (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
            (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
            (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
            (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
            (toShHom_square_of_comp_eq B S hS j j' b a hsq)) ≫
        (Stacks.Immersion.conormalSheafSelfIso
          ((BigFppfOver.toScheme B S hS).map j)).hom :=
  (Category.assoc _ _ _).symm

/-- **Part (2) of [Stacks Project, Tag 04G2] at immersion generality, from the naturality of the
respelling.**

For a commutative square of the big fppf category over `S` whose horizontal morphisms are
immersions of schemes, the comparison of part (1) at immersion generality carries the canonical
map of conormal modules of [Stacks Project, Tag 04CP] to the associated module of
`Stacks.Immersion.immersionConormalSheafMap`, the canonical map of Morphisms, Lemma
[Stacks Project, Tag 01R4].

The hypothesis `hnat` is the same equation with
`AlgebraicGeometry.Space.representedConormalOfImmersionKernelIdealZPowIso` in place of the
closed case's `AlgebraicGeometry.Space.representedConormalKernelIdealZPowIso`, with
`AlgebraicGeometry.Space.kernelIdealZPowSquareMap` for the spaces-side map and
`Stacks.ClosedImmersion.conormalSheafMap` for the schemes-side one; it is not proved here, and
the module documentation names the assembly it still owes. -/
theorem conormalMapOfImmersions_conormalModuleOfImmersionRepresentedIso (hsq : j ≫ a = b ≫ j')
    (hnat : (modulePullback B S hS (representedSpaceMap B S hS b)).map
            (representedConormalOfImmersionKernelIdealZPowIso B S hS j').hom ≫
          kernelIdealZPowSquareMap B S hS (representedSpaceMap B S hS j)
            (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
            (representedSpaceMap B S hS a)
            (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq) 1 =
        (representedAssociatedModulePullbackIso B S hS b
              (relativelyRepresentable_yoneda_map B S hS b)
              (Stacks.ClosedImmersion.conormalSheaf
                ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS R).functor.map
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
                (Stacks.ClosedImmersion.conormalSheafMap
                  (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
                  (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
                  (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                  (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom)
                  (toShHom_square_of_comp_eq B S hS j j' b a hsq))) ≫
            (representedConormalOfImmersionKernelIdealZPowIso B S hS j).hom) :
    conormalMapOfImmersions B S hS (representedSpaceMap B S hS j)
          (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
          (representedSpaceMap B S hS a) (isImmersion_representedSpaceMap B S hS j)
          (isImmersion_representedSpaceMap B S hS j')
          (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq) ≫
        (conormalModuleOfImmersionRepresentedIso B S hS j).hom =
      (modulePullback B S hS (representedSpaceMap B S hS b)).map
          (conormalModuleOfImmersionRepresentedIso B S hS j').hom ≫
        (representedAssociatedModulePullbackIso B S hS b
              (relativelyRepresentable_yoneda_map B S hS b)
              (Stacks.Conormal.conormalSheaf
                ((BigFppfOver.toScheme B S hS).map j'))).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS R).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj R) R.left.property).map
              (Stacks.Immersion.immersionConormalSheafMap
                ((BigFppfOver.toScheme B S hS).map j)
                ((BigFppfOver.toScheme B S hS).map j')
                ((BigFppfOver.toScheme B S hS).map b)
                ((BigFppfOver.toScheme B S hS).map a)
                (toShHom_square_of_comp_eq B S hS j j' b a hsq))) :=
  (congrArg (fun t => t ≫ (conormalModuleOfImmersionRepresentedIso B S hS j).hom)
      (conormalMapOfImmersions_eq_kernelIdealZPowSquareMap B S hS
        (representedSpaceMap B S hS j) (representedSpaceMap B S hS j')
        (representedSpaceMap B S hS b) (representedSpaceMap B S hS a)
        (isImmersion_representedSpaceMap B S hS j)
        (isImmersion_representedSpaceMap B S hS j')
        (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq))).trans
    (Stacks.CategoryTheory.conjugated_square_eq_of
      (Stacks.CategoryTheory.map_eq_map_comp_map
        (modulePullback B S hS (representedSpaceMap B S hS b)) _ _
        (conormalModuleOfImmersionZPowIso_inv_eq B S hS j'))
      (Stacks.CategoryTheory.map_eq_map_comp_map
        (modulePullback B S hS (representedSpaceMap B S hS b)) _ _ rfl)
      hnat
      (representedConormalOfImmersionKernelIdealZPowIso_hom_comp B S hS j)
      (representedAssociatedModulePullbackIso_naturality B S hS b
        (relativelyRepresentable_yoneda_map B S hS b)
        (Stacks.Immersion.conormalSheafSelfIso
          ((BigFppfOver.toScheme B S hS).map j')).inv)
      (Stacks.CategoryTheory.map_map_comp_eq_of
        (representedSmallEtaleModuleEquivalence B S hS R).functor
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj R) R.left.property) _ _ rfl)
      (Stacks.CategoryTheory.map_map_comp_eq_of
        (representedSmallEtaleModuleEquivalence B S hS R).functor
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj R) R.left.property) _ _
        (immersionConormalSheafMap_eq_comp B S hS j j' b a hsq)))

end Square

end AlgebraicGeometry.Space

end
