module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPointPushforward

/-!
# The sequence of Stacks 03M8 in the shape `a_*(F|_U) → b_*(F|_R)`

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `τ : U ⟶ X` be a surjective étale morphism, let `t, s : R ⟶ U` exhibit `R` as
`U ×_X U`, write `ρ` for the common composite `t ≫ τ = s ≫ τ` and put `a = τ ≫ f`,
`b = ρ ≫ f`.  Stacks 03M8 asserts that for every `𝒪_X`-module `F` the sequence

`0 → f_*F → a_*(F|_U) → b_*(F|_R)`,

whose second arrow is the difference of restriction along `t` and along `s`, is exact.

`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardPresentationExact.lean` proves the exactness
in the form the source's proof displays it — the middle and right terms being the sections of
`F` over `V ×_Y U` and `V ×_Y R` — and carries the tag.  What that file leaves open, and this
file supplies, is the *shape* of the assertion: the three terms as the direct images
`f_*`, `a_*`, `b_*` of a module and of its étale restrictions, and the arrows of the sequence
between them.

This file constructs those arrows and proves that the two readings of the second one agree
after the first, which is the assertion that the displayed sequence is a complex: for `h` equal
to `t` and to `s` the composite `f_*F → a_*(F|_U) → b_*(F|_R)` is one and the same morphism,
namely the arrow attached to `ρ` itself.  Equivalently, the difference `t^* - s^*` kills the
image of `f_*F`.  Everything is proved at the level of sheaves of sets at the universe `u` of
the structure rings, which by
`AlgebraicGeometry.Space.moduleSheaf_etaleModulePullback` and
`AlgebraicGeometry.Space.moduleSheaf_modulePushforward` is the level the three terms of the
module sequence live over.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDirectImageCompIso` names the composition comparison
  `τ_* ⋙ f_* ≅ (τ ≫ f)_*` of the direct image of sheaves of sets at the universe of the
  structure rings.  It is Stacks 03G2, part (3), transported to the small étale sites; the
  functor it is stated for is `AlgebraicGeometry.Space.smallEtaleDirectImage`.
* `AlgebraicGeometry.Space.restrictionUnitArrow` is the arrow `τ_*(P|_U) ⟶ ρ_*(P|_R)` attached
  to a factorization `h ≫ τ = ρ` with `h` étale: the direct image along `τ` of the unit of
  `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `h`, followed by the
  composition comparison.  In Stacks 03M8 it is `t^*` for `h = t` and `s^*` for `h = s`.
* `AlgebraicGeometry.Space.chartDirectImageUnitArrow` is the first arrow `f_*P ⟶ a_*(P|_U)`
  of the source's sequence: the direct image along `f` of the unit at `τ`, followed by the
  composition comparison.
* `AlgebraicGeometry.Space.chartDirectImageParallelArrow` is the second arrow
  `a_*(P|_U) ⟶ b_*(P|_R)`, one for each factorization of `ρ` through `τ`.
* `AlgebraicGeometry.Space.moduleRestrictionUnitArrow`,
  `AlgebraicGeometry.Space.moduleChartDirectImageUnitArrow` and
  `AlgebraicGeometry.Space.moduleChartDirectImageParallelArrow` are the same three arrows for
  `𝒪`-modules, built from the unit of
  `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` and the composition comparison
  `AlgebraicGeometry.Space.modulePushforwardCompIso` of Stacks 03LU: the sequence
  `0 → f_*F → a_*(F|_U) → b_*(F|_R)` of the source, in `Mod(𝒪_Y)`, with the arrows the source
  prescribes.

## Main results

* `AlgebraicGeometry.Space.unit_comp_restrictionUnitArrow`: the unit at `τ` followed by
  `AlgebraicGeometry.Space.restrictionUnitArrow` of a factorization `h ≫ τ = ρ` is the unit at
  `ρ`.  This is `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_app`, the
  composition law of Stacks 03LQ, read through the factorization.
* `AlgebraicGeometry.Space.chartDirectImageUnitArrow_comp_parallelArrow`: the first arrow of the
  sequence followed by the second is the first arrow attached to `ρ`.
* `AlgebraicGeometry.Space.chartDirectImageUnitArrow_comp_parallelArrow_eq`: **the displayed
  sequence of Stacks 03M8 is a complex** — the two parallel arrows of the second term agree
  after the first arrow, so the difference `t^* - s^*` vanishes on `f_*P`.
* `AlgebraicGeometry.Space.moduleSheaf_etaleModulePullback`: the sheaf of sets underlying the
  étale restriction `F|_U` of an `𝒪_X`-module is the small étale restriction of the sheaf of
  sets underlying `F`.  It holds by `rfl`.
* `AlgebraicGeometry.Space.moduleSheaf_modulePushforward_etaleModulePullback`: the sheaf of sets
  underlying the middle term `a_*(F|_U)` of the source's sequence is `a_*` of the small étale
  restriction of the sheaf of sets underlying `F`; also `rfl`.
* `AlgebraicGeometry.Space.smallEtaleSetRestriction_comp_obj` and
  `AlgebraicGeometry.Space.etaleModulePullback_comp_obj`: restriction along a composite of
  étale morphisms is the composite of the restrictions, on the nose, for sheaves of sets and
  for modules.  These are what make `F|_R` unambiguous: the two factorizations `t ≫ τ` and
  `s ≫ τ` of `ρ` give the same restriction of `F` as soon as they give the same morphism.
* `AlgebraicGeometry.Space.isLimitOfIsLimitModuleSheaf`: a fork of `𝒪`-modules on an algebraic
  space is a limit as soon as the fork of underlying sheaves of sets is.  This is
  `Stacks.Sheaves.RingedPoint.reflectsFiniteLimits_moduleSheafFunctor` at the shape of a fork.

## Implementation notes

The arrow of `AlgebraicGeometry.Space.restrictionUnitArrow` cannot be written down without the
factorization: its target names `ρ` and the unit it is built from names `h ≫ τ`, and `ρ` is
only *equal* to `h ≫ τ`, so the definition substitutes the factorization before producing the
term.  That is also why it is a definition rather than a composite written out at each use:
the two uses in Stacks 03M8, for `t` and for `s`, substitute two different factorizations of
the same `ρ`, and it is exactly the fact that both land in `ρ_*(P|_R)` that makes the source's
"difference of `t^*` and `s^*`" well-formed.  No hypothesis beyond the factorization is used,
and in particular neither surjectivity of `τ` nor the cartesian square `R = U ×_X U` is needed
for any statement in this file: those are what the *exactness* of the sequence consumes, not
its shape.

The composition comparison for the direct image of sheaves of sets is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, stated for the pushforward of the
morphism of small étale topoi of Stacks 03G8; that pushforward is
`AlgebraicGeometry.Space.smallEtaleDirectImage` on the nose, by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward_eq`, so
`AlgebraicGeometry.Space.smallEtaleDirectImageCompIso` is a reducible restatement with no
content of its own.  It is introduced because every statement below names it, and the
unrestated form mentions the morphism of topoi rather than the functor.

**The module-level sequence is a complex, and it is exact; this file is not where that is
proved.**  The three module arrows are constructed here, and nothing below asserts that they
compose to zero.  That assertion is
`AlgebraicGeometry.Space.moduleChartDirectImage_comp_sub_eq_zero`, and the exactness of the
sequence together with the injectivity of its first arrow is
`AlgebraicGeometry.Space.exact_moduleChartDirectImage`, which carries the attribute for
Tag 03M8; both are in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationExactSequence.lean` and
neither is conditional.  They are reached by reflecting a limiting fork of sheaves of *sets*
back to modules — `Stacks.Sheaves.RingedToposModules.isLimitForkOfIsLimitForkModuleSheaf`
against `AlgebraicGeometry.Space.isLimitForkSheafChartDirectImageCanonical`, with the three
arrows identified by the `heq_moduleSheafFunctor_map_…` lemmas — and so they do not use the
transport discussed below.

What the rest of this section records is therefore the state of **one route that is not the one
taken**: proving the complex law by transporting
`AlgebraicGeometry.Space.chartDirectImageUnitArrow_comp_parallelArrow_eq` along
`AlgebraicGeometry.Space.moduleSheaf_etaleModulePullback`.  It is kept because the obstruction
is worth recording, not because the sequence is waiting on it.  That transport needs two
inputs, and **both are now available** — what blocks the transport is no longer an input but the
kernel:

* **Available.**  The underlying map of sheaves of sets of the unit of
  `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is the unit of
  `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`.  It is
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app`
  (`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitChain.lean`), the comparison the
  four steps of
  `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitComparison.lean` are for.  The
  same comparison is what
  `AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction` and
  `AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_unit`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompIsoEtaleRestriction.lean`)
  carry as the hypothesis `hu`, but in the shape of an equality of the units of two adjunctions
  of *modules*; deriving that shape from the comparison is not done;
* **Available.**  That the composition comparison
  `AlgebraicGeometry.Space.modulePushforwardCompIso` of Stacks 03LU is
  `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` on underlying sheaves of sets is
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsComp.lean`), which carries
  `@[stacks 03LU]` for exactly this clause, together with
  `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_eq` in the same file, which rewrites
  the comparison into the transported `CategoryTheory.Functor.compIsoCongr` spelling that clause
  is stated at.  The implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean`, which record the
  clause as missing and list the spellings of the assembly that diverge, predate it and are
  stale: the assembly was carried out by staying at the level of isomorphisms and retyping with
  `HEq` rather than by reducing the `eqToHom` transports.

With both inputs in hand,
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_app` and faithfulness of
the underlying sheaf of sets
(`Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor`) would give the module-level
counterpart of `AlgebraicGeometry.Space.unit_comp_restrictionUnitArrow`, and the module sequence
would then be a complex by the same two lines as the set-level one.  **What goes through, and what
does not.**  The transport needs the sheaf of sets underlying each module arrow,
and the first half of that goes through:

`(smallEtaleDirectImage f).map (𝒱.map ((etaleModulePullbackAdjunction τ hτ).unit.app F)) =
  (smallEtaleDirectImage f).map ((smallEtaleSetRestrictionAdjunction τ hτ).unit.app (𝒱F))`

elaborates in seconds as `congrArg` against the comparison, *provided* the right-hand side's
arrow has its type pinned by a `show` in the `𝒱((modulePushforward τ).obj (F|_U))` spelling;
without that pin the statement reports `(deterministic) timeout at 'whnf'`.  The second half does
not go through: carrying `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_eq` under
`Sheaf.moduleSheafFunctor` by `congrArg` — the step that would let
`AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app` apply to the comparison as
the arrows spell it — elaborates and then reports

`error: (kernel) deterministic timeout`

so the obstruction now lies in the kernel rather than the elaborator, and it sits on the Stacks
03LU composition comparison and not on the unit.  Raising a limit is not available in this
repository, and a kernel timeout is not a limit that could be raised anyway.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Restriction along a composite -/

section Composite

variable {U V W : AlgebraicSpaces B S hS}

/-- **Restriction of sheaves of sets along a composite of étale morphisms is the composite of
the restrictions**, on the nose: both are restriction of sections along postcomposition of
étale charts, and postcomposition of charts is strictly functorial. -/
theorem smallEtaleSetRestriction_comp_obj (h : U ⟶ V) (g : V ⟶ W) (hh : IsEtale B S hS h.hom)
    (hg : IsEtale B S hS g.hom) (hhg : IsEtale B S hS (h ≫ g).hom)
    (P : Sheaf (SmallEtale.topology B S hS W.1) (Type u)) :
    (smallEtaleSetRestriction B S hS h hh).obj ((smallEtaleSetRestriction B S hS g hg).obj P) =
      (smallEtaleSetRestriction B S hS (h ≫ g) hhg).obj P := rfl

/-- **Restriction of modules along a composite of étale morphisms is the composite of the
restrictions**, on the nose, by the same computation as
`AlgebraicGeometry.Space.smallEtaleSetRestriction_comp_obj`: étale restriction of modules
reindexes the sections along postcomposition of charts and leaves the scalars alone. -/
theorem etaleModulePullback_comp_obj (h : U ⟶ V) (g : V ⟶ W) (hh : IsEtale B S hS h.hom)
    (hg : IsEtale B S hS g.hom) (hhg : IsEtale B S hS (h ≫ g).hom)
    (M : Modules.{u, u} B S hS W.1 W.2) :
    (etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS g hg).obj M) =
      (etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M := rfl

/-- **The composition comparison for the direct image of sheaves of sets** at the universe of
the structure rings: the direct image along `h` followed by the direct image along `g` is the
direct image along `h ≫ g`.

This is `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, Stacks 03G2, part (3), carried
to the small étale sites; the pushforward of the morphism of small étale topoi *is*
`AlgebraicGeometry.Space.smallEtaleDirectImage`, so no content is added here. -/
noncomputable abbrev smallEtaleDirectImageCompIso (h : U ⟶ V) (g : V ⟶ W) :
    smallEtaleDirectImage B S hS h ⋙ smallEtaleDirectImage B S hS g ≅
      smallEtaleDirectImage B S hS (h ≫ g) :=
  smallToposMorphismTypeU_comp B S hS h g

end Composite

/-! ### The underlying sheaves of sets of the terms of the sequence -/

section ModuleSheaf

variable {U V : AlgebraicSpaces B S hS}

/-- **The sheaf of sets underlying `F|_U` is the small étale restriction of the sheaf of sets
underlying `F`.**  Étale restriction of modules reindexes the sections along postcomposition of
charts and restricts the scalars along an identity, and restriction of scalars does not change
the sections; so the two sides are the same sheaf of sets. -/
theorem moduleSheaf_etaleModulePullback (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (M : Modules.{u, u} B S hS V.1 V.2) :
    Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS U)
        ((etaleModulePullback.{u, u} B S hS h hh).obj M) =
      (smallEtaleSetRestriction B S hS h hh).obj
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS V) M) := rfl

end ModuleSheaf

section MiddleTerm

variable {X Y U : AlgebraicSpaces B S hS}

/-- **The sheaf of sets underlying the middle term `a_*(F|_U)` of the sequence of Stacks 03M8.**
It is the direct image along `a` of the small étale restriction to `U` of the sheaf of sets
underlying `F`.

Both halves hold by `rfl`: `AlgebraicGeometry.Space.moduleSheaf_modulePushforward` for the
direct image and `AlgebraicGeometry.Space.moduleSheaf_etaleModulePullback` for the
restriction. -/
theorem moduleSheaf_modulePushforward_etaleModulePullback (a : U ⟶ Y) (τ : U ⟶ X)
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y)
        ((modulePushforward B S hS a).obj ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)) =
      (smallEtaleDirectImage B S hS a).obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj
          (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) F)) := rfl

end MiddleTerm

/-! ### The arrow attached to a factorization -/

section Arrows

variable {X U R : AlgebraicSpaces B S hS}

/-- **The arrow `τ_*(P|_U) ⟶ ρ_*(P|_R)` of a factorization `h ≫ τ = ρ`.**  For étale morphisms
`τ : U ⟶ X` and `h : R ⟶ U` and a sheaf of sets `P` on the small étale site of `X`, it is the
direct image along `τ` of the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `h`, followed by the
composition comparison `AlgebraicGeometry.Space.smallEtaleDirectImageCompIso`.

In Stacks 03M8, with `R = U ×_X U` and `t, s : R ⟶ U` its two projections, this is `t^*` for
`h = t` and `s^*` for `h = s`: the two factorizations of the same `ρ` give two arrows with the
same source and the same target, which is what makes the source's difference `t^* - s^*`
well-formed.  The factorization is substituted before the term is produced, because the target
names `ρ` while the unit names `h ≫ τ`. -/
noncomputable def restrictionUnitArrow {τ : U ⟶ X} (hτ : IsEtale B S hS τ.hom) {h : R ⟶ U}
    (hh : IsEtale B S hS h.hom) {ρ : R ⟶ X} (hρ : IsEtale B S hS ρ.hom) (hfac : h ≫ τ = ρ)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtaleDirectImage B S hS τ).obj ((smallEtaleSetRestriction B S hS τ hτ).obj P) ⟶
      (smallEtaleDirectImage B S hS ρ).obj
        ((smallEtaleSetRestriction B S hS ρ hρ).obj P) := by
  subst hfac
  exact (smallEtaleDirectImage B S hS τ).map
      ((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
        ((smallEtaleSetRestriction B S hS τ hτ).obj P)) ≫
    (smallEtaleDirectImageCompIso B S hS h τ).hom.app
      ((smallEtaleSetRestriction B S hS (h ≫ τ) hρ).obj P)

/-- **The unit at `τ` followed by the arrow of a factorization is the unit at `ρ`.**  This is
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_app`, the composition law
of Stacks 03LQ, read through the factorization `h ≫ τ = ρ`. -/
theorem unit_comp_restrictionUnitArrow {τ : U ⟶ X} (hτ : IsEtale B S hS τ.hom) {h : R ⟶ U}
    (hh : IsEtale B S hS h.hom) {ρ : R ⟶ X} (hρ : IsEtale B S hS ρ.hom) (hfac : h ≫ τ = ρ)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app P ≫
        restrictionUnitArrow B S hS hτ hh hρ hfac P =
      (smallEtaleSetRestrictionAdjunction B S hS ρ hρ).unit.app P := by
  subst hfac
  exact smallEtaleSetRestrictionAdjunction_unit_comp_app B S hS h τ hh hτ hρ P

end Arrows

/-! ### The sequence of Stacks 03M8 -/

section Sequence

variable {X Y U R : AlgebraicSpaces B S hS}

/-- **The first arrow `f_*P ⟶ a_*(P|_U)` of the sequence of Stacks 03M8**, for `a = τ ≫ f`: the
direct image along `f` of the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `τ`, followed by the
composition comparison of the direct images. -/
noncomputable def chartDirectImageUnitArrow (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtaleDirectImage B S hS f).obj P ⟶
      (smallEtaleDirectImage B S hS (τ ≫ f)).obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj P) :=
  (smallEtaleDirectImage B S hS f).map
      ((smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app P) ≫
    (smallEtaleDirectImageCompIso B S hS τ f).hom.app
      ((smallEtaleSetRestriction B S hS τ hτ).obj P)

/-- **The second arrow `a_*(P|_U) ⟶ b_*(P|_R)` of the sequence of Stacks 03M8**, one for each
factorization `h ≫ τ = ρ`, with `a = τ ≫ f` and `b = ρ ≫ f`: the direct image along `f` of
`AlgebraicGeometry.Space.restrictionUnitArrow`, conjugated by the composition comparisons of
the direct images along `τ ≫ f` and along `ρ ≫ f`.

For `h = t` it is the source's `t^*` and for `h = s` the source's `s^*`. -/
noncomputable def chartDirectImageParallelArrow (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) {h : R ⟶ U} (hh : IsEtale B S hS h.hom) {ρ : R ⟶ X}
    (hρ : IsEtale B S hS ρ.hom) (hfac : h ≫ τ = ρ)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallEtaleDirectImage B S hS (τ ≫ f)).obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj P) ⟶
      (smallEtaleDirectImage B S hS (ρ ≫ f)).obj
        ((smallEtaleSetRestriction B S hS ρ hρ).obj P) :=
  (smallEtaleDirectImageCompIso B S hS τ f).inv.app
      ((smallEtaleSetRestriction B S hS τ hτ).obj P) ≫
    (smallEtaleDirectImage B S hS f).map
      (restrictionUnitArrow B S hS hτ hh hρ hfac P) ≫
    (smallEtaleDirectImageCompIso B S hS ρ f).hom.app
      ((smallEtaleSetRestriction B S hS ρ hρ).obj P)

/-- **The first arrow of the sequence followed by the second is the first arrow attached to
`ρ`.**  For `a = τ ≫ f` and `b = ρ ≫ f` the composite
`f_*P → a_*(P|_U) → b_*(P|_R)` does not depend on the factorization `h ≫ τ = ρ` used to build
the second arrow: it is `AlgebraicGeometry.Space.chartDirectImageUnitArrow` of `ρ` itself.

The two composition comparisons in the middle cancel, and what is left is the direct image
along `f` of `AlgebraicGeometry.Space.unit_comp_restrictionUnitArrow`. -/
theorem chartDirectImageUnitArrow_comp_parallelArrow (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) {h : R ⟶ U} (hh : IsEtale B S hS h.hom) {ρ : R ⟶ X}
    (hρ : IsEtale B S hS ρ.hom) (hfac : h ≫ τ = ρ)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    chartDirectImageUnitArrow B S hS f hτ P ≫
        chartDirectImageParallelArrow B S hS f hτ hh hρ hfac P =
      chartDirectImageUnitArrow B S hS f hρ P := by
  rw [chartDirectImageUnitArrow, chartDirectImageParallelArrow, Category.assoc,
    ← Category.assoc ((smallEtaleDirectImageCompIso B S hS τ f).hom.app _),
    Iso.hom_inv_id_app, Category.id_comp, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    unit_comp_restrictionUnitArrow, chartDirectImageUnitArrow]

/-- **The displayed sequence of Stacks 03M8 is a complex.**  Let `f : X ⟶ Y` be a morphism of
algebraic spaces, let `τ : U ⟶ X` be étale, let `t, s : R ⟶ U` be étale and let `ρ : R ⟶ X` be
étale with `t ≫ τ = ρ` and `s ≫ τ = ρ` — in Stacks 03M8, `R = U ×_X U` with its two
projections.  Put `a = τ ≫ f` and `b = ρ ≫ f`.  Then the two parallel arrows
`a_*(P|_U) ⟶ b_*(P|_R)` attached to `t` and to `s` agree after the first arrow
`f_*P ⟶ a_*(P|_U)`:

`f_*P → a_*(P|_U) ⇉ b_*(P|_R)`

is a fork.  Equivalently, the source's difference `t^* - s^*` vanishes on the image of `f_*P`,
which is the "complex" half of the source's exactness assertion.

Both composites are `AlgebraicGeometry.Space.chartDirectImageUnitArrow` of `ρ`, by
`AlgebraicGeometry.Space.chartDirectImageUnitArrow_comp_parallelArrow`. -/
theorem chartDirectImageUnitArrow_comp_parallelArrow_eq (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) {t s : R ⟶ U} (ht : IsEtale B S hS t.hom)
    (hs : IsEtale B S hS s.hom) {ρ : R ⟶ X} (hρ : IsEtale B S hS ρ.hom) (hfact : t ≫ τ = ρ)
    (hfacs : s ≫ τ = ρ) (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    chartDirectImageUnitArrow B S hS f hτ P ≫
        chartDirectImageParallelArrow B S hS f hτ ht hρ hfact P =
      chartDirectImageUnitArrow B S hS f hτ P ≫
        chartDirectImageParallelArrow B S hS f hτ hs hρ hfacs P :=
  (chartDirectImageUnitArrow_comp_parallelArrow B S hS f hτ ht hρ hfact P).trans
    (chartDirectImageUnitArrow_comp_parallelArrow B S hS f hτ hs hρ hfacs P).symm

end Sequence

/-! ### The sequence of Stacks 03M8 for modules -/

section ModuleSequence

variable {X Y U R : AlgebraicSpaces B S hS}

/-- **The arrow `τ_*(F|_U) ⟶ ρ_*(F|_R)` of a factorization `h ≫ τ = ρ`, for modules.**  It is
the direct image along `τ` of the unit of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` at `h`, followed by the composition
comparison `AlgebraicGeometry.Space.modulePushforwardCompIso` of Stacks 03LU and the strict
composition `AlgebraicGeometry.Space.etaleModulePullbackComp` of étale restrictions.

This is the module-level counterpart of
`AlgebraicGeometry.Space.restrictionUnitArrow`, and as there the factorization is substituted
before the term is produced. -/
noncomputable def moduleRestrictionUnitArrow {τ : U ⟶ X} (hτ : IsEtale B S hS τ.hom)
    {h : R ⟶ U} (hh : IsEtale B S hS h.hom) {ρ : R ⟶ X} (hρ : IsEtale B S hS ρ.hom)
    (hfac : h ≫ τ = ρ) (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS τ).obj ((etaleModulePullback.{u, u} B S hS τ hτ).obj F) ⟶
      (modulePushforward B S hS ρ).obj
        ((etaleModulePullback.{u, u} B S hS ρ hρ).obj F) := by
  subst hfac
  exact (modulePushforward B S hS τ).map
      ((etaleModulePullbackAdjunction B S hS h hh).unit.app
        ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)) ≫
    (modulePushforwardCompIso B S hS h τ).hom.app
      ((etaleModulePullback.{u, u} B S hS h hh).obj
        ((etaleModulePullback.{u, u} B S hS τ hτ).obj F))

/-- **The first arrow `f_*F ⟶ a_*(F|_U)` of the sequence of Stacks 03M8, for modules**, with
`a = τ ≫ f`: the direct image along `f` of the unit of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` at `τ`, followed by the composition
comparison of Stacks 03LU. -/
noncomputable def moduleChartDirectImageUnitArrow (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS f).obj F ⟶
      (modulePushforward B S hS (τ ≫ f)).obj
        ((etaleModulePullback.{u, u} B S hS τ hτ).obj F) :=
  (modulePushforward B S hS f).map
      ((etaleModulePullbackAdjunction B S hS τ hτ).unit.app F) ≫
    (modulePushforwardCompIso B S hS τ f).hom.app
      ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)

/-- **The second arrow `a_*(F|_U) ⟶ b_*(F|_R)` of the sequence of Stacks 03M8, for modules**,
one for each factorization `h ≫ τ = ρ`, with `a = τ ≫ f` and `b = ρ ≫ f`: the direct image
along `f` of `AlgebraicGeometry.Space.moduleRestrictionUnitArrow`, conjugated by the
composition comparisons of Stacks 03LU along `τ ≫ f` and along `ρ ≫ f`.

For `h = t` it is the source's `t^*` and for `h = s` the source's `s^*`, so the source's second
arrow is the difference of the two. -/
noncomputable def moduleChartDirectImageParallelArrow (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) {h : R ⟶ U} (hh : IsEtale B S hS h.hom) {ρ : R ⟶ X}
    (hρ : IsEtale B S hS ρ.hom) (hfac : h ≫ τ = ρ) (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS (τ ≫ f)).obj
        ((etaleModulePullback.{u, u} B S hS τ hτ).obj F) ⟶
      (modulePushforward B S hS (ρ ≫ f)).obj
        ((etaleModulePullback.{u, u} B S hS ρ hρ).obj F) :=
  (modulePushforwardCompIso B S hS τ f).inv.app
      ((etaleModulePullback.{u, u} B S hS τ hτ).obj F) ≫
    (modulePushforward B S hS f).map
      (moduleRestrictionUnitArrow B S hS hτ hh hρ hfac F) ≫
    (modulePushforwardCompIso B S hS ρ f).hom.app
      ((etaleModulePullback.{u, u} B S hS ρ hρ).obj F)

end ModuleSequence

/-! ### Forks of modules are detected on underlying sheaves of sets -/

section Reflect

variable {X : AlgebraicSpaces B S hS}

/-- **A fork of `𝒪_X`-modules is a limit as soon as the fork of underlying sheaves of sets
is.**  The functor taking a sheaf of modules to its underlying sheaf of sets reflects finite
limits (`Stacks.Sheaves.RingedPoint.reflectsFiniteLimits_moduleSheafFunctor`), and the shape of
a fork is finite.

This is the step by which the exactness assertion of Stacks 03M8 for `𝒪`-modules would be
reduced to the corresponding assertion for sheaves of sets. -/
noncomputable def isLimitOfIsLimitModuleSheaf {M N : Modules.{u, u} B S hS X.1 X.2}
    {φ ψ : M ⟶ N} (c : Fork φ ψ)
    (hc : IsLimit ((Sheaf.moduleSheafFunctor.{u, u, u + 1}
      (structureRingSheaf B S hS X)).mapCone c)) :
    IsLimit c := by
  have hrefl := Stacks.Sheaves.RingedPoint.reflectsFiniteLimits_moduleSheafFunctor
    (SmallEtale.topology B S hS X.1) (structureRingSheaf B S hS X)
  exact ((hrefl.reflects WalkingParallelPair).reflectsLimit.reflects hc).some

end Reflect

end AlgebraicGeometry.Space

end
