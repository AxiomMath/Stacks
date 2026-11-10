module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartNatural
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistNatural

/-!
# The source factor of the chart maps `χ_w` of `θ` of Stacks 0D2Z along morphisms of points

The chart map `χ_w : w^*(r^*𝒪(d)) ⟶ w^*(ℒ^{⊗ d}|_{U(ψ)})` at a scheme point `w` of `U(ψ)`
(`…InvertibleTwistingRestriction.chartMap`) is a composite of three factors; its source factor
(`…InvertibleTwistingRestriction.chartSourceIso`) identifies `w^*(r^*𝒪(d))` with the module
attached (Stacks 03DX (2)) to `c_w^*𝒪(d)` on the scheme `W`, through the comparisons of
Stacks 03LU along the two factorisations of `r ∘ w` and the base change identification of
Stacks 084D at `W`.

This file assembles the pieces of **the square of that factor** along a morphism `τ : T' ⟶ T` of
test schemes, in the shape of the first hypothesis of
`AlgebraicGeometry.Space.pullbackTransportSquare_of_squares`.  The mathematical content is the
coherence of Stacks 03LU around the square of the two factorisations
(`AlgebraicGeometry.Space.modulePullback_sourceChain_eq`) together with the naturality of
Stacks 084D in the scheme point (`…RelativeProjSituation.fibreToSpaceTwistModuleIso_comp`); the
reduction of the square to those two is carried out by the chases of the section
`AbstractChases`, which are stated in an arbitrary category so that no step of the reduction is
ever elaborated at the category of modules on an algebraic space.

## Main results

* `AlgebraicGeometry.Space.modulePullback_sourceChain_eq`: **the coherence of Stacks 03LU behind
  the square**, at variables: for `rτ ≫ A = A₁`, two factorisations `A ≫ b = rc ≫ b'` and
  `A₁ ≫ b = rc₁ ≫ b'₁` of the two scheme points and `ry ≫ b' = b'₁`, the two composites of the
  comparisons of Stacks 03LU and transports `rτ^*(A^*(b^*𝒯)) ⟶ q^*(b'^*𝒯)` around the square
  agree; `…_eq_comp` is the same with a trailing morphism.
* `AlgebraicGeometry.Space.sourceReading_chase`,
  `AlgebraicGeometry.Space.targetReading_chase`,
  `AlgebraicGeometry.Space.leftSquare_chase`,
  `AlgebraicGeometry.Space.rightSquare_chase`,
  `AlgebraicGeometry.Space.attachedSourceSides_chase`,
  `AlgebraicGeometry.Space.attachedSourceRightGlue_chase`,
  `AlgebraicGeometry.Space.attachedSourceRightRead_chase`,
  `AlgebraicGeometry.Space.attachedSourceSquareLeft_chase`,
  `AlgebraicGeometry.Space.comp_congr_five`: the reductions of the square to that coherence, to
  the readings of Stacks 03DX (2) and to the comparison of the two pullbacks, at variables in an
  arbitrary category.
* `AlgebraicGeometry.Space.trans_trans_hom`, `AlgebraicGeometry.Space.comp_assoc_five_of_trans`:
  the underlying morphism of a three-fold composite of isomorphisms, and the five-factor
  composite read off one whose first factor is again three-fold, which is how
  `…InvertibleTwistingRestriction.chartSourceIso` is read without comparing two composites.
* `…InvertibleTwistingRestriction.map_comp_locusPoint_comp`,
  `…InvertibleTwistingRestriction.comp_chartSection_locusPoint`: the scheme point of `Y` under
  `w ∘ τ`, and the naturality `c_w ∘ τ = y ∘ c_{w ∘ τ}` of the sections.
* `…InvertibleTwistingRestriction.chartSource_reading`,
  `…InvertibleTwistingRestriction.chartSource_target_reading`,
  `…InvertibleTwistingRestriction.chartSource_sourceChain`: **the three pieces of the square of
  the source factor at the scheme points of `U(ψ)`** -- the contraction of its left-hand side,
  the contraction of its right-hand side, and the coherence of Stacks 03LU between them.
* `…InvertibleTwistingRestriction.chartSource_sides`: **the two sides of the square, glued along
  that coherence** -- the left-hand side of the square, read through the contraction of its last
  three factors, is the right-hand side followed by the reading of `𝒪(d)` along `c_{w ∘ τ} ≫ y`.
* `…InvertibleTwistingRestriction.chartSourceIso_hom_eq`: **the five factors of the source
  factor** `…InvertibleTwistingRestriction.chartSourceIso`.
* `AlgebraicGeometry.Space.attachedSourceReadingComp`: the reading of `𝒪(d)` along `c₁ ≫ y`,
  which the readings of BOTH sides of the square are stated at, so that they spell it the same
  way.
* `AlgebraicGeometry.Space.modulePullback_map_attachedSource_reading_eq`: the reading of the base
  change identification along the section `c`, pulled back along `τ` and composed with the module
  attached to the comparison `σ` of the two pullbacks -- the contraction of the left-hand side of
  the square.
* `AlgebraicGeometry.Space.modulePullback_map_attachedSource_target_reading_eq`: the reading along
  the section `c₁` of the transferred identification -- the contraction of the right-hand side.
* `AlgebraicGeometry.Space.attachedModuleIsoPullback_hom_of_eq` is NOT here: the step
  `(eqToIso h ≪≫ A).hom = eqToHom h ≫ A.hom` at these types is beyond the per-declaration
  budget in every shape tried (`rfl`, `rw`/`simp only [Iso.trans_hom]`, an abstract lemma applied
  as a term), so the transferred identification is consumed in its isomorphism form, by
  `…RelativeProjSituation.fibreToSpaceTwistModuleIso_comp_of_eq` together with
  `AlgebraicGeometry.Space.attachedModuleIsoPullback_hom`, inside
  `…modulePullback_map_attachedSource_target_reading_eq`.
* `AlgebraicGeometry.Space.attachedSourceSigma_eq`,
  `AlgebraicGeometry.Space.attachedSourceEqToHom_cancel`: the two facts about the comparison `σ`
  of the two pullbacks that the first chase consumes.
* `…RelativeProjSituation.fibreToSpaceTwistModuleIso_comp_of_eq`: **the naturality of Stacks 084D
  in the scheme point, for a point `v` equal to `f ∘ τ`** (the form in which the scheme points of
  `U(ψ)` present it).
* `…InvertibleTwistingRestriction.pointHom_comp_invertibleSpaceMorphism`: the factorisation
  `r_{ℒ,ψ} ∘ w = (T ×_Y Proj_Y(𝒜) ⟶ Proj_Y(𝒜)) ∘ c_w` of the chart maps.

## Implementation notes

The two sides of `AlgebraicGeometry.Space.modulePullback_sourceChain_eq` are compared after
composing with the comparison of Stacks 03LU for the total composite, which is split off by
`AlgebraicGeometry.Space.modulePullbackCompHom_comp_compInv`; each side is contracted to the same
canonical morphism by its own lemma, and the left side's contraction is split again into its
inner and outer halves, because a single declaration carrying the whole chain exhausts the
kernel.  For the same reason the inner half substitutes the two transports away before
contracting.

Every statement that mixes morphisms of modules on an algebraic space with the modules attached
to quasi-coherent modules on the schemes of the site is produced by `type_of%` of an application
of a chase, never written out: a hand-written statement of the same equation is rejected with a
`whnf` or `isDefEq` heartbeat timeout, and so is any step that asks the elaborator to COMPARE two
such composites (`Eq.trans` of two of them, or feeding one as the hypothesis of a chase whose
corresponding pattern is already instantiated).

**How the gluing of the three pieces is arranged, and what it cost.**  The three pieces above
are exactly the hypotheses `HL`, `HC`, `HR` of
`AlgebraicGeometry.Space.attachedSourceSides_chase` and of the two halves of the square, and
those chases are arranged so that the
elaborator never compares more than one morphism at a time: every object, the functor, both
ambient categories and all fourteen factors are implicit, `HL` comes first and determines them,
`HC` carries its own `cH'`, `T1'`, `T2'` with their own intermediate objects, and the single
comparison the gluing needs is isolated as `hbridge`.  With the functor named, with
`tl` inside `HC`, or with `HC` sharing `cH`, `T1`, `T2` with `HL`, the elaborator times out at
`whnf`/`isDefEq` or runs out of recursion depth.  The orientation of the bridge matters too:
written `cH ≫ T1 ≫ T2 = cH' ≫ T1' ≫ T2'` the elaborator closes it, while written the other way
round it times out at `whnf`.

With the bridge isolated, the elaborator closes it (`with_reducible rfl` and `congr 1` both
succeed) while the **kernel** can report `(kernel) deterministic timeout`.  What the kernel is
asked to decide is the defeq of two spellings of
`AlgebraicGeometry.Space.modulePullbackCompHom B S hS (representedSpaceMap B S hS τ)
(representedSpaceMap B S hS c) ((modulePullback B S hS b').obj (s.twistModule Px d).obj)`,
identical in every explicit argument but not in an implicit one: the readings of Stacks 03DX (2)
took the twist as the QUASI-COHERENT OBJECT of
`AlgebraicGeometry.Space.RelativeProjSituation.twistModule`, over a bundled algebraic space `P`,
and so indexed their `𝒪`-modules by the site of `P.obj`, while the coherence of Stacks 03LU and
`…InvertibleTwistingRestriction.chartSourceIso` index theirs by the site of
`s.relativeProjFunctor` itself.  Those agree by one iota step, which is why the elaborator closed
the bridge at reducible transparency; but the kernel has no reducibility setting, and comparing
`s.relativeProjFunctor` with a projection of a constructor it unfolds the side of greater
definition height -- the relative Proj.  **The cure is to state the readings for an `𝒪`-module on
`P` rather than for a quasi-coherent object on it** (quasi-coherence is never used in them), here
and in `AlgebraicGeometry.Space.attachedModuleIsoPullback_hom`: both producers then spell that
morphism identically and the bridge is a `rfl` the kernel checks at once.  That is
`…InvertibleTwistingRestriction.chartSource_sides`, and it is kernel-checked.

**What the square of the source factor still needs.**  The reduction is complete and every piece
of it is proved: the gluing of the two sides
(`…InvertibleTwistingRestriction.chartSource_sides`), the reading of the source factor as five
factors (`…InvertibleTwistingRestriction.chartSourceIso_hom_eq`, through
`AlgebraicGeometry.Space.trans_trans_hom` so that the elaborator matches `Iso.trans`
applications by their arguments and never reduces two `Iso.mk`s), and the three chases that
assemble them (`AlgebraicGeometry.Space.attachedSourceRightGlue_chase`,
`…attachedSourceRightRead_chase`, `…attachedSourceSquareLeft_chase`, each holding ONE comparison,
because two in one declaration exhaust the elaborator).  What is not proved is the FIRST of those
three, `…attachedSourceRightGlue_chase` at these morphisms: its `hbridge` identifies the last
five factors of the right-hand side of the coherence of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullback_sourceChain_eq`) with the right-hand side of the reading
of Stacks 03DX (2) along `c_{w ∘ τ}`
(`…InvertibleTwistingRestriction.chartSource_target_reading`), and those are two independently
elaborated spellings of one composite.  The fifth factor is shared outright
(`AlgebraicGeometry.Space.attachedSourceReadingComp`), so it needs no comparison at all; the
other four are closed by `with_reducible rfl` at the composite -- NOT factor by factor, which
fails, so a transport is distributed differently between the two -- and the **kernel** then times
out on them.  At default transparency the elaborator itself times out, and Lean's reduction
diagnostics say what on: it normalises the section `c_{w ∘ τ}` as a morphism of schemes,
unfolding `…InvertibleTwistingRestriction.chartSection` twenty thousand times and with it
`IsPullback.lift`, `RelativeProjPoints.pointEquivOver` and the colimits of the fibre.  The two
sides are identical in every explicit argument (as `pp.explicit` shows), the
difference is in an implicit one, and the two cures that worked for the bridge of
`…chartSource_sides` have been applied already: the twist is an `𝒪`-module on both sides, and the
represented algebraic space is spelled by its constructor on both sides.  The next spelling to
align is in those four factors -- the transports and the comparisons of Stacks 03LU of
`AlgebraicGeometry.Space.modulePullback_sourceChain_eq` against those of
`AlgebraicGeometry.Space.modulePullback_map_reading_comp`.  One lead, read off the instance
priorities: of the files those factors come from, only this one and
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistNatural` raise
`AlgebraicGeometry.Space.SmallEtale.instHasSheafify` and `…instWEqualsLocallyBijective` to
priority 5000, so a `Category` instance synthesised in
`…Spaces.Groupoids.EquivariantPullback` (`pullbackTransport_eq_eqToHom`, which the reading of the
right-hand side consumes) need not be the term synthesised here -- two derivations of one
instance are reducibly equal, which is what `with_reducible rfl` is closing, and comparing them
at default transparency is the sheafification the kernel is normalising.

Every step of the reduction of the square is stated in an arbitrary category (`AbstractChases`):
at the category of modules on an algebraic space, `simp only [Category.assoc]` and
`simp only [Functor.map_comp]` do not fire on composites whose ends are the modules attached to
quasi-coherent modules on the schemes of the site, because the two spellings
`SheafOfModules (representedStructureRingSheaf B S hS T)` and `Modules B S hS (yoneda.obj T) _`
of their type agree only after unfolding `AlgebraicGeometry.Space.smallEtaleRingedSite`, and
`reassoc_of%` and `Iso.trans_hom` fail there for the same reason.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

namespace AlgebraicGeometry.Space

section Canonical

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {V W L F F' P : AlgebraicSpaces B S hS}

/-- The inner half of `AlgebraicGeometry.Space.modulePullback_sourceChain_left_comp_compHom`: the
inverse comparison along `rc`, the comparison along `rτ`, the transports and the comparison for
the total composite contract to the comparison along `rτ` for `rc ≫ b'`. -/
theorem modulePullback_sourceChain_left_inner (rτ : V ⟶ W) (rc : W ⟶ F) (b' : F ⟶ P)
    {m q : V ⟶ F} (M : Modules.{u, u} B S hS P.1 P.2) (p₁ : rτ ≫ rc = m) (p₂ : m = q)
    (e : rτ ≫ rc ≫ b' = q ≫ b') :
    (modulePullback B S hS rτ).map (modulePullbackCompInv B S hS rc b' M) ≫
        modulePullbackCompHom B S hS rτ rc ((modulePullback B S hS b').obj M) ≫
        pullbackTransport ((modulePullback B S hS b').obj M) p₁ ≫
        pullbackTransport ((modulePullback B S hS b').obj M) p₂ ≫
        modulePullbackCompHom B S hS q b' M =
      modulePullbackCompHom B S hS rτ (rc ≫ b') M ≫ pullbackTransport M e := by
  subst p₂
  subst p₁
  have hrfl : ∀ {T X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)
      (k : T ⟶ X), pullbackTransport M (rfl : k = k) = 𝟙 _ := fun _ _ => rfl
  rw [hrfl, Category.id_comp, Category.id_comp,
    modulePullbackCompHom_comp_compHom rτ rc b' M,
    modulePullback_map_compInv_comp_map_compHom_assoc rτ rc b' M]

/-- The outer half of `AlgebraicGeometry.Space.modulePullback_sourceChain_left_comp_compHom`: the
inverse image of the transport along the factorisation, followed by the comparison along `rτ` for
`rc ≫ b'`, is the comparison along `rτ` for `A ≫ b`. -/
theorem modulePullback_sourceChain_left_outer (rτ : V ⟶ W) (A : W ⟶ L) (b : L ⟶ P) (rc : W ⟶ F)
    (b' : F ⟶ P) {q : V ⟶ F} (M : Modules.{u, u} B S hS P.1 P.2) (hab : A ≫ b = rc ≫ b')
    (e : rτ ≫ rc ≫ b' = q ≫ b') (eQ : rτ ≫ A ≫ b = q ≫ b') :
    (modulePullback B S hS rτ).map (pullbackTransport M hab) ≫
        modulePullbackCompHom B S hS rτ (rc ≫ b') M ≫ pullbackTransport M e =
      modulePullbackCompHom B S hS rτ (A ≫ b) M ≫ pullbackTransport M eQ := by
  rw [modulePullback_map_pullbackTransport_comp_compHom_assoc B S hS rτ hab M,
    pullbackTransport_comp M _ e eQ]

/-- The chain of comparisons of Stacks 03LU through the inverse image along `rc`, composed with
the comparison for the total composite, is the canonical comparison. -/
theorem modulePullback_sourceChain_left_comp_compHom (rτ : V ⟶ W) (A : W ⟶ L) (b : L ⟶ P)
    (rc : W ⟶ F) (b' : F ⟶ P) {m q : V ⟶ F} (M : Modules.{u, u} B S hS P.1 P.2)
    (hab : A ≫ b = rc ≫ b') (p₁ : rτ ≫ rc = m) (p₂ : m = q)
    (e : rτ ≫ rc ≫ b' = q ≫ b') (eQ : rτ ≫ A ≫ b = q ≫ b') :
    (modulePullback B S hS rτ).map (modulePullbackCompHom B S hS A b M) ≫
        (modulePullback B S hS rτ).map (pullbackTransport M hab) ≫
        (modulePullback B S hS rτ).map (modulePullbackCompInv B S hS rc b' M) ≫
        modulePullbackCompHom B S hS rτ rc ((modulePullback B S hS b').obj M) ≫
        pullbackTransport ((modulePullback B S hS b').obj M) p₁ ≫
        pullbackTransport ((modulePullback B S hS b').obj M) p₂ ≫
        modulePullbackCompHom B S hS q b' M =
      (modulePullback B S hS rτ).map (modulePullbackCompHom B S hS A b M) ≫
        modulePullbackCompHom B S hS rτ (A ≫ b) M ≫ pullbackTransport M eQ := by
  rw [modulePullback_sourceChain_left_inner rτ rc b' M p₁ p₂ e,
    modulePullback_sourceChain_left_outer rτ A b rc b' M hab e eQ]

/-- The chain of comparisons of Stacks 03LU through the inverse images along `rc₁` and `ry`,
composed with the comparison for the total composite, is the canonical comparison. -/
theorem modulePullback_sourceChain_right_comp_compHom (rτ : V ⟶ W) (A : W ⟶ L) (A₁ : V ⟶ L)
    (b : L ⟶ P) (b' : F ⟶ P) (rc₁ : V ⟶ F') (b'₁ : F' ⟶ P) (ry : F' ⟶ F) {q : V ⟶ F}
    (M : Modules.{u, u} B S hS P.1 P.2) (h : rτ ≫ A = A₁) (hab₁ : A₁ ≫ b = rc₁ ≫ b'₁)
    (hfy : ry ≫ b' = b'₁) (p₃ : rc₁ ≫ ry = q) (eQ : rτ ≫ A ≫ b = q ≫ b') :
    modulePullbackCompHom B S hS rτ A ((modulePullback B S hS b).obj M) ≫
        pullbackTransport ((modulePullback B S hS b).obj M) h ≫
        modulePullbackCompHom B S hS A₁ b M ≫
        pullbackTransport M hab₁ ≫
        modulePullbackCompInv B S hS rc₁ b'₁ M ≫
        (modulePullback B S hS rc₁).map (pullbackTransport M hfy.symm) ≫
        (modulePullback B S hS rc₁).map (modulePullbackCompInv B S hS ry b' M) ≫
        modulePullbackCompHom B S hS rc₁ ry ((modulePullback B S hS b').obj M) ≫
        pullbackTransport ((modulePullback B S hS b').obj M) p₃ ≫
        modulePullbackCompHom B S hS q b' M =
      (modulePullback B S hS rτ).map (modulePullbackCompHom B S hS A b M) ≫
        modulePullbackCompHom B S hS rτ (A ≫ b) M ≫ pullbackTransport M eQ := by
  have e₂ : rc₁ ≫ ry ≫ b' = q ≫ b' := by rw [← Category.assoc, p₃]
  have eR : A₁ ≫ b = q ≫ b' := by rw [hab₁, ← hfy, ← Category.assoc, p₃]
  have eQ₂ : (rτ ≫ A) ≫ b = q ≫ b' := (Category.assoc rτ A b).trans eQ
  rw [pullbackTransport_comp_compHom B S hS b' p₃ M,
    modulePullbackCompHom_assoc_transport B S hS rc₁ ry b' M _ e₂,
    modulePullback_map_compInv_comp_map_compHom_assoc rc₁ ry b' M,
    modulePullback_map_pullbackTransport_comp_compHom_assoc B S hS rc₁ hfy.symm M,
    modulePullbackCompInv_comp_compHom_assoc rc₁ b'₁ M,
    pullbackTransport_comp_pullbackTransport_assoc, pullbackTransport_comp M _ e₂ eR,
    pullbackTransport_comp_compHom_assoc B S hS b h M, pullbackTransport_comp M _ eR eQ₂,
    modulePullbackCompHom_assoc_transport B S hS rτ A b M eQ₂ eQ]

/-- **The coherence of Stacks 03LU behind the square of the source factor of the chart maps**,
at variables.  For `rτ ≫ A = A₁`, two factorisations `A ≫ b = rc ≫ b'` and `A₁ ≫ b = rc₁ ≫ b'₁`
of the two scheme points, `ry ≫ b' = b'₁` and `rτ ≫ rc = m = q = rc₁ ≫ ry`, the two composites
of the comparisons of Stacks 03LU and transports `rτ^*(A^*(b^*𝒯)) ⟶ q^*(b'^*𝒯)` agree: the one
through `rτ^*(rc^*(b'^*𝒯))` and the one through `A₁^*(b^*𝒯)` and `rc₁^*(ry^*(b'^*𝒯))`. -/
theorem modulePullback_sourceChain_eq (rτ : V ⟶ W) (A : W ⟶ L) (A₁ : V ⟶ L) (b : L ⟶ P)
    (rc : W ⟶ F) (b' : F ⟶ P) (rc₁ : V ⟶ F') (b'₁ : F' ⟶ P) (ry : F' ⟶ F) {m q : V ⟶ F}
    (M : Modules.{u, u} B S hS P.1 P.2) (h : rτ ≫ A = A₁) (hab : A ≫ b = rc ≫ b')
    (hab₁ : A₁ ≫ b = rc₁ ≫ b'₁) (hfy : ry ≫ b' = b'₁) (p₁ : rτ ≫ rc = m) (p₂ : m = q)
    (p₃ : rc₁ ≫ ry = q) :
    (modulePullback B S hS rτ).map (modulePullbackCompHom B S hS A b M) ≫
        (modulePullback B S hS rτ).map (pullbackTransport M hab) ≫
        (modulePullback B S hS rτ).map (modulePullbackCompInv B S hS rc b' M) ≫
        modulePullbackCompHom B S hS rτ rc ((modulePullback B S hS b').obj M) ≫
        pullbackTransport ((modulePullback B S hS b').obj M) p₁ ≫
        pullbackTransport ((modulePullback B S hS b').obj M) p₂ =
      modulePullbackCompHom B S hS rτ A ((modulePullback B S hS b).obj M) ≫
        pullbackTransport ((modulePullback B S hS b).obj M) h ≫
        modulePullbackCompHom B S hS A₁ b M ≫
        pullbackTransport M hab₁ ≫
        modulePullbackCompInv B S hS rc₁ b'₁ M ≫
        (modulePullback B S hS rc₁).map (pullbackTransport M hfy.symm) ≫
        (modulePullback B S hS rc₁).map (modulePullbackCompInv B S hS ry b' M) ≫
        modulePullbackCompHom B S hS rc₁ ry ((modulePullback B S hS b').obj M) ≫
        pullbackTransport ((modulePullback B S hS b').obj M) p₃ := by
  have e : rτ ≫ rc ≫ b' = q ≫ b' := by rw [← Category.assoc, p₁, p₂]
  have eQ : rτ ≫ A ≫ b = q ≫ b' := by rw [hab]; exact e
  have key := (modulePullback_sourceChain_left_comp_compHom rτ A b rc b' M hab p₁ p₂ e eQ).trans
    (modulePullback_sourceChain_right_comp_compHom rτ A A₁ b b' rc₁ b'₁ ry M h hab₁ hfy p₃
      eQ).symm
  have hcan := congrArg (· ≫ modulePullbackCompInv B S hS q b' M) key
  simp only [Category.assoc, modulePullbackCompHom_comp_compInv, Category.comp_id] at hcan
  exact hcan

/-- `AlgebraicGeometry.Space.modulePullback_sourceChain_eq` with a trailing morphism. -/
theorem modulePullback_sourceChain_eq_comp (rτ : V ⟶ W) (A : W ⟶ L) (A₁ : V ⟶ L) (b : L ⟶ P)
    (rc : W ⟶ F) (b' : F ⟶ P) (rc₁ : V ⟶ F') (b'₁ : F' ⟶ P) (ry : F' ⟶ F) {m q : V ⟶ F}
    (M : Modules.{u, u} B S hS P.1 P.2) (h : rτ ≫ A = A₁) (hab : A ≫ b = rc ≫ b')
    (hab₁ : A₁ ≫ b = rc₁ ≫ b'₁) (hfy : ry ≫ b' = b'₁) (p₁ : rτ ≫ rc = m) (p₂ : m = q)
    (p₃ : rc₁ ≫ ry = q) {K : Modules.{u, u} B S hS V.1 V.2}
    (k : (modulePullback B S hS q).obj ((modulePullback B S hS b').obj M) ⟶ K) :
    (modulePullback B S hS rτ).map (modulePullbackCompHom B S hS A b M) ≫
        (modulePullback B S hS rτ).map (pullbackTransport M hab) ≫
        (modulePullback B S hS rτ).map (modulePullbackCompInv B S hS rc b' M) ≫
        modulePullbackCompHom B S hS rτ rc ((modulePullback B S hS b').obj M) ≫
        pullbackTransport ((modulePullback B S hS b').obj M) p₁ ≫
        pullbackTransport ((modulePullback B S hS b').obj M) p₂ ≫ k =
      modulePullbackCompHom B S hS rτ A ((modulePullback B S hS b).obj M) ≫
        pullbackTransport ((modulePullback B S hS b).obj M) h ≫
        modulePullbackCompHom B S hS A₁ b M ≫
        pullbackTransport M hab₁ ≫
        modulePullbackCompInv B S hS rc₁ b'₁ M ≫
        (modulePullback B S hS rc₁).map (pullbackTransport M hfy.symm) ≫
        (modulePullback B S hS rc₁).map (modulePullbackCompInv B S hS ry b' M) ≫
        modulePullbackCompHom B S hS rc₁ ry ((modulePullback B S hS b').obj M) ≫
        pullbackTransport ((modulePullback B S hS b').obj M) p₃ ≫ k := by
  exact (reassoc_of% (modulePullback_sourceChain_eq rτ A A₁ b rc b' rc₁ b'₁ ry M h hab hab₁ hfy
    p₁ p₂ p₃)) k

end Canonical

section AbstractChases

variable {D : Type*} [Category D]

/-- The assembly of `AlgebraicGeometry.Space.modulePullback_map_attachedSource_reading_eq`, at
variables in an arbitrary category. -/
theorem sourceReading_chase {a b c d e f g h i j k n p : D} (A1 : a ⟶ b) (A2 : b ⟶ c)
    (A3 : c ⟶ d) (s : d ⟶ e) (cH : a ⟶ f) (t1 : f ⟶ g) (R : g ⟶ h) (P : h ⟶ i) (Q : i ⟶ d)
    (t2 : g ⟶ j) (R' : j ⟶ k) (P' : k ⟶ n) (Q' : n ⟶ i) (u : i ⟶ n) (v : n ⟶ p) (w : p ⟶ e)
    (tl : j ⟶ e) (H1 : A1 ≫ A2 ≫ A3 = cH ≫ t1 ≫ R ≫ P ≫ Q)
    (H2 : R ≫ P = t2 ≫ R' ≫ P' ≫ Q') (H3 : Q ≫ s = u ≫ v ≫ w) (H4 : Q' ≫ u = 𝟙 n)
    (Htl : tl = R' ≫ P' ≫ v ≫ w) :
    A1 ≫ A2 ≫ A3 ≫ s = cH ≫ t1 ≫ t2 ≫ tl := by
  have h1 : A1 ≫ A2 ≫ A3 ≫ s = (A1 ≫ A2 ≫ A3) ≫ s := by simp only [Category.assoc]
  rw [Htl, h1, H1]
  simp only [Category.assoc, H3]
  rw [← Category.assoc R P, H2]
  simp only [Category.assoc]
  rw [← Category.assoc Q' u, H4, Category.id_comp]

/-- The assembly of the target half of the square of the source factor, at variables: the
identification `E` is a transport followed by an isomorphism `A` whose underlying morphism is a
four-factor composite, and its inverse image along `F`, read through `ρ`, contracts. -/
theorem targetReading_chase {C : Type*} [Category C] (F : C ⥤ D) {a' b' c' d' e' f' : C}
    (hobj : a' = b') (n0 : a' ⟶ b') (hn0 : n0 = eqToHom hobj) (m1 : b' ⟶ c') (m2 : c' ⟶ d')
    (m3 : d' ⟶ e') (m4 : e' ⟶ f') (E : a' ≅ f') (A : b' ≅ f') (hE : E = eqToIso hobj ≪≫ A)
    (hA : A.hom = m1 ≫ m2 ≫ m3 ≫ m4) {g h i j k l : D} (ρ : F.obj f' ⟶ g)
    (ρ' : F.obj e' ⟶ h) (w : h ⟶ g) (cH : F.obj c' ⟶ i) (t : i ⟶ j) (R' : j ⟶ k) (P' : k ⟶ l)
    (Q' : l ⟶ h) (tl : j ⟶ g) (Hnat : F.map m4 ≫ ρ = ρ' ≫ w)
    (Hread : F.map m2 ≫ F.map m3 ≫ ρ' = cH ≫ t ≫ R' ≫ P' ≫ Q')
    (Htl : tl = R' ≫ P' ≫ Q' ≫ w) :
    F.map E.hom ≫ ρ = F.map n0 ≫ F.map m1 ≫ cH ≫ t ≫ tl := by
  have hEh : E.hom = n0 ≫ m1 ≫ m2 ≫ m3 ≫ m4 := by
    rw [hE, Iso.trans_hom, eqToIso.hom, hA, hn0]
  rw [hEh, Htl]
  simp only [Functor.map_comp, Category.assoc, Hnat]
  rw [reassoc_of% Hread]

/-- The left-hand side of the square of the source factor, assembled at variables. -/
theorem leftSquare_chase {C : Type*} [Category C] (F : C ⥤ D) {a' b' c' d' e' f' : C}
    (K1 : a' ⟶ b') (K2 : b' ⟶ c') (K3 : c' ⟶ d') (K4 : d' ⟶ e') (K5 : e' ⟶ f') (Ξ : a' ⟶ f')
    (hΞ : Ξ = K1 ≫ K2 ≫ K3 ≫ K4 ≫ K5) {g h i j k : D} (S1 : F.obj f' ⟶ g) (S2 : g ⟶ h)
    (β : F.obj f' ⟶ h) (hβ : β = S1 ≫ S2) (cH : F.obj d' ⟶ i) (T1 : i ⟶ j) (T2 : j ⟶ k)
    (tl : k ⟶ h) (H : F.map K4 ≫ F.map K5 ≫ S1 ≫ S2 = cH ≫ T1 ≫ T2 ≫ tl) :
    F.map Ξ ≫ β = F.map K1 ≫ F.map K2 ≫ F.map K3 ≫ cH ≫ T1 ≫ T2 ≫ tl := by
  rw [hΞ, hβ]
  simp only [Functor.map_comp, Category.assoc, H]

/-- The right-hand side of the square of the source factor, assembled at variables. -/
theorem rightSquare_chase {a b c d e f g h i j k l : D} (C0 : a ⟶ b) (Tr : b ⟶ c) (J1 : c ⟶ d)
    (J2 : d ⟶ e) (J3 : e ⟶ f) (J4 : f ⟶ g) (J5 : g ⟶ h) (Ξ' : c ⟶ h)
    (hΞ' : Ξ' = J1 ≫ J2 ≫ J3 ≫ J4 ≫ J5) (X1 : f ⟶ i) (X2 : i ⟶ j) (X3 : j ⟶ k) (X4 : k ⟶ l)
    (tl : l ⟶ h) (H : J4 ≫ J5 = X1 ≫ X2 ≫ X3 ≫ X4 ≫ tl) :
    (C0 ≫ Tr) ≫ Ξ' = C0 ≫ Tr ≫ J1 ≫ J2 ≫ J3 ≫ X1 ≫ X2 ≫ X3 ≫ X4 ≫ tl := by
  rw [hΞ']
  simp only [Category.assoc, H]

/-- The underlying morphism of a three-fold composite of isomorphisms, at variables: for
`I = A ≪≫ B ≪≫ C`, `I.hom = A.hom ≫ B.hom ≫ C.hom`.

`I` is an argument of its own and the three isomorphisms are implicit, so that an instance of this
lemma at a DEFINITION which is a three-fold composite -- `…chartSourceIso`,
or `…InvertibleTwistingRestriction.modulePullbackCompTransportIso` -- assigns the three and
compares nothing: both sides of `hI` are `Iso.trans` applications and are matched by their
arguments.  Stated the other way round, as `((A ≪≫ B ≪≫ C).hom = …)`, the elaborator instead
reduces the two sides to the `hom` and `inv` fields of two `Iso.mk`s -- composites at the
category of modules on an algebraic space -- and normalising those makes it unfold the section
`c_w` as a morphism of schemes, which is an `isDefEq` timeout. -/
theorem trans_trans_hom {x0 x1 x2 x3 : D} {A : x0 ≅ x1} {B : x1 ≅ x2} {C' : x2 ≅ x3}
    (I : x0 ≅ x3) (hI : I = A ≪≫ B ≪≫ C') : I.hom = A.hom ≫ B.hom ≫ C'.hom := by
  rw [hI]
  simp only [Iso.trans_hom]

/-- A five-factor composite read off a three-factor composite whose first factor is itself a
three-factor composite, which is how `…InvertibleTwistingRestriction.chartSourceIso` is built. -/
theorem comp_assoc_five_of_trans {x0 x1 x2 x3 x4 x5 : D} {a1 : x0 ⟶ x1} {a2 : x1 ⟶ x2}
    {a3 : x2 ⟶ x3} {a4 : x3 ⟶ x4} {a5 : x4 ⟶ x5} {c : x0 ⟶ x3} (Ξ : x0 ⟶ x5)
    (hΞ : Ξ = c ≫ a4 ≫ a5) (hc : c = a1 ≫ a2 ≫ a3) :
    Ξ = a1 ≫ a2 ≫ a3 ≫ a4 ≫ a5 := by
  rw [hΞ, hc]
  simp only [Category.assoc]

/-- Two five-factor composites agree when their factors do, at variables.

The five comparisons are then made one at a time, each at a single morphism.  At the category of
modules on an algebraic space that is the difference between a step that works and one that does
not: comparing the two composites directly, a single factor that does not match syntactically
makes the elaborator unfold the composition itself -- through the `Category` instance of a
category of sheaves of modules -- and it times out at `whnf`. -/
theorem comp_congr_five {x0 x1 x2 x3 x4 x5 : D} {a1 b1 : x0 ⟶ x1} {a2 b2 : x1 ⟶ x2}
    {a3 b3 : x2 ⟶ x3} {a4 b4 : x3 ⟶ x4} {a5 b5 : x4 ⟶ x5} (h1 : a1 = b1) (h2 : a2 = b2)
    (h3 : a3 = b3) (h4 : a4 = b4) (h5 : a5 = b5) :
    a1 ≫ a2 ≫ a3 ≫ a4 ≫ a5 = b1 ≫ b2 ≫ b3 ≫ b4 ≫ b5 := by
  rw [h1, h2, h3, h4, h5]

/-- **The two sides of the square, glued along the coherence of Stacks 03LU**, at variables: the
contraction `HL` of the left-hand side, the coherence `HC`, and the identification `hbridge` of
the three middle factors as the two of them spell those factors, composed with the reading `tl`
of the right-hand side.

Everything the gluing is made of -- the two categories, the functor and all of the factors -- is
implicit, and the hypotheses are ordered so that each *determines* as much as possible and
*compares* as little as possible: `HL` comes first and determines the two categories, the functor
and `cH`, `T1`, `T2`, `tl`, `K4`, `K5`, `S1`, `S2`; `HC` then determines `K1`, `K2`, `K3`, its own
`cH'`, `T1'`, `T2'` and the whole right-hand chain, comparing nothing but the two ends `F.obj p3`
and `d3` of the three factors it shares with `HL`.  The one comparison the gluing really needs is
`hbridge`, and it stands alone: an equation between two three-factor composites, nothing nested
inside a ten-factor pattern, so that the transparency at which it is attempted can be chosen.

Each of those choices is load-bearing at the category of modules on an algebraic space.  Naming
the functor explicitly fixes the ambient category -- and with it the `Category` instance carried
by every `≫` -- in the spelling `Modules B S hS _ _`, while the contraction of the left-hand side
is stated at the spelling `SheafOfModules (representedStructureRingSheaf B S hS T)` of the same
category, so `HL` alone then costs eight comparisons that each unfold
`AlgebraicGeometry.Space.smallEtaleRingedSite`.  With `tl` inside `HC`, its codomain -- an
attached module, so of the second spelling -- is forced into the `Modules B S hS _ _` slot that
`AlgebraicGeometry.Space.modulePullback_sourceChain_eq_comp` declares for it, which is that same
unfolding at every one of the seventeen `≫` of that hypothesis.  And with `HC` sharing `cH`,
`T1`, `T2` with `HL` rather than bridging to them, the elaborator compares
`AlgebraicGeometry.Space.modulePullbackCompHom` against a second spelling of itself while it is
buried in a six-factor pattern, which it answers by unfolding
`AlgebraicGeometry.Space.modulePullbackCompIso` -- that is, the uniqueness of a left adjoint --
until the recursion depth runs out.  Each of the three is fatal on its own. -/
theorem attachedSourceSides_chase {C : Type*} [Category C] {F : C ⥤ D}
    {p0 p1 p2 p3 p4 p5 : C} {g0 m0 d1 d2 d3 : D}
    {cH : F.obj p3 ⟶ d1} {T1 : d1 ⟶ d2} {T2 : d2 ⟶ d3} {tl : d3 ⟶ m0}
    {K4 : p3 ⟶ p4} {K5 : p4 ⟶ p5} {S1 : F.obj p5 ⟶ g0} {S2 : g0 ⟶ m0}
    (HL : F.map K4 ≫ F.map K5 ≫ S1 ≫ S2 = cH ≫ T1 ≫ T2 ≫ tl)
    {K1 : p0 ⟶ p1} {K2 : p1 ⟶ p2} {K3 : p2 ⟶ p3}
    {e1 e2 : D} {cH' : F.obj p3 ⟶ e1} {T1' : e1 ⟶ e2} {T2' : e2 ⟶ d3}
    {q0 q1 r1 r2 r3 r4 r5 r6 : D} {C0 : F.obj p0 ⟶ q0} {Tr : q0 ⟶ q1} {J1 : q1 ⟶ r1}
    {J2 : r1 ⟶ r2} {J3 : r2 ⟶ r3} {X1 : r3 ⟶ r4} {X2 : r4 ⟶ r5} {X3 : r5 ⟶ r6} {X4 : r6 ⟶ d3}
    (HC : F.map K1 ≫ F.map K2 ≫ F.map K3 ≫ cH' ≫ T1' ≫ T2' =
      C0 ≫ Tr ≫ J1 ≫ J2 ≫ J3 ≫ X1 ≫ X2 ≫ X3 ≫ X4)
    (hbridge : cH ≫ T1 ≫ T2 = cH' ≫ T1' ≫ T2') :
    F.map K1 ≫ F.map K2 ≫ F.map K3 ≫ F.map K4 ≫ F.map K5 ≫ S1 ≫ S2 =
      C0 ≫ Tr ≫ J1 ≫ J2 ≫ J3 ≫ X1 ≫ X2 ≫ X3 ≫ X4 ≫ tl := by
  have hc := congrArg (· ≫ tl) HC
  simp only [Category.assoc] at hc
  rw [HL, reassoc_of% hbridge]
  exact hc

/-- **The right-hand side of the square of the source factor, glued to its reading**, at
variables: the gluing `HS` of the two sides of the square and the reading `HR` of its right-hand
side give the left-hand side of the square as the right-hand chain with the two factors of `HR`
in place of its last five.

`HR` carries its OWN four factors and trailing reading, and the comparison with the five factors
`HS` ends in stands alone as `hbridge`: with `HR` stated directly at `X1`, `X2`, `X3`, `X4`,
`tl`, the elaborator has five single morphisms to compare while the ten-factor pattern of `HR` is
still being matched, and it times out at `whnf`.  The reading of the source factor at `w ∘ τ` is
a declaration further on for the same reason -- it is one comparison more than this one has
budget for. -/
theorem attachedSourceRightGlue_chase {C : Type*} [Category C] {F : C ⥤ D}
    {p0 p1 p2 p3 p4 p5 : C} {g0 m0 d3 : D}
    {K1 : p0 ⟶ p1} {K2 : p1 ⟶ p2} {K3 : p2 ⟶ p3} {K4 : p3 ⟶ p4} {K5 : p4 ⟶ p5}
    {S1 : F.obj p5 ⟶ g0} {S2 : g0 ⟶ m0} {tl : d3 ⟶ m0}
    {q0 q1 r1 r2 r3 r4 r5 r6 : D} {C0 : F.obj p0 ⟶ q0} {Tr : q0 ⟶ q1} {J1 : q1 ⟶ r1}
    {J2 : r1 ⟶ r2} {J3 : r2 ⟶ r3} {X1 : r3 ⟶ r4} {X2 : r4 ⟶ r5} {X3 : r5 ⟶ r6} {X4 : r6 ⟶ d3}
    (HS : F.map K1 ≫ F.map K2 ≫ F.map K3 ≫ F.map K4 ≫ F.map K5 ≫ S1 ≫ S2 =
      C0 ≫ Tr ≫ J1 ≫ J2 ≫ J3 ≫ X1 ≫ X2 ≫ X3 ≫ X4 ≫ tl)
    {s1 : D} {J4 : r3 ⟶ s1} {J5 : s1 ⟶ m0}
    {w1 w2 w3 w4 : D} {Y1 : r3 ⟶ w1} {Y2 : w1 ⟶ w2} {Y3 : w2 ⟶ w3} {Y4 : w3 ⟶ w4}
    {Y5 : w4 ⟶ m0}
    (HR : J4 ≫ J5 = Y1 ≫ Y2 ≫ Y3 ≫ Y4 ≫ Y5)
    (hbridge : Y1 ≫ Y2 ≫ Y3 ≫ Y4 ≫ Y5 = X1 ≫ X2 ≫ X3 ≫ X4 ≫ tl) :
    F.map K1 ≫ F.map K2 ≫ F.map K3 ≫ F.map K4 ≫ F.map K5 ≫ S1 ≫ S2 =
      C0 ≫ Tr ≫ J1 ≫ J2 ≫ J3 ≫ J4 ≫ J5 := by
  rw [HS, HR.trans hbridge]

/-- **The right-hand half of the square of the source factor**, at variables: the glued
right-hand side `H`, read through the reading `hΞ'` of the source factor at `w ∘ τ`, is the
right-hand side of the square.

The left-hand side `lhs` of `H` is a single morphism, so that this step compares nothing about
it, and the reading carries its own five factors with the comparison against the factors of `H`
standing alone as `hΞ'bridge`. -/
theorem attachedSourceRightRead_chase {a m0 q0 q1 r1 r2 r3 s1 : D} {lhs : a ⟶ m0}
    {C0 : a ⟶ q0} {Tr : q0 ⟶ q1} {J1 : q1 ⟶ r1} {J2 : r1 ⟶ r2} {J3 : r2 ⟶ r3}
    {J4 : r3 ⟶ s1} {J5 : s1 ⟶ m0}
    (H : lhs = C0 ≫ Tr ≫ J1 ≫ J2 ≫ J3 ≫ J4 ≫ J5)
    {v1 v2 v3 v4 : D} {V1 : q1 ⟶ v1} {V2 : v1 ⟶ v2} {V3 : v2 ⟶ v3} {V4 : v3 ⟶ v4}
    {V5 : v4 ⟶ m0}
    (Ξ' : q1 ⟶ m0) (hΞ' : Ξ' = V1 ≫ V2 ≫ V3 ≫ V4 ≫ V5)
    (hΞ'bridge : V1 ≫ V2 ≫ V3 ≫ V4 ≫ V5 = J1 ≫ J2 ≫ J3 ≫ J4 ≫ J5) :
    lhs = (C0 ≫ Tr) ≫ Ξ' := by
  rw [H, hΞ'.trans hΞ'bridge]
  simp only [Category.assoc]

/-- **The left-hand half of the square of the source factor**, at variables: the right-hand half
`H`, read through the reading `hΞ` of the source factor at `w` and the reading `hβ` of the module
attached to the comparison `σ` of the two pullbacks, is the square.

The right-hand side `R` of `H` is a single morphism, so that this half compares nothing about it;
and as in the right-hand half, the reading `hΞ` carries its own five factors and the comparison
with the factors `H` fixes stands alone as `hΞbridge`. -/
theorem attachedSourceSquareLeft_chase {C : Type*} [Category C] {F : C ⥤ D}
    {p0 p1 p2 p3 p4 p5 : C} {g0 m0 : D}
    {K1 : p0 ⟶ p1} {K2 : p1 ⟶ p2} {K3 : p2 ⟶ p3} {K4 : p3 ⟶ p4} {K5 : p4 ⟶ p5}
    {S1 : F.obj p5 ⟶ g0} {S2 : g0 ⟶ m0} {R : F.obj p0 ⟶ m0}
    (H : F.map K1 ≫ F.map K2 ≫ F.map K3 ≫ F.map K4 ≫ F.map K5 ≫ S1 ≫ S2 = R)
    {z1 z2 z3 z4 : C} {Z1 : p0 ⟶ z1} {Z2 : z1 ⟶ z2} {Z3 : z2 ⟶ z3} {Z4 : z3 ⟶ z4}
    {Z5 : z4 ⟶ p5}
    (Ξ : p0 ⟶ p5) (hΞ : Ξ = Z1 ≫ Z2 ≫ Z3 ≫ Z4 ≫ Z5)
    (hΞbridge : Z1 ≫ Z2 ≫ Z3 ≫ Z4 ≫ Z5 = K1 ≫ K2 ≫ K3 ≫ K4 ≫ K5)
    (β : F.obj p5 ⟶ m0) (hβ : β = S1 ≫ S2) :
    F.map Ξ ≫ β = R := by
  rw [hΞ.trans hΞbridge, hβ]
  simp only [Functor.map_comp, Category.assoc]
  exact H

end AbstractChases

section Bridge

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Tt Tt' Ff Ff' : BigFppfOver B S hS} {P L : AlgebraicSpaces B S hS}

/-- The module attached to the comparison `σ` of the two pullbacks, preceded by the module
attached to the inverse contraction along `τ` and `c`. -/
theorem attachedSourceSigma_eq (τ : Tt' ⟶ Tt) (c : Tt ⟶ Ff) (c₁ : Tt' ⟶ Ff') (y : Ff' ⟶ Ff)
    (hwc : τ ≫ c = c₁ ≫ y)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff).ringCatSheaf).FullSubcategory}
    {N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff').ringCatSheaf).FullSubcategory}
    (cmp : quasicoherentPullbackObj B S hS y N ⟶ N')
    (σ : quasicoherentPullbackObj B S hS τ (quasicoherentPullbackObj B S hS c N) ⟶
      quasicoherentPullbackObj B S hS c₁ N')
    (hσ : σ = (quasicoherentPullbackCompIso B S hS τ c N).hom ≫
      quasicoherentPullbackEqToHom B S hS hwc N ≫
        (quasicoherentPullbackCompIso B S hS c₁ y N).inv ≫
          quasicoherentPullbackMap B S hS c₁ cmp) :
    ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.map
          (quasicoherentPullbackCompIso B S hS τ c N).inv).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.map σ).hom =
      ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.map
          (quasicoherentPullbackEqToHom B S hS hwc N)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.map
            (quasicoherentPullbackCompIso B S hS c₁ y N).inv).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.map
            (quasicoherentPullbackMap B S hS c₁ cmp)).hom := by
  have hσ' : (quasicoherentPullbackCompIso B S hS τ c N).inv ≫ σ =
      quasicoherentPullbackEqToHom B S hS hwc N ≫
        (quasicoherentPullbackCompIso B S hS c₁ y N).inv ≫
          quasicoherentPullbackMap B S hS c₁ cmp := by
    rw [hσ, Iso.inv_hom_id_assoc]
  have hc := congrArg
    (fun k => ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.map k).hom) hσ'
  simpa only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using hc

/-- The two transports of the pullbacks along `τ ≫ c = c₁ ≫ y`, read on the attached modules,
cancel. -/
theorem attachedSourceEqToHom_cancel (τ : Tt' ⟶ Tt) (c : Tt ⟶ Ff) (c₁ : Tt' ⟶ Ff') (y : Ff' ⟶ Ff)
    (hwc : τ ≫ c = c₁ ≫ y)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff).ringCatSheaf).FullSubcategory} :
    ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.map
          (quasicoherentPullbackEqToHom B S hS hwc.symm N)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.map
          (quasicoherentPullbackEqToHom B S hS hwc N)).hom = 𝟙 _ := by
  have hid : quasicoherentPullbackEqToHom B S hS hwc.symm N ≫
      quasicoherentPullbackEqToHom B S hS hwc N = 𝟙 _ := by
    simp only [quasicoherentPullbackEqToHom, eqToHom_trans, eqToHom_refl]
  rw [functor_map_hom_comp_map_hom, hid, functor_map_id_hom]

/-- **The reading of `𝒯` along `c₁ ≫ y`**: the inverse image along `c₁ ≫ y` of the
identification `E₀ : b'^*𝒯 ≅ N^a`, read through `(c₁ ≫ y)^*(N^a) ≅ ((c₁ ≫ y)^*N)^a`, the inverse
comparison of Stacks 03LU for `c₁` and `y`, and the module attached to `cmp : y^*N ≅ N'`.

This is the trailing factor shared by the readings of the two sides of the square
(`AlgebraicGeometry.Space.modulePullback_map_attachedSource_reading_eq` and
`…_target_reading_eq`), and it has a NAME because the two must spell it the same way: each
stated with its own `tl` and `htl = rfl`, the two readings produce two independently elaborated
copies of this composite, and gluing them asks the kernel for a defeq that it answers by
unfolding `AlgebraicGeometry.Space.modulePullbackCompIso` -- the uniqueness of a left adjoint. -/
def attachedSourceReadingComp (c₁ : Tt' ⟶ Ff') (y : Ff' ⟶ Ff)
    (b' : (⟨yoneda.obj Ff, isAlgebraicSpace_yoneda B S hS Ff⟩ : AlgebraicSpaces B S hS) ⟶ P)
    (Tm : Modules.{u, u} B S hS P.1 P.2)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff).ringCatSheaf).FullSubcategory}
    {N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff').ringCatSheaf).FullSubcategory}
    (E₀ : (modulePullback B S hS b').obj Tm ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Ff).functor.obj N).obj)
    (cmp : quasicoherentPullbackObj B S hS y N ≅ N') :
    (modulePullback B S hS (representedSpaceMap B S hS (c₁ ≫ y))).obj
        ((modulePullback B S hS b').obj Tm) ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.obj
        (quasicoherentPullbackObj B S hS c₁ N')).obj :=
  (modulePullback B S hS (representedSpaceMap B S hS (c₁ ≫ y))).map E₀.hom ≫
    (modulePullbackRepresentedQuasicoherentIso B S hS (c₁ ≫ y) N).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.map
          (quasicoherentPullbackCompIso B S hS c₁ y N).inv).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.map
          (quasicoherentPullbackMap B S hS c₁ cmp.hom)).hom

/-- **The reading of `E₀'` along `c₁`** is the inverse image along `c₁` of the transfer of `E₀`
along `y`, the comparison of Stacks 03LU for `c₁` and `y`, and the reading `tl` of `E₀` along
`c₁ ≫ y`.

The module is an `𝒪`-module `Tm` on `P`, not the quasi-coherent object it underlies: see
`AlgebraicGeometry.Space.attachedModuleIsoPullback_hom` for why the quasi-coherent object makes
this statement unusable, even though quasi-coherence is not used. -/
theorem modulePullback_map_attachedSource_target_reading_eq (c₁ : Tt' ⟶ Ff') (y : Ff' ⟶ Ff)
    (b' : (⟨yoneda.obj Ff, isAlgebraicSpace_yoneda B S hS Ff⟩ : AlgebraicSpaces B S hS) ⟶ P)
    (b'₁ : (⟨yoneda.obj Ff', isAlgebraicSpace_yoneda B S hS Ff'⟩ : AlgebraicSpaces B S hS) ⟶ P)
    (hfy : representedSpaceMap B S hS y ≫ b' = b'₁)
    (Tm : Modules.{u, u} B S hS P.1 P.2)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff).ringCatSheaf).FullSubcategory}
    {N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff').ringCatSheaf).FullSubcategory}
    (E₀ : (modulePullback B S hS b').obj Tm ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Ff).functor.obj N).obj)
    (E₀' : (modulePullback B S hS b'₁).obj Tm ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Ff').functor.obj N').obj)
    (cmp : quasicoherentPullbackObj B S hS y N ≅ N')
    (hE : E₀' = eqToIso (congrArg
        (fun k : (⟨yoneda.obj Ff', isAlgebraicSpace_yoneda B S hS Ff'⟩ :
            AlgebraicSpaces B S hS) ⟶ P =>
          (modulePullback B S hS k).obj Tm) hfy.symm) ≪≫
      attachedModuleIsoPullback Tm b' y E₀ cmp)
    (tl : (modulePullback B S hS (representedSpaceMap B S hS (c₁ ≫ y))).obj
        ((modulePullback B S hS b').obj Tm) ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.obj
        (quasicoherentPullbackObj B S hS c₁ N')).obj)
    (htl : tl = attachedSourceReadingComp c₁ y b' Tm E₀ cmp) :
    type_of% (targetReading_chase (modulePullback B S hS (representedSpaceMap B S hS c₁)) _ _
      (pullbackTransport_eq_eqToHom Tm hfy.symm) _ _ _ _ _ _ hE
      (attachedModuleIsoPullback_hom (N := N) (N' := N') (y := y) (cmp := cmp)
        (Tmo := Tm) (hWc := b') (E₀ := E₀)) _ _ _ _ _ _ _ _ _
      (modulePullbackRepresentedQuasicoherentIso_naturality B S hS c₁ cmp.hom)
      (modulePullback_map_reading_comp Tm c₁ y b' E₀.hom) htl) :=
  targetReading_chase (modulePullback B S hS (representedSpaceMap B S hS c₁)) _ _
    (pullbackTransport_eq_eqToHom Tm hfy.symm) _ _ _ _ _ _ hE
    (attachedModuleIsoPullback_hom (N := N) (N' := N') (y := y) (cmp := cmp)
      (Tmo := Tm) (hWc := b') (E₀ := E₀)) _ _ _ _ _ _ _ _ _
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS c₁ cmp.hom)
    (modulePullback_map_reading_comp Tm c₁ y b' E₀.hom) htl

/-- **The reading of `E₀` along `c`, pulled back along `τ` and composed with the module attached
to the comparison `σ` of the two pullbacks**, is the comparison of Stacks 03LU for `τ` and `c`,
the transports along `τ ≫ c = c₁ ≫ y` and the reading `tl` of `E₀` along `c₁ ≫ y`.

The statement is the instance of `AlgebraicGeometry.Space.sourceReading_chase` (`type_of%`). -/
theorem modulePullback_map_attachedSource_reading_eq (τ : Tt' ⟶ Tt) (c : Tt ⟶ Ff) (c₁ : Tt' ⟶ Ff')
    (y : Ff' ⟶ Ff) (hwc : τ ≫ c = c₁ ≫ y)
    (b' : (⟨yoneda.obj Ff, isAlgebraicSpace_yoneda B S hS Ff⟩ : AlgebraicSpaces B S hS) ⟶ P)
    (Tm : Modules.{u, u} B S hS P.1 P.2)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff).ringCatSheaf).FullSubcategory}
    {N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Ff').ringCatSheaf).FullSubcategory}
    (E₀ : (modulePullback B S hS b').obj Tm ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Ff).functor.obj N).obj)
    (cmp : quasicoherentPullbackObj B S hS y N ≅ N')
    (σ : quasicoherentPullbackObj B S hS τ (quasicoherentPullbackObj B S hS c N) ⟶
      quasicoherentPullbackObj B S hS c₁ N')
    (hσ : σ = (quasicoherentPullbackCompIso B S hS τ c N).hom ≫
      quasicoherentPullbackEqToHom B S hS hwc N ≫
        (quasicoherentPullbackCompIso B S hS c₁ y N).inv ≫
          quasicoherentPullbackMap B S hS c₁ cmp.hom)
    (tl : (modulePullback B S hS (representedSpaceMap B S hS (c₁ ≫ y))).obj
        ((modulePullback B S hS b').obj Tm) ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS Tt').functor.obj
        (quasicoherentPullbackObj B S hS c₁ N')).obj)
    (htl : tl = attachedSourceReadingComp c₁ y b' Tm E₀ cmp) :
    type_of% (sourceReading_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (modulePullback_map_reading_comp Tm τ c b' E₀.hom)
      (reading_eq_of_eq Tm hwc b' E₀.hom)
      (attachedSourceSigma_eq τ c c₁ y hwc cmp.hom σ hσ)
      (attachedSourceEqToHom_cancel τ c c₁ y hwc (N := N)) htl) :=
  sourceReading_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (modulePullback_map_reading_comp Tm τ c b' E₀.hom)
    (reading_eq_of_eq Tm hwc b' E₀.hom)
    (attachedSourceSigma_eq τ c c₁ y hwc cmp.hom σ hσ)
    (attachedSourceEqToHom_cancel τ c c₁ y hwc (N := N)) htl

end Bridge

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)

/-- `…RelativeProjSituation.fibreToSpaceTwistModuleIso_comp` for a scheme point `v` equal to
`f ∘ τ`: the base change identification of Stacks 084D at `v` is the transport along
`(T' ×_X P ⟶ P) = y ≫ (T ×_X P ⟶ P)` followed by the transfer along `y` of the identification
at `f`. -/
theorem fibreToSpaceTwistModuleIso_comp_of_eq (f : yoneda.obj T ⟶ s.space.1)
    (v : yoneda.obj T' ⟶ s.space.1) (hv : yoneda.map τ ≫ f = v)
    (y : s.relativeProjPoints.fibre T' v ⟶ s.relativeProjPoints.fibre T f)
    (hy : s.relativeProjPoints.LiesOver y τ) (n : ℤ)
    (hfy : representedSpaceMap s.site s.base s.containsBase y ≫ s.fibreToSpaceHom T f =
      s.fibreToSpaceHom T' v) :
    s.fibreToSpaceTwistModuleIso Px T' v n =
      eqToIso (congrArg (fun k : (⟨yoneda.obj (s.relativeProjPoints.fibre T' v),
            isAlgebraicSpace_yoneda s.site s.base s.containsBase _⟩ :
            AlgebraicSpaces s.site s.base s.containsBase) ⟶
              ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ =>
          (modulePullback s.site s.base s.containsBase k).obj (s.twistModule Px n).obj)
          hfy.symm) ≪≫
        attachedModuleIsoPullback
          (X := ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩)
          (s.twistModule Px n).obj (s.fibreToSpaceHom T f) y
          (s.fibreToSpaceTwistModuleIso Px T f n) (s.twistPieceComparison τ hv y hy n) := by
  subst hv
  exact s.fibreToSpaceTwistModuleIso_comp Px τ f hy n

end AlgebraicGeometry.Space.RelativeProjSituation

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {T T' : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase} (τ : T' ⟶ T)
  {w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj}
  {w' : yoneda.obj T' ⟶ (locusSpaceOfUnitalHom s f L ψ).obj} (hw : yoneda.map τ ≫ w = w')

/-- The factorisation `r_{ℒ,ψ} ∘ w = (T ×_Y Proj_Y(𝒜) ⟶ Proj_Y(𝒜)) ∘ c_w` of the chart maps, as
morphisms of algebraic spaces. -/
theorem pointHom_comp_invertibleSpaceMorphism
    {V : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
    (v : yoneda.obj V ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) :
    pointHom (X := (ofUnitalHom s f L ψ).locusSpace X.property) v ≫
        (ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property =
      representedSpaceMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint v) (locusOpen_locusPoint v)) ≫
        s.fibreToSpaceHom V (locusPoint v ≫ f.hom) :=
  ObjectProperty.hom_ext _
    ((comp_invertibleMorphism v (locusOpen_locusPoint v)).trans
      ((ofUnitalHom s f L ψ).map_chartSection_fibreToSpace _ _).symm)

include hw in
/-- The scheme points of `Y` under the scheme points `w` and `w ∘ τ` of `U(ψ)`:
`(f ∘ w) ∘ τ = f ∘ (w ∘ τ)`. -/
theorem map_comp_locusPoint_comp :
    yoneda.map τ ≫ locusPoint w ≫ f.hom = locusPoint w' ≫ f.hom := by
  rw [← Category.assoc, map_comp_locusPoint τ hw]

include hw in
/-- **The sections `c_w` of the scheme points of `U(ψ)` are natural**: for a morphism
`y : T' ×_Y Proj_Y(𝒜) ⟶ T ×_Y Proj_Y(𝒜)` of base changes lying over `τ`,
`c_w ∘ τ = y ∘ c_{w ∘ τ}`. -/
theorem comp_chartSection_locusPoint
    (y : s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
      s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))
    (hy : s.relativeProjPoints.LiesOver y τ) :
    τ ≫ (ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w) =
      (ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w') ≫ y :=
  (chartSection_comp_of_liesOver (ofUnitalHom s f L ψ) τ (locusPoint w)
    (locusOpen_locusPoint w) (locusPoint w') (locusOpen_locusPoint w')
    (map_comp_locusPoint τ hw).symm y hy).symm

include hw in
/-- **The left-hand side of the square of the source factor**: the reading of the base change
identification of Stacks 084D along the section `c_w`, pulled back along `τ` and composed with
the module attached to the comparison `σ` of the two pullbacks.

The statement is the instance of
`AlgebraicGeometry.Space.modulePullback_map_attachedSource_reading_eq` (`type_of%`).  Its site is
named: left to `τ` it would be inferred as `s.shrink.site`, in which spelling nothing else in the
square is stated, and comparing the two spellings unfolds
`AlgebraicGeometry.Space.RelativeProjSituation.shrink` inside every subterm of a composite at the
category of modules on an algebraic space. -/
theorem chartSource_reading (d : ℤ)
    (y : s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
      s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))
    (hy : s.relativeProjPoints.LiesOver y τ) :
    type_of% (modulePullback_map_attachedSource_reading_eq
      (B := s.site) (S := s.base) (hS := s.containsBase) τ
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')) y
      (comp_chartSection_locusPoint τ hw y hy) (s.fibreToSpaceHom T (locusPoint w ≫ f.hom))
      (s.twistModule Px d).obj (s.fibreToSpaceTwistModuleIso Px T (locusPoint w ≫ f.hom) d)
      (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d) _ rfl _ rfl) :=
  modulePullback_map_attachedSource_reading_eq
    (B := s.site) (S := s.base) (hS := s.containsBase) τ
    ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
    ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')) y
    (comp_chartSection_locusPoint τ hw y hy) (s.fibreToSpaceHom T (locusPoint w ≫ f.hom))
    (s.twistModule Px d).obj (s.fibreToSpaceTwistModuleIso Px T (locusPoint w ≫ f.hom) d)
    (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d) _ rfl _ rfl

include hw in
/-- **The right-hand side of the square of the source factor**: the reading along the section
`c_{w ∘ τ}` of the base change identification of Stacks 084D at `w ∘ τ`, which is the transfer
along `y` of the identification at `w`.

The statement is the instance of
`AlgebraicGeometry.Space.modulePullback_map_attachedSource_target_reading_eq` (`type_of%`), with
its site named for the reason given at
`…InvertibleTwistingRestriction.chartSource_reading`. -/
theorem chartSource_target_reading (d : ℤ)
    (y : s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
      s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))
    (hy : s.relativeProjPoints.LiesOver y τ)
    (hfy : representedSpaceMap s.site s.base s.containsBase y ≫
        s.fibreToSpaceHom T (locusPoint w ≫ f.hom) =
      s.fibreToSpaceHom T' (locusPoint w' ≫ f.hom)) :
    type_of% (modulePullback_map_attachedSource_target_reading_eq
      (B := s.site) (S := s.base) (hS := s.containsBase)
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')) y
      (s.fibreToSpaceHom T (locusPoint w ≫ f.hom))
      (s.fibreToSpaceHom T' (locusPoint w' ≫ f.hom)) hfy (s.twistModule Px d).obj
      (s.fibreToSpaceTwistModuleIso Px T (locusPoint w ≫ f.hom) d)
      (s.fibreToSpaceTwistModuleIso Px T' (locusPoint w' ≫ f.hom) d)
      (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d)
      (s.fibreToSpaceTwistModuleIso_comp_of_eq Px τ (locusPoint w ≫ f.hom)
        (locusPoint w' ≫ f.hom) (map_comp_locusPoint_comp τ hw) y hy d hfy) _ rfl) :=
  modulePullback_map_attachedSource_target_reading_eq
    (B := s.site) (S := s.base) (hS := s.containsBase)
    ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')) y
    (s.fibreToSpaceHom T (locusPoint w ≫ f.hom))
    (s.fibreToSpaceHom T' (locusPoint w' ≫ f.hom)) hfy (s.twistModule Px d).obj
    (s.fibreToSpaceTwistModuleIso Px T (locusPoint w ≫ f.hom) d)
    (s.fibreToSpaceTwistModuleIso Px T' (locusPoint w' ≫ f.hom) d)
    (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d)
    (s.fibreToSpaceTwistModuleIso_comp_of_eq Px τ (locusPoint w ≫ f.hom)
      (locusPoint w' ≫ f.hom) (map_comp_locusPoint_comp τ hw) y hy d hfy) _ rfl

include hw in
/-- **The coherence of Stacks 03LU between the two sides of the square of the source factor**:
`AlgebraicGeometry.Space.modulePullback_sourceChain_eq` at the two factorisations
`w ≫ r = c_w ≫ (T ×_Y P ⟶ P)` and `(w ∘ τ) ≫ r = c_{w ∘ τ} ≫ (T' ×_Y P ⟶ P)` of the two scheme
points, and at `y`.

The statement is the instance of that lemma (`type_of%`).  No trailing morphism is attached: both
sides end at `(c_{w ∘ τ} ≫ y)^*((T ×_Y P ⟶ P)^*𝒪(d))`, so no attached module occurs, and the
composition with the reading of Stacks 03DX (2) is carried out by
`AlgebraicGeometry.Space.attachedSourceSquare_chase` in an arbitrary category.

All nine morphisms are written out, in the site spelling `s.site` that
`…InvertibleTwistingRestriction.chartSource_reading` is named at and that
`…InvertibleTwistingRestriction.chartSourceIso` is defined at: leaving them to be inferred from
the equations instead puts this declaration itself beyond the budget. -/
theorem chartSource_sourceChain (d : ℤ)
    (y : s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
      s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))
    (hfy : representedSpaceMap s.site s.base s.containsBase y ≫
        s.fibreToSpaceHom T (locusPoint w ≫ f.hom) =
      s.fibreToSpaceHom T' (locusPoint w' ≫ f.hom))
    (hwc : τ ≫ (ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w) =
      (ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w') ≫ y) :
    type_of% (modulePullback_sourceChain_eq
      (representedSpaceMap s.site s.base s.containsBase τ) (pointHom w) (pointHom w')
      ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
      (representedSpaceMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
      (s.fibreToSpaceHom T (locusPoint w ≫ f.hom))
      (representedSpaceMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')))
      (s.fibreToSpaceHom T' (locusPoint w' ≫ f.hom))
      (representedSpaceMap s.site s.base s.containsBase y) (s.twistModule Px d).obj
      (pointHom_comp τ hw) (pointHom_comp_invertibleSpaceMorphism w)
      (pointHom_comp_invertibleSpaceMorphism w') hfy
      (algebraicSpacesComp_representedSpaceMap s.site s.base s.containsBase τ _)
      (congrArg (representedSpaceMap s.site s.base s.containsBase) hwc)
      (algebraicSpacesComp_representedSpaceMap s.site s.base s.containsBase _ y)) :=
  modulePullback_sourceChain_eq
    (representedSpaceMap s.site s.base s.containsBase τ) (pointHom w) (pointHom w')
    ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
    (representedSpaceMap s.site s.base s.containsBase
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
    (s.fibreToSpaceHom T (locusPoint w ≫ f.hom))
    (representedSpaceMap s.site s.base s.containsBase
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')))
    (s.fibreToSpaceHom T' (locusPoint w' ≫ f.hom))
    (representedSpaceMap s.site s.base s.containsBase y) (s.twistModule Px d).obj
    (pointHom_comp τ hw) (pointHom_comp_invertibleSpaceMorphism w)
    (pointHom_comp_invertibleSpaceMorphism w') hfy
    (algebraicSpacesComp_representedSpaceMap s.site s.base s.containsBase τ _)
    (congrArg (representedSpaceMap s.site s.base s.containsBase) hwc)
    (algebraicSpacesComp_representedSpaceMap s.site s.base s.containsBase _ y)

/-- **The five factors of the source factor of the chart maps**: the comparison of Stacks 03LU
for `w` and `r_{ℒ,ψ}`, the transport along the two factorisations of `r_{ℒ,ψ} ∘ w`, the inverse
comparison for `c_w` and `T ×_Y P ⟶ P`, the inverse image along `c_w` of the base change
identification of Stacks 084D and the reading of Stacks 03DX (2).

The statement is the instance of `AlgebraicGeometry.Space.comp_assoc_five` (`type_of%`), and the
reading is in a declaration of its own, with its own budget: inside the square, where the ends of
the five factors are already fixed by the coherence of Stacks 03LU, matching
`…chartSourceIso.hom` against the grouped composite makes the elaborator normalise the section
`c_w` as a morphism of schemes -- `…InvertibleTwistingRestriction.chartSection` unfolded twenty
thousand times, and with it the `IsPullback.lift` and the colimits of the fibre -- and it times
out at `isDefEq`. -/
theorem chartSourceIso_hom_eq (d : ℤ) :
    type_of% (comp_assoc_five_of_trans
      ((chartSourceIso Px w (locusOpen_locusPoint w) d).hom) (trans_trans_hom _ rfl)
      (trans_trans_hom _ rfl)) :=
  comp_assoc_five_of_trans ((chartSourceIso Px w (locusOpen_locusPoint w) d).hom)
    (trans_trans_hom _ rfl) (trans_trans_hom _ rfl)

include hw in
/-- **The two sides of the square of the source factor, glued along the coherence of
Stacks 03LU**: the left-hand side of the square, read through the contraction
`…InvertibleTwistingRestriction.chartSource_reading` of its last three factors and the coherence
`…InvertibleTwistingRestriction.chartSource_sourceChain` of Stacks 03LU, is the right-hand side
followed by the reading of `𝒪(d)` along `c_{w ∘ τ} ≫ y`.

The statement is the instance of `AlgebraicGeometry.Space.attachedSourceSides_chase`
(`type_of%`).  The bridge the chase isolates is `rfl`: both producers spell the comparison of
Stacks 03LU for `τ` and `c_w` at the inverse image of the twist along `T ×_Y P ⟶ P`, and they
spell it the same way because the reading takes the twist as an `𝒪`-module rather than as the
quasi-coherent object of
`AlgebraicGeometry.Space.RelativeProjSituation.twistModule` -- see
`AlgebraicGeometry.Space.attachedModuleIsoPullback_hom`. -/
theorem chartSource_sides (d : ℤ)
    (y : s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
      s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))
    (hy : s.relativeProjPoints.LiesOver y τ)
    (hfy : representedSpaceMap s.site s.base s.containsBase y ≫
        s.fibreToSpaceHom T (locusPoint w ≫ f.hom) =
      s.fibreToSpaceHom T' (locusPoint w' ≫ f.hom)) :
    type_of% (attachedSourceSides_chase (chartSource_reading Px τ hw d y hy)
      (chartSource_sourceChain Px τ hw d y hfy (comp_chartSection_locusPoint τ hw y hy)) rfl) :=
  attachedSourceSides_chase (chartSource_reading Px τ hw d y hy)
    (chartSource_sourceChain Px τ hw d y hfy (comp_chartSection_locusPoint τ hw y hy)) rfl

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
