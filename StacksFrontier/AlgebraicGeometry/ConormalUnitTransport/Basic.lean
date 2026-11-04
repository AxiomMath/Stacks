module

public import StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Normalization

/-!
# The transports of the ideal sheaf commute with the units of the pullback adjunctions

`StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic` builds the transports of
`Stacks.ClosedImmersion.idealSheaf` along isomorphisms of source and target — in particular
`Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare`, which reads a
commuting square `f ≫ β.hom = ε.hom ≫ k` with `ε` and `β` isomorphisms and returns
`I(f) ≅ β.hom^* I(k)` — and characterizes every one of them **only** through the inclusion
`CategoryTheory.Limits.kernel.ι` of the ideal sheaf into the structure sheaf. Its own "What is not
done" records the consequence: the *pulled-back* form has no compatibility with those inclusions,
because an inclusion is not preserved by a pullback, so the statement that replaces it is one
about the **unit** of `RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction`. This file
supplies those unit statements.

They are what a generator formula has to travel through. The pullback of a sheaf of modules is a
sheafification, so a section of `β.hom^* I(k)` cannot be named elementwise — the module docstring
of `StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic` records that its comparison
isomorphism has no elementwise description either. A section *can* be named by transposing across
the adjunction, which is what the unit does, and the statements below say exactly what the two
transports do to a section named that way.

## Main results

* `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare_unit`: **the
  one that was missing.** For the square `f ≫ β.hom = ε.hom ≫ k`, the unit of
  `β.hom^* ⊣ β.hom_*` at `I(k)`, followed by `β.hom_*` of the comparison and of the inclusion of
  `I(f)` into `𝒪_T`, is the inclusion of `I(k)` into `𝒪_{T'}` followed by the structure-sheaf map
  of `β.hom`. In words: the section of `β.hom^* I(k)` that the comparison assigns to a section of
  `I(k)` has, in `β.hom_* 𝒪_T`, exactly the image that section had in `𝒪_{T'}`.
* `Stacks.Conormal.AffineCotangent.SourceTransport.eq_idealSheafIsoPullbackOfSquare_inv`: that
  property **determines** the comparison. Adjoint transposition is a bijection and
  `CategoryTheory.Limits.kernel.ι` is a monomorphism, so no other morphism
  `β.hom^* I(k) ⟶ I(f)` satisfies it.
* `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare_inv_comp_ι`:
  the sheaf-level half of the first, with no unit in it — the comparison composed with the
  inclusion of `I(f)` is the pullback of the inclusion of `I(k)` followed by the identification
  `Stacks.IdealSheafRestrict.pullbackUnitIso` of the pulled-back structure sheaf. This is the
  statement `idealSheafIsoOfIsoSource_hom_comp_ι` and
  `Stacks.IdealSheafRestrict.pullbackIdealSheafIso_hom_comp_ι` combine into, and the only input
  to the unit statement that is about ideal sheaves rather than about adjunctions.
* `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSourceOfCompEq_inv_comp_ι`:
  `idealSheafIsoOfIsoSource_inv_comp_ι` for the form in which the composite is presented as a
  separately named morphism together with an equation, which is the form
  `idealSheafIsoPullbackOfSquare` is built from.
* `Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackCompIso_comp_map`: **the
  pseudofunctoriality factor and the functorial factor at once.** For morphisms of ringed spaces
  `a : X'' ⟶ X'` and `b : X' ⟶ X` and a morphism `ψ : M ⟶ N` of sheaves of `𝒪_X`-modules, the
  unit of `(a ≫ b)^* ⊣ (a ≫ b)_*` at `M`, followed by `(a ≫ b)_*` of the pseudofunctoriality
  isomorphism and then of `a^* (b^* ψ)`, is `ψ` followed by the composite of the two units at `N`.
* `Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource_unit`:
  that general statement at the source-slot transport, which is the compatibility of the
  pulled-back form with the units that `ConormalSourceTransport.Basic` names as absent. The
  section of `α.hom^* g^* I(g)` assigned to a section of `I(α.hom ≫ g)` is the one obtained by
  first transporting the section along `idealSheafIsoOfIsoSource` and then applying the two units
  in turn.
* `Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource_unit_app`
  — **that statement on a section.** The same identity read over an open `O` of `B` at a section
  of `I(α.hom ≫ g)`, which is the form a chart layer consumes: the transport carries the section of
  `(α.hom ≫ g)^* I(α.hom ≫ g)` named through the unit by `x` to the section of `α.hom^* g^* I(g)`
  named through the two units by `idealSheafIsoOfIsoSource` of `x`, whose own sections
  `idealSheafIsoOfIsoSource_hom_val_app` computes. Every collapse it needs holds by `rfl`.

## Route

For `idealSheafIsoPullbackOfSquare`, the comparison is by construction
`β.hom^*(φ.inv) ≫ τ.hom` with `φ` the source-slot transport
`idealSheafIsoOfIsoSourceOfCompEq ε k (f ≫ β.hom)` and `τ` the target-slot transport
`Stacks.IdealSheafRestrict.pullbackIdealSheafIso β.hom f`, and both factors are described through
`kernel.ι`:

* `τ.hom ≫ ι(f) = β.hom^*(ι(f ≫ β.hom)) ≫ (pullbackUnitIso β.hom).hom`, which is
  `pullbackIdealSheafIso_hom_comp_ι`;
* `φ.inv ≫ ι(f ≫ β.hom) = ι(k)`, which is `idealSheafIsoOfIsoSource_inv_comp_ι` after the
  composite is substituted.

That gives `idealSheafIsoPullbackOfSquare_inv_comp_ι`, after which only two formal facts remain:
naturality of the unit, which moves the unit past `β.hom^*(ι(k))`, and
`Stacks.Conormal.unit_comp_map_pullbackUnitModuleIso`, which says the unit at the structure sheaf
followed by `β.hom_*(pullbackUnitIso β.hom).hom` is the structure-sheaf map of `β.hom`. Nothing
about the sheafification inside `RingedSpaceModuleAdjunction.modulePullback` is done by hand; the
two inputs just named are where it was paid for.

For `modulePullbackIdealSheafIsoOfIsoSource`, the general statement
`unit_comp_map_modulePullbackCompIso_comp_map` is proved by recognizing both sides as the unit of
`Stacks.PullbackPseudofunctor.compAdjunction` — the left-hand side by
`unit_comp_map_modulePullbackCompIso_hom_app`, the right-hand side by
`compAdjunction_unit_app` — so that the claim becomes naturality of that one unit. In particular
no functor equality is rewritten: `compAdjunction` is the declaration whose *type* already
performs the collapse `modulePushforward a ⋙ modulePushforward b = modulePushforward (a ≫ b)`,
so the collapse is never elaborated here. Doing it by hand instead, as a `rfl` between
`(a ≫ b)_*.map ψ` and `b_*.map (a_*.map ψ)`, **exceeds the default heartbeat budget**,
the same expense `StacksFrontier.AlgebraicGeometry.ConormalComparison.Normalization` records
for the identity.

## Vocabulary

Tag 01C2's `idealSheaf` is `Stacks.ClosedImmersion.idealSheaf`.

**No labelled assertion of
[Stacks, Tag 01R3] is discharged here and no `stacks` attribute is attached.** Everything below
is an input to its part (2).

No hypothesis beyond isomorphisms and morphisms of schemes is used: nothing is affine,
Noetherian, quasi-compact, or an immersion of any kind, and `k` and `g` are arbitrary morphisms,
not closed immersions.

## Universe situation

A single universe `u` (`Scheme.{u}` and `SheafOfModules.{u}`), as in the tagged statements, forced by
`RingedSpaceModuleAdjunction`, whose module pullback exists only for `RingedSpace.{u, u}`.

## Transparency gotchas

Three spellings have to be kept apart, and each one is forced on a different input.

* `Stacks.Conormal.unit_comp_map_pullbackUnitModuleIso` is stated with
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, and everything here with
  `RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` of the underlying morphism of
  ringed spaces. The two agree definitionally but not syntactically, so that input is restated
  by a type-ascribed `have` and used by `exact`, never by `rw`.
* `Stacks.Conormal.AffineCotangent.Transport.idealSheafIsoOfIsoTarget f β` is a *separate
  definition* whose body is `Stacks.IdealSheafRestrict.pullbackIdealSheafIso β.hom f`, so a `rw`
  with `pullbackIdealSheafIso_hom_comp_ι` does not match it. The decomposition of
  `idealSheafIsoPullbackOfSquare` is therefore written with `pullbackIdealSheafIso` directly —
  which is `rfl`, and makes the subsequent rewrites fire.
* `modulePullback (α.hom ≫ g).toLRSHom.toShHom` and
  `modulePullback (α.hom.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)` are definitionally equal, and a
  `rw` under them produces a term that is not type-correct at implicit transparency,
  with the rewrite failing at `Functor.map_comp`. That is why
  `modulePullbackIdealSheafIsoOfIsoSource_unit` is *applied* from a lemma proved at the
  ringed-space level, where the composite is literal, rather than proved in place.

## What is not done

* **No labelled assertion of [Stacks, Tag 01R3] is discharged and no tag is attached.**
* **No elementwise description of the unit itself, and none at all for the square transport.**
  `modulePullbackIdealSheafIsoOfIsoSource_unit_app` reads the source transport on a section
  *named by* the unit, which is as far as a sheafification admits: the module pullback has no
  elementwise description, so there is no formula for a unit generator's own value, and a
  generator formula in the sense of the statement has to be carried by these equations rather than by a
  section computation. For `idealSheafIsoPullbackOfSquare` not even that much is done — only the
  morphism equation `idealSheafIsoPullbackOfSquare_unit` is available.
* **No unit compatibility for the chain to the affine model as a whole.** The individual
  comparisons that `StacksFrontier.AlgebraicGeometry.CotangentAppIso.Sections` composes with the
  transports are now covered —
  `Stacks.Conormal.AffineShape.unit_comp_map_pullbackIsoPushforwardInv` and
  `Stacks.Conormal.AffineShape.unit_comp_map_pullbackObjCongr`, with the two
  `AlgebraicGeometry.Scheme.Modules.pushforwardComp`/`pushforwardCongr` steps needing nothing
  beyond Mathlib's own `pushforwardComp_hom_app_app` and `pushforwardCongr_hom_app_app` — but
  `Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` is still not characterized through the
  units, because it takes its locality comparison as an uncharacterized hypothesis; see the
  "What is not done" section of that file.
* **Nothing about `Ideal.Cotangent`**, the square of the ideal, or epimorphy of the quotient map.
* **No counit statements.** Only the units are treated; the counit of the same adjunction, which
  is what a *pushforward* comparison would be characterized by, is untouched.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.IdealSheafRestrict

universe u

namespace Stacks.PullbackPseudofunctor

/-- **The pseudofunctoriality factor and the functorial factor at once.** For morphisms of
ringed spaces `a : X'' ⟶ X'` and `b : X' ⟶ X` and a morphism `ψ : M ⟶ N` of sheaves of
`𝒪_X`-modules, the unit of `(a ≫ b)^* ⊣ (a ≫ b)_*` at `M`, followed by `(a ≫ b)_*` of the
pseudofunctoriality isomorphism `modulePullbackCompIso` and then of `a^* (b^* ψ)`, is `ψ`
followed by the two units in turn.

This is the shape in which a comparison built as `modulePullbackCompIso` followed by a pullback
of a morphism — which is how every pulled-back transport of an ideal sheaf is built — is
characterized through the units.

Both sides are the unit of `compAdjunction b a`: the left-hand side by
`unit_comp_map_modulePullbackCompIso_hom_app`, the right-hand side by `compAdjunction_unit_app`.
So the claim is naturality of that single unit, and the collapse
`modulePushforward a ⋙ modulePushforward b = modulePushforward (a ≫ b)` is performed by the
*type* of `compAdjunction` rather than elaborated; see the module docstring for the cost of doing
it by hand. -/
theorem unit_comp_map_modulePullbackCompIso_comp_map {X X' X'' : RingedSpace.{u, u}}
    (b : X' ⟶ X) (a : X'' ⟶ X') {M N : SheafOfModules.{u} (structureSheafRing X)} (ψ : M ⟶ N) :
    (modulePullbackPushforwardAdjunction (a ≫ b)).unit.app M ≫
        (modulePushforward (a ≫ b)).map
          ((modulePullbackCompIso b a).hom.app M ≫
            (modulePullback a).map ((modulePullback b).map ψ)) =
      ψ ≫ (modulePullbackPushforwardAdjunction b).unit.app N ≫
        (modulePushforward b).map
          ((modulePullbackPushforwardAdjunction a).unit.app ((modulePullback b).obj N)) := by
  rw [Functor.map_comp, ← Category.assoc, unit_comp_map_modulePullbackCompIso_hom_app,
    ← compAdjunction_unit_app, ← compAdjunction_unit_app]
  exact ((compAdjunction b a).unit.naturality ψ).symm

end Stacks.PullbackPseudofunctor

namespace Stacks.Conormal.AffineCotangent.SourceTransport

open Stacks.PullbackPseudofunctor

/-! ### The source slot with the composite presented by an equation -/

variable {A A' B : Scheme.{u}} (α : A' ≅ A) (g : A ⟶ B)

/-- `idealSheafIsoOfIsoSource_inv_comp_ι` for `idealSheafIsoOfIsoSourceOfCompEq`, that is, with
the composite `α.hom ≫ g` presented as a separately named morphism `h` together with the
equation `α.hom ≫ g = h`. This is the form `idealSheafIsoPullbackOfSquare` is built from, so it
is the form in which the source slot's description through `kernel.ι` has to be available. -/
theorem idealSheafIsoOfIsoSourceOfCompEq_inv_comp_ι (h : A' ⟶ B) (hh : α.hom ≫ g = h) :
    (idealSheafIsoOfIsoSourceOfCompEq α g h hh).inv ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom h.toLRSHom.toShHom)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom g.toLRSHom.toShHom)) := by
  subst hh
  exact idealSheafIsoOfIsoSource_inv_comp_ι α g

/-! ### The pulled-back source transport and the units -/

/-- **The pulled-back source-slot transport commutes with the units.** The unit of
`(α.hom ≫ g)^* ⊣ (α.hom ≫ g)_*` at the ideal sheaf of `α.hom ≫ g`, followed by the pushforward
of `modulePullbackIdealSheafIsoOfIsoSource`, is the sheaf transport
`idealSheafIsoOfIsoSource` followed by the unit for `g` and the pushforward along `g` of the unit
for `α.hom`.

This is the compatibility of the pulled-back form with the adjunctions that
`StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic` records as absent: the
inclusion of an ideal sheaf into the structure sheaf is not preserved by a pullback, so the
statement describing the pulled-back comparison is this one rather than an analogue of
`Stacks.IdealSheafRestrict.pullbackIdealSheafIso_hom_comp_ι`.

It is `Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackCompIso_comp_map` applied to the
two underlying morphisms of ringed spaces and to `(idealSheafIsoOfIsoSource α g).hom`, which is
exactly the pair of factors `modulePullbackIdealSheafIsoOfIsoSource` is built from. The
application rather than a proof in place is forced; see the module docstring. -/
theorem modulePullbackIdealSheafIsoOfIsoSource_unit :
    (modulePullbackPushforwardAdjunction (α.hom ≫ g).toLRSHom.toShHom).unit.app
          (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom) ≫
        (modulePushforward (α.hom ≫ g).toLRSHom.toShHom).map
          (modulePullbackIdealSheafIsoOfIsoSource α g).hom =
      (idealSheafIsoOfIsoSource α g).hom ≫
        (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom) ≫
          (modulePushforward g.toLRSHom.toShHom).map
            ((modulePullbackPushforwardAdjunction α.hom.toLRSHom.toShHom).unit.app
              ((modulePullback g.toLRSHom.toShHom).obj
                (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom))) :=
  unit_comp_map_modulePullbackCompIso_comp_map g.toLRSHom.toShHom α.hom.toLRSHom.toShHom
    (idealSheafIsoOfIsoSource α g).hom

/-- **The section formula for the pulled-back source-slot transport.** Over an open `O` of `B`,
the transport carries the section of `(α.hom ≫ g)^* I(α.hom ≫ g)` named by a section `x` of
`I(α.hom ≫ g)` through the unit to the section of `α.hom^* g^* I(g)` named by the image of `x`
under the *sheaf* transport `idealSheafIsoOfIsoSource` — whose sections
`idealSheafIsoOfIsoSource_hom_val_app` computes — through the unit for `g` and then the unit for
`α.hom`.

This is `modulePullbackIdealSheafIsoOfIsoSource_unit` read on sections over `O` at `x`. Every
collapse the descent needs holds by `rfl`: a composite of morphisms of sheaves of modules is the
composite on sections, and a direct image of a morphism is that morphism on sections over the
preimage. So the whole statement is a `congrArg` of the unit characterization, exactly as
`Stacks.Conormal.Locality.pullbackRestrictIsoOf_unit_app` is of its own.

The two opens agree: `(α.hom ≫ g) ⁻¹ᵁ O` and `α.hom ⁻¹ᵁ (g ⁻¹ᵁ O)` are the same open
definitionally, the composite being literal here, so no transport appears. The variant
`modulePullbackIdealSheafIsoOfIsoSourceOfCompEq`, with the composite presented by an equation,
does not arise in this form: its consumers hand over the literal composite. -/
theorem modulePullbackIdealSheafIsoOfIsoSource_unit_app (O : B.Opens)
    (x : (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom).val.obj (.op O)) :
    (modulePullbackIdealSheafIsoOfIsoSource α g).hom.val.app (.op ((α.hom ≫ g) ⁻¹ᵁ O))
        (((modulePullbackPushforwardAdjunction (α.hom ≫ g).toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom)).val.app (.op O)
          x) =
      ((modulePullbackPushforwardAdjunction α.hom.toLRSHom.toShHom).unit.app
            ((modulePullback g.toLRSHom.toShHom).obj
              (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom))).val.app (.op (g ⁻¹ᵁ O))
        (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
              (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom)).val.app (.op O)
          ((idealSheafIsoOfIsoSource α g).hom.val.app (.op O) x)) :=
  congrArg (fun ψ => ModuleCat.Hom.hom ψ x)
    (congr($(modulePullbackIdealSheafIsoOfIsoSource_unit α g).val.app (.op O)))

/-! ### The square transport and the units -/

variable {S S' T T' : Scheme.{u}} (f : S ⟶ T) (ε : S ≅ S') (k : S' ⟶ T') (β : T ≅ T')
  (hsq : f ≫ β.hom = ε.hom ≫ k)

/-- **`idealSheafIsoPullbackOfSquare` composed with the inclusion of `I(f)` is the pullback of
the inclusion of `I(k)`.** For the square `f ≫ β.hom = ε.hom ≫ k` with `ε` and `β`
isomorphisms, the comparison `I(f) ≅ β.hom^* I(k)`, inverted and followed by the inclusion of
`I(f)` into `𝒪_T`, is `β.hom^*` of the inclusion of `I(k)` into `𝒪_{T'}` followed by the
identification `Stacks.IdealSheafRestrict.pullbackUnitIso` of `β.hom^* 𝒪_{T'}` with `𝒪_T`.

This is the only ingredient of the unit statement below that is about ideal sheaves rather than
about adjunctions, and it is the two constituents' descriptions through `kernel.ι` combined:
`Stacks.IdealSheafRestrict.pullbackIdealSheafIso_hom_comp_ι` for the target slot and
`idealSheafIsoOfIsoSourceOfCompEq_inv_comp_ι` for the source slot. -/
theorem idealSheafIsoPullbackOfSquare_inv_comp_ι :
    (idealSheafIsoPullbackOfSquare f ε k β hsq).inv ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom f.toLRSHom.toShHom)) =
      (modulePullback β.hom.toLRSHom.toShHom).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom k.toLRSHom.toShHom))) ≫
        (pullbackUnitIso β.hom).hom := by
  have hinv : (idealSheafIsoPullbackOfSquare f ε k β hsq).inv =
      (modulePullback β.hom.toLRSHom.toShHom).map
          (idealSheafIsoOfIsoSourceOfCompEq ε k (f ≫ β.hom) hsq.symm).inv ≫
        (Stacks.IdealSheafRestrict.pullbackIdealSheafIso β.hom f).hom := rfl
  rw [hinv, Category.assoc, Stacks.IdealSheafRestrict.pullbackIdealSheafIso_hom_comp_ι,
    ← Category.assoc, ← Functor.map_comp,
    idealSheafIsoOfIsoSourceOfCompEq_inv_comp_ι ε k (f ≫ β.hom) hsq.symm]

/-- **`idealSheafIsoPullbackOfSquare` commutes with the units.** For the square
`f ≫ β.hom = ε.hom ≫ k` with `ε` and `β` isomorphisms, the unit of `β.hom^* ⊣ β.hom_*` at the
ideal sheaf of `k`, followed by `β.hom_*` of the comparison `β.hom^* I(k) ⟶ I(f)` and of the
inclusion of `I(f)` into `𝒪_T`, is the inclusion of `I(k)` into `𝒪_{T'}` followed by the
structure-sheaf map of `β.hom`.

Read on sections over an open `O` of `T'`: the section of `β.hom^* I(k)` that the comparison
sends to a section `x` of `I(k)` has, as a section of `𝒪_T` over `β.hom ⁻¹ᵁ O`, exactly the
image of `x` in `𝒪_{T'}` transported by `β.hom^♯`. That is the statement a generator formula has
to be pushed through, and it cannot be replaced by a section computation: the module pullback is
a sheafification and has no elementwise description.

`eq_idealSheafIsoPullbackOfSquare_inv` says this property determines the comparison, so it is a
characterization and not merely a compatibility.

The proof is `idealSheafIsoPullbackOfSquare_inv_comp_ι` followed by two formal facts: naturality
of the unit, and `Stacks.Conormal.unit_comp_map_pullbackUnitModuleIso` at `β.hom`, which is the
adjoint description of the identification of the pulled-back structure sheaf. -/
theorem idealSheafIsoPullbackOfSquare_unit :
    (modulePullbackPushforwardAdjunction β.hom.toLRSHom.toShHom).unit.app
          (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom) ≫
        (modulePushforward β.hom.toLRSHom.toShHom).map
          ((idealSheafIsoPullbackOfSquare f ε k β hsq).inv ≫
            kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom f.toLRSHom.toShHom))) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom k.toLRSHom.toShHom)) ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom β.hom.toLRSHom.toShHom) := by
  have hnat : ∀ {M N : SheafOfModules.{u} (structureSheafRing T'.toSheafedSpace)} (ψ : M ⟶ N),
      (modulePullbackPushforwardAdjunction β.hom.toLRSHom.toShHom).unit.app M ≫
          (modulePushforward β.hom.toLRSHom.toShHom).map
            ((modulePullback β.hom.toLRSHom.toShHom).map ψ) =
        ψ ≫ (modulePullbackPushforwardAdjunction β.hom.toLRSHom.toShHom).unit.app N :=
    fun ψ =>
      ((modulePullbackPushforwardAdjunction β.hom.toLRSHom.toShHom).unit.naturality ψ).symm
  have hunitiso :
      (modulePullbackPushforwardAdjunction β.hom.toLRSHom.toShHom).unit.app
            (SheafOfModules.unit (structureSheafRing T'.toSheafedSpace)) ≫
          (modulePushforward β.hom.toLRSHom.toShHom).map (pullbackUnitIso β.hom).hom =
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom β.hom.toLRSHom.toShHom) :=
    Stacks.Conormal.unit_comp_map_pullbackUnitModuleIso β.hom
  rw [idealSheafIsoPullbackOfSquare_inv_comp_ι, Functor.map_comp, ← Category.assoc, hnat,
    Category.assoc, hunitiso]
  rfl

/-- **The unit statement determines `idealSheafIsoPullbackOfSquare`.** Any morphism
`β.hom^* I(k) ⟶ I(f)` with the property of `idealSheafIsoPullbackOfSquare_unit` is its inverse.

So that property is a characterization. Two cancellations: adjoint transposition across
`β.hom^* ⊣ β.hom_*` is a bijection, which pins down the composite with the inclusion of `I(f)`,
and that inclusion is `CategoryTheory.Limits.kernel.ι`, a monomorphism, which pins down the
morphism itself. -/
theorem eq_idealSheafIsoPullbackOfSquare_inv
    (w : (modulePullback β.hom.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom) ⟶
      Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom)
    (hw : (modulePullbackPushforwardAdjunction β.hom.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom) ≫
          (modulePushforward β.hom.toLRSHom.toShHom).map
            (w ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom f.toLRSHom.toShHom))) =
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom k.toLRSHom.toShHom)) ≫
          SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom β.hom.toLRSHom.toShHom)) :
    w = (idealSheafIsoPullbackOfSquare f ε k β hsq).inv := by
  refine (cancel_mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom f.toLRSHom.toShHom)))).mp ?_
  refine ((modulePullbackPushforwardAdjunction β.hom.toLRSHom.toShHom).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact hw.trans (idealSheafIsoPullbackOfSquare_unit f ε k β hsq).symm

end Stacks.Conormal.AffineCotangent.SourceTransport

end
