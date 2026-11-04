module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForget
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ModuleInverseImagePushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.PullbackExtensionByZeroUnit
import StacksCore.Tactic.StacksAttribute

/-!
# The forgetful square of the module lower shriek in Situation 08PA

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)`, as in the
standing data of Stacks 08PA, and let `g` be the morphism of ringed topoi it induces.
**Stacks 08PC part (2)** is that the square

```
Mod(O_{C'}) --g_!--> Mod(O_C)
    |                   |
 forget              forget
    v                   v
 Ab(C')  --g_!^{Ab}--> Ab(C)
```

commutes up to natural isomorphism. Read off the Stacks text, that is
the whole of part (2): one assertion, whose sentence is merely interrupted by the displayed
diagram. `MorphismSituation.inverseImageForgetIso` in `ModuleInverseImage.lean` is the
corresponding square for the two *inverse* images; it is proved, but it is not a part of part (2)
and is not registered, for the reason recorded there.

The canonical comparison filling the square above, and the criterion
deciding when it is invertible, are the Stacks 0798 development in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LowerShriekForget.lean`. This file brings that
development to bear on the situation: it instantiates the comparison and the criterion here,
which is not a matter of unification.

The commutation is **false in general** — that is
`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`, with an explicit counterexample over
`Bool`. So the assertion cannot follow from part (1); whatever proves it must use the
hypothesis of Situation 08PA that the structure map `g♯` is invertible.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.moduleLowerShriekForgetComparison`: the
  canonical comparison `forget ∘ g_! ⟶ g_!^{Ab} ∘ forget` at this situation.
* `Stacks.Sites.FibredCategory.MorphismSituation.moduleExtensionByZeroUnitIso`: **Stacks 07AC
  here**, `g_! (j_{U'!} O_{U'}) ≅ j_{u(U')!} O_{u(U')}`, at the spelling of `j_{U!} O_U` the
  criterion uses.

## Main results

* `Stacks.Sites.FibredCategory.MorphismSituation.isIso_moduleLowerShriekForgetComparison_iff`:
  **the Stacks 0798 criterion, instantiated at Situation 08PA.** The forgetful square commutes
  if and only if the comparison is invertible at the extension by zero `j_{U'!} O_{U'}` of the
  structure sheaf, for every object `U'` of `C'`.

## Implementation notes

**Why instantiating the criterion is a separate step.** Three obstacles:

1. *The universes cannot be inverted.* In
   `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_iff` the module-sections universe
   `t` occurs only inside `max u₁ v₁ u₂ v₂ u t`, and a `max` has no inverse, so unification
   cannot recover it from the instance arguments: every universe has to be given positionally.
   The declaration's `universe` command is split across two closed sections of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LowerShriekForget.lean` (`universe u w u₁ u₂ v₁ v₂` for the comparison, and
   `universe w t u₁ u₂ v₁ v₂` with `u` auto-bound for the criterion), so the positional order
   is not readable off the source. As `#check @…` shows, it is

   `isIso_lowerShriekForgetComparison_iff.{u, t, u₁, u₂, v₁, v₂}`

   — **six** universes, not seven: `w` is declared in the criterion's section but does not
   occur in the statement, being pinned to `max u₁ v₁ u₂ v₂ u t` by the instance arguments. The
   auto-bound `u` comes *first*, ahead of the explicitly declared block. Here `u₁ v₁` are the
   source site's and `u₂ v₂` the target's — the criterion's `C` is the *source* — so at this
   situation the instantiation is `.{max w u₀ u₁ u₂ v₀ v₁ v₂, 0, u₂, u₁, v₂, v₁}`, with `t = 0`
   because the ring universe already absorbs the four site universes.

   `lowerShriekForgetComparison` itself lives in the other section and takes its universes in
   that section's order, `.{u, w, u₁, u₂, v₁, v₂}`; there `w` *is* a parameter.

2. *The two sites have two spellings.* The criterion's `J` and `K` get pinned by the structure
   sheaves, which exist only in ringed-topos form, so every hypothesis is asked for at
   `(S.sourceTopos S.pi').J` and `(S.totalTopos S.pi).J` rather than at `S.sourceTopology` and
   `S.totalTopology`. Those are the same topologies but carry different hidden `Category`
   arguments, so the instances declared at the latter are not found at the former. The four that
   had to be restated are `MorphismSituation.uContinuousTopos`,
   `MorphismSituation.hasWeakSheafifyTotalTopos`,
   `MorphismSituation.wEqualsLocallyBijectiveTotalTopos` and
   `MorphismSituation.abelianInverseImageTopos_isRightAdjoint`, all in `ModuleInverseImage.lean`
   next to the source-side ones that were already there.

3. *`g^*` is not syntactically a pushforward.* The criterion is phrased for
   `SheafOfModules.pushforward phi`, and needs that functor to be a right adjoint. Part (1)
   gives it for `g^* = RingedToposHom.pullbackModules S.gRinged`, which is only *isomorphic* to
   a pushforward; `MorphismSituation.modulePushforward_isRightAdjoint` transports it along
   `MorphismSituation.moduleInverseImageIsoPushforward`.

## What this file does not contain

Part (2) itself: that the comparison below is invertible is
`MorphismSituation.isIso_moduleLowerShriekForgetComparison` in
`ModuleLowerShriekForgetSquare.lean`, proved there through the criterion
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_localizedStructureSheafComparison` of
Stacks 0798 for the structure sheaf `u⁻¹O_C`, rather than through the criterion at the extensions
by zero instantiated here: the canonical maps `(g')^{Ab}_! O_{U'} ⟶ O_{u(U')}` are shown to be
isomorphisms by a Yoneda argument, Stacks 08PB entering through
`MorphismSituation.homEquiv_localizedLowerShriekSourceProjectionIso_hom_app_comp_of_unit`, and the
structure sheaf of Situation 08PA is then reached by restriction of scalars along the invertible
structure map. The comparison and the criterion instantiated below are kept for the record of the
Stacks 0798 development at this situation.

## References

* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 08PB](https://stacks.math.columbia.edu/tag/08PB)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})
  [HasWeakSheafify S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.sourceTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]
  [S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}]

/-- The canonical comparison `forget ∘ g_! ⟶ g_!^{Ab} ∘ forget` of Stacks 0798 at Situation
08PA: the natural transformation whose invertibility is Stacks 08PC part (2).

`g_!` appears here as the left adjoint of the *pushforward* along `u` and
`MorphismSituation.moduleStructureMap`, which is `g^*` by
`MorphismSituation.moduleInverseImageIsoPushforward`; that is the form
`Stacks.SheafOfModules.lowerShriekForgetComparison` is phrased in.

Every argument is given explicitly, including the two `Category` instances, which are taken
from the ringed topoi. This is not presentation: writing `lowerShriekForgetComparison S.u
S.moduleStructureMap` and letting unification work instead produces the *mixed* spelling —
the two sites from `moduleStructureMap`, hence `(S.sourceTopos S.pi').J` and
`(S.totalTopos S.pi).J`, but the two categories from `S.u`, hence the situation's
`sourceCategory` and `totalCategory`. Nothing is registered at that combination, so
`MorphismSituation.modulePushforward_isRightAdjoint` and
`MorphismSituation.abelianInverseImageTopos_isRightAdjoint` are both missed and the
abbreviation does not elaborate. The same reason forces the explicit form in
`isIso_moduleLowerShriekForgetComparison_iff` below. -/
abbrev moduleLowerShriekForgetComparison :=
  @Stacks.SheafOfModules.lowerShriekForgetComparison.{max w u₀ u₁ u₂ v₀ v₁ v₂,
      max w u₀ u₁ u₂ v₀ v₁ v₂, u₂, u₁, v₂, v₁}
    (S.sourceTopos S.pi').C (AlgebraicGeometry.RingedTopos.category (S.sourceTopos S.pi'))
    (S.totalTopos S.pi).C (AlgebraicGeometry.RingedTopos.category (S.totalTopos S.pi))
    (S.sourceTopos S.pi').J (S.totalTopos S.pi).J S.u S.uContinuousTopos
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O)
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O)
    S.moduleStructureMap _ _

/-- **The Stacks 0798 criterion at Situation 08PA.** The forgetful square of the module lower
shriek commutes — Stacks 08PC part (2) — if and only if its canonical
comparison is invertible at the extension by zero `j_{U'!} O_{U'}` of the structure sheaf, for
every object `U'` of the source fibred category.

This is `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_iff` instantiated, which the
module docstring above explains cannot be done by unification: all six of its universes are
given positionally, in the order `.{u, t, u₁, u₂, v₁, v₂}` determined empirically, and the two
sites, their categories and the functor are given explicitly for the reason recorded on
`moduleLowerShriekForgetComparison`.

The right-hand side is not discharged here, and is not a consequence of part (1): the square
does not commute for a general morphism of ringed sites, by
`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`. Part (2) is proved in
`ModuleLowerShriekForgetSquare.lean` by another form of the criterion. -/
theorem isIso_moduleLowerShriekForgetComparison_iff :
    IsIso S.moduleLowerShriekForgetComparison ↔
      ∀ U' : (S.sourceTopos S.pi').C,
        IsIso (S.moduleLowerShriekForgetComparison.app
          (Stacks.SheafOfModules.extensionByZeroUnit.{u₂, v₂,
            max w u₀ u₁ u₂ v₀ v₁ v₂, max u₁ v₁}
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O) U')) :=
  @Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_iff.{
      max w u₀ u₁ u₂ v₀ v₁ v₂, 0, u₂, u₁, v₂, v₁}
    (S.sourceTopos S.pi').C (AlgebraicGeometry.RingedTopos.category (S.sourceTopos S.pi'))
    (S.totalTopos S.pi).C (AlgebraicGeometry.RingedTopos.category (S.totalTopos S.pi))
    (S.sourceTopos S.pi').J (S.totalTopos S.pi).J S.u S.uContinuousTopos
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O)
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O)
    S.moduleStructureMap _ _ _ _ _ _

/-- **Stacks 07AC at Situation 08PA, at the spelling the criterion uses.** For every object `U'`
of the source fibred category,

`g_! (j_{U'!} O_{U'}) ≅ j_{u(U')!} O_{u(U')}`,

with `g_!` the left adjoint of the pushforward along `u` and `MorphismSituation.
moduleStructureMap` — the form `moduleLowerShriekForgetComparison` above is phrased in — and
both extensions by zero the sheafified free modules of Stacks 093C, which is the spelling
`isIso_moduleLowerShriekForgetComparison_iff` states its right-hand side at.

This is `Stacks.Cohomology.DerivedLowerShriek.pullbackExtensionByZeroUnitIso`, which is
Stacks 07AC for an *arbitrary* structure morphism of sheaves of rings `O' ⟶ u_* O`. The
statement registered for Stacks 07AC in
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ExtensionByZeroLowerShriekModules.lean`
is for `O_{C'} = g^{-1} O_C` *on the nose*, which Situation 08PA does not provide: here
`O_{C'}` is `(π')^{-1} O_D` and its comparison with `g^{-1} O_C` is the isomorphism `g♯`. No
transport along `g♯` is needed, the generalisation imposing no hypothesis on the structure
morphism at all; `S.moduleStructureMap` is the morphism `O_{C'} ⟶ u_* O_C` built from `g♯` in
`ModuleInverseImage.lean`.

The universes are given positionally, in
`pullbackExtensionByZeroUnitIso`'s own order `.{w, v₁, u₁, v₂, u₂, t}`, with its `C` the
*source* site: at this situation that is `.{max w u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₁, u₁, 0}`, again
with `t = 0` because the ring universe already absorbs the four site universes. The two
`Category` instances are taken from the ringed topoi for the reason recorded on
`moduleLowerShriekForgetComparison`.

That the source really is the object `isIso_moduleLowerShriekForgetComparison_iff` names,
`Stacks.SheafOfModules.extensionByZeroUnit.{u₂, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂, max u₁ v₁}`
applied to the source structure sheaf, was checked rather than assumed: the instantiation above
produces the module universe `max u₂ v₂ (max w u₀ u₁ u₂ v₀ v₁ v₂) (max u₁ v₁ 0)`, and `max l 0`
is the same universe level as `l`. -/
abbrev moduleExtensionByZeroUnitIso (U' : (S.sourceTopos S.pi').C) :=
  @Stacks.Cohomology.DerivedLowerShriek.pullbackExtensionByZeroUnitIso.{
      max w u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₁, u₁, 0}
    (S.sourceTopos S.pi').C (AlgebraicGeometry.RingedTopos.category (S.sourceTopos S.pi'))
    (S.totalTopos S.pi).C (AlgebraicGeometry.RingedTopos.category (S.totalTopos S.pi))
    (S.sourceTopos S.pi').J (S.totalTopos S.pi).J S.u S.uContinuousTopos
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalTopos S.pi).O)
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.sourceTopos S.pi').O)
    S.moduleStructureMap _ U'

end Stacks.Sites.FibredCategory.MorphismSituation

end

