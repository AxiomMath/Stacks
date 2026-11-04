module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeIsomorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekAbelianExact

/-!
# The lower shriek `i_!` of [Stacks, Tag 07IJ] at module coefficients

Let `(S, I, γ)` be a divided power scheme over `ℤ_{(p)}` and `X` a scheme over `S₀ = V(I)` with
`p` locally nilpotent on `X`.  The inclusion `i : Cris(X/S) ⥤ CRIS(X/S)` is fully faithful,
continuous and cocontinuous, so restriction along it has a left adjoint `i_!`, and
[Stacks, Tag 07IJ] records that adjunction together with the formula `i^{-1}i_! = id`.

`SmallSite/LowerShriekExact.lean` and `SmallSite/LowerShriekAbelianExact.lean` build `i_!` at
set and at abelian coefficients.  This file builds it on **sheaves of `𝒪_{X/S}`-modules**:

`i_! : Mod(𝒪_{X/S} on Cris(X/S)) ⟶ Mod(𝒪_{X/S} on CRIS(X/S))`,

left adjoint to the restriction `i^{-1}`, with the unit `F ⟶ i^{-1}i_!F` invertible.  It is the
leg that the general-`g` base change map of [Stacks, Tag 07MS] was missing: the pullback
`Crystalline.GlobalCrystallineSituation.SmallSite.crisModulePullback` needs no hypothesis on
`g : X ⟶ X'` but takes its coefficients on the big crystalline site, and `i_!` is what carries a
small-site module there.  Composing the two gives
`crisModuleInverseImage`, the module-valued `f_cris^{-1}` of [Stacks, Tag 07IK] in the full
generality of [Stacks, Tag 07MJ].

## The sheafification that was thought to be missing

The module documentation of `SmallSite/BaseChangeMap.lean`,
`SmallSite/BaseChangeIsomorphism.lean` and `SmallSite/BaseChangeMapConstruction.lean` recorded
that this `i_!` "wants `HasWeakSheafify` for `ModuleCat`-valued presheaves on the big site, the
one sheafification this chapter does not have".  **That is not what it wants.**  The general
construction `Stacks.SheafOfModules.lowerShriek`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LowerShriek.lean`, `@[stacks 0797]`) sheafifies a
presheaf of modules through `PresheafOfModules.sheafification`, whose existence hypotheses are
`HasWeakSheafify K AddCommGrpCat.{v}` and `K.WEqualsLocallyBijective AddCommGrpCat.{v}` on the
*target* site at the module universe — the coefficients are abelian groups, not `ModuleCat` —
together with four `UnivLE` conditions.  At `K = topology S` and `v = u + 1` every one of them is
already in the library:

* `HasWeakSheafify (topology S) AddCommGrpCat.{u + 1}` is
  `...SmallSite.instHasSheafifyBigAddCommGrpCat` of `SmallSite/CrisDirectImage.lean`, the very
  instance that the abelian `i_!` of `SmallSite/LowerShriekAbelianExact.lean` runs on;
* `(topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1}` is
  `instWEqualsLocallyBijectiveBigAddCommGrpCat` below, the big-site twin of
  `...SmallSite.instWEqualsLocallyBijectiveAddCommGrpCat` and the same one-line instance;
* the four `UnivLE`s are `UnivLE.{u, u + 1}` for the ring and the two morphism universes and
  `UnivLE.{u + 1, u + 1}` for the objects of `Cris(X/S)`, which lie in `Type (u + 1)`.

So no new sheafification is constructed here and none was needed.  What *is* genuinely absent is
the ring-universe-`u` right Kan extension of the structure sheaf along `i.op`, which is why the
module-valued **direct image** `i_*` needs the `ULift` detour of
`SmallSite/CrisModuleDirectImage.lean`; `i_!` is a left adjoint and meets no such obstruction.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `BigModuleSheaf` — the sheaves of `𝒪_{X/S}`-modules on the **big** crystalline site
  `CRIS(X/S)`, at the module universe `u + 1` of this chapter.
* `moduleLowerShriek` — **`i_! : ModuleSheaf S ⥤ BigModuleSheaf S`**, the module-level lower
  shriek of [Stacks, Tag 07IJ].
* `moduleLowerShriekAdjunction` — **`i_! ⊣ i^{-1}`**, with `i^{-1}` the restriction
  `...SmallSite.crisRestrictModules`.
* `moduleLowerShriekUnitIso` — the unit as an isomorphism `id ≅ i^{-1}i_!`.
* `crisModuleInverseImage` — **`f_cris^{-1}` on modules for an arbitrary `g : X ⟶ X'`**,
  `i_{X',!}` followed by `...SmallSite.crisModulePullback`.
* `crisModuleInverseImageIsoSmallChangeBase` — it agrees with the open-immersion pullback
  `...SmallSite.smallChangeBaseModulePullback` wherever the latter is defined.

## Main results

* `instAbelianBigModuleSheaf`, `instIsGrothendieckAbelianBigModuleSheaf`,
  `instEnoughInjectivesBigModuleSheaf` — the modules on the big crystalline site form a
  Grothendieck abelian category with enough injectives, which the library did not record.
* `crisRestrictModules_eq_inverseImage` and `inverseImageRing_eq_structureSheaf` — restriction of
  modules along `i` *is* the inverse image of the general construction, and the restricted
  structure sheaf *is* `𝒪_{X/S}` on the small site, both on the nose.
* `isIso_moduleLowerShriekAdjunction_unit` — **the formula `i^{-1}i_! = id` of
  [Stacks, Tag 07IJ] at module coefficients**, hence `full_moduleLowerShriek` and
  `faithful_moduleLowerShriek`.
* `crisModuleInverseImage_obj_val_obj` — the sections of the general inverse image, so that the
  construction is pinned down pointwise.
* `crisModulePullback_preservesFiniteLimits` and `crisModulePullback_preservesFiniteColimits` —
  **the general pullback of [Stacks, Tag 07MJ] is exact**, for every `g`, which the library had
  only for the open-immersion pullback.

## What is and is not proved

What is proved is unconditional in the situation: no affineness, no hypothesis on `g`, and no
appeal to [Stacks, Tag 07HP].

What is **not** proved — because it is **false** — is **exactness of the module-level `i_!`**,
that is, clause (6) of [Stacks, Tag 07IJ] at module coefficients.  Preservation of colimits is free
(`preservesColimits_moduleLowerShriek`, `i_!` being a left adjoint); preservation of finite
limits is not.  The abelian statement
`...CrystallineThickening.preservesFiniteLimits_lowerShriekAb` does not transfer by itself: the
comparison `Stacks.SheafOfModules.lowerShriekForgetComparison` between the module-level and the
abelian lower shriek is [Stacks, Tag 0798] and is **not** invertible in general — this is
`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LowerShriekForget.lean`), an explicit
counterexample.  The criterion that decides it,
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_iff`, asks for invertibility at every
extension by zero `j_{U!}𝒪_U` of the structure sheaf, and nothing here discharges that for the
crystalline inclusion.  So no `PreservesFiniteLimits (moduleLowerShriek S)` instance is declared
and nothing below asserts one.

**It is not merely unproved: it is false.**  Two things say so, and neither leaves room for a
cleverer argument from the formal properties of the inclusion.

*No soft route exists.*  `Stacks.SheafOfModules.lowerShriek_not_preservesFiniteLimits`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LowerShriekNotLeftExact.lean`) exhibits a functor
of sites that is continuous, cocontinuous, fully faithful and final, whose image covers the
target site (`CategoryTheory.GrothendieckTopology.CoversTop`, the crystalline instance of which
is `...CrystallineThickening.coversTop_ι`), with the identity structure map of sheaves of rings
and hence an invertible unit `id ⟶ i^{-1}i_!` — every formal property the inclusion of the small
crystalline site has — and whose module-level lower shriek does not preserve the monomorphism
`𝟙 + 𝟙` of the structure sheaf.  So exactness cannot follow from those properties, however they
are combined, and in particular not from `coversTop_ι`.

*The crystalline inclusion itself fails.*  Write `A_V = (i_!^{Ab}𝒪_{X/S})(V)` for the
presheaf-level abelian lower shriek of the structure sheaf at an object `V` of `CRIS(X/S)`, a
colimit over the costructured-arrow category `I_V` of the objects of `Cris(X/S)` under `V`.
Because the tensor product commutes with colimits in both variables, the presheaf underlying `i_!M`
is `V ↦ (i_!^{Ab}M)(V) ⊗_{A_V} 𝒪_{X/S}(V)`, so `i_!` on modules is exact exactly when `𝒪_{X/S}(V)`
is flat over `A_V` locally in `V`; the abelian factor is exact by
`...CrystallineThickening.preservesFiniteLimits_lowerShriekAb`.  Take `p = 2`,
`S = S₀ = X = Spec 𝔽₂` with `I = 0`, and the object `V = (𝔸¹, T, δ)` of `CRIS(X/S)` with
`Γ(T) = 𝔽₂[x][t]/(t²)`, divided power ideal `(t)` carrying the trivial divided powers of a
square-zero ideal in characteristic `2`.  Every object of `Cris(X/S)` has `U' = Spec 𝔽₂` and so
ambient ring `B = 𝔽₂ ⊕ J` with `J` a nil divided power ideal, and a morphism `V ⟶ i(W)` sends `J`
into `(t)`; hence every such morphism factors uniquely through the object `W₀` of `Cris(X/S)` with
ambient ring `R = 𝔽₂ ⊕ (t) ⊆ Γ(T)` and the restricted divided powers, which is therefore a terminal
object of `I_V`.  So `A_V = R`, and the comparison is the multiplication `𝒪(W₀) ⊗_R Γ(T) ⟶ Γ(T)` of
the divided power ideal subsheaf `𝒥 = ker(𝒪_{X/S} ⟶ Ō)`: since `(t)² = 0`, `(t)` is an
`R/(t) = 𝔽₂`-module and `(t) ⊗_R Γ(T) = 𝔽₂[x] ⊗_{𝔽₂} 𝔽₂[x]`, which maps onto `(t) ≅ 𝔽₂[x]` with a
huge kernel — `t ⊗ x - tx ⊗ 1` is a nonzero element of it, and it stays nonzero on every nonempty
Zariski open of `T`, since `x` is non-constant there, so it survives sheafification.  Thus
`i_!𝒥 ⟶ i_!𝒪_{X/S}` is not injective and `moduleLowerShriek S` does not preserve monomorphisms.
(That computation is mathematics, not Lean: it would need a concrete `GlobalCrystallineSituation`
and the explicit colimit formula for the presheaf-level pullback of modules, neither of which is in
the library.)

The consequence for the chapter is that any route through "`i_!` is exact at module coefficients"
is closed, including the three the base change map and [Stacks, Tag 07N5] were expected to take:
exactness of `crisModuleInverseImage`, preservation of injectives by `i_X^{-1}` (which is
equivalent to exactness of `i_!`), and invertibility of the [Stacks, Tag 05T2] map for
`i^{-1} ⋙ Γ`.  What survives is the other side of the retraction: `i^{-1}` is exact
unconditionally, so `i_*` on modules preserves injectives, and comparisons of derived global
sections should be sought through `i_*` and through acyclicity of `i^{-1}I`, not through `i_!`.

The extension of scalars is **exactly** the factor that fails, and the other one is settled
here:
`crisModulePullback_preservesFiniteLimits` and `crisModulePullback_preservesFiniteColimits`
prove that `...SmallSite.crisModulePullback` is exact for every `g`, matching what
`...SmallSite.smallChangeBaseModulePullback_preservesFiniteLimits` and
`...smallChangeBaseModulePullback_preservesFiniteColimits` give in the open-immersion case.  So
`crisModuleInverseImage` preserves finite colimits unconditionally
(`crisModuleInverseImage_preservesFiniteColimits`), and the single thing between it and
exactness is preservation of finite limits by `moduleLowerShriek`, which does not hold.

So the base change map of [Stacks, Tag 07MS] for a general `g` is not built by deriving
`f_cris^*` on the small sites.  It is built on ringed topoi, as
`...SmallSite.crisSheafBaseChangeMap` (`SmallSite/BaseChangeMapSheaf07MS.lean`), whose last step
is `Rτ_*` of the comparison `Lf_cris^* ⟶ f_cris^*`, and read on global sections as
`...SmallSite.crisGlobalBaseChangeMap`.
`crisModuleInverseImage` below is the pullback `F` of that tag and carries its `@[stacks 07MS]`
attribute; no `@[stacks 07MU]` attribute is placed.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### Modules on the big crystalline site -/

/-- **The category of sheaves of `𝒪_{X/S}`-modules on the big crystalline site `CRIS(X/S)`**, at
the module universe `u + 1` of this chapter and with the structure sheaf left at `RingCat.{u}`.
It is the target of the module-level lower shriek, and the big-site twin of
`Crystalline.GlobalCrystallineSituation.SmallSite.ModuleSheaf`. -/
abbrev BigModuleSheaf := SheafOfModules.{u + 1} (crystallineStructureSheaf S)

/-- Sheafification of abelian presheaves on the **big** crystalline site inverts exactly the
locally bijective morphisms, with the coefficients at the universe `u + 1` of the objects of the
site.  Together with `...SmallSite.instHasSheafifyBigAddCommGrpCat` this is what makes the
module-level lower shriek exist, and what makes `BigModuleSheaf` abelian. -/
instance instWEqualsLocallyBijectiveBigAddCommGrpCat :
    (topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u + 1} _

/-- **Sheaves of `𝒪_{X/S}`-modules on the big crystalline site form an abelian category** at the
raised module universe, exactly as on the small site. -/
instance instAbelianBigModuleSheaf : Abelian (BigModuleSheaf S) :=
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian.{u + 1, u, u, u}
    (crystallineStructureSheaf S)

/-- **Sheaves of `𝒪_{X/S}`-modules on the big crystalline site form a Grothendieck abelian
category** at the universe `u + 1`. -/
instance instIsGrothendieckAbelianBigModuleSheaf :
    IsGrothendieckAbelian.{u + 1} (BigModuleSheaf S) :=
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, u}
    (crystallineStructureSheaf S)

/-- **Sheaves of `𝒪_{X/S}`-modules on the big crystalline site have enough injectives**, so their
cohomology can be computed by injective resolutions. -/
instance instEnoughInjectivesBigModuleSheaf : EnoughInjectives (BigModuleSheaf S) :=
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, u}
    (crystallineStructureSheaf S)

/-! ### The lower shriek -/

/-- **`i^{-1}𝒪_{X/S} = 𝒪_{X/S}`**: restricting the structure sheaf of `CRIS(X/S)` along the
inclusion of the small crystalline site gives the structure sheaf of `Cris(X/S)` on the nose.
This is the sheaf-level form of `...SmallSite.ι_op_comp_crisRing`, and it is what identifies the
source of the general lower shriek with this chapter's `ModuleSheaf`. -/
theorem inverseImageRing_eq_structureSheaf :
    Stacks.SheafOfModules.inverseImageRing (smallTopology S) (topology S)
        (CrystallineThickening.ι S) (crystallineStructureSheaf S) = structureSheaf S :=
  rfl

/-- **Restriction of modules from `CRIS(X/S)` to `Cris(X/S)` is the inverse image of the general
construction.**  `...SmallSite.crisRestrictModules` is `SheafOfModules.pushforward` of the
identity comparison of structure sheaves, which is exactly
`Stacks.SheafOfModules.inverseImage` for the inclusion; so the adjunction built below is an
adjunction for the functor the chapter already uses. -/
theorem crisRestrictModules_eq_inverseImage :
    crisRestrictModules.{u + 1} S =
      Stacks.SheafOfModules.inverseImage.{u + 1} (smallTopology S) (topology S)
        (CrystallineThickening.ι S) (crystallineStructureSheaf S) :=
  rfl

/-- **Stacks Project, Tag 07IJ, at module coefficients: the lower shriek
`i_! : Mod(𝒪_{X/S} on Cris(X/S)) ⥤ Mod(𝒪_{X/S} on CRIS(X/S))`** along the inclusion of the small
crystalline site into the big one.

It is `Stacks.SheafOfModules.lowerShriek` ([Stacks, Tag 0797]) for the inclusion: a sheaf of
modules on `Cris(X/S)` is pushed forward as a presheaf of modules along `i.op` and the result is
sheafified for the big crystalline topology.  The inclusion is continuous and cocontinuous by
`...SmallSite.instIsContinuousι` and `...SmallSite.instIsCocontinuousι` of
`SmallSite/BigComparison.lean`, both unconditional, and the sheafification the construction needs
is of `AddCommGrpCat.{u + 1}`-valued presheaves on the big site, which is
`...SmallSite.instHasSheafifyBigAddCommGrpCat`; see the module docstring, which corrects the
record that this was unavailable. -/
@[stacks 07IJ "the lower shriek i_! at module coefficients"]
def moduleLowerShriek : ModuleSheaf S ⥤ BigModuleSheaf S :=
  Stacks.SheafOfModules.lowerShriek.{u + 1} (smallTopology S) (topology S)
    (CrystallineThickening.ι S) (crystallineStructureSheaf S)

/-- **Stacks Project, Tag 07IJ, at module coefficients: `i_! ⊣ i^{-1}`.**  The module-level lower
shriek is left adjoint to the restriction `...SmallSite.crisRestrictModules` of modules from
`CRIS(X/S)` to `Cris(X/S)`. -/
@[stacks 07IJ "i_! is left adjoint to i^{-1} on sheaves of modules"]
def moduleLowerShriekAdjunction : moduleLowerShriek S ⊣ crisRestrictModules.{u + 1} S :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1} (smallTopology S) (topology S)
    (CrystallineThickening.ι S) (crystallineStructureSheaf S)

/-- Restriction of modules from `CRIS(X/S)` to `Cris(X/S)` is a right adjoint, the module-level
lower shriek being its left adjoint. -/
instance isRightAdjoint_crisRestrictModules : (crisRestrictModules.{u + 1} S).IsRightAdjoint :=
  (moduleLowerShriekAdjunction S).isRightAdjoint

/-- Restriction of modules from `CRIS(X/S)` to `Cris(X/S)` is additive: it leaves the sections
alone, so addition of morphisms is computed in the same groups on both sides. -/
instance crisRestrictModulesSucc_additive : (crisRestrictModules.{u + 1} S).Additive where
  map_add := rfl

/-- The module-level lower shriek is additive, being a left adjoint between additive
categories. -/
instance moduleLowerShriek_additive : (moduleLowerShriek S).Additive :=
  (moduleLowerShriekAdjunction S).left_adjoint_additive

/-- **The module-level `i_!` preserves all colimits**, being a left adjoint.  This is the half of
clause (6) of [Stacks, Tag 07IJ] that is free; the other half, preservation of finite limits, is
false — see the module docstring. -/
instance preservesColimits_moduleLowerShriek :
    PreservesColimitsOfSize.{u + 1, u + 1} (moduleLowerShriek S) :=
  (moduleLowerShriekAdjunction S).leftAdjoint_preservesColimits

/-- **Stacks Project, Tag 07IJ: the formula `i^{-1}i_! = id`, at module coefficients.**  The unit
of `i_! ⊣ i^{-1}` on sheaves of modules is an isomorphism.

The inclusion `...CrystallineThickening.ι` is fully faithful, continuous and cocontinuous, and
the comparison of structure sheaves is the identity, so this is
`SheafOfModules.isIso_unit_of_isIso_coefficient`: in the adjoint triple `i_! ⊣ i^{-1} ⊣ i_*` the
unit of the left-hand adjunction is invertible exactly when the counit of the right-hand one is,
and the latter is full faithfulness of the direct image of modules along a fully faithful functor
of sites.  No model of `i_!` enters that argument, so this holds of the one built above. -/
@[stacks 07IJ "i^{-1} i_! = id on sheaves of modules"]
theorem isIso_moduleLowerShriekAdjunction_unit :
    IsIso (moduleLowerShriekAdjunction S).unit :=
  SheafOfModules.isIso_unit_of_isIso_coefficient.{u, u, u, u, u + 1, u + 1}
    (CrystallineThickening.ι S) (smallTopology S) (topology S) (crystallineStructureSheaf S)
    (𝟙 _) (moduleLowerShriekAdjunction S)

/-- **`i^{-1}i_! = id` as an isomorphism of functors**, the content of
`isIso_moduleLowerShriekAdjunction_unit` in the form a composite uses. -/
def moduleLowerShriekUnitIso :
    𝟭 (ModuleSheaf S) ≅ moduleLowerShriek S ⋙ crisRestrictModules.{u + 1} S :=
  haveI := isIso_moduleLowerShriekAdjunction_unit S
  asIso (moduleLowerShriekAdjunction S).unit

/-- **The module-level `i_!` is fully faithful**, its unit being invertible. -/
def fullyFaithfulModuleLowerShriek : (moduleLowerShriek S).FullyFaithful :=
  haveI := isIso_moduleLowerShriekAdjunction_unit S
  (moduleLowerShriekAdjunction S).fullyFaithfulLOfIsIsoUnit

/-- The module-level `i_!` is full. -/
instance full_moduleLowerShriek : (moduleLowerShriek S).Full :=
  (fullyFaithfulModuleLowerShriek S).full

/-- The module-level `i_!` is faithful. -/
instance faithful_moduleLowerShriek : (moduleLowerShriek S).Faithful :=
  (fullyFaithfulModuleLowerShriek S).faithful

/-! ### The inverse image of modules along `f_cris`, for an arbitrary `g` -/

variable {S}
variable {S' : GlobalCrystallineSituation.{u}}

/-- **`f_cris^{-1}` on sheaves of modules, in the generality of [Stacks, Tag 07MJ]**: no
hypothesis whatever on `g : X ⟶ X'`, in particular not that it is an open immersion, so this
covers the hypothesis `X = X' ×_{S'₀} S₀` of [Stacks, Tag 07MU](4).

It is the composite of the two legs of [Stacks, Tag 07IK]'s
`f_cris = π_{X'} ∘ f_CRIS ∘ i_X`: the module-level `i_{X', !}` of [Stacks, Tag 07IJ] carries a
sheaf of `𝒪_{X'/S'}`-modules on `Cris(X'/S')` to the big site `CRIS(X'/S')`, and
`...SmallSite.crisModulePullback` restricts it along `Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')`, a
functor of sites that exists for every `g`.

Where `...SmallSite.smallChangeBaseModulePullback` applies — that is, for `g` an open immersion,
the generality of [Stacks, Tag 07KL] — the two agree, by
`crisModuleInverseImageIsoSmallChangeBase`.

This is the pullback `F = f_cris^*F'` of [Stacks, Tag 07MS]; the base change map of that tag,
`L(S ⟶ S')^*Rτ_{X'/S', *}F' ⟶ Rτ_{X/S, *}F`, is `...SmallSite.crisSheafBaseChangeMap`, and on
global sections `...SmallSite.crisGlobalBaseChangeMap`. -/
@[stacks 07MS "the pullback F = f_cris^* F' of an O_{X'/S'}-module F', for an arbitrary
morphism g : X ⟶ X'"]
def crisModuleInverseImage (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    ModuleSheaf S' ⥤ ModuleSheaf S :=
  moduleLowerShriek S' ⋙ crisModulePullback.{u + 1} f g h

/-- **The sections of the general inverse image.**  Over an object `(U, T, δ)` of `Cris(X/S)`
they are the sections of `i_{X', !}F'` over the image of `(U, T, δ)` under change of divided
power base — the same ambient scheme `T`, with `U ⟶ X ⟶ X'` and `T ⟶ S ⟶ S'` as its structure
maps.  So the construction is pinned down pointwise and is not vacuous. -/
theorem crisModuleInverseImage_obj_val_obj (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (F' : ModuleSheaf S') (A : (CrystallineThickening S)ᵒᵖ) :
    (((crisModuleInverseImage f g h).obj F').val.obj A : Type (u + 1)) =
      (((moduleLowerShriek S').obj F').val.obj
        (op ((changeBase S S' f g h).obj A.unop.obj)) : Type (u + 1)) :=
  rfl

/-- The general inverse image, split along the open-immersion pullback.  For `g` an open
immersion the restriction `Cris(X/S) ⥤ CRIS(X'/S')` factors through `Cris(X'/S')`, so
`...SmallSite.crisModulePullback` is `i_{X'}^{-1}` followed by
`...SmallSite.smallChangeBaseModulePullback`; this is that factorization composed with
`i_{X', !}`, and it holds on the nose. -/
theorem crisModuleInverseImage_eq_comp (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    crisModuleInverseImage f g h =
      (moduleLowerShriek S' ⋙ crisRestrictModules.{u + 1} S') ⋙
        smallChangeBaseModulePullback S S' f g h :=
  rfl

/-- **The general inverse image extends the open-immersion pullback.**  For `g` an open immersion
`crisModuleInverseImage` is isomorphic to
`...SmallSite.smallChangeBaseModulePullback`, the pullback of [Stacks, Tag 07MS], so the general
construction is a generalisation and not a second notion.

The isomorphism is `i^{-1}i_{X', !} = id`, that is
`isIso_moduleLowerShriekAdjunction_unit`, whiskered with the open-immersion pullback; the
factorization it is whiskered into, `crisModuleInverseImage_eq_comp`, is an equality. -/
def crisModuleInverseImageIsoSmallChangeBase (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    crisModuleInverseImage f g h ≅ smallChangeBaseModulePullback S S' f g h :=
  eqToIso (crisModuleInverseImage_eq_comp f g h) ≪≫
    Functor.isoWhiskerRight (moduleLowerShriekUnitIso S').symm
      (smallChangeBaseModulePullback S S' f g h) ≪≫
    (smallChangeBaseModulePullback S S' f g h).leftUnitor

/-- The general pullback of modules is additive: it leaves the sections alone. -/
instance crisModulePullback_additive (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (crisModulePullback.{u + 1} f g h).Additive where
  map_add := rfl

/-- **`Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')` is cocontinuous**, for *every* `g : X ⟶ X'`: the
inclusion of the small crystalline site into the big one is cocontinuous ([Stacks, Tag 07IJ])
and so is change of divided power base on the big sites ([Stacks, Tag 07IC]), neither with any
hypothesis on `g`.  This is the companion of `...SmallSite.isContinuous_ι_comp_changeBase`, and
it is what makes the general pullback exact. -/
instance isCocontinuous_ι_comp_changeBase (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (CrystallineThickening.ι S ⋙ changeBase S S' f g h).IsCocontinuous
      (smallTopology S) (topology S') :=
  isCocontinuous_comp (CrystallineThickening.ι S) (changeBase S S' f g h)
    (smallTopology S) (topology S)

/-- **The general pullback preserves finite limits.**  It is a direct image of sheaves of
modules along a continuous functor of sites, hence a right adjoint; this is the left exact half
of [Stacks, Tag 04BD](2). -/
instance crisModulePullback_preservesFiniteLimits (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    PreservesFiniteLimits (crisModulePullback.{u + 1} f g h) :=
  SheafOfModules.preservesFiniteLimits_pushforward _

/-- **The general pullback preserves finite colimits**, because the composite
`Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')` is cocontinuous as well as continuous, so restriction
along it commutes with sheafification.  This is the right exact half of [Stacks, Tag 04BD](2).

Together with the previous instance this says the general pullback is **exact**, for every `g`,
which is the property the open-immersion pullback has by
`...SmallSite.smallChangeBaseModulePullback_preservesFiniteLimits` and
`...smallChangeBaseModulePullback_preservesFiniteColimits`.  So the exactness that a general-`g`
base change map would need sits entirely in the other factor, the module-level `i_!`; see the
module docstring. -/
instance crisModulePullback_preservesFiniteColimits (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    PreservesFiniteColimits (crisModulePullback.{u + 1} f g h) :=
  (SheafOfModules.exactFunctor_pushforward_of_isCocontinuous
    (CrystallineThickening.ι S ⋙ changeBase S S' f g h)
    (crisChangeBaseStructureHom f g h)).2

/-- **The general inverse image preserves finite colimits**, both of its factors doing so: the
module-level `i_!` is a left adjoint and the general pullback is exact. -/
instance crisModuleInverseImage_preservesFiniteColimits (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    PreservesFiniteColimits (crisModuleInverseImage f g h) :=
  inferInstanceAs
    (PreservesFiniteColimits (moduleLowerShriek S' ⋙ crisModulePullback.{u + 1} f g h))

/-- The general inverse image is additive, being a composite of two additive functors. -/
instance crisModuleInverseImage_additive (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (crisModuleInverseImage f g h).Additive :=
  inferInstanceAs (moduleLowerShriek S' ⋙ crisModulePullback.{u + 1} f g h).Additive

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
