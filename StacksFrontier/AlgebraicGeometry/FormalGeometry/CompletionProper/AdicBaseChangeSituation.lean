module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.FlatBaseChangeAlgebraization

/-!
# The base change of a proper morphism along `Spec B ^∧ ⟶ Spec B`

Let `B` be a Noetherian ring, `J ⊆ B` an ideal, `g = Spec B ^∧ ⟶ Spec B` the morphism induced by
the completion map, and `π : X' ⟶ Spec B` a proper morphism. The second paragraph of the proof of
Stacks 088B replaces `B` by `B ^∧`, and to do so it needs the base change

```
X'' --g'--> X'
|           |
π'          π
v           v
Spec B ^∧ -g-> Spec B
```

together with the comparison of the `J`-adic data over `Spec B` with the `J B ^∧`-adic data over
`Spec B ^∧`. This file builds that square and the comparison of the levels.

`Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison`
(`CompletionProper/FlatBaseChangeAlgebraization.lean`) reduces the whole of that paragraph to two
squares `hδ` and `hγ` for an *arbitrary* proper `π' : X'' ⟶ Spec B ^∧` with comparisons `ι` and
`θ`. Its module docstring records that nothing in the library builds `π'` as a base change of `π`,
its properness, or the identification of the levels. Those are what is built here.

## Main results

* `Stacks.Algebraization.cokernelIsoOfCompEqZeroIff` — two morphisms into a common object killed
  by exactly the same morphisms out of that object have the same cokernel, compatibly with the
  two quotient projections (`Stacks.Algebraization.π_comp_cokernelIsoOfCompEqZeroIff_hom`).
* `Stacks.Algebraization.pullbackIdealPowerQuotientIso` — **pullback commutes with the
  ideal-power quotient**: `f^*(M / 𝒥 ⁿ M) ≅ (f^*M) / ℐ ⁿ (f^*M)` for `ℐ = f^{-1}𝒥 𝒪_X`, for an
  arbitrary morphism of schemes and an arbitrary sheaf of modules, carrying the pullback of one
  quotient projection to the other
  (`Stacks.Algebraization.map_π_comp_pullbackIdealPowerQuotientIso_hom`). Pullback is a left
  adjoint, hence preserves the cokernel presenting the quotient, and
  `Stacks.Algebraization.pullback_idealPowerMultiple_comp_eq_zero_iff` identifies the resulting
  cokernel with the one presenting `(f^*M) / ℐ ⁿ (f^*M)`.
* `Stacks.Algebraization.adicBaseChange`, `…adicBaseChangeFst` and `…adicBaseChangeMap` —
  **the base change itself**: the scheme `X'' = X' ×_{Spec B} Spec B ^∧`, the projection
  `g' : X'' ⟶ X'` and the base-changed morphism `π' : X'' ⟶ Spec B ^∧`, with
  `…adicBaseChange_isPullback` the cartesian square and `…adicBaseChange_w` its commutativity.
* `Stacks.Algebraization.isProper_adicBaseChangeMap` — **`π'` is proper.** This is
  `AlgebraicGeometry.IsProper.isStableUnderBaseChange`, already in Mathlib; nothing is proved
  here beyond instantiating it at this square.
* `Stacks.Algebraization.isNoetherian_adicBaseChange` — `X''` is Noetherian, `π'` being proper
  over `Spec B ^∧` and `B ^∧` being Noetherian (`AdicCompletion.isNoetherianRing`).
* `Stacks.Algebraization.comap_comap_adicBaseChangeMap` — the inverse image of
  `J B ^∧ 𝒪_{Spec B ^∧}` along `π'` is the inverse image of `ℐ = π^{-1}J 𝒪_{X'}` along `g'`.
* `Stacks.Algebraization.pullbackIdealPowerQuotientIsoOfEq` and
  `…map_π_comp_pullbackIdealPowerQuotientIsoOfEq_hom` — the same with the ideal sheaf on the
  source a binder constrained to equal `𝒥.comap f`, which is the form in which it applies when
  that ideal sheaf arises as the inverse image of another one.
* `Stacks.Algebraization.adicBaseChangeIdealPowerQuotientIso` — **the identification of the
  levels**: `g'^*(𝓕 / ℐ ⁿ 𝓕) ≅ 𝓕' / ℐ' ⁿ 𝓕'` for `𝓕' = g'^*𝓕`.
* `Stacks.Algebraization.adicBaseChangePushforwardIso` — **Cohomology of Schemes 02KH in degree
  zero for this square**: `g^*(π_*F) ≅ π'_*(g'^*F)` for a quasi-coherent `F`.
* `Stacks.Algebraization.adicBaseChangeLevelComparison` — **the `θ` of the reduction**, the
  comparison `π'_*(𝓕' / ℐ' ⁿ⁺¹ 𝓕') ⟶ g^*(π_*(𝓕 / ℐ ⁿ⁺¹ 𝓕))` of the two direct images of the
  levels, built from the two items above.
* `Stacks.Algebraization.adicBaseChangeProperPushforwardIso` and
  `…adicBaseChangeCompletedComparison` — **the `ι` of the reduction**, the comparison
  `(π'_*𝓕') ^∧ ⟶ g^*((π_*𝓕) ^∧)` of the two completed direct images, 02KH at `𝓕` itself
  completed and then read through `Stacks.Coherent.completionPullbackIso` (Stacks 0887).
* `Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeSquares` — **the
  second paragraph of the proof of Stacks 088B at the actual base change**:
  `Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison` with `X''`,
  `π'`, `𝓕'`, `ι` and `θ` all supplied, so that the only binders left are the base-changed `β'`
  and the two squares `hδ` and `hγ` written at those specific `ι` and `θ`.

## What is not here

**The two squares `hδ` and `hγ` are not discharged**; they are the binders of
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_adicBaseChangeSquares`, now written
at the `ι` and `θ` built here rather than at arbitrary ones.

`hγ` *cannot* be a theorem while `β'` is a binder: it is the statement that `ι` and `θ` carry the
`γ` of the situation over `Spec B ^∧` built from `β'` to the pullback of the `γ` built from `β`,
and for a `β'` unrelated to `β` that is simply false. Discharging it needs `β'` constructed as
the base change of `β`, which is `β` pulled back along `g'` read through
`Stacks.Coherent.completionPullbackIso` at `g'` and the composition
`g'^*π^* = (g' ≫ π)^* = (π' ≫ g)^* = π'^*g^*` of pullbacks of coherent adic systems; that
composition isomorphism is not in this library.

`hδ` mentions no `β` and is a genuine theorem, provable from
`Stacks.Algebraization.map_π_comp_pullbackIdealPowerQuotientIsoOfEq_hom`,
`Stacks.Coherent.directImageQuotientComparison_π`,
`Stacks.Algebraization.completionProjection_comp_eqToHom`,
`Stacks.Algebraization.completionFunctor_map_quotient`,
`Stacks.Coherent.completionProjection_completionPullbackComparison` and
`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality`, after cancelling the
epimorphism `Stacks.Algebraization.epi_completionProjection`. It is not proved here for a
mechanical reason: the manipulation happens in `(X' ×_{Spec B} Spec B ^∧).Modules`, and the
kernel exhausts its reduction budget on any statement that spells a `cokernel` in that category
out in its type — a specialized restatement of the normalization of
`Stacks.Algebraization.adicBaseChangeIdealPowerQuotientIso` was removed for exactly that reason.

No `stacks` attribute is attached: nothing here is a statement of the source, and the attribution
for the flat base change of the source's second paragraph is already on
`Stacks.Algebraization.coherentAdicPullback_adicCompletionSpecMap_isEquivalence`.

## References

* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 0316](https://stacks.math.columbia.edu/tag/0316)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance] Stacks.Algebraization.zeroHomOfSheafOfModules

namespace Stacks.Algebraization

/-! ### Two presentations of one quotient -/

/-- Two morphisms into a common object which are killed by exactly the same morphisms out of that
object have the same cokernel. -/
public def cokernelIsoOfCompEqZeroIff {C : Type*} [Category* C] [HasZeroMorphisms C]
    {A A' M : C} (a : A ⟶ M) (a' : A' ⟶ M) [HasCokernel a] [HasCokernel a']
    (h : ∀ {N : C} (b : M ⟶ N), a ≫ b = 0 ↔ a' ≫ b = 0) :
    cokernel a ≅ cokernel a' where
  hom := cokernel.desc a (cokernel.π a') ((h _).mpr (cokernel.condition a'))
  inv := cokernel.desc a' (cokernel.π a) ((h _).mp (cokernel.condition a))
  hom_inv_id := by
    refine (cancel_epi (cokernel.π a)).1 ?_
    rw [Category.comp_id, ← Category.assoc, cokernel.π_desc, cokernel.π_desc]
  inv_hom_id := by
    refine (cancel_epi (cokernel.π a')).1 ?_
    rw [Category.comp_id, ← Category.assoc, cokernel.π_desc, cokernel.π_desc]

/-- The identification of two presentations of one quotient carries one quotient projection to
the other. -/
public theorem π_comp_cokernelIsoOfCompEqZeroIff_hom {C : Type*} [Category* C]
    [HasZeroMorphisms C] {A A' M : C} (a : A ⟶ M) (a' : A' ⟶ M) [HasCokernel a] [HasCokernel a']
    (h : ∀ {N : C} (b : M ⟶ N), a ≫ b = 0 ↔ a' ≫ b = 0) :
    cokernel.π a ≫ (cokernelIsoOfCompEqZeroIff a a' h).hom = cokernel.π a' :=
  cokernel.π_desc _ _ _

/-! ### Pullback and the ideal-power quotient -/

/-- Pullback of sheaves of modules is a left adjoint, hence preserves all colimits. -/
public theorem preservesColimits_modulesPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesColimits (Scheme.Modules.pullback f) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits

attribute [local instance] preservesColimits_modulesPullback

/-- **Pullback commutes with the ideal-power quotient.** For `f : X ⟶ Y`, a quasi-coherent sheaf
of ideals `𝒥` on `Y` with inverse image `ℐ = f^{-1}𝒥 𝒪_X`, and an `𝒪_Y`-module `M`,

`f^*(M / 𝒥 ⁿ M) ≅ (f^*M) / ℐ ⁿ (f^*M)`.

Pullback is a left adjoint, so it carries the cokernel presentation of `M / 𝒥 ⁿ M` to the
cokernel of `f^*(𝒥 ⁿ M) ⟶ f^*M`; that morphism and the inclusion `ℐ ⁿ (f^*M) ⟶ f^*M` are killed
by the same morphisms out of `f^*M`
(`Stacks.Algebraization.pullback_idealPowerMultiple_comp_eq_zero_iff`), so they have the same
cokernel. -/
public def pullbackIdealPowerQuotientIso {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData)
    (n : ℕ) (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj (idealPowerQuotient J n M) ≅
      idealPowerQuotient (J.comap f) n ((Scheme.Modules.pullback f).obj M) :=
  PreservesCokernel.iso (Scheme.Modules.pullback f) (idealPowerMultiple J n M).ι ≪≫
    cokernelIsoOfCompEqZeroIff
      ((Scheme.Modules.pullback f).map (idealPowerMultiple J n M).ι)
      (idealPowerMultiple (J.comap f) n ((Scheme.Modules.pullback f).obj M)).ι
      fun b => pullback_idealPowerMultiple_comp_eq_zero_iff f J n M b

/-- **The normalization of `Stacks.Algebraization.pullbackIdealPowerQuotientIso`**: it carries the
pullback of the quotient projection of `M` to the quotient projection of `f^*M`. The projection
being an epimorphism, this determines the isomorphism. -/
public theorem map_π_comp_pullbackIdealPowerQuotientIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (n : ℕ) (M : Y.Modules) :
    (Scheme.Modules.pullback f).map
          (cokernel.π (C := Y.Modules) (idealPowerMultiple J n M).ι) ≫
        (pullbackIdealPowerQuotientIso f J n M).hom =
      cokernel.π (C := X.Modules)
        (idealPowerMultiple (J.comap f) n ((Scheme.Modules.pullback f).obj M)).ι :=
  by
  rw [pullbackIdealPowerQuotientIso, Iso.trans_hom, ← Category.assoc]
  erw [PreservesCokernel.π_iso_hom]
  exact π_comp_cokernelIsoOfCompEqZeroIff_hom _ _ _

/-- `Stacks.Algebraization.pullbackIdealPowerQuotientIso` with the ideal sheaf on the source a
binder constrained to equal `𝒥.comap f`, so that it can be read at an ideal sheaf arising as the
inverse image of another one. -/
public def pullbackIdealPowerQuotientIsoOfEq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) {I : X.IdealSheafData} (h : J.comap f = I) (n : ℕ) (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj (idealPowerQuotient J n M) ≅
      idealPowerQuotient I n ((Scheme.Modules.pullback f).obj M) :=
  pullbackIdealPowerQuotientIso f J n M ≪≫
    eqToIso (congrArg
      (fun K => idealPowerQuotient K n ((Scheme.Modules.pullback f).obj M)) h)

/-- The normalization of `Stacks.Algebraization.pullbackIdealPowerQuotientIsoOfEq`, as for
`Stacks.Algebraization.map_π_comp_pullbackIdealPowerQuotientIso_hom`. -/
public theorem map_π_comp_pullbackIdealPowerQuotientIsoOfEq_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) {I : X.IdealSheafData} (h : J.comap f = I) (n : ℕ) (M : Y.Modules) :
    (Scheme.Modules.pullback f).map
          (cokernel.π (C := Y.Modules) (idealPowerMultiple J n M).ι) ≫
        (pullbackIdealPowerQuotientIsoOfEq f J h n M).hom =
      cokernel.π (C := X.Modules)
        (idealPowerMultiple I n ((Scheme.Modules.pullback f).obj M)).ι := by
  subst h
  exact (congrArg
      (fun k => (Scheme.Modules.pullback f).map
        (cokernel.π (C := Y.Modules) (idealPowerMultiple J n M).ι) ≫ k)
      (Category.comp_id (pullbackIdealPowerQuotientIso f J n M).hom)).trans
    (map_π_comp_pullbackIdealPowerQuotientIso_hom f J n M)

/-! ### The base change of a proper morphism along `Spec B ^∧ ⟶ Spec B` -/

section BaseChange

variable (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B) {X' : Scheme.{u}}
  (π : X' ⟶ Spec (.of B))

/-- **The base change `X'' = X' ×_{Spec B} Spec B ^∧`.** -/
public abbrev adicBaseChange : Scheme.{u} := pullback π (adicCompletionSpecMap B J)

/-- **The projection `g' : X'' ⟶ X'`** of the base change, a base change of
`g = Spec B ^∧ ⟶ Spec B`. -/
public abbrev adicBaseChangeFst : adicBaseChange B J π ⟶ X' :=
  pullback.fst π (adicCompletionSpecMap B J)

/-- **The base-changed morphism `π' = π ×_{Spec B} Spec B ^∧ : X'' ⟶ Spec B ^∧`.** -/
public abbrev adicBaseChangeMap : adicBaseChange B J π ⟶ Spec (.of (AdicCompletion J B)) :=
  pullback.snd π (adicCompletionSpecMap B J)

omit [IsNoetherianRing B] in
/-- The defining square of the base change: `g' ≫ π = π' ≫ g`. -/
public theorem adicBaseChange_w :
    adicBaseChangeFst B J π ≫ π = adicBaseChangeMap B J π ≫ adicCompletionSpecMap B J :=
  pullback.condition

omit [IsNoetherianRing B] in
/-- The defining square of the base change is cartesian. -/
public theorem adicBaseChange_isPullback :
    IsPullback (adicBaseChangeFst B J π) (adicBaseChangeMap B J π) π
      (adicCompletionSpecMap B J) :=
  IsPullback.of_hasPullback π (adicCompletionSpecMap B J)

/-- **The base change of a proper morphism is proper**, so `π' : X'' ⟶ Spec B ^∧` is proper.

This is `AlgebraicGeometry.IsProper.isStableUnderBaseChange`, i.e. [Stacks, Tag 01W6]; nothing is
proved here. -/
public instance isProper_adicBaseChangeMap [IsProper π] : IsProper (adicBaseChangeMap B J π) :=
  IsProper.isStableUnderBaseChange.of_isPullback (adicBaseChange_isPullback B J π) inferInstance

/-- **The base change `X''` is Noetherian.** `π'` is proper, hence locally of finite type and
quasi-compact, and `Spec B ^∧` is Noetherian because `B ^∧` is a Noetherian ring
(`AdicCompletion.isNoetherianRing`, [Stacks, Tag 0316]). -/
public instance isNoetherian_adicBaseChange [IsProper π] : IsNoetherian (adicBaseChange B J π) :=
  { toIsLocallyNoetherian :=
      LocallyOfFiniteType.isLocallyNoetherian (adicBaseChangeMap B J π)
    toCompactSpace :=
      QuasiCompact.compactSpace_of_compactSpace (adicBaseChangeMap B J π) }

omit [IsNoetherianRing B] in
/-- **The two routes from `J 𝒪_{Spec B}` to an ideal sheaf on the base change agree.** The
inverse image of `J B ^∧ 𝒪_{Spec B ^∧}` along `π'` is the inverse image of `ℐ = π^{-1}J 𝒪_{X'}`
along `g'`, both being the inverse image of `J 𝒪_{Spec B}` along the two equal composites of the
cartesian square. -/
public theorem comap_comap_adicBaseChangeMap :
    ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap (adicBaseChangeMap B J π) =
      ((adicIdealSheaf B J).comap π).comap (adicBaseChangeFst B J π) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    adicBaseChange_w B J π]

/-- **The levels of the base change are the base changes of the levels.** For a sheaf of modules
`𝓕` on `X'`, writing `ℐ = π^{-1}J 𝒪_{X'}`, `𝓕' = g'^*𝓕` and `ℐ' = (π')^{-1}(J B ^∧) 𝒪_{X''}`,

`g'^*(𝓕 / ℐ ⁿ 𝓕) ≅ 𝓕' / ℐ' ⁿ 𝓕'`.

This is `Stacks.Algebraization.pullbackIdealPowerQuotientIso` along `g'` together with the
identification `Stacks.Algebraization.comap_comap_adicBaseChangeMap` of the two ideal sheaves on
`X''`. -/
public def adicBaseChangeIdealPowerQuotientIso (n : ℕ) (F : X'.Modules) :
    (Scheme.Modules.pullback (adicBaseChangeFst B J π)).obj
        (idealPowerQuotient ((adicIdealSheaf B J).comap π) n F) ≅
      idealPowerQuotient
        (((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap
          (adicBaseChangeMap B J π)) n
        ((Scheme.Modules.pullback (adicBaseChangeFst B J π)).obj F) :=
  pullbackIdealPowerQuotientIsoOfEq (adicBaseChangeFst B J π) ((adicIdealSheaf B J).comap π)
    (comap_comap_adicBaseChangeMap B J π).symm n F

/-! The normalization of `Stacks.Algebraization.adicBaseChangeIdealPowerQuotientIso` — that it
carries the pullback along `g'` of the quotient projection of `𝓕` to the quotient projection of
`𝓕' = g'^*𝓕` — is `Stacks.Algebraization.map_π_comp_pullbackIdealPowerQuotientIsoOfEq_hom` at
`g'`, since the identification *is* that generic isomorphism at `g'`. It is deliberately not
restated with the base change spelled into its type: the right-hand side's `cokernel.π` lives in
`(X' ×_{Spec B} Spec B ^∧).Modules`, and the kernel exhausts its reduction budget on that
category, so the generic statement is the one to use at the point of application. -/

end BaseChange

/-! ### The two comparisons of direct images over the base change -/

section Comparison

open Stacks.Coherent Stacks.AlgebraicGeometry.FlatBaseChange

variable (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B) {X' : Scheme.{u}}
  [IsNoetherian X'] (π : X' ⟶ Spec (.of B)) [IsProper π]

/-- **Cohomology of Schemes 02KH in degree zero for the base change along `Spec B ^∧ ⟶ Spec B`.**
For a quasi-coherent `𝒪_{X'}`-module `F`,

`g^*(π_*F) ≅ π'_*(g'^*F)`.

This is `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange` at the cartesian square
of `Stacks.Algebraization.adicBaseChange_isPullback`, an isomorphism by
`Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffine`: both bases are
affine, `g` is flat (`Stacks.Algebraization.flat_adicCompletionSpecMap`, Algebra 00MB) and `π` is
proper, hence quasi-compact and quasi-separated. -/
public def adicBaseChangePushforwardIso (F : X'.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pullback (adicCompletionSpecMap B J)).obj
        ((Scheme.Modules.pushforward π).obj F) ≅
      (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).obj
        ((Scheme.Modules.pullback (adicBaseChangeFst B J π)).obj F) :=
  haveI := flat_adicCompletionSpecMap B J
  haveI := isIso_pushforwardBaseChange_of_isAffine (adicBaseChange_isPullback B J π) F
  asIso (pushforwardBaseChange (adicBaseChange_isPullback B J π).w F)

omit [AlgebraicGeometry.IsNoetherian X'] in
/-- The isomorphism of Cohomology of Schemes 02KH is the canonical comparison. -/
public theorem adicBaseChangePushforwardIso_hom (F : X'.Modules) [F.IsQuasicoherent] :
    (adicBaseChangePushforwardIso B J π F).hom =
      pushforwardBaseChange (adicBaseChange_isPullback B J π).w F :=
  rfl

variable (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)

/-- The coherent `𝒪_{X''}`-module `𝓕' = g'^*𝓕`.

The body is the bare `Stacks.Coherent.pullbackCoherentModules` along `g'`, the Noetherianness of
the base change coming from the instance
`Stacks.Algebraization.isNoetherian_adicBaseChange` and not from a `haveI` written inside the
body. The two have the same value, but a `haveI` makes the body a `letFun`, so the abbrev does
not unfold to the spelling `(pullbackCoherentModules g').obj 𝓕` in which the general lemmas
about pullbacks of coherent modules and about the levels of a completion are stated; with the
`haveI` removed, `𝓕'` and that spelling are the same term, and the identifications a statement
mixing the two presentations needs are free. -/
public abbrev adicBaseChangeCoherent :
    AlgebraicGeometry.SheafOfModules.CoherentModules (adicBaseChange B J π).ringCatSheaf :=
  (pullbackCoherentModules (adicBaseChangeFst B J π)).obj 𝓕

/-- **The comparison `θ_n` of the two direct images of the levels.** At level `n`,

`π'_*(𝓕' / ℐ' ⁿ⁺¹ 𝓕') ⟶ g^*(π_*(𝓕 / ℐ ⁿ⁺¹ 𝓕))`,

the inverse of the direct image along `π'` of the identification
`Stacks.Algebraization.adicBaseChangeIdealPowerQuotientIso` of the levels followed by the inverse
of the degree-zero flat base change `Stacks.Algebraization.adicBaseChangePushforwardIso` at the
level `𝓕 / ℐ ⁿ⁺¹ 𝓕`.

This is the `θ` of
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison` at the actual
base change. -/
public def adicBaseChangeLevelComparison (n : ℕ) :
    (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).obj
        (idealPowerQuotient
          (((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap
            (adicBaseChangeMap B J π))
          (n + 1) (adicBaseChangeCoherent B J π 𝓕).obj) ⟶
      (Scheme.Modules.pullback (adicCompletionSpecMap B J)).obj
        ((Scheme.Modules.pushforward π).obj
          (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)) :=
  haveI : 𝓕.obj.IsCoherent := 𝓕.property
  haveI :
      (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsCoherent :=
    (Stacks.Coherent.coherentAnnihilatedBy_idealPowerQuotient
      ((adicIdealSheaf B J).comap π) n 𝓕.obj 𝓕.property).1
  haveI :
      (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  (Scheme.Modules.pushforward (adicBaseChangeMap B J π)).map
      (adicBaseChangeIdealPowerQuotientIso B J π (n + 1) 𝓕.obj).inv ≫
    (adicBaseChangePushforwardIso B J π
      (idealPowerQuotient ((adicIdealSheaf B J).comap π) (n + 1) 𝓕.obj)).inv

/-- **The identification of `π'_*𝓕'` with `g^*(π_*𝓕)` as coherent `𝒪_{Spec B ^∧}`-modules.**
`Stacks.Algebraization.adicBaseChangePushforwardIso` at `𝓕` itself, read in `Coh(𝒪_{Spec B ^∧})`.
-/
public def adicBaseChangeProperPushforwardIso :
    properPushforwardCoherent (adicBaseChangeMap B J π) (adicBaseChangeCoherent B J π 𝓕) ≅
      (pullbackCoherentModules (adicCompletionSpecMap B J)).obj
        (properPushforwardCoherent π 𝓕) :=
  haveI := isNoetherian_adicBaseChange B J π
  haveI : 𝓕.obj.IsCoherent := 𝓕.property
  haveI : 𝓕.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  ObjectProperty.isoMk _ (adicBaseChangePushforwardIso B J π 𝓕.obj).symm

/-- **The comparison `ι` of the two completed direct images.**

`(π'_*𝓕') ^∧ ⟶ g^*((π_*𝓕) ^∧)`

It is an isomorphism, assembled from two: the degree-zero flat base change
`π'_*𝓕' ≅ g^*(π_*𝓕)` of Cohomology of Schemes 02KH
(`Stacks.Algebraization.adicBaseChangeProperPushforwardIso`), completed along `J B ^∧ 𝒪`, and the
identification `(g^*𝒜) ^∧ ≅ g^*(𝒜 ^∧)` of completion with pullback
(`Stacks.Coherent.completionPullbackIso`, Stacks 0887, unconditional).

This is the `ι` of
`Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison` at the actual
base change. -/
public def adicBaseChangeCompletedComparison :
    ((completionFunctor (Spec (.of (AdicCompletion J B)))
          ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj
        (properPushforwardCoherent (adicBaseChangeMap B J π)
          (adicBaseChangeCoherent B J π 𝓕))).obj ⟶
      ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj
        ((completionFunctor (Spec (.of B)) (adicIdealSheaf B J)).obj
          (properPushforwardCoherent π 𝓕))).obj :=
  haveI := isNoetherian_adicBaseChange B J π
  (((completionFunctor (Spec (.of (AdicCompletion J B)))
        ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).map
      (adicBaseChangeProperPushforwardIso B J π 𝓕).hom) ≫
    (completionPullbackIso (adicCompletionSpecMap B J) (adicIdealSheaf B J)
      (properPushforwardCoherent π 𝓕)).hom).hom

/-! ### The second paragraph of Stacks 088B at the actual base change -/

/-- **The reduction of the second paragraph of the proof of Stacks 088B to the two squares `hδ`
and `hγ`, instantiated at the actual base change `π' = π ×_{Spec B} Spec B ^∧`.**

`Stacks.Algebraization.exists_isDirectImageCharacterized_of_baseChangeComparison` states that
reduction for an *arbitrary* proper `π' : X'' ⟶ Spec B ^∧` with arbitrary comparisons `ι` and
`θ`. Here `X''`, `π'`, `𝓕'`, `ι` and `θ` are the base change and the comparisons built in this
file:

* `X'' = X' ×_{Spec B} Spec B ^∧` with `π'` its second projection, proper by
  `AlgebraicGeometry.IsProper.isStableUnderBaseChange`;
* `𝓕' = g'^*𝓕`;
* `ι` the comparison `(π'_*𝓕') ^∧ ⟶ g^*((π_*𝓕) ^∧)` of
  `Stacks.Algebraization.adicBaseChangeCompletedComparison`, built from Cohomology of Schemes
  02KH in degree zero and Stacks 0887;
* `θ` the comparison of the direct images of the levels,
  `Stacks.Algebraization.adicBaseChangeLevelComparison`, built from the same 02KH at the level
  `𝓕 / ℐ ⁿ⁺¹ 𝓕` and the identification
  `Stacks.Algebraization.adicBaseChangeIdealPowerQuotientIso` of the levels.

So the binders that remain are the base-changed `β'` and the two squares `hδ` and `hγ` for these
specific `ι` and `θ`, and nothing else. -/
public theorem exists_isDirectImageCharacterized_of_adicBaseChangeSquares
    (G : CoherentAdicSystems (adicIdealSheaf B J))
    (β : (coherentAdicPullback π (adicIdealSheaf B J)).obj G ≅
      (completionFunctor X' ((adicIdealSheaf B J).comap π)).obj 𝓕)
    (β' : (coherentAdicPullback (adicBaseChangeMap B J π)
          ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj
        ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G) ≅
      (completionFunctor (adicBaseChange B J π)
        (((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)).comap
          (adicBaseChangeMap B J π))).obj (adicBaseChangeCoherent B J π 𝓕))
    (𝒦 : (Spec (.of (AdicCompletion J B))).IdealSheafData)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules
        (Spec (.of (AdicCompletion J B))).ringCatSheaf,
      ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G ≅
          (completionFunctor (Spec (.of (AdicCompletion J B)))
            ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (adicBaseChangeMap B J π)).unit.app 𝒜.obj)))
    (hδ : ∀ n : ℕ, (adicBaseChangeCompletedComparison B J π 𝓕).app (op n) ≫
          (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
            (eqToHom (completionFunctor_obj (Spec (.of B)) (adicIdealSheaf B J)
                (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π (adicIdealSheaf B J) (n + 1) 𝓕.obj) =
        (eqToHom (completionFunctor_obj (Spec (.of (AdicCompletion J B)))
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
              (properPushforwardCoherent (adicBaseChangeMap B J π)
                (adicBaseChangeCoherent B J π 𝓕)) n) ≫
            directImageQuotientComparison (adicBaseChangeMap B J π)
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J)) (n + 1)
              (adicBaseChangeCoherent B J π 𝓕).obj) ≫
          adicBaseChangeLevelComparison B J π 𝓕 n)
    (hγ : ∀ n : ℕ,
        (directImageComparison (adicBaseChangeMap B J π)
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
              ((coherentAdicPullback (adicCompletionSpecMap B J) (adicIdealSheaf B J)).obj G)
              (adicBaseChangeCoherent B J π 𝓕) β').app (op n) ≫
            eqToHom (pushforward_completion_obj (adicBaseChangeMap B J π)
              ((adicIdealSheaf B J).comap (adicCompletionSpecMap B J))
              (adicBaseChangeCoherent B J π 𝓕) n) ≫
            adicBaseChangeLevelComparison B J π 𝓕 n =
          (Scheme.Modules.pullback (adicCompletionSpecMap B J)).map
            ((directImageComparison π (adicIdealSheaf B J) G 𝓕 β).app (op n) ≫
              eqToHom (pushforward_completion_obj π (adicIdealSheaf B J) 𝓕 n))) :
    ∃ α : G.obj ⟶ ((completionFunctor (Spec (.of B)) (adicIdealSheaf B J)).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsDirectImageCharacterized π (adicIdealSheaf B J) G 𝓕 β α :=
  exists_isDirectImageCharacterized_of_baseChangeComparison B J π 𝓕 G β
    (adicBaseChangeMap B J π) (adicBaseChangeCoherent B J π 𝓕) β' 𝒦 hc
    (adicBaseChangeCompletedComparison B J π 𝓕) (adicBaseChangeLevelComparison B J π 𝓕) hδ hγ

end Comparison

end Stacks.Algebraization

end
