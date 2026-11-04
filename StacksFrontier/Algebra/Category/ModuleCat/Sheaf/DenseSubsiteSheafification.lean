module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification of presheaves of modules commutes with restriction, as functors

Let `G : C ⥤ D` be continuous and cocontinuous for topologies `J` on `C` and `K` on `D`, and
let `R` be a sheaf of rings on `(D, K)`. Restriction of sections along `G` carries presheaves
of `R`-modules to presheaves of modules over the restricted ring sheaf
(`Stacks.SheafOfModules.PushforwardSheafification.presheafPushforwardFunctor`) and sheaves to
sheaves (`sheafPushforwardFunctor`), and
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyIso` already identifies
the sheafification of a restricted presheaf with the restriction of its sheafification, **for
one presheaf at a time**. This file upgrades that objectwise isomorphism to a natural
isomorphism of functors,

`presheafPushforwardFunctor ⋙ sheafification ≅ sheafification ⋙ sheafPushforwardFunctor`,

and specializes it to a dense subsite, where it is the third and last factor needed for the
statement that the tensor product of sheaves of modules depends only on the ringed topos and
not on the site presenting it (Stacks 03DG, method (2)).

## Main definitions

* `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyNatIso`: the natural
  isomorphism. This is the main result.
* `Stacks.SheafOfModules.PushforwardSheafification.pushforwardUnitAdj` and
  `pushforwardForgetHom`: the restricted sheafification unit and the restriction of a morphism
  into the underlying presheaf of a sheaf of modules, each with its target at the spelling the
  sheafification hom-equivalence on the subsite takes.
* `Stacks.DenseSubsiteModules.moduleRestriction_sheafification`: the same for a dense subsite,
  in the `ringRestriction`/`moduleRestriction` spelling of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules`.
* `Stacks.DenseSubsiteModules.presheafRestrict_comp_sheafification`: the same over a sheaf of
  *commutative* rings.
* `Stacks.DenseSubsiteModules.commRingRestriction`, `presheafCommRingRestrict` and
  `commRingRestriction_sheafification`: the same again, at the exact spelling
  `Stacks.sheafTensorRight` uses on the subsite, which is the form that composes with it.

## Main results

* `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom_naturality`: the
  comparison morphism of `pushforwardSheafifyIso` is natural. This is the content the
  objectwise statement was missing.
* `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom_comp_map`: **the
  comparison is compatible with adjoint transposes.** Applied degreewise to a complex of
  presheaves of modules with an augmentation, this is the statement that the comparison of the
  two sheafified complexes commutes with the two sheafified augmentations.
* `Stacks.DenseSubsiteModules.presheafRestrict_eq`: the restriction functor on presheaves of
  modules of `DenseSubsiteTensor`, `Stacks.DenseSubsiteModules.presheafRestrict`, **is**
  `presheafPushforwardFunctor` at the underlying sheaf of rings, by `rfl`.

## Implementation notes

**What is proved elsewhere, and what is added here.** Everything objectwise is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras`: `pushforwardUnit`,
`pushforwardToSheafify` with its local injectivity and surjectivity, `pushforwardSheafifyHom`,
`isIso_pushforwardSheafifyHom` and `pushforwardSheafifyIso`. Nothing in this file reproves any
of it. What this file adds is naturality in the presheaf, which is what turns a family of
isomorphisms into an isomorphism of functors, and that is all `pushforwardSheafifyHom_naturality`
and `pushforwardSheafifyNatIso` provide. The slice case of the objectwise statement is
`Stacks.SheafOfModules.SliceSheafification.sheafifyOverIso`.

**Two spellings of the hom-equivalence, and why the bridge is needed.** The comparison
`pushforwardSheafifyHom` is defined through `PresheafOfModules.sheafificationHomEquiv`, while
the naturality of an adjoint transpose is Mathlib's `Adjunction.homEquiv_naturality_left_symm`
and `homEquiv_naturality_right_symm`, which are about
`(PresheafOfModules.sheafificationAdjunction α).homEquiv`. Mathlib's
`PresheafOfModules.sheafificationAdjunction_homEquiv_apply` identifies the two **in the forward
direction only**, and that is not enough: an `Equiv`'s `invFun` is not determined
definitionally by its `toFun`, so the two `.symm`s are propositionally but not definitionally
equal, and an `Eq.trans` chain mixing them fails to elaborate. The bridge
`sheafificationAdjunction_homEquiv_eq` upgrades the pointwise identification to an equality of
`Equiv`s with `Equiv.ext`, and
`pushforwardSheafifyHom_eq` restates that morphism in the adjunction spelling; after that
the naturality chain is three applications of Mathlib lemmas and no `rw` across a spelling
boundary.

**Three implicit arguments must be supplied by name.** In `homEquiv_naturality_right_symm` the
objects `X`, `Y`, `Y'` are implicit, and leaving them to be inferred poses
`?Y.val =?= ((sheafPushforwardFunctor J G R).obj _).val` — a metavariable under a structure
projection — which exhausts the heartbeat budget in `whnf` inside the application rather than
in any proof. Named, the file compiles in seconds with no `set_option`.

**Why the composite `presheafRestrict v O ⋙ sheafification` cannot be *stated* across
the two spellings, and what replaces it.** `Stacks.DenseSubsiteModules.presheafRestrict v O`
has target `PresheafOfModules (Stacks.ringPresheaf (v.op ⋙ O))`, whereas the sheafification on
the subsite is indexed by `(ringRestriction J K v R).obj`. The two are definitionally equal —
`presheafRestrict_eq` proves the two *functors* equal by `rfl` — but composing them with `⋙`
forces `PresheafOfModules.sheafification`'s implicit `R₀` to the first spelling while `R` keeps
the second, so the instance goal becomes
`Presheaf.IsLocallyInjective J (α : ringPresheaf (v.op ⋙ O) ⟶ (ringRestriction …).obj)`, with
two spellings of one presheaf. `instance`-transparency does not unfold the semireducible
`sheafPushforwardContinuous`, so `IsIso.id` no longer matches and the instance is reported
absent although `infer_instance` finds it for either spelling on its own. A wrapper `def` with
an ascribed result type does *not* help here, because the mixed spelling is created by the
ascription itself. So this file follows the one-spelling-per-statement rule instead: every
statement is written at `(ringRestriction …).obj`, and `presheafRestrict_eq` — an equality of
functors, so `rw` along it cannot strand a type — is the crossing, to be used at the
application site.

**Universes.** `pushforwardSheafifyNatIso` keeps all four parameters of the objectwise
statement independent: the sites at `Type u`/`Type u'` with `Category.{v}`/`Category.{v'}`, the
sheaf of rings at `RingCat.{t}` and the modules at `PresheafOfModules.{w}`. The dense-subsite
corollaries tie the ring universe to the module universe, because
`Stacks.DenseSubsiteModules.moduleRestriction` does; that tie is inherited and not used by any
proof here, and freeing it is an edit to `DenseSubsiteModules`' variable block, not to this
file. It is not a narrowing for the intended consumer: `Stacks.sheafTensorRight` is stated over
`O : Sheaf J CommRingCat.{w}` with modules in `PresheafOfModules.{w}`.

**Hypotheses.** Beyond the two sites, the functor's continuity and cocontinuity and the sheaf
of rings, these are `HasWeakSheafify` and `WEqualsLocallyBijective` for `AddCommGrpCat.{w}` on
`J` and on `K` — exactly what the two sheafification functors need — and, for the commutative
corollary, `K.HasSheafCompose (forget₂ CommRingCat RingCat)`. Cocontinuity of a dense subsite
inclusion is automatic (`CategoryTheory.Functor.IsDenseSubsite.instIsCocontinuous`). No
hypothesis is placed on the sites themselves: no finite limits, no products, no smallness.

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG), method (2)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
-/

@[expose] public section

open CategoryTheory Limits

universe w t v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules.PushforwardSheafification

section Bridge

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {Rs : Sheaf J RingCat.{t}} (α : R₀ ⟶ Rs.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- `PresheafOfModules.sheafificationHomEquiv` **is** the hom-equivalence of
`PresheafOfModules.sheafificationAdjunction`, as an equality of `Equiv`s.

Mathlib's `PresheafOfModules.sheafificationAdjunction_homEquiv_apply` gives this pointwise in
the forward direction; the equality of the `Equiv`s is what is needed to transfer the two
`Adjunction.homEquiv_naturality_*_symm` lemmas to `pushforwardSheafifyHom`, whose
definition uses `sheafificationHomEquiv`. -/
theorem sheafificationAdjunction_homEquiv_eq (P : PresheafOfModules.{w} R₀)
    (T : SheafOfModules.{w} Rs) :
    (PresheafOfModules.sheafificationAdjunction.{w} α).homEquiv P T =
      PresheafOfModules.sheafificationHomEquiv α :=
  Equiv.ext fun f ↦ PresheafOfModules.sheafificationAdjunction_homEquiv_apply α f

/-- The inverse of the hom-equivalence of `PresheafOfModules.sheafificationAdjunction` is that of
`PresheafOfModules.sheafificationHomEquiv`. -/
private theorem sheafificationAdjunction_homEquiv_symm_apply (P : PresheafOfModules.{w} R₀)
    (T : SheafOfModules.{w} Rs) (g : P ⟶ (SheafOfModules.forget Rs ⋙
      PresheafOfModules.restrictScalars α).obj T) :
    ((PresheafOfModules.sheafificationAdjunction.{w} α).homEquiv P T).symm g =
      (PresheafOfModules.sheafificationHomEquiv α).symm g := by
  rw [sheafificationAdjunction_homEquiv_eq]

end Bridge

section Naturality

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D} (G : C ⥤ D)
  [G.IsContinuous J K] (R : Sheaf K RingCat.{t})
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [G.IsCocontinuous J K]

omit [G.IsCocontinuous J K] in
/-- The pushed-forward sheafification unit is the image under `presheafPushforwardFunctor` of
the sheafification unit. -/
theorem pushforwardUnit_eq (P : PresheafOfModules.{w} R.obj) :
    pushforwardUnit.{w} J G R P = (presheafPushforwardFunctor.{w} J G R).map
      ((PresheafOfModules.sheafificationAdjunction.{w} (𝟙 R.obj)).unit.app P) := rfl

omit [G.IsCocontinuous J K] in
/-- The pushed-forward sheafification unit is natural: this is the naturality of the
sheafification unit, carried through `presheafPushforwardFunctor`. -/
theorem pushforwardUnit_naturality {P Q : PresheafOfModules.{w} R.obj} (f : P ⟶ Q) :
    (presheafPushforwardFunctor.{w} J G R).map f ≫ pushforwardUnit.{w} J G R Q =
      pushforwardUnit.{w} J G R P ≫
        (_root_.SheafOfModules.forget (pushforwardRingSheaf J G R) ⋙
            PresheafOfModules.restrictScalars (𝟙 (pushforwardRingSheaf J G R).obj)).map
          ((sheafPushforwardFunctor.{w} J G R).map
            ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).map f)) :=
  ((presheafPushforwardFunctor.{w} J G R).map_comp _ _).symm.trans
    ((congrArg (presheafPushforwardFunctor.{w} J G R).map
        ((PresheafOfModules.sheafificationAdjunction.{w} (𝟙 R.obj)).unit.naturality f)).trans
      ((presheafPushforwardFunctor.{w} J G R).map_comp _ _))

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [G.IsCocontinuous J K] in
/-- The comparison morphism `pushforwardSheafifyHom`, restated in the
`sheafificationAdjunction` spelling, which is the spelling Mathlib's naturality lemmas for an
adjoint transpose are stated at. -/
theorem pushforwardSheafifyHom_eq (P : PresheafOfModules.{w} R.obj) :
    pushforwardSheafifyHom.{w} J G R P =
      ((PresheafOfModules.sheafificationAdjunction.{w}
          (𝟙 (pushforwardRingSheaf J G R).obj)).homEquiv
        ((presheafPushforwardFunctor.{w} J G R).obj P)
        ((sheafPushforwardFunctor.{w} J G R).obj
          ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj P))).symm
      (pushforwardUnit.{w} J G R P) := by
  rw [sheafificationAdjunction_homEquiv_eq]
  rfl

omit [G.IsCocontinuous J K] in
/-- **The comparison morphism of `pushforwardSheafifyIso` is natural in the presheaf.**

Cocontinuity of `G` is not used: it is what makes the morphism an isomorphism, not what makes
it natural. -/
theorem pushforwardSheafifyHom_naturality {P Q : PresheafOfModules.{w} R.obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification.{w} (𝟙 (pushforwardRingSheaf J G R).obj)).map
        ((presheafPushforwardFunctor.{w} J G R).map f) ≫ pushforwardSheafifyHom.{w} J G R Q =
      pushforwardSheafifyHom.{w} J G R P ≫ (sheafPushforwardFunctor.{w} J G R).map
        ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).map f) := by
  rw [pushforwardSheafifyHom_eq, pushforwardSheafifyHom_eq]
  exact ((PresheafOfModules.sheafificationAdjunction.{w}
        (𝟙 (pushforwardRingSheaf J G R).obj)).homEquiv_naturality_left_symm
      (Y := (sheafPushforwardFunctor.{w} J G R).obj
        ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj Q))
      ((presheafPushforwardFunctor.{w} J G R).map f)
      (pushforwardUnit.{w} J G R Q)).symm.trans
    ((congrArg ((PresheafOfModules.sheafificationAdjunction.{w}
            (𝟙 (pushforwardRingSheaf J G R).obj)).homEquiv
          ((presheafPushforwardFunctor.{w} J G R).obj P)
          ((sheafPushforwardFunctor.{w} J G R).obj
            ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj Q))).symm
        (pushforwardUnit_naturality.{w} J G R f)).trans
      ((PresheafOfModules.sheafificationAdjunction.{w}
          (𝟙 (pushforwardRingSheaf J G R).obj)).homEquiv_naturality_right_symm
        (X := (presheafPushforwardFunctor.{w} J G R).obj P)
        (Y := (sheafPushforwardFunctor.{w} J G R).obj
          ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj P))
        (Y' := (sheafPushforwardFunctor.{w} J G R).obj
          ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj Q))
        (pushforwardUnit.{w} J G R P)
        ((sheafPushforwardFunctor.{w} J G R).map
          ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).map f))))

/-- **Sheafification of presheaves of modules commutes with restriction of sections along a
continuous and cocontinuous functor of sites, as an isomorphism of functors.**

This is `pushforwardSheafifyIso` made natural. -/
noncomputable def pushforwardSheafifyNatIso :
    presheafPushforwardFunctor.{w} J G R ⋙
        PresheafOfModules.sheafification.{w} (𝟙 (pushforwardRingSheaf J G R).obj) ≅
      PresheafOfModules.sheafification.{w} (𝟙 R.obj) ⋙ sheafPushforwardFunctor.{w} J G R :=
  NatIso.ofComponents (fun P ↦ pushforwardSheafifyIso.{w} J G R P)
    (fun f ↦ pushforwardSheafifyHom_naturality.{w} J G R f)

/-! ### Compatibility with adjoint transposes

A complex of presheaves of modules usually comes with an augmentation onto some sheaf, and the
sheafified augmentation is the adjoint transpose of the augmentation of the presheaf complex.
The comparison above is compatible with taking that transpose, which is what makes the
degreewise comparison of two sheafified complexes compatible with their augmentations. -/

omit [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [G.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Restriction of sections along `G` commutes with forgetting the module structure, on the
nose. -/
theorem forget_map_sheafPushforwardFunctor_map {T₁ T₂ : _root_.SheafOfModules.{w} R}
    (A : T₁ ⟶ T₂) :
    (_root_.SheafOfModules.forget (pushforwardRingSheaf J G R) ⋙
        PresheafOfModules.restrictScalars (𝟙 (pushforwardRingSheaf J G R).obj)).map
      ((sheafPushforwardFunctor.{w} J G R).map A) =
      (presheafPushforwardFunctor.{w} J G R).map
        ((_root_.SheafOfModules.forget R ⋙
          PresheafOfModules.restrictScalars (𝟙 R.obj)).map A) := rfl

/-- `Stacks.SheafOfModules.PushforwardSheafification.pushforwardUnit` with its target spelled
through the right adjoint `SheafOfModules.forget ⋙ PresheafOfModules.restrictScalars` of the
sheafification adjunction on `C`, rather than through `Sheaf.val`.

The two types are definitionally equal, but only this spelling lets a composite with
`(SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars _).map _` be *stated*: the
elaborator checks the middle object of a `≫` at `instances` transparency, which does not unfold
`sheafPushforwardFunctor`. -/
noncomputable def pushforwardUnitAdj (P : PresheafOfModules.{w} R.obj) :
    (presheafPushforwardFunctor.{w} J G R).obj P ⟶
      (_root_.SheafOfModules.forget (pushforwardRingSheaf J G R) ⋙
          PresheafOfModules.restrictScalars (𝟙 (pushforwardRingSheaf J G R).obj)).obj
        ((sheafPushforwardFunctor.{w} J G R).obj
          ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj P)) :=
  pushforwardUnit.{w} J G R P

omit [G.IsCocontinuous J K] in
/-- `pushforwardSheafifyHom_eq` read at `pushforwardUnitAdj`. -/
theorem pushforwardSheafifyHom_eq_adj (P : PresheafOfModules.{w} R.obj) :
    pushforwardSheafifyHom.{w} J G R P =
      ((PresheafOfModules.sheafificationAdjunction.{w}
          (𝟙 (pushforwardRingSheaf J G R).obj)).homEquiv
        ((presheafPushforwardFunctor.{w} J G R).obj P)
        ((sheafPushforwardFunctor.{w} J G R).obj
          ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj P))).symm
      (pushforwardUnitAdj.{w} J G R P) :=
  pushforwardSheafifyHom_eq.{w} J G R P

variable {P : PresheafOfModules.{w} R.obj} {T : _root_.SheafOfModules.{w} R}

/-- Restriction of sections along `G` of a morphism from a presheaf of modules into the
underlying presheaf of a sheaf of modules, with its target at the spelling the sheafification
hom-equivalence on `C` takes. -/
noncomputable def pushforwardForgetHom (g : P ⟶ (_root_.SheafOfModules.forget R ⋙
      PresheafOfModules.restrictScalars (𝟙 R.obj)).obj T) :
    (presheafPushforwardFunctor.{w} J G R).obj P ⟶
      (_root_.SheafOfModules.forget (pushforwardRingSheaf J G R) ⋙
          PresheafOfModules.restrictScalars (𝟙 (pushforwardRingSheaf J G R).obj)).obj
        ((sheafPushforwardFunctor.{w} J G R).obj T) :=
  (presheafPushforwardFunctor.{w} J G R).map g

omit [G.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The restricted sheafification unit followed by the restriction of the transpose of `g` is
the restriction of `g`: the triangle identity of the sheafification adjunction on `D`, carried
through restriction of sections. -/
theorem pushforwardUnitAdj_comp_forget_map
    (g : P ⟶ (_root_.SheafOfModules.forget R ⋙
      PresheafOfModules.restrictScalars (𝟙 R.obj)).obj T) :
    pushforwardUnitAdj.{w} J G R P ≫
        (_root_.SheafOfModules.forget (pushforwardRingSheaf J G R) ⋙
          PresheafOfModules.restrictScalars (𝟙 (pushforwardRingSheaf J G R).obj)).map
          ((sheafPushforwardFunctor.{w} J G R).map
            ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm g)) =
      pushforwardForgetHom.{w} J G R g := by
  have hg : (PresheafOfModules.sheafificationAdjunction.{w} (𝟙 R.obj)).unit.app P ≫
      (_root_.SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm g) = g := by
    rw [← sheafificationAdjunction_homEquiv_symm_apply]
    exact ((PresheafOfModules.sheafificationAdjunction.{w} (𝟙 R.obj)).homEquiv_unit
      P T _).symm.trans (Equiv.apply_symm_apply _ g)
  exact ((presheafPushforwardFunctor.{w} J G R).map_comp
      ((PresheafOfModules.sheafificationAdjunction.{w} (𝟙 R.obj)).unit.app P)
      ((_root_.SheafOfModules.forget R ⋙
        PresheafOfModules.restrictScalars (𝟙 R.obj)).map
          ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm g))).symm.trans
    (congrArg (presheafPushforwardFunctor.{w} J G R).map hg)

omit [G.IsCocontinuous J K] in
/-- **The sheafification comparison is compatible with adjoint transposes**: the restriction of
sections of the morphism of sheaves of modules transposing `g` is, after the comparison, the
morphism transposing the restriction of `g`.

Applied to the augmentation of a complex of presheaves of modules, this says that the
degreewise comparison of the sheafified complexes commutes with the two sheafified
augmentations. -/
theorem pushforwardSheafifyHom_comp_map
    (g : P ⟶ (_root_.SheafOfModules.forget R ⋙
      PresheafOfModules.restrictScalars (𝟙 R.obj)).obj T) :
    pushforwardSheafifyHom.{w} J G R P ≫ (sheafPushforwardFunctor.{w} J G R).map
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm g) =
      (PresheafOfModules.sheafificationHomEquiv
          (𝟙 (pushforwardRingSheaf J G R).obj)).symm
        (pushforwardForgetHom.{w} J G R g) :=
  (congrArg (fun x ↦ x ≫ (sheafPushforwardFunctor.{w} J G R).map
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm g))
      (pushforwardSheafifyHom_eq_adj.{w} J G R P)).trans
    (((PresheafOfModules.sheafificationAdjunction.{w}
          (𝟙 (pushforwardRingSheaf J G R).obj)).homEquiv_naturality_right_symm
        (pushforwardUnitAdj.{w} J G R P)
        ((sheafPushforwardFunctor.{w} J G R).map
          ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm g))).symm.trans
      ((congrArg ((PresheafOfModules.sheafificationAdjunction.{w}
            (𝟙 (pushforwardRingSheaf J G R).obj)).homEquiv
          ((presheafPushforwardFunctor.{w} J G R).obj P)
          ((sheafPushforwardFunctor.{w} J G R).obj T)).symm
          (pushforwardUnitAdj_comp_forget_map.{w} J G R g)).trans
        (sheafificationAdjunction_homEquiv_symm_apply _ _ _ _)))

end Naturality

end Stacks.SheafOfModules.PushforwardSheafification

namespace Stacks.DenseSubsiteModules

open Stacks.SheafOfModules.PushforwardSheafification

section DenseSubsite

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Restriction to a dense subsite commutes with the sheafification of presheaves of
modules**, in the `ringRestriction`/`moduleRestriction` spelling of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules`.

Cocontinuity of `v` is automatic for a dense subsite, so the only hypotheses beyond
`v.IsDenseSubsite J K` are the ones the two sheafification functors need. -/
noncomputable def moduleRestriction_sheafification (R : Sheaf K RingCat.{w}) :
    presheafPushforwardFunctor.{w} J v R ⋙
        PresheafOfModules.sheafification.{w} (R := ringRestriction J K v R)
          (𝟙 (ringRestriction J K v R).obj) ≅
      PresheafOfModules.sheafification.{w} (R := R) (𝟙 R.obj) ⋙
        moduleRestriction.{w} J K v R :=
  pushforwardSheafifyNatIso.{w} J v R

variable [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

omit [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `Stacks.DenseSubsiteModules.presheafRestrict`, the restriction of presheaves of modules
over a sheaf of *commutative* rings used by `DenseSubsiteTensor`, **is**
`presheafPushforwardFunctor` at the underlying sheaf of rings — on the nose.

Both sides of this equality are the same functor, so rewriting along it cannot strand a type;
it is the intended crossing between the `Stacks.ringPresheaf` spelling of `DenseSubsiteTensor`
and the `ringRestriction` spelling of the statements above. See the implementation notes for
why the two cannot be mixed inside a single composite. -/
theorem presheafRestrict_eq (O : Sheaf K CommRingCat.{w}) :
    presheafRestrict v O.obj =
      presheafPushforwardFunctor.{w} J v (Stacks.commRingSheafToRingSheaf O) := rfl

/-- **Restriction to a dense subsite commutes with the sheafification of presheaves of modules
over a sheaf of commutative rings.** This is the third and last factor of
`Stacks.sheafTensorRight`; the other two commute with restriction on the nose, by
`Stacks.DenseSubsiteModules.moduleRestriction_comp_forget` and
`presheafRestrict_comp_tensorRight`. -/
noncomputable def presheafRestrict_comp_sheafification (O : Sheaf K CommRingCat.{w}) :
    presheafPushforwardFunctor.{w} J v (Stacks.commRingSheafToRingSheaf O) ⋙
        PresheafOfModules.sheafification.{w}
          (R := ringRestriction J K v (Stacks.commRingSheafToRingSheaf O))
          (𝟙 (ringRestriction J K v (Stacks.commRingSheafToRingSheaf O)).obj) ≅
      PresheafOfModules.sheafification.{w} (R := Stacks.commRingSheafToRingSheaf O)
          (𝟙 (Stacks.commRingSheafToRingSheaf O).obj) ⋙
        moduleRestriction.{w} J K v (Stacks.commRingSheafToRingSheaf O) :=
  pushforwardSheafifyNatIso.{w} J v (Stacks.commRingSheafToRingSheaf O)

/-- The restriction of a sheaf of *commutative* rings to the dense subsite. -/
noncomputable abbrev commRingRestriction (O : Sheaf K CommRingCat.{w}) :
    Sheaf J CommRingCat.{w} :=
  (v.sheafPushforwardContinuous CommRingCat.{w} J K).obj O

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Restriction of presheaves of modules along `v`, with its result type at the spelling
`Stacks.sheafTensorRight` uses on the subsite, namely
`(Stacks.commRingSheafToRingSheaf (commRingRestriction J K v O)).obj` rather than
`(ringRestriction J K v (Stacks.commRingSheafToRingSheaf O)).obj`.

The two presheaves of rings are definitionally equal — indeed the two *sheaves* of rings are,
by `rfl` — but not syntactically, and the difference is load-bearing: composing with
`PresheafOfModules.sheafification` across them produces a morphism whose source and target are
spelled differently, and then `instance`-transparency cannot see that `𝟙` is an isomorphism.
Fixing one spelling here is what makes the composite in `commRingRestriction_sheafification`
elaborate.

The body is Mathlib's `PresheafOfModules.pushforward₀`, through
`Stacks.DenseSubsiteModules.presheafRestrict`, with no restriction of scalars along an identity
in the way: that is what keeps the commutation with `Stacks.tensorRight` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteSheafTensor` a cheap `rfl`. -/
noncomputable def presheafCommRingRestrict (O : Sheaf K CommRingCat.{w}) :
    PresheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O).obj ⥤
      PresheafOfModules.{w} (Stacks.commRingSheafToRingSheaf (commRingRestriction J K v O)).obj :=
  presheafRestrict v O.obj

/-- **Restriction to a dense subsite commutes with sheafification, at the exact spelling
`Stacks.sheafTensorRight` uses on the subsite.**

This is the form in which the result composes with `Stacks.sheafTensorRight`: both the ring
sheaf on the subsite and the presheaf-level restriction functor are written the way
`Stacks.sheafTensorRight (commRingRestriction J K v O)` writes them. See the module
implementation notes for why `commRingRestriction_sheafification` and
`presheafRestrict_comp_sheafification` must both exist rather than one being `rw`-able into the
other. -/
noncomputable def commRingRestriction_sheafification (O : Sheaf K CommRingCat.{w}) :
    presheafCommRingRestrict J K v O ⋙
        PresheafOfModules.sheafification.{w}
          (R := Stacks.commRingSheafToRingSheaf (commRingRestriction J K v O))
          (𝟙 (Stacks.commRingSheafToRingSheaf (commRingRestriction J K v O)).obj) ≅
      PresheafOfModules.sheafification.{w} (R := Stacks.commRingSheafToRingSheaf O)
          (𝟙 (Stacks.commRingSheafToRingSheaf O).obj) ⋙
        moduleRestriction.{w} J K v (Stacks.commRingSheafToRingSheaf O) :=
  pushforwardSheafifyNatIso.{w} J v (Stacks.commRingSheafToRingSheaf O)

end DenseSubsite

end Stacks.DenseSubsiteModules

end
