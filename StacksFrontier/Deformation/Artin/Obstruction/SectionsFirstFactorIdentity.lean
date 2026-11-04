module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsObstructionIdentity
public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentIso
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Normalization

/-!
# The affine base-change comparison of Stacks 01I9 at the identity ring map

The first of the two tensor factors of the coefficient half of the map of obstruction modules of
Stacks 07YH, `Deformation.Artin.SectionsSheaf.tildeFirstFactorMapGen`, is built from three
comparisons: `AlgebraicGeometry.Scheme.Modules.pullbackComp` and `..pullbackCongr` of Mathlib's
pullback pseudofunctor, and the affine base-change isomorphism `(Spec ψ)^* M̃ ≅ (A₁ ⊗_A M)~` of
[Stacks, Tag 01I9], which this development uses in the spelling
`Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso`. This file computes each of them at
`ψ = 𝟙 A`, which is what the identity case of clause (2) of Stacks 07YG needs.

Everything here is a statement about Mathlib's pullback pseudofunctor and about Tag 01I9, not
about obstruction theories. It is placed in this namespace and not nearer its subject because
the adjoint equation it all rests on,
`Deformation.Artin.SectionsSheaf.unit_comp_pullbackId_hom_app`, already lives here, and
restating that would duplicate it.

## Main results

* `Deformation.Artin.SectionsSheaf.pullbackComp_congr_comp_inv_app` — **the pullback
  pseudofunctor part of the first tensor factor at an identity.** For `π : X ⟶ Y` and a morphism
  `u : Y ⟶ Y` equal to `𝟙 Y`, the transport of `g^* π^*` across the square `𝟙 X ≫ π = π ≫ u` is
  the identity law of `pullback` at `X` followed by `π^*` of the identity law at `Y`. This is
  `AlgebraicGeometry.Scheme.Modules.pseudofunctor_right_unitality` and `..left_unitality`
  joined by the fact that `pullbackCongr` is an `eqToIso`, so that two of them compose.
* `Deformation.Artin.SectionsSheaf.unit_comp_pullbackSpecIdIso` — **the adjoint equation at a
  morphism that is equal to an identity but not spelled as one.** The unit of `u^* ⊣ u_*`
  followed by `u_*` of the identity law for `u^*` is the identity law for `u_*`.
* `Deformation.Artin.SectionsSheaf.tildePullbackIso_id_hom_app` — **the comparison of Tag 01I9
  at the identity ring map**: `(Spec (𝟙 A))^* M̃ ≅ (A ⊗_A M)~` is the identity law for pullback
  followed by `M̃ ⟶ (A ⊗_A M)~`, the associated sheaf of the unit `m ↦ 1 ⊗ m` of
  `ModuleCat.extendRestrictScalarsAdj`.
* `Deformation.Artin.SectionsSheaf.unit_comp_tildeFirstFactorMapGen_id` — **the first of the two
  tensor factors of the coefficient map of Stacks 07YH at an identity**: the unit of the
  pullback--pushforward adjunction at `𝟙 X` followed by `g^* π^* M̃ ⟶ π^* Ñ` at `g = 𝟙 X` and the
  identity ring map is `π^*` of the associated sheaf of `f`. This is what the identity case of
  clause (2) of Stacks 07YG was waiting on for its first factor.

## Main definitions

* `Deformation.Artin.SectionsSheaf.pushforwardSpecIdIso` — the identity law
  `(Spec (𝟙 A))_* ≅ 𝟭` for the direct image.
* `Deformation.Artin.SectionsSheaf.extendUnitId` — the unit `m ↦ 1 ⊗ m` of extension of scalars
  along the identity ring map, with its target read as `A ⊗_A M` itself.
* `Deformation.Artin.SectionsSheaf.pullbackSpecIdIso` — the identity law
  `(Spec (𝟙 A))^* ≅ 𝟭` for the pullback.

## Implementation notes

`pullbackCongr` is `CategoryTheory.eqToIso` of an equality of *functors*
(`AlgebraicGeometry.Scheme.Modules.pullbackCongr`), and an equality of functors is a `Prop`, so
any two proofs of it are definitionally equal. That is what lets the transport
`pseudofunctor_right_unitality` produces be read as a `pullbackCongr` with no `eqToHom_app`
step, and what makes `pullbackCongr_hom_app_comp` hold.

**`pullbackCongr_hom_app_comp` is a third copy, and that is debt, not design.** The same
statement with the same proof is already `Stacks.Groupoids.pullbackCongr_hom_app_comp` in
`StacksFrontier/AlgebraicGeometry/Groupoids/DescentIso.lean` and, with the composite equality taken
as a third argument, `Stacks.Descent.pullbackCongr_hom_app_comp` in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/SpecSingletonCocycle.lean`. Neither is in
this file's import closure, and enlarging the closure of a file whose proofs turn on definitional
unfoldings is what the records elsewhere in this development warn against. A dedup pass should
move one of the three to a common ancestor and delete the other two.

The three lemmas that mention a morphism `u : Y ⟶ Y` take it as a *variable* with the
hypothesis `u = 𝟙 Y` and `subst` it. Stating them at `u = Spec.map (𝟙 A)` directly is not
possible for `unit_comp_pullbackSpecIdIso`: before the substitution `(pushforward u).obj Z` and
`Z` are different objects, so the conclusion is not even typeable, and after it they are the
same one, `Scheme.Modules.pushforward (𝟙 Y)` being `𝟭` on the nose.

`unit_comp_pullbackSpecIdIso` is proved in **term mode**. `rw` declines the goal as "not
type-correct under the `implicit` transparency level": its left-hand side is
`u_*` applied to a morphism with `u_* = 𝟭`, so the codomain of the composite is reached only
through a definitional unfolding that `rw` will not make.

`tildePullbackIso_id_hom_app` is the uniqueness of left adjoints, used the way
`Stacks.AlgebraicGeometry.AffineBaseChange.tildePullbackIso_unit` uses it:
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` says what the comparison is after the
unit of `tildePullbackAdjunction`, and the claim follows by `eq_of_unit_comp`, which is that
unit's injectivity on morphisms out of a left adjoint's value. Four computations feed it, each
made at the level where the two spellings agree: the identity law for `u_*` is the identity *on
sections over the whole space* (`pushforwardSpecIdIso_inv_app_app_top`, where `u ⁻¹ᵁ ⊤` and `⊤`
are the same open), hence on global sections it is the comparison of the two `A`-module
structures that `Stacks.AlgebraicGeometry.SectionsColimit.pullbackSectionsIso` supplies
(`map_pushforwardSpecIdIso_inv`), and the units of the two adjunctions are read off by
`CategoryTheory.Adjunction.comp_unit_app` and `..ofNatIsoRight_unit`.

Every re-association in that chain is `exact Category.assoc _ _ _` or a `congrArg`, and not
`rw [Category.assoc]`. The composite `η ≫ Γ(u_* -)` mixes the two spellings `(F ⋙ G).obj M` and
`G.obj (F.obj M)` of one object — Mathlib's `Adjunction.comp_unit_app` does — and `rw` matches
`(?f ≫ ?g) ≫ ?h` only up to `instances` transparency, which does not identify them; an `exact`
elaborates against the goal with the full definitional unfolding available.

**A warning about the heartbeat figures.** Three declarations here —
`tildePullbackAdjunction_unit_comp_map`, `..._eq` and `tildePullbackIso_id_hom_app` — compile
under the standard budget of 200 000 but report about 1.0 · 10⁶ under
`#count_heartbeats`, which runs at `maxHeartbeats 0`. The figures are not in contradiction: the
budget itself cuts off a speculative `whnf` on the `pullbackSections`/`moduleSpecΓFunctor`
spellings of one functor, and `exact` and `rw` recover from the abort along a cheap path, while
with no budget the elaborator pursues the unfolding to the end. So `#count_heartbeats` is not a
cost model for these three, and raising their budget would make them *slower*, not safer; the
split into separate declarations is what keeps the recovery local.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.SectionsColimit

universe u

namespace Deformation.Artin.SectionsSheaf

/-! ### Transports along equal morphisms -/

-- Two transports of the pullback along equal morphisms compose:
-- `Stacks.Groupoids.pullbackCongr_hom_app_comp`, public in
-- `StacksFrontier.AlgebraicGeometry.Groupoids.DescentIso` (import closure 3; +3 modules here),
-- where it also carries `@[reassoc]`. A copy stood here; the module docstring above recorded it
-- as debt and asked for exactly this pass.

/-- **The transport of the pushforward along `rfl` is the identity.** Its component over an open
`U` is the restriction map of the module along an equality of opens, which is the identity by
functoriality. -/
theorem pushforwardCongr_refl_inv_app {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    (Scheme.Modules.pushforwardCongr (rfl : f = f)).inv.app M = 𝟙 _ := by
  ext U
  simp [Scheme.Modules.pushforwardCongr_inv_app_app]

/-! ### The pullback identity laws read across a base-change square -/

section PullbackIdentity

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (u : Y ⟶ Y)

/-- **The pullback-pseudofunctor part of the first tensor factor of Stacks 07YH at an identity.**
For a morphism `u : Y ⟶ Y` equal to `𝟙 Y`, the comparison that carries `(𝟙 X)^* π^*` to
`π^* u^*` across the square `𝟙 X ≫ π = π ≫ u` is the identity law for pullback at `X`, followed
by `π^*` of the inverse of the identity law at `Y`.

Both unitality laws of Mathlib's pullback pseudofunctor enter: the right one at `π`, which
supplies the transport along `𝟙 X ≫ π = π`, and the left one, which supplies the transport along
`π ≫ 𝟙 Y = π`. The hypothesis `hfst` of
`Deformation.Artin.SectionsSheaf.tildeFirstFactorMapGen` is the composite of those two
equalities, and `pullbackCongr_hom_app_comp` is what splits it. -/
theorem pullbackComp_congr_comp_inv_app (hu : u = 𝟙 Y)
    (hfst : (𝟙 X : X ⟶ X) ≫ π = π ≫ u) (G : Y.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 X) π).hom.app G ≫
        (Scheme.Modules.pullbackCongr hfst).hom.app G ≫
        ((Scheme.Modules.pullbackComp π u).app G).inv =
      (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback π).obj G) ≫
        (Scheme.Modules.pullback π).map
          ((Scheme.Modules.pullbackId Y).inv.app G ≫
            (Scheme.Modules.pullbackCongr hu).inv.app G) := by
  subst hu
  have hR := congrArg (fun τ => NatTrans.app τ G)
    (Scheme.Modules.pseudofunctor_right_unitality π)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hR
  have keyR : (Scheme.Modules.pullbackComp (𝟙 X) π).inv.app G ≫
      (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback π).obj G) =
      (Scheme.Modules.pullbackCongr (hfst.trans (Category.comp_id π))).hom.app G := hR
  have hL := congrArg (fun τ => NatTrans.app τ G)
    (Scheme.Modules.pseudofunctor_left_unitality π)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hL
  have keyL : (Scheme.Modules.pullbackComp π (𝟙 Y)).inv.app G ≫
      (Scheme.Modules.pullback π).map ((Scheme.Modules.pullbackId Y).hom.app G) =
      (Scheme.Modules.pullbackCongr (Category.comp_id π)).hom.app G := hL
  have hA : (Scheme.Modules.pullbackComp (𝟙 X) π).hom.app G ≫
      (Scheme.Modules.pullbackCongr (hfst.trans (Category.comp_id π))).hom.app G =
      (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback π).obj G) := by
    rw [← keyR, ← Category.assoc, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app,
      Category.id_comp]
  have hinv : ((Scheme.Modules.pullbackComp π (𝟙 Y)).app G).inv =
      (Scheme.Modules.pullbackCongr (Category.comp_id π)).hom.app G ≫
        (Scheme.Modules.pullback π).map ((Scheme.Modules.pullbackId Y).inv.app G) := by
    rw [Iso.app_inv, ← keyL, Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  have hcongr : (Scheme.Modules.pullbackCongr (rfl : (𝟙 Y : Y ⟶ Y) = 𝟙 Y)).inv.app G = 𝟙 _ := rfl
  rw [hinv, hcongr, Category.comp_id ((Scheme.Modules.pullbackId Y).inv.app G),
    ← Category.assoc ((Scheme.Modules.pullbackCongr hfst).hom.app G),
    Stacks.Groupoids.pullbackCongr_hom_app_comp hfst (Category.comp_id π) G,
    ← Category.assoc, hA]

/-- **The adjoint equation at a morphism that is equal to an identity but not spelled as one.**
For `u : Y ⟶ Y` equal to `𝟙 Y`, the unit of `u^* ⊣ u_*` followed by `u_*` of the identity law
for `u^*` is the identity law for `u_*`.

This is `Deformation.Artin.SectionsSheaf.unit_comp_pullbackId_hom_app` with `u` carried as a
variable, which is what makes the statement typeable: `u_*` is `𝟭` only after the substitution,
and before it the two ends of the conclusion are different objects. -/
theorem unit_comp_pullbackSpecIdIso (hu : u = 𝟙 Y) (G : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction u).unit.app G ≫
        (Scheme.Modules.pushforward u).map
          ((Scheme.Modules.pullbackCongr hu).hom.app G ≫
            (Scheme.Modules.pullbackId Y).hom.app G) =
      (Scheme.Modules.pushforwardId Y).inv.app G ≫
        (Scheme.Modules.pushforwardCongr hu).inv.app G := by
  subst hu
  exact ((whisker_eq _ (Category.id_comp _)).trans (unit_comp_pullbackId_hom_app Y G)).trans
    ((whisker_eq _ (pushforwardCongr_refl_inv_app (𝟙 Y) G)).trans (Category.comp_id _)).symm

end PullbackIdentity

/-! ### The comparison of Stacks 01I9 at the identity ring map -/

/-- **The identity law for the direct image along `Spec.map (𝟙 A)`.** -/
def pushforwardSpecIdIso (A : CommRingCat.{u}) :
    Scheme.Modules.pushforward (Spec.map (𝟙 A)) ≅ 𝟭 (Spec A).Modules :=
  Scheme.Modules.pushforwardCongr (Spec.map_id A) ≪≫ Scheme.Modules.pushforwardId (Spec A)

section SpecId

variable {A : CommRingCat.{u}}

/-- The right adjoint of `tildePullbackAdjunction` acts through the direct image. -/
theorem pullbackSections_map {Z W : (Spec A).Modules} (h : Z ⟶ W) :
    (pullbackSections (𝟙 A)).map h =
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (Spec.map (𝟙 A))).map h) := rfl

/-- **On sections over the whole space the identity law for the direct image along
`Spec.map (𝟙 A)` is the identity.** The two opens `Spec.map (𝟙 A) ⁻¹ᵁ ⊤` and `𝟙 (Spec A) ⁻¹ᵁ ⊤`
are both `⊤`, so the restriction map `pushforwardCongr` contributes is the identity. -/
theorem pushforwardSpecIdIso_inv_app_app_top (Z : (Spec A).Modules) :
    Scheme.Modules.Hom.app ((pushforwardSpecIdIso A).inv.app Z) ⊤ = 𝟙 _ := by
  simp only [pushforwardSpecIdIso, Iso.trans_inv, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardId_inv_app_app,
    Scheme.Modules.pushforwardCongr_inv_app_app]
  exact Z.presheaf.map_id _

/-- **On global sections the identity law for the direct image along `Spec.map (𝟙 A)` is the
comparison of the two `A`-module structures.** Both are the identity map of `Γ(Z, ⊤)`; what they
compare is the `A`-action, which factors through `(Spec.map (𝟙 A)).appTop` on one side and
through the identity on the other. -/
theorem map_pushforwardSpecIdIso_inv (Z : (Spec A).Modules) :
    moduleSpecΓFunctor.map ((pushforwardSpecIdIso A).inv.app Z) =
      (pullbackSectionsIso (𝟙 A)).inv.app Z := by
  have h := pushforwardSpecIdIso_inv_app_app_top (A := A) Z
  ext x
  exact congrArg (fun k => (AddCommGrpCat.Hom.hom k) x) h

/-- The unit of `tildePullbackAdjunction` is the unit of the tilde--global-sections adjunction
followed by the global sections of the unit of the pullback--pushforward adjunction. -/
theorem tildePullbackAdjunction_unit_app (M : ModuleCat.{u} A) :
    (tildePullbackAdjunction (𝟙 A)).unit.app M =
      tilde.toTildeΓNatIso.hom.app M ≫ moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 A))).unit.app
          ((tilde.functor A).obj M)) := by
  rw [tildePullbackAdjunction, Adjunction.comp_unit_app]
  rfl

/-- **The unit `m ↦ 1 ⊗ m` of extension of scalars along the identity ring map**, with its
target read as the base change `A ⊗_A M` itself.

Naming it is not cosmetic. The unit of `ModuleCat.extendRestrictScalarsAdj` lands in
`(restrictScalars (𝟙 A)).obj (A ⊗_A M)`, and `restrictScalars (𝟙 A)` is the identity functor
only through a definitional unfolding of `Module.compHom` at `RingHom.id`; asking the elaborator
to take that step inside a composite costs the whole heartbeat budget, whereas here it is taken
once. -/
def extendUnitId {A : CommRingCat.{u}} (M : ModuleCat.{u} A) :
    M ⟶ (ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M :=
  (ModuleCat.extendRestrictScalarsAdj (𝟙 A : A ⟶ A).hom).unit.app M


section SpecIdTilde

variable {A : CommRingCat.{u}}

/-- The unit of `extendScalarsTildeAdjunction` at the identity ring map: extension of scalars'
own unit `m ↦ 1 ⊗ m`, then the unit of the tilde--global-sections adjunction, then the
comparison of the two `A`-module structures on global sections. -/
theorem extendScalarsTildeAdjunction_unit_app (M : ModuleCat.{u} A) :
    (extendScalarsTildeAdjunction (𝟙 A)).unit.app M =
      extendUnitId M ≫
        tilde.toTildeΓNatIso.hom.app
            ((ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M) ≫
          (pullbackSectionsIso (𝟙 A)).inv.app
            ((tilde.functor A).obj
              ((ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M)) := by
  have h := congrArg (fun τ => NatTrans.app τ M) (Adjunction.ofNatIsoRight_unit
    ((ModuleCat.extendRestrictScalarsAdj (𝟙 A : A ⟶ A).hom).comp tilde.adjunction)
    (pullbackSectionsIso (𝟙 A)).symm)
  simp only [NatTrans.comp_app, Adjunction.comp_unit_app, Iso.symm_hom] at h
  exact h

/-- The identity law for the direct image along `Spec.map (𝟙 A)` is natural. Split off so that
the unifier never has to guess its morphism argument inside a larger composite. -/
theorem pushforwardSpecIdIso_inv_naturality {Z W : (Spec A).Modules} (h : Z ⟶ W) :
    (pushforwardSpecIdIso A).inv.app Z ≫
        (Scheme.Modules.pushforward (Spec.map (𝟙 A))).map h =
      h ≫ (pushforwardSpecIdIso A).inv.app W :=
  ((pushforwardSpecIdIso A).inv.naturality h).symm

/-- The unit of the tilde--global-sections adjunction is natural, in the spelling
`tildePullbackIso_id_hom_app` consumes it. -/
theorem toTildeΓNatIso_hom_naturality {M N : ModuleCat.{u} A} (h : M ⟶ N) :
    tilde.toTildeΓNatIso.hom.app M ≫
        moduleSpecΓFunctor.map ((tilde.functor A).map h) =
      h ≫ tilde.toTildeΓNatIso.hom.app N :=
  (tilde.toTildeΓNatIso.hom.naturality h).symm

-- Two morphisms out of the value of a left adjoint agree as soon as they agree after the unit:
-- `Stacks.Conormal.eq_of_unit_comp_map`, public in
-- `StacksFrontier.AlgebraicGeometry.ConormalComparison.Normalization` (import closure 12; +5
-- modules here). A copy stood here under the name `eq_of_unit_comp`; Mathlib has no lemma of
-- this shape, only the `(adj.homEquiv _ _).injective` / `homEquiv_unit` pair all the copies
-- derive it from.

/-- `unit_comp_pullbackSpecIdIso` at `u = Spec.map (𝟙 A)`, in the `pushforwardSpecIdIso`
spelling. -/
theorem unit_comp_pushforwardSpecIdIso (G : (Spec A).Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 A))).unit.app G ≫
        (Scheme.Modules.pushforward (Spec.map (𝟙 A))).map
          ((Scheme.Modules.pullbackCongr (Spec.map_id A)).hom.app G ≫
            (Scheme.Modules.pullbackId (Spec A)).hom.app G) =
      (pushforwardSpecIdIso A).inv.app G := by
  have h : (pushforwardSpecIdIso A).inv.app G =
      (Scheme.Modules.pushforwardId (Spec A)).inv.app G ≫
        (Scheme.Modules.pushforwardCongr (Spec.map_id A)).inv.app G := rfl
  rw [h]
  exact unit_comp_pullbackSpecIdIso (Spec.map (𝟙 A)) (Spec.map_id A) G

/-- The unit of the pullback--pushforward adjunction along `Spec.map (𝟙 A)`, followed by the
direct image of the identity law for pullback and of the associated sheaf of `m ↦ 1 ⊗ m`, is
that associated sheaf followed by the identity law for the direct image. -/
theorem unit_comp_pushforward_tildeMap_unit_app (M : ModuleCat.{u} A) :
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 A))).unit.app
          ((tilde.functor A).obj M) ≫
        (Scheme.Modules.pushforward (Spec.map (𝟙 A))).map
          (((Scheme.Modules.pullbackCongr (Spec.map_id A)).hom.app
                ((tilde.functor A).obj M) ≫
              (Scheme.Modules.pullbackId (Spec A)).hom.app ((tilde.functor A).obj M)) ≫
            (tilde.functor A).map (extendUnitId M)) =
      (tilde.functor A).map (extendUnitId M) ≫
        (pushforwardSpecIdIso A).inv.app
          ((tilde.functor A).obj
            ((ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M)) := by
  rw [CategoryTheory.Functor.map_comp (Scheme.Modules.pushforward (Spec.map (𝟙 A))),
    ← Category.assoc, unit_comp_pushforwardSpecIdIso]
  exact pushforwardSpecIdIso_inv_naturality ((tilde.functor A).map (extendUnitId M))

/-- The transpose, under `tildePullbackAdjunction (𝟙 A)`, of the composite that
`tildePullbackIso_id_hom_app` claims the comparison of Tag 01I9 is. -/
theorem tildePullbackAdjunction_unit_comp_map (M : ModuleCat.{u} A) :
    (tildePullbackAdjunction (𝟙 A)).unit.app M ≫
        (pullbackSections (𝟙 A)).map
          (((Scheme.Modules.pullbackCongr (Spec.map_id A)).hom.app
                ((tilde.functor A).obj M) ≫
              (Scheme.Modules.pullbackId (Spec A)).hom.app ((tilde.functor A).obj M)) ≫
            (tilde.functor A).map (extendUnitId M)) =
      tilde.toTildeΓNatIso.hom.app M ≫
        moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 A))).unit.app
              ((tilde.functor A).obj M) ≫
            (Scheme.Modules.pushforward (Spec.map (𝟙 A))).map
              (((Scheme.Modules.pullbackCongr (Spec.map_id A)).hom.app
                    ((tilde.functor A).obj M) ≫
                  (Scheme.Modules.pullbackId (Spec A)).hom.app
                    ((tilde.functor A).obj M)) ≫
                (tilde.functor A).map (extendUnitId M))) := by
  rw [pullbackSections_map, tildePullbackAdjunction_unit_app,
    CategoryTheory.Functor.map_comp moduleSpecΓFunctor]
  exact Category.assoc _ _ _

/-- That transpose, rewritten by `unit_comp_pushforward_tildeMap_unit_app` and split at the
identity law for the direct image. -/
theorem tildePullbackAdjunction_unit_comp_map_eq (M : ModuleCat.{u} A) :
    tilde.toTildeΓNatIso.hom.app M ≫
        moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 A))).unit.app
              ((tilde.functor A).obj M) ≫
            (Scheme.Modules.pushforward (Spec.map (𝟙 A))).map
              (((Scheme.Modules.pullbackCongr (Spec.map_id A)).hom.app
                    ((tilde.functor A).obj M) ≫
                  (Scheme.Modules.pullbackId (Spec A)).hom.app
                    ((tilde.functor A).obj M)) ≫
                (tilde.functor A).map (extendUnitId M))) =
      (tilde.toTildeΓNatIso.hom.app M ≫
          moduleSpecΓFunctor.map ((tilde.functor A).map (extendUnitId M))) ≫
        moduleSpecΓFunctor.map
          ((pushforwardSpecIdIso A).inv.app
            ((tilde.functor A).obj
              ((ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M))) := by
  rw [unit_comp_pushforward_tildeMap_unit_app]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (fun z => tilde.toTildeΓNatIso.hom.app M ≫ z)
    (CategoryTheory.Functor.map_comp moduleSpecΓFunctor
      ((tilde.functor A).map (extendUnitId M))
      ((pushforwardSpecIdIso A).inv.app
        ((tilde.functor A).obj
          ((ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M))))

/-- And that is the unit of `extendScalarsTildeAdjunction (𝟙 A)`: the naturality of the unit of
the tilde--global-sections adjunction moves the associated sheaf of `m ↦ 1 ⊗ m` across, and
`map_pushforwardSpecIdIso_inv` identifies what is left. -/
theorem tildePullbackAdjunction_unit_comp_map_eq_unit (M : ModuleCat.{u} A) :
    (tilde.toTildeΓNatIso.hom.app M ≫
          moduleSpecΓFunctor.map ((tilde.functor A).map (extendUnitId M))) ≫
        moduleSpecΓFunctor.map
          ((pushforwardSpecIdIso A).inv.app
            ((tilde.functor A).obj
              ((ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M))) =
      (extendScalarsTildeAdjunction (𝟙 A)).unit.app M :=
  ((congrArg
          (fun z => (tilde.toTildeΓNatIso.hom.app M ≫
            moduleSpecΓFunctor.map ((tilde.functor A).map (extendUnitId M))) ≫ z)
          (map_pushforwardSpecIdIso_inv
            ((tilde.functor A).obj
              ((ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M)))).trans
        ((congrArg
            (fun z => z ≫ (pullbackSectionsIso (𝟙 A)).inv.app
              ((tilde.functor A).obj
                ((ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).obj M)))
            (toTildeΓNatIso_hom_naturality (extendUnitId M))).trans
          (Category.assoc _ _ _))).trans
    (extendScalarsTildeAdjunction_unit_app M).symm

/-- **The affine base-change comparison of [Stacks, Tag 01I9] at the identity ring map.** The
isomorphism `(Spec (𝟙 A))^* M̃ ≅ (A ⊗_A M)~` is the identity law for pullback followed by the
associated sheaf of the unit `m ↦ 1 ⊗ m` of extension of scalars.

Neither factor is an identity: `A ⊗_A M` is not `M` and `(Spec (𝟙 A))^*` is an abstract left
adjoint. What the statement says is that the comparison, which is built by uniqueness of left
adjoints and so has no formula, *is* the composite of the two canonical maps that are available.

The proof is the uniqueness itself:
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` evaluates the comparison after the unit
of `tildePullbackAdjunction (𝟙 A)`, and `eq_of_unit_comp` says that this determines a morphism
out of `(tilde.functor A ⋙ (Spec (𝟙 A))^*).obj M`; the four lemmas above evaluate the
right-hand side there. -/
@[stacks 01I9 "the affine base-change comparison at the identity ring map: the pullback of the
associated sheaf along Spec of the identity ring map is the identity law for pullback followed
by the associated sheaf of m ↦ 1 ⊗ m"]
theorem tildePullbackIso_id_hom_app (M : ModuleCat.{u} A) :
    (tildePullbackIso (𝟙 A)).hom.app M =
      ((Scheme.Modules.pullbackCongr (Spec.map_id A)).hom.app ((tilde.functor A).obj M) ≫
          (Scheme.Modules.pullbackId (Spec A)).hom.app ((tilde.functor A).obj M)) ≫
        (tilde.functor A).map (extendUnitId M) := by
  have key : (tildePullbackAdjunction (𝟙 A)).unit.app M ≫
      (pullbackSections (𝟙 A)).map ((tildePullbackIso (𝟙 A)).hom.app M) =
      (extendScalarsTildeAdjunction (𝟙 A)).unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ M
  exact Stacks.Conormal.eq_of_unit_comp_map (tildePullbackAdjunction (𝟙 A))
    (key.trans ((tildePullbackAdjunction_unit_comp_map M).trans
      ((tildePullbackAdjunction_unit_comp_map_eq M).trans
        (tildePullbackAdjunction_unit_comp_map_eq_unit M))).symm)

end SpecIdTilde

end SpecId

/-! ### The first tensor factor of the coefficient map at an identity -/

/-- **The identity law for the pullback along `Spec.map (𝟙 A)`**, the companion of
`Deformation.Artin.SectionsSheaf.pushforwardSpecIdIso`. -/
def pullbackSpecIdIso (A : CommRingCat.{u}) :
    Scheme.Modules.pullback (Spec.map (𝟙 A)) ≅ 𝟭 (Spec A).Modules :=
  Scheme.Modules.pullbackCongr (Spec.map_id A) ≪≫ Scheme.Modules.pullbackId (Spec A)

section FirstFactor

variable {A : CommRingCat.{u}}

/-- `pullbackSpecIdIso`, read as the composite of its two factors. -/
theorem pullbackSpecIdIso_hom_app (Z : (Spec A).Modules) :
    (pullbackSpecIdIso A).hom.app Z =
      (Scheme.Modules.pullbackCongr (Spec.map_id A)).hom.app Z ≫
        (Scheme.Modules.pullbackId (Spec A)).hom.app Z := rfl

/-- The inverse of `pullbackSpecIdIso`, read as the composite of its two factors. This is the
arrow that `pullbackComp_congr_comp_inv_app` produces at `u = Spec.map (𝟙 A)`. -/
theorem pullbackSpecIdIso_inv_app (Z : (Spec A).Modules) :
    (pullbackSpecIdIso A).inv.app Z =
      (Scheme.Modules.pullbackId (Spec A)).inv.app Z ≫
        (Scheme.Modules.pullbackCongr (Spec.map_id A)).inv.app Z := rfl

/-- **The unit `m ↦ 1 ⊗ m` followed by a semilinear map read as a map out of the base change is
the semilinear map itself.** This is the round trip of the `homEquiv` of
`ModuleCat.extendRestrictScalarsAdj` at the identity ring map, where restriction of scalars is
the identity functor on the nose. -/
theorem unit_comp_ofSemilinear_id {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    extendUnitId M ≫ ofSemilinear (𝟙 A) f = f :=
  ((ModuleCat.extendRestrictScalarsAdj (𝟙 A : A ⟶ A).hom).homEquiv_unit M N
      (ofSemilinear (𝟙 A) f)).symm.trans
    (((ModuleCat.extendRestrictScalarsAdj (𝟙 A : A ⟶ A).hom).homEquiv M N).apply_symm_apply f)

/-- **The coefficient tail of the first tensor factor at an identity.** The inverse of the
identity law for `(Spec (𝟙 A))^*`, then the comparison of [Stacks, Tag 01I9], then the
associated sheaf of the semilinear map, is the associated sheaf of the `A`-linear map itself:
the identity law cancels against the one `tildePullbackIso_id_hom_app` produces, and what
remains is the round trip `unit_comp_ofSemilinear_id`. -/
theorem pullbackSpecIdIso_inv_comp_tildePullbackIso_id {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    ((Scheme.Modules.pullbackId (Spec A)).inv.app ((tilde.functor A).obj M) ≫
          (Scheme.Modules.pullbackCongr (Spec.map_id A)).inv.app
            ((tilde.functor A).obj M)) ≫
        (tildePullbackIso (𝟙 A)).hom.app M ≫
          (tilde.functor A).map (ofSemilinear (𝟙 A) f) =
      (tilde.functor A).map f := by
  rw [← pullbackSpecIdIso_inv_app, tildePullbackIso_id_hom_app, ← pullbackSpecIdIso_hom_app,
    Category.assoc ((pullbackSpecIdIso A).hom.app ((tilde.functor A).obj M)),
    ← Category.assoc ((pullbackSpecIdIso A).inv.app ((tilde.functor A).obj M)),
    ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app, Category.id_comp,
    ← CategoryTheory.Functor.map_comp, unit_comp_ofSemilinear_id]

/-- `pullbackComp_congr_comp_inv_app` with a further arrow appended, so that it applies inside a
right-associated composite. -/
theorem pullbackComp_congr_comp_inv_app_assoc {X Y : Scheme.{u}} (π : X ⟶ Y) (u : Y ⟶ Y)
    (hu : u = 𝟙 Y) (hfst : (𝟙 X : X ⟶ X) ≫ π = π ≫ u) (G : Y.Modules) {Z : X.Modules}
    (z : (Scheme.Modules.pullback u ⋙ Scheme.Modules.pullback π).obj G ⟶ Z) :
    (Scheme.Modules.pullbackComp (𝟙 X) π).hom.app G ≫
        (Scheme.Modules.pullbackCongr hfst).hom.app G ≫
        ((Scheme.Modules.pullbackComp π u).app G).inv ≫ z =
      (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback π).obj G) ≫
        (Scheme.Modules.pullback π).map
            ((Scheme.Modules.pullbackId Y).inv.app G ≫
              (Scheme.Modules.pullbackCongr hu).inv.app G) ≫ z := by
  simpa only [Category.assoc] using
    congrArg (fun w => w ≫ z) (pullbackComp_congr_comp_inv_app π u hu hfst G)

/-- `pullbackComp_congr_comp_inv_app_assoc` with the unit of the pullback--pushforward
adjunction at `𝟙 X` in front: it cancels against the identity law at `X`, by
`unit_comp_pullbackId_hom_app`. -/
theorem unit_comp_pullbackComp_congr_comp_inv_app_assoc {X Y : Scheme.{u}} (π : X ⟶ Y)
    (u : Y ⟶ Y) (hu : u = 𝟙 Y) (hfst : (𝟙 X : X ⟶ X) ≫ π = π ≫ u) (G : Y.Modules)
    {Z : X.Modules}
    (z : (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback u).obj G) ⟶ Z) :
    pullbackIdUnit X ((Scheme.Modules.pullback π).obj G) ≫
        (Scheme.Modules.pullbackComp (𝟙 X) π).hom.app G ≫
        (Scheme.Modules.pullbackCongr hfst).hom.app G ≫
        ((Scheme.Modules.pullbackComp π u).app G).inv ≫ z =
      (Scheme.Modules.pullback π).map
          ((Scheme.Modules.pullbackId Y).inv.app G ≫
            (Scheme.Modules.pullbackCongr hu).inv.app G) ≫ z :=
  (whisker_eq _ (pullbackComp_congr_comp_inv_app_assoc π u hu hfst G z)).trans
    ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (unit_comp_pullbackId_hom_app X _) _).trans (Category.id_comp _)))

variable {X : Scheme.{u}} (π : X ⟶ Spec A)

/-- **The first of the two tensor factors of the coefficient map of Stacks 07YH degenerates at
an identity**: the unit of the pullback--pushforward adjunction at `𝟙 X`, followed by the map
`g^* π^* M̃ ⟶ π^* Ñ` of the first factor at `g = 𝟙 X` and the identity ring map, is `π^*` of the
associated sheaf of `f`.

This is the first of the two factor-wise obligations that the identity case of clause (2) of
Stacks 07YG reduces to by `Stacks.RingedSpace.unit_comp_comparisonIso_id`; the second is
`Deformation.Artin.SectionsSheaf.unit_comp_baseChangeSheafIsoGen_id`.

Three things degenerate at once, and each has its own lemma: the two `pullbackComp`s and the
`pullbackCongr` between them contract to the two identity laws for pullback, by
`pullbackComp_congr_comp_inv_app`; the unit cancels against the identity law at `X`, by
`unit_comp_pullbackId_hom_app`; and the identity law at `Spec A` cancels against the comparison
of [Stacks, Tag 01I9], by `pullbackSpecIdIso_inv_comp_tildePullbackIso_id`. -/
theorem unit_comp_tildeFirstFactorMapGen_id
    (hfst : (𝟙 X : X ⟶ X) ≫ π = π ≫ Spec.map (𝟙 A)) {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    pullbackIdUnit X ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M)) ≫
        tildeFirstFactorMapGen (𝟙 A) π π (𝟙 X) hfst (ofSemilinear (𝟙 A) f) =
      (Scheme.Modules.pullback π).map ((tilde.functor A).map f) := by
  have hfin : (Scheme.Modules.pullback π).map
        ((Scheme.Modules.pullbackId (Spec A)).inv.app ((tilde.functor A).obj M) ≫
          (Scheme.Modules.pullbackCongr (Spec.map_id A)).inv.app
            ((tilde.functor A).obj M)) ≫
        (Scheme.Modules.pullback π).map ((tildePullbackIso (𝟙 A)).hom.app M) ≫
          (Scheme.Modules.pullback π).map
            ((tilde.functor A).map (ofSemilinear (𝟙 A) f)) =
      (Scheme.Modules.pullback π).map ((tilde.functor A).map f) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      pullbackSpecIdIso_inv_comp_tildePullbackIso_id]
  have hd : tildeFirstFactorMapGen (𝟙 A) π π (𝟙 X) hfst (ofSemilinear (𝟙 A) f) =
      ((Scheme.Modules.pullbackComp (𝟙 X) π).hom.app ((tilde.functor A).obj M) ≫
          (Scheme.Modules.pullbackCongr hfst).hom.app ((tilde.functor A).obj M) ≫
          ((Scheme.Modules.pullbackComp π (Spec.map (𝟙 A))).app
              ((tilde.functor A).obj M)).inv ≫
            (Scheme.Modules.pullback π).map ((tildePullbackIso (𝟙 A)).hom.app M)) ≫
        (Scheme.Modules.pullback π).map
          ((tilde.functor A).map (ofSemilinear (𝟙 A) f)) := rfl
  have hassoc :
      ((Scheme.Modules.pullbackComp (𝟙 X) π).hom.app ((tilde.functor A).obj M) ≫
            (Scheme.Modules.pullbackCongr hfst).hom.app ((tilde.functor A).obj M) ≫
            ((Scheme.Modules.pullbackComp π (Spec.map (𝟙 A))).app
                ((tilde.functor A).obj M)).inv ≫
              (Scheme.Modules.pullback π).map ((tildePullbackIso (𝟙 A)).hom.app M)) ≫
          (Scheme.Modules.pullback π).map
            ((tilde.functor A).map (ofSemilinear (𝟙 A) f)) =
        (Scheme.Modules.pullbackComp (𝟙 X) π).hom.app ((tilde.functor A).obj M) ≫
          (Scheme.Modules.pullbackCongr hfst).hom.app ((tilde.functor A).obj M) ≫
          ((Scheme.Modules.pullbackComp π (Spec.map (𝟙 A))).app
              ((tilde.functor A).obj M)).inv ≫
            (Scheme.Modules.pullback π).map ((tildePullbackIso (𝟙 A)).hom.app M) ≫
              (Scheme.Modules.pullback π).map
                ((tilde.functor A).map (ofSemilinear (𝟙 A) f)) := by
    simp only [Category.assoc]
  have hfin : (Scheme.Modules.pullback π).map
        ((Scheme.Modules.pullbackId (Spec A)).inv.app ((tilde.functor A).obj M) ≫
          (Scheme.Modules.pullbackCongr (Spec.map_id A)).inv.app
            ((tilde.functor A).obj M)) ≫
        (Scheme.Modules.pullback π).map ((tildePullbackIso (𝟙 A)).hom.app M) ≫
          (Scheme.Modules.pullback π).map
            ((tilde.functor A).map (ofSemilinear (𝟙 A) f)) =
      (Scheme.Modules.pullback π).map ((tilde.functor A).map f) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      pullbackSpecIdIso_inv_comp_tildePullbackIso_id]
  exact (whisker_eq _ (hd.trans hassoc)).trans
    ((unit_comp_pullbackComp_congr_comp_inv_app_assoc π (Spec.map (𝟙 A)) (Spec.map_id A) hfst
        ((tilde.functor A).obj M)
        ((Scheme.Modules.pullback π).map ((tildePullbackIso (𝟙 A)).hom.app M) ≫
          (Scheme.Modules.pullback π).map
            ((tilde.functor A).map (ofSemilinear (𝟙 A) f)))).trans hfin)

end FirstFactor

end Deformation.Artin.SectionsSheaf

end
