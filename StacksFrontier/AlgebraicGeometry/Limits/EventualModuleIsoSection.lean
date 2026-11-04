module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitDescentHom

/-!
# Descending an isomorphism of modules together with prescribed sections

Let `G` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine transition
morphisms, let `cG` be a limit cone on it, and let `A` and `B` be sheaves of modules of finite
presentation on a stage `G.obj j₀`.  An isomorphism `N` between the pullbacks of `A` and `B` to
the limit is the pullback of an isomorphism at a later stage; that is
`AlgebraicGeometry.exists_stage_isIso_pullback_map`, Tag 01ZR (2) together with the reflection of
isomorphisms of Tag 01ZR (3).

This file refines that statement by one further datum.  Suppose `P` is a third module of finite
presentation at the stage and `a : P ⟶ A`, `b : P ⟶ B` are two morphisms whose pullbacks to the
limit are identified by `N`, in the sense that `π^*a ≫ N = π^*b`.  Then the isomorphism can be
found at a stage where it identifies `a` with `b` as well.

The intended reading is that `A` is a free module, `N` a trivialisation of `B` over the limit and
`a`, `b` a prescribed basis vector and a prescribed section: the conclusion then says that the
trivialisation descends *carrying the prescribed vector to the prescribed section*, which the
descent of the isomorphism alone does not give.  That is what makes a trivialisation of the
algebra of a finite locally free cover whose first basis vector is the unit descend to one with
the same property, since being a unit-first basis is exactly such an identification of a basis
vector with a section.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.canStep_comp_eq_of_further_step`: an identification of
  two morphisms out of a third module, valid after pulling the isomorphism back one stage
  further, holds for the morphism `Stacks.AlgebraicGeometry.ModuleLimits.canStep` produces at
  that stage.
* `AlgebraicGeometry.exists_stage_isIso_pullback_map_comp_eq`: **the refinement.**  Tag 01ZR (2)
  and (3), descending an isomorphism of pullbacks of finitely presented modules from the limit to
  a stage together with an identification of two prescribed morphisms out of a third finitely
  presented module.

## Implementation notes

The two steps are sequential and each pushes the stage once, so no common refinement of two
indices is ever taken.

The isomorphism is first descended by `AlgebraicGeometry.exists_stage_isIso_pullback_map`, which
returns a stage `j₁`, a transition `e₁` and an isomorphism `m₁` satisfying the canonical equation
over the limit.  At that stage the two morphisms `e₁^*a ≫ m₁` and `e₁^*b` out of `e₁^*P` have
equal pullbacks to the limit: composing with the canonical identification
`Stacks.AlgebraicGeometry.ModuleLimits.canHom`, which is a monomorphism, turns that comparison
into the canonical equation for `m₁` and the naturality of `canHom` in the module, with the
hypothesis on `a`, `b` and `N` in between.  Tag 01ZR (3) in the form
`Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit'` then makes them equal
at a later stage `j₂`.

The isomorphism is carried from `j₁` to `j₂` by
`Stacks.AlgebraicGeometry.ModuleLimits.canStep`, whose canonical equation over the limit is
`...canonical_eq_of_further_step` and whose identification of `a` with `b` is
`canStep_comp_eq_of_further_step` here.  Both are proved by cancelling the canonical
identification and using its naturality; no further coherence of the pullback pseudofunctor
beyond its cocycle `Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp` enters.

`canStep_comp_eq_of_further_step` is stated for arbitrary schemes and arbitrary modules, with
every composite supplied as a hypothesis, so that a diagram whose transition morphism is
`G.map (e₂ ≫ e₁)` can be fed to it with `CategoryTheory.Functor.map_comp`.

No `@[stacks]` attribute is placed here.  The clauses of **Stacks 01ZR** this rests on are tagged
where they are proved, in `StacksFrontier/AlgebraicGeometry/ModuleLimits/`; the statement below is a
joint strengthening of two of them by a datum the tag does not mention, and it asserts no tag of
its own.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open Stacks.AlgebraicGeometry.ModuleLimits (canHom canIso canIso_hom canStep canHom_naturality
  canonical_eq_of_further_step isFinitePresentation_pullback isIso_canHom
  exists_pullback_map_eq_of_isLimit')

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### Carrying an identification of two morphisms one stage further -/

/-- **An identification of two morphisms out of a third module is carried one stage further by
`Stacks.AlgebraicGeometry.ModuleLimits.canStep`.**  Let `Zk ⟶ Zj ⟶ Zi` be a chain with
`m ≫ g = mg`, let `a : P ⟶ F` and `b : P ⟶ E` be morphisms of modules on `Zi`, and let `ψ` be a
morphism of the pullbacks along `g` of `F` and `E`.  If the pullback along `m` of `g^*a ≫ ψ`
agrees with the pullback along `m` of `g^*b`, then `canStep m g mg hmg ψ` carries `mg^*a` to
`mg^*b`.

Composing with the canonical identification `Stacks.AlgebraicGeometry.ModuleLimits.canHom` at
`P`, which is an isomorphism, reduces this to the hypothesis together with the naturality of
`canHom` in the module, read at `a` and at `b`. -/
theorem canStep_comp_eq_of_further_step {Zk Zj Zi : Scheme.{u}} (m : Zk ⟶ Zj) (g : Zj ⟶ Zi)
    (mg : Zk ⟶ Zi) (hmg : m ≫ g = mg) {P F E : Zi.Modules} (a : P ⟶ F) (b : P ⟶ E)
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj E)
    (h : (Scheme.Modules.pullback m).map ((Scheme.Modules.pullback g).map a ≫ ψ)
      = (Scheme.Modules.pullback m).map ((Scheme.Modules.pullback g).map b)) :
    (Scheme.Modules.pullback mg).map a ≫ canStep m g mg hmg ψ
      = (Scheme.Modules.pullback mg).map b := by
  refine (cancel_epi (canHom m g mg hmg P)).mp ?_
  rw [← Category.assoc, ← canHom_naturality m g mg hmg a, ← canHom_naturality m g mg hmg b,
    canStep]
  simp only [Category.assoc, ← canIso_hom m g mg hmg F]
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp, h, canIso_hom]

end Stacks.AlgebraicGeometry.ModuleLimits

namespace AlgebraicGeometry

/-! ### The refinement of the descent of an isomorphism -/

/-- **Stacks 01ZR (2) and (3), descending an isomorphism together with prescribed sections.**
Let `cG` be a limit cone on a cofiltered diagram `G` of quasi-compact quasi-separated schemes
with affine transition morphisms, let `P`, `A` and `Bm` be sheaves of modules of finite
presentation on a stage `G.obj j₀`, and let `a : P ⟶ A` and `b : P ⟶ Bm`.  Suppose `N` is an
isomorphism of the pullbacks of `A` and `Bm` to the limit which identifies the pullback of `a`
with the pullback of `b`.  Then there is a stage over `j₀` carrying an isomorphism of the
pullbacks of `A` and `Bm` which, through the canonical identifications, is `N` over the limit,
and which identifies the pullback of `a` with the pullback of `b` already at that stage.

The isomorphism is descended by `AlgebraicGeometry.exists_stage_isIso_pullback_map`; the two
morphisms it then has to identify have equal pullbacks to the limit, so Tag 01ZR (3) identifies
them at a later stage, to which the isomorphism is carried by
`Stacks.AlgebraicGeometry.ModuleLimits.canStep`. -/
theorem exists_stage_isIso_pullback_map_comp_eq {J : Type u} [Category.{u} J] [IsCofiltered J]
    (G : J ⥤ Scheme.{u}) [∀ {a b : J} (g : a ⟶ b), IsAffineHom (G.map g)]
    (cG : Cone G) (hcG : IsLimit cG) [∀ a : J, CompactSpace (G.obj a)]
    [∀ a : J, QuasiSeparatedSpace (G.obj a)] (j₀ : J)
    (P A Bm : (G.obj j₀).Modules) (hP : P.IsFinitePresentation)
    (hA : A.IsFinitePresentation) (hB : Bm.IsFinitePresentation)
    (N : (Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj A ≅
      (Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).obj Bm)
    (a : P ⟶ A) (b : P ⟶ Bm)
    (hab : (Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).map a ≫ N.hom
      = (Scheme.Modules.pullback (X := cG.pt) (cG.π.app j₀)).map b) :
    ∃ (j : J) (ee : j ⟶ j₀)
      (mm : (Scheme.Modules.pullback (G.map ee)).obj A ≅
        (Scheme.Modules.pullback (G.map ee)).obj Bm),
      (Scheme.Modules.pullback (X := cG.pt) (cG.π.app j)).map mm.hom ≫
            canHom (W := cG.pt) (cG.π.app j) (G.map ee) (cG.π.app j₀) (cG.w ee) Bm =
          canHom (W := cG.pt) (cG.π.app j) (G.map ee) (cG.π.app j₀) (cG.w ee) A ≫ N.hom ∧
        (Scheme.Modules.pullback (G.map ee)).map a ≫ mm.hom =
          (Scheme.Modules.pullback (G.map ee)).map b := by
  have := hP
  have := hA
  have := hB
  obtain ⟨j₁, e₁, m₁, h₁⟩ :=
    exists_stage_isIso_pullback_map G cG hcG j₀ A Bm hA hB N
  -- the two morphisms out of `e₁^*P` that the descended isomorphism has to identify
  have hkey : (Scheme.Modules.pullback (cG.π.app j₁)).map
        ((Scheme.Modules.pullback (G.map e₁)).map a ≫ m₁.hom)
      = (Scheme.Modules.pullback (cG.π.app j₁)).map
        ((Scheme.Modules.pullback (G.map e₁)).map b) := by
    refine (cancel_mono (canHom (cG.π.app j₁) (G.map e₁) (cG.π.app j₀) (cG.w e₁) Bm)).mp ?_
    rw [CategoryTheory.Functor.map_comp, Category.assoc, h₁, ← Category.assoc,
      canHom_naturality (cG.π.app j₁) (G.map e₁) (cG.π.app j₀) (cG.w e₁) a, Category.assoc,
      hab, canHom_naturality (cG.π.app j₁) (G.map e₁) (cG.π.app j₀) (cG.w e₁) b]
  have hPe : ((Scheme.Modules.pullback (G.map e₁)).obj P).IsFinitePresentation :=
    isFinitePresentation_pullback _ P
  have hBe : ((Scheme.Modules.pullback (G.map e₁)).obj Bm).IsFinitePresentation :=
    isFinitePresentation_pullback _ Bm
  obtain ⟨j₂, e₂, h₂⟩ := exists_pullback_map_eq_of_isLimit' G cG hcG j₁
    ((Scheme.Modules.pullback (G.map e₁)).obj P)
    ((Scheme.Modules.pullback (G.map e₁)).obj Bm)
    ((Scheme.Modules.pullback (G.map e₁)).map a ≫ m₁.hom)
    ((Scheme.Modules.pullback (G.map e₁)).map b) hkey
  refine ⟨j₂, e₂ ≫ e₁,
    (canIso (G.map e₂) (G.map e₁) (G.map (e₂ ≫ e₁)) (G.map_comp e₂ e₁).symm A).symm ≪≫
      asIso ((Scheme.Modules.pullback (G.map e₂)).map m₁.hom) ≪≫
        canIso (G.map e₂) (G.map e₁) (G.map (e₂ ≫ e₁)) (G.map_comp e₂ e₁).symm Bm, ?_, ?_⟩
  · exact canonical_eq_of_further_step (cG.π.app j₂) (G.map e₂) (cG.π.app j₁) (cG.w e₂)
      (G.map e₁) (cG.π.app j₀) (cG.w e₁) (G.map (e₂ ≫ e₁)) (G.map_comp e₂ e₁).symm
      (cG.w (e₂ ≫ e₁)) m₁.hom N.hom h₁
  · exact Stacks.AlgebraicGeometry.ModuleLimits.canStep_comp_eq_of_further_step
      (G.map e₂) (G.map e₁) (G.map (e₂ ≫ e₁))
      (G.map_comp e₂ e₁).symm a b m₁.hom h₂

end AlgebraicGeometry

end
