module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentHmap
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue

/-!
# Descent of invertible modules through a limit of schemes, unconditionally

`StacksFrontier/AlgebraicGeometry/ModuleLimits/Invertible.lean` proves [Stacks Project,
Tag 0B8W] (2) — every invertible `𝒪_S`-module on the limit `S = lim Sᵢ` of a cofiltered system
of schemes is the pullback of an invertible `𝒪_{Sᵢ}`-module for some `i` — from two hypotheses,
which its implementation notes identify as the three clauses of Tag 01ZR.  All three clauses are
now proved, and this file discharges the hypotheses and states the tag unconditionally.

* `hDescend`, essential surjectivity, is Tag 01ZR (1):
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs`.  The
  match is on the nose apart from the finite-presentation hypothesis, which that theorem takes as
  an instance and `hDescend` as an argument.
* `hFullyFaithful` asks for an *isomorphism* at a stage, and Tag 01ZR (2)
  (`...exists_map_of_pullback_canonical_of_isLimit'`) descends only a *morphism*.  The reduction
  `Stacks.AlgebraicGeometry.ModuleLimits.fullyFaithful_of_exists_map_of_exists_isIso` of
  `Invertible.lean` splits the gap into descent of a morphism, which is Tag 01ZR (2) verbatim in
  its existential-identification form, and reflection of isomorphisms along one further step,
  which is `exists_isIso_pullback_of_isLimit` below.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isIso_pullback_of_isLimit`: reflection of
  isomorphisms.  A morphism of finitely presented modules at a stage whose pullback to the limit
  is an isomorphism is already an isomorphism after one further transition morphism.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_iso_pullback_of_isLimit`: two finitely presented
  modules at a stage whose pullbacks to the limit are isomorphic are isomorphic at a later stage.
  This is the `hFullyFaithful` input of `Invertible.lean`, discharged.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit`:
  **Stacks Project, Tag 0B8W (2)**, with no hypotheses beyond those of the tag.

## Implementation notes

**Reflection of isomorphisms.**  Let `ψ : A ⟶ B` be a morphism of finitely presented modules at
the stage `j` whose pullback to the limit is invertible.  Tag 01ZR (2) descends the *inverse* of
`(c.π.app j)^* ψ` to a morphism `θ` at some stage `m` over `j`, pinned by the canonical
identification `Stacks.AlgebraicGeometry.ModuleLimits.canHom`.  Naturality of
`Stacks.AlgebraicGeometry.ModuleLimits.canNatIso` turns that pinning into the statement that both
composites of `(D.map e)^* ψ` with `θ` pull back to the identity on the limit, so Tag 01ZR (3)
makes each composite *equal* to the identity at a stage over `m` — two stages, one per composite.
A single stage carrying both is produced by cofilteredness in two steps: `cone_objs` gives an
object below the two, and `cone_maps` then equalises the two resulting transition morphisms down
to `m`, which is needed because the two equalities must hold over *the same* morphism before they
can be read as the two halves of an inverse.  The composite over that stage is an isomorphism, and
`CategoryTheory.NatIso.isIso_map_iff` moves the conclusion from the iterated pullback to the
pullback along the composite transition morphism.

**The index universes.**  The index object universe is the universe of the schemes, because that
is where the proved clauses (2) and (3) of Tag 01ZR live; the index morphism universe stays free,
those clauses having been freed of it through `CategoryTheory.Functor.FullImage`.  The
implementation notes of `Invertible.lean` record this restriction as the obstruction to
discharging `hFullyFaithful`; it is a restriction on the index objects only, and the conditional
theorems there remain stated with all three universes independent.

**Quasi-compactness and quasi-separatedness.**  The tag assumes every stage quasi-compact and
quasi-separated, and so does this file: clause (2) of Tag 01ZR needs both at the stage carrying
the modules, clause (3) needs quasi-compactness there, and the stages at which they are applied
are produced by the argument rather than chosen, so the hypotheses are taken for all stages.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

include c in
/-- **Reflection of isomorphisms through the limit**, from Tag 01ZR (2) and (3).  A morphism
`ψ : A ⟶ B` of sheaves of modules of finite presentation on a stage `D.obj j` whose pullback to
the limit is an isomorphism already has invertible pullback along some transition morphism
`g : k ⟶ j`.

Tag 01ZR (2) descends the inverse of `(c.π.app j)^* ψ` to a morphism `θ` at a stage `m` over `j`,
compatibly with the canonical identifications; naturality of those identifications then says that
both composites of `(D.map e)^* ψ` with `θ` have identity pullback to the limit, and Tag 01ZR (3)
makes each an identity at a stage over `m`.  Cofilteredness produces one stage, and one transition
morphism to `m`, at which both hold. -/
theorem exists_isIso_pullback_of_isLimit (hc : IsLimit c) [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (j : I) (A B : (D.obj j).Modules) (hA : A.IsFinitePresentation)
    (hB : B.IsFinitePresentation) (ψ : A ⟶ B)
    (hψ : IsIso ((Scheme.Modules.pullback (c.π.app j)).map ψ)) :
    ∃ (k : I) (g : k ⟶ j), IsIso ((Scheme.Modules.pullback (D.map g)).map ψ) := by
  have hA' := hA
  have hB' := hB
  -- Tag 01ZR (2): descend the inverse of `(c.π.app j)^* ψ` to a stage `m`.
  obtain ⟨m, e, θ, hθ⟩ := exists_map_of_pullback_canonical_of_isLimit' D c hc j B A
    (inv ((Scheme.Modules.pullback (c.π.app j)).map ψ))
  have hAe : ((Scheme.Modules.pullback (D.map e)).obj A).IsFinitePresentation :=
    isFinitePresentation_pullback (D.map e) A
  have hBe : ((Scheme.Modules.pullback (D.map e)).obj B).IsFinitePresentation :=
    isFinitePresentation_pullback (D.map e) B
  have hnat : (Scheme.Modules.pullback (c.π.app m)).map
        ((Scheme.Modules.pullback (D.map e)).map ψ) ≫
        canHom (c.π.app m) (D.map e) (c.π.app j) (c.w e) B =
      canHom (c.π.app m) (D.map e) (c.π.app j) (c.w e) A ≫
        (Scheme.Modules.pullback (c.π.app j)).map ψ :=
    (canNatIso (c.π.app m) (D.map e) (c.π.app j) (c.w e)).hom.naturality ψ
  -- Both composites pull back to the identity on the limit.
  have e1 : (Scheme.Modules.pullback (c.π.app m)).map
        ((Scheme.Modules.pullback (D.map e)).map ψ ≫ θ) =
      (Scheme.Modules.pullback (c.π.app m)).map
        (𝟙 ((Scheme.Modules.pullback (D.map e)).obj A)) := by
    rw [← cancel_mono (canHom (c.π.app m) (D.map e) (c.π.app j) (c.w e) A),
      CategoryTheory.Functor.map_id, Category.id_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, hθ, ← Category.assoc, hnat, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have e2 : (Scheme.Modules.pullback (c.π.app m)).map
        (θ ≫ (Scheme.Modules.pullback (D.map e)).map ψ) =
      (Scheme.Modules.pullback (c.π.app m)).map
        (𝟙 ((Scheme.Modules.pullback (D.map e)).obj B)) := by
    rw [← cancel_mono (canHom (c.π.app m) (D.map e) (c.π.app j) (c.w e) B),
      CategoryTheory.Functor.map_id, Category.id_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, hnat, ← Category.assoc, hθ, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  -- Tag 01ZR (3), once per composite, and a single stage carrying both conclusions.
  obtain ⟨n₁, g₁, h1⟩ := exists_pullback_map_eq_of_isLimit' D c hc m _ _ _ _ e1
  obtain ⟨n₂, g₂, h2⟩ := exists_pullback_map_eq_of_isLimit' D c hc m _ _ _ _ e2
  obtain ⟨p, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs n₁ n₂
  obtain ⟨W, t, ht⟩ := IsCofilteredOrEmpty.cone_maps (a ≫ g₁) (b ≫ g₂)
  have hgW : (t ≫ a) ≫ g₁ = (t ≫ b) ≫ g₂ := by
    simpa only [Category.assoc] using ht
  have e1' := pullback_map_eq_of_precomp (D.map (t ≫ a)) (D.map g₁) h1
  have e2' := pullback_map_eq_of_precomp (D.map (t ≫ b)) (D.map g₂) h2
  rw [← D.map_comp] at e1' e2'
  rw [← hgW] at e2'
  have hfin : IsIso ((Scheme.Modules.pullback (D.map e) ⋙
      Scheme.Modules.pullback (D.map ((t ≫ a) ≫ g₁))).map ψ) :=
    ⟨(Scheme.Modules.pullback (D.map ((t ≫ a) ≫ g₁))).map θ,
      by simpa [← Functor.map_comp] using e1', by simpa [← Functor.map_comp] using e2'⟩
  exact ⟨W, ((t ≫ a) ≫ g₁) ≫ e, (NatIso.isIso_map_iff
    (canNatIso (D.map ((t ≫ a) ≫ g₁)) (D.map e) (D.map (((t ≫ a) ≫ g₁) ≫ e))
      (D.map_comp ((t ≫ a) ≫ g₁) e).symm) ψ).mp hfin⟩

include c in
/-- **Essential fullness of pullback through the limit**, from the three clauses of Tag 01ZR: two
sheaves of modules of finite presentation on a stage whose pullbacks to the limit are isomorphic
are already isomorphic after some transition morphism.

This is the `hFullyFaithful` input of
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit_of_descent`,
obtained from the reduction `fullyFaithful_of_exists_map_of_exists_isIso` by supplying descent of
a morphism from Tag 01ZR (2) and reflection of isomorphisms from
`exists_isIso_pullback_of_isLimit`. -/
theorem exists_iso_pullback_of_isLimit (hc : IsLimit c) [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (A B : (D.obj i).Modules) (hA : A.IsFinitePresentation)
    (hB : B.IsFinitePresentation)
    (h : Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj A ≅
      (Scheme.Modules.pullback (c.π.app i)).obj B)) :
    ∃ (j : I) (e : j ⟶ i), Nonempty ((Scheme.Modules.pullback (D.map e)).obj A ≅
      (Scheme.Modules.pullback (D.map e)).obj B) :=
  fullyFaithful_of_exists_map_of_exists_isIso D c
    (fun i' A' B' hA' hB' φ => by
      have hA'' := hA'
      have hB'' := hB'
      obtain ⟨j, e, φj, hφj⟩ := exists_map_of_pullback_canonical_of_isLimit' D c hc i' A' B' φ
      exact ⟨j, e, φj, asIso (canHom (c.π.app j) (D.map e) (c.π.app i') (c.w e) A'),
        asIso (canHom (c.π.app j) (D.map e) (c.π.app i') (c.w e) B'), hφj⟩)
    (exists_isIso_pullback_of_isLimit D c hc) i A B hA hB h

include c in
/-- **Stacks Project, Tag 0B8W (2).**  Let `S = lim Sᵢ` be the limit of a cofiltered system of
quasi-compact quasi-separated schemes with affine transition morphisms.  Then every invertible
`𝒪_S`-module is the pullback of an invertible `𝒪_{Sᵢ}`-module for some `i`.

This is `exists_isInvertible_pullback_iso_of_isLimit_of_descent` with its two hypotheses
discharged: `hDescend` by Tag 01ZR (1), `hFullyFaithful` by `exists_iso_pullback_of_isLimit`,
which rests on Tag 01ZR (2) and (3). -/
@[stacks 0B8W "(2)"]
theorem exists_isInvertible_pullback_iso_of_isLimit
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (hc : IsLimit c)
    (L : c.pt.Modules)
    (hL : IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property L) :
    ∃ (i : I) (Lᵢ : (D.obj i).Modules),
      IsInvertible (D.obj i).sheaf.obj (D.obj i).ringCatSheaf.property Lᵢ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback (c.π.app i)).obj Lᵢ) :=
  exists_isInvertible_pullback_iso_of_isLimit_of_descent D c
    (fun F hF => by
      have hF' := hF
      exact exists_isFinitePresentation_pullback_iso_of_qcqs D c hc F)
    (exists_iso_pullback_of_isLimit D c hc) L hL

end Stacks.AlgebraicGeometry.ModuleLimits

end
