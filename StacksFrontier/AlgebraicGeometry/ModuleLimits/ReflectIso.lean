module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentRefine
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue

/-!
# Reflection of isomorphisms through the limit

The *reflection of isomorphisms*: a morphism of finitely presented modules at a stage of a
cofiltered system of quasi-compact quasi-separated schemes with affine transition morphisms whose
pullback to the limit is an isomorphism is already an isomorphism at some later stage.  It follows
from [Stacks Project, Tag 01ZR] (2) in its canonically pinned form together with Tag 01ZR (3),
both of which are proved in
`StacksFrontier/AlgebraicGeometry/ModuleLimits/LocalDescentRefine.lean` and
`StacksFrontier/AlgebraicGeometry/ModuleLimits/EventualMapEq.lean`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.isIso_pullback_map_comp_iff` and
  `...pullback_map_comp_eq_iff`: the iterated pullback of a morphism is an isomorphism, resp.
  equal to the iterated pullback of another, exactly when the pullback along the composite is.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isIso_pullback_map_of_isLimit`: **the reflection
  of isomorphisms through the limit.**

## Implementation notes

**The canonical form of Tag 01ZR (2) is what makes the reflection work, and the existential form
does not.**  Given `ψ : A ⟶ B` at the stage `j` whose pullback to the limit is invertible, descend
the *inverse* of that pullback to a morphism `Φ` at some stage `k` over `j`.  The two composites
`ψ ≫ Φ` and `Φ ≫ ψ` at `k` must then be shown to pull back to identities, and that comparison
divides by the identification of `(c.π.app k)^* (D.map e)^* A` with `(c.π.app j)^* A`.  With the
*canonical* identification `Stacks.AlgebraicGeometry.ModuleLimits.canHom` this is immediate from
`...canHom_naturality` and the fact that `canHom` is an isomorphism; with an unconstrained
existential identification it is not available at all, which is the obstruction recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/ModuleLimits/Invertible.lean`.

**The two applications of Tag 01ZR (3) are sequential, not merged.**  Each of the two composites
needs its own appeal to eventual equality, and the two appeals return different stages.  Rather
than taking a common refinement and equalising the two legs — which would need a further
cofiltered step and a transport for each equation — the second appeal is made *at the stage the
first returned*: the equation for `Φ ≫ ψ` is carried from `k` to that stage by
`pullback_map_comp_eq_iff`, and the equation for `ψ ≫ Φ` is carried forward by applying the
pullback functor to it.  Both then hold at one stage, with no equalisation.

Only after both composites are identities is the three-fold iterated pullback compared with the
pullback along the composite index morphism, and that comparison is made on the *property* of
being an isomorphism rather than on any morphism, by two applications of
`isIso_pullback_map_comp_iff`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### Crossing the canonical identification -/

section Canonical

/-- The iterated pullback of a morphism of modules is an isomorphism exactly when the pullback
along the composite is, the two being conjugate by the canonical identification
`Stacks.AlgebraicGeometry.ModuleLimits.canHom`, which is an isomorphism. -/
theorem isIso_pullback_map_comp_iff {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) {F F' : X.Modules} (χ : F ⟶ F') :
    IsIso ((Scheme.Modules.pullback q).map ((Scheme.Modules.pullback g).map χ)) ↔
      IsIso ((Scheme.Modules.pullback pi).map χ) := by
  rw [← isIso_comp_left_iff (canHom q g pi hpi F) ((Scheme.Modules.pullback pi).map χ),
    ← canHom_naturality, isIso_comp_right_iff]

/-- Two morphisms of modules have equal iterated pullbacks exactly when they have equal pullbacks
along the composite. -/
theorem pullback_map_comp_eq_iff {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) {F F' : X.Modules} (α β : F ⟶ F') :
    (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback g).map α) =
        (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback g).map β) ↔
      (Scheme.Modules.pullback pi).map α = (Scheme.Modules.pullback pi).map β := by
  rw [← cancel_mono (canHom q g pi hpi F'), canHom_naturality, canHom_naturality,
    cancel_epi (canHom q g pi hpi F)]

/-- If `Φ` matches the inverse of the pullback of `ψ` along the composite under the canonical
identification, then both composites of `Φ` with the pullback of `ψ` pull back to identities. -/
theorem pullback_map_comp_eq_id_of_comp_canHom_eq {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X)
    (pi : W ⟶ X) (hpi : q ≫ g = pi) {A B : X.Modules} (ψ : A ⟶ B)
    [IsIso ((Scheme.Modules.pullback pi).map ψ)]
    (Φ : (Scheme.Modules.pullback g).obj B ⟶ (Scheme.Modules.pullback g).obj A)
    (hΦ : (Scheme.Modules.pullback q).map Φ ≫ canHom q g pi hpi A =
      canHom q g pi hpi B ≫ inv ((Scheme.Modules.pullback pi).map ψ)) :
    (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback g).map ψ ≫ Φ) =
        (Scheme.Modules.pullback q).map (𝟙 ((Scheme.Modules.pullback g).obj A)) ∧
      (Scheme.Modules.pullback q).map (Φ ≫ (Scheme.Modules.pullback g).map ψ) =
        (Scheme.Modules.pullback q).map (𝟙 ((Scheme.Modules.pullback g).obj B)) := by
  have hnat := canHom_naturality q g pi hpi ψ
  constructor
  · rw [← cancel_mono (canHom q g pi hpi A), Functor.map_comp, Category.assoc, hΦ,
      ← Category.assoc, hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp
  · rw [← cancel_mono (canHom q g pi hpi B), Functor.map_comp, Category.assoc, hnat,
      ← Category.assoc, hΦ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    simp

end Canonical

/-! ### Reflection of isomorphisms -/

section Limit

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- **The reflection of isomorphisms through the limit**, from [Stacks Project, Tag 01ZR] (2) and
(3).  Let `c` be a limit cone on a cofiltered diagram `D` of quasi-compact quasi-separated schemes
with affine transition morphisms, and let `ψ : A ⟶ B` be a morphism of sheaves of modules of
finite presentation on a stage `D.obj j`.  If the pullback of `ψ` to the limit is an isomorphism,
then the pullback of `ψ` to some stage over `j` is already an isomorphism.

The inverse of the pullback of `ψ` descends to a morphism `Φ` at a stage by Tag 01ZR (2) in its
canonically pinned form, the two composites of `ψ` with `Φ` then pull back to identities, and
Tag 01ZR (3) makes them identities at a later stage. -/
theorem exists_isIso_pullback_map_of_isLimit (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (j : I) (A B : (D.obj j).Modules) [A.IsFinitePresentation] [B.IsFinitePresentation]
    (ψ : A ⟶ B) (hψ : IsIso ((Scheme.Modules.pullback (c.π.app j)).map ψ)) :
    ∃ (k : I) (g : k ⟶ j), IsIso ((Scheme.Modules.pullback (D.map g)).map ψ) := by
  obtain ⟨k, e, Φ, hΦ⟩ := exists_map_of_pullback_of_isLimit D c hc j B A
    (inv ((Scheme.Modules.pullback (c.π.app j)).map ψ))
  have hcan : ∀ F : (D.obj j).Modules,
      canHom (c.π.app k) (D.map e) (c.π.app j) (c.w e) F =
        (Scheme.Modules.pullbackComp (c.π.app k) (D.map e)).hom.app F ≫
          (Scheme.Modules.pullbackCongr (c.w e)).hom.app F := fun _ => rfl
  rw [← hcan, ← Category.assoc, ← hcan] at hΦ
  obtain ⟨hEq1, hEq2⟩ :=
    pullback_map_comp_eq_id_of_comp_canHom_eq (c.π.app k) (D.map e) (c.π.app j) (c.w e) ψ Φ hΦ
  have hA' : ((Scheme.Modules.pullback (D.map e)).obj A).IsFinitePresentation :=
    isFinitePresentation_pullback (D.map e) A
  have hB' : ((Scheme.Modules.pullback (D.map e)).obj B).IsFinitePresentation :=
    isFinitePresentation_pullback (D.map e) B
  obtain ⟨l₁, h₁, hl₁⟩ := exists_pullback_map_eq_of_isLimit' D c hc k
    ((Scheme.Modules.pullback (D.map e)).obj A) ((Scheme.Modules.pullback (D.map e)).obj A)
    ((Scheme.Modules.pullback (D.map e)).map ψ ≫ Φ) (𝟙 _) hEq1
  have hB'' : ((Scheme.Modules.pullback (D.map h₁)).obj
      ((Scheme.Modules.pullback (D.map e)).obj B)).IsFinitePresentation :=
    isFinitePresentation_pullback (D.map h₁) _
  obtain ⟨l₂, h₂, hl₂⟩ := exists_pullback_map_eq_of_isLimit' D c hc l₁
    ((Scheme.Modules.pullback (D.map h₁)).obj ((Scheme.Modules.pullback (D.map e)).obj B))
    ((Scheme.Modules.pullback (D.map h₁)).obj ((Scheme.Modules.pullback (D.map e)).obj B))
    ((Scheme.Modules.pullback (D.map h₁)).map
      (Φ ≫ (Scheme.Modules.pullback (D.map e)).map ψ))
    ((Scheme.Modules.pullback (D.map h₁)).map
      (𝟙 ((Scheme.Modules.pullback (D.map e)).obj B)))
    ((pullback_map_comp_eq_iff (c.π.app l₁) (D.map h₁) (c.π.app k) (c.w h₁) _ _).mpr hEq2)
  have hiso : IsIso ((Scheme.Modules.pullback (D.map h₂)).map
      ((Scheme.Modules.pullback (D.map h₁)).map
        ((Scheme.Modules.pullback (D.map e)).map ψ))) := by
    refine ⟨(Scheme.Modules.pullback (D.map h₂)).map
      ((Scheme.Modules.pullback (D.map h₁)).map Φ), ?_, ?_⟩ <;>
      simp [← Functor.map_comp, hl₁, hl₂]
  exact ⟨l₂, (h₂ ≫ h₁) ≫ e,
    (isIso_pullback_map_comp_iff (D.map (h₂ ≫ h₁)) (D.map e) (D.map ((h₂ ≫ h₁) ≫ e))
      (D.map_comp (h₂ ≫ h₁) e).symm ψ).mp
      ((isIso_pullback_map_comp_iff (D.map h₂) (D.map h₁) (D.map (h₂ ≫ h₁))
        (D.map_comp h₂ h₁).symm ((Scheme.Modules.pullback (D.map e)).map ψ)).mp hiso)⟩

end Limit

end Stacks.AlgebraicGeometry.ModuleLimits

end
