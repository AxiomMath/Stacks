module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistComparison

/-!
# The twisted Frobenius twist of a constant sheaf is the self-map twist

Let `Y` be a scheme over a finite field `k`, `σ : Y ⟶ Y` a morphism over `k`, `k̄` an extension of
`k` and `φ = σ̄ ≫ π̄` the twisted geometric Frobenius of `Y_k̄`. For a module `M`, the twist
`M_Y|_{Y_k̄} ⟶ φ_*(M_Y|_{Y_k̄})` of `Stacks.EtaleCohomology.twistedFrobeniusTwist`, attached to the
canonical map `M_Y ⟶ σ_* M_Y`, is built from the Frobenius descent isomorphism of
[Stacks, Tag 03SR], the restriction of `ε` and a base change map. Each of these sends the pulled
back constant section to a restriction of it, hence so does the twist; the same holds for the
self-map twist of `φ` over `Spec k̄`. Transported to the constant sheaf `M_{Y_k̄}`, both twists
therefore fix the constant section, and maps out of a constant sheaf are determined by it.

This identifies the endomorphism `(g^{-1} π)^*` coming from the canonical Frobenius `π_X^*` with
the one of Weil's formula in Step 9 of the proof of [Stacks, Tag 03UG].

## Main results

* `Stacks.EtaleCohomology.exists_pulledBackConstantSection_comp_automorphismBaseChange`.
* `Stacks.EtaleCohomology.comp_map_comp_hom_app_eq_map`: a composite of twists fixing a section up
  to restriction fixes it up to restriction.
* `Stacks.EtaleCohomology.exists_pulledBackConstantSection_comp_twistedFrobeniusTwist`.
* `Stacks.EtaleCohomology.transportedConstantTwist_twistedFrobeniusTwist`: the comparison.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 8 and 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology


/-! ### The twisted Frobenius twist fixes constant sections -/

section TwistedFix

variable (Λ : Type r) [Ring Λ] (M : ModuleCat.{max (u + 1) r} Λ) {k : Type u} [Field k]
  [Fintype k] (Y : Over (Spec (.of k))) (σ : Y ⟶ Y) (kbar : Type u) [Field kbar] [Algebra k kbar]

private lemma autChase {D : Type*} [Category D] {A B1 B2 E E2 E3 E' : D} (κ : A ⟶ B1)
    (u : B1 ⟶ E) (eps0 : E ⟶ E2) (bc0 : E2 ⟶ E3) (ε : B1 ⟶ B2) (uσ : B2 ⟶ E2) (κσ : A ⟶ B2)
    (uc : B2 ⟶ E') (r : E' ⟶ E3) (Gm : E ⟶ E') (hu : u ≫ eps0 = ε ≫ uσ) (hκ : κ ≫ ε = κσ)
    (hbc : uσ ≫ bc0 = uc ≫ r) (hun : κσ ≫ uc = (κ ≫ u) ≫ Gm) :
    (κ ≫ u) ≫ eps0 ≫ bc0 = (κ ≫ u) ≫ Gm ≫ r := by
  rw [Category.assoc κ, reassoc_of% hu, ← Category.assoc κ, hκ, hbc, ← Category.assoc κσ, hun,
    Category.assoc]

private lemma comp_map_three' {C D : Type*} [Category C] [Category D] (G : Cᵒᵖ ⥤ D) {X : D}
    {A B C' E : C} (x : X ⟶ G.obj (op A)) (a : B ⟶ A) (b : C' ⟶ B) (c : E ⟶ C') :
    x ≫ G.map a.op ≫ G.map b.op ≫ G.map c.op = x ≫ G.map (c ≫ b ≫ a).op := by
  simp

/-- The sections of `f_*` of a map over `U` are its sections over the base change of `U`. -/
lemma etaleModuleDirectImage_map_hom_app {X X' : Scheme.{u}} (f : X' ⟶ X)
    {A B : EtaleModules.{u, r} Λ X'} (t : A ⟶ B) (U : X.Etale) :
    ((etaleModuleDirectImage.{u, r} Λ f).map t).hom.app (op U) =
      t.hom.app (op ((smallEtaleBaseChange f).obj U)) :=
  rfl

/-- **The restriction of `ε` followed by the base change map fixes the pulled back constant
section up to restriction.** -/
lemma exists_pulledBackConstantSection_comp_automorphismBaseChange :
    ∃ ρ₂ : (smallEtaleBaseChange (fieldBaseChangeMap σ kbar)).obj
        ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj (Scheme.Etale.mk (𝟙 Y.left))) ⟶
        (smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj (Scheme.Etale.mk (𝟙 Y.left)),
      pulledBackConstantSection Λ M (fieldBaseChangeProj Y kbar) ≫
          ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map
            (constantSelfMapTwist Λ M σ.left)).hom.app
            (op ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj
              (Scheme.Etale.mk (𝟙 Y.left)))) ≫
          ((automorphismBaseChange Λ Y σ kbar).app (etaleModuleConstantSheaf Λ M Y.left)).hom.app
            (op ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj
              (Scheme.Etale.mk (𝟙 Y.left)))) =
        pulledBackConstantSection Λ M (fieldBaseChangeProj Y kbar) ≫
          ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj
            (etaleModuleConstantSheaf Λ M Y.left)).obj.map ρ₂.op := by
  have hu : ((etaleModuleInverseImageAdj.{u, r} Λ (fieldBaseChangeProj Y kbar)).unit.app
        (etaleModuleConstantSheaf Λ M Y.left)).hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map
        (constantSelfMapTwist Λ M σ.left)).hom.app
        (op ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj
          (Scheme.Etale.mk (𝟙 Y.left)))) =
      (constantSelfMapTwist Λ M σ.left).hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
        ((etaleModuleInverseImageAdj.{u, r} Λ (fieldBaseChangeProj Y kbar)).unit.app
          ((etaleModuleDirectImage.{u, r} Λ σ.left).obj
            (etaleModuleConstantSheaf Λ M Y.left))).hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) :=
    (congrArg (fun z => z.hom.app (op (Scheme.Etale.mk (𝟙 Y.left))))
      ((etaleModuleInverseImageAdj.{u, r} Λ (fieldBaseChangeProj Y kbar)).unit.naturality
        (constantSelfMapTwist Λ M σ.left))).symm
  have hbc := congrArg (fun z => z.hom.app (op (Scheme.Etale.mk (𝟙 Y.left))))
    (unit_comp_map_etaleModuleBaseChange Λ σ.left (fieldBaseChangeMap σ kbar)
      (fieldBaseChangeProj Y kbar) (fieldBaseChangeProj Y kbar)
      (fieldBaseChangeMap_comp_fst σ kbar) (etaleModuleConstantSheaf Λ M Y.left))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    etaleModuleDirectImageComp_hom_app_hom_app, etaleModuleDirectImageComp_inv_app_hom_app] at hbc
  have hun := constantSheafSection_comp_unit Λ M (fieldBaseChangeProj Y kbar)
    ((isTerminalEtaleMkId Y.left).from ((smallEtaleBaseChange σ.left).obj
      (Scheme.Etale.mk (𝟙 Y.left))))
  have key := autChase _ _ _ _ _ _ _ _ _ _ hu
    (constantSheafSection_comp_constantSelfMapTwist Λ M σ.left) hbc hun
  have h3 := comp_map_three'
    ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj
      (etaleModuleConstantSheaf Λ M Y.left)).obj
    (pulledBackConstantSection Λ M (fieldBaseChangeProj Y kbar))
    ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).map ((isTerminalEtaleMkId Y.left).from
      ((smallEtaleBaseChange σ.left).obj (Scheme.Etale.mk (𝟙 Y.left)))))
    ((smallEtaleBaseChangeComp' (fieldBaseChangeProj Y kbar) σ.left
      (fieldBaseChangeMap σ kbar ≫ fieldBaseChangeProj Y kbar)
      (fieldBaseChangeMap_comp_fst σ kbar)).hom.app (Scheme.Etale.mk (𝟙 Y.left)))
    ((smallEtaleBaseChangeComp' (fieldBaseChangeMap σ kbar) (fieldBaseChangeProj Y kbar)
      (fieldBaseChangeMap σ kbar ≫ fieldBaseChangeProj Y kbar) rfl).inv.app
        (Scheme.Etale.mk (𝟙 Y.left)))
  rw [etaleModuleDirectImage_map_hom_app] at key
  exact ⟨_, key.trans h3⟩

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **A composite `G ⟶ b_* G ⟶ b_* a_* G ≅ (a ≫ b)_* G` fixing a section up to restriction**,
when both pieces do. -/
lemma comp_map_comp_hom_app_eq_map {X : Scheme.{u}} (a b ab : X ⟶ X) (hab : ab = a ≫ b)
    (G : EtaleModules.{u, r} Λ X) (f₁ : G ⟶ (etaleModuleDirectImage.{u, r} Λ b).obj G)
    (t : G ⟶ (etaleModuleDirectImage.{u, r} Λ a).obj G) {T : X.Etale}
    {A : ModuleCat.{max (u + 1) r} Λ}
    (x : A ⟶ G.obj.obj (op T)) (ρ : (smallEtaleBaseChange b).obj T ⟶ T)
    (ρ₂ : (smallEtaleBaseChange a).obj T ⟶ T)
    (hρ : x ≫ f₁.hom.app (op T) = x ≫ G.obj.map ρ.op)
    (h₂ : x ≫ t.hom.app (op T) = x ≫ G.obj.map ρ₂.op) :
    x ≫ (f₁ ≫ (etaleModuleDirectImage.{u, r} Λ b).map t ≫
        (etaleModuleDirectImageComp.{u, r} Λ a b ab hab).hom.app G).hom.app (op T) =
      x ≫ G.obj.map ((smallEtaleBaseChangeComp' a b ab hab).hom.app T ≫
        (smallEtaleBaseChange a).map ρ ≫ ρ₂).op := by
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    etaleModuleDirectImage_map_hom_app, etaleModuleDirectImageComp_hom_app_hom_app]
  calc x ≫ f₁.hom.app (op T) ≫ t.hom.app (op ((smallEtaleBaseChange b).obj T)) ≫
        G.obj.map (op ((smallEtaleBaseChangeComp' a b ab hab).hom.app T))
      = (x ≫ G.obj.map ρ.op ≫ t.hom.app (op ((smallEtaleBaseChange b).obj T))) ≫
        G.obj.map (op ((smallEtaleBaseChangeComp' a b ab hab).hom.app T)) := by
          rw [← Category.assoc x, hρ]
          exact (Category.assoc _ _ _).trans
            ((congrArg (x ≫ ·) (Category.assoc _ _ _)).symm.trans (Category.assoc _ _ _).symm)
    _ = ((x ≫ t.hom.app (op T)) ≫ G.obj.map ((smallEtaleBaseChange a).map ρ).op) ≫
        G.obj.map (op ((smallEtaleBaseChangeComp' a b ab hab).hom.app T)) := by
          rw [t.hom.naturality ρ.op]; simp only [Category.assoc]; rfl
    _ = x ≫ G.obj.map ((smallEtaleBaseChangeComp' a b ab hab).hom.app T ≫
        (smallEtaleBaseChange a).map ρ ≫ ρ₂).op := by
          rw [h₂]; simp only [Category.assoc, op_comp, Functor.map_comp]; rfl

/-- **The twisted Frobenius twist fixes the pulled back constant section up to restriction.** -/
lemma exists_pulledBackConstantSection_comp_twistedFrobeniusTwist :
    ∃ ρ₀ : (smallEtaleBaseChange (twistedGeometricFrobenius Y σ kbar p q hcard)).obj
        ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj (Scheme.Etale.mk (𝟙 Y.left))) ⟶
        (smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj (Scheme.Etale.mk (𝟙 Y.left)),
      pulledBackConstantSection Λ M (fieldBaseChangeProj Y kbar) ≫
          (twistedFrobeniusTwist.{u, r} Λ Y σ kbar p q hcard (etaleModuleConstantSheaf Λ M Y.left)
            (constantSelfMapTwist Λ M σ.left)).hom.app
            (op ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj
              (Scheme.Etale.mk (𝟙 Y.left)))) =
        pulledBackConstantSection Λ M (fieldBaseChangeProj Y kbar) ≫
          ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj
            (etaleModuleConstantSheaf Λ M Y.left)).obj.map ρ₀.op := by
  obtain ⟨ρ, hρ⟩ := exists_pulledBackConstantSection_comp_frobeniusBaseChangeTwist Λ M Y kbar p q
    hcard
  obtain ⟨ρ₂, h₂⟩ := exists_pulledBackConstantSection_comp_automorphismBaseChange Λ M Y σ kbar
  have h₂' : pulledBackConstantSection Λ M (fieldBaseChangeProj Y kbar) ≫
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).map
          (constantSelfMapTwist Λ M σ.left) ≫
        (automorphismBaseChange Λ Y σ kbar).app (etaleModuleConstantSheaf Λ M Y.left)).hom.app
        (op ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj
          (Scheme.Etale.mk (𝟙 Y.left)))) =
      pulledBackConstantSection Λ M (fieldBaseChangeProj Y kbar) ≫
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj
          (etaleModuleConstantSheaf Λ M Y.left)).obj.map ρ₂.op := by
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    exact h₂
  exact ⟨_, comp_map_comp_hom_app_eq_map Λ (fieldBaseChangeMap σ kbar)
    (geometricFrobeniusBaseChange Y kbar p q hcard) (twistedGeometricFrobenius Y σ kbar p q hcard)
    rfl _ _ _ _ ρ ρ₂ hρ h₂'⟩

/-- **The twisted Frobenius twist of a constant sheaf is the self-map twist.**  Transported to the
constant sheaf `M_{Y_k̄}`, the twist of `Stacks.EtaleCohomology.twistedFrobeniusTwist` attached to
the canonical map `M_Y ⟶ σ_* M_Y` agrees with the self-map twist of `φ = σ̄ ≫ π̄` over `Spec k̄` on
the constant sheaf `M_{k̄}`. -/
theorem transportedConstantTwist_twistedFrobeniusTwist :
    transportedConstantTwist.{u, r} Λ M (fieldBaseChangeProj Y kbar)
        (twistedGeometricFrobenius Y σ kbar p q hcard)
        (twistedFrobeniusTwist.{u, r} Λ Y σ kbar p q hcard (etaleModuleConstantSheaf Λ M Y.left)
          (constantSelfMapTwist Λ M σ.left)) =
      transportedConstantTwist.{u, r} Λ M (pullback.snd Y.hom (specAlgebraMap k kbar))
        (twistedGeometricFrobenius Y σ kbar p q hcard)
        ((selfMapTwist.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius Y σ kbar p q hcard)
          (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard)).app
            (etaleModuleConstantSheaf Λ M (Spec (.of kbar)))) := by
  obtain ⟨ρ₁, h₁⟩ := exists_pulledBackConstantSection_comp_twistedFrobeniusTwist Λ M Y σ kbar p q
    hcard
  obtain ⟨ρ₂, h₂⟩ := exists_pulledBackConstantSection_comp_selfMapTwist Λ M
    (pullback.snd Y.hom (specAlgebraMap k kbar)) (twistedGeometricFrobenius Y σ kbar p q hcard)
    (twistedGeometricFrobenius_comp_toBase Y σ kbar p q hcard)
  apply constantSheaf_hom_ext
  rw [constantSheafSection_comp_transportedConstantTwist Λ M _ _ _ ρ₁ h₁,
    constantSheafSection_comp_transportedConstantTwist Λ M _ _ _ ρ₂ h₂]

end TwistedFix

section BaseChangeFix

variable (Λ : Type r) [Ring Λ] (M : ModuleCat.{max (u + 1) r} Λ) {X X' : Scheme.{u}} (σ : X ⟶ X)
  (σ' : X' ⟶ X') (g : X' ⟶ X) (w : σ' ≫ g = g ≫ σ)

/-- **The restriction of the canonical map `M_X ⟶ σ_* M_X` followed by the base change map fixes
the pulled back constant section up to restriction**, for any square `σ' ≫ g = g ≫ σ`. -/
lemma exists_pulledBackConstantSection_comp_etaleModuleBaseChange :
    ∃ ρ₂ : (smallEtaleBaseChange (σ')).obj
        ((smallEtaleBaseChange (g)).obj (Scheme.Etale.mk (𝟙 X))) ⟶
        (smallEtaleBaseChange (g)).obj (Scheme.Etale.mk (𝟙 X)),
      pulledBackConstantSection Λ M (g) ≫
          ((etaleModuleInverseImage.{u, r} Λ (g)).map
            (constantSelfMapTwist Λ M σ)).hom.app
            (op ((smallEtaleBaseChange (g)).obj
              (Scheme.Etale.mk (𝟙 X)))) ≫
          ((etaleModuleBaseChange Λ σ σ' g g w).app (etaleModuleConstantSheaf Λ M X)).hom.app
            (op ((smallEtaleBaseChange (g)).obj
              (Scheme.Etale.mk (𝟙 X)))) =
        pulledBackConstantSection Λ M (g) ≫
          ((etaleModuleInverseImage.{u, r} Λ (g)).obj
            (etaleModuleConstantSheaf Λ M X)).obj.map ρ₂.op := by
  have hu : ((etaleModuleInverseImageAdj.{u, r} Λ (g)).unit.app
        (etaleModuleConstantSheaf Λ M X)).hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫
      ((etaleModuleInverseImage.{u, r} Λ (g)).map
        (constantSelfMapTwist Λ M σ)).hom.app
        (op ((smallEtaleBaseChange (g)).obj (Scheme.Etale.mk (𝟙 X)))) =
      (constantSelfMapTwist Λ M σ).hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫
        ((etaleModuleInverseImageAdj.{u, r} Λ (g)).unit.app
          ((etaleModuleDirectImage.{u, r} Λ σ).obj
            (etaleModuleConstantSheaf Λ M X))).hom.app (op (Scheme.Etale.mk (𝟙 X))) :=
    (congrArg (fun z => z.hom.app (op (Scheme.Etale.mk (𝟙 X))))
      ((etaleModuleInverseImageAdj.{u, r} Λ (g)).unit.naturality
        (constantSelfMapTwist Λ M σ))).symm
  have hbc := congrArg (fun z => z.hom.app (op (Scheme.Etale.mk (𝟙 X))))
    (unit_comp_map_etaleModuleBaseChange Λ σ σ' g g w (etaleModuleConstantSheaf Λ M X))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    etaleModuleDirectImageComp_hom_app_hom_app, etaleModuleDirectImageComp_inv_app_hom_app] at hbc
  have hun := constantSheafSection_comp_unit Λ M g
    ((isTerminalEtaleMkId X).from ((smallEtaleBaseChange σ).obj (Scheme.Etale.mk (𝟙 X))))
  have key := autChase _ _ _ _ _ _ _ _ _ _ hu
    (constantSheafSection_comp_constantSelfMapTwist Λ M σ) hbc hun
  have h3 := comp_map_three'
    ((etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X)).obj
    (pulledBackConstantSection Λ M g)
    ((smallEtaleBaseChange g).map ((isTerminalEtaleMkId X).from
      ((smallEtaleBaseChange σ).obj (Scheme.Etale.mk (𝟙 X)))))
    ((smallEtaleBaseChangeComp' g σ (σ' ≫ g) w).hom.app (Scheme.Etale.mk (𝟙 X)))
    ((smallEtaleBaseChangeComp' σ' g (σ' ≫ g) rfl).inv.app (Scheme.Etale.mk (𝟙 X)))
  rw [etaleModuleDirectImage_map_hom_app] at key
  exact ⟨_, key.trans h3⟩

end BaseChangeFix

end Stacks.EtaleCohomology

end
