module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapTwistRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom

/-!
# The twisted Frobenius twist of a constant sheaf is the self-map twist

Let `Y` be a scheme over a finite field `k`, `σ : Y ⟶ Y` a morphism over `k`, `k̄` an algebraically
closed extension and `φ = σ̄ ≫ π̄` the twisted geometric Frobenius of `Y_k̄`. For a module `M` let
`M_Y` be the constant sheaf, with its canonical map `ε : M_Y ⟶ σ_* M_Y` (adjoint to
`σ^{-1} M_Y ≅ M_Y`). Under the identification `M_Y|_{Y_k̄} ≅ M_{Y_k̄} ≅ f^{-1} M_{k̄}`, where
`f : Y_k̄ ⟶ Spec k̄`, the twist `M_Y|_{Y_k̄} ⟶ φ_*(M_Y|_{Y_k̄})` of
`Stacks.EtaleCohomology.twistedFrobeniusTwist` (built from the Frobenius descent isomorphism of
[Stacks, Tag 03SR]) is the self-map twist `f^{-1} M ⟶ φ_* f^{-1} M` of
`Stacks.EtaleCohomology.selfMapTwist`.

## Main definitions

* `Stacks.EtaleCohomology.constantSheafSection`: the constant sections `M ⟶ M_X(U)`.
* `Stacks.EtaleCohomology.constantSelfMapTwist`: the canonical map `M_X ⟶ σ_* M_X`.

## Main results

* `Stacks.EtaleCohomology.constantSheafSection_comp_inverseImageConstantIso`: inverse image
  carries constant sections to constant sections.
* `Stacks.EtaleCohomology.constantSheafSection_comp_transportedConstantTwist`: a twist fixing the
  pulled back constant section up to restriction fixes the constant section once transported.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 8 and 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

/-! ### Constant sections -/

section Sections

variable (Λ : Type r) [Ring Λ] (M : ModuleCat.{max (u + 1) r} Λ)

/-- The constant sheaf `M_X` of a module on the small étale site of `X`. -/
abbrev etaleModuleConstantSheaf (X : Scheme.{u}) : EtaleModules.{u, r} Λ X :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M

/-- **The constant sections** `M ⟶ M_X(U)`. -/
abbrev constantSheafSection {X : Scheme.{u}} (U : X.Etale) :
    M ⟶ (etaleModuleConstantSheaf Λ M X).obj.obj (op U) :=
  (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app (op U)

/-- Constant sections restrict to constant sections. -/
@[reassoc]
lemma constantSheafSection_comp_map {X : Scheme.{u}} {U U' : X.Etale} (m : U' ⟶ U) :
    constantSheafSection Λ M U ≫ (etaleModuleConstantSheaf Λ M X).obj.map m.op =
      constantSheafSection Λ M U' := by
  have h := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).naturality m.op
  exact h.symm.trans (Category.id_comp _)

/-- **Inverse image carries constant sections to constant sections**: the constant section over
the final object, pulled back by the unit of `g^{-1} ⊣ g_*` and transported along
`g^{-1} M_X ≅ M_{X'}`, is the constant section over the base change of the final object. -/
lemma constantSheafSection_comp_inverseImageConstantIso {X X' : Scheme.{u}} (g : X' ⟶ X) :
    constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X)) ≫
        ((etaleModuleInverseImageAdj.{u, r} Λ g).unit.app (etaleModuleConstantSheaf Λ M X)).hom.app
          (op (Scheme.Etale.mk (𝟙 X))) ≫
        ((etaleModuleInverseImageConstantIso.{u, r} Λ g).hom.app M).hom.app
          (op ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X)))) =
      constantSheafSection Λ M ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X))) := by
  let : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let hGT := hT.isTerminalObj (smallEtaleBaseChange g)
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((constantSheafAdj _ _ hT).comp (etaleModuleInverseImageAdj.{u, r} Λ g))
    (constantSheafAdj _ (ModuleCat.{max (u + 1) r} Λ) hGT) M
  simp only [Adjunction.comp_unit_app, Stacks.ConstantSheaf.constantSheafAdj_unit_app] at h
  exact (Category.assoc _ _ _).symm.trans h

end Sections

/-! ### The canonical map `M_X ⟶ σ_* M_X` -/

section SelfMap

variable (Λ : Type r) [Ring Λ] (M : ModuleCat.{max (u + 1) r} Λ)

/-- **The canonical map `M_X ⟶ σ_* M_X`** of a constant sheaf, adjoint to `σ^{-1} M_X ≅ M_X`. -/
def constantSelfMapTwist {X : Scheme.{u}} (s : X ⟶ X) :
    etaleModuleConstantSheaf Λ M X ⟶
      (etaleModuleDirectImage.{u, r} Λ s).obj (etaleModuleConstantSheaf Λ M X) :=
  (etaleModuleInverseImageAdj.{u, r} Λ s).homEquiv _ _
    ((etaleModuleInverseImageConstantIso.{u, r} Λ s).hom.app M)

/-- The canonical map sends constant sections to constant sections. -/
lemma constantSheafSection_comp_constantSelfMapTwist {X : Scheme.{u}} (s : X ⟶ X) :
    constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X)) ≫
        (constantSelfMapTwist Λ M s).hom.app (op (Scheme.Etale.mk (𝟙 X))) =
      constantSheafSection Λ M ((smallEtaleBaseChange s).obj (Scheme.Etale.mk (𝟙 X))) := by
  rw [constantSelfMapTwist, Adjunction.homEquiv_unit]
  exact constantSheafSection_comp_inverseImageConstantIso Λ M s

/-- **Maps out of the inverse image of a constant sheaf are determined by the pulled back
constant sections.** -/
lemma hom_ext_inverseImage_constant {X X' : Scheme.{u}} (g : X' ⟶ X) {G : EtaleModules.{u, r} Λ X'}
    {α β : (etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X) ⟶ G}
    (h : constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X)) ≫
        ((etaleModuleInverseImageAdj.{u, r} Λ g).unit.app (etaleModuleConstantSheaf Λ M X)).hom.app
          (op (Scheme.Etale.mk (𝟙 X))) ≫
        α.hom.app (op ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X)))) =
      constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X)) ≫
        ((etaleModuleInverseImageAdj.{u, r} Λ g).unit.app (etaleModuleConstantSheaf Λ M X)).hom.app
          (op (Scheme.Etale.mk (𝟙 X))) ≫
        β.hom.app (op ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X))))) : α = β := by
  let adj := (constantSheafAdj X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
    (isTerminalEtaleMkId X)).comp (etaleModuleInverseImageAdj.{u, r} Λ g)
  apply (adj.homEquiv M G).injective
  simp only [adj, Adjunction.homEquiv_unit, Adjunction.comp_unit_app,
    Stacks.ConstantSheaf.constantSheafAdj_unit_app]
  exact h

end SelfMap

/-! ### The twisted Frobenius twist on constant sections -/

section Frobenius

variable (Λ : Type r) [Ring Λ] (M : ModuleCat.{max (u + 1) r} Λ) {k : Type u} [Field k]
  [Fintype k] (Y : Over (Spec (.of k))) (σ : Y ⟶ Y) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

private lemma comp_map_three {C D : Type*} [Category C] [Category D] (G : Cᵒᵖ ⥤ D) {X : D}
    {A B C' E : C} (x : X ⟶ G.obj (op A)) (a : B ⟶ A) (b : C' ⟶ B) (c : E ⟶ C') :
    (x ≫ G.map a.op) ≫ G.map b.op ≫ G.map c.op = x ≫ G.map (c ≫ b ≫ a).op := by
  simp

/-- The constant sections of `M_Y` over the final object, pulled back to `Y_k̄`. -/
abbrev pulledBackConstantSection {X X' : Scheme.{u}} (g : X' ⟶ X) :
    M ⟶ ((etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X)).obj.obj
      (op ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X)))) :=
  constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X)) ≫
    ((etaleModuleInverseImageAdj.{u, r} Λ g).unit.app (etaleModuleConstantSheaf Λ M X)).hom.app
      (op (Scheme.Etale.mk (𝟙 X)))

/-- Pulling back a constant section over any étale `X`-scheme is a restriction of the pulled back
constant section over the final object. -/
lemma constantSheafSection_comp_unit {X X' : Scheme.{u}} (g : X' ⟶ X) {V : X.Etale}
    (m : V ⟶ Scheme.Etale.mk (𝟙 X)) :
    constantSheafSection Λ M V ≫
        ((etaleModuleInverseImageAdj.{u, r} Λ g).unit.app (etaleModuleConstantSheaf Λ M X)).hom.app
          (op V) =
      pulledBackConstantSection Λ M g ≫
        ((etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X)).obj.map
          ((smallEtaleBaseChange g).map m).op := by
  have hn := ((etaleModuleInverseImageAdj.{u, r} Λ g).unit.app
    (etaleModuleConstantSheaf Λ M X)).hom.naturality m.op
  have hκ := constantSheafSection_comp_map Λ M m
  exact (congrArg (· ≫ _) hκ.symm).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) hn).trans (Category.assoc _ _ _).symm))

/-- **The Frobenius base change twist fixes the pulled back constant sections**, up to
restriction. -/
lemma exists_pulledBackConstantSection_comp_frobeniusBaseChangeTwist :
    ∃ ρ : (smallEtaleBaseChange (geometricFrobeniusBaseChange Y kbar p q hcard)).obj
        ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj (Scheme.Etale.mk (𝟙 Y.left))) ⟶
        (smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj (Scheme.Etale.mk (𝟙 Y.left)),
      pulledBackConstantSection Λ M (fieldBaseChangeProj Y kbar) ≫
          ((frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app
            (etaleModuleConstantSheaf Λ M Y.left)).hom.app
            (op ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj
              (Scheme.Etale.mk (𝟙 Y.left)))) =
        pulledBackConstantSection Λ M (fieldBaseChangeProj Y kbar) ≫
          ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj
            (etaleModuleConstantSheaf Λ M Y.left)).obj.map ρ.op := by
  have h1 := congrArg (fun z => z.hom.app (op (Scheme.Etale.mk (𝟙 Y.left))))
    (unit_comp_etaleModuleBaseChangeTwist Λ (fieldBaseChangeProj Y kbar)
      (geometricFrobeniusBaseChange Y kbar p q hcard) (geometricFrobenius Y p q hcard).left
      (geometricFrobeniusBaseChange_comp_fst Y kbar p q hcard)
      (geometricFrobeniusPushforwardIso Y p q hcard (ModuleCat.{max (u + 1) r} Λ)).hom
      (etaleModuleConstantSheaf Λ M Y.left))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    etaleModuleDirectImageComp_hom_app_hom_app, etaleModuleDirectImageComp_inv_app_hom_app,
    geometricFrobeniusPushforwardIso_hom_app_hom_app] at h1
  have key : pulledBackConstantSection Λ M (fieldBaseChangeProj Y kbar) ≫
      ((frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app
        (etaleModuleConstantSheaf Λ M Y.left)).hom.app
        (op ((smallEtaleBaseChange (fieldBaseChangeProj Y kbar)).obj
          (Scheme.Etale.mk (𝟙 Y.left)))) =
      constantSheafSection Λ M (Scheme.Etale.mk (𝟙 Y.left)) ≫
        (etaleModuleConstantSheaf Λ M Y.left).obj.map
          ((geometricFrobeniusEtaleSiteIso Y p q hcard).inv.app (Scheme.Etale.mk (𝟙 Y.left))).op ≫
        ((etaleModuleInverseImageAdj.{u, r} Λ (fieldBaseChangeProj Y kbar)).unit.app
          (etaleModuleConstantSheaf Λ M Y.left)).hom.app
          (op ((smallEtaleBaseChange (geometricFrobenius Y p q hcard).left).obj
            (Scheme.Etale.mk (𝟙 Y.left)))) ≫
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj
          (etaleModuleConstantSheaf Λ M Y.left)).obj.map
          (op ((smallEtaleBaseChangeComp' (fieldBaseChangeProj Y kbar)
            (geometricFrobenius Y p q hcard).left
            (geometricFrobeniusBaseChange Y kbar p q hcard ≫ fieldBaseChangeProj Y kbar)
            (geometricFrobeniusBaseChange_comp_fst Y kbar p q hcard)).hom.app
              (Scheme.Etale.mk (𝟙 Y.left)))) ≫
        ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj
          (etaleModuleConstantSheaf Λ M Y.left)).obj.map
          (op ((smallEtaleBaseChangeComp' (geometricFrobeniusBaseChange Y kbar p q hcard)
            (fieldBaseChangeProj Y kbar)
            (geometricFrobeniusBaseChange Y kbar p q hcard ≫ fieldBaseChangeProj Y kbar)
            rfl).inv.app (Scheme.Etale.mk (𝟙 Y.left)))) :=
    (Category.assoc _ _ _).trans (congrArg (fun z =>
      constantSheafSection Λ M (Scheme.Etale.mk (𝟙 Y.left)) ≫ z) h1)
  rw [← Category.assoc (constantSheafSection Λ M _), constantSheafSection_comp_map,
    reassoc_of% (constantSheafSection_comp_unit Λ M (fieldBaseChangeProj Y kbar)
      ((isTerminalEtaleMkId Y.left).from _))] at key
  exact ⟨_, key.trans (comp_map_three _ _ _ _ _)⟩

end Frobenius

/-! ### Twists of a pulled back constant sheaf -/

section Twists

variable (Λ : Type r) [Ring Λ] (M : ModuleCat.{max (u + 1) r} Λ) {X X' : Scheme.{u}}
  (g : X' ⟶ X)

/-- The identification `g^{-1} M_X ≅ M_{X'}`. -/
abbrev inverseImageEtaleModuleConstantSheafIso :
    (etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X) ≅
      etaleModuleConstantSheaf Λ M X' :=
  (etaleModuleInverseImageConstantIso.{u, r} Λ g).app M

/-- The identification sends restrictions of pulled back constant sections to constant sections. -/
lemma pulledBackConstantSection_comp_map_inverseImageConstantIso_hom {V : X'.Etale}
    (ρ : V ⟶ (smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X))) :
    pulledBackConstantSection Λ M g ≫
        ((etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X)).obj.map ρ.op ≫
        (inverseImageEtaleModuleConstantSheafIso.{u, r} Λ M g).hom.hom.app (op V) =
      constantSheafSection Λ M V := by
  have hn := (inverseImageEtaleModuleConstantSheafIso.{u, r} Λ M g).hom.hom.naturality ρ.op
  have hF := (Category.assoc _ _ _).trans (constantSheafSection_comp_inverseImageConstantIso Λ M g)
  exact (congrArg (pulledBackConstantSection Λ M g ≫ ·) hn).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hF).trans (constantSheafSection_comp_map Λ M ρ)))

/-- The inverse identification sends constant sections to restrictions of pulled back constant
sections. -/
lemma constantSheafSection_comp_inverseImageConstantIso_inv {V : X'.Etale}
    (ρ : V ⟶ (smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X))) :
    constantSheafSection Λ M V ≫
        (inverseImageEtaleModuleConstantSheafIso.{u, r} Λ M g).inv.hom.app (op V) =
      pulledBackConstantSection Λ M g ≫
        ((etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X)).obj.map
          ρ.op := by
  rw [← pulledBackConstantSection_comp_map_inverseImageConstantIso_hom Λ M g ρ]
  simp

variable (φ : X' ⟶ X')

/-- The transport of a twist of `g^{-1} M_X` to `M_{X'}`. -/
abbrev transportedConstantTwist
    (τ : (etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X) ⟶
      (etaleModuleDirectImage.{u, r} Λ φ).obj
        ((etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X))) :
    etaleModuleConstantSheaf Λ M X' ⟶
      (etaleModuleDirectImage.{u, r} Λ φ).obj (etaleModuleConstantSheaf Λ M X') :=
  (inverseImageEtaleModuleConstantSheafIso.{u, r} Λ M g).inv ≫ τ ≫
    (etaleModuleDirectImage.{u, r} Λ φ).map
      (inverseImageEtaleModuleConstantSheafIso.{u, r} Λ M g).hom

private lemma transportChase {D : Type*} [Category D] {A B C E F H K : D} (κ : A ⟶ B)
    (ei : B ⟶ C) (pb : A ⟶ E) (Gt : E ⟶ C) (τtop : C ⟶ F) (τT : E ⟶ H) (Gφt : H ⟶ F)
    (Gρ₀ : E ⟶ H) (eh : F ⟶ K) (κ' : A ⟶ K) (h1 : κ ≫ ei = pb ≫ Gt)
    (h2 : Gt ≫ τtop = τT ≫ Gφt) (h3 : pb ≫ τT = pb ≫ Gρ₀) (h4 : pb ≫ (Gρ₀ ≫ Gφt) ≫ eh = κ') :
    κ ≫ (ei ≫ τtop ≫ eh) = κ' := by
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc Gt, h2, ← Category.assoc,
    ← Category.assoc, h3]
  simpa only [Category.assoc] using h4

/-- **A twist fixing the pulled back constant section up to restriction becomes, transported to
`M_{X'}`, a twist fixing the constant section.** -/
lemma constantSheafSection_comp_transportedConstantTwist
    (τ : (etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X) ⟶
      (etaleModuleDirectImage.{u, r} Λ φ).obj
        ((etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X)))
    (ρ₀ : (smallEtaleBaseChange φ).obj ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X))) ⟶
      (smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X)))
    (hτ : pulledBackConstantSection Λ M g ≫
        τ.hom.app (op ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X)))) =
      pulledBackConstantSection Λ M g ≫
        ((etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X)).obj.map ρ₀.op) :
    constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X')) ≫
        (transportedConstantTwist.{u, r} Λ M g φ τ).hom.app (op (Scheme.Etale.mk (𝟙 X'))) =
      constantSheafSection Λ M ((smallEtaleBaseChange φ).obj (Scheme.Etale.mk (𝟙 X'))) := by
  let t : Scheme.Etale.mk (𝟙 X') ⟶ (smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X)) :=
    ((isTerminalEtaleMkId X).isTerminalObj (smallEtaleBaseChange g)).from _
  have h1 := constantSheafSection_comp_inverseImageConstantIso_inv Λ M g t
  have h2 := τ.hom.naturality t.op
  have h4 := pulledBackConstantSection_comp_map_inverseImageConstantIso_hom Λ M g
    ((smallEtaleBaseChange φ).map t ≫ ρ₀)
  rw [op_comp, Functor.map_comp] at h4
  exact transportChase _ _ _ _ _ _ _ _ _ _ h1 h2 hτ h4

/-- **Maps out of a constant sheaf are determined by the constant section.** -/
lemma constantSheaf_hom_ext {G : EtaleModules.{u, r} Λ X'}
    {α β : etaleModuleConstantSheaf Λ M X' ⟶ G}
    (h : constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X')) ≫
        α.hom.app (op (Scheme.Etale.mk (𝟙 X'))) =
      constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X')) ≫
        β.hom.app (op (Scheme.Etale.mk (𝟙 X')))) : α = β := by
  apply ((constantSheafAdj X'.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
    (isTerminalEtaleMkId X')).homEquiv M G).injective
  rw [Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply,
    Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply]
  exact h

end Twists

/-! ### The two twists fix constant sections -/

section Fix

variable (Λ : Type r) [Ring Λ] (M : ModuleCat.{max (u + 1) r} Λ)

/-- **The self-map twist fixes the pulled back constant section up to restriction.** -/
lemma exists_pulledBackConstantSection_comp_selfMapTwist {X X' : Scheme.{u}} (g : X' ⟶ X)
    (φ : X' ⟶ X') (w : φ ≫ g = g) :
    ∃ ρ₀ : (smallEtaleBaseChange φ).obj ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X))) ⟶
        (smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X)),
      pulledBackConstantSection Λ M g ≫
          ((selfMapTwist.{u, r} Λ g φ w).app (etaleModuleConstantSheaf Λ M X)).hom.app
            (op ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X)))) =
        pulledBackConstantSection Λ M g ≫
          ((etaleModuleInverseImage.{u, r} Λ g).obj (etaleModuleConstantSheaf Λ M X)).obj.map
            ρ₀.op := by
  have h := congrArg (fun z => z.hom.app (op (Scheme.Etale.mk (𝟙 X))))
    (unit_comp_map_selfMapTwist Λ g φ w (etaleModuleConstantSheaf Λ M X))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    etaleModuleDirectImageComp_inv_app_hom_app] at h
  exact ⟨_, (Category.assoc _ _ _).trans ((congrArg (constantSheafSection Λ M _ ≫ ·) h).trans
    (Category.assoc _ _ _).symm)⟩

end Fix

end Stacks.EtaleCohomology

end
