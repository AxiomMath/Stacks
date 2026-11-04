module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimitTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageFixedBase

/-!
# Higher direct images along a limit of schemes over a fixed base as a colimit

Let `I` be a directed set, let `(X_i, f_{i'i})` be an inverse system of schemes over a fixed
scheme `S` with affine transition morphisms and quasi-compact and quasi-separated structure
morphisms `g_i : X_i ⟶ S`, let `X = lim X_i` with projections `f_i : X ⟶ X_i` and structure
morphism `g : X ⟶ S`, and let `(ℱ_i, φ_{i'i})` be a system of abelian sheaves on `(X_i)` with
`ℱ = colim f_i⁻¹ℱ_i`. Then `R^p g_* ℱ = colim_i R^p g_{i, *} ℱ_i`, the maps being those of
`Stacks.EtaleCohomology.FixedBaseHigherDirectImage.transitionMap` and
`Stacks.EtaleCohomology.FixedBaseHigherDirectImage.projectionMap`.

This is the case of [Stacks, Tag 0EYM] in which the system of bases is the constant system at
`S`, with identity transition morphisms, and its limit the constant cone. The source also assumes
`g` quasi-compact and quasi-separated; that hypothesis is not needed.

## Main results

* `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.isSystemColimit`:
  `R^p g_* ℱ = colim_i R^p g_{i, *} ℱ_i`.
* `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.conePullbackComp_inv_app_const`: the
  comparison of inverse images along the factorisation `𝟙_S = 𝟙_S ≫ 𝟙_S` of the constant cone is
  induced by `Stacks.EtaleCohomology.smallEtalePullbackAbIdOf`.
* `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.projectionMap_toConst`: for the constant
  base, the cocone maps of [Stacks, Tag 0EYM] are those of [Stacks, Tag 09Z1], up to the same
  identification.

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

namespace FixedBaseHigherDirectImage

section Colimit

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  {S : Scheme.{u}} (g : ∀ i : Iᵒᵖ, D.obj i ⟶ S)
  (hg : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), g i = D.map a ≫ g j)

/-- The morphism from the inverse system to the constant system at `S` given by the `g_i`. -/
def toConst : D ⟶ (Functor.const Iᵒᵖ).obj S where
  app := g
  naturality _ _ a := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    exact (hg a).symm

/-- The constant cone at `S` over the constant system at `S`. -/
abbrev constCone (S : Scheme.{u}) : Cone ((Functor.const Iᵒᵖ).obj S) :=
  ⟨S, 𝟙 _⟩

/-- **The constant cone over a directed set is a limit cone**, `Iᵒᵖ` being connected. -/
def constConeIsLimit (S : Scheme.{u}) : IsLimit (constCone (I := I) S) where
  lift s := s.π.app (Opposite.op (Classical.arbitrary I))
  fac s j := by
    obtain ⟨k, hj, hi⟩ := directed_of (· ≤ ·) j.unop (Classical.arbitrary I)
    have h₁ := s.w (homOfLE hj).op
    have h₂ := s.w (homOfLE hi).op
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h₁ h₂
    simp only [Functor.const_obj_obj, NatTrans.id_app, Category.comp_id]
    exact h₂.symm.trans h₁
  uniq s m hm := by
    simpa using hm (Opposite.op (Classical.arbitrary I))

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
/-- **The comparison of inverse images along the factorisation `𝟙_S = 𝟙_S ≫ 𝟙_S` of the constant
cone** is induced by the identification `Stacks.EtaleCohomology.smallEtalePullbackAbIdOf` of the
inverse image along `𝟙_S` with the identity functor. -/
theorem conePullbackComp_inv_app_const {i j : Iᵒᵖ} (a : i ⟶ j)
    (X : Sheaf (smallEtaleTopology S) Ab.{u + 1}) :
    (conePullbackComp (constCone (I := I) S) a).inv.app X =
      (smallEtalePullbackAb (𝟙 S)).map ((smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app X) := by
  have h := Adjunction.leftAdjointCompIso_id_comp
    (systemAdjunction ((Functor.const Iᵒᵖ).obj S) Ab.{u + 1} a) (smallEtaleAdjunctionAb (𝟙 S))
    (coneDirectImageCompAb (constCone (I := I) S) a) (smallEtalePushforwardAbIdOf (𝟙 S) rfl)
    (Iso.ext (NatTrans.ext (funext fun F =>
      (smallEtalePushforwardAbComp'_id_right_hom_app (𝟙 S) (𝟙 S) rfl
        (Category.comp_id _).symm F).trans (Category.comp_id _).symm)))
  exact (congrArg (fun e => NatTrans.app (Iso.inv e) X) h).trans (Category.id_comp _)

/-- The limit morphism `S` receives from a cone over the inverse system, the constant cone at `S`
being the limit of the constant system. -/
abbrev limitMorphism (c : Cone D) : c.pt ⟶ S :=
  LimitHigherDirectImage.limitMorphism (toConst g hg) c (constCone S) (constConeIsLimit S)

/-- The limit morphism is the structure morphism `g = f_i ≫ g_i` of the cone at every index. -/
theorem limitMorphism_eq (c : Cone D) (i : Iᵒᵖ) : limitMorphism g hg c = c.π.app i ≫ g i :=
  (Category.comp_id _).symm.trans (LimitHigherDirectImage.limitMorphism_comp_π _ c _ _ i)

/-- **The cocone maps of Stacks 0EYM for the constant base are those of Stacks 09Z1**, up to the
identification `Stacks.EtaleCohomology.smallEtalePullbackAbIdOf` of the inverse image along `𝟙_S`
with the identity functor. -/
theorem projectionMap_toConst (p : ℕ) (c : Cone D) (F : EtaleSheafSystem D Ab.{u + 1})
    (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    LimitHigherDirectImage.projectionMap (toConst g hg) c (constCone S) (constConeIsLimit S) p 𝓕
        F ι i =
      (smallEtalePullbackAbIdOf (𝟙 S) rfl).hom.app (stage g p F i) ≫
        projectionMap g p c (limitMorphism g hg c) 𝓕 F ι i (limitMorphism_eq g hg c i) := by
  rw [projectionMap, Iso.hom_inv_id_app_assoc]
  rfl

variable [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] [∀ i, QuasiCompact (g i)]
  [∀ i, QuasiSeparated (g i)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- The higher direct images `R^p g_{i, *} ℱ_i`, with the maps `transitionMap` and
`projectionMap`, present `R^p g_* ℱ` as their colimit, for `g` the limit morphism
`limitMorphism g hg c`. -/
theorem isSystemColimit_limitMorphism (p : ℕ) (F : EtaleSheafSystem D Ab.{u + 1})
    (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (conePullbackComp c a).inv.app (F.obj j) ≫
        (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι) :
    IsSystemColimit (stage g p F) (fun {_i _j} a => transitionMap g p F a (hg a))
      (((smallEtalePushforwardAb (limitMorphism g hg c)).rightDerived p).obj 𝓕)
      (fun i => projectionMap g p c (limitMorphism g hg c) 𝓕 F ι i
        (limitMorphism_eq g hg c i)) := by
  have : ∀ i, QuasiCompact ((toConst g hg).app i) := fun i => inferInstanceAs (QuasiCompact (g i))
  have : ∀ i, QuasiSeparated ((toConst g hg).app i) := fun i =>
    inferInstanceAs (QuasiSeparated (g i))
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (((Functor.const Iᵒᵖ).obj S).map a) :=
    fun _ => inferInstanceAs (IsAffineHom (𝟙 S))
  refine (LimitHigherDirectImage.isHigherDirectImageColimit (toConst g hg) hc
    (constConeIsLimit S) p F 𝓕 ι hι hpres).isSystemColimit.of_isoSystem (A' := stage g p F)
    (fun i => (smallEtalePullbackAbIdOf (𝟙 S) rfl).app (stage g p F i)) (Iso.refl _)
    (fun {i j} a => ?_) (fun i => ?_)
  · have key : ∀ (X Y : Sheaf (smallEtaleTopology S) Ab.{u + 1})
        (φ : (smallEtalePullbackAb (𝟙 S)).obj X ⟶ Y),
        ((smallEtalePullbackAb (𝟙 S)).map ((smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app X) ≫
          (smallEtalePullbackAb (𝟙 S)).map φ) ≫ (smallEtalePullbackAbIdOf (𝟙 S) rfl).hom.app Y =
        (smallEtalePullbackAbIdOf (𝟙 S) rfl).hom.app X ≫
          ((smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app X ≫ φ) := fun X Y φ => by
      rw [← Functor.map_comp]
      exact (smallEtalePullbackAbIdOf (𝟙 S) rfl).hom.naturality _
    dsimp only [LimitHigherDirectImage.higherDirectImageDiagramMap, Iso.app_hom]
    rw [conePullbackComp_inv_app_const]
    exact key _ _ (LimitHigherDirectImage.transitionMap (toConst g hg) p F a)
  · rw [Iso.refl_hom, Category.comp_id, Iso.app_hom]
    exact projectionMap_toConst g hg p c F 𝓕 ι i

variable (gX : c.pt ⟶ S) (w : ∀ i : Iᵒᵖ, gX = c.π.app i ≫ g i)

include hg hc in
/-- Let `X = lim X_i` be the limit of a directed inverse system of schemes over `S` with affine
transition morphisms and quasi-compact and quasi-separated structure morphisms `g_i : X_i ⟶ S`,
let `g : X ⟶ S` be the structure morphism of the limit, and let `ι_i : f_i⁻¹ℱ_i ⟶ ℱ` present
`ℱ = colim f_i⁻¹ℱ_i` for a system `(ℱ_i, φ_{i'i})` of abelian sheaves. Then for every `p` the
maps `ψ_i : R^p g_{i, *}ℱ_i ⟶ R^p g_*ℱ` present `R^p g_*ℱ = colim_i R^p g_{i, *}ℱ_i`, the
transition maps being the `ψ_{i'i}`. -/
@[stacks 09Z1, sga "4 VII 5.11" "special case"]
theorem isSystemColimit (p : ℕ) (F : EtaleSheafSystem D Ab.{u + 1})
    (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (conePullbackComp c a).inv.app (F.obj j) ≫
        (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι) :
    IsSystemColimit (stage g p F) (fun {_i _j} a => transitionMap g p F a (hg a))
      (((smallEtalePushforwardAb gX).rightDerived p).obj 𝓕)
      (fun i => projectionMap g p c gX 𝓕 F ι i (w i)) := by
  obtain rfl : limitMorphism g hg c = gX := (constConeIsLimit (I := I) S).hom_ext fun i =>
    (LimitHigherDirectImage.limitMorphism_comp_π _ c _ _ i).trans
      ((w i).symm.trans (Category.comp_id gX).symm)
  exact isSystemColimit_limitMorphism g hg hc p F 𝓕 ι hι hpres

end Colimit

end FixedBaseHigherDirectImage

end Stacks.EtaleCohomology

end
