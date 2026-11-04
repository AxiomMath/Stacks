module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeTransitivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageFixedBaseColimit

/-!
# The cocycle condition and the cocone identity for higher direct images over a fixed base

Let `(X_i, f_{i'i})` be an inverse system of schemes over a directed set with structure morphisms
`g_i : X_i ⟶ S` to a fixed scheme `S`, compatible with the transitions, and let
`(ℱ_i, φ_{i'i})` be a system of abelian sheaves on it. The maps
`ψ_{i'i} : R^p g_{i, *} ℱ_i ⟶ R^p g_{i', *} ℱ_{i'}` and `ψ_i : R^p g_{i, *} ℱ_i ⟶ R^p g_* ℱ` of
[Stacks, Tag 09Z1] satisfy the cocycle condition `ψ_{i''i} = ψ_{i''i'} ∘ ψ_{i'i}` and the cocone
identity `ψ_{i'} ∘ ψ_{i'i} = ψ_i`; so they form a diagram of abelian sheaves on `S` and a cocone
over it.

## Main results

* `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.transitionMap_comp` — the cocycle
  condition.
* `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.projectionMap_cocone` — the cocone
  identity.

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.FixedBaseHigherDirectImage

variable (p : ℕ) {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {D : Iᵒᵖ ⥤ Scheme.{u}} {S : Scheme.{u}} (g : ∀ i : Iᵒᵖ, D.obj i ⟶ S)
  (hg : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), g i = D.map a ≫ g j)

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
/-- **The comparison of inverse images along a composite transition of the constant system** is
given by the identification `Stacks.EtaleCohomology.smallEtalePullbackAbIdOf` of the inverse
image along `𝟙_S` with the identity functor. -/
theorem systemPullbackComp_inv_app_const {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    (X : Sheaf (smallEtaleTopology S) Ab.{u + 1}) :
    (systemPullbackComp ((Functor.const Iᵒᵖ).obj S) Ab.{u + 1} a b).inv.app X =
      (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app ((smallEtalePullbackAb (𝟙 S)).obj X) := by
  rw [systemPullbackComp_eq]
  exact smallEtalePullbackAbComp'_id_left_inv_app _ rfl _ _ X

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
/-- The transition map of Stacks 09Z1 is that of Stacks 0EYM for the constant system of bases,
read through `Stacks.EtaleCohomology.smallEtalePullbackAbIdOf`. -/
theorem transitionMap_eq (F : EtaleSheafSystem D Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    transitionMap g p F a (hg a) = (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app (stage g p F j) ≫
      LimitHigherDirectImage.transitionMap (toConst g hg) p F a := rfl

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
/-- The inverse image along a transition of the constant system is the inverse image along
`𝟙_S`. -/
theorem systemPullback_const_map {i j : Iᵒᵖ} (a : i ⟶ j)
    {X Y : Sheaf (smallEtaleTopology S) Ab.{u + 1}} (φ : X ⟶ Y) :
    (systemPullback ((Functor.const Iᵒᵖ).obj S) Ab.{u + 1} a).map φ =
      (smallEtalePullbackAb (𝟙 S)).map φ := rfl

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
/-- The cocycle condition of Stacks 0EYM for the constant system of bases. -/
private theorem transitionMap_comp_aux (F : EtaleSheafSystem D Ab.{u + 1}) {i j k : Iᵒᵖ}
    (a : i ⟶ j) (b : j ⟶ k) :
    (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app
        ((smallEtalePullbackAb (𝟙 S)).obj (stage g p F k)) ≫
      (smallEtalePullbackAb (𝟙 S)).map (LimitHigherDirectImage.transitionMap (toConst g hg) p F b) ≫
        LimitHigherDirectImage.transitionMap (toConst g hg) p F a =
    LimitHigherDirectImage.transitionMap (toConst g hg) p F (a ≫ b) := by
  have h := LimitHigherDirectImage.transitionMap_comp (toConst g hg) p F a b
  rwa [systemPullbackComp_inv_app_const, systemPullback_const_map] at h

private theorem idOf_inv_algebra (X Y Z : Sheaf (smallEtaleTopology S) Ab.{u + 1})
    (φ : (smallEtalePullbackAb (𝟙 S)).obj X ⟶ Y) (ψ : (smallEtalePullbackAb (𝟙 S)).obj Y ⟶ Z) :
    (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app X ≫
        (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app ((smallEtalePullbackAb (𝟙 S)).obj X) ≫
          (smallEtalePullbackAb (𝟙 S)).map φ ≫ ψ =
      ((smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app X ≫ φ) ≫
        (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app Y ≫ ψ := by
  rw [Category.assoc, reassoc_of% ((smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.naturality φ)]

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
/-- **The cocycle condition for the transition maps of Stacks 09Z1.** For `i'' ≥ i' ≥ i` the map
`ψ_{i''i}` is the composite of `ψ_{i'i}` and `ψ_{i''i'}`. -/
theorem transitionMap_comp (F : EtaleSheafSystem D Ab.{u + 1}) {i j k : Iᵒᵖ} (a : i ⟶ j)
    (b : j ⟶ k) :
    transitionMap g p F (a ≫ b) (hg (a ≫ b)) =
      transitionMap g p F b (hg b) ≫ transitionMap g p F a (hg a) := by
  rw [transitionMap_eq, transitionMap_eq, transitionMap_eq, ← transitionMap_comp_aux]
  exact idOf_inv_algebra _ _ _ _ _

/-- **The cocone identity for the maps of Stacks 09Z1.** For `i' ≥ i` the map `ψ_i` is the
composite of `ψ_{i'i}` and `ψ_{i'}`, for a family `ι_i` compatible with the transition maps of the
system of sheaves. -/
theorem projectionMap_cocone (c : Cone D) (gX : c.pt ⟶ S) (w : ∀ i : Iᵒᵖ, gX = c.π.app i ≫ g i)
    (F : EtaleSheafSystem D Ab.{u + 1}) (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : LimitHigherDirectImage.IsPullbackCocone c F ι) {i j : Iᵒᵖ} (a : i ⟶ j) :
    transitionMap g p F a (hg a) ≫ projectionMap g p c gX 𝓕 F ι i (w i) =
      projectionMap g p c gX 𝓕 F ι j (w j) := by
  obtain rfl : limitMorphism g hg c = gX := (constConeIsLimit (I := I) S).hom_ext fun i =>
    (LimitHigherDirectImage.limitMorphism_comp_π _ c _ _ i).trans
      ((w i).symm.trans (Category.comp_id gX).symm)
  have hι' : (conePullbackComp c a).hom.app (F.obj j) ≫ ι j =
      (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i := by
    rw [← hι a, Iso.hom_inv_id_app_assoc]
  have h := LimitHigherDirectImage.projectionMap_cocone (toConst g hg) p c (constCone S)
    (constConeIsLimit S) 𝓕 F ι a hι'
  rw [conePullbackComp_inv_app_const, projectionMap_toConst, projectionMap_toConst] at h
  have key : ∀ (X Y Z : Sheaf (smallEtaleTopology S) Ab.{u + 1})
      (φ : (smallEtalePullbackAb (𝟙 S)).obj X ⟶ Y) (P : Y ⟶ Z),
      (smallEtalePullbackAb (𝟙 S)).map ((smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app X) ≫
          (smallEtalePullbackAb (𝟙 S)).map φ ≫
            (smallEtalePullbackAbIdOf (𝟙 S) rfl).hom.app Y ≫ P =
        (smallEtalePullbackAbIdOf (𝟙 S) rfl).hom.app X ≫
          ((smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app X ≫ φ) ≫ P := fun X Y Z φ P => by
    rw [← Functor.map_comp_assoc, reassoc_of% ((smallEtalePullbackAbIdOf (𝟙 S) rfl).hom.naturality
      ((smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app X ≫ φ))]
    simp only [Category.assoc]
  rw [← cancel_epi ((smallEtalePullbackAbIdOf (𝟙 S) rfl).hom.app (stage g p F j)), ← h]
  exact (key _ _ _ (LimitHigherDirectImage.transitionMap (toConst g hg) p F a) _).symm

end Stacks.EtaleCohomology.FixedBaseHigherDirectImage

end
