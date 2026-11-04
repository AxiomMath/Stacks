module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleConstantPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity

/-!
# The étale cohomology of the levels and of the limit: the colimit of `Sheaf.H`

At the canonical site system of Stacks 0EYL with a cocone `d` on the system of schemes, the étale
cohomology groups `H^n(X_j, π_j⁻¹ 𝓜) = Sheaf.H (π_j⁻¹ 𝓜) n` of the levels, with the restriction
maps `Stacks.EtaleCohomology.ColimitBaseChange.sheafHRestriction` along the transitions, and the
restriction maps to `H^n(X, p⁻¹ 𝓜)`, form a colimit cocone as soon as one level is
quasi-compact and quasi-separated
(`Stacks.EtaleCohomology.AffineLimitCohomology.nonempty_isColimit_levelHCocone`).
The groups are compared with `Ext^n(π_j⁻¹ ℤ, π_j⁻¹ 𝓜)` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelExtColimit` through the canonical
isomorphisms `π_j⁻¹ ℤ ≅ ℤ` (`constPullbackIso`), which form a cocycle (`constPullbackIso_comp`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.EtaleCohomology.ColimitBaseChange

universe u

open Stacks.Homology

/-- Sheafification of abelian groups at the object universe of the small étale site. -/
local instance hasSheafify_smallEtale_objectUniverse' (Y : Scheme.{u}) :
    HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Scheme.hasSheafify_smallEtaleTopology.{u, u + 1} Y

/-- **Restriction of étale cohomology along `f : X ⟶ Y`**, read through a comparison
`e : f⁻¹ G ⟶ H`: `Ext` along the inverse image, followed by `f⁻¹ ℤ ≅ ℤ` and `e`. -/
def sheafHRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) {G : Sheaf Y.smallEtaleTopology Ab.{u + 1}}
    {H : Sheaf X.smallEtaleTopology Ab.{u + 1}} (e : (smallEtalePullbackAb f).obj G ⟶ H) (n : ℕ) :
    Sheaf.H.{u + 1, u + 1} G n →+ Sheaf.H.{u + 1, u + 1} H n :=
  (extConjHom (constPullbackIso f).inv e n).comp ((smallEtalePullbackAb f).mapExtAddHom _ _ n)

/-- `sheafHRestriction f e n x` is the conjugate by `f⁻¹ ℤ ≅ ℤ` and `e` of the image of `x` under
the inverse image along `f`. -/
theorem sheafHRestriction_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology Ab.{u + 1}} {H : Sheaf X.smallEtaleTopology Ab.{u + 1}}
    (e : (smallEtalePullbackAb f).obj G ⟶ H) (n : ℕ) (x : Sheaf.H.{u + 1, u + 1} G n) :
    sheafHRestriction f e n x =
      extConj (constPullbackIso f).inv e (x.mapExactFunctor (smallEtalePullbackAb f)) := rfl

/-- `Ext` out of `q⁻¹ ℤ` is étale cohomology, through `q⁻¹ ℤ ≅ ℤ`. -/
def extPullbackConstIso {X S : Scheme.{u}} (q : X ⟶ S) (G : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (n : ℕ) :
    Abelian.Ext.{u + 1} ((smallEtalePullbackAb q).obj (constZ S)) G n ≃+
      Sheaf.H.{u + 1, u + 1} G n where
  toFun := extConj (constPullbackIso q).inv (𝟙 G)
  invFun := extConj (constPullbackIso q).hom (𝟙 G)
  left_inv x := by simp [extConj_extConj, extConj_id]
  right_inv x := by simp [extConj_extConj, extConj_id]
  map_add' := extConj_add _ _

/-- `extPullbackConstIso q G n x` is the conjugate of `x` by the inverse of `q⁻¹ ℤ ≅ ℤ`. -/
theorem extPullbackConstIso_apply {X S : Scheme.{u}} (q : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology Ab.{u + 1}) (n : ℕ) (x) :
    extPullbackConstIso q G n x = extConj (constPullbackIso q).inv (𝟙 G) x := rfl

/-- The cocycle condition for `constPullbackIso`, in terms of inverses. -/
private theorem constPullbackIso_inv_comp_compIso_inv {W X S : Scheme.{u}} (g : W ⟶ X) (q : X ⟶ S)
    (q' : W ⟶ S) (hq : q' = g ≫ q) :
    (constPullbackIso q').inv ≫ (smallEtalePullbackAbCompIso' g q q' hq).inv.app _ =
      (constPullbackIso g).inv ≫ (smallEtalePullbackAb g).map (constPullbackIso q).inv := by
  have hi : (smallEtalePullbackAb g).mapIso (constPullbackIso q) ≪≫ constPullbackIso g =
      (smallEtalePullbackAbCompIso' g q q' hq).app (constZ S) ≪≫ constPullbackIso q' :=
    Iso.ext (constPullbackIso_comp g q q' hq)
  exact (congrArg Iso.inv hi).symm

/-- **The comparison is natural**: restriction of `Ext` out of the inverse images of `ℤ`, through
the composition comparisons, is restriction of étale cohomology. -/
theorem extPullbackConstIso_naturality {W X S : Scheme.{u}} (g : W ⟶ X) (q : X ⟶ S) (q' : W ⟶ S)
    (hq : q' = g ≫ q) {G : Sheaf X.smallEtaleTopology Ab.{u + 1}}
    {H : Sheaf W.smallEtaleTopology Ab.{u + 1}} (e : (smallEtalePullbackAb g).obj G ⟶ H) (n : ℕ)
    (x : Abelian.Ext.{u + 1} ((smallEtalePullbackAb q).obj (constZ S)) G n) :
    extPullbackConstIso q' H n (extConj ((smallEtalePullbackAbCompIso' g q q' hq).inv.app _) e
        (x.mapExactFunctor (smallEtalePullbackAb g))) =
      sheafHRestriction g e n (extPullbackConstIso q G n x) := by
  rw [extPullbackConstIso_apply, extPullbackConstIso_apply, sheafHRestriction_apply,
    extConj_extConj, extConj_mapExactFunctor, extConj_extConj,
    constPullbackIso_inv_comp_compIso_inv g q q' hq, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

/-- **Restrictions of étale cohomology compose.** -/
theorem sheafHRestriction_comp {X₀ X₁ X₂ : Scheme.{u}} (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁) (h : X₂ ⟶ X₀)
    (hh : h = g ≫ f) {G₀ : Sheaf X₀.smallEtaleTopology Ab.{u + 1}}
    {G₁ : Sheaf X₁.smallEtaleTopology Ab.{u + 1}} {G₂ : Sheaf X₂.smallEtaleTopology Ab.{u + 1}}
    (e_f : (smallEtalePullbackAb f).obj G₀ ⟶ G₁) (e_g : (smallEtalePullbackAb g).obj G₁ ⟶ G₂)
    (e_h : (smallEtalePullbackAb h).obj G₀ ⟶ G₂)
    (he : e_h = (smallEtalePullbackAbCompIso' g f h hh).inv.app G₀ ≫
      (smallEtalePullbackAb g).map e_f ≫ e_g) (n : ℕ) (x : Sheaf.H.{u + 1, u + 1} G₀ n) :
    sheafHRestriction g e_g n (sheafHRestriction f e_f n x) = sheafHRestriction h e_h n x := by
  rw [sheafHRestriction_apply, sheafHRestriction_apply, sheafHRestriction_apply,
    extConj_mapExactFunctor, extConj_extConj,
    ← ext_mapExactFunctor_comp_functor (smallEtalePullbackAb f) (smallEtalePullbackAb g),
    ext_mapExactFunctor_of_iso' (smallEtalePullbackAb f ⋙ smallEtalePullbackAb g)
      (smallEtalePullbackAb h) (smallEtalePullbackAbCompIso' g f h hh), extConj_extConj]
  rw [constPullbackIso_inv_comp_compIso_inv g f h hh, he]
  simp

/-- **Restriction along a morphism equal to the identity is bijective**, for an invertible
comparison. -/
theorem bijective_sheafHRestriction_of_eq_id {X : Scheme.{u}} (f : X ⟶ X) (hf : f = 𝟙 X)
    {G H : Sheaf X.smallEtaleTopology Ab.{u + 1}} (e : (smallEtalePullbackAb f).obj G ⟶ H)
    [IsIso e] (n : ℕ) : Function.Bijective (sheafHRestriction f e n) := by
  let α := smallEtalePullbackAbIdOf f hf
  have key : ∀ x : Sheaf.H.{u + 1, u + 1} G n, sheafHRestriction f e n x =
      extConj ((constPullbackIso f).inv ≫ α.hom.app _) (α.inv.app G ≫ e) x := by
    intro x
    rw [sheafHRestriction_apply, ext_mapExactFunctor_of_iso' (𝟭 _) (smallEtalePullbackAb f) α.symm,
      ext_mapExactFunctor_id, extConj_extConj]
    rfl
  have hb : Function.Bijective (fun x : Sheaf.H.{u + 1, u + 1} G n =>
      extConj ((constPullbackIso f).inv ≫ α.hom.app _) (α.inv.app G ≫ e) x) := by
    refine ⟨fun y y' hy => ?_, fun z => ⟨extConj (inv ((constPullbackIso f).inv ≫ α.hom.app _))
      (inv (α.inv.app G ≫ e)) z, ?_⟩⟩
    · have := congrArg (extConj (inv ((constPullbackIso f).inv ≫ α.hom.app _))
        (inv (α.inv.app G ≫ e))) hy
      simpa [extConj_extConj, extConj_id] using this
    · simp [extConj_extConj, extConj_id]
  exact (funext key ▸ hb : _)

end Stacks.EtaleCohomology.ColimitBaseChange

end
