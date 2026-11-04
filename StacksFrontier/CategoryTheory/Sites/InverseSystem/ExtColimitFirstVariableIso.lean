module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ExtColimitPullbackFirstVariable

/-!
# A first variable is determined by its value at the identity arrow

Let `𝒜` and `𝒜'` be first variables (`Stacks.WeakSites.ExtColimit.FirstVariable`) at an index `i`
of an inverse system of sites with finite coverings. Every transition and every leg of a first
variable is an isomorphism, so `𝒜` is determined, up to isomorphism, by its value `𝒜_⊤` at the
terminal object `⊤ = 𝟙 i` of `Over i`: `𝒜_A ≅ (A.hom)⁻¹ 𝒜_⊤` through the transition along the
unique arrow `A ⟶ ⊤`. An isomorphism `𝒜'_⊤ ≅ 𝒜_⊤` therefore extends to mutually inverse
morphisms of first variables (`Stacks.WeakSites.ExtColimit.FirstVariable.homOfTop`), and the
`Ext` colimit property passes from `𝒜` to `𝒜'`
(`Stacks.WeakSites.ExtColimit.FirstVariable.nonempty_isColimit_of_topIso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.Sites.InverseSystem

universe v u w

namespace Stacks.WeakSites.ExtColimit

open InverseSystemOfFiniteSites Stacks.Homology Stacks.WeakSites.ColimitSiteCohomology

variable {D : InverseSystemOfFiniteSites.{v, u, max u v w}}
  {C : Type (max u v w)} [SmallCategory C]
  {uC : ∀ i, D.C i ⥤ C} {hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j}
  {K : Precoverage C} [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]

namespace FirstVariable

variable {i : D.I} (𝒜 𝒜' : FirstVariable.{v, u, w} D uC hu K i)

/-- The terminal object `𝟙 i` of `Over i`. -/
abbrev topObj (i : D.I) : Over i := Over.mk (𝟙 i)

/-- The arrow `A ⟶ ⊤` of `Over i`. -/
abbrev toTop (A : Over i) : A ⟶ topObj i := Over.homMk A.hom

/-- Every arrow `A ⟶ ⊤` of `Over i` equals `toTop A`. -/
theorem eq_toTop {A : Over i} (g : A ⟶ topObj i) : g = toTop A :=
  Over.OverMorphism.ext (by simpa using Over.w g)

/-- For `f : A ⟶ B` in `Over i`, the composite `f ≫ toTop B` is `toTop A`. -/
theorem comp_toTop {A B : Over i} (f : A ⟶ B) : f ≫ toTop B = toTop A := eq_toTop _

variable {𝒜 𝒜'} (e : 𝒜'.obj (topObj i) ≅ 𝒜.obj (topObj i))

/-- The comparison at an arrow `A`, read along an arrow `g : A ⟶ ⊤`. -/
def appAlong {A : Over i} (g : A ⟶ topObj i) : 𝒜'.obj A ⟶ 𝒜.obj A :=
  inv (𝒜'.ψ g) ≫ (pb.{v, u, w} D g.left).map e.hom ≫ 𝒜.ψ g

/-- The comparison `appAlong e g` does not depend on the arrow `g : A ⟶ ⊤`. -/
theorem appAlong_eq {A : Over i} (g : A ⟶ topObj i) : appAlong e g = appAlong e (toTop A) := by
  obtain rfl := eq_toTop g
  rfl

/-- **The comparison commutes with the transitions**, in inverse-image form. -/
theorem ψ_comp_appAlong {A B : Over i} (f : A ⟶ B) :
    𝒜'.ψ f ≫ appAlong e (toTop A) =
      (pb.{v, u, w} D f.left).map (appAlong e (toTop B)) ≫ 𝒜.ψ f := by
  rw [← appAlong_eq e (f ≫ toTop B)]
  dsimp only [appAlong]
  simp only [← 𝒜.ψ_comp f (toTop B), ← 𝒜'.ψ_comp f (toTop B), IsIso.inv_comp, Category.assoc,
    IsIso.hom_inv_id_assoc, Functor.map_comp, Functor.map_inv, NatIso.inv_inv_app]
  have h := NatIso.naturality_2 (abelianSheafPullbackCompIso.{v, u, max u v w, max u v w} D f.left
    (toTop B).left) e.hom
  dsimp only [Functor.comp_map] at h
  dsimp only [Over.comp_left]
  rw [reassoc_of% h]

/-- The leg of `𝒜` at `A` is the leg at `⊤` followed by the transition of `𝒜` along `toTop A`. -/
theorem leg_eq_leg_top (𝒜 : FirstVariable.{v, u, w} D uC hu K i) (A : Over i) :
    𝒜.leg A = 𝒜.leg (topObj i) ≫
      (colimitPullbackCompIso.{v, u, w} D uC hu K (toTop A).left).inv.app (𝒜.obj (topObj i)) ≫
        (colimitPullback.{v, u, w} D uC K A.left).map (𝒜.ψ (toTop A)) := by
  rw [← reassoc_of% (𝒜.leg_map (toTop A)), map, ← Functor.map_comp, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The comparison on the colimit site. -/
def topAlong : 𝒜'.top ⟶ 𝒜.top :=
  inv (𝒜'.legInv (topObj i)) ≫ (colimitPullback.{v, u, w} D uC K i).map e.hom ≫
    𝒜.legInv (topObj i)

/-- **An isomorphism at the identity arrow extends to a morphism of first variables.** -/
def homOfTop : FirstVariable.Hom 𝒜' 𝒜 where
  app A := appAlong e (toTop A)
  top := topAlong e
  comm f := by
    change _ ≫ inv _ = inv _ ≫ _
    exact comp_inv_eq_inv_comp_of _ _ _ _ (ψ_comp_appAlong e f)
  top_comm A := by
    rw [leg_eq_leg_top 𝒜 A, leg_eq_leg_top 𝒜' A]
    dsimp only [topAlong, appAlong, leg]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, Functor.map_comp, Functor.map_inv]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact ((colimitPullbackCompIso.{v, u, w} D uC hu K (toTop A).left).inv.naturality e.hom)

/-- The component of `homOfTop e` at `A` is `appAlong e (toTop A)`. -/
theorem homOfTop_app (A : Over i) : (homOfTop e).app A = appAlong e (toTop A) := rfl

/-- The component of `homOfTop e` on the colimit site is `topAlong e`. -/
theorem homOfTop_top : (homOfTop e).top = topAlong e := rfl

/-- The comparisons along `e` and `e.symm` at `A` compose to the identity. -/
theorem appAlong_comp_appAlong_symm (A : Over i) :
    appAlong e (toTop A) ≫ appAlong e.symm (toTop A) = 𝟙 _ := by
  simp [appAlong, ← Functor.map_comp_assoc]

/-- The comparisons along `e` and `e.symm` on the colimit site compose to the identity. -/
theorem topAlong_comp_topAlong_symm : topAlong e ≫ topAlong e.symm = 𝟙 _ := by
  simp [topAlong, ← Functor.map_comp_assoc]

end FirstVariable

section Transfer

variable [∀ j, PreservesFiniteLimits (colimitPullback.{v, u, w} D uC K j)]
  [∀ j, EnoughInjectives (Sheaf (D.J j) Ab.{max u v w})]
  [∀ j, HasExt.{max u v w} (Sheaf (D.J j) Ab.{max u v w})]
  [HasExt.{max u v w} (Sheaf K.toGrothendieck Ab.{max u v w})]

variable {i : D.I} {𝒜 𝒜' : FirstVariable.{v, u, w} D uC hu K i}
  (F : AbelianSheafSystem.{v, u, max u v w, max u v w} D)
  {𝒢 : Sheaf K.toGrothendieck Ab.{max u v w}} (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
  (n : ℕ) (hι : IsCompatible.{v, u, max u v w, max u v w} D uC hu F 𝒢.obj ι)

/-- **First variables with isomorphic values at the identity arrow have the `Ext` colimit property
together.** -/
theorem FirstVariable.nonempty_isColimit_of_topIso
    (e : 𝒜'.obj (FirstVariable.topObj i) ≅ 𝒜.obj (FirstVariable.topObj i))
    (H : Nonempty (IsColimit (extCocone 𝒜 F ι n @hι))) :
    Nonempty (IsColimit (extCocone 𝒜' F ι n @hι)) :=
  FirstVariable.Hom.nonempty_isColimit_of_inverse F ι n hι (FirstVariable.homOfTop e.symm)
    (FirstVariable.homOfTop e)
    (fun A => by
      rw [FirstVariable.homOfTop_app, FirstVariable.homOfTop_app]
      simpa using FirstVariable.appAlong_comp_appAlong_symm e.symm A)
    (fun A => FirstVariable.appAlong_comp_appAlong_symm e A)
    (by
      rw [FirstVariable.homOfTop_top, FirstVariable.homOfTop_top]
      simpa using FirstVariable.topAlong_comp_topAlong_symm e.symm)
    (FirstVariable.topAlong_comp_topAlong_symm e) H

end Transfer

end Stacks.WeakSites.ExtColimit

end
