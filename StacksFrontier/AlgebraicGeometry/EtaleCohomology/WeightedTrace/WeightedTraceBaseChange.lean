module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CompGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceBaseChangeCore
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of the weighted trace: Stacks 0GKH, part (2)

Consider a cartesian square of a big étale site with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'`, with `f` locally quasi-finite,
let `w` be an integer-valued function on `X` and let `F` be an abelian sheaf on the small étale
site of `Y`. The function `w ∘ p` is a weighting of `f'` whenever `w` is a weighting of `f`, by
Stacks 0F3B, and part (2) of Stacks 0GKH asserts that the trace maps of Stacks 0GKG for `(f, w)`
and for `(f', w ∘ p)` agree under the two canonical comparisons attached to the square: the
base-change isomorphism `g^{-1}f_!G ≅ f'_!p^{-1}G` of Stacks 0F5J, and the comparison
`p^{-1}f^{-1}F ≅ f'^{-1}g^{-1}F` of the two iterated inverse images.

## Main definitions

* `AlgebraicGeometry.SmallEtale.inverseImageSquareIso` — the comparison
  `p^{-1}f^{-1}F ≅ f'^{-1}g^{-1}F`, as an isomorphism of functors, obtained by factoring both
  iterated inverse images through the inverse image along the diagonal `p ≫ f = f' ≫ g` of the
  square.

## Main results

* `AlgebraicGeometry.SmallEtale.inverseImageSquareIso_inv_germ` — the comparison of the two
  iterated inverse images, read on geometric stalks: it matches the identifications of Stacks 03Q1
  on both sides.
* `AlgebraicGeometry.SmallEtale.fiberPointPullbackStalkIso_square` — the resulting compatibility
  of the identifications of the stalk over a point of a geometric fibre with the stalk below.
* `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_baseChange` — **Stacks 0GKH, part (2).**
  The base change of a trace map for `(f, w)` is a trace map for `(f', w ∘ p)`.
* `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_baseChange_eq` — **Stacks 0GKH, part (2)**
  as an equation between the two trace maps.

## References

* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u

namespace AlgebraicGeometry.SmallEtale

section Transport

/-- The identification of the stalk of an inverse image with the stalk at the image point
commutes with moving the geometric point along an equality. -/
public theorem etaleStalkSmallEtalePullObjIso_hom_eqToHom_apply (B : BigEtaleSite.{u})
    {S T : B.Scheme} (q : T ⟶ S) {x x' : GeometricPoint T.obj} (h : x = x')
    (F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1})
    (z : ↑(etaleStalk B T.obj T.property x ((abPullback.{u, u + 1} B q).obj F).obj)) :
    (etaleStalkSmallEtalePullObjIso B q x' AddCommGrpCat.{u + 1} F).hom
        ((eqToHom (congrArg (fun k => etaleStalk B T.obj T.property k
          ((abPullback.{u, u + 1} B q).obj F).obj) h)) z) =
      (eqToHom (congrArg (fun k => etaleStalk B S.obj S.property
          (k.map (B.inclusion.map q)) F.obj) h))
        ((etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{u + 1} F).hom z) := by
  cases h
  simp

end Transport

/-- Two mutually inverse morphisms of sheaves induce mutually inverse maps on a geometric
stalk. -/
public theorem etaleStalk_map_comp_eq_id (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (x : GeometricPoint S)
    {M N : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}}
    (a : M ⟶ N) (b : N ⟶ M) (h : a ≫ b = 𝟙 M)
    (z : ↑(etaleStalk B S hS x M.obj)) :
    ((etaleStalkPresheafFunctor B S hS x AddCommGrpCat.{u + 1}).map b.hom)
      (((etaleStalkPresheafFunctor B S hS x AddCommGrpCat.{u + 1}).map a.hom) z) = z := by
  have hG := congrArg
    (sheafToPresheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1} ⋙
      etaleStalkPresheafFunctor B S hS x AddCommGrpCat.{u + 1}).map h
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hG
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom hG z).trans (ConcreteCategory.id_apply z))

/-- If an isomorphism of sheaves carries `z` to `z'` on a geometric stalk, its inverse carries
`z'` back to `z`. -/
private theorem etaleStalk_map_inv_eq_of_map_hom_eq (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (x : GeometricPoint S)
    {M N : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}} (e : M ≅ N)
    {z : ↑(etaleStalk B S hS x M.obj)} {z' : ↑(etaleStalk B S hS x N.obj)}
    (h : ((etaleStalkPresheafFunctor B S hS x AddCommGrpCat.{u + 1}).map e.hom.hom) z = z') :
    ((etaleStalkPresheafFunctor B S hS x AddCommGrpCat.{u + 1}).map e.inv.hom) z' = z :=
  h ▸ etaleStalk_map_comp_eq_id B S hS x e.hom e.inv e.hom_inv_id z

section Square

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)

/-- **The comparison of the two iterated inverse images of a cartesian square.** Both
`p^{-1}f^{-1}` and `f'^{-1}g^{-1}` are compared with the inverse image along the diagonal
`p ≫ f = f' ≫ g` of the square by the composition law of Stacks 021J; the comparison between them
is the composite of the first with the inverse of the second. -/
public def inverseImageSquareIso :
    abPullback.{u, u + 1} B f ⋙ abPullback.{u, u + 1} B p ≅
      abPullback.{u, u + 1} B g ⋙ abPullback.{u, u + 1} B f' :=
  smallEtaleSheafPullbackFactoredCompIso B X' X Y p f (p ≫ f) rfl AddCommGrpCat.{u + 1} ≪≫
    (smallEtaleSheafPullbackFactoredCompIso B X' Y' Y f' g (p ≫ f) sq.w.symm
      AddCommGrpCat.{u + 1}).symm

/-- **The comparison of the two iterated inverse images, on germs.** The comparison
`p^{-1}f^{-1}F ≅ f'^{-1}g^{-1}F` carries the germ of a section of `F`, transported through the
two identifications of Stacks 03Q1 along `f` and then `p`, to the same germ transported through
the identifications along `g` and then `f'`. -/
public theorem inverseImageSquareIso_germ (x : GeometricPoint X'.obj)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    (V : SmallEtale B Y.obj Y.property)
    (w₁ : (geometricPointFiber B Y.obj Y.property
      ((x.map (B.inclusion.map p)).map (B.inclusion.map f))).obj V)
    (w₂ : (geometricPointFiber B Y.obj Y.property
      (x.map (B.inclusion.map (p ≫ f)))).obj V)
    (w₃ : (geometricPointFiber B Y.obj Y.property
      ((x.map (B.inclusion.map f')).map (B.inclusion.map g))).obj V)
    (h₁₂ : w₁.1 = w₂.1) (h₃₂ : w₃.1 = w₂.1)
    (τ : F.obj.obj (op V)) :
    ((etaleStalkPresheafFunctor B X'.obj X'.property x AddCommGrpCat.{u + 1}).map
        ((inverseImageSquareIso.{u} B p f' f g sq).hom.app F).hom)
      ((etaleStalkSmallEtalePullObjIso B p x AddCommGrpCat.{u + 1}
          ((abPullback.{u, u + 1} B f).obj F)).inv
        ((etaleStalkSmallEtalePullObjIso B f (x.map (B.inclusion.map p))
            AddCommGrpCat.{u + 1} F).inv
          (etaleGerm B Y.obj Y.property
            ((x.map (B.inclusion.map p)).map (B.inclusion.map f)) F.obj V w₁ τ))) =
      (etaleStalkSmallEtalePullObjIso B f' x AddCommGrpCat.{u + 1}
          ((abPullback.{u, u + 1} B g).obj F)).inv
        ((etaleStalkSmallEtalePullObjIso B g (x.map (B.inclusion.map f'))
            AddCommGrpCat.{u + 1} F).inv
          (etaleGerm B Y.obj Y.property
            ((x.map (B.inclusion.map f')).map (B.inclusion.map g)) F.obj V w₃ τ)) := by
  have hA := etaleGerm_smallEtaleSheafPullbackFactoredCompIso.{u, u + 1}
    B p f (p ≫ f) rfl x F V w₁ w₂ h₁₂ τ
  have hB := etaleGerm_smallEtaleSheafPullbackFactoredCompIso.{u, u + 1}
    B f' g (p ≫ f) sq.w.symm x F V w₃ w₂ h₃₂ τ
  have hcomp : ((inverseImageSquareIso.{u} B p f' f g sq).hom.app F).hom =
      ((smallEtaleSheafPullbackFactoredCompIso B X' X Y p f (p ≫ f) rfl
        AddCommGrpCat.{u + 1}).hom.app F).hom ≫
      ((smallEtaleSheafPullbackFactoredCompIso B X' Y' Y f' g (p ≫ f) sq.w.symm
        AddCommGrpCat.{u + 1}).inv.app F).hom := rfl
  rw [hcomp, Functor.map_comp]
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  rw [hA]
  exact etaleStalk_map_inv_eq_of_map_hom_eq B X'.obj X'.property x
    ((smallEtaleSheafPullbackFactoredCompIso B X' Y' Y f' g (p ≫ f) sq.w.symm
      AddCommGrpCat.{u + 1}).app F) hB

/-- The identification of the stalk of an inverse image with the stalk at the image point, in its
inverse form, commutes with moving the geometric point along an equality. -/
public theorem etaleStalkSmallEtalePullObjIso_inv_eqToHom_apply (B : BigEtaleSite.{u})
    {S T : B.Scheme} (q : T ⟶ S) {x x' : GeometricPoint T.obj} (h : x = x')
    (F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1})
    (z : ↑(etaleStalk B S.obj S.property (x.map (B.inclusion.map q)) F.obj)) :
    (eqToHom (congrArg (fun k => etaleStalk B T.obj T.property k
          ((abPullback.{u, u + 1} B q).obj F).obj) h))
        ((etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{u + 1} F).inv z) =
      (etaleStalkSmallEtalePullObjIso B q x' AddCommGrpCat.{u + 1} F).inv
        ((eqToHom (congrArg (fun k => etaleStalk B S.obj S.property
          (k.map (B.inclusion.map q)) F.obj) h)) z) := by
  cases h
  simp

end Square

section SquareInverse

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)

/-- The inverse of the comparison of the two iterated inverse images, on germs. -/
public theorem inverseImageSquareIso_inv_germ (x : GeometricPoint X'.obj)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    (V : SmallEtale B Y.obj Y.property)
    (w₁ : (geometricPointFiber B Y.obj Y.property
      ((x.map (B.inclusion.map p)).map (B.inclusion.map f))).obj V)
    (w₂ : (geometricPointFiber B Y.obj Y.property
      (x.map (B.inclusion.map (p ≫ f)))).obj V)
    (w₃ : (geometricPointFiber B Y.obj Y.property
      ((x.map (B.inclusion.map f')).map (B.inclusion.map g))).obj V)
    (h₁₂ : w₁.1 = w₂.1) (h₃₂ : w₃.1 = w₂.1)
    (τ : F.obj.obj (op V)) :
    ((etaleStalkPresheafFunctor B X'.obj X'.property x AddCommGrpCat.{u + 1}).map
        ((inverseImageSquareIso.{u} B p f' f g sq).inv.app F).hom)
      ((etaleStalkSmallEtalePullObjIso B f' x AddCommGrpCat.{u + 1}
          ((abPullback.{u, u + 1} B g).obj F)).inv
        ((etaleStalkSmallEtalePullObjIso B g (x.map (B.inclusion.map f'))
            AddCommGrpCat.{u + 1} F).inv
          (etaleGerm B Y.obj Y.property
            ((x.map (B.inclusion.map f')).map (B.inclusion.map g)) F.obj V w₃ τ))) =
      (etaleStalkSmallEtalePullObjIso B p x AddCommGrpCat.{u + 1}
          ((abPullback.{u, u + 1} B f).obj F)).inv
        ((etaleStalkSmallEtalePullObjIso B f (x.map (B.inclusion.map p))
            AddCommGrpCat.{u + 1} F).inv
          (etaleGerm B Y.obj Y.property
            ((x.map (B.inclusion.map p)).map (B.inclusion.map f)) F.obj V w₁ τ)) := by
  exact etaleStalk_map_inv_eq_of_map_hom_eq B X'.obj X'.property x
    ((inverseImageSquareIso.{u} B p f' f g sq).app F)
    (inverseImageSquareIso_germ.{u} B p f' f g sq x F V w₁ w₂ w₃ h₁₂ h₃₂ τ)

end SquareInverse


section Crux

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) (s : GeometricPoint Y.obj)

/-- The identification of the stalk of `f^{-1}F` above a point of a geometric fibre with the
stalk of `F` below, on an element: it is the identification of Stacks 03Q1 followed by the
transport along the defining equality of the point of the fibre. -/
public theorem fiberPointPullbackStalkIso_hom_apply
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    (xx : GeometricFiberPoint B f s)
    (z : ↑(etaleStalk B X.obj X.property (xx.toGeometricPoint B f s)
      ((abPullback.{u, u + 1} B f).obj F).obj)) :
    (fiberPointPullbackStalkIso.{u, u + 1} B f s F xx).hom z =
      (eqToHom (congrArg (fun r => etaleStalk B Y.obj Y.property r F.obj)
          (toGeometricPoint_map B f s xx)))
        ((etaleStalkSmallEtalePullObjIso B f (xx.toGeometricPoint B f s)
          AddCommGrpCat.{u + 1} F).hom z) :=
  ConcreteCategory.comp_apply _ _ _

end Crux

section Compatibility

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)

/-- **The two identifications of the stalk over a point of a geometric fibre agree.** For a point
`x` of the geometric fibre of `f'` above a geometric point `t` of `Y'`, the identification of the
stalk of `f'^{-1}g^{-1}F` at `x` with the stalk of `g^{-1}F` at `t` agrees, through the comparison
of the two iterated inverse images and the identification of stalks over corresponding points of
the two geometric fibres, with the identification of the stalk of `f^{-1}F` at the image of `x`
with the stalk of `F` below.

This is the compatibility that turns the stalk computation of
`AlgebraicGeometry.SmallEtale.baseChangeTrace_fiberStalkOf` into part (2) of Stacks 0GKH. -/
public theorem fiberPointPullbackStalkIso_square (t : GeometricPoint Y'.obj)
    (x : GeometricFiberPoint B f' t)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    (z : ↑(etaleStalk B X'.obj X'.property (x.toGeometricPoint B f' t)
      ((abPullback.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B g).obj F)).obj)) :
    (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1} F).inv
        ((fiberPointPullbackStalkIso.{u, u + 1} B f (t.map (B.inclusion.map g)) F
            (fiberPointBaseChange B p f' f g sq t x)).hom
          ((fiberStalkBaseChangeIso.{u, u + 1} B p f' f g sq t
              ((abPullback.{u, u + 1} B f).obj F) x).inv
            (((etaleStalkPresheafFunctor B X'.obj X'.property (x.toGeometricPoint B f' t)
                AddCommGrpCat.{u + 1}).map
              ((inverseImageSquareIso.{u} B p f' f g sq).inv.app F).hom) z))) =
      (fiberPointPullbackStalkIso.{u, u + 1} B f' t
        ((abPullback.{u, u + 1} B g).obj F) x).hom z := by
  have hsqm : B.inclusion.map p ≫ B.inclusion.map f =
      B.inclusion.map f' ≫ B.inclusion.map g := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, sq.w]
  obtain ⟨V, ℓ, τ, hγ⟩ := exists_etaleGerm_eq B Y.obj Y.property
    (((x.toGeometricPoint B f' t).map (B.inclusion.map f')).map (B.inclusion.map g)) F.obj
    ((etaleStalkSmallEtalePullObjIso B g
        ((x.toGeometricPoint B f' t).map (B.inclusion.map f')) AddCommGrpCat.{u + 1} F).hom
      ((etaleStalkSmallEtalePullObjIso B f' (x.toGeometricPoint B f' t)
        AddCommGrpCat.{u + 1} ((abPullback.{u, u + 1} B g).obj F)).hom z))
  -- the same underlying morphism, read as a lift of the three other presentations of the point
  have pw₁ : ℓ.1 ≫ B.inclusion.map V.obj.hom =
      (((x.toGeometricPoint B f' t).map (B.inclusion.map p)).map (B.inclusion.map f)).hom :=
    ℓ.2.trans (by
      show (x.1 ≫ B.inclusion.map f') ≫ B.inclusion.map g =
        (x.1 ≫ B.inclusion.map p) ≫ B.inclusion.map f
      rw [Category.assoc, Category.assoc, hsqm])
  have pw₂ : ℓ.1 ≫ B.inclusion.map V.obj.hom =
      ((x.toGeometricPoint B f' t).map (B.inclusion.map (p ≫ f))).hom :=
    ℓ.2.trans (by
      show (x.1 ≫ B.inclusion.map f') ≫ B.inclusion.map g =
        x.1 ≫ B.inclusion.map (p ≫ f)
      rw [CategoryTheory.Functor.map_comp, Category.assoc, hsqm])
  have pℓt : ℓ.1 ≫ B.inclusion.map V.obj.hom = (t.map (B.inclusion.map g)).hom :=
    ℓ.2.trans (by
      show (x.1 ≫ B.inclusion.map f') ≫ B.inclusion.map g = t.hom ≫ B.inclusion.map g
      rw [x.2])
  have hz : (etaleStalkSmallEtalePullObjIso B f' (x.toGeometricPoint B f' t)
        AddCommGrpCat.{u + 1} ((abPullback.{u, u + 1} B g).obj F)).inv
      ((etaleStalkSmallEtalePullObjIso B g
          ((x.toGeometricPoint B f' t).map (B.inclusion.map f'))
          AddCommGrpCat.{u + 1} F).inv
        (etaleGerm B Y.obj Y.property
          (((x.toGeometricPoint B f' t).map (B.inclusion.map f')).map (B.inclusion.map g))
          F.obj V ℓ τ)) = z :=
    (congrArg (fun m => (etaleStalkSmallEtalePullObjIso B f' (x.toGeometricPoint B f' t)
          AddCommGrpCat.{u + 1} ((abPullback.{u, u + 1} B g).obj F)).inv
        ((etaleStalkSmallEtalePullObjIso B g
          ((x.toGeometricPoint B f' t).map (B.inclusion.map f'))
          AddCommGrpCat.{u + 1} F).inv m)) hγ).trans
      ((congrArg (fun m => (etaleStalkSmallEtalePullObjIso B f' (x.toGeometricPoint B f' t)
            AddCommGrpCat.{u + 1} ((abPullback.{u, u + 1} B g).obj F)).inv m)
          (iso_inv_hom_apply _ _)).trans (iso_inv_hom_apply _ _))
  subst hz
  have hinv := inverseImageSquareIso_inv_germ.{u} B p f' f g sq
    (x.toGeometricPoint B f' t) F V ⟨ℓ.1, pw₁⟩ ⟨ℓ.1, pw₂⟩ ℓ rfl rfl τ
  -- the left-hand side is the germ of `τ` at `t`, read through the comparison along `g`
  have hpcancel : (fiberStalkBaseChangeIso.{u, u + 1} B p f' f g sq t
          ((abPullback.{u, u + 1} B f).obj F) x).inv
      ((etaleStalkSmallEtalePullObjIso B p (x.toGeometricPoint B f' t) AddCommGrpCat.{u + 1}
          ((abPullback.{u, u + 1} B f).obj F)).inv
        ((etaleStalkSmallEtalePullObjIso B f
            ((x.toGeometricPoint B f' t).map (B.inclusion.map p)) AddCommGrpCat.{u + 1} F).inv
          (etaleGerm B Y.obj Y.property
            (((x.toGeometricPoint B f' t).map (B.inclusion.map p)).map (B.inclusion.map f))
            F.obj V ⟨ℓ.1, pw₁⟩ τ))) =
      (etaleStalkSmallEtalePullObjIso B f
          ((x.toGeometricPoint B f' t).map (B.inclusion.map p)) AddCommGrpCat.{u + 1} F).inv
        (etaleGerm B Y.obj Y.property
          (((x.toGeometricPoint B f' t).map (B.inclusion.map p)).map (B.inclusion.map f))
          F.obj V ⟨ℓ.1, pw₁⟩ τ) :=
    iso_hom_inv_apply (etaleStalkSmallEtalePullObjIso B p (x.toGeometricPoint B f' t)
      AddCommGrpCat.{u + 1} ((abPullback.{u, u + 1} B f).obj F)) _
  have hfhom := fiberPointPullbackStalkIso_hom_apply.{u} B f (t.map (B.inclusion.map g)) F
    (fiberPointBaseChange B p f' f g sq t x)
    ((etaleStalkSmallEtalePullObjIso B f
        ((x.toGeometricPoint B f' t).map (B.inclusion.map p)) AddCommGrpCat.{u + 1} F).inv
      (etaleGerm B Y.obj Y.property
        (((x.toGeometricPoint B f' t).map (B.inclusion.map p)).map (B.inclusion.map f))
        F.obj V ⟨ℓ.1, pw₁⟩ τ))
  have hfcancel := iso_hom_inv_apply (etaleStalkSmallEtalePullObjIso B f
    ((x.toGeometricPoint B f' t).map (B.inclusion.map p)) AddCommGrpCat.{u + 1} F)
    (etaleGerm B Y.obj Y.property
      (((x.toGeometricPoint B f' t).map (B.inclusion.map p)).map (B.inclusion.map f))
      F.obj V ⟨ℓ.1, pw₁⟩ τ)
  have hleft := etaleGerm_eqToHom.{u, u + 1} B Y.obj Y.property t.residueField
    (m := (x.1 ≫ B.inclusion.map p) ≫ B.inclusion.map f)
    (m' := t.hom ≫ B.inclusion.map g)
    (by rw [Category.assoc, hsqm, ← Category.assoc, x.2])
    F.obj V ⟨ℓ.1, pw₁⟩ ⟨ℓ.1, pℓt⟩ rfl τ
  -- the right-hand side is the same germ
  have hf'hom := fiberPointPullbackStalkIso_hom_apply.{u} B f' t
    ((abPullback.{u, u + 1} B g).obj F) x
    ((etaleStalkSmallEtalePullObjIso B f' (x.toGeometricPoint B f' t)
        AddCommGrpCat.{u + 1} ((abPullback.{u, u + 1} B g).obj F)).inv
      ((etaleStalkSmallEtalePullObjIso B g
          ((x.toGeometricPoint B f' t).map (B.inclusion.map f'))
          AddCommGrpCat.{u + 1} F).inv
        (etaleGerm B Y.obj Y.property
          (((x.toGeometricPoint B f' t).map (B.inclusion.map f')).map (B.inclusion.map g))
          F.obj V ℓ τ)))
  have hf'cancel := iso_hom_inv_apply (etaleStalkSmallEtalePullObjIso B f'
    (x.toGeometricPoint B f' t) AddCommGrpCat.{u + 1}
    ((abPullback.{u, u + 1} B g).obj F))
    ((etaleStalkSmallEtalePullObjIso B g
        ((x.toGeometricPoint B f' t).map (B.inclusion.map f'))
        AddCommGrpCat.{u + 1} F).inv
      (etaleGerm B Y.obj Y.property
        (((x.toGeometricPoint B f' t).map (B.inclusion.map f')).map (B.inclusion.map g))
        F.obj V ℓ τ))
  have htrans := etaleStalkSmallEtalePullObjIso_inv_eqToHom_apply.{u} B g
    (toGeometricPoint_map B f' t x) F
    (etaleGerm B Y.obj Y.property
      (((x.toGeometricPoint B f' t).map (B.inclusion.map f')).map (B.inclusion.map g))
      F.obj V ℓ τ)
  have hright := etaleGerm_eqToHom.{u, u + 1} B Y.obj Y.property t.residueField
    (m := (x.1 ≫ B.inclusion.map f') ≫ B.inclusion.map g)
    (m' := t.hom ≫ B.inclusion.map g)
    (by rw [x.2]) F.obj V ℓ ⟨ℓ.1, pℓt⟩ rfl τ
  rw [hinv, hpcancel, hfhom]
  erw [hfcancel, hleft]
  rw [hf'hom, hf'cancel, htrans]
  erw [hright]

end Compatibility


section Clause

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)

/-- The inverse form of the naturality of the stalk decomposition of Stacks 0F5F, on a summand:
the map induced by `f_!φ` on the stalk carries the summand indexed by a point of the geometric
fibre to the summand indexed by the same point. -/
public theorem fShriekStalkIso_inv_natural_apply {Z W : B.Scheme} (q : Z ⟶ W)
    [LocallyOfFiniteType (B.inclusion.map q)] [LocallyQuasiFinite (B.inclusion.map q)]
    (t : GeometricPoint W.obj)
    {G G' : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1}} (φ : G ⟶ G')
    (a : ↑(AddCommGrpCat.of (fiberStalks.{u, u + 1} B q t G))) :
    ((etaleStalkPresheafFunctor B W.obj W.property t AddCommGrpCat.{u + 1}).map
        (((fShriekFunctor.{u, u + 1} B q).map φ).hom))
      ((fShriekStalkIso.{u, u + 1} B q t G).inv a) =
      (fShriekStalkIso.{u, u + 1} B q t G').inv (fiberStalksMap.{u, u + 1} B q t φ a) := by
  have h := ConcreteCategory.congr_hom (fShriekStalkIso_natural.{u, u + 1} B q t φ)
    ((fShriekStalkIso.{u, u + 1} B q t G).inv a)
  have h' := (ConcreteCategory.comp_apply _ _ _).symm.trans
    (h.trans (ConcreteCategory.comp_apply _ _ _))
  have h'' := h'.trans (congrArg
    (fun m => AddCommGrpCat.ofHom (fiberStalksMap.{u, u + 1} B q t φ) m)
    (iso_hom_inv_apply (fShriekStalkIso.{u, u + 1} B q t G) a))
  exact (iso_inv_hom_apply (fShriekStalkIso.{u, u + 1} B q t G') _).symm.trans
    (congrArg (fun m => (fShriekStalkIso.{u, u + 1} B q t G').inv m) h'')

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]

/-- The base change of a trace map for `(f, w)` is a trace map for `(f', w ∘ p)`: it has the
behaviour on geometric stalks which characterises the trace map of Stacks 0GKG. -/
public theorem hasWeightedTraceStalks_baseChange' (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    {τ : (fShriekFunctor.{u, u + 1} B f).obj ((abPullback.{u, u + 1} B f).obj F) ⟶ F}
    (hτ : HasWeightedTraceStalks.{u, u + 1} B f w F τ) :
    HasWeightedTraceStalks.{u, u + 1} B f' (w ∘ B.inclusion.map p)
      ((abPullback.{u, u + 1} B g).obj F)
      ((fShriekFunctor.{u, u + 1} B f').map
          ((inverseImageSquareIso.{u} B p f' f g sq).inv.app F) ≫
        (fShriekBaseChangeNatIso.{u} B p f' f g sq).inv.app
          ((abPullback.{u, u + 1} B f).obj F) ≫
        (abPullback.{u, u + 1} B g).map τ) := by
  refine hasWeightedTraceStalks_of_fiberStalkOf.{u, u + 1} B f' (w ∘ B.inclusion.map p)
    ((abPullback.{u, u + 1} B g).obj F) _ fun t x z => ?_
  -- split the stalk of the composite
  have hmc := congrArg
    (fun m => (ConcreteCategory.hom m)
      ((fShriekStalkIso.{u, u + 1} B f' t
          ((abPullback.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B g).obj F))).inv
        (fiberStalkOf.{u, u + 1} B f' t
          ((abPullback.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B g).obj F)) x z)))
    ((etaleStalkPresheafFunctor B Y'.obj Y'.property t AddCommGrpCat.{u + 1}).map_comp
      (((fShriekFunctor.{u, u + 1} B f').map
        ((inverseImageSquareIso.{u} B p f' f g sq).inv.app F)).hom)
      (((fShriekBaseChangeNatIso.{u} B p f' f g sq).inv.app
          ((abPullback.{u, u + 1} B f).obj F) ≫
        (abPullback.{u, u + 1} B g).map τ).hom))
  refine hmc.trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  -- the first factor moves the summand across the comparison
  have hfirst := fShriekStalkIso_inv_natural_apply.{u} B f' t
    ((inverseImageSquareIso.{u} B p f' f g sq).inv.app F)
    (fiberStalkOf.{u, u + 1} B f' t
      ((abPullback.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B g).obj F)) x z)
  have hsummand := fiberStalksMap_fiberStalkOf.{u, u + 1} B f' t
    ((inverseImageSquareIso.{u} B p f' f g sq).inv.app F) x z
  refine (congrArg (fun m => ((etaleStalkPresheafFunctor B Y'.obj Y'.property t
      AddCommGrpCat.{u + 1}).map
      (((fShriekBaseChangeNatIso.{u} B p f' f g sq).inv.app
          ((abPullback.{u, u + 1} B f).obj F) ≫
        (abPullback.{u, u + 1} B g).map τ).hom)) m)
    (hfirst.trans (congrArg (fun m => (fShriekStalkIso.{u, u + 1} B f' t
      ((abPullback.{u, u + 1} B p).obj ((abPullback.{u, u + 1} B f).obj F))).inv m)
      hsummand))).trans ?_
  -- the rest is the stalk computation of the base change
  refine (baseChangeTrace_fiberStalkOf.{u} B p f' f g sq w F hτ t x _).trans ?_
  rw [fiberPointBaseChange_weight B p f' f g sq w t x]
  exact congrArg (fun m => w ((fiberPointBaseChange B p f' f g sq t x).1 default) • m)
    (fiberPointPullbackStalkIso_square.{u} B p f' f g sq t x F z)

end Clause

section Tagged

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **Stacks 0GKH, part (2): the trace map is compatible with arbitrary base change.** Let
`f : X ⟶ Y` be locally quasi-finite, let `w` be an integer-valued function on `X`, let `F` be an
abelian sheaf on the small étale site of `Y`, and let

```
X' --p--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square. Then the base change along `g` of a trace map `τ` for `(f, w)` at `F`,
transported along the base-change isomorphism `g^{-1}f_!G ≅ f'_!p^{-1}G` of Stacks 0F5J and the
comparison `p^{-1}f^{-1}F ≅ f'^{-1}g^{-1}F` of the two iterated inverse images, is a trace map for
`(f', w ∘ p)` at `g^{-1}F`; equivalently, the square formed by those two comparisons and the two
trace maps commutes.

The finite-type and quasi-finiteness hypotheses on the base change `f'` are supplied from the
square, so only the hypotheses of the source are assumed. The weighting hypothesis of the source
is not needed: the statement holds for an arbitrary integer-valued `w`, the pulled-back function
`w ∘ p` being a weighting of `f'` whenever `w` is a weighting of `f` by Stacks 0F3B
(`AlgebraicGeometry.IsWeighting.comp_of_isPullback`). The trace maps enter through the behaviour
on geometric stalks by which Stacks 0GKG characterises them, which by
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_unique` determines at most one morphism for
each sheaf. -/
@[stacks 0GKH "part (2), compatibility of the trace map with arbitrary base change, for an \
arbitrary cartesian square with locally quasi-finite vertical morphism and an arbitrary \
integer-valued weight: the base change of a trace map for `(f, w)` is a trace map for \
`(f', w ∘ p)`, and the square formed by the base-change isomorphism of 0F5J, the comparison of \
the two iterated inverse images, and the two trace maps commutes. The trace maps enter through \
the behaviour on geometric stalks by which 0GKG characterises them, which determines at most one \
morphism per sheaf by `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_unique`. The \
finite-type and quasi-finiteness conditions on the base change are supplied from the square.",
  sga "4 XVII 6.2.5" "more general"]
public theorem hasWeightedTraceStalks_baseChange (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    {τ : (fShriekFunctor.{u, u + 1} B f).obj ((abPullback.{u, u + 1} B f).obj F) ⟶ F}
    (hτ : HasWeightedTraceStalks.{u, u + 1} B f w F τ) :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    HasWeightedTraceStalks.{u, u + 1} B f' (w ∘ B.inclusion.map p)
        ((abPullback.{u, u + 1} B g).obj F)
        ((fShriekFunctor.{u, u + 1} B f').map
            ((inverseImageSquareIso.{u} B p f' f g sq).inv.app F) ≫
          (fShriekBaseChangeNatIso.{u} B p f' f g sq).inv.app
            ((abPullback.{u, u + 1} B f).obj F) ≫
          (abPullback.{u, u + 1} B g).map τ) ∧
      ∀ τ' : (fShriekFunctor.{u, u + 1} B f').obj
          ((abPullback.{u, u + 1} B f').obj ((abPullback.{u, u + 1} B g).obj F)) ⟶
            (abPullback.{u, u + 1} B g).obj F,
        HasWeightedTraceStalks.{u, u + 1} B f' (w ∘ B.inclusion.map p)
            ((abPullback.{u, u + 1} B g).obj F) τ' →
          (fShriekBaseChangeNatIso.{u} B p f' f g sq).hom.app
              ((abPullback.{u, u + 1} B f).obj F) ≫
            (fShriekFunctor.{u, u + 1} B f').map
              ((inverseImageSquareIso.{u} B p f' f g sq).hom.app F) ≫ τ' =
            (abPullback.{u, u + 1} B g).map τ := by
  let := locallyOfFiniteType_of_isPullback B p f' f g sq
  let := locallyQuasiFinite_of_isPullback B p f' f g sq
  refine ⟨hasWeightedTraceStalks_baseChange'.{u} B p f' f g sq w F hτ, fun τ' hτ' => ?_⟩
  have heq := hasWeightedTraceStalks_unique.{u, u + 1} B f' (w ∘ B.inclusion.map p)
    ((abPullback.{u, u + 1} B g).obj F) hτ'
    (hasWeightedTraceStalks_baseChange'.{u} B p f' f g sq w F hτ)
  rw [heq]
  simp

end Tagged

end AlgebraicGeometry.SmallEtale

end
