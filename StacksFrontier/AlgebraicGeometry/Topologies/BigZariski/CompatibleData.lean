module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigZariski.SheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites

/-!
# Compatible systems of sheaves on the schemes over a base

A sheaf on the big Zariski site of a scheme `S` is, by Tag 0213, the same thing as a sheaf on
each scheme `T` over `S` together with comparison maps `f⁻¹F_T → F_{T'}` for every morphism
`f : T' ⟶ T` over `S`, subject to a cocycle identity for compositions and the requirement
that the comparison be an isomorphism when `f` is an open immersion.  This file defines that
system of data and the category it forms.

## Main definitions

* `AlgebraicGeometry.BigZariskiSheafData` — the compatible system of sheaves.
* `AlgebraicGeometry.BigZariskiSheafData.Hom` and the resulting category structure.
* `AlgebraicGeometry.BigZariskiSheafData.eval` — evaluation at one scheme over `S`.

## Implementation notes

The sheaf attached to `T` is a sheaf on the underlying topological space of `T`; the small
Zariski site of `T` is identified with that space by Tag 020X.  The cocycle identity is
stated through the canonical composition isomorphism for inverse images.

## References

* [Stacks Project, Tag 0213](https://stacks.math.columbia.edu/tag/0213)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A sheaf on each scheme over `S`, with compatible inverse-image comparisons. -/
@[stacks 0213 "the compatible data"]
public structure BigZariskiSheafData where
  /-- The sheaf on the underlying space of each scheme over `S`. -/
  sheaf (T : BigZariskiOver B S hS) :
    Sheaf (Opens.grothendieckTopology T.left.1.toTopCat) (Type (max u v))
  /-- The comparison along a morphism over `S`. -/
  pullback {T T' : BigZariskiOver B S hS} (f : T' ⟶ T) :
    (TopCat.Sheaf.inverseImage.{u, v} (B.inclusion.map f.left).base).obj
      (sheaf T) ⟶ sheaf T'
  /-- Comparisons commute with composition, up to the canonical pullback isomorphism. -/
  pullback_comp {T T' T'' : BigZariskiOver B S hS}
      (f : T' ⟶ T) (g : T'' ⟶ T') :
    (TopCat.Sheaf.inverseImage.{u, v} (B.inclusion.map g.left).base).map
        (pullback f) ≫ pullback g =
      (TopCat.Sheaf.inverseImageCompIso.{u, v} (B.inclusion.map g.left).base
        (B.inclusion.map f.left).base).inv.app (sheaf T) ≫
        pullback (g ≫ f)
  /-- An open immersion induces an isomorphism of sheaves. -/
  isIso_pullback {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
      [IsOpenImmersion (B.inclusion.map f.left)] : IsIso (pullback f)

/-- A morphism of compatible systems commutes with every inverse-image comparison. -/
public structure BigZariskiSheafData.Hom (D E : BigZariskiSheafData.{u, v} B S hS) where
  /-- Its component on each scheme. -/
  app (T : BigZariskiOver B S hS) : D.sheaf T ⟶ E.sheaf T
  /-- Naturality with respect to morphisms of schemes over the base. -/
  naturality {T T' : BigZariskiOver B S hS} (f : T' ⟶ T) :
    (TopCat.Sheaf.inverseImage.{u, v} (B.inclusion.map f.left).base).map (app T) ≫
        E.pullback f = D.pullback f ≫ app T'

/-- Two morphisms of compatible systems agreeing on every scheme over `S` are equal. -/
@[ext] public theorem BigZariskiSheafData.Hom.ext
    {D E : BigZariskiSheafData.{u, v} B S hS}
    {φ ψ : BigZariskiSheafData.Hom B S hS D E}
    (h : ∀ T, φ.app T = ψ.app T) : φ = ψ := by
  cases φ
  cases ψ
  congr 1
  exact funext h

/-- Compatible systems of sheaves over `S` form a category, with componentwise identities
and composition. -/
public instance : Category (BigZariskiSheafData.{u, v} B S hS) where
  Hom := BigZariskiSheafData.Hom B S hS
  id D := ⟨fun T => 𝟙 _, fun _ => by simp⟩
  comp φ ψ := ⟨fun T => φ.app T ≫ ψ.app T, fun f => by
    rw [Functor.map_comp, Category.assoc, ψ.naturality f, ← Category.assoc, φ.naturality f,
      Category.assoc]⟩
  id_comp _ := BigZariskiSheafData.Hom.ext B S hS fun _ => Category.id_comp _
  comp_id _ := BigZariskiSheafData.Hom.ext B S hS fun _ => Category.comp_id _
  assoc _ _ _ := BigZariskiSheafData.Hom.ext B S hS fun _ => Category.assoc _ _ _

/-- Evaluation of compatible data at one scheme. -/
public def BigZariskiSheafData.eval
    (T : BigZariskiOver B S hS) :
    BigZariskiSheafData.{u, v} B S hS ⥤
      Sheaf (Opens.grothendieckTopology T.left.1.toTopCat) (Type (max u v)) where
  obj D := D.sheaf T
  map φ := φ.app T
  map_id _ := rfl
  map_comp _ _ := rfl

end AlgebraicGeometry
