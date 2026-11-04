module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Colimit preservation for a functor presented by a coproduct or by a cokernel

Let `A` and `B` be categories and let `D : K ⥤ A` be a diagram. Two ways of presenting a
functor `H : A ⥤ B` pass colimit preservation from the pieces of the presentation to `H`.

In the first, `H` is objectwise a coproduct: a family `F i : A ⥤ B` is given together with
natural transformations `F i ⟶ H` whose components at each object of `A` form a colimiting
cofan. In the second, `H` is objectwise a cokernel: natural transformations `α : F ⟶ G` and
`π : G ⟶ H` are given with `α.app X ≫ π.app X = 0` and with `π.app X` a cokernel of `α.app X`
for every `X`. Neither statement needs `B` to have colimits of shape `K`.

## Main results

* `Stacks.CategoryTheory.PresentedFunctor.preservesColimit_of_isColimitCofan`: a functor
  presented objectwise as a coproduct of functors preserving the colimit of `D` preserves that
  colimit, with
  `Stacks.CategoryTheory.PresentedFunctor.preservesColimitsOfShape_of_isColimitCofan` and
  `preservesColimitsOfSize_of_isColimitCofan` its shape and size forms.
* `Stacks.CategoryTheory.PresentedFunctor.preservesColimit_of_isColimitCokernelCofork`: a
  functor presented objectwise as a cokernel of a natural transformation between functors
  preserving the colimit of `D` preserves that colimit, with
  `Stacks.CategoryTheory.PresentedFunctor.preservesColimitsOfShape_of_isColimitCokernelCofork`
  and `preservesColimitsOfSize_of_isColimitCokernelCofork` its shape and size forms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ v u

namespace Stacks.CategoryTheory.PresentedFunctor

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {K : Type u} [Category.{v} K] {D : K ⥤ A}

section Cofan

variable {ι : Type w} {F : ι → A ⥤ B} {H : A ⥤ B} (incl : ∀ i, F i ⟶ H)

/-- The cocone on `D ⋙ F i` obtained from a cocone on `D ⋙ H` by composing with the structure
map of a coproduct presentation of `H`. -/
private def coconeOfCofan (i : ι) (s : Cocone (D ⋙ H)) : Cocone (D ⋙ F i) where
  pt := s.pt
  ι :=
    { app := fun k ↦ (incl i).app (D.obj k) ≫ s.ι.app k
      naturality := fun k k' f ↦ by simp [← s.w f] }

variable {c : Cocone D} (hF : ∀ i, IsColimit ((F i).mapCocone c))

/-- The component at `i` of the morphism out of `H.obj c.pt` attached to a cocone on `D ⋙ H` by
a coproduct presentation of `H`. -/
private def cofanComponent (i : ι) (s : Cocone (D ⋙ H)) : (F i).obj c.pt ⟶ s.pt :=
  (hF i).desc (coconeOfCofan incl i s)

private lemma map_comp_cofanComponent (i : ι) (s : Cocone (D ⋙ H)) (k : K) :
    (F i).map (c.ι.app k : D.obj k ⟶ c.pt) ≫ cofanComponent incl hF i s =
      (incl i).app (D.obj k) ≫ s.ι.app k :=
  (hF i).fac (coconeOfCofan incl i s) k

private lemma cofanComponent_uniq (i : ι) (s : Cocone (D ⋙ H)) (g : (F i).obj c.pt ⟶ s.pt)
    (hg : ∀ k : K, (F i).map (c.ι.app k : D.obj k ⟶ c.pt) ≫ g =
      (incl i).app (D.obj k) ≫ s.ι.app k) :
    g = cofanComponent incl hF i s :=
  (hF i).hom_ext fun k ↦ (hg k).trans (map_comp_cofanComponent incl hF i s k).symm

variable (hH : ∀ X : A, IsColimit (Cofan.mk (H.obj X) fun i ↦ (incl i).app X))

/-- The morphism out of `H.obj c.pt` attached to a cocone on `D ⋙ H` by a coproduct
presentation of `H`. -/
private def cofanDesc (s : Cocone (D ⋙ H)) : H.obj c.pt ⟶ s.pt :=
  Cofan.IsColimit.desc (hH c.pt) fun i ↦ cofanComponent incl hF i s

private lemma incl_comp_cofanDesc (s : Cocone (D ⋙ H)) (i : ι) :
    (incl i).app c.pt ≫ cofanDesc incl hF hH s = cofanComponent incl hF i s :=
  Cofan.IsColimit.fac (hH c.pt) _ i

/-- **A functor presented objectwise as a coproduct of colimit-preserving functors preserves
that colimit.** The presentation is the family `incl` of structure maps, whose components at
each object of `A` are required to form a colimiting cofan. -/
theorem preservesColimit_of_isColimitCofan
    (hH : ∀ X : A, IsColimit (Cofan.mk (H.obj X) fun i ↦ (incl i).app X))
    [∀ i, PreservesColimit D (F i)] : PreservesColimit D H := by
  refine ⟨fun {c} hc ↦ ⟨?_⟩⟩
  have hF : ∀ i, IsColimit ((F i).mapCocone c) := fun i ↦ isColimitOfPreserves (F i) hc
  refine
    { desc := cofanDesc incl hF hH
      fac := fun s k ↦ Cofan.IsColimit.hom_ext (hH (D.obj k)) _ _ fun i ↦ ?_
      uniq := fun s m hm ↦ Cofan.IsColimit.hom_ext (hH c.pt) _ _ fun i ↦ ?_ }
  · show (incl i).app (D.obj k) ≫ H.map (c.ι.app k : D.obj k ⟶ c.pt) ≫ cofanDesc incl hF hH s =
      (incl i).app (D.obj k) ≫ s.ι.app k
    rw [← (incl i).naturality_assoc (X := D.obj k) (Y := c.pt), incl_comp_cofanDesc,
      map_comp_cofanComponent]
  · have hm' : ∀ k : K, H.map (c.ι.app k : D.obj k ⟶ c.pt) ≫ m = s.ι.app k := hm
    show (incl i).app c.pt ≫ m = (incl i).app c.pt ≫ cofanDesc incl hF hH s
    rw [incl_comp_cofanDesc]
    refine cofanComponent_uniq incl hF i s _ fun k ↦ ?_
    rw [(incl i).naturality_assoc (X := D.obj k) (Y := c.pt), hm' k]

/-- The colimits of one shape are preserved by a functor presented objectwise as a coproduct of
functors preserving them. -/
theorem preservesColimitsOfShape_of_isColimitCofan
    (hH : ∀ X : A, IsColimit (Cofan.mk (H.obj X) fun i ↦ (incl i).app X))
    [∀ i, PreservesColimitsOfShape K (F i)] : PreservesColimitsOfShape K H where
  preservesColimit {_} := preservesColimit_of_isColimitCofan incl hH

/-- The colimits of one size are preserved by a functor presented objectwise as a coproduct of
functors preserving them. -/
theorem preservesColimitsOfSize_of_isColimitCofan
    (hH : ∀ X : A, IsColimit (Cofan.mk (H.obj X) fun i ↦ (incl i).app X))
    [∀ i, PreservesColimitsOfSize.{v, u} (F i)] : PreservesColimitsOfSize.{v, u} H where
  preservesColimitsOfShape {_ _} := preservesColimitsOfShape_of_isColimitCofan incl hH

end Cofan

section Cokernel

variable [HasZeroMorphisms B] {F G H : A ⥤ B} (α : F ⟶ G) (π : G ⟶ H)
  (hzero : ∀ X : A, α.app X ≫ π.app X = 0)

/-- The cocone on `D ⋙ G` obtained from a cocone on `D ⋙ H` by composing with the surjection
of a cokernel presentation of `H`. -/
private def coconeOfCokernel (s : Cocone (D ⋙ H)) : Cocone (D ⋙ G) where
  pt := s.pt
  ι :=
    { app := fun k ↦ π.app (D.obj k) ≫ s.ι.app k
      naturality := fun k k' f ↦ by simp [← s.w f] }

variable {c : Cocone D} (hG : IsColimit (G.mapCocone c))

/-- The morphism out of `G.obj c.pt` attached to a cocone on `D ⋙ H` by a cokernel presentation
of `H`. -/
private def cokernelComponent (s : Cocone (D ⋙ H)) : G.obj c.pt ⟶ s.pt :=
  hG.desc (coconeOfCokernel π s)

omit [HasZeroMorphisms B] in
private lemma map_comp_cokernelComponent (s : Cocone (D ⋙ H)) (k : K) :
    G.map (c.ι.app k : D.obj k ⟶ c.pt) ≫ cokernelComponent π hG s =
      π.app (D.obj k) ≫ s.ι.app k :=
  hG.fac (coconeOfCokernel π s) k

omit [HasZeroMorphisms B] in
private lemma cokernelComponent_uniq (s : Cocone (D ⋙ H)) (g : G.obj c.pt ⟶ s.pt)
    (hg : ∀ k : K, G.map (c.ι.app k : D.obj k ⟶ c.pt) ≫ g = π.app (D.obj k) ≫ s.ι.app k) :
    g = cokernelComponent π hG s :=
  hG.hom_ext fun k ↦ (hg k).trans (map_comp_cokernelComponent π hG s k).symm

private lemma alpha_comp_cokernelComponent
    (hzero : ∀ X : A, α.app X ≫ π.app X = 0) (hF : IsColimit (F.mapCocone c))
    (s : Cocone (D ⋙ H)) :
    α.app c.pt ≫ cokernelComponent π hG s = 0 ≫ cokernelComponent π hG s := by
  rw [zero_comp]
  refine hF.hom_ext fun k ↦ ?_
  show F.map (c.ι.app k : D.obj k ⟶ c.pt) ≫ α.app c.pt ≫ cokernelComponent π hG s =
    F.map (c.ι.app k : D.obj k ⟶ c.pt) ≫ 0
  rw [comp_zero, α.naturality_assoc (X := D.obj k) (Y := c.pt), map_comp_cokernelComponent,
    ← Category.assoc, hzero (D.obj k), zero_comp]

variable (hH : ∀ X : A, IsColimit (CokernelCofork.ofπ (π.app X) (hzero X)))
  (hF : IsColimit (F.mapCocone c))

/-- The morphism out of `H.obj c.pt` attached to a cocone on `D ⋙ H` by a cokernel presentation
of `H`. -/
private def cokernelDesc (s : Cocone (D ⋙ H)) : H.obj c.pt ⟶ s.pt :=
  Cofork.IsColimit.desc (hH c.pt) (cokernelComponent π hG s)
    (alpha_comp_cokernelComponent α π hG hzero hF s)

private lemma pi_comp_cokernelDesc (s : Cocone (D ⋙ H)) :
    π.app c.pt ≫ cokernelDesc α π hzero hG hH hF s = cokernelComponent π hG s :=
  Cofork.IsColimit.π_desc (hH c.pt)

/-- **A functor presented objectwise as a cokernel of a natural transformation between
colimit-preserving functors preserves that colimit.** -/
theorem preservesColimit_of_isColimitCokernelCofork
    (hH : ∀ X : A, IsColimit (CokernelCofork.ofπ (π.app X) (hzero X)))
    [PreservesColimit D F] [PreservesColimit D G] : PreservesColimit D H := by
  refine ⟨fun {c} hc ↦ ⟨?_⟩⟩
  have hF : IsColimit (F.mapCocone c) := isColimitOfPreserves F hc
  have hG : IsColimit (G.mapCocone c) := isColimitOfPreserves G hc
  refine
    { desc := cokernelDesc α π hzero hG hH hF
      fac := fun s k ↦ Cofork.IsColimit.hom_ext (hH (D.obj k)) ?_
      uniq := fun s m hm ↦ Cofork.IsColimit.hom_ext (hH c.pt) ?_ }
  · show π.app (D.obj k) ≫ H.map (c.ι.app k : D.obj k ⟶ c.pt) ≫
      cokernelDesc α π hzero hG hH hF s = π.app (D.obj k) ≫ s.ι.app k
    rw [← π.naturality_assoc (X := D.obj k) (Y := c.pt), pi_comp_cokernelDesc,
      map_comp_cokernelComponent]
  · have hm' : ∀ k : K, H.map (c.ι.app k : D.obj k ⟶ c.pt) ≫ m = s.ι.app k := hm
    show π.app c.pt ≫ m = π.app c.pt ≫ cokernelDesc α π hzero hG hH hF s
    rw [pi_comp_cokernelDesc]
    refine cokernelComponent_uniq π hG s _ fun k ↦ ?_
    rw [π.naturality_assoc (X := D.obj k) (Y := c.pt), hm' k]

/-- The colimits of one shape are preserved by a functor presented objectwise as a cokernel of
a natural transformation between functors preserving them. -/
theorem preservesColimitsOfShape_of_isColimitCokernelCofork
    (hH : ∀ X : A, IsColimit (CokernelCofork.ofπ (π.app X) (hzero X)))
    [PreservesColimitsOfShape K F] [PreservesColimitsOfShape K G] :
    PreservesColimitsOfShape K H where
  preservesColimit {_} := preservesColimit_of_isColimitCokernelCofork α π hzero hH

/-- The colimits of one size are preserved by a functor presented objectwise as a cokernel of a
natural transformation between functors preserving them. -/
theorem preservesColimitsOfSize_of_isColimitCokernelCofork
    (hH : ∀ X : A, IsColimit (CokernelCofork.ofπ (π.app X) (hzero X)))
    [PreservesColimitsOfSize.{v, u} F] [PreservesColimitsOfSize.{v, u} G] :
    PreservesColimitsOfSize.{v, u} H where
  preservesColimitsOfShape {_ _} :=
    preservesColimitsOfShape_of_isColimitCokernelCofork α π hzero hH

end Cokernel

end Stacks.CategoryTheory.PresentedFunctor

end
