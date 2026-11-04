module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso

/-!
# A pair of homotopy equivalences induces a homotopy equivalence of total complexes

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor, additive in each variable, between preadditive
categories, and let `c` totalize the pair of shapes `c₁`, `c₂`.  If `e₁ : K₁ ≃ L₁` and
`e₂ : K₂ ≃ L₂` are homotopy equivalences of homological complexes, then
`Tot(F(K₁, K₂)) ≃ Tot(F(L₁, L₂))` is one as well, with `hom` the induced map
`HomologicalComplex.mapBifunctorMap e₁.hom e₂.hom F c`. This is a two-variable form, for homotopy
equivalences, of [Stacks, Tag 064I].

## Main definitions

* `HomologicalComplex.mapBifunctorHomotopyEquiv`: the homotopy equivalence.

## Main results

* `HomologicalComplex.mapBifunctorHomotopyEquiv_hom` and
  `HomologicalComplex.mapBifunctorHomotopyEquiv_inv`: its two maps are the induced maps.

## References

* [Stacks Project, Tag 064I](https://stacks.math.columbia.edu/tag/064I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  {K₁ L₁ : HomologicalComplex C₁ c₁} {K₂ L₂ : HomologicalComplex C₂ c₂}
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁ : C₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [∀ (A : HomologicalComplex C₁ c₁) (B : HomologicalComplex C₂ c₂), HasMapBifunctor A B F c]

/-- **A pair of homotopy equivalences induces one on total complexes of a bifunctor.** A pair of
homotopy equivalences `e₁ : K₁ ≃ L₁`, `e₂ : K₂ ≃ L₂` induces a homotopy equivalence
`Tot(F(K₁, K₂)) ≃ Tot(F(L₁, L₂))`, whose two maps are the induced maps of the pair of `hom`s
and of the pair of `inv`s. -/
noncomputable def mapBifunctorHomotopyEquiv
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (mapBifunctor K₁ K₂ F c) (mapBifunctor L₁ L₂ F c) where
  hom := mapBifunctorMap e₁.hom e₂.hom F c
  inv := mapBifunctorMap e₁.inv e₂.inv F c
  homotopyHomInvId :=
    ((Homotopy.ofEq (mapBifunctorMap_comp F c e₁.hom e₂.hom e₁.inv e₂.inv)).trans
      ((mapBifunctorMapHomotopy₁ e₁.homotopyHomInvId (e₂.hom ≫ e₂.inv) F c).trans
        (mapBifunctorMapHomotopy₂ (𝟙 K₁) e₂.homotopyHomInvId F c))).trans
      (Homotopy.ofEq (mapBifunctorMap_id F c))
  homotopyInvHomId :=
    ((Homotopy.ofEq (mapBifunctorMap_comp F c e₁.inv e₂.inv e₁.hom e₂.hom)).trans
      ((mapBifunctorMapHomotopy₁ e₁.homotopyInvHomId (e₂.inv ≫ e₂.hom) F c).trans
        (mapBifunctorMapHomotopy₂ (𝟙 L₁) e₂.homotopyInvHomId F c))).trans
      (Homotopy.ofEq (mapBifunctorMap_id F c))

/-- The forward map of `HomologicalComplex.mapBifunctorHomotopyEquiv` is the induced map of
the two forward maps. -/
@[simp]
theorem mapBifunctorHomotopyEquiv_hom
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    (mapBifunctorHomotopyEquiv F c e₁ e₂).hom = mapBifunctorMap e₁.hom e₂.hom F c :=
  rfl

/-- The backward map of `HomologicalComplex.mapBifunctorHomotopyEquiv` is the induced map of
the two backward maps. -/
@[simp]
theorem mapBifunctorHomotopyEquiv_inv
    (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    (mapBifunctorHomotopyEquiv F c e₁ e₂).inv = mapBifunctorMap e₁.inv e₂.inv F c :=
  rfl

end HomologicalComplex

end
