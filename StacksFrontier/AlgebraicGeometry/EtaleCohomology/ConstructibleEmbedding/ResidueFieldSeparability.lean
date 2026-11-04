module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.FieldTheory.SeparableDegree

/-!
# Separability of residue field extensions along morphisms of schemes

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z` and a point `x` of `X` the residue field
extensions form a tower `κ(g (f x)) ⟶ κ(f x) ⟶ κ(x)`; if the composite is separable, so are both
steps. For a morphism `s : Spec K ⟶ Y` from the spectrum of a field the embedding
`κ(s pt) ⟶ K` of `AlgebraicGeometry.Scheme.descResidueField` plays the role of the top step.

These are the field-theoretic inputs to the last sentence of Stacks 09Z6: the function field of a
stage `Y_i ⟶ Z` of the proof is an intermediate field of a separable closure of `κ(x)`, hence
separable over the function field of `Z`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isSeparable_residueFieldMap_of_comp_left`,
  `AlgebraicGeometry.Scheme.Hom.isSeparable_residueFieldMap_of_comp_right` — the two steps of a
  separable tower.
* `AlgebraicGeometry.isSeparable_residueFieldMap_of_isSeparable_descResidueField`,
  `AlgebraicGeometry.isSeparable_descResidueField_comp_of_surjectiveOnStalks`,
  `AlgebraicGeometry.isSeparable_descResidueField_fromSpecStalk_genericPoint` — the same through
  a point with values in a field.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-- If a composite `A →+* B →+* C` of field homomorphisms is separable, so are both steps. -/
private theorem isSeparable_of_comp_eq {A B C : Type*} [Field A] [Field B] [Field C]
    (a : A →+* B) (b : B →+* C) {c : A →+* C} (hc : c = b.comp a)
    (h : letI := c.toAlgebra; Algebra.IsSeparable A C) :
    (letI := a.toAlgebra; Algebra.IsSeparable A B) ∧
      (letI := b.toAlgebra; Algebra.IsSeparable B C) := by
  subst hc
  let := a.toAlgebra
  let := b.toAlgebra
  let := (b.comp a).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨Algebra.isSeparable_tower_bot_of_isSeparable A B C,
    Algebra.isSeparable_tower_top_of_isSeparable A B C⟩

/-- **The bottom step of a separable tower of residue fields is separable.** If `p = f ≫ g` and
`κ(x)` is separable over `κ(p x)`, then `κ(f x)` is separable over `κ(g (f x))`. -/
theorem Scheme.Hom.isSeparable_residueFieldMap_of_comp_left (f : X ⟶ Y) (g : Y ⟶ Z)
    {p : X ⟶ Z} (hp : f ≫ g = p) (x : X)
    (h : letI := (p.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable (Z.residueField (p x)) (X.residueField x)) :
    letI := (g.residueFieldMap (f x)).hom.toAlgebra
    Algebra.IsSeparable (Z.residueField (g (f x))) (Y.residueField (f x)) := by
  subst hp
  exact (isSeparable_of_comp_eq _ _ (congrArg (·.hom) (Scheme.residueFieldMap_comp f g x)) h).1

/-- **The top step of a separable tower of residue fields is separable.** If `p = f ≫ g` and
`κ(x)` is separable over `κ(p x)`, then `κ(x)` is separable over `κ(f x)`. -/
theorem Scheme.Hom.isSeparable_residueFieldMap_of_comp_right (f : X ⟶ Y) (g : Y ⟶ Z)
    {p : X ⟶ Z} (hp : f ≫ g = p) (x : X)
    (h : letI := (p.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable (Z.residueField (p x)) (X.residueField x)) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
  subst hp
  exact (isSeparable_of_comp_eq _ _ (congrArg (·.hom) (Scheme.residueFieldMap_comp f g x)) h).2

variable {K : Type u} [Field K]

/-- For a point `s : Spec K ⟶ Y` with values in a field and a morphism `p : Y ⟶ X`: if `K` is
separable over `κ(q pt)` for `q = s ≫ p`, then so is `κ(s pt)`. -/
theorem isSeparable_residueFieldMap_of_isSeparable_descResidueField (s : Spec (.of K) ⟶ Y)
    (p : Y ⟶ X) {q : Spec (.of K) ⟶ X} (hq : s ≫ p = q)
    (h : letI : Algebra (X.residueField (q (closedPoint K))) K :=
        (Scheme.descResidueField (Scheme.stalkClosedPointTo q)).hom.toAlgebra
      Algebra.IsSeparable (X.residueField (q (closedPoint K))) K) :
    letI := (p.residueFieldMap (s (closedPoint K))).hom.toAlgebra
    Algebra.IsSeparable (X.residueField (p (s (closedPoint K))))
      (Y.residueField (s (closedPoint K))) := by
  subst hq
  exact (isSeparable_of_comp_eq _ _
    (congrArg (·.hom) (Scheme.descResidueField_stalkClosedPointTo_comp (f := p) s)) h).1

/-- Separability of a point with values in a field is preserved by composing with a morphism
which is surjective on stalks (for instance a closed immersion): its residue field maps are
isomorphisms. -/
theorem isSeparable_descResidueField_comp_of_surjectiveOnStalks (s : Spec (.of K) ⟶ Y)
    (ι : Y ⟶ X) [SurjectiveOnStalks ι] {q : Spec (.of K) ⟶ X} (hq : s ≫ ι = q)
    (h : letI : Algebra (Y.residueField (s (closedPoint K))) K :=
        (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
      Algebra.IsSeparable (Y.residueField (s (closedPoint K))) K) :
    letI : Algebra (X.residueField (q (closedPoint K))) K :=
      (Scheme.descResidueField (Scheme.stalkClosedPointTo q)).hom.toAlgebra
    Algebra.IsSeparable (X.residueField (q (closedPoint K))) K := by
  subst hq
  let : Algebra (X.residueField (ι (s (closedPoint K)))) (Y.residueField (s (closedPoint K))) :=
    (ι.residueFieldMap (s (closedPoint K))).hom.toAlgebra
  let : Algebra (Y.residueField (s (closedPoint K))) K :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
  let : Algebra (X.residueField (ι (s (closedPoint K)))) K :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (s ≫ ι))).hom.toAlgebra
  have : IsScalarTower (X.residueField (ι (s (closedPoint K))))
      (Y.residueField (s (closedPoint K))) K :=
    IsScalarTower.of_algebraMap_eq fun a =>
      congrArg (fun t => t.hom a) (Scheme.descResidueField_stalkClosedPointTo_comp (f := ι) s)
  have hsurj : Function.Surjective (ι.residueFieldMap (s (closedPoint K))) := by
    intro b
    obtain ⟨c, rfl⟩ := Y.residue_surjective _ b
    obtain ⟨d, rfl⟩ := ι.stalkMap_surjective _ c
    refine ⟨X.residue _ d, ?_⟩
    change (X.residue _ ≫ ι.residueFieldMap _).hom d = (ι.stalkMap _ ≫ Y.residue _).hom d
    rw [Scheme.residue_residueFieldMap]
  have : Algebra.IsSeparable (X.residueField (ι (s (closedPoint K))))
      (Y.residueField (s (closedPoint K))) := ⟨fun b => by
    obtain ⟨a, rfl⟩ := hsurj b
    exact isSeparable_algebraMap a⟩
  have : Algebra.IsSeparable (Y.residueField (s (closedPoint K))) K := h
  exact Algebra.IsSeparable.trans (X.residueField (ι (s (closedPoint K))))
    (Y.residueField (s (closedPoint K))) K

/-- The point `s : Spec K ⟶ Z` through the generic point of an integral scheme `Z` given by a
separable extension `φ : K(Z) ⟶ K` of the function field: `K` is separable over the residue field
at the image of `s`. -/
theorem isSeparable_descResidueField_fromSpecStalk_genericPoint [IsIntegral Z]
    (φ : Z.functionField ⟶ .of K)
    (hφ : letI := φ.hom.toAlgebra; Algebra.IsSeparable Z.functionField K) (s : Spec (.of K) ⟶ Z)
    (hs : s = Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)) :
    letI : Algebra (Z.residueField (s (closedPoint K))) K :=
      (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
    Algebra.IsSeparable (Z.residueField (s (closedPoint K))) K := by
  have hpt : s (closedPoint K) = genericPoint Z := by
    subst hs
    exact (congrArg (Z.fromSpecStalk (genericPoint Z)).base
      (Spec_closedPoint (R := Z.functionField) (S := CommRingCat.of K) (f := φ))).trans
      Scheme.fromSpecStalk_closedPoint
  have key : ∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : s (closedPoint K) ∈ U),
      Z.presheaf.germ U (s (closedPoint K)) hU' ≫ Scheme.stalkClosedPointTo s =
        Z.presheaf.germ U (genericPoint Z) hU ≫ φ := by
    subst hs
    exact fun U _ hU' => Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk φ U hU'
  let c : Z.functionField ⟶ Z.presheaf.stalk (s (closedPoint K)) :=
    (Z.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom
  have hc : c ≫ Scheme.stalkClosedPointTo s = φ := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
    rw [← key U hU (hpt ▸ hU), ← Category.assoc]
    congr 1
    exact TopCat.Presheaf.germ_stalkSpecializes _ hU (Inseparable.of_eq hpt.symm).ge
  let := φ.hom.toAlgebra
  have e : (c ≫ Z.residue _) ≫ Scheme.descResidueField (Scheme.stalkClosedPointTo s) = φ := by
    rw [Category.assoc, Scheme.residue_descResidueField, hc]
  exact (isSeparable_of_comp_eq (c ≫ Z.residue _).hom _ (congrArg (·.hom) e).symm hφ).2

end AlgebraicGeometry

end
