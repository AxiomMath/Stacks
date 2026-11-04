module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.Algebra.Homology.Int12AsTotalComplex
public import StacksFrontier.Algebra.Homology.TricomplexRotation

/-!
# Homology in the last index of a tricomplex built from a complex-valued functor

Let `G : C ⥤ HomologicalComplex D c₁` be an additive functor with values in complexes and let
`L : HomologicalComplex₂ C c₂ c₃` be a bicomplex. Applying `G` termwise and moving its new index
to the front gives the tricomplex `HomologicalComplex₃.ofComplexValuedFunctor G L`, whose term in
position `(i₁, i₂, i₃)` is `(G (L^{i₂, i₃}))_{i₁}`.

This file computes its homology in the third index, under the hypothesis that each
`G ⋙ HomologicalComplex.eval D c₁ i₁` -- that is, `G` followed by taking the degree-`i₁` term of
its value -- preserves homology. The answer is the expected one: homology may be taken before `G`
is applied,

```
H^q(G (L^{•, •})_{•}) ≅ G (H^q(L^{•, •}))_{•},
```

an isomorphism of bicomplexes in the two remaining indices `(i₁, i₂)`; and after integrating
those two indices,

```
H^q(Tot₁₂(G (L^{•, •, •}))) ≅ Tot(G (H^q(L^{•, •}))).
```

## Main definitions

* `HomologicalComplex₃.homologyIsoOfComplexValuedFunctor`: homology in the third index of
  `ofComplexValuedFunctor G L` is `G` applied to the homology of `L`.
* `HomologicalComplex₃.int₁₂HomologyIsoOfComplexValuedFunctor`: the same after integrating the
  first two indices of a tricomplex with finite support.

## Main results

* `HomologicalComplex.mapHomologyIso_hom_naturality_natTrans`: the comparison
  `H^q(F(K)) ≅ F(H^q(K))` for a functor preserving homology is natural in the functor.

## References

* [Stacks Project, Tag 08BI](https://stacks.math.columbia.edu/tag/08BI)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace HomologicalComplex

/-- The comparison `H^q(F(K)) ≅ F(H^q(K))` is natural in the functor: a natural
transformation `α : F ⟶ F'` of additive functors preserving homology induces a morphism of
complexes `F(K) ⟶ F'(K)`, and the resulting square of comparisons commutes. -/
lemma mapHomologyIso_hom_naturality_natTrans {ι : Type*} {c : ComplexShape ι} {C D : Type*}
    [Category* C] [Category* D] [Preadditive C] [Preadditive D] [CategoryWithHomology C]
    [CategoryWithHomology D] {F F' : C ⥤ D} [F.Additive] [F.PreservesHomology] [F'.Additive]
    [F'.PreservesHomology] (α : F ⟶ F') (K : HomologicalComplex C c) (q : ι) :
    homologyMap ((NatTrans.mapHomologicalComplex α c).app K) q ≫
        ((K.sc q).mapHomologyIso F').hom =
      ((K.sc q).mapHomologyIso F).hom ≫ α.app (K.homology q) := by
  have h : ((K.sc q).mapHomologyIso F).hom ≫ α.app (K.sc q).homology =
      ShortComplex.homologyMap ((K.sc q).mapNatTrans α) ≫ ((K.sc q).mapHomologyIso F').hom := by
    rw [_root_.CategoryTheory.NatTrans.app_homology α (K.sc q), Iso.hom_inv_id_assoc]
  exact h.symm

end HomologicalComplex

namespace HomologicalComplex₃

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D] {I₁ I₂ I₃ : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}
  (G : C ⥤ HomologicalComplex D c₁) [G.Additive]
  [∀ i₁ : I₁, (G ⋙ HomologicalComplex.eval D c₁ i₁).PreservesHomology]
  (L : HomologicalComplex₂ C c₂ c₃) (q : I₃)

/-- The complex `i₂ ↦ H^q(L^{i₂, •})` of the homology objects of the rows of a bicomplex. -/
abbrev rowHomology : HomologicalComplex C c₂ :=
  ((HomologicalComplex.homologyFunctor C c₃ q).mapHomologicalComplex c₂).obj L

/-- The comparison in bidegree `(i₁, i₂)`: homology in the third index of
`ofComplexValuedFunctor G L` is `G` applied to the homology of the row of `L` at `i₂`. -/
def homologyXXIsoOfComplexValuedFunctor (i₁ : I₁) (i₂ : I₂) :
    ((HomologicalComplex₂.TotalMap.mapBicomplex (HomologicalComplex.homologyFunctor D c₃ q)
        (asBicomplex (ofComplexValuedFunctor G L))).X i₁).X i₂ ≅
      ((G.obj ((rowHomology L q).X i₂)).X i₁) :=
  ((L.X i₂).sc q).mapHomologyIso (G ⋙ HomologicalComplex.eval D c₁ i₁)

/-- Homology in the third index of `ofComplexValuedFunctor G L` is `G` applied to the homology
of `L`. -/
def homologyIsoOfComplexValuedFunctor :
    HomologicalComplex₂.TotalMap.mapBicomplex (HomologicalComplex.homologyFunctor D c₃ q)
        (asBicomplex (ofComplexValuedFunctor G L)) ≅
      HomologicalComplex₂.flip ((G.mapHomologicalComplex c₂).obj (rowHomology L q)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i₁ => HomologicalComplex.Hom.isoOfComponents
      (fun i₂ => homologyXXIsoOfComplexValuedFunctor G L q i₁ i₂)
      (fun i₂ i₂' _ => (ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor C c₃ q).map (L.d i₂ i₂'))
        (G ⋙ HomologicalComplex.eval D c₁ i₁)).symm))
    (fun i₁ i₁' _ => HomologicalComplex.hom_ext _ _ (fun i₂ =>
      (HomologicalComplex.mapHomologyIso_hom_naturality_natTrans
        (Functor.whiskerLeft G (HomologicalComplex.dNatTrans D c₁ i₁ i₁')) (L.X i₂) q).symm))

section Int12

variable {I₁₂ : Type*} (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂] [TotalComplexShape c₁ c₂ c₁₂]
  [(ofComplexValuedFunctor G L).HasInt₁₂ c₁₂]
  [(HomologicalComplex₂.TotalMap.mapBicomplex (HomologicalComplex.homologyFunctor D c₃ q)
    (asBicomplex (ofComplexValuedFunctor G L))).HasTotal c₁₂]
  [(HomologicalComplex₂.flip ((G.mapHomologicalComplex c₂).obj (rowHomology L q))).HasTotal c₁₂]

/-- Homology in the third index of `Tot₁₂(ofComplexValuedFunctor G L)` is the total complex of
`G` applied to the homology of `L`, when each term of `Tot₁₂` has finitely many nonzero
summands. -/
def int₁₂HomologyIsoOfComplexValuedFunctor
    (hfin : ∀ i₁₂ : I₁₂, {p : I₁ × I₂ | ComplexShape.π c₁ c₂ c₁₂ p = i₁₂ ∧
      ¬ IsZero (((ofComplexValuedFunctor G L).X p.1).X p.2)}.Finite) :
    ((HomologicalComplex.homologyFunctor D c₃ q).mapHomologicalComplex c₁₂).obj
        ((ofComplexValuedFunctor G L).int₁₂ c₁₂) ≅
      (HomologicalComplex₂.flip ((G.mapHomologicalComplex c₂).obj (rowHomology L q))).total c₁₂ :=
  (int₁₂MapIsoOfFinite (ofComplexValuedFunctor G L) c₁₂
      (HomologicalComplex.homologyFunctor D c₃ q) hfin).symm ≪≫
    HomologicalComplex₂.total.mapIso (homologyIsoOfComplexValuedFunctor G L q) c₁₂

end Int12

end HomologicalComplex₃

end
