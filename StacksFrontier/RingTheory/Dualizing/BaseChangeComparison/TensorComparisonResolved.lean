module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonSquareOfProjection
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraBaseChangeResolution
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeUnitChainValue
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.RestrictionIsoComputation
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionSquareMateUnitSquare
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonFactors
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeMorEqLax
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonChainIdentity

/-!
# The tensor comparison of [stacks 0E2A] at resolved projection formulas

For a K-flat resolution `p : P ⟶ A[0]` of the algebra, the projection formula of
`Dualizing.resolvedProjectionFormula` has explicit components at K-flat complexes, and so has the
one over `R'` built from the base-changed resolution `R' ⊗_R P ⟶ (A ⊗_R R')[0]`.  This file
evaluates the composite comparison of `Dualizing.TensorComparisonCompatibilityOf` at the class
of a K-flat complex `K` with these two projection formulas, reducing it to a chain-level identity
of complexes of `R'`-modules.

## Main results

* `Dualizing.tensorComparisonResolved_source` — the first half of the composite, after the
  base change of the derived tensor product, as a class of chain maps.
* `Dualizing.tensorComparisonResolved_target` — the second half, through the square
  isomorphism and the projection formula over `R'`.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars CochainComplex.DerivedTensor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

universe uR uA uRp v

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

variable (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
  (hP : CochainComplex.KFlat.{uR, max (max v uRp) uR uA} P)
  (p : P ⟶ algebraComplex.{max v uRp} (algebraMap R A)) [QuasiIso p]

section Abstract
variable {C : Type*} [Category C]
/-- A composite `n1 ≫ n2 ≫ μA ≫ l2 ≫ l3` in a category equals
`qe ≫ q2 ≫ q3 ≫ qτ ≫ invT ≫ r1`, given the commuting relations `H1`–`H11` among its factors. -/
theorem tcAssembly_source_half
    {X0 X1 S S' T1 T1' T2 T3 T3' E1 E3 B1 B2 B3 B4 G1 G2 : C}
    (n1 : X0 ⟶ X1) (n2 : X1 ⟶ S) (μA : S ⟶ T1) (l2 : T1 ⟶ T2) (l3 : T2 ⟶ T3)
    (m1 : X1 ⟶ S') (μP : S' ⟶ T1') (bcRtm : T1' ⟶ T1)
    (m2 : S' ⟶ X1) (d2 : X1 ⟶ X0) (qe : X0 ⟶ E1) (tkInv : E1 ⟶ T1')
    (bdTC : T1' ⟶ B1) (bk : B1 ⟶ B2) (bχ : B2 ⟶ B3) (bUf : B3 ⟶ B4) (bUa : B4 ⟶ T2)
    (invαg : E1 ⟶ B1)
    (θN : B4 ⟶ T3') (r1 : T3' ⟶ T3)
    (bUfh : B4 ⟶ B3) (αgN : B3 ⟶ G1) (qτ : G1 ⟶ G2) (invT : G2 ⟶ T3')
    (αgA : B2 ⟶ E3) (q3 : E3 ⟶ G1) (αgP : B1 ⟶ E1) (q2 : E1 ⟶ E3)
    (H1 : n2 ≫ μA = m1 ≫ μP ≫ bcRtm)
    (H2 : μP = m2 ≫ d2 ≫ qe ≫ tkInv)
    (H3 : n1 ≫ m1 ≫ m2 ≫ d2 = 𝟙 X0)
    (H4 : bcRtm ≫ l2 = bdTC ≫ bk ≫ bχ ≫ bUf ≫ bUa)
    (H5 : tkInv ≫ bdTC = invαg)
    (H6 : bUa ≫ l3 = θN ≫ r1)
    (H7 : θN = (bUfh ≫ αgN ≫ qτ) ≫ invT)
    (H8 : bUf ≫ bUfh = 𝟙 B3)
    (H9 : bχ ≫ αgN = αgA ≫ q3)
    (H10 : bk ≫ αgA = αgP ≫ q2)
    (H11 : invαg ≫ αgP = 𝟙 E1) :
    n1 ≫ n2 ≫ μA ≫ l2 ≫ l3 = qe ≫ q2 ≫ q3 ≫ qτ ≫ invT ≫ r1 := by
  rw [reassoc_of% H1, H2]
  simp only [Category.assoc]
  rw [reassoc_of% H3, reassoc_of% H4, reassoc_of% H5, H6, H7]
  simp only [Category.assoc]
  rw [reassoc_of% H8, reassoc_of% H9, reassoc_of% H10, reassoc_of% H11]

/-- A composite `r1 ≫ l4 ≫ l5 ≫ o1 ≫ o2 ≫ o3` in a category equals `c1 ≫ u1 ≫ q5 ≫ s3`,
given the commuting relations `H14`–`H21` among its factors. -/
theorem tcAssembly_target_half
    {T3 T3' T4 T5 X0 X1 Y3 Z1 Z1' Z2 Z3 W1 V1 G2 : C}
    (r1 : T3' ⟶ T3) (l4 : T3 ⟶ T4) (l5 : T4 ⟶ T5) (o1 : T5 ⟶ X1) (o2 : X1 ⟶ X0)
    (o3 : X0 ⟶ Y3)
    (c1 : T3' ⟶ Z1) (cl : Z1 ⟶ Z1') (ci : Z1' ⟶ T4) (fK : T4 ⟶ Z3)
    (pK' : Z3 ⟶ W1) (t1 : W1 ⟶ T5)
    (s1 : Z3 ⟶ Z2) (s2 : Z2 ⟶ V1) (s3 : V1 ⟶ Y3) (s4 : Y3 ⟶ X0) (s5 : X0 ⟶ X1)
    (s6 : X1 ⟶ W1) (cri : Z1' ⟶ Z2) (u1 : Z1 ⟶ G2) (q5 : G2 ⟶ V1)
    (H14 : r1 ≫ l4 = c1 ≫ cl ≫ ci)
    (H15 : l5 = fK ≫ pK' ≫ t1)
    (H16 : pK' = s1 ≫ s2 ≫ s3 ≫ s4 ≫ s5 ≫ s6)
    (H17 : ci ≫ fK ≫ s1 = cri)
    (H18 : s6 ≫ t1 ≫ o1 = 𝟙 X1)
    (H19 : s5 ≫ o2 = 𝟙 X0)
    (H20 : s4 ≫ o3 = 𝟙 Y3)
    (H21 : cl ≫ cri ≫ s2 = u1 ≫ q5) :
    r1 ≫ l4 ≫ l5 ≫ o1 ≫ o2 ≫ o3 = c1 ≫ u1 ≫ q5 ≫ s3 := by
  rw [reassoc_of% H14, H15, H16]
  simp only [Category.assoc]
  rw [reassoc_of% H18, reassoc_of% H19, H20, reassoc_of% H17, reassoc_of% H21]
  simp only [Category.comp_id]

/-- Two composites with the shapes of `tcAssembly_source_half` and `tcAssembly_target_half`, glued
along `r1` and with `invT ≫ c1 ≫ u1 = 𝟙`, give
`n1 ≫ n2 ≫ μA ≫ (l2 ≫ l3 ≫ l4 ≫ l5) ≫ o1 ≫ o2 ≫ o3 = qe ≫ q2 ≫ q3 ≫ qτ ≫ q5 ≫ s3`. -/
theorem tcAssembly_full
    {X0 X1 S T1 T2 T3 T3' E1 E3 G1 G2 T4 T5 Y3 Z1 V1 : C}
    (n1 : X0 ⟶ X1) (n2 : X1 ⟶ S) (μA : S ⟶ T1) (l2 : T1 ⟶ T2) (l3 : T2 ⟶ T3)
    (l4 : T3 ⟶ T4) (l5 : T4 ⟶ T5) (o1 : T5 ⟶ X1) (o2 : X1 ⟶ X0) (o3 : X0 ⟶ Y3)
    (qe : X0 ⟶ E1) (q2 : E1 ⟶ E3) (q3 : E3 ⟶ G1) (qτ : G1 ⟶ G2) (invT : G2 ⟶ T3')
    (r1 : T3' ⟶ T3) (c1 : T3' ⟶ Z1) (u1 : Z1 ⟶ G2) (q5 : G2 ⟶ V1) (s3 : V1 ⟶ Y3)
    (Hs : n1 ≫ n2 ≫ μA ≫ l2 ≫ l3 = qe ≫ q2 ≫ q3 ≫ qτ ≫ invT ≫ r1)
    (Ht : r1 ≫ l4 ≫ l5 ≫ o1 ≫ o2 ≫ o3 = c1 ≫ u1 ≫ q5 ≫ s3)
    (H22 : invT ≫ c1 ≫ u1 = 𝟙 G2) :
    n1 ≫ n2 ≫ μA ≫ (l2 ≫ l3 ≫ l4 ≫ l5) ≫ o1 ≫ o2 ≫ o3 = qe ≫ q2 ≫ q3 ≫ qτ ≫ q5 ≫ s3 := by
  have : n1 ≫ n2 ≫ μA ≫ (l2 ≫ l3 ≫ l4 ≫ l5) ≫ o1 ≫ o2 ≫ o3 =
      (n1 ≫ n2 ≫ μA ≫ l2 ≫ l3) ≫ l4 ≫ l5 ≫ o1 ≫ o2 ≫ o3 := by simp only [Category.assoc]
  rw [this, Hs]
  simp only [Category.assoc]
  rw [Ht, reassoc_of% H22]

/-- If `n2 ≫ g ≫ o1 = 𝟙` and `n1 ≫ o2 = 𝟙`, then `n1 ≫ n2 ≫ g ≫ o1 ≫ o2 ≫ o3 = o3`. -/
theorem tcAssembly_rhs
    {X0 X1 S T5 Y3 : C} (n1 : X0 ⟶ X1) (n2 : X1 ⟶ S) (g : S ⟶ T5) (o1 : T5 ⟶ X1)
    (o2 : X1 ⟶ X0) (o3 : X0 ⟶ Y3) (H23 : n2 ≫ g ≫ o1 = 𝟙 X1) (H24 : n1 ≫ o2 = 𝟙 X0) :
    n1 ≫ n2 ≫ g ≫ o1 ≫ o2 ≫ o3 = o3 := by
  rw [reassoc_of% H23, reassoc_of% H24]

/-- If `u ≫ u' = 𝟙`, `σ ≫ cR = cL` with `cR` an isomorphism, and `cL = u' ≫ a ≫ b`, then
`u ≫ σ = a ≫ b ≫ inv cR`. -/
theorem tcAssembly_conj {X X' Y W W' : C} (u : X ⟶ X') (u' : X' ⟶ X) (hu : u ≫ u' = 𝟙 X)
    (σ : X' ⟶ Y) (cR : Y ⟶ W) [IsIso cR] (cL : X' ⟶ W) (a : X ⟶ W') (b : W' ⟶ W)
    (hσc : σ ≫ cR = cL) (hcL : cL = u' ≫ a ≫ b) :
    u ≫ σ = a ≫ b ≫ inv cR := by
  rw [← cancel_mono cR, Category.assoc, Category.assoc, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, hσc, hcL, ← Category.assoc u u', hu, Category.id_comp]

/-- If an isomorphism `c` factors as `x ≫ y ≫ z` and `z ≫ zi = 𝟙`, then `inv c ≫ x ≫ y = zi`. -/
theorem tcAssembly_inv {X Y Z W : C} (c : X ⟶ W) [hc : IsIso c] (x : X ⟶ Y) (y : Y ⟶ Z)
    (z : Z ⟶ W) (zi : W ⟶ Z) (h : c = x ≫ y ≫ z) (hz : z ≫ zi = 𝟙 Z) :
    inv c ≫ x ≫ y = zi := by
  have : inv c ≫ x ≫ y = inv c ≫ (x ≫ y ≫ z) ≫ zi := by
    simp only [Category.assoc]; rw [hz, Category.comp_id]
  rw [this, ← h, IsIso.inv_hom_id_assoc]

/-- If `a ≫ b = c ≫ m` and `m ≫ mi = 𝟙`, then `c = a ≫ b ≫ mi`. -/
theorem tcAssembly_nat {X Y Z W : C} (c : X ⟶ Y) (a : X ⟶ Z) (b : Z ⟶ W) (m : Y ⟶ W)
    (mi : W ⟶ Y) (hm : m ≫ mi = 𝟙 Y) (h : a ≫ b = c ≫ m) : c = a ≫ b ≫ mi := by
  rw [reassoc_of% h, hm, Category.comp_id]

/-- If `c ≫ q' = m ≫ θ` with `c` and `q'` isomorphisms, then `(inv c ≫ m) ≫ θ ≫ inv q' = 𝟙`,
written with `bi = m` and `bh = inv q'`. -/
theorem tcAssembly_alg {X Y Z W : C} (c : X ⟶ Y) [IsIso c] (q' : Y ⟶ W) [hq : IsIso q']
    (m : X ⟶ Z) (θ : Z ⟶ W) (bi : X ⟶ Z) (bh : W ⟶ Y) (h : c ≫ q' = m ≫ θ) (hbi : bi = m)
    (hbh : bh = inv q') : (inv c ≫ bi) ≫ θ ≫ bh = 𝟙 Y := by
  rw [hbi, hbh, Category.assoc, ← Category.assoc m, ← h]
  simp

/-- Split monomorphisms `n1`, `n2` on the left and split epimorphisms `o1`, `o2`, `o3` on the right
cancel: an equality `n1 ≫ n2 ≫ a1 ≫ a2 ≫ o1 ≫ o2 ≫ o3 = n1 ≫ n2 ≫ b ≫ o1 ≫ o2 ≫ o3` implies
`a1 ≫ a2 = b`. -/
theorem tcAssembly_cancel {X0 X1 S T T5 Y1 Y2 Y3 : C} (n1 : X0 ⟶ X1) (n2 : X1 ⟶ S)
    (a1 : S ⟶ T) (a2 : T ⟶ T5) (b : S ⟶ T5) (o1 : T5 ⟶ Y1) (o2 : Y1 ⟶ Y2) (o3 : Y2 ⟶ Y3)
    (m1 : X1 ⟶ X0) (m2 : S ⟶ X1) (h1 : m1 ≫ n1 = 𝟙 X1) (h2 : m2 ≫ n2 = 𝟙 S)
    (k1 : Y1 ⟶ T5) (k2 : Y2 ⟶ Y1) (k3 : Y3 ⟶ Y2) (j1 : o1 ≫ k1 = 𝟙 T5) (j2 : o2 ≫ k2 = 𝟙 Y1)
    (j3 : o3 ≫ k3 = 𝟙 Y2)
    (h : n1 ≫ n2 ≫ a1 ≫ a2 ≫ o1 ≫ o2 ≫ o3 = n1 ≫ n2 ≫ b ≫ o1 ≫ o2 ≫ o3) : a1 ≫ a2 = b := by
  have := congrArg (fun t => m2 ≫ m1 ≫ t ≫ k3 ≫ k2 ≫ k1) h
  simp only [Category.assoc] at this
  simpa only [reassoc_of% h1, reassoc_of% h2, j1, reassoc_of% j2, reassoc_of% j3,
    Category.comp_id, Category.id_comp] using this

/-- For functors `H : B ⥤ D` and `G : D ⥤ E`, the composite of the images under `G` of
`x`, `H.map y`, `H.map y'`, `z`, `w`, `t` is `G.map (x ≫ H.map (y ≫ y') ≫ z ≫ w ≫ t)`. -/
theorem tcAssembly_map_chain {B D E : Type*} [Category B] [Category D] [Category E]
    (G : D ⥤ E) (H : B ⥤ D) {a0 a4 a5 a6 : D} {b1 b2 b3 : B}
    (x : a0 ⟶ H.obj b1) (y : b1 ⟶ b2) (y' : b2 ⟶ b3) (z : H.obj b3 ⟶ a4) (w : a4 ⟶ a5)
    (t : a5 ⟶ a6) :
    G.map x ≫ G.map (H.map y) ≫ G.map (H.map y') ≫ G.map z ≫ G.map w ≫ G.map t =
      G.map (x ≫ H.map (y ≫ y') ≫ z ≫ w ≫ t) := by
  simp only [Functor.map_comp, Category.assoc]

end Abstract

/-- A functor on a product category sends a morphism `f` and a morphism `g` back, whose components
compose to identities, to a composite equal to the identity. -/
private theorem map_prod_comp_eq_id {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C × D ⥤ E) {X Y : C × D} (f : X ⟶ Y) (g : Y ⟶ X) (h₁ : f.1 ≫ g.1 = 𝟙 X.1)
    (h₂ : f.2 ≫ g.2 = 𝟙 X.2) : F.map f ≫ F.map g = 𝟙 _ := by
  rw [← F.map_comp, show f ≫ g = 𝟙 X from Prod.ext h₁ h₂, F.map_id]

include hTor hA hR in
/-- The base-changed resolution is a quasi-isomorphism (instance form). -/
theorem quasiIso_baseChangeResolution' (hP : CochainComplex.KFlat.{uR, max v uA uRp} P) :
    QuasiIso (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA
      comparisonA P p) :=
  quasiIso_baseChangeResolution.{uR, uA, uRp, v} hTor baseChangeR comparisonR baseChangeA
    comparisonA P p hP

set_option linter.checkUnivs false in
/-- The K-flatness of the base-changed resolution. -/
theorem kFlat_baseChangeResolution (hP : CochainComplex.KFlat.{uR, max v uA uRp} P) :
    CochainComplex.KFlat.{uRp, max (max v uR) uRp (max uA uRp)}
      (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{uR, uRp, max v uA}
    (algebraMap R R') P hP


include hTor hf hA hR hP p in
/-- **The source half of the tensor comparison at a K-flat complex.**  Granted the value of the
base change of the derived tensor product at the K-flat pair `(K, P)` through a tensor base-change
isomorphism `e` of total complexes, the composite of that base change at `A`, the inverse of the
resolved projection formula over `R`, and the inverse of the restriction isomorphism, is the
class of an explicit chain map followed by the inverses of the comparison morphisms over `A`. -/
theorem tensorComparisonResolved_source (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max (max v uRp) uR uA} K)
    [IsIso (comparisonR.app K)] [IsIso (comparisonR.app P)] [IsIso (alphaf.app K)]
    [IsIso (comparisonA.app (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))]
    (hFL : CochainComplex.KFlat.{uRp, max v uR uA uRp}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (e : tensorComplex.{uRp, max v uR uA uRp}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj (tensorComplex.{uR, max (max v uRp) uR uA} K P))
    (hval : derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj P) =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          ((CategoryTheory.Prod.mkHom (comparisonR.app K) (comparisonR.app P)) :
            (baseChangeR.obj (DerivedCategory.Q.obj K), baseChangeR.obj (DerivedCategory.Q.obj P)) ⟶
            (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
                DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        (derivedTensor_comparison.{uRp, max v uR uA uRp} R'
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hFL).hom ≫
          DerivedCategory.Q.map e.hom ≫
            (Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uRp, max v uA}
              (algebraMap R R') baseChangeR comparisonR K P hK hP).inv) :
    (derivedTensor_comparison.{uRp, max v uR uA uRp} R'
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hFL).inv ≫
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        ((CategoryTheory.inv (comparisonR.app K),
          CategoryTheory.inv (comparisonR.app P) ≫
            baseChangeR.map (algebraResolutionIso.{max v uRp} (algebraMap R A) P p).inv) :
          (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
              DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶
          (baseChangeR.obj (DerivedCategory.Q.obj K),
            baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
      derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
        (DerivedCategory.Q.obj K) (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
      baseChangeR.map ((resolvedProjectionFormula.{max v uRp} (algebraMap R A) Ff alphaf P
          hP p).inv.app
        (DerivedCategory.Q.obj K)) ≫
      (restrictionBaseChangeIsoGeneral.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR baseChangeA
        comparisonA hA).inv.app ((DerivedCategory.Q ⋙ Ff).obj K) =
    DerivedCategory.Q.map e.hom ≫
      DerivedCategory.Q.map (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max (max v uRp) uR uA} R)
            (ComplexShape.up ℤ))) ≫
      DerivedCategory.Q.map (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (RingTheory.TorIndependence.derivedBaseChangeComparison
            (algebraMap R A) (algebraMap R R')
            (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
            ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
              (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
            baseChangeR baseChangeA comparisonR comparisonA).1
          (ComplexShape.up ℤ)).app (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      CategoryTheory.inv
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R' (TensorProduct R A R'))).mapDerivedCategory.map
              (comparisonA.app (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
            (ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R' (TensorProduct R A R'))).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
                (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj
                      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
      (baseChangeA ⋙ (ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
            A R').toRingHom).mapDerivedCategory).map
          (CategoryTheory.inv (alphaf.app K)) := by
  -- H1
  have H1 : (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        ((CategoryTheory.inv (comparisonR.app K),
          CategoryTheory.inv (comparisonR.app P) ≫
            baseChangeR.map (algebraResolutionIso.{max v uRp} (algebraMap R A) P p).inv) :
          (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
            DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶
          (baseChangeR.obj (DerivedCategory.Q.obj K),
            baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
      derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
        (DerivedCategory.Q.obj K) (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        ((CategoryTheory.inv (comparisonR.app K), CategoryTheory.inv (comparisonR.app P)) :
          (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
            DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶
          (baseChangeR.obj (DerivedCategory.Q.obj K), baseChangeR.obj (DerivedCategory.Q.obj P))) ≫
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj P) ≫
        baseChangeR.map ((derivedHomAdjunctionOverRing.{uR, max v uR uA uRp,
          max v uR uA uRp + 1} R).tensor.map
          ((𝟙 (DerivedCategory.Q.obj K),
              (algebraResolutionIso.{max v uRp} (algebraMap R A) P p).inv) :
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
              (DerivedCategory.Q.obj K, derivedAlgebraSingle.{uR, uA, max v uRp}
                  (algebraMap R A)))) := by
    have hn := derivedTensorBaseChange_naturality.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
      comparisonR (𝟙 (DerivedCategory.Q.obj K))
          (algebraResolutionIso.{max v uRp} (algebraMap R A) P p).inv
    rw [CategoryTheory.Functor.map_id] at hn
    rw [← hn, ← Category.assoc]
    congr 1
    rw [← Functor.map_comp]
    exact congrArg _ (Prod.ext (Category.comp_id _).symm rfl)
  have H2 := hval
  have H3 : (derivedTensor_comparison.{uRp, max v uR uA uRp} R'
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hFL).inv ≫
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        ((CategoryTheory.inv (comparisonR.app K), CategoryTheory.inv (comparisonR.app P)) :
          (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
            DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶
          (baseChangeR.obj (DerivedCategory.Q.obj K), baseChangeR.obj (DerivedCategory.Q.obj P))) ≫
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        ((CategoryTheory.Prod.mkHom (comparisonR.app K) (comparisonR.app P)) :
          (baseChangeR.obj (DerivedCategory.Q.obj K), baseChangeR.obj (DerivedCategory.Q.obj P)) ⟶
          (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
            DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
      (derivedTensor_comparison.{uRp, max v uR uA uRp} R'
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hFL).hom =
      𝟙 _ := by
    rw [← Functor.map_comp_assoc]
    have h : ((CategoryTheory.inv (comparisonR.app K), CategoryTheory.inv (comparisonR.app P)) :
          (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
            DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶
          (baseChangeR.obj (DerivedCategory.Q.obj K), baseChangeR.obj (DerivedCategory.Q.obj P))) ≫
        CategoryTheory.Prod.mkHom (comparisonR.app K) (comparisonR.app P) = 𝟙 _ :=
      Prod.ext (IsIso.inv_hom_id _) (IsIso.inv_hom_id _)
    rw [h, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  -- the projection formula over `R`, inverted
  have hpf : ((resolvedProjectionFormula.{max v uRp} (algebraMap R A) Ff alphaf P hP p).app
      (DerivedCategory.Q.obj K)) =
      resolvedProjectionComponent.{max v uRp} (algebraMap R A) Ff alphaf P hP p K hK :=
    Iso.ext (resolvedProjectionFormula_hom_app.{max v uRp} (algebraMap R A) Ff alphaf P hP p K hK)
  have H4 : baseChangeR.map ((derivedHomAdjunctionOverRing.{uR, max v uR uA uRp,
          max v uR uA uRp + 1} R).tensor.map
          ((𝟙 (DerivedCategory.Q.obj K),
              (algebraResolutionIso.{max v uRp} (algebraMap R A) P p).inv) :
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
              (DerivedCategory.Q.obj K, derivedAlgebraSingle.{uR, uA, max v uRp}
                  (algebraMap R A)))) ≫
        baseChangeR.map
            ((resolvedProjectionFormula.{max v uRp} (algebraMap R A) Ff alphaf P hP p).inv.app
          (DerivedCategory.Q.obj K)) =
      baseChangeR.map (derivedTensor_comparison.{uR, max (max v uRp) uR uA} R K P hP).hom ≫
        baseChangeR.map (kFlatTensorResolutionIso.{max v uRp} (algebraMap R A) P p K hK).hom ≫
        baseChangeR.map
            (DerivedCategory.Q.map (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv) ≫
        baseChangeR.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ≫
        baseChangeR.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory.map
          (CategoryTheory.inv (alphaf.app K))) := by
    have hinv : (resolvedProjectionFormula.{max v uRp} (algebraMap R A) Ff alphaf P hP p).inv.app
        (DerivedCategory.Q.obj K) =
        (resolvedProjectionComponent.{max v uRp} (algebraMap R A) Ff alphaf P hP p K hK).inv := by
      rw [← hpf]; rfl
    have hin : (derivedHomAdjunctionOverRing.{uR, max v uR uA uRp,
          max v uR uA uRp + 1} R).tensor.map
          ((𝟙 (DerivedCategory.Q.obj K),
              (algebraResolutionIso.{max v uRp} (algebraMap R A) P p).inv) :
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
              (DerivedCategory.Q.obj K, derivedAlgebraSingle.{uR, uA, max v uRp}
                  (algebraMap R A))) ≫
          (resolvedProjectionComponent.{max v uRp} (algebraMap R A) Ff alphaf P hP p K hK).inv =
        (derivedTensor_comparison.{uR, max (max v uRp) uR uA} R K P hP).hom ≫
        (kFlatTensorResolutionIso.{max v uRp} (algebraMap R A) P p K hK).hom ≫
        DerivedCategory.Q.map (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory.map
          (CategoryTheory.inv (alphaf.app K)) := by
      refine (congrArg (fun z => _ ≫ z) (resolvedProjectionComponent_inv.{max v uRp}
        (algebraMap R A) Ff alphaf P hP p K hK)).trans ?_
      exact Iso.hom_inv_id_assoc
        ((derivedHomAdjunctionOverRing.{uR, max v uR uA uRp, max v uR uA uRp + 1} R).tensor.mapIso
          (Iso.prod (Iso.refl (DerivedCategory.Q.obj K))
            (algebraResolutionIso.{max v uRp} (algebraMap R A) P p).symm)) _
    refine (baseChangeR.map_comp _ _).symm.trans ?_
    refine (congrArg baseChangeR.map (hinv ▸ hin)).trans ?_
    simp only [Functor.map_comp]
  -- the comparison of [stacks 0661] at `N = A ⊗_R K`
  have hN : CochainComplex.KFlat.{uA, max v uR uRp}
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
    CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{uR, uA, max v uRp}
      (algebraMap R A) K hK
  have := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uA, max uA uRp,
    max v uR} (algebraMap A (TensorProduct R A R')) baseChangeA comparisonA _ hN
  have H6 := (restrictionBaseChangeIsoGeneral.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
    baseChangeA comparisonA hA).inv.naturality (CategoryTheory.inv (alphaf.app K))
  have H7 := restrictionBaseChangeIsoGeneral_inv_app_q_obj.{uR, uA, uRp, v} hTor baseChangeR
    comparisonR baseChangeA comparisonA
    (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
  have H8 : baseChangeR.map ((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R A)).mapDerivedCategoryFactors.inv.app
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) ≫
      baseChangeR.map ((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R A)).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have H9 := comparisonR.naturality (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv
  have H10 := comparisonR.naturality (HomologicalComplex.mapBifunctorMap (𝟙 K) p
    (moduleTensor.{uR, max (max v uRp) uR uA} R) (ComplexShape.up ℤ))
  have H11 : ((Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uRp, max v uA}
        (algebraMap R R') baseChangeR comparisonR K P hK hP).inv ≫
      baseChangeR.map (derivedTensor_comparison.{uR, max (max v uRp) uR uA} R K P hP).hom) ≫
      comparisonR.app (tensorComplex.{uR, max (max v uRp) uR uA} K P) = 𝟙 _ := by
    rw [Category.assoc]
    exact Iso.inv_hom_id _
  exact tcAssembly_source_half _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    H1 H2 H3 H4 rfl H6 H7 H8 H9 H10 H11

include hf hA hR hi p in
omit [QuasiIso p] in
/-- **The target half of the tensor comparison at a K-flat complex.**  Through the square
isomorphism of the four derived extensions of scalars and the resolved projection formula over
`R'`, followed by the K-flat description of the derived tensor product over `R'`, the composite is
the comparison morphism over `A ⊗_R R'` followed by the class of an explicit chain map. -/
theorem tensorComparisonResolved_target (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max (max v uRp) uR uA} K)
    [IsIso (comparisonR.app K)] [IsIso (alphaf.app K)]
    (hL : CochainComplex.KFlat.{uRp, max (max v uR) uRp (max uA uRp)}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (hP' : CochainComplex.KFlat.{uRp, max (max v uR) uRp (max uA uRp)}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    [QuasiIso (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
        P p)] :
    (baseChangeA ⋙ (ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
        A R').toRingHom).mapDerivedCategory).map (CategoryTheory.inv (alphaf.app K)) ≫
      (ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
          A R').toRingHom).mapDerivedCategory.map
          ((derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR
        comparisonR Fi alphai).hom.app (DerivedCategory.Q.obj K)) ≫
      (resolvedProjectionFormula.{max v uR}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hP'
          (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
          P p)).hom.app (baseChangeR.obj (DerivedCategory.Q.obj K)) ≫
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        (((comparisonR.app K, (algebraResolutionIso.{max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
            P p)).hom) :
          (baseChangeR.obj (DerivedCategory.Q.obj K),
              (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)) ⟶
            (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
                DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ≫
      (derivedTensor_comparison.{uRp, max (max v uR) uRp (max uA uRp)} R'
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hP').hom ≫
      (kFlatTensorResolutionIso.{max v uR}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
          P p) (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) hL).hom =
    (ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
        A R').toRingHom).mapDerivedCategory.map
        (comparisonA.app (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      (ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
          A R').toRingHom).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
            (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
          A R').toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (((NatTrans.mapHomologicalComplex
          (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
            (algebraMap R A) (algebraMap A (TensorProduct R A R'))
                (algebraMap R (TensorProduct R A R'))
            algebraMap_tensorProduct_comp_left) (ComplexShape.up ℤ)).app K) ≫
                ((NatIso.mapHomologicalComplex
          (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
          (ComplexShape.up ℤ)).app K).inv)) ≫
      DerivedCategory.Q.map (extendRestrictComplexIso.{max v uR}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom := by
  have hcR := compComparisonOfEq_app_eq_right.{uR, uA, uRp, v} baseChangeR comparisonR Fi alphai
    (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right K
  have hcL := compComparisonOfEq_app_eq_left.{uR, uA, uRp, v} baseChangeA comparisonA Ff alphaf
    (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_left K
  have hσc := derivedBaseChangeSquareIso_hom_app_comp_comparison.{uR, uA, uRp, v} Ff alphaf
    baseChangeA comparisonA baseChangeR comparisonR Fi alphai K
  have hcc := isIso_compComparisonOfEq_right_app_of_kFlat.{uR, uA, uRp, v} baseChangeR comparisonR
    Fi alphai K hK
  have hσ := tcAssembly_conj _ _ (by rw [← Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id]) _ _ _ _ _ hσc hcL
  have H14 := ((ModuleCat.restrictScalars.{max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
      R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map_comp _ _).symm.trans
      ((congrArg (ModuleCat.restrictScalars.{max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
      R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map hσ).trans
    (((ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map_comp _ _).trans
        (congrArg (fun z => _ ≫ z) ((ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map_comp _ _))))
  have H15 := tcAssembly_nat _ _ _ _ _ (by rw [← Functor.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id]) ((resolvedProjectionFormula.{max v uR}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hP'
          (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P
          p)).hom.naturality (comparisonR.app K))
  have H16 := (resolvedProjectionFormula_hom_app.{max v uR}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai
      _ hP' (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P
          p) _ hL).trans (resolvedProjectionComponent_hom.{max v uR}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai
      _ hP' (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P
          p) _ hL)
  have hz : DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uRp, max uA uRp, max v uA}
        (algebraMap R R')
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
      (ComplexShape.up ℤ)).app K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
                (ComplexShape.up ℤ)).app K).inv =
      𝟙 _ := by
    rw [← extendScalarsCompIsoOfEq_hom.{uR, uRp, max uA uRp, max v uA}]
    exact (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA}
          (algebraMap R R')
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
                (ComplexShape.up ℤ)).app K).hom_inv_id).trans
        (DerivedCategory.Q.map_id _))
  have h17c := tcAssembly_inv _ _ _ _ _ (hc := hcc) hcR hz
  have H17 := ((congrArg (fun z => _ ≫ z)
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
      R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map_comp _ _).symm).trans
    ((ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map_comp _ _).symm).trans
        (congrArg (ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map h17c)
  have H18 : (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1}
      R').tensor.map
        (((𝟙 (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)),
            (algebraResolutionIso.{max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P
            p)).inv) :
          (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
              DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶
            (DerivedCategory.Q.obj
                (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
                (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)))) ≫
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        (((CategoryTheory.inv (comparisonR.app K), 𝟙
            (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)) :
          (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
              (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)) ⟶
            (baseChangeR.obj (DerivedCategory.Q.obj K),
                (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)))) ≫
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        (((comparisonR.app K, (algebraResolutionIso.{max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P
            p)).hom) :
          (baseChangeR.obj (DerivedCategory.Q.obj K),
              (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)) ⟶
            (DerivedCategory.Q.obj
                (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
                DerivedCategory.Q.obj
                (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) = 𝟙 _ := by
    rw [← Functor.map_comp]
    refine map_prod_comp_eq_id _ _ _ ?_ ?_
    · exact (Category.id_comp _).trans (IsIso.inv_hom_id _)
    · exact (congrArg (fun z => _ ≫ z) (Category.id_comp _)).trans (Iso.inv_hom_id _)
  have H21 : (ModuleCat.restrictScalars.{max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
      R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
      (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
            (algebraMap R A) (algebraMap A (TensorProduct R A R'))
                (algebraMap R (TensorProduct R A R'))
            algebraMap_tensorProduct_comp_left) (ComplexShape.up ℤ)).app K)) ≫
                (ModuleCat.restrictScalars.{max v uR uA uRp}
                (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
                (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
          (ComplexShape.up ℤ)).app K).inv) ≫
      (ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      (ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
            (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (((NatTrans.mapHomologicalComplex
          (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
            (algebraMap R A) (algebraMap A (TensorProduct R A R'))
                (algebraMap R (TensorProduct R A R'))
            algebraMap_tensorProduct_comp_left) (ComplexShape.up ℤ)).app K) ≫
                ((NatIso.mapHomologicalComplex
          (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
          (ComplexShape.up ℤ)).app K).inv)) := by
    rw [← Category.assoc]
    exact (((ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map_comp _ _).symm.trans
        (congrArg (ModuleCat.restrictScalars.{max v uR uA uRp}
        (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
      (DerivedCategory.Q.map_comp _ _).symm) =≫ _).trans
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategoryFactors.hom.naturality _)
  exact tcAssembly_target_half _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14 H15 H16 H17 H18
    (Iso.inv_hom_id _) (Iso.inv_hom_id _) H21

include hTor hA hR in
/-- **The right-hand side of the tensor comparison at a K-flat complex.**  Conjugated by the same
isomorphisms as the two halves, the base change of the algebra is the class of the base-changed
resolution, by `Dualizing.comparisonR_app_comp_Q_map_baseChangeResolution`. -/
theorem tensorComparisonResolved_rhs (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    [IsIso (comparisonR.app K)] [IsIso (comparisonR.app P)]
    (hFL : CochainComplex.KFlat.{uRp, max v uR uA uRp}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (hL : CochainComplex.KFlat.{uRp, max (max v uR) uRp (max uA uRp)}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (hP' : CochainComplex.KFlat.{uRp, max (max v uR) uRp (max uA uRp)}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    [QuasiIso (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
        P p)] :
    (derivedTensor_comparison.{uRp, max v uR uA uRp} R'
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hFL).inv ≫
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        ((CategoryTheory.inv (comparisonR.app K),
          CategoryTheory.inv (comparisonR.app P) ≫ baseChangeR.map
              (algebraResolutionIso.{max v uRp} (algebraMap R A) P p).inv) :
          (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
              DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶
          (baseChangeR.obj (DerivedCategory.Q.obj K), baseChangeR.obj
              (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        ((𝟙 (baseChangeR.obj (DerivedCategory.Q.obj K)),
            (derivedBaseChangeAlgebraIso.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
            baseChangeA comparisonA hA).hom) :
          (baseChangeR.obj (DerivedCategory.Q.obj K), baseChangeR.obj
              (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
            (baseChangeR.obj (DerivedCategory.Q.obj K),
                (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom))) ≫
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        (((comparisonR.app K, (algebraResolutionIso.{max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
            P p)).hom) :
          (baseChangeR.obj (DerivedCategory.Q.obj K),
              (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)) ⟶
            (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
                DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ≫
      (derivedTensor_comparison.{uRp, max (max v uR) uRp (max uA uRp)} R'
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hP').hom ≫
      (kFlatTensorResolutionIso.{max v uR}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
          P p) (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) hL).hom =
    (kFlatTensorResolutionIso.{max v uR}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P p)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) hL).hom := by
  have hc := comparisonR_app_comp_Q_map_baseChangeResolution.{uR, uA, uRp, v} hTor baseChangeR
    comparisonR baseChangeA comparisonA P p
  have hq : IsIso (DerivedCategory.Q.map (baseChangeResolution.{uR, uA, uRp, v} baseChangeR
      comparisonR baseChangeA comparisonA P p)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr inferInstance
  refine tcAssembly_rhs _ _ _ _ _ _ ?_ (Iso.inv_hom_id _)
  rw [← Functor.map_comp]
  refine map_prod_comp_eq_id _ _ _ ?_ ?_
  · exact (congrArg (fun z => _ ≫ z) (Category.id_comp _)).trans (IsIso.inv_hom_id _)
  · exact tcAssembly_alg _ _ _ _ _ _ (hq := hq) hc
      (congrArg baseChangeR.map (Category.comp_id (DerivedCategory.Q.map p)))
      (Category.id_comp _)

include hTor hf hA hR hi hP p in
/-- **The tensor comparison of [stacks 0E2A] at a K-flat complex, from the chain-level identity.**
With the resolved projection formulas over `R` and over `R'`, the compatibility
`Dualizing.TensorComparisonCompatibilityOf` holds at the class of a K-flat complex `K` as soon as
the base change of the derived tensor product at `(K, P)` is computed by a tensor base-change
isomorphism `e` of total complexes, and `e` carries the chain map of the two halves onto
`R' ⊗_R K ⊗ p'`. -/
theorem tensorComparisonCompatibilityOf_resolved_of_chain
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max (max v uRp) uR uA} K)
    (hP' : CochainComplex.KFlat.{uRp, max (max v uR) uRp (max uA uRp)}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    [QuasiIso (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
        P p)]
    (e : tensorComplex.{uRp, max v uR uA uRp}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj (tensorComplex.{uR, max (max v uRp) uR uA} K P))
    (hval : derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj P) =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          ((CategoryTheory.Prod.mkHom (comparisonR.app K) (comparisonR.app P)) :
            (baseChangeR.obj (DerivedCategory.Q.obj K), baseChangeR.obj (DerivedCategory.Q.obj P)) ⟶
            (DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
                DerivedCategory.Q.obj (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        (derivedTensor_comparison.{uRp, max v uR uA uRp} R'
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hP').hom ≫
          DerivedCategory.Q.map e.hom ≫
            (Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso.{uR, uRp, max v uA}
              (algebraMap R R') baseChangeR comparisonR K P hK hP).inv)
    (hchain : e.hom ≫
      ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max (max v uRp) uR uA} R)
          (ComplexShape.up ℤ) ≫ (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv) ≫
      (NatTrans.mapHomologicalComplex
        (RingTheory.TorIndependence.derivedBaseChangeComparison
          (algebraMap R A) (algebraMap R R')
          (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
          ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
            (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
          baseChangeR baseChangeA comparisonR comparisonA).1
        (ComplexShape.up ℤ)).app (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
            (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
          A R').toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (((NatTrans.mapHomologicalComplex
          (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
            (algebraMap R A) (algebraMap A (TensorProduct R A R'))
                (algebraMap R (TensorProduct R A R'))
            algebraMap_tensorProduct_comp_left) (ComplexShape.up ℤ)).app K) ≫
                ((NatIso.mapHomologicalComplex
          (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
          (ComplexShape.up ℤ)).app K).inv) ≫
      (extendRestrictComplexIso.{max v uR}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom =
    HomologicalComplex.mapBifunctorMap (𝟙 _)
        (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P p)
      (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ)) :
    TensorComparisonCompatibilityOf hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai
      (resolvedProjectionFormula.{max v uRp} (algebraMap R A) Ff alphaf P hP p)
      (resolvedProjectionFormula.{max v uR}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hP'
          (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
          P p))
      (DerivedCategory.Q.obj K) := by
  have := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uRp, max v uA}
    (algebraMap R R') baseChangeR comparisonR K hK
  have := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uRp, max v uA}
    (algebraMap R R') baseChangeR comparisonR P hP
  have := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, max v uRp}
    (algebraMap R A) Ff alphaf K hK
  have : IsIso
      (comparisonA.app
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)) :=
    CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uA, max uA uRp,
      max v uR} (algebraMap A (TensorProduct R A R')) baseChangeA comparisonA _
      (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{uR, uA, max v uRp}
        (algebraMap R A) K hK)
  have hL := kFlat_baseChangeResolution.{uR, uA, uRp, v} (R' := R') K hK
  have Hs := tensorComparisonResolved_source.{uR, uA, uRp, v} hTor baseChangeR comparisonR
    baseChangeA comparisonA Ff alphaf P hP p K hK hP' e hval
  have Ht := tensorComparisonResolved_target.{uR, uA, uRp, v} baseChangeR comparisonR
    baseChangeA comparisonA Ff alphaf Fi alphai P p K hK hL hP'
  have Hr := tensorComparisonResolved_rhs.{uR, uA, uRp, v} hTor baseChangeR comparisonR
    baseChangeA comparisonA P p K hP' hL hP'
  have Hf := tcAssembly_full _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hs Ht (IsIso.inv_hom_id _)
  have hQ := (tcAssembly_map_chain DerivedCategory.Q
    ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.up ℤ)) _ _ _ _ _ _).trans (congrArg DerivedCategory.Q.map hchain)
  have h2 : (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        (((comparisonR.app K, baseChangeR.map
            (algebraResolutionIso.{max v uRp} (algebraMap R A) P p).hom ≫ comparisonR.app P) :
          (baseChangeR.obj (DerivedCategory.Q.obj K), baseChangeR.obj
              (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
            (DerivedCategory.Q.obj
                (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
                DerivedCategory.Q.obj
                (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ≫
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        ((CategoryTheory.inv (comparisonR.app K),
          CategoryTheory.inv (comparisonR.app P) ≫ baseChangeR.map
              (algebraResolutionIso.{max v uRp} (algebraMap R A) P p).inv) :
          (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
              DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶
          (baseChangeR.obj (DerivedCategory.Q.obj K), baseChangeR.obj
              (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) = 𝟙 _ := by
    refine map_prod_comp_eq_id _ _ _ ?_ ?_
    · exact IsIso.hom_inv_id _
    · exact (Category.assoc _ _ _).trans ((congrArg (fun z => _ ≫ z)
        (IsIso.hom_inv_id_assoc _ _)).trans ((baseChangeR.map_comp _ _).symm.trans
          ((congrArg baseChangeR.map
              (algebraResolutionIso.{max v uRp} (algebraMap R A) P p).hom_inv_id).trans
              (baseChangeR.map_id _))))
  have j1 : (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        (((comparisonR.app K, (algebraResolutionIso.{max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P
            p)).hom) :
          (baseChangeR.obj (DerivedCategory.Q.obj K),
              (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)) ⟶
            (DerivedCategory.Q.obj
                (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
                DerivedCategory.Q.obj
                (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))) ≫
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
        (((CategoryTheory.inv (comparisonR.app K),
            (algebraResolutionIso.{max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P
            p)).inv) :
          (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K),
              DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶
            (baseChangeR.obj (DerivedCategory.Q.obj K),
                (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)))) =
                𝟙 _ := by
    refine map_prod_comp_eq_id _ _ _ ?_ ?_
    · exact IsIso.hom_inv_id _
    · exact (algebraResolutionIso.{max v uR}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P
          p)).hom_inv_id
  exact tcAssembly_cancel _ _ _ _ _ _ _ _ _ _ (Iso.hom_inv_id _) h2 _ _ _ j1 (Iso.hom_inv_id _)
    (Iso.hom_inv_id _) (Hf.trans (hQ.trans Hr.symm))

include hTor hf hA hR hi hP p in
/-- **The tensor comparison of [stacks 0E2A] at every K-flat complex, from its two inputs.**  The
first input identifies the base change of the derived tensor product of [stacks 068I] with the
lax structure `Dualizing.derivedTensorBaseChange` at the pairs `(K, P)`; the second is the
chain-level identity carried by every tensor base-change isomorphism of total complexes. -/
theorem tensorComparisonCompatibilityOf_resolved_of_inputs
    (hP' : CochainComplex.KFlat.{uRp, max (max v uR) uRp (max uA uRp)}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    [QuasiIso (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
        P p)]
    (hmu : ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K →
      tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
          (totalDerivedExtensionScalars (algebraMap R R'))
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj P) =
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj P))
    (hchain : ∀ (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
      (e : tensorComplex.{uRp, max uR (max v uA)}
          ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj K)
          ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj P) ≅
        (extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj
            (tensorComplex.{uR, max uRp (max v uA)} K P)),
      IsTensorBaseChangeIso.{uR, uRp, max v uA} (algebraMap R R') K P e →
      e.hom ≫
        ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max v uR uA uRp} R)
            (ComplexShape.up ℤ) ≫ (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv) ≫
        (NatTrans.mapHomologicalComplex
          (RingTheory.TorIndependence.derivedBaseChangeComparison
            (algebraMap R A) (algebraMap R R')
            (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
            ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
              (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
            baseChangeR baseChangeA comparisonR comparisonA).1
          (ComplexShape.up ℤ)).app
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
            A R').toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex
              (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
                (algebraMap R A) (algebraMap A (TensorProduct R A R'))
                (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_left)
              (ComplexShape.up ℤ)).app K ≫
            ((NatIso.mapHomologicalComplex
              (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
                  (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
                (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
              (ComplexShape.up ℤ)).app K).inv) ≫
        (extendRestrictComplexIso.{max v uR}
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
            (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom =
      HomologicalComplex.mapBifunctorMap (𝟙 _)
          (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
          P p)
        (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ))
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA uRp} K) :
    TensorComparisonCompatibilityOf hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai
      (resolvedProjectionFormula.{max v uRp} (algebraMap R A) Ff alphaf P hP p)
      (resolvedProjectionFormula.{max v uR}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hP'
          (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
          P p))
      (DerivedCategory.Q.obj K) := by
  obtain ⟨hFL, e, he, hv⟩ := tensorBaseChangeMor_eq_q_obj.{uR, uRp, max v uA} (algebraMap R R')
    baseChangeR comparisonR (totalDerivedExtensionScalars (algebraMap R R')) K P hK hP
  exact tensorComparisonCompatibilityOf_resolved_of_chain.{uR, uA, uRp, v} hTor baseChangeR
    comparisonR baseChangeA comparisonA Ff alphaf Fi alphai P hP p K hK hP' e
    ((hmu K hK).symm.trans hv) (hchain K e he)

include hTor hf hi in
/-- **The comparison square of [stacks 0E2A], from the two inputs of the tensor comparison.**
For any K-flat resolution `p : P ⟶ A[0]`, the resolved projection formulas satisfy
`Dualizing.TensorComparisonCompatibilityOf` at every K-flat complex by
`Dualizing.tensorComparisonCompatibilityOf_resolved_of_inputs`, so the square of
`Dualizing.restrictScalars_map_derivedHomBaseChange_app_eq_of_pf` holds at every object. -/
theorem exists_restrictScalars_map_derivedHomBaseChange_app_eq_of_inputs
    (hmuAll : ∀ (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ),
      CochainComplex.KFlat.{uR, max v uA uRp} P →
      ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
        CochainComplex.KFlat.{uR, max v uA uRp} K →
        tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
            (totalDerivedExtensionScalars (algebraMap R R'))
            (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj P) =
          derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
            (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj P))
    (hchainAll : ∀ (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
      (p : P ⟶ algebraComplex.{max v uRp} (algebraMap R A)), QuasiIso p →
      ∀ (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
        (e : tensorComplex.{uRp, max uR (max v uA)}
            ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj K)
            ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj P) ≅
          (extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj
              (tensorComplex.{uR, max uRp (max v uA)} K P)),
        IsTensorBaseChangeIso.{uR, uRp, max v uA} (algebraMap R R') K P e →
        e.hom ≫
          ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max v uR uA uRp} R)
              (ComplexShape.up ℤ) ≫ (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv) ≫
          (NatTrans.mapHomologicalComplex
            (RingTheory.TorIndependence.derivedBaseChangeComparison
              (algebraMap R A) (algebraMap R R')
              (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
              ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
                (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
              baseChangeR baseChangeA comparisonR comparisonA).1
            (ComplexShape.up ℤ)).app
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
              A R').toRingHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex
                (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
                  (algebraMap R A) (algebraMap A (TensorProduct R A R'))
                  (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_left)
                (ComplexShape.up ℤ)).app K ≫
              ((NatIso.mapHomologicalComplex
                (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
                    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
                  (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
                (ComplexShape.up ℤ)).app K).inv) ≫
          (extendRestrictComplexIso.{max v uR}
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom =
        HomologicalComplex.mapBifunctorMap (𝟙 _)
            (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
            P p)
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ∃ (sIso : _ ≅ baseChangeR.obj
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom R).obj
            (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)), K)))
      (tIso : _ ≅ (Stacks.DerivedHom.ScalarTransportedInternalHom.hom R').obj
          (Opposite.op (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp}
              (algebraMap R A))), baseChangeR.obj K)),
      (ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
          A R').toRingHom).mapDerivedCategory.map
          ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
            baseChangeA comparisonA hA).app K) =
        sIso.hom ≫ Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
            (algebraMap R R') baseChangeR comparisonR
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K ≫ tIso.inv := by
  obtain ⟨P, p, hP, -, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{uR, max v uA uRp}
    (algebraComplex.{max v uRp} (algebraMap R A))
  have hP' := kFlat_baseChangeResolution.{uR, uA, uRp, v} (R' := R') P hP
  have := quasiIso_baseChangeResolution'.{uR, uA, uRp, v} hTor baseChangeR comparisonR
    baseChangeA comparisonA P p hP
  exact ⟨_, _, restrictScalars_map_derivedHomBaseChange_app_eq_of_pf hTor baseChangeR comparisonR
    baseChangeA comparisonA Ff alphaf Fi alphai
    (resolvedProjectionFormula.{max v uRp} (algebraMap R A) Ff alphaf P hP p)
    (resolvedProjectionFormula.{max v uR}
        (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hP'
        (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA P p))
    (tensorComparisonCompatibilityOf_resolved_of_inputs.{uR, uA, uRp, v} hTor baseChangeR
      comparisonR baseChangeA comparisonA Ff alphaf Fi alphai P hP p hP'
      (hmuAll P hP) (hchainAll P p hp))
    K⟩

include hTor hf hi in
/-- **The comparison square of [stacks 0E2A] at every object, from the chain-level identity.**
`Dualizing.exists_restrictScalars_map_derivedHomBaseChange_app_eq_of_inputs` with its first input
discharged by `Dualizing.tensorBaseChangeMor_eq_derivedTensorBaseChange_of_kFlat`. -/
theorem exists_restrictScalars_map_derivedHomBaseChange_app_eq_of_chain
    (hchainAll : ∀ (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
      (p : P ⟶ algebraComplex.{max v uRp} (algebraMap R A)), QuasiIso p →
      ∀ (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
        (e : tensorComplex.{uRp, max uR (max v uA)}
            ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj K)
            ((extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj P) ≅
          (extensionOfScalarsCochain.{uR, uRp, max v uA} (algebraMap R R')).obj
              (tensorComplex.{uR, max uRp (max v uA)} K P)),
        IsTensorBaseChangeIso.{uR, uRp, max v uA} (algebraMap R R') K P e →
        e.hom ≫
          ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max v uR uA uRp} R)
              (ComplexShape.up ℤ) ≫ (extendRestrictComplexIso.{max v uRp} (algebraMap R A) K).inv) ≫
          (NatTrans.mapHomologicalComplex
            (RingTheory.TorIndependence.derivedBaseChangeComparison
              (algebraMap R A) (algebraMap R R')
              (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
              ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
                (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
              baseChangeR baseChangeA comparisonR comparisonA).1
            (ComplexShape.up ℤ)).app
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                (algebraMap R A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
              A R').toRingHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex
                (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp}
                  (algebraMap R A) (algebraMap A (TensorProduct R A R'))
                  (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_left)
                (ComplexShape.up ℤ)).app K ≫
              ((NatIso.mapHomologicalComplex
                (extendScalarsCompIsoOfEq.{uR, uRp, max uA uRp, max v uA} (algebraMap R R')
                    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
                  (algebraMap R (TensorProduct R A R')) algebraMap_tensorProduct_comp_right)
                (ComplexShape.up ℤ)).app K).inv) ≫
          (extendRestrictComplexIso.{max v uR}
              (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
            (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
              (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).hom =
        HomologicalComplex.mapBifunctorMap (𝟙 _)
            (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
            P p)
          (moduleTensor.{uRp, max (max v uR) uRp (max uA uRp)} R') (ComplexShape.up ℤ))
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ∃ (sIso : _ ≅ baseChangeR.obj
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom R).obj
            (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)), K)))
      (tIso : _ ≅ (Stacks.DerivedHom.ScalarTransportedInternalHom.hom R').obj
          (Opposite.op (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp}
              (algebraMap R A))), baseChangeR.obj K)),
      (ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
          A R').toRingHom).mapDerivedCategory.map
          ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
            baseChangeA comparisonA hA).app K) =
        sIso.hom ≫ Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
            (algebraMap R R') baseChangeR comparisonR
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K ≫ tIso.inv :=
  exists_restrictScalars_map_derivedHomBaseChange_app_eq_of_inputs.{uR, uA, uRp, v} hTor baseChangeR
    comparisonR
    baseChangeA comparisonA Ff alphaf Fi alphai
    (fun P hP K hK => tensorBaseChangeMor_eq_derivedTensorBaseChange_of_kFlat.{uR, uRp, max v uA}
      (algebraMap R R') baseChangeR comparisonR (totalDerivedExtensionScalars (algebraMap R R')) K P
      hK hP)
    hchainAll K

include hTor hf hA hR hi hP p in
/-- **The tensor comparison of [stacks 0E2A] at the resolved projection formulas.**  For a K-flat
resolution `p : P ⟶ A[0]` of the algebra, `Dualizing.TensorComparisonCompatibilityOf` holds at
every object of `D(R)` for the projection formulas `Dualizing.resolvedProjectionFormula` of `p`
over `R` and of its base change over `R'`. -/
theorem tensorComparisonCompatibilityOf_resolved
    (hP' : CochainComplex.KFlat.{uRp, max (max v uR) uRp (max uA uRp)}
        (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    [QuasiIso (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
        P p)] (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    TensorComparisonCompatibilityOf hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai
      (resolvedProjectionFormula.{max v uRp} (algebraMap R A) Ff alphaf P hP p)
      (resolvedProjectionFormula.{max v uR}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
          (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hP'
          (baseChangeResolution.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
          P p)) X :=
  tensorComparisonCompatibilityOf_of_kFlat hTor baseChangeR comparisonR baseChangeA comparisonA
    Ff alphaf Fi alphai _ _
    (tensorComparisonCompatibilityOf_resolved_of_inputs.{uR, uA, uRp, v} hTor baseChangeR
      comparisonR baseChangeA comparisonA Ff alphaf Fi alphai P hP p hP'
      (fun K hK => tensorBaseChangeMor_eq_derivedTensorBaseChange_of_kFlat.{uR, uRp, max v uA}
        (algebraMap R R') baseChangeR comparisonR
            (totalDerivedExtensionScalars (algebraMap R R')) K P
        hK hP)
      (fun K e he => chainIdentity.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA comparisonA
        P p K e he)) X

include hTor hf hi in
/-- **The comparison square of [stacks 0E2A], at arbitrary models of the two derived extensions
of scalars.**  After restriction along `R' → A ⊗_R R'`, the base-change morphism of [stacks 0E29]
at `K` is the derived-Hom base-change morphism of [stacks 0E1X] along `R → R'` at the algebra and
`K`, between two isomorphisms. -/
theorem exists_restrictScalars_map_derivedHomBaseChange_app_eq_of_models
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ∃ (sIso : _ ≅ baseChangeR.obj
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom R).obj
            (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)), K)))
      (tIso : _ ≅ (Stacks.DerivedHom.ScalarTransportedInternalHom.hom R').obj
          (Opposite.op (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp}
              (algebraMap R A))), baseChangeR.obj K)),
      (ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
          A R').toRingHom).mapDerivedCategory.map
          ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
            baseChangeA comparisonA hA).app K) =
        sIso.hom ≫ Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
            (algebraMap R R') baseChangeR comparisonR
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K ≫ tIso.inv :=
  exists_restrictScalars_map_derivedHomBaseChange_app_eq_of_chain.{uR, uA, uRp, v} hTor baseChangeR
    comparisonR baseChangeA comparisonA Ff alphaf Fi alphai
    (fun P p _ K e he => chainIdentity.{uR, uA, uRp, v} baseChangeR comparisonR baseChangeA
      comparisonA P p K e he)
    K

include hTor in
/-- **The comparison square of [stacks 0E2A].**  After restriction along `R' → A ⊗_R R'`, the
base-change morphism `RHom_R(A, K) ⊗ᴸ_A A' ⟶ RHom_{R'}(A', K ⊗ᴸ_R R')` of [stacks 0E29] at `K` is
the derived-Hom base-change morphism `RHom_R(A, K) ⊗ᴸ_R R' ⟶ RHom_{R'}(A ⊗ᴸ_R R', K ⊗ᴸ_R R')` of
[stacks 0E1X] along `R → R'`, between two isomorphisms.  This is the step "it suffices to prove
it is an isomorphism after applying `φ'_*`" of the proof of [stacks 0E2A]. -/
theorem exists_restrictScalars_map_derivedHomBaseChange_app_eq
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    ∃ (sIso : _ ≅ baseChangeR.obj
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom R).obj
            (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)), K)))
      (tIso : _ ≅ (Stacks.DerivedHom.ScalarTransportedInternalHom.hom R').obj
          (Opposite.op (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp}
              (algebraMap R A))), baseChangeR.obj K)),
      (ModuleCat.restrictScalars.{max v uR uA uRp}
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R
          A R').toRingHom).mapDerivedCategory.map
          ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR hR
            baseChangeA comparisonA hA).app K) =
        sIso.hom ≫ Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
            (algebraMap R R') baseChangeR comparisonR
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K ≫ tIso.inv :=
  exists_restrictScalars_map_derivedHomBaseChange_app_eq_of_models.{uR, uA, uRp, v} hTor
    baseChangeR comparisonR baseChangeA comparisonA
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).functor
    (canonicalExtensionModel.{uR, uA, max v uRp} R A).comparison
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').functor
    (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').comparison
    (hf := (canonicalExtensionModel.{uR, uA, max v uRp} R A).isLeftDerived)
    (hi := (canonicalExtensionModelIncludeRight.{uR, uA, uRp, max v uR} R A R').isLeftDerived) K

end Dualizing
