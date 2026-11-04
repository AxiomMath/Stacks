module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.UniversalHomeomorphismInvariance
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorialBijective

/-!
# Étale cohomology of a finite disjoint union of open subschemes

Let `Z` be a scheme which is the disjoint union of finitely many open subschemes `U_a`, the
images of open immersions `j_a : U_a ⟶ Z`. Then every abelian sheaf `F` on the small étale site of
`Z` is the direct sum of the extensions by zero of its restrictions to the `U_a`, and restriction
identifies the étale cohomology of `Z` with the product of the étale cohomologies of the `U_a`:

`H^q(Z, F) = ∏_a H^q(U_a, j_a⁻¹ F)`.

The proof is at the level of `Ext` groups. The constant sheaf `ℤ` on `Z` is the direct sum of the
extensions by zero `j_{a!} j_a⁻¹ ℤ`, so `Ext^q(ℤ, F)` is the product of the
`Ext^q(j_{a!} j_a⁻¹ ℤ, F)`, and since extension by zero and restriction along an open immersion
form an adjoint pair of exact functors, `Ext^q(j_{a!} j_a⁻¹ ℤ, F) = Ext^q(j_a⁻¹ ℤ, j_a⁻¹ F)`.

## Main results

* `Stacks.EtaleCohomology.isIso_biproductDesc_counit`: an abelian sheaf on a finite disjoint union
  of open subschemes is the direct sum of the extensions by zero of its restrictions.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyPullback_pi`: **étale cohomology of a finite
  disjoint union of open subschemes is the product of their étale cohomologies.**

## References

* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV), where the additivity is
  used for the finite disjoint unions of copies of `Spec K`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Ext.subsingleton_of_injective Abelian.hasFiniteBiproducts

section Decomposition

variable {Z : Scheme.{u}} {ι : Type} [Fintype ι] [DecidableEq ι] {U : ι → Scheme.{u}}
  (j : ∀ a, U a ⟶ Z) [∀ a, IsOpenImmersion (j a)]

/-- The direct sum of the extensions by zero of the restrictions of a sheaf to a finite family of
open subschemes. -/
abbrev clopenSum (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ⨁ fun a => (extensionByZero.{u, 0} (j a)).obj ((etaleRestriction.{u, 0} (j a)).obj F)

/-- The map from the direct sum of the extensions by zero of the restrictions to the sheaf: the
sum of the counits. -/
abbrev clopenSumDesc (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    clopenSum j F ⟶ F :=
  biproduct.desc fun a => (extensionByZeroAdj.{u, 0} (j a)).counit.app F

omit [DecidableEq ι] in
/-- In a finite biproduct whose other summands vanish, the inclusion of one summand is an
isomorphism. -/
theorem isIso_biproduct_ι_of_isZero {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] (f : ι → C) (b : ι) (h : ∀ a, a ≠ b → IsZero (f a)) :
    IsIso (biproduct.ι f b) := by
  refine ⟨⟨biproduct.π f b, biproduct.ι_π_self f b, ?_⟩⟩
  refine biproduct.hom_ext _ _ fun a => ?_
  by_cases hab : a = b
  · subst hab
    simp
  · exact (h a hab).eq_of_tgt _ _

variable (hdisj : Pairwise fun a b => Disjoint (Set.range (j a).base) (Set.range (j b).base))
  (hcov : ⋃ a, Set.range (j a).base = Set.univ)

omit [DecidableEq ι] in
include hdisj hcov in
/-- **An abelian sheaf on a finite disjoint union of open subschemes is the direct sum of the
extensions by zero of its restrictions.** -/
theorem isIso_clopenSumDesc (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (clopenSumDesc j F) := by
  classical
  refine isIso_of_isIso_etaleAbelianInverseImage_family.{u, 0} (ι := ULift.{u} ι)
    (fun a => j a.down) (by
      rw [← hcov]
      ext z
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨a, h⟩ => ⟨a.down, h⟩, fun ⟨a, h⟩ => ⟨⟨a⟩, h⟩⟩) _ fun ⟨b⟩ => ?_
  refine (NatIso.isIso_map_iff (etaleAbelianInverseImageRestrictionIso.{u, 0} (j b)) _).mpr ?_
  set R := etaleRestriction.{u, 0} (j b)
  set D := fun a => (extensionByZero.{u, 0} (j a)).obj ((etaleRestriction.{u, 0} (j a)).obj F)
  have hzero : ∀ a, a ≠ b → IsZero (R.obj (D a)) := fun a hab =>
    (isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint.{u, 0} (j b) (j a)
      (hdisj (Ne.symm hab)) _).of_iso
        ((etaleAbelianInverseImageRestrictionIso.{u, 0} (j b)).app (D a)).symm
  have hι : IsIso (R.map (biproduct.ι D b)) := by
    have := Functor.preservesFiniteBiproductsOfAdditive R
    have h1 := isIso_biproduct_ι_of_isZero (fun a => R.obj (D a)) b hzero
    have h2 : R.map (biproduct.ι D b) =
        biproduct.ι (fun a => R.obj (D a)) b ≫ (R.mapBiproduct D).inv :=
      (biproduct.ι_desc (fun a => R.map (biproduct.ι D a)) b).symm
    rw [h2]
    infer_instance
  have hcomp : R.map (biproduct.ι D b) ≫ R.map (clopenSumDesc j F) =
      R.map ((extensionByZeroAdj.{u, 0} (j b)).counit.app F) := by
    rw [← R.map_comp, biproduct.ι_desc]
  have hcounit := isIso_etaleRestriction_map_counit.{u, 0} (j b) F
  rw [← hcomp] at hcounit
  exact IsIso.of_isIso_comp_left (R.map (biproduct.ι D b)) _

end Decomposition

/-! ### Cohomology -/

/-- Composing with isomorphisms on both sides is a bijection on `Ext`. -/
theorem ext_mk₀_comp_comp_mk₀_bijective {C : Type*} [Category C] [Abelian C] [HasExt.{u + 1} C]
    {A A' B B' : C} (e : A' ≅ A) (e' : B ≅ B') (q : ℕ) :
    Function.Bijective (fun y : Ext.{u + 1} A B q =>
      ((Ext.mk₀ e.hom).comp y (zero_add q)).comp (Ext.mk₀ e'.hom) (add_zero q)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun y => ((Ext.mk₀ e.inv).comp y (zero_add q)).comp (Ext.mk₀ e'.inv) (add_zero q), ?_, ?_⟩
  · intro y
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id,
      Ext.mk₀_id_comp, Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.comp_mk₀_id]
  · intro y
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id,
      Ext.mk₀_id_comp, Ext.mk₀_comp_mk₀, Iso.inv_hom_id, Ext.comp_mk₀_id]

section Cohomology

variable {Z : Scheme.{u}} {ι : Type} [Fintype ι] [DecidableEq ι] {U : ι → Scheme.{u}}
  (j : ∀ a, U a ⟶ Z) [∀ a, IsOpenImmersion (j a)]

/-- The inverse image of abelian sheaves along an étale morphism is restriction. -/
def smallEtalePullbackAbRestrictionIso {V X : Scheme.{u}} (i : V ⟶ X) [Etale i] :
    smallEtalePullbackAb i ≅ etaleRestriction.{u, 0} i :=
  (smallEtaleAdjunctionAb i).leftAdjointUniq (etaleRestrictionAbelianDirectImageAdj.{u, 0} i)

/-- Pulling back étale cohomology along an étale morphism is the action of restriction on `Ext`,
transported along the identifications of the constant sheaf and of the inverse image. -/
theorem etaleCohomologyPullback_eq_restriction {V X : Scheme.{u}} (i : V ⟶ X) [Etale i]
    (G : Sheaf X.smallEtaleTopology Ab.{u + 1}) (q : ℕ) (x : Sheaf.H.{u + 1} G q) :
    etaleCohomologyPullback i (𝟙 _) q x =
      ((Ext.mk₀ ((smallEtalePullbackAbConstantIso i).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
        (smallEtalePullbackAbRestrictionIso i).hom.app _)).comp
          (x.mapExactFunctor (etaleRestriction.{u, 0} i)) (zero_add q)).comp
        (Ext.mk₀ ((smallEtalePullbackAbRestrictionIso i).inv.app G)) (add_zero q) := by
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor
    (smallEtalePullbackAbRestrictionIso i).hom
    ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) q x
  rw [etaleCohomologyPullback_apply, Ext.comp_mk₀_id, ← Ext.mk₀_comp_mk₀_assoc, key,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id_app, Ext.comp_mk₀_id]

variable (hdisj : Pairwise fun a b => Disjoint (Set.range (j a).base) (Set.range (j b).base))
  (hcov : ⋃ a, Set.range (j a).base = Set.univ)

omit [DecidableEq ι] in
include hdisj hcov in
/-- **Étale cohomology of a finite disjoint union of open subschemes is the product of their
étale cohomologies**: restriction to the members is a bijection
`H^q(Z, G) → ∏_a H^q(U_a, j_a⁻¹ G)`. -/
theorem bijective_etaleCohomologyPullback_pi (G : Sheaf Z.smallEtaleTopology Ab.{u + 1})
    (q : ℕ) :
    Function.Bijective (fun x : Sheaf.H.{u + 1} G q => fun a =>
      etaleCohomologyPullback (j a) (𝟙 _) q x) := by
  classical
  set ZZ := (constantSheaf (smallEtaleTopology Z) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))
  set L := fun a => extensionByZero.{u, 0} (j a)
  set R := fun a => etaleRestriction.{u, 0} (j a)
  set D := fun a => (L a).obj ((R a).obj ZZ)
  have := isIso_clopenSumDesc j hdisj hcov ZZ
  set e := asIso (clopenSumDesc j ZZ)
  -- step 1: `ℤ` is the biproduct of the extensions by zero of its restrictions
  have h₁ := Stacks.ExtFunctorial.ext_finiteBiprod_bijective (Y := G) (Xs := D)
    (fun a => biproduct.ι D a ≫ e.hom) (fun a => e.inv ≫ biproduct.π D a)
    (fun a b => by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, biproduct.ι_π])
    (by
      calc (∑ k, (e.inv ≫ biproduct.π D k) ≫ biproduct.ι D k ≫ e.hom)
          = e.inv ≫ (∑ k, biproduct.π D k ≫ biproduct.ι D k) ≫ e.hom := by
            simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
        _ = 𝟙 ZZ := by rw [biproduct.total, Category.id_comp, e.inv_hom_id]) q
  -- step 2: adjunction
  have h₂ : ∀ a, Function.Bijective (fun y : Ext.{u + 1} (D a) G q =>
      (Ext.mk₀ ((extensionByZeroAdj.{u, 0} (j a)).unit.app ((R a).obj ZZ))).comp
        (y.mapExactFunctor (R a)) (zero_add q)) := fun a =>
    Stacks.ExtFunctorial.extAdjunction_bijective (extensionByZeroAdj.{u, 0} (j a)) _ G q
  have h₁₂ : Function.Bijective (fun x : Sheaf.H.{u + 1} G q => fun a =>
      x.mapExactFunctor (R a)) := by
    have hcomp : (fun x : Sheaf.H.{u + 1} G q => fun a => x.mapExactFunctor (R a)) =
        (fun y a => (Ext.mk₀ ((extensionByZeroAdj.{u, 0} (j a)).unit.app ((R a).obj ZZ))).comp
          ((y a).mapExactFunctor (R a)) (zero_add q)) ∘
        (fun x : Sheaf.H.{u + 1} G q => fun a =>
          (Ext.mk₀ (biproduct.ι D a ≫ e.hom)).comp x (zero_add q)) := by
      funext x a
      simp only [Function.comp_apply, e, asIso_hom, clopenSumDesc, biproduct.ι_desc,
        Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
        Ext.mk₀_comp_mk₀]
      rw [(extensionByZeroAdj.{u, 0} (j a)).right_triangle_components ZZ]
      exact (Ext.mk₀_id_comp _).symm
    rw [hcomp]
    exact (Function.Bijective.piMap h₂).comp h₁
  -- step 3: transport along the identifications of the inverse image and of the constant sheaf
  have h₃ : ∀ a, Function.Bijective (fun y : Ext.{u + 1} ((R a).obj ZZ) ((R a).obj G) q =>
      ((Ext.mk₀ ((smallEtalePullbackAbConstantIso (j a)).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
        (smallEtalePullbackAbRestrictionIso (j a)).hom.app _)).comp y (zero_add q)).comp
        (Ext.mk₀ ((smallEtalePullbackAbRestrictionIso (j a)).inv.app G)) (add_zero q)) := by
    intro a
    exact ext_mk₀_comp_comp_mk₀_bijective
      (((smallEtalePullbackAbConstantIso (j a)).app (AddCommGrpCat.of (ULift ℤ))).symm ≪≫
        (smallEtalePullbackAbRestrictionIso (j a)).app _)
      ((smallEtalePullbackAbRestrictionIso (j a)).app G).symm q
  simp_rw [etaleCohomologyPullback_eq_restriction]
  exact (Function.Bijective.piMap h₃).comp h₁₂

end Cohomology

end Stacks.EtaleCohomology
