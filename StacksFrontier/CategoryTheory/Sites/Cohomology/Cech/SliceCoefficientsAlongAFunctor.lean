module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOnTheSlice

/-!
# The Čech complex with coefficients on a slice, along a functor

The Čech complex of Stacks 03AM of a family `E = {U_i → U}` of morphisms of `C` with
coefficients in a presheaf `F` on `C` only sees the restriction of `F` to the slice `C/U`: it is
built from the values of `F` on the iterated fibre products `U_{i_0} ×_U … ×_U U_{i_p}`, which
are objects of `C/U`, and from the restriction maps between them, which are morphisms of `C/U`.
That complex, for an arbitrary presheaf `P` on the slice, is `Stacks.CechSite.sliceCechComplex`
(`StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOnTheSlice`).

This file compares two such complexes along a functor `u : C ⥤ D` which preserves the iterated
fibre products of `E`, for coefficients `P` on `C/U` and `Q` on `D/u(U)` which agree only on a
class `K` of objects of `C/U` containing those fibre products:

`Č(u(E), Q) ≅ Č(E, P)`

as soon as there are isomorphisms `P(Y) ≅ Q(u(Y))`, natural for the morphisms between members
of `K`. This is `Stacks.CechSite.sliceCechComplexIsoOfFunctor`. The case `K = ⊤` with `P` the
restriction of `Q` along `u` is `Stacks.CechSite.cechComplexIsoOfFunctor`; the point of the
generalization is that the two coefficient systems need neither be defined on the whole of `C`
and `D` nor agree away from the fibre products. That is the situation of the Čech complex of a
locally quasi-coherent module with the flat base change property on the site of a category
fibred in groupoids, whose values over an object agree with those of a quasi-coherent module
on the scheme below it only along flat morphisms.

## Main definitions

* `Stacks.CechSite.sliceCechComplexIsoOfFunctor`: the comparison isomorphism along `u`.

## Main results

* `Stacks.CechSite.isZero_homology_sliceCechComplex_of_functor`: transfer of vanishing of
  cohomology along the comparison.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

universe w v v₂ v' u u₂ u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] cechFormalCoproduct cechFormalCoproductMap
  CategoryTheory.PreZeroHypercover.map CategoryTheory.Over.post

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
  (u : C ⥤ D) {X : C} (E : PreZeroHypercover.{w} X)
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]

variable [hE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [hEu : ∀ (n : ℕ) (i : Fin (n + 1) → (E.map u).I₀),
    HasProduct (fun a ↦ Over.mk ((E.map u).f (i a)))]
  (P : (Over X)ᵒᵖ ⥤ A) (Q : (Over (u.obj X))ᵒᵖ ⥤ A) (K : ObjectProperty (Over X))
  (e : ∀ Y : Over X, K Y → (P.obj (op Y) ≅ Q.obj (op ((Over.post u).obj Y))))
  (he : ∀ {Y Y' : Over X} (hY : K Y) (hY' : K Y') (g : Y' ⟶ Y),
    P.map g.op ≫ (e Y' hY').hom = (e Y hY).hom ≫ Q.map ((Over.post u).map g).op)
  (hK : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), K (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))))

include he in
/-- The naturality of the inverse identifications. -/
theorem inv_comp_map_of_partialIso {Y Y' : Over X} (hY : K Y) (hY' : K Y') (g : Y' ⟶ Y) :
    (e Y hY).inv ≫ P.map g.op = Q.map ((Over.post u).map g).op ≫ (e Y' hY').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← he hY hY' g, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The degree-`n` component of the comparison of slice Čech complexes: on the factor indexed by
a tuple `i`, restriction of `Q` along the comparison map of the iterated fibre product of `i`,
followed by the identification of the values of `Q` and `P` there. -/
noncomputable def sliceCechComplexMapDegree (n : ℕ) :
    ((FormalCoproduct.evalOp.{w} (Over (u.obj X)) A).obj Q).obj
        (op ((cechSimplicialObject (E.map u)).obj (op (SimplexCategory.mk n)))) ⟶
      ((FormalCoproduct.evalOp.{w} (Over X) A).obj P).obj
        (op ((cechSimplicialObject E).obj (op (SimplexCategory.mk n)))) :=
  Pi.lift (fun i : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I ↦
    Pi.π (fun l : ((cechSimplicialObject (E.map u)).obj (op (SimplexCategory.mk n))).I ↦
        Q.obj (op (((cechSimplicialObject (E.map u)).obj
            (op (SimplexCategory.mk n))).obj l))) i ≫
      Q.map (cechProductMapOfFunctor u E n i).op ≫ (e _ (hK n i)).inv)

omit [Preadditive A] in
/-- The factor of the degree-`n` comparison indexed by a tuple `i`. -/
@[reassoc]
theorem sliceCechComplexMapDegree_comp_π (n : ℕ)
    (i : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I) :
    sliceCechComplexMapDegree u E P Q K e hK n ≫
        Pi.π (fun l : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I ↦
          P.obj (op (((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).obj l))) i =
      Pi.π (fun l : ((cechSimplicialObject (E.map u)).obj
            (op (SimplexCategory.mk n))).I ↦
          Q.obj (op (((cechSimplicialObject (E.map u)).obj
              (op (SimplexCategory.mk n))).obj l))) i ≫
        Q.map (cechProductMapOfFunctor u E n i).op ≫ (e _ (hK n i)).inv :=
  Pi.lift_π _ _

include he in
attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.evalOp in
/-- The degreewise comparison maps commute with each signed coface map. -/
theorem sliceCechComplexMapDegree_zsmul_δ_comm (n : ℕ) (k : Fin (n + 2)) :
    sliceCechComplexMapDegree u E P Q K e hK n ≫
        ((-1 : ℤ) ^ (k : ℕ) •
          ((FormalCoproduct.evalOp.{w} (Over X) A).obj P).map
            ((cechSimplicialObject E).map (SimplexCategory.δ k).op).op) =
      ((-1 : ℤ) ^ (k : ℕ) •
          ((FormalCoproduct.evalOp.{w} (Over (u.obj X)) A).obj Q).map
            ((cechSimplicialObject (E.map u)).map (SimplexCategory.δ k).op).op) ≫
        sliceCechComplexMapDegree u E P Q K e hK (n + 1) := by
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  refine congrArg (fun z ↦ ((-1 : ℤ) ^ (k : ℕ)) • z) ?_
  apply Pi.hom_ext
  intro j
  set gE := (cechSimplicialObject E).map (SimplexCategory.δ k).op with hgE
  set gG := (cechSimplicialObject (E.map u)).map (SimplexCategory.δ k).op with hgG
  have hEv := evalOpMapCompPi P gE j
  have hGv := evalOpMapCompPi Q gG j
  have hLow := sliceCechComplexMapDegree_comp_π u E P Q K e hK n (gE.f j)
  have hHigh := sliceCechComplexMapDegree_comp_π u E P Q K e hK (n + 1) j
  let d : Fin (n + 1) → Fin (n + 2) :=
    (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ k)).toFun
  have hProd := cechProductMapOfFunctor_face_naturality u E n d j
  have hOver :
      (Over.post (X := X) u).map (gE.φ j) ≫ cechProductMapOfFunctor u E n (gE.f j) =
        cechProductMapOfFunctor u E (n + 1) j ≫ gG.φ j := by
    simpa [gE, gG, cechSimplicialObject, cechFormalCoproductMap, Function.comp_def, d]
      using hProd
  have hQ :
      Q.map (cechProductMapOfFunctor u E n (gE.f j)).op ≫
          Q.map ((Over.post (X := X) u).map (gE.φ j)).op =
        Q.map (gG.φ j).op ≫ Q.map (cechProductMapOfFunctor u E (n + 1) j).op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hOver]
  have hinv := inv_comp_map_of_partialIso u P Q K e he (hK n (gE.f j)) (hK (n + 1) j) (gE.φ j)
  conv_lhs => rw [Category.assoc, hEv, ← Category.assoc, hLow, Category.assoc, Category.assoc,
    hinv, ← Category.assoc (Q.map _), hQ]
  conv_rhs => rw [Category.assoc, hHigh, ← Category.assoc, hGv, Category.assoc]
  simp only [Category.assoc]
  congr 1

include he in
/-- The degreewise comparison maps commute with the differentials. -/
theorem sliceCechComplexMapDegree_comm (n : ℕ) :
    sliceCechComplexMapDegree u E P Q K e hK n ≫ (sliceCechComplex E P).d n (n + 1) =
      (sliceCechComplex (E.map u) Q).d n (n + 1) ≫
        sliceCechComplexMapDegree u E P Q K e hK (n + 1) := by
  show sliceCechComplexMapDegree u E P Q K e hK n ≫
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        ((FormalCoproduct.cosimplicialObjectFunctor.{w} (cechSimplicialObject E)).obj
          P)).d n (n + 1) =
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        ((FormalCoproduct.cosimplicialObjectFunctor.{w}
            (cechSimplicialObject (E.map u))).obj Q)).d n (n + 1) ≫
      sliceCechComplexMapDegree u E P Q K e hK (n + 1)
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  exact comp_objD_comm
    (XE := (FormalCoproduct.cosimplicialObjectFunctor.{w} (cechSimplicialObject E)).obj P)
    (XG := (FormalCoproduct.cosimplicialObjectFunctor.{w}
        (cechSimplicialObject (E.map u))).obj Q)
    (fun m ↦ sliceCechComplexMapDegree u E P Q K e hK m)
    (fun m l ↦ sliceCechComplexMapDegree_zsmul_δ_comm u E P Q K e he hK m l) n

omit [Preadditive A] in
attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.evalOp in
/-- If every comparison map of iterated fibre products in degree `n` is invertible, so is the
degree-`n` comparison of slice Čech complexes. -/
theorem isIso_sliceCechComplexMapDegree (n : ℕ)
    (h : ∀ i : Fin (n + 1) → E.I₀, IsIso (cechProductMapOfFunctor u E n i)) :
    IsIso (sliceCechComplexMapDegree u E P Q K e hK n) := by
  refine ⟨Pi.lift (fun i : ((cechSimplicialObject (E.map u)).obj
        (op (SimplexCategory.mk n))).I ↦
      Pi.π (fun l : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I ↦
          P.obj (op (((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).obj l))) i ≫
        (e _ (hK n i)).hom ≫ inv (Q.map (cechProductMapOfFunctor u E n i).op)), ?_, ?_⟩
  · apply Pi.hom_ext
    intro i
    have := h i
    rw [Category.assoc, Pi.lift_π, ← Category.assoc, sliceCechComplexMapDegree_comp_π]
    simp
  · apply Pi.hom_ext
    intro i
    have := h i
    rw [Category.assoc, sliceCechComplexMapDegree_comp_π, ← Category.assoc, Pi.lift_π]
    simp

include he in
/-- The comparison morphism of slice Čech complexes, degree by degree
`Stacks.CechSite.sliceCechComplexMapDegree`. -/
noncomputable def sliceCechComplexMap :
    sliceCechComplex (E.map u) Q ⟶ sliceCechComplex E P :=
  CochainComplex.ofHom (fun n ↦ sliceCechComplexMapDegree u E P Q K e hK n)
    (sliceCechComplexMapDegree_comm u E P Q K e he hK)

include he in
/-- The comparison morphism is invertible as soon as every comparison map of iterated fibre
products is. -/
theorem isIso_sliceCechComplexMap
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), IsIso (cechProductMapOfFunctor u E n i)) :
    IsIso (sliceCechComplexMap u E P Q K e he hK) := by
  have : ∀ n, IsIso ((sliceCechComplexMap u E P Q K e he hK).f n) := fun n ↦
    isIso_sliceCechComplexMapDegree u E P Q K e hK n (h n)
  exact HomologicalComplex.Hom.isIso_of_components _

include he in
/-- **The comparison of slice Čech complexes along a functor.** Coefficients `P` on `C/X` and
`Q` on `D/u(X)` which are identified, naturally, on a class of objects of `C/X` containing the
iterated fibre products of `E`, have isomorphic Čech complexes along `E` and along `u(E)`, as
soon as `u` preserves those fibre products. -/
noncomputable def sliceCechComplexIsoOfFunctor
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), IsIso (cechProductMapOfFunctor u E n i)) :
    sliceCechComplex (E.map u) Q ≅ sliceCechComplex E P :=
  haveI := isIso_sliceCechComplexMap u E P Q K e he hK h
  asIso (sliceCechComplexMap u E P Q K e he hK)

end Stacks.CechSite

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
  (u : C ⥤ D) {X : C} (E : PreZeroHypercover.{w} X)
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [∀ (n : ℕ) (i : Fin (n + 1) → (E.map u).I₀),
    HasProduct (fun a ↦ Over.mk ((E.map u).f (i a)))]

/-- Vanishing of the cohomology of the slice Čech complex of the image family transfers to the
original one. -/
theorem isZero_homology_sliceCechComplex_of_functor
    (P : (Over X)ᵒᵖ ⥤ A) (Q : (Over (u.obj X))ᵒᵖ ⥤ A) (K : ObjectProperty (Over X))
    (e : ∀ Y : Over X, K Y → (P.obj (op Y) ≅ Q.obj (op ((Over.post u).obj Y))))
    (he : ∀ {Y Y' : Over X} (hY : K Y) (hY' : K Y') (g : Y' ⟶ Y),
      P.map g.op ≫ (e Y' hY').hom = (e Y hY).hom ≫ Q.map ((Over.post u).map g).op)
    (hK : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), K (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))))
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), IsIso (cechProductMapOfFunctor u E n i))
    (p : ℕ) (hp : IsZero ((sliceCechComplex (E.map u) Q).homology p)) :
    IsZero ((sliceCechComplex E P).homology p) :=
  hp.of_iso ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).mapIso
    (sliceCechComplexIsoOfFunctor u E P Q K e he hK h)).symm

end Stacks.CechSite

end
