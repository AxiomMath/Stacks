module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOnTheSlice

/-!
# The Čech complex along a functor defined only on the slice at the target

Let `E = {U_i → X}` be a family of morphisms of `C` with target `X`, and let
`v : Over X ⥤ Over V` be a functor between slice categories, for an object `V` of a category `D`.
This file compares the slice Čech complex of `E` with coefficients in the restriction `v^p P` of a
presheaf `P` on `Over V` with the slice Čech complex, with coefficients in `P`, of the image family
of `E` under `v`, and shows that the comparison is an isomorphism when `v` preserves the iterated
fibre products `U_{i_0} ×_X ⋯ ×_X U_{i_p}`.

## Main definitions

* `Stacks.CechSite.sliceImageFamily`: the image of a family under a functor defined on the
  slice at its target.  Its members are the total spaces of the images of the selected objects
  of the slice, and `Stacks.CechSite.overMk_sliceImageFamily_f` says that the selected objects
  of the image family are, on the nose, the images of the selected objects.
* `Stacks.CechSite.cechProductMapOfSliceFunctor`: the comparison map from the image of an
  iterated fibre product of the family to the iterated fibre product of the image family.
* `Stacks.CechSite.sliceCechComplexMapOfSliceFunctor` and
  `Stacks.CechSite.sliceCechComplexIsoOfSliceFunctor`: the induced morphism of slice Čech
  complexes, and that morphism as an isomorphism when the functor preserves the iterated fibre
  products of the family.
* `Stacks.CechSite.sliceCechCohomologyIsoOfSliceFunctor`: the resulting isomorphism of Čech
  cohomology objects.

## Main results

* `Stacks.CechSite.isIso_cechProductMapOfSliceFunctor`: a functor preserving the product, in
  the slice, of the selected objects of a tuple has an invertible comparison map.
* `Stacks.CechSite.isZero_sliceCechCohomology_of_isZero_of_sliceFunctor`: transfer of vanishing
  of Čech cohomology from the image family to the original one.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public section

universe w v v₂ v' u u₂ u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] cechFormalCoproduct cechFormalCoproductMap

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  {D : Type u₂} [Category.{v₂} D] {V : D} (v : Over X ⥤ Over V)

/-- The image of a family of morphisms with target `X` under a functor defined on the slice at
`X`: the member indexed by `i` is the total space of the image of the selected object
`Over.mk (E.f i)`, with the structure morphism of that image as its morphism to `V`. -/
public def sliceImageFamily : PreZeroHypercover.{w} V where
  I₀ := E.I₀
  X i := (v.obj (Over.mk (E.f i))).left
  f i := (v.obj (Over.mk (E.f i))).hom

attribute [local implicit_reducible] sliceImageFamily

/-- The selected object of the slice at `V` attached to a member of the image family is, on the
nose, the image of the selected object attached to the corresponding member of `E`. -/
public theorem overMk_sliceImageFamily_f (i : E.I₀) :
    Over.mk ((sliceImageFamily E v).f i) = v.obj (Over.mk (E.f i)) :=
  rfl

/-- The index type of the image family is that of the original family. -/
public theorem sliceImageFamily_I₀ : (sliceImageFamily E v).I₀ = E.I₀ :=
  rfl

section Comparison

variable [hE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [hEv : ∀ (n : ℕ) (i : Fin (n + 1) → (sliceImageFamily E v).I₀),
    HasProduct (fun a ↦ Over.mk ((sliceImageFamily E v).f (i a)))]

/-- The comparison map from the image under `v` of an iterated fibre product of the family `E`
to the corresponding iterated fibre product of the image family, as a morphism of the slice at
`V`.  It exists for every `v`; it is invertible exactly when `v` preserves that fibre product,
which is condition (2) of [Stacks, Tag 00WV]. -/
public noncomputable def cechProductMapOfSliceFunctor (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    v.obj (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))) ⟶
      ∏ᶜ (fun a ↦ Over.mk ((sliceImageFamily E v).f (i a))) :=
  Pi.lift (fun a ↦ v.map (Pi.π (fun b ↦ Over.mk (E.f (i b))) a))

/-- The comparison map is the one determined by the images of the projections. -/
@[reassoc]
public theorem cechProductMapOfSliceFunctor_comp_π (n : ℕ) (i : Fin (n + 1) → E.I₀)
    (b : Fin (n + 1)) :
    cechProductMapOfSliceFunctor E v n i ≫
        Pi.π (fun a ↦ Over.mk ((sliceImageFamily E v).f (i a))) b =
      v.map (Pi.π (fun a ↦ Over.mk (E.f (i a))) b) :=
  Pi.lift_π _ _

/-- The comparison map is the product comparison map of `v`. -/
public theorem cechProductMapOfSliceFunctor_eq_piComparison (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    letI : HasProduct (fun a ↦ v.obj (Over.mk (E.f (i a)))) := hEv n i
    cechProductMapOfSliceFunctor E v n i =
      piComparison v (fun a ↦ Over.mk (E.f (i a))) :=
  rfl

/-- A functor preserving the product, in the slice at `X`, of the selected objects of a tuple
has an invertible comparison map for that tuple. -/
public theorem isIso_cechProductMapOfSliceFunctor (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.f (i a)))) v] :
    IsIso (cechProductMapOfSliceFunctor E v n i) := by
  let : HasProduct (fun a ↦ v.obj (Over.mk (E.f (i a)))) := hEv n i
  exact inferInstanceAs (IsIso (piComparison v (fun a ↦ Over.mk (E.f (i a)))))

/-- The comparison maps are compatible with the reindexing maps between the formal coproducts of
the iterated fibre products. -/
public theorem cechProductMapOfSliceFunctor_face_naturality (n : ℕ)
    (d : Fin (n + 1) → Fin (n + 2)) (i : Fin (n + 2) → E.I₀) :
    v.map ((cechFormalCoproductMap E d).φ i) ≫ cechProductMapOfSliceFunctor E v n (i ∘ d) =
      cechProductMapOfSliceFunctor E v (n + 1) i ≫
        (cechFormalCoproductMap (sliceImageFamily E v) d).φ i := by
  apply Pi.hom_ext
  intro b
  rw [Category.assoc, cechProductMapOfSliceFunctor_comp_π, ← Functor.map_comp]
  simp only [Function.comp_apply]
  rw [cechFormalCoproductMap_φ_comp_π E d i b, Category.assoc,
    cechFormalCoproductMap_φ_comp_π (sliceImageFamily E v) d i b,
    cechProductMapOfSliceFunctor_comp_π]

end Comparison

section Complex

variable [hE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [hEv : ∀ (n : ℕ) (i : Fin (n + 1) → (sliceImageFamily E v).I₀),
    HasProduct (fun a ↦ Over.mk ((sliceImageFamily E v).f (i a)))]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]

/-- The degree-`n` component of the comparison morphism of slice Čech complexes: on the factor
indexed by a tuple `i`, restriction of the coefficients along the comparison map of the iterated
fibre product of `i`. -/
public noncomputable def sliceCechComplexMapOfSliceFunctorDegree (P : (Over V)ᵒᵖ ⥤ A) (n : ℕ) :
    ((FormalCoproduct.evalOp.{w} (Over V) A).obj P).obj
        (op ((cechSimplicialObject (sliceImageFamily E v)).obj (op (SimplexCategory.mk n)))) ⟶
      ((FormalCoproduct.evalOp.{w} (Over X) A).obj (v.op ⋙ P)).obj
        (op ((cechSimplicialObject E).obj (op (SimplexCategory.mk n)))) :=
  Pi.lift (fun i : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I ↦
    Pi.π (fun l : ((cechSimplicialObject (sliceImageFamily E v)).obj
          (op (SimplexCategory.mk n))).I ↦
        P.obj (op (((cechSimplicialObject (sliceImageFamily E v)).obj
          (op (SimplexCategory.mk n))).obj l))) i ≫
      P.map (cechProductMapOfSliceFunctor E v n i).op)

omit [Preadditive A] in
/-- In degree `n`, the component of the degreewise comparison map indexed by a tuple `i` is
restriction along the comparison map of the iterated fibre product of `i`. -/
@[reassoc]
public theorem sliceCechComplexMapOfSliceFunctorDegree_comp_π (P : (Over V)ᵒᵖ ⥤ A) (n : ℕ)
    (i : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I) :
    sliceCechComplexMapOfSliceFunctorDegree E v P n ≫
        Pi.π (fun l : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I ↦
          (v.op ⋙ P).obj
            (op (((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).obj l))) i =
      Pi.π (fun l : ((cechSimplicialObject (sliceImageFamily E v)).obj
            (op (SimplexCategory.mk n))).I ↦
          P.obj (op (((cechSimplicialObject (sliceImageFamily E v)).obj
            (op (SimplexCategory.mk n))).obj l))) i ≫
        P.map (cechProductMapOfSliceFunctor E v n i).op :=
  Pi.lift_π _ _

attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.evalOp in
/-- The degreewise comparison maps commute with each signed coface map of the cosimplicial
objects whose alternating-coface complexes are the two slice Čech complexes. -/
public theorem sliceCechComplexMapOfSliceFunctorDegree_zsmul_δ_comm (P : (Over V)ᵒᵖ ⥤ A)
    (n : ℕ) (k : Fin (n + 2)) :
    sliceCechComplexMapOfSliceFunctorDegree E v P n ≫
        ((-1 : ℤ) ^ (k : ℕ) •
          ((FormalCoproduct.evalOp.{w} (Over X) A).obj (v.op ⋙ P)).map
            ((cechSimplicialObject E).map (SimplexCategory.δ k).op).op) =
      ((-1 : ℤ) ^ (k : ℕ) •
          ((FormalCoproduct.evalOp.{w} (Over V) A).obj P).map
            ((cechSimplicialObject (sliceImageFamily E v)).map
              (SimplexCategory.δ k).op).op) ≫
        sliceCechComplexMapOfSliceFunctorDegree E v P (n + 1) := by
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  refine congrArg (fun z ↦ ((-1 : ℤ) ^ (k : ℕ)) • z) ?_
  apply Pi.hom_ext
  intro j
  set gE := (cechSimplicialObject E).map (SimplexCategory.δ k).op
  set gG := (cechSimplicialObject (sliceImageFamily E v)).map (SimplexCategory.δ k).op
  have hEv' := evalOpMapCompPi (v.op ⋙ P) gE j
  have hGv := evalOpMapCompPi P gG j
  have hLow := sliceCechComplexMapOfSliceFunctorDegree_comp_π E v P n (gE.f j)
  have hHigh := sliceCechComplexMapOfSliceFunctorDegree_comp_π E v P (n + 1) j
  let d : Fin (n + 1) → Fin (n + 2) :=
    (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ k)).toFun
  have hProd := cechProductMapOfSliceFunctor_face_naturality E v n d j
  have hOver :
      v.map (gE.φ j) ≫ cechProductMapOfSliceFunctor E v n (gE.f j) =
        cechProductMapOfSliceFunctor E v (n + 1) j ≫ gG.φ j := by
    simpa [gE, gG, cechSimplicialObject, cechFormalCoproductMap, Function.comp_def, d]
      using hProd
  have hFMap :
      P.map (cechProductMapOfSliceFunctor E v n (gE.f j)).op ≫
          P.map (v.map (gE.φ j)).op =
        P.map (gG.φ j).op ≫ P.map (cechProductMapOfSliceFunctor E v (n + 1) j).op := by
    have hOpp :
        (cechProductMapOfSliceFunctor E v n (gE.f j)).op ≫ (v.map (gE.φ j)).op =
          (gG.φ j).op ≫ (cechProductMapOfSliceFunctor E v (n + 1) j).op := by
      rw [← op_comp, ← op_comp, hOver]
    rw [← Functor.map_comp, ← Functor.map_comp, hOpp]
  conv_lhs => rw [Category.assoc, hEv', ← Category.assoc, hLow, Category.assoc]
  conv_rhs => rw [Category.assoc, hHigh, ← Category.assoc, hGv, Category.assoc]
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
  rw [hFMap]
  congr 1

/-- The degreewise comparison maps commute with the differentials of the two slice Čech
complexes. -/
public theorem sliceCechComplexMapOfSliceFunctorDegree_comm (P : (Over V)ᵒᵖ ⥤ A) (n : ℕ) :
    sliceCechComplexMapOfSliceFunctorDegree E v P n ≫
        (sliceCechComplex E (v.op ⋙ P)).d n (n + 1) =
      (sliceCechComplex (sliceImageFamily E v) P).d n (n + 1) ≫
        sliceCechComplexMapOfSliceFunctorDegree E v P (n + 1) := by
  show sliceCechComplexMapOfSliceFunctorDegree E v P n ≫
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        ((FormalCoproduct.cosimplicialObjectFunctor.{w} (cechSimplicialObject E)).obj
          (v.op ⋙ P))).d n (n + 1) =
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        ((FormalCoproduct.cosimplicialObjectFunctor.{w}
            (cechSimplicialObject (sliceImageFamily E v))).obj P)).d n (n + 1) ≫
      sliceCechComplexMapOfSliceFunctorDegree E v P (n + 1)
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  exact comp_objD_comm
    (XE := (FormalCoproduct.cosimplicialObjectFunctor.{w} (cechSimplicialObject E)).obj
      (v.op ⋙ P))
    (XG := (FormalCoproduct.cosimplicialObjectFunctor.{w}
        (cechSimplicialObject (sliceImageFamily E v))).obj P)
    (fun m ↦ sliceCechComplexMapOfSliceFunctorDegree E v P m)
    (fun m l ↦ sliceCechComplexMapOfSliceFunctorDegree_zsmul_δ_comm E v P m l) n

omit [Preadditive A] in
attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.evalOp in
/-- If every comparison map of iterated fibre products in degree `n` is invertible, so is the
degree-`n` comparison map of slice Čech complexes. -/
public theorem isIso_sliceCechComplexMapOfSliceFunctorDegree (P : (Over V)ᵒᵖ ⥤ A) (n : ℕ)
    (h : ∀ i : Fin (n + 1) → E.I₀, IsIso (cechProductMapOfSliceFunctor E v n i)) :
    IsIso (sliceCechComplexMapOfSliceFunctorDegree E v P n) := by
  have hcmp : ∀ i : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I,
      IsIso (P.map (cechProductMapOfSliceFunctor E v n i).op) := fun i ↦
    have := h i
    inferInstance
  refine ⟨Pi.lift (fun i : ((cechSimplicialObject (sliceImageFamily E v)).obj
        (op (SimplexCategory.mk n))).I ↦
      Pi.π (fun l : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I ↦
          (v.op ⋙ P).obj
            (op (((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).obj l))) i ≫
        inv (P.map (cechProductMapOfSliceFunctor E v n i).op)), ?_, ?_⟩
  · apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_π, ← Category.assoc,
      sliceCechComplexMapOfSliceFunctorDegree_comp_π, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · apply Pi.hom_ext
    intro i
    rw [Category.assoc, sliceCechComplexMapOfSliceFunctorDegree_comp_π, ← Category.assoc,
      Pi.lift_π, Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- **Čech functoriality along a functor defined on the slice at the target.**  The morphism of
slice Čech complexes from the Čech complex of the image family with coefficients in a presheaf
`P` on the slice at `V` to the Čech complex of `E` with coefficients in the restriction
`v^p P = P ∘ v`. -/
public noncomputable def sliceCechComplexMapOfSliceFunctor (P : (Over V)ᵒᵖ ⥤ A) :
    sliceCechComplex (sliceImageFamily E v) P ⟶ sliceCechComplex E (v.op ⋙ P) :=
  CochainComplex.ofHom (fun n ↦ sliceCechComplexMapOfSliceFunctorDegree E v P n)
    (sliceCechComplexMapOfSliceFunctorDegree_comm E v P)

/-- If `v` preserves the iterated fibre products of the family — condition (2) of
[Stacks, Tag 00WV] — then the comparison morphism of slice Čech complexes is an
isomorphism. -/
public theorem isIso_sliceCechComplexMapOfSliceFunctor (P : (Over V)ᵒᵖ ⥤ A)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), IsIso (cechProductMapOfSliceFunctor E v n i)) :
    IsIso (sliceCechComplexMapOfSliceFunctor E v P) := by
  have hdeg : ∀ n : ℕ, IsIso ((sliceCechComplexMapOfSliceFunctor E v P).f n) := fun n ↦
    isIso_sliceCechComplexMapOfSliceFunctorDegree E v P n (h n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Čech functoriality along a functor defined on the slice at the target, as an
isomorphism.**  When `v` preserves the iterated fibre products of the family `E`, the Čech
complex of the image family with coefficients in `P` is isomorphic to the Čech complex of `E`
with coefficients in the restriction of `P` along `v`. -/
public noncomputable def sliceCechComplexIsoOfSliceFunctor (P : (Over V)ᵒᵖ ⥤ A)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), IsIso (cechProductMapOfSliceFunctor E v n i)) :
    sliceCechComplex (sliceImageFamily E v) P ≅ sliceCechComplex E (v.op ⋙ P) :=
  have := isIso_sliceCechComplexMapOfSliceFunctor E v P h
  asIso (sliceCechComplexMapOfSliceFunctor E v P)

end Complex

section Cohomology

variable [hE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [hEv : ∀ (n : ℕ) (i : Fin (n + 1) → (sliceImageFamily E v).I₀),
    HasProduct (fun a ↦ Over.mk ((sliceImageFamily E v).f (i a)))]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]

/-- **Čech cohomology along a functor defined on the slice at the target.**  When `v` preserves
the iterated fibre products of `E`, the Čech cohomology of the image family with coefficients in
`P` agrees with the Čech cohomology of `E` with coefficients in the restriction of `P`
along `v`. -/
public noncomputable def sliceCechCohomologyIsoOfSliceFunctor (P : (Over V)ᵒᵖ ⥤ A)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), IsIso (cechProductMapOfSliceFunctor E v n i))
    (p : ℕ) :
    sliceCechCohomology (sliceImageFamily E v) P p ≅ sliceCechCohomology E (v.op ⋙ P) p :=
  (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).mapIso
    (sliceCechComplexIsoOfSliceFunctor E v P h)

/-- **Vanishing of Čech cohomology transfers from the image family to the original one**, when
the functor on the slice preserves the iterated fibre products of the family. -/
public theorem isZero_sliceCechCohomology_of_isZero_of_sliceFunctor (P : (Over V)ᵒᵖ ⥤ A)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), IsIso (cechProductMapOfSliceFunctor E v n i))
    (p : ℕ) (hp : IsZero (sliceCechCohomology (sliceImageFamily E v) P p)) :
    IsZero (sliceCechCohomology E (v.op ⋙ P) p) :=
  hp.of_iso (sliceCechCohomologyIsoOfSliceFunctor E v P h p).symm

end Cohomology

end Stacks.CechSite

end
