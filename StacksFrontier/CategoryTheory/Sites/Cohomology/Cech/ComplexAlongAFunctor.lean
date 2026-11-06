module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech complex along a functor between sites

Let `u : C ⥤ D` be a functor, let `E = {U_i → U}` be a family of morphisms of `C` with fixed
target, and let `I` be an additive presheaf on `D`. The image family `E.map u`, which is
`{u(U_i) → u(U)}`, has its own Čech complex of Stacks 03AM, and the restriction `u.op ⋙ I` of
`I` along `u` — the pullback `g⁻¹I` of Sites, Lemma 00XR when `u` is continuous and
cocontinuous — has a Čech complex with respect to `E` itself. This file relates the two.

The relation comes from the canonical comparison map
`u(U_{i_0} ×_U … ×_U U_{i_p}) ⟶ u(U_{i_0}) ×_{u(U)} … ×_{u(U)} u(U_{i_p})`,
which exists for any `u` whatsoever and is an isomorphism exactly when `u` preserves the
iterated fibre products in question — condition (2) of the definition of a continuous functor
of sites, Sites, Definition 00WV. Restricting `I` along that map, degree by degree, gives a
morphism of Čech complexes in the direction
`Č(u(E), I) ⟶ Č(E, u^p I)`,
which is an isomorphism as soon as every comparison map is.

## Main definitions

* `Stacks.CechSite.cechProductMapOfFunctor`: the comparison map between an iterated fibre
  product of the family and the corresponding iterated fibre product of its image, in the
  slice category over `u(U)`.
* `Stacks.CechSite.cechComplexMapOfFunctor`: the induced morphism of Čech complexes.
* `Stacks.CechSite.cechComplexIsoOfFunctor` and
  `Stacks.CechSite.cechCohomologyIsoOfFunctor`: that morphism as an isomorphism, and the
  resulting isomorphism of Čech cohomology objects, when `u` preserves the iterated fibre
  products of the family.

## Main results

* `Stacks.CechSite.isIso_cechProductMapOfFunctor`: a functor preserving the product of the
  selected objects of the slice category has an invertible comparison map.
* `Stacks.CechSite.cechCohomology_isZero_of_isZero_of_functor`: transfer of vanishing of Čech
  cohomology from the image family to the original one.

## Implementation notes

A family of morphisms with fixed target is a `PreZeroHypercover`, and its image under `u` is
Mathlib's `CategoryTheory.PreZeroHypercover.map`; the two families share their index type. The
iterated fibre products are, as in Stacks 03AM, the products of the selected objects of the
slice categories `Over U` and `Over (u.obj U)`, and the comparison map is the product
comparison map `CategoryTheory.Limits.piComparison` of `CategoryTheory.Over.post u`. Only the
existence of *those* products is assumed, for each of the two families separately: `u` is not
assumed to preserve them, and `Over U` is not assumed to have finite limits.

Because the two families have the same index type, the comparison morphism of Čech complexes
is degreewise a `CategoryTheory.Limits.Pi.map`, with no reindexing of the outer product; this
is what makes it invertible degreewise as soon as the comparison maps are, and distinguishes
the construction from the refinement map `Stacks.CechSite.cechComplexMap` of Stacks 03F4,
which moves the index.

The object and morphism universes of the two categories, the index universe of the family and
the universes of the coefficient category are all independent.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public section

universe w v v₂ v' u u₂ u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

-- The index type of the formal coproduct of the iterated fibre products of a family is, by
-- definition, the type of tuples of indices, and the image family shares its index type and
-- its selected objects with the original one only after `PreZeroHypercover.map` and
-- `Over.post` are unfolded. Both unfoldings have to be available at `implicit` transparency
-- for the two sides of the naturality squares below to be seen as composable.
attribute [local implicit_reducible] cechFormalCoproduct cechFormalCoproductMap
  CategoryTheory.PreZeroHypercover.map

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
  (u : C ⥤ D) {X : C} (E : PreZeroHypercover.{w} X)

section Comparison

variable [hE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [hEu : ∀ (n : ℕ) (i : Fin (n + 1) → (E.map u).I₀),
    HasProduct (fun a ↦ Over.mk ((E.map u).f (i a)))]

/-- The comparison map from the image under `u` of an iterated fibre product of the family `E`
to the corresponding iterated fibre product of the image family `E.map u`, as a morphism of the
slice category over `u(U)`. It exists for every functor `u`; it is invertible exactly when `u`
preserves that fibre product, which is condition (2) of Stacks 00WV. -/
noncomputable def cechProductMapOfFunctor (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    (Over.post (X := X) u).obj (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))) ⟶
      ∏ᶜ (fun a ↦ Over.mk ((E.map u).f (i a))) :=
  Pi.lift (fun a ↦ (Over.post (X := X) u).map (Pi.π (fun b ↦ Over.mk (E.f (i b))) a))

/-- The comparison map is the one determined by the images of the projections. -/
@[reassoc]
theorem cechProductMapOfFunctor_comp_π (n : ℕ) (i : Fin (n + 1) → E.I₀) (b : Fin (n + 1)) :
    cechProductMapOfFunctor u E n i ≫ Pi.π (fun a ↦ Over.mk ((E.map u).f (i a))) b =
      (Over.post (X := X) u).map (Pi.π (fun a ↦ Over.mk (E.f (i a))) b) :=
  Pi.lift_comp_π _ _

/-- The comparison map is the product comparison map of `Over.post u`. -/
theorem cechProductMapOfFunctor_eq_piComparison (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    letI : HasProduct (fun a ↦ (Over.post (X := X) u).obj (Over.mk (E.f (i a)))) := hEu n i
    cechProductMapOfFunctor u E n i =
      piComparison (Over.post (X := X) u) (fun a ↦ Over.mk (E.f (i a))) :=
  rfl

/-- A functor preserving the product, in the slice category, of the selected objects of a
tuple has an invertible comparison map for that tuple. -/
theorem isIso_cechProductMapOfFunctor (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.f (i a))))
      (Over.post (X := X) u)] :
    IsIso (cechProductMapOfFunctor u E n i) := by
  let : HasProduct (fun a ↦ (Over.post (X := X) u).obj (Over.mk (E.f (i a)))) := hEu n i
  exact inferInstanceAs
    (IsIso (piComparison (Over.post (X := X) u) (fun a ↦ Over.mk (E.f (i a)))))

/-- The underlying morphism of `D` of the comparison map is invertible as soon as the
comparison map is. -/
theorem isIso_cechProductMapOfFunctor_left (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [IsIso (cechProductMapOfFunctor u E n i)] :
    IsIso (cechProductMapOfFunctor u E n i).left :=
  inferInstanceAs (IsIso ((Over.forget (u.obj X)).map (cechProductMapOfFunctor u E n i)))

/-- The comparison maps are compatible with the reindexing maps between the formal coproducts
of the iterated fibre products. -/
theorem cechProductMapOfFunctor_face_naturality (n : ℕ) (d : Fin (n + 1) → Fin (n + 2))
    (i : Fin (n + 2) → E.I₀) :
    (Over.post (X := X) u).map ((cechFormalCoproductMap E d).φ i) ≫
        cechProductMapOfFunctor u E n (i ∘ d) =
      cechProductMapOfFunctor u E (n + 1) i ≫
        (cechFormalCoproductMap (E.map u) d).φ i := by
  refine Pi.hom_ext _ _ fun b ↦ ?_
  rw [Category.assoc, cechProductMapOfFunctor_comp_π, ← Functor.map_comp]
  simp only [Function.comp_apply]
  rw [cechFormalCoproductMap_φ_comp_π E d i b, Category.assoc,
    cechFormalCoproductMap_φ_comp_π (E.map u) d i b, cechProductMapOfFunctor_comp_π]

/-- The naturality square of the comparison maps, in `D`. -/
theorem cechProductMapOfFunctor_left_face_naturality (n : ℕ) (d : Fin (n + 1) → Fin (n + 2))
    (i : Fin (n + 2) → E.I₀) :
    u.map ((cechFormalCoproductMap E d).φ i).left ≫
        (cechProductMapOfFunctor u E n (i ∘ d)).left =
      (cechProductMapOfFunctor u E (n + 1) i).left ≫
        ((cechFormalCoproductMap (E.map u) d).φ i).left := by
  have h := congrArg Over.Hom.left (cechProductMapOfFunctor_face_naturality u E n d i)
  rw [Over.comp_left, Over.comp_left] at h
  exact h

end Comparison

section Complex

variable [hE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [hEu : ∀ (n : ℕ) (i : Fin (n + 1) → (E.map u).I₀),
    HasProduct (fun a ↦ Over.mk ((E.map u).f (i a)))]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]

/-- The degree-`n` component of the comparison morphism of Čech complexes: on the factor
indexed by a tuple `i`, restriction of the coefficients along the comparison map of the
iterated fibre product of `i`. The two Čech complexes have the same indexing type in each
degree, so no reindexing of the outer product is involved. -/
noncomputable def cechComplexMapOfFunctorDegree (I : Dᵒᵖ ⥤ A) (n : ℕ) :
    ((FormalCoproduct.evalOp.{w} (Over (u.obj X)) A).obj
        ((Over.forget (u.obj X)).op ⋙ I)).obj
        (op ((cechSimplicialObject (E.map u)).obj (op (SimplexCategory.mk n)))) ⟶
      ((FormalCoproduct.evalOp.{w} (Over X) A).obj ((Over.forget X).op ⋙ u.op ⋙ I)).obj
        (op ((cechSimplicialObject E).obj (op (SimplexCategory.mk n)))) :=
  Pi.lift (fun i : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I ↦
    Pi.π (fun l : ((cechSimplicialObject (E.map u)).obj (op (SimplexCategory.mk n))).I ↦
        ((Over.forget (u.obj X)).op ⋙ I).obj
          (op (((cechSimplicialObject (E.map u)).obj
            (op (SimplexCategory.mk n))).obj l))) i ≫
      I.map (cechProductMapOfFunctor u E n i).left.op)

omit [Preadditive A] in
/-- In degree `n`, the component of the degreewise comparison map indexed by a tuple `i` is
restriction along the comparison map of the iterated fibre product of `i`. -/
@[reassoc]
theorem cechComplexMapOfFunctorDegree_comp_π (I : Dᵒᵖ ⥤ A) (n : ℕ)
    (i : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I) :
    cechComplexMapOfFunctorDegree u E I n ≫
        Pi.π (fun l : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I ↦
          ((Over.forget X).op ⋙ u.op ⋙ I).obj
            (op (((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).obj l))) i =
      Pi.π (fun l : ((cechSimplicialObject (E.map u)).obj
            (op (SimplexCategory.mk n))).I ↦
          ((Over.forget (u.obj X)).op ⋙ I).obj
            (op (((cechSimplicialObject (E.map u)).obj
              (op (SimplexCategory.mk n))).obj l))) i ≫
        I.map (cechProductMapOfFunctor u E n i).left.op :=
  Pi.lift_comp_π _ _

attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.evalOp in
/-- The degreewise comparison maps commute with each signed coface map of the cosimplicial
objects whose alternating-coface complexes are the two Čech complexes. -/
theorem cechComplexMapOfFunctorDegree_zsmul_δ_comm (I : Dᵒᵖ ⥤ A) (n : ℕ) (k : Fin (n + 2)) :
    cechComplexMapOfFunctorDegree u E I n ≫
        ((-1 : ℤ) ^ (k : ℕ) •
          ((FormalCoproduct.evalOp.{w} (Over X) A).obj
              ((Over.forget X).op ⋙ u.op ⋙ I)).map
            ((cechSimplicialObject E).map (SimplexCategory.δ k).op).op) =
      ((-1 : ℤ) ^ (k : ℕ) •
          ((FormalCoproduct.evalOp.{w} (Over (u.obj X)) A).obj
              ((Over.forget (u.obj X)).op ⋙ I)).map
            ((cechSimplicialObject (E.map u)).map (SimplexCategory.δ k).op).op) ≫
        cechComplexMapOfFunctorDegree u E I (n + 1) := by
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  refine congrArg (fun z ↦ ((-1 : ℤ) ^ (k : ℕ)) • z) (Pi.hom_ext _ _ fun j ↦ ?_)
  set gE := (cechSimplicialObject E).map (SimplexCategory.δ k).op with hgE
  set gG := (cechSimplicialObject (E.map u)).map (SimplexCategory.δ k).op with hgG
  have hE := evalOpMapCompPi ((Over.forget X).op ⋙ u.op ⋙ I) gE j
  have hG := evalOpMapCompPi ((Over.forget (u.obj X)).op ⋙ I) gG j
  have hLow := cechComplexMapOfFunctorDegree_comp_π u E I n (gE.f j)
  have hHigh := cechComplexMapOfFunctorDegree_comp_π u E I (n + 1) j
  let d : Fin (n + 1) → Fin (n + 2) :=
    (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ k)).toFun
  have hProd := cechProductMapOfFunctor_left_face_naturality u E n d j
  have hOver :
      u.map (Over.Hom.left (gE.φ j)) ≫ (cechProductMapOfFunctor u E n (gE.f j)).left =
        (cechProductMapOfFunctor u E (n + 1) j).left ≫ Over.Hom.left (gG.φ j) := by
    simpa [gE, gG, cechSimplicialObject, cechFormalCoproductMap, Function.comp_def, d]
      using hProd
  have hFMap :
      I.map (cechProductMapOfFunctor u E n (gE.f j)).left.op ≫
          I.map (u.map (Over.Hom.left (gE.φ j))).op =
        I.map (Over.Hom.left (gG.φ j)).op ≫
          I.map (cechProductMapOfFunctor u E (n + 1) j).left.op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hOver]
  conv_lhs => rw [Category.assoc, hE, ← Category.assoc, hLow, Category.assoc]
  conv_rhs => rw [Category.assoc, hHigh, ← Category.assoc, hG, Category.assoc]
  simp only [Functor.comp_map, Functor.op_map, Over.forget_map, Quiver.Hom.unop_op]
  rw [hFMap]
  congr 1

/-- The degreewise comparison maps commute with the differentials of the two Čech complexes. -/
theorem cechComplexMapOfFunctorDegree_comm (I : Dᵒᵖ ⥤ A) (n : ℕ) :
    cechComplexMapOfFunctorDegree u E I n ≫ (cechComplex E (u.op ⋙ I)).d n (n + 1) =
      (cechComplex (E.map u) I).d n (n + 1) ≫
        cechComplexMapOfFunctorDegree u E I (n + 1) := by
  change cechComplexMapOfFunctorDegree u E I n ≫
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        ((FormalCoproduct.cosimplicialObjectFunctor.{w} (cechSimplicialObject E)).obj
          ((Over.forget X).op ⋙ u.op ⋙ I))).d n (n + 1) =
    (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        ((FormalCoproduct.cosimplicialObjectFunctor.{w}
            (cechSimplicialObject (E.map u))).obj
          ((Over.forget (u.obj X)).op ⋙ I))).d n (n + 1) ≫
      cechComplexMapOfFunctorDegree u E I (n + 1)
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  exact comp_objD_comm
    (XE := (FormalCoproduct.cosimplicialObjectFunctor.{w} (cechSimplicialObject E)).obj
      ((Over.forget X).op ⋙ u.op ⋙ I))
    (XG := (FormalCoproduct.cosimplicialObjectFunctor.{w}
        (cechSimplicialObject (E.map u))).obj
      ((Over.forget (u.obj X)).op ⋙ I))
    (fun m ↦ cechComplexMapOfFunctorDegree u E I m)
    (fun m l ↦ cechComplexMapOfFunctorDegree_zsmul_δ_comm u E I m l) n

omit [Preadditive A] in
attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.evalOp in
/-- If every comparison map of iterated fibre products in degree `n` is invertible, so is the
degree-`n` comparison map of Čech complexes. -/
theorem isIso_cechComplexMapOfFunctorDegree (I : Dᵒᵖ ⥤ A) (n : ℕ)
    (h : ∀ i : Fin (n + 1) → E.I₀, IsIso (cechProductMapOfFunctor u E n i)) :
    IsIso (cechComplexMapOfFunctorDegree u E I n) := by
  have hcmp : ∀ i : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I,
      IsIso (I.map (cechProductMapOfFunctor u E n i).left.op) := by
    intro i
    have := h i
    have : IsIso (cechProductMapOfFunctor u E n i).left :=
      isIso_cechProductMapOfFunctor_left u E n i
    infer_instance
  refine ⟨Pi.lift (fun i : ((cechSimplicialObject (E.map u)).obj
        (op (SimplexCategory.mk n))).I ↦
      Pi.π (fun l : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I ↦
          ((Over.forget X).op ⋙ u.op ⋙ I).obj
            (op (((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).obj l))) i ≫
        inv (I.map (cechProductMapOfFunctor u E n i).left.op)), ?_, ?_⟩
  · refine Pi.hom_ext _ _ fun i ↦ ?_
    rw [Category.assoc, Pi.lift_comp_π, ← Category.assoc,
      cechComplexMapOfFunctorDegree_comp_π, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · refine Pi.hom_ext _ _ fun i ↦ ?_
    rw [Category.assoc, cechComplexMapOfFunctorDegree_comp_π, ← Category.assoc,
      Pi.lift_comp_π, Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- **Čech functoriality along a functor of sites.** The morphism of Čech complexes from the
Čech complex of the image family `{u(U_i) → u(U)}` with coefficients in a presheaf `I` on `D`
to the Čech complex of `{U_i → U}` with coefficients in the restriction `u^p I = I ∘ u` — the
pullback `g⁻¹I` of Sites, Lemma 00XR when `u` is continuous and cocontinuous. It is induced by
restricting `I` along the comparison maps of the iterated fibre products. -/
noncomputable def cechComplexMapOfFunctor (I : Dᵒᵖ ⥤ A) :
    cechComplex (E.map u) I ⟶ cechComplex E (u.op ⋙ I) :=
  CochainComplex.ofHom (fun n ↦ cechComplexMapOfFunctorDegree u E I n)
    (cechComplexMapOfFunctorDegree_comm u E I)

/-- In degree `n`, the component of `cechComplexMapOfFunctor` indexed by a tuple `i` is
restriction along the comparison map of the iterated fibre product of `i`. -/
theorem cechComplexMapOfFunctor_f_Pi_π (I : Dᵒᵖ ⥤ A) (n : ℕ)
    (i : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I) :
    (cechComplexMapOfFunctor u E I).f n ≫
        Pi.π (fun l : ((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).I ↦
          ((Over.forget X).op ⋙ u.op ⋙ I).obj
            (op (((cechSimplicialObject E).obj (op (SimplexCategory.mk n))).obj l))) i =
      Pi.π (fun l : ((cechSimplicialObject (E.map u)).obj
            (op (SimplexCategory.mk n))).I ↦
          ((Over.forget (u.obj X)).op ⋙ I).obj
            (op (((cechSimplicialObject (E.map u)).obj
              (op (SimplexCategory.mk n))).obj l))) i ≫
        I.map (cechProductMapOfFunctor u E n i).left.op :=
  cechComplexMapOfFunctorDegree_comp_π u E I n i

/-- If every comparison map of iterated fibre products is invertible — for instance if `u`
preserves those fibre products, which is condition (2) of Stacks 00WV — then the comparison
morphism of Čech complexes is an isomorphism. -/
theorem isIso_cechComplexMapOfFunctor (I : Dᵒᵖ ⥤ A)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), IsIso (cechProductMapOfFunctor u E n i)) :
    IsIso (cechComplexMapOfFunctor u E I) := by
  have hdeg : ∀ n : ℕ, IsIso ((cechComplexMapOfFunctor u E I).f n) := fun n ↦
    isIso_cechComplexMapOfFunctorDegree u E I n (h n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Čech functoriality along a functor of sites, as an isomorphism.** When `u` preserves the
iterated fibre products of the family `E`, the Čech complex of the image family with
coefficients in `I` is isomorphic to the Čech complex of `E` with coefficients in the
restriction of `I` along `u`. -/
noncomputable def cechComplexIsoOfFunctor (I : Dᵒᵖ ⥤ A)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), IsIso (cechProductMapOfFunctor u E n i)) :
    cechComplex (E.map u) I ≅ cechComplex E (u.op ⋙ I) :=
  have := isIso_cechComplexMapOfFunctor u E I h
  asIso (cechComplexMapOfFunctor u E I)

end Complex

section Cohomology

variable [hE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [hEu : ∀ (n : ℕ) (i : Fin (n + 1) → (E.map u).I₀),
    HasProduct (fun a ↦ Over.mk ((E.map u).f (i a)))]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]

/-- **Čech cohomology along a functor of sites.** When `u` preserves the iterated fibre
products of `E`, the Čech cohomology of the image family with coefficients in `I` agrees with
the Čech cohomology of `E` with coefficients in the restriction of `I` along `u`. This is the
displayed identification `Ȟ^p(u(𝒰), I) = Ȟ^p(𝒰, g⁻¹I)` in the proof of Stacks 0D6X. -/
noncomputable def cechCohomologyIsoOfFunctor (I : Dᵒᵖ ⥤ A)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), IsIso (cechProductMapOfFunctor u E n i))
    (p : ℕ) :
    cechCohomology (E.map u) I p ≅ cechCohomology E (u.op ⋙ I) p :=
  (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).mapIso
    (cechComplexIsoOfFunctor u E I h)

/-- Vanishing of the Čech cohomology of the image family transfers to the original family,
when `u` preserves the iterated fibre products of the family. -/
theorem cechCohomology_isZero_of_isZero_of_functor (I : Dᵒᵖ ⥤ A)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), IsIso (cechProductMapOfFunctor u E n i))
    (p : ℕ) (hp : IsZero (cechCohomology (E.map u) I p)) :
    IsZero (cechCohomology E (u.op ⋙ I) p) :=
  hp.of_iso (cechCohomologyIsoOfFunctor u E I h p).symm

end Cohomology

end Stacks.CechSite
