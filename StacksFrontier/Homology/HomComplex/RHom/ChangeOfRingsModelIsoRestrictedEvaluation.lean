module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoMonoidalInverse

/-!
# The transpose in the model comparison of [stacks 0E1W] is a restricted evaluation

`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso` writes the
inverse of the model comparison `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` of
[stacks 0E1W] as a composite of five factors, one of which is the [stacks 0A63] transpose

`W = homEquiv (P ⊗ K) J ((extendScalarsMonoidalIso f P K).inv ≫ uncurry (ε Z)) ≫ q`,

where `Z = Hom_A(A ⊗_R K, J)` is the internal Hom complex over `A`, `P = Z|_R` is its restriction
to `R`, `ε` is the counit of degreewise extension--restriction and `q` is a K-injective resolution
of `J|_R`. This file shows that `W` is the **restricted evaluation**

`(𝟙 P ⊗ₘ η K) ≫ ρ ≫ (ev)|_R ≫ q`,

where `η` is the unit of degreewise extension--restriction, `ev : Z ⊗ (A ⊗_R K) ⟶ J` is the
evaluation of the internal Hom complex and `ρ` is the lax monoidal structure map
`CochainComplex.ExtendScalars.restrictScalarsLaxTensor` of restriction of scalars. The
underlying identity is the transposition of a strong monoidal left adjoint into a lax monoidal
right adjoint, `CategoryTheory.Adjunction.homEquiv_tensorHom_unit`.

## Main definitions

* `StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor` -- evaluation
  `Hom_R(L, M) ⊗ L ⟶ M` of the internal Hom complex, the uncurrying of the identity.
* `CochainComplex.ExtendScalars.extendRestrictScalarsComplexAdj` -- degreewise extension and
  restriction of scalars as an adjunction of categories of cochain complexes.
* `CochainComplex.ExtendScalars.restrictScalarsLaxTensor` -- the lax monoidal structure map
  `X|_R ⊗_R Y|_R ⟶ (X ⊗_S Y)|_R` of restriction of scalars, the transpose of the monoidality
  comparison of extension of scalars followed by the two counits.

## Main results

* `CategoryTheory.Adjunction.homEquiv_tensorHom_unit` -- for an adjunction `L ⊣ U` of monoidal
  categories and an oplax monoidality comparison for `L`, whiskering the unit into the second
  variable and transposing turns the counit in the second variable into an identity.
* `CochainComplex.ExtendScalars.extendScalarsMonoidalIso_inv_naturality` and
  `CochainComplex.ExtendScalars.extendScalarsMonoidalIso_inv_naturality_right` -- naturality of
  the inverse monoidality comparison of extension of scalars, in both variables and in the second.
* `CochainComplex.ExtendScalars.restrictScalarsLaxTensor_naturality` -- the lax monoidal
  structure map of restriction of scalars is natural in both variables.
* `StacksDraft.DerivedHom.DerivedInternalHom.Model.uncurry_comp_left` -- uncurrying is natural in
  its source variable, and
  `StacksDraft.DerivedHom.DerivedInternalHom.Model.uncurry_eq_tensorHom_evaluationMor`: every
  uncurrying is a tensor product followed by evaluation.
* `Stacks.DerivedHom.BaseChangeIso.homEquiv_monoidalIso_inv_uncurry_counit` and
  `Stacks.DerivedHom.BaseChangeIso.homEquiv_monoidalIso_inv_uncurry_counit_comp` -- the value of
  the transpose, without and with the resolution `q`.
* `Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_restrictedEvaluation`
  -- the inverse of the model comparison of [stacks 0E1W] with its transpose replaced by that
  value.

## Implementation notes

The statements in `Stacks.DerivedHom.BaseChangeIso` spell the adjunction as
`(ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (ComplexShape.up ℤ)` rather than as
the abbreviation `CochainComplex.ExtendScalars.extendRestrictScalarsComplexAdj`, as
`derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso` does, since keyed matching does not unfold
the abbreviation.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory

/-- A three-factor composite followed by a fourth factor, re-bracketed to the right. -/
theorem comp_four_assoc {C : Type*} [Category* C] {W X Y Z T : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ T) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp

end CategoryTheory

namespace CategoryTheory.Iso

/-- **A naturality square transposed across both of its isomorphisms.**  If `a` and `b` are
intertwined by the `hom` directions of `e₁` and `e₂`, then they are intertwined the other way
round by the `inv` directions. -/
theorem comp_inv_eq_inv_comp {C : Type*} [Category* C] {X Y X' Y' : C}
    (e₁ : X ≅ Y) (e₂ : X' ≅ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ e₂.hom = e₁.hom ≫ b) : b ≫ e₂.inv = e₁.inv ≫ a := by
  rw [Iso.comp_inv_eq, Category.assoc, h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end CategoryTheory.Iso

namespace CategoryTheory.Adjunction

/-- **Whiskering the unit into the second variable of a monoidality comparison, transposed.**

Let `L ⊣ U` be an adjunction between monoidal categories and let `mPK`, `mPU` be the components at
`(P, K)` and at `(P, U (L K))` of an oplax monoidality comparison for `L` -- that is, morphisms
`L (P ⊗ -) ⟶ L P ⊗ L -` -- whose naturality square along `adj.unit.app K` is `hm`.  Then
whiskering `adj.unit.app K` into the second variable and transposing across the adjunction turns
the counit `adj.counit.app (L K)` in the second variable into the identity. -/
theorem homEquiv_tensorHom_unit {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] {L : C ⥤ D} {U : D ⥤ C} (adj : L ⊣ U)
    {P K : C} {X Y : D}
    (mPK : L.obj (P ⊗ K) ⟶ L.obj P ⊗ L.obj K)
    (mPU : L.obj (P ⊗ U.obj (L.obj K)) ⟶ L.obj P ⊗ L.obj (U.obj (L.obj K)))
    (hm : L.map (𝟙 P ⊗ₘ adj.unit.app K) ≫ mPU =
      mPK ≫ (𝟙 (L.obj P) ⊗ₘ L.map (adj.unit.app K)))
    (g : L.obj P ⟶ X) (t : X ⊗ L.obj K ⟶ Y) :
    (𝟙 P ⊗ₘ adj.unit.app K) ≫
        adj.homEquiv (P ⊗ U.obj (L.obj K)) Y
          (mPU ≫ (g ⊗ₘ adj.counit.app (L.obj K)) ≫ t) =
      adj.homEquiv (P ⊗ K) Y (mPK ≫ (g ⊗ₘ 𝟙 (L.obj K)) ≫ t) := by
  have htri : (𝟙 (L.obj P) ⊗ₘ L.map (adj.unit.app K)) ≫ (g ⊗ₘ adj.counit.app (L.obj K)) =
      g ⊗ₘ 𝟙 (L.obj K) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    congr 1
    exact adj.left_triangle_components K
  have hchain : L.map (𝟙 P ⊗ₘ adj.unit.app K) ≫ mPU ≫ (g ⊗ₘ adj.counit.app (L.obj K)) ≫ t =
      mPK ≫ (g ⊗ₘ 𝟙 (L.obj K)) ≫ t := by
    rw [← Category.assoc, hm, Category.assoc, reassoc_of% htri]
  exact (adj.homEquiv_naturality_left (𝟙 P ⊗ₘ adj.unit.app K)
      (mPU ≫ (g ⊗ₘ adj.counit.app (L.obj K)) ≫ t)).symm.trans
    (congrArg (adj.homEquiv (P ⊗ K) Y) hchain)

end CategoryTheory.Adjunction

namespace StacksDraft.DerivedHom.DerivedInternalHom.Model

open CochainComplex CochainComplex.HomComplex HomologicalComplex

variable {R : Type u} [CommRing R]

/-- **Evaluation of the internal Hom complex**, `Hom_R(L, M) ⊗ L ⟶ M`: the uncurrying of the
identity of `Hom_R(L, M)` under the chain-level tensor--Hom adjunction of [stacks 0A63]. -/
public def evaluationMor (L M : CochainComplex (ModuleCat.{u} R) ℤ) :
    HomComplexR R L M ⊗ L ⟶ M :=
  uncurry (𝟙 (HomComplexR R L M))

/-- **Uncurrying is natural in its source variable.**  Precomposing before uncurrying is tensoring
with the identity of the test complex after it. -/
public lemma uncurry_comp_left {X P L M : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : X ⟶ P) (u : P ⟶ HomComplexR R L M) :
    uncurry (g ≫ u) = (g ⊗ₘ 𝟙 L) ≫ uncurry u := by
  ext n : 1
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  change (uncurry (g ≫ u)).f n ((ιTensorObj X L p q n hpq).hom (a ⊗ₜ[R] b)) =
    (uncurry u).f n ((g ⊗ₘ 𝟙 L).f n ((ιTensorObj X L p q n hpq).hom (a ⊗ₜ[R] b)))
  rw [uncurry_apply, tensorHom_apply, uncurry_apply]
  rfl

/-- **Every uncurrying factors through evaluation**: `uncurry u` is `u` tensored with the identity,
followed by `StacksDraft.DerivedHom.DerivedInternalHom.Model.evaluationMor`. -/
public lemma uncurry_eq_tensorHom_evaluationMor {P L M : CochainComplex (ModuleCat.{u} R) ℤ}
    (u : P ⟶ HomComplexR R L M) :
    uncurry u = (u ⊗ₘ 𝟙 L) ≫ evaluationMor L M :=
  (congrArg uncurry (Category.comp_id u)).symm.trans (uncurry_comp_left u (𝟙 _))

end StacksDraft.DerivedHom.DerivedInternalHom.Model

namespace CochainComplex.ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

local instance extendScalarsAdditiveRestrictedEvaluation :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **Degreewise extension and restriction of scalars as an adjunction of cochain complexes.**
`CategoryTheory.Adjunction.mapHomologicalComplex` applied to `ModuleCat.extendRestrictScalarsAdj`,
with its two functors named as `CochainComplex.ExtendScalars.mapCochainComplex` and
`CochainComplex.restrictScalarsLarge`. -/
public abbrev extendRestrictScalarsComplexAdj :
    mapCochainComplex f ⊣ CochainComplex.restrictScalarsLarge.{u, u, u} f :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The lax monoidal structure map of restriction of scalars on cochain complexes**:

`X|_R ⊗_R Y|_R ⟶ (X ⊗_S Y)|_R`.

Extension of scalars is strong monoidal, by
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, so its right adjoint is lax monoidal, and
the structure map is the transpose of

`L (X|_R ⊗_R Y|_R) ⟶ L (X|_R) ⊗_S L (Y|_R) ⟶ X ⊗_S Y`,

the inverse monoidality comparison followed by the counits in each variable. -/
public def restrictScalarsLaxTensor (X Y : CochainComplex (ModuleCat.{u} S) ℤ) :
    (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj X ⊗
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Y ⟶
      (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj (X ⊗ Y) :=
  (extendRestrictScalarsComplexAdj f).homEquiv _ _
    ((extendScalarsMonoidalIso f ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj X)
          ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Y)).inv ≫
      ((extendRestrictScalarsComplexAdj f).counit.app X ⊗ₘ
        (extendRestrictScalarsComplexAdj f).counit.app Y))

/-- **The lax structure map followed by the restriction of a morphism out of the tensor product**
is the transpose of the inverse monoidality comparison, followed by the two counits and the
morphism. -/
public theorem restrictScalarsLaxTensor_comp_map (X Y : CochainComplex (ModuleCat.{u} S) ℤ)
    {M : CochainComplex (ModuleCat.{u} S) ℤ} (t : X ⊗ Y ⟶ M) :
    restrictScalarsLaxTensor f X Y ≫ (CochainComplex.restrictScalarsLarge.{u, u, u} f).map t =
      (extendRestrictScalarsComplexAdj f).homEquiv _ M
        ((extendScalarsMonoidalIso f ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj X)
              ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Y)).inv ≫
          ((extendRestrictScalarsComplexAdj f).counit.app X ⊗ₘ
            (extendRestrictScalarsComplexAdj f).counit.app Y) ≫ t) := by
  rw [restrictScalarsLaxTensor, ← Adjunction.homEquiv_naturality_right, Category.assoc]

/-- **Naturality of the monoidality comparison, read in the `inv` direction**: the square of
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso_naturality` transposed across both
isomorphisms. -/
public theorem extendScalarsMonoidalIso_inv_naturality
    {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ} (a : K ⟶ K') (b : L ⟶ L') :
    (mapCochainComplex f).map (a ⊗ₘ b) ≫ (extendScalarsMonoidalIso f K' L').inv =
      (extendScalarsMonoidalIso f K L).inv ≫
        ((mapCochainComplex f).map a ⊗ₘ (mapCochainComplex f).map b) :=
  Iso.comp_inv_eq_inv_comp _ _ _ _ (extendScalarsMonoidalIso_naturality f a b)

/-- **The lax monoidal structure map of restriction of scalars is natural in both variables.** -/
public theorem restrictScalarsLaxTensor_naturality
    {X X' Y Y' : CochainComplex (ModuleCat.{u} S) ℤ} (a : X ⟶ X') (b : Y ⟶ Y') :
    ((CochainComplex.restrictScalarsLarge.{u, u, u} f).map a ⊗ₘ
          (CochainComplex.restrictScalarsLarge.{u, u, u} f).map b) ≫
        restrictScalarsLaxTensor f X' Y' =
      restrictScalarsLaxTensor f X Y ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map (a ⊗ₘ b) := by
  set adj := extendRestrictScalarsComplexAdj f
  have htens : ((mapCochainComplex f).map
          ((CochainComplex.restrictScalarsLarge.{u, u, u} f).map a) ⊗ₘ
        (mapCochainComplex f).map
          ((CochainComplex.restrictScalarsLarge.{u, u, u} f).map b)) ≫
        (adj.counit.app X' ⊗ₘ adj.counit.app Y') =
      (adj.counit.app X ⊗ₘ adj.counit.app Y) ≫ (a ⊗ₘ b) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    congr 1
    · exact adj.counit_naturality a
    · exact adj.counit_naturality b
  have hnat : (mapCochainComplex f).map
          ((CochainComplex.restrictScalarsLarge.{u, u, u} f).map a ⊗ₘ
            (CochainComplex.restrictScalarsLarge.{u, u, u} f).map b) ≫
        ((extendScalarsMonoidalIso f ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj X')
              ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Y')).inv ≫
          (adj.counit.app X' ⊗ₘ adj.counit.app Y')) =
      ((extendScalarsMonoidalIso f ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj X)
              ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Y)).inv ≫
            (adj.counit.app X ⊗ₘ adj.counit.app Y)) ≫ (a ⊗ₘ b) := by
    rw [← Category.assoc, extendScalarsMonoidalIso_inv_naturality, Category.assoc, htens,
      Category.assoc]
  exact ((adj.homEquiv_naturality_left _ _).symm.trans
    (congrArg (adj.homEquiv _ (X' ⊗ Y')) hnat)).trans
      (adj.homEquiv_naturality_right _ (a ⊗ₘ b))

/-- **Naturality of the monoidality comparison in the second variable, read in the `inv`
direction.** -/
public theorem extendScalarsMonoidalIso_inv_naturality_right
    (P : CochainComplex (ModuleCat.{u} R) ℤ) {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (b : K ⟶ K') :
    (mapCochainComplex f).map (𝟙 P ⊗ₘ b) ≫ (extendScalarsMonoidalIso f P K').inv =
      (extendScalarsMonoidalIso f P K).inv ≫
        (𝟙 ((mapCochainComplex f).obj P) ⊗ₘ (mapCochainComplex f).map b) := by
  simpa using extendScalarsMonoidalIso_inv_naturality f (𝟙 P) b

end CochainComplex.ExtendScalars

namespace Stacks.DerivedHom.BaseChangeIso

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

local instance extendScalarsAdditiveRestrictedEvaluation' :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **The value of the transpose in the model comparison of [stacks 0E1W].**

With `Z = Hom_A(A ⊗_R K, J)` the internal Hom complex over `A` and `P = Z|_R`, the [stacks 0A63]
transpose of the inverse monoidality comparison at `(P, K)` followed by the uncurried counit at
`Z` is the **restricted evaluation**

`(𝟙 P ⊗ₘ η K) ≫ ρ ≫ (ev)|_R`,

the unit of extension--restriction whiskered into the second variable, the lax monoidal structure
map `CochainComplex.ExtendScalars.restrictScalarsLaxTensor` of restriction of scalars, and the
restriction of the evaluation `Hom_A(A ⊗_R K, J) ⊗_A (A ⊗_R K) ⟶ J`. -/
public theorem homEquiv_monoidalIso_inv_uncurry_counit
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).homEquiv
        ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
          (CochainComplex.HomComplexR A
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J) ⊗ K) J
        ((extendScalarsMonoidalIso f
              ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
                (CochainComplex.HomComplexR A
                  ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)) K).inv ≫
          DerivedInternalHom.Model.uncurry
            (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).counit.app
              (CochainComplex.HomComplexR A
                ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J))) =
      (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
            (CochainComplex.HomComplexR A
              ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)) ⊗ₘ
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K) ≫
        CochainComplex.ExtendScalars.restrictScalarsLaxTensor f
            (CochainComplex.HomComplexR A
              ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
            (DerivedInternalHom.Model.evaluationMor
              ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J) := by
  set adj := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
    (ComplexShape.up ℤ)
  set Z := CochainComplex.HomComplexR A
    ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
  set P := (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z
  have h1 := CochainComplex.ExtendScalars.restrictScalarsLaxTensor_comp_map f Z
    ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K)
    (DerivedInternalHom.Model.evaluationMor
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)
  have h2 := Adjunction.homEquiv_tensorHom_unit adj (extendScalarsMonoidalIso f P K).inv
    (extendScalarsMonoidalIso f P
      ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
        ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K))).inv
    (CochainComplex.ExtendScalars.extendScalarsMonoidalIso_inv_naturality_right f P
      (adj.unit.app K))
    (adj.counit.app Z)
    (DerivedInternalHom.Model.evaluationMor
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)
  have h3 := congrArg (fun w => adj.homEquiv (P ⊗ K) J ((extendScalarsMonoidalIso f P K).inv ≫ w))
    (DerivedInternalHom.Model.uncurry_eq_tensorHom_evaluationMor (adj.counit.app Z))
  exact h3.trans (h2.symm.trans
    (congrArg (fun w => (𝟙 P ⊗ₘ adj.unit.app K) ≫ w) h1).symm)

/-- **The value of the transpose, followed by a morphism `q` out of the restriction of `J`.** -/
public theorem homEquiv_monoidalIso_inv_uncurry_counit_comp
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    {I : CochainComplex (ModuleCat.{u} R) ℤ}
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I) :
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).homEquiv
          ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
            (CochainComplex.HomComplexR A
              ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J) ⊗ K) J
          ((extendScalarsMonoidalIso f
                ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
                  (CochainComplex.HomComplexR A
                    ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)) K).inv ≫
            DerivedInternalHom.Model.uncurry
              (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).counit.app
                (CochainComplex.HomComplexR A
                  ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J))) ≫ q =
      (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} f).obj
            (CochainComplex.HomComplexR A
              ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)) ⊗ₘ
          ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K) ≫
        CochainComplex.ExtendScalars.restrictScalarsLaxTensor f
            (CochainComplex.HomComplexR A
              ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
            (DerivedInternalHom.Model.evaluationMor
              ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J) ≫ q :=
  (congrArg (· ≫ q) (homEquiv_monoidalIso_inv_uncurry_counit f K J)).trans
    (CategoryTheory.comp_four_assoc _ _ _ q)

/-- **The model comparison of [stacks 0E1W] with its transpose read as a restricted evaluation.**

`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso` with the
transpose `W` replaced by the restricted evaluation
`(𝟙 P ⊗ₘ η K) ≫ CochainComplex.ExtendScalars.restrictScalarsLaxTensor f Z (A ⊗_R K) ≫ (ev)|_R ≫ q`.
-/
public theorem derivedHomChangeOfRingsModelIso_inv_eq_restrictedEvaluation
    (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{u} R))
      (DerivedCategory (ModuleCat.{u} A)))
    (α : DerivedCategory.Q ⋙ F ⟶
      CochainComplex.extendScalarsLarge.{u, u, u} f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I) [QuasiIso q]
    (hK : CochainComplex.KFlat.{u, u} K) :
    letI : IsIso (α.app K) :=
      BaseChange.isIso_extendScalarsCounit_app_of_kFlat f F α K hK
    letI := BaseChange.quasiIso_homComplexChangeOfRingsMap_of_kFlat.{u, u, u} f K J I q F α hK
    let Z := CochainComplex.HomComplexR A
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
    let P := (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z
    let W := (𝟙 P ⊗ₘ
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K) ≫
      CochainComplex.ExtendScalars.restrictScalarsLaxTensor f Z
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
          (DerivedInternalHom.Model.evaluationMor
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J) ≫ q
    (BaseChange.derivedHomChangeOfRingsModelIso f F α K J I q hK).inv =
      (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.map
          (BaseChange.homModelIso ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
            (asIso (α.app K)) (Iso.refl _)).hom ≫
        ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app Z).hom ≫
          ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
              (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I)).symm
            (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
              DerivedCategory.Q.map W)) ≫
            ((DerivedInternalHom.Model.adjunction R).homIso K I).hom ≫
              (BaseChange.homModelIso K I (Iso.refl _)
                ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app J ≪≫
                  @asIso _ _ _ _ (DerivedCategory.Q.map q)
                    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance))).inv := by
  intro Z P W
  rw [derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso f F α K J I q hK,
    homEquiv_monoidalIso_inv_uncurry_counit_comp f K J q]

end Stacks.DerivedHom.BaseChangeIso

end
