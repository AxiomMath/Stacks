module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-!
# Extension of scalars is monoidal on cochain complexes

Let `f : R → S` be a homomorphism of commutative rings. Extension of scalars
`M ↦ S ⊗_R M` is a monoidal functor `ModuleCat R ⥤ ModuleCat S`: the comparison
`(S ⊗_R M) ⊗_S (S ⊗_R N) ≅ S ⊗_R (M ⊗_R N)` is `AlgebraTensorModule.distribBaseChange`.
This file propagates that comparison to the total tensor product of cochain complexes:
`(S ⊗_R K) ⊗_S (S ⊗_R L) ≅ S ⊗_R (K ⊗_R L)`.

In each cohomological degree both sides are a coproduct over an antidiagonal. Extension of
scalars is a left adjoint, so it preserves that coproduct, and the comparison is assembled
summand by summand from the module-level comparison. Compatibility with the two Koszul-signed
differentials, one in each variable, is naturality of the module-level comparison in each
variable, the signs being the ones read off the complex shapes on either side.

## Main definitions

* `CochainComplex.ExtendScalars.mapCochainComplex`: degreewise extension of scalars on cochain
  complexes.
* `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`: the monoidality isomorphism
  `(S ⊗_R K) ⊗_S (S ⊗_R L) ≅ S ⊗_R (K ⊗_R L)`.

## Main results

* `CochainComplex.ExtendScalars.ι_extendScalarsMonoidalIso_hom`: the comparison read on the
  antidiagonal summand of bidegree `(i, j)` is the module-level comparison followed by the
  inclusion of that summand.
* `CochainComplex.ExtendScalars.extendScalarsMonoidalIso_naturality`: the comparison is natural
  in both complexes.
* `CochainComplex.ExtendScalars.ιTensorObj_associator_hom`: the associator of total tensor
  products of cochain complexes, read on the summand of a tridegree.
* `CochainComplex.ExtendScalars.extendScalarsMonoidalIso_associativity`: the comparison satisfies
  the Eilenberg--Kelly associativity axiom -- the pentagon.
* `CochainComplex.ExtendScalars.extendScalarsMonoidalIso_associativity_inv`: the same pentagon
  read in the inverse direction, which is the direction in which the comparison occurs in the
  values of the change-of-rings isomorphism of [stacks 0E1W].

## Implementation notes

The ring universe and the module universe agree here: the monoidal structure of
`ModuleCat.{u} R` names `R` itself as its tensor unit, and it is Mathlib's monoidal structure
on `ModuleCat.{u} R` that carries the monoidal functor instance for extension of scalars.

Extension of scalars is additive because it is a left adjoint; the instance is not global in
Mathlib, so it is introduced here as a local instance.

## References

* [The Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

universe u

namespace CochainComplex.ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Degreewise extension of scalars along `f : R → S` on cochain complexes. -/
noncomputable abbrev mapCochainComplex (f : R →+* S) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ :=
  (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Extension of scalars is additive, being a left adjoint. -/
private lemma extendScalars_isAdditive (f : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive

attribute [local instance] extendScalars_isAdditive

private lemma curriedTensor_map_app' {C : Type*} [Category* C] [MonoidalCategory C]
    {X Y : C} (g : X ⟶ Y) (Z : C) : ((curriedTensor C).map g).app Z = g ▷ Z := rfl

private lemma curriedTensor_obj_map' {C : Type*} [Category* C] [MonoidalCategory C]
    (X : C) {Y Z : C} (g : Y ⟶ Z) : ((curriedTensor C).obj X).map g = X ◁ g := rfl

/-- The associator of the total tensor product of cochain complexes, read on the summand of
tridegree `(i, j, k)`: it is the associator of the three components, conjugated by the inclusions
of that summand on either side.  No Koszul sign appears -- the signs of the total complex live in
its differentials, and the associator is assembled degreewise from the pointwise associator. -/
lemma ιTensorObj_associator_hom {T : Type u} [CommRing T]
    (K₁ K₂ K₃ : CochainComplex (ModuleCat.{u} T) ℤ) (i j k n : ℤ) (h : i + j + k = n) :
    (HomologicalComplex.ιTensorObj K₁ K₂ i j (i + j) rfl ▷ K₃.X k) ≫
        HomologicalComplex.ιTensorObj (K₁ ⊗ K₂) K₃ (i + j) k n h ≫ (α_ K₁ K₂ K₃).hom.f n =
      (α_ (K₁.X i) (K₂.X j) (K₃.X k)).hom ≫
        (K₁.X i ◁ HomologicalComplex.ιTensorObj K₂ K₃ j k (j + k) rfl) ≫
          HomologicalComplex.ιTensorObj K₁ (K₂ ⊗ K₃) i (j + k) n (by omega) := by
  have he := HomologicalComplex.ι_mapBifunctorAssociatorX_hom
    (curriedAssociatorNatIso (ModuleCat.{u} T)) K₁ K₂ K₃
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) i j k n h
  rwa [HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ K₁ K₂ K₃ _ _ i j k (i + j) n rfl h,
    HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ K₁ K₂ K₃ _ _ _ i j k (j + k) n rfl
      (by change i + (j + k) = n; omega)] at he

variable (f : R →+* S) (K L : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The degree-`n` component of the monoidality comparison: on the antidiagonal summand of
bidegree `(i, j)` it is the module-level comparison, followed by the inclusion of the
corresponding summand of the base-changed total complex. -/
private noncomputable def monoidalCompX (n : ℤ) :
    ((mapCochainComplex f).obj K ⊗ (mapCochainComplex f).obj L).X n ⟶
      ((mapCochainComplex f).obj (K ⊗ L)).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := (mapCochainComplex f).obj K) (K₂ := (mapCochainComplex f).obj L)
    (F := curriedTensor (ModuleCat.{u} S)) (c := ComplexShape.up ℤ) (j := n)
    (fun i j h => μ (ModuleCat.extendScalars.{u, u, u} f) (K.X i) (L.X j) ≫
      (ModuleCat.extendScalars.{u, u, u} f).map (HomologicalComplex.ιTensorObj K L i j n h))

private lemma ι_monoidalCompX (n i j : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj ((mapCochainComplex f).obj K) ((mapCochainComplex f).obj L)
        i j n h ≫ monoidalCompX f K L n =
      μ (ModuleCat.extendScalars.{u, u, u} f) (K.X i) (L.X j) ≫
        (ModuleCat.extendScalars.{u, u, u} f).map (HomologicalComplex.ιTensorObj K L i j n h) :=
  HomologicalComplex.ι_mapBifunctorDesc _ _ _ _

private lemma ιOrZero_monoidalCompX (n i j : ℤ) :
    HomologicalComplex.ιMapBifunctorOrZero ((mapCochainComplex f).obj K)
        ((mapCochainComplex f).obj L) (curriedTensor (ModuleCat.{u} S)) (ComplexShape.up ℤ)
        i j n ≫ monoidalCompX f K L n =
      μ (ModuleCat.extendScalars.{u, u, u} f) (K.X i) (L.X j) ≫
        (ModuleCat.extendScalars.{u, u, u} f).map
          (HomologicalComplex.ιMapBifunctorOrZero K L (curriedTensor (ModuleCat.{u} R))
            (ComplexShape.up ℤ) i j n) := by
  by_cases h : i + j = n
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h,
      HomologicalComplex.ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h]
    exact ι_monoidalCompX f K L n i j h
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ h,
      HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ h,
      Functor.map_zero, Limits.comp_zero, Limits.zero_comp]

/-- The differential of a total tensor product of cochain complexes, read on the summand of
bidegree `(i, j)`: the two Koszul-signed differentials, one in each variable. -/
private lemma ιTensorObj_d {T : Type u} [CommRing T] (K₁ K₂ : CochainComplex (ModuleCat.{u} T) ℤ)
    (i j n m : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ i j n h ≫ (K₁ ⊗ K₂).d n m =
      (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, j) •
        (((curriedTensor (ModuleCat.{u} T)).map (K₁.d i (i + 1))).app (K₂.X j) ≫
          HomologicalComplex.ιMapBifunctorOrZero K₁ K₂ (curriedTensor (ModuleCat.{u} T))
            (ComplexShape.up ℤ) (i + 1) j m) +
      (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, j) •
        (((curriedTensor (ModuleCat.{u} T)).obj (K₁.X i)).map (K₂.d j (j + 1)) ≫
          HomologicalComplex.ιMapBifunctorOrZero K₁ K₂ (curriedTensor (ModuleCat.{u} T))
            (ComplexShape.up ℤ) i (j + 1) m) := by
  change HomologicalComplex.ιMapBifunctor K₁ K₂ _ _ i j n h ≫
    (HomologicalComplex.mapBifunctor K₁ K₂ (curriedTensor (ModuleCat.{u} T))
      (ComplexShape.up ℤ)).d n m = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _
      (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
    HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _
      (show (ComplexShape.up ℤ).Rel j (j + 1) from rfl)]

-- The two Koszul-signed differentials, one in each variable, are compared summand by summand;
-- the signs are determined by the complex shapes, which are the same on both sides.
private lemma monoidalCompX_comm (n m : ℤ) :
    monoidalCompX f K L n ≫ ((mapCochainComplex f).obj (K ⊗ L)).d n m =
      ((mapCochainComplex f).obj K ⊗ (mapCochainComplex f).obj L).d n m ≫
        monoidalCompX f K L m := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [← Category.assoc, ι_monoidalCompX f K L n i j h, Category.assoc,
    ← Category.assoc _ _ (monoidalCompX f K L m),
    ιTensorObj_d ((mapCochainComplex f).obj K) ((mapCochainComplex f).obj L) i j n m h]
  have hd : ((mapCochainComplex f).obj (K ⊗ L)).d n m =
      (ModuleCat.extendScalars.{u, u, u} f).map ((K ⊗ L).d n m) := rfl
  rw [hd, ← Functor.map_comp, ιTensorObj_d, Functor.map_add,
    Functor.map_units_smul, Functor.map_units_smul, Functor.map_comp, Functor.map_comp,
    Preadditive.comp_add, Preadditive.add_comp,
    Linear.units_smul_comp, Linear.units_smul_comp,
    Linear.comp_units_smul, Linear.comp_units_smul,
    Category.assoc, Category.assoc,
    ιOrZero_monoidalCompX f K L m (i + 1) j, ιOrZero_monoidalCompX f K L m i (j + 1)]
  congr 1
  · congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (Functor.LaxMonoidal.μ_natural_left (ModuleCat.extendScalars.{u, u, u} f)
      (K.d i (i + 1)) (L.X j)).symm
  · congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (Functor.LaxMonoidal.μ_natural_right (ModuleCat.extendScalars.{u, u, u} f)
      (K.X i) (L.d j (j + 1))).symm

/-- The monoidality comparison of degreewise extension of scalars, as a morphism of cochain
complexes. -/
private noncomputable def monoidalCompHom :
    (mapCochainComplex f).obj K ⊗ (mapCochainComplex f).obj L ⟶
      (mapCochainComplex f).obj (K ⊗ L) where
  f n := monoidalCompX f K L n
  comm' n m _ := monoidalCompX_comm f K L n m

-- Extension of scalars preserves the coproduct of antidiagonal summands, being a left adjoint,
-- so the comparison is invertible in each degree.
private instance monoidalCompX_isIso (n : ℤ) : IsIso (monoidalCompX f K L n) := by
  let F := ModuleCat.extendScalars.{u, u, u} f
  let Z := ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} R)) ℤ ℤ).obj K.X).obj L.X
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  have : PreservesColimitsOfShape (Discrete (p ⁻¹' {n})) F :=
    ((ModuleCat.extendRestrictScalarsAdj.{u} f).leftAdjoint_preservesColimits
      ).preservesColimitsOfShape
  have hcolim := isColimitOfPreserves F (Z.isColimitCofanMapObj p n)
  let tgt : Cocone (Discrete.functor (Z.mapObjFun p n) ⋙ F) :=
    { pt := ((mapCochainComplex f).obj K ⊗ (mapCochainComplex f).obj L).X n
      ι := Discrete.natTrans (fun i =>
        δ F (K.X i.as.1.1) (L.X i.as.1.2) ≫
          HomologicalComplex.ιTensorObj ((mapCochainComplex f).obj K)
            ((mapCochainComplex f).obj L) i.as.1.1 i.as.1.2 n i.as.2) }
  let hm : ((mapCochainComplex f).obj (K ⊗ L)).X n ⟶
      ((mapCochainComplex f).obj K ⊗ (mapCochainComplex f).obj L).X n := hcolim.desc tgt
  have fac : ∀ (i j : ℤ) (h : i + j = n),
      F.map (HomologicalComplex.ιTensorObj K L i j n h) ≫ hm =
        δ F (K.X i) (L.X j) ≫
          HomologicalComplex.ιTensorObj ((mapCochainComplex f).obj K)
            ((mapCochainComplex f).obj L) i j n h :=
    fun i j h => hcolim.fac tgt ⟨⟨(i, j), h⟩⟩
  refine ⟨hm, ?_, ?_⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    rw [← Category.assoc, ι_monoidalCompX f K L n i j h, Category.assoc, fac i j h,
      ← Category.assoc, μ_δ]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · apply hcolim.hom_ext
    rintro ⟨⟨⟨i, j⟩, (h : i + j = n)⟩⟩
    change F.map (HomologicalComplex.ιTensorObj K L i j n h) ≫ hm ≫ monoidalCompX f K L n =
      F.map (HomologicalComplex.ιTensorObj K L i j n h) ≫
        𝟙 (((mapCochainComplex f).obj (K ⊗ L)).X n)
    rw [reassoc_of% (fac i j h), ι_monoidalCompX f K L n i j h, δ_μ_assoc]
    exact (Category.comp_id _).symm

private instance monoidalCompHom_isIso : IsIso (monoidalCompHom f K L) := by
  have : ∀ n, IsIso ((monoidalCompHom f K L).f n) := monoidalCompX_isIso f K L
  exact HomologicalComplex.Hom.isIso_of_components _

-- The body names `private` helpers, so it must not be exposed to importers.
/-- **Monoidality of base change.** Degreewise extension of scalars along `f : R → S` carries
the total tensor product of cochain complexes of `R`-modules to the total tensor product over
`S` of the base changes: `(S ⊗_R K) ⊗_S (S ⊗_R L) ≅ S ⊗_R (K ⊗_R L)`. -/
@[no_expose]
noncomputable def extendScalarsMonoidalIso :
    (mapCochainComplex f).obj K ⊗ (mapCochainComplex f).obj L ≅
      (mapCochainComplex f).obj (K ⊗ L) where
  hom := monoidalCompHom f K L
  inv := CategoryTheory.inv (monoidalCompHom f K L)
  hom_inv_id := IsIso.hom_inv_id _
  inv_hom_id := IsIso.inv_hom_id _

/-- The monoidality comparison read on the antidiagonal summand of bidegree `(i, j)`: it is the
module-level comparison `(S ⊗_R K^i) ⊗_S (S ⊗_R L^j) ≅ S ⊗_R (K^i ⊗_R L^j)` followed by the
base change of the inclusion of that summand. -/
lemma ι_extendScalarsMonoidalIso_hom (n i j : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj ((mapCochainComplex f).obj K) ((mapCochainComplex f).obj L)
        i j n h ≫ (extendScalarsMonoidalIso f K L).hom.f n =
      μ (ModuleCat.extendScalars.{u, u, u} f) (K.X i) (L.X j) ≫
        (ModuleCat.extendScalars.{u, u, u} f).map (HomologicalComplex.ιTensorObj K L i j n h) :=
  ι_monoidalCompX f K L n i j h

/-- The monoidality comparison is natural in both complexes. -/
lemma extendScalarsMonoidalIso_naturality {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    ((mapCochainComplex f).map a ⊗ₘ (mapCochainComplex f).map b) ≫
        (extendScalarsMonoidalIso f K' L').hom =
      (extendScalarsMonoidalIso f K L).hom ≫ (mapCochainComplex f).map (a ⊗ₘ b) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  have hab : ((mapCochainComplex f).map a ⊗ₘ (mapCochainComplex f).map b) =
      HomologicalComplex.mapBifunctorMap ((mapCochainComplex f).map a)
        ((mapCochainComplex f).map b) (curriedTensor (ModuleCat.{u} S))
        (ComplexShape.up ℤ) := rfl
  have hab' : (a ⊗ₘ b) = HomologicalComplex.mapBifunctorMap a b
      (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) := rfl
  have hmap : ((mapCochainComplex f).map (a ⊗ₘ b)).f n =
      (ModuleCat.extendScalars.{u, u, u} f).map ((a ⊗ₘ b).f n) := rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc, hab,
    HomologicalComplex.ι_mapBifunctorMap _ _ _ _ i j n h, Category.assoc, Category.assoc,
    ι_extendScalarsMonoidalIso_hom f K' L' n i j h,
    reassoc_of% (ι_extendScalarsMonoidalIso_hom f K L n i j h), hmap, ← Functor.map_comp,
    hab', HomologicalComplex.ι_mapBifunctorMap _ _ _ _ i j n h]
  have key := Functor.LaxMonoidal.μ_natural (ModuleCat.extendScalars.{u, u, u} f) (a.f i) (b.f j)
  simp only [tensorHom_def, Category.assoc] at key
  simp only [Functor.map_comp, curriedTensor_map_app', curriedTensor_obj_map',
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X]
  rw [reassoc_of% key]
  simp only [Functor.map_comp, Category.assoc]

/-! ### The pentagon

The monoidality comparison satisfies the Eilenberg--Kelly associativity axiom.  Both sides are
computed on the summand of tridegree `(i, j, k)`, where each lands on the module-level comparison
of the three components; there the identity is the associativity axiom of the module-level
comparison.  No sign intervenes: by `CochainComplex.ExtendScalars.ιTensorObj_associator_hom` the
associator of total complexes carries a triple summand to the pointwise associator with no Koszul
factor.
-/

variable (M : CochainComplex (ModuleCat.{u} R) ℤ)

-- The comparison whiskered by `M` and then composed with the comparison at `(K ⊗ L, M)`, read on
-- the summand of tridegree `(i, j, k)`.
private lemma ι₁₂_monoidalIso_whiskerRight (i j k n : ℤ) (h : i + j + k = n) :
    (HomologicalComplex.ιTensorObj ((mapCochainComplex f).obj K)
          ((mapCochainComplex f).obj L) i j (i + j) rfl ▷
        ((mapCochainComplex f).obj M).X k) ≫
      HomologicalComplex.ιTensorObj
          ((mapCochainComplex f).obj K ⊗ (mapCochainComplex f).obj L)
          ((mapCochainComplex f).obj M) (i + j) k n h ≫
        ((extendScalarsMonoidalIso f K L).hom ▷ (mapCochainComplex f).obj M).f n ≫
        (extendScalarsMonoidalIso f (K ⊗ L) M).hom.f n =
      (μ (ModuleCat.extendScalars.{u, u, u} f) (K.X i) (L.X j) ▷
          (ModuleCat.extendScalars.{u, u, u} f).obj (M.X k)) ≫
        μ (ModuleCat.extendScalars.{u, u, u} f) (K.X i ⊗ L.X j) (M.X k) ≫
        (ModuleCat.extendScalars.{u, u, u} f).map
          ((HomologicalComplex.ιTensorObj K L i j (i + j) rfl ▷ M.X k) ≫
            HomologicalComplex.ιTensorObj (K ⊗ L) M (i + j) k n h) := by
  have hw : (extendScalarsMonoidalIso f K L).hom ▷ (mapCochainComplex f).obj M =
      HomologicalComplex.mapBifunctorMap (extendScalarsMonoidalIso f K L).hom
        (𝟙 ((mapCochainComplex f).obj M)) (curriedTensor (ModuleCat.{u} S))
        (ComplexShape.up ℤ) := rfl
  have key := Functor.LaxMonoidal.μ_natural_left (ModuleCat.extendScalars.{u, u, u} f)
    (HomologicalComplex.ιTensorObj K L i j (i + j) rfl) (M.X k)
  rw [hw, HomologicalComplex.ι_mapBifunctorMap_assoc _ _ _ _ (i + j) k n h,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp,
    ι_extendScalarsMonoidalIso_hom f (K ⊗ L) M n (i + j) k h,
    curriedTensor_map_app', ← Category.assoc, ← comp_whiskerRight,
    ι_extendScalarsMonoidalIso_hom f K L (i + j) i j rfl,
    comp_whiskerRight, Category.assoc, Functor.map_comp, ← reassoc_of% key]
  rfl

-- The left-hand side of the pentagon on the summand of tridegree `(i, j, k)`.
private lemma ι₁₂_pentagon_left (i j k n : ℤ) (h : i + j + k = n) :
    (HomologicalComplex.ιTensorObj ((mapCochainComplex f).obj K)
          ((mapCochainComplex f).obj L) i j (i + j) rfl ▷
        ((mapCochainComplex f).obj M).X k) ≫
      HomologicalComplex.ιTensorObj
          ((mapCochainComplex f).obj K ⊗ (mapCochainComplex f).obj L)
          ((mapCochainComplex f).obj M) (i + j) k n h ≫
        ((extendScalarsMonoidalIso f K L).hom ▷ (mapCochainComplex f).obj M).f n ≫
        (extendScalarsMonoidalIso f (K ⊗ L) M).hom.f n ≫
        ((mapCochainComplex f).map (α_ K L M).hom).f n =
      (μ (ModuleCat.extendScalars.{u, u, u} f) (K.X i) (L.X j) ▷
          (ModuleCat.extendScalars.{u, u, u} f).obj (M.X k)) ≫
        μ (ModuleCat.extendScalars.{u, u, u} f) (K.X i ⊗ L.X j) (M.X k) ≫
        (ModuleCat.extendScalars.{u, u, u} f).map
          ((α_ (K.X i) (L.X j) (M.X k)).hom ≫
            (K.X i ◁ HomologicalComplex.ιTensorObj L M j k (j + k) rfl) ≫
            HomologicalComplex.ιTensorObj K (L ⊗ M) i (j + k) n (by omega)) := by
  have hα : ((mapCochainComplex f).map (α_ K L M).hom).f n =
      (ModuleCat.extendScalars.{u, u, u} f).map ((α_ K L M).hom.f n) := rfl
  rw [reassoc_of% (ι₁₂_monoidalIso_whiskerRight f K L M i j k n h), hα, ← Functor.map_comp,
    Category.assoc, ιTensorObj_associator_hom K L M i j k n h]

-- The right-hand side of the pentagon on the summand of tridegree `(i, j, k)`.
private lemma ι₁₂_pentagon_right (i j k n : ℤ) (h : i + j + k = n) :
    (HomologicalComplex.ιTensorObj ((mapCochainComplex f).obj K)
          ((mapCochainComplex f).obj L) i j (i + j) rfl ▷
        ((mapCochainComplex f).obj M).X k) ≫
      HomologicalComplex.ιTensorObj
          ((mapCochainComplex f).obj K ⊗ (mapCochainComplex f).obj L)
          ((mapCochainComplex f).obj M) (i + j) k n h ≫
        (α_ ((mapCochainComplex f).obj K) ((mapCochainComplex f).obj L)
            ((mapCochainComplex f).obj M)).hom.f n ≫
        ((mapCochainComplex f).obj K ◁ (extendScalarsMonoidalIso f L M).hom).f n ≫
        (extendScalarsMonoidalIso f K (L ⊗ M)).hom.f n =
      (α_ ((ModuleCat.extendScalars.{u, u, u} f).obj (K.X i))
          ((ModuleCat.extendScalars.{u, u, u} f).obj (L.X j))
          ((ModuleCat.extendScalars.{u, u, u} f).obj (M.X k))).hom ≫
        ((ModuleCat.extendScalars.{u, u, u} f).obj (K.X i) ◁
          μ (ModuleCat.extendScalars.{u, u, u} f) (L.X j) (M.X k)) ≫
        μ (ModuleCat.extendScalars.{u, u, u} f) (K.X i) (L.X j ⊗ M.X k) ≫
        (ModuleCat.extendScalars.{u, u, u} f).map
          ((K.X i ◁ HomologicalComplex.ιTensorObj L M j k (j + k) rfl) ≫
            HomologicalComplex.ιTensorObj K (L ⊗ M) i (j + k) n (by omega)) := by
  have hjk : i + (j + k) = n := by omega
  have hw : (mapCochainComplex f).obj K ◁ (extendScalarsMonoidalIso f L M).hom =
      HomologicalComplex.mapBifunctorMap (𝟙 ((mapCochainComplex f).obj K))
        (extendScalarsMonoidalIso f L M).hom (curriedTensor (ModuleCat.{u} S))
        (ComplexShape.up ℤ) := rfl
  have hw2 : ((mapCochainComplex f).obj K).X i ◁
        HomologicalComplex.ιTensorObj ((mapCochainComplex f).obj L)
          ((mapCochainComplex f).obj M) j k (j + k) rfl ≫
      ((mapCochainComplex f).obj K).X i ◁ (extendScalarsMonoidalIso f L M).hom.f (j + k) =
    ((mapCochainComplex f).obj K).X i ◁
      (μ (ModuleCat.extendScalars.{u, u, u} f) (L.X j) (M.X k) ≫
        (ModuleCat.extendScalars.{u, u, u} f).map
          (HomologicalComplex.ιTensorObj L M j k (j + k) rfl)) := by
    rw [← whiskerLeft_comp, ι_extendScalarsMonoidalIso_hom f L M (j + k) j k rfl]
  have key : ((mapCochainComplex f).obj K).X i ◁
        (ModuleCat.extendScalars.{u, u, u} f).map
          (HomologicalComplex.ιTensorObj L M j k (j + k) rfl) ≫
      μ (ModuleCat.extendScalars.{u, u, u} f) (K.X i) ((L ⊗ M).X (j + k)) =
    μ (ModuleCat.extendScalars.{u, u, u} f) (K.X i) (L.X j ⊗ M.X k) ≫
      (ModuleCat.extendScalars.{u, u, u} f).map
        (K.X i ◁ HomologicalComplex.ιTensorObj L M j k (j + k) rfl) :=
    Functor.LaxMonoidal.μ_natural_right _ _ _
  rw [reassoc_of% (ιTensorObj_associator_hom ((mapCochainComplex f).obj K)
      ((mapCochainComplex f).obj L) ((mapCochainComplex f).obj M) i j k n h),
    hw, HomologicalComplex.ι_mapBifunctorMap_assoc _ _ _ _ i (j + k) n hjk,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    curriedTensor_obj_map', ι_extendScalarsMonoidalIso_hom f K (L ⊗ M) n i (j + k) hjk,
    reassoc_of% hw2, whiskerLeft_comp, Category.assoc, reassoc_of% key, ← Functor.map_comp]
  rfl

/-- **The pentagon of the monoidality comparison, at chain level.**  The comparison
`(S ⊗_R K) ⊗_S (S ⊗_R L) ≅ S ⊗_R (K ⊗_R L)` of degreewise extension of scalars satisfies the
Eilenberg--Kelly associativity axiom of a lax monoidal comparison: whiskering it by `S ⊗_R M` and
then comparing at `(K ⊗_R L, M)` agrees, across the two associators, with whiskering by `S ⊗_R K`
and comparing at `(K, L ⊗_R M)`.

Both sides are read on the summand of tridegree `(i, j, k)`, where each becomes the module-level
comparison of `K^i`, `L^j` and `M^k`; there the identity is the associativity axiom of the
module-level comparison `AlgebraTensorModule.distribBaseChange`.  No Koszul sign appears, the
associator of total complexes being summandwise the pointwise associator. -/
theorem extendScalarsMonoidalIso_associativity :
    (extendScalarsMonoidalIso f K L).hom ▷ (mapCochainComplex f).obj M ≫
        (extendScalarsMonoidalIso f (K ⊗ L) M).hom ≫
        (mapCochainComplex f).map (α_ K L M).hom =
      (α_ ((mapCochainComplex f).obj K) ((mapCochainComplex f).obj L)
            ((mapCochainComplex f).obj M)).hom ≫
        (mapCochainComplex f).obj K ◁ (extendScalarsMonoidalIso f L M).hom ≫
        (extendScalarsMonoidalIso f K (L ⊗ M)).hom := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext (c₁₂ := ComplexShape.up ℤ)
  intro i j k h
  have h' : i + j + k = n := h
  simp only [HomologicalComplex.comp_f]
  -- The inclusion of the summand of `(S ⊗ K) ⊗ (S ⊗ L)`, spelled through the monoidal structure.
  have hι : HomologicalComplex.ιMapBifunctor
        (HomologicalComplex.mapBifunctor ((mapCochainComplex f).obj K)
          ((mapCochainComplex f).obj L) (curriedTensor (ModuleCat.{u} S)) (ComplexShape.up ℤ))
        ((mapCochainComplex f).obj M) (curriedTensor (ModuleCat.{u} S)) (ComplexShape.up ℤ)
        (i + j) k n h' =
      HomologicalComplex.ιTensorObj
        ((mapCochainComplex f).obj K ⊗ (mapCochainComplex f).obj L)
        ((mapCochainComplex f).obj M) (i + j) k n h' := rfl
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{u} S))
      (curriedTensor (ModuleCat.{u} S)) _ _ _ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      i j k (i + j) n rfl h',
    curriedTensor_map_app', Category.assoc, Category.assoc, hι,
    ι₁₂_pentagon_left f K L M i j k n h', ι₁₂_pentagon_right f K L M i j k n h',
    Functor.map_comp, reassoc_of% (Functor.LaxMonoidal.associativity
      (ModuleCat.extendScalars.{u, u, u} f) (K.X i) (L.X j) (M.X k))]

/-- **The pentagon of the monoidality comparison, read in the inverse direction.**

`CochainComplex.ExtendScalars.extendScalarsMonoidalIso_associativity` is the Eilenberg--Kelly
associativity axiom for the `hom` direction of the comparison.  Every factor of it is an
isomorphism, so the whole equation inverts, and what comes out is the same axiom for the `inv`
direction, the three factors of each side in the opposite order.

This is the direction in which the comparison occurs wherever the change-of-rings isomorphism of
[stacks 0E1W] is read with nothing inverted: the chain map
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso` values the
representative model comparison with is the [stacks 0A63] transpose of
`(extendScalarsMonoidalIso f P K).inv`, and
`Stacks.DerivedHom.BaseChangeIso.eq_extendScalarsMonoidalIso_inv` characterizes that inverse on
summands.  A coherence between two such readings — at `(P, K)` and at `(K, L)`, say — therefore
needs the pentagon in this direction and not the other. -/
theorem extendScalarsMonoidalIso_associativity_inv :
    (extendScalarsMonoidalIso f K (L ⊗ M)).inv ≫
        (mapCochainComplex f).obj K ◁ (extendScalarsMonoidalIso f L M).inv ≫
        (α_ ((mapCochainComplex f).obj K) ((mapCochainComplex f).obj L)
          ((mapCochainComplex f).obj M)).inv =
      (mapCochainComplex f).map (α_ K L M).inv ≫
        (extendScalarsMonoidalIso f (K ⊗ L) M).inv ≫
        (extendScalarsMonoidalIso f K L).inv ▷ (mapCochainComplex f).obj M := by
  have key :
      whiskerRightIso (extendScalarsMonoidalIso f K L) ((mapCochainComplex f).obj M) ≪≫
          extendScalarsMonoidalIso f (K ⊗ L) M ≪≫ (mapCochainComplex f).mapIso (α_ K L M) =
        α_ ((mapCochainComplex f).obj K) ((mapCochainComplex f).obj L)
              ((mapCochainComplex f).obj M) ≪≫
          whiskerLeftIso ((mapCochainComplex f).obj K) (extendScalarsMonoidalIso f L M) ≪≫
            extendScalarsMonoidalIso f K (L ⊗ M) :=
    Iso.ext (extendScalarsMonoidalIso_associativity f K L M)
  simpa only [Iso.trans_inv, Functor.mapIso_inv, whiskerRightIso_inv, whiskerLeftIso_inv,
    Category.assoc] using (congrArg Iso.inv key).symm

end CochainComplex.ExtendScalars

end
