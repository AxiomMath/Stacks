module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Coproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ShiftedDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise

/-!
# Derived tensor product with an object whose cohomology sheaves are flat

Let `(C, O)` be a ringed site, `M` a sheaf of `O`-modules and `K` an object of `D(O)` all of whose
cohomology sheaves `H^i(K)` are flat. Then the derived tensor product with `M` may be computed on
cohomology:

`H^t(M ⊗^𝐋_O K) ≅ M ⊗_O H^t(K)` for every `t`.

This is the "tiny argument" that [Stacks, Tag 0FMN] omits when it writes the first page of the
spectral sequence of [Stacks, Tag 0FMM] as `Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`.

## Main definitions

* `CochainComplex.truncLETower`: the tower `n ↦ τ^{≤ n}L` of canonical truncations of a cochain
  complex, with the inclusions as transition maps.
* `CochainComplex.isColimitTruncLETowerCocone`: `L` is the colimit of its canonical truncations.
* `Stacks.DerivedTensor.RingedSite.tensorHomologyIsoOfHasFlatHomology`: the isomorphism
  `H^t(M[0] ⊗^𝐋_O K) ≅ M ⊗_O H^t(K)` when every `H^i(K)` is flat.

## Main results

* `Stacks.DerivedTensor.RingedSite.isGE_tensor_of_hasFlatHomology`: if `K` lies in `D^{≥ a}(O)`
  and has flat cohomology sheaves, then `A ⊗^𝐋_O K` lies in `D^{≥ a}(O)` for every `A` in
  `D^{≥ 0}(O)`. No boundedness from above is assumed.

## Implementation notes

Write `τ^{≤ t}K ⟶ K ⟶ τ^{> t}K` for the truncation
triangle.

* *Right-hand comparison.* In the triangle `τ^{< t}K ⟶ τ^{≤ t}K ⟶ H^t(K)[-t]` the first vertex
  stays in `D^{≤ t - 1}` after tensoring with `M[0]`, by right t-exactness of the derived tensor
  product, so `H^t(M ⊗^𝐋 τ^{≤ t}K) ≅ H^t(M ⊗^𝐋 H^t(K)[-t]) ≅ M ⊗ H^t(K)`. No flatness is used.
* *Left-hand comparison.* `H^t(M ⊗^𝐋 τ^{≤ t}K) ⟶ H^t(M ⊗^𝐋 K)` is an isomorphism as soon as
  `M ⊗^𝐋 τ^{> t}K` lies in `D^{≥ t + 1}`. This is where flatness enters, and it is the content of
  `isGE_tensor_of_hasFlatHomology`. For a *bounded* object it follows by induction on the length
  from the case of a single flat module, where the derived tensor product is computed by the
  K-flat complex `H[n]`. A general object of `D^{≥ a}` is not bounded above, and no induction on
  truncations reaches it. Instead it is represented by a complex `L` vanishing below `a`, which is
  the colimit of its canonical truncations `τ^{≤ n}L`; for a K-flat model `P` of the left factor
  the total tensor complex `Tot(P ⊗ -)` and cohomology both commute with this colimit (tensoring
  is a left adjoint, and filtered colimits of sheaves of modules are exact), so the cohomology of
  `Tot(P ⊗ L)` below `a` is a colimit of zero objects.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe d u

/-! ### The tower of canonical truncations -/

namespace CochainComplex

variable {A : Type*} [Category A] [Abelian A] (L : CochainComplex A ℤ)

/-- The inclusion `τ^{≤ n}L ⟶ τ^{≤ m}L` of canonical truncations, for `n ≤ m`. -/
def truncLEMapOfLE {n m : ℤ} (h : n ≤ m) : L.truncLE n ⟶ L.truncLE m :=
  haveI := (L.truncLE n).isStrictlyLE_of_le n m h
  inv ((L.truncLE n).ιTruncLE m) ≫ truncLEMap (L.ιTruncLE n) m

/-- The inclusion `τ^{≤ n}L ⟶ τ^{≤ m}L` composed with `τ^{≤ m}L ⟶ L` is the inclusion
`τ^{≤ n}L ⟶ L`. -/
@[reassoc (attr := simp)]
lemma truncLEMapOfLE_ι {n m : ℤ} (h : n ≤ m) :
    L.truncLEMapOfLE h ≫ L.ιTruncLE m = L.ιTruncLE n := by
  have := (L.truncLE n).isStrictlyLE_of_le n m h
  simp only [truncLEMapOfLE, Category.assoc, ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

/-- The tower `n ↦ τ^{≤ n}L` of canonical truncations of `L`, indexed by `n : ℕ`, with the
inclusions as transition maps. -/
def truncLETower : ℕ ⥤ CochainComplex A ℤ where
  obj n := L.truncLE (n : ℤ)
  map {m n} f := L.truncLEMapOfLE (Int.ofNat_le.2 (leOfHom f))
  map_id n := by
    rw [← cancel_mono (L.ιTruncLE (n : ℤ)), truncLEMapOfLE_ι, Category.id_comp]
  map_comp {_ _ k} f g := by
    rw [← cancel_mono (L.ιTruncLE (k : ℤ)), Category.assoc, truncLEMapOfLE_ι,
      truncLEMapOfLE_ι, truncLEMapOfLE_ι]

/-- The cocone on the tower of canonical truncations with vertex `L`. -/
def truncLETowerCocone : Cocone L.truncLETower where
  pt := L
  ι :=
    { app := fun n => L.ιTruncLE (n : ℤ)
      naturality := fun _ _ f => by
        dsimp only [truncLETower, Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, truncLEMapOfLE_ι] }

/-- A complex is the colimit of its canonical truncations. -/
def isColimitTruncLETowerCocone : IsColimit L.truncLETowerCocone := by
  refine HomologicalComplex.isColimitOfEval _ _ fun i => ?_
  have hleg (n : ℕ) (hn : i < n) : IsIso ((L.ιTruncLE (n : ℤ)).f i) :=
    L.isIso_ιTruncLE_f_of_lt n i hn
  have hc : Functor.IsEventuallyConstantFrom
      (L.truncLETower ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i) (i + 1).toNat := by
    intro j f
    have hj : ((i + 1).toNat : ℤ) ≤ (j : ℤ) := Int.ofNat_le.2 (leOfHom f)
    have h₁ := hleg ((i + 1).toNat) (by omega)
    have h₂ := hleg j (by omega)
    have hcomp : (L.truncLEMapOfLE (Int.ofNat_le.2 (leOfHom f))).f i ≫
        (L.ιTruncLE (j : ℤ)).f i = (L.ιTruncLE ((i + 1).toNat : ℤ)).f i := by
      rw [← HomologicalComplex.comp_f, truncLEMapOfLE_ι]
    change IsIso ((L.truncLEMapOfLE (Int.ofNat_le.2 (leOfHom f))).f i)
    have : IsIso ((L.truncLEMapOfLE (Int.ofNat_le.2 (leOfHom f))).f i ≫
        (L.ιTruncLE (j : ℤ)).f i) := by rw [hcomp]; exact h₁
    exact IsIso.of_isIso_comp_right _ ((L.ιTruncLE (j : ℤ)).f i)
  haveI : IsIso (((HomologicalComplex.eval A (ComplexShape.up ℤ) i).mapCocone
      L.truncLETowerCocone).ι.app (i + 1).toNat) :=
    hleg ((i + 1).toNat) (by omega)
  exact hc.isColimitOfIsIso _

end CochainComplex

/-! ### Derived tensor products with flat cohomology -/

namespace Stacks.DerivedTensor.RingedSite

attribute [local instance 100000] HasDerivedCategory.standard

open DerivedCategory

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- Flatness of the cohomology sheaves of an object of `D(O)`, in every degree. -/
abbrev HasFlatHomology (E : DerivedModules R) : Prop :=
  ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R)
    ((homologyFunctor (Modules R) i).obj E)

variable {R}

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M : Modules R, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)] in
/-- Having flat cohomology sheaves is invariant under isomorphism in `D(O)`. -/
lemma HasFlatHomology.of_iso {E E' : DerivedModules R} (e : E ≅ E') (h : HasFlatHomology R E) :
    HasFlatHomology R E' := fun i =>
  AlgebraicGeometry.SheafOfModules.IsFlat.of_iso R ((homologyFunctor (Modules R) i).mapIso e) (h i)

/-- The total tensor complex of two complexes vanishing below `a` and below `b` vanishes below
`a + b`. -/
theorem isStrictlyGE_mapBifunctor (P Q : CochainComplex (Modules R) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [Q.IsStrictlyGE b] :
    CochainComplex.IsStrictlyGE (HomologicalComplex.mapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)) (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (P.X p)).obj (Q.X q)) := by
    by_cases hp : p < a
    · exact ((Stacks.SheafOfModules.Tensor.sheafTensor R).map_isZero
        (P.isZero_of_isStrictlyGE a p hp)).obj _
    · exact ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (P.X p)).map_isZero
        (Q.isZero_of_isStrictlyGE b q (by dsimp at hpq; omega))
  exact hz.eq_of_src _ _

variable (T : DerivedTensorProduct R)

/-- For `A` in `D^{≥ 0}(O)` and a flat `O`-module `G`, the derived tensor product
`A ⊗^𝐋_O G[c]` lies in `D^{≥ c}(O)`. -/
theorem isGE_tensor_singleFunctor_of_isFlat (A : DerivedModules R) [A.IsGE 0] (G : Modules R)
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) G) (c : ℤ) :
    ((T.tensor.obj A).obj ((singleFunctor (Modules R) c).obj G)).IsGE c := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := A.exists_iso_Q_obj_of_isGE 0
  have hK := Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R G hG c
  have e := ((T.tensor.mapIso eP).app _) ≪≫
    (T.tensor.obj (Q.obj P)).mapIso ((singleFunctorIsoCompQ (Modules R) c).app G) ≪≫
    T.comparisonRight P ((HomologicalComplex.single _ (ComplexShape.up ℤ) c).obj G) hK
  have := isStrictlyGE_mapBifunctor P
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) c).obj G) 0 c
  rw [zero_add] at this
  have h : (Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex R).obj P).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) c).obj G))).IsGE c := by
    show (Q.obj (HomologicalComplex.mapBifunctor P
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) c).obj G)
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ))).IsGE c
    infer_instance
  exact TStructure.t.isGE_of_iso e.symm c

variable (R) in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M : Modules R, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)] in
/-- Truncating from above keeps the cohomology sheaves flat. -/
lemma hasFlatHomology_truncLT {E : DerivedModules R} (h : HasFlatHomology R E) (c : ℤ) :
    HasFlatHomology R ((TStructure.t.truncLT c).obj E) := fun i => by
  by_cases hi : i < c
  · have := DerivedCategory.isIso_homologyMap_truncLTι_app c i hi E
    exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso R
      (asIso ((homologyFunctor (Modules R) i).map ((TStructure.t.truncLTι c).app E))).symm (h i)
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero R
      (isZero_of_isLE _ (c - 1) i (by omega))

variable (R) in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M : Modules R, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)] in
/-- Truncating from below keeps the cohomology sheaves flat. -/
lemma hasFlatHomology_truncGE {E : DerivedModules R} (h : HasFlatHomology R E) (c : ℤ) :
    HasFlatHomology R ((TStructure.t.truncGE c).obj E) := fun i => by
  by_cases hi : c ≤ i
  · have := DerivedCategory.isIso_homologyMap_truncGEπ_app c i hi E
    exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso R
      (asIso ((homologyFunctor (Modules R) i).map ((TStructure.t.truncGEπ c).app E))) (h i)
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero R
      (isZero_of_isGE _ c i (by omega))

/-- For `A` in `D^{≥ 0}(O)` and `E` in `D^{≥ a}(O) ∩ D^{≤ a - 1 + n}(O)` with flat cohomology
sheaves, `A ⊗^𝐋_O E` lies in `D^{≥ a}(O)`. -/
theorem isGE_tensor_of_hasFlatHomology_of_isLE (A : DerivedModules R) [A.IsGE 0] (a : ℤ) :
    ∀ (n : ℕ) (E : DerivedModules R), E.IsGE a → E.IsLE (a - 1 + n) → HasFlatHomology R E →
      ((T.tensor.obj A).obj E).IsGE a
  | 0, E, _, _, _ => by
    have hz : IsZero E := TStructure.t.isZero E (a - 1 + ((0 : ℕ) : ℤ)) a (by push_cast; omega)
    exact TStructure.t.isGE_of_isZero ((T.tensor.obj A).map_isZero hz) a
  | n + 1, E, hge, hle, hfl => by
    let := T.commShift_right A
    have := T.exact_right A
    have := hge
    have := hle
    have : E.IsLE (a + n) :=
      TStructure.t.isLE_of_le E (a - 1 + ((n + 1 : ℕ) : ℤ)) (a + n) (by push_cast; omega)
    have hT := TStructure.t.triangleLTGE_distinguished (a + n) E
    have h₁ : ((T.tensor.obj A).obj ((TStructure.t.truncLT (a + n)).obj E)).IsGE a :=
      isGE_tensor_of_hasFlatHomology_of_isLE A a n _ inferInstance
        (TStructure.t.isLE_of_le _ (a + n - 1) _ (by omega))
        (hasFlatHomology_truncLT R hfl (a + n))
    have h₃ : ((T.tensor.obj A).obj ((TStructure.t.truncGE (a + n)).obj E)).IsGE a := by
      obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
        ((TStructure.t.truncGE (a + n)).obj E) (a + n)
      have hY : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) Y :=
        AlgebraicGeometry.SheafOfModules.IsFlat.of_iso R
          ((homologyFunctor (Modules R) (a + n)).mapIso e ≪≫
            (singleFunctorCompHomologyFunctorIso (Modules R) (a + n)).app Y)
          (hasFlatHomology_truncGE R hfl (a + n) (a + n))
      have := isGE_tensor_singleFunctor_of_isFlat T A Y hY (a + n)
      have := TStructure.t.isGE_of_iso ((T.tensor.obj A).mapIso e.symm) (a + n)
      exact TStructure.t.isGE_of_ge _ a (a + n) (by omega)
    exact TStructure.t.isGE₂ _ ((T.tensor.obj A).map_distinguished _ hT) a h₁ h₃

/-- A colimit of zero objects is zero. -/
lemma isZero_of_isColimit_of_isZero {D J' : Type*} [Category D] [Category J'] [HasZeroMorphisms D]
    {F : J' ⥤ D} {c : Cocone F} (hc : IsColimit c) (h : ∀ j, IsZero (F.obj j)) : IsZero c.pt := by
  rw [IsZero.iff_id_eq_zero]
  exact hc.hom_ext fun j => (h j).eq_of_src _ _

/-- For `A` in `D^{≥ 0}(O)` and `E` in `D^{≥ a}(O)` all of whose cohomology sheaves are flat,
`A ⊗^𝐋_O E` lies in `D^{≥ a}(O)`. No bound from above is assumed on `E`. -/
theorem isGE_tensor_of_hasFlatHomology (A : DerivedModules R) [A.IsGE 0] (a : ℤ)
    (E : DerivedModules R) [E.IsGE a] (hE : HasFlatHomology R E) :
    ((T.tensor.obj A).obj E).IsGE a := by
  obtain ⟨L, hL, ⟨eL⟩⟩ := E.exists_iso_Q_obj_of_isGE a
  obtain ⟨P, f, hP, hf⟩ := exists_kFlat_quasiIso R (Q.objPreimage A)
  have : IsIso (Q.map f) := (isIso_Q_map_iff_quasiIso (C := Modules R) f).2 hf
  let eA : Q.obj P ≅ A := asIso (Q.map f) ≪≫ Q.objObjPreimageIso A
  have : (Q.obj P).IsGE 0 := TStructure.t.isGE_of_iso eA.symm 0
  let F := (Stacks.SheafOfModules.Tensor.tensorComplex R).obj P
  have hcmp (K : CochainComplex (Modules R) ℤ) :
      (T.tensor.obj (Q.obj P)).obj (Q.obj K) ≅ Q.obj (F.obj K) :=
    (DerivedTensorProduct.comparisonLeftFac R T P hP).app K
  suffices h : (Q.obj (F.obj L)).IsGE a by
    have h' : ((T.tensor.obj (Q.obj P)).obj (Q.obj L)).IsGE a :=
      TStructure.t.isGE_of_iso (hcmp L).symm a
    exact TStructure.t.isGE_of_iso ((T.tensor.mapIso eA).app _ ≪≫
      (T.tensor.obj A).mapIso eL.symm) a
  have hn (n : ℕ) : (Q.obj (F.obj (L.truncLE (n : ℤ)))).IsGE a := by
    have : (L.truncLE (n : ℤ)).IsStrictlyGE a := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      have hz := L.isZero_of_isStrictlyGE a i hi
      rw [IsZero.iff_id_eq_zero, ← cancel_mono ((L.ιTruncLE (n : ℤ)).f i)]
      exact hz.eq_of_tgt _ _
    have hfl : HasFlatHomology R (Q.obj (L.truncLE (n : ℤ))) := fun i => by
      by_cases hi : i ≤ n
      · have hφ : IsIso (HomologicalComplex.homologyMap (L.ιTruncLE (n : ℤ)) i) := by
          rw [← quasiIsoAt_iff_isIso_homologyMap]
          exact L.quasiIsoAt_ιTruncLE (n : ℤ) i hi
        have e₁ : (homologyFunctor (Modules R) i).obj (Q.obj (L.truncLE (n : ℤ))) ≅
            (homologyFunctor (Modules R) i).obj E :=
          (homologyFunctorFactors (Modules R) i).app _ ≪≫
            @asIso _ _ _ _ (HomologicalComplex.homologyMap (L.ιTruncLE (n : ℤ)) i) hφ ≪≫
            ((homologyFunctorFactors (Modules R) i).app L).symm ≪≫
            (homologyFunctor (Modules R) i).mapIso eL.symm
        exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso R e₁.symm (hE i)
      · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero R
          (isZero_of_isLE _ (n : ℤ) i (by omega))
    have := isGE_tensor_of_hasFlatHomology_of_isLE T (Q.obj P) a ((n : ℤ) - a + 1).toNat
      (Q.obj (L.truncLE (n : ℤ))) inferInstance
      (TStructure.t.isLE_of_le _ (n : ℤ) _ (by omega)) hfl
    exact TStructure.t.isGE_of_iso (hcmp _) a
  have hF : PreservesColimitsOfShape ℕ F := by
    have h₁ := CochainComplex.KFlatBifunctor.preservesColimitsOfShape_mapBifunctorObj
      (J := ℕ) (Stacks.SheafOfModules.Tensor.sheafTensor R) P (fun M => by
        have := Stacks.SheafOfModules.preservesColimits_sheafTensorObj R M
        have : PreservesColimitsOfSize.{0, 0}
            ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M) :=
          preservesSmallestColimits_of_preservesColimits _
        infer_instance)
    have h₂ : PreservesColimitsOfShape ℕ
        (HomologicalComplex₂.totalFunctor (Modules R) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)) :=
      CochainComplex.KFlatBifunctor.preservesColimitsOfShape_totalFunctor
    have h₃ : PreservesColimitsOfShape ℕ
        (CochainComplex.KFlatBifunctor.totFunctor
          (Stacks.SheafOfModules.Tensor.sheafTensor R) P) :=
      comp_preservesColimitsOfShape _ _
    exact preservesColimitsOfShape_of_natIso (tensorComplexObjIso R P).symm
  have := SheafOfModules.DifferentialGradedModule.hasExactColimitsOfShape_nat
    (Stacks.SheafOfModules.Tensor.ringSheaf R)
  rw [isGE_Q_obj_iff, CochainComplex.isGE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have : PreservesColimitsOfShape ℕ
      (HomologicalComplex.homologyFunctor (Modules R) (ComplexShape.up ℤ) i) :=
    Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor (ComplexShape.up ℤ) i
  have hc := isColimitOfPreserves (F ⋙ HomologicalComplex.homologyFunctor _ _ i)
    L.isColimitTruncLETowerCocone
  refine isZero_of_isColimit_of_isZero hc fun n => ?_
  have := hn n
  exact ((Q.obj (F.obj (L.truncLE (n : ℤ)))).isZero_of_isGE a i hi).of_iso
    ((homologyFunctorFactors (Modules R) i).app _).symm

variable (R) in
/-- The functor `A[0] ⊗^𝐋_O -` for a sheaf of modules `A` placed in degree zero. -/
abbrev singleTensor (A : Modules R) : DerivedModules R ⥤ DerivedModules R :=
  (derivedTensorProductFunctor R).obj (Q.obj (sg R A))

/-- For `E` with flat cohomology sheaves, the inclusion `τ^{≤ t}E ⟶ E` induces an isomorphism
`H^t(A[0] ⊗^𝐋 τ^{≤ t}E) ≅ H^t(A[0] ⊗^𝐋 E)`. -/
lemma isIso_homologyMap_singleTensor_truncLTι (A : Modules R) (E : DerivedModules R)
    (hE : HasFlatHomology R E) (t : ℤ) :
    IsIso ((homologyFunctor (Modules R) t).map
      ((singleTensor R A).map ((TStructure.t.truncLTι (t + 1)).app E))) := by
  let := (canonicalDerivedTensorProduct R).commShift_right (Q.obj (sg R A))
  have := (canonicalDerivedTensorProduct R).exact_right (Q.obj (sg R A))
  let Tr := (singleTensor R A).mapTriangle.obj ((TStructure.t.triangleLTGE (t + 1)).obj E)
  have hT : Tr ∈ distTriang _ := (singleTensor R A).map_distinguished _
    (TStructure.t.triangleLTGE_distinguished (t + 1) E)
  have h₃ : Tr.obj₃.IsGE (t + 1) :=
    isGE_tensor_of_hasFlatHomology (canonicalDerivedTensorProduct R) (Q.obj (sg R A)) (t + 1)
      ((TStructure.t.truncGE (t + 1)).obj E) (hasFlatHomology_truncGE R hE (t + 1))
  have he : Epi ((homologyFunctor (Modules R) t).map Tr.mor₁) := by
    rw [HomologySequence.epi_homologyMap_mor₁_iff Tr hT t]
    exact (isZero_of_isGE Tr.obj₃ (t + 1) t (by omega)).eq_of_tgt _ _
  have hm : Mono ((homologyFunctor (Modules R) t).map Tr.mor₁) := by
    rw [HomologySequence.mono_homologyMap_mor₁_iff Tr hT (t - 1) t (by omega)]
    exact (isZero_of_isGE Tr.obj₃ (t + 1) (t - 1) (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi ((homologyFunctor (Modules R) t).map Tr.mor₁)

/-- For any `E`, the projection `E ⟶ τ^{≥ t}E` induces an isomorphism on `H^t(A[0] ⊗^𝐋 -)`. -/
lemma isIso_homologyMap_singleTensor_truncGEπ (A : Modules R) (E : DerivedModules R) (t : ℤ) :
    IsIso ((homologyFunctor (Modules R) t).map
      ((singleTensor R A).map ((TStructure.t.truncGEπ t).app E))) := by
  let := (canonicalDerivedTensorProduct R).commShift_right (Q.obj (sg R A))
  have := (canonicalDerivedTensorProduct R).exact_right (Q.obj (sg R A))
  let Tr := (singleTensor R A).mapTriangle.obj ((TStructure.t.triangleLTGE t).obj E)
  have hT : Tr ∈ distTriang _ := (singleTensor R A).map_distinguished _
    (TStructure.t.triangleLTGE_distinguished t E)
  have h₁ : Tr.obj₁.IsLE (t - 1) := by
    have := isLE_derivedTensorProduct R (canonicalDerivedTensorProduct R) (Q.obj (sg R A))
      ((TStructure.t.truncLT t).obj E) 0 (t - 1)
    rw [zero_add] at this
    exact this
  have he : Epi ((homologyFunctor (Modules R) t).map Tr.mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff Tr hT t (t + 1) rfl]
    exact (isZero_of_isLE Tr.obj₁ (t - 1) (t + 1) (by omega)).eq_of_tgt _ _
  have hm : Mono ((homologyFunctor (Modules R) t).map Tr.mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff Tr hT t]
    exact (isZero_of_isLE Tr.obj₁ (t - 1) t (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi ((homologyFunctor (Modules R) t).map Tr.mor₂)

/-- For a sheaf of `O`-modules `A` and an object `E` of `D(O)` all of whose cohomology sheaves are
flat, the isomorphism `H^t(A[0] ⊗^𝐋_O E) ≅ A ⊗_O H^t(E)`. -/
def tensorHomologyIsoOfHasFlatHomology (A : Modules R) (E : DerivedModules R)
    (hE : HasFlatHomology R E) (t : ℤ) :
    (homologyFunctor (Modules R) t).obj ((singleTensor R A).obj E) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj
        ((homologyFunctor (Modules R) t).obj E) :=
  haveI := isIso_homologyMap_singleTensor_truncLTι A E hE t
  haveI := isIso_homologyMap_singleTensor_truncGEπ A ((TStructure.t.truncLT (t + 1)).obj E) t
  (asIso ((homologyFunctor (Modules R) t).map
      ((singleTensor R A).map ((TStructure.t.truncLTι (t + 1)).app E)))).symm ≪≫
    asIso ((homologyFunctor (Modules R) t).map
      ((singleTensor R A).map ((TStructure.t.truncGEπ t).app
        ((TStructure.t.truncLT (t + 1)).obj E)))) ≪≫
    (homologyFunctor (Modules R) t).mapIso ((singleTensor R A).mapIso
      ((truncGELTIsoHomologyFunctorCompSingleFunctor t).app E)) ≪≫
    degreeSingleTensorIso R ((homologyFunctor (Modules R) t).obj E) A t

end Stacks.DerivedTensor.RingedSite
