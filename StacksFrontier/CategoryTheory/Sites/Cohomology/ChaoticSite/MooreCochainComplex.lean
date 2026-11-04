module

public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution

/-!
# The Moore complex of a presheaf evaluated on a cosimplicial object, at general coefficients

Let `C` be a small category, let `A` be an abelian category and let `U_•` be a cosimplicial
object of `C`. Evaluating an `A`-valued presheaf `ℱ` on `U_•` gives a simplicial object of `A`,
and this module develops the Moore complex `ℱ(U_•)` of that simplicial object: the chain complex
indexed by `ℕ`, its reindexing as a cochain complex over `ℤ` with the simplicial degree `n` in
cohomological degree `-n`, its augmentation to `(colim ℱ)[0]`, and the double complex
`Z^{p,q} = (K^p(U_•))^q` of a complex `K^•` of `A`-valued presheaves together with the first of
its two filtrations.

Everything here is coefficient-free: the two inputs that the coefficient category supplies — the
presentation of the colimit injection at `U_0` as a cokernel of the degree-one differential, and
the vanishing of the positive homology of `ℱ(U_•)` on a projective `ℱ` ([Stacks, Tag 08Q9]) —
are carried as hypotheses by the statements that need them. They are discharged at abelian-group
coefficients by `Stacks.ChaoticSite.colimitι_isColimit` and
`Stacks.ChaoticSite.isZero_cosimplicialHomology_projective_succ`, and at module coefficients by
`Stacks.ChaoticSite.ModuleValued.moduleColimitι_isColimit` and
`Stacks.ChaoticSite.ModuleValued.isZero_moduleCosimplicialHomology_projective_succ`; the two
coefficient-specific files instantiate the development below with them.

## Main definitions

* `Stacks.ChaoticSite.GeneralValued.cosimplicialMooreComplex`: the Moore complex of `ℱ(U_•)`,
  functorially in `ℱ`. The abelian-group-valued and module-valued Moore complexes of the site are
  this functor at those coefficients.
* `Stacks.ChaoticSite.GeneralValued.mooreCochainComplex`: the same complex read as a cochain
  complex over `ℤ`, the simplicial degree `n` sitting in cohomological degree `-n`.
* `Stacks.ChaoticSite.GeneralValued.mooreCochainAugmentation`: the augmentation
  `ℱ(U_•) ⟶ (colim ℱ)[0]`, as a natural transformation.
* `Stacks.ChaoticSite.GeneralValued.mooreBicomplexFunctor` and
  `Stacks.ChaoticSite.GeneralValued.mooreBicomplex`: the double complex
  `Z^{p,q} = (K^p(U_•))^q`, as a functor of the complex `K^•`.

## Main results

* `Stacks.ChaoticSite.GeneralValued.d_one_zero_comp_colimitι`: the colimit injection at `U_0`
  kills the degree-one differential of `ℱ(U_•)`.
* `Stacks.ChaoticSite.GeneralValued.quasiIso_mooreCochainAugmentation`: the extended Moore
  complex of `ℱ(U_•)` is a resolution of `colim ℱ`, given the two coefficient inputs for `ℱ`.
* `Stacks.ChaoticSite.GeneralValued.quasiIso_mooreBicomplexColumnTotalMap`: the first filtration
  of the double complex — a columnwise quasi-isomorphic augmentation gives
  `Tot(Z) ≃ colim K^•`. This is [Stacks, Tag 0133] for double complexes bounded above, with the
  hypothesis on the columns.

## Implementation notes

**Why the extended Moore complex.** The tools for [Stacks, Tag 0133] are stated for double
complexes indexed by `ℤ × ℤ` with cochain conventions in both directions, so the Moore complex —
a chain complex indexed by `ℕ` — is placed in cohomological degrees `≤ 0` along
`ComplexShape.embeddingUpIntLE 0`.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open StacksDraft.TotalComplexQuasiIso

namespace Stacks.ChaoticSite.GeneralValued

universe u

/-! ### Cokernel bookkeeping -/

section Cokernels

variable {A : Type*} [Category* A] [Abelian A]

/-- **A morphism between two cokernels of one morphism which is compatible with the projections
is an isomorphism.** -/
lemma isIso_of_isColimit_cokernelCofork {X Y Z W : A} {f : X ⟶ Y}
    {p : Y ⟶ Z} (hp : f ≫ p = 0) (hpc : IsColimit (CokernelCofork.ofπ p hp))
    {g : Y ⟶ W} (hg : f ≫ g = 0) (hgc : IsColimit (CokernelCofork.ofπ g hg))
    (u : Z ⟶ W) (hu : p ≫ u = g) : IsIso u := by
  have hv : g ≫ hgc.desc (CokernelCofork.ofπ p hp) = p := by
    simpa using hgc.fac (CokernelCofork.ofπ p hp) WalkingParallelPair.one
  refine ⟨hgc.desc (CokernelCofork.ofπ p hp), Cofork.IsColimit.hom_ext hpc ?_,
    Cofork.IsColimit.hom_ext hgc ?_⟩
  · have h : p ≫ u ≫ hgc.desc (CokernelCofork.ofπ p hp) = p ≫ 𝟙 Z := by
      rw [← Category.assoc, hu, hv, Category.comp_id]
    simpa using h
  · have h : g ≫ hgc.desc (CokernelCofork.ofπ p hp) ≫ u = g ≫ 𝟙 W := by
      rw [← Category.assoc, hv, hu, Category.comp_id]
    simpa using h

/-- **A cokernel of `f` is a cokernel of `u ≫ f ≫ v` for `u` an epimorphism and `v` an
isomorphism**, the projection being corrected by `v⁻¹`. -/
def isColimit_cokernelCofork_comp {X' X Y Y' Z : A} (u : X' ⟶ X) [Epi u] {f : X ⟶ Y}
    (v : Y ≅ Y') {p : Y ⟶ Z} (hp : f ≫ p = 0) (hpc : IsColimit (CokernelCofork.ofπ p hp))
    {f' : X' ⟶ Y'} (hf' : f' = u ≫ f ≫ v.hom) (h0 : f' ≫ v.inv ≫ p = 0) :
    IsColimit (CokernelCofork.ofπ (v.inv ≫ p) h0) := by
  subst hf'
  have key : ∀ S : CokernelCofork (u ≫ f ≫ v.hom), f ≫ v.hom ≫ Cofork.π S = 0 := by
    intro S
    have hS : (u ≫ f ≫ v.hom) ≫ Cofork.π S = 0 := CokernelCofork.condition S
    simp only [Category.assoc] at hS
    exact (cancel_epi u).1 (by rw [comp_zero]; exact hS)
  have hfac : ∀ S : CokernelCofork (u ≫ f ≫ v.hom),
      p ≫ hpc.desc (CokernelCofork.ofπ (v.hom ≫ Cofork.π S) (key S)) = v.hom ≫ Cofork.π S :=
    fun S => by
      simpa using hpc.fac (CokernelCofork.ofπ (v.hom ≫ Cofork.π S) (key S))
        WalkingParallelPair.one
  refine Cofork.IsColimit.mk _
    (fun S => hpc.desc (CokernelCofork.ofπ (v.hom ≫ Cofork.π S) (key S))) (fun S => ?_)
    (fun S m hm => ?_)
  · have h : (v.inv ≫ p) ≫ hpc.desc (CokernelCofork.ofπ (v.hom ≫ Cofork.π S) (key S)) =
      Cofork.π S := by rw [Category.assoc, hfac S, Iso.inv_hom_id_assoc]
    simpa using h
  · have hm' : (v.inv ≫ p) ≫ m = Cofork.π S := by simpa using hm
    refine Cofork.IsColimit.hom_ext hpc ?_
    have h2 : p ≫ m = v.hom ≫ Cofork.π S :=
      calc p ≫ m = v.hom ≫ (v.inv ≫ p) ≫ m := by
            rw [Category.assoc, Iso.hom_inv_id_assoc]
        _ = v.hom ≫ Cofork.π S := by rw [hm']
    have h : p ≫ m = p ≫ hpc.desc (CokernelCofork.ofπ (v.hom ≫ Cofork.π S) (key S)) := by
      rw [h2, hfac S]
    simpa using h

/-- **Composing a cokernel with an isomorphism gives a cokernel.** -/
def isColimit_cokernelCofork_comp_iso {X Y Z Z' : A} {f : X ⟶ Y}
    {p : Y ⟶ Z} (hp : f ≫ p = 0) (hpc : IsColimit (CokernelCofork.ofπ p hp)) (i : Z ≅ Z')
    (h0 : f ≫ p ≫ i.hom = 0) :
    IsColimit (CokernelCofork.ofπ (p ≫ i.hom) h0) :=
  IsColimit.ofIsoColimit hpc (Cofork.ext i (by simp))

end Cokernels

/-- The degree-one alternating face map differential of `U.op ⋙ G` is a difference of cofaces. -/
private theorem alternatingFaceMapComplex_d_one_zero_op {C : Type u} [Category* C] {A : Type*}
    [Category* A] [Preadditive A] (U : CosimplicialObject C) (G : Cᵒᵖ ⥤ A) :
    ((alternatingFaceMapComplex A).obj (U.op ⋙ G)).d 1 0 =
      G.map (U.map (SimplexCategory.δ (0 : Fin 2))).op -
        G.map (U.map (SimplexCategory.δ (1 : Fin 2))).op := by
  change ((alternatingFaceMapComplex A).obj (U.op ⋙ G)).d (0 + 1) 0 = _
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d _ 0,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_smul, neg_one_zsmul, ← sub_eq_add_neg]
  rfl

/-- A map to a complex in degree zero that is a cokernel of `d^{-1,0}` there is `QuasiIsoAt 0`. -/
private theorem quasiIsoAt_zero_of_isColimit {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} {Y : A} (φ : K ⟶ L) (hd : K.d 0 1 = 0)
    (hdL : L.d 0 1 = 0) (hdL' : L.d (-1) 0 = 0) {a : K.X 0 ⟶ Y} {ha : K.d (-1) 0 ≫ a = 0}
    (i : Y ⟶ L.X 0) [IsIso i] (hφ : φ.f 0 = a ≫ i) (hc : IsColimit (CokernelCofork.ofπ a ha)) :
    QuasiIsoAt φ 0 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hLp : IsIso (L.pOpcycles 0) := HomologicalComplex.isIso_pOpcycles _ (-1) 0 (by simp) hdL'
  have hop : IsIso (HomologicalComplex.opcyclesMap φ 0) :=
    isIso_of_isColimit_cokernelCofork (K.d_pOpcycles (-1) 0) (K.opcyclesIsCokernel (-1) 0 (by simp))
      (g := a ≫ i ≫ L.pOpcycles 0) (by rw [← Category.assoc, ha, zero_comp])
      (isColimit_cokernelCofork_comp_iso _ hc (asIso (i ≫ L.pOpcycles 0)) _) _
      ((HomologicalComplex.p_opcyclesMap _ 0).trans (by rw [hφ, Category.assoc]))
  have := HomologicalComplex.isIso_homologyι K 0 1 (by simp) hd
  have := HomologicalComplex.isIso_homologyι L 0 1 (by simp) hdL
  have : IsIso (HomologicalComplex.homologyMap φ 0 ≫ L.homologyι 0) := by
    rw [HomologicalComplex.homologyι_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (L.homologyι 0)

/-- A map `K ⟶ Y[0]` that is a quasi-isomorphism in degree zero and has `K` acyclic elsewhere. -/
private theorem quasiIso_of_single_zero {A : Type*} [Category* A] [Abelian A]
    {K : CochainComplex A ℤ} {Y : A}
    (φ : K ⟶ (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj Y)
    (h0 : QuasiIsoAt φ 0) (hK : ∀ q : ℤ, q ≠ 0 → IsZero (K.homology q)) : QuasiIso φ := by
  rw [quasiIso_iff]
  intro q
  by_cases hq : q = 0
  · exact hq ▸ h0
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    exact IsZero.isIso (hK q hq)
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 Y q hq) _

/-- Naturality of morphisms to `Y[0]` built from their degree-zero components. -/
private theorem comp_mkHomToSingle_naturality {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} (m : K ⟶ L) {Y Z : A} (g : Y ⟶ Z) {aK : K.X 0 ⟶ Y} {aL : L.X 0 ⟶ Z}
    (hK : ∀ i, (ComplexShape.up ℤ).Rel i 0 → K.d i 0 ≫ aK = 0)
    (hL : ∀ i, (ComplexShape.up ℤ).Rel i 0 → L.d i 0 ≫ aL = 0) (h : m.f 0 ≫ aL = aK ≫ g) :
    m ≫ HomologicalComplex.mkHomToSingle aL hL =
      HomologicalComplex.mkHomToSingle aK hK ≫
        (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map g := by
  refine HomologicalComplex.hom_ext _ _ (fun q => ?_)
  by_cases hq : q = 0
  · subst hq
    simp [HomologicalComplex.single_map_f_self, reassoc_of% h]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q hq).eq_of_tgt _ _

/-! ### The Moore complex of `ℱ(U_•)` -/

section MooreComplex

variable {C : Type u} [SmallCategory C]

/-- **The Moore complex of the evaluation of a presheaf on a cosimplicial object**: the complex
`ℱ(U_•)`, functorially in `ℱ`. The coefficient category enters only through its preadditive
structure, the alternating sum of the faces being formed in it. -/
abbrev cosimplicialMooreComplex (A : Type*) [Category* A] [Preadditive A]
    (U : CosimplicialObject C) : (Cᵒᵖ ⥤ A) ⥤ ChainComplex A ℕ :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ A).obj U.op ⋙ alternatingFaceMapComplex A

variable {A : Type*} [Category* A] [Preadditive A] (U : CosimplicialObject C)

/-- The degree-one differential of the Moore complex of `ℱ(U_•)` is the difference of the two
cofaces `U_0 ⟶ U_1`. -/
lemma cosimplicialMooreComplex_obj_d_one_zero (G : Cᵒᵖ ⥤ A) :
    ((cosimplicialMooreComplex A U).obj G).d 1 0 =
      G.map (U.map (SimplexCategory.δ (0 : Fin 2))).op -
        G.map (U.map (SimplexCategory.δ (1 : Fin 2))).op :=
  alternatingFaceMapComplex_d_one_zero_op U G

/-- **The colimit injection at `U_0` kills the degree-one differential**: the two cofaces become
equal after composing with the injections of the colimit over `Cᵒᵖ`. -/
theorem d_one_zero_comp_colimitι [HasColimitsOfShape Cᵒᵖ A] (G : Cᵒᵖ ⥤ A) :
    ((cosimplicialMooreComplex A U).obj G).d 1 0 ≫
        colimit.ι G (op (U.obj (SimplexCategory.mk 0))) = 0 := by
  rw [cosimplicialMooreComplex_obj_d_one_zero, Preadditive.sub_comp,
    colimit.w G (U.map (SimplexCategory.δ (0 : Fin 2))).op,
    colimit.w G (U.map (SimplexCategory.δ (1 : Fin 2))).op, sub_self]

end MooreComplex

/-! ### The same, for a category whose morphisms live in an arbitrary universe

The declarations below carry the names of their counterparts above with a prime, and drop the
smallness of `C`: its objects and its morphisms may live in different universes, as they do at
the site of [Stacks, Tag 08PR]. -/

universe vC

section MooreComplex

variable {C : Type u} [Category.{vC} C]

/-- **The Moore complex of the evaluation of a presheaf on a cosimplicial object**: the complex
`ℱ(U_•)`, functorially in `ℱ`. The coefficient category enters only through its preadditive
structure, the alternating sum of the faces being formed in it. -/
abbrev cosimplicialMooreComplex' (A : Type*) [Category* A] [Preadditive A]
    (U : CosimplicialObject C) : (Cᵒᵖ ⥤ A) ⥤ ChainComplex A ℕ :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ A).obj U.op ⋙ alternatingFaceMapComplex A

variable {A : Type*} [Category* A] [Preadditive A] (U : CosimplicialObject C)

/-- The degree-one differential of the Moore complex of `ℱ(U_•)` is the difference of the two
cofaces `U_0 ⟶ U_1`. -/
lemma cosimplicialMooreComplex_obj_d_one_zero' (G : Cᵒᵖ ⥤ A) :
    ((cosimplicialMooreComplex' A U).obj G).d 1 0 =
      G.map (U.map (SimplexCategory.δ (0 : Fin 2))).op -
        G.map (U.map (SimplexCategory.δ (1 : Fin 2))).op :=
  alternatingFaceMapComplex_d_one_zero_op U G

/-- **The colimit injection at `U_0` kills the degree-one differential**: the two cofaces become
equal after composing with the injections of the colimit over `Cᵒᵖ`. -/
theorem d_one_zero_comp_colimitι' [HasColimitsOfShape Cᵒᵖ A] (G : Cᵒᵖ ⥤ A) :
    ((cosimplicialMooreComplex' A U).obj G).d 1 0 ≫
        colimit.ι G (op (U.obj (SimplexCategory.mk 0))) = 0 := by
  rw [cosimplicialMooreComplex_obj_d_one_zero', Preadditive.sub_comp,
    colimit.w G (U.map (SimplexCategory.δ (0 : Fin 2))).op,
    colimit.w G (U.map (SimplexCategory.δ (1 : Fin 2))).op, sub_self]

end MooreComplex

/-! ### The Moore complex of `ℱ(U_•)` as a cochain complex over `ℤ` -/

section MooreCochain

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **The Moore complex of `ℱ(U_•)` read as a cochain complex over `ℤ`**, the simplicial degree
`n` sitting in cohomological degree `-n`. This is the reindexing along
`ComplexShape.embeddingUpIntLE 0` of
`Stacks.ChaoticSite.GeneralValued.cosimplicialMooreComplex`. -/
abbrev mooreCochainComplex (A : Type*) [Category* A] [Abelian A] :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℤ :=
  cosimplicialMooreComplex A U ⋙
    (ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor A

variable {A : Type*} [Category* A] [Abelian A] (F : Cᵒᵖ ⥤ A)

/-- The extended Moore complex vanishes in positive cohomological degrees. -/
lemma isZero_mooreCochainComplex_X (q : ℤ) (hq : 0 < q) :
    IsZero (((mooreCochainComplex U A).obj F).X q) :=
  HomologicalComplex.isZero_extend_X _ _ _
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 q).2 hq)

/-- The degree-zero term of the extended Moore complex is `ℱ(U_0)`. -/
def mooreCochainXZeroIso :
    ((mooreCochainComplex U A).obj F).X 0 ≅ ((cosimplicialMooreComplex A U).obj F).X 0 :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 0) (by simp)

/-- The degree `-1` term of the extended Moore complex is `ℱ(U_1)`. -/
def mooreCochainXNegOneIso :
    ((mooreCochainComplex U A).obj F).X (-1) ≅ ((cosimplicialMooreComplex A U).obj F).X 1 :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 1) (by simp)

/-- The differential `d^{-1,0}` of the extended Moore complex is the degree-one differential of
the Moore complex. -/
lemma mooreCochainComplex_d_neg_one_zero :
    ((mooreCochainComplex U A).obj F).d (-1) 0 =
      (mooreCochainXNegOneIso U F).hom ≫
        ((cosimplicialMooreComplex A U).obj F).d 1 0 ≫ (mooreCochainXZeroIso U F).inv :=
  HomologicalComplex.extend_d_eq _ _ (by simp) (by simp)

/-- The extended Moore complex is exact in positive cohomological degrees, where it vanishes. -/
lemma isZero_mooreCochainComplex_homology_pos (q : ℤ) (hq : 0 < q) :
    IsZero (((mooreCochainComplex U A).obj F).homology q) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact HomologicalComplex.extend_exactAt _ _ _
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 q).2 hq)

/-- **The extended Moore complex has no cohomology in negative degrees as soon as `ℱ(U_•)` has
none in positive simplicial degrees**: the two cohomologies are the same groups, reindexed. The
hypothesis is what [Stacks, Tag 08Q9] supplies for a projective `ℱ`. -/
lemma isZero_mooreCochainComplex_homology_neg
    (hzero : ∀ n : ℕ, IsZero (((cosimplicialMooreComplex A U).obj F).homology (n + 1)))
    (q : ℤ) (hq : q < 0) :
    IsZero (((mooreCochainComplex U A).obj F).homology q) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f (n + 1) = q :=
    ⟨(-q - 1).toNat, by simp; omega⟩
  exact ((HomologicalComplex.extendHomologyIso _
    (ComplexShape.embeddingUpIntLE (0 : ℤ)) hn).isZero_iff).2 (hzero n)

end MooreCochain

section MooreCochain

variable {C : Type u} [Category.{vC} C] (U : CosimplicialObject C)

/-- **The Moore complex of `ℱ(U_•)` read as a cochain complex over `ℤ`**, the simplicial degree
`n` sitting in cohomological degree `-n`. This is the reindexing along
`ComplexShape.embeddingUpIntLE 0` of
`Stacks.ChaoticSite.GeneralValued.cosimplicialMooreComplex'`. -/
abbrev mooreCochainComplex' (A : Type*) [Category* A] [Abelian A] :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℤ :=
  cosimplicialMooreComplex' A U ⋙
    (ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor A

variable {A : Type*} [Category* A] [Abelian A] (F : Cᵒᵖ ⥤ A)

/-- The extended Moore complex vanishes in positive cohomological degrees. -/
lemma isZero_mooreCochainComplex_X' (q : ℤ) (hq : 0 < q) :
    IsZero (((mooreCochainComplex' U A).obj F).X q) :=
  HomologicalComplex.isZero_extend_X _ _ _
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 q).2 hq)

/-- The degree-zero term of the extended Moore complex is `ℱ(U_0)`. -/
def mooreCochainXZeroIso' :
    ((mooreCochainComplex' U A).obj F).X 0 ≅ ((cosimplicialMooreComplex' A U).obj F).X 0 :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 0) (by simp)

/-- The degree `-1` term of the extended Moore complex is `ℱ(U_1)`. -/
def mooreCochainXNegOneIso' :
    ((mooreCochainComplex' U A).obj F).X (-1) ≅ ((cosimplicialMooreComplex' A U).obj F).X 1 :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := 1) (by simp)

/-- The differential `d^{-1,0}` of the extended Moore complex is the degree-one differential of
the Moore complex. -/
lemma mooreCochainComplex_d_neg_one_zero' :
    ((mooreCochainComplex' U A).obj F).d (-1) 0 =
      (mooreCochainXNegOneIso' U F).hom ≫
        ((cosimplicialMooreComplex' A U).obj F).d 1 0 ≫ (mooreCochainXZeroIso' U F).inv :=
  HomologicalComplex.extend_d_eq _ _ (by simp) (by simp)

/-- The extended Moore complex is exact in positive cohomological degrees, where it vanishes. -/
lemma isZero_mooreCochainComplex_homology_pos' (q : ℤ) (hq : 0 < q) :
    IsZero (((mooreCochainComplex' U A).obj F).homology q) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact HomologicalComplex.extend_exactAt _ _ _
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 q).2 hq)

/-- **The extended Moore complex has no cohomology in negative degrees as soon as `ℱ(U_•)` has
none in positive simplicial degrees**: the two cohomologies are the same groups, reindexed. The
hypothesis is what [Stacks, Tag 08Q9] supplies for a projective `ℱ`. -/
lemma isZero_mooreCochainComplex_homology_neg'
    (hzero : ∀ n : ℕ, IsZero (((cosimplicialMooreComplex' A U).obj F).homology (n + 1)))
    (q : ℤ) (hq : q < 0) :
    IsZero (((mooreCochainComplex' U A).obj F).homology q) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f (n + 1) = q :=
    ⟨(-q - 1).toNat, by simp; omega⟩
  exact ((HomologicalComplex.extendHomologyIso _
    (ComplexShape.embeddingUpIntLE (0 : ℤ)) hn).isZero_iff).2 (hzero n)

end MooreCochain

/-! ### The augmentation of the extended Moore complex -/

section Augmentation

variable {C : Type u} [SmallCategory C] {A : Type*} [Category* A] [Abelian A]
  [HasColimitsOfShape Cᵒᵖ A] (U : CosimplicialObject C) (F : Cᵒᵖ ⥤ A)

/-- **The degree-zero component of the augmentation `ℱ(U_•) ⟶ (colim ℱ)[0]`**: the colimit
injection at `U_0`, read on the degree-zero term of the extended Moore complex. -/
def mooreCochainAug₀ :
    ((mooreCochainComplex U A).obj F).X 0 ⟶ (colim : (Cᵒᵖ ⥤ A) ⥤ A).obj F :=
  (mooreCochainXZeroIso U F).hom ≫ colimit.ι F (op (U.obj (SimplexCategory.mk 0)))

/-- The degree-zero component of the augmentation kills the incoming differential: this is the
relation `Stacks.ChaoticSite.GeneralValued.d_one_zero_comp_colimitι` of the Moore complex. -/
lemma mooreCochainAug₀_comp (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i 0) :
    ((mooreCochainComplex U A).obj F).d i 0 ≫ mooreCochainAug₀ U F = 0 := by
  simp only [ComplexShape.up_Rel] at hi
  obtain rfl : i = -1 := by omega
  rw [mooreCochainAug₀, mooreCochainComplex_d_neg_one_zero, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, d_one_zero_comp_colimitι, comp_zero]

variable {F}

/-- The augmentation is natural in the presheaf: in degree zero it is the colimit injection at
`U_0`, and the colimit injections are natural. -/
lemma mooreCochainAugmentation_naturality {G : Cᵒᵖ ⥤ A} (η : F ⟶ G) :
    (mooreCochainComplex U A).map η ≫
        HomologicalComplex.mkHomToSingle (mooreCochainAug₀ U G) (mooreCochainAug₀_comp U G) =
      HomologicalComplex.mkHomToSingle (mooreCochainAug₀ U F) (mooreCochainAug₀_comp U F) ≫
        (colim ⋙ HomologicalComplex.single A (ComplexShape.up ℤ) 0).map η := by
  refine comp_mkHomToSingle_naturality _ (colim.map η) _ _ ?_
  have hmap : ((mooreCochainComplex U A).map η).f 0 =
      (mooreCochainXZeroIso U F).hom ≫
        ((cosimplicialMooreComplex A U).map η).f 0 ≫ (mooreCochainXZeroIso U G).inv :=
    HomologicalComplex.extendMap_f _ _ (by simp)
  rw [hmap, mooreCochainAug₀, mooreCochainAug₀]
  simp

variable (F)

/-- **The augmentation `ℱ(U_•) ⟶ (colim ℱ)[0]`**, as a natural transformation of functors of the
presheaf `ℱ`: in degree zero it is the colimit injection at `U_0`. -/
def mooreCochainAugmentation :
    mooreCochainComplex U A ⟶
      (colim : (Cᵒᵖ ⥤ A) ⥤ A) ⋙ HomologicalComplex.single A (ComplexShape.up ℤ) 0 where
  app F := HomologicalComplex.mkHomToSingle (mooreCochainAug₀ U F) (mooreCochainAug₀_comp U F)
  naturality _ _ η := mooreCochainAugmentation_naturality U η

/-- The degree-zero component of
`Stacks.ChaoticSite.GeneralValued.mooreCochainAugmentation`. -/
lemma mooreCochainAugmentation_f_zero :
    ((mooreCochainAugmentation U).app F).f 0 =
      mooreCochainAug₀ U F ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (colim.obj F)).inv :=
  HomologicalComplex.mkHomToSingle_f (mooreCochainAug₀ U F) (mooreCochainAug₀_comp U F)

/-- **The augmentation is a cokernel of the differential `d^{-1,0}`** as soon as the colimit
injection at `U_0` is a cokernel of the degree-one differential of `ℱ(U_•)`: the reindexing
changes that differential only by isomorphisms. The hypothesis is what a point resolution
supplies. -/
def mooreCochainAug₀IsColimit
    (hcolim : IsColimit (CokernelCofork.ofπ (colimit.ι F (op (U.obj (SimplexCategory.mk 0))))
      (d_one_zero_comp_colimitι U F))) :
    IsColimit (CokernelCofork.ofπ (mooreCochainAug₀ U F)
      (mooreCochainAug₀_comp U F (-1) (by simp))) :=
  isColimit_cokernelCofork_comp (mooreCochainXNegOneIso U F).hom
    (mooreCochainXZeroIso U F).symm (d_one_zero_comp_colimitι U F)
    hcolim (mooreCochainComplex_d_neg_one_zero U F) _

/-- **The augmentation is a quasi-isomorphism in degree zero**: on both sides the degree-zero
cohomology is the colimit, by the cokernel presentation of the colimit injection. -/
lemma quasiIsoAt_mooreCochainAugmentation_zero
    (hcolim : IsColimit (CokernelCofork.ofπ (colimit.ι F (op (U.obj (SimplexCategory.mk 0))))
      (d_one_zero_comp_colimitι U F))) :
    QuasiIsoAt ((mooreCochainAugmentation U).app F) 0 :=
  quasiIsoAt_zero_of_isColimit _
    ((isZero_mooreCochainComplex_X U F 1 (by omega)).eq_of_tgt _ _)
    (HomologicalComplex.single_obj_d _ _ _ _ _) (HomologicalComplex.single_obj_d _ _ _ _ _) _
    (mooreCochainAugmentation_f_zero U F) (mooreCochainAug₀IsColimit U F hcolim)

/-- **The extended Moore complex of `ℱ(U_•)` is a resolution of `colim ℱ`**, given the two
inputs the coefficient category supplies for `ℱ`: the vanishing of the positive homology of
`ℱ(U_•)` and the cokernel presentation of the colimit injection at `U_0`. For a projective `ℱ`
and a point resolution `U_•` both hold, and this is then the columnwise input to the comparison
of the two filtrations of the double complex. -/
lemma quasiIso_mooreCochainAugmentation
    (hzero : ∀ n : ℕ, IsZero (((cosimplicialMooreComplex A U).obj F).homology (n + 1)))
    (hcolim : IsColimit (CokernelCofork.ofπ (colimit.ι F (op (U.obj (SimplexCategory.mk 0))))
      (d_one_zero_comp_colimitι U F))) :
    QuasiIso ((mooreCochainAugmentation U).app F) :=
  quasiIso_of_single_zero _ (quasiIsoAt_mooreCochainAugmentation_zero U F hcolim) fun q hq => by
    rcases lt_or_gt_of_ne hq with hq | hq
    · exact isZero_mooreCochainComplex_homology_neg U F hzero q hq
    · exact isZero_mooreCochainComplex_homology_pos U F q hq

end Augmentation

section Augmentation

variable {C : Type u} [Category.{vC} C] {A : Type*} [Category* A] [Abelian A]
  [HasColimitsOfShape Cᵒᵖ A] (U : CosimplicialObject C) (F : Cᵒᵖ ⥤ A)

/-- **The degree-zero component of the augmentation `ℱ(U_•) ⟶ (colim ℱ)[0]`**: the colimit
injection at `U_0`, read on the degree-zero term of the extended Moore complex. -/
def mooreCochainAug₀' :
    ((mooreCochainComplex' U A).obj F).X 0 ⟶ (colim : (Cᵒᵖ ⥤ A) ⥤ A).obj F :=
  (mooreCochainXZeroIso' U F).hom ≫ colimit.ι F (op (U.obj (SimplexCategory.mk 0)))

/-- The degree-zero component of the augmentation kills the incoming differential: this is the
relation `Stacks.ChaoticSite.GeneralValued.d_one_zero_comp_colimitι'` of the Moore complex. -/
lemma mooreCochainAug₀_comp' (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i 0) :
    ((mooreCochainComplex' U A).obj F).d i 0 ≫ mooreCochainAug₀' U F = 0 := by
  simp only [ComplexShape.up_Rel] at hi
  obtain rfl : i = -1 := by omega
  rw [mooreCochainAug₀', mooreCochainComplex_d_neg_one_zero', Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, d_one_zero_comp_colimitι', comp_zero]

variable {F}

/-- The augmentation is natural in the presheaf: in degree zero it is the colimit injection at
`U_0`, and the colimit injections are natural. -/
lemma mooreCochainAugmentation_naturality' {G : Cᵒᵖ ⥤ A} (η : F ⟶ G) :
    (mooreCochainComplex' U A).map η ≫
        HomologicalComplex.mkHomToSingle (mooreCochainAug₀' U G) (mooreCochainAug₀_comp' U G) =
      HomologicalComplex.mkHomToSingle (mooreCochainAug₀' U F) (mooreCochainAug₀_comp' U F) ≫
        (colim ⋙ HomologicalComplex.single A (ComplexShape.up ℤ) 0).map η := by
  refine comp_mkHomToSingle_naturality _ (colim.map η) _ _ ?_
  have hmap : ((mooreCochainComplex' U A).map η).f 0 =
      (mooreCochainXZeroIso' U F).hom ≫
        ((cosimplicialMooreComplex' A U).map η).f 0 ≫ (mooreCochainXZeroIso' U G).inv :=
    HomologicalComplex.extendMap_f _ _ (by simp)
  rw [hmap, mooreCochainAug₀', mooreCochainAug₀']
  simp

variable (F)

/-- **The augmentation `ℱ(U_•) ⟶ (colim ℱ)[0]`**, as a natural transformation of functors of the
presheaf `ℱ`: in degree zero it is the colimit injection at `U_0`. -/
def mooreCochainAugmentation' :
    mooreCochainComplex' U A ⟶
      (colim : (Cᵒᵖ ⥤ A) ⥤ A) ⋙ HomologicalComplex.single A (ComplexShape.up ℤ) 0 where
  app F := HomologicalComplex.mkHomToSingle (mooreCochainAug₀' U F) (mooreCochainAug₀_comp' U F)
  naturality _ _ η := mooreCochainAugmentation_naturality' U η

/-- The degree-zero component of
`Stacks.ChaoticSite.GeneralValued.mooreCochainAugmentation'`. -/
lemma mooreCochainAugmentation_f_zero' :
    ((mooreCochainAugmentation' U).app F).f 0 =
      mooreCochainAug₀' U F ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (colim.obj F)).inv :=
  HomologicalComplex.mkHomToSingle_f (mooreCochainAug₀' U F) (mooreCochainAug₀_comp' U F)

/-- **The augmentation is a cokernel of the differential `d^{-1,0}`** as soon as the colimit
injection at `U_0` is a cokernel of the degree-one differential of `ℱ(U_•)`: the reindexing
changes that differential only by isomorphisms. The hypothesis is what a point resolution
supplies. -/
def mooreCochainAug₀IsColimit'
    (hcolim : IsColimit (CokernelCofork.ofπ (colimit.ι F (op (U.obj (SimplexCategory.mk 0))))
      (d_one_zero_comp_colimitι' U F))) :
    IsColimit (CokernelCofork.ofπ (mooreCochainAug₀' U F)
      (mooreCochainAug₀_comp' U F (-1) (by simp))) :=
  isColimit_cokernelCofork_comp (mooreCochainXNegOneIso' U F).hom
    (mooreCochainXZeroIso' U F).symm (d_one_zero_comp_colimitι' U F)
    hcolim (mooreCochainComplex_d_neg_one_zero' U F) _

/-- **The augmentation is a quasi-isomorphism in degree zero**: on both sides the degree-zero
cohomology is the colimit, by the cokernel presentation of the colimit injection. -/
lemma quasiIsoAt_mooreCochainAugmentation_zero'
    (hcolim : IsColimit (CokernelCofork.ofπ (colimit.ι F (op (U.obj (SimplexCategory.mk 0))))
      (d_one_zero_comp_colimitι' U F))) :
    QuasiIsoAt ((mooreCochainAugmentation' U).app F) 0 :=
  quasiIsoAt_zero_of_isColimit _
    ((isZero_mooreCochainComplex_X' U F 1 (by omega)).eq_of_tgt _ _)
    (HomologicalComplex.single_obj_d _ _ _ _ _) (HomologicalComplex.single_obj_d _ _ _ _ _) _
    (mooreCochainAugmentation_f_zero' U F) (mooreCochainAug₀IsColimit' U F hcolim)

/-- **The extended Moore complex of `ℱ(U_•)` is a resolution of `colim ℱ`**, given the two
inputs the coefficient category supplies for `ℱ`: the vanishing of the positive homology of
`ℱ(U_•)` and the cokernel presentation of the colimit injection at `U_0`. For a projective `ℱ`
and a point resolution `U_•` both hold, and this is then the columnwise input to the comparison
of the two filtrations of the double complex. -/
lemma quasiIso_mooreCochainAugmentation'
    (hzero : ∀ n : ℕ, IsZero (((cosimplicialMooreComplex' A U).obj F).homology (n + 1)))
    (hcolim : IsColimit (CokernelCofork.ofπ (colimit.ι F (op (U.obj (SimplexCategory.mk 0))))
      (d_one_zero_comp_colimitι' U F))) :
    QuasiIso ((mooreCochainAugmentation' U).app F) :=
  quasiIso_of_single_zero _ (quasiIsoAt_mooreCochainAugmentation_zero' U F hcolim) fun q hq => by
    rcases lt_or_gt_of_ne hq with hq | hq
    · exact isZero_mooreCochainComplex_homology_neg' U F hzero q hq
    · exact isZero_mooreCochainComplex_homology_pos' U F q hq

end Augmentation

/-! ### The double complex of a complex of presheaves -/

section Bicomplex

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **The double complex of a complex of presheaves, as a functor of that complex**:
`Z^{p,q} = (K^p(U_•))^q`, whose column `p` is the extended Moore complex of `K^p(U_•)` and whose
row `q` is `K^•(U_{-q})`. -/
abbrev mooreBicomplexFunctor (A : Type*) [Category* A] [Abelian A] :
    CochainComplex (Cᵒᵖ ⥤ A) ℤ ⥤
      HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (mooreCochainComplex U A).mapHomologicalComplex (ComplexShape.up ℤ)

variable {A : Type*} [Category* A] [Abelian A] (P : CochainComplex (Cᵒᵖ ⥤ A) ℤ)

/-- **The double complex obtained by evaluating a complex of presheaves on the cosimplicial
object `U_•`.** -/
abbrev mooreBicomplex : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (mooreBicomplexFunctor U A).obj P

/-- The double complex vanishes in positive second degrees. -/
lemma isZero_mooreBicomplex_X_X (p q : ℤ) (hq : 0 < q) :
    IsZero (((mooreBicomplex U P).X p).X q) :=
  isZero_mooreCochainComplex_X U (P.X p) q hq

/-- A column of the double complex vanishes where the complex does. -/
lemma isZero_mooreBicomplex_X (p : ℤ) (hp : IsZero (P.X p)) :
    IsZero ((mooreBicomplex U P).X p) :=
  Functor.map_isZero (mooreCochainComplex U A) hp

/-- **The double complex is bounded above in both directions, so it has a total complex.** -/
instance hasTotal_mooreBicomplex [P.IsStrictlyLE 0] :
    (mooreBicomplex U P).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => isZero_mooreBicomplex_X U P p
      (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    (fun p q hq => isZero_mooreBicomplex_X_X U P p q hq)

/-- **Evaluating the extended Moore complex in a fixed cohomological degree is an exact functor
of the presheaf**: it is evaluation at the object `U_{-q}` of the site for `q ≤ 0`, and zero for
`q > 0`. -/
instance preservesHomology_mooreCochainComplex_comp_eval (q : ℤ) :
    (mooreCochainComplex U A ⋙
      HomologicalComplex.eval A (ComplexShape.up ℤ) q).PreservesHomology := by
  rcases le_or_gt q 0 with hq | hq
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q :=
      ⟨(-q).toNat, by simp; omega⟩
    have e : mooreCochainComplex U A ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q ≅
          (evaluation Cᵒᵖ A).obj (op (U.obj (SimplexCategory.mk n))) :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (cosimplicialMooreComplex A U)
          ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctorCompEvalIso A hn)
    have := preservesFiniteLimits_of_natIso e.symm
    have := preservesFiniteColimits_of_natIso e.symm
    infer_instance
  · exact Functor.preservesHomology_of_map_exact _ fun S _ =>
      ShortComplex.exact_of_isZero_X₂ _ (isZero_mooreCochainComplex_X U S.X₂ q hq)

/-! #### The first filtration -/

variable [HasColimitsOfShape Cᵒᵖ A]

/-- **The columnwise augmentation of the double complex**, `Z ⟶ (colim K^•)[0]`: in each column
it is the augmentation `K^p(U_•) ⟶ (colim K^p)[0]` of the extended Moore complex. -/
abbrev mooreBicomplexColumnMap :
    mooreBicomplex U P ⟶
      singleRowZero
        (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex (mooreCochainAugmentation U) (ComplexShape.up ℤ)).app P

/-- The double complex `(colim K^•)[0]` vanishes in positive second degrees. -/
lemma isZero_singleRowZeroColim_X_X (p q : ℤ) (hq : 0 < q) :
    IsZero (((singleRowZero
      (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)).X p).X q) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q (by omega)

/-- A column of `(colim K^•)[0]` vanishes where the complex does. -/
lemma isZero_singleRowZeroColim_X (p : ℤ) (hp : IsZero (P.X p)) :
    IsZero ((singleRowZero
      (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).X p) :=
  Functor.map_isZero (HomologicalComplex.single A (ComplexShape.up ℤ) 0)
    (Functor.map_isZero (colim : (Cᵒᵖ ⥤ A) ⥤ A) hp)

/-- `(colim K^•)[0]` is bounded above in both directions, so it has a total complex. -/
instance hasTotal_singleRowZeroColim [P.IsStrictlyLE 0] :
    (singleRowZero
      (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => isZero_singleRowZeroColim_X P p
      (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    (fun p q hq => isZero_singleRowZeroColim_X_X P p q hq)

/-- **The first filtration of the double complex**: a columnwise quasi-isomorphic augmentation of
a bounded above complex is a quasi-isomorphism on total complexes, so `Tot(Z) ≃ colim K^•`. This
is [Stacks, Tag 0133] for double complexes bounded above, with the hypothesis on the columns; for
a complex of projectives and a point resolution the hypothesis is
`Stacks.ChaoticSite.GeneralValued.quasiIso_mooreCochainAugmentation`. -/
lemma quasiIso_mooreBicomplexColumnTotalMap [P.IsStrictlyLE 0]
    (haug : ∀ p : ℤ, QuasiIso ((mooreCochainAugmentation U).app (P.X p))) :
    QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexColumnMap U P)
      (ComplexShape.up ℤ)) :=
  quasiIso_total_map_of_upperBound (mooreBicomplexColumnMap U P) 0 0
    (fun p hp => isZero_mooreBicomplex_X U P p
      (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    (fun p q hq => isZero_mooreBicomplex_X_X U P p q hq)
    (fun p hp => isZero_singleRowZeroColim_X P p
      (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    (fun p q hq => isZero_singleRowZeroColim_X_X P p q hq)
    haug

end Bicomplex

section Bicomplex

variable {C : Type u} [Category.{vC} C] (U : CosimplicialObject C)

/-- **The double complex of a complex of presheaves, as a functor of that complex**:
`Z^{p,q} = (K^p(U_•))^q`, whose column `p` is the extended Moore complex of `K^p(U_•)` and whose
row `q` is `K^•(U_{-q})`. -/
abbrev mooreBicomplexFunctor' (A : Type*) [Category* A] [Abelian A] :
    CochainComplex (Cᵒᵖ ⥤ A) ℤ ⥤
      HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (mooreCochainComplex' U A).mapHomologicalComplex (ComplexShape.up ℤ)

variable {A : Type*} [Category* A] [Abelian A] (P : CochainComplex (Cᵒᵖ ⥤ A) ℤ)

/-- **The double complex obtained by evaluating a complex of presheaves on the cosimplicial
object `U_•`.** -/
abbrev mooreBicomplex' : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (mooreBicomplexFunctor' U A).obj P

/-- The double complex vanishes in positive second degrees. -/
lemma isZero_mooreBicomplex_X_X' (p q : ℤ) (hq : 0 < q) :
    IsZero (((mooreBicomplex' U P).X p).X q) :=
  isZero_mooreCochainComplex_X' U (P.X p) q hq

/-- A column of the double complex vanishes where the complex does. -/
lemma isZero_mooreBicomplex_X' (p : ℤ) (hp : IsZero (P.X p)) :
    IsZero ((mooreBicomplex' U P).X p) :=
  Functor.map_isZero (mooreCochainComplex' U A) hp

/-- **The double complex is bounded above in both directions, so it has a total complex.** -/
instance hasTotal_mooreBicomplex' [P.IsStrictlyLE 0] :
    (mooreBicomplex' U P).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => isZero_mooreBicomplex_X' U P p
      (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    (fun p q hq => isZero_mooreBicomplex_X_X' U P p q hq)

/-- **Evaluating the extended Moore complex in a fixed cohomological degree is an exact functor
of the presheaf**: it is evaluation at the object `U_{-q}` of the site for `q ≤ 0`, and zero for
`q > 0`. -/
instance preservesHomology_mooreCochainComplex_comp_eval' (q : ℤ) :
    (mooreCochainComplex' U A ⋙
      HomologicalComplex.eval A (ComplexShape.up ℤ) q).PreservesHomology := by
  rcases le_or_gt q 0 with hq | hq
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q :=
      ⟨(-q).toNat, by simp; omega⟩
    have e : mooreCochainComplex' U A ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q ≅
          (evaluation Cᵒᵖ A).obj (op (U.obj (SimplexCategory.mk n))) :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (cosimplicialMooreComplex' A U)
          ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctorCompEvalIso A hn)
    have := preservesFiniteLimits_of_natIso e.symm
    have := preservesFiniteColimits_of_natIso e.symm
    infer_instance
  · exact Functor.preservesHomology_of_map_exact _ fun S _ =>
      ShortComplex.exact_of_isZero_X₂ _ (isZero_mooreCochainComplex_X' U S.X₂ q hq)

/-! #### The first filtration -/

variable [HasColimitsOfShape Cᵒᵖ A]

/-- **The columnwise augmentation of the double complex**, `Z ⟶ (colim K^•)[0]`: in each column
it is the augmentation `K^p(U_•) ⟶ (colim K^p)[0]` of the extended Moore complex. -/
abbrev mooreBicomplexColumnMap' :
    mooreBicomplex' U P ⟶
      singleRowZero
        (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex (mooreCochainAugmentation' U) (ComplexShape.up ℤ)).app P

/-- The double complex `(colim K^•)[0]` vanishes in positive second degrees. -/
lemma isZero_singleRowZeroColim_X_X' (p q : ℤ) (hq : 0 < q) :
    IsZero (((singleRowZero
      (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)).X p).X q) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ q (by omega)

/-- A column of `(colim K^•)[0]` vanishes where the complex does. -/
lemma isZero_singleRowZeroColim_X' (p : ℤ) (hp : IsZero (P.X p)) :
    IsZero ((singleRowZero
      (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).X p) :=
  Functor.map_isZero (HomologicalComplex.single A (ComplexShape.up ℤ) 0)
    (Functor.map_isZero (colim : (Cᵒᵖ ⥤ A) ⥤ A) hp)

/-- `(colim K^•)[0]` is bounded above in both directions, so it has a total complex. -/
instance hasTotal_singleRowZeroColim' [P.IsStrictlyLE 0] :
    (singleRowZero
      (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_upperBound _ 0 0
    (fun p hp => isZero_singleRowZeroColim_X' P p
      (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    (fun p q hq => isZero_singleRowZeroColim_X_X' P p q hq)

/-- **The first filtration of the double complex**: a columnwise quasi-isomorphic augmentation of
a bounded above complex is a quasi-isomorphism on total complexes, so `Tot(Z) ≃ colim K^•`. This
is [Stacks, Tag 0133] for double complexes bounded above, with the hypothesis on the columns; for
a complex of projectives and a point resolution the hypothesis is
`Stacks.ChaoticSite.GeneralValued.quasiIso_mooreCochainAugmentation'`. -/
lemma quasiIso_mooreBicomplexColumnTotalMap' [P.IsStrictlyLE 0]
    (haug : ∀ p : ℤ, QuasiIso ((mooreCochainAugmentation' U).app (P.X p))) :
    QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexColumnMap' U P)
      (ComplexShape.up ℤ)) :=
  quasiIso_total_map_of_upperBound (mooreBicomplexColumnMap' U P) 0 0
    (fun p hp => isZero_mooreBicomplex_X' U P p
      (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    (fun p q hq => isZero_mooreBicomplex_X_X' U P p q hq)
    (fun p hp => isZero_singleRowZeroColim_X' P p
      (CochainComplex.isZero_of_isStrictlyLE P 0 p hp))
    (fun p q hq => isZero_singleRowZeroColim_X_X' P p q hq)
    haug

end Bicomplex

end Stacks.ChaoticSite.GeneralValued

end
