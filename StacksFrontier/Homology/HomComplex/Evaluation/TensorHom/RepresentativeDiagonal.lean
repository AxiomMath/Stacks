module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Generators
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.HomComplex.Composition
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.DerivedTensorHom
public import StacksFrontier.Homology.HomComplex.KoszulBraiding
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.HomComplex.TensorHom
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.LeftDual
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.DerivedTensorFunctorLargeUniverse
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.ProjectiveComparison
import StacksCore.Tactic.EgaSgaAttribute
import all StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.ProjectiveComparison

/-!
# The tensor--Hom diagonal on representatives

The derived-level formulas expressing `DerivedInternalHom.Model.diagonal` on representatives by
the explicit chain map `Stacks.HomComplex.TensorHomComparison.theta`: on K-flat and K-injective
representatives (`DerivedInternalHom.Model.diagonal_comparison`), and on a bounded-above
degreewise-projective internal-Hom source
(`DerivedInternalHom.Model.diagonal_projective_comparison`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u v w w'

set_option maxRecDepth 4096

/-! ### Representative comparisons for the canonical tensor--Hom diagonal

These are the two formulas expressing `DerivedInternalHom.Model.diagonal` on K-flat and
K-injective representatives, respectively on a bounded-above degreewise-projective internal-Hom
source, by the explicit chain map `Stacks.HomComplex.TensorHomComparison.theta`. -/

namespace StacksDraft.DerivedHom

namespace DerivedInternalHom.Model

set_option backward.isDefEq.respectTransparency false

section Complexes

open CochainComplex HomComplex

variable {R : Type u} [CommRing R]

variable [HasDerivedCategory (ModuleCat R)]

/-- For `L` K-flat and `I` K-injective, the derived transpose of the image of
`f : K ⟶ Hom(L, I)` is the image of `uncurry f`, through the tensor comparison. -/
lemma homEquiv_map_uncurry
    (K L I : CochainComplex (ModuleCat R) ℤ) (hL : L.KFlat) [I.IsKInjective]
    (f : K ⟶ HomComplexR R L I) :
    homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)
        (DerivedCategory.Q.map f ≫ ((adjunction R).homIso L I).inv) =
      ((adjunction R).tensorIso K L hL).hom ≫ DerivedCategory.Q.map (uncurry f) := by
  apply (homEquiv _ _ _).symm.injective
  rw [AddEquiv.symm_apply_apply]
  simpa only [Phi_postcomp_uncurry, homEquiv, hom,
    StacksDraft.DerivedHom.DerivedHomData.homIso, StacksDraft.DerivedHom.DerivedHomData.tensorIso]
      using
    ((adjunction R).homEquiv_symm_map_eq K L I hL (uncurry f)).symm

/-- The comparison of the derived internal Hom into a K-injective `I` with the Hom complex is
natural in the source: it intertwines precomposition with `f : K' ⟶ K` on both sides. -/
lemma homIso_precomp {K K' I : CochainComplex (ModuleCat R) ℤ}
    [I.IsKInjective] (f : K' ⟶ K) :
    (hom R).map ((DerivedCategory.Q.map f).op, 𝟙 (DerivedCategory.Q.obj I)) ≫
        ((adjunction R).homIso K' I).hom =
      ((adjunction R).homIso K I).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp R K' K I f) := by
  simpa only [hom, DerivedCategory.Q.map_id, postcomp_id, Category.comp_id] using
    (adjunction R).homIso_naturality f (𝟙 I)

/-- The inverse of the tensor--Hom adjunction bijection is natural in the target. -/
lemma homEquiv_symm_naturality_right
    {A B C D : DerivedCategory (ModuleCat R)} (f : C ⟶ D)
    (g : (tensor R).obj (A, B) ⟶ C) :
    (homEquiv A B D).symm (g ≫ f) =
      (homEquiv A B C).symm g ≫ (hom R).map (𝟙 (Opposite.op B), f) := by
  apply (homEquiv A B D).injective
  rw [AddEquiv.apply_symm_apply, (adjunction R).homEquiv_naturality_right,
    AddEquiv.apply_symm_apply]

/-- The inverse comparison of the Hom complex into a K-injective `I` with the derived internal
Hom intertwines precomposition with `f : K' ⟶ K` on both sides. -/
lemma homIso_precomp_inv {K K' I : CochainComplex (ModuleCat R) ℤ}
    [I.IsKInjective] (f : K' ⟶ K) :
    DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp R K' K I f) ≫
        ((adjunction R).homIso K' I).inv =
      ((adjunction R).homIso K I).inv ≫
        (hom R).map ((DerivedCategory.Q.map f).op, 𝟙 (DerivedCategory.Q.obj I)) := by
  apply (cancel_epi ((adjunction R).homIso K I).hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← homIso_precomp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- For `K` K-flat and `I` K-injective, the inverse of the derived currying isomorphism, computed
through the comparisons with Hom complexes and followed by the chain-level currying isomorphism,
is the comparison of `RHom(B ⊗ K, I)` with the Hom complex `Hom(B ⊗ K, I)`. -/
lemma currying_inv_comparison
    (B K I : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat)
    [I.IsKInjective] [(HomComplexR R K I).IsKInjective] :
    (hom R).map ((((adjunction R).tensorIso B K hK).hom).op,
        𝟙 (DerivedCategory.Q.obj I)) ≫
      (curryingIso (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj I)).inv ≫
      (hom R).map (𝟙 (Opposite.op (DerivedCategory.Q.obj B)),
        ((adjunction R).homIso K I).hom) ≫
      ((adjunction R).homIso B (HomComplexR R K I)).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.Currying.curryIso B K I).hom =
        ((adjunction R).homIso (B ⊗ K) I).hom := by
  rw [← (StacksDraft.DerivedHom.derivedHomCurrying (R := R)).representative_comparison B K I hK]
  simp only [Iso.inv_hom_id_assoc]
  simp only [← Category.assoc, ← Functor.map_comp, prod_comp, ← op_comp,
    Iso.inv_hom_id, Category.comp_id, op_id]
  change (hom R).map (𝟙 _) ≫ _ = _
  exact (congrArg (· ≫ ((adjunction R).homIso (B ⊗ K) I).hom)
    ((hom R).map_id _)).trans (Category.id_comp _)

/-- For `K`, `B` K-flat and `L`, `I` K-injective, composition of derived internal Homs, applied
to the comparison `Hom(L, I) ⟶ RHom(L, I)` and the image of `f : B ⟶ Hom(K, L)`, is computed on
representatives by `(𝟙 ⊗ₘ f) ≫ compMor K L I`. -/
lemma composition_map_comparison_of_kFlat
    (K L I B : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat) (hB : B.KFlat)
    [L.IsKInjective] [I.IsKInjective] (f : B ⟶ HomComplexR R K L) :
    (tensor R).map
        (((adjunction R).homIso L I).inv,
          DerivedCategory.Q.map f ≫ ((adjunction R).homIso K L).inv) ≫
        composition (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj I) =
      ((adjunction R).tensorIso (HomComplexR R L I) B hB).hom ≫
        DerivedCategory.Q.map ((𝟙 (HomComplexR R L I) ⊗ₘ f) ≫ compMor K L I) ≫
        ((adjunction R).homIso K I).inv := by
  let := StacksDraft.DerivedHom.homComplex_isKInjective_of_kFlat K I hK
  rw [composition_map, homEquiv_map_uncurry B K L hK]
  apply (homEquiv _ _ _).symm.injective
  rw [AddEquiv.symm_apply_apply]
  simp only [← Category.assoc]
  rw [homEquiv_symm_naturality_right]
  have hc := (adjunction R).homEquiv_symm_map_eq (HomComplexR R L I) B
    (HomComplexR R K I) hB ((𝟙 (HomComplexR R L I) ⊗ₘ f) ≫ compMor K L I)
  erw [hc]
  rw [← cancel_mono ((hom R).mapIso
    ((Iso.refl (Opposite.op (DerivedCategory.Q.obj B))).prod
      ((adjunction R).homIso K I))).hom]
  rw [← cancel_mono ((adjunction R).homIso B (HomComplexR R K I)).hom]
  rw [← cancel_mono (DerivedCategory.Q.mapIso
    (Stacks.HomComplex.Currying.curryIso B K I)).hom]
  simp only [Category.assoc]
  change _ = DerivedCategory.Q.map
    (Stacks.HomComplex.TensorHomMap.Phi R (HomComplexR R L I) B ≫
      Stacks.HomComplex.TensorHomMap.postcomp R B (HomComplexR R L I ⊗ B) (HomComplexR R K I)
        ((𝟙 (HomComplexR R L I) ⊗ₘ f) ≫ compMor K L I)) ≫
      ((adjunction R).homIso B (HomComplexR R K I)).inv ≫
        ((hom R).mapIso ((Iso.refl (Opposite.op (DerivedCategory.Q.obj B))).prod
          ((adjunction R).homIso K I))).inv ≫
        ((hom R).mapIso ((Iso.refl (Opposite.op (DerivedCategory.Q.obj B))).prod
          ((adjunction R).homIso K I))).hom ≫
        ((adjunction R).homIso B (HomComplexR R K I)).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.Currying.curryIso B K I).hom
  simp only [Iso.inv_hom_id_assoc]
  have hm : (hom R).map
      ((((adjunction R).tensorIso B K hK).hom ≫ DerivedCategory.Q.map (uncurry f)).op,
        𝟙 (DerivedCategory.Q.obj I)) =
      (hom R).map (show (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ⟶
        (Opposite.op (DerivedCategory.Q.obj (B ⊗ K)), DerivedCategory.Q.obj I) from
        ((DerivedCategory.Q.map (uncurry f)).op, 𝟙 (DerivedCategory.Q.obj I))) ≫
      (hom R).map (show
        (Opposite.op (DerivedCategory.Q.obj (B ⊗ K)), DerivedCategory.Q.obj I) ⟶
        (Opposite.op ((tensor R).obj (DerivedCategory.Q.obj B, DerivedCategory.Q.obj K)),
          DerivedCategory.Q.obj I) from
        ((((adjunction R).tensorIso B K hK).hom).op, 𝟙 (DerivedCategory.Q.obj I))) := by
    simp only [← Functor.map_comp, prod_comp, ← op_comp, Category.comp_id]
  rw [hm]
  simp only [Category.assoc]
  simp only [Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  rw [currying_inv_comparison B K I hK, homIso_precomp]
  rw [Iso.inv_hom_id_assoc, ← Functor.map_comp]
  rw [Category.assoc, Phi_postcomp_compMor_currying]


private lemma composition_comparison
    (K L I : CochainComplex (ModuleCat R) ℤ) [L.IsKInjective] [I.IsKInjective]
    (h : (HomComplexR R K L).KFlat) :
    composition (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj I) =
      (tensor R).map (((adjunction R).homIso L I).hom, ((adjunction R).homIso K L).hom) ≫
        ((adjunction R).tensorIso (HomComplexR R L I) (HomComplexR R K L) h).hom ≫
        DerivedCategory.Q.map (compMor K L I) ≫ ((adjunction R).homIso K I).inv := by
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution K
  let : QuasiIso f := hf
  let e := (tensor R).mapIso (((adjunction R).homIso L I).prod
    ((adjunction R).homIso K L))
  apply (cancel_epi e.inv).1
  change e.inv ≫ _ = e.inv ≫ e.hom ≫ _
  rw [Iso.inv_hom_id_assoc]
  let e' := (hom R).mapIso ((asIso (DerivedCategory.Q.map f)).op.prod
    (Iso.refl (DerivedCategory.Q.obj I)))
  apply (cancel_mono e'.hom).1
  have hc := composition_map_comparison_of_kFlat P L I (HomComplexR R K L) hP h
    (Stacks.HomComplex.TensorHomMap.precomp R P K L f)
  rw [homIso_precomp_inv, compMor_precomp] at hc
  simp only [Functor.map_comp, Category.assoc] at hc
  rw [homIso_precomp_inv] at hc
  simp only [Category.assoc, e', Functor.mapIso_hom, Iso.prod_hom, Iso.op_hom,
    asIso_hom, Iso.refl_hom]
  rw [← composition_naturality_source (DerivedCategory.Q.map f)]
  simpa only [e, e', Functor.mapIso_inv, Functor.mapIso_hom, Iso.prod_inv, Iso.prod_hom,
    Iso.op_hom, asIso_hom, Iso.refl_hom, ← Category.assoc,
    (adjunction R).tensor_map_comp, Category.comp_id] using hc

private lemma coevaluation_comparison (K L : CochainComplex (ModuleCat R) ℤ)
    (hL : L.KFlat) [(K ⊗ L).IsKInjective] :
    coevaluation (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        (hom R).map (𝟙 (Opposite.op (DerivedCategory.Q.obj L)),
          ((adjunction R).tensorIso K L hL).hom) =
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.Phi R K L) ≫
        ((adjunction R).homIso L (K ⊗ L)).inv := by
  rw [coevaluation, ← homEquiv_symm_naturality_right, Category.id_comp]
  have hc := (adjunction R).homEquiv_symm_map_eq K L (K ⊗ L) hL (𝟙 (K ⊗ L))
  erw [DerivedCategory.Q.map_id, Category.comp_id, postcomp_id, Category.comp_id] at hc
  exact hc

private lemma diagonal_comparison
    (K L M : CochainComplex (ModuleCat R) ℤ) [L.IsKInjective]
    [(K ⊗ L).IsKInjective] (hL : L.KFlat) (h : (HomComplexR R M L).KFlat) :
    diagonal (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj M) =
      (tensor R).map (𝟙 (DerivedCategory.Q.obj K), ((adjunction R).homIso M L).hom) ≫
        ((adjunction R).tensorIso K (HomComplexR R M L) h).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.theta K L M) ≫
        ((adjunction R).homIso M (K ⊗ L)).inv ≫
        (hom R).map (𝟙 (Opposite.op (DerivedCategory.Q.obj M)),
          ((adjunction R).tensorIso K L hL).inv) := by
  let e := (hom R).mapIso ((Iso.refl (Opposite.op (DerivedCategory.Q.obj M))).prod
    ((adjunction R).tensorIso K L hL))
  apply (cancel_mono e.hom).1
  simp only [Category.assoc]
  change diagonal _ _ _ ≫ e.hom = _ ≫ _ ≫ _ ≫ _ ≫ e.inv ≫ e.hom
  simp only [Iso.inv_hom_id, Category.comp_id]
  change diagonal (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj M) ≫
    (hom R).map (show
      (Opposite.op (DerivedCategory.Q.obj M),
        (tensor R).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ⟶
      (Opposite.op (DerivedCategory.Q.obj M), DerivedCategory.Q.obj (K ⊗ L)) from
      (𝟙 (Opposite.op (DerivedCategory.Q.obj M)),
        ((adjunction R).tensorIso K L hL).hom)) = _
  rw [diagonal, Category.assoc, ← composition_naturality_target]
  simp only [← Category.assoc, (adjunction R).tensor_map_comp, Category.comp_id]
  rw [coevaluation_comparison K L hL, composition_comparison M L (K ⊗ L) h]
  simp only [← Category.assoc, (adjunction R).tensor_map_comp, Category.id_comp]
  rw [Category.assoc (DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.Phi R K L)),
    Iso.inv_hom_id, Category.comp_id]
  have hn := (adjunction R).tensorIso_naturality (Stacks.HomComplex.TensorHomMap.Phi R K L)
    (𝟙 (HomComplexR R M L)) h h
  simp only [DerivedCategory.Q.map_id] at hn
  have hn' := congrArg ((tensor R).map (show
    (DerivedCategory.Q.obj K, (hom R).obj
      (Opposite.op (DerivedCategory.Q.obj M), DerivedCategory.Q.obj L)) ⟶
    (DerivedCategory.Q.obj K, DerivedCategory.Q.obj (HomComplexR R M L)) from
    (𝟙 (DerivedCategory.Q.obj K), ((adjunction R).homIso M L).hom)) ≫ ·) hn
  simp only [← Category.assoc, (adjunction R).tensor_map_comp,
    Category.id_comp, Category.comp_id] at hn'
  rw [hn']
  simp only [Category.assoc, ← Functor.map_comp, Phi_tensor_compMor]

/-- The specified comparison when the left tensor factor is K-flat. -/
def tensorLeftIso (K L : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat) :
    (tensor R).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (K ⊗ L) :=
  (adjunction R).tensorSwap _ _ ≪≫ (adjunction R).tensorIso L K hK ≪≫
    DerivedCategory.Q.mapIso (StacksDraft.DerivedHom.Model.complexSwap R L K)

/-- The comparison `tensorLeftIso` is natural in both factors. -/
lemma tensorLeftIso_naturality
    {K K' L L' : CochainComplex (ModuleCat R) ℤ} (f : K ⟶ K') (g : L ⟶ L')
    (hK : K.KFlat) (hK' : K'.KFlat) :
    (tensor R).map (DerivedCategory.Q.map f, DerivedCategory.Q.map g) ≫
        (tensorLeftIso K' L' hK').hom =
      (tensorLeftIso K L hK).hom ≫ DerivedCategory.Q.map (f ⊗ₘ g) := by
  let := CochainComplex.Koszul.koszulSymmetric R
  simp only [tensorLeftIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, (adjunction R).tensorSwap_naturality]
  rw [Category.assoc, ← Category.assoc ((tensor R).map _),
    (adjunction R).tensorIso_naturality g f hK hK']
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2
  exact congrArg DerivedCategory.Q.map (BraidedCategory.braiding_naturality g f)

/-- When both factors are K-flat, `tensorLeftIso` agrees with the comparison for a K-flat right
factor. -/
lemma tensorLeftIso_eq (K L : CochainComplex (ModuleCat R) ℤ)
    (hK : K.KFlat) (hL : L.KFlat) :
    tensorLeftIso K L hK = (adjunction R).tensorIso K L hL := by
  let := CochainComplex.Koszul.koszulSymmetric R
  apply Iso.ext
  simp only [tensorLeftIso, Iso.trans_hom, Functor.mapIso_hom]
  have hb := (adjunction R).tensorSwap_comparison K L hK hL
  change _ ≫ ((adjunction R).tensorIso L K hK).hom = _ at hb
  rw [← Category.assoc, hb,
    Category.assoc, ← Functor.map_comp]
  change _ ≫ DerivedCategory.Q.map ((β_ K L).hom ≫ (β_ L K).hom) = _
  simp
  rfl

/-- `tensorLeftIso` is natural in the right factor, with the left factor fixed. -/
private lemma tensorLeftIso_naturality_right
    {K L L' : CochainComplex (ModuleCat R) ℤ} (g : L ⟶ L') (hK : K.KFlat) :
    (tensor R).map (𝟙 (DerivedCategory.Q.obj K), DerivedCategory.Q.map g) ≫
        (tensorLeftIso K L' hK).hom =
      (tensorLeftIso K L hK).hom ≫ DerivedCategory.Q.map (𝟙 K ⊗ₘ g) := by
  simpa only [DerivedCategory.Q.map_id] using tensorLeftIso_naturality (𝟙 K) g hK hK

omit [HasDerivedCategory (ModuleCat R)] in
/-- Postcomposition on Hom complexes is functorial. -/
lemma postcomp_comp (A B C D : CochainComplex (ModuleCat R) ℤ)
    (f : B ⟶ C) (g : C ⟶ D) :
    Stacks.HomComplex.TensorHomMap.postcomp R A B C f ≫ Stacks.HomComplex.TensorHomMap.postcomp R A
      C D g =
      Stacks.HomComplex.TensorHomMap.postcomp R A B D (f ≫ g) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  change (((Stacks.HomComplex.TensorHomMap.postcomp R A C D g).f n).hom
    (((Stacks.HomComplex.TensorHomMap.postcomp R A B C f).f n).hom z)).v p q hpq = _
  simp only [postcomp_apply, HomologicalComplex.comp_f, Category.assoc]

omit [HasDerivedCategory (ModuleCat R)] in
/-- Precomposition and postcomposition on Hom complexes commute. -/
lemma precomp_postcomp (A B C D : CochainComplex (ModuleCat R) ℤ)
    (f : A ⟶ B) (g : C ⟶ D) :
    Stacks.HomComplex.TensorHomMap.precomp R A B C f ≫ Stacks.HomComplex.TensorHomMap.postcomp R A C
      D g =
      Stacks.HomComplex.TensorHomMap.postcomp R B C D g ≫ Stacks.HomComplex.TensorHomMap.precomp R A
        B D f := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  change (((Stacks.HomComplex.TensorHomMap.postcomp R A C D g).f n).hom
    (((Stacks.HomComplex.TensorHomMap.precomp R A B C f).f n).hom z)).v p q hpq =
    (((Stacks.HomComplex.TensorHomMap.precomp R A B D f).f n).hom
    (((Stacks.HomComplex.TensorHomMap.postcomp R B C D g).f n).hom z)).v p q hpq
  simp only [postcomp_apply, precomp_apply, Category.assoc]

/-- For `K` K-flat and `I` K-injective, the derived transpose of the image of `f : K ⊗ L ⟶ I`
is the image of the unit `K ⟶ Hom(L, K ⊗ L)` followed by postcomposition with `f`. -/
lemma homEquiv_symm_map_leftFlat
    (K L I : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat) [I.IsKInjective]
    (f : K ⊗ L ⟶ I) :
    (homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj I)).symm
        ((tensorLeftIso K L hK).hom ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.Phi R K L ≫
        Stacks.HomComplex.TensorHomMap.postcomp R L (K ⊗ L) I f) ≫ ((adjunction R).homIso L I).inv
          := by
  obtain ⟨P, p, hP, _, hp, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution L
  let : QuasiIso p := hp
  let e := (hom R).mapIso ((asIso (DerivedCategory.Q.map p)).op.prod
    (Iso.refl (DerivedCategory.Q.obj I)))
  apply (cancel_mono e.hom).1
  simp only [e, Functor.mapIso_hom, Iso.prod_hom, Iso.op_hom, asIso_hom, Iso.refl_hom]
  have hn (a : (tensor R).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj I) :
      (homEquiv _ _ _).symm a ≫ (hom R).map (show
        (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ⟶
          (Opposite.op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) from
        ((DerivedCategory.Q.map p).op, 𝟙 (DerivedCategory.Q.obj I))) =
        (homEquiv _ _ _).symm
          ((tensor R).map (𝟙 (DerivedCategory.Q.obj K), DerivedCategory.Q.map p) ≫ a) := by
    apply (homEquiv _ _ _).injective
    rw [(adjunction R).homEquiv_dinaturality, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply]
  rw [hn, ← Category.assoc]
  rw [tensorLeftIso_naturality_right p hK, Category.assoc, ← Functor.map_comp,
    tensorLeftIso_eq K P hK hP]
  erw [(adjunction R).homEquiv_symm_map_eq K P I hP ((𝟙 K ⊗ₘ p) ≫ f)]
  rw [Category.assoc, ← homIso_precomp_inv, ← Category.assoc, ← Functor.map_comp]
  congr 2
  rw [← postcomp_comp, ← Category.assoc]
  simp only [id_tensorHom]
  rw [Stacks.HomComplex.TensorHomMap.Phi_dinatural_L, Category.assoc, precomp_postcomp]
  simp only [Category.assoc]

omit [HasDerivedCategory (ModuleCat R)] in
/-- The composition map of Hom complexes is natural in the target. -/
lemma compMor_postcomp (M L J J' : CochainComplex (ModuleCat R) ℤ)
    (g : J ⟶ J') :
    (Stacks.HomComplex.TensorHomMap.postcomp R L J J' g ⊗ₘ 𝟙 (HomComplexR R M L)) ≫ compMor M L J' =
      compMor M L J ≫ Stacks.HomComplex.TensorHomMap.postcomp R M J J' g := by
  ext n : 1
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  change (compMor M L J').f n
    ((Stacks.HomComplex.TensorHomMap.postcomp R L J J' g ⊗ₘ 𝟙 (HomComplexR R M L)).f n
      ((HomologicalComplex.ιTensorObj (HomComplexR R L J) (HomComplexR R M L)
        p q n hpq).hom (a ⊗ₜ[R] b))) =
    (Stacks.HomComplex.TensorHomMap.postcomp R M J J' g).f n
      ((compMor M L J).f n
        ((HomologicalComplex.ιTensorObj (HomComplexR R L J) (HomComplexR R M L)
          p q n hpq).hom (a ⊗ₜ[R] b)))
  rw [tensorHom_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  erw [compMor_apply, compMor_apply]
  apply Cochain.ext
  intro r s hrs
  rw [postcomp_apply, Cochain.comp_v _ _ _ r (r + q) s rfl (by omega),
    postcomp_apply, Cochain.comp_v _ _ _ r (r + q) s rfl (by omega)]
  simp only [Category.assoc]

/-- For `K`, `B` K-flat and `L`, `J` K-injective, composition of derived internal Homs, applied
to the images of `a : A ⟶ Hom(L, J)` and `b : B ⟶ Hom(K, L)`, is computed on representatives by
`(a ⊗ₘ b) ≫ compMor K L J`. -/
lemma composition_pair_comparison
    (K L J A B : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat) (hB : B.KFlat)
    [L.IsKInjective] [J.IsKInjective]
    (a : A ⟶ HomComplexR R L J) (b : B ⟶ HomComplexR R K L) :
    (tensor R).map
        (DerivedCategory.Q.map a ≫ ((adjunction R).homIso L J).inv,
          DerivedCategory.Q.map b ≫ ((adjunction R).homIso K L).inv) ≫
      composition (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj J) =
    ((adjunction R).tensorIso A B hB).hom ≫
      DerivedCategory.Q.map ((a ⊗ₘ b) ≫ compMor K L J) ≫
        ((adjunction R).homIso K J).inv := by
  have hc := congrArg ((tensor R).map (show
    (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ⟶
    (DerivedCategory.Q.obj (HomComplexR R L J), DerivedCategory.Q.obj B) from
      (DerivedCategory.Q.map a, 𝟙 _)) ≫ ·)
    (composition_map_comparison_of_kFlat K L J B hK hB b)
  simp only [← Category.assoc, (adjunction R).tensor_map_comp, Category.id_comp] at hc
  rw [Category.assoc, Category.assoc] at hc
  have ht := (adjunction R).tensorIso_naturality a (𝟙 B) hB hB
  simp only [DerivedCategory.Q.map_id] at ht
  rw [← Category.assoc ((tensor R).map _), ht] at hc
  have hab : (a ⊗ₘ b) ≫ compMor K L J =
      (a ⊗ₘ 𝟙 B) ≫ ((𝟙 (HomComplexR R L J) ⊗ₘ b) ≫ compMor K L J) := by
    simp only [← Category.assoc, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp]
  rw [hab, Functor.map_comp]
  simpa only [Category.assoc] using hc

/-- Transport the diagonal to a specified K-injective target, including the actual map
from the tensor model to that target. -/
lemma diagonal_injective_model
    (K I M J : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat) (hM : M.KFlat)
    [I.IsKInjective] [J.IsKInjective] (q : K ⊗ I ⟶ J) :
    diagonal (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I)
        (DerivedCategory.Q.obj M) ≫
      (hom R).map (𝟙 (Opposite.op (DerivedCategory.Q.obj M)),
        (tensorLeftIso K I hK).hom ≫ DerivedCategory.Q.map q) =
    (tensor R).map (𝟙 (DerivedCategory.Q.obj K), ((adjunction R).homIso M I).hom) ≫
      (tensorLeftIso K (HomComplexR R M I) hK).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.theta K I M ≫
        Stacks.HomComplex.TensorHomMap.postcomp R M (K ⊗ I) J q) ≫ ((adjunction R).homIso M J).inv
          := by
  obtain ⟨B, b, hB, _, hb, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution (HomComplexR R M I)
  let : QuasiIso b := hb
  let e := (tensor R).mapIso ((Iso.refl (DerivedCategory.Q.obj K)).prod
    (asIso (DerivedCategory.Q.map b) ≪≫ ((adjunction R).homIso M I).symm))
  apply (cancel_epi e.hom).1
  simp only [e, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.trans_hom,
    asIso_hom, Iso.symm_hom]
  simp only [diagonal, Category.assoc, Prod.mkHom]
  rw [← composition_naturality_target]
  simp only [← Category.assoc, (adjunction R).tensor_map_comp,
    Category.id_comp, Category.comp_id]
  have hc : coevaluation (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I) ≫
      (hom R).map (𝟙 (Opposite.op (DerivedCategory.Q.obj I)),
        (tensorLeftIso K I hK).hom ≫ DerivedCategory.Q.map q) =
    DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.Phi R K I ≫
      Stacks.HomComplex.TensorHomMap.postcomp R I (K ⊗ I) J q) ≫
      ((adjunction R).homIso I J).inv := by
    rw [coevaluation, ← homEquiv_symm_naturality_right, Category.id_comp]
    exact homEquiv_symm_map_leftFlat K I J hK q
  rw [hc, composition_pair_comparison M I J K B hM hB]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc ((tensor R).map _), tensorLeftIso_naturality_right b hK,
    tensorLeftIso_eq K B hK hB]
  have he : ((Stacks.HomComplex.TensorHomMap.Phi R K I ≫ Stacks.HomComplex.TensorHomMap.postcomp R I
    (K ⊗ I) J q) ⊗ₘ b) ≫
      compMor M I J = (𝟙 K ⊗ₘ b) ≫
        (Stacks.HomComplex.TensorHomComparison.theta K I M ≫ Stacks.HomComplex.TensorHomMap.postcomp
          R M (K ⊗ I) J q) := by
    rw [← Phi_tensor_compMor]
    simp only [Category.assoc]
    rw [← compMor_postcomp]
    simp only [← Category.assoc, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  rw [he, Functor.map_comp]
  simp only [Category.assoc]

omit [HasDerivedCategory (ModuleCat R)] in
private lemma homCxMap_id_left (M L L' : CochainComplex (ModuleCat R) ℤ)
    (g : L ⟶ L') :
    Stacks.HomComplex.TensorHomComparison.HomCxMap M M L L' (𝟙 M) g =
      Stacks.HomComplex.TensorHomMap.postcomp R M L L' g := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  change (Stacks.HomComplex.TensorHomComparison.HomCxMapDeg M M L L' (𝟙 M) g n z).v p q hpq = _
  rw [Stacks.HomComplex.TensorHomComparison.HomCxMapDeg_v, postcomp_apply]
  simp only [HomologicalComplex.id_f, Category.id_comp]

private lemma hom_map_target_comp {A B C M : DerivedCategory (ModuleCat R)}
    (f : A ⟶ B) (g : B ⟶ C) :
    (hom R).map (show (Opposite.op M, A) ⟶ (Opposite.op M, B) from
      (𝟙 (Opposite.op M), f)) ≫
    (hom R).map (show (Opposite.op M, B) ⟶ (Opposite.op M, C) from
      (𝟙 (Opposite.op M), g)) =
    (hom R).map (show (Opposite.op M, A) ⟶ (Opposite.op M, C) from
      (𝟙 (Opposite.op M), f ≫ g)) := by
  simp only [← Functor.map_comp, prod_comp, Category.comp_id]

private lemma diagonal_projective_injective
    (K I M : CochainComplex (ModuleCat R) ℤ) (d : ℤ) (hK : K.KFlat) (hM : M.KFlat)
    [M.IsStrictlyLE d] [∀ i, Projective (M.X i)] [I.IsKInjective] :
    diagonal (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I)
        (DerivedCategory.Q.obj M) ≫
      (hom R).map (𝟙 (Opposite.op (DerivedCategory.Q.obj M)),
        (tensorLeftIso K I hK).hom) ≫
      ((Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)).iso M
        (K ⊗ I) d).hom =
    (tensor R).map (𝟙 (DerivedCategory.Q.obj K),
      ((Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)).iso M
        I d).hom) ≫
      (tensorLeftIso K (HomComplexR R M I) hK).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.theta K I M) := by
  obtain ⟨J, q, hq, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective (K ⊗ I)
  let : QuasiIso q := hq
  let : J.IsKInjective := hJ
  let E := Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)
  have := E.quasiIso_homCxMap M (K ⊗ I) J d q
  apply (cancel_mono (DerivedCategory.Q.map
    (Stacks.HomComplex.TensorHomComparison.HomCxMap M M (K ⊗ I) J (𝟙 M) q))).1
  simp only [Category.assoc]
  rw [E.resolution_comparison M (K ⊗ I) J d q]
  have hc := congrArg (· ≫ ((adjunction R).homIso M J).hom)
    (diagonal_injective_model K I M J hK hM q)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hc
  rw [E.iso_eq_homIso M I d, homCxMap_id_left]
  rw [← Category.assoc ((hom R).map _), hom_map_target_comp]
  simpa only [Functor.map_comp, Category.assoc] using hc


private lemma projective_naturality (M L L' : CochainComplex (ModuleCat R) ℤ)
    (d : ℤ) [M.IsStrictlyLE d] [∀ i, Projective (M.X i)] (f : L ⟶ L') :
    (hom R).map (𝟙 (Opposite.op (DerivedCategory.Q.obj M)), DerivedCategory.Q.map f) ≫
      ((Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)).iso M
        L' d).hom =
    ((Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)).iso M L
      d).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap M M L L' (𝟙 M) f) := by
  simpa only [DerivedCategory.Q.map_id, op_id] using
    (Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R :=
      R)).naturality M M L L' d d (𝟙 M) f

private lemma diagonal_projective_normalized
    (K L M : CochainComplex (ModuleCat R) ℤ) (d : ℤ) (hK : K.KFlat) (hM : M.KFlat)
    [M.IsStrictlyLE d] [∀ i, Projective (M.X i)] :
    diagonal (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj M) ≫
      (hom R).map (𝟙 (Opposite.op (DerivedCategory.Q.obj M)),
        (tensorLeftIso K L hK).hom) ≫
      ((Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)).iso M
        (K ⊗ L) d).hom =
    (tensor R).map (𝟙 (DerivedCategory.Q.obj K),
      ((Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)).iso M
        L d).hom) ≫
      (tensorLeftIso K (HomComplexR R M L) hK).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.theta K L M) := by
  obtain ⟨I, i, hi, hI⟩ := CochainComplex.exists_quasiIso_isKInjective L
  let : QuasiIso i := hi
  let : I.IsKInjective := hI
  let E := Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)
  have ht := tensorLeftIso_naturality_right i hK
  simp only [id_tensorHom] at ht
  have : IsIso (DerivedCategory.Q.map (K ◁ i)) := by
    have he : DerivedCategory.Q.map (K ◁ i) = (tensorLeftIso K L hK).inv ≫
        ((tensor R).mapIso ((Iso.refl (DerivedCategory.Q.obj K)).prod
          (asIso (DerivedCategory.Q.map i)))).hom ≫ (tensorLeftIso K I hK).hom := by
      simp only [Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, asIso_hom]
      rw [ht]
      simp
    rw [he]
    infer_instance
  have : QuasiIso (K ◁ i) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp inferInstance
  have := E.quasiIso_homCxMap M (K ⊗ L) (K ⊗ I) d (K ◁ i)
  apply (cancel_mono (DerivedCategory.Q.map
    (Stacks.HomComplex.TensorHomComparison.HomCxMap M M (K ⊗ L) (K ⊗ I) (𝟙 M) (K ◁ i)))).1
  simp only [Category.assoc]
  rw [← projective_naturality M (K ⊗ L) (K ⊗ I) d (K ◁ i)]
  rw [← Category.assoc ((hom R).map _), hom_map_target_comp, ← ht,
    ← hom_map_target_comp]
  rw [← Category.assoc, ← Category.assoc, ← diagonal_naturality_target]
  rw [Category.assoc, Category.assoc,
    diagonal_projective_injective K I M d hK hM]
  have hn := projective_naturality M L I d i
  simp only [← Category.assoc, (adjunction R).tensor_map_comp, Category.comp_id]
  rw [hn]
  have ht' := tensorLeftIso_naturality_right
    (Stacks.HomComplex.TensorHomComparison.HomCxMap M M L I (𝟙 M) i) hK
  have hs := (adjunction R).tensor_map_comp (𝟙 (DerivedCategory.Q.obj K))
    (E.iso M L d).hom (𝟙 (DerivedCategory.Q.obj K))
    (DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.HomCxMap M M L I (𝟙 M) i))
  simp only [Category.comp_id] at hs
  rw [← hs]
  simp only [Category.assoc]
  have ht'' := congrArg (· ≫ DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.theta K I
    M)) ht'
  simp only [Category.assoc] at ht''
  rw [ht'']
  apply congrArg ((tensor R).map (show
    (DerivedCategory.Q.obj K, (hom R).obj
      (Opposite.op (DerivedCategory.Q.obj M), DerivedCategory.Q.obj L)) ⟶
    (DerivedCategory.Q.obj K, DerivedCategory.Q.obj (HomComplexR R M L)) from
      (𝟙 (DerivedCategory.Q.obj K), (E.iso M L d).hom)) ≫ ·)
  apply congrArg ((tensorLeftIso K (HomComplexR R M L) hK).hom ≫ ·)
  simpa only [Functor.map_comp, id_tensorHom] using
    congrArg DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.theta_natural_L K L I M
      i).symm


/-- For a K-flat left tensor factor and a bounded-above degreewise-projective internal-Hom
source, the canonical diagonal is represented by the fixed chain map
  `Stacks.HomComplex.TensorHomComparison.theta`. No
condition is imposed on the target complex, and invertibility of `theta` is not assumed. -/
private lemma diagonal_projective_comparison
    (K L M : CochainComplex (ModuleCat R) ℤ) (d : ℤ) (hK : K.KFlat)
    [M.IsStrictlyLE d] [∀ i, Projective (M.X i)] :
    diagonal (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj M) =
      (tensor R).map
          (𝟙 (DerivedCategory.Q.obj K),
            ((Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R :=
              R)).iso M L d).hom) ≫
        ((adjunction R).tensorSwap (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj (CochainComplex.HomComplexR R M L)) ≪≫
          (adjunction R).tensorIso (CochainComplex.HomComplexR R M L) K hK ≪≫
          DerivedCategory.Q.mapIso (StacksDraft.DerivedHom.Model.complexSwap R
            (CochainComplex.HomComplexR R M L) K)).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.theta K L M) ≫
        ((Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)).iso
          M (K ⊗ L) d).inv ≫
        (hom R).map
          (𝟙 (Opposite.op (DerivedCategory.Q.obj M)),
            ((adjunction R).tensorSwap (DerivedCategory.Q.obj K)
                (DerivedCategory.Q.obj L) ≪≫
              (adjunction R).tensorIso L K hK ≪≫
              DerivedCategory.Q.mapIso
                (StacksDraft.DerivedHom.Model.complexSwap R L K)).inv) := by
  have hM : M.KFlat := CochainComplex.KFlat.kFlat_of_flat M d
  let E := Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)
  let e := (hom R).mapIso ((Iso.refl (Opposite.op (DerivedCategory.Q.obj M))).prod
    (tensorLeftIso K L hK))
  apply (cancel_mono e.hom).1
  simp only [Category.assoc]
  change diagonal _ _ _ ≫ e.hom =
    (tensor R).map (𝟙 (DerivedCategory.Q.obj K), (E.iso M L d).hom) ≫
      (tensorLeftIso K (CochainComplex.HomComplexR R M L) hK).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomComparison.theta K L M) ≫
      (E.iso M (K ⊗ L) d).inv ≫ e.inv ≫ e.hom
  simp only [Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono (E.iso M (K ⊗ L) d).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact diagonal_projective_normalized K L M d hK hM

end Complexes

end DerivedInternalHom.Model

end StacksDraft.DerivedHom

end
