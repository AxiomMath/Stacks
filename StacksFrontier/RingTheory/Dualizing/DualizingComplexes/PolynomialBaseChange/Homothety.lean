module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Criteria
public import StacksFrontier.Algebra.Module.InjectiveHull.Injective
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TorAmplitude.ExtendScalars
public import StacksFrontier.RingTheory.Dualizing.Complex
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange.FiniteInjectiveDimension

/-!
# Homothety maps and change of coefficients

Auxiliary results for `Dualizing.polynomialBaseChange_isDualizingComplex`: the homothety map of a
bounded below complex of injectives, its comparison with the canonical map `R → End K` in the
derived category, and the transport of these along restriction of scalars and universe lifting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace Dualizing

universe u v w x

private noncomputable def moduleHomothety {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ) :
    (CochainComplex.singleFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R) ⟶
      CochainComplex.HomComplexR R I I :=
  HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom
      { toFun := fun a ↦ a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)
        map_add' := by intros; simp [add_smul]
        map_smul' := by intros; simp [smul_smul] })
    (fun k hk ↦ by
      obtain rfl : (1 : ℤ) = k := by simpa using hk
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change CochainComplex.HomComplex.δ 0 1
        (a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) = 0
      simp)

private theorem moduleHomothety_f_zero_apply {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ) (a : R) :
    ((moduleHomothety I).f 0).hom a =
      a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I) := by
  rfl

private theorem moduleHomothety_f_zero_apply_source {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ)
    (a : ((CochainComplex.singleFunctor (ModuleCat.{w} R) 0).obj
      (ModuleCat.of R R)).X 0) :
    ((moduleHomothety I).f 0).hom a =
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).hom.hom a) •
        CochainComplex.HomComplex.Cochain.ofHom (𝟙 I) := by
  rfl

private noncomputable def additiveHomothety {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ) :
    (CochainComplex.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of R) ⟶
      CochainComplex.HomComplex I I :=
  HomologicalComplex.mkHomFromSingle
    (AddCommGrpCat.ofHom
      { toFun := fun a ↦ a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)
        map_zero' := by ext; simp
        map_add' := by intros; ext; simp [add_smul] })
    (fun k hk ↦ by
      obtain rfl : (1 : ℤ) = k := by simpa using hk
      ext a
      change CochainComplex.HomComplex.δ 0 1
        (a • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) = 0
      simp)

private theorem additiveHomothety_f_zero_apply_source {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ)
    (a : ((CochainComplex.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of R)).X 0) :
    ((additiveHomothety I).f 0).hom a =
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (AddCommGrpCat.of R)).hom.hom a) •
        CochainComplex.HomComplex.Cochain.ofHom (𝟙 I) := by
  rfl

/-- A morphism of complexes is a quasi-isomorphism iff its image under a homology-reflecting
functor is, after composing with an isomorphism on the source. -/
private theorem quasiIso_iff_of_inv_comp_map_eq {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    [F.ReflectsIsomorphisms] {K L : CochainComplex C ℤ} {M : CochainComplex D ℤ} (f : K ⟶ L)
    (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅ M)
    (g : M ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    (h : e.inv ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map f = g) :
    QuasiIso g ↔ QuasiIso f := by
  have : QuasiIso e.inv := inferInstance
  rw [← h, quasiIso_iff_comp_left e.inv, HomologicalComplex.quasiIso_map_iff_of_preservesHomology]

private theorem additiveHomothety_quasiIso_iff {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ) :
    QuasiIso (additiveHomothety I) ↔ QuasiIso (homothety I) := by
  symm
  refine quasiIso_iff_of_inv_comp_map_eq AddCommGrpCat.uliftFunctor.{w, w}
    (additiveHomothety I)
    ((CategoryTheory.Functor.mapCochainComplexSingleFunctor _ 0).app (AddCommGrpCat.of R))
    (homothety I) ?_
  apply HomologicalComplex.from_single_hom_ext
  ext a
  change ULift.up (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) =
    ULift.up (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I))
  rfl

private theorem moduleHomothety_quasiIso_iff {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ) :
    QuasiIso (moduleHomothety I) ↔ QuasiIso (additiveHomothety I) := by
  symm
  refine quasiIso_iff_of_inv_comp_map_eq (CategoryTheory.forget₂ (ModuleCat.{w} R) AddCommGrpCat)
    (moduleHomothety I)
    ((CategoryTheory.Functor.mapCochainComplexSingleFunctor _ 0).app (ModuleCat.of R R))
    (additiveHomothety I) ?_
  apply HomologicalComplex.from_single_hom_ext
  ext a
  rfl

private noncomputable def derivedHomothetyAt {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ) [I.IsKInjective] :
    DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)) ⟶
      (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom R).obj
        (Opposite.op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj I) :=
  DerivedCategory.Q.map (moduleHomothety I) ≫
    (Stacks.DerivedHom.ScalarTransportedInternalHom.Model.homComplexIso I I).inv

private theorem isIso_derivedHomothetyAt_iff {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ) [I.IsKInjective] :
    IsIso (derivedHomothetyAt I) ↔ QuasiIso (homothety I) := by
  rw [derivedHomothetyAt, isIso_comp_right_iff]
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ (moduleHomothety I)).trans
    ((moduleHomothety_quasiIso_iff I).trans (additiveHomothety_quasiIso_iff I))

private theorem unitTensor_apply {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ) (n : ℤ)
    (a : (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)).X 0) (x : I.X n) :
    ((λ_ I).hom.f n).hom ((ιTensorObj _ I 0 n n (zero_add n)).hom (a ⊗ₜ[R] x)) =
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{w} R))).hom.hom a) • x := by
  have h : (λ_ I).inv.f n = (λ_ (I.X n)).inv ≫
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{w} R))).inv ▷ I.X n) ≫
        ιTensorObj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) I 0 n n (zero_add n) :=
    leftUnitor'_inv I n
  have hh : ιTensorObj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) I 0 n n
        (zero_add n) ≫ (λ_ I).hom.f n =
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{w} R))).hom ▷ I.X n) ≫
        (λ_ (I.X n)).hom := by
    apply (cancel_epi ((λ_ (I.X n)).inv ≫
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{w} R))).inv ▷ I.X n))).mp
    simp only [Category.assoc]
    rw [← reassoc_of% h]
    simp
  exact ConcreteCategory.congr_hom hh (a ⊗ₜ[R] x)

private theorem moduleHomothety_eq_Phi {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ) :
    moduleHomothety I =
      Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) I ≫
        Stacks.HomComplex.TensorHomMap.postcomp R I
          ((𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) ⊗ I) I (λ_ I).hom := by
  apply HomologicalComplex.from_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply CochainComplex.HomComplex.Cochain.ext₀
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [moduleHomothety_f_zero_apply_source]
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply,
    Stacks.HomComplex.TensorHomMap.Phi_f_apply, Stacks.HomComplex.TensorHomMap.postcomp_f_apply]
  rw [CochainComplex.HomComplex.Cochain.smul_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  rw [CochainComplex.HomComplex.Cochain.comp_v _ _ (add_zero 0)
      p p p (by omega) (by omega),
    CochainComplex.HomComplex.Cochain.ofHom_v,
    Stacks.HomComplex.TensorHomMap.Phiv_v]
  change ((singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).hom.hom a) • x =
    ((λ_ I).hom.f p).hom
      ((ιTensorObj _ I 0 p p (zero_add p)).hom (a ⊗ₜ[R] x))
  rw [unitTensor_apply]
  rfl

private theorem moduleHomothety_precomp {R : Type w} [CommRing R]
    {P I : CochainComplex (ModuleCat.{w} R) ℤ} (f : P ⟶ I) :
    moduleHomothety I ≫ Stacks.HomComplex.TensorHomMap.precomp R P I I f =
      Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) P ≫
        Stacks.HomComplex.TensorHomMap.postcomp R P
          ((𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) ⊗ P) I ((λ_ P).hom ≫ f) := by
  apply HomologicalComplex.from_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  -- Name both sides as honest composites of cochains before touching their components: the
  -- carrier of `(HomComplexR R P I).X 0` is only definitionally `Cochain P I 0`, and the
  -- component lemmas below cannot match through that.
  change (CochainComplex.HomComplex.Cochain.ofHom f).comp
      (((singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).hom.hom a) •
        CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) (zero_add 0) =
    (Stacks.HomComplex.TensorHomMap.Phiv R (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) P 0 a).comp
      (CochainComplex.HomComplex.Cochain.ofHom ((λ_ P).hom ≫ f)) (add_zero 0)
  apply CochainComplex.HomComplex.Cochain.ext₀
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [CochainComplex.HomComplex.Cochain.comp_v _ _ (zero_add 0)
      n n n (by omega) (by omega),
    CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.HomComplex.Cochain.comp_v _ _ (add_zero 0)
      n n n (by omega) (by omega),
    CochainComplex.HomComplex.Cochain.ofHom_v,
    Stacks.HomComplex.TensorHomMap.Phiv_v]
  simp only [ModuleCat.comp_apply, HomologicalComplex.comp_f,
    Stacks.HomComplex.TensorHomMap.tmulLeft_apply]
  rw [CochainComplex.HomComplex.Cochain.smul_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  rw [unitTensor_apply]
  exact ((f.f n).hom.map_smul _ _).symm

private theorem derivedHomothetyAt_precomp {R : Type w} [CommRing R]
    {P I : CochainComplex (ModuleCat.{w} R) ℤ} [I.IsKInjective]
    (hP : P.KFlat) (p : P ⟶ I) :
    let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
    derivedHomothetyAt I ≫
      D.hom.map ((DerivedCategory.Q.map p).op, 𝟙 (DerivedCategory.Q.obj I)) =
        (D.homZeroEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)).symm
          (DerivedCategory.Q.map p) := by
  let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
  apply (cancel_mono (D.homIso P I).hom).1
  calc
    (derivedHomothetyAt I ≫
        D.hom.map ((DerivedCategory.Q.map p).op, 𝟙 (DerivedCategory.Q.obj I))) ≫
        (D.homIso P I).hom =
      DerivedCategory.Q.map (moduleHomothety I ≫ Stacks.HomComplex.TensorHomMap.precomp R P I I p)
        := by
        have hn : D.hom.map ((DerivedCategory.Q.map p).op,
            𝟙 (DerivedCategory.Q.obj I)) ≫ (D.homIso P I).hom =
              (D.homIso I I).hom ≫
                DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp R P I I p) := by
          simpa using (D.homIso_naturality p (𝟙 I))
        rw [Category.assoc, hn]
        simp [derivedHomothetyAt]
    _ = DerivedCategory.Q.map
      (Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) P ≫
        Stacks.HomComplex.TensorHomMap.postcomp R P
          ((𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) ⊗ P) I ((λ_ P).hom ≫ p)) := by
        rw [moduleHomothety_precomp]
    _ = ((D.homZeroEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)).symm
          (DerivedCategory.Q.map p)) ≫ (D.homIso P I).hom := by
        rw [D.homZeroEquiv_symm_map P I hP p]
        simp

private theorem homZeroEquiv_naturality_left {R : Type w} [CommRing R]
    (D : StacksDraft.DerivedHom.DerivedHomData R)
    {K K' M : DerivedCategory (ModuleCat.{w} R)} (f : K' ⟶ K)
    (a : DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) ⟶
      D.hom.obj (Opposite.op K, M)) :
    D.homZeroEquiv K' M (a ≫ D.hom.map (f.op, 𝟙 M)) =
      f ≫ D.homZeroEquiv K M a := by
  dsimp [StacksDraft.DerivedHom.DerivedHomData.homZeroEquiv]
  rw [D.homEquiv_dinaturality]
  have h := D.tensorUnitLeft_naturality f
  apply (cancel_epi (D.tensorUnitLeft K').hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h]
  simp

private theorem homZeroEquiv_naturality_right {R : Type w} [CommRing R]
    (D : StacksDraft.DerivedHom.DerivedHomData R)
    {K M M' : DerivedCategory (ModuleCat.{w} R)} (g : M ⟶ M')
    (a : DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{w} R) ℤ)) ⟶
      D.hom.obj (Opposite.op K, M)) :
    D.homZeroEquiv K M' (a ≫ D.hom.map (𝟙 (Opposite.op K), g)) =
      D.homZeroEquiv K M a ≫ g := by
  dsimp [StacksDraft.DerivedHom.DerivedHomData.homZeroEquiv]
  rw [D.homEquiv_naturality_right, Category.assoc]

theorem isIso_canonicalHomothety_of_iso {R : Type w} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{w} R)} (e : K ≅ L)
    (hK : IsIso (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homZeroEquiv
      K K).symm (𝟙 K))) :
    IsIso (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homZeroEquiv
      L L).symm (𝟙 L)) := by
  let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
  let a := (D.homZeroEquiv K K).symm (𝟙 K)
  have hmap : D.hom.map (e.inv.op, e.hom) =
      D.hom.map (show (Opposite.op K, K) ⟶ (Opposite.op L, K) from
        (e.inv.op, 𝟙 K)) ≫
        D.hom.map (show (Opposite.op L, K) ⟶ (Opposite.op L, L) from
          (𝟙 (Opposite.op L), e.hom)) := by
    rw [← D.hom.map_comp]
    simp
  have heq : (D.homZeroEquiv L L).symm (𝟙 L) =
      a ≫ D.hom.map (e.inv.op, e.hom) := by
    apply (D.homZeroEquiv L L).injective
    rw [AddEquiv.apply_symm_apply, hmap, ← Category.assoc,
      homZeroEquiv_naturality_right, homZeroEquiv_naturality_left]
    simp [a]
  rw [heq]
  have : IsIso a := hK
  have : IsIso e.inv.op := inferInstance
  have : IsIso (show (Opposite.op K, K) ⟶ (Opposite.op L, L) from
      (e.inv.op, e.hom)) := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (D.hom.map
      (show (Opposite.op K, K) ⟶ (Opposite.op L, L) from (e.inv.op, e.hom))) :=
    inferInstance
  infer_instance

private theorem derivedHomothetyAt_homZeroEquiv {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ) [I.IsKInjective] :
    ((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homZeroEquiv
      (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj I))
      (derivedHomothetyAt I) = 𝟙 (DerivedCategory.Q.obj I) := by
  let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
  obtain ⟨P, p, hP, _, hp, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution I
  let : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).mpr hp
  have hnat := homZeroEquiv_naturality_left D (DerivedCategory.Q.map p)
    (derivedHomothetyAt I)
  rw [derivedHomothetyAt_precomp hP p, AddEquiv.apply_symm_apply] at hnat
  apply (cancel_epi (DerivedCategory.Q.map p)).mp
  simpa using hnat.symm

private theorem isIso_homZeroEquiv_symm_id_iff {R : Type w} [CommRing R]
    (I : CochainComplex (ModuleCat.{w} R) ℤ) [I.IsKInjective] :
    let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
    IsIso ((D.homZeroEquiv (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj I)).symm
      (𝟙 (DerivedCategory.Q.obj I))) ↔ QuasiIso (homothety I) := by
  let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
  have h : (D.homZeroEquiv (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj I)).symm
      (𝟙 (DerivedCategory.Q.obj I)) = derivedHomothetyAt I := by
    apply (D.homZeroEquiv (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj I)).injective
    simpa using (derivedHomothetyAt_homZeroEquiv I).symm
  change IsIso ((D.homZeroEquiv (DerivedCategory.Q.obj I)
    (DerivedCategory.Q.obj I)).symm (𝟙 (DerivedCategory.Q.obj I))) ↔
      QuasiIso (homothety I)
  rw [h]
  exact isIso_derivedHomothetyAt_iff I

private noncomputable def liftedHomComplexMapRestrictScalars
    {R : Type w} {S : Type x} [CommRing R] [CommRing S] (e : S ≃+* R)
    (I : CochainComplex (ModuleCat.{max w x} R) ℤ) :
    let F := ModuleCat.restrictScalars.{max w x} e.toRingHom
    liftedEndomorphismComplex I ⟶
      liftedEndomorphismComplex
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  intro F
  refine { f := ?_, comm' := ?_ }
  · intro n
    exact AddCommGrpCat.ofHom
      { toFun := fun z => ULift.up (z.down.map F)
        map_zero' := ULift.ext (CochainComplex.HomComplex.Cochain.map_zero I I n F)
        map_add' z z' :=
          ULift.ext (CochainComplex.HomComplex.Cochain.map_add z.down z'.down F) }
  · intro n m _
    ext z
    apply ULift.ext
    exact CochainComplex.HomComplex.δ_map n m z.down F

private theorem isIso_liftedHomComplexMapRestrictScalars
    {R : Type w} {S : Type x} [CommRing R] [CommRing S] (e : S ≃+* R)
    (I : CochainComplex (ModuleCat.{max w x} R) ℤ) :
    IsIso (liftedHomComplexMapRestrictScalars e I) := by
  let F := ModuleCat.restrictScalars.{max w x} e.toRingHom
  let : F.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  have (n : ℤ) : IsIso ((liftedHomComplexMapRestrictScalars e I).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ((Equiv.ulift.symm.bijective.comp (cochainMap_bijective F I I n)).comp
        Equiv.ulift.bijective)
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem homothety_restrictScalars_general
    {R : Type w} {S : Type x} [CommRing R] [CommRing S] (e : S ≃+* R)
    (I : CochainComplex (ModuleCat.{max w x} R) ℤ) :
    let F := ModuleCat.restrictScalars.{max w x} e.toRingHom
    let J := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
    let g : AddCommGrpCat.of (ULift.{max w x} R) ⟶
        AddCommGrpCat.of (ULift.{max w x} S) :=
      AddCommGrpCat.ofHom
        { toFun := fun a => ULift.up (e.symm a.down)
          map_zero' := by ext; simp
          map_add' := by intro a b; ext; simp }
    homothety I ≫ liftedHomComplexMapRestrictScalars e I =
      ((CochainComplex.singleFunctor AddCommGrpCat 0).map g) ≫
        homothety J := by
  intro F J g
  apply HomologicalComplex.from_single_hom_ext
  ext a
  apply ULift.ext
  apply CochainComplex.HomComplex.Cochain.ext₀
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  simp only [HomologicalComplex.comp_f, AddCommGrpCat.comp_apply]
  rw [homothety_f_zero_apply_source I a]
  rw [homothety_f_zero_apply_source J]
  change (((a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)).map F).v
      n n (add_zero n)).hom y =
    (((e.symm a.down) • CochainComplex.HomComplex.Cochain.ofHom (𝟙 J)).v
      n n (add_zero n)).hom y
  rw [CochainComplex.HomComplex.Cochain.map_v,
    CochainComplex.HomComplex.Cochain.smul_v,
    CochainComplex.HomComplex.Cochain.smul_v,
    CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  let yR : I.X n := y
  change a.down • yR = e (e.symm a.down) • yR
  rw [e.apply_symm_apply]

private theorem homothetyQuasiIso_restrictScalars_general_iff
    {R : Type w} {S : Type x} [CommRing R] [CommRing S] (e : S ≃+* R)
    (I : CochainComplex (ModuleCat.{max w x} R) ℤ) :
    QuasiIso (homothety
      (((ModuleCat.restrictScalars.{max w x} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) ↔ QuasiIso (homothety I) := by
  let g : AddCommGrpCat.of (ULift.{max w x} R) ⟶
      AddCommGrpCat.of (ULift.{max w x} S) :=
    AddCommGrpCat.ofHom
      { toFun := fun a => ULift.up (e.symm a.down)
        map_zero' := by ext; simp
        map_add' := by intro a b; ext; simp }
  have : IsIso g := (ConcreteCategory.isIso_iff_bijective g).mpr
    ((Equiv.ulift.symm.bijective.comp e.symm.bijective).comp Equiv.ulift.bijective)
  have : IsIso ((CochainComplex.singleFunctor AddCommGrpCat 0).map g) := inferInstance
  have : IsIso (liftedHomComplexMapRestrictScalars e I) :=
    isIso_liftedHomComplexMapRestrictScalars e I
  rw [← quasiIso_iff_comp_right (homothety I) (liftedHomComplexMapRestrictScalars e I),
    homothety_restrictScalars_general e I,
    quasiIso_iff_comp_left ((CochainComplex.singleFunctor AddCommGrpCat 0).map g)]

private theorem homothetyQuasiIso_restrictScalars_general
    {R : Type w} {S : Type x} [CommRing R] [CommRing S] (e : S ≃+* R)
    (I : CochainComplex (ModuleCat.{max w x} R) ℤ)
    (hI : QuasiIso (homothety I)) :
    QuasiIso (homothety
      (((ModuleCat.restrictScalars.{max w x} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) :=
  (homothetyQuasiIso_restrictScalars_general_iff e I).2 hI

private theorem homothetyQuasiIso_of_restrictScalars_general
    {R : Type w} {S : Type x} [CommRing R] [CommRing S] (e : S ≃+* R)
    (I : CochainComplex (ModuleCat.{max w x} R) ℤ)
    (hJ : QuasiIso (homothety
      (((ModuleCat.restrictScalars.{max w x} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I))) :
    QuasiIso (homothety I) :=
  (homothetyQuasiIso_restrictScalars_general_iff e I).1 hJ

private noncomputable def derivedRestrictScalarsUnitIso
    {R : Type w} {S : Type x} [CommRing R] [CommRing S] (e : S ≃+* R)
    (K : DerivedCategory (ModuleCat.{max w x} R)) :
    let F := ModuleCat.restrictScalars.{max w x} e.toRingHom
    let G := ModuleCat.restrictScalars.{max w x} e.symm.toRingHom
    G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) ≅ K := by
  intro F G
  let P := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let Ecat := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let Ec := Ecat.mapHomologicalComplex (ComplexShape.up ℤ)
  exact G.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso eK.symm) ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
    G.mapDerivedCategoryFactors.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.mapIso (Ec.unitIso.app P).symm ≪≫ eK

private theorem additiveHomothety_ulift_change
    {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{v} A) ℤ) :
    let A' := ULift.{v} A
    let U := ModuleCat.uliftFunctor.{u, v} A
    let C := ModuleCat.restrictScalars.{max u v} (ULift.ringEquiv : A' ≃+* A).toRingHom
    let F := U ⋙ C
    let J := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
    homothety I ≫ homComplexMapLift F I I = additiveHomothety J := by
  intro A' U C F J
  apply HomologicalComplex.from_single_hom_ext
  ext a
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  obtain rfl : p = q := by omega
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private theorem homothetyQuasiIso_ulift_change
    {A : Type u} [CommRing A]
    (I : CochainComplex (ModuleCat.{v} A) ℤ)
    (hI : QuasiIso (homothety I)) :
    let A' := ULift.{v} A
    let U := ModuleCat.uliftFunctor.{u, v} A
    let C := ModuleCat.restrictScalars.{max u v} (ULift.ringEquiv : A' ≃+* A).toRingHom
    QuasiIso (homothety
      ((C.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := by
  intro A' U C
  let F := U ⋙ C
  let J := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let : C.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (ULift.ringEquiv : A' ≃+* A)
  have : IsIso (homComplexMapLift F I I) := isIso_homComplexMapLift F I I
  have : QuasiIso (homothety I) := hI
  have hJ : QuasiIso (additiveHomothety J) := by
    rw [← additiveHomothety_ulift_change I]
    infer_instance
  change QuasiIso (homothety J)
  exact (additiveHomothety_quasiIso_iff J).1 hJ

/-- A functor preserving injective objects and zero morphisms maps a bounded below complex of
injectives to a `K`-injective complex. -/
private theorem isKInjective_map_of_injective {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesInjectiveObjects]
    (I : CochainComplex C ℤ) (a : ℤ) [I.IsStrictlyGE a] (hinj : ∀ i, Injective (I.X i)) :
    (show CochainComplex D ℤ from (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
      ).IsKInjective := by
  have : (show CochainComplex D ℤ from
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => F.map_isZero ((CochainComplex.isStrictlyGE_iff I a).mp inferInstance i hi)
  have : ∀ i, Injective (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).X i) :=
    fun i => F.injective_obj_of_injective (hinj i)
  exact CochainComplex.isKInjective_of_injective _ a

private theorem isIso_canonicalHomothety_ulift_change
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : IsDualizingComplex K) :
    let A' := ULift.{v} A
    let U := ModuleCat.uliftFunctor.{u, v} A
    let C := ModuleCat.restrictScalars.{max u v} (ULift.ringEquiv : A' ≃+* A).toRingHom
    let K₂ := C.mapDerivedCategory.obj (U.mapDerivedCategory.obj K)
    IsIso (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction A').homZeroEquiv
      K₂ K₂).symm (𝟙 K₂)) := by
  intro A' U C K₂
  obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hK.finiteInjectiveDimension
  let : Small.{v} A := small_base_from_dualizing K hK
  let : Small.{max u v} A := small_lift.{u, max u v, v} A
  let F := U ⋙ C
  let J : CochainComplex (ModuleCat.{max u v} A') ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let : U.PreservesInjectiveObjects := inferInstance
  let : C.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (ULift.ringEquiv : A' ≃+* A)
  let : C.PreservesInjectiveObjects := inferInstance
  have : J.IsKInjective := isKInjective_map_of_injective F I a hinj
  have hI : QuasiIso (homothety I) :=
    hK.homothetyQuasiIso I ⟨eI.symm⟩ hinj ⟨a, b, hge, hle⟩
  have hJ : QuasiIso (homothety J) := by
    change QuasiIso (homothety
      ((C.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
    exact homothetyQuasiIso_ulift_change I hI
  have hQJ : IsIso
      (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction A').homZeroEquiv
        (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj J)).symm
          (𝟙 (DerivedCategory.Q.obj J))) :=
    (isIso_homZeroEquiv_symm_id_iff J).2 hJ
  let e₁ : DerivedCategory.Q.obj
      ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      U.mapDerivedCategory.obj K :=
    (U.mapDerivedCategoryFactors.app I).symm ≪≫ U.mapDerivedCategory.mapIso eI.symm
  let e₂ : DerivedCategory.Q.obj J ≅ K₂ :=
    (C.mapDerivedCategoryFactors.app
      ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).symm ≪≫
      C.mapDerivedCategory.mapIso e₁
  exact isIso_canonicalHomothety_of_iso e₂ hQJ

private theorem isIso_canonicalHomothety_restrictScalars
    {R S : Type w} [CommRing R] [CommRing S] (e : S ≃+* R)
    (K : DerivedCategory (ModuleCat.{w} R))
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K)
    (hcanon : IsIso
      (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homZeroEquiv
        K K).symm (𝟙 K))) :
    let F := ModuleCat.restrictScalars.{w} e.toRingHom
    let L := F.mapDerivedCategory.obj K
    IsIso (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction S).homZeroEquiv
      L L).symm (𝟙 L)) := by
  intro F L
  obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hK
  let J : CochainComplex (ModuleCat.{w} S) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let : F.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  let : F.PreservesInjectiveObjects := inferInstance
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  have : J.IsKInjective := isKInjective_map_of_injective F I a hinj
  have hQI : IsIso
      (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homZeroEquiv
        (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj I)).symm
          (𝟙 (DerivedCategory.Q.obj I))) :=
    isIso_canonicalHomothety_of_iso eI hcanon
  have hI : QuasiIso (homothety I) :=
    (isIso_homZeroEquiv_symm_id_iff I).1 hQI
  have hJ : QuasiIso (homothety J) :=
    homothetyQuasiIso_restrictScalars_general e I hI
  have hQJ : IsIso
      (((StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction S).homZeroEquiv
        (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj J)).symm
          (𝟙 (DerivedCategory.Q.obj J))) :=
    (isIso_homZeroEquiv_symm_id_iff J).2 hJ
  let eJ : DerivedCategory.Q.obj J ≅ L :=
    (F.mapDerivedCategoryFactors.app I).symm ≪≫
      F.mapDerivedCategory.mapIso eI.symm
  exact isIso_canonicalHomothety_of_iso eJ hQJ

end Dualizing
