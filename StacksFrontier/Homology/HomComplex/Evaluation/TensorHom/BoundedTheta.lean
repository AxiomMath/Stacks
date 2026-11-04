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
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.RepresentativeDiagonal
import StacksCore.Tactic.EgaSgaAttribute
import all StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.ProjectiveComparison
import all StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.RepresentativeDiagonal

/-!
# Retracts, representatives and the bounded tensor--Hom comparison

Generic categorical input for the invertibility of the derived tensor--Hom diagonal (stability
under retracts and under isomorphisms of representatives, and the tensor--Hom strength of an
adjunction with a dual object), the reduction of the diagonal to a
quasi-isomorphism of `Stacks.HomComplex.TensorHomComparison.theta` on representatives, and the
degreewise bijectivity of `theta` when the tensor factors are bounded below and the Hom source is
a bounded-above complex of finite projective modules (`isIso_theta_of_boundedBelow`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u v w w'

set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000

namespace Stacks.DerivedTensorHomDiagonal

open StacksDraft.DerivedHom

/-! ### Generic categorical input -/


/-- The tensor–Hom comparison is bijective when its Hom source is finite projective. -/
private theorem bijective_lTensorHomToHomLTensor
    {R : Type u} [CommSemiring R]
    (M : Type v) (K : Type w) (L : Type w')
    [AddCommMonoid M] [AddCommMonoid K] [AddCommMonoid L]
    [Module R M] [Module R K] [Module R L]
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (TensorProduct.lTensorHomToHomLTensor (RingHom.id R) M K L) := by
  rw [← lTensorHomEquivHomLTensor_toLinearMap]
  exact (lTensorHomEquivHomLTensor R M K L).bijective

/-- Being invertible at an object is preserved under retracts of that object. -/
private theorem isIso_app_of_retract
    {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (τ : F ⟶ G) {X Y : C} (r : Retract X Y)
    [IsIso (τ.app Y)] : IsIso (τ.app X) := by
  refine ⟨G.map r.i ≫ inv (τ.app Y) ≫ F.map r.r, ?_, ?_⟩
  · rw [← τ.naturality_assoc, IsIso.hom_inv_id_assoc, ← F.map_comp, r.retract, F.map_id]
  · rw [Category.assoc, Category.assoc, τ.naturality, IsIso.inv_hom_id_assoc,
      ← G.map_comp, r.retract, G.map_id]

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of triangulated functors which is invertible on a family of objects is
invertible throughout its saturated triangulated envelope. -/
private theorem isIso_app_of_mem_triangEnvelope
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (P : ObjectProperty C) (h : ∀ X, P X → IsIso (τ.app X))
    (X : C) (hX : P.triangEnvelope X) : IsIso (τ.app X) := by
  let Q : ObjectProperty C := fun X ↦ IsIso (τ.app X)
  have : Q.IsStableUnderRetracts := ⟨fun r hY ↦ by
    have : IsIso (τ.app _) := hY
    exact isIso_app_of_retract τ r⟩
  have : Q.IsStableUnderShift ℤ := ⟨fun n ↦ .mk (fun Y hY ↦ by
    have : IsIso (τ.app _) := hY
    show IsIso (τ.app (Y⟦n⟧))
    rw [NatTrans.app_shift]
    infer_instance)⟩
  have : Q.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦ by
    let f : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T :=
      { hom₁ := τ.app T.obj₁
        hom₂ := τ.app T.obj₂
        hom₃ := τ.app T.obj₃
        comm₁ := τ.naturality T.mor₁
        comm₂ := τ.naturality T.mor₂
        comm₃ := by
          show (F.map T.mor₃ ≫ _) ≫ _ = _ ≫ G.map T.mor₃ ≫ _
          rw [Category.assoc, NatTrans.shift_app_comm, τ.naturality_assoc] }
    exact isIso₂_of_isIso₁₃ f (F.map_distinguished T hT)
      (G.map_distinguished T hT) h₁ h₃)
  have : Q.ContainsZero := ⟨0, isZero_zero C, by
    show IsIso (τ.app (0 : C))
    exact IsZero.isIso (Functor.map_isZero F (isZero_zero C))
      (Functor.map_isZero G (isZero_zero C)) _⟩
  have : Q.IsTriangulated := {}
  exact ((P.triangEnvelope_le_iff).2 h) X hX

section TensorHomStrength
variable {C : Type*} [Category* C] [MonoidalCategory C]

private noncomputable def tensorHomStrength {M : C} {H : C ⥤ C} (a : tensorRight M ⊣ H) (K L : C) :
    K ⊗ H.obj L ⟶ H.obj (K ⊗ L) :=
  a.homEquiv _ _ ((α_ K (H.obj L) M).hom ≫ K ◁ a.counit.app L)

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_tensorHomStrength_of_source_dual {M N : C} [ExactPairing M N] {H : C ⥤ C}
    (a : tensorRight M ⊣ H) (K L : C) : IsIso (tensorHomStrength a K L) := by
  let b := tensorRightAdjunction M N
  let e := b.rightAdjointUniq a
  have he (X : C) : e.hom.app X ▷ M ≫ a.counit.app X = b.counit.app X :=
    b.rightAdjointUniq_hom_app_counit a X
  have hh : K ◁ e.hom.app L ≫ tensorHomStrength a K L =
      (α_ K L N).inv ≫ e.hom.app (K ⊗ L) := by
    apply (a.homEquiv _ _).symm.injective
    rw [a.homEquiv_naturality_left_symm, a.homEquiv_naturality_left_symm]
    simp only [tensorHomStrength, Equiv.symm_apply_apply]
    rw [a.homEquiv_symm_apply]
    show (K ◁ e.hom.app L) ▷ M ≫ (α_ K (H.obj L) M).hom ≫ K ◁ a.counit.app L =
      (α_ K L N).inv ▷ M ≫ e.hom.app (K ⊗ L) ▷ M ≫ a.counit.app (K ⊗ L)
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, he, he]
    have hc (X : C) : b.counit.app X = (α_ X N M).hom ≫ X ◁ ε_ M N ≫ (ρ_ X).hom := by
      show (𝟙 (X ⊗ N)) ▷ M ≫ _ = _
      simp
    rw [hc, hc]
    monoidal
  have : IsIso (K ◁ e.hom.app L ≫ tensorHomStrength a K L) := by
    rw [hh]
    infer_instance
  exact IsIso.of_isIso_comp_left (K ◁ e.hom.app L) _

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_tensorHomStrength_of_tensor_dual {K N : C} [ExactPairing K N] {M : C}
    {H : C ⥤ C} (a : tensorRight M ⊣ H) (L : C) : IsIso (tensorHomStrength a K L) := by
  let e (X : C) : (X ⟶ K ⊗ H.obj L) ≃ (X ⟶ H.obj (K ⊗ L)) :=
    (tensorLeftHomEquiv X K N (H.obj L)).symm.trans
      ((a.homEquiv (N ⊗ X) L).symm.trans
        ((Iso.homCongr (α_ N X M) (Iso.refl L)).trans
          ((tensorLeftHomEquiv (X ⊗ M) K N L).trans (a.homEquiv X (K ⊗ L)))))
  have he (X : C) (f : X ⟶ K ⊗ H.obj L) : e X f = f ≫ tensorHomStrength a K L := by
    apply (a.homEquiv _ _).symm.injective
    apply (tensorLeftHomEquiv (X ⊗ M) K N L).symm.injective
    dsimp [e]
    simp only [Equiv.symm_apply_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
    show _ = (tensorLeftHomEquiv (X ⊗ M) K N L).symm
      ((a.homEquiv X (K ⊗ L)).symm (f ≫ a.homEquiv _ _
        ((α_ K (H.obj L) M).hom ≫ K ◁ a.counit.app L)))
    rw [a.homEquiv_naturality_left_symm f]
    simp only [Equiv.symm_apply_apply]
    have hn {A B : C} (g : (X ⊗ M) ⟶ K ⊗ A) (h : A ⟶ B) :
        (tensorLeftHomEquiv (X ⊗ M) K N B).symm (g ≫ K ◁ h) =
          (tensorLeftHomEquiv (X ⊗ M) K N A).symm g ≫ h := by
      apply (tensorLeftHomEquiv (X ⊗ M) K N B).injective
      rw [Equiv.apply_symm_apply, tensorLeftHomEquiv_naturality, Equiv.apply_symm_apply]
    show _ = (tensorLeftHomEquiv (X ⊗ M) K N L).symm
      (f ▷ M ≫ (α_ K (H.obj L) M).hom ≫ K ◁ a.counit.app L)
    rw [← Category.assoc, hn]
    have ht := tensorLeftHomEquiv_tensor (Y' := N) f (𝟙 M)
    simp only [tensorHom_id] at ht
    rw [ht]
    show (α_ N X M).inv ≫
      ((tensorLeftHomEquiv X K N (H.obj L)).symm f) ▷ M ≫ a.counit.app L = _
    simp only [Category.assoc]
  exact (isIso_iff_yoneda_map_bijective _).mpr fun X => by
    simpa only [← he] using (e X).bijective

end TensorHomStrength

variable {R : Type u} [CommRing R]

/-- The isomorphism property of the diagonal is stable under retracts of its tensor factor. -/
private theorem isIso_diagonal_of_retract_tensor
    {K K' : DerivedCategory (ModuleCat R)} (L M : DerivedCategory (ModuleCat R))
    (r : Retract K K') [IsIso (DerivedInternalHom.Model.diagonal K' L M)] :
    IsIso (DerivedInternalHom.Model.diagonal K L M) := by
  let T := Functor.curry.obj (DerivedInternalHom.Model.tensor R)
  let H := Functor.curry.obj (DerivedInternalHom.Model.hom R)
  let F := T.flip.obj ((DerivedInternalHom.Model.hom R).obj (Opposite.op M, L))
  let G := T.flip.obj L ⋙ H.obj (Opposite.op M)
  let τ : F ⟶ G :=
    { app K := DerivedInternalHom.Model.diagonal K L M
      naturality {X Y} f :=
        (DerivedInternalHom.Model.canonicalMapLaws R).diagonal_naturality_tensor f }
  exact isIso_app_of_retract τ r

/-- The isomorphism property of the diagonal is stable under retracts of its target. -/
private theorem isIso_diagonal_of_retract_target
    (K M : DerivedCategory (ModuleCat R)) {L L' : DerivedCategory (ModuleCat R)}
    (r : Retract L L') [IsIso (DerivedInternalHom.Model.diagonal K L' M)] :
    IsIso (DerivedInternalHom.Model.diagonal K L M) := by
  let T := Functor.curry.obj (DerivedInternalHom.Model.tensor R)
  let H := Functor.curry.obj (DerivedInternalHom.Model.hom R)
  let F := H.obj (Opposite.op M) ⋙ T.obj K
  let G := T.obj K ⋙ H.obj (Opposite.op M)
  let τ : F ⟶ G :=
    { app L := DerivedInternalHom.Model.diagonal K L M
      naturality {X Y} f :=
        (DerivedInternalHom.Model.canonicalMapLaws R).diagonal_naturality_target f }
  exact isIso_app_of_retract τ r

/-- The isomorphism property of the diagonal is stable under retracts of its Hom source. -/
private theorem isIso_diagonal_of_retract_source
    (K L : DerivedCategory (ModuleCat R)) {M M' : DerivedCategory (ModuleCat R)}
    (r : Retract M M') [IsIso (DerivedInternalHom.Model.diagonal K L M')] :
    IsIso (DerivedInternalHom.Model.diagonal K L M) := by
  let T := Functor.curry.obj (DerivedInternalHom.Model.tensor R)
  let H := Functor.curry.obj (DerivedInternalHom.Model.hom R)
  let F := H.flip.obj L ⋙ T.obj K
  let G := H.flip.obj ((DerivedInternalHom.Model.tensor R).obj (K, L))
  let τ : F ⟶ G :=
    { app M := DerivedInternalHom.Model.diagonal K L M.unop
      naturality {X Y} f :=
        (DerivedInternalHom.Model.canonicalMapLaws R).diagonal_naturality_source f.unop }
  exact isIso_app_of_retract τ
    (show Retract (Opposite.op M) (Opposite.op M') from
      { i := r.r.op, r := r.i.op, retract := by rw [← op_comp, r.retract, op_id] })

/-- Isomorphism of any representatives preserves invertibility of the diagonal. -/
public theorem isIso_diagonal_of_iso
    {K K' L L' M M' : DerivedCategory (ModuleCat R)}
    (eK : K ≅ K') (eL : L ≅ L') (eM : M ≅ M')
    [IsIso (DerivedInternalHom.Model.diagonal K' L' M')] :
    IsIso (DerivedInternalHom.Model.diagonal K L M) := by
  have := isIso_diagonal_of_retract_tensor L' M'
    (show Retract K K' from ⟨eK.hom, eK.inv, eK.hom_inv_id⟩)
  have := isIso_diagonal_of_retract_target K M'
    (show Retract L L' from ⟨eL.hom, eL.inv, eL.hom_inv_id⟩)
  exact isIso_diagonal_of_retract_source K L
    (show Retract M M' from ⟨eM.hom, eM.inv, eM.hom_inv_id⟩)

/-- A Hom complex from a complex bounded above to one bounded below is bounded below. -/
public theorem isStrictlyGE_homComplex
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (d b : ℤ)
    [P.IsStrictlyLE d] [L.IsStrictlyGE b] :
    (CochainComplex.HomComplexR R P L).IsStrictlyGE (b - d) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ ?_⟩
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  by_cases hp : d < p
  · exact (P.isZero_of_isStrictlyLE d p hp).eq_of_src _ _
  · exact (L.isZero_of_isStrictlyGE b q (by omega)).eq_of_tgt _ _

/-- Evaluation identifies a bounded Hom-complex degree with a finite product of Hom modules. -/
public theorem bijective_cochain_evaluation
    {C : Type*} [Category* C] [Preadditive C]
    (P L : CochainComplex C ℤ) (d b n : ℤ)
    [P.IsStrictlyLE d] [L.IsStrictlyGE b] :
    Function.Bijective
      (fun z : CochainComplex.HomComplex.Cochain P L n ↦
        fun p : Set.Icc (b - n) d ↦ z.v p (p + n) rfl) := by
  classical
  refine ⟨fun x y h ↦ ?_, fun f ↦ ?_⟩
  · apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    subst q
    by_cases hp : p ∈ Set.Icc (b - n) d
    · exact congrFun h ⟨p, hp⟩
    by_cases hpd : d < p
    · exact (P.isZero_of_isStrictlyLE d p hpd).eq_of_src _ _
    · exact (L.isZero_of_isStrictlyGE b (p + n) (by
        simp only [Set.mem_Icc] at hp
        omega)).eq_of_tgt _ _
  · refine ⟨CochainComplex.HomComplex.Cochain.mk (fun p q hpq ↦ ?_), ?_⟩
    · subst q
      exact if hp : p ∈ Set.Icc (b - n) d then f ⟨p, hp⟩ else 0
    · funext p
      simp only [CochainComplex.HomComplex.Cochain.mk_v, dite_eq_left p.property]

/-- Each bounded Hom degree is the finite product of its potentially nonzero components. -/
public noncomputable def cochainEvaluationLinearEquiv
    {C : Type*} [Category* C] [Preadditive C] [Linear R C]
    (P L : CochainComplex C ℤ) (d b n : ℤ)
    [P.IsStrictlyLE d] [L.IsStrictlyGE b] :
    CochainComplex.HomComplex.Cochain P L n ≃ₗ[R]
      (∀ p : Set.Icc (b - n) d, P.X p ⟶ L.X (p + n)) :=
  LinearEquiv.ofBijective
    ({ toFun z p := z.v p (p + n) rfl
       map_add' _ _ := rfl
       map_smul' _ _ := rfl } :
      CochainComplex.HomComplex.Cochain P L n →ₗ[R]
        (∀ p : Set.Icc (b - n) d, P.X p ⟶ L.X (p + n)))
    (bijective_cochain_evaluation P L d b n)

/-- The finite product comparison is component evaluation. -/
public theorem cochainEvaluationLinearEquiv_apply
    {C : Type*} [Category* C] [Preadditive C] [Linear R C]
    (P L : CochainComplex C ℤ) (d b n : ℤ)
    [P.IsStrictlyLE d] [L.IsStrictlyGE b]
    (z : CochainComplex.HomComplex.Cochain P L n) (p : Set.Icc (b - n) d) :
    cochainEvaluationLinearEquiv (R := R) P L d b n z p = z.v p (p + n) rfl := rfl

/-- The boundedness hypotheses give simultaneous models of the three complexes. -/
private theorem exists_bounded_tensorHom_representatives
    (K L M : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M) [L.IsGE b]
    (hK : ∀ (N : ModuleCat.{u} R) (i : ℤ), i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))))) :
    ∃ (E F P : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ),
      E.IsStrictlyGE a ∧ E.KFlat ∧ (∀ i, Module.Flat R (E.X i)) ∧
      F.IsStrictlyGE b ∧ P.IsStrictlyLE d ∧
      (∀ i, Module.Finite R (P.X i) ∧ Module.Free R (P.X i)) ∧
      Nonempty (K ≅ DerivedCategory.Q.obj E) ∧
      Nonempty (L ≅ DerivedCategory.Q.obj F) ∧
      Nonempty (M ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨E, hEk, hEf, hEa, eK⟩ :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R) K a).mp hK
  obtain ⟨F, hFb, eL⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE L b
  obtain ⟨P, hP, ⟨eM⟩⟩ := hM
  obtain ⟨d, hPd⟩ := hP.upperBound
  exact ⟨E, F, P, d, hEa, hEk, hEf, hFb, hPd, hP.finiteFree, eK, eL, ⟨eM.symm⟩⟩

/-- A K-flat left factor computes derived tensor product, by symmetry. -/
private noncomputable abbrev tensorIsoOfKFlatLeft
    (K L : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat) :
    (DerivedInternalHom.Model.tensor R).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (K ⊗ L) :=
  letI := CochainComplex.Koszul.koszulSymmetric R
  (DerivedInternalHom.Model.adjunction R).tensorSwap _ _ ≪≫
    (DerivedInternalHom.Model.adjunction R).tensorIso L K hK ≪≫
    DerivedCategory.Q.mapIso (β_ L K)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison for a K-flat left factor is natural in both complex variables. -/
private theorem tensorIsoOfKFlatLeft_naturality
    (K K' L L' : CochainComplex (ModuleCat R) ℤ)
    (hK : K.KFlat) (hK' : K'.KFlat) (f : K ⟶ K') (g : L ⟶ L') :
    (DerivedInternalHom.Model.tensor R).map
        (DerivedCategory.Q.map f, DerivedCategory.Q.map g) ≫
      (tensorIsoOfKFlatLeft K' L' hK').hom =
    (tensorIsoOfKFlatLeft K L hK).hom ≫ DerivedCategory.Q.map (f ⊗ₘ g) := by
  let := CochainComplex.Koszul.koszulSymmetric R
  dsimp only [tensorIsoOfKFlatLeft, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% ((DerivedInternalHom.Model.adjunction R).tensorSwap_naturality
      (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)),
    reassoc_of% ((DerivedInternalHom.Model.adjunction R).tensorIso_naturality g f hK hK'),
    ← Functor.map_comp, BraidedCategory.braiding_naturality, Functor.map_comp]

/-- For a K-flat tensor factor and a bounded-above projective Hom source, both objects of
the derived diagonal are represented by the ordinary tensor and Hom complexes. -/
private theorem nonempty_tensorHom_model_isos
    (K L M : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat)
    (d : ℤ) [M.IsStrictlyLE d] [∀ i, Projective (M.X i)] :
    Nonempty ((DerivedInternalHom.Model.tensor R).obj
        (DerivedCategory.Q.obj K, (DerivedInternalHom.Model.hom R).obj
          (Opposite.op (DerivedCategory.Q.obj M), DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj (K ⊗ CochainComplex.HomComplexR R M L)) ∧
    Nonempty ((DerivedInternalHom.Model.hom R).obj
        (Opposite.op (DerivedCategory.Q.obj M), (DerivedInternalHom.Model.tensor R).obj
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR R M (K ⊗ L))) := by
  let c := Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)
  exact ⟨⟨(DerivedInternalHom.Model.tensor R).mapIso
      ((Iso.refl (DerivedCategory.Q.obj K)).prod (c.iso M L d)) ≪≫
    tensorIsoOfKFlatLeft K (CochainComplex.HomComplexR R M L) hK⟩,
    ⟨(DerivedInternalHom.Model.hom R).mapIso
      ((Iso.refl (Opposite.op (DerivedCategory.Q.obj M))).prod
        (tensorIsoOfKFlatLeft K L hK)) ≪≫ c.iso M (K ⊗ L) d⟩⟩

/-- A quasi-isomorphism of the tensor–Hom comparison induces an isomorphism of its derived
diagonal whenever the canonical representative comparisons apply. -/
public theorem isIso_diagonal_of_quasiIso_theta
    (K L M : CochainComplex (ModuleCat R) ℤ) [L.IsKInjective]
    [(K ⊗ L).IsKInjective] (hL : L.KFlat)
    (h : (CochainComplex.HomComplexR R M L).KFlat)
    [QuasiIso (Stacks.HomComplex.TensorHomComparison.theta K L M)] :
    IsIso (DerivedInternalHom.Model.diagonal
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)) := by
  rw [DerivedInternalHom.Model.diagonal_comparison K L M hL h]
  have : IsIso ((𝟙 (DerivedCategory.Q.obj K)),
      ((DerivedInternalHom.Model.adjunction R).homIso M L).hom) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (𝟙 (Opposite.op (DerivedCategory.Q.obj M)),
      ((DerivedInternalHom.Model.adjunction R).tensorIso K L hL).inv) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  infer_instance

open CochainComplex HomComplex HomologicalComplex TensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- Projection onto a homogeneous tensor summand. -/
private noncomputable def tensorDegreeProjection
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n p q : ℤ) (hpq : p + q = n) :
    (K ⊗ L).X n ⟶ K.X p ⊗ L.X q := by
  classical
  exact GradedObject.Monoidal.tensorObjDesc (X₁ := K.X) (X₂ := L.X)
    (fun i j h ↦ if hi : i = p then
      eqToHom (by
        subst i
        have hj : j = q := by omega
        exact congrArg (fun t ↦ MonoidalCategory.tensorObj (K.X p) (L.X t)) hj) else 0)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorDegreeProjection_self
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n p q : ℤ) (h : p + q = n) :
    ιTensorObj K L p q n h ≫ tensorDegreeProjection K L n p q h = 𝟙 _ := by
  obtain rfl : q = n - p := by omega
  show GradedObject.Monoidal.ιTensorObj K.X L.X p (n - p) n _ ≫ _ = _
  simp [tensorDegreeProjection, GradedObject.Monoidal.ι_tensorObjDesc]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorDegreeProjection_ne
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n p q i j : ℤ)
    (h : p + q = n) (hij : i + j = n) (hi : i ≠ p) :
    ιTensorObj K L i j n hij ≫ tensorDegreeProjection K L n p q h = 0 := by
  obtain rfl : q = n - p := by omega
  show GradedObject.Monoidal.ιTensorObj K.X L.X i j n hij ≫ _ = _
  simp [tensorDegreeProjection, GradedObject.Monoidal.ι_tensorObjDesc, hi]

/-- A tensor summand vanishes if either factor vanishes. -/
private theorem tensor_eq_zero_of_isZero
    (A B : ModuleCat.{u} R) (h : IsZero A ∨ IsZero B) (x : A ⊗[R] B) : x = 0 := by
  rcases h with h | h
  · have : Subsingleton A := ModuleCat.isZero_iff_subsingleton.mp h
    have : Subsingleton (A ⊗[R] B) := inferInstance
    exact Subsingleton.elim _ _
  · have : Subsingleton B := ModuleCat.isZero_iff_subsingleton.mp h
    have : Subsingleton (A ⊗[R] B) := inferInstance
    exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- Finitely supported tensor degrees are reconstructed from their homogeneous projections. -/
private theorem sum_tensorDegreeProjection
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (S : Finset ℤ)
    (hS : ∀ p ∉ S, IsZero (K.X p) ∨ IsZero (L.X (n - p))) :
    ∑ p ∈ S, tensorDegreeProjection K L n p (n - p) (by omega) ≫
      ιTensorObj K L p (n - p) n (by omega) =
      𝟙 ((K ⊗ L).X n) := by
  classical
  apply mapBifunctor.hom_ext
  intro i j hij
  have hj : j = n - i := by change i + j = n at hij; omega
  subst j
  show ιTensorObj K L i (n - i) n (by omega) ≫ _ = _
  simp only [Preadditive.comp_sum, ← Category.assoc]
  by_cases hi : i ∈ S
  · rw [Finset.sum_eq_single i, tensorDegreeProjection_self K L n i (n - i) (by omega)]
    · show (𝟙 (K.X i ⊗ L.X (n - i)) ≫ ιTensorObj K L i (n - i) n (by omega)) =
        ιTensorObj K L i (n - i) n (by omega) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
    · intro p hp hpi
      rw [tensorDegreeProjection_ne K L n p (n - p) i (n - i) (by omega) (by omega) (Ne.symm hpi),
        zero_comp]
    · exact fun h ↦ (h hi).elim
  · have hz : IsZero (MonoidalCategory.tensorObj (K.X i) (L.X (n - i))) :=
      ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y ↦ by
        rw [tensor_eq_zero_of_isZero _ _ (hS i hi) x,
          tensor_eq_zero_of_isZero _ _ (hS i hi) y]⟩
    exact hz.eq_of_src _ _

/-- Tensoring a bounded Hom degree is the product of the finite-projective component maps. -/
private noncomputable def tensorCochainEvaluationEquiv
    (A : Type u) [AddCommGroup A] [Module R A]
    (M L : CochainComplex (ModuleCat.{u} R) ℤ) (d b q : ℤ)
    [M.IsStrictlyLE d] [L.IsStrictlyGE b]
    [∀ i, Module.Finite R (M.X i)] [∀ i, Module.Projective R (M.X i)] :
    (A ⊗[R] Cochain M L q) ≃ₗ[R]
      (∀ i : Set.Icc (b - q) d, M.X i →ₗ[R] A ⊗[R] L.X (i + q)) := by
  classical
  exact (TensorProduct.congr (LinearEquiv.refl R A)
      ((cochainEvaluationLinearEquiv M L d b q) ≪≫ₗ
        (LinearEquiv.piCongrRight fun _ ↦ ModuleCat.homLinearEquiv (S := R)))) ≪≫ₗ
    TensorProduct.piRight R R A _ ≪≫ₗ
    (LinearEquiv.piCongrRight fun i ↦ lTensorHomEquivHomLTensor R (M.X i) A (L.X (i + q)))

private theorem tensorCochainEvaluationEquiv_tmul
    (A : Type u) [AddCommGroup A] [Module R A]
    (M L : CochainComplex (ModuleCat.{u} R) ℤ) (d b q : ℤ)
    [M.IsStrictlyLE d] [L.IsStrictlyGE b]
    [∀ i, Module.Finite R (M.X i)] [∀ i, Module.Projective R (M.X i)]
    (x : A) (φ : Cochain M L q) (i : Set.Icc (b - q) d) (m : M.X i) :
    tensorCochainEvaluationEquiv A M L d b q (x ⊗ₜ[R] φ) i m =
      x ⊗ₜ[R] (φ.v i (i + q) rfl m) := by
  simp [tensorCochainEvaluationEquiv, TensorProduct.piRight_apply,
    cochainEvaluationLinearEquiv_apply]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
/-- Changing the displayed right-hand degree does not change vanishing of a projection. -/
private theorem tensorDegreeProjection_eq_zero_iff
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n p q q' : ℤ)
    (h : p + q = n) (h' : p + q' = n) (x : (K ⊗ L).X n) :
    tensorDegreeProjection K L n p q h x = 0 ↔
      tensorDegreeProjection K L n p q' h' x = 0 := by
  have hq : q' = q := by omega
  subst q'
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tensorDegreeProjection_cochain_ι
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n p q q' a t : ℤ)
    (h : p + q = n) (h' : p + q' = n) (ha : a + t = q) (ha' : a + t = q')
    (x : K.X p) (φ : Cochain M L t) (m : M.X a) :
    tensorDegreeProjection K L n p q h
      (ιTensorObj K L p q' n h' (x ⊗ₜ[R] (φ.v a q' ha' m))) =
        x ⊗ₜ[R] (φ.v a q ha m) := by
  have hq : q' = q := by omega
  cases hq
  exact ConcreteCategory.congr_hom (tensorDegreeProjection_self K L n p _ _) _

/-- Restrict a cochain with tensor target to a fixed degree of the left tensor factor. -/
private noncomputable def restrictTheta
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (d b n p : ℤ) :
    Cochain M (K ⊗ L) n →ₗ[R]
      (∀ i : Set.Icc (b - (n - p)) d, M.X i →ₗ[R] K.X p ⊗[R] L.X (i + (n - p))) where
  toFun z i := (tensorDegreeProjection K L (i + n) p (i + (n - p)) (by omega)).hom.comp
    (z.v i (i + n) rfl).hom
  map_add' x y := by ext i m; simp [Cochain.add_v]
  map_smul' r x := by ext i m; simp [Cochain.smul_v]

private theorem restrictTheta_apply
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (d b n p : ℤ)
    (z : Cochain M (K ⊗ L) n) (i : Set.Icc (b - (n - p)) d) (m : M.X i) :
    restrictTheta K L M d b n p z i m =
      (tensorDegreeProjection K L (i + n) p (i + (n - p)) (by omega))
        (z.v i (i + n) rfl m) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem restrictTheta_tmul_self
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (d b n p : ℤ)
    [M.IsStrictlyLE d] [L.IsStrictlyGE b]
    [∀ i, Module.Finite R (M.X i)] [∀ i, Module.Projective R (M.X i)]
    (x : K.X p) (φ : Cochain M L (n - p)) :
    restrictTheta K L M d b n p
      ((Stacks.HomComplex.TensorHomComparison.thetaDeg K L M n)
        ((ιTensorObj K (HomComplexR R M L) p (n - p) n (by omega)) (x ⊗ₜ[R] φ))) =
      tensorCochainEvaluationEquiv (K.X p) M L d b (n - p) (x ⊗ₜ[R] φ) := by
  ext i m
  rw [restrictTheta_apply, tensorCochainEvaluationEquiv_tmul,
    Stacks.HomComplex.TensorHomComparison.theta_apply]
  simp only [Stacks.HomComplex.TensorHomComparison.canonicalC_apply]
  exact tensorDegreeProjection_cochain_ι K L M (i + n) p (i + (n - p)) (i + n - p) i
    (n - p) (by omega) (by omega) rfl (by omega) x φ m

set_option backward.isDefEq.respectTransparency false in
private theorem restrictTheta_tmul_ne
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (d b n p r : ℤ) (hr : r ≠ p)
    (x : K.X r) (φ : Cochain M L (n - r)) :
    restrictTheta K L M d b n p
      ((Stacks.HomComplex.TensorHomComparison.thetaDeg K L M n)
        ((ιTensorObj K (HomComplexR R M L) r (n - r) n (by omega)) (x ⊗ₜ[R] φ))) = 0 := by
  ext i m
  rw [restrictTheta_apply, Stacks.HomComplex.TensorHomComparison.theta_apply]
  exact ConcreteCategory.congr_hom (tensorDegreeProjection_ne K L (i + n) p
    (i + (n - p)) r (i + n - r) (by omega) (by omega) hr) _

/-- A linear map out of a vanishing module, or into a vanishing tensor product, is zero. -/
private theorem apply_eq_zero_of_isZero_or
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (n p i : ℤ)
    (h : IsZero (K.X p) ∨ IsZero (M.X i) ∨ IsZero (L.X (i + n - p)))
    (f : M.X i →ₗ[R] K.X p ⊗[R] L.X (i + (n - p))) (m : M.X i) : f m = 0 := by
  rcases h with hK | hM | hL
  · exact tensor_eq_zero_of_isZero _ _ (Or.inl hK) _
  · have : Subsingleton (M.X i) := ModuleCat.isZero_iff_subsingleton.mp hM
    rw [Subsingleton.elim m 0, map_zero]
  · rw [show (i : ℤ) + n - p = i + (n - p) by omega] at hL
    exact tensor_eq_zero_of_isZero _ _ (Or.inr hL) _

private theorem restrictTheta_eq_zero
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (d b n p : ℤ)
    (h : ∀ i j, i + n = j → IsZero (K.X p) ∨ IsZero (M.X i) ∨ IsZero (L.X (j - p)))
    (z : Cochain M (K ⊗ L) n) : restrictTheta K L M d b n p z = 0 := by
  ext i m
  exact apply_eq_zero_of_isZero_or K L M n p i (h i (i + n) rfl) _ m

private theorem tensorCochain_eq_zero
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (d b n p : ℤ)
    [M.IsStrictlyLE d] [L.IsStrictlyGE b]
    [∀ i, Module.Finite R (M.X i)] [∀ i, Module.Projective R (M.X i)]
    (h : ∀ i j, i + n = j → IsZero (K.X p) ∨ IsZero (M.X i) ∨ IsZero (L.X (j - p)))
    (x : K.X p ⊗[R] Cochain M L (n - p)) : x = 0 := by
  apply (tensorCochainEvaluationEquiv (K.X p) M L d b (n - p)).injective
  rw [map_zero]
  ext i m
  exact apply_eq_zero_of_isZero_or K L M n p i (h i (i + n) rfl) _ m

set_option backward.isDefEq.respectTransparency false in
/-- The homogeneous tensor projections detect cochains under finite support bounds. -/
private theorem restrictTheta_injective
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (d b n : ℤ)
    [M.IsStrictlyLE d] [L.IsStrictlyGE b] (S : Finset ℤ)
    (hS : ∀ p ∉ S, ∀ i j, i + n = j →
      IsZero (K.X p) ∨ IsZero (M.X i) ∨ IsZero (L.X (j - p))) :
    Function.Injective (fun z : Cochain M (K ⊗ L) n ↦
      fun p ↦ restrictTheta K L M d b n p z) := by
  show Function.Injective (LinearMap.pi fun p ↦ restrictTheta K L M d b n p)
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun z hz ↦ ?_)
  apply Cochain.ext
  intro i j hij
  subst j
  by_cases hMi : IsZero (M.X i)
  · exact hMi.eq_of_src _ _
  have hid : ¬ d < i := fun h ↦ hMi (M.isZero_of_isStrictlyLE d i h)
  refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  have hp (p : ℤ) :
      (tensorDegreeProjection K L (i + n) p (i + n - p) (by omega)) (z.v i (i + n) rfl m) = 0 := by
    by_cases hi : i ∈ Set.Icc (b - (n - p)) d
    · have hh := congrArg (fun f ↦ f (⟨i, hi⟩ : Set.Icc (b - (n - p)) d) m) (congrFun hz p)
      change restrictTheta K L M d b n p z ⟨i, hi⟩ m = 0 at hh
      rw [restrictTheta_apply] at hh
      dsimp only at hh
      exact (tensorDegreeProjection_eq_zero_iff K L (i + n) p (i + (n - p)) (i + n - p)
        (by omega) (by omega) _).mp hh
    · exact tensor_eq_zero_of_isZero _ _ (Or.inr
        (L.isZero_of_isStrictlyGE b (i + n - p) (by
          simp only [Set.mem_Icc] at hi
          omega))) _
  have hsupport : ∀ p ∉ S, IsZero (K.X p) ∨ IsZero (L.X (i + n - p)) :=
    fun p hp ↦ (hS p hp i (i + n) rfl).imp_right (·.resolve_left hMi)
  have hh := ConcreteCategory.congr_hom (sum_tensorDegreeProjection K L (i + n) S hsupport)
    (z.v i (i + n) rfl m)
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id] at hh
  change (∑ p ∈ S, (ιTensorObj K L p (i + n - p) (i + n) (by omega))
    ((tensorDegreeProjection K L (i + n) p (i + n - p) (by omega))
      (z.v i (i + n) rfl m))) = z.v i (i + n) rfl m at hh
  show z.v i (i + n) rfl m = 0
  rw [← hh]
  exact Finset.sum_eq_zero fun p hpS ↦ by rw [hp p, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor–Hom comparison is bijective in each finitely supported total degree. -/
private theorem thetaDeg_bijective_of_support
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (d b n : ℤ)
    [M.IsStrictlyLE d] [L.IsStrictlyGE b]
    [∀ i, Module.Finite R (M.X i)] [∀ i, Module.Projective R (M.X i)]
    (S : Finset ℤ)
    (hS : ∀ p ∉ S, ∀ i j, i + n = j →
      IsZero (K.X p) ∨ IsZero (M.X i) ∨ IsZero (L.X (j - p))) :
    Function.Bijective (Stacks.HomComplex.TensorHomComparison.thetaDeg K L M n).hom := by
  classical
  let F := (Stacks.HomComplex.TensorHomComparison.thetaDeg K L M n).hom
  let E p := tensorCochainEvaluationEquiv (K.X p) M L d b (n - p)
  let I p := (ιTensorObj K (HomComplexR R M L) p (n - p) n (by omega)).hom
  let P p := (E p).symm.toLinearMap.comp (restrictTheta K L M d b n p)
  have hself (p : ℤ) (x : K.X p ⊗[R] Cochain M L (n - p)) : P p (F (I p x)) = x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x φ =>
      show (E p).symm (restrictTheta K L M d b n p (F (I p (x ⊗ₜ[R] φ)))) = _
      rw [restrictTheta_tmul_self]
      exact (E p).symm_apply_apply _
    | add x y hx hy => simp only [map_add, hx, hy]
  have hne (p r : ℤ) (hr : r ≠ p) (x : K.X r ⊗[R] Cochain M L (n - r)) :
      P p (F (I r x)) = 0 := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x φ =>
      show (E p).symm (restrictTheta K L M d b n p (F (I r (x ⊗ₜ[R] φ)))) = 0
      rw [restrictTheta_tmul_ne K L M d b n p r hr, map_zero]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  let G := ∑ p ∈ S, (I p).comp (P p)
  have hG (z : Cochain M (K ⊗ L) n) : G z = ∑ p ∈ S, I p (P p z) := by
    simp only [G, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  have hGF : G.comp F = LinearMap.id := by
    suffices h : ModuleCat.ofHom (G.comp F) = ModuleCat.ofHom
        (LinearMap.id (R := R) (M := (K ⊗ HomComplexR R M L).X n)) by
      exact congrArg ModuleCat.Hom.hom h
    apply mapBifunctor.hom_ext
    intro p q hpq
    obtain rfl : q = n - p := by
      change p + q = n at hpq
      omega
    refine ModuleCat.hom_ext (TensorProduct.ext (LinearMap.ext fun x ↦ LinearMap.ext fun φ ↦ ?_))
    show G (F (I p (x ⊗ₜ[R] φ))) = I p (x ⊗ₜ[R] φ)
    by_cases hp : p ∈ S
    · rw [hG, Finset.sum_eq_single p, hself]
      · intro r hr hrp
        rw [hne r p (Ne.symm hrp), map_zero]
      · exact fun h ↦ (h hp).elim
    · rw [tensorCochain_eq_zero K L M d b n p (hS p hp) (x ⊗ₜ[R] φ)]
      simp only [map_zero]
  have hFG (z : Cochain M (K ⊗ L) n) : F (G z) = z := by
    apply restrictTheta_injective K L M d b n S hS
    funext p
    apply (E p).symm.injective
    show P p (F (G z)) = P p z
    rw [hG, map_sum, map_sum]
    by_cases hp : p ∈ S
    · rw [Finset.sum_eq_single p, hself]
      · intro r hr hrp
        exact hne p r hrp _
      · exact fun h ↦ (h hp).elim
    · rw [Finset.sum_eq_zero (fun r hr ↦ hne p r (fun he ↦ hp (he ▸ hr)) _)]
      show 0 = (E p).symm (restrictTheta K L M d b n p z)
      rw [restrictTheta_eq_zero K L M d b n p (hS p hp), map_zero]
  exact ⟨Function.LeftInverse.injective (LinearMap.congr_fun hGF),
    Function.RightInverse.surjective hFG⟩

/-- A bounded-above finite-projective Hom source and bounded-below tensor factors make
the tensor--Hom comparison an isomorphism of complexes.

No flatness is asked of any of the three complexes, and no Tor amplitude is bounded: the two
lower bounds and the upper bound make each degree of both sides the same finite sum, the Hom
complex out of a complex that is unbounded below being an infinite product in each degree
otherwise. Turning this into invertibility of the derived diagonal of [stacks 0BYN] needs, in
addition, that the chain-level tensor products compute the derived ones; that is what
`isIso_diagonal_of_projective_quasiIso_theta` asks of the tensor factor. -/
public theorem isIso_theta_of_boundedBelow
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (a b d : ℤ)
    [K.IsStrictlyGE a] [L.IsStrictlyGE b] [M.IsStrictlyLE d]
    [∀ i, Module.Finite R (M.X i)] [∀ i, Module.Projective R (M.X i)] :
    IsIso (Stacks.HomComplex.TensorHomComparison.theta K L M) := by
  have (n : ℤ) : IsIso ((Stacks.HomComplex.TensorHomComparison.theta K L M).f n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    apply thetaDeg_bijective_of_support K L M d b n (Finset.Icc a (d + n - b))
    intro p hp i j hij
    by_cases hpa : p < a
    · exact Or.inl (K.isZero_of_isStrictlyGE a p hpa)
    by_cases hid : d < i
    · exact Or.inr (Or.inl (M.isZero_of_isStrictlyLE d i hid))
    exact Or.inr (Or.inr (L.isZero_of_isStrictlyGE b (j - p) (by
      simp only [Finset.mem_Icc] at hp
      omega)))
  exact HomologicalComplex.Hom.isIso_of_components _

end Stacks.DerivedTensorHomDiagonal

end
