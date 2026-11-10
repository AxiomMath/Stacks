module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.MorphismDescent

/-!
# Descent of elements of tensor products along universal effective epimorphisms

For a universal effective epimorphic family of morphisms of affine schemes, this file
identifies the pairwise pushouts of the square-zero extensions `S ⊕ (S ⊗[R] M)` and uses
morphisms out of their spectra to the affine line to show that compatible families of
elements of the base changes `S i ⊗[R] M` descend uniquely to `M`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

open scoped ChangeOfRings TensorProduct

namespace SectionsEqualizer

open Stacks.Ample (unitModule)

private lemma isPushout_baseChange_cube
    {C : Type*} [Category C]
    {R S T D E F P K : C}
    (rS : R ⟶ S) (rT : R ⟶ T) (rD : R ⟶ D)
    (sE : S ⟶ E) (tF : T ⟶ F) (dE : D ⟶ E) (dF : D ⟶ F)
    (sP : S ⟶ P) (tP : T ⟶ P)
    (eK : E ⟶ K) (fK : F ⟶ K) (pK : P ⟶ K)
    (hDS : IsPushout rS rD sE dE)
    (hDT : IsPushout rD rT dF tF)
    (hDP : IsPushout (rS ≫ sP) rD pK (dE ≫ eK))
    (hST : IsPushout rS rT sP tP)
    (hSE : sE ≫ eK = sP ≫ pK)
    (hTK : tP ≫ pK = tF ≫ fK)
    (hDE : dE ≫ eK = dF ≫ fK) :
    IsPushout dE dF eK fK := by
  have hSP : IsPushout sP sE pK eK := hDP.of_left hSE.symm hDS
  have hRT : IsPushout (rS ≫ sE) rT eK (tP ≫ pK) :=
    hST.paste_horiz hSP.flip
  have hRT' : IsPushout (rD ≫ dE) rT eK (tF ≫ fK) := by
    simpa only [hDS.w, hTK] using hRT
  exact hRT'.of_left hDE hDT

section PairwiseTensor

variable (R S T M : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [AddCommGroup M] [Module R M]

noncomputable def tensorPairLeft :
    (S ⊗[R] M) →ₗ[R] ((S ⊗[R] T) ⊗[R] M) :=
  TensorProduct.map
    (Algebra.TensorProduct.includeLeft (R := R) (A := S) (B := T)).toLinearMap
    LinearMap.id

noncomputable def tensorPairRight :
    (T ⊗[R] M) →ₗ[R] ((S ⊗[R] T) ⊗[R] M) :=
  TensorProduct.map
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)).toLinearMap
    LinearMap.id

private lemma tensorPairLeft_tmul (s : S) (m : M) :
    tensorPairLeft R S T M (s ⊗ₜ[R] m) = (s ⊗ₜ[R] (1 : T)) ⊗ₜ[R] m := by
  simp [tensorPairLeft]

private lemma tensorPairRight_tmul (t : T) (m : M) :
    tensorPairRight R S T M (t ⊗ₜ[R] m) = ((1 : S) ⊗ₜ[R] t) ⊗ₜ[R] m := by
  simp [tensorPairRight]

variable [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

@[instance_reducible]
private noncomputable def squareZeroBaseAlgebra (K : Type u) [CommRing K]
    (α : TrivSqZeroExt S (S ⊗[R] M) →+* K) : Algebra R K :=
  ((α.comp (trivSqZeroExtBaseChange R S M)).comp
    (TrivSqZeroExt.inlHom R M)).toAlgebra

private noncomputable def squareZeroLeftAlgHom (K : Type u) [CommRing K]
    (α : TrivSqZeroExt S (S ⊗[R] M) →+* K) :
    letI := squareZeroBaseAlgebra R S M K α
    S →ₐ[R] K := by
  letI := squareZeroBaseAlgebra R S M K α
  refine { toRingHom := α.comp (TrivSqZeroExt.inlHom S (S ⊗[R] M))
           commutes' := ?_ }
  intro r
  change α (TrivSqZeroExt.inl (algebraMap R S r)) =
    α (trivSqZeroExtBaseChange R S M (TrivSqZeroExt.inl r))
  rw [trivSqZeroExtBaseChange_apply]
  congr 1
  apply TrivSqZeroExt.ext <;> simp

private def squareZeroMap
    {K L : Type u} [CommRing K] [CommRing L]
    {P Q : Type u} [AddCommGroup P] [Module K P]
    [Module Kᵐᵒᵖ P] [IsCentralScalar K P]
    [AddCommGroup Q] [Module L Q]
    [Module Lᵐᵒᵖ Q] [IsCentralScalar L Q]
    (ρ : K →+* L) (η : P →ₛₗ[ρ] Q) :
    TrivSqZeroExt K P →+* TrivSqZeroExt L Q where
  toFun a := (ρ a.fst, η a.snd)
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · change ρ (a.fst + b.fst) = ρ a.fst + ρ b.fst
      exact map_add ρ _ _
    · change η (a.snd + b.snd) = η a.snd + η b.snd
      exact map_add η _ _
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · change ρ (a.fst * b.fst) = ρ a.fst * ρ b.fst
      exact map_mul ρ _ _
    · change η (a.fst • b.snd + (MulOpposite.op b.fst) • a.snd) =
        ρ a.fst • η b.snd + (MulOpposite.op (ρ b.fst)) • η a.snd
      simp [op_smul_eq_smul]

private lemma squareZeroMap_inr
    {K L : Type u} [CommRing K] [CommRing L]
    {P Q : Type u} [AddCommGroup P] [Module K P]
    [Module Kᵐᵒᵖ P] [IsCentralScalar K P]
    [AddCommGroup Q] [Module L Q]
    [Module Lᵐᵒᵖ Q] [IsCentralScalar L Q]
    (ρ : K →+* L) (η : P →ₛₗ[ρ] Q) (p : P) :
    squareZeroMap ρ η (TrivSqZeroExt.inr p) = TrivSqZeroExt.inr (η p) := by
  change (ρ (0 : K), η p) = ((0 : L), η p)
  simp

private noncomputable def tensorPairLeftRingHom : S →+* (S ⊗[R] T) :=
  Algebra.TensorProduct.includeLeftRingHom

private noncomputable def tensorPairLeftSemilinear :
    (S ⊗[R] M) →ₛₗ[tensorPairLeftRingHom R S T] ((S ⊗[R] T) ⊗[R] M) where
  toFun := tensorPairLeft R S T M
  map_add' x y := map_add (tensorPairLeft R S T M) x y
  map_smul' s z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp [smul_add, map_add, hx, hy]
    | tmul t m =>
      simp [tensorPairLeft_tmul, tensorPairLeftRingHom,
        Algebra.TensorProduct.includeLeftRingHom_apply,
        TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]

private noncomputable def tensorPairRightRingHom : T →+* (S ⊗[R] T) :=
  Algebra.TensorProduct.includeRight.toRingHom

private noncomputable def tensorPairRightSemilinear :
    (T ⊗[R] M) →ₛₗ[tensorPairRightRingHom R S T] ((S ⊗[R] T) ⊗[R] M) where
  toFun := tensorPairRight R S T M
  map_add' x y := map_add (tensorPairRight R S T M) x y
  map_smul' t z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp [smul_add, map_add, hx, hy]
    | tmul s m =>
      simp [tensorPairRight_tmul, tensorPairRightRingHom,
        Algebra.TensorProduct.includeRight_apply,
        TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]

private noncomputable def squareZeroPairLeft :
    TrivSqZeroExt S (S ⊗[R] M) →+*
      TrivSqZeroExt (S ⊗[R] T) ((S ⊗[R] T) ⊗[R] M) :=
  squareZeroMap (tensorPairLeftRingHom R S T)
    (tensorPairLeftSemilinear R S T M)

private noncomputable def squareZeroPairRight :
    TrivSqZeroExt T (T ⊗[R] M) →+*
      TrivSqZeroExt (S ⊗[R] T) ((S ⊗[R] T) ⊗[R] M) :=
  squareZeroMap (tensorPairRightRingHom R S T)
    (tensorPairRightSemilinear R S T M)

omit [Module Rᵐᵒᵖ M] [IsCentralScalar R M] in
private lemma squareZeroPairLeft_inr (z : S ⊗[R] M) :
    squareZeroPairLeft R S T M (TrivSqZeroExt.inr z) =
      TrivSqZeroExt.inr (tensorPairLeft R S T M z) :=
  squareZeroMap_inr _ _ _

omit [Module Rᵐᵒᵖ M] [IsCentralScalar R M] in
private lemma squareZeroPairRight_inr (z : T ⊗[R] M) :
    squareZeroPairRight R S T M (TrivSqZeroExt.inr z) =
      TrivSqZeroExt.inr (tensorPairRight R S T M z) :=
  squareZeroMap_inr _ _ _

omit [Module Rᵐᵒᵖ M] [IsCentralScalar R M] in
private lemma squareZeroPairLeft_inl (s : S) :
    squareZeroPairLeft R S T M (TrivSqZeroExt.inl s) =
      TrivSqZeroExt.inl (s ⊗ₜ[R] (1 : T)) := by
  apply TrivSqZeroExt.ext
  · rfl
  · change (tensorPairLeft R S T M) (0 : S ⊗[R] M) = 0
    simp

omit [Module Rᵐᵒᵖ M] [IsCentralScalar R M] in
private lemma squareZeroPairRight_inl (t : T) :
    squareZeroPairRight R S T M (TrivSqZeroExt.inl t) =
      TrivSqZeroExt.inl ((1 : S) ⊗ₜ[R] t) := by
  apply TrivSqZeroExt.ext
  · rfl
  · change (tensorPairRight R S T M) (0 : T ⊗[R] M) = 0
    simp

omit [Module Rᵐᵒᵖ M] [IsCentralScalar R M] in
private lemma squareZeroPair_inr_iff (x : S ⊗[R] M) (y : T ⊗[R] M) :
    squareZeroPairLeft R S T M (TrivSqZeroExt.inr x) =
        squareZeroPairRight R S T M (TrivSqZeroExt.inr y) ↔
      tensorPairLeft R S T M x = tensorPairRight R S T M y := by
  rw [squareZeroPairLeft_inr, squareZeroPairRight_inr]
  exact TrivSqZeroExt.inr_injective.eq_iff

private lemma squareZeroPair_comp_baseChange :
    (squareZeroPairLeft R S T M).comp (trivSqZeroExtBaseChange R S M) =
      (squareZeroPairRight R S T M).comp (trivSqZeroExtBaseChange R T M) := by
  apply RingHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · have hfst : (algebraMap R S a.fst) ⊗ₜ[R] (1 : T) =
        (1 : S) ⊗ₜ[R] (algebraMap R T a.fst) :=
      (Algebra.TensorProduct.algebraMap_apply a.fst).symm.trans
        (Algebra.TensorProduct.algebraMap_apply' a.fst)
    simp only [RingHom.comp_apply, trivSqZeroExtBaseChange_apply]
    change (tensorPairLeftRingHom R S T) (algebraMap R S a.fst) =
      (tensorPairRightRingHom R S T) (algebraMap R T a.fst)
    simp [tensorPairLeftRingHom, tensorPairRightRingHom]
  · have hsnd : (tensorPairLeft R S T M) ((1 : S) ⊗ₜ[R] a.snd) =
        (tensorPairRight R S T M) ((1 : T) ⊗ₜ[R] a.snd) := by
      rw [tensorPairLeft_tmul, tensorPairRight_tmul]
    simp only [RingHom.comp_apply, trivSqZeroExtBaseChange_apply]
    change (tensorPairLeft R S T M) ((1 : S) ⊗ₜ[R] a.snd) =
      (tensorPairRight R S T M) ((1 : T) ⊗ₜ[R] a.snd)
    exact hsnd

private lemma squareZeroPairLeft_comp_baseChange :
    (squareZeroPairLeft R S T M).comp (trivSqZeroExtBaseChange R S M) =
      trivSqZeroExtBaseChange R (S ⊗[R] T) M := by
  apply RingHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · simp only [RingHom.comp_apply, trivSqZeroExtBaseChange_apply]
    change (algebraMap R S a.fst) ⊗ₜ[R] (1 : T) =
        algebraMap R (S ⊗[R] T) a.fst
    exact (Algebra.TensorProduct.algebraMap_apply a.fst).symm
  · simp only [RingHom.comp_apply, trivSqZeroExtBaseChange_apply]
    change (tensorPairLeft R S T M) ((1 : S) ⊗ₜ[R] a.snd) =
        (1 : S ⊗[R] T) ⊗ₜ[R] a.snd
    rw [tensorPairLeft_tmul]
    rfl

private noncomputable def tensorPairLeftCancelBaseChange :
    ((S ⊗[R] T) ⊗[S] (S ⊗[R] M)) ≃ₗ[S ⊗[R] T]
      ((S ⊗[R] T) ⊗[R] M) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R S (S ⊗[R] T) (S ⊗[R] T) M

private noncomputable def squareZeroAlgEquivOfLinearEquiv
    {K P Q : Type*} [CommRing K]
    [AddCommGroup P] [Module K P] [Module Kᵐᵒᵖ P] [IsCentralScalar K P]
    [AddCommGroup Q] [Module K Q] [Module Kᵐᵒᵖ Q] [IsCentralScalar K Q]
    (e : P ≃ₗ[K] Q) : TrivSqZeroExt K P ≃ₐ[K] TrivSqZeroExt K Q :=
  AlgEquiv.ofAlgHom (TrivSqZeroExt.map e.toLinearMap)
    (TrivSqZeroExt.map e.symm.toLinearMap)
    (by
      rw [← TrivSqZeroExt.map_comp_map]
      have hc : e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id := by
        ext x
        exact e.apply_symm_apply x
      rw [hc, TrivSqZeroExt.map_id])
    (by
      rw [← TrivSqZeroExt.map_comp_map]
      have hc : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id := by
        ext x
        exact e.symm_apply_apply x
      rw [hc, TrivSqZeroExt.map_id])

private noncomputable def squareZeroPairLeftCancelBaseChange :
    TrivSqZeroExt (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] (S ⊗[R] M)) ≃ₐ[S ⊗[R] T]
      TrivSqZeroExt (S ⊗[R] T) ((S ⊗[R] T) ⊗[R] M) :=
  squareZeroAlgEquivOfLinearEquiv (tensorPairLeftCancelBaseChange R S T M)

private noncomputable def squareZeroPairPushoutHom :
    let D := TrivSqZeroExt R M
    let E := TrivSqZeroExt S (S ⊗[R] M)
    let F := TrivSqZeroExt T (T ⊗[R] M)
    let K := TrivSqZeroExt (S ⊗[R] T) ((S ⊗[R] T) ⊗[R] M)
    letI : Algebra D E := (trivSqZeroExtBaseChange R S M).toAlgebra
    letI : Algebra D F := (trivSqZeroExtBaseChange R T M).toAlgebra
    E ⊗[D] F →+* K := by
  let D := TrivSqZeroExt R M
  let E := TrivSqZeroExt S (S ⊗[R] M)
  let F := TrivSqZeroExt T (T ⊗[R] M)
  let K := TrivSqZeroExt (S ⊗[R] T) ((S ⊗[R] T) ⊗[R] M)
  letI : Algebra D E := (trivSqZeroExtBaseChange R S M).toAlgebra
  letI : Algebra D F := (trivSqZeroExtBaseChange R T M).toAlgebra
  letI : Algebra D K :=
    ((squareZeroPairLeft R S T M).comp (trivSqZeroExtBaseChange R S M)).toAlgebra
  let α : E →ₐ[D] K :=
    { toRingHom := squareZeroPairLeft R S T M
      commutes' := by intro d; rfl }
  let β : F →ₐ[D] K :=
    { toRingHom := squareZeroPairRight R S T M
      commutes' := by
        intro d
        exact congrArg (fun h : D →+* K => h d)
          (squareZeroPair_comp_baseChange R S T M).symm }
  exact (Algebra.TensorProduct.lift α β (fun _ _ => Commute.all _ _)).toRingHom

private lemma squareZeroPairPushoutHom_tmul
    (a : TrivSqZeroExt S (S ⊗[R] M))
    (b : TrivSqZeroExt T (T ⊗[R] M)) :
    let D := TrivSqZeroExt R M
    letI : Algebra D (TrivSqZeroExt S (S ⊗[R] M)) :=
      (trivSqZeroExtBaseChange R S M).toAlgebra
    letI : Algebra D (TrivSqZeroExt T (T ⊗[R] M)) :=
      (trivSqZeroExtBaseChange R T M).toAlgebra
    squareZeroPairPushoutHom R S T M (a ⊗ₜ[D] b) =
      squareZeroPairLeft R S T M a * squareZeroPairRight R S T M b := by
  simp [squareZeroPairPushoutHom, Algebra.TensorProduct.lift_tmul]

private lemma squareZeroPairPushoutHom_left
    (x : S ⊗[R] M) :
    let D := TrivSqZeroExt R M
    letI : Algebra D (TrivSqZeroExt S (S ⊗[R] M)) :=
      (trivSqZeroExtBaseChange R S M).toAlgebra
    letI : Algebra D (TrivSqZeroExt T (T ⊗[R] M)) :=
      (trivSqZeroExtBaseChange R T M).toAlgebra
    squareZeroPairPushoutHom R S T M
        (TrivSqZeroExt.inr x ⊗ₜ[D] (1 : TrivSqZeroExt T (T ⊗[R] M))) =
      TrivSqZeroExt.inr (tensorPairLeft R S T M x) := by
  dsimp only
  rw [squareZeroPairPushoutHom_tmul, squareZeroPairLeft_inr]
  simp

private lemma squareZeroPairPushoutHom_right
    (y : T ⊗[R] M) :
    let D := TrivSqZeroExt R M
    letI : Algebra D (TrivSqZeroExt S (S ⊗[R] M)) :=
      (trivSqZeroExtBaseChange R S M).toAlgebra
    letI : Algebra D (TrivSqZeroExt T (T ⊗[R] M)) :=
      (trivSqZeroExtBaseChange R T M).toAlgebra
    squareZeroPairPushoutHom R S T M
        ((1 : TrivSqZeroExt S (S ⊗[R] M)) ⊗ₜ[D] TrivSqZeroExt.inr y) =
      TrivSqZeroExt.inr (tensorPairRight R S T M y) := by
  dsimp only
  rw [squareZeroPairPushoutHom_tmul, squareZeroPairRight_inr]
  simp

private lemma squareZeroPair_isPushout :
    IsPushout
      (CommRingCat.ofHom (trivSqZeroExtBaseChange R S M))
      (CommRingCat.ofHom (trivSqZeroExtBaseChange R T M))
      (CommRingCat.ofHom (squareZeroPairLeft R S T M))
      (CommRingCat.ofHom (squareZeroPairRight R S T M)) := by
  let P := S ⊗[R] T
  let D := TrivSqZeroExt R M
  let E := TrivSqZeroExt S (S ⊗[R] M)
  let F := TrivSqZeroExt T (T ⊗[R] M)
  let K := TrivSqZeroExt P (P ⊗[R] M)
  let rS : CommRingCat.of R ⟶ CommRingCat.of S :=
    CommRingCat.ofHom (algebraMap R S)
  let rT : CommRingCat.of R ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (algebraMap R T)
  let rD : CommRingCat.of R ⟶ CommRingCat.of D :=
    CommRingCat.ofHom (TrivSqZeroExt.inlHom R M)
  let sE : CommRingCat.of S ⟶ CommRingCat.of E :=
    CommRingCat.ofHom (TrivSqZeroExt.inlHom S (S ⊗[R] M))
  let tF : CommRingCat.of T ⟶ CommRingCat.of F :=
    CommRingCat.ofHom (TrivSqZeroExt.inlHom T (T ⊗[R] M))
  let dE : CommRingCat.of D ⟶ CommRingCat.of E :=
    CommRingCat.ofHom (trivSqZeroExtBaseChange R S M)
  let dF : CommRingCat.of D ⟶ CommRingCat.of F :=
    CommRingCat.ofHom (trivSqZeroExtBaseChange R T M)
  let sP : CommRingCat.of S ⟶ CommRingCat.of P :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)
  let tP : CommRingCat.of T ⟶ CommRingCat.of P :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)
  let eK : CommRingCat.of E ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (squareZeroPairLeft R S T M)
  let fK : CommRingCat.of F ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (squareZeroPairRight R S T M)
  let pK : CommRingCat.of P ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (TrivSqZeroExt.inlHom P (P ⊗[R] M))
  have hDS : IsPushout rS rD sE dE :=
    trivSqZeroExtBaseChange_isPushout R S M
  have hDT : IsPushout rD rT dF tF :=
    (trivSqZeroExtBaseChange_isPushout R T M).flip
  have hST : IsPushout rS rT sP tP :=
    CommRingCat.isPushout_tensorProduct R S T
  have hrP : rS ≫ sP = CommRingCat.ofHom (algebraMap R P) := by
    ext r
    exact Algebra.TensorProduct.algebraMap_apply r
  have hdK : dE ≫ eK = CommRingCat.ofHom (trivSqZeroExtBaseChange R P M) :=
    congrArg CommRingCat.ofHom (squareZeroPairLeft_comp_baseChange R S T M)
  have hDP : IsPushout (rS ≫ sP) rD pK (dE ≫ eK) := by
    rw [hrP, hdK]
    exact trivSqZeroExtBaseChange_isPushout R P M
  have hSE : sE ≫ eK = sP ≫ pK := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    exact squareZeroPairLeft_inl R S T M s
  have hTK : tP ≫ pK = tF ≫ fK := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    exact (squareZeroPairRight_inl R S T M t).symm
  have hDE : dE ≫ eK = dF ≫ fK :=
    congrArg CommRingCat.ofHom (squareZeroPair_comp_baseChange R S T M)
  exact isPushout_baseChange_cube rS rT rD sE tF dE dF sP tP eK fK pK
    hDS hDT hDP hST hSE hTK hDE

private lemma squareZeroPairPushoutHom_injective :
    let D := TrivSqZeroExt R M
    let E := TrivSqZeroExt S (S ⊗[R] M)
    let F := TrivSqZeroExt T (T ⊗[R] M)
    letI : Algebra D E := (trivSqZeroExtBaseChange R S M).toAlgebra
    letI : Algebra D F := (trivSqZeroExtBaseChange R T M).toAlgebra
    Function.Injective (squareZeroPairPushoutHom R S T M) := by
  let D := TrivSqZeroExt R M
  let E := TrivSqZeroExt S (S ⊗[R] M)
  let F := TrivSqZeroExt T (T ⊗[R] M)
  let K := TrivSqZeroExt (S ⊗[R] T) ((S ⊗[R] T) ⊗[R] M)
  let : Algebra D E := (trivSqZeroExtBaseChange R S M).toAlgebra
  let : Algebra D F := (trivSqZeroExtBaseChange R T M).toAlgebra
  let h₀ := CommRingCat.isPushout_tensorProduct D E F
  let h₁ := squareZeroPair_isPushout R S T M
  let p : CommRingCat.of (E ⊗[D] F) ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (squareZeroPairPushoutHom R S T M)
  have hleft :
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := D) (A := E) (B := F))
        ≫ p = CommRingCat.ofHom (squareZeroPairLeft R S T M) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change squareZeroPairPushoutHom R S T M (a ⊗ₜ[D] (1 : F)) =
      squareZeroPairLeft R S T M a
    rw [squareZeroPairPushoutHom_tmul]
    simp
  have hright :
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := D) (A := E) (B := F)).toRingHom
        ≫ p = CommRingCat.ofHom (squareZeroPairRight R S T M) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change squareZeroPairPushoutHom R S T M ((1 : E) ⊗ₜ[D] b) =
      squareZeroPairRight R S T M b
    rw [squareZeroPairPushoutHom_tmul]
    simp
  have hp : p = (h₀.isoIsPushout _ _ h₁).hom := by
    apply h₀.hom_ext
    · rw [hleft]
      exact (h₀.inl_isoIsPushout_hom (CommRingCat.of E) (CommRingCat.of F) h₁).symm
    · rw [hright]
      exact (h₀.inr_isoIsPushout_hom (CommRingCat.of E) (CommRingCat.of F) h₁).symm
  have hip : IsIso p := by rw [hp]; infer_instance
  exact ((ConcreteCategory.isIso_iff_bijective p).mp hip).1

private lemma squareZeroPairPushout_inr_iff
    (x : S ⊗[R] M) (y : T ⊗[R] M) :
    let D := TrivSqZeroExt R M
    letI : Algebra D (TrivSqZeroExt S (S ⊗[R] M)) :=
      (trivSqZeroExtBaseChange R S M).toAlgebra
    letI : Algebra D (TrivSqZeroExt T (T ⊗[R] M)) :=
      (trivSqZeroExtBaseChange R T M).toAlgebra
    (TrivSqZeroExt.inr x ⊗ₜ[D] (1 : TrivSqZeroExt T (T ⊗[R] M))) =
      ((1 : TrivSqZeroExt S (S ⊗[R] M)) ⊗ₜ[D] TrivSqZeroExt.inr y) ↔
        tensorPairLeft R S T M x = tensorPairRight R S T M y := by
  dsimp only
  calc
    _ ↔ squareZeroPairLeft R S T M (TrivSqZeroExt.inr x) =
        squareZeroPairRight R S T M (TrivSqZeroExt.inr y) := by
      rw [squareZeroPairLeft_inr, squareZeroPairRight_inr]
      rw [← squareZeroPairPushoutHom_left, ← squareZeroPairPushoutHom_right]
      exact (squareZeroPairPushoutHom_injective R S T M).eq_iff.symm
    _ ↔ _ := squareZeroPair_inr_iff R S T M x y

end PairwiseTensor

lemma specMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (f r) :=
  congrArg (fun k : R ⟶ Γ(Spec S, ⊤) => k r)
    (Scheme.ΓSpecIso_inv_naturality f).symm

private lemma schemeIso_inv_appTop_injective {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Injective e.inv.appTop := by
  have h : e.inv.appTop ≫ e.hom.appTop = 𝟙 Γ(X, ⊤) := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]
    simp
  intro a b hab
  have ha := ConcreteCategory.congr_hom h a
  have hb := ConcreteCategory.congr_hom h b
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at ha hb
  rw [← ha, ← hb, hab]

private theorem ringElements_descend_of_isEffectiveEpiFamily_spec
    {I : Type w} (R : Type u) [CommRing R] (S : I → Type u)
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (h : StacksEffectiveEpi.IsEffectiveEpiFamily
      (fun i => AffineScheme.Spec.obj (op (CommRingCat.of (S i))))
      (fun i => AffineScheme.Spec.map
        (CommRingCat.ofHom (algebraMap R (S i))).op))
    (s : ∀ i, S i)
    (hs : ∀ i j,
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S i) (B := S j)) (s i) =
      (Algebra.TensorProduct.includeRight (R := R) (A := S i) (B := S j)).toRingHom
        (s j)) :
    ∃! r : R, ∀ i, algebraMap R (S i) r = s i := by
  let X := AffineScheme.Spec.obj (op (CommRingCat.of R))
  let U i := AffineScheme.Spec.obj (op (CommRingCat.of (S i)))
  let f i := AffineScheme.Spec.map (CommRingCat.ofHom (algebraMap R (S i))).op
  let t i : Γ((U i).obj, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (S i))).inv (s i)
  have ht : ∀ i j, (pairwiseFst X U f i j).left.appTop (t i) =
      (pairwiseSnd X U f i j).left.appTop (t j) := by
    intro i j
    let e := pullbackSpecIso R (S i) (S j)
    have he : Function.Injective e.inv.appTop := schemeIso_inv_appTop_injective e
    apply he
    change e.inv.appTop ((pullback.fst (Spec.map
        (CommRingCat.ofHom (algebraMap R (S i))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (S j))))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (S i))).inv (s i))) =
      e.inv.appTop ((pullback.snd (Spec.map
        (CommRingCat.ofHom (algebraMap R (S i))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (S j))))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (S j))).inv (s j)))
    change ((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (S i))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (S j))))).appTop ≫ e.inv.appTop)
        ((Scheme.ΓSpecIso (CommRingCat.of (S i))).inv (s i)) =
      ((pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (S i))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (S j))))).appTop ≫ e.inv.appTop)
        ((Scheme.ΓSpecIso (CommRingCat.of (S j))).inv (s j))
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
    rw [pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd]
    rw [specMap_appTop_ΓSpecIso_inv, specMap_appTop_ΓSpecIso_inv]
    exact congrArg (Scheme.ΓSpecIso (CommRingCat.of (S i ⊗[R] S j))).inv (hs i j)
  obtain ⟨a, ha, hu⟩ := ringSectionsEqualizer_of_isEffectiveEpiFamily X U f h t ht
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom a, ?_, ?_⟩
  · intro i
    have hh := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of (S i))).hom z) (ha i)
    have hfi : (AffineScheme.forgetToScheme.map (f i)).appTop =
        (Spec.map (CommRingCat.ofHom (algebraMap R (S i)))).appTop := rfl
    have hright : (Scheme.ΓSpecIso (CommRingCat.of (S i))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (S i))).inv (s i)) = s i :=
      Iso.hom_inv_id_apply _ _
    simp only [t] at hh
    rw [hfi, hright] at hh
    have hn := congrArg (fun q : Γ(Spec (CommRingCat.of R), ⊤) ⟶
        CommRingCat.of (S i) => q a)
      (Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (algebraMap R (S i))))
    calc
      algebraMap R (S i) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom a) =
          (Scheme.ΓSpecIso (CommRingCat.of (S i))).hom
            ((Spec.map (CommRingCat.ofHom (algebraMap R (S i)))).appTop a) := hn.symm
      _ = s i := hh
  · intro r hr
    have huniq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv r = a := by
      apply hu
      intro i
      change (Spec.map (CommRingCat.ofHom (algebraMap R (S i)))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) =
          (Scheme.ΓSpecIso (CommRingCat.of (S i))).inv (s i)
      rw [specMap_appTop_ΓSpecIso_inv]
      exact congrArg (Scheme.ΓSpecIso (CommRingCat.of (S i))).inv (hr i)
    have hh := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom huniq
    simpa using hh

private theorem squareZeroBaseChange_isEffectiveEpiFamily
    {I : Type w} (R : Type u) [CommRing R] (S : I → Type u)
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily
      (fun i => AffineScheme.Spec.obj (op (CommRingCat.of (S i))))
      (fun i => AffineScheme.Spec.map (CommRingCat.ofHom (algebraMap R (S i))).op))
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    StacksEffectiveEpi.IsEffectiveEpiFamily
      (fun i => AffineScheme.Spec.obj
        (op (CommRingCat.of (TrivSqZeroExt (S i) (S i ⊗[R] M)))))
      (fun i => AffineScheme.Spec.map
        (CommRingCat.ofHom (trivSqZeroExtBaseChange R (S i) M)).op) :=
  h.2 (AffineScheme.Spec.map
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom R M)).op)
    (fun i => AffineScheme.Spec.obj
      (op (CommRingCat.of (TrivSqZeroExt (S i) (S i ⊗[R] M)))))
    (fun i => AffineScheme.Spec.map
      (CommRingCat.ofHom (trivSqZeroExtBaseChange R (S i) M)).op)
    (fun i => AffineScheme.Spec.map
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom (S i) (S i ⊗[R] M))).op)
    (fun i => (trivSqZeroExtBaseChange_isPullback R (S i) M).flip)

private lemma appTop_zero {X Y : Scheme.{u}} (p : X ⟶ Y) :
    p.appTop (0 : Γ(Y, ⊤)) = 0 :=
  map_zero _

private lemma eq_zero_of_isEffectiveEpiFamily_spec
    {I : Type w} (R : CommRingCat.{u}) (S : I → CommRingCat.{u})
    (f : ∀ i, R ⟶ S i)
    (h : StacksEffectiveEpi.IsEffectiveEpiFamily
      (fun i => AffineScheme.Spec.obj (op (S i)))
      (fun i => AffineScheme.Spec.map (f i).op))
    (r : R) (hr : ∀ i, f i r = 0) : r = 0 := by
  let X := AffineScheme.Spec.obj (op R)
  let U i := AffineScheme.Spec.obj (op (S i))
  let g i := AffineScheme.Spec.map (f i).op
  obtain ⟨a, ha, hu⟩ := ringSectionsEqualizer_of_isEffectiveEpiFamily X U g h
    (fun i => 0) (fun i j => (appTop_zero _).trans (appTop_zero _).symm)
  have hz : (Scheme.ΓSpecIso R).inv r = (0 : Γ(Spec R, ⊤)) := by
    apply (hu _ ?_).trans (hu 0 (fun i => appTop_zero _)).symm
    intro i
    change (Spec.map (f i)).appTop ((Scheme.ΓSpecIso R).inv r) = 0
    rw [specMap_appTop_ΓSpecIso_inv, hr, map_zero]
  have hh := congrArg (fun z => (Scheme.ΓSpecIso R).hom z) hz
  simpa using hh

private theorem tensor_eq_zero_of_isUniversalEffectiveEpiFamily
    {I : Type w} (R : Type u) [CommRing R] (S : I → Type u)
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily
      (fun i => AffineScheme.Spec.obj (op (CommRingCat.of (S i))))
      (fun i => AffineScheme.Spec.map (CommRingCat.ofHom (algebraMap R (S i))).op))
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (m : M) (hm : ∀ i, (1 : S i) ⊗ₜ[R] m = 0) : m = 0 := by
  let D := TrivSqZeroExt R M
  let E i := TrivSqZeroExt (S i) (S i ⊗[R] M)
  let θ (i) : D →+* E i := trivSqZeroExtBaseChange R (S i) M
  have hD : StacksEffectiveEpi.IsEffectiveEpiFamily
      (fun i => AffineScheme.Spec.obj (op (CommRingCat.of (E i))))
      (fun i => AffineScheme.Spec.map (CommRingCat.ofHom (θ i)).op) :=
    squareZeroBaseChange_isEffectiveEpiFamily R S h M
  have hz : (TrivSqZeroExt.inr m : D) = 0 :=
    eq_zero_of_isEffectiveEpiFamily_spec (CommRingCat.of D)
      (fun i => CommRingCat.of (E i)) (fun i => CommRingCat.ofHom (θ i)) hD
      (TrivSqZeroExt.inr m) (by
        intro i
        change trivSqZeroExtBaseChange R (S i) M (TrivSqZeroExt.inr m) = 0
        rw [trivSqZeroExtBaseChange_apply]
        apply TrivSqZeroExt.ext
        · simp
        · simpa using hm i)
  exact congrArg TrivSqZeroExt.snd hz

/-- A universal effective epimorphic family of affine schemes, as a family of spectra of the
rings of global sections with the structure maps induced by `algebraMap`. -/
private theorem isUniversalEffectiveEpiFamily_spec_algebraMap
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f) :
    letI : ∀ i, Algebra Γ(X.obj, ⊤) Γ((U i).obj, ⊤) :=
      fun i => (f i).hom.appTop.hom.toAlgebra
    StacksEffectiveEpi.IsUniversalEffectiveEpiFamily
      (fun i => AffineScheme.Spec.obj (op (CommRingCat.of Γ((U i).obj, ⊤))))
      (fun i => AffineScheme.Spec.map
        (CommRingCat.ofHom (algebraMap Γ(X.obj, ⊤) Γ((U i).obj, ⊤))).op) := by
  convert isUniversalEffectiveEpiFamily_spec X U f h using 1
  funext i
  rfl

theorem tensor_eq_zero_of_universalEffectiveEpiFamily_affine
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f)
    (M : Type u) [AddCommGroup M] [Module Γ(X.obj, ⊤) M]
    [Module Γ(X.obj, ⊤)ᵐᵒᵖ M] [IsCentralScalar Γ(X.obj, ⊤) M]
    (m : M)
    (hm : ∀ i, (1 : Γ((U i).obj, ⊤)) ⊗ₜ[Γ(X.obj, ⊤),(f i).hom.appTop.hom] m = 0) :
    m = 0 := by
  let R := Γ(X.obj, ⊤)
  let S (i : I) := Γ((U i).obj, ⊤)
  let : ∀ i, Algebra R (S i) := fun i => (f i).hom.appTop.hom.toAlgebra
  exact tensor_eq_zero_of_isUniversalEffectiveEpiFamily
    (R : Type u) (fun i : I => (S i : Type u))
    (isUniversalEffectiveEpiFamily_spec_algebraMap X U f h) M m hm

private theorem tensorElements_descend_of_isUniversalEffectiveEpiFamily
    {I : Type w} (R : Type u) [CommRing R] (S : I → Type u)
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily
      (fun i => AffineScheme.Spec.obj (op (CommRingCat.of (S i))))
      (fun i => AffineScheme.Spec.map
        (CommRingCat.ofHom (algebraMap R (S i))).op))
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (s : ∀ i, S i ⊗[R] M)
    (hs : ∀ i j,
      tensorPairLeft R (S i) (S j) M (s i) =
        tensorPairRight R (S i) (S j) M (s j)) :
    ∃! m : M, ∀ i, (1 : S i) ⊗ₜ[R] m = s i := by
  let D := TrivSqZeroExt R M
  let E i := TrivSqZeroExt (S i) (S i ⊗[R] M)
  let θ i : D →+* E i := trivSqZeroExtBaseChange R (S i) M
  let : ∀ i, Algebra D (E i) := fun i => (θ i).toAlgebra
  have hD : StacksEffectiveEpi.IsEffectiveEpiFamily
      (fun i => AffineScheme.Spec.obj (op (CommRingCat.of (E i))))
      (fun i => AffineScheme.Spec.map (CommRingCat.ofHom (θ i)).op) :=
    squareZeroBaseChange_isEffectiveEpiFamily R S h M
  have hcompat : ∀ i j,
      (Algebra.TensorProduct.includeLeftRingHom (R := D) (A := E i) (B := E j))
          (TrivSqZeroExt.inr (s i)) =
        (Algebra.TensorProduct.includeRight (R := D) (A := E i) (B := E j)).toRingHom
          (TrivSqZeroExt.inr (s j)) := by
    intro i j
    exact (squareZeroPairPushout_inr_iff R (S i) (S j) M (s i) (s j)).2 (hs i j)
  obtain ⟨d, hd, hu⟩ := ringElements_descend_of_isEffectiveEpiFamily_spec
    D E hD (fun i => TrivSqZeroExt.inr (s i)) hcompat
  have hfst : ∀ i, algebraMap R (S i) d.fst = 0 := by
    intro i
    have hi := congrArg TrivSqZeroExt.fst (hd i)
    change (θ i d).fst = 0 at hi
    rw [trivSqZeroExtBaseChange_apply] at hi
    exact hi
  have hzero : d.fst = 0 :=
    eq_zero_of_isEffectiveEpiFamily_spec (CommRingCat.of R)
      (fun i => CommRingCat.of (S i))
      (fun i => CommRingCat.ofHom (algebraMap R (S i)))
      h.isEffectiveEpiFamily d.fst hfst
  have hdinr : d = TrivSqZeroExt.inr d.snd := by
    apply TrivSqZeroExt.ext
    · exact hzero
    · rfl
  refine ⟨d.snd, ?_, ?_⟩
  · intro i
    have hi := congrArg TrivSqZeroExt.snd (hd i)
    change (θ i d).snd = s i at hi
    rw [hdinr, trivSqZeroExtBaseChange_apply] at hi
    simpa using hi
  · intro m hm
    have hm' : (TrivSqZeroExt.inr m : D) = d := by
      apply hu
      intro i
      change θ i (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (s i)
      rw [trivSqZeroExtBaseChange_apply]
      apply TrivSqZeroExt.ext
      · simp
      · exact hm i
    have := congrArg TrivSqZeroExt.snd hm'
    simpa using this

theorem tensorElements_descend_of_universalEffectiveEpiFamily_affine
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f)
    (M : Type u) [AddCommGroup M] [Module Γ(X.obj, ⊤) M]
    [Module Γ(X.obj, ⊤)ᵐᵒᵖ M] [IsCentralScalar Γ(X.obj, ⊤) M] :
    letI : ∀ i, Algebra Γ(X.obj, ⊤) Γ((U i).obj, ⊤) :=
      fun i => (f i).hom.appTop.hom.toAlgebra
    ∀ (s : ∀ i, Γ((U i).obj, ⊤) ⊗[Γ(X.obj, ⊤)] M),
    (∀ i j,
      tensorPairLeft Γ(X.obj, ⊤) Γ((U i).obj, ⊤) Γ((U j).obj, ⊤) M
        (s i) =
      tensorPairRight Γ(X.obj, ⊤) Γ((U i).obj, ⊤) Γ((U j).obj, ⊤) M
        (s j)) →
    ∃! m : M, ∀ i,
      (1 : Γ((U i).obj, ⊤)) ⊗ₜ[Γ(X.obj, ⊤)] m = s i := by
  let R := Γ(X.obj, ⊤)
  let S (i : I) := Γ((U i).obj, ⊤)
  let : ∀ i, Algebra R (S i) := fun i => (f i).hom.appTop.hom.toAlgebra
  intro s hs
  exact tensorElements_descend_of_isUniversalEffectiveEpiFamily
    (R : Type u) (fun i : I => (S i : Type u))
    (isUniversalEffectiveEpiFamily_spec_algebraMap X U f h) M s hs

end SectionsEqualizer

end AlgebraicGeometry
