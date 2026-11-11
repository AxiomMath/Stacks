module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.AlgebraicTopology.MooreComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Dold-Kan for cosimplicial objects

Let `A` be an abelian category. The *Moore cochain complex* `s(U)` of a cosimplicial object `U` of
`A` is `U₀ → U₁ → U₂ → ⋯`, concentrated in nonnegative degrees, with `s(U)ⁿ = Uₙ` and differential
`dⁿ = ∑_{i=0}^{n+1} (-1)ⁱ δⁿ⁺¹ᵢ`; this is Mathlib's
`AlgebraicTopology.alternatingCofaceMapComplex A`. The *normalized cochain complex* `Q(U)` is its
quotient: `Q(U)⁰ = U₀` and `Q(U)ⁿ` is the cokernel of the map `⊕_{i=0}^{n-1} Uₙ₋₁ → Uₙ` with
components the cofaces `δⁿᵢ`, `i < n`, so that the projections `Uₙ = s(U)ⁿ → Q(U)ⁿ` form a morphism
of cochain complexes whose differential is induced by `(-1)ⁿ⁺¹ δⁿ⁺¹ₙ₊₁`.

The statement below is the dual of the Dold-Kan theorem: `s` is exact, `s(U)` decomposes
functorially as `D(U) ⊕ Q(U)`, the projection `s(U) → Q(U)` is a quasi-isomorphism, and `Q` is an
exact equivalence `CoSimp(A) ≌ CoCh_{≥0}(A)`.

## Main results

* `AlgebraicTopology.exists_normalizedCochainComplex`: the six assertions of the dual Dold-Kan
  theorem — exactness of the Moore cochain complex functor `s`, the existence of the normalized
  cochain complex functor `Q` together with the canonical morphism `s ⟶ Q`, the functorial
  splitting `s = D ⊕ Q`, exactness of `Q`, the fact that `s(U) → Q(U)` is a quasi-isomorphism, and
  that `Q` is an equivalence of categories.

## References

* [Stacks, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
* [Stacks, Tag 0195](https://stacks.math.columbia.edu/tag/0195)
* [Stacks, Tag 019A](https://stacks.math.columbia.edu/tag/019A)
-/

open CategoryTheory Limits Simplicial Opposite

universe v u

namespace AlgebraicTopology

section DualDoldKan

variable (A : Type u) [Category.{v} A] [Abelian A]

/-! ### Exactness of the Moore cochain complex functor -/

private lemma additive_alternatingCofaceMapComplex :
    (alternatingCofaceMapComplex A).Additive where

attribute [local instance] additive_alternatingCofaceMapComplex

private lemma preservesLimit_parallelPair_cofaceMap {U V : CosimplicialObject A} (f : U ⟶ V) :
    PreservesLimit (parallelPair f 0) (alternatingCofaceMapComplex A) where
  preserves {_} hc := ⟨HomologicalComplex.isLimitOfEval _ _ fun n =>
    ((evaluation_preservesLimit_of_hasKernel_app f ⦋n⦌).preserves hc).some⟩

private lemma preservesColimit_parallelPair_cofaceMap {U V : CosimplicialObject A} (f : U ⟶ V) :
    PreservesColimit (parallelPair f 0) (alternatingCofaceMapComplex A) where
  preserves {_} hc := ⟨HomologicalComplex.isColimitOfEval _ _ fun n =>
    ((evaluation_preservesColimit_of_hasCokernel_app f ⦋n⦌).preserves hc).some⟩

private lemma preservesFiniteLimits_alternatingCofaceMapComplex :
    PreservesFiniteLimits (alternatingCofaceMapComplex A) := by
  have : ∀ {U V : CosimplicialObject A} (f : U ⟶ V),
      PreservesLimit (parallelPair f 0) (alternatingCofaceMapComplex A) :=
    fun f => preservesLimit_parallelPair_cofaceMap A f
  exact Functor.preservesFiniteLimits_of_preservesKernels _

private lemma preservesFiniteColimits_alternatingCofaceMapComplex :
    PreservesFiniteColimits (alternatingCofaceMapComplex A) := by
  have : ∀ {U V : CosimplicialObject A} (f : U ⟶ V),
      PreservesColimit (parallelPair f 0) (alternatingCofaceMapComplex A) :=
    fun f => preservesColimit_parallelPair_cofaceMap A f
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

/-! ### Dualization -/

/-- The dualization of functors from simplicial objects of `Aᵒᵖ` to chain complexes in `Aᵒᵖ` into
functors from cosimplicial objects of `A` to cochain complexes in `A`. It is contravariant. -/
@[implicit_reducible]
private def dualize :
    (SimplicialObject Aᵒᵖ ⥤ ChainComplex Aᵒᵖ ℕ)ᵒᵖ ⥤
      (CosimplicialObject A ⥤ CochainComplex A ℕ) where
  obj F := ((cosimplicialSimplicialEquiv A).functor ⋙ F.unop).rightOp ⋙
    HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)
  map α := Functor.whiskerRight
    (NatTrans.rightOp (Functor.whiskerLeft (cosimplicialSimplicialEquiv A).functor α.unop)) _
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Precomposition of a cosimplicial object with the involution `SimplexCategory.rev`. -/
@[implicit_reducible]
private def revFunctor : CosimplicialObject A ⥤ CosimplicialObject A :=
  (Functor.whiskeringLeft _ _ A).obj SimplexCategory.rev

omit [Abelian A] in
private lemma revFunctor_obj_map (U : CosimplicialObject A) {x y : SimplexCategory}
    (f : x ⟶ y) : ((revFunctor A).obj U).map f = U.map (SimplexCategory.rev.map f) := by
  simp [revFunctor]

omit [Abelian A] in
private lemma revFunctor_δ (U : CosimplicialObject A) {n : ℕ} (i : Fin (n + 2)) :
    ((revFunctor A).obj U).δ i = U.δ i.rev := by
  rw [CosimplicialObject.δ, CosimplicialObject.δ, revFunctor_obj_map, SimplexCategory.rev_map_δ]

omit [Abelian A] in
private lemma isEquivalence_revFunctor : (revFunctor A).IsEquivalence := by
  have h : (SimplexCategory.revEquivalence.congrLeft (E := A)).functor = revFunctor A := rfl
  rw [← h]; infer_instance

/-- The normalized cochain complex functor `Q`. -/
@[implicit_reducible]
private noncomputable def normalizedCochainComplexFunctor :
    CosimplicialObject A ⥤ CochainComplex A ℕ :=
  revFunctor A ⋙ (dualize A).obj (op (normalizedMooreComplex Aᵒᵖ))

/-! ### The sign twist -/

/-- The signs `(-1)^{n(n+1)/2}` comparing `s(U)` with `s(U ∘ rev)`. -/
private def sign : ℕ → ℤ := fun n => Nat.rec (1 : ℤ) (fun k s => (-1) ^ (k + 1) * s) n

private lemma sign_zero : sign 0 = 1 := rfl

private lemma sign_succ (n : ℕ) : sign (n + 1) = (-1) ^ (n + 1) * sign n := rfl

private lemma sign_mul_self (n : ℕ) : sign n * sign n = 1 := by
  induction n with
  | zero => rw [sign_zero]; norm_num
  | succ n ih =>
      rw [sign_succ, mul_mul_mul_comm, ← pow_add, ih, mul_one]
      exact (Even.add_self (n + 1)).neg_one_pow

/-- Multiplication by a scalar `z` with `z * z = 1` is an automorphism. -/
private def zsmulIso {X : A} (z : ℤ) (hz : z * z = 1) : X ≅ X where
  hom := z • 𝟙 X
  inv := z • 𝟙 X
  hom_inv_id := by
    simp [smul_smul, hz]
  inv_hom_id := by
    simp [smul_smul, hz]

private lemma alternatingCofaceMapComplex_d (V : CosimplicialObject A) (n : ℕ) :
    ((alternatingCofaceMapComplex A).obj V).d n (n + 1) =
      AlternatingCofaceMapComplex.objD V n := by
  simp [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj]

private lemma objD_revFunctor (U : CosimplicialObject A) (n : ℕ) :
    AlternatingCofaceMapComplex.objD ((revFunctor A).obj U) n
      = (-1 : ℤ) ^ (n + 1) • AlternatingCofaceMapComplex.objD U n := by
  simp only [AlternatingCofaceMapComplex.objD, revFunctor_δ, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  have hsum : ((i.rev : ℕ)) + ((i : ℕ)) = n + 1 := by
    rw [Fin.val_rev]; omega
  have h1 : ((-1 : ℤ)) ^ ((i.rev : ℕ)) * (-1) ^ ((i : ℕ)) = (-1) ^ (n + 1) := by
    rw [← pow_add, hsum]
  have h2 : ((-1 : ℤ)) ^ ((i.rev : ℕ)) * (-1) ^ ((i.rev : ℕ)) = 1 := by
    rw [← pow_add]; exact (Even.add_self _).neg_one_pow
  have key : ((-1 : ℤ)) ^ (n + 1) * (-1) ^ ((i.rev : ℕ)) = (-1) ^ ((i : ℕ)) := by
    rw [← h1, mul_comm ((-1 : ℤ) ^ ((i.rev : ℕ))) ((-1 : ℤ) ^ ((i : ℕ))), mul_assoc, h2, mul_one]
  rw [Fin.revPerm_apply]
  congr 1
  rw [key]

/-- Multiplication by a scalar on the left of a composite with an identity. -/
private lemma zsmul_id_comp {X Y : A} (z : ℤ) (g : X ⟶ Y) : (z • 𝟙 X) ≫ g = z • g := by
  rw [Preadditive.zsmul_comp, Category.id_comp]

/-- Multiplication by a scalar on the right of a composite with an identity. -/
private lemma comp_zsmul_id {X Y : A} (z : ℤ) (g : X ⟶ Y) : g ≫ (z • 𝟙 Y) = z • g := by
  rw [Preadditive.comp_zsmul, Category.comp_id]

/-- The commutation of the sign twist with the differentials. -/
private lemma sign_comm (U : CosimplicialObject A) (n : ℕ)
    (dL dR : U.obj ⦋n⦌ ⟶ U.obj ⦋n + 1⦌) (hd : dL = (-1 : ℤ) ^ (n + 1) • dR) :
    (sign n • 𝟙 (U.obj ⦋n⦌)) ≫ dL = dR ≫ (sign (n + 1) • 𝟙 (U.obj ⦋n + 1⦌)) := by
  rw [zsmul_id_comp, comp_zsmul_id, hd, smul_smul, sign_succ, mul_comm]

omit [Abelian A] in
/-- Cancelling identities on both sides of an equation of morphisms. -/
private lemma comp_id_eq_id_comp {X Y : A} (f g : X ⟶ Y) (h : f = g) :
    f ≫ 𝟙 Y = 𝟙 X ≫ g := by rw [Category.id_comp, Category.comp_id, h]

/-- Multiplication by a scalar, with two identities inserted. -/
private lemma zsmul_id_comp_id_comp {X Y : A} (z : ℤ) (g : X ⟶ Y) :
    (z • 𝟙 X) ≫ (𝟙 X ≫ g) = z • g := by rw [Category.id_comp, zsmul_id_comp]

/-- Cancelling scalar multiples of identities on both sides of an equation of morphisms. -/
private lemma comp_zsmul_id_eq {X Y : A} (f g : X ⟶ Y) (z : ℤ) (h : f = g) :
    f ≫ (z • 𝟙 Y) = (z • 𝟙 X) ≫ g := by rw [comp_zsmul_id, zsmul_id_comp, h]

omit [Abelian A] in
/-- Transport of `IsIso` along an equality of morphisms. -/
private lemma isIso_of_eq {X Y : A} {f g : X ⟶ Y} (h : f = g) (hg : IsIso g) : IsIso f := by
  rw [h]; exact hg

/-- Transport of `QuasiIso` along an equality of morphisms of cochain complexes. -/
private lemma quasiIso_of_eq {K L : CochainComplex A ℕ} {f g : K ⟶ L} (h : f = g)
    (hg : QuasiIso g) : QuasiIso f := by rw [h]; exact hg

/-- A composite with a scalar multiple vanishes as soon as the composite does. -/
private lemma comp_zsmul_eq_zero {W X Y : A} (g : W ⟶ X) (f : X ⟶ Y) (z : ℤ) (h : g ≫ f = 0) :
    g ≫ (z • f) = 0 := by rw [Preadditive.comp_zsmul, h, smul_zero]

omit [Abelian A] in
/-- Transport of a universal property along an equality of morphisms. -/
private lemma existsUnique_congr_left {X Q Z : A} {p q : X ⟶ Q} (hpq : p = q) (g : X ⟶ Z)
    (h : ∃! k, p ≫ k = g) : ∃! k, q ≫ k = g := by rw [← hpq]; exact h

/-- The comparison `s(U) ≅ s(U ∘ rev)`, the identity in degree `n` up to the sign
`(-1)^{n(n+1)/2}`. -/
private noncomputable def signIso :
    alternatingCofaceMapComplex A ≅ revFunctor A ⋙ alternatingCofaceMapComplex A :=
  NatIso.ofComponents
    (fun U => HomologicalComplex.Hom.isoOfComponents
      (fun n => zsmulIso A (sign n) (sign_mul_self n))
      (fun i j hij => by
        obtain rfl : i + 1 = j := hij
        have h : ((revFunctor A ⋙ alternatingCofaceMapComplex A).obj U).d i (i + 1)
            = (-1 : ℤ) ^ (i + 1) • ((alternatingCofaceMapComplex A).obj U).d i (i + 1) :=
          (alternatingCofaceMapComplex_d A ((revFunctor A).obj U) i).trans
            ((objD_revFunctor A U i).trans
              (congrArg (fun d => (-1 : ℤ) ^ (i + 1) • d)
                (alternatingCofaceMapComplex_d A U i)).symm)
        exact sign_comm A U i _ _ h))
    (fun f => by
      ext n
      exact comp_zsmul_id_eq A _ _ (sign n) rfl)

private lemma dualS_d (U : CosimplicialObject A) (n : ℕ) :
    (((dualize A).obj (op (alternatingFaceMapComplex Aᵒᵖ))).obj U).d n (n + 1)
      = AlternatingCofaceMapComplex.objD U n := by
  rw [AlternatingCofaceMapComplex.d_eq_unop_d]
  exact congrArg Quiver.Hom.unop
    (alternatingFaceMapComplex_obj_d ((cosimplicialSimplicialEquiv A).functor.obj (op U)) n)

/-- The Moore cochain complex functor is the dualization of Mathlib's alternating face map complex
functor for `Aᵒᵖ`. -/
private noncomputable def isoDualS :
    alternatingCofaceMapComplex A ≅ (dualize A).obj (op (alternatingFaceMapComplex Aᵒᵖ)) :=
  NatIso.ofComponents
    (fun U => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
      (fun i j hij => by
        obtain rfl : i + 1 = j := hij
        have h : (((dualize A).obj (op (alternatingFaceMapComplex Aᵒᵖ))).obj U).d i (i + 1)
            = ((alternatingCofaceMapComplex A).obj U).d i (i + 1) := by
          rw [dualS_d, alternatingCofaceMapComplex_d]
        exact (Category.id_comp _).trans (h.trans (Category.comp_id _).symm)))
    (fun f => by
      ext n
      exact comp_id_eq_id_comp A _ _ rfl)

/-- The projection `π : s ⟶ Q`. -/
private noncomputable def pi :
    alternatingCofaceMapComplex A ⟶ normalizedCochainComplexFunctor A :=
  (signIso A).hom ≫ Functor.whiskerLeft (revFunctor A)
    ((isoDualS A).hom ≫ (dualize A).map (inclusionOfMooreComplex Aᵒᵖ).op)

/-- The simplicial object of `Aᵒᵖ` whose normalized Moore complex is `Q(U)`: the dual of `U`
precomposed with `SimplexCategory.rev`. -/
@[implicit_reducible]
private def dualRev (U : CosimplicialObject A) : SimplicialObject Aᵒᵖ :=
  ((revFunctor A).obj U).op

private lemma pi_app_f (U : CosimplicialObject A) (n : ℕ) :
    ((pi A).app U).f n
      = sign n • ((NormalizedMooreComplex.objX (dualRev A U) n).arrow).unop := by
  have h : ((pi A).app U).f n = (sign n • 𝟙 (U.obj ⦋n⦌)) ≫ (𝟙 (U.obj ⦋n⦌) ≫
      ((NormalizedMooreComplex.objX (dualRev A U) n).arrow).unop) := rfl
  exact h.trans (zsmul_id_comp_id_comp A (sign n) _)

/-! ### The degreewise description of `π` -/

private lemma existsUnique_zsmul {X Q Z : A} (p : X ⟶ Q) (z : ℤ) (hz : z * z = 1) (g : X ⟶ Z)
    (h : ∃! k : Q ⟶ Z, p ≫ k = g) : ∃! k : Q ⟶ Z, (z • p) ≫ k = g := by
  obtain ⟨k₀, hk₀, huniq⟩ := h
  refine ⟨z • k₀, ?_, ?_⟩
  · beta_reduce
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, hz, one_smul, hk₀]
  · intro k hk
    have h1 : p ≫ (z • k) = g := by
      rw [Preadditive.comp_zsmul, ← Preadditive.zsmul_comp, hk]
    rw [← huniq _ h1, smul_smul, hz, one_smul]

omit [Abelian A] in
private lemma op_δ (V : CosimplicialObject A) {n : ℕ} (i : Fin (n + 2)) :
    SimplicialObject.δ V.op i = (V.δ i).op := by
  rw [SimplicialObject.δ_def, Functor.op_map, Quiver.Hom.unop_op, CosimplicialObject.δ]

omit [Abelian A] in
private lemma dualRev_δ (U : CosimplicialObject A) {n : ℕ} (i : Fin (n + 1)) :
    (dualRev A U).δ i.succ = (U.δ i.rev.castSucc).op := by
  dsimp only [dualRev]
  rw [op_δ, revFunctor_δ, Fin.rev_succ]

/-- The arrow of Mathlib's normalized Moore subobject kills the faces `δ i.succ`. -/
private lemma arrow_comp_δ (X : SimplicialObject Aᵒᵖ) (n : ℕ) (i : Fin (n + 1)) :
    (NormalizedMooreComplex.objX X (n + 1)).arrow ≫ X.δ i.succ = 0 := by
  rw [NormalizedMooreComplex.objX_add_one,
    ← Subobject.factorThru_arrow _ _
      (Subobject.finset_inf_arrow_factors Finset.univ _ i (Finset.mem_univ i)),
    Category.assoc, kernelSubobject_arrow_comp, comp_zero]

/-- The `unop` of the arrow of Mathlib's normalized Moore subobject, in degree `n + 1`, has the
universal property of the cokernel of the family of cofaces `δ i.castSucc`, `i ≤ n`. -/
private lemma existsUnique_arrow_unop (U : CosimplicialObject A) (n : ℕ) {Z : A}
    (g : U.obj ⦋n + 1⦌ ⟶ Z)
    (hg : ∀ i : Fin (n + 1), U.δ i.castSucc ≫ g = 0) :
    ∃! k, ((NormalizedMooreComplex.objX (dualRev A U) (n + 1)).arrow).unop ≫ k = g := by
  have hfac : (NormalizedMooreComplex.objX (dualRev A U) (n + 1)).Factors g.op := by
    rw [NormalizedMooreComplex.objX_add_one]
    refine (Subobject.finset_inf_factors _).mpr fun i _ => kernelSubobject_factors _ _ ?_
    rw [dualRev_δ]
    exact congrArg Quiver.Hom.op (hg i.rev)
  have hw : ((NormalizedMooreComplex.objX (dualRev A U) (n + 1)).arrow).unop ≫
      (Subobject.factorThru _ g.op hfac).unop = g :=
    congrArg Quiver.Hom.unop (Subobject.factorThru_arrow _ g.op hfac)
  refine ⟨_, hw, fun y hy => ?_⟩
  exact (cancel_epi ((NormalizedMooreComplex.objX (dualRev A U) (n + 1)).arrow).unop).mp
    (hy.trans hw.symm)

private lemma isIso_pi_app_f_zero (U : CosimplicialObject A) : IsIso (((pi A).app U).f 0) := by
  have h : ((pi A).app U).f 0 = ((NormalizedMooreComplex.objX (dualRev A U) 0).arrow).unop :=
    (pi_app_f A U 0).trans (by rw [sign_zero, one_smul])
  refine isIso_of_eq A h ?_
  exact inferInstanceAs (IsIso ((⊤ : Subobject ((dualRev A U).obj (op ⦋0⦌))).arrow).unop)

private lemma δ_comp_arrow_unop (U : CosimplicialObject A) (n : ℕ) (i : Fin (n + 1)) :
    U.δ i.castSucc ≫ ((NormalizedMooreComplex.objX (dualRev A U) (n + 1)).arrow).unop = 0 := by
  have h : (NormalizedMooreComplex.objX (dualRev A U) (n + 1)).arrow ≫
      (dualRev A U).δ i.rev.succ = 0 := arrow_comp_δ A _ n i.rev
  rw [dualRev_δ, Fin.rev_rev] at h
  exact congrArg Quiver.Hom.unop h

private lemma δ_comp_pi (U : CosimplicialObject A) (n : ℕ) (i : Fin (n + 1)) :
    U.δ i.castSucc ≫ ((pi A).app U).f (n + 1) = 0 :=
  (congrArg (fun q => U.δ i.castSucc ≫ q) (pi_app_f A U (n + 1))).trans
    (comp_zsmul_eq_zero A _ _ (sign (n + 1)) (δ_comp_arrow_unop A U n i))

/-- A morphism with the universal property of a cokernel of `g` is a cokernel of `g`. -/
private lemma exists_iso_cokernel {X Y P : A} (g : X ⟶ Y) (p : Y ⟶ P) (hgp : g ≫ p = 0)
    (h : ∀ {Z : A} (u : Y ⟶ Z), g ≫ u = 0 → ∃! k, p ≫ k = u) :
    ∃ e : cokernel g ≅ P, cokernel.π g ≫ e.hom = p := by
  obtain ⟨k, hk, -⟩ := h (cokernel.π g) (cokernel.condition g)
  refine ⟨⟨cokernel.desc g p hgp, k, ?_, ?_⟩, cokernel.π_desc g p hgp⟩
  · rw [← cancel_epi (cokernel.π g), ← Category.assoc, cokernel.π_desc, hk, Category.comp_id]
  · exact (h p hgp).unique (by rw [← Category.assoc, hk, cokernel.π_desc])
      (Category.comp_id p)

/-- A map out of the sum of the cofaces vanishes iff it vanishes on each coface. -/
private lemma sigma_desc_comp_eq_zero_iff (n : ℕ) (U : CosimplicialObject A) {Z : A}
    (u : U.obj ⦋n + 1⦌ ⟶ Z) :
    (Sigma.desc (f := fun _ : Fin (n + 1) => U.obj ⦋n⦌) fun i => U.δ i.castSucc) ≫ u = 0 ↔
      ∀ i : Fin (n + 1), U.δ i.castSucc ≫ u = 0 := by
  simp [Sigma.hom_ext_iff]

private lemma key_cokernel (U : CosimplicialObject A) (n : ℕ) {Z : A}
    (u : U.obj ⦋n + 1⦌ ⟶ Z) (hu : ∀ i : Fin (n + 1), U.δ i.castSucc ≫ u = 0) :
    ∃! k, ((pi A).app U).f (n + 1) ≫ k = u :=
  existsUnique_congr_left A (pi_app_f A U (n + 1)).symm u
    (existsUnique_zsmul A _ (sign (n + 1)) (sign_mul_self (n + 1)) u
      (existsUnique_arrow_unop A U n u hu))

private lemma cokernel_pi (U : CosimplicialObject A) (n : ℕ) :
    ∃ e : cokernel (Sigma.desc (f := fun _ : Fin (n + 1) => U.obj ⦋n⦌)
        fun i => U.δ i.castSucc) ≅ ((normalizedCochainComplexFunctor A).obj U).X (n + 1),
      cokernel.π _ ≫ e.hom = ((pi A).app U).f (n + 1) := by
  refine exists_iso_cokernel A _ _ ((sigma_desc_comp_eq_zero_iff A n U _).mpr (δ_comp_pi A U n)) ?_
  intro Z u hu
  exact key_cokernel A U n u ((sigma_desc_comp_eq_zero_iff A n U u).mp hu)

/-! ### The splitting, the quasi-isomorphism and the equivalence -/

/-- A section of `g` gives a section of `e.hom ≫ g` for an isomorphism `e`. -/
private lemma comp_inv_comp_hom_comp {D : Type*} [Category D] {X Y Z : D} (e : X ≅ Y) (g : Y ⟶ Z)
    (t : Z ⟶ Y) (ht : t ≫ g = 𝟙 Z) : (t ≫ e.inv) ≫ (e.hom ≫ g) = 𝟙 Z := by
  rw [Category.assoc, Iso.inv_hom_id_assoc, ht]

private lemma isSplitMono_inclusion : IsSplitMono (inclusionOfMooreComplex Aᵒᵖ) := by
  obtain ⟨D, e, he⟩ := exists_degenerateComplex Aᵒᵖ
  exact ⟨⟨e.inv ≫ biprod.fst, by rw [← he]; simp⟩⟩

private lemma isSplitEpi_pi : IsSplitEpi (pi A) := by
  have := isSplitMono_inclusion A
  have : IsSplitEpi (Functor.whiskerLeft (revFunctor A)
      ((isoDualS A).hom ≫ (dualize A).map (inclusionOfMooreComplex Aᵒᵖ).op)) := by
    have h : Functor.whiskerLeft (revFunctor A)
        ((isoDualS A).hom ≫ (dualize A).map (inclusionOfMooreComplex Aᵒᵖ).op)
        = ((Functor.whiskeringLeft (CosimplicialObject A) (CosimplicialObject A)
            (CochainComplex A ℕ)).obj (revFunctor A)).map
          ((isoDualS A).hom ≫ (dualize A).map (inclusionOfMooreComplex Aᵒᵖ).op) := rfl
    rw [h]
    infer_instance
  obtain ⟨⟨t, ht⟩⟩ := this
  have h2 : pi A = (signIso A).hom ≫ Functor.whiskerLeft (revFunctor A)
      ((isoDualS A).hom ≫ (dualize A).map (inclusionOfMooreComplex Aᵒᵖ).op) := rfl
  refine IsSplitEpi.mk' ⟨t ≫ (signIso A).inv, ?_⟩
  exact (congrArg (fun q => (t ≫ (signIso A).inv) ≫ q) h2).trans
    (comp_inv_comp_hom_comp (signIso A) _ t ht)

private lemma quasiIso_inclusion (Y : SimplicialObject Aᵒᵖ) :
    QuasiIso (inclusionOfMooreComplexMap Y) :=
  (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y)).quasiIso_hom

private lemma quasiIso_unop_inclusion (Y : SimplicialObject Aᵒᵖ) :
    QuasiIso ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
      (inclusionOfMooreComplexMap Y).op) := by
  have := quasiIso_inclusion A Y
  infer_instance

private lemma quasiIso_dualize_inclusion (V : CosimplicialObject A) :
    QuasiIso (((dualize A).map (inclusionOfMooreComplex Aᵒᵖ).op).app V) := by
  have h : ((dualize A).map (inclusionOfMooreComplex Aᵒᵖ).op).app V
      = (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
        (inclusionOfMooreComplexMap
          ((cosimplicialSimplicialEquiv A).functor.obj (op V))).op := rfl
  exact quasiIso_of_eq A h (quasiIso_unop_inclusion A _)

private lemma quasiIso_pi (U : CosimplicialObject A) : QuasiIso ((pi A).app U) := by
  have h : (pi A).app U = ((signIso A).hom.app U ≫ (isoDualS A).hom.app ((revFunctor A).obj U)) ≫
      ((dualize A).map (inclusionOfMooreComplex Aᵒᵖ).op).app ((revFunctor A).obj U) :=
    (Category.assoc _ _ _).symm
  have : IsIso ((signIso A).hom.app U ≫
      (isoDualS A).hom.app ((revFunctor A).obj U)) := inferInstance
  exact quasiIso_of_eq A h
    ((quasiIso_iff_comp_left _ _).mpr (quasiIso_dualize_inclusion A _))

private lemma isEquivalence_normalizedCochainComplexFunctor :
    (normalizedCochainComplexFunctor A).IsEquivalence := by
  have := isEquivalence_revFunctor A
  have := isEquivalence_normalizedMooreComplex Aᵒᵖ
  exact inferInstanceAs ((revFunctor A ⋙ (((cosimplicialSimplicialEquiv A).functor ⋙
    normalizedMooreComplex Aᵒᵖ).rightOp ⋙
    HomologicalComplex.unopFunctor A (ComplexShape.down ℕ))).IsEquivalence)

/-- **Stacks 019I**.
Let `A` be an abelian category. (1) The Moore cochain complex functor
`s : CoSimp(A) ⥤ CoCh_{≥0}(A)` is exact. (2) There is a functor `Q`, the normalized cochain
complex, together with a natural transformation `π : s ⟶ Q` which is an isomorphism in degree `0`
and, in degree `n + 1`, a cokernel of the cofaces `δ i : Uₙ ⟶ Uₙ₊₁`, `i ≤ n`. (3) `π` is a split
epimorphism in the functor category, which is the functorial direct sum decomposition
`s(U) = D(U) ⊕ Q(U)` with `D = ker π`. (4) `Q` is exact. (5) Each `π.app U` is a quasi-isomorphism.
(6) `Q` is an equivalence of categories. -/
@[stacks 019I,
  sga "4 XVII 5.5.3" "Dold–Puppe equivalence",
  sga "4½ Fonctions_L 1.4" "N is an equivalence"]
public theorem exists_normalizedCochainComplex :
    (PreservesFiniteLimits (alternatingCofaceMapComplex A) ∧
      PreservesFiniteColimits (alternatingCofaceMapComplex A)) ∧
    ∃ (Q : CosimplicialObject A ⥤ CochainComplex A ℕ)
      (π : alternatingCofaceMapComplex A ⟶ Q),
      (∀ U : CosimplicialObject A, IsIso ((π.app U).f 0)) ∧
      (∀ (U : CosimplicialObject A) (n : ℕ),
        ∃ e : cokernel (Sigma.desc (f := fun _ : Fin (n + 1) => U.obj ⦋n⦌)
            fun i => U.δ i.castSucc) ≅ (Q.obj U).X (n + 1),
          cokernel.π _ ≫ e.hom = (π.app U).f (n + 1)) ∧
      IsSplitEpi π ∧
      (PreservesFiniteLimits Q ∧ PreservesFiniteColimits Q) ∧
      (∀ U : CosimplicialObject A, QuasiIso (π.app U)) ∧
      Q.IsEquivalence := by
  refine ⟨⟨preservesFiniteLimits_alternatingCofaceMapComplex A,
      preservesFiniteColimits_alternatingCofaceMapComplex A⟩,
    normalizedCochainComplexFunctor A, pi A, isIso_pi_app_f_zero A, cokernel_pi A,
    isSplitEpi_pi A, ?_, quasiIso_pi A, isEquivalence_normalizedCochainComplexFunctor A⟩
  have := isEquivalence_normalizedCochainComplexFunctor A
  exact ⟨inferInstance, inferInstance⟩

/-! ### The projection `s(U) ⟶ Q(U)` is a homotopy equivalence -/

section HomotopyUnop

variable {A} {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex Aᵒᵖ c}

/-- A homotopy between morphisms of complexes of `Aᵒᵖ` gives a homotopy between the morphisms of
the unopposed complexes. -/
private def homotopyUnopFunctorMap {f g : K ⟶ L} (H : Homotopy f g) :
    Homotopy ((HomologicalComplex.unopFunctor A c).map f.op)
      ((HomologicalComplex.unopFunctor A c).map g.op) where
  hom i j := (H.hom j i).unop
  zero i j hij := by
    rw [H.zero j i hij]
    rfl
  comm i := Quiver.Hom.op_inj <| by
    have e₁ : (dNext i (C := (HomologicalComplex.unopFunctor A c).obj (op L))
        (D := (HomologicalComplex.unopFunctor A c).obj (op K))
        (fun i j => (H.hom j i).unop)).op = prevD i H.hom := rfl
    have e₂ : (prevD i (C := (HomologicalComplex.unopFunctor A c).obj (op L))
        (D := (HomologicalComplex.unopFunctor A c).obj (op K))
        (fun i j => (H.hom j i).unop)).op = dNext i H.hom := rfl
    rw [op_add, op_add, e₁, e₂]
    exact (H.comm i).trans (by rw [add_comm (dNext i H.hom)]; rfl)

/-- A homotopy equivalence of complexes of `Aᵒᵖ` gives a homotopy equivalence of the unopposed
complexes, in the opposite direction. -/
private def homotopyEquivUnop (e : HomotopyEquiv K L) :
    HomotopyEquiv ((HomologicalComplex.unopFunctor A c).obj (op L))
      ((HomologicalComplex.unopFunctor A c).obj (op K)) where
  hom := (HomologicalComplex.unopFunctor A c).map e.hom.op
  inv := (HomologicalComplex.unopFunctor A c).map e.inv.op
  homotopyHomInvId := (Homotopy.ofEq (by rw [← CategoryTheory.Functor.map_comp, ← op_comp])).trans
    ((homotopyUnopFunctorMap e.homotopyInvHomId).trans
      (Homotopy.ofEq (by rw [op_id, CategoryTheory.Functor.map_id])))
  homotopyInvHomId := (Homotopy.ofEq (by rw [← CategoryTheory.Functor.map_comp, ← op_comp])).trans
    ((homotopyUnopFunctorMap e.homotopyHomInvId).trans
      (Homotopy.ofEq (by rw [op_id, CategoryTheory.Functor.map_id])))

end HomotopyUnop

private lemma homotopyEquivalences_unopFunctor_map_inclusion (Y : SimplicialObject Aᵒᵖ) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
      ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
        (inclusionOfMooreComplexMap Y).op) :=
  ⟨homotopyEquivUnop
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y)), rfl⟩

private lemma homotopyEquivalences_dualize_inclusion (V : CosimplicialObject A) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
      (((dualize A).map (inclusionOfMooreComplex Aᵒᵖ).op).app V) :=
  homotopyEquivalences_unopFunctor_map_inclusion A
    ((cosimplicialSimplicialEquiv A).functor.obj (op V))

private lemma homotopyEquivalences_pi (U : CosimplicialObject A) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ) ((pi A).app U) := by
  have h : (pi A).app U = ((signIso A).hom.app U ≫ (isoDualS A).hom.app ((revFunctor A).obj U)) ≫
      ((dualize A).map (inclusionOfMooreComplex Aᵒᵖ).op).app ((revFunctor A).obj U) :=
    (Category.assoc _ _ _).symm
  obtain ⟨E, hE⟩ := homotopyEquivalences_dualize_inclusion A ((revFunctor A).obj U)
  rw [h, ← hE]
  exact ⟨(HomotopyEquiv.ofIso (asIso ((signIso A).hom.app U ≫
      (isoDualS A).hom.app ((revFunctor A).obj U)))).trans E, rfl⟩

/-- **The projection from the Moore cochain complex onto the normalized cochain complex is a
homotopy equivalence.** Let `A` be an abelian category. There is a functor `Q`, the normalized
cochain complex of [Stacks, Tag 019I], together with a natural transformation `π : s ⟶ Q` which is
an isomorphism in degree `0` and, in degree `n + 1`, a cokernel of the cofaces `δ i : Uₙ ⟶ Uₙ₊₁`,
`i ≤ n`, such that each `π.app U : s(U) ⟶ Q(U)` is a homotopy equivalence of cochain complexes. -/
public theorem exists_normalizedCochainComplex_homotopyEquivalences :
    ∃ (Q : CosimplicialObject A ⥤ CochainComplex A ℕ)
      (π : alternatingCofaceMapComplex A ⟶ Q),
      (∀ U : CosimplicialObject A, IsIso ((π.app U).f 0)) ∧
      (∀ (U : CosimplicialObject A) (n : ℕ),
        ∃ e : cokernel (Sigma.desc (f := fun _ : Fin (n + 1) => U.obj ⦋n⦌)
            fun i => U.δ i.castSucc) ≅ (Q.obj U).X (n + 1),
          cokernel.π _ ≫ e.hom = (π.app U).f (n + 1)) ∧
      ∀ U : CosimplicialObject A,
        HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ) (π.app U) :=
  ⟨normalizedCochainComplexFunctor A, pi A, isIso_pi_app_f_zero A, cokernel_pi A,
    homotopyEquivalences_pi A⟩

end DualDoldKan

end AlgebraicTopology
