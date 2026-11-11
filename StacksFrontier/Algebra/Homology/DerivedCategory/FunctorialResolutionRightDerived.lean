module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicResolutionIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceAlgebra

/-!
# Right derived functors computed by a functorial resolution

Let `F : 𝒜 ⥤ ℬ` be an additive functor of abelian categories, `𝒜` with enough injectives, and let
`ε : A[0] ⟶ C(A)` be a functorial "resolution": an additive functor `C : 𝒜 ⥤ CochainComplex 𝒜 ℕ`
with a natural map from `A` placed in degree `0`, which is a quasi-isomorphism onto a complex of
injective objects whenever `A` is injective. The terms `Cᵖ(A)` are *not* assumed to be acyclic for
`F`. Instead, assume that each composite `Cᵖ ⋙ F` is left exact and has vanishing higher right
derived functors at `A`. Then `RF(A[0])` is computed by `F(C(A))`.

The proof is the double complex argument. Let `I` be an injective resolution of `A` and let
`D^{q,p} = F(Cᵖ(I^q))`. Applying `F ∘ ε` to each `I^q` exhibits each column `F(C(I^q))` as a
resolution of `F(I^q)` (an exact complex of injectives is split, hence preserved by `F`), so
`F(I) ⟶ Tot(D)` is a quasi-isomorphism. In the other direction, for each `p`, the complex
`q ↦ F(Cᵖ(I^q))` computes the right derived functors of `Cᵖ ⋙ F` at `A`: it is exact in positive
degrees and its zeroth cohomology is `F(Cᵖ(A))` by left exactness, so `F(C(A)) ⟶ Tot(D)` is a
quasi-isomorphism ([Stacks, Tag 0133]). Finally `RF(A[0]) ≅ F(I)` because injective objects are
acyclic.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusSingleIsoOfFunctorialResolution`:
  `ι(RF(A[0])) ≅ Q(F(C(A)))` in the derived category of `ℬ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace OfFunctorialResolution

section Generalities

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]

/-- If `S` is exact and `S.f` is a monomorphism, then the map from `S.X₁` to the kernel of
`S.g` induced by `S.f` is an isomorphism. -/
lemma isIso_kernel_lift_of_exact (S : ShortComplex ℬ) (hS : S.Exact) [Mono S.f] :
    IsIso (kernel.lift S.g S.f S.zero) := by
  have heq : kernel.lift S.g S.f S.zero =
      (IsLimit.conePointUniqueUpToIso hS.fIsKernel (limit.isLimit _)).hom := by
    apply (cancel_mono (kernel.ι S.g)).mp
    rw [kernel.lift_ι]
    exact (IsLimit.conePointUniqueUpToIso_hom_comp hS.fIsKernel (limit.isLimit _)
      WalkingParallelPair.zero).symm
  rw [heq]
  infer_instance

/-- The terms of an injective object placed in degree `0` are injective. -/
lemma injective_single₀_obj_X (J : 𝒜) [Injective J] (n : ℕ) :
    Injective (((CochainComplex.single₀ 𝒜).obj J).X n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact Injective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 J).symm
      inferInstance
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 J n hn).injective

/-- A double complex vanishing outside the first quadrant has a total complex. -/
lemma hasTotal_of_firstQuadrant
    (K : HomologicalComplex₂ ℬ (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hK : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j)) :
    K.HasTotal (ComplexShape.up ℤ) := by
  apply HomologicalComplex₂.hasTotal_of_finite
  intro n
  refine ((Set.finite_Icc 0 n).image (fun i : ℤ => (i, n - i))).subset ?_
  rintro ⟨i, j⟩ ⟨hij, hne⟩
  change i + j = n at hij
  have hi : 0 ≤ i := by by_contra h; exact hne (hK i j (Or.inl (by omega)))
  have hj : 0 ≤ j := by by_contra h; exact hne (hK i j (Or.inr (by omega)))
  exact ⟨i, ⟨hi, by omega⟩, Prod.ext rfl (show n - i = j by omega)⟩

end Generalities

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive] (C : 𝒜 ⥤ CochainComplex 𝒜 ℕ) [C.Additive]

/-- The functor `X ↦ F(C(X))`, extended by zero to a `ℤ`-indexed cochain complex. -/
abbrev mapExtend : 𝒜 ⥤ CochainComplex ℬ ℤ :=
  C ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙ ComplexShape.embeddingUpNat.extendFunctor ℬ

/-- In degree `k ≥ 0`, the functor `mapExtend F C` is `Cᵏ ⋙ F`. -/
def mapExtendEvalIso (k : ℕ) :
    mapExtend F C ⋙ HomologicalComplex.eval ℬ (ComplexShape.up ℤ) (k : ℤ) ≅
      C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) k ⋙ F :=
  Functor.isoWhiskerLeft (C ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ))
    (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso ℬ (i := k) rfl)

omit [C.Additive] in
/-- The functor `mapExtend F C` vanishes in negative degrees. -/
lemma isZero_mapExtend_obj_X (X : 𝒜) (j : ℤ) (hj : j < 0) :
    IsZero (((mapExtend F C).obj X).X j) :=
  ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (C.obj X)).isZero_extend_X
    ComplexShape.embeddingUpNat j (fun n => by change (n : ℤ) ≠ j; omega)

variable {A : 𝒜} (I : InjectiveResolution A)

/-- The double complex `D^{q,p} = F(Cᵖ(I^q))` attached to an injective resolution `I`: its outer
index `q` is the index of `I`, its inner index `p` the index of the resolution `C`. -/
abbrev doubleComplex : HomologicalComplex₂ ℬ (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((mapExtend F C).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex

/-- The double complex `doubleComplex F C I` vanishes outside the first quadrant. -/
lemma isZero_doubleComplex_X_X (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero (((doubleComplex F C I).X i).X j) := by
  rcases h with hi | hj
  · exact (HomologicalComplex.eval ℬ (ComplexShape.up ℤ) j).map_isZero
      ((mapExtend F C).map_isZero (I.cochainComplex.isZero_of_isStrictlyGE 0 i hi))
  · exact isZero_mapExtend_obj_X F C _ j hj

/-- The double complex `doubleComplex F C I` has a total complex. -/
instance hasTotal_doubleComplex : (doubleComplex F C I).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_firstQuadrant _ (isZero_doubleComplex_X_X F C I)

/-! ### The comparison `F(I) ⟶ Tot(D)` -/

section Columns

variable (ε : CochainComplex.single₀ 𝒜 ⟶ C)

/-- The augmentation `F(X)[0] ⟶ F(C(X))`, extended to `ℤ`-indexed complexes. -/
def augmentation : F ⋙ HomologicalComplex.single ℬ (ComplexShape.up ℤ) 0 ⟶ mapExtend F C :=
  (Functor.isoWhiskerLeft F (Stacks.RelativeCech.singleExtendUpNatIso ℬ)).inv ≫
    Functor.whiskerRight
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv ≫
        Functor.whiskerRight ε (F.mapHomologicalComplex (ComplexShape.up ℕ)))
      (ComplexShape.embeddingUpNat.extendFunctor ℬ)

omit [C.Additive] in
/-- At an injective object `J`, the augmentation `F(J)[0] ⟶ F(C(J))` is a quasi-isomorphism:
`J[0] ⟶ C(J)` is a quasi-isomorphism of complexes of injectives, hence a homotopy equivalence,
which `F` preserves. -/
lemma quasiIso_augmentation_app (hε : ∀ I : 𝒜, Injective I → QuasiIso (ε.app I))
    (hC : ∀ I : 𝒜, Injective I → ∀ p : ℕ, Injective ((C.obj I).X p)) (J : 𝒜) [hJ : Injective J] :
    QuasiIso ((augmentation F C ε).app J) := by
  have := hε J hJ
  have := hC J hJ
  have := injective_single₀_obj_X J
  have hα : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (ε.app J)) :=
    Stacks.RelativeCech.quasiIso_map_of_injective F (ε.app J)
  let a : F ⋙ HomologicalComplex.single ℬ (ComplexShape.up ℕ) 0 ⟶
      C ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ) :=
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv ≫
      Functor.whiskerRight ε (F.mapHomologicalComplex (ComplexShape.up ℕ))
  have ha : QuasiIso (a.app J) := by
    dsimp [a]
    infer_instance
  exact quasiIso_comp ((Stacks.RelativeCech.singleExtendUpNatIso ℬ).inv.app (F.obj J))
    (HomologicalComplex.extendMap (a.app J) ComplexShape.embeddingUpNat)
    (hφ' := (HomologicalComplex.quasiIso_extendMap_iff
      (a.app J) ComplexShape.embeddingUpNat).mpr ha)

/-- The augmentation of the double complex by `F(I)` placed in inner degree `0`. -/
def columnAugmentation :
    StacksDraft.TotalComplexQuasiIso.singleRowZero
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex) ⟶
      doubleComplex F C I :=
  (NatTrans.mapHomologicalComplex (augmentation F C ε) (ComplexShape.up ℤ)).app I.cochainComplex

/-- `F(I)` placed in inner degree `0` vanishes in negative outer degrees. -/
lemma isZero_singleRowZero_X (p : ℤ) (hp : p < 0) :
    IsZero ((StacksDraft.TotalComplexQuasiIso.singleRowZero
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex)).X p) :=
  (HomologicalComplex.single ℬ (ComplexShape.up ℤ) 0).map_isZero
    (F.map_isZero (I.cochainComplex.isZero_of_isStrictlyGE 0 p hp))

/-- `F(I)` placed in inner degree `0` has a total complex. -/
instance hasTotal_singleRowZero :
    (StacksDraft.TotalComplexQuasiIso.singleRowZero
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex)).HasTotal
        (ComplexShape.up ℤ) :=
  hasTotal_of_firstQuadrant _ (by
    rintro i j (hi | hj)
    · exact (HomologicalComplex.eval ℬ (ComplexShape.up ℤ) j).map_isZero
        (isZero_singleRowZero_X F I i hi)
    · exact StacksDraft.TotalComplexQuasiIso.isZero_singleRowZero_X_X _ i j hj)

/-- The comparison map `F(I) ⟶ Tot(D)`, through the augmentation of each column. -/
def toTotal :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex ⟶
      (doubleComplex F C I).total (ComplexShape.up ℤ) :=
  StacksDraft.TotalComplexQuasiIso.totalSingleRowZeroUnit
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex) ≫
    HomologicalComplex₂.total.map (columnAugmentation F C I ε) (ComplexShape.up ℤ)

/-- The comparison map `F(I) ⟶ Tot(D)` is a quasi-isomorphism: each column of `D` is a
resolution of the corresponding term of `F(I)` ([Stacks, Tag 0133]). -/
lemma quasiIso_toTotal (hε : ∀ I : 𝒜, Injective I → QuasiIso (ε.app I))
    (hC : ∀ I : 𝒜, Injective I → ∀ p : ℕ, Injective ((C.obj I).X p)) :
    QuasiIso (toTotal F C I ε) := by
  have := StacksDraft.TotalComplexQuasiIso.isIso_totalSingleRowZeroUnit
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex)
  have := StacksDraft.TotalComplexQuasiIso.quasiIso_total_map (columnAugmentation F C I ε) 0
    (fun p q hq => StacksDraft.TotalComplexQuasiIso.isZero_singleRowZero_X_X _ p q hq)
    (isZero_singleRowZero_X F I)
    (fun p q hq => isZero_doubleComplex_X_X F C I p q (Or.inr hq))
    (fun p hp => (mapExtend F C).map_isZero (I.cochainComplex.isZero_of_isStrictlyGE 0 p hp))
    (fun p => quasiIso_augmentation_app F C ε hε hC (I.cochainComplex.X p))
  dsimp only [toTotal]
  infer_instance

end Columns

/-! ### The comparison `F(C(A)) ⟶ Tot(D)` -/

section Rows

/-- The augmentation `A ⟶ I⁰` of an injective resolution, in the `ℤ`-indexed complex. -/
def augZero : A ⟶ I.cochainComplex.X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv ≫ I.ι.f 0 ≫
    (I.cochainComplexXIso 0 0 rfl).inv

/-- The augmentation `A ⟶ I⁰` composes to zero with the differential `I⁰ ⟶ I¹`. -/
lemma augZero_comp_d : augZero I ≫ I.cochainComplex.d 0 1 = 0 := by
  rw [I.cochainComplex_d 0 1 0 1 rfl rfl, augZero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [I.ι_f_zero_comp_complex_d_assoc, zero_comp, comp_zero]

/-- The short complex `A ⟶ I⁰ ⟶ I¹` in the `ℤ`-indexed complex. -/
@[simps]
def augShortComplex : ShortComplex 𝒜 :=
  ShortComplex.mk (augZero I) (I.cochainComplex.d 0 1) (augZero_comp_d I)

/-- `augZero` followed by the comparison of `I⁰` with its `ℤ`-indexed copy. -/
lemma augZero_comp_cochainComplexXIso_hom :
    augZero I ≫ (I.cochainComplexXIso 0 0 rfl).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv ≫ I.ι.f 0 := by
  unfold augZero
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The differential `I⁰ ⟶ I¹` of the `ℤ`-indexed complex, read on the `ℕ`-indexed one. -/
lemma cochainComplexXIso_hom_comp_d :
    (I.cochainComplexXIso 0 0 rfl).hom ≫ I.cocomplex.d 0 1 =
      I.cochainComplex.d 0 1 ≫ (I.cochainComplexXIso 1 1 rfl).hom := by
  simp [I.cochainComplex_d 0 1 0 1 rfl rfl]

/-- The sequence `0 ⟶ A ⟶ I⁰ ⟶ I¹` is exact. -/
lemma augShortComplex_exact_and_mono : (augShortComplex I).Exact ∧ Mono (augShortComplex I).f :=
  (ShortComplex.exact_and_mono_f_iff_of_iso
    (ShortComplex.isoMk (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).symm
      (I.cochainComplexXIso 0 0 rfl)
      (I.cochainComplexXIso 1 1 rfl) (augZero_comp_cochainComplexXIso_hom I).symm
      (cochainComplexXIso_hom_comp_d I) :
      augShortComplex I ≅ ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d)).2
    ⟨I.exact₀, inferInstanceAs (Mono (I.ι.f 0))⟩

/-- The augmentation `F(C(A)) ⟶ F(C(I⁰))` into the row `q = 0` of the flipped double complex. -/
def rowAugmentation :
    (mapExtend F C).obj A ⟶ rowZero (doubleComplex F C I).flip where
  f p := ((mapExtend F C).map (augZero I)).f p
  comm' p p' _ := ((mapExtend F C).map (augZero I)).comm p p'

/-- The hypotheses of [Stacks, Tag 0133] for the rows of the double complex: for each `p`, the
complex `q ↦ F(Cᵖ(I^q))` is exact away from `q = 0` because it computes the right derived
functors of `Cᵖ ⋙ F` at `A`, and its kernel in degree `0` is `F(Cᵖ(A))` by left exactness. -/
lemma hypotheses_rowAugmentation [EnoughInjectives 𝒜]
    [∀ p : ℕ, PreservesFiniteLimits (C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) p ⋙ F)]
    (hA : ∀ p q : ℕ, 0 < q →
      IsZero (((C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) p ⋙ F).rightDerived q).obj A)) :
    Hypotheses ((mapExtend F C).obj A) (doubleComplex F C I).flip (rowAugmentation F C I) where
  diagonalFinite n := by
    refine (Set.finite_Icc 0 n).subset ?_
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    by_contra h
    rw [Set.mem_Icc] at h
    exact hp (isZero_doubleComplex_X_X F C I (n - p) p (by omega))
  zero_of_neg p q hq := isZero_doubleComplex_X_X F C I q p (Or.inl hq)
  exactAt_of_ne_zero p q hq := by
    rcases lt_or_ge p 0 with hp | hp
    · exact HomologicalComplex.ExactAt.of_isZero (isZero_doubleComplex_X_X F C I q p (Or.inr hp))
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℤ) = p := ⟨p.toNat, by omega⟩
      exact HomologicalComplex.ExactAt.of_iso
        (InjectiveResolution.exactAt_mapHomologicalComplex_cochainComplex _ I (hA k) q hq)
        ((NatIso.mapHomologicalComplex (mapExtendEvalIso F C k)
          (ComplexShape.up ℤ)).symm.app I.cochainComplex)
  inducesIsoKernel p := by
    have hα : (rowAugmentation F C I).f p ≫ ((doubleComplex F C I).flip.X p).d 0 1 = 0 := by
      change ((mapExtend F C).map (augZero I)).f p ≫
        ((mapExtend F C).map (I.cochainComplex.d 0 1)).f p = 0
      rw [← HomologicalComplex.comp_f, ← Functor.map_comp, augZero_comp_d, Functor.map_zero,
        HomologicalComplex.zero_f]
    refine ⟨hα, ?_⟩
    rcases lt_or_ge p 0 with hp | hp
    · refine StacksDraft.TotalComplexQuasiIso.isIso_of_isZero _
        (isZero_mapExtend_obj_X F C A p hp) ?_
      exact IsZero.of_mono (kernel.ι _) (isZero_doubleComplex_X_X F C I 0 p (Or.inr hp))
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℤ) = p := ⟨p.toNat, by omega⟩
      obtain ⟨hS₀, hm₀⟩ := augShortComplex_exact_and_mono I
      have hH : ((augShortComplex I).map
          (C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) k ⋙ F)).Exact :=
        hS₀.map_of_mono_of_preservesKernel _ hm₀ inferInstance
      have : Mono (augZero I) := hm₀
      have hmH : Mono ((augShortComplex I).map
          (C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) k ⋙ F)).f :=
        Functor.map_mono (C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) k ⋙ F) (augZero I)
      obtain ⟨hS, hm⟩ := (ShortComplex.exact_and_mono_f_iff_of_iso
        ((augShortComplex I).mapNatIso (mapExtendEvalIso F C k))).2 ⟨hH, hmH⟩
      exact isIso_kernel_lift_of_exact _ hS

/-- The comparison map `F(C(A)) ⟶ Tot(D)`, through the augmentation of each row. -/
def resolutionToTotal [EnoughInjectives 𝒜]
    [∀ p : ℕ, PreservesFiniteLimits (C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) p ⋙ F)]
    (hA : ∀ p q : ℕ, 0 < q →
      IsZero (((C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) p ⋙ F).rightDerived q).obj A)) :
    (mapExtend F C).obj A ⟶ (doubleComplex F C I).total (ComplexShape.up ℤ) :=
  comparisonMapP _ _ _ (hypotheses_rowAugmentation F C I hA) ≫
    ((doubleComplex F C I).totalFlipIso (ComplexShape.up ℤ)).hom

/-- The comparison map `F(C(A)) ⟶ Tot(D)` is a quasi-isomorphism ([Stacks, Tag 0133]). -/
lemma quasiIso_resolutionToTotal [EnoughInjectives 𝒜]
    [∀ p : ℕ, PreservesFiniteLimits (C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) p ⋙ F)]
    (hA : ∀ p q : ℕ, 0 < q →
      IsZero (((C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) p ⋙ F).rightDerived q).obj A)) :
    QuasiIso (resolutionToTotal F C I hA) := by
  dsimp only [resolutionToTotal]
  infer_instance

end Rows

end OfFunctorialResolution

open OfFunctorialResolution

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory 𝒜] [HasDerivedCategory ℬ] [EnoughInjectives 𝒜]
  (F : 𝒜 ⥤ ℬ) [F.Additive] (C : 𝒜 ⥤ CochainComplex 𝒜 ℕ) [C.Additive]

/-- **`RF(A[0])` is computed by a functorial resolution `C`** whose terms need not be
`F`-acyclic: it suffices that `A[0] ⟶ C(A)` is, functorially, a resolution by injectives at
injective objects, and that each composite `Cᵖ ⋙ F` is left exact with vanishing higher right
derived functors at `A`. Then `RF(A[0]) ≅ F(C(A))` in the derived category of `ℬ`. -/
def rightDerivedFunctorPlusSingleIsoOfFunctorialResolution
    (ε : CochainComplex.single₀ 𝒜 ⟶ C)
    (hε : ∀ I : 𝒜, Injective I → QuasiIso (ε.app I))
    (hC : ∀ I : 𝒜, Injective I → ∀ p : ℕ, Injective ((C.obj I).X p))
    (A : 𝒜)
    [∀ p : ℕ, PreservesFiniteLimits (C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) p ⋙ F)]
    (hA : ∀ p q : ℕ, 0 < q →
      IsZero (((C ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) p ⋙ F).rightDerived q).obj A)) :
    DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj A)) ≅
      DerivedCategory.Q.obj
        (((F.mapHomologicalComplex _).obj (C.obj A)).extend ComplexShape.embeddingUpNat) :=
  let I := injectiveResolution A
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso _ (toTotal F C I ε)).2
    (quasiIso_toTotal F C I ε hε hC)
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso _ (resolutionToTotal F C I hA)).2
    (quasiIso_resolutionToTotal F C I hA)
  (F.rightDerivedFunctorPlusSingleIsoOfAcyclic A I.cochainComplex 0 I.ι'
      (fun n => F.rightAcyclic_of_injective (I.cochainComplex.X n))).symm ≪≫
    asIso (DerivedCategory.Q.map (toTotal F C I ε)) ≪≫
    (asIso (DerivedCategory.Q.map (resolutionToTotal F C I hA))).symm

end CategoryTheory.Functor
