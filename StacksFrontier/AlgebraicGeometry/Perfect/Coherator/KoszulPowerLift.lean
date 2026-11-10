module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Functor.IsIsoMapOfHypothesis
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulPowerDefs
public import StacksFrontier.Homology.DerivedComplete.KoszulTensorVanishing
public import StacksFrontier.Homology.Perfect.Duality
public import StacksFrontier.RingTheory.Koszul.Cone

/-!
# Lifting a class to a Koszul complex on a power of a sequence

Let `A` be a commutative ring and `f : Fin r → A` a finite sequence, and let `E` be an object of
the derived category of `A`-modules. Suppose every element of `H^n(E)` is killed by a power of
each `f i`, for `-r + 1 ≤ n ≤ 0`. Then a morphism `A[0] ⟶ E` factors through the Koszul complex
`K(f_1^{e+1}, …, f_r^{e+1})` for some `e`, along the canonical map from that Koszul complex to
`A[0]`.

Geometrically `A[0] ⟶ E` is a global section of `E` over `Spec A`, and the hypothesis says that
the cohomology of `E` in the stated range vanishes on the union of the basic opens `D(f i)`; the
conclusion is that the section comes from a Koszul complex, which is the perfect complex
supported on the closed complement.

## Main results

* `AdicKoszul.exists_koszulPower_lift`: the factorization through a Koszul power complex.

## Implementation notes

The induction is on the length `r` of the sequence. The inductive step uses the distinguished
triangle relating the Koszul complex of `f_1, …, f_{r+1}` to that of `f_1, …, f_r`, which is the
cone on multiplication by `f_{r+1}`; a power of `f_{r+1}` kills the composite into `E`, so the
morphism factors through the cone. Comparing the cone with the Koszul complex of the longer
sequence is the work of `KoszulTensorVanishing.ConeBridge.coneIso`, which identifies the mapping
cone of the extension to `ℤ` of a chain map of `ℕ`-indexed complexes with the extension of its
mapping cone.

The exponent is written `e : ℕ` for the source's positive power `e + 1`, so the existence
assertion is unchanged.

## References

* [Stacks Project, Tag 08E3](https://stacks.math.columbia.edu/tag/08E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

namespace AdicKoszul

universe u v

open CategoryTheory MonoidalCategory CochainComplex CochainComplex.HomComplex
  HomologicalComplex

/-! ### Transparency-stable rewriting helpers

Several comparisons below are between two spellings of the same object that agree by definition
but not at the `implicit` transparency level that `rw` and `simp` work at, for instance the
degree-`n` cohomology `(HomologicalComplex.homologyFunctor _ _ n).obj L` of a cochain complex and
the complex's own homology `L.homology n`. The lemmas in this section state the handful of
rewriting steps needed at such places abstractly, so that they can be applied in term mode, where
elaboration happens at the default transparency level. -/

/-- Conjugation by a composite isomorphism, performed one factor at a time: a commuting square
for the first factor turns into a conjugation statement for the second. -/
private theorem trans_conj {D : Type*} [Category D] {X Y Z : D} (α : X ≅ Y) (β : Y ≅ Z)
    {φ : X ⟶ X} {ψ : Y ⟶ Y} (h : φ ≫ α.hom = α.hom ≫ ψ) :
    (α ≪≫ β).inv ≫ φ ≫ (α ≪≫ β).hom = β.inv ≫ ψ ≫ β.hom := by
  simp [reassoc_of% h]

/-- Cancel an inverse pair in the middle of a four-fold composite. -/
private theorem comp_cancel_mid {D : Type*} [Category D] {W X Y Z V : D}
    (σ : W ⟶ X) (u : X ⟶ Y) (ι : Y ⟶ Z) (π : Z ⟶ Y) (τ : Y ⟶ V) {u' : X ⟶ V}
    (hιπ : ι ≫ π = 𝟙 Y) (h : u ≫ τ = u') :
    (σ ≫ u ≫ ι) ≫ π ≫ τ = σ ≫ u' := by
  simp only [Category.assoc]
  rw [← Category.assoc ι π τ, hιπ, Category.id_comp, h]

/-- A composite is annihilated by a scalar that annihilates its second factor. -/
private theorem comp_smul_eq_zero {D : Type*} [Category D] [Preadditive D] {R : Type*}
    [Semiring R] [Linear R D] {X Y Z : D} (φ : X ⟶ Y) {ψ : Y ⟶ Z} {c : R}
    (h : c • ψ = 0) : c • (φ ≫ ψ) = 0 := by
  rw [← Linear.comp_smul, h, Limits.comp_zero]

/-- Moving a scalar that annihilates a composite onto the second factor. -/
private theorem comp_smul_eq_zero' {D : Type*} [Category D] [Preadditive D] {R : Type*}
    [Semiring R] [Linear R D] {X Y Z : D} {φ : X ⟶ Y} {ψ : Y ⟶ Z} {c : R}
    (h : c • (φ ≫ ψ) = 0) : φ ≫ (c • ψ) = 0 := by
  rw [Linear.comp_smul, h]

/-- Cancel an isomorphism in front of a morphism killed by a scalar. -/
private theorem smul_eq_zero_of_iso_comp {D : Type*} [Category D] [Preadditive D] {R : Type*}
    [Semiring R] [Linear R D] {X Y Z : D} (e : X ≅ Y) {t : Y ⟶ Z} {c : R}
    (h : c • (e.hom ≫ t) = 0) : c • t = 0 :=
  (cancel_epi e.hom).mp (by rw [Linear.comp_smul, h, Limits.comp_zero])

/-- A module map out of `A` that kills `1` is zero. -/
private theorem moduleCat_hom_eq_zero_of_apply_one {A : Type u} [CommRing A]
    {M : ModuleCat.{u} A} (φ : ModuleCat.of A A ⟶ M) (h : φ.hom 1 = 0) : φ = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change φ.hom x = 0
  calc
    _ = φ.hom (x • (1 : A)) := by congr 1; simp
    _ = x • φ.hom 1 := map_smul _ _ _
    _ = 0 := by rw [h, smul_zero]

/-- Multiplication by `c` on `A[n]`, seen in the derived category, is `c • 𝟙`. -/
private theorem Q_map_single_smul_id {A : Type u} [CommRing A] (n : ℤ) (c : A) :
    DerivedCategory.Q.map (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor n).map
      (ModuleCat.ofHom (c • (LinearMap.id : A →ₗ[A] A)))) = c • 𝟙 _ := by
  have hm : ModuleCat.ofHom (c • (LinearMap.id : A →ₗ[A] A)) = c • 𝟙 (ModuleCat.of A A) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp [ModuleCat.ofHom]
  rw [hm, Functor.map_smul, CategoryTheory.Functor.map_id, DerivedCategory.Q.map_smul,
    DerivedCategory.Q.map_id]

private theorem exists_power_kills_single_map
    {A : Type u} [CommRing A] (E : DerivedCategory (ModuleCat.{u} A))
    (n : ℤ) (a : A)
    (t : DerivedCategory.Q.obj
      (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor n).obj
        (ModuleCat.of A A)) ⟶ E)
    (hkill : ∃ k : ℕ,
      a ^ k • (((((DerivedCategory.homologyFunctorFactors
        (ModuleCat.{u} A) n).app
          (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor n).obj
            (ModuleCat.of A A)) ≪≫
          singleObjHomologySelfIso (ComplexShape.up ℤ) n (ModuleCat.of A A)).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map t) 1)) = 0) :
    ∃ k : ℕ, a ^ k • t = 0 := by
  classical
  let U := ((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor n).obj
    (ModuleCat.of A A)
  let D := DerivedCategory.Q.obj U
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let e := (DerivedCategory.homologyFunctorFactors
    (ModuleCat.{u} A) n).app U ≪≫
    singleObjHomologySelfIso (ComplexShape.up ℤ) n (ModuleCat.of A A)
  let α : ModuleCat.of A A ⟶ H.obj E := e.inv ≫ H.map t
  obtain ⟨k, hk⟩ := hkill
  let m : ModuleCat.of A A ⟶ ModuleCat.of A A :=
    ModuleCat.ofHom (a ^ k • (LinearMap.id : A →ₗ[A] A))
  let K := CochainComplex.singleFunctors (ModuleCat.{u} A)
  let kmap := K.functor n |>.map m
  let g : D ⟶ D := DerivedCategory.Q.map kmap
  let F := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n
  let e₁ := singleObjHomologySelfIso (ComplexShape.up ℤ) n (ModuleCat.of A A)
  have hF := F.hom.naturality kmap
  change H.map (DerivedCategory.Q.map kmap) ≫ F.hom.app U =
    F.hom.app U ≫ homologyMap kmap n at hF
  have hS := NatIso.naturality_1
    (HomologicalComplex.homologyFunctorSingleIso (ModuleCat.{u} A)
      (ComplexShape.up ℤ) n) m
  change e₁.inv ≫ homologyMap kmap n ≫ e₁.hom = m at hS
  have hnat : e.inv ≫ H.map (DerivedCategory.Q.map kmap) ≫ e.hom = m :=
    (trans_conj (F.app U) e₁ hF).trans hS
  have hsource : e.inv ≫ H.map g = m ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simpa [Category.assoc, Iso.inv_hom_id] using hnat
  have hαone : ((e.inv ≫ H.map (g ≫ t)) : ModuleCat.of A A ⟶ H.obj E) 1 = 0 := by
    rw [Functor.map_comp, ← Category.assoc, hsource, Category.assoc]
    change α.hom (a ^ k • (1 : A)) = 0
    rw [map_smul]
    exact hk
  have hαzero := moduleCat_hom_eq_zero_of_apply_one (e.inv ≫ H.map (g ≫ t)) hαone
  have hzero : g ≫ t = 0 := by
    apply (StacksDraft.Perfect.single_derived_homology_bijective (ModuleCat.of A A) E n).injective
    change e.inv ≫ H.map (g ≫ t) = e.inv ≫ H.map 0
    rw [Functor.map_zero, hαzero]
    simp
  refine ⟨k, ?_⟩
  rw [show g = a ^ k • 𝟙 D from Q_map_single_smul_id n (a ^ k), Linear.smul_comp] at hzero
  simpa using hzero

private noncomputable def koszul_empty_iso_single {A : Type u} [CommRing A]
    (f : Fin 0 → A) :
    DerivedCategory.Q.obj ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) := by
  let S := (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.down ℕ) 0).obj
    (ModuleCat.of A A)
  let e (n : ℕ) : (Koszul.seqComplex f).X n ≅ S.X n := by
    by_cases hn : n = 0
    · subst n
      exact (exteriorPower.zeroEquiv A (Fin 0 → A)).toModuleIso ≪≫
        (HomologicalComplex.singleObjXSelf _ _ _).symm
    · exact (Koszul.seqComplex_isZero_of_lt f n (by omega)).iso
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  let eK : Koszul.seqComplex f ≅ S :=
    HomologicalComplex.Hom.isoOfComponents e (by
      intro i j hij
      exact (Koszul.seqComplex_isZero_of_lt f i (by change j + 1 = i at hij; omega)).eq_of_src _ _)
  exact DerivedCategory.Q.mapIso
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).mapIso eK ≪≫
      HomologicalComplex.extendSingleIso _ _ 0 0 rfl)

private noncomputable abbrev tensorKoszulObject {A : Type u} [CommRing A]
    {r : ℕ} (f : Fin r → A) : DerivedCategory (ModuleCat.{u} A) :=
  ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor A).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))).obj
    (DerivedCategory.Q.obj ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat))

private noncomputable abbrev koszulObject {A : Type u} [CommRing A]
    {r : ℕ} (f : Fin r → A) : DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.Q.obj ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat)

private noncomputable def tensorUnitKoszulIso {A : Type u} [CommRing A]
    {r : ℕ} (f : Fin r → A) : tensorKoszulObject f ≅ koszulObject f := by
  let I := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  exact CochainComplex.DerivedTensor.derivedTensorProductCommIso I (koszulObject f) ≪≫
    CochainComplex.DerivedTensor.derivedTensorProductRightUnitorIso (koszulObject f)

private theorem derivedKoszul_snoc_chain_triangle {A : Type u} [CommRing A]
    {r : ℕ} (f : Fin r → A) (a : A) :
    ∃ (q : (Koszul.seqComplex f).extend ComplexShape.embeddingDownNat ⟶
        (Koszul.seqComplex (Fin.snoc f a)).extend ComplexShape.embeddingDownNat)
      (c : koszulObject (Fin.snoc f a) ⟶ (koszulObject f)⟦(1 : ℤ)⟧),
      Triangle.mk (a • 𝟙 (koszulObject f)) (DerivedCategory.Q.map q) c ∈ distTriang _ := by
  let C := Koszul.seqComplex f
  let g := Stacks.MappingCone.NatIndexed.mulByF C a
  let E := ComplexShape.embeddingDownNat
  let q₁ := HomologicalComplex.extendMap g E
  obtain ⟨eK⟩ := Koszul.seqComplex_snoc_iso_cone f a
  let eC : CochainComplex.mappingCone q₁ ≅
      (Koszul.seqComplex (Fin.snoc f a)).extend E :=
    KoszulTensorVanishing.ConeBridge.coneIso C C g ≪≫
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).mapIso eK.symm
  let q₂ := (CochainComplex.mappingCone.triangle q₁).mor₂ ≫ eC.hom
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle q₁)
  let δ : DerivedCategory.Q.obj (CochainComplex.mappingCone q₁) ⟶
      (koszulObject f)⟦(1 : ℤ)⟧ := T.mor₃
  let c₀ := DerivedCategory.Q.map eC.inv ≫ δ
  have hExt : HomologicalComplex.extendMap (a • 𝟙 C) E =
      a • 𝟙 (C.extend E) := by
    ext1 i
    by_cases hi : ∃ n, E.f n = i
    · obtain ⟨n, rfl⟩ := hi
      simp [HomologicalComplex.extendMap_f _ _ (rfl : E.f n = E.f n)]
    · exact (C.isZero_extend_X E i (fun n hn => hi ⟨n, hn⟩)).eq_of_src _ _
  have hmul : DerivedCategory.Q.map q₁ = a • 𝟙 (koszulObject f) := by
    change DerivedCategory.Q.map (HomologicalComplex.extendMap (a • 𝟙 C) E) = _
    rw [hExt, Functor.map_smul, DerivedCategory.Q.map_id]
  let T' := Triangle.mk (a • 𝟙 (koszulObject f)) (DerivedCategory.Q.map q₂) c₀
  have hinv : DerivedCategory.Q.map eC.hom ≫ DerivedCategory.Q.map eC.inv =
      𝟙 (DerivedCategory.Q.obj (CochainComplex.mappingCone q₁)) := by
    rw [← DerivedCategory.Q.map_comp, eC.hom_inv_id, DerivedCategory.Q.map_id]
  have eT : T ≅ T' := Triangle.isoMk T T'
    (Iso.refl _) (Iso.refl _) (DerivedCategory.Q.mapIso eC)
    (by
      change DerivedCategory.Q.map q₁ ≫ 𝟙 _ = 𝟙 _ ≫ (a • 𝟙 (koszulObject f))
      rw [Category.comp_id, Category.id_comp, hmul])
    (by
      change DerivedCategory.Q.map (CochainComplex.mappingCone.triangle q₁).mor₂ ≫
        DerivedCategory.Q.map eC.hom = DerivedCategory.Q.map q₂
      exact (DerivedCategory.Q.map_comp _ _).symm)
    (by
      change δ ≫ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A))
          (1 : ℤ)).map (𝟙 (koszulObject f)) =
        DerivedCategory.Q.map eC.hom ≫ DerivedCategory.Q.map eC.inv ≫ δ
      rw [CategoryTheory.Functor.map_id, Category.comp_id, ← Category.assoc, hinv,
        Category.id_comp])
  exact ⟨q₂, c₀, Pretriangulated.isomorphic_distinguished T
    (DerivedCategory.mappingCone_triangle_distinguished q₁) T' eT.symm⟩

/-- Transport the Koszul triangle along the tensor-unit isomorphisms. -/
private theorem tensorKoszul_snoc_triangle {A : Type u} [CommRing A]
    {r : ℕ} (f : Fin r → A) (a : A) :
    ∃ (b : tensorKoszulObject f ⟶ tensorKoszulObject (Fin.snoc f a))
      (c : tensorKoszulObject (Fin.snoc f a) ⟶ (tensorKoszulObject f)⟦(1 : ℤ)⟧),
      Triangle.mk (a • 𝟙 (tensorKoszulObject f)) b c ∈ distTriang _ := by
  obtain ⟨q, c, hT⟩ := derivedKoszul_snoc_chain_triangle f a
  let e := tensorUnitKoszulIso f
  let e' := tensorUnitKoszulIso (Fin.snoc f a)
  let S := CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)
  let b := e.hom ≫ DerivedCategory.Q.map q ≫ e'.inv
  let d := e'.hom ≫ c ≫ S.map e.inv
  let T := Triangle.mk (a • 𝟙 (koszulObject f)) (DerivedCategory.Q.map q) c
  let T' := Triangle.mk (a • 𝟙 (tensorKoszulObject f)) b d
  have eT : T' ≅ T := Triangle.isoMk T' T e e e'
    (by simp [T', T, Linear.smul_comp, Linear.comp_smul])
    (by simp [T', T, b, Category.assoc])
    (by simp [T', T, d, S, Category.assoc, ← Functor.map_comp])
  exact ⟨b, d, Pretriangulated.isomorphic_distinguished T hT T' eT⟩

private theorem koszulPowerUnit_transition {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) (m n : ℕ) (hmn : n ≤ m) :
    DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f m) ≫
        DerivedCategory.Q.map ((ComplexShape.embeddingDownNat.extendFunctor
          (ModuleCat.{u} A)).map (AdicKoszul.koszulPowerTransition f m n hmn)) =
      DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f n) := by
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  have hSpec := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      (_root_.koszulPowerComplexes_form_inverseSystem f))))
  have hunit' : AdicKoszul.koszulPowerUnitChain f m ≫
      AdicKoszul.koszulPowerTransition f m n hmn =
        AdicKoszul.koszulPowerUnitChain f n := hSpec.2.2.2.2.2.2.1 m n hmn
  have hunit0' : (AdicKoszul.koszulPowerUnitChain f m).f 0 ≫
      (AdicKoszul.koszulPowerTransition f m n hmn).f 0 =
        (AdicKoszul.koszulPowerUnitChain f n).f 0 := by
    simpa only [HomologicalComplex.comp_f] using congrArg (fun q => q.f 0) hunit'
  -- The chosen degree-zero maps commute with the canonical Koszul transitions.
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  simp only [AdicKoszul.koszulPowerUnit, HomologicalComplex.mkHomFromSingle_f,
    ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ _
      (show ComplexShape.embeddingDownNat.f 0 = 0 by rfl)]
  exact comp_cancel_mid _ _ _ _ _ (Iso.inv_hom_id _) ((reassoc_of% hunit0') _)

private noncomputable def koszulUnitChain {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) :
    ((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
        (ModuleCat.of A A) ⟶
      (Koszul.seqComplex f).extend ComplexShape.embeddingDownNat :=
    HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom (exteriorPower.zeroEquiv A (Fin r → A)).symm.toLinearMap ≫
      ((Koszul.seqComplex f).extendXIso ComplexShape.embeddingDownNat
        (i := 0) rfl).inv)
    (fun i hi => by
      change 0 + 1 = i at hi
      simp only [zero_add] at hi
      subst i
      apply (HomologicalComplex.isZero_extend_X (Koszul.seqComplex f)
        ComplexShape.embeddingDownNat 1 ?_).eq_of_tgt
      intro j
      change -(j : ℤ) ≠ 1
      omega)

private theorem koszulPowerUnit_eq_koszulUnitChain {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) (e : ℕ) :
    AdicKoszul.koszulPowerUnit f e =
      koszulUnitChain (fun i => f i ^ (e + 1)) := by
  apply HomologicalComplex.from_single_hom_ext
  have hSpec := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      (_root_.koszulPowerComplexes_form_inverseSystem f))))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have hstd (x : A) : (exteriorPower.zeroEquiv A (Fin r → A)).symm x =
      x • ⟨ExteriorAlgebra.ιMulti A 0 Fin.elim0,
        Koszul.ιMulti_mem 0 Fin.elim0⟩ := by
    apply (exteriorPower.zeroEquiv A (Fin r → A)).injective
    rw [LinearEquiv.apply_symm_apply, map_smul]
    change x = x * (exteriorPower.zeroEquiv A (Fin r → A))
      ⟨ExteriorAlgebra.ιMulti A 0 Fin.elim0,
        Koszul.ιMulti_mem 0 Fin.elim0⟩
    have hι : (⟨ExteriorAlgebra.ιMulti A 0 Fin.elim0,
        Koszul.ιMulti_mem 0 Fin.elim0⟩ : ⋀[A]^0 (Fin r → A)) =
        exteriorPower.ιMulti A 0 Fin.elim0 :=
      Subtype.ext rfl
    rw [hι, exteriorPower.zeroEquiv_ιMulti, mul_one]
  simp only [AdicKoszul.koszulPowerUnit, koszulUnitChain,
    HomologicalComplex.mkHomFromSingle_f, ModuleCat.comp_apply,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  let xA : A := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (ModuleCat.of A A)).hom a
  change ((Koszul.seqComplex (fun i => f i ^ (e + 1))).extendXIso
      ComplexShape.embeddingDownNat (i := 0) rfl).inv.hom
        (((AdicKoszul.koszulPowerUnitChain f e).f 0).hom xA) =
    ((Koszul.seqComplex (fun i => f i ^ (e + 1))).extendXIso
      ComplexShape.embeddingDownNat (i := 0) rfl).inv.hom
        ((exteriorPower.zeroEquiv A (Fin r → A)).symm xA)
  congr 1
  exact (hSpec.2.2.2.2.2.1 e xA).trans (hstd xA).symm

private theorem single_hom_eq_smul_of_isIso
    {A : Type u} [CommRing A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (u v : ((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
      (ModuleCat.of A A) ⟶ K) [IsIso (v.f 0)] :
    ∃ a : A, u = a • v := by
  let e := singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)
  let m : ModuleCat.of A A ⟶ ModuleCat.of A A :=
    e.inv ≫ u.f 0 ≫ inv (v.f 0) ≫ e.hom
  have hm : m = m 1 • 𝟙 (ModuleCat.of A A) :=
    sub_eq_zero.mp (moduleCat_hom_eq_zero_of_apply_one _ (by simp))
  refine ⟨m 1, ?_⟩
  apply HomologicalComplex.from_single_hom_ext
  have h := congrArg (fun q => e.hom ≫ q ≫ e.inv ≫ v.f 0) hm
  simpa [m, Category.assoc, Linear.comp_smul, Linear.smul_comp] using h

private theorem koszulUnitChain_isIso_f_zero
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    IsIso ((koszulUnitChain f).f 0) := by
  let e := singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A) ≪≫
    (exteriorPower.zeroEquiv A (Fin r → A)).symm.toModuleIso ≪≫
    ((Koszul.seqComplex f).extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).symm
  exact ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩

private theorem factor_through_koszulUnit
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : DerivedCategory (ModuleCat.{u} A))
    (u : ((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
      (ModuleCat.of A A) ⟶ (Koszul.seqComplex f).extend ComplexShape.embeddingDownNat)
    (t : koszulObject f ⟶ E) :
    ∃ t' : koszulObject f ⟶ E,
      DerivedCategory.Q.map u ≫ t = DerivedCategory.Q.map (koszulUnitChain f) ≫ t' := by
  have := koszulUnitChain_isIso_f_zero f
  obtain ⟨a, ha⟩ := single_hom_eq_smul_of_isIso _ u (koszulUnitChain f)
  refine ⟨a • t, ?_⟩
  rw [ha, Functor.map_smul, Linear.smul_comp, Linear.comp_smul]

private theorem koszulUnitChain_empty_isIso
    {A : Type u} [CommRing A] (f : Fin 0 → A) : IsIso (koszulUnitChain f) := by
  have (n : ℤ) : IsIso ((koszulUnitChain f).f n) := by
    by_cases hn : n = 0
    · subst n
      exact koszulUnitChain_isIso_f_zero f
    · apply IsZero.isIso (isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n hn)
      by_cases h : ∃ j, ComplexShape.embeddingDownNat.f j = n
      · obtain ⟨j, rfl⟩ := h
        exact (Koszul.seqComplex_isZero_of_lt f j (by
          simp only [ComplexShape.embeddingDownNat_f] at hn
          omega)).of_iso ((Koszul.seqComplex f).extendXIso
            ComplexShape.embeddingDownNat (i := j) rfl)
      · exact (Koszul.seqComplex f).isZero_extend_X _ n (by simpa using h)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The base case of `exists_power_kills_tensorKoszulMap`: the empty sequence. -/
private theorem exists_power_kills_tensorKoszulMap_zero
    {A : Type u} [CommRing A] (f : Fin 0 → A)
    (E : DerivedCategory (ModuleCat.{u} A)) (a : A) (s : ℤ)
    (hE : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-s)).obj E,
      ∃ k : ℕ, a ^ k • x = 0)
    (t : (tensorKoszulObject f)⟦s⟧ ⟶ E) :
    ∃ k : ℕ, a ^ k • t = 0 := by
  let I := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let T := (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor A).obj I
  let e₀ : tensorKoszulObject f ≅ I :=
    T.mapIso (koszul_empty_iso_single f) ≪≫
      CochainComplex.DerivedTensor.derivedTensorProductRightUnitorIso I
  let eS : (tensorKoszulObject f)⟦s⟧ ≅
      DerivedCategory.Q.obj
        (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor (-s)).obj
          (ModuleCat.of A A)) :=
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) s).mapIso e₀ ≪≫
      ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso s (-s) 0
        (by omega)).app (ModuleCat.of A A) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) (-s)).app
        (ModuleCat.of A A)
  let t' := eS.inv ≫ t
  let eH := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) (-s)).app
      (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor (-s)).obj
        (ModuleCat.of A A)) ≪≫
    singleObjHomologySelfIso (ComplexShape.up ℤ) (-s) (ModuleCat.of A A)
  let x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-s)).obj E :=
    (eH.inv ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-s)).map t') 1
  obtain ⟨k, hk⟩ := hE x
  obtain ⟨k, hk'⟩ := exists_power_kills_single_map E (-s) a t' ⟨k, hk⟩
  exact ⟨k, smul_eq_zero_of_iso_comp eS.symm hk'⟩

private theorem exists_power_kills_tensorKoszulMap
    {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)
    (E : DerivedCategory (ModuleCat.{u} A)) (a : A) (s : ℤ)
    (hE : ∀ n : ℤ, -(r : ℤ) - s ≤ n → n ≤ -s →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj E,
        ∃ k : ℕ, a ^ k • x = 0)
    (t : (tensorKoszulObject f)⟦s⟧ ⟶ E) :
    ∃ k : ℕ, a ^ k • t = 0 := by
  induction r generalizing s with
  | zero => exact exists_power_kills_tensorKoszulMap_zero f E a s (hE (-s) (by omega) le_rfl) t
  | succ r ih =>
      let g : Fin r → A := fun i => f i.castSucc
      let a' := f (Fin.last r)
      have hf : f = Fin.snoc g a' := (Fin.snoc_init_self f).symm
      let eSeq : tensorKoszulObject f ≅ tensorKoszulObject (Fin.snoc g a') :=
        eqToIso (congrArg tensorKoszulObject hf)
      let eSeqShift := (CategoryTheory.shiftFunctor
        (DerivedCategory (ModuleCat.{u} A)) s).mapIso eSeq
      let tSnoc :
          (tensorKoszulObject (Fin.snoc g a'))⟦s⟧ ⟶ E := eSeqShift.inv ≫ t
      obtain ⟨b, c, hT⟩ := tensorKoszul_snoc_triangle g a'
      let T := Triangle.mk (a' • 𝟙 (tensorKoszulObject g)) b c
      let Ts := (Triangle.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) s).obj T
      obtain ⟨k₁, hk₁⟩ := ih g s (fun n hlow hhigh x => hE n (by omega) hhigh x)
        (Ts.mor₂ ≫ tSnoc)
      obtain ⟨u, hu⟩ := Triangle.yoneda_exact₃ Ts (T.shift_distinguished hT s) (a ^ k₁ • tSnoc)
        (comp_smul_eq_zero' hk₁)
      let sh := CategoryTheory.shiftFunctorAdd'
        (DerivedCategory (ModuleCat.{u} A)) s 1 (s + 1) (by omega)
      let u' := (sh.app (tensorKoszulObject g)).hom ≫ u
      obtain ⟨k₂, hk₂⟩ := ih g (s + 1) (fun n hlow hhigh x => hE n (by omega) (by omega) x) u'
      have huzero : a ^ k₂ • u = 0 := smul_eq_zero_of_iso_comp (sh.app (tensorKoszulObject g)) hk₂
      have hkillSnoc : a ^ (k₂ + k₁) • tSnoc = 0 := by
        rw [pow_add, mul_smul, hu]
        exact comp_smul_eq_zero Ts.mor₃ huzero
      exact ⟨k₂ + k₁, smul_eq_zero_of_iso_comp eSeqShift.symm hkillSnoc⟩

private theorem exists_power_kills_koszulMap
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : DerivedCategory (ModuleCat.{u} A)) (a : A)
    (hE : ∀ n : ℤ, -(r : ℤ) ≤ n → n ≤ 0 →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj E,
        ∃ k : ℕ, a ^ k • x = 0)
    (t : koszulObject f ⟶ E) : ∃ k : ℕ, a ^ k • t = 0 := by
  let e : (tensorKoszulObject f)⟦(0 : ℤ)⟧ ≅ koszulObject f :=
    (CategoryTheory.shiftFunctorZero _ ℤ).app _ ≪≫ tensorUnitKoszulIso f
  obtain ⟨k, hk⟩ := exists_power_kills_tensorKoszulMap r f E a 0
    (fun n hn hn' x => hE n (by omega) (by omega) x) (e.hom ≫ t)
  exact ⟨k, smul_eq_zero_of_iso_comp e hk⟩

/-- The inductive step of `exists_koszulPower_lift`: a class factoring through the Koszul complex
on `g ^ (e + 1)` and killed there by `a ^ k` factors through the Koszul complex on the powers
`(g, a) ^ (max e k + 1)`. -/
private theorem exists_snoc_koszulUnitChain_factor {A : Type u} [CommRing A] {r : ℕ}
    (g : Fin r → A) (a : A) (E : DerivedCategory (ModuleCat.{u} A))
    (s : DerivedCategory.Q.obj
      (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
        (ModuleCat.of A A)) ⟶ E)
    {e k : ℕ} (t : (AdicKoszul.canonicalKoszulPowerSystem g).obj ⟨e⟩ ⟶ E)
    (ht : s = DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit g e) ≫ t)
    (hk : a ^ k • t = 0) :
    ∃ w : koszulObject (Fin.snoc (fun i => g i ^ (max e k + 1)) (a ^ (max e k + 1))) ⟶ E,
      s = DerivedCategory.Q.map
        (koszulUnitChain (Fin.snoc (fun i => g i ^ (max e k + 1)) (a ^ (max e k + 1)))) ≫ w := by
  let m := max e k
  -- Clean spellings of the maps involved, so that the rewriting below stays within the
  -- `koszulObject` vocabulary.
  let qUnit : ∀ j : ℕ, DerivedCategory.Q.obj
        (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
          (ModuleCat.of A A)) ⟶ koszulObject (fun i => g i ^ (j + 1)) :=
    fun j => DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit g j)
  let p₀ : koszulObject (fun i => g i ^ (m + 1)) ⟶
      koszulObject (fun i => g i ^ (e + 1)) :=
    DerivedCategory.Q.map ((ComplexShape.embeddingDownNat.extendFunctor
      (ModuleCat.{u} A)).map
        (AdicKoszul.koszulPowerTransition g m e (Nat.le_max_left _ _)))
  let t₀ : koszulObject (fun i => g i ^ (e + 1)) ⟶ E := t
  have ht₀ : s = qUnit e ≫ t₀ := ht
  have hk₀ : a ^ k • t₀ = 0 := hk
  have htr : qUnit m ≫ p₀ = qUnit e :=
    koszulPowerUnit_transition g m e (Nat.le_max_left _ _)
  let t' : koszulObject (fun i => g i ^ (m + 1)) ⟶ E := p₀ ≫ t₀
  have hk' : a ^ (m + 1) • t' = 0 := by
    have hp : a ^ (m + 1) = a ^ (m + 1 - k) * a ^ k := by
      rw [← pow_add]
      congr 1
      dsimp [m]
      omega
    rw [hp, mul_smul, comp_smul_eq_zero p₀ hk₀, smul_zero]
  obtain ⟨q, c, hT⟩ := derivedKoszul_snoc_chain_triangle
    (fun i => g i ^ (m + 1)) (a ^ (m + 1))
  obtain ⟨v, hv⟩ := Triangle.yoneda_exact₂ _ hT t' (by
    change (a ^ (m + 1) • 𝟙 (koszulObject (fun i => g i ^ (m + 1)))) ≫ t' = 0
    rw [Linear.smul_comp, Category.id_comp, hk'])
  let v₀ : koszulObject (Fin.snoc (fun i => g i ^ (m + 1)) (a ^ (m + 1))) ⟶ E := v
  have hv₀ : t' = DerivedCategory.Q.map q ≫ v₀ := hv
  let uq : ((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
        (ModuleCat.of A A) ⟶
      (Koszul.seqComplex (Fin.snoc (fun i => g i ^ (m + 1)) (a ^ (m + 1)))).extend
        ComplexShape.embeddingDownNat :=
    AdicKoszul.koszulPowerUnit g m ≫ q
  have hmapq : DerivedCategory.Q.map uq = qUnit m ≫ DerivedCategory.Q.map q :=
    DerivedCategory.Q.map_comp _ _
  have hs : s = DerivedCategory.Q.map uq ≫ v₀ := by
    rw [hmapq, Category.assoc, ← hv₀]
    change s = qUnit m ≫ p₀ ≫ t₀
    rw [← Category.assoc, htr]
    exact ht₀
  obtain ⟨w, hw⟩ := factor_through_koszulUnit
    (Fin.snoc (fun i => g i ^ (m + 1)) (a ^ (m + 1))) E uq v₀
  exact ⟨w, hs.trans hw⟩

/-- A degree-zero class of a quasi-coherent complex on `Spec A`, supported on the
closed complement of a union of `r` basic opens in the indicated range, comes
from a Koszul complex on powers of the defining equations. -/
@[stacks 08E3]
public theorem exists_koszulPower_lift {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) (E : DerivedCategory (ModuleCat.{u} A))
    (hE : ∀ i : Fin r, ∀ n : ℤ, -(r : ℤ) + 1 ≤ n → n ≤ 0 →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj E,
        ∃ k : ℕ, f i ^ k • x = 0)
    (s : DerivedCategory.Q.obj
      (((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj
        (ModuleCat.of A A)) ⟶ E) :
    ∃ e : ℕ, ∃ t : (AdicKoszul.canonicalKoszulPowerSystem f).obj ⟨e⟩ ⟶ E,
      s = DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f e) ≫ t := by
  induction r with
  | zero =>
      have hq : IsIso (DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit f 0)) := by
        rw [koszulPowerUnit_eq_koszulUnitChain]
        exact CategoryTheory.Functor.isIso_map_of_isIso DerivedCategory.Q _
          (koszulUnitChain_empty_isIso _)
      obtain ⟨ψ, hψ, -⟩ := hq.out
      refine ⟨0, ψ ≫ s, ?_⟩
      exact ((Category.id_comp s).symm.trans
        (congrArg (fun φ => φ ≫ s) hψ.symm)).trans (Category.assoc _ _ _)
  | succ r ih =>
      let g : Fin r → A := fun i => f i.castSucc
      let a := f (Fin.last r)
      obtain ⟨e, t, ht⟩ := ih g (fun i n hn hn' x => hE i.castSucc n (by omega) hn' x)
      obtain ⟨k, hk⟩ := exists_power_kills_koszulMap (fun i => g i ^ (e + 1)) E a
        (fun n hn hn' x => hE (Fin.last r) n (by omega) hn' x) t
      obtain ⟨w, hw⟩ := exists_snoc_koszulUnitChain_factor g a E s t ht hk
      have hseq : Fin.snoc (fun i => g i ^ (max e k + 1)) (a ^ (max e k + 1)) =
          (fun i => f i ^ (max e k + 1)) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [g, a]
      obtain ⟨w, hw⟩ : ∃ w : koszulObject (fun i => f i ^ (max e k + 1)) ⟶ E,
          s = DerivedCategory.Q.map (koszulUnitChain (fun i => f i ^ (max e k + 1))) ≫ w := by
        rw [← hseq]
        exact ⟨w, hw⟩
      exact ⟨max e k, w, by rwa [koszulPowerUnit_eq_koszulUnitChain]⟩

end AdicKoszul

end
