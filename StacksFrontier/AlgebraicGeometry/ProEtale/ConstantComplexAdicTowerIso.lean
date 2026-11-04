module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstantComplexAdicTowerRestrict
public import StacksFrontier.CategoryTheory.MittagLefflerSelection
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ConstantProjective
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.RowAdicTowerChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.RowAdicTowerMittagLeffler
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.RowAdicTowerNakayama
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.RowAdicTowerRigidity
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeAssembly

/-!
# Non-compatible isomorphisms with constant complexes give an isomorphism of towers

Let `(C, J)` be a site with a final object `T` over which sections of sheaves are exact (every
locally surjective map of sheaves is surjective on sections over `T`), `Λ` a Noetherian ring,
`I ⊆ Λ` an ideal and `Λ^∧` the `I`-adic completion. Let `P` be a K-flat complex of sheaves of
`Λ`-modules and `M` a bounded complex of finite projective `Λ^∧`-modules such that for every `n`
there is an isomorphism `Λ/Iⁿ⁺¹ ⊗ P ≅ \underline{Λ/Iⁿ⁺¹ ⊗ M}` in `D(C, Λ/Iⁿ⁺¹)`, the isomorphisms
being in no way compatible. Then the tower of derived reductions `n ↦ P ⊗_Λ^L \underline{Λ/Iⁿ}` is
isomorphic to the tower `n ↦ \underline{M/IⁿM}`.

This is the Mittag-Leffler and Nakayama core of the proof of Stacks 09C6. The argument runs over
`A = Λ^∧` with `𝔞 = IA`: the homotopy classes of maps `\underline{M} ⟶ P ⊗ \underline{A/𝔞ʲ}` form
an inverse system which, truncated at any level, is identified (through the isomorphism at that
level and the K-projectivity of `\underline{S ⊗ M}` for `S = A/𝔞ⁿ⁺¹`) with the system of
endomorphisms `j ↦ Hom(\underline{M}, \underline{M} ⊗ \underline{A/𝔞ʲ})`, which is Mittag-Leffler
by the Artin–Rees lemma. A good element of the eventual image at the first level lifts to a
compatible family, all of whose members are quasi-isomorphisms by a sheaf version of Nakayama's
lemma (`CategoryTheory.Functor.exists_natTrans_forall_of_isMittagLeffler`).

## Main results

* `Stacks.ModuleSheaf.exists_quasiIso_rowAdicTower_le`: the comparison at a fixed level.
* `Stacks.ModuleSheaf.quasiIso_of_quasiIso_reduction_rowAdicTower`: Nakayama at a fixed level.
* `Stacks.ModuleSheaf.exists_natTrans_rowAdicTower_quasiIso`: the selection, over `A`.
* `Stacks.ModuleSheaf.nonempty_derivedReductionTower_iso_of_isWeaklyContractible`: the statement
  over `Λ`.

## References

* [Stacks Project, Tag 09C6](https://stacks.math.columbia.edu/tag/09C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor Opposite

universe t t' w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

/-- If the kernel of `e` is `𝔞ᵐ`, then `(e(𝔞))ᵐ = 0`. -/
theorem _root_.Ideal.map_pow_eq_bot_of_ker_eq {A S : Type*} [CommRing A] [CommRing S]
    (𝔞 : Ideal A) (e : A →+* S) {m : ℕ} (hker : RingHom.ker e = 𝔞 ^ m) :
    (𝔞.map e) ^ m = ⊥ := by
  rw [← Ideal.map_pow, ← hker]
  exact le_bot_iff.1 (Ideal.map_le_iff_le_comap.2 fun x hx => by simpa using hx)

/-- Termwise extension of scalars of a complex of projective modules is a complex of projective
modules. -/
theorem _root_.CochainComplex.projective_extendScalars_X {A S : Type w} [CommRing A] [CommRing S]
    (e : A →+* S) (M : CochainComplex (ModuleCat.{w} A) ℤ)
    (hM : ∀ k, Module.Projective A (M.X k)) (k : ℤ) :
    Module.Projective S ((((ModuleCat.extendScalars.{w, w, w} e).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M).X k) := by
  have := hM k
  have : Projective (M.X k) := (IsProjective.iff_projective (R := A) (M.X k)).1 inferInstance
  exact (IsProjective.iff_projective (R := S) _).2 (Dualizing.projective_extendScalars e (M.X k))

/-- Conjugating a commutative square by isomorphisms compatible with the horizontal maps. -/
theorem _root_.CategoryTheory.comp_conj_eq_conj_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (R : 𝒟 ⥤ 𝒞) {Y₁ Y₂ X₁ X₂ : 𝒞} {Y₁' Y₂' X₁' X₂' : 𝒟} {a : Y₁ ⟶ Y₂} {a' : Y₁' ⟶ Y₂'}
    {b : X₁ ⟶ X₂} {b' : X₁' ⟶ X₂'} {εY₁ : Y₁ ≅ R.obj Y₁'} {εY₂ : Y₂ ≅ R.obj Y₂'}
    {εX₁ : X₁ ≅ R.obj X₁'} {εX₂ : X₂ ≅ R.obj X₂'} {τ₁ : Y₁' ⟶ X₁'} {τ₂ : Y₂' ⟶ X₂'}
    (h₁ : a ≫ εY₂.hom = εY₁.hom ≫ R.map a') (h₂ : b ≫ εX₂.hom = εX₁.hom ≫ R.map b')
    (h₃ : a' ≫ τ₂ = τ₁ ≫ b') :
    a ≫ εY₂.hom ≫ R.map τ₂ ≫ εX₂.inv = (εY₁.hom ≫ R.map τ₁ ≫ εX₁.inv) ≫ b := by
  have h₂' : εX₁.inv ≫ b = R.map b' ≫ εX₂.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h₂, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [reassoc_of% h₁, Category.assoc, Category.assoc, h₂', ← R.map_comp_assoc, h₃,
    R.map_comp_assoc]

/-- A morphism in the homotopy category between acyclic complexes is a quasi-isomorphism. -/
theorem _root_.HomotopyCategory.quasiIso_of_acyclic {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (hK : K.Acyclic) (hL : L.Acyclic)
    (φ : (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj L) :
    HomotopyCategory.quasiIso _ _ φ := by
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff,
    quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_of_source_target_iso_zero _ ((hK i).isZero_homology.isoZero)
    ((hL i).isZero_homology.isoZero)

/-- A morphism of towers in the homotopy category all of whose components are
quasi-isomorphisms induces an isomorphism of the towers in the derived category. -/
theorem _root_.DerivedCategory.nonempty_iso_of_natTrans_quasiIso {𝒜 : Type*} [Category 𝒜]
    [Abelian 𝒜] [HasDerivedCategory 𝒜] {ι : Type*} [Category ι] {F G : ι ⥤ CochainComplex 𝒜 ℤ}
    (φ : F ⋙ HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ) ⟶
      G ⋙ HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ))
    (hφ : ∀ j, HomotopyCategory.quasiIso _ _ (φ.app j)) :
    Nonempty (F ⋙ DerivedCategory.Q ≅ G ⋙ DerivedCategory.Q) := by
  let θ := Functor.whiskerRight φ DerivedCategory.Qh
  have : ∀ j, IsIso (θ.app j) := fun j =>
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _ (hφ j)
  have : IsIso θ := NatIso.isIso_of_isIso_app θ
  exact ⟨Functor.isoWhiskerLeft F (DerivedCategory.quotientCompQhIso 𝒜).symm ≪≫ asIso θ ≪≫
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso 𝒜)⟩

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type w} [CommRing A]
  [UnivLE.{max u v, w}]

/-- Extending scalars of a constant complex of projective modules, bounded above, gives a K-flat
complex of sheaves. -/
private theorem kFlat_extendScalars_constantSheaf_complex {S : Type w} [CommRing S] (e : A →+* S)
    (M : CochainComplex (ModuleCat.{w} A) ℤ) (b : ℤ) [M.IsStrictlyLE b]
    (hM : ∀ k, Module.Projective A (M.X k)) :
    KFlat (curriedTensor (Sheaf J (ModuleCat.{w} S)))
      (((extendScalars J e).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :=
  kFlat_extendScalars J e (kFlat_constantSheaf_mapHomologicalComplex (C := C) (J := J) M b hM)

section Core

variable [IsNoetherianRing A] {T : C} (hT : IsTerminal T)
  (hW : ∀ {F G : Sheaf J (Type w)} (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
    Function.Surjective (φ.hom.app (op T)))
  (𝔞 : Ideal A) {S : ℕ → Type w} [∀ n, CommRing (S n)]
  [∀ n, HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} (S n)))]
  (e : ∀ n, A →+* S n) (he : ∀ n, Function.Surjective (e n))
  (hker : ∀ n, RingHom.ker (e n) = 𝔞 ^ (n + 1))
  {P : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ}
  (hP : KFlat (curriedTensor (Sheaf J (ModuleCat.{w} A))) P)
  (M : CochainComplex (ModuleCat.{w} A) ℤ) (a b : ℤ) [M.IsStrictlyGE a] [M.IsStrictlyLE b]
  (hM : ∀ k, Module.Finite A (M.X k) ∧ Module.Projective A (M.X k))


omit [IsNoetherianRing A] in
include hT hW he hker hP hM b in
/-- **The level `n + 1` comparison.** An isomorphism `S ⊗ P ≅ \underline{S ⊗ M}` in `D(C, S)`,
`S = A/𝔞ⁿ⁺¹`, gives quasi-isomorphisms `\underline{M} ⊗ \underline{A/𝔞ʲ} ⟶ P ⊗ \underline{A/𝔞ʲ}`
for `j ≤ n + 1`, compatible with the transition maps. -/
theorem exists_quasiIso_rowAdicTower_le (n : ℕ)
    (hn : Nonempty (DerivedCategory.Q.obj
        (((extendScalars J (e n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj (((constantSheaf J (ModuleCat.{w} (S n))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{w, w, w} (e n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)))) :
    ∃ g : ∀ j : ℕ, j ≤ n + 1 →
        ((rowAdicTower J 𝔞 (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).obj (op j) ⟶ (rowAdicTower J 𝔞 P).obj (op j)),
      (∀ j hj, QuasiIso (g j hj)) ∧
        ∀ (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n + 1),
          (rowAdicTower J 𝔞 (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)).map (homOfLE hij).op ≫ g i (hij.trans hjn) =
            g j hjn ≫ (rowAdicTower J 𝔞 P).map (homOfLE hij).op := by
  obtain ⟨eP⟩ := hn
  have hker' : RingHom.ker (e n) ≤ 𝔞 ^ (n + 1) := (hker n).le
  obtain ⟨εY, hεY⟩ := exists_rowAdicTower_iso_restrictScalars (J := J) (e n) (he n) 𝔞 (n + 1)
    hker' (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
  obtain ⟨εX, hεX⟩ := exists_rowAdicTower_iso_restrictScalars (J := J) (e n) (he n) 𝔞 (n + 1)
    hker' P
  obtain ⟨u, hu⟩ := exists_quasiIso_of_iso_constantSheaf (C := C) (J := J) (R := S n) hT hW _ b
    (CochainComplex.projective_extendScalars_X (e n) M (fun k => (hM k).2)) eP
  let u' := (extendScalarsConstantSheafComplexIso (J := J) (e n) M).hom ≫ u
  have hU := kFlat_extendScalars_constantSheaf_complex (C := C) (J := J) (e n) M b fun k => (hM k).2
  have hPS := kFlat_extendScalars J (e n) hP
  have hu' : QuasiIso u' := inferInstance
  let R := (restrictScalars J (e n)).mapHomologicalComplex (ComplexShape.up ℤ)
  let τ := rowAdicTowerMap J (𝔞.map (e n)) u'
  refine ⟨fun j hj => (εY j hj).hom ≫ R.map (τ.app (op j)) ≫ (εX j hj).inv,
    fun j hj => ?_, fun i j hij hjn => ?_⟩
  · have : QuasiIso (R.map (τ.app (op j))) :=
      (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (restrictScalars J (e n))).2
        (quasiIso_rowComplexMap_of_kFlat (C := C) (J := J) u' hU hPS
          ((constantAdicQuotientTower J (S n) (𝔞.map (e n)) (ModuleCat.of (S n) (S n))).obj (op j)))
    show QuasiIso ((εY j hj).hom ≫ R.map (τ.app (op j)) ≫ (εX j hj).inv)
    infer_instance
  · exact comp_conj_eq_conj_comp _ (hεY i j hij hjn) (hεX i j hij hjn)
      (τ.naturality (homOfLE hij).op)

omit [IsNoetherianRing A] [∀ n, HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} (S n)))] in
include hT he hker hP hM b in
/-- **Nakayama at the level `n + 1`.** A map
`\underline{M} ⊗ \underline{A/𝔞ⁿ⁺¹} ⟶ P ⊗ \underline{A/𝔞ⁿ⁺¹}` in the homotopy category whose
reduction modulo `𝔞` is a quasi-isomorphism is a quasi-isomorphism. -/
theorem quasiIso_of_quasiIso_reduction_rowAdicTower (n : ℕ)
    (φ : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((rowAdicTower J 𝔞 (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).obj (op (n + 1))) ⟶
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ((rowAdicTower J 𝔞 P).obj (op (n + 1))))
    (ψ : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((rowAdicTower J 𝔞 (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).obj (op 1)) ⟶
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ((rowAdicTower J 𝔞 P).obj (op 1)))
    (hψ : HomotopyCategory.quasiIso _ _ ψ)
    (h : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((rowAdicTower J 𝔞 (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).map (homOfLE (Nat.le_add_left 1 n)).op) ≫ ψ =
      φ ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((rowAdicTower J 𝔞 P).map (homOfLE (Nat.le_add_left 1 n)).op)) :
    HomotopyCategory.quasiIso _ _ φ := by
  let cM := ((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  obtain ⟨εY, hεY⟩ := exists_rowAdicTower_iso_restrictScalars (J := J) (e n) (he n) 𝔞 (n + 1)
    (hker n).le cM
  obtain ⟨εX, hεX⟩ := exists_rowAdicTower_iso_restrictScalars (J := J) (e n) (he n) 𝔞 (n + 1)
    (hker n).le P
  have hU := kFlat_extendScalars_constantSheaf_complex (C := C) (J := J) (e n) M b fun k => (hM k).2
  have hPS := kFlat_extendScalars J (e n) hP
  have := (fullyFaithfulRestrictScalars J (he n)).full
  have := (fullyFaithfulRestrictScalars J (he n)).faithful
  let Rf := restrictScalars J (e n)
  let RC := Rf.mapHomologicalComplex (ComplexShape.up ℤ)
  have : RC.Full := inferInstance
  let qA := HomotopyCategory.quotient (Sheaf J (ModuleCat.{w} A)) (ComplexShape.up ℤ)
  obtain ⟨f, rfl⟩ := qA.map_surjective φ
  obtain ⟨f'', hf''⟩ := RC.map_surjective ((εY (n + 1) le_rfl).inv ≫ f ≫ (εX (n + 1) le_rfl).hom)
  have hf : f = (εY (n + 1) le_rfl).hom ≫ RC.map f'' ≫ (εX (n + 1) le_rfl).inv := by
    simp [hf'']
  have hb := Ideal.map_pow_eq_bot_of_ker_eq 𝔞 (e n) (hker n)
  let δU := rowAdicTowerObjIsoOfPowEqBot (J := J) (𝔞.map (e n)) hb
    (((extendScalars J (e n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj cM)
  let δP := rowAdicTowerObjIsoOfPowEqBot (J := J) (𝔞.map (e n)) hb
    (((extendScalars J (e n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  let χ := δU.inv ≫ f'' ≫ δP.hom
  let τ := rowAdicTowerMap J (𝔞.map (e n)) χ
  have hτ : τ.app (op (n + 1)) = f'' := by
    have hnat := rowAdicTowerObjIsoOfPowEqBot_hom_naturality (J := J) (𝔞.map (e n)) hb χ
    have h1 : τ.app (op (n + 1)) = (δU.hom ≫ χ) ≫ δP.inv := (Iso.eq_comp_inv δP).2 hnat
    rw [h1]
    simp [χ]
  have h1n : 1 ≤ n + 1 := Nat.le_add_left 1 n
  let f₁ := (εY 1 h1n).hom ≫ RC.map (τ.app (op 1)) ≫ (εX 1 h1n).inv
  have hcomp : (rowAdicTower J 𝔞 cM).map (homOfLE h1n).op ≫ f₁ =
      f ≫ (rowAdicTower J 𝔞 P).map (homOfLE h1n).op := by
    rw [hf, ← hτ]
    exact comp_conj_eq_conj_comp RC (hεY 1 (n + 1) h1n le_rfl) (hεX 1 (n + 1) h1n le_rfl)
      (τ.naturality (homOfLE h1n).op)
  have hcone : (rowAdicTowerCone J 𝔞 cM).app (op (n + 1)) ≫
        (rowAdicTower J 𝔞 cM).map (homOfLE h1n).op =
      (rowAdicTowerCone J 𝔞 cM).app (op 1) := by
    simpa using ((rowAdicTowerCone J 𝔞 cM).naturality (homOfLE h1n).op).symm
  have hψ' : ψ = qA.map f₁ := by
    apply (bijective_rowAdicTowerCone_comp (C := C) (J := J) hT 𝔞 M P (le_refl 1)).1
    show qA.map _ ≫ ψ = qA.map _ ≫ qA.map f₁
    calc _ = qA.map ((rowAdicTowerCone J 𝔞 cM).app (op (n + 1))) ≫
          qA.map ((rowAdicTower J 𝔞 cM).map (homOfLE h1n).op) ≫ ψ := by
          rw [← hcone, qA.map_comp, Category.assoc]
      _ = qA.map ((rowAdicTowerCone J 𝔞 cM).app (op (n + 1))) ≫ qA.map f ≫
            qA.map ((rowAdicTower J 𝔞 P).map (homOfLE h1n).op) := by rw [h]
      _ = qA.map ((rowAdicTowerCone J 𝔞 cM).app (op (n + 1)) ≫
            (rowAdicTower J 𝔞 cM).map (homOfLE h1n).op ≫ f₁) := by
          rw [hcomp]; simp only [Functor.map_comp]
      _ = _ := by rw [← Category.assoc, hcone, qA.map_comp]
  have hq1 : QuasiIso f₁ := (HomotopyCategory.quotient_map_mem_quasiIso_iff f₁).1 (hψ' ▸ hψ)
  have hq2 : QuasiIso (RC.map (τ.app (op 1))) := by
    have : QuasiIso ((εY 1 h1n).hom ≫ RC.map (τ.app (op 1)) ≫ (εX 1 h1n).inv) := hq1
    rwa [quasiIso_iff_comp_left, quasiIso_iff_comp_right] at this
  have hq3 : QuasiIso (τ.app (op 1)) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ Rf).1 hq2
  have hχ : QuasiIso χ := quasiIso_of_quasiIso_rowAdicTowerMap_app_one (C := C) (J := J)
    (𝔞.map (e n)) ⟨n + 1, hb⟩ χ hU hPS hq3
  have hf'' : f'' = δU.hom ≫ χ ≫ δP.inv := by simp [χ]
  have hq4 : QuasiIso f'' := by rw [hf'']; infer_instance
  have hq5 : QuasiIso (RC.map f'') :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ Rf).2 hq4
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff, hf]
  infer_instance

include hT hW he hker hP hM a b in
/-- **The selection.** Non-compatible isomorphisms `S_n ⊗ P ≅ \underline{S_n ⊗ M}` for all `n`
give a morphism of towers `\underline{M} ⊗ \underline{A/𝔞ʲ} ⟶ P ⊗ \underline{A/𝔞ʲ}` in the
homotopy category all of whose components are quasi-isomorphisms. -/
theorem exists_natTrans_rowAdicTower_quasiIso
    (h : ∀ n, Nonempty (DerivedCategory.Q.obj
        (((extendScalars J (e n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj (((constantSheaf J (ModuleCat.{w} (S n))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{w, w, w} (e n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)))) :
    ∃ φ : rowAdicTower J 𝔞 (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⟶
        rowAdicTower J 𝔞 P ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ),
      ∀ j, HomotopyCategory.quasiIso _ _ (φ.app (op j)) := by
  let q := HomotopyCategory.quotient (Sheaf J (ModuleCat.{w} A)) (ComplexShape.up ℤ)
  let cM := ((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  let p : (Functor.const ℕᵒᵖ).obj (q.obj cM) ⟶ rowAdicTower J 𝔞 cM ⋙ q :=
    (Functor.constComp ℕᵒᵖ cM q).inv ≫ Functor.whiskerRight (rowAdicTowerCone J 𝔞 cM) q
  have hpapp : ∀ j, p.app j = q.map ((rowAdicTowerCone J 𝔞 cM).app j) := fun j => by
    simp [p]
  refine Functor.exists_natTrans_forall_of_isMittagLeffler (HomotopyCategory.quasiIso _ _) p
    (fun i j hij => ?_) (fun w hw => ?_) (fun n => ?_) ?_ 1 (fun j hj φ => ?_)
    (fun j hj φ ψ hψ hφψ => ?_)
  · simp only [hpapp]
    exact bijective_rowAdicTowerCone_comp (C := C) (J := J) hT 𝔞 M P hij
  · exact bijective_comp_quasiIso_of_constantSheaf (C := C) (J := J) (R := A) hT hW M b
      (fun k => (hM k).2) w hw
  · obtain ⟨g, hg, hgc⟩ := exists_quasiIso_rowAdicTower_le (C := C) (J := J) hT hW 𝔞 e he hker hP
      M b hM n (h n)
    refine ⟨fun j hj => q.map (g j (hj.trans n.le_succ)), fun j hj => ?_, fun i j hij hjn => ?_⟩
    · rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
      exact hg j _
    · show q.map _ ≫ q.map _ = q.map _ ≫ q.map _
      rw [← q.map_comp, ← q.map_comp, hgc i j hij (hjn.trans n.le_succ)]
  · exact isMittagLeffler_coyoneda_rowAdicTower_constantSheaf (C := C) (J := J) hT hW 𝔞 M a b hM
  · obtain rfl : j = 0 := Nat.lt_one_iff.1 hj
    exact HomotopyCategory.quasiIso_of_acyclic (acyclic_rowAdicTower_obj_zero (C := C) (J := J) _ _)
      (acyclic_rowAdicTower_obj_zero (C := C) (J := J) _ _) φ
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    exact quasiIso_of_quasiIso_reduction_rowAdicTower (C := C) (J := J) hT 𝔞 e he hker hP M b hM
      n φ ψ hψ hφψ

end Core

section Final

variable {Λ : Type w} [CommRing Λ] (I : Ideal Λ)
  [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
  [∀ n : ℕ, HasDerivedCategory.{t'} (Sheaf J (ModuleCat.{w} (Λ ⧸ I ^ n)))]

/-- **Non-compatible isomorphisms with constant complexes give an isomorphism of towers.** On a
site with a final object `T` over which sections are exact, let `P` be K-flat and `M` a bounded
complex of finite projective `Λ^∧`-modules with isomorphisms `Λ/Iⁿ⁺¹ ⊗ P ≅ \underline{Λ/Iⁿ⁺¹ ⊗ M}`
in `D(C, Λ/Iⁿ⁺¹)` for all `n`, not assumed compatible. Then the derived reductions of `P` form a
tower isomorphic to `n ↦ \underline{M/IⁿM}` in `D(C, Λ)`. -/
theorem nonempty_derivedReductionTower_iso_of_isWeaklyContractible [IsNoetherianRing Λ]
    {T : C} (hT : IsTerminal T)
    (hW : ∀ {F G : Sheaf J (Type w)} (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op T)))
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P)
    (M : CochainComplex (ModuleCat.{w} (AdicCompletion I Λ)) ℤ) (a b : ℤ)
    [M.IsStrictlyGE a] [M.IsStrictlyLE b]
    (hM : ∀ k, Module.Finite (AdicCompletion I Λ) (M.X k) ∧
      Module.Projective (AdicCompletion I Λ) (M.X k))
    (h : ∀ n : ℕ, Nonempty (DerivedCategory.Q.obj
        (((extendScalars J (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj (((constantSheaf J
          (ModuleCat.{w} (Λ ⧸ I ^ (n + 1)))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)))) :
    Nonempty (derivedReductionTower J Λ I (DerivedCategory.Q.obj P) ≅
      constantAdicQuotientComplexTower J Λ I
        (((ModuleCat.restrictScalars (algebraMap Λ (AdicCompletion I Λ))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ⋙ DerivedCategory.Q) := by
  let := HasDerivedCategory.standard (Sheaf J (ModuleCat.{w} (AdicCompletion I Λ)))
  have hI : I.FG := IsNoetherian.noetherian I
  have hP' := kFlat_extendScalars J (algebraMap Λ (AdicCompletion I Λ)) hP
  have h' : ∀ n : ℕ, Nonempty (DerivedCategory.Q.obj
      (((extendScalars J (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((extendScalars J
            (algebraMap Λ (AdicCompletion I Λ))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) ≅
      DerivedCategory.Q.obj (((constantSheaf J
          (ModuleCat.{w} (Λ ⧸ I ^ (n + 1)))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{w, w, w}
            (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M))) := by
    intro n
    obtain ⟨e⟩ := h n
    have key : ∀ f : Λ →+* Λ ⧸ I ^ (n + 1), f = Ideal.Quotient.mk (I ^ (n + 1)) →
        Nonempty (DerivedCategory.Q.obj
          (((extendScalars J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
        DerivedCategory.Q.obj (((constantSheaf J
            (ModuleCat.{w} (Λ ⧸ I ^ (n + 1)))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{w, w, w}
            (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M))) := by
      rintro f rfl
      exact ⟨e⟩
    obtain ⟨e'⟩ := key _ (AdicCompletion.evalₐ I (n + 1)).comp_algebraMap
    exact ⟨DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso (Iso.refl _)
      (ComplexShape.up ℤ)).app P ≪≫ (NatIso.mapHomologicalComplex
        (extendScalarsCompExtendScalarsIso (J := J) (algebraMap Λ (AdicCompletion I Λ))
          (AdicCompletion.evalₐ I (n + 1)).toRingHom) (ComplexShape.up ℤ)).app P) ≪≫ e'⟩
  obtain ⟨φ, hφ⟩ := exists_natTrans_rowAdicTower_quasiIso (C := C) (J := J)
    (A := AdicCompletion I Λ) hT hW (I.map (algebraMap Λ (AdicCompletion I Λ)))
    (S := fun n => Λ ⧸ I ^ (n + 1)) (fun n => (AdicCompletion.evalₐ I (n + 1)).toRingHom)
    (fun n => AdicCompletion.surjective_evalₐ I (n + 1))
    (fun n => AdicCompletion.ker_evalₐ I hI (n + 1)) hP' M a b hM h'
  obtain ⟨ψ⟩ := DerivedCategory.nonempty_iso_of_natTrans_quasiIso φ fun j => hφ j.unop
  exact nonempty_derivedReductionTower_iso_of_rowAdicTower_iso (C := C) (J := J) I hP M ψ.symm

end Final

end Stacks.ModuleSheaf
