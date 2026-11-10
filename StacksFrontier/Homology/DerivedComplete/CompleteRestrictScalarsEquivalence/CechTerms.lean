module

public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.DerivedAdjunction
import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections
import all StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence.DerivedAdjunction

/-!
# Hom-sets out of Čech terms into derived complete complexes

Second part of `StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence`.
It contains the Hom-vanishing and bijectivity statements for maps from (mapped) Čech terms of a
finite sequence of elements of `I` into derived complete complexes, derived completeness of
images and shifts, and the comparison of the derived unit on Hom-sets with the degreewise unit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe uA uB v u w

namespace CompleteRestrictScalarsEquivalence

set_option backward.isDefEq.respectTransparency false


open StacksDraft.TotalComplexQuasiIso
open scoped ZeroObject

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open scoped DirectSum

private theorem subsingleton_hom_cechTerm
    (A : Type u) [CommRing A] (I : Ideal A) {r : ℕ} (f : Fin r → A)
    (hf : ∀ i, f i ∈ I) (M : Type (max u v)) [AddCommGroup M] [Module A M]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A))]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (hK : IsDerivedComplete I K)
    (q : ℕ) (hq : q ≠ 0) (p n : ℤ) :
    Subsingleton (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{max u v} A) (ComplexShape.up ℤ) p).obj
        (ModuleCat.of A (Cech.cechTerm f M q))) ⟶ K⟦n⟧) := by
  classical
  apply subsingleton_hom_map_directSum
    (fun s : {s : Finset (Fin r) // s.card = q} => Cech.cechMod f M s.val)
    ((HomologicalComplex.single (ModuleCat.{max u v} A) (ComplexShape.up ℤ) p) ⋙
      DerivedCategory.Q) (K⟦n⟧)
  intro s
  have hs : s.val.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hs
  apply subsingleton_hom_single_of_isUnit_smul A I K hK (∏ j ∈ s.val, f j)
    (I.prod_mem (f := f) hi (hf i))
  exact IsLocalizedModule.map_units (S := Cech.cechSub f s.val)
    (LocalizedModule.mkLinearMap (Cech.cechSub f s.val) M)
    ⟨_, Submonoid.mem_powers _⟩

private theorem isZero_cechTerm_of_gt
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A)
    (M : Type v) [AddCommGroup M] [Module A M] (p : ℕ) (hp : r < p) :
    IsZero ((Cech.cechComplex f M).X p) := by
  let : IsEmpty {s : Finset (Fin r) // s.card = p} := ⟨fun s => by
    have := s.val.card_le_univ
    simp only [Fintype.card_fin, s.property] at this
    omega⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (inferInstanceAs (Subsingleton (Cech.cechTerm f M p)))

/-- The extension by zero of an `ℕ`-indexed complex vanishes in negative degrees. -/
private theorem isZero_extend_X_embeddingUpNat_of_neg
    {V : Type*} [Category V] [Preadditive V] [HasZeroObject V]
    (C : CochainComplex V ℕ) {p : ℤ} (hp : p < 0) :
    IsZero ((C.extend ComplexShape.embeddingUpNat).X p) := by
  apply HomologicalComplex.isZero_extend_X
  intro n hn
  have : (n : ℤ) = p := hn
  omega

/-- The extension by zero of an `ℕ`-indexed complex vanishes in negative degrees and in degrees
above any bound beyond which the complex vanishes. -/
private theorem isZero_extend_X_embeddingUpNat
    {V : Type*} [Category V] [Preadditive V] [HasZeroObject V]
    (C : CochainComplex V ℕ) {r : ℕ} (hC : ∀ n : ℕ, r < n → IsZero (C.X n)) (p : ℤ)
    (hp : p < 0 ∨ (r : ℤ) < p) : IsZero ((C.extend ComplexShape.embeddingUpNat).X p) := by
  rcases hp with hp | hp
  · exact isZero_extend_X_embeddingUpNat_of_neg C hp
  · have hnonneg : 0 ≤ p := by omega
    have he : ComplexShape.embeddingUpNat.f p.toNat = p := by simp [hnonneg]
    exact (hC p.toNat (by omega)).of_iso (C.extendXIso ComplexShape.embeddingUpNat he)

/-- Maps out of a single-degree term of the extension by zero of an `ℕ`-indexed complex vanish
(up to uniqueness) as soon as they do in the corresponding nonnegative degrees. -/
private theorem subsingleton_hom_single_extend_X
    {V : Type*} [Category V] [Abelian V] [HasDerivedCategory V]
    (C : CochainComplex V ℕ) (K : DerivedCategory V) (p n : ℤ)
    (h : 0 ≤ p → Subsingleton (DerivedCategory.Q.obj
      ((HomologicalComplex.single V (ComplexShape.up ℤ) p).obj (C.X p.toNat)) ⟶ K⟦n⟧)) :
    Subsingleton (DerivedCategory.Q.obj
      ((HomologicalComplex.single V (ComplexShape.up ℤ) p).obj
        ((C.extend ComplexShape.embeddingUpNat).X p)) ⟶ K⟦n⟧) := by
  by_cases hnonneg : 0 ≤ p
  · have he : ComplexShape.embeddingUpNat.f p.toNat = p := by simp [hnonneg]
    have := h hnonneg
    exact (Iso.homCongr (DerivedCategory.Q.mapIso
      ((HomologicalComplex.single V (ComplexShape.up ℤ) p).mapIso
        (C.extendXIso ComplexShape.embeddingUpNat he))) (Iso.refl _)).injective.subsingleton
  · exact ⟨fun g h => (DerivedCategory.Q.map_isZero
      ((HomologicalComplex.single V (ComplexShape.up ℤ) p).map_isZero
        (isZero_extend_X_embeddingUpNat_of_neg C (not_le.mp hnonneg)))).eq_of_src g h⟩

private theorem cech_column_bounds
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A)
    (M : Type v) [AddCommGroup M] [Module A M] (p : ℤ) (hp : p < 0 ∨ (r : ℤ) < p) :
    IsZero (((Cech.cechComplex f M).extend ComplexShape.embeddingUpNat).X p) :=
  isZero_extend_X_embeddingUpNat _ (isZero_cechTerm_of_gt A f M) p hp

private theorem bijective_precomp_cech_bottomProjection
    (A : Type u) [CommRing A] (I : Ideal A) {r : ℕ} (f : Fin r → A)
    (hf : ∀ i, f i ∈ I) (M : Type (max u v)) [AddCommGroup M] [Module A M]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A))]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (hK : IsDerivedComplete I K) :
    let C := (Cech.cechComplex f M).extend ComplexShape.embeddingUpNat
    let ha : IsZero (C.X (0 - 1)) := cech_column_bounds A f M _ (Or.inl (by norm_num))
    Function.Bijective (fun g : DerivedCategory.Q.obj
        ((HomologicalComplex.single (ModuleCat.{max u v} A) (ComplexShape.up ℤ) 0).obj (C.X 0)) ⟶ K
          =>
      DerivedCategory.Q.map (bottomProjection C 0 ha) ≫ g) := by
  dsimp only
  apply bijective_precomp_bottomProjection _ 0 r (cech_column_bounds A f M) K
  intro p hp n
  exact subsingleton_hom_single_extend_X _ K p n fun hnonneg =>
    subsingleton_hom_cechTerm A I f hf M K hK p.toNat (by omega) p n



open scoped ModuleCat.Algebra

private theorem subsingleton_hom_map_cechTerm
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {r : ℕ} (f : Fin r → A) (hf : ∀ i, f i ∈ I)
    (M : Type w) [AddCommGroup M] [Module B M]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (F : ModuleCat.{max uB w} B ⥤ DerivedCategory (ModuleCat.{v} A))
    [F.Additive] [F.Linear A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDerivedComplete I K)
    (q : ℕ) (hq : q ≠ 0) (n : ℤ) :
    Subsingleton (F.obj (ModuleCat.of B
      (Cech.cechTerm (fun i => algebraMap A B (f i)) M q)) ⟶ K⟦n⟧) := by
  classical
  let g := fun i => algebraMap A B (f i)
  apply subsingleton_hom_map_directSum
    (fun s : {s : Finset (Fin r) // s.card = q} => Cech.cechMod g M s.val)
    F (K⟦n⟧)
  intro s
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < s.val.card by omega)
  let a := ∏ j ∈ s.val, f j
  have ha : a ∈ I := I.prod_mem (f := f) hi (hf i)
  have hu : IsUnit (algebraMap B (Module.End B (Cech.cechMod g M s.val))
      (algebraMap A B a)) := by
    have h := IsLocalizedModule.map_units (S := Cech.cechSub g s.val)
      (LocalizedModule.mkLinearMap (Cech.cechSub g s.val) M)
      ⟨∏ j ∈ s.val, g j, Submonoid.mem_powers _⟩
    simpa only [a, g, map_prod] using h
  have hm : IsIso (a • 𝟙 (ModuleCat.of B (Cech.cechMod g M s.val))) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun x : Cech.cechMod g M s.val => algebraMap A B a • x)
    have he : (⇑(algebraMap B (Module.End B (Cech.cechMod g M s.val))
        (algebraMap A B a))) = (fun x => algebraMap A B a • x) := by
      funext x
      exact Module.algebraMap_end_apply B B (Cech.cechMod g M s.val) (algebraMap A B a) x
    rw [← he]
    exact (Module.End.isUnit_iff _).mp hu
  apply subsingleton_hom_shift_of_isIso_smul I hK ha _ n
  rw [← F.map_id, ← F.map_smul]
  infer_instance

private theorem mapped_cech_column_bounds
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B]
    {r : ℕ} (f : Fin r → B) (M : Type w) [AddCommGroup M] [Module B M]
    (F : ModuleCat.{max uB w} B ⥤ ModuleCat.{v} A) [F.Additive]
    (p : ℤ) (hp : p < 0 ∨ (r : ℤ) < p) :
    IsZero ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Cech.cechComplex f M)).extend ComplexShape.embeddingUpNat).X p) :=
  isZero_extend_X_embeddingUpNat _
    (fun n hn => F.map_isZero (isZero_cechTerm_of_gt B f M n hn)) p hp

private theorem subsingleton_hom_mapped_cech_column
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {r : ℕ} (f : Fin r → A) (hf : ∀ i, f i ∈ I)
    (M : Type w) [AddCommGroup M] [Module B M]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (F : ModuleCat.{max uB w} B ⥤ ModuleCat.{v} A) [F.Additive] [F.Linear A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDerivedComplete I K) (p : ℤ) (hp : p ≠ 0) (n :
      ℤ) :
    Subsingleton (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{v} A) (ComplexShape.up ℤ) p).obj
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (Cech.cechComplex (fun i => algebraMap A B (f i)) M)).extend
            ComplexShape.embeddingUpNat).X p)) ⟶ K⟦n⟧) := by
  refine subsingleton_hom_single_extend_X _ K p n fun hnonneg => ?_
  exact subsingleton_hom_map_cechTerm A B I f hf M
    (F ⋙ CochainComplex.singleFunctor (ModuleCat.{v} A) p ⋙ DerivedCategory.Q)
    K hK p.toNat (by omega) n


private theorem bijective_precomp_mapped_cech_bottomProjection
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {r : ℕ} (f : Fin r → A) (hf : ∀ i, f i ∈ I)
    (M : Type w) [AddCommGroup M] [Module B M]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (F : ModuleCat.{max uB w} B ⥤ ModuleCat.{v} A) [F.Additive] [F.Linear A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDerivedComplete I K) :
    let C := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Cech.cechComplex (fun i => algebraMap A B (f i)) M)).extend
        ComplexShape.embeddingUpNat
    let ha : IsZero (C.X (0 - 1)) := mapped_cech_column_bounds A B _ M F _
      (Or.inl (by norm_num))
    Function.Bijective (fun g : DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{v} A) (ComplexShape.up ℤ) 0).obj
        (C.X 0)) ⟶ K => DerivedCategory.Q.map (bottomProjection C 0 ha) ≫ g) := by
  dsimp only
  apply bijective_precomp_bottomProjection _ 0 r
    (mapped_cech_column_bounds A B _ M F) K
  exact subsingleton_hom_mapped_cech_column A B I f hf M F K hK


private noncomputable def cechTermZeroMap
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (M : Type v) [AddCommGroup M] [Module R M] : M →ₗ[R] Cech.cechTerm f M 0 :=
  (DirectSum.lof R {s : Finset (Fin r) // s.card = 0}
    (fun s => Cech.cechMod f M s.val) ⟨∅, Finset.card_empty⟩).comp
      (LocalizedModule.mkLinearMap (Cech.cechSub f ∅) M)

private theorem cechTermZeroMap_apply
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (M : Type v) [AddCommGroup M] [Module R M] (x : M) :
    cechTermZeroMap f M x = DirectSum.lof R {s : Finset (Fin r) // s.card = 0}
      (fun s => Cech.cechMod f M s.val) ⟨∅, Finset.card_empty⟩
      (LocalizedModule.mk x 1) := rfl

private theorem bijective_cechTermZeroMap
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Bijective (cechTermZeroMap f M) := by
  classical
  have hu (y : Cech.cechSub f ∅) : y = 1 := by
    apply Subtype.ext
    obtain ⟨n, hn⟩ := y.property
    simpa using hn.symm
  constructor
  · intro x y hxy
    have h := congrArg (DirectSum.component R {s : Finset (Fin r) // s.card = 0}
      (fun s => Cech.cechMod f M s.val) ⟨∅, Finset.card_empty⟩) hxy
    simp only [cechTermZeroMap_apply, DirectSum.component.lof_self] at h
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
      (S := Cech.cechSub f ∅) (f := LocalizedModule.mkLinearMap (Cech.cechSub f ∅) M) h
    rw [hu c] at hc
    simpa using hc
  · intro z
    induction z using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add _ _ _⟩
    | of s x =>
      obtain rfl : s = ⟨∅, Finset.card_empty⟩ :=
        Subtype.ext (Finset.card_eq_zero.mp s.property)
      induction x using LocalizedModule.induction_on with
      | _ x y =>
        rw [hu y]
        exact ⟨x, rfl⟩

open HomologicalComplex

private theorem isDerivedComplete_map
    (A : Type u) [CommRing A] (I : Ideal A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{w} A))]
    (F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{w} A))
    [F.Additive] [F.Linear A]
    (K : DerivedCategory (ModuleCat.{v} A))
    [PreservesLimit (Discrete.functor (fun _ : ℕ => K)) F]
    (hK : IsDerivedComplete I K) :
    IsDerivedComplete I (F.obj K) := by
  rw [isDerivedComplete_iff_isIso_difference] at hK ⊢
  intro f hf
  let dK := Pi.lift (fun n : ℕ => Pi.π (fun _ : ℕ => K) n -
    Pi.π (fun _ : ℕ => K) (n + 1) ≫ (f • 𝟙 K))
  let dL := Pi.lift (fun n : ℕ => Pi.π (fun _ : ℕ => F.obj K) n -
    Pi.π (fun _ : ℕ => F.obj K) (n + 1) ≫ (f • 𝟙 (F.obj K)))
  let e := piComparison F (fun _ : ℕ => K)
  have he : F.map dK ≫ e = e ≫ dL := by
    apply Pi.hom_ext
    intro n
    simp only [e, dL, Category.assoc, piComparison_comp_π, limit.lift_π,
      Fan.mk_π_app, Preadditive.comp_sub]
    rw [← F.map_comp]
    simp only [dK, limit.lift_π, Fan.mk_π_app, Functor.map_sub, Functor.map_comp,
      Functor.map_smul]
    rw [F.map_id K, ← Category.assoc, piComparison_comp_π]
  have : IsIso dK := hK f hf
  have : IsIso (e ≫ dL) := by rw [← he]; infer_instance
  exact IsIso.of_isIso_comp_left e dL

private theorem isDerivedComplete_shift
    (A : Type u) [CommRing A] (I : Ideal A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDerivedComplete I K)
    (n : ℤ) : IsDerivedComplete I (K⟦n⟧) :=
  isDerivedComplete_map A I (shiftFunctor _ n) K hK

private theorem bijective_precomp_of_iso_square
    {C : Type*} [Category C] {X Y X' Y' : C}
    (f : X ⟶ Y) (g : X' ⟶ Y') (i : X ≅ X') (j : Y ≅ Y')
    (h : i.hom ≫ g = f ≫ j.hom) (Z : C)
    (hg : Function.Bijective (fun a : Y' ⟶ Z => g ≫ a)) :
    Function.Bijective (fun a : Y ⟶ Z => f ≫ a) := by
  have hi : Function.Bijective (fun a : X' ⟶ Z => i.hom ≫ a) :=
    (Iso.homFromEquiv i.symm).bijective
  have hj : Function.Bijective (fun a : Y' ⟶ Z => j.hom ≫ a) :=
    (Iso.homFromEquiv j.symm).bijective
  have hh := hi.comp hg
  have he : (fun a : Y' ⟶ Z => i.hom ≫ (g ≫ a)) =
      (fun a : Y' ⟶ Z => f ≫ (j.hom ≫ a)) := by
    funext a
    simp only [← Category.assoc, h]
  change Function.Bijective (fun a : Y' ⟶ Z => i.hom ≫ (g ≫ a)) at hh
  rw [he] at hh
  exact (Function.Bijective.of_comp_iff _ hj).mp hh

private theorem bijective_precomp_cechMap_zero
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {r : ℕ} (f : Fin r → A) (hf : ∀ i, f i ∈ I)
    (c : ((ModuleCat.uliftFunctor.{uB} A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Cech.cechComplex f A) ⟶
      ((ModuleCat.uliftFunctor.{uA} B ⋙ ModuleCat.restrictScalars (algebraMap A
        B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (Cech.cechComplex (fun i => algebraMap A B (f i)) B))
    [QuasiIso c]
    (H : ModuleCat.{max uA uB} A ⥤ ModuleCat.{v} A)
    [H.Additive] [H.Linear A] [H.PreservesHomology]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDerivedComplete I K) :
    Function.Bijective (fun g : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{v} A) 0).obj (H.obj ((CategoryTheory.Arrow.mk
        c).right.X 0))) ⟶ K =>
        DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{v} A) 0).map
          (H.map (c.f 0))) ≫ g) := by
  let : (ModuleCat.uliftFunctor.{uA} B).Linear A := {
    map_smul := by intros; ext; rfl }
  let : (ModuleCat.restrictScalars.{max uA uB} (algebraMap A B)).Linear A := {
    map_smul := by intros; ext; rfl }
  let d := (H.mapHomologicalComplex (ComplexShape.up ℕ)).map c
  let de := HomologicalComplex.extendMap d ComplexShape.embeddingUpNat
  have : QuasiIso de := (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr inferInstance
  have hd := bijective_precomp_single_map_of_quasiIso de 0 r
    (mapped_cech_column_bounds A A f A (ModuleCat.uliftFunctor.{uB} A ⋙ H))
    (mapped_cech_column_bounds A B (fun i => algebraMap A B (f i)) B
      (ModuleCat.uliftFunctor.{uA} B ⋙ ModuleCat.restrictScalars (algebraMap A B) ⋙ H)) K
    (subsingleton_hom_mapped_cech_column A A I f hf A
      (ModuleCat.uliftFunctor.{uB} A ⋙ H) K hK)
    (subsingleton_hom_mapped_cech_column A B I f hf B
      (ModuleCat.uliftFunctor.{uA} B ⋙ ModuleCat.restrictScalars (algebraMap A B) ⋙ H) K hK)
  let S := CochainComplex.singleFunctor (ModuleCat.{v} A) (0 : ℤ) ⋙ DerivedCategory.Q
  let eX := ((CategoryTheory.Arrow.mk d).left).extendXIso ComplexShape.embeddingUpNat (i := 0) (i'
    := 0) (by rfl)
  let eY := ((CategoryTheory.Arrow.mk d).right).extendXIso ComplexShape.embeddingUpNat (i := 0) (i'
    := 0) (by rfl)
  apply bijective_precomp_of_iso_square _ (S.map (de.f 0))
    (S.mapIso eX.symm) (S.mapIso eY.symm) _ K hd
  change S.map eX.inv ≫ S.map (de.f 0) = S.map (d.f 0) ≫ S.map eY.inv
  rw [← S.map_comp, ← S.map_comp]
  congr 1
  change eX.inv ≫ (HomologicalComplex.extendMap d ComplexShape.embeddingUpNat).f 0 = _
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by rfl)]
  change eX.inv ≫ (eX.hom ≫ d.f 0 ≫ eY.inv) = _
  simp only [Iso.inv_hom_id_assoc]


private theorem bijective_precomp_algebraMap_of_cechMap
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) {r : ℕ} (f : Fin r → A) (hf : ∀ i, f i ∈ I)
    (c : ((ModuleCat.uliftFunctor.{uB} A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Cech.cechComplex f A) ⟶
      ((ModuleCat.uliftFunctor.{uA} B ⋙ ModuleCat.restrictScalars (algebraMap A
        B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (Cech.cechComplex (fun i => algebraMap A B (f i)) B))
    [QuasiIso c]
    (hc : ∀ x : A, c.f 0 (ULift.up (cechTermZeroMap f A x)) =
      ULift.up (cechTermZeroMap (fun i => algebraMap A B (f i)) B (algebraMap A B x)))
    (g : (ModuleCat.uliftFunctor.{uB} A).obj (ModuleCat.of A A) ⟶
      (ModuleCat.uliftFunctor.{uA} B ⋙ ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B B))
    (hg : ∀ x : A, g (ULift.up x) = ULift.up (algebraMap A B x))
    (H : ModuleCat.{max uA uB} A ⥤ ModuleCat.{v} A)
    [H.Additive] [H.Linear A] [H.PreservesHomology]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDerivedComplete I K) :
    Function.Bijective (fun a : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{v} A) 0).obj
        (H.obj ((Arrow.mk g).right))) ⟶ K =>
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{v} A) 0).map
        (H.map g)) ≫ a) := by
  let eA : (Arrow.mk g).left ≅ (Arrow.mk c).left.X 0 :=
    (ModuleCat.uliftFunctor.{uB} A).mapIso
      (LinearEquiv.ofBijective (cechTermZeroMap f A) (bijective_cechTermZeroMap f A)).toModuleIso
  let eB : (Arrow.mk g).right ≅ (Arrow.mk c).right.X 0 :=
    (ModuleCat.uliftFunctor.{uA} B ⋙ ModuleCat.restrictScalars (algebraMap A B)).mapIso
      (LinearEquiv.ofBijective (cechTermZeroMap (fun i => algebraMap A B (f i)) B)
        (bijective_cechTermZeroMap _ B)).toModuleIso
  have he : eA.hom ≫ c.f 0 = g ≫ eB.hom := by
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨x⟩ := x
    change c.f 0 (ULift.up (cechTermZeroMap f A x)) = eB.hom (g (ULift.up x))
    rw [hg, hc]
    rfl
  let S := H ⋙ CochainComplex.singleFunctor (ModuleCat.{v} A) (0 : ℤ) ⋙ DerivedCategory.Q
  apply bijective_precomp_of_iso_square _ (S.map (c.f 0))
    (S.mapIso eA) (S.mapIso eB) _ K
    (bijective_precomp_cechMap_zero A B I f hf c H K hK)
  change S.map eA.hom ≫ S.map (c.f 0) = S.map g ≫ S.map eB.hom
  rw [← S.map_comp, ← S.map_comp, he]

private theorem bijective_precomp_algebraMap
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map))
    (g : (ModuleCat.uliftFunctor.{uB} A).obj (ModuleCat.of A A) ⟶
      (ModuleCat.uliftFunctor.{uA} B ⋙ ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B B))
    (hg : ∀ x : A, g (ULift.up x) = ULift.up (algebraMap A B x))
    (H : ModuleCat.{max uA uB} A ⥤ ModuleCat.{v} A)
    [H.Additive] [H.Linear A] [H.PreservesHomology]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDerivedComplete I K) :
    Function.Bijective (fun a : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{v} A) 0).obj
        (H.obj ((Arrow.mk g).right))) ⟶ K =>
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{v} A) 0).map
        (H.map g)) ≫ a) := by
  obtain ⟨r, f, hspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  have hspan' : Ideal.span (Set.range f) = I := hspan
  have hf (i : Fin r) : f i ∈ I := by
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨_, _, _, c, hc, hqc⟩ :=
    FormalGlueing.quasiIso_koszulSeq_and_cechComplex_baseChange A B I hI hflat hquot f
      (by rw [hspan'])
  let : QuasiIso c := hqc
  apply bijective_precomp_algebraMap_of_cechMap A B I f hf c _ g hg H K hK
  intro x
  have hh := hc 0 ⟨∅, Finset.card_empty⟩ x 1
  have hy (h : (1 : B) ∈ Cech.cechSub (fun i => algebraMap A B (f i)) ∅) :
      (⟨1, h⟩ : Cech.cechSub (fun i => algebraMap A B (f i)) ∅) = 1 :=
    Subtype.ext (Submonoid.coe_one _).symm
  simpa only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj,
    cechTermZeroMap_apply, Submonoid.coe_one, map_one, hy] using hh

private theorem hom_homology_eq_zero_of_single_hom_eq_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (I : CochainComplex C ℤ) (P : C) [Projective P] (n : ℤ)
    (h : ∀ f : (DerivedCategory.singleFunctor C n).obj P ⟶ DerivedCategory.Q.obj I,
      f = 0) (f : P ⟶ I.homology n) : f = 0 := by
  let g := Projective.factorThru f (I.homologyπ n)
  let φ := mkHomFromSingle (g ≫ I.iCycles n) (fun j _ => by simp)
  have hφ : homologyMap φ n = 0 := by
    rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors C n).hom.app
      ((CochainComplex.singleFunctor C n).obj P))]
    rw [← DerivedCategory.homologyFunctorFactors_hom_naturality,
      h (DerivedCategory.Q.map φ), Functor.map_zero, zero_comp, comp_zero]
  have hc : (singleObjCyclesSelfIso (.up ℤ) n P).inv ≫ cyclesMap φ n = g := by
    rw [← cancel_mono (I.iCycles n), Category.assoc, cyclesMap_i]
    dsimp [φ]
    simp only [mkHomFromSingle_f, ← Category.assoc, singleObjCyclesSelfIso_inv_iCycles,
      Iso.inv_hom_id, Category.id_comp]
  rw [← Projective.factorThru_comp f (I.homologyπ n)]
  change g ≫ I.homologyπ n = 0
  rw [← hc, Category.assoc, ← homologyπ_naturality, hφ, comp_zero, comp_zero]

private theorem isZero_of_single_hom_eq_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [Projective P] (hP : ∀ X : C, (∀ f : P ⟶ X, f = 0) → IsZero X)
    (K : DerivedCategory C)
    (hK : ∀ n : ℤ, ∀ f : (DerivedCategory.singleFunctor C n).obj P ⟶ K, f = 0) :
    IsZero K := by
  let I := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  have hI (n : ℤ) : IsZero (I.homology n) := by
    apply hP
    apply hom_homology_eq_zero_of_single_hom_eq_zero
    intro f
    apply (cancel_mono e.hom).mp
    simpa only [zero_comp] using hK n (f ≫ e.hom)
  have hHK (n : ℤ) : IsZero ((DerivedCategory.homologyFunctor C n).obj K) :=
    (hI n).of_iso (((DerivedCategory.homologyFunctor C n).mapIso e.symm) ≪≫
      (DerivedCategory.homologyFunctorFactors C n).app I)
  have : IsIso (0 : K ⟶ K) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    rw [Functor.map_zero]
    exact (hHK n).isIso (hHK n) _
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_epi (0 : K ⟶ K)).mp
  simp


private theorem isIso_of_bijective_single_postcomp
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [Projective P] (hP : ∀ X : C, (∀ f : P ⟶ X, f = 0) → IsZero X)
    {X Y : DerivedCategory C} (f : X ⟶ Y)
    (hf : ∀ n : ℤ, Function.Bijective
      (fun a : (DerivedCategory.singleFunctor C n).obj P ⟶ X => a ≫ f)) : IsIso f := by
  have hinj (n : ℤ) : Function.Injective
      (fun a : (DerivedCategory.singleFunctor C n).obj P ⟶ X⟦(1 : ℤ)⟧ => a ≫ f⟦1⟧') := by
    intro a b hab
    let F := shiftFunctor (DerivedCategory C) (1 : ℤ)
    let e := ((DerivedCategory.singleFunctors C).shiftIso 1 n (n + 1) (by omega)).app P
    obtain ⟨a', ha'⟩ := F.map_surjective (e.hom ≫ a)
    obtain ⟨b', hb'⟩ := F.map_surjective (e.hom ≫ b)
    apply (cancel_epi e.hom).mp
    rw [← ha', ← hb']
    apply congrArg F.map
    apply (hf (n + 1)).injective
    apply F.map_injective
    simp only [Functor.map_comp, ha', hb', Category.assoc]
    exact congrArg (fun k => e.hom ≫ k) hab
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle f
  have hZ : IsZero Z := by
    apply isZero_of_single_hom_eq_zero P hP
    intro n a
    let T := Triangle.mk f g δ
    have ha : a ≫ δ = 0 := by
      apply hinj n
      simp only [Category.assoc, zero_comp]
      have hz : δ ≫ f⟦1⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
      rw [hz, comp_zero]
    obtain ⟨b, hb⟩ := T.coyoneda_exact₃ hT a ha
    obtain ⟨c, hc⟩ := (hf n).surjective b
    rw [hb, ← hc, Category.assoc]
    change c ≫ f ≫ g = 0
    have hz : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
    rw [hz, comp_zero]
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).mp hZ

private theorem isZero_module_of_ulift_hom_eq_zero
    (A : Type u) [CommRing A] (M : ModuleCat.{max u v} A)
    (h : ∀ f : ModuleCat.of A (ULift.{v} A) ⟶ M, f = 0) : IsZero M := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  let f : ModuleCat.of A (ULift.{v} A) ⟶ M :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton A M x).comp ULift.moduleEquiv.toLinearMap)
  have hx := congrArg (fun g : ModuleCat.of A (ULift.{v} A) ⟶ M => g (ULift.up 1)) (h f)
  simpa [f] using hx

/-- **The unit of the descended adjunction, tested against a Hom-set, is the degreewise unit.**
For an adjunction of exact functors and a cochain complex `X`, precomposition with the unit of
`CategoryTheory.Adjunction.mapDerivedCategory` at `Q X` is bijective on maps into `Y` as soon as
precomposition with the image under `Q` of the degreewise unit is. -/
theorem bijective_precomp_derivedUnit
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (X : CochainComplex C ℤ) (Y : DerivedCategory C)
    (h : Function.Bijective (fun g : DerivedCategory.Q.obj
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) ⟶ Y =>
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app X) ≫ g)) :
    Function.Bijective (fun g : G.mapDerivedCategory.obj
      (F.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) ⟶ Y =>
      adj.mapDerivedCategory.unit.app (DerivedCategory.Q.obj X) ≫ g) := by
  simp only [Adjunction.mapDerivedCategory, Adjunction.localization_unit_app]
  simpa only [Function.comp_def, Iso.homFromEquiv_apply, Iso.symm_inv, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc, Functor.comp_obj,
      Functor.id_obj] using
    h.comp ((Iso.homFromEquiv
    ((G.mapDerivedCategoryFactors.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)).symm ≪≫
      G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app X).symm).symm).bijective)

private theorem bijective_precomp_singleUnit
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    (adj : F ⊣ G) (P : C) (n : ℤ) (Y : DerivedCategory C)
    (h : Function.Bijective (fun g : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor C n).obj (G.obj (F.obj P))) ⟶ Y =>
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C n).map (adj.unit.app P)) ≫ g)) :
    Function.Bijective (fun g : DerivedCategory.Q.obj
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C n).obj P))) ⟶ Y =>
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
        ((CochainComplex.singleFunctor C n).obj P)) ≫ g) := by
  let e := (G.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app P) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) n).app (F.obj P)
  apply bijective_precomp_of_iso_square _ _ (Iso.refl _) (DerivedCategory.Q.mapIso e) _ Y h
  simp only [Iso.refl_hom, Category.id_comp, Functor.mapIso_hom, ← Functor.map_comp]
  congr 1
  apply HomologicalComplex.from_single_hom_ext
  simp only [e, Iso.trans_hom, HomologicalComplex.comp_f, Functor.mapIso_hom,
    Functor.mapHomologicalComplex_map_f, Iso.app_hom,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (F.obj P)).inv
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (F.obj P)).hom,
    Iso.inv_hom_id, G.map_id, Category.id_comp]
  change ((HomologicalComplex.single C (ComplexShape.up ℤ) n).map (adj.unit.app P)).f n =
    adj.unit.app _ ≫ G.map (F.map (HomologicalComplex.singleObjXSelf _ n P).hom) ≫
      (HomologicalComplex.singleObjXSelf _ n _).inv
  rw [HomologicalComplex.single_map_f_self]
  simpa only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj, Category.assoc]
    using
    congrArg (fun k => k ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
      (G.obj (F.obj P))).inv)
      (adj.unit.naturality (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n P).hom)
private theorem bijective_precomp_of_map
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.Full] [F.Faithful]
    {X X' : C} (f : X ⟶ X') (Y : C)
    (h : Function.Bijective (fun g : F.obj X' ⟶ F.obj Y => F.map f ≫ g)) :
    Function.Bijective (fun g : X' ⟶ Y => f ≫ g) := by
  have hh := h.comp (show Function.Bijective (F.map : (X' ⟶ Y) → _) from ⟨F.map_injective,
    F.map_surjective⟩)
  simp only [Function.comp_def, ← F.map_comp] at hh
  exact (Function.Bijective.of_comp_iff' (show Function.Bijective (F.map : (X ⟶ Y) → _) from
    ⟨F.map_injective, F.map_surjective⟩) _).mp hh

private theorem bijective_precomp_single_shift
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {P Q : C} (f : P ⟶ Q) (Y : DerivedCategory C) (n : ℤ)
    (h : Function.Bijective (fun g : (DerivedCategory.singleFunctor C 0).obj Q ⟶ Y⟦n⟧ =>
      (DerivedCategory.singleFunctor C 0).map f ≫ g)) :
    Function.Bijective (fun g : (DerivedCategory.singleFunctor C n).obj Q ⟶ Y =>
      (DerivedCategory.singleFunctor C n).map f ≫ g) := by
  let e := (DerivedCategory.singleFunctors C).shiftIso n 0 n (add_zero n)
  apply bijective_precomp_of_map (shiftFunctor _ n) _ Y
  apply bijective_precomp_of_iso_square _ _ (e.app P) (e.app Q) _ _ h
  exact (e.hom.naturality f).symm

end CompleteRestrictScalarsEquivalence

end
