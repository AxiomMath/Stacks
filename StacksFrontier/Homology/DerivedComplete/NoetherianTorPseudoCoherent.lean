module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EpiTowerLimit
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.RingTheory.AdicCompletion.FiniteFreeTensor
import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionTorSequence


/-!
# Derived completion commutes with pseudo-coherent tensor factors

Let `I` be an ideal in a Noetherian ring `A`, and let `K` be a bounded-above object of `D(A)`.
Derived `I`-adic completion commutes with derived tensoring `K` by a finite module, and more
generally by a pseudo-coherent object of `D(A)`.

## Main definitions

There are no new definitions.

## Main results

* `AdicCompletionPseudoCoherentTensor.derivedCompletion_tensor_iso_of_boundedAbove` gives the
  comparison isomorphisms for finite modules and pseudo-coherent derived objects.

## Implementation notes

Derived completion is represented by a reflector onto the derived-complete objects together with
its canonical derived-limit description. Equalities in the source are expressed as isomorphisms in
the derived category. A finite module is placed in degree zero for the first part of the result.

## References

* [The Stacks Project, Tag 0EEV](https://stacks.math.columbia.edu/tag/0EEV)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u v w v' w'

namespace AdicCompletionPseudoCoherentTensor

private theorem isPseudoCoherent_single_of_finite
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) :=
  (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))
    0 M).2.2.mpr inferInstance

private theorem nonempty_iso_of_isDerivedLimit
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    {K L : D} (hK : IsDerivedLimit F K) (hL : IsDerivedLimit F L) :
    Nonempty (K ≅ L) := by
  obtain ⟨p, δ, hp⟩ := hK
  obtain ⟨q, ε, hq⟩ := hL
  let d := Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let t := Triangle.mk p d δ
  let s := Triangle.mk q d ε
  obtain ⟨f, hf, hf'⟩ := complete_distinguished_triangle_morphism₁ t s hp hq
    (𝟙 _) (𝟙 _) (by simp [t, s])
  let φ : t ⟶ s := Triangle.homMk t s f (𝟙 _) (𝟙 _) hf (by simp [t, s]) hf'
  have : IsIso f := isIso₁_of_isIso₂₃ φ hp hq (by change IsIso (𝟙 _); infer_instance)
    (by change IsIso (𝟙 _); infer_instance)
  exact ⟨asIso f⟩

private def adicCompletionFunctor {A : Type u} [CommRing A] (I : Ideal A) :
    ModuleCat.{v} A ⥤ ModuleCat.{v} A where
  obj M := ModuleCat.of A (AdicCompletion I M)
  map f := ModuleCat.ofHom (AdicCompletion.map I f.hom)
  map_id M := ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    DFunLike.congr_fun (AdicCompletion.map_id I M) x
  map_comp f g := ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    (DFunLike.congr_fun (AdicCompletion.map_comp I f.hom g.hom) x).symm

private theorem adicCompletionFunctor_additive {A : Type u} [CommRing A] (I : Ideal A) :
    (adicCompletionFunctor.{u, v} I).Additive where
  map_add := by
    intro M N f g
    ext x
    exact DFunLike.congr_fun (map_add (AdicCompletion.map I) f.hom g.hom) x

private abbrev adicCompletionComplex {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{v} A) ℤ) : CochainComplex (ModuleCat.{v} A) ℤ :=
  have := adicCompletionFunctor_additive I
  ((adicCompletionFunctor I).mapHomologicalComplex (ComplexShape.up ℤ)).obj E

private theorem exists_boundedAbove_projective_representative
    {A : Type u} [CommRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : DerivedCategory.TStructure.t.minus K) :
    ∃ (E : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ),
      E.IsStrictlyLE b ∧ (∀ i : ℤ, Projective (E.X i)) ∧
        Nonempty (DerivedCategory.Q.obj E ≅ K) := by
  obtain ⟨b, hb⟩ := hK
  have : K.IsLE b := hb
  obtain ⟨E, hE, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  obtain ⟨P, _⟩ := ProjectiveResolutionLemma.statement3 b E hE
  have := P.quasiIso
  exact ⟨P.complex, b, P.boundedAbove, P.projective,
    ⟨asIso (DerivedCategory.Q.map P.α) ≪≫ e.symm⟩⟩

private theorem quasiIso_tensorRight_map
    {A : Type u} [CommRing A]
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (hF : F.KFlat)
    {E E' : CochainComplex (ModuleCat.{u} A) ℤ} (f : E ⟶ E') [QuasiIso f] :
    QuasiIso ((TrightCochain F).map f) := by
  have hf : HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ _).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr ‹QuasiIso f›
  have h := CochainComplex.KFlat.kFlat_tright_preserves_quasiIso F hF
    ((HomotopyCategory.quotient _ _).map f) hf
  change HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
    ((HomotopyCategory.quotient _ _ ⋙ Tright F).map f) at h
  unfold Tright at h
  rw [descendF_comp_quotient] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp h

set_option backward.isDefEq.respectTransparency false in
private theorem nonempty_derivedTensor_iso_tensor_of_kFlat_right
    {A : Type u} [CommRing A] (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (E F : CochainComplex (ModuleCat.{u} A) ℤ) (hF : F.KFlat) :
    Nonempty ((T.tensor.obj (DerivedCategory.Q.obj E)).obj (DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj (E ⊗ F)) := by
  obtain ⟨P, f, hPL, _, hf, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} E
  have hP : P.KFlat := hPL
  have := hf
  have : QuasiIso ((TrightCochain F).map f) := quasiIso_tensorRight_map F hF f
  let e := asIso (DerivedCategory.Q.map ((TrightCochain F).map f))
  exact ⟨(T.tensor.mapIso (asIso (DerivedCategory.Q.map f)).symm).app
      (DerivedCategory.Q.obj F) ≪≫ T.comparison P F hP hF ≪≫
        e⟩


set_option backward.isDefEq.respectTransparency false in
private def isColimitCofanRestrict
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {ι : Type w} {X : ι → C} (c : Cofan X) (hc : IsColimit c)
    (p : ι → Prop) (hz : ∀ i, ¬ p i → IsZero (X i)) :
    IsColimit (Cofan.mk c.pt (fun i : Subtype p ↦ c.inj i)) := by
  classical
  refine Cofan.IsColimit.mk _ (fun s ↦ hc.desc
    (Cofan.mk s.pt (fun i ↦ if h : p i then s.inj ⟨i, h⟩ else 0))) ?_ ?_
  · intro s i
    simp [i.property]
  · intro s m hm
    apply hc.hom_ext
    intro i
    rcases i with ⟨i⟩
    rw [hc.fac]
    by_cases hi : p i
    · change c.inj i ≫ m = (if h : p i then s.inj ⟨i, h⟩ else 0)
      rw [dite_eq_left hi]
      exact hm ⟨i, hi⟩
    · exact (hz i hi).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private def isColimitCofanOfRestrict
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {ι : Type w} {X : ι → C} (c : Cofan X)
    (p : ι → Prop) (hz : ∀ i, ¬ p i → IsZero (X i))
    (hc : IsColimit (Cofan.mk c.pt (fun i : Subtype p ↦ c.inj i))) :
    IsColimit c := by
  refine Cofan.IsColimit.mk _ (fun s ↦ hc.desc
    (Cofan.mk s.pt (fun i : Subtype p ↦ s.inj i))) ?_ ?_
  · intro s i
    by_cases hi : p i
    · exact hc.fac _ ⟨⟨i, hi⟩⟩
    · exact (hz i hi).eq_of_src _ _
  · exact fun s m hm ↦ hc.hom_ext fun i ↦ (hm i.as.val).trans (hc.fac
      (Cofan.mk s.pt (fun i : Subtype p ↦ s.inj i)) i).symm

private def isColimitMapCofanOfFiniteSupport
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type w} [Category.{w'} D] [Preadditive D]
    (G : C ⥤ D) [G.Additive]
    {ι : Type} {X : ι → C} (c : Cofan X) (hc : IsColimit c)
    (p : ι → Prop) [Finite (Subtype p)]
    (hz : ∀ i, ¬ p i → IsZero (X i)) :
    IsColimit (Cofan.mk (G.obj c.pt) (fun i ↦ G.map (c.inj i))) :=
  isColimitCofanOfRestrict _ p (fun i hi ↦ G.map_isZero (hz i hi))
    (isColimitCofanMkObjOfIsColimit G _ _ (isColimitCofanRestrict c hc p hz))

open HomologicalComplex
private theorem tensor_ι_d
    {A : Type u} [CommRing A]
    (E F : CochainComplex (ModuleCat.{u} A) ℤ)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj E F i j n h ≫ (E ⊗ F).d n (n + 1) =
      (E.d i (i + 1) ▷ F.X j) ≫
          ιTensorObj E F (i + 1) j (n + 1) (by omega) +
      i.negOnePow • ((E.X i ◁ F.d j (j + 1)) ≫
          ιTensorObj E F i (j + 1) (n + 1) (by omega)) := by
  show ιTensorObj E F i j n h ≫ (HomologicalComplex.tensorObj E F).d n (n + 1) = _
  rw [mapBifunctor.d_eq E F (curriedTensor _) (ComplexShape.up ℤ), Preadditive.comp_add,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq E F (curriedTensor _) (ComplexShape.up ℤ) (i₁' := i + 1) (by simp) j
      (n + 1) (by simpa using show i + 1 + j = n + 1 by omega),
    mapBifunctor.d₂_eq E F (curriedTensor _) (ComplexShape.up ℤ) i (i₂' := j + 1) (by simp)
      (n + 1) (by simpa using show i + (j + 1) = n + 1 by omega)]
  simp

attribute [local instance] adicCompletionFunctor_additive

private theorem adicCompletionTensorMap_naturality_cat
    {A : Type u} [CommRing A] (I : Ideal A)
    {M M' N N' : ModuleCat.{u} A} (f : M ⟶ M') (g : N ⟶ N') :
    ((adicCompletionFunctor I).map f ⊗ₘ g) ≫
        ModuleCat.ofHom (adicCompletionTensorMap I M' N') =
      ModuleCat.ofHom (adicCompletionTensorMap I M N) ≫
        (adicCompletionFunctor I).map (f ⊗ₘ g) :=
  ModuleCat.hom_ext (adicCompletionTensorMap_naturality I f.hom g.hom).symm

private def adicCompletionTensorComplexMapX
    {A : Type u} [CommRing A] (I : Ideal A)
    (E F : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (adicCompletionComplex I E ⊗ F).X n ⟶ (adicCompletionComplex I (E ⊗ F)).X n :=
  mapBifunctorDesc (fun i j h ↦
    ModuleCat.ofHom (adicCompletionTensorMap I (E.X i) (F.X j)) ≫
      (adicCompletionFunctor I).map (ιTensorObj E F i j n h))

private theorem ι_adicCompletionTensorComplexMapX
    {A : Type u} [CommRing A] (I : Ideal A)
    (E F : CochainComplex (ModuleCat.{u} A) ℤ) (i j n : ℤ) (h : i + j = n) :
    ιTensorObj (adicCompletionComplex I E) F i j n h ≫
        adicCompletionTensorComplexMapX I E F n =
      ModuleCat.ofHom (adicCompletionTensorMap I (E.X i) (F.X j)) ≫
        (adicCompletionFunctor I).map (ιTensorObj E F i j n h) :=
  ι_mapBifunctorDesc _ i j h

set_option backward.isDefEq.respectTransparency false in
private theorem adicCompletionTensorComplexMapX_comm
    {A : Type u} [CommRing A] (I : Ideal A)
    (E F : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (adicCompletionComplex I E ⊗ F).d n (n + 1) ≫
        adicCompletionTensorComplexMapX I E F (n + 1) =
      adicCompletionTensorComplexMapX I E F n ≫
        (adicCompletionComplex I (E ⊗ F)).d n (n + 1) := by
  apply mapBifunctor.hom_ext
  intro i j h
  change i + j = n at h
  rw [reassoc_of% (ι_adicCompletionTensorComplexMapX I E F i j n h)]
  rw [← Category.assoc, tensor_ι_d]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
    ι_adicCompletionTensorComplexMapX]
  show _ = ModuleCat.ofHom (adicCompletionTensorMap I (E.X i) (F.X j)) ≫
    (adicCompletionFunctor I).map (ιTensorObj E F i j n h) ≫
      (adicCompletionFunctor I).map ((E ⊗ F).d n (n + 1))
  rw [← Functor.map_comp, tensor_ι_d, Functor.map_add, Preadditive.comp_add]
  simp only [Functor.map_comp, Functor.map_units_smul, Linear.comp_units_smul]
  have key {M M' N N' Z : ModuleCat.{u} A} (f : M ⟶ M') (g : N ⟶ N') (k : M' ⊗ N' ⟶ Z) :
      ((adicCompletionFunctor I).map f ⊗ₘ g) ≫
        ModuleCat.ofHom (adicCompletionTensorMap I M' N') ≫ (adicCompletionFunctor I).map k =
      ModuleCat.ofHom (adicCompletionTensorMap I M N) ≫
        (adicCompletionFunctor I).map ((f ⊗ₘ g) ≫ k) := by
    simp only [Functor.map_comp, ← Category.assoc, adicCompletionTensorMap_naturality_cat]
  congr 1
  · simpa [adicCompletionComplex] using key (E.d i (i + 1)) (𝟙 (F.X j)) _
  · congr 1
    simpa [adicCompletionComplex] using key (𝟙 (E.X i)) (F.d j (j + 1)) _

private def adicCompletionTensorComplexMap
    {A : Type u} [CommRing A] (I : Ideal A)
    (E F : CochainComplex (ModuleCat.{u} A) ℤ) :
    adicCompletionComplex I E ⊗ F ⟶ adicCompletionComplex I (E ⊗ F) where
  f := adicCompletionTensorComplexMapX I E F
  comm' n m h := by
    obtain rfl : m = n + 1 := h.symm
    exact (adicCompletionTensorComplexMapX_comm I E F n).symm

set_option backward.isDefEq.respectTransparency false in
private def isColimitCofanOfComponentIso
    {C : Type u} [Category.{v} C] {ι : Type w}
    {X Y : ι → C} (e : ∀ i, X i ≅ Y i) (c : Cofan Y) (hc : IsColimit c) :
    IsColimit (Cofan.mk c.pt (fun i ↦ (e i).hom ≫ c.inj i)) := by
  refine Cofan.IsColimit.mk _ (fun s ↦ hc.desc
    (Cofan.mk s.pt (fun i ↦ (e i).inv ≫ s.inj i))) ?_ ?_
  · intro s i
    change ((e i).hom ≫ c.inj i) ≫ hc.desc _ = _
    rw [Category.assoc, show c.inj i ≫ hc.desc (Cofan.mk s.pt (fun i ↦ (e i).inv ≫ s.inj i)) =
      (e i).inv ≫ s.inj i from hc.fac _ ⟨i⟩]
    simp
  · intro s m hm
    apply hc.hom_ext
    rintro ⟨i⟩
    rw [hc.fac]
    apply (cancel_epi (e i).hom).mp
    change (e i).hom ≫ c.inj i ≫ m = (e i).hom ≫ (e i).inv ≫ s.inj i
    simpa only [cofan_mk_inj, Iso.hom_inv_id_assoc, Category.assoc] using hm i

private def isColimitTensorCofan
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
    [(curriedTensor C).Additive] [∀ X, ((curriedTensor C).obj X).Additive]
    (E F : CochainComplex C ℤ) [E.HasTensor F] (n : ℤ) :
    IsColimit (Cofan.mk ((HomologicalComplex.tensorObj E F).X n)
      (fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} ↦
        ιTensorObj E F ij.1.1 ij.1.2 n ij.2)) := by
  refine Cofan.IsColimit.mk _ (fun s ↦ mapBifunctorDesc
    (fun i j h ↦ s.inj ⟨(i, j), h⟩)) ?_ ?_
  · intro s ij
    exact ι_mapBifunctorDesc _ ij.1.1 ij.1.2 ij.2
  · intro s m hm
    apply mapBifunctor.hom_ext
    intro i j h
    rw [ι_mapBifunctorDesc]
    exact hm ⟨(i, j), h⟩

private theorem finite_bounded_diagonal (b c n : ℤ) :
    Finite {ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} // ij.1.1 ≤ b ∧ ij.1.2 ≤ c} := by
  let f : {ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} // ij.1.1 ≤ b ∧ ij.1.2 ≤ c} →
      ↥(Finset.Icc (n - c) b) := fun ij ↦ ⟨ij.1.1.1, by
        have := ij.1.2
        have := ij.2
        simp only [Finset.mem_Icc]
        omega⟩
  refine Finite.of_injective f fun ij kl h ↦ ?_
  have he : ij.1.1.1 = kl.1.1.1 := congrArg Subtype.val h
  have := ij.1.2
  have := kl.1.2
  exact Subtype.ext (Subtype.ext (Prod.ext he (by omega)))

private def isColimitMapTensorCofanOfBoundedAbove
    {A : Type u} [CommRing A]
    {D : Type w} [Category.{w'} D] [Preadditive D]
    (G : ModuleCat.{u} A ⥤ D) [G.Additive]
    (E F : CochainComplex (ModuleCat.{u} A) ℤ) (b c : ℤ)
    [E.IsStrictlyLE b] [F.IsStrictlyLE c] (n : ℤ) :
    IsColimit (Cofan.mk (G.obj ((E ⊗ F).X n))
      (fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} ↦
        G.map (ιTensorObj E F ij.1.1 ij.1.2 n ij.2))) := by
  have := finite_bounded_diagonal b c n
  apply isColimitMapCofanOfFiniteSupport G _ (isColimitTensorCofan E F n)
    (fun ij ↦ ij.1.1 ≤ b ∧ ij.1.2 ≤ c)
  intro ij hij
  by_cases hi : ij.1.1 ≤ b
  · have hj : c < ij.1.2 := lt_of_not_ge (fun hj ↦ hij ⟨hi, hj⟩)
    exact (tensorLeft (E.X ij.1.1)).map_isZero (F.isZero_of_isStrictlyLE c _ hj)
  · exact (tensorRight (F.X ij.1.2)).map_isZero
      (E.isZero_of_isStrictlyLE b _ (lt_of_not_ge hi))

private theorem isIso_adicCompletionTensorComplexMapX
    {A : Type u} [CommRing A] (I : Ideal A)
    (E F : CochainComplex (ModuleCat.{u} A) ℤ) (b c : ℤ)
    [E.IsStrictlyLE b] [F.IsStrictlyLE c]
    [∀ i, Module.Finite A (F.X i)] [∀ i, Module.Free A (F.X i)] (n : ℤ) :
    IsIso (adicCompletionTensorComplexMapX I E F n) := by
  let e (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) :=
    (LinearEquiv.ofBijective
      (adicCompletionTensorMap I (E.X ij.1.1) (F.X ij.1.2))
      (adicCompletionTensorMap_bijective_of_finite_free I _ _)).toModuleIso
  let cT := Cofan.mk ((adicCompletionComplex I (E ⊗ F)).X n)
    (fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} ↦
      (e ij).hom ≫ (adicCompletionFunctor I).map
        (ιTensorObj E F ij.1.1 ij.1.2 n ij.2))
  let hs := isColimitTensorCofan (adicCompletionComplex I E) F n
  let ht : IsColimit cT := isColimitCofanOfComponentIso e _
    (isColimitMapTensorCofanOfBoundedAbove (adicCompletionFunctor I) E F b c n)
  let q := hs.coconePointUniqueUpToIso ht
  have hq : adicCompletionTensorComplexMapX I E F n = q.hom := by
    apply mapBifunctor.hom_ext
    intro i j h
    rw [ι_adicCompletionTensorComplexMapX]
    exact (hs.fac cT ⟨⟨(i, j), h⟩⟩).symm
  rw [hq]
  infer_instance

private def adicCompletionTensorComplexIso
    {A : Type u} [CommRing A] (I : Ideal A)
    (E F : CochainComplex (ModuleCat.{u} A) ℤ) (b c : ℤ)
    [E.IsStrictlyLE b] [F.IsStrictlyLE c]
    [∀ i, Module.Finite A (F.X i)] [∀ i, Module.Free A (F.X i)] :
    adicCompletionComplex I E ⊗ F ≅ adicCompletionComplex I (E ⊗ F) := by
  have : ∀ n, IsIso ((adicCompletionTensorComplexMap I E F).f n) :=
    isIso_adicCompletionTensorComplexMapX I E F b c
  have := HomologicalComplex.Hom.isIso_of_components (adicCompletionTensorComplexMap I E F)
  exact asIso (adicCompletionTensorComplexMap I E F)


private def reductionFunctor {A : Type u} [CommRing A] (J : Ideal A) :
    ModuleCat.{v} A ⥤ ModuleCat.{v} A where
  obj M := ModuleCat.of A (M ⧸ (J • ⊤ : Submodule A M))
  map f := ModuleCat.ofHom ((f.hom.reduceModIdeal J).restrictScalars A)
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

private theorem reductionFunctor_additive {A : Type u} [CommRing A] (J : Ideal A) :
    (reductionFunctor.{u,v} J).Additive where
  map_add := by
    intro M N f g
    ext x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

attribute [local instance] reductionFunctor_additive

private def reductionTransition {A : Type u} [CommRing A] (I : Ideal A)
    {m n : ℕ} (h : m ≤ n) : reductionFunctor (I ^ n) ⟶ reductionFunctor.{u,v} (I ^ m) where
  app M := ModuleCat.ofHom (AdicCompletion.transitionMap I M h)
  naturality _ _ f := ModuleCat.hom_ext (AdicCompletion.transitionMap_comp_reduceModIdeal I f.hom h)

private def reductionComplex {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :=
  ((reductionFunctor (I ^ n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E

private def reductionComplexTransition {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{v} A) ℤ) {m n : ℕ} (h : m ≤ n) :
    reductionComplex I E n ⟶ reductionComplex I E m where
  f i := (reductionTransition I h).app (E.X i)
  comm' i j _ := ((reductionTransition I h).naturality (E.d i j)).symm

private theorem reductionComplexTransition_refl {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :
    reductionComplexTransition I E (le_refl n) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  show AdicCompletion.transitionMap I (E.X i) (le_refl n) = LinearMap.id
  ext x
  rfl

private theorem reductionComplexTransition_trans {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{v} A) ℤ) {l m n : ℕ} (h : l ≤ m) (h' : m ≤ n) :
    reductionComplexTransition I E (h.trans h') =
      reductionComplexTransition I E h' ≫ reductionComplexTransition I E h := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  show AdicCompletion.transitionMap I (E.X i) (h.trans h') =
    AdicCompletion.transitionMap I (E.X i) h ∘ₗ AdicCompletion.transitionMap I (E.X i) h'
  ext x
  rfl

private def reductionTower {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{v} A) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ where
  obj n := reductionComplex I E (n.unop + 1)
  map f := reductionComplexTransition I E (Nat.add_le_add_right (leOfHom f.unop) 1)
  map_id n := reductionComplexTransition_refl I E (n.unop + 1)
  map_comp _ _ := reductionComplexTransition_trans I E _ _

private theorem reductionTower_epi {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :
    Epi ((reductionTower I E).map (homOfLE (Nat.le_succ n)).op) := by
  refine HomologicalComplex.epi_of_epi_f _ fun i ↦ (ModuleCat.epi_iff_surjective _).2 fun x ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Submodule.Quotient.mk x, rfl⟩

private theorem adicCompletion_ext_succ {A : Type u} [CommRing A] (I : Ideal A)
    {M : Type v} [AddCommGroup M] [Module A M] {x y : AdicCompletion I M}
    (h : ∀ n, x.val (n + 1) = y.val (n + 1)) : x = y :=
  AdicCompletion.ext fun
    | 0 => (x.property (Nat.zero_le 1)).symm.trans
      ((congrArg (AdicCompletion.transitionMap I M (Nat.zero_le 1)) (h 0)).trans
        (y.property (Nat.zero_le 1)))
    | n + 1 => h n

private def adicCompletionLiftSucc {A : Type u} [CommRing A] (I : Ideal A)
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : ∀ n : ℕ, M →ₗ[A] N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N))
    (h : ∀ {m n : ℕ} (h : m ≤ n),
      AdicCompletion.transitionMap I N (Nat.add_le_add_right h 1) ∘ₗ f n = f m) :
    M →ₗ[A] AdicCompletion I N :=
  AdicCompletion.lift I (fun n => match n with | 0 => 0 | n + 1 => f n) (by
    intro m n hmn
    cases m with
    | zero =>
      apply LinearMap.ext
      intro x
      have : Subsingleton (N ⧸ (I ^ 0 • ⊤ : Submodule A N)) := by
        rw [pow_zero, one_smul]
        infer_instance
      exact Subsingleton.elim _ _
    | succ m =>
      cases n with
      | zero => omega
      | succ n => exact h (by omega))

private def adicCompletionProjection {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :
    adicCompletionComplex I E ⟶ reductionComplex I E n where
  f i := ModuleCat.ofHom (AdicCompletion.eval I (E.X i) n)
  comm' i j _ := ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    (AdicCompletion.map_val_apply I (E.d i j).hom x).symm

private def adicCompletionCone {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{v} A) ℤ) : Cone (reductionTower I E) where
  pt := adicCompletionComplex I E
  π :=
    { app := fun n => adicCompletionProjection I E (n.unop + 1)
      naturality := by
        intro n m f
        ext i x
        exact (AdicCompletion.transitionMap_comp_eval_apply I (E.X i)
          (Nat.add_le_add_right (leOfHom f.unop) 1) x).symm }

private def adicCompletionConeIsLimit {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{v} A) ℤ) : IsLimit (adicCompletionCone I E) := by
  apply HomologicalComplex.isLimitOfEval
  intro i
  let lift (s : Cone (reductionTower I E ⋙ HomologicalComplex.eval _ _ i)) :
      s.pt ⟶ ModuleCat.of A (AdicCompletion I (E.X i)) :=
    ModuleCat.ofHom (adicCompletionLiftSucc I (fun n => (s.π.app ⟨n⟩).hom) (by
      intro m n h
      exact congrArg ModuleCat.Hom.hom (s.w (homOfLE h).op)))
  exact { lift := lift, fac _ _ := rfl, uniq _ m hm := ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    adicCompletion_ext_succ I fun n ↦ congrArg (fun f => f x) (hm ⟨n⟩) }


private theorem completion_isDerivedLimit_reductionTower
    {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    IsDerivedLimit (reductionTower I E ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (adicCompletionComplex I E)) := by
  have := reductionTower_epi I E
  exact DerivedCategory.isDerivedLimit_of_limit_cone_of_epi (reductionTower I E)
    (adicCompletionCone I E) (adicCompletionConeIsLimit I E)

set_option backward.isDefEq.respectTransparency false in
private def tensorSingleInclusion {A : Type u} [CommRing A]
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (M : ModuleCat.{u} A) :
    ((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
      E ⊗ (CochainComplex.singleFunctor _ 0).obj M where
  f i := ιTensorObj E ((CochainComplex.singleFunctor _ 0).obj M) i 0 i (by omega)
  comm' i j h := by
    obtain rfl : j = i + 1 := h.symm
    rw [tensor_ι_d]
    simp only [CochainComplex.singleFunctor_obj_d, MonoidalPreadditive.whiskerLeft_zero, zero_comp,
      smul_zero, add_zero]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_tensorSingleInclusion_f {A : Type u} [CommRing A]
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (M : ModuleCat.{u} A) (n : ℤ) :
    IsIso ((tensorSingleInclusion E M).f n) := by
  let F := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  let J := {ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} // ij.1.2 = 0}
  let j : J := ⟨⟨(n, 0), by simp⟩, rfl⟩
  have hj (k : J) : k = j := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> dsimp [j]
    · have := k.1.2
      have := k.2
      omega
    · exact k.2
  let hterm : IsTerminal (Discrete.mk j) :=
    IsTerminal.ofUniqueHom (fun k => eqToHom (congrArg Discrete.mk (hj k.as)))
      (fun _ _ => Subsingleton.elim _ _)
  let h := isColimitCofanRestrict _ (isColimitTensorCofan E F n)
    (fun ij => ij.1.2 = 0) fun ij hij ↦ (tensorLeft (E.X ij.1.1)).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ M _ hij)
  exact h.isIso_ι_app_of_isTerminal (Discrete.mk j) hterm

set_option backward.isDefEq.respectTransparency false in
private theorem tensorSingleInclusion_naturality {A : Type u} [CommRing A]
    (E : CochainComplex (ModuleCat.{u} A) ℤ) {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (NatTrans.mapHomologicalComplex ((curriedTensor _).flip.map f) _).app E ≫
        (tensorSingleInclusion E N) =
      tensorSingleInclusion E M ≫ (E ◁ (CochainComplex.singleFunctor _ 0).map f) := by
  apply HomologicalComplex.Hom.ext
  funext i
  show (E.X i ◁ f) ≫
      ιTensorObj E ((CochainComplex.singleFunctor _ 0).obj N) i 0 i (by simp) =
    ιTensorObj E ((CochainComplex.singleFunctor _ 0).obj M) i 0 i (by simp) ≫
      (E ◁ (CochainComplex.singleFunctor _ 0).map f).f i
  have h := HomologicalComplex.ι_mapBifunctorMap (𝟙 E)
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).map f)
    (curriedTensor (ModuleCat.{u} A)) (ComplexShape.up ℤ) i 0 i (by simp)
  change ιTensorObj E ((CochainComplex.singleFunctor _ 0).obj M) i 0 i (by simp) ≫
      (E ◁ (CochainComplex.singleFunctor _ 0).map f).f i =
    (𝟙 (E.X i) ▷ M) ≫ (E.X i ◁ f) ≫
      ιTensorObj E ((CochainComplex.singleFunctor _ 0).obj N) i 0 i (by simp) at h
  simp only [id_whiskerRight, Category.id_comp] at h
  exact h.symm


set_option backward.isDefEq.respectTransparency false in
private def tensorQuotientComplexIso {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) :
    ((tensorRight (ModuleCat.of A (A ⧸ I ^ n))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ≅ reductionComplex I E n :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (TensorProduct.tensorQuotEquivQuotSMul (E.X i) (I ^ n)).toModuleIso)
    (by
      intro i j hij
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x r
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change (E.d i j).hom.reduceModIdeal (I ^ n)
          (TensorProduct.tensorQuotEquivQuotSMul (E.X i) (I ^ n)
            (x ⊗ₜ[A] Ideal.Quotient.mk (I ^ n) r)) =
        TensorProduct.tensorQuotEquivQuotSMul (E.X j) (I ^ n)
          ((E.d i j).hom x ⊗ₜ[A] Ideal.Quotient.mk (I ^ n) r)
      simp)

set_option backward.isDefEq.respectTransparency false in
private def quotientTransition {A : Type u} [CommRing A] (I : Ideal A)
    {m n : ℕ} (h : m ≤ n) :
    ModuleCat.of A (A ⧸ I ^ n) ⟶ ModuleCat.of A (A ⧸ I ^ m) :=
  ModuleCat.ofHom ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).toLinearMap)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorQuotientComplexIso_naturality {A : Type u} [CommRing A]
    (I : Ideal A) (E : CochainComplex (ModuleCat.{u} A) ℤ)
    {m n : ℕ} (h : m ≤ n) :
    (tensorQuotientComplexIso I E n).hom ≫ reductionComplexTransition I E h =
      (NatTrans.mapHomologicalComplex
        ((curriedTensor _).flip.map (quotientTransition I h)) _).app E ≫
          (tensorQuotientComplexIso I E m).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  show AdicCompletion.transitionMap I (E.X i) h
      (TensorProduct.tensorQuotEquivQuotSMul (E.X i) (I ^ n)
        (x ⊗ₜ[A] Ideal.Quotient.mk (I ^ n) r)) =
    TensorProduct.tensorQuotEquivQuotSMul (E.X i) (I ^ m)
      (x ⊗ₜ[A] Ideal.Quotient.mk (I ^ m) r)
  simp


set_option backward.isDefEq.respectTransparency false in
private theorem isDerivedLimit_of_natIso
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ G.obj ⟨n⟩]
    (e : F ≅ G) {K : D} (h : IsDerivedLimit F K) : IsDerivedLimit G K := by
  obtain ⟨p, δ, hp⟩ := h
  let q : (∏ᶜ fun n : ℕ => F.obj ⟨n⟩) ≅ (∏ᶜ fun n : ℕ => G.obj ⟨n⟩) :=
    { hom := CategoryTheory.Limits.Pi.map (fun n => e.hom.app ⟨n⟩)
      inv := CategoryTheory.Limits.Pi.map (fun n => e.inv.app ⟨n⟩)
      hom_inv_id := by ext n; simp
      inv_hom_id := by ext n; simp }
  let d := Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n+1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let d' := Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => G.obj ⟨n⟩) n -
    Pi.π (fun n : ℕ => G.obj ⟨n⟩) (n+1) ≫ G.map (homOfLE (Nat.le_succ n)).op
  have hd : d ≫ q.hom = q.hom ≫ d' := by
    apply Pi.hom_ext
    intro n
    simp only [q, Category.assoc, Pi.map_π, Pi.map_π_assoc, d, d',
      Pi.lift_π, Pi.lift_π_assoc, Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc]
    rw [e.hom.naturality]
  let t := Triangle.mk p d δ
  let s := Triangle.mk (p ≫ q.hom) d' (q.inv ≫ δ)
  let ei : t ≅ s := Triangle.isoMk _ _ (Iso.refl _) q q
    (by simp [t,s]) hd (by simp [t,s])
  exact ⟨_, _, isomorphic_distinguished _ hp _ ei.symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem quasiIso_tensorLeft_map
    {A : Type u} [CommRing A]
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat)
    {F F' : CochainComplex (ModuleCat.{u} A) ℤ} (f : F ⟶ F') [QuasiIso f] :
    QuasiIso (E ◁ f) := by
  let := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory A).choose
  have : QuasiIso (f ▷ E) := quasiIso_tensorRight_map E hE f
  exact (quasiIso_iff_of_arrow_mk_iso (E ◁ f) (f ▷ E)
    (Arrow.isoMk (β_ E F) (β_ E F') (by simp))).mpr this

set_option backward.isDefEq.respectTransparency false in
private theorem projectiveResolution_extend_lift_commutes
    {A : Type u} [CommRing A] {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (P : ProjectiveResolution M) (R : ProjectiveResolution N) :
    HomologicalComplex.extendMap (ProjectiveResolution.lift f P R)
        ComplexShape.embeddingDownNat ≫ R.π' =
      P.π' ≫ (CochainComplex.singleFunctor _ 0).map f := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, ProjectiveResolution.π'_f_zero,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = 0 by simp)]
  simp only [ProjectiveResolution.cochainComplexXIso, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [ProjectiveResolution.lift_commutes_zero_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem projectiveResolution_kFlat
    {A : Type u} [CommRing A] {M : ModuleCat.{u} A} (P : ProjectiveResolution M) :
    P.cochainComplex.KFlat :=
  CochainComplex.KFlat.kFlat_of_flat P.cochainComplex 0

set_option backward.isDefEq.respectTransparency false in
private def derivedTensorSingleIso
    {A : Type u} [CommRing A] (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat) (M : ModuleCat.{u} A) :
    (T.tensor.obj (DerivedCategory.Q.obj E)).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M)) ≅
      DerivedCategory.Q.obj (E ⊗ (CochainComplex.singleFunctor _ 0).obj M) := by
  let P := ProjectiveResolution.of M
  have := quasiIso_tensorLeft_map E hE P.π'
  exact (T.tensor.obj (DerivedCategory.Q.obj E)).mapIso
      (asIso (DerivedCategory.Q.map P.π')).symm ≪≫
    T.comparison E P.cochainComplex hE (projectiveResolution_kFlat P) ≪≫
      asIso (DerivedCategory.Q.map (E ◁ P.π'))

set_option backward.isDefEq.respectTransparency false in
private theorem derivedTensorSingleIso_fac
    {A : Type u} [CommRing A] (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat) (M : ModuleCat.{u} A) :
    (T.tensor.obj (DerivedCategory.Q.obj E)).map
        (DerivedCategory.Q.map (ProjectiveResolution.of M).π') ≫
      (derivedTensorSingleIso T E hE M).hom =
    (T.comparison E (ProjectiveResolution.of M).cochainComplex hE
        (projectiveResolution_kFlat _)).hom ≫
      DerivedCategory.Q.map (E ◁ (ProjectiveResolution.of M).π') := by
  have := quasiIso_tensorLeft_map E hE (ProjectiveResolution.of M).π'
  simp [derivedTensorSingleIso]

set_option backward.isDefEq.respectTransparency false in
private theorem derivedTensorSingleIso_naturality
    {A : Type u} [CommRing A] (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (T.tensor.obj (DerivedCategory.Q.obj E)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map f)) ≫
      (derivedTensorSingleIso T E hE N).hom =
    (derivedTensorSingleIso T E hE M).hom ≫
      DerivedCategory.Q.map (E ◁ (CochainComplex.singleFunctor _ 0).map f) := by
  let P := ProjectiveResolution.of M
  let R := ProjectiveResolution.of N
  let g := HomologicalComplex.extendMap (ProjectiveResolution.lift f P R)
    ComplexShape.embeddingDownNat
  have hg : g ≫ R.π' = P.π' ≫ (CochainComplex.singleFunctor _ 0).map f :=
    projectiveResolution_extend_lift_commutes f P R
  have he := quasiIso_tensorLeft_map E hE P.π'
  have he' := quasiIso_tensorLeft_map E hE R.π'
  apply (cancel_epi ((T.tensor.obj (DerivedCategory.Q.obj E)).map
    (DerivedCategory.Q.map P.π'))).mp
  have hnat := T.comparison_naturality (𝟙 E) g hE hE
    (projectiveResolution_kFlat P) (projectiveResolution_kFlat R)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at hnat
  change (T.tensor.obj (DerivedCategory.Q.obj E)).map (DerivedCategory.Q.map g) ≫
      (T.comparison E R.cochainComplex hE (projectiveResolution_kFlat R)).hom =
    (T.comparison E P.cochainComplex hE (projectiveResolution_kFlat P)).hom ≫
      DerivedCategory.Q.map (E ◁ g) at hnat
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp, ← hg,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    derivedTensorSingleIso_fac, ← Category.assoc, hnat, Category.assoc,
    ← CategoryTheory.Functor.map_comp,
    ← whiskerLeft_comp, hg, whiskerLeft_comp, CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, ← derivedTensorSingleIso_fac, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private def natIsoOfOpSequence
    {D : Type u} [Category.{v} D] {F G : ℕᵒᵖ ⥤ D}
    (e : ∀ n : ℕ, F.obj ⟨n⟩ ≅ G.obj ⟨n⟩)
    (h : ∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ G.map (homOfLE (Nat.le_succ n)).op) : F ≅ G :=
  NatIso.ofComponents (fun n => e n.unop)
    fun f ↦ (NatTrans.ofOpSequence (fun n => (e n).hom) h).naturality f

set_option backward.isDefEq.respectTransparency false in
private theorem extendSingleIso_naturality
    {A : Type u} [CommRing A] {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    HomologicalComplex.extendMap ((ChainComplex.single₀ _).map f)
        ComplexShape.embeddingDownNat ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat N 0 0 (by simp)).hom =
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat M 0 0 (by simp)).hom ≫
      (CochainComplex.singleFunctor _ 0).map f := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = 0 by simp),
    HomologicalComplex.extendSingleIso_hom_f, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def quotientSingleTower {A : Type u} [CommRing A] (I : Ideal A) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  Functor.ofOpSequence (X := fun n : ℕ =>
    (CochainComplex.singleFunctor _ 0).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))))
    (fun n => (CochainComplex.singleFunctor _ 0).map
      (quotientTransition I (Nat.add_le_add_right (Nat.le_succ n) 1)))

set_option backward.isDefEq.respectTransparency false in
private def idealPowerQuotientSystemIso {A : Type u} [CommRing A] (I : Ideal A) :
    NoetherianAdicCompletion.idealPowerQuotientSystem I ≅
      quotientSingleTower I ⋙ DerivedCategory.Q :=
  natIsoOfOpSequence (fun n => DerivedCategory.Q.mapIso
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (ModuleCat.of A (A ⧸ I ^ (n + 1))) 0 0 (by simp))) (by
    intro n
    simp only [NoetherianAdicCompletion.idealPowerQuotientSystem, quotientSingleTower,
      Functor.ofOpSequence_map_homOfLE_succ, Functor.comp_map, Functor.mapIso_hom,
      ← CategoryTheory.Functor.map_comp]
    exact congrArg DerivedCategory.Q.map
      (extendSingleIso_naturality (quotientTransition I
        (Nat.add_le_add_right (Nat.le_succ n) 1))))

set_option backward.isDefEq.respectTransparency false in
private theorem tensorSingleIso_hom {A : Type u} [CommRing A]
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (M : ModuleCat.{u} A) :
    ((AdicCompletionTor.tensorSingleIso E).app M).hom = tensorSingleInclusion E M := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem reductionTensorIso_naturality {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) {m n : ℕ} (h : m ≤ n) :
    reductionComplexTransition I E h ≫ (tensorQuotientComplexIso I E m).inv ≫
        tensorSingleInclusion E _ =
      (tensorQuotientComplexIso I E n).inv ≫ tensorSingleInclusion E _ ≫
        E ◁ (CochainComplex.singleFunctor _ 0).map (quotientTransition I h) := by
  apply (cancel_epi (tensorQuotientComplexIso I E n).hom).mp
  rw [← Category.assoc, tensorQuotientComplexIso_naturality]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact tensorSingleInclusion_naturality E _

set_option backward.isDefEq.respectTransparency false in
private def reductionTensorTowerIso {A : Type u} [CommRing A] (I : Ideal A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) :
    reductionTower I E ≅ quotientSingleTower I ⋙ tensorLeft E :=
  natIsoOfOpSequence (fun n => (tensorQuotientComplexIso I E (n + 1)).symm ≪≫
    (AdicCompletionTor.tensorSingleIso E).app (ModuleCat.of A (A ⧸ I ^ (n + 1)))) (by
    intro n
    simpa only [reductionTower, quotientSingleTower, CategoryTheory.Functor.comp_map,
      Functor.ofOpSequence_map_homOfLE_succ, Iso.trans_hom, Iso.symm_hom,
      tensorSingleIso_hom, tensorLeft, curriedTensor_obj_map, curriedTensor_obj_obj,
      CategoryTheory.Functor.comp_obj, Functor.ofOpSequence_obj, Category.assoc] using
      reductionTensorIso_naturality I E (Nat.add_le_add_right (Nat.le_succ n) 1))

set_option backward.isDefEq.respectTransparency false in
private def derivedTensorQuotientTowerIso
    {A : Type u} [CommRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat) :
    NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj (DerivedCategory.Q.obj E) ≅
      reductionTower I E ⋙ DerivedCategory.Q :=
  CategoryTheory.Functor.isoWhiskerRight (idealPowerQuotientSystemIso I)
      (T.tensor.obj (DerivedCategory.Q.obj E)) ≪≫
    natIsoOfOpSequence
      (F := (quotientSingleTower I ⋙ DerivedCategory.Q) ⋙
        T.tensor.obj (DerivedCategory.Q.obj E))
      (G := (quotientSingleTower I ⋙ tensorLeft E) ⋙ DerivedCategory.Q)
      (fun n => derivedTensorSingleIso T E hE (ModuleCat.of A (A ⧸ I ^ (n + 1))))
      (fun n => by
        simpa only [quotientSingleTower, Functor.comp_map,
          Functor.ofOpSequence_map_homOfLE_succ, CategoryTheory.Functor.comp_obj,
          Functor.ofOpSequence_obj, tensorLeft, curriedTensor_obj_map,
          curriedTensor_obj_obj] using
          derivedTensorSingleIso_naturality T E hE
            (quotientTransition I (Nat.add_le_add_right (Nat.le_succ n) 1))) ≪≫
    (CategoryTheory.Functor.isoWhiskerRight (reductionTensorTowerIso I E) DerivedCategory.Q).symm

set_option backward.isDefEq.respectTransparency false in
private theorem kFlat_completion_isDerivedLimit
    {A : Type u} [CommRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    IsDerivedLimit
      (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj (DerivedCategory.Q.obj E))
      (DerivedCategory.Q.obj (adicCompletionComplex I E)) :=
  isDerivedLimit_of_natIso (derivedTensorQuotientTowerIso I T E hE).symm
    (completion_isDerivedLimit_reductionTower I E)

private theorem completion_tensor_iso_of_pseudoCoherent
    {A : Type u} [CommRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (C : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    (hC : ∀ K, IsDerivedLimit
      (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) (C.obj K))
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : DerivedCategory.TStructure.t.minus K)
    (L : DerivedCategory (ModuleCat.{u} A)) (hL : StacksDraft.PseudoCoherence.IsPseudoCoherent L) :
    Nonempty (C.obj ((T.tensor.obj K).obj L) ≅ (T.tensor.obj (C.obj K)).obj L) := by
  obtain ⟨E, b, hE, hproj, ⟨e⟩⟩ := exists_boundedAbove_projective_representative K hK
  let : E.IsStrictlyLE b := hE
  let : ∀ i, Projective (E.X i) := hproj
  have hkE : E.KFlat := CochainComplex.KFlat.kFlat_of_flat E b
  obtain ⟨F, hF, ⟨f⟩⟩ := hL
  obtain ⟨c, hc⟩ := hF.upperBound
  let : F.IsStrictlyLE c := hc
  let : ∀ i, Module.Free A (F.X i) := fun i => (hF.finiteFree i).2
  let : ∀ i, Module.Finite A (F.X i) := fun i => (hF.finiteFree i).1
  have hkF : F.KFlat := CochainComplex.KFlat.kFlat_of_flat F c
  obtain ⟨eC⟩ := nonempty_iso_of_isDerivedLimit (hC (DerivedCategory.Q.obj E))
    (kFlat_completion_isDerivedLimit I T E hkE)
  obtain ⟨eCF⟩ := nonempty_iso_of_isDerivedLimit (hC (DerivedCategory.Q.obj (E ⊗ F)))
    (kFlat_completion_isDerivedLimit I T (E ⊗ F)
      (CochainComplex.KFlat.tensor A E F hkE hkF))
  obtain ⟨eT⟩ := nonempty_derivedTensor_iso_tensor_of_kFlat_right T
    (adicCompletionComplex I E) F hkF
  let eKL := (T.tensor.mapIso e.symm).app L ≪≫
    (T.tensor.obj (DerivedCategory.Q.obj E)).mapIso f.symm ≪≫
      T.comparison E F hkE hkF
  let eCK := C.mapIso e.symm ≪≫ eC
  exact ⟨C.mapIso eKL ≪≫ eCF ≪≫
    DerivedCategory.Q.mapIso (adicCompletionTensorComplexIso I E F b c).symm ≪≫
      eT.symm ≪≫ (T.tensor.mapIso eCK.symm).app (DerivedCategory.Q.obj F) ≪≫
        (T.tensor.obj (C.obj K)).mapIso f⟩


/-- **Stacks 0EEV.** Derived completion of a bounded-above complex commutes with derived
tensor product by a finite module, and more generally by a pseudo-coherent complex. -/
@[stacks 0EEV]
public theorem derivedCompletion_tensor_iso_of_boundedAbove
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun K ↦ IsDerivedComplete I K
    ∀ (C : Functor (DerivedCategory (ModuleCat.{u} A)) P.FullSubcategory),
    Nonempty (C ⊣ P.ι) →
    (∀ K, IsDerivedLimit
      (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K)
      ((C ⋙ P.ι).obj K)) →
    ∀ (K : DerivedCategory (ModuleCat.{u} A)),
    DerivedCategory.TStructure.t.minus K →
      (∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
        Nonempty
          ((C ⋙ P.ι).obj
              ((T.tensor.obj K).obj
                ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                  (ModuleCat.of A M))) ≅
            (T.tensor.obj ((C ⋙ P.ι).obj K)).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                (ModuleCat.of A M)))) ∧
      (∀ L : DerivedCategory (ModuleCat.{u} A), StacksDraft.PseudoCoherence.IsPseudoCoherent L →
        Nonempty
          ((C ⋙ P.ι).obj ((T.tensor.obj K).obj L) ≅
            (T.tensor.obj ((C ⋙ P.ι).obj K)).obj L)) := by
  dsimp only
  intro C _ hC K hK
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun X => IsDerivedComplete I X
  have h := completion_tensor_iso_of_pseudoCoherent I T (C ⋙ P.ι) hC K hK
  exact ⟨fun M _ _ _ => h _ (isPseudoCoherent_single_of_finite M), h⟩
end AdicCompletionPseudoCoherentTensor

end
