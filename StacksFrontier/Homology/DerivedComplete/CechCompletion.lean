module

public import Mathlib.RingTheory.Flat.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.RingTheory.LocalCohomology.CechModel.BoundedTerms
public import StacksFrontier.RingTheory.Cech.Cohomology
public import StacksFrontier.RingTheory.Cech.Extended
public import StacksFrontier.RingTheory.Cech.KFlat
public import StacksFrontier.RingTheory.Cech.Tensor

section


/-!
# Derived completion by an alternating Čech complex

For a finite family of generators of an ideal, derived completion is computed functorially by
derived Hom from the associated extended alternating Čech complex. The resulting functor is a
reflection onto the derived-complete objects.

## Main definitions

* `extendedCechObject`: the extended alternating Čech complex, regarded as an object
  of the derived category.
* `cechCompletionFunctor`: derived Hom from that Čech object.

## Main results

* `extendedCechObject_tensorIso`: the derived tensor comparison with the
  coefficient Čech complex in the original derived category.
* `extendedCechObject_localizedTensor_isZero`: the derived tensor product of the Čech object
  with a localization at an element of the ideal vanishes.
* `cechCompletion_localizedHomIso`: the identification of `RHom_A(A_g, RHom_A(Č(f), K))` with
  derived Hom from the Čech complex with coefficients in `A_g`.
* `cechCompletion_isReflection`: the Čech completion is derived complete and has the
  universal property of the left adjoint to the inclusion of derived-complete objects.

## Implementation notes

The finite list of generators is represented by a map `Fin r → A`. Derived Hom and the derived
tensor product are those of `StacksDraft.DerivedHom.derivedHomAdjunction`.

## References

* [The Stacks Project, Tag 091V](https://stacks.math.columbia.edu/tag/091V)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CechCompletion

open MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
section

/-- The isomorphism `Č(f, M) ≅ M ⊗ Č(f, R)` of Čech complexes. -/
private noncomputable def cechTensorIso {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (M : ModuleCat.{u} R) :
    Cech.cechComplex f M ≅
      ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Cech.cechComplex f R) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p => (ExtendedCech.termTensorEquiv f M p).toModuleIso) ?_
  intro p q hpq
  obtain rfl : q = p + 1 := hpq.symm
  apply ModuleCat.hom_ext
  simpa only [Functor.mapHomologicalComplex_obj_d, Cech.cechComplex,
    CochainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearEquiv.toModuleIso_hom, curriedTensor_obj_map,
    ModuleCat.hom_whiskerLeft] using (ExtendedCech.termTensorEquiv_comm_d f M p).symm

/-- The derived tensor product of `M` with the extended Čech complex of `R` is the extended
Čech complex of `M`, in `D(R)`. -/
public noncomputable def extendedCechObject_tensorIso {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (M : ModuleCat.{u} R) :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M),
          DerivedCategory.Q.obj
            ((Cech.cechComplex f R).extend ComplexShape.embeddingUpNat)) ≅
      DerivedCategory.Q.obj
        ((Cech.cechComplex f M).extend ComplexShape.embeddingUpNat) :=
  (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensorIso _ _
      (Cech.kFlat_extend_cechComplex f) ≪≫
    DerivedCategory.Q.mapIso
      (StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso M _ ≪≫
        (HomologicalComplex.mapHomologicalComplexExtendIso (tensorLeft M)
          (Cech.cechComplex f R) ComplexShape.embeddingUpNat).symm ≪≫
        (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (cechTensorIso f M).symm)

/-- Localizing the extended Čech object at any element of its defining ideal annihilates it:
its derived tensor product with `R_g` vanishes in `D(R)`. -/
public theorem extendedCechObject_localizedTensor_isZero
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (g : R) (hg : g ∈ Ideal.span (Set.range f)) :
    IsZero ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).tensor.obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj
        (ModuleCat.of R (Localization.Away g))),
       DerivedCategory.Q.obj
        ((Cech.cechComplex f R).extend ComplexShape.embeddingUpNat))) :=
  IsZero.of_iso (Cech.extendedCechObject_localized_isZero f g hg)
    (extendedCechObject_tensorIso f (ModuleCat.of R (Localization.Away g)))

end

end CechCompletion

@[expose] public noncomputable section

namespace CechCompletion

/-- The extended alternating Čech complex of a finite family `f`, viewed in `D(A)`. -/
public noncomputable abbrev extendedCechObject (A : Type u) [CommRing A] {r : ℕ}
    (f : Fin r → A) : DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.Q.obj ((Cech.cechComplex f A).extend ComplexShape.embeddingUpNat)

/-- The functor `K ↦ RHom_A(Č(f), K)`, where `Č(f)` is the extended alternating Čech
complex of the finite family `f`. -/
public noncomputable def cechCompletionFunctor (A : Type u) [CommRing A] {r : ℕ}
    (f : Fin r → A) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  ((Functor.const (DerivedCategory (ModuleCat.{u} A))).obj
      (Opposite.op (extendedCechObject A f))).prod' (Functor.id _) ⋙
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom

/-- `RHom_A(A_g, RHom_A(Č(f), K))` is derived Hom from the Čech complex with coefficients in
`A_g`, in `D(A)`. -/
public noncomputable def cechCompletion_localizedHomIso
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A) (g : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    let D := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
    D.hom.obj
      (Opposite.op (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat A) 0).obj
          (ModuleCat.of A (Localization.Away g)))),
        (cechCompletionFunctor A f).obj K) ≅
      D.hom.obj (Opposite.op (DerivedCategory.Q.obj
        ((Cech.cechComplex f (Localization.Away g)).extend
          ComplexShape.embeddingUpNat)), K) :=
  (StacksDraft.DerivedHom.derivedHomCurrying.iso _ _ K) ≪≫
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.mapIso
      (Iso.prod (extendedCechObject_tensorIso f
        (ModuleCat.of A (Localization.Away g))).symm.op (Iso.refl K))

end CechCompletion
end

end

section


open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CechCompletion

private theorem bijective_precomp_unit
    {C : Type u} [Category.{v} C] (F : C ⥤ C) (η : 𝟭 C ⟶ F)
    (X E : C) [IsIso (η.app E)] [Epi (F.map (η.app X))] :
    Function.Bijective (fun g : F.obj X ⟶ E ↦ η.app X ≫ g) := by
  constructor
  · intro a b hab
    have h := congrArg F.map hab
    simp only [Functor.map_comp] at h
    have hm := (cancel_epi (F.map (η.app X))).mp h
    apply (cancel_mono (η.app E)).mp
    simpa only [← η.naturality, Functor.id_map] using congrArg
      (fun k ↦ η.app (F.obj X) ≫ k) hm
  · intro a
    refine ⟨F.map a ≫ inv (η.app E), ?_⟩
    change η.app X ≫ F.map a ≫ inv (η.app E) = a
    rw [← Category.assoc, ← η.naturality]
    simp

section DerivedHom

variable {R : Type u} [CommRing R]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]
  (d : StacksDraft.DerivedHom.DerivedHomAdjunction R)

private theorem tensor_map_zero_left
    (X Y L : DerivedCategory (ModuleCat.{u} R)) :
    d.tensor.map (show (X, L) ⟶ (Y, L) from (0, 𝟙 L)) = 0 := by
  have h := d.homEquiv_naturality_left (L := L)
    (M := d.tensor.obj (Y, L)) (0 : X ⟶ Y)
    ((d.homEquiv Y L (d.tensor.obj (Y, L))).symm (𝟙 _))
  simpa only [zero_comp, map_zero, AddEquiv.apply_symm_apply, Category.comp_id] using h.symm

private theorem tensor_map_zero_right
    (X L M : DerivedCategory (ModuleCat.{u} R)) :
    d.tensor.map (show (X, L) ⟶ (X, M) from (𝟙 X, 0)) = 0 := by
  apply (cancel_mono (d.tensorSwap X M).hom).mp
  rw [d.tensorSwap_naturality, tensor_map_zero_left, comp_zero, zero_comp]

private theorem tensor_isZero_right
    (X L : DerivedCategory (ModuleCat.{u} R)) (hL : IsZero L) :
    IsZero (d.tensor.obj (X, L)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← d.tensor_map_id, hL.eq_of_src (𝟙 L) 0, tensor_map_zero_right]

private theorem derivedHom_isZero_left
    (L M : DerivedCategory (ModuleCat.{u} R)) (hL : IsZero L) :
    IsZero (d.hom.obj (Opposite.op L, M)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (d.homEquiv _ L M).injective
  exact (tensor_isZero_right d _ L hL).eq_of_src _ _

end DerivedHom

section Augmentation

open MonoidalCategory

variable {R : Type u} [CommRing R]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]
  (d : StacksDraft.DerivedHom.DerivedHomData R) (c : StacksDraft.DerivedHom.DerivedHomCurrying d)

private noncomputable abbrev tensorUnitRight
    (K : DerivedCategory (ModuleCat.{u} R)) :
    d.tensor.obj (K, DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ))) ≅ K :=
  d.tensorSwap _ _ ≪≫ c.tensorUnitLeft K

private theorem tensorUnitRight_naturality
    {K L : DerivedCategory (ModuleCat.{u} R)} (g : K ⟶ L) :
    d.tensor.map (g, 𝟙 (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ)))) ≫
        (tensorUnitRight d c L).hom =
      (tensorUnitRight d c K).hom ≫ g := by
  dsimp only [tensorUnitRight, Iso.trans_hom]
  rw [← Category.assoc, d.tensorSwap_naturality, Category.assoc,
    c.tensorUnitLeft_naturality, Category.assoc]

private noncomputable def homUnitOfAugmentation
    (C : DerivedCategory (ModuleCat.{u} R))
    (ε : C ⟶ DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ))) :
    𝟭 (DerivedCategory (ModuleCat.{u} R)) ⟶
      ((Functor.const _).obj (Opposite.op C)).prod' (𝟭 _) ⋙ d.hom where
  app K := (d.homEquiv K C K).symm
    (d.tensor.map (𝟙 K, ε) ≫ (tensorUnitRight d c K).hom)
  naturality {X Y} g := by
    apply (d.homEquiv X C Y).injective
    change d.homEquiv X C Y (g ≫ _) = d.homEquiv X C Y
      (_ ≫ d.hom.map (show (Opposite.op C, X) ⟶ (Opposite.op C, Y) from (𝟙 _, g)))
    rw [d.homEquiv_naturality_left, d.homEquiv_naturality_right]
    simp only [AddEquiv.apply_symm_apply]
    rw [← Category.assoc, d.tensor_map_comp]
    simp only [Category.comp_id, Category.id_comp]
    rw [Category.assoc, ← tensorUnitRight_naturality d c g,
      ← Category.assoc, d.tensor_map_comp]
    simp only [Category.comp_id, Category.id_comp]

private theorem homEquiv_homUnitOfAugmentation_app
    (C : DerivedCategory (ModuleCat.{u} R))
    (ε : C ⟶ DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
    (K : DerivedCategory (ModuleCat.{u} R)) :
    d.homEquiv K C K ((homUnitOfAugmentation d c C ε).app K) =
      d.tensor.map (𝟙 K, ε) ≫ (tensorUnitRight d c K).hom :=
  (d.homEquiv K C K).apply_symm_apply _

end Augmentation

open MonoidalCategory

/-- The degree-zero term of the extended Čech complex is its coefficient module. -/
private noncomputable def cechTermZeroIso {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (M : ModuleCat.{u} R) :
    (Cech.cechComplex f M).X 0 ≅ M := by
  classical
  exact ((DirectSum.linearEquivFunOnFintype R _ _).trans
    (ExtendedAlternatingCech.cechZeroEquiv f M)).toModuleIso

/-- The augmentation of the extended Čech complex to the coefficient module in degree zero. -/
private noncomputable def cechAugmentation {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (M : ModuleCat.{u} R) :
    (Cech.cechComplex f M).extend ComplexShape.embeddingUpNat ⟶
      (CochainComplex.singleFunctor (ModuleCat R) 0).obj M := by
  let K := Cech.cechComplex f M
  let e := ComplexShape.embeddingUpNat
  refine HomologicalComplex.mkHomToSingle
    ((K.extendXIso e (i := 0) (i' := 0) rfl).hom ≫
      (cechTermZeroIso f M).hom) ?_
  intro i hi
  apply (K.isZero_extend_X e i ?_).eq_of_src
  intro n hn
  change (n : ℤ) = i at hn
  change i + 1 = (0 : ℤ) at hi
  omega

/-- The Čech augmentation is an isomorphism in degree zero. -/
private theorem isIso_cechAugmentation_f_zero {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (M : ModuleCat.{u} R) :
    IsIso ((cechAugmentation f M).f 0) := by
  dsimp only [cechAugmentation]
  rw [HomologicalComplex.mkHomToSingle_f]
  infer_instance

attribute [local instance] HasDerivedCategory.standard

/-- Transposing the Čech augmentation gives the natural map to Čech completion. -/
private noncomputable def cechCompletionUnit (A : Type u) [CommRing A]
    {r : ℕ} (f : Fin r → A) :
    𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶ cechCompletionFunctor A f :=
  homUnitOfAugmentation (StacksDraft.DerivedHom.derivedHomAdjunction (R := A))
    StacksDraft.DerivedHom.derivedHomCurrying (extendedCechObject A f)
    (DerivedCategory.Q.map (cechAugmentation f (ModuleCat.of A A)))

/-- Under tensor–Hom adjunction the completion unit is induced by the Čech augmentation. -/
private theorem homEquiv_cechCompletionUnit_app (A : Type u) [CommRing A]
    {r : ℕ} (f : Fin r → A) (K : DerivedCategory (ModuleCat.{u} A)) :
    let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
    d.homEquiv K (extendedCechObject A f) K ((cechCompletionUnit A f).app K) =
      d.tensor.map (𝟙 K, DerivedCategory.Q.map (cechAugmentation f (ModuleCat.of A A))) ≫
        (tensorUnitRight d StacksDraft.DerivedHom.derivedHomCurrying K).hom :=
  homEquiv_homUnitOfAugmentation_app _ _ _ _ _

/-- Derived Hom from a localization in the defining ideal annihilates Čech completion. -/
private theorem cechCompletion_localizedHom_isZero
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A)
    (g : A) (hg : g ∈ Ideal.span (Set.range f))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsZero ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
      (Opposite.op (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat A) 0).obj
          (ModuleCat.of A (Localization.Away g)))),
        (cechCompletionFunctor A f).obj K)) :=
  IsZero.of_iso
    (derivedHom_isZero_left
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).toDerivedHomAdjunction _ K
      (Cech.extendedCechObject_localized_isZero f g hg))
    (cechCompletion_localizedHomIso A f g K)

private theorem kFlat_single_ring (A : Type u) [CommRing A] (n : ℤ) :
    ((CochainComplex.singleFunctor (ModuleCat A) n).obj (ModuleCat.of A A)).KFlat := by
  let K := (CochainComplex.singleFunctor (ModuleCat A) n).obj (ModuleCat.of A A)
  have (i : ℤ) : Module.Flat A (K.X i) := by
    by_cases hi : i = n
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) n
          (ModuleCat.of A A) i hi).toLinearEquiv
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n
          (ModuleCat.of A A) i hi).isoZero.toLinearEquiv
  exact CochainComplex.KFlat.kFlat_of_flat K n

private noncomputable def tensor_single_ring_iso
    (A : Type u) [CommRing A] (M : ModuleCat.{u} A) (n : ℤ) :
    let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
    d.tensor.obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat A) n).obj
        (ModuleCat.of A A)),
       DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat A) 0).obj M)) ≅
    (DerivedCategory.singleFunctor (ModuleCat A) n).obj M := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  let U := (CochainComplex.singleFunctor (ModuleCat A) n).obj (ModuleCat.of A A)
  exact d.tensorSwap _ _ ≪≫ d.tensorIso _ U (kFlat_single_ring A n) ≪≫
    DerivedCategory.Q.mapIso
      (StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso M U ≪≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorLeft M)
          (ComplexShape.up ℤ) n).app (ModuleCat.of A A) ≪≫
        (CochainComplex.singleFunctor (ModuleCat A) n).mapIso (ρ_ M)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) n).app M).symm

private theorem subsingleton_single_hom_of_derivedHom_isZero
    (A : Type u) [CommRing A] (M : ModuleCat.{u} A)
    (E : DerivedCategory (ModuleCat.{u} A))
    (h : IsZero ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
      (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M), E)))
    (n : ℤ) : Subsingleton ((DerivedCategory.singleFunctor (ModuleCat A) n).obj M ⟶ E) := by
  let e := tensor_single_ring_iso A M n
  constructor
  intro a b
  apply (cancel_epi e.hom).mp
  apply ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).homEquiv _ _ _).symm.injective
  exact h.eq_of_tgt _ _

private theorem subsingleton_ext_of_single_hom
    (A : Type u) [CommRing A] (M : ModuleCat.{u} A)
    (E : DerivedCategory (ModuleCat.{u} A))
    (h : ∀ n : ℤ, Subsingleton ((DerivedCategory.singleFunctor (ModuleCat A) n).obj M ⟶ E))
    (n : ℤ) : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M) E n) := by
  let S := DerivedCategory.singleFunctors (ModuleCat A)
  let e := (S.shiftIso (-n) n 0 (neg_add_cancel n)).app M
  let e' := (shiftEquiv' (DerivedCategory (ModuleCat A)) (-n) n (neg_add_cancel
    n)).toAdjunction.homEquiv
    ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M) E
  have := h n
  exact (e'.symm.trans (Iso.homCongr e (Iso.refl E))).injective.subsingleton

private theorem isDerivedComplete_of_localizedHom_isZero
    (A : Type u) [CommRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (h : ∀ g ∈ I, IsZero ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
      (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
        (ModuleCat.of A (Localization.Away g))), K))) :
    IsDerivedComplete I K := by
  rw [isDerivedComplete_iff_forall_exists_isDerivedLimit_isZero]
  intro g hg
  apply ((DerivedHomAway.tfae_ext_localization_vanishing A g K).2.2.out 1 3).mp
  intro n
  exact subsingleton_ext_of_single_hom A (ModuleCat.of A (Localization.Away g)) K
    (subsingleton_single_hom_of_derivedHom_isZero A _ K (h g hg)) n

private theorem cechCompletion_isDerivedComplete
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDerivedComplete (Ideal.span (Set.range f))
      ((cechCompletionFunctor A f).obj K) :=
  isDerivedComplete_of_localizedHom_isZero A _ _ fun g hg ↦
    cechCompletion_localizedHom_isZero A f g hg K

set_option backward.isDefEq.respectTransparency false in
private theorem tensorIso_naturality_left {R : Type u} [CommRing R]
    (d : StacksDraft.DerivedHom.DerivedHomData R)
    (K K' L : CochainComplex (ModuleCat R) ℤ) (hL : L.KFlat) (f : K ⟶ K') :
    d.tensor.map (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj L)) ≫
      (d.tensorIso K' L hL).hom =
    (d.tensorIso K L hL).hom ≫ DerivedCategory.Q.map (f ▷ L) := by
  simpa only [DerivedCategory.Q.map_id L, tensorHom_id] using
    d.tensorIso_naturality f (𝟙 L) hL hL

/-- Morphisms out of an object isomorphic to one with subsingleton Hom into `E` are unique. -/
private theorem subsingleton_hom_of_iso {C : Type u} [Category.{v} C] {X Y E : C} (e : X ≅ Y)
    [Subsingleton (Y ⟶ E)] : Subsingleton (X ⟶ E) :=
  (Iso.homCongr e (Iso.refl E)).injective.subsingleton

private theorem subsingleton_restrictScalars_hom_of_isDerivedComplete
    (A : Type u) [CommRing A] (I : Ideal A)
    (E : DerivedCategory (ModuleCat.{u} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (hE : IsDerivedComplete I E) (g : A) (hg : g ∈ I)
    (L : DerivedCategory (ModuleCat.{u} (Localization.Away g))) :
    Subsingleton (((ModuleCat.restrictScalars (algebraMap A (Localization.Away
      g))).mapDerivedCategory.obj L) ⟶ E) := by
  have h : ∀ L : DerivedCategory (ModuleCat.{u} (Localization.Away g)),
      Subsingleton (((ModuleCat.restrictScalars (algebraMap A (Localization.Away
        g))).mapDerivedCategory.obj L) ⟶ E) :=
    ((DerivedHomAway.tfae_ext_localization_vanishing A g E).2.2.out 3 2).mp
      ((isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero E g).mp (hE g hg))
  exact h L

private theorem subsingleton_single_away_hom_of_isDerivedComplete
    (A : Type u) [CommRing A] (I : Ideal A)
    (E : DerivedCategory (ModuleCat.{u} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (hE : IsDerivedComplete I E) (g : A) (hg : g ∈ I) (n : ℤ) :
    Subsingleton ((DerivedCategory.singleFunctor (ModuleCat A) n).obj
      (ModuleCat.of A (Localization.Away g)) ⟶ E) := by
  let F := ModuleCat.restrictScalars (algebraMap A (Localization.Away g))
  let L := (CochainComplex.singleFunctor (ModuleCat (Localization.Away g)) n).obj
    (ModuleCat.of (Localization.Away g) (Localization.Away g))
  have : Subsingleton ((DerivedCategory.Q ⋙ F.mapDerivedCategory).obj L ⟶ E) :=
    subsingleton_restrictScalars_hom_of_isDerivedComplete A I E hE g hg
      (DerivedCategory.Q.obj L)
  let eM : F.obj (ModuleCat.of (Localization.Away g) (Localization.Away g)) ≅
      ModuleCat.of A (Localization.Away g) :=
    (show F.obj (ModuleCat.of (Localization.Away g) (Localization.Away g)) ≃ₗ[A]
      ModuleCat.of A (Localization.Away g) from
      { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
        map_add' := fun _ _ => rfl,
        map_smul' := fun a x => by
          exact (@Algebra.smul_def A (Localization.Away g) _ _ _ a x).symm }).toModuleIso
  let e := F.mapDerivedCategoryFactors.app L ≪≫ DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app _) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) n).app _).symm ≪≫
      (DerivedCategory.singleFunctor (ModuleCat A) n).mapIso eM
  exact subsingleton_hom_of_iso e.symm

private theorem subsingleton_map_directSum_hom
    {R : Type u} [Ring R] {C : Type v} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] (F : ModuleCat.{max u w} R ⥤ C) [F.Additive]
    {ι : Type w} [Finite ι] (M : ι → ModuleCat.{max u w} R) (E : C)
    (h : ∀ i, Subsingleton (F.obj (M i) ⟶ E)) :
    Subsingleton (F.obj (ModuleCat.of R (DirectSum ι (fun i => (M i : Type (max u w))))) ⟶ E) := by
  classical
  have := Fintype.ofFinite ι
  constructor
  intro a b
  apply (cancel_epi (F.mapIso (ModuleCat.coprodIsoDirectSum M)).hom).mp
  apply (isColimitOfPreserves F (coproductIsCoproduct M)).hom_ext
  intro i
  exact (h i.as).elim _ _

private theorem subsingleton_single_cechTerm_hom_of_isDerivedComplete
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : DerivedCategory (ModuleCat.{u} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (hE : IsDerivedComplete (Ideal.span (Set.range f)) E)
    (p : ℕ) (hp : 0 < p) (n : ℤ) :
    Subsingleton ((DerivedCategory.singleFunctor (ModuleCat A) n).obj
      ((Cech.cechComplex f A).X p) ⟶ E) := by
  classical
  change Subsingleton ((DerivedCategory.singleFunctor (ModuleCat A) n).obj
    (ModuleCat.of A (Cech.cechTerm f A p)) ⟶ E)
  refine subsingleton_map_directSum_hom (DerivedCategory.singleFunctor (ModuleCat A) n)
    (fun s : { s : Finset (Fin r) // s.card = p } =>
      ModuleCat.of A (Cech.cechMod f A s.1)) E ?_
  intro s
  have hs : s.1.Nonempty := Finset.card_pos.mp (by omega)
  have hg : (∏ i ∈ s.1, f i) ∈ Ideal.span (Set.range f) := by
    obtain ⟨i, hi⟩ := hs
    exact (Ideal.span (Set.range f)).mem_of_dvd
      (Finset.dvd_prod_of_mem f hi) (Ideal.subset_span (Set.mem_range_self i))
  have := subsingleton_single_away_hom_of_isDerivedComplete A _ E hE
    (∏ i ∈ s.1, f i) hg n
  exact subsingleton_hom_of_iso ((DerivedCategory.singleFunctor (ModuleCat A) n).mapIso
    (ExtendedAlternatingCech.mlocREquiv f s.1).toModuleIso)

section
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

private theorem subsingleton_hom_of_bounded
    (K : CochainComplex C ℤ) (E : DerivedCategory C) (a : ℤ) (m : ℕ)
    (hz : ∀ i, i < a ∨ a + m ≤ i → IsZero (K.X i))
    (ht : ∀ i n, Subsingleton ((DerivedCategory.singleFunctor C n).obj (K.X i) ⟶ E)) :
    Subsingleton (DerivedCategory.Q.obj K ⟶ E) := by
  let P : ObjectProperty (DerivedCategory C) := ObjectProperty.leftOrthogonal (fun X => X = E)
  have hP : P (DerivedCategory.Q.obj K) :=
    Stacks.LocalCohomology.prop_Q_obj_of_bounded_terms P m a K hz (by
    intro i n Y f hY
    subst Y
    exact (ht i n).elim _ _)
  exact ⟨fun f g => (hP f rfl).trans (hP g rfl).symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem bijective_precomp_to_single
    (K : CochainComplex C ℤ) (E : DerivedCategory C) (M : C) (n a : ℤ) (m : ℕ)
    (π : K ⟶ (CochainComplex.singleFunctor C n).obj M) [IsIso (π.f n)]
    (hz : ∀ i, i < a ∨ a + m ≤ i → IsZero (K.X i))
    (ht : ∀ i, i ≠ n → ∀ q,
      Subsingleton ((DerivedCategory.singleFunctor C q).obj (K.X i) ⟶ E)) :
    Function.Bijective (fun f : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor C n).obj M) ⟶ E => DerivedCategory.Q.map π ≫ f) := by
  have hπ : IsIso (π.f n) := inferInstance
  have hS := Stacks.LocalCohomology.toSingleKernelShortComplex_shortExact π hπ
  have hzero : IsZero ((kernel π).X n) :=
    Stacks.LocalCohomology.isZero_kernel_toSingle_X_self π hπ
  have hiso := Stacks.LocalCohomology.isIso_kernel_ι_toSingle_f π hπ
  have hkerzero (i : ℤ) (hi : i < a ∨ a + m ≤ i) : IsZero ((kernel π).X i) := by
    obtain rfl | hin := eq_or_ne i n
    · exact hzero
    · have := hiso i hin
      exact (hz i hi).of_iso (asIso ((kernel.ι π).f i))
  have hkerterm (i q : ℤ) :
      Subsingleton ((DerivedCategory.singleFunctor C q).obj ((kernel π).X i) ⟶ E) := by
    obtain rfl | hin := eq_or_ne i n
    · exact ⟨fun f g => ((DerivedCategory.singleFunctor C q).map_isZero hzero).eq_of_src f g⟩
    · have := hiso i hin
      have := ht i hin q
      exact subsingleton_hom_of_iso ((DerivedCategory.singleFunctor C q).mapIso
        (asIso ((kernel.ι π).f i)))
  have : Subsingleton (DerivedCategory.Q.obj (kernel π) ⟶ E) :=
    subsingleton_hom_of_bounded (kernel π) E a m hkerzero hkerterm
  have hshift : Subsingleton (DerivedCategory.Q.obj ((kernel π)⟦(1 : ℤ)⟧) ⟶ E) := by
    apply subsingleton_hom_of_bounded _ E (a - 1) m
    · intro i hi
      exact hkerzero (i + 1) (by omega)
    · intro i q
      exact hkerterm (i + 1) q
  have : Subsingleton ((shiftFunctor (CochainComplex C ℤ) (1 : ℤ) ⋙ DerivedCategory.Q).obj (kernel
    π) ⟶ E) := hshift
  have : Subsingleton ((DerivedCategory.Q.obj (kernel π))⟦(1 : ℤ)⟧ ⟶ E) :=
    (Iso.homCongr ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app (kernel π)).symm
      (Iso.refl E)).injective.subsingleton
  let T := DerivedCategory.triangleOfSES hS
  have hT := DerivedCategory.triangleOfSES_distinguished hS
  constructor
  · intro f g hfg
    have hfg' : T.mor₂ ≫ (f - g) = 0 := by
      change DerivedCategory.Q.map π ≫ (f - g) = 0
      simpa only [Preadditive.comp_sub, sub_eq_zero] using hfg
    obtain ⟨b, hb⟩ := T.yoneda_exact₃ hT (f - g) hfg'
    apply sub_eq_zero.mp
    have hbzero : b = 0 := (show Subsingleton
      ((DerivedCategory.Q.obj (kernel π))⟦(1 : ℤ)⟧ ⟶ E) from inferInstance).elim b 0
    rw [hb, hbzero, comp_zero]
  · intro f
    have hfzero : T.mor₁ ≫ f = 0 := by
      change DerivedCategory.Q.map (kernel.ι π) ≫ f = 0
      exact Subsingleton.elim _ _
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT f hfzero
    exact ⟨g, hg.symm⟩
end

private theorem isIso_cofan_inj_of_isZero
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {F : ι → C} (c : Cofan F) (hc : IsColimit c) (j : ι)
    (hz : ∀ i, i ≠ j → IsZero (F i)) : IsIso (c.inj j) := by
  classical
  let f (i : ι) : F i ⟶ F j := if h : i = j then eqToHom (congrArg F h) else 0
  refine ⟨⟨Cofan.IsColimit.desc hc f, ?_, ?_⟩⟩
  · rw [Cofan.IsColimit.fac]
    simp [f]
  · apply Cofan.IsColimit.hom_ext hc
    intro i
    rw [← Category.assoc, Cofan.IsColimit.fac]
    by_cases hi : i = j
    · subst i; simp [f]
    · exact (hz i hi).eq_of_src _ _

private theorem isIso_ιTensorObj_single
    {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (M : ModuleCat.{u} R) (n i : ℤ) :
    IsIso (HomologicalComplex.ιTensorObj K
      ((CochainComplex.singleFunctor (ModuleCat R) n).obj M) (i - n) n i (sub_add_cancel i n)) := by
  let L := (CochainComplex.singleFunctor (ModuleCat R) n).obj M
  let Z := ((GradedObject.mapBifunctor (curriedTensor (ModuleCat R)) ℤ ℤ).obj K.X).obj L.X
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  change IsIso ((Z.cofanMapObj p i).inj ⟨(i-n,n), sub_add_cancel i n⟩)
  apply isIso_cofan_inj_of_isZero _ (Z.isColimitCofanMapObj p i)
  intro b hb
  have hbn : b.1.2 ≠ n := by
    intro h
    apply hb
    apply Subtype.ext
    apply Prod.ext
    · have hh := b.2
      change b.1.1 + b.1.2 = i at hh
      change b.1.1 = i - n
      omega
    · exact h
  exact (tensorLeft (K.X b.1.1)).map_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n M b.1.2 hbn)

private noncomputable def tensorSingleRingXIso
    {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n i : ℤ) :
    (K ⊗ (CochainComplex.singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R)).X i ≅
      K.X (i - n) := by
  have := isIso_ιTensorObj_single K (ModuleCat.of R R) n i
  exact (asIso (HomologicalComplex.ιTensorObj K _ (i-n) n i (sub_add_cancel i n))).symm ≪≫
    (tensorLeft (K.X (i-n))).mapIso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of R R)) ≪≫
    (ρ_ (K.X (i-n)))

/-- The extended Čech complex is supported in the interval of degrees `0, …, r`. -/
private theorem extendedCechComplex_isZero_X
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (i : ℤ)
    (hi : i < 0 ∨ (r : ℤ) + 1 ≤ i) :
    IsZero (((Cech.cechComplex f A).extend ComplexShape.embeddingUpNat).X i) := by
  by_cases hn : 0 ≤ i
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n := ⟨i.toNat, by simp [hn]⟩
    have hs : Subsingleton (Cech.cechTerm f A n) := by
      constructor
      intro x y
      apply DirectSum.ext
      intro t
      exact False.elim (by
        have ht := Finset.card_le_univ t.1
        simp only [Fintype.card_fin] at ht
        omega)
    exact (ModuleCat.isZero_iff_subsingleton.mpr hs).of_iso
      ((Cech.cechComplex f A).extendXIso ComplexShape.embeddingUpNat
        (i := n) (i' := (n : ℤ)) (by simp))
  · apply HomologicalComplex.isZero_extend_X
    intro n hn'
    simp only [ComplexShape.embeddingUpNat_f] at hn'
    omega

/-- Every positive Čech term, in every degree, is orthogonal to a complete object. -/
private theorem subsingleton_single_extendedCech_hom
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : DerivedCategory (ModuleCat.{u} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (hE : IsDerivedComplete (Ideal.span (Set.range f)) E)
    (i : ℤ) (hi : i ≠ 0) (q : ℤ) :
    Subsingleton ((DerivedCategory.singleFunctor (ModuleCat A) q).obj
      (((Cech.cechComplex f A).extend ComplexShape.embeddingUpNat).X i) ⟶ E) := by
  by_cases hn : 0 ≤ i
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n := ⟨i.toNat, by simp [hn]⟩
    have := subsingleton_single_cechTerm_hom_of_isDerivedComplete A f E hE n (by omega) q
    exact subsingleton_hom_of_iso ((DerivedCategory.singleFunctor (ModuleCat A) q).mapIso
      ((Cech.cechComplex f A).extendXIso ComplexShape.embeddingUpNat
        (i := n) (i' := (n : ℤ)) (by simp)))
  · exact ⟨fun a b => ((DerivedCategory.singleFunctor (ModuleCat A) q).map_isZero
      (extendedCechComplex_isZero_X f i (Or.inl (lt_of_not_ge hn)))).eq_of_src a b⟩

/-- The Čech augmentation induces a bijection on morphisms to a complete object. -/
private theorem bijective_precomp_cechAugmentation
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : DerivedCategory (ModuleCat.{u} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (hE : IsDerivedComplete (Ideal.span (Set.range f)) E) :
    Function.Bijective (fun g : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A A)) ⟶ E =>
        DerivedCategory.Q.map (cechAugmentation f (ModuleCat.of A A)) ≫ g) := by
  have := isIso_cechAugmentation_f_zero f (ModuleCat.of A A)
  apply bijective_precomp_to_single _ E (ModuleCat.of A A) 0 0 (r + 1)
  · intro i hi
    exact extendedCechComplex_isZero_X f i (by simpa using hi)
  · exact subsingleton_single_extendedCech_hom A f E hE

/-- Tensoring a morphism with a shifted copy of the ring preserves componentwise
isomorphisms in the corresponding degree. -/
private theorem isIso_tensor_single_f
    {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ L) (n i : ℤ) [IsIso (f.f (i - n))] :
    IsIso ((f ▷ (CochainComplex.singleFunctor (ModuleCat R) n).obj
      (ModuleCat.of R R)).f i) := by
  let S := (CochainComplex.singleFunctor (ModuleCat R) n).obj (ModuleCat.of R R)
  have := isIso_ιTensorObj_single K (ModuleCat.of R R) n i
  have := isIso_ιTensorObj_single L (ModuleCat.of R R) n i
  have h := Stacks.HomComplex.Currying.ιTensorObj_comp_whiskerRight (L := S) f (i - n) n i
    (sub_add_cancel i n)
  have : IsIso (HomologicalComplex.ιTensorObj K S (i - n) n i (sub_add_cancel i n) ≫
      (f ▷ S).f i) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.ιTensorObj K S (i - n) n i (sub_add_cancel i n)) _

/-- The tensor of the Čech augmentation with a shifted ring is universal on maps
into a derived-complete object. -/
private theorem bijective_precomp_cechAugmentation_tensor_single
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : DerivedCategory (ModuleCat.{u} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (hE : IsDerivedComplete (Ideal.span (Set.range f)) E) (n : ℤ) :
    let S := (CochainComplex.singleFunctor (ModuleCat A) n).obj (ModuleCat.of A A)
    Function.Bijective (fun g : DerivedCategory.Q.obj S ⟶ E =>
      DerivedCategory.Q.map ((cechAugmentation f (ModuleCat.of A A) ▷ S) ≫
        (λ_ S).hom) ≫ g) := by
  let C := (Cech.cechComplex f A).extend ComplexShape.embeddingUpNat
  let S := (CochainComplex.singleFunctor (ModuleCat A) n).obj (ModuleCat.of A A)
  let π := (cechAugmentation f (ModuleCat.of A A) ▷ S) ≫ (λ_ S).hom
  have hε : IsIso ((cechAugmentation f (ModuleCat.of A A)).f (n - n)) := by
    rw [sub_self]
    exact isIso_cechAugmentation_f_zero f (ModuleCat.of A A)
  have : IsIso ((cechAugmentation f (ModuleCat.of A A) ▷ S).f n) :=
    isIso_tensor_single_f _ n n
  have : IsIso (π.f n) := by
    dsimp [π]
    infer_instance
  apply bijective_precomp_to_single (C ⊗ S) E (ModuleCat.of A A) n n (r + 1) π
  · intro i hi
    exact (extendedCechComplex_isZero_X f (i - n) (by push_cast at hi; omega)).of_iso
      (tensorSingleRingXIso C n i)
  · intro i hi q
    have := subsingleton_single_extendedCech_hom A f E hE (i - n) (sub_ne_zero.mpr hi) q
    exact subsingleton_hom_of_iso ((DerivedCategory.singleFunctor (ModuleCat A) q).mapIso
      (tensorSingleRingXIso C n i))

/-- Precomposition with an isomorphism is bijective. -/
private theorem bijective_precomp_hom {C : Type u} [Category.{v} C] {X Y E : C} (e : X ≅ Y) :
    Function.Bijective (fun g : Y ⟶ E => e.hom ≫ g) :=
  ⟨fun _ _ hab => (cancel_epi e.hom).mp hab, fun a => ⟨e.inv ≫ a, by simp⟩⟩

/-- Transposing an augmentation identifies the tests for its unit with
precomposition by the corresponding tensor augmentation. -/
private theorem bijective_postcomp_homUnitOfAugmentation
    {R : Type u} [CommRing R] [HasDerivedCategory.{v} (ModuleCat.{u} R)]
    (d : StacksDraft.DerivedHom.DerivedHomData R)
    (c : StacksDraft.DerivedHom.DerivedHomCurrying d)
    (C X E : DerivedCategory (ModuleCat.{u} R))
    (ε : C ⟶ DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
    (h : Function.Bijective (fun a : X ⟶ E =>
      d.tensor.map (show (X, C) ⟶ (X, DerivedCategory.Q.obj
        (𝟙_ (CochainComplex (ModuleCat R) ℤ))) from (𝟙 X, ε)) ≫ (tensorUnitRight d c X).hom ≫ a)) :
    Function.Bijective (fun a : X ⟶ E => a ≫ (homUnitOfAugmentation d c C ε).app E) := by
  have hn (a : X ⟶ E) :
      d.homEquiv X C E (a ≫ (homUnitOfAugmentation d c C ε).app E) =
        d.tensor.map (show (X, C) ⟶ (X, DerivedCategory.Q.obj
        (𝟙_ (CochainComplex (ModuleCat R) ℤ))) from (𝟙 X, ε)) ≫ (tensorUnitRight d c X).hom ≫ a :=
          by
    rw [d.homEquiv_naturality_left, homEquiv_homUnitOfAugmentation_app,
      ← Category.assoc, d.tensor_map_comp]
    simp only [Category.comp_id, Category.id_comp]
    rw [← tensorUnitRight_naturality d c a, ← Category.assoc, d.tensor_map_comp]
    simp only [Category.comp_id, Category.id_comp]
  constructor
  · intro a b hab
    apply h.injective
    exact (hn a).symm.trans ((congrArg (d.homEquiv X C E) hab).trans (hn b))
  · intro b
    obtain ⟨a, ha⟩ := h.surjective (d.homEquiv X C E b)
    exact ⟨a, (d.homEquiv X C E).injective ((hn a).trans ha)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The completion unit induces a bijection on all tests by shifted copies of the ring. -/
private theorem bijective_postcomp_cechCompletionUnit_single
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : DerivedCategory (ModuleCat.{u} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (hE : IsDerivedComplete (Ideal.span (Set.range f)) E) (n : ℤ) :
    let S := (CochainComplex.singleFunctor (ModuleCat A) n).obj (ModuleCat.of A A)
    Function.Bijective (fun a : DerivedCategory.Q.obj S ⟶ E =>
      a ≫ (cechCompletionUnit A f).app E) := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  let c := StacksDraft.DerivedHom.derivedHomCurrying (R := A)
  let C := (Cech.cechComplex f A).extend ComplexShape.embeddingUpNat
  let S := (CochainComplex.singleFunctor (ModuleCat A) n).obj (ModuleCat.of A A)
  let ε : C ⟶ 𝟙_ (CochainComplex (ModuleCat A) ℤ) :=
    cechAugmentation f (ModuleCat.of A A)
  let e := d.tensorSwap (DerivedCategory.Q.obj S) (DerivedCategory.Q.obj C) ≪≫
    d.tensorIso C S (kFlat_single_ring A n)
  have heq : d.tensor.map (𝟙 (DerivedCategory.Q.obj S), DerivedCategory.Q.map ε) ≫
      (tensorUnitRight d c (DerivedCategory.Q.obj S)).hom =
      e.hom ≫ DerivedCategory.Q.map ((ε ▷ S) ≫ (λ_ S).hom) := by
    dsimp only [tensorUnitRight, Iso.trans_hom, e]
    rw [← Category.assoc, d.tensorSwap_naturality (𝟙 (DerivedCategory.Q.obj S))
      (DerivedCategory.Q.map ε), Category.assoc,
      ← c.tensorUnitLeft_comparison S (kFlat_single_ring A n)]
    simp only [Category.assoc]
    rw [reassoc_of% tensorIso_naturality_left d C _ S (kFlat_single_ring A n) ε]
    simp only [Functor.map_comp, Functor.mapIso_hom]
  apply bijective_postcomp_homUnitOfAugmentation d c
  have h := bijective_precomp_cechAugmentation_tensor_single A f E hE n
  convert (bijective_precomp_hom e).comp h using 1
  ext a
  dsimp only [Function.comp_apply]
  rw [← Category.assoc, heq, Category.assoc]

open HomologicalComplex in
/-- The homology map of a morphism from a single complex is the induced map on cycles. -/
private theorem homologyMap_mkHomFromSingle_cycles
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (P : C) (n : ℤ) (u : P ⟶ K.cycles n) :
    let c := HomologicalComplex.mkHomFromSingle (u ≫ K.iCycles n)
      (by intro i _hi; simp [Category.assoc])
    (singleObjHomologySelfIso (ComplexShape.up ℤ) n P).inv ≫ homologyMap c n =
      u ≫ K.homologyπ n := by
  intro c
  have hc : (singleObjCyclesSelfIso (ComplexShape.up ℤ) n P).inv ≫ cyclesMap c n = u := by
    apply (cancel_mono (K.iCycles n)).mp
    rw [Category.assoc, cyclesMap_i]
    dsimp only [c]
    rw [mkHomFromSingle_f]
    simp only [← Category.assoc, singleObjCyclesSelfIso_inv_iCycles,
      Iso.inv_hom_id, Category.id_comp]
  rw [← singleObjCyclesSelfIso_inv_homologyπ (ComplexShape.up ℤ) n P,
    Category.assoc, homologyπ_naturality, ← Category.assoc, hc]

open HomologicalComplex in
/-- The homology map of a morphism `P[-n] ⟶ K` from a single complex, induced by a map `u` into
the cycles, is `u` followed by the projection of the cycles onto homology. -/
public theorem singleObjHomologySelfIso_inv_comp_homologyMap_mkHomFromSingle
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (P : C) (n : ℤ) (u : P ⟶ K.cycles n) :
    let c := HomologicalComplex.mkHomFromSingle (u ≫ K.iCycles n)
      (by intro i _hi; simp [Category.assoc])
    (singleObjHomologySelfIso (ComplexShape.up ℤ) n P).inv ≫ homologyMap c n =
      u ≫ K.homologyπ n :=
  homologyMap_mkHomFromSingle_cycles K P n u

open HomologicalComplex in
set_option backward.isDefEq.respectTransparency false in
/-- Shifted copies of the ring detect zero objects in the unbounded derived category. -/
private theorem isZero_of_single_hom_eq_zero
    (A : Type u) [Ring A] (E : DerivedCategory (ModuleCat.{u} A))
    (h : ∀ n : ℤ, ∀ g : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat A) n).obj (ModuleCat.of A A)) ⟶ E,
      g = 0) : IsZero E := by
  let K := DerivedCategory.Q.objPreimage E
  let e := DerivedCategory.Q.objObjPreimageIso E
  have hz (n : ℤ) : IsZero (K.homology n) := by
    have hm (a : ModuleCat.of A A ⟶ K.homology n) : a = 0 := by
      let b := Projective.factorThru a (K.homologyπ n)
      let g := HomologicalComplex.mkHomFromSingle (b ≫ K.iCycles n)
        (by intro i _hi; simp [Category.assoc])
      have hg : DerivedCategory.Q.map g = 0 := by
        apply (cancel_mono e.hom).mp
        simpa using h n (DerivedCategory.Q.map g ≫ e.hom)
      have hh : homologyMap g n = 0 := by
        have hh := DerivedCategory.homologyFunctorFactors_hom_naturality g n
        rw [hg, Functor.map_zero, zero_comp] at hh
        exact (cancel_epi ((DerivedCategory.homologyFunctorFactors (ModuleCat A) n).hom.app _)).mp
          (by simpa using hh.symm)
      have hb := homologyMap_mkHomFromSingle_cycles K (ModuleCat.of A A) n b
      change (singleObjHomologySelfIso (ComplexShape.up ℤ) n (ModuleCat.of A A)).inv ≫
        homologyMap g n = b ≫ K.homologyπ n at hb
      rw [hh, comp_zero] at hb
      dsimp only [b] at hb
      rw [Projective.factorThru_comp] at hb
      exact hb.symm
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro x
    have hx := ConcreteCategory.congr_hom
      (hm (ModuleCat.ofHom (LinearMap.toSpanSingleton A (K.homology n) x))) 1
    change (1 : A) • x = 0 at hx
    simpa only [one_smul] using hx
  have hq (n : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) n).obj
      (DerivedCategory.Q.obj K)) :=
    (hz n).of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat A) n).app K)
  have : IsIso (0 : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj K) := by
    apply (DerivedCategory.isIso_iff _ _).mpr
    intro n
    rw [Functor.map_zero]
    exact (hq n).isIso (hq n) _
  have hi : 𝟙 (DerivedCategory.Q.obj K) = 0 := by
    simpa only [zero_comp] using
      (IsIso.hom_inv_id (0 : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj K)).symm
  exact ((IsZero.iff_id_eq_zero _).mpr hi).of_iso e.symm

set_option backward.isDefEq.respectTransparency false in
/-- A morphism is invertible if all shifted-ring Hom tests are bijections. -/
private theorem isIso_of_bijective_single_tests
    (A : Type u) [Ring A]
    {X Y : DerivedCategory (ModuleCat.{u} A)} (f : X ⟶ Y)
    (h : ∀ n : ℤ, Function.Bijective (fun a : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat A) n).obj (ModuleCat.of A A)) ⟶ X =>
      a ≫ f)) : IsIso f := by
  have hi (n : ℤ) (a : DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat A) n).obj (ModuleCat.of A A)) ⟶ X⟦(1 : ℤ)⟧)
      (ha : a ≫ f⟦(1 : ℤ)⟧' = 0) : a = 0 := by
    let S := (DerivedCategory.singleFunctor (ModuleCat A) n).obj (ModuleCat.of A A)
    let adj := (shiftEquiv' (DerivedCategory (ModuleCat.{u} A)) (-1) 1 (by omega)).toAdjunction
    have : (shiftEquiv' (DerivedCategory (ModuleCat.{u} A)) (-1) 1 (by omega)).functor.Additive :=
      inferInstanceAs ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-1 : ℤ)).Additive)
    let e := ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso (-1) (n + 1) n
      (by omega)).app (ModuleCat.of A A)
    have hh : e.inv ≫ (adj.homEquiv S X).symm a = 0 := by
      apply (h (n + 1)).injective
      change (e.inv ≫ (adj.homEquiv S X).symm a) ≫ f = 0 ≫ f
      rw [Category.assoc, ← adj.homEquiv_naturality_right_symm]
      change e.inv ≫ (adj.homEquiv S Y).symm (a ≫ f⟦(1 : ℤ)⟧') = 0 ≫ f
      rw [ha]
      simp only [adj.homAddEquiv_symm_zero, comp_zero, zero_comp]
    have hh' : (adj.homEquiv S X).symm a = 0 := by
      apply (cancel_epi e.inv).mp
      simpa using hh
    apply (adj.homEquiv S X).symm.injective
    simpa only [adj.homAddEquiv_symm_zero] using hh'
  obtain ⟨Z, g, k, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  let T := Pretriangulated.Triangle.mk f g k
  apply (Pretriangulated.Triangle.isZero₃_iff_isIso₁ T hT).mp
  apply isZero_of_single_hom_eq_zero A Z
  intro n a
  have hak : a ≫ k = 0 := hi n (a ≫ k) (by
    rw [Category.assoc]
    exact (congrArg (a ≫ ·) (Pretriangulated.comp_distTriang_mor_zero₃₁ T hT)).trans
      comp_zero)
  obtain ⟨b, hb⟩ := Pretriangulated.Triangle.coyoneda_exact₃ T hT a hak
  obtain ⟨c, hc⟩ := (h n).surjective b
  rw [hb, ← hc, Category.assoc]
  exact (congrArg (c ≫ ·) (Pretriangulated.comp_distTriang_mor_zero₁₂ T hT)).trans
    comp_zero

/-- The completion unit is invertible on every derived-complete object. -/
private theorem isIso_cechCompletionUnit_of_complete
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (E : DerivedCategory (ModuleCat.{u} A))
    (hE : IsDerivedComplete (Ideal.span (Set.range f)) E) :
    IsIso ((cechCompletionUnit A f).app E) :=
  isIso_of_bijective_single_tests A _
    (bijective_postcomp_cechCompletionUnit_single A f E hE)

section
variable {R : Type u} [CommRing R]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]
  (d : StacksDraft.DerivedHom.DerivedHomData R) (c : StacksDraft.DerivedHom.DerivedHomCurrying d)

/-- The augmentation unit factors through internal Hom from the tensor unit. -/
private theorem homUnitOfAugmentation_factor
    (C : DerivedCategory (ModuleCat.{u} R))
    (ε : C ⟶ DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
    (X : DerivedCategory (ModuleCat.{u} R)) :
    (homUnitOfAugmentation d c C ε).app X =
      (homUnitOfAugmentation d c _ (𝟙 _)).app X ≫
        d.hom.map (show (Opposite.op (DerivedCategory.Q.obj
          (𝟙_ (CochainComplex (ModuleCat R) ℤ))), X) ⟶ (Opposite.op C, X) from
        (ε.op, 𝟙 X)) := by
  apply (d.homEquiv X C X).injective
  rw [d.homEquiv_dinaturality, homEquiv_homUnitOfAugmentation_app,
    homEquiv_homUnitOfAugmentation_app, d.tensor_map_id, Category.id_comp]

/-- The identity augmentation induces the tensor-unit isomorphism under adjunction. -/
private theorem isIso_homUnitOfAugmentation_id
    (X : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((homUnitOfAugmentation d c _ (𝟙 _)).app X) := by
  apply isIso_of_yoneda_map_bijective
  intro Y
  apply bijective_postcomp_homUnitOfAugmentation d c
  simp only [d.tensor_map_id, Category.id_comp]
  exact bijective_precomp_hom (tensorUnitRight d c Y)

/-- If the augmentation unit is invertible at an internal Hom object, internal Hom
also inverts the unit at the original object. -/
private theorem isIso_map_homUnitOfAugmentation
    (C X : DerivedCategory (ModuleCat.{u} R))
    (ε : C ⟶ DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ)))
    (h : IsIso ((homUnitOfAugmentation d c C ε).app (d.hom.obj (Opposite.op C, X)))) :
    IsIso (d.hom.map (show (Opposite.op C, X) ⟶
      (Opposite.op C, d.hom.obj (Opposite.op C, X)) from
      (𝟙 (Opposite.op C), (homUnitOfAugmentation d c C ε).app X))) := by
  let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ))
  let H := d.hom.obj (Opposite.op C, X)
  have hν (Y : DerivedCategory (ModuleCat.{u} R)) :
      IsIso ((homUnitOfAugmentation d c U (𝟙 U)).app Y) :=
    isIso_homUnitOfAugmentation_id d c Y
  have hε : IsIso (d.hom.map (show (Opposite.op U, H) ⟶ (Opposite.op C, H) from
      (ε.op, 𝟙 H))) := by
    have hi : IsIso ((homUnitOfAugmentation d c U (𝟙 U)).app H ≫
        d.hom.map (show (Opposite.op U, H) ⟶ (Opposite.op C, H) from
          (ε.op, 𝟙 H))) := by
      rw [← homUnitOfAugmentation_factor]
      infer_instance
    exact IsIso.of_isIso_comp_left ((homUnitOfAugmentation d c U (𝟙 U)).app H) _
  have hl : IsIso (d.hom.map (show (Opposite.op (d.tensor.obj (U, C)), X) ⟶
      (Opposite.op (d.tensor.obj (C, C)), X) from
      ((d.tensor.map (ε, 𝟙 C)).op, 𝟙 X))) := by
    have hi : IsIso ((c.iso U C X).hom ≫
        d.hom.map (show (Opposite.op (d.tensor.obj (U, C)), X) ⟶
          (Opposite.op (d.tensor.obj (C, C)), X) from
          ((d.tensor.map (ε, 𝟙 C)).op, 𝟙 X))) := by
      rw [← c.naturality_left ε]
      infer_instance
    exact IsIso.of_isIso_comp_left (c.iso U C X).hom _
  have hr : IsIso (d.hom.map (show (Opposite.op (d.tensor.obj (C, U)), X) ⟶
      (Opposite.op (d.tensor.obj (C, C)), X) from
      ((d.tensor.map (𝟙 C, ε)).op, 𝟙 X))) := by
    have he : d.tensor.map (show (C, C) ⟶ (C, U) from (𝟙 C, ε)) =
        (d.tensorSwap C C).inv ≫ d.tensor.map (show (C, C) ⟶ (U, C) from (ε, 𝟙 C)) ≫
          (d.tensorSwap U C).hom := by
      rw [d.tensorSwap_naturality, Iso.inv_hom_id_assoc]
    rw [he]
    have he' : (show (Opposite.op (d.tensor.obj (C, U)), X) ⟶
        (Opposite.op (d.tensor.obj (C, C)), X) from
        (((d.tensorSwap C C).inv ≫ d.tensor.map (ε, 𝟙 C) ≫
          (d.tensorSwap U C).hom).op, 𝟙 X)) =
      (show (Opposite.op (d.tensor.obj (C, U)), X) ⟶
        (Opposite.op (d.tensor.obj (U, C)), X) from ((d.tensorSwap U C).hom.op, 𝟙 X)) ≫
      (show (Opposite.op (d.tensor.obj (U, C)), X) ⟶
        (Opposite.op (d.tensor.obj (C, C)), X) from ((d.tensor.map (ε, 𝟙 C)).op, 𝟙 X)) ≫
      (show (Opposite.op (d.tensor.obj (C, C)), X) ⟶
        (Opposite.op (d.tensor.obj (C, C)), X) from ((d.tensorSwap C C).inv.op, 𝟙 X)) := by
      apply Prod.ext <;> simp [Category.assoc]
    rw [he', Functor.map_comp, Functor.map_comp]
    have : IsIso (show (Opposite.op (d.tensor.obj (C, U)), X) ⟶
        (Opposite.op (d.tensor.obj (U, C)), X) from
        ((d.tensorSwap U C).hom.op, 𝟙 X)) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    have : IsIso (show (Opposite.op (d.tensor.obj (C, C)), X) ⟶
        (Opposite.op (d.tensor.obj (C, C)), X) from
        ((d.tensorSwap C C).inv.op, 𝟙 X)) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    infer_instance
  have hm : IsIso (d.hom.map (show (Opposite.op C, d.hom.obj (Opposite.op U, X)) ⟶
      (Opposite.op C, H) from
      (𝟙 (Opposite.op C), d.hom.map (show (Opposite.op U, X) ⟶ (Opposite.op C, X) from
        (ε.op, 𝟙 X))))) := by
    have hi : IsIso (d.hom.map (show (Opposite.op C, d.hom.obj (Opposite.op U, X)) ⟶
        (Opposite.op C, H) from
        (𝟙 (Opposite.op C), d.hom.map (show (Opposite.op U, X) ⟶ (Opposite.op C, X) from
          (ε.op, 𝟙 X)))) ≫ (c.iso C C X).hom) := by
      rw [c.naturality_middle ε]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (c.iso C C X).hom
  rw [homUnitOfAugmentation_factor]
  have he : (show (Opposite.op C, X) ⟶ (Opposite.op C, H) from
      (𝟙 (Opposite.op C), (homUnitOfAugmentation d c U (𝟙 U)).app X ≫
        d.hom.map (show (Opposite.op U, X) ⟶ (Opposite.op C, X) from (ε.op, 𝟙 X)))) =
    (show (Opposite.op C, X) ⟶ (Opposite.op C, d.hom.obj (Opposite.op U, X)) from
      (𝟙 (Opposite.op C), (homUnitOfAugmentation d c U (𝟙 U)).app X)) ≫
    (show (Opposite.op C, d.hom.obj (Opposite.op U, X)) ⟶ (Opposite.op C, H) from
      (𝟙 (Opposite.op C), d.hom.map (show (Opposite.op U, X) ⟶ (Opposite.op C, X) from
        (ε.op, 𝟙 X)))) := by
    apply Prod.ext <;> simp
  rw [he, Functor.map_comp]
  have := hν X
  have : IsIso (show (Opposite.op C, X) ⟶
      (Opposite.op C, d.hom.obj (Opposite.op U, X)) from
      (𝟙 (Opposite.op C), (homUnitOfAugmentation d c U (𝟙 U)).app X)) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  infer_instance

end

/-- Čech completion is the reflection into the derived-complete objects. -/
private theorem cechCompletion_isReflection_aux (A : Type u) [CommRing A] {r : ℕ}
    (f : Fin r → A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    ∃ η : Functor.id (DerivedCategory (ModuleCat.{u} A)) ⟶ cechCompletionFunctor A f,
      (∀ K, IsDerivedComplete (Ideal.span (Set.range f))
        ((cechCompletionFunctor A f).obj K)) ∧
      ∀ (K E : DerivedCategory (ModuleCat.{u} A)),
        IsDerivedComplete (Ideal.span (Set.range f)) E →
          Function.Bijective
            (fun g : (cechCompletionFunctor A f).obj K ⟶ E ↦ η.app K ≫ g) := by
  refine ⟨cechCompletionUnit A f, cechCompletion_isDerivedComplete A f, ?_⟩
  intro K E hE
  have := isIso_cechCompletionUnit_of_complete A f E hE
  have hK := isIso_cechCompletionUnit_of_complete A f ((cechCompletionFunctor A f).obj K)
    (cechCompletion_isDerivedComplete A f K)
  have : IsIso ((cechCompletionFunctor A f).map ((cechCompletionUnit A f).app K)) :=
    isIso_map_homUnitOfAugmentation (StacksDraft.DerivedHom.derivedHomAdjunction (R := A))
      StacksDraft.DerivedHom.derivedHomCurrying (extendedCechObject A f) K
      (DerivedCategory.Q.map (cechAugmentation f (ModuleCat.of A A))) hK
  exact bijective_precomp_unit (cechCompletionFunctor A f) (cechCompletionUnit A f) K E

end CechCompletion

end

section


open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

@[expose] public noncomputable section

namespace CechCompletion

/-- Derived completion with respect to the ideal generated by a finite family
`f` is computed functorially as derived Hom from its extended alternating Čech complex. It is
derived complete, and the natural map from an object to its completion induces a bijection on
morphisms into every derived-complete object. -/
@[stacks 091V]
public theorem cechCompletion_isReflection (A : Type u) [CommRing A] {r : ℕ}
    (f : Fin r → A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    ∃ η : Functor.id (DerivedCategory (ModuleCat.{u} A)) ⟶ cechCompletionFunctor A f,
      (∀ K, IsDerivedComplete (Ideal.span (Set.range f))
        ((cechCompletionFunctor A f).obj K)) ∧
      ∀ (K E : DerivedCategory (ModuleCat.{u} A)),
        IsDerivedComplete (Ideal.span (Set.range f)) E →
          Function.Bijective
            (fun g : (cechCompletionFunctor A f).obj K ⟶ E ↦ η.app K ≫ g) :=
  cechCompletion_isReflection_aux A f

end CechCompletion

end

end
