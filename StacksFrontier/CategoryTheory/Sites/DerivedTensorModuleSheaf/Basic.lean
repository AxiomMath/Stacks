module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Algebra.Homology.KoszulSymmetric
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Flat
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedBifunctor
public import StacksFrontier.Homology.KFlat.BifunctorOneSided

/-!
# The derived tensor product of sheaves of modules over a ring

Let `(C, J)` be a site and `Λ` a commutative ring. The derived category `D(C, Λ)` of sheaves of
`Λ`-modules on `C` carries the derived tensor product `K ⊗_Λ^L L`: the tensor product of
`CategoryTheory.Sheaf.monoidalCategory`, derived by means of K-flat resolutions (Stacks 06YU).
It makes `D(C, Λ)` a symmetric monoidal category. This file constructs it, identifies it on K-flat
complexes with the total tensor complex, and proves that it is exact in each variable and right
t-exact: if `K` lies in degrees `≤ a` and `L` in degrees `≤ b` then `K ⊗_Λ^L L` lies in degrees
`≤ a + b`.

## Main definitions

* `Stacks.ModuleSheaf.derivedMonoidal`: the monoidal structure on `D(C, Λ)` given by the derived
  tensor product (not an instance).
* `Stacks.ModuleSheaf.derivedSymmetric`: its symmetry, induced by the Koszul symmetry of
  complexes.
* `Stacks.ModuleSheaf.derivedTensorIso`: on two K-flat complexes the derived tensor product is
  the total tensor complex.
* `Stacks.ModuleSheaf.derivedTensorIsoOfKFlat`: a K-flat right factor computes the derived
  tensor product against an arbitrary left factor.

## Main results

* `Stacks.ModuleSheaf.exists_commShift_isTriangulated_tensorLeft`,
  `Stacks.ModuleSheaf.exists_commShift_isTriangulated_tensorRight`: the derived tensor product
  is an exact functor in each variable.
* `Stacks.ModuleSheaf.isLE_tensor`: right t-exactness.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor

universe t w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}]

/-- **The K-flat resolutions of Stacks 06YS for sheaves of `Λ`-modules, as an instance**:
`Stacks.ModuleSheaf.exists_kFlat_quasiIso` in the form the localization instance
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` takes, so that the
K-flat objects of the homotopy category localize to `D(C, Λ)`. -/
instance kFlatLocalizer_hasLeftResolutions :
    (kFlatLocalizer (curriedTensor (Sheaf J (ModuleCat.{w} Λ)))).HasLeftResolutions :=
  CochainComplex.KFlatBifunctor.kFlatLocalizer_hasLeftResolutions _
    (exists_kFlat_quasiIso (J := J) (Λ := Λ))

/-- **The left K-flat resolutions for sheaves of `Λ`-modules, as an instance**: the K-flat
resolutions are left K-flat by the Koszul braiding of complexes,
`CochainComplex.KFlatMonoidal.exists_kFlatLeft_quasiIso`, and this is the form the localization
instance `CochainComplex.KFlatBifunctor.kFlatQLeft_isLocalization_of_hasLeftResolutions` takes,
so that the left K-flat objects of the homotopy category localize to `D(C, Λ)`. -/
instance kFlatLocalizerLeft_hasLeftResolutions :
    (kFlatLocalizerLeft (curriedTensor (Sheaf J (ModuleCat.{w} Λ)))).HasLeftResolutions :=
  CochainComplex.KFlatBifunctor.kFlatLocalizerLeft_hasLeftResolutions _
    (CochainComplex.KFlatMonoidal.exists_kFlatLeft_quasiIso _
      (exists_kFlat_quasiIso (J := J) (Λ := Λ)))

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]

/-- **The derived tensor product of sheaves of `Λ`-modules**, as a monoidal structure on the
derived category `D(C, Λ)`. -/
@[instance_reducible]
def derivedMonoidal : MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :=
  CochainComplex.KFlatMonoidal.derivedMonoidal _ (exists_kFlat_quasiIso (J := J) (Λ := Λ))

attribute [local instance] derivedMonoidal

variable {J Λ}

/-- **On K-flat complexes the derived tensor product is the total tensor complex.** -/
def derivedTensorIso {K L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hK : KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) K)
    (hL : KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) L) :
    DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj (K ⊗ L) :=
  CochainComplex.KFlatMonoidal.derivedTensorIso _ (exists_kFlat_quasiIso (J := J) (Λ := Λ)) hK hL

variable (J Λ)

/-- The tensor product of `derivedMonoidal` is the derived bifunctor of the tensor product
descended along the two K-flat localizations. -/
def curriedTensorIsoDerivedBifunctor :
    curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) ≅
      derivedBifunctor (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) :=
  CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso _ (exists_kFlat_quasiIso (J := J) (Λ := Λ))

/-- **The derived tensor product of sheaves of `Λ`-modules is symmetric**, the symmetry being
induced by the Koszul symmetry of complexes, `CochainComplex.symmetricCategory`. -/
@[instance_reducible]
def derivedSymmetric : SymmetricCategory (DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :=
  letI := CochainComplex.symmetricCategory (Sheaf J (ModuleCat.{w} Λ))
  CochainComplex.KFlatMonoidal.derivedSymmetric _ (exists_kFlat_quasiIso (J := J) (Λ := Λ))

variable {J Λ} in
/-- **A K-flat right factor computes the derived tensor product** against an arbitrary left
factor. -/
def derivedTensorIsoOfKFlat (N : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P) :
    DerivedCategory.Q.obj N ⊗ DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (N ⊗ P) :=
  ((curriedTensorIsoDerivedBifunctor J Λ).app _).app _ ≪≫ comparisonRight _ N P hP

/-- Exactness transfers along a natural isomorphism of endofunctors of `D(C, Λ)`. -/
private theorem exists_commShift_isTriangulated_of_iso
    {F G : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{w} Λ))}
    (h : ∃ s : F.CommShift ℤ, letI := s; F.IsTriangulated) (e : F ≅ G) :
    ∃ s : G.CommShift ℤ, letI := s; G.IsTriangulated := by
  obtain ⟨s, hs⟩ := h
  let _ := Functor.CommShift.ofIso e ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  exact ⟨_, Functor.isTriangulated_of_iso e⟩

/-- **The derived tensor product is exact in its second variable**: tensoring on the left with a
fixed object is a triangulated functor. -/
theorem exists_commShift_isTriangulated_tensorLeft
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    ∃ s : (tensorLeft K).CommShift ℤ, letI := s; (tensorLeft K).IsTriangulated := by
  exact exists_commShift_isTriangulated_of_iso J Λ
    (derivedBifunctor_exact_right (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) K)
    ((curriedTensorIsoDerivedBifunctor J Λ).app K).symm

/-- **The derived tensor product is exact in its first variable**: tensoring on the right with a
fixed object is a triangulated functor. -/
theorem exists_commShift_isTriangulated_tensorRight
    (L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    ∃ s : (tensorRight L).CommShift ℤ, letI := s; (tensorRight L).IsTriangulated := by
  exact exists_commShift_isTriangulated_of_iso J Λ
    (derivedBifunctor_exact_left (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) L)
    (NatIso.ofComponents (fun K => ((curriedTensorIsoDerivedBifunctor J Λ).app K).app L)
      (fun f => NatTrans.congr_app ((curriedTensorIsoDerivedBifunctor J Λ).hom.naturality f)
        L)).symm

variable {J Λ}

/-- An object of `D(C, Λ)` with cohomology vanishing above `a` is represented by a K-flat complex
of sheafified presheaves of free modules vanishing above `a`. -/
theorem exists_kFlat_isStrictlyLE_representative (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
    (a : ℤ) [K.IsLE a] :
    ∃ F : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ,
      (∀ n, sheafifiedFree J Λ (F.X n)) ∧ F.IsStrictlyLE a ∧
        Nonempty (DerivedCategory.Q.obj F ≅ K) := by
  let P := DerivedCategory.Q.objPreimage K
  let eP : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hPLE : P.IsLE a :=
    (DerivedCategory.isLE_Q_obj_iff P a).1 (DerivedCategory.TStructure.t.isLE_of_iso eP.symm a)
  obtain ⟨F, f, hf, hF, hFLE⟩ := exists_quasiIso_sheafifiedFree_isStrictlyLE P a
  have : IsIso (DerivedCategory.Q.map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  exact ⟨F, hF, hFLE, ⟨asIso (DerivedCategory.Q.map f) ≪≫ eP⟩⟩

omit [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))] in
/-- The total tensor complex of two complexes vanishing above `a` and above `b` vanishes above
`a + b`. -/
theorem isStrictlyLE_tensor (P Q : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b] : (P ⊗ Q).IsStrictlyLE (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  refine (IsZero.iff_id_eq_zero _).mpr (HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_)
  refine IsZero.eq_of_src ?_ _ _
  by_cases hp : a < p
  · exact (tensorRight (Q.X q)).map_isZero (P.isZero_of_isStrictlyLE a p hp)
  · exact (tensorLeft (P.X p)).map_isZero (Q.isZero_of_isStrictlyLE b q (by dsimp at hpq; lia))

/-- **The derived tensor product is right t-exact**: if `K` lies in degrees `≤ a` and `L` in
degrees `≤ b`, then `K ⊗_Λ^L L` lies in degrees `≤ a + b`. -/
theorem isLE_tensor (K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (a b : ℤ)
    [K.IsLE a] [L.IsLE b] : (K ⊗ L).IsLE (a + b) := by
  obtain ⟨F, hF, hFLE, ⟨eF⟩⟩ := exists_kFlat_isStrictlyLE_representative K a
  obtain ⟨G, hG, hGLE, ⟨eG⟩⟩ := exists_kFlat_isStrictlyLE_representative L b
  have := isStrictlyLE_tensor F G a b
  have : (DerivedCategory.Q.obj (F ⊗ G)).IsLE (a + b) :=
    (DerivedCategory.isLE_Q_obj_iff _ _).2 inferInstance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((derivedTensorIso (kFlat_of_isStrictlyLE F a hF) (kFlat_of_isStrictlyLE G b hG)).symm ≪≫
      (eF ⊗ᵢ eG)) (a + b)

end Stacks.ModuleSheaf
