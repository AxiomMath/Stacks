module

public import StacksFrontier.RingTheory.Dualizing.Complexes.InvertibleImage.CoherentObjects

/-!
# The image of a residue field under a linear autoequivalence

Let `A` be a Noetherian commutative ring, `m` a maximal ideal with residue field `κ`, and `F` an
`A`-linear autoequivalence of `D^b_{Coh}(A)`. This file shows that `F(κ[0])` is a shift of
`κ[0]` once it has no nonzero morphism to its negative shifts, proves that `κ` placed in any
degree is a brick killed by `m`, and relates the self-extensions `κ ⟶ κ⟦1⟧` to the linear forms
on `m` with values in `κ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

variable {A : Type u} [CommRing A]

/-- A nonzero object of `ModuleCat` has a nontrivial underlying module. -/
private theorem nontrivial_of_not_isZero_moduleCat {M : ModuleCat.{u} A} (h : ¬ IsZero M) :
    Nontrivial M :=
  not_subsingleton_iff_nontrivial.mp fun hsub => h (ModuleCat.isZero_iff_subsingleton.mpr hsub)

/-- The linear equivalence between `A ⧸ m` and the residue field of a maximal ideal `m`. -/
private noncomputable def quotientLinearEquivResidueField (m : Ideal A) [m.IsMaximal] :
    (A ⧸ m) ≃ₗ[A] m.ResidueField :=
  LinearEquiv.ofBijective ((Algebra.linearMap (A ⧸ m) m.ResidueField).restrictScalars A)
    m.bijective_algebraMap_quotient_residueField

/-- The image of a residue field is nonzero. -/
public theorem residueField_image_not_isZero [IsNoetherianRing A]
    (F : BoundedCoherentDerivedCategory.{u, u} A ⥤ BoundedCoherentDerivedCategory.{u, u} A)
    [F.IsEquivalence] [F.Linear A] [F.Additive]
    (m : Ideal A) [m.IsMaximal] :
    ¬ IsZero (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj := by
  let E : ModuleCat.{u} A := ModuleCat.of A m.ResidueField
  let X := finiteModuleObject A E
  let Y := F.obj X
  let K := Y.obj
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A)
  let _ : IsSimpleModule A E := isSimpleModule_residueField m
  have hidE : (𝟙 E : E ⟶ E) ≠ 0 := CategoryTheory.id_nonzero E
  have hidX : (𝟙 X : X ⟶ X) ≠ 0 := by
    intro hz
    apply hidE
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun Z => (∀ i : ℤ, Module.Finite A ((H i).obj Z)) ∧
        (DerivedCategory.TStructure.t).bounded Z
    let ι := ObjectProperty.ι P
    have hz' := congrArg (fun f : X ⟶ X => ι.map f) hz
    have hred : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (𝟙 E) =
        ι.map (0 : X ⟶ X) := by
      simpa [X, finiteModuleObject, ringObject, P, ι, Functor.map_id] using hz'
    have hz'' : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (𝟙 E) = 0 := by
      rw [hred, ι.map_zero]
      rfl
    apply (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map_injective
    simpa using hz''
  have hidY : (𝟙 Y : Y ⟶ Y) ≠ 0 := fun hz => hidX (F.map_injective (by simpa using hz))
  exact fun hzero => hidY ((ObjectProperty.ι (fun Z : DerivedCategory (ModuleCat.{u} A) =>
    (∀ i : ℤ, Module.Finite A ((H i).obj Z)) ∧
    (DerivedCategory.TStructure.t).bounded Z)).map_injective (hzero.eq_of_src _ _))

/-- The image of a residue field has cohomology in exactly one degree, provided it has no
nonzero morphism to any of its negative shifts. If two cohomology modules were nonzero, their
common maximal-ideal torsion gives a nonzero map from the higher one to the lower one, and the
truncation bridge turns it into such a morphism. -/
public theorem residueField_image_homology_concentrated [IsNoetherianRing A]
    (F : BoundedCoherentDerivedCategory.{u, u} A ⥤ BoundedCoherentDerivedCategory.{u, u} A)
    [F.IsEquivalence] [F.Linear A] [F.Additive]
    (m : Ideal A) [m.IsMaximal]
    (hneg : ∀ n : ℤ, n < 0 →
      ∀ g : (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj ⟶
        (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj⟦n⟧, g = 0) :
    ∃ a : ℤ, ∀ i : ℤ, i ≠ a → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj) := by
  classical
  let E : ModuleCat.{u} A := ModuleCat.of A m.ResidueField
  let _ : IsSimpleModule A E := isSimpleModule_residueField m
  let X := finiteModuleObject A E
  let Y := F.obj X
  let K := Y.obj
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A)
  have hK : ¬ IsZero K := residueField_image_not_isZero F m
  obtain ⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := Y.property.2
  have : K.IsGE lo := by simpa [K] using hlo
  have : K.IsLE hi := by simpa [K] using hhi
  let S : Set ℤ := {i | i ∈ Set.Icc lo hi ∧ ¬ IsZero ((H i).obj K)}
  have hSfin : S.Finite := (Set.finite_Icc lo hi).subset (fun i hiS => hiS.1)
  obtain ⟨a, haI, ha⟩ := exists_nonzero_homology_of_bounded_nonzero K lo hi hK
  let s := hSfin.toFinset
  have hsne : s.Nonempty := ⟨a, (Set.Finite.mem_toFinset hSfin).2 ⟨haI, ha⟩⟩
  let l := s.min' hsne
  let r := s.max' hsne
  have hlS : l ∈ S := (Set.Finite.mem_toFinset hSfin).1 (Finset.min'_mem s hsne)
  have hrS : r ∈ S := (Set.Finite.mem_toFinset hSfin).1 (Finset.max'_mem s hsne)
  have hl_le (i : ℤ) (hi : i ∈ S) : l ≤ i :=
    Finset.min'_le s i ((Set.Finite.mem_toFinset hSfin).2 hi)
  have le_hr (i : ℤ) (hi : i ∈ S) : i ≤ r :=
    Finset.le_max' s i ((Set.Finite.mem_toFinset hSfin).2 hi)
  have hmemS (i : ℤ) (h : ¬ IsZero ((H i).obj K)) : i ∈ S := by
    refine ⟨⟨?_, ?_⟩, h⟩
    · by_contra hlt
      exact h (DerivedCategory.isZero_of_isGE K lo i (by omega))
    · by_contra hgt
      exact h (DerivedCategory.isZero_of_isLE K hi i (by omega))
  have htors (i : ℤ) := residueField_image_homology_torsionBySet F m i
  have hpair (l r : ℤ) (hlr : l < r) (hGE : K.IsGE l) (hLE : K.IsLE r)
      (hl : ¬ IsZero ((H l).obj K)) (hr : ¬ IsZero ((H r).obj K)) : False := by
    have hNl := nontrivial_of_not_isZero_moduleCat hl
    have hNr := nontrivial_of_not_isZero_moduleCat hr
    obtain ⟨f, hf⟩ := exists_nonzero_linearMap_of_maximal_ideal_killed m
      (htors r) (htors l) hNr hNl
    obtain ⟨g, hg⟩ := exists_nonzero_negative_shift_hom_of_two_nonzero_homology K l r hlr hf
    exact hg (hneg (l - r) (by omega) g)
  by_cases hlr : l = r
  · refine ⟨l, fun i hia => ?_⟩
    by_contra hnonzero
    have hli := hl_le i (hmemS i hnonzero)
    have hir := le_hr i (hmemS i hnonzero)
    exact hia (by omega)
  · have hlr' : l < r := lt_of_le_of_ne (hl_le r hrS) hlr
    have hGE_l : K.IsGE l := (DerivedCategory.isGE_iff K l).2 (by
      intro i hil
      by_contra hnonzero
      have hli := hl_le i (hmemS i hnonzero)
      omega)
    have hLE_r : K.IsLE r := (DerivedCategory.isLE_iff K r).2 (by
      intro i hir
      by_contra hnonzero
      have hir' := le_hr i (hmemS i hnonzero)
      omega)
    exact (hpair l r hlr' hGE_l hLE_r hlS.2 hrS.2).elim

/-- The image of a residue field is a shift of a nonzero finite module killed by the maximal
ideal, provided it has no nonzero morphism to any of its negative shifts. -/
public theorem residueField_image_iso_single [IsNoetherianRing A]
    (F : BoundedCoherentDerivedCategory.{u, u} A ⥤ BoundedCoherentDerivedCategory.{u, u} A)
    [F.IsEquivalence] [F.Linear A] [F.Additive]
    (m : Ideal A) [m.IsMaximal]
    (hneg : ∀ n : ℤ, n < 0 →
      ∀ g : (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj ⟶
        (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj⟦n⟧, g = 0) :
    ∃ a : ℤ, ∃ M : ModuleCat.{u} A,
      Nonempty ((F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) a).obj M) ∧
      Module.Finite A M ∧ Module.IsTorsionBySet A M m ∧ ¬ IsZero M := by
  obtain ⟨a, ha⟩ := residueField_image_homology_concentrated F m hneg
  let K := (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A)
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_homology_vanish_off K a ha
  let hHom : (H a).obj K ≅ M :=
    (H a).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) a).app M
  let e' : K ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) a).obj ((H a).obj K) :=
    e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) a).mapIso hHom.symm
  exact ⟨a, (H a).obj K, ⟨e'⟩,
    (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).property.1 a,
    residueField_image_homology_torsionBySet F m a, fun hM => (residueField_image_not_isZero F m)
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) a).map_isZero hM).of_iso e')⟩

/-- Once the image of a residue field is concentrated in one degree, its only cohomology module
has no endomorphisms other than zero and isomorphisms. -/
public theorem residueField_image_endomorphism_property [IsNoetherianRing A]
    (F : BoundedCoherentDerivedCategory.{u, u} A ⥤ BoundedCoherentDerivedCategory.{u, u} A)
    [F.IsEquivalence] [F.Linear A] [F.Additive]
    (m : Ideal A) [m.IsMaximal] (a : ℤ) (M : ModuleCat.{u} A) [Module.Finite A M]
    (e : (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) a).obj M) :
    ∀ f : M ⟶ M, f = 0 ∨ IsIso f := by
  let E : ModuleCat.{u} A := ModuleCat.of A m.ResidueField
  let X := finiteModuleObject A E
  let S₀ := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let Sₐ := DerivedCategory.singleFunctor (ModuleCat.{u} A) a
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun K => (∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ∧
      (DerivedCategory.TStructure.t).bounded K
  let ι := ObjectProperty.ι P
  let Fff : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  let _ : IsSimpleModule A E := isSimpleModule_residueField m
  intro f
  by_cases hf : f = 0
  · exact Or.inl hf
  · let g₀ : (F.obj X).obj ⟶ (F.obj X).obj := e.hom ≫ Sₐ.map f ≫ e.inv
    let g : F.obj X ⟶ F.obj X := ObjectProperty.homMk g₀
    have hg : g ≠ 0 := by
      intro hz
      have hz' : g₀ = 0 := by simpa [g] using congrArg (fun q => q.hom) hz
      have hzero : Sₐ.map f = 0 := by
        simpa [g₀, Category.assoc] using congrArg (fun q => e.inv ≫ q ≫ e.hom) hz'
      exact hf (Sₐ.map_injective (by simpa using hzero))
    let g' := Fff.homEquiv.symm g
    have hg' : g' ≠ 0 := by
      intro hz
      apply hg
      have hh : Fff.homEquiv g' = g := Equiv.apply_symm_apply _ _
      rw [← hh, hz]
      simp
    have hgι : ι.map g' ≠ 0 := fun hz => hg' (ι.map_injective (hz.trans (ι.map_zero _ _).symm))
    obtain ⟨q, hq⟩ := S₀.map_surjective (ι.map g')
    have hqne : q ≠ 0 := fun hz => hgι (hq.symm.trans (show S₀.map q = 0 by simp [hz]))
    have hqiso : IsIso q := by
      have : Simple E := (simple_iff_isSimpleModule' E).2 inferInstance
      exact (CategoryTheory.isIso_iff_nonzero q).2 hqne
    have hg'iso : IsIso g' := by
      have hmap : IsIso (ι.map g') := by
        rw [← hq]
        exact Functor.map_isIso S₀ q
      exact (isIso_iff_of_reflects_iso g' ι).mp hmap
    have hgiso : IsIso g := by
      have hh₁ : Fff.homEquiv g' = g := Equiv.apply_symm_apply _ _
      have hh : F.map g' = g := (Fff.homEquiv_apply g').symm.trans hh₁
      rw [← hh]
      infer_instance
    have hg₀iso : IsIso g₀ := Functor.map_isIso ι g
    have hmiddle : IsIso (Sₐ.map f) := by
      have hcomp : IsIso ((e.hom ≫ Sₐ.map f) ≫ e.inv) := by
        simpa [g₀, Category.assoc] using hg₀iso
      have hleft : IsIso (e.hom ≫ Sₐ.map f) :=
        (isIso_comp_right_iff (e.hom ≫ Sₐ.map f) e.inv).mp hcomp
      exact (isIso_comp_left_iff e.hom (Sₐ.map f)).mp hleft
    exact Or.inr (isIso_iff_of_reflects_iso f Sₐ |>.mp hmiddle)

/-- A finite module killed by a maximal ideal whose nonzero endomorphisms are all invertible is
one-dimensional over the residue field. -/
public theorem residueField_image_module_finrank_one
    (m : Ideal A) [m.IsMaximal] (M : ModuleCat.{u} A) [Module.Finite A M]
    (hM : Module.IsTorsionBySet A M m) (hMne : ¬ IsZero M)
    (hEnd : ∀ f : M ⟶ M, f = 0 ∨ IsIso f) :
    letI : Field (A ⧸ m) := Ideal.Quotient.field m
    letI : Module (A ⧸ m) M := hM.module
    Module.finrank (A ⧸ m) M = 1 := by
  let k := A ⧸ m
  let _ : Field k := Ideal.Quotient.field m
  let _ : Module k M := hM.module
  let _ : IsScalarTower A k M := hM.isScalarTower
  let _ : Module.Finite k M := Module.Finite.of_restrictScalars_finite A k M
  have := nontrivial_of_not_isZero_moduleCat hMne
  have hpos : 0 < Module.finrank k M := Module.finrank_pos (R := k) (M := M)
  show Module.finrank k M = 1
  by_contra hdim
  have hdim' : 1 < Module.finrank k M := by omega
  let b := Module.finBasis k M
  let i : Fin (Module.finrank k M) := ⟨0, by omega⟩
  let j : Fin (Module.finrank k M) := ⟨1, by omega⟩
  have hij : i ≠ j := Fin.ne_of_val_ne (by simp [i, j])
  let ℓ : M →ₗ[k] M := (b.coord i).smulRight (b j)
  have hℓi : ℓ (b i) = b j := by
    show b.coord i (b i) • b j = b j
    simp
  have hℓj : ℓ (b j) = 0 := by
    show b.coord i (b j) • b j = 0
    rw [show b.coord i (b j) = 0 by simp [hij], zero_smul]
  let f : M ⟶ M := ModuleCat.ofHom (ℓ.restrictScalars A)
  have hf : f ≠ 0 := by
    intro hz
    apply b.ne_zero j
    simpa [f, hℓi] using congrArg (fun g : M ⟶ M => g.hom (b i)) hz
  rcases hEnd f with hzero | hIso
  · exact (hf hzero).elim
  · have hbij : Function.Bijective f.hom := (ConcreteCategory.isIso_iff_bijective f).mp hIso
    exact b.ne_zero j (hbij.1 (by simp [f, hℓj]))

/-- The preceding endomorphism criterion identifies the module itself with the residue field. -/
public theorem residueField_image_module_equiv_quotient
    (m : Ideal A) [m.IsMaximal] (M : ModuleCat.{u} A) [Module.Finite A M]
    (hM : Module.IsTorsionBySet A M m) (hMne : ¬ IsZero M)
    (hEnd : ∀ f : M ⟶ M, f = 0 ∨ IsIso f) :
    Nonempty ((A ⧸ m) ≃ₗ[A] M) := by
  let k := A ⧸ m
  let _ : Field k := Ideal.Quotient.field m
  let _ : Module k M := hM.module
  let _ : IsScalarTower A k M := hM.isScalarTower
  let _ : Module.Finite k M := Module.Finite.of_restrictScalars_finite A k M
  have hdim : Module.finrank k M = 1 := residueField_image_module_finrank_one m M hM hMne hEnd
  let e : k ≃ₗ[k] M := LinearEquiv.ofFinrankEq k M (by simpa using hdim.symm)
  exact ⟨e.restrictScalars A⟩

/-- The image of a residue field under a linear autoequivalence is a shift of that residue
field, not merely a shift of a finite module supported at the maximal ideal, provided it has
no nonzero morphism to any of its negative shifts. -/
public theorem residueField_image_iso_residueField [IsNoetherianRing A]
    (F : BoundedCoherentDerivedCategory.{u, u} A ⥤ BoundedCoherentDerivedCategory.{u, u} A)
    [F.IsEquivalence] [F.Linear A] [F.Additive]
    (m : Ideal A) [m.IsMaximal]
    (hneg : ∀ n : ℤ, n < 0 →
      ∀ g : (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj ⟶
        (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj⟦n⟧, g = 0) :
    ∃ a : ℤ, Nonempty ((F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) a).obj
        (ModuleCat.of A m.ResidueField)) := by
  obtain ⟨a, M, ⟨e⟩, _, htors, hne⟩ := residueField_image_iso_single F m hneg
  obtain ⟨eM⟩ := residueField_image_module_equiv_quotient m M htors hne
    (residueField_image_endomorphism_property F m a M e)
  exact ⟨a, ⟨e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) a).mapIso
    (eM.symm.trans (quotientLinearEquivResidueField m)).toModuleIso⟩⟩

/-- Maps from the ring to a residue field, both in degree zero, form a one-dimensional vector
space over that residue field. -/
public noncomputable def residueFieldHomFromRingLinearEquiv
    (m : Ideal A) [m.IsMaximal] :
    (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A m.ResidueField))) ≃ₗ[A] m.ResidueField :=
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  (fullyFaithfulHomLinearEquiv (R := A) S
      (Functor.FullyFaithful.ofFullyFaithful S) _ _).symm.trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf A A m.ResidueField))

/-- The inclusion of the bounded coherent subcategory does not change morphisms between
degree-zero modules. -/
public noncomputable def boundedRingToResidueFieldHomLinearEquiv
    (m : Ideal A) [m.IsMaximal] :
    (ringObject A ⟶ finiteModuleObject A (ModuleCat.of A m.ResidueField)) ≃ₗ[A]
      m.ResidueField :=
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun K => (∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ∧
      (DerivedCategory.TStructure.t).bounded K
  let ι := ObjectProperty.ι P
  (fullyFaithfulHomLinearEquiv (R := A) ι (Functor.FullyFaithful.ofFullyFaithful ι)
      (ringObject A) (finiteModuleObject A (ModuleCat.of A m.ResidueField))).trans
    (residueFieldHomFromRingLinearEquiv m)

/-! ### The residue field in every degree, and its images -/

/-- The residue field has no endomorphisms other than zero and isomorphisms. -/
public theorem isBrick_residueField_moduleCat (m : Ideal A) [m.IsMaximal] :
    IsBrick (ModuleCat.of A m.ResidueField) := by
  intro f
  have : Simple (ModuleCat.of A m.ResidueField) :=
    (simple_iff_isSimpleModule' _).2 (isSimpleModule_residueField m)
  exact (em (f = 0)).imp_right (isIso_iff_nonzero f).2

/-- The residue field in any degree is a brick of the derived category. -/
public theorem isBrick_residueObject_obj (m : Ideal A) [m.IsMaximal] (n : ℤ) :
    IsBrick (residueObject m n).obj :=
  (isBrick_residueField_moduleCat m).map (DerivedCategory.singleFunctor (ModuleCat.{u} A) n)

/-- The residue field in any degree is a brick of the bounded coherent derived category. -/
public theorem isBrick_residueObject (m : Ideal A) [m.IsMaximal] (n : ℤ) :
    IsBrick (residueObject m n) :=
  IsBrick.of_map (ObjectProperty.ι _) (isBrick_residueObject_obj m n)

/-- The residue field in any degree is a nonzero object of the derived category. -/
public theorem not_isZero_residueObject_obj (m : Ideal A) [m.IsMaximal] (n : ℤ) :
    ¬ IsZero (residueObject m n).obj := by
  intro h
  have h2 : IsZero (ModuleCat.of A m.ResidueField) :=
    IsZero.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map_isZero h)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) n).app _).symm
  exact not_subsingleton m.ResidueField (ModuleCat.isZero_iff_subsingleton.mp h2)

/-- The residue field in any degree is a nonzero object of the bounded coherent derived
category. -/
public theorem not_isZero_residueObject (m : Ideal A) [m.IsMaximal] (n : ℤ) :
    ¬ IsZero (residueObject m n) :=
  fun h => not_isZero_residueObject_obj m n ((ObjectProperty.ι _).map_isZero h)

/-- The maximal ideal annihilates the residue field in any degree. -/
public theorem residueObject_smul_id_eq_zero (m : Ideal A) [m.IsMaximal] (n : ℤ) (r : A)
    (hr : r ∈ m) :
    r • 𝟙 (residueObject m n) = 0 := by
  have hE : r • (𝟙 (ModuleCat.of A m.ResidueField)) = 0 := by
    ext x
    show r • x = 0
    rw [Algebra.smul_def, Ideal.algebraMap_residueField_eq_zero.mpr hr, zero_mul]
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) n
  have hsingle : r • (𝟙 (S.obj (ModuleCat.of A m.ResidueField))) = 0 := by
    simpa only [Functor.map_smul, Functor.map_zero, S.map_id] using congrArg S.map hE
  exact ObjectProperty.hom_ext _ hsingle

/-- There is no nonzero morphism from the residue field in degree `-1` to the residue field in
degree `0`. -/
public theorem hom_shift_one_residueObject_eq_zero [IsNoetherianRing A] (m : Ideal A) [m.IsMaximal]
    (l : (residueObject m 0)⟦(1 : ℤ)⟧ ⟶ residueObject m 0) : l = 0 := by
  let ι := ObjectProperty.ι (fun K : DerivedCategory (ModuleCat.{u} A) =>
    (∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ∧
      (DerivedCategory.TStructure.t).bounded K)
  let X := residueObject m 0
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let E := ModuleCat.of A m.ResidueField
  apply ι.map_injective
  rw [ι.map_zero]
  let e := (ι.commShiftIso (1 : ℤ)).app X
  have hLE : ((S.obj E)⟦(1 : ℤ)⟧).IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_shift (S.obj E) 0 1 (-1) (by omega)
  have h0 : e.inv ≫ ι.map l = 0 :=
    DerivedCategory.TStructure.t.zero (e.inv ≫ ι.map l : (S.obj E)⟦(1 : ℤ)⟧ ⟶ S.obj E) (-1) 0
  exact (cancel_epi e.inv).mp (h0.trans comp_zero.symm)

/-- A module killed by a maximal ideal has, for each nonzero element, a linear form to the
residue field that does not vanish on it. -/
public theorem exists_linearMap_residueField_apply_ne_zero (m : Ideal A) [m.IsMaximal]
    {M : Type u} [AddCommGroup M] [Module A M] (hM : Module.IsTorsionBySet A M m) {x : M}
    (hx : x ≠ 0) : ∃ ω : M →ₗ[A] m.ResidueField, ω x ≠ 0 := by
  classical
  let k := A ⧸ m
  let _ : Field k := Ideal.Quotient.field m
  let _ : Module k M := hM.module
  let _ : IsScalarTower A k M := hM.isScalarTower
  obtain ⟨ι, ⟨bM⟩⟩ := Module.Basis.exists_basis k M
  have hrepr : bM.repr x ≠ 0 := fun h => hx (bM.repr.injective (by simpa using h))
  obtain ⟨i, hi⟩ := (Finsupp.support_nonempty_iff).mpr hrepr
  have hcoord : bM.coord i x ≠ 0 := by
    simpa only [bM.coord_apply] using (Finsupp.mem_support_iff.mp hi)
  let κ := (Algebra.linearMap k m.ResidueField).restrictScalars A
  refine ⟨κ ∘ₗ (bM.coord i).restrictScalars A, ?_⟩
  show algebraMap k m.ResidueField (bM.coord i x) ≠ 0
  exact (map_ne_zero_iff _ (algebraMap k m.ResidueField).injective).mpr hcoord

/-- Being killed by an ideal transfers along a linear isomorphism. -/
public theorem isTorsionBySet_of_linearEquiv {I : Ideal A} {M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (hM : Module.IsTorsionBySet A M I) :
    Module.IsTorsionBySet A N I := by
  intro x r
  simpa using congrArg e (@hM (e.symm x) r)

/-- If every linear form on the maximal ideal with values in the residue field vanishes, the
residue field is a projective module: the maximal ideal is then idempotent, hence generated by
an idempotent, and the residue field is a direct summand of the ring. -/
public theorem projective_residueField_of_forall_linearMap_eq_zero [IsNoetherianRing A]
    (m : Ideal A) [m.IsMaximal] (h : ∀ ℓ : m →ₗ[A] m.ResidueField, ℓ = 0) :
    Module.Projective A m.ResidueField := by
  have hsq : m ≤ m ^ 2 := by
    intro y hy
    by_contra hy2
    let x : m := ⟨y, hy⟩
    have hx : m.toCotangent x ≠ 0 := by rwa [Ne, Ideal.toCotangent_eq_zero]
    have htors : Module.IsTorsionBySet A m.Cotangent m := by
      intro c r
      obtain ⟨z, rfl⟩ := m.toCotangent_surjective c
      rw [← map_smul, Ideal.toCotangent_eq_zero]
      show (r : A) * (z : A) ∈ m ^ 2
      rw [pow_two]
      exact Ideal.mul_mem_mul r.2 z.2
    obtain ⟨ω, hω⟩ := exists_linearMap_residueField_apply_ne_zero m htors hx
    exact hω (LinearMap.congr_fun (h (ω ∘ₗ m.toCotangent)) x)
  have hidem : IsIdempotentElem m := by
    apply le_antisymm Ideal.mul_le_right
    simpa [pow_two] using hsq
  obtain ⟨e, he, hme⟩ := (Ideal.isIdempotentElem_iff_of_fg m (IsNoetherian.noetherian m)).mp hidem
  have hem : e ∈ m := by rw [hme]; exact Submodule.mem_span_singleton_self e
  let s₀ : (A ⧸ m) →ₗ[A] A := m.liftQ (LinearMap.mulLeft A (1 - e)) (by
    intro y hy
    rw [hme] at hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    show (1 - e) * (r • e) = 0
    rw [smul_eq_mul, mul_left_comm, sub_mul, one_mul, he.eq, sub_self, mul_zero])
  have hsplit : (m.mkQ).comp s₀ = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext
    show Submodule.Quotient.mk ((1 - e) * 1) = Submodule.Quotient.mk (1 : A)
    rw [Submodule.Quotient.eq, mul_one, sub_sub_cancel_left]
    exact m.neg_mem hem
  have : Module.Projective A (A ⧸ m) := Module.Projective.of_split s₀ m.mkQ hsplit
  exact Module.Projective.of_equiv' (quotientLinearEquivResidueField m)

/-- A nonzero linear form on the maximal ideal with values in the residue field produces a
nonzero morphism from the residue field to its shift by one, that is, a nonzero class in
`Ext^1_A(κ, κ)`: the connecting morphism of `0 → m → A → κ → 0` followed by the form. -/
public theorem exists_ne_zero_hom_residueObject_shift_one [IsNoetherianRing A] (m : Ideal A)
    [m.IsMaximal] (ℓ : m →ₗ[A] m.ResidueField) (hℓ : ℓ ≠ 0) :
    ∃ e : residueObject m 0 ⟶ (residueObject m 0)⟦(1 : ℤ)⟧, e ≠ 0 := by
  let κ := m.ResidueField
  let S₀ : ShortComplex (ModuleCat.{u} A) :=
    ModuleCat.shortComplexOfCompEqZero m.subtype (Algebra.linearMap A κ) (by
      ext y
      exact Ideal.algebraMap_residueField_eq_zero.mpr y.2)
  have hS : S₀.ShortExact := by
    refine ModuleCat.shortComplex_shortExact S₀ ?_ ?_ ?_
    · intro y
      show algebraMap A κ y = 0 ↔ y ∈ Set.range m.subtype
      rw [Ideal.algebraMap_residueField_eq_zero]
      exact ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨z, hz⟩ => hz ▸ z.2⟩
    · exact m.injective_subtype
    · exact m.algebraMap_residueField_surjective
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let δ := hS.singleδ
  let k : (S.obj S₀.X₁)⟦(1 : ℤ)⟧ ⟶ (S.obj (ModuleCat.of A κ))⟦(1 : ℤ)⟧ :=
    (S.map (ModuleCat.ofHom ℓ))⟦(1 : ℤ)⟧'
  let e₀ : S.obj (ModuleCat.of A κ) ⟶ (S.obj (ModuleCat.of A κ))⟦(1 : ℤ)⟧ := δ ≫ k
  have he₀ : e₀ ≠ 0 := by
    intro h0
    have hR := rot_of_distTriang _ hS.singleTriangle_distinguished
    obtain ⟨l, hl⟩ := Triangle.yoneda_exact₃ _ hR k h0
    let l' : (S.obj S₀.X₂)⟦(1 : ℤ)⟧ ⟶ (S.obj (ModuleCat.of A κ))⟦(1 : ℤ)⟧ := l
    have hl₁ : k = (-((S.map S₀.f)⟦(1 : ℤ)⟧')) ≫ l' := hl
    obtain ⟨l₀, hl₀⟩ :=
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map_surjective l'
    have hl' : S.map (ModuleCat.ofHom ℓ) = -(S.map S₀.f ≫ l₀) := by
      apply (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map_injective
      rwa [Functor.map_neg, Functor.map_comp, hl₀, ← Preadditive.neg_comp]
    obtain ⟨q, rfl⟩ := S.map_surjective l₀
    have hq : ModuleCat.ofHom ℓ = -(S₀.f ≫ q) := by
      apply S.map_injective
      rw [hl', Functor.map_neg, Functor.map_comp]
    apply hℓ
    ext y
    have hy := congrArg (fun φ : S₀.X₁ ⟶ ModuleCat.of A κ => φ.hom y) hq
    change ℓ y = -(q.hom ((y : A))) at hy
    rw [hy, show (y : A) = (y : A) • (1 : A) by rw [smul_eq_mul, mul_one], map_smul,
      Algebra.smul_def, Ideal.algebraMap_residueField_eq_zero.mpr y.2, zero_mul, neg_zero]
    rfl
  let ι := ObjectProperty.ι (fun K : DerivedCategory (ModuleCat.{u} A) =>
    (∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ∧
      (DerivedCategory.TStructure.t).bounded K)
  let X := residueObject m 0
  let eX := (ι.commShiftIso (1 : ℤ)).app X
  refine ⟨ObjectProperty.homMk (e₀ ≫ eX.inv), fun h => he₀ ((cancel_mono eX.inv).mp ?_)⟩
  exact (congrArg (fun φ => φ.hom) h : e₀ ≫ eX.inv = 0).trans zero_comp.symm

end Dualizing

end
