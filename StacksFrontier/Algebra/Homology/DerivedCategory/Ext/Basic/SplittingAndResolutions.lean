module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Interval
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.CategoryTheory.Triangulated.Elementary
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.ExtOneAndVanishing

/-!
# Splitting a bounded complex into its cohomologies, and `Ext` via resolutions

## Main results

* `DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_eq_zero`:
  a bounded object of the derived category with no `Ext^p`, `p ≥ 2`, between its cohomologies
  in strictly decreasing degrees is isomorphic to the direct sum of its cohomologies.
* `DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_two_eq_zero`:
  the same conclusion for every bounded object, when `Ext²` vanishes between all pairs of
  objects of `𝒜`.
* `ExtByResolutions.ext_via_injective_resolution_bijective`,
  `ExtByResolutions.ext_via_projective_resolution_bijective`: `Ext` groups computed by an
  injective resolution of the second variable or a projective resolution of the first.

## Implementation notes

The two splitting results are stated for objects of the unbounded derived category satisfying
`DerivedCategory.IsGE a` and `DerivedCategory.IsLE b` rather than inside
`DerivedCategory.Bounded`, which is the same hypothesis and is how Mathlib states the
neighbouring lemmas; accordingly the direct sum of the cohomologies is the finite biproduct over
`Finset.Icc a b`, the derived category of an abelian category having no reason to admit infinite
coproducts. The isomorphism to that biproduct depends on a choice of splitting of each truncation
triangle, so only its existence is asserted.

## References

* [Stacks Project 0EWX](https://stacks.math.columbia.edu/tag/0EWX)
* [Stacks Project 0GM4](https://stacks.math.columbia.edu/tag/0GM4)
-/

@[expose] public section

universe w' w v u

namespace DerivedCategory

/-! ### Splitting a bounded complex into its cohomologies -/

section

open CategoryTheory Limits Pretriangulated Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D]

/-- If every morphism `X' ⟶ Y'` is zero, so is every morphism between objects isomorphic to
`X'` and to `Y'`. -/
private lemma hom_eq_zero_of_iso {X X' Y Y' : D} (eX : X ≅ X') (eY : Y ≅ Y')
    (h : ∀ g : X' ⟶ Y', g = 0) (f : X ⟶ Y) : f = 0 := by
  rw [← cancel_epi eX.inv, ← cancel_mono eY.hom]
  simpa using h (eX.inv ≫ f ≫ eY.hom)

end

section

open CategoryTheory Limits

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
  [HasBinaryBiproducts D]

/-- A finite biproduct is the biproduct of the summands away from one index and the summand
at that index. -/
private noncomputable def biproductIsoBiprodRestrict {J : Type} [Fintype J] [DecidableEq J]
    (F : J → D) (j₀ : J) :
    (⨁ F) ≅ (⨁ Subtype.restrict (fun j => j ≠ j₀) F) ⊞ F j₀ where
  hom := biprod.lift (biproduct.toSubtype F _) (biproduct.π F j₀)
  inv := biprod.desc (biproduct.fromSubtype F _) (biproduct.ι F j₀)
  hom_inv_id := by
    rw [biprod.lift_desc]
    refine biproduct.hom_ext' _ _ fun j => biproduct.hom_ext _ _ fun k => ?_
    by_cases hj : j = j₀ <;> by_cases hk : k = j₀ <;>
      subst_vars <;> simp_all [biproduct.ι_π]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [biproduct.fromSubtype_π, biproduct.ι_toSubtype]

/-- The elements of `Finset.Icc a b` other than `b` are the elements of
`Finset.Icc a (b - 1)`. -/
private def equivIccErase (a b : ℤ) (hab : a ≤ b) :
    ((Finset.Icc a (b - 1) : Finset ℤ)) ≃
      {j : ((Finset.Icc a b : Finset ℤ)) //
        j ≠ ⟨b, by simp only [Finset.mem_Icc]; omega⟩} where
  toFun i :=
    ⟨⟨i.1, by have := Finset.mem_Icc.mp i.2; simp only [Finset.mem_Icc]; omega⟩, by
      have := Finset.mem_Icc.mp i.2
      simp only [ne_eq, Subtype.mk.injEq]
      omega⟩
  invFun j :=
    ⟨j.1.1, by
      have h₁ := Finset.mem_Icc.mp j.1.2
      have h₂ : (j.1 : ℤ) ≠ b := by simpa only [ne_eq, Subtype.ext_iff] using j.2
      simp only [Finset.mem_Icc]
      omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Splitting off the summand of index `b` from a biproduct indexed by `Finset.Icc a b`. -/
private noncomputable def biproductIccIso (F : ℤ → D) (a b : ℤ) (hab : a ≤ b) :
    (⨁ fun i : (Finset.Icc a b : Finset ℤ) => F i.1) ≅
      (⨁ fun i : (Finset.Icc a (b - 1) : Finset ℤ) => F i.1) ⊞ F b :=
  biproductIsoBiprodRestrict _ ⟨b, by simp only [Finset.mem_Icc]; omega⟩ ≪≫
    biprod.mapIso (biproduct.whiskerEquiv
      (g := fun i : (Finset.Icc a (b - 1) : Finset ℤ) => F i.1)
      (equivIccErase a b hab).symm fun _ => Iso.refl _) (Iso.refl _)

omit [HasBinaryBiproducts D] in
/-- A biproduct indexed by an empty `Finset.Icc a b` is a zero object. -/
private lemma isZero_biproductIcc (F : ℤ → D) (a b : ℤ) (hab : b < a) :
    IsZero (⨁ fun i : (Finset.Icc a b : Finset ℤ) => F i.1) := by
  rw [IsZero.iff_id_eq_zero]
  refine biproduct.hom_ext _ _ fun j => ?_
  have := Finset.mem_Icc.mp j.2
  omega

end

section

open CategoryTheory Limits Pretriangulated Triangulated

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If the third object of a distinguished triangle is `≥ b`, the first morphism is an
isomorphism on `H^i` for `i < b`. -/
private lemma isIso_homologyFunctor_map_of_isGE {L K M : DerivedCategory C} (u : L ⟶ K)
    (v : K ⟶ M) (w : M ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u v w ∈ distTriang (DerivedCategory C)) (i b : ℤ) (hi : i < b)
    [M.IsGE b] : IsIso ((homologyFunctor C i).map u) := by
  have h₁ := HomologySequence.mono_homologyMap_mor₁_iff (Triangle.mk u v w) hT (i - 1) i (by omega)
  have h₂ := HomologySequence.epi_homologyMap_mor₁_iff (Triangle.mk u v w) hT i
  dsimp at h₁ h₂
  have : Mono ((homologyFunctor C i).map u) := by
    rw [h₁]
    exact (isZero_of_isGE M b (i - 1) (by omega)).eq_of_src _ _
  have : Epi ((homologyFunctor C i).map u) := by
    rw [h₂]
    exact (isZero_of_isGE M b i hi).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

/-- If the first object of a distinguished triangle is `≤ a`, the second morphism is an
isomorphism on `H^i` for `a < i`. -/
private lemma isIso_homologyFunctor_map_of_isLE {L K M : DerivedCategory C} (u : L ⟶ K)
    (v : K ⟶ M) (w : M ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u v w ∈ distTriang (DerivedCategory C)) (i a : ℤ) (hi : a < i)
    [L.IsLE a] : IsIso ((homologyFunctor C i).map v) := by
  have h₁ := HomologySequence.mono_homologyMap_mor₂_iff (Triangle.mk u v w) hT i
  have h₂ := HomologySequence.epi_homologyMap_mor₂_iff (Triangle.mk u v w) hT i (i + 1) (by omega)
  dsimp at h₁ h₂
  have : Mono ((homologyFunctor C i).map v) := by
    rw [h₁]
    exact (isZero_of_isLE L a i hi).eq_of_src _ _
  have : Epi ((homologyFunctor C i).map v) := by
    rw [h₂]
    exact (isZero_of_isLE L a (i + 1) (by omega)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

/-- The truncation `τ_{< b}K ⟶ K` is an isomorphism on `H^i` for `i < b`. -/
private noncomputable def homologyTruncLTIso (K : DerivedCategory C) (i b : ℤ) (hi : i < b) :
    (homologyFunctor C i).obj ((TStructure.t.truncLT b).obj K) ≅ (homologyFunctor C i).obj K :=
  have := isIso_homologyFunctor_map_of_isGE ((TStructure.t.truncLTι b).app K)
    ((TStructure.t.truncGEπ b).app K) ((TStructure.t.truncGEδLT b).app K)
    (TStructure.t.triangleLTGE_distinguished b K) i b hi
  asIso ((homologyFunctor C i).map ((TStructure.t.truncLTι b).app K))

/-- The truncation `K ⟶ τ_{≥ b}K` is an isomorphism on `H^b`. -/
private noncomputable def homologyTruncGEIso (K : DerivedCategory C) (b : ℤ) :
    (homologyFunctor C b).obj ((TStructure.t.truncGE b).obj K) ≅ (homologyFunctor C b).obj K :=
  have := isIso_homologyFunctor_map_of_isLE ((TStructure.t.truncLTι b).app K)
    ((TStructure.t.truncGEπ b).app K) ((TStructure.t.truncGEδLT b).app K)
    (TStructure.t.triangleLTGE_distinguished b K) b (b - 1) (by omega)
  (asIso ((homologyFunctor C b).map ((TStructure.t.truncGEπ b).app K))).symm

/-- The cohomology of `X[1]` in degree `j` is the cohomology of `X` in degree `1 + j`. -/
private noncomputable def homologyShiftIso (X : DerivedCategory C) (j k : ℤ) (h : 1 + j = k) :
    (homologyFunctor C j).obj (X⟦(1 : ℤ)⟧) ≅ (homologyFunctor C k).obj X :=
  ((homologyFunctor C 0).shiftIso 1 j k h).app X

/-- An object of the derived category which is cohomologically concentrated in degree `j` is
its `j`-th cohomology placed in degree `j`. -/
private lemma nonempty_iso_singleFunctor_obj_homology (Z : DerivedCategory C) (j : ℤ)
    [Z.IsGE j] [Z.IsLE j] :
    Nonempty (Z ≅ (singleFunctor C j).obj ((homologyFunctor C j).obj Z)) := by
  obtain ⟨W, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE Z j
  exact ⟨e ≪≫ (singleFunctor C j).mapIso (((homologyFunctor C j).mapIso e ≪≫
    (singleFunctorCompHomologyFunctorIso (C := C) j).app W).symm)⟩

/-- A distinguished triangle with vanishing connecting morphism is split: this is
[Stacks, Tag 05QT]. -/
private lemma nonempty_iso_biprod_of_mor₃_eq_zero (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (h : T.mor₃ = 0) :
    Nonempty (T.obj₂ ≅ T.obj₁ ⊞ T.obj₃) := by
  have := T.epi₂ hT h
  have := isSplitEpi_of_epi T.mor₂
  have := isIso_biprod_desc_of_distTriang T hT (section_ T.mor₂) (IsSplitEpi.id T.mor₂)
  exact ⟨(asIso (biprod.desc T.mor₁ (section_ T.mor₂))).symm⟩

/-- A morphism into an object concentrated in a single degree vanishes as soon as morphisms
into that degree's cohomology, placed in that degree, vanish. -/
private lemma hom_eq_zero_of_isGE_of_isLE (X Z Z' : DerivedCategory C) (j : ℤ)
    [Z.IsGE j] [Z.IsLE j]
    (e : (homologyFunctor C j).obj Z ≅ (homologyFunctor C j).obj Z')
    (hyp : ∀ g : X ⟶ (singleFunctor C j).obj ((homologyFunctor C j).obj Z'), g = 0)
    (f : X ⟶ Z) : f = 0 :=
  (nonempty_iso_singleFunctor_obj_homology Z j).elim fun e' =>
    hom_eq_zero_of_iso (Iso.refl X) (e' ≪≫ (singleFunctor C j).mapIso e) hyp f

/-- The induction on the amplitude of `Y` behind
`hom_eq_zero_of_forall_hom_singleFunctor_obj_homology_eq_zero`: the case `b ≤ a + n`. -/
private lemma hom_eq_zero_of_forall_hom_singleFunctor_obj_homology_eq_zero_aux
    (X : DerivedCategory C) (n : ℕ) :
    ∀ (a b : ℤ) (Y : DerivedCategory C), b ≤ a + n → ∀ [Y.IsGE a] [Y.IsLE b],
      (∀ (j : ℤ), a ≤ j → j ≤ b →
        ∀ (g : X ⟶ (singleFunctor C j).obj ((homologyFunctor C j).obj Y)), g = 0) →
      ∀ (f : X ⟶ Y), f = 0 := by
  induction n with
  | zero =>
      intro a b Y hb _ _ hyp f
      rcases lt_or_ge b a with hba | hba
      · exact (TStructure.t.isZero Y b a hba).eq_of_tgt _ _
      · have hab : a = b := by omega
        subst hab
        exact hom_eq_zero_of_isGE_of_isLE X Y Y a (Iso.refl _) (hyp a le_rfl le_rfl) f
  | succ n ih =>
      intro a b Y hb _ _ hyp f
      rcases lt_or_ge b a with hba | hba
      · exact (TStructure.t.isZero Y b a hba).eq_of_tgt _ _
      have hv : f ≫ (TStructure.t.truncGEπ b).app Y = 0 :=
        hom_eq_zero_of_isGE_of_isLE X _ Y b (homologyTruncGEIso Y b) (hyp b hba le_rfl) _
      obtain ⟨g, hg⟩ := (Triangle.mk _ _ _).coyoneda_exact₂
        (TStructure.t.triangleLTGE_distinguished b Y) f hv
      have hg0 : g = 0 :=
        ih a (b - 1) ((TStructure.t.truncLT b).obj Y) (by omega)
          (fun j hj hj' g' => hom_eq_zero_of_iso (Iso.refl X)
            ((singleFunctor C j).mapIso (homologyTruncLTIso Y j b (by omega)))
            (hyp j hj (by omega)) g') g
      simpa [hg0] using hg

/-- **The key vanishing.** Let `Y` have cohomology only in `[a, b]`. If every morphism from `X`
to `H^j(Y)` placed in degree `j` vanishes for `a ≤ j ≤ b`, then every morphism `X ⟶ Y`
vanishes. -/
private lemma hom_eq_zero_of_forall_hom_singleFunctor_obj_homology_eq_zero
    (X Y : DerivedCategory C) (a b : ℤ) [Y.IsGE a] [Y.IsLE b]
    (hyp : ∀ (j : ℤ), a ≤ j → j ≤ b →
      ∀ (g : X ⟶ (singleFunctor C j).obj ((homologyFunctor C j).obj Y)), g = 0)
    (f : X ⟶ Y) : f = 0 :=
  hom_eq_zero_of_forall_hom_singleFunctor_obj_homology_eq_zero_aux X (b - a).toNat a b Y
    (by omega) hyp f

/-- **The connecting morphism of the top truncation triangle vanishes.** Let `K` have
cohomology only in `[a, b]` and suppose there is no nonzero morphism
`H^i(K)[-i] ⟶ H^j(K)[-k]` when `k + 1 = j < i`. Then the connecting morphism
`τ_{≥ b}K ⟶ (τ_{< b}K)[1]` is zero: the object `(τ_{< b}K)[1]` has cohomology only in
`[a - 1, b - 2]`, its cohomology in degree `j` is `H^{j + 1}(K)`, and `τ_{≥ b}K` is
`H^b(K)[-b]`, so each group to be killed is one of those assumed to vanish. -/
private lemma truncGEδLT_app_eq_zero (K : DerivedCategory C) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hyp : ∀ (i j k : ℤ), j < i → k + 1 = j →
      ∀ f : (singleFunctor C i).obj ((homologyFunctor C i).obj K) ⟶
        (singleFunctor C k).obj ((homologyFunctor C j).obj K), f = 0) :
    (TStructure.t.truncGEδLT b).app K = 0 := by
  have : (((TStructure.t.truncLT b).obj K)⟦(1 : ℤ)⟧).IsGE (a - 1) :=
    TStructure.t.isGE_shift _ a 1 (a - 1) (by omega)
  have : (((TStructure.t.truncLT b).obj K)⟦(1 : ℤ)⟧).IsLE (b - 2) :=
    TStructure.t.isLE_shift _ (b - 1) 1 (b - 2) (by omega)
  obtain ⟨eM⟩ := nonempty_iso_singleFunctor_obj_homology ((TStructure.t.truncGE b).obj K) b
  refine hom_eq_zero_of_forall_hom_singleFunctor_obj_homology_eq_zero
    ((TStructure.t.truncGE b).obj K) (((TStructure.t.truncLT b).obj K)⟦(1 : ℤ)⟧) (a - 1) (b - 2)
    (fun j hj hj' g => ?_) _
  exact hom_eq_zero_of_iso (eM ≪≫ (singleFunctor C b).mapIso (homologyTruncGEIso K b))
    ((singleFunctor C j).mapIso (homologyShiftIso _ j (j + 1) (by omega) ≪≫
      homologyTruncLTIso K (j + 1) b (by omega))) (hyp b (j + 1) j (by omega) rfl) g

/-- **The induction.** `K` with cohomology in `[a, b]` and no morphisms between the shifts of
its cohomology objects is the biproduct of them: the case `b + 1 ≤ a + n`. -/
private lemma nonempty_iso_biproduct_aux (n : ℕ) :
    ∀ (a b : ℤ) (K : DerivedCategory C), b + 1 ≤ a + n → ∀ [K.IsGE a] [K.IsLE b],
      (∀ (i j k : ℤ), j < i → k + 1 = j →
        ∀ f : (singleFunctor C i).obj ((homologyFunctor C i).obj K) ⟶
          (singleFunctor C k).obj ((homologyFunctor C j).obj K), f = 0) →
      Nonempty (K ≅ ⨁ fun i : (Finset.Icc a b : Finset ℤ) =>
        (singleFunctor C i.1).obj ((homologyFunctor C i.1).obj K)) := by
  induction n with
  | zero =>
      intro a b K hab _ _ _
      exact ⟨(TStructure.t.isZero K b a (by omega)).iso (isZero_biproductIcc
        (fun i => (singleFunctor C i).obj ((homologyFunctor C i).obj K)) a b (by omega))⟩
  | succ n ih =>
      intro a b K hab _ _ hyp
      rcases lt_or_ge b a with hba | hba
      · exact ih a b K (by omega) hyp
      obtain ⟨e₁⟩ := nonempty_iso_biprod_of_mor₃_eq_zero _
        (TStructure.t.triangleLTGE_distinguished b K) (truncGEδLT_app_eq_zero K a b hyp)
      obtain ⟨eM⟩ := nonempty_iso_singleFunctor_obj_homology ((TStructure.t.truncGE b).obj K) b
      have hypL : ∀ (i j k : ℤ), j < i → k + 1 = j →
          ∀ f : (singleFunctor C i).obj
                ((homologyFunctor C i).obj ((TStructure.t.truncLT b).obj K)) ⟶
              (singleFunctor C k).obj
                ((homologyFunctor C j).obj ((TStructure.t.truncLT b).obj K)), f = 0 := by
        intro i j k hij hkj f
        by_cases hi : i < b
        · by_cases hj : j < b
          · exact hom_eq_zero_of_iso ((singleFunctor C i).mapIso (homologyTruncLTIso K i b hi))
              ((singleFunctor C k).mapIso (homologyTruncLTIso K j b hj)) (hyp i j k hij hkj) f
          · exact ((singleFunctor C k).map_isZero
              (isZero_of_isLE _ (b - 1) j (by omega))).eq_of_tgt _ _
        · exact ((singleFunctor C i).map_isZero
            (isZero_of_isLE _ (b - 1) i (by omega))).eq_of_src _ _
      obtain ⟨e₂⟩ := ih a (b - 1) ((TStructure.t.truncLT b).obj K) (by omega) hypL
      exact ⟨e₁ ≪≫ biprod.mapIso (e₂ ≪≫ biproduct.mapIso fun i =>
          (singleFunctor C i.1).mapIso
            (homologyTruncLTIso K i.1 b (by have := Finset.mem_Icc.mp i.2; omega)))
          (eM ≪≫ (singleFunctor C b).mapIso (homologyTruncGEIso K b)) ≪≫
        (biproductIccIso (fun i => (singleFunctor C i).obj ((homologyFunctor C i).obj K)) a b
          hba).symm⟩

variable [HasExt.{w'} C]

/-- The vanishing of `Ext^p_𝒜(A, B)` says that every morphism `A[0] ⟶ B[0][p]` in the derived
category is zero. -/
private lemma shiftedHom_eq_zero_of_forall_ext_eq_zero (A B : C) (p : ℕ)
    (h : ∀ e : Abelian.Ext.{w'} A B p, e = 0)
    (g : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj B)⟦(p : ℤ)⟧) : g = 0 := by
  have hg : (Abelian.Ext.homEquiv.symm g).hom = 0 := by
    rw [h (Abelian.Ext.homEquiv.symm g)]
    exact Abelian.Ext.zero_hom (X := A) (Y := B) (n := p)
  simpa [Abelian.Ext.hom] using hg

/-- The translation of the vanishing of `Ext^p_𝒜(A, B)` into the vanishing of the group of
morphisms from `A` placed in degree `m` to `B` placed in degree `k`, where `p + k = m`. -/
private lemma hom_eq_zero_of_forall_ext_eq_zero (A B : C) (m k : ℤ) (p : ℕ)
    (hp : (p : ℤ) + k = m) (h : ∀ e : Abelian.Ext.{w'} A B p, e = 0)
    (f : (singleFunctor C m).obj A ⟶ (singleFunctor C k).obj B) : f = 0 := by
  refine (shiftFunctor (DerivedCategory C) m).map_injective ?_
  rw [Functor.map_zero]
  exact hom_eq_zero_of_iso (((singleFunctors C).shiftIso m 0 m (by omega)).app A)
    (((singleFunctors C).shiftIso m (k - m) k (by omega)).app B ≪≫
      (((singleFunctors C).shiftIso (p : ℤ) (k - m) 0 (by omega)).app B).symm)
    (shiftedHom_eq_zero_of_forall_ext_eq_zero A B p h) _

/-- **A bounded complex with no higher Ext between its cohomologies is the sum of them.**
Let `𝒜` be an abelian category and let `K` be an object of `D(𝒜)` whose cohomology vanishes
outside `[a, b]`. If `Ext^p_𝒜(H^i(K), H^j(K)) = 0` for all `p ≥ 2` and all `i > j`, then `K` is
isomorphic to the direct sum `⨁_{a ≤ i ≤ b} H^i(K)[-i]` of its cohomologies. The isomorphism
depends on choices of splittings, so only its existence is asserted. For `a = b` this is
`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`. -/
@[stacks 0GM4]
public theorem nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_eq_zero
    (K : DerivedCategory C) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (h : ∀ (i j : ℤ) (p : ℕ), j < i → 2 ≤ p →
      ∀ e : Abelian.Ext.{w'} ((homologyFunctor C i).obj K) ((homologyFunctor C j).obj K) p,
        e = 0) :
    Nonempty (K ≅ ⨁ fun i : Finset.Icc a b =>
      (singleFunctor C i.1).obj ((homologyFunctor C i.1).obj K)) :=
  nonempty_iso_biproduct_aux (b + 1 - a).toNat a b K (by omega) fun i j k hij hkj f =>
    hom_eq_zero_of_forall_ext_eq_zero _ _ i k (i - k).toNat (by omega)
      (h i j (i - k).toNat hij (by omega)) f

end

section

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w'} C]

/-- **Vanishing of `Ext^p` between all pairs of objects propagates upwards in the degree.**
If `Ext^p_𝒜(B, A) = 0` for every pair of objects `A`, `B` of an abelian category `𝒜`, then
`Ext^q_𝒜(B, A) = 0` for every `q ≥ p` and every pair `A`, `B`. This is the two-slot reading of
[Stacks, Tag 0EWW] (`CategoryTheory.hasProjectiveDimensionLT_of_forall_ext_eq_zero`, stated for a
single object in the contravariant slot), the hypothesis giving `B` projective dimension `< p`. -/
private lemma ext_eq_zero_of_forall_forall_ext_eq_zero {p q : ℕ}
    (h : ∀ (A B : C) (e : Abelian.Ext.{w'} B A p), e = 0) (hpq : p ≤ q) {A B : C}
    (e : Abelian.Ext.{w'} B A q) : e = 0 :=
  have : HasProjectiveDimensionLT B p :=
    hasProjectiveDimensionLT_of_forall_ext_eq_zero B p fun Y e => h Y B e
  e.eq_zero_of_hasProjectiveDimensionLT p hpq

end

section

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C]

/-- **A bounded complex over a category with no `Ext²` is the sum of its cohomologies.**
Let `𝒜` be an abelian category with `Ext²_𝒜(B, A) = 0` for every pair of objects `A`, `B`, and
let `K` be an object of `D(𝒜)` whose cohomology vanishes outside `[a, b]`. Then `K` is
isomorphic to the direct sum `⨁_{a ≤ i ≤ b} H^i(K)[-i]` of its cohomologies. The isomorphism
depends on choices of splittings, so only its existence is asserted. This is the special case
of `DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_eq_zero`
([Stacks, Tag 0GM4]) in which the vanishing of `Ext^p`, `p ≥ 2`, comes from the category rather
than from `K`, via [Stacks, Tag 0EWW]. -/
@[stacks 0EWX]
public theorem nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_two_eq_zero
    (K : DerivedCategory C) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (h : ∀ (A B : C) (e : Abelian.Ext.{w'} B A 2), e = 0) :
    Nonempty (K ≅ ⨁ fun i : Finset.Icc a b =>
      (singleFunctor C i.1).obj ((homologyFunctor C i.1).obj K)) :=
  DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_eq_zero
    K a b fun _ _ _ _ hp e => ext_eq_zero_of_forall_forall_ext_eq_zero h hp e

end

end DerivedCategory

end

section

@[expose] public section


/-
# Problem Description

Throughout, `A` (here `C`) is an abelian category. We work with cochain
complexes indexed by `Z` (Mathlib: `CochainComplex C ℤ`).

- `K(A)` denotes the homotopy category `HomotopyCategory C (ComplexShape.up ℤ)`,
  with quotient functor `HomotopyCategory.quotient C (ComplexShape.up ℤ)`.
- `D(A)` denotes the derived category `DerivedCategory C`, with localization
  functors `DerivedCategory.Q` (from complexes) and `DerivedCategory.Qh` (from
  the homotopy category). We assume `[HasDerivedCategory C]`.
- `[n]` (i.e. `(-)⟦n⟧`) is the shift functor by `n : ℤ` on cochain complexes, on
  `K(A)` and on `D(A)`. All localization/quotient functors commute with the
  shift (`DerivedCategory.Qh.commShiftIso`), and
  `Qh.obj (quotient.obj X) ≅ Q.obj X` canonically, via
  `DerivedCategory.quotientCompQhIso : quotient ⋙ Qh ≅ Q`.

## Definition 1 (Ext groups, Stacks 06XQ / Definition 13.27.1)

For `X, Y` objects of `D(A)` and `i : ℤ`,
  `Ext^i_A(X, Y) = Hom_{D(A)}(X, Y[i])`.
For cochain complexes `X, Y` (objects of `K(A)`), read `X, Y` as their images in
`D(A)` under the localization functor `Q`, so that
  `Ext^i_A(X, Y) = Hom_{D(A)}(Q(X), Q(Y)[i])`.

## Definition 2 (Injective resolution, Stacks 013I / Definition 13.18.1)

An injective resolution of a cochain complex `Y` is a quasi-isomorphism
`f : Y → I` of cochain complexes, where `I` is bounded below
(`I.IsStrictlyGE n` for some `n : ℤ`) all of whose terms `I.X j` are injective
objects of `A`.

## Definition 3 (Projective resolution, Stacks 0644 / Definition 13.19.1)

A projective resolution of a cochain complex `X` is a quasi-isomorphism
`g : P → X` of cochain complexes, where `P` is bounded above
(`P.IsStrictlyLE m` for some `m : ℤ`) all of whose terms `P.X j` are projective
objects of `A`.

# Main Statement(s) — Stacks Tag 06XR (Lemma 13.27.2)

- Statement 1: given an injective resolution `f : Y → I`, there is a *canonical*
  bijection of Hom-sets
    `Hom_{D(A)}(Q(X), Q(Y)[i]) ≅ Hom_{K(A)}(X, I[i])`,
  induced by `f`. We render this canonical identification by exhibiting the
  explicit canonical map `Hom_{K(A)}(X, I[i]) → Hom_{D(A)}(Q(X), Q(Y)[i])`
  (`canMapOfInjectiveResolution`, built from `f`) and proving it is a bijection
  (and, packaging the same content, an `Equiv`).
- Statement 2: given a projective resolution `g : P → X`, there is a *canonical*
  bijection of Hom-sets
    `Hom_{D(A)}(Q(X), Q(Y)[i]) ≅ Hom_{K(A)}(P[-i], Y)`,
  induced by `g` (`canMapOfProjectiveResolution`).

## Notes on Interpretation

The Stacks text writes `Ext^i = Hom_{K(A)}(...)`, but the two sides are Hom-sets
in different categories (`D(A)` and `K(A)`). The `=` denotes the canonical
identification induced by the resolution; we render it as a *canonical*
bijection. Rather than merely asserting that *some* bijection exists, we exhibit
the explicit canonical map induced by the resolution `f` (resp. `g`) and assert
it is bijective; we also package this as an `Equiv` returned by a `def`.

The canonical map in part (1) is: apply `Qh` to a homotopy class
`α : X ⟶ I[i]`, identify `Qh(X) = Q(X)` and use that `Qh` commutes with the
shift to land in `(Q I)[i]`, then transport along the isomorphism
`Q(Y) ≅ Q(I)` induced by the quasi-isomorphism `f` (i.e. compose with the
inverse of `(Q f)[i]`). Part (2) is dual, using `(Q g)⁻¹` and the
shift-adjunction identification `Hom_D((Q P)[-i], Q Y) ≅ Hom_D(Q P, (Q Y)[i])`.

The boundedness hypotheses, together with degreewise injectivity (resp.
projectivity), are exactly what make `I` K-injective (Stacks 05TG,
`CochainComplex.isKInjective_of_injective`) and `P` K-projective (Stacks 064B,
`CochainComplex.isKProjective_of_projective`); these are the properties used in
the proof via `CochainComplex.IsKInjective.Qh_map_bijective` (resp.
`CochainComplex.IsKProjective.Qh_map_bijective`).

We phrase `Ext^i` through the derived category directly (as in Definition
13.27.1) to handle arbitrary cochain complexes, rather than the narrower
`CategoryTheory.Abelian.Ext` which is defined only for objects of `A` itself.
-/

open CategoryTheory

namespace ExtByResolutions

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

-- Main Definition(s)

/-- Definition 1 (Stacks 06XQ / 13.27.1): the `i`-th Ext group of objects
`X Y : D(A)` is `Hom_{D(A)}(X, Y[i])`. -/
def Ext (X Y : DerivedCategory C) (i : ℤ) : Type _ := X ⟶ Y⟦i⟧

/-- Definition 1, for cochain complexes: read `X, Y : CochainComplex C ℤ` as
their images `Q(X), Q(Y)` in the derived category. -/
def ExtComplex (X Y : CochainComplex C ℤ) (i : ℤ) : Type _ :=
  Ext (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y) i

/-- Definition 2 (Stacks 013I / 13.18.1): `f : Y ⟶ I` is an injective resolution
of `Y` if it is a quasi-isomorphism, `I` is bounded below, and each term `I.X j`
is injective. -/
structure IsInjectiveResolution {Y I : CochainComplex C ℤ} (f : Y ⟶ I) : Prop where
  quasiIso : QuasiIso f
  bddBelow : ∃ n : ℤ, I.IsStrictlyGE n
  injective : ∀ j, Injective (I.X j)

/-- Definition 3 (Stacks 0644 / 13.19.1): `g : P ⟶ X` is a projective resolution
of `X` if it is a quasi-isomorphism, `P` is bounded above, and each term `P.X j`
is projective. -/
structure IsProjectiveResolution {X P : CochainComplex C ℤ} (g : P ⟶ X) : Prop where
  quasiIso : QuasiIso g
  bddAbove : ∃ m : ℤ, P.IsStrictlyLE m
  projective : ∀ j, Projective (P.X j)

-- Canonical maps induced by the resolutions

/-- The **canonical map** induced by an injective resolution `f : Y ⟶ I`
(Statement 1, Stacks 06XR part 1):
  `Hom_{K(A)}(X, I[i]) → Hom_{D(A)}(Q(X), Q(Y)[i])`.
It sends a homotopy class `α : X ⟶ I[i]` to `Qh(α)`, identified via the
commutation of `Qh` with the shift and transported along the isomorphism
`Q(Y) ≅ Q(I)` induced by the quasi-isomorphism `f` (composition with the inverse
of the shifted `Q f`). -/
noncomputable def canMapOfInjectiveResolution
    (X Y I : CochainComplex C ℤ) (i : ℤ) (f : Y ⟶ I) [QuasiIso f]
    (α : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X ⟶
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)⟦i⟧) :
    DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj Y)⟦i⟧ :=
  -- Lean 4.34: `Qh.obj (quotient.obj ·)` is no longer definitionally `Q.obj ·`
  -- (`HomologicalComplexUpToQuasiIso.Qh` has an unexposed body), so the identification
  -- the docstring above describes is now written out explicitly, via Mathlib's
  -- `quotientCompQhIso : quotient ⋙ Qh ≅ Q`.  The stated type is unchanged.
  ((DerivedCategory.quotientCompQhIso C).app X).inv ≫
    DerivedCategory.Qh.map α ≫
    ((DerivedCategory.Qh.commShiftIso i).app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)).hom ≫
    ((shiftFunctor (DerivedCategory C) i).map
      ((DerivedCategory.quotientCompQhIso C).app I).hom) ≫
    ((shiftFunctor (DerivedCategory C) i).mapIso (asIso (DerivedCategory.Q.map f))).inv

/-- The **canonical map** induced by a projective resolution `g : P ⟶ X`
(Statement 2, Stacks 06XR part 2):
  `Hom_{K(A)}(P[-i], Y) → Hom_{D(A)}(Q(X), Q(Y)[i])`.
It sends a homotopy class `β : P[-i] ⟶ Y` to `Qh(β)`, identified via the
commutation of `Qh` with the shift, then re-indexed using the
shift-adjunction isomorphism `((Q P)[-i])[i] ≅ Q P` and transported along the
isomorphism `Q(X) ≅ Q(P)` induced by the quasi-isomorphism `g` (composition with
the inverse of `Q g`). -/
noncomputable def canMapOfProjectiveResolution
    (X Y P : CochainComplex C ℤ) (i : ℤ) (g : P ⟶ X) [QuasiIso g]
    (β : ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)⟦(-i)⟧ ⟶
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y) :
    DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj Y)⟦i⟧ :=
  -- Lean 4.34: as in `canMapOfInjectiveResolution`, the `Qh`/`Q` identification is now
  -- written out via `quotientCompQhIso` rather than left to defeq.  Type unchanged.
  let β' : (DerivedCategory.Q.obj P)⟦(-i)⟧ ⟶ DerivedCategory.Q.obj Y :=
    ((shiftFunctor (DerivedCategory C) (-i)).map
        ((DerivedCategory.quotientCompQhIso C).app P).inv) ≫
      ((DerivedCategory.Qh.commShiftIso (-i)).app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)).inv ≫
      DerivedCategory.Qh.map β ≫ ((DerivedCategory.quotientCompQhIso C).app Y).hom
  inv (DerivedCategory.Q.map g) ≫
    ((shiftFunctorCompIsoId (DerivedCategory C) (-i) i (by ring)).app
      (DerivedCategory.Q.obj P)).inv ≫
    (β'⟦i⟧')

/-- Pre- and post-composition with isomorphisms is a bijection on Hom-sets. -/
private lemma bijective_comp_comp_of_isIso {D : Type*} [Category D] {A A' B B' : D}
    (u : A' ⟶ A) (v : B ⟶ B') [IsIso u] [IsIso v] :
    Function.Bijective (fun γ : A ⟶ B => u ≫ γ ≫ v) :=
  (Iso.homCongr (asIso u).symm (asIso v)).bijective

/-- For a K-injective complex `I`, the functor `Qh : K(C) ⥤ D(C)` is bijective on morphisms
from any complex `X` into the shift `I[i]`. -/
theorem qhMap_bijective_shift (X I : CochainComplex C ℤ) (i : ℤ) [hI : I.IsKInjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X ⟶
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)⟦i⟧) →
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) ⟶
        DerivedCategory.Qh.obj (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            I)⟦i⟧))) := by
  set Quot := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  -- iso (quotient I)⟦i⟧ ≅ quotient (I⟦i⟧)
  let e : (Quot.obj I)⟦i⟧ ≅ Quot.obj (I⟦i⟧) := ((Quot.commShiftIso i).app I).symm
  have : (I⟦i⟧).IsKInjective := inferInstance
  have hb : Function.Bijective (DerivedCategory.Qh.map :
      (Quot.obj X ⟶ Quot.obj (I⟦i⟧)) → _) :=
    CochainComplex.IsKInjective.Qh_map_bijective (Quot.obj X) (I⟦i⟧)
  -- transport via e
  have key : (DerivedCategory.Qh.map :
      (Quot.obj X ⟶ (Quot.obj I)⟦i⟧) → _) =
      (fun γ => γ ≫ DerivedCategory.Qh.map e.inv) ∘
        (DerivedCategory.Qh.map : (Quot.obj X ⟶ Quot.obj (I⟦i⟧)) → _) ∘
        (fun α => α ≫ e.hom) := by
    funext α
    simp only [Function.comp_apply]
    rw [← DerivedCategory.Qh.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [key]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp hb ?_)
  · simpa only [Category.id_comp] using bijective_comp_comp_of_isIso (𝟙 _)
      (DerivedCategory.Qh.map e.inv)
  · simpa only [Category.id_comp] using bijective_comp_comp_of_isIso (𝟙 _) e.hom

/-- Precomposition with an isomorphism is a bijection on Hom-sets. -/
theorem precomp_iso_bijective {D : Type*} [Category D] {A B X : D} (u : A ⟶ B) [IsIso u] :
    Function.Bijective (fun γ : B ⟶ X => u ≫ γ) := by
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · simpa using congrArg (fun t => inv u ≫ t) hab
  · exact ⟨inv u ≫ y, by simp⟩

/-- For a K-projective complex `P`, the functor `Qh : K(C) ⥤ D(C)` is bijective on morphisms
from the shift `P[j]` into any complex `Y`. -/
theorem qhMap_bijective_shift_src (P Y : CochainComplex C ℤ) (j : ℤ) [hP : P.IsKProjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)⟦j⟧ ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y) →
      (DerivedCategory.Qh.obj (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)⟦j⟧) ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y))) := by
  set Quot := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let e : (Quot.obj P)⟦j⟧ ≅ Quot.obj (P⟦j⟧) := ((Quot.commShiftIso j).app P).symm
  have : (P⟦j⟧).IsKProjective := inferInstance
  have hb : Function.Bijective (DerivedCategory.Qh.map :
      (Quot.obj (P⟦j⟧) ⟶ Quot.obj Y) → _) :=
    CochainComplex.IsKProjective.Qh_map_bijective (P⟦j⟧) (Quot.obj Y)
  have key : (DerivedCategory.Qh.map :
      ((Quot.obj P)⟦j⟧ ⟶ Quot.obj Y) → _) =
      (fun δ => DerivedCategory.Qh.map e.hom ≫ δ) ∘
        (DerivedCategory.Qh.map : (Quot.obj (P⟦j⟧) ⟶ Quot.obj Y) → _) ∘
        (fun β => e.inv ≫ β) := by
    funext β
    simp only [Function.comp_apply]
    rw [← DerivedCategory.Qh.map_comp]
    simp only [Iso.hom_inv_id_assoc]
  rw [key]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp hb ?_)
  · simpa only [Category.comp_id] using bijective_comp_comp_of_isIso
      (DerivedCategory.Qh.map e.hom) (𝟙 _)
  · simpa only [Category.comp_id] using bijective_comp_comp_of_isIso e.inv (𝟙 _)

-- Main Statement(s)

/-- Statement 1 (Stacks 06XR, part 1): computing Ext via an injective resolution.
Given an injective resolution `f : Y ⟶ I` (Definition 2), the canonical map
`canMapOfInjectiveResolution` (induced by `f`) is a bijection
  `Hom_{K(A)}(X, I[i]) → Hom_{D(A)}(Q(X), Q(Y)[i])`.
This is the canonical identification
  `Ext^i_A(X, Y) = Hom_{D(A)}(Q(X), Q(Y)[i]) ≅ Hom_{K(A)}(X, I[i])`. -/
@[stacks 06XR "(1)"]
theorem ext_via_injective_resolution_bijective
    (X Y I : CochainComplex C ℤ) (i : ℤ)
    {f : Y ⟶ I} (hf : IsInjectiveResolution f) :
    haveI := hf.quasiIso
    Function.Bijective (canMapOfInjectiveResolution X Y I i f) := by
  have := hf.quasiIso
  set Quot := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  -- K-injectivity of I from boundedness + degreewise injectivity
  obtain ⟨n, hn⟩ := hf.bddBelow
  have : I.IsStrictlyGE n := hn
  have : ∀ j, Injective (I.X j) := hf.injective
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I n
  -- the post-composition isomorphism φ
  set φ : DerivedCategory.Qh.obj ((Quot.obj I)⟦i⟧) ⟶ (DerivedCategory.Q.obj Y)⟦i⟧ :=
    ((DerivedCategory.Qh.commShiftIso i).app (Quot.obj I)).hom ≫
      ((shiftFunctor (DerivedCategory C) i).map
        ((DerivedCategory.quotientCompQhIso C).app I).hom) ≫
      ((shiftFunctor (DerivedCategory C) i).mapIso (asIso (DerivedCategory.Q.map f))).inv with hφ
  have : IsIso φ := by
    rw [hφ]; infer_instance
  -- Lean 4.34: the source seam `Q.obj X` vs `Qh.obj (Quot.obj X)` also needs the explicit
  -- `quotientCompQhIso` identification, so the comparison is a `homCongr`, not a bare
  -- post-composition.  Both are bijections, so the statement is unaffected.
  have hcan : canMapOfInjectiveResolution X Y I i f =
      (fun g => ((DerivedCategory.quotientCompQhIso C).app X).inv ≫ g ≫ φ) ∘
        (DerivedCategory.Qh.map :
        (Quot.obj X ⟶ (Quot.obj I)⟦i⟧) → _) := by
    funext α
    show canMapOfInjectiveResolution X Y I i f α = _
    rw [hφ]
    rfl
  rw [hcan]
  refine Function.Bijective.comp ?_ (qhMap_bijective_shift X I i)
  -- pre-composition with `quotientCompQhIso` and post-composition with `φ` are bijections
  exact bijective_comp_comp_of_isIso ((DerivedCategory.quotientCompQhIso C).app X).inv φ

/-- Statement 2 (Stacks 06XR, part 2): computing Ext via a projective resolution.
Given a projective resolution `g : P ⟶ X` (Definition 3), the canonical map
`canMapOfProjectiveResolution` (induced by `g`) is a bijection
  `Hom_{K(A)}(P[-i], Y) → Hom_{D(A)}(Q(X), Q(Y)[i])`.
This is the canonical identification
  `Ext^i_A(X, Y) = Hom_{D(A)}(Q(X), Q(Y)[i]) ≅ Hom_{K(A)}(P[-i], Y)`. -/
@[stacks 06XR "(2)"]
theorem ext_via_projective_resolution_bijective
    (X Y P : CochainComplex C ℤ) (i : ℤ)
    {g : P ⟶ X} (hg : IsProjectiveResolution g) :
    haveI := hg.quasiIso
    Function.Bijective (canMapOfProjectiveResolution X Y P i g) := by
  have := hg.quasiIso
  set Quot := HomotopyCategory.quotient C (ComplexShape.up ℤ) with hQuot
  -- K-projectivity of P
  obtain ⟨m, hm⟩ := hg.bddAbove
  have : P.IsStrictlyLE m := hm
  have : ∀ j, Projective (P.X j) := hg.projective
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P m
  -- isos used in the composite
  -- Lean 4.34: `commShiftIso` only lands at `(Qh.obj (Quot.obj P))⟦-i⟧`, which is no longer
  -- definitionally `(Q.obj P)⟦-i⟧`; compose with the shifted `quotientCompQhIso` to land
  -- where the declared type says.  The declared type of `c` is unchanged.
  set c : DerivedCategory.Qh.obj ((Quot.obj P)⟦(-i)⟧) ≅ (DerivedCategory.Q.obj P)⟦(-i)⟧ :=
    (DerivedCategory.Qh.commShiftIso (-i)).app (Quot.obj P) ≪≫
      (shiftFunctor (DerivedCategory C) (-i)).mapIso
        ((DerivedCategory.quotientCompQhIso C).app P) with hc
  set ψ : (DerivedCategory.Q.obj P)⟦(-i)⟧⟦i⟧ ≅ DerivedCategory.Q.obj P :=
    (shiftFunctorCompIsoId (DerivedCategory C) (-i) i (by ring)).app (DerivedCategory.Q.obj P)
      with hψ
  -- Q.map g is an iso
  have : IsIso (DerivedCategory.Q.map g) := by infer_instance
  -- the post/pre-composition iso φ : Q P ⟶ (Q X)⟦?⟧  -- target side
  set φ : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj X :=
    DerivedCategory.Q.map g with hφ
  -- rewrite canMap as a composite of four bijections
  have hcan : canMapOfProjectiveResolution X Y P i g =
      (fun γ => inv (DerivedCategory.Q.map g) ≫ ψ.inv ≫ γ) ∘
        (fun β' : (DerivedCategory.Q.obj P)⟦(-i)⟧ ⟶ DerivedCategory.Q.obj Y => β'⟦i⟧') ∘
        (fun δ => c.inv ≫ δ ≫ ((DerivedCategory.quotientCompQhIso C).app Y).hom) ∘
        (DerivedCategory.Qh.map :
          ((Quot.obj P)⟦(-i)⟧ ⟶ Quot.obj Y) → _) := by
    funext β
    show canMapOfProjectiveResolution X Y P i g β = _
    simp only [canMapOfProjectiveResolution, Function.comp_apply, hc, hψ, Iso.trans_inv,
      Functor.mapIso_inv, Category.assoc]
    rfl
  rw [hcan]
  -- step1 : Qh.map bijective (shifted K-projective source)
  refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_
    (Function.Bijective.comp ?_ (qhMap_bijective_shift_src P Y (-i))))
  · -- step4: γ ↦ inv (Q.map g) ≫ ψ.inv ≫ γ ; reassociate then precompose with an iso
    have hb4 := precomp_iso_bijective (X := (DerivedCategory.Q.obj Y)⟦i⟧)
      (inv (DerivedCategory.Q.map g) ≫ ψ.inv)
    convert hb4 using 1
    funext γ; rw [Category.assoc]
  · -- step3: shift functor on morphisms is bijective
    refine ⟨fun a b hab => (shiftFunctor (DerivedCategory C) i).map_injective hab, fun y => ?_⟩
    exact ⟨(shiftFunctor (DerivedCategory C) i).preimage y,
      (shiftFunctor (DerivedCategory C) i).map_preimage y⟩
  · -- step2: pre-compose with `c.inv` and post-compose with `quotientCompQhIso` at `Y`
    exact bijective_comp_comp_of_isIso c.inv ((DerivedCategory.quotientCompQhIso C).app Y).hom

/-- Statement 1, packaged as the canonical `Equiv` induced by the injective
resolution `f` (`canMapOfInjectiveResolution` is its inverse direction):
  `Hom_{D(A)}(Q(X), Q(Y)[i]) ≃ Hom_{K(A)}(X, I[i])`. -/
noncomputable def extEquivOfInjectiveResolution
    (X Y I : CochainComplex C ℤ) (i : ℤ)
    {f : Y ⟶ I} (hf : IsInjectiveResolution f) :
    (DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj Y)⟦i⟧) ≃
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X ⟶
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)⟦i⟧) :=
  haveI := hf.quasiIso
  (Equiv.ofBijective _ (ext_via_injective_resolution_bijective X Y I i hf)).symm

/-- Statement 2, packaged as the canonical `Equiv` induced by the projective
resolution `g` (`canMapOfProjectiveResolution` is its inverse direction):
  `Hom_{D(A)}(Q(X), Q(Y)[i]) ≃ Hom_{K(A)}(P[-i], Y)`. -/
noncomputable def extEquivOfProjectiveResolution
    (X Y P : CochainComplex C ℤ) (i : ℤ)
    {g : P ⟶ X} (hg : IsProjectiveResolution g) :
    (DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj Y)⟦i⟧) ≃
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)⟦(-i)⟧ ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y) :=
  haveI := hg.quasiIso
  (Equiv.ofBijective _ (ext_via_projective_resolution_bijective X Y P i hg)).symm

end ExtByResolutions

end

end
