module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.PUnit
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.TotallySplit
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products of strictly perfect complexes

Let `R` be a commutative ring. A cochain complex of `R`-modules is strictly perfect if it is
bounded and each of its terms is a direct summand of a finite free module. The tensor product of
two strictly perfect complexes is strictly perfect; here the tensor product `E ⊗ F` of cochain
complexes is the total complex of the tensor product double complex, with the Koszul sign rule.

## Main definitions

* `IsFiniteFree`: a module isomorphic to `Fin n → R` for some `n`.
* `IsDirectSummandOfFiniteFree`: a module `M` with `M ⊞ N ≅ (Fin n → R)` for some `N` and `n`.
* `Bounded`: a complex whose terms vanish outside a finite set of degrees.
* `IsStrictlyPerfect`: a bounded complex whose terms are direct summands of finite free modules.

## Main results

* `isDirectSummandOfFiniteFree_iff_finite_projective`: a module is a direct summand of a finite
  free module if and only if it is finitely generated and projective.
* `isStrictlyPerfect_tensor`: the tensor product of two strictly perfect complexes is strictly
  perfect.

## Implementation notes

The source states the result for sheaves of modules on a ringed site `(C, 𝒪)`. The argument uses
only the additive structure and the symmetric monoidal tensor product, which distributes over
finite direct sums, so we state it for modules over a commutative ring `R`, with `𝒪 = R`.
-/

open CategoryTheory Limits MonoidalCategory

namespace Stacks.StrictlyPerfect.Modules

variable {R : Type} [CommRing R]

/-- An object `M` of `ModuleCat R` is *finite free* if it is isomorphic to `Fin n → R` for some
`n : ℕ`. -/
def IsFiniteFree (M : ModuleCat R) : Prop :=
  ∃ n : ℕ, Nonempty (M ≅ ModuleCat.of R (Fin n → R))

/-- An object `M` of `ModuleCat R` is a *direct summand of a finite free module* if there are a
module `N` and `n : ℕ` such that the biproduct `M ⊞ N` is isomorphic to `Fin n → R`. -/
def IsDirectSummandOfFiniteFree (M : ModuleCat R) : Prop :=
  ∃ (N : ModuleCat R) (n : ℕ), Nonempty ((M ⊞ N) ≅ ModuleCat.of R (Fin n → R))

/-- `E` is bounded if `E^i = 0` for all but finitely many `i`. -/
def Bounded (E : CochainComplex (ModuleCat R) ℤ) : Prop :=
  ∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s → IsZero (E.X i)

/-- A cochain complex of `R`-modules is *strictly perfect* if it is bounded and each of its terms
is a direct summand of a finite free module. -/
@[sga "6 I 2.1" "special case"]
structure IsStrictlyPerfect (E : CochainComplex (ModuleCat R) ℤ) : Prop where
  /-- The complex vanishes outside a finite set of degrees. -/
  bounded : Bounded E
  /-- Each term `E.X i` is a direct summand of a finite free module. -/
  termDirectSummand : ∀ i : ℤ, IsDirectSummandOfFiniteFree (E.X i)

/-- A module is a direct summand of a finite free module if and only if it is finitely generated
and projective. -/
@[sga "4½ Fonctions_L 1.12" "partial"]
theorem isDirectSummandOfFiniteFree_iff_finite_projective (M : ModuleCat R) :
    IsDirectSummandOfFiniteFree M ↔ (Module.Finite R M ∧ Module.Projective R M) := by
  constructor
  · rintro ⟨N, n, ⟨e⟩⟩
    set i : ↥M →ₗ[R] (Fin n → R) := (biprod.inl ≫ e.hom).hom with hi
    set s : (Fin n → R) →ₗ[R] ↥M := (e.inv ≫ biprod.fst).hom with hs
    have H : s ∘ₗ i = LinearMap.id := by
      rw [hi, hs, ← ModuleCat.hom_comp, Category.assoc, ← Category.assoc e.hom,
        e.hom_inv_id, Category.id_comp, biprod.inl_fst, ModuleCat.hom_id]
    exact ⟨Module.Finite.of_surjective s fun x => ⟨i x, LinearMap.congr_fun H x⟩,
      Module.Projective.of_split i s H⟩
  · rintro ⟨hfin, hproj⟩
    obtain ⟨n, f, g, hfsurj, hginj, hfg⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective R (↑M)
    have hgf : ∀ y : (↑M : Type), f (g y) = y := fun y => LinearMap.congr_fun hfg y
    have hcompl : IsCompl (LinearMap.range g) (LinearMap.ker f) := by
      constructor
      · rw [Submodule.disjoint_def]
        rintro x ⟨y, rfl⟩ hxk
        rw [LinearMap.mem_ker] at hxk
        simp [(hgf y).symm.trans hxk]
      · rw [codisjoint_iff_le_sup]
        intro z _
        refine Submodule.mem_sup.mpr ⟨g (f z), ⟨f z, rfl⟩, z - g (f z), ?_, by abel⟩
        rw [LinearMap.mem_ker, map_sub, hgf]
        simp
    exact ⟨ModuleCat.of R (LinearMap.ker f), n, ⟨ModuleCat.biprodIsoProd M _ ≪≫
      (((LinearEquiv.ofInjective g hginj).prodCongr (LinearEquiv.refl R _)).trans
        (Submodule.prodEquivOfIsCompl _ _ hcompl)).toModuleIso⟩⟩

/-- The tensor product of two direct summands of finite free modules is a direct summand of a
finite free module. -/
theorem IsDirectSummandOfFiniteFree.tensor {M M' : ModuleCat R}
    (hM : IsDirectSummandOfFiniteFree M) (hM' : IsDirectSummandOfFiniteFree M') :
    IsDirectSummandOfFiniteFree (M ⊗ M') := by
  rw [isDirectSummandOfFiniteFree_iff_finite_projective] at hM hM' ⊢
  obtain ⟨hMfin, hMproj⟩ := hM
  obtain ⟨hM'fin, hM'proj⟩ := hM'
  exact ⟨Module.Finite.tensorProduct R M M', Module.Projective.tensorProduct⟩

/-- A finite biproduct of direct summands of finite free modules is a direct summand of a finite
free module. -/
theorem IsDirectSummandOfFiniteFree.biproduct {ι : Type} [Finite ι]
    (f : ι → ModuleCat R) (hf : ∀ j, IsDirectSummandOfFiniteFree (f j)) :
    IsDirectSummandOfFiniteFree (⨁ f) := by
  have := Fintype.ofFinite ι
  rw [isDirectSummandOfFiniteFree_iff_finite_projective]
  have hfin : ∀ j, Module.Finite R (f j) := fun j =>
    ((isDirectSummandOfFiniteFree_iff_finite_projective (f j)).mp (hf j)).1
  have hproj : ∀ j, Module.Projective R (f j) := fun j =>
    ((isDirectSummandOfFiniteFree_iff_finite_projective (f j)).mp (hf j)).2
  have e : (↑(⨁ f) : Type) ≃ₗ[R] ((j : ι) → ↑(f j)) :=
    (ModuleCat.biproductIsoPi f).toLinearEquiv
  classical
  exact ⟨Module.Finite.equiv e.symm,
    .of_equiv ((DFinsupp.linearEquivFunOnFintype (R := R) (M := fun j => ↑(f j))).trans e.symm)⟩

/-- Tensoring a zero object on the left yields a zero object. -/
private lemma isZero_tensor_left {X Y : ModuleCat R} (hX : IsZero X) : IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero] at hX ⊢
  rw [← id_tensorHom_id, hX, MonoidalPreadditive.zero_tensor]

/-- Tensoring a zero object on the right yields a zero object. -/
private lemma isZero_tensor_right {X Y : ModuleCat R} (hY : IsZero Y) : IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero] at hY ⊢
  rw [← id_tensorHom_id, hY, MonoidalPreadditive.tensor_zero]

/-- For bounded `E`, `F` (vanishing outside `sE`, `sF`), the degree-`n` term of `E ⊗ F` is
isomorphic to the (finite) biproduct of `E.X p ⊗ F.X q` over the support antidiagonal
`T := (sE ×ˢ sF).filter (fun pq => pq.1 + pq.2 = n)`. -/
theorem tensorObj_X_iso_biproduct (E F : CochainComplex (ModuleCat R) ℤ)
    (sE sF : Finset ℤ)
    (hE : ∀ i, i ∉ sE → IsZero (E.X i)) (hF : ∀ i, i ∉ sF → IsZero (F.X i))
    (n : ℤ) (T : Finset (ℤ × ℤ)) (hT : T = (sE ×ˢ sF).filter (fun pq => pq.1 + pq.2 = n)) :
    Nonempty ((E ⊗ F).X n ≅
      ⨁ (fun (j : T) => E.X (j : ℤ × ℤ).1 ⊗ F.X (j : ℤ × ℤ).2)) := by
  have hmemsum : ∀ j : T, ((j : ℤ × ℤ).1 + (j : ℤ × ℤ).2 = n) := by
    intro j
    have h := j.2
    simp only [hT, Finset.mem_filter] at h
    exact h.2
  have hzero : ∀ (i₁ i₂ : ℤ), i₁ + i₂ = n → (i₁, i₂) ∉ T → IsZero (E.X i₁ ⊗ F.X i₂) := by
    intro i₁ i₂ hsum hnot
    rw [hT, Finset.mem_filter, Finset.mem_product] at hnot
    by_cases h1 : i₁ ∈ sE
    · exact isZero_tensor_right (hF i₂ fun h2 => hnot ⟨⟨h1, h2⟩, hsum⟩)
    · exact isZero_tensor_left (hE i₁ h1)
  set fam : T → ModuleCat R := fun (j : T) => E.X (j : ℤ × ℤ).1 ⊗ F.X (j : ℤ × ℤ).2
  let homf : (i₁ i₂ : ℤ) → i₁ + i₂ = n →
      (MonoidalCategoryStruct.tensorObj (E.X i₁) (F.X i₂) ⟶ ⨁ fam) := by
    intro i₁ i₂ h
    by_cases hmem : (i₁, i₂) ∈ T
    · exact biproduct.ι fam ⟨(i₁, i₂), hmem⟩
    · exact 0
  have he : ∀ i₁ i₂ h (hmem : (i₁, i₂) ∈ T), homf i₁ i₂ h = biproduct.ι fam ⟨(i₁, i₂), hmem⟩ :=
    fun _ _ _ hmem => by simp only [homf, dite_eq_left hmem]
  let iso' : GradedObject.Monoidal.tensorObj E.X F.X n ≅ ⨁ fam :=
    { hom := GradedObject.Monoidal.tensorObjDesc homf
      inv := biproduct.desc (fun (j : T) =>
        GradedObject.Monoidal.ιTensorObj E.X F.X (j : ℤ × ℤ).1 (j : ℤ × ℤ).2 n (hmemsum j))
      hom_inv_id := by
        apply GradedObject.Monoidal.tensorObj_ext
        intro i₁ i₂ hi
        rw [← Category.assoc, GradedObject.Monoidal.ι_tensorObjDesc, Category.comp_id]
        by_cases hmem : (i₁, i₂) ∈ T
        · rw [he _ _ hi hmem, biproduct.ι_desc]
        · exact (hzero i₁ i₂ hi hmem).eq_of_src _ _
      inv_hom_id := by
        apply biproduct.hom_ext'
        intro j
        rw [← Category.assoc, biproduct.ι_desc, GradedObject.Monoidal.ι_tensorObjDesc,
          Category.comp_id]
        rw [he _ _ (hmemsum j) j.2] }
  exact ⟨iso'⟩

/-- If `E` and `F` vanish outside finite sets `sE` and `sF`, then `(E ⊗ F).X n` is a zero object
whenever `n` is not of the form `p + q` with `p ∈ sE` and `q ∈ sF`. -/
theorem tensorObj_X_isZero_of_not_mem_add (E F : CochainComplex (ModuleCat R) ℤ)
    (sE sF : Finset ℤ)
    (hE : ∀ i, i ∉ sE → IsZero (E.X i)) (hF : ∀ i, i ∉ sF → IsZero (F.X i))
    (n : ℤ) (hn : n ∉ (sE ×ˢ sF).image (fun pq => pq.1 + pq.2)) :
    IsZero ((E ⊗ F).X n) := by
  set T : Finset (ℤ × ℤ) := (sE ×ˢ sF).filter (fun pq => pq.1 + pq.2 = n) with hT
  have hTempty : T = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro pq hpq hsum
    exact hn (Finset.mem_image.mpr ⟨pq, hpq, hsum⟩)
  obtain ⟨iso⟩ := tensorObj_X_iso_biproduct E F sE sF hE hF n T hT
  have hempty : IsEmpty (T : Type) := by
    rw [hTempty]
    infer_instance
  have hzero : IsZero (⨁ (fun (j : T) => E.X (j : ℤ × ℤ).1 ⊗ F.X (j : ℤ × ℤ).2)) :=
    (IsZero.iff_id_eq_zero _).mpr (biproduct.hom_ext _ _ fun j => isEmptyElim j)
  exact hzero.of_iso iso

/-- If `E` and `F` are strictly perfect complexes of `R`-modules, then so is their tensor product
`E ⊗ F`, the total complex of the tensor product double complex. -/
@[stacks 09J8]
theorem isStrictlyPerfect_tensor
    (E F : CochainComplex (ModuleCat R) ℤ)
    (hE : IsStrictlyPerfect E) (hF : IsStrictlyPerfect F) :
    IsStrictlyPerfect (E ⊗ F) := by
  obtain ⟨sE, hsE⟩ := hE.bounded
  obtain ⟨sF, hsF⟩ := hF.bounded
  refine ⟨⟨_, tensorObj_X_isZero_of_not_mem_add E F sE sF hsE hsF⟩, fun n => ?_⟩
  set T : Finset (ℤ × ℤ) := (sE ×ˢ sF).filter (fun pq => pq.1 + pq.2 = n) with hT
  obtain ⟨iso⟩ := tensorObj_X_iso_biproduct E F sE sF hsE hsF n T hT
  obtain ⟨N, m, ⟨e⟩⟩ : IsDirectSummandOfFiniteFree
      (⨁ (fun (j : T) => E.X (j : ℤ × ℤ).1 ⊗ F.X (j : ℤ × ℤ).2)) :=
    .biproduct _ fun _ => (hE.termDirectSummand _).tensor (hF.termDirectSummand _)
  exact ⟨N, m, ⟨(biprod.mapIso iso (Iso.refl N)) ≪≫ e⟩⟩

end Stacks.StrictlyPerfect.Modules
