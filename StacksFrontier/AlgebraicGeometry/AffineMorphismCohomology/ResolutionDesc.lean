module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Comparing an arbitrary resolution with an injective resolution

Let `𝒞` be an abelian category, `B` an object of it, and `ι : B[0] ⟶ K` a quasi-isomorphism
from the complex concentrated in degree zero on `B` to an `ℕ`-indexed cochain complex `K`.
That is exactly the data of an exact resolution `0 ⟶ B ⟶ K ⁰ ⟶ K ¹ ⟶ ⋯` of `B`, with **no
assumption that the terms of `K` are injective**. Let `J` be an injective resolution of `B`.

This file produces a comparison `K ⟶ J.cocomplex` over the identity of `B`, and shows that any
two such comparisons are homotopic, hence agree on homology after an additive functor is
applied.

Mathlib proves both statements for `CategoryTheory.InjectiveResolution.desc` and
`CategoryTheory.InjectiveResolution.descHomotopy`, where the source is an injective resolution
too. The constructions use only *exactness* of the source and *injectivity of the terms* of the
target, so they go through verbatim when the source is not an `InjectiveResolution`.

## Main definitions

* `Stacks.ResolutionDesc.desc`: a cochain map `K ⟶ J.cocomplex` whose degree-zero component
  intertwines the two augmentations.
* `Stacks.ResolutionDesc.homotopy`: two comparisons agreeing on the augmentation are homotopic.

## Main results

* `Stacks.ResolutionDesc.exact₀` and `Stacks.ResolutionDesc.exact_succ`: the resolution is
  exact, in the two shapes `CategoryTheory.ShortComplex.Exact.descToInjective` consumes.
* `Stacks.ResolutionDesc.homologyMap_map_eq`: therefore any two comparisons induce the same map
  on the homology of `T` applied termwise, for every additive `T`.

## Implementation notes

**Exactness in degree zero.** `CategoryTheory.InjectiveResolution.exact₀` is proved from the
kernel fork of the augmentation. Here `exact₀` is obtained differently: the degree-zero cycles of
an `ℕ`-indexed cochain complex receive the augmentation (`cyclesComparison`), that comparison is
invertible because `CochainComplex.isoHomologyπ₀_inv_naturality` identifies it with the homology
comparison in degree zero, and `HomologicalComplex.cyclesIsKernel` already says that the cycles
are the kernel of the differential. `CategoryTheory.ShortComplex.exact_of_iso` then transports
exactness from the cycles to `B`.

**Degrees.** Everything is `ℕ`-indexed; the quasi-isomorphism hypothesis is used twice, through
`quasiIsoAt_iff_isIso_homologyMap` in degree zero and through `quasiIsoAt_iff_exactAt` in the
positive degrees, as in `CategoryTheory.InjectiveResolution.cocomplex_exactAt_succ`.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category HomologicalComplex

namespace Stacks.ResolutionDesc

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {B : C} {K : CochainComplex C ℕ}
  (ι : (CochainComplex.single₀ C).obj B ⟶ K) [QuasiIso ι]

/-! ### Exactness of the resolution -/

/-- The comparison of `B`, read in degree zero of the single complex, with the degree-zero
cycles of `K`. -/
noncomputable def cyclesComparison :
    ((CochainComplex.single₀ C).obj B).X 0 ⟶ K.cycles 0 :=
  (((CochainComplex.single₀ C).obj B).iCyclesIso 0 _ rfl rfl).inv ≫
    HomologicalComplex.cyclesMap ι 0

omit [QuasiIso ι] in
/-- The comparison `cyclesComparison ι` followed by the inclusion of the cycles is `ι.f 0`. -/
lemma cyclesComparison_comp_iCycles : cyclesComparison ι ≫ K.iCycles 0 = ι.f 0 := by
  rw [cyclesComparison, assoc, HomologicalComplex.cyclesMap_i, ← assoc,
    show (((CochainComplex.single₀ C).obj B).iCyclesIso 0 _ rfl rfl).inv ≫
        ((CochainComplex.single₀ C).obj B).iCycles 0 = 𝟙 _ from
      (((CochainComplex.single₀ C).obj B).iCyclesIso 0 _ rfl rfl).inv_hom_id, id_comp]

/-- The map induced by `ι` on degree-zero cycles is an isomorphism. -/
instance isIso_cyclesMap_zero : IsIso (HomologicalComplex.cyclesMap ι 0) := by
  have hhom : IsIso (HomologicalComplex.homologyMap ι 0) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  have h2 : IsIso (HomologicalComplex.homologyMap ι 0 ≫ K.isoHomologyπ₀.inv) := inferInstance
  rw [CochainComplex.isoHomologyπ₀_inv_naturality ι] at h2
  exact IsIso.of_isIso_comp_left
    ((CochainComplex.single₀ C).obj B).isoHomologyπ₀.inv
    (HomologicalComplex.cyclesMap ι 0)

/-- The comparison `cyclesComparison ι` is an isomorphism. -/
instance isIso_cyclesComparison : IsIso (cyclesComparison ι) := by
  rw [cyclesComparison]
  infer_instance

/-- The augmentation `ι.f 0 : B ⟶ K ⁰` is a monomorphism. -/
instance mono_f_zero : Mono (ι.f 0) := by
  rw [← cyclesComparison_comp_iCycles ι]
  infer_instance

omit [QuasiIso ι] in
/-- The augmentation followed by the first differential of `K` is zero. -/
lemma f_zero_comp_d : ι.f 0 ≫ K.d 0 1 = 0 := by
  rw [ι.comm 0 1,
    show ((CochainComplex.single₀ C).obj B).d 0 1 = 0 from
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 B 1
        (by simp)).eq_of_tgt _ _, zero_comp]

/-- **The resolution is exact in degree zero**: `0 ⟶ B ⟶ K ⁰ ⟶ K ¹` is exact at `K ⁰`. -/
lemma exact₀ : (ShortComplex.mk (ι.f 0) (K.d 0 1) (f_zero_comp_d ι)).Exact := by
  have hS : (ShortComplex.mk (K.iCycles 0) (K.d 0 1) (K.iCycles_d 0 1)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel 0 1 (by simp))
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk
    (asIso (cyclesComparison ι)).symm (Iso.refl (K.X 0)) (Iso.refl (K.X 1)) ?_ ?_) hS
  · exact ((Iso.inv_comp_eq (asIso (cyclesComparison ι))).2
      (cyclesComparison_comp_iCycles ι).symm).trans (comp_id _).symm
  · exact (id_comp _).trans (comp_id _).symm

include ι in
/-- The resolution is exact in the positive degrees. -/
lemma exactAt_succ (n : ℕ) : K.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt ι (n + 1) (CochainComplex.exactAt_succ_single_obj _ _)]
  infer_instance

include ι in
/-- The resolution is exact in the positive degrees, as a short complex. -/
lemma exact_succ (n : ℕ) :
    (ShortComplex.mk _ _ (K.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (exactAt_succ ι n)

/-! ### The comparison with an injective resolution -/

section Desc

variable (J : InjectiveResolution B)

/-- Auxiliary construction for `Stacks.ResolutionDesc.desc`. -/
noncomputable def descFZero : K.X 0 ⟶ J.cocomplex.X 0 :=
  Injective.factorThru (J.ι.f 0) (ι.f 0)

/-- The degree-zero component `descFZero ι J` intertwines the two augmentations. -/
@[reassoc (attr := simp)]
lemma f_zero_comp_descFZero : ι.f 0 ≫ descFZero ι J = J.ι.f 0 :=
  Injective.comp_factorThru _ _

/-- The composite `B ⟶ K ⁰ ⟶ J ⁰ ⟶ J ¹` of the augmentation, `descFZero ι J` and the
differential of `J.cocomplex` is zero. -/
lemma f_zero_comp_descFZero_comp_d :
    ι.f 0 ≫ descFZero ι J ≫ J.cocomplex.d 0 1 = 0 := by
  rw [← assoc, f_zero_comp_descFZero, J.ι_f_zero_comp_complex_d]

/-- Auxiliary construction for `Stacks.ResolutionDesc.desc`. -/
noncomputable def descFOne : K.X 1 ⟶ J.cocomplex.X 1 :=
  (exact₀ ι).descToInjective (descFZero ι J ≫ J.cocomplex.d 0 1)
    (f_zero_comp_descFZero_comp_d ι J)

/-- The components `descFZero ι J` and `descFOne ι J` commute with the differentials in
degrees zero and one. -/
@[reassoc (attr := simp)]
lemma d_comp_descFOne :
    K.d 0 1 ≫ descFOne ι J = descFZero ι J ≫ J.cocomplex.d 0 1 :=
  (exact₀ ι).comp_descToInjective _ _

/-- If `g` and `g'` commute with the differentials in degrees `n` and `n + 1`, then
`K.d n (n + 1) ≫ g' ≫ J.cocomplex.d (n + 1) (n + 2) = 0`. -/
lemma d_comp_comp_d_succ (n : ℕ) (g : K.X n ⟶ J.cocomplex.X n)
    (g' : K.X (n + 1) ⟶ J.cocomplex.X (n + 1))
    (w : K.d n (n + 1) ≫ g' = g ≫ J.cocomplex.d n (n + 1)) :
    K.d n (n + 1) ≫ g' ≫ J.cocomplex.d (n + 1) (n + 2) = 0 := by
  rw [← assoc, w, assoc, HomologicalComplex.d_comp_d, comp_zero]

/-- Auxiliary construction for `Stacks.ResolutionDesc.desc`. -/
noncomputable def descFSucc (n : ℕ) (g : K.X n ⟶ J.cocomplex.X n)
    (g' : K.X (n + 1) ⟶ J.cocomplex.X (n + 1))
    (w : K.d n (n + 1) ≫ g' = g ≫ J.cocomplex.d n (n + 1)) :
    Σ' g'' : K.X (n + 2) ⟶ J.cocomplex.X (n + 2),
      K.d (n + 1) (n + 2) ≫ g'' = g' ≫ J.cocomplex.d (n + 1) (n + 2) :=
  ⟨(exact_succ ι n).descToInjective (g' ≫ J.cocomplex.d (n + 1) (n + 2))
      (d_comp_comp_d_succ J n g g' w),
    (exact_succ ι n).comp_descToInjective _ _⟩

/-- **The comparison of the resolution with an injective resolution of the same object.** -/
noncomputable def desc : K ⟶ J.cocomplex :=
  CochainComplex.mkHom _ _ (descFZero ι J) (descFOne ι J) (d_comp_descFOne ι J).symm
    fun n ⟨g, g', w⟩ => ⟨(descFSucc ι J n g g' w.symm).1, (descFSucc ι J n g g' w.symm).2.symm⟩

/-- The degree-zero component of `desc ι J` is `descFZero ι J`. -/
@[simp]
lemma desc_f_zero : (desc ι J).f 0 = descFZero ι J := rfl

/-- The comparison intertwines the two augmentations. -/
lemma f_zero_comp_desc_f_zero : ι.f 0 ≫ (desc ι J).f 0 = J.ι.f 0 := by
  rw [desc_f_zero, f_zero_comp_descFZero]

end Desc

/-! ### Uniqueness of the comparison up to homotopy

Here the injective resolution is allowed to resolve a *different* object: the construction below
uses only exactness of `K` and injectivity of the terms of `J.cocomplex`, so two comparisons over
one and the same morphism `B ⟶ B'` are homotopic. -/

section Homotopy

variable {B' : C} (J : InjectiveResolution B')

/-- Auxiliary construction for `Stacks.ResolutionDesc.homotopyZero`. -/
noncomputable def homotopyZeroZero (φ : K ⟶ J.cocomplex) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.X 1 ⟶ J.cocomplex.X 0 :=
  (exact₀ ι).descToInjective (φ.f 0) comm

/-- The first differential of `K` followed by `homotopyZeroZero ι J φ comm` is `φ.f 0`. -/
@[reassoc (attr := simp)]
lemma d_comp_homotopyZeroZero (φ : K ⟶ J.cocomplex) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.d 0 1 ≫ homotopyZeroZero ι J φ comm = φ.f 0 :=
  (exact₀ ι).comp_descToInjective _ _

/-- The first differential of `K` kills
`φ.f 1 - homotopyZeroZero ι J φ comm ≫ J.cocomplex.d 0 1`. -/
lemma d_comp_homotopyZeroOne_aux (φ : K ⟶ J.cocomplex) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.d 0 1 ≫ (φ.f 1 - homotopyZeroZero ι J φ comm ≫ J.cocomplex.d 0 1) = 0 := by
  rw [Preadditive.comp_sub, d_comp_homotopyZeroZero_assoc ι J φ comm,
    HomologicalComplex.Hom.comm, sub_self]

/-- Auxiliary construction for `Stacks.ResolutionDesc.homotopyZero`. -/
noncomputable def homotopyZeroOne (φ : K ⟶ J.cocomplex) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.X 2 ⟶ J.cocomplex.X 1 :=
  (exact_succ ι 0).descToInjective
    (φ.f 1 - homotopyZeroZero ι J φ comm ≫ J.cocomplex.d 0 1)
    (d_comp_homotopyZeroOne_aux ι J φ comm)

/-- The differential `K.d 1 2` followed by `homotopyZeroOne ι J φ comm` is
`φ.f 1 - homotopyZeroZero ι J φ comm ≫ J.cocomplex.d 0 1`. -/
@[reassoc (attr := simp)]
lemma d_comp_homotopyZeroOne (φ : K ⟶ J.cocomplex) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.d 1 2 ≫ homotopyZeroOne ι J φ comm =
      φ.f 1 - homotopyZeroZero ι J φ comm ≫ J.cocomplex.d 0 1 :=
  (exact_succ ι 0).comp_descToInjective _ _

/-- If `φ.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)`, then the
differential `K.d (n + 1) (n + 2)` kills `φ.f (n + 2) - g' ≫ J.cocomplex.d (n + 1) (n + 2)`. -/
lemma d_comp_homotopyZeroSucc_aux (φ : K ⟶ J.cocomplex) (n : ℕ)
    (g : K.X (n + 1) ⟶ J.cocomplex.X n) (g' : K.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : φ.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    K.d (n + 1) (n + 2) ≫
      (φ.f (n + 2) - g' ≫ J.cocomplex.d (n + 1) (n + 2)) = 0 := by
  rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
    assoc, assoc, HomologicalComplex.d_comp_d, comp_zero, add_zero, sub_self]

/-- Auxiliary construction for `Stacks.ResolutionDesc.homotopyZero`. -/
noncomputable def homotopyZeroSucc (φ : K ⟶ J.cocomplex) (n : ℕ)
    (g : K.X (n + 1) ⟶ J.cocomplex.X n) (g' : K.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : φ.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    K.X (n + 3) ⟶ J.cocomplex.X (n + 2) :=
  (exact_succ ι (n + 1)).descToInjective
    (φ.f (n + 2) - g' ≫ J.cocomplex.d (n + 1) (n + 2))
    (d_comp_homotopyZeroSucc_aux J φ n g g' w)

/-- The differential `K.d (n + 2) (n + 3)` followed by `homotopyZeroSucc ι J φ n g g' w` is
`φ.f (n + 2) - g' ≫ J.cocomplex.d (n + 1) (n + 2)`. -/
@[reassoc (attr := simp)]
lemma d_comp_homotopyZeroSucc (φ : K ⟶ J.cocomplex) (n : ℕ)
    (g : K.X (n + 1) ⟶ J.cocomplex.X n) (g' : K.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : φ.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    K.d (n + 2) (n + 3) ≫ homotopyZeroSucc ι J φ n g g' w =
      φ.f (n + 2) - g' ≫ J.cocomplex.d (n + 1) (n + 2) :=
  (exact_succ ι (n + 1)).comp_descToInjective _ _

/-- A comparison killing the augmentation is homotopic to zero. -/
noncomputable def homotopyZero (φ : K ⟶ J.cocomplex) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    Homotopy φ 0 :=
  Homotopy.mkCoinductive _ (homotopyZeroZero ι J φ comm) (by simp)
    (homotopyZeroOne ι J φ comm) (by simp) (fun n ⟨g, g', w⟩ =>
      ⟨homotopyZeroSucc ι J φ n g g' (by simp only [w, add_comm]), by simp⟩)

omit [QuasiIso ι] in
/-- If `φ` and `φ'` agree after the augmentation, then `φ - φ'` vanishes after it. -/
lemma f_zero_comp_sub_f_zero (φ φ' : K ⟶ J.cocomplex)
    (h : ι.f 0 ≫ φ.f 0 = ι.f 0 ≫ φ'.f 0) : ι.f 0 ≫ (φ - φ').f 0 = 0 := by
  rw [HomologicalComplex.sub_f_apply, Preadditive.comp_sub, h, sub_self]

/-- **Two comparisons agreeing on the augmentation are homotopic.** -/
noncomputable def homotopy (φ φ' : K ⟶ J.cocomplex)
    (h : ι.f 0 ≫ φ.f 0 = ι.f 0 ≫ φ'.f 0) : Homotopy φ φ' :=
  Homotopy.equivSubZero.invFun
    (homotopyZero ι J (φ - φ') (f_zero_comp_sub_f_zero ι J φ φ' h))

/-- **Two comparisons agreeing on the augmentation induce the same map on the homology of any
additive functor applied termwise.** -/
lemma homologyMap_map_eq {E : Type*} [Category* E] [Abelian E] (T : C ⥤ E) [T.Additive]
    (φ φ' : K ⟶ J.cocomplex) (h : ι.f 0 ≫ φ.f 0 = ι.f 0 ≫ φ'.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n =
      HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ') n :=
  (T.mapHomotopy (homotopy ι J φ φ' h)).homologyMap_eq n

end Homotopy

end Stacks.ResolutionDesc

end
