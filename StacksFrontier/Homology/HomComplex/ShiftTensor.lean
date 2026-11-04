module

public import Mathlib.Algebra.Homology.BifunctorShift
public import StacksFrontier.Homology.HomComplex.KoszulBraiding

/-!
# Shifts of tensor products of cochain complexes

Let `R` be a commutative ring, let `M` and `N` be cochain complexes of `R`-modules and let `a`
and `b` be integers. Shifting `M` by `a` and `N` by `b` simultaneously identifies the tensor
product of the shifts with the shift of the tensor product by `a + b`. On the homogeneous summand
`M^p ⊗ N^q` the identification is the evident reindexing multiplied by the Koszul sign
`(-1)^(p*b)`, the sign incurred by moving the shift of the second factor past the first factor.
Transporting the identification back to an unshifted source turns it into a morphism
`M ⊗ N ⟶ (M[a] ⊗ N[b])[-a - b]`.

## Main definitions

* `CochainComplex.HomComplex.tensorShiftIso` ([stacks 0FNH]): the canonical simultaneous-shift
  isomorphism `(M ⊗ N)[a + b] ≅ M[a] ⊗ N[b]`.
* `CochainComplex.HomComplex.tensorShiftHom` ([stacks 0FNH]): the corresponding morphism
  `M ⊗ N ⟶ (M[a] ⊗ N[b])[-a - b]` with unshifted source.

## Main results

* `CochainComplex.HomComplex.tensorShiftIso_hom_ι_and_naturality` ([stacks 0FNH]): the
  homogeneous sign formula for `tensorShiftIso`, namely that on the summand `M^p ⊗ N^q` it is
  `(-1)^(p*b)` times the evident reindexing, together with its naturality in both complexes.

## Implementation notes

The monoidal structure on `CochainComplex (ModuleCat R) ℤ` is the total complex of the degreewise
tensor product, the one whose Koszul commutativity constraint is supplied by
`StacksFrontier.Homology.HomComplex.KoszulBraiding`; the braiding itself plays no role here, only
the underlying monoidal structure and the Koszul sign convention it fixes.

The isomorphism is defined as the inverse of the composite which first removes the shift from the
first factor, without a sign, then removes the shift from the second factor, with its Koszul
sign, and finally recombines the two shifts into a single shift by `a + b`. Performing the two
removals in this order is what leaves the *source* degree `p` in the exponent `p * b`; the
opposite order would produce the exponent in the shifted degree.

Naturality is proved by splitting `f ⊗ g` as `(f ⊗ 1) ≫ (1 ⊗ g)` on both sides and moving each
factor through the two one-sided shift isomorphisms separately. The private lemmas below are the
four resulting one-sided naturality statements for the inverses of
`CochainComplex.mapBifunctorShift₁Iso` and `CochainComplex.mapBifunctorShift₂Iso`, plus the
image of one of them under a further shift.

Mathlib's monoidal structure on `ModuleCat R` requires the module universe to agree with the
universe of `R`, so everything here is stated for `ModuleCat.{u} R` with `R : Type u`.

## References

* [The Stacks Project, Tag 0FNH](https://stacks.math.columbia.edu/tag/0FNH)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace CochainComplex.HomComplex

section ShiftTensor

variable {R : Type u} [CommRing R]

/-- **Stacks 0FNH.** The canonical isomorphism from the shift by `a + b` of the tensor product
`M ⊗ N` to the tensor product `M[a] ⊗ N[b]` of the shifts.

It is the inverse of the composite that removes the shift from the first factor, then from the
second factor, and finally recombines the two shifts; see
`CochainComplex.HomComplex.tensorShiftIso_hom_ι_and_naturality` for the homogeneous formula that
pins it down. -/
@[stacks 0FNH "canonical isomorphism"]
noncomputable def tensorShiftIso (M N : CochainComplex (ModuleCat R) ℤ) (a b : ℤ) :
    (M ⊗ N)⟦a + b⟧ ≅ M⟦a⟧ ⊗ N⟦b⟧ :=
  (CochainComplex.mapBifunctorShift₁Iso M (N⟦b⟧)
      (curriedTensor (ModuleCat R)) a ≪≫
    (CategoryTheory.shiftFunctor _ a).mapIso
      (CochainComplex.mapBifunctorShift₂Iso M N (curriedTensor (ModuleCat R)) b) ≪≫
    (CategoryTheory.shiftFunctorAdd' (CochainComplex (ModuleCat R) ℤ) b a (a + b)
      (by omega)).symm.app (M ⊗ N)).symm

/-- **Stacks 0FNH.** The morphism corresponding to
`CochainComplex.HomComplex.tensorShiftIso`: its source is the unshifted tensor product and its
target is the tensor product of the shifts, shifted back by `-a - b`. -/
@[stacks 0FNH "corresponding shifted map"]
noncomputable def tensorShiftHom (M N : CochainComplex (ModuleCat R) ℤ) (a b : ℤ) :
    M ⊗ N ⟶ (M⟦a⟧ ⊗ N⟦b⟧)⟦-a - b⟧ :=
  (CategoryTheory.shiftFunctorCompIsoId (CochainComplex (ModuleCat R) ℤ) (a + b) (-a - b)
      (by omega)).inv.app (M ⊗ N) ≫
    (tensorShiftIso M N a b).hom⟦-a - b⟧'

/-- Removing the shift from the first factor is natural in the first factor. -/
@[reassoc]
private lemma shift₁Iso_inv_naturality {K L : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ L) (T : CochainComplex (ModuleCat R) ℤ) (x : ℤ) :
    (HomologicalComplex.tensorHom f (𝟙 T))⟦x⟧' ≫
        (CochainComplex.mapBifunctorShift₁Iso L T
          (curriedTensor (ModuleCat R)) x).inv =
      (CochainComplex.mapBifunctorShift₁Iso K T
          (curriedTensor (ModuleCat R)) x).inv ≫
        HomologicalComplex.tensorHom (f⟦x⟧') (𝟙 T) := by
  rw [← cancel_mono (CochainComplex.mapBifunctorShift₁Iso L T
    (curriedTensor (ModuleCat R)) x).hom]
  simp [Category.assoc, CochainComplex.mapBifunctorShift₁Iso_hom_naturality₁]

/-- Removing the shift from the first factor is natural in the second factor. -/
@[reassoc]
private lemma shift₁Iso_inv_naturality₂ (K : CochainComplex (ModuleCat R) ℤ)
    {T U : CochainComplex (ModuleCat R) ℤ} (g : T ⟶ U) (x : ℤ) :
    (HomologicalComplex.tensorHom (𝟙 K) g)⟦x⟧' ≫
        (CochainComplex.mapBifunctorShift₁Iso K U
          (curriedTensor (ModuleCat R)) x).inv =
      (CochainComplex.mapBifunctorShift₁Iso K T
          (curriedTensor (ModuleCat R)) x).inv ≫
        HomologicalComplex.tensorHom (𝟙 (K⟦x⟧)) g := by
  have hn :
      (CochainComplex.mapBifunctorShift₁Iso K T
          (curriedTensor (ModuleCat R)) x).hom ≫
        (HomologicalComplex.tensorHom (𝟙 K) g)⟦x⟧' =
      HomologicalComplex.tensorHom (𝟙 (K⟦x⟧)) g ≫
        (CochainComplex.mapBifunctorShift₁Iso K U
          (curriedTensor (ModuleCat R)) x).hom := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    simp only [HomologicalComplex.comp_f]
    rw [← Category.assoc,
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _
        (p + x) (n + x) rfl rfl]
    simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.id_f]
    conv_rhs =>
      rw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _
        (p + x) (n + x) rfl rfl]
    simp
  rw [← cancel_epi (CochainComplex.mapBifunctorShift₁Iso K T
    (curriedTensor (ModuleCat R)) x).hom, ← Category.assoc, hn]
  simp

/-- Removing the shift from the second factor is natural in the second factor. -/
@[reassoc]
private lemma shift₂Iso_inv_naturality (K : CochainComplex (ModuleCat R) ℤ)
    {T U : CochainComplex (ModuleCat R) ℤ} (g : T ⟶ U) (y : ℤ) :
    (HomologicalComplex.tensorHom (𝟙 K) g)⟦y⟧' ≫
        (CochainComplex.mapBifunctorShift₂Iso K U
          (curriedTensor (ModuleCat R)) y).inv =
      (CochainComplex.mapBifunctorShift₂Iso K T
          (curriedTensor (ModuleCat R)) y).inv ≫
        HomologicalComplex.tensorHom (𝟙 K) (g⟦y⟧') := by
  rw [← cancel_mono (CochainComplex.mapBifunctorShift₂Iso K U
    (curriedTensor (ModuleCat R)) y).hom]
  simp [Category.assoc, CochainComplex.mapBifunctorShift₂Iso_hom_naturality₂]

/-- Removing the shift from the second factor is natural in the first factor. -/
@[reassoc]
private lemma shift₂Iso_inv_naturality₁ {K L : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ L) (T : CochainComplex (ModuleCat R) ℤ) (y : ℤ) :
    (HomologicalComplex.tensorHom f (𝟙 T))⟦y⟧' ≫
        (CochainComplex.mapBifunctorShift₂Iso L T
          (curriedTensor (ModuleCat R)) y).inv =
      (CochainComplex.mapBifunctorShift₂Iso K T
          (curriedTensor (ModuleCat R)) y).inv ≫
        HomologicalComplex.tensorHom f (𝟙 (T⟦y⟧)) := by
  have hn :
      (CochainComplex.mapBifunctorShift₂Iso K T
          (curriedTensor (ModuleCat R)) y).hom ≫
        (HomologicalComplex.tensorHom f (𝟙 T))⟦y⟧' =
      HomologicalComplex.tensorHom f (𝟙 (T⟦y⟧)) ≫
        (CochainComplex.mapBifunctorShift₂Iso L T
          (curriedTensor (ModuleCat R)) y).hom := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    simp only [HomologicalComplex.comp_f]
    rw [← Category.assoc,
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _
        (q + y) (n + y) rfl rfl]
    simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.id_f]
    conv_rhs =>
      rw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _
          (q + y) (n + y) rfl rfl]
    simp
  rw [← cancel_epi (CochainComplex.mapBifunctorShift₂Iso K T
    (curriedTensor (ModuleCat R)) y).hom, ← Category.assoc, hn]
  simp

/-- The image under a further shift of the naturality in the first factor of removing the shift
from the second factor. -/
@[reassoc]
private lemma shift_map_shift₂Iso_inv_naturality₁
    {K L : CochainComplex (ModuleCat R) ℤ} (f : K ⟶ L)
    (T : CochainComplex (ModuleCat R) ℤ) (x y : ℤ) :
    (CategoryTheory.shiftFunctor _ x).map
        ((HomologicalComplex.tensorHom f (𝟙 T))⟦y⟧') ≫
        (CategoryTheory.shiftFunctor _ x).map
          (CochainComplex.mapBifunctorShift₂Iso L T
            (curriedTensor (ModuleCat R)) y).inv =
      (CategoryTheory.shiftFunctor _ x).map
          (CochainComplex.mapBifunctorShift₂Iso K T
            (curriedTensor (ModuleCat R)) y).inv ≫
        (CategoryTheory.shiftFunctor _ x).map
          (HomologicalComplex.tensorHom f (𝟙 (T⟦y⟧))) := by
  rw [← Functor.map_comp, shift₂Iso_inv_naturality₁, Functor.map_comp]

/-- A tensor product of morphisms of complexes factors into its two one-sided parts. -/
private lemma tensorHom_eq_tensorHom_id_comp {K L K' L' : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    HomologicalComplex.tensorHom f g =
      HomologicalComplex.tensorHom f (𝟙 L) ≫ HomologicalComplex.tensorHom (𝟙 K') g := by
  change f ⊗ₘ g = (f ⊗ₘ 𝟙 L) ≫ (𝟙 K' ⊗ₘ g)
  rw [MonoidalCategory.tensorHom_comp_tensorHom]
  simp

/-- **Stacks 0FNH.** On the summand `M^p ⊗ N^q`, the simultaneous-shift isomorphism
`CochainComplex.HomComplex.tensorShiftIso` is multiplication by the Koszul sign `(-1)^(p*b)`
followed by the canonical inclusion of `M[a]^{p-a} ⊗ N[b]^{q-b}` into the shifted total complex.
Since the homogeneous summands generate, this determines the isomorphism. It is moreover natural
in both complexes. -/
@[stacks 0FNH "homogeneous sign formula and naturality"]
theorem tensorShiftIso_hom_ι_and_naturality
    (M N : CochainComplex (ModuleCat R) ℤ) (a b : ℤ) :
    (∀ (p q : ℤ),
      HomologicalComplex.ιTensorObj M N p q (p + q) rfl ≫
          (CochainComplex.shiftFunctorObjXIso (M ⊗ N) (a + b)
            (p + q - a - b) (p + q) (by omega)).inv ≫
          (tensorShiftIso M N a b).hom.f (p + q - a - b) =
        ((p * b).negOnePow : ℤˣ) •
          ((CochainComplex.shiftFunctorObjXIso M a (p - a) p (by omega)).inv ⊗ₘ
              (CochainComplex.shiftFunctorObjXIso N b (q - b) q (by omega)).inv) ≫
            HomologicalComplex.ιTensorObj (M⟦a⟧) (N⟦b⟧)
              (p - a) (q - b) (p + q - a - b) (by omega)) ∧
      (∀ (M' N' : CochainComplex (ModuleCat R) ℤ) (f : M ⟶ M') (g : N ⟶ N'),
        (HomologicalComplex.tensorHom f g)⟦a + b⟧' ≫
            (tensorShiftIso M' N' a b).hom =
          (tensorShiftIso M N a b).hom ≫
            HomologicalComplex.tensorHom (f⟦a⟧') (g⟦b⟧')) := by
  constructor
  · intro p q
    have hp : p - a + a = p := by omega
    have hq : q - b + b = q := by omega
    have hpq : p + q - a - b + a + b = p + q := by omega
    rw [← cancel_mono ((tensorShiftIso M N a b).inv.f (p + q - a - b))]
    simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
      HomologicalComplex.id_f]
    dsimp [tensorShiftIso]
    simp [
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc,
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc,
      CochainComplex.shiftFunctorAdd'_inv_app_f',
      MonoidalCategory.tensorHom_def, smul_smul,
      HomologicalComplex.XIsoOfEq, eqToHom_map,
      hp, hq, hpq]
  · intro M' N' f g
    dsimp [tensorShiftIso]
    rw [← Category.assoc, ← Category.assoc]
    erw [(CategoryTheory.shiftFunctorAdd' (CochainComplex (ModuleCat R) ℤ) b a (a + b)
      (by omega)).hom.naturality]
    rw [tensorHom_eq_tensorHom_id_comp f g, tensorHom_eq_tensorHom_id_comp (f⟦a⟧') (g⟦b⟧')]
    simp only [Functor.map_comp, Category.assoc]
    erw [cancel_epi]
    slice_lhs 2 3 =>
      change (CategoryTheory.shiftFunctor _ a).map
          ((HomologicalComplex.tensorHom (𝟙 M') g)⟦b⟧') ≫
        (CategoryTheory.shiftFunctor _ a).map
          (CochainComplex.mapBifunctorShift₂Iso M' N'
            (curriedTensor (ModuleCat R)) b).inv
      rw [← Functor.map_comp, shift₂Iso_inv_naturality, Functor.map_comp]
    rw [Category.assoc]
    slice_lhs 3 4 =>
      change (HomologicalComplex.tensorHom (𝟙 M') (g⟦b⟧'))⟦a⟧' ≫
        (CochainComplex.mapBifunctorShift₁Iso M' (N'⟦b⟧)
          (curriedTensor (ModuleCat R)) a).inv
      rw [shift₁Iso_inv_naturality₂]
    slice_lhs 1 2 =>
      change (CategoryTheory.shiftFunctor _ a).map
          ((HomologicalComplex.tensorHom f (𝟙 N))⟦b⟧') ≫
        (CategoryTheory.shiftFunctor _ a).map
          (CochainComplex.mapBifunctorShift₂Iso M' N
            (curriedTensor (ModuleCat R)) b).inv
      rw [shift_map_shift₂Iso_inv_naturality₁]
    slice_lhs 2 3 =>
      change (HomologicalComplex.tensorHom f (𝟙 (N⟦b⟧)))⟦a⟧' ≫
        (CochainComplex.mapBifunctorShift₁Iso M' (N⟦b⟧)
          (curriedTensor (ModuleCat R)) a).inv
      rw [shift₁Iso_inv_naturality]
    simp only [Category.assoc]

end ShiftTensor

end CochainComplex.HomComplex

end
