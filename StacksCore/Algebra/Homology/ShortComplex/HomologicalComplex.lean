module

public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import StacksCore.Tactic.StacksAttribute

/-! ## Homological Complex

This file also carries part 2 of Stacks tags 010Z and 0115, the definition of an *acyclic*
complex. Mathlib defines `HomologicalComplex.Acyclic` as exactness in every degree, so the tag
goes on that definition, and `acyclic_iff_isZero_homology` identifies it with the vanishing of
every homology object, which is how the Stacks project words it. Part 1 of those tags, the
quasi-isomorphisms, is in `StacksCore.Algebra.Homology.QuasiIso`, mirroring where Mathlib puts each.
-/

@[expose] public section

open CategoryTheory Limits

add_to_stacks 010E HomologicalComplex.ExactAt

add_to_stacks 010Z "(2), the definition" HomologicalComplex.Acyclic

add_to_stacks 0115 "(2), the definition; `Acyclic` is stated for an arbitrary `ComplexShape`, so
the chain- and cochain-complex tags are the same declaration."
  HomologicalComplex.Acyclic

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}

/-- **Stacks 010Z (2) and 0115 (2).** A complex is acyclic exactly when all of its homology
objects vanish. -/
@[stacks 010Z "(2), identified with the Stacks wording",
  stacks 0115 "(2), identified with the Stacks wording"]
lemma acyclic_iff_isZero_homology (K : HomologicalComplex C c) [∀ i, K.HasHomology i] :
    K.Acyclic ↔ ∀ i, IsZero (K.homology i) :=
  (acyclic_iff K).trans (forall_congr' fun i ↦ exactAt_iff_isZero_homology K i)

end HomologicalComplex

/-! ### The homology of a complex as the subquotient `Ker d/Im d`

For a homological complex `K` and `i, j, k` with `c.prev j = i` and `c.next j = k`, Mathlib's
homology `K.homology j` is defined through `ShortComplex.homology`; this section identifies it
with the subquotient `Ker(d_{j,k})/Im(d_{i,j})` of `K.X j` in the language of `Subobject`:
`kernelSubobjectIsoCycles : Ker(d_{j,k}) ≅ K.cycles j` (compatible with the inclusions into
`K.X j`), `homologyIsCokernelOfLE` (the map `Ker(d_{j,k}) ≅ Z_j ⟶ H_j` is a cokernel of the
inclusion `Im ⊆ Ker`) and `homologyIsoCokernelOfLE : K.homology j ≅ cokernel (ofLE Im Ker _)` with
the compatibility `π_homologyIsoCokernelOfLE_inv`. The inclusion `Im ⊆ Ker` is `Subobject.ofLE` in
the statements used by `rw`, and Mathlib's `imageToKernel` (its `simp` normal form) in the `simp`
lemmas. The kernel part needs only zero morphisms and the
kernel; the image part is stated in an abelian category. Used for the towers of Stacks 011N
(`StacksCore.Algebra.Homology.SpectralSequence.Tower`). -/

namespace HomologicalComplex

open Subobject

section Kernel

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  (K : HomologicalComplex C c) (j k : ι) (hk : c.next j = k) [K.HasHomology j]
  [HasKernel (K.d j k)]

/-- `Ker(d_{j,k}) ≅ Z_j`: the kernel subobject of the differential out of `j` is the object of
cycles, when `c.next j = k`. -/
noncomputable def kernelSubobjectIsoCycles : (kernelSubobject (K.d j k) : C) ≅ K.cycles j :=
  kernelSubobjectIso (K.d j k) ≪≫
    IsLimit.conePointUniqueUpToIso (kernelIsKernel (K.d j k)) (K.cyclesIsKernel j k hk)

/-- `Ker(d_{j,k}) ≅ Z_j` is compatible with the inclusions into `X_j`. -/
@[reassoc (attr := simp)]
lemma kernelSubobjectIsoCycles_hom_iCycles :
    (K.kernelSubobjectIsoCycles j k hk).hom ≫ K.iCycles j = (kernelSubobject (K.d j k)).arrow := by
  have h := IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel (K.d j k))
    (K.cyclesIsKernel j k hk) WalkingParallelPair.zero
  simp only [Fork.app_zero_eq_ι, Fork.ι_ofι] at h
  rw [kernelSubobjectIsoCycles, Iso.trans_hom, Category.assoc, h, kernelSubobject_arrow]

/-- `Z_j ≅ Ker(d_{j,k})` is compatible with the inclusions into `X_j`. -/
@[reassoc (attr := simp)]
lemma kernelSubobjectIsoCycles_inv_arrow :
    (K.kernelSubobjectIsoCycles j k hk).inv ≫ (kernelSubobject (K.d j k)).arrow = K.iCycles j := by
  rw [← kernelSubobjectIsoCycles_hom_iCycles K j k hk, Iso.inv_hom_id_assoc]

end Kernel

section Image

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  (K : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)

/-- `X_i ↠ Im(d_{i,j}) ⊆ Ker(d_{j,k}) ≅ Z_j` is the map `X_i ⟶ Z_j` induced by `d_{i,j}`, with the
inclusion `Im ⊆ Ker` spelled as `imageToKernel`, its `simp` normal form. -/
@[reassoc (attr := simp)]
lemma factorThruImageSubobject_imageToKernel_kernelSubobjectIsoCycles_hom :
    factorThruImageSubobject (K.d i j) ≫ imageToKernel (K.d i j) (K.d j k) (K.d_comp_d i j k) ≫
      (K.kernelSubobjectIsoCycles j k hk).hom = K.toCycles i j := by
  rw [← cancel_mono (K.iCycles j)]
  simp

/-- `factorThruImageSubobject_imageToKernel_kernelSubobjectIsoCycles_hom` with the inclusion
`Im ⊆ Ker` spelled as `Subobject.ofLE`, for `rw` (`simp` rewrites `ofLE` to `imageToKernel` first,
by `subobject_ofLE_as_imageToKernel`). -/
@[reassoc]
lemma factorThruImageSubobject_ofLE_kernelSubobjectIsoCycles_hom :
    factorThruImageSubobject (K.d i j) ≫ ofLE _ _ (image_le_kernel _ _ (K.d_comp_d i j k)) ≫
      (K.kernelSubobjectIsoCycles j k hk).hom = K.toCycles i j :=
  K.factorThruImageSubobject_imageToKernel_kernelSubobjectIsoCycles_hom i j k hk

/-- The homology `H_j` is the subquotient `Ker(d_{j,k})/Im(d_{i,j})` of `X_j`:
`Ker(d_{j,k}) ≅ Z_j ⟶ H_j` is a cokernel of `Im(d_{i,j}) ⊆ Ker(d_{j,k})`, when `c.prev j = i` and
`c.next j = k`. -/
noncomputable def homologyIsCokernelOfLE :
    IsColimit (CokernelCofork.ofπ (f := ofLE _ _ (image_le_kernel _ _ (K.d_comp_d i j k)))
      ((K.kernelSubobjectIsoCycles j k hk).hom ≫ K.homologyπ j) (by
        rw [← cancel_epi (factorThruImageSubobject (K.d i j)), comp_zero,
          factorThruImageSubobject_ofLE_kernelSubobjectIsoCycles_hom_assoc,
          toCycles_comp_homologyπ])) := by
  have hw {Z' : C} (g' : (kernelSubobject (K.d j k) : C) ⟶ Z')
      (hg' : ofLE _ _ (image_le_kernel _ _ (K.d_comp_d i j k)) ≫ g' = 0) :
      K.toCycles i j ≫ (K.kernelSubobjectIsoCycles j k hk).inv ≫ g' = 0 := by
    rw [← factorThruImageSubobject_ofLE_kernelSubobjectIsoCycles_hom K i j k hk,
      Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, hg', comp_zero]
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {Z'} g' hg' => (K.homologyIsCokernel i j hi).desc (CokernelCofork.ofπ _ (hw g' hg')))
    (fun {Z'} g' hg' => ?_) (fun {Z'} g' hg' m hm => ?_)
  · have h := Cofork.IsColimit.π_desc (K.homologyIsCokernel i j hi)
      (t := CokernelCofork.ofπ _ (hw g' hg'))
    rw [CokernelCofork.π_ofπ, CokernelCofork.π_ofπ] at h
    rw [Category.assoc, h, Iso.hom_inv_id_assoc]
  · refine Cofork.IsColimit.hom_ext (K.homologyIsCokernel i j hi) ?_
    rw [Cofork.IsColimit.π_desc]
    simp [← hm]

/-- The homology `H_j` as the subquotient `Ker(d_{j,k})/Im(d_{i,j})` of `X_j`, when
`c.prev j = i` and `c.next j = k`. -/
noncomputable def homologyIsoCokernelOfLE :
    K.homology j ≅ cokernel (ofLE _ _ (image_le_kernel _ _ (K.d_comp_d i j k))) :=
  ((cokernelIsCokernel _).coconePointUniqueUpToIso (K.homologyIsCokernelOfLE i j k hi hk)).symm

/-- The quotient map `Ker(d_{j,k}) ⟶ Ker/Im ≅ H_j` is `Ker(d_{j,k}) ≅ Z_j ⟶ H_j`; for `rw`, see
`π_imageToKernel_homologyIsoCokernelOfLE_inv` for the `simp` normal form. -/
@[reassoc]
lemma π_homologyIsoCokernelOfLE_inv :
    cokernel.π _ ≫ (K.homologyIsoCokernelOfLE i j k hi hk).inv =
      (K.kernelSubobjectIsoCycles j k hk).hom ≫ K.homologyπ j :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (K.homologyIsCokernelOfLE i j k hi hk) WalkingParallelPair.one

/-- `π_homologyIsoCokernelOfLE_inv` with the inclusion `Im ⊆ Ker` spelled as `imageToKernel`, its
`simp` normal form. No `reassoc`: the `_assoc` form is `simp`-provable from this one, and its
statement is type-correct only at default transparency (`imageToKernel` unfolds to `ofLE`). -/
@[simp]
lemma π_imageToKernel_homologyIsoCokernelOfLE_inv :
    cokernel.π (imageToKernel (K.d i j) (K.d j k) (K.d_comp_d i j k)) ≫
      (K.homologyIsoCokernelOfLE i j k hi hk).inv =
      (K.kernelSubobjectIsoCycles j k hk).hom ≫ K.homologyπ j :=
  K.π_homologyIsoCokernelOfLE_inv i j k hi hk

/-- `Ker(d_{j,k}) ≅ Z_j ⟶ H_j ≅ Ker/Im` is the quotient map. -/
@[reassoc (attr := simp)]
lemma kernelSubobjectIsoCycles_hom_homologyπ_homologyIsoCokernelOfLE_hom :
    (K.kernelSubobjectIsoCycles j k hk).hom ≫ K.homologyπ j ≫
      (K.homologyIsoCokernelOfLE i j k hi hk).hom = cokernel.π _ := by
  rw [← Category.assoc, ← π_homologyIsoCokernelOfLE_inv K i j k hi hk, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end Image

end HomologicalComplex
