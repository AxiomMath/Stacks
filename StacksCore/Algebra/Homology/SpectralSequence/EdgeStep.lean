module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Edge maps of a spectral sequence

Port of `Mathlib/Algebra/Homology/SpectralSequence/EdgeStep.lean` from mathlib#25848 (Joël Riou,
head 2f4d873c95, not yet merged; Copyright (c) 2025 Joël Riou, released under the Apache 2.0
license); delete when the pin includes it. Names, statements and namespace are upstream's;
proofs may differ (the upstream `set_option` workarounds are not used).
**Everything in this file is temporary and is expected to be deleted** when the pin includes
mathlib#25848.

For a spectral sequence `E : SpectralSequence C c r₀` (Mathlib, any index type, shape family and
starting page) and a position `pq` on the page `r`, `E.HasEdgeMonoAt pq r` says that every
differential into `pq` on the page `r` vanishes; then `E_{r+1}^{pq}` is the kernel of the
differential out of `pq`, and `E.edgeMonoStep pq r r' : E_{r'}^{pq} ⟶ E_r^{pq}` (`r' = r + 1`) is
the corresponding monomorphism (`edgeMonoStepShortComplex_exact`: `E_{r+1} → E_r → E_r^{next}` is
exact). Dually `E.HasEdgeEpiAt pq r` and `E.edgeEpiStep pq r r' : E_r^{pq} ⟶ E_{r'}^{pq}`
(`edgeEpiStepShortComplex_exact`: `E_r^{prev} → E_r → E_{r+1}` is exact); when both hold the two
maps are inverse isomorphisms (`edgeMonoStep_edgeEpiStep`, `edgeEpiStep_edgeMonoStep`).
`hasEdgeMonoSet`/`hasEdgeEpiSet` collect the pages from which all differentials into/out of `pq`
vanish (the input of `HasPageInfinityAt` in `PageInfinity`), and `isIso_hom_of_GE` says that a
morphism of spectral sequences which is an isomorphism on one page is one on every later page.

Everything in upstream's file is ported, including the four `*HomologyData*_compatibility`
lemmas. Upstream's six `set_option backward.isDefEq.respectTransparency false in` are avoided:
the two `_exact` lemmas go through `HomologicalComplex.cyclesIsKernel`/`opcyclesIsCokernel`
(stated with `K.d`, so that no `subst` is needed and both forks have the same shape), and the
compatibility lemmas cross the `sc'`/`K` boundary once, through an explicit expression of
`left.i`/`right.p` in terms of `cyclesIsoSc'`/`opcyclesIsoSc'`. Upstream's `isIso_hom_succ`
carries a `change`-based `have` ("this should already be an instance"); at the pin it is an
instance (`IsIso (homologyMap φ i)`), so the `have` is dropped.

Two of the compatibility lemmas (`leftHomologyData_π_edgeMonoStep_compatibility`,
`rightHomologyData_ι_edgeEpiStep_compatibility`) are used by upstream's spectral objects
(`Mathlib/Algebra/Homology/SpectralObject/PageInfinity.lean` of the same pull request), the
route planned for Stacks §12.24–12.25; that is why the whole file is ported. One attribute
differs from upstream: `rightHomologyData_p_edgeMonoStep_compatibility` and
`leftHomologyData_i_edgeEpiStep_compatibility` carry `@[simp]` instead of
`@[reassoc (attr := simp)]`. Their left-hand sides `edgeMonoStep ≫ right.p`, `left.i ≫ edgeEpiStep`
compose across the defeq boundary `(sc' …).X₂ ≡ (E.page r _).X pq'` (unfolding `sc'`), so
without upstream's `set_option backward.isDefEq.respectTransparency false` `reassoc` cannot
re-associate them: the generated `_assoc` variants stay left-associated (never match a goal)
and the `simpNF` linter rejects them as `simp`-provable. The statements are upstream's.

In the language of the towers `B_r ⊆ Z_r ⊆ E_{r₀}` of Stacks 011N
(`StacksCore.Algebra.Homology.SpectralSequence.Tower`), `HasEdgeMonoAt pq r` gives `B_{r+1} = B_r`
and `edgeMonoStep` is `Z_{r+1}/B_r ⊆ Z_r/B_r`; `HasEdgeEpiAt pq r` gives `Z_{r+1} = Z_r` and
`edgeEpiStep` is `Z_r/B_r ↠ Z_r/B_{r+1}`.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] [Abelian C]
  {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

variable (E E' : SpectralSequence C c r₀)

/-- This means that the differential to an object E_r^{p,q} is zero (both r and (p,q) fixed) -/
class HasEdgeMonoAt (pq : ι) (r : ℤ) : Prop where
  /-- the page `r` exists -/
  le : r₀ ≤ r := by lia
  /-- every differential into `pq` on the page `r` vanishes -/
  zero (pq' : ι) : (E.page r).d pq' pq = 0

/-- The page `r` exists when `E.HasEdgeMonoAt pq r`. -/
lemma le₀_of_hasEdgeMonoAt (pq : ι) (r : ℤ) [E.HasEdgeMonoAt pq r] :
    r₀ ≤ r :=
  HasEdgeMonoAt.le (E := E) (pq := pq)

/-- The differentials into `pq` on the page `r` vanish when `E.HasEdgeMonoAt pq r`. -/
@[simp]
lemma d_eq_zero_of_hasEdgeMonoAt (pq' pq : ι) (r : ℤ) [E.HasEdgeMonoAt pq r] :
    (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).d pq' pq = 0 :=
  HasEdgeMonoAt.zero _

/-- The monomorphism `E_{r'}^{pq} ⟶ E_r^{pq}` (`r' = r + 1`) when the differentials into `pq`
on the page `r` vanish: `E_{r'}^{pq} ≅ H_r^{pq} ≅ Z_r^{pq} ⟶ E_r^{pq}`. -/
noncomputable def edgeMonoStep (pq : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hrr' : r + 1 = r' := by lia) :
  (E.page r' (by have := E.le₀_of_hasEdgeMonoAt pq r; lia)).X pq ⟶
    (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).X pq :=
  (E.iso r r' pq hrr' (E.le₀_of_hasEdgeMonoAt pq r)).inv ≫
    ((E.page r (E.le₀_of_hasEdgeMonoAt pq r)).isoHomologyπ _ pq rfl (by simp)).inv ≫
    (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).iCycles pq

/-- `E.edgeMonoStep pq r r'` is a monomorphism. -/
instance (pq : ι) (r r' : ℤ) (hrr' : r + 1 = r') [E.HasEdgeMonoAt pq r] :
    Mono (E.edgeMonoStep pq r r' hrr') := by
  dsimp [edgeMonoStep]
  infer_instance

/-- `E.edgeMonoStep pq r r'` followed by a differential out of `pq` vanishes. -/
@[reassoc (attr := simp)]
lemma edgeMonoStep_comp_d (pq pq' : ι) (r r' : ℤ)
    (hrr' : r + 1 = r' := by lia)
    [E.HasEdgeMonoAt pq r] :
    E.edgeMonoStep pq r r' hrr' ≫ (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).d pq pq' = 0 := by
  simp [edgeMonoStep]

/-- `E.edgeMonoStep pq r r'` composed with `E.iso r r' pq` is the inclusion of cycles. -/
@[reassoc (attr := simp)]
lemma iso_hom_comp_edgeMonoStep (pq : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hrr' : r + 1 = r' := by lia) :
    (E.iso r r' pq hrr' (E.le₀_of_hasEdgeMonoAt pq r)).hom ≫ E.edgeMonoStep pq r r' =
      ((E.page r (E.le₀_of_hasEdgeMonoAt pq r)).isoHomologyπ _ pq rfl (by simp)).inv ≫
        (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).iCycles pq := by
  simp [edgeMonoStep]

/-- The short complex `E_{r'}^{pq} ⟶ E_r^{pq} ⟶ E_r^{pq'}` (`r' = r + 1`) given by
`E.edgeMonoStep pq r r'` and the differential `d pq pq'` of the page `r`. -/
@[implicit_reducible, simps]
noncomputable def edgeMonoStepShortComplex (pq pq' : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hr' : r + 1 = r' := by lia) : ShortComplex C :=
  ShortComplex.mk _ _ (E.edgeMonoStep_comp_d pq pq' r r')

/-- The short complex `E_{r'}^{pq} ⟶ E_r^{pq} ⟶ E_r^{pq'}` is exact when `pq'` is the
target of the differential out of `pq`: `E_{r'}^{pq}` is the kernel of `d pq pq'`. -/
lemma edgeMonoStepShortComplex_exact (pq pq' : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hpq' : (c r).next pq = pq')
    (hrr' : r + 1 = r' := by lia) :
    (E.edgeMonoStepShortComplex pq pq' r r' hrr').Exact := by
  have : IsLimit (KernelFork.ofι (E.edgeMonoStep pq r r' hrr')
      (E.edgeMonoStep_comp_d pq pq' r r' hrr')) :=
    IsLimit.ofIsoLimit ((E.page r (E.le₀_of_hasEdgeMonoAt pq r)).cyclesIsKernel pq pq' hpq')
      (Fork.ext (((E.page r (E.le₀_of_hasEdgeMonoAt pq r)).isoHomologyπ _ pq rfl (by simp))
        ≪≫ E.iso r r' pq hrr' (E.le₀_of_hasEdgeMonoAt pq r)) (by simp))
  exact ShortComplex.exact_of_f_is_kernel _ this

/-- This means that the differential from an object E_r^{p,q} is zero (both r and (p,q) fixed) -/
class HasEdgeEpiAt (pq : ι) (r : ℤ) : Prop where
  /-- the page `r` exists -/
  le : r₀ ≤ r := by lia
  /-- every differential out of `pq` on the page `r` vanishes -/
  zero (pq' : ι) : (E.page r).d pq pq' = 0

/-- The page `r` exists when `E.HasEdgeEpiAt pq r`. -/
lemma le₀_of_hasEdgeEpiAt (pq : ι) (r : ℤ) [E.HasEdgeEpiAt pq r] :
    r₀ ≤ r :=
  HasEdgeEpiAt.le (E := E) (pq := pq)

/-- The differentials out of `pq` on the page `r` vanish when `E.HasEdgeEpiAt pq r`. -/
@[simp]
lemma d_eq_zero_of_hasEdgeEpiAt (pq pq' : ι) (r : ℤ) [E.HasEdgeEpiAt pq r] :
    (E.page r (E.le₀_of_hasEdgeEpiAt pq r)).d pq pq' = 0 :=
  HasEdgeEpiAt.zero _

/-- The epimorphism `E_r^{pq} ⟶ E_{r'}^{pq}` (`r' = r + 1`) when the differentials out of `pq`
on the page `r` vanish: `E_r^{pq} ⟶ E_r^{pq}/B_r^{pq} ≅ H_r^{pq} ≅ E_{r'}^{pq}`. -/
noncomputable def edgeEpiStep (pq : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r' := by lia) :
  (E.page r (E.le₀_of_hasEdgeEpiAt pq r)).X pq ⟶ (E.page r'
    (by have := E.le₀_of_hasEdgeEpiAt pq r; lia)).X pq :=
    (E.page r (E.le₀_of_hasEdgeEpiAt pq r)).pOpcycles pq ≫
      ((E.page r (E.le₀_of_hasEdgeEpiAt pq r) ).isoHomologyι pq _ rfl (by simp)).inv ≫
      (E.iso r r' pq hrr' (E.le₀_of_hasEdgeEpiAt pq r)).hom

/-- `E.edgeEpiStep pq r r'` is an epimorphism. -/
instance (pq : ι) (r r' : ℤ) (hrr' : r + 1 = r') [E.HasEdgeEpiAt pq r] :
    Epi (E.edgeEpiStep pq r r' hrr') := by
  dsimp [edgeEpiStep]
  infer_instance

/-- A differential into `pq'` followed by `E.edgeEpiStep pq' r r'` vanishes. -/
@[reassoc (attr := simp)]
lemma d_comp_edgeEpiStep (pq pq' : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq' r]
    (hrr' : r + 1 = r' := by lia) :
    (E.page r (E.le₀_of_hasEdgeEpiAt pq' r)).d pq pq' ≫ E.edgeEpiStep pq' r r' hrr' = 0 := by
  simp [edgeEpiStep]

/-- `E.edgeEpiStep pq r r'` composed with the inverse of `E.iso r r' pq` is the projection
to opcycles. -/
@[reassoc (attr := simp)]
lemma edgeEpiStep_comp_iso_inv (pq : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r' := by lia) :
    E.edgeEpiStep pq r r' hrr' ≫ (E.iso r r' pq hrr' (E.le₀_of_hasEdgeEpiAt pq r)).inv =
      (E.page r (E.le₀_of_hasEdgeEpiAt pq r)).pOpcycles pq ≫
        ((E.page r (E.le₀_of_hasEdgeEpiAt pq r)).isoHomologyι pq _ rfl (by simp)).inv := by
  simp [edgeEpiStep]

/-- The short complex `E_r^{pq} ⟶ E_r^{pq'} ⟶ E_{r'}^{pq'}` (`r' = r + 1`) given by the
differential `d pq pq'` of the page `r` and `E.edgeEpiStep pq' r r'`. -/
@[implicit_reducible, simps]
noncomputable def edgeEpiStepShortComplex (pq pq' : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq' r]
    (hrr' : r + 1 = r' := by lia) : ShortComplex C :=
  ShortComplex.mk _ _ (E.d_comp_edgeEpiStep pq pq' r r' hrr')

/-- The short complex `E_r^{pq} ⟶ E_r^{pq'} ⟶ E_{r'}^{pq'}` is exact when `pq` is the
source of the differential into `pq'`: `E_{r'}^{pq'}` is the cokernel of `d pq pq'`. -/
lemma edgeEpiStepShortComplex_exact (pq pq' : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq' r]
    (hpq' : (c r).prev pq' = pq) (hrr' : r + 1 = r' := by lia) :
    (E.edgeEpiStepShortComplex pq pq' r r' hrr').Exact := by
  have : IsColimit (CokernelCofork.ofπ (E.edgeEpiStep pq' r r' hrr')
      (E.d_comp_edgeEpiStep pq pq' r r' hrr')) :=
    IsColimit.ofIsoColimit
      ((E.page r (E.le₀_of_hasEdgeEpiAt pq' r)).opcyclesIsCokernel pq pq' hpq')
      (Cofork.ext (((E.page r (E.le₀_of_hasEdgeEpiAt pq' r)).isoHomologyι pq' _ rfl
        (by simp)).symm ≪≫ E.iso r r' pq' hrr' (E.le₀_of_hasEdgeEpiAt pq' r))
        (by simp [edgeEpiStep]))
  exact ShortComplex.exact_of_g_is_cokernel _ this

/-- `E.edgeMonoStep` followed by `E.edgeEpiStep` is the identity. -/
@[reassoc (attr := simp)]
lemma edgeMonoStep_edgeEpiStep (pq : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r] [E.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r' := by lia) :
        E.edgeMonoStep pq r r' hrr' ≫ E.edgeEpiStep pq r r' hrr' = 𝟙 _ := by
  simp [edgeMonoStep, edgeEpiStep, assoc,
    ← (E.page r (E.le₀_of_hasEdgeEpiAt pq r)).homology_π_ι_assoc pq,
    HomologicalComplex.isoHomologyι_hom_inv_id_assoc,
    HomologicalComplex.isoHomologyπ_inv_hom_id_assoc, Iso.inv_hom_id]

/-- `E.edgeEpiStep` followed by `E.edgeMonoStep` is the identity. -/
@[reassoc (attr := simp)]
lemma edgeEpiStep_edgeMonoStep (pq : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r] [E.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r' := by lia) :
    E.edgeEpiStep pq r r' hrr' ≫ E.edgeMonoStep pq r r' hrr' = 𝟙 _ := by
  have := E.le₀_of_hasEdgeEpiAt pq r
  simp [edgeEpiStep, edgeMonoStep,
    ← cancel_mono ((E.page r).isoHomologyπ _ pq rfl (by simp)).hom,
    ← cancel_mono ((E.page r).isoHomologyι pq _ rfl (by simp)).hom,
    ← cancel_mono ((E.page r).iCyclesIso pq _ rfl (by simp)).inv,
    HomologicalComplex.iCyclesIso_hom_inv_id, comp_id, id_comp,
    HomologicalComplex.isoHomologyπ_hom, HomologicalComplex.isoHomologyπ_inv_hom_id,
    HomologicalComplex.isoHomologyι_hom, HomologicalComplex.isoHomologyι_inv_hom_id,
    HomologicalComplex.homology_π_ι, HomologicalComplex.iCyclesIso_inv_hom_id_assoc,
    assoc, Iso.hom_inv_id_assoc]

section

variable (r r' : ℤ) (pq pq' pq'' : ι)
  (hpq : (c r).prev pq' = pq) (hpq'' : (c r).next pq' = pq'')
  {hr : r₀ ≤ r}
  (left : ((E.page r hr).sc' pq pq' pq'').LeftHomologyData)
  (right : ((E.page r hr).sc' pq pq' pq'').RightHomologyData)

/-- `left.i` factors through `cyclesIsoSc'` and the inclusion of cycles. -/
private lemma leftHomologyData_i_eq :
    left.i = left.cyclesIso.inv ≫
      ((E.page r hr).cyclesIsoSc' pq pq' pq'' hpq hpq'').inv ≫ (E.page r hr).iCycles pq' := by
  rw [HomologicalComplex.cyclesIsoSc'_inv_iCycles]
  exact left.cyclesIso_inv_comp_iCycles.symm

/-- `right.p` factors through the projection to opcycles and `opcyclesIsoSc'`. -/
private lemma rightHomologyData_p_eq :
    right.p = (E.page r hr).pOpcycles pq' ≫
      ((E.page r hr).opcyclesIsoSc' pq pq' pq'' hpq hpq'').hom ≫ right.opcyclesIso.hom := by
  rw [HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom_assoc]
  exact right.pOpcycles_comp_opcyclesIso_hom.symm

/-- Through a left homology data of `E_r^{pq} ⟶ E_r^{pq'} ⟶ E_r^{pq''}`, `E.edgeMonoStep`
is the inclusion of cycles. -/
@[reassoc]
lemma leftHomologyData_π_edgeMonoStep_compatibility [E.HasEdgeMonoAt pq' r]
    (hrr' : r + 1 = r' := by lia) :
    left.π ≫ left.homologyIso.inv ≫ ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').inv ≫
      (E.iso r r' pq' hrr').hom ≫ E.edgeMonoStep pq' r r' hrr' = left.i := by
  rw [E.leftHomologyData_i_eq r pq pq' pq'' hpq hpq'' left]
  simp [iso_hom_comp_edgeMonoStep,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv_assoc,
    HomologicalComplex.π_homologyIsoSc'_inv_assoc,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc]

/-- Through a right homology data of `E_r^{pq} ⟶ E_r^{pq'} ⟶ E_r^{pq''}`, `E.edgeMonoStep`
followed by the projection to opcycles is the inclusion of the homology. -/
@[simp]
lemma rightHomologyData_p_edgeMonoStep_compatibility [E.HasEdgeMonoAt pq' r]
    (hrr' : r + 1 = r' := by lia) :
      E.edgeMonoStep pq' r r' hrr' ≫ right.p =
       (E.iso r r' pq' hrr' hr).inv ≫ ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').hom ≫
       right.homologyIso.hom ≫ right.ι := by
  rw [E.rightHomologyData_p_eq r pq pq' pq'' hpq hpq'' right]
  simp only [edgeMonoStep, assoc, ShortComplex.RightHomologyData.homologyIso_hom_comp_ι,
    HomologicalComplex.homologyIsoSc'_hom_ι_assoc]
  rw [← HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.isoHomologyπ_inv_hom_id_assoc]

/-- Through a left homology data of `E_r^{pq} ⟶ E_r^{pq'} ⟶ E_r^{pq''}`, the inclusion of
cycles followed by `E.edgeEpiStep` is the projection to the homology. -/
@[simp]
lemma leftHomologyData_i_edgeEpiStep_compatibility [E.HasEdgeEpiAt pq' r]
    (hrr' : r + 1 = r' := by lia) :
    left.i ≫ E.edgeEpiStep pq' r r' hrr' =
      left.π ≫ left.homologyIso.inv ≫ ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').inv ≫
        (E.iso r r' pq' hrr' hr).hom := by
  calc left.i ≫ E.edgeEpiStep pq' r r' hrr'
      = (left.cyclesIso.inv ≫ ((E.page r hr).cyclesIsoSc' pq pq' pq'' hpq hpq'').inv ≫
          (E.page r hr).iCycles pq') ≫ E.edgeEpiStep pq' r r' hrr' :=
        eq_whisker (E.leftHomologyData_i_eq r pq pq' pq'' hpq hpq'' left) _
    _ = _ := by
      simp only [edgeEpiStep, assoc, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv_assoc,
        HomologicalComplex.π_homologyIsoSc'_inv_assoc]
      rw [← HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.isoHomologyι_hom_inv_id_assoc]

/-- Through a right homology data of `E_r^{pq} ⟶ E_r^{pq'} ⟶ E_r^{pq''}`, `E.edgeEpiStep`
is the projection to opcycles. -/
@[reassoc]
lemma rightHomologyData_ι_edgeEpiStep_compatibility [E.HasEdgeEpiAt pq' r]
      (hrr' : r + 1 = r' := by lia) :
    E.edgeEpiStep pq' r r' hrr' ≫ (E.iso r r' pq' hrr' hr).inv ≫
      ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').hom ≫
        right.homologyIso.hom ≫ right.ι = right.p := by
  rw [E.rightHomologyData_p_eq r pq pq' pq'' hpq hpq'' right]
  simp [edgeEpiStep_comp_iso_inv_assoc,
    ShortComplex.RightHomologyData.homologyIso_hom_comp_ι,
    HomologicalComplex.homologyIsoSc'_hom_ι_assoc,
    HomologicalComplex.isoHomologyι_inv_hom_id_assoc]

end

/-- The set of pages `r` from which all differentials into `pq` vanish. -/
def hasEdgeMonoSet (pq : ι) : Set ℤ  :=
  fun r => r₀ ≤ r ∧ ∀ (r' : ℤ) (_ : r ≤ r'), E.HasEdgeMonoAt pq r'

/-- The set of pages `r` from which all differentials out of `pq` vanish. -/
def hasEdgeEpiSet (pq : ι) : Set ℤ :=
  fun r => r₀ ≤ r ∧ ∀ (r' : ℤ) (_ : r ≤ r'), E.HasEdgeEpiAt pq r'

section

variable {E E'}

/-- If a morphism of spectral sequences is an isomorphism on the page `r`, it is an isomorphism
on the page `r + 1`. -/
lemma isIso_hom_succ (f : E ⟶ E') (r : ℤ) {hr : r₀ ≤ r}
    (hf : IsIso (f.hom r hr)) : IsIso (f.hom (r + 1)) := by
  have : ∀ (pq : ι), IsIso ((f.hom (r + 1)).f pq) := fun pq =>
    IsIso.of_isIso_fac_left (Hom.comm f r (r + 1) pq).symm
  apply HomologicalComplex.Hom.isIso_of_components

/-- If a morphism of spectral sequences is an isomorphism on the page `r`, it is an isomorphism
on every page `r' ≥ r`. -/
lemma isIso_hom_of_GE (f : E ⟶ E') (r r' : ℤ) (hrr' : r ≤ r') {hr : r₀ ≤ r}
    (hf : IsIso (f.hom r hr)) : IsIso (f.hom r') := by
  obtain ⟨k, hk⟩ := Int.le.dest hrr'
  revert r' hrr'
  induction k with
  | zero =>
    intro r' _ hrr'
    obtain rfl : r = r' := by lia
    exact hf
  | succ k hk =>
    intro r' _ hrr'
    obtain rfl : r' = (r + k) + 1 := by omega
    exact isIso_hom_succ f (r + k) (hk (r + k) (by lia) (by rfl))

end

end SpectralSequence

end CategoryTheory
