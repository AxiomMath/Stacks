module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Quasi-isomorphisms out of a single complex

A morphism `M[q] ⟶ K` from an object placed in degree `q` of a cochain complex indexed by `ℕ` is
given by a map `φ : M ⟶ Kᵠ` killed by the differential. It is a quasi-isomorphism in degree `q`
exactly when the induced map `M ⟶ Hᵠ(K)` is an isomorphism.

## Main results

* `Stacks.QuasiIsoFromSingle.quasiIsoAt_mkHomFromSingle`: a map from an object placed in degree
  `q` is a quasi-isomorphism in degree `q` when the induced map to `Hᵠ(K)` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Stacks.QuasiIsoFromSingle

section Basic

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℕ) (q : ℕ) {M : C}
  (φ : M ⟶ K.X q) (hφ : ∀ k, (ComplexShape.up ℕ).Rel q k → φ ≫ K.d q k = 0)

/-- The map on degree-`q` cycles induced by `mkHomFromSingle φ hφ` is the lift of `φ` to the
cycles of `K`, after identifying the cycles of `M[q]` with `M`. -/
theorem cyclesMap_mkHomFromSingle :
    cyclesMap (mkHomFromSingle φ hφ) q =
      (singleObjCyclesSelfIso (ComplexShape.up ℕ) q M).hom ≫
        K.liftCycles φ (q + 1) (by simp) (hφ _ rfl) := by
  rw [← cancel_mono (K.iCycles q), cyclesMap_i, mkHomFromSingle_f, Category.assoc,
    liftCycles_i, singleObjCyclesSelfIso_hom, Category.assoc]

/-- The map on degree-`q` homology induced by `mkHomFromSingle φ hφ` is the class of `φ` in
`Hᵠ(K)`, after identifying the homology of `M[q]` with `M`. -/
theorem homologyMap_mkHomFromSingle :
    homologyMap (mkHomFromSingle φ hφ) q =
      (singleObjHomologySelfIso (ComplexShape.up ℕ) q M).hom ≫
        (K.liftCycles φ (q + 1) (by simp) (hφ _ rfl) ≫ K.homologyπ q) := by
  rw [← cancel_epi (((single C (ComplexShape.up ℕ) q).obj M).homologyπ q),
    homologyπ_naturality, cyclesMap_mkHomFromSingle, homologyπ_singleObjHomologySelfIso_hom_assoc,
    Category.assoc]

/-- **A map from an object placed in degree `q` is a quasi-isomorphism in degree `q`** when the
induced map to the degree-`q` homology is an isomorphism. -/
theorem quasiIsoAt_mkHomFromSingle
    (h : IsIso (K.liftCycles φ (q + 1) (by simp) (hφ _ rfl) ≫ K.homologyπ q)) :
    QuasiIsoAt (mkHomFromSingle φ hφ) q := by
  rw [quasiIsoAt_iff_isIso_homologyMap, homologyMap_mkHomFromSingle]
  infer_instance

/-- **Two maps out of an object placed in degree `q` which differ by a boundary induce the same
map on homology in degree `q`.** -/
theorem homologyMap_mkHomFromSingle_eq_of_boundary (φ' : M ⟶ K.X q)
    (hφ' : ∀ k, (ComplexShape.up ℕ).Rel q k → φ' ≫ K.d q k = 0) {i' : ℕ} (h : M ⟶ K.X i')
    (e : φ - φ' = h ≫ K.d i' q) :
    homologyMap (mkHomFromSingle φ hφ) q = homologyMap (mkHomFromSingle φ' hφ') q := by
  rw [homologyMap_mkHomFromSingle, homologyMap_mkHomFromSingle]
  congr 1
  rw [← sub_eq_zero, ← Preadditive.sub_comp]
  have hl : K.liftCycles φ (q + 1) (by simp) (hφ _ rfl) - K.liftCycles φ' (q + 1) (by simp)
      (hφ' _ rfl) = K.liftCycles (φ - φ') (q + 1) (by simp)
        (by rw [Preadditive.sub_comp, hφ _ rfl, hφ' _ rfl, sub_zero]) := by
    rw [← cancel_mono (K.iCycles q), Preadditive.sub_comp, liftCycles_i, liftCycles_i,
      liftCycles_i]
  rw [hl]
  exact K.liftCycles_homologyπ_eq_zero_of_boundary (φ - φ') (q + 1) (by simp) h e

/-- **A cocycle map whose class factors through the class of another differs from it by a
boundary.** For maps `φ, Z : M ⟶ Kᵠ` killed by the differential with `M` projective and the map
`M ⟶ Hᵠ(K)` induced by `φ` invertible, there are `N : M ⟶ M` and `w : M ⟶ K^{q-1}` with
`Z - N ≫ φ = w ≫ d`. -/
theorem exists_sub_eq_boundary [Projective M] (Z : M ⟶ K.X q)
    (hZ : ∀ k, (ComplexShape.up ℕ).Rel q k → Z ≫ K.d q k = 0)
    (h : IsIso (K.liftCycles φ (q + 1) (by simp) (hφ _ rfl) ≫ K.homologyπ q)) :
    ∃ (N : M ⟶ M) (w : M ⟶ K.X (q - 1)), Z - N ≫ φ = w ≫ K.d (q - 1) q := by
  have hprev : (ComplexShape.up ℕ).prev q = q - 1 := by
    cases q with
    | zero => exact CochainComplex.prev_nat_zero
    | succ n => exact CochainComplex.prev_nat_succ n
  obtain ⟨N, hN⟩ : ∃ N : M ⟶ M, N = (K.liftCycles Z (q + 1) (CochainComplex.next ℕ q) (hZ _ rfl) ≫
      K.homologyπ q) ≫
        inv (K.liftCycles φ (q + 1) (CochainComplex.next ℕ q) (hφ _ rfl) ≫ K.homologyπ q) :=
    ⟨_, rfl⟩
  have hd : (Z - N ≫ φ) ≫ K.d q (q + 1) = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hφ _ rfl, hZ _ rfl, comp_zero,
      sub_self]
  have e : K.liftCycles (Z - N ≫ φ) (q + 1) (CochainComplex.next ℕ q) hd =
      K.liftCycles Z (q + 1) (CochainComplex.next ℕ q) (hZ _ rfl) -
        N ≫ K.liftCycles φ (q + 1) (CochainComplex.next ℕ q) (hφ _ rfl) := by
    refine (cancel_mono (K.iCycles q)).1 ?_
    simp only [Preadditive.sub_comp, Category.assoc, liftCycles_i]
  have hk : K.liftCycles (Z - N ≫ φ) (q + 1) (CochainComplex.next ℕ q) hd ≫ K.homologyπ q = 0 := by
    rw [e, Preadditive.sub_comp, Category.assoc, hN, Category.assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id, sub_self]
  have hS : (ShortComplex.mk (K.toCycles (q - 1) q) (K.homologyπ q)
      (K.toCycles_comp_homologyπ (q - 1) q)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel (q - 1) q hprev)
  refine ⟨N, hS.liftFromProjective _ hk, ?_⟩
  have h2 := hS.liftFromProjective_comp _ hk
  calc Z - N ≫ φ = K.liftCycles (Z - N ≫ φ) (q + 1) (CochainComplex.next ℕ q) hd ≫ K.iCycles q :=
        (liftCycles_i _ _ _ _ _).symm
    _ = (hS.liftFromProjective _ hk ≫ K.toCycles (q - 1) q) ≫ K.iCycles q :=
        congrArg (· ≫ K.iCycles q) h2.symm
    _ = _ := by rw [Category.assoc, toCycles_i]

end Basic

section Functoriality

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] {c : ComplexShape ℕ} {K L : HomologicalComplex C c} {q : ℕ}
  {M : C} (φ : M ⟶ K.X q) (hφ : ∀ k, c.Rel q k → φ ≫ K.d q k = 0)

/-- Composing `mkHomFromSingle φ hφ` with a morphism of complexes `g` gives the map out of the
single complex determined by `φ ≫ g.f q`. -/
theorem mkHomFromSingle_comp (g : K ⟶ L) :
    mkHomFromSingle φ hφ ≫ g = mkHomFromSingle (φ ≫ g.f q) (fun k hk => by
      rw [Category.assoc, g.comm, ← Category.assoc, hφ k hk, zero_comp]) := by
  ext
  simp only [HomologicalComplex.comp_f, mkHomFromSingle_f, Category.assoc]

/-- Precomposing `mkHomFromSingle φ hφ` with the image of `e : M' ⟶ M` under the single-complex
functor gives the map out of the single complex determined by `e ≫ φ`. -/
theorem single_map_comp_mkHomFromSingle {M' : C} (e : M' ⟶ M) :
    (single C c q).map e ≫ mkHomFromSingle φ hφ = mkHomFromSingle (e ≫ φ) (fun k hk => by
      rw [Category.assoc, hφ k hk, comp_zero]) := by
  ext
  simp only [HomologicalComplex.comp_f, single_map_f_self, mkHomFromSingle_f, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- Applying an additive functor `G` to `mkHomFromSingle φ hφ` gives, up to the identification of
`G` applied to `M[q]` with `(G M)[q]`, the map out of the single complex determined by `G.map φ`.
-/
theorem map_mkHomFromSingle (G : C ⥤ D) [G.Additive] :
    (G.mapHomologicalComplex c).map (mkHomFromSingle φ hφ) =
      (singleMapHomologicalComplex G c q).hom.app M ≫ mkHomFromSingle (G.map φ) (fun k hk => by
        rw [Functor.mapHomologicalComplex_obj_d, ← G.map_comp, hφ k hk, G.map_zero]) := by
  refine (Iso.inv_comp_eq ((singleMapHomologicalComplex G c q).app M)).1 ?_
  refine HomologicalComplex.from_single_hom_ext ?_
  simp only [Iso.app_inv, HomologicalComplex.comp_f, singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, mkHomFromSingle_f, Category.assoc, ← G.map_comp,
    Iso.inv_hom_id_assoc]

omit [HasZeroObject C] [HasZeroObject D] in
include hφ in
/-- If `φ` is killed by the differential of `K`, then `G₂.map (G₁.map φ ≫ g₁.f q) ≫ g₂.f q` is
killed by the differential of `L₂`. -/
theorem map_map_comp_d_eq_zero {E : Type*} [Category* E] [Preadditive E]
    (G₁ : C ⥤ D) [G₁.Additive] (G₂ : D ⥤ E) [G₂.Additive] {L₁ : HomologicalComplex D c}
    {L₂ : HomologicalComplex E c} (g₁ : (G₁.mapHomologicalComplex c).obj K ⟶ L₁)
    (g₂ : (G₂.mapHomologicalComplex c).obj L₁ ⟶ L₂) (k : ℕ) (hk : c.Rel q k) :
    (G₂.map (G₁.map φ ≫ g₁.f q) ≫ g₂.f q) ≫ L₂.d q k = 0 := by
  rw [Category.assoc, g₂.comm, ← Category.assoc, Functor.mapHomologicalComplex_obj_d,
    ← G₂.map_comp, Category.assoc, g₁.comm, Functor.mapHomologicalComplex_obj_d,
    ← Category.assoc, ← G₁.map_comp, hφ k hk, G₁.map_zero, zero_comp, G₂.map_zero, zero_comp]

/-- Two additive functors applied to a map out of a single complex, followed by morphisms of
complexes, as a map out of a single complex. -/
theorem map_map_mkHomFromSingle_comp {E : Type*} [Category* E] [Preadditive E] [HasZeroObject E]
    (G₁ : C ⥤ D) [G₁.Additive] (G₂ : D ⥤ E) [G₂.Additive] {L₁ : HomologicalComplex D c}
    {L₂ : HomologicalComplex E c} (g₁ : (G₁.mapHomologicalComplex c).obj K ⟶ L₁)
    (g₂ : (G₂.mapHomologicalComplex c).obj L₁ ⟶ L₂) :
    (G₂.mapHomologicalComplex c).map
        ((G₁.mapHomologicalComplex c).map (mkHomFromSingle φ hφ) ≫ g₁) ≫ g₂ =
      (G₂.mapHomologicalComplex c).map ((singleMapHomologicalComplex G₁ c q).hom.app M) ≫
        (singleMapHomologicalComplex G₂ c q).hom.app (G₁.obj M) ≫
          mkHomFromSingle (G₂.map (G₁.map φ ≫ g₁.f q) ≫ g₂.f q) (fun k hk => by
            rw [Category.assoc, g₂.comm, ← Category.assoc, Functor.mapHomologicalComplex_obj_d,
              ← G₂.map_comp, Category.assoc, g₁.comm, Functor.mapHomologicalComplex_obj_d,
              ← Category.assoc, ← G₁.map_comp, hφ k hk, G₁.map_zero, zero_comp, G₂.map_zero,
              zero_comp]) := by
  rw [Functor.map_comp, map_mkHomFromSingle, Functor.map_comp, map_mkHomFromSingle,
    Category.assoc, Category.assoc, Category.assoc, mkHomFromSingle_comp]
  congr 3
  rw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, ← Category.assoc,
    ← G₂.map_comp]

end Functoriality

end Stacks.QuasiIsoFromSingle

end
