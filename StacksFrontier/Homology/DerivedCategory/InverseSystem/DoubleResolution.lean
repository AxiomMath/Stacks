module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Two-term double resolutions of a short exact sequence

A short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in an abelian category resolves its kernel by the
two-term complex concentrated in degrees zero and one with differential its epimorphism, and an
additive functor preserves that quasi-isomorphism as soon as it keeps the sequence exact. A
cochain complex supported in degrees zero and one is isomorphic to such a two-term complex.
-/

@[expose] public section

open CategoryTheory Limits

namespace Stacks.DoubleResolution

/-- The morphism of cochain complexes from `S.X₁` in degree zero to the two-term complex
`S.X₂ ⟶ S.X₃` in degrees zero and one with differential `S.g`, given by `S.f` in degree zero. -/
noncomputable def shortExactResolutionUnit
    {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C) :
    (CochainComplex.singleFunctor C 0).obj S.X₁ ⟶
      HomologicalComplex.double S.g (show (ComplexShape.up ℤ).Rel 0 1 by rfl) :=
  HomologicalComplex.mkHomFromSingle
    (S.f ≫ (HomologicalComplex.doubleXIso₀ S.g (by rfl)).inv) (by
      intro j hj
      obtain rfl : j = 1 := by simpa using hj.symm
      simp [HomologicalComplex.double_d])

/-- In degree zero, `shortExactResolutionUnit S` is `S.f` composed with the identifications of the
degree-zero objects with `S.X₁` and `S.X₂`. -/
lemma shortExactResolutionUnit_f_zero
    {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C) :
    (shortExactResolutionUnit S).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁).hom ≫
        S.f ≫ (HomologicalComplex.doubleXIso₀ S.g (by rfl)).inv := by
  apply HomologicalComplex.mkHomFromSingle_f

/-- Auxiliary form of `map_shortExactResolutionUnit_quasiIsoAt_zero`. -/
private theorem map_shortExactResolutionUnit_quasiIsoAt_zero_aux
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (S : ShortComplex C) (hS : (S.map F).Exact)
    [Mono (F.map S.f)] :
    QuasiIsoAt ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (shortExactResolutionUnit S)) 0 := by
  rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.quasiIso_iff_of_zeros _ (by simp) (by simp)
      (by simp [HomologicalComplex.double_d_eq_zero₀])]
  constructor
  · refine ShortComplex.exact_of_iso (ShortComplex.isoMk
      (F.mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 S.X₁)).symm
      (F.mapIso (HomologicalComplex.doubleXIso₀ S.g
        (show (ComplexShape.up ℤ).Rel 0 1 by rfl))).symm
      (F.mapIso (HomologicalComplex.doubleXIso₁ S.g
        (show (ComplexShape.up ℤ).Rel 0 1 by rfl) (by norm_num))).symm ?_ ?_) hS
    · change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← F.map_comp, ← F.map_comp]
      congr 1
      simp [shortExactResolutionUnit_f_zero]
    · change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← F.map_comp, ← F.map_comp]
      congr 1
      simp [HomologicalComplex.double_d]
  · change Mono (F.map ((shortExactResolutionUnit S).f 0))
    rw [shortExactResolutionUnit_f_zero, F.map_comp, F.map_comp]
    infer_instance

/-- Auxiliary form of `map_shortExactResolutionUnit_quasiIso`. -/
private theorem map_shortExactResolutionUnit_quasiIso_aux
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (S : ShortComplex C) (hS : (S.map F).ShortExact) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (shortExactResolutionUnit S)) := by
  have : Mono (F.map S.f) := hS.mono_f
  have : Epi (F.map S.g) := hS.epi_g
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := HomologicalComplex.double S.g (show (ComplexShape.up ℤ).Rel 0 1 by rfl)
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = 0
  · subst i
    exact map_shortExactResolutionUnit_quasiIsoAt_zero_aux F S hS.exact
  · rw [quasiIsoAt_iff_exactAt _ i
      ((G.obj ((CochainComplex.singleFunctor C 0).obj S.X₁)).sc i |>.exact_of_isZero_X₂
        (F.map_isZero (HomologicalComplex.isZero_single_obj_X _ 0 _ i hi)))]
    by_cases hi₁ : i = 1
    · subst i
      apply ((G.obj L).exactAt_iff' 0 1 2 (by simp) (by simp)).2
      apply (((G.obj L).sc' 0 1 2).exact_iff_epi (by
        simp [G, L, HomologicalComplex.double_d_eq_zero₀])).2
      change Epi (F.map (L.d 0 1))
      dsimp [L]
      rw [HomologicalComplex.double_d _ _ (by norm_num), F.map_comp, F.map_comp]
      infer_instance
    · exact ((G.obj L).sc i).exact_of_isZero_X₂
        (F.map_isZero (HomologicalComplex.isZero_double_X S.g
          (show (ComplexShape.up ℤ).Rel 0 1 by rfl) i hi hi₁))

/-- For a short exact sequence `S`, the morphism `shortExactResolutionUnit S` is a
quasi-isomorphism. -/
theorem shortExactResolutionUnit_quasiIso
    {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C) (hS : S.ShortExact) :
    QuasiIso (shortExactResolutionUnit S) := by
  exact map_shortExactResolutionUnit_quasiIso_aux (𝟭 C) S hS

/-- A complex supported in degrees zero and one is determined by its differential. -/
noncomputable def isoDoubleOfSupport
    {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
    (K : CochainComplex C ℤ) {X Y : C} (f : X ⟶ Y)
    (e₀ : K.X 0 ≅ X) (e₁ : K.X 1 ≅ Y)
    (hz : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (K.X i))
    (hd : e₀.inv ≫ K.d 0 1 ≫ e₁.hom = f) :
    K ≅ HomologicalComplex.double f (show (ComplexShape.up ℤ).Rel 0 1 by rfl) := by
  classical
  let L := HomologicalComplex.double f (show (ComplexShape.up ℤ).Rel 0 1 by rfl)
  let e : ∀ i : ℤ, K.X i ≅ L.X i := fun i =>
    if h₀ : i = 0 then (K.XIsoOfEq h₀) ≪≫ e₀ ≪≫
      (HomologicalComplex.doubleXIso₀ f (by rfl)).symm ≪≫ (L.XIsoOfEq h₀).symm
    else if h₁ : i = 1 then (K.XIsoOfEq h₁) ≪≫ e₁ ≪≫
      (HomologicalComplex.doubleXIso₁ f (by rfl) (by norm_num)).symm ≪≫
        (L.XIsoOfEq h₁).symm
    else (hz i h₀ h₁).iso (HomologicalComplex.isZero_double_X f (by rfl) i h₀ h₁)
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j hij
  have hij' : i + 1 = j := hij
  by_cases hi₀ : i = 0
  · subst i
    obtain rfl : j = 1 := by omega
    simp only [e, dite_eq_left]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.symm_hom,
      Iso.trans_hom, Category.id_comp]
    dsimp [L]
    rw [HomologicalComplex.double_d _ _ (by norm_num)]
    simp only [Category.assoc]
    rw [← hd]
    simp
  · by_cases hi₁ : i = 1
    · subst i
      exact (HomologicalComplex.isZero_double_X f (by rfl) j (by omega) (by omega)).eq_of_tgt _ _
    · exact (hz i hi₀ hi₁).eq_of_src _ _

/-- If `F` is additive, `S.map F` is exact and `F.map S.f` is a monomorphism, then the image of
`shortExactResolutionUnit S` under `F` is a quasi-isomorphism in degree zero. -/
theorem map_shortExactResolutionUnit_quasiIsoAt_zero
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (S : ShortComplex C) (hS : (S.map F).Exact)
    [Mono (F.map S.f)] :
    QuasiIsoAt ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (shortExactResolutionUnit S)) 0 := by
  exact map_shortExactResolutionUnit_quasiIsoAt_zero_aux F S hS

/-- Applying a functor to the augmentation of a two-term resolution preserves its quasi-isomorphism
whenever the resulting short sequence is exact. -/
theorem map_shortExactResolutionUnit_quasiIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (S : ShortComplex C) (hS : (S.map F).ShortExact) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (shortExactResolutionUnit S)) := by
  exact map_shortExactResolutionUnit_quasiIso_aux F S hS

end Stacks.DoubleResolution

end
