module

public import StacksFrontier.RingTheory.Koszul.Concatenation.KoszulRegularAppend
import all StacksFrontier.RingTheory.Koszul.Concatenation.KoszulRegularAppend

@[expose] public section

-- The comparison maps below are assembled from `ModuleCat` quotients, `total` complexes and
-- `extend`/`restriction` wrappers, and the `rw`/`erw`/`change` steps that identify their
-- components unfold those wrappers through reducible-transparency defeq.
set_option backward.isDefEq.respectTransparency false

/-! # Koszul-regularity in the quotient

This part of `StacksFrontier.RingTheory.Koszul.Concatenation` contains the proof of Stacks Tag 068M
(`Koszul.koszulRegular_quotient_of_koszulRegular_append`), using the shared infrastructure of
`StacksFrontier.RingTheory.Koszul.Concatenation.KoszulRegularAppend`.
-/

namespace Koszul

universe u

open CategoryTheory CategoryTheory.Limits

/-! ## Koszul-regularity in the quotient (Tag 068M)

If both `f₁, …, f_n` and `f₁, …, f_n, g₁, …, g_m` are Koszul-regular in `A`, then the images
`ḡ₁, …, ḡ_m` form a Koszul-regular sequence in `A / (f₁, …, f_n)`.

The Koszul augmentation resolves the quotient ring. Tensoring its rows with the free terms of
the second Koszul complex gives quasi-isomorphisms, and the total complex comparison
identifies the resulting homology with that of the Koszul complex over the quotient.
-/

section Quotient

/-- Tensoring a quasi-isomorphism with a flat module preserves it. -/
private theorem quasiIso_tensorRight_map
    {A : Type u} [CommRing A] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} A) c}
    (α : K ⟶ L) [QuasiIso α] (M : ModuleCat.{u} A) [Module.Flat A M] :
    QuasiIso (((MonoidalCategory.tensorRight M).mapHomologicalComplex c).map α) := by
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight M) := inferInstance
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight M) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : (MonoidalCategory.tensorRight M).PreservesHomology := inferInstance
  exact HomologicalComplex.quasiIso_map_of_preservesHomology α _

/-- Every row of the tensor product with a Koszul complex resolves its augmentation. -/
private theorem koszulAugmentation_tensorRight_quasiIso
    {A : Type u} [CommRing A] {r s : ℕ} (f : Fin r → A) (g : Fin s → A)
    (hf : Koszul.IsKoszulRegular f) (q : ℕ) :
    QuasiIso (((MonoidalCategory.tensorRight ((Koszul.seqComplex g).X q)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (Koszul.koszulAugmentation f)) := by
  have : QuasiIso (Koszul.koszulAugmentation f) := koszulAugmentation_quasiIso f hf
  have : Module.Free A ((Koszul.seqComplex g).X q) :=
    Module.Free.of_basis ((Pi.basisFun A (Fin s)).exteriorPower q)
  exact quasiIso_tensorRight_map _ _

section TensorComparison

open HomologicalComplex MonoidalCategory

variable {A : Type u} [CommRing A]

private noncomputable abbrev tensorDouble
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (((curriedTensor (ModuleCat.{u} A)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K).obj L

private noncomputable def tensorSingleZeroInclusion
    (M : ModuleCat.{u} A) (K : ChainComplex (ModuleCat.{u} A) ℕ) :
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
      (tensorDouble ((ChainComplex.single₀ _).obj M) K).total (ComplexShape.down ℕ) where
  f n := (tensorDouble ((ChainComplex.single₀ _).obj M) K).ιTotal
    (ComplexShape.down ℕ) 0 n n (by simp)
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₁_eq_zero _ _ 0 (j + 1) j (by simp),
      HomologicalComplex₂.d₂_eq _ _ 0
        (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl) j (by simp)]
    simp

private theorem tensorSingleZero_isZero_XX
    (M : ModuleCat.{u} A) (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (p q : ℕ) (hp : p ≠ 0) :
    IsZero (((tensorDouble ((ChainComplex.single₀ _).obj M) K).X p).X q) :=
  Functor.map_isZero (tensorRight (K.X q))
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 M p hp)

private theorem tensorSingleZeroInclusion_isIso
    (M : ModuleCat.{u} A) (K : ChainComplex (ModuleCat.{u} A) ℕ) :
    IsIso (tensorSingleZeroInclusion M K) := by
  classical
  have h : ∀ n, IsIso ((tensorSingleZeroInclusion M K).f n) := by
    intro n
    let D := tensorDouble ((ChainComplex.single₀ _).obj M) K
    let r : (D.total (ComplexShape.down ℕ)).X n ⟶ M ⊗ K.X n :=
      D.totalDesc fun p q h =>
        if hp : p = 0 then eqToHom (by
          subst p
          have hq : q = n := by change 0 + q = n at h; omega
          subst q
          rfl)
        else (tensorSingleZero_isZero_XX M K p q hp).to_ _
    refine ⟨r, ?_, ?_⟩
    · change D.ιTotal _ 0 n n _ ≫ r = _
      simp [r, HomologicalComplex₂.ι_totalDesc]
      rfl
    · apply HomologicalComplex₂.total.hom_ext (ComplexShape.down ℕ)
      intro p q h
      by_cases hp : p = 0
      · subst p
        have hq : q = n := by change 0 + q = n at h; omega
        subst q
        change D.ιTotal _ 0 n n _ ≫ r ≫ D.ιTotal _ 0 n n _ = _
        rw [← Category.assoc]
        simp [r, HomologicalComplex₂.ι_totalDesc]
        rfl
      · exact (tensorSingleZero_isZero_XX M K p q hp).eq_of_src _ _
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem koszul_baseChange_iso
    (S : Type u) [CommRing S] [Algebra A S] {r : ℕ} (f : Fin r → A) :
    Nonempty
      (((tensorLeft (ModuleCat.of A S)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Koszul.seqComplex f) ≅
        ((ModuleCat.restrictScalars (algebraMap A S)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (Koszul.seqComplex (fun j => algebraMap A S (f j)))) := by
  choose β hβ using fun n => KoszulC.extPow_baseChange_natEquiv (R := A) (S := S) (r := r) n
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun n => ((β n).restrictScalars A).toModuleIso) ?_⟩
  intro i j hij
  obtain rfl : j + 1 = i := hij
  simp only [Functor.mapHomologicalComplex_obj_d, Koszul.seqComplex_d]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s z
  change Koszul.d (Koszul.seqDual (fun k => algebraMap A S (f k))) j
      (β (j + 1) (s ⊗ₜ[A] z)) = β j (s ⊗ₜ[A] Koszul.d (Koszul.seqDual f) j z)
  have h := KoszulC.d_baseChange_comm f β hβ j z
  have hs (k : ℕ) (w : ⋀[A]^k (Fin r → A)) :
      β k (s ⊗ₜ[A] w) = s • β k (1 ⊗ₜ[A] w) := by
    rw [← map_smul]
    congr 1
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hs, hs, map_smul, h]

private theorem koszul_isZero_homology_of_tensorLeft
    (S : Type u) [CommRing S] [Algebra A S] {r : ℕ} (f : Fin r → A) (i : ℕ)
    (h : IsZero ((((tensorLeft (ModuleCat.of A S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Koszul.seqComplex f)).homology i)) :
    IsZero ((Koszul.seqComplex (fun j => algebraMap A S (f j))).homology i) := by
  obtain ⟨e⟩ := koszul_baseChange_iso S f
  have hz := h.of_iso ((homologyFunctor _ _ i).mapIso e).symm
  let F := ModuleCat.restrictScalars (algebraMap A S)
  let K := Koszul.seqComplex (fun j => algebraMap A S (f j))
  have hz' : IsZero (F.obj (K.homology i)) :=
    hz.of_iso ((K.sc i).mapHomologyIso F).symm
  have hs : Subsingleton (F.obj (K.homology i)) := ModuleCat.isZero_iff_subsingleton.mp hz'
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

end TensorComparison

/-- If `f` and the concatenation of `f` and `g` are Koszul-regular, then the image
of `g` in the quotient by the ideal generated by `f` is Koszul-regular. -/
@[stacks 068M]
public theorem koszulRegular_quotient_of_koszulRegular_append
    {A : Type*} [CommRing A] {n m : ℕ} (f : Fin n → A) (g : Fin m → A)
    (hf : Koszul.IsKoszulRegular f)
    (hfg : Koszul.IsKoszulRegular (Fin.append f g)) :
    Koszul.IsKoszulRegular
      (fun j : Fin m => Ideal.Quotient.mk (Ideal.span (Set.range f)) (g j)) := by
  classical
  let := chainTotalSymmetry
  intro i hi
  let Q := ModuleCat.of A (A ⧸ Ideal.span (Set.range f))
  let F := Koszul.seqComplex f
  let G := Koszul.seqComplex g
  let S := (ChainComplex.single₀ (ModuleCat A)).obj Q
  let D := tensorDouble F G
  let E := tensorDouble S G
  let B := (MonoidalCategory.curriedTensor (ModuleCat A)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  let α : D ⟶ E := (B.map (Koszul.koszulAugmentation f)).app G
  let φ : D.flip ⟶ E.flip := (HomologicalComplex₂.flipFunctor _ _ _).map α
  obtain ⟨e⟩ := seqComplex_append_iso_totTensor f g
  have hD : IsZero ((D.total (ComplexShape.down ℕ)).homology i) :=
    (hfg i hi).of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso e.symm)
  have hDf := hD.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (D.totalFlipIso (ComplexShape.down ℕ)))
  have hE := isZero_total_homology_of_column_quasiIso φ m n
    (fun p hp => by
      apply (IsZero.iff_id_eq_zero _).mpr
      ext q : 1
      exact (Functor.map_isZero (MonoidalCategory.tensorLeft (F.X q))
        (koszul_isZero_X_of_lt g p hp)).eq_of_src _ _)
    (fun p q hq => Functor.map_isZero (MonoidalCategory.tensorRight (G.X p))
      (koszul_isZero_X_of_lt f q hq))
    (fun p hp => by
      apply (IsZero.iff_id_eq_zero _).mpr
      ext q : 1
      exact (Functor.map_isZero (MonoidalCategory.tensorLeft (S.X q))
        (koszul_isZero_X_of_lt g p hp)).eq_of_src _ _)
    (fun p q hq => tensorSingleZero_isZero_XX Q G q p (by omega))
    (fun p => koszulAugmentation_tensorRight_quasiIso f g hf p) i hi hDf
  have hEt := hE.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (E.totalFlipIso (ComplexShape.down ℕ)).symm)
  have : IsIso (tensorSingleZeroInclusion Q G) := tensorSingleZeroInclusion_isIso Q G
  have hL := hEt.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (asIso (tensorSingleZeroInclusion Q G)))
  exact koszul_isZero_homology_of_tensorLeft (A ⧸ Ideal.span (Set.range f)) g i hL

end Quotient

end Koszul

end
