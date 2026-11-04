module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedSerreInducedTStructure
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSums
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived

/-!
# Exact functors and direct sums of bounded below complexes with cohomology in a Serre class

Let `A`, `C` be abelian categories, `𝒜 ⊆ A` a weak Serre subcategory and `R : D(A) ⥤ D(C)` an
exact functor. If `R` commutes with direct sums of families `M_j[-a]` of objects of `𝒜` placed
in a single degree, then it commutes with the direct sum of every *uniformly bounded* family of
objects of `D_𝒜(A)` (dévissage along the truncation triangles), and, if moreover `R` does not
lower degrees (`R(D^{≥ b}) ⊆ D^{≥ b}`, e.g. `R` is the right derived functor of a left exact
functor), with the direct sum of every *uniformly bounded below* family of objects of `D_𝒜(A)`.

This is the affine input of [Stacks, Tag 08FB]: for an affine `Y`, `RΓ(Y, -)` carries a
quasi-coherent module `F[-a]` to `Γ(Y, F)[-a]` (affine vanishing) and global sections commute
with direct sums of quasi-coherent modules, so the hypothesis on single degrees holds with `𝒜`
the quasi-coherent modules, and the uniformly bounded below case follows from this file. The
passage to unbounded families is the uniform bound of
`Stacks.DerivedFunctor.Coproducts.preservesColimitsOfShape_ι_comp_of_uniform_bound`.

## Main results

* `Stacks.DerivedFunctor.Coproducts.isIso_sigmaComparison_of_isGE_isLE_of_weakSerre`: uniformly
  bounded families.
* `Stacks.DerivedFunctor.Coproducts.isIso_sigmaComparison_of_isGE_of_weakSerre`: uniformly
  bounded below families.
* `Stacks.DerivedFunctor.Coproducts.isIso_sigmaComparison_singleFunctor_of_rightDerived`: the
  single-degree hypothesis for a right derived functor, from the underived functor commuting with
  the direct sum and the vanishing of the higher derived functors on the family and on its sum.

## References

* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DerivedCategoryB WeakSerre

universe w

namespace Stacks.DerivedFunctor.Coproducts

variable {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory C]
  (R : DerivedCategory A ⥤ DerivedCategory C) [R.CommShift ℤ] [R.IsTriangulated]
  (𝒜 : ObjectProperty A) (h𝒜 : IsWeakSerre 𝒜) {α : Type w}
  [HasCoproductsOfShape α (DerivedCategory A)] [HasCoproductsOfShape α (DerivedCategory C)]

include h𝒜 in
/-- **Direct sums of uniformly bounded families with cohomology in a weak Serre class.** If an
exact functor commutes with direct sums of families of objects of `𝒜` placed in one degree, it
commutes with the direct sum of every family of objects of `D_𝒜(A)` lying in degrees `[a, b]`
for one `a` and `b`. -/
theorem isIso_sigmaComparison_of_isGE_isLE_of_weakSerre
    (hsingle : ∀ (a : ℤ) (M : α → A), (∀ j, 𝒜 (M j)) →
      IsIso (sigmaComparison R fun j ↦ (DerivedCategory.singleFunctor A a).obj (M j))) :
    ∀ (k : ℕ) (a b : ℤ), b - a ≤ (k : ℤ) →
      ∀ E : α → DerivedCategory A, (∀ j, derivedCategoryB 𝒜 (E j)) →
      (∀ j, (E j).IsGE a) → (∀ j, (E j).IsLE b) → IsIso (sigmaComparison R E) := by
  have hself : ∀ (a : ℤ) (E : α → DerivedCategory A), (∀ j, derivedCategoryB 𝒜 (E j)) →
      (∀ j, (E j).IsGE a) → (∀ j, (E j).IsLE a) → IsIso (sigmaComparison R E) := by
    intro a E hE hge hle
    have hex : ∀ j, ∃ N : A,
        Nonempty (E j ≅ (DerivedCategory.singleFunctor A a).obj N) := by
      intro j
      have := hge j
      have := hle j
      exact DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (E j) a
    choose N hN using hex
    have hN𝒜 : ∀ j, 𝒜 (N j) := fun j ↦
      h𝒜.isClosedUnderIsomorphisms.of_iso
        ((DerivedCategory.homologyFunctor A a).mapIso (hN j).some ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso A a).app (N j)) (hE j a)
    have hpres : PreservesColimit
        (Discrete.functor fun j ↦ (DerivedCategory.singleFunctor A a).obj (N j)) R :=
      preservesColimit_discreteFunctor_of_isIso_sigmaComparison _ _ (hsingle a N hN𝒜)
    have hdiag : (Discrete.functor fun j ↦ (DerivedCategory.singleFunctor A a).obj (N j))
        ≅ Discrete.functor E :=
      Discrete.natIso fun i ↦ ((hN i.as).some).symm
    exact isIso_sigmaComparison_of_preservesColimit _ E
      (preservesColimit_of_iso_diagram R hdiag)
  intro k
  induction k with
  | zero =>
      intro a b hba E hE hge hle
      refine hself a E hE hge fun j ↦ ?_
      have := hle j
      exact DerivedCategory.TStructure.t.isLE_of_le (E j) b a (by omega)
  | succ k ih =>
      intro a b hba E hE hge hle
      have h₁ : IsIso (sigmaComparison R
          fun j ↦ (DerivedCategory.TStructure.t.truncLE a).obj (E j)) := by
        refine hself a _ (fun j ↦ derivedCategoryB_truncLT_obj 𝒜 h𝒜 (a + 1) (E j) (hE j))
          (fun j ↦ ?_) (fun _ ↦ ?_)
        · have := hge j
          infer_instance
        · infer_instance
      have h₃ : IsIso (sigmaComparison R
          fun j ↦ (DerivedCategory.TStructure.t.truncGT a).obj (E j)) := by
        refine ih (a + 1) b (by omega) _
          (fun j ↦ derivedCategoryB_truncGE_obj 𝒜 h𝒜 (a + 1) (E j) (hE j))
          (fun _ ↦ ?_) (fun j ↦ ?_)
        · infer_instance
        · have := hle j
          infer_instance
      exact isIso_sigmaComparison_of_distTriang R
        (fun j ↦ (DerivedCategory.TStructure.t.truncLEι a).app (E j))
        (fun j ↦ (DerivedCategory.TStructure.t.truncGTπ a).app (E j))
        (fun j ↦ (DerivedCategory.TStructure.t.truncGTδLE a).app (E j))
        (fun j ↦ DerivedCategory.TStructure.t.triangleLEGT_distinguished a (E j))
        h₁ h₃

omit [HasCoproductsOfShape α (DerivedCategory A)] in
/-- A direct sum of objects of `D(C)` lying in degrees `≥ b` lies in degrees `≥ b`, when the
cohomology functors commute with the direct sum. -/
theorem isGE_sigma_of_forall_isGE
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete α) (DerivedCategory.homologyFunctor C n)]
    (X : α → DerivedCategory C) (b : ℤ) (h : ∀ j, (X j).IsGE b) : (∐ X).IsGE b := by
  rw [DerivedCategory.isGE_iff]
  intro n hn
  have hc := isColimitOfPreserves (DerivedCategory.homologyFunctor C n) (coproductIsCoproduct X)
  refine (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun j ↦ ?_)
  have := h j.as
  exact ((X j.as).isZero_of_isGE b n hn).eq_of_src _ _

include h𝒜 in
/-- **Direct sums of uniformly bounded below families with cohomology in a weak Serre class.**
If an exact functor `R` does not lower degrees and commutes with direct sums of families of
objects of `𝒜` placed in one degree, it commutes with the direct sum of every family of objects
of `D_𝒜(A)` lying in degrees `≥ a` for one `a`. In degree `q` the comparison is cut by the
truncation triangles `τ_{≤ q+1}E ⟶ E ⟶ τ_{> q+1}E`, whose third vertices `R` carries into degrees
`≥ q + 2`. -/
theorem isIso_sigmaComparison_of_isGE_of_weakSerre
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete α) (DerivedCategory.homologyFunctor A n)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete α) (DerivedCategory.homologyFunctor C n)]
    (hGE : ∀ (E : DerivedCategory A) (b : ℤ), E.IsGE b → (R.obj E).IsGE b)
    (hsingle : ∀ (a : ℤ) (M : α → A), (∀ j, 𝒜 (M j)) →
      IsIso (sigmaComparison R fun j ↦ (DerivedCategory.singleFunctor A a).obj (M j)))
    (a : ℤ) (E : α → DerivedCategory A) (hE : ∀ j, derivedCategoryB 𝒜 (E j))
    (hge : ∀ j, (E j).IsGE a) : IsIso (sigmaComparison R E) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  let m := q + 1
  let T : α → Triangle (DerivedCategory A) := fun j ↦
    (DerivedCategory.TStructure.t.triangleLEGT m).obj (E j)
  have hT : ∀ j, T j ∈ distTriang _ := fun j ↦
    DerivedCategory.TStructure.t.triangleLEGT_distinguished m (E j)
  have hGT : ∀ j, ((T j).obj₃).IsGE (m + 1) := fun j ↦
    inferInstanceAs (((DerivedCategory.TStructure.t.truncGT m).obj (E j)).IsGE (m + 1))
  have hs3 : (∐ fun j ↦ R.obj ((T j).obj₃)).IsGE (m + 1) :=
    isGE_sigma_of_forall_isGE _ (m + 1) fun j ↦ hGE _ _ (hGT j)
  have hw3 : (R.obj (∐ fun j ↦ (T j).obj₃)).IsGE (m + 1) :=
    hGE _ _ (isGE_sigma_of_forall_isGE _ (m + 1) hGT)
  have h₁ : IsIso (sigmaComparison R fun j ↦ (T j).obj₁) :=
    isIso_sigmaComparison_of_isGE_isLE_of_weakSerre R 𝒜 h𝒜 hsingle (m - a).toNat a m
      (by omega) _ (fun j ↦ derivedCategoryB_truncLT_obj 𝒜 h𝒜 (m + 1) (E j) (hE j))
      (fun j ↦ by have := hge j; exact inferInstanceAs
        (((DerivedCategory.TStructure.t.truncLE m).obj (E j)).IsGE a))
      (fun j ↦ inferInstanceAs (((DerivedCategory.TStructure.t.truncLE m).obj (E j)).IsLE m))
  exact Stacks.Duality.DerivedPushforward.isIso_homologyMap_sigmaComparison_of_isIso_obj₁ R T hT q
    ((∐ fun j ↦ R.obj ((T j).obj₃)).isZero_of_isGE (m + 1) q (by omega))
    ((∐ fun j ↦ R.obj ((T j).obj₃)).isZero_of_isGE (m + 1) (q - 1) (by omega))
    ((R.obj (∐ fun j ↦ (T j).obj₃)).isZero_of_isGE (m + 1) q (by omega))
    ((R.obj (∐ fun j ↦ (T j).obj₃)).isZero_of_isGE (m + 1) (q - 1) (by omega))
    (inferInstance)

section SingleDegree

variable {A C : Type*} [Category* A] [Category* C] [Abelian A] [Abelian C]
  [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory C]
  (F : A ⥤ C) [F.Additive] [PreservesFiniteLimits F]
  (RF : DerivedCategory A ⥤ DerivedCategory C) [RF.CommShift ℤ]
  (η : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor η (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  {β : Type w} [HasCoproductsOfShape β A] [HasCoproductsOfShape β C]
  [HasCoproductsOfShape β (DerivedCategory A)] [HasCoproductsOfShape β (DerivedCategory C)]

include η in
/-- **A right derived functor commutes with the direct sum of a family placed in one degree**,
as soon as the underived functor commutes with the direct sum of the family and the higher
derived functors vanish on every member of the family and on its direct sum. In degree `m` the
comparison is the comparison of `R^{m-a}F` (`m ≥ a`), which is that of `F` for `m = a` and a
morphism between zero objects for `m > a`; below `a` both sides vanish. -/
theorem isIso_sigmaComparison_singleFunctor_of_rightDerived
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete β) (DerivedCategory.homologyFunctor A n)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete β) (DerivedCategory.homologyFunctor C n)]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (a : ℤ) [PreservesColimitsOfShape (Discrete β) (DerivedCategory.singleFunctor A a)]
    (M : β → A) (h0 : IsIso (sigmaComparison F M))
    (hvan : ∀ n : ℕ, 0 < n → (∀ j, IsZero ((F.rightDerived n).obj (M j))) ∧
      IsZero ((F.rightDerived n).obj (∐ M))) :
    IsIso (sigmaComparison RF fun j ↦ (DerivedCategory.singleFunctor A a).obj (M j)) := by
  have hcomp : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (η.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := fun I hI ↦
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres).2
        DerivedCategory.Qh RF η I hI
  rw [DerivedCategory.isIso_iff]
  intro m
  refine isIso_map_sigmaComparison_of_isIso_comp _ _ _ ?_
    (isIso_sigmaComparison_of_preservesColimit _ _ inferInstance)
  rcases lt_or_ge m a with hlt | hle
  · have hz : ∀ X : DerivedCategory A, X.IsGE a →
        IsZero ((DerivedCategory.homologyFunctor C m).obj (RF.obj X)) := fun X hX ↦
      have : (RF.obj X).IsGE a := Stacks.SmallDerivedCategory.isGE_obj_of_isGE F RF η hcomp _ a hX
      DerivedCategory.isZero_of_isGE _ a m hlt
    refine Stacks.Duality.DerivedPushforward.isIso_of_isZero_of_isZero ?_ (hz _ ?_) _
    · refine Stacks.Duality.isZero_sigmaObj _ fun j ↦ hz _ inferInstance
    · exact isGE_sigma_of_forall_isGE _ a fun _ ↦ inferInstance
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, m - a = (n : ℤ) := ⟨(m - a).toNat, by omega⟩
    let e := Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived F RF η
      hres a m n hn
    have hRn : IsIso (sigmaComparison (F.rightDerived n) M) := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · have := preservesColimit_discreteFunctor_of_isIso_sigmaComparison F M h0
        exact isIso_sigmaComparison_of_preservesColimit _ M
          (preservesColimit_of_natIso _ F.rightDerivedZeroIsoSelf.symm)
      · exact Stacks.Duality.DerivedPushforward.isIso_of_isZero_of_isZero
          (Stacks.Duality.isZero_sigmaObj _ (hvan n hpos).1) (hvan n hpos).2 _
    have h₁ : IsIso (sigmaComparison (DerivedCategory.singleFunctor A a ⋙
        (RF ⋙ DerivedCategory.homologyFunctor C m)) M) :=
      have := preservesColimit_discreteFunctor_of_isIso_sigmaComparison _ M hRn
      isIso_sigmaComparison_of_preservesColimit _ M (preservesColimit_of_natIso _ e.symm)
    rw [sigmaComparison_comp] at h₁
    have h₂ : IsIso (sigmaComparison (DerivedCategory.singleFunctor A a) M) :=
      isIso_sigmaComparison_of_preservesColimit _ M inferInstance
    exact IsIso.of_isIso_comp_right _
      ((RF ⋙ DerivedCategory.homologyFunctor C m).map
        (sigmaComparison (DerivedCategory.singleFunctor A a) M))

end SingleDegree

end Stacks.DerivedFunctor.Coproducts

end
