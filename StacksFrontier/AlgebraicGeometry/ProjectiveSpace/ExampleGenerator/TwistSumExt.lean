module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsHomUnit
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Derived
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.DerivedTwistSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.QuasiCoherentGenerator

/-!
# The twist sum on projective space has no higher self-extensions

Let `A` be a ring, `X = P^n_A = Proj A[T₀, …, Tₙ]` and `P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`.
For `0 ≤ a, b ≤ n` the group `Ext^m_X(𝒪_X(-a), 𝒪_X(-b)) = H^m(X, 𝒪_X(a - b))` vanishes for
`m > 0` by the computation of the cohomology of projective space ([Stacks, Tag 01XT]), since
`a - b ≥ -n`. Hence `Ext^m_X(P, P) = 0` for every `m ≠ 0`. This is the input of
[Stacks, Tag 0BQU] that the endomorphism algebra of `P` computes the ext groups of `P`.

## Main results

* `Stacks.AlgebraicGeometry.ExampleGenerator.subsingleton_ext_twistModule`: the vanishing of
  `Ext^m(𝒪_X(-a), 𝒪_X(-b))` for `m > 0` and `0 ≤ a, b ≤ n`.
* `Stacks.AlgebraicGeometry.ExampleGenerator.subsingleton_hom_single_twistSumModule_shift`:
  `Hom_{D(𝒪_X)}(P, P[m]) = 0` for `m ≠ 0`, in any model of the derived category.

## Implementation notes

The computation is made in the standard model of `D(𝒪_X)`, where the twist autoequivalence
`Stacks.AlgebraicGeometry.ProjTwistFunctor.derivedTwist` and the identification
`H^0(X, M) = Hom(𝒪_X[0], M)` of
`AlgebraicGeometry.bijective_derivedGlobalSectionsOver_homToHomology` are available: twisting by
`𝒪_X(a)` turns `Hom(𝒪_X(-a)[0], 𝒪_X(-b)[m])` into
`Hom(𝒪_X[0], 𝒪_X(a - b)[m]) = H^m(X, 𝒪_X(a - b))`. It is then read in the model-independent
`Ext` groups of Mathlib, which makes the conclusion available at every model.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0BQU](https://stacks.math.columbia.edu/tag/0BQU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ExampleGenerator

variable (A : Type u) [CommRing A] (n : ℕ)

/-- In any model of the derived category of an abelian category, the module `N` placed in
degree zero and shifted by `m ≠ 0` has vanishing cohomology in degree zero. -/
theorem isZero_homologyFunctor_zero_singleFunctor_shift {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (N : C) (m : ℤ) (hm : m ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor C 0).obj
      (((DerivedCategory.singleFunctor C 0).obj N)⟦m⟧)) := by
  rcases lt_or_gt_of_ne hm with h | h
  · have : (((DerivedCategory.singleFunctor C 0).obj N)⟦m⟧).IsGE (-m) :=
      DerivedCategory.TStructure.t.isGE_shift _ 0 m (-m) (by omega)
    exact DerivedCategory.isZero_of_isGE _ (-m) 0 (by omega)
  · have : (((DerivedCategory.singleFunctor C 0).obj N)⟦m⟧).IsLE (-m) :=
      DerivedCategory.TStructure.t.isLE_shift _ 0 m (-m) (by omega)
    exact DerivedCategory.isZero_of_isLE _ (-m) 0 (by omega)

/-- **`Ext^m(𝒪_X(-a), 𝒪_X(-b)) = 0` for `m > 0` and `0 ≤ a, b ≤ n`**, on `X = P^n_A`: twisting
by `𝒪_X(a)` identifies the group with `H^m(X, 𝒪_X(a - b))`, which vanishes because
`a - b ≥ -n` ([Stacks, Tag 01XT]). -/
theorem subsingleton_ext_twistModule (a b : ℕ) (hb : b ≤ n) (m : ℕ) (hm : 0 < m) :
    letI := CategoryTheory.HasExt.standard (AlgebraicGeometry.Proj (polyGrading A n)).Modules
    Subsingleton (Abelian.Ext (twistModule A n (-(a : ℤ))) (twistModule A n (-(b : ℤ))) m) := by
  let := CategoryTheory.HasExt.standard (AlgebraicGeometry.Proj (polyGrading A n)).Modules
  let := HasDerivedCategory.standard (AlgebraicGeometry.Proj (polyGrading A n)).Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  rw [Abelian.Ext.homEquiv.subsingleton_congr]
  let S := DerivedCategory.singleFunctor (AlgebraicGeometry.Proj (polyGrading A n)).Modules 0
  let T := (ProjTwistFunctor.derivedTwist A n a).functor
  let e : ℤ := -(b : ℤ) + a
  have he : -(n : ℤ) ≤ e := by omega
  -- the source, twisted, is the structure sheaf in degree zero
  let e₁ : T.obj (S.obj (twistModule A n (-(a : ℤ)))) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient
          (AlgebraicGeometry.Proj (polyGrading A n)).Modules (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (AlgebraicGeometry.Proj (polyGrading A n)).Modules
          (ComplexShape.up ℤ) 0).obj
          (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf))) :=
    ProjTwistFunctor.derivedTwistTwistingSheafIso A n (-(a : ℤ)) a ≪≫
      S.mapIso (eqToIso (congrArg (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n))
        (neg_add_cancel (a : ℤ))) ≪≫ ProjTwistFunctor.twistingSheafZeroIso A n) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
      ((DerivedCategory.quotientCompQhIso (AlgebraicGeometry.Proj (polyGrading A n)).Modules).app
        ((HomologicalComplex.single (AlgebraicGeometry.Proj (polyGrading A n)).Modules
          (ComplexShape.up ℤ) 0).obj
          (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf))).symm
  -- the target, twisted, is `𝒪_X(e)[m]`
  let M := (S.obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) e))⟦(m : ℤ)⟧
  let e₂ : T.obj ((S.obj (twistModule A n (-(b : ℤ))))⟦(m : ℤ)⟧) ≅ M :=
    (T.commShiftIso (m : ℤ)).app _ ≪≫
      (CategoryTheory.shiftFunctor _ (m : ℤ)).mapIso
        (ProjTwistFunctor.derivedTwistTwistingSheafIso A n (-(b : ℤ)) a)
  -- `H^0(X, 𝒪_X(e)[m]) = H^m(X, 𝒪_X(e)) = 0`
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((derivedGlobalSectionsOver (projToSpecCoeff A n)).obj M)) :=
    IsZero.of_iso (isZero_homologyFunctor_zero_singleFunctor_shift
      (Stacks.ProjectiveSpace.Cohomology.twistCohomology A n e 0) (m : ℤ) (by omega))
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso
        (((derivedGlobalSectionsOver (projToSpecCoeff A n)).commShiftIso (m : ℤ)).app _ ≪≫
          (CategoryTheory.shiftFunctor _ (m : ℤ)).mapIso
            (Stacks.ProjectiveSpace.Cohomology.derivedGlobalSectionsOverTwistingSheafIso A n e he)))
  refine ⟨fun x y => T.map_injective ?_⟩
  apply (e₁.homCongr e₂).injective
  apply (bijective_derivedGlobalSectionsOver_homToHomology (projToSpecCoeff A n) M).1
  exact hz.eq_of_tgt _ _

/-- **`Hom_{D(𝒪_X)}(P, P[m]) = 0` for `m > 0`**, for the twist sum
`P = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` on `X = P^n_A`, in any model of the derived category. -/
theorem subsingleton_hom_single_twistSumModule_shift_of_pos
    [HasDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)).Modules] (m : ℕ) (hm : 0 < m) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj (twistSumModule A n) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj (twistSumModule A n))⟦(m : ℤ)⟧) := by
  let := HasExt.standard (AlgebraicGeometry.Proj (polyGrading A n)).Modules
  let S := DerivedCategory.singleFunctor (AlgebraicGeometry.Proj (polyGrading A n)).Modules 0
  let e₁ : S.obj (twistSumModule A n) ≅ ⨁ fun i => S.obj (twistFamily A n i) :=
    S.mapBiproduct (twistFamily A n)
  let e₂ : (S.obj (twistSumModule A n))⟦(m : ℤ)⟧ ≅
      ⨁ fun i => (S.obj (twistFamily A n i))⟦(m : ℤ)⟧ :=
    (CategoryTheory.shiftFunctor _ (m : ℤ)).mapIso e₁ ≪≫
      (CategoryTheory.shiftFunctor _ (m : ℤ)).mapBiproduct _
  have hij : ∀ i j : Fin (n + 1),
      Subsingleton (S.obj (twistFamily A n i) ⟶ (S.obj (twistFamily A n j))⟦(m : ℤ)⟧) :=
    fun i j => (Abelian.Ext.homEquiv (X := twistFamily A n i) (Y := twistFamily A n j)
      (n := m)).subsingleton_congr.mp
        (subsingleton_ext_twistModule A n i j (Nat.lt_succ_iff.mp j.2) m hm)
  refine ⟨fun f g => ?_⟩
  rw [← cancel_epi e₁.inv, ← cancel_mono e₂.hom]
  refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
  exact (hij i j).elim _ _

/-- **`Hom_{D(𝒪_X)}(P[k], P) = 0` for `k ≠ 0`**, for the twist sum `P` on `X = P^n_A`, in any
model of the derived category: for `k > 0` because `P` sits in degree zero, and for `k < 0` it is
`Ext^{-k}(P, P) = 0`. -/
theorem subsingleton_hom_single_twistSumModule_shift
    [HasDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)).Modules] (k : ℤ) (hk : k ≠ 0) :
    Subsingleton (((DerivedCategory.singleFunctor _ 0).obj (twistSumModule A n))⟦k⟧ ⟶
      (DerivedCategory.singleFunctor _ 0).obj (twistSumModule A n)) := by
  set Z := (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj (polyGrading A n)).Modules 0).obj
    (twistSumModule A n)
  rcases lt_or_gt_of_ne hk with h | h
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -k := ⟨(-k).toNat, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨fun f g => (CategoryTheory.shiftFunctor _ (m : ℤ)).map_injective ?_⟩
    let e : (Z⟦k⟧)⟦(m : ℤ)⟧ ≅ Z := (shiftFunctorCompIsoId _ k (m : ℤ) (by omega)).app Z
    rw [← cancel_epi e.inv]
    exact (subsingleton_hom_single_twistSumModule_shift_of_pos A n m (by omega)).elim _ _
  · have : (Z⟦k⟧).IsLE (-k) := DerivedCategory.TStructure.t.isLE_shift _ 0 k (-k) (by omega)
    refine ⟨fun f g => ?_⟩
    rw [DerivedCategory.TStructure.t.zero f (-k) 0 (by omega),
      DerivedCategory.TStructure.t.zero g (-k) 0 (by omega)]

end Stacks.AlgebraicGeometry.ExampleGenerator

/-! ### Bijectivity of the localization functor on maps between shifted single complexes -/

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

omit [HasDerivedCategory C] in
/-- For `M` in degree zero and `k ≠ 0`, there are no nonzero maps `M[k] ⟶ M` in the homotopy
category, for degree reasons. -/
private theorem _root_.HomotopyCategory.subsingleton_singleFunctor_shift_hom (M : C) {k : ℤ}
    (hk : k ≠ 0) :
    Subsingleton (((HomotopyCategory.singleFunctor C 0).obj M)⟦k⟧ ⟶
      (HomotopyCategory.singleFunctor C 0).obj M) := by
  refine ⟨fun f g => ?_⟩
  let eq : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)⟦k⟧) ≅
        ((HomotopyCategory.singleFunctor C 0).obj M)⟦k⟧ :=
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso k).app
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)
  refine (cancel_epi eq.hom).1 ?_
  obtain ⟨f', hf'⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective
    (eq.hom ≫ f)
  obtain ⟨g', hg'⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective
    (eq.hom ≫ g)
  obtain rfl : f' = g' := HomologicalComplex.to_single_hom_ext
    ((IsZero.of_iso (HomologicalComplex.isZero_single_obj_X _ 0 M (0 + k) (by omega))
      (CochainComplex.shiftFunctorObjXIso _ k 0 (0 + k) rfl)).eq_of_src _ _)
  exact hf'.symm.trans hg'

/-- The functor `K(C) ⥤ D(C)` is bijective on `Hom_{K(C)}(M[0], M)` for `M` in degree zero:
both groups are `Hom(M, M)`. -/
private theorem bijective_Qh_map_singleFunctor_shift_zero (M : C) :
    Function.Bijective (Qh.map :
      (((HomotopyCategory.singleFunctor C 0).obj M)⟦(0 : ℤ)⟧ ⟶
        (HomotopyCategory.singleFunctor C 0).obj M) → _) := by
  set Zh := (HomotopyCategory.singleFunctor C 0).obj M
  let e := (shiftFunctorZero (HomotopyCategory C (ComplexShape.up ℤ)) ℤ).app Zh
  have hsurj : Function.Surjective
      ((HomotopyCategory.singleFunctor C 0).map : (M ⟶ M) → (Zh ⟶ Zh)) := by
    intro φ
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective φ
    obtain ⟨f₀, rfl⟩ := (CochainComplex.singleFunctor C 0).map_surjective f
    exact ⟨f₀, rfl⟩
  have hEnd : Function.Bijective (Qh.map : (Zh ⟶ Zh) → _) := by
    have h1 := ((Functor.FullyFaithful.ofFullyFaithful (singleFunctor C 0)).ofIso
      (singleFunctorIsoCompQh C 0)).map_bijective M M
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · obtain ⟨a', rfl⟩ := hsurj a
      obtain ⟨b', rfl⟩ := hsurj b
      exact congrArg _ (h1.1 hab)
    · obtain ⟨c', rfl⟩ := h1.2 c
      exact ⟨_, rfl⟩
  have heq : (Qh.map : (Zh⟦(0 : ℤ)⟧ ⟶ Zh) → _) =
      (fun g => Qh.map e.hom ≫ g) ∘ (Qh.map : (Zh ⟶ Zh) → _) ∘ (fun g => e.inv ≫ g) := by
    funext g
    simp only [Function.comp_apply, ← Functor.map_comp, Iso.hom_inv_id_assoc]
  rw [heq]
  exact (Qh.mapIso e).symm.homFromEquiv.bijective.comp (hEnd.comp e.homFromEquiv.bijective)

/-- The functor `K(C) ⥤ D(C)` is bijective on `Hom_{K(C)}(M[k], M)` for `M` in degree zero, as
soon as `Hom_{D(C)}(M[k], M)` vanishes for `k ≠ 0`: in degree zero both groups are `Hom(M, M)`,
and away from it the source vanishes for degree reasons. -/
theorem bijective_Qh_map_singleFunctor_shift (M : C) (k : ℤ)
    (hk : k ≠ 0 → Subsingleton (((singleFunctor C 0).obj M)⟦k⟧ ⟶ (singleFunctor C 0).obj M)) :
    Function.Bijective (Qh.map :
      (((HomotopyCategory.singleFunctor C 0).obj M)⟦k⟧ ⟶
        (HomotopyCategory.singleFunctor C 0).obj M) → _) := by
  set Zh := (HomotopyCategory.singleFunctor C 0).obj M
  rcases eq_or_ne k 0 with rfl | h0
  · exact bijective_Qh_map_singleFunctor_shift_zero M
  · have := HomotopyCategory.subsingleton_singleFunctor_shift_hom M h0
    have htgt : Subsingleton (Qh.obj (Zh⟦k⟧) ⟶ Qh.obj Zh) := by
      let e₁ : Qh.obj (Zh⟦k⟧) ≅ ((singleFunctor C 0).obj M)⟦k⟧ :=
        (Qh.commShiftIso k).app Zh ≪≫
          (CategoryTheory.shiftFunctor _ k).mapIso ((singleFunctorIsoCompQh C 0).app M).symm
      let e₂ : Qh.obj Zh ≅ (singleFunctor C 0).obj M := ((singleFunctorIsoCompQh C 0).app M).symm
      exact (e₁.homCongr e₂).subsingleton_congr.mpr (hk h0)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun c => ⟨0, Subsingleton.elim _ _⟩⟩

end DerivedCategory

end
