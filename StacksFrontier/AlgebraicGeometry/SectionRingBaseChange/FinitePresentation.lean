module

public import StacksFrontier.AlgebraicGeometry.SymSectionsBaseChange.SectionRing
public import StacksFrontier.RingTheory.FinitePresentation.GradedTail
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Descent

/-!
# Finite presentation of a graded ring of sections from a graded base change

Let `A` be a quasi-coherent graded `𝒪_S`-algebra (Situation [Stacks, Tag 01NN]) and `U` an open
of `S`; its graded ring of sections `A(U) = ⨁_{n ≥ 0} Γ(U, A_n)` is a `Γ(S, U)`-algebra through
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom`.  This file reads
`GradedTailFinitePresentation.finitePresentation_of_isBaseChange` — steps (c)–(i) of the proof of
[Stacks, Tag 0D4F] — on graded rings of sections: if `A_0 = 𝒪_S`, the pieces `A_n`, `0 < n < e`,
have finitely presented sections over `U`, and some finitely presented graded ring of sections
`B(V)` over a ring `Γ(T, V)` with `B_0 = 𝒪_T` and `B_n = 0` for `0 < n < e` maps to `A(U)` by a
graded ring map exhibiting each `Γ(U, A_n)`, `n ≥ e`, as the base change of `Γ(V, B_n)`, then
`A(U)` is a finitely presented `Γ(S, U)`-algebra.

## Main definitions

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.gradingSubmodule`: the homogeneous parts of
  `A(U)` as `Γ(S, U)`-submodules, which form a graded algebra.

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.finitePresentation_strHom_of_isBaseChange`.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite DirectSum TensorProduct
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

/-- The degree-`n` part of the graded ring of sections, as a `Γ(S, U)`-submodule: the range of
the inclusion of the degree-`n` summand. -/
def gradingSubmodule (n : ℕ) : Submodule Γ(S, U) (A.sectionRing U) :=
  LinearMap.range (DirectSum.lof Γ(S, U) ℕ (A.sectionPieces U) n)

/-- The image of an element of the degree-`n` summand lies in the degree-`n` part. -/
theorem lof_mem_gradingSubmodule {n : ℕ} (y : A.sectionPieces U n) :
    DirectSum.of (A.sectionPieces U) n y ∈ gradingSubmodule A U n := ⟨y, rfl⟩

/-- The degree-`n` summand is the degree-`n` part. -/
def gradingSubmoduleEquiv (n : ℕ) : A.sectionPieces U n ≃ₗ[Γ(S, U)] gradingSubmodule A U n :=
  LinearEquiv.ofInjective _ (DFinsupp.single_injective (β := A.sectionPieces U) (i := n))

/-- `gradingSubmoduleEquiv` is the inclusion of the degree-`n` summand. -/
theorem coe_gradingSubmoduleEquiv (n : ℕ) (y : A.sectionPieces U n) :
    (gradingSubmoduleEquiv A U n y : A.sectionRing U) = DirectSum.of _ n y := rfl

/-- The graded ring of sections is the direct sum of the submodules `gradingSubmodule`. -/
instance decompositionGradingSubmodule : DirectSum.Decomposition (gradingSubmodule A U) := by
  let d : A.sectionRing U →+ ⨁ n : ℕ, gradingSubmodule A U n :=
    DirectSum.toAddMonoid fun n =>
      (DirectSum.of (fun n => gradingSubmodule A U n) n).comp
        (gradingSubmoduleEquiv A U n).toLinearMap.toAddMonoidHom
  refine DirectSum.Decomposition.ofAddHom _ d ?_ ?_
  · apply DirectSum.addHom_ext
    intro n x
    simp only [d, AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of, AddMonoidHom.id_apply,
      DirectSum.coeAddMonoidHom_of]
    rfl
  · apply DirectSum.addHom_ext
    intro n y
    obtain ⟨x, hx⟩ := y
    obtain ⟨a, rfl⟩ := hx
    simp only [d, AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
    exact (DirectSum.toAddMonoid_of _ n a).trans (congrArg (DirectSum.of _ n) (Subtype.ext rfl))

attribute [local instance] Stacks.SymGraded.AffinePieces.sectionRingAlgebra

/-- The graded ring of sections is a graded algebra for the submodules `gradingSubmodule`. -/
instance gradedAlgebraGradingSubmodule : _root_.GradedAlgebra (gradingSubmodule A U) where
  one_mem := ⟨_, (DirectSum.one_def _).symm⟩
  mul_mem := by
    rintro n m a b ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨_, (DirectSum.of_mul_of (A := A.sectionPieces U) a b).symm⟩

open scoped ChangeOfRings in
/-- A morphism out of an extension of scalars carries `t ⊗ m` to `t` times its value on
`1 ⊗ m`, being semilinear over the larger ring. -/
theorem extendScalars_hom_tmul {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (ψ : (ModuleCat.extendScalars φ).obj M ⟶ N) (t : S) (m : M) :
    ψ (t ⊗ₜ[R, φ] m) = t • ψ ((1 : S) ⊗ₜ[R, φ] m) := by
  let := φ.toAlgebra
  have hs : t ⊗ₜ[R, φ] m = t • ((1 : S) ⊗ₜ[R, φ] m) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact (congrArg (fun z => ψ z) hs).trans (ψ.hom.map_smul t _)

open scoped ChangeOfRings in
/-- **A bijective map out of an extension of scalars exhibits a base change.**  If
`G : S ⊗_R M ⟶ N` out of `ModuleCat.extendScalars` is bijective and sends `1 ⊗ m` to `f m`, then
`f` exhibits `N` as the base change of `M` along `R → S`.  The extension of scalars is formed with
the module structure of `S` restricted along `algebraMap R S`, which is a different term from the
one of the algebra `S`; this lemma is where the two are compared. -/
theorem isBaseChange_of_extendScalars {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] (f : M →ₗ[R] N)
    (G : (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M) ⟶ ModuleCat.of S N)
    (hG : Function.Bijective G) (h1 : ∀ m : M, G ((1 : S) ⊗ₜ[R, algebraMap R S] m) = f m) :
    IsBaseChange S f := by
  let χ : S ⊗[R] M →+ (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M) :=
    TensorProduct.liftAddHom
      { toFun := fun s =>
          { toFun := fun m => s ⊗ₜ[R, algebraMap R S] m
            map_zero' := TensorProduct.tmul_zero _ _
            map_add' := fun _ _ => TensorProduct.tmul_add _ _ _ }
        map_zero' := AddMonoidHom.ext fun m => TensorProduct.zero_tmul _ _
        map_add' := fun _ _ => AddMonoidHom.ext fun m => TensorProduct.add_tmul _ _ _ }
      (fun r s m => by
        change (r • s) ⊗ₜ[R, algebraMap R S] m = s ⊗ₜ[R, algebraMap R S] (r • m)
        rw [Algebra.smul_def]
        exact TensorProduct.smul_tmul (R := R) (M := (ModuleCat.restrictScalars
          (algebraMap R S)).obj (ModuleCat.of S S)) (N := M) r s m)
  let χ' : (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M) →+ S ⊗[R] M :=
    TensorProduct.liftAddHom
      { toFun := fun s =>
          { toFun := fun m => (s : S) ⊗ₜ[R] m
            map_zero' := TensorProduct.tmul_zero _ _
            map_add' := fun _ _ => TensorProduct.tmul_add _ _ _ }
        map_zero' := AddMonoidHom.ext fun m => TensorProduct.zero_tmul _ _
        map_add' := fun _ _ => AddMonoidHom.ext fun m => TensorProduct.add_tmul _ _ _ }
      (fun r s m => by
        change (algebraMap R S r * (show S from s)) ⊗ₜ[R] m = (show S from s) ⊗ₜ[R] (r • m)
        rw [← Algebra.smul_def]
        exact TensorProduct.smul_tmul r (show S from s) m)
  have hχχ' : ∀ z, χ (χ' z) = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s m => rfl
    | add z z' hz hz' =>
      exact (congrArg χ (map_add χ' z z')).trans ((map_add χ _ _).trans
        (congrArg₂ (· + ·) hz hz'))
  have hχ'χ : ∀ z, χ' (χ z) = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s m => rfl
    | add z z' hz hz' =>
      exact (congrArg χ' (map_add χ z z')).trans ((map_add χ' _ _).trans
        (congrArg₂ (· + ·) hz hz'))
  have hχbij : Function.Bijective χ :=
    Function.bijective_iff_has_inverse.mpr ⟨χ', hχ'χ, hχχ'⟩
  refine Stacks.FlatSectionsDescent.isBaseChange_of_bijective_liftBaseChange _
    (Stacks.FlatSectionsDescent.bijective_liftBaseChange_of_tmul _
      ((ConcreteCategory.hom G).toAddMonoidHom.comp χ) (hG.comp hχbij) fun s m => ?_)
  change G (s ⊗ₜ[R, algebraMap R S] m) = s • f m
  rw [extendScalars_hom_tmul (algebraMap R S) G s m, h1]

/-- If `r ↦ r • 1` is surjective onto the degree-`0` piece, the degree-`0` part of the graded ring
of sections consists of the image of the base ring. -/
private theorem exists_algebraMap_eq_of_mem_gradingSubmodule_zero {T : Scheme.{u}}
    (B : SheafGradedAlgebra T) (V : T.Opens)
    (hB0 : Function.Surjective fun r : Γ(T, V) => r • B.one V) (b : B.sectionRing V)
    (hb : b ∈ gradingSubmodule B V 0) : ∃ r : Γ(T, V), algebraMap Γ(T, V) _ r = b := by
  obtain ⟨y, rfl⟩ := hb
  obtain ⟨r, hr⟩ := hB0 y
  exact ⟨r, (Stacks.SymGraded.AffinePieces.algebraMap_sectionRingAlgebra B V r).trans
    ((SheafGradedAlgebra.strHom_apply B V r).trans (congrArg (DirectSum.of _ 0) hr))⟩

open scoped ChangeOfRings in
open Stacks.SymGraded.AffinePieces in
/-- **Steps (c)–(i) of the proof of [Stacks, Tag 0D4F], on graded rings of sections.**  Let `A`
be a quasi-coherent graded `𝒪_S`-algebra with `A_0 = 𝒪_S` over the open `U`, whose pieces in the
degrees `0 < n < e` have finitely presented sections over `U`.  Let `B` be one on `T` with
`B_0 = 𝒪_T` and `B_n = 0` for `0 < n < e` over `V`, whose graded ring of sections over `V` is a
finitely presented `Γ(T, V)`-algebra.  A graded ring map `B(V) → A(U)` lying over a ring map
`Γ(T, V) → Γ(S, U)`, and exhibiting every `Γ(U, A_n)`, `n ≥ e`, as the base change of
`Γ(V, B_n)`, makes `A(U)` a finitely presented `Γ(S, U)`-algebra. -/
theorem finitePresentation_strHom_of_isBaseChange {T : Scheme.{u}} (B : SheafGradedAlgebra T)
    (V : T.Opens) [Algebra Γ(T, V) Γ(S, U)] (e : ℕ)
    (hA0 : Function.Bijective fun r : Γ(S, U) => r • A.one U)
    (hband : ∀ n : ℕ, 0 < n → n < e →
      Module.FinitePresentation Γ(S, U) (A.sectionPieces U n))
    (hB0 : Function.Surjective fun r : Γ(T, V) => r • B.one V)
    (hBband : ∀ n : ℕ, 0 < n → n < e → ∀ b : B.sectionPieces V n, b = 0)
    (hBfp : (B.strHom V).FinitePresentation)
    (φ : B.sectionRing V →+* A.sectionRing U)
    (hφ0 : ∀ r, φ (B.strHom V r) = A.strHom U (algebraMap Γ(T, V) Γ(S, U) r))
    (φn : ∀ n : ℕ, B.sectionPieces V n →+ A.sectionPieces U n)
    (hφ : ∀ n x, φ (DirectSum.of _ n x) = DirectSum.of _ n (φn n x))
    (hbc : ∀ n, e ≤ n →
      ∃ G : (ModuleCat.extendScalars (algebraMap Γ(T, V) Γ(S, U))).obj
          (ModuleCat.of Γ(T, V) (B.sectionPieces V n)) ⟶ ModuleCat.of Γ(S, U) (A.sectionPieces U n),
        Function.Bijective G ∧
          ∀ x, G ((1 : Γ(S, U)) ⊗ₜ[Γ(T, V), (algebraMap Γ(T, V) Γ(S, U))] x) = φn n x) :
    (A.strHom U).FinitePresentation := by
  classical
  let iTA : Algebra Γ(T, V) (A.sectionRing U) :=
    ((A.strHom U).comp (algebraMap Γ(T, V) Γ(S, U))).toAlgebra
  have : IsScalarTower Γ(T, V) Γ(S, U) (A.sectionRing U) :=
    IsScalarTower.of_algebraMap_eq fun r => (algebraMap_sectionRingAlgebra A U _).symm
  have hAalg : (A.strHom U).toAlgebra = sectionRingAlgebra A U :=
    Algebra.algebra_ext _ _ fun r => (algebraMap_sectionRingAlgebra A U r).symm
  have hBalg : (B.strHom V).toAlgebra = sectionRingAlgebra B V :=
    Algebra.algebra_ext _ _ fun r => (algebraMap_sectionRingAlgebra B V r).symm
  have hBfp' : Algebra.FinitePresentation Γ(T, V) (B.sectionRing V) := hBalg ▸ hBfp
  let φa : B.sectionRing V →ₐ[Γ(T, V)] A.sectionRing U :=
    { φ with
      commutes' := fun r => by
        change φ (algebraMap Γ(T, V) (B.sectionRing V) r) = A.strHom U (algebraMap _ _ r)
        rw [algebraMap_sectionRingAlgebra]
        exact hφ0 r }
  have hφa : ∀ n, ∀ b ∈ gradingSubmodule B V n, φa b ∈ gradingSubmodule A U n := by
    rintro n b ⟨x, rfl⟩
    exact ⟨φn n x, (hφ n x).symm⟩
  have h0 := exists_algebraMap_eq_of_mem_gradingSubmodule_zero A U hA0.2
  have hinj : Function.Injective (algebraMap Γ(S, U) (A.sectionRing U)) := by
    intro r r' h
    rw [algebraMap_sectionRingAlgebra, algebraMap_sectionRingAlgebra,
      SheafGradedAlgebra.strHom_apply, SheafGradedAlgebra.strHom_apply] at h
    exact hA0.1 (DirectSum.of_injective (β := A.sectionPieces U) 0 h)
  have hband' : ∀ n, 0 < n → n < e →
      Module.FinitePresentation Γ(S, U) (gradingSubmodule A U n) := fun n hn hne =>
    have := hband n hn hne
    Module.FinitePresentation.of_equiv (gradingSubmoduleEquiv A U n)
  have hB0' := exists_algebraMap_eq_of_mem_gradingSubmodule_zero B V hB0
  have hBband' : ∀ n, 0 < n → n < e → ∀ b ∈ gradingSubmodule B V n, b = 0 := by
    rintro n hn hne b ⟨y, rfl⟩
    rw [hBband n hn hne y]
    exact map_zero _
  have hbc' : ∀ n, e ≤ n → IsBaseChange Γ(S, U)
      (GradedTailFinitePresentation.pieceMap (gradingSubmodule A U) (gradingSubmodule B V) φa
        hφa n) := by
    intro n hn
    obtain ⟨G, hG, hG1⟩ := hbc n hn
    let eB := gradingSubmoduleEquiv B V n
    let eA := gradingSubmoduleEquiv A U n
    let G' := (ModuleCat.extendScalars (algebraMap Γ(T, V) Γ(S, U))).map
        (ModuleCat.ofHom (eB.symm.toLinearMap : gradingSubmodule B V n →ₗ[Γ(T, V)] _)) ≫ G ≫
      ModuleCat.ofHom (eA.toLinearMap : A.sectionPieces U n →ₗ[Γ(S, U)] _)
    have hG' : Function.Bijective G' := by
      have i1 : IsIso ((ModuleCat.extendScalars (algebraMap Γ(T, V) Γ(S, U))).map
          (ModuleCat.ofHom (eB.symm.toLinearMap : gradingSubmodule B V n →ₗ[Γ(T, V)] _))) :=
        Functor.map_isIso _ (LinearEquiv.toModuleIso eB.symm).hom
      exact (eA.bijective.comp hG).comp
        (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ i1)
    refine isBaseChange_of_extendScalars _ G' hG' fun b => ?_
    obtain ⟨y, rfl⟩ := eB.surjective b
    change eA (G ((1 : Γ(S, U)) ⊗ₜ[Γ(T, V), (algebraMap Γ(T, V) Γ(S, U))] (eB.symm (eB y)))) = _
    rw [LinearEquiv.symm_apply_apply, hG1]
    exact Subtype.ext (hφ n y).symm
  rw [RingHom.FinitePresentation, hAalg]
  exact GradedTailFinitePresentation.finitePresentation_of_isBaseChange
    (gradingSubmodule A U) (gradingSubmodule B V) e h0 hinj hband' hB0' hBband' φa hφa hbc'

end Stacks.AlgebraicGeometry.SectionRingBaseChange

end
