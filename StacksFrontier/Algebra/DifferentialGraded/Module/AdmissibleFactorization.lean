module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory
public import StacksFrontier.Algebra.DGA.Cone

/-!
# Factoring homomorphisms of differential graded modules through admissible monomorphisms

Every homomorphism `α : K ⟶ L` of right differential graded modules factors as an admissible
monomorphism `K ⟶ L'` followed by a homomorphism `L' ⟶ L` which is a homotopy equivalence with a
strict section. Consequently every finite sequence of homomorphisms can be replaced, up to
homotopy equivalence, by a sequence all of whose arrows are admissible monomorphisms.

## Main definitions

* `DifferentialGradedModule.IsHomotopyEquivalence`: a homomorphism admitting a two-sided inverse
  up to homotopy.

## Main results

* `DifferentialGradedModule.exists_factorization_isAdmissibleMono`: the factorization of a single
  homomorphism, with the admissibility of the first arrow and the section and homotopy properties
  of the second.
* `DifferentialGradedModule.exists_admissibleMono_sequence`: the replacement of a finite sequence
  of homomorphisms by one with admissible monomorphisms.

## Implementation notes

The intermediate module `L'` is the mapping cone of the zero map from the `(-1)`-shift of the
cone of `𝟙 K` to `L`; the cone of `𝟙 K` is contractible, which is what makes the projection
`L' ⟶ L` a homotopy equivalence. The factorization and the section are expressed as equalities of
homomorphisms of differential graded modules, and the homotopy runs from the composite of the
projection and its section to the identity of `L'`.

In the sequence statement the sequence is indexed by `Fin n`, with the `i`-th arrow joining
`i.castSucc` to `i.succ`; the induction step appends one arrow, so the intermediate modules of
the replacement are produced by `Fin.lastCases` and the squares are compared after transporting
along the resulting equalities of objects.

## References

* [Stacks Project, Tag 09JW](https://stacks.math.columbia.edu/tag/09JW)
* [Stacks Project, Tag 09JX](https://stacks.math.columbia.edu/tag/09JX)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

section Factorization

variable {K L : DifferentialGradedModule.{u, v, w} A}

/-- A homomorphism of differential graded modules factors through an admissible monomorphism,
followed by a homomorphism which is split and a homotopy equivalence. -/
@[stacks 09JW]
theorem exists_factorization_isAdmissibleMono (α : K ⟶ L) :
    ∃ (L' : DifferentialGradedModule.{u, v, w} A) (α' : K ⟶ L')
      (π : L' ⟶ L) (s : L ⟶ L'),
      α' ≫ π = α ∧ IsAdmissibleMono α' ∧
        s ≫ π = 𝟙 L ∧ Homotopic (π ≫ s) (𝟙 L') := by
  classical
  let C := coneModule (𝟙 K)
  let D0 := shift C (-1)
  let D : DifferentialGradedModule.{u, v, w} A := {
    M := C.M
    grading := D0.grading
    decomposition := D0.decomposition
    smul_mem := D0.smul_mem
    d := D0.d
    d_comp_d := D0.d_comp_d
    d_mem := D0.d_mem
    leibniz := D0.leibniz
  }
  let z : D ⟶ L := 0
  let E : Cone z := cone z
  let L' := E.module
  have hcoordsymm : ∀ y : L.M × D.M, E.coordinates.symm y = y := fun _ => rfl
  have hcoord_smul (a : A.Aᵐᵒᵖ) (x : L'.M) :
      E.coordinates (a • x) = a • E.coordinates x := rfl
  have hsnd_smul (a : A.Aᵐᵒᵖ) (x : L.M × D.M) : (a • x).2 = a • x.2 := rfl
  have hcoordsymm_smul (a : A.Aᵐᵒᵖ) (x : L.M × D.M) :
      E.coordinates.symm (a • x) = a • E.coordinates.symm x := rfl
  let contractC : C.M →ₗ[R] C.M :=
    (0 : C.M →ₗ[R] K.M).prod (-(LinearMap.fst R K.M K.M))
  have hcontractC_smul (a : A.Aᵐᵒᵖ) (x : C.M) :
      contractC (a • x) = a • contractC x := by
    show ((0 : K.M), -(a • x).1) = (a • (0 : K.M), a • -x.1)
    simp [show (a • x).1 = a • x.1 by rfl]
  have hcontractPair_smul (a : A.Aᵐᵒᵖ) (x : C.M) :
      ((0 : L.M), contractC (a • x)) =
        a • ((0 : L.M), contractC x) :=
    Prod.ext (by simp) (hcontractC_smul a x)
  have hcontractC_d (x : K.M × K.M) :
      coneD (𝟙 K) ((0 : K.M), -x.1) +
        ((0 : K.M), -(coneD (𝟙 K) x).1) = -x := by
    ext <;> simp [coneD_apply] <;> rfl
  have hgrade (n : ℤ) : D.grading (n + 1) = C.grading n := by
    show D0.grading (n + 1) = C.grading n
    rw [shift_grading]
    congr 1
    omega
  have hdD : ∀ y : C.M, -D.d y = C.d y := fun y => by
    simp [D, D0, shift_d, Int.negOnePow]
  let α' : K ⟶ L' := {
    toFun := E.coordinates.symm.toLinearMap.comp
      ((α.toFun).prod (coneInclusion (𝟙 K)).toFun)
    map_smul := by
      intro x a
      show E.coordinates.symm
          (α.toFun (MulOpposite.op a • x),
            (coneInclusion (𝟙 K)).toFun (MulOpposite.op a • x)) =
        MulOpposite.op a • E.coordinates.symm
          (α.toFun x, (coneInclusion (𝟙 K)).toFun x)
      rw [hcoordsymm, hcoordsymm, α.map_smul,
        (coneInclusion (𝟙 K)).map_smul]
      exact (Prod.ext rfl rfl)
    map_grading := by
      intro n x hx
      rw [E.grading_iff]
      show α.toFun x ∈ L.grading n ∧
        (coneInclusion (𝟙 K)).toFun x ∈ D.grading (n + 1)
      refine ⟨α.map_grading n x hx, ?_⟩
      rw [hgrade]
      exact (coneInclusion (𝟙 K)).map_grading n x hx
    map_d := by
      apply LinearMap.ext
      intro x
      apply E.coordinates.injective
      show E.coordinates (E.coordinates.symm
          (α.toFun (K.d x), (coneInclusion (𝟙 K)).toFun (K.d x))) =
        E.coordinates (E.module.d (E.coordinates.symm
          (α.toFun x, (coneInclusion (𝟙 K)).toFun x)))
      simp only [E.coordinates.apply_symm_apply]
      rw [E.differential]
      simp only [E.coordinates.apply_symm_apply]
      apply Prod.ext
      · simpa [z] using (LinearMap.congr_fun α.map_d x)
      · show (coneInclusion (𝟙 K)).toFun (K.d x) =
          -D.d ((coneInclusion (𝟙 K)).toFun x)
        rw [hdD]
        exact LinearMap.congr_fun (coneInclusion (𝟙 K)).map_d x
  }
  let π : L' ⟶ L := {
    toFun := (LinearMap.fst R L.M D.M).comp E.coordinates.toLinearMap
    map_smul := fun _ _ => rfl
    map_grading := fun n x hx => ((E.grading_iff n x).mp hx).1
    map_d := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply]
      show (LinearMap.fst R L.M D.M) (E.coordinates (E.module.d x)) =
        L.d ((LinearMap.fst R L.M D.M) (E.coordinates x))
      rw [E.differential]
      simp [z]
  }
  let s : L ⟶ L' := E.inclusion
  let Hlin : L'.M →ₗ[R] L'.M := E.coordinates.symm.toLinearMap.comp
    ((0 : L'.M →ₗ[R] L.M).prod
      (contractC.comp ((LinearMap.snd R L.M D.M).comp E.coordinates.toLinearMap)))
  have hHcoord (x : L'.M) :
      E.coordinates (Hlin x) = (0, contractC ((E.coordinates x).2)) := by
    simp [Hlin]
  have hπscoord (x : L'.M) :
      E.coordinates ((π ≫ s).toFun x) = ((E.coordinates x).1, 0) := by
    show E.coordinates (E.inclusion.toFun
      ((LinearMap.fst R L.M D.M) (E.coordinates x))) = ((E.coordinates x).1, 0)
    rw [E.inclusion_coordinates]
    rfl
  have hdcoord (x : L'.M) :
      E.coordinates (L'.d x) =
        (L.d (E.coordinates x).1, C.d (E.coordinates x).2) := by
    rw [E.differential]
    simp [z, hdD]
  have hcgrade (n : ℤ) (x : L'.M) (hx : x ∈ L'.grading n) :
      (E.coordinates x).2 ∈ coneGrading K K n := by
    have hx' := (E.grading_iff n x).mp hx
    rw [hgrade] at hx'
    exact hx'.2
  refine ⟨L', α', π, s, ?_, ?_, ?_, ?_⟩
  · apply Hom.ext
    apply LinearMap.ext
    intro x
    rfl
  · refine ⟨{
      toFun := {
        toFun := fun x => (LinearMap.fst R K.M K.M)
          ((LinearMap.snd R L.M D.M) (E.coordinates.toLinearMap x))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
      }
      map_smul := ?_
      map_grading := ?_
    }, ?_⟩
    · intro x a
      show (LinearMap.fst R K.M K.M)
          ((LinearMap.snd R L.M D.M) (E.coordinates (MulOpposite.op a • x))) =
        MulOpposite.op a • (LinearMap.fst R K.M K.M)
          ((LinearMap.snd R L.M D.M) (E.coordinates x))
      rw [hcoord_smul]
      rfl
    · intro n x hx
      exact ((coneGrading_mem n (E.coordinates x).2).mp (hcgrade n x hx)).1
    · exact fun _ => rfl
  · apply Hom.ext
    apply LinearMap.ext
    intro x
    rfl
  · refine ⟨{
      toLinearMap := {
        toFun := Hlin
        map_add' := Hlin.map_add
        map_smul' := by
          intro a x
          have h : E.coordinates.symm
              ((0 : L.M), contractC ((E.coordinates (a • x)).2)) =
            a • E.coordinates.symm
              ((0 : L.M), contractC ((E.coordinates x).2)) := by
            rw [hcoord_smul, hsnd_smul, hcontractPair_smul, hcoordsymm_smul]
          simpa [Hlin] using h
      }
      map_grading := ?_
      homotopy_eq := ?_
    }⟩
    · intro n x hx
      have hcparts := (coneGrading_mem n (E.coordinates x).2).mp (hcgrade n x hx)
      show E.coordinates.symm
          ((0 : L.M), contractC ((E.coordinates x).2)) ∈ L'.grading (n - 1)
      rw [E.grading_iff, E.coordinates.apply_symm_apply]
      rw [hgrade (n - 1)]
      show (0 : L.M) ∈ L.grading (n - 1) ∧
        contractC ((E.coordinates x).2) ∈ coneGrading K K (n - 1)
      refine ⟨(L.grading (n - 1)).zero_mem, ?_⟩
      show ((0 : K.M), -(LinearMap.fst R K.M K.M ((E.coordinates x).2))) ∈
        coneGrading K K (n - 1)
      rw [coneGrading_mem]
      refine ⟨(K.grading (n - 1)).zero_mem, ?_⟩
      show -(E.coordinates x).2.1 ∈ K.grading (n - 1 + 1)
      simpa only [show n - 1 + 1 = n by omega] using
        (K.grading n).neg_mem hcparts.1
    · intro x
      apply E.coordinates.injective
      simp only [map_sub, map_add]
      show E.coordinates ((π ≫ s).toFun x) - E.coordinates x =
        E.coordinates (L'.d (Hlin x)) + E.coordinates (Hlin (L'.d x))
      rw [hπscoord, hdcoord (Hlin x), hHcoord x,
        hHcoord (L'.d x), hdcoord x]
      apply Prod.ext
      · simp
      · simp only [Prod.snd_add, Prod.snd_sub, zero_sub]
        dsimp only [D, contractC, C, coneModule, cone, coneObject]
        exact (hcontractC_d (E.coordinates x).2).symm

end Factorization

/-- A homomorphism of differential graded modules with a two-sided homotopy inverse. -/
abbrev IsHomotopyEquivalence {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) : Prop :=
  ∃ g : Hom N M,
    Homotopic (Hom.comp g f) (Hom.id M) ∧ Homotopic (Hom.comp f g) (Hom.id N)

private theorem isAdmissibleMono_congr
    {K K' L L' : DifferentialGradedModule.{u, v, w} A}
    (eK : K' = K) (eL : L = L') (f : K ⟶ L) (hf : IsAdmissibleMono f) :
    IsAdmissibleMono (eqToHom eK ≫ f ≫ eqToHom eL) := by
  cases eK
  cases eL
  simpa using hf

private theorem isHomotopyEquivalence_congr
    {M M' N N' : DifferentialGradedModule.{u, v, w} A}
    (eM : M' = M) (eN : N = N') (f : M ⟶ N) (hf : IsHomotopyEquivalence f) :
    IsHomotopyEquivalence (eqToHom eM ≫ f ≫ eqToHom eN) := by
  cases eM
  cases eN
  simpa [IsHomotopyEquivalence] using hf

/-- Replace a finite sequence of differential graded modules by one whose arrows are admissible
monomorphisms, compatibly with homotopy equivalences to the original sequence. -/
@[stacks 09JX]
theorem exists_admissibleMono_sequence (n : ℕ)
    (L : Fin (n + 1) → DifferentialGradedModule.{u, v, w} A)
    (f : ∀ i : Fin n, Hom (L i.castSucc) (L i.succ)) :
    ∃ (M : Fin (n + 1) → DifferentialGradedModule.{u, v, w} A)
      (g : ∀ i : Fin n, Hom (M i.castSucc) (M i.succ))
      (p : ∀ i : Fin (n + 1), Hom (M i) (L i)),
      (∀ i, IsAdmissibleMono (g i)) ∧
      (∀ i, IsHomotopyEquivalence (p i)) ∧
      (∀ i : Fin n, Hom.comp (p i.succ) (g i) = Hom.comp (f i) (p i.castSucc)) := by
  induction n with
  | zero =>
      refine ⟨L, (fun i => i.elim0), (fun i => Hom.id (L i)), ?_, ?_, ?_⟩
      · exact fun i => i.elim0
      · exact fun i => ⟨Hom.id (L i), Homotopic.refl _, Homotopic.refl _⟩
      · exact fun i => i.elim0
  | succ n ih =>
      let L₀ : Fin (n + 1) → DifferentialGradedModule.{u, v, w} A := fun i => L i.castSucc
      let f₀ : ∀ i : Fin n, Hom (L₀ i.castSucc) (L₀ i.succ) := fun i => f i.castSucc
      obtain ⟨M₀, g₀, p₀, hg₀, hp₀, hcomm₀⟩ := ih L₀ f₀
      let α : Hom (M₀ (Fin.last n)) (L (Fin.last n).succ) :=
        Hom.comp (f (Fin.last n)) (p₀ (Fin.last n))
      obtain ⟨M₁, α', π, s, hfactor, hmono, hsπ, hπs⟩ :=
        exists_factorization_isAdmissibleMono α
      let M' : Fin (n + 2) → DifferentialGradedModule.{u, v, w} A :=
        Fin.lastCases M₁ (fun i => M₀ i)
      have hMcast (i : Fin (n + 1)) : M' i.castSucc = M₀ i := Fin.lastCases_castSucc i
      have hMlast : M' (Fin.last (n + 1)) = M₁ := Fin.lastCases_last
      have hMsucc (i : Fin n) : M' i.castSucc.succ = M₀ i.succ := by
        rw [Fin.succ_castSucc, hMcast]
      have hMlastSucc : M' (Fin.last n).succ = M₁ := by rw [Fin.succ_last, hMlast]
      have hLlast : L (Fin.last n).succ = L (Fin.last (n + 1)) := by rw [Fin.succ_last]
      let g' : ∀ i : Fin (n + 1), M' i.castSucc ⟶ M' i.succ :=
        Fin.lastCases
          (eqToHom (hMcast (Fin.last n)) ≫ α' ≫ eqToHom hMlastSucc.symm)
          (fun i => eqToHom (hMcast i.castSucc) ≫ g₀ i ≫ eqToHom (hMsucc i).symm)
      let p' : ∀ i : Fin (n + 2), M' i ⟶ L i :=
        Fin.lastCases (eqToHom hMlast ≫ π ≫ eqToHom hLlast)
          (fun i => eqToHom (hMcast i) ≫ p₀ i)
      have hg_last : g' (Fin.last n) =
          eqToHom (hMcast (Fin.last n)) ≫ α' ≫ eqToHom hMlastSucc.symm := by
        unfold g'
        rw [Fin.lastCases_last]
      have hg_cast (i : Fin n) : g' i.castSucc =
          eqToHom (hMcast i.castSucc) ≫ g₀ i ≫ eqToHom (hMsucc i).symm := by
        unfold g'
        rw [Fin.lastCases_castSucc]
      have hp_last : p' (Fin.last (n + 1)) = eqToHom hMlast ≫ π ≫ eqToHom hLlast := by
        unfold p'
        rw [Fin.lastCases_last]
      have hp_cast (i : Fin (n + 1)) : p' i.castSucc = eqToHom (hMcast i) ≫ p₀ i := by
        unfold p'
        rw [Fin.lastCases_castSucc]
      refine ⟨M', g', p', ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
            rw [hg_last]
            exact isAdmissibleMono_congr (hMcast (Fin.last n)) hMlastSucc.symm α' hmono
        | cast i =>
            rw [hg_cast]
            exact isAdmissibleMono_congr (hMcast i.castSucc) (hMsucc i).symm (g₀ i) (hg₀ i)
      · intro i
        induction i using Fin.lastCases with
        | last =>
            rw [hp_last]
            have hπ : IsHomotopyEquivalence π := by
              refine ⟨s, hπs, ?_⟩
              rw [show Hom.comp π s = Hom.id (L (Fin.last n).succ) from hsπ]
              exact Homotopic.refl _
            exact isHomotopyEquivalence_congr hMlast hLlast π hπ
        | cast i =>
            rw [hp_cast]
            exact isHomotopyEquivalence_congr (hMcast i) rfl (p₀ i) (hp₀ i)
      · intro i
        induction i using Fin.lastCases with
        | last =>
            have hidx : (Fin.last n).succ = Fin.last (n + 1) := by simp
            have hpidx : p' (Fin.last n).succ = p' (Fin.last (n + 1)) := by cases hidx; rfl
            rw [hpidx]
            calc
              _ = eqToHom (hMcast (Fin.last n)) ≫ (α' ≫ π) ≫ eqToHom hLlast := by
                rw [hg_last, hp_last]
                show (eqToHom (hMcast (Fin.last n)) ≫ α' ≫
                    eqToHom hMlastSucc.symm ≫ eqToHom hMlast ≫ π ≫ eqToHom hLlast) =
                  (eqToHom (hMcast (Fin.last n)) ≫ (α' ≫ π) ≫ eqToHom hLlast)
                simp
              _ = eqToHom (hMcast (Fin.last n)) ≫ α ≫ eqToHom hLlast := by
                rw [hfactor]
              _ = Hom.comp (f (Fin.last n)) (p' (Fin.last n).castSucc) := by
                rw [hp_cast]
                show eqToHom (hMcast (Fin.last n)) ≫
                    (p₀ (Fin.last n) ≫ f (Fin.last n)) =
                  (eqToHom (hMcast (Fin.last n)) ≫ p₀ (Fin.last n)) ≫ f (Fin.last n)
                exact (Category.assoc _ _ _).symm
        | cast i =>
            calc
              _ = eqToHom (hMcast i.castSucc) ≫ (g₀ i ≫ p₀ i.succ) := by
                have hpTarget : p' i.castSucc.succ =
                    eqToHom (hMcast i.succ) ≫ p₀ i.succ := by
                  simpa only [Fin.succ_castSucc] using hp_cast i.succ
                rw [hg_cast, hpTarget]
                show (eqToHom (hMcast i.castSucc) ≫ g₀ i ≫
                    eqToHom (hMsucc i).symm ≫ eqToHom (hMcast i.succ) ≫ p₀ i.succ) =
                  (eqToHom (hMcast i.castSucc) ≫ (g₀ i ≫ p₀ i.succ))
                simp
              _ = eqToHom (hMcast i.castSucc) ≫ (p₀ i.castSucc ≫ f i.castSucc) :=
                congrArg (fun k => eqToHom (hMcast i.castSucc) ≫ k) (hcomm₀ i)
              _ = Hom.comp (f i.castSucc) (p' i.castSucc.castSucc) := by
                rw [hp_cast]
                show eqToHom (hMcast i.castSucc) ≫ Hom.comp (f₀ i) (p₀ i.castSucc) =
                  Hom.comp (f i.castSucc) (eqToHom (hMcast i.castSucc) ≫ p₀ i.castSucc)
                exact (Category.assoc _ _ _).symm

end DifferentialGradedModule
