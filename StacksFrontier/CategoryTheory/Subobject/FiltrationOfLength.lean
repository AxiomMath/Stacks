module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import StacksFrontier.CategoryTheory.Subobject.CokernelOfLE

/-!
# Finite filtrations with prescribed successive quotients

Let `P` be a property of objects of a category with zero morphisms and cokernels. An object `E`
*has a filtration of length `r` with successive quotients in `P`* when there is a chain of
subobjects

  `0 = E_0 ⊂ E_1 ⊂ ⋯ ⊂ E_r = E`

with every quotient `E_i / E_{i-1}` satisfying `P`. Recorded from the top, this says that `E` is
zero when `r = 0`, and otherwise `E` has a subobject `A` with `E / A` in `P` such that `A` has a
filtration of length `r - 1`; this is the inductive predicate
`CategoryTheory.ObjectProperty.HasFiltrationOfLength`.

Two operations are recorded. A functor which preserves monomorphisms, zero objects and
cokernels carries a filtration of `E` with quotients in `P` to a filtration of its image with
quotients in the image of `P`; this is how a filtration of a module is pulled back along a flat
morphism. And a filtration in the inductive sense is a filtration by subobjects in the sense of
a monotone family `F : Fin (r + 1) → Subobject E` with `F 0 = ⊥`, `F r = ⊤` and every
`F (i + 1) / F i` in `P`.

## Main definitions

* `CategoryTheory.ObjectProperty.HasFiltrationOfLength`: a filtration of length `r` with
  successive quotients in `P`.

## Main results

* `CategoryTheory.ObjectProperty.HasFiltrationOfLength.of_iso`: the property is invariant under
  isomorphism, when `P` is.
* `CategoryTheory.ObjectProperty.HasFiltrationOfLength.map`: a functor preserving monomorphisms,
  zero objects and cokernels carries filtrations to filtrations.
* `CategoryTheory.ObjectProperty.HasFiltrationOfLength.exists_subobject`: a filtration is a
  monotone chain of subobjects from `⊥` to `⊤` whose successive quotients are in `P`.
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.ObjectProperty

open Limits Subobject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]

/-- An object `E` has a *filtration of length `r` with successive quotients in `P`*: `E` is zero
when `r = 0`, and for `r + 1` it has a subobject `ι : A ⟶ E` whose quotient `cokernel ι` is in
`P` and such that `A` has a filtration of length `r`. Unfolded, this is a chain
`0 = E_0 ⊂ E_1 ⊂ ⋯ ⊂ E_r = E` with every `E_i / E_{i-1}` in `P`. -/
inductive HasFiltrationOfLength (P : ObjectProperty C) : ℕ → C → Prop
  | zero {E : C} : IsZero E → HasFiltrationOfLength P 0 E
  | succ {r : ℕ} {A E : C} (ι : A ⟶ E) [Mono ι] :
      HasFiltrationOfLength P r A → P (cokernel ι) → HasFiltrationOfLength P (r + 1) E

variable {P : ObjectProperty C}

/-- **Invariance under isomorphism.** If `E ≅ E'` and `E` has a filtration of length `r` with
quotients in `P`, so does `E'`, when `P` is closed under isomorphisms. -/
theorem HasFiltrationOfLength.of_iso [P.IsClosedUnderIsomorphisms] {r : ℕ} {E E' : C}
    (e : E ≅ E') (h : P.HasFiltrationOfLength r E) : P.HasFiltrationOfLength r E' := by
  cases h with
  | zero hE => exact .zero (hE.of_iso e.symm)
  | succ ι hA hq => exact .succ (ι ≫ e.hom) hA (P.prop_of_iso (cokernelCompIsIso ι e.hom).symm hq)

/-- **Images of filtrations.** Let `G : C ⥤ D` preserve monomorphisms, zero morphisms and
cokernels, and let `G` carry objects in `P` to objects in `Q`, a property closed under
isomorphisms. Then `G` carries a filtration of `E` of length `r` with quotients in `P` to a
filtration of `G E` of length `r` with quotients in `Q`: the image of `ι : A ⟶ E` is a
monomorphism `G A ⟶ G E` whose cokernel is `G (cokernel ι)`. -/
theorem HasFiltrationOfLength.map {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]
    [HasCokernels D] {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms] (G : C ⥤ D)
    [G.PreservesZeroMorphisms] [G.PreservesMonomorphisms]
    [PreservesColimitsOfShape WalkingParallelPair G] (hPQ : ∀ X, P X → Q (G.obj X))
    {r : ℕ} {E : C} (h : P.HasFiltrationOfLength r E) : Q.HasFiltrationOfLength r (G.obj E) := by
  induction h with
  | zero hE => exact .zero (G.map_isZero hE)
  | succ ι _ hq ih =>
    exact .succ (G.map ι) ih (Q.prop_of_iso (PreservesCokernel.iso G ι) (hPQ _ hq))

/-- **A filtration is a chain of subobjects.** If `E` has a filtration of length `r` with
quotients in `P`, a property closed under isomorphisms, then there is a monotone family
`F : Fin (r + 1) → Subobject E` with `F 0 = ⊥` and `F r = ⊤` such that every successive quotient
`F (i + 1) / F i` is in `P`. -/
theorem HasFiltrationOfLength.exists_subobject [HasZeroObject C] [P.IsClosedUnderIsomorphisms]
    {r : ℕ} {E : C}
    (h : P.HasFiltrationOfLength r E) :
    ∃ (F : Fin (r + 1) → Subobject E) (hF : Monotone F), F 0 = ⊥ ∧ F (Fin.last r) = ⊤ ∧
      ∀ i : Fin r, P (cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ))) := by
  induction h with
  | zero hE =>
    exact ⟨fun _ => ⊥, monotone_const, rfl, @Subsingleton.elim _ (subsingleton_of_isZero hE) _ _,
      fun i => i.elim0⟩
  | @succ r A E ι _ _ hq ih =>
    obtain ⟨F, hF, h0, hr, hP⟩ := ih
    let G : Fin (r + 1 + 1) → Subobject E := fun j =>
      if hj : (j : ℕ) < r + 1 then mk ((F ⟨j, hj⟩).arrow ≫ ι) else ⊤
    have hGlt : ∀ (j : Fin (r + 1 + 1)) (hj : (j : ℕ) < r + 1),
        G j = mk ((F ⟨j, hj⟩).arrow ≫ ι) := fun j hj => dif_pos hj
    have hGlast : G (Fin.last (r + 1)) = ⊤ := dif_neg (by simp)
    have hle : ∀ a b : Fin (r + 1), a ≤ b → mk ((F a).arrow ≫ ι) ≤ mk ((F b).arrow ≫ ι) :=
      fun a b hab => mk_le_mk_of_comm (ofLE _ _ (hF hab)) (by rw [ofLE_arrow_assoc])
    have hG : Monotone G := fun i j (hij' : (i : ℕ) ≤ j) => by
      by_cases hj : (j : ℕ) < r + 1
      · have hi : (i : ℕ) < r + 1 := hij'.trans_lt hj
        rw [hGlt i hi, hGlt j hj]
        exact hle ⟨i, hi⟩ ⟨j, hj⟩ hij'
      · exact le_top.trans_eq (show G j = ⊤ from dif_neg hj).symm
    refine ⟨G, hG, ?_, hGlast, fun i => ?_⟩
    · rw [hGlt 0 (by simp), mk_eq_bot_iff_zero]
      erw [h0]
      simp
    · have hic : ((i.castSucc : Fin (r + 1 + 1)) : ℕ) < r + 1 := by simp
      by_cases hi : (i : ℕ) < r
      · -- an inner step: the quotient is the quotient of the filtration of `A`
        let i' : Fin r := ⟨i, hi⟩
        have his : ((i.succ : Fin (r + 1 + 1)) : ℕ) < r + 1 := by simpa using hi
        have h₁ : G i.castSucc = mk ((F i'.castSucc).arrow ≫ ι) := hGlt _ hic
        have h₂ : G i.succ = mk ((F i'.succ).arrow ≫ ι) := hGlt _ his
        refine P.prop_of_iso
          (?_ ≪≫ (cokernelOfLEIsoOfEq _ (hle _ _ i'.castSucc_le_succ) h₁ h₂).symm) (hP i')
        refine (cokernel.mapIso _ (ofLE (F i'.castSucc) (F i'.succ) (hF i'.castSucc_le_succ))
          (underlyingIso _) (underlyingIso _) ?_).symm
        rw [ofLE_mk_le_mk_of_comm (ofLE _ _ (hF i'.castSucc_le_succ)) (by rw [ofLE_arrow_assoc])]
        simp
      · -- the top step: the quotient is `cokernel ι`
        have hir : (i : ℕ) = r := by omega
        have h₁ : G i.castSucc = mk ((F (Fin.last r)).arrow ≫ ι) := by
          rw [hGlt _ hic, show (⟨(i.castSucc : ℕ), hic⟩ : Fin (r + 1)) = Fin.last r from
            Fin.ext (by simpa using hir)]
        have h₂ : G i.succ = ⊤ := by
          rw [show i.succ = Fin.last (r + 1) from Fin.ext (by simp [hir]), hGlast]
        have : IsIso (F (Fin.last r)).arrow := by
          rw [hr]
          infer_instance
        refine P.prop_of_iso (?_ ≪≫ (cokernelOfLEIsoOfEq _ le_top h₁ h₂).symm) hq
        refine (cokernel.mapIso _ ι (underlyingIso _ ≪≫ asIso (F (Fin.last r)).arrow)
          (asIso (⊤ : Subobject E).arrow) ?_).symm
        simp [ofLE_arrow, underlyingIso_hom_comp_eq_mk]

end CategoryTheory.ObjectProperty

end
