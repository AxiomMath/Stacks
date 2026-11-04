module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechGaps.ShortExact

/-!
# Čech cochains of an abelian presheaf on a space: the element-level calculus

`Stacks.CechGaps.cech_X` and `Stacks.CechGaps.cech_d_comp_π` identify Mathlib's
`CategoryTheory.cechComplexFunctor` degreewise: its term in degree `n` is the product of the
sections of the presheaf over the Čech opens `∏ᶜ (U ∘ x)`, and its differential is the alternating
sum of the restrictions along the faces. This file states on elements how a map of presheaves, the
differential and the projections interact, and two degree-specific facts about a `0`-cochain: when
its differential vanishes, and what the vanishing says.

## Main results

* `Stacks.CechElementChase.cech_ext`, `Stacks.CechElementChase.cech_eq_zero`: an element of a Čech
  term is determined by its components.
* `Stacks.CechElementChase.cechMap_π_apply`: the component of the image of a cochain under the map
  induced by `α : P ⟶ Q` is `α` applied to the component.
* `Stacks.CechElementChase.cechMap_d_apply`: the induced map is a chain map, on elements.
* `Stacks.CechElementChase.cechD_zero_apply`: `d⁰` on elements, as a difference of two
  restrictions.
* `Stacks.CechElementChase.cechD_zero_eq_zero_of_restrict`: a `0`-cochain whose components are all
  restrictions of one section of `P` over an open containing the Čech opens is a cocycle.
* `Stacks.CechElementChase.zeroCocycle_agree`: the components of a `0`-cocycle agree on any open
  contained in two of the Čech opens.
* `Stacks.CechElementChase.exists_coboundary_of_cocycle`: in a cochain complex of abelian groups
  with vanishing degree-`1` homology, a `1`-cocycle is a coboundary.

## References

* [Stacks Project, Tag 01EU](https://stacks.math.columbia.edu/tag/01EU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CechGaps

universe u

namespace Stacks.CechElementChase

variable {X : Type u} [TopologicalSpace X]

section Restriction

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- Restricting along `B ≤ A` and then along `C ≤ B` is restricting along `C ≤ A`. -/
lemma map_homOfLE_comp {A B C : Opens X} (h₁ : C ≤ B) (h₂ : B ≤ A)
    (s : ToType (P.obj (op A))) :
    P.map (homOfLE h₁).op (P.map (homOfLE h₂).op s) = P.map (homOfLE (h₁.trans h₂)).op s := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  rfl

end Restriction

variable {ι : Type u} (U : ι → Opens X)

/-- A Čech open is contained in each of the members of the family it is formed from. -/
lemma prodOpens_le_obj {n : ℕ} (x : Fin n → ι) (k : Fin n) :
    (∏ᶜ (U ∘ x) : Opens X) ≤ U (x k) :=
  (Limits.Pi.π (U ∘ x) k).le

/-- A member of the family is contained in the Čech open of the constant `0`-simplex at it. -/
lemma obj_le_prodOpens_const (i : ι) :
    U i ≤ (∏ᶜ (U ∘ (fun _ : Fin 1 ↦ i)) : Opens X) := by
  rw [prodOpens_eq_iInf]
  exact le_iInf fun _ ↦ le_refl _

variable (P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- An element of a Čech term is determined by its components. -/
lemma cech_ext (n : ℕ) (a b : ToType (((cechComplexFunctor U).obj P).X n))
    (h : ∀ x, Limits.Pi.π (cechDeg U P n) x a = Limits.Pi.π (cechDeg U P n) x b) : a = b :=
  pi_ext a b h

/-- The components of the zero cochain vanish. -/
lemma cech_π_zero (n : ℕ) (x : Fin (n + 1) → ι) :
    Limits.Pi.π (cechDeg U P n) x (0 : ToType (((cechComplexFunctor U).obj P).X n)) = 0 :=
  map_zero _

/-- A Čech cochain all of whose components vanish is zero. -/
lemma cech_eq_zero (n : ℕ) (a : ToType (((cechComplexFunctor U).obj P).X n))
    (h : ∀ x, Limits.Pi.π (cechDeg U P n) x a = 0) : a = 0 :=
  cech_ext U P n a 0 fun x ↦ (h x).trans (cech_π_zero U P n x).symm

/-- A component of the image of a cochain under the map induced by `α : P ⟶ Q` is `α` applied to
the corresponding component of the cochain. -/
lemma cechMap_π_apply (α : P ⟶ Q) (n : ℕ)
    (a : ToType (((cechComplexFunctor U).obj P).X n)) (x : Fin (n + 1) → ι) :
    Limits.Pi.π (cechDeg U Q n) x (((cechComplexFunctor U).map α).f n a)
      = α.app (op (∏ᶜ (U ∘ x))) (Limits.Pi.π (cechDeg U P n) x a) :=
  piMap_π_apply _ a x

/-- The map of Čech complexes induced by `α : P ⟶ Q` commutes with the differentials, on
elements. -/
lemma cechMap_d_apply (α : P ⟶ Q) (n m : ℕ)
    (a : ToType (((cechComplexFunctor U).obj P).X n)) :
    ((cechComplexFunctor U).map α).f m (((cechComplexFunctor U).obj P).d n m a)
      = ((cechComplexFunctor U).obj Q).d n m (((cechComplexFunctor U).map α).f n a) := by
  simpa only [ConcreteCategory.comp_apply] using
    (ConcreteCategory.congr_hom (((cechComplexFunctor U).map α).comm n m) a).symm

/-- Two consecutive differentials annihilate a cochain. -/
lemma cech_d_d_apply (n m k : ℕ) (a : ToType (((cechComplexFunctor U).obj P).X n)) :
    ((cechComplexFunctor U).obj P).d m k (((cechComplexFunctor U).obj P).d n m a) = 0 := by
  simpa only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
    using ConcreteCategory.congr_hom (((cechComplexFunctor U).obj P).d_comp_d n m k) a

/-- The differential `d⁰` of the Čech complex on elements: the difference of the restrictions
along the faces `Fin.succAbove 0` and `Fin.succAbove 1`. -/
lemma cechD_zero_apply (t : ToType (((cechComplexFunctor U).obj P).X 0)) (x : Fin 2 → ι) :
    Limits.Pi.π (cechDeg U P 1) x (((cechComplexFunctor U).obj P).d 0 1 t)
      = P.map (homOfLE (prodOpens_le U x ((0 : Fin 2).succAbove))).op
          (Limits.Pi.π (cechDeg U P 0) (x ∘ (0 : Fin 2).succAbove) t)
        - P.map (homOfLE (prodOpens_le U x ((1 : Fin 2).succAbove))).op
            (Limits.Pi.π (cechDeg U P 0) (x ∘ (1 : Fin 2).succAbove) t) := by
  rw [cech_d_apply U P 0 t x, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

/-- If every component of the `0`-cochain `t` is the restriction of a fixed `s : P(W)`, then
`d⁰ t = 0`. -/
lemma cechD_zero_eq_zero_of_restrict {W : Opens X} (s : ToType (P.obj (op W)))
    (hle : ∀ y : Fin 1 → ι, (∏ᶜ (U ∘ y) : Opens X) ≤ W)
    (t : ToType (((cechComplexFunctor U).obj P).X 0))
    (ht : ∀ y, Limits.Pi.π (cechDeg U P 0) y t = P.map (homOfLE (hle y)).op s) :
    ((cechComplexFunctor U).obj P).d 0 1 t = 0 := by
  refine cech_eq_zero U P 1 _ fun x ↦ ?_
  rw [cechD_zero_apply, ht, ht, map_homOfLE_comp, map_homOfLE_comp, sub_self]

/-- The components of a `0`-cocycle agree on any open contained in two of the Čech opens. -/
lemma zeroCocycle_agree {t : ToType (((cechComplexFunctor U).obj P).X 0)}
    (ht : ((cechComplexFunctor U).obj P).d 0 1 t = 0) (y z : Fin 1 → ι) (O : Opens X)
    (hy : O ≤ ∏ᶜ (U ∘ y)) (hz : O ≤ ∏ᶜ (U ∘ z)) :
    P.map (homOfLE hy).op (Limits.Pi.π (cechDeg U P 0) y t)
      = P.map (homOfLE hz).op (Limits.Pi.π (cechDeg U P 0) z t) := by
  have key : ∀ x : Fin 2 → ι, ∀ (O' : Opens X)
      (hy' : O' ≤ ∏ᶜ (U ∘ (x ∘ (0 : Fin 2).succAbove)))
      (hz' : O' ≤ ∏ᶜ (U ∘ (x ∘ (1 : Fin 2).succAbove))),
      P.map (homOfLE hy').op (Limits.Pi.π (cechDeg U P 0) (x ∘ (0 : Fin 2).succAbove) t)
        = P.map (homOfLE hz').op
            (Limits.Pi.π (cechDeg U P 0) (x ∘ (1 : Fin 2).succAbove) t) := by
    intro x O' hy' hz'
    have hsum := cechD_zero_apply U P t x
    rw [ht, cech_π_zero] at hsum
    have hO : O' ≤ (∏ᶜ (U ∘ x) : Opens X) := by
      rw [prodOpens_eq_iInf]
      refine le_iInf (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · exact hz'.trans (prodOpens_le_obj U (x ∘ (1 : Fin 2).succAbove) 0)
      · exact hy'.trans (prodOpens_le_obj U (x ∘ (0 : Fin 2).succAbove) 0)
    simpa only [map_homOfLE_comp] using congrArg (P.map (homOfLE hO).op) (sub_eq_zero.1 hsum.symm)
  have h0 : (fun m : Fin 2 ↦ if m = 0 then z 0 else y 0) ∘ (0 : Fin 2).succAbove = y := by
    funext k; obtain rfl : k = 0 := Fin.fin_one_eq_zero k; rfl
  have h1 : (fun m : Fin 2 ↦ if m = 0 then z 0 else y 0) ∘ (1 : Fin 2).succAbove = z := by
    funext k; obtain rfl : k = 0 := Fin.fin_one_eq_zero k; rfl
  have hkey := key (fun m : Fin 2 ↦ if m = 0 then z 0 else y 0)
  rw [h0, h1] at hkey
  exact hkey O hy hz

/-- In a cochain complex of abelian groups with vanishing degree-`1` homology, a `1`-cocycle is a
coboundary. -/
lemma exists_coboundary_of_cocycle (K : CochainComplex AddCommGrpCat.{u} ℕ)
    (hK : IsZero (K.homology 1)) (c : ToType (K.X 1)) (hc : K.d 1 2 c = 0) :
    ∃ b : ToType (K.X 0), K.d 0 1 b = c := by
  have hE : K.ExactAt 1 := (K.exactAt_iff_isZero_homology 1).2 hK
  rw [K.exactAt_iff' 0 1 2 (by simp) (by simp), ShortComplex.ab_exact_iff] at hE
  exact hE c hc

end Stacks.CechElementChase
