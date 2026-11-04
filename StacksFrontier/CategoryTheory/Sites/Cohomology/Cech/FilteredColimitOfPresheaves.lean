module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CofilteredLimitOfFamilies
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeZeroAndSheafCondition

/-!
# Čech complexes of a filtered colimit of presheaves

Let `E = {U_i → U}` be a finite family of morphisms with fixed target whose iterated fibre products
exist, and let `P` be an abelian presheaf together with a directed system of abelian presheaves
`P_k` and maps `φ_k : P_k ⟶ P` compatible with the transition maps. If on each iterated fibre
product `U_{i_0} ×_U ⋯ ×_U U_{i_p}` the sections of `P` are, elementwise, the colimit of the
sections of the `P_k` — every section comes from some `P_k`, and a section of `P_k` which vanishes
in `P` vanishes in some `P_l` — then the Čech complex of `P` is exact in every degree in which the
Čech complexes of all the `P_k` are.

## Main results

* `Stacks.CechSite.exactAt_cechComplex_of_forall_exists` — exactness of the Čech complex of a
  presheaf which is elementwise the filtered colimit, on the iterated fibre products of the family,
  of presheaves with exact Čech complexes.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CechSite

universe a w v u t

variable {C : Type u} [Category.{v} C] {U : C} (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasProducts.{w} AddCommGrpCat.{a}]
  {Λ : Type t} [Preorder Λ] {P : Cᵒᵖ ⥤ AddCommGrpCat.{a}} {Pk : Λ → Cᵒᵖ ⥤ AddCommGrpCat.{a}}
  (φ : ∀ k, Pk k ⟶ P) (ψ : ∀ {k l : Λ}, k ≤ l → (Pk k ⟶ Pk l))
  (hψ : ∀ {k l : Λ} (h : k ≤ l), ψ h ≫ φ l = φ k)
  (hψcomp : ∀ {k l m : Λ} (h₁ : k ≤ l) (h₂ : l ≤ m), ψ (h₁.trans h₂) = ψ h₁ ≫ ψ h₂)

include hψ hψcomp in
/-- **The Čech complex of a filtered colimit of presheaves.** If on every iterated fibre product of
a finite family `E` the sections of `P` are elementwise the directed colimit of the sections of the
presheaves `P_k`, then the Čech complex of `P` is exact in every degree in which those of all the
`P_k` are. -/
theorem exactAt_cechComplex_of_forall_exists [Finite E.I₀] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (hsurj : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀) (x : cochainFactor E P n i),
      ∃ (k : Λ) (y : cochainFactor E (Pk k) n i),
        (φ k).app (op ((∏ᶜ (fun j ↦ Over.mk (E.f (i j))) : Over U).left)) y = x)
    (hinj : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀) (k : Λ) (y : cochainFactor E (Pk k) n i),
      (φ k).app (op ((∏ᶜ (fun j ↦ Over.mk (E.f (i j))) : Over U).left)) y = 0 →
        ∃ (l : Λ) (h : k ≤ l),
          (ψ h).app (op ((∏ᶜ (fun j ↦ Over.mk (E.f (i j))) : Over U).left)) y = 0)
    (p : ℕ) (hexact : ∀ k, (cechComplex E (Pk k)).ExactAt p) :
    (cechComplex E P).ExactAt p := by
  classical
  refine HomologicalComplex.exactAt_of_forall_exists _ p (fun k ↦ cechComplex E (Pk k))
    (fun k ↦ (cechComplexFunctor E).map (φ k)) hexact ?_ ?_
  · intro x
    choose k y hy using fun i ↦ hsurj p i ((productAddEquiv (cochainFactor E P p)) x i)
    obtain ⟨m, hk⟩ := Finite.exists_le k
    refine ⟨m, (productAddEquiv (cochainFactor E (Pk m) p)).symm fun i ↦
      (ψ (hk i)).app _ (y i), (productAddEquiv (cochainFactor E P p)).injective
        (funext fun i ↦ ?_)⟩
    refine (cechComplexFunctor_map_f_π_apply E (φ m) p i _).trans ?_
    show (φ m).app _ ((productAddEquiv (cochainFactor E (Pk m) p))
      ((productAddEquiv (cochainFactor E (Pk m) p)).symm fun i ↦ (ψ (hk i)).app _ (y i)) i) = _
    rw [AddEquiv.apply_symm_apply, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, hψ, hy]
  · intro k y hy
    have hcomp : ∀ i, (φ k).app _
        (Pi.π (cochainFactor E (Pk k) ((ComplexShape.up ℕ).next p)) i y) = 0 := fun i ↦ by
      have := congrArg (ConcreteCategory.hom
        (Pi.π (cochainFactor E P ((ComplexShape.up ℕ).next p)) i)) hy
      exact (cechComplexFunctor_map_f_π_apply E (φ k) _ i y).symm.trans
        (this.trans (map_zero _))
    choose l hl hly using fun i ↦ hinj _ i k _ (hcomp i)
    obtain ⟨m, hm⟩ := Finite.exists_le (Option.elim · k l)
    have hkm : k ≤ m := hm none
    have hlm : ∀ i, l i ≤ m := fun i ↦ hm (some i)
    refine ⟨m, (cechComplexFunctor E).map (ψ hkm), ?_, ?_⟩
    · rw [← Functor.map_comp, hψ]
    · refine (productAddEquiv (cochainFactor E (Pk m) _)).injective
        (Eq.trans ?_ (map_zero (productAddEquiv (cochainFactor E (Pk m) _))).symm)
      funext i
      refine (cechComplexFunctor_map_f_π_apply E (ψ hkm) _ i y).trans ?_
      refine (congrArg (fun f : Pk k ⟶ Pk m ↦ ConcreteCategory.hom
        (f.app (op ((∏ᶜ (fun j ↦ Over.mk (E.f (i j))) : Over U).left)))
          (Pi.π (cochainFactor E (Pk k) _) i y)) (hψcomp (hl i) (hlm i))).trans ?_
      rw [NatTrans.comp_app, ConcreteCategory.comp_apply, hly i, map_zero]
      rfl

end Stacks.CechSite
