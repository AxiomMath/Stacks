module

public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Reverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of morphisms along a family with fully faithful descent-data functor

For a fibred category `p : 𝒳 ⥤ 𝒞` and a family `f i : X i ⟶ S`, a family of morphisms between the
chosen pullbacks of `x, y` over `S` whose base changes agree on common refinements is the family of
base changes of a unique morphism `x ⟶ y`, as soon as the descent-data functor of `f` is fully
faithful.

## Main results

* `CategoryTheory.Functor.comparison_comm_of_baseChangeFiberMor_eq`: equal base changes make the
  square of canonical comparisons of chosen pullbacks commute.
* `CategoryTheory.Functor.existsUnique_fiberHom_of_fullyFaithful_toDescentData`: unique descent of
  a compatible family of morphisms along such a family.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe w v₁ v₂ u₁ u₂

namespace Functor

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒞} [p.IsFibered]

/-- The converse of `CategoryTheory.Functor.baseChangeFiberMor_eq_of_comparison`: if two
morphisms between chosen pullbacks have the same base change to a common further object, the square
of canonical comparisons `CategoryTheory.Functor.pullbackFiberComparison` commutes. -/
lemma comparison_comm_of_baseChangeFiberMor_eq {S : 𝒞} {x y : p.Fiber S} {V W Z : 𝒞}
    {fx : V ⟶ S} {fy : W ⟶ S}
    (ψ : pullbackFiber p x fx ⟶ pullbackFiber p y fx)
    (ψ' : pullbackFiber p x fy ⟶ pullbackFiber p y fy)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) {q : Z ⟶ S} (h₁ : ε ≫ fx = q) (h₂ : ε' ≫ fy = q)
    (heq : ε ≫ fx = ε' ≫ fy)
    (hb : baseChangeFiberMor ψ ε q h₁ q h₁ = baseChangeFiberMor ψ' ε' q h₂ q h₂) :
    pullbackFiberHom ψ ε ≫ (pullbackFiberComparison y ε ε' heq).hom =
      (pullbackFiberComparison x ε ε' heq).hom ≫ pullbackFiberHom ψ' ε' := by
  rw [← pullbackFiberCompIso'_hom_comp_inv p x fx fy ε ε' q h₁ h₂ heq,
    ← pullbackFiberCompIso'_hom_comp_inv p y fx fy ε ε' q h₁ h₂ heq]
  rw [baseChangeFiberMor, baseChangeFiberMor, Iso.inv_comp_eq] at hb
  rw [← Category.assoc, hb]
  simp

/-- **Descent of morphisms along a family along which the descent-data functor is fully
faithful.** A family of morphisms `ψ i : (f i)^* x ⟶ (f i)^* y` between the chosen pullbacks, whose
base changes to any object mapping compatibly into two members agree, is the family of base changes
of a *unique* morphism `x ⟶ y` of the fibre over `S`, as soon as the functor from the fibre over
`S` to the descent data relative to `f` is fully faithful. -/
@[sga "3 IV 2.2" "partial"]
theorem existsUnique_fiberHom_of_fullyFaithful_toDescentData {S : 𝒞} {I : Type w} {X : I → 𝒞}
    (f : ∀ i, X i ⟶ S)
    (hff : Nonempty ((IsFibered.pullbackPseudofunctor p).toDescentData f).FullyFaithful)
    {x y : p.Fiber S}
    (ψ : ∀ i, pullbackFiber p x (f i) ⟶ pullbackFiber p y (f i))
    (hψ : ∀ (i j : I) {Z : 𝒞} (ε : Z ⟶ X i) (ε' : Z ⟶ X j) (q : Z ⟶ S)
      (h₁ : ε ≫ f i = q) (h₂ : ε' ≫ f j = q),
      baseChangeFiberMor (ψ i) ε q h₁ q h₁ = baseChangeFiberMor (ψ j) ε' q h₂ q h₂) :
    ∃! m : x ⟶ y, ∀ i, pullbackFiberHom m (f i) = ψ i := by
  obtain ⟨hff⟩ := hff
  let ξ : ((IsFibered.pullbackPseudofunctor p).toDescentData f).obj x ⟶
      ((IsFibered.pullbackPseudofunctor p).toDescentData f).obj y :=
    { hom := ψ
      comm := by
        intro Z q i j ε ε' h₁ h₂
        erw [pullbackPseudofunctor_map_map p ε (ψ i), pullbackPseudofunctor_map_map p ε' (ψ j),
          toDescentData_obj_hom p f y q ε ε' h₁ h₂ (h₁.trans h₂.symm),
          toDescentData_obj_hom p f x q ε ε' h₁ h₂ (h₁.trans h₂.symm)]
        exact comparison_comm_of_baseChangeFiberMor_eq (ψ i) (ψ j) ε ε' h₁ h₂ (h₁.trans h₂.symm)
          (hψ i j ε ε' q h₁ h₂) }
  have key (i : I) (m : x ⟶ y) : pullbackFiberHom m (f i) =
      (((IsFibered.pullbackPseudofunctor p).toDescentData f).map m).hom i :=
    pullbackPseudofunctor_map_map p (f i) m
  refine ⟨hff.preimage ξ, fun i ↦ ?_, fun m hm ↦ hff.map_injective ?_⟩
  · exact (key i _).trans (congrArg (fun η ↦ Pseudofunctor.DescentData.Hom.hom η i)
      (hff.map_preimage ξ))
  · refine (Pseudofunctor.DescentData.hom_ext fun i ↦ ?_).trans (hff.map_preimage ξ).symm
    exact (key i m).trans (hm i)

end Functor

end CategoryTheory

end
