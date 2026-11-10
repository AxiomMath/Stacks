module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Ext along an exact endofunctor isomorphic to the identity

An exact endofunctor of an abelian category with enough injectives which is isomorphic to the
identity acts on `Ext`-groups by conjugation with that isomorphism: carrying a class along the
functor and then transporting back along the components of the isomorphism returns the class.

The proof is dimension shifting in the target: in degree zero the statement is naturality of the
isomorphism, and the step from degree `n` to degree `n + 1` writes a class as a composite with
the class of an injective presentation and uses that an exact functor carries that class to the
class of the image presentation.

## Main results

* `Stacks.Homology.ext_mapExactFunctor_of_isoId` — the conjugation formula.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u

namespace Stacks.Homology

/-- An exact endofunctor `E` isomorphic to the identity acts on `Ext`-groups by conjugation: the
image `x.mapExactFunctor E` of a class `x : Ext A B n`, precomposed with the component of the
isomorphism at `A` and postcomposed with the component at `B`, is `x` again. -/
public theorem ext_mapExactFunctor_of_isoId {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] [EnoughInjectives C] (E : C ⥤ C) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] (β : E ≅ 𝟭 C) (A : C) :
    ∀ (n : ℕ) (B : C) (x : Ext.{w} A B n),
      (Ext.mk₀ (β.inv.app A)).comp
          ((x.mapExactFunctor E).comp (Ext.mk₀ (β.hom.app B)) (add_zero n)) (zero_add n) = x := by
  intro n
  induction n with
  | zero =>
    intro B x
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (X := A) (Y := B)).2 x
    rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
    congr 1
    rw [β.hom.naturality f]
    simp
  | succ n ih =>
    intro B x
    let I : InjectivePresentation B := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hinj : Injective S.X₂ := I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨y, rfl⟩ :=
      Ext.covariant_sequence_exact₁ A hS x (Ext.eq_zero_of_injective _) rfl
    let φ : S.map E ⟶ S :=
      { τ₁ := β.hom.app S.X₁
        τ₂ := β.hom.app S.X₂
        τ₃ := β.hom.app S.X₃
        comm₁₂ := by simp
        comm₂₃ := by simp }
    calc
      (Ext.mk₀ (β.inv.app A)).comp
            (((y.comp hS.extClass rfl).mapExactFunctor E).comp
              (Ext.mk₀ (β.hom.app S.X₁)) (add_zero (n + 1))) (zero_add (n + 1))
          = (Ext.mk₀ (β.inv.app A)).comp
              ((y.mapExactFunctor E).comp
                ((Ext.mk₀ (β.hom.app S.X₃)).comp hS.extClass (zero_add 1)) rfl)
              (zero_add (n + 1)) := by
            rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
              Ext.comp_assoc_of_third_deg_zero,
              ShortComplex.ShortExact.extClass_naturality (hS.map_of_exact E) hS φ]
      _ = ((Ext.mk₀ (β.inv.app A)).comp
              ((y.mapExactFunctor E).comp (Ext.mk₀ (β.hom.app S.X₃)) (add_zero n))
              (zero_add n)).comp hS.extClass rfl := by
            rw [Ext.comp_assoc _ _ _ (zero_add n) rfl (by lia),
              Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) (by lia)]
      _ = y.comp hS.extClass rfl := by rw [ih S.X₃ y]

end Stacks.Homology

end
