module

public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.Galois.Profinite
import StacksCore.Tactic.StacksAttribute

/-!
# Infinite Galois extensions as limits of finite ones

For a Galois extension `K/k`, the finite Galois subextensions form a directed system of
`k`-algebras with colimit `K`, and `Gal(K/k)` is the limit of their Galois groups as a profinite
group (Stacks 0BU2).
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace FiniteGaloisIntermediateField

universe u v

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/-- The finite Galois subextensions of `K/k`, ordered by inclusion, as a system of `k`-algebras;
the transition maps are the inclusions. -/
@[simps]
noncomputable def algCatFunctor : FiniteGaloisIntermediateField k K ⥤ AlgCat.{v} k where
  obj L := AlgCat.of k L
  map h := AlgCat.ofHom (IntermediateField.inclusion (leOfHom h))

/-- The cocone over `algCatFunctor k K` with point `K`, given by the inclusions `L → K`. -/
@[simps]
noncomputable def algCatCocone : Cocone (algCatFunctor k K) where
  pt := AlgCat.of k K
  ι := { app L := AlgCat.ofHom L.toIntermediateField.val }

/-- **Stacks 0BU2**. Let `K/k` be a Galois extension, and let `Λ` be the set of finite Galois
subextensions `K/L/k`, ordered by inclusion. Then
1. `Λ` is a (nonempty) directed partially ordered set;
2. the `L ∈ Λ` form a system of `k`-algebras over `Λ` and `K = colim L` (in the category of
  `k`-algebras);
3. the Galois groups `Gal(L/k)` form an inverse system of finite groups over `Λ` with surjective
  transition maps, and the restriction maps identify `Gal(K/k)` with `lim Gal(L/k)` as a
  profinite group;
4. each projection `Gal(K/k) → Gal(L/k)` is continuous and surjective. -/
@[stacks 0BU2]
theorem isDirected_isColimit_galoisGroup_isLimit [IsGalois k K] :
    (Nonempty (FiniteGaloisIntermediateField k K) ∧
      IsDirected (FiniteGaloisIntermediateField k K) (· ≤ ·)) ∧
    Nonempty (IsColimit (algCatCocone k K)) ∧
    ((∀ ⦃L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ⦄ (f : L₁ ⟶ L₂),
        Function.Surjective ((finGaloisGroupFunctor k K).map f).hom) ∧
      ∃ e : Gal(K/k) ≃ₜ* ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor k K),
        ∀ (L : FiniteGaloisIntermediateField k K) (σ : Gal(K/k)),
          InfiniteGalois.proj L (e σ) = AlgEquiv.restrictNormalHom L σ) ∧
    ∀ L : FiniteGaloisIntermediateField k K,
      Continuous (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) L) ∧
      Function.Surjective (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) L) := by
  have : Nonempty (FiniteGaloisIntermediateField k K) := ⟨⊥⟩
  refine ⟨⟨this, inferInstance⟩, ⟨?_⟩, ⟨fun L₁ L₂ f ↦ ?_,
    ⟨InfiniteGalois.continuousMulEquivToLimit k K, fun _ _ ↦ rfl⟩⟩,
    fun L ↦ ⟨InfiniteGalois.restrictNormalHom_continuous L.1,
      AlgEquiv.restrictNormalHom_surjective K⟩⟩
  · have : HasColimitsOfShape (FiniteGaloisIntermediateField k K) RingCat.{v} :=
      HasColimitsOfSize.has_colimits_of_shape _
    have : ReflectsColimitsOfShape (FiniteGaloisIntermediateField k K) (forget (AlgCat.{v} k)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    refine isColimitOfReflects (forget (AlgCat.{v} k)) (Types.FilteredColimit.isColimitOf _ _
      (fun (x : K) ↦ ⟨adjoin k {x}, ⟨x, subset_adjoin k {x} rfl⟩, rfl⟩) ?_)
    rintro L₁ L₂ ⟨x, hx⟩ ⟨y, hy⟩ (h : x = y)
    exact ⟨L₁ ⊔ L₂, homOfLE le_sup_left, homOfLE le_sup_right, Subtype.ext h⟩
  · let : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom f.1)
    have : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    exact AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := L₂.unop) L₁.unop

end FiniteGaloisIntermediateField
