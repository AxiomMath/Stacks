module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsom

/-!
# Supplement to `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ConstantSheafIsom`

Declarations used by the pro-étale comparison of Stacks 09B1 and 09A6, kept in their own module
so that `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsom` is unchanged.
-/


@[expose] public section
open CategoryTheory Opposite
universe u v w x t

namespace Stacks.ConstantSheaf

/-! ### Sheafification of presheaves of modules in a universe containing the site -/

section ModuleSheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [UnivLE.{max u v, t}]
  (R : Type w) [Ring R]

/-- **`J.W` is local bijectivity for presheaves of modules** at any module universe containing the
site: the plus-plus sheafification of presheaves of modules is computed on the underlying
presheaves of types, where it is locally bijective. Mathlib provides this only when the carrier
universe is `max u v`. -/
instance wEqualsLocallyBijective_moduleCat_of_univLE :
    J.WEqualsLocallyBijective (ModuleCat.{t} R) := by
  have : ∀ P : Cᵒᵖ ⥤ ModuleCat.{t} R,
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) := fun P => by
    have := GrothendieckTopology.isLocallyInjective_toSheafify_type_of_univLE J
      (P ⋙ forget (ModuleCat.{t} R))
    rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    infer_instance
  have : ∀ P : Cᵒᵖ ⥤ ModuleCat.{t} R,
      Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) := fun P => by
    have := GrothendieckTopology.isLocallySurjective_toSheafify_type_of_univLE J
      (P ⋙ forget (ModuleCat.{t} R))
    rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    infer_instance
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' J (ModuleCat.{t} R)

end ModuleSheafification


end Stacks.ConstantSheaf
end


@[expose] public section
open CategoryTheory Opposite
universe u v w x t

namespace Stacks.ConstantSheaf

/-! ### Constant sheaves which are locally isomorphic have isomorphic values -/

section Values

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type w) [CommRing Λ]

/-- **Isomorphic constant sheaves have isomorphic values.** Let `M` and `N` be finitely presented
`Λ`-modules and let `V` be an object of the site over which the empty sieve is not covering. If
the constant sheaves `M̲` and `N̲` become isomorphic after restriction to `C/V`, then `M` and `N`
are isomorphic. -/
theorem nonempty_linearEquiv_of_iso (M N : ModuleCat.{max u v x} Λ)
    [Module.FinitePresentation Λ (M : Type (max u v x))]
    [Module.FinitePresentation Λ (N : Type (max u v x))] {V : C} (hV : (⊥ : Sieve V) ∉ J V)
    (e : (J.overPullback (ModuleCat.{max u v x} Λ) V).obj
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M) ≅
      (J.overPullback (ModuleCat.{max u v x} Λ) V).obj
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N)) :
    Nonempty ((M : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x))) := by
  -- By Tag 093T (2) an isomorphism `M̲|_V ≅ N̲|_V` is a section over `V` of the constant sheaf on
  -- `M ≃ₗ[Λ] N`, which is locally a constant section, and some member of a covering sieve of `V`
  -- exists.
  let s : (moduleSheafIsom J Λ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)
      ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N)).obj.obj (op V) :=
    ⟨e.hom, (inferInstance : IsIso e.hom)⟩
  have hsurj := isLocallySurjective_toSheafify_type.{u, v, max u v x} J
    ((Functor.const Cᵒᵖ).obj ((M : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x))))
  have hS := Presheaf.imageSieve_mem J
    (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
      ((M : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x)))))
    (((constantSheafIsomIso J Λ M N).inv.hom.app (op V)) s)
  by_contra h
  refine hV (J.superset_covering ?_ hS)
  rintro W f ⟨x, -⟩
  exact (h ⟨x⟩).elim

end Values


end Stacks.ConstantSheaf
end
