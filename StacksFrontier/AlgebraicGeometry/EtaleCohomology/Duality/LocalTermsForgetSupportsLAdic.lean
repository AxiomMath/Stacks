module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocalTermsForgetSupports
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.BoundaryLocalTerms

/-!
# Forgetting supports for an ℓ-adic sheaf whose local terms at the boundary are bounded

Let `F` be an ℓ-adic sheaf on `U` with a compactification `j : U ⟶ X̄` over `k`, and let
`j' : U_k̄ ⟶ X̄_k̄` be the base change of `j` and `Gₙ = Fₙ|_{U_k̄}`. If the local terms of `F` at
the boundary are killed by `ℓ^K` (`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy`), then
for every level `n` the forget supports map `H¹_c(U_k̄, Gₙ) → H¹(U_k̄, Gₙ)` has kernel killed by
`ℓ^K` and cokernel killed by `ℓ^{2K}`, uniformly in `n`. This is the comparison through which
Poincaré duality on `X̄_k̄` pairs `H¹_c(U_k̄, Fₙ)` with `H¹_c(U_k̄, F'ₙ)`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.forgetSupports_bounds_of_localTermsKilledBy`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
  AlgebraicGeometry.SmallEtale Stacks.Frobenius
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian U.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] (f : U.1 ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **Forgetting supports for an ℓ-adic sheaf with bounded local terms.** If the local terms of
`F` at the boundary are killed by `ℓ^K`, then at every level `n` the forget supports map
`w ↦ extMap (w ∘ (j'_! Gₙ ↪ j'_* Gₙ)) : H¹_c(U_k̄, Gₙ) → H¹(U_k̄, Gₙ)` has kernel killed by `ℓ^K`
and `ℓ^K · ℓ^K` times every class of `H¹(U_k̄, Gₙ)` in its image. -/
theorem LAdicSheaf.forgetSupports_bounds_of_localTermsKilledBy (F : LAdicSheaf B U ℓ) {K : ℕ}
    (hF : LAdicSheaf.LocalTermsKilledBy B U ℓ f j kbar F K) (n : ℕ) :
    (∀ w : Ext (unitSheaf (X := fieldBaseChange j.obj.right kbar) (ℓ ^ (n + 1)))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeMap j.obj.hom kbar)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj (LAdicSheaf.etaleLevel B U ℓ F n))) 1,
      Stacks.ExtAdjunction.extMap (etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeMap j.obj.hom kbar)) _ _ 1
        (w.comp (Ext.mk₀ ((etaleModuleExtensionByZeroToDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeMap j.obj.hom kbar)).app _)) (add_zero 1)) = 0 → (ℓ ^ K) • w = 0) ∧
      ∀ x : Ext ((etaleModuleRestriction.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeMap j.obj.hom kbar)).obj
            (unitSheaf (X := fieldBaseChange j.obj.right kbar) (ℓ ^ (n + 1))))
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj (LAdicSheaf.etaleLevel B U ℓ F n)) 1,
        ∃ w : Ext (unitSheaf (X := fieldBaseChange j.obj.right kbar) (ℓ ^ (n + 1)))
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeMap j.obj.hom kbar)).obj
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (fieldBaseChangeProj (Over.mk f) kbar)).obj (LAdicSheaf.etaleLevel B U ℓ F n))) 1,
          Stacks.ExtAdjunction.extMap (etaleModuleRestrictionDirectImageAdj.{u, 0}
              (ZMod (ℓ ^ (n + 1))) (fieldBaseChangeMap j.obj.hom kbar)) _ _ 1
            (w.comp (Ext.mk₀ ((etaleModuleExtensionByZeroToDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (fieldBaseChangeMap j.obj.hom kbar)).app _)) (add_zero 1)) = (ℓ ^ K * ℓ ^ K) • x := by
  have : IsOpenImmersion j.obj.hom.left := j.property.1
  have : IsOpenImmersion (fieldBaseChangeMap j.obj.hom kbar) :=
    have : MorphismProperty.IsStableUnderComposition @IsOpenImmersion.{u} :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      (inferInstanceAs (IsOpenImmersion j.obj.hom.left))
      (inferInstanceAs (IsOpenImmersion (𝟙 _))) (Over.w j.obj.hom).symm (Category.id_comp _).symm
  exact forgetSupports_bounds_extensionByZero _ _ (hF n).1 (hF n).2

end Stacks.EtaleCohomology

end
