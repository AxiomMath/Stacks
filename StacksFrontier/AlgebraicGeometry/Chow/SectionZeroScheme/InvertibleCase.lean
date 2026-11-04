module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.InvertibleStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularitySectionMultiplicationFieldDescent

/-!
# Intersecting with an invertible module whose section has a regular local equation

Let `(S, δ)` be the base situation of chapter 42, `X` locally of finite type over `S`, `ℒ` an
invertible module on `X` and `s ∈ Γ(X, ℒ)`. If `dim_δ(X) ≤ k + 1`, `dim_δ(Z(s)) ≤ k`, and at every
generic point of `Z(s)` of `δ`-dimension `k` the ideal of `Z(s)` in the local ring contains a
nonzerodivisor, then

  `c₁(ℒ) ∩ [X]_{k + 1} = [Z(s)]_k`  in  `CH_k(X)`.

This is [Stacks, Tag 02SQ] for the closed subscheme `X ⊆ X`, with its third hypothesis read off
the local equations of `Z(s)`
(`Stacks.Chow.SectionZeroScheme.injective_stalk_of_nonZeroDivisor_mem`). It is the case `r = 1`
of [Stacks, Tag 0FA9], and the claim inside the inductive step of the source's proof of that tag.

## Main results

* `Stacks.Chow.SectionZeroScheme.exists_sections_pullbackId` — a global section, read as a
  section of the pullback along the identity.
* `Stacks.Chow.SectionZeroScheme.firstChernClassCapOfInvertible_fundamental_eq_zeroScheme`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Chow.SectionZeroScheme

/-- A global section of `ℒ`, read as a compatible family of sections of the pullback of `ℒ`
along the identity. -/
theorem exists_sections_pullbackId {X : Scheme.{u}} (L : X.Modules) (s : Γ(L, ⊤)) :
    ∃ t : ((Scheme.Modules.pullback (𝟙 X)).obj L).sections,
      Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).app L).hom ⊤ (t.eval (op ⊤)) = s := by
  obtain ⟨σ, hσ⟩ := AlgebraicGeometry.exists_sections_val_top L s
  refine ⟨SheafOfModules.sectionsMap ((Scheme.Modules.pullbackId X).app L).inv σ, ?_⟩
  refine (Stacks.SheafOfModules.hom_val_app_inv_val_app ((Scheme.Modules.pullbackId X).app L)
    (op ⊤) (σ.val (op ⊤))).trans hσ

/-- **[Stacks, Tag 02SQ] for the whole scheme, with the third hypothesis read off local
equations.** -/
theorem firstChernClassCapOfInvertible_fundamental_eq_zeroScheme (C : ChowSituation.{u})
    {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    (hX : schemeDeltaDimension C q ≤ ((k + 1 : ℤ) : EInt))
    (hZ : schemeDeltaDimension C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ q) ≤
      (k : EInt))
    (hnzd : ∀ ξ : genericPoints (Stacks.Divisors.zeroScheme X L s).subscheme,
      relativeDimension C.dimensionFunction q
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ξ.1) = k →
        ∃ a ∈ nonZeroDivisors
            (X.presheaf.stalk ((Stacks.Divisors.zeroScheme X L s).subschemeι ξ.1)),
          a ∈ RingHom.ker ((Stacks.Divisors.zeroScheme X L s).subschemeι.stalkMap ξ.1).hom) :
    firstChernClassCapOfInvertible C q k L (cycleAssociatedToClosedSubscheme C q (𝟙 X) (k + 1)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C q
        (Stacks.Divisors.zeroScheme X L s).subschemeι k) := by
  obtain ⟨t, ht⟩ := exists_sections_pullbackId L s
  have hZeq : Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L)
      (t.eval (op ⊤)) = Stacks.Divisors.zeroScheme X L s :=
    AlgebraicGeometry.zeroScheme_eq_of_iso ((Scheme.Modules.pullbackId X).app L) ht
  have key : ∀ I : X.IdealSheafData, Stacks.Divisors.zeroScheme X
      ((Scheme.Modules.pullback (𝟙 X)).obj L) (t.eval (op ⊤)) = I →
      schemeDeltaDimension C (I.subschemeι ≫ q) ≤ (k : EInt) →
      (∀ ξ : genericPoints I.subscheme,
        relativeDimension C.dimensionFunction q (I.subschemeι ξ.1) = k →
          ∃ a ∈ nonZeroDivisors (X.presheaf.stalk (I.subschemeι ξ.1)),
            a ∈ RingHom.ker (I.subschemeι.stalkMap ξ.1).hom) →
      firstChernClassCapOfInvertible C q k L
          (cycleAssociatedToClosedSubscheme C q (𝟙 X) (k + 1)) =
        QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C q I.subschemeι k) := by
    intro I hI hZI hnzdI
    subst hI
    have hY : schemeDeltaDimension C (𝟙 X ≫ q) ≤ ((k + 1 : ℤ) : EInt) :=
      le_trans (le_of_eq (schemeDeltaDimension_congr C (Category.id_comp q))) hX
    have hD : schemeDeltaDimension C
        ((Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L)
          (t.eval (op ⊤))).subschemeι ≫ (𝟙 X ≫ q)) ≤ (k : EInt) :=
      le_trans (le_of_eq (schemeDeltaDimension_congr C
        (congrArg (fun φ => _ ≫ φ) (Category.id_comp q)))) hZI
    have hs : ∀ ξ : genericPoints (Stacks.Divisors.zeroScheme X
        ((Scheme.Modules.pullback (𝟙 X)).obj L) (t.eval (op ⊤))).subscheme,
        relativeDimension C.dimensionFunction (𝟙 X ≫ q)
          ((Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L)
            (t.eval (op ⊤))).subschemeι ξ.1) = k →
        Function.Injective (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
            ((Stacks.Divisors.zeroScheme X ((Scheme.Modules.pullback (𝟙 X)).obj L)
              (t.eval (op ⊤))).subschemeι ξ.1)).map
            ((Scheme.Modules.toPresheaf X).map
              (((Scheme.Modules.pullback (𝟙 X)).obj L).unitHomEquiv.symm t)))) := by
      intro ξ hξ
      rw [Category.id_comp] at hξ
      obtain ⟨a, ha, hmem⟩ := hnzdI ξ hξ
      exact injective_stalk_of_nonZeroDivisor_mem ((Scheme.Modules.pullback (𝟙 X)).obj L) t
        ξ.1.1 ξ.1.2 a ha hmem
    rw [Stacks.ChernCap42.firstChernClassCapOfInvertible_closedSubscheme_eq_zeroScheme
      C q (𝟙 X) k L t hY hD hs]
    exact congrArg QuotientAddGroup.mk
      (cycleAssociatedToClosedSubscheme_of_hom_eq C q (Category.comp_id _) k)
  exact key _ hZeq hZ hnzd

end Stacks.Chow.SectionZeroScheme

end
