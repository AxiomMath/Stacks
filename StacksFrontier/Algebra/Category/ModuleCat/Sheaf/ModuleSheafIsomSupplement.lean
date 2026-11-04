module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafIsom

/-!
# Supplement to `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ModuleSheafIsom`

Declarations used by the pro-étale comparison of Stacks 09B1 and 09A6, kept in their own module
so that `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafIsom` is unchanged.
-/


@[expose] public section
open CategoryTheory Opposite
universe u v w x u' v'

namespace Stacks.ConstantSheaf
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section Isom
variable (A : Type u') [Category.{v'} A]

/-- **Local isomorphisms glue over an object where sections are exact.** Let `W` be an object of
the site over which every locally surjective morphism of sheaves of sets is surjective on
sections, for instance a weakly contractible object. If two sheaves become isomorphic after
restriction to every member of a covering sieve of `W`, they are isomorphic after restriction to
`W`.

The sheaf `Isom(F, G)` then maps locally surjectively onto its image in the terminal sheaf, and
that image has a section over `W`; a preimage is an isomorphism `F|_W ≅ G|_W`. -/
theorem nonempty_overPullback_iso_of_mem {F G : Sheaf J A} {W : C}
    (hW : ∀ {P Q : Sheaf J (Type (max u v v'))} (φ : P ⟶ Q), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op W)))
    {R : Sieve W} (hR : R ∈ J W)
    (h : ∀ ⦃V : C⦄ ⦃f : V ⟶ W⦄, R f →
      Nonempty ((J.overPullback A V).obj F ≅ (J.overPullback A V).obj G)) :
    Nonempty ((J.overPullback A W).obj F ≅ (J.overPullback A W).obj G) := by
  have hT := Sheaf.isTerminalTerminal J (Limits.Types.isTerminalPUnit.{max u v v'})
  let φ : sheafIsom J A F G ⟶ Sheaf.terminal J (Limits.Types.isTerminalPUnit.{max u v v'}) :=
    hT.from (sheafIsom J A F G)
  have hmem : Subfunctor.sieveOfSection (Subfunctor.range φ.hom) PUnit.unit ∈ J W := by
    refine J.superset_covering (fun V f hf => ?_) hR
    obtain ⟨e⟩ := h hf
    exact ⟨⟨e.hom, (inferInstance : IsIso e.hom)⟩, rfl⟩
  obtain ⟨s, -⟩ := hW (Sheaf.toImage φ) inferInstance ⟨PUnit.unit, hmem⟩
  have : IsIso s.1 := s.2
  exact ⟨asIso s.1⟩


end Isom
end Stacks.ConstantSheaf
end
