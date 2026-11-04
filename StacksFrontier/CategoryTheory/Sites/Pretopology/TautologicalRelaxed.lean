module

public import StacksFrontier.CategoryTheory.Sites.Pretopology.EquivalenceComparison
public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# Tautologically equivalent families impose the same sheaf condition

Stacks tag 00VW: if two families of morphisms with the same fixed target — Mathlib's
`CategoryTheory.PreZeroHypercover` — are tautologically equivalent, then a presheaf satisfies
the sheaf condition for one exactly when it satisfies it for the other.

## The fibre products the source assumes are not needed

00VW assumes the fibre products `U_i ×_U U_{i'}` and `V_j ×_U V_{j'}` exist, because it states
the sheaf condition as the equalizer diagram of 00VN, which is written with them. Mathlib's
`Presieve.IsSheafFor` is the sheaf condition for an arbitrary presieve and needs no fibre
products; where they do exist the two agree. The statement below is therefore the source's
conclusion under strictly weaker hypotheses.

The proof is now one line of content: `Presieve.isSheafFor_iff_generate` reduces both sides to
the generated sieve, and tautologically equivalent families generate the same sieve
(`generate_presieve₀_eq_of_tautologicallyEquivalent`, from 00VV (2)).
-/

@[expose] public section

namespace CategoryTheory.PreZeroHypercover

universe w w' t v u

variable {C : Type u} [Category.{v} C] {U : C}

/-- **Stacks 00VW.** Tautologically equivalent families of morphisms with a fixed target
generate the same sieve, hence impose the same sheaf condition on every presheaf. -/
@[stacks 00VW]
theorem isSheafFor_presieve₀_iff_of_tautologicallyEquivalent
    (E : PreZeroHypercover.{w} U) (F : PreZeroHypercover.{w'} U)
    (h : TautologicallyEquivalent E F) (P : Cᵒᵖ ⥤ Type t) :
    Presieve.IsSheafFor P E.presieve₀ ↔ Presieve.IsSheafFor P F.presieve₀ := by
  rw [Presieve.isSheafFor_iff_generate (R := E.presieve₀),
    Presieve.isSheafFor_iff_generate (R := F.presieve₀),
    generate_presieve₀_eq_of_tautologicallyEquivalent E F h]

end CategoryTheory.PreZeroHypercover
