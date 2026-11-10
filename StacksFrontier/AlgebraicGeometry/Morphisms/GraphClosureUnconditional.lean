module
public import StacksFrontier.AlgebraicGeometry.Morphisms.GraphClosure
import all StacksFrontier.AlgebraicGeometry.Morphisms.GraphClosure

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# GraphClosureUnconditional

Stronger forms of declarations of `StacksFrontier.AlgebraicGeometry.Morphisms.GraphClosure`,
stated as
separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace GraphClosure

variable {X S P : Scheme.{u}} (sX : X ⟶ S) (q : P ⟶ S) (U : X.Opens) (g : U.toScheme ⟶ P)
  (hg : g ≫ q = U.ι ≫ sX)

/-- The graphGeneral `U ⟶ X ×_S P` of a morphism `g : U ⟶ P` over `S`. -/
def graphGeneral : U.toScheme ⟶ pullback sX q :=
  pullback.lift U.ι g hg.symm

/-- The graphGeneral morphism is quasi-compact as soon as the open immersion of `U` is and `q` is
quasi-separated: the graphGeneral is a section of `X ×_S P ⟶ X` over `U`. -/
instance quasiCompact_graph [QuasiCompact U.ι] [QuasiSeparated q] :
    QuasiCompact (graphGeneral sX q U g hg) := by
  have : QuasiCompact (graphGeneral sX q U g hg ≫ pullback.fst sX q) := by
    rw [graphGeneral, pullback.lift_fst]
    infer_instance
  exact QuasiCompact.of_comp (graphGeneral sX q U g hg) (pullback.fst sX q)

end GraphClosure

end AlgebraicGeometry

end
