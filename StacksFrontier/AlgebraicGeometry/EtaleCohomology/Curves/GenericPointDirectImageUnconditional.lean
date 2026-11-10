module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IrreducibleGenericPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf

/-!
# GenericPointDirectImageUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage`, stated as
separate
declarations beside the ones there: over more general coefficient universes, or with inputs that
are carried there as hypotheses discharged, together with the new results built on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section DirectImage

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

/-- **Global sections on `X_étale` composed with the direct image along `i : Y ⟶ X` are global
sections on `Y_étale`.** The direct image is restriction along base change, so its composite
with sections over a terminal object `T` of `X_étale` is, on the nose, sections over the base
change `T ×_X Y`, which is a terminal object of `Y_étale`. -/
def etaleAbelianDirectImageCompGlobalSectionsIsoUniv :
    etaleAbelianDirectImage.{u, v} i ⋙
        Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ≅
      Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v} (terminalIsTerminal (C := X.Etale))) ≪≫
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}
      (isTerminalSmallEtaleBaseChangeObj i (terminalIsTerminal (C := X.Etale)))).symm

end DirectImage

section GenericPoint

variable (X : Scheme.{u}) [IrreducibleSpace X]

end GenericPoint

section Comparison

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

end Comparison

end Stacks.EtaleCohomology

end
