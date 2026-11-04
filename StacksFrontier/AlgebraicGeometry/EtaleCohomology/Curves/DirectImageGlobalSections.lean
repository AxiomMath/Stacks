module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage

/-!
# Global sections of a direct image on the small étale site

For a morphism of schemes `i : Y ⟶ X`, global sections on `X_étale` composed with the direct image
`i_*` are global sections on `Y_étale`.

The declaration belongs with
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage` and is placed in a
new module.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianDirectImageCompΓIso`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

/-- **Global sections on `X_étale` composed with the direct image along `i : Y ⟶ X` are global
sections on `Y_étale`.** The direct image is restriction along base change, so its composite
with sections over a terminal object `T` of `X_étale` is, on the nose, sections over the base
change `T ×_X Y`, which is a terminal object of `Y_étale`. -/
def etaleAbelianDirectImageCompΓIso :
    etaleAbelianDirectImage.{u, v} i ⋙
        Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ≅
      Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v} (terminalIsTerminal (C := X.Etale))) ≪≫
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}
      (isTerminalSmallEtaleBaseChangeObj i (terminalIsTerminal (C := X.Etale)))).symm

end Stacks.EtaleCohomology

end
