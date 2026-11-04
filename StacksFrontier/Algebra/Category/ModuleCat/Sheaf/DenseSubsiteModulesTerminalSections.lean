module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.CategoryTheory.Sites.DenseSubsiteTerminalSections

/-!
# Sections of a sheaf of modules over a terminal object, on a dense subsite

Let `v : C ⥤ C'` exhibit `(C, J)` as a dense subsite of `(C', K)`, let `R` be a sheaf of rings on
`(C', K)` and `T` a terminal object of `C'`.  For a sheaf of `R`-modules `N`, restriction along the
unique maps `v(Y) ⟶ T` identifies the sections of `N` over `T` with the global sections of the
restriction `Stacks.DenseSubsiteModules.moduleRestriction J K v R N` of `N` to the subsite.

## Main definitions

* `Stacks.DenseSubsiteModules.terminalSectionsEquiv`: the bijection
  `N(T) ≃ (moduleRestriction N).sections`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe w u₁ v₁ u₂ v₂

namespace Stacks.DenseSubsiteModules

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K] (R : Sheaf K RingCat.{w}) {T : C'}
  [K.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- **Sections over a terminal object are the global sections of the restriction to a dense
subsite**: restriction along the unique maps `v(Y) ⟶ T` is a bijection. -/
def terminalSectionsEquiv (hT : IsTerminal T) (N : SheafOfModules.{w} R) :
    N.val.obj (op T) ≃ ((moduleRestriction J K v R).obj N).sections :=
  haveI := Functor.IsDenseSubsite.isCoverDense J K v
  haveI := Functor.IsDenseSubsite.isLocallyFull J K v
  Functor.IsCoverDense.terminalSectionsEquiv v K
    ((sheafCompose K (forget AddCommGrpCat.{w})).obj ((SheafOfModules.toSheaf R).obj N)) hT

/-- The component at `Y` of the global section `terminalSectionsEquiv J K v R hT N x` is the
restriction of `x` along the unique map `v(Y) ⟶ T`. -/
@[simp]
theorem terminalSectionsEquiv_apply_val (hT : IsTerminal T) (N : SheafOfModules.{w} R)
    (x : N.val.obj (op T)) (Y : Cᵒᵖ) :
    (terminalSectionsEquiv J K v R hT N x).val Y =
      N.val.map (hT.from (v.obj Y.unop)).op x :=
  rfl

end Stacks.DenseSubsiteModules

end
