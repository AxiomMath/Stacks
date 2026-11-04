module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sheaves.Presheaf

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 006K — Presheaves of abelian groups

Stacks 006K defines (1) a presheaf of abelian groups on a topological space `X`, also called an
abelian presheaf, as a presheaf of sets `F` in which every `F(U)` is endowed with the structure
of an abelian group and every restriction map `ρ^U_V` is a homomorphism of abelian groups; (2) a
morphism of abelian presheaves, a morphism of presheaves of sets inducing a group homomorphism
`F(U) → G(U)` for every open `U`; and (3) the category $\mathit{PAb}(X)$.

All three clauses are Mathlib's `TopCat.Presheaf AddCommGrpCat X`, presheaves valued in the
category of abelian groups (`Ab` is notation for `AddCommGrpCat`). Taking values in
`AddCommGrpCat` builds the group structure on each `F(U)` and the homomorphism condition on each
restriction map into the functor, so clause (1) is that functor; natural transformations between
such functors have group homomorphisms as components, which is clause (2); and clause (3) is
`TopCat.instCategoryPresheaf` at this target category.
-/

@[expose] public section

-- The former @[stacks 006K] declarations were abbreviations for the Mathlib notions, and two
-- lemmas extracting the group homomorphism that taking values in `AddCommGrpCat` supplies.
add_to_stacks 006K "the target category of abelian groups, which supplies the group structure
  on each `F(U)` and makes each restriction map a homomorphism" AddCommGrpCat
add_to_sga "4 I 2.3.2" AddCommGrpCat
add_to_sga "7 VII 3.5" "special case" AddCommGrpCat
add_to_stacks 006K "an abelian presheaf on `X` is a functor `(Opens X)ᵒᵖ ⥤ AddCommGrpCat`; the
  objects of `PAb(X)`" TopCat.Presheaf
add_to_sga "3 IV 4.3.1" "special case" TopCat.Presheaf
add_to_sga "3 IV 4.3.17" "special case" TopCat.Presheaf
add_to_sga "4 I 1.2" "special case" TopCat.Presheaf
add_to_sga "4 II 6.0" "special case" TopCat.Presheaf
add_to_sga "4½ Arcata 1.6.3" "special case" TopCat.Presheaf
add_to_stacks 006K "morphisms of abelian presheaves are natural transformations, with group
  homomorphisms as components; the category `PAb(X)`" TopCat.instCategoryPresheaf
add_to_sga "3 IV 4.3.1" "special case" TopCat.instCategoryPresheaf
add_to_sga "4 I 1.2" "special case" TopCat.instCategoryPresheaf
