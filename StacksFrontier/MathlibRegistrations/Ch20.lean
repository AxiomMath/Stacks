module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags covered by Mathlib: Chapter 20 (Cohomology of Sheaves)

The Stacks tags below are stated in Mathlib. This file registers the Mathlib declarations that
realize them with `add_to_stacks`; it contains no declarations of its own.
-/

add_to_stacks 0712 "definition of H^i(X, -), at F = Γ(X, -) on abelian sheaves"
  CategoryTheory.Functor.rightDerived
add_to_stacks 0712 "H^i(X, F) = H^i(Γ(X, I•)) for any injective resolution F[0] → I•"
  CategoryTheory.InjectiveResolution.isoRightDerivedObj

add_to_stacks 0713 "definition of R^i f_*, at F = f_* on abelian sheaves"
  CategoryTheory.Functor.rightDerived
add_to_stacks 0713 "R^i f_* F = H^i(f_* I•) for any injective resolution F[0] → I•"
  CategoryTheory.InjectiveResolution.isoRightDerivedObj

add_to_stacks 0714 "definition of H^i(X, -), at F = Γ(X, -) on 𝒪_X-modules"
  CategoryTheory.Functor.rightDerived
add_to_stacks 0714 "H^i(X, F) = H^i(Γ(X, I•)) for any injective resolution in Mod(𝒪_X)"
  CategoryTheory.InjectiveResolution.isoRightDerivedObj

add_to_stacks 01EF "the Čech complex `Č^•(𝒰, F)`: for `C = Opens X`, a family `U : ι → Opens X` and
  an abelian presheaf `F`, `(cechComplexFunctor U).obj F` has degree `p` term
  `∏_{x : Fin (p + 1) → ι} F(U_{x 0} ⊓ ⋯ ⊓ U_{x p})` and the alternating coface differential"
  CategoryTheory.cechComplexFunctor

add_to_stacks 01EF "the Čech cohomology groups `Ȟ^i(𝒰, F) = H^i(Č^•(𝒰, F))`, as the homology of
  `(cechComplexFunctor U).obj F`" HomologicalComplex.homology

/-! ### Further tags of this chapter covered by Mathlib

Where a Mathlib declaration is more general than the tag, the note says how the tag is the
special case. -/

add_to_stacks 02FS "more general: any family of subsets; Mathlib asks for a neighbourhood of x, \
  equivalently an open one"
  LocallyFinite

add_to_stacks 09SW "flasque presheaf: every restriction map is an epimorphism \
  (for presheaves in any category)" TopCat.Presheaf.IsFlasque
add_to_stacks 09SW "for presheaves of sets, an epimorphism is a surjection"
  CategoryTheory.epi_iff_surjective
