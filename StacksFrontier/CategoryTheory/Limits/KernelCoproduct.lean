module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Kernels of coproducts of morphisms

In an abelian category in which coproducts indexed by `J` are exact — Grothendieck's axiom
AB4 for the shape `Discrete J`, recorded in Mathlib as
`CategoryTheory.Limits.HasExactColimitsOfShape (Discrete J)` — the kernel of
`Limits.Sigma.map α` is the coproduct of the kernels of the `α j`.

Unlike the binary case of `CategoryTheory.Limits.kernelBiprodMapIso`, this needs exactness of
the coproduct functor: for a general abelian category the canonical map
`∐ (fun j ↦ kernel (α j)) ⟶ kernel (Limits.Sigma.map α)` is a monomorphism but not an
isomorphism.

## Main results

* `CategoryTheory.Limits.kernelSigmaMapIso`: the isomorphism
  `∐ (fun j ↦ kernel (α j)) ≅ kernel (Limits.Sigma.map α)`.

## Implementation notes

The exactness hypothesis says that `colim : (Discrete J ⥤ C) ⥤ C` preserves finite limits, so
it carries the kernel of a morphism of `Discrete J`-shaped diagrams to the kernel of the
induced morphism of coproducts. The kernel in the diagram category is computed pointwise,
which is what identifies its colimit with `∐ (fun j ↦ kernel (α j))`.
-/

@[expose] public section

namespace CategoryTheory.Limits

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] {J : Type w}
  [HasColimitsOfShape (Discrete J) C] [HasExactColimitsOfShape (Discrete J) C]
  {X Y : J → C} (α : ∀ j, X j ⟶ Y j)

/-- The morphism of `Discrete J`-shaped diagrams induced by a family of morphisms. -/
public def discreteNatTransOfFamily : Discrete.functor X ⟶ Discrete.functor Y :=
  Discrete.natTrans fun j => α j.as

omit [Abelian C] [HasExactColimitsOfShape (Discrete J) C] in
/-- The colimit of the family of morphisms is the morphism of coproducts. -/
public lemma colim_map_discreteNatTransOfFamily :
    colim.map (discreteNatTransOfFamily α) = Limits.Sigma.map α := by
  apply colimit.hom_ext
  intro j
  obtain ⟨j⟩ := j
  simp [discreteNatTransOfFamily, Limits.Sigma.map, Discrete.natTrans]

/-- The pointwise kernels of a family of morphisms form the kernel of the induced morphism of
`Discrete J`-shaped diagrams: kernels in a diagram category are computed pointwise. -/
public noncomputable def kernelDiscreteNatTransOfFamilyIso :
    kernel (discreteNatTransOfFamily α) ≅ Discrete.functor fun j => kernel (α j) :=
  Discrete.natIso fun j =>
    (PreservesKernel.iso ((evaluation (Discrete J) C).obj j)
      (discreteNatTransOfFamily α)).trans (eqToIso (by obtain ⟨j⟩ := j; rfl))

/-- **The kernel of a coproduct of morphisms is the coproduct of their kernels**, when
coproducts indexed by `J` are exact. -/
public noncomputable def kernelSigmaMapIso :
    (∐ fun j => kernel (α j)) ≅ kernel (Limits.Sigma.map α) :=
  haveI : PreservesFiniteLimits (colim (J := Discrete J) (C := C)) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  (HasColimit.isoOfNatIso (kernelDiscreteNatTransOfFamilyIso α)).symm ≪≫
    PreservesKernel.iso colim (discreteNatTransOfFamily α) ≪≫
      kernelIsoOfEq (colim_map_discreteNatTransOfFamily α)

end CategoryTheory.Limits

end
