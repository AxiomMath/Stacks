module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing.SubterminalRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing.GluedPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing.FppfMayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing.Equivalence

/-!
# Glueing algebraic spaces of finite presentation along a covering of the base by two opens

This file re-exports its parts: subterminal objects and restrictions along products, the glued
presheaf, the two-open coverings of the base of the big fppf site, and the equivalence of
Stacks 0E8Z between algebraic spaces of finite presentation over the base and the `2`-fibre
product `FP_U ×_{FP_V} FP_W`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace FinitePresentationSpacesOver

open CategoryTheory.SubterminalGlueing

attribute [local instance] BigFppfOver.hasSheafify_type

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z U W V : BigFppfOver B S hS}

variable (hZ : IsTerminal Z) {jU : U ⟶ Z} {jW : W ⟶ Z} [Mono jU] [Mono jW] {iU : V ⟶ U}
  {iW : V ⟶ W} (hV : IsPullback iU iW jU jW)

section Cover

/-! ### The equivalence -/

variable (hjU : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU))
  (hjW : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW))
  (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
    x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jU) ∨
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jW))
  (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
  (hWopen : IsOpenImmersion (B.inclusion.map W.hom))
  (hScov : ∀ x : S, x ∈ Set.range (B.inclusion.map U.hom) ∨
    x ∈ Set.range (B.inclusion.map W.hom))

include hZ hV hjU hjW hsurj hUopen hWopen hScov in
/-- **The algebraic spaces of finite presentation over a base covered by two opens `U` and `W`
with intersection `V` are the `2`-fibre product `FP_U ×_{FP_V} FP_W`.** The comparison functor
taking a space to its two restrictions together with their canonical identification over `V` is
an equivalence: it is faithful and full by the sheaf condition at the Mayer--Vietoris squares of
the covering, and essentially surjective because the space glued from a datum restricts back to
it. -/
@[stacks 0E8Z "the equivalence clause: for an open covering of the base, base change is an \
equivalence onto the 2-fibre product of the categories of finite-presentation algebraic spaces \
over the two members. The criterion clause, that algebraicity is detected on such a covering, is \
`AlgebraicGeometry.isAlgebraicSpace_iff_forall_isAlgebraicSpace_relocalizeRestrict` in \
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraicityOnBaseCover`, which this module imports, so \
the two clauses cannot live in one file"]
theorem isEquivalence_glueingFunctor : (glueingFunctor B S hS hV.w).IsEquivalence := by
  have hcov := ofTwoArrows_mem_topology B S hS jU jW hjU hjW hsurj
  have := full_glueingFunctor B S hS hZ hV hcov
  have := faithful_glueingFunctor B S hS hZ hV hcov
  have := essSurj_glueingFunctor B S hS hZ hV hjU hjW hsurj hUopen hWopen hScov
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Cover

end FinitePresentationSpacesOver

end AlgebraicGeometry

end
