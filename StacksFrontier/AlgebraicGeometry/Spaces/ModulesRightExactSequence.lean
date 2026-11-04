module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# Right-exact sequences of `𝒪`-modules and their inverse images

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  The category
of `𝒪_X`-modules on the small étale site of `X` is abelian, and the inverse image along a
morphism of algebraic spaces is a left adjoint, so it preserves cokernels and epimorphisms.
This file records the three consequences a right-exact sequence of `𝒪_X`-modules is read
through: that a short complex whose first map is a kernel of its second is exact, that the
inverse image of an epimorphism is an epimorphism, and that the inverse image of a short complex
exact in the middle whose second map is an epimorphism is again exact in the middle.

## Main results

* `AlgebraicGeometry.Space.exact_of_isLimit_kernelFork`
* `AlgebraicGeometry.Space.epi_modulePullback_map`
* `AlgebraicGeometry.Space.exact_map_modulePullback`,
  `AlgebraicGeometry.Space.exact_map_map_modulePullback` and
  `AlgebraicGeometry.Space.exact_mk_of_exact_map`

## Implementation notes

**Why these three statements are made here and not where they are used.**  Each is `inferInstance`
over an abelian-category instance of `CategoryTheory.SheafOfModules` whose universe of module
sections is a variable of the instance, and resolving it against the module sections of
`AlgebraicGeometry.Space.Modules` leaves a universe constraint the elaborator will only solve in
a context where no other candidate instance of the same class is in scope.  Stating them at a
variable short complex, in a file importing nothing beyond the abelian structure and the
adjunction, resolves the instances once; their consumers then apply a lemma with no instance
argument left to find.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] preservesZeroMorphisms_modulePullback
  preservesFiniteColimits_modulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS}

/-- A short complex of `𝒪_X`-modules whose first map is a kernel of its second is exact. -/
theorem exact_of_isLimit_kernelFork (T : ShortComplex (Modules.{u, u} B S hS X.1 X.2))
    (h : IsLimit (KernelFork.ofι T.f T.zero)) : T.Exact :=
  ShortComplex.exact_of_f_is_kernel T h

/-- The inverse image of `𝒪`-modules carries an epimorphism to an epimorphism: it is a left
adjoint, so it preserves finite colimits. -/
theorem epi_modulePullback_map (f : X' ⟶ X) {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (hφ : Epi φ) : Epi ((modulePullback B S hS f).map φ) :=
  have _ := hφ
  inferInstance

/-- **The inverse image of `𝒪`-modules preserves exactness in the middle of a right-exact
sequence.**  It is a left adjoint, so it preserves the cokernel of the first map, and the second
map is assumed to be an epimorphism. -/
theorem exact_map_modulePullback (f : X' ⟶ X)
    (T : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) (hT : T.Exact) (hg : Epi T.g) :
    (T.map (modulePullback B S hS f)).Exact :=
  hT.map_of_epi_of_preservesCokernel (modulePullback B S hS f) hg inferInstance

/-- The inverse image along two successive morphisms of algebraic spaces preserves exactness in
the middle of a right-exact sequence of `𝒪`-modules. -/
theorem exact_map_map_modulePullback {X'' : AlgebraicSpaces B S hS} (f : X' ⟶ X) (g : X'' ⟶ X')
    (T : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) (hT : T.Exact) (hg : Epi T.g) :
    ((T.map (modulePullback B S hS f)).map (modulePullback B S hS g)).Exact :=
  exact_map_modulePullback B S hS g _ (exact_map_modulePullback B S hS f T hT hg)
    (epi_modulePullback_map B S hS f T.g hg)

/-- **The inverse image of a right-exact sequence, with its last term renamed.**  The inverse
image of a short complex exact in the middle whose second map is an epimorphism stays exact in
the middle after its last object is transported along an isomorphism. -/
theorem exact_mk_of_exact_map (f : X' ⟶ X) (T : ShortComplex (Modules.{u, u} B S hS X.1 X.2))
    (hT : T.Exact) (hg : Epi T.g) {K : Modules.{u, u} B S hS X'.1 X'.2}
    (e : (modulePullback B S hS f).obj T.X₃ ≅ K)
    (gg : (modulePullback B S hS f).obj T.X₂ ⟶ K)
    (hgg : (modulePullback B S hS f).map T.g ≫ e.hom = gg)
    (w : (modulePullback B S hS f).map T.f ≫ gg = 0) :
    (ShortComplex.mk ((modulePullback B S hS f).map T.f) gg w).Exact :=
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₁ := T.map (modulePullback B S hS f)) (Iso.refl _) (Iso.refl _) e
      ((Category.id_comp _).trans (Category.comp_id _).symm)
      ((Category.id_comp _).trans hgg.symm))
    (exact_map_modulePullback B S hS f T hT hg)

end AlgebraicGeometry.Space

end
