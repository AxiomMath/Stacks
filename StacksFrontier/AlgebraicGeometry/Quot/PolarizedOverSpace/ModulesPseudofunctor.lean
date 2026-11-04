module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# The pseudofunctor of inverse images of modules on algebraic spaces

Stacks 03LU attaches to a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the inverse
image `f^*` of `𝒪`-modules, with the comparison `g^* ∘ f^* ≅ (f ≫ g)^*`
(`AlgebraicGeometry.Space.modulePullbackCompIso`) and the unit law `(𝟙 X)^* ≅ 𝟭`
(`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackIdIso` of the coherence
`AlgebraicGeometry.Space.modulePushforwardCoherence`, which holds with no hypothesis). The
associativity coherence (`AlgebraicGeometry.Space.modulePullbackCompIso_assoc`) and the two unit
laws (`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIso_id_left` and
`…_id_right`) are those of a pseudofunctor `LocallyDiscrete (AlgebraicSpaces)ᵒᵖ ⥤ᵖ Cat`, sending
`X` to the category of `𝒪_X`-modules and `f` to `f^*`, with these comparisons on the nose.

Its Grothendieck construction is the category of pairs `(X, M)` with morphisms
`(f, M ⟶ f^*M')`, composed through `modulePullbackCompIso`, which is how the categories of
polarized families of algebraic spaces of Stacks 0E94 are built: the category laws are those of
Mathlib's `CategoryTheory.Pseudofunctor.CoGrothendieck`, checked once at an abstract pseudofunctor.

## Main definitions

* `AlgebraicGeometry.Space.modulesPseudofunctor`: the pseudofunctor.

## Main results

* `AlgebraicGeometry.Space.modulesPseudofunctor_mapComp` and
  `AlgebraicGeometry.Space.modulesPseudofunctor_mapId`: its comparisons are those of Stacks 03LU.

## Implementation notes

Composition in `AlgebraicGeometry.Space.AlgebraicSpaces` is associative and unital by definitional
unfolding (a morphism of algebraic spaces is a morphism of presheaves of types), so every
`eqToHom` in the coherences of `CategoryTheory.LocallyDiscrete.mkPseudofunctor` is an identity.

The comparisons are taken to be those of Stacks 03LU themselves rather than their adjoint mates:
a statement relating a comparison built as a mate to `modulePullbackCompIso` has to unfold the
morphisms of ringed topoi underlying the inverse images, which is unaffordable. For the same
reason the comparisons are recorded as equalities of isomorphisms in `Cat`, whose two sides have
the same shape, and never as equalities of components: a component of a comparison is compared by
the kernel with a component of `modulePullbackCompIso` only after both are unfolded completely.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The pseudofunctor of inverse images of `𝒪`-modules on algebraic spaces** (Stacks 03LU):
`X ↦ Modules(𝒪_X)`, `f ↦ f^*`, with the comparisons of Stacks 03LU. -/
def modulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete (AlgebraicSpaces B S hS)ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (Modules.{u, u} B S hS X.unop.1 X.unop.2))
    (fun {_ _} f => (modulePullback B S hS f.unop).toCatHom)
    (fun X => Cat.Hom.isoMk ((modulePushforwardCoherence B S hS).modulePullbackIdIso X.unop))
    (fun {_ _ _} f g => Cat.Hom.isoMk (modulePullbackCompIso B S hS g.unop f.unop).symm)
    (fun {_ _ _ _} f g h => by
      ext1
      have key := congrArg Iso.hom (modulePullbackCompIso_assoc B S hS h.unop g.unop f.unop)
      simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Iso.symm_hom] at key
      simp
      rw [key]
      simp [← Functor.whiskerRight_comp_assoc])
    (fun {_ _} f => by
      ext1
      simp [(modulePushforwardCoherence B S hS).modulePullbackCompIso_id_right f.unop,
        ← Functor.whiskerRight_comp_assoc])
    (fun {_ _} f => by
      ext1
      simp [(modulePushforwardCoherence B S hS).modulePullbackCompIso_id_left f.unop,
        ← Functor.whiskerLeft_comp_assoc])

section Comparisons

-- The comparisons below are stated against the pseudofunctor's own construction; the inverse
-- images and their comparison are made irreducible so that elaboration unfolds the construction
-- rather than the inverse images.
attribute [local irreducible] modulePullback modulePullbackCompIso

/-- The composition comparison of the pseudofunctor is the comparison of Stacks 03LU. -/
theorem modulesPseudofunctor_mapComp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (modulesPseudofunctor B S hS).mapComp g.op.toLoc f.op.toLoc =
      Cat.Hom.isoMk (modulePullbackCompIso B S hS f g).symm :=
  rfl

/-- The identity comparison of the pseudofunctor is the unit law of Stacks 03LU. -/
theorem modulesPseudofunctor_mapId (X : AlgebraicSpaces B S hS) :
    (modulesPseudofunctor B S hS).mapId ⟨Opposite.op X⟩ =
      Cat.Hom.isoMk ((modulePushforwardCoherence B S hS).modulePullbackIdIso X) :=
  rfl

end Comparisons

end AlgebraicGeometry.Space

end
