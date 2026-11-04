module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.RingTheory.Catenary.Formal

/-!
# Sections of a universally catenary scheme over an affine open

A universally catenary scheme has universally catenary rings of sections over its affine
opens. This is the passage from the scheme-level hypothesis to the commutative algebra in
which the coherence criteria for a pushforward are stated.
-/

@[expose] public section

open CategoryTheory TopologicalSpace IrreducibleClosedsCodim

universe u

namespace AlgebraicGeometry

/-- The ring of sections of a universally catenary scheme over an affine open is universally
catenary. -/
public theorem isUniversallyCatenary_sections_of_affineOpen {S : Scheme.{u}}
    [IsLocallyNoetherian S] (hS : Scheme.IsUniversallyCatenary S) (U : S.affineOpens) :
    Ring.IsUniversallyCatenary Γ(S, (U : S.Opens)) := by
  intro C _ _ _
  apply isCatenary_of_isCatenarySpace
  have hφ : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, (U : S.Opens)) C))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hι : LocallyOfFiniteType U.2.fromSpec :=
    @locallyOfFiniteType_of_isOpenImmersion _ _ U.2.fromSpec U.2.isOpenImmersion_fromSpec
  have hcomp : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, (U : S.Opens)) C)) ≫ U.2.fromSpec) :=
    @locallyOfFiniteType_comp _ _ _
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, (U : S.Opens)) C))) U.2.fromSpec hφ hι
  exact @Scheme.IsUniversallyCatenary.isCatenarySpace S _ _ hS
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, (U : S.Opens)) C)) ≫ U.2.fromSpec) hcomp

end AlgebraicGeometry

end
