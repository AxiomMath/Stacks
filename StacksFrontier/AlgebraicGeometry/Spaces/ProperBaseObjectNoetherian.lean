module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints

/-!
# A proper algebraic space over a Noetherian ring is Noetherian

Let `A` be a Noetherian ring and `X` an algebraic space proper over `Spec A`.  Then `X` is a
Noetherian algebraic space in the sense of Stacks 03EA: it is quasi-compact
(`AlgebraicGeometry.Space.isQuasiCompactSpace_of_isProper_baseObject`), absolutely
quasi-separated, the structure morphism being separated and its target a scheme, and locally
Noetherian by Stacks 04ZK
(`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isProper`).  Consequently
`X` is decent, by Stacks 03JX, and its space of points is a Noetherian topological space.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isProper_baseObject`
* `AlgebraicGeometry.Space.isNoetherian_of_isProper_baseObject`
* `AlgebraicGeometry.Space.isDecentSpace_of_isProper_baseObject`
* `AlgebraicGeometry.Space.noetherianSpace_points_of_isProper_baseObject`
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (baseObject A B hA))

include hX in
/-- **A proper algebraic space over an affine base is absolutely quasi-separated**: its structure
morphism is separated, hence quasi-separated, and its target is represented by the affine, hence
quasi-separated, scheme `Spec A` (Stacks 03JX). -/
theorem isAbsolutelyQuasiSeparated_of_isProper_baseObject
    (hf : IsProper B (Spec (.of A)) hA f) :
    IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA B.contains_terminal X :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of A)) hA B.contains_terminal hX
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (Spec (.of A)) hA
      (yoneda.obj (baseObject A B hA)) B.contains_terminal
      ⟨baseObject A B hA, inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of A))),
        ⟨Functor.RepresentableBy.yoneda _⟩⟩)
    (isQuasiSeparated_of_isSeparated B (Spec (.of A)) hA hf.1)

include hX in
/-- **A proper algebraic space over the spectrum of a Noetherian ring is Noetherian** in the sense
of Stacks 03EA: quasi-compact, absolutely quasi-separated and locally Noetherian. -/
theorem isNoetherian_of_isProper_baseObject [IsNoetherianRing A]
    (hf : IsProper B (Spec (.of A)) hA f) :
    IsNoetherian B (Spec (.of A)) hA B.contains_terminal X :=
  ⟨isQuasiCompactSpace_of_isProper_baseObject A B hA X hX f hf,
    isAbsolutelyQuasiSeparated_of_isProper_baseObject A B hA X hX f hf,
    hasEtaleLocalProperty_isLocallyNoetherian_of_isProper A B hA X hX f hf⟩

include hX in
/-- **A proper algebraic space over an affine base is decent**, being absolutely quasi-separated
(Stacks 03JX). -/
theorem isDecentSpace_of_isProper_baseObject (hf : IsProper B (Spec (.of A)) hA f) :
    IsDecentSpace B (Spec (.of A)) hA X :=
  isDecentSpace_of_isAbsolutelyQuasiSeparated B (Spec (.of A)) hA X hX
    (isAbsolutelyQuasiSeparated_of_isProper_baseObject A B hA X hX f hf)

include hX in
/-- **The space of points of a proper algebraic space over a Noetherian ring is Noetherian**: it
is quasi-compact and locally Noetherian. -/
theorem noetherianSpace_points_of_isProper_baseObject [IsNoetherianRing A]
    (hf : IsProper B (Spec (.of A)) hA f) :
    TopologicalSpace.NoetherianSpace (points B (Spec (.of A)) hA X) :=
  noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B (Spec (.of A)) hA X hX
    (isQuasiCompactSpace_of_isProper_baseObject A B hA X hX f hf)
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper A B hA X hX f hf)

end AlgebraicGeometry.Space

end
