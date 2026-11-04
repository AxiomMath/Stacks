module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonal

/-!
# Properties of the relative diagonal of a morphism of algebraic spaces (Stacks 03HK)

Let `S` be a scheme contained in a big fppf site `B` and let `f : F ⟶ G` be a morphism of
presheaves on the big fppf site of `S` with `F` an algebraic space over `S`. The relative
diagonal `Δ_f : F ⟶ F ×_G F` is locally of finite type, a monomorphism, separated and locally
quasi-finite — each of these being a property of the represented base changes of `Δ_f`.

The target `G` is an arbitrary presheaf, and no hypothesis on it is needed: `Δ_f` is a base
change of the *absolute* diagonal `F ⟶ F × F` along the comparison morphism
`F ×_G F ⟶ F × F`, by `AlgebraicGeometry.isPullback_pullbackDiagonal_diag`, and a relative
property is stable under base change. So each clause here is the corresponding clause of
**Stacks 02X4** for the absolute diagonal, fed through
`AlgebraicGeometry.presheaf_pullbackDiagonal_of_diag`.

Part (1) of Stacks 03HK — representability of `Δ_f` — is
`AlgebraicGeometry.relativelyRepresentable_pullbackDiagonal`, in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonal`.

## Main results

* `AlgebraicGeometry.presheaf_locallyOfFiniteType_pullbackDiagonal`: **Stacks 03HK**, part (2).
* `AlgebraicGeometry.presheaf_monomorphisms_pullbackDiagonal`: **Stacks 03HK**, part (3).
* `AlgebraicGeometry.presheaf_isSeparated_pullbackDiagonal`: **Stacks 03HK**, part (4).
* `AlgebraicGeometry.presheaf_locallyQuasiFinite_pullbackDiagonal`: **Stacks 03HK**, part (5).

## References

* [Stacks Project, Tag 03HK](https://stacks.math.columbia.edu/tag/03HK)
* [Stacks Project, Tag 02X4](https://stacks.math.columbia.edu/tag/02X4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03HK, part (2).** The relative diagonal of a morphism out of an algebraic space
over `S` is locally of finite type. -/
@[stacks 03HK "part (2)"]
theorem presheaf_locallyOfFiniteType_pullbackDiagonal (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (pullback.diagonal f) :=
  presheaf_pullbackDiagonal_of_diag B S hS f _
    (presheaf_locallyOfFiniteType_diag B S hS F hF)

/-- **Stacks 03HK, part (3).** Every represented base change of the relative diagonal of a
morphism out of an algebraic space over `S` is a monomorphism of schemes. -/
@[stacks 03HK "part (3)"]
theorem presheaf_monomorphisms_pullbackDiagonal (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (MorphismProperty.monomorphisms Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (pullback.diagonal f) :=
  presheaf_pullbackDiagonal_of_diag B S hS f _
    (presheaf_monomorphisms_diag B S hS F hF)

/-- **Stacks 03HK, part (4).** The relative diagonal of a morphism out of an algebraic space
over `S` is separated. -/
@[stacks 03HK "part (4)"]
theorem presheaf_isSeparated_pullbackDiagonal (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (pullback.diagonal f) :=
  presheaf_pullbackDiagonal_of_diag B S hS f _
    (presheaf_isSeparated_diag B S hS F hF)

/-- **Stacks 03HK, part (5).** The relative diagonal of a morphism out of an algebraic space
over `S` is locally quasi-finite. -/
@[stacks 03HK "part (5)"]
theorem presheaf_locallyQuasiFinite_pullbackDiagonal (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS))) (pullback.diagonal f) :=
  presheaf_pullbackDiagonal_of_diag B S hS f _
    (presheaf_locallyQuasiFinite_diag B S hS F hF)

end AlgebraicGeometry

end
