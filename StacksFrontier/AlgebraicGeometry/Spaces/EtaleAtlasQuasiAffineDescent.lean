module

public import StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalFromAtlas

/-!
# The étale atlas criterion from effective descent for quasi-affine morphisms

`AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas_of_etaleDescent` proves that a
sheaf on the big fppf site of `S` with a representable, surjective, étale atlas is an algebraic
space, granted effective descent along the surjective étale morphisms of the site at the
monomorphisms locally of finite type. This file replaces that hypothesis by effective descent for
the *quasi-affine* morphisms of schemes.

The passage goes through Stacks 02W8: a monomorphism locally of finite type is separated and
locally quasi-finite, and effective descent for the separated, locally quasi-finite morphisms
locally of finite type follows from effective descent for the quasi-affine morphisms.

## Main results

* `isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType`, in the
  namespace `AlgebraicGeometry.Space`: effective descent along the surjective étale morphisms of
  the site for the quasi-affine morphisms implies it for the monomorphisms locally of finite
  type.
* `AlgebraicGeometry.relativelyRepresentable_diag_of_surjective_etale_atlas_of_quasiAffineDescent`:
  the absolute diagonal of a sheaf with a representable surjective étale atlas is representable,
  granted effective descent for the quasi-affine morphisms.
* `AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas_of_quasiAffineDescent` and
  `isAlgebraicSpace_of_relativelyRepresentable_surjective_etale_of_quasiAffineDescent`: the
  criteria of Stacks 0BGQ and Stacks 0BGR from that one hypothesis.

## References

* [Stacks Project, Tag 0BGQ](https://stacks.math.columbia.edu/tag/0BGQ)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

/-- **Effective descent for the monomorphisms locally of finite type, from effective descent for
the quasi-affine morphisms.** Effective descent along the surjective étale morphisms of the big
fppf site of `S` for the quasi-affine morphisms of schemes implies it for the monomorphisms
locally of finite type. -/
theorem isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (h0247 : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) :=
  have _hbc : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) := .inf
  have _hri : MorphismProperty.RespectsIso
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _hd := monomorphisms_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  isEffectiveDescentAlongSurjectiveEtale_of_le
    (isEffectiveDescentAlongSurjectiveEtale_isSeparated_locallyQuasiFinite_locallyOfFiniteType
      h0247)
    monomorphisms_inf_locallyOfFiniteType_le_stacks02W8

end Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The absolute diagonal of a sheaf with a representable surjective étale atlas is
representable**, granted effective descent along the surjective étale morphisms of the site for
the quasi-affine morphisms of schemes. -/
theorem relativelyRepresentable_diag_of_surjective_etale_atlas_of_quasiAffineDescent
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (h0247 : Space.IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})) :
    yoneda.relativelyRepresentable (diag F) :=
  relativelyRepresentable_diag_of_surjective_etale_atlas B S hS hF f hsurj hetale
    (Space.isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType h0247)

/-- **The criterion of Stacks 0BGQ**, granted effective descent along the surjective étale
morphisms of the site for the quasi-affine morphisms of schemes. A sheaf `F` on the big fppf site
over `S` which has a representable, surjective, étale morphism `f : h_U ⟶ F` from an object `U` of
the site is an algebraic space over `S`. -/
theorem isAlgebraicSpace_of_surjective_etale_atlas_of_quasiAffineDescent
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (h0247 : Space.IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_surjective_etale_atlas_of_etaleDescent B S hS hF U f hsurj hetale
    (Space.isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType h0247)

/-- **The criterion of Stacks 0BGR**, granted effective descent along the surjective étale
morphisms of the site for the quasi-affine morphisms of schemes. A sheaf `F` on the big fppf site
over `S` which has a representable, surjective, étale morphism `a : G ⟶ F` from an algebraic space
`G` over `S` is an algebraic space over `S`.

Representability of `a` is not a separate hypothesis: it is the first component of
`CategoryTheory.MorphismProperty.presheaf`, which each of `hs` and `he` is. -/
theorem isAlgebraicSpace_of_relativelyRepresentable_surjective_etale_of_quasiAffineDescent
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (a : G ⟶ F)
    (hs : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) a)
    (he : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) a)
    (h0247 : Space.IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_relativelyRepresentable_surjective_etale_of_etaleDescent B S hS hG hF a hs
    he (Space.isEffectiveDescentAlongSurjectiveEtale_monomorphisms_inf_locallyOfFiniteType h0247)

end AlgebraicGeometry

end
