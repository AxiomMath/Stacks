module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.SquareLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale

/-!
# Isomorphisms in `D(𝒪_W)` are detected on an elementary distinguished square

Let `(U ⊆ W, j_V : V ⟶ W)` be an elementary distinguished square of algebraic spaces over a
scheme `S`.  A morphism of `D(𝒪_W)` whose restrictions to `U` and to `V` are isomorphisms is an
isomorphism: the cone of the morphism restricts to the cones of the two restrictions, which
vanish, and vanishing in `D(𝒪_W)` is local for the square
(`AlgebraicGeometry.Space.isZero_of_isZero_derivedRestrict_eds`).

This is the derived companion of the module-level
`AlgebraicGeometry.Space.isIso_of_eds`, and it is what recognises the morphism produced by the
glueing lemma Stacks 08HB as an isomorphism.

## The two restriction functors

Two functors in this library compute the restriction of `D(𝒪_W)` along an étale morphism
`a : X ⟶ W`: the canonical derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, which is what Stacks 08H6
(`AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback`) and the affine base case
of Stacks 09RJ are stated with, and the exact restriction functor read on derived categories,
`(AlgebraicGeometry.Space.etaleModulePullback a ha).mapDerivedCategory`, which is what the
Mayer–Vietoris machinery and the glueing lemma Stacks 08HB are stated with.  They are
isomorphic, by `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoEtale`, and the three
transport lemmas below move the three properties this chapter tests across that isomorphism
once and for all, so that no argument has to thread it by hand.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedModulePullback_map_iff`,
  `AlgebraicGeometry.Space.isZero_smallEtaleDerivedModulePullback_obj_iff` and
  `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback_obj_iff`: invertibility,
  vanishing and perfectness of a derived restriction along an étale morphism do not depend on
  which of the two restriction functors computes it.
* `AlgebraicGeometry.Space.isIso_of_isIso_derivedRestrict_eds`: **a morphism of `D(𝒪_W)` whose
  restrictions to the two members of an elementary distinguished square are isomorphisms is an
  isomorphism**, in the restriction-functor spelling of Stacks 08HB.
* `AlgebraicGeometry.Space.isIso_of_isIso_smallEtaleDerivedRestrict_eds`: the same, in the
  canonical derived-pullback spelling.
* `AlgebraicGeometry.Space.isPerfect_of_isPerfect_smallEtaleDerivedRestrict_eds`: perfectness in
  the canonical derived-pullback spelling is also tested on the two members, which is
  `AlgebraicGeometry.Space.isPerfect_of_isPerfect_edsRestrict` transported.

## Implementation notes

No hypothesis beyond the square is carried.  The instances that the Mayer–Vietoris sequence of
the square needs are supplied by the `attribute [local instance]` declarations of
`StacksFrontier/AlgebraicGeometry/Spaces/CompactGeneration/SquareLocality.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ElementaryDistinguishedSquareCover.lean`, so the
statements imported from there take none; the ones declared below are the ones the *statements*
of this file need, namely the standard model of the derived category and the exactness of étale
restriction.

## References

* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08H6](https://stacks.math.columbia.edu/tag/08H6)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Moving between the two restriction functors -/

section Transport

variable {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y) (ha : IsEtale B S hS a.hom)

/-- **Invertibility of a derived restriction does not depend on which restriction functor
computes it.**  The canonical derived pullback along an étale morphism and the exact restriction
functor read on derived categories are isomorphic, by
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoEtale`. -/
theorem isIso_smallEtaleDerivedModulePullback_map_iff
    {K L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)} (φ : K ⟶ L) :
    IsIso ((smallEtaleDerivedModulePullback B S hS a).map φ) ↔
      IsIso ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.map φ) :=
  NatIso.isIso_map_iff (smallEtaleDerivedModulePullbackIsoEtale B S hS a ha) φ

/-- **Vanishing of a derived restriction does not depend on which restriction functor computes
it.** -/
theorem isZero_smallEtaleDerivedModulePullback_obj_iff
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    IsZero ((smallEtaleDerivedModulePullback B S hS a).obj K) ↔
      IsZero ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.obj K) :=
  ⟨fun h => h.of_iso ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app K).symm,
    fun h => h.of_iso ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app K)⟩

/-- **Perfectness of a derived restriction does not depend on which restriction functor computes
it.** -/
theorem isPerfect_smallEtaleDerivedModulePullback_obj_iff
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect
        ((smallEtaleDerivedModulePullback B S hS a).obj K) ↔
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect
        ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.obj K) :=
  ⟨fun h => RingedSite.IsPerfect.of_iso _ h
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app K),
    fun h => RingedSite.IsPerfect.of_iso _ h
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app K).symm⟩

end Transport

/-! ### Invertibility is local for an elementary distinguished square -/

section Square

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **Invertibility in `D(𝒪_W)` is local for an elementary distinguished square**: a morphism
whose restrictions to the open subspace `U` and to the étale algebraic space `V` are
isomorphisms is an isomorphism.

The cone of the morphism restricts to the cones of the two restrictions, which vanish because
those are invertible, and an object of `D(𝒪_W)` restricting to zero on `U` and on `V` is zero by
`AlgebraicGeometry.Space.isZero_of_isZero_derivedRestrict_eds`.  No hypothesis beyond the square
is used.

This is the derived companion of the module-level `AlgebraicGeometry.Space.isIso_of_eds`. -/
theorem isIso_of_isIso_derivedRestrict_eds
    {E F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)} (φ : E ⟶ F)
    (hU : IsIso ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.map φ))
    (hV : IsIso ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.map φ)) : IsIso φ := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle φ
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_isZero_derivedRestrict_eds B S hS hsq C ?_ ?_) <;>
  exact Triangle.isZero₃_of_isIso₁ _ (Functor.map_distinguished _ _ hT) ‹_›

/-- **Invertibility in `D(𝒪_W)` is local for an elementary distinguished square**, with the
restrictions taken by the canonical derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`.  This is
`AlgebraicGeometry.Space.isIso_of_isIso_derivedRestrict_eds` transported across
`AlgebraicGeometry.Space.isIso_smallEtaleDerivedModulePullback_map_iff`. -/
theorem isIso_of_isIso_smallEtaleDerivedRestrict_eds
    {E F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)} (φ : E ⟶ F)
    (hU : IsIso ((smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).map φ))
    (hV : IsIso ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).map φ)) :
    IsIso φ :=
  isIso_of_isIso_derivedRestrict_eds B S hS hsq φ
    ((isIso_smallEtaleDerivedModulePullback_map_iff B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) φ).1 hU)
    ((isIso_smallEtaleDerivedModulePullback_map_iff B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) φ).1 hV)

/-- **Perfectness is local for an elementary distinguished square**, with the restrictions taken
by the canonical derived pullback `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`.
This is `AlgebraicGeometry.Space.isPerfect_of_isPerfect_edsRestrict` transported across
`AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback_obj_iff`. -/
theorem isPerfect_of_isPerfect_smallEtaleDerivedRestrict_eds
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).IsPerfect
      ((smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj E))
    (hV : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).IsPerfect
      ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj E)) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect E :=
  isPerfect_of_isPerfect_edsRestrict B S hS hsq E
    ((isPerfect_smallEtaleDerivedModulePullback_obj_iff B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) E).1 hU)
    ((isPerfect_smallEtaleDerivedModulePullback_obj_iff B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) E).1 hV)

end Square

end AlgebraicGeometry.Space

end
