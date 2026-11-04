module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatSurjectiveMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separatedness from a flat presentation, and the canonical gluing functor (Stacks 0F9U)

The last step of the proof of Stacks 0F9U reads separatedness of the realizing space `Y` off a
presentation `a : E ⟶ Y` which is quasi-compact, flat and surjective and whose kernel pair is a
closed subspace of `E ⨯ E`. The base module
`StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffine` proves this when the
square `a ⨯ a` is assumed to be an fpqc covering; this module derives that covering from the
three morphism properties, and instantiates the gluing functor of Stacks 0F9N at the canonical
square of a glueing pair, which is where the affine equivalence of Stacks 0F9Q lives.

## Main definitions

* `BeauvilleLaszlo.Space.canonicalGlueingFunctorSpec`: the gluing functor of Stacks 0F9N at the
  canonical square of a glueing pair.

## Main results

* `AlgebraicGeometry.AlgebraicSpaces.productIsoProd`: the explicit product of two algebraic
  spaces is the categorical binary product.
* `AlgebraicGeometry.AlgebraicSpaces.prop_productMapHom`: a property of morphisms stable under
  base change and under composition passes from `a` to `a ⨯ a`.
* `AlgebraicGeometry.Space.isCovering_fpqc_productMapHom` and
  `AlgebraicGeometry.Space.isSeparatedOver_of_kernelPair_of_flat_presentation`: the square of a
  quasi-compact, flat, surjective morphism is an fpqc covering, so separatedness follows from
  such a presentation with closed kernel pair.

## References

* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.AlgebraicSpaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The explicit product is the categorical one -/

/-- The explicit product of two algebraic spaces over `S` is the categorical binary product.
Both are limits of the same pair, so the comparison is the unique map over the projections. -/
noncomputable abbrev productIsoProd (F G : AlgebraicSpaces B S hS) :
    product B S hS F G ≅ F ⨯ G :=
  (isLimitBinaryFanProduct B S hS F G).conePointUniqueUpToIso (limit.isLimit (pair F G))

/-- The comparison `productIsoProd` followed by the first categorical projection is the first
projection of the explicit product. -/
@[simp]
theorem productIsoProd_hom_comp_fst (F G : AlgebraicSpaces B S hS) :
    (productIsoProd B S hS F G).hom ≫ Limits.prod.fst = productProjFst B S hS F G := by
  simpa using (isLimitBinaryFanProduct B S hS F G).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (pair F G)) ⟨WalkingPair.left⟩

/-- The comparison `productIsoProd` followed by the second categorical projection is the second
projection of the explicit product. -/
@[simp]
theorem productIsoProd_hom_comp_snd (F G : AlgebraicSpaces B S hS) :
    (productIsoProd B S hS F G).hom ≫ Limits.prod.snd = productProjSnd B S hS F G := by
  simpa using (isLimitBinaryFanProduct B S hS F G).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (pair F G)) ⟨WalkingPair.right⟩

/-- The inverse of `productIsoProd` followed by the first projection of the explicit product is
the first categorical projection. -/
@[simp]
theorem productIsoProd_inv_comp_projFst (F G : AlgebraicSpaces B S hS) :
    (productIsoProd B S hS F G).inv ≫ productProjFst B S hS F G = Limits.prod.fst := by
  rw [← productIsoProd_hom_comp_fst B S hS F G, Iso.inv_hom_id_assoc]

/-- The inverse of `productIsoProd` followed by the second projection of the explicit product is
the second categorical projection. -/
@[simp]
theorem productIsoProd_inv_comp_projSnd (F G : AlgebraicSpaces B S hS) :
    (productIsoProd B S hS F G).inv ≫ productProjSnd B S hS F G = Limits.prod.snd := by
  rw [← productIsoProd_hom_comp_snd B S hS F G, Iso.inv_hom_id_assoc]

/-- The product `a ⨯ a` of a morphism with itself, read through the comparison with the
categorical product. -/
theorem productMapHom_eq_prodMap {F G : AlgebraicSpaces B S hS} (a : F ⟶ G) :
    productMapHom B S hS a =
      (productIsoProd B S hS F F).hom ≫ Limits.prod.map a a ≫
        (productIsoProd B S hS G G).inv := by
  refine product_hom_ext B S hS ?_ ?_ <;> simp [productMapHom_comp_fst, productMapHom_comp_snd]

/-- **A property stable under base change and composition passes to `a ⨯ a`.** This is how the
source of Stacks 0F9U gets an fpqc covering of `Y ⨯ Y` out of a flat, surjective, quasi-compact
presentation `a : E ⟶ Y`: the product of `a` with itself is a composite of two base changes
of `a`. -/
theorem prop_productMapHom (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {F G : AlgebraicSpaces B S hS} (a : F ⟶ G) (ha : P a) :
    P (productMapHom B S hS a) := by
  rw [productMapHom_eq_prodMap]
  exact MorphismProperty.RespectsIso.precomp P _ _
    (MorphismProperty.RespectsIso.postcomp P _ _ (P.prod_map_mem ha ha))

end AlgebraicGeometry.AlgebraicSpaces

namespace AlgebraicGeometry.Space

/-- **The square of a flat, surjective, quasi-compact morphism is an fpqc covering.** For
`a : E ⟶ F` flat, surjective and quasi-compact, the product `a ⨯ a` covers `F ⨯ F` in the fpqc
topology. Each of the three properties passes from `a` to `a ⨯ a` because all three are stable
under base change and under composition, and `a ⨯ a` is a composite of two base changes
of `a`. -/
@[sga "3 VIB 9.2.1" "(ii), special case"]
theorem isCovering_fpqc_productMapHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {E F : AlgebraicSpaces B S hS} (a : E ⟶ F)
    (hqc : IsQuasiCompact B S hS a.hom) (hflat : IsFlat B S hS a.hom)
    (hsurj : IsSurjective B S hS a.hom) :
    Topology.IsCovering .fpqc B S hS
      (fun _ : PUnit.{v + 1} => (AlgebraicSpaces.product B S hS E E).obj)
      (fun _ => (AlgebraicSpaces.productMapHom B S hS a).hom) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsFlat B S hS f.hom) :=
    isFlat_isStableUnderBaseChange B S hS
  refine ⟨(AlgebraicSpaces.product B S hS F F).property,
    fun _ => (AlgebraicSpaces.product B S hS E E).property, ?_⟩
  exact isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective.{u, v} B S hS
    (AlgebraicSpaces.productMapHom B S hS a)
    (AlgebraicSpaces.prop_productMapHom B S hS (quasiCompactProperty B S hS) a hqc)
    (AlgebraicSpaces.prop_productMapHom B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsFlat B S hS f.hom) a hflat)
    (AlgebraicSpaces.prop_productMapHom B S hS (surjectiveMorphismProperty B S hS) a hsurj)

/-- **Separatedness from a flat presentation, with the covering derived.** Let `a : E ⟶ F` be a
flat, surjective, quasi-compact morphism of algebraic spaces over `S`. If the kernel pair
`E ×_F E` is a closed subspace of `E ⨯ E`, then `F` is separated over `S`.

This is the form in which the source of Stacks 0F9U uses the step: what the construction there
supplies about the presentation `a` is that it is flat, surjective and quasi-compact, not that
its square is a covering. The covering is derived. -/
theorem isSeparatedOver_of_kernelPair_of_flat_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {E F : AlgebraicSpaces B S hS} (a : E ⟶ F)
    (hqc : IsQuasiCompact B S hS a.hom) (hflat : IsFlat B S hS a.hom)
    (hsurj : IsSurjective B S hS a.hom)
    (hrel : IsClosedImmersion B S hS
      (AlgebraicSpaces.kernelPairToProduct B S hS a).hom) :
    IsSeparatedOver B S hS F.obj :=
  isSeparatedOver_of_kernelPair_isClosedImmersion.{u, u} B S hS a
    (isCovering_fpqc_productMapHom.{u, u} B S hS a hqc hflat hsurj) hrel

end AlgebraicGeometry.Space

namespace BeauvilleLaszlo.Space

/-! ### Stacks 0F9U at the Beauville--Laszlo square

The base statement of Stacks 0F9U quantifies over an arbitrary commutative square and an
arbitrary `BeauvilleLaszlo.Space.GlueingFunctorSpec` for it. The affine equivalence of Stacks 0F9Q
is about the *canonical* square of a glueing pair, and is proved from the ring theory of that
square, so the gluing functor has to be instantiated there before the two can be combined.
-/

/-- **The gluing functor specification of the Beauville--Laszlo square.** The gluing functor of
Stacks 0F9N, instantiated at the canonical square of a glueing pair `(g : R →+* R', f)`, whose
four corners are `Spec R'_{g f}`, `Spec R_f`, `Spec R'` and `Spec R`.

This is the one `BeauvilleLaszlo.Space.GlueingFunctorSpec` that the affine equivalence of
Stacks 0F9Q speaks about: `BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction` is a
`CategoryTheory.ObjectProperty.lift` of the functor of *this* specification, so a statement
quantified over an abstract specification cannot consume Stacks 0F9Q until it is instantiated
here. It is an `abbrev` so that its `functor` field is reducibly the functor appearing in
`BeauvilleLaszlo.Space.affineGlueingEquivalence`, rather than merely equal to it. -/
noncomputable abbrev canonicalGlueingFunctorSpec {R R' : Type u} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX =
      canGX' g f B hU' hX' ≫ canJX' g B hX' hX) :
    GlueingFunctorSpec B (Spec (.of (Localization.Away (g f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) (Spec (.of R)) hU' hU hX' hX
      (canGU g f B hU' hU) (canGX' g f B hU' hX')
      (canJU f B hU hX) (canJX' g B hX' hX) hcomm :=
  beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _ hcomm

end BeauvilleLaszlo.Space

end
