module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperComparison
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.ImmersionClosure

/-!
# The compactification by closure in a proper scheme

Let `g : U ⟶ V` be a morphism of `AlgebraicGeometry.FTS S` which factors as a closed immersion
`ι : U ⟶ A` into an open `a : A ⟶ P` of a scheme `P` proper over `V`. The scheme-theoretic
closure `Ū` of `U` in `P` is a compactification of `U` over `V`, and the inverse image of `A` in
`Ū` is `U`. Hence, writing `c : Ū ⟶ P` for the closed immersion and `a_π` for the twisted inverse
image of `π : P ⟶ V`,

  `g^!(E) = (a_{c ≫ π} E)|_U ≅ (a_c (a_π E))|_U ≅ a_ι((a_π E)|_A)`,

the last step wherever the map of [Stacks, Tag 0A9L] for the square `U ⟶ Ū` over `A ⟶ P` is
invertible at `a_π E`. This is how [Stacks, Tag 0BV2] computes `f^!` on an affine chart, with
`P = ℙⁿ_V`, `A = 𝔸ⁿ_V`.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.ofClosedInOpen` — the compactification `U ⟶ Ū ⟶ V`.
* `Stacks.Duality.upperShriekOfClosedInOpenObjIsoOfIsIso` — `g^!(E) ≅ a_ι(La^*(a_π E))`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {U V : FTS S} (g : U ⟶ V)
  {A P : Scheme.{u}} [CompactSpace P] [QuasiSeparatedSpace P] (π : P ⟶ V.left) [IsProper π]
  (a : A ⟶ P) [IsOpenImmersion a]
  (ι : U.left ⟶ A) [IsClosedImmersion ι] (hg : ι ≫ a ≫ π = g.left)

/-- The immersion `U ⟶ P`. -/
abbrev closedInOpenImmersion : U.left ⟶ P := ι ≫ a


/-- **The compactification of `g : U ⟶ V` by closure in `P`**: the scheme-theoretic closure `Ū`
of the immersion `U ⟶ A ⟶ P`, with the open immersion `U ⟶ Ū` and the proper morphism
`Ū ⟶ P ⟶ V`. -/
def ofClosedInOpen (ι : U.left ⟶ A) [IsClosedImmersion ι] (hg : ι ≫ a ≫ π = g.left) :
    CompactificationOf (Over.mk g.left) :=
  ⟨StructuredArrow.mk (Y := Over.mk ((closedInOpenImmersion a ι).imageι ≫ π))
      (Over.homMk (closedInOpenImmersion a ι).toImage (by
        simp only [Over.mk_left, Functor.id_obj, Over.mk_hom]
        rw [Scheme.Hom.toImage_imageι_assoc, Category.assoc, hg])),
    ⟨(inferInstance : IsOpenImmersion (closedInOpenImmersion a ι).toImage),
      (inferInstance : IsProper ((closedInOpenImmersion a ι).imageι ≫ π))⟩⟩

omit [QuasiSeparatedSpace S] [CompactSpace P] in
/-- The space of `ofClosedInOpen` is the scheme-theoretic image of `U ⟶ P`. -/
@[simp]
theorem ofClosedInOpen_space :
    (ofClosedInOpen g π a ι hg).space = (closedInOpenImmersion a ι).image :=
  rfl

omit [QuasiSeparatedSpace S] [CompactSpace P] in
/-- The open immersion of `ofClosedInOpen` is the morphism `U ⟶ Ū` into the closure. -/
@[simp]
theorem ofClosedInOpen_immersion :
    (ofClosedInOpen g π a ι hg).immersion = (closedInOpenImmersion a ι).toImage :=
  rfl

omit [QuasiSeparatedSpace S] [CompactSpace P] in
/-- The morphism to the base of `ofClosedInOpen` is the composite `Ū ⟶ P ⟶ V`. -/
@[simp]
theorem ofClosedInOpen_toBase :
    (ofClosedInOpen g π a ι hg).toBase = (closedInOpenImmersion a ι).imageι ≫ π :=
  rfl

omit [QuasiSeparatedSpace S] [CompactSpace P] in
/-- The inverse image of `A` in the closure `Ū` is `U`. -/
theorem preimage_imageι_closedInOpen :
    (closedInOpenImmersion a ι).imageι ⁻¹ᵁ a.opensRange =
      (closedInOpenImmersion a ι).toImage.opensRange :=
  Scheme.Hom.preimage_imageι_eq_opensRange_toImage_of_isClosedImmersion _ a.opensRange
    (ι ≫ (IsOpenImmersion.isoOfRangeEq a a.opensRange.ι (by simp)).hom)
    (by rw [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac])

omit [QuasiSeparatedSpace S] [CompactSpace P] in
/-- **`U` is the inverse image of `A` in the closure**: the square `U ⟶ Ū` over `A ⟶ P` is
cartesian. -/
theorem isPullback_closedInOpen :
    IsPullback (closedInOpenImmersion a ι).toImage ι (closedInOpenImmersion a ι).imageι a :=
  isPullback_of_preimage_opensRange_eq _ _ _ _ (Scheme.Hom.toImage_imageι _)
    (preimage_imageι_closedInOpen a ι)

end AlgebraicGeometry.CompactificationOf

namespace Stacks.Duality

open CompactificationOf

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {U V : FTS S} (g : U ⟶ V)
  {A P : Scheme.{u}} [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace A]
  [QuasiSeparatedSpace A] (π : P ⟶ V.left) [IsProper π] (a : A ⟶ P) [IsOpenImmersion a]
  (ι : U.left ⟶ A) [IsClosedImmersion ι] (hg : ι ≫ a ≫ π = g.left)

/-- The closure `Ū` of `U` in `P` is quasi-compact. -/
instance : CompactSpace (closedInOpenImmersion a ι).image :=
  QuasiCompact.compactSpace_of_compactSpace (closedInOpenImmersion a ι).imageι

/-- The closure `Ū` of `U` in `P` is quasi-separated. -/
instance : QuasiSeparatedSpace (closedInOpenImmersion a ι).image :=
  quasiSeparatedSpace_of_quasiSeparated (closedInOpenImmersion a ι).imageι

/-- The map of [Stacks, Tag 0A9L] for the cartesian square `U ⟶ Ū` over `A ⟶ P`. -/
abbrev closedInOpenRestrictionMap :=
  OpenImmersion.twistedInverseImageRestrictionMap (closedInOpenImmersion a ι).toImage ι
    (closedInOpenImmersion a ι).imageι a
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (OpenImmersion.isQuasicoherent_homology_derivedRestrict _)
    (OpenImmersion.isQuasicoherent_homology_derivedRestrict _) (isPullback_closedInOpen a ι)

/-- **`g^!(E) ≅ a_ι((a_π E)|_A)` at the compactification by closure in `P`**, wherever the map
of [Stacks, Tag 0A9L] for the square `U ⟶ Ū` over `A ⟶ P` is invertible at `a_π(E)`. -/
def upperShriekOfClosedInOpenObjIsoOfIsIso (E : quasiCoherentDerivedCategory V.left)
    [IsIso ((closedInOpenRestrictionMap a ι).app ((twistedInverseImage π
      (isQuasicoherent_homology_derivedPushforward_of_qcqs π)).obj E))] :
    (upperShriek g (ofClosedInOpen g π a ι hg)).obj E ≅
      (twistedInverseImage ι (isQuasicoherent_homology_derivedPushforward_of_qcqs ι)).obj
        ((quasiCoherentDerivedPullback' a).obj ((twistedInverseImage π
          (isQuasicoherent_homology_derivedPushforward_of_qcqs π)).obj E)) :=
  let aπ := twistedInverseImage π (isQuasicoherent_homology_derivedPushforward_of_qcqs π)
  let aι := twistedInverseImage ι (isQuasicoherent_homology_derivedPushforward_of_qcqs ι)
  let c := (closedInOpenImmersion a ι).imageι
  let t := (closedInOpenImmersion a ι).toImage
  ((quasiCoherentDerivedPullback' t).mapIso
      ((twistedInverseImageCompIso c π _ _ _).app E)) ≪≫
    ((restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback t).app _).symm ≪≫
    asIso ((closedInOpenRestrictionMap a ι).app (aπ.obj E)) ≪≫
    aι.mapIso ((restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback a).app (aπ.obj E))

end Stacks.Duality
