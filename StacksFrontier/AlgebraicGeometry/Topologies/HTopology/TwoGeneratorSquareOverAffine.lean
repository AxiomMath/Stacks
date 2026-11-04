module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorQuotient
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorSupportedSections
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.ThickeningHSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.TwoGeneratorSquareInSite

/-!
# The square of Example 0EVH over an arbitrary affine object of the big h site

The induction of Stacks 0EVI replaces a pair of generators of the ideal of the centre of an
almost blowup square by one generator fewer, and the geometric input of that step is the square
of Example 0EVH: for an affine scheme `X` and two global functions `f₁, f₂` on it there is an
almost blowup square over `X` whose centre is cut out by `(f₁, f₂)` and whose modification and
centre have the shape of Example 0EVH.

Stacks 0EVH itself is stated for `X = Spec A` with coordinates chosen, as
`Stacks.AlmostBlowUp.isAlmostBlowUpSquare_modificationToBase`.  This file transports it along
the canonical isomorphism `X ≅ Spec Γ(X, ⊤)` of an affine scheme, so that no coordinates are
pinned on `X`, and then packages the result inside the big h category over a base scheme: both
the modification and the centre are of finite presentation over `X`, hence below the site's
cutoff, so both are again objects of the site.

## Main results

* `AlgebraicGeometry.nonempty_overIso_centerIdealSheaf_subschemeι`: the closed subscheme of
  `Spec A` cut out by `(f₁, f₂)` is `Spec (A ⧸ (f₁, f₂))`, as a scheme over `Spec A`.
* `AlgebraicGeometry.exists_isTwoGeneratorAlmostBlowUpSquare_of_isAffine`: **the square of
  Example 0EVH over an arbitrary affine scheme.**
* `AlgebraicGeometry.BigHOver.exists_isTwoGeneratorAlmostBlowUpSquare_of_isAffine`: the same
  square with all of its corners realized as objects of the big h category over a base scheme.

## Implementation notes

The transport is a base change along an isomorphism, so no new geometry is needed: Tag 0EV7,
`AlgebraicGeometry.isAlmostBlowUpSquare_baseChange`, holds for an arbitrary base change, and the
isomorphisms exhibiting the shape of Example 0EVH are the projections of the fibre products,
which are isomorphisms because the base change is.  The centre of the base-changed square is
`(f₁, f₂)` on global sections by `Stacks.IdealSheaf.ideal_comap_top_of_isAffine`, the formula for
the inverse image of an ideal sheaf along a morphism of affine schemes, after the two
`Ideal.map`s along `Γ(X, ⊤) ≅ Γ(Spec Γ(X, ⊤), ⊤)` and its inverse cancel.

The identification of the centre of the model square — the closed subscheme of `Spec A` cut out
by the ideal sheaf attached to `(f₁, f₂)` — with `Spec (A ⧸ (f₁, f₂))` is Mathlib's universal
property of closed immersions: the two closed immersions have the same kernel ideal sheaf by
`AlgebraicGeometry.ker_Spec_map_quotient_mk`, so the lift of one through the other is an
isomorphism over `Spec A`.

The objects of the big h category are built with `AlgebraicGeometry.BigHOver.mk`, whose
underlying scheme is the given one by `rfl`.  Their structure morphisms to `X` are built with
`CategoryTheory.Over.homMk` rather than with `AlgebraicGeometry.BigHOver.homMk`: the latter
constructs morphisms *into* an object produced by `AlgebraicGeometry.BigHOver.mk`, whereas the
modification and the centre are morphisms *out of* the new objects.

## References

* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EV7](https://stacks.math.columbia.edu/tag/0EV7)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The centre of the model square is the spectrum of the quotient -/

/-- **The centre of the square of Example 0EVH is `Spec (A ⧸ (f₁, f₂))`.** The closed subscheme
of `Spec A` cut out by the ideal sheaf attached to `(f₁, f₂)` is, as a scheme over `Spec A`, the
spectrum of the quotient ring.

Both morphisms are closed immersions with the same kernel ideal sheaf, by
`AlgebraicGeometry.ker_Spec_map_quotient_mk`, so Mathlib's universal property of closed
immersions lifts one through the other by an isomorphism over `Spec A`. -/
public theorem nonempty_overIso_centerIdealSheaf_subschemeι (A : Type u) [CommRing A]
    (f₁ f₂ : A) :
    Nonempty (Over.mk (Stacks.AlmostBlowUp.centerIdealSheaf A f₁ f₂).subschemeι ≅
      Over.mk (Stacks.AlmostBlowUp.centerToBase A f₁ f₂)) := by
  let : IsClosedImmersion (Stacks.AlmostBlowUp.centerToBase A f₁ f₂) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hker : (Stacks.AlmostBlowUp.centerToBase A f₁ f₂).ker =
      (Stacks.AlmostBlowUp.centerIdealSheaf A f₁ f₂).subschemeι.ker :=
    (ker_Spec_map_quotient_mk (Stacks.AlmostBlowUp.centerIdeal A f₁ f₂)).trans
      (Scheme.IdealSheafData.ker_subschemeι _).symm
  have hiso := IsClosedImmersion.isIso_lift (Stacks.AlmostBlowUp.centerToBase A f₁ f₂)
    (Stacks.AlmostBlowUp.centerIdealSheaf A f₁ f₂).subschemeι hker
  exact ⟨Over.isoMk (asIso (IsClosedImmersion.lift _ _ hker.le))
    (IsClosedImmersion.lift_fac _ _ hker.le)⟩

/-! ### The square of Example 0EVH over an arbitrary affine scheme -/

/-- **The square of Example 0EVH over an arbitrary affine scheme.** For an affine scheme `X` and
two global functions `f₁, f₂` on it there is an almost blowup square over `X` whose centre is the
closed subscheme cut out by `(f₁, f₂)` and whose modification and centre have the shape of
Example 0EVH.

The square is the base change of the model square of Stacks 0EVH along the canonical isomorphism
`X ≅ Spec Γ(X, ⊤)`. -/
public theorem exists_isTwoGeneratorAlmostBlowUpSquare_of_isAffine (XS : Scheme.{u})
    [IsAffine XS] (f₁ f₂ : Γ(XS, ⊤)) :
    ∃ (YS : Scheme.{u}) (bY : YS ⟶ XS) (J : XS.IdealSheafData),
      IsAlmostBlowUpSquare J bY ∧
      IsTwoGeneratorAlmostBlowUpModel bY J.subschemeι ∧
      J.ideal ⟨⊤, isAffineOpen_top XS⟩ = Ideal.span {f₁, f₂} := by
  let := (Stacks.AlmostBlowUp.twoGeneratorSquare (Γ(XS, ⊤) : Type u) f₁ f₂).modificationGraded
  obtain ⟨eC⟩ := nonempty_overIso_centerIdealSheaf_subschemeι (Γ(XS, ⊤) : Type u) f₁ f₂
  refine ⟨pullback XS.isoSpec.hom
      (Stacks.AlmostBlowUp.modificationToBase (Γ(XS, ⊤) : Type u) f₁ f₂), pullback.fst _ _,
    (Stacks.AlmostBlowUp.centerIdealSheaf (Γ(XS, ⊤) : Type u) f₁ f₂).comap XS.isoSpec.hom,
    isAlmostBlowUpSquare_baseChange _ _ _
      (Stacks.AlmostBlowUp.isAlmostBlowUpSquare_modificationToBase (Γ(XS, ⊤) : Type u) f₁ f₂),
    ⟨(Γ(XS, ⊤) : Type u), inferInstance, f₁, f₂, XS.isoSpec,
      asIso (pullback.snd XS.isoSpec.hom
        (Stacks.AlmostBlowUp.modificationToBase (Γ(XS, ⊤) : Type u) f₁ f₂)),
      (Stacks.AlmostBlowUp.centerIdealSheaf (Γ(XS, ⊤) : Type u) f₁ f₂).comapIso XS.isoSpec.hom ≪≫
        asIso (pullback.snd XS.isoSpec.hom
          (Stacks.AlmostBlowUp.centerIdealSheaf (Γ(XS, ⊤) : Type u) f₁ f₂).subschemeι) ≪≫
        (Over.forget _).mapIso eC,
      pullback.condition, ?_⟩, ?_⟩
  · simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc]
    rw [show eC.hom.left ≫ Stacks.AlmostBlowUp.centerToBase (Γ(XS, ⊤) : Type u) f₁ f₂ =
      (Stacks.AlmostBlowUp.centerIdealSheaf (Γ(XS, ⊤) : Type u) f₁ f₂).subschemeι from eC.hom.w,
      ← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  · rw [Stacks.IdealSheaf.ideal_comap_top_of_isAffine]
    have hid : (Stacks.AlmostBlowUp.centerIdealSheaf (Γ(XS, ⊤) : Type u) f₁ f₂).ideal
        ⟨⊤, isAffineOpen_top (Spec Γ(XS, ⊤))⟩ =
        Ideal.map (Scheme.ΓSpecIso Γ(XS, ⊤)).inv.hom (Ideal.span {f₁, f₂}) :=
      (Scheme.IdealSheafData.equivOfIsAffine (X := Spec Γ(XS, ⊤))).apply_symm_apply _
    rw [hid, Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_appTop, Ideal.map_map,
      ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

namespace BigHOver

/-- **The square of Example 0EVH over an arbitrary affine object of the big h site.** For an
object `X` of the big h category over `S` with affine underlying scheme and two global functions
`f₁, f₂` on it, the square of Example 0EVH over `X` has all of its corners in the site: there are
objects `Y` and `Z₁` over `X` whose underlying morphisms form an almost blowup square with centre
cut out by `(f₁, f₂)` and of the shape of Example 0EVH.

The underlying square is
`AlgebraicGeometry.exists_isTwoGeneratorAlmostBlowUpSquare_of_isAffine`; membership in the site
is Stacks 000R (5), `AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`,
applied to the modification and to the centre, both of which are of finite presentation. -/
public theorem exists_isTwoGeneratorAlmostBlowUpSquare_of_isAffine
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : BigHOver B S hS) [IsAffine ((BigHOver.toScheme B S hS).obj X)]
    (f₁ f₂ : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) :
    ∃ (Y Z₁ : BigHOver B S hS) (y : Y ⟶ X) (z₁ : Z₁ ⟶ X)
      (J : ((BigHOver.toScheme B S hS).obj X).IdealSheafData),
      IsAlmostBlowUpSquare J ((BigHOver.toScheme B S hS).map y) ∧
      Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z₁) ≅ Over.mk J.subschemeι) ∧
      IsTwoGeneratorAlmostBlowUpModel ((BigHOver.toScheme B S hS).map y)
        ((BigHOver.toScheme B S hS).map z₁) ∧
      J.ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {f₁, f₂} := by
  have hsize : ((BigHOver.toScheme B S hS).obj X).size < B.cutoff := X.left.property
  obtain ⟨YS, bY, J, hsq, hmodel, hideal⟩ :=
    AlgebraicGeometry.exists_isTwoGeneratorAlmostBlowUpSquare_of_isAffine
      ((BigHOver.toScheme B S hS).obj X) f₁ f₂
  have : LocallyOfFinitePresentation bY := hsq.finitePresentation.1
  have : QuasiCompact bY := hsq.finitePresentation.2.1
  have : LocallyOfFiniteType bY := inferInstance
  have : LocallyOfFinitePresentation J.subschemeι := hsq.center_finitePresentation.1
  have : QuasiCompact J.subschemeι := hsq.center_finitePresentation.2.1
  have : LocallyOfFiniteType J.subschemeι := inferInstance
  have hY : B.Contains YS :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact bY hsize
  have hZ : B.Contains J.subscheme :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact J.subschemeι hsize
  exact ⟨BigHOver.mk B S hS hY (bY ≫ B.inclusion.map X.hom),
    BigHOver.mk B S hS hZ (J.subschemeι ≫ B.inclusion.map X.hom),
    Over.homMk (ObjectProperty.homMk bY), Over.homMk (ObjectProperty.homMk J.subschemeι),
    J, hsq, ⟨Iso.refl _⟩, hmodel, hideal⟩

end BigHOver

end AlgebraicGeometry

end
