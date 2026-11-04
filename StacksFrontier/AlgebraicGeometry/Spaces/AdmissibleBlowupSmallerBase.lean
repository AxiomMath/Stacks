module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenGaloisDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceGeneralCase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningNoetherianSmallerBase

/-!
# Admissible blowups across a change of base scheme

Let `g : T ⟶ S` be a morphism of schemes of a big fppf site, let `X` be an algebraic space over
`T` and write `Λ X` for its lower-shriek extension to `S` (Stacks 03I5 part (2)).  This file
reflects Stacks 086B along `Λ`: if the extension `Λ f : Λ X' ⟶ Λ X` of a morphism of algebraic
spaces over `T` is a `Λ U`-admissible blowing up, for the open subspace of `Λ X` cut out by an
open subspace `U ⊆ X`, then `f` is a `U`-admissible blowing up of `X` over `T`.  Specialized to
the structural morphism `S ⟶ Spec ℤ` of the site this is the base crossing which the first move
of the proof of Stacks 0GV6 performs and which
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyStep1.lean` records as missing.

Admissibility is made of three conditions, and the two that are not already in the library are
proved here.

* **The centre.**  The closed subspaces of `X` and of `Λ X` are in bijection
  (`AlgebraicGeometry.Space.closedSubspacesRelocalizeEquiv`), the inclusion of a closed subspace
  stays of finite presentation
  (`AlgebraicGeometry.Space.isFinitePresentation_relocalizeSubfunctor_ι_iff`), and the points of
  `X` and of `Λ X` are in bijection (`AlgebraicGeometry.Space.pointsRelocalize_bijective`), so
  disjointness of the point sets of the centre and of `U` reflects.  All three are available.
* **The effective Cartier divisor.**  This is the first thing proved here, and it is where the
  geometry is: `AlgebraicGeometry.Space.isEffectiveCartierDivisor_relocalize_iff`.
* **The terminal object of the category `𝒞` of Stacks 085U.**  This is the second,
  `AlgebraicGeometry.Space.isBlowupAlong_of_relocalize`.

## How the effective Cartier condition crosses the base change

Being an effective Cartier divisor is *not* a categorical property of a morphism of algebraic
spaces: it is the invertibility of the defining ideal sheaf `𝓘_D` on the small étale site of
`X`.  So the equivalence of Stacks 04SG and its full faithfulness say nothing about it directly,
and the condition is carried instead by Stacks 083C, which reads it off the *étale scheme
charts*: `D` is an effective Cartier divisor on `X` exactly when the inverse image of `D` is an
effective Cartier divisor on one surjective étale scheme chart of `X`, equivalently on every
étale scheme chart.

That is a condition on schemes, and the étale scheme charts of `X` and of `Λ X` are the same
schemes: a chart `a : h_U ⟶ X` over `T` gives the chart
`AlgebraicGeometry.Space.relocalizeChartHom` of `Λ X` on the same scheme, étale and surjective
exactly when `a` is, and every chart of `Λ X` arises this way.  Moreover the inverse image
`D ×_X U` is computed by a base change of the closed immersion `D ⟶ X` along the chart, a
morphism of the site whose underlying morphism of schemes is not changed by viewing the site
over `S`.  So the two chart conditions are effective Cartier-ness of the kernel of pullback of
regular functions along *one and the same* closed immersion of schemes
(`AlgebraicGeometry.Space.isSchemeEffectiveCartierPullback_relocalize_iff`), and the reflection
follows.

## How the universal property of Stacks 085U crosses the base change

The extension `Λ` is faithful (`AlgebraicGeometry.relocalizePresheaf_faithful`) but **not**
full: Stacks 04SG is an equivalence onto the *slice* of algebraic spaces over `S` equipped with a
morphism to the representable algebraic space of `T`, so what is true is that a morphism
`Λ X ⟶ Λ Y` commuting with the structural morphisms to that representable presheaf is the
extension of a morphism `X ⟶ Y`
(`AlgebraicGeometry.Space.exists_map_eq_of_comp_viewStructureMap`).  That is exactly enough:
a morphism of the category `𝒞` of Stacks 085U commutes with the morphisms to `X`, hence with
the structural morphisms, so morphisms of `𝒞` between relocalized objects are the
relocalizations of morphisms of `𝒞` over `T`, and finality reflects.

## Main results

* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_relocalize_iff`: **Stacks 083B part (2) is
  preserved and reflected by the lower-shriek extension.**
* `AlgebraicGeometry.Space.isPullbackDefined_relocalize_iff`: the same for Stacks 083Y.
* `AlgebraicGeometry.Space.isBlowupAlong_of_relocalize`: **being the blowup in a closed subspace
  is reflected**, both halves of Stacks 085U.
* `AlgebraicGeometry.Space.isAdmissibleBlowup_of_relocalize` and
  `AlgebraicGeometry.Space.isAdmissibleBlowup_of_relocalize_iso`: **Stacks 086B is reflected**,
  the second absorbing the isomorphism that Stacks 04SG leaves.
* `AlgebraicGeometry.Space.isAdmissibleBlowup_of_viewOverIntegers` and
  `AlgebraicGeometry.Space.isAdmissibleBlowup_of_viewOverIntegers_iso`: the same for the view
  over the terminal scheme of Stacks 03BS.
* `AlgebraicGeometry.Space.exists_map_eq_of_comp_viewStructureMap`: the lower-shriek extension
  is full relative to the structural morphisms.
* `AlgebraicGeometry.Space.relocalizeSubfunctor_preimage` and
  `AlgebraicGeometry.Space.relocalizeSubfunctor_range`: the extension of subfunctors commutes
  with inverse images and with ranges.

## Implementation notes

No tag is attached here.  Stacks 086B is registered on
`AlgebraicGeometry.Space.IsAdmissibleBlowup` and Stacks 083B, 083C, 083Y, 085U and 04SG on the
results used; what this file adds is the transport of those statements along `Λ`, which the
source performs silently in the words "we may view `X` as an algebraic space over `Spec ℤ`".

Only the reflecting direction of Stacks 085U and 086B is proved.  The preserving direction would
need, for an object of `𝒞` over `S`, an object of `𝒞` over `T` whose relocalization it is, which
is `AlgebraicGeometry.Space.exists_relocalizeSpace_iso` together with transport of the Cartier
condition along the resulting isomorphism; it is not needed for the base crossing, where the
hypotheses travel forward and only the conclusion has to be reflected.

## References

* [Stacks Project, Tag 086B](https://stacks.math.columbia.edu/tag/086B)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 0GV6](https://stacks.math.columbia.edu/tag/0GV6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS)

/-! ### Subfunctors across the lower-shriek extension -/

section Subfunctors

variable {X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}

/-- **Membership in the relocalization of a subfunctor.**  A section of `Λ X` over `W` -- a
factorization `ψ` of the structure morphism of `W` together with a section `s` of `X` over
`(W, ψ)` -- lies in the subfunctor of `Λ X` cut out by `Z ⊆ X` exactly when `s` lies in `Z`. -/
theorem mem_relocalizeSubfunctor_iff (Z : Subfunctor X) (W : (BigFppfOver B S hS)ᵒᵖ)
    (x : ((OverShriek.relocalizePresheafFunctor g).obj X).obj W) :
    x ∈ (relocalizeSubfunctor B hT hS g Z).obj W ↔
      x.val.snd ∈ Z.obj (op (Over.mk x.val.fst)) :=
  OverShriek.mem_range_relocalizePresheafFunctor_map_ι g Z W x

/-- **The relocalization of subfunctors commutes with preimages.**  For a morphism
`k : Y ⟶ X` of presheaves on the big fppf site of `T`, the subfunctor of `Λ Y` cut out by the
preimage of `Z` is the preimage along `Λ k` of the subfunctor of `Λ X` cut out by `Z`. -/
theorem relocalizeSubfunctor_preimage {Y : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (Z : Subfunctor X)
    (k : Y ⟶ X) :
    relocalizeSubfunctor B hT hS g (Z.preimage k) =
      (relocalizeSubfunctor B hT hS g Z).preimage
        ((OverShriek.relocalizePresheafFunctor g).map k) := by
  refine Subfunctor.ext (funext fun W => ?_)
  ext x
  rw [mem_relocalizeSubfunctor_iff]
  show _ ↔ ((OverShriek.relocalizePresheafFunctor g).map k).app W x ∈
    (relocalizeSubfunctor B hT hS g Z).obj W
  rw [mem_relocalizeSubfunctor_iff]
  rfl

/-- **The lower-shriek extension on morphisms, read on sections.**  It leaves the factorization
alone and applies the morphism to the section. -/
theorem relocalize_map_app_val {Y : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (p : Y ⟶ X)
    (W : (BigFppfOver B S hS)ᵒᵖ) (x : ((OverShriek.relocalizePresheafFunctor g).obj Y).obj W) :
    (((OverShriek.relocalizePresheafFunctor g).map p).app W x).val =
      ⟨x.val.fst, p.app (op (Over.mk x.val.fst)) x.val.snd⟩ :=
  rfl

/-- **The relocalization of a range is the range of the relocalization.** -/
theorem relocalizeSubfunctor_range {Y : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (p : Y ⟶ X) :
    relocalizeSubfunctor B hT hS g (Subfunctor.range p) =
      Subfunctor.range ((OverShriek.relocalizePresheafFunctor g).map p) := by
  refine Subfunctor.ext (funext fun W => ?_)
  ext x
  rw [mem_relocalizeSubfunctor_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨⟨⟨x.val.fst, t⟩, x.property⟩, Subtype.ext (congrArg (Sigma.mk x.val.fst) ht)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y.val.snd, rfl⟩

end Subfunctors

/-! ### Ranges and preimages along an isomorphism -/

section RangeIso

variable {A A' A'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Precomposing with an isomorphism does not change the range of a morphism of presheaves. -/
theorem range_isIso_comp_presheaf (e : A ⟶ A') [IsIso e] (q : A' ⟶ A'') :
    Subfunctor.range (e ≫ q) = Subfunctor.range q := by
  rw [Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top]

/-- The preimage along an isomorphism of the range of a morphism postcomposed with that
isomorphism is the range of the morphism. -/
theorem preimage_range_comp_isIso_presheaf (q : A ⟶ A') (k : A' ⟶ A'') [IsIso k] :
    (Subfunctor.range (q ≫ k)).preimage k = Subfunctor.range q := by
  refine Subfunctor.ext (funext fun W => ?_)
  have hk : Function.Injective (k.app W) := by
    have h : IsIso (k.app W) := inferInstance
    rw [isIso_iff_bijective] at h
    exact h.1
  ext x
  simp only [Subfunctor.preimage_obj, Subfunctor.range_obj, Set.mem_preimage, Set.mem_range,
    FunctorToTypes.comp]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hk hy⟩, fun ⟨y, hy⟩ => ⟨y, by rw [hy]⟩⟩

end RangeIso

/-! ### Scheme charts across the lower-shriek extension -/

section Charts

variable {X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}

/-- **The scheme chart of `Λ X` attached to a scheme chart of `X`**: the same scheme, read over
`S`, mapping to `Λ X` through the identification `Λ h_U ≅ h_{j U}` of Stacks 03I4 part (2). -/
def relocalizeChartHom {U : BigFppfOver B T hT} (a : yoneda.obj U ⟶ X) :
    yoneda.obj ((Over.map g).obj U) ⟶ (OverShriek.relocalizePresheafFunctor g).obj X :=
  (OverShriek.relocalizeYonedaIso g).inv.app U ≫ (OverShriek.relocalizePresheafFunctor g).map a

/-- The extension of a chart is the attached chart precomposed with an isomorphism. -/
private theorem map_eq_inv_comp_relocalizeChartHom {U : BigFppfOver B T hT}
    (a : yoneda.obj U ⟶ X) :
    (OverShriek.relocalizePresheafFunctor g).map a =
      inv ((OverShriek.relocalizeYonedaIso g).inv.app U) ≫ relocalizeChartHom B hT hS g a := by
  rw [relocalizeChartHom, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- **A scheme chart of `X` is étale exactly when the attached chart of `Λ X` is.** -/
theorem isEtale_relocalizeChartHom_iff (hX : IsAlgebraicSpace B T hT X)
    {U : BigFppfOver B T hT} (a : yoneda.obj U ⟶ X) :
    IsEtale B S hS (relocalizeChartHom B hT hS g a) ↔ IsEtale B T hT a := by
  refine Iff.trans ?_ (isEtale_relocalize_iff B T S hT hS g
    (isAlgebraicSpace_yoneda B T hT U) hX a)
  refine ⟨fun h => ?_, fun h => isEtale_comp B S hS (isEtale_of_isIso B S hS _) h⟩
  rw [map_eq_inv_comp_relocalizeChartHom]
  exact isEtale_comp B S hS (isEtale_of_isIso B S hS _) h

/-- **A scheme chart of `X` is surjective exactly when the attached chart of `Λ X` is.** -/
theorem isSurjective_relocalizeChartHom_iff {U : BigFppfOver B T hT} (a : yoneda.obj U ⟶ X) :
    IsSurjective B S hS (relocalizeChartHom B hT hS g a) ↔ IsSurjective B T hT a := by
  refine Iff.trans ?_ (isSurjective_relocalize_iff B T hT S hS g a)
  refine ⟨fun h => ?_, fun h => isSurjective_comp B S hS (isSurjective_of_isIso B S hS _) h⟩
  rw [map_eq_inv_comp_relocalizeChartHom]
  exact isSurjective_comp B S hS (isSurjective_of_isIso B S hS _) h

/-- **The inverse image of a subfunctor on the attached chart.** -/
theorem preimage_relocalizeChartHom (Z : Subfunctor X) {U : BigFppfOver B T hT}
    (a : yoneda.obj U ⟶ X) :
    (relocalizeSubfunctor B hT hS g Z).preimage (relocalizeChartHom B hT hS g a) =
      (relocalizeSubfunctor B hT hS g (Z.preimage a)).preimage
        ((OverShriek.relocalizeYonedaIso g).inv.app U) := by
  rw [relocalizeChartHom, Subfunctor.preimage_comp, ← relocalizeSubfunctor_preimage]

/-- **A closed-subscheme presentation of the inverse image on a chart relocalizes.**  If the
inverse image of `Z` on the chart `a` is the range of `h_j` for a morphism `j : R ⟶ U` of the
site, then the inverse image of the relocalized subfunctor on the attached chart of `Λ X` is the
range of `h_{j U}` for the same morphism of schemes, read over `S`. -/
theorem preimage_relocalizeChartHom_range (Z : Subfunctor X) {U R : BigFppfOver B T hT}
    (a : yoneda.obj U ⟶ X) (j : R ⟶ U) (hj : Z.preimage a = Subfunctor.range (yoneda.map j)) :
    (relocalizeSubfunctor B hT hS g Z).preimage (relocalizeChartHom B hT hS g a) =
      Subfunctor.range (yoneda.map ((Over.map g).map j)) := by
  rw [preimage_relocalizeChartHom, hj, relocalizeSubfunctor_range]
  have hnat : yoneda.map ((Over.map g).map j) ≫ (OverShriek.relocalizeYonedaIso g).inv.app U =
      (OverShriek.relocalizeYonedaIso g).inv.app R ≫
        (OverShriek.relocalizePresheafFunctor g).map (yoneda.map j) :=
    (OverShriek.relocalizeYonedaIso g).inv.naturality j
  rw [show Subfunctor.range ((OverShriek.relocalizePresheafFunctor g).map (yoneda.map j)) =
      Subfunctor.range (yoneda.map ((Over.map g).map j) ≫
        (OverShriek.relocalizeYonedaIso g).inv.app U) from
    ((range_isIso_comp_presheaf B hS ((OverShriek.relocalizeYonedaIso g).inv.app R)
      ((OverShriek.relocalizePresheafFunctor g).map (yoneda.map j))).symm.trans
      (congrArg Subfunctor.range hnat.symm))]
  exact preimage_range_comp_isIso_presheaf B hS _ _

end Charts

/-! ### Effective Cartier divisors across the lower-shriek extension -/

section Cartier

/-- **The chart condition of Stacks 083C is unchanged by the lower-shriek extension.**  The
inverse image of a closed subspace `D ⊆ X` on a scheme chart `a` of `X` is an effective Cartier
divisor exactly when the inverse image of the subspace it cuts out in `Λ X` is one on the
attached chart of `Λ X`.

Both sides are, by Stacks 083C, effective Cartier-ness of the kernel of pullback of regular
functions along *one and the same* closed immersion of schemes `D ×_X U ⟶ U`: the base change
of `D ⟶ X` along `a` is a morphism of the site whose underlying morphism of schemes is not
changed by viewing the site over `S`.  This is the geometric content of the reflection, and it
is what makes the effective Cartier condition travel: it is read off the small étale charts,
which are the same schemes for `X` and for `Λ X`. -/
theorem isSchemeEffectiveCartierPullback_relocalize_iff (X : AlgebraicSpaces B T hT)
    (D : ClosedSubspaces B T hT X.1) (U : BigFppfOver B T hT) (a : yoneda.obj U ⟶ X.1) :
    IsSchemeEffectiveCartierPullback B S hS (relocalizeSpace B hT hS g X)
        (closedSubspacesRelocalizeEquiv B hT hS g X.1 D) ((Over.map g).obj U)
        (relocalizeChartHom B hT hS g a) ↔
      IsSchemeEffectiveCartierPullback B T hT X D U a := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map ((Over.map g).map (D.2.2.rep.snd a))) :=
    D.2.2.property a (D.2.2.rep.fst a) (D.2.2.rep.snd a) (D.2.2.rep.isPullback a)
  rw [isSchemeEffectiveCartierPullback_iff_ker B S hS _ _ _ _ _
      ((Over.map g).map (D.2.2.rep.snd a))
      (preimage_relocalizeChartHom_range B hT hS g D.1 a (D.2.2.rep.snd a)
        (preimage_eq_range_rep_snd B T hT X D U a)),
    isSchemeEffectiveCartierPullback_iff B T hT X D U a]
  rfl

/-- **Being an effective Cartier divisor is preserved and reflected by the lower-shriek
extension.**  A closed subspace `D` of an algebraic space `X` over `T` is an effective Cartier
divisor exactly when the closed subspace of `Λ X` it cuts out is one.

Stacks 083C reduces both sides to the chart condition, and the chart condition is unchanged:
one surjective étale chart of `X` relocalizes to a surjective étale chart of `Λ X` for the
forward direction, and every chart of `X` relocalizes for the converse. -/
theorem isEffectiveCartierDivisor_relocalize_iff (X : AlgebraicSpaces B T hT)
    (D : ClosedSubspaces B T hT X.1) :
    IsEffectiveCartierDivisor B S hS (relocalizeSpace B hT hS g X)
        (closedSubspacesRelocalizeEquiv B hT hS g X.1 D) ↔
      IsEffectiveCartierDivisor B T hT X D := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h3 : HasEffectiveCartierEtalePullbacks B S hS (relocalizeSpace B hT hS g X)
        (closedSubspacesRelocalizeEquiv B hT hS g X.1 D) :=
      ((isEffectiveCartierDivisor_tfae B S hS (relocalizeSpace B hT hS g X)
        (closedSubspacesRelocalizeEquiv B hT hS g X.1 D)).out 1 3).1 h
    exact ((isEffectiveCartierDivisor_tfae B T hT X D).out 3 1).1 fun U a ha =>
      (isSchemeEffectiveCartierPullback_relocalize_iff B hT hS g X D U a).1
        (h3 _ _ ((isEtale_relocalizeChartHom_iff B hT hS g X.2 a).2 ha))
  · obtain ⟨U, a, hae, has, hsec⟩ := ((isEffectiveCartierDivisor_tfae B T hT X D).out 1 2).1 h
    have h2 : HasEffectiveCartierEtaleCover B S hS (relocalizeSpace B hT hS g X)
        (closedSubspacesRelocalizeEquiv B hT hS g X.1 D) :=
      ⟨(Over.map g).obj U, relocalizeChartHom B hT hS g a,
        (isEtale_relocalizeChartHom_iff B hT hS g X.2 a).2 hae,
        (isSurjective_relocalizeChartHom_iff B hT hS g a).2 has,
        (isSchemeEffectiveCartierPullback_relocalize_iff B hT hS g X D U a).2 hsec⟩
    exact ((isEffectiveCartierDivisor_tfae B S hS (relocalizeSpace B hT hS g X)
      (closedSubspacesRelocalizeEquiv B hT hS g X.1 D)).out 2 1).1 h2

/-- **Stacks 083Y is preserved and reflected by the lower-shriek extension.**  The pullback of a
closed subspace `D ⊆ X` along `f : Y ⟶ X` is defined exactly when the pullback of the closed
subspace of `Λ X` it cuts out is defined along `Λ f`.

The inverse image commutes with the extension,
`AlgebraicGeometry.Space.relocalizeSubfunctor_preimage`, so the two closed subspaces whose
effective Cartier-ness is at stake correspond. -/
theorem isPullbackDefined_relocalize_iff {X Y : AlgebraicSpaces B T hT} (f : Y ⟶ X)
    (D : ClosedSubspaces B T hT X.1) :
    IsPullbackDefined B S hS (relocalizeHom B hT hS g f)
        (closedSubspacesRelocalizeEquiv B hT hS g X.1 D) ↔
      IsPullbackDefined B T hT f D := by
  have he : (⟨(closedSubspacesRelocalizeEquiv B hT hS g X.1 D).1.preimage
          (relocalizeHom B hT hS g f).hom,
        isClosedSubspace_preimage B S hS (relocalizeHom B hT hS g f).hom
          (closedSubspacesRelocalizeEquiv B hT hS g X.1 D).1 (relocalizeSpace B hT hS g X).2
          (relocalizeSpace B hT hS g Y).2 (closedSubspacesRelocalizeEquiv B hT hS g X.1 D).2⟩ :
        ClosedSubspaces B S hS (relocalizeSpace B hT hS g Y).1) =
      closedSubspacesRelocalizeEquiv B hT hS g Y.1
        (⟨D.1.preimage f.hom, isClosedSubspace_preimage B T hT f.hom D.1 X.2 Y.2 D.2⟩ :
          ClosedSubspaces B T hT Y.1) :=
    Subtype.ext (relocalizeSubfunctor_preimage B hT hS g D.1 f.hom).symm
  exact (Iff.of_eq (congrArg (IsEffectiveCartierDivisor B S hS
    (relocalizeSpace B hT hS g Y)) he)).trans
    (isEffectiveCartierDivisor_relocalize_iff B hT hS g Y _)

end Cartier

/-! ### Morphisms across the lower-shriek extension -/

section Homs

variable {X Y : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}

/-- **The structural morphism of the presheaf-level equivalence of Stacks 04SG is the structural
morphism of the lower-shriek extension**, read through the identification of the forward functor
with the extension. -/
theorem smallerBasePresheafForgetIso_inv_app_comp_hom (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) :
    (smallerBasePresheafForgetIso B T S hT hS g).inv.app F ≫
        ((smallerBasePresheafEquivalence B T S hT hS g).functor.obj F).hom =
      OverShriek.viewStructureMap g F := by
  ext W s
  exact Over.OverMorphism.ext rfl

/-- **The lower-shriek extension is full relative to the structural morphisms.**  A morphism
`Λ X ⟶ Λ Y` commuting with the structural morphisms to the representable presheaf of `g` is the
extension of a morphism `X ⟶ Y`.

The extension is *not* full -- it is only faithful,
`AlgebraicGeometry.relocalizePresheaf_faithful` -- so the hypothesis on the structural morphisms
cannot be dropped: it is exactly what makes the morphism one of the slice
`AlgebraicGeometry.SpacesOverSmallerBase` in which Stacks 04SG is an equivalence. -/
theorem exists_map_eq_of_comp_viewStructureMap
    (k : (OverShriek.relocalizePresheafFunctor g).obj X ⟶
      (OverShriek.relocalizePresheafFunctor g).obj Y)
    (hk : k ≫ OverShriek.viewStructureMap g Y = OverShriek.viewStructureMap g X) :
    ∃ α : X ⟶ Y, (OverShriek.relocalizePresheafFunctor g).map α = k := by
  have hX := smallerBasePresheafForgetIso_inv_app_comp_hom B hT hS g X
  have hY := smallerBasePresheafForgetIso_inv_app_comp_hom B hT hS g Y
  have hw : ((smallerBasePresheafForgetIso B T S hT hS g).hom.app X ≫ k ≫
        (smallerBasePresheafForgetIso B T S hT hS g).inv.app Y) ≫
        ((smallerBasePresheafEquivalence B T S hT hS g).functor.obj Y).hom =
      ((smallerBasePresheafEquivalence B T S hT hS g).functor.obj X).hom := by
    simp only [Category.assoc]
    rw [hY, hk, ← hX, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  obtain ⟨α, hα⟩ := (smallerBasePresheafEquivalence B T S hT hS g).functor.map_surjective
    (Over.homMk ((smallerBasePresheafForgetIso B T S hT hS g).hom.app X ≫ k ≫
      (smallerBasePresheafForgetIso B T S hT hS g).inv.app Y) hw)
  refine ⟨α, (cancel_epi ((smallerBasePresheafForgetIso B T S hT hS g).hom.app X)).1 ?_⟩
  have hnat := (smallerBasePresheafForgetIso B T S hT hS g).hom.naturality α
  have hleft : (((smallerBasePresheafEquivalence B T S hT hS g).functor ⋙
        Over.forget (yoneda.obj (Over.mk g))).map α) =
      (smallerBasePresheafForgetIso B T S hT hS g).hom.app X ≫ k ≫
        (smallerBasePresheafForgetIso B T S hT hS g).inv.app Y := by
    rw [show (((smallerBasePresheafEquivalence B T S hT hS g).functor ⋙
        Over.forget (yoneda.obj (Over.mk g))).map α) =
        ((smallerBasePresheafEquivalence B T S hT hS g).functor.map α).left from rfl, hα]
    rfl
  rw [← hnat, hleft, Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end Homs

/-! ### Admissible blowups across the lower-shriek extension -/

section Blowup

variable {X X' : AlgebraicSpaces B T hT}

/-- The underlying morphism of presheaves of the lower-shriek extension of a morphism of
algebraic spaces. -/
theorem relocalizeHom_hom {W : AlgebraicSpaces B T hT} (q : W ⟶ X) :
    (relocalizeHom B hT hS g q).hom = (OverShriek.relocalizePresheafFunctor g).map q.hom :=
  rfl

/-- **The lower-shriek extension of a factorization.**  If `α ≫ f = q` then `Λ α` factors `Λ q`
through `Λ f`. -/
theorem relocalizeHom_comp {W : AlgebraicSpaces B T hT} (f : X' ⟶ X) (q : W ⟶ X) (α : W ⟶ X')
    (hα : α ≫ f = q) :
    relocalizeHom B hT hS g α ≫ relocalizeHom B hT hS g f = relocalizeHom B hT hS g q := by
  subst hα
  exact ObjectProperty.hom_ext _
    ((OverShriek.relocalizePresheafFunctor g).map_comp α.hom f.hom).symm

/-- **A morphism of algebraic spaces over `S` between relocalized spaces, commuting with the
relocalization of a morphism, is the relocalization of a morphism over `T`.**  This is
`AlgebraicGeometry.Space.exists_map_eq_of_comp_viewStructureMap`, whose hypothesis is supplied
by the commutation: the structural morphism of `Λ X'` factors through `Λ f`. -/
theorem exists_hom_eq_of_relocalize {W : AlgebraicSpaces B T hT} (f : X' ⟶ X) (p : W ⟶ X)
    (m : relocalizeSpace B hT hS g W ⟶ relocalizeSpace B hT hS g X')
    (hm : m ≫ relocalizeHom B hT hS g f = relocalizeHom B hT hS g p) :
    ∃ α : W ⟶ X', α ≫ f = p ∧ (relocalizeHom B hT hS g α).hom = m.hom := by
  have hm0 : m.hom ≫ (OverShriek.relocalizePresheafFunctor g).map f.hom =
      (OverShriek.relocalizePresheafFunctor g).map p.hom :=
    congrArg (fun φ : relocalizeSpace B hT hS g W ⟶ relocalizeSpace B hT hS g X => φ.hom) hm
  have hm' : m.hom ≫ OverShriek.viewStructureMap g X'.1 =
      OverShriek.viewStructureMap g W.1 := by
    rw [← OverShriek.relocalize_map_viewStructureMap g f.hom, ← Category.assoc, hm0,
      OverShriek.relocalize_map_viewStructureMap]
  obtain ⟨a, ha⟩ := exists_map_eq_of_comp_viewStructureMap B hT hS g m.hom hm'
  have := relocalizePresheaf_faithful g
  refine ⟨ObjectProperty.homMk a, ObjectProperty.hom_ext _ ?_, ha⟩
  refine (OverShriek.relocalizePresheafFunctor g).map_injective ?_
  calc (OverShriek.relocalizePresheafFunctor g).map
        ((ObjectProperty.homMk a ≫ f : W ⟶ X)).hom
      = (OverShriek.relocalizePresheafFunctor g).map a ≫
        (OverShriek.relocalizePresheafFunctor g).map f.hom := Functor.map_comp _ _ _
    _ = m.hom ≫ (OverShriek.relocalizePresheafFunctor g).map f.hom := by rw [ha]
    _ = (OverShriek.relocalizePresheafFunctor g).map p.hom := hm0

/-- **Being the blowup in a closed subspace is reflected by the lower-shriek extension.**  If
`Λ f : Λ X' ⟶ Λ X` is the blowup of `Λ X` in the closed subspace cut out by `Z`, then `f` is the
blowup of `X` in `Z`.

Both halves of the universal property of Stacks 085U reflect.  Membership in the category `𝒞`
is `AlgebraicGeometry.Space.isPullbackDefined_relocalize_iff`, the effective Cartier reflection.
Finality reflects because the objects of `𝒞` over `T` relocalize to objects of `𝒞` over `S`, and
every morphism between relocalized objects of `𝒞` is the relocalization of one over `T`: a
morphism of `𝒞` commutes with the morphisms to `X`, which is exactly the compatibility with the
structural morphisms that `AlgebraicGeometry.Space.exists_hom_eq_of_relocalize` needs.
Uniqueness is the faithfulness of the extension,
`AlgebraicGeometry.relocalizePresheaf_faithful`. -/
theorem isBlowupAlong_of_relocalize (Z : ClosedSubspaces B T hT X.1) (f : X' ⟶ X)
    (h : IsBlowupAlong B S hS (closedSubspacesRelocalizeEquiv B hT hS g X.1 Z)
      (relocalizeHom B hT hS g f)) :
    IsBlowupAlong B T hT Z f := by
  obtain ⟨hmem, ⟨ht⟩⟩ := h
  have hmemT : IsCartierOver B T hT Z (Over.mk f) :=
    (isPullbackDefined_relocalize_iff B hT hS g f Z).1 hmem
  have := relocalizePresheaf_faithful g
  have hmorph : ∀ (Yo : @CartierOver B T hT X Z) (α : Yo.1.left ⟶ X') (_ : α ≫ f = Yo.1.hom),
      { n : (⟨Over.mk (relocalizeHom B hT hS g Yo.1.hom),
            (isPullbackDefined_relocalize_iff B hT hS g Yo.1.hom Z).2 Yo.2⟩ :
          @CartierOver B S hS (relocalizeSpace B hT hS g X)
            (closedSubspacesRelocalizeEquiv B hT hS g X.1 Z)) ⟶
          ⟨Over.mk (relocalizeHom B hT hS g f), hmem⟩ //
        ((ObjectProperty.ι (@IsCartierOver B S hS (relocalizeSpace B hT hS g X)
          (closedSubspacesRelocalizeEquiv B hT hS g X.1 Z))).map n).left =
            relocalizeHom B hT hS g α } :=
    fun _ α hα => ⟨ObjectProperty.homMk
      (Over.homMk (relocalizeHom B hT hS g α) (relocalizeHom_comp B hT hS g f _ α hα)), rfl⟩
  have huniq : ∀ (Yo : @CartierOver B T hT X Z)
      (m₁ m₂ : Yo ⟶ (⟨Over.mk f, hmemT⟩ : @CartierOver B T hT X Z)), m₁ = m₂ := by
    intro Yo m₁ m₂
    set o₁ := (ObjectProperty.ι (@IsCartierOver B T hT X Z)).map m₁
    set o₂ := (ObjectProperty.ι (@IsCartierOver B T hT X Z)).map m₂
    have hmm := ht.hom_ext (hmorph Yo o₁.left (Over.w o₁)).1
      (hmorph Yo o₂.left (Over.w o₂)).1
    have hleft : relocalizeHom B hT hS g o₁.left = relocalizeHom B hT hS g o₂.left :=
      (hmorph Yo o₁.left (Over.w o₁)).2.symm.trans
        ((congrArg (fun φ => ((ObjectProperty.ι (@IsCartierOver B S hS
          (relocalizeSpace B hT hS g X)
          (closedSubspacesRelocalizeEquiv B hT hS g X.1 Z))).map φ).left) hmm).trans
          (hmorph Yo o₂.left (Over.w o₂)).2)
    refine (ObjectProperty.ι (@IsCartierOver B T hT X Z)).map_injective
      (Over.OverMorphism.ext (ObjectProperty.hom_ext _
        ((OverShriek.relocalizePresheafFunctor g).map_injective ?_)))
    rw [← relocalizeHom_hom B hT hS g o₁.left, ← relocalizeHom_hom B hT hS g o₂.left, hleft]
  have hex : ∀ Yo : @CartierOver B T hT X Z,
      Nonempty (Yo ⟶ (⟨Over.mk f, hmemT⟩ : @CartierOver B T hT X Z)) := by
    intro Yo
    have hm' := ht.from (⟨Over.mk (relocalizeHom B hT hS g Yo.1.hom),
      (isPullbackDefined_relocalize_iff B hT hS g Yo.1.hom Z).2 Yo.2⟩)
    obtain ⟨α, hαf, -⟩ := exists_hom_eq_of_relocalize B hT hS g f Yo.1.hom
      ((ObjectProperty.ι (@IsCartierOver B S hS (relocalizeSpace B hT hS g X)
        (closedSubspacesRelocalizeEquiv B hT hS g X.1 Z))).map hm').left
      (Over.w ((ObjectProperty.ι (@IsCartierOver B S hS (relocalizeSpace B hT hS g X)
        (closedSubspacesRelocalizeEquiv B hT hS g X.1 Z))).map hm'))
    exact ⟨ObjectProperty.homMk (Over.homMk α hαf)⟩
  exact ⟨hmemT, ⟨IsTerminal.ofUniqueHom (fun Yo => (hex Yo).some)
    (fun Yo m => huniq Yo m _)⟩⟩

/-- **Stacks 086B is reflected by the lower-shriek extension.**  If `Λ f : Λ X' ⟶ Λ X` is a
`Λ U`-admissible blowing up of `Λ X`, then `f : X' ⟶ X` is a `U`-admissible blowing up of `X`.

The centre comes home by the bijection of the subfunctor lattices,
`AlgebraicGeometry.Space.closedSubspacesRelocalizeEquiv`; its inclusion stays of finite
presentation by `AlgebraicGeometry.Space.isFinitePresentation_relocalizeSubfunctor_ι_iff`; its
points are the points of the centre read through the bijection
`AlgebraicGeometry.Space.pointsRelocalize_bijective`, so disjointness from the points of `U`
reflects; and being the blowup in that centre reflects by
`AlgebraicGeometry.Space.isBlowupAlong_of_relocalize`. -/
theorem isAdmissibleBlowup_of_relocalize (U : OpenSubspaces B T hT X.1) (f : X' ⟶ X)
    (h : IsAdmissibleBlowup B S hS (openSubspacesRelocalizeEquiv B hT hS g X.1 U)
      (relocalizeHom B hT hS g f)) :
    IsAdmissibleBlowup B T hT U f := by
  obtain ⟨Z', hfp', hdisj', hb'⟩ := h
  obtain ⟨Z, rfl⟩ := (closedSubspacesRelocalizeEquiv B hT hS g X.1).surjective Z'
  refine ⟨Z, (isFinitePresentation_relocalizeSubfunctor_ι_iff B hT hS g Z.1).1 hfp', ?_,
    isBlowupAlong_of_relocalize B hT hS g Z f hb'⟩
  have hdisj : Disjoint
      (Set.range (pointsMap B S hS _ (relocalizeSubfunctor B hT hS g U.1).ι))
      (Set.range (pointsMap B S hS _ (relocalizeSubfunctor B hT hS g Z.1).ι)) := hdisj'
  rw [range_pointsMap_relocalizeSubfunctor_ι B hT hS g U.1,
    range_pointsMap_relocalizeSubfunctor_ι B hT hS g Z.1,
    Set.disjoint_image_iff (pointsRelocalize_bijective B T S hT hS g X.1).1] at hdisj
  exact hdisj

/-- **Stacks 086B is reflected by the lower-shriek extension, up to an isomorphism of the
source.**  The form in which the reflection is consumed: the over-`S` data is an *arbitrary*
algebraic space `Y'` over `Λ X` isomorphic to `Λ X'` over `Λ X`, which is what Stacks 04SG
produces (`AlgebraicGeometry.Space.exists_relocalizeSpace_iso` gives only `Λ X' ≅ Y'`, not
equality).

The isomorphism is absorbed by
`AlgebraicGeometry.Space.IsBlowupAlong.of_iso_over`. -/
theorem isAdmissibleBlowup_of_relocalize_iso {Y' : AlgebraicSpaces B S hS}
    (U : OpenSubspaces B T hT X.1) (f : X' ⟶ X) (f' : Y' ⟶ relocalizeSpace B hT hS g X)
    (e : relocalizeSpace B hT hS g X' ≅ Y') (he : e.hom ≫ f' = relocalizeHom B hT hS g f)
    (h : IsAdmissibleBlowup B S hS (openSubspacesRelocalizeEquiv B hT hS g X.1 U) f') :
    IsAdmissibleBlowup B T hT U f := by
  obtain ⟨Z', hfp', hdisj', hb'⟩ := h
  refine isAdmissibleBlowup_of_relocalize B hT hS g U f ⟨Z', hfp', hdisj', ?_⟩
  rw [← he]
  exact hb'.of_iso_over e

end Blowup

/-! ### Admissible blowups across the view over `Spec ℤ` -/

section OverIntegers

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u})) {X X' : AlgebraicSpaces B S hS}

/-- **Stacks 086B is reflected by the view over `Spec ℤ` of Stacks 03BS.**  If the view of
`f : X' ⟶ X` over the terminal scheme is a `U`-admissible blowing up of the view of `X`, for the
view of an open subspace `U ⊆ X`, then `f` is a `U`-admissible blowing up of `X` over `S`.

This is `AlgebraicGeometry.Space.isAdmissibleBlowup_of_relocalize` for the structural morphism
`S ⟶ Spec ℤ` of the site, which is the base crossing of the first move of the proof of
Stacks 0GV6. -/
theorem isAdmissibleBlowup_of_viewOverIntegers (U : OpenSubspaces B S hS X.1) (f : X' ⟶ X)
    (h : IsAdmissibleBlowup B (⊤_ Scheme.{u}) hZ
      (openSubspacesViewOverIntegersEquiv B S hS hZ X.1 U)
      (relocalizeHom B hS hZ (integersMap B S hS hZ) f)) :
    IsAdmissibleBlowup B S hS U f :=
  isAdmissibleBlowup_of_relocalize B hS hZ (integersMap B S hS hZ) U f h

/-- **Stacks 086B is reflected by the view over `Spec ℤ`, up to an isomorphism of the source.**
The form the first move of the proof of Stacks 0GV6 needs: the admissible blowing up produced
over the terminal scheme has an arbitrary source, which Stacks 04SG identifies with the view of
an algebraic space over `S` only up to isomorphism. -/
theorem isAdmissibleBlowup_of_viewOverIntegers_iso
    {Y' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ} (U : OpenSubspaces B S hS X.1) (f : X' ⟶ X)
    (f' : Y' ⟶ relocalizeSpace B hS hZ (integersMap B S hS hZ) X)
    (e : relocalizeSpace B hS hZ (integersMap B S hS hZ) X' ≅ Y')
    (he : e.hom ≫ f' = relocalizeHom B hS hZ (integersMap B S hS hZ) f)
    (h : IsAdmissibleBlowup B (⊤_ Scheme.{u}) hZ
      (openSubspacesViewOverIntegersEquiv B S hS hZ X.1 U) f') :
    IsAdmissibleBlowup B S hS U f :=
  isAdmissibleBlowup_of_relocalize_iso B hS hZ (integersMap B S hS hZ) U f f' e he h

end OverIntegers

end AlgebraicGeometry.Space

end
