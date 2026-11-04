module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsChartSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecOfGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedImage
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global functions of a universally closed algebraic space over an affine base

Let `W` be an algebraic space over a scheme `S` of a big fppf site and let `V` be an object of
the big fppf category over `S` whose underlying scheme is affine.  If `p : W ⟶ V` is
universally closed then the ring `Γ(W, 𝒪_W)` of global regular functions on `W` is integral
over `Γ(V, 𝒪_V)`.  This is the affine-chart content of the first assertion of Stacks 0A0Q, and
it is what `StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctions` feeds the
sections of a direct image into.

The argument is the one Mathlib uses for schemes
(`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`) rather than the source's, which
reads a global function as a morphism to `𝔸¹_V` and cuts down to the scheme-theoretic image.
Given a ring `C` of the working universe which is of finite type over `Γ(V, ⊤)` and injects
into `Γ(W, 𝒪_W)` compatibly with pullback along `p`, the spectrum of `C` is an object of the
site, `W ⟶ Spec C` is universally closed because `Spec C ⟶ V` is affine hence separated, and it
is surjective because its image on points is closed and contains the image of an affine
surjective étale chart of `W`, which is dense since `C` injects into the functions on that
chart.  Stacks 08AJ then makes `Spec C ⟶ V` universally closed, and an affine universally
closed morphism of schemes is integral.  A single global function `h` generates such a `C`,
namely a quotient of a polynomial ring in one variable over `Γ(V, ⊤)`, and `h` is the image of
the variable, so `h` is integral.

## Main definitions

* `AlgebraicGeometry.Space.homOfSchemeHom` reads a morphism of schemes over `S` between the
  schemes underlying two objects of the big fppf category as a morphism of that category, and
  `AlgebraicGeometry.Space.yonedaToSchemePoints` compares the functor of points of an object of
  the category with the functor of points of the scheme underlying it.
* `AlgebraicGeometry.Space.liftToYoneda` factors a morphism of presheaves into the functor of
  points of the scheme underlying an object `Z` of the category through `yoneda.obj Z`, when its
  composite with a structure morphism `Z ⟶ V` of the category is a morphism of the category
  pointwise.
* `AlgebraicGeometry.Space.smallEtaleChartMapToBase` is the morphism of the site from an étale
  scheme chart of `W` to `V` induced by `p`.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_toScheme_map_of_isSurjective`: **Stacks 08AJ**
  followed by **Stacks 03XD** — a surjection from an algebraic space onto a scheme of the site
  over `V` carries universal closedness down to the morphism of schemes `Z ⟶ V`.
* `AlgebraicGeometry.Space.isSurjective_of_universallyClosed_of_denseRange`: a universally
  closed morphism to a scheme of the site whose image contains the dense image of a chart is
  surjective.
* `AlgebraicGeometry.Space.exists_siteObject_of_locallyOfFiniteType`: **Stacks 000R (5)** in the
  shape used here — the source of a finite type morphism into the scheme of an object of the
  category is the scheme of an object of the category over it.
* `AlgebraicGeometry.Space.denseRange_base_specMapOfGlobalHom`: the canonical morphism from an
  affine scheme to the spectrum of a ring injecting into its functions has dense image.
* `AlgebraicGeometry.Space.isIntegral_of_universallyClosed_of_injective_of_finiteType`:
  integrality of a finite type model, which is the geometric heart.
* `AlgebraicGeometry.Space.isIntegral_globalFunctions_of_universallyClosed`: **pullback of
  global functions along a universally closed morphism to an affine object of the site is
  integral.**

## Implementation notes

The spectrum of the model is produced as an object of the site only up to an isomorphism of
schemes (`AlgebraicGeometry.Space.exists_siteObject_of_locallyOfFiniteType` returns one), not
as an equality of schemes.  That is deliberate: `AlgebraicGeometry.BigFppfOver.mk` is
semireducible, so an equality of underlying schemes is invisible to `rw` and to instance
search, whereas an isomorphism is carried along by
`CategoryTheory.MorphismProperty.cancel_left_of_respectsIso` and by the composition instances
of the morphism properties involved.

`Γ(V, ⊤)` lives in `Type u` and the global functions of an algebraic space in `Type (u + 1)`,
so the ring homomorphism whose integrality is proved crosses a universe boundary;
`RingHom.IsIntegral` and `RingHom.IsIntegralElem` are stated for independent universes, and the
finite type model is what keeps the geometry inside `Type u`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 03XD](https://stacks.math.columbia.edu/tag/03XD)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of schemes over `S` between the schemes underlying two objects of the big fppf
category over `S`, read as a morphism of that category. -/
noncomputable def homOfSchemeHom {T T' : BigFppfOver B S hS}
    (φ : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B S hS).obj T')
    (hφ : φ ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom) : T ⟶ T' :=
  Over.homMk (B.inclusion.preimage φ) (B.inclusion.map_injective
    (by rw [Functor.map_comp, B.inclusion.map_preimage]; exact hφ))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.homOfSchemeHom` is the given
one. -/
@[simp]
theorem toScheme_map_homOfSchemeHom {T T' : BigFppfOver B S hS}
    (φ : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B S hS).obj T')
    (hφ : φ ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom) :
    (BigFppfOver.toScheme B S hS).map (homOfSchemeHom B S hS φ hφ) = φ :=
  B.inclusion.map_preimage φ

/-- The functor of points of an object of the big fppf category over `S`, compared with the
functor of points of the scheme underlying it: a morphism of the category is read as a
morphism of schemes. -/
def yonedaToSchemePoints (T : BigFppfOver B S hS) :
    yoneda.obj T ⟶ schemePoints B S hS ((BigFppfOver.toScheme B S hS).obj T) where
  app U := ↾fun g : U.unop ⟶ T => (BigFppfOver.toScheme B S hS).map g
  naturality _ _ k := by
    ext g
    exact (BigFppfOver.toScheme B S hS).map_comp k.unop g

/-- On a scheme-valued point the comparison with the functor of points of the underlying
scheme is the underlying morphism of schemes. -/
@[simp]
theorem yonedaToSchemePoints_app (T : BigFppfOver B S hS) (U : (BigFppfOver B S hS)ᵒᵖ)
    (g : U.unop ⟶ T) :
    (yonedaToSchemePoints B S hS T).app U g = (BigFppfOver.toScheme B S hS).map g := rfl

/-- A scheme-valued point of the functor of points of the scheme underlying an object `Z` of
the big fppf category over `S` whose composite with a structure morphism `Z ⟶ V` of the
category is a morphism of the category is itself a morphism over `S`. -/
theorem liftToYoneda_comp_structureHom {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Z V : BigFppfOver B S hS}
    (π₀ : F ⟶ schemePoints B S hS ((BigFppfOver.toScheme B S hS).obj Z))
    (z : Z ⟶ V) (q : F ⟶ yoneda.obj V)
    (hq : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (w : F.obj U),
      π₀.app U w ≫ (BigFppfOver.toScheme B S hS).map z =
        (BigFppfOver.toScheme B S hS).map (q.app U w))
    (U : (BigFppfOver B S hS)ᵒᵖ) (w : F.obj U) :
    π₀.app U w ≫ B.inclusion.map Z.hom = B.inclusion.map U.unop.hom := by
  rw [← BigFppfOver.toScheme_map_comp_structureHom B S hS z, ← Category.assoc, hq U w]
  exact BigFppfOver.toScheme_map_comp_structureHom B S hS (q.app U w)

/-- **A morphism of presheaves into the functor of points of a scheme of the site which lies
over the site factors through the site.**  A morphism `π₀` of presheaves into the functor of
points of the scheme underlying an object `Z` of the big fppf category over `S` whose composite
with a structure morphism `Z ⟶ V` of the category is a morphism `q` of the category, pointwise,
takes values in the morphisms over `S`, and is therefore a morphism into `yoneda.obj Z`. -/
noncomputable def liftToYoneda {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Z V : BigFppfOver B S hS}
    (π₀ : F ⟶ schemePoints B S hS ((BigFppfOver.toScheme B S hS).obj Z))
    (z : Z ⟶ V) (q : F ⟶ yoneda.obj V)
    (hq : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (w : F.obj U),
      π₀.app U w ≫ (BigFppfOver.toScheme B S hS).map z =
        (BigFppfOver.toScheme B S hS).map (q.app U w)) :
    F ⟶ yoneda.obj Z where
  app U := ↾fun w => homOfSchemeHom B S hS (π₀.app U w)
    (liftToYoneda_comp_structureHom B S hS π₀ z q hq U w)
  naturality U U' k := by
    ext w
    change homOfSchemeHom B S hS (π₀.app U' (F.map k w))
        (liftToYoneda_comp_structureHom B S hS π₀ z q hq U' (F.map k w)) =
      k.unop ≫ homOfSchemeHom B S hS (π₀.app U w)
        (liftToYoneda_comp_structureHom B S hS π₀ z q hq U w)
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, toScheme_map_homOfSchemeHom, toScheme_map_homOfSchemeHom]
    exact ConcreteCategory.congr_hom (π₀.naturality k) w

/-- The morphism of schemes underlying a value of `AlgebraicGeometry.Space.liftToYoneda` is
the given scheme-valued point. -/
@[simp]
theorem toScheme_map_liftToYoneda_app {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Z V : BigFppfOver B S hS}
    (π₀ : F ⟶ schemePoints B S hS ((BigFppfOver.toScheme B S hS).obj Z))
    (z : Z ⟶ V) (q : F ⟶ yoneda.obj V)
    (hq : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (w : F.obj U),
      π₀.app U w ≫ (BigFppfOver.toScheme B S hS).map z =
        (BigFppfOver.toScheme B S hS).map (q.app U w))
    (U : (BigFppfOver B S hS)ᵒᵖ) (w : F.obj U) :
    (BigFppfOver.toScheme B S hS).map ((liftToYoneda B S hS π₀ z q hq).app U w) =
      π₀.app U w :=
  toScheme_map_homOfSchemeHom B S hS (π₀.app U w)
    (liftToYoneda_comp_structureHom B S hS π₀ z q hq U w)

/-- The factorization of `AlgebraicGeometry.Space.liftToYoneda` lies over the given morphism
to `V`. -/
theorem liftToYoneda_comp_yoneda_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Z V : BigFppfOver B S hS}
    (π₀ : F ⟶ schemePoints B S hS ((BigFppfOver.toScheme B S hS).obj Z))
    (z : Z ⟶ V) (q : F ⟶ yoneda.obj V)
    (hq : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (w : F.obj U),
      π₀.app U w ≫ (BigFppfOver.toScheme B S hS).map z =
        (BigFppfOver.toScheme B S hS).map (q.app U w)) :
    liftToYoneda B S hS π₀ z q hq ≫ yoneda.map z = q := by
  ext U w
  show (liftToYoneda B S hS π₀ z q hq).app U w ≫ z = q.app U w
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, toScheme_map_liftToYoneda_app]
  exact hq U w

/-- The factorization of `AlgebraicGeometry.Space.liftToYoneda`, read back in the functor of
points of the underlying scheme, is the morphism it was built from. -/
theorem liftToYoneda_comp_yonedaToSchemePoints {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Z V : BigFppfOver B S hS}
    (π₀ : F ⟶ schemePoints B S hS ((BigFppfOver.toScheme B S hS).obj Z))
    (z : Z ⟶ V) (q : F ⟶ yoneda.obj V)
    (hq : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (w : F.obj U),
      π₀.app U w ≫ (BigFppfOver.toScheme B S hS).map z =
        (BigFppfOver.toScheme B S hS).map (q.app U w)) :
    liftToYoneda B S hS π₀ z q hq ≫ yonedaToSchemePoints B S hS Z = π₀ := by
  ext U w
  exact toScheme_map_liftToYoneda_app B S hS π₀ z q hq U w

/-- The morphism of the site from an étale scheme chart of `W` to `V` induced by a morphism
`p : W ⟶ V` of presheaves. -/
noncomputable def smallEtaleChartMapToBase {W : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
    (p : W.obj ⟶ yoneda.obj V) (c : SmallEtale B S hS W.obj) :
    (SmallEtale.toOver B S hS W.obj).obj c ⟶ V :=
  yoneda.preimage (c.obj.hom ≫ p)

/-- The chart morphism to the base is characterized by its Yoneda morphism, which is the chart
followed by the given morphism to `V`. -/
theorem yoneda_map_smallEtaleChartMapToBase {W : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
    (p : W.obj ⟶ yoneda.obj V) (c : SmallEtale B S hS W.obj) :
    yoneda.map (smallEtaleChartMapToBase B S hS p c) = c.obj.hom ≫ p :=
  yoneda.map_preimage _

/-- **Universal closedness descends along a surjection, in the represented case.**  If
`π : W ⟶ Z` is a surjective morphism from an algebraic space to a scheme of the site and the
composite `W ⟶ Z ⟶ V` is universally closed, then the morphism of schemes under `Z ⟶ V` is
universally closed.  This is Stacks 08AJ followed by Stacks 03XD. -/
theorem universallyClosed_toScheme_map_of_isSurjective
    {W : AlgebraicSpaces B S hS} {Z V : BigFppfOver B S hS}
    (p : W.obj ⟶ yoneda.obj V) (huc : UniversallyClosed B S hS p)
    (z : Z ⟶ V) (π : W.obj ⟶ yoneda.obj Z) (hπ : π ≫ yoneda.map z = p)
    (hsurj : IsSurjective B S hS π) :
    AlgebraicGeometry.UniversallyClosed ((BigFppfOver.toScheme B S hS).map z) := by
  have hZ : IsAlgebraicSpace B S hS (yoneda.obj Z) := isAlgebraicSpace_yoneda B S hS Z
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hyo : UniversallyClosed B S hS (yoneda.map z) :=
    universallyClosed_of_isSurjective B S hS W.property hZ hV π p (yoneda.map z) hπ hsurj huc
  exact (presheaf_yoneda_map_iff B S hS
    (P := @AlgebraicGeometry.UniversallyClosed.{u}) inferInstance z).mp
    ((presheaf_universallyClosed_iff B S hS hZ hV
      (Functor.relativelyRepresentable.map yoneda z)).mpr hyo)

/-- **A universally closed morphism to a scheme of the site with dense image is surjective.**
The image on points of a universally closed morphism is closed, and it contains the image of
a chart whose morphism of schemes has dense range. -/
theorem isSurjective_of_universallyClosed_of_denseRange
    {W : AlgebraicSpaces B S hS} {Z : BigFppfOver B S hS}
    (π : W.obj ⟶ yoneda.obj Z) (hπ : UniversallyClosed B S hS π)
    {P : BigFppfOver B S hS} (a : yoneda.obj P ⟶ W.obj) (g : P ⟶ Z)
    (hag : yoneda.map g = a ≫ π)
    (hdense : DenseRange ((BigFppfOver.toScheme B S hS).map g).base) :
    IsSurjective B S hS π := by
  classical
  let := pointTopology B S hS W.obj
  let := pointTopology B S hS (yoneda.obj Z)
  have hclosed : IsClosed (Set.range (pointsMap B S hS W.obj π)) :=
    (isClosed_of_universallyClosed B S hS (isAlgebraicSpace_yoneda B S hS Z) π
      hπ).isClosed_range
  have himg : IsClosed (pointsToScheme B S hS Z '' Set.range (pointsMap B S hS W.obj π)) :=
    (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS Z _).1 hclosed
  have hsub : Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆
      pointsToScheme B S hS Z '' Set.range (pointsMap B S hS W.obj π) := by
    have key := image_pointsToScheme_image_pointsMap B S hS g Set.univ
    rw [Set.image_univ, Set.image_univ,
      Set.range_eq_univ.2 (surjective_pointsToScheme B S hS P), Set.image_univ] at key
    rw [← key]
    refine Set.image_mono ?_
    rw [hag, pointsMap_comp]
    exact Set.range_comp_subset_range _ _
  have htop : pointsToScheme B S hS Z '' Set.range (pointsMap B S hS W.obj π) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hdense.closure_eq]
    exact himg.closure_subset_iff.2 hsub
  intro w
  obtain ⟨y, hy⟩ : pointsToScheme B S hS Z w ∈
      pointsToScheme B S hS Z '' Set.range (pointsMap B S hS W.obj π) := by
    rw [htop]; exact Set.mem_univ _
  obtain ⟨x, hx⟩ := hy.1
  exact ⟨x, injective_pointsToScheme B S hS Z (by rw [hx]; exact hy.2)⟩


/-- **A scheme of the big fppf category over `S` out of a finite type morphism into one.**
A scheme with a morphism locally of finite type and quasi-compact to the scheme underlying an
object `V` of the category is isomorphic to the scheme underlying an object of the category
over `V`. -/
theorem exists_siteObject_of_locallyOfFiniteType {V : BigFppfOver B S hS} {T : Scheme.{u}}
    (zv : T ⟶ (BigFppfOver.toScheme B S hS).obj V)
    [LocallyOfFiniteType zv] [QuasiCompact zv] :
    ∃ (Z : BigFppfOver B S hS) (z : Z ⟶ V) (e : T ≅ (BigFppfOver.toScheme B S hS).obj Z),
      e.hom ≫ (BigFppfOver.toScheme B S hS).map z = zv := by
  have hsize : B.Contains T :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact zv
      (show B.Contains ((BigFppfOver.toScheme B S hS).obj V) from V.left.property)
  refine ⟨BigFppfOver.mk B S hS hsize (zv ≫ B.inclusion.map V.hom),
    homOfSchemeHom B S hS (T := BigFppfOver.mk B S hS hsize (zv ≫ B.inclusion.map V.hom))
      (T' := V) zv rfl, Iso.refl _, ?_⟩
  exact (Category.id_comp ((BigFppfOver.toScheme B S hS).map
      (homOfSchemeHom B S hS (T := BigFppfOver.mk B S hS hsize (zv ≫ B.inclusion.map V.hom))
        (T' := V) zv rfl))).trans
    (toScheme_map_homOfSchemeHom B S hS
      (T := BigFppfOver.mk B S hS hsize (zv ≫ B.inclusion.map V.hom)) (T' := V) zv rfl)

/-- **The canonical morphism from an affine scheme to the spectrum of a ring injecting into
its functions has dense image.**  The morphism is the isomorphism `Pz ≅ Spec Γ(Pz, ⊤)`
followed by the spectrum of an injective ring homomorphism, whose image is dense because its
kernel is zero. -/
theorem denseRange_base_specMapOfGlobalHom {Pz : Scheme.{u}} [IsAffine Pz] {C : Type u}
    [CommRing C] (χ : C →+* Γ(Pz, ⊤)) (hχ : Function.Injective χ) :
    DenseRange (specMapOfGlobalHom C χ).base := by
  have hd : DenseRange (Spec.map (CommRingCat.ofHom χ)).base := by
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical χ).2 ?_
    rw [show RingHom.ker χ = ⊥ from (RingHom.injective_iff_ker_eq_bot χ).1 hχ]
    exact bot_le
  have hsurj : Function.Surjective Pz.toSpecΓ.base := Scheme.Hom.surjective Pz.toSpecΓ
  have hfun : ((Pz.toSpecΓ ≫ Spec.map (CommRingCat.ofHom χ)).base : Pz → _) =
      (Spec.map (CommRingCat.ofHom χ)).base ∘ Pz.toSpecΓ.base :=
    funext fun x => Scheme.Hom.comp_apply _ _ x
  show Dense (Set.range ((Pz.toSpecΓ ≫ Spec.map (CommRingCat.ofHom χ)).base : Pz → _))
  rw [hfun, Set.range_comp, hsurj.range_eq, Set.image_univ]
  exact hd

/-- **The chart value of the canonical morphism to a spectrum, followed by the structure
morphism.**  Let `Vz` be affine, let `ρ : Γ(Vz, ⊤) →+* C` and `χ : C →+* Γ(Pz, ⊤)` be ring
homomorphisms and let `m : Pz ⟶ Vz` be a morphism of schemes whose map on global functions is
`χ ∘ ρ`.  Then the morphism `Pz ⟶ Spec C` attached to `χ`, followed by the morphism
`Spec C ⟶ Vz` attached to `ρ`, is `m`. -/
theorem specMapOfGlobalHom_comp_specMap_comp_isoSpec_inv {Pz Vz : Scheme.{u}} [IsAffine Vz]
    {C : Type u} [CommRing C] (ρ : Γ(Vz, ⊤) →+* C) (χ : C →+* Γ(Pz, ⊤))
    (m : Pz ⟶ Vz) (hm : m.appTop.hom = χ.comp ρ) :
    specMapOfGlobalHom C χ ≫ Spec.map (CommRingCat.ofHom ρ) ≫ Vz.isoSpec.inv = m := by
  have h1 : specMapOfGlobalHom C χ ≫ Spec.map (CommRingCat.ofHom ρ) =
      Pz.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (χ.comp ρ)) := by
    rw [specMapOfGlobalHom, Category.assoc, ← Spec.map_comp]
    rfl
  have h2 : m ≫ Vz.toSpecΓ = Pz.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (χ.comp ρ)) := by
    rw [Scheme.toSpecΓ_naturality]
    refine congrArg (fun k => Pz.toSpecΓ ≫ Spec.map k) (CommRingCat.hom_ext ?_)
    rw [hm]
    rfl
  rw [← Category.assoc, h1, ← h2, Category.assoc, ← Vz.isoSpec_hom, Iso.hom_inv_id,
    Category.comp_id]

/-- **Integrality of a finite-type model of the global functions of a universally closed
algebraic space over an affine base.**  Let `W` be an algebraic space over `S`, let `V` be an
object of the big fppf category over `S` with affine underlying scheme and let
`p : W ⟶ V` be universally closed.  Let `C` be a ring of the working universe with a
homomorphism `ρ : Γ(V, ⊤) →+* C` of finite type and an injective homomorphism
`κ : C →+* Γ(W, 𝒪_W)` whose composite with `ρ` is pullback of functions along `p` on every
étale scheme chart of `W`.  Then `ρ` is integral.

The proof is the one Mathlib uses for schemes: `W ⟶ Spec C` is universally closed, because
`Spec C ⟶ V` is affine hence separated, and it is surjective, because its image on points is
closed and contains the image of an affine surjective étale chart of `W`, which is dense since
`C` injects into the functions on that chart.  Stacks 08AJ then makes `Spec C ⟶ V` universally
closed, and an affine universally closed morphism of schemes is integral. -/
theorem isIntegral_of_universallyClosed_of_injective_of_finiteType
    {W : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (p : W.obj ⟶ yoneda.obj V) (huc : UniversallyClosed B S hS p)
    (C : Type u) [CommRing C]
    (ρ : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+* C)
    (hρ : RingHom.FiniteType ρ)
    (κ : C →+* globalFunctions B S hS W.obj) (hκ : Function.Injective κ)
    (hcompat : ∀ c : SmallEtale B S hS W.obj,
      (globalFunctionsChartRestriction B S hS W c).comp (κ.comp ρ) =
        ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS p c)).appTop.hom) :
    ρ.IsIntegral := by
  have := hV
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom ρ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 hρ
  set zv : Spec (CommRingCat.of C) ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    Spec.map (CommRingCat.ofHom ρ) ≫ ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv
    with hzvdef
  have : LocallyOfFiniteType zv := by rw [hzvdef]; infer_instance
  have hzvaff : _root_.AlgebraicGeometry.IsAffineHom zv := by rw [hzvdef]; infer_instance
  obtain ⟨Z, z, e, he⟩ := exists_siteObject_of_locallyOfFiniteType B S hS zv
  have hzeq : (BigFppfOver.toScheme B S hS).map z = e.inv ≫ zv := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map z) := by
    rw [hzeq]; infer_instance
  have hsep : IsSeparated B S hS (yoneda.map z) :=
    (isSeparated_yoneda_map_iff B S hS z).2 (AlgebraicGeometry.IsSeparated.of_isAffineHom _)
  -- the canonical morphism to the spectrum
  obtain ⟨π₀, hπ₀⟩ := exists_specMap_of_globalHom B S hS W C κ
  -- an affine surjective étale chart of `W`
  have hWqc : IsQuasiCompactSpace B S hS W.obj :=
    isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS V hV W.property
      (isAlgebraicSpace_yoneda B S hS V) p huc
  obtain ⟨c₀, hc₀aff, hc₀surj, hc₀etale⟩ :
      ∃ c : SmallEtale B S hS W.obj,
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.obj).obj c)) ∧
          (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
            (BigFppfOver.toScheme B S hS)).presheaf c.obj.hom ∧
          (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
            (BigFppfOver.toScheme B S hS)).presheaf c.obj.hom := by
    obtain ⟨P, a, hPaff, haSurj, haEtale⟩ :=
      (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS W.obj
        W.property).1 hWqc
    exact ⟨chartFromEtaleHom B S hS W P a (presheaf_etale_of_isEtale B S hS haEtale), hPaff,
      haSurj, presheaf_etale_of_isEtale B S hS haEtale⟩
  have := hc₀aff
  set χ : C →+* Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS W.obj).obj c₀), ⊤) :=
    (globalFunctionsChartRestriction B S hS W c₀).comp κ with hχdef
  have hχinj : Function.Injective χ :=
    (injective_globalFunctionsChartRestriction_of_isSurjective B S hS W c₀
      ((presheafSurjective_iff_isSurjective_yoneda B S hS W.obj W.property _
        c₀.obj.hom).1 hc₀surj)).comp hκ
  -- the chart value of the canonical morphism, composed with `Spec C ⟶ V`
  have hchart : specMapOfGlobalHom C χ ≫ zv =
      (BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS p c₀) := by
    rw [hzvdef]
    refine specMapOfGlobalHom_comp_specMap_comp_isoSpec_inv ρ χ _ ?_
    rw [← hcompat c₀, hχdef]
    rfl
  -- a point of the chart, read in the functor of points of a scheme
  have hpt : ∀ {P T : BigFppfOver B S hS} (g : P ⟶ T),
      yonedaEquiv (yoneda.map g ≫ yonedaToSchemePoints B S hS T) =
        (BigFppfOver.toScheme B S hS).map g := fun g => by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact yonedaToSchemePoints_app B S hS _ _ g
  -- the canonical morphism on the chart, followed by a morphism out of `Spec C`
  have hchartπ : ∀ {T : Scheme.{u}} (f : Spec (CommRingCat.of C) ⟶ T),
      yonedaEquiv (c₀.obj.hom ≫ π₀ ≫ schemePointsMap B S hS f) = specMapOfGlobalHom C χ ≫ f :=
    fun f => by
    rw [← Category.assoc, yonedaEquiv_comp_schemePointsMap]
    exact congrArg (fun k => k ≫ f) (hπ₀ c₀)
  -- the canonical morphism agrees with `p` after `Spec C ⟶ V`
  have hEq : π₀ ≫ schemePointsMap B S hS zv = p ≫ yonedaToSchemePoints B S hS V := by
    refine hom_ext_of_etale_atlas B S hS W.property.isSheaf
      (isSheaf_schemePoints B S hS ((BigFppfOver.toScheme B S hS).obj V)) c₀.obj.hom hc₀surj
      hc₀etale ?_
    refine yonedaEquiv.injective ((hchartπ zv).trans (hchart.trans ?_))
    rw [← Category.assoc, ← yoneda_map_smallEtaleChartMapToBase B S hS p c₀, hpt]
  -- the canonical morphism, read as a morphism into the site object
  have hq : ∀ (U : (BigFppfOver B S hS)ᵒᵖ) (w : W.obj.obj U),
      (π₀ ≫ schemePointsMap B S hS e.hom).app U w ≫ (BigFppfOver.toScheme B S hS).map z =
        (BigFppfOver.toScheme B S hS).map (p.app U w) := by
    intro U w
    have h1 : (π₀ ≫ schemePointsMap B S hS e.hom).app U w = π₀.app U w ≫ e.hom := rfl
    rw [h1, Category.assoc, he]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hEq U) w
  set π := liftToYoneda B S hS (π₀ ≫ schemePointsMap B S hS e.hom) z p hq with hπdef
  have hπz : π ≫ yoneda.map z = p :=
    liftToYoneda_comp_yoneda_map B S hS (π₀ ≫ schemePointsMap B S hS e.hom) z p hq
  have hπ0 : π ≫ yonedaToSchemePoints B S hS Z = π₀ ≫ schemePointsMap B S hS e.hom :=
    liftToYoneda_comp_yonedaToSchemePoints B S hS (π₀ ≫ schemePointsMap B S hS e.hom) z p hq
  obtain ⟨g, hg⟩ : ∃ g : (SmallEtale.toOver B S hS W.obj).obj c₀ ⟶ Z,
      yoneda.map g = c₀.obj.hom ≫ π := ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hgs : (BigFppfOver.toScheme B S hS).map g = specMapOfGlobalHom C χ ≫ e.hom := by
    rw [← hpt, hg, Category.assoc, hπ0, ← hchartπ]
  -- the chart has dense image in `Spec C`
  have hdense : DenseRange ((BigFppfOver.toScheme B S hS).map g).base := by
    rw [hgs]
    exact ((Scheme.Hom.surjective e.hom).denseRange).comp
      (denseRange_base_specMapOfGlobalHom χ hχinj) e.hom.base.hom.continuous
  -- the canonical morphism is universally closed and surjective
  have hπuc : UniversallyClosed B S hS π :=
    universallyClosed_of_comp_of_isSeparated B S hS W.property
      (isAlgebraicSpace_yoneda B S hS Z) (isAlgebraicSpace_yoneda B S hS V) π (yoneda.map z)
      (by rw [hπz]; exact huc) hsep
  have hsurjπ : IsSurjective B S hS π :=
    isSurjective_of_universallyClosed_of_denseRange B S hS π hπuc c₀.obj.hom g hg hdense
  have huczs : AlgebraicGeometry.UniversallyClosed ((BigFppfOver.toScheme B S hS).map z) :=
    universallyClosed_toScheme_map_of_isSurjective B S hS p huc z π hπz hsurjπ
  have huczv : _root_.AlgebraicGeometry.UniversallyClosed zv := by
    rw [← he]; infer_instance
  have hint : _root_.AlgebraicGeometry.IsIntegralHom zv :=
    _root_.AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom.2
      ⟨huczv, hzvaff⟩
  have h2 : Spec.map (CommRingCat.ofHom ρ) =
      zv ≫ ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom := by
    rw [hzvdef, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have : _root_.AlgebraicGeometry.IsIntegralHom (Spec.map (CommRingCat.ofHom ρ)) := by
    rw [h2]; infer_instance
  exact (_root_.AlgebraicGeometry.IsIntegralHom.SpecMap_iff
    (φ := CommRingCat.ofHom ρ)).1 inferInstance

/-- **The global functions of a universally closed algebraic space over an affine base are
integral over the base.**  Let `W` be an algebraic space over `S` and let `V` be an object of
the big fppf category over `S` with affine underlying scheme.  If `p : W ⟶ V` is universally
closed then pullback of regular functions along `p` is an integral ring homomorphism.

The hypothesis `hψ` says that `ψ` *is* that pullback: on every étale scheme chart `c` of `W`
it is pullback of functions along the induced morphism of schemes `c ⟶ V`.

A global function `h` on `W` generates, over `Γ(V, ⊤)`, a quotient `C` of a polynomial ring in
one variable, which is of finite type over `Γ(V, ⊤)` and injects into the functions on `W`;
`AlgebraicGeometry.Space.isIntegral_of_universallyClosed_of_injective_of_finiteType` makes `C`
integral over `Γ(V, ⊤)`, and `h` is the image of the variable. -/
@[ega "II 7.3.11" "Integrality of Γ(X"]
theorem isIntegral_globalFunctions_of_universallyClosed
    {W : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (p : W.obj ⟶ yoneda.obj V) (huc : UniversallyClosed B S hS p)
    (ψ : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+* globalFunctions B S hS W.obj)
    (hψ : ∀ c : SmallEtale B S hS W.obj,
      (globalFunctionsChartRestriction B S hS W c).comp ψ =
        ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS p c)).appTop.hom) :
    ψ.IsIntegral := by
  intro h
  classical
  set φ : MvPolynomial (Fin 1) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+*
      globalFunctions B S hS W.obj := MvPolynomial.eval₂Hom ψ (fun _ => h) with hφdef
  set ρ : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+*
      MvPolynomial (Fin 1) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ RingHom.ker φ :=
    (Ideal.Quotient.mk (RingHom.ker φ)).comp MvPolynomial.C with hρdef
  have hκρ : (RingHom.kerLift φ).comp ρ = ψ := by
    refine RingHom.ext fun r => ?_
    rw [RingHom.comp_apply, hρdef, RingHom.comp_apply, RingHom.kerLift_mk, hφdef]
    exact MvPolynomial.eval₂Hom_C ψ (fun _ => h) r
  have hCft : RingHom.FiniteType
      (MvPolynomial.C : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+*
        MvPolynomial (Fin 1) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) := by
    rw [show (MvPolynomial.C : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+*
        MvPolynomial (Fin 1) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) =
          algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
            (MvPolynomial (Fin 1) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) from
      (MvPolynomial.algebraMap_eq _ _).symm]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hρft : RingHom.FiniteType ρ :=
    RingHom.FiniteType.comp_surjective hCft Ideal.Quotient.mk_surjective
  have hint := isIntegral_of_universallyClosed_of_injective_of_finiteType B S hS hV p huc _ ρ
    hρft (RingHom.kerLift φ) (RingHom.kerLift_injective φ) (by rw [hκρ]; exact hψ)
  have hx := (hint (Ideal.Quotient.mk (RingHom.ker φ) (MvPolynomial.X 0))).map
    (RingHom.kerLift φ)
  rw [hκρ, RingHom.kerLift_mk, hφdef] at hx
  rwa [MvPolynomial.eval₂Hom_X'] at hx

end AlgebraicGeometry.Space

end
