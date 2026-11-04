module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantPointsHelpers
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralPushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveSmallEtale

/-!
# The essential image of the small étale direct image along an integral universally injective
morphism

Let `f : Y ⟶ X` be an integral and universally injective morphism of algebraic spaces over a
scheme `S`. This file proves that an abelian sheaf on the small étale site of `X` is a direct
image along `f` exactly when its support is contained in the image of the point set of `Y`.
That is the essential-image clause of Stacks 0AEH, part (2); the full-faithfulness clause and
the left-inverse clause of the same tag are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/IntegralUniversallyInjectiveSmallEtale.lean`.

## Main results

* `AlgebraicGeometry.exists_section_of_isIntegralHom_spec`: an integral morphism of schemes to
  the spectrum of an algebraically closed field whose source is nonempty has a section. The
  source is affine with integral ring of sections over the field, so a maximal ideal of that
  ring cuts out a retraction onto the field.
* `AlgebraicGeometry.Space.nonempty_pullback_of_mem_range_pointsMap`: for a relatively
  representable morphism, the scheme representing the base change along a geometric point of the
  target whose image lies in the point set of the source is nonempty. This is Stacks 03BU: the
  two field-valued points have a common extension, and that extension maps into the base change
  by its universal property.
* `AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_section` and
  `AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_scheme_section`: a section of the
  projection from the represented base change of `f` along a geometric point of `X` to the field
  spectrum of that point lifts the point to a geometric point of `Y`, over the same field. The
  geometry of the morphism enters only through the existence of that section.
* `AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_mem_range_of_isIntegralHom`: **a
  geometric point of `X` lying on the image of an integral morphism `f : Y ⟶ X` is the image of
  a geometric point of `Y`, over the same algebraically closed field.** The base change of `f`
  along the point is integral over the field spectrum and nonempty, hence has a section.
* `AlgebraicGeometry.Space.isZero_stalkFunctor_abelianPushforward_of_notMem_of_isIntegralHom`:
  the abelian stalk of a direct image along an integral morphism vanishes off the image of the
  point set, which is Étale Cohomology 04FX in its stalkwise form.
* `AlgebraicGeometry.Space.isIso_unit_app_of_supportOfSheaf_subset_of_isIntegralHom`: the unit
  `F ⟶ f_*f^{-1}F` is invertible at every abelian sheaf supported on the image of the point set
  of `Y`. This is Étale Cohomology 04FZ, part (2) for algebraic spaces.
* `AlgebraicGeometry.Space.smallEtalePushforwardAb_essImage_iff_of_integral_universallyInjective`:
  **Stacks 0AEH, part (2), the essential image**, in both directions.

## Implementation notes

The argument is the one by which
`AlgebraicGeometry.Space.smallEtalePushforward_essImage_iff_abelian_of_isClosedImmersion`
settles the same clause of Stacks 04E5 for a closed immersion, and it is run stalkwise rather
than by reduction to charts. Only one step of that argument uses anything about the morphism
beyond representability and closedness of the image, namely the lifting of a geometric point of
`X` lying over the image to a geometric point of `Y`; for a closed immersion the base change of
the immersion along the point is a nonempty closed subscheme of the spectrum of a field and so
the whole of it, while for an integral morphism the base change is only *affine and integral*
over that spectrum. What rescues the step is that a geometric point is the spectrum of an
**algebraically** closed field, so the residue field at a maximal ideal of a nonzero integral
algebra over it is the field itself: the base change has a section even though it is not an
isomorphism. Universal injectivity is not used here, and is not needed: it enters only through
the full faithfulness that turns invertibility of the unit into membership of the essential
image.

The hypothesis that the field is algebraically closed is what the step needs, and separable
closure would not do: for a separably closed field `k` of characteristic `p` which is not
perfect and `t ∈ k` without a `p`-th root, `Spec k[x]/(x^p - t) ⟶ Spec k` is integral and
universally injective, the identity geometric point of the target lies on its image, and it has
no lift. The development's `AlgebraicGeometry.Space.GeometricPoint` is `IsAlgClosed`, so the
step is available; an argument conducted at separably closed points would have to pass through
the topological invariance of the étale site instead.

The support bound in the other direction holds for every integral morphism and is
`AlgebraicGeometry.Space.supportOfSheaf_subset_of_essImage_of_isIntegralHom`; the coefficient
universe is `u + 1` throughout, because the inverse image occurs and the small étale site
carries sheafification for abelian groups there as an instance.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
* [Stacks Project, Tag 04FZ](https://stacks.math.columbia.edu/tag/04FZ)
* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **An integral morphism to the spectrum of an algebraically closed field with nonempty source
has a section.** Such a morphism is affine, so its source is the spectrum of a ring integral over
the field; that ring is nonzero, and the residue field at any of its maximal ideals is an
algebraic extension of an algebraically closed field, hence the field itself. The resulting
retraction of rings is the section. -/
theorem exists_section_of_isIntegralHom_spec (k : Type u) [Field k] [IsAlgClosed k]
    {W : Scheme.{u}} (p : W ⟶ Spec (.of k)) [IsIntegralHom p] [Nonempty W] :
    ∃ s : Spec (.of k) ⟶ W, s ≫ p = 𝟙 _ := by
  have _ : IsAffine W := isAffine_of_isAffineHom p
  have hint : (Scheme.Hom.appTop p).hom.IsIntegral :=
    IsIntegralHom.isIntegral_app p ⊤ (isAffineOpen_top _)
  have hne : Nonempty (PrimeSpectrum Γ(W, ⊤)) :=
    ⟨W.isoSpec.hom.base (Classical.arbitrary W)⟩
  have hnt : Nontrivial Γ(W, ⊤) := by
    rcases subsingleton_or_nontrivial Γ(W, ⊤) with h | h
    · exact absurd hne (not_nonempty_iff.2 (PrimeSpectrum.isEmpty_iff_subsingleton.2 h))
    · exact h
  set φ : CommRingCat.of k ⟶ Γ(W, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop p with hφ
  have hφint : φ.hom.IsIntegral :=
    (RingHom.isIntegral_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv (Scheme.Hom.appTop p)).2 hint
  obtain ⟨ψ, hψ⟩ := exists_ringHom_comp_eq_of_isIntegral φ.hom hφint
    (RingHom.injective (φ.hom : k →+* Γ(W, ⊤))) (RingHom.id k)
  have hret : φ ≫ CommRingCat.ofHom ψ = 𝟙 (CommRingCat.of k) := by
    apply CommRingCat.hom_ext
    simpa using hψ
  have happ : Scheme.Hom.appTop p ≫ CommRingCat.ofHom ψ =
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom := by
    rw [hφ, Category.assoc, Iso.inv_comp_eq] at hret
    simpa using hret
  have hkey : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (Scheme.Hom.appTop p) =
      (Spec (CommRingCat.of k)).toSpecΓ :=
    (Spec.map_comp (Scheme.Hom.appTop p) (CommRingCat.ofHom ψ)).symm.trans
      ((congrArg Spec.map happ).trans (SpecMap_ΓSpecIso_hom _))
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ W.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality p, ← Category.assoc, hkey,
    Scheme.toSpecΓ_isoSpec_inv]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-- **The represented base change of a morphism along a geometric point lying on its image is
nonempty.** For a relatively representable morphism `f : Y ⟶ X` of algebraic spaces over `S` and
a geometric point `x` of `X` whose image lies in the point set of `f`, the scheme representing
the base change of `f` along `x` has a point.

By Stacks 03BU the field-valued point of `X` underlying `x` and the field-valued point of `X`
obtained by pushing forward a representative of the point of `|Y|` above it admit a single
common field-valued extension; that extension maps to `Y` over `X` and to the field spectrum of
`x`, hence into the base change by its universal property, and its own spectrum is nonempty. -/
theorem nonempty_pullback_of_mem_range_pointsMap (f : Y ⟶ X)
    (hr : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1)
    (g : yoneda.obj x.val.siteObject ⟶ X.1) (hgval : yonedaEquiv g = x.val.value)
    (hx : x.image ∈ Set.range (pointsMap B S hS Y.1 f.hom)) :
    Nonempty ((BigFppfOver.toScheme B S hS).obj (hr.pullback g)) := by
  obtain ⟨p₀, hp₀⟩ := hx
  obtain ⟨p, rfl⟩ := Quot.exists_rep p₀
  obtain ⟨r, ⟨a, ha⟩, ⟨h, hh⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS X.1
      (FieldValuedPoint.map B S hS Y.1 f.hom p) x.val).1 hp₀
  have hsq : (yoneda.map a ≫ (yonedaEquiv.symm p.value :
        yoneda.obj (FieldValuedPoint.siteObject B S hS X.1
          (FieldValuedPoint.map B S hS Y.1 f.hom p)) ⟶ Y.1)) ≫ f.hom
      = yoneda.map h ≫ g := by
    have hps : yonedaEquiv (yonedaEquiv.symm p.value :
        yoneda.obj (FieldValuedPoint.siteObject B S hS X.1
          (FieldValuedPoint.map B S hS Y.1 f.hom p)) ⟶ Y.1) = p.value :=
      yonedaEquiv.apply_symm_apply _
    refine yonedaEquiv.injective ?_
    rwa [Category.assoc, ← yonedaEquiv_naturality, ← yonedaEquiv_naturality, yonedaEquiv_comp,
      hps, hgval, hh]
  have hsrc : Nonempty ((BigFppfOver.toScheme B S hS).obj r.siteObject) :=
    ⟨(default : Spec (CommRingCat.of r.carrier))⟩
  exact ⟨(BigFppfOver.toScheme B S hS).map
    (yoneda.preimage ((hr.isPullback g).lift _ (yoneda.map h) hsq)) hsrc.some⟩

/-- **A section of the represented base change along a geometric point lifts the point.** For a
relatively representable morphism `f : Y ⟶ X` of algebraic spaces over `S` and a geometric point
`x` of `X`, a section of the projection to the field spectrum of `x` from the object representing
the base change of `f` along `x` determines a geometric point of `Y`, over the same field, whose
image is `x`.

This is the whole of the geometric-point lifting step, with the geometry isolated into the
existence of the section: a closed immersion gets its section from the base change's being an
isomorphism, an integral morphism from a retraction of a nonzero integral algebra over an
algebraically closed field, and an open immersion from a nonempty open subscheme of the spectrum
of a field being the whole of it. -/
theorem exists_geometricPoint_map_eq_of_section (f : Y ⟶ X)
    (hr : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1)
    (g : yoneda.obj x.val.siteObject ⟶ X.1) (hgval : yonedaEquiv g = x.val.value)
    (sec : x.val.siteObject ⟶ hr.pullback g) (hsec : sec ≫ hr.snd g = 𝟙 _) :
    ∃ y : GeometricPoint B S hS Y.1, geometricPointMap f.hom y = x := by
  have hzhom : (yoneda.map sec ≫ hr.fst g) ≫ f.hom = g := by
    rw [Category.assoc, hr.w g, ← Category.assoc, ← yoneda.map_comp, hsec, yoneda.map_id,
      Category.id_comp]
  refine ⟨⟨{ carrier := x.val.carrier, contained := x.val.contained, toBase := x.val.toBase
             value := yonedaEquiv (yoneda.map sec ≫ hr.fst g) }, x.property⟩, ?_⟩
  refine Subtype.ext ?_
  change FieldValuedPoint.map B S hS Y.1 f.hom _ = x.val
  have hval : f.hom.app (Opposite.op x.val.siteObject)
      (yonedaEquiv (yoneda.map sec ≫ hr.fst g)) = x.val.value := by
    rw [← yonedaEquiv_comp, hzhom, hgval]
  rw [FieldValuedPoint.map]
  congr 1

/-- **A section of the underlying scheme morphism of the represented base change lifts a
geometric point.** The inclusion of the big fppf site into schemes is full, so a section of the
projection as a morphism of schemes comes from a morphism of the site, and that morphism is a
section there too. -/
theorem exists_geometricPoint_map_eq_of_scheme_section (f : Y ⟶ X)
    (hr : yoneda.relativelyRepresentable f.hom) (x : GeometricPoint B S hS X.1)
    (g : yoneda.obj x.val.siteObject ⟶ X.1) (hgval : yonedaEquiv g = x.val.value)
    (sec : (BigFppfOver.toScheme B S hS).obj (x.val.siteObject) ⟶
      (BigFppfOver.toScheme B S hS).obj (hr.pullback g))
    (hsec : sec ≫ (BigFppfOver.toScheme B S hS).map (hr.snd g) = 𝟙 _) :
    ∃ y : GeometricPoint B S hS Y.1, geometricPointMap f.hom y = x := by
  let secInclusion : B.inclusion.obj (x.val.siteObject).left ⟶
      B.inclusion.obj (hr.pullback g).left := sec
  change secInclusion ≫ B.inclusion.map (hr.snd g).left = 𝟙 _ at hsec
  have hleft : B.inclusion.preimage secInclusion ≫ (hr.snd g).left = 𝟙 _ := by
    apply B.inclusion.map_injective
    simpa only [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_id] using hsec
  refine exists_geometricPoint_map_eq_of_section B S hS f hr x g hgval
    (Over.homMk (B.inclusion.preimage secInclusion) (by
      rw [← Over.w (hr.snd g), ← Category.assoc, hleft, Category.id_comp])) ?_
  apply Over.OverMorphism.ext
  simpa using hleft

/-- **A geometric point of `X` lying on the image of an integral morphism comes from a geometric
point of the source.** If the image of a geometric point `x` of `X` lies in the point set of an
integral morphism `f : Y ⟶ X` of algebraic spaces over `S`, then `x` is the image of a geometric
point of `Y` over the same algebraically closed field.

The base change of `f` along `x` is represented by a scheme integral over the spectrum of the
field of `x`, nonempty by
`AlgebraicGeometry.Space.nonempty_pullback_of_mem_range_pointsMap`, so it has a section by
`AlgebraicGeometry.exists_section_of_isIntegralHom_spec`.

Universal injectivity is not assumed: the base change need not be an isomorphism, only to have
a section, and that is what integrality over an algebraically closed field supplies. -/
theorem exists_geometricPoint_map_eq_of_mem_range_of_isIntegralHom (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (x : GeometricPoint B S hS X.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS Y.1 f.hom)) :
    ∃ y : GeometricPoint B S hS Y.1, geometricPointMap f.hom y = x := by
  let hr := relativelyRepresentable_of_isIntegralHom B S hS f hf
  let g : yoneda.obj x.val.siteObject ⟶ X.1 := yonedaEquiv.symm x.val.value
  have hgval : yonedaEquiv g = x.val.value := yonedaEquiv.apply_symm_apply _
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj (hr.pullback g)) :=
    nonempty_pullback_of_mem_range_pointsMap B S hS f hr x g hgval hx
  have hint : _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map (hr.snd g)) :=
    ((isIntegralHom_iff_representable B S hS f.hom Y.property X.property).mp hf).2.property
      g (hr.fst g) (hr.snd g) (hr.isPullback g)
  have _ : IsAlgClosed x.val.carrier := x.property
  obtain ⟨sec, hsec⟩ := exists_section_of_isIntegralHom_spec x.val.carrier
    ((BigFppfOver.toScheme B S hS).map (hr.snd g))
  exact exists_geometricPoint_map_eq_of_scheme_section B S hS f hr x g hgval sec hsec

/-- The abelian stalk of a sheaf vanishes at a geometric point whose image lies outside a set
containing the support of the sheaf. -/
private theorem isZero_stalkFunctor_of_supportOfSheaf_subset
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
    {T : Set (points B S hS X.1)} (hsupp : supportOfSheaf B S hS X.1 F ⊆ T)
    (x : GeometricPoint B S hS X.1) (hx : x.image ∉ T) :
    IsZero ((stalkFunctor AddCommGrpCat.{u + 1} x).obj F.obj) := by
  rw [isZero_stalkFunctor_iff_subsingleton_stalkSet B S hS X.property]
  by_contra hns
  exact hx (hsupp ⟨x, rfl, hns⟩)

/-- The abelian stalk of a small étale direct image along an integral morphism vanishes at
every geometric point whose image misses the point set of the source. -/
theorem isZero_stalkFunctor_abelianPushforward_of_notMem_of_isIntegralHom (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
    (x : GeometricPoint B S hS X.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Y.1 f.hom)) :
    IsZero ((stalkFunctor AddCommGrpCat.{u + 1} x).obj
      ((smallEtaleAbelianPushforward.{u + 1} B S hS f
        (relativelyRepresentable_of_isIntegralHom B S hS f hf)).obj G).obj) := by
  exact isZero_stalkFunctor_of_supportOfSheaf_subset B S hS _
    (supportOfSheaf_smallEtaleAbelianPushforward_subset_of_isClosed_range B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)
      (isClosed_range_pointsMap_of_isIntegralHom B S hS f hf) G) x hx

/-- **Étale Cohomology 04FZ, part (2), for algebraic spaces.** For an integral and universally
injective morphism `f : Y ⟶ X` of algebraic spaces over `S`, the unit of the
inverse-image/direct-image adjunction on abelian sheaves is invertible at every abelian sheaf on
`X_étale` supported on the image of the point set of `Y`.

The abelian geometric stalks are conservative, so it suffices to check invertibility stalkwise.
At a geometric point of `X` lying over the image the point comes from a geometric point of `Y`
by `AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_mem_range_of_isIntegralHom`; there
the inverse image already carries the unit to an isomorphism, by the triangle identity and the
left-inverse clause of Stacks 0AEH, and the stalk of an inverse image is the stalk at the image
point by part (4) of Stacks 04K2. At a geometric point whose image misses the point set of `Y`
the stalk of the sheaf vanishes by hypothesis and the stalk of the direct image vanishes by
Étale Cohomology 04FX, so any map between them is invertible. -/
theorem isIso_unit_app_of_supportOfSheaf_subset_of_isIntegralHom (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
    (hsupp : supportOfSheaf B S hS X.1 F ⊆ Set.range (pointsMap B S hS Y.1 f.hom)) :
    IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).unit.app F) := by
  have hff := fullyFaithfulSmallEtaleAbelianPushforwardOfIntegralUniversallyInjective.{u + 1}
    B S hS f hf hui
  have := hff.full
  have := hff.faithful
  set hr := relativelyRepresentable_of_isIntegralHom B S hS f hf
  set pb := smallEtaleAbelianInverseImage B S hS f hr
  set adj := smallEtaleAbelianInverseImageAdjunction B S hS f hr with hadj
  refine isIso_of_isIso_stalkFunctor_map B S hS X.property (adj.unit.app F) fun x ↦ ?_
  by_cases hx : x.image ∈ Set.range (pointsMap B S hS Y.1 f.hom)
  · obtain ⟨y, rfl⟩ :=
      exists_geometricPoint_map_eq_of_mem_range_of_isIntegralHom B S hS f hf x hx
    have hcounit : IsIso (adj.counit.app (pb.obj F)) := by
      rw [hadj]
      infer_instance
    have htri : pb.map (adj.unit.app F) ≫ adj.counit.app (pb.obj F) = 𝟙 _ :=
      adj.left_triangle_components F
    have hcomp : IsIso (pb.map (adj.unit.app F) ≫ adj.counit.app (pb.obj F)) := by
      rw [htri]
      infer_instance
    have hpull : IsIso (pb.map (adj.unit.app F)) :=
      IsIso.of_isIso_comp_right _ (adj.counit.app (pb.obj F))
    have hwhisk : IsIso ((pb ⋙ sheafToPresheaf (SmallEtale.topology B S hS Y.1)
        AddCommGrpCat.{u + 1} ⋙ stalkFunctor AddCommGrpCat.{u + 1} y).map
          (adj.unit.app F)) :=
      inferInstanceAs (IsIso ((stalkFunctor AddCommGrpCat.{u + 1} y).map
        (pb.map (adj.unit.app F)).hom))
    exact isIso_map_of_natIso (smallEtaleAbelianInverseImageStalkIso B S hS f hr y)
      (adj.unit.app F)
  · have hsrc := isZero_stalkFunctor_of_supportOfSheaf_subset B S hS F hsupp x hx
    have htgt : IsZero ((stalkFunctor AddCommGrpCat.{u + 1} x).obj
        ((smallEtaleAbelianPushforward.{u + 1} B S hS f hr).obj (pb.obj F)).obj) :=
      isZero_stalkFunctor_abelianPushforward_of_notMem_of_isIntegralHom
        B S hS f hf (pb.obj F) x hx
    have hmap : (stalkFunctor AddCommGrpCat.{u + 1} x).map (adj.unit.app F).hom =
        (hsrc.iso htgt).hom := hsrc.eq_of_src _ _
    rw [hmap]
    infer_instance

/-- **Stacks 0AEH, part (2), the essential image.** For an integral and universally injective
morphism `f : Y ⟶ X` of algebraic spaces over a scheme `S`, an abelian sheaf on the small étale
site of `X` lies in the essential image of the direct image along `f` exactly when its support
is contained in the image of the point set of `Y`.

The forward inclusion is
`AlgebraicGeometry.Space.supportOfSheaf_subset_of_essImage_of_isIntegralHom`, resting on Étale
Cohomology 04FX for algebraic spaces, and the converse is
`AlgebraicGeometry.Space.isIso_unit_app_of_supportOfSheaf_subset_of_isIntegralHom` together with
the characterization of the essential image of a fully faithful right adjoint by invertibility
of the unit. -/
@[stacks 0AEH "part (2): the essential image, for an integral and universally injective \
morphism of algebraic spaces"]
theorem smallEtalePushforwardAb_essImage_iff_of_integral_universallyInjective (f : Y ⟶ X)
    (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) :
    (smallEtaleAbelianPushforward.{u + 1} B S hS f
        (relativelyRepresentable_of_isIntegralHom B S hS f hf)).essImage F ↔
      supportOfSheaf B S hS X.1 F ⊆ Set.range (pointsMap B S hS Y.1 f.hom) := by
  refine ⟨supportOfSheaf_subset_of_essImage_of_isIntegralHom B S hS f hf F, fun h ↦ ?_⟩
  have := isIso_unit_app_of_supportOfSheaf_subset_of_isIntegralHom B S hS f hf hui F h
  exact (smallEtaleAbelianInverseImageAdjunction B S hS f
    (relativelyRepresentable_of_isIntegralHom B S hS f hf)).mem_essImage_of_unit_isIso F

end Space

end AlgebraicGeometry

end
