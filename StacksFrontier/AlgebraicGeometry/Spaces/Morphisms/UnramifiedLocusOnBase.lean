module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.InducedProperty
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.EtaleLocalStructure.ClosedImmersionOpens
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.BaseChangeLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Local
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts

/-!
# The open loci on the base over which a base change is unramified

Consider a commutative triangle of algebraic spaces over a scheme `S`: a morphism `f : X ⟶ Y`
together with morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` such that `f ≫ q = p`. If `p` is locally
of finite type and closed, then there is an open subspace `W` of `Z` through which a morphism
`Z' ⟶ Z` factors exactly when the base change of `f` along it is unramified. This is
**Stacks 05X8**. If in addition the morphism `X ×_Y X ⟶ Z` given by the first projection
followed by `p` is closed, there is an open subspace of `Z` through which `Z' ⟶ Z` factors
exactly when that base change is unramified *and* universally injective, which is
**Stacks 05X9**.

## Main results

* `AlgebraicGeometry.unramifiedAt_iff_hasRepresentativeWithProperty'`: unramifiedness of a
  morphism of schemes at a point of its source is the germ condition of Stacks 04R6 induced by
  unramifiedness.
* `AlgebraicGeometry.Space.isUnramifiedAt_iff_of_isPullback` is part (2) of **Stacks 05W2**:
  the unramified locus of a morphism of algebraic spaces locally of finite type is formed
  compatibly with base change, read at a point.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_forall_factorsThrough_iff_isUnramified_baseChange`
  is **Stacks 05X8**.
* `AlgebraicGeometry.Space.isPullback_selfPullbackBaseChange`: forming the fibre product of a
  morphism over `Z` with itself commutes with base change along a morphism to `Z`.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isUnramified_universallyInjective_baseChange`
  is **Stacks 05X9**.

## Implementation notes

The open subspace `W` is the one cut out, through the correspondence of Stacks 03BZ, by the
complement of the image under `p` of the closed set of points at which `f` is not unramified.
That set of points is closed because the unramified locus of Stacks 05W2 is open, and its image
is closed because `p` is; the hypothesis that `p` be locally of finite type is what makes the
unramified locus compatible with base change.

Factoring through an open subspace is tested on points by Stacks 03IE, and unramifiedness of a
morphism of algebraic spaces is tested at points by Stacks 03ZK; the two tests meet because the
points of the fibre product `X ×_Z Z'` lying over a point of `Z'` are exactly the points of `X`
in the fibre of `p`, which is `AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback`
read on the whole of `X`. So both sides of Stacks 05X8 become a condition on the fibres of `p`
over the image of `Z'`, and what remains is pure set theory.

Part (2) of Stacks 05W2 is proved pointwise rather than as an equality of open subspaces, which
is the form the main theorem consumes. Unramifiedness of morphisms of schemes is étale local on
the source and target (Stacks 04R3), so unramifiedness at a point of an algebraic space is the
pointed-chart condition of Stacks 04NC for the germ property induced by unramifiedness, and the
compatible pointed charts of
`AlgebraicGeometry.Space.exists_etaleChartAtPoint_pair_of_isPullback` turn the statement into
the corresponding statement for a cartesian square of morphisms of schemes.

Unramifiedness of a morphism of schemes at a point, Stacks 02G4, is stated on affine opens; the
germ form is reached through the open unramified locus of Stacks 0475. The translation in the
direction that needs work is from unramifiedness of the restriction `W.ι ≫ f` to an open
subscheme to unramifiedness of `f` at a point of `W`: an affine open of `W` witnessing the
former has an affine open image in the source of `f`, and the two maps on sections differ by
the isomorphism an open immersion induces on sections over that image.

For Stacks 05X9 the open subspace is cut out, again through Stacks 03BZ, by the point set of the
open subspace of Stacks 05X8 intersected with the complement of the image under `X ×_Y X ⟶ Z`
of the complement of the image of the relative diagonal of the base change of `f` over that
open subspace. The relative diagonal is an open immersion by part (1) of Stacks 05W1, and the
comparison morphism `isPullback_selfPullbackBaseChange` exhibits the source of that diagonal
inside `X ×_Y X` as a base change of an open subspace, so the image of the diagonal is an open
subspace of `X ×_Y X` and the set subtracted is closed.

Both conditions on a morphism `g : Z' ⟶ Z` then become conditions on the fibres of `X ×_Y X`
over the image of `g`: that the base change of `f` be unramified is Stacks 05X8, and that it be
universally injective is, by Stacks 03IE, that the comparison morphism out of the self fibre
product of the base change factor through the image of the diagonal. One direction of the latter
reads off that both projections of `X ×_Y X` restrict on that image to the same morphism, which
makes the base change a monomorphism; the other uses that the relative diagonal is a section of
the first projection.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 03ZK](https://stacks.math.columbia.edu/tag/03ZK)
* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 05W2](https://stacks.math.columbia.edu/tag/05W2)
* [Stacks Project, Tag 05X8](https://stacks.math.columbia.edu/tag/05X8)
* [Stacks Project, Tag 05X9](https://stacks.math.columbia.edu/tag/05X9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Unramifiedness at a point of a scheme -/

/-- Unramifiedness of a morphism of schemes at a point of an open subscheme on which the
restricted morphism is unramified.

An affine open `A` of the open subscheme witnessing unramifiedness of the restriction at the
point has affine open image in the source, the image lies over the same affine open of the
target, and the map on sections over the image agrees with the one over `A` up to the
isomorphism the open immersion induces on sections. -/
private theorem unramifiedAt_of_unramified_ι_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (W : X.Opens)
    (hW : Unramified (W.ι ≫ f)) (x : X) (hxW : x ∈ W) : UnramifiedAt f x := by
  obtain ⟨A, hA, hxA, V, hV, e, -⟩ := hW.unramifiedAt ⟨x, hxW⟩
  have he : W.ι ''ᵁ A ≤ f ⁻¹ᵁ V := Set.image_subset_iff.mpr e
  have hiso : IsIso (W.ι.appLE (W.ι ''ᵁ A) A (W.ι.preimage_image_eq A).ge) :=
    inferInstanceAs (IsIso (W.ι.app _ ≫
      W.toScheme.presheaf.map (eqToHom (W.ι.preimage_image_eq A).symm).op))
  have key := HasRingHomProperty.appLE (@Unramified.{u}) (W.ι ≫ f) hW ⟨V, hV⟩ ⟨A, hA⟩ e
  rw [← Scheme.Hom.appLE_comp_appLE W.ι f V (W.ι ''ᵁ A) A he
      (W.ι.preimage_image_eq A).ge, CommRingCat.hom_comp,
    (HasRingHomProperty.isLocal_ringHomProperty
      (@Unramified.{u})).respectsIso.cancel_right_isIso] at key
  refine ⟨W.ι ''ᵁ A, hA.image_of_isOpenImmersion W.ι, ⟨⟨x, hxW⟩, hxA, rfl⟩, V, hV, he, ?_⟩
  let : Algebra Γ(Y, V) Γ(X, W.ι ''ᵁ A) := (f.appLE V (W.ι ''ᵁ A) he).hom.toAlgebra
  exact ⟨RingHom.formallyUnramified_algebraMap.mp key.1,
    RingHom.finiteType_algebraMap.mp key.2⟩

/-- A morphism of schemes is unramified at a point of its source exactly when it is unramified
on some open neighbourhood of that point.

The unramified locus is open by Stacks 0475, and a morphism all of whose points are points of
unramifiedness is unramified on the corresponding open subscheme. -/
@[sga "3 XI 1.3"]
private theorem unramifiedAt_iff_exists_opens {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    UnramifiedAt f x ↔ ∃ U : X.Opens, x ∈ U ∧ Unramified (U.ι ≫ f) := by
  refine ⟨fun hx => ⟨⟨{z | UnramifiedAt f z}, isOpen_setOf_unramifiedAt f⟩, hx,
    unramified_ι_comp_of_forall_unramifiedAt f _ fun _ hz => hz⟩, ?_⟩
  rintro ⟨U, hxU, hU⟩
  exact unramifiedAt_of_unramified_ι_comp f U hU x hxU

/-- **Unramifiedness at a point is the germ condition induced by unramifiedness.** A morphism of
schemes is unramified at a point of its source exactly when the germ it defines there has an
unramified representative, which is the property of Stacks 04R6 associated with unramifiedness.

Both directions restrict along an open neighbourhood: a neighbourhood witnessing unramifiedness
is the source of a representative, and conversely an unramified representative agrees with the
morphism on a common open neighbourhood of the point, on which the morphism is then
unramified.

`AlgebraicGeometry.unramifiedAt_iff_hasRepresentativeWithProperty` is the same biconditional
under the additional hypothesis that `f` is locally of finite type; no finiteness is needed
here. -/
@[sga "3 XI 1.3"]
theorem unramifiedAt_iff_hasRepresentativeWithProperty' {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    UnramifiedAt f x ↔
      MorphismOfGerms.HasRepresentativeWithProperty
        (@Unramified.{u} : MorphismProperty Scheme.{u}) (MorphismOfGerms.ofSchemeHom f x) := by
  rw [unramifiedAt_iff_exists_opens]
  constructor
  · rintro ⟨U, hxU, hU⟩
    exact ⟨{ source := U, mem_source := hxU, hom := U.ι ≫ f, map_point := rfl },
      MorphismOfGerms.mk_eq_mk_iff.mpr ⟨U, hxU, le_rfl, le_top, by simp⟩, hU⟩
  · rintro ⟨r, hr, hP⟩
    obtain ⟨W, hxW, hWr, hWtop, heq⟩ : r.AgreeNear
        ({ source := ⊤, mem_source := by simp, hom := X.topIso.hom ≫ f,
            map_point := rfl } : MorphismOfGerms.Representative ⟨X, x⟩ ⟨Y, f x⟩) :=
      MorphismOfGerms.mk_eq_mk_iff.mp hr
    refine ⟨W, hxW, ?_⟩
    have hrestrict : W.ι ≫ f = X.homOfLE hWr ≫ r.hom := by
      rw [heq, ← Category.assoc]
      exact (congrArg (fun k => k ≫ f) (by simp : X.homOfLE hWtop ≫ X.topIso.hom = W.ι)).symm
    have : IsZariskiLocalAtSource (@Unramified.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := _)
    rw [hrestrict]
    exact IsZariskiLocalAtSource.comp hP _

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The unramified locus under base change -/

/-- **Part (2) of Stacks 05W2, read at a point.** In a cartesian square of algebraic spaces over
`S` whose right vertical arrow `f` is locally of finite type, the base change `f'` is unramified
at a point `x'` of its source exactly when `f` is unramified at the image of `x'`; that is,
forming the unramified locus commutes with base change.

Read on the compatible pointed charts of
`AlgebraicGeometry.Space.exists_etaleChartAtPoint_pair_of_isPullback`, each side is
unramifiedness of a morphism of schemes at corresponding points of a cartesian square of
schemes whose right vertical arrow is locally of finite type.

The source assumes all four corners of the square algebraic; only the three producing the charts
and the source of the base change are needed, the latter merely to read unramifiedness at a
point of it off a single chart. -/
@[stacks 05W2 "part (2): base-change invariance of the unramified locus, pointwise"]
theorem isUnramifiedAt_iff_of_isPullback {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (x' : points B S hS X') :
    IsUnramifiedAt B S hS f (pointsMap B S hS X' g' x') ↔ IsUnramifiedAt B S hS f' x' := by
  obtain ⟨c, c', pU, q, hsq, hft, hpoint, -⟩ :=
    exists_etaleChartAtPoint_pair_of_isPullback B S hS sq hX hY' hY hf x'
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) := hft
  have hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget
      (MorphismOfGerms.HasRepresentativeWithProperty
        (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})) :=
    MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget _
      _root_.AlgebraicGeometry.unramified_isEtaleLocalOnSourceAndTarget
  rw [isUnramifiedAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hX hY f _,
    isUnramifiedAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hX' hY' f' x',
    holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS _ hQ f _ c,
    holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS _ hQ f' x' c',
    ← _root_.AlgebraicGeometry.unramifiedAt_iff_hasRepresentativeWithProperty',
    ← _root_.AlgebraicGeometry.unramifiedAt_iff_hasRepresentativeWithProperty', hpoint]
  exact _root_.AlgebraicGeometry.unramifiedAt_iff_of_isPullback hsq (c'.sourcePoint B S hS)

/-! ### The open locus on the base, Stacks 05X8 -/

section OnBase

attribute [local instance] pointTopology

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The base change of `f : X ⟶ Y` along a morphism `g : Z' ⟶ Z`, where `X` and `Y` are given
over `Z` by morphisms `p` and `q` with `f ≫ q = p`: a morphism `X ×_Z Z' ⟶ Y ×_Z Z'` between
the canonical fibre products. -/
noncomputable def baseChangeOverBase (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z' ⟶ Z) : pullback p g ⟶ pullback q g :=
  pullback.lift (pullback.fst p g ≫ f) (pullback.snd p g)
    (by rw [Category.assoc, hfq, pullback.condition])

/-- `AlgebraicGeometry.Space.baseChangeOverBase` really is a base change of `f`: the square
formed by it, by `f` and by the two projections to `X` and to `Y` is cartesian.

Stacked under the cartesian square defining `Y ×_Z Z'` it gives the cartesian square defining
`X ×_Z Z'`, because `f ≫ q = p`, so it is cartesian itself. -/
theorem isPullback_baseChangeOverBase (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z' ⟶ Z) :
    IsPullback (pullback.fst p g) (baseChangeOverBase B S hS f p q hfq g) f
      (pullback.fst q g) := by
  refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback q g)
  have hb : baseChangeOverBase B S hS f p q hfq g ≫ pullback.snd q g = pullback.snd p g :=
    pullback.lift_snd _ _ _
  rw [hb, hfq]
  exact IsPullback.of_hasPullback p g

/-- **Stacks 05X8.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose source and
target are given over a third algebraic space `Z` by morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` with
`f ≫ q = p`. If `p` is locally of finite type and closed, then there is an open subspace `W` of
`Z` through which a morphism `Z' ⟶ Z` from an algebraic space factors exactly when the base
change of `f` along it is unramified.

The open subspace is the one cut out, through the correspondence of Stacks 03BZ, by the
complement of the image under `p` of the set of points at which `f` is not unramified: that set
is closed because the unramified locus of part (1) of Stacks 05W2 is open, and its image is
closed because `p` is. Factoring through `W` is the containment of the image of the points of
`Z'` in that complement, by Stacks 03IE, while unramifiedness of the base change is
unramifiedness at each of its points, by Stacks 03ZK; part (2) of Stacks 05W2 identifies the
latter with unramifiedness of `f` at each point of `X` lying over a point of the image of `Z'`,
and the two conditions then agree by a complementation. -/
@[stacks 05X8]
theorem exists_isOpenSubspace_forall_factorsThrough_iff_isUnramified_baseChange
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hp : IsLocallyOfFiniteType B S hS p) (hpc : IsClosedMorphism B S hS p) :
    ∃ W : Subfunctor Z, IsOpenSubspace B S hS W ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z),
        (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
          IsUnramified B S hS (baseChangeOverBase B S hS f p q hfq g) := by
  have hf : IsLocallyOfFiniteType B S hS f :=
    isLocallyOfFiniteType_of_comp B S hS hX hY hZ f q (by rwa [hfq])
  have hclosed : IsClosed {x : points B S hS X | IsUnramifiedAt B S hS f x}ᶜ :=
    (isOpen_setOf_isUnramifiedAt B S hS f).isClosed_compl
  obtain ⟨W, hWopen, hWrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hZ
    (pointsMap B S hS X p '' {x : points B S hS X | IsUnramifiedAt B S hS f x}ᶜ)ᶜ
    (hpc _ hclosed).isOpen_compl
  refine ⟨W, hWopen, fun Z' hZ' g => ?_⟩
  have hPX : IsAlgebraicSpace B S hS (pullback p g) :=
    isAlgebraicSpace_pullback B S hS p g hX hZ' hZ
  have hPY : IsAlgebraicSpace B S hS (pullback q g) :=
    isAlgebraicSpace_pullback B S hS q g hY hZ' hZ
  have hfibre : Set.range (pointsMap B S hS (pullback p g) (pullback.fst p g)) =
      pointsMap B S hS X p ⁻¹' Set.range (pointsMap B S hS Z' g) := by
    rw [← Set.image_univ, ← Set.image_univ,
      preimage_image_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback p g).flip Set.univ,
      Set.preimage_univ]
  have htfae : IsUnramified B S hS (baseChangeOverBase B S hS f p q hfq g) ↔
      ∀ x' : points B S hS (pullback p g),
        IsUnramifiedAt B S hS (baseChangeOverBase B S hS f p q hfq g) x' :=
    (isUnramified_tfae B S hS hPX hPY (baseChangeOverBase B S hS f p q hfq g)).out 1 2
  have hat := fun x' => isUnramifiedAt_iff_of_isPullback B S hS
    (isPullback_baseChangeOverBase B S hS f p q hfq g) hPX hX hPY hY hf x'
  rw [factorsThrough_openSubspace_iff_points B S hS hZ hZ' W hWopen g, hWrange, htfae]
  constructor
  · intro hsub x'
    rw [← hat]
    by_contra hbad
    exact hsub ⟨_, rfl⟩ ⟨_, hbad, (pointsMap_apply_comm B S hS
      (IsPullback.of_hasPullback p g).flip.w x').symm⟩
  · rintro hall _ ⟨z', rfl⟩ ⟨x, hxbad, hx⟩
    obtain ⟨x', hx'⟩ : x ∈ Set.range (pointsMap B S hS (pullback p g) (pullback.fst p g)) := by
      rw [hfibre]
      exact ⟨z', hx.symm⟩
    exact hxbad (hx' ▸ (hat x').mpr (hall x'))

/-! ### Self fibre products under base change -/

section SelfPullback

variable (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
  {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z' ⟶ Z)

/-- The base change of `f` along `g` composed with the projection to `Y` is the projection to
`X` composed with `f`. -/
private theorem baseChangeOverBase_comp_fst :
    baseChangeOverBase B S hS f p q hfq g ≫ pullback.fst q g = pullback.fst p g ≫ f :=
  pullback.lift_fst _ _ _

/-- The base change of `f` along `g` is a morphism over `Z'`. -/
private theorem baseChangeOverBase_comp_snd :
    baseChangeOverBase B S hS f p q hfq g ≫ pullback.snd q g = pullback.snd p g :=
  pullback.lift_snd _ _ _

/-- The morphism `(X ×_Z Z') ×_{Y ×_Z Z'} (X ×_Z Z') ⟶ X ×_Y X` whose two components are the
two projections of the fibre product followed by the projection `X ×_Z Z' ⟶ X`. -/
noncomputable def selfPullbackBaseChange :
    pullback (baseChangeOverBase B S hS f p q hfq g)
        (baseChangeOverBase B S hS f p q hfq g) ⟶ pullback f f :=
  pullback.lift
    (pullback.fst (baseChangeOverBase B S hS f p q hfq g)
      (baseChangeOverBase B S hS f p q hfq g) ≫ pullback.fst p g)
    (pullback.snd (baseChangeOverBase B S hS f p q hfq g)
      (baseChangeOverBase B S hS f p q hfq g) ≫ pullback.fst p g)
    (by
      rw [Category.assoc, Category.assoc, ← baseChangeOverBase_comp_fst B S hS f p q hfq g,
        ← Category.assoc, ← Category.assoc, pullback.condition])

/-- The first component of `AlgebraicGeometry.Space.selfPullbackBaseChange`. -/
theorem selfPullbackBaseChange_comp_fst :
    selfPullbackBaseChange B S hS f p q hfq g ≫ pullback.fst f f =
      pullback.fst (baseChangeOverBase B S hS f p q hfq g)
        (baseChangeOverBase B S hS f p q hfq g) ≫ pullback.fst p g :=
  pullback.lift_fst _ _ _

/-- The second component of `AlgebraicGeometry.Space.selfPullbackBaseChange`. -/
theorem selfPullbackBaseChange_comp_snd :
    selfPullbackBaseChange B S hS f p q hfq g ≫ pullback.snd f f =
      pullback.snd (baseChangeOverBase B S hS f p q hfq g)
        (baseChangeOverBase B S hS f p q hfq g) ≫ pullback.fst p g :=
  pullback.lift_snd _ _ _

/-- **Forming the fibre product of a morphism over `Z` with itself commutes with base change.**
The self fibre product of the base change of `f` along `g : Z' ⟶ Z` is the base change along
`g` of `X ×_Y X`, viewed over `Z` through the first projection followed by `p`.

The square is assembled from the cartesian square exhibiting `X ×_Z Z'` as a base change of
`X` along `Y ×_Z Z' ⟶ Y` and the cartesian square defining `X ×_Z Z'`. -/
theorem isPullback_selfPullbackBaseChange :
    IsPullback (selfPullbackBaseChange B S hS f p q hfq g)
      (pullback.fst (baseChangeOverBase B S hS f p q hfq g)
        (baseChangeOverBase B S hS f p q hfq g) ≫ pullback.snd p g)
      (pullback.fst f f ≫ p) g := by
  have hbc : IsPullback (pullback.fst p g) (baseChangeOverBase B S hS f p q hfq g) f
      (pullback.fst q g) := isPullback_baseChangeOverBase B S hS f p q hfq g
  have hpaste : IsPullback
      (pullback.snd (baseChangeOverBase B S hS f p q hfq g)
        (baseChangeOverBase B S hS f p q hfq g) ≫ pullback.fst p g)
      (pullback.fst (baseChangeOverBase B S hS f p q hfq g)
        (baseChangeOverBase B S hS f p q hfq g)) f (pullback.fst p g ≫ f) := by
    have h := (IsPullback.of_hasPullback (baseChangeOverBase B S hS f p q hfq g)
      (baseChangeOverBase B S hS f p q hfq g)).flip.paste_horiz hbc
    rwa [← hbc.w] at h
  refine (IsPullback.of_right ?_ (selfPullbackBaseChange_comp_fst B S hS f p q hfq g)
    (IsPullback.of_hasPullback f f).flip).paste_vert (IsPullback.of_hasPullback p g)
  rw [selfPullbackBaseChange_comp_snd]
  exact hpaste

/-- The relative diagonal of the base change of `f` along `g`, followed by the comparison
morphism to `X ×_Y X` and the first projection, is the projection `X ×_Z Z' ⟶ X`. -/
private theorem diagonal_comp_selfPullbackBaseChange_comp_fst :
    (pullback.diagonal (baseChangeOverBase B S hS f p q hfq g) ≫
        selfPullbackBaseChange B S hS f p q hfq g) ≫ pullback.fst f f = pullback.fst p g := by
  rw [Category.assoc, selfPullbackBaseChange_comp_fst, ← Category.assoc,
    pullback.diagonal_fst, Category.id_comp]

/-- The relative diagonal of the base change of `f` along `g`, followed by the comparison
morphism to `X ×_Y X` and the second projection, is the projection `X ×_Z Z' ⟶ X`. -/
private theorem diagonal_comp_selfPullbackBaseChange_comp_snd :
    (pullback.diagonal (baseChangeOverBase B S hS f p q hfq g) ≫
        selfPullbackBaseChange B S hS f p q hfq g) ≫ pullback.snd f f = pullback.fst p g := by
  rw [Category.assoc, selfPullbackBaseChange_comp_snd, ← Category.assoc,
    pullback.diagonal_snd, Category.id_comp]

end SelfPullback

/-! ### The open locus on the base, Stacks 05X9 -/

/-- On points, the relative diagonal is a section of the first projection. -/
private theorem pointsMap_diagonal_comp_fst {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G)
    (x : points B S hS F) :
    pointsMap B S hS (pullback k k) (pullback.fst k k)
        (pointsMap B S hS F (pullback.diagonal k) x) = x := by
  rw [← pointsMap_comp_apply, pullback.diagonal_fst, pointsMap_id, id_eq]

/-- **Universal injectivity of a base change, read on the fibres of `X ×_Y X ⟶ Z`.** Let `W₀`
be an open subspace of `Z`, let `d` be a morphism from `X ×_Z W₀` to `X ×_Y X` which is an open
immersion and whose two components are the projection `X ×_Z W₀ ⟶ X`, and let `f'` be a base
change of `f` along a morphism `g : Z' ⟶ Z` factoring through `W₀`, presented with its
comparison morphism `e'` to `X ×_Y X`. Then `f'` is universally injective exactly when every
point of `X ×_Y X` lying over a point of the image of `g` lies in the image of `d`. -/
private theorem universallyInjective_iff_forall_points_mem_range
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (W₀ : Subfunctor Z) (hW₀ : IsOpenSubspace B S hS W₀)
    (d : pullback p W₀.ι ⟶ pullback f f) (hdOpen : IsOpenImmersion B S hS d)
    (hdfst : d ≫ pullback.fst f f = pullback.fst p W₀.ι)
    (hdsnd : d ≫ pullback.snd f f = pullback.fst p W₀.ι)
    {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ' : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z)
    (k : Z' ⟶ W₀.toFunctor) (hk : k ≫ W₀.ι = g)
    (f' : pullback p g ⟶ pullback q g)
    (hf'snd : f' ≫ pullback.snd q g = pullback.snd p g)
    (e' : pullback f' f' ⟶ pullback f f)
    (hsq' : IsPullback e' (pullback.fst f' f' ≫ pullback.snd p g) (pullback.fst f f ≫ p) g)
    (he'fst : e' ≫ pullback.fst f f = pullback.fst f' f' ≫ pullback.fst p g)
    (he'snd : e' ≫ pullback.snd f f = pullback.snd f' f' ≫ pullback.fst p g) :
    (∀ (z' : points B S hS Z') (x : points B S hS (pullback f f)),
        pointsMap B S hS (pullback f f) (pullback.fst f f ≫ p) x =
            pointsMap B S hS Z' g z' →
          x ∈ Set.range (pointsMap B S hS (Subfunctor.range d).toFunctor
            (Subfunctor.range d).ι)) ↔
      UniversallyInjective B S hS f' := by
  have hX₀ : IsAlgebraicSpace B S hS (pullback p W₀.ι) :=
    isAlgebraicSpace_pullback B S hS p W₀.ι hX hW₀.1 hZ
  have hP : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback B S hS f f hX hX hY
  have hPX : IsAlgebraicSpace B S hS (pullback p g) :=
    isAlgebraicSpace_pullback B S hS p g hX hZ' hZ
  have hPY : IsAlgebraicSpace B S hS (pullback q g) :=
    isAlgebraicSpace_pullback B S hS q g hY hZ' hZ
  have hP' : IsAlgebraicSpace B S hS (pullback f' f') :=
    isAlgebraicSpace_pullback B S hS f' f' hPX hPX hPY
  have hD : IsOpenSubspace B S hS (Subfunctor.range d) :=
    isOpenSubspace_range_of_isAlgebraicSpace B S hS hX₀ d hdOpen
  have : Mono d := mono_of_presheaf_isOpenImmersion hdOpen
  obtain ⟨j, hjfst⟩ : ∃ j : pullback p g ⟶ pullback p W₀.ι,
      j ≫ pullback.fst p W₀.ι = pullback.fst p g :=
    ⟨pullback.lift (pullback.fst p g) (pullback.snd p g ≫ k)
      (by rw [Category.assoc, hk, pullback.condition]), pullback.lift_fst _ _ _⟩
  have hdiagFactor : pullback.diagonal f' ≫ e' = j ≫ d := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hdfst, hjfst, he'fst, ← Category.assoc,
        pullback.diagonal_fst, Category.id_comp]
    · rw [Category.assoc, Category.assoc, hdsnd, hjfst, he'snd, ← Category.assoc,
        pullback.diagonal_snd, Category.id_comp]
  have hfp := factorsThrough_openSubspace_iff_points B S hS hP hP' (Subfunctor.range d) hD e'
  refine Iff.trans (b := ∃ l : pullback f' f' ⟶ (Subfunctor.range d).toFunctor,
    l ≫ (Subfunctor.range d).ι = e') ?_ ?_
  · rw [hfp]
    constructor
    · rintro hall x ⟨w, rfl⟩
      refine hall (pointsMap B S hS (pullback f' f')
        (pullback.fst f' f' ≫ pullback.snd p g) w) _ ?_
      have h := congrFun (congrArg (pointsMap B S hS (pullback f' f') ·) hsq'.w) w
      simpa only [pointsMap_comp, Function.comp_apply] using h
    · rintro hsub z' x hx
      obtain ⟨w, hwe, -⟩ := exists_point_of_isPullback_presheaf B S hS hsq' x z' hx
      exact hwe ▸ hsub ⟨w, rfl⟩
  constructor
  · rintro ⟨l, hl⟩
    have hinv : inv (Subfunctor.toRange d) ≫ d = (Subfunctor.range d).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι d).symm
    have ht : (l ≫ inv (Subfunctor.toRange d)) ≫ d = e' := by
      rw [Category.assoc, hinv]
      exact hl
    have hdiag : pullback.fst f' f' = pullback.snd f' f' := by
      refine pullback.hom_ext ?_ ?_
      · rw [← he'fst, ← he'snd, ← ht]
        simp only [Category.assoc, hdfst, hdsnd]
      · rw [← hf'snd]
        simp only [← Category.assoc, pullback.condition]
    have _ : Mono f' := ⟨fun {T} a b hab ↦ by
      calc a = pullback.lift a b hab ≫ pullback.fst f' f' := (pullback.lift_fst a b hab).symm
        _ = pullback.lift a b hab ≫ pullback.snd f' f' := by rw [hdiag]
        _ = b := pullback.lift_snd a b hab⟩
    intro T _ u
    exact pointsMap_injective_of_mono B S hS (pullback.fst u f')
  · intro hui
    rw [hfp]
    rintro x ⟨w, rfl⟩
    have hw : pointsMap B S hS (pullback p g) (pullback.diagonal f')
        (pointsMap B S hS (pullback f' f') (pullback.fst f' f') w) = w :=
      hui (pullback p g) hPX f' (pointsMap_diagonal_comp_fst B S hS f'
        (pointsMap B S hS (pullback f' f') (pullback.fst f' f') w))
    refine ⟨pointsMap B S hS (pullback p g) (j ≫ Subfunctor.toRange d)
      (pointsMap B S hS (pullback f' f') (pullback.fst f' f') w), ?_⟩
    rw [← pointsMap_comp_apply, Category.assoc, Subfunctor.toRange_ι, ← hdiagFactor,
      pointsMap_comp_apply, hw]

/-- **Stacks 05X9.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose source and
target are given over a third algebraic space `Z` by morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` with
`f ≫ q = p`. If `p` is locally of finite type and closed and the morphism `X ×_Y X ⟶ Z` given by
the first projection followed by `p` is closed, then there is an open subspace `W` of `Z`
through which a morphism `Z' ⟶ Z` from an algebraic space factors exactly when the base change
of `f` along it is unramified and universally injective.

The open subspace is cut out, through the correspondence of Stacks 03BZ, by the point set of the
open subspace of Stacks 05X8 intersected with the complement of the image under `X ×_Y X ⟶ Z` of
the complement of the image of the relative diagonal of the base change of `f` over that open
subspace; that image is an open subspace of `X ×_Y X` because the relative diagonal of an
unramified morphism is an open immersion by part (1) of Stacks 05W1 and because `X ×_Z W₀` sits
inside `X ×_Y X` as a base change of `W₀`. Factoring through the intersection is, by Stacks 03IE,
the conjunction of factoring through the open subspace of Stacks 05X8 and of every point of
`X ×_Y X` over the image of `Z'` lying in the image of the diagonal, and the second condition is
universal injectivity of the base change. -/
@[stacks 05X9]
theorem exists_isOpenSubspace_iff_isUnramified_universallyInjective_baseChange
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hp : IsLocallyOfFiniteType B S hS p) (hpc : IsClosedMorphism B S hS p)
    (hp₂ : IsClosedMorphism B S hS (pullback.fst f f ≫ p)) :
    ∃ W : Subfunctor Z, IsOpenSubspace B S hS W ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z),
        (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
          IsUnramified B S hS (baseChangeOverBase B S hS f p q hfq g) ∧
            UniversallyInjective B S hS (baseChangeOverBase B S hS f p q hfq g) := by
  obtain ⟨W₀, hW₀, hW₀unram⟩ :=
    exists_isOpenSubspace_forall_factorsThrough_iff_isUnramified_baseChange B S hS hX hY hZ
      f p q hfq hp hpc
  have hX₀ : IsAlgebraicSpace B S hS (pullback p W₀.ι) :=
    isAlgebraicSpace_pullback B S hS p W₀.ι hX hW₀.1 hZ
  have hY₀ : IsAlgebraicSpace B S hS (pullback q W₀.ι) :=
    isAlgebraicSpace_pullback B S hS q W₀.ι hY hW₀.1 hZ
  obtain ⟨d, hdOpen, hdfst, hdsnd⟩ : ∃ d : pullback p W₀.ι ⟶ pullback f f,
      IsOpenImmersion B S hS d ∧ d ≫ pullback.fst f f = pullback.fst p W₀.ι ∧
        d ≫ pullback.snd f f = pullback.fst p W₀.ι := by
    refine ⟨pullback.diagonal (baseChangeOverBase B S hS f p q hfq W₀.ι) ≫
      selfPullbackBaseChange B S hS f p q hfq W₀.ι, ?_,
      diagonal_comp_selfPullbackBaseChange_comp_fst B S hS f p q hfq W₀.ι,
      diagonal_comp_selfPullbackBaseChange_comp_snd B S hS f p q hfq W₀.ι⟩
    have hQbc := MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
    have hQcomp := MorphismProperty.relative_isStableUnderComposition
      (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
    exact MorphismProperty.comp_mem _ _ _
      (isOpenImmersion_diagonal_of_isUnramified B S hS hX₀ hY₀ _
        ((hW₀unram W₀.toFunctor hW₀.1 W₀.ι).mp ⟨𝟙 _, Category.id_comp _⟩))
      (hQbc.of_isPullback (isPullback_selfPullbackBaseChange B S hS f p q hfq W₀.ι).flip hW₀.2)
  have hD : IsOpenSubspace B S hS (Subfunctor.range d) :=
    isOpenSubspace_range_of_isAlgebraicSpace B S hS hX₀ d hdOpen
  obtain ⟨W, hWopen, hWrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hZ
    (Set.range (pointsMap B S hS W₀.toFunctor W₀.ι) ∩
      (pointsMap B S hS (pullback f f) (pullback.fst f f ≫ p) ''
        (Set.range (pointsMap B S hS (Subfunctor.range d).toFunctor
          (Subfunctor.range d).ι))ᶜ)ᶜ)
    ((isOpen_range_pointsMap_of_isOpenImmersion B S hS W₀.ι hW₀.2).inter
      (hp₂ _ (isOpen_range_pointsMap_of_isOpenImmersion B S hS (Subfunctor.range d).ι
        hD.2).isClosed_compl).isOpen_compl)
  refine ⟨W, hWopen, fun Z' hZ' g ↦ ?_⟩
  rw [factorsThrough_openSubspace_iff_points B S hS hZ hZ' W hWopen g, hWrange]
  have hW₀pts := factorsThrough_openSubspace_iff_points B S hS hZ hZ' W₀ hW₀ g
  have key := fun (k : Z' ⟶ W₀.toFunctor) (hk : k ≫ W₀.ι = g) ↦
    universallyInjective_iff_forall_points_mem_range B S hS hX hY hZ f p q W₀ hW₀ d hdOpen
      hdfst hdsnd hZ' g k hk (baseChangeOverBase B S hS f p q hfq g)
      (baseChangeOverBase_comp_snd B S hS f p q hfq g)
      (selfPullbackBaseChange B S hS f p q hfq g)
      (isPullback_selfPullbackBaseChange B S hS f p q hfq g)
      (selfPullbackBaseChange_comp_fst B S hS f p q hfq g)
      (selfPullbackBaseChange_comp_snd B S hS f p q hfq g)
  constructor
  · intro hsub
    obtain ⟨k, hk⟩ := hW₀pts.mpr fun _ hx ↦ (hsub hx).1
    refine ⟨(hW₀unram Z' hZ' g).mp ⟨k, hk⟩, (key k hk).mp fun z' x hx ↦ ?_⟩
    by_contra hbad
    exact (hsub ⟨z', rfl⟩).2 ⟨x, hbad, hx⟩
  · rintro ⟨hunram, hui⟩
    obtain ⟨k, hk⟩ := (hW₀unram Z' hZ' g).mpr hunram
    have havoid := (key k hk).mpr hui
    rintro z ⟨z', rfl⟩
    refine ⟨hW₀pts.mp ⟨k, hk⟩ ⟨z', rfl⟩, ?_⟩
    rintro ⟨x, hxbad, hx⟩
    exact hxbad (havoid z' x hx)

end OnBase

end Space

end AlgebraicGeometry

end
