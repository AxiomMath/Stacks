module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineOverBaseDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStageSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.LocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfCompletedLocalRing
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrictRepresentable

/-!
# A space which is a scheme over every local ring of the base

Let `X` be an algebraic space over a scheme `S` whose structure morphism is quasi-compact and
quasi-separated. Suppose that for every point `x` of `X`, with image `s` in `S`, the base
change `X ×_S Spec(𝒪_{S, s})` is a scheme. Then `X` is a scheme: this is Stacks 0B80.

The source proof is two steps. The base change to the local ring is the limit of the base
changes to the affine open neighbourhoods of `s`, which is
`AlgebraicGeometry.Space.isLimitBaseChangeAffineNhdsCone` in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/LocalRingBaseChange.lean`; so Stacks 07SR,
that a stage of a limit situation is a scheme as soon as the limit is, produces an affine open
neighbourhood `U` of `s` with `X ×_S U` a scheme. Being an open subspace of `X` which is a
scheme, `X ×_S U` then lies in the schematic locus of Stacks 03JH, and the images of these open
subspaces exhaust the points of `X`, so the schematic locus is everything and `X` is a scheme.

## Main definitions

* `AlgebraicGeometry.Space.specStalkSiteObject`: `Spec(𝒪_{S, s})` as an object of the big fppf
  site of `S`, which it is by `AlgebraicGeometry.BigFppfSite.contains_spec_stalk_of_contains`.
* `AlgebraicGeometry.Space.affineNhdsDescentSituation`: Situation 084R for the base changes of
  `X` to the affine open neighbourhoods of a point of `S`, with limit the base change to the
  local ring there. Its transition morphisms are open immersions, not merely affine.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_spec_stalk_of_contains`: the spectrum of a local ring of
  `S` belongs to the site, so the base change of the tag is formed inside it with nothing assumed.
* `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_baseChange_specStalkSiteObject`:
  **Stacks 0B80**, at the canonical local scheme, with nothing assumed beyond the tag's own
  hypotheses. This is where the tag is registered.
* `Space.isRepresentable_of_isRepresentable_relocalizeRestrict_specStalkSiteObject`:
  the same in the restriction reading of the base change.
* `AlgebraicGeometry.Space.isAffineHom_baseChangeSiteFunctor_map`,
  `AlgebraicGeometry.Space.isOpenImmersion_baseChangeSiteFunctor_map`,
  `AlgebraicGeometry.Space.isQuasiCompactSpace_baseChangeSiteFunctor_obj` and
  `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_baseChangeSiteFunctor_obj`: the base
  change of a quasi-compact and quasi-separated algebraic space to an affine object of the site
  is a quasi-compact and quasi-separated algebraic space, and the base change of the system
  along a morphism of affine objects is affine and, if that morphism is an open immersion, an
  open immersion.
* `AlgebraicGeometry.Space.range_baseChangeSiteFunctor_le_schematicLocus`: the image in `X` of a
  base change along an open immersion which is a scheme lies in the schematic locus.
* `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_baseChange_specStalk` and
  `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_relocalizeRestrict_specStalk`:
  the two statements above with the local scheme presented as any object of the site identified
  with `Spec(𝒪_{S, s})` over `S` rather than as the canonical one. The two readings of the base
  change agree by `AlgebraicGeometry.Space.isRepresentable_baseChangeSiteFunctor_obj_iff`.

## Implementation notes

An algebraic space over `S` is a presheaf on the big fppf site of `S`, so `S` itself is the
terminal object `Over.mk (𝟙 _)` of that site and the structure morphism of `X` is a morphism
`f : X ⟶ h_S` of presheaves. The base change of `X` to an object `T` of the site is the fibre
product `h_T ×_{h_S} X`, which is `AlgebraicGeometry.Space.baseChangeSiteFunctor` applied to
`T`; over the terminal object a fibre product is a product, which is what makes the fibre
product reading agree with the restriction reading of Stacks 03I5 part (1).

*Where the point `s` comes from.* Points of `X` are equivalence classes of field-valued points
(Stacks 03BU), and a field-valued point `p` has a structure morphism `Spec(κ) ⟶ S` whose image
point is `s`. Its factorization `Spec(κ) ⟶ Spec(𝒪_{S, s}) ⟶ U` through the affine open
neighbourhood produced by Stacks 07SR is `AlgebraicGeometry.Scheme.stalkClosedPointTo` followed
by `AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem`, and it is what places the point in the
image of `X ×_S U`, hence in the schematic locus.

*Stacks 03JH is available unconditionally.* The schematic locus of an algebraic space is an open
subspace and is representable, by
`AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace`;
no cofinality bound on a family of representable open subspaces is needed. So the only input of
Stacks 0B80 that this library does not have is Stacks 07SR *in a size-free form*.

*Where Stacks 07SR comes from, and why the system needs no bound.* Stacks 07SR is
`AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall`, and
it asks of the inverse system only that it be small for the site,
`AlgebraicGeometry.Space.IsSiteSmall`. The system here — the base changes of `X` to the affine
open neighbourhoods of `s` — meets that condition with nothing asked of the index: its
transition morphisms are open immersions
(`AlgebraicGeometry.Space.isOpenImmersion_baseChangeSiteFunctor_map`), hence immersions, hence
monomorphisms by Stacks 042R, and that is the second alternative of
`AlgebraicGeometry.Space.IsSiteSmall`. So the registration carries no side condition on the
site.

**Why the system is not thinned.** An earlier form of this argument met a Stacks 07SR stated
at `#I < B.cutoff.ord.cof` by asking the site for a regular cutoff: the index is the set
`AlgebraicGeometry.Scheme.AffineNhds S s`, which numbers at most
`#S.affineOpens ≤ S.size < B.cutoff` by `AlgebraicGeometry.Scheme.mk_affineOpens_le_size`, and
regularity is exactly what turns `< B.cutoff` into `< B.cutoff.ord.cof`. That route cannot be
repaired by thinning the system, since the limit is unchanged only by passing to a *cofinal*
subfamily, that is to a basis of affine open neighbourhoods of `s`; the least cardinality of
one is the cofinality of that neighbourhood filter, and for `S = Spec(k[x_α : α < κ])` at its
generic point that is exactly `κ`. Indeed a cofinal family must have, for each `α`, a member
contained in the basic open `D(x_α)`; an affine open is a finite union of basic opens `D(f)`,
and `D(f) ⊆ D(x_α)` forces `x_α` to divide a power of `f`, so each member of the family is
contained in `D(x_α)` for only finitely many `α`. An `AlgebraicGeometry.BigFppfSite` requires
of its cutoff only that it be uncountable, a strong prelimit and of uncountable cofinality —
`ℶ_{ω₁}` is such a cardinal, and is singular of cofinality `ω₁` — so `κ` can exceed
`B.cutoff.ord.cof` while `Spec(k[x_α : α < κ])` is still an object of the site. The
monomorphism route used instead needs no thinning at all.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 0B80](https://stacks.math.columbia.edu/tag/0B80)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change along an object of the site -/

section BaseChange

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))

/-- The structure morphisms of the objects of the site to `S`, read as morphisms of presheaves,
are compatible with the morphisms of the site: `S` is terminal there. -/
theorem yonedaStructure_naturality {T T' : BigFppfOver B S hS} (g : T ⟶ T') :
    yoneda.map g ≫ (yonedaStructure B S hS).app T' = (yonedaStructure B S hS).app T := by
  simp

/-- The square defining the morphism of base changes induced by a morphism of the site
commutes. -/
theorem baseChangeSiteFunctor_condition {T T' : BigFppfOver B S hS} (g : T ⟶ T') :
    (pullback.fst ((yonedaStructure B S hS).app T) f ≫ yoneda.map g) ≫
        (yonedaStructure B S hS).app T' =
      pullback.snd ((yonedaStructure B S hS).app T) f ≫ f := by
  rw [Category.assoc, yonedaStructure_naturality B S hS g]
  exact pullback.condition

/-- The morphism of base changes induced by a morphism of the site lies over it. -/
theorem baseChangeSiteFunctor_map_fst {T T' : BigFppfOver B S hS} (g : T ⟶ T') :
    (baseChangeSiteFunctor f).map g ≫ pullback.fst ((yonedaStructure B S hS).app T') f =
      pullback.fst ((yonedaStructure B S hS).app T) f ≫ yoneda.map g :=
  pullback.lift_fst _ _ (baseChangeSiteFunctor_condition B S hS f g)

/-- The morphism of base changes induced by a morphism of the site lies over `X`. -/
theorem baseChangeSiteFunctor_map_snd {T T' : BigFppfOver B S hS} (g : T ⟶ T') :
    (baseChangeSiteFunctor f).map g ≫ pullback.snd ((yonedaStructure B S hS).app T') f =
      pullback.snd ((yonedaStructure B S hS).app T) f :=
  pullback.lift_snd _ _ (baseChangeSiteFunctor_condition B S hS f g)

/-- **The base change of the system is a base change of the morphism of the site.** The square
with the two base changes of `X` on top, the two objects of the site below, and the projections
as vertical maps is Cartesian. -/
theorem isPullback_baseChangeSiteFunctor_map {T T' : BigFppfOver B S hS} (g : T ⟶ T') :
    IsPullback ((baseChangeSiteFunctor f).map g)
      (pullback.fst ((yonedaStructure B S hS).app T) f)
      (pullback.fst ((yonedaStructure B S hS).app T') f) (yoneda.map g) := by
  have hbig : IsPullback
      (pullback.lift (pullback.fst ((yonedaStructure B S hS).app T) f ≫ yoneda.map g)
          (pullback.snd ((yonedaStructure B S hS).app T) f)
          (baseChangeSiteFunctor_condition B S hS f g) ≫
        pullback.snd ((yonedaStructure B S hS).app T') f)
      (pullback.fst ((yonedaStructure B S hS).app T) f) f
      (yoneda.map g ≫ (yonedaStructure B S hS).app T') := by
    rw [pullback.lift_snd, yonedaStructure_naturality B S hS g]
    exact (IsPullback.of_hasPullback _ f).flip
  exact IsPullback.of_right hbig (baseChangeSiteFunctor_map_fst B S hS f g)
    (IsPullback.of_hasPullback _ f).flip

/-- The base change of an algebraic space over `S` to an object of the site is an algebraic
space over `S`: it is a fibre product of algebraic spaces. -/
theorem isAlgebraicSpace_baseChangeSiteFunctor_obj (hX : IsAlgebraicSpace B S hS X)
    (T : BigFppfOver B S hS) :
    IsAlgebraicSpace B S hS ((baseChangeSiteFunctor f).obj T) :=
  isAlgebraicSpace_pullback B S hS ((yonedaStructure B S hS).app T) f
    (isAlgebraicSpace_yoneda B S hS T) hX
    (isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS))))

/-- The base change of a quasi-compact algebraic space over `S` to an affine object of the site
is quasi-compact: this is the implication (1) ⇒ (3) of Stacks 03KG. -/
theorem isQuasiCompactSpace_baseChangeSiteFunctor_obj (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompact B S hS f) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsQuasiCompactSpace B S hS ((baseChangeSiteFunctor f).obj T) := by
  have h := ((isQuasiCompact_tfae B S hS hX
    (isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))) f).out 1 3).mp hqc
  exact h T ((yonedaStructure B S hS).app T) hT

/-- The base change of a quasi-separated algebraic space over `S` to an affine object of the
site is quasi-separated, absolutely: the projection to the affine object is quasi-separated,
being a base change of the structure morphism, and an affine object of the site is absolutely
quasi-separated, so Stacks 04ZH part (2) applies. -/
theorem isAbsolutelyQuasiSeparated_baseChangeSiteFunctor_obj (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsQuasiSeparated B S hS f) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsAbsolutelyQuasiSeparated B S hS B.contains_terminal
      ((baseChangeSiteFunctor f).obj T) := by
  have _ := hT
  have hTqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (yoneda.obj T) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj T)
      B.contains_terminal ⟨T, inferInstance, ⟨Functor.RepresentableBy.yoneda T⟩⟩
  have hfst : IsQuasiSeparated B S hS (pullback.fst ((yonedaStructure B S hS).app T) f) :=
    isQuasiSeparated_of_isPullback B S hS
      (IsPullback.of_hasPullback ((yonedaStructure B S hS).app T) f).flip hqs
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal
    (isAlgebraicSpace_baseChangeSiteFunctor_obj B S hS f hX T) hTqs hfst

/-- The morphism of base changes induced by a morphism of affine objects of the site is affine:
it is a base change of the represented morphism, which is affine because a morphism of affine
schemes is. -/
theorem isAffineHom_baseChangeSiteFunctor_map {T T' : BigFppfOver B S hS} (g : T ⟶ T')
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')) :
    IsAffineHom B S hS ((baseChangeSiteFunctor f).map g) :=
  isAffineHom_of_isPullback (isPullback_baseChangeSiteFunctor_map B S hS f g).flip
    (have := hT; have := hT'; isAffineHom_yoneda_map B S hS g)

/-- The morphism of base changes induced by an open immersion of the site is an open immersion:
it is a base change of the represented morphism, and open immersions of presheaves are stable
under base change. -/
theorem isOpenImmersion_baseChangeSiteFunctor_map {T T' : BigFppfOver B S hS} (g : T ⟶ T')
    (hg : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g)) :
    IsOpenImmersion B S hS ((baseChangeSiteFunctor f).map g) := by
  have hy : IsOpenImmersion B S hS (yoneda.map g) :=
    (presheaf_yoneda_map_iff B S hS
      (P := @AlgebraicGeometry.IsOpenImmersion.{u}) inferInstance g).mpr hg
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_baseChangeSiteFunctor_map B S hS f g).flip hy

/-- **A base change which is a scheme along an open immersion lands in the schematic locus.**
If the structure morphism of `T` is an open immersion and the base change `X ×_S T` is
representable, then the image of `X ×_S T` in `X` is contained in the schematic locus of `X`:
that image is an open subspace of `X`, isomorphic to the base change and so representable, and
the schematic locus of Stacks 03JH contains every representable open subspace. -/
theorem range_baseChangeSiteFunctor_le_schematicLocus (hX : IsAlgebraicSpace B S hS X)
    (T : BigFppfOver B S hS)
    (hT : IsOpenImmersion B S hS ((yonedaStructure B S hS).app T))
    (hrep : ((baseChangeSiteFunctor f).obj T).IsRepresentable) :
    Subfunctor.range (pullback.snd ((yonedaStructure B S hS).app T) f) ≤
      schematicLocus B S hS X := by
  have hj : IsOpenImmersion B S hS (pullback.snd ((yonedaStructure B S hS).app T) f) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback ((yonedaStructure B S hS).app T) f) hT
  have _ : Mono (pullback.snd ((yonedaStructure B S hS).app T) f) :=
    mono_of_isOpenImmersion B S hS _ hj
  have _ : (Limits.pullback ((yonedaStructure B S hS).app T) f).IsRepresentable := hrep
  have _ : IsIso (Subfunctor.toRange (pullback.snd ((yonedaStructure B S hS).app T) f)) :=
    inferInstance
  exact le_schematicLocus B S hS X _
    (isOpenSubspace_subfunctorRange B S hS
      (isAlgebraicSpace_baseChangeSiteFunctor_obj B S hS f hX T) hj)
    (isRepresentable_of_natIso (Limits.pullback ((yonedaStructure B S hS).app T) f)
      (asIso (Subfunctor.toRange (pullback.snd ((yonedaStructure B S hS).app T) f))))

/-! ### The two readings of the base change -/

/-- **Over the terminal object a fibre product is a product.** The base change `X ×_S T`, which
is a fibre product over the terminal object `S` of the site, is the product of `h_T` with
`X`. -/
noncomputable def baseChangeSiteFunctorObjIsoProd (T : BigFppfOver B S hS) :
    (baseChangeSiteFunctor f).obj T ≅ FunctorToTypes.prod (yoneda.obj T) X := by
  have hterm : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hS)))) :=
    IsTerminal.isTerminalObj yoneda (Over.mk (𝟙 (B.obj hS))) Over.mkIdTerminal
  have hPB : IsPullback (prod.fst : yoneda.obj T ⨯ X ⟶ _) prod.snd
      ((yonedaStructure B S hS).app T) f := by
    rw [hterm.hom_ext ((yonedaStructure B S hS).app T) (hterm.from _),
      hterm.hom_ext f (hterm.from X)]
    exact IsPullback.of_is_product' (prodIsProd (yoneda.obj T) X) hterm
  exact hPB.isoPullback.symm ≪≫ FunctorToTypes.binaryProductIso (yoneda.obj T) X

/-- **The two readings of "the base change `X ×_S T` is a scheme" agree.** The fibre product
`X ×_S T`, read as a presheaf over `S`, is representable exactly when the restriction of `X` to
the big fppf site over `T` — the base change as a space over its own base, Stacks 03I5 part (1)
— is.

Over the terminal object of the site the fibre product is a product, so this is
`CategoryTheory.OverShriek.isRepresentable_relocalizeRestrict_iff`. -/
theorem isRepresentable_baseChangeSiteFunctor_obj_iff (T : BigFppfOver B S hS) :
    ((baseChangeSiteFunctor f).obj T).IsRepresentable ↔
      ((OverShriek.relocalizeRestrict T.hom).obj X).IsRepresentable := by
  rw [OverShriek.isRepresentable_relocalizeRestrict_iff]
  constructor
  · intro h
    exact isRepresentable_of_natIso _ (baseChangeSiteFunctorObjIsoProd B S hS f T)
  · intro h
    have _ : (FunctorToTypes.prod (yoneda.obj T) X).IsRepresentable := h
    exact isRepresentable_of_natIso _ (baseChangeSiteFunctorObjIsoProd B S hS f T).symm

end BaseChange

/-! ### The local scheme at a point of the base is an object of the site -/

/-- `Spec(𝒪_{S, s})` as an object of the big fppf site of `S`, through the canonical
morphism `Spec(𝒪_{S, s}) ⟶ S`. -/
noncomputable def specStalkSiteObject (s : S) : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (S.fromSpecStalk s) :
    B.obj (B.contains_spec_stalk_of_contains hS s) ⟶ B.obj hS)

/-! ### Situation 084R for the affine open neighbourhoods of a point of the base -/

section DescentSituation

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))

/-- The structure morphism of the site object of an affine open neighbourhood is an open
immersion of presheaves. -/
theorem isOpenImmersion_yonedaStructure_affineNhdsSiteObject (s : S)
    (U : Scheme.AffineNhds S s) :
    IsOpenImmersion B S hS
      ((yonedaStructure B S hS).app (affineNhdsSiteObject B S hS s U)) := by
  have hmap : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (Over.homMk (affineNhdsSiteObject B S hS s U).hom (by simp) :
        affineNhdsSiteObject B S hS s U ⟶ Over.mk (𝟙 (B.obj hS)))) :=
    inferInstanceAs (AlgebraicGeometry.IsOpenImmersion U.opens.ι)
  exact (presheaf_yoneda_map_iff B S hS
    (P := @AlgebraicGeometry.IsOpenImmersion.{u}) inferInstance _).mpr hmap

/-- The transition morphisms of the system of affine open neighbourhoods of `s` are open
immersions of schemes, being inclusions of one open into another. -/
theorem isOpenImmersion_toScheme_affineNhdsSiteSystem_map (s : S)
    {i j : (Scheme.AffineNhds S s)ᵒᵖ} (g : i ⟶ j) :
    AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map ((affineNhdsSiteSystem B S hS s).map g)) := by
  show AlgebraicGeometry.IsOpenImmersion
    (S.homOfLE (show i.unop.opens ≤ j.unop.opens from leOfHom g.unop))
  infer_instance

/-- **Situation 084R for the base changes to the affine open neighbourhoods of `s`.** For a
quasi-compact and quasi-separated algebraic space `X` over `S` and an object `T` of the site
identified with `Spec(𝒪_{S, s})` over `S`, the base changes `X ×_S U` over the affine open
neighbourhoods `U` of `s` form a limit situation whose limit is `X ×_S T`. -/
noncomputable def affineNhdsDescentSituation (s : S) (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompact B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (T : BigFppfOver B S hS) (e : T.left.obj ≅ Spec (S.presheaf.stalk s))
    (he : B.inclusion.map T.hom = e.hom ≫ S.fromSpecStalk s) :
    DescentSituation B S hS B.contains_terminal (Scheme.AffineNhds S s) where
  system := affineNhdsSiteSystem B S hS s ⋙ baseChangeSiteFunctor f
  algebraicSpace _ := isAlgebraicSpace_baseChangeSiteFunctor_obj B S hS f hX _
  transition_affine := fun {i j} g =>
    isAffineHom_baseChangeSiteFunctor_map B S hS f ((affineNhdsSiteSystem B S hS s).map g)
      i.unop.2.1 j.unop.2.1
  quasiCompact i := isQuasiCompactSpace_baseChangeSiteFunctor_obj B S hS f hX hqc _ i.2.1
  quasiSeparated i :=
    isAbsolutelyQuasiSeparated_baseChangeSiteFunctor_obj B S hS f hX hqs _ i.2.1
  limitCone := (baseChangeSiteFunctor f).mapCone (affineNhdsSiteConeOfStalkIso T e he)
  isLimit := isLimitBaseChangeAffineNhdsCone f T e he
  limitAlgebraicSpace := isAlgebraicSpace_baseChangeSiteFunctor_obj B S hS f hX T
  base := Classical.arbitrary (Scheme.AffineNhds S s)

end DescentSituation

/-! ### The schematic locus from the points it sees -/

section SchematicLocus

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **An algebraic space whose schematic locus sees every point is its schematic locus.** If
every point of `X` is in the image of the schematic locus, then the identity of `X` factors
through it by Stacks 03IE, so the schematic locus is everything. -/
theorem schematicLocus_eq_top_of_forall_mem_range_points (hX : IsAlgebraicSpace B S hS X)
    (hcov : ∀ q : points B S hS X, q ∈ Set.range (pointsMap B S hS
      (schematicLocus B S hS X).toFunctor (schematicLocus B S hS X).ι)) :
    schematicLocus B S hS X = ⊤ := by
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS hX hX
    (schematicLocus B S hS X)
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX).1
    (𝟙 X)).2 (fun q _ => hcov q)
  refine top_unique fun T x _ => ?_
  have hval : (g.app T x).val = x := congrArg (fun α : X ⟶ X => α.app T x) hg
  show x ∈ (schematicLocus B S hS X).obj T
  rw [← hval]
  exact (g.app T x).property

/-- **An algebraic space whose schematic locus is everything is a scheme.** The schematic locus
is representable by Stacks 03JH, and if it is everything its inclusion is an isomorphism. -/
theorem isRepresentable_of_schematicLocus_eq_top (hX : IsAlgebraicSpace B S hS X)
    (hL : schematicLocus B S hS X = ⊤) : X.IsRepresentable := by
  have _ : (schematicLocus B S hS X).toFunctor.IsRepresentable :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX).2
  have _ : IsIso (schematicLocus B S hS X).ι := (Subfunctor.eq_top_iff_isIso _).mp hL
  exact isRepresentable_of_natIso _ (asIso (schematicLocus B S hS X).ι)

end SchematicLocus

/-! ### Stacks 0B80, granted Stacks 07SR -/

section Main

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))

/-- **Stacks 0B80 at a local scheme presented as an object of the site.**

Let `X` be an algebraic space over a scheme `S` whose structure morphism is quasi-compact and
quasi-separated. If for every field-valued point `p` of `X`, with image `s` in `S`, some object
of the site identified with `Spec(𝒪_{S, s})` over `S` has schematic base change, then `X` is a
scheme.

Nothing is asked of the size of the index. Stacks 07SR is
`AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall`, and
the system of base changes of `X` to the affine open neighbourhoods of `s` meets its smallness
hypothesis through `AlgebraicGeometry.Space.IsSiteSmall.of_mono`: the transition morphisms are
open immersions (`AlgebraicGeometry.Space.isOpenImmersion_baseChangeSiteFunctor_map`), hence
immersions, hence monomorphisms by Stacks 042R, and for such a system nothing is asked of the
index. -/
theorem isRepresentable_of_isRepresentable_baseChange_specStalk
    (hX : IsAlgebraicSpace B S hS X) (hqc : IsQuasiCompact B S hS f)
    (hqs : IsQuasiSeparated B S hS f)
    (hloc : ∀ p : FieldValuedPoint B S hS X,
      ∃ (T : BigFppfOver B S hS) (e : T.left.obj ≅
          Spec (S.presheaf.stalk (p.toBase (IsLocalRing.closedPoint p.carrier)))),
        B.inclusion.map T.hom =
            e.hom ≫ S.fromSpecStalk (p.toBase (IsLocalRing.closedPoint p.carrier)) ∧
          ((baseChangeSiteFunctor f).obj T).IsRepresentable) :
    X.IsRepresentable := by
  classical
  refine isRepresentable_of_schematicLocus_eq_top B S hS X hX
    (schematicLocus_eq_top_of_forall_mem_range_points B S hS X hX fun q => ?_)
  induction q using Quot.inductionOn with
  | h p =>
    obtain ⟨T, e, he, hT⟩ := hloc p
    obtain ⟨U, hU⟩ := DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall
      (affineNhdsDescentSituation B S hS f _ hX hqc hqs T e he)
      (.of_mono fun {i j} φ => mono_of_isImmersion B S hS
        (isImmersion_of_isOpenImmersion B S hS
          (isOpenImmersion_baseChangeSiteFunctor_map B S hS f _
            (isOpenImmersion_toScheme_affineNhdsSiteSystem_map B S hS _ φ)))) hT
    have hle := range_baseChangeSiteFunctor_le_schematicLocus B S hS f hX
      (affineNhdsSiteObject B S hS _ U)
      (isOpenImmersion_yonedaStructure_affineNhdsSiteObject B S hS _ U) hU
    have hfac : (Spec.map (Scheme.stalkClosedPointTo p.toBase) ≫
        U.opens.fromSpecStalkOfMem _ U.2.2) ≫ U.opens.ι = p.toBase := by
      rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk p.toBase
    let k : p.siteObject ⟶ affineNhdsSiteObject B S hS _ U :=
      Over.homMk (ObjectProperty.homMk (Spec.map (Scheme.stalkClosedPointTo p.toBase) ≫
        U.opens.fromSpecStalkOfMem _ U.2.2)) (by
          apply ObjectProperty.hom_ext
          exact hfac)
    let α : yoneda.obj p.siteObject ⟶ X := yonedaEquiv.symm p.value
    have hcomm : yoneda.map k ≫
        (yonedaStructure B S hS).app (affineNhdsSiteObject B S hS _ U) = α ≫ f := by
      ext W x
      exact Over.mkIdTerminal.hom_ext _ _
    have hp : p.value ∈ (schematicLocus B S hS X).obj (op p.siteObject) := by
      refine hle _ ⟨yonedaEquiv (pullback.lift (yoneda.map k) α hcomm), ?_⟩
      rw [← yonedaEquiv_comp, pullback.lift_snd]
      exact yonedaEquiv.apply_symm_apply p.value
    exact ⟨(⟨p.carrier, p.contained, p.toBase, ⟨p.value, hp⟩⟩ :
      FieldValuedPoint B S hS (schematicLocus B S hS X).toFunctor).class B S hS _, rfl⟩

/-- **Stacks 0B80 in the restriction reading of the base change.** The same statement as
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_baseChange_specStalk`, with
`X ×_S Spec(𝒪_{S, s})` read as the restriction of `X` to the big fppf site over
`Spec(𝒪_{S, s})` rather than as the fibre product over `S`. The two readings agree by
`AlgebraicGeometry.Space.isRepresentable_baseChangeSiteFunctor_obj_iff`. -/
theorem isRepresentable_of_isRepresentable_relocalizeRestrict_specStalk
    (hX : IsAlgebraicSpace B S hS X) (hqc : IsQuasiCompact B S hS f)
    (hqs : IsQuasiSeparated B S hS f)
    (hloc : ∀ p : FieldValuedPoint B S hS X,
      ∃ (T : BigFppfOver B S hS) (e : T.left.obj ≅
          Spec (S.presheaf.stalk (p.toBase (IsLocalRing.closedPoint p.carrier)))),
        B.inclusion.map T.hom =
            e.hom ≫ S.fromSpecStalk (p.toBase (IsLocalRing.closedPoint p.carrier)) ∧
          ((OverShriek.relocalizeRestrict T.hom).obj X).IsRepresentable) :
    X.IsRepresentable :=
  isRepresentable_of_isRepresentable_baseChange_specStalk B S hS f hX hqc hqs
    (fun p => by
      obtain ⟨T, e, he, hrep⟩ := hloc p
      exact ⟨T, e, he, (isRepresentable_baseChangeSiteFunctor_obj_iff B S hS f T).mpr hrep⟩)

/-- **Stacks 0B80.** Let `X` be an algebraic space over a scheme `S` whose structure morphism
`f` is quasi-compact and quasi-separated. If for every point of `X`, with image `s` in `S`, the
base change `X ×_S Spec(𝒪_{S, s})` is a scheme, then `X` is a scheme.

This is the same statement as
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_baseChange_specStalk` with the
object of the site no longer quantified over: `Spec(𝒪_{S, s})` *is* an object of the big fppf
site of `S` whenever `S` is, by `AlgebraicGeometry.BigFppfSite.contains_spec_stalk_of_contains`, so
the
base change of the tag is formed inside the site with nothing assumed.

Nothing is assumed beyond the tag's own hypotheses: no condition on the size of the system of
affine open neighbourhoods of `s` and none on the site's size cutoff. See the module
documentation for how Stacks 07SR is met. -/
@[stacks 0B80]
theorem isRepresentable_of_isRepresentable_baseChange_specStalkSiteObject
    (hX : IsAlgebraicSpace B S hS X) (hqc : IsQuasiCompact B S hS f)
    (hqs : IsQuasiSeparated B S hS f)
    (hloc : ∀ p : FieldValuedPoint B S hS X,
      ((baseChangeSiteFunctor f).obj (specStalkSiteObject B S hS
        (p.toBase (IsLocalRing.closedPoint p.carrier)))).IsRepresentable) :
    X.IsRepresentable :=
  isRepresentable_of_isRepresentable_baseChange_specStalk B S hS f hX hqc hqs
    (fun p => ⟨specStalkSiteObject B S hS _, Iso.refl _, by simp [specStalkSiteObject],
      hloc p⟩)

/-- **Stacks 0B80 in the restriction reading of the base change, at the canonical local
scheme.** The hypothesis is that the restriction of `X` to the big fppf site over
`Spec(𝒪_{S, s})` — the base change of Stacks 03I5 part (1) — is a scheme, for `s` the image of
each point of `X`. -/
theorem isRepresentable_of_isRepresentable_relocalizeRestrict_specStalkSiteObject
    (hX : IsAlgebraicSpace B S hS X) (hqc : IsQuasiCompact B S hS f)
    (hqs : IsQuasiSeparated B S hS f)
    (hloc : ∀ p : FieldValuedPoint B S hS X,
      ((OverShriek.relocalizeRestrict (specStalkSiteObject B S hS
        (p.toBase (IsLocalRing.closedPoint p.carrier))).hom).obj X).IsRepresentable) :
    X.IsRepresentable :=
  isRepresentable_of_isRepresentable_baseChange_specStalkSiteObject B S hS f hX hqc hqs
    (fun p => (isRepresentable_baseChangeSiteFunctor_obj_iff B S hS f _).mpr (hloc p))

end Main

end Space

end AlgebraicGeometry

end
