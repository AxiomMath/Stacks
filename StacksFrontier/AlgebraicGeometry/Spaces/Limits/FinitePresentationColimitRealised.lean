module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsolutelyQuasiSeparatedAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePointsQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationColimitEssIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationCanonicalFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentRealised
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpensStalkAffineNhdsSiteLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StalkAffineNhdsSiteLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Retrocompact

/-!
# The `2`-colimit identification, for a limit realised in the site

Stacks 0E90 and Stacks 0E91 are stated, in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedFibreGlueing` and
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLocalRingGlueing`, from a
hypothesis `AlgebraicGeometry.FinitePresentationSpacesOver.IsFinitePresentationColimit`, that base
change exhibits the algebraic spaces of finite presentation over the vertex of a cone as the
cofiltered `2`-colimit of those over the stages. That hypothesis has four fields. This file
discharges **all four** of them — `faithful`, `full` and `essSurj` from the three clauses of
Stacks 07SK in the form that carries no hypothesis on the size of the index category, and
`essIso` from `full` and `faithful` by the cofiltered argument of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationColimitEssIso` — assembles them
into the structure, and instantiates each at the two systems those two tags take the colimit
over.

The two formulations differ only in packaging, and the translation between them costs nothing:
`AlgebraicGeometry.FinitePresentationSpacesOver.baseChange` is base change along the Yoneda image,
restricted to the full subcategory of algebraic spaces of finite presentation, so
`AlgebraicGeometry.FinitePresentationSpacesOver.ι_map_baseChange_map` — which holds by `rfl` —
carries an equation of morphisms across the inclusion in either direction, and the inclusion of a
full subcategory is faithful.

## Main results

* `AlgebraicGeometry.FinitePresentationSpacesOver.faithful_of_isLimitMapCone`: the `faithful`
  field of `IsFinitePresentationColimit`, for an arbitrary diagram in the big fppf category over
  `S` and an arbitrary cone on it whose image under the underlying-scheme functor is a limit cone.
* `AlgebraicGeometry.FinitePresentationSpacesOver.faithful_specStalkSiteCone`: the same
  for the system of affine open neighbourhoods of a point `s` and the cone with vertex
  `Spec 𝒪_{S, s}`, where the three hypotheses are discharged outright.

* `AlgebraicGeometry.FinitePresentationSpacesOver.faithful_opensSpecStalkSiteCone`: the same for
  the system of the overlaps `W ∩ U` with an open `U` of `S` and the cone with vertex the
  preimage of `U` in `Spec 𝒪_{S, s}`, under the hypothesis that `U` is retrocompact.
* `AlgebraicGeometry.FinitePresentationSpacesOver.full_of_isLimitMapCone`: the `full` field, in
  the same generality, from the fullness clause of Stacks 07SK in the size-free form.
* `AlgebraicGeometry.FinitePresentationSpacesOver.full_specStalkSiteCone` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.full_opensSpecStalkSiteCone`: that field at the
  two systems, with the hypotheses discharged as for the faithfulness clause.
* `AlgebraicGeometry.FinitePresentationSpacesOver.essSurj_of_isLimitMapCone`: the `essSurj`
  field, in the same generality, from the essential-surjectivity clause of Stacks 07SK in the
  size-free form.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isFinitePresentationColimit_of_isLimitMapCone`:
  **all four fields, assembled**, for an arbitrary cone whose image under the underlying-scheme
  functor is a limit cone.
* `isFinitePresentationColimit_specStalkSiteCone` and
  `isFinitePresentationColimit_opensSpecStalkSiteCone`, of this namespace: that structure at the
  two systems the tags take the colimit over. The first, at the affine open neighbourhoods of
  `s`, carries no hypothesis — the `hloc` of Stacks 0E90 and Stacks 0E91. The second, at the
  overlaps `W ∩ U`, carries only retrocompactness of `U` — the `hoverlap` of those tags, and the
  one place their quasi-compactness of `U → S` is used.

The two instantiations differ in where quasi-compactness of the stages comes from. The
neighbourhoods are affine, so it is free. The overlaps need not be affine — an intersection
`W ∩ U` is only quasi-affine — so there it comes from retrocompactness of `U`, which is what the
hypothesis of Stacks 0E90 and Stacks 0E91 that the complement of the point be quasi-compact over
`S` delivers. Affineness of the transition morphisms is available on both systems: on the
overlaps each transition is a base change of a transition morphism of the neighbourhoods, hence a
morphism of affine schemes.

## Where the four fields come from

Three are the three clauses of Stacks 07SK in the form that replaces the bound on the size of the
index category by the hypothesis that the limit is realised by an object of the site:
`AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq_of_isLimit` for `faithful` and
`AlgebraicGeometry.Space.exists_model_of_finitePresentation_of_isLimit` for `essSurj`, both of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentRealised`, and
`AlgebraicGeometry.Space.exists_morphism_canonical_after_baseChange_of_isLimit` of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationCanonicalFullness` for `full`. The
fourth, `essIso`, needs no clause of Stacks 07SK of its own: it is a consequence of `full` and
`faithful` by a cofiltered argument.

No field is ever assumed. A structure one of whose fields was assumed would reintroduce exactly
the conditional statement that discharging it is meant to remove, so each of the two
instantiations is built from the three clauses and the cofiltered argument, and carries only the
hypotheses listed above — none for the system of neighbourhoods, retrocompactness of `U` for the
system of overlaps.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FinitePresentationSpacesOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type u} [Category.{u} I] [IsCofiltered I] {Dsite : I ⥤ BigFppfOver B S hS}

/-- **Two morphisms of algebraic spaces of finite presentation over a stage whose base changes to
the vertex agree already agree at a later stage.** This is the `faithful` field of
`AlgebraicGeometry.FinitePresentationSpacesOver.IsFinitePresentationColimit`, for a cone whose
image under the underlying-scheme functor is a limit cone.

It is Stacks 07SK, in the form that replaces the bound on the size of the index category by the
hypothesis that the limit is realised by an object of the site, read in the full subcategory of
algebraic spaces of finite presentation instead of in the slice of presheaves. The stages are not
assumed affine, only quasi-compact. -/
theorem faithful_of_isLimitMapCone
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      IsAffineHom ((BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cS))
    (hQc : ∀ i, Space.IsQuasiCompactSpace B S hS (yoneda.obj (Dsite.obj i)))
    (i : I) (X Y : FinitePresentationSpacesOver B S hS (Dsite.obj i)) (f g : X ⟶ Y)
    (hfg : (baseChange B S hS (cS.π.app i)).map f =
      (baseChange B S hS (cS.π.app i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (baseChange B S hS (Dsite.map e)).map f = (baseChange B S hS (Dsite.map e)).map g := by
  obtain ⟨j, e, he⟩ := Space.eventually_eq_of_baseChange_eq_of_isLimit B S hS hAffine hcS hQc i
    X.obj Y.obj X.property.1 Y.property.1 X.property.2 Y.property.2
    ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS (Dsite.obj i))).map f)
    ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS (Dsite.obj i))).map g)
    (by rw [← ι_map_baseChange_map, ← ι_map_baseChange_map, hfg])
  refine ⟨j, e,
    (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS (Dsite.obj j))).map_injective ?_⟩
  rw [ι_map_baseChange_map, ι_map_baseChange_map]
  exact he

/-- The transition morphisms of the affine open neighbourhood diagram are affine. -/
private theorem isAffineHom_toScheme_map_affineOpenNhdsSiteDiagram_map (s : S)
    {i j : AffineOpenNhds S s} (e : i ⟶ j) :
    IsAffineHom ((BigFppfOver.toScheme B S hS).map
      ((affineOpenNhdsSiteDiagram B S hS s).map e)) := by
  rw [toScheme_map_affineOpenNhdsSiteDiagram_map]
  exact isAffineHom_affineOpenNhdsDiagram_map S s e

/-- Each stage of the affine open neighbourhood diagram is a quasi-compact space. -/
private theorem isQuasiCompactSpace_yoneda_affineOpenNhdsSiteDiagram_obj (s : S)
    (k : AffineOpenNhds S s) :
    Space.IsQuasiCompactSpace B S hS (yoneda.obj ((affineOpenNhdsSiteDiagram B S hS s).obj k)) :=
  Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS _
    (isAffine_toScheme_affineOpenNhdsSiteDiagram_obj B S hS s k)

/-- Each stage of the affine open neighbourhood diagram is absolutely quasi-separated. -/
private theorem isAbsolutelyQuasiSeparated_yoneda_affineOpenNhdsSiteDiagram_obj (s : S)
    (k : AffineOpenNhds S s) :
    Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B)
      (yoneda.obj ((affineOpenNhdsSiteDiagram B S hS s).obj k)) :=
  Space.isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS B.contains_terminal _
    (isAffine_toScheme_affineOpenNhdsSiteDiagram_obj B S hS s k)

/-- Each overlap stage is a quasi-compact space when `U` is retrocompact. -/
private theorem isQuasiCompactSpace_yoneda_opensSpecStalkSiteDiagram_obj (s : S)
    (W₀ : AffineOpenNhds S s) (U : S.Opens) (hU : IsRetrocompact (U : Set S)) (k : Over W₀) :
    Space.IsQuasiCompactSpace B S hS
      (yoneda.obj ((opensSpecStalkSiteDiagram B S hS s W₀ U).obj k)) := by
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((opensSpecStalkSiteDiagram B S hS s W₀ U).obj k)) :=
    compactSpace_opensSpecStalkDiagram_obj_of_isRetrocompact S U hU W₀ k
  exact (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS _
      (isAlgebraicSpace_yoneda B S hS _)).mpr
    (Space.compactSpace_points_yoneda B S hS _)

/-- Each overlap stage is absolutely quasi-separated. -/
private theorem isAbsolutelyQuasiSeparated_yoneda_opensSpecStalkSiteDiagram_obj (s : S)
    (W₀ : AffineOpenNhds S s) (U : S.Opens) (k : Over W₀) :
    Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B)
      (yoneda.obj ((opensSpecStalkSiteDiagram B S hS s W₀ U).obj k)) := by
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj
      ((opensSpecStalkSiteDiagram B S hS s W₀ U).obj k)) :=
    quasiSeparatedSpace_opensSpecStalkDiagram_obj S U W₀ k
  exact Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _
    (BigFppfSite.contains_terminal B)
    ⟨(opensSpecStalkSiteDiagram B S hS s W₀ U).obj k, inferInstance,
      ⟨Functor.RepresentableBy.yoneda _⟩⟩

/-- **The faithfulness clause for the affine open neighbourhoods of a point and the cone with
vertex `Spec 𝒪_{S, s}`.** The three hypotheses of
`AlgebraicGeometry.FinitePresentationSpacesOver.faithful_of_isLimitMapCone` are discharged:
the transition morphisms are morphisms of affine schemes, the stages are affine and hence
quasi-compact, and the limit identification is
`AlgebraicGeometry.isLimitMapConeSpecStalkSiteCone`.

No hypothesis on the site, on the size of the index category, or on the point `s` enters. -/
theorem faithful_specStalkSiteCone (s : S) (i : AffineOpenNhds S s)
    (X Y : FinitePresentationSpacesOver B S hS ((affineOpenNhdsSiteDiagram B S hS s).obj i))
    (f g : X ⟶ Y)
    (hfg : (baseChange B S hS ((specStalkSiteCone B S hS s).π.app i)).map f =
      (baseChange B S hS ((specStalkSiteCone B S hS s).π.app i)).map g) :
    ∃ (j : AffineOpenNhds S s) (e : j ⟶ i),
      (baseChange B S hS ((affineOpenNhdsSiteDiagram B S hS s).map e)).map f =
        (baseChange B S hS ((affineOpenNhdsSiteDiagram B S hS s).map e)).map g :=
  faithful_of_isLimitMapCone B S hS
    (isAffineHom_toScheme_map_affineOpenNhdsSiteDiagram_map B S hS s)
    (isLimitMapConeSpecStalkSiteCone B S hS s)
    (isQuasiCompactSpace_yoneda_affineOpenNhdsSiteDiagram_obj B S hS s)
    i X Y f g hfg

/-- **The faithfulness clause for the overlaps `W ∩ U` and the cone with vertex the preimage of
`U` in `Spec 𝒪_{S, s}`.** This is the companion of
`AlgebraicGeometry.FinitePresentationSpacesOver.faithful_specStalkSiteCone` on the other of the
two systems that Stacks 0E90 and Stacks 0E91 take the `2`-colimit over, and the three hypotheses
are again discharged.

Quasi-compactness of the stages is the only one that costs anything: an overlap `W ∩ U` need not
be affine, so it does not follow from affineness as it does for the neighbourhoods. It comes from
`CompactSpace` of the underlying scheme — which is where retrocompactness of `U` is used, and so
where the hypothesis of the two tags that the complement of the point be quasi-compact over `S`
enters — carried across the identification of the point space of a represented algebraic space
with the underlying space of the representing scheme.
`AlgebraicGeometry.isRetrocompact_of_quasiCompact_ι` supplies `hU` from `QuasiCompact U.ι`, which
is the form in which the tags state that hypothesis. -/
theorem faithful_opensSpecStalkSiteCone (s : S) (W₀ : AffineOpenNhds S s) (U : S.Opens)
    (hU : IsRetrocompact (U : Set S)) (j : Over W₀)
    (X Y : FinitePresentationSpacesOver B S hS
      ((opensSpecStalkSiteDiagram B S hS s W₀ U).obj j))
    (f g : X ⟶ Y)
    (hfg : (baseChange B S hS ((opensSpecStalkSiteCone B S hS s W₀ U).π.app j)).map f =
      (baseChange B S hS ((opensSpecStalkSiteCone B S hS s W₀ U).π.app j)).map g) :
    ∃ (k : Over W₀) (e : k ⟶ j),
      (baseChange B S hS ((opensSpecStalkSiteDiagram B S hS s W₀ U).map e)).map f =
        (baseChange B S hS ((opensSpecStalkSiteDiagram B S hS s W₀ U).map e)).map g :=
  faithful_of_isLimitMapCone B S hS
    (fun {_ _} _ => inferInstance)
    (isLimitMapConeOpensSpecStalkSiteCone B S hS s W₀ U)
    (isQuasiCompactSpace_yoneda_opensSpecStalkSiteDiagram_obj B S hS s W₀ U hU)
    j X Y f g hfg

/-- **A morphism between the base changes to the vertex of two algebraic spaces of finite
presentation over a stage is the base change of a morphism at a later stage.** This is the `full`
field of `AlgebraicGeometry.FinitePresentationSpacesOver.IsFinitePresentationColimit`, for a cone
whose image under the underlying-scheme functor is a limit cone.

It is the fullness clause of Stacks 07SK in the size-free form, read in the full subcategory of
algebraic spaces of finite presentation. The comparison isomorphisms are the canonical ones of
`CategoryTheory.Over.pullbackFactorObjIso`, by
`AlgebraicGeometry.Space.exists_morphism_canonical_after_baseChange_of_isLimit`, which is why no
identification of existential witnesses happens here. The stages are not assumed affine, only
quasi-compact. -/
theorem full_of_isLimitMapCone
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      IsAffineHom ((BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cS))
    (hQc : ∀ i, Space.IsQuasiCompactSpace B S hS (yoneda.obj (Dsite.obj i)))
    (hQs : ∀ i, Space.IsAbsolutelyQuasiSeparated B S hS
      (BigFppfSite.contains_terminal B) (yoneda.obj (Dsite.obj i)))
    (i : I) (X Y : FinitePresentationSpacesOver B S hS (Dsite.obj i))
    (h : (baseChange B S hS (cS.π.app i)).obj X ⟶ (baseChange B S hS (cS.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i) (h' : (baseChange B S hS (Dsite.map e)).obj X ⟶
      (baseChange B S hS (Dsite.map e)).obj Y),
      (baseChangeFactorIso B S hS (cS.w e)).hom.app X ≫
          (baseChange B S hS (cS.π.app j)).map h' =
        h ≫ (baseChangeFactorIso B S hS (cS.w e)).hom.app Y := by
  obtain ⟨j, e, g, hg⟩ :=
    Space.exists_morphism_canonical_after_baseChange_of_isLimit B S hS hAffine hcS hQc hQs i
      X.obj Y.obj X.property.1 Y.property.1 X.property.2 Y.property.2
      ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS cS.pt)).map h :
        (Over.pullback (yoneda.map (cS.π.app i))).obj X.obj ⟶
          (Over.pullback (yoneda.map (cS.π.app i))).obj Y.obj)
  refine ⟨j, e, (ObjectProperty.homMk g :
      (baseChange B S hS (Dsite.map e)).obj X ⟶ (baseChange B S hS (Dsite.map e)).obj Y),
    (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS cS.pt)).map_injective ?_⟩
  rw [Functor.map_comp, Functor.map_comp, baseChangeFactorIso_hom_app_left,
    baseChangeFactorIso_hom_app_left, ι_map_baseChange_map]
  exact hg

/-- **The fullness clause for the affine open neighbourhoods of a point and the cone with vertex
`Spec 𝒪_{S, s}`.** All four hypotheses are discharged from affineness of the stages: their
transition morphisms are morphisms of affine schemes, and an affine object of the site represents
a quasi-compact and quasi-separated algebraic space. The limit identification is
`AlgebraicGeometry.isLimitMapConeSpecStalkSiteCone`. -/
theorem full_specStalkSiteCone (s : S) (i : AffineOpenNhds S s)
    (X Y : FinitePresentationSpacesOver B S hS ((affineOpenNhdsSiteDiagram B S hS s).obj i))
    (h : (baseChange B S hS ((specStalkSiteCone B S hS s).π.app i)).obj X ⟶
      (baseChange B S hS ((specStalkSiteCone B S hS s).π.app i)).obj Y) :
    ∃ (j : AffineOpenNhds S s) (e : j ⟶ i)
      (h' : (baseChange B S hS ((affineOpenNhdsSiteDiagram B S hS s).map e)).obj X ⟶
        (baseChange B S hS ((affineOpenNhdsSiteDiagram B S hS s).map e)).obj Y),
      (baseChangeFactorIso B S hS ((specStalkSiteCone B S hS s).w e)).hom.app X ≫
          (baseChange B S hS ((specStalkSiteCone B S hS s).π.app j)).map h' =
        h ≫ (baseChangeFactorIso B S hS ((specStalkSiteCone B S hS s).w e)).hom.app Y :=
  full_of_isLimitMapCone B S hS
    (isAffineHom_toScheme_map_affineOpenNhdsSiteDiagram_map B S hS s)
    (isLimitMapConeSpecStalkSiteCone B S hS s)
    (isQuasiCompactSpace_yoneda_affineOpenNhdsSiteDiagram_obj B S hS s)
    (isAbsolutelyQuasiSeparated_yoneda_affineOpenNhdsSiteDiagram_obj B S hS s)
    i X Y h

/-- **The fullness clause for the overlaps `W ∩ U` and the cone with vertex the preimage of `U`
in `Spec 𝒪_{S, s}`.** Quasi-compactness of the stages is the only hypothesis that costs
anything, and it is where retrocompactness of `U` — the form the two tags' hypothesis on the
complement of the point takes — is used. Quasi-separatedness needs no hypothesis on `U`: every
stage is an open subscheme of an affine scheme. -/
theorem full_opensSpecStalkSiteCone (s : S) (W₀ : AffineOpenNhds S s) (U : S.Opens)
    (hU : IsRetrocompact (U : Set S)) (i : Over W₀)
    (X Y : FinitePresentationSpacesOver B S hS
      ((opensSpecStalkSiteDiagram B S hS s W₀ U).obj i))
    (h : (baseChange B S hS ((opensSpecStalkSiteCone B S hS s W₀ U).π.app i)).obj X ⟶
      (baseChange B S hS ((opensSpecStalkSiteCone B S hS s W₀ U).π.app i)).obj Y) :
    ∃ (j : Over W₀) (e : j ⟶ i)
      (h' : (baseChange B S hS ((opensSpecStalkSiteDiagram B S hS s W₀ U).map e)).obj X ⟶
        (baseChange B S hS ((opensSpecStalkSiteDiagram B S hS s W₀ U).map e)).obj Y),
      (baseChangeFactorIso B S hS ((opensSpecStalkSiteCone B S hS s W₀ U).w e)).hom.app X ≫
          (baseChange B S hS ((opensSpecStalkSiteCone B S hS s W₀ U).π.app j)).map h' =
        h ≫ (baseChangeFactorIso B S hS
          ((opensSpecStalkSiteCone B S hS s W₀ U).w e)).hom.app Y :=
  full_of_isLimitMapCone B S hS
    (fun {_ _} _ => inferInstance)
    (isLimitMapConeOpensSpecStalkSiteCone B S hS s W₀ U)
    (isQuasiCompactSpace_yoneda_opensSpecStalkSiteDiagram_obj B S hS s W₀ U hU)
    (isAbsolutelyQuasiSeparated_yoneda_opensSpecStalkSiteDiagram_obj B S hS s W₀ U)
    i X Y h

/-- **Every algebraic space of finite presentation over the vertex is, up to isomorphism, the
base change of one over a stage.** This is the `essSurj` field of
`AlgebraicGeometry.FinitePresentationSpacesOver.IsFinitePresentationColimit`, for a cone whose
image under the underlying-scheme functor is a limit cone.

It is the essential-surjectivity clause of Stacks 07SK in the size-free form, read in the full
subcategory. No transport is needed: that clause is already stated for an object over the
representable presheaf of the vertex of the given cone. -/
theorem essSurj_of_isLimitMapCone
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      IsAffineHom ((BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cS))
    (hQc : ∀ i, Space.IsQuasiCompactSpace B S hS (yoneda.obj (Dsite.obj i)))
    (hQs : ∀ i, Space.IsAbsolutelyQuasiSeparated B S hS
      (BigFppfSite.contains_terminal B) (yoneda.obj (Dsite.obj i)))
    (Y : FinitePresentationSpacesOver B S hS cS.pt) :
    ∃ (i : I) (Yi : FinitePresentationSpacesOver B S hS (Dsite.obj i)),
      Nonempty ((baseChange B S hS (cS.π.app i)).obj Yi ≅ Y) := by
  obtain ⟨i, Yi, halg, hfp, ⟨θ⟩⟩ :=
    Space.exists_model_of_finitePresentation_of_isLimit B S hS
      (BigFppfSite.contains_terminal B) hAffine hcS hQc hQs Y.obj Y.property.1 Y.property.2
  exact ⟨i, ⟨Yi, ⟨halg, hfp⟩⟩,
    ⟨(ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS cS.pt)).preimageIso θ.symm⟩⟩

/-- **Base change exhibits the algebraic spaces of finite presentation over the vertex of a cone
as the cofiltered `2`-colimit of those over the stages, whenever the cone is a limit cone of
schemes.** All four conditions of
`AlgebraicGeometry.FinitePresentationSpacesOver.IsFinitePresentationColimit` hold: three are the
three clauses of Stacks 07SK in the form that carries no hypothesis on the size of the index
category, and the fourth, `essIso`, follows from the other two by a cofiltered argument and needs
no clause of its own.

This is the hypothesis that the glueing theorems of Stacks 0E90 and Stacks 0E91 carry, now
discharged from a limit of schemes. Nothing is assumed about the size of the index category, and
nothing about the site beyond the stages being quasi-compact and quasi-separated and the
transition morphisms affine. -/
theorem isFinitePresentationColimit_of_isLimitMapCone
    (hAffine : ∀ {i j : I} (f : i ⟶ j),
      IsAffineHom ((BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cS))
    (hQc : ∀ i, Space.IsQuasiCompactSpace B S hS (yoneda.obj (Dsite.obj i)))
    (hQs : ∀ i, Space.IsAbsolutelyQuasiSeparated B S hS
      (BigFppfSite.contains_terminal B) (yoneda.obj (Dsite.obj i))) :
    IsFinitePresentationColimit B S hS Dsite cS.pt (fun i => cS.π.app i)
      (fun {_ _} e => cS.w e) where
  essSurj := essSurj_of_isLimitMapCone B S hS hAffine hcS hQc hQs
  full := full_of_isLimitMapCone B S hS hAffine hcS hQc hQs
  essIso := essIso_of_full_of_faithful B S hS (fun i => cS.π.app i) (fun {_ _} e => cS.w e)
    (full_of_isLimitMapCone B S hS hAffine hcS hQc hQs)
    (faithful_of_isLimitMapCone B S hS hAffine hcS hQc)
  faithful := faithful_of_isLimitMapCone B S hS hAffine hcS hQc

/-! ### The two systems of Stacks 0E90 and Stacks 0E91 -/

/-- **Base change exhibits the algebraic spaces of finite presentation over `Spec 𝒪_{S, s}` as
the cofiltered `2`-colimit of those over the affine open neighbourhoods of `s`.** All four
conditions hold outright: no hypothesis on the site, on the size of the index category, or on the
point `s`.

This is the hypothesis `hloc` of the glueing theorems of Stacks 0E90 and Stacks 0E91, for the
system of neighbourhoods. -/
theorem isFinitePresentationColimit_specStalkSiteCone (s : S) :
    IsFinitePresentationColimit B S hS (affineOpenNhdsSiteDiagram B S hS s)
      (specStalkSiteCone B S hS s).pt
      (fun i => (specStalkSiteCone B S hS s).π.app i)
      (fun {_ _} e => (specStalkSiteCone B S hS s).w e) :=
  isFinitePresentationColimit_of_isLimitMapCone B S hS
    (isAffineHom_toScheme_map_affineOpenNhdsSiteDiagram_map B S hS s)
    (isLimitMapConeSpecStalkSiteCone B S hS s)
    (isQuasiCompactSpace_yoneda_affineOpenNhdsSiteDiagram_obj B S hS s)
    (isAbsolutelyQuasiSeparated_yoneda_affineOpenNhdsSiteDiagram_obj B S hS s)

/-- **Base change exhibits the algebraic spaces of finite presentation over
`V = Spec 𝒪_{S, s} ∩ U` as the cofiltered `2`-colimit of those over the overlaps `W ∩ U`.** This
is the hypothesis `hoverlap` of the glueing theorems of Stacks 0E90 and Stacks 0E91.

The sole hypothesis is that `U` be retrocompact in `S`, and it is used in exactly one place: the
quasi-compactness of the stages. An overlap `W ∩ U` need not be affine, so quasi-compactness does
not come for free as it does for the neighbourhoods. Quasi-separatedness needs no hypothesis on
`U` at all, every stage being an open subscheme of an affine scheme. Retrocompactness is the
hypothesis Stacks 0E91 states on `U`, so nothing beyond the tag's own assumptions enters. -/
theorem isFinitePresentationColimit_opensSpecStalkSiteCone (s : S) (W₀ : AffineOpenNhds S s)
    (U : S.Opens) (hU : IsRetrocompact (U : Set S)) :
    IsFinitePresentationColimit B S hS (opensSpecStalkSiteDiagram B S hS s W₀ U)
      (opensSpecStalkSiteCone B S hS s W₀ U).pt
      (fun i => (opensSpecStalkSiteCone B S hS s W₀ U).π.app i)
      (fun {_ _} e => (opensSpecStalkSiteCone B S hS s W₀ U).w e) :=
  isFinitePresentationColimit_of_isLimitMapCone B S hS
    (fun {_ _} _ => inferInstance)
    (isLimitMapConeOpensSpecStalkSiteCone B S hS s W₀ U)
    (isQuasiCompactSpace_yoneda_opensSpecStalkSiteDiagram_obj B S hS s W₀ U hU)
    (isAbsolutelyQuasiSeparated_yoneda_opensSpecStalkSiteDiagram_obj B S hS s W₀ U)

end AlgebraicGeometry.FinitePresentationSpacesOver

end
