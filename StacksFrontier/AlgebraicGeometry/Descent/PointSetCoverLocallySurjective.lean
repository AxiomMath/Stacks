module

public import StacksFrontier.AlgebraicGeometry.Descent.StableQuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiCoverSizeBound

/-!
# From a point-set covering to a Zariski covering of the descended sheaf

This is the bridge between the second and the fifth step of the proof of Stacks 02W8. The second
step produces from a chart `g : yoneda.obj V ⟶ G` of a presheaf `G` on the big fppf site of `S` a
family of open subfunctors of `G`: for each open `T ⊆ V` the subfunctor
`AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by the image of `T` in the point space of
`G`. What it proves about the family is that the *point sets* cover, which is
`AlgebraicGeometry.Space.iUnion_image_pointsMap_eq_univ`. The fifth step — the glueing of Tag
01JJ, in the shape of
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff` —
asks instead for local surjectivity of the induced morphism out of the coproduct. This file
upgrades the first statement to the second.

The upgrade is proved directly. The short route would be part (2) of Stacks 03BZ, that a family of
open subspaces is a Zariski covering exactly when its point sets cover; but that part needs
Tag 03H5 for the morphism out of a coproduct of open subspaces, which is not relatively
representable without Tag 02WO. The direct argument instead works one test object at a time. A
section of `G` over an object `c` of the site is a morphism `σ : yoneda.obj c ⟶ G`; the preimages
under `σ` of the members of the point-set covering are open subsets of the point space of
`yoneda.obj c`, hence — the points of a represented presheaf being the points of the representing
scheme — open subschemes of `c`, which cover `c` and so generate a covering sieve of the fppf
topology by `AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion`. Over such a
piece every point of the restricted section lies in the corresponding member of the covering, which
is *verbatim* the defining condition of `AlgebraicGeometry.Space.openSubspaceOfPoints`; so the
restricted section factors through that subfunctor, and hence through its representing object.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_of_range_eq_openSubspaceOfPoints`: **a
  point-set covering of a presheaf by open subfunctors which happen to be representable is a
  Zariski covering in the sense the glueing step consumes.** Given open sets of points `A i`
  covering the point space of `G`, and morphisms `k i : yoneda.obj (W i) ⟶ G` from representables
  whose ranges are the subfunctors cut out by the `A i`, the induced morphism out of the coproduct
  is locally surjective for the fppf topology.
* `AlgebraicGeometry.Space.presheafIsOpenMap_of_isPullback_of_etale` and
  `AlgebraicGeometry.Space.surjective_pointsMap_of_isPullback_of_surjective`: the two properties
  of the chart which the second step needs, for a chart arising as a represented base change of a
  surjective étale morphism of the site. The first is Stacks 01UA: étale implies flat and locally
  of finite presentation, hence universally open, and *that* property is stable under base change,
  which plain openness is not.
* `AlgebraicGeometry.Space.exists_zariskiCover_affineOpens_of_chart`: **the covering of step 2,
  with the index bound step 5 asks for.** For a chart which is surjective on points and an open
  map of schemes after every represented base change, the family indexed by the affine opens of
  the chart gives exactly the data of
  `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff`
  — index cardinality below the cutoff, open immersions, locally surjective coproduct morphism —
  as soon as each of the open subfunctors is representable. The index bound is free:
  `AlgebraicGeometry.Scheme.mk_affineOpens_le_size`.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_representable_openSubspaces`:
  **step 5 of Stacks 02W8 consuming step 2's output.** Effective descent along the surjective
  étale morphisms of the big fppf site of `S` holds for `P` as soon as, for every descent datum
  and every represented base change `g` of the datum's covering morphism to the descended sheaf,
  the open subfunctor cut out by the image of an affine open of `g`'s source is representable. No
  cardinal hypothesis of any kind survives.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_representable_of_quasiCompact`
  is the same statement with the two remaining obligations separated: a hypothesis `hqc` asking
  for the fibre product of the chart with itself inside the site with quasi-compact first
  projection — the affine reduction of Descent, Lemma 35.36.2 — and a hypothesis `H` which is
  handed the full package of step 2, namely the quasi-compact open subscheme of the chart cutting
  out the saturation together with its Cartesian square over the open subfunctor, and owes nothing
  but steps 3 and 4 (Stacks 02LR and Stacks 0247).

## Implementation notes

The core result asks for `Subfunctor.range (k i) = openSubspaceOfPoints B S hS G (A i)` rather
than for an isomorphism onto that subfunctor, because only one inclusion of it is used — a
section whose points all lie in `A i` has to be in the range of `k i` — and because an
isomorphism supplies the equality through `CategoryTheory.Subfunctor.range_comp` and
`CategoryTheory.Subfunctor.range_eq_top`, which is how
`AlgebraicGeometry.Space.exists_zariskiCover_affineOpens_of_chart` feeds representability of the
subfunctor into it.

The covering is indexed by the affine opens of the chart and not by an abstract index type, for
two independent reasons: the index cardinality is then bounded by the chart's size, which is below
the cutoff, so the one remaining hypothesis of
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff`
is discharged; and the members are quasi-compact, which is what the third step of Stacks 02W8
needs of them.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A point-set covering by representable open subfunctors is locally surjective -/

/-- **The covering claim of the second step of Stacks 02W8, as local surjectivity.** Let `A i` be
open sets of points of a presheaf `G` on the big fppf site of `S` whose union is the whole point
space, and suppose that for each `i` the open subfunctor
`AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by `A i` is the range of a morphism
`k i : yoneda.obj (W i) ⟶ G` from a representable presheaf. Then the induced morphism out of the
coproduct of the `yoneda.obj (W i)` is locally surjective for the fppf topology.

This is the hypothesis `hsurj` of `AlgebraicGeometry.isRepresentable_of_zariskiCover_of_size_le`
and of the descent statements built on it, such as
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_size_le`,
obtained from the point-set covering of `AlgebraicGeometry.Space.iUnion_image_pointsMap_eq_univ`.
It replaces part (2) of Stacks 03BZ, which would deduce it from the point-set covering for an
arbitrary family of open subspaces but needs Tag 03H5 for a coproduct of open subspaces, whose
structure morphism is not relatively representable without Tag 02WO.

The proof is a direct one and uses no chart of `G`. A section of `G` over an object `c` of the
site is a morphism `σ : yoneda.obj c ⟶ G`; its point map is continuous
(`AlgebraicGeometry.Space.continuous_pointsMap`, clause (2) of Stacks 03BX), so the preimages of
the `A i` are open sets of points of `yoneda.obj c`, which by clause (1) of Stacks 03BX
(`AlgebraicGeometry.Space.isOpen_pointTopology_yoneda_iff_isOpen_image`) are open subsets of the
scheme `c`. They cover it, and `AlgebraicGeometry.exists_restrict_bigFppfOver` realises each as an
object of the site, so they generate a covering sieve. Over the `i`-th piece every point of the
restricted section is carried into `A i`, which is the defining condition of
`AlgebraicGeometry.Space.openSubspaceOfPoints`; the hypothesis on the range of `k i` then lifts
the restricted section along `k i`. -/
theorem isLocallySurjective_sigmaDesc_of_range_eq_openSubspaceOfPoints
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ι : Type u}
    (A : ι → Set (points B S hS G)) (hAopen : ∀ i, IsOpen (A i))
    (hAcov : ⋃ i, A i = Set.univ)
    {W : ι → BigFppfOver B S hS} (k : ∀ i, yoneda.obj (W i) ⟶ G)
    (hk : ∀ i, Subfunctor.range (k i) = openSubspaceOfPoints B S hS G (A i)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k) := by
  classical
  constructor
  intro c s
  set σ : yoneda.obj c ⟶ G := yonedaEquiv.symm s with hσ
  -- the part of the scheme `c` lying over the `i`-th member of the covering, an open subset
  have hopen : ∀ i, IsOpen (pointsToScheme B S hS c ''
      (pointsMap B S hS (yoneda.obj c) σ ⁻¹' A i)) := fun i =>
    (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS c _).1
      ((hAopen i).preimage (continuous_pointsMap B S hS σ))
  choose d j hj hjrange _ using fun i : ι => exists_restrict_bigFppfOver c
    ⟨pointsToScheme B S hS c '' (pointsMap B S hS (yoneda.obj c) σ ⁻¹' A i), hopen i⟩
  have hjcov : ∀ x : (BigFppfOver.toScheme B S hS).obj c,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j i)) := by
    intro x
    obtain ⟨w, hw⟩ := surjective_pointsToScheme B S hS c x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hAcov ▸ Set.mem_univ
      (pointsMap B S hS (yoneda.obj c) σ w))
    exact ⟨i, by rw [hjrange i]; exact ⟨w, hi, hw⟩⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS j hj hjcov)
  rw [Sieve.generate_le_iff]
  rintro Z z ⟨i⟩
  -- over the `i`-th piece all points of the restricted section lie in `A i`
  have hmem : G.map (j i).op s ∈
      (openSubspaceOfPoints B S hS G (A i)).obj (Opposite.op (d i)) := by
    rw [mem_openSubspaceOfPoints_iff]
    rintro y ⟨v, rfl⟩
    have he : yonedaEquiv.symm (G.map (j i).op s) = yoneda.map (j i) ≫ σ := by
      rw [hσ]; exact yonedaEquiv_symm_map (j i).op s
    rw [he, pointsMap_comp_apply]
    have hw : pointsToScheme B S hS c
        (pointsMap B S hS (yoneda.obj (d i)) (yoneda.map (j i)) v) ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (j i)) := by
      rw [pointsToScheme_pointsMap_yoneda]; exact ⟨_, rfl⟩
    rw [hjrange i] at hw
    obtain ⟨w', hw'mem, hw'eq⟩ := hw
    rwa [injective_pointsToScheme B S hS c hw'eq] at hw'mem
  -- so it lifts along `k i`
  rw [← hk i] at hmem
  obtain ⟨t, ht⟩ := hmem
  refine ⟨(Sigma.ι (fun i => yoneda.obj (W i)) i).app (Opposite.op (d i)) t, ?_⟩
  have h0 : (Sigma.ι (fun i => yoneda.obj (W i)) i ≫ Sigma.desc k).app
      (Opposite.op (d i)) t = (k i).app (Opposite.op (d i)) t := by rw [Sigma.ι_desc]
  simpa only [NatTrans.comp_app, types_comp_apply] using h0.trans ht

/-! ### The two properties of a chart which is a base change of a surjective étale morphism -/

/-- **Stacks 01UA at a chart.** A morphism of presheaves on the big fppf site of `S` which is a
represented base change of `yoneda.map q` for an étale morphism `q` of the site is an open map of
schemes after every represented base change.

This is the hypothesis `hg` of the second step of Stacks 02W8, in the form
`AlgebraicGeometry.Space.isOpen_image_pointsMap_of_isOpen` and
`AlgebraicGeometry.Space.exists_isPullback_ι_openSubspaceOfPoints_image` ask for it. It cannot be
obtained by base-changing plain openness, which is not stable under base change; the detour
through `AlgebraicGeometry.UniversallyOpen` is the content of Stacks 01UA. An étale morphism is
flat and locally of finite presentation by
`AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified`, hence universally open by
`AlgebraicGeometry.UniversallyOpen.of_flat`; the relative form of the
inverse image of `AlgebraicGeometry.UniversallyOpen` *is* stable under base change, and dominates
the relative form of the inverse image of openness. -/
theorem presheafIsOpenMap_of_isPullback_of_etale
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a c : BigFppfOver B S hS}
    {π : G ⟶ yoneda.obj a} {q : c ⟶ a} {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ G}
    {ρ : yoneda.obj V ⟶ yoneda.obj c} (sq : IsPullback g ρ π (yoneda.map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    (MorphismProperty.inverseImage (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g := by
  obtain ⟨hflat, -, hlfp⟩ := Etale.iff_flat_and_formallyUnramified.1 hqe
  have _ : Flat ((BigFppfOver.toScheme B S hS).map q) := hflat
  have _ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) := hlfp
  have hqo : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.UniversallyOpen.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2
      (UniversallyOpen.of_flat _)
  have _ := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.UniversallyOpen.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have hle : (@_root_.AlgebraicGeometry.UniversallyOpen.{u} : MorphismProperty Scheme.{u}) ≤
      (topologically @IsOpenMap : MorphismProperty Scheme.{u}) := fun _ _ k hk =>
    have := hk
    k.isOpenMap
  exact MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) hle) _
    (MorphismProperty.of_isPullback sq.flip hqo)

/-- A morphism of presheaves on the big fppf site of `S` which is a represented base change of
`yoneda.map q` for a surjective morphism `q` of the site is surjective on the point sets of Tag
03BU.

This is the hypothesis `hsurj` of
`AlgebraicGeometry.Space.iUnion_image_pointsMap_eq_univ`. Surjectivity after every represented
base change is stable under base change, and Tag 03MD in the form
`AlgebraicGeometry.Space.isSurjective_of_presheafSurjective` turns it into surjectivity on
points. -/
theorem surjective_pointsMap_of_isPullback_of_surjective
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a c : BigFppfOver B S hS}
    {π : G ⟶ yoneda.obj a} {q : c ⟶ a} {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ G}
    {ρ : yoneda.obj V ⟶ yoneda.obj c} (sq : IsPullback g ρ π (yoneda.map q))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q)) :
    Function.Surjective (pointsMap B S hS (yoneda.obj V) g) := by
  have hqs' : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs
  have _ := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  exact isSurjective_of_presheafSurjective B S hS g
    (MorphismProperty.of_isPullback sq.flip hqs')

/-! ### The covering of step 2, indexed by the affine opens of the chart -/

/-- **The covering of the second step of Stacks 02W8, in the shape the fifth step consumes.** Let
`g : yoneda.obj V ⟶ G` be a chart of a presheaf `G` on the big fppf site of `S` which is
surjective on points and an open map of schemes after every represented base change, and suppose
that for every affine open `T` of `V` the open subfunctor of `G` cut out by the image of `T` in
the point space of `G` is representable. Then `G` admits a Zariski covering by representable open
subfunctors, indexed by a type of cardinality below the site's cutoff, whose induced morphism out
of the coproduct is locally surjective.

The conclusion is verbatim what the hypothesis `H` of
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff`
asks to be produced, with no size hypothesis left on the pieces. The index type is the affine
opens of the chart, so the index bound is `AlgebraicGeometry.Scheme.mk_affineOpens_le_size`
together with the chart being an object of the site; openness of the images is
`AlgebraicGeometry.Space.isOpen_image_pointsMap_of_isOpen`, the point-set covering is
`AlgebraicGeometry.Space.iUnion_image_pointsMap_eq_univ`, the open immersions are
`AlgebraicGeometry.Space.presheaf_isOpenImmersion_ι_openSubspaceOfPoints_image`, and the upgrade
of the point-set covering to local surjectivity is
`AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_of_range_eq_openSubspaceOfPoints`. -/
theorem exists_zariskiCover_affineOpens_of_chart
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS} (g : yoneda.obj V ⟶ G)
    (hg : (MorphismProperty.inverseImage (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V) g))
    (hrep : ∀ T : ((BigFppfOver.toScheme B S hS).obj V).affineOpens,
      (openSubspaceOfPoints B S hS G (pointsMap B S hS (yoneda.obj V) g ''
          (pointsToScheme B S hS V ⁻¹'
            (T : Set _)))).toFunctor.IsRepresentable) :
    ∃ ι : Type u, #ι < B.cutoff ∧
      ∃ (W : ι → BigFppfOver B S hS) (k : ∀ i, yoneda.obj (W i) ⟶ G),
        (∀ i, IsOpenImmersion B S hS (k i)) ∧
          Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k) := by
  classical
  set A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens → Set (points B S hS G) :=
    fun T => pointsMap B S hS (yoneda.obj V) g ''
      (pointsToScheme B S hS V ⁻¹' (T : Set _))
  have hAopen : ∀ T, IsOpen (A T) := fun T =>
    isOpen_image_pointsMap_of_isOpen B S hS g hg T.1.isOpen
  have hAcov : ⋃ T, A T = Set.univ := by
    refine iUnion_image_pointsMap_eq_univ B S hS g hsurj _ ?_
    rw [← TopologicalSpace.Opens.coe_iSup, iSup_affineOpens_eq_top]
    rfl
  have hex : ∀ T, ∃ (Wt : BigFppfOver B S hS) (kt : yoneda.obj Wt ⟶ G),
      IsOpenImmersion B S hS kt ∧
        Subfunctor.range kt = openSubspaceOfPoints B S hS G (A T) := by
    intro T
    have _ := hrep T
    refine ⟨_, (openSubspaceOfPoints B S hS G (A T)).toFunctor.reprW.hom ≫
      (openSubspaceOfPoints B S hS G (A T)).ι, ?_, ?_⟩
    · exact MorphismProperty.RespectsIso.precomp _ _ _
        (presheaf_isOpenImmersion_ι_openSubspaceOfPoints B S hS (A T) (hAopen T))
    · rw [Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top,
        Subfunctor.range_ι]
  choose W k hkoi hkrange using hex
  exact ⟨_, (Scheme.mk_affineOpens_le_size _).trans_lt V.left.property, W, k, hkoi,
    isLocallySurjective_sigmaDesc_of_range_eq_openSubspaceOfPoints B S hS A hAopen hAcov k hkrange⟩

end Chart

/-! ### Step 5 of Stacks 02W8, consuming step 2 -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Step 5 of Stacks 02W8 consuming the output of step 2.** Effective descent along the
surjective étale morphisms of the big fppf site of `S` holds for a morphism property `P` as soon
as the following holds. For every descent datum — a morphism `f : X ⟶ Y` of sheaves, a chart
`h : yoneda.obj a ⟶ Y`, a surjective étale `q : c ⟶ a` and a presentation `(m, r)` of a presheaf
`A` as `X ×[Y] yoneda.obj c` with `r` satisfying `P` relatively — and for every object `U` of the
site presenting `yoneda.obj U` as a base change of `yoneda.map q` along the projection
`X ×[Y] yoneda.obj a ⟶ yoneda.obj a`, and every affine open `T` of `U`, the open subfunctor of
`X ×[Y] yoneda.obj a` cut out by the image of `T` in its point space is representable.

No cardinal hypothesis survives: the index bound of
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff`
is discharged by indexing the covering by the affine opens of the chart, and the uniform size
bound by `AlgebraicGeometry.Space.exists_size_bound_of_descentDatum`.

What is left for the hypothesis is the content of the third and fourth steps of Stacks 02W8 —
Stacks 02LR, that a quasi-compact open of the chart is quasi-affine over the base, and Stacks
0247, that quasi-affine morphisms descend effectively — applied to the quasi-compact open
subscheme of the chart which
`AlgebraicGeometry.Space.exists_isPullback_ι_openSubspaceOfPoints_image` produces, together with
the quasi-compactness of that open subscheme, which
`AlgebraicGeometry.Space.isCompact_preimage_image_pointsMap` supplies from a quasi-compact first
projection of the fibre product of the chart with itself. The variant
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_representable_of_quasiCompact`
separates those two obligations.

The chart is the datum's total space `A`, representable by Tag 03KC because `r` is relatively
representable over the representable `yoneda.obj c`; its two properties are
`AlgebraicGeometry.Space.presheafIsOpenMap_of_isPullback_of_etale`, which is Stacks 01UA, and
`AlgebraicGeometry.Space.surjective_pointsMap_of_isPullback_of_surjective`. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_representable_openSubspaces
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          ∀ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ pullback f h)
            (ρ : yoneda.obj U ⟶ yoneda.obj c),
            IsPullback g ρ (pullback.snd f h) (yoneda.map q) →
            ∀ T : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
              (openSubspaceOfPoints B S hS (pullback f h)
                (pointsMap B S hS (yoneda.obj U) g ''
                  (pointsToScheme B S hS U ⁻¹'
                    (T : Set _)))).toFunctor.IsRepresentable) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  refine isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover_of_mk_lt_cutoff ?_
  intro X Y f hX hY a c h q hqs hqe A m r sq hr
  -- the datum's total space is representable, by Tag 03KC; it is the chart
  have _ : A.IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable r hr.rep
  have sq₂ := sq.of_right' (IsPullback.of_hasPullback f h)
  have sq₃ : IsPullback
      (A.reprW.hom ≫ (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]))
      (A.reprW.hom ≫ r) (pullback.snd f h) (yoneda.map q) :=
    sq₂.of_iso' A.reprW (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  exact exists_zariskiCover_affineOpens_of_chart B S hS _
    (presheafIsOpenMap_of_isPullback_of_etale B S hS sq₃ hqe)
    (surjective_pointsMap_of_isPullback_of_surjective B S hS sq₃ hqs)
    (H f hX hY h q hqs hqe m r sq hr A.reprX _ (A.reprW.hom ≫ r) sq₃)

/-- **Step 5 of Stacks 02W8 consuming step 2, with the two remaining obligations separated.** This
is `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_representable_openSubspaces`
with its single hypothesis split into the two pieces it is made of.

The hypothesis `hqc` asks, for every chart `g` presented as a base change of the datum's covering
morphism, for the fibre product of `g` with itself *inside the site*, with quasi-compact first
projection. In the Stacks Project this comes from the reduction of Descent, Lemma 35.36.2 to
affine `a` and `c`, after which `q` is a morphism of affine schemes and so are all its base
changes.

The hypothesis `H` is then exactly the third and fourth steps of Stacks 02W8 — Stacks 02LR and
Stacks 0247 — since it is handed the entire output of step 2 for each affine open `T` of the
chart: the object `b` of the site with an open immersion `i : b ⟶ U` whose image is the saturation
of `T`, the fact that the saturation is quasi-compact, and the Cartesian square exhibiting `b` as
the part of the chart lying over the open subfunctor. All of it comes from
`AlgebraicGeometry.Space.exists_isPullback_ι_openSubspaceOfPoints_image` and
`AlgebraicGeometry.Space.isCompact_preimage_image_pointsMap`. -/
theorem isEffectiveDescentAlongSurjectiveEtale_of_representable_of_quasiCompact
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hqc : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          ∀ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ pullback f h)
            (ρ : yoneda.obj U ⟶ yoneda.obj c),
            IsPullback g ρ (pullback.snd f h) (yoneda.map q) →
            ∃ (D : BigFppfOver B S hS) (π₁ π₂ : D ⟶ U),
              IsPullback (yoneda.map π₁) (yoneda.map π₂) g g ∧
                QuasiCompact ((BigFppfOver.toScheme B S hS).map π₁))
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          ∀ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ pullback f h)
            (ρ : yoneda.obj U ⟶ yoneda.obj c),
            IsPullback g ρ (pullback.snd f h) (yoneda.map q) →
            ∀ (T : ((BigFppfOver.toScheme B S hS).obj U).affineOpens)
              (b : BigFppfOver B S hS) (i : b ⟶ U)
              (k : yoneda.obj b ⟶ (openSubspaceOfPoints B S hS (pullback f h)
                (pointsMap B S hS (yoneda.obj U) g ''
                  (pointsToScheme B S hS U ⁻¹'
                    (T : Set _)))).toFunctor),
              _root_.AlgebraicGeometry.IsOpenImmersion
                ((BigFppfOver.toScheme B S hS).map i) →
              Set.range ((BigFppfOver.toScheme B S hS).map i) =
                pointsToScheme B S hS U ''
                  (pointsMap B S hS (yoneda.obj U) g ⁻¹'
                    (pointsMap B S hS (yoneda.obj U) g ''
                      (pointsToScheme B S hS U ⁻¹'
                        (T : Set _)))) →
              IsCompact (pointsToScheme B S hS U ''
                (pointsMap B S hS (yoneda.obj U) g ⁻¹'
                  (pointsMap B S hS (yoneda.obj U) g ''
                    (pointsToScheme B S hS U ⁻¹'
                      (T : Set _))))) →
              IsPullback k (yoneda.map i)
                (openSubspaceOfPoints B S hS (pullback f h)
                  (pointsMap B S hS (yoneda.obj U) g ''
                    (pointsToScheme B S hS U ⁻¹'
                      (T : Set _)))).ι g →
                (openSubspaceOfPoints B S hS (pullback f h)
                  (pointsMap B S hS (yoneda.obj U) g ''
                    (pointsToScheme B S hS U ⁻¹'
                      (T : Set _)))).toFunctor.IsRepresentable) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  refine isEffectiveDescentAlongSurjectiveEtale_of_representable_openSubspaces ?_
  intro X Y f hX hY a c h q hqs hqe A m r sq hr U g ρ sqg T
  obtain ⟨D, π₁, π₂, sqD, hπ₁⟩ := hqc f hX hY h q hqs hqe m r sq hr U g ρ sqg
  have hg := presheafIsOpenMap_of_isPullback_of_etale B S hS sqg hqe
  have hTopen : IsOpen (T.1 : Set ((BigFppfOver.toScheme B S hS).obj U)) := T.1.isOpen
  obtain ⟨b, i, kb, hi, hirange, hsqb⟩ :=
    exists_isPullback_ι_openSubspaceOfPoints_image B S hS g hg hTopen
  exact H f hX hY h q hqs hqe m r sq hr U g ρ sqg T b i kb hi hirange
    (isCompact_preimage_image_pointsMap B S hS g sqD hπ₁ hTopen T.2.isCompact) hsqb

end AlgebraicGeometry.Space

end
