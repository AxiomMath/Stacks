module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAtlas02WR
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteGluingBySize
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# Gluing algebraic spaces along an open covering, with no bound on the index type

`StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAtlas02WR` proves Stacks 02WR for an index type
carrying `#I < B.cutoff.ord.cof`. That bound is not part of the source, and it is not needed for
the atlas clause; it is inherited from
`AlgebraicGeometry.Space.isRepresentable_of_locally_covering`, which puts the glued scheme into
the site by bounding the number of charts. This file removes it, using instead the size-based
gluing step `AlgebraicGeometry.Space.isRepresentable_of_locally_covering_of_le_power`, whose
hypothesis is a uniform bound on the charts.

Two observations do it. First, a covering family may be *thinned* before it is glued: the
coproduct `G` is assumed to be an algebraic space, so it has a chart `U`, and the members whose
traces on `U` already cover `U` still cover `G`, because the chart is locally surjective. The
affine opens of `U` refine that trace covering, so the thinned family is indexed by a type of
cardinality at most `size U` -- a bound by `B.cutoff`, which is what the size-based gluing step
consumes, and not by `B.cutoff.ord.cof`, which is what the old one needed. Second, the charts of
both glued objects are uniformly bounded by a single object of the site:

* for the covering map, the charts are open subschemes of the test object `V`;
* for the diagonal, the charts are the base changes `T ×_G Fᵢ` of the members along the single
  object `T` of the site representing `(V ×_F W) ×_F G`, so they are open subschemes of `T`.

`T` exists because `G` has a representable diagonal and both `V ×_F G` and `W ×_F G` are
representable -- the latter by the covering-map clause, which is therefore proved first.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.sheafify_iSup_range_subfamily`: a subfamily of a family of
  relatively representable open immersions whose traces on a chart cover the chart still covers.
  This is the thinning step.
* `AlgebraicGeometry.Space.exists_subfamily_le_size`: the thinned family may be taken to be
  indexed by a type of cardinality at most the size of the chart.
* `AlgebraicGeometry.Space.isLocallySurjective_of_presheaf_surjective_etale`: a surjective étale
  chart is locally surjective. This is Stacks 05VM with its single morphism property assembled
  from the two carried by `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_openCover_of_isAlgebraicSpace` and
  `AlgebraicGeometry.Space.relativelyRepresentable_diag_of_openCover_of_isAlgebraicSpace`:
  `AlgebraicGeometry.Space.relativelyRepresentable_of_openCover` and
  `AlgebraicGeometry.Space.relativelyRepresentable_diag_of_openCover` with the bound on the
  index type removed.

## Implementation notes

The source states 02WR for an arbitrary index type, so the generality is needed here. It is
supplied upstream: `AlgebraicGeometry.Space.sheafify_iSup_range_hom_of_isColimit` and
`AlgebraicGeometry.Space.exists_mem_range_snd_of_sheafify_iSup` state the covering input at an
arbitrary index universe, the second with the covering hypothesis in place of the colimit,
which is all its proof uses.

The diagonal clause no longer uses that the members are algebraic spaces. Its charts used to be
the fibre products `Aᵢ ×_{Fᵢ} Bᵢ`, which need the diagonal of the member to be representable and
whose size is governed by that diagonal, so they admit no bound in terms of `V` and `W`: a fibre
product over an algebraic space is not a fibre product of schemes, and
`AlgebraicGeometry.Scheme.size_pullback_le` does not apply to it. Taking the charts to be
`T ×_G Fᵢ` instead replaces the member's diagonal by the diagonal of `G` and bounds every chart
by `T` at once. The hypothesis that each member is an algebraic space is unused by the diagonal
clause, and is retained in it because it is a hypothesis of the source.

Every implicit argument of
`AlgebraicGeometry.Space.isRepresentable_of_locally_covering_of_le_power` is supplied explicitly
at each use site, as in `AlgebraicGeometry.Space.relativelyRepresentable_of_isFinite`: leaving
them to be inferred spends more than the default heartbeat budget on a single `isDefEq`.

## References

* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Thinning a covering family against a chart -/

/-- **A subfamily whose traces on a chart cover the chart still covers.** Let `c` be a family of
relatively representable open immersions into `G` and let `a : yoneda.obj V ⟶ G` be a locally
surjective chart of `G`. A subfamily indexed through `ii : J → I` whose represented pullbacks
along `a` are jointly surjective on the points of `V` again has sheafified supremum of ranges
the whole of `G`.

A section of `G` comes, on a covering sieve, from a morphism to `V`; the pullbacks of the
subfamily are an open covering of `V`, hence a covering family of the site, and pulling it back
along that morphism refines the sieve to one on which the section factors through a member. -/
theorem sheafify_iSup_range_subfamily
    {I : Type v} {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : ∀ i, Ci i ⟶ G}
    (hc : ∀ i, (openImmersionOver B S hS).presheaf (c i))
    {V : BigFppfOver B S hS} (a : yoneda.obj V ⟶ G)
    (ha : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a)
    {J : Type u} (ii : J → I)
    (hJ : ∀ y : (BigFppfOver.toScheme B S hS).obj V,
      ∃ j, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hc (ii j)).rep.snd a)).base) :
    (⨆ j, Subfunctor.range (c (ii j))).sheafify (BigFppfOver.topology B S hS) = ⊤ := by
  classical
  have hVcov : Sieve.ofArrows (fun j => (hc (ii j)).rep.pullback a)
      (fun j => (hc (ii j)).rep.snd a) ∈ BigFppfOver.topology B S hS V :=
    BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B S hS _ V _
      (fun j => (hc (ii j)).property_snd a) hJ
  rw [eq_top_iff]
  intro T t _
  change (⨆ j, Subfunctor.range (c (ii j))).sieveOfSection t ∈
    BigFppfOver.topology B S hS (unop T)
  refine (BigFppfOver.topology B S hS).transitive (Presheaf.imageSieve_mem _ a t) _ ?_
  rintro Z f ⟨s, hs⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).pullback_stable s hVcov)
  rintro Y₀ e ⟨W₀, h, _, ⟨j⟩, hfac⟩
  change G.map (e ≫ f).op t ∈ (⨆ j, Subfunctor.range (c (ii j))).obj (op Y₀)
  rw [Subfunctor.iSup_obj]
  refine Set.mem_iUnion.2 ⟨j, yonedaEquiv (yoneda.map h ≫ (hc (ii j)).rep.fst a), ?_⟩
  have key : yonedaEquiv (yoneda.map h ≫ (hc (ii j)).rep.fst a ≫ c (ii j)) =
      (c (ii j)).app (op Y₀) (yonedaEquiv (yoneda.map h ≫ (hc (ii j)).rep.fst a)) := by
    rw [← Category.assoc, yonedaEquiv_comp]
  have hcomp : yonedaEquiv (yoneda.map (e ≫ s) ≫ a) =
      a.app (op Y₀) ((yoneda.obj V).map e.op s) := by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    rfl
  rw [← key, ((hc (ii j)).rep.isPullback a).w, ← Category.assoc,
    ← Functor.map_comp, hfac, hcomp,
    NatTrans.naturality_apply a e.op s, hs, ← ConcreteCategory.comp_apply,
    ← G.map_comp, ← op_comp]

/-- **A covering family may be thinned to one indexed by the size of a chart.** Of a family of
relatively representable open immersions whose represented pullbacks along `a` cover the chart
`V`, a subfamily indexed by a type of cardinality at most `size V` already does: the affine
opens of `V` refine the covering, and there are at most `size V` of them.

The resulting bound is a bound by `B.cutoff`, which is what
`AlgebraicGeometry.Space.isRepresentable_of_locally_covering_of_le_power` consumes, and not by
`B.cutoff.ord.cof`. -/
theorem exists_subfamily_le_size
    {I : Type v} {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : ∀ i, Ci i ⟶ G}
    (hc : ∀ i, (openImmersionOver B S hS).presheaf (c i))
    {V : BigFppfOver B S hS} (a : yoneda.obj V ⟶ G)
    (hI : ∀ y : (BigFppfOver.toScheme B S hS).obj V,
      ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hc i).rep.snd a)).base) :
    ∃ (J : Type u) (ii : J → I),
      #J ≤ ((BigFppfOver.toScheme B S hS).obj V).size ∧
      ∀ y : (BigFppfOver.toScheme B S hS).obj V,
        ∃ j, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hc (ii j)).rep.snd a)).base := by
  classical
  have hropen : ∀ i, IsOpen (Set.range
      ((BigFppfOver.toScheme B S hS).map ((hc i).rep.snd a)).base) := by
    intro i
    have h : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map ((hc i).rep.snd a)) := (hc i).property_snd a
    exact h.base_open.isOpen_range
  refine ⟨{W : ((BigFppfOver.toScheme B S hS).obj V).affineOpens //
      ∃ i, (W.1 : Set ((BigFppfOver.toScheme B S hS).obj V)) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map ((hc i).rep.snd a)).base},
    fun j => j.2.choose,
    (Cardinal.mk_subtype_le _).trans
      (Scheme.mk_affineOpens_le_size ((BigFppfOver.toScheme B S hS).obj V)), fun y => ?_⟩
  obtain ⟨i, hi⟩ := hI y
  obtain ⟨-, ⟨W, hW, rfl⟩, hyV, hVle⟩ :=
    (Scheme.isBasis_affineOpens ((BigFppfOver.toScheme B S hS).obj V)).exists_subset_of_mem_open
      hi (hropen i)
  exact ⟨⟨⟨W, hW⟩, i, hVle⟩, (⟨⟨W, hW⟩, i, hVle⟩ :
    {W : ((BigFppfOver.toScheme B S hS).obj V).affineOpens //
      ∃ i, (W.1 : Set ((BigFppfOver.toScheme B S hS).obj V)) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map ((hc i).rep.snd a)).base}).2.choose_spec hyV⟩

/-! ### Local surjectivity of an atlas -/

/-- **An atlas is locally surjective.** A relatively representable morphism from a representable
presheaf whose represented base changes are surjective and étale is locally surjective for the
fppf topology: étale morphisms are flat and locally of finite presentation, so Stacks 05VM
applies. Both properties are applied to the same base-change square, so no two choices of
represented pullback have to be compared. -/
theorem isLocallySurjective_of_presheaf_surjective_etale
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} {V : BigFppfOver B S hS}
    {a : yoneda.obj V ⟶ G.obj}
    (hsurjA : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (hetA : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  have hprop : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((fun _ _ f => _root_.AlgebraicGeometry.Flat f ∧
          _root_.AlgebraicGeometry.LocallyOfFinitePresentation f ∧
          _root_.AlgebraicGeometry.Surjective f) : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a := by
    refine ⟨hetA.rep, fun A A' ζ fst snd sq => ?_⟩
    have h1 : _root_.AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map snd) := hetA.property ζ fst snd sq
    obtain ⟨hflat, -, hlfp⟩ :=
      _root_.AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.1 h1
    exact ⟨hflat, hlfp, hsurjA.property ζ fst snd sq⟩
  exact isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
    B S hS (⟨a⟩ : (BigFppfOver.topology B S hS).yoneda.obj V ⟶ G) hprop

/-! ### The two representability clauses, with no bound on the index type -/

/-- The thinned family and the bound on its index type, from an atlas of the coproduct. -/
private theorem exists_subfamily_covering_of_isAlgebraicSpace
    {I : Type v} {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (jj : ∀ i, Fi i ⟶ G) (hcoprod : IsColimit (Cofan.mk G jj))
    (hG : IsAlgebraicSpace B S hS G.obj) :
    ∃ (U : BigFppfOver B S hS) (J : Type u) (ii : J → I),
      #J ≤ ((BigFppfOver.toScheme B S hS).obj U).size ∧
      (⨆ j, Subfunctor.range (jj (ii j)).hom).sheafify (BigFppfOver.topology B S hS) = ⊤ := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  have hopenj : ∀ i, (openImmersionOver B S hS).presheaf (jj i).hom := fun i =>
    isOpenImmersion_coproductInj B S hS I Fi G jj hcoprod i
  obtain ⟨U, atl, hsurjA, hetA⟩ := hG.exists_atlas
  have hlsA : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) atl :=
    isLocallySurjective_of_presheaf_surjective_etale B S hS hsurjA hetA
  obtain ⟨J, ii, hJcard, hJsurj⟩ := exists_subfamily_le_size B S hS hopenj atl
    (exists_mem_range_snd_of_sheafify_iSup B S hS hopenj
      (sheafify_iSup_range_hom_of_isColimit B S hS jj hcoprod) atl)
  exact ⟨U, J, ii, hJcard, sheafify_iSup_range_subfamily B S hS hopenj atl hlsA ii hJsurj⟩

/-- The base change of an open immersion along a map from `V` is no larger than `V`. -/
private theorem size_pullback_le_of_openImmersion
    {Ci G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : Ci ⟶ G}
    (hc : (openImmersionOver B S hS).presheaf c) {V : BigFppfOver B S hS}
    (a : yoneda.obj V ⟶ G) :
    ((BigFppfOver.toScheme B S hS).obj (hc.rep.pullback a)).size ≤
      ((BigFppfOver.toScheme B S hS).obj V).size := by
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hc.rep.snd a)) := hc.property_snd a
  exact Scheme.size_le_of_mono_locallyOfFinitePresentation
    ((BigFppfOver.toScheme B S hS).map (hc.rep.snd a))

/-- Gluing with a uniform size bound, where the bound is the larger of two objects `U` and `T`. -/
private theorem isRepresentable_of_locally_covering_of_size_le
    {K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type u}
    {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : ∀ i, Ci i ⟶ K)
    (hcov : (⨆ i, Subfunctor.range (c i)).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (hopen : ∀ i, (openImmersionOver B S hS).presheaf (c i))
    (H : Sheaf (BigFppfOver.topology B S hS) (Type u)) (h : H.obj ⟶ K)
    {X : I → BigFppfOver B S hS}
    (p : ∀ i, yoneda.obj (X i) ⟶ H.obj) (q : ∀ i, yoneda.obj (X i) ⟶ Ci i)
    (hp : ∀ i, IsPullback (p i) (q i) h (c i)) (U T : BigFppfOver B S hS)
    (hIU : #I ≤ ((BigFppfOver.toScheme B S hS).obj U).size)
    (hX : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤
      ((BigFppfOver.toScheme B S hS).obj T).size) :
    H.obj.IsRepresentable := by
  rcases le_total ((BigFppfOver.toScheme B S hS).obj U).size
      ((BigFppfOver.toScheme B S hS).obj T).size with hle | hle
  · exact isRepresentable_of_locally_covering_of_le_power B S hS (K := K) (I := I)
      (Ci := Ci) c hcov hopen H h (X := X) p q hp
      (T := (BigFppfOver.toScheme B S hS).obj T) T.left.property
      ((hIU.trans hle).trans (Cardinal.self_le_power _ one_le_aleph0))
      (fun j => (hX j).trans (Cardinal.self_le_power _ one_le_aleph0))
  · exact isRepresentable_of_locally_covering_of_le_power B S hS (K := K) (I := I)
      (Ci := Ci) c hcov hopen H h (X := X) p q hp
      (T := (BigFppfOver.toScheme B S hS).obj U) U.left.property
      (hIU.trans (Cardinal.self_le_power _ one_le_aleph0))
      (fun j => ((hX j).trans hle).trans (Cardinal.self_le_power _ one_le_aleph0))

/-- **Stacks 02WR, representability of the covering map, with no bound on the index type.** The
map from the coproduct of the members of the cover to `F` is relatively representable.

This is `AlgebraicGeometry.Space.relativelyRepresentable_of_openCover` with the hypothesis
`#I < B.cutoff.ord.cof` removed, at the cost of assuming that the coproduct is an algebraic
space -- which is hypothesis (2)(e) of the source, so no hypothesis is added to Stacks 02WR. The
covering family is thinned against a chart of the coproduct, and the charts of the glued object
are open subschemes of the test object. -/
theorem relativelyRepresentable_of_openCover_of_isAlgebraicSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {I : Type v} {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (jj : ∀ i, Fi i ⟶ G) (hcoprod : IsColimit (Cofan.mk G jj))
    (g : G.obj ⟶ F)
    (hopen : ∀ i, (openImmersionOver B S hS).presheaf ((jj i).hom ≫ g))
    (hG : IsAlgebraicSpace B S hS G.obj) :
    yoneda.relativelyRepresentable g := by
  classical
  let _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  have hopenj : ∀ i, (openImmersionOver B S hS).presheaf (jj i).hom := fun i =>
    isOpenImmersion_coproductInj B S hS I Fi G jj hcoprod i
  obtain ⟨U, J, ii, hJcard, hcovG⟩ := exists_subfamily_covering_of_isAlgebraicSpace B S hS jj
    hcoprod hG
  rw [yoneda_relativelyRepresentable_iff_pullback_representable]
  intro V ξ
  set γ : yoneda.obj V ⟶ F := yonedaEquiv.symm ξ
  let Fs : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨F, hF⟩
  let γs : (BigFppfOver.topology B S hS).yoneda.obj V ⟶ Fs := ⟨γ⟩
  let gs : G ⟶ Fs := ⟨g⟩
  let H := pullback γs gs
  let fstH : H.obj ⟶ yoneda.obj V := (pullback.fst γs gs).hom
  let sndH : H.obj ⟶ G.obj := (pullback.snd γs gs).hom
  have hH : IsPullback fstH sndH γ g :=
    (IsPullback.of_hasPullback γs gs).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
  have hdata : ∀ j : J, ∃ (Z : BigFppfOver B S hS) (p₀ : yoneda.obj Z ⟶ H.obj)
      (q₀ : yoneda.obj Z ⟶ (Fi (ii j)).obj),
      IsPullback p₀ q₀ sndH (jj (ii j)).hom ∧
        ((BigFppfOver.toScheme B S hS).obj Z).size ≤
          ((BigFppfOver.toScheme B S hS).obj V).size := by
    intro j
    have hsq : IsPullback ((hopen (ii j)).rep.fst γ)
        (yoneda.map ((hopen (ii j)).rep.snd γ)) ((jj (ii j)).hom ≫ g) γ :=
      (hopen (ii j)).rep.isPullback γ
    have hc : yoneda.map ((hopen (ii j)).rep.snd γ) ≫ γ =
        ((hopen (ii j)).rep.fst γ ≫ (jj (ii j)).hom) ≫ g := by
      rw [Category.assoc]; exact hsq.w.symm
    let p₀ : yoneda.obj ((hopen (ii j)).rep.pullback γ) ⟶ H.obj :=
      hH.lift (yoneda.map ((hopen (ii j)).rep.snd γ))
        ((hopen (ii j)).rep.fst γ ≫ (jj (ii j)).hom) hc
    have hps : p₀ ≫ sndH = (hopen (ii j)).rep.fst γ ≫ (jj (ii j)).hom := hH.lift_snd _ _ _
    rw [← hH.lift_fst (yoneda.map ((hopen (ii j)).rep.snd γ))
      ((hopen (ii j)).rep.fst γ ≫ (jj (ii j)).hom) hc] at hsq
    exact ⟨_, p₀, (hopen (ii j)).rep.fst γ,
      (IsPullback.of_bot hsq hps.symm hH.flip).flip,
      size_pullback_le_of_openImmersion B S hS (hopen (ii j)) γ⟩
  choose X p q hp hsize using hdata
  have hrep : H.obj.IsRepresentable :=
    isRepresentable_of_locally_covering_of_size_le B S hS (fun j => (jj (ii j)).hom) hcovG
      (fun j => hopenj (ii j)) H sndH p q hp U V hJcard hsize
  let _ := hrep
  exact isRepresentable_of_natIso H.obj hH.isoPullback

/-- **Stacks 02WR, representability of the diagonal, with no bound on the index type.** An fppf
sheaf with a locally surjective coproduct decomposition into subfunctors by representable open
immersions, whose coproduct is an algebraic space, has a representable diagonal.

This is `AlgebraicGeometry.Space.relativelyRepresentable_diag_of_openCover` with the hypothesis
`#I < B.cutoff.ord.cof` removed and the hypothesis that each member is an algebraic space
dropped: the fibre product `V ×_F W` is covered by the base changes of the members along the
object `T` of the site representing `(V ×_F W) ×_F G`, which exists because `G` has a
representable diagonal and `V ×_F G` and `W ×_F G` are representable. Each chart is then an open
subscheme of `T`, which bounds them all at once; the members' own diagonals are not used. -/
theorem relativelyRepresentable_diag_of_openCover_of_isAlgebraicSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {I : Type v} {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (jj : ∀ i, Fi i ⟶ G) (hcoprod : IsColimit (Cofan.mk G jj))
    (g : G.obj ⟶ F)
    (hopen : ∀ i, (openImmersionOver B S hS).presheaf ((jj i).hom ≫ g))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g)
    (hG : IsAlgebraicSpace B S hS G.obj) :
    yoneda.relativelyRepresentable (diag F) := by
  classical
  let _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  let _ := B.hasPullbacks_schemes
  let _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have hgrep : yoneda.relativelyRepresentable g :=
    relativelyRepresentable_of_openCover_of_isAlgebraicSpace B S hS hF jj hcoprod g hopen hG
  have hopenj : ∀ i, (openImmersionOver B S hS).presheaf (jj i).hom := fun i =>
    isOpenImmersion_coproductInj B S hS I Fi G jj hcoprod i
  obtain ⟨U, J, ii, hJcard, hcovG⟩ := exists_subfamily_covering_of_isAlgebraicSpace B S hS jj
    hcoprod hG
  have hcovF : (⨆ j, Subfunctor.range ((jj (ii j)).hom ≫ g)).sheafify
      (BigFppfOver.topology B S hS) = ⊤ :=
    sheafify_iSup_range_comp B S hS (fun j => (jj (ii j)).hom) g hcovG hsurj
  refine ((yoneda_relativelyRepresentable_diag_tfae F).out 3 1).1 ?_
  intro V W ξ ξ'
  set α : yoneda.obj V ⟶ F := yonedaEquiv.symm ξ
  set β : yoneda.obj W ⟶ F := yonedaEquiv.symm ξ'
  let Fs : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨F, hF⟩
  let αs : (BigFppfOver.topology B S hS).yoneda.obj V ⟶ Fs := ⟨α⟩
  let βs : (BigFppfOver.topology B S hS).yoneda.obj W ⟶ Fs := ⟨β⟩
  let H := pullback αs βs
  let fstH : H.obj ⟶ yoneda.obj V := (pullback.fst αs βs).hom
  let sndH : H.obj ⟶ yoneda.obj W := (pullback.snd αs βs).hom
  have hH : IsPullback fstH sndH α β :=
    (IsPullback.of_hasPullback αs βs).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
  -- the object of the site representing `(V ×_F W) ×_F G`, which bounds every chart
  obtain ⟨T₀, s₀, t₀, hT₀⟩ :=
    (Functor.relativelyRepresentable.diag_iff.1 hG.diagonal_representable
      (hgrep.fst α)) (hgrep.fst β)
  have hA := hT₀.paste_vert (hgrep.isPullback β)
  have hcompat : (t₀ ≫ yoneda.map (hgrep.snd α)) ≫ α =
      (yoneda.map s₀ ≫ yoneda.map (hgrep.snd β)) ≫ β := by
    rw [Category.assoc, ← (hgrep.isPullback α).w]
    exact hA.w
  let ρ : yoneda.obj T₀ ⟶ H.obj :=
    hH.lift (t₀ ≫ yoneda.map (hgrep.snd α))
      (yoneda.map s₀ ≫ yoneda.map (hgrep.snd β)) hcompat
  have hρfst : ρ ≫ fstH = t₀ ≫ yoneda.map (hgrep.snd α) := hH.lift_fst _ _ _
  have hρsnd : ρ ≫ sndH = yoneda.map s₀ ≫ yoneda.map (hgrep.snd β) := hH.lift_snd _ _ _
  have hA' : IsPullback t₀ (ρ ≫ sndH) (yoneda.map (hgrep.snd α) ≫ α) β := by
    rw [hρsnd, ← (hgrep.isPullback α).w]
    exact hA
  have hT0H : IsPullback ρ (t₀ ≫ hgrep.fst α) (fstH ≫ α) g :=
    (IsPullback.of_bot hA' hρfst.symm hH).flip.paste_vert (hgrep.isPullback α).flip
  have hdata : ∀ j : J, ∃ (Z : BigFppfOver B S hS) (p₀ : yoneda.obj Z ⟶ H.obj)
      (q₀ : yoneda.obj Z ⟶ (Fi (ii j)).obj),
      IsPullback p₀ q₀ (fstH ≫ α) ((jj (ii j)).hom ≫ g) ∧
        ((BigFppfOver.toScheme B S hS).obj Z).size ≤
          ((BigFppfOver.toScheme B S hS).obj T₀).size := by
    intro j
    exact ⟨_, yoneda.map ((hopenj (ii j)).rep.snd (t₀ ≫ hgrep.fst α)) ≫ ρ,
      (hopenj (ii j)).rep.fst (t₀ ≫ hgrep.fst α),
      (((hopenj (ii j)).rep.isPullback (t₀ ≫ hgrep.fst α)).paste_vert hT0H.flip).flip,
      size_pullback_le_of_openImmersion B S hS (hopenj (ii j)) (t₀ ≫ hgrep.fst α)⟩
  choose X p q hp hsize using hdata
  have hrep : H.obj.IsRepresentable :=
    isRepresentable_of_locally_covering_of_size_le B S hS (fun j => (jj (ii j)).hom ≫ g) hcovF
      (fun j => hopen (ii j)) H (fstH ≫ α) p q hp U T₀ hJcard hsize
  let _ := hrep
  exact isRepresentable_of_natIso H.obj hH.isoPullback

end AlgebraicGeometry.Space

end
