module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SplitPushforwardProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSurjectiveDescent
public import StacksCore.Tactic.StacksAttribute

/-!
# The direct image along a finite étale morphism preserves constructible sheaves

**Stacks 095H.** Let `p : T ⟶ S` be a finite étale morphism of a big étale site and let `Λ` be a
Noetherian ring. If `ℱ` is a constructible sheaf of sets, a constructible sheaf of abelian
groups, or a constructible sheaf of `Λ`-modules on `T_étale`, then so is `p_*ℱ` on `S_étale`. No
hypothesis is imposed on `S` or `T`.

The proof is the source's. Constructibility may be checked on an open covering of `S` by
Stacks 095F, so it suffices to treat an affine open of `S`, which is quasi-compact and
quasi-separated. Over such a base, Stacks 04HN makes `p` *split* after an étale base change: every
point of `S` has an étale neighbourhood `V`, with affine underlying scheme and lying in the small
étale site of `S`, over which `p` acquires sheet data. Finitely many such neighbourhoods cover a
quasi-compact `S`, because the image of an étale morphism is open, and their disjoint union `Z` is
an affine object of the site surjecting onto `S`. The restriction of `p_*ℱ` to each neighbourhood
is the direct image of the restriction of `ℱ` along the base change of `p`
(`AlgebraicGeometry.smallEtaleRestrictionPushforwardBaseChangeIso`), which is split, so it is a
finite product of constructible sheaves by
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SplitPushforwardProduct`. Stacks
095F again assembles those into constructibility of the inverse image of `p_*ℱ` on `Z`, and Stacks
095Q descends that along the surjection `Z ⟶ S`.

## Main results

* `Stacks.Etale.IsSplitOver.ofIsPullback` — sheet data for `p` over an `S`-scheme `g : N ⟶ S` is
  sheet data, over the identity of `N`, for the base change of `p` along `g`. This is what turns
  the étale-local trivialization of Stacks 04HN into the hypothesis the split case consumes.
* `AlgebraicGeometry.exists_affine_smallEtale_isSplitOver` — **Stacks 04HN** inside the small
  étale site: an étale neighbourhood with affine underlying scheme, in the site, carrying sheet
  data for `p`.
* `AlgebraicGeometry.exists_affine_etale_surjection` — finitely many such neighbourhoods cover a
  quasi-compact base, and their disjoint union is an affine object of the site surjecting onto it,
  presented as an open covering of that disjoint union.
* `AlgebraicGeometry.isConstructibleFiniteSheaf_smallEtaleRestriction` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_smallEtaleRestriction` — restriction to an object
  of the small étale site preserves constructibility, by Stacks 03S3 and Stacks 095G.
* `AlgebraicGeometry.isConstructibleSetSheaf_restriction_pushforward_of_isSplitOver`,
  `AlgebraicGeometry.isConstructibleAbelianSheaf_restriction_pushforward_of_isSplitOver` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_restriction_pushforward_of_isSplitOver` — the
  étale-local half of the tag: the restriction of `p_*ℱ` to an object of the small étale site of
  `S` over which `p` splits is constructible, at each of the three coefficient categories.
* `AlgebraicGeometry.isConstructibleSetSheaf_pushforward_of_compactSpace`,
  `AlgebraicGeometry.isConstructibleAbelianSheaf_pushforward_of_compactSpace` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_pushforward_of_compactSpace` — the tag over a
  quasi-compact quasi-separated base.
* `AlgebraicGeometry.isConstructibleModuleSheaf_pushforward` — **Stacks 095H**, with no
  hypothesis on `S` or `T`. For sheaves of sets and of abelian groups, with nothing granted, it is
  `AlgebraicGeometry.isConstructibleSetSheaf_pushforward_unconditional` and
  `AlgebraicGeometry.isConstructibleAbelianSheaf_pushforward_unconditional`.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_pushforward` — the special case for sheaves of
  abelian groups with no hypothesis on `S` or `T`, granted Stacks 095Q (2).

## What is granted, and what is not

The sheaves-of-modules statement grants **nothing**: the library's Stacks 095Q for sheaves of
modules, `AlgebraicGeometry.isConstructibleModuleSheaf_pullback_iff_of_surjective`, assumes
nothing beyond surjectivity and quasi-compactness and quasi-separatedness of source and target,
and those are supplied here. The Noetherian hypothesis on `Λ` and the finiteness and étaleness of
`p` are assumed in full and are never dropped.

The sheaves-of-sets and sheaves-of-abelian-groups statements carry **one** hypothesis each,
`AlgebraicGeometry.SetConstructibilityDescendsAlongSurjective` and
`AlgebraicGeometry.AbelianConstructibilityDescendsAlongSurjective`: the converse halves of
Stacks 095Q (1) and Stacks 095Q (2). Neither mentions `p` or `ℱ` — each quantifies over the
surjective morphisms of quasi-compact quasi-separated schemes of `B` and over sheaves on their
targets — so neither can supply the content of the statements below, which is the reduction of
Stacks 095H to Stacks 095Q. They are discharged in the library by
`AlgebraicGeometry.isConstructibleSetSheaf_of_isConstructibleSetSheaf_pullback` and
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_isConstructibleAbelianSheaf_pullback`, which are
themselves stated with granted hypotheses (Stacks 0245 for sets; Stacks 093C for torsion abelian
sheaves, Stacks 03S8 (2) and Stacks 095N for `ℤ`-modules for abelian groups); carrying the descent
statement itself rather than importing those files keeps this file's dependencies to modules that
build, and makes the single thing that is assumed visible in each statement.

## Implementation notes

The spelling subtleties of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SplitPushforwardProduct` recur here:
the underlying scheme of `(smallEtaleBaseChange B p).obj V` is a fibre product under a different
name, and an object `V` of the small étale site agrees with
`AlgebraicGeometry.SmallEtale.ofEtaleHom B V.obj.hom` only by structure eta, so `change` rather
than `show` is used to retype, and the étaleness of a structure morphism is extracted as
`V.property`.

The coefficient universe of the sheaves-of-modules statements is `ModuleCat.{u + 1} Λ` for
`Λ : Type (u + 1)`, which is the one at which Stacks 095Q for modules is available. The
étale-local statements are proved at the more general `ModuleCat.{max (u + 1) w}` of
`SplitPushforwardProduct`, and are applied with explicit universe levels, because the unifier
cannot solve `max (u + 1) ?w =?= u + 1` on its own.

## References

* [Stacks Project, Tag 095H](https://stacks.math.columbia.edu/tag/095H)
* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w r t

namespace Stacks.Etale

/-- Sheet data for `p : P ⟶ S` over an `S`-scheme `g : N ⟶ S` is sheet data for the base change
`b : T ⟶ N` of `p` along `g` over the identity of `N`: the sheets, being sections of `p` over
`S`, lift to sections of `b`. -/
public def IsSplitOver.ofIsPullback {P S N T : AlgebraicGeometry.Scheme.{u}} {p : P ⟶ S}
    {g : N ⟶ S} {a : T ⟶ P} {b : T ⟶ N} (h : IsSplitOver p g)
    (hab : IsPullback a b p g) : IsSplitOver b (𝟙 N) where
  I := h.I
  finite_I := h.finite_I
  sheet i := h.sectionOfIsPullback hab i
  sheet_comp i := h.sectionOfIsPullback_comp_snd hab i
  exists_openCover := by
    intro Z z c hc
    rw [Category.comp_id] at hc
    obtain ⟨κ, Y, pr, hpr, idx, hcov, hfac⟩ :=
      h.exists_openCover z (c ≫ a) (by rw [Category.assoc, hab.w, ← Category.assoc, hc])
    refine ⟨κ, Y, pr, hpr, idx, hcov, fun k => hab.hom_ext ?_ ?_⟩
    · rw [Category.assoc, Category.assoc, Category.assoc,
        h.sectionOfIsPullback_comp_fst hab (idx k), ← Category.assoc]
      exact hfac k
    · rw [Category.assoc, Category.assoc, Category.assoc,
        h.sectionOfIsPullback_comp_snd hab (idx k), Category.comp_id, hc]
  isEmpty_of_sheet_eq := by
    intro Z z i j hij hz
    refine h.isEmpty_of_sheet_eq z hij ?_
    rw [← h.sectionOfIsPullback_comp_fst hab i, ← h.sectionOfIsPullback_comp_fst hab j,
      ← Category.assoc, ← Category.assoc, hz]

end Stacks.Etale

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (p : T ⟶ S)

/-- **Stacks 04HN inside the small étale site.** A finite étale morphism of a big étale site has
sheet data over an étale neighbourhood of any point of its target which is an object of the small
étale site with *affine* underlying scheme. The neighbourhood of `Stacks.Etale.exists_isSplitOver`
is cut down to an affine open containing the distinguished point, which is harmless because sheet
data base changes, and an affine open of a scheme étale over `S` is below the size cutoff of the
site because étale morphisms are locally of finite type. -/
public theorem exists_affine_smallEtale_isSplitOver [IsFinite (B.inclusion.map p)]
    [Etale (B.inclusion.map p)] (s : B.inclusion.obj S) :
    ∃ V : SmallEtale B S.1 S.property,
      IsAffine (B.inclusion.obj V.obj.left) ∧
      s ∈ Set.range (B.inclusion.map V.obj.hom).base ∧
      Nonempty (Stacks.Etale.IsSplitOver (B.inclusion.map p)
        (B.inclusion.map V.obj.hom)) := by
  obtain ⟨W, g, hg, w, hw, ⟨hsp⟩⟩ :=
    Stacks.Etale.exists_isSplitOver (B.inclusion.map p) (𝟙 (B.inclusion.obj S)) s
  have := hg
  rw [Category.comp_id] at hsp
  obtain ⟨i, y, hy⟩ := W.affineOpenCover.openCover.exists_eq w
  have : IsAffine (W.affineOpenCover.openCover.X i) := Scheme.isAffine_affineCover W i
  have : IsOpenImmersion (W.affineOpenCover.openCover.f i) :=
    W.affineOpenCover.openCover.map_prop i
  have hWc : B.Contains (W.affineOpenCover.openCover.X i) :=
    (Scheme.size_le_of_locallyOfFiniteType (W.affineOpenCover.openCover.f i ≫ g)).trans_lt
      S.property
  refine ⟨⟨Over.mk (ObjectProperty.homMk (W.affineOpenCover.openCover.f i ≫ g) :
      B.obj _ hWc ⟶ B.obj S.1 S.property), ?_⟩, ?_, ?_, ⟨hsp.comp _⟩⟩
  · change Etale (W.affineOpenCover.openCover.f i ≫ g)
    infer_instance
  · exact ‹IsAffine (W.affineOpenCover.openCover.X i)›
  · refine ⟨y, ?_⟩
    change g (W.affineOpenCover.openCover.f i y) = s
    rw [hy, hw]

/-- **A quasi-compact scheme of the site is covered by finitely many affine étale objects, whose
disjoint union is again an object of the site.** Given an étale neighbourhood of every point with
affine underlying scheme, finitely many of them already cover, by quasi-compactness and because
the image of an étale morphism is open; their disjoint union is affine, hence quasi-compact and
quasi-separated, and it lies below the size cutoff of the site because the cutoff is closed under
finite coproducts. The components are open subschemes of the disjoint union, which is the shape
Stacks 095F consumes, and the disjoint union surjects onto the base. -/
public theorem exists_affine_etale_surjection (X : B.Scheme)
    (hXc : CompactSpace (B.inclusion.obj X))
    (V : B.inclusion.obj X → SmallEtale B X.1 X.property)
    (hVa : ∀ s, IsAffine (B.inclusion.obj (V s).obj.left))
    (hVm : ∀ s, s ∈ Set.range (B.inclusion.map (V s).obj.hom).base) :
    ∃ (Z : B.Scheme) (g : Z ⟶ X) (ι : Type u) (_ : Finite ι)
      (σ : ι → B.inclusion.obj X) (k : ∀ a, (V (σ a)).obj.left ⟶ Z),
      CompactSpace (B.inclusion.obj Z) ∧ QuasiSeparatedSpace (B.inclusion.obj Z) ∧
        Function.Surjective (B.inclusion.map g).base ∧
        (∀ a, IsOpenImmersion (B.inclusion.map (k a))) ∧
        Set.univ = ⋃ a, Set.range (B.inclusion.map (k a)).base ∧
        ∀ a, k a ≫ g = (V (σ a)).obj.hom := by
  classical
  have := hXc
  have hopen : ∀ s, IsOpen (Set.range (B.inclusion.map (V s).obj.hom).base) := by
    intro s
    have : Etale (B.inclusion.map (V s).obj.hom) := (V s).property
    exact (Scheme.Hom.isOpenMap (B.inclusion.map (V s).obj.hom)).isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun s : B.inclusion.obj X => Set.range (B.inclusion.map (V s).obj.hom).base) hopen
    fun s _ => Set.mem_iUnion.2 ⟨s, hVm s⟩
  set Y : {x // x ∈ t} → Scheme.{u} := fun a => B.inclusion.obj (V a.1).obj.left with hY
  have hYa : ∀ a, IsAffine (Y a) := fun a => hVa a.1
  have : ∀ a, IsAffine (Y a) := hYa
  have hZ : B.Contains (∐ Y) :=
    Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0 Y
      fun a => (V a.1).obj.left.property
  have hrange : ⋃ a, Set.range (B.inclusion.map (V (a : {x // x ∈ t}).1).obj.hom).base
      = Set.univ := by
    refine Set.univ_subset_iff.1 fun x _ => ?_
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Set.mem_iUnion.2 ⟨⟨s, hs⟩, hx⟩
  have hsurj : Function.Surjective
      (Limits.Sigma.desc fun a => B.inclusion.map (V (a : {x // x ∈ t}).1).obj.hom).base :=
    (Surjective.sigmaDesc_of_union_range_eq_univ hrange).1
  refine ⟨B.obj _ hZ, ObjectProperty.homMk
      (Limits.Sigma.desc fun a => B.inclusion.map (V (a : {x // x ∈ t}).1).obj.hom),
    {x // x ∈ t}, inferInstance, Subtype.val,
    fun a => ObjectProperty.homMk (Limits.Sigma.ι Y a), ?_, ?_, hsurj, ?_, ?_, ?_⟩
  · exact Scheme.compactSpace_of_isAffine (∐ Y)
  · exact quasiSeparatedSpace_of_isAffine (∐ Y)
  · exact fun a => inferInstanceAs (IsOpenImmersion (Limits.Sigma.ι Y a))
  · exact ((sigmaOpenCover Y).iUnion_range).symm
  · intro a
    apply B.inclusion.map_injective
    rw [Functor.map_comp]
    exact Limits.Sigma.ι_comp_desc _ _

section Restriction

variable {D : Type w} [Category.{v} D] {FD : D → D → Type*} {CD : D → Type t}
  [∀ A A', FunLike (FD A A') (CD A) (CD A')] [ConcreteCategory.{t} D FD]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) D]

/-- **Restriction to an object of the small étale site preserves constructibility.** By Stacks
03S3 restriction along the structure morphism of `V` is the inverse image along it, and Stacks
095G says that inverse image preserves constructibility. -/
public theorem isConstructibleFiniteSheaf_smallEtaleRestriction (X : B.Scheme)
    (V : SmallEtale B X.1 X.property)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) D)
    (hF : IsConstructibleFiniteSheaf B X F) :
    IsConstructibleFiniteSheaf B V.obj.left
      (((smallEtalePostcompose B X.1 X.property V).sheafPushforwardContinuous D
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
        (SmallEtale.topology B X.1 X.property)).obj F) :=
  have : Etale (B.inclusion.map V.obj.hom) := V.property
  isConstructibleFiniteSheaf_congr B V.obj.left
    ((smallInverseImageIsoPostcomposePushforward B V.obj.hom D).app F)
    (isConstructibleFiniteSheaf_pullback B V.obj.hom F hF)

end Restriction

section EtaleLocal

variable [Etale (B.inclusion.map p)]

/-- **The direct image along a finite étale morphism is constructible after restriction to an
object of the small étale site over which the morphism splits, sheaves of sets.** The restriction
of the direct image is the direct image of the restriction, by
`AlgebraicGeometry.smallEtaleRestrictionPushforwardBaseChangeIso`; the base change of `p` to `V`
is split by `Stacks.Etale.IsSplitOver.ofIsPullback`, and the restriction of the sheaf is
constructible by Stacks 095G, so the split case
`AlgebraicGeometry.isConstructibleSetSheaf_splitPushforward` applies. -/
public theorem isConstructibleSetSheaf_restriction_pushforward_of_isSplitOver
    (V : SmallEtale B S.1 S.property)
    (hsp : Stacks.Etale.IsSplitOver (B.inclusion.map p) (B.inclusion.map V.obj.hom))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B T F) :
    IsConstructibleSetSheaf B V.obj.left
      (((smallEtalePostcompose B S.1 S.property V).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
        (SmallEtale.topology B S.1 S.property)).obj
          ((B.smallPushforward p (Type (u + 1))).obj F)) := by
  have hEt : Etale (B.inclusion.map (baseChangedEtaleProjection B p V)) :=
    MorphismProperty.of_isPullback (isPullback_splitBaseChange B p V) inferInstance
  refine isConstructibleSetSheaf_congr B V.obj.left
    ((smallEtaleRestrictionPushforwardBaseChangeIso B p V (Type (u + 1))).app F) ?_
  exact isConstructibleSetSheaf_splitPushforward B (baseChangedEtaleProjection B p V)
    (hsp.ofIsPullback (isPullback_splitBaseChange B p V)) _
    (isConstructibleFiniteSheaf_smallEtaleRestriction B T
      ((smallEtaleBaseChange B p).obj V) F hF)

/-- **The direct image along a finite étale morphism is constructible after restriction to an
object of the small étale site over which the morphism splits, sheaves of abelian groups.** The
argument is that of
`AlgebraicGeometry.isConstructibleSetSheaf_restriction_pushforward_of_isSplitOver`, with
`AlgebraicGeometry.isConstructibleAbelianSheaf_splitPushforward` for the split case. -/
public theorem isConstructibleAbelianSheaf_restriction_pushforward_of_isSplitOver
    (V : SmallEtale B S.1 S.property)
    (hsp : Stacks.Etale.IsSplitOver (B.inclusion.map p) (B.inclusion.map V.obj.hom))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B T F) :
    IsConstructibleAbelianSheaf B V.obj.left
      (((smallEtalePostcompose B S.1 S.property V).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
        (SmallEtale.topology B S.1 S.property)).obj
          ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj F)) := by
  have hEt : Etale (B.inclusion.map (baseChangedEtaleProjection B p V)) :=
    MorphismProperty.of_isPullback (isPullback_splitBaseChange B p V) inferInstance
  refine isConstructibleAbelianSheaf_congr B V.obj.left
    ((smallEtaleRestrictionPushforwardBaseChangeIso B p V AddCommGrpCat.{u + 1}).app F) ?_
  exact isConstructibleAbelianSheaf_splitPushforward B (baseChangedEtaleProjection B p V)
    (hsp.ofIsPullback (isPullback_splitBaseChange B p V)) _
    (isConstructibleFiniteSheaf_smallEtaleRestriction B T
      ((smallEtaleBaseChange B p).obj V) F hF)

section Modules

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) w} Λ)]

omit [IsNoetherianRing Λ] in
/-- **Restriction to an object of the small étale site preserves constructibility of sheaves of
modules over a Noetherian ring.** By Stacks 03S3 restriction along the structure morphism of `V`
is the inverse image along it, and Stacks 095G for modules over a Noetherian ring says that
inverse image preserves constructibility. -/
public theorem isConstructibleModuleSheaf_smallEtaleRestriction (X : B.Scheme)
    (V : SmallEtale B X.1 X.property)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) w} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F) :
    IsConstructibleModuleSheaf B V.obj.left Λ
      (((smallEtalePostcompose B X.1 X.property V).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
        (SmallEtale.topology B X.1 X.property)).obj F) :=
  have : Etale (B.inclusion.map V.obj.hom) := V.property
  isConstructibleModuleSheaf_congr B Λ V.obj.left
    ((smallInverseImageIsoPostcomposePushforward B V.obj.hom
      (ModuleCat.{max (u + 1) w} Λ)).app F)
    (isConstructibleModuleSheaf_pullback B Λ V.obj.hom F hF)

/-- **The direct image along a finite étale morphism is constructible after restriction to an
object of the small étale site over which the morphism splits, sheaves of modules over a
Noetherian ring.** The argument is that of
`AlgebraicGeometry.isConstructibleSetSheaf_restriction_pushforward_of_isSplitOver`, with
`AlgebraicGeometry.isConstructibleModuleSheaf_splitPushforward` for the split case. The
Noetherian hypothesis on `Λ` is the one carried by
`AlgebraicGeometry.IsConstructibleModuleSheaf` itself and is not dropped. -/
public theorem isConstructibleModuleSheaf_restriction_pushforward_of_isSplitOver
    (V : SmallEtale B S.1 S.property)
    (hsp : Stacks.Etale.IsSplitOver (B.inclusion.map p) (B.inclusion.map V.obj.hom))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{max (u + 1) w} Λ))
    (hF : IsConstructibleModuleSheaf B T Λ F) :
    IsConstructibleModuleSheaf B V.obj.left Λ
      (((smallEtalePostcompose B S.1 S.property V).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
        (SmallEtale.topology B S.1 S.property)).obj
          ((B.smallPushforward p (ModuleCat.{max (u + 1) w} Λ)).obj F)) := by
  have hEt : Etale (B.inclusion.map (baseChangedEtaleProjection B p V)) :=
    MorphismProperty.of_isPullback (isPullback_splitBaseChange B p V) inferInstance
  refine isConstructibleModuleSheaf_congr B Λ V.obj.left
    ((smallEtaleRestrictionPushforwardBaseChangeIso B p V
      (ModuleCat.{max (u + 1) w} Λ)).app F) ?_
  exact isConstructibleModuleSheaf_splitPushforward B (baseChangedEtaleProjection B p V) Λ
    (hsp.ofIsPullback (isPullback_splitBaseChange B p V)) _
    (isConstructibleModuleSheaf_smallEtaleRestriction B Λ T
      ((smallEtaleBaseChange B p).obj V) F hF)

end Modules

end EtaleLocal

/-- The affine open subschemes of an object of the site form a Zariski cover by objects of its
small étale site. -/
private theorem exists_affine_openCover_smallEtale (X : B.Scheme) :
    ∃ (ι : Type u) (W : ι → SmallEtale B X.1 X.property),
      (∀ i, IsAffine (B.inclusion.obj (W i).obj.left)) ∧
      (∀ i, IsOpenImmersion (B.inclusion.map (W i).obj.hom)) ∧
      Set.univ = ⋃ i, Set.range (B.inclusion.map (W i).obj.hom).base := by
  have hUopen : ∀ i, IsOpenImmersion ((B.inclusion.obj X).affineOpenCover.openCover.f i) :=
    fun i => (B.inclusion.obj X).affineOpenCover.openCover.map_prop i
  have hUc : ∀ i, B.Contains ((B.inclusion.obj X).affineOpenCover.openCover.X i) := fun i =>
    have := hUopen i
    Scheme.size_lt_of_isOpenImmersion ((B.inclusion.obj X).affineOpenCover.openCover.f i)
      X.property
  refine ⟨_, fun i => ⟨Over.mk (ObjectProperty.homMk
      ((B.inclusion.obj X).affineOpenCover.openCover.f i) :
        B.obj _ (hUc i) ⟶ B.obj X.1 X.property), ?_⟩,
    fun i => Scheme.isAffine_affineCover (B.inclusion.obj X) i, hUopen,
    ((B.inclusion.obj X).affineOpenCover.openCover.iUnion_range).symm⟩
  have := hUopen i
  change Etale ((B.inclusion.obj X).affineOpenCover.openCover.f i)
  infer_instance

section ModuleDescent

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks 095H for sheaves of modules over a Noetherian ring, over a quasi-compact and
quasi-separated base.** Let `p : T ⟶ S` be a finite étale morphism of a big étale site with `S`
quasi-compact and quasi-separated, let `Λ` be a Noetherian ring and let `ℱ` be a constructible
sheaf of `Λ`-modules on `T_étale`. Then `p_*ℱ` is constructible.

Nothing is granted. By Stacks 04HN, in the form
`AlgebraicGeometry.exists_affine_smallEtale_isSplitOver`, every point of `S` has an affine étale
neighbourhood `V` in the small étale site of `S` over which `p` becomes split; finitely many of
those cover `S`, and their disjoint union `Z` is an affine object of the site surjecting onto `S`
(`AlgebraicGeometry.exists_affine_etale_surjection`). The restriction of `p_*ℱ` to each `V` is
constructible by
`AlgebraicGeometry.isConstructibleModuleSheaf_restriction_pushforward_of_isSplitOver`; the `V`
are open subschemes covering `Z`, so Stacks 095F makes the inverse image of `p_*ℱ` on `Z`
constructible; and Stacks 095Q for sheaves of modules, which assumes nothing beyond
surjectivity and quasi-compactness and quasi-separatedness of `Z` and `S`, descends that to
`S`. -/
@[sga "4 IX 2.14" "(i), special case"]
public theorem isConstructibleModuleSheaf_pushforward_of_compactSpace
    [IsFinite (B.inclusion.map p)] [Etale (B.inclusion.map p)]
    (hSc : CompactSpace (B.inclusion.obj S)) (hSq : QuasiSeparatedSpace (B.inclusion.obj S))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B T Λ F) :
    IsConstructibleModuleSheaf B S Λ
      ((B.smallPushforward p (ModuleCat.{u + 1} Λ)).obj F) := by
  classical
  choose V hVa hVm hVsp using fun s => exists_affine_smallEtale_isSplitOver B p s
  obtain ⟨Z, g, ι, hι, σ, k, hZc, hZq, hgsurj, hko, hkcover, hkg⟩ :=
    exists_affine_etale_surjection B S hSc V hVa hVm
  have := hι
  have hpull : IsConstructibleModuleSheaf B Z Λ
      ((B.smallInverseImage g (ModuleCat.{u + 1} Λ)).obj
        ((B.smallPushforward p (ModuleCat.{u + 1} Λ)).obj F)) := by
    refine isConstructibleModuleSheaf_of_openCover B Λ Z _
      (fun a => (V (σ a)).obj.left) k hko hkcover fun a => ?_
    refine isConstructibleModuleSheaf_congr B Λ _
      (((smallEtaleSheafPullbackCompIso B _ _ _ (k a) g (ModuleCat.{u + 1} Λ)).app
        ((B.smallPushforward p (ModuleCat.{u + 1} Λ)).obj F)).symm) ?_
    rw [hkg a]
    have hEt : Etale (B.inclusion.map (V (σ a)).obj.hom) := (V (σ a)).property
    exact isConstructibleModuleSheaf_congr B Λ _
      ((smallInverseImageIsoPostcomposePushforward B (V (σ a)).obj.hom
        (ModuleCat.{u + 1} Λ)).app _).symm
      (isConstructibleModuleSheaf_restriction_pushforward_of_isSplitOver.{u, u + 1, u + 1}
          B p Λ (V (σ a))
        (hVsp (σ a)).some F hF)
  exact (isConstructibleModuleSheaf_pullback_iff_of_surjective B Λ g hSc hSq hZc hZq
    hgsurj _).2 hpull

/-- **Stacks 095H for sheaves of modules over a Noetherian ring.** Let `p : T ⟶ S` be a finite
étale morphism of a big étale site, let `Λ` be a Noetherian ring and let `ℱ` be a constructible
sheaf of `Λ`-modules on `T_étale`. Then `p_*ℱ` is a constructible sheaf of `Λ`-modules on
`S_étale`. No hypothesis is imposed on `S` or `T`, and nothing is granted.

By Stacks 095F constructibility may be checked on an open covering of `S`, and the affine opens
of `S` are such a covering; the restriction of `p_*ℱ` to an affine open `U` is the direct image,
along the base change of `p` to `U`, of the restriction of `ℱ`
(`AlgebraicGeometry.smallEtaleRestrictionPushforwardBaseChangeIso`), that base change is again
finite étale, the restriction of `ℱ` is constructible by Stacks 095G, and `U` is quasi-compact
and quasi-separated, so
`AlgebraicGeometry.isConstructibleModuleSheaf_pushforward_of_compactSpace` applies. -/
@[stacks 095H "sheaves of modules over a Noetherian ring; nothing granted, no hypothesis on S or T",
  sga "4 IX 2.14" "(i), special case",
  sga "5 I 1.14" "b)"]
public theorem isConstructibleModuleSheaf_pushforward
    [IsFinite (B.inclusion.map p)] [Etale (B.inclusion.map p)]
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B T Λ F) :
    IsConstructibleModuleSheaf B S Λ
      ((B.smallPushforward p (ModuleCat.{u + 1} Λ)).obj F) := by
  classical
  obtain ⟨ι, W, hWa, hWo, hWc⟩ := exists_affine_openCover_smallEtale B S
  refine isConstructibleModuleSheaf_of_openCover B Λ S _
    (fun i => (W i).obj.left) (fun i => (W i).obj.hom) hWo hWc fun i => ?_
  have hEtW : Etale (B.inclusion.map (W i).obj.hom) := (W i).property
  have : IsFinite (B.inclusion.map (baseChangedEtaleProjection B p (W i))) :=
    MorphismProperty.of_isPullback (isPullback_splitBaseChange B p (W i)) inferInstance
  have : Etale (B.inclusion.map (baseChangedEtaleProjection B p (W i))) :=
    MorphismProperty.of_isPullback (isPullback_splitBaseChange B p (W i)) inferInstance
  have := hWa i
  refine isConstructibleModuleSheaf_congr B Λ _
    ((smallInverseImageIsoPostcomposePushforward B (W i).obj.hom
      (ModuleCat.{u + 1} Λ)).app _).symm ?_
  refine isConstructibleModuleSheaf_congr B Λ _
    ((smallEtaleRestrictionPushforwardBaseChangeIso B p (W i)
      (ModuleCat.{u + 1} Λ)).app F) ?_
  exact isConstructibleModuleSheaf_pushforward_of_compactSpace B
    (baseChangedEtaleProjection B p (W i)) Λ
    (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _) _
    (isConstructibleModuleSheaf_smallEtaleRestriction.{u, u + 1, u + 1} B Λ T
      ((smallEtaleBaseChange B p).obj (W i)) F hF)

end ModuleDescent

section SetDescent

/-- **Stacks 095Q (1) as a hypothesis.** Constructibility of a sheaf of sets on the small étale
site descends along a surjective morphism of quasi-compact quasi-separated schemes of `B`: if the
inverse image of `ℱ` along such a morphism is constructible then so is `ℱ`.

This is exactly the converse half of Stacks 095Q (1). It mentions neither the finite étale
morphism nor the sheaf of Stacks 095H, so it cannot supply the content of the statements below. -/
public def SetConstructibilityDescendsAlongSurjective (B : BigEtaleSite.{u}) : Prop :=
  ∀ (X Y : B.Scheme) (f : X ⟶ Y), Function.Surjective (B.inclusion.map f).base →
    CompactSpace (B.inclusion.obj X) → QuasiSeparatedSpace (B.inclusion.obj X) →
    CompactSpace (B.inclusion.obj Y) → QuasiSeparatedSpace (B.inclusion.obj Y) →
    ∀ G : Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1)),
      IsConstructibleSetSheaf B X ((B.smallInverseImage f (Type (u + 1))).obj G) →
        IsConstructibleSetSheaf B Y G

/-- **Stacks 095Q (2) as a hypothesis.** Constructibility of an abelian sheaf on the small étale
site descends along a surjective morphism of quasi-compact quasi-separated schemes of `B`.

This is exactly the converse half of Stacks 095Q (2), with no torsion hypothesis. It mentions
neither the finite étale morphism nor the sheaf of Stacks 095H. -/
public def AbelianConstructibilityDescendsAlongSurjective (B : BigEtaleSite.{u}) : Prop :=
  ∀ (X Y : B.Scheme) (f : X ⟶ Y), Function.Surjective (B.inclusion.map f).base →
    CompactSpace (B.inclusion.obj X) → QuasiSeparatedSpace (B.inclusion.obj X) →
    CompactSpace (B.inclusion.obj Y) → QuasiSeparatedSpace (B.inclusion.obj Y) →
    ∀ G : Sheaf (SmallEtale.topology B Y.1 Y.property) AddCommGrpCat.{u + 1},
      IsConstructibleAbelianSheaf B X
          ((B.smallInverseImage f AddCommGrpCat.{u + 1}).obj G) →
        IsConstructibleAbelianSheaf B Y G

/-- **Stacks 095H for sheaves of sets, over a quasi-compact and quasi-separated base.** Let
`p : T ⟶ S` be a finite étale morphism of a big étale site with `S` quasi-compact and
quasi-separated and let `ℱ` be a constructible sheaf of sets on `T_étale`. Then `p_*ℱ` is
constructible.

The argument is that of
`AlgebraicGeometry.isConstructibleModuleSheaf_pushforward_of_compactSpace`: Stacks 04HN provides
an affine étale neighbourhood of every point of `S` over which `p` splits, finitely many of them
cover, their disjoint union `Z` is affine and surjects onto `S`, the restriction of `p_*ℱ` to
each neighbourhood is constructible by
`AlgebraicGeometry.isConstructibleSetSheaf_restriction_pushforward_of_isSplitOver`, and Stacks
095F assembles that into constructibility of the inverse image of `p_*ℱ` on `Z`.

Stacks 095Q (1) is carried as the hypothesis `h095Q`, in the form
`AlgebraicGeometry.SetConstructibilityDescendsAlongSurjective`. It is discharged in the library
by `AlgebraicGeometry.isConstructibleSetSheaf_of_isConstructibleSetSheaf_pullback`, and mentions
neither `p` nor `ℱ`. -/
public theorem isConstructibleSetSheaf_pushforward_of_compactSpace
    [IsFinite (B.inclusion.map p)] [Etale (B.inclusion.map p)]
    (hSc : CompactSpace (B.inclusion.obj S)) (hSq : QuasiSeparatedSpace (B.inclusion.obj S))
    (h095Q : SetConstructibilityDescendsAlongSurjective B)
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B T F) :
    IsConstructibleSetSheaf B S ((B.smallPushforward p (Type (u + 1))).obj F) := by
  classical
  choose V hVa hVm hVsp using fun s => exists_affine_smallEtale_isSplitOver B p s
  obtain ⟨Z, g, ι, hι, σ, k, hZc, hZq, hgsurj, hko, hkcover, hkg⟩ :=
    exists_affine_etale_surjection B S hSc V hVa hVm
  have := hι
  refine h095Q Z S g hgsurj hZc hZq hSc hSq _ ?_
  refine isConstructibleFiniteSheaf_of_openCover B Z _
    (fun a => (V (σ a)).obj.left) k hko hkcover fun a => ?_
  refine isConstructibleSetSheaf_congr B _
    (((smallEtaleSheafPullbackCompIso B _ _ _ (k a) g (Type (u + 1))).app
      ((B.smallPushforward p (Type (u + 1))).obj F)).symm) ?_
  rw [hkg a]
  have hEt : Etale (B.inclusion.map (V (σ a)).obj.hom) := (V (σ a)).property
  exact isConstructibleSetSheaf_congr B _
    ((smallInverseImageIsoPostcomposePushforward B (V (σ a)).obj.hom
      (Type (u + 1))).app _).symm
    (isConstructibleSetSheaf_restriction_pushforward_of_isSplitOver B p (V (σ a))
      (hVsp (σ a)).some F hF)

/-- **Stacks 095H for sheaves of abelian groups, over a quasi-compact and quasi-separated
base.** The argument is that of
`AlgebraicGeometry.isConstructibleSetSheaf_pushforward_of_compactSpace`, with
`AlgebraicGeometry.isConstructibleAbelianSheaf_restriction_pushforward_of_isSplitOver` for the
split case and Stacks 095Q (2) carried as the hypothesis `h095Q`, in the form
`AlgebraicGeometry.AbelianConstructibilityDescendsAlongSurjective`. No torsion hypothesis is
imposed on `ℱ`. -/
public theorem isConstructibleAbelianSheaf_pushforward_of_compactSpace
    [IsFinite (B.inclusion.map p)] [Etale (B.inclusion.map p)]
    (hSc : CompactSpace (B.inclusion.obj S)) (hSq : QuasiSeparatedSpace (B.inclusion.obj S))
    (h095Q : AbelianConstructibilityDescendsAlongSurjective B)
    (F : Sheaf (SmallEtale.topology B T.1 T.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B T F) :
    IsConstructibleAbelianSheaf B S
      ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj F) := by
  classical
  choose V hVa hVm hVsp using fun s => exists_affine_smallEtale_isSplitOver B p s
  obtain ⟨Z, g, ι, hι, σ, k, hZc, hZq, hgsurj, hko, hkcover, hkg⟩ :=
    exists_affine_etale_surjection B S hSc V hVa hVm
  have := hι
  refine h095Q Z S g hgsurj hZc hZq hSc hSq _ ?_
  refine isConstructibleFiniteSheaf_of_openCover B Z _
    (fun a => (V (σ a)).obj.left) k hko hkcover fun a => ?_
  refine isConstructibleAbelianSheaf_congr B _
    (((smallEtaleSheafPullbackCompIso B _ _ _ (k a) g AddCommGrpCat.{u + 1}).app
      ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj F)).symm) ?_
  rw [hkg a]
  have hEt : Etale (B.inclusion.map (V (σ a)).obj.hom) := (V (σ a)).property
  exact isConstructibleAbelianSheaf_congr B _
    ((smallInverseImageIsoPostcomposePushforward B (V (σ a)).obj.hom
      AddCommGrpCat.{u + 1}).app _).symm
    (isConstructibleAbelianSheaf_restriction_pushforward_of_isSplitOver B p (V (σ a))
      (hVsp (σ a)).some F hF)

/-- **A special case of Stacks 095H for sheaves of abelian groups, granted Stacks 095Q (2).** Let
`p : T ⟶ S` be a finite étale morphism of a big étale site and let `ℱ` be a constructible abelian
sheaf on `T_étale`. Then `p_*ℱ` is a constructible abelian sheaf on `S_étale`. No hypothesis is
imposed on `S` or `T`, and no torsion hypothesis on `ℱ`. The statement with nothing granted, which
carries the tag, is `AlgebraicGeometry.isConstructibleAbelianSheaf_pushforward_unconditional`.

The Zariski reduction is that of
`AlgebraicGeometry.isConstructibleSetSheaf_pushforward_unconditional`, and
Stacks 095Q (2) is carried as the hypothesis `h095Q`, which quantifies over all morphisms of the
site. -/
public theorem isConstructibleAbelianSheaf_pushforward
    [IsFinite (B.inclusion.map p)] [Etale (B.inclusion.map p)]
    (h095Q : AbelianConstructibilityDescendsAlongSurjective B)
    (F : Sheaf (SmallEtale.topology B T.1 T.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B T F) :
    IsConstructibleAbelianSheaf B S
      ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj F) := by
  classical
  obtain ⟨ι, W, hWa, hWo, hWc⟩ := exists_affine_openCover_smallEtale B S
  refine isConstructibleFiniteSheaf_of_openCover B S _
    (fun i => (W i).obj.left) (fun i => (W i).obj.hom) hWo hWc fun i => ?_
  have hEtW : Etale (B.inclusion.map (W i).obj.hom) := (W i).property
  have : IsFinite (B.inclusion.map (baseChangedEtaleProjection B p (W i))) :=
    MorphismProperty.of_isPullback (isPullback_splitBaseChange B p (W i)) inferInstance
  have : Etale (B.inclusion.map (baseChangedEtaleProjection B p (W i))) :=
    MorphismProperty.of_isPullback (isPullback_splitBaseChange B p (W i)) inferInstance
  have := hWa i
  refine isConstructibleAbelianSheaf_congr B _
    ((smallInverseImageIsoPostcomposePushforward B (W i).obj.hom
      AddCommGrpCat.{u + 1}).app _).symm ?_
  refine isConstructibleAbelianSheaf_congr B _
    ((smallEtaleRestrictionPushforwardBaseChangeIso B p (W i)
      AddCommGrpCat.{u + 1}).app F) ?_
  exact isConstructibleAbelianSheaf_pushforward_of_compactSpace B
    (baseChangedEtaleProjection B p (W i))
    (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _) h095Q _
    (isConstructibleFiniteSheaf_smallEtaleRestriction B T
      ((smallEtaleBaseChange B p).obj (W i)) F hF)

end SetDescent

end AlgebraicGeometry

end
