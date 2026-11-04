module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreePullbackChartShrink
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreePullbackChartTarget

/-!
# Shrinking the comparison of `b^*N` with `𝒢` over the preimage of the open carrying a section

Over the open `V` on which `b` is invertible the chart comparison of the essential surjectivity
half of [Stacks, Tag 0EXD] is `AlgebraicGeometry.pullbackSectionChartIso`, and it mentions neither
a free module nor `α`:  the restriction of `N` to `V` is identified with the inverse image of `𝒢`
along the section `AlgebraicGeometry.freeChartBaseSection` of `b`, and the inverse image along
`b ∣_ V` undoes that section.  This file shrinks it, which is the second of the two chart shrinks
the glueing of `b^*N ≅ 𝒢` needs; the first is
`AlgebraicGeometry.restrictChartIso_pullbackFreeTrivIso`.

## The route

It is the route of
`StacksFrontier/AlgebraicGeometry/FiniteLocallyFree/BlowUpFreePullbackChartShrink.lean`, with one
factor replaced.  Both chart comparisons are, in the inverse-image world, the square comparison
`AlgebraicGeometry.pullbackPreimageSquareIso` cut out by the open, followed by the inverse image of
a trivialisation of `N` there, followed by a comparison that leaves the inverse-image world; so
both are shrunk by `Stacks.AlgebraicGeometry.ModuleLimits.trivShrink_of_paste`, with the *same*
paste law `AlgebraicGeometry.pullbackPreimageSquareIso_shrink`.  Only the last factor differs:
for the free chart it is `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso`, and what the shrink
costs is its pseudo-functoriality; here it is the comparison undoing the section, and what the
shrink costs is the pseudo-functoriality of *that*.

So the content of this file is the general comparison
`AlgebraicGeometry.pullbackRestrictObjIso` -- the inverse image along `g` of a restriction along
`p` is the restriction along `g ≫ p` -- of which the comparison undoing the section is an
instance, and its pseudo-functoriality
`AlgebraicGeometry.pullbackRestrictObjIso_comp`.  The two instances the shrink needs are the
section itself and the fact, `AlgebraicGeometry.homOfLE_comp_freeChartBaseSection`, that the
section over `V'` is the restriction of the section over `V`.

## Implementation notes

Nothing in this file mentions a free module on a scheme, so -- unlike the free chart -- the
transparency obstruction recorded in
`StacksFrontier/AlgebraicGeometry/FiniteLocallyFree/RestrictFreeIsoComp.lean` does not arise and the
general lemmas are proved by `rw` and `simp`.  The two chart-level statements are nevertheless in
term mode, for a different reason:  they are reassociations of a composite of six, which
`AlgebraicGeometry.comp_reassoc₆` settles directly and a rewrite would only reach by unfolding
every `CategoryTheory.Iso.trans` in sight.

Both the hypothesis and the conclusion of the shrink are stated as
`... ≪≫ (restrictCompIso ...).symm = ...` rather than `... = ... ≪≫ restrictCompIso ...`:  taking
`CategoryTheory.Iso.hom` of the first shape gives exactly an equation between
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE`s, which is what
`Stacks.AlgebraicGeometry.ModuleLimits.nonempty_iso_of_cover_of_inf` consumes, with no further
algebra.

## Main definitions

* `AlgebraicGeometry.pullbackRestrictObjIso`: **the inverse image along `g` of the restriction of
  `G` along an open immersion `p` is the restriction of `G` along `g ≫ p`.**
* `AlgebraicGeometry.pullbackSectionChartPullbackIso`: the chart comparison over the preimage of
  `V`, entirely in the inverse-image world.

## Main results

* `AlgebraicGeometry.pullbackSectionRestrictIso_eq`: the comparison undoing the section is an
  instance of the general one.
* `AlgebraicGeometry.restrictFunctorIsoPullback_app_trans_pullbackRestrictObjIso`: the general
  comparison along an open immersion is the comparison of the two restrictions.
* `AlgebraicGeometry.pullbackRestrictObjIso_comp`: **the general comparison is
  pseudo-functorial**, with every composite kept as a variable.
* `AlgebraicGeometry.pullbackSectionChartIso_eq`, and
  `AlgebraicGeometry.pullbackSectionChartPullbackIso_shrink`: the chart comparison in the
  inverse-image world, and its cocycle condition.
* `AlgebraicGeometry.restrictChartIso_pullbackSectionChartIso`: **the comparison over the preimage
  of `V` is compatible with shrinking `V`.**

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The inverse image of a restriction -/

/-- **The inverse image along `g` of the restriction of `G` along an open immersion `p` is the
restriction of `G` along the composite.**  Both are the inverse image of `G` along `g ≫ p`, the
passage between restriction and inverse image at the two ends being
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
def pullbackRestrictObjIso {A B S : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ S) [IsOpenImmersion p]
    {k : A ⟶ S} (hk : g ≫ p = k) [IsOpenImmersion k] (G : S.Modules) :
    (Scheme.Modules.pullback g).obj (Scheme.Modules.restrict G p) ≅
      Scheme.Modules.restrict G k :=
  (Scheme.Modules.pullback g).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback p).app G) ≪≫
    pullbackCompIsoOfEq g p hk G ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback k).app G).symm

/-- **The comparison undoing the section of `b` over `V` is the general comparison of
`AlgebraicGeometry.pullbackRestrictObjIso`**, at the section and the restricted morphism. -/
theorem pullbackSectionRestrictIso_eq {X X' : Scheme.{u}} (b : X' ⟶ X) {V : X.Opens}
    [IsIso (b ∣_ V)] (G : X'.Modules) :
    pullbackSectionRestrictIso b G =
      pullbackRestrictObjIso (b ∣_ V) (freeChartBaseSection b V)
        (morphismRestrict_comp_freeChartBaseSection b) G :=
  rfl

/-- **The comparison of `AlgebraicGeometry.pullbackRestrictObjIso` along an open immersion is the
comparison of the two restrictions.**  Read backwards:  the identification of the restriction
along `g ≫ p` with the restriction along `g` of the restriction along `p` is the passage to the
inverse image followed by the comparison. -/
theorem restrictFunctorIsoPullback_app_trans_pullbackRestrictObjIso {A B S : Scheme.{u}}
    (g : A ⟶ B) (p : B ⟶ S) [IsOpenImmersion g] [IsOpenImmersion p] {k : A ⟶ S}
    (hk : g ≫ p = k) [IsOpenImmersion k] (G : S.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback g).app (Scheme.Modules.restrict G p) ≪≫
        pullbackRestrictObjIso g p hk G = (restrictCompIso g p hk G).symm := by
  have hcoh := NatTrans.congr_app
    (Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_comp_of_eq g p hk) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hcoh
  have key : (Scheme.Modules.restrictFunctor g).map
        ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app G) ≫
      (Scheme.Modules.restrictFunctorIsoPullback g).hom.app
          ((Scheme.Modules.pullback p).obj G) ≫ (pullbackCompIsoOfEq g p hk G).hom =
      (restrictCompIso g p hk G).inv ≫
        (Scheme.Modules.restrictFunctorIsoPullback k).hom.app G := by
    rw [show (restrictCompIso g p hk G).inv =
        (Scheme.Modules.restrictFunctorComp g p).inv.app G ≫
          (Scheme.Modules.restrictFunctorCongr hk).hom.app G from rfl, pullbackCompIsoOfEq]
    simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
    exact hcoh.symm
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback g).hom.naturality
    ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app G)
  refine Iso.ext ?_
  simp only [pullbackRestrictObjIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv]
  rw [← reassoc_of% hnat, reassoc_of% key, Iso.hom_inv_id_app, Category.comp_id]

/-- **`AlgebraicGeometry.pullbackRestrictObjIso` is pseudo-functorial, with every composite kept
as a variable.**  Taking the inverse image along `c` of the comparison for `g` and comparing again
is contracting the iterated inverse image and comparing once.

This is the pentagon `AlgebraicGeometry.modulesPullbackTriangleIso_pentagon_app` together with
the naturality of the contraction; keeping `k`, `k'` and `m` variables is what lets the two routes
of a shrink, which present the one morphism `A' ⟶ S` as two different composites, be compared. -/
theorem pullbackRestrictObjIso_comp {A' A B S : Scheme.{u}} (c : A' ⟶ A) (g : A ⟶ B) (p : B ⟶ S)
    [IsOpenImmersion p] {k : A ⟶ S} (hk : g ≫ p = k) [IsOpenImmersion k] {k' : A' ⟶ S}
    (hk2 : c ≫ k = k') [IsOpenImmersion k'] {m : A' ⟶ B} (hm : c ≫ g = m) (hm2 : m ≫ p = k')
    (G : S.Modules) :
    (Scheme.Modules.pullback c).map (pullbackRestrictObjIso g p hk G).hom ≫
        (pullbackRestrictObjIso c k hk2 G).hom =
      (pullbackCompIsoOfEq c g hm (Scheme.Modules.restrict G p)).hom ≫
        (pullbackRestrictObjIso m p hm2 G).hom := by
  have pent := modulesPullbackTriangleIso_pentagon_app c g p m k k' hm hk hk2 hm2 G
  have hnat := (modulesPullbackTriangleIso c g m hm).hom.naturality
    ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app G)
  dsimp only [Functor.comp_map] at hnat
  simp only [pullbackRestrictObjIso, pullbackCompIsoOfEq_eq, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    CategoryTheory.Functor.map_comp]
  rw [← reassoc_of% pent, reassoc_of% hnat]

/-! ### The section chart comparison and its shrink -/

variable {X X' : Scheme.{u}} (b : X' ⟶ X) {G : X'.Modules}

/-- **The restriction of `b` to `V`, shrunk to a smaller `V'`, followed by the section of `b` over
`V`, is the inclusion of the preimage of `V'`.**  This is
`AlgebraicGeometry.morphismRestrict_comp_freeChartBaseSection` preceded by the inclusion of the
preimages. -/
theorem homOfLE_comp_morphismRestrict_comp_freeChartBaseSection {V V' : X.Opens} (hV : V' ≤ V)
    [IsIso (b ∣_ V)] :
    (X'.homOfLE (b.preimage_mono hV) ≫ (b ∣_ V)) ≫ freeChartBaseSection b V =
      (b ⁻¹ᵁ V').ι := by
  rw [Category.assoc, morphismRestrict_comp_freeChartBaseSection, Scheme.homOfLE_ι]

/-- **The comparison of `b^*N` with `𝒢` over the preimage of `V`, in the inverse-image world.**
This is `AlgebraicGeometry.pullbackSectionChartIso` with its source read as an inverse image
rather than a restriction, and with the identification of `N|_V` with the inverse image of `𝒢`
along the section given on the inverse image too. -/
def pullbackSectionChartPullbackIso {V : X.Opens} [IsIso (b ∣_ V)] (N : X.Modules)
    (σ : (Scheme.Modules.pullback V.ι).obj N ≅
      Scheme.Modules.restrict G (freeChartBaseSection b V)) :
    (Scheme.Modules.pullback (b ⁻¹ᵁ V).ι).obj ((Scheme.Modules.pullback b).obj N) ≅
      Scheme.Modules.restrict G (b ⁻¹ᵁ V).ι :=
  pullbackPreimageSquareIso b V N ≪≫
    (Scheme.Modules.pullback (b ∣_ V)).mapIso σ ≪≫
    pullbackSectionRestrictIso b G

/-- **The comparison over the preimage of `V` is the identification of the restriction with the
inverse image followed by the inverse-image comparison.**  Both sides are the same six
comparisons in the same order, bracketed differently; the proof is the reassociation in term
mode, as in `AlgebraicGeometry.pullbackFreeTrivIso_eq`. -/
theorem pullbackSectionChartIso_eq {V : X.Opens} [IsIso (b ∣_ V)] (N : X.Modules)
    (σ : Scheme.Modules.restrict N V.ι ≅
      Scheme.Modules.restrict G (freeChartBaseSection b V)) :
    pullbackSectionChartIso b N σ =
      (Scheme.Modules.restrictFunctorIsoPullback (b ⁻¹ᵁ V).ι).app
          ((Scheme.Modules.pullback b).obj N) ≪≫
        pullbackSectionChartPullbackIso b N
          (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).symm ≪≫ σ) :=
  Iso.ext ((comp_reassoc₆ _ _ _ _ _ _).trans
    (congrArg (fun z =>
      (Scheme.Modules.restrictFunctorIsoPullback (b ⁻¹ᵁ V).ι).hom.app
          ((Scheme.Modules.pullback b).obj N) ≫
        ((pullbackCompIsoOfEq (b ⁻¹ᵁ V).ι b (morphismRestrict_ι b V).symm N).hom ≫
            (pullbackCompIsoOfEq (b ∣_ V) V.ι rfl N).inv) ≫
          z ≫ (pullbackSectionRestrictIso b G).hom)
      ((Scheme.Modules.pullback (b ∣_ V)).map_comp
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).inv σ.hom).symm))

/-- **The inverse-image comparison over the preimage of `V` shrinks to the one over the preimage
of a smaller `V'`**, provided the two identifications of `N` with the inverse image of `𝒢` along
the section are compatible.

This is the cocycle condition that `AlgebraicGeometry.restrictChartIso_pullback_trans` asks for,
and it is `Stacks.AlgebraicGeometry.ModuleLimits.trivShrink_of_paste` again:  the paste law is the
same `AlgebraicGeometry.pullbackPreimageSquareIso_shrink` as for the free chart, and the role the
pseudo-functoriality of the free comparison played there is played here by
`AlgebraicGeometry.pullbackRestrictObjIso_comp`, the section over `V'` being the restriction of
the section over `V` by `AlgebraicGeometry.homOfLE_comp_freeChartBaseSection`. -/
theorem pullbackSectionChartPullbackIso_shrink {V V' : X.Opens} (hV : V' ≤ V) [IsIso (b ∣_ V)]
    [IsIso (b ∣_ V')] (N : X.Modules)
    (σ : (Scheme.Modules.pullback V.ι).obj N ≅
      Scheme.Modules.restrict G (freeChartBaseSection b V))
    (σ' : (Scheme.Modules.pullback V'.ι).obj N ≅
      Scheme.Modules.restrict G (freeChartBaseSection b V'))
    (hσ : (pullbackCompIsoOfEq (X.homOfLE hV) V.ι (Scheme.homOfLE_ι X hV) N).hom ≫ σ'.hom =
      (Scheme.Modules.pullback (X.homOfLE hV)).map σ.hom ≫
        (pullbackRestrictObjIso (X.homOfLE hV) (freeChartBaseSection b V)
          (homOfLE_comp_freeChartBaseSection b hV) G).hom) :
    (pullbackCompIsoOfEq (X'.homOfLE (b.preimage_mono hV)) (b ⁻¹ᵁ V).ι
          (Scheme.homOfLE_ι X' (b.preimage_mono hV))
          ((Scheme.Modules.pullback b).obj N)).hom ≫
        (pullbackSectionChartPullbackIso b N σ').hom =
      (Scheme.Modules.pullback (X'.homOfLE (b.preimage_mono hV))).map
          (pullbackSectionChartPullbackIso b N σ).hom ≫
        (pullbackRestrictObjIso (X'.homOfLE (b.preimage_mono hV)) (b ⁻¹ᵁ V).ι
          (Scheme.homOfLE_ι X' (b.preimage_mono hV)) G).hom :=
  Stacks.AlgebraicGeometry.ModuleLimits.trivShrink_of_paste
    (Scheme.Modules.pullback (b ∣_ V)) (Scheme.Modules.pullback (X.homOfLE hV))
    (Scheme.Modules.pullback (X'.homOfLE (b.preimage_mono hV)))
    (Scheme.Modules.pullback (b ∣_ V'))
    (Scheme.Modules.pullback (X'.homOfLE (b.preimage_mono hV) ≫ (b ∣_ V)))
    (pullbackPreimageSquareIso b V N).hom σ.hom
    (pullbackSectionRestrictIso b G).hom
    (pullbackRestrictObjIso (X'.homOfLE (b.preimage_mono hV)) (b ⁻¹ᵁ V).ι
      (Scheme.homOfLE_ι X' (b.preimage_mono hV)) G).hom
    (pullbackCompIsoOfEq (X'.homOfLE (b.preimage_mono hV)) (b ⁻¹ᵁ V).ι
      (Scheme.homOfLE_ι X' (b.preimage_mono hV)) ((Scheme.Modules.pullback b).obj N)).hom
    (pullbackPreimageSquareIso b V' N).hom σ'.hom
    (pullbackSectionRestrictIso b G).hom
    (pullbackRestrictObjIso (X.homOfLE hV) (freeChartBaseSection b V)
      (homOfLE_comp_freeChartBaseSection b hV) G).hom
    (pullbackRestrictObjIso (X'.homOfLE (b.preimage_mono hV) ≫ (b ∣_ V))
      (freeChartBaseSection b V)
      (homOfLE_comp_morphismRestrict_comp_freeChartBaseSection b hV) G).hom
    (pullbackCompIsoOfEq (X'.homOfLE (b.preimage_mono hV)) (b ∣_ V) rfl
      ((Scheme.Modules.pullback V.ι).obj N)).hom
    (pullbackCompIsoOfEq (X'.homOfLE (b.preimage_mono hV)) (b ∣_ V) rfl
      (Scheme.Modules.restrict G (freeChartBaseSection b V))).hom
    (pullbackCompIsoOfEq (b ∣_ V') (X.homOfLE hV) (morphismRestrict_homOfLE b V' V hV)
      ((Scheme.Modules.pullback V.ι).obj N)).hom
    (pullbackCompIsoOfEq (b ∣_ V') (X.homOfLE hV) (morphismRestrict_homOfLE b V' V hV)
      (Scheme.Modules.restrict G (freeChartBaseSection b V))).hom
    (pullbackCompIsoOfEq (X.homOfLE hV) V.ι (Scheme.homOfLE_ι X hV) N).hom
    (pullbackCompIsoOfEq (X.homOfLE hV) V.ι (Scheme.homOfLE_ι X hV) N).inv
    (pullbackPreimageSquareIso_shrink b hV N).symm
    ((modulesPullbackTriangleIso (X'.homOfLE (b.preimage_mono hV)) (b ∣_ V)
      (X'.homOfLE (b.preimage_mono hV) ≫ (b ∣_ V)) rfl).hom.naturality σ.hom)
    (pullbackRestrictObjIso_comp (X'.homOfLE (b.preimage_mono hV)) (b ∣_ V)
      (freeChartBaseSection b V) (morphismRestrict_comp_freeChartBaseSection b)
      (Scheme.homOfLE_ι X' (b.preimage_mono hV)) rfl
      (homOfLE_comp_morphismRestrict_comp_freeChartBaseSection b hV) G)
    ((modulesPullbackTriangleIso (b ∣_ V') (X.homOfLE hV)
      (X'.homOfLE (b.preimage_mono hV) ≫ (b ∣_ V))
      (morphismRestrict_homOfLE b V' V hV)).hom.naturality σ.hom)
    (pullbackRestrictObjIso_comp (b ∣_ V') (X.homOfLE hV) (freeChartBaseSection b V)
      (homOfLE_comp_freeChartBaseSection b hV)
      (morphismRestrict_comp_freeChartBaseSection b)
      (morphismRestrict_homOfLE b V' V hV)
      (homOfLE_comp_morphismRestrict_comp_freeChartBaseSection b hV) G)
    hσ (pullbackCompIsoOfEq (X.homOfLE hV) V.ι (Scheme.homOfLE_ι X hV) N).inv_hom_id

/-- **The comparison of `b^*N` with `𝒢` over the preimage of `V` is compatible with shrinking
`V`.**  For `V' ≤ V`, both opens carrying a section of `b`, and identifications `σ`, `σ'` of the
restrictions of `N` with the inverse images of `𝒢` along the two sections that agree over the
smaller open, the chart comparison of `AlgebraicGeometry.pullbackSectionChartIso` at `V` along the
inclusion of the preimage of `V'` is the comparison at `V'`, read through the comparison of the
two restrictions of `𝒢`.

The two sides of the hypothesis and of the conclusion are shaped so that taking `Iso.hom` turns
each of them into the equation between `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE`s
that the Zariski glueing of an isomorphism consumes.

The route is `AlgebraicGeometry.restrictChartIso_pullback_trans`, whose cocycle condition is
`AlgebraicGeometry.pullbackSectionChartPullbackIso_shrink`; the hypothesis is carried to the
inverse images by `AlgebraicGeometry.pullbackCompIsoOfEq_hom_comp_of_restrictChartIso`, and the
comparison factor the conclusion comes with is recognised by
`AlgebraicGeometry.restrictFunctorIsoPullback_app_trans_pullbackRestrictObjIso`. -/
theorem restrictChartIso_pullbackSectionChartIso {V V' : X.Opens} (hV : V' ≤ V)
    [IsIso (b ∣_ V)] [IsIso (b ∣_ V')] (N : X.Modules)
    (σ : Scheme.Modules.restrict N V.ι ≅
      Scheme.Modules.restrict G (freeChartBaseSection b V))
    (σ' : Scheme.Modules.restrict N V'.ι ≅
      Scheme.Modules.restrict G (freeChartBaseSection b V'))
    (hσ : restrictChartIso V.ι σ (X.homOfLE hV) (Scheme.homOfLE_ι X hV) ≪≫
        (restrictCompIso (X.homOfLE hV) (freeChartBaseSection b V)
          (homOfLE_comp_freeChartBaseSection b hV) G).symm = σ') :
    restrictChartIso (b ⁻¹ᵁ V).ι (pullbackSectionChartIso b N σ)
            (X'.homOfLE (b.preimage_mono hV))
            (Scheme.homOfLE_ι X' (b.preimage_mono hV)) ≪≫
          (restrictCompIso (X'.homOfLE (b.preimage_mono hV)) (b ⁻¹ᵁ V).ι
            (Scheme.homOfLE_ι X' (b.preimage_mono hV)) G).symm =
      pullbackSectionChartIso b N σ' := by
  have hc :
      restrictChartIso V.ι
            ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N ≪≫
              (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).symm ≪≫ σ))
            (X.homOfLE hV) (Scheme.homOfLE_ι X hV) ≪≫
          ((Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE hV)).app
              (Scheme.Modules.restrict G (freeChartBaseSection b V)) ≪≫
            pullbackRestrictObjIso (X.homOfLE hV) (freeChartBaseSection b V)
              (homOfLE_comp_freeChartBaseSection b hV) G) =
        (Scheme.Modules.restrictFunctorIsoPullback V'.ι).app N ≪≫
          (((Scheme.Modules.restrictFunctorIsoPullback V'.ι).app N).symm ≪≫ σ') :=
    (congrArg (fun s₀ => restrictChartIso V.ι s₀ (X.homOfLE hV) (Scheme.homOfLE_ι X hV) ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE hV)).app
            (Scheme.Modules.restrict G (freeChartBaseSection b V)) ≪≫
          pullbackRestrictObjIso (X.homOfLE hV) (freeChartBaseSection b V)
            (homOfLE_comp_freeChartBaseSection b hV) G))
      (Iso.self_symm_id_assoc _ σ)).trans
      ((congrArg (restrictChartIso V.ι σ (X.homOfLE hV) (Scheme.homOfLE_ι X hV) ≪≫ ·)
        (restrictFunctorIsoPullback_app_trans_pullbackRestrictObjIso (X.homOfLE hV)
          (freeChartBaseSection b V) (homOfLE_comp_freeChartBaseSection b hV) G))
        |>.trans (hσ.trans (Iso.self_symm_id_assoc _ σ').symm))
  refine Eq.trans (congrArg (fun s₀ => restrictChartIso (b ⁻¹ᵁ V).ι s₀
        (X'.homOfLE (b.preimage_mono hV))
        (Scheme.homOfLE_ι X' (b.preimage_mono hV)) ≪≫
      (restrictCompIso (X'.homOfLE (b.preimage_mono hV)) (b ⁻¹ᵁ V).ι
        (Scheme.homOfLE_ι X' (b.preimage_mono hV)) G).symm)
    (pullbackSectionChartIso_eq b N σ)) ?_
  refine Eq.trans (congrArg (restrictChartIso (b ⁻¹ᵁ V).ι
      ((Scheme.Modules.restrictFunctorIsoPullback (b ⁻¹ᵁ V).ι).app
          ((Scheme.Modules.pullback b).obj N) ≪≫
        pullbackSectionChartPullbackIso b N
          (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).symm ≪≫ σ))
      (X'.homOfLE (b.preimage_mono hV))
      (Scheme.homOfLE_ι X' (b.preimage_mono hV)) ≪≫ ·)
    (restrictFunctorIsoPullback_app_trans_pullbackRestrictObjIso
      (X'.homOfLE (b.preimage_mono hV)) (b ⁻¹ᵁ V).ι
      (Scheme.homOfLE_ι X' (b.preimage_mono hV)) G).symm) ?_
  exact (restrictChartIso_pullback_trans (b ⁻¹ᵁ V).ι (X'.homOfLE (b.preimage_mono hV))
    (Scheme.homOfLE_ι X' (b.preimage_mono hV))
    (pullbackSectionChartPullbackIso b N
      (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).symm ≪≫ σ))
    (pullbackRestrictObjIso (X'.homOfLE (b.preimage_mono hV)) (b ⁻¹ᵁ V).ι
      (Scheme.homOfLE_ι X' (b.preimage_mono hV)) G)
    (pullbackSectionChartPullbackIso b N
      (((Scheme.Modules.restrictFunctorIsoPullback V'.ι).app N).symm ≪≫ σ'))
    (pullbackSectionChartPullbackIso_shrink b hV N _ _
      (pullbackCompIsoOfEq_hom_comp_of_restrictChartIso V.ι (X.homOfLE hV)
        (Scheme.homOfLE_ι X hV)
        (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).symm ≪≫ σ)
        (pullbackRestrictObjIso (X.homOfLE hV) (freeChartBaseSection b V)
          (homOfLE_comp_freeChartBaseSection b hV) G)
        (((Scheme.Modules.restrictFunctorIsoPullback V'.ι).app N).symm ≪≫ σ')
        hc))).trans (pullbackSectionChartIso_eq b N σ').symm

end AlgebraicGeometry

end
