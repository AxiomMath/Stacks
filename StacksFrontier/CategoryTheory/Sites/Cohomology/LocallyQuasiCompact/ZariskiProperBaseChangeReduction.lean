module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonEmbedding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiProperBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiProperMorphisms
public import StacksFrontier.Topology.Sheaves.Limits.GermPullbackSections
public import StacksFrontier.Topology.Sheaves.ProperPushforward.ProperBaseChange

/-!
# The base-change map of the Zariski comparison morphisms is a counit

Let `f : X ⟶ Y` be a morphism of the locally quasi-compact Zariski site. Clause (7a) of
Stacks 0DCU asserts that the base-change map

`π_Y^{-1} ∘ f_* ⟶ f_{Zar,*} ∘ π_X^{-1}`

is an isomorphism when `f` is proper. Since the unit of the comparison adjunction is an
isomorphism (clause (3) of Stacks 0DCU) and the direct-image square of clause (5) is an
isomorphism, the component of the base-change map at a sheaf `F` is an isomorphism precisely when
a counit of the comparison adjunction at `Y` is. Clause (7a) is therefore an essential-image
membership:

`IsIso (zariskiComparisonBaseChangeMap S f) ↔
  ∀ F, f_{Zar,*}(π_X^{-1}F) lies in the essential image of π_Y^{-1}`.

In particular, clause (7a) follows from the existence, for every `F`, of an abstract isomorphism
`f_{Zar,*}(π_X^{-1}F) ≅ π_Y^{-1}(f_*F)`, not necessarily the canonical one.

The file also proves two identifications:

* the inverse image of sheaves of sets along a morphism of the site, the sheaf pullback along
  `Opens.map` of the sections formula of Stacks 09X3, is the germ model `GermPullback.sheaf` of
  proper base change on topological spaces (Stacks 0D90), `spaceInverseImageGermIso`;
* the object of `LC_Zar/X` that `Over.pullback f` produces from `g : Z ⟶ Y` has underlying space
  the topological fibre product `Function.Pullback`, compatibly with both projections,
  `zariskiPullbackSpaceIso` and `overPullbackSpaceIso`.

The right-hand side of the formula of Stacks 09X3 is a presheaf on `LC_Zar/Y`,
`germSectionsPresheaf`, and proper base change for sheaves of sets is an isomorphism of such
presheaves, natural in the object of the localized site, `germBaseChangeIso`. Consequently clause
(7a) follows from the sections formula of Stacks 09X3 in the form of an isomorphism of presheaves
`π_X^{-1}F ≅ germSectionsPresheaf`, `isIso_zariskiComparisonBaseChangeMap_of_germSectionsIso`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.spaceInverseImageGermIso`: the inverse
  image of a sheaf of sets along a morphism of the site is the germ model.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiPullbackSpaceIso`: the space of a
  fibre product of the site is the fibre product `Function.Pullback` on which Stacks 0D90 is
  stated.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.overPullbackSpaceIso`: the same, as an
  isomorphism over `X`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.siteToTop`: the inclusion of the site
  into `TopCat`, which takes an object to its underlying space.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.germSectionsPresheaf`: the right-hand
  side of the sections formula of Stacks 09X3, as a presheaf on the localized site:
  `(h : W ⟶ X) ↦ Γ(W, h^{-1}F)`, with `h^{-1}F` the germ model.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonInverseImageGermSectionsIso`:
  the sections formula of Stacks 09X3 with the germ model on the right-hand side, pointwise.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.germBaseChangeNatTrans` and
  `germBaseChangeIso`: proper base change for sheaves of sets on the localized site,
  `Γ(Z, g^{-1}f_*F) ≅ Γ(Z ×_Y X, (g')^{-1}F)`, natural in the object `g : Z ⟶ Y`.

## Main results

All in the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `comparisonBaseChangeMap_app`: the component of the base-change map, computed from the
  definition of a mate.
* `isIso_app_zariskiComparisonBaseChangeMap_iff`: the component of the base-change map at `F` is
  an isomorphism exactly when the counit of the comparison adjunction at `Y` is one at
  `f_{Zar,*}(π_X^{-1}F)`.
* `isIso_app_zariskiComparisonBaseChangeMap_iff_mem_essImage` and
  `isIso_zariskiComparisonBaseChangeMap_iff_mem_essImage`: the same read as an essential-image
  membership, componentwise and globally.
* `isIso_zariskiComparisonBaseChangeMap_of_iso`: clause (7a) follows from the existence of an
  abstract isomorphism `f_{Zar,*}(π_X^{-1}F) ≅ π_Y^{-1}(f_*F)`.
* `zariskiPullbackSpaceIso_hom_pullbackFst` and `zariskiPullbackSpaceIso_hom_pullbackSnd`: the
  identification of the fibre products is compatible with the two projections of Stacks 0D90.
* `pullbackBaseMap_zariskiPullbackHomeo`: the identification of the space of a fibre product of
  the site with the topological fibre product is natural in the base.
* `bijective_germBaseChangeNatTrans_app`: the germ-model base-change morphism is bijective at
  every object of the localized site when the underlying map of `f` is proper, which is
  Stacks 0D90.
* `isIso_zariskiComparisonBaseChangeMap_of_germSectionsIso`: clause (7a) of Stacks 0DCU follows
  from an isomorphism of presheaves on the localized site between the comparison inverse image
  and `germSectionsPresheaf`, at `X` and at `Y`.

## Implementation notes

The component formula is Mathlib's `CategoryTheory.mateEquiv` read at an object: the inverse
mate of `β` at `F` is `L₂(G(η_F)) ≫ L₂(β_{L₁F}) ≫ ε_{H(L₁F)}`. Here `η` is the unit of the
comparison adjunction at `X`, an isomorphism by clause (3) of Stacks 0DCU
(`comparisonAdjunction_unit_isIso`), and `β` is the isomorphism
`zariskiComparisonDirectImageSquareIso`; so the first two factors are isomorphisms and the
third, a counit, carries all the content.

The germ-model sections presheaf is a presheaf on the nose: pulling a germ-model section back
along a further map is precomposition (`GermPullback.comap`), which is strictly functorial. The
same is true of the base-change map of Stacks 0D90, which is substitution into a germwise
formula; its naturality in the base (`Stacks.Topology.ProperBaseChange.baseChangeApp_comap`)
holds by unfolding.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w a b t

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y Z : S.category} (f : X ⟶ Y)

/-! ### The inverse image of a sheaf of sets along a morphism of the site is the germ model -/

/-- **The inverse image of sheaves of sets along a morphism of the site is the germ model.** The
functor `spaceInverseImage`, the `h^{-1}` of the sections formula of Stacks 09X3 and Mathlib's
sheaf pullback along `Opens.map`, agrees on each sheaf of `Type u`-valued sections with the
germ-model inverse image `GermPullback.sheaf` along the underlying continuous map of `k`. -/
def spaceInverseImageGermIso {X' Y' : S.category} (k : X' ⟶ Y')
    (F : Sheaf (Opens.grothendieckTopology Y'.obj) (Type u)) :
    (spaceInverseImage.{u, w, u} S k).obj F ≅
      GermPullback.sheaf ⇑((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map k) F.1 :=
  GermPullback.sheafPullbackIso
    ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map k) F

/-! ### The fibre product of the site is the fibre product of Stacks 0D90 -/

variable (g : Z ⟶ Y)

attribute [local instance] boundedSiteInclusionCreatesPullbacks

/-- **The space of a fibre product of the Zariski site is the fibre product of Stacks 0D90.**
The space underlying `Z ×_Y X` is isomorphic in `TopCat` to
`Stacks.Topology.ProperBaseChange.pullbackSpace`, the subspace of the product on which the two
maps agree. -/
def zariskiPullbackSpaceIso :
    (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj (pullback g f) ≅
      Stacks.Topology.ProperBaseChange.pullbackSpace
        ⇑((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map g)
        ⇑((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) :=
  (zariskiPullbackTopIso S f g).trans (TopCat.pullbackIsoProdSubtype _ _)

/-- `zariskiPullbackSpaceIso` is the underlying isomorphism of `zariskiPullbackHomeo`. -/
lemma zariskiPullbackSpaceIso_hom_apply (p : (pullback g f).obj) :
    (zariskiPullbackSpaceIso S f g).hom p = zariskiPullbackHomeo S f g p := rfl

/-- The identification of the space of `Z ×_Y X` with the fibre product of Stacks 0D90 carries
the first projection of the site to the first projection `f'` of Stacks 0D90. -/
lemma zariskiPullbackSpaceIso_hom_pullbackFst :
    (zariskiPullbackSpaceIso S f g).hom ≫
        Stacks.Topology.ProperBaseChange.pullbackFst
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map g) =
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map (pullback.fst g f) :=
  ConcreteCategory.hom_ext _ _ fun p => zariskiPullbackHomeo_fst S f g p

/-- The identification of the space of `Z ×_Y X` with the fibre product of Stacks 0D90 carries
the structure morphism over `X` to the second projection `g'` of Stacks 0D90. -/
lemma zariskiPullbackSpaceIso_hom_pullbackSnd :
    (zariskiPullbackSpaceIso S f g).hom ≫
        Stacks.Topology.ProperBaseChange.pullbackSnd
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)
          ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map g) =
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map (pullback.snd g f) :=
  ConcreteCategory.hom_ext _ _ fun p => zariskiPullbackHomeo_snd S f g p

/-- **The object `Over.pullback f` produces from `g : Z ⟶ Y` is the fibre product of
Stacks 0D90, over `X`.** The object `(Over.pullback f).obj (Over.mk g)` of `LC_Zar/X` has
underlying space the topological fibre product and structure morphism its second projection. -/
def overPullbackSpaceIso :
    Over.mk ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map
        ((Over.pullback f).obj (Over.mk g)).hom) ≅
      Over.mk (Stacks.Topology.ProperBaseChange.pullbackSnd
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map g)) :=
  Over.isoMk (zariskiPullbackSpaceIso S f g) (zariskiPullbackSpaceIso_hom_pullbackSnd S f g)

/-! ### The base-change map is a counit -/

variable (A : Type a) [Category.{b} A]

/-- **The component of the base-change map.** Reading the definition of a mate at an object, the
base-change map at a sheaf `F` on the space `X` is the composite of the comparison inverse image
at `Y` applied to the unit of the comparison adjunction at `X` and to the direct-image square of
clause (5) of Stacks 0DCU, followed by a counit of the comparison adjunction at `Y`. -/
theorem comparisonBaseChangeMap_app
    {PX : Sheaf (Opens.grothendieckTopology X.obj) A ⥤ Sheaf (S.zariskiTopology.over X) A}
    {PY : Sheaf (Opens.grothendieckTopology Y.obj) A ⥤ Sheaf (S.zariskiTopology.over Y) A}
    (adjX : PX ⊣ S.comparisonDirectImage X A) (adjY : PY ⊣ S.comparisonDirectImage Y A)
    (F : Sheaf (Opens.grothendieckTopology X.obj) A) :
    (comparisonBaseChangeMap S f A adjX adjY).app F =
      PY.map ((spaceDirectImage S f A).map (adjX.unit.app F)) ≫
        PY.map ((zariskiComparisonDirectImageSquareIso S f A).hom.app (PX.obj F)) ≫
          adjY.counit.app ((sliceDirectImage S f A).obj (PX.obj F)) := by
  simp [comparisonBaseChangeMap, mateEquiv]

/-- **Clause (7a) of Stacks 0DCU, at a single sheaf, is the invertibility of a counit.** The
component at `F` of the base-change map of the Zariski comparison morphisms is an isomorphism
exactly when the counit of the comparison adjunction at `Y` is an isomorphism at
`f_{Zar,*}(π_X^{-1}F)`. -/
theorem isIso_app_zariskiComparisonBaseChangeMap_iff
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t))) :
    IsIso ((zariskiComparisonBaseChangeMap.{u, w, t} S f).app F) ↔
      IsIso ((comparisonAdjunction.{u, w, t} S Y).counit.app
        ((sliceDirectImage S f (Type (max u t))).obj
          ((comparisonInverseImage.{u, w, t} S X).obj F))) := by
  have hX : IsIso (comparisonAdjunction.{u, w, t} S X).unit :=
    comparisonAdjunction_unit_isIso.{u, w, t} S X
  rw [show (zariskiComparisonBaseChangeMap.{u, w, t} S f).app F = _ from
    comparisonBaseChangeMap_app S f (Type (max u t)) (comparisonAdjunction.{u, w, t} S X)
      (comparisonAdjunction.{u, w, t} S Y) F,
    isIso_comp_left_iff, isIso_comp_left_iff]

/-- **Clause (7a) of Stacks 0DCU, at a single sheaf, is an essential-image membership.** The
component at `F` of the base-change map is an isomorphism exactly when `f_{Zar,*}(π_X^{-1}F)`
lies in the essential image of the comparison inverse image `π_Y^{-1}`, which is fully faithful
by clause (3) of Stacks 0DCU. -/
theorem isIso_app_zariskiComparisonBaseChangeMap_iff_mem_essImage
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t))) :
    IsIso ((zariskiComparisonBaseChangeMap.{u, w, t} S f).app F) ↔
      (comparisonInverseImage.{u, w, t} S Y).essImage
        ((sliceDirectImage S f (Type (max u t))).obj
          ((comparisonInverseImage.{u, w, t} S X).obj F)) := by
  obtain ⟨hfull, hfaithful⟩ := comparisonInverseImage_fullyFaithful.{u, w, t} S Y
  rw [isIso_app_zariskiComparisonBaseChangeMap_iff.{u, w, t} S f F]
  exact Adjunction.isIso_counit_app_iff_mem_essImage (comparisonAdjunction.{u, w, t} S Y)

/-- **Clause (7a) of Stacks 0DCU is an essential-image membership.** The base-change map of the
Zariski comparison morphisms is an isomorphism exactly when `f_{Zar,*}(π_X^{-1}F)` lies in the
essential image of `π_Y^{-1}` for every sheaf of sets `F` on the space `X`. -/
theorem isIso_zariskiComparisonBaseChangeMap_iff_mem_essImage :
    IsIso (zariskiComparisonBaseChangeMap.{u, w, t} S f) ↔
      ∀ F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t)),
        (comparisonInverseImage.{u, w, t} S Y).essImage
          ((sliceDirectImage S f (Type (max u t))).obj
            ((comparisonInverseImage.{u, w, t} S X).obj F)) := by
  refine ⟨fun h F => ?_, fun h => ?_⟩
  · exact (isIso_app_zariskiComparisonBaseChangeMap_iff_mem_essImage.{u, w, t} S f F).1
      inferInstance
  · have : ∀ F, IsIso ((zariskiComparisonBaseChangeMap.{u, w, t} S f).app F) := fun F =>
      (isIso_app_zariskiComparisonBaseChangeMap_iff_mem_essImage.{u, w, t} S f F).2 (h F)
    exact NatIso.isIso_of_isIso_app _

/-- **An abstract isomorphism suffices for clause (7a) of Stacks 0DCU.** If for every sheaf of
sets `F` on the space `X` there is *some* isomorphism

`f_{Zar,*}(π_X^{-1}F) ≅ π_Y^{-1}(f_*F)`,

then the base-change map of the Zariski comparison morphisms is an isomorphism. -/
theorem isIso_zariskiComparisonBaseChangeMap_of_iso
    (e : ∀ F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t)),
      (sliceDirectImage S f (Type (max u t))).obj
          ((comparisonInverseImage.{u, w, t} S X).obj F) ≅
        (comparisonInverseImage.{u, w, t} S Y).obj
          ((spaceDirectImage S f (Type (max u t))).obj F)) :
    IsIso (zariskiComparisonBaseChangeMap.{u, w, t} S f) :=
  (isIso_zariskiComparisonBaseChangeMap_iff_mem_essImage.{u, w, t} S f).2
    fun F => ⟨_, ⟨(e F).symm⟩⟩

/-! ### The germ-model sections presheaf on the localized site -/

/-- The inclusion of the locally quasi-compact Zariski site into `TopCat`, which takes an object
of the site to its underlying topological space. -/
abbrev siteToTop : S.category ⥤ TopCat.{u} :=
  S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop

/-- A morphism of a localized Zariski site commutes with the two structure morphisms, read on
points of the underlying topological spaces. -/
lemma siteToTop_hom_apply {X' : S.category} {W W' : Over X'} (k : W' ⟶ W)
    (z : ↥((siteToTop S).obj W'.left)) :
    ((siteToTop S).map W'.hom) z = ((siteToTop S).map W.hom) (((siteToTop S).map k.left) z) := by
  have h : (siteToTop S).map k.left ≫ (siteToTop S).map W.hom = (siteToTop S).map W'.hom := by
    rw [← Functor.map_comp, Over.w]
  exact (ConcreteCategory.congr_hom h z).symm

/-- **The germ-model sections presheaf, the right-hand side of the formula of Stacks 09X3.**
For a sheaf of sets `F` on the space of an object `X'` of the site, this is the presheaf on the
localized site `LC_Zar/X'` whose sections over `h : W ⟶ X'` are the global sections of the
germ-model inverse image `h^{-1}F` on `W`:

`(h : W ⟶ X') ↦ Γ(W, h^{-1}F)`.

Restriction along a morphism of the localized site is precomposition (`GermPullback.comap`). -/
def germSectionsPresheaf (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    (Over X')ᵒᵖ ⥤ Type (max u t) where
  obj W :=
    (GermPullback.sheaf ⇑((siteToTop S).map (unop W).hom) F.1).presheaf.obj (op ⊤)
  map {W W'} k := TypeCat.ofHom fun σ => by
    refine GermPullback.comap ((siteToTop S).map k.unop.left).hom.continuous
      (siteToTop_hom_apply S k.unop) ?_ σ
    exact fun _ => trivial
  map_id W := by
    refine ConcreteCategory.hom_ext _ _ fun σ => ?_
    exact GermPullback.ext fun z => congrArg σ.1 (Subtype.ext (by simp))
  map_comp {W W' W''} k l := by
    refine ConcreteCategory.hom_ext _ _ fun σ => ?_
    exact GermPullback.ext fun z => congrArg σ.1 (Subtype.ext (by simp))

/-- The sections of the germ-model sections presheaf over an object of the localized site, by
definition. -/
lemma germSectionsPresheaf_obj (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) (W : Over X') :
    (germSectionsPresheaf S X' F).obj (op W) =
      (GermPullback.sheaf ⇑((siteToTop S).map W.hom) F.1).presheaf.obj (op ⊤) := rfl

/-- Restriction in the germ-model sections presheaf is precomposition with the underlying map of
the morphism of the localized site. -/
@[simp]
lemma germSectionsPresheaf_map_val (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) {W W' : (Over X')ᵒᵖ}
    (k : W ⟶ W')
    (σ : (germSectionsPresheaf S X' F).obj W) (z : (⊤ : Opens ((siteToTop S).obj (unop W').left))) :
    ((germSectionsPresheaf S X' F).map k σ).1 z =
      σ.1 ⟨((siteToTop S).map k.unop.left) z.1, trivial⟩ := rfl

/-- **The sections formula of Stacks 09X3, with the germ model on the right-hand side.** At each
object `h : W ⟶ X'` of the localized site the comparison inverse image `π_{X'}^{-1}F` has the
same sections as the germ-model sections presheaf, namely `Γ(W, h^{-1}F)`.

This is `comparisonInverseImageSectionsIso` followed by `spaceInverseImageGermIso`. -/
def comparisonInverseImageGermSectionsIso {X' : S.category}
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type u)) (W : Over X') :
    ((comparisonInverseImage.{u, w, u} S X').obj F).obj.obj (op W) ≅
      (germSectionsPresheaf S X' F).obj (op W) :=
  comparisonInverseImageSectionsIso.{u, w, u} S W F ≪≫
    ((sheafToPresheaf _ _).mapIso (spaceInverseImageGermIso S W.hom F)).app (op ⊤)

/-! ### Proper base change on the localized site -/

/-- The identification of the space of a fibre product of the site with the topological fibre
product of Stacks 0D90 is natural in the base: the map of topological fibre products induced by
a morphism `k` of the base corresponds to the morphism of the site that `Over.pullback f`
produces from `k`. -/
lemma pullbackBaseMap_zariskiPullbackHomeo {W W' : Over Y} (k : W' ⟶ W)
    (p : ↥((siteToTop S).obj ((Over.pullback f).obj W').left)) :
    Stacks.Topology.ProperBaseChange.pullbackBaseMap ((siteToTop S).map f)
        ((siteToTop S).map k.left) (fun z => (siteToTop_hom_apply S k z).symm)
        (zariskiPullbackHomeo S f W'.hom p) =
      zariskiPullbackHomeo S f W.hom
        (((siteToTop S).map ((Over.pullback f).map k).left) p) := by
  have h1 : ((Over.pullback f).map k).left ≫ pullback.fst W.hom f =
      pullback.fst W'.hom f ≫ k.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have h2 : ((Over.pullback f).map k).left ≫ pullback.snd W.hom f = pullback.snd W'.hom f :=
    Over.w ((Over.pullback f).map k)
  have hfst := ConcreteCategory.congr_hom (congrArg (siteToTop S).map h1) p
  have hsnd := ConcreteCategory.congr_hom (congrArg (siteToTop S).map h2) p
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hfst hsnd
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change ((siteToTop S).map k.left) (Function.Pullback.fst (zariskiPullbackHomeo S f W'.hom p)) =
      Function.Pullback.fst (zariskiPullbackHomeo S f W.hom _)
    rw [zariskiPullbackHomeo_fst, zariskiPullbackHomeo_fst]
    exact hfst.symm
  · change Function.Pullback.snd (zariskiPullbackHomeo S f W'.hom p) =
      Function.Pullback.snd (zariskiPullbackHomeo S f W.hom _)
    rw [zariskiPullbackHomeo_snd, zariskiPullbackHomeo_snd]
    exact hsnd.symm

/-- **Proper base change on the localized Zariski site, in germ-model form.** The base-change
map of Stacks 0D90, applied at every object `g : Z ⟶ Y` of the localized site and transported
along the identification of the space of `Z ×_Y X` with the topological fibre product, is a
morphism of presheaves on `LC_Zar/Y`

`Γ(Z, g^{-1}f_*F) ⟶ Γ(Z ×_Y X, (g')^{-1}F)`. -/
def germBaseChangeNatTrans (F : Sheaf (Opens.grothendieckTopology X.obj) (Type u)) :
    germSectionsPresheaf S Y ((spaceDirectImage S f (Type u)).obj F) ⟶
      (Over.pullback f).op ⋙ germSectionsPresheaf S X F where
  app W := TypeCat.ofHom fun σ => by
    refine GermPullback.comap (zariskiPullbackHomeo S f (unop W).hom).continuous
      (fun p => (zariskiPullbackHomeo_snd S f (unop W).hom p).symm) ?_
      (Stacks.Topology.ProperBaseChange.baseChangeApp ((siteToTop S).map f)
        ((siteToTop S).map (unop W).hom) F.1 σ)
    exact fun _ => trivial
  naturality {W W'} k := by
    refine ConcreteCategory.hom_ext _ _ fun σ => ?_
    refine GermPullback.ext fun z => ?_
    change (Stacks.Topology.ProperBaseChange.baseChangeApp ((siteToTop S).map f)
        ((siteToTop S).map (unop W).hom) F.1 σ).1
        ⟨Stacks.Topology.ProperBaseChange.pullbackBaseMap ((siteToTop S).map f)
          ((siteToTop S).map k.unop.left) (fun w => (siteToTop_hom_apply S k.unop w).symm)
          (zariskiPullbackHomeo S f (unop W').hom z.1), trivial⟩ =
      (Stacks.Topology.ProperBaseChange.baseChangeApp ((siteToTop S).map f)
        ((siteToTop S).map (unop W).hom) F.1 σ).1
        ⟨zariskiPullbackHomeo S f (unop W).hom
          (((siteToTop S).map ((Over.pullback f).map k.unop).left) z.1), trivial⟩
    exact congrArg _ (Subtype.ext (pullbackBaseMap_zariskiPullbackHomeo S f k.unop z.1))

/-- **Proper base change on the localized Zariski site, pointwise.** When the underlying
continuous map of `f` is proper, the germ-model base-change morphism is bijective at every
object `g : Z ⟶ Y` of the localized site. -/
lemma bijective_germBaseChangeNatTrans_app
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} ⇑((siteToTop S).map f))
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type u)) (W : (Over Y)ᵒᵖ) :
    Function.Bijective ((germBaseChangeNatTrans S f F).app W) := by
  have hbc := (ConcreteCategory.isIso_iff_bijective _).1
    (((sheafToPresheaf _ _).mapIso (@asIso _ _ _ _
      (Stacks.Topology.ProperBaseChange.properBaseChangeMap ((siteToTop S).map f)
        ((siteToTop S).map (unop W).hom) F)
      (Stacks.Topology.ProperBaseChange.isIso_properBaseChangeMap _ _ _ hf))).app
        (op (⊤ : Opens ((siteToTop S).obj (unop W).left)))).isIso_hom
  have hcm := GermPullback.bijective_comap_of_homeomorph (ℋ := F.1)
    (e := zariskiPullbackHomeo S f (unop W).hom)
    (hcomp := fun p => (zariskiPullbackHomeo_snd S f (unop W).hom p).symm)
    (W := (Opens.map (Stacks.Topology.ProperBaseChange.pullbackFst ((siteToTop S).map f)
      ((siteToTop S).map (unop W).hom))).obj ⊤)
    (W' := ⊤) (hW := fun _ => trivial) (hW' := fun _ => trivial)
  exact hcm.comp hbc

/-- **Proper base change on the localized Zariski site, Stacks 0D90 for the Zariski site.** For
a morphism `f` of the site whose underlying continuous map is proper, and a sheaf of sets `F` on
the space of `X`, the germ-model sections presheaves fit into an isomorphism

`Γ(Z, g^{-1}f_*F) ≅ Γ(Z ×_Y X, (g')^{-1}F)`,

natural in the object `g : Z ⟶ Y` of the localized site. -/
def germBaseChangeIso
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} ⇑((siteToTop S).map f))
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type u)) :
    germSectionsPresheaf S Y ((spaceDirectImage S f (Type u)).obj F) ≅
      (Over.pullback f).op ⋙ germSectionsPresheaf S X F := by
  have : ∀ W, IsIso ((germBaseChangeNatTrans S f F).app W) := fun W =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_germBaseChangeNatTrans_app S f hf F W)
  have := NatIso.isIso_of_isIso_app (germBaseChangeNatTrans S f F)
  exact asIso (germBaseChangeNatTrans S f F)

/-- **Clause (7a) of Stacks 0DCU follows from the sections formula of Stacks 09X3 in its natural
form.** Suppose that for every sheaf of sets `F` on the space of `X`, and for every sheaf of sets
on the space of `Y`, the comparison inverse image is isomorphic *as a presheaf on the localized
site* to the germ-model sections presheaf

`(h : W ⟶ X) ↦ Γ(W, h^{-1}F)`

of Stacks 09X3. Then the base-change map of the Zariski comparison morphisms is an isomorphism
whenever the underlying continuous map of `f` is proper, which is clause (7a) of Stacks 0DCU. -/
theorem isIso_zariskiComparisonBaseChangeMap_of_germSectionsIso
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} ⇑((siteToTop S).map f))
    (eX : ∀ F : Sheaf (Opens.grothendieckTopology X.obj) (Type u),
      ((comparisonInverseImage.{u, w, u} S X).obj F).obj ≅ germSectionsPresheaf S X F)
    (eY : ∀ G : Sheaf (Opens.grothendieckTopology Y.obj) (Type u),
      ((comparisonInverseImage.{u, w, u} S Y).obj G).obj ≅ germSectionsPresheaf S Y G) :
    IsIso (zariskiComparisonBaseChangeMap.{u, w, u} S f) :=
  isIso_zariskiComparisonBaseChangeMap_of_iso.{u, w, u} S f fun F =>
    ObjectProperty.isoMk _
      (Functor.isoWhiskerLeft (Over.pullback f).op (eX F) ≪≫
        (germBaseChangeIso S f hf F).symm ≪≫ (eY _).symm)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
