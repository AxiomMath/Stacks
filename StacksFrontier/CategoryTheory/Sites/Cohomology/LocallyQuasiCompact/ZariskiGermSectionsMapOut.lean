module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiGermSections

/-!
# Mapping out of the germ-model sections presheaf

Let `X'` be an object of the locally quasi-compact Zariski site and let `F` be a sheaf of sets on
its space. The germ-model sections presheaf `germSectionsPresheaf S X' F` of
`ZariskiProperBaseChangeReduction.lean` is the right-hand side of the sections formula of
Stacks 09X3, and `germSectionsUnit S X' F` of `ZariskiGermSections.lean` is the germ map
`F(U) ⟶ Γ(U, (U → X')^{-1}F)` out of `F` over an open `U ⊆ X'`.

This file proves that the pair has the universal property of the inverse image along the
comparison morphism `π_{X'} : Sh(LC_Zar/X') → Sh(X'_Zar)`: for every sheaf of sets `H` on the
localized Zariski site and every morphism `φ : F ⟶ H|_{Opens X'}` there is a *unique* morphism of
presheaves `ψ : germSectionsPresheaf ⟶ H` with `germSectionsUnit ≫ ψ|_{Opens X'} = φ`. This is
the mapping-out half of the sections formula of Stacks 09X3; the naturality of the pointwise
isomorphism `comparisonInverseImageGermSectionsIso` is what it supplies.

## Main definitions

All in the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `overHomOfContinuous`: a continuous map over `X'` is a morphism of the localized site, the
  inclusion of the site into `TopCat` being fully faithful.
* `opensLift`: a map into the space of `Y` whose image lies in an open `U` factors through the
  open subobject `U` of `Y`.
* `sliceOpen`: the object of `LC_Zar/X'` cut out by an open subset of the space of an object
  `W` over `X'`, with `sliceOpenIncl`, `sliceOpenMap` and `sliceOpenToOpens` the comparison
  morphisms between such objects, and `sliceOpenTopIso` the identification of `W` with its own
  open subobject `⊤`.
* `sliceRestrict`: the restriction of `H` to the small Zariski site of the space of `W`, a sheaf
  of sets on that space (`sliceRestrict_isSheaf`).
* `sliceRestrictUnit`: the morphism `F ⟶ q_{W*}(H|_W)` that `φ` induces, `q_W` being the
  underlying map of the structure morphism of `W`.
* `germMapOut` and `germSectionsMapOutApp`: the mapping-out morphism of the germ model on the
  space of `W`, and its value on global sections read as a section of `H` over `W`.
* `germSectionsMapOut`: the mapping-out morphism `germSectionsPresheaf ⟶ H`.

## Main results

* `map_sliceOpenIncl_germSectionsMapOutApp`: where the germ-model section is the family of germs
  of a section `s` of `F` over `U`, the mapping-out value restricts to the restriction of
  `φ_U s`. This is the engine of the whole file.
* `sliceOpen_section_ext`: sections of `H` over `W` are determined by their restrictions to the
  open subobjects of an open covering of the space of `W`.
* `germSectionsMapOutApp_naturality`: the mapping-out values are natural in the object over `X'`.
* `germSectionsUnit_comp_germSectionsMapOut` and `germSectionsMapOut_unique`: the two halves of
  the universal property.
* `existsUnique_germSectionsMapOut`: **the mapping-out half of the sections formula of
  Stacks 09X3.**

## Implementation notes

The whole construction is a transport of the germ model's own universal property, which is
`GermPullback.Sets.existsUnique_mapOut`. For an object `W` over `X'` the sheaf `H` is restricted
along the composite `Opens W ⥤ LC_Zar/W ⥤ LC_Zar/X'` of the open-subset functor with
`Over.map W.hom`, a continuous functor of sites, giving a sheaf of sets `sliceRestrict W` on the
space of `W`; `φ` induces a morphism `F ⟶ q_{W*}(sliceRestrict W)`, and the germ model's
universal property produces the unique morphism `germMapOut W` out of `q_W^{-1}F`. Its value at
the open `⊤`, transported along `sliceOpenTopIso`, is the component of `ψ` at `W`.

Two facts make the bookkeeping light. First, morphisms of the localized site *are* continuous
maps over `X'`, because the inclusion of the site into `TopCat` is fully faithful
(`overHomOfContinuous`, `over_hom_ext`); every comparison morphism between open subobjects is
built that way, and every identity between such morphisms is checked on points. Second, the
structure morphism of an open subobject of `X'` is a monomorphism, so there is *at most one*
morphism of `LC_Zar/X'` into it (`over_hom_opensToSlice_ext`); this discharges every coherence
between the comparison morphisms, including the naturality of `sliceOpenToOpens`.

Naturality of `ψ`, and its uniqueness, are both proved by restricting to an open covering rather
than by unfolding: `sliceRestrict W` is a sheaf on the space of `W`, so a section of `H` over `W`
is determined by its restrictions to the open subobjects `sliceOpen W A`
(`sliceOpen_section_ext`), and `GermPullback.exists_repr` supplies a covering on whose members the
given germ-model section is a family of germs of a single section of `F`. There the value is
forced, by `map_sliceOpenIncl_germSectionsMapOutApp` for the constructed `ψ` and by naturality
plus the defining equation for any competitor.

## References

* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w t

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)

/-! ### Morphisms of the localized site are continuous maps over `X'` -/

/-- The inclusion of the site into `TopCat` is fully faithful: it is a composite of two
inclusions of full subcategories. -/
def siteToTopFullyFaithful : (siteToTop S).FullyFaithful := by
  have hInc : S.qcSite.inclusion.FullyFaithful := by
    change (ObjectProperty.ι _).FullyFaithful
    exact ObjectProperty.fullyFaithfulι _
  have hTop : locallyQuasiCompactHausdorffToTop.FullyFaithful := by
    change (ObjectProperty.ι _).FullyFaithful
    exact ObjectProperty.fullyFaithfulι _
  exact hInc.comp hTop

/-- Morphisms of a localized site are determined by their underlying maps. -/
lemma over_hom_ext {A B : Over X'} {f f' : A ⟶ B} (h : ∀ a, f.left a = f'.left a) : f = f' :=
  Over.OverMorphism.ext (ConcreteCategory.hom_ext _ _ h)

/-- **A continuous map over `X'` is a morphism of the localized site.** The inclusion of the site
into `TopCat` is fully faithful, so a continuous map between the spaces commuting with the two
structure morphisms is a morphism over `X'`. -/
def overHomOfContinuous {A B : Over X'}
    (t : (siteToTop S).obj A.left ⟶ (siteToTop S).obj B.left)
    (ht : ∀ a, B.hom (t a) = A.hom a) : A ⟶ B := by
  have := (siteToTopFullyFaithful S).full
  have := (siteToTopFullyFaithful S).faithful
  refine Over.homMk ((siteToTop S).preimage t) (ConcreteCategory.hom_ext _ _ fun a => ?_)
  rw [ConcreteCategory.comp_apply]
  change B.hom ((siteToTop S).map ((siteToTop S).preimage t) a) = A.hom a
  rw [Functor.map_preimage]
  exact ht a

/-- The underlying map of `overHomOfContinuous` is the given continuous map. -/
@[simp]
lemma overHomOfContinuous_left_apply {A B : Over X'}
    (t : (siteToTop S).obj A.left ⟶ (siteToTop S).obj B.left)
    (ht : ∀ a, B.hom (t a) = A.hom a) (a : (siteToTop S).obj A.left) :
    (overHomOfContinuous S X' t ht).left a = t a := by
  have := (siteToTopFullyFaithful S).full
  have := (siteToTopFullyFaithful S).faithful
  exact ConcreteCategory.congr_hom (Functor.map_preimage (siteToTop S) t) a

/-! ### Open subobjects of the localized site -/

/-- The structure morphism of the open subobject `U` of an object `Y` of the site is an open
embedding. -/
lemma opensToSlice_isOpenEmbedding (Y : S.category) (U : Opens Y.obj) :
    Topology.IsOpenEmbedding ⇑((S.opensToSlice Y).1.obj U).hom :=
  ((S.opensToSlice Y).2 U).1

/-- The structure morphism of the open subobject `U` of an object `Y` of the site has image
exactly `U`. -/
lemma opensToSlice_range (Y : S.category) (U : Opens Y.obj) :
    Set.range ⇑((S.opensToSlice Y).1.obj U).hom = (U : Set Y.obj) :=
  ((S.opensToSlice Y).2 U).2

/-- A point of an open `U ⊆ Y` is the image of a point of the open subobject `U`. -/
lemma opensLift_exists (Y : S.category) (U : Opens Y.obj) {A : TopCat.{u}}
    (t : A ⟶ (siteToTop S).obj Y) (ht : ∀ a, t a ∈ U) (a : A) :
    ∃ z, ((S.opensToSlice Y).1.obj U).hom z = t a := by
  have hmem : t a ∈ Set.range ⇑((S.opensToSlice Y).1.obj U).hom := by
    rw [opensToSlice_range S Y U]
    exact ht a
  exact hmem

/-- The underlying function of `opensLift`. -/
def opensLiftFun (Y : S.category) (U : Opens Y.obj) {A : TopCat.{u}}
    (t : A ⟶ (siteToTop S).obj Y) (ht : ∀ a, t a ∈ U) (a : A) :
    ((S.opensToSlice Y).1.obj U).left.obj :=
  (opensLift_exists S Y U t ht a).choose

/-- The underlying function of `opensLift` is a section of the inclusion of the subobject. -/
lemma opensLiftFun_spec (Y : S.category) (U : Opens Y.obj) {A : TopCat.{u}}
    (t : A ⟶ (siteToTop S).obj Y) (ht : ∀ a, t a ∈ U) (a : A) :
    ((S.opensToSlice Y).1.obj U).hom (opensLiftFun S Y U t ht a) = t a :=
  (opensLift_exists S Y U t ht a).choose_spec

/-- **Lifting a map through an open subobject.** A continuous map into the space of `Y` whose
image lies in an open `U ⊆ Y` factors through the open subobject `U`, because the structure
morphism of that subobject is an open embedding with image exactly `U`. -/
def opensLift (Y : S.category) (U : Opens Y.obj) {A : TopCat.{u}}
    (t : A ⟶ (siteToTop S).obj Y) (ht : ∀ a, t a ∈ U) :
    A ⟶ (siteToTop S).obj ((S.opensToSlice Y).1.obj U).left :=
  TopCat.ofHom
    { toFun := opensLiftFun S Y U t ht
      continuous_toFun := by
        refine (opensToSlice_isOpenEmbedding S Y U).isInducing.continuous_iff.mpr ?_
        have hfun : ⇑((S.opensToSlice Y).1.obj U).hom ∘ opensLiftFun S Y U t ht = ⇑t :=
          funext (opensLiftFun_spec S Y U t ht)
        rw [hfun]
        exact (ConcreteCategory.hom t).continuous }

/-- The lift of a map through an open subobject is a section of the inclusion of that
subobject. -/
@[simp]
lemma opensLift_spec (Y : S.category) (U : Opens Y.obj) {A : TopCat.{u}}
    (t : A ⟶ (siteToTop S).obj Y) (ht : ∀ a, t a ∈ U) (a : A) :
    ((S.opensToSlice Y).1.obj U).hom (opensLift S Y U t ht a) = t a :=
  opensLiftFun_spec S Y U t ht a

/-- Two morphisms of the opposite localized site with an open subobject of `X'` as source are
equal. -/
lemma opensToSlice_op_hom_unique {A : Over X'} {U : Opens X'.obj}
    (f f' : op ((S.opensToSlice X').1.obj U) ⟶ op A) : f = f' :=
  Quiver.Hom.unop_inj (over_hom_opensToSlice_ext S f.unop f'.unop)

/-- Two morphisms of the site into an open subobject of `Y` agree as soon as their composites
with the inclusion of that subobject agree, that inclusion being injective. -/
lemma opensToSlice_left_hom_ext (Y : S.category) (A : Opens Y.obj) {Z : S.category}
    {t t' : Z ⟶ ((S.opensToSlice Y).1.obj A).left}
    (h : ∀ z, ((S.opensToSlice Y).1.obj A).hom (t z) =
      ((S.opensToSlice Y).1.obj A).hom (t' z)) : t = t' :=
  ConcreteCategory.hom_ext _ _ fun z => (opensToSlice_isOpenEmbedding S Y A).injective (h z)

/-- **The open subobject of the localized site cut out by an open subset of an object over
`X'`.** For `W : Over X'` and an open `A` of the space of `W`, this is the open subobject `A` of
`W`, read as an object over `X'`. -/
abbrev sliceOpen (W : Over X') (A : Opens W.left.obj) : Over X' :=
  (Over.map W.hom).obj ((S.opensToSlice W.left).1.obj A)

/-- Two morphisms of the localized site into an open subobject of `W` agree as soon as their
underlying maps to the space of `W` agree. -/
lemma sliceOpen_hom_ext {Z W : Over X'} {A : Opens W.left.obj} {f f' : Z ⟶ sliceOpen S X' W A}
    (h : ∀ z, ((S.opensToSlice W.left).1.obj A).hom (f.left z) =
      ((S.opensToSlice W.left).1.obj A).hom (f'.left z)) : f = f' :=
  Over.OverMorphism.ext (opensToSlice_left_hom_ext S W.left A h)

/-- **The inclusion of an open subobject of `W` into `W`**, over `X'`. -/
def sliceOpenIncl (W : Over X') (A : Opens W.left.obj) : sliceOpen S X' W A ⟶ W :=
  overHomOfContinuous S X'
    ((siteToTop S).map ((S.opensToSlice W.left).1.obj A).hom) (fun _ => rfl)

/-- The underlying map of the inclusion of an open subobject is the inclusion of the open. -/
@[simp]
lemma sliceOpenIncl_left_apply (W : Over X') (A : Opens W.left.obj)
    (z : (siteToTop S).obj (sliceOpen S X' W A).left) :
    (sliceOpenIncl S X' W A).left z = ((S.opensToSlice W.left).1.obj A).hom z :=
  overHomOfContinuous_left_apply S X' _ _ z

/-- The inclusion of a smaller open subobject factors through a bigger one. -/
lemma sliceOpen_map_comp_incl (W : Over X') {A B : Opens W.left.obj} (j : A ⟶ B) :
    ((S.opensToSlice W.left).1 ⋙ Over.map W.hom).map j ≫ sliceOpenIncl S X' W B =
      sliceOpenIncl S X' W A := by
  refine over_hom_ext S X' fun z => ?_
  have h1 : (((S.opensToSlice W.left).1 ⋙ Over.map W.hom).map j ≫
      sliceOpenIncl S X' W B).left z =
      ((S.opensToSlice W.left).1.obj B).hom (((S.opensToSlice W.left).1.map j).left z) := by
    rw [Over.comp_left, ConcreteCategory.comp_apply]
    exact sliceOpenIncl_left_apply S X' W B _
  rw [h1, sliceOpenIncl_left_apply]
  exact ConcreteCategory.congr_hom (Over.w ((S.opensToSlice W.left).1.map j)) z

/-- The inverse of the inclusion of the open subobject `⊤`. -/
def sliceOpenTopInv (W : Over X') : W ⟶ sliceOpen S X' W ⊤ :=
  overHomOfContinuous S X'
    (opensLift S W.left ⊤ (𝟙 ((siteToTop S).obj W.left)) (fun _ => trivial))
    (fun a => congrArg (fun y => W.hom y)
      (opensLift_spec S W.left ⊤ (𝟙 ((siteToTop S).obj W.left)) (fun _ => trivial) a))

/-- The underlying map of `sliceOpenTopInv` is the lift through the open subobject `⊤`. -/
@[simp]
lemma sliceOpenTopInv_left_apply (W : Over X') (a : (siteToTop S).obj W.left) :
    (sliceOpenTopInv S X' W).left a =
      opensLift S W.left ⊤ (𝟙 ((siteToTop S).obj W.left)) (fun _ => trivial) a :=
  overHomOfContinuous_left_apply S X' _ _ a

/-- **The open subobject `⊤` of `W` is `W`.** The inclusion of the open subobject `⊤` is an open
embedding whose image is the whole of `W`, hence a homeomorphism, hence an isomorphism over
`X'`. -/
def sliceOpenTopIso (W : Over X') : sliceOpen S X' W ⊤ ≅ W where
  hom := sliceOpenIncl S X' W ⊤
  inv := sliceOpenTopInv S X' W
  hom_inv_id := by
    refine sliceOpen_hom_ext S X' fun z => ?_
    rw [Over.comp_left, ConcreteCategory.comp_apply, sliceOpenIncl_left_apply,
      sliceOpenTopInv_left_apply]
    exact opensLift_spec S W.left ⊤ (𝟙 ((siteToTop S).obj W.left)) (fun _ => trivial) _
  inv_hom_id := by
    refine over_hom_ext S X' fun a => ?_
    rw [Over.comp_left, ConcreteCategory.comp_apply, sliceOpenTopInv_left_apply,
      sliceOpenIncl_left_apply]
    exact opensLift_spec S W.left ⊤ (𝟙 ((siteToTop S).obj W.left)) (fun _ => trivial) _

/-- The forward map of `sliceOpenTopIso` is the inclusion of the open subobject `⊤`. -/
@[simp]
lemma sliceOpenTopIso_hom (W : Over X') :
    (sliceOpenTopIso S X' W).hom = sliceOpenIncl S X' W ⊤ := rfl

/-- **The comparison of an open subobject of `W` with an open subobject of `X'`.** If the
structure morphism of `W` carries an open `A` of the space of `W` into an open `U` of `X'`, then
the open subobject `A` of `W` maps to the open subobject `U` of `X'`, over `X'`. -/
def sliceOpenToOpens (W : Over X') (A : Opens W.left.obj) (U : Opens X'.obj)
    (hA : ∀ z : A, ((siteToTop S).map W.hom) z.1 ∈ U) :
    sliceOpen S X' W A ⟶ (S.opensToSlice X').1.obj U :=
  overHomOfContinuous S X'
    (opensLift S X' U ((siteToTop S).map (sliceOpen S X' W A).hom)
      (fun z => hA ⟨_, opensToSlice_hom_mem S (T := W.left) A z⟩))
    (fun z => opensLift_spec S X' U _ _ z)

/-- The comparison morphisms of `sliceOpenToOpens` are natural in the open of `X'`. -/
def sliceOpenNatTrans (W : Over X') :
    Opens.map ((siteToTop S).map W.hom) ⋙ (S.opensToSlice W.left).1 ⋙ Over.map W.hom ⟶
      (S.opensToSlice X').1 where
  app U := sliceOpenToOpens S X' W ((Opens.map ((siteToTop S).map W.hom)).obj U) U fun z => z.2
  naturality _ _ _ := over_hom_opensToSlice_ext S _ _

/-! ### Restricting a sheaf on the localized site to the small site of an object -/

variable (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t)))
  (H : Sheaf (S.zariskiTopology.over X') (Type (max u t)))

/-- The composite of the open-subset functor of `W` with `Over.map W.hom` is continuous from the
small Zariski site of the space of `W` to the localized Zariski site of `X'`. -/
lemma sliceOpen_isContinuous (W : Over X') :
    ((S.opensToSlice W.left).1 ⋙ Over.map W.hom).IsContinuous
      (Opens.grothendieckTopology W.left.obj) (S.zariskiTopology.over X') :=
  let := S.opensToSlice_isContinuous W.left
  Functor.isContinuous_comp (S.opensToSlice W.left).1 (Over.map W.hom)
    (Opens.grothendieckTopology W.left.obj) (S.zariskiTopology.over W.left)
    (S.zariskiTopology.over X')

/-- **The restriction of `H` to the small Zariski site of an object over `X'`**, as a sheaf: the
sections over an open `A` of the space of `W` are the sections of `H` over the open subobject
`sliceOpen W A` of the localized site. -/
def sliceRestrictSheaf (W : Over X') :
    Sheaf (Opens.grothendieckTopology W.left.obj) (Type (max u t)) :=
  letI := sliceOpen_isContinuous S X' W
  (((S.opensToSlice W.left).1 ⋙ Over.map W.hom).sheafPushforwardContinuous (Type (max u t))
    (Opens.grothendieckTopology W.left.obj) (S.zariskiTopology.over X')).obj H

/-- The restriction of `H` to the small Zariski site of `W`, as a presheaf on the space of `W`. -/
def sliceRestrict (W : Over X') : ((siteToTop S).obj W.left).Presheaf (Type (max u t)) :=
  ((S.opensToSlice W.left).1 ⋙ Over.map W.hom).op ⋙ H.1

/-- The sections of `sliceRestrict` over an open `A` are the sections of `H` over the open
subobject `sliceOpen W A`. -/
lemma sliceRestrict_obj (W : Over X') (A : Opens W.left.obj) :
    (sliceRestrict S X' H W).obj (op A) = H.1.obj (op (sliceOpen S X' W A)) := rfl

/-- The restriction of `H` to the small Zariski site of `W` is a sheaf. -/
lemma sliceRestrict_isSheaf (W : Over X') :
    TopCat.Presheaf.IsSheaf (sliceRestrict S X' H W) :=
  (sliceRestrictSheaf S X' H W).2

/-! ### The germ-model unit attached to `φ` -/

variable (φ : F.1 ⟶ (S.opensToSlice X').1.op ⋙ H.1)

/-- **The unit of the germ model attached to `φ`.** For an object `W` over `X'` this is the
morphism `F ⟶ q_{W*}(H|_W)` whose component at an open `U ⊆ X'` sends a section of `F` over `U`
to the restriction of `φ_U` along the comparison `sliceOpenToOpens`. -/
def sliceRestrictUnit (W : Over X') :
    F.1 ⟶ (TopCat.Presheaf.pushforward (Type (max u t)) ((siteToTop S).map W.hom)).obj
      (sliceRestrict S X' H W) :=
  φ ≫ Functor.whiskerRight (NatTrans.op (sliceOpenNatTrans S X' W)) H.1

/-- The components of `sliceRestrictUnit`, by definition. -/
lemma sliceRestrictUnit_app_apply (W : Over X') (U : Opens X'.obj) (s : F.1.obj (op U)) :
    (sliceRestrictUnit S X' F H φ W).app (op U) s =
      H.1.map (sliceOpenToOpens S X' W ((Opens.map ((siteToTop S).map W.hom)).obj U) U
        (fun z => z.2)).op (φ.app (op U) s) := rfl

/-- Restricting a section of `H` along two morphisms from an open subobject of `X'` gives the same
result. -/
private lemma map_op_opensToSlice_ext {A : Over X'} {U : Opens X'.obj}
    (f f' : A ⟶ (S.opensToSlice X').1.obj U) (x : H.1.obj (op ((S.opensToSlice X').1.obj U))) :
    H.1.map f.op x = H.1.map f'.op x :=
  congrArg (fun m => ConcreteCategory.hom (H.1.map m.op) x) (over_hom_opensToSlice_ext S f f')

/-- **The local value of `sliceRestrictUnit` is the restriction of `φ`.** -/
lemma localValue_sliceRestrictUnit (W : Over X') (A : Opens W.left.obj) (U : Opens X'.obj)
    (hA : ∀ z : A, ((siteToTop S).map W.hom) z.1 ∈ U) (s : F.1.obj (op U)) :
    GermPullback.Sets.localValue (sliceRestrictUnit S X' F H φ W) hA s =
      H.1.map (sliceOpenToOpens S X' W A U hA).op (φ.app (op U) s) := by
  have h1 : GermPullback.Sets.localValue (sliceRestrictUnit S X' F H φ W) hA s =
      H.1.map (((S.opensToSlice W.left).1 ⋙ Over.map W.hom).map
          (homOfLE (fun z hz => hA ⟨z, hz⟩) :
            A ⟶ (Opens.map ((siteToTop S).map W.hom)).obj U)).op
        (H.1.map (sliceOpenToOpens S X' W
          ((Opens.map ((siteToTop S).map W.hom)).obj U) U (fun z => z.2)).op
          (φ.app (op U) s)) := rfl
  rw [h1, ← ConcreteCategory.comp_apply, ← H.1.map_comp]
  exact map_op_opensToSlice_ext S X' H _ _ _


/-! ### The mapping-out morphism -/

/-- **The mapping-out morphism of the germ model on the space of `W`**, attached to `φ` by the
universal property of the germ model. -/
def germMapOut (W : Over X') :
    (GermPullback.sheaf ⇑((siteToTop S).map W.hom) F.1).presheaf ⟶ sliceRestrict S X' H W :=
  GermPullback.Sets.mapOut (sliceRestrictUnit S X' F H φ W) (sliceRestrict_isSheaf S X' H W)

/-- **The value of the mapping-out morphism at an object over `X'`**: the global sections of the
germ model on the space of `W` map to the sections of `H` over `W`, through the identification of
`W` with its own open subobject `⊤`. -/
def germSectionsMapOutApp (W : Over X') (σ : (germSectionsPresheaf S X' F).obj (op W)) :
    H.1.obj (op W) :=
  H.1.map (sliceOpenTopIso S X' W).inv.op ((germMapOut S X' F H φ W).app (op ⊤) σ)

/-- Restriction of `H` along an isomorphism of the localized site is injective. -/
lemma map_op_injective_of_iso {A B : Over X'} (e : A ≅ B) {a b : H.1.obj (op B)}
    (h : H.1.map e.hom.op a = H.1.map e.hom.op b) : a = b := by
  have hcancel : ∀ x : H.1.obj (op B), H.1.map e.inv.op (H.1.map e.hom.op x) = x := by
    intro x
    rw [← ConcreteCategory.comp_apply, ← H.1.map_comp, ← op_comp, Iso.inv_hom_id, op_id,
      H.1.map_id, ConcreteCategory.id_apply]
  rw [← hcancel a, h, hcancel]

/-- **Sections of `H` over `W` are determined by their restrictions to the open subobjects of an
open covering of the space of `W`**: those restrictions are the restrictions of `sliceRestrict`,
which is a sheaf on the space of `W`. -/
lemma sliceOpen_section_ext (W : Over X') {ι : Type u} (A : ι → Opens W.left.obj)
    (hcov : (⊤ : Opens ((siteToTop S).obj W.left)) ≤ iSup A) {a b : H.1.obj (op W)}
    (h : ∀ i, H.1.map (sliceOpenIncl S X' W (A i)).op a =
      H.1.map (sliceOpenIncl S X' W (A i)).op b) : a = b := by
  refine map_op_injective_of_iso S X' H (sliceOpenTopIso S X' W) ?_
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨sliceRestrict S X' H W, sliceRestrict_isSheaf S X' H W⟩ :
      ((siteToTop S).obj W.left).Sheaf (Type (max u t)))
    A ⊤ (fun i => homOfLE le_top) hcov _ _ fun i => ?_
  have hcomp : ∀ x : H.1.obj (op W),
      (sliceRestrict S X' H W).map (homOfLE le_top : A i ⟶ ⊤).op
          (H.1.map (sliceOpenTopIso S X' W).hom.op x) =
        H.1.map (sliceOpenIncl S X' W (A i)).op x := by
    intro x
    have h1 : (sliceRestrict S X' H W).map (homOfLE le_top : A i ⟶ ⊤).op
          (H.1.map (sliceOpenTopIso S X' W).hom.op x) =
        H.1.map ((((S.opensToSlice W.left).1 ⋙ Over.map W.hom).map
            (homOfLE le_top : A i ⟶ ⊤)).op)
          (H.1.map (sliceOpenTopIso S X' W).hom.op x) := rfl
    rw [h1, ← ConcreteCategory.comp_apply, ← H.1.map_comp, ← op_comp]
    refine congrArg (fun m => ConcreteCategory.hom (H.1.map (Opposite.op m)) x) ?_
    exact sliceOpen_map_comp_incl S X' W (homOfLE le_top : A i ⟶ (⊤ : Opens W.left.obj))
  rw [hcomp, hcomp]
  exact h i

/-- **The restriction of the mapping-out value to an open subobject on which the section is a
germ section.** This is the defining property of the germ model's mapping-out morphism, read on
the localized site: where `σ` is the family of germs of a section `s` of `F` over `U`, the value
of the mapping-out morphism restricts to the restriction of `φ_U s`. -/
lemma map_sliceOpenIncl_germSectionsMapOutApp (W : Over X')
    (σ : (germSectionsPresheaf S X' F).obj (op W)) (A : Opens W.left.obj) (U : Opens X'.obj)
    (hA : ∀ z : A, ((siteToTop S).map W.hom) z.1 ∈ U) (s : F.1.obj (op U))
    (hσ : (GermPullback.sheaf ⇑((siteToTop S).map W.hom) F.1).presheaf.map
        (homOfLE le_top : A ⟶ ⊤).op σ = GermPullback.ofSection hA s) :
    H.1.map (sliceOpenIncl S X' W A).op (germSectionsMapOutApp S X' F H φ W σ) =
      H.1.map (sliceOpenToOpens S X' W A U hA).op (φ.app (op U) s) := by
  have hstep1 : sliceOpenIncl S X' W A ≫ (sliceOpenTopIso S X' W).inv =
      ((S.opensToSlice W.left).1 ⋙ Over.map W.hom).map (homOfLE le_top : A ⟶ ⊤) := by
    refine sliceOpen_hom_ext S X' fun z => ?_
    have hleft : (sliceOpenIncl S X' W A ≫ (sliceOpenTopIso S X' W).inv).left z =
        opensLift S W.left ⊤ (𝟙 ((siteToTop S).obj W.left)) (fun _ => trivial)
          (((S.opensToSlice W.left).1.obj A).hom z) := by
      rw [Over.comp_left, ConcreteCategory.comp_apply, sliceOpenIncl_left_apply]
      exact sliceOpenTopInv_left_apply S X' W _
    rw [hleft]
    refine (opensLift_spec S W.left ⊤ (𝟙 ((siteToTop S).obj W.left))
      (fun _ => trivial) _).trans ?_
    exact (ConcreteCategory.congr_hom (Over.w ((S.opensToSlice W.left).1.map
      (homOfLE le_top : A ⟶ (⊤ : Opens W.left.obj)))) z).symm
  have e1 : H.1.map (sliceOpenIncl S X' W A).op (germSectionsMapOutApp S X' F H φ W σ) =
      H.1.map ((sliceOpenIncl S X' W A ≫ (sliceOpenTopIso S X' W).inv).op)
        ((germMapOut S X' F H φ W).app (op ⊤) σ) := by
    rw [op_comp, H.1.map_comp]
    rfl
  have e2 : H.1.map ((sliceOpenIncl S X' W A ≫ (sliceOpenTopIso S X' W).inv).op)
        ((germMapOut S X' F H φ W).app (op ⊤) σ) =
      (germMapOut S X' F H φ W).app (op A)
        ((GermPullback.sheaf ⇑((siteToTop S).map W.hom) F.1).presheaf.map
          (homOfLE le_top : A ⟶ ⊤).op σ) := by
    rw [hstep1]
    exact (NatTrans.naturality_apply (germMapOut S X' F H φ W)
      (homOfLE le_top : A ⟶ (⊤ : Opens ((siteToTop S).obj W.left))).op σ).symm
  have e3 : (germMapOut S X' F H φ W).app (op A)
        ((GermPullback.sheaf ⇑((siteToTop S).map W.hom) F.1).presheaf.map
          (homOfLE le_top : A ⟶ ⊤).op σ) =
      H.1.map (sliceOpenToOpens S X' W A U hA).op (φ.app (op U) s) := by
    rw [hσ]
    exact (GermPullback.Sets.appValue_ofSection (sliceRestrictUnit S X' F H φ W)
      (sliceRestrict_isSheaf S X' H W) hA s).trans
      (localValue_sliceRestrictUnit S X' F H φ W A U hA s)
  exact e1.trans (e2.trans e3)

/-- **A morphism of open subobjects over `X'`**: if a morphism `k : W' ⟶ W` of the localized site
carries an open `A` of the space of `W'` into an open `B` of the space of `W`, then it carries the
open subobject `A` of `W'` to the open subobject `B` of `W`. -/
def sliceOpenMap {W W' : Over X'} (k : W' ⟶ W) (A : Opens W'.left.obj) (B : Opens W.left.obj)
    (hAB : ∀ z : A, ((siteToTop S).map k.left) z.1 ∈ B) :
    sliceOpen S X' W' A ⟶ sliceOpen S X' W B :=
  overHomOfContinuous S X'
    (opensLift S W.left B
      ((siteToTop S).map ((S.opensToSlice W'.left).1.obj A).hom ≫ (siteToTop S).map k.left)
      (fun z => hAB ⟨_, opensToSlice_hom_mem S (T := W'.left) A z⟩))
    (fun z => (congrArg (fun y => ((siteToTop S).map W.hom) y)
        (opensLift_spec S W.left B _ _ z)).trans
      (siteToTop_hom_apply S k (((S.opensToSlice W'.left).1.obj A).hom z)).symm)

/-- The underlying map of `sliceOpenMap` is the underlying map of `k`. -/
lemma sliceOpenMap_incl {W W' : Over X'} (k : W' ⟶ W) (A : Opens W'.left.obj)
    (B : Opens W.left.obj) (hAB : ∀ z : A, ((siteToTop S).map k.left) z.1 ∈ B)
    (z : (siteToTop S).obj (sliceOpen S X' W' A).left) :
    ((S.opensToSlice W.left).1.obj B).hom ((sliceOpenMap S X' k A B hAB).left z) =
      ((siteToTop S).map k.left) (((S.opensToSlice W'.left).1.obj A).hom z) := by
  rw [sliceOpenMap, overHomOfContinuous_left_apply]
  exact opensLift_spec S W.left B _ _ z

/-- `sliceOpenMap` is compatible with the inclusions of the two open subobjects. -/
lemma sliceOpenMap_comp_incl {W W' : Over X'} (k : W' ⟶ W) (A : Opens W'.left.obj)
    (B : Opens W.left.obj) (hAB : ∀ z : A, ((siteToTop S).map k.left) z.1 ∈ B) :
    sliceOpenIncl S X' W' A ≫ k = sliceOpenMap S X' k A B hAB ≫ sliceOpenIncl S X' W B := by
  refine over_hom_ext S X' fun z => ?_
  rw [Over.comp_left, ConcreteCategory.comp_apply, sliceOpenIncl_left_apply, Over.comp_left,
    ConcreteCategory.comp_apply, sliceOpenIncl_left_apply]
  exact (sliceOpenMap_incl S X' k A B hAB z).symm


/-! ### Naturality, and the universal property -/

/-- **The mapping-out values are natural in the object over `X'`.** Near every point the section
`σ` is a family of germs of a section of `F`, and both sides restrict there to the restriction of
`φ` applied to that section (`map_sliceOpenIncl_germSectionsMapOutApp`); the open subobjects so
obtained cover, and `H` restricted to the space of `W'` is a sheaf. -/
lemma germSectionsMapOutApp_naturality {W W' : Over X'} (k : W' ⟶ W)
    (σ : (germSectionsPresheaf S X' F).obj (op W)) :
    germSectionsMapOutApp S X' F H φ W' ((germSectionsPresheaf S X' F).map k.op σ) =
      H.1.map k.op (germSectionsMapOutApp S X' F H φ W σ) := by
  classical
  choose A hmem ii V hV s hs using fun x' : (siteToTop S).obj W'.left =>
    GermPullback.exists_repr σ
      (show ((siteToTop S).map k.left) x' ∈ (⊤ : Opens ((siteToTop S).obj W.left)) from trivial)
  set B : (siteToTop S).obj W'.left → Opens ((siteToTop S).obj W'.left) := fun x' =>
    (Opens.map ((siteToTop S).map k.left)).obj (A x') with hB
  have hcover : (⊤ : Opens ((siteToTop S).obj W'.left)) ≤ iSup B := fun x' _ =>
    Opens.mem_iSup.2 ⟨x', hmem x'⟩
  have hV' : ∀ (x' : (siteToTop S).obj W'.left) (z : B x'),
      ((siteToTop S).map W'.hom) z.1 ∈ V x' := by
    intro x' z
    rw [siteToTop_hom_apply S k z.1]
    exact hV x' ⟨_, z.2⟩
  have hσ : ∀ x', (GermPullback.sheaf ⇑((siteToTop S).map W.hom) F.1).presheaf.map
      (homOfLE le_top : A x' ⟶ ⊤).op σ = GermPullback.ofSection (hV x') (s x') := by
    exact fun x' => GermPullback.ext (hs x')
  have hσ' : ∀ x', (GermPullback.sheaf ⇑((siteToTop S).map W'.hom) F.1).presheaf.map
      (homOfLE le_top : B x' ⟶ ⊤).op ((germSectionsPresheaf S X' F).map k.op σ) =
      GermPullback.ofSection (hV' x') (s x') := by
    exact fun x' => GermPullback.ext fun z => (hs x' ⟨_, z.2⟩).trans
      (GermPullback.Germs.mk_eq_mk (s x') (siteToTop_hom_apply S k z.1).symm _ _)
  refine sliceOpen_section_ext S X' H W' B hcover fun x' => ?_
  rw [map_sliceOpenIncl_germSectionsMapOutApp S X' F H φ W'
    ((germSectionsPresheaf S X' F).map k.op σ) (B x') (V x') (hV' x') (s x') (hσ' x')]
  have hr1 : H.1.map (sliceOpenIncl S X' W' (B x')).op
        (H.1.map k.op (germSectionsMapOutApp S X' F H φ W σ)) =
      H.1.map ((sliceOpenMap S X' k (B x') (A x') (fun z => z.2) ≫
          sliceOpenIncl S X' W (A x')).op)
        (germSectionsMapOutApp S X' F H φ W σ) := by
    rw [← sliceOpenMap_comp_incl S X' k (B x') (A x') (fun z => z.2), op_comp, H.1.map_comp]
    rfl
  have hr2 : H.1.map (sliceOpenMap S X' k (B x') (A x') (fun z => z.2)).op
        (H.1.map (sliceOpenToOpens S X' W (A x') (V x') (hV x')).op
          (φ.app (op (V x')) (s x'))) =
      H.1.map ((sliceOpenMap S X' k (B x') (A x') (fun z => z.2) ≫
          sliceOpenToOpens S X' W (A x') (V x') (hV x')).op) (φ.app (op (V x')) (s x')) := by
    rw [op_comp, H.1.map_comp]
    rfl
  rw [hr1, op_comp, H.1.map_comp, ConcreteCategory.comp_apply,
    map_sliceOpenIncl_germSectionsMapOutApp S X' F H φ W σ (A x') (V x') (hV x') (s x') (hσ x'),
    hr2]
  exact map_op_opensToSlice_ext S X' H _ _ _

/-- **The mapping-out morphism of the germ-model sections presheaf.** -/
def germSectionsMapOut : germSectionsPresheaf S X' F ⟶ H.1 where
  app W := TypeCat.ofHom fun σ => germSectionsMapOutApp S X' F H φ W.unop σ
  naturality {W W'} k := by
    refine ConcreteCategory.hom_ext _ _ fun σ => ?_
    exact germSectionsMapOutApp_naturality S X' F H φ k.unop σ

/-- **`germSectionsMapOut` solves the mapping-out problem**: its restriction to opens, precomposed
with the germ map, is `φ`. -/
lemma germSectionsUnit_comp_germSectionsMapOut :
    germSectionsUnit S X' F ≫
      Functor.whiskerLeft (S.opensToSlice X').1.op (germSectionsMapOut S X' F H φ) = φ := by
  refine NatTrans.ext (funext fun U => ConcreteCategory.hom_ext _ _ fun s => ?_)
  induction U with
  | op U =>
    have hval : ((Functor.whiskerLeft (S.opensToSlice X').1.op
          (germSectionsMapOut S X' F H φ)).app (op U))
          ((germSectionsUnit S X' F).app (op U) s) =
        germSectionsMapOutApp S X' F H φ ((S.opensToSlice X').1.obj U)
          (germSectionsOfSection S X' F U s) := rfl
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply, hval]
    have hA : ∀ z : (⊤ : Opens ((siteToTop S).obj ((S.opensToSlice X').1.obj U).left)),
        ((siteToTop S).map ((S.opensToSlice X').1.obj U).hom) z.1 ∈ U :=
      fun z => opensToSlice_hom_mem S (T := X') U z.1
    have hσ : (GermPullback.sheaf
        ⇑((siteToTop S).map ((S.opensToSlice X').1.obj U).hom) F.1).presheaf.map
        (homOfLE le_top :
          (⊤ : Opens ((siteToTop S).obj ((S.opensToSlice X').1.obj U).left)) ⟶ ⊤).op
        (germSectionsOfSection S X' F U s) = GermPullback.ofSection hA s :=
      GermPullback.ext fun _ => rfl
    refine map_op_injective_of_iso S X' H
      (sliceOpenTopIso S X' ((S.opensToSlice X').1.obj U)) ?_
    rw [sliceOpenTopIso_hom, map_sliceOpenIncl_germSectionsMapOutApp S X' F H φ
      ((S.opensToSlice X').1.obj U) (germSectionsOfSection S X' F U s) ⊤ U hA s hσ]
    exact map_op_opensToSlice_ext S X' H _ _ _

/-- **`germSectionsMapOut` is the only solution of the mapping-out problem.** A solution `ψ` is
determined on each object `W` over `X'` by its restrictions to the open subobjects on which the
given germ-model section is a family of germs, and there naturality of `ψ` and the defining
equation force the value. -/
lemma germSectionsMapOut_unique {ψ : germSectionsPresheaf S X' F ⟶ H.1}
    (hψ : germSectionsUnit S X' F ≫
      Functor.whiskerLeft (S.opensToSlice X').1.op ψ = φ) :
    ψ = germSectionsMapOut S X' F H φ := by
  have hunit : ∀ (U : Opens X'.obj) (s : F.1.obj (op U)),
      ψ.app (op ((S.opensToSlice X').1.obj U)) (germSectionsOfSection S X' F U s) =
        φ.app (op U) s := by
    intro U s
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hψ (op U)) s
    rwa [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  refine NatTrans.ext (funext fun W => ConcreteCategory.hom_ext _ _ fun σ => ?_)
  induction W with
  | op W =>
    classical
    choose A hmem ii V hV s hs using fun x : (siteToTop S).obj W.left =>
      GermPullback.exists_repr σ
        (show x ∈ (⊤ : Opens ((siteToTop S).obj W.left)) from trivial)
    have hcover : (⊤ : Opens ((siteToTop S).obj W.left)) ≤ iSup A := fun x _ =>
      Opens.mem_iSup.2 ⟨x, hmem x⟩
    have hσ : ∀ x, (GermPullback.sheaf ⇑((siteToTop S).map W.hom) F.1).presheaf.map
        (homOfLE le_top : A x ⟶ ⊤).op σ = GermPullback.ofSection (hV x) (s x) := by
      exact fun x => GermPullback.ext (hs x)
    have hval : (germSectionsMapOut S X' F H φ).app (op W) σ =
        germSectionsMapOutApp S X' F H φ W σ := rfl
    refine sliceOpen_section_ext S X' H W A hcover fun x => ?_
    rw [hval,
      map_sliceOpenIncl_germSectionsMapOutApp S X' F H φ W σ (A x) (V x) (hV x) (s x) (hσ x)]
    have hrepr : (germSectionsPresheaf S X' F).map (sliceOpenIncl S X' W (A x)).op σ =
        (germSectionsPresheaf S X' F).map
          (sliceOpenToOpens S X' W (A x) (V x) (hV x)).op
          (germSectionsOfSection S X' F (V x) (s x)) := by
      refine GermPullback.ext fun z => ?_
      have hmem2 : ((S.opensToSlice W.left).1.obj (A x)).hom z.1 ∈ A x :=
        opensToSlice_hom_mem S (T := W.left) (A x) z.1
      have e : ((S.opensToSlice X').1.obj (V x)).hom
            ((sliceOpenToOpens S X' W (A x) (V x) (hV x)).left z.1) =
          ((siteToTop S).map (sliceOpen S X' W (A x)).hom) z.1 := by
        rw [sliceOpenToOpens, overHomOfContinuous_left_apply]
        exact opensLift_spec S X' (V x) _ _ z.1
      refine (congrArg (fun t => σ.1 t)
        (Subtype.ext (sliceOpenIncl_left_apply S X' W (A x) z.1) :
          (⟨(sliceOpenIncl S X' W (A x)).left z.1, trivial⟩ :
            (⊤ : Opens ((siteToTop S).obj W.left))) = ii x ⟨_, hmem2⟩)).trans ?_
      exact (hs x ⟨_, hmem2⟩).trans (GermPullback.Germs.mk_eq_mk (s x) e.symm _ _)
    rw [← NatTrans.naturality_apply ψ (sliceOpenIncl S X' W (A x)).op σ, hrepr,
      NatTrans.naturality_apply ψ (sliceOpenToOpens S X' W (A x) (V x) (hV x)).op
        (germSectionsOfSection S X' F (V x) (s x)),
      hunit]

/-- **The mapping-out half of the sections formula of Stacks 09X3.** The germ-model sections
presheaf, together with the germ map, has the universal property of the inverse image along the
comparison morphism: for every sheaf `H` on the localized Zariski site of `X'` and every
morphism `φ : F ⟶ H|_{Opens X'}` there is a *unique* morphism of presheaves
`ψ : germSectionsPresheaf ⟶ H` whose restriction to opens, precomposed with the germ map, is
`φ`. -/
theorem existsUnique_germSectionsMapOut :
    ∃! ψ : germSectionsPresheaf S X' F ⟶ H.1,
      germSectionsUnit S X' F ≫ Functor.whiskerLeft (S.opensToSlice X').1.op ψ = φ :=
  ⟨germSectionsMapOut S X' F H φ, germSectionsUnit_comp_germSectionsMapOut S X' F H φ,
    fun _ hψ => germSectionsMapOut_unique S X' F H φ hψ⟩

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
