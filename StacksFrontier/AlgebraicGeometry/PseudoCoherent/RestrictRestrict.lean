module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent across one level of restriction

Let `X` be a ringed space, let `U` be an open of `X` and let `V` be an open of the subspace
`X|U`. The `𝒪`-modules of the *doubly* restricted space `(X|U)|V` are compared here with the
`𝒪`-modules of the singly restricted space `X|W`, where `W` is the open of `X` corresponding
to `V`.

The comparison is an *equivalence*, and that is the point: an equivalence is additive, preserves
all limits and colimits, and takes the structure module to the structure module, so a strictly
perfect complex on `(X|U)|V` becomes a strictly perfect complex on `X|W` with no further work.

Why the comparison is needed. Pseudo-coherence of an object of `D(𝒪_X)` is phrased with opens of
`X` (Stacks 08CB), so a statement about the restriction `E|_U` unfolds to approximations over
the doubly restricted spaces `(X|U)|V`, whereas
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_derivedRestrict` consumes
approximations over opens of `X`. The whole
`AlgebraicGeometry.RingedSpace.restrictModulesOfLE` apparatus of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PseudoCoherentIso.lean` exists in order to *avoid*
double restriction and therefore does not apply: its inputs live on `X|U` whole, with the
shrinking happening internally. Mathlib has no iso of ringed spaces `(X|U)|V ≅ X|W` either —
only `AlgebraicGeometry.PresheafedSpace.restrictTopIso` and
`AlgebraicGeometry.SheafedSpace.restrictTopIso` for `V = ⊤`, and
`AlgebraicGeometry.Scheme.restrictRestrictComm` for schemes.

## Main definitions

* `AlgebraicGeometry.RingedSpace.CorrespondingOpens` bundles an open `W ≤ U` of `X` with the
  open `V` of `X|U` corresponding to it.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.homToBase` and
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.homToSub` are the two mutually inverse
  continuous maps between the carriers of `(X|U)|V` and `X|W`.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.sitesEquiv` is the induced equivalence of
  the sites of opens, bi-continuous for the open-cover topologies.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.structureSheafCompare` and
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.structureSheafCompare'` are the comparisons
  of structure sheaves of rings along that equivalence.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compareEquiv` is the resulting equivalence
  `OXMod ((X|U)|V) ≌ OXMod (X|W)`, and
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare` is its underlying functor.

## Main results

* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.image_eq_base`: the image in `X` of an open
  of `W`, read through the equivalence as an open of `V` and then pushed to `X`, is the image of
  that open of `W` in `X`. This is the one geometric fact everything else rests on.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare_obj_val_obj`,
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare_obj_val_map_forget` and
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare_map_val_app_apply` pin the
  comparison down: the sections of `Φ ℳ` over an open `Z` of `W` are the sections of `ℳ` over
  the corresponding open of `V`, with the same restriction maps and the same action on
  morphisms.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare_additive`,
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare_preservesFiniteLimits` and
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare_preservesFiniteColimits`: the
  comparison is exact.

## Implementation notes

The equivalence is Mathlib's `SheafOfModules.pushforwardPushforwardEquivalence` applied to the
equivalence of sites `AlgebraicGeometry.RingedSpace.CorrespondingOpens.sitesEquiv`. That
equivalence is built from the two continuous maps `homToBase` and `homToSub`, whose composites
are the identity *definitionally*, so the unit and the counit of the equivalence are
`CategoryTheory.Iso.refl`; and both of its directions are `CategoryTheory.Functor.IsContinuous`
by Mathlib's instance for `TopologicalSpace.Opens.map` of a continuous map, so no site-theoretic
work is needed at all.

Everything else is carried by the fact that `Opens X.carrier` is a *poset*: the two comparisons
of structure sheaves of rings are the whiskering of `X.presheaf` with a natural transformation
of functors into `Opens X.carrier` whose naturality is `Subsingleton.elim`, and the two
coherence conditions of `SheafOfModules.pushforwardPushforwardEquivalence` reduce — by
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.map_presheaf_comp` and
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.map_presheaf_comp_three_id` — to the statement
that two morphisms of `Opens X.carrier` with the same source and target are equal. This is why
the file needs no transparency flag.

Every binder is written at the `StrictlyPerfect.OXMod` spelling of the category of
`𝒪`-modules; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PushforwardOXMod.lean` for why that matters.

## References

* [Stacks Project, Lemma 20.46.9 (Tag 08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Definition 20.46.4 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe u

namespace AlgebraicGeometry.RingedSpace

/-! ### Continuity of the functors on opens that appear -/

/-- The functor on opens induced by the inclusion of an open subspace of a ringed space is
continuous for the open-cover topologies.

This is `Topology.IsOpenEmbedding.functor_isContinuous`, which Mathlib states as a lemma, made
into an instance at the spelling in which it arises here: the source site is the site of opens of
`X.restrict U.isOpenEmbedding`. -/
@[sga "4 III 1.9.2" "special case"]
public instance isContinuous_isOpenEmbedding_functor (X : RingedSpace.{u, u})
    (U : Opens X.carrier) :
    (U.isOpenEmbedding.functor).IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.carrier) :=
  U.isOpenEmbedding.functor_isContinuous

/-! ### Corresponding opens of `X` and of a subspace of `X` -/

/-- **An open of `X` contained in `U` together with the open of the subspace `X|U` that
corresponds to it.** The two conditions say that `base` is contained in `U` and that a point of
`U` lies in `sub` exactly when it lies in `base`; `sub` is then the preimage of `base` in `U`,
and `base` is the image of `sub` in `X`.

The data is bundled so that the typeclass instances the comparison needs — continuity of the
functors on opens, and the two derived categories — can be stated for it. The two ways in which
the pair arises are `AlgebraicGeometry.RingedSpace.CorrespondingOpens.ofSub`, which starts from
an open of the subspace, and `AlgebraicGeometry.RingedSpace.CorrespondingOpens.ofBase`, which
starts from an open of `X` contained in `U`. -/
public structure CorrespondingOpens (X : RingedSpace.{u, u}) (U : Opens X.carrier) where
  /-- The open of `X`. -/
  base : Opens X.carrier
  /-- The corresponding open of the subspace `X|U`. -/
  sub : Opens (X.restrict U.isOpenEmbedding).carrier
  /-- The open of `X` is contained in `U`. -/
  le_base : base ≤ U
  /-- A point of `U` lies in the open of the subspace exactly when it lies in the open of `X`. -/
  mem_sub_iff (p : U) : p ∈ sub ↔ (p : X.carrier) ∈ base

namespace CorrespondingOpens

variable {X : RingedSpace.{u, u}} {U : Opens X.carrier}

/-- The pair determined by an open `V` of the subspace `X|U`: the open of `X` is the image of `V`
under the inclusion of `U`. -/
public def ofSub (U : Opens X.carrier) (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    CorrespondingOpens X U where
  base := U.isOpenEmbedding.functor.obj V
  sub := V
  le_base := by rintro x ⟨p, -, rfl⟩; exact p.2
  mem_sub_iff p := ⟨fun hp => ⟨p, hp, rfl⟩, by rintro ⟨q, hq, hqp⟩; exact Subtype.ext hqp ▸ hq⟩

/-- `AlgebraicGeometry.RingedSpace.CorrespondingOpens.ofSub` keeps the given open of the
subspace. -/
@[simp] public theorem ofSub_sub (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) : (ofSub U V).sub = V := rfl

/-- The open of `X` attached by `AlgebraicGeometry.RingedSpace.CorrespondingOpens.ofSub` is the
image of the given open of the subspace. -/
@[simp] public theorem ofSub_base (U : Opens X.carrier)
    (V : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (ofSub U V).base = U.isOpenEmbedding.functor.obj V := rfl

/-- The pair determined by an open `W` of `X` contained in `U`: the open of the subspace is the
preimage of `W` under the inclusion of `U`. -/
public def ofBase {W : Opens X.carrier} (hWU : W ≤ U) : CorrespondingOpens X U where
  base := W
  sub := (Opens.map U.inclusion').obj W
  le_base := hWU
  mem_sub_iff _ := Iff.rfl

/-- `AlgebraicGeometry.RingedSpace.CorrespondingOpens.ofBase` keeps the given open of `X`. -/
@[simp] public theorem ofBase_base {W : Opens X.carrier} (hWU : W ≤ U) :
    (ofBase hWU).base = W := rfl

variable (D : CorrespondingOpens X U)

/-- The doubly restricted ringed space `(X|U)|V`. -/
public abbrev subspace : RingedSpace.{u, u} :=
  (X.restrict U.isOpenEmbedding).restrict D.sub.isOpenEmbedding

/-- The singly restricted ringed space `X|W`. -/
public abbrev basespace : RingedSpace.{u, u} := X.restrict D.base.isOpenEmbedding

/-! ### The homeomorphism of carriers -/

/-- The underlying map of `AlgebraicGeometry.RingedSpace.CorrespondingOpens.homToBase`: a point
of `V`, viewed inside `U` and then inside `X`, lies in `W`. -/
public def funToBase : (D.subspace).carrier → (D.basespace).carrier :=
  fun p => ⟨(show ↥U from p.1).1, (D.mem_sub_iff (show ↥U from p.1)).1 p.2⟩

/-- The underlying map of `AlgebraicGeometry.RingedSpace.CorrespondingOpens.homToSub`: a point
of `W` lies in `U`, and as such lies in `V`. -/
public def funToSub : (D.basespace).carrier → (D.subspace).carrier :=
  fun q => ⟨⟨(show ↥(D.base) from q).1, D.le_base q.2⟩,
    (D.mem_sub_iff ⟨(show ↥(D.base) from q).1, D.le_base q.2⟩).2 q.2⟩

/-- `AlgebraicGeometry.RingedSpace.CorrespondingOpens.funToBase` is continuous: it is a
restriction of the inclusion of `U` into `X` precomposed with the inclusion of `V` into `U`. -/
public theorem continuous_funToBase : Continuous D.funToBase := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp continuous_subtype_val

/-- `AlgebraicGeometry.RingedSpace.CorrespondingOpens.funToSub` is continuous. -/
public theorem continuous_funToSub : Continuous D.funToSub :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The canonical map from the carrier of the doubly restricted space `(X|U)|V` to the carrier of
`X|W`: it is the identity on the underlying points of `X`. -/
public def homToBase : (D.subspace).carrier ⟶ (D.basespace).carrier :=
  TopCat.ofHom ⟨D.funToBase, D.continuous_funToBase⟩

/-- The canonical map from the carrier of `X|W` to the carrier of the doubly restricted space
`(X|U)|V`: it is the identity on the underlying points of `X`. -/
public def homToSub : (D.basespace).carrier ⟶ (D.subspace).carrier :=
  TopCat.ofHom ⟨D.funToSub, D.continuous_funToSub⟩

/-- The two canonical maps between the carriers compose to the identity. -/
@[simp] public theorem homToBase_comp_homToSub : D.homToBase ≫ D.homToSub = 𝟙 _ := rfl

/-- The two canonical maps between the carriers compose to the identity. -/
@[simp] public theorem homToSub_comp_homToBase : D.homToSub ≫ D.homToBase = 𝟙 _ := rfl

/-! ### The equivalence of sites -/

/-- **The sites of opens of `X|W` and of `(X|U)|V` are equivalent**, by taking preimages along
the two mutually inverse continuous maps between the carriers.

The unit and the counit are `CategoryTheory.Iso.refl` because the two maps compose to the
identity definitionally, so taking preimages twice is taking the preimage along the identity. -/
public def sitesEquiv : Opens (D.basespace).carrier ≌ Opens (D.subspace).carrier where
  functor := Opens.map D.homToBase
  inverse := Opens.map D.homToSub
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Taking preimages along `AlgebraicGeometry.RingedSpace.CorrespondingOpens.homToBase` is
continuous for the open-cover topologies, by Mathlib's instance for
`TopologicalSpace.Opens.map`. -/
public instance isContinuous_sitesEquiv_functor :
    (D.sitesEquiv).functor.IsContinuous
      (Opens.grothendieckTopology (D.basespace).carrier)
      (Opens.grothendieckTopology (D.subspace).carrier) :=
  inferInstanceAs ((Opens.map D.homToBase).IsContinuous _ _)

/-- Taking preimages along `AlgebraicGeometry.RingedSpace.CorrespondingOpens.homToSub` is
continuous for the open-cover topologies. -/
public instance isContinuous_sitesEquiv_inverse :
    (D.sitesEquiv).inverse.IsContinuous
      (Opens.grothendieckTopology (D.subspace).carrier)
      (Opens.grothendieckTopology (D.basespace).carrier) :=
  inferInstanceAs ((Opens.map D.homToSub).IsContinuous _ _)

/-! ### The geometric identity -/

/-- **The geometric fact the whole comparison rests on.** Let `Z` be an open of `W`. Its preimage
in `V` has the same image in `X` as `Z` has: both consist of the points of `X` lying in `Z`.

Everything else in this file is formal, so this is the only place where the hypotheses of
`AlgebraicGeometry.RingedSpace.CorrespondingOpens` are used. -/
public theorem image_eq_base (Z : Opens (D.basespace).carrier) :
    U.isOpenEmbedding.functor.obj (D.sub.isOpenEmbedding.functor.obj
        ((Opens.map D.homToBase).obj Z)) = D.base.isOpenEmbedding.functor.obj Z := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨_, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨_, ⟨D.funToSub q, hq, rfl⟩, rfl⟩

/-- The companion of `AlgebraicGeometry.RingedSpace.CorrespondingOpens.image_eq_base` for an open
`Z` of `V`: the image in `X` of the preimage of `Z` in `W` is the image of `Z` in `X`. -/
public theorem base_image_eq_image (Z : Opens (D.subspace).carrier) :
    D.base.isOpenEmbedding.functor.obj ((Opens.map D.homToSub).obj Z) =
      U.isOpenEmbedding.functor.obj (D.sub.isOpenEmbedding.functor.obj Z) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨_, ⟨_, hq, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨D.funToBase q, hq, rfl⟩

/-! ### The comparison of structure sheaves of rings -/

/-- The inclusion of opens underlying
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.structureSheafCompare`: it is an equality by
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.image_eq_base`, and its naturality is
automatic because `Opens X.carrier` is a poset. -/
public def opensCompare :
    Opens.map D.homToBase ⋙ D.sub.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor ⟶
      D.base.isOpenEmbedding.functor where
  app Z := homOfLE (le_of_eq (D.image_eq_base Z))
  naturality _ _ _ := Subsingleton.elim _ _

/-- The inclusion of opens underlying
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.structureSheafCompare'`. -/
public def opensCompare' :
    Opens.map D.homToSub ⋙ D.base.isOpenEmbedding.functor ⟶
      D.sub.isOpenEmbedding.functor ⋙ U.isOpenEmbedding.functor where
  app Z := homOfLE (le_of_eq (D.base_image_eq_image Z))
  naturality _ _ _ := Subsingleton.elim _ _

/-- **The comparison of the structure sheaf of rings of `X|W` with the one of `(X|U)|V` pulled
back along the equivalence of sites.** It is the whiskering of `𝒪_X` with
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.opensCompare`: the sections of `𝒪_{X|W}` over
an open `Z` of `W` are the sections of `𝒪_X` over the image of `Z` in `X`, and the sections of
`𝒪_{(X|U)|V}` over the preimage of `Z` in `V` are the sections of `𝒪_X` over an open of `X`
which is *equal* to that image. -/
public def structureSheafCompare :
    structureSheafOfRings (D.basespace) ⟶
      ((D.sitesEquiv).functor.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (D.basespace).carrier)
        (Opens.grothendieckTopology (D.subspace).carrier)).obj
        (structureSheafOfRings (D.subspace)) :=
  ObjectProperty.homMk
    (Functor.whiskerRight (NatTrans.op D.opensCompare) (X.presheaf ⋙ forget₂ CommRingCat RingCat))

/-- The comparison of structure sheaves of rings in the other direction; see
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.structureSheafCompare`. -/
public def structureSheafCompare' :
    structureSheafOfRings (D.subspace) ⟶
      ((D.sitesEquiv).inverse.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (D.subspace).carrier)
        (Opens.grothendieckTopology (D.basespace).carrier)).obj
        (structureSheafOfRings (D.basespace)) :=
  ObjectProperty.homMk
    (Functor.whiskerRight (NatTrans.op D.opensCompare')
      (X.presheaf ⋙ forget₂ CommRingCat RingCat))

/-! ### The two coherence conditions -/

/-- Any morphism of `𝒪_X`-sections induced by a morphism of opens of `X` factors any composite of
two such with the same source and target: two morphisms of `Opens X.carrier` with the same source
and target are equal, because `Opens X.carrier` is a poset. -/
public theorem map_presheaf_comp {A B C : Opens X.carrier} (f : Opposite.op A ⟶ Opposite.op B)
    (g : Opposite.op B ⟶ Opposite.op C) (h : Opposite.op A ⟶ Opposite.op C) :
    (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map h) =
      (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map f) ≫
        (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map g) := by
  rw [← Functor.map_comp, ← X.presheaf.map_comp, Subsingleton.elim h (f ≫ g)]

/-- A composite of three morphisms of `𝒪_X`-sections induced by morphisms of opens of `X` which
returns to its source is the identity; see
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.map_presheaf_comp`. -/
public theorem map_presheaf_comp_three_id {A B C : Opens X.carrier}
    (f : Opposite.op A ⟶ Opposite.op B) (g : Opposite.op B ⟶ Opposite.op C)
    (k : Opposite.op C ⟶ Opposite.op A) :
    (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map f) ≫
      ((forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map g) ≫
        (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map k)) = 𝟙 _ := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← X.presheaf.map_comp, ← X.presheaf.map_comp,
    Subsingleton.elim (f ≫ g ≫ k) (𝟙 _), CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

/-- The first coherence condition of `SheafOfModules.pushforwardPushforwardEquivalence` for the
two comparisons of structure sheaves of rings. Both sides are induced by morphisms of opens of
`X` with the same source and target. -/
public theorem structureSheafCompare_counit :
    Functor.whiskerRight (NatTrans.op (D.sitesEquiv).counit)
        (structureSheafOfRings (D.subspace)).obj =
      (D.structureSheafCompare').hom ≫
        (D.sitesEquiv).inverse.op.whiskerLeft (D.structureSheafCompare).hom := by
  ext Z : 2
  show (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map _) =
    (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map _) ≫
      (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map _)
  exact map_presheaf_comp _ _ _

/-- The second coherence condition of `SheafOfModules.pushforwardPushforwardEquivalence` for the
two comparisons of structure sheaves of rings. -/
public theorem structureSheafCompare_unit :
    (D.structureSheafCompare).hom ≫
        (D.sitesEquiv).functor.op.whiskerLeft (D.structureSheafCompare').hom ≫
          Functor.whiskerRight (NatTrans.op (D.sitesEquiv).unit)
            (structureSheafOfRings (D.basespace)).obj =
      𝟙 (structureSheafOfRings (D.basespace)).obj := by
  ext Z : 2
  show (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map _) ≫
      ((forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map _) ≫
        (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map _)) = 𝟙 _
  exact map_presheaf_comp_three_id _ _ _

/-! ### The comparison equivalence -/

/-- **The `𝒪`-modules of the doubly restricted space `(X|U)|V` are equivalent to the
`𝒪`-modules of the singly restricted space `X|W`.**

It is Mathlib's `SheafOfModules.pushforwardPushforwardEquivalence` for the equivalence of sites
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.sitesEquiv` and the two comparisons of
structure sheaves of rings. -/
public def compareEquiv : OXMod.{u, u} (D.subspace) ≌ OXMod.{u, u} (D.basespace) :=
  SheafOfModules.pushforwardPushforwardEquivalence (D.sitesEquiv) (D.structureSheafCompare)
    (D.structureSheafCompare') (D.structureSheafCompare_counit) (D.structureSheafCompare_unit)

/-- **The comparison functor** `Φ : OXMod ((X|U)|V) ⥤ OXMod (X|W)`, the functor underlying
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.compareEquiv`. -/
public def compare : OXMod.{u, u} (D.subspace) ⥤ OXMod.{u, u} (D.basespace) :=
  (D.compareEquiv).functor

/-- The comparison functor is the functor of the comparison equivalence, by definition. -/
public theorem compareEquiv_functor : (D.compareEquiv).functor = D.compare := rfl

/-- The comparison functor is an equivalence. -/
public instance compare_isEquivalence : (D.compare).IsEquivalence :=
  inferInstanceAs ((D.compareEquiv).functor.IsEquivalence)

/-! ### Pinning the comparison down -/

/-- **The sections of `Φ ℳ` over an open `Z` of `W` are the sections of `ℳ` over the preimage of
`Z` in `V`**, with the scalars restricted along
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.structureSheafCompare`.

Without a statement of this kind the comparison functor would be opaque: the three abstract
properties below are shared by many functors, including useless ones. -/
public theorem compare_obj_val_obj (M : OXMod.{u, u} (D.subspace))
    (Z : (Opens (D.basespace).carrier)ᵒᵖ) :
    ((D.compare).obj M).val.obj Z =
      (ModuleCat.restrictScalars ((D.structureSheafCompare).hom.app Z).hom).obj
        (M.val.obj ((Opens.map D.homToBase).op.obj Z)) := rfl

/-- The restriction maps of `Φ ℳ` are those of `ℳ`, read on the preimages: the underlying
presheaf of abelian groups of `Φ ℳ` is that of `ℳ` precomposed with taking preimages. -/
public theorem compare_obj_val_map_forget (M : OXMod.{u, u} (D.subspace))
    {Z Z' : (Opens (D.basespace).carrier)ᵒᵖ} (k : Z ⟶ Z') :
    (forget₂ _ AddCommGrpCat).map (((D.compare).obj M).val.map k) =
      M.val.presheaf.map ((Opens.map D.homToBase).map k.unop).op := rfl

/-- **`Φ` acts on a morphism by the same functions on sections**: the value of `Φ f` on a section
over an open `Z` of `W` is the value of `f` on that section, read over the preimage of `Z`
in `V`. -/
public theorem compare_map_val_app_apply {M N : OXMod.{u, u} (D.subspace)} (f : M ⟶ N)
    (Z : (Opens (D.basespace).carrier)ᵒᵖ)
    (x : ((D.compare).obj M).val.obj Z) :
    ((D.compare).map f).val.app Z x = f.val.app ((Opens.map D.homToBase).op.obj Z) x := rfl

/-! ### Exactness -/

/-- The comparison functor is additive: it does not change the sections of a morphism, hence not
the sum of two morphisms. -/
public instance compare_additive : (D.compare).Additive where
  map_add := by
    intros
    ext _ _
    rfl

/-- The comparison functor preserves finite limits, being an equivalence. -/
public instance compare_preservesFiniteLimits : PreservesFiniteLimits (D.compare) :=
  inferInstance

/-- The comparison functor preserves finite colimits, being an equivalence. -/
public instance compare_preservesFiniteColimits : PreservesFiniteColimits (D.compare) :=
  inferInstance

end CorrespondingOpens

end AlgebraicGeometry.RingedSpace

end
