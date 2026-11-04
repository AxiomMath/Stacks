module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumSectionsPushout
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.CanonicalFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetSingleMorphism
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.OpenSubDatum

/-!
# Invariant opens of a canonical descent datum

Let `f : X ⟶ S` be a surjective flat quasi-compact morphism of schemes and let `U` be a scheme
over `S`. The canonical descent datum of `U` relative to `f` carries the scheme `U ×_S X` over
`X`, and that scheme projects to `U`. An open of `U ×_S X` invariant under the gluing isomorphism
of the canonical datum is the preimage of a unique open of `U`; conversely every such preimage is
invariant, and the restriction of the canonical datum to it is the canonical datum of that open
of `U`, hence effective. Isomorphisms of such restrictions descend to isomorphisms over `S` of
the corresponding opens of the base.

## Main definitions

* `AlgebraicGeometry.DescentData.canonicalOverIso` identifies the scheme over `X` underlying
  the canonical descent datum of `U : Over S` with the base change `U ×_S X`.
* `AlgebraicGeometry.DescentData.canonicalProj` is the projection `U ×_S X ⟶ U` of that scheme
  to `U`, that is the base change of `f` along the structure morphism of `U`.
* `AlgebraicGeometry.DescentData.canonicalOpenSubHom` is the morphism of canonical descent
  data induced by an open subscheme of `U`. Its component is an open immersion, and its image
  is the preimage of that open under the projection.
* `AlgebraicGeometry.DescentData.canonicalRestrictOpenPreimageIso` identifies the canonical
  datum of an open `W₀ ⊆ U` with the restriction of the canonical datum of `U` to the preimage
  of `W₀`.
* `AlgebraicGeometry.DescentData.descendIso` descends an isomorphism of canonical descent data
  to an isomorphism of the schemes over `S` they come from. It is characterised by
  `AlgebraicGeometry.DescentData.canonicalFunctor_map_descendIso_hom` and
  `AlgebraicGeometry.DescentData.descendIso_eq`.
* `AlgebraicGeometry.DescentData.opensIsoOfRestrictOpenPreimageIso` descends an isomorphism of
  the restrictions of two canonical data to the preimages of opens `W₀ ⊆ U` and `W₀' ⊆ U'` to an
  isomorphism of `W₀` and `W₀'` over `S`.

## Main results

* `AlgebraicGeometry.DescentData.canonical_transition_comp_canonicalProj`: **the gluing
  isomorphism of a canonical descent datum commutes with the projection to `U`.**
* `AlgebraicGeometry.DescentData.isPullback_canonicalProj`: the projection to `U` and the
  structure morphism to `X` exhibit the canonical datum's scheme as `U ×_S X`.
* `AlgebraicGeometry.DescentData.isPullback_transition_canonicalProj`: **`V ×_S X` is the
  self-fibre product `V ×_U V`,** where `V` is the canonical datum's scheme, with the first
  leg given by the gluing isomorphism followed by the projection of `X ×_S V` to `V` and the
  second leg by the projection of `V ×_S X` to `V`.
* `AlgebraicGeometry.DescentData.preimage_transition_snd_eq_preimage_fst`: for an arbitrary
  descent datum, an invariant open has equal preimages along those two legs.
* `AlgebraicGeometry.DescentData.existsUnique_opens_preimage_canonicalProj_eq`: **an invariant
  open of a canonical descent datum is the preimage of a unique open of `U`.**
* `AlgebraicGeometry.DescentData.isTransitionInvariant_canonicalProj_preimage`: conversely,
  every preimage of an open of `U` is invariant, for any `f`.
* `AlgebraicGeometry.DescentData.isEffective_restrictOpen_canonical`: **the restriction of a
  canonical descent datum to an invariant open is effective.**
* `AlgebraicGeometry.DescentData.existsUnique_map_eq_of_restrictOpen_hom`: **a morphism of the
  restricted data descends to exactly one morphism of the descended opens.**
* `AlgebraicGeometry.DescentData.exists_opens_iso_of_restrictOpen_iso`: **isomorphic
  restrictions of canonical data give isomorphic descended opens.**

## Implementation notes

The identification of `V ×_S X` with `V ×_U V` is `CategoryTheory.IsPullback.of_right'` applied
to the horizontal pasting `V ×_S X ⟶ V ⟶ X` over `V ⟶ U ⟶ S`, whose outer square is the
defining pullback of `V ×_S X` and whose right-hand square is
`AlgebraicGeometry.DescentData.isPullback_canonicalProj`.

`AlgebraicGeometry.DescentData.canonicalOverIso` is definitionally the identity, so
`canonicalProj f U` is `CategoryTheory.Limits.pullback.fst U.hom f` on the nose
(`AlgebraicGeometry.DescentData.canonicalProj_eq_pullbackFst`). The instances on the projection
are stated with `inferInstanceAs` at the domain `pullback U.hom f`: instance search does not find
them at the domain `(DescentDatum.over ((canonicalFunctor f).obj U)).left`.

## References

* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentData

variable {S X : Scheme.{u}}

/-! ### The gluing isomorphism of a trivial descent datum -/

/-- The gluing isomorphism of the trivial descent datum of `U : Over S`, relative to the
one-member family `{𝟙 S}`, followed by the projection of `S ×_S U` to `U`, is the projection
of `U ×_S S` to `U`. It is the braiding, so it exchanges the two factors. -/
theorem trivialFunctor_gluingPullbackIso_hom_comp_snd (U : Over S) :
    (((trivialFunctor S).obj U).gluingPullbackIso () ()).hom ≫
        pullback.snd (𝟙 S) (U.hom ≫ 𝟙 S) =
      pullback.fst (U.hom ≫ 𝟙 S) (𝟙 S) := by
  have h2 := Over.prodLeftIsoPullback_hom_snd (Over.mk (𝟙 S)) ((Over.map (𝟙 S)).obj U)
  have h3 := Over.prodLeftIsoPullback_inv_fst ((Over.map (𝟙 S)).obj U) (Over.mk (𝟙 S))
  have key : (Over.prodLeftIsoPullback ((Over.map (𝟙 S)).obj U) (Over.mk (𝟙 S))).inv ≫
      (prod.braiding ((Over.map (𝟙 S)).obj U) (Over.mk (𝟙 S))).hom.left ≫
        ((Over.prodLeftIsoPullback (Over.mk (𝟙 S)) ((Over.map (𝟙 S)).obj U)).hom ≫
          pullback.snd (Over.mk (𝟙 S)).hom ((Over.map (𝟙 S)).obj U).hom) =
      pullback.fst ((Over.map (𝟙 S)).obj U).hom (Over.mk (𝟙 S)).hom := by
    rwa [h2, ← Over.comp_left, prod.braiding_hom, prod.lift_snd]
  have h1 : (((trivialFunctor S).obj U).gluingPullbackIso () ()).hom =
      (Over.prodLeftIsoPullback ((Over.map (𝟙 S)).obj U) (Over.mk (𝟙 S))).inv ≫
        (prod.braiding ((Over.map (𝟙 S)).obj U) (Over.mk (𝟙 S))).hom.left ≫
          (Over.prodLeftIsoPullback (Over.mk (𝟙 S)) ((Over.map (𝟙 S)).obj U)).hom := rfl
  rwa [h1, Category.assoc, Category.assoc]

/-! ### The canonical descent datum's scheme, and its projection to the base -/

/-- The scheme over `X` underlying the canonical descent datum of `U : Over S` relative to
`f : X ⟶ S`, identified with the base change `U ×_S X`. -/
def canonicalOverIso (f : X ⟶ S) (U : Over S) :
    DescentDatum.over ((canonicalFunctor f).obj U) ≅ (Over.pullback f).obj U :=
  (pullbackFunctor (𝟙 S) f (𝟙 S) f rfl).objIso ((trivialFunctor S).obj U)

/-- The projection `U ×_S X ⟶ U` of the scheme underlying the canonical descent datum of
`U : Over S` to `U`. It is the base change of `f` along the structure morphism of `U`,
transported along `AlgebraicGeometry.DescentData.canonicalOverIso`. -/
def canonicalProj (f : X ⟶ S) (U : Over S) :
    (DescentDatum.over ((canonicalFunctor f).obj U)).left ⟶ U.left :=
  (canonicalOverIso f U).hom.left ≫ pullback.fst U.hom f

/-- `AlgebraicGeometry.DescentData.canonicalProj` is the first projection of `U ×_S X`, read
through `AlgebraicGeometry.DescentData.canonicalOverIso`. -/
lemma canonicalProj_eq (f : X ⟶ S) (U : Over S) :
    canonicalProj f U = (canonicalOverIso f U).hom.left ≫ pullback.fst U.hom f := rfl

/-- The projection of the canonical descent datum of `U` to `U` is, on the nose, the first
projection of the fibre product `U ×_S X`: the identification
`AlgebraicGeometry.DescentData.canonicalOverIso` is the identity. -/
lemma canonicalProj_eq_pullbackFst (f : X ⟶ S) (U : Over S) :
    canonicalProj f U = pullback.fst U.hom f := rfl

/-- The identification of the canonical datum's scheme with `U ×_S X` is an isomorphism of
schemes, not merely of schemes over `X`. -/
instance isIso_canonicalOverIso_hom_left (f : X ⟶ S) (U : Over S) :
    IsIso ((canonicalOverIso f U).hom.left) :=
  inferInstanceAs (IsIso ((Over.forget X).map (canonicalOverIso f U).hom))

/-- The projection to `U` is surjective, being the base change of a surjective morphism. -/
instance surjective_canonicalProj (f : X ⟶ S) [Surjective f] (U : Over S) :
    Surjective (canonicalProj f U) :=
  inferInstanceAs (Surjective (pullback.fst U.hom f))

/-- The projection to `U` is flat, being the base change of a flat morphism. -/
instance flat_canonicalProj (f : X ⟶ S) [Flat f] (U : Over S) :
    Flat (canonicalProj f U) :=
  inferInstanceAs (Flat (pullback.fst U.hom f))

/-- The projection to `U` is quasi-compact, being the base change of a quasi-compact
morphism. -/
instance quasiCompact_canonicalProj (f : X ⟶ S) [QuasiCompact f] (U : Over S) :
    QuasiCompact (canonicalProj f U) :=
  inferInstanceAs (QuasiCompact (pullback.fst U.hom f))

/-! ### The gluing isomorphism of a canonical datum commutes with the projection -/

/-- **The gluing isomorphism of a canonical descent datum commutes with the projection to
`U`.** Composing `φ` with the projection of `X ×_S V` to `V` and then with `V ⟶ U` is the
projection of `V ×_S X` to `V` followed by `V ⟶ U`. -/
theorem canonical_transition_comp_canonicalProj (f : X ⟶ S) (U : Over S) :
    (DescentDatum.transitionPullbackIso ((canonicalFunctor f).obj U)).hom ≫
        pullback.snd f ((DescentDatum.over ((canonicalFunctor f).obj U)).hom ≫ f) ≫
          canonicalProj f U =
      pullback.fst ((DescentDatum.over ((canonicalFunctor f).obj U)).hom ≫ f) f ≫
        canonicalProj f U := by
  have hg : (DescentDatum.transitionPullbackIso ((canonicalFunctor f).obj U)).hom ≫
      (pullbackFunctor (𝟙 S) f (𝟙 S) f rfl).targetMap ((trivialFunctor S).obj U) =
        (pullbackFunctor (𝟙 S) f (𝟙 S) f rfl).sourceMap ((trivialFunctor S).obj U) ≫
          (((trivialFunctor S).obj U).gluingPullbackIso () ()).hom :=
    (pullbackFunctor (𝟙 S) f (𝟙 S) f rfl).gluing ((trivialFunctor S).obj U)
  have hsf : (pullbackFunctor (𝟙 S) f (𝟙 S) f rfl).sourceMap
        ((trivialFunctor S).obj U) ≫ pullback.fst (U.hom ≫ 𝟙 S) (𝟙 S) =
      pullback.fst ((DescentDatum.over ((canonicalFunctor f).obj U)).hom ≫ f) f ≫
        canonicalProj f U :=
    (pullbackFunctor (𝟙 S) f (𝟙 S) f rfl).sourceMap_fst ((trivialFunctor S).obj U)
  have hts : (pullbackFunctor (𝟙 S) f (𝟙 S) f rfl).targetMap
        ((trivialFunctor S).obj U) ≫ pullback.snd (𝟙 S) (U.hom ≫ 𝟙 S) =
      pullback.snd f ((DescentDatum.over ((canonicalFunctor f).obj U)).hom ≫ f) ≫
        canonicalProj f U :=
    (pullbackFunctor (𝟙 S) f (𝟙 S) f rfl).targetMap_snd ((trivialFunctor S).obj U)
  rw [← hts, ← Category.assoc, hg, Category.assoc,
    trivialFunctor_gluingPullbackIso_hom_comp_snd, hsf]

/-! ### `V ×_S X` is the self-fibre product of `V` over `U` -/

/-- The scheme underlying the canonical descent datum of `U` is the fibre product `U ×_S X`:
its projection to `U` and its structure morphism to `X` form a pullback square over `S`. -/
theorem isPullback_canonicalProj (f : X ⟶ S) (U : Over S) :
    IsPullback (DescentDatum.over ((canonicalFunctor f).obj U)).hom (canonicalProj f U)
      f U.hom := by
  have hw : (canonicalOverIso f U).hom.left ≫ pullback.snd U.hom f =
      (DescentDatum.over ((canonicalFunctor f).obj U)).hom := Over.w (canonicalOverIso f U).hom
  refine (IsPullback.of_iso_pullback ⟨?_⟩
    ((Over.forget X).mapIso (canonicalOverIso f U)) rfl hw).flip
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ f) hw

/-- **`V ×_S X` is the self-fibre product `V ×_U V`,** for `V` the scheme underlying the
canonical descent datum of `U`. The leg to the first copy of `V` is the gluing isomorphism
followed by the projection of `X ×_S V` to `V`; the leg to the second copy is the projection
of `V ×_S X` to `V`. -/
theorem isPullback_transition_canonicalProj (f : X ⟶ S) (U : Over S) :
    IsPullback
      ((DescentDatum.transitionPullbackIso ((canonicalFunctor f).obj U)).hom ≫
        pullback.snd f ((DescentDatum.over ((canonicalFunctor f).obj U)).hom ≫ f))
      (pullback.fst ((DescentDatum.over ((canonicalFunctor f).obj U)).hom ≫ f) f)
      (canonicalProj f U) (canonicalProj f U) := by
  set C := (canonicalFunctor f).obj U with hC
  set c := (DescentDatum.over C).hom with hc
  set p := canonicalProj f U with hp
  have hpb : IsPullback c p f U.hom := isPullback_canonicalProj f U
  have hs : IsPullback (pullback.snd (c ≫ f) f) (pullback.fst (c ≫ f) f) f (p ≫ U.hom) := by
    rw [← hpb.w]
    exact (IsPullback.of_hasPullback (c ≫ f) f).flip
  have hmain := IsPullback.of_right' hs hpb
  have heq : hpb.lift (pullback.snd (c ≫ f) f) (pullback.fst (c ≫ f) f ≫ p)
        (by rw [hs.w, Category.assoc]) =
      (DescentDatum.transitionPullbackIso C).hom ≫ pullback.snd f (c ≫ f) := by
    refine hpb.hom_ext ?_ ?_
    · rw [hpb.lift_fst, Category.assoc]
      exact (DescentDatum.transitionPullbackIso_hom_comp_pullbackSnd C).symm
    · rw [hpb.lift_snd, Category.assoc]
      exact (canonical_transition_comp_canonicalProj f U).symm
  rwa [heq] at hmain

/-! ### Invariance as the equality of two preimages -/

variable {f : X ⟶ S}

/-- The preimage of a set under a composite of morphisms of schemes is the iterated preimage. -/
private theorem preimage_comp_base {Y Z T : Scheme.{u}} (g : Y ⟶ Z) (h : Z ⟶ T) (A : Set T) :
    (g ≫ h).base ⁻¹' A = g.base ⁻¹' (h.base ⁻¹' A) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]

/-- **Invariance of an open under the gluing isomorphism gives an equality of preimages.** For
an arbitrary descent datum `(V, φ)`, if an open `W ⊆ V` is invariant then its preimage along `φ`
followed by the projection of `X ×_S V` to `V` agrees with its preimage along the projection of
`V ×_S X` to `V`. -/
theorem preimage_transition_snd_eq_preimage_fst (D : DescentDatum f)
    (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W) :
    (D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f)).base ⁻¹' (W : Set _) =
      (pullback.fst (D.over.hom ≫ f) f).base ⁻¹' (W : Set _) := by
  have hinj : Function.Injective D.transitionPullbackIso.hom.base :=
    (Scheme.homeoOfIso D.transitionPullbackIso).injective
  have hset : D.transitionPullbackIso.hom.base ''
      ((pullback.fst (D.over.hom ≫ f) f).base ⁻¹' (W : Set _)) =
      (pullback.snd f (D.over.hom ≫ f)).base ⁻¹' (W : Set _) := by
    simpa only [Scheme.Hom.coe_image, TopologicalSpace.Opens.map_coe] using
      TopologicalSpace.Opens.ext_iff.mp hW
  have h := congrArg (fun T ↦ D.transitionPullbackIso.hom.base ⁻¹' T) hset
  simp only [Set.preimage_image_eq _ hinj] at h
  rw [preimage_comp_base, ← h]

/-! ### The descended open -/

/-- **An invariant open of a canonical descent datum descends to the base.** Let `f : X ⟶ S`
be surjective, flat and quasi-compact and let `U` be a scheme over `S`. An open `W` of the
scheme `U ×_S X` underlying the canonical descent datum of `U` which is invariant under the
canonical gluing isomorphism is the preimage of exactly one open of `U`. -/
theorem existsUnique_opens_preimage_canonicalProj_eq (f : X ⟶ S)
    [Surjective f] [Flat f] [QuasiCompact f] (U : Over S)
    (W : (DescentDatum.over ((canonicalFunctor f).obj U)).left.Opens)
    (hW : DescentDatum.IsTransitionInvariant ((canonicalFunctor f).obj U) W) :
    ∃! W₀ : U.left.Opens, canonicalProj f U ⁻¹ᵁ W₀ = W := by
  have hpb := isPullback_transition_canonicalProj f U
  have hesurj : Function.Surjective hpb.isoPullback.hom.base :=
    (Scheme.homeoOfIso hpb.isoPullback).surjective
  refine existsUnique_opens_preimage_eq_of_flat_of_quasiCompact_of_surjective
    (canonicalProj f U) W (hesurj.preimage_injective ?_)
  rw [← preimage_comp_base, ← preimage_comp_base, hpb.isoPullback_hom_fst,
    hpb.isoPullback_hom_snd]
  exact preimage_transition_snd_eq_preimage_fst ((canonicalFunctor f).obj U) W hW

/-! ### The open sub-datum of a canonical datum cut out by an open of the base -/

/-- **The identification of the canonical datum's scheme with `U ×_S X` is natural** in
`U : Over S`. -/
theorem canonicalOverIso_naturality (f : X ⟶ S) {U' U : Over S} (j : U' ⟶ U) :
    (canonicalOverIso f U').hom ≫ (Over.pullback f).map j =
      ((canonicalFunctor f).map j).hom () ≫ (canonicalOverIso f U).hom :=
  (pullbackFunctor (𝟙 S) f (𝟙 S) f rfl).map ((trivialFunctor S).map j)

/-- The inverse of `AlgebraicGeometry.DescentData.canonicalOverIso` is an isomorphism of
schemes, not merely of schemes over `X`. -/
instance isIso_canonicalOverIso_inv_left (f : X ⟶ S) (U : Over S) :
    IsIso ((canonicalOverIso f U).inv.left) :=
  inferInstanceAs (IsIso ((Over.forget X).map (canonicalOverIso f U).inv))

/-- The morphism of canonical descent data induced by an open subscheme `W₀ ⊆ U`: the
canonical datum of `W₀`, viewed as a scheme over `S`, maps to the canonical datum of `U`. -/
abbrev canonicalOpenSubHom (f : X ⟶ S) (U : Over S) (W₀ : U.left.Opens) :
    (canonicalFunctor f).obj (Over.mk (W₀.ι ≫ U.hom)) ⟶ (canonicalFunctor f).obj U :=
  (canonicalFunctor f).map (Over.homMk W₀.ι)

/-- The component of `AlgebraicGeometry.DescentData.canonicalOpenSubHom`, read on the fibre
products: it is the base change of the open immersion `W₀ ⟶ U` along `f`. -/
theorem canonicalOpenSubHom_hom_left_comp (f : X ⟶ S) (U : Over S) (W₀ : U.left.Opens) :
    ((canonicalOpenSubHom f U W₀).hom ()).left ≫ (canonicalOverIso f U).hom.left =
      (canonicalOverIso f (Over.mk (W₀.ι ≫ U.hom))).hom.left ≫
        pullback.map (W₀.ι ≫ U.hom) f U.hom f W₀.ι (𝟙 X) (𝟙 S) (by simp) (by simp) := by
  have hnat := canonicalOverIso_naturality f
    (Over.homMk W₀.ι : Over.mk (W₀.ι ≫ U.hom) ⟶ U)
  have hm : ((Over.pullback f).map (Over.homMk W₀.ι : Over.mk (W₀.ι ≫ U.hom) ⟶ U)).left =
      pullback.map (W₀.ι ≫ U.hom) f U.hom f W₀.ι (𝟙 X) (𝟙 S) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [pullback.map]
  have h := congrArg Over.Hom.left hnat
  rw [Over.comp_left, Over.comp_left, hm] at h
  exact h.symm

/-- `AlgebraicGeometry.DescentData.canonicalOpenSubHom_hom_left_comp` with the isomorphism
moved to the other side. -/
theorem canonicalOpenSubHom_hom_left (f : X ⟶ S) (U : Over S) (W₀ : U.left.Opens) :
    ((canonicalOpenSubHom f U W₀).hom ()).left =
      (canonicalOverIso f (Over.mk (W₀.ι ≫ U.hom))).hom.left ≫
        pullback.map (W₀.ι ≫ U.hom) f U.hom f W₀.ι (𝟙 X) (𝟙 S) (by simp) (by simp) ≫
          (canonicalOverIso f U).inv.left := by
  have hBB : (canonicalOverIso f U).hom.left ≫ (canonicalOverIso f U).inv.left =
      𝟙 (DescentDatum.over ((canonicalFunctor f).obj U)).left := by
    rw [← Over.comp_left, Iso.hom_inv_id]
    rfl
  rw [← Category.assoc, ← canonicalOpenSubHom_hom_left_comp, Category.assoc, hBB,
    Category.comp_id]

/-- **The component of `AlgebraicGeometry.DescentData.canonicalOpenSubHom` is an open
immersion.** -/
instance isOpenImmersion_canonicalOpenSubHom (f : X ⟶ S) (U : Over S) (W₀ : U.left.Opens) :
    IsOpenImmersion (((canonicalOpenSubHom f U W₀).hom ()).left) := by
  have hoi : IsOpenImmersion
      (pullback.map (W₀.ι ≫ U.hom) f U.hom f W₀.ι (𝟙 X) (𝟙 S) (by simp) (by simp)) := by
    have h := pullbackRightPullbackFstIso_hom_comp_pullbackMap W₀.ι U.hom f (by simp) (by simp)
    have h2 : pullback.map (W₀.ι ≫ U.hom) f U.hom f W₀.ι (𝟙 X) (𝟙 S) (by simp) (by simp) =
        (pullbackRightPullbackFstIso U.hom f W₀.ι).inv ≫
          pullback.snd W₀.ι (pullback.fst U.hom f) := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [h2]; infer_instance
  rw [canonicalOpenSubHom_hom_left]
  infer_instance

/-- **The image of `AlgebraicGeometry.DescentData.canonicalOpenSubHom` is the preimage of
`W₀`.** The canonical datum of an open `W₀ ⊆ U` sits inside the canonical datum of `U` as the
preimage of `W₀` under the projection to `U`. -/
theorem range_canonicalOpenSubHom_hom_left (f : X ⟶ S) (U : Over S) (W₀ : U.left.Opens) :
    Set.range (((canonicalOpenSubHom f U W₀).hom ()).left).base =
      ↑(canonicalProj f U ⁻¹ᵁ W₀) := by
  have hrange := range_pullbackMapFst_of_isOpenImmersion W₀.ι U.hom (W₀.ι ≫ U.hom) f rfl
    (by simp) (by simp)
  have hsurj : Function.Surjective
      ((canonicalOverIso f (Over.mk (W₀.ι ≫ U.hom))).hom.left).base :=
    (Scheme.homeoOfIso ((Over.forget X).mapIso
      (canonicalOverIso f (Over.mk (W₀.ι ≫ U.hom))))).surjective
  have himg : Set.image (((canonicalOverIso f U).inv.left).base) =
      Set.preimage (((canonicalOverIso f U).hom.left).base) := by
    refine Set.image_eq_preimage_of_inverse ?_ ?_
    · exact (Scheme.homeoOfIso ((Over.forget X).mapIso (canonicalOverIso f U))).symm_apply_apply
    · exact (Scheme.homeoOfIso ((Over.forget X).mapIso (canonicalOverIso f U))).apply_symm_apply
  rw [canonicalOpenSubHom_hom_left, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, hrange, himg, Scheme.Opens.opensRange_ι, canonicalProj_eq,
    Scheme.Hom.comp_preimage]
  rfl

/-- `AlgebraicGeometry.DescentData.range_canonicalOpenSubHom_hom_left` as an equality of open
subschemes. -/
theorem opensRange_canonicalOpenSubHom_hom_left (f : X ⟶ S) (U : Over S)
    (W₀ : U.left.Opens) :
    ((canonicalOpenSubHom f U W₀).hom ()).left.opensRange = canonicalProj f U ⁻¹ᵁ W₀ :=
  TopologicalSpace.Opens.ext (range_canonicalOpenSubHom_hom_left f U W₀)

/-- **The preimage of an open of `U` is invariant**, for any `f`. This is the converse of
`AlgebraicGeometry.DescentData.existsUnique_opens_preimage_canonicalProj_eq`. -/
theorem isTransitionInvariant_canonicalProj_preimage (f : X ⟶ S) (U : Over S)
    (W₀ : U.left.Opens) :
    DescentDatum.IsTransitionInvariant ((canonicalFunctor f).obj U)
      (canonicalProj f U ⁻¹ᵁ W₀) := by
  rw [← opensRange_canonicalOpenSubHom_hom_left f U W₀]
  exact DescentDatum.isTransitionInvariant_opensRange (canonicalOpenSubHom f U W₀)

/-! ### The restriction of a canonical datum to an invariant open is effective -/

/-- Restriction to an invariant open depends only on the open, the invariance being a
proposition. -/
theorem restrictOpen_congr_opens {f : X ⟶ S} (D : DescentDatum f)
    {W₁ W₂ : D.over.left.Opens} (h : W₁ = W₂) (h₁ : D.IsTransitionInvariant W₁)
    (h₂ : D.IsTransitionInvariant W₂) : D.restrictOpen W₁ h₁ = D.restrictOpen W₂ h₂ := by
  subst h
  rfl

/-- **The restriction of a canonical descent datum to the preimage of an open of the base is
the canonical datum of that open.** The canonical datum of `W₀ ⊆ U`, viewed as a scheme over
`S`, is isomorphic as a descent datum to the restriction of the canonical datum of `U` to
`p^{-1}(W₀)`, for `p` the projection to `U`. -/
def canonicalRestrictOpenPreimageIso (f : X ⟶ S) (U : Over S) (W₀ : U.left.Opens) :
    (canonicalFunctor f).obj (Over.mk (W₀.ι ≫ U.hom)) ≅
      DescentDatum.restrictOpen ((canonicalFunctor f).obj U) (canonicalProj f U ⁻¹ᵁ W₀)
        (isTransitionInvariant_canonicalProj_preimage f U W₀) :=
  DescentDatum.restrictOpenIsoOpensRange (canonicalOpenSubHom f U W₀) ≪≫
    eqToIso (restrictOpen_congr_opens ((canonicalFunctor f).obj U)
      (opensRange_canonicalOpenSubHom_hom_left f U W₀) _ _)

/-- **The restriction of a canonical descent datum to an invariant open is effective.** For
`f : X ⟶ S` surjective, flat and quasi-compact and `U` a scheme over `S`, every open of
`U ×_S X` invariant under the canonical gluing isomorphism carries a descent datum which is
the canonical datum of an open of `U`, hence is effective. -/
theorem isEffective_restrictOpen_canonical (f : X ⟶ S)
    [Surjective f] [Flat f] [QuasiCompact f] (U : Over S)
    (W : (DescentDatum.over ((canonicalFunctor f).obj U)).left.Opens)
    (hW : DescentDatum.IsTransitionInvariant ((canonicalFunctor f).obj U) W) :
    IsEffective (DescentDatum.restrictOpen ((canonicalFunctor f).obj U) W hW) := by
  obtain ⟨W₀, hW₀, -⟩ := existsUnique_opens_preimage_canonicalProj_eq f U W hW
  subst hW₀
  exact (DescentDatum.isEffective_canonical f (Over.mk (W₀.ι ≫ U.hom))).ofIso
    (canonicalRestrictOpenPreimageIso f U W₀)

/-! ### Descending isomorphisms of canonical descent data -/

/-- **The canonical functor is faithful.** Two morphisms of schemes over `S` whose canonical
descent data agree are equal. -/
theorem canonicalFunctor_map_injective (f : X ⟶ S)
    [Surjective f] [Flat f] [QuasiCompact f] {W W' : Over S} {a b : W ⟶ W'}
    (h : (canonicalFunctor f).map a = (canonicalFunctor f).map b) : a = b :=
  (existsUnique_canonicalFunctor_map_eq f ((canonicalFunctor f).map b)).unique h rfl

/-- **An isomorphism of canonical descent data descends to an isomorphism of the schemes over
`S` it comes from.** For `f : X ⟶ S` surjective, flat and quasi-compact and an isomorphism `e`
of the canonical data of `W` and `W'`, this is the isomorphism `W ≅ W'` whose hom and inverse are
the unique morphisms sent by the canonical functor to `e.hom` and `e.inv`. -/
def descendIso (f : X ⟶ S) [Surjective f] [Flat f] [QuasiCompact f] {W W' : Over S}
    (e : (canonicalFunctor f).obj W ≅ (canonicalFunctor f).obj W') : W ≅ W' where
  hom := (existsUnique_canonicalFunctor_map_eq f e.hom).choose
  inv := (existsUnique_canonicalFunctor_map_eq f e.inv).choose
  hom_inv_id := canonicalFunctor_map_injective f <| by
    rw [Functor.map_comp, (existsUnique_canonicalFunctor_map_eq f e.hom).choose_spec.1,
      (existsUnique_canonicalFunctor_map_eq f e.inv).choose_spec.1, e.hom_inv_id,
      CategoryTheory.Functor.map_id]
  inv_hom_id := canonicalFunctor_map_injective f <| by
    rw [Functor.map_comp, (existsUnique_canonicalFunctor_map_eq f e.inv).choose_spec.1,
      (existsUnique_canonicalFunctor_map_eq f e.hom).choose_spec.1, e.inv_hom_id,
      CategoryTheory.Functor.map_id]

/-- The defining property of `AlgebraicGeometry.DescentData.descendIso`: the canonical functor
sends the descended isomorphism back to the one it was built from. -/
@[simp]
theorem canonicalFunctor_map_descendIso_hom (f : X ⟶ S)
    [Surjective f] [Flat f] [QuasiCompact f] {W W' : Over S}
    (e : (canonicalFunctor f).obj W ≅ (canonicalFunctor f).obj W') :
    (canonicalFunctor f).map (descendIso f e).hom = e.hom :=
  (existsUnique_canonicalFunctor_map_eq f e.hom).choose_spec.1

/-- The inverse of `AlgebraicGeometry.DescentData.descendIso` is characterised in the same way:
the canonical functor sends it to the inverse of the given isomorphism. -/
@[simp]
theorem canonicalFunctor_map_descendIso_inv (f : X ⟶ S)
    [Surjective f] [Flat f] [QuasiCompact f] {W W' : Over S}
    (e : (canonicalFunctor f).obj W ≅ (canonicalFunctor f).obj W') :
    (canonicalFunctor f).map (descendIso f e).inv = e.inv :=
  (existsUnique_canonicalFunctor_map_eq f e.inv).choose_spec.1

/-- `AlgebraicGeometry.DescentData.descendIso` is the *only* isomorphism over `S` whose
canonical datum is the given one, so any isomorphism with that property is it. -/
theorem descendIso_eq (f : X ⟶ S) [Surjective f] [Flat f] [QuasiCompact f] {W W' : Over S}
    {e : (canonicalFunctor f).obj W ≅ (canonicalFunctor f).obj W'} (i : W ≅ W')
    (hi : (canonicalFunctor f).map i.hom = e.hom) : i = descendIso f e :=
  Iso.ext ((existsUnique_canonicalFunctor_map_eq f e.hom).unique hi
    (canonicalFunctor_map_descendIso_hom f e))

/-- Descending the canonical datum of an isomorphism of schemes over `S` returns that
isomorphism. -/
@[simp]
theorem descendIso_mapIso (f : X ⟶ S) [Surjective f] [Flat f] [QuasiCompact f] {W W' : Over S}
    (i : W ≅ W') : descendIso f ((canonicalFunctor f).mapIso i) = i :=
  (descendIso_eq f i rfl).symm

/-- **An isomorphism of restrictions to preimages descends to an isomorphism of the opens.**
Let `f : X ⟶ S` be surjective, flat and quasi-compact, let `U` and `U'` be schemes over `S` and
let `W₀ ⊆ U` and `W₀' ⊆ U'` be opens. An isomorphism of the restrictions of the canonical data of
`U` and `U'` to the preimages of `W₀` and `W₀'` gives an isomorphism, over `S`, of `W₀` and `W₀'`
viewed as schemes over `S`. -/
def opensIsoOfRestrictOpenPreimageIso (f : X ⟶ S)
    [Surjective f] [Flat f] [QuasiCompact f] {U U' : Over S}
    (W₀ : U.left.Opens) (W₀' : U'.left.Opens)
    (e : DescentDatum.restrictOpen ((canonicalFunctor f).obj U)
          (canonicalProj f U ⁻¹ᵁ W₀)
          (isTransitionInvariant_canonicalProj_preimage f U W₀) ≅
        DescentDatum.restrictOpen ((canonicalFunctor f).obj U')
          (canonicalProj f U' ⁻¹ᵁ W₀')
          (isTransitionInvariant_canonicalProj_preimage f U' W₀')) :
    Over.mk (W₀.ι ≫ U.hom) ≅ Over.mk (W₀'.ι ≫ U'.hom) :=
  descendIso f (canonicalRestrictOpenPreimageIso f U W₀ ≪≫ e ≪≫
    (canonicalRestrictOpenPreimageIso f U' W₀').symm)

/-- **Isomorphic restrictions of canonical data give isomorphic descended opens.** Let
`f : X ⟶ S` be surjective, flat and quasi-compact, let `U` and `U'` be schemes over `S` and
let `W`, `W'` be invariant opens of their canonical descent data. An isomorphism of the two
restricted descent data descends to an isomorphism, over `S`, of the two opens of `U` and `U'`
that `W` and `W'` come from. -/
theorem exists_opens_iso_of_restrictOpen_iso (f : X ⟶ S)
    [Surjective f] [Flat f] [QuasiCompact f] {U U' : Over S}
    {W : (DescentDatum.over ((canonicalFunctor f).obj U)).left.Opens}
    {W' : (DescentDatum.over ((canonicalFunctor f).obj U')).left.Opens}
    (hW : DescentDatum.IsTransitionInvariant ((canonicalFunctor f).obj U) W)
    (hW' : DescentDatum.IsTransitionInvariant ((canonicalFunctor f).obj U') W')
    (e : DescentDatum.restrictOpen ((canonicalFunctor f).obj U) W hW ≅
      DescentDatum.restrictOpen ((canonicalFunctor f).obj U') W' hW') :
    ∃ (W₀ : U.left.Opens) (W₀' : U'.left.Opens),
      canonicalProj f U ⁻¹ᵁ W₀ = W ∧ canonicalProj f U' ⁻¹ᵁ W₀' = W' ∧
        Nonempty (Over.mk (W₀.ι ≫ U.hom) ≅ Over.mk (W₀'.ι ≫ U'.hom)) := by
  obtain ⟨W₀, hW₀, -⟩ := existsUnique_opens_preimage_canonicalProj_eq f U W hW
  obtain ⟨W₀', hW₀', -⟩ := existsUnique_opens_preimage_canonicalProj_eq f U' W' hW'
  subst hW₀ hW₀'
  exact ⟨W₀, W₀', rfl, rfl, ⟨opensIsoOfRestrictOpenPreimageIso f W₀ W₀' e⟩⟩

/-- **A morphism of the restricted data descends to exactly one morphism of the descended
opens.** For `f : X ⟶ S` surjective, flat and quasi-compact and opens `W₀ ⊆ U`, `W₀' ⊆ U'`, a
morphism of the restrictions of the canonical data of `U` and `U'` to the preimages of `W₀` and
`W₀'`, transported along `AlgebraicGeometry.DescentData.canonicalRestrictOpenPreimageIso`, is the
image under the canonical functor of exactly one morphism of `W₀` to `W₀'` over `S`. -/
theorem existsUnique_map_eq_of_restrictOpen_hom (f : X ⟶ S)
    [Surjective f] [Flat f] [QuasiCompact f] (U U' : Over S)
    (W₀ : U.left.Opens) (W₀' : U'.left.Opens)
    (g : DescentDatum.restrictOpen ((canonicalFunctor f).obj U) (canonicalProj f U ⁻¹ᵁ W₀)
          (isTransitionInvariant_canonicalProj_preimage f U W₀) ⟶
        DescentDatum.restrictOpen ((canonicalFunctor f).obj U') (canonicalProj f U' ⁻¹ᵁ W₀')
          (isTransitionInvariant_canonicalProj_preimage f U' W₀')) :
    ∃! h : Over.mk (W₀.ι ≫ U.hom) ⟶ Over.mk (W₀'.ι ≫ U'.hom),
      (canonicalFunctor f).map h =
        (canonicalRestrictOpenPreimageIso f U W₀).hom ≫ g ≫
          (canonicalRestrictOpenPreimageIso f U' W₀').inv :=
  existsUnique_canonicalFunctor_map_eq f _

end DescentData

end AlgebraicGeometry

end
