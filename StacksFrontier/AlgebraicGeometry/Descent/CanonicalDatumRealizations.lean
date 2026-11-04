module

public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalDatumInvariantOpen
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EffectiveDescentData

/-!
# The canonical descent datum of a single morphism, and its projection to the base scheme

Let `f : X ⟶ S` be a morphism of schemes and let `U` be a scheme over `S`. Two constructions in
the library produce the canonical descent datum of `U`: `AlgebraicGeometry.CanonicalDatum.datum`,
for an arbitrarily indexed family of morphisms with target `S`, and
`AlgebraicGeometry.DescentData.canonicalFunctor`, which is the pullback along `f` of the trivial
descent datum of `U` relative to `𝟙 S`. The second is the one effectivity of descent data is
stated with. Their components agree, but their gluing isomorphisms are built differently, so a
property of one is not immediately a property of the other.

The property at issue is the one characterizing the canonical datum: its gluing isomorphism
preserves the projection to `U`. This file proves it for the second construction, and deduces
that an invariant family of opens of such a datum along an fpqc covering comes from a unique open
subscheme of `U`, which is the form in which Stacks 03N0 enters the proof of Stacks 0AP4.

## Main results

* `AlgebraicGeometry.DescentData.canonicalFunctor_obj_obj` and
  `AlgebraicGeometry.DescentData.canonicalFunctor_map_hom` identify the component of the canonical
  descent datum of `U` with the fibre product `U ×_S X` and the action on morphisms with base
  change along `f`.
* `AlgebraicGeometry.DescentData.gluingPullbackIso_hom_snd_comp_iff` compares the two coordinate
  systems a gluing isomorphism is written in: the products in `Over S` that carry it, and the
  literal fibre products of schemes. It is the bridge used throughout this file.
* `AlgebraicGeometry.DescentData.canonicalFunctor_gluing_snd_originalProjection`: the gluing
  isomorphism of `AlgebraicGeometry.DescentData.canonicalFunctor` preserves the projection to the
  original scheme over `S`.
* `AlgebraicGeometry.DescentData.canonicalFunctor_existsUnique_preimage_eq_of_isInvariantOpens`
  and `AlgebraicGeometry.DescentData.canonicalFunctor_existsUnique_preimage_eq_opensRange`: an
  invariant open of the canonical descent datum of `U` relative to a one-member fpqc covering —
  given either directly or as the image of a morphism of descent data with open-immersion
  component — is the inverse image of a unique open subscheme of `U`. The specializations to a
  surjective quasi-compact flat morphism are the `_of_flat` variants.
* `AlgebraicGeometry.DescentData.canonicalFunctor_isInvariantOpens_preimage` and
  `AlgebraicGeometry.DescentData.canonicalFunctor_isInvariantOpens_iff`: conversely the inverse
  image of an open subscheme of `U` is always invariant, so for a surjective quasi-compact flat
  morphism the invariant opens of the canonical descent datum of `U` are exactly the inverse
  images of the opens of `U`.

## Implementation notes

The gluing isomorphism of a descent datum is an isomorphism of objects over the pairwise base
in `Over S`, while invariance of opens and the hypothesis of Stacks 03N0 are stated on the
literal fibre products of schemes. `AlgebraicGeometry.DescentData.gluingPullbackIso_hom_eq`
records that the transport between the two is conjugation by
`CategoryTheory.Over.prodLeftIsoPullback`, and
`AlgebraicGeometry.DescentData.gluingPullbackIso_hom_snd_comp_iff` cancels that conjugation.
Everything else is read off the specification fields of
`AlgebraicGeometry.DescentData.PullbackFunctor`, which describe the pulled-back gluing
isomorphism in the fibre-product coordinates; for the trivial descent datum relative to `𝟙 S`
the gluing isomorphism is the braiding, whose effect on the projections is immediate.

The conclusion is obtained from
`AlgebraicGeometry.CanonicalDatum.existsUnique_preimage_eq_of_preimage_eq`, which asks for the
gluing isomorphisms only as bare morphisms between the two products subject to the two
compatibilities proved here, and so applies to either realization of the canonical datum.

## References

* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry.DescentData

open CategoryTheory CategoryTheory.Limits CanonicalDatum

section Coordinates

variable {ι : Type v} {S : Scheme.{u}} {Z : ι → Scheme.{u}} {f : ∀ i, Z i ⟶ S}

/-- The gluing isomorphism of a descent datum, read on the literal fibre products of schemes, is
the conjugate of the gluing isomorphism in `Over S` by the identifications of the products in
`Over S` with those fibre products. -/
lemma gluingPullbackIso_hom_eq (D : DescentData f) (i j : ι) :
    (D.gluingPullbackIso i j).hom =
      (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).inv ≫
        ((D.gluing i j).hom.left).left ≫
        (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (D.obj j))).hom := rfl

/-- **The two coordinate systems for a gluing isomorphism agree.** A gluing isomorphism carries
the second projection of the fibre product `X i ×_S V j`, followed by a map `k`, to the first
projection of `V i ×_S X j` followed by a map `k'` exactly when the same holds for the second and
first projections of the products in `Over S`. -/
lemma gluingPullbackIso_hom_snd_comp_iff (D : DescentData f) (i j : ι) {T : Scheme.{u}}
    (k : (D.obj j).left ⟶ T) (k' : (D.obj i).left ⟶ T) :
    ((D.gluingPullbackIso i j).hom ≫ pullback.snd (f i) ((D.obj j).hom ≫ f j) ≫ k =
        pullback.fst ((D.obj i).hom ≫ f i) (f j) ≫ k') ↔
      ((D.gluing i j).hom.left.left ≫
          (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ _).left ≫ k =
        (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _).left ≫ k') := by
  have h₂ : (Over.prodLeftIsoPullback (Over.mk (f i))
        ((Over.map (f j)).obj (D.obj j))).hom ≫
      pullback.snd (f i) ((D.obj j).hom ≫ f j) ≫ k =
      (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ _).left ≫ k := by
    rw [← Category.assoc]
    exact congrArg (fun m ↦ m ≫ k) (Over.prodLeftIsoPullback_hom_snd
      (Over.mk (f i)) ((Over.map (f j)).obj (D.obj j)))
  have h₁ : (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).inv ≫
      (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _).left =
      pullback.fst ((D.obj i).hom ≫ f i) (f j) :=
    Over.prodLeftIsoPullback_inv_fst _ _
  rw [gluingPullbackIso_hom_eq, ← h₁]
  simp only [Category.assoc, h₂]
  exact Iso.cancel_iso_inv_left _ _ _

end Coordinates

variable {S X : Scheme.{u}} (f : X ⟶ S) (U : Over S)

/-- The sole component of the canonical descent datum of `U` relative to `f` is the fibre product
`U ×_S X`, viewed as a scheme over `X`. -/
lemma canonicalFunctor_obj_obj : ((canonicalFunctor f).obj U).obj () = (Over.pullback f).obj U :=
  rfl

/-- The canonical descent datum functor acts on morphisms by base change along `f`. -/
lemma canonicalFunctor_map_hom {U V : Over S} (g : U ⟶ V) :
    ((canonicalFunctor f).map g).hom () = (Over.pullback f).map g := by
  have h : 𝟙 ((Over.pullback f).obj U) ≫ (Over.pullback f).map g =
      ((canonicalFunctor f).map g).hom () ≫ 𝟙 ((Over.pullback f).obj V) :=
    (pullbackFunctor (𝟙 S) f (𝟙 S) f rfl).map ((trivialFunctor S).map g)
  rw [Category.id_comp] at h
  exact (Category.comp_id _).symm.trans h.symm

/-- The gluing isomorphism of the trivial descent datum of `U` relative to `𝟙 S` exchanges the
two projections: it is the braiding of `U` with the terminal object `Over.mk (𝟙 S)`. -/
lemma trivialFunctor_gluingPullbackIso_hom_snd (S : Scheme.{u}) (U : Over S) :
    (((trivialFunctor S).obj U).gluingPullbackIso () ()).hom ≫
        pullback.snd (𝟙 S) (U.hom ≫ 𝟙 S) = pullback.fst (U.hom ≫ 𝟙 S) (𝟙 S) := by
  rw [← Category.comp_id (pullback.snd _ _), ← Category.comp_id (pullback.fst _ _)]
  refine (gluingPullbackIso_hom_snd_comp_iff ((trivialFunctor S).obj U) () () _ _).mpr ?_
  erw [Category.comp_id, Category.comp_id, ← Over.comp_left]
  exact congrArg Over.Hom.left (prod.lift_snd _ _)

/-- The gluing isomorphism of the canonical descent datum of `U` relative to `f`, read on the
literal fibre products, preserves the projection to `U`. -/
lemma canonicalFunctor_gluingPullbackIso_hom_snd_fst :
    (((canonicalFunctor f).obj U).gluingPullbackIso () ()).hom ≫
        pullback.snd f ((((canonicalFunctor f).obj U).obj ()).hom ≫ f) ≫
          pullback.fst U.hom f =
      pullback.fst ((((canonicalFunctor f).obj U).obj ()).hom ≫ f) f ≫
        pullback.fst U.hom f := by
  have hid : ∀ {T : Scheme.{u}} (m : ((Over.pullback f).obj U).left ⟶ T),
      ((pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)).objIso
        ((trivialFunctor S).obj U)).hom.left ≫ m = m :=
    fun m ↦ Category.id_comp m
  have htgt : (pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)).targetMap
        ((trivialFunctor S).obj U) ≫ pullback.snd (𝟙 S) (U.hom ≫ 𝟙 S) =
      pullback.snd f ((((canonicalFunctor f).obj U).obj ()).hom ≫ f) ≫
        pullback.fst U.hom f := by
    refine ((pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)).targetMap_snd
      ((trivialFunctor S).obj U)).trans ?_
    rw [hid]
    rfl
  have hsrc : (pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)).sourceMap
        ((trivialFunctor S).obj U) ≫
        (((trivialFunctor S).obj U).gluingPullbackIso () ()).hom ≫
          pullback.snd (𝟙 S) (U.hom ≫ 𝟙 S) =
      pullback.fst ((((canonicalFunctor f).obj U).obj ()).hom ≫ f) f ≫
        pullback.fst U.hom f := by
    rw [trivialFunctor_gluingPullbackIso_hom_snd]
    refine ((pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)).sourceMap_fst
      ((trivialFunctor S).obj U)).trans ?_
    rw [hid]
    rfl
  have key := congrArg (fun m ↦ m ≫ pullback.snd (𝟙 S) (U.hom ≫ 𝟙 S))
    ((pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)).gluing ((trivialFunctor S).obj U))
  rwa [Category.assoc, Category.assoc, htgt, hsrc] at key

/-- **The canonical gluing isomorphism preserves the projection to the original scheme over the
base.** This is the characteristic property of the canonical descent datum, for the realization
`AlgebraicGeometry.DescentData.canonicalFunctor` used to define effectivity. -/
theorem canonicalFunctor_gluing_snd_originalProjection :
    (((canonicalFunctor f).obj U).gluing () ()).hom.left ≫ prod.snd ≫
        originalProjection U f =
      prod.fst ≫ originalProjection U f :=
  Over.OverMorphism.ext
    ((gluingPullbackIso_hom_snd_comp_iff ((canonicalFunctor f).obj U) () ()
      (pullback.fst U.hom f) (pullback.fst U.hom f)).mp
        (canonicalFunctor_gluingPullbackIso_hom_snd_fst f U))

/-- The gluing isomorphism of the canonical descent datum of `U` relative to `f` preserves the
projection to `X`, as every gluing isomorphism does. -/
lemma canonicalFunctor_gluing_snd_structureMap :
    (((canonicalFunctor f).obj U).gluing () ()).hom.left ≫ prod.snd ≫
        structureMap f ((Over.pullback f).obj U) = prod.snd :=
  gluing_hom_snd_structureMap _ () ()

/-- Two maps into an open subscheme agree on inverse images of opens when they agree after the
inclusion of the open subscheme. -/
private lemma preimage_comp_preimage_eq {A B C E : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : A ⟶ C) (h : a ≫ b ≫ c = d ≫ c) (V : E.Opens) :
    a ⁻¹ᵁ (b ⁻¹ᵁ (c ⁻¹ᵁ V)) = d ⁻¹ᵁ (c ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    Category.assoc, h]

/-- **The inverse image of an open subscheme of `U` is an invariant open of the canonical descent
datum of `U`.** This is the direction of Stacks 03N0 which holds for every morphism `f`. -/
theorem canonicalFunctor_isInvariantOpens_preimage (V : U.left.Opens) :
    ((canonicalFunctor f).obj U).IsInvariantOpens fun _ ↦ pullback.fst U.hom f ⁻¹ᵁ V := by
  refine (isInvariantOpens_iff_gluing ((canonicalFunctor f).obj U)
    fun _ ↦ pullback.fst U.hom f ⁻¹ᵁ V).mpr ?_
  rintro ⟨⟩ ⟨⟩
  exact preimage_comp_preimage_eq _ _ _ _
    (congrArg Over.Hom.left (canonicalFunctor_gluing_snd_originalProjection f U)) V

section Fpqc

/-- **An invariant open of the canonical descent datum of `U` relative to a one-member fpqc
covering is the inverse image of a unique open subscheme of `U`.** This is the application of
Stacks 03N0 inside the proof of Stacks 0AP4. -/
theorem canonicalFunctor_existsUnique_preimage_eq_of_isInvariantOpens
    (hf : Presieve.ofArrows (fun _ : Unit ↦ X) (fun _ ↦ f) ∈ Scheme.fpqcPrecoverage S)
    (W : (pullback U.hom f).Opens)
    (hW : ((canonicalFunctor f).obj U).IsInvariantOpens fun _ ↦ W) :
    ∃! U' : U.left.Opens, pullback.fst U.hom f ⁻¹ᵁ U' = W := by
  have hg := (isInvariantOpens_iff_gluing ((canonicalFunctor f).obj U) fun _ ↦ W).mp hW
  obtain ⟨U', hU', huniq⟩ :=
    CanonicalDatum.existsUnique_preimage_eq_of_preimage_eq (fun _ : Unit ↦ f) hf U
      (fun _ _ ↦ (((canonicalFunctor f).obj U).gluing () ()).hom.left)
      (fun _ _ ↦ canonicalFunctor_gluing_snd_originalProjection f U)
      (fun _ _ ↦ canonicalFunctor_gluing_snd_structureMap f U) (fun _ ↦ W)
      fun i j ↦ hg i j
  exact ⟨U', hU' (), fun V hV ↦ huniq V fun _ ↦ hV⟩

/-- **A descent datum mapping to the canonical descent datum of `U` by an open immersion
determines a unique open subscheme of `U`** with the same inverse image in `U ×_S X`. This is the
step of Stacks 0AP4 which produces the opens `U_{ij} ⊆ U_i`. -/
theorem canonicalFunctor_existsUnique_preimage_eq_opensRange
    (hf : Presieve.ofArrows (fun _ : Unit ↦ X) (fun _ ↦ f) ∈ Scheme.fpqcPrecoverage S)
    {E : DescentData (fun _ : Unit ↦ f)} (φ : E ⟶ (canonicalFunctor f).obj U)
    [IsOpenImmersion (φ.hom ()).left] :
    ∃! U' : U.left.Opens,
      pullback.fst U.hom f ⁻¹ᵁ U' = (φ.hom ()).left.opensRange := by
  have : ∀ i : Unit, IsOpenImmersion (φ.hom i).left := fun _ ↦ ‹_›
  exact canonicalFunctor_existsUnique_preimage_eq_of_isInvariantOpens f U hf _
    (isInvariantOpens_opensRange φ)

variable [Surjective f] [QuasiCompact f] [Flat f]

/-- **An invariant open of the canonical descent datum of `U` relative to a surjective
quasi-compact flat morphism is the inverse image of a unique open subscheme of `U`.** -/
theorem canonicalFunctor_existsUnique_preimage_eq_of_isInvariantOpens_of_flat
    (W : (pullback U.hom f).Opens)
    (hW : ((canonicalFunctor f).obj U).IsInvariantOpens fun _ ↦ W) :
    ∃! U' : U.left.Opens, pullback.fst U.hom f ⁻¹ᵁ U' = W :=
  canonicalFunctor_existsUnique_preimage_eq_of_isInvariantOpens f U
    (ofArrows_unit_mem_fpqcPrecoverage f) W hW

/-- **A descent datum mapping to the canonical descent datum of `U` by an open immersion
determines a unique open subscheme of `U`,** for a surjective quasi-compact flat morphism. -/
theorem canonicalFunctor_existsUnique_preimage_eq_opensRange_of_flat
    {E : DescentData (fun _ : Unit ↦ f)} (φ : E ⟶ (canonicalFunctor f).obj U)
    [IsOpenImmersion (φ.hom ()).left] :
    ∃! U' : U.left.Opens,
      pullback.fst U.hom f ⁻¹ᵁ U' = (φ.hom ()).left.opensRange :=
  canonicalFunctor_existsUnique_preimage_eq_opensRange f U
    (ofArrows_unit_mem_fpqcPrecoverage f) φ

/-- **Stacks 03N0 for the canonical descent datum of `U`.** For a surjective quasi-compact flat
morphism `f : X ⟶ S`, the invariant opens of the canonical descent datum of an `S`-scheme `U` are
exactly the inverse images of the open subschemes of `U`. -/
theorem canonicalFunctor_isInvariantOpens_iff (W : (pullback U.hom f).Opens) :
    ((canonicalFunctor f).obj U).IsInvariantOpens (fun _ ↦ W) ↔
      ∃ V : U.left.Opens, pullback.fst U.hom f ⁻¹ᵁ V = W :=
  ⟨fun hW ↦ (canonicalFunctor_existsUnique_preimage_eq_of_isInvariantOpens_of_flat f U W hW).exists,
    fun ⟨V, hV⟩ ↦ hV ▸ canonicalFunctor_isInvariantOpens_preimage f U V⟩

end Fpqc

end AlgebraicGeometry.DescentData

end

end
