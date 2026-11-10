module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantBaseChange

/-!
# Groupoid schemes which are disjoint unions, and their invariant rings

A groupoid scheme `G` is the disjoint union of two groupoid schemes `G₁` and `G₂` when it
receives morphisms from them which exhibit its object scheme as the coproduct of the two object
schemes and its arrow scheme as the coproduct of the two arrow schemes. Since a morphism of
groupoid schemes already carries compatibility with source, target, identity and composition,
this says exactly that the quintuple `(U, R, s, t, c)` of `G` is the disjoint union of the
quintuples of `G₁` and of `G₂`.

On global functions a disjoint union becomes a product, and the subring of invariant functions
of `G` becomes the product of the two subrings of invariant functions: the canonical ring
homomorphism `invariantRing G →+* invariantRing G₁ × invariantRing G₂`, given by pullback of
functions along the two object maps, is an isomorphism. Dually the spectrum of the invariant
ring of `G` is the disjoint union of the spectra of the two invariant rings, compatibly with
the canonical morphisms from the object schemes.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.IsCoproductDecomposition` says that a pair of morphisms of
  groupoid schemes into `G` exhibits `G` as the disjoint union of their sources.
* `AlgebraicGeometry.GroupoidScheme.CoproductDecomposition` bundles such a decomposition with
  the two groupoid schemes and the two morphisms.
* `AlgebraicGeometry.GroupoidScheme.invariantRingProdHom` is the canonical homomorphism from
  the invariant ring of `G` to the product of the invariant rings of `G₁` and `G₂`.
* `AlgebraicGeometry.GroupoidScheme.IsCoproductDecomposition.invariantRingProdEquiv` is that
  homomorphism, promoted to a ring isomorphism for a decomposition.
* `AlgebraicGeometry.GroupoidScheme.IsCoproductDecomposition.invariantSpectrumCoprodIso`
  presents the spectrum of the invariant ring of `G` as the binary coproduct of the spectra of
  the two invariant rings.

## Main results

* `AlgebraicGeometry.bijective_prod_appTop`: global functions on a scheme presented as the
  disjoint union of two others are the product of the global functions on the two pieces.
* `AlgebraicGeometry.GroupoidScheme.IsCoproductDecomposition.mem_invariantRing_iff`: a function
  on the object scheme of `G` is invariant exactly when both of its restrictions are.
* `AlgebraicGeometry.GroupoidScheme.IsCoproductDecomposition.isIso_coprod_desc_invariantSpectrum`:
  the invariant spectrum of `G` is the disjoint union of the two invariant spectra.
* `AlgebraicGeometry.GroupoidScheme.IsCoproductDecomposition` has
  `mapObjects_comp_objectsToInvariantSpectrum_left` and its companion on the right: the two
  canonical morphisms to the invariant spectrum of `G` factor through the coproduct injections.

## Implementation notes

The two coproduct conditions are stated on the underlying schemes, as the assertion that the
morphism out of a binary coproduct of schemes is an isomorphism. This is the same idiom used
for the decompositions of
`AlgebraicGeometry.GroupoidScheme.exists_finite_openClosed_subgroupoid`, and it is equivalent
to the corresponding condition in `CategoryTheory.Over S` because the forgetful functor from
the over category creates colimits.

The ring isomorphism is produced from an explicitly given ring homomorphism rather than from an
existence statement, and `invariantRingProdHom_apply_fst_coe` and
`invariantRingProdHom_apply_snd_coe` record that it is pullback of functions along the two
object maps.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry

/-! ### Global functions on a disjoint union of two schemes -/

private theorem isIso_appTop {X Z : Scheme.{u}} (f : X ⟶ Z) [IsIso f] : IsIso f.appTop :=
  ⟨(inv f).appTop,
    by rw [← Scheme.Hom.comp_appTop, IsIso.inv_hom_id, Scheme.Hom.id_appTop],
    by rw [← Scheme.Hom.comp_appTop, IsIso.hom_inv_id, Scheme.Hom.id_appTop]⟩

/-- The global functions on a binary coproduct of schemes, with the two pullback maps, are a
product of the global functions on the two summands. -/
private def coprodSectionsFanIsLimit (X Y : Scheme.{u}) :
    IsLimit (BinaryFan.mk ((coprod.inl : X ⟶ X ⨿ Y).appTop)
      ((coprod.inr : Y ⟶ X ⨿ Y).appTop)) :=
  IsLimit.ofIsoLimit (limit.isLimit (pair Γ(X, ⊤) Γ(Y, ⊤)))
    (Cone.ext (Scheme.coprodPresheafObjIso (X := X) (Y := Y) ⊤).symm (by
      rintro ⟨⟨⟩⟩
      · exact ((Iso.inv_comp_eq _).2 (Scheme.coprodPresheafObjIso_hom_fst ⊤).symm).symm
      · exact ((Iso.inv_comp_eq _).2 (Scheme.coprodPresheafObjIso_hom_snd ⊤).symm).symm))

private theorem bijective_coprodSectionsProd (X Y : Scheme.{u}) :
    Function.Bijective (RingHom.prod (coprod.inl : X ⟶ X ⨿ Y).appTop.hom
      (coprod.inr : Y ⟶ X ⨿ Y).appTop.hom) := by
  have h1 := (coprodSectionsFanIsLimit X Y).conePointUniqueUpToIso_hom_comp
    (CommRingCat.prodFanIsLimit Γ(X, ⊤) Γ(Y, ⊤)) ⟨WalkingPair.left⟩
  have h2 := (coprodSectionsFanIsLimit X Y).conePointUniqueUpToIso_hom_comp
    (CommRingCat.prodFanIsLimit Γ(X, ⊤) Γ(Y, ⊤)) ⟨WalkingPair.right⟩
  have key : RingHom.prod (coprod.inl : X ⟶ X ⨿ Y).appTop.hom
      (coprod.inr : Y ⟶ X ⨿ Y).appTop.hom =
      ((coprodSectionsFanIsLimit X Y).conePointUniqueUpToIso
        (CommRingCat.prodFanIsLimit Γ(X, ⊤) Γ(Y, ⊤))).hom.hom := by
    ext a
    · exact (ConcreteCategory.congr_hom h1 a).symm
    · exact (ConcreteCategory.congr_hom h2 a).symm
  rw [key]
  exact ConcreteCategory.bijective_of_isIso _

/-- If the morphism out of the binary coproduct of two schemes over a third is an isomorphism,
then the global functions on the target are the product of the global functions on the two
pieces, by pullback along the two morphisms. -/
theorem bijective_prod_appTop {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsIso (coprod.desc f g)] :
    Function.Bijective (RingHom.prod f.appTop.hom g.appTop.hom) := by
  have hf : f.appTop = (coprod.desc f g).appTop ≫ (coprod.inl : X ⟶ X ⨿ Y).appTop := by
    rw [← Scheme.Hom.comp_appTop, coprod.inl_desc]
  have hg : g.appTop = (coprod.desc f g).appTop ≫ (coprod.inr : Y ⟶ X ⨿ Y).appTop := by
    rw [← Scheme.Hom.comp_appTop, coprod.inr_desc]
  have key : RingHom.prod f.appTop.hom g.appTop.hom =
      (RingHom.prod (coprod.inl : X ⟶ X ⨿ Y).appTop.hom
        (coprod.inr : Y ⟶ X ⨿ Y).appTop.hom).comp (coprod.desc f g).appTop.hom := by
    ext a
    · exact congrArg (fun k : Γ(Z, ⊤) ⟶ Γ(X, ⊤) => k.hom a) hf
    · exact congrArg (fun k : Γ(Z, ⊤) ⟶ Γ(Y, ⊤) => k.hom a) hg
  rw [key, RingHom.coe_comp]
  have := isIso_appTop (coprod.desc f g)
  exact (bijective_coprodSectionsProd X Y).comp (ConcreteCategory.bijective_of_isIso _)

namespace GroupoidScheme

variable {S : Scheme.{u}}

/-! ### Pullback of invariant functions along a morphism of groupoid schemes -/

/-- Pullback of functions along a morphism of groupoid schemes intertwines the two source
maps on global functions. -/
theorem mapArrows_appTop_comp_sourceMap {G G₁ : GroupoidScheme S}
    (F : GroupoidScheme.Hom G₁ G) :
    F.mapArrows.left.appTop.hom.comp (sourceMap G) =
      (sourceMap G₁).comp F.mapObjects.left.appTop.hom := by
  have h := congrArg (fun k : G₁.arrows.left ⟶ G.objects.left => k.appTop.hom)
    F.map_source_left
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact h

/-- Pullback of functions along a morphism of groupoid schemes intertwines the two target
maps on global functions. -/
theorem mapArrows_appTop_comp_targetMap {G G₁ : GroupoidScheme S}
    (F : GroupoidScheme.Hom G₁ G) :
    F.mapArrows.left.appTop.hom.comp (targetMap G) =
      (targetMap G₁).comp F.mapObjects.left.appTop.hom := by
  have h := congrArg (fun k : G₁.arrows.left ⟶ G.objects.left => k.appTop.hom)
    F.map_target_left
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact h

/-! ### Decomposition of a groupoid scheme as a disjoint union -/

/-- A pair of morphisms of groupoid schemes `F₁ : G₁ ⟶ G` and `F₂ : G₂ ⟶ G` exhibits `G` as the
disjoint union of `G₁` and `G₂` when the induced morphisms out of the binary coproducts of the
object schemes and of the arrow schemes are isomorphisms. Compatibility of the decomposition
with source, target, identity and composition is already carried by the two morphisms. -/
structure IsCoproductDecomposition {G G₁ G₂ : GroupoidScheme S}
    (F₁ : GroupoidScheme.Hom G₁ G) (F₂ : GroupoidScheme.Hom G₂ G) : Prop where
  /-- The object scheme is the disjoint union of the two object schemes. -/
  isIso_objects : IsIso (coprod.desc F₁.mapObjects.left F₂.mapObjects.left)
  /-- The arrow scheme is the disjoint union of the two arrow schemes. -/
  isIso_arrows : IsIso (coprod.desc F₁.mapArrows.left F₂.mapArrows.left)

/-- A presentation of a groupoid scheme as the disjoint union of two groupoid schemes. -/
structure CoproductDecomposition (G : GroupoidScheme S) where
  /-- The first summand. -/
  left : GroupoidScheme S
  /-- The second summand. -/
  right : GroupoidScheme S
  /-- The morphism from the first summand. -/
  inl : GroupoidScheme.Hom left G
  /-- The morphism from the second summand. -/
  inr : GroupoidScheme.Hom right G
  /-- The two morphisms exhibit `G` as the disjoint union of the two summands. -/
  isCoproductDecomposition : IsCoproductDecomposition inl inr

variable {G G₁ G₂ : GroupoidScheme S} {F₁ : GroupoidScheme.Hom G₁ G}
  {F₂ : GroupoidScheme.Hom G₂ G}

/-- Global functions on the object scheme of a disjoint union are the product of the global
functions on the two object schemes. -/
theorem IsCoproductDecomposition.bijective_objects (h : IsCoproductDecomposition F₁ F₂) :
    Function.Bijective (RingHom.prod F₁.mapObjects.left.appTop.hom
      F₂.mapObjects.left.appTop.hom) :=
  have := h.isIso_objects
  bijective_prod_appTop _ _

/-- Global functions on the arrow scheme of a disjoint union are the product of the global
functions on the two arrow schemes. -/
theorem IsCoproductDecomposition.bijective_arrows (h : IsCoproductDecomposition F₁ F₂) :
    Function.Bijective (RingHom.prod F₁.mapArrows.left.appTop.hom
      F₂.mapArrows.left.appTop.hom) :=
  have := h.isIso_arrows
  bijective_prod_appTop _ _

/-- A function on the object scheme of a disjoint union of two groupoid schemes is invariant
exactly when both of its pullbacks are. -/
theorem IsCoproductDecomposition.mem_invariantRing_iff (h : IsCoproductDecomposition F₁ F₂)
    (a : Γ(G.objects.left, ⊤)) :
    a ∈ invariantRing G ↔ F₁.mapObjects.left.appTop.hom a ∈ invariantRing G₁ ∧
      F₂.mapObjects.left.appTop.hom a ∈ invariantRing G₂ := by
  refine ⟨fun ha => ⟨(invariantRingMap F₁ ⟨a, ha⟩).2, (invariantRingMap F₂ ⟨a, ha⟩).2⟩,
    fun ⟨h₁, h₂⟩ => ?_⟩
  have hs₁ := RingHom.congr_fun (mapArrows_appTop_comp_sourceMap F₁) a
  have ht₁ := RingHom.congr_fun (mapArrows_appTop_comp_targetMap F₁) a
  have hs₂ := RingHom.congr_fun (mapArrows_appTop_comp_sourceMap F₂) a
  have ht₂ := RingHom.congr_fun (mapArrows_appTop_comp_targetMap F₂) a
  simp only [RingHom.coe_comp, Function.comp_apply] at hs₁ ht₁ hs₂ ht₂
  change sourceMap G a = targetMap G a
  refine h.bijective_arrows.1 (Prod.ext ?_ ?_)
  · change F₁.mapArrows.left.appTop.hom (sourceMap G a) = _
    rw [hs₁, h₁]
    exact ht₁.symm
  · change F₂.mapArrows.left.appTop.hom (sourceMap G a) = _
    rw [hs₂, h₂]
    exact ht₂.symm

/-! ### The invariant ring of a disjoint union -/

/-- The canonical homomorphism from the invariant ring of `G` to the product of the invariant
rings of two groupoid schemes mapping to it, given by the two induced maps on invariant
rings. -/
def invariantRingProdHom (F₁ : GroupoidScheme.Hom G₁ G) (F₂ : GroupoidScheme.Hom G₂ G) :
    invariantRing G →+* invariantRing G₁ × invariantRing G₂ :=
  RingHom.prod (invariantRingMap F₁) (invariantRingMap F₂)

/-- The first component of `invariantRingProdHom` is the map induced by the first morphism. -/
@[simp]
theorem fst_comp_invariantRingProdHom :
    (RingHom.fst (invariantRing G₁) (invariantRing G₂)).comp (invariantRingProdHom F₁ F₂) =
      invariantRingMap F₁ := rfl

/-- The second component of `invariantRingProdHom` is the map induced by the second
morphism. -/
@[simp]
theorem snd_comp_invariantRingProdHom :
    (RingHom.snd (invariantRing G₁) (invariantRing G₂)).comp (invariantRingProdHom F₁ F₂) =
      invariantRingMap F₂ := rfl

/-- The first component of `invariantRingProdHom F₁ F₂ a` is the pullback of `a` along the first
object map. -/
@[simp]
theorem invariantRingProdHom_apply_fst_coe (a : invariantRing G) :
    ((invariantRingProdHom F₁ F₂ a).1 : Γ(G₁.objects.left, ⊤)) =
      F₁.mapObjects.left.appTop.hom a := rfl

/-- The second component of `invariantRingProdHom F₁ F₂ a` is the pullback of `a` along the second
object map. -/
@[simp]
theorem invariantRingProdHom_apply_snd_coe (a : invariantRing G) :
    ((invariantRingProdHom F₁ F₂ a).2 : Γ(G₂.objects.left, ⊤)) =
      F₂.mapObjects.left.appTop.hom a := rfl

/-- For a decomposition of `G` as a disjoint union, pullback of invariant functions along the
two object maps is bijective onto the product of the two invariant rings. -/
theorem IsCoproductDecomposition.bijective_invariantRingProdHom
    (h : IsCoproductDecomposition F₁ F₂) :
    Function.Bijective (invariantRingProdHom F₁ F₂) := by
  refine ⟨fun a b hab => ?_, fun p => ?_⟩
  · refine Subtype.ext (h.bijective_objects.1 (Prod.ext ?_ ?_))
    · exact congrArg
        (fun p : invariantRing G₁ × invariantRing G₂ => (p.1 : Γ(G₁.objects.left, ⊤))) hab
    · exact congrArg
        (fun p : invariantRing G₁ × invariantRing G₂ => (p.2 : Γ(G₂.objects.left, ⊤))) hab
  · obtain ⟨a, ha⟩ := h.bijective_objects.2 ((p.1 : Γ(G₁.objects.left, ⊤)),
      (p.2 : Γ(G₂.objects.left, ⊤)))
    have ha₁ : F₁.mapObjects.left.appTop.hom a = (p.1 : Γ(G₁.objects.left, ⊤)) :=
      congrArg Prod.fst ha
    have ha₂ : F₂.mapObjects.left.appTop.hom a = (p.2 : Γ(G₂.objects.left, ⊤)) :=
      congrArg Prod.snd ha
    exact ⟨⟨a, (h.mem_invariantRing_iff a).2 ⟨ha₁ ▸ p.1.2, ha₂ ▸ p.2.2⟩⟩,
      Prod.ext (Subtype.ext ha₁) (Subtype.ext ha₂)⟩

/-- **The invariant ring of a disjoint union is a product.** For a decomposition of a groupoid
scheme `G` as the disjoint union of `G₁` and `G₂`, pullback of functions along the two object
maps is a ring isomorphism from the invariant ring of `G` onto the product of the invariant
rings of `G₁` and `G₂`. -/
def IsCoproductDecomposition.invariantRingProdEquiv (h : IsCoproductDecomposition F₁ F₂) :
    invariantRing G ≃+* invariantRing G₁ × invariantRing G₂ :=
  RingEquiv.ofBijective _ h.bijective_invariantRingProdHom

/-- The isomorphism `invariantRingProdEquiv` acts as `invariantRingProdHom`. -/
@[simp]
theorem IsCoproductDecomposition.invariantRingProdEquiv_apply
    (h : IsCoproductDecomposition F₁ F₂) (a : invariantRing G) :
    h.invariantRingProdEquiv a = invariantRingProdHom F₁ F₂ a := rfl

/-- The ring homomorphism underlying `invariantRingProdEquiv` is `invariantRingProdHom`. -/
theorem IsCoproductDecomposition.invariantRingProdEquiv_toRingHom
    (h : IsCoproductDecomposition F₁ F₂) :
    (h.invariantRingProdEquiv : invariantRing G →+* invariantRing G₁ × invariantRing G₂) =
      invariantRingProdHom F₁ F₂ := rfl

/-- Pulling back the inverse image of a pair `p` under `invariantRingProdEquiv` along the first
object map gives the first component of `p`. -/
@[simp]
theorem IsCoproductDecomposition.appTop_invariantRingProdEquiv_symm_fst
    (h : IsCoproductDecomposition F₁ F₂) (p : invariantRing G₁ × invariantRing G₂) :
    F₁.mapObjects.left.appTop.hom (h.invariantRingProdEquiv.symm p) =
      (p.1 : Γ(G₁.objects.left, ⊤)) :=
  congrArg (fun q : invariantRing G₁ × invariantRing G₂ => (q.1 : Γ(G₁.objects.left, ⊤)))
    (h.invariantRingProdEquiv.apply_symm_apply p)

/-- Pulling back the inverse image of a pair `p` under `invariantRingProdEquiv` along the second
object map gives the second component of `p`. -/
@[simp]
theorem IsCoproductDecomposition.appTop_invariantRingProdEquiv_symm_snd
    (h : IsCoproductDecomposition F₁ F₂) (p : invariantRing G₁ × invariantRing G₂) :
    F₂.mapObjects.left.appTop.hom (h.invariantRingProdEquiv.symm p) =
      (p.2 : Γ(G₂.objects.left, ⊤)) :=
  congrArg (fun q : invariantRing G₁ × invariantRing G₂ => (q.2 : Γ(G₂.objects.left, ⊤)))
    (h.invariantRingProdEquiv.apply_symm_apply p)

/-! ### Compatibility with the morphism to the invariant spectrum -/

/-- **The invariant spectrum of a disjoint union is a disjoint union.** For a decomposition of
a groupoid scheme `G` as the disjoint union of `G₁` and `G₂`, the spectrum of the invariant ring
of `G` is the disjoint union of the spectra of the invariant rings of `G₁` and of `G₂`, through
the spectra of the two induced maps on invariant rings. -/
theorem IsCoproductDecomposition.isIso_coprod_desc_invariantSpectrum
    (h : IsCoproductDecomposition F₁ F₂) :
    IsIso (coprod.desc (Spec.map (CommRingCat.ofHom (invariantRingMap F₁)))
      (Spec.map (CommRingCat.ofHom (invariantRingMap F₂)))) := by
  have hdesc : coprod.desc
      (Spec.map (CommRingCat.ofHom (RingHom.fst (invariantRing G₁) (invariantRing G₂))))
      (Spec.map (CommRingCat.ofHom (RingHom.snd (invariantRing G₁) (invariantRing G₂)))) =
      coprodSpec (invariantRing G₁) (invariantRing G₂) := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc, coprodSpec_inl]
    · rw [coprod.inr_desc, coprodSpec_inr]
  have h1 : CommRingCat.ofHom (invariantRingMap F₁) =
      CommRingCat.ofHom (invariantRingProdHom F₁ F₂) ≫
        CommRingCat.ofHom (RingHom.fst (invariantRing G₁) (invariantRing G₂)) := rfl
  have h2 : CommRingCat.ofHom (invariantRingMap F₂) =
      CommRingCat.ofHom (invariantRingProdHom F₁ F₂) ≫
        CommRingCat.ofHom (RingHom.snd (invariantRing G₁) (invariantRing G₂)) := rfl
  rw [h1, h2, Spec.map_comp, Spec.map_comp, ← coprod.desc_comp, hdesc]
  have : IsIso (CommRingCat.ofHom (invariantRingProdHom F₁ F₂)) :=
    h.invariantRingProdEquiv.toCommRingCatIso.isIso_hom
  infer_instance

/-- The spectrum of the invariant ring of `G`, presented as the binary coproduct of the spectra
of the invariant rings of the two summands. -/
def IsCoproductDecomposition.invariantSpectrumCoprodIso (h : IsCoproductDecomposition F₁ F₂) :
    (Spec (.of (invariantRing G₁)) ⨿ Spec (.of (invariantRing G₂))) ≅
      Spec (.of (invariantRing G)) :=
  @asIso _ _ _ _ _ h.isIso_coprod_desc_invariantSpectrum

/-- Composing the first coproduct injection with `invariantSpectrumCoprodIso` gives the spectrum of
the map on invariant rings induced by the first morphism. -/
@[reassoc (attr := simp)]
theorem IsCoproductDecomposition.inl_invariantSpectrumCoprodIso_hom
    (h : IsCoproductDecomposition F₁ F₂) :
    coprod.inl ≫ h.invariantSpectrumCoprodIso.hom =
      Spec.map (CommRingCat.ofHom (invariantRingMap F₁)) :=
  coprod.inl_desc _ _

/-- Composing the second coproduct injection with `invariantSpectrumCoprodIso` gives the spectrum
of the map on invariant rings induced by the second morphism. -/
@[reassoc (attr := simp)]
theorem IsCoproductDecomposition.inr_invariantSpectrumCoprodIso_hom
    (h : IsCoproductDecomposition F₁ F₂) :
    coprod.inr ≫ h.invariantSpectrumCoprodIso.hom =
      Spec.map (CommRingCat.ofHom (invariantRingMap F₂)) :=
  coprod.inr_desc _ _

/-- The object scheme of the first summand maps to the invariant spectrum of `G` through the
first coproduct injection of `invariantSpectrumCoprodIso`. -/
theorem IsCoproductDecomposition.mapObjects_comp_objectsToInvariantSpectrum_left
    (h : IsCoproductDecomposition F₁ F₂) :
    F₁.mapObjects.left ≫ objectsToInvariantSpectrum G =
      objectsToInvariantSpectrum G₁ ≫ coprod.inl ≫ h.invariantSpectrumCoprodIso.hom := by
  rw [h.inl_invariantSpectrumCoprodIso_hom, mapObjects_comp_objectsToInvariantSpectrum]

/-- The object scheme of the second summand maps to the invariant spectrum of `G` through the
second coproduct injection of `invariantSpectrumCoprodIso`. -/
theorem IsCoproductDecomposition.mapObjects_comp_objectsToInvariantSpectrum_right
    (h : IsCoproductDecomposition F₁ F₂) :
    F₂.mapObjects.left ≫ objectsToInvariantSpectrum G =
      objectsToInvariantSpectrum G₂ ≫ coprod.inr ≫ h.invariantSpectrumCoprodIso.hom := by
  rw [h.inr_invariantSpectrumCoprodIso_hom, mapObjects_comp_objectsToInvariantSpectrum]

end GroupoidScheme

end AlgebraicGeometry

end

end
