module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingDataIso
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.BeauvilleLaszlo
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaDiagonalToProducts

/-!
# Full faithfulness of the Beauville--Laszlo glueing functor (Stacks 0F9T)

Let `(g : R → R', f)` be a Beauville--Laszlo glueing pair, and write `X = Spec R`,
`U = Spec R_f`, `X' = Spec R'` and `U' = Spec R'_f`. The glueing functor of Stacks 0F9N sends
an algebraic space `Y/X` to the cartesian triple `(U ×_X Y, U' ×_X Y, X' ×_X Y)`. This module
proves that it is *full* on the full subcategory of algebraic spaces over `X` which are glueable
for `(g, f)` and have affine diagonal `Y → Y ×_X Y`, granted Stacks 0F9Q and 0F9R as described
below. The full faithfulness of Stacks 0F9T is
`beauvilleLaszloGlueingSpaces_map_bijective_of_isGlueable_of_isAffineHom_diag` (in the namespace
`BeauvilleLaszlo.Space`) in
`StacksFrontier/AlgebraicGeometry/Spaces/BeauvilleLaszloGlueingFullyFaithfulComplete.lean`.

## Main definitions

* `BeauvilleLaszlo.Space.affineGlueableSpaces`: the full subcategory of affine algebraic spaces
  over `X` which are glueable for `(g, f)`.
* `BeauvilleLaszlo.Space.AffineGlueingEquivalenceSpec`: the statement of Stacks 0F9Q as data —
  an equivalence between affine glueable spaces over `X` and cartesian triples with three
  affine components, together with the identification of its forward functor with the glueing
  functor.

## Main results

* `beauvilleLaszloGlueingSpaces_map_surjective_of_isGlueable_of_affineDiagonal`:
  **Stacks 0F9T**, fullness: compatible morphisms over `U` and `X'` descend to a morphism over
  `X` when the source and target are glueable and the target has affine diagonal.

## Implementation notes

Full faithfulness on a full subcategory is bijectivity of the map on each hom-set between its
objects. Injectivity is Stacks 0F9S,
`BeauvilleLaszlo.Space.beauvilleLaszloGlueingSpaces_map_injective_of_isGlueable`, which needs
glueability only. Surjectivity is the content proved here, and it needs affineness of the
diagonal of the target only.

The proof follows the source. Glueability of `Y` provides an étale covering of `Y` by affine
schemes, and Stacks 0F9S makes a morphism out of `Y` determined by its restrictions to such a
covering, so it suffices to construct the morphism on each member; descent of the resulting
family is Stacks 04P2 together with the fact that the glueing functor is conservative enough to
compare the two descended morphisms on an fpqc covering. When the target is itself affine the
morphism is produced directly by the affine equivalence. Otherwise, fix an affine chart `V` of
`Y` and an étale covering of the target by affine schemes `W j`; the fibre product of the triple
of `V` with the triple of `W j` over the triple of `Z` is a cartesian triple with affine
components — this is where affineness of the diagonal of `Z` enters, through
`AlgebraicGeometry.Space.IsAffineHom B X hX (diag Z.1)`. The affine equivalence turns that
triple into an affine glueable space `L j` over `X` with morphisms `L j → W j` and `L j → V`,
Stacks 0F9R makes `L j → V` étale, and the family `{L j → V}` is surjective on points: a point
of `V` is defined over a field, the glueing pair makes the corresponding map `R → K` factor
through `R_f` or through `R'`, and in either case the point lifts to the corresponding component
of the triple by Stacks 03H4.

Two results the source cites are not available in this library and are carried as explicit
hypotheses of the fullness theorem: Stacks 0F9Q, the equivalence in the affine case, as
`BeauvilleLaszlo.Space.AffineGlueingEquivalenceSpec`; and Stacks 0F9R for the property "étale",
as the hypothesis `hEtale`. Both are theorems of the source, and neither follows from the
conclusion proved here: the equivalence of 0F9Q asserts essential surjectivity, which full
faithfulness does not give, and 0F9R is a statement about étaleness of morphisms rather than
about the glueing functor being fully faithful.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9P](https://stacks.math.columbia.edu/tag/0F9P)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9R](https://stacks.math.columbia.edu/tag/0F9R)
* [Stacks Project, Tag 0F9S](https://stacks.math.columbia.edu/tag/0F9S)
* [Stacks Project, Tag 0F9T](https://stacks.math.columbia.edu/tag/0F9T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace BeauvilleLaszlo.Space

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf_beauvilleLaszloGlueingFullyFaithful
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The affine subcategory and the statement of Stacks 0F9Q -/

/-- Affine algebraic spaces over `Spec R` which are glueable for the pair `(g, f)`. -/
abbrev affineGlueableSpaces {R : Type u} {R' : Type u} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R) (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R))) :
    ObjectProperty (AlgebraicSpaces B (Spec (.of R)) hX) :=
  fun Y => AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX Y.1 ∧
    AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Y

/-- **The statement of Stacks 0F9Q, as data.** An equivalence between the affine glueable
algebraic spaces over `Spec R` and the cartesian glueing triples with three affine components,
whose forward functor is naturally identified with the restriction of a given functor `F` on
algebraic spaces — in the application, the glueing functor of Stacks 0F9N.

The natural isomorphism is part of the data: the bare existence of an equivalence between the
two subcategories says nothing about the glueing functor. -/
structure AffineGlueingEquivalenceSpec {R R' : Type u} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R) (B : BigFppfSite.{u})
    (U' U X' : Scheme.{u}) (hU' : B.Contains U') (hU : B.Contains U) (hX' : B.Contains X')
    (hX : B.Contains (Spec (.of R)))
    (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (F : AlgebraicSpaces B (Spec (.of R)) hX ⥤ GlueingData B U' U X' hU' hU hX' gU gX') where
  /-- The equivalence between the two full subcategories. -/
  equivalence : (affineGlueableSpaces g f B hX).FullSubcategory ≌
    (affineComponents B U' U X' hU' hU hX' gU gX').FullSubcategory
  /-- Its forward functor is the restriction of the given functor on algebraic spaces. -/
  functorIso : equivalence.functor ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙ F

/-! ### Fibre products of algebraic spaces and their base changes -/

/-- The inclusion of algebraic spaces into presheaves preserves fibre products: the fibre
product of algebraic spaces is the presheaf fibre product. -/
private theorem spaces_inclusion_preservesPullback (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Y Z T : AlgebraicSpaces B S hS} (f : Y ⟶ T) (g : Z ⟶ T) :
    PreservesLimit (cospan f g) (ObjectProperty.ι (IsAlgebraicSpace B S hS)) := by
  apply preservesLimit_of_preserves_limit_cone
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).isLimit
  exact (isLimitMapConePullbackConeEquiv _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).w).symm
      (IsPullback.of_hasPullback f.hom g.hom).isLimit

attribute [local instance] spaces_inclusion_preservesPullback

/-- Base change of algebraic spaces carries a cartesian square to a cartesian square: on
presheaves it is restriction along a functor, which is computed pointwise. -/
private theorem baseChange_isPullback (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    {V W Y Z : AlgebraicSpaces B T hT}
    {p : V ⟶ W} {q : V ⟶ Y} {a : W ⟶ Z} {b : Y ⟶ Z} (sq : IsPullback p q a b) :
    let F := baseChange B S T hS hT g
    IsPullback (F.map p) (F.map q) (F.map a) (F.map b) := by
  let F := baseChange B S T hS hT g
  show IsPullback (F.map p) (F.map q) (F.map a) (F.map b)
  apply IsPullback.of_map (ObjectProperty.ι (IsAlgebraicSpace B S hS))
    (by simpa only [F.map_comp] using F.congr_map sq.w)
  exact (sq.map (ObjectProperty.ι (IsAlgebraicSpace B T hT))).map
    (OverShriek.relocalizeRestrict g)

/-- Base change of algebraic spaces preserves fibre products. -/
private theorem baseChange_preservesPullback (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    {V W Z : AlgebraicSpaces B T hT} (a : V ⟶ Z) (b : W ⟶ Z) :
    PreservesLimit (cospan a b) (baseChange B S T hS hT g) := by
  apply preservesLimit_of_preserves_limit_cone (IsPullback.of_hasPullback a b).isLimit
  exact (isLimitMapConePullbackConeEquiv _ (pullback.condition (f := a) (g := b))).symm
    (baseChange_isPullback B S T hS hT g (IsPullback.of_hasPullback a b)).isLimit

attribute [local instance] baseChange_preservesPullback

/-! ### Representability of base changes along the restriction functor -/

/-- Restriction along a morphism `g : S ⟶ T` of a base takes a representable base change of a
morphism of presheaves over `T`, with representing object satisfying a property `Q` of its
structure morphism, to a representable base change of the restricted morphism with the same
property. The representing object over `S` is the one over `T` read as an object over `S`
through the chosen factorization. -/
private theorem exists_restrict_representable_pullback {C : Type*} [Category.{u} C] {S T : C}
    (g : S ⟶ T) {F G : (Over T)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (A : Over S)
    (a : yoneda.obj A ⟶ (OverShriek.relocalizeRestrict g).obj G) (Q : MorphismProperty C)
    (h : ∃ (W : Over T) (p : yoneda.obj W ⟶ F) (q : W ⟶ (Over.map g).obj A),
      IsPullback p (yoneda.map q) f
        (yonedaEquiv.symm
          (yonedaEquiv (F := (OverShriek.relocalizeRestrict g).obj G) a)) ∧ Q q.left) :
    ∃ (W : Over S) (p : yoneda.obj W ⟶ (OverShriek.relocalizeRestrict g).obj F) (q : W ⟶ A),
      IsPullback p (yoneda.map q) ((OverShriek.relocalizeRestrict g).map f) a ∧ Q q.left := by
  let H := Over.map g
  let L := OverShriek.relocalizeRestrict g
  obtain ⟨W, p, q, sq, hq⟩ := h
  let W' : Over S := Over.mk (q.left ≫ A.hom)
  let e : H.obj W' ≅ W := Over.isoMk (Iso.refl _) (by
    simpa only [H, W', Over.map_obj_hom, Over.mk_hom,
      Iso.refl_hom, Category.id_comp, Category.assoc] using q.w.symm)
  let q' : W' ⟶ A := Over.homMk q.left rfl
  let p' : yoneda.obj W' ⟶ L.obj F := yonedaEquiv.symm (F.map e.hom.op (yonedaEquiv p))
  have he : e.hom ≫ q = H.map q' := by
    apply Over.OverMorphism.ext
    simp [e, q', H]
  have hp' (V : Over S) (k : V ⟶ W') :
      p'.app (op V) k = p.app (op (H.obj V)) (H.map k ≫ e.hom) := by
    show F.map (H.map k).op (F.map e.hom.op (p.app (op W) (𝟙 W))) = _
    simpa using (p.naturality_apply (H.map k ≫ e.hom).op (𝟙 W)).symm
  have ha (V : Over S) (k : V ⟶ A) :
      (yonedaEquiv.symm (yonedaEquiv (F := L.obj G) a) :
          yoneda.obj (H.obj A) ⟶ G).app (op (H.obj V)) (H.map k) = a.app (op V) k := by
    show G.map (H.map k).op (a.app (op A) (𝟙 A)) = _
    simpa using (a.naturality_apply k.op (𝟙 A)).symm
  refine ⟨W', p', q', IsPullback.of_forall_isPullback_app ?_, hq⟩
  intro V
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext k
    show f.app (op (H.obj V.unop)) (p'.app V k) = a.app V (k ≫ q')
    rw [hp']
    have hw := congrArg (fun n : yoneda.obj W ⟶ G ↦
      n.app (op (H.obj V.unop)) (H.map k ≫ e.hom)) sq.w
    change f.app _ (p.app _ (H.map k ≫ e.hom)) =
      (yonedaEquiv.symm (yonedaEquiv (F := L.obj G) a) :
        yoneda.obj (H.obj A) ⟶ G).app _ ((H.map k ≫ e.hom) ≫ q) at hw
    rw [Category.assoc, he, ← H.map_comp, ha] at hw
    exact hw
  · intro k l hkl
    have hk := hkl.1
    rw [hp', hp'] at hk
    have h' : H.map k ≫ e.hom = H.map l ≫ e.hom := by
      apply Types.ext_of_isPullback (sq.app (op (H.obj V.unop))) hk
      show (H.map k ≫ e.hom) ≫ q = (H.map l ≫ e.hom) ≫ q
      rw [Category.assoc, Category.assoc, he, ← H.map_comp, ← H.map_comp]
      exact H.congr_map hkl.2
    apply Over.OverMorphism.ext
    exact congrArg (fun t ↦ t.left) ((cancel_mono e.hom).mp h')
  · intro x k hx
    have hx' : f.app (op (H.obj V.unop)) x =
        (yonedaEquiv.symm (yonedaEquiv (F := L.obj G) a) :
          yoneda.obj (H.obj A) ⟶ G).app _ (H.map k) := by rw [ha]; exact hx
    obtain ⟨l, hl, hlq⟩ := Types.exists_of_isPullback
      (sq.app (op (H.obj V.unop))) x (H.map k) hx'
    change l ≫ q = H.map k at hlq
    let l' : V.unop ⟶ W' := Over.homMk l.left (by
      show l.left ≫ q.left ≫ A.hom = V.unop.hom
      have hleft : l.left ≫ q.left = k.left := congrArg (fun t ↦ t.left) hlq
      rw [← Category.assoc, hleft]
      exact k.w)
    have hl' : H.map l' ≫ e.hom = l := by
      apply Over.OverMorphism.ext
      simp [H, l', e]
    refine ⟨l', ?_, ?_⟩
    · rw [hp', hl']
      exact hl
    · apply Over.OverMorphism.ext
      exact (congrArg (fun t ↦ t.left) hlq)

/-! ### Affine morphisms -/

/-- Affineness of a morphism of algebraic spaces is relative representability for the inclusion
of the big affine fppf site. -/
private theorem isAffineHom_iff_relativelyRepresentable (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    AlgebraicGeometry.Space.IsAffineHom B S hS f ↔
      (BigAffineFppf.inclusion B S hS ⋙ yoneda).relativelyRepresentable f := by
  constructor
  · intro h A a
    obtain ⟨W, p, q, sq⟩ := h A a
    exact ⟨W, ObjectProperty.homMk q, p, sq⟩
  · intro h A a
    obtain ⟨W, q, p, sq⟩ := h a
    exact ⟨W, p, q.hom, sq⟩

/-- Base change along a morphism of bases takes an affine morphism of algebraic spaces to an
affine morphism. -/
private theorem isAffineHom_restrict (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    {F G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : AlgebraicGeometry.Space.IsAffineHom B T hT f) :
    AlgebraicGeometry.Space.IsAffineHom B S hS ((OverShriek.relocalizeRestrict g).map f) := by
  intro A a
  let Q : MorphismProperty B.Schemes := fun W _ _ ↦ IsAffine W.obj
  obtain ⟨W, p, q, sq, hW⟩ := exists_restrict_representable_pullback g f A.obj a Q (by
    obtain ⟨W, p, q, sq⟩ := hf ⟨(Over.map g).obj A.obj, A.property⟩
      (yonedaEquiv.symm (yonedaEquiv (F := (OverShriek.relocalizeRestrict g).obj G) a))
    exact ⟨W.obj, p, q, sq, W.property⟩)
  exact ⟨⟨W, hW⟩, p, q, sq⟩

/-- The big fppf category over `S` has binary products: they are the fibre products over
`S`. -/
private alias site_hasBinaryProducts := AlgebraicGeometry.Stack.hasBinaryProducts_bigFppfOver

attribute [local instance] site_hasBinaryProducts

/-- Over an affine base, affineness of an object of the big fppf site is stable under binary
products, because a fibre product of affine schemes over an affine scheme is affine. -/
private theorem affineOver_closed_binaryProducts (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [IsAffine S] :
    (IsAffineOver B S hS).IsClosedUnderLimitsOfShape (Discrete WalkingPair) := by
  constructor
  rintro V ⟨h⟩
  let c := (Cone.postcompose (diagramIsoPair h.diag).hom).obj h.toLimitPresentation.cone
  have hc : IsLimit c := (IsLimit.postcomposeHomEquiv (diagramIsoPair h.diag) _).2 h.isLimit
  have sq := (Over.isPullback_of_binaryFan_isLimit c hc).map B.inclusion
  have : IsAffine (B.inclusion.obj (h.diag.obj ⟨.left⟩).left) := h.prop_diag_obj ⟨.left⟩
  have : IsAffine (B.inclusion.obj (h.diag.obj ⟨.right⟩).left) := h.prop_diag_obj ⟨.right⟩
  have : IsAffine (B.inclusion.obj (B.obj hS)) := ‹IsAffine S›
  have hpb := @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
    (B.inclusion.obj (h.diag.obj ⟨.left⟩).left)
    (B.inclusion.obj (h.diag.obj ⟨.right⟩).left) S
    (B.inclusion.map (h.diag.obj ⟨.left⟩).hom)
    (B.inclusion.map (h.diag.obj ⟨.right⟩).hom)
    (h.prop_diag_obj ⟨.left⟩) (h.prop_diag_obj ⟨.right⟩) ‹IsAffine S›
  exact IsAffine.of_isIso sq.isoPullback.hom

attribute [local instance] affineOver_closed_binaryProducts

/-- A morphism from an affine scheme of the site to an algebraic space with affine diagonal is
affine: it is a base change of the diagonal along the product of itself with the identity. -/
private theorem isAffineHom_of_affineSource_of_affineDiagonal (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) [IsAffine S] (A : BigAffineFppf B S hS)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : yoneda.obj A.obj ⟶ G)
    (hG : AlgebraicGeometry.Space.IsAffineHom B S hS (diag G)) :
    AlgebraicGeometry.Space.IsAffineHom B S hS f := by
  rw [isAffineHom_iff_relativelyRepresentable] at hG ⊢
  exact hG.of_diag f

/-! ### Étale morphisms -/

/-- A morphism of presheaves all of whose represented base changes are étale is étale in the
sense of Stacks 03FR. -/
private theorem isEtale_of_etalePresheaf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    AlgebraicGeometry.Space.IsEtale B S hS f := by
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  intro W p hp
  exact MorphismProperty.comp_mem P.presheaf p f hp hf

/-- An étale morphism out of a representable presheaf has all its represented base changes
étale. -/
private theorem etalePresheaf_of_isEtale_yoneda (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (W : BigFppfOver B S hS)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : yoneda.obj W ⟶ G)
    (hf : AlgebraicGeometry.Space.IsEtale B S hS f) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  let : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  apply (by simpa using hf W (𝟙 _))
  apply MorphismProperty.relative.of_exists
  intro A a
  refine ⟨A, a, 𝟙 _, ?_, ?_⟩
  · simpa using (IsPullback.of_id_snd (f := a))
  · show Etale ((BigFppfOver.toScheme B S hS).map (𝟙 A))
    rw [CategoryTheory.Functor.map_id]
    infer_instance

/-- Base change along a morphism of bases preserves the property that every represented base
change of a morphism of presheaves is étale. -/
private theorem etalePresheaf_restrict (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    {F G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B T hT)).presheaf f) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      ((OverShriek.relocalizeRestrict g).map f) := by
  let : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative.of_exists
  intro A a
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) B.inclusion
  obtain ⟨W, p, q, sq, hq⟩ := exists_restrict_representable_pullback g f A a Q (by
    let a₀ : yoneda.obj ((Over.map g).obj A) ⟶ G :=
      yonedaEquiv.symm (yonedaEquiv (F := (OverShriek.relocalizeRestrict g).obj G) a)
    exact ⟨hf.rep.pullback a₀, hf.rep.fst a₀, hf.rep.snd a₀,
      hf.rep.isPullback a₀, hf.property_snd a₀⟩)
  exact ⟨W, p, q, sq, hq⟩

/-- Étaleness of a morphism of algebraic spaces is invariant under isomorphism of arrows. -/
private theorem isEtale_of_arrowIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} {f' : F' ⟶ G'}
    (e : Arrow.mk f ≅ Arrow.mk f') (hf : AlgebraicGeometry.Space.IsEtale B S hS f) :
    AlgebraicGeometry.Space.IsEtale B S hS f' := by
  let P := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf
  intro W a ha
  have h₁ : P (a ≫ e.inv.left) := MorphismProperty.RespectsIso.postcomp P e.inv.left a ha
  have h₂ : P (a ≫ e.inv.left ≫ f) := hf W _ h₁
  have h₃ : P ((a ≫ e.inv.left ≫ f) ≫ e.hom.right) :=
    MorphismProperty.RespectsIso.postcomp P e.hom.right _ h₂
  have he : e.inv.left ≫ f ≫ e.hom.right = f' := by
    rw [show f ≫ e.hom.right = e.hom.left ≫ f' from e.hom.w.symm, ← Category.assoc]
    have h := congrArg (fun t ↦ t.left) e.inv_hom_id
    change e.inv.left ≫ e.hom.left = 𝟙 _ at h
    rw [h, Category.id_comp]
  simpa only [Category.assoc, he] using h₃

/-- Étaleness of a morphism of algebraic spaces respects isomorphisms. -/
private theorem isEtale_respectsIso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    MorphismProperty.RespectsIso
      (fun {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) ↦
        AlgebraicGeometry.Space.IsEtale B S hS f) := by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf
  exact isEtale_of_arrowIso B S hS e hf

attribute [local instance] isEtale_respectsIso

/-- A property of morphisms invariant under isomorphism is transported along a natural
isomorphism of functors. -/
private theorem map_property_of_natIso {C : Type*} [Category C] {D : Type*} [Category D]
    (P : MorphismProperty D) [P.RespectsIso] {F G : C ⥤ D} (e : F ≅ G) {X Y : C} (f : X ⟶ Y)
    (h : P (G.map f)) : P (F.map f) :=
  (P.arrow_mk_iso_iff (Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm)).mpr h

/-- A component of the glueing triple of an affine morphism is affine. -/
private theorem component_isAffineHom (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    (K : AlgebraicSpaces B T hT ⥤ AlgebraicSpaces B S hS) (e : K ≅ baseChange B S T hS hT g)
    {Y Z : AlgebraicSpaces B T hT} (f : Y ⟶ Z)
    (hf : AlgebraicGeometry.Space.IsAffineHom B T hT f.hom) :
    AlgebraicGeometry.Space.IsAffineHom B S hS (K.map f).hom := by
  rw [isAffineHom_iff_relativelyRepresentable]
  apply map_property_of_natIso _ (CategoryTheory.Functor.isoWhiskerRight e (ObjectProperty.ι _)) f
  exact (isAffineHom_iff_relativelyRepresentable B S hS _).mp
    (isAffineHom_restrict B S T hS hT g f.hom hf)

/-- A component of the glueing triple of an étale morphism is étale. -/
private theorem component_isEtale (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    (K : AlgebraicSpaces B T hT ⥤ AlgebraicSpaces B S hS) (e : K ≅ baseChange B S T hS hT g)
    {Y Z : AlgebraicSpaces B T hT} (f : Y ⟶ Z)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B T hT)).presheaf f.hom) :
    AlgebraicGeometry.Space.IsEtale B S hS (K.map f).hom := by
  apply isEtale_of_etalePresheaf
  apply map_property_of_natIso _ (CategoryTheory.Functor.isoWhiskerRight e (ObjectProperty.ι _)) f
  exact etalePresheaf_restrict B S T hS hT g f.hom hf

/-! ### Points and base change -/

/-- A field-valued point of a base change is a field-valued point of the original space, read
over the larger base. -/
private noncomputable def fieldPointToBase (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS
      ((OverShriek.relocalizeRestrict g).obj F)) :
    AlgebraicGeometry.Space.FieldValuedPoint B T hT F where
  carrier := p.carrier
  contained := p.contained
  toBase := p.toBase ≫ g.hom
  value := p.value

/-- Reading a field-valued point of a base change over the larger base preserves domination. -/
private theorem dominates_fieldPointToBase (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
    {p q : AlgebraicGeometry.Space.FieldValuedPoint B S hS
      ((OverShriek.relocalizeRestrict g).obj F)}
    (h : AlgebraicGeometry.Space.FieldValuedPoint.Dominates B S hS _ p q) :
    AlgebraicGeometry.Space.FieldValuedPoint.Dominates B T hT F
      (fieldPointToBase B S T hS hT g F p) (fieldPointToBase B S T hS hT g F q) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨(Over.map g).map a, ha⟩

/-- The map on points induced by reading a base change over the larger base. -/
private noncomputable def pointsToBase (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) :
    AlgebraicGeometry.Space.points B S hS ((OverShriek.relocalizeRestrict g).obj F) →
      AlgebraicGeometry.Space.points B T hT F :=
  Quot.map (fieldPointToBase B S T hS hT g F) (by
    intro p q h
    obtain ⟨r, hp, hq⟩ := h
    exact ⟨fieldPointToBase B S T hS hT g F r,
      dominates_fieldPointToBase B S T hS hT g F hp,
      dominates_fieldPointToBase B S T hS hT g F hq⟩)

/-- Reading points of a base change over the larger base is natural in the space. -/
private theorem pointsToBase_naturality (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    {F G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (p : AlgebraicGeometry.Space.points B S hS
      ((OverShriek.relocalizeRestrict g).obj F)) :
    pointsToBase B S T hS hT g G
        (AlgebraicGeometry.Space.pointsMap B S hS _
          ((OverShriek.relocalizeRestrict g).map f) p) =
      AlgebraicGeometry.Space.pointsMap B T hT F f (pointsToBase B S T hS hT g F p) := by
  induction p using Quot.inductionOn
  rfl

/-- The map on points of a composite of morphisms of presheaves, applied to a point. -/
private theorem pointsMap_apply_comp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : G ⟶ H)
    (p : AlgebraicGeometry.Space.points B S hS F) :
    AlgebraicGeometry.Space.pointsMap B S hS F (f ≫ g) p =
      AlgebraicGeometry.Space.pointsMap B S hS G g
        (AlgebraicGeometry.Space.pointsMap B S hS F f p) := by
  induction p using Quot.inductionOn
  rfl

/-- The map on points of the identity is the identity, applied to a point. -/
private theorem pointsMap_apply_id (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (p : AlgebraicGeometry.Space.points B S hS F) :
    AlgebraicGeometry.Space.pointsMap B S hS F (𝟙 F) p = p := by
  induction p using Quot.inductionOn
  rfl

/-- The map on points of a composite of morphisms of algebraic spaces, applied to a point. -/
private theorem pointsMap_apply_comp_space (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : AlgebraicGeometry.Space.points B S hS X.obj) :
    AlgebraicGeometry.Space.pointsMap B S hS _ (f ≫ g).hom p =
      AlgebraicGeometry.Space.pointsMap B S hS _ g.hom
        (AlgebraicGeometry.Space.pointsMap B S hS _ f.hom p) :=
  pointsMap_apply_comp B S hS f.hom g.hom p

/-- A point of the base change of a space covered by a family lifts to the base change of a
member of that family. -/
private theorem exists_restricted_cover_point (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT) {I : Type (u + 1)}
    {F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (X : I → (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
    (f : ∀ i, X i ⟶ F)
    (hc : (⋃ i, Set.range (AlgebraicGeometry.Space.pointsMap B T hT (X i) (f i))) = Set.univ)
    (p : AlgebraicGeometry.Space.points B S hS
      ((OverShriek.relocalizeRestrict g).obj F)) :
    ∃ i, ∃ q : AlgebraicGeometry.Space.points B S hS
      ((OverShriek.relocalizeRestrict g).obj (X i)),
      AlgebraicGeometry.Space.pointsMap B S hS _
        ((OverShriek.relocalizeRestrict g).map (f i)) q = p := by
  induction p using Quot.inductionOn with
  | _ p =>
    let px := fieldPointToBase B S T hS hT g F p
    have hmem : px.class B T hT F ∈
        ⋃ i, Set.range (AlgebraicGeometry.Space.pointsMap B T hT (X i) (f i)) := by
      rw [hc]
      exact Set.mem_univ _
    obtain ⟨i, q, hq⟩ := Set.mem_iUnion.mp hmem
    induction q using Quot.inductionOn with
    | _ q =>
      have heq : px.class B T hT F =
          (AlgebraicGeometry.Space.FieldValuedPoint.map B T hT (X i) (f i) q).class B T hT F := by
        simpa only [AlgebraicGeometry.Space.pointsMap_class] using hq.symm
      obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
        (AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff B T hT F _ _).mp heq
      dsimp [px, fieldPointToBase] at a ha
      let s : Spec (.of r.carrier) ⟶ S := a.left.hom ≫ p.toBase
      have hs : s ≫ g.hom = r.toBase := by
        show (a.left.hom ≫ p.toBase) ≫ g.hom = r.toBase
        rw [Category.assoc]
        exact congrArg (fun x ↦ x.hom) a.w
      let e : (Over.map g).obj (Over.mk (⟨s⟩ : B.obj r.contained ⟶ B.obj hS)) ≅
          r.siteObject := Over.isoMk (Iso.refl _) (by
            apply ObjectProperty.hom_ext
            exact hs.symm)
      let rs : AlgebraicGeometry.Space.FieldValuedPoint B S hS
          ((OverShriek.relocalizeRestrict g).obj F) :=
        { carrier := r.carrier
          contained := r.contained
          toBase := s
          value := F.map e.hom.op r.value }
      let qs : AlgebraicGeometry.Space.FieldValuedPoint B S hS
          ((OverShriek.relocalizeRestrict g).obj (X i)) :=
        { carrier := r.carrier
          contained := r.contained
          toBase := s
          value := (X i).map e.hom.op ((X i).map b.op q.value) }
      refine ⟨i, qs.class B S hS _, ?_⟩
      have hval :
          (AlgebraicGeometry.Space.FieldValuedPoint.map B S hS _
            ((OverShriek.relocalizeRestrict g).map (f i)) qs).value = rs.value := by
        change F.map b.op ((f i).app (op q.siteObject) q.value) = r.value at hb
        show (f i).app _ ((X i).map e.hom.op ((X i).map b.op q.value)) =
          F.map e.hom.op r.value
        calc
          (f i).app _ ((X i).map e.hom.op ((X i).map b.op q.value)) =
              F.map e.hom.op ((f i).app (op r.siteObject) ((X i).map b.op q.value)) :=
            (f i).naturality_apply e.hom.op ((X i).map b.op q.value)
          _ = F.map e.hom.op (F.map b.op ((f i).app (op q.siteObject) q.value)) :=
            congrArg (F.map e.hom.op) ((f i).naturality_apply b.op q.value)
          _ = F.map e.hom.op r.value := congrArg (F.map e.hom.op) hb
      have hclass :
          (AlgebraicGeometry.Space.FieldValuedPoint.map B S hS _
            ((OverShriek.relocalizeRestrict g).map (f i)) qs).class B S hS _ =
            rs.class B S hS _ := by
        apply (AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff B S hS _ _ _).mpr
        refine ⟨rs, ?_, AlgebraicGeometry.Space.FieldValuedPoint.dominates_refl B S hS _ rs⟩
        refine ⟨𝟙 rs.siteObject, ?_⟩
        show ((OverShriek.relocalizeRestrict g).obj F).map (𝟙 _)
          (AlgebraicGeometry.Space.FieldValuedPoint.map B S hS _
            ((OverShriek.relocalizeRestrict g).map (f i)) qs).value = rs.value
        rw [((OverShriek.relocalizeRestrict g).obj F).map_id]
        exact hval
      have hdom : AlgebraicGeometry.Space.FieldValuedPoint.Dominates B S hS _ rs p := by
        let m : rs.siteObject ⟶ p.siteObject := Over.homMk a.left rfl
        refine ⟨m, ?_⟩
        show F.map ((Over.map g).map m).op p.value = rs.value
        have hem : e.hom ≫ a = (Over.map g).map m := by
          apply Over.OverMorphism.ext
          rfl
        show F.map ((Over.map g).map m).op p.value = F.map e.hom.op r.value
        calc
          F.map ((Over.map g).map m).op p.value = F.map (e.hom ≫ a).op p.value :=
            congrArg (fun k ↦ F.map k.op p.value) hem.symm
          _ = F.map e.hom.op (F.map a.op p.value) := by simp
          _ = F.map e.hom.op r.value := congrArg (F.map e.hom.op) ha
      exact (AlgebraicGeometry.Space.pointsMap_class B S hS _ _ qs).trans
        (hclass.trans (Quot.sound ⟨rs,
          AlgebraicGeometry.Space.FieldValuedPoint.dominates_refl B S hS _ rs, hdom⟩))

/-- A field-valued point of a space over `T` whose structure map factors through `S` comes from
a point of the base change to `S`. -/
private theorem exists_restricted_point_of_base_factorization (B : BigFppfSite.{u})
    (S T : Scheme.{u}) (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B T hT F)
    (s : Spec (.of p.carrier) ⟶ S) (hs : s ≫ g.hom = p.toBase) :
    ∃ q : AlgebraicGeometry.Space.points B S hS
      ((OverShriek.relocalizeRestrict g).obj F),
      pointsToBase B S T hS hT g F q = p.class B T hT F := by
  let e : (Over.map g).obj (Over.mk (⟨s⟩ : B.obj p.contained ⟶ B.obj hS)) ≅
      p.siteObject := Over.isoMk (Iso.refl _) (by
        apply ObjectProperty.hom_ext
        exact hs.symm)
  let q : AlgebraicGeometry.Space.FieldValuedPoint B S hS
      ((OverShriek.relocalizeRestrict g).obj F) :=
    { carrier := p.carrier
      contained := p.contained
      toBase := s
      value := F.map e.hom.op p.value }
  refine ⟨q.class B S hS _, ?_⟩
  have hdom : AlgebraicGeometry.Space.FieldValuedPoint.Dominates B T hT F
      (fieldPointToBase B S T hS hT g F q) p := by
    refine ⟨e.hom, ?_⟩
    rfl
  exact Quot.sound ⟨fieldPointToBase B S T hS hT g F q,
    AlgebraicGeometry.Space.FieldValuedPoint.dominates_refl B T hT F _, hdom⟩

/-- A point of a component of the glueing triple of `V` lifts to a component of the triple of
one of the fibre products with a member of a covering of the target. -/
private theorem exists_component_cover_point (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT) {J : Type (u + 1)}
    {V Z : AlgebraicSpaces B T hT} (A : J → AlgebraicSpaces B T hT) (b : ∀ j, A j ⟶ Z)
    (hc : (⋃ j, Set.range (AlgebraicGeometry.Space.pointsMap B T hT (A j).obj (b j).hom)) =
      Set.univ)
    {D : Type*} [Category D] (F : AlgebraicSpaces B T hT ⥤ D)
    (O : D ⥤ AlgebraicSpaces B S hS) (e : F ⋙ O ≅ baseChange B S T hS hT g)
    (m : F.obj V ⟶ F.obj Z) (P : J → D) (p : ∀ j, P j ⟶ F.obj (A j)) (q : ∀ j, P j ⟶ F.obj V)
    (sq : ∀ j, IsPullback (O.map (p j)) (O.map (q j)) (O.map (F.map (b j))) (O.map m))
    (L : J → AlgebraicSpaces B T hT) (el : ∀ j, F.obj (L j) ≅ P j) (l : ∀ j, L j ⟶ V)
    (hl : ∀ j, F.map (l j) = (el j).hom ≫ q j)
    (v : AlgebraicGeometry.Space.points B S hS (O.obj (F.obj V)).obj) :
    ∃ j, ∃ w : AlgebraicGeometry.Space.points B S hS (O.obj (F.obj (L j))).obj,
      AlgebraicGeometry.Space.pointsMap B S hS _ (O.map (F.map (l j))).hom w = v := by
  let H := baseChange B S T hS hT g
  let z := AlgebraicGeometry.Space.pointsMap B S hS _ (O.map m).hom v
  let z' := AlgebraicGeometry.Space.pointsMap B S hS _ (e.hom.app Z).hom z
  obtain ⟨j, a', ha'⟩ := exists_restricted_cover_point B S T hS hT g
    (fun j ↦ (A j).obj) (fun j ↦ (b j).hom) hc z'
  let a := AlgebraicGeometry.Space.pointsMap B S hS _ (e.inv.app (A j)).hom a'
  have hcompat : AlgebraicGeometry.Space.pointsMap B S hS _
      (O.map (F.map (b j))).hom a = z := by
    calc
      AlgebraicGeometry.Space.pointsMap B S hS _ (O.map (F.map (b j))).hom a =
          AlgebraicGeometry.Space.pointsMap B S hS _
            (e.inv.app (A j) ≫ O.map (F.map (b j))).hom a' :=
        (pointsMap_apply_comp_space B S hS (e.inv.app (A j))
          (O.map (F.map (b j))) a').symm
      _ = AlgebraicGeometry.Space.pointsMap B S hS _
          (H.map (b j) ≫ e.inv.app Z).hom a' := by
        exact congrArg (fun k ↦ AlgebraicGeometry.Space.pointsMap B S hS _ k.hom a')
          (e.inv.naturality (b j)).symm
      _ = AlgebraicGeometry.Space.pointsMap B S hS _ (e.inv.app Z).hom
          (AlgebraicGeometry.Space.pointsMap B S hS _ (H.map (b j)).hom a') :=
        pointsMap_apply_comp_space B S hS (H.map (b j)) (e.inv.app Z) a'
      _ = AlgebraicGeometry.Space.pointsMap B S hS _ (e.inv.app Z).hom z' :=
        congrArg (AlgebraicGeometry.Space.pointsMap B S hS _ (e.inv.app Z).hom) ha'
      _ = z := by
        show AlgebraicGeometry.Space.pointsMap B S hS _ (e.inv.app Z).hom
          (AlgebraicGeometry.Space.pointsMap B S hS _ (e.hom.app Z).hom z) = z
        rw [← pointsMap_apply_comp_space]
        rw [e.hom_inv_id_app Z]
        exact pointsMap_apply_id B S hS _ z
  obtain ⟨d, _, hd⟩ := AlgebraicGeometry.Space.exists_point_of_isPullback B S hS
    (sq j) a v hcompat
  let w := AlgebraicGeometry.Space.pointsMap B S hS _ (O.map (el j).inv).hom d
  refine ⟨j, w, ?_⟩
  have hmap : O.map ((el j).inv ≫ F.map (l j)) = O.map (q j) := by
    rw [hl j, ← Category.assoc, (el j).inv_hom_id]
    simp
  calc
    AlgebraicGeometry.Space.pointsMap B S hS _ (O.map (F.map (l j))).hom w =
        AlgebraicGeometry.Space.pointsMap B S hS _
          (O.map ((el j).inv ≫ F.map (l j))).hom d := by
      show AlgebraicGeometry.Space.pointsMap B S hS _ (O.map (F.map (l j))).hom
          (AlgebraicGeometry.Space.pointsMap B S hS _ (O.map (el j).inv).hom d) = _
      rw [← pointsMap_apply_comp_space, ← O.map_comp]
    _ = AlgebraicGeometry.Space.pointsMap B S hS _ (O.map (q j)).hom d := by rw [hmap]
    _ = v := hd

/-- A point of the base change of `V` lies in the image of one of the morphisms `L j ⟶ V`
produced by the affine equivalence, as a point of `V` itself. -/
private theorem exists_global_cover_point_of_component (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT) {J : Type (u + 1)}
    {V Z : AlgebraicSpaces B T hT} (A : J → AlgebraicSpaces B T hT) (b : ∀ j, A j ⟶ Z)
    (hc : (⋃ j, Set.range (AlgebraicGeometry.Space.pointsMap B T hT (A j).obj (b j).hom)) =
      Set.univ)
    {D : Type*} [Category D] (F : AlgebraicSpaces B T hT ⥤ D)
    (O : D ⥤ AlgebraicSpaces B S hS) (e : F ⋙ O ≅ baseChange B S T hS hT g)
    (m : F.obj V ⟶ F.obj Z) (P : J → D) (p : ∀ j, P j ⟶ F.obj (A j)) (q : ∀ j, P j ⟶ F.obj V)
    (sq : ∀ j, IsPullback (O.map (p j)) (O.map (q j)) (O.map (F.map (b j))) (O.map m))
    (L : J → AlgebraicSpaces B T hT) (el : ∀ j, F.obj (L j) ≅ P j) (l : ∀ j, L j ⟶ V)
    (hl : ∀ j, F.map (l j) = (el j).hom ≫ q j)
    (v : AlgebraicGeometry.Space.points B S hS
      ((baseChange B S T hS hT g).obj V).obj) :
    ∃ j, ∃ w : AlgebraicGeometry.Space.points B T hT (L j).obj,
      AlgebraicGeometry.Space.pointsMap B T hT _ (l j).hom w =
        pointsToBase B S T hS hT g V.obj v := by
  let v' := AlgebraicGeometry.Space.pointsMap B S hS _ (e.inv.app V).hom v
  obtain ⟨j, w, hw⟩ := exists_component_cover_point B S T hS hT g
    A b hc F O e m P p q sq L el l hl v'
  let w' := AlgebraicGeometry.Space.pointsMap B S hS _ (e.hom.app (L j)).hom w
  have he : AlgebraicGeometry.Space.pointsMap B S hS _
      ((baseChange B S T hS hT g).map (l j)).hom w' = v := by
    calc
      AlgebraicGeometry.Space.pointsMap B S hS _
          ((baseChange B S T hS hT g).map (l j)).hom w' =
          AlgebraicGeometry.Space.pointsMap B S hS _
            (e.hom.app (L j) ≫ (baseChange B S T hS hT g).map (l j)).hom w :=
        (pointsMap_apply_comp_space B S hS (e.hom.app (L j))
          ((baseChange B S T hS hT g).map (l j)) w).symm
      _ = AlgebraicGeometry.Space.pointsMap B S hS _
            (O.map (F.map (l j)) ≫ e.hom.app V).hom w := by
        rw [← e.hom.naturality (l j)]
        rfl
      _ = AlgebraicGeometry.Space.pointsMap B S hS _ (e.hom.app V).hom v' := by
        rw [pointsMap_apply_comp_space, hw]
        rfl
      _ = v := by
        show AlgebraicGeometry.Space.pointsMap B S hS _ (e.hom.app V).hom
          (AlgebraicGeometry.Space.pointsMap B S hS _ (e.inv.app V).hom v) = v
        rw [← pointsMap_apply_comp_space, e.inv_hom_id_app]
        exact pointsMap_apply_id B S hS _ v
  exact ⟨j, pointsToBase B S T hS hT g (L j).obj w',
    (pointsToBase_naturality B S T hS hT g (l j).hom w').symm.trans
      (congrArg (pointsToBase B S T hS hT g V.obj) he)⟩

/-! ### The glueing pair at the closed fibre -/

/-- When `R/fR ≅ R'/fR'` through `g`, a ring map out of `R` killing `f` extends uniquely to
`R'`. -/
private theorem existsUnique_lift_of_quotientEquiv {R R' A : Type*} [CommRing R] [CommRing R']
    [Semiring A] (g : R →+* R') (f : R)
    (e : (R ⧸ Ideal.span {f}) ≃+* (R' ⧸ Ideal.span {g f}))
    (he : ∀ r, e (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (g r))
    (a : R →+* A) (ha : a f = 0) : ∃! b : R' →+* A, b.comp g = a := by
  let a₀ : R ⧸ Ideal.span {f} →+* A :=
    Ideal.Quotient.lift _ a (by
      show Ideal.span {f} ≤ RingHom.ker a
      rw [Ideal.span_le]
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ha)
  let b : R' →+* A := (a₀.comp e.symm.toRingHom).comp (Ideal.Quotient.mk _)
  have hb : b.comp g = a := by
    ext r
    show a₀ (e.symm (Ideal.Quotient.mk _ (g r))) = a r
    rw [← he r, e.symm_apply_apply]
    rfl
  refine ⟨b, hb, ?_⟩
  intro c hc
  have hcf : c (g f) = 0 := by
    have h := RingHom.congr_fun hc f
    exact h.trans ha
  let c₀ : R' ⧸ Ideal.span {g f} →+* A :=
    Ideal.Quotient.lift _ c (by
      show Ideal.span {g f} ≤ RingHom.ker c
      rw [Ideal.span_le]
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact hcf)
  have hce : c₀.comp e.toRingHom = a₀ := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    show c₀ (e (Ideal.Quotient.mk _ r)) = a r
    rw [he]
    exact RingHom.congr_fun hc r
  ext r
  have h := RingHom.congr_fun hce (e.symm (Ideal.Quotient.mk _ r))
  change c₀ (e (e.symm (Ideal.Quotient.mk _ r))) = a₀ (e.symm (Ideal.Quotient.mk _ r)) at h
  rw [e.apply_symm_apply] at h
  exact h

/-! ### Morphisms and fibre products of glueing triples -/

/-- A morphism of cartesian glueing triples is determined by its components over `U` and
`X'`. -/
private alias glueingData_hom_ext := BeauvilleLaszlo.Space.hom_ext_of_overU_of_overX

/-- Two morphisms of cartesian glueing triples with a common target have a fibre product,
computed componentwise. -/
private theorem exists_glueingData_pullback (B : BigFppfSite.{u}) (U' U X' : Scheme.{u})
    (hU' : B.Contains U') (hU : B.Contains U) (hX' : B.Contains X')
    (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    {D E T : GlueingData B U' U X' hU' hU hX' gU gX'} (a : D ⟶ T) (b : E ⟶ T) :
    ∃ (P : GlueingData B U' U X' hU' hU hX' gU gX') (p : P ⟶ D) (q : P ⟶ E),
      p ≫ a = q ≫ b ∧
      IsPullback p.hom.left.right q.hom.left.right a.hom.left.right b.hom.left.right ∧
      IsPullback p.hom.left.left q.hom.left.left a.hom.left.left b.hom.left.left ∧
      IsPullback p.hom.right q.hom.right a.hom.right b.hom.right := by
  let L := baseChange B U' U hU' hU gU
  let M := baseChange B U' X' hU' hX' gX'
  let P₀ := pullback a.hom.left.left b.hom.left.left
  let PU := pullback a.hom.left.right b.hom.left.right
  let PX := pullback a.hom.right b.hom.right
  let tU : P₀ ⟶ L.obj PU :=
    pullback.map _ _ _ _ D.obj.left.hom E.obj.left.hom T.obj.left.hom
      a.hom.left.w b.hom.left.w ≫
      (PreservesPullback.iso L a.hom.left.right b.hom.left.right).inv
  let tX : P₀ ⟶ M.obj PX :=
    pullback.map _ _ _ _ D.obj.hom E.obj.hom T.obj.hom a.hom.w b.hom.w ≫
      (PreservesPullback.iso M a.hom.right b.hom.right).inv
  have : IsIso D.obj.left.hom := D.property.1
  have : IsIso E.obj.left.hom := E.property.1
  have : IsIso T.obj.left.hom := T.property.1
  have : IsIso D.obj.hom := D.property.2
  have : IsIso E.obj.hom := E.property.2
  have : IsIso T.obj.hom := T.property.2
  let P : GlueingData B U' U X' hU' hU hX' gU gX' :=
    ⟨⟨⟨P₀, PU, tU⟩, PX, tX⟩, by
      exact ⟨inferInstanceAs (IsIso tU), inferInstanceAs (IsIso tX)⟩⟩
  let p : P ⟶ D := ObjectProperty.homMk
    { left :=
        { left := pullback.fst _ _
          right := pullback.fst _ _
          w := by
            dsimp only [P, tU]
            rw [Category.assoc, PreservesPullback.iso_inv_fst L]
            simp only [L, pullback.map, pullback.lift_fst, Functor.id_map] }
      right := pullback.fst _ _
      w := by
        show pullback.fst a.hom.left.left b.hom.left.left ≫ D.obj.hom =
          tX ≫ M.map (pullback.fst a.hom.right b.hom.right)
        dsimp only [tX]
        rw [Category.assoc, PreservesPullback.iso_inv_fst M]
        simp only [M, pullback.map, pullback.lift_fst] }
  let q : P ⟶ E := ObjectProperty.homMk
    { left :=
        { left := pullback.snd _ _
          right := pullback.snd _ _
          w := by
            dsimp only [P, tU]
            rw [Category.assoc, PreservesPullback.iso_inv_snd L]
            simp only [L, pullback.map, pullback.lift_snd, Functor.id_map] }
      right := pullback.snd _ _
      w := by
        show pullback.snd a.hom.left.left b.hom.left.left ≫ E.obj.hom =
          tX ≫ M.map (pullback.snd a.hom.right b.hom.right)
        dsimp only [tX]
        rw [Category.assoc, PreservesPullback.iso_inv_snd M]
        simp only [M, pullback.map, pullback.lift_snd] }
  refine ⟨P, p, q, ?_, IsPullback.of_hasPullback _ _,
    IsPullback.of_hasPullback _ _, IsPullback.of_hasPullback _ _⟩
  apply glueingData_hom_ext B U' U X' hU' hU hX' gU gX'
  · exact pullback.condition
  · exact pullback.condition

/-! ### Comparing two descended morphisms -/

/-- An extensionality principle transported along a natural isomorphism of functors. -/
private theorem hom_ext_of_iso {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {Y Z : C} {I : Type*} {V : I → C} (p : ∀ i, V i ⟶ Y)
    (hG : ∀ a b : G.obj Y ⟶ G.obj Z, (∀ i, G.map (p i) ≫ a = G.map (p i) ≫ b) → a = b)
    {a b : F.obj Y ⟶ F.obj Z}
    (hab : ∀ i, F.map (p i) ≫ a = F.map (p i) ≫ b) : a = b := by
  apply (cancel_epi (e.inv.app Y)).mp
  apply (cancel_mono (e.hom.app Z)).mp
  apply hG
  intro i
  simp only [Category.assoc, e.inv.naturality_assoc]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ e.inv.app (V i) ≫ t ≫ e.hom.app Z) (hab i)

/-- A morphism into a sheaf on the big fppf site of `S` is determined by its values on the
affine objects of the site, which are cover dense. -/
private theorem hom_ext_of_affine (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) {a b : F ⟶ G}
    (h : ∀ A : BigAffineFppf B S hS, a.app (op A.obj) = b.app (op A.obj)) : a = b := by
  have := Functor.IsDenseSubsite.isCoverDense
    (BigAffineFppf.topology B S hS) (BigFppfOver.topology B S hS)
    (BigAffineFppf.inclusion B S hS)
  ext T x
  apply Functor.IsCoverDense.ext (BigAffineFppf.inclusion B S hS) ⟨G, hG⟩ T.unop
  intro A k
  exact (a.naturality_apply k.op x).symm.trans
    ((ConcreteCategory.congr_hom (h A) (F.map k.op x)).trans (b.naturality_apply k.op x))

/-- Two morphisms out of the base change of `Y` which agree after base changing an fpqc
covering of `Y` are equal. -/
private theorem baseChange_hom_ext_of_fpqcCovering (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    {I : Type v} {V : I → AlgebraicSpaces B T hT} {Y Z : AlgebraicSpaces B T hT}
    (p : ∀ i, V i ⟶ Y)
    (hp : AlgebraicGeometry.Space.IsFpqcCovering B T hT (fun i ↦ (p i).hom))
    {a b : (baseChange B S T hS hT g).obj Y ⟶ (baseChange B S T hS hT g).obj Z}
    (hab : ∀ i, (baseChange B S T hS hT g).map (p i) ≫ a =
      (baseChange B S T hS hT g).map (p i) ≫ b) : a = b := by
  let H := Over.map g
  let F := baseChange B S T hS hT g
  let Qₛ := BigFppfOver.toScheme B S hS
  apply ObjectProperty.hom_ext
  apply hom_ext_of_affine B S hS (F.obj Z).property.isSheaf
  intro A
  ext x
  change Y.obj.obj (op (H.obj A.obj)) at x
  let A' : BigAffineFppf B T hT := ⟨H.obj A.obj, A.property⟩
  obtain ⟨E, _, hE, hlift⟩ := hp.2 A' (yonedaEquiv.symm x)
  choose ix l hl using hlift
  let W (j : E.I₀) : BigFppfOver B S hS := Over.mk ((E.f j).hom.left ≫ A.obj.hom)
  let r (j : E.I₀) : W j ⟶ A.obj := Over.homMk (E.f j).hom.left rfl
  let e (j : E.I₀) : H.obj (W j) ≅ (E.X j).obj :=
    Over.isoMk (Iso.refl _) (by
      dsimp [H, W, A']
      simpa only [A', H, Over.map_obj_hom, Over.mk_hom, Category.id_comp, Category.assoc]
        using (E.f j).hom.w.symm)
  have he (j : E.I₀) : H.map (r j) = (e j).hom ≫ (E.f j).hom := by
    apply Over.OverMorphism.ext
    simp [H, r, e]
  let K := Scheme.fpqcPrecoverage.comap Qₛ
  have hcover : Presieve.ofArrows W r ∈ K A.obj := by
    rw [Scheme.fpqcPrecoverage.mem_comap_iff]
    simpa only [PreZeroHypercover.presieve₀, Presieve.map_ofArrows, W, r, Qₛ, A', H,
      BigAffineFppf.toScheme, BigAffineFppf.inclusion, BigFppfOver.toScheme,
      BigFppfOver.forget, Functor.comp_obj, Functor.comp_map, Over.map_obj_left, Over.mk_left,
      ObjectProperty.ι_obj, ObjectProperty.ι_map, Over.forget_obj, Over.forget_map,
      Over.homMk_left] using hE
  have hsheaf := (isSheaf_iff_isSheaf_of_type K.toGrothendieck (F.obj Z).obj).mp
    (IsAlgebraicSpace.isSheaf_fpqc (F.obj Z).property)
  have hs := (Presieve.IsSheaf.isSheafFor_of_mem_precoverage hsheaf hcover).isSeparatedFor
  have hrestr (j : E.I₀) :
      (F.obj Z).obj.map (r j).op (a.hom.app (op A.obj) x) =
      (F.obj Z).obj.map (r j).op (b.hom.app (op A.obj) x) := by
    let vj := (V (ix j)).obj.map (e j).hom.op (yonedaEquiv (l j))
    have hv : ((F.map (p (ix j))).hom.app (op (W j))) vj =
        (F.obj Y).obj.map (r j).op x := by
      show (p (ix j)).hom.app (op (H.obj (W j)))
        ((V (ix j)).obj.map (e j).hom.op (yonedaEquiv (l j))) =
        Y.obj.map (H.map (r j)).op x
      rw [NatTrans.naturality_apply, he]
      have hj : (p (ix j)).hom.app (op (E.X j).obj) (yonedaEquiv (l j)) =
          Y.obj.map (E.f j).hom.op x := by
        rw [← yonedaEquiv_comp, hl j, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
        rfl
      rw [hj]
      simp only [op_comp, Functor.map_comp_apply]
    rw [← a.hom.naturality_apply (r j).op x, ← b.hom.naturality_apply (r j).op x, ← hv]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun f ↦ f.hom) (hab (ix j))) (op (W j))) vj
  apply hs.ext
  intro R k hk
  rw [Presieve.ofArrows.eq_eqToHom_comp_hom_idx hk]
  simp only [op_comp, Functor.map_comp_apply]
  exact congrArg ((F.obj Z).obj.map (eqToHom (Presieve.ofArrows.obj_idx hk).symm).op)
    (hrestr hk.idx)

/-- Two morphisms of glueing triples which agree after restricting along an fpqc covering of
the source are equal. -/
private theorem glueingFunctor_hom_ext_of_fpqcCovering (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U') (hU : B.Contains U) (hX' : B.Contains X')
    (hX : B.Contains X) (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX')
    (F : GlueingFunctorSpec B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm)
    {I : Type*} {V : I → AlgebraicSpaces B X hX} {Y Z : AlgebraicSpaces B X hX}
    (p : ∀ i, V i ⟶ Y)
    (hp : AlgebraicGeometry.Space.IsFpqcCovering B X hX (fun i ↦ (p i).hom))
    {a b : F.functor.obj Y ⟶ F.functor.obj Z}
    (hab : ∀ i, F.functor.map (p i) ≫ a = F.functor.map (p i) ≫ b) : a = b := by
  apply glueingData_hom_ext B U' U X' hU' hU hX' gU gX'
  · apply hom_ext_of_iso F.overUIso p
      (fun a b h ↦ baseChange_hom_ext_of_fpqcCovering B U X hU hX jU p hp h)
    intro i
    exact congrArg (fun t ↦ (overU B U' U X' hU' hU hX' gU gX').map t) (hab i)
  · apply hom_ext_of_iso F.overX'Iso p
      (fun a b h ↦ baseChange_hom_ext_of_fpqcCovering B X' X hX' hX jX' p hp h)
    intro i
    exact congrArg (fun t ↦ (overX' B U' U X' hU' hU hX' gU gX').map t) (hab i)

/-! ### Consequences of the affine equivalence -/

/-- A functor whose restriction to a full subcategory is naturally an equivalence onto another
full subcategory is full on that subcategory. -/
private theorem map_surjective_of_equivalence {C : Type*} [Category C] {D : Type*} [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (e : P.FullSubcategory ≌ Q.FullSubcategory) (he : e.functor ⋙ Q.ι ≅ P.ι ⋙ F)
    {Y Z : C} (hY : P Y) (hZ : P Z) : Function.Surjective (F.map (X := Y) (Y := Z)) := by
  have : (P.ι ⋙ F).Full := Functor.Full.of_iso he
  intro a
  obtain ⟨b, hb⟩ := Functor.Full.map_surjective (F := P.ι ⋙ F)
    (X := (⟨Y, hY⟩ : P.FullSubcategory)) (Y := (⟨Z, hZ⟩ : P.FullSubcategory)) a
  exact ⟨b.hom, hb⟩

/-- Affineness of an algebraic space is invariant under isomorphism in the category of
algebraic spaces. -/
private theorem isAffineSpace_of_iso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Y Z : AlgebraicSpaces B S hS} (e : Y ≅ Z)
    (hY : AlgebraicGeometry.Space.IsAffineSpace B S hS Y.1) :
    AlgebraicGeometry.Space.IsAffineSpace B S hS Z.1 := by
  obtain ⟨W, hW, ⟨eW⟩⟩ := hY
  exact ⟨W, hW, ⟨(ObjectProperty.ι _).mapIso e.symm ≪≫ eW⟩⟩

/-- The source of a cartesian square whose right-hand leg is affine and whose lower right-hand
corner is an affine algebraic space is an affine algebraic space. -/
private theorem isAffineSpace_of_isPullback_of_isAffineHom (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {P Y Z T : AlgebraicSpaces B S hS}
    {p : P ⟶ Y} {q : P ⟶ Z} {f : Y ⟶ T} {g : Z ⟶ T} (sq : IsPullback p q f g)
    (hf : AlgebraicGeometry.Space.IsAffineHom B S hS f.hom)
    (hZ : AlgebraicGeometry.Space.IsAffineSpace B S hS Z.1) :
    AlgebraicGeometry.Space.IsAffineSpace B S hS P.1 := by
  obtain ⟨W, hW, ⟨e⟩⟩ := hZ
  obtain ⟨A, a, b, hA⟩ := hf ⟨W, hW⟩ (e.inv ≫ g.hom)
  have sq' : IsPullback p.hom (q.hom ≫ e.hom) f.hom (e.inv ≫ g.hom) :=
    (sq.map (ObjectProperty.ι _)).of_iso (Iso.refl _) (Iso.refl _)
    e (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  exact ⟨A.obj, A.property, ⟨sq'.isoPullback ≪≫ hA.isoPullback.symm⟩⟩

/-- An object of the target subcategory of the affine equivalence comes from an object of the
source subcategory, together with the two morphisms induced by a pair of morphisms out of
it. -/
private theorem exists_span_of_equivalence {C : Type*} [Category C] {D : Type*} [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (E : P.FullSubcategory ≌ Q.FullSubcategory) (eF : E.functor ⋙ Q.ι ≅ P.ι ⋙ F)
    {A V : C} (hA : P A) (hV : P V) {T : D} (hT : Q T) (a : T ⟶ F.obj A) (v : T ⟶ F.obj V) :
    ∃ (W : C) (_hW : P W) (e : F.obj W ≅ T) (p : W ⟶ A) (q : W ⟶ V),
      F.map p = e.hom ≫ a ∧ F.map q = e.hom ≫ v := by
  let W := E.inverse.obj ⟨T, hT⟩
  let e : F.obj W.obj ≅ T :=
    (eF.app W).symm ≪≫ Q.ι.mapIso (E.counitIso.app ⟨T, hT⟩)
  obtain ⟨p, hp⟩ := map_surjective_of_equivalence P Q F E eF W.property hA (e.hom ≫ a)
  obtain ⟨q, hq⟩ := map_surjective_of_equivalence P Q F E eF W.property hV (e.hom ≫ v)
  exact ⟨W.obj, W.property, e, p, q, hp, hq⟩

/-! ### Glueability along étale morphisms -/

/-- An algebraic space étale over a glueable algebraic space is glueable. -/
private theorem isGlueable_of_isEtale {R R' : Type u} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R) (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
    {Y Z : AlgebraicSpaces B (Spec (.of R)) hX} (p : Y ⟶ Z)
    (hp : AlgebraicGeometry.Space.IsEtale B (Spec (.of R)) hX p.hom)
    (hZ : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Z) :
    AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Y := by
  intro W q hW hq
  apply hZ W (q ≫ p.hom) hW
  intro V φ hφ
  simpa only [Category.assoc] using hp V (φ ≫ q) (hq V φ hφ)

/-- The fibre product of a glueable algebraic space with an algebraic space étale over the
common target is glueable. -/
private theorem isGlueable_fibreProduct_of_isEtale {R R' : Type u} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R) (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
    {V W Y : AlgebraicSpaces B (Spec (.of R)) hX} (p : V ⟶ Y) (q : W ⟶ Y)
    (hq : AlgebraicGeometry.Space.IsEtale B (Spec (.of R)) hX q.hom)
    (hV : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX V) :
    AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX
      (AlgebraicSpaces.fiberProduct B (Spec (.of R)) hX p q) := by
  let fst : AlgebraicSpaces.fiberProduct B (Spec (.of R)) hX p q ⟶ V :=
    ObjectProperty.homMk (pullback.fst p.hom q.hom)
  let snd : AlgebraicSpaces.fiberProduct B (Spec (.of R)) hX p q ⟶ W :=
    ObjectProperty.homMk (pullback.snd p.hom q.hom)
  exact isGlueable_of_isEtale g f B hX fst
    (AlgebraicGeometry.Space.isEtale_of_isPullback B (Spec (.of R)) hX snd fst q p
      (AlgebraicSpaces.isPullback_fiberProduct B (Spec (.of R)) hX p q).flip hq) hV

/-! ### Descending a morphism along an étale covering -/

/-- A family of morphisms out of the members of an étale covering of `Y`, whose images under a
functor `F` are the restrictions of a single morphism `F.obj Y ⟶ F.obj Z`, descends to a
morphism `Y ⟶ Z` with that image, provided `F` is injective on the relevant hom-sets of fibre
products and morphisms out of `F.obj Y` are determined by their restrictions. -/
private theorem exists_lift_of_etaleCovering (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {D : Type*} [Category D] (F : AlgebraicSpaces B S hS ⥤ D)
    {Y Z : AlgebraicSpaces B S hS} {I : Type*} {V : I → AlgebraicSpaces B S hS}
    (p : ∀ i, V i ⟶ Y)
    (hcover : AlgebraicGeometry.Space.IsEtaleCovering B S hS (fun i ↦ (V i).obj)
      (fun i ↦ (p i).hom))
    (α : F.obj Y ⟶ F.obj Z) (a : ∀ i, V i ⟶ Z) (ha : ∀ i, F.map (a i) = F.map (p i) ≫ α)
    (hinj : ∀ i j, Function.Injective
      (F.map (X := AlgebraicSpaces.fiberProduct B S hS (p i) (p j)) (Y := Z)))
    (hext : ∀ β γ : F.obj Y ⟶ F.obj Z,
      (∀ i, F.map (p i) ≫ β = F.map (p i) ≫ γ) → β = γ) :
    ∃ f : Y ⟶ Z, F.map f = α := by
  have hcompat (i j : I) :
      (ObjectProperty.homMk (pullback.fst (p i).hom (p j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (p i) (p j) ⟶ V i) ≫ a i =
      (ObjectProperty.homMk (pullback.snd (p i).hom (p j).hom) :
        AlgebraicSpaces.fiberProduct B S hS (p i) (p j) ⟶ V j) ≫ a j := by
    apply hinj i j
    rw [F.map_comp, F.map_comp, ha i, ha j,
      ← Category.assoc, ← Category.assoc, ← F.map_comp, ← F.map_comp]
    rw [(AlgebraicSpaces.isPullback_fiberProduct B S hS (p i) (p j)).w]
  obtain ⟨f, hf, _⟩ := AlgebraicGeometry.Space.existsUnique_desc_of_fpqcCovering B S hS p
    (AlgebraicGeometry.Space.isFpqcCovering_of_isEtaleCovering B S hS
      (fun i ↦ (V i).obj) (fun i ↦ (p i).hom) hcover) Z a hcompat
  refine ⟨f, hext _ _ ?_⟩
  intro i
  rw [← F.map_comp, hf i, ha i]

/-! ### Full faithfulness -/

add_to_stacks 0F9T "faithfulness"
  BeauvilleLaszlo.Space.beauvilleLaszloGlueingSpaces_map_injective_of_isGlueable

/-- **Stacks 0F9T, fullness.** For a Beauville--Laszlo glueing pair `(g : R → R', f)`, a
morphism of glueing triples between the images of two algebraic spaces over `Spec R` which are
glueable for `(g, f)` comes from a morphism of algebraic spaces, provided the target has affine
diagonal.

Two results of the source are carried as hypotheses, since the library does not have them:
Stacks 0F9Q, the equivalence of the affine case, as `E`, and Stacks 0F9R for the property
"étale", as `hEtale`. -/
theorem beauvilleLaszloGlueingSpaces_map_surjective_of_isGlueable_of_affineDiagonal
    (R R' : Type u) [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R))) :
    let U' : Scheme.{u} := Spec (.of (Localization.Away (g f)))
    let U : Scheme.{u} := Spec (.of (Localization.Away f))
    let X' : Scheme.{u} := Spec (.of R')
    let X : Scheme.{u} := Spec (.of R)
    let gU : B.obj hU' ⟶ B.obj hU :=
      ⟨Spec.map (CommRingCat.ofHom (Localization.awayMap g f))⟩
    let gX' : B.obj hU' ⟶ B.obj hX' :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (g f))))⟩
    let jU : B.obj hU ⟶ B.obj hX :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))⟩
    let jX' : B.obj hX' ⟶ B.obj hX := ⟨Spec.map (CommRingCat.ofHom g)⟩
    ∀ (hcomm : gU ≫ jU = gX' ≫ jX')
      (E : AffineGlueingEquivalenceSpec g f B U' U X' hU' hU hX' hX gU gX'
        (beauvilleLaszloGlueingSpaces B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).functor),
      (∀ (Y Z : (affineGlueableSpaces g f B hX).FullSubcategory) (h : Y ⟶ Z),
        AlgebraicGeometry.Space.IsEtale B (Spec (.of R)) hX h.hom.hom ↔
          (AlgebraicGeometry.Space.IsEtale B U hU
              ((overU B U' U X' hU' hU hX' gU gX').map
                ((ObjectProperty.ι _).map (E.equivalence.functor.map h))).hom ∧
            AlgebraicGeometry.Space.IsEtale B U' hU'
              ((overU' B U' U X' hU' hU hX' gU gX').map
                ((ObjectProperty.ι _).map (E.equivalence.functor.map h))).hom ∧
            AlgebraicGeometry.Space.IsEtale B X' hX'
              ((overX' B U' U X' hU' hU hX' gU gX').map
                ((ObjectProperty.ι _).map (E.equivalence.functor.map h))).hom)) →
      ∀ (Y Z : AlgebraicSpaces B X hX),
      AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Y →
      AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Z →
      AlgebraicGeometry.Space.IsAffineHom B X hX (diag Z.1) →
      Function.Surjective (fun (φ : Y ⟶ Z) ↦
        (beauvilleLaszloGlueingSpaces
          B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).functor.map φ) := by
  intro U' U X' X gU gX' jU jX' hcomm E hEtale Y Z hY hZ hdiag
  let F := (beauvilleLaszloGlueingSpaces
    B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).functor
  intro α
  classical
  have hAffine {V W : AlgebraicSpaces B X hX}
      (hV : AlgebraicGeometry.Space.IsAffineSpace B X hX V.1 ∧
        AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX V)
      (hW : AlgebraicGeometry.Space.IsAffineSpace B X hX W.1 ∧
        AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX W) :
      Function.Surjective (F.map (X := V) (Y := W)) :=
    map_surjective_of_equivalence _ _ F E.equivalence E.functorIso hV hW
  obtain ⟨I, W, p, hcover, hW⟩ :=
    (AlgebraicGeometry.Space.exists_etaleCovering_iff_isGlueable g f hglue B hX Y).mpr hY
  let V (i : I) : AlgebraicSpaces B X hX :=
    ⟨yoneda.obj (W i), hcover.source_isAlgebraicSpace i⟩
  let q (i : I) : V i ⟶ Y := ObjectProperty.homMk (p i)
  have hV (i : I) : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX (V i) :=
    isGlueable_of_isEtale g f B hX (q i) (hcover.etale i) hY
  have hAV (i : I) : AlgebraicGeometry.Space.IsAffineSpace B X hX (V i).1 :=
    ⟨W i, (hW i).1, ⟨Iso.refl _⟩⟩
  have hdesc {Y' : AlgebraicSpaces B X hX} {I' : Type (u + 1)} {V' : I' → AlgebraicSpaces B X hX}
      (q' : ∀ i, V' i ⟶ Y')
      (hc : AlgebraicGeometry.Space.IsEtaleCovering B X hX (fun i ↦ (V' i).obj)
        (fun i ↦ (q' i).hom))
      (hV' : ∀ i, AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX (V' i))
      (α' : F.obj Y' ⟶ F.obj Z)
      (hlocal : ∀ i, ∃ a : V' i ⟶ Z, F.map a = F.map (q' i) ≫ α') :
      ∃ a : Y' ⟶ Z, F.map a = α' := by
    choose a ha using hlocal
    apply exists_lift_of_etaleCovering B X hX F q' hc α' a ha
    · intro i j
      exact beauvilleLaszloGlueingSpaces_map_injective_of_isGlueable
        R R' g f hglue B hU' hU hX' hX hcomm _ Z
        (isGlueable_fibreProduct_of_isEtale g f B hX (q' i) (q' j) (hc.etale j) (hV' i)) hZ
    · intro β γ h
      exact glueingFunctor_hom_ext_of_fpqcCovering B U' U X' X
        hU' hU hX' hX gU gX' jU jX' hcomm _ q'
        (AlgebraicGeometry.Space.isFpqcCovering_of_isEtaleCovering B X hX _ _ hc) h
  by_cases hAZ : AlgebraicGeometry.Space.IsAffineSpace B X hX Z.1
  · exact hdesc q hcover hV α (fun i ↦ hAffine ⟨hAV i, hV i⟩ ⟨hAZ, hZ⟩ (F.map (q i) ≫ α))
  · refine hdesc q hcover hV α fun i ↦ ?_
    obtain ⟨J, T, t, hTcover, hT⟩ :=
      (AlgebraicGeometry.Space.exists_etaleCovering_iff_isGlueable g f hglue B hX Z).mpr hZ
    let A (j : J) : AlgebraicSpaces B X hX :=
      ⟨yoneda.obj (T j), hTcover.source_isAlgebraicSpace j⟩
    let b (j : J) : A j ⟶ Z := ObjectProperty.homMk (t j)
    have hA (j : J) : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX (A j) :=
      isGlueable_of_isEtale g f B hX (b j) (hTcover.etale j) hZ
    have hAA (j : J) : AlgebraicGeometry.Space.IsAffineSpace B X hX (A j).1 :=
      ⟨T j, (hT j).1, ⟨Iso.refl _⟩⟩
    have hclosed {K : Type u} [Field K] (a : R →+* K) (ha : a f = 0) :
        ∃! b : R' →+* K, b.comp g = a := by
      obtain ⟨e, he⟩ : ∃ e : (R ⧸ Ideal.span {f}) ≃+* (R' ⧸ Ideal.span {g f}),
          ∀ r, e (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (g r) := by
        have hdom : (Ideal.span ({f} : Set R)) ^ 1 = Ideal.span ({f} : Set R) := pow_one _
        have hcod : (Ideal.span ({g f} : Set R')) ^ 1 = Ideal.span ({g f} : Set R') := pow_one _
        refine ⟨(Ideal.quotEquivOfEq hdom.symm).trans
          ((RingEquiv.ofBijective _ (hglue.1 1 Nat.one_pos)).trans
            (Ideal.quotEquivOfEq hcod)), fun r ↦ ?_⟩
        simp [_root_.BeauvilleLaszlo.quotientPowMap]
      exact existsUnique_lift_of_quotientEquiv g f e he a ha
    let G := beauvilleLaszloGlueingSpaces B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm
    let OU := overU B U' U X' hU' hU hX' gU gX'
    let OM := overU' B U' U X' hU' hU hX' gU gX'
    let OX := overX' B U' U X' hU' hU hX' gU gX'
    have hFimage (Y : AlgebraicSpaces B X hX)
        (hY : AlgebraicGeometry.Space.IsAffineSpace B X hX Y.1 ∧
          AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Y) :
        AlgebraicGeometry.Space.IsAffineSpace B U hU (OU.obj (F.obj Y)).1 ∧
        AlgebraicGeometry.Space.IsAffineSpace B U' hU' (OM.obj (F.obj Y)).1 ∧
        AlgebraicGeometry.Space.IsAffineSpace B X' hX' (OX.obj (F.obj Y)).1 := by
      let e := E.functorIso.app ⟨Y, hY⟩
      have hh := (E.equivalence.functor.obj ⟨Y, hY⟩).property
      exact ⟨isAffineSpace_of_iso B U hU (OU.mapIso e) hh.1,
        isAffineSpace_of_iso B U' hU' (OM.mapIso e) hh.2.1,
        isAffineSpace_of_iso B X' hX' (OX.mapIso e) hh.2.2⟩
    have hbAff (j : J) : AlgebraicGeometry.Space.IsAffineHom B X hX (b j).hom :=
      isAffineHom_of_affineSource_of_affineDiagonal B X hX ⟨T j, (hT j).1⟩ (t j) hdiag
    choose D dA dV hcond hDU hDM hDX using fun j : J ↦
      exists_glueingData_pullback B U' U X' hU' hU hX' gU gX'
        (F.map (b j)) (F.map (q i) ≫ α)
    have hD (j : J) :
        AlgebraicGeometry.Space.IsAffineSpace B U hU (OU.obj (D j)).1 ∧
        AlgebraicGeometry.Space.IsAffineSpace B U' hU' (OM.obj (D j)).1 ∧
        AlgebraicGeometry.Space.IsAffineSpace B X' hX' (OX.obj (D j)).1 := by
      refine ⟨?_, ?_, ?_⟩
      · exact isAffineSpace_of_isPullback_of_isAffineHom B U hU (hDU j)
          (component_isAffineHom B U X hU hX jU _ G.overUIso (b j) (hbAff j))
          (hFimage (V i) ⟨hAV i, hV i⟩).1
      · exact isAffineSpace_of_isPullback_of_isAffineHom B U' hU' (hDM j)
          (component_isAffineHom B U' X hU' hX (gU ≫ jU) _ G.overU'Iso (b j) (hbAff j))
          (hFimage (V i) ⟨hAV i, hV i⟩).2.1
      · exact isAffineSpace_of_isPullback_of_isAffineHom B X' hX' (hDX j)
          (component_isAffineHom B X' X hX' hX jX' _ G.overX'Iso (b j) (hbAff j))
          (hFimage (V i) ⟨hAV i, hV i⟩).2.2
    choose L hL eL pL qL hpL hqL using fun j : J ↦
      exists_span_of_equivalence _ _ F E.equivalence E.functorIso
        ⟨hAA j, hA j⟩ ⟨hAV i, hV i⟩ (hD j) (dA j) (dV j)
    have hmap (j : J) : F.map (pL j ≫ b j) = F.map (qL j) ≫ (F.map (q i) ≫ α) := by
      rw [F.map_comp, hpL j, hqL j, Category.assoc, hcond j, Category.assoc]
    have hbEt (j : J) : (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B X hX)).presheaf (b j).hom :=
      etalePresheaf_of_isEtale_yoneda B X hX (T j) (t j) (hTcover.etale j)
    have hqEt (j : J) :
        AlgebraicGeometry.Space.IsEtale B U hU (OU.map (F.map (qL j))).hom ∧
        AlgebraicGeometry.Space.IsEtale B U' hU' (OM.map (F.map (qL j))).hom ∧
        AlgebraicGeometry.Space.IsEtale B X' hX' (OX.map (F.map (qL j))).hom := by
      have htU := AlgebraicGeometry.Space.isEtale_of_isPullback B U hU _ _ _ _ (hDU j)
        (component_isEtale B U X hU hX jU _ G.overUIso (b j) (hbEt j))
      have htM := AlgebraicGeometry.Space.isEtale_of_isPullback B U' hU' _ _ _ _ (hDM j)
        (component_isEtale B U' X hU' hX (gU ≫ jU) _ G.overU'Iso (b j) (hbEt j))
      have htX := AlgebraicGeometry.Space.isEtale_of_isPullback B X' hX' _ _ _ _ (hDX j)
        (component_isEtale B X' X hX' hX jX' _ G.overX'Iso (b j) (hbEt j))
      have htransfer (S₀ : Scheme.{u}) (hS₀ : B.Contains S₀)
          (O : GlueingData B U' U X' hU' hU hX' gU gX' ⥤ AlgebraicSpaces B S₀ hS₀)
          (ht : AlgebraicGeometry.Space.IsEtale B S₀ hS₀ (O.map (dV j)).hom) :
          AlgebraicGeometry.Space.IsEtale B S₀ hS₀ (O.map (F.map (qL j))).hom := by
        let e : Arrow.mk (O.map (F.map (qL j))).hom ≅ Arrow.mk (O.map (dV j)).hom :=
          Arrow.isoMk ((ObjectProperty.ι _).mapIso (O.mapIso (eL j))) (Iso.refl _)
            (by
              show (O.map (eL j).hom).hom ≫ (O.map (dV j)).hom =
                (O.map (F.map (qL j))).hom ≫ 𝟙 _
              rw [Category.comp_id]
              simpa only [O.map_comp, ObjectProperty.FullSubcategory.comp_hom] using
                congrArg (fun a ↦ (O.map a).hom) (hqL j).symm)
        exact isEtale_of_arrowIso B S₀ hS₀ e.symm ht
      exact ⟨htransfer U hU OU htU, htransfer U' hU' OM htM, htransfer X' hX' OX htX⟩
    have hqLEt (j : J) : AlgebraicGeometry.Space.IsEtale B X hX (qL j).hom := by
      let qL' : (⟨L j, hL j⟩ : (affineGlueableSpaces g f B hX).FullSubcategory) ⟶
          ⟨V i, hAV i, hV i⟩ := ObjectProperty.homMk (qL j)
      apply (hEtale ⟨L j, hL j⟩ ⟨V i, hAV i, hV i⟩ qL').mpr
      refine ⟨?_, ?_, ?_⟩
      · exact map_property_of_natIso
          (fun {V W} p ↦ AlgebraicGeometry.Space.IsEtale B U hU p)
          (CategoryTheory.Functor.isoWhiskerRight E.functorIso (OU ⋙ ObjectProperty.ι _))
          qL' (hqEt j).1
      · exact map_property_of_natIso
          (fun {V W} p ↦ AlgebraicGeometry.Space.IsEtale B U' hU' p)
          (CategoryTheory.Functor.isoWhiskerRight E.functorIso (OM ⋙ ObjectProperty.ι _))
          qL' (hqEt j).2.1
      · exact map_property_of_natIso
          (fun {V W} p ↦ AlgebraicGeometry.Space.IsEtale B X' hX' p)
          (CategoryTheory.Functor.isoWhiskerRight E.functorIso (OX ⋙ ObjectProperty.ι _))
          qL' (hqEt j).2.2
    refine hdesc qL ?_ (fun j ↦ (hL j).2) _ fun j ↦ ⟨pL j ≫ b j, hmap j⟩
    refine ⟨(V i).property, fun j ↦ (L j).property, hqLEt, ?_⟩
    have hfactor {K : Type u} [Field K] (a : R →+* K) :
        (∃ c : Localization.Away f →+* K, c.comp (algebraMap R (Localization.Away f)) = a) ∨
        (∃ c : R' →+* K, c.comp g = a) := by
      by_cases ha : a f = 0
      · exact Or.inr (hclosed a ha).exists
      · exact Or.inl ⟨IsLocalization.Away.lift f (isUnit_iff_ne_zero.mpr ha),
          IsLocalization.Away.lift_comp f (isUnit_iff_ne_zero.mpr ha)⟩
    apply Set.eq_univ_iff_forall.mpr
    intro x
    induction x using Quot.inductionOn with
    | _ pt =>
      let a : R →+* pt.carrier := (Spec.preimage pt.toBase).hom
      rcases hfactor a with ⟨c, hc⟩ | ⟨c, hc⟩
      · let s : Spec (.of pt.carrier) ⟶ U := Spec.map (CommRingCat.ofHom c)
        have hs : s ≫ jU.hom = pt.toBase := by
          show Spec.map (CommRingCat.ofHom c) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) = pt.toBase
          rw [← Spec.map_comp, ← Spec.map_preimage pt.toBase]
          congr 1
          exact congrArg CommRingCat.ofHom hc
        obtain ⟨v, hv⟩ := exists_restricted_point_of_base_factorization
          B U X hU hX jU (V i).obj pt s hs
        obtain ⟨j, w, hw⟩ := exists_global_cover_point_of_component
          B U X hU hX jU A b hTcover.jointly_surjective
          F OU G.overUIso (F.map (q i) ≫ α) D dA dV hDU L eL qL hqL v
        exact Set.mem_iUnion.mpr ⟨j, Set.mem_range.mpr ⟨w, hw.trans hv⟩⟩
      · let s : Spec (.of pt.carrier) ⟶ X' := Spec.map (CommRingCat.ofHom c)
        have hs : s ≫ jX'.hom = pt.toBase := by
          show Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom g) = pt.toBase
          rw [← Spec.map_comp, ← Spec.map_preimage pt.toBase]
          congr 1
          exact congrArg CommRingCat.ofHom hc
        obtain ⟨v, hv⟩ := exists_restricted_point_of_base_factorization
          B X' X hX' hX jX' (V i).obj pt s hs
        obtain ⟨j, w, hw⟩ := exists_global_cover_point_of_component
          B X' X hX' hX jX' A b hTcover.jointly_surjective
          F OX G.overX'Iso (F.map (q i) ≫ α) D dA dV hDX L eL qL hqL v
        exact Set.mem_iUnion.mpr ⟨j, Set.mem_range.mpr ⟨w, hw.trans hv⟩⟩

end BeauvilleLaszlo.Space

end
