module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralBaseChangeReduction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Crossing from set coefficients to abelian coefficients in the étale base change comparison

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes with `f` finite. Stacks 0959 identifies `g^{-1} f_*` with
`f'_* (g')^{-1}` for sheaves of **sets**, and
`AlgebraicGeometry.SmallEtale.isIso_mateEquiv_symm_unboundedBaseChangeMate` carries that
identification onto the presentation of the small étale site that the proper base change
development uses. This file crosses the remaining gap, from sheaves of sets to sheaves of
**abelian groups**, and so discharges the last input of Stacks 0A4E that was previously carried
as a hypothesis.

The device is again `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`: a mate
transports along a change of the four categories of its square. The four functors joining the
two squares are all composition with the forgetful functor of abelian groups,
`CategoryTheory.sheafCompose`. That functor **reflects** isomorphisms, which is all the
transport lemma asks of the functor at the lower right corner, and it commutes with direct image
on the nose — direct image is restriction along a functor of sites, so the two ways around each
side face through a direct image are the same functor and the comparison filling it is the
identity.

What is not formal is the comparison filling the two side faces through an **inverse** image.
Inverse image is left Kan extension followed by sheafification, and composition with the
forgetful functor commutes with neither for free. It commutes with sheafification because the
small étale topology preserves sheafification along the forgetful functor, and with the Kan
extension because base change of étale schemes is representably flat, so the costructured-arrow
categories indexing the Kan extension are filtered and the forgetful functor preserves filtered
colimits of that size. That is
`Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange` below, the
argument already written out in
`Stacks.EtaleCohomology.etaleAbelianInverseImage_preservesFiniteLimits` re-aimed at
`CategoryTheory.CostructuredArrow.proj`.

**Both descriptions of that comparison are needed, and they must be identified.** A comparison
assembled from `CategoryTheory.Functor.leftKanExtensionCompIsoOfPreserves` and
`CategoryTheory.sheafComposeNatTrans` is visibly invertible, but it is not built as a comparison
of left adjoints, so its mate is not pinned by its construction; the comparison defined as the
mate of the strict direct-image comparison has the mate that the cube identity needs by
construction, but nothing says it is invertible. The identification is
`Stacks.EtaleCohomology.coefficientPullbackTwoSquare_app`, and it rests on the single equation
`Stacks.EtaleCohomology.coefficientPullbackComparison_unit`: the comparison built from the Kan
extension and from sheafification matches the units of the two inverse-image/direct-image
adjunctions. Mathlib's `CategoryTheory.unit_mateEquiv_symm` turns that equation into the
identification, a morphism out of an inverse image being determined by its adjoint transpose.

## Main definitions

* `Stacks.EtaleCohomology.coefficientPushforwardTwoSquare` — the comparison of the two composites
  of a direct image with a change of coefficients; it is the identity.
* `Stacks.EtaleCohomology.coefficientPullbackTwoSquare` — its mate, the comparison of the two
  composites of an inverse image with a change of coefficients.

## Main results

* `Stacks.EtaleCohomology.coefficientPullbackComparison_unit` — the Kan-extension description of
  the inverse-image comparison matches the units of the two adjunctions.
* `Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare` — the inverse-image comparison is
  invertible.
* `Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange` — the forgetful
  functor of abelian groups preserves left Kan extensions along the opposite of base change of
  étale schemes.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isIso_smallEtaleBaseChangeNatTrans` —
  **the underived comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` of abelian sheaves is invertible as
  soon as the comparison at set coefficients is.** Nothing is assumed of the square: finiteness
  enters only through that hypothesis.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite` — the previous statement with
  the set-valued hypothesis supplied by Stacks 0959, for a cartesian square with `f` finite, the
  square being drawn from a big étale site.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite` — **Stacks
  0A4E**: the derived base change map `g^{-1} Rf_* F ⟶ Rf'_* (g')^{-1} F` is invertible for every
  abelian sheaf `F` on the small étale site of `X`.

## Implementation notes

**Why a big étale site appears in the hypotheses.** Stacks 0959 is proved in this library for
morphisms of a big étale site, so the containment is carried as an explicit hypothesis: the four
schemes and the four morphisms of the square are taken in the underlying category of a big étale
site `B`, and the conclusion is about their images under `B.inclusion`. This is set-theoretic
bookkeeping about the ambient site, upstream of the geometry and absent from the conclusion; no
invertibility is assumed anywhere. The hypothesis is *not* a restriction:
`AlgebraicGeometry.BigEtaleSite.exists_contains_of_small` produces a big étale site containing
any small set of schemes, and
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbFinite` discharges it for an
arbitrary square.

**Everything that can be is proved abstractly.** The sites of the étale development are
`CategoryTheory.MorphismProperty.Over` at `AlgebraicGeometry.Etale`, where `rw` and `simp`
frequently fail to match because the goal is not type-correct at the transparency at which they
work. Each step is therefore either a statement about an arbitrary site with an arbitrary
coefficient functor, or a `private` lemma about abstract categories applied to explicit
arguments, as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransfer`.

## References

* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 0A4E](https://stacks.math.columbia.edu/tag/0A4E)
* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-! ### Reassociation and cancellation, done where `rw` works -/

section Abstract

/-- Cancelling the image of an identity and an identity at the end of a composite. -/
private lemma comp_comp_mapid_id {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Fn : 𝒞 ⥤ 𝒟)
    {X Y : 𝒟} {W : 𝒞} (m : X ⟶ Y) (n : Y ⟶ Fn.obj W) :
    (m ≫ n) ≫ Fn.map (𝟙 W) ≫ 𝟙 (Fn.obj W) = m ≫ n := by
  rw [Fn.map_id, Category.id_comp, Category.comp_id]

/-- Two whiskerings on the left compose into the whiskering of the composite. -/
private lemma comp_whiskerLeft_two {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟] [Category* ℰ]
    (Fn : 𝒞 ⥤ 𝒟) {P Q R : 𝒟 ⥤ ℰ} {S : 𝒞 ⥤ ℰ} (m : S ⟶ Fn ⋙ P) (a : P ⟶ Q) (b : Q ⟶ R) :
    (m ≫ Functor.whiskerLeft Fn a) ≫ Functor.whiskerLeft Fn b =
      m ≫ Functor.whiskerLeft Fn (a ≫ b) := by
  rw [Category.assoc, Functor.whiskerLeft_comp]

/-- **The combination step behind the unit identity.** Two units of left Kan extensions matched
by a comparison `ι` up to the associator stay matched after `ι` is composed with a further
transformation `ts` of the extended functor. -/
private lemma whisker_combine {𝒞 𝒟 𝒜 ℬ : Type*} [Category* 𝒞] [Category* 𝒟] [Category* 𝒜]
    [Category* ℬ] (W : 𝒞 ⥤ 𝒟) (Gf : 𝒜 ⥤ ℬ) {S : 𝒞 ⥤ 𝒜} {E₁ E₂ : 𝒟 ⥤ 𝒜} {F₁ : 𝒟 ⥤ ℬ}
    (uA : S ⟶ W ⋙ E₁) (uB : S ⋙ Gf ⟶ W ⋙ F₁) (ι : F₁ ⟶ E₁ ⋙ Gf) (ts : E₁ ⟶ E₂)
    (h : uB ≫ Functor.whiskerLeft W ι =
      Functor.whiskerRight uA Gf ≫ (Functor.associator W E₁ Gf).hom) :
    uB ≫ Functor.whiskerLeft W (ι ≫ Functor.whiskerRight ts Gf) =
      Functor.whiskerRight (uA ≫ Functor.whiskerLeft W ts) Gf := by
  refine NatTrans.ext (funext fun V => ?_)
  have hV := NatTrans.congr_app h V
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at hV ⊢
  rw [← Category.assoc, hV, ← Gf.map_comp]

/-- **Cancelling the four identities of the cube identity.** Two morphisms that agree stay in
agreement after padding with identities on either side, which is the shape in which the cube
identity presents the comparison of the two composite direct images: the four comparisons of
direct images with a change of coefficients are all identities. -/
private lemma pad_identities {𝒟 : Type*} [Category* 𝒟] {X Y : 𝒟} (m n : X ⟶ Y) (a b : X ⟶ X)
    (c d : Y ⟶ Y) (h : m = n) (ha : a = 𝟙 X) (hb : b = 𝟙 X) (hc : c = 𝟙 Y) (hd : d = 𝟙 Y) :
    (a ≫ b ≫ m) ≫ c = n ≫ d := by
  rw [h, ha, hb, hc, hd, Category.id_comp, Category.id_comp]

/-- A morphism is its own composite with the identity. -/
private lemma eq_comp_id {𝒟 : Type*} [Category* 𝒟] {X Y : 𝒟} (m : X ⟶ Y) : m = m ≫ 𝟙 Y :=
  (Category.comp_id m).symm

-- NO `sheaf_comp_hom` HERE. It stated exactly
-- `CategoryTheory.ObjectProperty.FullSubcategory.comp_hom`
-- (Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean:78), which is `@[simp, reassoc]`
-- and proved by `rfl` just as this copy was; `Sheaf J A` is an `ObjectProperty` full
-- subcategory in this pin, so Mathlib's lemma applies directly.

end Abstract

/-! ### The unit of the inverse-image adjunction built from a Kan extension -/

section Unit

variable {C D : Type*} [Category* C] [Category* D] (uf : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
  {A : Type*} [Category* A]

/-- Direct image acts on a morphism of sheaves by restriction along the functor of sites. -/
private lemma push_map_hom {M N : Sheaf K A} (ψ : M ⟶ N) :
    ((uf.sheafPushforwardContinuous A J K).map ψ).hom = Functor.whiskerLeft uf.op ψ.hom := rfl

variable [HasWeakSheafify K A] [∀ P : Cᵒᵖ ⥤ A, uf.op.HasLeftKanExtension P]

/-- **The unit of the inverse-image/direct-image adjunction of
`CategoryTheory.Functor.sheafPullbackConstruction`**: the unit of the left Kan extension followed
by the sheafification unit, restricted along the functor of sites. -/
private lemma sheafAdj_unit_hom (c : Sheaf J A) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A J K).unit.app c).hom =
      uf.op.leftKanExtensionUnit c.obj ≫
        Functor.whiskerLeft uf.op (toSheafify K (uf.op.leftKanExtension c.obj)) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
      (L := Functor.sheafPullbackConstruction.sheafPullback uf A J K)
      (R := uf.sheafPushforwardContinuous A J K)
      ((uf.op.lanAdjunction A).comp (sheafificationAdjunction K A))
      (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id (Sheaf K A))
      (Iso.refl _) (Iso.refl _) c
  refine h.trans ?_
  simp only [Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
    sheafificationAdjunction_unit_app, ObjectProperty.ι_obj, Iso.refl_hom, NatTrans.id_app]
  exact comp_comp_mapid_id _ _ _

end Unit

/-! ### Changing the coefficient category in the two images -/

section Coefficients

variable {C D : Type*} [Category* C] [Category* D] (uf : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
  {A B : Type*} [Category* A] [Category* B] (Gf : A ⥤ B)
  [HasWeakSheafify K A] [HasWeakSheafify K B]
  [∀ P : Cᵒᵖ ⥤ A, uf.op.HasLeftKanExtension P] [∀ P : Cᵒᵖ ⥤ B, uf.op.HasLeftKanExtension P]
  [Gf.PreservesLeftKanExtensions uf.op]
  [J.HasSheafCompose Gf] [K.HasSheafCompose Gf] [K.PreservesSheafification Gf]

/-- **Direct image commutes with a change of coefficients on the nose.** Both composites send a
sheaf to the restriction of its sections along the functor of sites, followed by the coefficient
functor, so the comparison filling the square is the identity. -/
public def coefficientPushforwardTwoSquare :
    TwoSquare (uf.sheafPushforwardContinuous A J K) (sheafCompose K Gf) (sheafCompose J Gf)
      (uf.sheafPushforwardContinuous B J K) :=
  TwoSquare.mk _ _ _ _ (𝟙 _)

/-- **The comparison of the two composites of an inverse image with a change of coefficients, as
built from the Kan extension and from sheafification.** The coefficient functor preserves the
left Kan extension by hypothesis and the sheafification by hypothesis, so each half is an
isomorphism. -/
public def coefficientPullbackComparison (c : Sheaf J A) :
    (Functor.sheafPullbackConstruction.sheafPullback uf B J K).obj ((sheafCompose J Gf).obj c) ⟶
      (sheafCompose K Gf).obj
        ((Functor.sheafPullbackConstruction.sheafPullback uf A J K).obj c) :=
  (presheafToSheaf K B).map (Gf.leftKanExtensionCompIsoOfPreserves c.obj uf.op).inv ≫
    (sheafComposeNatTrans K Gf (sheafificationAdjunction K A)
      (sheafificationAdjunction K B)).app (uf.op.leftKanExtension c.obj)

private instance isIso_coefficientPullbackComparison (c : Sheaf J A) :
    IsIso (coefficientPullbackComparison uf J K Gf c) := by
  change IsIso ((presheafToSheaf K B).map
      (Gf.leftKanExtensionCompIsoOfPreserves c.obj uf.op).inv ≫
    (sheafComposeNatTrans K Gf (sheafificationAdjunction K A)
      (sheafificationAdjunction K B)).app (uf.op.leftKanExtension c.obj))
  infer_instance

omit [uf.IsContinuous J K] [K.PreservesSheafification Gf] in
/-- The comparison, precomposed with the sheafification unit, is the comparison of the Kan
extensions followed by the coefficient functor applied to the sheafification unit. -/
private lemma coefficientPullbackComparison_hom_fac (c : Sheaf J A) :
    toSheafify K (uf.op.leftKanExtension (c.obj ⋙ Gf)) ≫
        (coefficientPullbackComparison uf J K Gf c).hom =
      (Gf.leftKanExtensionCompIsoOfPreserves c.obj uf.op).inv ≫
        Functor.whiskerRight (toSheafify K (uf.op.leftKanExtension c.obj)) Gf := by
  change toSheafify K (uf.op.leftKanExtension (c.obj ⋙ Gf)) ≫
      sheafifyMap K (Gf.leftKanExtensionCompIsoOfPreserves c.obj uf.op).inv ≫
      ((sheafComposeNatTrans K Gf (sheafificationAdjunction K A)
        (sheafificationAdjunction K B)).app (uf.op.leftKanExtension c.obj)).hom = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  exact congrArg (fun z => (Gf.leftKanExtensionCompIsoOfPreserves c.obj uf.op).inv ≫ z)
    (sheafComposeNatTrans_fac K Gf (sheafificationAdjunction K A)
      (sheafificationAdjunction K B) (uf.op.leftKanExtension c.obj))

omit [K.PreservesSheafification Gf] in
/-- **The inverse-image comparison matches the units of the two
inverse-image/direct-image adjunctions.** This is the one equation that identifies the
Kan-extension description of the comparison with the mate of the direct-image comparison; it
holds because the left Kan extension of the composite is the composite of the left Kan
extension, compatibly with the units, and likewise for sheafification. -/
public theorem coefficientPullbackComparison_unit (c : Sheaf J A) :
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf B J K).unit.app
          ((sheafCompose J Gf).obj c) ≫
        (uf.sheafPushforwardContinuous B J K).map
          (coefficientPullbackComparison uf J K Gf c) =
      (sheafCompose J Gf).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A J K).unit.app c) ≫
        (coefficientPushforwardTwoSquare uf J K Gf).app
          ((Functor.sheafPullbackConstruction.sheafPullback uf A J K).obj c) := by
  refine Sheaf.hom_ext ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    push_map_hom, sheafCompose_map_hom, sheafAdj_unit_hom,
    sheafAdj_unit_hom]
  refine Eq.trans ?_ (eq_comp_id _)
  change (uf.op.leftKanExtensionUnit (c.obj ⋙ Gf) ≫
      Functor.whiskerLeft uf.op (toSheafify K (uf.op.leftKanExtension (c.obj ⋙ Gf)))) ≫
      Functor.whiskerLeft uf.op (coefficientPullbackComparison uf J K Gf c).hom = _
  refine Eq.trans (comp_whiskerLeft_two uf.op _ _ _) ?_
  refine Eq.trans (congrArg
    (fun z => uf.op.leftKanExtensionUnit (c.obj ⋙ Gf) ≫ Functor.whiskerLeft uf.op z)
    (coefficientPullbackComparison_hom_fac uf J K Gf c)) ?_
  exact whisker_combine uf.op Gf _ _ _ _
    (Functor.leftKanExtensionCompIsoOfPreserves_inv_fac Gf c.obj uf.op)

/-- **The comparison of the two composites of an inverse image with a change of coefficients**,
defined as the mate of `Stacks.EtaleCohomology.coefficientPushforwardTwoSquare`. Taking it as the
mate is what makes it usable in the cube identity of
`Stacks.CategoryTheory.mateEquiv_symm_hComp_eq`; that it is invertible is
`Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare`, proved by identifying it with the
Kan-extension description. -/
public def coefficientPullbackTwoSquare :
    TwoSquare (sheafCompose J Gf) (Functor.sheafPullbackConstruction.sheafPullback uf A J K)
      (Functor.sheafPullbackConstruction.sheafPullback uf B J K) (sheafCompose K Gf) :=
  (mateEquiv (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf B J K)).symm
      (coefficientPushforwardTwoSquare uf J K Gf)

omit [Gf.PreservesLeftKanExtensions uf.op] [K.PreservesSheafification Gf] in
/-- The mate of the inverse-image comparison is the direct-image comparison, by construction. -/
public theorem mateEquiv_coefficientPullbackTwoSquare :
    mateEquiv (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A J K)
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf B J K)
        (coefficientPullbackTwoSquare uf J K Gf) =
      coefficientPushforwardTwoSquare uf J K Gf :=
  Equiv.apply_symm_apply _ _

omit [K.PreservesSheafification Gf] in
/-- **The two descriptions of the inverse-image comparison agree.** The mate of the direct-image
comparison and the comparison built from the Kan extension and from sheafification have the same
adjoint transpose, by `Stacks.EtaleCohomology.coefficientPullbackComparison_unit`, hence are
equal. -/
public theorem coefficientPullbackTwoSquare_app (c : Sheaf J A) :
    (coefficientPullbackTwoSquare uf J K Gf).app c =
      coefficientPullbackComparison uf J K Gf c := by
  refine ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf B J K).homEquiv
    _ _).injective ?_
  simp only [Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A J K)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf B J K)
      (coefficientPushforwardTwoSquare uf J K Gf) c).symm.trans
    (coefficientPullbackComparison_unit uf J K Gf c).symm

/-- **The inverse-image comparison is invertible.** -/
public instance isIso_coefficientPullbackTwoSquare :
    IsIso (coefficientPullbackTwoSquare uf J K Gf) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro c
  rw [coefficientPullbackTwoSquare_app]
  exact isIso_coefficientPullbackComparison uf J K Gf c

end Coefficients

/-! ### The forgetful functor and the Kan extensions of the small étale site -/

/-- **The forgetful functor of abelian groups preserves left Kan extensions along the opposite of
base change of étale schemes.** Base change `Stacks.EtaleCohomology.smallEtaleBaseChange` is
representably flat, so each costructured-arrow category indexing the pointwise left Kan extension
is filtered — it is opposite to a structured-arrow category, by
`CategoryTheory.structuredArrowOpEquivalence` — and the forgetful functor preserves filtered
colimits of that size. This is the argument of
`Stacks.EtaleCohomology.etaleAbelianInverseImage_preservesFiniteLimits` aimed at
`CategoryTheory.CostructuredArrow.proj` instead of at the evaluation of the Kan extension. -/
@[sga "4 I 5.8.3" "special case"]
public instance preservesLeftKanExtensions_forget_smallEtaleBaseChange {X Y : Scheme.{u}}
    (i : Y ⟶ X) :
    (forget AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions (smallEtaleBaseChange i).op := by
  intro P
  have hfil : ∀ V : Y.Etaleᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange i).op V) := fun V =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange i) V.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _
  infer_instance

/-! ### Stacks 0A4E -/

section BaseChange

variable (B : BigEtaleSite.{u}) {X X' Y Y' : B.Scheme}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)

/-- Composition with the forgetful functor, on abelian sheaves of Mathlib's small étale site of
a scheme of a big étale site. -/
private abbrev coefficientForgetSheaf (S : B.Scheme) :
    Sheaf (Scheme.smallEtaleTopology S.obj) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Scheme.smallEtaleTopology S.obj) (Type (u + 1)) :=
  sheafCompose (Scheme.smallEtaleTopology S.obj) (forget AddCommGrpCat.{u + 1})

/-- Inverse image of abelian sheaves on Mathlib's small étale site, along a morphism of the
underlying category of a big étale site. -/
private abbrev bigSiteAbelianPullback {S T : B.Scheme} (k : T ⟶ S) :
    Sheaf (Scheme.smallEtaleTopology S.obj) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Scheme.smallEtaleTopology T.obj) AddCommGrpCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtaleBaseChange (B.inclusion.map k)) AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology S.obj) (Scheme.smallEtaleTopology T.obj)

/-- The inverse-image/direct-image adjunction for abelian sheaves on Mathlib's small étale
site. -/
private abbrev abelianAdj {S T : B.Scheme} (k : T ⟶ S) :
    bigSiteAbelianPullback B k ⊣
      AlgebraicGeometry.SmallEtale.unboundedPushforward B AddCommGrpCat.{u + 1} k :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- Inverse image of sheaves of sets on Mathlib's small étale site, along a morphism of the
underlying category of a big étale site. -/
private abbrev unboundedPullback {S T : B.Scheme} (k : T ⟶ S) :
    Sheaf (Scheme.smallEtaleTopology S.obj) (Type (u + 1)) ⥤
      Sheaf (Scheme.smallEtaleTopology T.obj) (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtaleBaseChange (B.inclusion.map k)) (Type (u + 1))
    (Scheme.smallEtaleTopology S.obj) (Scheme.smallEtaleTopology T.obj)

/-- The inverse-image/direct-image adjunction for sheaves of sets on Mathlib's small étale
site. -/
private abbrev unboundedAdj {S T : B.Scheme} (k : T ⟶ S) :
    unboundedPullback B k ⊣
      AlgebraicGeometry.SmallEtale.unboundedPushforward B (Type (u + 1)) k :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- The comparison of the two composites of an inverse image with the change of coefficients,
for a morphism of the underlying category of a big étale site. -/
private abbrev bigSitePullbackForget {S T : B.Scheme} (k : T ⟶ S) :
    TwoSquare (coefficientForgetSheaf B S) (bigSiteAbelianPullback B k) (unboundedPullback B k)
      (coefficientForgetSheaf B T) :=
  coefficientPullbackTwoSquare (smallEtaleBaseChange (B.inclusion.map k))
    (Scheme.smallEtaleTopology S.obj) (Scheme.smallEtaleTopology T.obj)
    (forget AddCommGrpCat.{u + 1})

/-- **Direct image commutes with the change of coefficients on the nose**: both composites
restrict sections along base change and then forget the group structure. -/
private abbrev pushforwardForget {S T : B.Scheme} (k : T ⟶ S) :
    AlgebraicGeometry.SmallEtale.unboundedPushforward B AddCommGrpCat.{u + 1} k ⋙
        coefficientForgetSheaf B S ⟶
      coefficientForgetSheaf B T ⋙
        AlgebraicGeometry.SmallEtale.unboundedPushforward B (Type (u + 1)) k :=
  𝟙 _

private instance isIso_pushforwardForget {S T : B.Scheme} (k : T ⟶ S) :
    IsIso (pushforwardForget B k) := by
  change IsIso (𝟙 (AlgebraicGeometry.SmallEtale.unboundedPushforward B AddCommGrpCat.{u + 1} k ⋙
    coefficientForgetSheaf B S))
  infer_instance

/-- The comparison of `Stacks.EtaleCohomology.pushforwardForget` read in the other direction. -/
private abbrev pushforwardForget' {S T : B.Scheme} (k : T ⟶ S) :
    coefficientForgetSheaf B T ⋙
        AlgebraicGeometry.SmallEtale.unboundedPushforward B (Type (u + 1)) k ⟶
      AlgebraicGeometry.SmallEtale.unboundedPushforward B AddCommGrpCat.{u + 1} k ⋙
        coefficientForgetSheaf B S :=
  𝟙 _

private instance isIso_pushforwardForget' {S T : B.Scheme} (k : T ⟶ S) :
    IsIso (pushforwardForget' B k) := by
  change IsIso (𝟙 (coefficientForgetSheaf B T ⋙
    AlgebraicGeometry.SmallEtale.unboundedPushforward B (Type (u + 1)) k))
  infer_instance

/-- **The comparison of composite direct images around the square is compatible with the change
of coefficients.** Both sides restrict sections along the same composite of comparisons of base
changes of sites, so the statement is the compatibility of that restriction with the forgetful
functor. -/
private lemma unboundedBaseChangeMate_forget
    (F : Sheaf (Scheme.smallEtaleTopology X'.obj) AddCommGrpCat.{u + 1}) :
    (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B (Type (u + 1)) f g g' f'
          P hP₁ hP₂).app ((coefficientForgetSheaf B X').obj F) =
      (coefficientForgetSheaf B Y).map
        ((AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f'
          P hP₁ hP₂).app F) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun UU => ?_))
  obtain ⟨U⟩ := UU
  rw [AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate_app_hom_app, sheafCompose_map_hom,
    Functor.whiskerRight_app, AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate_app_hom_app]
  rfl

/-- **The cube identity for the change of coefficients.** The comparison of the two composite
direct images around the square at set coefficients, pasted with the comparisons of the two
coefficient categories, is the comparison at abelian coefficients. Every side comparison through
a direct image is an identity, so this is
`Stacks.EtaleCohomology.unboundedBaseChangeMate_forget` padded with identities. -/
private lemma coefficient_cube_eq :
    ((mateEquiv (abelianAdj B g') (unboundedAdj B g') (bigSitePullbackForget B g') ≫ᵥ
          AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B (Type (u + 1)) f g g' f'
            P hP₁ hP₂).whiskerRight (pushforwardForget B f)).whiskerLeft
        (pushforwardForget' B f') =
      AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f'
          P hP₁ hP₂ ≫ᵥ
        mateEquiv (abelianAdj B g) (unboundedAdj B g) (bigSitePullbackForget B g) := by
  rw [mateEquiv_coefficientPullbackTwoSquare, mateEquiv_coefficientPullbackTwoSquare]
  refine NatTrans.ext (funext fun F => ?_)
  rw [AlgebraicGeometry.SmallEtale.ts_whiskerLeft_app,
    AlgebraicGeometry.SmallEtale.ts_whiskerRight_app, AlgebraicGeometry.SmallEtale.ts_vComp_app,
    AlgebraicGeometry.SmallEtale.ts_vComp_app]
  exact pad_identities _ _ _ _ _ _ (unboundedBaseChangeMate_forget B f g g' f' P hP₁ hP₂ F)
    rfl (CategoryTheory.Functor.map_id _ _) (CategoryTheory.Functor.map_id _ _) rfl

/-- **The mate of the comparison of composite direct images is invertible at abelian
coefficients.** This is the transport of Stacks 0959 from sheaves of sets to sheaves of abelian
groups: the cube identity `Stacks.EtaleCohomology.coefficient_cube_eq` feeds
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`, whose hypothesis at the
lower right corner is only that composition with the forgetful functor reflects isomorphisms.

Nothing is assumed of the square: finiteness enters only through `hsets`.
`Stacks.EtaleCohomology.isIso_mateEquiv_symm_abelianBaseChangeMate` is this statement with
`hsets` supplied from a cartesian square and a finite `f`. -/
private lemma isIso_mateEquiv_symm_abelianBaseChangeMate_of_isIso (hcomm : g' ≫ f = f' ≫ g)
    (hsets : ∀ F, IsIso
      ((AlgebraicGeometry.smallEtaleBaseChangeNatTrans B g' f' f g hcomm).app F)) :
    IsIso ((mateEquiv (abelianAdj B g') (abelianAdj B g)).symm
      (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f'
        P hP₁ hP₂)) := by
  have hback :=
    AlgebraicGeometry.SmallEtale.isIso_mateEquiv_symm_unboundedBaseChangeMate_of_isIso
      B f g g' f' hcomm hsets P hP₁ hP₂ (unboundedAdj B g) (unboundedAdj B g')
  exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    (abelianAdj B g') (abelianAdj B g) (unboundedAdj B g') (unboundedAdj B g)
    (bigSitePullbackForget B g') (bigSitePullbackForget B g)
    (pushforwardForget B f) (pushforwardForget' B f')
    (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f'
      P hP₁ hP₂)
    (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B (Type (u + 1)) f g g' f' P hP₁ hP₂)
    (coefficient_cube_eq B f g g' f' P hP₁ hP₂)

/-- **The mate of the comparison of composite direct images is invertible at abelian
coefficients.** This is the transport of Stacks 0959 from sheaves of sets to sheaves of abelian
groups: the cube identity `Stacks.EtaleCohomology.coefficient_cube_eq` feeds
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`, whose hypothesis at the
lower right corner is only that composition with the forgetful functor reflects isomorphisms. -/
private lemma isIso_mateEquiv_symm_abelianBaseChangeMate
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)] (hcomm : g' ≫ f = f' ≫ g) :
    IsIso ((mateEquiv (abelianAdj B g') (abelianAdj B g)).symm
      (AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate B AddCommGrpCat.{u + 1} f g g' f'
        P hP₁ hP₂)) := by
  exact isIso_mateEquiv_symm_abelianBaseChangeMate_of_isIso B f g g' f' P hP₁ hP₂ hcomm
    fun F => AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans B g' f' f g sq hcomm F

end BaseChange

section Main

variable (B : BigEtaleSite.{u}) {X X' Y Y' : B.Scheme}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- **The underived base change comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` of abelian sheaves on
the small étale sites is invertible**, for a cartesian square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of the underlying category of a big étale site with `f` finite. This is Stacks 0959 at abelian
coefficients and at the presentation of the small étale site used here; the statement proved in
the library, `AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans`, is for sheaves of sets on
the size-bounded small étale site of Stacks 021B, and both changes are instances of the same
transport of a mate along a change of the four categories of its square. -/
public theorem isIso_etaleAbelianBaseChange_of_isIso_smallEtaleBaseChangeNatTrans
    (hcomm : g' ≫ f = f' ≫ g)
    (hsets : ∀ F, IsIso
      ((AlgebraicGeometry.smallEtaleBaseChangeNatTrans B g' f' f g hcomm).app F))
    (hw : B.inclusion.map g' ≫ B.inclusion.map f =
      B.inclusion.map f' ≫ B.inclusion.map g) :
    IsIso (etaleAbelianBaseChange.{u, 0} (B.inclusion.map f) (B.inclusion.map g)
      (B.inclusion.map g') (B.inclusion.map f') hw) := by
  have hkey := isIso_mateEquiv_symm_abelianBaseChangeMate_of_isIso B f g g' f' (g' ≫ f) rfl
    hcomm.symm hcomm hsets
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, 0}
    (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map g') (B.inclusion.map f') hw
    (B.inclusion.map (g' ≫ f)) (B.inclusion.map_comp g' f)
    ((congrArg B.inclusion.map hcomm).trans (B.inclusion.map_comp f' g))]
  exact hkey

/-- **Stacks 0959 at abelian coefficients** for a cartesian square with `f` finite: the case of
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isIso_smallEtaleBaseChangeNatTrans` in
which the invertibility at set coefficients is
`AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans`, Stacks 0959 itself. -/
public theorem isIso_etaleAbelianBaseChange_of_isFinite
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g)) [IsFinite (B.inclusion.map f)] :
    IsIso (etaleAbelianBaseChange.{u, 0} (B.inclusion.map f) (B.inclusion.map g)
      (B.inclusion.map g') (B.inclusion.map f') sq.w) :=
  have hcomm : g' ≫ f = f' ≫ g :=
    B.inclusion.map_injective (by rw [B.inclusion.map_comp, B.inclusion.map_comp]; exact sq.w)
  isIso_etaleAbelianBaseChange_of_isIso_smallEtaleBaseChangeNatTrans B f g g' f' hcomm
    (fun F => AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans B g' f' f g sq hcomm F) sq.w

/-- **Stacks 0A4E: cohomology commutes with base change for a finite morphism.** For a cartesian
square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of the underlying category of a big étale site with `f` finite, and every abelian sheaf `F` on
the small étale site of `X`, the base change map `g^{-1} Rf_* F ⟶ Rf'_* (g')^{-1} F` on
unbounded derived categories is an isomorphism.

No torsion condition on `F` is imposed — the source states the lemma for torsion sheaves, and
this is the stronger statement — and finiteness of `f'` is not assumed but obtained from the
square. The two inputs are
`Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_of_isIso`, which
reduces the derived statement to the underived comparison using the vanishing of the positive
higher direct images of a finite morphism, and
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite`, which is Stacks 0959 at
abelian coefficients. -/
@[stacks 0A4E "RESTRICTED: the cartesian square is carried as four objects and four morphisms of
the underlying category of a given big étale site `B`, the conclusion being about their images
under `B.inclusion`; that containment is the only hypothesis beyond the square being cartesian
with `f` finite, and coefficients are the abelian groups of `AddCommGrpCat.{u+1}`, which is
`Ab.{u+1}`. No torsion condition and no invertibility is assumed.", sga "4 XII 5.1" "(iii)"]
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g)) [IsFinite (B.inclusion.map f)]
    (F : Sheaf (Scheme.smallEtaleTopology (B.inclusion.obj X)) AddCommGrpCat.{u + 1}) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} (B.inclusion.map f) (B.inclusion.map g)
      (B.inclusion.map g') (B.inclusion.map f') sq.w F) :=
  isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_of_isIso.{u, 0}
    (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map g') (B.inclusion.map f') sq
    (isIso_etaleAbelianBaseChange_of_isFinite B f g g' f' sq) F

end Main

end Stacks.EtaleCohomology

end
