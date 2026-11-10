module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Points of an algebraic stack (Stacks 04XF, 04XG)

A *field-valued point* of a category over the big fppf site of `S` is an object of that
category lying over the spectrum of a field in the working universe, together with an
identification of its base with that spectrum. By the 2-Yoneda lemma this is the same thing
as a 1-morphism from the field spectrum to the associated stack. Two field-valued points are
*equivalent* when they admit a common field-valued refinement, i.e. a third field-valued
point with arrows to both; the two arrows encode the two 2-commutative triangles of the
source's definition. For a category fibred in groupoids this is an equivalence relation
(Stacks 04XF), and the set of *points* `|𝒳|` of the stack is the quotient (Stacks 04XG).

## Main definitions

* `AlgebraicGeometry.Stack.FieldValuedPoint`: a field-valued point of a based category over
  the big fppf site of `S`.
* `AlgebraicGeometry.Stack.FieldValuedPoint.HasCommonExtension`: the common-refinement
  relation, and `AlgebraicGeometry.Stack.FieldValuedPoint.setoid` the setoid it defines on a
  category fibred in groupoids.
* `AlgebraicGeometry.Stack.points`: **Stacks 04XG**, the set of points `|𝒳|`, with
  `AlgebraicGeometry.Stack.pointClass` the point represented by a field-valued point.
* `AlgebraicGeometry.Stack.fieldValuedPointMap` and `AlgebraicGeometry.Stack.pointsMap`: the
  action of a 1-morphism on field-valued points and on points.

## Main results

* `AlgebraicGeometry.Stack.FieldValuedPoint.hasCommonExtension_equivalence`: **Stacks 04XF**,
  common refinement is an equivalence relation.
* `AlgebraicGeometry.Stack.class_eq_class_iff_hasCommonExtension`: two field-valued points
  represent the same point exactly when they admit a common refinement.

## Implementation notes

Only transitivity has content. Given refinements `a` of `p, q` and `b` of `q, r`, the two
arrows `a ⟶ q` and `b ⟶ q` are mapped down to the site, where they become two field-valued
points of the representable presheaf `yoneda.obj (Spec κ(q))` dominating the tautological
one. Transitivity for an algebraic space — `AlgebraicGeometry.Space.FieldValuedPoint` and
`AlgebraicGeometry.Space.FieldValuedPoint.hasCommonExtension_trans` of Stacks 03BU, which is
where the size bookkeeping for the compositum of two field extensions lives — produces a
field spectrum in the site dominating both over `Spec κ(q)`, and the fibred-in-groupoids
property lifts it to an object of the category refining `a` and `b`, hence `p` and `r`.

A field-valued point records its base as an arbitrary object `base` of the site together
with an isomorphism `isSpec` of its underlying scheme with the field spectrum, rather than
as the canonical object `Spec κ ⟶ S` of the site; this is what makes the action of a
1-morphism on field-valued points (`AlgebraicGeometry.Stack.fieldValuedPointMap`) the
identity on the base. `canonicalSiteObject` and `siteObjectIso` convert to the canonical
form, which is the one Stacks 03BU uses.

The algebraic-stack axioms beyond being fibred in groupoids are nowhere used, so everything
is stated for a `CategoryTheory.BasedCategory` over the big fppf site with the
fibred-in-groupoids hypothesis carried explicitly. The object and morphism universes of the
total category are independent of the universe of the base schemes, and the source and
target of a 1-morphism may have different ones.

## References

* [Stacks Project, Tag 04XF](https://stacks.math.columbia.edu/tag/04XF)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v t v' t' v'' t''

/-- An object of a category over a big fppf site, based over the spectrum of a field. By
2-Yoneda it is a 1-morphism from that spectrum to the associated fibred category. -/
structure FieldValuedPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)) where
  /-- The field of definition. -/
  carrier : Type u
  /-- Its field structure. -/
  [field : Field carrier]
  /-- The object of the big site determined by the field spectrum and its map to the base. -/
  base : BigFppfOver B S hS
  /-- Identification of the underlying scheme with the field spectrum. -/
  isSpec : (BigFppfOver.toScheme B S hS).obj base ≅ Spec (.of carrier)
  /-- The object of the fibred category over this field spectrum. -/
  obj : 𝒳.obj
  /-- The object's base is the specified field spectrum. -/
  over : 𝒳.p.obj obj = base

attribute [instance] FieldValuedPoint.field

namespace FieldValuedPoint

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}

/-- The structure morphism of a field-valued point, as a morphism of schemes out of the
field spectrum. -/
private noncomputable def toBaseScheme (p : FieldValuedPoint B S hS 𝒳) :
    Spec (.of p.carrier) ⟶ S :=
  p.isSpec.inv ≫ B.inclusion.map p.base.hom

/-- The field spectrum of a field-valued point lies in the chosen big fppf site. -/
private theorem spectrumContained (p : FieldValuedPoint B S hS 𝒳) :
    B.Contains (Spec (.of p.carrier)) := by
  have hb : ((BigFppfOver.toScheme B S hS).obj p.base).size < B.cutoff := p.base.left.2
  rwa [Scheme.size_congr p.isSpec] at hb

/-- The field spectrum of a field-valued point as an object of the site over `S`. -/
private noncomputable def canonicalSiteObject (p : FieldValuedPoint B S hS 𝒳) :
    BigFppfOver B S hS :=
  Over.mk (⟨toBaseScheme p⟩ : B.obj (spectrumContained p) ⟶ B.obj hS)

/-- A field-valued point of the stack together with a section of a presheaf over its field
spectrum is a field-valued point of that presheaf, in the sense of Stacks 03BU. -/
private noncomputable def asSitePoint {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS 𝒳)
    (value : F.obj (Opposite.op (canonicalSiteObject p))) :
    Space.FieldValuedPoint B S hS F where
  carrier := p.carrier
  field := p.field
  contained := spectrumContained p
  toBase := toBaseScheme p
  value := value

/-- The canonical field-spectrum object of the site is isomorphic, over `S`, to the recorded
base of the field-valued point. -/
private noncomputable def siteObjectIso (p : FieldValuedPoint B S hS 𝒳) :
    canonicalSiteObject p ≅ p.base :=
  Over.isoMk (B.inclusion.preimageIso p.isSpec.symm) (B.inclusion.map_injective (by
    rw [B.inclusion.map_comp]
    exact congrArg (· ≫ _) (B.inclusion.map_preimage _)))

/-- An arrow between the objects of two field-valued points, read on their recorded bases. -/
private def pointBaseMap {p q : FieldValuedPoint B S hS 𝒳} (f : p.obj ⟶ q.obj) :
    p.base ⟶ q.base :=
  eqToHom p.over.symm ≫ 𝒳.p.map f ≫ eqToHom q.over

/-- An arrow between the objects of two field-valued points, read on their canonical field
spectra in the site. -/
private noncomputable def siteMap {p q : FieldValuedPoint B S hS 𝒳} (f : p.obj ⟶ q.obj) :
    canonicalSiteObject p ⟶ canonicalSiteObject q :=
  (siteObjectIso p).hom ≫ pointBaseMap f ≫ (siteObjectIso q).inv

/-- **The field spectrum of a field-valued point is the field spectrum of a field-valued point
of the site, and it maps to the recorded base.** There are a witness that the spectrum lies in
the chosen big fppf site and a structure morphism from it to `S` — the two data an
`AlgebraicGeometry.Space.FieldValuedPoint` records besides its section — such that the object of
the site over `S` they determine admits a morphism over `S` to the recorded base of the point.

The witness is `AlgebraicGeometry.Stack.FieldValuedPoint.spectrumContained`, the structure
morphism is `AlgebraicGeometry.Stack.FieldValuedPoint.toBaseScheme`, and the morphism is the
isomorphism `AlgebraicGeometry.Stack.FieldValuedPoint.siteObjectIso`. All three are internal to
this module, and this is the statement about them that its consumers use: it is what lets a
field-valued point of a based category be transported to a field-valued point of a presheaf on
the site over the same field, placed over the recorded base. -/
theorem exists_contains_toBase_hom_base (p : FieldValuedPoint B S hS 𝒳) :
    ∃ (h : B.Contains (Spec (.of p.carrier))) (m : Spec (.of p.carrier) ⟶ S),
      Nonempty ((Over.mk (⟨m⟩ : B.obj h ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ p.base) :=
  ⟨spectrumContained p, toBaseScheme p, ⟨(siteObjectIso p).hom⟩⟩

/-- Two field-valued points have a common field-valued refinement. The arrows encode the two
2-commutative triangles of the Stacks definition. -/
def HasCommonExtension
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    (p q : FieldValuedPoint B S hS 𝒳) : Prop :=
  ∃ r : FieldValuedPoint B S hS 𝒳,
    Nonempty (r.obj ⟶ p.obj) ∧ Nonempty (r.obj ⟶ q.obj)

/-- A field-valued point `a` of the stack with an arrow of field spectra to that of `q` and the
tautological point of `q` have a common refinement as points of the representable presheaf. -/
private theorem asSitePoint_hasCommonExtension {a q : FieldValuedPoint B S hS 𝒳}
    (f : canonicalSiteObject a ⟶ canonicalSiteObject q) :
    Space.FieldValuedPoint.HasCommonExtension B S hS (yoneda.obj (canonicalSiteObject q))
      (asSitePoint a f) (asSitePoint q (𝟙 _)) := by
  refine ⟨asSitePoint a f, ⟨𝟙 _, ?_⟩, ⟨f, ?_⟩⟩
  · simp [Space.FieldValuedPoint.siteObject]
  · change f ≫ 𝟙 (canonicalSiteObject q) = f
    exact Category.comp_id _

/-- In a category fibred in groupoids, two arrows `a ⟶ q` and `b ⟶ q` of field-valued points
whose base maps agree after maps from a field spectrum `Z` to the bases of `a` and `b` lift to
a common refinement of `a` and `b`. -/
private theorem hasCommonExtension_of_pointBaseMap_eq (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    {a b q : FieldValuedPoint B S hS 𝒳} (faq : a.obj ⟶ q.obj) (fbq : b.obj ⟶ q.obj)
    {K : Type u} [Field K] (Z : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj Z ≅ Spec (.of K))
    (eza : Z ⟶ a.base) (ezb : Z ⟶ b.base)
    (hbasePath : eza ≫ pointBaseMap faq = ezb ≫ pointBaseMap fbq) :
    HasCommonExtension a b := by
  let fzq : Z ⟶ q.base := eza ≫ pointBaseMap faq
  obtain ⟨w, φ, hφ⟩ := h𝒳.exists_lift fzq q.obj q.over
  have hdom : 𝒳.p.obj w = Z := IsHomLift.domain_eq 𝒳.p fzq φ
  have hφfac : 𝒳.p.map φ = eqToHom hdom ≫ fzq ≫ eqToHom q.over.symm :=
    IsHomLift.fac' 𝒳.p fzq φ
  let gA : 𝒳.p.obj w ⟶ 𝒳.p.obj a.obj := eqToHom hdom ≫ eza ≫ eqToHom a.over.symm
  let gB : 𝒳.p.obj w ⟶ 𝒳.p.obj b.obj := eqToHom hdom ≫ ezb ≫ eqToHom b.over.symm
  have hbaseA : gA ≫ 𝒳.p.map faq = 𝒳.p.map φ := by
    dsimp [gA, pointBaseMap] at *
    calc
      _ = eqToHom hdom ≫ eza ≫
          (eqToHom a.over.symm ≫ 𝒳.p.map faq ≫ eqToHom q.over) ≫
            eqToHom q.over.symm := by simp [Category.assoc]
      _ = eqToHom hdom ≫ fzq ≫ eqToHom q.over.symm := by
        simp [fzq, pointBaseMap, Category.assoc]
      _ = 𝒳.p.map φ := hφfac.symm
  have hpaths : gA ≫ 𝒳.p.map faq = gB ≫ 𝒳.p.map fbq := by
    have hpaths := congrArg
      (fun k : Z ⟶ q.base ↦ eqToHom hdom ≫ k ≫ eqToHom q.over.symm) hbasePath
    simpa [gA, gB, pointBaseMap, Category.assoc] using hpaths
  obtain ⟨ψa, ⟨_, hψa⟩, _⟩ := h𝒳.unique_lift faq φ gA hbaseA
  obtain ⟨ψb, ⟨_, hψb⟩, _⟩ := h𝒳.unique_lift fbq φ gB (hpaths.symm.trans hbaseA)
  exact ⟨{ carrier := K, base := Z, isSpec := e, obj := w, over := hdom }, ⟨ψa⟩, ⟨ψb⟩⟩

/-- Common field-valued refinement is transitive on the field-valued points of a category
fibred in groupoids. -/
theorem hasCommonExtension_trans (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    {p q r : FieldValuedPoint B S hS 𝒳} (hpq : HasCommonExtension p q)
    (hqr : HasCommonExtension q r) : HasCommonExtension p r := by
  obtain ⟨a, ⟨fap⟩, ⟨faq⟩⟩ := hpq
  obtain ⟨b, ⟨fbq⟩, ⟨fbr⟩⟩ := hqr
  obtain ⟨z, ⟨gza, hgza⟩, ⟨gzb, hgb⟩⟩ := Space.FieldValuedPoint.hasCommonExtension_trans B S hS _
    (asSitePoint_hasCommonExtension (siteMap faq))
    (Space.FieldValuedPoint.hasCommonExtension_symm B S hS _
      (asSitePoint_hasCommonExtension (siteMap fbq)))
  have hza : gza ≫ siteMap faq = gzb ≫ siteMap fbq := by
    change (yoneda.obj (canonicalSiteObject q)).map gza.op (siteMap faq) = z.value at hgza
    change (yoneda.obj (canonicalSiteObject q)).map gzb.op (siteMap fbq) = z.value at hgb
    simpa using hgza.trans hgb.symm
  have hbasePath : (gza ≫ (siteObjectIso a).hom) ≫ pointBaseMap faq =
      (gzb ≫ (siteObjectIso b).hom) ≫ pointBaseMap fbq := by
    refine (cancel_mono (siteObjectIso q).inv).1 ?_
    change gza ≫ (siteObjectIso a).hom ≫ pointBaseMap faq ≫ (siteObjectIso q).inv =
      gzb ≫ (siteObjectIso b).hom ≫ pointBaseMap fbq ≫ (siteObjectIso q).inv
    exact hza
  obtain ⟨w, ⟨ψa⟩, ⟨ψb⟩⟩ := hasCommonExtension_of_pointBaseMap_eq h𝒳 faq fbq (K := z.carrier)
    z.siteObject (Iso.refl _) _ _ hbasePath
  exact ⟨w, ⟨ψa ≫ fap⟩, ⟨ψb ≫ fbr⟩⟩

/-- **Stacks 04XF.** Common field-valued refinement is an equivalence relation on the
field-valued points of a category fibred in groupoids. -/
@[stacks 04XF]
theorem hasCommonExtension_equivalence
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) :
    Equivalence (HasCommonExtension (𝒳 := 𝒳)) :=
  ⟨fun p ↦ ⟨p, ⟨𝟙 p.obj⟩, ⟨𝟙 p.obj⟩⟩, fun ⟨r, hrp, hrq⟩ ↦ ⟨r, hrq, hrp⟩,
    hasCommonExtension_trans h𝒳⟩

/-- The setoid of field-valued points of a category fibred in groupoids. -/
def setoid
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) : Setoid (FieldValuedPoint B S hS 𝒳) :=
  ⟨HasCommonExtension, hasCommonExtension_equivalence h𝒳⟩

end FieldValuedPoint

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))

/-- **Stacks 04XG.** The points of a category fibred in groupoids, in particular of an
algebraic stack, are the equivalence classes of its field-valued points. -/
@[stacks 04XG]
abbrev points (h𝒳 : 𝒳.p.IsFiberedInGroupoids) : Type (max (u + 1) t) :=
  Quotient (FieldValuedPoint.setoid h𝒳)

/-- The point represented by a field-valued point. -/
abbrev pointClass (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (p : FieldValuedPoint B S hS 𝒳) :
    points B S hS 𝒳 h𝒳 :=
  Quotient.mk _ p

/-- Two field-valued points represent the same point exactly when they admit a common
field-valued refinement. -/
theorem class_eq_class_iff_hasCommonExtension (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    (p q : FieldValuedPoint B S hS 𝒳) :
    pointClass B S hS 𝒳 h𝒳 p = pointClass B S hS 𝒳 h𝒳 q ↔
      FieldValuedPoint.HasCommonExtension p q :=
  Quotient.eq

/-- Apply a 1-morphism over the base site to a field-valued point. -/
def fieldValuedPointMap {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)} (F : 𝒳 ⥤ᵇ 𝒴)
    (p : FieldValuedPoint B S hS 𝒳) : FieldValuedPoint B S hS 𝒴 where
  carrier := p.carrier
  field := p.field
  base := p.base
  isSpec := p.isSpec
  obj := F.obj p.obj
  over := (F.w_obj p.obj).trans p.over

/-- A 1-morphism over the site preserves common field-valued refinements. -/
theorem hasCommonExtension_fieldValuedPointMap
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)} (F : 𝒳 ⥤ᵇ 𝒴)
    {p q : FieldValuedPoint B S hS 𝒳} (h : FieldValuedPoint.HasCommonExtension p q) :
    FieldValuedPoint.HasCommonExtension
      (fieldValuedPointMap B S hS 𝒳 F p) (fieldValuedPointMap B S hS 𝒳 F q) := by
  obtain ⟨r, ⟨f⟩, ⟨g⟩⟩ := h
  exact ⟨fieldValuedPointMap B S hS 𝒳 F r, ⟨F.map f⟩, ⟨F.map g⟩⟩

/-- The map on points induced by a 1-morphism over the base site. -/
def pointsMap (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)} (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ᵇ 𝒴) : points B S hS 𝒳 h𝒳 → points B S hS 𝒴 h𝒴 :=
  Quotient.map (fieldValuedPointMap B S hS 𝒳 F)
    (fun _ _ h ↦ hasCommonExtension_fieldValuedPointMap B S hS 𝒳 F h)

/-- The map on points induced by `F` sends the class of a field-valued point `p` to the class of
its image `fieldValuedPointMap B S hS 𝒳 F p`. -/
@[simp]
theorem pointsMap_class (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)} (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ᵇ 𝒴) (p : FieldValuedPoint B S hS 𝒳) :
    pointsMap B S hS 𝒳 h𝒳 h𝒴 F (pointClass B S hS 𝒳 h𝒳 p) =
      pointClass B S hS 𝒴 h𝒴 (fieldValuedPointMap B S hS 𝒳 F p) := rfl

/-- A 2-morphism of 1-morphisms over the site does not change the point represented by the
image of a field-valued point: the two images have a common refinement, namely either one of
them, with the 2-morphism as one of the two arrows. -/
theorem pointClass_fieldValuedPointMap_eq_of_basedNatTrans
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)} (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    {F G : 𝒳 ⥤ᵇ 𝒴} (η : BasedNatTrans F G) (p : FieldValuedPoint B S hS 𝒳) :
    pointClass B S hS 𝒴 h𝒴 (fieldValuedPointMap B S hS 𝒳 F p) =
      pointClass B S hS 𝒴 h𝒴 (fieldValuedPointMap B S hS 𝒳 G p) :=
  (class_eq_class_iff_hasCommonExtension B S hS 𝒴 h𝒴 _ _).2
    ⟨fieldValuedPointMap B S hS 𝒳 F p, ⟨𝟙 _⟩, ⟨η.toNatTrans.app p.obj⟩⟩

/-- 2-isomorphic 1-morphisms induce the same map on points; in particular a 2-commutative
square of 1-morphisms induces a commutative square of maps on points. -/
theorem pointsMap_eq_of_basedNatTrans (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)} (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    {F G : 𝒳 ⥤ᵇ 𝒴} (η : BasedNatTrans F G) :
    pointsMap B S hS 𝒳 h𝒳 h𝒴 F = pointsMap B S hS 𝒳 h𝒳 h𝒴 G := by
  funext z
  induction z using Quotient.inductionOn with
  | h p => exact pointClass_fieldValuedPointMap_eq_of_basedNatTrans B S hS 𝒳 h𝒴 η p

/-- The map on points of a composite of 1-morphisms is the composite of the maps on points. -/
theorem pointsMap_comp (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)} (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    {𝒵 : BasedCategory.{v'', t''} (BigFppfOver B S hS)} (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵) (z : points B S hS 𝒳 h𝒳) :
    pointsMap B S hS 𝒴 h𝒴 h𝒵 G (pointsMap B S hS 𝒳 h𝒳 h𝒴 F z) =
      pointsMap B S hS 𝒳 h𝒳 h𝒵 (F.comp G) z := by
  induction z using Quotient.inductionOn with
  | h p => rfl

end AlgebraicGeometry.Stack

end
