module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionExistencePoints

/-!
# The existence part of the valuative criterion for categories fibred in groupoids

Definition 0CLK of the Stacks project is stated for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks,
and `AlgebraicGeometry.Stack.ValuativeCriterion.Existence` formalises it in that generality. The
data of the definition — a valuation ring `R` with fraction field `K`, a 2-commutative square with
left edge `Spec K ⟶ Spec R`, an extension `K'/K` with a valuation ring `R' ⊂ K'` dominating `R`,
and a dotted arrow for the extended square — make sense for an arbitrary 1-morphism of categories
fibred in groupoids over the big fppf site of `S`, with no algebraicity anywhere.

This file states the criterion in that generality. By the 2-Yoneda lemma (Stacks 004B) a
1-morphism out of the category fibred in groupoids represented by `Spec K` is an object of the
fibre over `Spec K`, a 2-morphism between two such is a morphism of that fibre, and a dotted
arrow is determined by its value at the unit object. So the square is presented by an object `x`
of `𝒳` over `Spec K`, an object `y` of `𝒴` over `Spec R` and a morphism `f(x) ⟶ y` of `𝒴` lying
over `Spec K ⟶ Spec R`; and a dotted arrow for the extended square is a span
`x ⟵ z ⟶ a` in `𝒳` over `Spec K ⟵ Spec K' ⟶ Spec R'` together with a morphism `f(a) ⟶ y` over
`Spec R' ⟶ Spec R` making the two composites `f(z) ⟶ y` agree. Phrased this way the criterion
does not mention the universes of the two total categories at all, which is what lets it apply to
categories fibred in groupoids whose morphisms live in a larger universe than those of the site,
such as the stack of coherent sheaves `Coh_{X/B}` of Stacks 08KB.

The two formulations agree: for a 1-morphism of algebraic stacks, the criterion stated here holds
for its underlying 1-morphism of categories fibred in groupoids exactly when
`AlgebraicGeometry.Stack.ValuativeCriterion.Existence` holds. So the predicate of this file is a
generalisation of the one of Stacks 0CLK, not a second version of it.

## Main definitions

* `AlgebraicGeometry.Stack.FiberedValuativeSquare`: the solid part of a valuative square for a
  1-morphism of categories fibred in groupoids, presented at the unit objects.
* `AlgebraicGeometry.Stack.FiberedValuativeSquare.Extension`: an extension `K'/K` with a
  dominating valuation ring, and the morphisms of spectra it induces.
* `AlgebraicGeometry.Stack.FiberedValuativeSquare.Lift`: a dotted arrow for the extended square,
  presented at the unit objects.
* `AlgebraicGeometry.Stack.FiberedValuativeExistence`: the existence part of the valuative
  criterion for a 1-morphism of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.FiberedValuativeSquare.trivialExtension`: the extension along the
  identities of the valuation ring and of its fraction field.

## Main results

* `AlgebraicGeometry.Stack.valuativeCriterionExistence_iff_fiberedValuativeExistence`: for a
  1-morphism of algebraic stacks the two criteria are equivalent.
* `AlgebraicGeometry.Stack.FiberedValuativeSquare.exists_lift_of_diagonal`: a diagonal over the
  valuation ring itself, compatible with the square, is a dotted arrow after the trivial
  extension.

## Implementation notes

The morphisms of spectra are carried as morphisms of the site together with the equation
identifying their underlying morphism of schemes, exactly as in
`AlgebraicGeometry.Stack.ValuativeSquare`, so that a square or an extension of either kind is
turned into one of the other kind field by field. The translation of the 2-categorical data is
`AlgebraicGeometry.Stack.exists_span_of_dottedArrow` and
`AlgebraicGeometry.Stack.nonempty_dottedArrow_of_span` in one direction of the comparison, and
the 2-Yoneda extension `CategoryTheory.Functor.TwoYoneda.homOverBase` of a morphism at the unit
object in the other.

## References

* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.Bicategory.InducedBicategory

namespace AlgebraicGeometry.Stack

universe u v w w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The solid part of a valuative square for a 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in
groupoids over the big fppf site of `S`, presented at the unit objects: a valuation ring `R` with
fraction field `K`, both of whose spectra lie in the site, a structure morphism `Spec R ⟶ S`, the
canonical map `Spec K ⟶ Spec R` as a morphism of the site, an object `x` of `𝒳` (the generic
point), an object `y` of `𝒴` (the special point), and a morphism `f(x) ⟶ y` of `𝒴` lying over the
canonical map (the 2-morphism filling the square). -/
structure FiberedValuativeSquare
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) where
  /-- The valuation ring. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  /-- The fraction field of the valuation ring. -/
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  /-- The spectrum of the valuation ring lies in the big fppf site. -/
  ring_mem : B.Contains (Spec (.of R))
  /-- The spectrum of the fraction field lies in the big fppf site. -/
  field_mem : B.Contains (Spec (.of K))
  /-- The structure morphism of the spectrum of the valuation ring. -/
  base : Spec (.of R) ⟶ S
  /-- The canonical map from the generic point to the spectrum of the valuation ring. -/
  genericMap : siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
    siteObject B S hS ring_mem base
  /-- The canonical map is the one induced by the inclusion of the valuation ring in its fraction
  field. -/
  genericMap_left : (B.inclusion).map genericMap.left =
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  /-- The generic point of `𝒳`, an object over the spectrum of the fraction field. -/
  x : 𝒳.val.obj
  /-- The special point of `𝒴`, an object over the spectrum of the valuation ring. -/
  y : 𝒴.val.obj
  /-- The morphism filling the square. -/
  link : f.hom.obj x ⟶ y
  /-- The morphism filling the square lies over the canonical map. -/
  link_lift : 𝒴.val.p.IsHomLift genericMap link

namespace FiberedValuativeSquare

attribute [instance] commRing domain valuationRing field algebra isFractionRing

variable {B S hS} {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
  {f : 𝒳 ⟶ 𝒴}

/-- An extension `K'/K` of fields together with a valuation ring `R' ⊂ K'` dominating `R`, and the
three morphisms of spectra it induces, as morphisms of the site. -/
structure Extension (q : FiberedValuativeSquare B S hS f) where
  /-- The dominating valuation ring. -/
  R' : Type u
  [commRing : CommRing R']
  [domain : IsDomain R']
  [valuationRing : ValuationRing R']
  /-- The extension of the fraction field. -/
  K' : Type u
  [field : Field K']
  [algebra : Algebra R' K']
  [isFractionRing : IsFractionRing R' K']
  /-- The map of valuation rings. -/
  ringMap : q.R →+* R'
  /-- The map of fraction fields. -/
  fieldMap : q.K →+* K'
  /-- The map of valuation rings is local: this is the domination condition. -/
  isLocalHom : IsLocalHom ringMap
  /-- The two maps are compatible with the inclusions of the valuation rings in their fraction
  fields. -/
  fraction_comm :
    (algebraMap R' K').comp ringMap = fieldMap.comp (algebraMap q.R q.K)
  /-- The spectrum of the dominating valuation ring lies in the big fppf site. -/
  ring_mem : B.Contains (Spec (.of R'))
  /-- The spectrum of the extended fraction field lies in the big fppf site. -/
  field_mem : B.Contains (Spec (.of K'))
  /-- The map of spectra of valuation rings. -/
  specialOver : siteObject B S hS ring_mem
      (Spec.map (CommRingCat.ofHom ringMap) ≫ q.base) ⟶
    siteObject B S hS q.ring_mem q.base
  /-- `specialOver` is the map induced by `ringMap`. -/
  specialOver_left : (B.inclusion).map specialOver.left =
    Spec.map (CommRingCat.ofHom ringMap)
  /-- The map of spectra of fraction fields. -/
  genericOver : siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom ringMap) ≫ q.base) ⟶
    siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  /-- `genericOver` is the map induced by `fieldMap`. -/
  genericOver_left : (B.inclusion).map genericOver.left =
    Spec.map (CommRingCat.ofHom fieldMap)
  /-- The canonical map of the extended square. -/
  genericMap : siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom ringMap) ≫ q.base) ⟶
    siteObject B S hS ring_mem
      (Spec.map (CommRingCat.ofHom ringMap) ≫ q.base)
  /-- The canonical map of the extended square is the one induced by the inclusion of the
  dominating valuation ring in its fraction field. -/
  genericMap_left : (B.inclusion).map genericMap.left =
    Spec.map (CommRingCat.ofHom (algebraMap R' K'))

attribute [instance] Extension.commRing Extension.domain Extension.valuationRing Extension.field
  Extension.algebra Extension.isFractionRing

/-- A dotted arrow for the square extended along `e`, presented at the unit objects: an object
`a` of `𝒳` over `Spec R'` (the value of the diagonal), a span `x ⟵ z ⟶ a` in `𝒳` over
`Spec K ⟵ Spec K' ⟶ Spec R'` (the upper triangle) and a morphism `f(a) ⟶ y` of `𝒴` over
`Spec R' ⟶ Spec R` (the lower triangle), such that the two composites `f(z) ⟶ y` agree (the
pasting condition). -/
structure Lift {q : FiberedValuativeSquare B S hS f} (e : q.Extension) where
  /-- The restriction of the generic point to the spectrum of the extended fraction field. -/
  z : 𝒳.val.obj
  /-- The value of the diagonal at the spectrum of the dominating valuation ring. -/
  a : 𝒳.val.obj
  /-- The restriction morphism of the generic point. -/
  n : z ⟶ q.x
  /-- The upper triangle. -/
  m : z ⟶ a
  /-- The lower triangle. -/
  b : f.hom.obj a ⟶ q.y
  n_lift : 𝒳.val.p.IsHomLift e.genericOver n
  m_lift : 𝒳.val.p.IsHomLift e.genericMap m
  b_lift : 𝒴.val.p.IsHomLift e.specialOver b
  /-- The pasting condition. -/
  comm : f.hom.map n ≫ q.link = f.hom.map m ≫ b

end FiberedValuativeSquare

/-- **The existence part of the valuative criterion (Stacks 0CLK) for a 1-morphism of categories
fibred in groupoids.** Every valuative square admits a dotted arrow after an extension of the
fraction field and passage to a dominating valuation ring. -/
def FiberedValuativeExistence
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ q : FiberedValuativeSquare B S hS f, ∃ e : q.Extension, Nonempty (FiberedValuativeSquare.Lift e)

namespace FiberedValuativeSquare

variable {B S hS} {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
  {f : 𝒳 ⟶ 𝒴}

/-- The trivial extension of a valuative square, along the identities of the valuation ring and
of its fraction field. -/
noncomputable def trivialExtension (q : FiberedValuativeSquare B S hS f) : q.Extension where
  R' := q.R
  K' := q.K
  ringMap := RingHom.id q.R
  fieldMap := RingHom.id q.K
  isLocalHom := isLocalHom_id q.R
  fraction_comm := by rw [RingHom.comp_id, RingHom.id_comp]
  ring_mem := q.ring_mem
  field_mem := q.field_mem
  specialOver := Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (RingHom.id q.R))))
  specialOver_left := rfl
  genericOver := Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (RingHom.id q.K))))
    (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (RingHom.id q.K)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) =
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫
          Spec.map (CommRingCat.ofHom (RingHom.id q.R)) ≫ q.base
      simp only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp])
  genericOver_left := rfl
  genericMap :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))))
  genericMap_left := rfl

/-- A 1-morphism of categories fibred in groupoids sends a lift of `g` to a lift of `g`. -/
private theorem map_isHomLift (f : 𝒳 ⟶ 𝒴) {R T : BigFppfOver B S hS} {g : R ⟶ T} {a a' : 𝒳.val.obj}
    {φ : a ⟶ a'} (h : 𝒳.val.p.IsHomLift g φ) : 𝒴.val.p.IsHomLift g (f.hom.map φ) :=
  have : (BasedCategory.ofFunctor 𝒳.val.p).p.IsHomLift g φ := h
  f.hom.preserves_isHomLift _ _

/-- The composite of a lift of `g` with a lift of an identity is a lift of `g`. -/
private theorem comp_isHomLift_id {C : Type*} [Category C] {D : Type*} [Category D] {p : C ⥤ D}
    {R T U : D} {g : R ⟶ T} {a b c : C} {φ : a ⟶ b} {ψ : b ⟶ c} (hφ : p.IsHomLift g φ)
    (hψ : p.IsHomLift (𝟙 U) ψ) : p.IsHomLift g (φ ≫ ψ) :=
  IsHomLift.comp_lift_id_right' p g φ U ψ

/-- **A dotted arrow over the valuation ring itself.** If the generic point maps to an object `a`
of `𝒳` over the spectrum of the valuation ring by a morphism `m` over the canonical map, and `f(a)`
maps to the special point by a morphism `b` over the identity, compatibly with the link, then the
square has a dotted arrow, already after the trivial extension.

The objects over the spectra of the trivial extension are the restrictions of `x` and `a` along its
morphisms of spectra, which exist because `𝒳` is fibred in groupoids; the upper triangle is the
fill-in of `m` against the strongly cartesian restriction morphism of `a`. -/
theorem exists_lift_of_diagonal (q : FiberedValuativeSquare B S hS f) (a : 𝒳.val.obj)
    (m : q.x ⟶ a) (hm : 𝒳.val.p.IsHomLift q.genericMap m)
    (b : f.hom.obj a ⟶ q.y) (hb : 𝒴.val.p.IsHomLift (𝟙 (siteObject B S hS q.ring_mem q.base)) b)
    (h : f.hom.map m ≫ b = q.link) :
    ∃ e : q.Extension, Nonempty (Lift e) := by
  let e := q.trivialExtension
  have hp := 𝒳.isFiberedInGroupoids
  have hX : 𝒳.val.p.obj q.x = siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) :=
    IsHomLift.domain_eq 𝒳.val.p q.genericMap m
  have hA : 𝒳.val.p.obj a = siteObject B S hS q.ring_mem q.base :=
    IsHomLift.codomain_eq 𝒳.val.p q.genericMap m
  obtain ⟨z, n, hn⟩ := hp.exists_lift e.genericOver q.x hX
  obtain ⟨a', s, hs⟩ := hp.exists_lift e.specialOver a hA
  have hcart := hp.isStronglyCartesian_homLift e.specialOver s
  have hnm : 𝒳.val.p.IsHomLift (e.genericOver ≫ q.genericMap) (n ≫ m) := inferInstance
  have hsq : e.genericOver ≫ q.genericMap = e.genericMap ≫ e.specialOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    simp only [Over.comp_left, Functor.map_comp, q.genericMap_left]
    show Spec.map (CommRingCat.ofHom (RingHom.id q.K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) =
      Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫
        Spec.map (CommRingCat.ofHom (RingHom.id q.R))
    simp only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
  let m' := Functor.IsStronglyCartesian.map 𝒳.val.p e.specialOver s hsq (n ≫ m)
  have hm' : 𝒳.val.p.IsHomLift e.genericMap m' := inferInstance
  have hfac : m' ≫ s = n ≫ m := Functor.IsStronglyCartesian.fac _ _ _ _ _
  let bb : f.hom.obj a' ⟶ q.y := f.hom.map s ≫ b
  refine ⟨e, ⟨⟨z, a', n, m', bb, hn, hm', ?_, ?_⟩⟩⟩
  · exact comp_isHomLift_id (map_isHomLift f hs) hb
  · rw [← h, ← Functor.map_comp_assoc, ← hfac, Functor.map_comp_assoc]

end FiberedValuativeSquare

/-! ### Comparison with the criterion for algebraic stacks -/

section Comparison

variable {B S hS} {𝒳 𝒴 : AlgebraicStacks.{u, w'} B S hS}

/-- The valuative square at the unit objects underlying a valuative square for a 1-morphism of
algebraic stacks: the values of the two points at the unit objects, joined by the link of the
square. -/
noncomputable def ValuativeSquare.toFibered {f : 𝒳 ⟶ 𝒴} (q : ValuativeSquare B S hS f) :
    FiberedValuativeSquare B S hS f.hom where
  R := q.R
  K := q.K
  ring_mem := q.ring_mem
  field_mem := q.field_mem
  base := q.base
  genericMap := q.genericMap
  genericMap_left := q.genericMap_left
  x := q.x.hom.obj (Over.mk (𝟙 _))
  y := q.y.hom.obj (Over.mk (𝟙 _))
  link := pointLink B q
  link_lift := pointLink_lift B q

/-- **A dotted arrow at the unit objects is a dotted arrow.** If the valuative square at the unit
objects underlying a valuative square `q` for a 1-morphism of algebraic stacks admits a dotted
arrow after an extension, so does `q`, after the dominating extension induced by the same maps of
rings. -/
theorem ValuativeSquare.exists_of_toFibered {f : 𝒳 ⟶ 𝒴} (q : ValuativeSquare B S hS f)
    (e : q.toFibered.Extension) (l : FiberedValuativeSquare.Lift e) :
    ∃ e' : q.DominatingExtension,
      Nonempty (DottedArrow (e'.k ≫ q.x) e'.j f.hom (e'.a ≫ q.y) e'.inducedGamma) := by
  let e' := dominatingExtensionOfRingMaps B q e.R' e.K' e.ringMap e.fieldMap e.isLocalHom
    e.fraction_comm e.ring_mem e.field_mem
  have hgo : e'.genericOver = e.genericOver :=
    Over.OverMorphism.ext (B.inclusion.map_injective e.genericOver_left.symm)
  have hgm : e'.genericMap = e.genericMap :=
    Over.OverMorphism.ext (B.inclusion.map_injective e.genericMap_left.symm)
  have hso : e'.specialOver = e.specialOver :=
    Over.OverMorphism.ext (B.inclusion.map_injective e.specialOver_left.symm)
  refine ⟨e', nonempty_dottedArrow_of_span B q e' l.n ?_ l.m ?_ l.b ?_ l.comm⟩
  · rw [hgo]; exact l.n_lift
  · rw [hgm]; exact l.m_lift
  · rw [hso]; exact l.b_lift

/-- **A valuative square at the unit objects is the one underlying a valuative square.** Every
valuative square at the unit objects for a 1-morphism of algebraic stacks arises, up to the
replacement of its two points by isomorphic ones, from a valuative square in the sense of
Stacks 0CLK; and a dotted arrow for any dominating extension of the latter gives one at the unit
objects for the former.

The two points are extended to 1-morphisms out of the represented categories by the 2-Yoneda
lemma, and the filling 2-morphism is the 2-Yoneda extension of the link. -/
theorem FiberedValuativeSquare.exists_of_valuativeSquare {f : 𝒳 ⟶ 𝒴}
    (q : FiberedValuativeSquare B S hS f.hom)
    (H : ∀ Q : ValuativeSquare B S hS f, ∃ e : Q.DominatingExtension,
      Nonempty (DottedArrow (e.k ≫ Q.x) e.j f.hom (e.a ≫ Q.y) e.inducedGamma)) :
    ∃ e : q.Extension, Nonempty (FiberedValuativeSquare.Lift e) := by
  classical
  let KS := siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  let RS := siteObject B S hS q.ring_mem q.base
  have hl := q.link_lift
  have hX : 𝒳.val.val.p.obj q.x = KS :=
    (Functor.congr_obj f.hom.hom.w q.x).symm.trans
      (IsHomLift.domain_eq 𝒴.val.val.p q.genericMap q.link)
  have hY : 𝒴.val.val.p.obj q.y = RS := IsHomLift.codomain_eq 𝒴.val.val.p q.genericMap q.link
  obtain ⟨G, cG, hcG⟩ := Functor.TwoYoneda.exists_basedFunctor_unitHom 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids q.x hX
  obtain ⟨L, cL, hcL⟩ := Functor.TwoYoneda.exists_basedFunctor_unitHom 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids q.y hY
  have hcLiso : IsIso cL :=
    Functor.isIso_of_fiber_isGroupoid
      (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid RS) cL hcL
  have hfcG : 𝒴.val.val.p.IsHomLift (𝟙 KS) (f.hom.hom.map cG) := map_isHomLift f.hom hcG
  have hcLinv : 𝒴.val.val.p.IsHomLift (𝟙 RS) (inv cL) :=
    have := hcL
    have := hcLiso
    IsHomLift.lift_id_inv_isIso 𝒴.val.val.p RS cL
  let c := f.hom.hom.map cG ≫ q.link ≫ inv cL
  have hc₀ : 𝒴.val.val.p.IsHomLift q.genericMap (f.hom.hom.map cG ≫ q.link) :=
    @IsHomLift.comp_lift_id_left _ _ _ _ 𝒴.val.val.p _ _ _ _ _
      q.genericMap q.link hl (f.hom.hom.map cG) hfcG
  have hc₁ : 𝒴.val.val.p.IsHomLift q.genericMap c := by
    have hc₂ := comp_isHomLift_id hc₀ hcLinv
    simpa only [c, Category.assoc] using hc₂
  let δ := Functor.TwoYoneda.homOverBase 𝒴.val.val.p q.genericMap 𝒴.val.isFiberedInGroupoids
    (G := BasedFunctor.comp G f.hom.hom) (H := L) c hc₁
  have hδiso : IsIso δ :=
    Functor.TwoYoneda.isIso_hom 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids δ
  let γQ := @inv _ _ _ _ δ hδiso
  let Q : ValuativeSquare B S hS f :=
    { R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem
      base := q.base
      genericMap := q.genericMap
      genericMap_left := q.genericMap_left
      j := schemeMorphism B q.genericMap
      j_canonical := rfl
      x := Bicategory.InducedBicategory.mkHom G
      y := Bicategory.InducedBicategory.mkHom L
      γ := ⟨γQ⟩ }
  have hcQ : pointLink B Q = c := by
    have hδfac := Functor.TwoYoneda.homOverBase_fac 𝒴.val.val.p q.genericMap
      𝒴.val.isFiberedInGroupoids (G := BasedFunctor.comp G f.hom.hom) (H := L) c hc₁
    have hisoγ : IsIso (γQ.app (Over.mk (𝟙 KS))) :=
      Functor.isIso_of_fiber_isGroupoid
        (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid KS) _
        (γQ.isHomLift' (Over.mk (𝟙 KS)))
    have := hisoγ
    have hcomp : γQ.app (Over.mk (𝟙 KS)) ≫ δ.app (Over.mk (𝟙 KS)) = 𝟙 _ :=
      congrArg (fun η => η.app (Over.mk (𝟙 KS))) (@IsIso.inv_hom_id _ _ _ _ δ hδiso)
    have hinv : inv (γQ.app (Over.mk (𝟙 KS))) = δ.app (Over.mk (𝟙 KS)) :=
      IsIso.inv_eq_of_hom_inv_id hcomp
    show inv (γQ.app (Over.mk (𝟙 KS))) ≫ _ = c
    rw [hinv]
    exact hδfac
  obtain ⟨d, ⟨l⟩⟩ := H Q
  obtain ⟨ZK, ZR, n, m, b, hn, hm, hb, hspan⟩ := exists_span_of_dottedArrow B Q d l
  let e : q.Extension :=
    { R' := d.R', K' := d.K', ringMap := d.ringMap, fieldMap := d.fieldMap
      isLocalHom := d.isLocalHom, fraction_comm := d.fraction_comm
      ring_mem := d.ring_mem, field_mem := d.field_mem
      specialOver := d.specialOver, specialOver_left := d.specialOver_left
      genericOver := d.genericOver, genericOver_left := d.genericOver_left
      genericMap := d.genericMap, genericMap_left := d.genericMap_left }
  refine ⟨e, ⟨{ z := ZK, a := ZR, n := n ≫ cG, m := m, b := b ≫ cL,
                n_lift := ?_, m_lift := hm, b_lift := ?_, comm := ?_ }⟩⟩
  · exact comp_isHomLift_id hn hcG
  · exact comp_isHomLift_id hb hcL
  · have hh := congrArg (fun t => t ≫ cL) hspan
    rw [hcQ] at hh
    simpa only [c, f.hom.hom.toFunctor.map_comp, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id] using hh

/-- **The criterion for categories fibred in groupoids generalises the one for algebraic stacks.**
A 1-morphism of algebraic stacks satisfies the existence part of the valuative criterion of
Stacks 0CLK exactly when its underlying 1-morphism of categories fibred in groupoids satisfies
`AlgebraicGeometry.Stack.FiberedValuativeExistence`. -/
theorem valuativeCriterionExistence_iff_fiberedValuativeExistence (f : 𝒳 ⟶ 𝒴) :
    ValuativeCriterion.Existence B S hS f ↔ FiberedValuativeExistence B S hS f.hom :=
  ⟨fun H q => q.exists_of_valuativeSquare H, fun H q => by
    obtain ⟨e, ⟨l⟩⟩ := H q.toFibered
    exact q.exists_of_toFibered e l⟩

end Comparison

end AlgebraicGeometry.Stack

end
