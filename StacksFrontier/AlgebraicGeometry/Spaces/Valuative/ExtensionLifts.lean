module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartValuativeExtension

/-!
# Lifting the edges of a valuative square after dominating extensions

Let `q` be a valuative square for a morphism `f : X ⟶ Y` of presheaves on the big fppf site of a
scheme `S`, with valuation ring `R` and fraction field `K`. Arguments with the valuative
criterion often lift, one after the other, morphisms out of `Spec R` and `Spec K` through further
morphisms `t : T ⟶ T'`, each time after replacing `R` by a valuation ring dominating it in an
extension of `K`. This file provides the steps of such an argument.

* Dominating extensions compose: an extension of an extension of `q` is an extension of `q`.
* If `t` satisfies the existence part of the valuative criterion, then any commutative square
  `Spec K ⟶ T`, `Spec R ⟶ T'` over `t` acquires a dotted arrow after a dominating extension of
  `q`.
* If `t` is a flat morphism of algebraic spaces, then any `Spec R ⟶ T'` whose closed point lies
  in the image of `|T| ⟶ |T'|` lifts through `t` after a dominating extension of `q`
  (Stacks 089F).

## Main definitions

* `AlgebraicGeometry.Space.ValuativeSquare.DominatingExtension.trans`: the composite of two
  dominating extensions.
* `AlgebraicGeometry.Space.ValuativeSquare.closedPoint`: the closed point of the spectrum of the
  valuation ring, as a point of the presheaf it represents.

## Main results

* `AlgebraicGeometry.Space.ValuativeSquare.exists_dominatingExtension_lift_of_existence`: the
  existence step.
* `AlgebraicGeometry.Space.ValuativeSquare.exists_dominatingExtension_lift_of_isFlat`: the flat
  step.

## References

* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 089F](https://stacks.math.columbia.edu/tag/089F)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace ValuativeSquare

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- **Dominating extensions compose.** An extension `e'` of the square of a dominating extension
`e` of `q` is a dominating extension of `q`, through the composite homomorphisms of valuation
rings and of fraction fields. -/
noncomputable def DominatingExtension.trans {q : ValuativeSquare f} (e : q.DominatingExtension)
    (e' : e.square.DominatingExtension) : q.DominatingExtension := by
  letI := e.isLocalHom
  letI := e'.isLocalHom
  exact {
    square := e'.square
    ringMap := e'.ringMap.comp e.ringMap
    fieldMap := e'.fieldMap.comp e.fieldMap
    isLocalHom := inferInstance
    fraction_comm := by
      rw [← RingHom.comp_assoc, e'.fraction_comm, RingHom.comp_assoc,
        e.fraction_comm, RingHom.comp_assoc]
    base_comm := by
      rw [e'.base_comm, e.base_comm, ← Category.assoc, ← Spec.map_comp]
      rfl
    genericOver := e'.genericOver ≫ e.genericOver
    genericOver_left := by
      change B.inclusion.map e'.genericOver.left ≫ B.inclusion.map e.genericOver.left = _
      rw [e'.genericOver_left, e.genericOver_left, ← Spec.map_comp]
      rfl
    specialOver := e'.specialOver ≫ e.specialOver
    specialOver_left := by
      change B.inclusion.map e'.specialOver.left ≫ B.inclusion.map e.specialOver.left = _
      rw [e'.specialOver_left, e.specialOver_left, ← Spec.map_comp]
      rfl
    generic_comm := by rw [e'.generic_comm, e.generic_comm]; simp
    special_comm := by rw [e'.special_comm, e.special_comm]; simp }

/-- The generic-point morphism of a composite of dominating extensions is the composite of the
generic-point morphisms. -/
@[simp]
theorem DominatingExtension.trans_genericOver {q : ValuativeSquare f}
    (e : q.DominatingExtension) (e' : e.square.DominatingExtension) :
    (e.trans e').genericOver = e'.genericOver ≫ e.genericOver := rfl

/-- The closed-point morphism of a composite of dominating extensions is the composite of the
closed-point morphisms. -/
@[simp]
theorem DominatingExtension.trans_specialOver {q : ValuativeSquare f}
    (e : q.DominatingExtension) (e' : e.square.DominatingExtension) :
    (e.trans e').specialOver = e'.specialOver ≫ e.specialOver := rfl

/-- The square of a composite of dominating extensions is the square of the second one. -/
theorem DominatingExtension.trans_square {q : ValuativeSquare f}
    (e : q.DominatingExtension) (e' : e.square.DominatingExtension) :
    (e.trans e').square = e'.square := rfl

/-- **The existence step.** Let `q` be a valuative square, with valuation ring `R` and fraction
field `K`, and let `t : T ⟶ T'` satisfy the existence part of the valuative criterion. A
commutative square `gen : Spec K ⟶ T`, `spec : Spec R ⟶ T'` over `t` acquires a dotted arrow
after a dominating extension of `q`. -/
theorem exists_dominatingExtension_lift_of_existence (q : ValuativeSquare f) (t : T ⟶ T')
    (ht : ValuativeCriterion.Existence t)
    (gen : yoneda.obj (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ T)
    (spec : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ T')
    (h : gen ≫ t = yoneda.map q.fracHom ≫ spec) :
    ∃ (e : q.DominatingExtension)
      (φ : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ T),
      yoneda.map e.square.fracHom ≫ φ = yoneda.map e.genericOver ≫ gen ∧
        φ ≫ t = yoneda.map e.specialOver ≫ spec := by
  let q' : ValuativeSquare t :=
    { R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem, base := q.base
      generic := gen, special := spec, comm := h }
  obtain ⟨e', ⟨l⟩⟩ := ht q'
  have hsq : yoneda.map e'.genericOver ≫ yoneda.map q.fracHom =
      yoneda.map e'.square.fracHom ≫ yoneda.map e'.specialOver :=
    e'.yonedaMap_genericOver_comp_fracHom
  let e : q.DominatingExtension :=
    { square :=
        { R := e'.square.R, K := e'.square.K
          ring_mem := e'.square.ring_mem, field_mem := e'.square.field_mem
          base := e'.square.base
          generic := yoneda.map e'.genericOver ≫ q.generic
          special := yoneda.map e'.specialOver ≫ q.special
          comm := by
            rw [Category.assoc, q.comm', ← Category.assoc, hsq, Category.assoc] }
      ringMap := e'.ringMap, fieldMap := e'.fieldMap, isLocalHom := e'.isLocalHom
      fraction_comm := e'.fraction_comm, base_comm := e'.base_comm
      genericOver := e'.genericOver, genericOver_left := e'.genericOver_left
      specialOver := e'.specialOver, specialOver_left := e'.specialOver_left
      generic_comm := rfl, special_comm := rfl }
  exact ⟨e, l.map, l.generic_comm'.trans e'.generic_comm, l.special_comm.trans e'.special_comm⟩

/-- The residue field of the valuation ring of a valuative square at its closed point, as a
field-valued point of the presheaf represented by the spectrum of the valuation ring. -/
noncomputable def closedFieldPoint (q : ValuativeSquare f) :
    FieldValuedPoint B S hS (yoneda.obj (siteObject B S hS q.ring_mem q.base)) where
  carrier := IsLocalRing.ResidueField q.R
  contained := spec_mem_of_surjective B q.ring_mem (IsLocalRing.residue q.R)
    IsLocalRing.residue_surjective
  toBase := Spec.map (CommRingCat.ofHom (IsLocalRing.residue q.R)) ≫ q.base
  value := Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue q.R))))

/-- The closed point of the spectrum of the valuation ring of a valuative square, as a point of
the presheaf it represents. -/
noncomputable def closedPoint (q : ValuativeSquare f) :
    points B S hS (yoneda.obj (siteObject B S hS q.ring_mem q.base)) :=
  q.closedFieldPoint.class B S hS _

/-- **The flat step (Stacks 089F).** Let `q` be a valuative square, with valuation ring `R`, let
`t : T ⟶ T'` be a flat morphism of algebraic spaces and let `spec : Spec R ⟶ T'` send the
closed point into the image of `|T| ⟶ |T'|`. Then `spec` lifts through `t` after a dominating
extension of `q`.

This is `AlgebraicGeometry.Space.exists_valuationRing_extension_lift_of_isFlat`; the enlarged
valuation ring and its fraction field are made into a dominating extension as in
`AlgebraicGeometry.Space.exists_dominatingExtension_lift_of_isFlat_of_isSurjective`. -/
theorem exists_dominatingExtension_lift_of_isFlat (q : ValuativeSquare f)
    (hT : IsAlgebraicSpace B S hS T) (hT' : IsAlgebraicSpace B S hS T') (t : T ⟶ T')
    (ht : IsFlat B S hS t) (spec : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ T')
    (himage : pointsMap B S hS _ spec q.closedPoint ∈ Set.range (pointsMap B S hS T t)) :
    ∃ (e : q.DominatingExtension)
      (φ : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ T),
      φ ≫ t = yoneda.map e.specialOver ≫ spec := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨A, hAring, hAdomain, hAval, i, hi, V, eV, j, l, hj, hl⟩ :=
    AlgebraicGeometry.Space.exists_valuationRing_extension_lift_of_isFlat q.R hT hT' t ht
      (siteObject B S hS q.ring_mem q.base) (Iso.refl _) spec q.closedFieldPoint
      (IsLocalRing.comap_closedPoint (IsLocalRing.residue q.R)) himage
  have hA : B.Contains (Spec (.of A)) := (Scheme.size_congr eV).symm.trans_lt V.left.2
  let L := FractionRing A
  let kmap : q.K →+* L := IsFractionRing.lift (A := q.R) (K := q.K)
    (g := (algebraMap A L).comp i) ((IsFractionRing.injective A L).comp hi.1)
  have hkmap : (algebraMap A L).comp i = kmap.comp (algebraMap q.R q.K) :=
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap (K := q.K)
      (g := (algebraMap A L).comp i) ((IsFractionRing.injective A L).comp hi.1) x).symm
  let e := dominatingExtensionOfRingHom q hA (spec_fractionRing_mem B hA) i kmap hi.2 hkmap
  have hj' : G.map j = eV.hom ≫ Spec.map (CommRingCat.ofHom i) :=
    (Category.comp_id _).symm.trans hj
  have hb : eV.inv ≫ B.inclusion.map V.hom = e.square.base := by
    change eV.inv ≫ B.inclusion.map V.hom = Spec.map (CommRingCat.ofHom i) ≫ q.base
    have hw : G.map j ≫ q.base = B.inclusion.map V.hom := congrArg B.inclusion.map j.w
    rw [← hw, hj']
    simp
  let v : siteObject B S hS e.square.ring_mem e.square.base ⟶ V :=
    Over.homMk (ObjectProperty.homMk eV.inv) (B.inclusion.map_injective hb)
  have hv : v ≫ j = e.specialOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change eV.inv ≫ G.map j = Spec.map (CommRingCat.ofHom i)
    rw [hj']
    simp
  refine ⟨e, yoneda.map v ≫ l, ?_⟩
  rw [Category.assoc, hl, ← Category.assoc, ← yoneda.map_comp, hv]

end ValuativeSquare

end AlgebraicGeometry.Space

end
