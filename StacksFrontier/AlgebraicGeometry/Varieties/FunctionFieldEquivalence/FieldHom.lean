module

public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.GenericPointData

/-!
# Dominant rational maps of varieties and maps of function fields

A dominant rational map of varieties over `k` induces a `k`-algebra map of function fields in
the opposite direction, by pullback at the generic points. This assignment is injective, surjective
and compatible with identities and composition, so taking function fields is a contravariant fully
faithful operation on varieties over `k`. Surjectivity is where Stacks 0BX8 enters: a prescribed
local homomorphism on generic stalks extends to a rational map because the structure morphism of a
variety is locally of finite presentation.

## Main definitions

* `AlgebraicGeometry.fieldHomOfRationalMap` — the `k`-algebra map `k(Y) → k(X)` induced by a
  morphism of varieties `X ⟶ Y`.
* `AlgebraicGeometry.fieldHomOfRationalMap_injective` and
  `AlgebraicGeometry.fieldHomOfRationalMap_surjective` — it is a bijection onto the `k`-algebra
  maps `k(Y) → k(X)`.
* `AlgebraicGeometry.fieldHomOfRationalMap_id` and `AlgebraicGeometry.fieldHomOfRationalMap_comp` —
  functoriality.

## References

* [Stacks Project, Tag 0BXN](https://stacks.math.columbia.edu/tag/0BXN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A generic-point datum whose point is the generic point of the target induces a `k`-algebra map
from the function field of the target to that of the source. -/
private noncomputable def fieldHomOfGenericPointLocalMap {k : Type u} [Field k]
    (X Y : Variety k)
    (d : (varietyGenericPointMapContext X Y).GenericPointLocalMap
      (⟨0, by simp [varietyGenericPointMapContext]⟩ :
        Fin (varietyGenericPointMapContext X Y).numberOfComponents))
    (hp : d.point = genericPoint Y.toScheme) :
    Y.toScheme.functionField →ₐ[k] X.toScheme.functionField := by
  rcases d with ⟨p, mapsTo, ψ, hlocal, hcomm⟩
  dsimp [varietyGenericPointMapContext] at mapsTo ψ hlocal hcomm
  have hp' : p = genericPoint Y.toScheme := hp
  subst p
  let pY := Y.structureMap (genericPoint Y.toScheme)
  let pX := X.structureMap (genericPoint X.toScheme)
  have hbase : pY = pX := Subsingleton.elim _ _
  have hmaps : mapsTo = hbase := Subsingleton.elim _ _
  rw [hmaps] at hcomm
  let c := eqToHom (congrArg (fun z : PrimeSpectrum k =>
    (Spec (.of k)).presheaf.stalk z) hbase)
  letI : Algebra k ((Spec (.of k)).presheaf.stalk
      pY) := StructureSheaf.stalkAlgebra k pY
  letI : Algebra k ((Spec (.of k)).presheaf.stalk
      pX) := StructureSheaf.stalkAlgebra k pX
  let φ := ψ.hom
  refine { φ with commutes' := fun a => ?_ }
  change φ ((Y.structureMap.stalkMap (genericPoint Y.toScheme)).hom
      (algebraMap k ((Spec (.of k)).presheaf.stalk
        pY) a)) =
    (X.structureMap.stalkMap (genericPoint X.toScheme)).hom
      (algebraMap k ((Spec (.of k)).presheaf.stalk
        pX) a)
  have hα : c.hom.comp (algebraMap k
      ((Spec (.of k)).presheaf.stalk pY)) = algebraMap k
        ((Spec (.of k)).presheaf.stalk pX) := by
    change (eqToHom (congrArg (fun z : PrimeSpectrum k =>
      (Spec (.of k)).presheaf.stalk z) hbase)).hom.comp
        (StructureSheaf.toStalk k pY).hom = (StructureSheaf.toStalk k pX).hom
    exact primeSpectrum_toStalk_congr (k := k) hbase
  have hcomm'' : Y.structureMap.stalkMap (genericPoint Y.toScheme) ≫ ψ =
      c ≫ X.structureMap.stalkMap (genericPoint X.toScheme) := by
    simpa [c, varietyGenericPointMapContext] using hcomm
  have hcommApply := congrArg
    (fun (g : (Spec (.of k)).presheaf.stalk pY →+* _) =>
      g (algebraMap k ((Spec (.of k)).presheaf.stalk pY) a))
    (congrArg CommRingCat.Hom.hom hcomm'')
  have hcommApply' := by simpa [RingHom.comp_apply] using hcommApply
  calc
    φ ((Y.structureMap.stalkMap (genericPoint Y.toScheme)).hom
        (algebraMap k ((Spec (.of k)).presheaf.stalk pY) a)) =
        (X.structureMap.stalkMap (genericPoint X.toScheme)).hom
          (c.hom (algebraMap k ((Spec (.of k)).presheaf.stalk pY) a)) := hcommApply'
    _ = (X.structureMap.stalkMap (genericPoint X.toScheme)).hom
        (algebraMap k ((Spec (.of k)).presheaf.stalk pX) a) :=
      congrArg (X.structureMap.stalkMap (genericPoint X.toScheme)).hom
        (congrArg (fun g : k →+* (Spec (.of k)).presheaf.stalk pX => g a) hα)

/-- The `k`-algebra map `k(Y) → k(X)` induced by a dominant rational map of varieties `X ⤏ Y`. -/
@[no_expose]
noncomputable def fieldHomOfRationalMap {k : Type u} [Field k]
    (X Y : Variety k) (f : X.Hom Y) :
    Y.toScheme.functionField →ₐ[k] X.toScheme.functionField :=
  fieldHomOfGenericPointLocalMap X Y (rationalMapGenericData X Y f)
    (rationalMapGenericData_point X Y f)

/-- A generic-point datum at the generic point whose stalk map is the identity induces the
identity `k`-algebra map of the function field. -/
private lemma fieldHomOfGenericPointLocalMap_id {k : Type u} [Field k]
    (X : Variety k)
    (d : (varietyGenericPointMapContext X X).GenericPointLocalMap
      (⟨0, by simp [varietyGenericPointMapContext]⟩ :
        Fin (varietyGenericPointMapContext X X).numberOfComponents))
    (hp : d.point = genericPoint X.toScheme)
    (hs : HEq d.stalkMap (𝟙 X.toScheme.functionField)) :
    fieldHomOfGenericPointLocalMap X X d hp =
      AlgHom.id k X.toScheme.functionField := by
  rcases d with ⟨point, mapsTo, ψ, isLocal, commutes⟩
  obtain rfl : point = genericPoint X.toScheme := hp
  have hs' : HEq ψ (𝟙 X.toScheme.functionField) := by simpa using hs
  obtain rfl : ψ = 𝟙 X.toScheme.functionField := eq_of_heq hs'
  exact AlgHom.ext fun _ => rfl

/-- The identity morphism of a variety induces the identity of its function field. -/
lemma fieldHomOfRationalMap_id {k : Type u} [Field k] (X : Variety k) :
    fieldHomOfRationalMap X X (𝟙 X) = AlgHom.id k X.toScheme.functionField :=
  fieldHomOfGenericPointLocalMap_id X (rationalMapGenericData X X (𝟙 X))
    (rationalMapGenericData_point X X (𝟙 X)) (rationalMapGenericData_id_stalkMap X)

/-- Reading off the `k`-algebra map of the generic-point datum attached to a `k`-algebra map of
function fields recovers that map. -/
private lemma fieldHomOfGenericPointLocalMapOfFieldHom {k : Type u} [Field k]
    (X Y : Variety k) (φ : Y.toScheme.functionField →ₐ[k] X.toScheme.functionField) :
    fieldHomOfGenericPointLocalMap X Y (genericPointLocalMapOfFieldHom X Y φ)
      rfl = φ :=
  AlgHom.ext fun _ => rfl

/-- Every `k`-algebra map `k(Y) → k(X)` of function fields of varieties comes from a dominant
rational map `X ⤏ Y` over `k`. This is the surjectivity half of full faithfulness, and it is
where Stacks 0BX8 is used. -/
lemma fieldHomOfRationalMap_surjective {k : Type u} [Field k]
    (X Y : Variety k) (φ : Y.toScheme.functionField →ₐ[k] X.toScheme.functionField) :
    ∃ f : X.Hom Y, fieldHomOfRationalMap X Y f = φ := by
  let C := varietyGenericPointMapContext X Y
  let i : Fin C.numberOfComponents := ⟨0, by simp [C, varietyGenericPointMapContext]⟩
  let d : ∀ j : Fin C.numberOfComponents, C.GenericPointLocalMap j := fun j => by
    have hj : j.val < 1 := by
      simpa [C, varietyGenericPointMapContext] using j.isLt
    have hij : j = i := Fin.ext (show j.val = 0 by omega)
    subst j
    exact genericPointLocalMapOfFieldHom X Y φ
  let G := C.genericPointMapForRationalMaps
  have : LocallyOfFinitePresentation C.toBaseTarget :=
    varietyStructureMap_locallyOfFinitePresentation Y
  obtain ⟨q, hq⟩ :=
    (GenericPointMapContext.bijective_genericPointMapForRationalMaps_of_locallyOfFinitePresentation
      C).2 d
  let : C.X.Over C.S := ⟨C.toBaseSource⟩
  let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
  have : q.1.IsOver C.S := (Scheme.RationalMap.isOver_iff).2 q.2
  obtain ⟨g, hg, hrepr⟩ := q.1.exists_partialMap_over C.S
  have hbase : g.hom ≫ Y.structureMap = g.domain.ι ≫ X.structureMap :=
    (Scheme.PartialMap.isOver_iff).mp hg
  have : IsIntegral C.X := show IsIntegral X.toScheme from inferInstance
  have : IrreducibleSpace C.X := inferInstance
  have hmem : C.genericPoint i ∈ g.domain :=
    genericPoint_mem_of_dense g.domain g.dense_domain
  have hpoint := C.genericPointMapForRationalMaps.map_point q g hrepr hbase
    (fun _ ↦ hmem) i
  have hpoint' : g.hom ⟨C.genericPoint i, hmem⟩ = genericPoint Y.toScheme := by
    have hdi := congrArg (fun z : C.GenericPointLocalMap i => z.point)
      (congrFun hq i)
    change (C.genericPointMapForRationalMaps q i).point = _ at hpoint
    rw [hdi] at hpoint
    simpa [d, i, C, varietyGenericPointMapContext,
      genericPointLocalMapOfFieldHom] using hpoint.symm
  have hgdom : IsDominant g.hom :=
    ⟨(dense_iff_closure_eq.mpr (genericPoint_spec Y.toScheme)).mono
      (Set.singleton_subset_iff.mpr ⟨⟨C.genericPoint i, hmem⟩, hpoint'⟩)⟩
  have hdom : q.1.IsDominant := hrepr ▸ (g.toRationalMap.isDominant_iff).2 hgdom
  let : C.X.Over (Spec (.of k)) := ⟨C.toBaseSource⟩
  let : C.Y.Over (Spec (.of k)) := ⟨C.toBaseTarget⟩
  let : X.toScheme.Over (Spec (.of k)) := ⟨X.structureMap⟩
  let : Y.toScheme.Over (Spec (.of k)) := ⟨Y.structureMap⟩
  have hqover : Scheme.RationalMap.IsOver (Spec (.of k))
      (q.1 : X.toScheme ⤏ Y.toScheme) := (Scheme.RationalMap.isOver_iff).2 q.2
  refine ⟨@Variety.Hom.mk k ‹Field k› X Y q.1 hdom hqover, ?_⟩
  have hi : G q i = genericPointLocalMapOfFieldHom X Y φ := by
    simpa [d] using congrFun hq i
  show fieldHomOfGenericPointLocalMap X Y (G q i) _ = φ
  simpa only [hi] using fieldHomOfGenericPointLocalMapOfFieldHom X Y φ

/-- The `k`-algebra map extracted from a generic-point datum at the generic point of the target is,
as a map of stalks, the stalk map of that datum. -/
private lemma fieldHomOfGenericPointLocalMap_stalkMap {k : Type u} [Field k]
    (X Y : Variety k)
    (d : (varietyGenericPointMapContext X Y).GenericPointLocalMap
      ⟨0, by simp [varietyGenericPointMapContext]⟩)
    (hp : d.point = genericPoint Y.toScheme) :
    HEq (CommRingCat.ofHom (fieldHomOfGenericPointLocalMap X Y d hp).toRingHom)
      d.stalkMap := by
  rcases d with ⟨p, hbase, ψ, hlocal, hcomm⟩
  obtain rfl : p = genericPoint Y.toScheme := hp
  rfl

/-- The induced map of function fields is pullback at the generic point: for any representative
partial map `g` of the rational map which is defined at the generic point of the source and
compatible with the structure morphisms, `fieldHomOfRationalMap X Y f` is the stalk map of `g`
followed by the identification of the stalk of the domain with the stalk of the source. -/
lemma fieldHomOfRationalMap_stalkMap {k : Type u} [Field k]
    (X Y : Variety k) (f : X.Hom Y) (g : X.toScheme.PartialMap Y.toScheme)
    (hrepr : g.toRationalMap = f.toRationalMap)
    (hbase : g.hom ≫ Y.structureMap = g.domain.ι ≫ X.structureMap)
    (hmem : genericPoint X.toScheme ∈ g.domain) :
    HEq (CommRingCat.ofHom (fieldHomOfRationalMap X Y f).toRingHom)
      (g.hom.stalkMap ⟨genericPoint X.toScheme, hmem⟩ ≫
        (g.domain.stalkIso ⟨genericPoint X.toScheme, hmem⟩).hom) :=
  (fieldHomOfGenericPointLocalMap_stalkMap X Y
      (rationalMapGenericData X Y f) (rationalMapGenericData_point X Y f)).trans
    (rationalMapGenericData_stalkMap X Y f g hrepr hbase hmem)

/-- The morphism `Spec k(X) ⟶ Y` obtained from the induced map of function fields is the canonical
morphism attached to the rational map. -/
lemma fieldHomOfRationalMap_specMap {k : Type u} [Field k]
    (X Y : Variety k) (f : X.Hom Y) :
    Spec.map (CommRingCat.ofHom (fieldHomOfRationalMap X Y f).toRingHom) ≫
      Y.toScheme.fromSpecStalk (genericPoint Y.toScheme) =
        f.toRationalMap.fromFunctionField := by
  obtain ⟨g, hg, hrep⟩ := f.toRationalMap.exists_partialMap_over (Spec (.of k))
  have hbase := Scheme.PartialMap.isOver_iff.mp hg
  have hmem := genericPoint_mem_of_dense g.domain g.dense_domain
  let z : g.domain := ⟨genericPoint X.toScheme, hmem⟩
  have hpoint : genericPoint Y.toScheme = g.hom z :=
    (rationalMapGenericData_point X Y f).symm.trans
      ((varietyGenericPointMapContext X Y).genericPointMapForRationalMaps.map_point
        (rationalMapOverData X Y f) g hrep hbase (fun _ ↦ hmem)
        ⟨0, by simp [varietyGenericPointMapContext]⟩)
  have hs := fieldHomOfRationalMap_stalkMap X Y f g hrep hbase hmem
  rw [specMap_fromSpecStalk_eq_of_heq hpoint hs, Spec.map_comp, Category.assoc]
  calc
    Spec.map (g.domain.stalkIso z).hom ≫
        (Spec.map (g.hom.stalkMap z) ≫ Y.toScheme.fromSpecStalk (g.hom z)) =
      Spec.map (g.domain.stalkIso z).hom ≫
        (g.domain.toScheme.fromSpecStalk z ≫ g.hom) :=
          congrArg (fun t => Spec.map (g.domain.stalkIso z).hom ≫ t)
            (Scheme.SpecMap_stalkMap_fromSpecStalk g.hom)
    _ = f.toRationalMap.fromFunctionField := by
      rw [← hrep, Scheme.RationalMap.fromFunctionField_toRationalMap]
      have : IsIso (g.domain.ι.stalkMap z) := by
        rw [← Scheme.Opens.stalkIso_inv]
        exact (g.domain.stalkIso z).isIso_inv
      show Spec.map (g.domain.stalkIso z).hom ≫
        (g.domain.toScheme.fromSpecStalk z ≫ g.hom) =
          (Spec.map (inv (g.domain.ι.stalkMap z)) ≫
            g.domain.toScheme.fromSpecStalk z) ≫ g.hom
      simp [← Scheme.Opens.stalkIso_inv, Category.assoc]

/-- Taking function fields is contravariantly functorial on dominant rational maps of varieties. -/
lemma fieldHomOfRationalMap_comp {k : Type u} [Field k]
    (X Y Z : Variety k) (f : X ⟶ Y) (g : Y ⟶ Z) :
    fieldHomOfRationalMap X Z (f ≫ g) =
      (fieldHomOfRationalMap X Y f).comp (fieldHomOfRationalMap Y Z g) := by
  apply AlgHom.coe_ringHom_injective
  suffices h : CommRingCat.ofHom (fieldHomOfRationalMap X Z (f ≫ g)).toRingHom =
      CommRingCat.ofHom ((fieldHomOfRationalMap X Y f).comp
        (fieldHomOfRationalMap Y Z g)).toRingHom from congrArg CommRingCat.Hom.hom h
  apply Spec.map_injective
  apply (cancel_mono (Z.toScheme.fromSpecStalk (genericPoint Z.toScheme))).mp
  rw [fieldHomOfRationalMap_specMap]
  show (f.toRationalMap.comp g.toRationalMap).fromFunctionField = _
  have hp := fieldHomOfRationalMap_specMap X Y f
  rw [← g.toRationalMap.toRationalMap_representative,
    Scheme.RationalMap.comp_def,
    Scheme.RationalMap.fromFunctionField_toRationalMap]
  rw [← f.toRationalMap.toRationalMap_representative,
    Scheme.RationalMap.fromFunctionField_toRationalMap] at hp
  rw [partialMap_fromFunctionField_comp _ _ _ hp,
    ← Scheme.RationalMap.fromFunctionField_toRationalMap,
    g.toRationalMap.toRationalMap_representative, ← fieldHomOfRationalMap_specMap Y Z g]
  exact (Spec.map_comp_assoc _ _ _).symm

/-- A dominant rational map of varieties is determined by the induced map of function fields.
This is the faithfulness half of full faithfulness. -/
lemma fieldHomOfRationalMap_injective {k : Type u} [Field k]
    (X Y : Variety k) : Function.Injective (fieldHomOfRationalMap X Y) := by
  intro f g h
  apply Variety.Hom.ext
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [← fieldHomOfRationalMap_specMap X Y f, ← fieldHomOfRationalMap_specMap X Y g, h]

end AlgebraicGeometry

end
