module

public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.FunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMapFinitePresentation

/-!
# Generic-point data of a morphism of varieties

A variety is irreducible, so it has a single irreducible component with the generic point of
the scheme as its generic point. A pair of varieties over `k` therefore gives a
`AlgebraicGeometry.GenericPointMapContext`, in which a dominant rational map over `k` is evaluated
at that generic point: it records the image point, which is the generic point of the target, and
the induced local homomorphism of generic stalks. Conversely a `k`-algebra map of function fields
gives such a datum.

## Main definitions

* `AlgebraicGeometry.varietyGenericPointMapContext` — the context attached to two varieties.
* `AlgebraicGeometry.rationalMapGenericData` — the generic-point datum of a morphism of varieties.
* `AlgebraicGeometry.genericPointLocalMapOfFieldHom` — the generic-point datum attached to a
  `k`-algebra map of function fields.

## References

* [Stacks Project, Tag 0BXN](https://stacks.math.columbia.edu/tag/0BXN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An integral scheme has exactly one irreducible component, namely the whole space; this is
the resulting indexing of its irreducible components by `Fin 1`. -/
noncomputable def oneIrreducibleComponentEquiv (X : Scheme.{u})
    [IsIntegral X] : Fin 1 ≃ {Z : Set X // Z ∈ irreducibleComponents X} := by
  refine Equiv.ofBijective (fun (_ : Fin 1) ↦ ⟨Set.univ, ?_⟩) ⟨?_, ?_⟩
  · simp [irreducibleComponents_eq_singleton]
  · exact fun a b _ ↦ Subsingleton.elim a b
  · intro Z
    have hZ : Z.1 = Set.univ := by
      simpa [irreducibleComponents_eq_singleton] using Z.2
    exact ⟨0, Subtype.ext hZ.symm⟩

/-- The generic-point context of a pair of varieties over `k`: the source has the single
irreducible component `Set.univ`, whose generic point is the generic point of the scheme. -/
noncomputable def varietyGenericPointMapContext {k : Type u} [Field k]
    (X Y : Variety k) : GenericPointMapContext.{u} where
  S := Spec (.of k)
  X := X.toScheme
  Y := Y.toScheme
  toBaseSource := X.structureMap
  toBaseTarget := Y.structureMap
  numberOfComponents := 1
  components := oneIrreducibleComponentEquiv X.toScheme
  genericPoint := fun _ ↦ genericPoint X.toScheme
  isGenericPoint := fun _ ↦ by
    change IsGenericPoint (genericPoint X.toScheme) Set.univ
    exact genericPoint_spec X.toScheme

/-- A morphism of varieties over `k`, viewed as a rational map commuting with the structure
morphisms in the sense of `AlgebraicGeometry.GenericPointMapContext.RationalMapsOver`. -/
noncomputable def rationalMapOverData {k : Type u} [Field k]
    (X Y : Variety k) (f : X.Hom Y) :
    (varietyGenericPointMapContext X Y).RationalMapsOver := by
  let C := varietyGenericPointMapContext X Y
  letI : X.toScheme.Over C.S := ⟨C.toBaseSource⟩
  letI : Y.toScheme.Over C.S := ⟨C.toBaseTarget⟩
  letI : f.toRationalMap.IsOver C.S := f.isOver
  exact ⟨f.toRationalMap, Scheme.RationalMap.isOver_iff.mp f.isOver⟩

/-- The generic-point datum of a morphism of varieties over `k`: the image of the generic point
together with the induced local homomorphism of generic stalks. -/
noncomputable def rationalMapGenericData {k : Type u} [Field k]
    (X Y : Variety k) (f : X.Hom Y) :
    let C := varietyGenericPointMapContext X Y
    C.GenericPointLocalMap (⟨0, by simp [C, varietyGenericPointMapContext]⟩ :
      Fin C.numberOfComponents) := by
  let C := varietyGenericPointMapContext X Y
  let i : Fin C.numberOfComponents := ⟨0, by simp [C, varietyGenericPointMapContext]⟩
  exact C.genericPointMapForRationalMaps (rationalMapOverData X Y f) i

/-- A dominant rational map of varieties carries the generic point of the source to the generic
point of the target. -/
lemma rationalMapGenericData_point {k : Type u} [Field k]
    (X Y : Variety k) (f : X.Hom Y) :
    (rationalMapGenericData X Y f).point = genericPoint Y.toScheme := by
  let C := varietyGenericPointMapContext X Y
  let q := rationalMapOverData X Y f
  let : X.toScheme.Over C.S := ⟨C.toBaseSource⟩
  let : Y.toScheme.Over C.S := ⟨C.toBaseTarget⟩
  let : f.toRationalMap.IsOver C.S := f.isOver
  let : f.toRationalMap.IsDominant := f.isDominant
  let : LocallyOfFinitePresentation Y.structureMap :=
    varietyStructureMap_locallyOfFinitePresentation Y
  let g := Classical.choose (f.toRationalMap.exists_partialMap_over C.S)
  have hg := Classical.choose_spec (f.toRationalMap.exists_partialMap_over C.S)
  have hrep : g.toRationalMap = f.toRationalMap := hg.2
  have hbase : g.hom ≫ Y.structureMap = g.domain.ι ≫ X.structureMap :=
    (Scheme.PartialMap.isOver_iff).mp hg.1
  have hmem : genericPoint X.toScheme ∈ g.domain :=
    genericPoint_mem_of_dense g.domain g.dense_domain
  let : Nonempty g.domain := ⟨⟨genericPoint X.toScheme, hmem⟩⟩
  let : IsDominant g.hom := by
    have hr : g.toRationalMap.IsDominant := hrep ▸ f.isDominant
    exact (g.isDominant_toRationalMap_iff).mp hr
  let i : Fin C.numberOfComponents := ⟨0, by simp [C, varietyGenericPointMapContext]⟩
  have hpoint : (C.genericPointMapForRationalMaps q i).point =
      g.hom ⟨genericPoint X.toScheme, hmem⟩ :=
    C.genericPointMapForRationalMaps.map_point q g hrep hbase (fun _ ↦ hmem) i
  have hopen : (⟨genericPoint X.toScheme, hmem⟩ : g.domain) = genericPoint g.domain :=
    Subtype.ext (genericPoint_eq_of_isOpenImmersion g.domain.ι).symm
  change (C.genericPointMapForRationalMaps q i).point = genericPoint Y.toScheme
  rw [hpoint, hopen]
  exact map_genericPoint_of_isDominant g.hom

/-- The stalk map of the generic-point datum of a morphism of varieties is computed by any
representative partial map defined at the generic point and compatible with the base. -/
lemma rationalMapGenericData_stalkMap {k : Type u} [Field k]
    (X Y : Variety k) (f : X.Hom Y) (g : X.toScheme.PartialMap Y.toScheme)
    (hrepr : g.toRationalMap = f.toRationalMap)
    (hbase : g.hom ≫ Y.structureMap = g.domain.ι ≫ X.structureMap)
    (hmem : genericPoint X.toScheme ∈ g.domain) :
    HEq (rationalMapGenericData X Y f).stalkMap
      (g.hom.stalkMap ⟨genericPoint X.toScheme, hmem⟩ ≫
        (g.domain.stalkIso ⟨genericPoint X.toScheme, hmem⟩).hom) := by
  let C := varietyGenericPointMapContext X Y
  let i : Fin C.numberOfComponents := ⟨0, by simp [C, varietyGenericPointMapContext]⟩
  exact C.genericPointMapForRationalMaps.map_stalk (rationalMapOverData X Y f) g hrepr hbase
    (fun _ ↦ hmem) i

/-- The generic-point datum of the identity morphism of a variety has the identity of the function
field as its stalk map. -/
lemma rationalMapGenericData_id_stalkMap {k : Type u} [Field k]
    (X : Variety k) :
    HEq (rationalMapGenericData X X (𝟙 X)).stalkMap
      (𝟙 X.toScheme.functionField) := by
  let C := varietyGenericPointMapContext X X
  let p : X.toScheme.PartialMap X.toScheme := Scheme.PartialMap.id X.toScheme
  have hrepr : p.toRationalMap = (𝟙 X : X.Hom X).toRationalMap := rfl
  have hover : p.hom ≫ X.structureMap = p.domain.ι ≫ X.structureMap :=
    (Scheme.PartialMap.isOver_iff).mp (inferInstance : p.IsOver (Spec (.of k)))
  have hmem : genericPoint X.toScheme ∈ p.domain := by
    simp [p, Scheme.PartialMap.id]
  have htop : p.hom.stalkMap ⟨genericPoint X.toScheme, hmem⟩ =
      (p.domain.stalkIso ⟨genericPoint X.toScheme, hmem⟩).inv :=
    (Scheme.Opens.stalkIso_inv p.domain ⟨genericPoint X.toScheme, hmem⟩).symm
  refine (rationalMapGenericData_stalkMap X X (𝟙 X) p hrepr hover hmem).trans ?_
  rw [htop]
  exact heq_of_eq (p.domain.stalkIso ⟨genericPoint X.toScheme, hmem⟩).inv_hom_id

/-- A `k`-algebra map `k(Y) → k(X)` of function fields of varieties is the generic-point datum of
a rational map: the map of fields is automatically local, and compatibility with the base holds
because the structure map from `k` to the generic stalk of `Spec k` is surjective. -/
noncomputable def genericPointLocalMapOfFieldHom {k : Type u} [Field k]
    (X Y : Variety k) (φ : Y.toScheme.functionField →ₐ[k] X.toScheme.functionField) :
    let C := varietyGenericPointMapContext X Y
    C.GenericPointLocalMap (⟨0, by simp [C, varietyGenericPointMapContext]⟩ :
      Fin C.numberOfComponents) := by
  let C := varietyGenericPointMapContext X Y
  let ηY := genericPoint Y.toScheme
  let ηX := genericPoint X.toScheme
  letI : Field Y.toScheme.functionField := inferInstance
  letI : Field X.toScheme.functionField := inferInstance
  let pY := Y.structureMap ηY
  let pX := X.structureMap ηX
  have hbase : pY = pX := Subsingleton.elim _ _
  let c := eqToHom (congrArg (fun z : PrimeSpectrum k =>
    (Spec (.of k)).presheaf.stalk z) hbase)
  let RY := (Spec (.of k)).presheaf.stalk pY
  let RX := (Spec (.of k)).presheaf.stalk pX
  letI : Algebra k RY := StructureSheaf.stalkAlgebra k pY
  letI : Algebra k RX := StructureSheaf.stalkAlgebra k pX
  have hsurj : Function.Surjective (algebraMap k RY) := by
    change Function.Surjective (StructureSheaf.toStalk k pY).hom
    exact fieldBaseStalkAlgebraMap_surjective (k := k) (Subsingleton.elim _ _)
  refine {
    point := ηY
    mapsTo := hbase
    stalkMap := CommRingCat.ofHom φ.toRingHom
    isLocalHom := (inferInstance : IsLocalHom φ.toRingHom)
    commutes := ?_ }
  have hc : c.hom.comp (algebraMap k RY) = algebraMap k RX := by
    change c.hom.comp (StructureSheaf.toStalk k pY).hom =
      (StructureSheaf.toStalk k pX).hom
    exact primeSpectrum_toStalk_congr (k := k) hbase
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro x
  obtain ⟨a, rfl⟩ := hsurj x
  change φ ((Y.structureMap.stalkMap ηY).hom ((algebraMap k RY) a)) =
    (X.structureMap.stalkMap ηX).hom (c.hom ((algebraMap k RY) a))
  rw [show c.hom (algebraMap k RY a) = algebraMap k RX a from DFunLike.congr_fun hc a]
  exact φ.commutes a

end AlgebraicGeometry

end
