module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.DenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMapReduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericStalkCriterion

/-!
# Integral schemes of finite type with isomorphic generic residue fields share an open

Let `X` and `Y` be integral schemes locally of finite type over a base `S`. Then `X` and `Y`
are `S`-birational if and only if they have `S`-isomorphic nonempty open subschemes, and
if and only if their generic points have the same image `s` in `S` and their residue fields
there are isomorphic as extensions of the residue field of `s`.

## Main results

* `AlgebraicGeometry.birationalOver_tfae_of_isIntegral` is the equivalence of the three
  conditions, with `S`-birationality read as `AlgebraicGeometry.Scheme.BirationalOver`. Stacks
  Tag 0552, with Stacks' own notion of `S`-birationality, is
  `AlgebraicGeometry.tfae_dominantBirationalOver_residueField_genericPoint`.
* `AlgebraicGeometry.birationalOver_of_residueFieldIso` is the implication from the
  isomorphism of generic residue fields to birationality over the base.
* `AlgebraicGeometry.exists_nonempty_open_iso_of_residueFieldIso` is the implication from the
  isomorphism of generic residue fields to the existence of a common open, in the shape its
  consumers use.

## Implementation notes

The forward implication is
`AlgebraicGeometry.residueFieldIso_of_birationalOver`, and the equivalence with the existence
of `S`-isomorphic nonempty opens is
`AlgebraicGeometry.birationalOver_iff_exists_nonempty_open_iso`. Only the converse is proved
here, by the argument of the source: the local ring of an integral scheme at its generic point
is its residue field, so the prescribed isomorphism of residue fields is generic-point data in
the sense of Stacks Tag 0BX8 for the context with the single irreducible component; the source
being reduced and the target locally of finite type over the base, that data is realized by a
rational map, whose chosen representative is a birational morphism from a nonempty open of `X`
to `Y`; Stacks Tag 0BAC turns it into an isomorphism of nonempty opens.

The argument is that of `AlgebraicGeometry.birationalOver_iff_generic_stalk_iso`, which is the
same statement for targets locally of *finite presentation* and with the local rings in place of
the residue fields. Finite presentation is avoided here by using the bijectivity of the
generic-point map for a reduced source rather than for a target of finite presentation, and by
invoking Tag 0BAC in its finite-type form, which is available because `Y` is reduced.

## References

* [Stacks Project, Tag 0552](https://stacks.math.columbia.edu/tag/0552)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- In an irreducible scheme, the generic point is the generic point of every open containing
it. -/
private theorem isGenericPoint_mk_genericPoint_opens {X : Scheme.{u}} [IrreducibleSpace X]
    (U : X.Opens) (h : genericPoint X ∈ U) :
    IsGenericPoint (⟨genericPoint X, h⟩ : U.toScheme) Set.univ := by
  rw [isGenericPoint_def]
  refine Set.eq_univ_iff_forall.mpr fun w ↦ mem_closure_iff.mpr fun V hV hwV ↦ ?_
  let incl : U.toScheme → X := fun a ↦ a.1
  have hVopen : IsOpen (incl '' (V : Set U.toScheme)) :=
    U.2.isOpenEmbedding_subtypeVal.isOpenMap _ hV
  have hVne : (incl '' (V : Set U.toScheme)).Nonempty := ⟨w.1, ⟨w, hwV, rfl⟩⟩
  obtain ⟨v, hv, hvx⟩ : genericPoint X ∈ incl '' (V : Set U.toScheme) := by
    rw [(genericPoint_spec X).mem_open_set_iff hVopen]
    simpa using hVne
  have hvz : v = ⟨genericPoint X, h⟩ := Subtype.ext hvx
  exact ⟨_, hvz ▸ hv, rfl⟩

/-- The domain of a partial map out of an irreducible scheme is irreducible. -/
private theorem irreducibleSpace_partialMap_domain {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) : IrreducibleSpace g.domain.toScheme :=
  Subtype.irreducibleSpace ⟨g.dense_domain.nonempty_iff.mpr inferInstance,
    (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset g.domain.2
      (Set.subset_univ _)⟩

/-- A morphism of irreducible schemes sending the generic point to the generic point, with an
isomorphism of stalks there, is birational. -/
private theorem isBirational_of_map_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (hf : f (genericPoint X) = genericPoint Y)
    [IsIso (f.stalkMap (genericPoint X))] : IsBirational f :=
  isBirational_of_bijOn_of_isIso_stalkMap f
    (by simpa only [genericPoints_eq_singleton] using Set.bijOn_singleton.mpr hf)
    fun x hx ↦ by
      obtain rfl : x = genericPoint X := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
      infer_instance

/-- An irreducible space has finitely many irreducible components. -/
private instance finite_irreducibleComponents_of_irreducibleSpace {Z : Type*} [TopologicalSpace Z]
    [IrreducibleSpace Z] : Finite (irreducibleComponents Z) := by
  rw [irreducibleComponents_eq_singleton]
  infer_instance

/-- A partial map over the base which is birational and is defined on a dense open makes integral
schemes birational over the base. -/
private theorem birationalOver_of_partialMap {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType sX] (g : X.PartialMap Y)
    (hg : g.hom ≫ sY = g.domain.ι ≫ sX) (hbir : IsBirational g.hom) :
    Scheme.BirationalOver sX sY := by
  have := irreducibleSpace_partialMap_domain g
  let : LocallyOfFiniteType (g.hom ≫ sY) := by
    rw [hg]
    infer_instance
  exact (g.domain.birationalOver_of_dense sX g.dense_domain).symm.trans
    (birationalOver_of_isBirational (g.domain.ι ≫ sX) sY g.hom hbir hg
      (Or.inl ⟨locallyOfFiniteType_of_comp g.hom sY, inferInstance⟩))

/-- An isomorphism of the local rings at the generic points of two integral schemes over a
base, compatible with the structure morphisms, is realized by a birational partial map over the
base as soon as both are locally of finite type over it. -/
private theorem exists_partialMap_isBirational_of_genericStalkIso {S X Y : Scheme.{u}}
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (h : sX (genericPoint X) = sY (genericPoint Y))
    (e : X.presheaf.stalk (genericPoint X) ≅ Y.presheaf.stalk (genericPoint Y))
    (H : h ▸ (sX.stalkMap (genericPoint X) ≫ e.hom) = sY.stalkMap (genericPoint Y)) :
    ∃ g : X.PartialMap Y, g.hom ≫ sY = g.domain.ι ≫ sX ∧ IsBirational g.hom := by
  let C := genericPointContext sX sY
  let d : ∀ i : Fin C.numberOfComponents, C.GenericPointLocalMap i := fun i ↦
    { point := genericPoint Y
      mapsTo := h.symm
      stalkMap := e.inv
      isLocalHom := isLocalHom_of_iso e.symm
      commutes := transport_comp_inv C.S.presheaf.stalk h
        (C.toBaseSource.stalkMap (C.genericPoint i)) e
        (C.toBaseTarget.stalkMap (genericPoint Y)) H }
  let : LocallyOfFiniteType C.toBaseTarget := inferInstanceAs (LocallyOfFiniteType sY)
  let : IsReduced C.X := inferInstanceAs (IsReduced X)
  obtain ⟨r, hr⟩ :=
    (GenericPointMapContext.bijective_genericPointMapForRationalMaps_of_isReduced C).2 d
  let : IrreducibleSpace C.X := inferInstanceAs (IrreducibleSpace X)
  let : C.X.Over C.S := ⟨C.toBaseSource⟩
  let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
  let : r.1.IsOver C.S := (Scheme.RationalMap.isOver_iff).mpr r.2
  obtain ⟨g, hgOver, hgR⟩ := r.1.exists_partialMap_over C.S
  have hg : g.hom ≫ C.toBaseTarget = g.domain.ι ≫ C.toBaseSource :=
    (Scheme.PartialMap.isOver_iff).mp hgOver
  let i0 : Fin C.numberOfComponents := ⟨0, by simp [C]⟩
  have hxmem : C.genericPoint i0 ∈ g.domain :=
    (C.isGenericPoint i0).mem_open_set_iff g.domain.2 |>.2 (by
      simpa [C, i0] using g.dense_domain.nonempty_iff.mpr inferInstance)
  let z : g.domain.toScheme := ⟨C.genericPoint i0, hxmem⟩
  have hmap : g.hom z = genericPoint Y :=
    (C.genericPointMapForRationalMaps.map_point r g hgR hg (fun _ ↦ hxmem) i0).symm.trans
      (by rw [congrFun hr i0])
  have hstalk := C.genericPointMapForRationalMaps.map_stalk r g hgR hg (fun _ ↦ hxmem) i0
  have hstalkHEq : HEq e.inv (g.hom.stalkMap z ≫ (g.domain.stalkIso z).hom) := by
    rw [congrFun hr i0] at hstalk
    simpa [d] using hstalk
  have hstalkIso : IsIso (g.hom.stalkMap z ≫ (g.domain.stalkIso z).hom) := by
    have hDom : C.Y.presheaf.stalk (g.hom z) = Y.presheaf.stalk (genericPoint Y) := by
      rw [hmap]
    have hCod : C.X.presheaf.stalk z.1 = X.presheaf.stalk (genericPoint X) := by
      simp [z, C]
    exact isIso_of_heq_of_eq hDom hCod hstalkHEq
  have := irreducibleSpace_partialMap_domain g
  have hz : z = genericPoint g.domain.toScheme :=
    (isGenericPoint_mk_genericPoint_opens g.domain hxmem).eq
      (genericPoint_spec g.domain.toScheme)
  have : IsIso (g.hom.stalkMap (genericPoint g.domain.toScheme)) := by
    rw [← hz]
    exact (isIso_comp_right_iff (g.hom.stalkMap z) (g.domain.stalkIso z).hom).mp hstalkIso
  exact ⟨g, hg, isBirational_of_map_genericPoint g.hom (hz ▸ hmap)⟩

/-- An isomorphism of the local rings at the generic points of two integral schemes over a
base, compatible with the structure morphisms, makes them birational over that base as soon as
both are locally of finite type over it. -/
@[ega "I 6.5.5" "(ii)"]
private theorem birationalOver_of_genericStalkIso {S X Y : Scheme.{u}}
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (h : sX (genericPoint X) = sY (genericPoint Y))
    (e : X.presheaf.stalk (genericPoint X) ≅ Y.presheaf.stalk (genericPoint Y))
    (H : h ▸ (sX.stalkMap (genericPoint X) ≫ e.hom) = sY.stalkMap (genericPoint Y)) :
    Scheme.BirationalOver sX sY :=
  let ⟨g, hg, hbir⟩ := exists_partialMap_isBirational_of_genericStalkIso sX sY h e H
  birationalOver_of_partialMap sX sY g hg hbir

/-- For integral schemes locally of finite type over a base, an isomorphism of the residue
fields at the generic points over the base makes them birational over that base. -/
public theorem birationalOver_of_residueFieldIso {S X Y : Scheme.{u}}
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (h : sX (genericPoint X) = sY (genericPoint Y))
    (e : X.residueField (genericPoint X) ≅ Y.residueField (genericPoint Y))
    (he : h ▸ (sX.residueFieldMap (genericPoint X) ≫ e.hom) =
      sY.residueFieldMap (genericPoint Y)) :
    Scheme.BirationalOver sX sY :=
  let ⟨e', he'⟩ := exists_genericStalkIso_of_residueFieldIso sX sY h e he
  birationalOver_of_genericStalkIso sX sY h e' he'

/-- For integral schemes locally of finite type over a base, birationality over the base (an
isomorphism of dense open subschemes over the base), the existence of isomorphic nonempty open
subschemes over the base, and the existence of an isomorphism of the residue fields at the
generic points over the base are equivalent. -/
public theorem birationalOver_tfae_of_isIntegral {S X Y : Scheme.{u}}
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] :
    List.TFAE
      [Scheme.BirationalOver sX sY,
        ∃ (U : X.Opens) (V : Y.Opens), (U : Set X).Nonempty ∧ (V : Set Y).Nonempty ∧
          ∃ e : U.toScheme ≅ V.toScheme, e.hom ≫ V.ι ≫ sY = U.ι ≫ sX,
        ∃ (h : sX (genericPoint X) = sY (genericPoint Y))
          (e : X.residueField (genericPoint X) ≅ Y.residueField (genericPoint Y)),
          h ▸ (sX.residueFieldMap (genericPoint X) ≫ e.hom) =
            sY.residueFieldMap (genericPoint Y)] := by
  tfae_have 1 ↔ 2 := birationalOver_iff_exists_nonempty_open_iso sX sY
  tfae_have 1 → 3 := fun hb ↦ residueFieldIso_of_birationalOver sX sY hb
  tfae_have 3 → 1 := fun ⟨h, e, he⟩ ↦ birationalOver_of_residueFieldIso sX sY h e he
  tfae_finish

/-- For integral schemes locally of finite type over a base, an isomorphism of the residue
fields at the generic points over the base produces nonempty open subschemes which are
isomorphic over the base. -/
public theorem exists_nonempty_open_iso_of_residueFieldIso {S X Y : Scheme.{u}}
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (h : sX (genericPoint X) = sY (genericPoint Y))
    (e : X.residueField (genericPoint X) ≅ Y.residueField (genericPoint Y))
    (he : h ▸ (sX.residueFieldMap (genericPoint X) ≫ e.hom) =
      sY.residueFieldMap (genericPoint Y)) :
    ∃ (U : X.Opens) (V : Y.Opens), (U : Set X).Nonempty ∧ (V : Set Y).Nonempty ∧
      ∃ e' : U.toScheme ≅ V.toScheme, e'.hom ≫ V.ι ≫ sY = U.ι ≫ sX :=
  (birationalOver_iff_exists_nonempty_open_iso sX sY).mp
    (birationalOver_of_residueFieldIso sX sY h e he)

end AlgebraicGeometry

end
