module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeGluingOverBasis

/-!
# Gluing a compatible family of morphisms of schemes

Fix a locally directed open cover `𝒰` of a scheme `S` and two relative gluing data over it, with
local schemes `Xᵢ` and `Yᵢ`. A family of morphisms `Xᵢ ⟶ Yᵢ` commuting with the restriction maps
and lying over the members of the cover glues to a morphism `X ⟶ Y` of the glued schemes. That
morphism is over `S` and restricts to the given one on every member of the cover.

The same functoriality holds for the gluing data of Tag 01LH, which are indexed by a basis `B` of
the topology of `S` rather than by a locally directed cover: given two such data, with local
schemes `X_U ⟶ U` and `Y_U ⟶ U`, and morphisms `h_U : X_U ⟶ Y_U` over `U` compatible with the two
families of restriction morphisms, there is a morphism `h : X ⟶ Y` over `S` between any two
solutions of the corresponding gluing problems which restricts back to the `h_U`, and it is the
only such morphism.

## Main definitions

* `AlgebraicGeometry.CompatibleRelativeGluingData` bundles two relative gluing data over one
  locally directed open cover together with a compatible family of morphisms between their local
  schemes.

## Main results

* `CategoryTheory.Limits.colimMap` is the induced morphism of glued schemes, and
  `CategoryTheory.Limits.ι_colimMap` says that it restricts to the given morphism on each member
  of the cover. Both are Mathlib declarations, recorded here for Tag 01LK.
* `AlgebraicGeometry.CompatibleRelativeGluingData.colimMap_localHom_toBase`: the induced
  morphism is a morphism over the base.
* `AlgebraicGeometry.Scheme.BasisGluingData.existsUnique_hom_of_compatible`: **the functoriality
  of Tag 01LK for the gluing data of Tag 01LH**, which are indexed by a basis of the topology of
  the base.

## Implementation notes

The glued schemes are the colimits of their relative gluing diagrams, so the induced morphism is
the map on colimits associated with the natural transformation of local morphisms; no new
definition is needed for it. The family of local morphisms and its compatibility with the
restriction maps are therefore expressed by a natural transformation, and being a morphism over
the corresponding member of the cover is the equality of natural transformations `localHom_over`.
Mathlib's relative gluing data canonically supply the glued schemes, their structure maps, and
the pullback identifications with the local schemes.

Agreement of the induced morphism with the given family on each member of the cover is the
canonical cocone equation `CategoryTheory.Limits.ι_colimMap`; compatibility with the base follows
from the local compatibility equation by `colimit.hom_ext`.

Over a basis the morphism is not produced as a map of colimits, because the source and the target
are arbitrary solutions of the two gluing problems and need not be the canonical colimits. Instead
the charts of a solution form a locally directed open cover of it
(`AlgebraicGeometry.Scheme.BasisGluingData.Gluing.cover`), so the composites of the `h_U` with the
charts of the target glue; compatibility with the base and uniqueness both follow because a
morphism out of a solution is determined by its charts.

## References

* [Stacks Project, Tag 01LK](https://stacks.math.columbia.edu/tag/01LK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Two relative gluing data over one locally directed open cover, equipped with a compatible
family of morphisms between their local schemes. -/
public structure CompatibleRelativeGluingData where
  /-- The base scheme. -/
  base : Scheme.{u}
  /-- The locally directed open cover of the base. -/
  cover : base.OpenCover
  /-- The category structure recording inclusions among members of the cover. -/
  [category : Category cover.I₀]
  /-- The cover is locally directed. -/
  [locallyDirected : cover.LocallyDirected]
  /-- The indexing category is small enough for the relative gluing construction. -/
  [small : Small.{u} cover.I₀]
  /-- There is at most one inclusion between two members of the cover. -/
  [thin : Quiver.IsThin cover.I₀]
  /-- The relative gluing datum for the source schemes. -/
  source : cover.RelativeGluingData
  /-- The relative gluing datum for the target schemes. -/
  target : cover.RelativeGluingData
  /-- The morphisms between the local source and target schemes, compatible with restriction. -/
  localHom : source.functor ⟶ target.functor
  /-- Every local morphism is a morphism over the corresponding member of the base cover. -/
  localHom_over : localHom ≫ target.natTrans = source.natTrans

namespace CompatibleRelativeGluingData

add_to_stacks 01LK "scheme_morphism" CategoryTheory.Limits.colimMap
add_to_stacks 01LK "scheme_morphism" CategoryTheory.Limits.ι_colimMap

variable (D : CompatibleRelativeGluingData.{u})

/-- The category structure on the index set of the cover. -/
local instance : Category D.cover.I₀ := D.category
/-- The cover is locally directed. -/
local instance : D.cover.LocallyDirected := D.locallyDirected
/-- The index set of the cover is `u`-small. -/
local instance : Small.{u} D.cover.I₀ := D.small
/-- There is at most one inclusion between two members of the cover. -/
local instance : Quiver.IsThin D.cover.I₀ := D.thin

/-- The morphism induced on the glued schemes is a morphism over the common base. -/
@[stacks 01LK "scheme_morphism"]
public lemma colimMap_localHom_toBase :
    colimMap D.localHom ≫ D.target.toBase = D.source.toBase := by
  refine colimit.hom_ext fun i ↦ ?_
  rw [← Category.assoc, ι_colimMap, Category.assoc, D.target.ι_toBase, D.source.ι_toBase,
    ← D.localHom_over, NatTrans.comp_app]
  exact (Category.assoc _ _ _).symm

end CompatibleRelativeGluingData

/-! ### Functoriality for the gluing data of Tag 01LH -/

section Basis

open TopologicalSpace

namespace Scheme.BasisGluingData

variable {S : Scheme.{u}} {B : Set S.Opens}

/-- **Stacks Project, Tag 01LK: functoriality for the data of Lemma 01LH.** Let `S` be a scheme
and `B` a basis for its topology, and let `D` and `D'` be gluing data over `B` as in Tag 01LH,
with local schemes `D.obj U ⟶ U` and `D'.obj U ⟶ U` and restriction morphisms `D.res` and
`D'.res`. Let `f : X ⟶ S` be a scheme glued from `D`, with charts `i U`, and `g : Y ⟶ S` one
glued from `D'`, with charts `j U`. A family of morphisms `h U : D.obj U ⟶ D'.obj U` over `U`
compatible with the restriction morphisms gives rise to a morphism `k : X ⟶ Y` over `S` which
restricts back to the `h U`, and `k` is the only such morphism. -/
@[stacks 01LK "scheme_morphism, for the gluing data over a basis of Tag 01LH"]
public theorem existsUnique_hom_of_compatible (hB : Opens.IsBasis B) (D D' : BasisGluingData S B)
    {X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {i : ∀ U : B, D.obj U ⟶ X} {j : ∀ U : B, D'.obj U ⟶ Y}
    (hi : ∀ U : B, IsPullback (D.proj U) (i U) U.1.ι f)
    (hj : ∀ U : B, IsPullback (D'.proj U) (j U) U.1.ι g)
    (hires : ∀ {V U : B} (h : V.1 ≤ U.1), D.res h ≫ i U = i V)
    (hjres : ∀ {V U : B} (h : V.1 ≤ U.1), D'.res h ≫ j U = j V)
    (h : ∀ U : B, D.obj U ⟶ D'.obj U)
    (hover : ∀ U : B, h U ≫ D'.proj U = D.proj U)
    (hcompat : ∀ {V U : B} (hVU : V.1 ≤ U.1), D.res hVU ≫ h U = h V ≫ D'.res hVU) :
    ∃! k : X ⟶ Y, (∀ U : B, i U ≫ k = h U ≫ j U) ∧ k ≫ g = f := by
  let G : D.Gluing := ⟨X, f, i, hi, hires⟩
  let G' : D'.Gluing := ⟨Y, g, j, hj, hjres⟩
  have hw : ∀ {a b : B} (hab : a ⟶ b),
      (G.cover hB).trans hab ≫ (h b ≫ G'.chart b) = h a ≫ G'.chart a := by
    intro a b hab
    change D.res (leOfHom hab) ≫ h b ≫ G'.chart b = h a ≫ G'.chart a
    rw [← Category.assoc, hcompat (leOfHom hab), Category.assoc, G'.res_comp_chart]
  set k := (G.cover hB).glueMorphismsOfLocallyDirected (fun U => h U ≫ G'.chart U) hw
  have hchart : ∀ U : B, G.chart U ≫ k = h U ≫ G'.chart U := fun U =>
    (G.cover hB).map_glueMorphismsOfLocallyDirected (fun U => h U ≫ G'.chart U) hw U
  refine ⟨k, ⟨hchart, ?_⟩, ?_⟩
  · refine G.hom_ext hB fun U ↦ ?_
    rw [← Category.assoc, hchart U, Category.assoc, ← (G'.isPullback_chart U).w,
      ← Category.assoc, hover U, ← (G.isPullback_chart U).w]
  · intro m hm
    refine G.hom_ext hB fun U ↦ ?_
    rw [hm.1 U, hchart U]

end Scheme.BasisGluingData

end Basis

end AlgebraicGeometry
