module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic

/-!
# Sections of the glued module through the restriction adjunction

The glued module of a `Stacks.SheafOfModules.ModulesGlueData` comes with comparison isomorphisms
`D.glued.restrict (f i) ≅ D.mod i` on each chart of the family. Transposing the `i`-th
comparison across the adjunction `restrictFunctor (f i) ⊣ pushforward (f i)` turns it into a
single morphism `D.glued ⟶ (pushforward (f i)).obj (D.mod i)` of sheaves of modules on the
ambient scheme, and this file identifies that morphism on sections over an open `V` inside the
range of `f i` with the chart isomorphism `ModulesGlueData.chartSectionsIso` there. The
consequence is that the transition isomorphism of the glueing datum carries the `i`-th chart of a
section of the glued module to its `j`-th chart.

The adjunction triangle `ModulesGlueData.restrictFunctor_map_chartAdjunct` records that the
transposed comparison, restricted back along `f i` and followed by the counit, is the comparison
isomorphism again; it is what makes the chart comparison of the glued module an isomorphism on
each chart of the family.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

open AlgebraicGeometry

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ S}
  [∀ i, IsOpenImmersion (f i)]

namespace ModulesGlueData

/-- The comparison isomorphism `D.glued.restrict (f i) ≅ D.mod i` of
`ModulesGlueData.chartIso`, transposed across the adjunction
`restrictFunctor (f i) ⊣ pushforward (f i)` into a morphism of sheaves of modules on `S`. -/
noncomputable def chartAdjunct (D : ModulesGlueData S f) (i : ι) :
    D.glued ⟶ (Scheme.Modules.pushforward (f i)).obj (D.mod i) :=
  (Scheme.Modules.restrictAdjunction (f i)).homEquiv _ _ (D.chartIso i).hom

/-- **The adjunction triangle for `chartAdjunct`.**  Restricting the transposed comparison along
`f i` and following it with the counit of the restriction adjunction gives back the comparison
isomorphism `ModulesGlueData.chartIso`.  In particular the restriction of `chartAdjunct i` along
`f i` is an isomorphism, although `chartAdjunct i` itself is not. -/
lemma restrictFunctor_map_chartAdjunct (D : ModulesGlueData S f) (i : ι) :
    (Scheme.Modules.restrictFunctor (f i)).map (D.chartAdjunct i) ≫
        ((Scheme.Modules.restrictFunctorAdjCounitIso (f i)).app (D.mod i)).hom =
      (D.chartIso i).hom :=
  (Adjunction.homEquiv_counit (adj := Scheme.Modules.restrictAdjunction (f i))
      (g := (Scheme.Modules.restrictAdjunction (f i)).homEquiv _ _
        (D.chartIso i).hom)).symm.trans (Equiv.symm_apply_apply _ _)

/-- On sections over an open `V` inside the range of `f i` the transposed comparison
`chartAdjunct` is the chart isomorphism `ModulesGlueData.chartSectionsIso`: the unit of the
adjunction restricts a section of the glued module from `V` to `f i ''ᵁ (f i ⁻¹ᵁ V)`, which is `V`
again because `V` lies in the range of `f i`, so no restriction survives. -/
lemma chartAdjunct_apply (D : ModulesGlueData S f) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) (s : ToType (D.glued.val.obj (op V))) :
    (D.chartAdjunct i).app V s = (D.chartSectionsIso i hV).hom s := by
  have h4 : ∀ {A B : (Y i).Opens} (a : op A ⟶ op B) (b : op B ⟶ op A)
      (x : ToType ((D.mod i).val.obj (op A))),
      (D.mod i).val.map b ((D.mod i).val.map a x) = x := by
    intro A B a b x
    rw [← PresheafOfModules.map_comp_apply, show a ≫ b = 𝟙 _ from Subsingleton.elim _ _,
      (D.mod i).val.map_id]
    rfl
  have h1 : (D.chartAdjunct i).app V s
      = (D.mod i).val.map
          (eqToHom ((f i).preimage_image_eq ((f i) ⁻¹ᵁ V)).symm).op
          ((D.toOModuleGlueData.chartIso i ((f i).image_le_opensRange ((f i) ⁻¹ᵁ V))).hom
            (D.glued.val.map (homOfLE ((f i).image_preimage_le V)).op s)) := rfl
  have h3 : (D.toOModuleGlueData.chartIso i ((f i).image_le_opensRange ((f i) ⁻¹ᵁ V))).hom
        (D.glued.val.map (homOfLE ((f i).image_preimage_le V)).op s)
      = (D.mod i).val.map ((Opens.map (f i).base).map
          (homOfLE ((f i).image_preimage_le V))).op ((D.chartSectionsIso i hV).hom s) :=
    D.toOModuleGlueData.chartLinearEquiv_restrict i hV ((f i).image_preimage_le V) s
  rw [h1, h3]
  exact h4 _ _ _

/-- The transition isomorphism of the glueing datum carries the `i`-th chart of a section of the
glued module to its `j`-th chart, over any open `V` contained in the ranges of both `f i` and
`f j`. -/
lemma trans_chartAdjunct (D : ModulesGlueData S f) (i j : ι) {V : S.Opens}
    (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange)
    (s : ToType (D.glued.val.obj (op V))) :
    D.trans i j hi hj ((D.chartAdjunct i).app V s) = (D.chartAdjunct j).app V s := by
  rw [D.chartAdjunct_apply i hi s, D.chartAdjunct_apply j hj s]
  exact D.toOModuleGlueData.trans_chartLinearEquiv i j hi hj s

end ModulesGlueData

end Stacks.SheafOfModules

end
