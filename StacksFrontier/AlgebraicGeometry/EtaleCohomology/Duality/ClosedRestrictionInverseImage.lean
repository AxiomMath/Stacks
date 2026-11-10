module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroInverseImageCounit

/-!
# Inverse image of the restriction to a closed subscheme

Let `g : Y' ⟶ Y` be a morphism of schemes, `Y = j(V) ⊔ i(W)` and `Y' = j'(V') ⊔ i'(W')`
decompositions into an open and a complementary closed subscheme with `g(V') ⊆ V` and
`g(W') ⊆ W`. Write `E_W = i_* i⁻¹` and `E_{W'} = i'_* i'⁻¹` for the restrictions to the closed
parts. Then `g⁻¹ ∘ E_W ≅ E_{W'} ∘ g⁻¹`, naturally, compatibly with the units `𝟭 ⟶ E_W` and
`𝟭 ⟶ E_{W'}`: both `g⁻¹ E_W G` and `E_{W'} g⁻¹ G` are the cokernel of the extension by zero from
the open part (Tag 095L), and the inverse image of `j_! j⁻¹ G ⟶ G` is `j'_! j'⁻¹ g⁻¹ G ⟶ g⁻¹ G`
(`Stacks.EtaleCohomology.inverseImageExtensionByZeroCounitIso`). The square need not be
cartesian: `W'` may be any closed subscheme with the same support as the preimage of `W`.

## Main definitions

* `Stacks.EtaleCohomology.closedRestrictionInverseImageIso`: `g⁻¹ ∘ E_W ≅ E_{W'} ∘ g⁻¹`.

## Main results

* `Stacks.EtaleCohomology.inverseImage_map_unit_comp_closedRestrictionInverseImageIsoApp_hom`:
  the isomorphism carries `g⁻¹` of the unit `G ⟶ E_W G` to the unit `g⁻¹ G ⟶ E_{W'} g⁻¹ G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {Y Y' W W' V V' : Scheme.{u}} (g : Y' ⟶ Y)
  (i : W ⟶ Y) [IsClosedImmersion i] (j : V ⟶ Y) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)
  (i' : W' ⟶ Y') [IsClosedImmersion i'] (j' : V' ⟶ Y') [IsOpenImmersion j']
  (hij' : Set.range j'.base = (Set.range i'.base)ᶜ)
  (gW : W' ⟶ W) (hW : i' ≫ g = gW ≫ i) (gV : V' ⟶ V) (hV : j' ≫ g = gV ≫ j)

/-- The restriction `i_* i⁻¹` to a closed subscheme, on sheaves of `Λ`-modules. -/
abbrev closedRestrictionFunctor : EtaleModules.{u, r} Λ Y ⥤ EtaleModules.{u, r} Λ Y :=
  etaleModuleInverseImage.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ i

include hij hij' hW hV in
/-- **`g⁻¹(i_* i⁻¹ G) ≅ i'_* i'⁻¹(g⁻¹ G)`**, the unique isomorphism compatible with the units of
`i⁻¹ ⊣ i_*` and `i'⁻¹ ⊣ i'_*`. -/
def closedRestrictionInverseImageIsoApp (G : EtaleModules.{u, r} Λ Y) :
    (etaleModuleInverseImage.{u, r} Λ g).obj ((closedRestrictionFunctor Λ i).obj G) ≅
      (closedRestrictionFunctor Λ i').obj ((etaleModuleInverseImage.{u, r} Λ g).obj G) := by
  have hS₂ := inverseImageOpenClosedShortComplex_shortExact Λ g i j hij G
  have hS₁ := (shortExact_etaleModuleExtensionByZero_directImage.{u, r} Λ i' j' hij'
    ((etaleModuleInverseImage.{u, r} Λ g).obj G)).choose_spec
  haveI := hS₁.epi_g
  haveI := hS₂.epi_g
  exact {
    hom := hS₂.exact.desc _ (inverseImage_map_counit_comp_unit_eq_zero Λ g i j hij i' gW hW G)
    inv := hS₁.exact.desc _ (counit_comp_inverseImage_map_unit_eq_zero Λ g i j hij j' gV hV G)
    hom_inv_id := by
      rw [← cancel_epi ((inverseImageOpenClosedShortComplex Λ g i j hij G).g), Category.comp_id,
        ← Category.assoc, hS₂.exact.g_desc]
      exact hS₁.exact.g_desc _ _
    inv_hom_id := by
      rw [← cancel_epi ((etaleModuleInverseImageAdj.{u, r} Λ i').unit.app
        ((etaleModuleInverseImage.{u, r} Λ g).obj G)), Category.comp_id, ← Category.assoc]
      rw [show (etaleModuleInverseImageAdj.{u, r} Λ i').unit.app
          ((etaleModuleInverseImage.{u, r} Λ g).obj G) ≫
            hS₁.exact.desc _ (counit_comp_inverseImage_map_unit_eq_zero Λ g i j hij j' gV hV G) =
          (etaleModuleInverseImage.{u, r} Λ g).map
            ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.app G) from hS₁.exact.g_desc _ _]
      exact hS₂.exact.g_desc _ _ }

/-- **The isomorphism is compatible with the units.** -/
@[reassoc]
theorem inverseImage_map_unit_comp_closedRestrictionInverseImageIsoApp_hom
    (G : EtaleModules.{u, r} Λ Y) :
    (etaleModuleInverseImage.{u, r} Λ g).map ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.app G) ≫
        (closedRestrictionInverseImageIsoApp Λ g i j hij i' j' hij' gW hW gV hV G).hom =
      (etaleModuleInverseImageAdj.{u, r} Λ i').unit.app
        ((etaleModuleInverseImage.{u, r} Λ g).obj G) := by
  have hS₂ := inverseImageOpenClosedShortComplex_shortExact Λ g i j hij G
  have := hS₂.epi_g
  exact hS₂.exact.g_desc _ _

/-- **`g⁻¹ ∘ i_* i⁻¹ ≅ i'_* i'⁻¹ ∘ g⁻¹`**, naturally. -/
def closedRestrictionInverseImageIso :
    closedRestrictionFunctor Λ i ⋙ etaleModuleInverseImage.{u, r} Λ g ≅
      etaleModuleInverseImage.{u, r} Λ g ⋙ closedRestrictionFunctor Λ i' :=
  NatIso.ofComponents (closedRestrictionInverseImageIsoApp Λ g i j hij i' j' hij' gW hW gV hV)
    (fun {G G'} f => by
      have hS₂ := inverseImageOpenClosedShortComplex_shortExact Λ g i j hij G
      have := hS₂.epi_g
      rw [← cancel_epi ((inverseImageOpenClosedShortComplex Λ g i j hij G).g)]
      change (etaleModuleInverseImage.{u, r} Λ g).map
          ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.app G) ≫
          (etaleModuleInverseImage.{u, r} Λ g).map ((closedRestrictionFunctor Λ i).map f) ≫ _ =
        (etaleModuleInverseImage.{u, r} Λ g).map
          ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.app G) ≫ _ ≫ _
      have key := inverseImage_map_unit_comp_closedRestrictionInverseImageIsoApp_hom Λ g i j hij i'
        j' hij' gW hW gV hV
      have hu := (etaleModuleInverseImageAdj.{u, r} Λ i).unit.naturality f
      dsimp only [Functor.id_map, Functor.comp_map] at hu
      have hu' := (etaleModuleInverseImageAdj.{u, r} Λ i').unit.naturality
        ((etaleModuleInverseImage.{u, r} Λ g).map f)
      dsimp only [Functor.id_map, Functor.comp_map] at hu'
      calc _ = (etaleModuleInverseImage.{u, r} Λ g).map f ≫
            ((etaleModuleInverseImage.{u, r} Λ g).map
              ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.app G') ≫
            (closedRestrictionInverseImageIsoApp Λ g i j hij i' j' hij' gW hW gV hV G').hom) := by
            rw [← Functor.map_comp_assoc, show (etaleModuleInverseImageAdj.{u, r} Λ i).unit.app G ≫
              (closedRestrictionFunctor Λ i).map f = f ≫
                (etaleModuleInverseImageAdj.{u, r} Λ i).unit.app G' from hu.symm,
              Functor.map_comp_assoc]
        _ = (etaleModuleInverseImage.{u, r} Λ g).map f ≫
            (etaleModuleInverseImageAdj.{u, r} Λ i').unit.app
              ((etaleModuleInverseImage.{u, r} Λ g).obj G') := by rw [key]
        _ = (etaleModuleInverseImageAdj.{u, r} Λ i').unit.app
              ((etaleModuleInverseImage.{u, r} Λ g).obj G) ≫
            (closedRestrictionFunctor Λ i').map ((etaleModuleInverseImage.{u, r} Λ g).map f) :=
            hu'
        _ = _ := by rw [← key, Category.assoc]; rfl)

/-- The component of `closedRestrictionInverseImageIso` at `G` is
`closedRestrictionInverseImageIsoApp` at `G`. -/
@[simp]
theorem closedRestrictionInverseImageIso_app (G : EtaleModules.{u, r} Λ Y) :
    (closedRestrictionInverseImageIso Λ g i j hij i' j' hij' gW hW gV hV).app G =
      closedRestrictionInverseImageIsoApp Λ g i j hij i' j' hij' gW hW gV hV G :=
  rfl

end Stacks.EtaleCohomology

end
