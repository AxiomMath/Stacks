module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# The truncation `τ^{≥d} K ≅ H^d(K)[-d]` computes the identity on `H^d`

`DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor` identifies the one-step truncation
`τ^{≥q} τ^{<q+1}` with `H^q(-)` placed in degree `q`. This file computes its effect on cohomology:
applying `H^q` to that isomorphism, and reading the result through
`DerivedCategory.singleFunctorCompHomologyFunctorIso`, gives back the comparison
`DerivedCategory.truncGELTCompHomologyFunctorIso` of `τ^{≥q} τ^{<q+1} ⋙ H^q` with `H^q`.

## Main results

* `Stacks.TruncGESingleHomology.homologyMap_truncGELTIso_hom_app`: the identity above.
* `Stacks.TruncGESingleHomology.homologyMap_truncGEπ_truncGELTIso`: for `K` with no cohomology
  above `d`, the canonical map `κ : K ⟶ H^d(K)[-d]` — the truncation projection followed by that
  identification — induces the **identity** on `H^d`, up to the canonical identification of
  `H^d` of a single complex with the object itself.
* `Stacks.TruncGESingleHomology.eq_truncGEπ_comp_of_homologyMap_eq_id`: a morphism `K ⟶ H^d(K)[-d]`
  inducing the identity on `H^d` is the composite of the truncation projection with any isomorphism
  `τ^{≥d} K ≅ H^d(K)[-d]` whose composite with the truncation projection does so; in particular
  that property determines `κ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category

namespace Stacks.TruncGESingleHomology

open DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- Naturality of `singleFunctorCompHomologyFunctorIso` for `H^q` of a single map. -/
private theorem map_single_map_comp_iso (q : ℤ) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (homologyFunctor C q).map ((singleFunctor C q).map g) ≫
        (singleFunctorCompHomologyFunctorIso C q).hom.app Y₂ =
      (singleFunctorCompHomologyFunctorIso C q).hom.app Y₁ ≫ g := by
  simpa using (singleFunctorCompHomologyFunctorIso C q).hom.naturality g

/-- **`truncGELTIsoHomologyFunctorCompSingleFunctor` induces the canonical comparison on
`H^q`.** -/
theorem homologyMap_truncGELTIso_hom_app (q : ℤ) (X : DerivedCategory C) :
    (homologyFunctor C q).map
          ((truncGELTIsoHomologyFunctorCompSingleFunctor q).hom.app X) ≫
        (singleFunctorCompHomologyFunctorIso C q).hom.app
          ((homologyFunctor C q).obj X) =
      (truncGELTCompHomologyFunctorIso q).hom.app X := by
  have keya : ∀ {Y₁ Y₂ Z : C} (g : Y₁ ⟶ Y₂) (h : Y₂ ⟶ Z),
      (homologyFunctor C q).map ((singleFunctor C q).map g) ≫
          (singleFunctorCompHomologyFunctorIso C q).hom.app Y₂ ≫ h =
        (singleFunctorCompHomologyFunctorIso C q).hom.app Y₁ ≫ g ≫ h := by
    intro Y₁ Y₂ Z g h
    rw [← assoc, map_single_map_comp_iso, assoc]
  simp only [truncGELTIsoHomologyFunctorCompSingleFunctor, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.map_comp, assoc, id_comp]
  rw [map_single_map_comp_iso q, keya, keya, Iso.hom_inv_id_app_assoc, ← assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  simp

/-- `truncLTCompHomologyFunctorIso` is the map induced by the truncation inclusion. -/
theorem truncLTCompHomologyFunctorIso_hom_app (c i : ℤ) (hi : i < c) (X : DerivedCategory C) :
    (truncLTCompHomologyFunctorIso c i hi).hom.app X =
      (homologyFunctor C i).map ((TStructure.t.truncLTι c).app X) := by
  simp [truncLTCompHomologyFunctorIso]

/-- `truncGECompHomologyFunctorIso` is the map induced by the truncation projection. -/
theorem truncGECompHomologyFunctorIso_hom_app (c i : ℤ) (hi : c ≤ i) (X : DerivedCategory C) :
    (truncGECompHomologyFunctorIso c i hi).hom.app X =
      (homologyFunctor C i).map ((TStructure.t.truncGEπ c).app X) := by
  simp [truncGECompHomologyFunctorIso]

/-- **`truncGELTCompHomologyFunctorIso` is the truncation projection inverted and then the
truncation inclusion.** -/
theorem truncGELTCompHomologyFunctorIso_hom_app (q : ℤ) (X : DerivedCategory C) :
    (truncGELTCompHomologyFunctorIso q).hom.app X =
      (truncGECompHomologyFunctorIso q q le_rfl).inv.app
          ((TStructure.t.truncLT (q + 1)).obj X) ≫
        (homologyFunctor C q).map ((TStructure.t.truncLTι (q + 1)).app X) := by
  simp [truncGELTCompHomologyFunctorIso, truncLTCompHomologyFunctorIso_hom_app]

/-- **The canonical map `κ : K ⟶ H^d(K)[-d]` induces the identity on `H^d`.**

For `K` with no cohomology above `d` the truncation inclusion `τ^{<d+1} K ⟶ K` is invertible, so
`τ^{≥d} K` is `τ^{≥d} τ^{<d+1} K`, which `truncGELTIsoHomologyFunctorCompSingleFunctor` identifies
with `H^d(K)` placed in degree `d`. The composite of the truncation projection with that
identification is the canonical map `κ`; this says that `H^d(κ)`, read through the canonical
identification of `H^d` of a single complex with the object itself, is the identity. -/
theorem homologyMap_truncGEπ_truncGELTIso (K : DerivedCategory C) (d : ℤ)
    (hι : IsIso ((TStructure.t.truncLTι (d + 1)).app K)) :
    (homologyFunctor C d).map
          ((TStructure.t.truncGEπ d).app K ≫
            (TStructure.t.truncGE d).map
                (asIso ((TStructure.t.truncLTι (d + 1)).app K)).inv ≫
              (truncGELTIsoHomologyFunctorCompSingleFunctor d).hom.app K) ≫
        (singleFunctorCompHomologyFunctorIso C d).hom.app
          ((homologyFunctor C d).obj K) =
      𝟙 ((homologyFunctor C d).obj K) := by
  have hnat := TStructure.t.truncGEπ_naturality d
    (asIso ((TStructure.t.truncLTι (d + 1)).app K)).inv
  simp only [Functor.id_obj] at hnat
  rw [Functor.map_comp, Functor.map_comp, assoc, assoc,
    homologyMap_truncGELTIso_hom_app, truncGELTCompHomologyFunctorIso_hom_app,
    ← assoc ((homologyFunctor C d).map ((TStructure.t.truncGEπ d).app K)),
    ← Functor.map_comp, hnat, Functor.map_comp, assoc,
    ← truncGECompHomologyFunctorIso_hom_app d d le_rfl,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp]
  simp

/-- **`κ` is the only morphism `K ⟶ H^d(K)[-d]` inducing the identity on `H^d`.** Given any
isomorphism `ε : τ^{≥d} K ≅ H^d(K)[-d]` whose composite with the truncation projection induces the
identity on `H^d`, a morphism `φ` with the same effect on `H^d` equals that composite. -/
theorem eq_truncGEπ_comp_of_homologyMap_eq_id (K : DerivedCategory C) (d : ℤ)
    (ε : (TStructure.t.truncGE d).obj K ≅
      (singleFunctor C d).obj ((homologyFunctor C d).obj K))
    (hε : (homologyFunctor C d).map ((TStructure.t.truncGEπ d).app K ≫ ε.hom) ≫
        (singleFunctorCompHomologyFunctorIso C d).hom.app ((homologyFunctor C d).obj K) =
      𝟙 ((homologyFunctor C d).obj K))
    (φ : K ⟶ (singleFunctor C d).obj ((homologyFunctor C d).obj K))
    (hφ : (homologyFunctor C d).map φ ≫
        (singleFunctorCompHomologyFunctorIso C d).hom.app ((homologyFunctor C d).obj K) =
      𝟙 ((homologyFunctor C d).obj K)) :
    φ = (TStructure.t.truncGEπ d).app K ≫ ε.hom := by
  have hdesc : (TStructure.t.truncGEπ d).app K ≫ TStructure.t.descTruncGE φ d = φ :=
    TStructure.t.π_descTruncGE φ d
  obtain ⟨v, hv⟩ := (singleFunctor C d).map_surjective (ε.inv ≫ TStructure.t.descTruncGE φ d)
  have hfac : φ = ((TStructure.t.truncGEπ d).app K ≫ ε.hom) ≫ (singleFunctor C d).map v := by
    rw [hv, assoc, Iso.hom_inv_id_assoc, hdesc]
  have hv1 : v = 𝟙 ((homologyFunctor C d).obj K) := by
    rw [hfac, Functor.map_comp, assoc, map_single_map_comp_iso, ← assoc, hε, id_comp] at hφ
    exact hφ
  rw [hfac, hv1, CategoryTheory.Functor.map_id, comp_id]

end Stacks.TruncGESingleHomology

end
