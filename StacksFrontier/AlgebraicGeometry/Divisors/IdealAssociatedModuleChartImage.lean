module

public import StacksFrontier.AlgebraicGeometry.Divisors.IdealAssociatedModuleEtaleChart
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSubmoduleAssociatedModule

/-!
# The image of `ε^*I ⟶ 𝒪` on the sections over an arbitrary étale chart

Let `T` be a scheme contained in a big étale site `E` and let `I ⊆ 𝒪_T` be a quasi-coherent
sheaf of ideals.  `AlgebraicGeometry.SmallEtale.idealAssociatedMap` is the morphism `ε^*I ⟶ 𝒪`
of `𝒪`-modules on the small étale site of `T`: the associated-module functor `ε^*` of
Stacks 03DU (4) applied to the inclusion `I ⊆ 𝒪_T`, followed by the comparison `ε^*𝒪_T ≅ 𝒪` of
Stacks 070R.

This file computes its image on the sections over an **arbitrary** étale chart: over a chart
with structure morphism `g : W ⟶ T` the image is exactly the sections over `W` of the
inverse-image sheaf of ideals `I·𝒪_W` of Stacks 01WR.

`StacksFrontier/AlgebraicGeometry/Divisors/IdealSubmoduleAssociatedModule.lean` does this over the
charts cut out by the Zariski opens of `T`, and
`StacksFrontier/AlgebraicGeometry/Divisors/IdealAssociatedModuleEtaleChart.lean` does it over an
arbitrary chart for `ε^*(I ⊆ 𝒪_T)` *alone* — that is, with the sections read through the
Stacks 03DS identification rather than through the comparison of structure sheaves.  What is
added here is that the two readings may be interchanged, which turns that statement into one
about `ε^*I ⟶ 𝒪` and so removes the last comparison from the right-hand side.

## The two readings differ by a unit, and that is enough

A section of `ε^*𝒪_T` over a chart `W` can be read as a regular function on the chart scheme in
two ways:

* `AlgebraicGeometry.SmallEtale.structureComparisonSections`, through the comparison
  `ε^*𝒪_T ≅ 𝒪` of Stacks 070R, which is Mathlib's
  `CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` and is an isomorphism because the small
  Zariski site is final in the small étale site; and
* `AlgebraicGeometry.SmallEtale.chartStructureSections`, through the Stacks 03DS identification
  `AlgebraicGeometry.SmallEtale.chartSectionsIso` followed by the comparison `g^*𝒪_T ≅ 𝒪_W` of
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`.

**The two are not identified here.**  Identifying them is a statement about an arbitrary étale
chart, and the natural route to it — exhibiting the second as the sections of a morphism of
sheaves of modules — needs the naturality in the chart of
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, which this development carries only in the
form `AlgebraicGeometry.pullbackSectionsHomEquiv_naturality`, for the presheaf of morphisms of
the pullback pseudofunctor.

No identification is needed: both readings are **linear bijections** of the ring of regular
functions on the chart scheme with itself, so their comparison is multiplication by a unit, and
multiplication by a unit carries every ideal onto itself.  That is
`Stacks.Ideal.mem_iff_of_linear_bijective`, and it is the only place where the fact that `I` is a
sheaf of *ideals* rather than of modules is used.

## Main definitions

* `AlgebraicGeometry.SmallEtale.structureComparisonSections` and
  `AlgebraicGeometry.SmallEtale.chartStructureSections`: the two readings.
* `AlgebraicGeometry.SmallEtale.chartStructureComparison`: their comparison, the second reading
  after undoing the first.

## Main results

* `Stacks.Ideal.mem_iff_of_linear_bijective`: **an `R`-linear bijection of `R` onto itself
  preserves every ideal.**
* `AlgebraicGeometry.SmallEtale.structureComparisonSections_smul`,
  `AlgebraicGeometry.SmallEtale.chartStructureSections_smul` and their bijectivity companions:
  both readings are linear bijections.
* `AlgebraicGeometry.SmallEtale.mem_iff_chartStructureComparison_mem`: the comparison of the two
  readings preserves every multiplication-closed subset of the chart ring.
* `AlgebraicGeometry.SmallEtale.exists_idealAssociatedMap_app_eq_iff_mem`: **the image of
  `ε^*I ⟶ 𝒪` on the sections over an arbitrary étale chart is the sections there of `I·𝒪_W`.**

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), part (4), the associated
  module.
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS), the pullback-sections
  presheaf.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the comparison `ε`.
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S), the identification of
  the two.
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR), the inverse image of a
  sheaf of ideals.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.Ideal

/-- **An `R`-linear bijection of `R` onto itself preserves every ideal.**  Linearity makes it
multiplication by `σ 1`, and bijectivity makes `σ 1` a unit.

The ideal is taken as a multiplication-closed subset rather than as an `Ideal`, so that the
statement applies to a sheaf of ideals read as a submodule of the structure sheaf without
transporting the submodule across the identification of its ring of scalars. -/
theorem mem_iff_of_linear_bijective {R : Type*} [CommRing R] (σ : R → R)
    (hsmul : ∀ r x : R, σ (r * x) = r * σ x) (hbij : Function.Bijective σ)
    (P : R → Prop) (hP : ∀ r y : R, P y → P (r * y)) (x : R) :
    P (σ x) ↔ P x := by
  have h1 : ∀ y : R, σ y = y * σ 1 := fun y => by
    rw [← hsmul y 1, mul_one]
  obtain ⟨z, hz⟩ := hbij.2 1
  have hv : σ 1 * z = 1 := by rw [mul_comm, ← h1 z]; exact hz
  rw [h1 x]
  refine ⟨fun h => ?_, fun h => (mul_comm x (σ 1) ▸ hP (σ 1) x h : P (x * σ 1))⟩
  have hx : x = z * (x * σ 1) := by rw [mul_comm x (σ 1), ← mul_assoc, mul_comm z (σ 1), hv,
    one_mul]
  rw [hx]
  exact hP z _ h

end Stacks.Ideal

namespace AlgebraicGeometry.SmallEtale

variable (E : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : E.Contains T) (I : T.IdealSheafData)
  (W : (SmallEtale E T hT)ᵒᵖ)

/-- The comparison `ε^*𝒪_T ≅ 𝒪` of Stacks 070R, read on the sections over an étale chart. -/
public noncomputable abbrev structureComparisonSections :
    ToType (((associatedModule E T hT).obj (Scheme.unitModule T)).val.obj W) →
      ToType ((SheafOfModules.unit (structureSheaf E T hT)).val.obj W) :=
  ConcreteCategory.hom
    ((SheafOfModules.pullbackObjUnitToUnit (structureMap E T hT)).val.app W)

/-- The map on sections over an étale chart induced by `ε^*(I ⊆ 𝒪_T)` followed by the comparison
of structure sheaves is `AlgebraicGeometry.SmallEtale.idealAssociatedMap` there. -/
public theorem idealAssociatedMap_app_apply
    (m : ToType (((associatedModule E T hT).obj
      I.unitSubmodule.toSheafOfModules).val.obj W)) :
    ConcreteCategory.hom ((idealAssociatedMap E T hT I).val.app W) m =
      structureComparisonSections E T hT W
        (ConcreteCategory.hom (associatedIdealSectionsMap E T hT I W) m) := rfl

/-- **The structure comparison on sections is linear.** -/
public theorem structureComparisonSections_smul
    (r : ToType ((structureSheaf E T hT).obj.obj W))
    (x : ToType (((associatedModule E T hT).obj (Scheme.unitModule T)).val.obj W)) :
    structureComparisonSections E T hT W (r • x) =
      r • structureComparisonSections E T hT W x :=
  ((SheafOfModules.pullbackObjUnitToUnit (structureMap E T hT)).val.app W).hom.map_smul r x

/-- The inverse of the structure comparison on sections is a left inverse of it. -/
private theorem inv_structureComparisonSections (x) :
    ConcreteCategory.hom ((inv (SheafOfModules.pullbackObjUnitToUnit
      (structureMap E T hT))).val.app W) (structureComparisonSections E T hT W x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun k => k.val.app W)
    (IsIso.hom_inv_id (SheafOfModules.pullbackObjUnitToUnit (structureMap E T hT)))) x

/-- The inverse of the structure comparison on sections is a right inverse of it. -/
private theorem structureComparisonSections_inv (x) :
    structureComparisonSections E T hT W (ConcreteCategory.hom
      ((inv (SheafOfModules.pullbackObjUnitToUnit (structureMap E T hT))).val.app W) x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun k => k.val.app W)
    (IsIso.inv_hom_id (SheafOfModules.pullbackObjUnitToUnit (structureMap E T hT)))) x

/-- **The structure comparison on sections is bijective**, the comparison `ε^*𝒪_T ⟶ 𝒪` of
Stacks 070R being an isomorphism. -/
public theorem bijective_structureComparisonSections :
    Function.Bijective (structureComparisonSections E T hT W) :=
  ⟨Function.LeftInverse.injective (inv_structureComparisonSections E T hT W),
    Function.RightInverse.surjective (structureComparisonSections_inv E T hT W)⟩

/-- **The second reading of a section of `ε^*𝒪_T` over an étale chart as a regular function on
the chart scheme.**  Read the section as a global section of `g^*𝒪_T` through the Stacks 03DS
identification `AlgebraicGeometry.SmallEtale.chartSectionsIso` and then transport along the
comparison `g^*𝒪_T ≅ 𝒪_W` of `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`.

This is the reading in which
`AlgebraicGeometry.SmallEtale.exists_associatedModule_map_idealIota_app_eq_iff_mem` states the
chart identification; `AlgebraicGeometry.SmallEtale.structureComparisonSections` is the other
one, and the two are compared below only up to multiplication by a unit, which is all an ideal
needs. -/
public noncomputable def chartStructureSections :
    ToType (((associatedModule E T hT).obj (Scheme.unitModule T)).val.obj W) →
      ToType ((SheafOfModules.unit (structureSheaf E T hT)).val.obj W) :=
  fun x => ConcreteCategory.hom (Scheme.Modules.Hom.app
      (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤)
    (ConcreteCategory.hom (chartSectionsIso E T hT W (Scheme.unitModule T)).hom x)

/-- **The second reading is linear too.**  Both factors are maps of modules: the Stacks 03DS
identification is the map of abelian presheaves underlying
`AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsPresheaf`, and the comparison of
structure sheaves on the chart scheme is linear by
`AlgebraicGeometry.Scheme.Modules.Hom.app_smul`. -/
public theorem chartStructureSections_smul
    (r : ToType ((structureSheaf E T hT).obj.obj W))
    (x : ToType (((associatedModule E T hT).obj (Scheme.unitModule T)).val.obj W)) :
    chartStructureSections E T hT W (r • x) = r • chartStructureSections E T hT W x := by
  have hc : ConcreteCategory.hom ((associatedModuleIsoSectionsPresheaf E T hT
          (Scheme.unitModule T)).hom.app W) (r • x) =
      r • ConcreteCategory.hom ((associatedModuleIsoSectionsPresheaf E T hT
        (Scheme.unitModule T)).hom.app W) x :=
    map_smul _ r x
  refine Eq.trans (congrArg (ConcreteCategory.hom (Scheme.Modules.Hom.app
    (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤)) hc) ?_
  exact Scheme.Modules.Hom.app_smul _ r _

/-- **The second reading of the sections over an étale chart is bijective**, both factors being
components of isomorphisms. -/
public theorem bijective_chartStructureSections :
    Function.Bijective (chartStructureSections E T hT W) := by
  have hcl : ∀ y, ConcreteCategory.hom (chartSectionsIso E T hT W (Scheme.unitModule T)).inv
      (ConcreteCategory.hom (chartSectionsIso E T hT W (Scheme.unitModule T)).hom y) = y :=
    fun y => ConcreteCategory.congr_hom
      (chartSectionsIso E T hT W (Scheme.unitModule T)).hom_inv_id y
  have hcr : ∀ y, ConcreteCategory.hom (chartSectionsIso E T hT W (Scheme.unitModule T)).hom
      (ConcreteCategory.hom (chartSectionsIso E T hT W (Scheme.unitModule T)).inv y) = y :=
    fun y => ConcreteCategory.congr_hom
      (chartSectionsIso E T hT W (Scheme.unitModule T)).inv_hom_id y
  have hphom : Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤ ≫
      Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).inv ⊤ = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
  have hpinv : Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).inv ⊤ ≫
      Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤ = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
  have hpl : ∀ y, ConcreteCategory.hom (Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).inv ⊤)
      (ConcreteCategory.hom (Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤) y) = y :=
    fun y => ConcreteCategory.congr_hom hphom y
  have hpr : ∀ y, ConcreteCategory.hom (Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤)
      (ConcreteCategory.hom (Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).inv ⊤) y) = y :=
    fun y => ConcreteCategory.congr_hom hpinv y
  refine ⟨fun y z hyz => ?_, fun y => ⟨ConcreteCategory.hom
    (chartSectionsIso E T hT W (Scheme.unitModule T)).inv (ConcreteCategory.hom
      (Scheme.Modules.Hom.app (Scheme.Modules.pullbackUnitIso
        ((toOver E T hT).obj W.unop).hom).inv ⊤) y), ?_⟩⟩
  · exact ((hcl y).symm.trans (congrArg (ConcreteCategory.hom
      (chartSectionsIso E T hT W (Scheme.unitModule T)).inv)
      ((hpl _).symm.trans ((congrArg (ConcreteCategory.hom (Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).inv ⊤))
        hyz).trans (hpl _))))).trans (hcl z)
  · exact (congrArg (ConcreteCategory.hom (Scheme.Modules.Hom.app
      (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤))
      (hcr _)).trans (hpr y)

/-- **The comparison of the two readings of the sections of `ε^*𝒪_T` over an étale chart**: read
a regular function on the chart scheme back as a section of `ε^*𝒪_T` through the comparison of
structure sheaves, then read it forward again through the Stacks 03DS identification. -/
public noncomputable def chartStructureComparison :
    ToType ((SheafOfModules.unit (structureSheaf E T hT)).val.obj W) →
      ToType ((SheafOfModules.unit (structureSheaf E T hT)).val.obj W) :=
  fun a => chartStructureSections E T hT W (ConcreteCategory.hom
    ((inv (SheafOfModules.pullbackObjUnitToUnit (structureMap E T hT))).val.app W) a)

/-- The comparison of the two readings is linear. -/
public theorem chartStructureComparison_smul
    (r : ToType ((structureSheaf E T hT).obj.obj W))
    (a : ToType ((SheafOfModules.unit (structureSheaf E T hT)).val.obj W)) :
    chartStructureComparison E T hT W (r • a) =
      r • chartStructureComparison E T hT W a := by
  have h1 : ConcreteCategory.hom ((inv (SheafOfModules.pullbackObjUnitToUnit
          (structureMap E T hT))).val.app W) (r • a) =
      r • ConcreteCategory.hom ((inv (SheafOfModules.pullbackObjUnitToUnit
        (structureMap E T hT))).val.app W) a :=
    ((inv (SheafOfModules.pullbackObjUnitToUnit (structureMap E T hT))).val.app W).hom.map_smul r a
  refine Eq.trans (congrArg (chartStructureSections E T hT W) h1) ?_
  exact chartStructureSections_smul E T hT W r _

/-- The comparison of the two readings is bijective. -/
public theorem bijective_chartStructureComparison :
    Function.Bijective (chartStructureComparison E T hT W) := by
  have hinvbij : Function.Bijective (fun a => ConcreteCategory.hom
      ((inv (SheafOfModules.pullbackObjUnitToUnit (structureMap E T hT))).val.app W) a) :=
    ⟨Function.LeftInverse.injective (structureComparisonSections_inv E T hT W),
      Function.RightInverse.surjective (inv_structureComparisonSections E T hT W)⟩
  exact (bijective_chartStructureSections E T hT W).comp hinvbij

/-- **The two readings of the sections of `ε^*𝒪_T` over an étale chart differ by a unit**, so
they have the same preimage of every ideal.  The comparison of the two is a linear bijection of
the ring of regular functions on the chart scheme with itself, hence multiplication by a
unit. -/
public theorem mem_iff_chartStructureComparison_mem
    (P : Γ(((toOver E T hT).obj W.unop).left, ⊤) → Prop)
    (hP : ∀ r y : Γ(((toOver E T hT).obj W.unop).left, ⊤), P y → P (r * y))
    (a : ToType ((SheafOfModules.unit (structureSheaf E T hT)).val.obj W)) :
    P (chartStructureComparison E T hT W a) ↔ P a :=
  Stacks.Ideal.mem_iff_of_linear_bijective
    (R := Γ(((toOver E T hT).obj W.unop).left, ⊤)) (chartStructureComparison E T hT W)
    (fun r x => chartStructureComparison_smul E T hT W r x)
    (bijective_chartStructureComparison E T hT W) P hP a

/-- **The image of `ε^*(I ⊆ 𝒪_T) ⟶ 𝒪` on the sections over an arbitrary étale chart.**  Over an
étale chart with structure morphism `g : W ⟶ T`, a regular function on the chart scheme is in the
image of `AlgebraicGeometry.SmallEtale.idealAssociatedMap` exactly when it lies in the sections
over `W` of the inverse-image sheaf of ideals `I·𝒪_W` of Stacks 01WR.

Both sides mention only one reading of the sections: the left-hand side the comparison
`ε^*𝒪_T ≅ 𝒪` of Stacks 070R, the right-hand side nothing but `I` and `g`.  That is what makes
this the chartwise dictionary between a sheaf of ideals on the small étale site of `T` and a
Zariski sheaf of ideals of `T`, with no comparison left over.

`AlgebraicGeometry.SmallEtale.exists_associatedModule_map_idealIota_app_eq_iff_mem` computes the
image of `ε^*(I ⊆ 𝒪_T)` alone, in the *other* reading of the sections — through the Stacks 03DS
identification followed by `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`.  The two readings
are not identified here, and they need not be: each is a linear bijection of the ring of regular
functions on the chart scheme with itself, so they differ by multiplication by a unit, which
carries every ideal onto itself
(`AlgebraicGeometry.SmallEtale.mem_iff_chartStructureComparison_mem`). -/
public theorem exists_idealAssociatedMap_app_eq_iff_mem
    (a : ToType ((SheafOfModules.unit (structureSheaf E T hT)).val.obj W)) :
    (∃ m, ConcreteCategory.hom ((idealAssociatedMap E T hT I).val.app W) m = a) ↔
      a ∈ ((I.comap ((toOver E T hT).obj W.unop).hom).unitSubmodule).toSubmodule.obj (op ⊤) := by
  obtain ⟨hinj, hsurj⟩ := bijective_structureComparisonSections E T hT W
  obtain ⟨b, hb⟩ := hsurj a
  have hstep : (∃ m, ConcreteCategory.hom ((idealAssociatedMap E T hT I).val.app W) m = a) ↔
      (∃ m, ConcreteCategory.hom (associatedIdealSectionsMap E T hT I W) m = b) := by
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · obtain ⟨m, hm⟩ := hm
      exact ⟨m, hinj (((idealAssociatedMap_app_apply E T hT I W m).symm.trans hm).trans hb.symm)⟩
    · obtain ⟨m, hm⟩ := hm
      exact ⟨m, ((idealAssociatedMap_app_apply E T hT I W m).trans
        (congrArg (structureComparisonSections E T hT W) hm)).trans hb⟩
  have hinvb : ConcreteCategory.hom ((inv (SheafOfModules.pullbackObjUnitToUnit
      (structureMap E T hT))).val.app W) a = b := by
    rw [← hb]
    exact inv_structureComparisonSections E T hT W b
  have hcs : chartStructureComparison E T hT W a = chartStructureSections E T hT W b :=
    congrArg (chartStructureSections E T hT W) hinvb
  have h := mem_iff_chartStructureComparison_mem E T hT W
    (fun y => y ∈ ((I.comap ((toOver E T hT).obj W.unop).hom).unitSubmodule).toSubmodule.obj
      (op ⊤))
    (fun r _ hx => Submodule.smul_mem _ r hx) a
  rw [hcs] at h
  exact hstep.trans
    ((exists_associatedModule_map_idealIota_app_eq_iff_mem E T hT I W b).trans h)

end AlgebraicGeometry.SmallEtale

end
