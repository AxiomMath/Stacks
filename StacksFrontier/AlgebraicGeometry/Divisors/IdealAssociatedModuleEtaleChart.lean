module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSectionsModule
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSubmodulePullbackChartSections

/-!
# The sections of `ε^*I ⊆ 𝒪` over an arbitrary étale chart of a scheme

Let `T` be a scheme contained in a big étale site `E` and let `I ⊆ 𝒪_T` be a quasi-coherent
sheaf of ideals.  `AlgebraicGeometry.SmallEtale.associatedModule` is the functor `ε^*` of
Stacks 03DU (4) at `τ = étale`, and it carries the inclusion `I ⊆ 𝒪_T` to a map of `𝒪`-modules
on the small étale site of `T`.

`StacksFrontier/AlgebraicGeometry/Divisors/IdealSubmoduleAssociatedModule.lean` computes the image
of that map on sections **over the charts cut out by the Zariski opens of `T`**.  This file does
it **over an arbitrary étale chart**: over a chart with structure morphism `g : W ⟶ T` the image
is, read through the Stacks 03DS identification of the sections of `ε^*` with global sections of
a pullback, exactly the sections over `W` of the inverse-image sheaf of ideals `I·𝒪_W` of
Stacks 01WR.

## The two inputs

* **Naturality in the module** of the Stacks 03DS identification:
  `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality_module`.  It says that
  reading a section of `ε^*𝓕` over a chart as a global section of the pullback of `𝓕` to the
  chart scheme commutes with a morphism of quasi-coherent modules.  Applied to the inclusion
  `I ⊆ 𝒪_T` it transports the image of `ε^*(I ⊆ 𝒪_T)` on sections over the chart to the image of
  `g^*(I ⊆ 𝒪_T)` on global sections of the chart scheme.  Nothing about the construction of `ε^*`
  by sheafification is used: both identifications are isomorphisms of presheaves, so the square
  alone determines the image.
* **The image of `g^*(I ⊆ 𝒪_T)` on sections**, which is
  `Stacks.ClosedSubscheme.exists_pullbackIdealMap_app_eq_iff_mem` of
  `StacksFrontier/AlgebraicGeometry/Divisors/IdealSubmodulePullbackChartSections.lean`.  Its
  flatness hypothesis is discharged at a chart: the structure morphism of an object of the small
  étale site is étale, hence flat.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_associatedModule_map_idealIota_app_eq_iff`: the transport.
  A section of `ε^*𝒪_T` over an étale chart is in the image of `ε^*(I ⊆ 𝒪_T)` exactly when its
  reading as a global section of `g^*𝒪_T` is in the image of `g^*(I ⊆ 𝒪_T)`.
* `AlgebraicGeometry.SmallEtale.exists_associatedModule_map_idealIota_app_eq_iff_mem`: **the
  chart identification.**  The same, with the right-hand side the sections over the chart scheme
  of the inverse-image sheaf of ideals `I·𝒪_W`, which is affine-local data of `I` and of `g`
  alone.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), part (4), the associated
  module.
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS), the pullback-sections
  presheaf.
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S), the identification of
  the two.
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR), the inverse image of a
  sheaf of ideals.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (E : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : E.Contains T) (I : T.IdealSheafData)
  (W : (SmallEtale E T hT)ᵒᵖ)

/-- The Stacks 03DS reading of a section of `ε^*𝓕` over an étale chart as a global section of the
pullback of `𝓕` to the chart scheme, as an isomorphism of abelian groups: the component of
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso` at the chart. -/
public noncomputable abbrev chartSectionsIso (F : T.Modules) [F.IsQuasicoherent] :
    ((associatedModule E T hT).obj F).val.presheaf.obj W ≅
      ((toOver E T hT).op ⋙ quasiCoherentPresheafFunctor T F).obj W :=
  (associatedModulePresheafIso E T hT F).app W

/-- The map on sections over an étale chart induced by `ε^*` of the inclusion of a sheaf of
ideals into the structure sheaf. -/
public noncomputable abbrev associatedIdealSectionsMap :
    ((associatedModule E T hT).obj I.unitSubmodule.toSheafOfModules).val.presheaf.obj W ⟶
      ((associatedModule E T hT).obj (Scheme.unitModule T)).val.presheaf.obj W :=
  ((PresheafOfModules.toPresheaf (structureSheaf E T hT).obj).map
    ((SheafOfModules.forget (structureSheaf E T hT)).map
      ((associatedModule E T hT).map (Stacks.ClosedSubscheme.idealIota I)))).app W

/-- **The image of `ε^*(I ⊆ 𝒪_T)` on the sections over an étale chart, transported to the chart
scheme.**  A section of `ε^*𝒪_T` over the chart is in that image exactly when its reading as a
global section of `g^*𝒪_T`, under the Stacks 03DS identification
`AlgebraicGeometry.SmallEtale.chartSectionsIso`, is in the image of `g^*(I ⊆ 𝒪_T)`. -/
public theorem exists_associatedModule_map_idealIota_app_eq_iff
    (a : ToType (((associatedModule E T hT).obj (Scheme.unitModule T)).val.presheaf.obj W)) :
    (∃ m, ConcreteCategory.hom (associatedIdealSectionsMap E T hT I W) m = a) ↔
      ∃ n, ConcreteCategory.hom (Scheme.Modules.Hom.app ((Scheme.Modules.pullback
            ((toOver E T hT).obj W.unop).hom).map (Stacks.ClosedSubscheme.idealIota I)) ⊤) n =
        ConcreteCategory.hom
          (chartSectionsIso E T hT W (Scheme.unitModule T)).hom a := by
  have hsq : ∀ m, ConcreteCategory.hom
        (chartSectionsIso E T hT W (Scheme.unitModule T)).hom
        (ConcreteCategory.hom (associatedIdealSectionsMap E T hT I W) m) =
      ConcreteCategory.hom (Scheme.Modules.Hom.app ((Scheme.Modules.pullback
          ((toOver E T hT).obj W.unop).hom).map (Stacks.ClosedSubscheme.idealIota I)) ⊤)
        (ConcreteCategory.hom
          (chartSectionsIso E T hT W I.unitSubmodule.toSheafOfModules).hom m) := fun m =>
    ConcreteCategory.congr_hom
      (associatedModulePresheafIso_hom_naturality_module E T hT
        (Stacks.ClosedSubscheme.idealIota I) W) m
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨_, (hsq m).symm⟩
  · rintro ⟨n, hn⟩
    have hinj : ∀ x, ConcreteCategory.hom
          (chartSectionsIso E T hT W (Scheme.unitModule T)).inv
          (ConcreteCategory.hom (chartSectionsIso E T hT W (Scheme.unitModule T)).hom x) = x :=
      fun x => ConcreteCategory.congr_hom
        (chartSectionsIso E T hT W (Scheme.unitModule T)).hom_inv_id x
    have hmn : ∀ x, ConcreteCategory.hom
          (chartSectionsIso E T hT W I.unitSubmodule.toSheafOfModules).hom
          (ConcreteCategory.hom
            (chartSectionsIso E T hT W I.unitSubmodule.toSheafOfModules).inv x) = x :=
      fun x => ConcreteCategory.congr_hom
        (chartSectionsIso E T hT W I.unitSubmodule.toSheafOfModules).inv_hom_id x
    refine ⟨ConcreteCategory.hom
      (chartSectionsIso E T hT W I.unitSubmodule.toSheafOfModules).inv n, ?_⟩
    have hboth := ((hsq _).trans (congrArg (ConcreteCategory.hom (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullback ((toOver E T hT).obj W.unop).hom).map
        (Stacks.ClosedSubscheme.idealIota I)) ⊤)) (hmn n))).trans hn
    exact (hinj _).symm.trans ((congrArg (ConcreteCategory.hom
      (chartSectionsIso E T hT W (Scheme.unitModule T)).inv) hboth).trans (hinj a))

/-- **The chart identification.**  Over an étale chart of `T` with structure morphism
`g : W ⟶ T`, a section of `ε^*𝒪_T` is in the image of `ε^*(I ⊆ 𝒪_T)` exactly when its reading as
a global regular function on the chart scheme lies in the sections over `W` of the inverse-image
sheaf of ideals `I·𝒪_W` of Stacks 01WR. -/
public theorem exists_associatedModule_map_idealIota_app_eq_iff_mem
    (a : ToType (((associatedModule E T hT).obj (Scheme.unitModule T)).val.presheaf.obj W)) :
    (∃ m, ConcreteCategory.hom (associatedIdealSectionsMap E T hT I W) m = a) ↔
      ConcreteCategory.hom (Scheme.Modules.Hom.app
          (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤)
        (ConcreteCategory.hom
          (chartSectionsIso E T hT W (Scheme.unitModule T)).hom a) ∈
        ((I.comap ((toOver E T hT).obj W.unop).hom).unitSubmodule).toSubmodule.obj (op ⊤) := by
  have hetale : Etale ((toOver E T hT).obj W.unop).hom :=
    etale_structureMorphism E T hT W.unop
  have hflat : AlgebraicGeometry.Flat ((toOver E T hT).obj W.unop).hom := inferInstance
  rw [exists_associatedModule_map_idealIota_app_eq_iff E T hT I W a,
    ← Stacks.ClosedSubscheme.exists_pullbackIdealMap_app_eq_iff_mem
      ((toOver E T hT).obj W.unop).hom I ⊤ _]
  have hfac : ∀ n, ConcreteCategory.hom (Scheme.Modules.Hom.app
        (Stacks.ClosedSubscheme.pullbackIdealMap ((toOver E T hT).obj W.unop).hom I) ⊤) n =
      ConcreteCategory.hom (Scheme.Modules.Hom.app
          (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤)
        (ConcreteCategory.hom (Scheme.Modules.Hom.app ((Scheme.Modules.pullback
          ((toOver E T hT).obj W.unop).hom).map (Stacks.ClosedSubscheme.idealIota I)) ⊤) n) :=
    fun n => ConcreteCategory.congr_hom
      (Scheme.Modules.Hom.comp_app ((Scheme.Modules.pullback
          ((toOver E T hT).obj W.unop).hom).map (Stacks.ClosedSubscheme.idealIota I))
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom) n
  have happ : Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤ ≫
      Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).inv ⊤ = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
  have hinj : ∀ x, ConcreteCategory.hom (Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).inv ⊤)
      (ConcreteCategory.hom (Scheme.Modules.Hom.app
        (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤) x) = x :=
    fun x => ConcreteCategory.congr_hom happ x
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (hfac n).trans (congrArg (ConcreteCategory.hom (Scheme.Modules.Hom.app
      (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).hom ⊤)) hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (hinj _).symm.trans ((congrArg (ConcreteCategory.hom (Scheme.Modules.Hom.app
      (Scheme.Modules.pullbackUnitIso ((toOver E T hT).obj W.unop).hom).inv ⊤))
      ((hfac n).symm.trans hn)).trans (hinj _))⟩

end AlgebraicGeometry.SmallEtale

end
