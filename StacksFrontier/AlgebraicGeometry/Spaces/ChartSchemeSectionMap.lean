module

public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectivityLocusChartScheme
public import StacksFrontier.AlgebraicGeometry.Modules.CokernelSupportNonvanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward

/-!
# Maps out of the structure sheaf of a represented space, read on the scheme

Let `U` be a scheme of the big fppf site, with underlying scheme `W`, and let `𝓖` be a
quasi-coherent module on the algebraic space `h_U`. A map `ψ : 𝒪_{h_U} ⟶ 𝓖` is carried by the
inverse of the equivalence `QCoh(W) ≌ QCoh(h_U)` of Stacks 03DX to a map of quasi-coherent
`𝒪_W`-modules, `AlgebraicGeometry.Space.chartSectionMap`. This passage is additive and functorial.
If `𝓖` corresponds to an invertible `𝒪_W`-module, then a point `x` of `W` at which the map named by
an element of the span of a family of global sections is surjective is a point at which the map
named by one member of the family is surjective.

## Main definitions

* `AlgebraicGeometry.Space.chartUnitQcoh`: `𝒪_{h_U}` as a quasi-coherent module.
* `AlgebraicGeometry.Space.chartSectionMap`: the map of `𝒪_W`-modules corresponding to a map
  `𝒪_{h_U} ⟶ 𝓖`.
* `AlgebraicGeometry.Space.chartSchemeUnitIso`: `𝒪_W` is the module corresponding to `𝒪_{h_U}`.

## Main results

* `AlgebraicGeometry.Space.exists_notMem_supp_cokernel_of_mem_span`: **surjectivity at a point
  passes from an element of a span to a generator.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Represented

variable (U : BigFppfOver B S hS)

/-- The equivalence `QCoh(W) ≌ QCoh(h_U)` of Stacks 03DX is additive. -/
instance additive_representedQuasicoherentSchemeEquivalence_functor :
    (representedQuasicoherentSchemeEquivalence B S hS U).functor.Additive where
  map_add {_ _ f g} := ObjectProperty.hom_ext _
    ((representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)).map_add
      (f := f.hom) (g := g.hom))

/-- `𝒪_{h_U}`, as a quasi-coherent module on the represented space. -/
def chartUnitQcoh :
    QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  ⟨SheafOfModules.unit _, SheafOfModules.isQuasicoherentOnSite_unit _⟩

variable {U}

/-- The map of quasi-coherent `𝒪_W`-modules corresponding to a map `ψ` between quasi-coherent
modules on `h_U`: the image of `ψ` under the inverse of the equivalence of Stacks 03DX. -/
def chartSectionMap {𝓐 𝓖 : QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)} (ψ : 𝓐.obj ⟶ 𝓖.obj) :
    ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj 𝓐).obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj 𝓖).obj :=
  ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.map
    (ObjectProperty.homMk ψ : 𝓐 ⟶ 𝓖)).hom

/-- `chartSectionMap` is additive: the map corresponding to `ψ + ψ'` is the sum of the maps
corresponding to `ψ` and `ψ'`. -/
theorem chartSectionMap_add {𝓐 𝓖 : QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)} (ψ ψ' : 𝓐.obj ⟶ 𝓖.obj) :
    chartSectionMap (ψ + ψ') = chartSectionMap ψ + chartSectionMap ψ' :=
  congrArg (fun k => k.hom)
    ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.map_add
      (f := (ObjectProperty.homMk ψ : 𝓐 ⟶ 𝓖)) (g := ObjectProperty.homMk ψ'))

/-- The map of `𝒪_W`-modules corresponding to the zero map is zero. -/
theorem chartSectionMap_zero {𝓐 𝓖 : QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)} :
    chartSectionMap (0 : 𝓐.obj ⟶ 𝓖.obj) = 0 :=
  congrArg (fun k => k.hom)
    ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.map_zero 𝓐 𝓖)

/-- `chartSectionMap` is functorial: the map corresponding to a composite `a ≫ b` is the
composite of the maps corresponding to `a` and `b`. -/
theorem chartSectionMap_comp {𝓐 𝓑 𝓖 : QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)} (a : 𝓐.obj ⟶ 𝓑.obj) (b : 𝓑.obj ⟶ 𝓖.obj) :
    chartSectionMap (a ≫ b) = chartSectionMap a ≫ chartSectionMap b :=
  congrArg (fun k => k.hom)
    ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.map_comp
      (ObjectProperty.homMk a : 𝓐 ⟶ 𝓑) (ObjectProperty.homMk b : 𝓑 ⟶ 𝓖))

/-- Every map of quasi-coherent `𝒪_W`-modules between the modules corresponding to `𝓐` and `𝓖`
is the map corresponding to a map `𝓐 ⟶ 𝓖`: the inverse of an equivalence is full. -/
theorem exists_chartSectionMap_eq {𝓐 𝓖 : QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)}
    (φ : ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj 𝓐).obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj 𝓖).obj) :
    ∃ ψ : 𝓐.obj ⟶ 𝓖.obj, chartSectionMap ψ = φ :=
  ⟨((representedQuasicoherentSchemeEquivalence B S hS U).inverse.preimage
      (ObjectProperty.homMk φ)).hom,
    congrArg (fun k => k.hom)
      ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.map_preimage
        (ObjectProperty.homMk φ))⟩

variable (U) in
/-- `𝒪_W` is the quasi-coherent `𝒪_W`-module corresponding to `𝒪_{h_U}`. -/
def chartSchemeUnitIso : Stacks.Ample.unitModule ((BigFppfOver.toScheme B S hS).obj U) ≅
    ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj (chartUnitQcoh U)).obj :=
  (ObjectProperty.ι _).mapIso
    ((representedQuasicoherentSchemeEquivalence B S hS U).unitIso.app
        ⟨SheafOfModules.unit _, inferInstance⟩ ≪≫
      (representedQuasicoherentSchemeEquivalence B S hS U).inverse.mapIso
        (ObjectProperty.isoMk _ (Y := chartUnitQcoh U)
          (representedAssociatedModuleObjUnitIso B S hS U (isAlgebraicSpace_yoneda B S hS U))))

/-- The map out of the structure sheaf named by a scalar multiple of a global section is the
precomposition with multiplication by the scalar. -/
theorem unitHomEquiv_symm_smul {G : Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)}
    (a : RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O).obj)
    (t : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)).obj G) :
    (SheafOfModules.unitHomEquiv G).symm (a • t) =
      Stacks.Cohomology.SiteModules.unitEnd _ a ≫ (SheafOfModules.unitHomEquiv G).symm t :=
  (Equiv.symm_apply_eq _).mpr
    ((congrArg (a • ·) ((SheafOfModules.unitHomEquiv G).apply_symm_apply t)).symm.trans
      (Stacks.Cohomology.SiteModules.unitHomEquiv_unitEnd_comp _ a _).symm)

/-- The map out of the structure sheaf named by the zero section is zero. -/
theorem unitHomEquiv_symm_zero (G : Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) :
    (SheafOfModules.unitHomEquiv G).symm
      (0 : (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O)).obj G) = 0 :=
  (Equiv.symm_apply_eq _).mpr (Subtype.ext (funext fun _ => rfl))

/-- **Surjectivity at a point passes from an element of a span to a generator.** Let `𝓖` be a
quasi-coherent module on `h_U` whose corresponding `𝒪_W`-module is invertible, let `ps` be a
family of global sections of `𝓖` and `t` an element of the `Γ(h_U, 𝒪)`-span of the family. If
the map of `𝒪_W`-modules corresponding to the map `𝒪_{h_U} ⟶ 𝓖` named by `t` is surjective at a
point `x` of `W`, so is the one named by some member of the family. -/
theorem exists_notMem_supp_cokernel_of_mem_span (𝓖 : QuasicoherentSheaves.{u, u} B S hS
      (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    [Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj 𝓖).obj]
    (x : (BigFppfOver.toScheme B S hS).obj U) {ι : Type*}
    (ps : ι → (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)).obj 𝓖.obj)
    (t : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)).obj 𝓖.obj)
    (ht : t ∈ Submodule.span (RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O).obj) (Set.range ps))
    (hx : x ∉ _root_.SheafOfModules.supp (cokernel (chartSectionMap (𝓐 := chartUnitQcoh U)
      (𝓖 := 𝓖) ((SheafOfModules.unitHomEquiv 𝓖.obj).symm t)))) :
    ∃ i, x ∉ _root_.SheafOfModules.supp (cokernel (chartSectionMap (𝓐 := chartUnitQcoh U)
      (𝓖 := 𝓖) ((SheafOfModules.unitHomEquiv 𝓖.obj).symm (ps i)))) := by
  have hcongr : ∀ {φ φ' : ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj
      (chartUnitQcoh U)).obj ⟶ ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj
        𝓖).obj}, φ = φ' → x ∉ _root_.SheafOfModules.supp (cokernel φ) →
          x ∉ _root_.SheafOfModules.supp (cokernel φ') := fun h hx => h ▸ hx
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨i, hx⟩
  | zero =>
    exfalso
    exact (hcongr ((congrArg chartSectionMap (unitHomEquiv_symm_zero 𝓖.obj)).trans
        chartSectionMap_zero) hx)
      (Stacks.CokernelSupport.mem_supp_cokernel_zero (chartSchemeUnitIso U) x)
  | add y z _ _ hy hz =>
    have h := hcongr ((congrArg chartSectionMap
      (Stacks.Cohomology.SiteModules.unitHomEquiv_symm_add _ y z)).trans
        (chartSectionMap_add _ _)) hx
    rcases Stacks.CokernelSupport.notMem_supp_cokernel_of_add (chartSchemeUnitIso U) _ _ x h with
      h | h
    · exact hy h
    · exact hz h
  | smul a y _ hy =>
    have h := hcongr ((congrArg chartSectionMap (unitHomEquiv_symm_smul a y)).trans
      (chartSectionMap_comp (𝓑 := chartUnitQcoh U) _ _)) hx
    exact hy (Stacks.CokernelSupport.notMem_supp_cokernel_of_comp _ _ x h)

end Represented

end AlgebraicGeometry.Space

end
