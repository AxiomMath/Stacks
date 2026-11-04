module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCoversTop
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiQuasicoherentComponents
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceCounit
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceTransitionLocalization
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0D7M: quasi-coherence on the total Zariski site is cartesian plus quasi-coherent
components

Let `X` be a simplicial scheme and `F` a sheaf of `𝒪_X`-modules on its total Zariski site. This
file proves both directions of Stacks 0D7M: `F` is quasi-coherent in the sense of Stacks 03DL (6)
if and only if `F` is cartesian in the sense of Stacks 07TF (2) and every component module `F_n`
is a quasi-coherent `𝒪_{X_n}`-module.

## Main results

* `AlgebraicGeometry.SimplicialScheme.isCartesianModule_of_isQuasicoherentOnSite`: a
  quasi-coherent module on the total Zariski site is cartesian.
* `AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_of_isCartesianModule`: a cartesian
  module whose components are quasi-coherent is quasi-coherent on the total Zariski site.
* `AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_iff_isCartesianModule_and_components`:
  **Stacks 0D7M.**

## The two proofs

Both run on the slice of the total Zariski site at an object `(a, W)` and on the transition of
Stacks 09WF read there, `AlgebraicGeometry.SimplicialScheme.sliceComponentModuleTransition`,
which by `AlgebraicGeometry.SimplicialScheme.sliceComponentModuleTransition_over` is the
transition of `F` itself restricted to the open `(X φ)⁻¹W`.

*Forward.* Quasi-coherence of `F` gives, at the object `(a, ⊤)`, a covering on whose members `F`
has a global presentation; the covering is levelwise, so its members in degree `a` are opens of
`X_a` covering `X_a`, and a global presentation travels along an arbitrary arrow of the site. On
such an open the transition on the slice is invertible, by the colimit mechanism of
`isIso_sliceComponentModuleTransition_of_presentation`; so the transition of `F` is invertible
after restriction to the preimage of each member, and invertibility of a morphism of modules is
local. The quasi-coherence of the components is `isQuasicoherentOnSite_componentModule`.

*Converse.* Quasi-coherence of the component `F_a` gives a family of opens of `X_a` covering the
top on whose members `F_a` has a global presentation, hence a presentation. The family of objects
`(a, V_i)` covers the top of the total Zariski site, because every object of the total site
admits an arrow to `(a, ⊤)` — the simplex category has a map between any two objects. On each
slice at `(a, V_i)` the cartesian hypothesis makes every transition invertible, so the counit of
the slice adjunction is invertible by
`isIso_sliceCounit_of_isIso_transition`; therefore `F|_{(a,V_i)}` is the pullback to the slice of
a presented module, and a pullback of a presented module is presented because it preserves
colimits and carries the structure sheaf to the structure sheaf. Quasi-coherence is then the
clause of Stacks 03DN.

## Implementation notes

A global presentation becomes a `SheafOfModules.Presentation` by
`SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections`, whose hypothesis
is that the sections of every module on the site be small; on a slice that holds because the
slice has a terminal object (`SheafOfModules.small_sections_of_isTerminal`). This is why both
directions pass through a slice rather than through the total site itself, which has no terminal
object.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Topology.Simplicial
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable (X : SimplicialObject Scheme.{u})

/-- **Every object of the total Zariski site admits an arrow into one simplicial degree.** The
object `(a, ⊤)` receives an arrow from every `(b, V)`, because the simplex category has a
morphism between any two of its objects. -/
public theorem exists_hom_levelFunctor (a : SimplexCategoryᵒᵖ) (A : ZariskiOpen X) :
    ∃ T : Opens ((zariskiSpace X).obj a),
      Nonempty (A ⟶ (levelFunctor (zariskiSpace X) a).obj T) :=
  ⟨⊤, ⟨{ base := (SimplexCategory.const a.unop A.degree.unop 0).op, le := le_top }⟩⟩

/-- Sections of modules on a slice of the total Zariski site are small, because the slice has a
terminal object. -/
public theorem small_sections_sliceStructureRingSheaf (U : ZariskiOpen X)
    (N : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O).over U)) :
    Small.{u} N.sections :=
  SheafOfModules.small_sections_of_isTerminal Over.mkIdTerminal N

/-- Sections of modules on a slice of the open-set site of a simplicial degree are small, because
the slice has a terminal object. -/
public theorem small_sections_sliceDegreeRingSheaf {a : SimplexCategoryᵒᵖ}
    (W : Opens ↥(X.obj a)) (N : SheafOfModules.{u} (sliceDegreeRingSheaf X a W)) :
    Small.{u} N.sections :=
  SheafOfModules.small_sections_of_isTerminal Over.mkIdTerminal N

/-- **The forward direction of Stacks 0D7M, cartesian half.** A quasi-coherent module on the
total Zariski site of a simplicial scheme is cartesian in the sense of Stacks 07TF (2). -/
public theorem isCartesianModule_of_isQuasicoherentOnSite (F : Modules X)
    (hF : F.IsQuasicoherentOnSite) : IsCartesianModule X F := by
  classical
  intro n m φ
  obtain ⟨I, V, f, hsieve, hpres⟩ := hF.locally_hasGlobalPresentation (sliceObj X m ⊤)
  have hpt : ∀ x : ↥(X.obj m), ∃ U : Opens ↥(X.obj m),
      x ∈ U ∧ (F.over (sliceObj X m U)).HasGlobalPresentation := by
    intro x
    obtain ⟨U, hU, hmem, hxU⟩ :=
      (SimplicialOpen.mem_grothendieckTopology_iff _).1 hsieve x (by trivial)
    obtain ⟨i, A, hA⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hmem
    exact ⟨U, hxU, Stacks.SheafOfModules.hasGlobalPresentation_overMap F A (hpres i)⟩
  have hsup : (⨆ i : {U : Opens ↥(X.obj m) //
      (F.over (sliceObj X m U)).HasGlobalPresentation}, i.1) = ⊤ := by
    refine le_antisymm le_top fun x _ => ?_
    obtain ⟨U, hxU, hUp⟩ := hpt x
    exact Opens.mem_iSup.2 ⟨⟨U, hUp⟩, hxU⟩
  have hcov : (Opens.grothendieckTopology ↥(X.obj n)).CoversTop
      fun i : {U : Opens ↥(X.obj m) //
        (F.over (sliceObj X m U)).HasGlobalPresentation} => slicePreimage X i.1 φ := by
    refine (Opens.coversTop_iff _ _).2 ?_
    refine Eq.trans (Opens.map_iSup _ _).symm ?_
    rw [hsup, Opens.map_top]
  refine isIso_componentModuleTransition_of_coversTop X φ F
    (fun i : {U : Opens ↥(X.obj m) //
      (F.over (sliceObj X m U)).HasGlobalPresentation} => i.1) hcov fun i => ?_
  have : ∀ N : SheafOfModules.{u} (sliceStructureRingSheaf X m i.1), Small.{u} N.sections :=
    small_sections_sliceStructureRingSheaf X (sliceObj X m i.1)
  exact isIso_sliceComponentModuleTransition_of_presentation X i.1 φ _
    (SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections i.2).some

/-- **The converse direction of Stacks 0D7M.** A cartesian module on the total Zariski site of a
simplicial scheme all of whose component modules are quasi-coherent is quasi-coherent on the
total Zariski site. -/
public theorem isQuasicoherentOnSite_of_isCartesianModule (F : Modules X)
    (hcart : IsCartesianModule X F)
    (hcomp : ∀ k : SimplexCategoryᵒᵖ,
      ((componentModule X k).obj F).IsQuasicoherentOnSite) :
    F.IsQuasicoherentOnSite := by
  classical
  obtain ⟨I, V, hV, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation
      ((componentModule X (op (SimplexCategory.mk 0))).obj F)).1
      (hcomp (op (SimplexCategory.mk 0)))
  have hcont : (levelFunctor (zariskiSpace X) (op (SimplexCategory.mk 0))).IsContinuous
      (Opens.grothendieckTopology ↥(X.obj (op (SimplexCategory.mk 0))))
      ((zariskiRingedTopos X).J) :=
    levelFunctor_isContinuous_opens X (op (SimplexCategory.mk 0))
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation F
    (W := fun i => sliceObj X (op (SimplexCategory.mk 0)) (V i))
    (Stacks.CategoryTheory.coversTop_map_of_forall_exists_hom
      (levelFunctor (zariskiSpace X) (op (SimplexCategory.mk 0)))
      (exists_hom_levelFunctor X (op (SimplexCategory.mk 0))) hV) fun i => ?_
  have : ∀ N : SheafOfModules.{u}
      (sliceDegreeRingSheaf X (op (SimplexCategory.mk 0)) (V i)), Small.{u} N.sections :=
    small_sections_sliceDegreeRingSheaf X (V i)
  obtain ⟨P⟩ :=
    SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections (hP i)
  have hε : IsIso ((sliceModulePullbackAdj X (op (SimplexCategory.mk 0)) (V i)).counit.app
      (F.over (sliceObj X (op (SimplexCategory.mk 0)) (V i)))) :=
    isIso_sliceCounit_of_isIso_transition X (V i) _ P fun c ψ => by
      have hov : IsIso ((componentModuleTransition X ψ F).over (slicePreimage X (V i) ψ)) :=
        Iso.isIso_hom ((SheafOfModules.overFunctor.{u} ((X.obj c).ringCatSheaf)
          (slicePreimage X (V i) ψ)).mapIso (@asIso _ _ _ _ _ (hcart ψ)))
      exact (isIso_sliceComponentModuleTransition_over_iff X (V i) ψ F).2 hov
  have η : SheafOfModules.unit
        (sliceStructureRingSheaf X (op (SimplexCategory.mk 0)) (V i)) ≅
      (sliceModulePullback X (op (SimplexCategory.mk 0)) (V i)).obj
        (SheafOfModules.unit
          (sliceDegreeRingSheaf X (op (SimplexCategory.mk 0)) (V i))) :=
    (asIso (SheafOfModules.pullbackObjUnitToUnit
      (SheafOfModules.overComparison
        (componentStructureHom X (op (SimplexCategory.mk 0))) (V i)))).symm
  exact (SheafOfModules.Presentation.ofIsIso
    ((sliceModulePullbackAdj X (op (SimplexCategory.mk 0)) (V i)).counit.app
      (F.over (sliceObj X (op (SimplexCategory.mk 0)) (V i))))
    (P.map (sliceModulePullback X (op (SimplexCategory.mk 0)) (V i)) η)).hasGlobalPresentation

/-- **Stacks 0D7M for the total Zariski site of a simplicial scheme.** A sheaf of `𝒪_X`-modules
on the total Zariski site is quasi-coherent in the sense of Stacks 03DL (6) if and only if it is
cartesian in the sense of Stacks 07TF (2) and every one of its component modules `F_n` is a
quasi-coherent `𝒪_{X_n}`-module. -/
@[stacks 0D7M "for the total Zariski site of a simplicial scheme, which is the site of 09VL; \
the cartesian condition is `AlgebraicGeometry.SimplicialScheme.IsCartesianModule`, 07TF (2) at \
the transition of 09WF, and quasi-coherence of the components is 03DL (6) over the structure \
sheaf of the degree, with the component functors of `ZariskiModulePushforward`"]
public theorem isQuasicoherentOnSite_iff_isCartesianModule_and_components (F : Modules X) :
    F.IsQuasicoherentOnSite ↔
      IsCartesianModule X F ∧
        ∀ k : SimplexCategoryᵒᵖ,
          ((componentModule X k).obj F).IsQuasicoherentOnSite :=
  ⟨fun hF => ⟨isCartesianModule_of_isQuasicoherentOnSite X F hF,
      fun k => isQuasicoherentOnSite_componentModule X k F hF⟩,
    fun h => isQuasicoherentOnSite_of_isCartesianModule X F h.1 h.2⟩

end AlgebraicGeometry.SimplicialScheme

end
