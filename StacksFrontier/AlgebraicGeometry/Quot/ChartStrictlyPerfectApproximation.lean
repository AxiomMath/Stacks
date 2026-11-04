module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverTerminal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSliceQuasicoherentGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverTerminal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives

/-!
# Strictly perfect approximations on the chart of an algebraic space

Let `X` be an algebraic space and `V` an étale chart of `X`, that is an object of its small étale
site.  Pseudo-coherence of a complex `E` of `𝒪_X`-modules (Stacks 08FT) supplies strictly perfect
complexes `P` of modules on the *slice* of the small étale site of `X` at `V`, with maps
`P ⟶ E|_V` which are approximations: isomorphisms on cohomology above some degree `m` and
surjective in degree `m`.  To pull such an approximation back along an arbitrary morphism of
schemes into `V` it has to be read as a complex of modules on the algebraic space represented by
`V` itself.  This file does that.

The slice at `V` is identified with the slice at the identity chart of the represented algebraic
space by the slice comparison of Stacks 04M0, and restriction to the slice at the identity chart,
a final object, is an equivalence; both are exact and carry the structure sheaf to the structure
sheaf, so strict perfectness and the two cohomological conditions survive, and the restriction
`E|_V` becomes the pullback of `E` along the chart (Stacks 03LW).

## Main definitions

* `AlgebraicGeometry.Space.postcompChartIdChartHom`: the identity chart of the space represented
  by an étale chart `V`, composed with the chart, maps to `V`.

## Main results

* `AlgebraicGeometry.RingedSite.exists_approximation_of_over_terminal`: an approximation over the
  slice at a final object is one over the site.
* `AlgebraicGeometry.Space.exists_approximation_over_postcomp`: an approximation over the slice
  at an étale chart of `X` gives one, for the étale pullback, over the slice at a chart of an
  étale `Y ⟶ X` mapping to it.
* `AlgebraicGeometry.Space.exists_chartApproximation`: **an approximation over the slice at an
  étale chart `V` of `X` gives one of the étale pullback of `E` to the algebraic space `V`.**

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck


namespace AlgebraicGeometry.RingedSite

universe u v w

attribute [local instance] ovFunctorLimits ovFunctorColimits

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- An exact functor carries an approximation `α` to one, once the target is rewritten along an
isomorphism `c`. -/
private theorem approximation_map_comp_iso {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P Q : CochainComplex C ℤ} {R : CochainComplex D ℤ} (α : P ⟶ Q)
    (c : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ≅ R) (m : ℤ)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ c.hom) j)) ∧
      Epi (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ c.hom) m) :=
  ⟨fun j hj => isIso_homologyMap_comp_iso _ c j
    (Stacks.PseudoCoherence.DerivedCharacterization.isIso_homologyMap_mapHomologicalComplex
      F α j (hiso j hj)),
    epi_homologyMap_comp_iso _ c m
      (Stacks.PseudoCoherence.DerivedCharacterization.epi_homologyMap_mapHomologicalComplex
        F α m hepi)⟩

/-- **An approximation over the slice at a final object is an approximation over the site.**
If `T` is a final object of the site and `β : P ⟶ E|_T` is a map from a strictly perfect complex
of `𝒪|_T`-modules which is an isomorphism on cohomology in every degree `> m` and surjective in
degree `m`, then reading it back along the equivalence
`Stacks.SheafOfModules.overTerminalEquivalence` gives a strictly perfect complex of `𝒪`-modules
with such a map to `E`. -/
theorem exists_approximation_of_over_terminal {T : X.C} (hT : IsTerminal T)
    (E : CochainComplex (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ)
    (P : CochainComplex (_root_.SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over T)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over T) P)
    (β : P ⟶ X.restrictComplex E T)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j))
    (hepi : Epi (HomologicalComplex.homologyMap β m)) :
    ∃ P' : CochainComplex (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P' ∧
        ∃ γ : P' ⟶ E, (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap γ j)) ∧
          Epi (HomologicalComplex.homologyMap γ m) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let e := Stacks.SheafOfModules.overTerminalEquivalence R hT
  let G := e.inverse
  have : e.functor.Additive := inferInstanceAs (_root_.SheafOfModules.overFunctor R T).Additive
  have : G.Additive := e.inverse_additive
  let c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (X.restrictComplex E T) ≅ E :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app E ≪≫
      (NatIso.mapHomologicalComplex e.unitIso.symm (ComplexShape.up ℤ)).app E ≪≫
      (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app E
  let uG : G.obj (_root_.SheafOfModules.unit (R.over T)) ≅ _root_.SheafOfModules.unit R :=
    (e.unitIso.app (_root_.SheafOfModules.unit R)).symm
  refine ⟨(G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    _root_.SheafOfModules.isStrictlyPerfect_map G uG hP,
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map β ≫ c.hom,
    approximation_map_comp_iso G β c m hiso hepi⟩

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  RingedSite.ovFunctorLimits RingedSite.ovFunctorColimits smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective RingedSite.overMapLimits RingedSite.overMapColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An approximation over the slice at an étale chart of `X` gives one for the étale pullback
over the slice at a chart of `Y` mapping to it.**  For an étale `f : Y ⟶ X`, a chart `V` of `Y`
and an arrow `h` from the composite chart `f ∘ V` to a chart `Z` of `X`, a strictly perfect
approximation of `K|_Z` above degree `m` is restricted along `h` and carried across the slice
equivalence of Stacks 04M0 to a strictly perfect approximation of `(f^*K)|_V` above degree `m`.
-/
theorem exists_approximation_over_postcomp {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (m : ℤ)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) (Z : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (h : (smallEtaleRingedSitePostcomp B S hS f hf).obj V ⟶ Z)
    (P : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).over Z)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).over Z) P)
    (α : P ⟶ (smallEtaleRingedSite B S hS X.1 X.2).restrictComplex K Z)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    ∃ P' : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V) P' ∧
        ∃ β : P' ⟶ (smallEtaleRingedSite B S hS Y.1 Y.2).restrictComplex
          (((etaleModulePullback B S hS f hf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) V,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
            Epi (HomologicalComplex.homologyMap β m) := by
  let pull := etaleModulePullback B S hS f hf
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  let M := SheafOfModules.overMap.{u} R h
  let F := (postcompSliceModuleEquivalence B S hS f hf V).functor
  let c₁ : (M.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((smallEtaleRingedSite B S hS X.1 X.2).restrictComplex K Z) ≅
      (smallEtaleRingedSite B S hS X.1 X.2).restrictComplex K
        ((smallEtaleRingedSitePostcomp B S hS f hf).obj V) :=
    (Stacks.SheafOfModules.overFunctorMapComplexIso.{u} R h).app K
  let c₂ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((smallEtaleRingedSite B S hS X.1 X.2).restrictComplex K
          ((smallEtaleRingedSitePostcomp B S hS f hf).obj V)) ≅
      (smallEtaleRingedSite B S hS Y.1 Y.2).restrictComplex
        ((pull.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) V :=
    (Functor.mapHomologicalComplexCompIso (overEtaleModulePullbackIso B S hS f hf V)
        (ComplexShape.up ℤ)).app K ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app K).symm
  let β : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((M.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      (smallEtaleRingedSite B S hS Y.1 Y.2).restrictComplex
        ((pull.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) V :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((M.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ c₁.hom) ≫ c₂.hom
  have h₁ := RingedSite.approximation_map_comp_iso M α c₁ m hiso hepi
  exact ⟨_, SheafOfModules.isStrictlyPerfect_map F (postcompSliceUnitIsoFunctor B S hS f hf V)
    (Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general R h hP), β,
    RingedSite.approximation_map_comp_iso F _ c₂ m h₁.1 h₁.2⟩

/-- The identity chart of the space represented by an étale chart `V`, composed with the chart
map, is `V` again. -/
def postcompChartIdChartHom {X : AlgebraicSpaces B S hS} (V : SmallEtale B S hS X.1) :
    (smallEtaleRingedSitePostcomp B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).obj (chartIdChart B S hS X V) ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _) (by
    change yoneda.map (𝟙 _) ≫ V.1.hom = (chartIdChart B S hS X V).1.hom ≫ V.1.hom
    have h : (chartIdChart B S hS X V).1.hom = 𝟙 _ := rfl
    rw [h, CategoryTheory.Functor.map_id]
    rfl))

/-- **An approximation over the slice at an étale chart is an approximation of the pullback to
the chart.**  Let `V` be an étale chart of an algebraic space `X` and `K` a complex of
`𝒪_X`-modules.  A strictly perfect complex over the slice of the small étale site of `X` at `V`
with a map to `K|_V` which is an isomorphism on cohomology above degree `m` and surjective in
degree `m` gives a strictly perfect complex of modules on the algebraic space `V` itself with
such a map to the pullback of `K` along the chart. -/
theorem exists_chartApproximation {X : AlgebraicSpaces B S hS}
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (m : ℤ)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (P : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).over V)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).over V) P)
    (α : P ⟶ (smallEtaleRingedSite B S hS X.1 X.2).restrictComplex K V)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    ∃ P' : CochainComplex
        (Modules.{u, u} B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2) ℤ,
      IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2).O) P' ∧
        ∃ γ : P' ⟶ ((etaleModulePullback B S hS (chartToSpace B S hS X V)
            (isEtale_chartToSpace B S hS X V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap γ j)) ∧
            Epi (HomologicalComplex.homologyMap γ m) := by
  obtain ⟨P₁, hP₁, β, hβ, hβ'⟩ := exists_approximation_over_postcomp (chartToSpace B S hS X V)
    (isEtale_chartToSpace B S hS X V) K m (chartIdChart B S hS X V) V (postcompChartIdChartHom V)
    P hP α hiso hepi
  exact RingedSite.exists_approximation_of_over_terminal
    (smallEtaleRingedSite B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2)
    (isTerminal_chartIdChart B S hS X V) _ m P₁ hP₁ β hβ hβ'

end AlgebraicGeometry.Space

end
