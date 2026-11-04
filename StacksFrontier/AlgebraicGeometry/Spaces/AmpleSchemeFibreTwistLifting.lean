module

public import StacksFrontier.AlgebraicGeometry.FromSpecStalkOfMemAppTop
public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwistStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatGlobalSectionsRingHom
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject

/-!
# Lifting sections from the fibre: reductions for the second conclusion of Stacks 0D39

The second conclusion of Stacks 0D39 is the surjectivity of
`f_*(ℱ ⊗ ℒ^{⊗ d})_y ⟶ H⁰(X_y, ℱ_y ⊗ ℒ_y^{⊗ d})`, formalized as the lifting of every section on
the fibre to a section over the preimage of an open neighbourhood of `y`
(`AlgebraicGeometry.Space.AmpleSchemeFibreTwistConclusion`). The restriction
`AlgebraicGeometry.Space.restrictSectionAlong` is surjective as soon as the inverse image of global
sections along `h_U ⟶ X_V` is.

## Main definitions

* `AlgebraicGeometry.Space.openSiteObjectHomOfLE`: the inclusion of open subschemes `V ⊆ W`, as a
  morphism of the site.
* `AlgebraicGeometry.Space.stalkPointToOpen`: `Spec 𝒪_{Y,y} ⟶ W` for an open `W ∋ y`.

## Main results

* `AlgebraicGeometry.Space.exists_restrictSectionAlong_eq_of_surjective`: the restriction to the
  fibre is surjective when the inverse image of global sections is.
* `AlgebraicGeometry.Space.representedSpaceMap_openSiteObjectHom_cancel`: morphisms into an open
  subscheme are determined after composing with its inclusion.
* `AlgebraicGeometry.Space.exists_le_forall_globalSectionsRingHomSite_stalkPointToOpen_eq`:
  finitely many global functions on `Spec 𝒪_{Y,y}` come from one neighbourhood of `y`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If the inverse image of global sections along `h_U ⟶ X_V` is surjective, so is the
restriction `AlgebraicGeometry.Space.restrictSectionAlong` to the fibre. -/
theorem exists_restrictSectionAlong_eq_of_surjective {X XV : AlgebraicSpaces B S hS}
    (pV : XV ⟶ X) (U : BigFppfOver B S hS) (jV : yoneda.obj U ⟶ XV.1) (p : yoneda.obj U ⟶ X.1)
    (h : jV ≫ pV.hom = p) (G : Modules.{u, u} B S hS X.1 X.2)
    (hs : Function.Surjective (globalSectionsPullbackMap B S hS (representedPointHom U jV)
      ((modulePullback B S hS pV).obj G)).hom)
    (t : spaceModuleSections (representedAlgebraicSpace B S hS U)
      ((modulePullback B S hS (ObjectProperty.homMk p :
        representedAlgebraicSpace B S hS U ⟶ X)).obj G)) :
    ∃ s : spaceModuleSections XV ((modulePullback B S hS pV).obj G),
      restrictSectionAlong pV U jV p h G s = t := by
  have hb₁ := ConcreteCategory.bijective_of_isIso (spaceModuleSectionsPullbackCongr
    (ObjectProperty.hom_ext _ h : (representedPointHom U jV) ≫ pV = ObjectProperty.homMk p) G).hom
  have hb₂ := ConcreteCategory.bijective_of_isIso ((globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).O)).map
    ((modulePullbackCompIso B S hS (representedPointHom U jV) pV).hom.app G))
  obtain ⟨z₁, hz₁⟩ := hb₁.2 t
  obtain ⟨z₂, hz₂⟩ := hb₂.2 z₁
  obtain ⟨s, hs'⟩ := hs z₂
  exact ⟨s, by rw [restrictSectionAlong, hs', hz₂, hz₁]⟩

/-! ### Inclusions of open subschemes, as morphisms of the site -/

section OpenInclusion

variable (Y : BigFppfOver B S hS)

/-- The inclusion `V ⊆ W` of open subschemes, as a morphism of the site. -/
def openSiteObjectHomOfLE {V W : ((BigFppfOver.toScheme B S hS).obj Y).Opens} (h : V ≤ W) :
    openSiteObject B S hS Y V ⟶ openSiteObject B S hS Y W :=
  Over.homMk (ObjectProperty.homMk (((BigFppfOver.toScheme B S hS).obj Y).homOfLE h)) (by
    refine ObjectProperty.hom_ext _ ?_
    change ((BigFppfOver.toScheme B S hS).obj Y).homOfLE h ≫ (W.ι ≫ (Over.hom Y).hom) =
      V.ι ≫ (Over.hom Y).hom
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (Over.hom Y).hom) (Scheme.homOfLE_ι _ h)))

/-- The inclusion `V ⊆ W` followed by the inclusion of `W` is the inclusion of `V`. -/
theorem openSiteObjectHomOfLE_comp {V W : ((BigFppfOver.toScheme B S hS).obj Y).Opens}
    (h : V ≤ W) :
    openSiteObjectHomOfLE Y h ≫ openSiteObjectHom B S hS Y W = openSiteObjectHom B S hS Y V := by
  refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
  show ((BigFppfOver.toScheme B S hS).obj Y).homOfLE h ≫ W.ι = V.ι
  exact Scheme.homOfLE_ι _ h

/-- Morphisms into an open subscheme agree once composed with its inclusion. -/
theorem openSiteObjectHom_cancel {W : ((BigFppfOver.toScheme B S hS).obj Y).Opens}
    {Z : BigFppfOver B S hS} {a b : Z ⟶ openSiteObject B S hS Y W}
    (h : a ≫ openSiteObjectHom B S hS Y W = b ≫ openSiteObjectHom B S hS Y W) : a = b := by
  have h' := congrArg (BigFppfOver.toScheme B S hS).map h
  rw [Functor.map_comp, Functor.map_comp, map_openSiteObjectHom] at h'
  exact (BigFppfOver.toScheme B S hS).map_injective ((cancel_mono W.ι).1 h')

/-- Morphisms of represented algebraic spaces into an open subscheme agree once composed with its
inclusion. -/
theorem representedSpaceMap_openSiteObjectHom_cancel
    {W : ((BigFppfOver.toScheme B S hS).obj Y).Opens} {Z : BigFppfOver B S hS}
    {α β : representedAlgebraicSpace B S hS Z ⟶
      representedAlgebraicSpace B S hS (openSiteObject B S hS Y W)}
    (h : α ≫ representedSpaceMap B S hS (openSiteObjectHom B S hS Y W) =
      β ≫ representedSpaceMap B S hS (openSiteObjectHom B S hS Y W)) : α = β := by
  obtain ⟨a, ha⟩ := yoneda.map_surjective α.hom
  obtain ⟨b, hb⟩ := yoneda.map_surjective β.hom
  have h₁ := congrArg (fun f ↦ f.hom) h
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom, ← ha,
    ← hb] at h₁
  change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ yoneda.map _ at h₁
  rw [← Functor.map_comp, ← Functor.map_comp] at h₁
  exact ObjectProperty.hom_ext _ (ha.symm.trans ((congrArg yoneda.map
    (openSiteObjectHom_cancel Y (yoneda.map_injective h₁))).trans hb))

end OpenInclusion

/-! ### `Spec 𝒪_{Y,y}` over an open neighbourhood of `y` -/

section StalkOpen

variable (Y : BigFppfOver B S hS)
  [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
  {y : (BigFppfOver.toScheme B S hS).obj Y} (W : ((BigFppfOver.toScheme B S hS).obj Y).Opens)
  (hy : y ∈ W)

/-- The morphism `Spec 𝒪_{Y,y} ⟶ W` for an open neighbourhood `W` of `y`, as a morphism of the
site. -/
def stalkPointToOpen : stalkPointObject Y y ⟶ openSiteObject B S hS Y W :=
  Over.homMk (ObjectProperty.homMk (W.fromSpecStalkOfMem y hy)) (by
    refine ObjectProperty.hom_ext _ ?_
    change W.fromSpecStalkOfMem y hy ≫ (W.ι ≫ (Over.hom Y).hom) = _
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (Over.hom Y).hom) (Scheme.Opens.fromSpecStalkOfMem_ι W y hy)))

/-- `Spec 𝒪_{Y,y} ⟶ W` followed by the inclusion of `W` is `Spec 𝒪_{Y,y} ⟶ Y`. -/
theorem stalkPointToOpen_comp_openSiteObjectHom :
    stalkPointToOpen Y W hy ≫ openSiteObjectHom B S hS Y W = stalkPointHom Y y := by
  refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
  show W.fromSpecStalkOfMem y hy ≫ W.ι = _
  exact Scheme.Opens.fromSpecStalkOfMem_ι W y hy

/-- `Spec 𝒪_{Y,y} ⟶ V` followed by the inclusion `V ⊆ W` is `Spec 𝒪_{Y,y} ⟶ W`. -/
theorem stalkPointToOpen_comp_openSiteObjectHomOfLE
    {V : ((BigFppfOver.toScheme B S hS).obj Y).Opens} (hVW : V ≤ W) (hyV : y ∈ V) :
    stalkPointToOpen Y V hyV ≫ openSiteObjectHomOfLE Y hVW = stalkPointToOpen Y W hy :=
  openSiteObjectHom_cancel Y (by
    rw [Category.assoc, openSiteObjectHomOfLE_comp, stalkPointToOpen_comp_openSiteObjectHom,
      stalkPointToOpen_comp_openSiteObjectHom])

/-- The diagram of identity charts over the morphism `Spec 𝒪_{Y,y} ⟶ V`. -/
def stalkPointToOpenChartDiagram : ChartDiagram B S hS (yoneda.obj (stalkPointObject Y y))
    (yoneda.obj (openSiteObject B S hS Y W)) (yoneda.map (stalkPointToOpen Y W hy)) :=
  ⟨idEtaleChart B S hS (stalkPointObject Y y), idEtaleChart B S hS (openSiteObject B S hS Y W),
    stalkPointToOpen Y W hy, (Category.id_comp _).trans (Category.comp_id _).symm⟩

include hy in
/-- Finitely many global regular functions on `Spec 𝒪_{Y,y}` come from one open neighbourhood
`V ⊆ W` of `y`, read on the algebraic spaces the two schemes represent. -/
theorem exists_le_forall_globalSectionsRingHomSite_stalkPointToOpen_eq {ι : Type*}
    (s : Finset ι) (c : ι → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (representedAlgebraicSpace B S hS (stalkPointObject Y y)).1
      (representedAlgebraicSpace B S hS (stalkPointObject Y y)).2).O).obj) :
    ∃ (V : ((BigFppfOver.toScheme B S hS).obj Y).Opens) (_ : V ≤ W) (hyV : y ∈ V)
      (a : ι → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
        (representedAlgebraicSpace B S hS (openSiteObject B S hS Y V)).1
        (representedAlgebraicSpace B S hS (openSiteObject B S hS Y V)).2).O).obj),
      ∀ i ∈ s, globalSectionsRingHomSite B S hS
        (representedSpaceMap B S hS (stalkPointToOpen Y V hyV)) (a i) = c i := by
  let T := stalkPointObject Y y
  have hbT := bijective_globalSectionsChartEval_of_isTerminal B S hS
    (representedAlgebraicSpace B S hS T) (isTerminalIdEtaleChart B S hS T)
  obtain ⟨V, hVW, hyV, a', ha'⟩ := Scheme.exists_le_forall_fromSpecStalkOfMem_appTop_eq y hy s
    (fun i ↦ globalSectionsChartEval B S hS (representedAlgebraicSpace B S hS T)
      (idEtaleChart B S hS T) (c i))
  have hbV := bijective_globalSectionsChartEval_of_isTerminal B S hS
    (representedAlgebraicSpace B S hS (openSiteObject B S hS Y V))
    (isTerminalIdEtaleChart B S hS (openSiteObject B S hS Y V))
  choose a ha using fun i ↦ hbV.2 (a' i)
  refine ⟨V, hVW, hyV, a, fun i hi ↦ hbT.1 ?_⟩
  refine (globalSectionsChartEval_globalSectionsRingHomSite B S hS
    (representedSpaceMap B S hS (stalkPointToOpen Y V hyV))
    (stalkPointToOpenChartDiagram Y V hyV) (a i)).trans ?_
  exact (congrArg (fun z ↦ (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (stalkPointToOpen Y V hyV)).op).hom z) (ha i)).trans (ha' i hi)

end StalkOpen

end AlgebraicGeometry.Space

end
