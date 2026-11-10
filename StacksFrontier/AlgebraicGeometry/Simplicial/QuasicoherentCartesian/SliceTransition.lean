module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.Slice

/-!
# Localized transitions of a simplicial site

A *localized transition* along an arrow `c : P ⟶ Q` of the total category of a simplicial-site
situation, from degree `k` to degree `n`, is a colimit-preserving functor `Φ` from modules on the
degree-`n` slice at `Q` to modules on the degree-`k` slice at `P`, with a comparison
`Φ ∘ (-)|_Q ⟶ (-)|_c` invertible on the structure sheaf. This is the abstract shape of the
transitions of Stacks 09WF restricted to slices, in both cases of Stacks 09WE.

The comparison is then invertible on every module with a global presentation, and this is
enough to run both halves of the argument of Stacks 0D7M that do not depend on the case:

* a module on the total site whose components are quasi-coherent, and which has a global
  presentation over `Q` as soon as its degree-`n` component has one, is quasi-coherent;
* a module on the total slice at `Q` whose degree-`n` restriction is presented, and at which
  localized transitions reaching every object of the slice are invertible, is presented itself:
  the counit of the extension `μ_!` is invertible, being so after every restriction `(-)|_c`.

All declarations are in the namespace `CategoryTheory.SimplicialSiteSituation.CartesianSlice`.

## Main definitions

* `SliceTransition`: a localized transition along an arrow of the total category.

## Main results

* `hasGlobalPresentation_of_sliceTransition`: a module on the total slice at `Q` whose degree-`n`
  restriction is presented, and at which localized transitions reaching every object of the
  slice are invertible, has a global presentation.
* `isQuasicoherentOnSite_componentModuleRestriction`: the components of a quasi-coherent module
  are quasi-coherent (Stacks 03DO).
* `isQuasicoherentOnSite_of_components`: a module on the total site whose components are
  quasi-coherent, and which has a global presentation over the image of every object over which
  one of its components has one, is quasi-coherent.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSiteSituation.CartesianSlice

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology RingCat.{u}}

/-- **A localized transition** along an arrow `c : P ⟶ Q` of the total category, from degree `k`
to degree `n`: a colimit-preserving functor `Φ` from modules on the degree-`n` slice at `Q` to
modules on the degree-`k` slice at `P`, together with a comparison `Φ ∘ (-)|_Q ⟶ (-)|_c` which is
invertible on the structure sheaf. -/
structure SliceTransition {k n : SimplexCategory} {P : S.component k} {Q : S.component n}
    (c : (componentFunctor S k).obj P ⟶ (componentFunctor S n).obj Q) where
  /-- The localized pullback. -/
  Φ : SheafOfModules.{u} ((S.componentRingSheaf O n).over Q) ⥤
    SheafOfModules.{u} ((S.componentRingSheaf O k).over P)
  /-- The localized pullback preserves colimits. -/
  preservesColimits : PreservesColimitsOfSize.{u, u} Φ
  /-- The localized transition. -/
  τ : sliceRestriction S O Q ⋙ Φ ⟶ sliceRestrictionAt S O c
  /-- The localized transition is invertible on the structure sheaf. -/
  isIso_τ_app_unit : IsIso (τ.app (SheafOfModules.unit _))

namespace SliceTransition

variable {k n : SimplexCategory} {P : S.component k} {Q : S.component n}
  {c : (componentFunctor S k).obj P ⟶ (componentFunctor S n).obj Q}
  (T : SliceTransition (O := O) c)

attribute [instance] preservesColimits isIso_τ_app_unit

/-- **A localized transition is invertible on a module with a global presentation.** -/
theorem isIso_τ_app_of_presentation {M : SheafOfModules.{u} (O.over ((componentFunctor S n).obj Q))}
    (P : M.Presentation) : IsIso (T.τ.app M) :=
  have : PreservesColimitsOfSize.{u, u} (sliceRestriction S O Q ⋙ T.Φ) :=
    comp_preservesColimits _ _
  have : PreservesFiniteColimits (sliceRestriction S O Q ⋙ T.Φ) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _
  Stacks.SheafOfModules.isIso_app_of_presentation_of_unit T.τ T.isIso_τ_app_unit P

/-- The comparison `Φ ⟶ (-)|_c ∘ μ_!`. -/
def extensionTransition : T.Φ ⟶ sliceExtension S O Q ⋙ sliceRestrictionAt S O c :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (sliceExtensionAdj S O Q).unit T.Φ ≫
      Functor.whiskerLeft (sliceExtension S O Q) T.τ

/-- The comparison with the extension, followed by the restriction of a map out of the extension,
is the localized transition after the adjunct of that map. -/
private theorem extensionTransition_app_comp_map
    {X : SheafOfModules.{u} ((S.componentRingSheaf O n).over Q)}
    {G : SheafOfModules.{u} (O.over ((componentFunctor S n).obj Q))}
    (g : (sliceExtension S O Q).obj X ⟶ G) :
    T.extensionTransition.app X ≫ (sliceRestrictionAt S O c).map g =
      T.Φ.map ((sliceExtensionAdj S O Q).homEquiv _ _ g) ≫ T.τ.app G := by
  simp only [extensionTransition, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp, Category.assoc]
  rw [← T.τ.naturality, ← Category.assoc, Functor.comp_map, ← Functor.map_comp]
  simp [Adjunction.homEquiv_unit]

/-- The comparison with the extension, followed by the restricted counit, is the localized
transition. -/
theorem extensionTransition_app_comp_map_counit (G : SheafOfModules.{u}
    (O.over ((componentFunctor S n).obj Q))) :
    T.extensionTransition.app ((sliceRestriction S O Q).obj G) ≫
        (sliceRestrictionAt S O c).map ((sliceExtensionAdj S O Q).counit.app G) =
      T.τ.app G := by
  rw [extensionTransition_app_comp_map]
  simp [Adjunction.homEquiv_unit]

/-- On the structure sheaf, the comparison with the extension is the localized transition up to the
unit identifications. -/
theorem extensionTransition_app_unit :
    T.extensionTransition.app (SheafOfModules.unit _) ≫
        (sliceRestrictionAt S O c).map (sliceExtensionUnitHom S O Q) =
      T.Φ.map (sliceRestrictionUnitHom S O Q) ≫ T.τ.app (SheafOfModules.unit _) := by
  rw [extensionTransition_app_comp_map]
  exact congrArg (· ≫ _) (congrArg T.Φ.map
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _))

/-- The comparison with the extension is invertible on the structure sheaf. -/
instance isIso_extensionTransition_app_unit :
    IsIso (T.extensionTransition.app (SheafOfModules.unit _)) := by
  have h := T.extensionTransition_app_unit
  have : IsIso (T.extensionTransition.app (SheafOfModules.unit _) ≫
      (sliceRestrictionAt S O c).map (sliceExtensionUnitHom S O Q)) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_right _ ((sliceRestrictionAt S O c).map (sliceExtensionUnitHom S O Q))

/-- The comparison with the extension is invertible on a module with a global presentation. -/
theorem isIso_extensionTransition_app_of_presentation
    {M : SheafOfModules.{u} ((S.componentRingSheaf O n).over Q)}
    (P : M.Presentation) : IsIso (T.extensionTransition.app M) :=
  have := (sliceExtensionAdj S O Q).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} (sliceExtension S O Q ⋙ sliceRestrictionAt S O c) :=
    comp_preservesColimits _ _
  have : PreservesFiniteColimits (sliceExtension S O Q ⋙ sliceRestrictionAt S O c) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _
  have : PreservesFiniteColimits T.Φ := PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _
  Stacks.SheafOfModules.isIso_app_of_presentation_of_unit T.extensionTransition
    T.isIso_extensionTransition_app_unit P

/-- **The counit of extension is invertible along `c`** as soon as the localized transition is
invertible at the module and the restriction of the module to the degree-`n` slice is
presented. -/
theorem isIso_sliceRestrictionAt_map_counit (G : SheafOfModules.{u}
    (O.over ((componentFunctor S n).obj Q)))
    (P : ((sliceRestriction S O Q).obj G).Presentation) (hτ : IsIso (T.τ.app G)) :
    IsIso ((sliceRestrictionAt S O c).map ((sliceExtensionAdj S O Q).counit.app G)) := by
  have := T.isIso_extensionTransition_app_of_presentation P
  exact IsIso.of_isIso_fac_left (T.extensionTransition_app_comp_map_counit G)

end SliceTransition

end CategoryTheory.SimplicialSiteSituation.CartesianSlice

namespace CategoryTheory.SimplicialSiteSituation.CartesianSlice

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})

/-- **A morphism of modules on the total slice at `Q` is invertible as soon as its restrictions
along a family of arrows reaching every object of the slice are.** -/
theorem isIso_of_forall_sliceRestrictionAt {n : SimplexCategory} {Q : S.component n}
    {G G' : SheafOfModules.{u} (O.over ((componentFunctor S n).obj Q))} (g : G ⟶ G')
    (h : ∀ Z : Over ((componentFunctor S n).obj Q), ∃ (k : SimplexCategory) (P : S.component k)
      (c : (componentFunctor S k).obj P ⟶ (componentFunctor S n).obj Q) (W : Over P),
      (sliceInclusionAt S c).obj W = Z ∧ IsIso ((sliceRestrictionAt S O c).map g)) :
    IsIso g := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _),
    NatTrans.isIso_iff_isIso_app]
  intro Z
  obtain ⟨k, P, c, W, hW, hc⟩ := h Z.unop
  have := Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward
    (F := sliceInclusionAt S c)
    (J := (S.componentTopology k).over P) (K := S.totalTopology.over _)
    (S := (S.componentRingSheaf O k).over P) (R := O.over ((componentFunctor S n).obj Q))
    (𝟙 ((S.componentRingSheaf O k).over P)) g hc (op W)
  rw [show Z = op ((sliceInclusionAt S c).obj W) from congrArg op hW.symm]
  exact Functor.map_isIso (forget₂ (ModuleCat _) AddCommGrpCat.{u}) (g.val.app _)

/-- On a site with a final object, a global presentation gives a presentation. -/
private theorem nonempty_presentation_of_isTerminal {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {T : C} (hT : IsTerminal T)
    {M : SheafOfModules.{u} R} (h : M.HasGlobalPresentation) : Nonempty M.Presentation :=
  have := fun N : SheafOfModules.{u} R => SheafOfModules.small_sections_of_isTerminal hT N
  SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections h

/-- **A module on the total slice at `Q` has a global presentation** as soon as its restriction to
the degree-`n` slice at `Q` has one, and localized transitions reaching every object of the
total slice are invertible at it. -/
theorem hasGlobalPresentation_of_sliceTransition {n : SimplexCategory} {Q : S.component n}
    (G : SheafOfModules.{u} (O.over ((componentFunctor S n).obj Q)))
    (hG : ((sliceRestriction S O Q).obj G).HasGlobalPresentation)
    (h : ∀ Z : Over ((componentFunctor S n).obj Q), ∃ (k : SimplexCategory) (P : S.component k)
      (c : (componentFunctor S k).obj P ⟶ (componentFunctor S n).obj Q) (W : Over P),
      (sliceInclusionAt S c).obj W = Z ∧
        ∃ T : SliceTransition (O := O) c, IsIso (T.τ.app G)) :
    G.HasGlobalPresentation := by
  obtain ⟨P⟩ := nonempty_presentation_of_isTerminal Over.mkIdTerminal hG
  have : IsIso ((sliceExtensionAdj S O Q).counit.app G) := by
    refine isIso_of_forall_sliceRestrictionAt S O _ fun Z => ?_
    obtain ⟨k, P', c, W, hW, T, hT⟩ := h Z
    exact ⟨k, P', c, W, hW, T.isIso_sliceRestrictionAt_map_counit G P hT⟩
  have := (sliceExtensionAdj S O Q).leftAdjoint_preservesColimits
  exact SheafOfModules.Presentation.hasGlobalPresentation
    ((P.map (sliceExtension S O Q) (asIso (sliceExtensionUnitHom S O Q)).symm).ofIsIso
      ((sliceExtensionAdj S O Q).counit.app G))

/-- In each degree, the objects over whose image a quasi-coherent module on the total site has a
global presentation cover the final object. -/
theorem coversTop_component_hasGlobalPresentation (F : SheafOfModules.{u} O)
    (hF : F.IsQuasicoherentOnSite) (k : SimplexCategory) :
    (S.componentTopology k).CoversTop fun i : {Q : S.component k //
      (F.over ((componentFunctor S k).obj Q)).HasGlobalPresentation} => i.1 := by
  intro Y
  have h := (componentFunctor S k).cover_lift (S.componentTopology k) S.totalTopology
    (SheafOfModules.coversTop_hasGlobalPresentation F hF ((componentFunctor S k).obj Y))
  refine (S.componentTopology k).superset_covering ?_ h
  rintro Y' g ⟨⟨Z, hZ⟩, ⟨b⟩⟩
  exact ⟨⟨Y', Stacks.SheafOfModules.hasGlobalPresentation_overMap F b hZ⟩, ⟨𝟙 _⟩⟩

/-- Restriction to the degree-`n` slice carries a global presentation to a global presentation. -/
theorem hasGlobalPresentation_sliceRestriction {n : SimplexCategory} (Q : S.component n)
    {G : SheafOfModules.{u} (O.over ((componentFunctor S n).obj Q))}
    (hG : G.HasGlobalPresentation) : ((sliceRestriction S O Q).obj G).HasGlobalPresentation := by
  obtain ⟨P⟩ := nonempty_presentation_of_isTerminal Over.mkIdTerminal hG
  have := (Stacks.SheafOfModules.RestrictRan.sheafAdjunction (sliceInclusion S Q)
    ((S.componentTopology n).over Q) (S.totalTopology.over _)
      (O.over _)).leftAdjoint_preservesColimits.{u, u}
  exact SheafOfModules.Presentation.hasGlobalPresentation
    (P.map (sliceRestriction S O Q) (asIso (sliceRestrictionUnitHom S O Q)))

/-- **The components of a quasi-coherent module on the total site are quasi-coherent.** -/
theorem isQuasicoherentOnSite_componentModuleRestriction (F : SheafOfModules.{u} O)
    (hF : F.IsQuasicoherentOnSite) (n : SimplexCategory) :
    ((S.componentModuleRestriction O n).obj F).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation _
    (coversTop_component_hasGlobalPresentation S O F hF n)
    fun i => hasGlobalPresentation_sliceRestriction S O i.1 i.2

/-- **A module on the total site is quasi-coherent** as soon as its components are and it has a
global presentation over the image of every object over which one of its components has one. -/
theorem isQuasicoherentOnSite_of_components (F : SheafOfModules.{u} O)
    (hobj : ∀ X : S.totalCategory, ∃ (k : SimplexCategory) (x : S.component k),
      (componentFunctor S k).obj x = X)
    (hcomp : ∀ n : SimplexCategory,
      ((S.componentModuleRestriction O n).obj F).IsQuasicoherentOnSite)
    (hloc : ∀ (n : SimplexCategory) (Q : S.component n),
      (((S.componentModuleRestriction O n).obj F).over Q).HasGlobalPresentation →
        (F.over ((componentFunctor S n).obj Q)).HasGlobalPresentation) :
    F.IsQuasicoherentOnSite := by
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation F
    (W := fun i : (Σ n : SimplexCategory, {Q : S.component n //
      (((S.componentModuleRestriction O n).obj F).over Q).HasGlobalPresentation}) =>
      (componentFunctor S i.1).obj i.2.1) ?_ fun i => hloc i.1 i.2.1 i.2.2
  intro X
  obtain ⟨k, x, rfl⟩ := hobj X
  have h := (CoverPreserving.of_isContinuous (componentFunctor S k) (S.componentTopology k)
    S.totalTopology).cover_preserve
    (SheafOfModules.coversTop_hasGlobalPresentation _ (hcomp k) x)
  refine S.totalTopology.superset_covering ?_ h
  rintro Z g ⟨Y, a, b, ⟨⟨Q, hQ⟩, ⟨c⟩⟩, rfl⟩
  exact ⟨⟨k, Q, hQ⟩, ⟨b ≫ (componentFunctor S k).map c⟩⟩

end CategoryTheory.SimplicialSiteSituation.CartesianSlice
