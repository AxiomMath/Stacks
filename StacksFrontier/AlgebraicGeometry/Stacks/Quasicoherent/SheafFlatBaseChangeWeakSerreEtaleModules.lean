module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChange
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.IsoLocusOfNatTrans

/-!
# `LQCoh^fbc` is a weak Serre subcategory of the étale modules (Stacks 0771 (2))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. This file proves that the
étale sheaves of `𝒪_𝒳`-modules which are locally quasi-coherent (Stacks 06WJ) and have the flat
base change property of Stacks 0762, read with the pullback of sheaves of Stacks 06WC, form a
weak Serre subcategory of `Mod(𝒳_ét, 𝒪_𝒳)`.

The argument is the one of Stacks 0764 (2): the restriction functors `F ↦ F|_{U_ét}` are exact,
`f_{small}^*` is exact for a flat morphism of schemes `f`, the comparison maps `c_φ` are natural,
and the five lemma applies. Exactness of `f_{small}^*` is used only on quasi-coherent modules,
where it is proved here: a quasi-coherent module `𝒢` on `V_ét` is the associated module
`ε^*𝒢|_{V_Zar}` (Stacks 03DX (2)), `f_{small}^* ∘ ε^* = ε^* ∘ f^*` (Stacks 03LC (1)), and `ε^*`
(Stacks 08H8) and `f^*` for flat `f` (Stacks 02N4) preserve monomorphisms.

## Main definitions

* `AlgebraicGeometry.Stack.sheafifiedRestrictModulePullbackComparisonNatTrans`: the comparison
  `c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of Stacks 06WC as a natural transformation of
  functors on étale sheaves of modules.

## Main results

* `AlgebraicGeometry.Stack.mono_sheafifiedPullbackComparison_map`: `f_{small}^*` preserves
  monomorphisms between quasi-coherent modules for flat `f`.
* `AlgebraicGeometry.Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChange`:
  **Stacks 0771 (2) for `Mod(𝒳_ét, 𝒪_𝒳)`**.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Adjunction

variable {C₀ : Type*} [Category* C₀] {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂]
  {L : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adj : L ⊣ G)

/-- A natural transformation `A ⟶ Bf ⋙ G` into a right adjoint, transposed objectwise into a
natural transformation `A ⋙ L ⟶ Bf` out of the left adjoint. -/
def natTransOfHomEquivSymm (A : C₀ ⥤ C₁) (Bf : C₀ ⥤ C₂) (α : A ⟶ Bf ⋙ G) : A ⋙ L ⟶ Bf where
  app X := (adj.homEquiv _ _).symm (α.app X)
  naturality X Y f := by
    simp only [Functor.comp_map]
    rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm,
      α.naturality]
    rfl

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

section Mono

variable (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **`f_{small}^*` preserves monomorphisms between quasi-coherent modules, for flat `f`.** Below
an arrow `φ : x ⟶ y` of `𝒳` lying over a flat morphism of schemes `f : U ⟶ V`, the sheafified
pullback of Stacks 06WC carries a monomorphism between quasi-coherent modules on `V_ét` to a
monomorphism.

A quasi-coherent module `𝒢` on `V_ét` is the associated module of its restriction to the Zariski
site through the counit of `ε^* ⊣ ε_*` (Stacks 03DX (2)), so `m` is `ε^*ε_*m` up to
isomorphisms; `ε_*m` is a monomorphism, `ε_*` being a right adjoint; the sheafified pullback of
`ε^*ε_*m` is `ε^*f^*ε_*m` up to isomorphisms (Stacks 03LC (1)); and `f^*` (Stacks 02N4) and `ε^*`
(Stacks 08H8) preserve monomorphisms. -/
theorem mono_sheafifiedPullbackComparison_map {x y : 𝒳} (φ : x ⟶ y)
    (hflat : Flat (B.inclusion.map (p.map φ).left))
    {G G' : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj y).left.1
      (contains_base B E h S hS p y))} (m : G ⟶ G') [Mono m]
    (hG : G.IsQuasicoherentOnSite) (hG' : G'.IsQuasicoherentOnSite) :
    Mono ((sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map m) := by
  let V := (p.obj y).left.1
  let hV := contains_base B E h S hS p y
  let adj := SmallEtale.associatedModuleAdjunction E V hV
  have : IsIso (adj.counit.app G) := SmallEtale.isIso_counit E V hV G hG
    (SmallEtale.isQuasicoherent_restrictModule E V hV G hG)
  have : IsIso (adj.counit.app G') := SmallEtale.isIso_counit E V hV G' hG'
    (SmallEtale.isQuasicoherent_restrictModule E V hV G' hG')
  have hm : m = inv (adj.counit.app G) ≫
      (SmallEtale.associatedModule E V hV).map ((SmallEtale.restrictModule E V hV).map m) ≫
        adj.counit.app G' := by
    have := adj.counit.naturality m
    simp only [Functor.comp_map, Functor.id_map] at this
    rw [this, IsIso.inv_hom_id_assoc]
  let g := (SmallEtale.restrictModule E V hV).map m
  have : (SmallEtale.restrictModule E V hV).IsRightAdjoint := adj.isRightAdjoint
  have : Mono g := inferInstanceAs (Mono ((SmallEtale.restrictModule E V hV).map m))
  have : Flat (B.inclusion.map (p.map φ).left) := hflat
  have : PreservesFiniteLimits (Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)) :=
    preservesFiniteLimits_pullback_of_flat _
  have : PreservesFiniteLimits (SmallEtale.associatedModule E (p.obj x).left.1
      (contains_base B E h S hS p x)) :=
    SmallEtale.preservesFiniteLimits_associatedModule E _ _
  let N := associatedModuleSmallEtaleBaseChangeIso B E h S hS p hp τ hτ φ
  have hN : (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map
      ((SmallEtale.associatedModule E V hV).map g) =
      N.hom.app _ ≫ (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).map
          ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).map g) ≫ N.inv.app _ := by
    have := N.hom.naturality g
    simp only [Functor.comp_map] at this
    rw [← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rfl
  have : Mono ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).map g) :=
    Functor.map_mono _ _
  have i₀ : Mono ((SmallEtale.associatedModule E (p.obj x).left.1
      (contains_base B E h S hS p x)).map
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).map g)) :=
    Functor.map_mono _ _
  have i₁ : Mono ((sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map
      (inv (adj.counit.app G))) :=
    @IsIso.mono_of_iso _ _ _ _ _ (Functor.map_isIso _ _)
  have i₂ : Mono (N.hom.app ((SmallEtale.restrictModule E V hV).obj G)) :=
    @IsIso.mono_of_iso _ _ _ _ _ (N.app _).isIso_hom
  have i₃ : Mono (N.inv.app ((SmallEtale.restrictModule E V hV).obj G')) :=
    @IsIso.mono_of_iso _ _ _ _ _ (N.app _).isIso_inv
  have i₄ : Mono ((sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map
      (adj.counit.app G')) :=
    @IsIso.mono_of_iso _ _ _ _ _ (Functor.map_isIso _ _)
  rw [hm, Functor.map_comp, Functor.map_comp, hN]
  exact @mono_comp _ _ _ _ _ _ i₁ _ (@mono_comp _ _ _ _ _ _
    (@mono_comp _ _ _ _ _ _ i₂ _ (@mono_comp _ _ _ _ _ _ i₀ _ i₃)) _ i₄)

end Mono

section NatTrans

variable {x y : 𝒳} (φ : x ⟶ y)

/-- **The comparison `c_φ` of Stacks 06WC, as a natural transformation of functors on étale
sheaves of modules**: from the restriction to `V_ét` followed by the sheafified pullback
`f_{small}^*`, to the restriction to `U_ét`. Its component at `F` is the morphism of sheaves
induced by the presheaf comparison `AlgebraicGeometry.Stack.restrictModulePullbackComparison`
through the sheafification adjunction (`sheafifiedRestrictModulePullbackComparisonNatTrans_app`).
-/
def sheafifiedRestrictModulePullbackComparisonNatTrans :
    restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp y ⋙
        sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ ⟶
      restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x :=
  (PresheafOfModules.sheafificationAdjunction
      (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj)).natTransOfHomEquivSymm
    (SheafOfModules.forget _ ⋙ restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) y ⋙
        PresheafOfModules.pullback.{u} (smallEtaleStructureComparison B E h S hS p hp φ
          (etaleTopology B) (etaleTopology_le_topology B)))
    (restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x)
    (Functor.whiskerLeft (SheafOfModules.forget _)
      (restrictModulePullbackComparisonNatTrans B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ))

/-- The component of the sheafified comparison at an étale sheaf of modules `F` is the morphism of
sheaves which the sheafification adjunction attaches to the presheaf comparison
`AlgebraicGeometry.Stack.restrictModulePullbackComparison` of `F`. -/
theorem sheafifiedRestrictModulePullbackComparisonNatTrans_app
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    (sheafifiedRestrictModulePullbackComparisonNatTrans B E h S hS p hp φ).app F =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj)).homEquiv _
        ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp x).obj F)).symm
      (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F.val) :=
  rfl

end NatTrans

section WeakSerre

/-- Local quasi-coherence (Stacks 06WJ) is a weak Serre subcategory of the étale sheaves of
modules: it contains zero and is closed under isomorphisms, kernels, cokernels (Stacks 06WM (2))
and extensions (Stacks 06WM (3)). -/
theorem isWeakSerreClass_isLocallyQuasicoherent :
    haveI := hasSheafify_etaleAssociatedTopology B S hS p hp
    haveI := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
    (isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp).IsWeakSerreClass := by
  have := hasSheafify_etaleAssociatedTopology B S hS p hp
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
  have hk := isClosedUnderKernels_isLocallyQuasicoherent B E h S hS p hp
  have hc := isClosedUnderCokernels_isLocallyQuasicoherent B E h S hS p hp
  have hz := containsZero_isLocallyQuasicoherent B E h S hS p hp
  have hi := isClosedUnderIsomorphisms_isLocallyQuasicoherent B E h S hS p hp
  exact { prop_X₂_of_shortExact := fun hT h₁ h₃ =>
    (isLocallyQuasicoherent_twoOutOfThree B E h S hS p hp _ hT).2.2 h₁ h₃ }

/-- The objects of `𝒳` below arrows lying over flat morphisms of schemes, the index of the
comparison maps the flat base change property of Stacks 0762 is about. -/
abbrev FlatArrowIndex :=
  {a : Σ (x y : 𝒳), x ⟶ y // Flat (B.inclusion.map (p.map a.2.2).left)}

/-- **Stacks 0771 (2) for `Mod(𝒳_ét, 𝒪_𝒳)`**, with the flat base change property of Stacks 0762
read with the pullback of sheaves: the étale sheaves of `𝒪_𝒳`-modules which are locally
quasi-coherent and have the flat base change property form a weak Serre subcategory of the étale
sheaves of modules.

Local quasi-coherence is a weak Serre class (Stacks 06WM). Below a flat arrow `φ` the restriction
`F ↦ F|_{U_ét}` is exact, the restriction to `V_ét` followed by `f_{small}^*` is right exact and
preserves monomorphisms between locally quasi-coherent modules
(`AlgebraicGeometry.Stack.mono_sheafifiedPullbackComparison_map`), and the comparison `c_φ` is a
natural transformation between them; the locus where all `c_φ` are invertible is then weak Serre
by `CategoryTheory.ObjectProperty.isWeakSerreClass_isoLocus` (the five lemma), and it is the class
of the source by `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictModulePullbackComparison_iff`. -/
theorem isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChange :
    haveI := hasSheafify_etaleAssociatedTopology B S hS p hp
    haveI := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
    ObjectProperty.IsWeakSerreClass
      (C := SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)))
      (fun F => IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp
        F.val) := by
  have := hasSheafify_etaleAssociatedTopology B S hS p hp
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
  let Q := isLocallyQuasicoherent.{u, v, w, u} B E h S hS p hp
  have : Q.IsWeakSerreClass := isWeakSerreClass_isLocallyQuasicoherent B E h S hS p hp
  let T : ∀ i : FlatArrowIndex B S hS p, _ := fun i =>
    restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp i.1.2.1 ⋙
      sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) i.1.2.2
  let R : ∀ i : FlatArrowIndex B S hS p, _ := fun i =>
    restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp i.1.1
  let c : ∀ i, T i ⟶ R i := fun i =>
    sheafifiedRestrictModulePullbackComparisonNatTrans B E h S hS p hp i.1.2.2
  have : ∀ i, (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) (i : FlatArrowIndex B S hS p).1.2.2).IsLeftAdjoint :=
    fun i => (sheafifiedPullbackComparisonAdjunction B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) i.1.2.2).isLeftAdjoint
  have : ∀ i, PreservesFiniteColimits (T i) := fun i => by dsimp only [T]; infer_instance
  have : ∀ i, (T i).PreservesZeroMorphisms := fun i => by dsimp only [T]; infer_instance
  have : ∀ i, PreservesFiniteLimits (R i) := fun i => by dsimp only [R]; infer_instance
  have : ∀ i, PreservesFiniteColimits (R i) := fun i => by dsimp only [R]; infer_instance
  have : ∀ i, (R i).PreservesZeroMorphisms := fun i => by dsimp only [R]; infer_instance
  have hT : ∀ i ⦃X Y⦄ (f : X ⟶ Y), Q X → Q Y → Mono f → Mono ((T i).map f) := by
    intro i X Y f hX hY hf
    have : Mono ((restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp i.1.2.1).map f) :=
      Functor.map_mono _ _
    exact mono_sheafifiedPullbackComparison_map B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) i.1.2.2 i.2 _
      ((isLocallyQuasicoherent_iff B E h S hS p hp X).1 hX i.1.2.1)
      ((isLocallyQuasicoherent_iff B E h S hS p hp Y).1 hY i.1.2.1)
  have hmain := ObjectProperty.isWeakSerreClass_isoLocus Q T R c hT
  convert hmain using 1
  funext F
  apply propext
  refine and_congr Iff.rfl ⟨fun hF i => ?_, fun hF x y φ hφ => ?_⟩
  · exact (isIso_sheafifiedRestrictModulePullbackComparison_iff B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) i.1.2.2 F.val
      (restrictModuleToSmallEtale_isSheaf B E h S hS p hp i.1.1 F.val F.isSheaf)).2 (hF _ i.2)
  · exact (isIso_sheafifiedRestrictModulePullbackComparison_iff B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ F.val
      (restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F.val F.isSheaf)).1
        (hF ⟨⟨x, y, φ⟩, hφ⟩)

end WeakSerre

end AlgebraicGeometry.Stack
