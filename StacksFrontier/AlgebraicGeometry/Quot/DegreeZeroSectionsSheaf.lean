module

public import StacksFrontier.AlgebraicGeometry.Quot.DegreeZeroSectionsLocalRepresentability
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomConeChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional

/-!
# The degree-zero sections functor is an fpqc sheaf

Let `K` be a pseudo-coherent object of `D(𝒪_X)` on an algebraic space `X`, represented by a
K-flat complex `P₀` with flat terms.  The functor `(g : T → X) ↦ H⁰(T, H⁰(Lg^*K))` satisfies the
sheaf property for the fpqc topology on the schemes over `X`.

## Main results

* `AlgebraicGeometry.Space.isSheafFor_relKerFunctor_of_kernel`: the relative kernel functor of a
  morphism of modules whose kernel is quasi-coherent glues along fpqc coverings of the base.
* `AlgebraicGeometry.Space.isSheaf_degreeZeroSectionsFunctor`: the functor
  `(g : T → X) ↦ H⁰(T, H⁰(g^*P₀))` is a sheaf for the fpqc topology.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)

universe u


/-! ### Transporting the sheaf condition along a functor -/

namespace CategoryTheory.Presieve

universe w

/-- Let `Φ : C' ⥤ C` carry a family `g' i : U' i ⟶ T'` to the family `g i : U i ⟶ T` up to
isomorphisms of the objects.  If a presheaf `P'` on `C'` isomorphic to `Φ.op ⋙ P` is a sheaf for
the family `g'`, then `P` is a sheaf for the family `g`. -/
theorem isSheafFor_ofArrows_of_natIso {C C' : Type*} [Category* C] [Category* C'] (Φ : C' ⥤ C)
    {P : Cᵒᵖ ⥤ Type w} {P' : C'ᵒᵖ ⥤ Type w} (η : Φ.op ⋙ P ≅ P') {T : C} {T' : C'}
    (e : Φ.obj T' ≅ T) {J : Type*} {U : J → C} (g : ∀ i, U i ⟶ T) {U' : J → C'}
    (g' : ∀ i, U' i ⟶ T') (eU : ∀ i, Φ.obj (U' i) ≅ U i)
    (hw : ∀ i, (eU i).hom ≫ g i = Φ.map (g' i) ≫ e.hom)
    (h : (Presieve.ofArrows U' g').IsSheafFor P') : (Presieve.ofArrows U g).IsSheafFor P := by
  rw [Presieve.isSheafFor_arrows_iff] at h ⊢
  intro x hx
  let x' : ∀ i, P'.obj (Opposite.op (U' i)) :=
    fun i => η.hom.app (Opposite.op (U' i)) (P.map (eU i).hom.op (x i))
  have key : ∀ i {Z : C'} (a : Z ⟶ U' i), P'.map a.op (x' i) =
      η.hom.app (Opposite.op Z) (P.map (Φ.map a ≫ (eU i).hom).op (x i)) := by
    intro i Z a
    rw [← NatTrans.naturality_apply]
    simp only [Functor.comp_map, Functor.op_map, op_comp, Functor.map_comp_apply]
    rfl
  have hx' : Presieve.Arrows.Compatible P' g' x' := by
    intro i j Z a b hab
    rw [key, key]
    refine congrArg _ (hx i j _ _ _ ?_)
    rw [Category.assoc, Category.assoc, hw, hw, ← Category.assoc, ← Category.assoc,
      ← Φ.map_comp, ← Φ.map_comp, hab]
  obtain ⟨t', ht', hu⟩ := h x' hx'
  have hinj : ∀ i, Function.Injective (P.map (eU i).hom.op) := fun i a b hab => by
    have := congrArg (P.map (eU i).inv.op) hab
    rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id,
      Functor.map_id_apply, Functor.map_id_apply] at this
  have hpt : ∀ (s : P.obj (Opposite.op T)) i,
      P.map (eU i).hom.op (P.map (g i).op s) =
        P.map (Φ.map (g' i)).op (P.map e.hom.op s) := fun s i => by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hw]
  refine ⟨P.map e.inv.op (η.inv.app (Opposite.op T') t'), fun i => hinj i ?_, fun s hs => ?_⟩
  · rw [hpt, ← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have := NatTrans.naturality_apply η.inv (g' i).op t'
    simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at this
    rw [← this, ht' i]
    exact Iso.hom_inv_id_app_apply η (Opposite.op (U' i)) _
  · have hs' : η.hom.app (Opposite.op T') (P.map e.hom.op s) = t' := by
      refine hu _ fun i => ?_
      have := NatTrans.naturality_apply η.hom (g' i).op (P.map e.hom.op s)
      simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at this
      rw [← this, ← hpt, hs i]
    rw [← hs', Iso.hom_inv_id_app_apply, ← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id,
      op_id, Functor.map_id_apply]

end CategoryTheory.Presieve

/-! ### Compatible families of sections of a relative kernel functor -/

namespace CategoryTheory.PullbackData

section RelKer

variable {A' : Type*} {_ : Category* A'} {D' : A' → Type*} {_ : ∀ a, Category* (D' a)}
  {_ : ∀ a, Abelian (D' a)} (P : PullbackData A' D')
  {_ : ∀ {a b : A'} (f : a ⟶ b), (P.pull f).PreservesZeroMorphisms}
  {I : Type*} {_ : Category* I} {π : I ⥤ A'} {a₀ : A'}

/-- If two sections of a relative kernel functor agree after restriction to a common test object
along which the inverse image of `ι` is a monomorphism, then any lifts of them through `ι` also
agree after restriction. -/
theorem relHomMap_eq_of_relKerFunctor_map_eq (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D' a₀)
    {N N' K : D' a₀} (φ : N ⟶ N') (ι : K ⟶ N) {i₁ i₂ j : I} (f₁ : j ⟶ i₁) (f₂ : j ⟶ i₂)
    [Mono ((P.pull (κ.leg j)).map ι)]
    (a₁ : (P.relKerFunctor hP κ M φ).obj (Opposite.op i₁))
    (a₂ : (P.relKerFunctor hP κ M φ).obj (Opposite.op i₂))
    (h : (P.relKerFunctor hP κ M φ).map f₁.op a₁ = (P.relKerFunctor hP κ M φ).map f₂.op a₂)
    (α₁ : P.relHomObj κ M K i₁) (α₂ : P.relHomObj κ M K i₂)
    (h₁ : α₁ ≫ (P.pull (κ.leg i₁)).map ι = a₁.1) (h₂ : α₂ ≫ (P.pull (κ.leg i₂)).map ι = a₂.1) :
    P.relHomMap κ M K f₁ α₁ = P.relHomMap κ M K f₂ α₂ := by
  refine (cancel_mono ((P.pull (κ.leg j)).map ι)).1 ?_
  rw [relHomMap_comp_map, relHomMap_comp_map, h₁, h₂]
  exact (relKerFunctor_map_coe P hP κ M φ f₁ a₁).symm.trans
    ((congrArg Subtype.val h).trans (relKerFunctor_map_coe P hP κ M φ f₂ a₂))

/-- For a compatible family of sections of a relative kernel functor, lifts through `ι` of two of
its members agree after restriction to a common test object along which the inverse image of `ι`
is a monomorphism. -/
theorem relHomMap_eq_of_compatible (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D' a₀)
    {N N' K : D' a₀} (φ : N ⟶ N') (ι : K ⟶ N) {T : I} {R : Presieve T}
    {x : Presieve.FamilyOfElements (P.relKerFunctor hP κ M φ) R} (hx : x.Compatible)
    {i₁ i₂ j : I} (f₁ : j ⟶ i₁) (f₂ : j ⟶ i₂) {g₁ : i₁ ⟶ T} {g₂ : i₂ ⟶ T} (hg₁ : R g₁)
    (hg₂ : R g₂) (hcomp : f₁ ≫ g₁ = f₂ ≫ g₂) [Mono ((P.pull (κ.leg j)).map ι)]
    (α₁ : P.relHomObj κ M K i₁) (α₂ : P.relHomObj κ M K i₂)
    (h₁ : α₁ ≫ (P.pull (κ.leg i₁)).map ι = (x g₁ hg₁).1)
    (h₂ : α₂ ≫ (P.pull (κ.leg i₂)).map ι = (x g₂ hg₂).1) :
    P.relHomMap κ M K f₁ α₁ = P.relHomMap κ M K f₂ α₂ :=
  P.relHomMap_eq_of_relKerFunctor_map_eq hP κ M φ ι f₁ f₂ _ _ (hx f₁ f₂ hg₁ hg₂ hcomp) α₁ α₂ h₁ h₂

/-- Two sections of a relative kernel functor with the same underlying morphism are equal. -/
theorem relKerFunctor_obj_ext (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D' a₀) {N N' : D' a₀}
    (φ : N ⟶ N') {T : I} {a b : (P.relKerFunctor hP κ M φ).obj (Opposite.op T)}
    (h : a.1 = b.1) : a = b :=
  Subtype.ext h

/-- If `ι ≫ φ = 0`, a lift `δ` over `T` whose restrictions are lifts `α i` through `ι` of the
members of a family of sections of the relative kernel functor of `φ` gives an amalgamation of the
family, with underlying morphism `δ ≫ ι`. -/
theorem exists_isAmalgamation_of_relHomMap_eq (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D' a₀)
    {N N' K : D' a₀} (φ : N ⟶ N') (ι : K ⟶ N) (hι : ι ≫ φ = 0) {T : I} {J : Type*}
    {U : J → I} (g : ∀ i, U i ⟶ T)
    (x : Presieve.FamilyOfElements (P.relKerFunctor hP κ M φ) (Presieve.ofArrows U g))
    (δ : P.relHomObj κ M K T) (α : ∀ i, P.relHomObj κ M K (U i))
    (hα : ∀ i, α i ≫ (P.pull (κ.leg (U i))).map ι = (x (g i) (Presieve.ofArrows.mk i)).1)
    (hδ : ∀ i, P.relHomMap κ M K (g i) δ = α i) :
    ∃ t, x.IsAmalgamation t ∧ t.1 = δ ≫ (P.pull (κ.leg T)).map ι := by
  refine ⟨⟨δ ≫ (P.pull (κ.leg T)).map ι, by
    rw [Category.assoc, ← Functor.map_comp, hι, Functor.map_zero, Limits.comp_zero]⟩, ?_, rfl⟩
  rintro _ _ ⟨i⟩
  exact Subtype.ext <| (relKerFunctor_map_coe P hP κ M φ (g i) _).trans
    ((relHomMap_comp_map P κ M ι (g i) δ).symm.trans
      ((congrArg (· ≫ (P.pull (κ.leg (U i))).map ι) (hδ i)).trans (hα i)))

/-- The restriction of a lift through `ι` of an amalgamation is the lift of the member, along
each member along which the inverse image of `ι` is a monomorphism. -/
theorem relHomMap_eq_of_isAmalgamation (hP : P.IsCoherent) (κ : ConeTo π a₀) (M : D' a₀)
    {N N' K : D' a₀} (φ : N ⟶ N') (ι : K ⟶ N) {T : I} {R : Presieve T}
    {x : Presieve.FamilyOfElements (P.relKerFunctor hP κ M φ) R}
    {t : (P.relKerFunctor hP κ M φ).obj (Opposite.op T)} (ht : x.IsAmalgamation t) {i : I}
    {gi : i ⟶ T} (hgi : R gi) [Mono ((P.pull (κ.leg i)).map ι)] (β : P.relHomObj κ M K T)
    (hβ : β ≫ (P.pull (κ.leg T)).map ι = t.1) (αi : P.relHomObj κ M K i)
    (hαi : αi ≫ (P.pull (κ.leg i)).map ι = (x gi hgi).1) :
    P.relHomMap κ M K gi β = αi := by
  exact (cancel_mono ((P.pull (κ.leg i)).map ι)).1 <|
    (relHomMap_comp_map P κ M ι gi β).trans ((congrArg (P.relHomMap κ M N gi) hβ).trans
    ((relKerFunctor_map_coe P hP κ M φ gi t).symm.trans
      ((congrArg Subtype.val (ht gi hgi)).trans hαi.symm)))

end RelKer

end CategoryTheory.PullbackData

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local irreducible] modulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Flatness of the morphisms of represented algebraic spaces -/

/-- The morphism of represented algebraic spaces of a flat morphism of schemes is flat. -/
theorem isFlat_schemeSpaceFunctor_map {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hh : Flat ((BigFppfOver.toScheme B S hS).map h)) :
    IsFlat B S hS ((schemeSpaceFunctor B S hS).map h).hom :=
  (isFlat_iff_presheaf B S hS (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
    (Functor.relativelyRepresentable.map yoneda h)).2
    ((presheaf_yoneda_map_iff B S hS AlgebraicGeometry.Flat.isStableUnderBaseChange h).2 hh)



/-! ### Quasi-coherence of the cohomology of the pullbacks -/

section Quasicoherent

variable {X : AlgebraicSpaces B S hS} (P₀ : CochainComplex (toposModules B S hS X) ℤ)
  (hP₀ : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀))
  {K : derivedModules B S hS X} (hK : IsPseudoCoherentObject K)
  (e : DerivedCategory.Q.obj P₀ ≅ K)

include hK e in
/-- A complex representing a pseudo-coherent object has quasi-coherent cohomology. -/
theorem isQuasicoherentOnSite_homology_of_isPseudoCoherentObject (j : ℤ) :
    (P₀.homology j).IsQuasicoherentOnSite := by
  obtain ⟨K', hK', ⟨e'⟩⟩ := hK
  have h := isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional B S hS X.1 X.2 K
    (j - 1) j ⟨K', hK' (j - 1), ⟨e'⟩⟩ (by omega)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((DerivedCategory.homologyFunctor _ j).mapIso e).symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ j).app P₀) h

include hP₀ hK e in
/-- The pullback of a K-flat representative of a pseudo-coherent object along every morphism of
algebraic spaces has quasi-coherent cohomology. -/
theorem isQuasicoherentOnSite_homology_pull_of_isPseudoCoherentObject {Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (n : ℤ) :
    (((((toposModulePullbackData B S hS).pull f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P₀).homology n).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_homology_modulePullback_of_isKFlat B S hS f P₀ hP₀
    (isQuasicoherentOnSite_homology_of_isPseudoCoherentObject P₀ hK e) n

end Quasicoherent

/-! ### Lifting through the kernel along a flat morphism -/

section Kernel

variable {Y Z : AlgebraicSpaces B S hS} (c : Z ⟶ Y) (hc : IsFlat B S hS c.hom)
  {A Q P : toposModules B S hS Y} (d : Q ⟶ P)

include hc in
/-- Along a flat morphism a homomorphism killed by the inverse image of `d` factors uniquely
through the inverse image of the kernel of `d`. -/
theorem existsUnique_lift_kernel
    (β : ((toposModulePullbackData B S hS).pull c).obj A ⟶
      ((toposModulePullbackData B S hS).pull c).obj Q)
    (hβ : β ≫ ((toposModulePullbackData B S hS).pull c).map d = 0) :
    ∃! α : ((toposModulePullbackData B S hS).pull c).obj A ⟶
        ((toposModulePullbackData B S hS).pull c).obj (kernel d),
      α ≫ ((toposModulePullbackData B S hS).pull c).map (kernel.ι d) = β := by
  have : PreservesLimit (parallelPair d 0) ((toposModulePullbackData B S hS).pull c) :=
    preservesKernel_modulePullback_of_isFlat B S hS c hc d
  let hl := isLimitOfHasKernelOfPreservesLimit ((toposModulePullbackData B S hS).pull c) d
  exact ⟨(KernelFork.IsLimit.lift' hl β hβ).1, (KernelFork.IsLimit.lift' hl β hβ).2,
    fun α hα => Fork.IsLimit.hom_ext hl (hα.trans (KernelFork.IsLimit.lift' hl β hβ).2.symm)⟩

include hc in
/-- Along a flat morphism the inverse image of the inclusion of a kernel is a monomorphism. -/
theorem mono_map_kernel_ι : Mono (((toposModulePullbackData B S hS).pull c).map (kernel.ι d)) := by
  have : PreservesFiniteLimits ((toposModulePullbackData B S hS).pull c) :=
    preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS c hc
  infer_instance

end Kernel

/-! ### The relative kernel functor glues along fpqc coverings -/

section Core

/-- Let `c i : Zi i ⟶ W` be an fpqc covering, `q i = c i ≫ w`, and let the inverse images of `F`
and `G` along `w` be quasi-coherent.  Homomorphisms `α i` between the inverse images of `F` and `G`
along `q i` that agree on the overlaps are the restrictions of a unique homomorphism between the
inverse images along `w`. -/
theorem gluesModuleHomAlongFpqcCovering_topos {I : Type (u + 1)} {X W : AlgebraicSpaces B S hS}
    {Zi : I → AlgebraicSpaces B S hS} (w : W ⟶ X) (c : ∀ i, Zi i ⟶ W) (q : ∀ i, Zi i ⟶ X)
    (hq : ∀ i, c i ≫ w = q i) (hc : IsFpqcCovering B S hS (fun i ↦ (c i).hom))
    (F G : toposModules B S hS X)
    (hF : (((toposModulePullbackData B S hS).pull w).obj F).IsQuasicoherentOnSite)
    (hG : (((toposModulePullbackData B S hS).pull w).obj G).IsQuasicoherentOnSite)
    (α : ∀ i, ((toposModulePullbackData B S hS).pull (q i)).obj F ⟶
      ((toposModulePullbackData B S hS).pull (q i)).obj G)
    (hα : ∀ i j, Functor.conjHom ((toposModulePullbackData B S hS).triangle
        (rfl : overlapFst c i j ≫ q i = _)) (α i) =
      Functor.conjHom ((toposModulePullbackData B S hS).triangle
        (overlapSnd_comp_eq w c q hq i j)) (α j)) :
    ∃! β : ((toposModulePullbackData B S hS).pull w).obj F ⟶
        ((toposModulePullbackData B S hS).pull w).obj G,
      ∀ i, Functor.conjHom ((toposModulePullbackData B S hS).triangle (hq i)) β = α i :=
  gluesModuleHomAlongFpqcCovering.{u, u + 1} (B := B) (S := S) (hS := hS) w c q hq hc F G hF hG α hα

variable {Y₀ : BigFppfOver B S hS}
  (A : toposModules B S hS ((schemeSpaceFunctor B S hS).obj Y₀))
  {Q P : toposModules B S hS ((schemeSpaceFunctor B S hS).obj Y₀)} (d : Q ⟶ P)

/-- The identity test scheme of the algebraic space of a scheme. -/
abbrev idTest (Y₀ : BigFppfOver B S hS) :
    CostructuredArrow (schemeSpaceFunctor B S hS) ((schemeSpaceFunctor B S hS).obj Y₀) :=
  CostructuredArrow.mk (𝟙 ((schemeSpaceFunctor B S hS).obj Y₀))

variable {I : Type (u + 1)}
  {U : I → CostructuredArrow (schemeSpaceFunctor B S hS) ((schemeSpaceFunctor B S hS).obj Y₀)}
  (g : ∀ i, U i ⟶ idTest Y₀)

/-- Homomorphisms of inverse images of quasi-coherent modules along the members of an fpqc
covering of the identity test scheme, agreeing on the overlaps, come from a unique homomorphism
over the identity test scheme. -/
theorem existsUnique_relHomMap_eq (A G : toposModules B S hS ((schemeSpaceFunctor B S hS).obj Y₀))
    (hA : (((toposModulePullbackData B S hS).pull
      ((schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)).leg (idTest Y₀))).obj
        A).IsQuasicoherentOnSite)
    (hG : (((toposModulePullbackData B S hS).pull
      ((schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)).leg (idTest Y₀))).obj
        G).IsQuasicoherentOnSite)
    (hg : IsFpqcCovering B S hS fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom)
    (α : ∀ i, (toposModulePullbackData B S hS).relHomObj
      (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) A G (U i))
    (hα : ∀ i j, Functor.conjHom ((toposModulePullbackData B S hS).triangle
        (rfl : overlapFst (fun i => (schemeSpaceFunctor B S hS).map (g i).left) i j ≫
          (U i).hom = _)) (α i) =
      Functor.conjHom ((toposModulePullbackData B S hS).triangle
        (overlapSnd_comp_eq (𝟙 _) (fun i => (schemeSpaceFunctor B S hS).map (g i).left)
          (fun i => (U i).hom) (fun i => CostructuredArrow.w (g i)) i j)) (α j)) :
    ∃! β : (toposModulePullbackData B S hS).relHomObj
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) A G (idTest Y₀),
      ∀ i, (toposModulePullbackData B S hS).relHomMap
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) A G (g i) β = α i :=
  gluesModuleHomAlongFpqcCovering_topos (𝟙 _)
    (fun i => (schemeSpaceFunctor B S hS).map (g i).left) (fun i => (U i).hom)
    (fun i => CostructuredArrow.w (g i)) hg A G hA hG α hα

/-- Two homomorphisms over members of a covering whose restrictions to the fibre product of the two
test schemes agree also agree on the fibre product of the two algebraic spaces, which maps to the
former. -/
theorem conjHom_overlap_eq_of_relHomMap_eq
    (A G : toposModules B S hS ((schemeSpaceFunctor B S hS).obj Y₀)) (i j : I)
    (α : ∀ i, (toposModulePullbackData B S hS).relHomObj
      (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) A G (U i))
    (hL : ∀ (h₂ : (schemeSpaceFunctor B S hS).map (pullback.snd (g i).left (g j).left) ≫ (U j).hom =
        (schemeSpaceFunctor B S hS).map (pullback.fst (g i).left (g j).left) ≫ (U i).hom),
      (toposModulePullbackData B S hS).relHomMap
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) A G
        (CostructuredArrow.homMk (pullback.fst (g i).left (g j).left) rfl :
          (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map
            (pullback.fst (g i).left (g j).left) ≫ (U i).hom) :
              CostructuredArrow (schemeSpaceFunctor B S hS)
                ((schemeSpaceFunctor B S hS).obj Y₀)) ⟶ U i) (α i) =
      (toposModulePullbackData B S hS).relHomMap
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) A G
        (CostructuredArrow.homMk (pullback.snd (g i).left (g j).left) h₂ :
          (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map
            (pullback.fst (g i).left (g j).left) ≫ (U i).hom) :
              CostructuredArrow (schemeSpaceFunctor B S hS)
                ((schemeSpaceFunctor B S hS).obj Y₀)) ⟶ U j) (α j)) :
    Functor.conjHom ((toposModulePullbackData B S hS).triangle
        (rfl : overlapFst (fun i => (schemeSpaceFunctor B S hS).map (g i).left) i j ≫
          (U i).hom = _)) (α i) =
      Functor.conjHom ((toposModulePullbackData B S hS).triangle
        (overlapSnd_comp_eq (𝟙 _) (fun i => (schemeSpaceFunctor B S hS).map (g i).left)
          (fun i => (U i).hom) (fun i => CostructuredArrow.w (g i)) i j)) (α j) := by
  let D := toposModulePullbackData B S hS
  let hD := toposModulePullbackData_isCoherent B S hS
  let c := fun i => (schemeSpaceFunctor B S hS).map (g i).left
  let p₁ := pullback.fst (g i).left (g j).left
  let p₂ := pullback.snd (g i).left (g j).left
  have h₂ : (schemeSpaceFunctor B S hS).map p₂ ≫ (U j).hom =
      (schemeSpaceFunctor B S hS).map p₁ ≫ (U i).hom := by
    rw [← CostructuredArrow.w (g i), ← CostructuredArrow.w (g j), ← Category.assoc,
      ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  have hpb := HomSituation.isPullback_schemeSpaceFunctor (g i).left (g j).left
  let e := hpb.lift (overlapFst c i j) (overlapSnd c i j) (overlapFst_comp_eq c i j)
  have he₁ : e ≫ (schemeSpaceFunctor B S hS).map p₁ = overlapFst c i j := hpb.lift_fst _ _ _
  have he₂ : e ≫ (schemeSpaceFunctor B S hS).map p₂ = overlapSnd c i j := hpb.lift_snd _ _ _
  have hb : e ≫ ((schemeSpaceFunctor B S hS).map p₁ ≫ (U i).hom) =
      overlapFst c i j ≫ (U i).hom := by
    rw [← Category.assoc, he₁]
  have hba₁ : (e ≫ (schemeSpaceFunctor B S hS).map p₁) ≫ (U i).hom =
      overlapFst c i j ≫ (U i).hom := by rw [he₁]
  have hba₂ : (e ≫ (schemeSpaceFunctor B S hS).map p₂) ≫ (U j).hom =
      overlapFst c i j ≫ (U i).hom := by rw [Category.assoc, h₂]; exact hb
  calc Functor.conjHom (D.triangle (rfl : overlapFst c i j ≫ (U i).hom = _)) (α i)
      = Functor.conjHom (D.triangle hba₁) (α i) :=
        D.conjHom_triangle_congr he₁.symm rfl hba₁ (α i)
    _ = Functor.conjHom (D.triangle hb) (Functor.conjHom (D.triangle
          (rfl : (schemeSpaceFunctor B S hS).map p₁ ≫ (U i).hom = _)) (α i)) :=
        (D.conjHom_triangle_triangle hD rfl hb hba₁ (α i)).symm
    _ = Functor.conjHom (D.triangle hb) (Functor.conjHom (D.triangle h₂) (α j)) :=
        congrArg (Functor.conjHom (D.triangle hb)) (hL h₂)
    _ = Functor.conjHom (D.triangle hba₂) (α j) :=
        D.conjHom_triangle_triangle hD h₂ hb hba₂ (α j)
    _ = _ := D.conjHom_triangle_congr he₂ hba₂ _ (α j)

/-- For modules `A`, `Q`, `P` on the algebraic space of a scheme `Y₀` and `d : Q ⟶ P`, with `A`
and `ker d` quasi-coherent, the functor `(c : Z → Y₀) ↦ {α : c^*A ⟶ c^*Q | α ≫ c^*d = 0}`
satisfies the sheaf condition for every fpqc covering of `Y₀`. -/
theorem isSheafFor_relKerFunctor_of_kernel
    (hA : (((toposModulePullbackData B S hS).pull
      ((schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)).leg (idTest Y₀))).obj
        A).IsQuasicoherentOnSite)
    (hM : (((toposModulePullbackData B S hS).pull
      ((schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)).leg (idTest Y₀))).obj
        (kernel d)).IsQuasicoherentOnSite)
    (hg : IsFpqcCovering B S hS fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom) :
    Presieve.IsSheafFor ((toposModulePullbackData B S hS).relKerFunctor
      (toposModulePullbackData_isCoherent B S hS)
      (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) A d) (Presieve.ofArrows U g) := by
  have hw : IsFlat B S hS ((schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)).leg
      (idTest Y₀)).hom := isFlat_id B S hS ((schemeSpaceFunctor B S hS).obj Y₀).2
  have hqf : ∀ i, IsFlat B S hS ((schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)).leg
      (U i)).hom := fun i => by
    rw [← (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)).w (g i)]
    exact isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS _)
      ((schemeSpaceFunctor B S hS).obj Y₀).2 ((schemeSpaceFunctor B S hS).obj Y₀).2 _ _ (hg.1 i) hw
  intro x hx
  choose α hα _ using fun i => existsUnique_lift_kernel _ (hqf i) d
    (x (g i) (Presieve.ofArrows.mk i)).1 (x (g i) (Presieve.ofArrows.mk i)).2
  have hL : ∀ i j (h₂ : (schemeSpaceFunctor B S hS).map (pullback.snd (g i).left (g j).left) ≫
      (U j).hom = (schemeSpaceFunctor B S hS).map (pullback.fst (g i).left (g j).left) ≫ (U i).hom),
      (toposModulePullbackData B S hS).relHomMap
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) A (kernel d)
        (CostructuredArrow.homMk (pullback.fst (g i).left (g j).left) rfl :
          (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map
            (pullback.fst (g i).left (g j).left) ≫ (U i).hom) :
              CostructuredArrow (schemeSpaceFunctor B S hS)
                ((schemeSpaceFunctor B S hS).obj Y₀)) ⟶ U i) (α i) =
      (toposModulePullbackData B S hS).relHomMap
        (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) A (kernel d)
        (CostructuredArrow.homMk (pullback.snd (g i).left (g j).left) h₂ :
          (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map
            (pullback.fst (g i).left (g j).left) ≫ (U i).hom) :
              CostructuredArrow (schemeSpaceFunctor B S hS)
                ((schemeSpaceFunctor B S hS).obj Y₀)) ⟶ U j) (α j) := by
    intro i j h₂
    let κ := schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)
    let V : CostructuredArrow (schemeSpaceFunctor B S hS) ((schemeSpaceFunctor B S hS).obj Y₀) :=
      CostructuredArrow.mk
        ((schemeSpaceFunctor B S hS).map (pullback.fst (g i).left (g j).left) ≫ (U i).hom)
    let f₁ : V ⟶ U i := CostructuredArrow.homMk (pullback.fst (g i).left (g j).left) rfl
    let f₂ : V ⟶ U j := CostructuredArrow.homMk (pullback.snd (g i).left (g j).left) h₂
    have hfl : IsFlat B S hS ((schemeSpaceFunctor B S hS).map
        (pullback.fst (g i).left (g j).left)).hom :=
      isFlat_of_isPullback_of_isAlgebraicSpace B S hS
        ((IsPullback.of_hasPullback (g i).left (g j).left).map yoneda)
        (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) (hg.1 j)
    have hV : IsFlat B S hS (κ.leg V).hom := by
      rw [← κ.w f₁]
      exact isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
        ((schemeSpaceFunctor B S hS).obj Y₀).2 _ _ hfl (hqf i)
    have : Mono (((toposModulePullbackData B S hS).pull (κ.leg V)).map (kernel.ι d)) :=
      mono_map_kernel_ι _ hV d
    have hcomp : f₁ ≫ g i = f₂ ≫ g j := CostructuredArrow.hom_ext _ _ pullback.condition
    exact (toposModulePullbackData B S hS).relHomMap_eq_of_compatible
      (toposModulePullbackData_isCoherent B S hS) κ A d (kernel.ι d) hx f₁ f₂
      (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j) hcomp (α i) (α j) (hα i) (hα j)
  obtain ⟨δ, hδ, huniq⟩ := existsUnique_relHomMap_eq g A (kernel d) hA hM hg α
    fun i j => conjHom_overlap_eq_of_relHomMap_eq g A (kernel d) i j α (hL i j)
  obtain ⟨t, ht, htδ⟩ := (toposModulePullbackData B S hS).exists_isAmalgamation_of_relHomMap_eq
    (toposModulePullbackData_isCoherent B S hS)
    (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀))
    A d (kernel.ι d) (kernel.condition d) g x δ α hα hδ
  refine ⟨t, ht, fun t' ht' => ?_⟩
  obtain ⟨β, hβ, -⟩ := existsUnique_lift_kernel _ hw d t'.1 t'.2
  have hβδ : β = δ := huniq β fun i => by
    have := mono_map_kernel_ι _ (hqf i) d
    exact (toposModulePullbackData B S hS).relHomMap_eq_of_isAmalgamation
      (toposModulePullbackData_isCoherent B S hS)
      (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) A d (kernel.ι d) ht'
      (Presieve.ofArrows.mk i) β hβ (α i) (hα i)
  subst hβδ
  exact (toposModulePullbackData B S hS).relKerFunctor_obj_ext
    (toposModulePullbackData_isCoherent B S hS)
    (schemesOverCone ((schemeSpaceFunctor B S hS).obj Y₀)) A d (hβ.symm.trans htδ.symm)

end Core

/-! ### The sheaf property of the degree-zero sections functor -/

section Sheaf

variable {X : AlgebraicSpaces B S hS} (P₀ : CochainComplex (toposModules B S hS X) ℤ)
  (hP₀ : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀))
  {K : derivedModules B S hS X} (hK : IsPseudoCoherentObject K)
  (e : DerivedCategory.Q.obj P₀ ≅ K)

include hP₀ hK e in
/-- The degree-zero sections functor satisfies the sheaf condition for an fpqc covering of a
test scheme. -/
theorem isSheafFor_degreeZeroSectionsFunctor {T : SchemesOver X} {J : Type (u + 1)}
    {U : J → SchemesOver X} (g : ∀ i, U i ⟶ T)
    (hg : IsFpqcCovering B S hS fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom) :
    Presieve.IsSheafFor (degreeZeroSectionsFunctor (schemesOverCone X) P₀)
      (Presieve.ofArrows U g) := by
  let Y := (schemeSpaceFunctor B S hS).obj T.left
  let Pk := (((toposModulePullbackData B S hS).pull T.hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P₀
  let U' : J → CostructuredArrow (schemeSpaceFunctor B S hS) Y := fun i =>
    CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map (g i).left)
  let g' : ∀ i, U' i ⟶ idTest T.left := fun i =>
    CostructuredArrow.homMk (g i).left (Category.comp_id _)
  let eT : (CostructuredArrow.map T.hom).obj (idTest T.left) ≅ T :=
    CostructuredArrow.isoMk (Iso.refl _) (by simp)
  let eU : ∀ i, (CostructuredArrow.map T.hom).obj (U' i) ≅ U i := fun i =>
    CostructuredArrow.isoMk (Iso.refl _) (by
      simp only [Iso.refl_hom]
      exact (CostructuredArrow.w (g i)).symm)
  have hw : ∀ i, (eU i).hom ≫ g i = (CostructuredArrow.map T.hom).map (g' i) ≫ eT.hom :=
    fun i => CostructuredArrow.hom_ext _ _ (by simp [eU, eT, g'])
  have hd : (kernel (Pk.fromOpcycles 0 1)).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (IsLimit.conePointUniqueUpToIso (Pk.homologyIsKernel 0 1 (by simp))
        (limit.isLimit _))
      (isQuasicoherentOnSite_homology_pull_of_isPseudoCoherentObject P₀ hP₀ hK e T.hom 0)
  exact Presieve.isSheafFor_ofArrows_of_natIso (CostructuredArrow.map T.hom)
    (degreeZeroSectionsPrecompIso T.hom P₀) eT g g' eU hw
    (isSheafFor_relKerFunctor_of_kernel (SheafOfModules.unit _) (Pk.fromOpcycles 0 1) g'
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
        (SheafOfModules.isQuasicoherentOnSite_unit _))
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hd) hg)

include hP₀ hK e in
/-- For a pseudo-coherent object `K` of `D(𝒪_X)` represented by a K-flat complex `P₀`
with flat terms, the functor `(g : T → X) ↦ H⁰(T, H⁰(g^*P₀))` on the schemes over `X` satisfies
the sheaf property for the fpqc topology. -/
theorem isSheaf_degreeZeroSectionsFunctor :
    Presheaf.IsSheaf (fpqcTopology X) (degreeZeroSectionsFunctor (schemesOverCone X) P₀) := by
  rw [isSheaf_iff_isSheaf_of_type, fpqcTopology,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro T R hR
  rw [← Presieve.presieve₀_preZeroHypercover R] at hR ⊢
  simp only [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR
  exact isSheafFor_degreeZeroSectionsFunctor P₀ hP₀ hK e R.preZeroHypercover.f
    (represented_fpqc_family B S hS _ _ _ hR)

end Sheaf

end AlgebraicGeometry.Space

end
