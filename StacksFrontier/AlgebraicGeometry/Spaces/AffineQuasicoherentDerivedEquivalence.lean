module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineReconstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors

/-!
# `D_QCoh` of an affine representable algebraic space is `D(R)`

Let `U` be an object of the big fppf site over `S` whose underlying scheme is affine, with ring
of global functions `R`, and let `yoneda.obj U` be the algebraic space it represents.  This file
proves that the derived associated-module functor

`Φ : D(R) ⥤ D_QCoh(𝒪_{yoneda.obj U})`

is an equivalence of triangulated categories, with quasi-inverse the derived sections functor
`RΓ`.  It is the algebraic-space counterpart of Stacks 06Z0 for an affine scheme
(`AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence`).

## Main definitions

* `AlgebraicGeometry.Space.representedAffineAssociated`: the associated-module functor
  `Mod(R) ⥤ Mod(𝒪_{yoneda.obj U})`, with its right adjoint
  `AlgebraicGeometry.Space.representedAffineSections`.
* `AlgebraicGeometry.Space.representedAffineDerivedAssociated` (`Φ`) and
  `AlgebraicGeometry.Space.representedAffineDerivedSections` (`RΓ`), with the adjunction
  `AlgebraicGeometry.Space.representedAffineDerivedAdjunction`.
* `AlgebraicGeometry.Space.representedAffineDerivedEquivalence`: the equivalence
  `D(R) ≌ D_QCoh(𝒪_{yoneda.obj U})`.

## Main results

* `AlgebraicGeometry.Space.isIso_representedAffineDerivedAdjunction_unit`: the unit of
  `Φ ⊣ RΓ` is invertible.
* `AlgebraicGeometry.Space.isEquivalence_representedAffineDerivedAssociatedQcoh`: `Φ` is an
  equivalence onto `D_QCoh`.
* `AlgebraicGeometry.Space.isIso_representedAffineDerivedAdjunction_counit_app`: the counit
  `Φ(RΓ(E)) ⟶ E` is invertible for `E` in `D_QCoh`.
* `AlgebraicGeometry.Space.isStrictlyPerfect_representedAffineAssociated_mapHomologicalComplex`
  and `AlgebraicGeometry.Space.exists_strictlyPerfect_iso_representedAffineDerivedAssociated_obj`:
  a bounded complex of finite projective `R`-modules goes to a strictly perfect complex, so a
  splitting `K ≅ R ⊕ P` in `D(R)` becomes a splitting `Φ(K) ≅ 𝒪 ⊕ P'`.

## References

* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

/-! ### Two general lemmas -/

section General

variable {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']

/-- If `H ∘ F` agrees with `G ∘ H'` up to a natural isomorphism, `H'` and `G` are bijective on the
relevant morphism sets and `H` is injective on the morphisms between the images under `F`, then
`F` is bijective on morphisms `X ⟶ Y`. -/
theorem bijective_map_of_iso_comp (F : C ⥤ D) (H : D ⥤ E) (H' : C ⥤ E') (G : E' ⥤ E)
    (α : F ⋙ H ≅ H' ⋙ G) (X Y : C)
    (h₁ : Function.Bijective (fun f : X ⟶ Y => H'.map f))
    (h₂ : Function.Bijective (fun f : H'.obj X ⟶ H'.obj Y => G.map f))
    (h₃ : Function.Injective (fun f : F.obj X ⟶ F.obj Y => H.map f)) :
    Function.Bijective (fun f : X ⟶ Y => F.map f) := by
  have hk : (fun f : X ⟶ Y => H.map (F.map f)) =
      (fun g => α.hom.app X ≫ g ≫ α.inv.app Y) ∘ (fun f => G.map f) ∘ (fun f => H'.map f) := by
    funext f
    have := α.hom.naturality f
    simp only [Functor.comp_map] at this
    simp only [Function.comp_apply, ← Category.assoc, ← this]
    simp
  have hc : Function.Bijective (fun g : G.obj (H'.obj X) ⟶ G.obj (H'.obj Y) =>
      α.hom.app X ≫ g ≫ α.inv.app Y) :=
    (Iso.homCongr (α.app X).symm (α.app Y).symm).bijective
  have hb : Function.Bijective (fun f : X ⟶ Y => H.map (F.map f)) := by
    rw [hk]
    exact hc.comp (h₂.comp h₁)
  refine ⟨fun a b h => hb.1 (by simp only at h ⊢; rw [h]), fun y => ?_⟩
  obtain ⟨x, hx⟩ := hb.2 (H.map y)
  exact ⟨x, h₃ hx⟩

/-- Precomposition with an isomorphism is bijective. -/
theorem bijective_iso_comp {X Y Z : C} (e : X ≅ Y) :
    Function.Bijective (fun g : Y ⟶ Z => e.hom ≫ g) :=
  e.symm.homFromEquiv.bijective

end General

/-- A map of `R`-modules is an isomorphism as soon as composing with it is bijective on maps
out of `R`. -/
theorem isIso_of_bijective_comp_moduleCat {R : Type u} [Ring R] {A A' : ModuleCat.{u} R}
    (φ : A ⟶ A') (h : Function.Bijective (fun g : ModuleCat.of R R ⟶ A => g ≫ φ)) : IsIso φ := by
  have hb : Function.Bijective φ := by
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · have := h.1 (a₁ := ModuleCat.ofHom (LinearMap.toSpanSingleton R A a))
        (a₂ := ModuleCat.ofHom (LinearMap.toSpanSingleton R A b)) (by
          ext
          simp [hab])
      simpa using congrArg (fun g => g.hom (1 : R)) this
    · obtain ⟨g, hg⟩ := h.2 (ModuleCat.ofHom (LinearMap.toSpanSingleton R A' c))
      refine ⟨g.hom 1, ?_⟩
      simpa using congrArg (fun g => g.hom (1 : R)) hg
  exact (ConcreteCategory.isIso_iff_bijective φ).2 hb

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- The ring `R = Γ(U, 𝒪_U)` of the affine scheme underlying `U`. -/
abbrev representedAffineRing : CommRingCat.{u} := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)

/-- **`Mod(R) ≌ QCoh(𝒪_{yoneda.obj U})`**: the affine case of Stacks 03DX (2), read on the small
étale site of the algebraic space represented by `U`. -/
def representedAffineAssoc :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ≌
      QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  (affineQuasicoherentModulesEquiv _).trans (representedQuasicoherentSheavesEquivalence B S hS U)

/-- The associated `𝒪`-module of an `R`-module, on the small étale site of `yoneda.obj U`:
`M ↦ M^~`, pulled back along `U ≅ Spec R`, read on the small étale site of `U`, and transported
to the small étale site of the algebraic space `yoneda.obj U`. -/
def representedAffineAssociated :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⥤
      Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⋙
    Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ⋙
    _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    (representedSmallEtaleModuleEquivalence B S hS U).functor

/-- The sections functor right adjoint to `AlgebraicGeometry.Space.representedAffineAssociated`. -/
abbrev representedAffineSections :
    Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
      ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  (representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ⋙
    moduleSpecΓFunctor

/-- The associated module is left adjoint to the sections functor. -/
def representedAffineAssociatedAdjunction :
    representedAffineAssociated B S hS U ⊣ representedAffineSections B S hS U :=
  (tilde.adjunction).comp ((Scheme.Modules.pullbackPushforwardAdjunction _).comp
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction _ _ _).comp
      (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction))

/-- The associated module is `AlgebraicGeometry.Space.representedAffineAssoc` followed by the
inclusion of the quasi-coherent modules. -/
def representedAffineAssociatedIso :
    (representedAffineAssoc B S hS U).functor ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
            (isAlgebraicSpace_yoneda B S hS U)).O))) ≅
      representedAffineAssociated B S hS U :=
  Functor.isoWhiskerRight (affineQuasicoherentModulesEquivCompι _)
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS U).functor) ≪≫
    Functor.associator _ _ _

section Derived

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-- The sections functor is additive. -/
instance additive_representedAffineSections :
    (representedAffineSections B S hS U).Additive :=
  have := (representedAffineAssociatedAdjunction B S hS U).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- The associated-module functor is additive. -/
instance additive_representedAffineAssociated :
    (representedAffineAssociated B S hS U).Additive :=
  (representedAffineAssociatedAdjunction B S hS U).left_adjoint_additive

/-- The associated-module functor preserves finite colimits. -/
instance preservesFiniteColimits_representedAffineAssociated :
    PreservesFiniteColimits (representedAffineAssociated B S hS U) :=
  have := (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- The associated-module functor preserves finite limits. -/
instance preservesFiniteLimits_representedAffineAssociated :
    PreservesFiniteLimits (representedAffineAssociated B S hS U) :=
  letI := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U)
  letI := isClosedUnderCokernels_quasicoherentSheaves B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U)
  preservesFiniteLimits_of_natIso (representedAffineAssociatedIso B S hS U)

/-- **`Φ : D(R) ⥤ D(𝒪_{yoneda.obj U})`**, the functor induced on derived categories by the exact
associated-module functor. -/
abbrev representedAffineDerivedAssociated :
    DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
      DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :=
  (representedAffineAssociated B S hS U).mapDerivedCategory

/-- The associated module of `R` is the structure sheaf. -/
def representedAffineAssociatedObjUnitIso :
    (representedAffineAssociated B S hS U).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≅
      structureModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :=
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    (representedSmallEtaleModuleEquivalence B S hS U).functor).mapIso
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).mapIso
        tildeSelf ≪≫ Scheme.Modules.pullbackUnitIso _)) ≪≫
    representedAssociatedModuleObjUnitIso B S hS U (isAlgebraicSpace_yoneda B S hS U)

/-- The sections functor has a total right derived functor, computed on K-injective
resolutions. -/
instance hasRightDerivedFunctor_representedAffineSections :
    ((representedAffineSections B S hS U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
        (ComplexShape.up ℤ)) :=
  have := Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective
    ((representedAffineSections B S hS U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (exists_quasiIso_isKInjective_modules B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **`RΓ : D(𝒪_{yoneda.obj U}) ⥤ D(R)`**, the total right derived functor of the sections
functor `AlgebraicGeometry.Space.representedAffineSections`. -/
abbrev representedAffineDerivedSections :
    DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) ⥤
      DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :=
  ((representedAffineSections B S hS U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
      (ComplexShape.up ℤ))

/-- `RΓ` is a triangulated functor. -/
instance isTriangulated_representedAffineDerivedSections :
    (representedAffineDerivedSections B S hS U).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    (exists_quasiIso_isKInjective_modules B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    _ (representedAffineDerivedSections B S hS U) (Functor.totalRightDerivedUnit _ _ _)

/-- **`Φ ⊣ RΓ`**, Stacks 09T5 for the exact associated-module functor. -/
def representedAffineDerivedAdjunction :
    representedAffineDerivedAssociated B S hS U ⊣ representedAffineDerivedSections B S hS U :=
  Stacks.DerivedFunctor.derivedAdjunction (representedAffineAssociatedAdjunction B S hS U)
    (representedAffineDerivedSections B S hS U) (Functor.totalRightDerivedUnit _ _ _)
    (exists_quasiIso_isKInjective_modules B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))

end Derived

/-! ### Morphisms out of `𝒪[q]` -/

section Generator

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}

/-- **`H^q` is injective on morphisms `𝒪_X[q] ⟶ E`** for `E` in `D_QCoh(𝒪_X)`, when the small
étale site has a final object with affine underlying scheme. -/
theorem homologyFunctor_map_injective_fromUnit (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) (q : ℤ) (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hE : QcohDerived B S hS ⟨X, hX⟩ E) :
    Function.Injective (fun x : (DerivedCategory.singleFunctor _ q).obj
        (structureModule ⟨X, hX⟩) ⟶ E =>
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) q).map x) := by
  intro f g hfg
  simp only at hfg
  let c : (DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩) ≅
      ((DerivedCategory.singleFunctor _ q).obj (structureModule ⟨X, hX⟩))⟦q⟧ :=
    (((DerivedCategory.singleFunctors (Modules.{u, u} B S hS X hX)).shiftIso q 0 q
      (add_zero q)).app (structureModule ⟨X, hX⟩)).symm
  let e := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).shiftIso q 0 q
    (add_zero q)
  have hsh : ∀ x : (DerivedCategory.singleFunctor _ q).obj (structureModule ⟨X, hX⟩) ⟶ E,
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).map (x⟦q⟧') =
        e.hom.app _ ≫
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).shift q).map x ≫
            e.inv.app E := fun x => by
    rw [← Category.assoc, ← e.hom.naturality x, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
    rfl
  have h0 : (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).map
        (c.hom ≫ f⟦q⟧') =
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).map (c.hom ≫ g⟦q⟧') := by
    rw [Functor.map_comp, Functor.map_comp, hsh, hsh]
    exact congrArg (fun z => (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).map
      c.hom ≫ e.hom.app _ ≫ z ≫ e.inv.app E) hfg
  exact (shiftFunctor _ q).map_injective ((cancel_epi c.hom).mp
    ((bijective_homologyFunctor_map_fromUnit T hT hTa (E⟦q⟧) (qcohDerived_shift E q hE)).1 h0))

end Generator

/-! ### Finite projective complexes go to strictly perfect complexes -/

/-- A finite projective `R`-module is a retract of a finite coproduct of copies of `R`. -/
theorem exists_retract_sigma_of_finite_projective {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (s : M ⟶ ∐ (fun _ : ULift.{u} (Fin n) => ModuleCat.of R R))
      (t : ∐ (fun _ : ULift.{u} (Fin n) => ModuleCat.of R R) ⟶ M), s ≫ t = 𝟙 M := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R M
  let t : ∐ (fun _ : ULift.{u} (Fin n) => ModuleCat.of R R) ⟶ M :=
    Sigma.desc fun i => ModuleCat.ofHom (LinearMap.toSpanSingleton R M (g (Pi.single i.down 1)))
  have ht : Epi t := by
    rw [ModuleCat.epi_iff_surjective]
    intro m
    obtain ⟨v, rfl⟩ := hg m
    refine ⟨∑ i : Fin n, (Sigma.ι (fun _ : ULift.{u} (Fin n) => ModuleCat.of R R) ⟨i⟩).hom (v i),
      ?_⟩
    rw [map_sum]
    have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : R) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ModuleCat.comp_apply, Sigma.ι_comp_desc, map_smul]
    simp
  have : Projective M := M.projective_of_categoryTheory_projective
  exact ⟨n, Projective.factorThru (𝟙 M) t, t, Projective.factorThru_comp _ _⟩

section StrictlyPerfect

attribute [local instance 5000] SheafOfModules.instAbelian

/-- The associated module of a finite projective `R`-module is a direct summand of a finite free
module. -/
theorem isDirectSummandOfFiniteFree_representedAffineAssociated_obj
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    [Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) M]
    [Module.Projective Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) M] :
    IsDirectSummandOfFiniteFree.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O))
      ((representedAffineAssociated B S hS U).obj M) := by
  obtain ⟨n, s, t, hst⟩ := exists_retract_sigma_of_finite_projective M
  have : PreservesColimitsOfSize.{u, u} (representedAffineAssociated B S hS U) :=
    (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
  have : HasFiniteBiproducts (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) := Abelian.hasFiniteBiproducts
  have : HasFiniteCoproducts (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) := hasFiniteCoproducts_of_hasFiniteBiproducts _
  have : HasColimitsOfShape (Discrete (ULift.{u} (Fin n))) (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) := hasColimitsOfShape_discrete _ _
  let F := representedAffineAssociated B S hS U
  let e : F.obj (∐ (fun _ : ULift.{u} (Fin n) =>
        ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) ≅
      SheafOfModules.free (ULift.{u} (Fin n)) :=
    PreservesCoproduct.iso F _ ≪≫
      Sigma.mapIso (fun _ => representedAffineAssociatedObjUnitIso B S hS U)
  rw [isDirectSummandOfFiniteFree_iff_free]
  exact ⟨n, F.map s ≫ e.hom, e.inv ≫ F.map t, by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp, hst, F.map_id]⟩

/-- **The associated complex of a bounded complex of finite projective `R`-modules is strictly
perfect.** -/
theorem isStrictlyPerfect_representedAffineAssociated_mapHomologicalComplex
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) (a b : ℤ)
    (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfin : ∀ j, Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (P.X j))
    (hproj : ∀ j, Module.Projective Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (P.X j)) :
    IsStrictlyPerfect.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O))
      (((representedAffineAssociated B S hS U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) := by
  refine ⟨(Set.finite_Icc a b).subset fun j hj => ?_, fun j => ?_⟩
  · simp only [Set.mem_ofPred_eq] at hj
    simp only [Set.mem_Icc]
    by_contra hne
    apply hj
    refine Functor.map_isZero (representedAffineAssociated B S hS U) ?_
    rcases not_and_or.mp hne with h | h
    · exact P.isZero_of_isStrictlyGE a j (by omega)
    · exact P.isZero_of_isStrictlyLE b j (by omega)
  · exact isDirectSummandOfFiniteFree_representedAffineAssociated_obj B S hS U (P.X j)

end StrictlyPerfect

/-! ### The unit of `Φ ⊣ RΓ` is invertible -/

section Unit

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-- The associated-module functor is fully faithful. -/
def representedAffineAssociatedFullyFaithful :
    (representedAffineAssociated B S hS U).FullyFaithful :=
  ((representedAffineAssoc B S hS U).fullyFaithfulFunctor.comp
    (ObjectProperty.fullyFaithfulι _)).ofIso (representedAffineAssociatedIso B S hS U)

/-- The associated module of an `R`-module is quasi-coherent. -/
theorem isQuasicoherentOnSite_representedAffineAssociated_obj
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((representedAffineAssociated B S hS U).obj M).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso ((representedAffineAssociatedIso B S hS U).app M)
    ((representedAffineAssoc B S hS U).functor.obj M).property

/-- `Φ` lands in `D_QCoh`. -/
theorem qcohDerived_representedAffineDerivedAssociated_obj
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
      ((representedAffineDerivedAssociated B S hS U).obj M) := fun n =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((representedAffineAssociated B S hS U).mapDerivedCategoryHomologyIso n).app M).symm
    (isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U _)

/-- The final chart of the small étale site of `yoneda.obj U`. -/
abbrev representedAffineFinalChart : SmallEtale B S hS (yoneda.obj U) :=
  chartOfIso B S hS U (Iso.refl _)

/-- The final chart of the small étale site of `yoneda.obj U` is affine. -/
theorem isAffineChart_representedAffineFinalChart :
    IsAffineChart B S hS (yoneda.obj U) (representedAffineFinalChart B S hS U) :=
  ‹IsAffine ((BigFppfOver.toScheme B S hS).obj U)›

/-- `Φ(R[q]) ≅ 𝒪[q]`. -/
def representedAffineDerivedAssociatedSingleUnitIso (q : ℤ) :
    (representedAffineDerivedAssociated B S hS U).obj
        ((DerivedCategory.singleFunctor _ q).obj
          (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) ≅
      (DerivedCategory.singleFunctor _ q).obj
        (structureModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) :=
  ((representedAffineAssociated B S hS U).mapDerivedCategorySingleFunctor q).app _ ≪≫
    (DerivedCategory.singleFunctor _ q).mapIso (representedAffineAssociatedObjUnitIso B S hS U)

/-- **`Φ` is bijective on morphisms out of `R[q]`.** -/
theorem bijective_representedAffineDerivedAssociated_map_single (q : ℤ)
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor _ q).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⟶ M =>
      (representedAffineDerivedAssociated B S hS U).map f) := by
  set R₀ := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  have : Projective R₀ := ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} _)
  refine bijective_map_of_iso_comp (representedAffineDerivedAssociated B S hS U)
    (DerivedCategory.homologyFunctor _ q) (DerivedCategory.homologyFunctor _ q)
    (representedAffineAssociated B S hS U)
    ((representedAffineAssociated B S hS U).mapDerivedCategoryHomologyIso q) _ M ?_
    ((representedAffineAssociatedFullyFaithful B S hS U).map_bijective _ _) ?_
  · have hk : (fun f : (DerivedCategory.singleFunctor _ q).obj R₀ ⟶ M =>
        (DerivedCategory.homologyFunctor _ q).map f) =
        (fun g => ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ q).app R₀).hom ≫ g) ∘
          DerivedCategory.homologyFromSingle R₀ M q := by
      funext f
      rw [Function.comp_apply, DerivedCategory.homologyFromSingle_apply, ← Category.assoc,
        Iso.app_hom, Iso.hom_inv_id_app, Category.id_comp]
    rw [hk]
    exact (bijective_iso_comp ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ q).app
      R₀)).comp (DerivedCategory.bijective_homologyFromSingle_of_projective R₀ M q)
  · intro a b hab
    have hab' : (DerivedCategory.homologyFunctor _ q).map a =
        (DerivedCategory.homologyFunctor _ q).map b := hab
    set i := representedAffineDerivedAssociatedSingleUnitIso B S hS U q
    have := homologyFunctor_map_injective_fromUnit (representedAffineFinalChart B S hS U)
      (isTerminalChartOfIso U (Iso.refl _)) (isAffineChart_representedAffineFinalChart B S hS U) q
      _ (qcohDerived_representedAffineDerivedAssociated_obj B S hS U M)
      (a₁ := i.inv ≫ a) (a₂ := i.inv ≫ b) (by
        change (DerivedCategory.homologyFunctor _ q).map (i.inv ≫ a) =
          (DerivedCategory.homologyFunctor _ q).map (i.inv ≫ b)
        rw [Functor.map_comp, Functor.map_comp, hab'])
    exact (cancel_epi i.inv).mp this

/-- **The unit of `Φ ⊣ RΓ` is invertible.** -/
instance isIso_representedAffineDerivedAdjunction_unit :
    IsIso (representedAffineDerivedAdjunction B S hS U).unit := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M => ?_
  set adj := representedAffineDerivedAdjunction B S hS U
  set R₀ := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  have : Projective R₀ := ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} _)
  rw [DerivedCategory.isIso_iff]
  intro q
  refine isIso_of_bijective_comp_moduleCat _ ?_
  have hu : Function.Bijective (fun g : (DerivedCategory.singleFunctor _ q).obj R₀ ⟶ M =>
      g ≫ adj.unit.app M) := by
    have hk : (fun g : (DerivedCategory.singleFunctor _ q).obj R₀ ⟶ M => g ≫ adj.unit.app M) =
        (adj.homEquiv _ _) ∘ (fun f => (representedAffineDerivedAssociated B S hS U).map f) := by
      funext g
      simp only [Function.comp_apply, Adjunction.homEquiv_unit]
      exact adj.unit.naturality g
    rw [hk]
    exact (adj.homEquiv _ _).bijective.comp
      (bijective_representedAffineDerivedAssociated_map_single B S hS U q M)
  have h₁ := DerivedCategory.bijective_homologyFromSingle_of_projective R₀ M q
  have h₂ := DerivedCategory.bijective_homologyFromSingle_of_projective R₀
    ((representedAffineDerivedAssociated B S hS U ⋙ representedAffineDerivedSections B S hS U).obj
      M) q
  have hk : (DerivedCategory.homologyFromSingle R₀ _ q) ∘
      (fun g : (DerivedCategory.singleFunctor _ q).obj R₀ ⟶ M => g ≫ adj.unit.app M) =
      (fun g => g ≫ (DerivedCategory.homologyFunctor _ q).map (adj.unit.app M)) ∘
        (DerivedCategory.homologyFromSingle R₀ M q) := by
    funext g
    exact DerivedCategory.homologyFromSingle_comp R₀ M q g _
  have := h₂.comp hu
  rw [hk] at this
  exact (Function.Bijective.of_comp_iff _ h₁).mp this

/-- **A splitting `K ≅ R ⊕ P` in `D(R)` with `P` a bounded complex of finite projective modules in
degrees `≥ a` becomes a splitting `Φ(K) ≅ 𝒪 ⊕ P'` with `P'` strictly perfect in degrees `≥ a`.** -/
theorem exists_strictlyPerfect_iso_representedAffineDerivedAssociated_obj
    (K : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (P : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) (a b : ℤ)
    (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfin : ∀ j, Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (P.X j))
    (hproj : ∀ j, Module.Projective Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (P.X j))
    (e : K ≅ (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⊞ DerivedCategory.Q.obj P) :
    ∃ P' : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)) ℤ,
      IsStrictlyPerfect.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O)) P' ∧ P'.IsStrictlyGE a ∧
      Nonempty ((representedAffineDerivedAssociated B S hS U).obj K ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (structureModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) ⊞
          DerivedCategory.Q.obj P') := by
  let Φ₀ := representedAffineAssociated B S hS U
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (representedAffineDerivedAssociated B S hS U)
  have : Φ₀.Faithful := (representedAffineAssociatedFullyFaithful B S hS U).faithful
  exact ⟨(Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    isStrictlyPerfect_representedAffineAssociated_mapHomologicalComplex B S hS U P a b hGE hLE
      hfin hproj,
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := P) Φ₀ a).2 hGE,
    ⟨(representedAffineDerivedAssociated B S hS U).mapIso e ≪≫
      (representedAffineDerivedAssociated B S hS U).mapBiprod _ _ ≪≫
      biprod.mapIso (representedAffineDerivedAssociatedSingleUnitIso B S hS U 0)
        (Φ₀.mapDerivedCategoryFactors.app P)⟩⟩

/-! ### The equivalence -/

/-- `Φ`, as a functor `D(R) ⥤ D_QCoh(𝒪_{yoneda.obj U})`. -/
def representedAffineDerivedAssociatedQcoh :
    DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) :=
  ObjectProperty.lift _ (representedAffineDerivedAssociated B S hS U)
    (qcohDerived_representedAffineDerivedAssociated_obj B S hS U)

/-- `Φ : D(R) ⥤ D_QCoh(𝒪_{yoneda.obj U})` commutes with shifts. -/
instance commShift_representedAffineDerivedAssociatedQcoh :
    (representedAffineDerivedAssociatedQcoh B S hS U).CommShift ℤ :=
  inferInstanceAs ((ObjectProperty.lift _ _ _).CommShift ℤ)

/-- `Φ : D(R) ⥤ D_QCoh(𝒪_{yoneda.obj U})` is a triangulated functor. -/
instance isTriangulated_representedAffineDerivedAssociatedQcoh :
    (representedAffineDerivedAssociatedQcoh B S hS U).IsTriangulated :=
  inferInstanceAs (ObjectProperty.lift _ _ _).IsTriangulated

/-- `RΓ`, restricted to `D_QCoh(𝒪_{yoneda.obj U})`. -/
abbrev representedAffineDerivedSectionsQcoh :
    QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) ⥤
      DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :=
  ObjectProperty.ι _ ⋙ representedAffineDerivedSections B S hS U

/-- `Φ ⊣ RΓ` on `D_QCoh`. -/
def representedAffineDerivedQcohAdjunction :
    representedAffineDerivedAssociatedQcoh B S hS U ⊣
      representedAffineDerivedSectionsQcoh B S hS U :=
  Adjunction.restrictFullyFaithful (representedAffineDerivedAdjunction B S hS U)
    (Functor.FullyFaithful.id _) (ObjectProperty.fullyFaithfulι _)
    (Functor.leftUnitor _ ≪≫ (ObjectProperty.liftCompιIso _ _ _).symm)
    (Functor.rightUnitor _).symm

/-- `Φ` is fully faithful. -/
def representedAffineDerivedAssociatedFullyFaithful :
    (representedAffineDerivedAssociated B S hS U).FullyFaithful :=
  Adjunction.fullyFaithfulLOfIsIsoUnit (representedAffineDerivedAdjunction B S hS U)

/-- `Φ : D(R) ⥤ D_QCoh(𝒪_{yoneda.obj U})` is faithful. -/
instance faithful_representedAffineDerivedAssociatedQcoh :
    (representedAffineDerivedAssociatedQcoh B S hS U).Faithful :=
  have := (representedAffineDerivedAssociatedFullyFaithful B S hS U).faithful
  have : (representedAffineDerivedAssociatedQcoh B S hS U ⋙ ObjectProperty.ι _).Faithful :=
    inferInstanceAs (representedAffineDerivedAssociated B S hS U).Faithful
  Functor.Faithful.of_comp _ (ObjectProperty.ι _)

/-- `Φ : D(R) ⥤ D_QCoh(𝒪_{yoneda.obj U})` is full. -/
instance full_representedAffineDerivedAssociatedQcoh :
    (representedAffineDerivedAssociatedQcoh B S hS U).Full :=
  have := (representedAffineDerivedAssociatedFullyFaithful B S hS U).full
  have : (representedAffineDerivedAssociatedQcoh B S hS U ⋙ ObjectProperty.ι _).Full :=
    inferInstanceAs (representedAffineDerivedAssociated B S hS U).Full
  Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)

/-- **`RΓ` has zero kernel on `D_QCoh`.** -/
theorem isZero_of_isZero_representedAffineDerivedSectionsQcoh_obj
    (E : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    (hE : IsZero ((representedAffineDerivedSectionsQcoh B S hS U).obj E)) : IsZero E := by
  refine ObjectProperty.isZero_fullSubcategory_of_isZero_obj ?_
  refine isZero_of_forall_homFromUnit_eq_zero (representedAffineFinalChart B S hS U)
    (isTerminalChartOfIso U (Iso.refl _)) (isAffineChart_representedAffineFinalChart B S hS U)
    E.obj E.property fun q g => ?_
  set adj := representedAffineDerivedAdjunction B S hS U
  set i := representedAffineDerivedAssociatedSingleUnitIso B S hS U 0
  have hZ : IsZero ((representedAffineDerivedSections B S hS U).obj (E.obj⟦q⟧)) :=
    IsZero.of_iso ((shiftFunctor _ q).map_isZero hE)
      (((representedAffineDerivedSections B S hS U).commShiftIso q).app E.obj)
  have h0 : adj.homEquiv _ _ (i.hom ≫ g) = 0 := hZ.eq_of_tgt _ _
  have h1 : i.hom ≫ g = 0 := by
    rw [← (adj.homEquiv _ _).symm_apply_apply (i.hom ≫ g), h0, Adjunction.homEquiv_counit,
      Functor.map_zero, Limits.zero_comp]
  simpa using congrArg (i.inv ≫ ·) h1

/-- **`Φ : D(R) ⥤ D_QCoh(𝒪_{yoneda.obj U})` is an equivalence.** -/
instance isEquivalence_representedAffineDerivedAssociatedQcoh :
    (representedAffineDerivedAssociatedQcoh B S hS U).IsEquivalence :=
  isEquivalence_of_fullyFaithful_of_adjunction_of_ker_eq_zero _ _
    (representedAffineDerivedQcohAdjunction B S hS U)
    (isZero_of_isZero_representedAffineDerivedSectionsQcoh_obj B S hS U)

/-- **`D(R) ≌ D_QCoh(𝒪_{yoneda.obj U})`** for `U` with affine underlying scheme `Spec R`. -/
def representedAffineDerivedEquivalence :
    DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≌
      QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) :=
  (representedAffineDerivedAssociatedQcoh B S hS U).asEquivalence

/-- **The counit `Φ(RΓ(E)) ⟶ E` is invertible** for `E` in `D_QCoh(𝒪_{yoneda.obj U})`. -/
theorem isIso_representedAffineDerivedAdjunction_counit_app
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hE : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E) :
    IsIso ((representedAffineDerivedAdjunction B S hS U).counit.app E) := by
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := representedAffineDerivedAssociatedQcoh B S hS U)
    (⟨E, hE⟩ : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
  have := (representedAffineDerivedAssociatedFullyFaithful B S hS U).full
  have := (representedAffineDerivedAssociatedFullyFaithful B S hS U).faithful
  exact Adjunction.isIso_counit_app_of_iso _ ((ObjectProperty.ι _).mapIso e.symm)

/-- **`RΓ` is left t-exact**: `RΓ(E)` has no cohomology below a degree below which `E` has none. -/
theorem isGE_representedAffineDerivedSections_obj
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))) (n : ℤ) [E.IsGE n] :
    ((representedAffineDerivedSections B S hS U).obj E).IsGE n :=
  Stacks.DerivedFunctor.isGE_totalRightDerived_obj (representedAffineSections B S hS U) E n

end Unit

end AlgebraicGeometry.Space

end
