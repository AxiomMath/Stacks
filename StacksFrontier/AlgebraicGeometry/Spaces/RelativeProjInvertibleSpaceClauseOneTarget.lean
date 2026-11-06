module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceSchemeHomBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneChartMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModulePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PresentationPullbackDescent

/-!
# The target square of clause (1) of Stacks 0D2Z at a scheme point of `U(ψ)`

Clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)` (the hypothesis of
`…InvertibleTwistingRestriction.clauseOneSections_thetaOfFamily` for the family of chart maps) is
pasted from three squares: the source square
`…InvertibleTwistingRestriction.clauseOneSource_square_of_chartSourceIso`, the scheme-level
clause (1) of Tag 01O9 on `W`
(`…InvertibleTwistingRestriction.quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartTheta`),
and the target square, which reads `w^*ψ` on `W` back as the inverse image along `w` of the `ψ`
leg.  This file proves the pieces of the target square.

## Main results

* `…RelativeProjInvertibleMorphism.homEquiv_symm_twistingOfUnitalHom_psi_comp_powCompare`: for
  the quadruple `twistingOfUnitalHom (𝟙 T) 𝒜 ℒ Φ` over the identity of a scheme `T`, the
  component `ψ_d` of Tag 01O8 read back through the adjunction of `𝟙_T` and through
  `ℒ^{⊗ d} ≅ ℒ^{⊗ d}` of the iterated and integral tensor powers is `Φ_d`.
* `AlgebraicGeometry.Space.pointComparison_app_eq_of_eq_id`: the comparison of restricted
  algebras along a morphism of test objects equal to the identity is the identification
  `(𝟙_T)^*N ≅ N`.
* `…RelativeProjSituation.pointTwisting_psi_homEquiv_symm_comp_powCompare`: the same at the
  restriction `w^*ψ` of `ψ` to a scheme point (`…RelativeProjSituation.pointTwisting`), where `Φ`
  is the identification `(𝟙_W)^*((f ∘ w)^*𝒜) = (f ∘ w)^*𝒜` followed by
  `AlgebraicGeometry.Space.pointPsi`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- **The component `ψ_d` of the datum of Tag 01O8 of a quadruple over the identity, read back.**
For a unital homomorphism `Φ : (𝟙_T)^*𝒜 ⟶ ⨁_n ℒ^{⊗ n}` on a scheme `T`, the component `ψ_d`
of `toGradedPowerMap (twistingOfUnitalHom (𝟙_T) 𝒜 ℒ Φ)`, transposed back along the adjunction of
`𝟙_T` and followed by the comparison `ℒ^{⊗ d} ≅ ℒ^{⊗ d}` of the iterated and the integral tensor
powers, is `Φ_d`.  The instances are bound implicitly, so that an instance is matched by
unification rather than by instance search. -/
theorem homEquiv_symm_twistingOfUnitalHom_psi_comp_powCompare {T : Scheme.{u}}
    {A : SheafGradedAlgebra.{u} T} {L : T.Modules} {hLm : Stacks.Ample.IsInvertibleModule T L}
    {hLi : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
      (isSheafStruct T) L}
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom (𝟙 T)) (situationAlgebra A))
      (laurent L)) (d : ℕ) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 T)).homEquiv _ _).symm
        ((toGradedPowerMap (Stacks.RelativeProj.twistingOfUnitalHom (𝟙 T) (situationAlgebra A)
          L Φ)).ψ d) ≫ (powCompare L d).hom = Φ.app (d : ℤ) := by
  refine (congrArg (· ≫ _) (Equiv.symm_apply_apply _ _)).trans ?_
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans (Category.comp_id _))))).trans ?_
  exact (congrArg (· ≫ _) (eqToHom_map _ _)).trans ((eqToHom_trans_assoc _ _ _).trans
    ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)))

/-- `…homEquiv_symm_twistingOfUnitalHom_psi_comp_powCompare` for a twisting given in a second
spelling of the scheme, the algebra and the module: if `tw` is heterogeneously equal to the
quadruple of `Φ`, then `ψ_d` of `tw` read back is heterogeneously equal to `Φ_d`.  Each of the
spellings is compared by its own hypothesis, so that an instance compares only leaves. -/
theorem homEquiv_symm_psi_comp_powCompare_heq_of_heq {T₁ T₂ : Scheme.{u}} (hT : T₁ = T₂)
    {A₁ : SheafGradedAlgebra.{u} T₁} {A₂ : SheafGradedAlgebra.{u} T₂} (hA : HEq A₁ A₂)
    {L₁ : T₁.Modules} {L₂ : T₂.Modules} (hL : HEq L₁ L₂)
    {hLm₁ : Stacks.Ample.IsInvertibleModule T₁ L₁}
    {hLi₁ : Stacks.SheafOfModules.IsInvertible T₁.toRingedSpace.presheaf (isSheafStruct T₁) L₁}
    {hLm₂ : Stacks.Ample.IsInvertibleModule T₂ L₂}
    {hLi₂ : Stacks.SheafOfModules.IsInvertible T₂.toRingedSpace.presheaf (isSheafStruct T₂) L₂}
    (tw : Twisting (𝟙 T₁) (situationAlgebra A₁) 1 L₁)
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom (𝟙 T₂)) (situationAlgebra A₂))
      (laurent L₂))
    (h : HEq tw (Stacks.RelativeProj.twistingOfUnitalHom (𝟙 T₂) (situationAlgebra A₂) L₂ Φ))
    (d : ℕ) :
    HEq (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 T₁)).homEquiv _ _).symm
        ((toGradedPowerMap tw).ψ d) ≫ (powCompare L₁ d).hom) (Φ.app (d : ℤ)) := by
  subst hT
  have eA := eq_of_heq hA
  have eL := eq_of_heq hL
  subst eA eL
  obtain rfl : hLm₂ = hLm₁ := rfl
  obtain rfl : hLi₂ = hLi₁ := rfl
  have e := eq_of_heq h
  subst e
  exact heq_of_eq (homEquiv_symm_twistingOfUnitalHom_psi_comp_powCompare (hLm := hLm₂) Φ d)

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace AlgebraicGeometry.Space

/-- **A comparison `m^*Z ⟶ Z` along an endomorphism `m = 𝟙` satisfying the cocycle law is the
identification of the pullback along the identity.**  If `P : m^*Z ⟶ Z` is invertible and
`P` transported along `m ≫ m = m` is `(m ≫ m)^*Z ≅ m^*(m^*Z) ⟶ m^*Z ⟶ Z` (the cocycle law of a
comparison at `m` and `m`), then `P` is the transport along `m = 𝟙` followed by
`(𝟙_X)^*Z ≅ Z`.  This is the left unitality of the pseudofunctor of inverse images. -/
theorem eq_pullbackCongr_comp_pullbackId_of_comp {X : Scheme.{u}} (m : X ⟶ X) (hm : m = 𝟙 X)
    (Z : X.Modules) (P : (Scheme.Modules.pullback m).obj Z ⟶ Z) (hP : IsIso P) (hmm : m ≫ m = m)
    (E : (Scheme.Modules.pullbackCongr hmm).hom.app Z ≫ P =
      (Scheme.Modules.pullbackComp m m).inv.app Z ≫ (Scheme.Modules.pullback m).map P ≫ P) :
    P = (Scheme.Modules.pullbackCongr hm).hom.app Z ≫ (Scheme.Modules.pullbackId X).hom.app Z := by
  subst hm
  have E1 : (Scheme.Modules.pullbackCongr hmm).hom.app Z =
      (Scheme.Modules.pullbackComp (𝟙 X) (𝟙 X)).inv.app Z ≫
        (Scheme.Modules.pullback (𝟙 X)).map P := by
    rw [← Category.assoc] at E
    exact (cancel_mono P).1 E
  have U := congrArg (fun k => NatTrans.app k Z)
    (Scheme.Modules.pseudofunctor_left_unitality (𝟙 X))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    eqToHom_app] at U
  replace U := (congrArg (_ ≫ ·) (Category.comp_id _)).symm.trans U
  have E2 : (Scheme.Modules.pullback (𝟙 X)).map P =
      (Scheme.Modules.pullback (𝟙 X)).map ((Scheme.Modules.pullbackId X).hom.app Z) := by
    have : Epi ((Scheme.Modules.pullbackComp (𝟙 X) (𝟙 X)).inv.app Z) :=
      @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv ((Scheme.Modules.pullbackComp (𝟙 X) (𝟙 X)).app Z))
    refine (cancel_epi ((Scheme.Modules.pullbackComp (𝟙 X) (𝟙 X)).inv.app Z)).1 ?_
    rw [← E1, U]
    simp [Scheme.Modules.pullbackCongr]
  have N1 := (Scheme.Modules.pullbackId X).hom.naturality P
  have N2 := (Scheme.Modules.pullbackId X).hom.naturality
    ((Scheme.Modules.pullbackId X).hom.app Z)
  simp only [Functor.id_map] at N1 N2
  rw [E2] at N1
  have := (Iso.cancel_iso_hom_left ((Scheme.Modules.pullbackId X).app _) _ _).1
    (N1.symm.trans N2)
  simpa [Scheme.Modules.pullbackCongr] using this

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The comparison of restricted algebras along a morphism of test objects equal to the
identity** is the transport along `τ = 𝟙` followed by the identification `(𝟙_T)^*N ≅ N`: by the
cocycle law `AlgebraicGeometry.Space.pointComparison_comp_app` at `𝟙` and `𝟙`, the invertibility
of the comparison, and `AlgebraicGeometry.Space.eq_pullbackCongr_comp_pullbackId_of_comp`. -/
theorem pointComparison_app_eq_of_eq_id {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
    {T : BigFppfOver B S hS} (τ : T ⟶ T) (hτ : τ = 𝟙 T) (f : yoneda.obj T ⟶ X.1)
    (hf : yoneda.map τ ≫ f = f) (n : ℤ) :
    (pointComparison A τ f f hf).app n =
      (Scheme.Modules.pullbackCongr ((congrArg (BigFppfOver.toScheme B S hS).map hτ).trans
        ((BigFppfOver.toScheme B S hS).map_id T))).hom.app _ ≫
        (Scheme.Modules.pullbackId _).hom.app _ := by
  subst hτ
  have hmm : (BigFppfOver.toScheme B S hS).map (𝟙 T) ≫ (BigFppfOver.toScheme B S hS).map (𝟙 T) =
      (BigFppfOver.toScheme B S hS).map (𝟙 T) :=
    ((BigFppfOver.toScheme B S hS).map_comp (𝟙 T) (𝟙 T)).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map (Category.id_comp (𝟙 T)))
  have hf'' : yoneda.map (𝟙 T ≫ 𝟙 T) ≫ f = f := by rw [Category.id_comp]; exact hf
  have hc := pointComparison_comp_app A (𝟙 T) (𝟙 T) f f f hf hf hf'' n
  have hk := pointComparison_app_congr A n (Category.id_comp (𝟙 T)) f f hf'' hf
  exact eq_pullbackCongr_comp_pullbackId_of_comp ((BigFppfOver.toScheme B S hS).map (𝟙 T))
    ((BigFppfOver.toScheme B S hS).map_id T) _ _ (isIso_pointComparison_app A hA (𝟙 T) f f hf n)
    hmm (hk.symm.trans hc)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

section SectionUnit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The underlying morphisms of the images of two mutually inverse morphisms under a functor to a
full subcategory are mutually inverse. -/
theorem map_hom_comp_map_hom_eq_id {C D : Type*} [Category C] [Category D]
    {Q : ObjectProperty D} (F : C ⥤ Q.FullSubcategory) {a b : C} (f : a ⟶ b) (g : b ⟶ a)
    (h : f ≫ g = 𝟙 a) : (F.map f).hom ≫ (F.map g).hom = 𝟙 (F.obj a).obj := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, ← F.map_comp, h, F.map_id]
  rfl

/-- A morphism read off as `u ≫ e⁻¹`, followed by `e`, is `u`, written out as `t ≫ i`. -/
theorem comp_eq_of_eq_comp_of_comp_eq_id {C : Type*} [Category C] {X Y Z₀ Z₁ : C} {a : X ⟶ Y}
    {u : X ⟶ Z₁} {einv : Z₁ ⟶ Y} {e : Y ⟶ Z₁} {t : X ⟶ Z₀} {i : Z₀ ⟶ Z₁}
    (h : a = u ≫ einv) (he : einv ≫ e = 𝟙 Z₁) (hu : u = t ≫ i) : a ≫ e = t ≫ i := by
  rw [h, Category.assoc, he, Category.comp_id, hu]

/-- **The identification `g^*(M^a) ≅ (g^*M)^a` of Stacks 03DX (2) at the identity of the site** is
the unit law `(𝟙)^* ≅ 𝟭` of Stacks 03LU, transported along
`AlgebraicGeometry.Space.representedSpaceMap_id`, followed by the module attached to the inverse
of the unit law `(𝟙_W)^*M ≅ M` on the scheme.  The unit law of a morphism of pseudofunctors, from
the composition law
`AlgebraicGeometry.Space.compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom` at `(𝟙, 𝟙)`,
the naturality of the identification and the unit laws of the two inverse images
(`Stacks.CategoryTheory.map_comp_eq_of_cancel`,
`Stacks.CategoryTheory.eq_app_comp_of_map_comp_eq`). -/
theorem modulePullbackRepresentedQuasicoherentIso_id_hom (W : BigFppfOver B S hS)
    (Z : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory) :
    (modulePullbackRepresentedQuasicoherentIso B S hS (𝟙 W) Z).hom =
      (eqToIso (congrArg (modulePullback B S hS) (representedSpaceMap_id B S hS W)) ≪≫
          modulePullbackIdIso B S hS
            (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS)).hom.app
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj Z).obj ≫
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
        (ObjectProperty.homMk ((Scheme.Modules.pullbackId _).inv.app Z.obj) :
          Z ⟶ quasicoherentPullbackObj B S hS (𝟙 W) Z)).hom := by
  have hcomp := compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS (𝟙 W) (𝟙 W) Z
  have hnat := modulePullbackRepresentedQuasicoherentIso_naturality B S hS (𝟙 W)
    (ObjectProperty.homMk ((Scheme.Modules.pullbackId _).hom.app Z.obj) :
      quasicoherentPullbackObj B S hS (𝟙 W) Z ⟶ Z)
  have hn : (quasicoherentPullbackMap B S hS (𝟙 W)
      (ObjectProperty.homMk ((Scheme.Modules.pullbackId _).hom.app Z.obj) :
        quasicoherentPullbackObj B S hS (𝟙 W) Z ⟶ Z)) =
      (quasicoherentPullbackCompIso B S hS (𝟙 W) (𝟙 W) Z).hom :=
    ObjectProperty.hom_ext _ (Scheme.Modules.pullbackComp_id_id_hom_app _ Z.obj).symm
  rw [hn] at hnat
  have hkey := Stacks.CategoryTheory.map_comp_eq_of_cancel
    (modulePullback B S hS (representedSpaceMap B S hS (𝟙 W)))
    (modulePullbackRepresentedQuasicoherentIso B S hS (𝟙 W) Z)
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
      (ObjectProperty.homMk ((Scheme.Modules.pullbackId _).hom.app Z.obj) :
        quasicoherentPullbackObj B S hS (𝟙 W) Z ⟶ Z)).hom
    (modulePullbackRepresentedQuasicoherentIso B S hS (𝟙 W)
      (quasicoherentPullbackObj B S hS (𝟙 W) Z)).hom
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
      (quasicoherentPullbackCompIso B S hS (𝟙 W) (𝟙 W) Z).hom).hom
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS (𝟙 W))
      (representedSpaceMap B S hS (𝟙 W))).hom.app
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj Z).obj)
    hcomp.symm hnat
  refine Stacks.CategoryTheory.eq_app_comp_of_map_comp_eq
    (modulePullback B S hS (representedSpaceMap B S hS (𝟙 W)))
    (eqToIso (congrArg (modulePullback B S hS) (representedSpaceMap_id B S hS W)) ≪≫
      modulePullbackIdIso B S hS
        (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS))
    (modulePullbackRepresentedQuasicoherentIso B S hS (𝟙 W) Z) _ _ ?_
    (hkey.trans (modulePullbackCompIso_hom_app_representedSpaceMap_id B S hS W _))
  exact map_hom_comp_map_hom_eq_id _ _ _
    (ObjectProperty.hom_ext _ ((Scheme.Modules.pullbackId _).hom_inv_id_app Z.obj))

/-- `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_id_hom` at an endomorphism
`m = 𝟙` of the site: the identification along `m`, followed by the module attached to the
transport `m^*Z = (𝟙)^*Z` and the unit law `(𝟙)^*Z ≅ Z` on the scheme, is the transport along
`m = 𝟙` followed by the unit law of Stacks 03LU. -/
theorem modulePullbackRepresentedQuasicoherentIso_hom_comp_map_of_eq_id {W : BigFppfOver B S hS}
    (m : W ⟶ W) (hm : m = 𝟙 W)
    (hm' : (BigFppfOver.toScheme B S hS).map m = 𝟙 ((BigFppfOver.toScheme B S hS).obj W))
    (hms : representedSpaceMap B S hS m =
      𝟙 (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS))
    (Z : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory) :
    (modulePullbackRepresentedQuasicoherentIso B S hS m Z).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
        (ObjectProperty.homMk ((Scheme.Modules.pullbackCongr hm').hom.app Z.obj ≫
          (Scheme.Modules.pullbackId _).hom.app Z.obj) :
          quasicoherentPullbackObj B S hS m Z ⟶ Z)).hom =
      pullbackTransport _ hms ≫
        (modulePullbackIdIso B S hS
          (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS)).hom.app
          ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj Z).obj := by
  subst hm
  have hc : (Scheme.Modules.pullbackCongr hm').hom.app Z.obj = 𝟙 _ := rfl
  exact comp_eq_of_eq_comp_of_comp_eq_id (modulePullbackRepresentedQuasicoherentIso_id_hom W Z)
    (map_hom_comp_map_hom_eq_id _ _ _ (ObjectProperty.hom_ext _
      ((congrArg (_ ≫ ·) ((congrArg (· ≫ _) hc).trans (Category.id_comp _))).trans
        ((Scheme.Modules.pullbackId _).inv_hom_id_app Z.obj))))
    (congrArg (· ≫ _) (eqToIso_modulePullback_app_hom B S hS hms _))

/-- The abstract shape of
`…modulePullback_map_modulePullbackRepresentedQuasicoherentIso_hom_comp_canHom`:
a composite rewritten by a splitting of its last factor, a composition law and a unit law. -/
theorem comp_comp_eq_of_split_of_comp_of_unit {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ Y₁ Y₂ Y₃ Y₄ : C} {x₁ : X₀ ⟶ X₁} {x₂ : X₁ ⟶ X₂} {e : X₂ ⟶ X₃} {y₁ : X₂ ⟶ Y₃}
    {y₂ : Y₃ ⟶ X₃} {t₁ : X₀ ⟶ Y₁} {T : Y₁ ⟶ Y₂} {m : Y₂ ⟶ Y₃} {T' : Y₂ ⟶ Y₄} {t₂ : Y₁ ⟶ Y₄}
    {t₃ : Y₄ ⟶ X₃} (hsplit : e = y₁ ≫ y₂) (hcomp : t₁ ≫ T ≫ m = x₁ ≫ x₂ ≫ y₁)
    (hunit : m ≫ y₂ = T' ≫ t₃) (hT : T ≫ T' = t₂) :
    x₁ ≫ x₂ ≫ e = t₁ ≫ t₂ ≫ t₃ := by
  rw [hsplit, ← hT]
  simp only [← Category.assoc] at hcomp ⊢
  rw [← hcomp]
  simp only [Category.assoc]
  rw [hunit]

/-- Two transports along equalities of morphisms compose to the transport along the composite
equality. -/
theorem pullbackTransport_comp_pullbackTransport_eq {T X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) {f g k : T ⟶ X} (h₁ : f = g) (h₂ : g = k) (h₃ : f = k) :
    pullbackTransport M h₁ ≫ pullbackTransport M h₂ = pullbackTransport M h₃ := by
  subst h₁ h₂
  rfl

/-- **The identification `g^*(M^a) ≅ (g^*M)^a` of Stacks 03DX (2) along a section.**  For
morphisms `c : W ⟶ F` and `q : F ⟶ W` of the site with `c ≫ q = 𝟙`, the identification along `q`
pulled back along `c`, followed by the identification along `c` and the module attached to the
canonical identification `c^*(q^*Z) ≅ (c ≫ q)^*Z = (𝟙)^*Z ≅ Z` on the scheme, is the comparison
`c^*q^* ≅ (c ≫ q)^*` of Stacks 03LU followed by the transport along `c ≫ q = 𝟙` and the unit law
`(𝟙)^* ≅ 𝟭`: the composition law
`AlgebraicGeometry.Space.compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom` and the unit
law `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_hom_comp_map_of_eq_id`. -/
theorem modulePullback_map_modulePullbackRepresentedQuasicoherentIso_hom_comp_canHom
    {W F : BigFppfOver B S hS} (c : W ⟶ F) (q : F ⟶ W) (hcq : c ≫ q = 𝟙 W)
    (hcq' : (BigFppfOver.toScheme B S hS).map c ≫ (BigFppfOver.toScheme B S hS).map q =
      𝟙 ((BigFppfOver.toScheme B S hS).obj W))
    (hs : CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS c)
      (representedSpaceMap B S hS q) =
        𝟙 (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS))
    (Z : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory) :
    (modulePullback B S hS (representedSpaceMap B S hS c)).map
        (modulePullbackRepresentedQuasicoherentIso B S hS q Z).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS c
        (quasicoherentPullbackObj B S hS q Z)).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
        (ObjectProperty.homMk (Stacks.AlgebraicGeometry.ModuleLimits.canHom
            ((BigFppfOver.toScheme B S hS).map c) ((BigFppfOver.toScheme B S hS).map q)
            (𝟙 _) hcq' Z.obj ≫ (Scheme.Modules.pullbackId _).hom.app Z.obj) :
          quasicoherentPullbackObj B S hS c (quasicoherentPullbackObj B S hS q Z) ⟶ Z)).hom =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS c)
          (representedSpaceMap B S hS q)).hom.app
          ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj Z).obj ≫
        pullbackTransport _ hs ≫
        (modulePullbackIdIso B S hS
          (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS)).hom.app
          ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj Z).obj :=
  comp_comp_eq_of_split_of_comp_of_unit
    (((representedQuasicoherentSchemeEquivalence B S hS W).functor.map_comp
      (quasicoherentPullbackCompIso B S hS c q Z).hom
      (ObjectProperty.homMk ((Scheme.Modules.pullbackCongr hcq').hom.app Z.obj ≫
          (Scheme.Modules.pullbackId _).hom.app Z.obj) :
          quasicoherentPullbackObj B S hS (c ≫ q) Z ⟶ Z)).symm ▸ rfl)
    (compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS c q Z)
    (modulePullbackRepresentedQuasicoherentIso_hom_comp_map_of_eq_id (c ≫ q) hcq hcq'
      ((representedSpaceMap_comp B S hS c q).symm.trans hs) Z)
    (pullbackTransport_comp_pullbackTransport_eq _ _ _ _)

end SectionUnit

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  (W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase) (x : yoneda.obj W ⟶ X.1)
  (d : ℕ)

/-- **`ψ_d` of the restriction `x^*ψ` of `ψ` to a scheme point `x : W ⟶ X`, read back**: the
component of `…RelativeProjSituation.pointTwisting`, transposed back along the adjunction of
`𝟙_W` and followed by `powCompare`, is the identification `(𝟙_W)^*((f ∘ x)^*𝒜) = (f ∘ x)^*𝒜`
followed by `AlgebraicGeometry.Space.pointPsi` in degree `d`. -/
theorem pointTwisting_psi_homEquiv_symm_comp_powCompare :
    ((Scheme.Modules.pullbackPushforwardAdjunction
        (𝟙 ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj
          W))).homEquiv _ _).symm
      ((toGradedPowerMap (s.pointTwisting f L ψ W x)).ψ d) ≫
      (powCompare (pointLine s.shrink.site s.shrink.base s.shrink.containsBase L W x) d).hom =
    ((Stacks.Conormal.gradedPullbackId
      (situationAlgebra (s.shrink.pointAlgebra W (x ≫ f.hom)))).comp
        (pointPsi f s.shrink.algebra L ψ W x)).app (d : ℤ) :=
  homEquiv_symm_twistingOfUnitalHom_psi_comp_powCompare
    (A := s.shrink.pointAlgebra W (x ≫ f.hom)) (hLm := isInvertible_pointLine_toScheme L W x)
    ((Stacks.Conormal.gradedPullbackId
      (situationAlgebra (s.shrink.pointAlgebra W (x ≫ f.hom)))).comp
        (pointPsi f s.shrink.algebra L ψ W x)) d

end AlgebraicGeometry.Space.RelativeProjSituation

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism Stacks.AlgebraicGeometry.RelativeProj

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  {W : BigFppfOver s.site s.base s.containsBase} (x : yoneda.obj W ⟶ X.1)
  (hx : (ofUnitalHom s f L ψ).locusOpen W x = ⊤) (d : ℕ)

/-- The restriction of `ψ` to a scheme point in the restriction datum
`…InvertibleTwistingRestriction.ofUnitalHom` is `…RelativeProjSituation.pointTwisting`, by
definition; the leaf comparing the spelling over the site of `s` with that over `s.shrink`. -/
theorem ofUnitalHom_twisting_eq_pointTwisting :
    (ofUnitalHom s f L ψ).twisting W x = s.pointTwisting f L ψ W x :=
  rfl

/-- **`ψ_d` of `w^*ψ` read back, in the spelling of the middle square**: the component `ψ_d` of
the twisting `…InvertibleTwistingRestriction.ofUnitalHom`'s restriction of `ψ` at `w`, over the
site of `s`, read back along the adjunction of `𝟙_W` and `powCompare`, is heterogeneously equal to
the identification `(𝟙_W)^*((f ∘ w)^*𝒜) = (f ∘ w)^*𝒜` followed by
`AlgebraicGeometry.Space.pointPsi` in degree `d`, over the site of `s.shrink`: the instance of
`…homEquiv_symm_psi_comp_powCompare_heq_of_heq` with the two spellings of `W`, of `(f ∘ w)^*𝒜`, of
`w^*ℒ` and of `w^*ψ` compared as leaves. -/
theorem homEquiv_symm_ofUnitalHom_twisting_psi_comp_powCompare_heq :
    type_of% (homEquiv_symm_psi_comp_powCompare_heq_of_heq
      (T₁ := (BigFppfOver.toScheme s.site s.base s.containsBase).obj W)
      (T₂ := (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj W) rfl
      (A₁ := s.relativeProjPoints.algebra W (x ≫ f.hom))
      (A₂ := s.shrink.pointAlgebra W (x ≫ f.hom)) HEq.rfl
      (L₁ := (ofUnitalHom s f L ψ).line W x)
      (L₂ := pointLine s.shrink.site s.shrink.base s.shrink.containsBase L W x) HEq.rfl
      (hLm₁ := (ofUnitalHom s f L ψ).isInvertible W x)
      (hLm₂ := isInvertible_pointLine_toScheme L W x)
      ((ofUnitalHom s f L ψ).twisting W x)
      ((Stacks.Conormal.gradedPullbackId
        (situationAlgebra (s.shrink.pointAlgebra W (x ≫ f.hom)))).comp
          (pointPsi f s.shrink.algebra L ψ W x))
      (heq_of_eq (ofUnitalHom_twisting_eq_pointTwisting s f L ψ x)) d) :=
  homEquiv_symm_psi_comp_powCompare_heq_of_heq
      (T₁ := (BigFppfOver.toScheme s.site s.base s.containsBase).obj W)
      (T₂ := (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj W) rfl
      (A₁ := s.relativeProjPoints.algebra W (x ≫ f.hom))
      (A₂ := s.shrink.pointAlgebra W (x ≫ f.hom)) HEq.rfl
      (L₁ := (ofUnitalHom s f L ψ).line W x)
      (L₂ := pointLine s.shrink.site s.shrink.base s.shrink.containsBase L W x) HEq.rfl
      (hLm₁ := (ofUnitalHom s f L ψ).isInvertible W x)
      (hLm₂ := isInvertible_pointLine_toScheme L W x)
      ((ofUnitalHom s f L ψ).twisting W x)
      ((Stacks.Conormal.gradedPullbackId
        (situationAlgebra (s.shrink.pointAlgebra W (x ≫ f.hom)))).comp
          (pointPsi f s.shrink.algebra L ψ W x))
      (heq_of_eq (ofUnitalHom_twisting_eq_pointTwisting s f L ψ x)) d

/-- The unit law `(𝟙_T)^*M ≅ M` at two spellings of the scheme and of the module. -/
theorem pullbackId_hom_app_heq {T₁ T₂ : Scheme.{u}} (hT : T₁ = T₂) {M₁ : T₁.Modules}
    {M₂ : T₂.Modules} (hM : HEq M₁ M₂) :
    HEq ((Scheme.Modules.pullbackId T₁).hom.app M₁)
      ((Scheme.Modules.pullbackId T₂).hom.app M₂) := by
  subst hT
  have e := eq_of_heq hM
  subst e
  rfl

/-- An equation `a = (k' ≫ i') ≫ P'` from `a ≍ k ≫ g` and `g ≍ i ≫ P`, with `k`, `i`, `P` read in
a second spelling `k'`, `i'`, `P'`.  The objects and the leaves are compared by separate
hypotheses, so that an instance compares each spelling once. -/
theorem eq_comp_comp_of_heq_comp_of_heq_comp {C : Type*} [Category C] {X X' Y Z Z' : C}
    {a : X' ⟶ Z'} {k : X ⟶ Y} {g : Y ⟶ Z} (h : HEq a (k ≫ g)) {Y₁ Y₂ Z₁ : C} {i : Y₁ ⟶ Y₂}
    {P : Y₂ ⟶ Z₁} (hg : HEq g (i ≫ P)) {Y' Y'' : C} (k' : X' ⟶ Y') (i' : Y' ⟶ Y'')
    (P' : Y'' ⟶ Z') (hX : X = X') (hY : Y = Y') (hY₁ : Y₁ = Y') (hY₂ : Y₂ = Y'') (hZ : Z = Z')
    (hZ₁ : Z₁ = Z') (hk : HEq k k') (hi : HEq i i') (hP : HEq P P') :
    a = (k' ≫ i') ≫ P' := by
  subst hX hY hY₁ hY₂ hZ hZ₁
  have e1 := eq_of_heq hk
  have e2 := eq_of_heq hi
  have e3 := eq_of_heq hP
  subst e1 e2 e3
  rw [eq_of_heq h, eq_of_heq hg, Category.assoc]

/-- **The middle square of clause (1) at a scheme point, with `w^*ψ` read as the point `ψ`**: the
inverse image along the section `c_w` of `ψ` of Tag 01NR, followed by `θ_w`, is the canonical
identification `c_w^*((W ×_Y P ⟶ W)^*((f ∘ w)^*𝒜)_d) ≅ (𝟙_W)^*((f ∘ w)^*𝒜)_d ≅ ((f ∘ w)^*𝒜)_d`
followed by `AlgebraicGeometry.Space.pointPsi` in degree `d`:
`…quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom` with `w^*ψ` read back by
`…RelativeProjSituation.pointTwisting_psi_homEquiv_symm_comp_powCompare`. -/
theorem quasicoherentPullbackMap_fibrePsiQcohHom_comp_chartSchemeTheta_eq_pointPsi :
    quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x hx) (s.fibrePsiQcohHom W (x ≫ f.hom) d) ≫
      chartSchemeTheta s f L ψ x hx (d : ℤ) =
    (ObjectProperty.homMk (Stacks.AlgebraicGeometry.ModuleLimits.canHom
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map
            ((ofUnitalHom s f L ψ).chartSection x hx))
          (s.fibreToBase W (x ≫ f.hom))
          (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W))
          (toScheme_map_chartSection_comp_fibreToBase s f L ψ x hx)
          (s.pointPieceQcoh W (x ≫ f.hom) (d : ℤ)).obj ≫
        (Scheme.Modules.pullbackId _).hom.app (s.pointPieceQcoh W (x ≫ f.hom) (d : ℤ)).obj) :
      quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection x hx)
          (quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom W (x ≫ f.hom))
            (s.pointPieceQcoh W (x ≫ f.hom) (d : ℤ))) ⟶
        s.pointPieceQcoh W (x ≫ f.hom) (d : ℤ)) ≫
      (ObjectProperty.homMk ((pointPsi f s.shrink.algebra L ψ W x).app (d : ℤ)) :
        s.pointPieceQcoh W (x ≫ f.hom) (d : ℤ) ⟶ pointLaurentPieceQcoh L W x (d : ℤ)) := by
  refine ObjectProperty.hom_ext _ ?_
  have H := eq_comp_comp_of_heq_comp_of_heq_comp
    (quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartSchemeTheta_hom_heq s f L ψ x hx d)
    (homEquiv_symm_ofUnitalHom_twisting_psi_comp_powCompare_heq s f L ψ x d)
    (Stacks.AlgebraicGeometry.ModuleLimits.canHom
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map
            ((ofUnitalHom s f L ψ).chartSection x hx))
          (s.fibreToBase W (x ≫ f.hom))
          (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W))
          (toScheme_map_chartSection_comp_fibreToBase s f L ψ x hx)
          (s.pointPieceQcoh W (x ≫ f.hom) (d : ℤ)).obj)
    ((Scheme.Modules.pullbackId _).hom.app (s.pointPieceQcoh W (x ≫ f.hom) (d : ℤ)).obj)
    ((pointPsi f s.shrink.algebra L ψ W x).app (d : ℤ))
    rfl rfl rfl rfl
    ((pointLaurentPieceQcoh_obj_eq_tensorPowerModule s f L ψ x (d : ℤ)).trans
      (tensorPowerModule_line_eq_tensorPower s f L ψ x (d : ℤ))).symm rfl HEq.rfl
      (pullbackId_hom_app_heq rfl HEq.rfl) HEq.rfl
  exact H

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction
