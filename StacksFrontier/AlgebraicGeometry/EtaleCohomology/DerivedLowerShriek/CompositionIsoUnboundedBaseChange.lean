module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCubeUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoUnboundedBaseChangeAbstract
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.UnboundedBaseChangeToDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.OpenImmersionDirectImageToDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.UnboundedExtensionByZeroCompToDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionByZeroToDirectImageMono
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySquareQ
public import StacksFrontier.Tactic.KernelApply

/-!
# The isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` through the auxiliary compactification commutes with
base change, on `D(X_étale, Λ)`

For cartesian squares `X' ⟶ X` over `Y' ⟶ Y` over `Z' ⟶ Z`, a compactification `Y ⟶ Ȳ` of `Y`
over `Z` and a compactification `X ⟶ X̄` of `X` over `Ȳ`, the isomorphism
`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompOverIso` is
compatible with the base change maps of the cubes of compactifications. This is the unbounded
counterpart of `Stacks.EtaleCohomology.derivedLowerShriekCompOverIso_baseChange`.

The isomorphism is `R(f̄ ≫ ḡ)_* ≅ Rḡ_* ∘ Rf̄_*` followed by `Rḡ_*` of
`Rf̄_* (b ∘ a)_! ≅ Rf̄_* b_! a_! ≅ i_! Rf'_* a_!`. The Leray isomorphism is compatible with base
change by `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded_comp`; the identification
`(b ∘ a)_! ≅ b_! ∘ a_!` is compatible with the isomorphisms `φ⁻¹ ∘ j_! ≅ j'_! ∘ g'⁻¹` of
[Stacks, Tag 03S6] already on sheaves; and the open immersion case `Rf̄_* ∘ b_! ≅ i_! ∘ Rf'_*` of
[Stacks, Tag 0F7B] is compatible with the base change maps because both of its sides are right
derived functors of `i_! ∘ f'_* ≅ f̄_* ∘ b_!`, whose compatibility with the base change maps on
sheaves is checked after the monomorphism `f̄'_* b'_! ⟶ f̄'_* b'_*`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIso_comp`: the isomorphisms of
  [Stacks, Tag 03S6] paste along a composite of open immersions.
* `Stacks.EtaleCohomology.etaleModuleDirectImageExtensionByZeroIso_baseChange`: the underived open
  immersion case of [Stacks, Tag 0F7B] commutes with base change.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroDirectImageUnboundedIso_baseChange`: the open
  immersion case of [Stacks, Tag 0F7B] on `D(-_étale, Λ)` commutes with base change.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompOverIso_baseChange`.

## Implementation notes

The compatibilities on unbounded derived categories are first proved with the comparisons on
sheaves, the base change maps on derived categories and the derived-functor units as variables
(`Stacks.EtaleCohomology.extensionByZeroDirectImageUnboundedIso_baseChange_of` and the lemmas
before it), and only then instantiated. Stated directly for the base change maps of étale
sheaves, the kernel compares the differently written hypotheses by unfolding these maps.

## References

* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace AlgebraicGeometry.CompactificationOf

variable {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z' ⟶ Z} {hY : Y' ⟶ Y}
  {g' : Y' ⟶ Z'} {hX : X' ⟶ X} {f' : X' ⟶ Y'}
  (sqg : IsPullback hY g' g h) (sqf : IsPullback hX f' f hY)
  (jg : CompactificationOf (Over.mk g)) (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

/-- The square of the open immersions `X̄★ ×_{Ȳ'} Y' ⟶ X̄★` and `X̄ ×_Ȳ Y ⟶ X̄` over the
projections `X̄★ ⟶ X̄` and `X̄★ ×_{Ȳ'} Y' ⟶ X̄ ×_Ȳ Y` is cartesian, for `X̄★ = X̄ ×_Ȳ Ȳ'`. -/
theorem isPullback_restrictBaseι_baseChange :
    IsPullback (restrictBaseBaseChangeι sqg sqf jg jX)
      (restrictBaseι (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
      (restrictBaseι jg jX) (compImmersionBaseChangeι sqg sqf jg jX) := by
  have outer := (IsPullback.of_hasPullback (compImmersionBaseChange sqg sqf jg jX).toBase
    (jg.baseChange sqg).immersion).flip.paste_horiz (isPullback_baseChange sqg jg)
  have e1 : pullback.snd (compImmersionBaseChange sqg sqf jg jX).toBase
        (jg.baseChange sqg).immersion ≫ hY =
      restrictBaseBaseChangeι sqg sqf jg jX ≫ pullback.snd jX.toBase jg.immersion :=
    (restrictBaseBaseChangeι_snd sqg sqf jg jX).symm
  have e2 : (compImmersionBaseChange sqg sqf jg jX).toBase ≫ pullback.fst jg.toBase h =
      compImmersionBaseChangeι sqg sqf jg jX ≫ jX.toBase := pullback.condition.symm
  rw [e1, e2] at outer
  exact IsPullback.of_right outer (restrictBaseBaseChangeι_fst sqg sqf jg jX)
    (IsPullback.of_hasPullback jX.toBase jg.immersion).flip

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-! ### Two identities on sheaves -/

section Underived

variable (Λ : Type) [CommRing Λ]

/-- **The isomorphisms `φ⁻¹ ∘ j_! ≅ j'_! ∘ g'⁻¹` of [Stacks, Tag 03S6] paste along a composite
of open immersions**, read through `(b ∘ a)_! ≅ b_! ∘ a_!`. Checked after the monomorphism
`b'_! a'_! ⟶ (b' ∘ a')_*`, where both sides become the base change of `(b ∘ a)_! ⟶ (b ∘ a)_*`. -/
theorem etaleModuleInverseImageExtensionByZeroIso_comp {X U T X' U' T' : Scheme.{u}}
    {a : X ⟶ U} {b : U ⟶ T} {a' : X' ⟶ U'} {b' : U' ⟶ T'} {hX : X' ⟶ X} {ρ : U' ⟶ U}
    {φ : T' ⟶ T} [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion a']
    [IsOpenImmersion b'] (hca : IsPullback hX a' a ρ) (hcb : IsPullback ρ b' b φ)
    (hcab : IsPullback hX (a' ≫ b') (a ≫ b) φ) (F : EtaleModules.{u, 0} Λ X) :
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hcab).inv.app F ≫
        (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a' b').hom.app
          ((etaleModuleInverseImage.{u, 0} Λ hX).obj F) =
      (etaleModuleInverseImage.{u, 0} Λ φ).map
          ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).hom.app F) ≫
        (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hcb).inv.app
          ((etaleModuleExtensionByZero.{u, 0} Λ a).obj F) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ b').map
          ((etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hca).inv.app F) := by
  exact DerivedComparisonPaste.extensionByZero_comp_baseChange_abstract
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ a)
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b)
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ (a ≫ b))
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ a')
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b')
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ (a' ≫ b'))
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b)
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a' b')
    (etaleModuleDirectImageComp.{u, 0} Λ a b (a ≫ b) rfl)
    (etaleModuleDirectImageComp.{u, 0} Λ a' b' (a' ≫ b') rfl)
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hca)
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hcb)
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hcab)
    (etaleModuleBaseChange Λ a a' ρ hX hca.w.symm) (etaleModuleBaseChange Λ b b' φ ρ hcb.w.symm)
    (etaleModuleBaseChange Λ (a ≫ b) (a' ≫ b') φ hX hcab.w.symm)
    (etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage Λ a b)
    (etaleModuleExtensionByZeroCompIso_hom_comp_toDirectImage Λ a' b')
    (ExtensionByZeroPasting.map_extensionByZeroToDirectImage_comp_baseChange Λ hca)
    (ExtensionByZeroPasting.map_extensionByZeroToDirectImage_comp_baseChange Λ hcb)
    (ExtensionByZeroPasting.map_extensionByZeroToDirectImage_comp_baseChange Λ hcab)
    (etaleModuleBaseChange_pasteV Λ a b (a ≫ b) rfl a' b' (a' ≫ b') rfl hX ρ φ
      hca.w.symm hcb.w.symm hcab.w.symm)
    (fun G => mono_etaleModuleExtensionByZeroToDirectImage_app Λ (a' ≫ b') G) F

/-- **The underived open immersion case of [Stacks, Tag 0F7B] commutes with base change**, over
a torsion ring: for cartesian squares `b ≫ f̄ = f' ≫ i` and `b' ≫ f̄' = f'' ≫ i'` over a cube,
the isomorphism `i_! f'_* ≅ f̄_* b_!` is compatible with the base change maps of `f'_*` and
`f̄_*` and the isomorphisms of [Stacks, Tag 03S6] for `i` and `b`. Checked after the monomorphism
`f̄'_* b'_! ⟶ f̄'_* b'_*`, where both sides become the base change of `(f' ≫ i)_*`. -/
theorem etaleModuleDirectImageExtensionByZeroIso_baseChange (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)
    {T Ub P Y T' Ub' P' Y' : Scheme.{u}} {fb : T ⟶ Ub} [IsProper fb] {i : Y ⟶ Ub}
    [IsOpenImmersion i] {b : P ⟶ T} [IsOpenImmersion b] {f' : P ⟶ Y} (sq : IsPullback b f' fb i)
    {fb' : T' ⟶ Ub'} [IsProper fb'] {i' : Y' ⟶ Ub'} [IsOpenImmersion i'] {b' : P' ⟶ T'}
    [IsOpenImmersion b'] {f'' : P' ⟶ Y'} (sq' : IsPullback b' f'' fb' i')
    {φT : T' ⟶ T} {φU : Ub' ⟶ Ub} {φP : P' ⟶ P} {φY : Y' ⟶ Y}
    (hcb : IsPullback φP b' b φT) (hci : IsPullback φY i' i φU)
    (wf : fb' ≫ φU = φT ≫ fb) (wf' : f'' ≫ φY = φP ≫ f') (F : EtaleModules.{u, 0} Λ P) :
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hci).inv.app
        ((etaleModuleDirectImage.{u, 0} Λ f').obj F) ≫
      (etaleModuleExtensionByZero.{u, 0} Λ i').map
        ((etaleModuleBaseChange Λ f' f'' φY φP wf').app F) =
    (etaleModuleInverseImage.{u, 0} Λ φU).map
        ((etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq).hom.app F) ≫
      (etaleModuleBaseChange Λ fb fb' φU φT wf).app
        ((etaleModuleExtensionByZero.{u, 0} Λ b).obj F) ≫
      (etaleModuleDirectImage.{u, 0} Λ fb').map
        ((etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hcb).inv.app F) ≫
      (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb' i' b' f'' sq').inv.app
        ((etaleModuleInverseImage.{u, 0} Λ φP).obj F) := by
  have wpq : φP ≫ f' ≫ i = (f'' ≫ i') ≫ φU :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ i) wf'.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (f'' ≫ ·) hci.w).trans
        (Category.assoc _ _ _).symm)))
  exact DerivedComparisonPaste.directImageExtensionByZero_baseChange_abstract
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i)
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b)
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i')
    (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b')
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq)
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb' i' b' f'' sq')
    (etaleModuleDirectImageComp.{u, 0} Λ f' i (f' ≫ i) rfl)
    (etaleModuleDirectImageComp.{u, 0} Λ b fb (f' ≫ i) sq.w.symm)
    (etaleModuleDirectImageComp.{u, 0} Λ f'' i' (f'' ≫ i') rfl)
    (etaleModuleDirectImageComp.{u, 0} Λ b' fb' (f'' ≫ i') sq'.w.symm)
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hci)
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hcb)
    (etaleModuleBaseChange Λ f' f'' φY φP wf') (etaleModuleBaseChange Λ i i' φU φY hci.w.symm)
    (etaleModuleBaseChange Λ b b' φT φP hcb.w.symm) (etaleModuleBaseChange Λ fb fb' φU φT wf)
    (etaleModuleBaseChange Λ (f' ≫ i) (f'' ≫ i') φU φP wpq.symm)
    (etaleModuleDirectImageExtensionByZeroIso_hom_comp_toDirectImage Λ fb i b f' sq hΛ)
    (etaleModuleDirectImageExtensionByZeroIso_hom_comp_toDirectImage Λ fb' i' b' f'' sq' hΛ)
    (ExtensionByZeroPasting.map_extensionByZeroToDirectImage_comp_baseChange Λ hci)
    (ExtensionByZeroPasting.map_extensionByZeroToDirectImage_comp_baseChange Λ hcb)
    (etaleModuleBaseChange_pasteV Λ f' i (f' ≫ i) rfl f'' i' (f'' ≫ i') rfl φP φY φU
      wf' hci.w.symm wpq.symm)
    (etaleModuleBaseChange_pasteV Λ b fb (f' ≫ i) sq.w.symm b' fb' (f'' ≫ i')
      sq'.w.symm φP φT φU hcb.w.symm wf wpq.symm)
    (fun G => by
      have := (etaleModuleInverseImageAdj.{u, 0} Λ fb').isRightAdjoint
      have := mono_etaleModuleExtensionByZeroToDirectImage_app Λ b' G
      infer_instance) F

end Underived

/-! ### The comparisons on `D(X_étale, Λ)` -/

section Derived

/-- `Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso` at the image of a complex, after the
canonical factorization: the degreewise isomorphism, read through the canonical
factorizations. -/
theorem mapDerivedCategoryCompIsoOfIso_hom_app_Q {C₁ C₂ C₃ : Type*} [Category C₁]
    [Category C₂] [Category C₃] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory.{w} C₁] [HasDerivedCategory.{w} C₂] [HasDerivedCategory.{w} C₃]
    (H : C₁ ⥤ C₃) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : H ≅ F ⋙ G)
    (K : CochainComplex C₁ ℤ) :
    H.mapDerivedCategoryFactors.inv.app K ≫
        (Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso H F G e).hom.app
          (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e.symm (ComplexShape.up ℤ)).inv.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  have hL : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) H.mapDerivedCategory =
      H.mapDerivedCategoryFactors := rfl
  simp [Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso, Localization.liftNatTrans_app, hL]
  rfl

variable (Λ : Type) [CommRing Λ] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

/-- A comparison `α : F ⋙ G ⟶ G' ⋙ F'` of functors of sheaves of `Λ`-modules applied degreewise to
unbounded complexes, spelled on `CochainComplex` as
`Stacks.EtaleCohomology.etaleModuleComplexBaseChangeUnboundedOf`. -/
def etaleModuleComplexComparisonOf {X X' Y Y' : Scheme.{u}}
    {F : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ Y}
    {G : EtaleModules.{u, 0} Λ Y ⥤ EtaleModules.{u, 0} Λ Y'}
    {G' : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ X'}
    {F' : EtaleModules.{u, 0} Λ X' ⥤ EtaleModules.{u, 0} Λ Y'}
    [F.Additive] [G.Additive] [G'.Additive] [F'.Additive] (α : F ⋙ G ⟶ G' ⋙ F') :
    (F.mapHomologicalComplex _ ⋙ G.mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, 0} Λ X) ℤ ⥤ CochainComplex (EtaleModules.{u, 0} Λ Y') ℤ) ⟶
      (G'.mapHomologicalComplex _ ⋙ F'.mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, 0} Λ X) ℤ ⥤ CochainComplex (EtaleModules.{u, 0} Λ Y') ℤ) :=
  NatTrans.mapHomologicalComplex α _

/-- The components of `Stacks.EtaleCohomology.etaleModuleComplexComparisonOf`. -/
theorem etaleModuleComplexComparisonOf_app_f {X X' Y Y' : Scheme.{u}}
    {F : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ Y}
    {G : EtaleModules.{u, 0} Λ Y ⥤ EtaleModules.{u, 0} Λ Y'}
    {G' : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ X'}
    {F' : EtaleModules.{u, 0} Λ X' ⥤ EtaleModules.{u, 0} Λ Y'}
    [F.Additive] [G.Additive] [G'.Additive] [F'.Additive] (α : F ⋙ G ⟶ G' ⋙ F')
    (K : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) (i : ℤ) :
    ((etaleModuleComplexComparisonOf Λ α).app K).f i = α.app (K.X i) :=
  NatTrans.mapHomologicalComplex_app_f _ _ _ _

/-- The components of `Stacks.EtaleCohomology.etaleModuleComplexComparisonOf` at a pasted
comparison. -/
theorem etaleModuleComplexComparisonOf_pasteComparison_app_f {X M Y X' M' Y' : Scheme.{u}}
    {A : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ M}
    {B : EtaleModules.{u, 0} Λ M ⥤ EtaleModules.{u, 0} Λ Y}
    {A' : EtaleModules.{u, 0} Λ X' ⥤ EtaleModules.{u, 0} Λ M'}
    {B' : EtaleModules.{u, 0} Λ M' ⥤ EtaleModules.{u, 0} Λ Y'}
    {GA : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ X'}
    {GB : EtaleModules.{u, 0} Λ M ⥤ EtaleModules.{u, 0} Λ M'}
    {GC : EtaleModules.{u, 0} Λ Y ⥤ EtaleModules.{u, 0} Λ Y'}
    [A.Additive] [B.Additive] [A'.Additive] [B'.Additive] [GA.Additive] [GC.Additive]
    (αA : A ⋙ GB ⟶ GA ⋙ A') (αB : B ⋙ GC ⟶ GB ⋙ B')
    (K : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) (i : ℤ) :
    ((etaleModuleComplexComparisonOf Λ (DerivedComparisonPaste.pasteComparison αA αB)).app K).f i =
      αB.app (A.obj (K.X i)) ≫ B'.map (αA.app (K.X i)) :=
  DerivedComparisonPaste.mapHomologicalComplex_pasteComparison_app_f αA αB K i

/-- The components of `Stacks.EtaleCohomology.etaleModuleComplexBaseChangeUnbounded` are those of
the underived base change map. -/
theorem etaleModuleComplexBaseChangeUnbounded_app_f {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : g' ≫ f = f' ≫ g)
    (K : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ) (i : ℤ) :
    ((etaleModuleComplexBaseChangeUnbounded.{u, 0} Λ f g g' f' h).app K).f i =
      (etaleModuleBaseChange Λ f f' g g' h.symm).app (K.X i) := by
  rw [etaleModuleComplexBaseChangeUnbounded_eq]
  obtain ⟨β, hβ⟩ : ∃ β, β = etaleModuleBaseChange Λ f f' g g' h.symm := ⟨_, rfl⟩
  rw [← hβ]
  exact Stacks.DerivedCategorySquare.mapHomologicalComplexCompIso_natTrans_app_f _ _ _ _ β K i

section Cube

open DerivedComparisonPaste

variable {T Ub P Y T' Ub' P' Y' : Scheme.{u}} {fb : T ⟶ Ub} [IsProper fb] {i : Y ⟶ Ub}
  [IsOpenImmersion i] {b : P ⟶ T} [IsOpenImmersion b] {f' : P ⟶ Y} (sq : IsPullback b f' fb i)
  {fb' : T' ⟶ Ub'} [IsProper fb'] {i' : Y' ⟶ Ub'} [IsOpenImmersion i'] {b' : P' ⟶ T'}
  [IsOpenImmersion b'] {f'' : P' ⟶ Y'} (sq' : IsPullback b' f'' fb' i')
  {φT : T' ⟶ T} {φU : Ub' ⟶ Ub} {φP : P' ⟶ P} {φY : Y' ⟶ Y}
  (hcb : IsPullback φP b' b φT) (hci : IsPullback φY i' i φU)
  (wf : φT ≫ fb = fb' ≫ φU) (wf' : φP ≫ f' = f'' ≫ φY)

/-! The compatibilities below are first proved with the comparisons on sheaves, the base change
maps on derived categories and the derived-functor units as variables, and then instantiated. -/

omit [IsProper fb] [IsProper fb'] in
/-- The degreewise base change comparisons of `i_! ∘ f'_*` and `f̄_* ∘ b_!` correspond under
`i_! ∘ f'_* ≅ f̄_* ∘ b_!`, for comparisons `β₁`, `ι₁`, `ι₂`, `β₂` of the four functors and
isomorphisms `e₁`, `e₂` compatible on sheaves (the hypothesis `h`). -/
theorem complexComparison_pasteComparison_conj
    (β₁ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleInverseImage.{u, 0} Λ φY ⟶
      etaleModuleInverseImage.{u, 0} Λ φP ⋙ etaleModuleDirectImage.{u, 0} Λ f'')
    (ι₁ : etaleModuleExtensionByZero.{u, 0} Λ i ⋙ etaleModuleInverseImage.{u, 0} Λ φU ⟶
      etaleModuleInverseImage.{u, 0} Λ φY ⋙ etaleModuleExtensionByZero.{u, 0} Λ i')
    (ι₂ : etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleInverseImage.{u, 0} Λ φT ⟶
      etaleModuleInverseImage.{u, 0} Λ φP ⋙ etaleModuleExtensionByZero.{u, 0} Λ b')
    (β₂ : etaleModuleDirectImage.{u, 0} Λ fb ⋙ etaleModuleInverseImage.{u, 0} Λ φU ⟶
      etaleModuleInverseImage.{u, 0} Λ φT ⋙ etaleModuleDirectImage.{u, 0} Λ fb')
    (e₁ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb)
    (e₂ : etaleModuleDirectImage.{u, 0} Λ f'' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i' ≅
      etaleModuleExtensionByZero.{u, 0} Λ b' ⋙ etaleModuleDirectImage.{u, 0} Λ fb')
    (h : ∀ F, ι₁.app ((etaleModuleDirectImage.{u, 0} Λ f').obj F) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ i').map (β₁.app F) =
      (etaleModuleInverseImage.{u, 0} Λ φU).map (e₁.hom.app F) ≫
        β₂.app ((etaleModuleExtensionByZero.{u, 0} Λ b).obj F) ≫
        (etaleModuleDirectImage.{u, 0} Λ fb').map (ι₂.app F) ≫
        e₂.inv.app ((etaleModuleInverseImage.{u, 0} Λ φP).obj F))
    (K : CochainComplex (EtaleModules.{u, 0} Λ P) ℤ) :
    (etaleModuleComplexComparisonOf Λ (pasteComparison β₁ ι₁)).app K =
      ((etaleModuleInverseImage.{u, 0} Λ φU).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex e₁ (ComplexShape.up ℤ)).hom.app K) ≫
        (etaleModuleComplexComparisonOf Λ (pasteComparison ι₂ β₂)).app K ≫
        (NatIso.mapHomologicalComplex e₂ (ComplexShape.up ℤ)).inv.app
          (((etaleModuleInverseImage.{u, 0} Λ φP).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            K) :=
  mapHomologicalComplex_pasteComparison_conj_of_components _ _ _ _ _ _ h
    _ (fun K i => etaleModuleComplexComparisonOf_pasteComparison_app_f Λ _ _ K i)
    _ (fun K i => etaleModuleComplexComparisonOf_pasteComparison_app_f Λ _ _ K i)
    _ (fun K i => by simp only [NatIso.mapHomologicalComplex_hom_app_f])
    _ (fun K i => by simp only [NatIso.mapHomologicalComplex_inv_app_f]) K

/-- The base change comparison `φ_U⁻¹ ∘ i_! ∘ Rf'_* ⟶ i'_! ∘ Rf''_* ∘ φ_P⁻¹` on derived
categories built from a base change map `bD` of `Rf'_*` and an isomorphism `η` of [Stacks,
Tag 03S6] is induced by the comparison on sheaves pasted from `η` and the comparison `β` inducing
`bD`. -/
theorem derivedDirectImageExtensionByZero_comparison_fac
    (β : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleInverseImage.{u, 0} Λ φY ⟶
      etaleModuleInverseImage.{u, 0} Λ φP ⋙ etaleModuleDirectImage.{u, 0} Λ f'')
    (η : etaleModuleInverseImage.{u, 0} Λ φY ⋙ etaleModuleExtensionByZero.{u, 0} Λ i' ≅
      etaleModuleExtensionByZero.{u, 0} Λ i ⋙ etaleModuleInverseImage.{u, 0} Λ φU)
    (γ : ((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex _ ⋙
        (etaleModuleInverseImage.{u, 0} Λ φY).mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, 0} Λ P) ℤ ⥤ CochainComplex (EtaleModules.{u, 0} Λ Y') ℤ) ⟶
      ((etaleModuleInverseImage.{u, 0} Λ φP).mapHomologicalComplex _ ⋙
        (etaleModuleDirectImage.{u, 0} Λ f'').mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, 0} Λ P) ℤ ⥤ CochainComplex (EtaleModules.{u, 0} Λ Y') ℤ))
    (hγ : ∀ K i, (γ.app K).f i = β.app (K.X i))
    (bD : etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f' ⋙
        etaleModuleDerivedInverseImage.{u, 0} Λ φY ⟶
      etaleModuleDerivedInverseImage.{u, 0} Λ φP ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f'')
    (hbD : ∀ K, (etaleModuleDerivedInverseImage.{u, 0} Λ φY).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').app K) ≫
      bD.app (DerivedCategory.Q.obj K) =
    (etaleModuleInverseImage.{u, 0} Λ φY).mapDerivedCategoryFactors.hom.app
        (((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map (γ.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f'').app
        (((etaleModuleInverseImage.{u, 0} Λ φP).mapHomologicalComplex _).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f'').map
        ((etaleModuleInverseImage.{u, 0} Λ φP).mapDerivedCategoryFactors.inv.app K))
    (K : CochainComplex (EtaleModules.{u, 0} Λ P) ℤ) :
    (etaleModuleDerivedInverseImage.{u, 0} Λ φU).map
        ((directImageExtensionByZeroUnboundedUnit Λ i f').app K) ≫
      ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f')
          (mapDerivedCategoryCube (etaleModuleInverseImage.{u, 0} Λ φY)
            (etaleModuleExtensionByZero.{u, 0} Λ i') (etaleModuleExtensionByZero.{u, 0} Λ i)
            (etaleModuleInverseImage.{u, 0} Λ φU) η).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight bD (etaleModuleExtensionByZero.{u, 0} Λ i').mapDerivedCategory ≫
        (Functor.associator _ _ _).hom).app (DerivedCategory.Q.obj K) =
    (etaleModuleInverseImage.{u, 0} Λ φU).mapDerivedCategoryFactors.hom.app
        (((etaleModuleDirectImage.{u, 0} Λ f' ⋙
          etaleModuleExtensionByZero.{u, 0} Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((etaleModuleComplexComparisonOf Λ (pasteComparison β η.inv)).app K) ≫
      (directImageExtensionByZeroUnboundedUnit Λ i' f'').app
        (((etaleModuleInverseImage.{u, 0} Λ φP).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f'' ⋙
          (etaleModuleExtensionByZero.{u, 0} Λ i').mapDerivedCategory).map
        ((etaleModuleInverseImage.{u, 0} Λ φP).mapDerivedCategoryFactors.inv.app K) :=
  comparison_comp
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f')
    (etaleModuleExtensionByZero.{u, 0} Λ i).mapDerivedCategoryFactors.inv
    (directImageExtensionByZeroUnboundedUnit Λ i f')
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f'')
    (etaleModuleExtensionByZero.{u, 0} Λ i').mapDerivedCategoryFactors.inv
    (directImageExtensionByZeroUnboundedUnit Λ i' f'')
    (etaleModuleInverseImage.{u, 0} Λ φP).mapDerivedCategoryFactors
    (etaleModuleInverseImage.{u, 0} Λ φY).mapDerivedCategoryFactors
    (etaleModuleInverseImage.{u, 0} Λ φU).mapDerivedCategoryFactors
    γ (etaleModuleComplexComparisonOf Λ η.inv)
    (etaleModuleComplexComparisonOf Λ (pasteComparison β η.inv)) bD
    (mapDerivedCategoryCube (etaleModuleInverseImage.{u, 0} Λ φY)
        (etaleModuleExtensionByZero.{u, 0} Λ i') (etaleModuleExtensionByZero.{u, 0} Λ i)
        (etaleModuleInverseImage.{u, 0} Λ φU) η).inv
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _)
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _)
    hbD (mapDerivedCategoryCube_comparison _ _ _ _ _)
    (fun K => by
      simp only [directImageExtensionByZeroUnboundedUnit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id])
    (fun K => by
      simp only [directImageExtensionByZeroUnboundedUnit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id])
    (mapHomologicalComplex_comparison_comp_of_components β η.inv _ hγ _
      (fun K i => etaleModuleComplexComparisonOf_app_f Λ _ K i) _
      (fun K i => etaleModuleComplexComparisonOf_pasteComparison_app_f Λ β η.inv K i)
      _ (fun K i => by
        simp only [Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app])
      _ (fun K i => by
        simp only [Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv,
          NatTrans.id_app])) K

omit [IsProper fb] [IsProper fb'] in
/-- The base change comparison `φ_U⁻¹ ∘ Rf̄_* ∘ b_! ⟶ Rf̄'_* ∘ b'_! ∘ φ_P⁻¹` on derived
categories built from a base change map `bD` of `Rf̄_*` and an isomorphism `η` of [Stacks,
Tag 03S6] is induced by the comparison on sheaves pasted from `η` and the comparison `β` inducing
`bD`. -/
theorem derivedExtensionByZeroDirectImage_comparison_fac
    (β : etaleModuleDirectImage.{u, 0} Λ fb ⋙ etaleModuleInverseImage.{u, 0} Λ φU ⟶
      etaleModuleInverseImage.{u, 0} Λ φT ⋙ etaleModuleDirectImage.{u, 0} Λ fb')
    (η : etaleModuleInverseImage.{u, 0} Λ φP ⋙ etaleModuleExtensionByZero.{u, 0} Λ b' ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleInverseImage.{u, 0} Λ φT)
    (γ : ((etaleModuleDirectImage.{u, 0} Λ fb).mapHomologicalComplex _ ⋙
        (etaleModuleInverseImage.{u, 0} Λ φU).mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, 0} Λ T) ℤ ⥤ CochainComplex (EtaleModules.{u, 0} Λ Ub') ℤ) ⟶
      ((etaleModuleInverseImage.{u, 0} Λ φT).mapHomologicalComplex _ ⋙
        (etaleModuleDirectImage.{u, 0} Λ fb').mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, 0} Λ T) ℤ ⥤ CochainComplex (EtaleModules.{u, 0} Λ Ub') ℤ))
    (hγ : ∀ K i, (γ.app K).f i = β.app (K.X i))
    (bD : etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb ⋙
        etaleModuleDerivedInverseImage.{u, 0} Λ φU ⟶
      etaleModuleDerivedInverseImage.{u, 0} Λ φT ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb')
    (hbD : ∀ K, (etaleModuleDerivedInverseImage.{u, 0} Λ φU).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb).app K) ≫
      bD.app (DerivedCategory.Q.obj K) =
    (etaleModuleInverseImage.{u, 0} Λ φU).mapDerivedCategoryFactors.hom.app
        (((etaleModuleDirectImage.{u, 0} Λ fb).mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map (γ.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb').app
        (((etaleModuleInverseImage.{u, 0} Λ φT).mapHomologicalComplex _).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb').map
        ((etaleModuleInverseImage.{u, 0} Λ φT).mapDerivedCategoryFactors.inv.app K))
    (K : CochainComplex (EtaleModules.{u, 0} Λ P) ℤ) :
    (etaleModuleDerivedInverseImage.{u, 0} Λ φU).map
        ((extensionByZeroDirectImageUnboundedUnit Λ fb b).app K) ≫
      ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ b).mapDerivedCategory bD ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (mapDerivedCategoryCube (etaleModuleInverseImage.{u, 0} Λ φP)
            (etaleModuleExtensionByZero.{u, 0} Λ b') (etaleModuleExtensionByZero.{u, 0} Λ b)
            (etaleModuleInverseImage.{u, 0} Λ φT) η).inv
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb') ≫
        (Functor.associator _ _ _).hom).app (DerivedCategory.Q.obj K) =
    (etaleModuleInverseImage.{u, 0} Λ φU).mapDerivedCategoryFactors.hom.app
        (((etaleModuleExtensionByZero.{u, 0} Λ b ⋙
          etaleModuleDirectImage.{u, 0} Λ fb).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((etaleModuleComplexComparisonOf Λ (pasteComparison η.inv β)).app K) ≫
      (extensionByZeroDirectImageUnboundedUnit Λ fb' b').app
        (((etaleModuleInverseImage.{u, 0} Λ φP).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      ((etaleModuleExtensionByZero.{u, 0} Λ b').mapDerivedCategory ⋙
          etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb').map
        ((etaleModuleInverseImage.{u, 0} Λ φP).mapDerivedCategoryFactors.inv.app K) :=
  comparison_comp
    (etaleModuleExtensionByZero.{u, 0} Λ b).mapDerivedCategoryFactors.inv
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb)
    (extensionByZeroDirectImageUnboundedUnit Λ fb b)
    (etaleModuleExtensionByZero.{u, 0} Λ b').mapDerivedCategoryFactors.inv
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb')
    (extensionByZeroDirectImageUnboundedUnit Λ fb' b')
    (etaleModuleInverseImage.{u, 0} Λ φP).mapDerivedCategoryFactors
    (etaleModuleInverseImage.{u, 0} Λ φT).mapDerivedCategoryFactors
    (etaleModuleInverseImage.{u, 0} Λ φU).mapDerivedCategoryFactors
    (etaleModuleComplexComparisonOf Λ η.inv) γ
    (etaleModuleComplexComparisonOf Λ (pasteComparison η.inv β))
    (mapDerivedCategoryCube (etaleModuleInverseImage.{u, 0} Λ φP)
        (etaleModuleExtensionByZero.{u, 0} Λ b') (etaleModuleExtensionByZero.{u, 0} Λ b)
        (etaleModuleInverseImage.{u, 0} Λ φT) η).inv bD
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _)
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _)
    (mapDerivedCategoryCube_comparison _ _ _ _ _) hbD
    (fun K => by
      simp only [extensionByZeroDirectImageUnboundedUnit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id])
    (fun K => by
      simp only [extensionByZeroDirectImageUnboundedUnit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id])
    (mapHomologicalComplex_comparison_comp_of_components η.inv β _
      (fun K i => etaleModuleComplexComparisonOf_app_f Λ _ K i) _ hγ _
      (fun K i => etaleModuleComplexComparisonOf_pasteComparison_app_f Λ η.inv β K i)
      _ (fun K i => by
        simp only [Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app])
      _ (fun K i => by
        simp only [Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv,
          NatTrans.id_app])) K

omit [IsProper fb] [IsProper fb'] in
/-- **Base change of the open immersion case of [Stacks, Tag 0F7B] on unbounded derived
categories, for variable comparisons**: the identifications `Rf̄_* ∘ b_! ≅ i_! ∘ Rf'_*` of right
derived functors through `e₁`, `e₂` (the units `u₁`, `u₂`, the hypotheses `hu₁`, `hu₂`) are
compatible with base change maps `bD₁`, `bD₂` induced by comparisons `β₁`, `β₂` on sheaves, read
through isomorphisms `η₁`, `η₂`, provided the comparisons on sheaves correspond (`h`). -/
theorem extensionByZeroDirectImageUnboundedIso_baseChange_of
    (β₁ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleInverseImage.{u, 0} Λ φY ⟶
      etaleModuleInverseImage.{u, 0} Λ φP ⋙ etaleModuleDirectImage.{u, 0} Λ f'')
    (η₁ : etaleModuleInverseImage.{u, 0} Λ φY ⋙ etaleModuleExtensionByZero.{u, 0} Λ i' ≅
      etaleModuleExtensionByZero.{u, 0} Λ i ⋙ etaleModuleInverseImage.{u, 0} Λ φU)
    (β₂ : etaleModuleDirectImage.{u, 0} Λ fb ⋙ etaleModuleInverseImage.{u, 0} Λ φU ⟶
      etaleModuleInverseImage.{u, 0} Λ φT ⋙ etaleModuleDirectImage.{u, 0} Λ fb')
    (η₂ : etaleModuleInverseImage.{u, 0} Λ φP ⋙ etaleModuleExtensionByZero.{u, 0} Λ b' ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleInverseImage.{u, 0} Λ φT)
    (e₁ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb)
    (e₂ : etaleModuleDirectImage.{u, 0} Λ f'' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i' ≅
      etaleModuleExtensionByZero.{u, 0} Λ b' ⋙ etaleModuleDirectImage.{u, 0} Λ fb')
    (h : ∀ F, η₁.inv.app ((etaleModuleDirectImage.{u, 0} Λ f').obj F) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ i').map (β₁.app F) =
      (etaleModuleInverseImage.{u, 0} Λ φU).map (e₁.hom.app F) ≫
        β₂.app ((etaleModuleExtensionByZero.{u, 0} Λ b).obj F) ≫
        (etaleModuleDirectImage.{u, 0} Λ fb').map (η₂.inv.app F) ≫
        e₂.inv.app ((etaleModuleInverseImage.{u, 0} Λ φP).obj F))
    (γ₁ : ((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex _ ⋙
        (etaleModuleInverseImage.{u, 0} Λ φY).mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, 0} Λ P) ℤ ⥤ CochainComplex (EtaleModules.{u, 0} Λ Y') ℤ) ⟶
      ((etaleModuleInverseImage.{u, 0} Λ φP).mapHomologicalComplex _ ⋙
        (etaleModuleDirectImage.{u, 0} Λ f'').mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, 0} Λ P) ℤ ⥤ CochainComplex (EtaleModules.{u, 0} Λ Y') ℤ))
    (hγ₁ : ∀ K i, (γ₁.app K).f i = β₁.app (K.X i))
    (bD₁ : etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f' ⋙
        etaleModuleDerivedInverseImage.{u, 0} Λ φY ⟶
      etaleModuleDerivedInverseImage.{u, 0} Λ φP ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f'')
    (hbD₁ : ∀ K, (etaleModuleDerivedInverseImage.{u, 0} Λ φY).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').app K) ≫
      bD₁.app (DerivedCategory.Q.obj K) =
    (etaleModuleInverseImage.{u, 0} Λ φY).mapDerivedCategoryFactors.hom.app
        (((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map (γ₁.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f'').app
        (((etaleModuleInverseImage.{u, 0} Λ φP).mapHomologicalComplex _).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f'').map
        ((etaleModuleInverseImage.{u, 0} Λ φP).mapDerivedCategoryFactors.inv.app K))
    (γ₂ : ((etaleModuleDirectImage.{u, 0} Λ fb).mapHomologicalComplex _ ⋙
        (etaleModuleInverseImage.{u, 0} Λ φU).mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, 0} Λ T) ℤ ⥤ CochainComplex (EtaleModules.{u, 0} Λ Ub') ℤ) ⟶
      ((etaleModuleInverseImage.{u, 0} Λ φT).mapHomologicalComplex _ ⋙
        (etaleModuleDirectImage.{u, 0} Λ fb').mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, 0} Λ T) ℤ ⥤ CochainComplex (EtaleModules.{u, 0} Λ Ub') ℤ))
    (hγ₂ : ∀ K i, (γ₂.app K).f i = β₂.app (K.X i))
    (bD₂ : etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb ⋙
        etaleModuleDerivedInverseImage.{u, 0} Λ φU ⟶
      etaleModuleDerivedInverseImage.{u, 0} Λ φT ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb')
    (hbD₂ : ∀ K, (etaleModuleDerivedInverseImage.{u, 0} Λ φU).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb).app K) ≫
      bD₂.app (DerivedCategory.Q.obj K) =
    (etaleModuleInverseImage.{u, 0} Λ φU).mapDerivedCategoryFactors.hom.app
        (((etaleModuleDirectImage.{u, 0} Λ fb).mapHomologicalComplex _).obj K) ≫
      DerivedCategory.Q.map (γ₂.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb').app
        (((etaleModuleInverseImage.{u, 0} Λ φT).mapHomologicalComplex _).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb').map
        ((etaleModuleInverseImage.{u, 0} Λ φT).mapDerivedCategoryFactors.inv.app K))
    (u₁ : (etaleModuleDirectImage.{u, 0} Λ f' ⋙
          etaleModuleExtensionByZero.{u, 0} Λ i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ ((etaleModuleExtensionByZero.{u, 0} Λ b).mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb))
    (hu₁ : u₁ = Functor.whiskerRight (NatIso.mapHomologicalComplex e₁ (ComplexShape.up ℤ)).hom
      DerivedCategory.Q ≫ extensionByZeroDirectImageUnboundedUnit Λ fb b)
    [((etaleModuleExtensionByZero.{u, 0} Λ b).mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb).IsRightDerivedFunctor u₁
      (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ P) (ComplexShape.up ℤ))]
    (u₂ : (etaleModuleDirectImage.{u, 0} Λ f'' ⋙
          etaleModuleExtensionByZero.{u, 0} Λ i').mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ ((etaleModuleExtensionByZero.{u, 0} Λ b').mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb'))
    (hu₂ : u₂ = Functor.whiskerRight (NatIso.mapHomologicalComplex e₂ (ComplexShape.up ℤ)).hom
      DerivedCategory.Q ≫ extensionByZeroDirectImageUnboundedUnit Λ fb' b')
    [((etaleModuleExtensionByZero.{u, 0} Λ b').mapDerivedCategory ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb').IsRightDerivedFunctor u₂
      (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ P') (ComplexShape.up ℤ))]
    (L : DerivedCategory (EtaleModules.{u, 0} Λ P)) :
    (etaleModuleDerivedInverseImage.{u, 0} Λ φU).map
        ((Functor.rightDerivedUnique _ _ u₁ (directImageExtensionByZeroUnboundedUnit Λ i f')
          (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ P) (ComplexShape.up ℤ))).hom.app L) ≫
      ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f')
          (mapDerivedCategoryCube (etaleModuleInverseImage.{u, 0} Λ φY)
            (etaleModuleExtensionByZero.{u, 0} Λ i') (etaleModuleExtensionByZero.{u, 0} Λ i)
            (etaleModuleInverseImage.{u, 0} Λ φU) η₁).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight bD₁ (etaleModuleExtensionByZero.{u, 0} Λ i').mapDerivedCategory ≫
        (Functor.associator _ _ _).hom).app L =
    ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ b).mapDerivedCategory bD₂ ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (mapDerivedCategoryCube (etaleModuleInverseImage.{u, 0} Λ φP)
            (etaleModuleExtensionByZero.{u, 0} Λ b') (etaleModuleExtensionByZero.{u, 0} Λ b)
            (etaleModuleInverseImage.{u, 0} Λ φT) η₂).inv
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb') ≫
        (Functor.associator _ _ _).hom).app L ≫
      (Functor.rightDerivedUnique _ _ u₂ (directImageExtensionByZeroUnboundedUnit Λ i' f'')
          (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ P') (ComplexShape.up ℤ))).hom.app
        ((etaleModuleDerivedInverseImage.{u, 0} Λ φP).obj L) :=
  comparison_rightDerivedUnique
    (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ P) (ComplexShape.up ℤ))
    (directImageExtensionByZeroUnboundedUnit Λ i f')
    (extensionByZeroDirectImageUnboundedUnit Λ fb b)
    (directImageExtensionByZeroUnboundedUnit Λ i' f'')
    (extensionByZeroDirectImageUnboundedUnit Λ fb' b')
    (NatIso.mapHomologicalComplex e₁ (ComplexShape.up ℤ))
    (NatIso.mapHomologicalComplex e₂ (ComplexShape.up ℤ)) _ _
    (rightDerivedUnique_hom_fac DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ P) (ComplexShape.up ℤ))
      (Functor.whiskerRight (NatIso.mapHomologicalComplex e₁ (ComplexShape.up ℤ)).hom
        DerivedCategory.Q)
      (extensionByZeroDirectImageUnboundedUnit Λ fb b) u₁ hu₁
      (directImageExtensionByZeroUnboundedUnit Λ i f'))
    (rightDerivedUnique_hom_fac DerivedCategory.Q
      (HomologicalComplex.quasiIso (EtaleModules.{u, 0} Λ P') (ComplexShape.up ℤ))
      (Functor.whiskerRight (NatIso.mapHomologicalComplex e₂ (ComplexShape.up ℤ)).hom
        DerivedCategory.Q)
      (extensionByZeroDirectImageUnboundedUnit Λ fb' b') u₂ hu₂
      (directImageExtensionByZeroUnboundedUnit Λ i' f''))
    (etaleModuleInverseImage.{u, 0} Λ φP).mapDerivedCategoryFactors
    (etaleModuleInverseImage.{u, 0} Λ φU).mapDerivedCategoryFactors
    (etaleModuleComplexComparisonOf Λ (pasteComparison β₁ η₁.inv))
    (etaleModuleComplexComparisonOf Λ (pasteComparison η₂.inv β₂)) _ _
    (derivedDirectImageExtensionByZero_comparison_fac Λ β₁ η₁ γ₁ hγ₁ bD₁ hbD₁)
    (derivedExtensionByZeroDirectImage_comparison_fac Λ β₂ η₂ γ₂ hγ₂ bD₂ hbD₂)
    (complexComparison_pasteComparison_conj Λ β₁ η₁.inv η₂.inv β₂ e₁ e₂ h) L

include hΛ sq sq' hcb hci wf wf' in
open DerivedComparisonPaste in
/-- **The open immersion case of [Stacks, Tag 0F7B] on unbounded derived categories commutes with
base change**, over a torsion ring: for cartesian squares `b ≫ f̄ = f' ≫ i` and
`b' ≫ f̄' = f'' ≫ i'` over a cube, the isomorphism `Rf̄_* ∘ b_! ≅ i_! ∘ Rf'_*` is compatible with
the base change maps of `Rf'_*` and `Rf̄_*` and the isomorphisms of [Stacks, Tag 03S6] for `i` and
`b`. Both are right derived functors of `i_! ∘ f'_* ≅ f̄_* ∘ b_!`, and the base change maps are
induced by the base change maps on sheaves, which correspond by
`Stacks.EtaleCohomology.etaleModuleDirectImageExtensionByZeroIso_baseChange`. -/
theorem etaleModuleExtensionByZeroDirectImageUnboundedIso_baseChange [CompactSpace Ub]
    [CompactSpace Ub'] (L : DerivedCategory (EtaleModules.{u, 0} Λ P)) :
    (etaleModuleDerivedInverseImage.{u, 0} Λ φU).map
        ((etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ fb i b f' sq).hom.app L) ≫
      ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f')
          (mapDerivedCategoryCube (etaleModuleInverseImage.{u, 0} Λ φY)
            (etaleModuleExtensionByZero.{u, 0} Λ i') (etaleModuleExtensionByZero.{u, 0} Λ i)
            (etaleModuleInverseImage.{u, 0} Λ φU)
            (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hci)).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedBaseChangeUnbounded.{u, 0} Λ f' φY φP f'' wf')
          (etaleModuleExtensionByZero.{u, 0} Λ i').mapDerivedCategory ≫
        (Functor.associator _ _ _).hom).app L =
    ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ b).mapDerivedCategory
          (etaleModuleDerivedBaseChangeUnbounded.{u, 0} Λ fb φU φT fb' wf) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (mapDerivedCategoryCube (etaleModuleInverseImage.{u, 0} Λ φP)
            (etaleModuleExtensionByZero.{u, 0} Λ b') (etaleModuleExtensionByZero.{u, 0} Λ b)
            (etaleModuleInverseImage.{u, 0} Λ φT)
            (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hcb)).inv
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb') ≫
        (Functor.associator _ _ _).hom).app L ≫
      (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ fb' i' b' f'' sq').hom.app
        ((etaleModuleDerivedInverseImage.{u, 0} Λ φP).obj L) := by
  have := isRightDerivedFunctor_directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq
  have := isRightDerivedFunctor_directImageExtensionByZeroUnboundedUnit' Λ hΛ fb' i' b' f'' sq'
  exact extensionByZeroDirectImageUnboundedIso_baseChange_of Λ
    (etaleModuleBaseChange Λ f' f'' φY φP wf'.symm)
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hci)
    (etaleModuleBaseChange Λ fb fb' φU φT wf.symm)
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hcb)
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq)
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb' i' b' f'' sq')
    (fun F => etaleModuleDirectImageExtensionByZeroIso_baseChange Λ hΛ sq sq' hcb hci wf.symm
      wf'.symm F)
    (etaleModuleComplexBaseChangeUnbounded.{u, 0} Λ f' φY φP f'' wf')
    (etaleModuleComplexBaseChangeUnbounded_app_f Λ f' φY φP f'' wf')
    (etaleModuleDerivedBaseChangeUnbounded.{u, 0} Λ f' φY φP f'' wf')
    (etaleModuleDerivedBaseChangeUnbounded_fac Λ f' φY φP f'' wf')
    (etaleModuleComplexBaseChangeUnbounded.{u, 0} Λ fb φU φT fb' wf)
    (etaleModuleComplexBaseChangeUnbounded_app_f Λ fb φU φT fb' wf)
    (etaleModuleDerivedBaseChangeUnbounded.{u, 0} Λ fb φU φT fb' wf)
    (etaleModuleDerivedBaseChangeUnbounded_fac Λ fb φU φT fb' wf)
    (directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq) rfl
    (directImageExtensionByZeroUnboundedUnit' Λ hΛ fb' i' b' f'' sq') rfl L

end Cube

end Derived

/-! ### The isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` and base change -/

section CompOver

variable (Λ : Type) [CommRing Λ] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)
  {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z' ⟶ Z}
  {hY : Y' ⟶ Y} {g' : Y' ⟶ Z'} {hX : X' ⟶ X} {f' : X' ⟶ Y'}
  (sqg : IsPullback hY g' g h) (sqf : IsPullback hX f' f hY)
  (jg : CompactificationOf (Over.mk g)) (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

open CompactificationOf in
/-- The component of `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompOverIso`: the Leray
isomorphism `R(f̄ ≫ ḡ)_* ≅ Rḡ_* ∘ Rf̄_*` followed by `Rḡ_*` of
`Rf̄_* (b ∘ a)_! ≅ Rf̄_* b_! a_! ≅ i_! Rf'_* a_!`. -/
theorem derivedLowerShriekUnboundedCompOverIso_hom_app_unfolded [CompactSpace jg.space]
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX).hom.app K =
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase jg.toBase _ rfl).hom.app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            ((restrictBase jg jX).immersion ≫ restrictBaseι jg jX)).obj K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jg.toBase).map
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase).map
              ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
                  ((restrictBase jg jX).immersion ≫ restrictBaseι jg jX) ≪≫
                Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
                  (etaleModuleExtensionByZeroCompIso.{u, 0} Λ (restrictBase jg jX).immersion
                    (restrictBaseι jg jX))).hom.app K) ≫
            (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ jX.toBase jg.immersion
                (restrictBaseι jg jX) (restrictBase jg jX).toBase
                (IsPullback.of_hasPullback jX.toBase jg.immersion)).hom.app
              ((etaleModuleExtensionByZero.{u, 0} Λ
                (restrictBase jg jX).immersion).mapDerivedCategory.obj K) ≫
            (etaleModuleExtensionByZero.{u, 0} Λ jg.immersion).mapDerivedCategory.map
              ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (restrictBase jg jX).toBase).map
                ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
                  (restrictBase jg jX).immersion).inv.app K)) ≫
            (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ jg.immersion).inv.app
              ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (restrictBase jg jX).toBase).obj
                ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
                  (restrictBase jg jX).immersion).obj K))) := by
  exact DerivedComparisonPaste.compOverIso_hom_app_abstract
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
        ((restrictBase jg jX).immersion ≫ restrictBaseι jg jX) ≪≫
      Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
        (etaleModuleExtensionByZeroCompIso.{u, 0} Λ (restrictBase jg jX).immersion
          (restrictBaseι jg jX)))
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase jg.toBase _ rfl)
    (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ jX.toBase jg.immersion
      (restrictBaseι jg jX) (restrictBase jg jX).toBase
      (IsPullback.of_hasPullback jX.toBase jg.immersion))
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ (restrictBase jg jX).immersion)
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ jg.immersion) K

open CompactificationOf DerivedComparisonPaste in
/-- **The isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` through the auxiliary compactification is
compatible with base change** along `Z' ⟶ Z`, on `D(X_étale, Λ)` for a torsion ring `Λ`: the
base change maps of the cubes of the compactifications `restrictBase`, `jg` and `compOver`
correspond under `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompOverIso`. -/
theorem derivedLowerShriekUnboundedCompOverIso_baseChange [CompactSpace jg.space]
    [CompactSpace (jg.baseChange sqg).space] (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedInverseImage.{u, 0} Λ h).map
        ((derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jg jX).hom.app K) ≫
      (derivedLowerShriekUnboundedBaseChange.{u, 0} Λ sqg jg).app
        ((derivedLowerShriekUnbounded.{u, 0} f (restrictBase jg jX) Λ).obj K) ≫
      (derivedLowerShriekUnbounded.{u, 0} g' (jg.baseChange sqg) Λ).map
        ((derivedLowerShriekUnboundedBaseChangeCube Λ (restrictBase jg jX)
          (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
          (restrictBaseBaseChangeι sqg sqf jg jX) (isPullback_restrictBase_baseChange sqg sqf jg jX)
          (restrictBase_baseChange_toBase_comm sqg sqf jg jX)).app K) =
    (derivedLowerShriekUnboundedBaseChangeCube Λ (compOver jg jX)
        (compOver (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
        (compImmersionBaseChangeι sqg sqf jg jX) (isPullback_compOver_baseChange sqg sqf jg jX)
        (compOver_baseChange_toBase_comm sqg sqf jg jX)).app K ≫
      (derivedLowerShriekUnboundedCompOverIso Λ hΛ f' g' (jg.baseChange sqg)
        (compImmersionBaseChange sqg sqf jg jX)).hom.app
          ((etaleModuleDerivedInverseImage.{u, 0} Λ hX).obj K) := by
  have hcab : IsPullback hX
      ((restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).immersion ≫
        restrictBaseι (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
      ((restrictBase jg jX).immersion ≫ restrictBaseι jg jX)
      (compImmersionBaseChangeι sqg sqf jg jX) :=
    isPullback_compOver_baseChange sqg sqf jg jX
  have wp : compImmersionBaseChangeι sqg sqf jg jX ≫ jX.toBase =
      (compImmersionBaseChange sqg sqf jg jX).toBase ≫ pullback.fst jg.toBase h :=
    (overBar_baseChange_toBase_comm sqg sqf jg jX).symm
  have wq : pullback.fst jg.toBase h ≫ jg.toBase = (jg.baseChange sqg).toBase ≫ h :=
    pullback.condition
  have wpq : compImmersionBaseChangeι sqg sqf jg jX ≫ (jX.toBase ≫ jg.toBase) =
      ((compImmersionBaseChange sqg sqf jg jX).toBase ≫ (jg.baseChange sqg).toBase) ≫ h :=
    (compOver_baseChange_toBase_comm sqg sqf jg jX).symm
  rw [derivedLowerShriekUnboundedCompOverIso_hom_app_unfolded,
    derivedLowerShriekUnboundedCompOverIso_hom_app_unfolded]
  refine compOver_baseChange_abstract
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase jg.toBase _ rfl)
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ
      (compImmersionBaseChange sqg sqf jg jX).toBase (jg.baseChange sqg).toBase _ rfl)
    (etaleModuleDerivedBaseChangeUnbounded.{u, 0} Λ jg.toBase h (pullback.fst jg.toBase h)
      (jg.baseChange sqg).toBase wq)
    (etaleModuleDerivedBaseChangeUnbounded.{u, 0} Λ jX.toBase (pullback.fst jg.toBase h)
      (compImmersionBaseChangeι sqg sqf jg jX) (compImmersionBaseChange sqg sqf jg jX).toBase wp)
    (etaleModuleDerivedBaseChangeUnbounded.{u, 0} Λ (jX.toBase ≫ jg.toBase) h
      (compImmersionBaseChangeι sqg sqf jg jX)
      ((compImmersionBaseChange sqg sqf jg jX).toBase ≫ (jg.baseChange sqg).toBase) wpq)
    (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ (isPullback_baseChange sqg jg))
    (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hcab)
    (derivedLowerShriekUnboundedBaseChange.{u, 0} Λ sqg jg)
    (derivedLowerShriekUnboundedBaseChangeCube Λ (compOver jg jX)
        (compOver (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
        (compImmersionBaseChangeι sqg sqf jg jX) (isPullback_compOver_baseChange sqg sqf jg jX)
        (compOver_baseChange_toBase_comm sqg sqf jg jX))
    (derivedLowerShriekUnboundedBaseChangeCube Λ (overBar jg jX)
        (overBar (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
        (compImmersionBaseChangeι sqg sqf jg jX) (isPullback_overBar_baseChange sqg sqf jg jX)
        (overBar_baseChange_toBase_comm sqg sqf jg jX))
    (derivedLowerShriekUnboundedBaseChangeCube Λ (restrictBase jg jX)
          (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
          (restrictBaseBaseChangeι sqg sqf jg jX) (isPullback_restrictBase_baseChange sqg sqf jg jX)
          (restrictBase_baseChange_toBase_comm sqg sqf jg jX))
    rfl rfl rfl
    (etaleModuleDerivedBaseChangeUnbounded_comp Λ jX.toBase jg.toBase (jX.toBase ≫ jg.toBase) rfl
      (compImmersionBaseChange sqg sqf jg jX).toBase (jg.baseChange sqg).toBase
      ((compImmersionBaseChange sqg sqf jg jX).toBase ≫ (jg.baseChange sqg).toBase) rfl
      (compImmersionBaseChangeι sqg sqf jg jX) (pullback.fst jg.toBase h) h wp wq wpq)
    K _ _ ?_
  let cmdA := mapDerivedCategoryCube (etaleModuleInverseImage.{u, 0} Λ hX)
      (etaleModuleExtensionByZero.{u, 0} Λ
        (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).immersion)
      (etaleModuleExtensionByZero.{u, 0} Λ (restrictBase jg jX).immersion)
      (etaleModuleInverseImage.{u, 0} Λ (restrictBaseBaseChangeι sqg sqf jg jX))
      (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ
        (isPullback_restrictBase_baseChange sqg sqf jg jX))
  let cmdB := mapDerivedCategoryCube
      (etaleModuleInverseImage.{u, 0} Λ (restrictBaseBaseChangeι sqg sqf jg jX))
      (etaleModuleExtensionByZero.{u, 0} Λ
        (restrictBaseι (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)))
      (etaleModuleExtensionByZero.{u, 0} Λ (restrictBaseι jg jX))
      (etaleModuleInverseImage.{u, 0} Λ (compImmersionBaseChangeι sqg sqf jg jX))
      (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ
        (isPullback_restrictBaseι_baseChange sqg sqf jg jX))
  let cmdAB := mapDerivedCategoryCube (etaleModuleInverseImage.{u, 0} Λ hX)
      (etaleModuleExtensionByZero.{u, 0} Λ
        ((restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).immersion ≫
          restrictBaseι (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)))
      (etaleModuleExtensionByZero.{u, 0} Λ
        ((restrictBase jg jX).immersion ≫ restrictBaseι jg jX))
      (etaleModuleInverseImage.{u, 0} Λ (compImmersionBaseChangeι sqg sqf jg jX))
      (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hcab)
  have : Functor.Additive (C := EtaleModules.{u, 0} Λ jg.space)
      (D := EtaleModules.{u, 0} Λ (jg.baseChange sqg).space)
      (etaleModuleInverseImage.{u, 0} Λ (pullback.fst jg.toBase h)) :=
    etaleModuleInverseImage_additive.{u, 0} Λ _
  have : PreservesFiniteLimits (C := EtaleModules.{u, 0} Λ jg.space)
      (D := EtaleModules.{u, 0} Λ (jg.baseChange sqg).space)
      (etaleModuleInverseImage.{u, 0} Λ (pullback.fst jg.toBase h)) :=
    etaleModuleInverseImage_preservesFiniteLimits.{u, 0} Λ _
  have : PreservesFiniteColimits (C := EtaleModules.{u, 0} Λ jg.space)
      (D := EtaleModules.{u, 0} Λ (jg.baseChange sqg).space)
      (etaleModuleInverseImage.{u, 0} Λ (pullback.fst jg.toBase h)) :=
    etaleModuleInverseImage_preservesFiniteColimits.{u, 0} Λ _
  let cmdI := mapDerivedCategoryCube (etaleModuleInverseImage.{u, 0} Λ hY)
      (etaleModuleExtensionByZero.{u, 0} Λ (jg.baseChange sqg).immersion)
      (etaleModuleExtensionByZero.{u, 0} Λ jg.immersion)
      (etaleModuleInverseImage.{u, 0} Λ (pullback.fst jg.toBase h))
      (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ (isPullback_baseChange sqg jg))
  exact restrictBase_baseChange_unbounded_abstract
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ (restrictBase jg jX).immersion)
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
      (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).immersion)
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
      ((restrictBase jg jX).immersion ≫ restrictBaseι jg jX))
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ
      ((restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).immersion ≫
        restrictBaseι (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)))
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ jg.immersion)
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ (jg.baseChange sqg).immersion)
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
      (etaleModuleExtensionByZeroCompIso.{u, 0} Λ (restrictBase jg jX).immersion
        (restrictBaseι jg jX)))
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
      (etaleModuleExtensionByZeroCompIso.{u, 0} Λ
        (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).immersion
        (restrictBaseι (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))))
    (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ jX.toBase jg.immersion
      (restrictBaseι jg jX) (restrictBase jg jX).toBase
      (IsPullback.of_hasPullback jX.toBase jg.immersion))
    (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ
      (compImmersionBaseChange sqg sqf jg jX).toBase (jg.baseChange sqg).immersion
      (restrictBaseι (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
      (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).toBase
      (IsPullback.of_hasPullback (compImmersionBaseChange sqg sqf jg jX).toBase
        (jg.baseChange sqg).immersion))
    cmdA cmdB cmdAB cmdI
    (etaleModuleDerivedBaseChangeUnbounded.{u, 0} Λ (restrictBase jg jX).toBase hY
      (restrictBaseBaseChangeι sqg sqf jg jX)
      (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).toBase
      (restrictBase_baseChange_toBase_comm sqg sqf jg jX).symm)
    (etaleModuleDerivedBaseChangeUnbounded.{u, 0} Λ jX.toBase (pullback.fst jg.toBase h)
      (compImmersionBaseChangeι sqg sqf jg jX) (compImmersionBaseChange sqg sqf jg jX).toBase wp)
    (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ
      (isPullback_restrictBase_baseChange sqg sqf jg jX))
    (by simp only [etaleModuleDerivedExtensionByZeroUnboundedCubeIso, mapDerivedCategoryCube,
      Iso.trans_assoc, cmdA])
    (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hcab)
    (by simp only [etaleModuleDerivedExtensionByZeroUnboundedCubeIso, mapDerivedCategoryCube,
      Iso.trans_assoc, cmdAB])
    (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ (isPullback_baseChange sqg jg))
    (by simp only [etaleModuleDerivedExtensionByZeroUnboundedCubeIso, mapDerivedCategoryCube,
      Iso.trans_assoc, cmdI])
    (fun K' => mapDerivedCategoryCube_comp _ _ _ _ _ _ _
      (fun N => mapDerivedCategoryCompIsoOfIso_hom_app_Q _ _ _ _ N)
      (fun N => mapDerivedCategoryCompIsoOfIso_hom_app_Q _ _ _ _ N)
      (fun F => etaleModuleInverseImageExtensionByZeroIso_comp Λ
        (isPullback_restrictBase_baseChange sqg sqf jg jX)
        (isPullback_restrictBaseι_baseChange sqg sqf jg jX) hcab F) K')
    (fun L => etaleModuleExtensionByZeroDirectImageUnboundedIso_baseChange Λ hΛ
      (IsPullback.of_hasPullback jX.toBase jg.immersion)
      (IsPullback.of_hasPullback (compImmersionBaseChange sqg sqf jg jX).toBase
        (jg.baseChange sqg).immersion)
      (isPullback_restrictBaseι_baseChange sqg sqf jg jX) (isPullback_baseChange sqg jg) wp
      (restrictBase_baseChange_toBase_comm sqg sqf jg jX).symm L)
    K

end CompOver

end Stacks.EtaleCohomology

end
