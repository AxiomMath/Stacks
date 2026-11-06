module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpDerivedGlobalSectionsNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpERepresentationDerived

/-!
# Naturality in `M` of `E = Γ^Gal(X̄, ℋom^•_ℤ(I, K)) ≅ RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))`

Let `π : N ⟶ M` be a morphism of finite `Λ`-modules with continuous `π₁(X, x)`-action, `I_N`, `I_M`
injective resolutions of `(j_! ℱ_N)[0]`, `(j_! ℱ_M)[0]`, and `φ : I_N ⟶ I_M` a morphism of
complexes over `(j_! ℱ_π)[0]`. Then precomposition with `φ` on
`E_M = Γ^Gal(X̄, ℋom^•_ℤ(I_M, K)) ⟶ E_N` corresponds, under the isomorphisms
`AlgebraicGeometry.galoisHomOpECyclotomicDerivedIso`, to `RΓ^Gal(X, -)` of
`ℋom_ℤ(ℱ_M, ℱ_μ) ⟶ ℋom_ℤ(ℱ_N, ℱ_μ)`.

## Main results

* `Stacks.EtaleCohomology.galoisHomOpEDerivedGlobalSectionsOverIso_hom_naturality`: naturality of
  `Stacks.EtaleCohomology.galoisHomOpEDerivedGlobalSectionsOverIso` in `F`.
* `AlgebraicGeometry.galoisHomOpECyclotomicDerivedIso_hom_naturality`: naturality of
  `AlgebraicGeometry.galoisHomOpECyclotomicDerivedIso` in `M`.

## Implementation notes

The local instances of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpDerivedGlobalSections` are
reactivated in the section on `galoisHomOpEDerivedGlobalSectionsOverIso`, so that its complexes are
spelled as there (see the implementation notes of that file). The statement on
`galoisHomOpECyclotomicDerivedIso` is spelled with the default instances, as its consumers state
it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.AbelianInternalHom
  Stacks.ConstantSheaf Stacks.Frobenius

universe w₁ w₂ w₃ w₄ w v u

namespace Stacks.AbelianInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {Λ : Type w} [Ring Λ]

/-- Precomposition commutes with transport of the target complex along an equation. -/
lemma homOpComplexPrecomp_eqToHom_target {L L' : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ}
    (f : L' ⟶ L) {T T' : CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ} (h : T = T') :
    homOpComplexPrecomp (M := T) f ≫ eqToHom (congrArg (homOpComplex K L') h) =
      eqToHom (congrArg (homOpComplex K L) h) ≫ homOpComplexPrecomp (M := T') f := by
  subst h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Precomposition with the transport `L ⟶ L'` along an equation is the transport
`ℋom^•(L', M) ⟶ ℋom^•(L, M)`. -/
lemma homOpComplexPrecomp_eqToHom {L L' : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ}
    (h : L = L') (M : CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ) :
    homOpComplexPrecomp (M := M) (eqToHom h) =
      eqToHom (congrArg (fun L => homOpComplex K L M) h.symm) := by
  subst h
  simpa using homOpComplexPrecomp_id K L M

end Stacks.AbelianInternalHom

namespace Stacks.EtaleCohomology

/-- Bookkeeping for `galoisHomOpEDerivedGlobalSectionsOverIso_hom_naturality`: a commutative square
of composites in `𝒞`, mapped by `G` and then by `F`, followed by a commutative square in `ℰ`. -/
lemma map_map_comp_square {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟] [Category* ℰ] (G : 𝒞 ⥤ 𝒟)
    (F : 𝒟 ⥤ ℰ) {X₁ X₂ W₁ W₂ V₁ V₂ T₁ T₂ : 𝒞} {U₁ U₂ : 𝒟} {S₁ S₂ : ℰ}
    {x : X₂ ⟶ X₁} {b₁ : X₁ ⟶ W₁} {b₂ : X₂ ⟶ W₂} {c₁ : W₁ ⟶ V₁} {c₂ : W₂ ⟶ V₂}
    {d₁ : V₁ ⟶ T₁} {d₂ : V₂ ⟶ T₂} {g : T₂ ⟶ T₁} {e₁ : U₁ ⟶ G.obj X₁} {e₂ : U₂ ⟶ G.obj X₂}
    {x' : U₂ ⟶ U₁} {s₁ : F.obj (G.obj T₁) ⟶ S₁} {s₂ : F.obj (G.obj T₂) ⟶ S₂} {r : S₂ ⟶ S₁}
    (hcx : x ≫ b₁ ≫ c₁ ≫ d₁ = b₂ ≫ c₂ ≫ d₂ ≫ g) (he : x' ≫ e₁ = e₂ ≫ G.map x)
    (hgen : F.map (G.map g) ≫ s₁ = s₂ ≫ r) :
    F.map x' ≫ F.map (e₁ ≫ G.map b₁) ≫ F.map (G.map c₁) ≫ F.map (G.map d₁) ≫ s₁ =
      (F.map (e₂ ≫ G.map b₂) ≫ F.map (G.map c₂) ≫ F.map (G.map d₂) ≫ s₂) ≫ r := by
  have h := congrArg (fun t => F.map (G.map t)) hcx
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  rw [← F.map_comp_assoc, he, F.map_comp_assoc, reassoc_of% h, hgen]

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Mine

attribute [local instance 10000] isRightCancelAdd_int_galoisHomOpDerived
  preservesZeroMorphisms_forgetAbOp_galoisHomOpDerived
  preservesZeroMorphisms_forgetAbZMod_galoisHomOpDerived
  preservesZeroMorphisms_forgetAbZModBar_galoisHomOpDerived
  preservesZeroMorphisms_homOp_galoisHomOpDerived preservesZeroMorphisms_homAb_galoisHomOpDerived
  preservesZeroMorphisms_restriction_galoisHomOpDerived
  preservesZeroMorphisms_etaleRestriction_galoisHomOpDerived
  preservesZeroMorphisms_galoisGlobalSections_galoisHomOpDerived
  additive_galoisGlobalSections_galoisHomOpDerived enoughInjectives_galoisHomOpDerived
  hasZeroObject_zmod_galoisHomOpDerived hasZeroObject_zmodBar_galoisHomOpDerived
  hasZeroObject_op_galoisHomOpDerived hasZeroObject_ab_galoisHomOpDerived etale_galoisHomOpDerived
  preservesZeroMorphisms_galoisGlobalSectionsBar_galoisHomOpDerived
  hasZeroObject_bar_galoisHomOpDerived hasZeroObject_abBar_galoisHomOpDerived
  hasZeroObject_opBar_galoisHomOpDerived preservesZeroMorphisms_restrictScalarsInt_galoisHomOpE

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar] {Y Yb : Over (Spec (.of k))} (i : Y ⟶ Yb) [IsOpenImmersion i.left]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom]

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom] in
/-- The precompositions with `φ : I₁ ⟶ I₂` and with `(i_! v)[0]` correspond under the
precompositions with the resolutions `Zₐ ⟶ Iₐ`, `Zₐ = (i_! Fₐ)[0]`. -/
lemma homOpComplexPrecomp_injectiveResolution_naturality {F₁ F₂ : EtaleModules.{u, 0} Λ Y.left}
    (v : F₁ ⟶ F₂) (M : CochainComplex (Sheaf Yb.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    {Z₁ Z₂ : CochainComplex (EtaleModules.{u, 0} Λ Yb.left) ℤ}
    (hZ₁ : Z₁ = (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ i.left).obj F₁))
    (hZ₂ : Z₂ = (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ i.left).obj F₂))
    (I₁ : CochainComplex.InjectiveResolution Z₁) (I₂ : CochainComplex.InjectiveResolution Z₂)
    (φ : I₁.cocomplex ⟶ I₂.cocomplex) (g : Z₁ ⟶ Z₂) (hφ : I₁.ι ≫ φ = g ≫ I₂.ι)
    (hg : g = eqToHom hZ₁ ≫ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      ((etaleModuleExtensionByZero.{u, 0} Λ i.left).map v) ≫ eqToHom hZ₂.symm) :
    homOpComplexPrecomp (M := M) φ ≫ homOpComplexPrecomp (M := M) I₁.ι ≫
        eqToHom (congrArg (fun L => homOpComplex Yb.left.smallEtaleTopology L M) hZ₁) =
      homOpComplexPrecomp (M := M) I₂.ι ≫
        eqToHom (congrArg (fun L => homOpComplex Yb.left.smallEtaleTopology L M) hZ₂) ≫
          homOpComplexPrecomp (M := M) ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
            ((etaleModuleExtensionByZero.{u, 0} Λ i.left).map v)) := by
  subst hZ₁ hZ₂ hg
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hφ ⊢
  rw [homOpComplexPrecomp_comp, hφ, ← homOpComplexPrecomp_comp]

section Derived

variable [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ Y.left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λᵐᵒᵖ k kbar)]
  [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λᵐᵒᵖ (fieldBaseChange Y kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)]
  [CompactSpace (kbar ≃ₐ[k] kbar)] [Finite Λ] {n : ℕ} [NeZero n]

/-- **`Γ^Gal(Ȳ, ℋom^•_ℤ(I, res_ℤ K)) ≅ RΓ^Gal(Y, ℋom_ℤ(F, ω))` is natural in `F`**: for
`v : F₁ ⟶ F₂` and a morphism `φ : I₁ ⟶ I₂` of injective resolutions of `(i_! Fₐ)[0]` over
`(i_! v)[0]`, the isomorphisms `galoisHomOpEDerivedGlobalSectionsOverIso` commute with
precomposition by `φ` and `RΓ^Gal(Y, -)` of precomposition by `v`. -/
theorem galoisHomOpEDerivedGlobalSectionsOverIso_hom_naturality
    {F₁ F₂ : EtaleModules.{u, 0} Λ Y.left} (v : F₁ ⟶ F₂)
    (G₁ : EtaleModules.{u, 0} (ZMod n) Y.left) (e₁ : toAb _ F₁ ≅ toAb _ G₁)
    (hG₁ : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G₁)
    (G₂ : EtaleModules.{u, 0} (ZMod n) Y.left) (e₂ : toAb _ F₂ ≅ toAb _ G₂)
    (hG₂ : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G₂)
    (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (hω : Stacks.ModuleInternalHom.IsLocallyConstantInjective Y.left.smallEtaleTopology (ZMod n) ω)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) [K₀.IsStrictlyGE 0]
    [∀ q, Injective (K₀.X q)]
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) [hι₀ : QuasiIso ι₀] (hn : (n : Λ) = 0)
    {Z₁ Z₂ : CochainComplex (EtaleModules.{u, 0} Λ Yb.left) ℤ}
    (hZ₁ : Z₁ = (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ i.left).obj F₁))
    (hZ₂ : Z₂ = (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ i.left).obj F₂))
    (I₁ : CochainComplex.InjectiveResolution Z₁) (I₂ : CochainComplex.InjectiveResolution Z₂)
    (Kc : CochainComplex (EtaleModules.{u, 0} ℤ Yb.left) ℤ)
    (hKc : Kc =
        ((etaleModuleRestrictScalars (Int.castRingHom (ZMod n)) Yb.left).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K₀)
    (φ : I₁.cocomplex ⟶ I₂.cocomplex) (g : Z₁ ⟶ Z₂) (hφ : I₁.ι ≫ φ = g ≫ I₂.ι)
    (hg : g = eqToHom hZ₁ ≫ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
      ((etaleModuleExtensionByZero.{u, 0} Λ i.left).map v) ≫ eqToHom hZ₂.symm) :
    DerivedCategory.Q.map (((galoisGlobalSections Λᵐᵒᵖ Yb kbar).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (homOpComplexPrecomp (M := etaleHomOpTarget Yb Kc) φ)) ≫
        (galoisHomOpEDerivedGlobalSectionsOverIso Λ kbar i F₁ G₁ e₁ hG₁ ω hω K₀ ι₀ hn hZ₁ I₁ Kc
          hKc).hom =
      (galoisHomOpEDerivedGlobalSectionsOverIso Λ kbar i F₂ G₂ e₂ hG₂ ω hω K₀ ι₀ hn hZ₂ I₂ Kc
          hKc).hom ≫
        DerivedCategory.Plus.ι.map ((galoisDerivedGlobalSections Λᵐᵒᵖ Y kbar).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            (homOpMapLeft Y.left.smallEtaleTopology v (toAb _ ω)))) := by
  have hT := etaleHomOpTarget_eq_of_restrictScalarsInt K₀ Kc hKc
  have h₁ := homOpComplexPrecomp_eqToHom_target Yb.left.smallEtaleTopology φ hT
  have h₂ := homOpComplexPrecomp_injectiveResolution_naturality Λ i v
    (((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K₀)
    hZ₁ hZ₂ I₁ I₂ φ g hφ hg
  have hcx := (Category.assoc _ _ _).symm.trans ((h₁ =≫ (homOpComplexPrecomp I₁.ι ≫
    eqToHom (congrArg (fun L => homOpComplex Yb.left.smallEtaleTopology L
      (((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₀)) hZ₁))).trans ((Category.assoc _ _ _).trans
    (congrArg (fun t => eqToHom (congrArg (homOpComplex Yb.left.smallEtaleTopology I₂.cocomplex)
      hT) ≫ t) h₂)))
  have hgen := galoisHomOpDerivedGlobalSectionsOverIso_hom_naturality Λ kbar i v G₁ e₁ hG₁ G₂ e₂ hG₂
    ω hω K₀ ι₀
  exact map_map_comp_square _ _ hcx ((Category.comp_id _).trans (Category.id_comp _).symm) hgen

end Derived

end Mine

/-- Transport of a morphism along equations of its source and target commutes with a functor. -/
lemma map_comp_eqToHom_eq_eqToHom_comp_map {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ]
    (H : 𝒜 ⥤ ℬ) {A₁ A₂ B₁ B₂ : 𝒜} (h₁ : A₁ = B₁) (h₂ : A₂ = B₂) (a : A₂ ⟶ A₁) (b : B₂ ⟶ B₁)
    (hab : a ≫ eqToHom h₁ = eqToHom h₂ ≫ b) :
    H.map a ≫ eqToHom (congrArg (fun A => H.obj A) h₁) =
      eqToHom (congrArg (fun A => H.obj A) h₂) ≫ H.map b := by
  subst h₁ h₂
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hab ⊢
  rw [hab]

/-- Two commutative squares compose. -/
lemma comp_comp_square {𝒞 : Type*} [Category* 𝒞] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : 𝒞}
    {p : X₂ ⟶ X₁} {a₁ : X₁ ⟶ Y₁} {a₂ : X₂ ⟶ Y₂} {q : Y₂ ⟶ Y₁} {b₁ : Y₁ ⟶ Z₁} {b₂ : Y₂ ⟶ Z₂}
    {r : Z₂ ⟶ Z₁} (h₁ : p ≫ a₁ = a₂ ≫ q) (h₂ : q ≫ b₁ = b₂ ≫ r) :
    p ≫ a₁ ≫ b₁ = (a₂ ≫ b₂) ≫ r := by
  simp only [Category.assoc, reassoc_of% h₁, h₂]

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.GroupCohomology Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]
  (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod n) j.immersion).obj
          ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n)))))
  (Λ : Type) [Ring Λ] [Finite Λ] [Algebra (ZMod n) Λ]
  [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ (Over.mk f).left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λᵐᵒᵖ k kbar)]
  [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λᵐᵒᵖ (fieldBaseChange (Over.mk f) kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)]

set_option maxHeartbeats 1000000 in
/-- **Naturality in `M` of `E = Γ^Gal(X̄, ℋom^•_ℤ(I_M, K)) ≅ RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))`**: for
`π : N ⟶ M` and a morphism `φ : I_N ⟶ I_M` of injective resolutions of `(j_! ℱ_N)[0]`,
`(j_! ℱ_M)[0]` over `(j_! ℱ_π)[0]`, the isomorphisms
`AlgebraicGeometry.galoisHomOpECyclotomicDerivedIso` commute with precomposition by `φ` and
`RΓ^Gal(X, -)` of `ℋom_ℤ(ℱ_π, ℱ_μ)`. -/
theorem galoisHomOpECyclotomicDerivedIso_hom_naturality [ConnectedSpace X.1]
    {M N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))}
    (π : N ⟶ M)
    (IM : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj M))))
    (IN : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
          ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj N))))
    [K₀.cocomplex.IsStrictlyGE 0]
    (hG'M : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} X.1.smallEtaleTopology
      (ZMod n) ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) X.1).obj
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj M)))
    (hG'N : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} X.1.smallEtaleTopology
      (ZMod n) ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) X.1).obj
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj N)))
    (hω : letI := connectedSpace_of_isCurve B X f
      Stacks.ModuleInternalHom.IsLocallyConstantInjective X.1.smallEtaleTopology (ZMod n)
        ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n)))
    (φ : IN.cocomplex ⟶ IM.cocomplex)
    (hφ : IN.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
        ((representationSheaf B X (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map π)) ≫ IM.ι) :
    DerivedCategory.Q.map
        (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex
        _).map (homOpComplexPrecomp (M := etaleHomOpTarget (Over.mk j.toBase)
          (cyclotomicIntResolution B X f kbar y n j K₀)) φ)) ≫
        (galoisHomOpECyclotomicDerivedIso B X f kbar y n j K₀ Λ N IN hG'N hω).hom =
      (galoisHomOpECyclotomicDerivedIso B X f kbar y n j K₀ Λ M IM hG'M hω).hom ≫
        (DerivedCategory.Plus.singleFunctor _ 0 ⋙ galoisDerivedGlobalSections Λᵐᵒᵖ
            (Over.mk f) kbar ⋙
          DerivedCategory.Plus.ι).map
            ((etaleHomOpRepresentationFunctor B X (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ n
                (cyclotomicContinuousModule B X f kbar y n)).map π.op) := by
  have hE := galoisHomOpEDerivedGlobalSectionsOverIso_hom_naturality Λ kbar
    (compactificationImmersionOverHom j) ((representationSheaf B X _ Λ).map π)
    ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) X.1).obj
        ((representationSheaf B X _ Λ).obj N))
    (Iso.refl _) hG'N
    ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) X.1).obj
        ((representationSheaf B X _ Λ).obj M))
    (Iso.refl _) hG'M _ hω K₀.cocomplex K₀.ι (hι₀ := K₀.quasiIso) (natCast_eq_zero_of_zmodAlgebra Λ)
    rfl rfl IN IM _ rfl φ _ hφ
    ((Category.id_comp _).symm.trans (congrArg (𝟙 _ ≫ ·) (Category.comp_id _).symm))
  have hH := map_comp_eqToHom_eq_eqToHom_comp_map
    (DerivedCategory.Plus.singleFunctor _ 0 ⋙ galoisDerivedGlobalSections Λᵐᵒᵖ (Over.mk f) kbar ⋙
      DerivedCategory.Plus.ι)
    (homOpSheaf_cyclotomic_eq_etaleHomOpRepresentationFunctor_obj B X f kbar y n Λ N)
    (homOpSheaf_cyclotomic_eq_etaleHomOpRepresentationFunctor_obj B X f kbar y n Λ M) _
    ((etaleHomOpRepresentationFunctor B X (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ n
        (cyclotomicContinuousModule B X f kbar y n)).map π.op)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact comp_comp_square hE hH

end AlgebraicGeometry

end
